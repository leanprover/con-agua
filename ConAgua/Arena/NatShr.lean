module

public import ConAgua.Arena.NatShl
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr

@[expose] public section

/-!
# `Nat.shiftRight` on the limb pool: `nat_shr`

`nat_shr(oa, la, ob, lb)` is `a >>> b = a / 2^b` for two pool slices, `b` normalised (con-ron's
`shift_right_nat`, `skip_index`, `shr_from`, `shr_bits_from`, `ron/nat.rs:406-462`). An amount of
two or more limbs is at least `2^64`, so the result is `0` (for `la < 2^57`, which every pool
satisfies; above that, `abort`). Otherwise `k = b[0]`: skip `w = k >> 6` limbs (if that is all of
`a`, the result is `0`), then one pass over the remaining slice `(oa + w, la - w)`, limb `i` of the
result being `(x >> s) | ((y << 1) << (63 - s))` with `x`, `y` limbs `i`, `i + 1` and `s = k & 63`
(branch-free, as in `nat_shl`: the second part is `y << (64 - s)` for `s ≥ 1` and `0` for
`s = 0`), then `nat_trim`.

The loop runs over the shifted slice, so `w` does not occur in its invariant: the result so far
times `2^s`, plus the low `s` bits of the slice's first limb, is the slice's first `i` limbs plus
the low `s` bits of limb `i`, weighted (`ShrInv`). `shr_split` is its digit equation. The skipped
limbs and the division are three lemmas at the end (`shr_val`, `shr_big_w`, `shr_big_b`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Word facts -/

/-- The low `s` bits of `x`, as a named function (an atom to `grind`). -/
def lowb (x s : Nat) : Nat := x % 2 ^ s

theorem lowb_lt (x s : Nat) : lowb x s < sh s := Nat.mod_lt _ (Nat.two_pow_pos _)
grind_pattern [arena_grind] lowb_lt => lowb x s

@[arena_grind =] theorem lowb_zero (s : Nat) : lowb 0 s = 0 := Nat.zero_mod _

theorem shr_hi (y b : Word) (hb : b.toNat < 64) :
    ((y <<< 1) <<< (63 - b)).toNat = (y.toNat % 2 ^ b.toNat) * 2 ^ (64 - b.toNat) := by
  have h63 : (63 - b).toNat = 63 - b.toNat := by grind
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft, h63]
  simp only [Nat.shiftLeft_eq, UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega : 63 - b.toNat < 64), Nat.mod_eq_of_lt (by omega : 1 < 64)]
  rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, show 1 + (63 - b.toNat) = 64 - b.toNat by omega]
  have : 2 ^ 64 = 2 ^ b.toNat * 2 ^ (64 - b.toNat) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_mod_mul_right]

/-- The digit equation of one limb of the right shift. -/
theorem shr_split (x y b : Word) (hb : b.toNat < 64) :
    ((x >>> b) ||| ((y <<< 1) <<< (63 - b))).toNat * sh b.toNat + lowb x.toNat b.toNat =
      x.toNat + lowb y.toNat b.toNat * 2 ^ 64 := by
  rw [UInt64.toNat_or, shr_hi y b hb, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hb,
    Nat.shiftRight_eq_div_pow]
  have hlt : x.toNat / 2 ^ b.toNat < 2 ^ (64 - b.toNat) := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show b.toNat + (64 - b.toNat) = 64 by omega]; exact x.toNat_lt
  rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq]
  simp only [sh, lowb]
  have h2 : 2 ^ (64 - b.toNat) * 2 ^ b.toNat = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have := Nat.div_add_mod x.toNat (2 ^ b.toNat)
  rw [Nat.add_mul, Nat.mul_assoc, h2]
  rw [Nat.mul_comm (x.toNat / 2 ^ b.toNat)]
  omega
grind_pattern [arena_grind] shr_split => (x >>> b) ||| ((y <<< 1) <<< (63 - b))

/-! ## The division at the end -/

theorem pv_append (p : Array Word) (o w k : Nat) :
    pv p o (w + k) = pv p o w + wt w * pv p (o + w) k := by
  induction k with
  | zero => simp [pv]
  | succ k ih =>
    rw [← Nat.add_assoc, pv, ih, pv, wt_add w k (w + k) rfl,
      show o + (w + k) = o + w + k by omega]
    grind

theorem pv_ge_wt (p : Array Word) (o l : Nat) (hl : 0 < l) (hn : Norm p o l) :
    wt (l - 1) ≤ pv p o l := by
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pv]
  have : (p[o + j]?.getD 0) ≠ 0 := hn (by omega)
  have : 1 ≤ (p[o + j]?.getD 0).toNat := by
    rcases Nat.eq_zero_or_pos (p[o + j]?.getD 0).toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm)) this
    · exact h
  have := Nat.mul_le_mul_right (wt j) this
  omega

/-- The shift that skips `w < la` limbs: the quotient is what the loop computed. -/
theorem shr_val (P : Array Word) (oa la w o l S R : Nat) (ho : o = oa + w) (hl : l = la - w)
    (hw : w < la) (h1 : R * S ≤ pv P o l) (h2 : pv P o l < R * S + S) :
    pv P oa la / (S * wt w) = R := by
  have hA := pv_append P oa w (la - w)
  rw [show w + (la - w) = la by omega] at hA
  subst ho hl
  have h3 := pv_lt_wt P oa w
  have hS : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · subst h; omega
    · exact h
  have m1 : wt w * (R * S) ≤ wt w * pv P (oa + w) (la - w) := Nat.mul_le_mul_left _ h1
  have m2 : wt w * pv P (oa + w) (la - w) + wt w ≤ wt w * (R * S + S) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
  apply Nat.div_eq_of_lt_le <;> grind

/-- The quotient by an amount `b = k` of at most one limb that skips `w = k >> 6 < la` limbs, in
the shape the loop's post gives (`ShrPost`). Every variable of the pattern is bound by a term of
that post, so it fires about once (DESIGN.md, "Slow declarations": `shr_val`'s own pattern
`pv P oa la / (S * wt w), pv P o l, R * S` matched every `pv` and every product). -/
theorem shr_small (P Q R : Array Word) (oa la ob lb o l t r : Nat) (k : Word)
    (hk : pv Q ob lb = k.toNat) (ho : o = oa + (k >>> 6).toNat) (hl : l = la - (k >>> 6).toNat)
    (hw : (k >>> 6).toNat < la)
    (h : pv R t r * sh (k &&& 63).toNat + lowb (lv P o l 0) (k &&& 63).toNat = pv P o l) :
    pv P oa la / 2 ^ pv Q ob lb = pv R t r := by
  rw [hk, shamt]
  exact shr_val P oa la _ o l _ _ ho hl hw (by omega)
    (by have := lowb_lt (lv P o l 0) (k &&& 63).toNat; omega)
grind_pattern [natop_grind] shr_small => pv P oa la / 2 ^ pv Q ob lb,
  pv R t r * sh (k &&& 63).toNat, lowb (lv P o l 0) (k &&& 63).toNat

/-- Skipping all of `a`: the quotient is `0`. -/
theorem shr_big_w (P : Array Word) (oa la w S : Nat) (hw : la ≤ w) (hS : 0 < S) :
    pv P oa la / (S * wt w) = 0 := by
  apply Nat.div_eq_of_lt
  have := pv_lt_wt P oa la
  have : wt la ≤ wt w := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hw)
  have : wt w ≤ S * wt w := Nat.le_mul_of_pos_left _ hS
  omega
grind_pattern [natop_grind] shr_big_w => pv P oa la / (S * wt w)

/-- An amount of two or more limbs: the quotient is `0`. -/
theorem shr_big_b (P Q : Array Word) (oa la ob lb : Nat) (hn : Norm Q ob lb) (hl : 2 ≤ lb)
    (hla : la < 2 ^ 57) : pv P oa la / 2 ^ pv Q ob lb = 0 := by
  apply Nat.div_eq_of_lt
  have h1 := pv_lt_wt P oa la
  have h2 := pv_ge_wt Q ob lb (by omega) hn
  have h3 : wt 1 ≤ wt (lb - 1) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega))
  have h4 : 64 * la < pv Q ob lb := by
    have : wt 1 = 2 ^ 64 := rfl
    omega
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h4))
grind_pattern [natop_grind] shr_big_b => pv P oa la / 2 ^ pv Q ob lb, Norm Q ob lb

/-! ## `nat_shr(oa, la, ob, lb)` -/

/-- One pass over the shifted slice `(oa, n)` (`oa` already moved past the skipped limbs). -/
def shrLoop : Stmt := lblk (oa, la, ob, lb, top, n, w, b, i, x, y, pt, pb) {
  while i < n {
    y := call nat_limb(oa, n, i + 1);
    POOL⟨pt⟩[pb + i] := (x >> b) | ((y << 1) << (63 - b));
    x := y;
    i += 1
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natShr : FunDecl := lfn (oa, la, ob, lb) locals (top, n, w, b, i, x, y, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if lb < 2 {
    if lb == 1 { w := POOL⦃ob⦄ };
    b := w & 63;
    w := w >> 6;
    if w < la {
      oa := oa + w;
      n := la - w;
      if len(POOL⟨pt⟩) - pb < n { abort };
      x := POOL⦃oa⦄;
      ⟪shrLoop⟫;
      n := call nat_trim(top, n)
    }
  } else {
    if 144115188075855872 <= la { abort }
  };
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_shr`. -/
def natShrProg : Prog := natProg ++ [("nat_shr", natShr)]

/- `[0, 6, 2] >>> 65 = [3, 1]`: `a` at 0, `b = [65]` at 3, top 4. -/
#guard (run natShrProg 100 "nat_shr" [0, 3, 3, 1]
  { words := #[#[0, 6, 2, 65, 0, 0, 0], #[4]] }).toOption.map (fun (r, m) => (r, m.words)) ==
  some ([2], #[#[0, 6, 2, 65, 3, 1, 0], #[6]])
/- `a >>> 0 = a`; `[1] >>> 64 = 0`; `[1] >>> 2^64 = 0`. -/
#guard (run natShrProg 100 "nat_shr" [0, 2, 0, 0]
  { words := #[#[7, 9, 0, 0], #[2]] }).toOption.map (fun (r, m) => (r, m.words)) ==
  some ([2], #[#[7, 9, 7, 9], #[4]])
#guard (run natShrProg 100 "nat_shr" [0, 1, 1, 1]
  { words := #[#[1, 64, 0], #[2]] }).toOption.map (fun (r, m) => (r, m.words.back!)) ==
  some ([0], #[2])
#guard (run natShrProg 100 "nat_shr" [0, 1, 1, 2]
  { words := #[#[1, 0, 1, 0], #[3]] }).toOption.map (fun (r, m) => (r, m.words.back!)) ==
  some ([0], #[3])

section shr
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb) (Pg : Array Word) (C : Nat)

/-- The invariant of the pass over the shifted slice `(oa, n)`: `x` is limb `i`, and the result
so far times `2^s`, plus the low bits of limb `0`, is the first `i` limbs plus the low bits of
limb `i`, weighted. -/
def ShrInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 63 ∧ Pg.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  Agree (vpool s.mem) Pg (s.loc 4).toNat ∧
  (s.loc 4).toNat + (s.loc 5).toNat ≤ C ∧ (s.loc 0).toNat + (s.loc 5).toNat ≤ (s.loc 4).toNat ∧
  s.loc 11 = s.loc 4 >>> 40 ∧ s.loc 12 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 12).toNat + (s.loc 5).toNat ≤ (s.mem.arr64 (tierA 0 (s.loc 11))).size ∧
  (s.mem.arr64 (tierA 0 (s.loc 11))).size ≤ 2 ^ 40 ∧ (s.loc 11).toNat ≤ 1 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 7).toNat < 64 ∧ (s.loc 8).toNat ≤ (s.loc 5).toNat ∧
  (s.loc 9).toNat = lv Pg (s.loc 0).toNat (s.loc 5).toNat (s.loc 8).toNat ∧
  pv (vpool s.mem) (s.loc 4).toNat (s.loc 8).toNat * sh (s.loc 7).toNat +
      lowb (lv Pg (s.loc 0).toNat (s.loc 5).toNat 0) (s.loc 7).toNat =
    xv Pg (s.loc 0).toNat (s.loc 5).toNat (s.loc 8).toNat +
      lowb (s.loc 9).toNat (s.loc 7).toNat * wt (s.loc 8).toNat

def ShrPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧
  pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 6 = s₀.loc 6 ∧
  s'.loc 7 = s₀.loc 7 ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat * sh (s₀.loc 7).toNat +
      lowb (lv Pg (s₀.loc 0).toNat (s₀.loc 5).toNat 0) (s₀.loc 7).toNat =
    pv Pg (s₀.loc 0).toNat (s₀.loc 5).toNat

set_option maxHeartbeats 2000000 in
include hpl in
theorem shrLoop_spec (n : Nat) (s₀ : St) (h : ShrInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n shrLoop ⦃fun r s' => ShrPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [ShrInv, ShrPost] at h ⊢
    rw [exec, step_while (w := shrLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih, natLimb_spec p hpl n] <;>
      finish (splits := 20) [ShrInv, ShrPost]

include hpl in
theorem shrLoop_step_spec (n : Nat) (s₀ : St) (h : ShrInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) shrLoop ⦃fun r s' => ShrPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (shrLoop_spec p hpl Pg C (n + 1) s₀ h)

end shr

section shrFn
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_shr" = some natShr)

set_option maxHeartbeats 0 in
include hpl hpt hpn in
/-- `nat_shr` appends `a / 2^b` (`b` normalised), normalised, at the old top and moves the top
past it; nothing below the old top changes, and no other array but `CTL[0]`. -/
theorem natShr_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_shr" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat / 2 ^ pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  replace ha := ha.1
  replace hb := hb.1
  rw [invoke_eq _ hpn]
  simp only [callFn, natShr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      shrLoop_step_spec p hpl (vpool s₀.mem) (pcap s₀.mem) n, natTrim_spec p hpt n]
    all_goals (try simp only [ShrInv, ShrPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc, St.setLocs, BinOp.eval, Cmp.eval, reduceIte,
      Nat.reduceEqDiff, Locals.init, List.getD_cons_zero, List.getD_cons_succ,
      UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals (try (set_option maxHeartbeats 200000 in grind (splits := 40) [arena_grind, lang_grind, natop_grind]))

end shrFn

end L.Arena
