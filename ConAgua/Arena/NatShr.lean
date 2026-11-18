module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatShiftFacts
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve

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

/-! ## The division at the end -/

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

/-- The shift proper over the slice `(oa, n)` (`oa` already moved past the skipped limbs, `n ≥ 1`):
`shr_n` over its first `n - 1` limbs (each with the low bits of the next), its last limb shifted
alone. Locals `(oa, la, ob, lb, top, n, w, b, c, pt, pb)`. -/
def shrCore : Stmt := lblk (oa, la, ob, lb, top, n, w, b, c, pt, pb) {
  c := call shr_n(top, oa, n - 1, b);
  POOL⟨pt⟩[pb + (n - 1)] := POOL⦃oa + (n - 1)⦄ >> b
}

/-- The amount `b` (one limb at most) splits into `w = b >> 6` whole limbs to skip and `b & 63`
bits; `shrCore` shifts what is left, `nat_trim`. The pass is a leaf (`NatLeaf.lean`).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natShr : FunDecl := lfn (oa, la, ob, lb) locals (top, n, w, b, c, pt, pb) {
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
      ⟪shrCore⟫;
      n := call nat_trim(top, n)
    }
  } else {
    if 144115188075855872 <= la { abort }
  };
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_shr`. -/
def natShrProg : Prog := natProg ++ [("shr_n", shrN), ("nat_shr", natShr)]

/- `[0, 6, 2] >>> 65 = [3, 1]`: `a` at 0, `b = [65]` at 3, top 4. -/
#guard (run natShrProg 100 "nat_shr" [0, 3, 3, 1]
  (Mem.ofWords [(POOL, #[0, 6, 2, 65, 0, 0, 0]), (CTL, #[4])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([2], #[0, 6, 2, 65, 3, 1, 0], #[6])
/- `a >>> 0 = a`; `[1] >>> 64 = 0`; `[1] >>> 2^64 = 0`. -/
#guard (run natShrProg 100 "nat_shr" [0, 2, 0, 0]
  (Mem.ofWords [(POOL, #[7, 9, 0, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([2], #[7, 9, 7, 9], #[4])
#guard (run natShrProg 100 "nat_shr" [0, 1, 1, 1]
  (Mem.ofWords [(POOL, #[1, 64, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 CTL)) ==
  some ([0], #[2])
#guard (run natShrProg 100 "nat_shr" [0, 1, 1, 2]
  (Mem.ofWords [(POOL, #[1, 0, 1, 0]), (CTL, #[3])])).toOption.map (fun (r, m) => (r, m.arr64 CTL)) ==
  some ([0], #[3])

/-- The shift's last limb on its own: `L >> b` times `2^b`, plus `L`'s low bits, is `L`. -/
theorem shr_last (L b : Word) (hb : b.toNat < 64) :
    (L >>> b).toNat * sh b.toNat + lowb L.toNat b.toNat = L.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow]
  simp only [sh, lowb]
  have := Nat.div_add_mod L.toNat (2 ^ b.toNat)
  rw [Nat.mul_comm]; omega

/-- `shrCore`'s value, in the shape of its goal: `shr_n` wrote the first `n - 1` limbs at `T`
(`m1`), the last limb is limb `n - 1` of the slice shifted alone. -/
theorem shr_core_goal (m0 m1 : Mem) (T oa n b Tt Ti : Word) (hTt : Tt = T >>> 40)
    (hTi : Ti = T &&& 1099511627775) (hn : 1 ≤ n.toNat) (hT41 : T.toNat < 2 ^ 41)
    (ha : oa.toNat + n.toNat ≤ T.toNat) (hb : b.toNat < 64)
    (hc1 : pcap m1 < 2 ^ 64)
    (hst : (Ti + (n - 1)).toNat < (m1.arr64 (tierA POOL Tt)).size)
    (hld : ((oa + (n - 1)) &&& 1099511627775).toNat <
      (m1.arr64 (tierA POOL ((oa + (n - 1)) >>> 40))).size)
    (h1 : Off (vpool m1) (vpool m0) T.toNat (n - 1).toNat)
    (e1 : pv (vpool m1) T.toNat (n - 1).toNat * sh b.toNat +
        lowb ((vpool m0)[oa.toNat]?.getD 0).toNat b.toNat =
      pv (vpool m0) oa.toNat (n - 1).toNat +
        lowb ((vpool m0)[oa.toNat + (n - 1).toNat]?.getD 0).toNat b.toNat * wt (n - 1).toNat) :
    pv (vpool (m1.set64 (tierA POOL Tt) (Ti + (n - 1))
        ((m1.arr64 (tierA POOL ((oa + (n - 1)) >>> 40)))[((oa + (n - 1)) &&& 1099511627775).toNat] >>> b)))
        T.toNat n.toNat * sh b.toNat + lowb (lv (vpool m0) oa.toNat n.toNat 0) b.toNat =
      pv (vpool m0) oa.toNat n.toNat := by
  have hsz : (m1.arr64 (tierA POOL Tt)).size ≤ 2 ^ 40 := Nat.le_of_lt (pcap_tier m1 Tt hc1)
  subst hTt hTi
  have hk : (n - 1).toNat = n.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
  have hok : (oa + (n - 1)).toNat = oa.toNat + (n.toNat - 1) := by
    rw [UInt64.toNat_add, hk]; exact Nat.mod_eq_of_lt (by omega)
  have hvs0 := vpool_size m0
  have hvs1 := vpool_size m1
  have hTn : T.toNat + (n.toNat - 1) < 2 ^ 41 := by
    have := win_lt m1 T (n - 1) hT41 (by omega) hsz hst; omega
  have eL : (m1.arr64 (tierA POOL ((oa + (n - 1)) >>> 40)))[((oa + (n - 1)) &&& 1099511627775).toNat] =
      (vpool m0)[oa.toNat + (n.toNat - 1)]'(by omega) := by
    rw [vpool_ld m1 (oa + (n - 1)) hld (by omega)]
    have := h1 (oa.toNat + (n.toNat - 1)) (Or.inl (by omega))
    simp only [Array.getElem?_eq_getElem (by omega : oa.toNat + (n.toNat - 1) < (vpool m1).size),
      Array.getElem?_eq_getElem (by omega : oa.toNat + (n.toNat - 1) < (vpool m0).size),
      Option.some.injEq] at this
    simp only [hok]; exact this
  rw [eL, st_win m1 T (n - 1) _ hT41 (by omega) hsz hst, hk]
  rw [hk] at e1
  have hn1 : n.toNat = (n.toNat - 1) + 1 := by omega
  rw [pv_set_succ (vpool m1) T.toNat (n.toNat - 1) n.toNat (T.toNat + (n.toNat - 1)) _ hn1 rfl (by omega),
    pv_succ (vpool m0) oa.toNat (n.toNat - 1) n.toNat (oa.toNat + (n.toNat - 1)) hn1 rfl (by omega)]
  have hlv : lv (vpool m0) oa.toNat n.toNat 0 = ((vpool m0)[oa.toNat]?.getD 0).toNat := by
    simp [lv]; omega
  rw [hlv]
  rw [Array.getElem?_eq_getElem (by omega : oa.toNat + (n.toNat - 1) < (vpool m0).size),
    Option.getD_some] at e1
  have hl := shr_last (vpool m0)[oa.toNat + (n.toNat - 1)] b hb
  generalize (vpool m0)[oa.toNat + (n.toNat - 1)] = L at *
  generalize pv (vpool m1) T.toNat (n.toNat - 1) = A at *
  generalize pv (vpool m0) oa.toNat (n.toNat - 1) = B at *
  generalize wt (n.toNat - 1) = W at *
  generalize sh b.toNat = S at *
  generalize lowb ((vpool m0)[oa.toNat]?.getD 0).toNat b.toNat = L0 at *
  generalize (L >>> b).toNat = Q at *
  generalize lowb L.toNat b.toNat = Lo at *
  grind


/-- The pool below `T` is kept by `shrCore`. -/
theorem shr_core_agree (m0 m1 : Mem) (T k v Tt Ti : Word) (hTt : Tt = T >>> 40)
    (hTi : Ti = T &&& 1099511627775) (hT41 : T.toNat < 2 ^ 41) (hk41 : k.toNat < 2 ^ 41)
    (hc1 : pcap m1 < 2 ^ 64)
    (hst : (Ti + k).toNat < (m1.arr64 (tierA POOL Tt)).size)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat) :
    Agree (vpool (m1.set64 (tierA POOL Tt) (Ti + k) v)) (vpool m0) T.toNat := by
  have hsz : (m1.arr64 (tierA POOL Tt)).size ≤ 2 ^ 40 := Nat.le_of_lt (pcap_tier m1 Tt hc1)
  subst hTt hTi
  rw [st_win m1 T k v hT41 hk41 hsz hst]
  intro j hj
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by omega)]
  exact h1 j (Or.inl hj)

section shrCoreSec
variable (p : Prog) (hps : p.lookup "shr_n" = some shrN)

/-- `shrCore`'s precondition: locals `(oa, la, ob, lb, top, n, w, b, c, pt, pb)`, the slice
`(oa, n)` below the top, room for `n ≥ 1` limbs in the top's tier. -/
def ShrCorePre (s : St) : Prop :=
  pcap s.mem < 2 ^ 64 ∧ (s.loc 4).toNat < 2 ^ 41 ∧ (s.loc 0).toNat + (s.loc 5).toNat ≤ (s.loc 4).toNat ∧
  1 ≤ (s.loc 5).toNat ∧ (s.loc 7).toNat < 64 ∧
  s.loc 9 = s.loc 4 >>> 40 ∧ s.loc 10 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 10).toNat + (s.loc 5).toNat ≤ (s.mem.arr64 (tierA POOL (s.loc 9))).size ∧
  (s.loc 4).toNat + (s.loc 5).toNat ≤ pcap s.mem

def ShrCorePost (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
  s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
  Agree (vpool s'.mem) (vpool s₀.mem) (s₀.loc 4).toNat ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat * sh (s₀.loc 7).toNat +
      lowb (lv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 5).toNat 0) (s₀.loc 7).toNat =
    pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 5).toNat

include hps in
theorem shrCore_spec (n : Nat) (s₀ : St) (h : ShrCorePre s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) shrCore ⦃fun r s' => ShrCorePost s₀ r s'; ⊤⦄ := by
  simp only [ShrCorePre, ShrCorePost] at h ⊢
  obtain ⟨hs, hT41, ha, hn, hb, h9, h10, hroom, hcap⟩ := h
  have hsz := pcap_tier s₀.mem (s₀.loc 9) hs
  unfold shrCore
  vcgen [step, evalE, evalArgs, setLoc, setLocs, ld64, st64, shrN_spec p hps n]
  all_goals (try simp only [LocEq] at *)
  all_goals (try dsimp only at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    BinOp.eval.eq_1, BinOp.eval.eq_2, BinOp.eval.eq_4, BinOp.eval.eq_8, reduceIte, Nat.reduceEqDiff])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals first
    | (grind (splits := 10) [arena_grind, lang_grind]; done)
    | (with_reducible apply shr_core_goal
       case h1 => with_reducible assumption
       case e1 => with_reducible assumption
       all_goals grind)
    | (with_reducible apply shr_core_agree
       case h1 => with_reducible assumption
       all_goals grind)

end shrCoreSec

/-- `nat_shr`'s result: the trimmed `n` limbs `shrCore` wrote are the quotient (`shr_small`). -/
theorem shr_final (m : Mem) (P Q : Array Word) (T T' X n n' r R w k : Word) (oa la ob lb o : Nat)
    (hX : X = T) (hR : R = r) (hT : T' = T) (hn : n' = n)
    (et : pv (vpool m) T'.toNat r.toNat = pv (vpool m) T'.toNat n'.toNat)
    (hk : pv Q ob lb = k.toNat) (ho : o = oa + (k >>> 6).toNat)
    (hl : n.toNat = la - (k >>> 6).toNat) (hw : (k >>> 6).toNat < la)
    (h : pv (vpool m) T.toNat n.toNat * sh (k &&& 63).toNat +
        lowb (lv P o n.toNat 0) (k &&& 63).toNat = pv P o n.toNat) :
    pv (vpool (m.set64 CTL 0 w)) X.toNat R.toNat = pv P oa la / 2 ^ pv Q ob lb := by
  subst X R T' n'
  rw [vpool_ctl, et]
  exact (shr_small P Q (vpool m) oa la ob lb o n.toNat T.toNat n.toNat k hk ho hl hw h).symm

section shrFn
variable (p : Prog) (hps : p.lookup "shr_n" = some shrN)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_shr" = some natShr)

-- the whole function's paths (the amount's three cases, the room check, `nat_trim`) in one
-- declaration: about 16 s, over the default budget (it had none before the leaf split)
set_option maxHeartbeats 1000000 in
include hps hpt hpn in
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
  have hok2 := hok.ctl; have hok3 := hok.cap; have hok4 := hok.top; have hok6 := hok.inTier
  clear hok
  replace ha := ha.1
  replace hb := hb.1
  have hs : pcap s₀.mem < 2 ^ 64 := by omega
  rw [invoke_eq _ hpn]
  simp only [callFn, natShr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      shrCore_spec p hps n, natTrim_spec p hpt n]
    all_goals (try simp only [LocEq, ShrCorePre, ShrCorePost] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval.eq_1,
      BinOp.eval.eq_2, BinOp.eval.eq_4, BinOp.eval.eq_8, Cmp.eval, reduceIte, Nat.reduceEqDiff,
      UInt64.toNat_zero, Sig.retVal, Sig.retOr] at *)
    all_goals split_clear_locs
    all_goals (try and_intros)
    all_goals first
      | (with_reducible apply shr_final
         case h => with_reducible assumption
         case et => with_reducible assumption
         all_goals first | rfl | grind [arena_grind, natop_grind, Mem.top_eq])
      | (grind (splits := 10) [arena_grind, lang_grind, natop_grind, Mem.top_eq, vpool_ctl, Norm]; done)

end shrFn

end L.Arena
