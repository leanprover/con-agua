module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr
public import ConAgua.Arena.NatAdd
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve

@[expose] public section

/-!
# `Nat.shiftLeft` on the limb pool: `nat_shl`

`nat_shl(oa, la, ob, lb)` is `a <<< b = a * 2^b` for two pool slices (con-ron's
`shift_left_nat`, `shl_onto`, `shl_bits_from`, `push_zeros`, `push_zeros_nat`,
`ron/nat.rs:313-403`). The amount `b` is a slice too; an amount of more than one limb, with
`a ≠ 0`, cannot fit any pool (con-ron runs out of memory pushing `u64::MAX` zero limbs), so it is
an `abort` here. Otherwise `k = b[0]`: `k >> 6` zero limbs, then `a` shifted by `k & 63` bits,
one pass with a carry, then `nat_trim`.

The bit shift is branch-free: limb `i` is `(x << s) | c` and the next carry
`(x >> 1) >> (63 - s)`, which is `x >> (64 - s)` for `s ≥ 1` and `0` for `s = 0`; con-ron
special-cases `s = 0` because `x >> 64` is not a legal `u64` shift. `shl_split` is the digit
equation `low + carry · 2^64 = x · 2^s + c`, the shape of `adc_split`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `nat_shl(oa, la, ob, lb)` -/

/-- The shift proper: `zero_n` over the `w` skipped limbs, `shl_n` over `a` at `top + w`, its carry
as the top limb. Locals `(oa, la, ob, lb, top, n, w, b, c, pt, pb)`. -/
def shlCore : Stmt := lblk (oa, la, ob, lb, top, n, w, b, c, pt, pb) {
  c := call zero_n(top, w);
  c := call shl_n(top + w, oa, la, b, 0);
  POOL⟨pt⟩[pb + (w + la)] := c
}

/-- The amount (one limb at most) splits into `w = b >> 6` zero limbs and `b & 63` bits;
`shlCore`, `nat_trim`. The passes are leaves (`NatLeaf.lean`).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natShl : FunDecl := lfn (oa, la, ob, lb) locals (top, n, w, b, c, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if la != 0 {
    if 1 < lb { abort };
    if lb == 1 { w := POOL⦃ob⦄ };
    b := w & 63;
    w := w >> 6;
    if len(POOL⟨pt⟩) - pb <= la { abort };
    if len(POOL⟨pt⟩) - pb - la - 1 < w { abort };
    ⟪shlCore⟫;
    n := call nat_trim(top, w + la + 1)
  };
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_shl`. -/
def natShlProg : Prog := natProg ++ [("nat_shl", natShl)]

/- `[3, 1] <<< 65 = [0, 6, 2]`: `a` at 0 (2 limbs), `b = [65]` at 2, top 3. -/
#guard (run natShlProg 100 "nat_shl" [0, 2, 2, 1]
  (Mem.ofWords [(POOL, #[3, 1, 65, 0, 0, 0, 0]), (CTL, #[3])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([3], #[3, 1, 65, 0, 6, 2, 0], #[6])
/- `2^63 <<< 1 = 2^64`; `a <<< 0 = a`; `0 <<< 2^64 = 0` (no abort). -/
#guard (run natShlProg 100 "nat_shl" [0, 1, 1, 1]
  (Mem.ofWords [(POOL, #[0x8000000000000000, 1, 0, 0, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([2], #[0x8000000000000000, 1, 0, 1, 0], #[4])
#guard (run natShlProg 100 "nat_shl" [0, 1, 1, 0]
  (Mem.ofWords [(POOL, #[7, 0, 0]), (CTL, #[1])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([1], #[7, 7, 0], #[2])
#guard (run natShlProg 100 "nat_shl" [0, 0, 0, 2]
  (Mem.ofWords [(POOL, #[0, 1, 0]), (CTL, #[2])])).toOption.map (·.1) == some [0]


/-- `shlCore`'s value, in the shape of its goal: `zero_n` wrote the `w` limbs at `T` (`m1`),
`shl_n` the `la` limbs after them (`m2`), the carry `c` goes on top. -/
theorem shl_core_goal (m0 m1 m2 : Mem) (T oa w la b c c0 Tt Ti : Word) (hc0 : c0 = 0)
    (hTt : Tt = T >>> 40) (hTi : Ti = T &&& 1099511627775) (hc2 : pcap m2 < 2 ^ 64)
    (hT41 : T.toNat < 2 ^ 41) (hw41 : w.toNat + la.toNat < 2 ^ 41)
    (ha : oa.toNat + la.toNat ≤ T.toNat)
    (hst : (Ti + (w + la)).toNat < (m2.arr64 (tierA POOL Tt)).size)
    (h1 : Off (vpool m1) (vpool m0) T.toNat w.toNat) (z1 : pv (vpool m1) T.toNat w.toNat = 0)
    (h2 : Off (vpool m2) (vpool m1) (T + w).toNat la.toNat)
    (e2 : pv (vpool m2) (T + w).toNat la.toNat + c.toNat * wt la.toNat =
      pv (vpool m1) oa.toNat la.toNat * sh b.toNat + c0.toNat) :
    pv (vpool (m2.set64 (tierA POOL Tt) (Ti + (w + la)) c)) T.toNat (w.toNat + la.toNat + 1) =
      pv (vpool m0) oa.toNat la.toNat * sh b.toNat * wt w.toNat := by
  subst c0 hTt hTi
  have hsz : (m2.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40 := Nat.le_of_lt (pcap_tier m2 _ hc2)
  have hT : T.toNat + (w + la).toNat < 2 ^ 41 := win_lt m2 T (w + la) hT41 (by
    rw [UInt64.toNat_add]; omega) hsz hst
  have hwl : (w + la).toNat = w.toNat + la.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hTw : (T + w).toNat = T.toNat + w.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  rw [hwl] at hT
  rw [hTw] at h2 e2
  have hvs := vpool_size m2
  rw [st_win m2 T (w + la) c hT41 (by omega) hsz hst, hwl,
    pv_set_succ (vpool m2) T.toNat (w.toNat + la.toNat) (w.toNat + la.toNat + 1) (T.toNat + (w.toNat + la.toNat)) _
      rfl (by omega) (by omega)]
  have a2 := pv_append (vpool m2) T.toNat w.toNat la.toNat
  have d2 : pv (vpool m2) T.toNat w.toNat = pv (vpool m1) T.toNat w.toNat :=
    Off.pv_disj _ _ _ _ _ _ h2 (Or.inl (by omega))
  have d1 : pv (vpool m1) oa.toNat la.toNat = pv (vpool m0) oa.toNat la.toNat :=
    Off.pv_disj _ _ _ _ _ _ h1 (Or.inl ha)
  have wl := wt_add w.toNat la.toNat (w.toNat + la.toNat) rfl
  rw [a2, d2, z1, wl, ← Nat.add_assoc T.toNat w.toNat la.toNat] at *
  rw [d1, UInt64.toNat_zero, Nat.add_zero] at e2
  generalize pv (vpool m2) (T.toNat + w.toNat) la.toNat = A at *
  generalize pv (vpool m0) oa.toNat la.toNat = B at *
  generalize wt w.toNat = W at *
  generalize wt la.toNat = L at *
  generalize sh b.toNat = S at *
  have : W * (A + c.toNat * L) = W * (B * S) := by rw [e2]
  grind

/-- The pool below `T` is kept by `shlCore`. -/
theorem shl_core_agree (m0 m1 m2 : Mem) (T w la c Tt Ti : Word)
    (hTt : Tt = T >>> 40) (hTi : Ti = T &&& 1099511627775) (hc2 : pcap m2 < 2 ^ 64)
    (hT41 : T.toNat < 2 ^ 41) (hw41 : w.toNat + la.toNat < 2 ^ 41)
    (hst : (Ti + (w + la)).toNat < (m2.arr64 (tierA POOL Tt)).size)
    (h1 : Off (vpool m1) (vpool m0) T.toNat w.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + w).toNat la.toNat) :
    Agree (vpool (m2.set64 (tierA POOL Tt) (Ti + (w + la)) c)) (vpool m0) T.toNat := by
  subst hTt hTi
  have hsz : (m2.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40 := Nat.le_of_lt (pcap_tier m2 _ hc2)
  have hwl : (w + la).toNat = w.toNat + la.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hT : T.toNat + (w + la).toNat < 2 ^ 41 := win_lt m2 T (w + la) hT41 (by omega) hsz hst
  have hTw : (T + w).toNat = T.toNat + w.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  rw [hTw] at h2
  rw [st_win m2 T (w + la) c hT41 (by omega) hsz hst]
  intro j hj
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by omega)]
  exact (h2 j (Or.inl (by omega))).trans (h1 j (Or.inl hj))

section shlCoreSec
variable (p : Prog) (hpz : p.lookup "zero_n" = some zeroN) (hps : p.lookup "shl_n" = some shlN)

/-- `shlCore`'s precondition: locals `(oa, la, ob, lb, top, n, w, b, c, pt, pb)`. -/
def ShlCorePre (s : St) : Prop :=
  pcap s.mem < 2 ^ 64 ∧ (s.loc 4).toNat < 2 ^ 41 ∧ (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 7).toNat < 64 ∧ s.loc 9 = s.loc 4 >>> 40 ∧ s.loc 10 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 10).toNat + (s.loc 6).toNat + (s.loc 1).toNat + 1 ≤ (s.mem.arr64 (tierA POOL (s.loc 9))).size ∧
  (s.loc 4).toNat + (s.loc 6).toNat + (s.loc 1).toNat + 1 ≤ pcap s.mem

def ShlCorePost (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
  PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
  Agree (vpool s'.mem) (vpool s₀.mem) (s₀.loc 4).toNat ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat ((s₀.loc 6).toNat + (s₀.loc 1).toNat + 1) =
    pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat * sh (s₀.loc 7).toNat * wt (s₀.loc 6).toNat

include hpz hps in
theorem shlCore_spec (n : Nat) (s₀ : St) (h : ShlCorePre s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) shlCore ⦃fun r s' => ShlCorePost s₀ r s'; ⊤⦄ := by
  simp only [ShlCorePre, ShlCorePost] at h ⊢
  obtain ⟨hs, hT41, ha, hb, h9, h10, hroom, hcap⟩ := h
  have hsz := pcap_tier s₀.mem (s₀.loc 9) hs
  unfold shlCore
  vcgen [step, evalE, evalArgs, setLoc, setLocs, st64, zeroN_spec p hpz n, shlN_spec p hps n]
  all_goals (try simp only [LocEq] at *)
  all_goals (try dsimp only at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    BinOp.eval.eq_1, reduceIte, Nat.reduceEqDiff])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals first
    | (grind (splits := 10) [arena_grind, lang_grind]; done)
    | (with_reducible apply shl_core_goal
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       case e2 => with_reducible assumption
       all_goals first | rfl | grind)
    | (with_reducible apply shl_core_agree
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       all_goals grind)

end shlCoreSec

theorem shr6_zero : (0 : Word) >>> 6 = 0 := rfl
theorem and63_zero : (0 : Word) &&& 63 = 0 := rfl

/-- `nat_shl`'s result: the trimmed `w + la + 1` limbs `shlCore` wrote are `a · 2^b`, `b = k` of
at most one limb (`shamt`). -/
theorem shl_final (m : Mem) (P Q : Array Word) (T T' X w la r R v k n' : Word) (oa ob lb : Nat)
    (hX : X = T) (hR : R = r) (hT : T' = T) (hn' : n' = w + la + 1)
    (hw41 : w.toNat + la.toNat + 1 < 2 ^ 64)
    (et : pv (vpool m) T'.toNat r.toNat = pv (vpool m) T'.toNat n'.toNat)
    (hk : pv Q ob lb = k.toNat) (hw : w = k >>> 6)
    (h : pv (vpool m) T.toNat (w.toNat + la.toNat + 1) =
      pv P oa la.toNat * sh (k &&& 63).toNat * wt w.toNat) :
    pv (vpool (m.set64 CTL 0 v)) X.toNat R.toNat = pv P oa la.toNat * 2 ^ pv Q ob lb := by
  subst X R T' n' hw
  have e : (k >>> 6 + la + 1).toNat = (k >>> 6).toNat + la.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_one]; omega
  rw [vpool_ctl, et, e, h, hk, shamt, Nat.mul_assoc]

section shlFn
variable (p : Prog) (hpz : p.lookup "zero_n" = some zeroN) (hps : p.lookup "shl_n" = some shlN)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_shl" = some natShl)

-- the whole function's paths (the amount's cases, the two room checks, `nat_trim`) in one
-- declaration: about 15 s, over the default budget (it had 8M before the leaf split)
set_option maxHeartbeats 1000000 in
include hpz hps hpt hpn in
/-- `nat_shl` appends `a * 2^b`, normalised, at the old top and moves the top past it; nothing
below the old top changes, and no other array but `CTL[0]`. -/
theorem natShl_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_shl" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat * 2 ^ pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  have hok2 := hok.ctl; have hok3 := hok.cap; have hok4 := hok.top; have hok6 := hok.inTier
  clear hok
  replace ha := ha.1
  replace hb := hb.1
  have hs : pcap s₀.mem < 2 ^ 64 := by omega
  rw [invoke_eq _ hpn]
  simp only [callFn, natShl]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      shlCore_spec p hpz hps n, natTrim_spec p hpt n]
    all_goals (try simp only [LocEq, ShlCorePre, ShlCorePost] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval.eq_1,
      BinOp.eval.eq_2, BinOp.eval.eq_4, BinOp.eval.eq_8, Cmp.eval, reduceIte, Nat.reduceEqDiff,
      UInt64.toNat_zero, Sig.retVal, Sig.retOr] at *)
    all_goals split_clear_locs
    all_goals (try and_intros)
    all_goals first
      | (with_reducible apply shl_final
         case h => with_reducible assumption
         case et => with_reducible assumption
         all_goals first | rfl | grind [arena_grind, natop_grind, Mem.top_eq])
      | (grind (splits := 10) [arena_grind, lang_grind, natop_grind, Mem.top_eq, vpool_ctl, Norm]; done)

end shlFn

end L.Arena
