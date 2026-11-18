module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr
public import ConAgua.Arena.NatAdd
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
# Truncated subtraction on the limb pool: `nat_sub`

`nat_sub(oa, la, ob, lb)` is Lean's `a - b` (`0` when `a < b`), con-ron's `sub`/`sub_from`
(`ron/nat.rs:270-300`). con-ron compares first (`cmp`) and subtracts only when `a > b`; here `b`
is trimmed when it is longer than `a` (still longer: `a < b`), then the leaves `sub_n` and `sub_1`
(`NatLeaf.lean`) subtract, and the borrow out of the top limb decides: `1` means `a < b`, and the
result is `0`. This needs neither normalised inputs nor `nat_cmp`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `nat_sub(oa, la, ob, lb)` -/

/-- The subtraction proper, `b` of length `n` (`b` trimmed if it was longer than `a`): `sub_n` over
`b`'s limbs, `sub_1` over the rest of `a`, the result trimmed, or `0` on a borrow out or if `b` is
still longer. -/
def subCore : Stmt := lblk (oa, la, ob, lb, top, n, c, pt, pb) {
  if n <= la {
    c := call sub_n(top, oa, ob, n, 0);
    c := call sub_1(top + n, oa + n, la - n, c);
    n := 0;
    if c == 0 { n := call nat_trim(top, la) }
  } else { n := 0 }
}

/-- `sub_n` over `b`'s limbs, `sub_1` over the rest of `a`; a borrow out means `a < b` and the
result is `0`. If `b` is longer than `a`, it is trimmed first (the inputs need not be normalised):
still longer, `a < b`. The passes are leaves (`NatLeaf.lean`).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natSub : FunDecl := lfn (oa, la, ob, lb) locals (top, n, c, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if la < lb { n := lb };
  if len(POOL⟨pt⟩) - pb < n { abort };
  n := lb;
  if la < lb { n := call nat_trim(ob, lb) };
  ⟪subCore⟫;
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_sub`. -/
def natSubProg : Prog := natProg ++ [("sub_n", subN), ("sub_1", sub1), ("nat_sub", natSub)]

/- `2^64 - 1 = [max]`: operands `[0, 1]` at 0 and `[1]` at 2, top 3. -/
#guard (run natSubProg 100 "nat_sub" [0, 2, 2, 1]
  (Mem.ofWords [(POOL, #[0, 1, 1, 0, 0]), (CTL, #[3])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([1], #[0, 1, 1, 0xFFFFFFFFFFFFFFFF, 0], #[4])
/- `1 - 2^64 = 0`, and `5 - 5 = 0`; the top stays. -/
#guard (run natSubProg 100 "nat_sub" [2, 1, 0, 2]
  (Mem.ofWords [(POOL, #[0, 1, 1, 0, 0]), (CTL, #[3])])).toOption.map (fun (r, m) => (r, m.arr64 CTL)) ==
  some ([0], #[3])
#guard (run natSubProg 100 "nat_sub" [0, 1, 1, 1]
  (Mem.ofWords [(POOL, #[5, 5, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 CTL)) ==
  some ([0], #[2])

/-! ## Composing the passes -/

/-- The value of `nat_sub`'s result on arrays: `sub_n` wrote `k` limbs (`P1`), `sub_1` the
`l - k` limbs of `a`'s rest (`P2`). -/
theorem sub_pv (P0 P1 P2 : Array Word) (T x y k l c1 c2 : Nat) (hk : k ≤ l) (hx : x + l ≤ T)
    (h1 : Off P1 P0 T k) (h2 : Off P2 P1 (T + k) (l - k))
    (e1 : pv P1 T k + pv P0 y k + 0 = pv P0 x k + c1 * wt k)
    (e2 : pv P2 (T + k) (l - k) + c1 = pv P1 (x + k) (l - k) + c2 * wt (l - k)) :
    pv P2 T l + pv P0 y k = pv P0 x l + c2 * wt l := by
  have a2 := pv_append P2 T k (l - k)
  have a0 := pv_append P0 x k (l - k)
  rw [show k + (l - k) = l by omega] at a2 a0
  have d2 : pv P2 T k = pv P1 T k := Off.pv_disj P2 P1 (T + k) (l - k) T k h2 (Or.inl (by omega))
  have d1 : pv P1 (x + k) (l - k) = pv P0 (x + k) (l - k) :=
    Off.pv_disj P1 P0 T k (x + k) (l - k) h1 (Or.inl (by omega))
  have w := wt_add k (l - k) l (by omega)
  rw [a2, a0, d2, w]
  rw [d1] at e2
  generalize pv P1 T k = A at *
  generalize pv P2 (T + k) (l - k) = B at *
  generalize pv P0 (x + k) (l - k) = D at *
  generalize wt k = W at *
  generalize wt (l - k) = W' at *
  have : W * (B + c1) = W * (D + c2 * W') := by rw [e2]
  grind

/-- `sub_pv` at the machine's words: the borrow out `v` and the identity it satisfies. -/
theorem sub_words (m0 m1 m2 : Mem) (T x y k l c1 v : Word)
    (hT41 : T.toNat < 2 ^ 41) (hk41 : k.toNat < 2 ^ 41)
    (hk : k.toNat ≤ l.toNat) (hx : x.toNat + l.toNat ≤ T.toNat)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat)
    (e1 : pv (vpool m1) T.toNat k.toNat + pv (vpool m0) y.toNat k.toNat + 0 =
      pv (vpool m0) x.toNat k.toNat + c1.toNat * wt k.toNat)
    (e2 : pv (vpool m2) (T + k).toNat (l - k).toNat + c1.toNat =
      pv (vpool m1) (x + k).toNat (l - k).toNat + v.toNat * wt (l - k).toNat) :
    pv (vpool m2) T.toNat l.toNat + pv (vpool m0) y.toNat k.toNat =
      pv (vpool m0) x.toNat l.toNat + v.toNat * wt l.toNat := by
  have hTk : (T + k).toNat = T.toNat + k.toNat := w_add T k (by omega)
  have hxk : (x + k).toNat = x.toNat + k.toNat := w_add x k (by omega)
  have hlk : (l - k).toNat = l.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hk)
  rw [hTk, hlk] at h2 e2
  rw [hxk] at e2
  exact sub_pv _ _ _ T.toNat x.toNat y.toNat k.toNat l.toNat c1.toNat v.toNat hk hx h1 h2 e1 e2

/-- No borrow: the result is `a - b` (`b` read at its trimmed length `k`, of the same value as at
its length `K`). -/
theorem sub_core_ok (m0 m1 m2 : Mem) (T x y k l c1 v r K c0 : Word) (hc0 : c0 = 0) (hv : v = 0)
    (hT41 : T.toNat < 2 ^ 41) (hk41 : k.toNat < 2 ^ 41)
    (hk : k.toNat ≤ l.toNat) (hx : x.toNat + l.toNat ≤ T.toNat)
    (hK : pv (vpool m0) y.toNat k.toNat = pv (vpool m0) y.toNat K.toNat)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat)
    (e1 : pv (vpool m1) T.toNat k.toNat + pv (vpool m0) y.toNat K.toNat + c0.toNat =
      pv (vpool m0) x.toNat k.toNat + c1.toNat * wt k.toNat)
    (e2 : pv (vpool m2) (T + k).toNat (l - k).toNat + c1.toNat =
      pv (vpool m1) (x + k).toNat (l - k).toNat + v.toNat * wt (l - k).toNat)
    (et : pv (vpool m2) T.toNat r.toNat = pv (vpool m2) T.toNat l.toNat) :
    pv (vpool m2) T.toNat r.toNat = pv (vpool m0) x.toNat l.toNat - pv (vpool m0) y.toNat K.toNat := by
  subst hc0
  rw [← hK] at e1
  have e := sub_words m0 m1 m2 T x y k l c1 v hT41 hk41 hk hx h1 h2 e1 e2
  rw [et, ← hK]
  have hv0 : v.toNat = 0 := by simp [hv]
  rw [hv0, Nat.zero_mul, Nat.add_zero] at e
  omega

/-- A borrow: `a < b`, the result `0` is `a - b`. -/
theorem sub_core_bor (m0 m1 m2 : Mem) (P : Array Word) (T X x y k l c1 v K R c0 : Word) (hc0 : c0 = 0) (hR : R = 0)
    (hv0 : v ≠ 0) (hv1 : v.toNat ≤ 1)
    (hT41 : T.toNat < 2 ^ 41) (hk41 : k.toNat < 2 ^ 41)
    (hk : k.toNat ≤ l.toNat) (hx : x.toNat + l.toNat ≤ T.toNat)
    (hK : pv (vpool m0) y.toNat k.toNat = pv (vpool m0) y.toNat K.toNat)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat)
    (e1 : pv (vpool m1) T.toNat k.toNat + pv (vpool m0) y.toNat K.toNat + c0.toNat =
      pv (vpool m0) x.toNat k.toNat + c1.toNat * wt k.toNat)
    (e2 : pv (vpool m2) (T + k).toNat (l - k).toNat + c1.toNat =
      pv (vpool m1) (x + k).toNat (l - k).toNat + v.toNat * wt (l - k).toNat) :
    pv P X.toNat R.toNat = pv (vpool m0) x.toNat l.toNat - pv (vpool m0) y.toNat K.toNat := by
  subst hc0
  subst hR
  rw [← hK] at e1
  have e := sub_words m0 m1 m2 T x y k l c1 v hT41 hk41 hk hx h1 h2 e1 e2
  have hv : v.toNat = 1 := by
    have : v.toNat ≠ 0 := fun h => hv0 (UInt64.toNat_inj.mp (by simpa using h))
    omega
  have hlt := pv_lt_wt (vpool m2) T.toNat l.toNat
  rw [hv, Nat.one_mul] at e
  rw [← hK]
  simp only [UInt64.toNat_zero, pv]
  omega

/-- `b` longer than `a` even trimmed: `a < b`, the result `0` is `a - b`. -/
theorem sub_core_short (m0 : Mem) (P : Array Word) (X x y k l K R : Word) (hR : R = 0)
    (hn : Norm (vpool m0) y.toNat k.toNat) (hl : l.toNat < k.toNat)
    (hK : pv (vpool m0) y.toNat k.toNat = pv (vpool m0) y.toNat K.toNat) :
    pv P X.toNat R.toNat = pv (vpool m0) x.toNat l.toNat - pv (vpool m0) y.toNat K.toNat := by
  subst hR
  have := pv_len_lt (vpool m0) (vpool m0) x.toNat y.toNat l.toNat k.toNat hn hl
  rw [← hK]
  simp only [UInt64.toNat_zero, pv]
  omega

/-- The pool below `T` is kept: `sub_n` and `sub_1` wrote only at `T` and above. -/
theorem sub_core_agree (m0 m1 m2 : Mem) (T k l : Word)
    (hT41 : T.toNat < 2 ^ 41) (hk41 : k.toNat < 2 ^ 41)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat) :
    Agree (vpool m2) (vpool m0) T.toNat := by
  have hTk : (T + k).toNat = T.toNat + k.toNat := w_add T k (by omega)
  rw [hTk] at h2
  intro j hj
  exact (h2 j (Or.inl (by omega))).trans (h1 j (Or.inl hj))

/-- The room check `len - i ≥ n` of a tier array: `i + r ≤ len` for `r ≤ k ≤ n`. -/
theorem room_le' (m : Mem) (a : TieredArray) (i n r k : Word) (hin : i.toNat ≤ (m.arr64 a).size)
    (hsz : (m.arr64 a).size < 2 ^ 40) (h : ¬decide (m.len64 a - i < n) = true)
    (hr : r.toNat ≤ k.toNat) (hk : k.toNat ≤ n.toNat) : i.toNat + r.toNat ≤ (m.arr64 a).size := by
  have hs : (m.len64 a).toNat = (m.arr64 a).size := by
    simp only [Mem.len64]; exact Nat.mod_eq_of_lt (by omega)
  have h' : n.toNat ≤ (m.len64 a - i).toNat := by
    simpa [UInt64.le_iff_toNat_le] using h
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hs] at h'
  omega

section subCore
variable (p : Prog) (hps : p.lookup "sub_n" = some subN) (hp1 : p.lookup "sub_1" = some sub1)
  (hpt : p.lookup "nat_trim" = some natTrim)

/-- `subCore`'s precondition: locals `(oa, la, ob, lb, top, n, c, pt, pb)`, the operands below
the top, `n` `b`'s trimmed length. -/
def SubCorePre (s : St) : Prop :=
  pcap s.mem < 2 ^ 64 ∧ (s.loc 4).toNat < 2 ^ 41 ∧ (s.loc 4).toNat + (s.loc 1).toNat ≤ pcap s.mem ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧ (s.loc 5).toNat ≤ (s.loc 3).toNat ∧
  pv (vpool s.mem) (s.loc 2).toNat (s.loc 5).toNat = pv (vpool s.mem) (s.loc 2).toNat (s.loc 3).toNat ∧
  ((s.loc 1).toNat < (s.loc 5).toNat → Norm (vpool s.mem) (s.loc 2).toNat (s.loc 5).toNat)

def SubCorePost (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.loc 4 = s₀.loc 4 ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = pcap s₀.mem ∧
  Agree (vpool s'.mem) (vpool s₀.mem) (s₀.loc 4).toNat ∧ (s'.loc 5).toNat ≤ (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s'.loc 5).toNat =
    pv (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat - pv (vpool s₀.mem) (s₀.loc 2).toNat (s₀.loc 3).toNat ∧
  Norm (vpool s'.mem) (s₀.loc 4).toNat (s'.loc 5).toNat

include hps hp1 hpt in
theorem subCore_spec (n : Nat) (s₀ : St) (h : SubCorePre s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) subCore ⦃fun r s' => SubCorePost s₀ r s'; ⊤⦄ := by
  simp only [SubCorePre, SubCorePost] at h ⊢
  obtain ⟨hs, hT41, hroom, ha, hb, hn, hK, hN⟩ := h
  unfold subCore
  vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs,
    subN_spec p hps n, sub1_spec p hp1 n, natTrim_spec p hpt n]
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    BinOp.eval, Cmp.eval, reduceIte, Nat.reduceEqDiff])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals first
    | (grind (splits := 10) [arena_grind, lang_grind, Norm]; done)
    | (with_reducible apply sub_core_ok
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       case e1 => with_reducible assumption
       case e2 => with_reducible assumption
       all_goals (first | rfl | (with_reducible assumption) | grind))
    | (with_reducible apply sub_core_bor
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       case e1 => with_reducible assumption
       case e2 => with_reducible assumption
       all_goals (first | rfl | (with_reducible assumption) | grind))
    | (with_reducible apply sub_core_short
       case hK => with_reducible assumption
       all_goals (first | (with_reducible assumption) | grind))
    | (with_reducible apply sub_core_agree
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       all_goals grind)

end subCore

section subFn
variable (p : Prog) (hps : p.lookup "sub_n" = some subN) (hp1 : p.lookup "sub_1" = some sub1)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_sub" = some natSub)

include hps hp1 hpt hpn in
/-- `nat_sub` appends `a - b` (truncated), normalised, at the old top and moves the top past it;
nothing below the old top changes, and no other array but `CTL[0]`. -/
theorem natSub_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_sub" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat - pv (vpool s₀.mem) ob.toNat lb.toNat ∧
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
  simp only [callFn, natSub]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      subCore_spec p hps hp1 hpt n, natTrim_spec p hpt n]
    all_goals (try simp only [LocEq, SubCorePre, SubCorePost] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    all_goals (try and_intros)
    all_goals first
      | (grind (splits := 10) [arena_grind, lang_grind, Mem.top_eq, vpool_ctl, Norm]; done)
      | (with_reducible apply grows_ctl
         case hroom =>
           first
             | grind [Mem.top_eq]
             | (apply room_le'
                case hr => with_reducible assumption
                case h => assumption
                all_goals grind [Mem.top_eq])
         all_goals grind [Mem.top_eq, vpool_ctl])

end subFn

end L.Arena
