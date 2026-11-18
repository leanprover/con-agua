module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatAdd
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.NatSub
import ConAgua.L.Records
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve

@[expose] public section

/-!
# Bitwise `Nat` ops on the limb pool: `land`, `lor`, `xor`

`nat_land`/`nat_lor`/`nat_xor` (con-ron's `land`/`lor`/`xor` and their `*_from` loops,
`ron/nat.rs:658-703`): the leaf `and_n`/`or_n`/`xor_n` combines the limbs both operands have,
`copy_n` copies the rest of the longer one (`lor`, `xor`), then `nat_trim`. `land`'s result has
`min la lb` limbs, `lor`/`xor` have `max la lb`. Inputs need not be normalised; the output is.

The model `bv` is `xv` with a combining function instead of a single read (the zero-extended
combine); the leaves' `bwv` is the plain one, and `bv_bw`, `bv_tail_a`, `bv_tail_b` relate them.
Whether packing a limb-wise combine into the pool matches `Nat.land`/`Nat.lor`/`Nat.xor` on the
full value is `NatOpRefine.lean`'s job (deferred, as `Norm`/pv bounds are for comparison).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Limb `i` of the slice `(o, l)` as a WORD, `0` past its end (`lv`, but not converted to
`Nat`: `bv` needs to feed it to a word operator `f`). -/
def lvW (p : Array Word) (o l i : Nat) : Word := if i < l then p[o + i]?.getD 0 else 0

theorem lvW_toNat (p : Array Word) (o l i : Nat) : (lvW p o l i).toNat = lv p o l i := by
  simp only [lvW, lv]; split <;> rfl
grind_pattern [arena_grind] lvW_toNat => lvW p o l i, lv p o l i

/-- The value of combining the zero-extended slices `(oa, la)`/`(ob, lb)` limb by limb with `f`,
for the first `k` limbs (`xv` with a second slice and a combinator instead of one read). -/
def bv (f : Word → Word → Word) (p : Array Word) (oa la ob lb : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => bv f p oa la ob lb k + (f (lvW p oa la k) (lvW p ob lb k)).toNat * wt k

theorem bv_succ (f : Word → Word → Word) (p : Array Word) (oa la ob lb k k' : Nat)
    (hk : k' = k + 1) :
    bv f p oa la ob lb k' = bv f p oa la ob lb k + (f (lvW p oa la k) (lvW p ob lb k)).toNat * wt k := by
  subst hk; rfl
grind_pattern [arena_grind] bv_succ => bv f p oa la ob lb k', bv f p oa la ob lb k

@[arena_grind =] theorem bv_zero (f : Word → Word → Word) (p : Array Word) (oa la ob lb : Nat) :
    bv f p oa la ob lb 0 = 0 := rfl

/-- The three word combinators, as NAMED constants (not `(· &&& ·)`-style sections): a lambda
and its point-free `HAnd.hAnd`/… form are eta-equal but not syntactically equal, and `finish`'s
pattern matching saw both forms appear (one from the invariant as written, one from `BinOp.eval`
unfolding the code's own `&`/`|`/`^`) and failed to connect them. One rigid name avoids it. -/
def andF : Word → Word → Word := fun a b => a &&& b
def orF : Word → Word → Word := fun a b => a ||| b
def xorF : Word → Word → Word := fun a b => a ^^^ b

@[arena_grind =] theorem andF_eq (a b : Word) : andF a b = a &&& b := rfl
@[arena_grind =] theorem orF_eq (a b : Word) : orF a b = a ||| b := rfl
@[arena_grind =] theorem xorF_eq (a b : Word) : xorF a b = a ^^^ b := rfl

/-- The two passes of `lor`/`xor`: the leaf `g` (`or_n`, `xor_n`) over the limbs both operands
have, `copy_n` over the rest of the longer one. Locals `(oa, la, ob, lb, top, n, c, pt, pb)`. -/
def bitCore (g : FnName) : Stmt :=
  .ite (.cmp .ult (.var 1) (.var 3))
    (.seq (.call [6] g [.var 4, .var 0, .var 2, .var 1])
      (.call [6] "copy_n" [.bin .add (.var 4) (.var 1), .bin .add (.var 2) (.var 1),
        .bin .sub (.var 3) (.var 1)]))
    (.seq (.call [6] g [.var 4, .var 0, .var 2, .var 3])
      (.call [6] "copy_n" [.bin .add (.var 4) (.var 3), .bin .add (.var 0) (.var 3),
        .bin .sub (.var 1) (.var 3)]))

/-- `land`'s pass: `and_n` over the shorter length `n`. Locals `(oa, la, ob, lb, top, n, c, pt, pb)`. -/
def andCore : Stmt := .call [6] "and_n" [.var 4, .var 0, .var 2, .var 5]

/-- `and_n` over the shorter length, `nat_trim`. The pass is a leaf (`NatLeaf.lean`).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natLand : FunDecl := lfn (oa, la, ob, lb) locals (top, n, c, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if lb < la { n := lb };
  if len(POOL⟨pt⟩) - pb < n { abort };
  ⟪andCore⟫;
  n := call nat_trim(top, n);
  CTL.u64[0] := top + n;
  return n
}

/-- `lor`/`xor`: `bitCore g` over the longer length, `nat_trim`.
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose] def natBitG (g : FnName) : FunDecl := lfn (oa, la, ob, lb) locals (top, n, c, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la;
  if la < lb { n := lb };
  if len(POOL⟨pt⟩) - pb < n { abort };
  ⟪bitCore g⟫;
  n := call nat_trim(top, n);
  CTL.u64[0] := top + n;
  return n
}

/-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natLor : FunDecl := natBitG "or_n"

/-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natXor : FunDecl := natBitG "xor_n"

/-- The bitwise `Nat` functions, as one program. -/
def natBitsProg : Prog :=
  natProg ++ [("nat_land", natLand), ("nat_lor", natLor), ("nat_xor", natXor)]

/- `0xF0 land 0x0F = 0` (operands at 0, 1; top at 2, after both). -/
#guard (run natBitsProg 100 "nat_land" [0, 1, 1, 1] (Mem.ofWords [(POOL, #[0xF0, 0x0F, 0, 0]), (CTL, #[2])])).toOption.map (·.1)
  == some [0]
/- `0xF0 lor 0x0F = 0xFF` (same layout). -/
#guard (run natBitsProg 100 "nat_lor" [0, 1, 1, 1] (Mem.ofWords [(POOL, #[0xF0, 0x0F, 0, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL))
  == some ([1], #[0xF0, 0x0F, 0xFF, 0], #[3])
/- `[1, 1] xor [1] = [0, 1]` (top limb survives, bottom cancels; length 2 after trim; operands at
0 (len 2) and 2 (len 1), top at 3). -/
#guard (run natBitsProg 100 "nat_xor" [0, 2, 2, 1] (Mem.ofWords [(POOL, #[1, 1, 1, 0, 0]), (CTL, #[3])])).toOption.map
  (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) == some ([2], #[1, 1, 1, 0, 1], #[5])

/-! ## Composing the passes -/

/-- Within both lengths, the zero-extended combine is the plain one. -/
theorem bv_bw (f : Word → Word → Word) (p : Array Word) (oa la ob lb k : Nat) (ha : k ≤ la)
    (hb : k ≤ lb) : bv f p oa la ob lb k = bwv f p oa ob k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bv, bwv, ih (by omega) (by omega), lvW, show k < la by omega,
      show k < lb by omega, ite_true]

/-- Past `b`'s end, `f x 0 = x` passes `a`'s limbs through. -/
theorem bv_tail_a (f : Word → Word → Word) (hf : ∀ x, f x 0 = x) (p : Array Word)
    (oa la ob lb j : Nat) (hl : lb ≤ la) (hj : lb + j ≤ la) :
    bv f p oa la ob lb (lb + j) = bwv f p oa ob lb + wt lb * pv p (oa + lb) j := by
  induction j with
  | zero => rw [Nat.add_zero, bv_bw f p oa la ob lb lb hl (Nat.le_refl _)]; simp [pv]
  | succ j ih =>
    have c1 : lb + j < la := by omega
    have c2 : ¬lb + j < lb := by omega
    rw [← Nat.add_assoc, bv, ih (by omega), pv, lvW, lvW]
    simp only [c1, c2, ite_true, ite_false]
    rw [hf, wt_add lb j (lb + j) rfl, Nat.add_assoc oa lb j]
    grind

/-- Past `a`'s end, `f 0 y = y` passes `b`'s limbs through. -/
theorem bv_tail_b (f : Word → Word → Word) (hf : ∀ y, f 0 y = y) (p : Array Word)
    (oa la ob lb j : Nat) (hl : la ≤ lb) (hj : la + j ≤ lb) :
    bv f p oa la ob lb (la + j) = bwv f p oa ob la + wt la * pv p (ob + la) j := by
  induction j with
  | zero => rw [Nat.add_zero, bv_bw f p oa la ob lb la (Nat.le_refl _) hl]; simp [pv]
  | succ j ih =>
    have c1 : ¬la + j < la := by omega
    have c2 : la + j < lb := by omega
    rw [← Nat.add_assoc, bv, ih (by omega), pv, lvW, lvW]
    simp only [c1, c2, ite_true, ite_false]
    rw [hf, wt_add la j (la + j) rfl, Nat.add_assoc ob la j]
    grind

/-- The value `bitCore` leaves: the leaf over `k` limbs (`P1`), `copy_n` over the `l - k` limbs of
the longer operand `z` after them (`P2`). -/
theorem bit_pv (P0 P1 P2 : Array Word) (T z k l B : Nat) (hk : k ≤ l) (hz : z + l ≤ T)
    (h1 : Off P1 P0 T k) (h2 : Off P2 P1 (T + k) (l - k))
    (e1 : pv P1 T k = B) (e2 : pv P2 (T + k) (l - k) = pv P1 (z + k) (l - k)) :
    pv P2 T l = B + wt k * pv P0 (z + k) (l - k) := by
  have a2 := pv_append P2 T k (l - k)
  rw [show k + (l - k) = l by omega] at a2
  have d2 : pv P2 T k = pv P1 T k := Off.pv_disj P2 P1 (T + k) (l - k) T k h2 (Or.inl (by omega))
  have d1 : pv P1 (z + k) (l - k) = pv P0 (z + k) (l - k) :=
    Off.pv_disj P1 P0 T k (z + k) (l - k) h1 (Or.inl (by omega))
  rw [a2, d2, e1, e2, d1]

/-- `bit_pv` with `a` the longer operand, in the shape of `bitCore`'s goal. -/
theorem bit_core_a (op : BinOp) (hf : ∀ x, BinOp.eval op x 0 = x) (m0 m1 m2 : Mem) (T oa la ob lb n : Word) (hn : n = la)
    (hT41 : T.toNat < 2 ^ 41) (hl : lb.toNat ≤ la.toNat) (hz : oa.toNat + la.toNat ≤ T.toNat)
    (h1 : Off (vpool m1) (vpool m0) T.toNat lb.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + lb).toNat (la - lb).toNat)
    (e1 : pv (vpool m1) T.toNat lb.toNat = bwv (BinOp.eval op) (vpool m0) oa.toNat ob.toNat lb.toNat)
    (e2 : pv (vpool m2) (T + lb).toNat (la - lb).toNat = pv (vpool m1) (oa + lb).toNat (la - lb).toNat) :
    pv (vpool m2) T.toNat n.toNat =
      bv (BinOp.eval op) (vpool m0) oa.toNat la.toNat ob.toNat lb.toNat n.toNat := by
  subst n
  have hTk : (T + lb).toNat = T.toNat + lb.toNat := w_add T lb (by omega)
  have hzk : (oa + lb).toNat = oa.toNat + lb.toNat := w_add oa lb (by omega)
  have hlk : (la - lb).toNat = la.toNat - lb.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl)
  rw [hTk, hlk] at h2 e2
  rw [hzk] at e2
  rw [bit_pv _ _ _ T.toNat oa.toNat lb.toNat la.toNat _ hl hz h1 h2 e1 e2]
  have := bv_tail_a _ hf (vpool m0) oa.toNat la.toNat ob.toNat lb.toNat (la.toNat - lb.toNat) hl (by omega)
  rw [show lb.toNat + (la.toNat - lb.toNat) = la.toNat by omega] at this
  rw [this]

/-- `bit_pv` with `b` the longer operand. -/
theorem bit_core_b (op : BinOp) (hf : ∀ y, BinOp.eval op 0 y = y) (m0 m1 m2 : Mem) (T oa la ob lb n : Word) (hn : n = lb)
    (hT41 : T.toNat < 2 ^ 41) (hl : la.toNat ≤ lb.toNat) (hz : ob.toNat + lb.toNat ≤ T.toNat)
    (h1 : Off (vpool m1) (vpool m0) T.toNat la.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + la).toNat (lb - la).toNat)
    (e1 : pv (vpool m1) T.toNat la.toNat = bwv (BinOp.eval op) (vpool m0) oa.toNat ob.toNat la.toNat)
    (e2 : pv (vpool m2) (T + la).toNat (lb - la).toNat = pv (vpool m1) (ob + la).toNat (lb - la).toNat) :
    pv (vpool m2) T.toNat n.toNat =
      bv (BinOp.eval op) (vpool m0) oa.toNat la.toNat ob.toNat lb.toNat n.toNat := by
  subst n
  have hTk : (T + la).toNat = T.toNat + la.toNat := w_add T la (by omega)
  have hzk : (ob + la).toNat = ob.toNat + la.toNat := w_add ob la (by omega)
  have hlk : (lb - la).toNat = lb.toNat - la.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl)
  rw [hTk, hlk] at h2 e2
  rw [hzk] at e2
  rw [bit_pv _ _ _ T.toNat ob.toNat la.toNat lb.toNat _ hl hz h1 h2 e1 e2]
  have := bv_tail_b _ hf (vpool m0) oa.toNat la.toNat ob.toNat lb.toNat (lb.toNat - la.toNat) hl (by omega)
  rw [show la.toNat + (lb.toNat - la.toNat) = lb.toNat by omega] at this
  rw [this]

/-- The pool below `T` is kept by the two passes. -/
theorem bit_core_agree (m0 m1 m2 : Mem) (T k l : Word) (hT41 : T.toNat < 2 ^ 41) (hk41 : k.toNat < 2 ^ 41)
    (h1 : Off (vpool m1) (vpool m0) T.toNat k.toNat)
    (h2 : Off (vpool m2) (vpool m1) (T + k).toNat (l - k).toNat) :
    Agree (vpool m2) (vpool m0) T.toNat := by
  have hTk : (T + k).toNat = T.toNat + k.toNat := w_add T k (by omega)
  rw [hTk] at h2
  intro j hj
  exact (h2 j (Or.inl (by omega))).trans (h1 j (Or.inl hj))

theorem or_x0 (x : Word) : BinOp.eval .or x 0 = x := by simp [BinOp.eval]
theorem or_0y (y : Word) : BinOp.eval .or 0 y = y := by simp [BinOp.eval]
theorem xor_x0 (x : Word) : BinOp.eval .xor x 0 = x := by simp [BinOp.eval]
theorem xor_0y (y : Word) : BinOp.eval .xor 0 y = y := by simp [BinOp.eval]

/-- The room check `len - i ≥ n` of the top's tier: the `n` limbs from the top `T` stay below the
pool's capacity. -/
theorem room_top (m M : Mem) (T X n r : Word) (hX : X = T) (hM : pcap M = pcap m)
    (hs : pcap m < 2 ^ 64) (hT41 : T.toNat < 2 ^ 41)
    (hin : (T &&& 1099511627775).toNat ≤ (m.arr64 (tierA POOL (T >>> 40))).size)
    (h : ¬decide (m.len64 (tierA POOL (T >>> 40)) - (T &&& 1099511627775) < n) = true)
    (hr : r.toNat ≤ n.toNat) : X.toNat + r.toNat ≤ pcap M := by
  subst X
  have hsz := pcap_tier m (T >>> 40) hs
  have h1 := room_le' m _ _ n r r hin (by omega) h (Nat.le_refl _) hr
  have := tag_split T; have := tag_tier_le T hT41
  rw [hM, pcap_eq m hs]; omega

/-- A pool written only in `[o, o + n)` agrees with the old one below `o`. -/
theorem off_agree (P Q : Array Word) (o n : Nat) (h : Off P Q o n) : Agree P Q o :=
  fun j hj => h j (Or.inl hj)

theorem pcap_ctl (m : Mem) (w : Word) : pcap (m.set64 CTL 0 w) = pcap m := by
  simp only [pcap, PSmall, Mem.size64_set64]

/-- `room_le'` up to equal names for the array and the index. -/
theorem room_le_eq (m : Mem) (a a' : TieredArray) (i i' n r k : Word) (ha : a = a') (hi : i = i')
    (hin : i.toNat ≤ (m.arr64 a).size) (hsz : (m.arr64 a).size < 2 ^ 40)
    (h : ¬decide (m.len64 a' - i' < n) = true) (hr : r.toNat ≤ k.toNat) (hk : k.toNat ≤ n.toNat) :
    i.toNat + r.toNat ≤ (m.arr64 a).size := by
  subst ha hi; exact room_le' m a i n r k hin hsz h hr hk

section andCore
variable (p : Prog) (hpn : p.lookup "and_n" = some (bitNG .and))

def AndCorePre (s : St) : Prop :=
  pcap s.mem < 2 ^ 64 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 5).toNat ≤ (s.loc 1).toNat ∧ (s.loc 5).toNat ≤ (s.loc 3).toNat ∧
  (s.loc 4).toNat + (s.loc 5).toNat ≤ pcap s.mem

def AndCorePost (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ PFrame s₀.mem s'.mem ∧
  pcap s'.mem = pcap s₀.mem ∧ Agree (vpool s'.mem) (vpool s₀.mem) (s₀.loc 4).toNat ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat =
    bwv (BinOp.eval .and) (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 2).toNat (s₀.loc 5).toNat

include hpn in
theorem andCore_spec (n : Nat) (s₀ : St) (h : AndCorePre s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) andCore ⦃fun r s' => AndCorePost s₀ r s'; ⊤⦄ := by
  simp only [AndCorePre, AndCorePost] at h ⊢
  obtain ⟨hs, hT41, ha, hb, hn1, hn2, hroom⟩ := h
  unfold andCore
  vcgen [step, evalE, evalArgs, setLoc, setLocs, bitN_spec p .and "and_n" hpn n]
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals grind [arena_grind, lang_grind, off_agree]

end andCore

section bitCore
variable (p : Prog) (op : BinOp) (g : FnName) (hpg : p.lookup g = some (bitNG op))
  (hpc : p.lookup "copy_n" = some copyN)

/-- `bitCore`'s precondition: locals `(oa, la, ob, lb, top, n, c, pt, pb)`. -/
def BitCorePre (s : St) : Prop :=
  pcap s.mem < 2 ^ 64 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 1 < s.loc 3 → s.loc 5 = s.loc 3) ∧ (¬s.loc 1 < s.loc 3 → s.loc 5 = s.loc 1) ∧
  (s.loc 4).toNat + (s.loc 5).toNat ≤ pcap s.mem

def BitCorePost (op : BinOp) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ PFrame s₀.mem s'.mem ∧
  pcap s'.mem = pcap s₀.mem ∧ Agree (vpool s'.mem) (vpool s₀.mem) (s₀.loc 4).toNat ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat =
    bv (BinOp.eval op) (vpool s₀.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat (s₀.loc 2).toNat (s₀.loc 3).toNat
      (s₀.loc 5).toNat

include hpg hpc in
theorem bitCore_spec (hfa : ∀ x, BinOp.eval op x 0 = x) (hfb : ∀ y, BinOp.eval op 0 y = y)
    (n : Nat) (s₀ : St) (h : BitCorePre s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) (bitCore g) ⦃fun r s' => BitCorePost op s₀ r s'; ⊤⦄ := by
  simp only [BitCorePre, BitCorePost] at h ⊢
  obtain ⟨hs, hT41, ha, hb, hn1, hn2, hroom⟩ := h
  unfold bitCore
  vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs,
    bitN_spec p op g hpg n, copyN_spec p hpc n]
  all_goals (try simp only [LocEq] at *)
  all_goals (try simp_all only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    BinOp.eval.eq_1, BinOp.eval.eq_2, Cmp.eval, reduceIte, Nat.reduceEqDiff])
  all_goals split_clear_locs
  all_goals (try and_intros)
  all_goals first
    | (grind (splits := 10) [arena_grind, lang_grind]; done)
    | (with_reducible apply bit_core_a op hfa
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       case e1 => with_reducible assumption
       case e2 => with_reducible assumption
       all_goals grind)
    | (with_reducible apply bit_core_b op hfb
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       case e1 => with_reducible assumption
       case e2 => with_reducible assumption
       all_goals grind)
    | (with_reducible apply bit_core_agree
       case h2 => with_reducible assumption
       case h1 => with_reducible assumption
       all_goals grind)

end bitCore

/-! ## The functions -/

theorem andF_eval : andF = BinOp.eval .and := by funext a b; rfl
theorem orF_eval : orF = BinOp.eval .or := by funext a b; rfl
theorem xorF_eval : xorF = BinOp.eval .xor := by funext a b; rfl

/-- `land`'s value: `and_n` over the shorter length is the zero-extended combine there. -/
theorem land_val (p : Array Word) (oa la ob lb n : Word) (hn : n = if lb < la then lb else la) :
    bwv (BinOp.eval .and) p oa.toNat ob.toNat n.toNat =
      bv (BinOp.eval .and) p oa.toNat la.toNat ob.toNat lb.toNat
        (if lb.toNat < la.toNat then lb.toNat else la.toNat) := by
  subst hn
  have e : (if lb < la then lb else la).toNat = if lb.toNat < la.toNat then lb.toNat else la.toNat := by
    split <;> rename_i h <;> simp only [UInt64.lt_iff_toNat_lt] at h <;> simp [h]
  rw [e, bv_bw]
  · split <;> omega
  · split <;> omega

/-- The longer length as a word and as a number. -/
theorem max_val (la lb n : Word) (hn : n = if la < lb then lb else la) :
    n.toNat = if la.toNat < lb.toNat then lb.toNat else la.toNat := by
  subst hn
  split <;> rename_i h <;> simp only [UInt64.lt_iff_toNat_lt] at h <;> simp [h]

/-- A bitwise function's result: the trimmed length `r` of the `n` limbs written, read after the
top moved. -/
theorem bit_final (m : Mem) (T T' X n n' r R w : Word) (A A' : Nat) (hX : X = T) (hR : R = r)
    (hT : T' = T) (hn' : n' = n)
    (et : pv (vpool m) T'.toNat r.toNat = pv (vpool m) T'.toNat n'.toNat)
    (hc : pv (vpool m) T.toNat n.toNat = A') (hA : A' = A) :
    pv (vpool (m.set64 CTL 0 w)) X.toNat R.toNat = A := by
  subst X R T' n' hA
  rw [vpool_ctl, et, hc]

section bitFn
variable (p : Prog) (hpt : p.lookup "nat_trim" = some natTrim) (hpc : p.lookup "copy_n" = some copyN)

include hpt in
/-- `nat_land` appends the limb-wise AND of `(oa, la)`/`(ob, lb)` (`min la lb` limbs before
`nat_trim`). -/
theorem natLand_spec (hpa : p.lookup "nat_land" = some natLand) (hpn : p.lookup "and_n" = some andN)
    (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_land" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv andF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if lb.toNat < la.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  rw [andF_eval]
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  have hok2 := hok.ctl; have hok3 := hok.cap; have hok4 := hok.top; have hok6 := hok.inTier
  clear hok
  replace ha := ha.1
  replace hb := hb.1
  have hs : pcap s₀.mem < 2 ^ 64 := by omega
  have hpn' : p.lookup "and_n" = some (bitNG .and) := by rw [hpn, andN_eq]
  rw [invoke_eq _ hpa]
  simp only [callFn, natLand]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      andCore_spec p hpn' n, natTrim_spec p hpt n]
    all_goals (try simp only [LocEq, AndCorePre, AndCorePost] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval.eq_1,
      BinOp.eval.eq_2, BinOp.eval.eq_4, BinOp.eval.eq_8, Cmp.eval, reduceIte, Nat.reduceEqDiff,
      UInt64.toNat_zero, Sig.retVal, Sig.retOr] at *)
    all_goals split_clear_locs
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
      | (with_reducible apply bit_final
         case et => with_reducible assumption
         case hc => with_reducible assumption
         all_goals first | rfl | grind [Mem.top_eq, land_val])
      | (with_reducible apply room_top
         case h => assumption
         all_goals (first | (with_reducible assumption) | grind [Mem.top_eq, pcap_ctl]))
      | (with_reducible apply grows_ctl
         case hroom =>
           apply room_le_eq
           case h => assumption
           case hr => with_reducible assumption
           all_goals grind [Mem.top_eq]
         all_goals grind [Mem.top_eq, vpool_ctl])

include hpt hpc in
theorem natBitG_spec (op : BinOp) (g fn : FnName) (hfa : ∀ x, BinOp.eval op x 0 = x)
    (hfb : ∀ y, BinOp.eval op 0 y = y) (hpf : p.lookup fn = some (natBitG g))
    (hpg : p.lookup g = some (bitNG op)) (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) fn [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv (BinOp.eval op) (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if la.toNat < lb.toNat then lb.toNat else la.toNat) ∧
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
  rw [invoke_eq _ hpf]
  simp only [callFn, natBitG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      bitCore_spec p op g hpg hpc hfa hfb n, natTrim_spec p hpt n]
    all_goals (try simp only [LocEq, BitCorePre, BitCorePost] at *)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      L.Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval.eq_1,
      BinOp.eval.eq_2, BinOp.eval.eq_4, BinOp.eval.eq_8, Cmp.eval, reduceIte, Nat.reduceEqDiff,
      UInt64.toNat_zero, Sig.retVal, Sig.retOr] at *)
    all_goals split_clear_locs
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
      | (with_reducible apply bit_final
         case et => with_reducible assumption
         case hc => with_reducible assumption
         all_goals first | rfl | grind [Mem.top_eq, max_val])
      | (with_reducible apply room_top
         case h => assumption
         all_goals (first | (with_reducible assumption) | grind [Mem.top_eq, pcap_ctl]))
      | (with_reducible apply grows_ctl
         case hroom =>
           apply room_le_eq
           case h => assumption
           case hr => with_reducible assumption
           all_goals grind [Mem.top_eq]
         all_goals grind [Mem.top_eq, vpool_ctl])

include hpt hpc in
theorem natLor_spec (hpo : p.lookup "nat_lor" = some natLor) (hpn : p.lookup "or_n" = some orN)
    (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_lor" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv orF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if la.toNat < lb.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  rw [orF_eval]
  exact natBitG_spec p hpt hpc .or "or_n" "nat_lor" or_x0 or_0y (by rw [hpo]; rfl) (by rw [hpn, orN_eq]) n s₀ oa la ob lb hok ha hb

include hpt hpc in
theorem natXor_spec (hpx : p.lookup "nat_xor" = some natXor) (hpn : p.lookup "xor_n" = some xorN)
    (n : Nat) (s₀ : St)
    (oa la ob lb : Word) (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_xor" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        bv xorF (vpool s₀.mem) oa.toNat la.toNat ob.toNat lb.toNat
          (if la.toNat < lb.toNat then lb.toNat else la.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  rw [xorF_eval]
  exact natBitG_spec p hpt hpc .xor "xor_n" "nat_xor" xor_x0 xor_0y (by rw [hpx]; rfl) (by rw [hpn, xorN_eq]) n s₀ oa la ob lb hok ha hb

end bitFn

end L.Arena
