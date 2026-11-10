module

public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Arena.IndInstallSpec.LeafKeep
import ConAgua.Arena.TwinStep
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarStore
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.ImaxStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LevelEquiv
import all ConAgua.Arena.LevelHeap
import all ConAgua.Arena.LevelIntern
import all ConAgua.Arena.LevelStore
import all ConAgua.Arena.LevelSubstLP
import all ConAgua.Arena.LevelZero
import all ConAgua.Arena.LsStore
import all ConAgua.Arena.MaxStore
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.SortStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.WhnfSpineArgs
import all ConAgua.Arena.WhnfSpineRefine
import all ConAgua.Arena.ZeroStore
import ConAgua.Arena.InstLPKeys
import ConAgua.L.VcFlat

@[expose] public section

/-!
# `inst_lp_core` keeps the walk memos, at any memory (lane `ronsync2`, stage 3)

The stream index's builder (`decl_constants`, `decl_tables`) reaches `inst_lp_core` (under
`cv_at_lps`, `ci_at_lps`, `rules_at_lps_go`), whose walk writes the three `instLP` memos (arrays
52‥54, `CTL[54‥59]`). The builder's write-set facts take it as a leaf, so they need its keep fact
at **any** memory, not under the core's `CoreS`: `CoreMemos` and `WkOK` survive every returning
call (`instLPCore_keepCM`, `instLPCore_keepWk`).

The proof does not follow the walk's memo contents. A weaker fact, `LpBnd` (the control words are
there, the live stamp is not `0`, no slot's stamp nor the header's first word is above it), holds
of a well-formed memo, survives every `put` at any arguments (`put` writes only the live stamp)
and every writer of other words, and after the `clear`s at the core's exit gives the empty map
(`memoRV_fresh`). The walk's call closure without the three `put`s (`lpgFns`) stores into none of
52‥54, `CTL[54‥59]` (`lpg_closed`, decided on `ilpfP`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The stamp bound -/

/-- **No stamp above the live one**: the control words are there, the live stamp is not `0`, the
header's first word and every slot's stamp are at most the live stamp. -/
def LpBnd (S : MemoSch) (m : Mem) : Prop :=
  S.cs.toNat + 2 ≤ (m.arr64 CTL).size ∧ epG S m ≠ 0 ∧
    (rdW (m.arr64 S.arr) 0).toNat ≤ (epG S m).toNat ∧
    ∀ j : Word, j.toNat < slotsG S m → (mstG S m j).toNat ≤ (epG S m).toNat

section bnd
variable {S : MemoSch} (hS : S.WF)
include hS

theorem epG_setArr (m : Mem) (i v : Word) : epG S (m.set64 S.arr i v) = epG S m := by
  simp only [epG, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (TieredArray.t0_ne hS.arr_ctl))]

/-- A write to the memo's array keeps the bound when a stamp word gets at most the live stamp. -/
theorem LpBnd.setArr {m : Mem} {i v : Word} (h : LpBnd S m)
    (hv : ∀ j : Word, i = j * 4 → v.toNat ≤ (epG S m).toNat) : LpBnd S (m.set64 S.arr i v) := by
  have hc : (m.set64 S.arr i v).arr64 CTL = m.arr64 CTL :=
    Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (TieredArray.t0_ne hS.arr_ctl))
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [hc]; exact h1, by rw [epG_setArr hS]; exact h2, ?_, fun j hj => ?_⟩
  · rw [epG_setArr hS, rdW_set64]
    split
    · rename_i hh; exact hv 0 (by rw [hh.2.1]; rfl)
    · exact h3
  · rw [slotsG_set64] at hj
    simp only [mstG]
    rw [epG_setArr hS, rdW_set64]
    split
    · rename_i hh; exact hv j hh.2.1
    · exact h4 j hj

/-- A write to a control word other than the stamp keeps the bound. -/
theorem LpBnd.setCtl {m : Mem} {x v : Word} (h : LpBnd S m) (hx : x ≠ S.cs) :
    LpBnd S (m.set64 CTL x v) := by
  have ha : (m.set64 CTL x v).arr64 S.arr = m.arr64 S.arr :=
    Mem.arr64_set64_ne _ _ _ _ _ (TieredArray.t0_ne hS.arr_ctl)
  have he : epG S (m.set64 CTL x v) = epG S m := by
    simp only [epG, rdW_set64]; simp [hx]
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [L.Mem.size64_set64]; exact h1, by rw [he]; exact h2, by rw [he, ha]; exact h3,
    fun j hj => ?_⟩
  rw [slotsG_set64] at hj
  simp only [mstG, ha, he]; exact h4 j hj

end bnd

/-- **A writer of other words keeps the bound.** -/
theorem LpBnd.frame {S : MemoSch} (hS : S.WF) {A : List TieredArray} {C : List Word} {m m' : Mem}
    (hf : MemFrame A C m m') (ha : (S.arr : TieredArray) ∉ A) (hc : S.cs ∉ C) (h : LpBnd S m) :
    LpBnd S m' := by
  have hA : m'.arr64 S.arr = m.arr64 S.arr := hf.arr _ ha (TieredArray.t0_ne hS.arr_ctl)
  have he : epG S m' = epG S m := by simp only [epG, hf.ctl _ hc]
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [hf.size]; exact h1, by rw [he]; exact h2, by rw [he, hA]; exact h3, fun j hj => ?_⟩
  rw [slotsG_frame S hf] at hj
  simp only [mstG, hA, he]; exact h4 j hj

theorem w4_ne1 (s j : Word) : s * 4 + 1 ≠ j * 4 := by
  intro h; have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, UInt64.toNat_mul] at this; simp at this; omega
theorem w4_ne2 (s j : Word) : s * 4 + 2 ≠ j * 4 := by
  intro h; have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, UInt64.toNat_mul] at this; simp at this; omega
theorem w4_ne3 (s j : Word) : s * 4 + 3 ≠ j * 4 := by
  intro h; have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, UInt64.toNat_mul] at this; simp at this; omega
theorem w4_ne1' (j : Word) : (1 : Word) ≠ j * 4 := by simpa using w4_ne1 0 j
theorem w4_ne2' (j : Word) : (2 : Word) ≠ j * 4 := by simpa using w4_ne2 0 j

theorem w_succ2 (t : Word) (h1 : t + 1 ≠ 0) (h2 : t + 1 + 1 ≠ 0) :
    (t + 1).toNat = t.toNat + 1 ∧ (t + 1 + 1).toNat = t.toNat + 2 := by
  have ht := t.toNat_lt
  have n1 : (t + 1).toNat ≠ 0 := fun h => h1 (UInt64.toNat_inj.mp (h.trans (by simp)))
  have n2 : (t + 1 + 1).toNat ≠ 0 := fun h => h2 (UInt64.toNat_inj.mp (h.trans (by simp)))
  simp only [UInt64.toNat_add] at n1 n2 ⊢; simp at n1 n2 ⊢; omega

section bnd2
variable {S : MemoSch} (hS : S.WF)
include hS

/-- A slot write at the live stamp keeps the bound. -/
theorem LpBnd.put4 {m : Mem} {s e x y w : Word} (h : LpBnd S m) (he : e = epG S m) :
    LpBnd S (mput4 S m s e x y w) := by
  unfold mput4
  have e1 := epG_setArr hS m (s * 4) e
  have e2 := epG_setArr hS (m.set64 S.arr (s * 4) e) (s * 4 + 1) x
  have e3 := epG_setArr hS ((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) x) (s * 4 + 2) y
  refine LpBnd.setArr hS (LpBnd.setArr hS (LpBnd.setArr hS (LpBnd.setArr hS h ?_) ?_) ?_) ?_
  · intro j _; rw [he]; exact Nat.le_refl _
  · intro j hj; exact absurd hj (w4_ne1 s j)
  · intro j hj; exact absurd hj (w4_ne2 s j)
  · intro j hj; exact absurd hj (w4_ne3 s j)

theorem epG_put4 (m : Mem) (s e x y w : Word) : epG S (mput4 S m s e x y w) = epG S m := by
  unfold mput4; simp only [epG_setArr hS]

/-- **The growth's rehash keeps the bound** (it writes slots at the live stamp only). -/
theorem LpBnd.rehash (e nb nn : Word) :
    ∀ (k : Nat) (i c : Word) (m m' : Mem) (c' : Word), nb.toNat - i.toNat = k →
      mrehashG S e nb nn i c m = some (m', c') → e = epG S m → LpBnd S m →
      LpBnd S m' ∧ epG S m' = epG S m := by
  intro k
  induction k with
  | zero =>
    intro i c m m' c' hk h _ hb
    rw [mrehashG] at h
    have hi : ¬ i < nb := fun h' => by have : i.toNat < nb.toNat := h'; omega
    simp only [hi, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨hb, rfl⟩
  | succ k ih =>
    intro i c m m' c' hk h he hb
    rw [mrehashG] at h
    by_cases hi : i < nb
    · have hi' : i.toNat < nb.toNat := hi
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := nb.toNat_lt; omega
      simp only [hi, ↓reduceIte] at h
      split at h
      · split at h
        · have := ih _ _ _ _ _ (by omega) h (by rw [epG_put4 hS]; exact he) (hb.put4 hS he)
          rw [epG_put4 hS] at this; exact this
        · simp at h
      · exact ih _ _ _ _ _ (by omega) h he hb
    · have : ¬ i.toNat < nb.toNat := fun h' => hi (UInt64.lt_iff_toNat_lt.mpr h')
      omega

theorem LpBnd.grow {e b n : Word} {m m₁ : Mem} {c : Word} (h : mgrowAt S e b n m = some (m₁, c))
    (he : e = epG S m) (hb : LpBnd S m) : LpBnd S m₁ ∧ epG S m₁ = epG S m := by
  have hcs : S.cs + 1 ≠ S.cs := by
    intro h'; have := congrArg UInt64.toNat h'; have := hS.cs
    simp only [UInt64.toNat_add] at *; simp at *; try omega
  simp only [mgrowAt] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i m' c' hr
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]
  obtain ⟨hb', he'⟩ := LpBnd.rehash hS e _ _ _ _ _ _ _ _ rfl hr he hb
  have f1 := epG_setArr hS m' 0 e
  have f2 := epG_setArr hS (m'.set64 S.arr 0 e) 1 (b + n)
  have f3 := epG_setArr hS ((m'.set64 S.arr 0 e).set64 S.arr 1 (b + n)) 2 (n * 2)
  have hctl : ∀ (m : Mem) v, epG S (m.set64 CTL (S.cs + 1) v) = epG S m := fun m v => by
    simp only [epG, rdW_set64]; simp [hcs]
  refine ⟨LpBnd.setCtl hS (LpBnd.setArr hS (LpBnd.setArr hS (LpBnd.setArr hS hb' ?_) ?_) ?_) hcs, ?_⟩
  · intro j _; rw [he', he]; exact Nat.le_refl _
  · intro j hj; exact absurd hj (w4_ne1' j)
  · intro j hj; exact absurd hj (w4_ne2' j)
  · rw [hctl, f3, f2, f1, he']

theorem LpBnd.putE {m : Mem} {fd j k1 k2 v e c : Word} (hb : LpBnd S m) (he : e = epG S m) :
    LpBnd S (mputMemE S m fd j k1 k2 v e c) := by
  have hcs : S.cs + 1 ≠ S.cs := by
    intro h'; have := congrArg UInt64.toNat h'; have := hS.cs
    simp only [UInt64.toNat_add] at *; simp at *; try omega
  unfold mputMemE
  split
  · refine LpBnd.setArr hS (LpBnd.setCtl hS (LpBnd.setArr hS (LpBnd.setArr hS
      (LpBnd.setArr hS hb ?_) ?_) ?_) hcs) ?_
    · intro i _; rw [he]; exact Nat.le_refl _
    · intro i hi; exact absurd hi (w4_ne1 j i)
    · intro i hi; exact absurd hi (w4_ne2 j i)
    · intro i hi; exact absurd hi (w4_ne3 j i)
  · exact LpBnd.setArr hS hb (fun i hi => absurd hi (w4_ne3 j i))

/-- **A `put` keeps the bound**, at any arguments. -/
theorem LpBnd.mput {m m' : Mem} {k1 k2 v fd j : Word} (h : mputG S m k1 k2 v fd j = some m')
    (hb : LpBnd S m) : LpBnd S m' := by
  simp only [mputG] at h
  split at h
  · split at h
    · simp at h
    · rename_i m₁ c hg
      split at h
      · simp only [Option.some.injEq] at h; subst h
        obtain ⟨hb1, he1⟩ := LpBnd.grow hS hg rfl hb
        exact LpBnd.putE hS hb1 he1.symm
      · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact LpBnd.putE hS hb rfl

/-- After a `clear`: the stamp and the epoch through the two control writes. -/
theorem mclearG_ctl (m : Mem) (hsz : S.cs.toNat + 2 ≤ (m.arr64 CTL).size) :
    rdW ((mclearG S m).arr64 CTL) S.cs = rdW (m.arr64 CTL) S.cs + 1 ∧
      (mclearG S m).arr64 S.arr = m.arr64 S.arr ∧ ((mclearG S m).arr64 CTL).size = (m.arr64 CTL).size := by
  have hcs : S.cs + 1 ≠ S.cs := by
    intro h'; have := congrArg UInt64.toNat h'; have := hS.cs
    simp only [UInt64.toNat_add] at *; simp at *; try omega
  have hf := mclearG_frame S m
  refine ⟨?_, hf.arr _ (by simp) (TieredArray.t0_ne hS.arr_ctl), hf.size _⟩
  unfold mclearG
  rw [rdW_set64, rdW_set64]
  simp [hcs, show S.cs.toNat < (m.arr64 CTL).size by omega]

/-- **A `clear` keeps the bound** (the live stamp goes up by one). -/
theorem LpBnd.clear {m : Mem} (hb : LpBnd S m) (hw : rdW (m.arr64 CTL) S.cs + 2 ≠ 0) :
    LpBnd S (mclearG S m) := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  obtain ⟨c1, c2, c3⟩ := mclearG_ctl hS m h1
  have hw' : rdW (m.arr64 CTL) S.cs + 1 + 1 ≠ 0 := by
    rwa [UInt64.add_assoc]
  obtain ⟨n1, n2⟩ := w_succ2 _ h2 hw'
  have he : epG S (mclearG S m) = rdW (m.arr64 CTL) S.cs + 1 + 1 := by simp only [epG, c1]
  have hsl : slotsG S (mclearG S m) = slotsG S m := slotsG_frame S (mclearG_frame S m)
  have he0 : (epG S m).toNat = (rdW (m.arr64 CTL) S.cs).toNat + 1 := n1
  refine ⟨by rw [c3]; exact h1, by rw [he]; exact hw', ?_, fun j hj => ?_⟩
  · rw [he, c2, n2]; omega
  · rw [hsl] at hj
    have := h4 j hj
    simp only [mstG, c2] at this ⊢
    rw [he, n2]; omega

/-- **After a `clear`, a bounded memo is the empty map.** -/
theorem LpBnd.rv_clear {κ ν : Type} [BEq κ] [Hashable κ] (K : MemoKey κ) (VR : Mem → Word → ν → Prop)
    {m : Mem} (hb : LpBnd S m) (hw : rdW (m.arr64 CTL) S.cs + 2 ≠ 0) :
    MemoRV S K VR (mclearG S m) ∅ := by
  obtain ⟨h1, h2, h3, h4⟩ := hb
  obtain ⟨c1, c2, c3⟩ := mclearG_ctl hS m h1
  have hw' : rdW (m.arr64 CTL) S.cs + 1 + 1 ≠ 0 := by
    rwa [UInt64.add_assoc]
  obtain ⟨n1, n2⟩ := w_succ2 _ h2 hw'
  have he : epG S (mclearG S m) = rdW (m.arr64 CTL) S.cs + 1 + 1 := by simp only [epG, c1]
  have hsl : slotsG S (mclearG S m) = slotsG S m := slotsG_frame S (mclearG_frame S m)
  have he0 : (epG S m).toNat = (rdW (m.arr64 CTL) S.cs).toNat + 1 := n1
  refine memoRV_fresh S K VR _ (by rw [c3]; exact h1) (by rw [he]; exact hw') ?_ (fun j hj => ?_)
  · rw [he, c2, n2]; omega
  · rw [hsl] at hj
    have := h4 j hj
    simp only [mstG, c2] at this ⊢
    rw [he, n2]; omega

omit hS in
/-- A well-formed memo is bounded. -/
theorem LpBnd.of_rv {κ ν : Type} [BEq κ] [Hashable κ] {K : MemoKey κ} {VR : Mem → Word → ν → Prop}
    {m : Mem} {mp : Std.HashMap κ ν} (h : MemoRV S K VR m mp) : LpBnd S m := by
  obtain ⟨h1, h2, ⟨-, h4, -, h6⟩, -⟩ := h
  exact ⟨h1, h2, h6, h4⟩

end bnd2


/-! ## The leaves' specs at any arguments -/

theorem memoPutG_specV (S : MemoSch) (p : Prog) (f : FnName) (hp : p.lookup f = some (memoPutG S))
    (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f vs
    ⦃fun _ s' => LocEq s' s₀ ∧ mputG S s₀.mem (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) (vs.getD 3 0)
      (vs.getD 4 0) = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoPutG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        mgrowBlkG_step_spec S p n] <;>
      finish [mputG, mputMem, mputMemE, nG, mbG, hdG, epG, cntG, dfltN_alt, Locals.init]

/-- `inst_lp_core`'s model at any argument list. -/
theorem instLPCore_specV (p : Prog) (hp : ILWProg p) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_lp_core" vs ⦃fun r s' =>
        LocEq s' s₀ ∧ ilwCoreW p n s₀.mem (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) (vs.getD 3 0) =
          some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.core]
  simp only [callFn, instLPCore]
  cases n with
  | zero => vcgen [exec] <;> grind [ilwCoreW]
  | succ n =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "keys_ok", callW_spec p n "ilp_clear", callW_spec p n "ilpl_clear",
        callW_spec p n "ilpls_clear", callW_spec p n "der_b", lsNode_spec p hp.lsn n,
        callW_spec p n "lp_go"] <;> vc_flat <;>
      first
      | grind (hom := false) (abstractProof := false) (ematch := 28) (gen := 28)
          [lang_grind, arena_grind, Locals.init, -List.cons.injEq]
      | grind (ematch := 28) (gen := 28) [lang_grind, arena_grind, Locals.init]

/-! ## The walk's write set without its `put`s -/

/-- `lp_go`'s call closure in `ilpfP` without the three memo `put`s. -/
def lpgFns : List FnName :=
  ["lp_go", "lp_proj", "ilp_find", "mk_proj", "intern_proj", "proj_push", "proj_find", "der_b",
   "lp_let", "lp_let_tail", "lp_rb_let", "mk_let", "intern_letE", "letE_push", "letE_find",
   "lp_forall", "mk_forall", "intern_forall", "forall_push", "forall_find", "lp_lam", "mk_lam",
   "intern_lam", "lam_push", "lam_find", "lp_app", "mk_app", "intern_app", "app_push", "app_find",
   "lp_fvar", "intern_fvar", "fvar_push", "fvar_find", "intern_const", "const_push", "const_find",
   "sls_memo", "ilpls_find", "spn_ls", "intern_ls", "ls_push", "ls_find", "ls_match", "limbs_eq",
   "lit_hash", "spn_pool", "sls_go", "lv_sub_int", "lv_intern", "intern_imax", "imax_push",
   "imax_find", "intern_max", "max_push", "max_find", "intern_succ", "succ_push", "succ_find",
   "intern_param", "param_push", "param_find", "intern_zero", "zero_push", "zero_find", "lv_node",
   "lp_substl", "lh_mk", "lp_lookup", "ls_node", "intern_sort", "sort_push", "sort_find", "sl_memo",
   "ilpl_find"]

/-- The walk's leaves: the three memo `put`s. -/
def lpgLeaves : List FnName := ["ilp_put", "ilpl_put", "ilpls_put"]

/-- What the rest writes: `inst_lp_fast`'s write set but the three memos. -/
def lpgA : List TieredArray :=
  ilpfA.filter fun b => !(b == (LPMEMO : TieredArray) || b == (LPLMEMO : TieredArray) ||
    b == (LPLSMEMO : TieredArray))

/-- The `CTL` words the rest writes: `inst_lp_fast`'s but the memos' stamps and counts. -/
def lpgC : List Word := ilpfC.filter fun x => !(54 ≤ x && x ≤ 59)

theorem lpg_closed : closedAL ilpfP lpgA lpgC lpgFns lpgLeaves = true := by decide +kernel

/-- The three bounds. -/
def LpBnd3 (m : Mem) : Prop := LpBnd lpSch m ∧ LpBnd lplSch m ∧ LpBnd lplsSch m

theorem LpBnd3.frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (LPMEMO : TieredArray) ∉ A ∧ (LPLMEMO : TieredArray) ∉ A ∧ (LPLSMEMO : TieredArray) ∉ A)
    (hC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C) (h : LpBnd3 m) : LpBnd3 m' :=
  ⟨h.1.frame lpSch_wf hf hA.1 hC.1, h.2.1.frame lplSch_wf hf hA.2.1 hC.2.1,
    h.2.2.frame lplsSch_wf hf hA.2.2 hC.2.2⟩

/-- A `put` of one of the three keeps all three bounds. -/
theorem LpBnd3.put {S : MemoSch} (hS3 : S = lpSch ∨ S = lplSch ∨ S = lplsSch) {m m' : Mem}
    {k1 k2 v fd j : Word} (h : mputG S m k1 k2 v fd j = some m') (hb : LpBnd3 m) : LpBnd3 m' := by
  rcases hS3 with rfl | rfl | rfl
  · have hf := mputG_frame lpSch lpSch_wf _ _ _ _ _ _ _ h
    exact ⟨hb.1.mput lpSch_wf h, hb.2.1.frame lplSch_wf hf (by decide) (by decide),
      hb.2.2.frame lplsSch_wf hf (by decide) (by decide)⟩
  · have hf := mputG_frame lplSch lplSch_wf _ _ _ _ _ _ _ h
    exact ⟨hb.1.frame lpSch_wf hf (by decide) (by decide), hb.2.1.mput lplSch_wf h,
      hb.2.2.frame lplsSch_wf hf (by decide) (by decide)⟩
  · have hf := mputG_frame lplsSch lplsSch_wf _ _ _ _ _ _ _ h
    exact ⟨hb.1.frame lpSch_wf hf (by decide) (by decide),
      hb.2.1.frame lplSch_wf hf (by decide) (by decide), hb.2.2.mput lplsSch_wf h⟩

theorem lpgLeaf_keep {S : MemoSch} (hS3 : S = lpSch ∨ S = lplSch ∨ S = lplsSch) {g : FnName}
    (hg : ilpfP.lookup g = some (memoPutG S)) :
    ∀ n vs m r m', callW ilpfP n g vs m = some (r, m') → LpBnd3 m → LpBnd3 m' := by
  intro n vs m r m' hc hb
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoPutG_specV S ilpfP g hg n _ vs) hc
  rw [hs'] at hW
  exact LpBnd3.put hS3 hW hb

/-- **`lp_go` keeps the three bounds**, at any memory and arguments. -/
theorem lpGo_keep {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW ilpfP n "lp_go" vs m = some (r, m')) (hb : LpBnd3 m) : LpBnd3 m' := by
  refine callW_keepL lpg_closed (fun m m' hf hb => hb.frame hf (by decide) (by decide)) ?_
    (by decide) h hb
  intro g hg
  simp only [lpgLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact lpgLeaf_keep (Or.inl rfl) rfl
  · exact lpgLeaf_keep (Or.inr (Or.inl rfl)) rfl
  · exact lpgLeaf_keep (Or.inr (Or.inr rfl)) rfl

/-! ## `inst_lp_core` -/

theorem LpBnd3.clear {S : MemoSch} (hS3 : S = lpSch ∨ S = lplSch ∨ S = lplsSch) {m : Mem}
    (hb : LpBnd3 m) (hw : rdW (m.arr64 CTL) S.cs + 2 ≠ 0) : LpBnd3 (mclearG S m) := by
  have hf := mclearG_frame S m
  rcases hS3 with rfl | rfl | rfl
  · exact ⟨hb.1.clear lpSch_wf hw, hb.2.1.frame lplSch_wf hf (by decide) (by decide),
      hb.2.2.frame lplsSch_wf hf (by decide) (by decide)⟩
  · exact ⟨hb.1.frame lpSch_wf hf (by decide) (by decide), hb.2.1.clear lplSch_wf hw,
      hb.2.2.frame lplsSch_wf hf (by decide) (by decide)⟩
  · exact ⟨hb.1.frame lpSch_wf hf (by decide) (by decide),
      hb.2.1.frame lplSch_wf hf (by decide) (by decide), hb.2.2.clear lplsSch_wf hw⟩

theorem LpBnd3.of_lp {m : Mem} (h : LPMemos m) : LpBnd3 m :=
  ⟨let ⟨_, hm⟩ := h.lp; LpBnd.of_rv hm, let ⟨_, hm⟩ := h.lpl; LpBnd.of_rv hm,
    let ⟨_, hm⟩ := h.lpls; LpBnd.of_rv hm⟩

theorem vh_any (m m' : Mem) (w : Word) (v : EIdx) (h : VH m w v) : VH m' w v := h
theorem vi_any {k : IdxKind} (m m' : Mem) (w : Word) (v : Idx k) (h : VI m w v) : VI m' w v := h

/-- **The three exit clears of bounded memos give well-formed (empty) memos.** -/
theorem LpBnd3.clears {m : Mem} (hb : LpBnd3 m)
    (h1 : rdW (m.arr64 CTL) lpSch.cs + 2 ≠ 0)
    (h2 : rdW ((mclearG lpSch m).arr64 CTL) lplSch.cs + 2 ≠ 0)
    (h3 : rdW ((mclearG lplSch (mclearG lpSch m)).arr64 CTL) lplsSch.cs + 2 ≠ 0) :
    LPMemos (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) := by
  have b1 := LpBnd3.clear (S := lpSch) (Or.inl rfl) hb h1
  have b2 := LpBnd3.clear (S := lplSch) (Or.inr (Or.inl rfl)) b1 h2
  have f2 := mclearG_frame lplSch (mclearG lpSch m)
  have f3 := mclearG_frame lplsSch (mclearG lplSch (mclearG lpSch m))
  have r1 : MemoRV coreLpSch lfKey VH (mclearG lpSch m) ∅ := hb.1.rv_clear lpSch_wf lfKey VH h1
  have r2 : MemoRV coreLplSch ilKey VI (mclearG lplSch (mclearG lpSch m)) (∅ : Std.HashMap LIdx LIdx) :=
    b1.2.1.rv_clear lplSch_wf ilKey VI h2
  have r3 : MemoRV coreLplsSch ilKey VI (mclearG lplsSch (mclearG lplSch (mclearG lpSch m)))
      (∅ : Std.HashMap LsIdx LsIdx) := b2.2.2.rv_clear lplsSch_wf ilKey VI h3
  have r1a : MemoRV coreLpSch lfKey VH (mclearG lplSch (mclearG lpSch m)) ∅ :=
    memoRV_frame coreLpSch coreLpSch_wf lfKey VH [] _ (by simp) (by decide) (mclearG lpSch m)
      (mclearG lplSch (mclearG lpSch m)) f2 (vh_any _ _) _ r1
  have r1' : MemoRV coreLpSch lfKey VH (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) ∅ :=
    memoRV_frame coreLpSch coreLpSch_wf lfKey VH [] _ (by simp) (by decide)
      (mclearG lplSch (mclearG lpSch m)) (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) f3
      (vh_any _ _) _ r1a
  have r2' : MemoRV coreLplSch ilKey VI (mclearG lplsSch (mclearG lplSch (mclearG lpSch m)))
      (∅ : Std.HashMap LIdx LIdx) :=
    memoRV_frame coreLplSch coreLplSch_wf ilKey VI [] _ (by simp) (by decide)
      (mclearG lplSch (mclearG lpSch m)) (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) f3
      (vi_any _ _) _ r2
  exact ⟨⟨∅, r1'⟩, ⟨∅, r2'⟩, ⟨∅, r3⟩⟩

/-- **`inst_lp_core` keeps the `instLP` memos well formed**, at any memory and arguments (in
`ilpfP`). -/
theorem instLPCore_lp {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW ilpfP n "inst_lp_core" vs m = some (r, m')) (hL : LPMemos m) : LPMemos m' := by
  have hp := ilpfP_entry
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (instLPCore_specV ilpfP hp.all.lev.ilw n _ vs) h
  rw [hs'] at hW
  rcases n with _ | k
  · simp [ilwCoreW] at hW
  rw [ilwCoreW.eq_2] at hW
  cases h1 : callW ilpfP k "der_b" [vs.getD 3 0] m with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨d, m₁⟩ := q
  rw [h1] at hW
  obtain ⟨s1, hs1, -, hm1, -⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (derB_spec ilpfP hp.all.mkp.spine.derb k _ _) h1
  have hm₁ : m₁ = m := hs1.symm.trans hm1
  subst hm₁
  simp only [ilwCoreW.k_der_b] at hW
  split at hW
  · simp only [Option.some.injEq, Prod.mk.injEq] at hW; rw [← hW.2]; exact hL
  split at hW
  · cases hW
  cases h2 : callW ilpfP k "keys_ok" [vs.getD 0 0, vs.getD 1 0] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨r2, m₂⟩ := q
  rw [h2, ilwCoreW.k_keys_ok.arm1] at hW
  obtain ⟨s2, hs2, -, hm2, -⟩ :=
    triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩) (keysOk_spec ilpfP hp.keys k _ _ _) h2
  have hm₂ : m₂ = m₁ := hs2.symm.trans hm2
  subst hm₂
  cases h3 : callW ilpfP k "ilp_clear" [] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q =>
  obtain ⟨r3, m₃⟩ := q
  rw [h3, ilwCoreW.k_ilp_clear.arm1] at hW
  obtain ⟨hw3, rfl⟩ := ilw_clearCall lpSch hp.all.lev.ilw.ilpc h3
  cases h4 : callW ilpfP k "ilpl_clear" [] (mclearG lpSch m₂) with
  | none => rw [h4] at hW; cases hW
  | some q =>
  obtain ⟨r4, m₄⟩ := q
  rw [h4, ilwCoreW.k_ilpl_clear.arm1] at hW
  obtain ⟨hw4, rfl⟩ := ilw_clearCall lplSch hp.all.lev.ilw.ilplc h4
  cases h5 : callW ilpfP k "ilpls_clear" [] (mclearG lplSch (mclearG lpSch m₂)) with
  | none => rw [h5] at hW; cases hW
  | some q =>
  obtain ⟨r5, m₅⟩ := q
  rw [h5, ilwCoreW.k_ilpls_clear.arm1] at hW
  obtain ⟨hw5, rfl⟩ := ilw_clearCall lplsSch hp.all.lev.ilw.ilplsc h5
  have hB := LpBnd3.clear (S := lplsSch) (Or.inr (Or.inr rfl))
    (LpBnd3.clear (S := lplSch) (Or.inr (Or.inl rfl))
      (LpBnd3.clear (S := lpSch) (Or.inl rfl) (LpBnd3.of_lp hL) hw3) hw4) hw5
  cases h6 : callW ilpfP k "lp_go" [vs.getD 3 0, vs.getD 0 0, vs.getD 1 0, _, _, 4000000000]
      (mclearG lplsSch (mclearG lplSch (mclearG lpSch m₂))) with
  | none => rw [h6] at hW; cases hW
  | some q =>
  obtain ⟨r6, m₆⟩ := q
  rw [h6, ilwCoreW.k_lp_go.arm1] at hW
  have hB6 := lpGo_keep h6 hB
  cases h7 : callW ilpfP k "ilp_clear" [] m₆ with
  | none => rw [h7] at hW; cases hW
  | some q =>
  obtain ⟨r7, m₇⟩ := q
  rw [h7, ilwCoreW.k_ilp_clear_2.arm1] at hW
  obtain ⟨hw7, rfl⟩ := ilw_clearCall lpSch hp.all.lev.ilw.ilpc h7
  cases h8 : callW ilpfP k "ilpl_clear" [] (mclearG lpSch m₆) with
  | none => rw [h8] at hW; cases hW
  | some q =>
  obtain ⟨r8, m₈⟩ := q
  rw [h8, ilwCoreW.k_ilpl_clear_2.arm1] at hW
  obtain ⟨hw8, rfl⟩ := ilw_clearCall lplSch hp.all.lev.ilw.ilplc h8
  cases h9 : callW ilpfP k "ilpls_clear" [] (mclearG lplSch (mclearG lpSch m₆)) with
  | none => rw [h9] at hW; cases hW
  | some q =>
  obtain ⟨r9, m₉⟩ := q
  rw [h9, ilwCoreW.k_ilpls_clear_2.arm1] at hW
  obtain ⟨hw9, rfl⟩ := ilw_clearCall lplsSch hp.all.lev.ilw.ilplsc h9
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  rw [← hW.2]
  exact hB6.clears hw7 hw8 hw9


/-! ## The leaf facts, in any program that has `ilpfP` -/

section leaf
variable {p : Prog} (hp : IlpfF p)
include hp

theorem instLPCore_toIlpf {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n "inst_lp_core" vs m = some (r, m')) :
    callW ilpfP n "inst_lp_core" vs m = some (r, m') := by
  rw [← callW_agree ilpfP_closed (hp.agree ilpfFns) n (by decide) vs m]; exact h

/-- `inst_lp_core` writes only `ilpfA`, `ilpfC`. -/
theorem instLPCore_frame {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n "inst_lp_core" vs m = some (r, m')) : MemFrame ilpfA ilpfC m m' :=
  (run_memFrame ilpfP_closed (by decide) (run_of_callW (instLPCore_toIlpf hp h))).1

/-- **`inst_lp_core` keeps the walk memos**, at any memory and arguments. -/
theorem instLPCore_keepW {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n "inst_lp_core" vs m = some (r, m')) (hM : WalkMemos m) : WalkMemos m' := by
  have hf := instLPCore_frame hp h
  exact ⟨let ⟨mp, hm⟩ := hM.ws; ⟨mp, memoRG_frame coreWsSch coreWsSch_wf lfKey _ ilpfA ilpfC
      (by decide) (by decide) m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := hM.fl; ⟨mp, memoRG_frame coreFlSch coreFlSch_wf bmKey _ ilpfA ilpfC
      (by decide) (by decide) m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := hM.lsb; ⟨mp, memoRG_frame coreLsbSch coreLsbSch_wf bmKey _ ilpfA ilpfC
      (by decide) (by decide) m m' hf mp hm⟩,
    instLPCore_lp (instLPCore_toIlpf hp h) hM.lp⟩

/-- **`inst_lp_core` keeps `CoreMemos`**, at any memory and arguments. -/
theorem instLPCore_keepCM {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n "inst_lp_core" vs m = some (r, m')) (hM : CoreMemos m) : CoreMemos m' := by
  have hf := instLPCore_frame hp h
  exact ⟨let ⟨mp, hm⟩ := hM.il; ⟨mp, memoRG_frame coreIlSch coreIlSch_wf lfKey decE ilpfA ilpfC
      (by decide) (by decide) m m' hf mp hm⟩,
    let ⟨mp, hm⟩ := hM.ab; ⟨mp, memoRG_frame coreAbSch coreAbSch_wf lfKey decE ilpfA ilpfC
      (by decide) (by decide) m m' hf mp hm⟩,
    instLPCore_keepW hp h hM.walk, hM.hbF hf⟩

/-- **`inst_lp_core` keeps `WkOK`**, at any memory and arguments. -/
theorem instLPCore_keepWk {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n "inst_lp_core" vs m = some (r, m')) (hM : WkOK m) : WkOK m' := by
  have hf := instLPCore_frame hp h
  obtain ⟨hw, h1, h2, h3, h4⟩ := hM
  exact ⟨instLPCore_keepW hp h hw, by rw [hf.size]; exact h1, by rw [hf.size]; exact h2,
    by rw [hf.size]; exact h3, by rw [pinW_frame hf (by decide)]; exact h4⟩

end leaf

end L.Ind
