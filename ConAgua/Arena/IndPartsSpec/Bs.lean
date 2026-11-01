module

public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.IndPosSpec.CtxFields
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndParts

@[expose] public section

/-!
# Bs

`decSR`, `decSC`, `partsDecRules_mono`, `decSR_mono`, `decSC_mono`, `partsRec3_eq` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Decoders of the split's records -/

/-- `blockSplitRecs`'s element `[cv, mI, rP, rules.off, rules.len]`. -/
def decSR (m : Mem) (p : Nat) : Option (IConstantVal × Nat × Nat × List IRecRule) := do
  pure (← decCVp m (← iwN m p), ← iwN m (p + 1), ← iwN m (p + 2),
    ← decRules (erA m) (← iwN m (p + 3)) (← iwN m (p + 4)))

/-- `blockSplitCtors`'s element `[cv, nP, nF]`. -/
def decSC (m : Mem) (p : Nat) : Option (IConstantVal × Nat × Nat) := do
  pure (← decCVp m (← iwN m p), ← iwN m (p + 1), ← iwN m (p + 2))

theorem partsDecRules_mono (o l : Nat) : OMono (fun m => decRules (erA m) o l) :=
  ⟨fun _ _ _ he h => he.2.decRules h⟩

theorem decSR_mono (p : Nat) : OMono (fun m => decSR m p) := by
  unfold decSR
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.decCVp
    | apply partsDecRules_mono
    | apply OMono.bind
    | intro _)

theorem decSC_mono (p : Nat) : OMono (fun m => decSC m p) := by
  unfold decSC
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.decCVp
    | apply OMono.bind
    | intro _)

/-! ## `rec3` as `posRecW` -/

theorem partsRec3_eq (m : Mem) (a b c : Word) :
    (match allocW m 3 with | none => none | some (q, _) => some (q, rec3Mem m a b c)) =
      posRecW m [a, b, c] := by
  rw [posRecW_eq m [a, b, c] 3 rfl, rec3Mem_eq]; cases allocW m 3 <;> rfl

theorem partsRec3_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (h3 : p.lookup "rec3" = some rec3) (n : Nat) (s₀ : St) (a b c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec3" [a, b, c]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← partsRec3_eq, invoke_eq _ h3]
  simp only [callFn, rec3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec3Mem, allocMem, allocW]

/-! ## The word models and their `vcgen` specs (generated) -/

/-- After `sl_cons` in `block_split_recs`: the result triple. `block_merge_group`'s model
(`BmgW.lean`) ends with the same step. -/
def bsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m3) => some ([1, r2.headD 0, r2.tail.headD 0], m3)

theorem bsK3_some (m2 : Mem) (r2 : List Word) :
    bsK3 (some (r2, m2)) = some ([1, r2.headD 0, r2.tail.headD 0], m2) := rfl
attribute [ind_grind] bsK3_some

/-- **`block_split_recs` is its model** `bsrW`. -/
l_model bsr_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hs : p.lookup "sl_cons" = some slCons)
  (h5 : p.lookup "rec5" = some rec5)
  (hp : p.lookup "block_split_recs" = some blockSplitRecs)
  fns [hp ↦ bsrW list]
  specs [posRec5_specW p ha h5 n, slCons_specW p ha hc hs n]
  grind [arena_grind, ind_grind] finish [rdW_eq] gen 20

/-- **`block_split_ctors` is its model** `bscW`. -/
l_model bsc_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hs : p.lookup "sl_cons" = some slCons)
  (h5 : p.lookup "rec5" = some rec5) (h3 : p.lookup "rec3" = some rec3)
  (hr : p.lookup "block_split_recs" = some blockSplitRecs)
  (hp : p.lookup "block_split_ctors" = some blockSplitCtors)
  fns [hp ↦ bscW list]
  specs [partsRec3_specW p ha h3 n, slCons_specW p ha hc hs n, bsr_spec p ha hc hs h5 hr n]
  grind [arena_grind, ind_grind] finish [rdW_eq] gen 20

/-- **`block_split` is its model** `bsW`. -/
l_model bs_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hs : p.lookup "sl_cons" = some slCons)
  (h5 : p.lookup "rec5" = some rec5) (h3 : p.lookup "rec3" = some rec3)
  (h6 : p.lookup "rec6" = some rec6)
  (hr : p.lookup "block_split_recs" = some blockSplitRecs)
  (hct : p.lookup "block_split_ctors" = some blockSplitCtors)
  (hp : p.lookup "block_split" = some blockSplit)
  fns [hp ↦ bsW list]
  specs [rec6_specW p ha h6 n, slCons_specW p ha hc hs n, bsc_spec p ha hc hs h5 h3 hr hct n]
  grind [arena_grind, ind_grind] finish [rdW_eq] gen 20

end L.Ind

end
