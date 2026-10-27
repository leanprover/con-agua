import ConAgua.Arena.IndDecStab
import ConAgua.Arena.RecClassSpec.Classes

/-!
# InstallCvDecB

`installCvDecB`, `CstProg`, `TeleOut`, `MemOK`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Constant records below the tops -/

/-- A constant decoded in a memory whose record lies below the tops (`CVExt`) is decoded below
the tops. -/
theorem installCvDecB {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv)
    (hx : CVExt m q) : DecB (fun m => decCVp m q) m cv := by
  obtain ⟨hq, hsl⟩ := hx
  have e : ∀ i, i < erTop m → (erA (truncM m))[i]? = (erA m)[i]? := fun i hi => truncM_er_eq hi
  show decCVp (truncM m) q = some cv
  simp only [decCVp] at h ⊢
  simp only [decCV, bind, Option.bind, pure, hlist?] at h ⊢
  have e0 : (hd? (erA (truncM m)) q : Option NIdx) = hd? (erA m) q := by simp only [hd?, e q (by omega)]
  have e1 : nat? (erA (truncM m)) (q + 1) = nat? (erA m) (q + 1) := by simp only [nat?, e (q + 1) (by omega)]
  have e2 : nat? (erA (truncM m)) (q + 1 + 1) = nat? (erA m) (q + 1 + 1) := by
    simp only [nat?, e (q + 1 + 1) (by omega)]
  have e3 : (hd? (erA (truncM m)) (q + 3) : Option EIdx) = hd? (erA m) (q + 3) := by
    simp only [hd?, e (q + 3) (by omega)]
  rw [e0, e1, e2, e3]
  cases h1 : nat? (erA m) (q + 1) with
  | none => rw [h1] at h; revert h; cases (hd? (erA m) q : Option NIdx) <;> simp
  | some lo =>
  cases h2 : nat? (erA m) (q + 1 + 1) with
  | none => rw [h1, h2] at h; revert h; cases (hd? (erA m) q : Option NIdx) <;> simp
  | some ll =>
  have hN := hsl lo ll h1 (by simpa using h2)
  have hs : (hslice? (erA (truncM m)) lo ll : Option (List NIdx)) = hslice? (erA m) lo ll := by
    simp only [hslice?]
    exact mapM_congr_of _ _ _ (fun j hj => by
      have := List.mem_range.mp hj
      simp only [hd?, e (lo + j) (by omega)])
  rw [h1, h2] at h
  simp only [hs]
  exact h

/-! ## The lookups of `check_sum_tele` -/

/-- The lookups `check_sum_tele`'s refinement takes. -/
structure CstProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  view : p.lookup "e_view" = some eView
  fvarFind : p.lookup "fvar_find" = some fvarFind
  fvarPush : p.lookup "fvar_push" = some fvarPush
  internFVar : p.lookup "intern_fvar" = some internFVar
  wt : p.lookup "whnf_telescope" = some whnfTelescopeL
  sortFind : p.lookup "sort_find" = some sortFind
  sortPush : p.lookup "sort_push" = some sortPush
  internSort : p.lookup "intern_sort" = some internSort
  derB : p.lookup "der_b" = some derB
  forallFind : p.lookup "forall_find" = some forallFind
  forallPush : p.lookup "forall_push" = some forallPush
  internForall : p.lookup "intern_forall" = some internForallL
  mkForall : p.lookup "mk_forall" = some mkForall
  closeTele : p.lookup "close_telescope" = some closeTelescope
  erAlloc : p.lookup "erec_alloc" = some erecAlloc
  cvNew : p.lookup "cv_new" = some cvNew
  slow : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL
  tele : p.lookup "check_sum_tele" = some checkSumTeleL
  strip : StripProg p
  i1 : I1Prog p
  ab : AbF p

/-- The post of `check_block_tele`: the checked former below the tops, its result sort a handle. -/
def TeleOut (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (x : IConstantVal × LIdx) (m' : Mem) (a' : AState) : Prop :=
  StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some x.1 ∧
    CVExt m' (r.headD 0).toNat ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2

/-- What a member record must satisfy: decoded below the tops, its former's constant record
below the tops (`CVExt`). -/
def MemOK (m : Mem) (q : Nat) (ms : MemberShape) : Prop :=
  DecB (fun m => decMS m q) m ms ∧ ∀ c, iwN m q = some c → CVExt m c

end L.Ind

end
