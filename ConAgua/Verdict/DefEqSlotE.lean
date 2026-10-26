import ConAgua.Verdict.DefEqBaseE

/-!
# The knot's `defeq` slot: its error claim one level up (lane `verdicts-b`, helper `k3`)

`defeq(mode, vis, d, a, b)` (`Knot.lean`) probes the memo (`de_find`), runs `defeq_body` on a miss
and records the verdict (`de_put`). The memo's two calls are outside the verdict closure, so a
failure of class `1`/`2` is `defeq_body`'s, at a memo miss: the twin's slot runs `defeqBody` there
(`knot_defeq_missE`). `defeqSlotE_of`: `DefeqSlotE p (n + 1)` from `defeq_body`'s error spec
(`DefeqBodySpecE`, the error half of `DefeqBodySpec`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model defeqSlot_specE (p : Prog) (hf : p.lookup "defeq" = some defeqSlotL)
  fns [hf ↦ defeqSlotE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] errors

/-- **`defeq_body`'s error spec** (the error half of `DefeqBodySpec`): under the same hypotheses
and the error knot up to `n`. -/
def DefeqBodySpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW x → HW y → KnotUpTo p n → KnotUpToE p n →
    CoreSpecE p n "defeq_body" [mode, vis, d, x, y]
      (defeqBody (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE x) (decE y)) s₀ a₀

/-- At a memo miss the twin's slot fails where its body does. -/
theorem knot_defeq_missE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (x y : EIdx)
    (a : AState) (hm : a.caches.defeqC[(x, y)]? = none) {e : Err}
    (h : ErrClaim (defeqBody mode (coreKnot mode fe id F) fe d x y) a e) :
    ErrClaim ((coreKnot mode fe id (F + 1)).defeq d x y) a e := by
  refine ErrClaim.of_run_eq (fun ce hce => ?_) h
  simp [coreKnot, hm, StateT.run_bind, hce]
  rfl

/-- The memo's calls are outside the verdict closure. -/
theorem defeqSlotE_nv : ∀ f ∈ ["de_find", "de_put"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- **The knot's `defeq` slot's error claim one level up**, from `defeq_body`'s. -/
theorem defeqSlotE_of (p : Prog) (hp : KnotProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (hb : DefeqBodySpecE p n) :
    DefeqSlotE p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d x y hF hn2 hs hx hy
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (defeqSlot_specE p hp.defeq (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d x y) hc (Err.code_ne_of_cls hk0)
  simp only [defeqSlotE] at hW
  have hS := hs.rel
  have hkey : y ||| (mode >>> 1 &&& 1) <<< 32 = genW y eb := by rw [hs.eb_mode]; rfl
  rw [hkey] at hW
  cases h1 : callE p n "de_find" [x, genW y eb] s₀.mem with
  | error e1 =>
    rw [h1, defeqSlotE.k_de_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (defeqSlotE_nv "de_find" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  obtain ⟨t₁, ht₁, rfl, hne, rfl⟩ := triple_of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (memoFindG_spec deSch p _ hp.deFind n ⟨s₀.mem, Locals.init []⟩ x (genW y eb)) h1
  simp only at ht₁
  subst ht₁
  rw [h1] at hW
  have hf := hS.core.de.findD hS.core.eb1 x y hx hy hne
  by_cases h2 : (mfindG deSch s₀.mem x (genW y eb)).headD 0 ≠ 0
  · rw [defeqSlotE.k_de_find.arm1 _ _ _ _ _ _ _ _ _ _ h2] at hW; cases hW
  have h2' : (mfindG deSch s₀.mem x (genW y eb)).headD 0 = 0 := by simpa using h2
  rw [defeqSlotE.k_de_find.arm2 _ _ _ _ _ _ _ _ _ _ h2'] at hW
  have hmiss := hf.2 h2'
  cases h3 : callE p n "defeq_body" [mode, vis, d, x, y] s₀.mem with
  | error e3 =>
    rw [h3, defeqSlotE.k_defeq_body.none] at hW; cases hW
    exact knot_defeq_missE _ fe F' d.toNat _ _ a₀ hmiss
      (CoreSpecE.of_callE (hb F' s₀ a₀ dn vis fe MM eb mode d x y (by omega) (by omega) hs hx hy hk
        hkE) h3)
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW
  simp only [defeqSlotE.k_defeq_body] at hW
  cases h4 : callE p n "de_find" [x, genW y eb] m₃ with
  | error e4 =>
    rw [h4, defeqSlotE.k_de_find_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (defeqSlotE_nv "de_find" (by simp)) h4
  | ok q =>
  rw [h4] at hW
  simp only [defeqSlotE.k_de_find_2] at hW
  cases h5 : callE p n "de_put" _ _ with
  | error e5 =>
    rw [h5, defeqSlotE.k_de_put.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (defeqSlotE_nv "de_put" (by simp)) h5
  | ok q => rw [h5] at hW; simp only [defeqSlotE.k_de_put] at hW; cases hW

end L.Arena
