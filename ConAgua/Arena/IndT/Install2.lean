import ConAgua.Arena.IndT.Install1
import ConRon.Bridge.Inductives.BlockInstall
import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.IndInstallSpec.IagW
import ConAgua.Arena.IndInstallSpec.InstallSimCall
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndPartsSpec.PartsPSlCons

/-!
# `lvl_eq_fueled` under `StageC` (lane `indstaget`)

`lveC_okC`: `lvl_eq_fueled`'s model at `realCall p`, an answer other than `0` the twin's
`lvlEq?` verdict. `check_block_agree(_one)`'s refinements are `cbao_ref`/`cbag_ref`
(`Verdict/IndsE4`, `IndsE5`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`lvl_eq_fueled`, its `lvl_eq_c` the real call, under `StageC`** (`lveW_ok`'s statement with
`lvlEqC_simC` for the stub contract): an answer other than `0` is the twin's verdict. -/
theorem lveC_okC {p : Prog} (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {n : Nat}
    {m m' : Mem} {a : AState} {u v : Word} {r : List Word}
    (h : lveC (realCall p) n m u v = some (r, m')) (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hu : H u) (hv : H v) {lu lv : ConLeche.Level} (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    ∃ b a', (lvlEq? (decI u) (decI v)).run a = .ok (some b, a') ∧ StageC dn vis fe env m' a' ∧
      IWGrow m m' ∧ AbsOK m' ∧ PStep a a' ∧ r.headD 0 = (if b then 1 else 0) := by
  rcases n with _ | n
  · simp [lveC] at h
  simp only [lveC] at h
  rcases hs : realCall p n "lvl_eq_c" [u, v] m with _ | ⟨r1, m1⟩
  · simp [hs] at h
  simp only [hs] at h
  by_cases h0 : r1.headD 0 = 0
  · rw [ite_eq_left h0] at h; exact absurd h (by simp)
  rw [ite_eq_right h0] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a1, hrun, hC1, hg, hdec, hA1, hp⟩ :=
    lvlEqC_simC p hcl hLC n hC hA u v hu hv lu lv hdu hdv r1 m1 hs
  simp only [decLvlEq] at hdec
  cases x with
  | none => exact absurd hdec h0
  | some b =>
    refine ⟨b, a1, hrun, hC1, hg, hA1, hp, ?_⟩
    cases b <;> simp at hdec ⊢ <;> simp [hdec]

end L.Ind
