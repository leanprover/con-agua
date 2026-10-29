import ConAgua.Arena.InferBodySpineF

/-!
# Error claims of the application spines

The error halves of the unified refinements of `infer_app_io` and `infer_app` (`aio_ref`, `a_ref`;
the spines `infer_spine_io`, `infer_spine` are `spio_ref`, `sp_ref`), as the error claims
(`CoreSpecE`) their non-migrated reader `InferKnotE` takes.
-/

open ConRon.Arena

namespace L.Arena

/-- **`infer_app_io`'s verdicts** (`aio_ref`'s error half). -/
theorem inferAppIO_refinesE (p : Prog) (hq : SpineInferProg p) (hsp : SpineProg p)
    (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e)
    (h4 : e >>> 28 = 4) :
    CoreSpecE p (n + 1) "infer_app_io" [mode, vis, d, e]
      (inferAppIOAt (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE e)) s₀ a₀ :=
  RefE.coreSpecE (aioE_spec p hq.appIO (n + 1) s₀ mode vis d e) hnv ⟨hkE, hnv⟩
    (aio_ref p hq hsp hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d e hs he h4)

/-- **`infer_app`'s verdicts** (`a_ref`'s error half). -/
theorem inferApp_refinesE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (hsp : SpineProg p) (he : IsEagerReduceH p) (hda : DefeqArgE p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hHe : HW e)
    (h4 : e >>> 28 = 4) :
    CoreSpecE p (n + 1) "infer_app" [mode, vis, d, e]
      (inferApp (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) s₀ a₀ :=
  RefE.coreSpecE (aE_spec p hq.app (n + 1) s₀ mode vis d e) hnv ⟨⟨hkE, hnv⟩, hda⟩
    (a_ref p hp hkp hq hsp he hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d e hs hHe h4)

end L.Arena
