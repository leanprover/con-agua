import ConAgua.Arena.InferBodyBindPi

/-!
# Error claims of the binder telescopes

The error halves of the unified refinements of `infer_lam` and `infer_forall` (`ilm_ref`,
`ifr_ref`; the telescopes `infer_lams`, `infer_pis` and their leaves are `ils_ref`, `ips_ref`,
`ilf_ref`, `ipl_ref`), as the error claims (`CoreSpecE`) their non-migrated reader `InferKnotE` takes.
-/

open ConRon.Arena

namespace L.Arena

theorem callE_zero_cls {p : Prog} {f : FnName} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p 0 f vs m = .error e) : e.cls = 0 := by
  obtain ⟨e', he', h0⟩ := callE_zero p f vs m
  rw [h] at he'; cases he'; exact h0

/-- **`infer_lam`'s verdicts** (`ilm_ref`'s error half). -/
theorem inferLam_refinesE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hnv : closedNV p L.Checker.nvFns = true)
    (hcap : BStkCap) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpecE p (n + 1) "infer_lam" [mode, vis, d, ty, body]
      (inferLam (coreKnot (decMode mode) fe id F) d.toNat (decE ty) (decE body)) s₀ a₀ :=
  RefE.coreSpecE (ilmE_spec p hq.lam (n + 1) s₀ mode vis d ty body) hnv ⟨hkE, hnv⟩
    (ilm_ref p hp hq hb hil hab hcap n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty body hs hty hbody)

/-- **`infer_forall`'s verdicts** (`ifr_ref`'s error half). -/
theorem inferForall_refinesE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpecE p (n + 1) "infer_forall" [mode, vis, d, ty, body]
      (inferForall (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE body)) s₀ a₀ :=
  RefE.coreSpecE (ifrE_spec p hq.fa (n + 1) s₀ mode vis d ty body) hnv ⟨hkE, hnv⟩
    (ifr_ref p hp hq hb hil hcap n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty body hs hty hbody)

end L.Arena
