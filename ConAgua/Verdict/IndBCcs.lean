import ConAgua.Arena.IndT.RecGen27
/-!
# `classes_ctors`' error claim

The `CoreSpecE` shape of `ccs_ref`'s error half, for `gen_rec_check_prep`'s claim.
-/

open ConRon.Arena
open ConRon.Bridge.Inductives (dShape dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`classes_ctors`' error claim** (every fuel; `classesCtors_refinesC`'s hypotheses), from
`ccs_ref`. -/
theorem classesCtors_claim {p : Prog} (hkp : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (P : CcsProg p) (hIlpf : IlpfF p) (hOpf : OpfF p)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    {vis : Word} (hcE : CoreStubsE p) (q fto ftl rd mo ml : Word)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {MsP : List ConLeche.TargetMajor}
    {rdP : ConLeche.ClassRead}
    (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (bs : BlockShape)
    (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem) (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp s₀.mem mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem)
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hrdP : ConRon.Bridge.Inductives.dClassRead a₀.store R = some rdP)
    (hmsP : ms.mapM (dMajor a₀.store) = some MsP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, ConLeche.Cached.TargetMajScoped M) :
    CoreSpecE p N "classes_ctors" [vis, q, fto, ftl, rd, mo, ml]
      (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) s₀ a₀ := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    exact RefE.coreSpecE (ccsE_spec p P (n + 1) s₀ vis q fto ftl rd mo ml) hnv ⟨hnv, hcE⟩
      (ccs_ref hkp henv P hIlpf hOpf dn fe n hN hC hA hbs hft hftb hR hms hmsb hlp hnpk hsz5 hP hsh hftP
        hrdP hmsP hformer hMs)

end L.Ind
