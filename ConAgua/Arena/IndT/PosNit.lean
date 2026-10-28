import ConAgua.Arena.IndT.Install2
import ConAgua.Arena.IndPosSpec.NitLe
import ConAgua.Arena.IndRealAbsPos

/-!
# `nest_inst_type`'s level comparison under `StageC` (lane `indstaget`, helper `rcF`)

`NitLe` (`IndPosSpec/NitLe.lean`) at `realCall p`: `lvl_eq_fueled` with the real `lvl_eq_c`
(`lef_ref`), from `StageC` at `nest_inst_type`'s start and the context's and key's denotations.
The twin's steps before the comparison are con-ron's `nestInstType_spec`'s: `stripPis`
(`stripPis_pstep`), `instLPFast` (`instLPFast_cstep`), `instPisWith` (`instPisWith_spec`),
`piBinders` (`piBinders_spec`) and the result's sort (`denote_sort_inv`); `AbsOK` across the L
calls before it by their frames (`piBW_afr`, `noaW_afr`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dKey)

namespace L.Ind

open L.Arena

/-- **`nest_inst_type`'s `lvl_eq_fueled` under `StageC`**: `NitLe` at the real call, `AbsOK`
after. -/
theorem nitLe_realC {p : Prog} (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    (hlf : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env} (k : Nat)
    (ctx hi key : Word) (c : NestCtx) (kk : NestKey) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) {ctxP : ConLeche.NestCtx}
    (hctx : dCtx a.store env.find? c = some ctxP) {keyP : ConLeche.NestKey}
    (hkey : dKey a.store kk = some keyP) :
    NitLe (realCall p) k dn vis fe ctx hi key c kk (fun m' _ => AbsOK m') m a := by
  intro m1 m2 m3 m4 r1 rs r3 r4 cv caps q a3 a4 a5 tl ty bs e uw _ hA1 hpb hoa hfind hsp hil hipw hpbr
    hview hS3 _ hu hv hvd hle
  have hok := hC.check
  obtain ⟨hcn, hlv, hds⟩ := ConRon.Bridge.Inductives.dKey_inv hkey
  obtain ⟨namesP, lpsP, paramsP, sortP, -, -, -, -, hsort, -⟩ := ConRon.Bridge.Inductives.dCtx_inv hctx
  obtain ⟨ci, hci, -⟩ := ConRon.Bridge.Inductives.find_some_rel hok.ienv hcn hfind
  obtain ⟨cvP, capsP, hcvP, -, -⟩ := ConRon.Bridge.Inductives.denoteCI_indInfo_inv hci
  obtain ⟨-, hlpsC, htyC⟩ := ConRon.Bridge.denoteCV_inv hcvP
  obtain ⟨hs3, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hok.state htyC hsp
  subst hs3
  obtain ⟨c4, htl⟩ := ConRon.Bridge.Inductives.instLPFast_cstep hok hlpsC hlv htyC hil
  obtain ⟨p5, ho2⟩ := ConRon.Bridge.Inductives.instPisWith_spec kk.ds keyP.ds tl _ a4 a5 (some ty)
    c4.ok.state ⟨ConRon.Bridge.denoteEList_ext c4.ext _ _ hds, htl⟩ hipw
  have c5 := c4.trans (p5.toCore c4.ok)
  obtain ⟨tyP, -, hty⟩ := ho2
  obtain ⟨-, -, hpb2⟩ := ConRon.Bridge.Inductives.piBinders_spec _ ty tyP a5 a5 (bs, e) c5.ok.state hty hpbr
  obtain ⟨-, hv5⟩ := ConRon.Bridge.view_run hview
  obtain ⟨sP, -, hsL⟩ := ConRon.Bridge.denote_sort_inv c5.ok.state.wf hv5 hpb2
  have hA3 : AbsOK m3 := noaW_afr _ _ _ _ _ _ _ _ _ _ hoa (piBW_afr _ _ _ _ _ _ hpb (hA1 hA))
  have hC3 : StageC dn vis fe env m3 a5 := hC.of_check hS3 hA3 c5.ok c5.ext
  have hdv : denoteL a5.store.ls (decI (rdW (m3.arr64 IW) (ctx + 9))) = some sortP := by
    rw [hvd]; exact ConRon.Bridge.denoteL_ext hsort c5.ext
  obtain ⟨s4, hs4, -, b, a6, -, ⟨hrun, hr, -, hg4, hf4, hC4'⟩⟩ :=
    RefE.run_okW (lefE_spec p hlf k ⟨m3, Locals.init []⟩ _ _) (lef_ref hcl hLC k hC3.stageT hu hv hsL hdv) hle
  subst hs4
  obtain ⟨hC4, hA4, -⟩ := hC4' env hC3 hA3
  rw [hvd] at hrun
  exact ⟨b, a6, hrun, hC4.stage, hg4, hf4, hr, hA4⟩

end L.Ind
