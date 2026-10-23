import ConAgua.Arena.IndTwin
import ConAgua.Arena.IndRealAbs

/-!
# `AbsOK` from the twin's invariants (lane `indproofs4`, helper `abs`)

The core's walk memos (`CoreMemos`, `WhnfBase.lean`) contain the `abstract1` memo at `coreAbSch`
(= `abSch`: array 49, `CTL[48]`), so a `StageT` stage carries `AbsOK` (`IndStubs.lean`): the link
the later `StageT` migration of the `abstract1_fast` users needs (`abF_ok` takes `AbsOK`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem _root_.L.Arena.TwinOK.absOK {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    (h : TwinOK dn m a fe) : AbsOK m :=
  h.memos.2.1

theorem StageT.absOK {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (h : StageT dn vis fe m a) : AbsOK m :=
  h.twin.absOK

end L.Ind
