import ConAgua.Arena.IndTwin

/-!
# `AbsOK` from the twin's invariants (lane `indproofs4`, helpers `abs`, `memo`)

The core's walk memos (`CoreMemos`, `WhnfBase.lean`) contain the `abstract1` memo at `coreAbSch`
(= `abSch`: array 49, `CTL[48]`) and the `instantiateList` memo at `coreIlSch` (array 50,
`CTL[50]`), so a `StageT` stage carries those two parts of `AbsOK` (`IndStubs.lean`); the other two
(`I1Memo`, array 51; `CrMemo`, array 155) are not in `CoreMemos` and come from the caller (lane
`loopt3`'s `LoopT` memo clause carries `CrOK`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem _root_.L.Arena.TwinOK.absOK {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    (h : TwinOK dn m a fe) (hi : I1Memo m) (hc : CrMemo m) (hp : pinW m 0 ≠ 0) : AbsOK m :=
  ⟨h.memos.2.1, hi, hc, h.memos.1, h.memos.2.2, h.erec, h.spn, h.bstk, hp⟩

theorem StageT.absOK {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (h : StageT dn vis fe m a) (hi : I1Memo m) (hc : CrMemo m) : AbsOK m :=
  h.twin.absOK hi hc h.flag

end L.Ind
