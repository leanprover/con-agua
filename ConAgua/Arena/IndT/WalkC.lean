import ConAgua.Arena.IndT.Base
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.IndRealMemoCrT

/-!
# `AbsOK` across the real `all_level_params_defined` and `consts_resolve_ffast` (lane `indstaget`)

For the `StageC` proofs that call the two walks' models (`apdF`, `crfF`) under `StageT`
(`apdF_okT`, `crfF_okT`): the walk memos `AbsOK` holds survive the call. `apdF` writes the core's
`wscopedBFast` memo (array 151), which `TwinOK` holds after (`StageT` after the call); `crfF`
writes its own memo (array 155), which `crfF_okT` gives back (`CrMemo` after); the rest is framed.
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`AbsOK` across `all_level_params_defined`**, `StageT` after it. -/
theorem absOK_apdF {m m' : Mem} {args r : List Word} {a' : AState} (h : apdF m args = some (r, m'))
    (hA : AbsOK m) (hT : StageT dn vis fe m' a') : AbsOK m' :=
  have hf := apdF_frame h
  ⟨hT.twin.memos.2.1, hA.2.1.frame hf (by decide) (by decide),
    hA.2.2.1.frame hf (by decide) (by decide), hT.twin.memos.1,
    hT.twin.memos.2.2, hT.twin.erec, hT.twin.spn, hT.twin.bstk, hT.flag⟩

/-- **`AbsOK` across `consts_resolve_ffast`**, `StageT` and its memo after it. -/
theorem absOK_crfF {m m' : Mem} {args r : List Word} {a' : AState} (h : crfF m args = some (r, m'))
    (hA : AbsOK m) (hCr : CrMemo m') (hT : StageT dn vis fe m' a') : AbsOK m' :=
  have hf := crfF_frame h
  ⟨hT.twin.memos.2.1, hA.2.1.frame hf (by decide) (by decide), hCr, hT.twin.memos.1,
    hT.twin.memos.2.2, hT.twin.erec, hT.twin.spn, hT.twin.bstk, hT.flag⟩

end L.Ind
