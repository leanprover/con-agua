import ConAgua.Verdict.PosKnotE
import ConAgua.Verdict.PosE1S
import ConAgua.Verdict.PosE1N
import ConAgua.Verdict.PosE2
import ConAgua.Verdict.PosE3C

/-!
# The positivity walk's error claims at every fuel, assembled (lane `verdicts-b`, helper `ia2`)

`nbOKE_all`: the block's error claims (`NbOKE`) at every L fuel up to `2 ^ 62`, by induction on
the fuel from the steps (`PosE1S`, `PosE2`, `PosE3*`, `IndE.keyOKE_step`) and the ok block
(`nbOKC_all`).
-/

set_option linter.deprecated false

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **The positivity walk's error claims at every L fuel `≤ 2 ^ 62`.** -/
theorem nbOKE_all {p : Prog} (L : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p)
    (hLC : LvlCacheProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)
    (hW : WhnfTopE p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} (henv : ConLeche.EnvWF env) :
    ∀ n, n ≤ 2 ^ 62 → NbOKE p dn vis fe env n
  | 0, _ => nbOKE_zero p dn vis fe env
  | n + 1, hn => by
    have ihE := nbOKE_all (dn := dn) (vis := vis) (fe := fe) L hq hIlpf hLC hnv hcE hW henv n (by omega)
    have ihC := nbOKC_all (dn := dn) (vis := vis) (fe := fe) hq hIlpf hLC henv n (by omega)
    have hNit := nitE_all L hq hIlpf hLC hnv dn vis fe env
    exact ⟨posOKE_step L hq hnv hW dn vis fe henv n (by omega) ihE,
      bindOKE_step L hnv dn vis fe n ihE,
      appOKE_step L hnv dn vis fe n ihE,
      contOKE_step L hq hIlpf hLC hnv dn vis fe hNit n ihE,
      keyOKEc_of L (keyOKE_step L hnv dn vis fe n ihE.2.2.2.2.2.1),
      newOKE_step L hq hnv dn vis fe hIlpf hLC hNit n ihC ihE,
      frameOKE_step L hq hnv hcE dn vis fe henv n (by omega) ihC ihE,
      ctorsOKE_step L hnv dn vis fe n ihC ihE,
      oneOKE_step L hq hIlpf hnv hcE dn vis fe henv n hn ihC ihE,
      walkOKE_step L hnv dn vis fe n ihE,
      fieldsOKE_step L hnv dn vis fe henv n ihC ihE⟩

end L.Ind
