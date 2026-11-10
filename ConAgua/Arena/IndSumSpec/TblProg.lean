module

public import ConAgua.Arena.IndRealCrF
public import ConAgua.Arena.IndRealIlpP
public import ConAgua.Arena.DeclRec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndRealWalk
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# TblProg

`erecPut_specM` and `efgW_spec` (`er_from_iw_go`), the lookups `TblProg`, the record memory `tblMem`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `er_from_iw` -/

/-- `erec_put`'s effect without its bound (the models of the record copies are total). -/
theorem erecPut_specM (p : Prog) (hp : p.lookup "erec_put" = some erecPut) (n : Nat) (s₀ : St)
    (a v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_put" [a, v]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = erecPutMem s₀.mem a v; ⊤⦄ :=
  triple_post (erecPut_specW p hp n s₀ a v) fun _ _ h => ⟨h.1, h.2.1⟩

/-- **The model of `er_from_iw_go(q, o, l)`** at exec fuel `n`. -/
l_model efgW_spec (p : Prog) (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "er_from_iw_go" = some erFromIwGo)
  fns [hp ↦ efgW list]
  specs [erecPut_specM p hpu n]
  grind [arena_grind]

/-! ## `check_struct_proj_table`: the word model -/

/-- The memory after the table record's thirteen writes. -/
def tblMem (m : Mem) (q T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 : Word) : Mem :=
  ((((((((((((m.set64 EREC q 6).set64 EREC (q + 1) 0).set64 EREC (q + 2) T).set64 EREC (q + 3) lo2
    ).set64 EREC (q + 4) ll2).set64 EREC (q + 5) nP).set64 EREC (q + 6) C).set64 EREC (q + 7) nF
    ).set64 EREC (q + 8) rs).set64 EREC (q + 9) bo2).set64 EREC (q + 10) bl2).set64 EREC (q + 11) go2
    ).set64 EREC (q + 12) gl2

/-- The program lookups of `check_struct_proj_table`. -/
structure TblProg (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hsc : p.lookup "sl_cons" = some slCons
  hv : p.lookup "e_view" = some eView
  hd : p.lookup "der_b" = some derB
  hpf : p.lookup "bvar_find" = some bvarFind
  hpp : p.lookup "bvar_push" = some bvarPush
  hib : p.lookup "intern_bvar" = some internBVar
  hjf : p.lookup "proj_find" = some projFind
  hjp : p.lookup "proj_push" = some projPush
  hji : p.lookup "intern_proj" = some internProj
  hmp : p.lookup "mk_proj" = some mkProj
  hap : p.lookup "struct_proj_arg_p" = some structProjArgPL
  hpg : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL
  hgo : p.lookup "struct_ps_at_go" = some structPsAtGoL
  hps : p.lookup "struct_ps_at" = some structPsAtL
  hpj : p.lookup "struct_proj_ps" = some structProjPsL
  hspb : p.lookup "struct_proj_bodies" = some structProjBodiesL
  hsct : p.lookup "check_struct_proj_table_scoped" = some checkStructProjTableScopedL
  hbb : BvbProg p
  hhf : HfF p
  hrg : p.lookup "env_row_get" = some envRowGetL
  hfind : p.lookup "env_find" = some envFindL
  hftab : p.lookup "find_table" = some findTableL
  hept : p.lookup "env_push_table" = some envPushTableL
  hea : p.lookup "erec_alloc" = some erecAlloc
  hefg : p.lookup "er_from_iw_go" = some erFromIwGo
  hef : p.lookup "er_from_iw" = some erFromIw
  htbl : p.lookup "check_struct_proj_table" = some checkStructProjTableL
  hrec : RecProg p
  hi1 : I1lF p
  hipal : IpalF p
  hcr : CrfF p
  hft : FindTableProg p

end L.Ind

end
