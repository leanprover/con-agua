import ConAgua.Arena.IndPosSpec.SlRCongr
import ConAgua.Arena.IndRealCrF
import ConAgua.Arena.IndRealIlpP
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecStab

/-!
# TblProg

`efgK`, `efgW`, `efgW_nil`, `efgW_cons`, `efgK_some`, `efgW_spec` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `er_from_iw` -/

/-- After the rest of the copy. -/
def efgK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

/-- **The model of `er_from_iw_go(q, o, l)`** at exec fuel `n`. -/
def efgW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, o, l =>
    if l = 0 then some ([0], m)
    else efgK (efgW n (m.set64 EREC q (rdW (m.arr64 IW) o)) (q + 1) (o + 1) (l - 1))

theorem efgW_nil (n : Nat) (m : Mem) (q o l : Word) (h : l = 0) : efgW (n + 1) m q o l = some ([0], m) := by
  simp [efgW, h]
theorem efgW_cons (n : Nat) (m : Mem) (q o l : Word) (h : l ≠ 0) : efgW (n + 1) m q o l =
    efgK (efgW n (m.set64 EREC q (rdW (m.arr64 IW) o)) (q + 1) (o + 1) (l - 1)) := by simp [efgW, h]
theorem efgK_some (r : List Word) (m : Mem) : efgK (some (r, m)) = some ([0], m) := rfl
attribute [ind_grind] efgW_nil efgW_cons efgK_some

theorem efgW_spec (p : Prog) (hp : p.lookup "er_from_iw_go" = some erFromIwGo) (n : Nat) :
    ∀ (s₀ : St) (q o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_from_iw_go" [q, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ efgW n s₀.mem q o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ q o l; rw [invoke_eq _ hp]; simp only [callFn, erFromIwGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q o l
    rw [invoke_eq _ hp]
    simp only [callFn, erFromIwGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- After the copy. -/
def efK2 (q l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([q, l], m)
/-- After the allocation. -/
def efK1 (n : Nat) (o l : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m) => efK2 q l (efgW n m q o l)
/-- **The model of `er_from_iw(o, l)`** at callee fuel `n`. -/
def efW (n : Nat) (m : Mem) (o l : Word) : Option (List Word × Mem) := efK1 n o l (erAllocW m l)

theorem efK1_some (n : Nat) (o l q : Word) (m : Mem) : efK1 n o l (some (q, m)) = efK2 q l (efgW n m q o l) :=
  rfl
theorem efK2_some (q l : Word) (r : List Word) (m : Mem) : efK2 q l (some (r, m)) = some ([q, l], m) := rfl
attribute [ind_grind] efK1_some efK2_some

theorem efW_spec (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hg : p.lookup "er_from_iw_go" = some erFromIwGo) (hp : p.lookup "er_from_iw" = some erFromIw)
    (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "er_from_iw" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ efW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erFromIw]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, erecAlloc_specW p ha n,
      efgW_spec p hg n] <;>
    finish (gen := 20) [efW]

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
  hix : p.lookup "env_ix" = some envIxL
  hrg : p.lookup "env_row_get" = some envRowGetL
  hfind : p.lookup "env_find" = some envFindL
  htix : p.lookup "tbl_ix" = some tblIxL
  htrg : p.lookup "tbl_row_get" = some tblRowGetL
  htrs : p.lookup "tbl_row_set" = some tblRowSetL
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

end L.Ind

end
