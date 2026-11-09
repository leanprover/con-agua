module

public import ConAgua.Arena.IndDeclConstsBlock
public import ConAgua.Arena.IndSumSpec.StructProjBodies
public import ConAgua.Arena.IndPartsSpec.MemberNames
public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.IndSumSpec.TsrW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# A declaration's tables (lane `ronsync2`, stage 3)

`block_table(p, ms)` refines one member of con-ron's `blockTables` (`Arena/Install.lean`): a
structure-like member's constructor (`MemberShape.structCtor?`), its projection bodies
(`struct_proj_bodies`, `spbW_ok`), the block's level parameters (`block_shape_lps`, `lpsW_dec`)
and the bodies copied into `EREC` (`er_from_iw`, `efF_stage`), the 13-word table record
(`erec_alloc`, `erec_put`s: `btMem_eq`, `erRec_stage`). `block_tables(p, mo, ml)` refines
`blockTables p ms`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `block_table(s)`. -/
structure TablesProg (p : Prog) : Prop extends BlockProg p where
  tErCopy : p.lookup "er_copy" = some L.Ind.erCopy
  tErToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  sView : p.lookup "e_view" = some eView
  sDerB : p.lookup "der_b" = some derB
  sBvarFind : p.lookup "bvar_find" = some bvarFind
  sBvarPush : p.lookup "bvar_push" = some bvarPush
  sInternBVar : p.lookup "intern_bvar" = some internBVar
  sProjFind : p.lookup "proj_find" = some projFind
  sProjPush : p.lookup "proj_push" = some projPush
  sInternProj : p.lookup "intern_proj" = some internProj
  sMkProj : p.lookup "mk_proj" = some mkProj
  sArgP : p.lookup "struct_proj_arg_p" = some structProjArgPL
  sGo : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL
  sPsAtGo : p.lookup "struct_ps_at_go" = some structPsAtGoL
  sPsAt : p.lookup "struct_ps_at" = some structPsAtL
  sProjPs : p.lookup "struct_proj_ps" = some structProjPsL
  spb : p.lookup "struct_proj_bodies" = some structProjBodiesL
  i1l : I1lF p
  ipal : IpalF p
  bt : p.lookup "block_table" = some blockTable
  bts : p.lookup "block_tables" = some blockTables

/-! ## The twin, one member at a time -/

/-- One member's table, if any (`blockTables`' step). -/
def tblOne (bs : BlockShape) (ms : MemberShape) : AM (Option IProjTable) :=
  match ms.structCtor? with
  | some c => do
    match ← structProjBodies ms.declared.name bs.nP c.2 c.1.type with
    | some bodies => pure (some ⟨ms.declared.name, bs.lps, bs.nP, c.1.name, c.2, bodies⟩)
    | none => pure none
  | none => pure none

theorem blockTables_cons (bs : BlockShape) (ms : MemberShape) (rest : List MemberShape) :
    ConRon.Arena.blockTables bs (ms :: rest) =
      (do let o ← tblOne bs ms; let ts ← ConRon.Arena.blockTables bs rest; pure (o.toList ++ ts)) := by
  cases h : ms.structCtor? with
  | none => simp [ConRon.Arena.blockTables, tblOne, h]
  | some c =>
    simp only [ConRon.Arena.blockTables, tblOne, h, bind_assoc]
    congr 1; funext x
    cases x <;> simp

/-! ## `block_table`: the model -/

/-- The memory after the table record's thirteen `erec_put`s (each argument read at its time). -/
def btMem (m1 : Mem) (q pp c cv T elo ell ebo ebl : Word) : Mem :=
  let m6 := erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m1 q 6) (q + 1) 0) (q + 2) T)
    (q + 3) elo) (q + 4) ell
  let m7 := erecPutMem m6 (q + 5) (rdW (m6.arr64 IW) (pp + 4))
  let m8 := erecPutMem m7 (q + 6) (erRd m7 cv)
  let m9 := erecPutMem m8 (q + 7) (rdW (m8.arr64 IW) (c + 1))
  erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m9 (q + 8) 0) (q + 9) ebo) (q + 10) ebl)
    (q + 11) 0) (q + 12) 0

/-- After `erec_alloc`: the puts. -/
def btK5 (pp c cv T elo ell ebo ebl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([1, r.headD 0], btMem m (r.headD 0) pp c cv T elo ell ebo ebl)

/-- After the bodies' copy: the record. -/
def btK4 (p : Prog) (n : Nat) (pp c cv T elo ell : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => btK5 pp c cv T elo ell (r.headD 0) (r.tail.headD 0) (callW p n "erec_alloc" [13] m)

/-- After the level parameters' copy: the bodies'. -/
def btK3 (p : Prog) (n : Nat) (pp c cv T bo bl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => btK4 p n pp c cv T (r.headD 0) (r.tail.headD 0) (callW p n "er_from_iw" [bo, bl] m)

/-- After `block_shape_lps`: their copy. -/
def btK2 (p : Prog) (n : Nat) (pp c cv T bo bl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => btK3 p n pp c cv T bo bl (callW p n "er_from_iw" [r.headD 0, r.tail.headD 0] m)

/-- After `struct_proj_bodies`. -/
def btK1 (p : Prog) (n : Nat) (pp c cv T : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else btK2 p n pp c cv T (r.tail.headD 0) (r.tail.tail.headD 0) (callW p n "block_shape_lps" [pp] m)

/-- **The model of `block_table(p, ms)`** at exec fuel `n`. -/
def btW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, pp, ms =>
    if rdW (m.arr64 IW) (ms + 3) ≠ 1 then some ([0, 0], m)
    else if rdW (m.arr64 IW) (ms + 1) ≠ 0 then some ([0, 0], m)
    else
      let c := rdW (m.arr64 IW) (rdW (m.arr64 IW) (ms + 2))
      let cv := rdW (m.arr64 IW) c
      let T := erRd m (rdW (m.arr64 IW) (ms + 4))
      btK1 p n pp c cv T (callW p n "struct_proj_bodies"
        [T, rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (c + 1), erRd m (cv + 3)] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp c cv T bo bl elo ell ebo ebl : Word) (r : List Word)
theorem btK5_some : btK5 pp c cv T elo ell ebo ebl (some (r, m)) =
    some ([1, r.headD 0], btMem m (r.headD 0) pp c cv T elo ell ebo ebl) := rfl
theorem btK4_some : btK4 p n pp c cv T elo ell (some (r, m)) =
    btK5 pp c cv T elo ell (r.headD 0) (r.tail.headD 0) (callW p n "erec_alloc" [13] m) := rfl
theorem btK3_some : btK3 p n pp c cv T bo bl (some (r, m)) =
    btK4 p n pp c cv T (r.headD 0) (r.tail.headD 0) (callW p n "er_from_iw" [bo, bl] m) := rfl
theorem btK2_some : btK2 p n pp c cv T bo bl (some (r, m)) =
    btK3 p n pp c cv T bo bl (callW p n "er_from_iw" [r.headD 0, r.tail.headD 0] m) := rfl
theorem btK1_some : btK1 p n pp c cv T (some (r, m)) =
    if r.headD 0 = 0 then some ([0, 0], m)
    else btK2 p n pp c cv T (r.tail.headD 0) (r.tail.tail.headD 0) (callW p n "block_shape_lps" [pp] m) := rfl
end arms
attribute [ind_grind] btK5_some btK4_some btK3_some btK2_some btK1_some

theorem bt_spec {p : Prog} (hP : TablesProg p) (n : Nat) (s₀ : St) (pp ms : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_table" [pp, ms]
    ⦃fun r s' => LocEq s' s₀ ∧ btW p n s₀.mem pp ms = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.bt]
  simp only [callFn, blockTable]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "struct_proj_bodies", callW_spec p n "block_shape_lps",
        callW_spec p n "er_from_iw", callW_spec p n "erec_alloc", erecPut_specW p hP.erPut n] <;>
      finish (gen := 40) (instances := 20000) [btW, btMem, erRd, rdW_eq]

end L.Ind

end
