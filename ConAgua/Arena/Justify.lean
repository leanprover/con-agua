module

public import ConAgua.Arena.JustifyIface
public import ConAgua.Arena.DeclStep
import ConAgua.Census.Attr
import ConAgua.Layout
import ConAgua.L.Notation

@[expose] public section

/-!
# The justification in L: the comparison and the cone (lane compare, helper compare-cone)

The twin's `Arena/Justify.lean` (Rust `arena/justify.rs`) from `justifiable` to `checkRecord`,
except the side records, the mates and `solutionOf` (`JustifySide.lean`), the solution's
lookups (`JustifyIface.lean`) and the needs walk (`Needs.lean`).

* Constants are `EREC` records (`decCI`), constant values `EREC` pointers (`decCV`), a table an
  `EREC` record handed out as its address plus one (`0`: none), as everywhere.
* **The comparisons** are word comparisons of handles: one store holds both streams. A renaming
  of level parameters is the pin machinery's (`cv_at_lps`, `ci_at_lps`, `BasisL.lean`).
* **The cone walk** keeps its `seen` map in the memo `csSch` (`cs_find`, `cs_put`) and its work
  list on the stack `CWK[0‥CTL[228])`, the next name on top, as the Rust's `cone_go` (a loop over
  a vector and its height). What a name reads (`entry_needs`) is left by the needs walk on
  `NACC[0‥CTL[227])` and pushed last first (`cone_push`), so that the walk takes `ns[0]` next.
* `justify_why(vis, q)` returns `0` for the twin's `none` and the reason's number otherwise
  (`1`: no constant of the name, `2`: another type, `3`: the cone); the twin's message text is not
  mirrored, a rejection is `R_NOT_JUSTIFIED_BY`.
-/

namespace L.Arena

open ConRon.Arena
open L.Front (DECL)
open L.Ind (IW)

/-! ## Which records offer a statement -/

/-- `justifiable(i)`: `justifiable` of record `i` of `DECL`: `1` for an axiom (kind `1`) whose
name is no built-in axiom's (`builtin_axiom_name`), no certified `Nat` operation's
(`nat_op_name`) and no compiler-trust operation's (`reduceOpNames`, pin slots `43`, `44`), else
`0`. The statement offered is the record's own constant value. -/
-- con-ron: ConRon/Arena/Justify.lean:72-82 ConRon.Arena.justifiable
@[no_expose, l_impl ConRon.Arena.justifiable]
def justifiableL : FunDecl := lfn (i) locals (k, n, b, a) {
  k := DECL.u64[1 + 8 * i];
  if k != 1 { return 0 };
  n := DECL.u64[2 + 8 * i] & 4294967295;
  b := call builtin_axiom_name(n);
  if b != 0 { return 0 };
  b := call nat_op_name(n);
  if b != 0 { return 0 };
  a := call pin_at(43);
  b := call pin_at(44);
  if n == a || n == b { return 0 };
  return 1
}

/-! ## The comparison -/

/-- `levels_renaming(q, r)`: `levelsRenaming` of the level parameters of the constant values `q`
and `r`: as many, neither with a repeat (`sl_nodup` of their `IW` copies). -/
-- con-ron: ConRon/Arena/Justify.lean:86-89 ConRon.Arena.levelsRenaming
@[no_expose, l_impl ConRon.Arena.levelsRenaming]
def levelsRenamingL : FunDecl := lfn (q, r) locals (o, l, d) {
  if EREC⦃q + ⟪CV.lpsLen⟫⦄ != EREC⦃r + ⟪CV.lpsLen⟫⦄ { return 0 };
  (o, l) := call cv_lps(q);
  d := call sl_nodup(o, l);
  if d == 0 { return 0 };
  (o, l) := call cv_lps(r);
  d := call sl_nodup(o, l);
  return d
}

/-- `same_cv_up_to_levels(q, r)`: `sameCvUpToLevels cv cv'` (`q` the input's constant value,
`r` the solution's): the same level parameters and equal, or a renaming apart and the solution's at
the input's names (`cv_at_lps` into a fresh `CV.size`-word value) the input's. -/
-- con-ron: ConRon/Arena/Justify.lean:91-101 ConRon.Arena.sameCvUpToLevels
@[no_expose, l_impl ConRon.Arena.sameCvUpToLevels]
def sameCvUpToLevelsL : FunDecl := lfn (q, r) locals (e, d, z) {
  e := call er_sl_eq(EREC⦃q + ⟪CV.lpsOff⟫⦄, EREC⦃q + ⟪CV.lpsLen⟫⦄,
    EREC⦃r + ⟪CV.lpsOff⟫⦄, EREC⦃r + ⟪CV.lpsLen⟫⦄);
  if e != 0 { e := call cv_eq(q, r); return e };
  e := call levels_renaming(q, r);
  if e == 0 { return 0 };
  d := call erec_alloc(⟪CV.size⟫);
  z := call cv_at_lps(d, r, EREC⦃q + ⟪CV.lpsOff⟫⦄, EREC⦃q + ⟪CV.lpsLen⟫⦄);
  e := call cv_eq(d, q);
  return e
}

/-- `tbl_eq(q, r)`: the derived equality of two table records (`decTbl`): the structure, the
level parameters, the counts, the constructor, the bodies. -/
-- con-ron: none — the derived `IProjTable` equality (the Rust's `i_proj_table_beq`, field by field)
@[no_expose] def tblEqL : FunDecl := lfn (q, r) locals (e) {
  if EREC⦃q + ⟪ProjTbl.structName⟫⦄ != EREC⦃r + ⟪ProjTbl.structName⟫⦄ { return 0 };
  e := call er_sl_eq(EREC⦃q + ⟪ProjTbl.lpsOff⟫⦄, EREC⦃q + ⟪ProjTbl.lpsLen⟫⦄,
    EREC⦃r + ⟪ProjTbl.lpsOff⟫⦄, EREC⦃r + ⟪ProjTbl.lpsLen⟫⦄);
  if e == 0 { return 0 };
  if EREC⦃q + ⟪ProjTbl.numParams⟫⦄ != EREC⦃r + ⟪ProjTbl.numParams⟫⦄ { return 0 };
  if EREC⦃q + ⟪ProjTbl.ctor⟫⦄ != EREC⦃r + ⟪ProjTbl.ctor⟫⦄ { return 0 };
  if EREC⦃q + ⟪ProjTbl.numFields⟫⦄ != EREC⦃r + ⟪ProjTbl.numFields⟫⦄ { return 0 };
  e := call er_sl_eq(EREC⦃q + ⟪ProjTbl.bodiesOff⟫⦄, EREC⦃q + ⟪ProjTbl.bodiesLen⟫⦄,
    EREC⦃r + ⟪ProjTbl.bodiesOff⟫⦄, EREC⦃r + ⟪ProjTbl.bodiesLen⟫⦄);
  return e
}

/-- `tbl_beq_p(a, b)`: `tableBeqP` of two lookups' tables (each a record's address plus one, `0`
for none). -/
-- con-ron: ConRon/Arena/Justify.lean:103-107 ConRon.Arena.tableBeqP
@[no_expose, l_impl ConRon.Arena.tableBeqP]
def tblBeqPL : FunDecl := lfn (a, b) locals (e) {
  if a == 0 { return u64(b == 0) };
  if b == 0 { return 0 };
  e := call tbl_eq(a - 1, b - 1);
  return e
}

/-- `is_stmt_kind(p)`: `IConstantInfo.isStmtKind` of the constant record `p`: an axiom (kind `0`),
a definition (`1`) or a theorem (`2`). -/
-- con-ron: ConRon/Arena/Justify.lean:109-113 ConRon.Arena.IConstantInfo.isStmtKind
@[no_expose, l_impl ConRon.Arena.IConstantInfo.isStmtKind]
def isStmtKindL : FunDecl := lfn (p) locals () {
  return u64(EREC⦃p⦄ <= 2)
}

/-- `copy_b(d, c)`: `copyB ci' ci` (`d` the solution's constant record, `c` the input's): the same
level parameters and equal (`ci_eq`), or, for a definition, theorem or axiom at a name no pin
reserves, a renaming apart and the solution's at the input's names (`ci_at_lps`) the input's. -/
-- con-ron: ConRon/Arena/Justify.lean:115-130 ConRon.Arena.copyB
@[no_expose, l_impl ConRon.Arena.copyB]
def copyBL : FunDecl := lfn (d, c) locals (e, s, a) {
  e := call er_sl_eq(EREC⦃c + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃c + ⟪CI.cv + CV.lpsLen⟫⦄,
    EREC⦃d + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃d + ⟪CI.cv + CV.lpsLen⟫⦄);
  if e != 0 { e := call ci_eq(c, d); return e };
  s := call is_stmt_kind(d);
  if s == 0 { return 0 };
  s := call reserved_contains(EREC⦃d + ⟪CI.cv + CV.name⟫⦄);
  if s != 0 { return 0 };
  e := call levels_renaming(d + ⟪CI.cv⟫, c + ⟪CI.cv⟫);
  if e == 0 { return 0 };
  a := call ci_at_lps(d, EREC⦃c + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃c + ⟪CI.cv + CV.lpsLen⟫⦄);
  e := call ci_eq(a, c);
  return e
}

/-- `refines_b(c, d)`: `refinesB ci ci'` (`c` the input's constant record, `d` the solution's): a
copy (`copy_b`), or the input's an axiom and the solution's a definition, theorem or axiom other
than a compiler-trust operation (pin slots `43`, `44`) whose statement, as a fresh axiom record,
it copies. -/
-- con-ron: ConRon/Arena/Justify.lean:132-145 ConRon.Arena.refinesB
@[no_expose, l_impl ConRon.Arena.refinesB]
def refinesBL : FunDecl := lfn (c, d) locals (e, s, n, a, b, x, ez) {
  e := call copy_b(d, c);
  if e != 0 { return 1 };
  if EREC⦃c⦄ != 0 { return 0 };
  s := call is_stmt_kind(d);
  if s == 0 { return 0 };
  n := EREC⦃d + ⟪CI.cv + CV.name⟫⦄;
  a := call pin_at(43);
  b := call pin_at(44);
  if n == a || n == b { return 0 };
  x := call erec_alloc(⟪CI.axiomSize⟫);
  ez := call erec_put(x, 0);
  ez := call er_copy_er(x + ⟪CI.cv⟫, d + ⟪CI.cv⟫, ⟪CV.size⟫);
  e := call copy_b(x, c);
  return e
}

/-! ## The cone -/

/-- `rec_names(d, o, l)`: `recNames`: the names `ms.str "rec"` of the `EREC` name slice `(o, l)`
(`name_rec`), written to `EREC[d‥d + l)`. Returns `0`. -/
-- con-ron: ConRon/Arena/Justify.lean:198-204 ConRon.Arena.recNames
@[no_expose, l_impl ConRon.Arena.recNames]
def recNamesL : FunDecl := lfn (d, o, l) locals (n, ez, u) {
  if l == 0 { return 0 };
  n := call name_rec(EREC⦃o⦄);
  ez := call erec_put(d, n);
  u := call rec_names(d + 1, o + 1, l - 1);
  return 0
}

/-- `entry_needs(c, vis)`: `entryNeeds` of the input's constant record `c` at the view `vis`,
left on `NACC[0‥CTL[227])`: from an empty walk (`needs_reset`) the constant's laws
(`needs_const`), an inductive's constructors and its block's recursors (`rec_names` into a fresh
slice), the record mates of its name (`mates_get`), the names of its table in the input's index
(`find_table`). Returns `0`. -/
-- con-ron: ConRon/Arena/Justify.lean:206-225 ConRon.Arena.entryNeeds
@[no_expose, l_impl ConRon.Arena.entryNeeds]
def entryNeedsL : FunDecl := lfn (c, vis) locals (z, l, d, n, o, t) {
  z := call needs_reset();
  z := call needs_const(c);
  if EREC⦃c⦄ == 3 {
    z := call needs_names(EREC⦃c + ⟪CI.indCaps + Caps.ctorsOff⟫⦄, EREC⦃c + ⟪CI.indCaps + Caps.ctorsLen⟫⦄);
    l := EREC⦃c + ⟪CI.indCaps + Caps.allLen⟫⦄;
    d := call erec_alloc(l);
    z := call rec_names(d, EREC⦃c + ⟪CI.indCaps + Caps.allOff⟫⦄, l);
    z := call needs_names(d, l)
  };
  n := EREC⦃c + ⟪CI.cv + CV.name⟫⦄;
  (o, l) := call mates_get(n);
  if o != 0 { z := call needs_names(o - 1, l) };
  t := call find_table(vis, n);
  if t != 0 { z := call needs_table(t - 1) };
  return 0
}

/-- `cone_entry(w, vis)`: `coneEntry`: `1` with what the name `w` reads on `NACC` (`entry_needs`)
when the input's constant `w` (at the view `vis`) is the solution's (`refines_b`) with the same
table (`tbl_beq_p`), `0` when it is not or either index lacks it. -/
-- con-ron: ConRon/Arena/Justify.lean:227-242 ConRon.Arena.coneEntry
@[no_expose, l_impl ConRon.Arena.coneEntry]
def coneEntryL : FunDecl := lfn (w, vis) locals (f, c, g, d, e, a, b, z) {
  (f, c) := call env_find(w, vis);
  if f == 0 { return 0 };
  (g, d) := call sol_find(w);
  if g == 0 { return 0 };
  e := call refines_b(c, d);
  if e == 0 { return 0 };
  a := call find_table(vis, w);
  b := call sol_find_table(w);
  e := call tbl_beq_p(a, b);
  if e == 0 { return 0 };
  z := call entry_needs(c, vis);
  return 1
}

/-- `cone_push()`: the names `NACC[0‥CTL[227])` onto the stack `CWK` at its top `CTL[228]`, last
first, so that `NACC[0]` is the new top (the cited `ns ++ work`). A full stack aborts (class `0`,
a capacity; the Rust's vector grows). -/
-- con-ron: none — the cited `ns ++ work` on L's stack (the Rust's `cone_push`, a loop)
@[no_expose] def conePushL : FunDecl := lfn () locals (k, h) {
  k := CTL.u64[⟪NTOPC⟫];
  h := CTL.u64[⟪CTOPC⟫];
  while k != 0 {
    k := k - 1;
    if len(CWK.u64) <= h { abort };
    CWK.u64[h] := NACC.u64[k];
    h := h + 1
  };
  CTL.u64[⟪CTOPC⟫] := h;
  return 0
}

/-- `cone_go(f, vis)`: `coneGo J fe f seen work`, `seen` in the memo `csSch`, `work` the stack
`CWK[0‥CTL[228])`, the next name on top: `(1, n)` for the first name `n` that is not the same
constant in both indices (or met at fuel `0`), `(0, 0)` when the stack runs empty. A loop, one
iteration per name taken off the stack (the Rust's `cone_go`). -/
-- con-ron: ConRon/Arena/Justify.lean:244-260 ConRon.Arena.coneGo
@[no_expose, l_impl ConRon.Arena.coneGo]
def coneGoL : FunDecl := lfn (f, vis) locals (h, n, fd, j, d, e, z) {
  h := CTL.u64[⟪CTOPC⟫];
  while h != 0 {
    h := h - 1;
    CTL.u64[⟪CTOPC⟫] := h;
    n := CWK.u64[h];
    (fd, j, d) := call cs_find(n, 0);
    if fd == 0 {
      if f == 0 { return (1, n) };
      e := call cone_entry(n, vis);
      if e == 0 { return (1, n) };
      (fd, j, d) := call cs_find(n, 0);
      d := call cs_put(n, 0, 1, fd, j);
      f := f - 1;
      z := call cone_push()
    };
    h := CTL.u64[⟪CTOPC⟫]
  };
  return (0, 0)
}

/-- `justify_why(vis, q)`: `justifyWhy J fe cv` (`q` the statement's constant value, `vis` the
input's view): `0` when the solution justifies it; `1` when the solution has no constant of its
name, `2` when the solution's has another type (`same_cv_up_to_levels`), `3` when its type's cone
(`needs_expr`, then `cone_go` from an empty `seen` at the fuel `CTL[225] + 1`) meets a name the
solution does not declare alike. -/
-- con-ron: ConRon/Arena/Justify.lean:262-278 ConRon.Arena.justifyWhy
@[no_expose, l_impl ConRon.Arena.justifyWhy]
def justifyWhyL : FunDecl := lfn (vis, q) locals (g, d, e, z, r, n) {
  (g, d) := call sol_find(EREC⦃q⦄);
  if g == 0 { return 1 };
  e := call same_cv_up_to_levels(q, d + ⟪CI.cv⟫);
  if e == 0 { return 2 };
  z := call needs_reset();
  z := call needs_expr(EREC⦃q + ⟪CV.type⟫⦄);
  z := call cs_clear();
  CTL.u64[⟪CTOPC⟫] := 0;
  z := call cone_push();
  (r, n) := call cone_go(CTL.u64[⟪SNEXTC⟫] + 1, vis);
  if r == 0 { return 0 };
  return 3
}

/-! ## The check of one record, with a solution -/

/-- `check_justified(i, vis)`: `checkJustified` of the axiom record `i` of `DECL` (its constant
into `EREC`: `erec_ci(i, 0)`, as the axiom arm): the statement justified by the solution
(`justify_why`, else `R_NOT_JUSTIFIED_BY`), its type checked (`check_constant_val`, no reserved
name allowed), the reserved names' check (`basis_names_ok` at kind `1`, its failure
`basis_names_error`'s reason, as `check_decl`), then the axiom pushed (`env_push`). -/
-- con-ron: ConRon/Arena/Justify.lean:295-306 ConRon.Arena.checkJustified
@[no_expose, l_impl ConRon.Arena.checkJustified]
def checkJustifiedL : FunDecl := lfn (i, vis) locals (p, y, z, ok, e, w) {
  p := call erec_ci(i, 0);
  y := call justify_why(vis, p + ⟪CI.cv⟫);
  if y != 0 { fail R_NOT_JUSTIFIED_BY };
  z := call check_constant_val(vis, p + ⟪CI.cv⟫, 0, 0, 0);
  ok := call basis_names_ok(1, EREC⦃p + ⟪CI.cv + CV.name⟫⦄, 0, 0);
  if ok == 0 {
    e := call basis_names_error(1, 0, 0);
    -- the twin's `fail e`: the reject at the reason `e` (one of `basis_names_error`'s)
    if e == ⟪R_RESERVED_BASIS_NAME_THE⟫ { fail R_RESERVED_BASIS_NAME_THE };
    if e == ⟪R_RESERVED_BASIS_NAME_IN⟫ { fail R_RESERVED_BASIS_NAME_IN };
    fail R_RESERVED_BASIS_NAME
  };
  w := call env_push(vis, p);
  return w
}

/-- `check_record_sol(i, vis)`: `checkRecord` at a solution (`some j`) on record `i` of `DECL` at
the view `vis`: a record that offers a statement (`justifiable`) takes the justification route
(`check_justified`), every other record its own check (`check_decl`). -/
-- con-ron: ConRon/Arena/Justify.lean:308-319 ConRon.Arena.checkRecord
@[no_expose, l_impl ConRon.Arena.checkRecord]
def checkRecordSolL : FunDecl := lfn (i, vis) locals (j, v) {
  j := call justifiable(i);
  if j == 0 { v := call check_decl(i, vis); return v };
  v := call check_justified(i, vis);
  return v
}

/-- This module's functions. -/
def justifyProg : Prog :=
  [("justifiable", justifiableL), ("levels_renaming", levelsRenamingL),
   ("same_cv_up_to_levels", sameCvUpToLevelsL), ("tbl_eq", tblEqL), ("tbl_beq_p", tblBeqPL),
   ("is_stmt_kind", isStmtKindL), ("copy_b", copyBL), ("refines_b", refinesBL),
   ("rec_names", recNamesL), ("entry_needs", entryNeedsL), ("cone_entry", coneEntryL),
   ("cone_push", conePushL), ("cone_go", coneGoL), ("justify_why", justifyWhyL),
   ("check_justified", checkJustifiedL), ("check_record_sol", checkRecordSolL)]

end L.Arena
