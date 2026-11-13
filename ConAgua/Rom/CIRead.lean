module

public import ConAgua.Arena.Prelude
public import ConAgua.Rom.CIConst

@[expose] public section

/-!
# The ROM stubs' readers (lane `integrate`)

`rom_basis_decls(kind)`, `rom_ci(id)`, `rom_cv(id)`, `rom_expr_pin(id)` and `rom_and_pin()`
(the interface of `DeclArmsNat.lean`'s `romStubs`, the specs of `DeclRomStubs.lean`) read the
structured region `romCIData` of the ROM (at `ciOff`; the encoding is `ConAgua/Rom/CIEnc.lean`'s)
and build the records `EnvRec.lean`'s decoders read: a constant in `EREC` (`decCI`; its lists are
`EREC` slices, recursor rules 11-word records), a constant value in `EREC` (`decCV`, 4 words), a
block an `IW` slice of `EREC` pointers. Every name, level and expression goes through the ROM
readers over the program's constant data (`rom_name_c`, `rom_level_c`, `rom_expr_c`,
`rom_exprs_to_c`, `CIConst.lean`: a job has no pin-data buffer), at a fresh expression memo per
twin call (`internCI`, `internCV`, `internExpr`) and one memo per block (`internCIList`), in the
twin's intern order. As the twin, each use interns again (in a job, into the scratch tier): there
is no cache.
-/

namespace L.Rom

open L.Arena L.Ind

/-! ## Helpers -/

/-- `rci_slot(s)`: the position of the region's entry `s`. -/
-- con-ron: none — the ROM layout (L reads con-leche values from the pin-data buffer)
@[no_expose] def rciSlot : FunDecl := lfn (s) locals (x) {
  x := call rom_u64_c(⟪ciOff⟫ + 8 * s);
  return ⟪ciOff⟫ + x
}

/-- `rci_fresh()`: a fresh expression memo, and the level stack `RSTK` at its base (`rom_levels`
needs room above `CTL[131]`; nothing else holds the stack between two ROM reads). -/
-- con-ron: none — the expression memo's reset (the twin starts each intern at `∅`)
@[no_expose] def rciFresh : FunDecl := lfn () locals (z) {
  CTL.u64[131] := 0;
  CTL.u64[132] := 0;
  z := call rset_clear();
  return 0
}

/-- `rci_names_to(q, o, k)`: `k` names to `EREC[o ‥]`; the position after. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:271-277 ConRon.Arena.Frontend.internNameList
@[no_expose] def rciNamesTo : FunDecl := lfn (q, o, k) locals (h, r, ez) {
  if k == 0 { return q };
  (h, q) := call rom_name_c(q);
  ez := call erec_put(o, h);
  r := call rci_names_to(q, o + 1, k - 1);
  return r
}

/-- `rci_name_sl(q, d)`: a name list (count, names) as an `EREC` slice, its offset and length to
`EREC[d]`, `EREC[d + 1]`; the position after. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:271-277 ConRon.Arena.Frontend.internNameList
@[no_expose] def rciNameSl : FunDecl := lfn (q, d) locals (c, o, ez) {
  c := call rom_u64_c(q);
  o := call erec_alloc(c);
  ez := call erec_put(d, o);
  ez := call erec_put(d + 1, c);
  q := call rci_names_to(q + 8, o, c);
  return q
}

/-- `rci_lvls_to(q, o, k)`: `k` levels to `EREC[o ‥]`; the position after. -/
-- con-ron: ConRon/Arena/Monad.lean:528-534 ConRon.Arena.internLevelList
@[no_expose] def rciLvlsTo : FunDecl := lfn (q, o, k) locals (h, r, ez) {
  if k == 0 { return q };
  (h, q) := call rom_level_c(q);
  ez := call erec_put(o, h);
  r := call rci_lvls_to(q, o + 1, k - 1);
  return r
}

/-- `rci_cv(q, p)`: a constant value to `EREC[p ‥ p + 3]` (name, level parameters, type) at the
current memo; the position after. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:279-284 ConRon.Arena.Frontend.internCV
@[no_expose, l_impl ConRon.Arena.Frontend.internCV]
def rciCv : FunDecl := lfn (q, p) locals (h, ez) {
  (h, q) := call rom_name_c(q);
  ez := call erec_put(p, h);
  q := call rci_name_sl(q, p + 1);
  (h, q) := call rom_expr_c(q);
  ez := call erec_put(p + 3, h);
  return q
}

/-- `rci_caps(q, c)`: an inductive's capabilities to the 15 words at `c` (`decCaps`); the position
after. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:312-316 ConRon.Arena.Frontend.internCaps
-- con-ron: CHANGED since 4ca283d1 — `ConRon.Arena.Frontend.internCaps` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.Frontend.internCaps]
def rciCaps : FunDecl := lfn (q, c) locals (x, ez) {
  x := call rom_u64_c(q);
  ez := call erec_put(c, x);
  x := call rom_u64_c(q + 8);
  ez := call erec_put(c + 6, x);
  x := call rom_u64_c(q + 16);
  ez := call erec_put(c + 12, x);
  q := call rci_name_sl(q + 24, c + 10);
  q := call rci_name_sl(q, c + 13);
  x := call rom_u64_c(q);
  ez := call erec_put(c + 7, x);
  return q + 8
}

/-- `rci_rule(q, r)`: a recursor rule to the 11-word record at `r` (`decRule`) at the current
memo; the position after. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:297-302 ConRon.Arena.Frontend.internRule
-- con-ron: ConRon/Arena/Frontend/Readback.lean:286-295 ConRon.Arena.Frontend.internFire
@[no_expose, l_impl ConRon.Arena.Frontend.internRule ConRon.Arena.Frontend.internFire]
def rciRule : FunDecl := lfn (q, r) locals (h, x, f, l, o, ez) {
  (h, q) := call rom_name_c(q);
  ez := call erec_put(r, h);
  x := call rom_u64_c(q);
  ez := call erec_put(r + 1, x);
  f := call rom_u64_c(q + 8);
  ez := call erec_put(r + 3, f);
  q := q + 16;
  ez := call erec_put(r + 4, 0);
  ez := call erec_put(r + 5, 0);
  ez := call erec_put(r + 6, 0);
  ez := call erec_put(r + 7, 0);
  if f == 1 || f == 2 {
    l := call rom_u64_c(q);
    o := call erec_alloc(l);
    ez := call erec_put(r + 4, o);
    ez := call erec_put(r + 5, l);
    q := call rci_lvls_to(q + 8, o, l)
  };
  if f == 1 {
    l := call rom_u64_c(q);
    o := call erec_alloc(l);
    ez := call erec_put(r + 6, o);
    ez := call erec_put(r + 7, l);
    q := call rom_exprs_to_c(q + 8, o, l)
  };
  (h, q) := call rom_expr_c(q);
  ez := call erec_put(r + 8, h);
  return q
}

/-- `rci_rules_to(q, o, k)`: `k` rules to the 11-word records at `o`, `o + 11`, …; the position
after. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:304-310 ConRon.Arena.Frontend.internRules
@[no_expose, l_impl ConRon.Arena.Frontend.internRules]
def rciRulesTo : FunDecl := lfn (q, o, k) locals (r) {
  if k == 0 { return q };
  q := call rci_rule(q, o);
  r := call rci_rules_to(q, o + 11, k - 1);
  return r
}

/-- `rci_ci(q)`: a constant at the current memo, as a fresh `EREC` record (`decCI`); the record's
pointer and the position after; an unknown kind is refused. Each kind's arm returns (no paths
merge after it). -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:318-341 ConRon.Arena.Frontend.internCI
-- con-ron: CHANGED since 4ca283d1 — `ConRon.Arena.Frontend.internCI` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.Frontend.internCI]
def rciCi : FunDecl := lfn (q) locals (k, n, p, h, x, l, o, ez) {
  k := call rom_u64_c(q);
  q := q + 8;
  if k == 0 { n := 5 } else if k == 2 { n := 5 } else if k == 1 { n := 8 } else if k == 3 { n := 20 }
  else if k == 4 { n := 8 } else if k == 5 { n := 10 } else { abort };
  p := call erec_alloc(n);
  ez := call erec_put(p, k);
  q := call rci_cv(q, p + 1);
  if k == 1 {
    (h, q) := call rom_expr_c(q);
    ez := call erec_put(p + 5, h);
    x := call rom_u64_c(q);
    ez := call erec_put(p + 6, x);
    x := call rom_u64_c(q + 8);
    ez := call erec_put(p + 7, x);
    return (p, q + 16)
  };
  if k == 3 {
    q := call rci_caps(q, p + 5);
    return (p, q)
  };
  if k == 4 {
    x := call rom_u64_c(q);
    ez := call erec_put(p + 5, x);
    x := call rom_u64_c(q + 8);
    ez := call erec_put(p + 6, x);
    (h, q) := call rom_name_c(q + 16);
    ez := call erec_put(p + 7, h);
    return (p, q)
  };
  if k == 5 {
    x := call rom_u64_c(q);
    ez := call erec_put(p + 5, x);
    x := call rom_u64_c(q + 8);
    ez := call erec_put(p + 6, x);
    x := call rom_u64_c(q + 16);
    ez := call erec_put(p + 9, x);
    l := call rom_u64_c(q + 24);
    o := call erec_alloc(11 * l);
    ez := call erec_put(p + 7, o);
    ez := call erec_put(p + 8, l);
    q := call rci_rules_to(q + 32, o, l);
    return (p, q)
  };
  return (p, q)
}

/-- `rci_block_to(q, o, k)`: `k` constants at the current memo, their record pointers to
`IW[o ‥]`; the position after. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:343-349 ConRon.Arena.Frontend.internCIList
@[no_expose, l_impl ConRon.Arena.Frontend.internCIList]
def rciBlockTo : FunDecl := lfn (q, o, k) locals (p, r) {
  if k == 0 { return q };
  (p, q) := call rci_ci(q);
  IW.u64[o] := p;
  r := call rci_block_to(q, o + 1, k - 1);
  return r
}

/-- `rci_block(s)`: the block of entry `s` at one fresh memo, as an `IW` slice. -/
-- con-ron: ConRon/Arena/Intern.lean:66-69 ConRon.Arena.internCIList
@[no_expose, l_impl ConRon.Arena.internCIList]
def rciBlock : FunDecl := lfn (s) locals (q, c, o, z) {
  q := call rci_slot(s);
  c := call rom_u64_c(q);
  z := call rci_fresh();
  o := call iw_alloc(c);
  q := call rci_block_to(q + 8, o, c);
  return (o, c)
}

/-! ## The entries -/

/-- `rom_basis_decls(kind)`: the raw basis block of `kind` (`0` eqK … `4` quotK). -/
-- con-ron: ConRon/Arena/Basis.lean:38-41 ConRon.Arena.BasisKind.decls
@[no_expose, l_impl ConRon.Arena.BasisKind.decls]
def romBasisDeclsL : FunDecl := lfn (kind) locals (o, l) {
  if kind >= 5 { abort };
  (o, l) := call rci_block(kind);
  return (o, l)
}

/-- `rom_ci(id)`: the constant `romCiT id` at a fresh memo, an `EREC` record pointer. -/
-- con-ron: ConRon/Arena/Basis.lean:43-47 ConRon.Arena.natA
-- con-ron: CHANGED since 4ca283d1 — below `ConRon.Arena.iffIntroA`, `ConRon.Arena.internCI` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 4ca283d1 — below `ConRon.Arena.nonemptyRecA`, `ConRon.Arena.internCI` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 4ca283d1 — below `ConRon.Arena.natA`, `ConRon.Arena.internCI` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 4ca283d1 — below `ConRon.Arena.nonemptyIntroA`, `ConRon.Arena.internCI` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 4ca283d1 — below `ConRon.Arena.iffRecA`, `ConRon.Arena.internCI` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 4ca283d1 — below `ConRon.Arena.iffA`, `ConRon.Arena.internCI` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 4ca283d1 — below `ConRon.Arena.nonemptyA`, `ConRon.Arena.internCI` changed; re-check the L code and its proofs, then delete this line
-- con-ron: ConRon/Arena/StdAxioms.lean:70-71 ConRon.Arena.iffA
-- con-ron: ConRon/Arena/StdAxioms.lean:72-73 ConRon.Arena.iffIntroA
-- con-ron: ConRon/Arena/StdAxioms.lean:74-75 ConRon.Arena.iffRecA
-- con-ron: ConRon/Arena/StdAxioms.lean:78-79 ConRon.Arena.nonemptyA
-- con-ron: ConRon/Arena/StdAxioms.lean:80-81 ConRon.Arena.nonemptyIntroA
-- con-ron: ConRon/Arena/StdAxioms.lean:82-83 ConRon.Arena.nonemptyRecA
@[no_expose, l_impl ConRon.Arena.natA ConRon.Arena.iffA ConRon.Arena.iffIntroA
  ConRon.Arena.iffRecA ConRon.Arena.nonemptyA ConRon.Arena.nonemptyIntroA ConRon.Arena.nonemptyRecA]
def romCiL : FunDecl := lfn (id) locals (q, z, p) {
  if id >= 7 { abort };
  q := call rci_slot(5 + id);
  z := call rci_fresh();
  (p, q) := call rci_ci(q);
  return p
}

/-- `rom_cv(id)`: the constant value `romCvT id` at a fresh memo, a 4-word `EREC` record. -/
-- con-ron: ConRon/Arena/StdAxioms.lean:76-77 ConRon.Arena.propextA
-- con-ron: ConRon/Arena/StdAxioms.lean:84-85 ConRon.Arena.choiceA
-- con-ron: ConRon/Arena/TrustAxioms.lean:61-62 ConRon.Arena.trueCvA
-- con-ron: ConRon/Arena/TrustAxioms.lean:63-64 ConRon.Arena.trueIntroCvA
-- con-ron: ConRon/Arena/TrustAxioms.lean:65-66 ConRon.Arena.trustCompilerA
-- con-ron: ConRon/Arena/TrustAxioms.lean:67-68 ConRon.Arena.boolCvA
-- con-ron: ConRon/Arena/TrustAxioms.lean:81-83 ConRon.Arena.reduceNatCvA
-- con-ron: ConRon/Arena/TrustAxioms.lean:84-85 ConRon.Arena.reduceBoolCvA
-- con-ron: ConRon/Arena/TrustAxioms.lean:86-87 ConRon.Arena.ofReduceNatA
-- con-ron: ConRon/Arena/TrustAxioms.lean:88-89 ConRon.Arena.ofReduceBoolA
@[no_expose, l_impl ConRon.Arena.propextA ConRon.Arena.choiceA ConRon.Arena.trueCvA ConRon.Arena.trueIntroCvA
  ConRon.Arena.trustCompilerA ConRon.Arena.boolCvA ConRon.Arena.reduceNatCvA
  ConRon.Arena.reduceBoolCvA ConRon.Arena.ofReduceNatA ConRon.Arena.ofReduceBoolA]
def romCvL : FunDecl := lfn (id) locals (q, z, p) {
  if id >= 10 { abort };
  q := call rci_slot(12 + id);
  p := call erec_alloc(4);
  z := call rci_fresh();
  q := call rci_cv(q, p);
  return p
}

/-- `rom_expr_pin(id)`: the expression `romExprT id` at a fresh memo, a handle (the stub
`rom_expr(id)` of `romStubs`, renamed). -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:109-111 ConRon.Arena.reduceNatDeclPin
-- con-ron: ConRon/Arena/TrustAxioms.lean:105-107 ConRon.Arena.reduceBoolDeclPin
@[no_expose, l_impl ConRon.Arena.reduceNatDeclPin ConRon.Arena.reduceBoolDeclPin]
def romExprPinL : FunDecl := lfn (id) locals (q, z, h) {
  if id >= 2 { abort };
  q := call rci_slot(22 + id);
  z := call rci_fresh();
  (h, q) := call rom_expr_c(q);
  return h
}

/-- `rom_and_pin()`: the pinned `And` block (`andPinDecls`, `internCIList andPin`), an `IW` slice. -/
-- con-ron: ConRon/Arena/Basis.lean:286-290 ConRon.Arena.andPinDecls
@[no_expose, l_impl ConRon.Arena.andPinDecls]
def romAndPinL : FunDecl := lfn () locals (o, l) {
  (o, l) := call rci_block(24);
  return (o, l)
}

/-- **The ROM stubs' readers.** The functions they call from other modules: `rom_u64`,
`rom_name`, `rom_level`, `rom_expr`, `rom_exprs_to`, `rset_clear` (`romProgPB`), `erec_alloc`,
`iw_alloc` (`IndIface.lean`). -/
def romCIProg : Prog :=
  [("rom_basis_decls", romBasisDeclsL), ("rom_ci", romCiL),
   ("rom_cv", romCvL), ("rom_expr_pin", romExprPinL), ("rom_and_pin", romAndPinL),
   ("rci_slot", rciSlot), ("rci_fresh", rciFresh),
   ("rci_names_to", rciNamesTo), ("rci_name_sl", rciNameSl), ("rci_lvls_to", rciLvlsTo),
   ("rci_cv", rciCv), ("rci_caps", rciCaps), ("rci_rule", rciRule), ("rci_rules_to", rciRulesTo),
   ("rci_ci", rciCi), ("rci_block_to", rciBlockTo), ("rci_block", rciBlock)] ++ romConstProg

end L.Rom
