import ConAgua.Rom.PinStream
import ConAgua.Rom.DataLit
import ConAgua.Rom.Subst
import ConAgua.Arena.IndIface

/-!
# Reading the pin-data buffer in L (lane `romload`)

The checker reads its startup data and the `Nat`-operation pin variants from the pin-data buffer,
byte array `PB` (DESIGN.md, "The pin data as an input"):

* `pb_check()`: the buffer starts with the program's own `romData` (byte for byte; else abort).
  `check` calls it first; after it, `bs = romData ++ rest` for the buffer `bs`.
* The ROM readers (`rom_u64`, `rom_put`, `rom_name`, `rom_level`, `rom_levels`, `rom_expr`,
  `rom_items`) read `PB`: they are the ROM readers of `ConAgua/Arena/Rom*.lean` with every
  `rom.c8[i]` turned into `PB.u8[i]` (`FunDecl.toPB`; `rom_u64`, `rom_put` also read `len(PB.u8)`
  and are written out). Under `Prog.subPB bs` (`ConAgua/Rom/Subst.lean`) they are the ROM readers
  at `rom := bs` (`romProgPB_subPB`), so their proofs carry over.
* `intern_pin_sets(q)`: the variant list (`encPinSets`) at `q`, as the twin's `internPinSets`:
  per variant a 24-word `EREC` record (the eight pin handles, then the eight certificate lists as
  `EREC` slices `(off, len)`), the list of records an `EREC` slice whose offset and count are
  `CTL[150]`, `CTL[151]`. Every expression goes through `rom_expr` at a fresh memo (a pin) or one
  memo per list (a certificate list), as `internExpr`/`internExprList`.
* `rom_pin_sets()`: that list, copied into `IW` (`checkDecl`'s `pins`; lane `decls2`'s
  `check_div_mod_pin_loop` reads it).
-/

namespace L

/-- A block's constant bytes `↦ PB`. -/
def BSrc.toPB : BSrc → BSrc
  | .arr a => .arr a
  | .rom _ => .arr L.Rom.PB

/-- `ldc _ i ↦ PB.u8[i]`: a ROM reader turned into a pin-data reader. -/
def Expr.toPB : Expr → Expr
  | .const w => .const w
  | .var x => .var x
  | .bin op a b => .bin op a.toPB b.toPB
  | .ld8 a i => .ld8 a i.toPB
  | .ld64 a i => .ld64 a i.toPB
  | .len8 a => .len8 a
  | .len64 a => .len64 a
  | .cmpw c a b => .cmpw c a.toPB b.toPB
  | .ldc _ i => .ld8 L.Rom.PB i.toPB
  | .glob g => .glob g
  | .ld64t a t i => .ld64t a t.toPB i.toPB
  | .len64t a t => .len64t a t.toPB
  | .ld8x8 b i => .ld8x8 b.toPB i.toPB

def WArr.toPB : WArr → WArr
  | .plain a => .plain a
  | .tier a t => .tier a t.toPB

def Cond.toPB : Cond → Cond
  | .cmp c a b => .cmp c a.toPB b.toPB
  | .and p q => .and p.toPB q.toPB
  | .or p q => .or p.toPB q.toPB
  | .not p => .not p.toPB

def Stmt.toPB : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x e.toPB
  | .st8 a i e => .st8 a i.toPB e.toPB
  | .st64 a i e => .st64 a i.toPB e.toPB
  | .seq s t => .seq s.toPB t.toPB
  | .ite c s t => .ite c.toPB s.toPB t.toPB
  | .while c s => .while c.toPB s.toPB
  | .brk => .brk
  | .ret es => .ret (es.map Expr.toPB)
  | .call xs f args => .call xs f (args.map Expr.toPB)
  | .abort e => .abort e.toPB
  | .gset g e => .gset g e.toPB
  | .st64t a t i e => .st64t a t.toPB i.toPB e.toPB
  | .copy64 d di s si n => .copy64 d.toPB di.toPB s.toPB si.toPB n.toPB
  | .copy8w d di s si n => .copy8w d.toPB di.toPB s.toPB si.toPB n.toPB
  | .scan8 x s i e c => .scan8 x s.toPB i.toPB e.toPB c

-- con-ron: none — the transform of a ROM reader into a pin-data reader (no twin)
def FunDecl.toPB (fd : FunDecl) : FunDecl := { fd with body := fd.body.toPB }

end L

namespace L.Rom

open L.Arena L.Ind

/-! ## The readers over `PB` -/

/-- `rom_u64(i)` over `PB`. -/
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
def romU64PB : FunDecl := lfn (i) locals (x) {
  if len(PB.u8) < i + 8 || i + 8 < i { abort };
  x := le64!(PB.u8, i);
  return x
}

/-- `rom_put(i, l)` over `PB`. -/
-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values)
def romPutPB : FunDecl := lfn (i, l) locals (top, j, pt, pb, e) {
  if len(PB.u8) < i + l || i + l < i { abort };
  e := i + l;
  j := scan!(PB.u8, i, e, hiC);
  if j != e { abort };
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) < pb { abort };
  if len(POOL⟨pt⟩) - pb < l { abort };
  copy!(POOL.u64⟨pt⟩, pb, PB.u8, i, l);
  CTL.u64[0] := top + l;
  return top
}

theorem romU64PB_subPB (bs : List UInt8) : romU64PB.subPB bs = romU64 bs := rfl
theorem romPutPB_subPB (bs : List UInt8) : romPutPB.subPB bs = romPut bs := rfl
theorem romName_subPB (bs : List UInt8) : (romName []).toPB.subPB bs = romName bs := rfl
theorem romLevel_subPB (bs : List UInt8) : (romLevel []).toPB.subPB bs = romLevel bs := rfl
theorem romExpr_subPB (bs : List UInt8) : (romExpr []).toPB.subPB bs = romExpr bs := rfl
theorem romItems_subPB (bs : List UInt8) : (romItems []).toPB.subPB bs = romItems bs := rfl

/-! ## `pb_check()` -/

/-- `pb_check()`: the buffer starts with `romData`. -/
-- con-ron: none — the pin-data buffer's header (the startup data the twin interns exactly)
def pbCheck : FunDecl := lfn () locals (i) {
  if len(PB.u8) < len(romDataLit.c8) { abort };
  while i < len(romDataLit.c8) {
    if PB.u8[i] != romDataLit.c8[i] { abort };
    i += 1
  };
  return 0
}

/-! ## The variant list -/

/-- `rom_exprs_to(q, o, k)`: `k` expressions at the current memo, their handles to `EREC[o ‥]`;
the position after. -/
-- con-ron: ConRon/Arena/Intern.lean:50-52 ConRon.Arena.internExprList
-- con-ron: ConRon/Arena/Frontend/Readback.lean:262-268 ConRon.Arena.Frontend.internExprList
@[l_impl ConRon.Arena.Frontend.internExprList ConRon.Arena.internExprList]
def romExprsTo : FunDecl := lfn (q, o, k) locals (h, r) {
  if k == 0 { return q };
  (h, q) := call rom_expr(q);
  EREC.u64[o] := h;
  r := call rom_exprs_to(q, o + 1, k - 1);
  return r
}

/-- `rom_pins_to(q, r, k)`: the variant's pins `k ‥ 7`, each at a fresh memo, to `EREC[r + k ‥]`. -/
-- con-ron: ConRon/Arena/Intern.lean:47-48 ConRon.Arena.internExpr
-- con-ron: CHANGED since 12752ca7 — below `ConRon.Arena.internPinSet`, `ConRon.Arena.internPinSetTypePins` changed; re-check the L code and its proofs, then delete this line
-- con-ron: ConRon/Arena/Frontend/Readback.lean:258-260 ConRon.Arena.Frontend.internExpr
-- con-ron: ConRon/Arena/NatOpPinSet.lean:93-114 ConRon.Arena.internPinSet
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.internPinSet` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.internPinSet ConRon.Arena.internExpr ConRon.Arena.Frontend.internExpr]
def romPinsTo : FunDecl := lfn (q, r, k) locals (z) {
  if k == 8 { return q };
  CTL.u64[132] := 0;
  z := call rset_clear();
  q := call rom_exprs_to(q, r + k, 1);
  z := call rom_pins_to(q, r, k + 1);
  return z
}

/-- `rom_lists_to(q, r, j)`: the variant's certificate lists `j ‥ 7`, each at a fresh memo, as
`EREC` slices whose offset and length go to `EREC[r + 8 + 2j]`, `EREC[r + 9 + 2j]`. -/
-- con-ron: ConRon/Arena/NatOpPinSet.lean:93-114 ConRon.Arena.internPinSet
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.internPinSet` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 12752ca7 — below `ConRon.Arena.internPinSet`, `ConRon.Arena.internPinSetTypePins` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.internPinSet]
def romListsTo : FunDecl := lfn (q, r, j) locals (l, o, z) {
  if j == 8 { return q };
  l := call rom_u64(q);
  o := call erec_alloc(l);
  EREC.u64[r + 8 + 2 * j] := o;
  EREC.u64[r + 9 + 2 * j] := l;
  CTL.u64[132] := 0;
  z := call rset_clear();
  q := call rom_exprs_to(q + 8, o, l);
  z := call rom_lists_to(q, r, j + 1);
  return z
}

/-- `rom_sets_to(q, o, k)`: `k` variants, the pointers to their records to `EREC[o ‥]`. -/
-- con-ron: ConRon/Arena/NatOpPinSet.lean:116-123 ConRon.Arena.internPinSets
def romSetsTo : FunDecl := lfn (q, o, k) locals (r, z) {
  if k == 0 { return q };
  r := call erec_alloc(24);
  q := call rom_pins_to(q, r, 0);
  q := call rom_lists_to(q, r, 0);
  EREC.u64[o] := r;
  z := call rom_sets_to(q, o + 1, k - 1);
  return z
}

/-- `intern_pin_sets(q)`: the variant count, then the variants; the list of records at
`CTL[150]` (offset) and `CTL[151]` (count). -/
-- con-ron: ConRon/Arena/NatOpPinSet.lean:116-123 ConRon.Arena.internPinSets
@[l_impl ConRon.Arena.internPinSets]
def internPinSetsL : FunDecl := lfn (q) locals (c, o) {
  c := call rom_u64(q);
  o := call erec_alloc(c);
  CTL.u64[150] := o;
  CTL.u64[151] := c;
  q := call rom_sets_to(q + 8, o, c);
  return q
}

/-- `rom_pin_sets()`: the variant list, an `IW` slice of pointers to the records. -/
-- con-ron: none — the interned pin list `internAllPins` returns, read where `checkDecl` takes it
def romPinSetsL : FunDecl := lfn () locals (o, l, q) {
  o := CTL.u64[150];
  l := CTL.u64[151];
  (q, l) := call er_to_iw(o, l);
  return (q, l)
}

/-- `intern_all_pins()` over the buffer: the memo reset, the startup walk's items at
`allPinsOff`, then the variant list right after them. -/
-- con-ron: ConRon/Arena/Checker.lean:312-342 ConRon.Arena.internAllPins
@[l_impl ConRon.Arena.internAllPins]
def internAllPinsPB : FunDecl := lfn () locals (q, z) {
  CTL.u64[132] := 0;
  z := call rset_clear();
  q := call rom_items(⟪allPinsOff⟫);
  q := call intern_pin_sets(q);
  return 0
}

/-- The pin-data readers of the program (the ROM readers over `PB`, the pin-set readers, the
check), with the other functions the ROM readers call (the store's interners) left to the
program. -/
def romProgPB : Prog :=
  [("pb_check", pbCheck), ("rom_u64", romU64PB), ("rom_put", romPutPB),
   ("rom_name", (romName []).toPB), ("rom_level", (romLevel []).toPB),
   ("rom_expr", (romExpr []).toPB), ("rom_items", (romItems []).toPB),
   ("rom_exprs_to", romExprsTo), ("rom_pins_to", romPinsTo), ("rom_lists_to", romListsTo),
   ("rom_sets_to", romSetsTo), ("intern_pin_sets", internPinSetsL), ("rom_pin_sets", romPinSetsL),
   ("intern_all_pins", internAllPinsPB),
   ("rset_find", memoFindG rsetSch), ("rset_put", memoPutG rsetSch), ("rset_clear", memoClearG rsetSch),
   ("rom_lit", romLit), ("memo_push", memoPush)]

end L.Rom
