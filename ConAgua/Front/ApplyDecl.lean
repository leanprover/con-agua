import ConAgua.Front.ApplyExpr
import ConAgua.Front.DeclIface
import ConAgua.Census.Attr

/-!
# Declaration lines into the parse state: `apply_decl`

con-ron's `processLineCoreD` (`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:405`) reads a
declaration record's common data (`parseCVD`: the name, the type, the universe parameter names),
its value, and appends one `IDeclaration` to `StateD.decls`. Nothing is interned: the arena state
is unchanged. Here the declarations are two word arrays:

* `DECL` (67): word `0` is the number of records; record `i` is the eight words at `1 + 8 i`:
  kind (`1` axiom, `2` def, `3` thm, `4` opaque, `5` quot), name handle, the universe parameters'
  slice `(o, l)` of `DLP`, type handle, value handle (`0` without a value), hint kind / quot kind,
  regular height.
* `DLP` (68): word `0` is the number of words in use; words `1 + j` are name handles.

The functions:
* `lp_put(v)`: the universe parameter list whose `[` is at `v`, read again from the input (the
  traversal of `itemsN`, as `ls_put`), each item a name id looked up in `NID`, the handle words
  appended to `DLP`; returns the slice `(top, count)`.
* `decl_kind(pl, hk, hn, flag)`: the record kind and its hint word, or `abort` where con-ron
  declines (an unsafe axiom or opaque, a definition whose safety is not `safe`), fails (an unknown
  quotient kind) or where the record is not applied here (`inductive`, a string with an escape).
* `decl_push(k, n, o, l, t, v, q, h)`: appends a record.
* `decl_cv(name, lps, type)`: con-ron's `parseCVD`, the name and type handles and the universe
  parameters' slice (`lp_put`).
* `apply_decl(pl, name, lps, type, value, hk, hn, flag)`: the fields of `DeclIface.lean`; in
  con-ron's order, `decl_cv` first, then `decl_kind` (its declines), the value, the push.

Each spec is an equation about a named `Option` model; the refinement is in
`ApplyDeclRefine.lean`.
-/

set_option experimental.vcgen true
set_option linter.unusedSectionVars false

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (numEndN)
open L.Front.Fields (rdNatN NONE itemsN itemsN_end itemsN_close itemsN_digit itemsN_noprog
  itemsN_other)

namespace L.Front

/-- The declaration records. -/
abbrev DECL : ArrId := 67
/-- The universe parameter names of the declaration records. -/
abbrev DLP : ArrId := 68

/-! ## `lp_put(v)` -/

def lpLoop : Stmt := lblk (v, i, top, cnt, c, e, x, h) {
  while 0 == 0 {
    if len(IN.u8) <= i { DLP.u64[0] := top + cnt; return (top, cnt) };
    c := IN.u8[i];
    if c == 93 { DLP.u64[0] := top + cnt; return (top, cnt) };
    if 48 <= c && c <= 57 {
      e := call num_end(i);
      if e <= i { DLP.u64[0] := top + cnt; return (top, cnt) };
      x := call read_nat(i, e);
      if x == 18446744073709551615 { abort R_LONG_NUMBER };
      h := call name_get(x);
      if len(DLP.u64) <= 1 + top + cnt { abort R_CAP_TABLE };
      DLP.u64[1 + top + cnt] := h;
      cnt += 1;
      i := e
    } else {
      i += 1
    }
  }
}

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:405-455 ConRon.Arena.Frontend.processLineCoreD -/
def lpPut : FunDecl := lfn (v) locals (i, top, cnt, c, e, x, h) {
  if len(DLP.u64) == 0 { abort };
  top := DLP.u64[0];
  i := v + 1;
  ⟪lpLoop⟫;
  return (0, 0)
}

/-- The memory after the copy loop of `lp_put`, from `i` with `cnt` written above `top`; `none`
where it aborts. -/
def lpLoopM (b : Array UInt8) (m : Mem) (top i cnt : Word) : Option Mem :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 93 then some (m.set64 DLP 0 (top + cnt))
    else if 48 ≤ byteW b i ∧ byteW b i ≤ 57 then
      if hj : i < UInt64.ofNat (numEndN b i.toNat) then
        if rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) = NONE then none
        else if tblOK m NID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))) = true ∧
            1 + top + cnt < m.len64 DLP then
          lpLoopM b (m.set64 DLP (1 + top + cnt)
            (tblW m NID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))))) top
            (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1)
        else none
      else some (m.set64 DLP 0 (top + cnt))
    else lpLoopM b m top (i + 1) cnt
  else some (m.set64 DLP 0 (top + cnt))
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    first
      | (rw [UInt64.lt_iff_toNat_lt] at hj; omega)
      | (have := L.Scan.toNat_add_one_of_lt_ofNat h; omega)

section lpArms
variable (b : Array UInt8) (m : Mem) (top i cnt : Word)

theorem lpLoopM_end (h : ¬ i < UInt64.ofNat b.size) :
    lpLoopM b m top i cnt = some (m.set64 DLP 0 (top + cnt)) := by
  rw [lpLoopM, dite_eq_right h]
theorem lpLoopM_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) :
    lpLoopM b m top i cnt = some (m.set64 DLP 0 (top + cnt)) := by
  rw [lpLoopM, dite_eq_left h, ite_eq_left hc]
theorem lpLoopM_digit (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : i < UInt64.ofNat (numEndN b i.toNat)) :
    lpLoopM b m top i cnt =
      if rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) = NONE then none
      else if tblOK m NID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))) = true ∧
          1 + top + cnt < m.len64 DLP then
        lpLoopM b (m.set64 DLP (1 + top + cnt)
          (tblW m NID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))))) top
          (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1)
      else none := by
  rw [lpLoopM, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_left he]
theorem lpLoopM_noprog (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : ¬ i < UInt64.ofNat (numEndN b i.toNat)) :
    lpLoopM b m top i cnt = some (m.set64 DLP 0 (top + cnt)) := by
  rw [lpLoopM, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_right he]
theorem lpLoopM_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) : lpLoopM b m top i cnt = lpLoopM b m top (i + 1) cnt := by
  rw [lpLoopM, dite_eq_left h, ite_eq_right hc, ite_eq_right hd]
end lpArms

grind_pattern [lang_grind] lpLoopM_end => lpLoopM b m top i cnt
grind_pattern [lang_grind] lpLoopM_close => lpLoopM b m top i cnt, b[i.toNat]
grind_pattern [lang_grind] lpLoopM_digit => lpLoopM b m top i cnt, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] lpLoopM_noprog => lpLoopM b m top i cnt, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] lpLoopM_other => lpLoopM b m top i cnt, b[i.toNat]

/-- The model of `lp_put(v)`: the memory after. -/
def lpPutW (b : Array UInt8) (m : Mem) (v : Word) : Option Mem :=
  if m.len64 DLP = 0 then none else lpLoopM b m (rdW (m.arr64 DLP) 0) (v + 1) 0

/-! ## `decl_kind`, `decl_push`, `apply_decl` -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:405-455 ConRon.Arena.Frontend.processLineCoreD -/
def declKind : FunDecl := lfn (pl, hk, hn, flag) {
  if pl == 20 { if flag != 0 { if flag == 1 { fail R_UNSAFE_AXIOM_2 }; abort }; return (1, 0) };
  if pl == 21 {
    if flag != 1 { if flag == 2 { abort R_ESCAPED_STRING }; if flag == 0 { fail R_DEFINITION_WITH_SAFETY }; abort };
    if hk == 0 || 3 < hk { abort };
    if hk == 3 && hn == 18446744073709551615 { abort };
    return (2, hk)
  };
  if pl == 22 { return (3, 0) };
  if pl == 23 { if flag != 0 { if flag == 1 { fail R_UNSAFE_OPAQUE_DECLARATION }; abort }; return (4, 0) };
  if pl == 24 { if flag == 5 { abort R_ESCAPED_STRING }; if flag == 0 || 4 < flag { abort }; return (5, flag) };
  abort
}

/-- The model of `decl_kind`: the kind and the hint word, `none` where it aborts. -/
def declKindW (pl hk hn flag : Word) : Option (Word × Word) :=
  if pl = 20 then (if flag = 0 then some (1, 0) else none)
  else if pl = 21 then
    (if flag = 1 ∧ hk ≠ 0 ∧ hk ≤ 3 ∧ ¬ (hk = 3 ∧ hn = NONE) then some (2, hk) else none)
  else if pl = 22 then some (3, 0)
  else if pl = 23 then (if flag = 0 then some (4, 0) else none)
  else if pl = 24 then (if flag ≠ 0 ∧ flag ≤ 4 then some (5, flag) else none)
  else none

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:405-455 ConRon.Arena.Frontend.processLineCoreD -/
def declPush : FunDecl := lfn (k, n, o, l, t, v, q, h) locals (c, x) {
  if len(DECL.u64) == 0 { abort };
  c := DECL.u64[0];
  if 1152921504606846976 <= c { abort R_CAP_WORD };
  x := 1 + c * 8;
  if len(DECL.u64) < x + 8 { abort R_CAP_TABLE };
  DECL.u64[x] := k;
  DECL.u64[x + 1] := n;
  DECL.u64[x + 2] := o;
  DECL.u64[x + 3] := l;
  DECL.u64[x + 4] := t;
  DECL.u64[x + 5] := v;
  DECL.u64[x + 6] := q;
  DECL.u64[x + 7] := h;
  DECL.u64[0] := c + 1;
  return 0
}

/-- The eight words of a record written at `x`. -/
def recM (m : Mem) (x k n o l t v q h : Word) : Mem :=
  ((((((((m.set64 DECL x k).set64 DECL (x + 1) n).set64 DECL (x + 2) o).set64 DECL (x + 3) l).set64
    DECL (x + 4) t).set64 DECL (x + 5) v).set64 DECL (x + 6) q).set64 DECL (x + 7) h)

/-- The model of `decl_push`. -/
def pushW (m : Mem) (k n o l t v q h : Word) : Option Mem :=
  if m.len64 DECL = 0 then none
  else if 1152921504606846976 ≤ rdW (m.arr64 DECL) 0 then none
  else if m.len64 DECL < 1 + rdW (m.arr64 DECL) 0 * 8 + 8 then none
  else some ((recM m (1 + rdW (m.arr64 DECL) 0 * 8) k n o l t v q h).set64 DECL 0
    (rdW (m.arr64 DECL) 0 + 1))

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:405-455 ConRon.Arena.Frontend.processLineCoreD -/
def declCv : FunDecl := lfn (name, lps, type) locals (n, t, o, l) {
  n := call name_get(name);
  t := call expr_get(type);
  (o, l) := call lp_put(lps);
  return (n, t, o, l)
}

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:405-455 ConRon.Arena.Frontend.processLineCoreD -/
@[l_impl ConRon.Arena.Frontend.processLineCoreD]
def applyDecl : FunDecl :=
    lfn (pl, name, lps, type, value, hk, hn, flag) locals (n, t, o, l, k, q, v, z) {
  (n, t, o, l) := call decl_cv(name, lps, type);
  (k, q) := call decl_kind(pl, hk, hn, flag);
  if k == 2 || k == 3 || k == 4 { v := call expr_get(value) } else { v := 0 };
  z := call decl_push(k, n, o, l, t, v, q, hn);
  return 0
}

/-- The model of `decl_cv(name, lps, type)`: the memory after `lp_put`, `none` where it aborts. -/
def cvW (b : Array UInt8) (m : Mem) (name lps type : Word) : Option Mem :=
  if tblOK m NID name = true ∧ tblOK m EID type = true then lpPutW b m lps else none

/-- After `lp_put`: the value (for kinds `2`‥`4`) and the push. -/
def declK1 (k q n t o l hn value : Word) : Option Mem → Option Mem
  | none => none
  | some m₁ =>
    if k = 2 ∨ k = 3 ∨ k = 4 then
      (if tblOK m₁ EID value = true then pushW m₁ k n o l t (tblW m₁ EID value) q hn else none)
    else pushW m₁ k n o l t 0 q hn

@[arena_grind =] theorem declK1_none (k q n t o l hn value : Word) :
    declK1 k q n t o l hn value none = none := rfl
@[arena_grind =] theorem declK1_some (k q n t o l hn value : Word) (m₁ : Mem) :
    declK1 k q n t o l hn value (some m₁) =
      if k = 2 ∨ k = 3 ∨ k = 4 then
        (if tblOK m₁ EID value = true then pushW m₁ k n o l t (tblW m₁ EID value) q hn else none)
      else pushW m₁ k n o l t 0 q hn := rfl

/-- The record after `decl_kind` returned `(k, q)`: `decl_cv`'s common data, the value, the push.
(`apply_decl` runs `decl_cv` before `decl_kind`, as con-ron's `parseCVD` before the safety
declines; `decl_kind` reads no memory, so the order does not show in this `Option` model.) -/
def declCvW (b : Array UInt8) (m : Mem) (k q name lps type value hn : Word) : Option Mem :=
  if tblOK m NID name = true ∧ tblOK m EID type = true then
    declK1 k q (tblW m NID name) (tblW m EID type) (rdW (m.arr64 DLP) 0) (lsCntN b (lps + 1) 0)
      hn value (lpPutW b m lps)
  else none

/-- After `decl_kind`. -/
def declK0 (b : Array UInt8) (m : Mem) (name lps type value hn : Word) :
    Option (Word × Word) → Option Mem
  | none => none
  | some (k, q) => declCvW b m k q name lps type value hn

@[arena_grind =] theorem declK0_none (b : Array UInt8) (m : Mem) (name lps type value hn : Word) :
    declK0 b m name lps type value hn none = none := rfl
@[arena_grind =] theorem declK0_some (b : Array UInt8) (m : Mem) (name lps type value hn k q : Word) :
    declK0 b m name lps type value hn (some (k, q)) = declCvW b m k q name lps type value hn := rfl

/-- **The model of `apply_decl`.** -/
def applyDeclW (b : Array UInt8) (m : Mem) (pl name lps type value hk hn flag : Word) :
    Option Mem :=
  declK0 b m name lps type value hn (declKindW pl hk hn flag)

/-! ## The program -/

/-- The declaration functions with everything they call, on top of `exprProg`. -/
def declProg : Prog := exprProg ++
  [("lp_put", lpPut), ("decl_kind", declKind), ("decl_push", declPush), ("decl_cv", declCv),
   ("apply_decl", applyDecl)]

/-- Every word array 128 words (all zero), the input `[0, 1]`. -/
def declMem : Mem :=
  { bytes := #["[0, 1]".toUTF8.data], words := Array.replicate 75 (Array.replicate 128 0) }

/-- Run the calls in turn; the results. -/
def declRuns (m : Mem) : List (FnName × List Word) → Option (List (List Word))
  | [] => some []
  | (f, vs) :: xs => match run declProg 400 f vs m with
    | .ok (r, m') => (declRuns m' xs).map (r :: ·)
    | .error _ => none

/-- The final memory of the calls. -/
def declFinal (m : Mem) : List (FnName × List Word) → Option Mem
  | [] => some m
  | (f, vs) :: xs => match run declProg 400 f vs m with
    | .ok (_, m') => declFinal m' xs
    | .error _ => none

/- Name 1 = `abc`; expression 0 = `sort 0`; an axiom `abc.{anon, abc}` (universe list `[0, 1]` at
input position 0) of type 0, then a regular definition of height 7: the two records and the
universe parameter words. -/
#guard (declFinal declMem
  [("front_init", []), ("str_put", [0, 3]), ("apply_nstr", [1, 0, 0, 3]),
   ("apply_expr", [9, 0, 0, 0, 0]),
   ("apply_decl", [20, 1, 0, 0, 0, 0, 0, 0]), ("apply_decl", [21, 1, 0, 0, 0, 3, 7, 1])]).map
  (fun m => ((m.arr64 DECL).extract 0 17, (m.arr64 DLP).extract 0 5)) ==
  some (#[2, 1, 0x10000000, 0, 2, 0x20000000, 0, 0, 0, 2, 0x10000000, 2, 2, 0x20000000, 0x20000000, 3, 7],
    #[4, 0, 0x10000000, 0, 0x10000000])

/- An unsafe axiom aborts; a definition that is not `safe` aborts; an unbound type aborts;
`inductive` aborts. -/
#guard (declRuns declMem [("front_init", []), ("apply_expr", [9, 0, 0, 0, 0]),
  ("apply_decl", [20, 0, 0, 0, 0, 0, 0, 1])]).isNone
#guard (declRuns declMem [("front_init", []), ("apply_expr", [9, 0, 0, 0, 0]),
  ("apply_decl", [21, 0, 0, 0, 0, 1, 0, 0])]).isNone
#guard (declRuns declMem [("front_init", []), ("apply_decl", [22, 0, 0, 0, 0, 0, 0, 0])]).isNone
#guard (declRuns declMem [("front_init", []), ("apply_expr", [9, 0, 0, 0, 0]),
  ("apply_decl", [25, 0, 0, 0, 0, 0, 0, 0])]).isNone

/-! ## The specs -/

/-- Every function the declaration functions call, at its name in `p`. -/
structure DeclLookups (p : Prog) : Prop where
  expr : ExprLookups p
  lp_put : p.lookup "lp_put" = some lpPut
  decl_kind : p.lookup "decl_kind" = some declKind
  decl_push : p.lookup "decl_push" = some declPush
  decl_cv : p.lookup "decl_cv" = some declCv
  apply_decl : p.lookup "apply_decl" = some applyDecl

section specs
variable (p : Prog) (hE : DeclLookups p)
include hE

theorem lpLoop_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n lpLoop
    ⦃fun r s' => r ≠ .brk ∧ r.retOr [0, 0] = [s₀.loc 2, lsCntN b (s₀.loc 1) (s₀.loc 3)] ∧
      lpLoopM b s₀.mem (s₀.loc 2) (s₀.loc 1) (s₀.loc 3) = some s'.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lpLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ld64, st64, ih,
        L.Scan.Leaves.numEnd_spec p hE.expr.skip_digits hE.expr.num_end b hb64 n,
        L.Front.Fields.readNat_spec p b hb hE.expr.read_nat n,
        nameGet_spec p hE.expr.front n] <;> finish [NONE]

theorem lpLoop_step_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) lpLoop
    ⦃fun r s' => r ≠ .brk ∧ r.retOr [0, 0] = [s₀.loc 2, lsCntN b (s₀.loc 1) (s₀.loc 3)] ∧
      lpLoopM b s₀.mem (s₀.loc 2) (s₀.loc 1) (s₀.loc 3) = some s'.mem; ⊤⦄ :=
  Triple.step_exec (lpLoop_spec p hE b hb (n + 1) s₀)

theorem lpPut_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lp_put" [v]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [rdW (s₀.mem.arr64 DLP) 0, lsCntN b (v + 1) 0] ∧
      lpPutW b s₀.mem v = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hE.lp_put]
  simp only [callFn, lpPut]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lpLoop_step_spec p hE b hb n] <;> finish [lpPutW]

theorem declKind_spec (n : Nat) (s₀ : St) (pl hk hn flag : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "decl_kind" [pl, hk, hn, flag]
    ⦃fun r s' => s' = s₀ ∧ declKindW pl hk hn flag = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hE.decl_kind]
  simp only [callFn, declKind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc] <;> finish [declKindW, NONE]

theorem declPush_spec (n : Nat) (s₀ : St) (k nm o l t v q h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "decl_push" [k, nm, o, l, t, v, q, h]
    ⦃fun _ s' => LocEq s' s₀ ∧ pushW s₀.mem k nm o l t v q h = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hE.decl_push]
  simp only [callFn, declPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 24) only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;> finish [pushW, recM]

theorem declCv_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (name lps type : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "decl_cv" [name, lps, type]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [tblW s₀.mem NID name, tblW s₀.mem EID type,
      rdW (s₀.mem.arr64 DLP) 0, lsCntN b (lps + 1) 0] ∧ cvW b s₀.mem name lps type = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hE.decl_cv]
  simp only [callFn, declCv]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, nameGet_spec p hE.expr.front n,
        exprGet_spec p hE.expr n, lpPut_spec p hE b hb n] <;>
      finish [cvW]

/-- `apply_decl`'s order (`decl_cv`, then `decl_kind`) gives `applyDeclW`. -/
theorem applyDeclW_cv (b : Array UInt8) (m m₁ : Mem) (pl name lps type value hk hn flag : Word)
    (h : cvW b m name lps type = some m₁) :
    applyDeclW b m pl name lps type value hk hn flag =
      match declKindW pl hk hn flag with
      | none => none
      | some (k, q) => declK1 k q (tblW m NID name) (tblW m EID type) (rdW (m.arr64 DLP) 0)
          (lsCntN b (lps + 1) 0) hn value (some m₁) := by
  unfold cvW at h
  split at h
  · rename_i hok
    unfold applyDeclW
    cases declKindW pl hk hn flag with
    | none => rfl
    | some kq => obtain ⟨k, q⟩ := kq; simp only [declK0, declCvW, ite_eq_left hok, h]
  · cases h

theorem applyDecl_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (pl name lps type value hk hn flag : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_decl" [pl, name, lps, type, value, hk, hn, flag]
    ⦃fun _ s' => LocEq s' s₀ ∧
      applyDeclW b s₀.mem pl name lps type value hk hn flag = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hE.apply_decl]
  simp only [callFn, applyDecl]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, declCv_spec p hE b hb n,
        declKind_spec p hE n, exprGet_spec p hE.expr n, declPush_spec p hE n] <;>
      finish [applyDeclW_cv]

end specs

end L.Front
