import ConAgua.Front.ApplyExpr
import ConAgua.L.ProgHas
import ConAgua.Front.RunModel
import ConAgua.Front.LineRecLink
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# One line of the export, applied: `front_line`

`front_line(i)` reads the line at `i` once, as con-ron's `scan_line_fwd` does (`line_rec`,
`ConAgua.Front.LineRec`): it validates the line and reads its record's fields in one pass, then
applies the record to the parse state: a name or level line by `apply_rec` (`apply_nstr`,
`apply_nnum`, `apply_level`, `ConAgua.Front.Apply`), an expression line by `apply_expr`, a
declaration or inductive line by `apply_dline` (below). It returns `(0, 0)` for a line that does
not scan, `(1, next)` otherwise (`next` after the line's newline, `0` at the end of the input). A
blank line and the `meta` header change nothing. A number of more than 18 digits aborts
(`docs/deviations.md`, D2), as does a full pool or table.

The model `frontLineW` is the validator's `lineFwdN` with the record passes' fields (`recLineN`,
`exprLineN`); `frontLineW_eq` shows it is the single pass's (`ConAgua.Front.LineRecLink`).

`frontLine_refines`: when `front_line(i)` returns `(1, next)`, con-leche's `scanLineFwd b i` is
`.ok r next'` with `next'` the word `next`, and con-ron's `applyLine st r` runs, its state is
related to the memory after by `ArenaR` and its parse state by `StateDR`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line L.Front.Fields
open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (skipWsN hasEscapeN)
open L.Front.Unescape (strPutEscW strPutEsc_specW escSur escOne utf8Put strPutEsc)

namespace L.Front

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:464-477 ConRon.Arena.Frontend.applyLine -/
@[l_impl ConRon.Arena.Frontend.applyLine]
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2576-2599 ConLeche.Frontend.scanLineFwd
def frontLine : FunDecl := lfn (i) locals (ok, nx, s, pl, idx, a, c, d, j, q) {
  s := call skip_ws(i);
  if s < len(IN.u8) && IN.u8[s] == 10 { return (1, s + 1) };
  if len(IN.u8) <= s { return (1, 0) };
  if IN.u8[s] != 123 { return (0, 0) };
  (j, pl, idx, a, c, d) := call line_rec(s + 1);
  if j == 0 { return (0, 0) };
  q := call skip_ws(j);
  if q < len(IN.u8) && IN.u8[q] == 10 { nx := q + 1 }
  else if len(IN.u8) <= q { nx := 0 }
  else { return (0, 0) };
  if pl == 0 { ok := call apply_dline(s + 1) }
  else if pl <= 7 { ok := call apply_rec(pl, idx, a, c, d) }
  else { ok := call apply_expr(pl, idx, a, c, d) };
  return (1, nx)
}

/-- A declaration line: its fields, applied (an inductive block by `apply_ind` at its value's
position `nm`, `IndApply.lean`; a line that does not read aborts). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:464-477 ConRon.Arena.Frontend.applyLine
def applyDLine : FunDecl := lfn (j) locals (pl, nm, lps, ty, vl, hk, hn, fl, z) {
  (pl, nm, lps, ty, vl, hk, hn, fl) := call rec_decl_line(j);
  if pl == 0 { abort };
  if pl == 25 {
    z := call apply_ind(nm);
    return 0
  };
  z := call apply_decl(pl, nm, lps, ty, vl, hk, hn, fl);
  return 0
}

/-- A name or level line with fields `(pl, idx, a, c, d)`, applied. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:464-477 ConRon.Arena.Frontend.applyLine
def applyRec : FunDecl := lfn (pl, idx, a, c, d) locals (z) {
  if pl == 0 { abort };
  if pl == 7 { return 0 };
  if idx == 18446744073709551615 || a == 18446744073709551615 { abort R_LONG_NUMBER };
  if pl == 1 {
    z := call apply_str(idx, a, c, d);
    return 0
  };
  if c == 18446744073709551615 && (pl == 2 || pl == 4 || pl == 5) { abort R_LONG_NUMBER };
  if pl == 2 {
    z := call apply_nnum(idx, a, c);
    return 0
  };
  z := call apply_level(idx, pl - 2, a, c);
  return 0
}

/-- A `str` name line: the body `[c, d)`, unescaped into the pool and applied. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:464-477 ConRon.Arena.Frontend.applyLine
def applyStr : FunDecl := lfn (idx, a, c, d) locals (z, o, l) {
  if c == 0 { abort };
  (o, l) := call str_put_esc(c, d);
  if len(POOL⟨⦃o⦄.tier⟩) < o - ⦃o⦄.base { abort };
  if len(POOL⟨⦃o⦄.tier⟩) - (o - ⦃o⦄.base) < l { abort };
  z := call apply_nstr(idx, a, o, l);
  return 0
}

/-! ## The model -/

/-- A line applied: `(1, next)` and the memory. -/
def okRes (nx : Word) (m : Mem) : List Word × Mem := ([1, nx], m)

/-- After `str_put_esc`: its result `(l, memory)` (`none`: it aborted), the slice at `o`. -/
def strK (idx a o : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (l, m₁) =>
    if m₁.len64 (tierA POOL (o >>> 40)) < o - (o >>> 40) <<< 40 then none
    else if m₁.len64 (tierA POOL (o >>> 40)) - (o - (o >>> 40) <<< 40) < l then none
    else applyNStrW m₁ idx a o l

@[arena_grind =] theorem strK_none (idx a o : Word) : strK idx a o none = none := rfl
@[arena_grind =] theorem strK_some (idx a o l : Word) (m₁ : Mem) : strK idx a o (some (l, m₁)) =
    if m₁.len64 (tierA POOL (o >>> 40)) < o - (o >>> 40) <<< 40 then none
    else if m₁.len64 (tierA POOL (o >>> 40)) - (o - (o >>> 40) <<< 40) < l then none
    else applyNStrW m₁ idx a o l := rfl

theorem strK_intern {idx a o l : Word} {m₁ m' : Mem} (h : strK idx a o (some (l, m₁)) = some m') :
    applyNStrW m₁ idx a o l = some m' := by
  rw [strK_some] at h
  split at h
  · cases h
  split at h
  · cases h
  exact h

/-- The model of `apply_str`. -/
def applyStrW (b : Array UInt8) (m : Mem) (idx a c d : Word) : Option Mem :=
  if c = 0 then none else strK idx a m.top (strPutEscW b m c d)

/-- A name or level line with fields `f`, applied. -/
def lineRecW (b : Array UInt8) (m : Mem) (pl idx a c d : Word) : Option Mem :=
  if pl = 0 then none
  else if pl = 7 then some m
  else if idx = NONE ∨ a = NONE then none
  else if pl = 1 then applyStrW b m idx a c d
  else if c = NONE ∧ (pl = 2 ∨ pl = 4 ∨ pl = 5) then none
  else if pl = 2 then applyNNumW m idx a c
  else applyLevelW m idx (pl - 2) a c

/-- The model of `apply_any(j)`. -/
noncomputable def applyAnyW (p : Prog) (b : Array UInt8) (m : Mem) (j : Word) : Option Mem :=
  if (recLineN b j).pl ≠ 0 then
    lineRecW b m (recLineN b j).pl (recLineN b j).idx (recLineN b j).a (recLineN b j).c
      (recLineN b j).d
  else if (exprLineN b j).pl ≠ 0 then
    applyExprW b m (exprLineN b j).pl (exprLineN b j).idx (exprLineN b j).a (exprLineN b j).c
      (exprLineN b j).d
  else runF p "apply_dline" [j] m

/-- The model of `front_line(i)`. -/
noncomputable def frontLineW (p : Prog) (b : Array UInt8) (m : Mem) (i : Word) : Option (List Word × Mem) :=
  if (lineFwdN b i).1 = 0 then some ([0, 0], m)
  else if UInt64.ofNat (skipWsN b i.toNat) < UInt64.ofNat b.size ∧
      byteW b (UInt64.ofNat (skipWsN b i.toNat)) = 123 then
    (applyAnyW p b m (UInt64.ofNat (skipWsN b i.toNat) + 1)).map (okRes (lineFwdN b i).2)
  else some ([1, (lineFwdN b i).2], m)

theorem map_okRes (nx : Word) (m : Mem) : Option.map (okRes nx) (some m) = some ([1, nx], m) := rfl

open L.Front.LineRec in
/-- The record of a line that scans, applied as `front_line` dispatches on `pl`. -/
noncomputable def lineApplyW (p : Prog) (b : Array UInt8) (m : Mem) (j : Word) (r : LRS) :
    Option Mem :=
  if r.f.pl = 0 then runF p "apply_dline" [j] m
  else if r.f.pl ≤ 7 then lineRecW b m r.f.pl r.f.idx r.f.a r.f.c r.f.d
  else applyExprW b m r.f.pl r.f.idx r.f.a r.f.c r.f.d

open L.Front.LineRec in
/-- After the line's closing brace, at the first non-blank byte `q`. -/
noncomputable def lineEndW (p : Prog) (b : Array UInt8) (m : Mem) (j : Word) (r : LRS) (q : Word) :
    Option (List Word × Mem) :=
  if q < UInt64.ofNat b.size ∧ byteW b q = 10 then (lineApplyW p b m j r).map (okRes (q + 1))
  else if UInt64.ofNat b.size ≤ q then (lineApplyW p b m j r).map (okRes 0)
  else some ([0, 0], m)

open L.Front.LineRec in
/-- `front_line(i)`'s code as a model: from the first non-blank byte `s`. -/
noncomputable def frontLine2W (p : Prog) (b : Array UInt8) (m : Mem) (s : Word) :
    Option (List Word × Mem) :=
  if s < UInt64.ofNat b.size ∧ byteW b s = 10 then some ([1, s + 1], m)
  else if UInt64.ofNat b.size ≤ s then some ([1, 0], m)
  else if byteW b s ≠ 123 then some ([0, 0], m)
  else if (lineRecEntryN b (s + 1)).e = 0 then some ([0, 0], m)
  else lineEndW p b m (s + 1) (lineRecEntryN b (s + 1))
    (UInt64.ofNat (skipWsN b (lineRecEntryN b (s + 1)).e.toNat))

open L.Front.LineRec in
/-- **The record passes' dispatch is the single pass's**, on a line that scans. -/
theorem applyAnyW_lineRec (p : Prog) (b : Array UInt8) (m : Mem) (j : Word)
    (he : (lineRecEntryN b j).e ≠ 0) :
    applyAnyW p b m j = lineApplyW p b m j (lineRecEntryN b j) := by
  have hpl : PlOK 0 Fld.none.pl := ⟨fun _ => rfl, fun h => by simp at h, fun h => by simp at h⟩
  obtain ⟨⟨k0, k1, k2⟩, hk, -⟩ := lineRecN_kind (b := b) j 1 0 0 .none hpl he
  unfold applyAnyW lineApplyW lineRecEntryN at *
  rcases hk with h | h | h | h | h
  · have hr := lineRecN_recN (b := b) j 1 0 0 .none he (.inl h) (.inl rfl)
    obtain ⟨l1, l2⟩ := k1 (.inl h)
    rw [recLineN, hr, ite_eq_left (by intro h0; rw [h0] at l1; simp at l1),
      ite_eq_right (by intro h0; rw [h0] at l1; simp at l1), ite_eq_left l2]
  · have hr := lineRecN_recN (b := b) j 1 0 0 .none he (.inr (.inl h)) (.inl rfl)
    obtain ⟨l1, l2⟩ := k1 (.inr (.inl h))
    rw [recLineN, hr, ite_eq_left (by intro h0; rw [h0] at l1; simp at l1),
      ite_eq_right (by intro h0; rw [h0] at l1; simp at l1), ite_eq_left l2]
  · have hr := lineRecN_recN_none (b := b) j 1 0 0 .none he (.inl h) rfl
    have hx := lineRecN_exprN (b := b) j 1 0 0 .none he h (.inl rfl)
    have l := k2 h
    have l0 : (lineRecN b j 1 0 0 .none).f.pl ≠ 0 := fun h0 => by rw [h0] at l; simp at l
    have l7 : ¬ (lineRecN b j 1 0 0 .none).f.pl ≤ 7 := fun hle => by
      rw [UInt64.le_iff_toNat_le] at hle l; simp at hle l; omega
    rw [recLineN, exprLineN, hr, hx, ite_eq_right (by simp), ite_eq_left l0, ite_eq_right l0,
      ite_eq_right l7]
  · have hr := lineRecN_recN_none (b := b) j 1 0 0 .none he (.inr h) rfl
    have hx := lineRecN_exprN_none (b := b) j 1 0 0 .none he h rfl
    rw [recLineN, exprLineN, hr, hx, ite_eq_right (by simp), ite_eq_right (by simp),
      ite_eq_left (k0 (.inr h))]
  · have hr := lineRecN_recN (b := b) j 1 0 0 .none he (.inr (.inr h)) (.inl rfl)
    obtain ⟨l1, l2⟩ := k1 (.inr (.inr h))
    rw [recLineN, hr, ite_eq_left (by intro h0; rw [h0] at l1; simp at l1),
      ite_eq_right (by intro h0; rw [h0] at l1; simp at l1), ite_eq_left l2]

open L.Front.LineRec in
/-- **`front_line`'s model is its single pass.** -/
theorem frontLineW_eq (p : Prog) (b : Array UInt8) (m : Mem) (i : Word) :
    frontLineW p b m i = frontLine2W p b m (UInt64.ofNat (skipWsN b i.toNat)) := by
  unfold frontLineW frontLine2W lineFwdN lineFwdN.lineFwd2N
  generalize UInt64.ofNat (skipWsN b i.toNat) = s
  by_cases h10 : s < UInt64.ofNat b.size ∧ byteW b s = 10
  · rw [ite_eq_left h10, ite_eq_left h10, ite_eq_right (by simp),
      ite_eq_right (fun h => by rw [h10.2] at h; simp at h)]
  rw [ite_eq_right h10, ite_eq_right h10]
  by_cases hend : UInt64.ofNat b.size ≤ s
  · rw [ite_eq_left hend, ite_eq_left hend, ite_eq_right (by simp),
      ite_eq_right (fun h => absurd h.1 (UInt64.not_lt.mpr hend))]
  rw [ite_eq_right hend, ite_eq_right hend]
  by_cases h123 : byteW b s ≠ 123
  · rw [ite_eq_left h123, ite_eq_left h123, ite_eq_left rfl]
  rw [ite_eq_right h123, ite_eq_right h123]
  have hlt : s < UInt64.ofNat b.size := UInt64.not_le.mp hend
  have hb : byteW b s = 123 := Decidable.not_not.mp h123
  have hL : lineLoopN b (s + 1) = (lineRecEntryN b (s + 1)).e := by
    rw [lineLoopN, lineRecEntryN, lineRecN_e]
  rw [hL]
  by_cases h0 : (lineRecEntryN b (s + 1)).e = 0
  · rw [ite_eq_left h0, ite_eq_left h0, ite_eq_left rfl]
  rw [ite_eq_right h0, ite_eq_right h0]
  unfold lineFwdN.lineEndN lineEndW
  rw [applyAnyW_lineRec p b m (s + 1) h0]
  generalize UInt64.ofNat (skipWsN b (lineRecEntryN b (s + 1)).e.toNat) = q
  by_cases hq : q < UInt64.ofNat b.size ∧ byteW b q = 10
  · rw [ite_eq_left hq, ite_eq_left hq, ite_eq_right (by simp), ite_eq_left ⟨hlt, hb⟩]
  rw [ite_eq_right hq, ite_eq_right hq]
  by_cases he : UInt64.ofNat b.size ≤ q
  · rw [ite_eq_left he, ite_eq_left he, ite_eq_right (by simp), ite_eq_left ⟨hlt, hb⟩]
  rw [ite_eq_right he, ite_eq_right he, ite_eq_left rfl]

/-! ## The spec -/

/-- The functions of `ScanLookups`. -/
def scanLookupsFns : Prog :=
  [("skip_ws", L.Scan.Leaves.skipWs), ("skip_digits", L.Scan.Leaves.skipDigits),
   ("key_end", L.Scan.Leaves.keyEnd), ("num_end", L.Scan.Leaves.numEnd),
   ("key_at_g1", L.Scan.Key.keyAtG1), ("key_at_g2", L.Scan.Key.keyAtG2),
   ("key_at_g3", L.Scan.Key.keyAtG3), ("key_at_g4", L.Scan.Key.keyAtG4),
   ("key_at_g5", L.Scan.Key.keyAtG5), ("key_at_g6", L.Scan.Key.keyAtG6),
   ("key_at", L.Scan.Key.keyAt), ("value_at", L.Scan.Key.valueAt),
   ("next_member", L.Scan.Member.nextMember), ("slot_nat", L.Scan.Values.slotNat),
   ("match_word", L.Scan.Values.matchWord), ("scan_binder_info", L.Scan.Values.scanBinderInfo),
   ("hints_num", L.Scan.Values.hintsNum), ("hints_obj", L.Scan.Values.hintsObj),
   ("scan_hints", L.Scan.Values.scanHints), ("scan_nat_list", L.Scan.Values.scanNatList),
   ("match_lit", L.Scan.Lit.matchLit), ("scan_bool", L.Scan.Lit.scanBool),
   ("utf8_char", L.Scan.Utf8.utf8Char), ("utf8_valid", L.Scan.Str.utf8Valid),
   ("byte_in", L.Scan.Str.byteIn), ("hex_val", L.Scan.Str.hexVal), ("hex4", L.Scan.Str.hex4),
   ("hex3", L.Scan.Str.hex3), ("u_next", L.Scan.Str.uNext), ("unescape", L.Scan.Str.unescape),
   ("str_close", L.Examples.strClose), ("has_escape", L.Scan.Leaves.hasEscape),
   ("scan_string", L.Scan.Str.scanString), ("scan_str_name", L.Scan.Records.scanStrName),
   ("scan_num_name", L.Scan.Records.scanNumName), ("scan_app", L.Scan.Records.scanApp),
   ("scan_binder", L.Scan.Records.scanBinder), ("scan_let", L.Scan.Records.scanLetE),
   ("scan_const", L.Scan.Records.scanConstE), ("scan_proj", L.Scan.Records.scanProj),
   ("scan_rule", L.Scan.Records.scanRule), ("scan_rules", L.Scan.Records.scanRules),
   ("scan_ind_rec", L.Scan.Records.scanIndRec), ("scan_ind_recs", L.Scan.Records.scanIndRecs),
   ("scan_ind_type", L.Scan.Records.scanIndType), ("scan_ind_types", L.Scan.Records.scanIndTypes),
   ("scan_ind_ctor", L.Scan.Records.scanIndCtor), ("scan_ind_ctors", L.Scan.Records.scanIndCtors),
   ("scan_axiom", L.Scan.Records.scanAxiomD), ("scan_def", L.Scan.Records.scanDefD),
   ("scan_thm", L.Scan.Records.scanThmD), ("scan_opaque", L.Scan.Records.scanOpaqueD),
   ("scan_quot", L.Scan.Records.scanQuotD), ("scan_ind_decl", L.Scan.Records.scanIndD),
   ("skip_braced", L.Examples.skipBraced), ("scan_quoted_nat", L.Scan.Values.scanQuotedNat),
   ("scan_line_loop", L.Scan.Line.scanLineLoop), ("scan_line", L.Scan.Line.scanLine),
   ("validate", L.Scan.Line.validate), ("read_nat", L.Front.Fields.readNat),
   ("rec_nat_list", L.Front.Fields.recNatList), ("sub_bit", L.Front.LineRec.subBitF),
   ("sub_val", L.Front.LineRec.subValF), ("sub_rec", L.Front.LineRec.subRec),
   ("line_rec", L.Front.LineRec.lineRec),
   ("esc_sur", escSur), ("esc_one", escOne), ("utf8_put", utf8Put), ("str_put_esc", strPutEsc)]

/-- Every function of the validator and of the single pass, at its name in `p`. -/
abbrev ScanLookups (p : Prog) : Prop := ProgHas p scanLookupsFns

section spec
variable (p : Prog) (hS : ScanLookups p) (hL : FrontLookups p)
  (hpf : p.lookup "front_line" = some frontLine) (hps : p.lookup "str_put" = some strPut)
  (hpn : p.lookup "apply_nstr" = some applyNStr) (hpu : p.lookup "apply_nnum" = some applyNNum)
  (hpl : p.lookup "apply_level" = some applyLevel)
  (hpr : p.lookup "apply_rec" = some applyRec) (hpt : p.lookup "apply_str" = some applyStr)
  (hE : ExprLookups p)
  (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hS hL hpf hps hpn hpu hpl hpr hpt hE hb

attribute [local lang_grind =] map_okRes

omit hb in
omit hpf hps hpu hpl hpr in
theorem applyStr_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (hpool : pcap s₀.mem < 2 ^ 63)
    (htop : s₀.mem.top.toNat ≤ pcap s₀.mem)
    (idx a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_str" [idx, a, c, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ applyStrW b s₀.mem idx a c d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hpt]
  simp only [callFn, applyStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hesc : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ c d : Word,
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "str_put_esc" [c, d]
        ⦃fun r s' => (LocEq s' s₁ ∧ r.headD 0 = s₁.mem.top ∧
          strPutEscW b s₁.mem c d = some (r.tail.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ := fun s₁ hm₁ c d =>
      Triple.keep hE.no_st8 (strPutEsc_specW p b (hS.get "byte_in") (hS.get "hex_val") (hS.get "hex4") (hS.get "hex3")
        (hS.get "esc_sur") (hS.get "esc_one") (hS.get "utf8_put") (hS.get "str_put_esc") n s₁ hm₁ c d)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hesc,
        applyNStr_spec p hL hpn n] <;> finish [applyStrW, Keep.size]

omit hb in
omit hpf hps in
theorem applyRec_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (hpool : pcap s₀.mem < 2 ^ 63)
    (htop : s₀.mem.top.toNat ≤ pcap s₀.mem)
    (pl idx a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_rec" [pl, idx, a, c, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ lineRecW b s₀.mem pl idx a c d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hpr]
  simp only [callFn, applyRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        applyStr_spec p hS hL hpn hpt hE b n,
        applyNNum_spec p hL hpu n, applyLevel_spec p hL hpl n] <;> finish [lineRecW, NONE]

omit hps in
theorem frontLine_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word)
    (hi : i.toNat ≤ b.size) (hpool : pcap s₀.mem < 2 ^ 63)
    (htop : s₀.mem.top.toNat ≤ pcap s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_line" [i]
    ⦃fun r s' => frontLineW p b s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpf]
  simp only [callFn, frontLine]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    rw [frontLineW_eq]
    sym (gen := 16) only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8,
        L.Front.LineRec.lineRec_spec p b hb (hS.get "skip_ws") (hS.get "skip_digits") (hS.get "key_end") (hS.get "num_end") (hS.get "key_at_g1") (hS.get "key_at_g2") (hS.get "key_at_g3") (hS.get "key_at_g4") (hS.get "key_at_g5") (hS.get "key_at_g6") (hS.get "key_at") (hS.get "value_at") (hS.get "next_member") (hS.get "slot_nat") (hS.get "match_word") (hS.get "scan_binder_info") (hS.get "scan_nat_list") (hS.get "match_lit") (hS.get "scan_bool") (hS.get "utf8_char") (hS.get "utf8_valid") (hS.get "byte_in") (hS.get "hex_val") (hS.get "hex4") (hS.get "hex3") (hS.get "u_next") (hS.get "unescape") (hS.get "str_close") (hS.get "has_escape") (hS.get "scan_string") (hS.get "read_nat") (hS.get "sub_bit") (hS.get "sub_val") (hS.get "sub_rec") (hS.get "rec_nat_list") (hS.get "scan_quoted_nat") (hS.get "skip_braced") (hS.get "hints_num") (hS.get "hints_obj") (hS.get "scan_hints") (hS.get "scan_rule") (hS.get "scan_rules") (hS.get "scan_ind_rec") (hS.get "scan_ind_recs") (hS.get "scan_ind_type") (hS.get "scan_ind_types") (hS.get "scan_ind_ctor") (hS.get "scan_ind_ctors") (hS.get "scan_axiom") (hS.get "scan_def") (hS.get "scan_thm") (hS.get "scan_opaque") (hS.get "scan_quot") (hS.get "scan_ind_decl") (hS.get "line_rec") n,
        L.Scan.Leaves.skipWs_spec p (hS.get "skip_ws") b hb64 n,
        applyRec_spec p hS hL hpn hpu hpl hpr hpt hE b n,
        applyExpr_spec p hE b hb (hS.get "byte_in") (hS.get "hex_val") (hS.get "hex4") (hS.get "hex3") (hS.get "esc_sur") (hS.get "esc_one")
          (hS.get "utf8_put") (hS.get "str_put_esc") n,
        runF_spec p "apply_dline" _ n] <;>
        finish [frontLine2W, lineEndW, lineApplyW, okRes, L.Front.LineRec.LRS.enc,
          L.Front.LineRec.lineRecEntryN_le]

end spec

end L.Front
