module

public import ConAgua.Front.LineRefine
public import ConAgua.Front.ApplyDLineRef
import ConAgua.Front.LineRecLink
public import ConAgua.Scan.LineLink
import ConAgua.Arena.Env
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.FieldsExprLink
import ConAgua.Scan.LeafLink
import all ConAgua.Front.ApplyDecl
import all ConAgua.Front.IndApply
import all ConAgua.Front.Line

@[expose] public section

/-!
# One line, both outcomes: `front_line`

One unified model and one refinement (`docs/design/unifiede.md`). `front_line(i)` reads the line at
`i` once (`skip_ws`, `line_rec`, `skip_ws`) and applies its record (`apply_dline`, `apply_rec`,
`apply_expr`); the twin is con-leche's `scanLineFwd` followed by con-ron's `applyLine`, which
reports a declined record as a value. So `frontLine_ref` is a `RefC`:

* an ok run returns `(0, 0)` (the line does not scan) or `(1, next)`, and then the scan reads a
  record whose `applyLine` succeeds with the memory related after (`LineStep`); the records' table
  grows (`DGrow`) and the mode is kept (`FrontLinePost`);
* a failure of class `≠ 0` is the line's: the scan reads a record and `applyLine` fails on it, in
  the monad or by its record verdict (`LineClaim`).

The scan is read through the validator's `lineFwdN` (`lineFwd_link`) at the arm's value; the
record's fields are the single pass's (`lineRec_fields`, against the record passes the links are
stated for).
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line L.Front.Fields
open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (skipWsN)
open ConLeche.Frontend hiding StateD RecordVerdict applyLine
open ConAgua.Scan ConAgua.Scan.RecordsLink ConAgua.Scan.LineLink
open ConAgua.Front.FieldsLink
open ConRon.Arena ConRon.Arena.Frontend

set_option experimental.vcgen true

namespace L.Front

/-- The scanner's `safety` converse on the declaration lines of `b` (`DeclSafeR`, which
`apply_decl`'s claim takes): what `rec_decl_line` reads at a line con-leche's loop reads as a
declaration record. -/
def SafeLink (b : ByteArray) : Prop :=
  ∀ (j : USize) (r : LineRec) (e : USize) (d : DeclRec),
    scanLineLoop b j true 0 0 .absent = .ok r e → (declLineN b.data j.toUInt64).pl ≠ 0 → r = .decl d →
      DeclSafeR d (declLineN b.data j.toUInt64)

/-- The lookups of a line: the scanner, the name and level steps, the expression and declaration
lines. -/
structure LineLookups (p : Prog) : Prop extends DLineLookups p where
  scan : ScanLookups p
  apply : L.Front.Ind.IndApplyLookups p
  fields : L.Front.Ind.IndFieldLookups p
  install : L.Front.Ind.IndInstallLookups p
  front_line : p.lookup "front_line" = some frontLine
  apply_nstr : p.lookup "apply_nstr" = some applyNStr
  apply_nnum : p.lookup "apply_nnum" = some applyNNum
  apply_level : p.lookup "apply_level" = some applyLevel
  apply_rec : p.lookup "apply_rec" = some applyRec
  apply_str : p.lookup "apply_str" = some applyStr

/-- **`front_line`'s unified model**: the scanner's leaves and the name, level and expression
steps (outside the verdict closure) lifted, `apply_dline` by its unified model. -/
l_model frontLine_specE (p : Prog) (hf : p.lookup "front_line" = some frontLine)
  (hdl : p.lookup "apply_dline" = some applyDLine)
  (hi : p.lookup "apply_ind" = some L.Front.Ind.applyInd)
  (hd : p.lookup "apply_decl" = some applyDecl) (hk : p.lookup "decl_kind" = some declKind)
  fns [hf ↦ frontLineE]
  specs [callW_spec p n "skip_ws", callW_spec p n "line_rec", callW_spec p n "apply_rec",
    callW_spec p n "apply_expr", applyDLine_specE p hdl hi hd hk n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE] heartbeats 1000000
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The twin's scan of a line -/

open L.Front.LineRec in
/-- **The single pass's fields are the record passes'**, on a line that scans: a name or level
line's (`pl ≤ 7`) are `recLineN`'s, an expression line's `exprLineN`'s. -/
theorem lineRec_fields (b : Array UInt8) (j : Word) (he : (lineRecEntryN b j).e ≠ 0)
    (hpl : (lineRecEntryN b j).f.pl ≠ 0) :
    ((lineRecEntryN b j).f.pl ≤ 7 → recLineN b j = (lineRecEntryN b j).f) ∧
      (¬ (lineRecEntryN b j).f.pl ≤ 7 → exprLineN b j = (lineRecEntryN b j).f) := by
  have hp : PlOK 0 Fld.none.pl := ⟨fun _ => rfl, fun h => by simp at h, fun h => by simp at h⟩
  obtain ⟨⟨k0, k1, k2⟩, hk, -⟩ := lineRecN_kind (b := b) j 1 0 0 .none hp he
  unfold lineRecEntryN at *
  rcases hk with h | h | h | h | h
  · exact ⟨fun _ => by rw [recLineN, lineRecN_recN (b := b) j 1 0 0 .none he (.inl h) (.inl rfl)],
      fun h7 => absurd (k1 (.inl h)).2 h7⟩
  · exact ⟨fun _ => by
      rw [recLineN, lineRecN_recN (b := b) j 1 0 0 .none he (.inr (.inl h)) (.inl rfl)],
      fun h7 => absurd (k1 (.inr (.inl h))).2 h7⟩
  · have l := k2 h
    refine ⟨fun h7 => ?_, fun _ => by
      rw [exprLineN, lineRecN_exprN (b := b) j 1 0 0 .none he h (.inl rfl)]⟩
    rw [UInt64.le_iff_toNat_le] at h7 l; simp at h7 l; omega
  · exact absurd (k0 (.inr h)) hpl
  · exact ⟨fun _ => by
      rw [recLineN, lineRecN_recN (b := b) j 1 0 0 .none he (.inr (.inr h)) (.inl rfl)],
      fun h7 => absurd (k1 (.inr (.inr h))).2 h7⟩

section scan
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- A line the validator accepts scans, its next position the validator's. -/
theorem scan_of_fwd (i : USize) {nx : Word} (h : lineFwdN b.data i.toUInt64 = (1, nx)) :
    ∃ r q, scanLineFwd b i = .ok r q ∧ q.toUInt64 = nx := by
  have hL := lineFwd_link b h64 hsize i
  rw [h] at hL
  revert hL
  cases scanLineFwd b i with
  | ok r q => intro hL; exact ⟨r, q, rfl, by simp only [encLine, Prod.mk.injEq] at hL; exact hL.2⟩
  | err e => intro hL; simp [encLine] at hL

/-- **The record of a line that scans**: blank unless its first non-blank byte `s` is `{`, else
the line loop's from the byte after it. -/
theorem scan_shape (i : USize) {r : LineRec} {q : USize} (hs : scanLineFwd b i = .ok r q) (s : Word)
    (hsd : UInt64.ofNat (skipWsN b.data i.toUInt64.toNat) = s) :
    (¬ (s < UInt64.ofNat b.data.size ∧ byteW b.data s = 123) → r = .blank) ∧
      (s < UInt64.ofNat b.data.size → byteW b.data s = 123 →
        ∃ j e', j.toUInt64 = s + 1 ∧ scanLineLoop b j true 0 0 .absent = .ok r e') := by
  rw [USize.toNat_toUInt64, ← ConAgua.Scan.skipWs_toUInt64_eq b h64 (by omega) i] at hsd
  subst hsd
  unfold scanLineFwd at hs
  dsimp only at hs
  generalize skipWs b i = s at hs ⊢
  refine ⟨fun hrec => ?_, fun hslt hs123 => ?_⟩
  · split at hs
    · cases hs; rfl
    split at hs
    · cases hs; rfl
    rename_i h10 hle
    split at hs
    · cases hs
    rename_i h123
    exfalso; apply hrec
    refine ⟨(lt_usize_iff b h64 hsize s).mp (USize.not_le.mp hle), ?_⟩
    rw [byteW_eq b h64 hsize]
    have : byteAt b s = 123 := by simpa using h123
    rw [this]; rfl
  · have hsU : s < b.usize := (lt_usize_iff b h64 hsize s).mpr hslt
    have hb123 : byteAt b s = 123 := by
      rw [byteW_eq b h64 hsize] at hs123; exact (u8_toUInt64_eq _ 123 (by decide)).mp hs123
    simp only [hb123, show ((123 : UInt8) == 10) = false by decide, Bool.false_eq_true, ite_false,
      show (b.usize ≤ s) = False from propext ⟨fun h' => absurd hsU (USize.not_lt.mpr h'), False.elim⟩,
      show ((123 : UInt8) != 123) = false by decide] at hs
    split at hs
    · cases hs
    rename_i r' e' hloop
    have hrr : r' = r := by
      split at hs
      · cases hs; rfl
      · split at hs
        · cases hs; rfl
        · cases hs
    subst hrr
    exact ⟨s + 1, e', succ_toUInt64 h64 s, hloop⟩

/-- A blank line, applied: nothing changes. -/
theorem lineStep_blank (i : USize) {nx : Word} (hf : lineFwdN b.data i.toUInt64 = (1, nx)) (s : Word)
    (hsd : UInt64.ofNat (skipWsN b.data i.toUInt64.toNat) = s)
    (hn : ¬ (s < UInt64.ofNat b.data.size ∧ byteW b.data s = 123))
    {st : StateD} {a : AState} {m : Mem} (hA : ArenaD m a) (hD : StateDR m st) :
    LineStep b i nx st a m := by
  obtain ⟨r, q, hsc, hq⟩ := scan_of_fwd b h64 hsize i hf
  have hr := (scan_shape b h64 hsize i hsc s hsd).1 hn
  subst hr
  obtain ⟨h1, h2, h3⟩ := applyLine_pure st a .blank (.inr rfl)
  exact ⟨.blank, q, st, hsc, hq, h1, h2, by rw [h3]; exact hA, hD⟩

end scan

/-! ## The refinement -/

/-- What `front_line`'s error arms assume: `apply_dline`'s (`ApplyIndG`) and the scanner's
`safety` converse on the input (`SafeLink`). -/
structure FrontLineG (p : Prog) (b : ByteArray) (st : StateD) (a : AState) : Prop where
  ind : L.Front.Ind.ApplyIndG p st a
  safe : SafeLink b

/-- **A failing line's claim**: con-leche's scan reads a record at `i` and con-ron's `applyLine`
fails on it with the error's class, in the monad or by its record verdict. -/
def LineClaim (b : ByteArray) (i : USize) (st : StateD) (a : AState) (e : Err) : Prop :=
  e.cls ≠ 0 → ∃ r q, scanLineFwd b i = .ok r q ∧ VerdictClaimR (applyRecord st r) a e

/-- What a successful `front_line` from `m` gives: `(0, 0)`, or `(1, next)` for a line con-ron
applies (`LineStep`); the records' table grows, the mode is kept. -/
structure FrontLinePost (b : ByteArray) (i : USize) (st : StateD) (a : AState) (m : Mem)
    (x : List Word × Mem) : Prop where
  res : x.1 = [0, 0] ∨ ∃ nx, x.1 = [1, nx] ∧ LineStep b i nx st a x.2
  grow : DGrow m x.2
  mode : ModeOK x.2

/- ronsync2 stage 2: commented out (statement at the old twin/L)
open L.Front.LineRec in
/-- **`front_line` refines con-ron's per-line step, both outcomes**: the scanner's leaves give the
first non-blank byte, the record and the line's end, which are the validator's `lineFwdN` and so
con-leche's scan (`scan_of_fwd`, `scan_shape`); a name or level line is `lineRecW_refines`, an
expression line `applyExprW_refines`, a declaration line `applyDLine_ref` (its failure the
line's). -/
theorem frontLine_ref {p : Prog} (hP : LineLookups p) {b : ByteArray}
    (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (n : Nat) {m : Mem} {a : AState}
    {st : StateD} (hm : m.arr8 IN = b.data) (hA : ArenaD m a) (hD : StateDR m st)
    (hok : ConRon.Bridge.StateOK a) (hmode : ModeOK m) (i : USize) (hi : i.toNat ≤ b.size) :
    RefC (FrontLineG p b st a) (frontLineE p n m i.toUInt64) (FrontLinePost b i st a m)
      (LineClaim b i st a) := by
  have hb64 : b.data.size < 2 ^ 64 := by have : b.data.size = b.size := rfl; omega
  have hi' : i.toUInt64.toNat ≤ b.data.size := by rw [USize.toNat_toUInt64]; exact hi
  have hsz : m.len8 IN = UInt64.ofNat b.data.size := by unfold Mem.len8; rw [hm]
  have hbyte : ∀ w : Word, ((m.arr8 IN)[w.toNat]?.getD 0).toUInt64 = byteW b.data w := by
    intro w; rw [hm]; simp [byteW, Array.getD_eq_getD_getElem?]
  have keep : ∀ r, (r = [0, 0] ∨ ∃ nx, r = [1, nx] ∧ LineStep b i nx st a m) →
      FrontLinePost b i st a m (r, m) := fun r h => ⟨h, (DK.refl m).grow, hmode⟩
  cases n with
  | zero => exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  simp only [frontLineE]
  -- the first non-blank byte
  rcases h1 : callW p n "skip_ws" [i.toUInt64] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, frontLineE.k_skip_ws.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some]
  obtain ⟨s1, hs1, hsm1, rfl⟩ := triple_of_callW (L.Scan.Leaves.skipWs_spec p
    (hP.scan.get "skip_ws") b.data hb64 n ⟨m, Locals.init []⟩ hm i.toUInt64 hi') h1
  obtain rfl : m = m1 := by rw [← hs1, hsm1]
  generalize hsd : UInt64.ofNat (skipWsN b.data i.toUInt64.toNat) = s
  have hfwd : lineFwdN b.data i.toUInt64 = lineFwdN.lineFwd2N b.data s := by rw [lineFwdN, hsd]
  by_cases hnl : s < m.len8 IN ∧ ((m.arr8 IN)[s.toNat]?.getD 0).toUInt64 = 10
  · rw [frontLineE.k_skip_ws.arm1 _ _ [s] m hnl]
    rw [hsz, hbyte] at hnl
    refine keep _ (.inr ⟨s + 1, rfl, lineStep_blank b h64 hsize i ?_ s hsd ?_ hA hD⟩)
    · rw [hfwd]; unfold lineFwdN.lineFwd2N; rw [ite_eq_left hnl]
    · exact fun h => absurd (hnl.2.symm.trans h.2) (by decide)
  by_cases hend : m.len8 IN ≤ s
  · rw [frontLineE.k_skip_ws.arm2 _ _ [s] m hnl hend]
    rw [hsz, hbyte] at hnl
    rw [hsz] at hend
    refine keep _ (.inr ⟨0, rfl, lineStep_blank b h64 hsize i ?_ s hsd ?_ hA hD⟩)
    · rw [hfwd]; unfold lineFwdN.lineFwd2N; rw [ite_eq_right hnl, ite_eq_left hend]
    · exact fun h => absurd h.1 (UInt64.not_lt.mpr hend)
  by_cases h123 : ((m.arr8 IN)[s.toNat]?.getD 0).toUInt64 ≠ 123
  · rw [frontLineE.k_skip_ws.arm3 _ _ [s] m hnl hend h123]; exact keep _ (.inl rfl)
  rw [frontLineE.k_skip_ws.arm4 _ _ [s] m hnl hend (Decidable.not_not.mp h123)]
  simp only [List.headD_cons]
  rw [hsz, hbyte] at hnl
  rw [hsz] at hend
  have hlt : s < UInt64.ofNat b.data.size := UInt64.not_le.mp hend
  have hb : byteW b.data s = 123 := by rw [← hbyte]; exact Decidable.not_not.mp h123
  -- the single pass over the record
  rcases h3 : callW p n "line_rec" [s + 1] m with _ | ⟨r3, m3⟩
  · rw [liftE_none, frontLineE.k_line_rec.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some]
  obtain ⟨s3, hs3, hsm3, rfl⟩ := triple_of_callW (lineRec_spec p b.data hsize (hP.scan.get "skip_ws") (hP.scan.get "skip_digits") (hP.scan.get "key_end") (hP.scan.get "num_end") (hP.scan.get "key_at_g1") (hP.scan.get "key_at_g2") (hP.scan.get "key_at_g3") (hP.scan.get "key_at_g4") (hP.scan.get "key_at_g5") (hP.scan.get "key_at_g6") (hP.scan.get "key_at") (hP.scan.get "value_at") (hP.scan.get "next_member") (hP.scan.get "slot_nat") (hP.scan.get "match_word") (hP.scan.get "scan_binder_info") (hP.scan.get "scan_nat_list") (hP.scan.get "match_lit") (hP.scan.get "scan_bool") (hP.scan.get "utf8_char") (hP.scan.get "utf8_valid") (hP.scan.get "byte_in") (hP.scan.get "hex_val") (hP.scan.get "hex4") (hP.scan.get "hex3") (hP.scan.get "u_next") (hP.scan.get "unescape") (hP.scan.get "str_close") (hP.scan.get "has_escape") (hP.scan.get "scan_string") (hP.scan.get "read_nat") (hP.scan.get "sub_bit") (hP.scan.get "sub_val") (hP.scan.get "sub_rec") (hP.scan.get "rec_nat_list") (hP.scan.get "scan_quoted_nat") (hP.scan.get "skip_braced") (hP.scan.get "hints_num") (hP.scan.get "hints_obj") (hP.scan.get "scan_hints") (hP.scan.get "scan_rule") (hP.scan.get "scan_rules") (hP.scan.get "scan_ind_rec") (hP.scan.get "scan_ind_recs") (hP.scan.get "scan_ind_type") (hP.scan.get "scan_ind_types") (hP.scan.get "scan_ind_ctor") (hP.scan.get "scan_ind_ctors") (hP.scan.get "scan_axiom") (hP.scan.get "scan_def") (hP.scan.get "scan_thm") (hP.scan.get "scan_opaque") (hP.scan.get "scan_quot") (hP.scan.get "scan_ind_decl") (hP.scan.get "line_rec") n ⟨m, Locals.init []⟩ hm (s + 1)) h3
  obtain rfl : m = m3 := by rw [← hs3, hsm3]
  generalize hR : lineRecEntryN b.data (s + 1) = R
  by_cases hne : R.e = 0
  · rw [frontLineE.k_line_rec.arm1 _ _ _ R.enc m hne]; exact keep _ (.inl rfl)
  rw [frontLineE.k_line_rec.arm2 _ _ _ R.enc m hne]
  simp only [LRS.enc, List.headD_cons, List.tail_cons]
  -- the end of the line
  rcases h4 : callW p n "skip_ws" [R.e] m with _ | ⟨r4, m4⟩
  · rw [liftE_none, frontLineE.k_skip_ws_2.none]; exact fun _ hk => absurd (by simp) hk
  rw [liftE_some]
  obtain ⟨s4, hs4, hsm4, rfl⟩ := triple_of_callW (L.Scan.Leaves.skipWs_spec p
    (hP.scan.get "skip_ws") b.data hb64 n ⟨m, Locals.init []⟩ hm R.e
    (by rw [← hR]; exact lineRecEntryN_le (b := b.data) _)) h4
  obtain rfl : m = m4 := by rw [← hs4, hsm4]
  generalize hQ : UInt64.ofNat (skipWsN b.data R.e.toNat) = q
  have hend2 : lineFwdN b.data i.toUInt64 = lineFwdN.lineEndN b.data q := by
    have hL : lineLoopN b.data (s + 1) = R.e := by rw [← hR, lineLoopN, lineRecEntryN, lineRecN_e]
    rw [hfwd]; unfold lineFwdN.lineFwd2N
    rw [ite_eq_right (fun h => by rw [hb] at h; exact absurd h.2 (by decide)),
      ite_eq_right (UInt64.not_le.mpr hlt), ite_eq_right (fun h => h hb), hL, ite_eq_right hne, hQ]
  -- the line scans: its record, applied
  have hj : ∀ nx, lineFwdN b.data i.toUInt64 = (1, nx) →
      RefC (FrontLineG p b st a) (frontLineE.j1 p n nx s R.f.pl R.f.idx R.f.a R.f.c R.f.d m)
        (FrontLinePost b i st a m) (LineClaim b i st a) := by
    intro nx hf
    obtain ⟨r, q', hsc, hq'⟩ := scan_of_fwd b h64 hsize i hf
    obtain ⟨j, e', hjs, hloop⟩ := (scan_shape b h64 hsize i hsc s hsd).2 hlt hb
    have done : ∀ m' st', AM.ok (applyRecord st r) a → AM.res (applyRecord st r) a = .inl st' →
        ArenaD m' (AM.st (applyRecord st r) a) → StateDR m' st' → DGrow m m' → ModeOK m' →
        FrontLinePost b i st a m ([1, nx], m') := fun m' st' h1 h2 h3 h4 hg hmo =>
      ⟨.inr ⟨nx, rfl, r, q', st', hsc, hq', h1, h2, h3, h4⟩, hg, hmo⟩
    simp only [frontLineE.j1]
    by_cases hpl : R.f.pl = 0
    · -- a declaration line
      rw [ite_eq_left hpl]
      have hR' := applyDLine_ref hP.dfields hP.apply.decl hP.apply hP.fields hP.install h64 hsize n
        hm hA hD hok hloop (p := p)
      rw [hjs] at hR'
      rcases h5 : applyDLineE p n m (s + 1) with e5 | ⟨z, m5⟩
      · rw [h5] at hR'; rw [frontLineE.k_apply_dline.none]
        exact fun hG _ => ⟨r, q', hsc, hR' ⟨hG.ind, fun h0 d hd => by
          rw [← hjs]; exact hG.safe j r e' d hloop (by rw [hjs]; exact h0) hd⟩⟩
      rw [h5] at hR'; rw [frontLineE.k_apply_dline.arm1]
      obtain ⟨⟨st', hrun, hD'⟩, hA', hmo, hg⟩ := hR'
      exact done _ st' (by simp [AM.ok, hrun]) (by simp [AM.res, hrun])
        (by simp [AM.st, hrun]; exact hA') hD' hg (hmo hmode)
    rw [ite_eq_right hpl]
    have hF := lineRec_fields b.data (s + 1) (by rw [hR]; exact hne) (by rw [hR]; exact hpl)
    rw [hR] at hF
    by_cases hp7 : R.f.pl ≤ 7
    · -- a name or level line
      rw [ite_eq_left hp7]
      rcases h5 : callW p n "apply_rec" [R.f.pl, R.f.idx, R.f.a, R.f.c, R.f.d] m with _ | ⟨r5, m5⟩
      · rw [liftE_none, frontLineE.k_apply_rec.none]; exact fun _ hk => absurd (by simp) hk
      rw [liftE_some, frontLineE.k_apply_rec.arm1]
      obtain ⟨s5, rfl, -, hW⟩ := triple_of_callW (applyRec_spec p hP.scan hP.apply.decl.expr.front
        hP.apply_nstr hP.apply_nnum hP.apply_level hP.apply_rec hP.apply_str hP.apply.decl.expr b.data
        n ⟨m, Locals.init []⟩ hm hA.base.lit.1.cap hA.base.lit.1.top _ _ _ _ _) h5
      have hRec := recLine_link b h64 hsize j true 0 0 .absent Fld.none r e' hloop itemR_zero trivial
      have hfe : recN b.data j.toUInt64 (bw true) Fld.none = R.f := by
        rw [hjs, ← hF.1 hp7]; rfl
      rw [hfe] at hRec
      obtain ⟨st', h1, h2, h3, h4, h5⟩ :=
        lineRecW_refines b h64 hsize m _ hm a st hA hD hmode R.f r hRec hW
      exact done _ st' h1 h2 h3 h4 (lineRecW_dk _ _ _ _ _ _ _ _ hW).grow h5
    · -- an expression line
      rw [ite_eq_right hp7]
      rcases h5 : callW p n "apply_expr" [R.f.pl, R.f.idx, R.f.a, R.f.c, R.f.d] m with _ | ⟨r5, m5⟩
      · rw [liftE_none, frontLineE.k_apply_rec.none]; exact fun _ hk => absurd (by simp) hk
      rw [liftE_some, frontLineE.k_apply_rec.arm1]
      obtain ⟨s5, rfl, -, hW⟩ := triple_of_callW (applyExpr_spec p hP.apply.decl.expr b.data hsize
        (hP.scan.get "byte_in") (hP.scan.get "hex_val") (hP.scan.get "hex4") (hP.scan.get "hex3")
        (hP.scan.get "esc_sur") (hP.scan.get "esc_one") (hP.scan.get "utf8_put")
        (hP.scan.get "str_put_esc") n ⟨m, Locals.init []⟩ hm hA.base.lit.1.cap hA.base.lit.1.top
        _ _ _ _ _) h5
      have hfe : exprLineN b.data j.toUInt64 = R.f := by rw [hjs, hF.2 hp7]
      have hX := exprLineN_link b h64 hsize j r e' hloop (by rw [hfe]; exact hpl)
      rw [hfe] at hX
      rcases r with _ | _ | ⟨k, er⟩ | _ | _ | _ <;> simp only [ERecR] at hX
      obtain ⟨hI, hE⟩ := hX
      obtain ⟨hok', hA', hD', hM'⟩ := applyExprW_refines b h64 hsize m _ a st hA hD hmode R.f k er hI hE hW
      obtain ⟨h1, h2, h3⟩ := applyLine_expr st a k er hok'
      exact done _ _ h1 h2 (by rw [h3]; exact hA') hD' (applyExprW_dk _ _ _ _ _ _ _ _ hW).grow hM'
  by_cases h10 : q < m.len8 IN ∧ ((m.arr8 IN)[q.toNat]?.getD 0).toUInt64 = 10
  · rw [frontLineE.k_skip_ws_2.arm1 _ _ _ _ _ _ _ _ [q] m h10]
    rw [hsz, hbyte] at h10
    exact hj _ (by rw [hend2]; unfold lineFwdN.lineEndN; rw [ite_eq_left h10]; rfl)
  by_cases hle : m.len8 IN ≤ q
  · rw [frontLineE.k_skip_ws_2.arm2 _ _ _ _ _ _ _ _ [q] m h10 hle]
    rw [hsz, hbyte] at h10
    rw [hsz] at hle
    exact hj _ (by rw [hend2]; unfold lineFwdN.lineEndN; rw [ite_eq_right h10, ite_eq_left hle])
  rw [frontLineE.k_skip_ws_2.arm3 _ _ _ _ _ _ _ _ [q] m h10 hle]; exact keep _ (.inl rfl)
-/

/-- **`front_line(i)` refines con-ron's per-line step**: when it returns `(1, nx)`, con-leche's
scanner reads a record at `i` whose next position is `nx`, and con-ron's `applyLine` applies it,
with `ArenaD` and `StateDR` holding of the memory after (`frontLine_ref`'s ok half). -/
@[refines ConRon.Arena.Frontend.applyLine]
theorem frontLine_refines {p : Prog} (hP : LineLookups p) (b : ByteArray)
    (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b.data) (i : USize) (hi : i.toNat ≤ b.size) (a₀ : AState) (st : StateD)
    (hR : ArenaD s₀.mem a₀) (hD : StateDR s₀.mem st) (hmode : ModeOK s₀.mem)
    (hok : ConRon.Bridge.StateOK a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_line" [i.toUInt64]
    ⦃fun r s' => ∀ nx, r = [1, nx] → LineStep b i nx st a₀ s'.mem; ⊤⦄ := by
  sorry

end L.Front
