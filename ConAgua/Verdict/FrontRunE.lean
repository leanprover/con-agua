import ConAgua.Verdict.FrontE
import ConAgua.Front.FrontPreOK
import ConAgua.Checker.FrontProg
import ConAgua.Checker.NoVerdictClosed

/-!
# Error refinements of the frontend's driver: `apply_ind`, `apply_dline`, `apply_any`,
`front_line`, `front_run` (lane `verdicts-b`, helper `f2`)
-/

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD processLineCoreD feedChunk applyFinalLine
open Std.WP
open scoped Lean.Order
open L.Arena

set_option experimental.vcgen true

namespace L.Front.Ind

/-- **The claim of `validate_ind_d`** (proved in `FrontValidE.lean`): from the hypotheses of the
ok refinement `validateW_twin` and twin facts `X st a`, a failing call claims `validateIndD`'s
record verdict (or failure). -/
def ValidateClaim (p : Prog) (X : StateD → AState → Prop) : Prop :=
  ∀ (b : ByteArray) (n : Nat) (m : Mem) (a : AState) (st : StateD) (to tn co cn ro rn : Word)
    (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) (e : Err),
    ArenaR m a → StateDR m st → ConRon.Bridge.StateOK a → TopOK m →
    IndFR b m to tn co cn ro rn tys cts rcs → topN m IFR < 2 ^ 62 → X st a →
    callE p n "validate_ind_d" [to, tn, co, cn, ro, rn] m = .error e →
    VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a e

/-- `validateIndD`'s verdict is the `.ind` line's. -/
theorem claimR_of_validate {st : StateD} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} {a : AState} {e : Err}
    (h : VerdictClaimL (ConRon.Arena.Frontend.validateIndD st tys cts rcs) a e) :
    VerdictClaimR (applyLine st (.decl (.ind tys cts rcs))) a e := by
  intro hk
  have hrun : (applyLine st (.decl (.ind tys cts rcs))).run a =
      (processLineCoreD st (.ind tys cts rcs)).run a := rfl
  rcases h hk with ⟨ce, hce, hc⟩ | ⟨v, a', hv, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    rw [hrun]; unfold processLineCoreD
    simp only [StateT.run_bind, show (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = _ from hce]
    rfl
  · refine .inr ⟨v, a', ?_, hc⟩
    rw [hrun]; unfold processLineCoreD
    simp only [StateT.run_bind, show (ConRon.Arena.Frontend.validateIndD st tys cts rcs).run a = _ from hv]
    rfl

l_model applyInd_specE (p : Prog) (hf : p.lookup "apply_ind" = some applyInd)
  fns [hf ↦ applyIndE] grind [arena_grind] simp [] errors

end L.Front.Ind

namespace L.Front

l_model applyDLine_specE (p : Prog) (hf : p.lookup "apply_dline" = some applyDLine)
  fns [hf ↦ applyDLineE] grind [arena_grind] simp [] errors

l_model applyAny_specE (p : Prog) (hf : p.lookup "apply_any" = some applyAny)
  fns [hf ↦ applyAnyE] grind [arena_grind] simp [] errors

l_model frontLine_specE (p : Prog) (hf : p.lookup "front_line" = some frontLine)
  fns [hf ↦ frontLineE] grind [arena_grind] extra [L.Arena.ld64_rdW_specE] errors

l_model frontRun_specE (p : Prog) (hf : p.lookup "front_run" = some frontRun)
  fns [hf ↦ frontRunE] grind [arena_grind] errors

end L.Front

namespace L.Front.Ind

/-- **`apply_ind`'s error model claims the `.ind` line's verdict**: `ind_fields` and
`install_ind_d` claim nothing; `validate_ind_d`'s claim (`ValidateClaim`) is the line's. -/
theorem applyIndE_claim (p : Prog) (hFI : IndFieldLookups p) {X : StateD → AState → Prop}
    (hV : ValidateClaim p X) (hnv : NVCls p ["ind_fields", "install_ind_d"])
    {b : ByteArray} (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
    {m : Mem} {a : AState} {st : StateD} (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) (hX : X st a) {v : USize}
    {tys : List IndTypeRec} {cts : List IndCtorRec} {rcs : List IndRecRec} {e' : USize}
    (hscan : scanIndDecl b v = .ok (.ind tys cts rcs) e') (n : Nat) :
    ∀ e, applyIndE p n m v.toUInt64 = .error e → VerdictClaimR (applyLine st (.decl (.ind tys cts rcs))) a e := by
  intro e he
  by_cases hk : e.cls = 0
  · exact fun h => absurd hk h
  cases n with
  | zero => simp only [applyIndE] at he; cases he; exact absurd rfl hk
  | succ n =>
  simp only [applyIndE] at he
  cases h1 : callE p n "ind_fields" [v.toUInt64] m with
  | error e1 =>
    rw [h1, applyIndE.k_ind_fields.none] at he; cases he
    exact absurd (hnv.cls (by simp) h1) hk
  | ok q1 =>
  obtain ⟨r, m₁⟩ := q1
  rw [h1, applyIndE.k_ind_fields.arm1] at he
  obtain ⟨s1, hs1, -, hW1⟩ :=
    triple_of_callE (indFields_spec p hFI b.data hsize n ⟨m, Locals.init []⟩ hm v.toUInt64) h1
  rw [hs1] at hW1
  have hifs := hD.ifs
  obtain ⟨to, tn, co, cn, ro, rn, rfl, hF, hfR⟩ :=
    indFields_link b h64 hsize m m₁ ⟨by omega, by omega⟩ v tys cts rcs e' hscan _ hW1
  have hfr1 : MemFrame [IFR, IFL] [] m m₁ := hfR.1
  have hRoom : Room m₁ := hfR.2
  simp only [List.headD, List.tail] at he
  cases h2 : callE p n "validate_ind_d" [to, tn, co, cn, ro, rn] m₁ with
  | error e2 =>
    rw [h2, applyIndE.k_validate_ind_d.none] at he; cases he
    have hA1 : ArenaD m₁ a :=
      ⟨ArenaR.frame_ext _ _ (by simp [IFR, IFL]) (by simp) _ _ hfr1 _ hA.1,
        DerR.frameT hfr1 (by simp [IFR, IFL]) hA.2⟩
    have hD1 : StateDR m₁ st := hD.frame hfr1 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hT1 : TopOK m₁ := ⟨by have := hRoom.2.1; exact this, Nat.le_of_lt hRoom.2.2.2⟩
    have hIFR1 : topN m₁ IFR < 2 ^ 62 := by have := hRoom.2.2.1; have := hD1.ifs; omega
    exact claimR_of_validate (hV b n m₁ a st to tn co cn ro rn tys cts rcs e hA1.1 hD1 hok hT1 hF hIFR1 hX h2)
  | ok q2 =>
  obtain ⟨r2, m₂⟩ := q2
  rw [h2, applyIndE.k_validate_ind_d.arm1] at he
  cases h3 : callE p n "install_ind_d" [to, tn, r2.headD 0, cn, ro, rn, r2.tail.headD 0] m₂ with
  | error e3 =>
    rw [h3, applyIndE.k_install_ind_d.none] at he; cases he
    exact absurd (hnv.cls (by simp) h3) hk
  | ok q3 =>
    obtain ⟨r3, m₃⟩ := q3
    rw [h3, applyIndE.k_install_ind_d.arm1] at he; cases he

end L.Front.Ind

namespace L.Front

open ConAgua.Front.FieldsLink ConAgua.Scan L.Front.Fields
open L.Scan.Line (scanLineLoop lineFwdN)
open ConAgua.Scan.RecordsLink ConAgua.Scan.LineLink
open L.Scan.Leaves (skipWsN)

/-- The scanner's `safety` converse on the declaration lines of `b` (`DeclSafeR`, which
`apply_decl`'s claim takes): what `rec_decl_line` reads at a line con-leche's loop reads as a
declaration record. -/
def SafeLink (b : ByteArray) : Prop :=
  ∀ (j : USize) (r : LineRec) (e : USize) (d : DeclRec),
    scanLineLoop b j true 0 0 .absent = .ok r e → r = .decl d → DeclSafeR d (declLineN b.data j.toUInt64)

/-- **`apply_dline`'s error model claims the line's verdict**: the record is con-leche's
(`declLine_link`); an inductive block is `apply_ind`'s claim, any other declaration
`apply_decl`'s (`applyDecl_refinesE`). -/
theorem applyDLineE_claim (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p) (hDL : DeclLookups p)
    (hF : DeclFieldLookups p) (hXI : L.Front.Ind.IndLineLookups p)
    {X : StateD → AState → Prop} (hV : L.Front.Ind.ValidateClaim p X)
    (hnv : NVCls p ["ind_fields", "install_ind_d", "rec_decl_line"]) (hnvD : ApplyDeclNV p)
    {b : ByteArray} (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (hSL : SafeLink b)
    {m : Mem} {a : AState} {st : StateD} (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) (hX : X st a)
    (j : USize) (r : LineRec) (e' : USize) (hloop : scanLineLoop b j true 0 0 .absent = .ok r e') (n : Nat) :
    ∀ e, applyDLineE p n m j.toUInt64 = .error e → VerdictClaimR (applyLine st r) a e := by
  intro e he hk
  cases n with
  | zero => simp only [applyDLineE] at he; cases he; exact absurd rfl hk
  | succ n =>
  simp only [applyDLineE] at he
  cases h1 : callE p n "rec_decl_line" [j.toUInt64] m with
  | error e1 =>
    rw [h1, applyDLineE.k_rec_decl_line.none] at he; cases he
    exact absurd (hnv.cls (by simp) h1) hk
  | ok q1 =>
  obtain ⟨r1, m₁⟩ := q1
  rw [h1] at he
  obtain ⟨s1, hs1, hsm, hr1⟩ :=
    triple_of_callE (recDeclLine_spec p hF b.data hsize n ⟨m, Locals.init []⟩ hm j.toUInt64) h1
  subst hr1
  have hm1 : m₁ = m := by rw [← hs1, hsm]
  rw [hm1] at he h1
  generalize hf : declLineN b.data j.toUInt64 = f at he
  by_cases h0 : f.pl = 0
  · rw [applyDLineE.k_rec_decl_line.abort1 _ _ _ _ (by simpa [DFld.enc] using h0)] at he
    cases he; exact absurd rfl hk
  have hX' : DRecR b r f := by
    rw [← hf]; exact declLine_link b h64 hsize j true 0 0 .absent DFld.none r e' hloop trivial
      (by show (declLineN b.data j.toUInt64).pl ≠ 0; rw [hf]; exact h0)
  rcases r with _ | _ | _ | d | _ | _ <;> simp only [DRecR] at hX'
  by_cases h25 : f.pl = 25
  · rw [applyDLineE.k_rec_decl_line.arm1 _ _ _ _ (by simpa [DFld.enc] using h0)
      (by simpa [DFld.enc] using h25)] at he
    cases h2 : callE p n "apply_ind" [(f.enc).tail.headD 0] m with
    | error e2 =>
      rw [h2, applyDLineE.k_apply_ind.none] at he; cases he
      cases d with
      | ind tys cts rcs =>
        obtain ⟨-, v, hv, e'', hscan⟩ := hX'
        have h2' : callE p n "apply_ind" [v.toUInt64] m = .error e := by
          rw [← hv]; simpa [DFld.enc] using h2
        exact L.Front.Ind.applyIndE_claim p hFI hV (fun g hg => hnv g (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hg ⊢; rcases hg with rfl | rfl <;> simp)) h64 hsize hm hA hD hok hX
          hscan n e (triple_of_callE_err (L.Front.Ind.applyInd_specE p hXI.apply_ind n ⟨m, Locals.init []⟩ _) h2'
            (Err.code_ne_of_cls hk)) hk
      | ax _ _ => exact absurd (hX'.1.symm.trans h25) (by decide)
      | defn _ _ _ _ => exact absurd (hX'.1.symm.trans h25) (by decide)
      | thm _ _ => exact absurd (hX'.1.symm.trans h25) (by decide)
      | opaq _ _ _ => exact absurd (hX'.1.symm.trans h25) (by decide)
      | quot _ _ => exact absurd (hX'.1.symm.trans h25) (by decide)
    | ok q2 => obtain ⟨_, _⟩ := q2; rw [h2, applyDLineE.k_apply_ind.arm1] at he; cases he
  · rw [applyDLineE.k_rec_decl_line.arm2 _ _ _ _ (by simpa [DFld.enc] using h0)
      (by simpa [DFld.enc] using h25)] at he
    cases h2 : callE p n "apply_decl" [f.pl, f.name, f.lps, f.type, f.value, f.hk, f.hn, f.flag] m with
    | error e2 =>
      simp only [DFld.enc, List.headD_cons, List.tail_cons] at he
      rw [h2, applyDLineE.k_apply_ind.none] at he; cases he
      have hS := hSL j (.decl d) e' d hloop rfl
      rw [hf] at hS
      exact applyDecl_refinesE p hDL hnvD b hsize m hm st a hD f d hX' hS n e h2 hk
    | ok q2 =>
      obtain ⟨_, _⟩ := q2
      simp only [DFld.enc, List.headD_cons, List.tail_cons] at he
      rw [h2, applyDLineE.k_apply_ind.arm1] at he; cases he

/-- **`apply_any`'s error model claims the line's verdict**: the fields passes leave the memory
alone, `apply_rec`/`apply_expr` claim nothing, the rest is `apply_dline`'s. -/
theorem applyAnyE_claim (p : Prog) (hS : ScanLookups p) (hFI : L.Front.Ind.IndFieldLookups p)
    (hDL : DeclLookups p) (hF : DeclFieldLookups p) (hXI : L.Front.Ind.IndLineLookups p)
    (hpz : p.lookup "apply_dline" = some applyDLine)
    {X : StateD → AState → Prop} (hV : L.Front.Ind.ValidateClaim p X)
    (hnv : NVCls p ["ind_fields", "install_ind_d", "rec_decl_line", "apply_rec", "apply_expr",
      "rec_line_loop", "rec_expr_loop"]) (hnvD : ApplyDeclNV p)
    {b : ByteArray} (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (hSL : SafeLink b)
    {m : Mem} {a : AState} {st : StateD} (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) (hX : X st a)
    (j : USize) (r : LineRec) (e' : USize) (hloop : scanLineLoop b j true 0 0 .absent = .ok r e') (n : Nat) :
    ∀ e, applyAnyE p n m j.toUInt64 = .error e → VerdictClaimR (applyLine st r) a e := by
  intro e he hk
  cases n with
  | zero => simp only [applyAnyE] at he; cases he; exact absurd rfl hk
  | succ n =>
  simp only [applyAnyE] at he
  cases h1 : callE p n "rec_line_loop" [j.toUInt64] m with
  | error e1 =>
    rw [h1, applyAnyE.k_rec_line_loop.none] at he; cases he
    exact absurd (hnv.cls (by simp) h1) hk
  | ok q1 =>
  obtain ⟨r1, m₁⟩ := q1
  rw [h1] at he
  obtain ⟨s1, hs1, hsm, -⟩ := triple_of_callE (L.Front.Fields.recLineLoop_spec p b.data hsize (hS.get "skip_ws") (hS.get "skip_digits") (hS.get "key_end") (hS.get "num_end") (hS.get "key_at_g1") (hS.get "key_at_g2") (hS.get "key_at_g3") (hS.get "key_at_g4") (hS.get "key_at_g5") (hS.get "key_at_g6") (hS.get "key_at") (hS.get "value_at") (hS.get "next_member") (hS.get "slot_nat") (hS.get "utf8_char") (hS.get "utf8_valid") (hS.get "byte_in") (hS.get "hex_val") (hS.get "hex4") (hS.get "hex3") (hS.get "u_next") (hS.get "unescape") (hS.get "str_close") (hS.get "has_escape") (hS.get "scan_string") (hS.get "skip_braced") (hS.get "read_nat") (hS.get "rec_nat_list") (hS.get "rec_str_name") (hS.get "rec_num_name") (hS.get "rec_line_loop") n ⟨m, Locals.init []⟩ hm j.toUInt64) h1
  have hm1 : m₁ = m := by rw [← hs1, hsm]
  rw [hm1] at he
  by_cases hp1 : r1.headD 0 = 0
  · rw [applyAnyE.k_rec_line_loop.arm2 _ _ _ _ _ hp1] at he
    cases h2 : callE p n "rec_expr_loop" [j.toUInt64] m with
    | error e2 =>
      rw [h2, applyAnyE.k_rec_expr_loop.none] at he; cases he
      exact absurd (hnv.cls (by simp) h2) hk
    | ok q2 =>
    obtain ⟨r2, m₂⟩ := q2
    rw [h2] at he
    obtain ⟨s2, hs2, hsm2, -⟩ := triple_of_callE (L.Front.Fields.recExprLoop_spec p b.data hsize (hS.get "skip_ws") (hS.get "skip_digits") (hS.get "key_end") (hS.get "num_end") (hS.get "key_at_g1") (hS.get "key_at_g2") (hS.get "key_at_g3") (hS.get "key_at_g4") (hS.get "key_at_g5") (hS.get "key_at_g6") (hS.get "key_at") (hS.get "value_at") (hS.get "next_member") (hS.get "slot_nat") (hS.get "scan_quoted_nat") (hS.get "match_word") (hS.get "scan_binder_info") (hS.get "scan_nat_list") (hS.get "match_lit") (hS.get "scan_bool") (hS.get "utf8_char") (hS.get "utf8_valid") (hS.get "byte_in") (hS.get "hex_val") (hS.get "hex4") (hS.get "hex3") (hS.get "u_next") (hS.get "unescape") (hS.get "str_close") (hS.get "has_escape") (hS.get "scan_string") (hS.get "read_nat") (hS.get "obj_val") (hS.get "rec_obj") (hS.get "expr_val") (hS.get "rec_expr_loop") n ⟨m, Locals.init []⟩ hm j.toUInt64) h2
    have hm2 : m₂ = m := by rw [← hs2, hsm2]
    rw [hm2] at he
    by_cases hp2 : r2.headD 0 = 0
    · rw [applyAnyE.k_rec_expr_loop.arm2 _ _ _ _ _ hp2] at he
      cases h3 : callE p n "apply_dline" [j.toUInt64] m with
      | error e3 =>
        rw [h3, applyAnyE.k_apply_rec.none] at he; cases he
        exact applyDLineE_claim p hFI hDL hF hXI hV
          (fun g hg => hnv g (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hg ⊢; rcases hg with rfl | rfl | rfl <;> simp))
          hnvD h64 hsize hSL hm hA hD hok hX j r e' hloop n e
          (triple_of_callE_err (applyDLine_specE p hpz n ⟨m, Locals.init []⟩ _) h3 (Err.code_ne_of_cls hk)) hk
      | ok q3 => obtain ⟨_, _⟩ := q3; rw [h3, applyAnyE.k_apply_rec.arm1] at he; cases he
    · rw [applyAnyE.k_rec_expr_loop.arm1 _ _ _ _ _ hp2] at he
      cases h3 : callE p n "apply_expr" _ m with
      | error e3 =>
        rw [h3, applyAnyE.k_apply_rec.none] at he; cases he
        exact absurd (hnv.cls (by simp) h3) hk
      | ok q3 => obtain ⟨_, _⟩ := q3; rw [h3, applyAnyE.k_apply_rec.arm1] at he; cases he
  · rw [applyAnyE.k_rec_line_loop.arm1 _ _ _ _ _ hp1] at he
    cases h3 : callE p n "apply_rec" _ m with
    | error e3 =>
      rw [h3, applyAnyE.k_apply_rec.none] at he; cases he
      exact absurd (hnv.cls (by simp) h3) hk
    | ok q3 => obtain ⟨_, _⟩ := q3; rw [h3, applyAnyE.k_apply_rec.arm1] at he; cases he

/-- **`front_line`'s error model claims the line's verdict**: a line that fails (class `≠ 0`)
scans (`scanLineFwd`, else `front_line` returns `(0, 0)`), and its record's `applyLine` fails or
gives a verdict of that class (`applyAnyE_claim`). -/
theorem frontLineE_claim (p : Prog) (hS : ScanLookups p) (hFI : L.Front.Ind.IndFieldLookups p)
    (hDL : DeclLookups p) (hF : DeclFieldLookups p) (hXI : L.Front.Ind.IndLineLookups p)
    (hpz : p.lookup "apply_dline" = some applyDLine) (hpy : p.lookup "apply_any" = some applyAny)
    {X : StateD → AState → Prop} (hV : L.Front.Ind.ValidateClaim p X)
    (hnv : NVCls p ["ind_fields", "install_ind_d", "rec_decl_line", "apply_rec", "apply_expr",
      "rec_line_loop", "rec_expr_loop", "scan_line", "skip_ws"]) (hnvD : ApplyDeclNV p)
    {b : ByteArray} (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (hSL : SafeLink b)
    {m : Mem} {a : AState} {st : StateD} (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) (hX : X st a)
    (i : USize) (hi : i.toNat ≤ b.size) (n : Nat) :
    ∀ e, frontLineE p n m i.toUInt64 = .error e → e.cls ≠ 0 →
      ∃ r q, scanLineFwd b i = .ok r q ∧ VerdictClaimR (applyLine st r) a e := by
  intro e he hk
  cases n with
  | zero => simp only [frontLineE] at he; cases he; exact absurd rfl hk
  | succ n =>
  simp only [frontLineE] at he
  have hi' : i.toUInt64.toNat ≤ b.data.size := by rw [USize.toNat_toUInt64]; exact hi
  cases h1 : callE p n "scan_line" [i.toUInt64] m with
  | error e1 =>
    rw [h1, frontLineE.k_scan_line.none] at he; cases he
    exact absurd (hnv.cls (by simp) h1) hk
  | ok q1 =>
  obtain ⟨r1, m₁⟩ := q1
  rw [h1] at he
  obtain ⟨s1, hs1, hsm, hr1⟩ := triple_of_callE (L.Scan.Line.scanLine_spec p b.data hsize (hS.get "skip_ws") (hS.get "skip_digits") (hS.get "key_end") (hS.get "num_end") (hS.get "key_at_g1") (hS.get "key_at_g2") (hS.get "key_at_g3") (hS.get "key_at_g4") (hS.get "key_at_g5") (hS.get "key_at_g6") (hS.get "key_at") (hS.get "value_at") (hS.get "next_member") (hS.get "slot_nat") (hS.get "match_word") (hS.get "scan_binder_info") (hS.get "hints_num") (hS.get "hints_obj") (hS.get "scan_hints") (hS.get "scan_nat_list") (hS.get "match_lit") (hS.get "scan_bool") (hS.get "utf8_char") (hS.get "utf8_valid") (hS.get "byte_in") (hS.get "hex_val") (hS.get "hex4") (hS.get "hex3") (hS.get "u_next") (hS.get "unescape") (hS.get "str_close") (hS.get "has_escape") (hS.get "scan_string") (hS.get "scan_str_name") (hS.get "scan_num_name") (hS.get "scan_app") (hS.get "scan_binder") (hS.get "scan_let") (hS.get "scan_const") (hS.get "scan_proj") (hS.get "scan_rule") (hS.get "scan_rules") (hS.get "scan_ind_rec") (hS.get "scan_ind_recs") (hS.get "scan_ind_type") (hS.get "scan_ind_types") (hS.get "scan_ind_ctor") (hS.get "scan_ind_ctors") (hS.get "scan_axiom") (hS.get "scan_def") (hS.get "scan_thm") (hS.get "scan_opaque") (hS.get "scan_quot") (hS.get "scan_ind_decl") (hS.get "skip_braced") (hS.get "scan_quoted_nat") (hS.get "scan_line_loop") (hS.get "scan_line") (hS.get "validate") n ⟨m, Locals.init []⟩ hm i.toUInt64 hi') h1
  have hm1 : m₁ = m := by rw [← hs1, hsm]
  rw [hm1] at he
  subst hr1
  by_cases hok0 : (lineFwdN b.data i.toUInt64).1 = 0
  · rw [frontLineE.k_scan_line.arm1 _ _ _ _ _ (by simpa using hok0)] at he; cases he
  rw [frontLineE.k_scan_line.arm2 _ _ _ _ _ (by simpa using hok0)] at he
  cases h2 : callE p n "skip_ws" [i.toUInt64] m with
  | error e2 =>
    rw [h2, frontLineE.k_skip_ws.none] at he; cases he
    exact absurd (hnv.cls (by simp) h2) hk
  | ok q2 =>
  obtain ⟨r2, m₂⟩ := q2
  rw [h2] at he
  have hb64 : b.data.size < 2 ^ 64 := by have : b.data.size = b.size := rfl; omega
  obtain ⟨s2, hs2, hsm2, hr2⟩ := triple_of_callE (L.Scan.Leaves.skipWs_spec p (hS.get "skip_ws") b.data
    hb64 n ⟨m, Locals.init []⟩ hm i.toUInt64 hi') h2
  have hm2 : m₂ = m := by rw [← hs2, hsm2]
  rw [hm2] at he
  subst hr2
  by_cases hrec : UInt64.ofNat (skipWsN b.data i.toUInt64.toNat) < m.len8 IN ∧
      ((m.arr8 IN)[(UInt64.ofNat (skipWsN b.data i.toUInt64.toNat)).toNat]?.getD 0).toUInt64 = 123
  rotate_left
  · rw [frontLineE.k_skip_ws.arm1 _ _ _ [UInt64.ofNat (skipWsN b.data i.toUInt64.toNat)] m hrec] at he; cases he
  rw [frontLineE.k_skip_ws.arm2 _ _ _ [UInt64.ofNat (skipWsN b.data i.toUInt64.toNat)] m hrec] at he
  simp only [List.headD_cons, List.tail_cons] at he
  cases h3 : callE p n "apply_any" [UInt64.ofNat (skipWsN b.data i.toUInt64.toNat) + 1] m with
  | ok q3 => obtain ⟨_, _⟩ := q3; rw [h3, frontLineE.k_apply_any.arm1] at he; cases he
  | error e3 =>
  rw [h3, frontLineE.k_apply_any.none] at he; cases he
  -- the twin's scan of the line
  have hL := lineFwd_link b h64 hsize i
  have hs := ConAgua.Scan.skipWs_toUInt64_eq b h64 (by omega) i
  obtain ⟨r, q, hsc⟩ : ∃ r q, scanLineFwd b i = .ok r q := by
    revert hL hok0
    cases scanLineFwd b i with
    | ok r q => intro _ _; exact ⟨r, q, rfl⟩
    | err e => intro hok hL; rw [← hL] at hok; exact absurd rfl hok
  refine ⟨r, q, hsc, ?_⟩
  rw [USize.toNat_toUInt64, ← hs] at hrec h3
  have hsc' := hsc
  unfold scanLineFwd at hsc'
  dsimp only at hsc'
  generalize hsw : skipWs b i = s at hsc' hrec h3
  obtain ⟨hslt, hs123⟩ := hrec
  have hslt' : s.toUInt64 < UInt64.ofNat b.data.size := by rw [← hm]; exact hslt
  have hsU : s < b.usize := (lt_usize_iff b h64 hsize s).mpr hslt'
  have hb123 : byteAt b s = 123 := by
    have : L.Scan.Utf8.byteW b.data s.toUInt64 = 123 := by
      rw [← hm]; simpa [L.Scan.Utf8.byteW, Array.getD_eq_getD_getElem?] using hs123
    rw [byteW_eq b h64 hsize] at this; exact (u8_toUInt64_eq _ 123 (by decide)).mp this
  simp only [hb123, show ((123 : UInt8) == 10) = false by decide, Bool.false_eq_true, ite_false,
    show (b.usize ≤ s) = False from propext ⟨fun h' => absurd hsU (USize.not_lt.mpr h'), False.elim⟩,
    show ((123 : UInt8) != 123) = false by decide] at hsc'
  split at hsc'
  · cases hsc'
  rename_i r' j hloop
  have hrr : r' = r := by
    split at hsc'
    · cases hsc'; rfl
    · split at hsc'
      · cases hsc'; rfl
      · cases hsc'
  subst hrr
  rw [← succ_toUInt64 b h64 hsize] at h3
  exact applyAnyE_claim p hS hFI hDL hF hXI hpz hV
    (fun g hg => hnv g (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hg ⊢; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    hnvD h64 hsize hSL hm hA hD hok hX (s + 1) r' j hloop n e
    (triple_of_callE_err (applyAny_specE p hpy n ⟨m, Locals.init []⟩ _) h3 (Err.code_ne_of_cls hk))

end L.Front

namespace L.Front

/-! ## The driver: a failing line ends the twin's parse -/

/-- **A line whose `applyLine` fails or gives a verdict of class `c` ends `finishFrom` so**
(through `feedChunk`, or `applyFinalLine` for a last line without a newline). -/
theorem finishFrom_fail (st : StateD) (b : ByteArray) (i : USize) (lineNo : Nat) (a : AState)
    (r : LineRec) (q : USize) (hi : i < b.usize) (hs : scanLineFwd b i = .ok r q) (c : Word)
    (h : (∃ ce, (applyLine st r).run a = .error ce ∧ twinCls ce = c) ∨
      ∃ v a', (applyLine st r).run a = .ok (.inr v, a') ∧ twinCls v.toError = c) :
    TwinFailsV (finishFrom st b i lineNo) a c := by
  have hi' : i < USize.ofNat b.size := hi
  by_cases hq : q = 0
  · subst hq
    rcases h with ⟨ce, hce, hc⟩ | ⟨v, a', hv, hc⟩
    · refine .inl ⟨ce, ?_, hc⟩
      unfold finishFrom
      rw [feedChunk, dif_pos hi]
      simp [hs, hi', applyFinalLine, StateT.run_bind, hce]
      rfl
    · refine .inr ⟨v.toError, lineNo + 1, a', ?_, hc⟩
      unfold finishFrom
      rw [feedChunk, dif_pos hi]
      simp [hs, hi', applyFinalLine, StateT.run_bind, hv]
      rfl
  · rcases h with ⟨ce, hce, hc⟩ | ⟨v, a', hv, hc⟩
    · refine .inl ⟨ce, ?_, hc⟩
      unfold finishFrom
      rw [feedChunk, dif_pos hi]
      simp [hs, hq, StateT.run_bind, hce]
      rfl
    · refine .inr ⟨v.toError, lineNo + 1, a', ?_, hc⟩
      unfold finishFrom
      rw [feedChunk, dif_pos hi]
      simp [hs, hq, StateT.run_bind, hv]
      rfl

/-- A claim at the prefixed parse state is one at the twin's own (`applyLine_pre_run`). -/
theorem claimR_of_pre (D : Array IDeclaration) {st : StateD} {r : LineRec} {a : AState} {e : Err}
    (h : VerdictClaimR (applyLine (st.pre D) r) a e) : VerdictClaimR (applyLine st r) a e := by
  intro hk
  rcases h hk with ⟨ce, hce, hc⟩ | ⟨v, a', hv, hc⟩
  · refine .inl ⟨ce, ?_, hc⟩
    rw [applyLine_pre_run] at hce
    cases hr : (applyLine st r).run a with
    | error e' => rw [hr] at hce; cases hce; rfl
    | ok x => rw [hr] at hce; cases hce
  · rw [applyLine_pre_run] at hv
    cases hr : (applyLine st r).run a with
    | error e' => rw [hr] at hv; cases hv
    | ok x =>
      obtain ⟨y, a''⟩ := x
      rw [hr] at hv
      cases y with
      | inl s => exfalso; simp [preL, Except.map] at hv
      | inr w =>
        simp [preL, Except.map] at hv
        obtain ⟨rfl, rfl⟩ := hv
        exact .inr ⟨w, a'', rfl, hc⟩

end L.Front

namespace L.Front

/-! ## At the frontend's program -/

/-- A call into the frontend runs in `frontAllProg` as in `checkerProg`. -/
theorem callE_frontAll {g : FnName} (hg : L.Checker.inFront g = true) (n : Nat) (args : List Word)
    (m : Mem) : callE frontAllProg n g args m = callE L.Checker.checkerProg n g args m := by
  unfold callE
  rw [L.Checker.invoke_exec_agree (P := L.Checker.inFront)
    (fun f hf => L.Checker.checkerProg_frontAgree f ((L.Checker.inFront_iff f).1 hf))
    L.Checker.checkerProg_frontClosed n hg]

theorem NVCls.mono {p : Prog} {fs gs : List FnName} (h : NVCls p fs) (hs : ∀ g ∈ gs, g ∈ fs) :
    NVCls p gs := fun g hg => h g (hs g hg)

/-- The frontend's callees outside the verdict closure. -/
def frontNV : List FnName := ["ind_fields", "install_ind_d", "rec_decl_line", "apply_rec",
  "apply_expr", "rec_line_loop", "rec_expr_loop", "scan_line", "skip_ws", "front_init", "decl_cv",
  "expr_get", "decl_push"]

theorem frontNV_nv : ∀ f ∈ frontNV, f ∈ L.Checker.nvFns := by decide +kernel

theorem frontNV_front : ∀ f ∈ frontNV, L.Checker.inFront f = true := by decide

/-- **The frontend's callees outside the closure claim nothing in `frontAllProg`.** -/
theorem frontAll_nvcls : NVCls frontAllProg frontNV := by
  intro g hg n args m e h
  rw [callE_frontAll (frontNV_front g hg)] at h
  exact callE_nv L.Checker.checkerProg_nv (frontNV_nv g hg) n args m h

theorem frontAll_nvD : ApplyDeclNV frontAllProg := by
  intro f hf n args m e h
  refine frontAll_nvcls f ?_ n args m e h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> decide

end L.Front

namespace L.Front

section loop
variable (D : Array IDeclaration) (b : ByteArray) (h64 : System.Platform.numBits = 64)
  (hsize : b.size < 2 ^ 63) {X : StateD → AState → Prop}
  (hV : L.Front.Ind.ValidateClaim frontAllProg X) (hXT : ∀ a st, TwinOK a st → X (st.pre D) a)
  (hSL : SafeLink b)
include h64 hsize hV hXT hSL

/-- One line's error claim at `frontAllProg`, under the driver's invariant. -/
theorem frontLineE_claim_all (n : Nat) (m : Mem) (a : AState) (st : StateD)
    (hI : FrontInvOK D b m a st) (i : USize) (hi : i.toNat ≤ b.size) (e : Err)
    (he : frontLineE frontAllProg n m i.toUInt64 = .error e) (hk : e.cls ≠ 0) :
    ∃ r q, scanLineFwd b i = .ok r q ∧ VerdictClaimR (applyLine st r) a e := by
  obtain ⟨⟨hm, hA, hD, hT, -⟩, -, -⟩ := hI
  obtain ⟨r, q, hs, hc⟩ := frontLineE_claim frontAllProg frontAllProg_scan frontAllProg_indFields
    frontAllProg_decl frontAllProg_dfields frontAllProg_indLine rfl rfl hV
    (frontAll_nvcls.mono (by decide))
    frontAll_nvD h64 hsize hSL hm hA hD hT.1 (hXT a st hT) i hi n e he hk
  exact ⟨r, q, hs, claimR_of_pre D hc⟩

omit h64 hsize hV hXT hSL in
theorem twinFailsV_of_run_eq {α β : Type} {T T' : AM (Except (ConRon.Arena.CheckError × α) β)}
    {a a' : AState} {c : Word} (h : T.run a = T'.run a') (h' : TwinFailsV T' a' c) : TwinFailsV T a c := by
  rcases h' with ⟨ce, hce, hc⟩ | ⟨ce, i, a'', hce, hc⟩
  · exact .inl ⟨ce, h.trans hce, hc⟩
  · exact .inr ⟨ce, i, a'', h.trans hce, hc⟩

/-- **The driver's loop**: a failing run (class `≠ 0`) from position `i`, under the driver's
invariant, ends the twin's `finishFrom` from `i` with that class: the lines before ran ok
(`lineKW_step_ok`, `finishFrom_next`), the failing one is `front_line`'s claim
(`finishFrom_fail`). -/
theorem loop1_claim : ∀ (n : Nat) (i : USize) (m : Mem) (ln : Word) (st : StateD) (a : AState)
    (lineNo : Nat) (e : Err), FrontInvOK D b m a st →
    frontRunE.loop1 frontAllProg n m i.toUInt64 ln = .error e → e.cls ≠ 0 →
    TwinFailsV (finishFrom st b i lineNo) a e.cls := by
  intro n
  induction n with
  | zero =>
    intro i m ln st a lineNo e _ he hk
    simp [frontRunE.loop1] at he
    subst he; exact absurd rfl hk
  | succ n ih =>
  intro i m ln st a lineNo e hI he hk
  have hm : m.arr8 IN = b.data := hI.1.1
  by_cases hlt : i.toUInt64 < m.len8 IN0
  rotate_left
  · rw [frontRunE.loop1.arm2 _ _ _ _ _ hlt] at he; cases he
  rw [frontRunE.loop1.arm1 _ _ _ _ _ hlt] at he
  have hlt' : i.toUInt64 < UInt64.ofNat b.data.size := by
    have : m.len8 IN0 = UInt64.ofNat b.data.size := by
      show UInt64.ofNat (m.arr8 IN).size = _; rw [hm]
    rw [← this]; exact hlt
  have hi : i < b.usize := (ConAgua.Scan.RecordsLink.lt_usize_iff b h64 hsize i).mpr hlt'
  have hiN : i.toNat ≤ b.size := by
    have := ConLeche.Frontend.usizeInBounds b i hi; omega
  cases h1 : callE frontAllProg n "front_line" [i.toUInt64] m with
  | error e1 =>
    rw [h1, frontRunE.k_front_line.none] at he; cases he
    have hE := triple_of_callE_err (frontLine_specE frontAllProg rfl n ⟨m, Locals.init []⟩ _) h1
      (Err.code_ne_of_cls hk)
    obtain ⟨r, q, hs, hc⟩ := frontLineE_claim_all D b h64 hsize hV hXT hSL n m a st hI i hiN e hE hk
    exact finishFrom_fail st b i lineNo a r q hi hs e.cls (hc hk)
  | ok q1 =>
  obtain ⟨r1, m₁⟩ := q1
  rw [h1] at he
  have hK := triple_of_callE (frontLineK_spec frontAllProg frontAllProg_scan frontAllProg_front rfl
      rfl rfl rfl rfl rfl rfl frontAllProg_expr rfl frontAllProg_dfields frontAllProg_decl rfl
      b.data hsize (fun m => ∃ a st, FrontInvOK D b m a st)
      (fun m ⟨_, _, hI⟩ => ⟨hI.1.2.1.1.lit.1.2.2.1, hI.1.2.1.1.lit.1.2.2.2.1⟩)
      (inv_step frontAllProg (FrontInvOK D b) b h64 hsize
        (fun m m' i ok nx st a hI hi h hok => lineKW_step_ok D b h64 hsize frontAllProg
          frontAllProg_indFields frontAllProg_indApply frontAllProg_indInstall frontAllProg_indLine
          m m' i ok nx st a hI hi h hok)) n ⟨m, Locals.init []⟩ i.toUInt64 hm ⟨a, st, hI⟩ hlt') h1
  obtain ⟨s1, hs1, hK1, -, -, -⟩ := hK
  rw [hs1] at hK1
  by_cases h0 : r1.headD 0 = 0
  · rw [frontRunE.k_front_line.arm1 _ _ _ _ _ _ h0] at he; cases he
  by_cases hnx : r1.tail.headD 0 = 0
  · rw [frontRunE.k_front_line.arm2 _ _ _ _ _ _ h0 hnx] at he; cases he
  by_cases hle : r1.tail.headD 0 ≤ i.toUInt64
  · rw [frontRunE.k_front_line.arm3 _ _ _ _ _ _ h0 hnx hle] at he; cases he
  rw [frontRunE.k_front_line.arm4 _ _ _ _ _ _ h0 hnx hle] at he
  obtain ⟨r, q, st', hs, hq, hok', hres, hInv⟩ :=
    lineKW_step_ok D b h64 hsize frontAllProg frontAllProg_indFields frontAllProg_indApply
      frontAllProg_indInstall frontAllProg_indLine m m₁ i _ _ st a hI hi hK1 h0
  have hrun := AM.run_of_ok _ _ hok'
  rw [hres] at hrun
  have hq0 : q ≠ 0 := by
    intro h0'; apply hnx; rw [← hq, h0']; rfl
  have hx : i.toUInt64 < r1.tail.headD 0 := UInt64.not_le.mp hle
  have hiq : i < q := by
    rw [ConAgua.Scan.lt_toUInt64_iff, hq]; exact hx
  refine twinFailsV_of_run_eq (finishFrom_next st b i lineNo a r q st' _ hi hs hq0 hiq hrun) ?_
  rw [← hq] at he
  exact ih q m₁ (ln + 1) st' _ (lineNo + 1) e hInv he hk

end loop

end L.Front
