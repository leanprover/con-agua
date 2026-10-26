import ConAgua.Verdict.FrontE
import ConAgua.Front.FrontPreOK

/-!
# Error refinements of the frontend's driver: `apply_ind`, `apply_dline`, `apply_any`,
`front_line`, `front_run` (lane `verdicts-b`, helper `f2`)
-/

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD processLineCoreD
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
open L.Scan.Line (scanLineLoop)

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

end L.Front
