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
