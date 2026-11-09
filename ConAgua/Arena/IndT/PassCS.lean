module

public import ConAgua.Arena.IndT.Pass
public import ConAgua.Arena.IndT.Install4
public import ConAgua.Arena.IndT.Install7
import ConAgua.Verdict.IndBSum4
import ConAgua.Arena.IndInstallSpec.ShapeCVOfDecB
import ConAgua.Arena.CrOKFrame
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.RecGenSpec.ClassSeeds
public import ConAgua.Arena.IndT.ArmMemos
public import ConAgua.Arena.IndInstallSpec.OfClosed
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.RefWalk

@[expose] public section

/-!
# `check_block_pass`'s callees' contracts from their refinements (lane `ronsync2`, stage 3)

`indsRefS_of` (`check_block_inds`: `IndT/Install4`'s `cbi_ref`), `ctorsRefS_of`
(`check_block_ctors`: `IndT/Install7`'s `ict_ref`, `check_sum_ctors` by `sctsRefS_of`, the verdict
area's `scts_refC`); the memos across both by `callW_indMemos` (both are in `imFns`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section
variable {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- **A call's refinement, its post weakened with the call's ok result at hand.** -/
theorem RefE.callOk {β : Type} {G : Prop} {x : Except Err (List Word × Mem)} {T : AM β} {a : AState}
    {R R' : List Word × Mem → β → AState → Prop} (h : RefE G x T a R)
    (hR : ∀ rm y a', x = .ok rm → R rm y a' → R' rm y a') : RefE G x T a R' := by
  cases x with
  | error e => exact h
  | ok v => obtain ⟨y, a', h1, h2⟩ := h; exact ⟨y, a', h1, hR _ _ _ rfl h2⟩

/-- **`check_sum_ctors`' contract** (`SctsRefS`): the verdict area's `scts_refC`. -/
theorem sctsRefS_of (hq : KnotStageProg p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
    (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hApd : ApdF p) (hCrk : CrKeep p)
    (hP : SumProg p) (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn) :
    SctsRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env env₀ m a T lo ll nP nIdx rs isP lg cvq cO cL lps cvTa cs TP lpsP rsP cvTaP csP
    hC henv hA hT hrs hlps hlb hta hcs hTP hlpsP hrsP hcvTaP hfv hcsP hok₀
  exact scts_refC hq henv hOpf hLC hLT hApd hCrk hP hV hcr hCS n hn m a T lo ll nP nIdx rs isP lg cvq
    cO cL lps cvTa cs TP lpsP rsP cvTaP csP hC hA hT hrs hlps hlb hta hcs hTP hlpsP hrsP hcvTaP hfv
    hcsP hok₀

/-- **`check_block_inds`' contract** (`IndsRefS`): `cbi_ref` through the call; the memos by
`callW_indMemos`. -/
theorem indsRefS_of (hq : KnotStageProg p) (hV : CcvProg p) (hcr : CrfF p) (hCS : CcvSims p dn)
    (hOpf : OpfF p) (hLC : LvlCacheProg p) (hApd : ApdF p) (hCrk : CrKeep p) (hP : IndsProg p)
    (hk : ∀ f ∈ indsKeepCalleesC, AbsKeep p f) (hl : IndLeaves p) :
    IndsRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env m a pp isRec bs bsP b hB henv hqd hsl hdP hb
  rcases n with _ | n
  · obtain ⟨e, he, h0⟩ := L.callE_zero p "check_block_inds" [vis, pp, isRec] m
    rw [he]; exact RefE.of_cls0 h0
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (cbiE_spec p hP (n + 1) _ vis pp isRec)
    (fun hG => hG.nv)
    (cbi_ref hq henv hV hcr hCS hOpf hLC hApd hCrk hP n (by omega) hB.c hqd hsl.1 (shapeCV_of_decB hqd)
      hb hB.abs hk hdP)
  refine RefE.callOk h fun ⟨r, m'⟩ x a' hc hR => ?_
  obtain ⟨s', hs', -, hR⟩ := hR
  simp only at hs'; subst hs'
  exact ⟨hR.out, callW_indMemos hCrk.closed hl (im_mem _ rfl) (callW_of_callE hc) hB.ind, hR.abs,
    hR.out.2.2.2, hR.recs hsl.2⟩

/-- **`check_block_ctors`' contract** (`CtorsRefS`): `ict_ref` through the call, `check_sum_ctors`
by its contract; the memos by `callW_indMemos`. -/
theorem ctorsRefS_of (hP : CtorsProg p) (hR : SctsRefS (VerdictCtxU p) p dn) (hCrk : CrKeep p)
    (hl : IndLeaves p) : CtorsRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env env₀ m a pp bs bsP hB henv hqd hsl hdP hws hok₀
  obtain ⟨hdm, hbm, -, -⟩ := bsAt hqd hsl
  obtain ⟨hms, -⟩ := ConRon.Bridge.Inductives.dShape_inv hdP
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩)
    (ictE_spec p hP n _ vis vis pp (rdW (m.arr64 IW) pp) (rdW (m.arr64 IW) (pp + 1))) (fun hG => hG.nv)
    (ict_ref hP hR henv pp bs n hn m a _ _ bs.members bsP.members hB.c hB.abs hqd hsl.1 ⟨hdm, hbm⟩
      hdP hms hws hok₀)
  refine RefE.callOk h fun ⟨r, m'⟩ x a' hc hR => ?_
  obtain ⟨s', hs', -, hR⟩ := hR
  simp only at hs'; subst hs'
  exact ⟨⟨hR.stage, callW_indMemos hCrk.closed hl (im_mem _ rfl) (callW_of_callE hc) hB.ind, hR.abs⟩,
    hR.grow⟩

/-! ## The memos across a callee writing the positivity memos -/

/-- **The walk memos outside the positivity check's** (`maMR`, `mcMR`, `taMR`) **kept by `f`**
(at the checker: `armMa`, `armMc`, `armTa`'s write sets). -/
structure WmKeep (p : Prog) (f : FnName) : Prop where
  ma : ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem), callW p n f vs m = some (r, m') →
    (∃ mp, maMR m mp) → ∃ mp, maMR m' mp
  mc : ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem), callW p n f vs m = some (r, m') →
    (∃ mp, mcMR m mp) → ∃ mp, mcMR m' mp
  ta : ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem), callW p n f vs m = some (r, m') →
    (∃ mp, taMR m mp) → ∃ mp, taMR m' mp

/-- **`IndMemos` across a call keeping the other walk memos**, the positivity memos and `AbsOK`
(its `I1Memo`, `CrOK`) after it given. -/
theorem IndMemos.ofCall {p : Prog} {f : FnName} (hK : WmKeep p f) {n : Nat} {vs : List Word} {m : Mem}
    {r : List Word} {m' : Mem} (h : callW p n f vs m = some (r, m')) (hI : IndMemos m) (hP : PosMR m')
    (hA : AbsOK m') : IndMemos m' :=
  ⟨⟨hP, hK.ma _ _ _ _ _ h hI.stage.ma, hK.mc _ _ _ _ _ h hI.stage.mc, hK.ta _ _ _ _ _ h hI.stage.ta⟩,
    hA.i1, hA.crMemo.crOK⟩

/-- **`class_seeds`' contract** (`SeedsRefS`): `classSeeds_refines` through the call (the twin
never fails); `AbsOK` by `AbsKeep`, the memos by `IndMemos.ofCall`. -/
theorem seedsRefS_of (hP : SdProg p) (hk : AbsKeep p "class_seeds") (hW : WmKeep p "class_seeds") :
    SeedsRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env m a ctx hO hL mo ml c holes ms hB hU hhi hho hhob hms
  refine RefE.onlyCall (K := id) (fun _ => rfl) (fun hG => hG.nv)
    (_root_.L.Checker.nv_mem (by decide +kernel)) fun r m' hc => ?_
  obtain ⟨s', hs', -, hok, hS', hg, hsd, hP'⟩ := triple_of_callW
    (classSeeds_refines hP n ⟨m, Locals.init []⟩ a dn vis fe ctx hO hL mo ml c holes ms hB.c.stage hU hhi hho
      hhob hms hB.ind.stage.pos) (callW_of_callE hc)
  subst hs'
  have hA' := hk _ _ _ _ _ (callW_of_callE hc) hB.abs
  exact ⟨_, _, AM.run_of_ok _ _ hok, hS', IndMemos.ofCall hW (callW_of_callE hc) hB.ind hP' hA', hA', hg, hsd⟩

end

end L.Ind

end
