module

public import ConAgua.Arena.DefEqStuckProj
public import ConAgua.Arena.DefEqStuckDisp
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
import all ConAgua.Arena.DefEq
import ConAgua.Arena.DefEqMid

@[expose] public section

/-!
# `defeq_tail` refines `defeqBody`'s tail (lane `defeq`, helper `defeq-top`)

`defeqBody` from the lazy-delta loop's `.unknown` pair on (`defeqTailT`): the projection pair,
the stuck comparison when neither head is a projection, else the full `whnfCore` of both sides
and a restart unless neither moved.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`defeqBody` past the lazy-delta loop's `.unknown a₁ b₁`**, copied. -/
def defeqTailT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a₁ b₁ : EIdx) :
    AM Bool := do
  if ← defeqProjPair mode r fe depth a₁ b₁ then pure true else do
  let pa ← headIsProj a₁
  let pb ← headIsProj b₁
  if !pa && !pb then defeqStuck mode r fe depth a₁ b₁ else do
  let a₂ ← r.whnfCore false depth a₁
  let b₂ ← r.whnfCore false depth b₁
  if a₂ == a₁ && b₂ == b₁ then defeqStuck mode r fe depth a₁ b₁
  else r.defeq depth a₂ b₂

/-! ## Leaves at any fuel -/

theorem headIsProj_at (p : Prog) (hq : StuckProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
      (fe : IFEnv) (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
      CoreSpec p n "head_is_proj" [e] (headIsProj (decE e)) decBool s₀ a₀ dn vis fe MM eb
  | 0, s₀, a₀, dn, vis, fe, MM, eb, _, _, _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | n + 1, s₀, a₀, dn, vis, fe, MM, eb, e, hS, he =>
      headIsProj_refines p hq.leaf n s₀ a₀ dn vis fe MM eb e hS he

/-! ## The model -/

/-- **`defeq_tail`'s model, both outcomes** (generated; `head_is_proj` lifted, `defeq_proj_pair` and
`defeq_stuck` by their unified models, the slots through their runs). -/
l_model dtE_spec (p : Prog) (hf : p.lookup "defeq_tail" = some defeqTailL)
    (hpp : p.lookup "defeq_proj_pair" = some defeqProjPairL)
    (hl : p.lookup "lazy_delta_proj_reduction" = some lazyDeltaProjReductionL)
    (hds : p.lookup "defeq_stuck" = some defeqStuckL)
    (hstr : p.lookup "stuck_str" = some stuckStrL) (hsa : p.lookup "stuck_app" = some stuckAppL)
    (hac : p.lookup "stuck_app_cong" = some stuckAppCongL) (hdr : p.lookup "stuck_rest" = some stuckRestL)
    (hi : p.lookup "stuck_irrel" = some stuckIrrelL)
    (hc : p.lookup "struct_eta_cert" = some structEtaCertL)
    (hw : p.lookup "struct_eta_cert_with" = some structEtaCertWithL)
    (hb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
    (hg : p.lookup "struct_eta_cert_go" = some structEtaCertGoL)
    (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
    (hu : p.lookup "struct_unit_cert" = some structUnitCertL)
    (hh : p.lookup "struct_unit_head" = some structUnitHeadL)
    (hut : p.lookup "struct_unit_tail" = some structUnitTailL)
    (he : p.lookup "eta_cert" = some etaCertL)
    (heb : p.lookup "eta_cert_body" = some etaCertBodyL) (het : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ dtE list]
  specs [callW_spec p n "head_is_proj", ppE_spec p hpp hl n,
    dsE_spec p hds hstr hsa hac hdr hi hc hw hb hg ht hu hh hut he heb het n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **What `defeq_tail`'s errors claim from**: the projection pair's (`LdprG`) and the stuck
side's (`StuckG`). -/
structure TailG (p : Prog) (n : Nat) : Prop extends LdprG p n where
  pirr : ProofIrrelWE p
  lst : DefeqLstWE p

theorem TailG.mono {p : Prog} {n n' : Nat} (h : TailG p n) (hn : n' ≤ n) : TailG p n' :=
  ⟨h.toLdprG.mono hn, h.pirr, h.lst⟩

theorem TailG.stuck {p : Prog} {n : Nat} (h : TailG p n) : StuckG p n := ⟨h.knot, h.pirr, h.lst⟩

/-- **`defeq_tail` refines `defeqTailT` (`defeqBody` past the lazy-delta loop), both outcomes**: the
errors are the projection pair's, the stuck side's and the slots'. -/
theorem dt_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a1 b1 : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a1) (hb : HW b1) (hd : d.toNat < 2 ^ 63) :
    RefE (TailG p n) (dtE p (n + 1) s₀.mem mode vis d a1 b1)
      (defeqTailT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a1) (decE b1)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  unfold defeqTailT
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ k =>
  -- `defeq_stuck` from any state related at `m`
  have hstk : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      RefE (TailG p (k + 1)) (dtE.k_defeq_stuck p (dsE p (k + 1) m mode vis d a1 b1))
        (defeqStuck (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a1) (decE b1)) st
        (CorePost decBool dn m vis fe M' eb ResH) := fun st m M' hS' =>
    RefE.tail_relist1 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.stuck.mono (by omega))
      (ds_ref p hq hi hc k (hk.mono (by omega)) F ⟨m, Locals.init []⟩ st dn vis fe M' eb mode d a1 b1
        (by omega) (by omega) ⟨hS', hs.mode4, hs.eb_mode⟩ ha hb)
  simp only [dtE]
  refine RefE.bind_coreE (w := id) (fun _ => rfl) (fun hG => hG.toLdprG.mono (by omega))
    (pp_ref p hq hc k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a1 b1 (by omega)
      (by omega) hs ha hb hd)
    (fun r₁ m₁ _ _ M₁ hS₁ _ => ?_)
  dsimp only [dtE.k_defeq_proj_pair]
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left h0, L.Arena.decBool_true_of h0]; exact RefE.ret rfl (CorePost.ret hS₁ rfl hw1)
  rw [ite_eq_right h0, L.Arena.decBool_false_of (by simpa using h0)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine RefE.bind_callW (fun _ => rfl) (headIsProj_at p hq (k + 1) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb a1
    hS₁ ha) fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [dtE.k_head_is_proj]
  refine RefE.bind_callW (fun _ => rfl) (headIsProj_at p hq (k + 1) ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb b1
    hS₂ hb) fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [dtE.k_head_is_proj_2]
  have hpp : (!decBool r₂ && !decBool r₃) = decide (r₂.headD 0 = 0 ∧ r₃.headD 0 = 0) := by
    unfold decBool
    generalize r₂.headD 0 = u
    generalize r₃.headD 0 = v
    by_cases x : u = 0 <;> by_cases y : v = 0 <;> simp [x, y]
  rw [hpp]
  by_cases hp0 : r₂.headD 0 = 0 ∧ r₃.headD 0 = 0
  · rw [ite_eq_left hp0]
    simp only [hp0, and_self, decide_true, ↓reduceIte]
    exact hstk _ m₃ M₃ hS₃
  rw [ite_eq_right hp0]
  simp only [hp0, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hs₃ : SlotPre ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hS₃, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl)
    ((hk (k + 1) (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₃ eb mode 0 d a1 hF hn hs₃ ha)
    (fun (hG : TailG p (k + 1)) => (hG.knot (k + 1) (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₃ eb mode
        0 d a1 hF hn hs₃ ha)
    fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  dsimp only [dtE.k_whnf_core]
  have hs₄ : SlotPre ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode := ⟨hS₄, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl)
    ((hk (k + 1) (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₄ eb mode 0 d b1 hF hn hs₄ hb)
    (fun (hG : TailG p (k + 1)) => (hG.knot (k + 1) (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₄ eb mode
        0 d b1 hF hn hs₄ hb)
    fun r₅ m₅ _ h₅ => RefE.after_core (w := id) h₅ fun M₅ hS₅ _ => ?_
  dsimp only [dtE.k_whnf_core_2]
  have heq : (decH r₄ == decE a1 && decH r₅ == decE b1) =
      decide (r₄.headD 0 = a1 ∧ r₅.headD 0 = b1) := by
    simp only [decH, L.Arena.decE_beq_eq _ _ h₄.resOk ha, L.Arena.decE_beq_eq _ _ h₅.resOk hb, Bool.decide_and]
  rw [heq]
  by_cases hm : r₄.headD 0 = a1 ∧ r₅.headD 0 = b1
  · rw [ite_eq_left hm]
    simp only [hm, and_self, decide_true, ↓reduceIte]
    exact hstk _ m₅ M₅ hS₅
  rw [ite_eq_right hm]
  simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hs₅ : SlotPre ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode := ⟨hS₅, hs.mode4, hs.eb_mode⟩
  rw [← bind_pure ((coreKnot (decMode mode) (decEager mode) fe id F).defeq _ _ _)]
  exact RefE.bind_callE (fun _ => rfl)
    ((hk (k + 1) (Nat.le_refl _)).defeq F _ _ dn vis fe M₅ eb mode d _ _ hF hn hs₅ h₄.resOk h₅.resOk)
    (fun (hG : TailG p (k + 1)) => (hG.knot (k + 1) (Nat.le_refl _)).defeq F _ _ dn vis fe M₅ eb mode d _
        _ hF hn hs₅ h₄.resOk h₅.resOk)
    fun _ _ _ h => RefE.ret rfl ⟨h.after, rfl, h.resOk⟩

/-- **`defeq_tail` refines `defeqTailT`** (`defeqBody` past the lazy-delta loop) at the knot
(`dt_ref`'s ok half). -/
@[refines_part ConRon.Arena.defeqBody "past the lazy-delta loop (defeqTailT)"]
theorem defeqTail_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a1 b1 : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a1) (hb : HW b1) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "defeq_tail" [mode, vis, d, a1, b1]
      (defeqTailT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a1) (decE b1))
      decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (dtE_spec p hq.defeqTail hq.projPair hq.ldpr hq.defeqStuck hq.stuckStr hq.stuckApp
    hq.stuckAppCong hq.stuckRest hq.stuckIrrel hq.setCert hq.setWith hq.setWtb hq.setGo hq.setTail
    hq.sunit hq.suHead hq.suTail hq.etaCert hq.etaCertBody hq.etaCertTy (n + 1) s₀ mode vis d a1 b1)
    (dt_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a1 b1 hF hn hs ha hb hd)

end L.Arena
