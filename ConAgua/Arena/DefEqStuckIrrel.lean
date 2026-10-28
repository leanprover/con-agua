import ConAgua.Arena.DefEqStuckUnit

/-!
# `stuck_irrel` refines `stuckIrrel` (lane `defeq`, helper `defeq-top`)

Structural η both ways, unit-likeness, then proof irrelevance.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- One `if ← c then pure true else k` step: a `true` verdict answers `1`. -/
theorem coreRef_true {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word} {m' : Mem}
    (hS : CoreS dn m a vis fe M eb) (hW : some ((1 : Word), m) = some (r.headD 0, m')) :
    CoreRef (pure true : AM Bool) a decBool dn m vis fe M eb r m' := by
  obtain ⟨hr, hm⟩ := some_pair_inj hW
  rw [← hm]
  exact coreRef_pure hS rfl (decBool_true_of (by rw [← hr]; decide)).symm
    (by unfold ResH; rw [← hr]; exact hw1)

/-- **What the stuck side's errors claim from**: the knot's slots, `proof_irrel`'s claim and
`defeq_lst`'s (through `struct_eta_cert`, `SetG`). -/
structure StuckG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  pirr : ProofIrrelWE p
  lst : DefeqLstWE p

theorem StuckG.mono {p : Prog} {n n' : Nat} (h : StuckG p n) (hn : n' ≤ n) : StuckG p n' :=
  ⟨h.knot.mono hn, h.pirr, h.lst⟩

theorem StuckG.set {p : Prog} {n : Nat} (h : StuckG p n) : SetG p n := ⟨h.knot, h.lst⟩

/-- **`stuck_irrel`'s model, both outcomes** (generated; `struct_eta_cert` and `struct_unit_cert`
by their unified models, `proof_irrel` through its run). -/
l_model siE_spec (p : Prog) (hf : p.lookup "stuck_irrel" = some stuckIrrelL)
    (hc : p.lookup "struct_eta_cert" = some structEtaCertL)
    (hw : p.lookup "struct_eta_cert_with" = some structEtaCertWithL)
    (hb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
    (hg : p.lookup "struct_eta_cert_go" = some structEtaCertGoL)
    (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
    (hu : p.lookup "struct_unit_cert" = some structUnitCertL)
    (hh : p.lookup "struct_unit_head" = some structUnitHeadL)
    (hut : p.lookup "struct_unit_tail" = some structUnitTailL)
  fns [hf ↦ siE list]
  specs [secE_spec p hc hw hb hg ht n, sucE_spec p hu hh hut n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`stuck_irrel` refines `stuckIrrel`, both outcomes**: structural η both ways, unit-likeness,
then proof irrelevance; the errors are theirs. -/
theorem si_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (StuckG p n) (siE p (n + 1) s₀.mem mode vis d a b)
      (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  unfold stuckIrrel
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ k =>
  simp only [siE]
  have H := sec_ref p hq hi hc k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b (by omega)
    (by omega) hs ha hb
  rcases h1 : secE p (k + 1) s₀.mem mode vis d a b with e | ⟨r₁, m₁⟩
  · rw [h1] at H; exact fun hG => ErrClaim.bind_left (H (hG.set.mono (by omega)))
  rw [h1] at H
  obtain ⟨y, a', hrun, hP⟩ := H
  simp only [siE.k_struct_eta_cert]
  refine RefE.bind_core (w := id) (hP.coreRef hrun) (fun M₁ hS₁ _ => ?_)
  by_cases g1 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left g1, decBool_true_of g1]; exact RefE.ret rfl (CorePost.ret hS₁ rfl hw1)
  rw [ite_eq_right g1, decBool_false_of (by simpa using g1)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have H := sec_ref p hq hi hc k (hk.mono (by omega)) F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
    b a (by omega) (by omega) ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb ha
  rcases h2 : secE p (k + 1) m₁ mode vis d b a with e | ⟨r₂, m₂⟩
  · rw [h2] at H; exact fun hG => ErrClaim.bind_left (H (hG.set.mono (by omega)))
  rw [h2] at H
  obtain ⟨y, a', hrun, hP⟩ := H
  simp only [siE.k_struct_eta_cert_2]
  refine RefE.bind_core (w := id) (hP.coreRef hrun) (fun M₂ hS₂ _ => ?_)
  by_cases g2 : r₂.headD 0 ≠ 0
  · rw [ite_eq_left g2, decBool_true_of g2]; exact RefE.ret rfl (CorePost.ret hS₂ rfl hw1)
  rw [ite_eq_right g2, decBool_false_of (by simpa using g2)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have H := suc_ref p hq hc k (hk.mono (by omega)) F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d
    a b (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb
  rcases h3 : sucE p (k + 1) m₂ mode vis d a b with e | ⟨r₃, m₃⟩
  · rw [h3] at H; exact fun hG => ErrClaim.bind_left (H (hG.knot.mono (by omega)))
  rw [h3] at H
  obtain ⟨y, a', hrun, hP⟩ := H
  simp only [siE.k_struct_unit_cert]
  refine RefE.bind_core (w := id) (hP.coreRef hrun) (fun M₃ hS₃ _ => ?_)
  by_cases g3 : r₃.headD 0 ≠ 0
  · rw [ite_eq_left g3, decBool_true_of g3]; exact RefE.ret rfl (CorePost.ret hS₃ rfl hw1)
  rw [ite_eq_right g3, decBool_false_of (by simpa using g3)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases c4 : callE p (k + 1) "proof_irrel" [mode, vis, d, a, b] m₃ with e | ⟨r₄, m₄⟩
  · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
      (hG.pirr k (hk.mono (by omega)) (hG.knot.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe
        M₃ eb mode d a b hS₃ hs.mode4 hs.eb_mode ha hb) c4
  obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
    (proofIrrel_at p hc (k + 1) hk F hF hn _ _ dn vis fe M₃ eb mode d a b hS₃ hs.mode4 hs.eb_mode ha
      hb) (callW_of_callE c4)).post
  exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩

/-- **`stuck_irrel` refines `stuckIrrel`** at the knot (`si_ref`'s ok half). -/
@[refines ConRon.Arena.stuckIrrel]
theorem stuckIrrel_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "stuck_irrel" [mode, vis, d, a, b]
      (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (siE_spec p hq.stuckIrrel hq.setCert hq.setWith hq.setWtb hq.setGo hq.setTail hq.sunit
    hq.suHead hq.suTail (n + 1) s₀ mode vis d a b)
    (si_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
