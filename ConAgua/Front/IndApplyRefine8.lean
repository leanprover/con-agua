module

public import ConAgua.Verdict.FrontOrderE
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
import all ConAgua.Front.IndApply

@[expose] public section

/-!
# The apply step of an `inductive` line against the twin, VIII: `vi_order`

`order_ref`: `vi_order` allocates the ordered slice above the pool's top and fills it, every
constructor checked as the twin checks it (`CtorOK`, per type `k` and position `c`), or stops at
the first constructor that fails the twin's checks (`OrderFailW`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true


namespace L.Front.Ind

theorem psum_congr {m m' : Mem} (h : m'.arr64 IFR = m.arr64 IFR) (to : Word) (i : Nat) :
    psum m' to i = psum m to i := by
  unfold psum
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [cntF, wd, h]

/-! ## The unified model -/

l_model viOrder_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_order ↦ viOrderE]
  specs [iflAlloc_spec p hL.ifl_alloc n, viOrderGo_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`vi_order`'s ok half**: the slice is allocated above the pool's top (`IExt`), `cts.length`
words, and every constructor of every type passes the twin's checks, its record's pointer at its
position in the slice. -/
structure OrderPost (st : StateD) (a : AState) (cts : List IndCtorRec) (m : Mem)
    (to tn tyn fo cno co np fuel : Word) (v : Word × Mem) : Prop where
  off : v.1.toNat = topN m IFL + 1
  ext : IExt m v.2
  top : TopOK v.2
  topN : topN v.2 IFL = topN m IFL + cts.length
  ctors : ∀ k, k < tn.toNat → ∀ c, c < cntF m to k →
    ∃ kk, wd v.2 IFL (v.1.toNat + psum m to k + c) = co + 10 * UInt64.ofNat kk ∧
      CtorOK st a cts (islice m cno.toNat cts.length) (decI (wd m IFL (fo.toNat + psum m to k + c)))
        c (decI (wd m IFL (tyn.toNat + k))) np.toNat fuel.toNat kk

/-- **`vi_order`'s error half**: an error of class `≠ 0` (with the type name handles below `2^32`)
is a reject (class `1`) and stops the twin's constructor order (`OrderFailW`). -/
def OrderErr (st : StateD) (a : AState) (cts : List IndCtorRec) (m : Mem)
    (to tn tyn fo cno np fuel : Word) (e : Err) : Prop :=
  (∀ k, k < tn.toNat → (wd m IFL (tyn.toNat + k)).toNat < 2 ^ 32) → e.cls ≠ 0 →
    e.cls = 1 ∧ OrderFailW st a cts m to tn tyn fo cno np.toNat fuel.toNat

/-- **`vi_order`, both outcomes.** -/
theorem order_ref {b : ByteArray} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {cts : List IndCtorRec}
    {to tn tyn fo cno co cn fuel np : Word} (hT : TopOK m)
    (hCt : ListF (CtF b m) m 10 co.toNat cts) (hcn : cn.toNat = cts.length)
    (hCN : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32)
    (hcnB : cno.toNat + cts.length ≤ topN m IFL + 1) (hnp : np.toNat < 10 ^ 18)
    (hco : co.toNat + 10 * cts.length < 2 ^ 63) (h1 : 1 ≤ cno.toNat ∧ 1 ≤ fo.toNat ∧ 1 ≤ tyn.toNat)
    (hto : to.toNat + 11 * tn.toNat < 2 ^ 63) (htyn : tyn.toNat + tn.toNat ≤ topN m IFL + 1)
    (hfo : ∀ p, p < psum m to tn.toNat → fo.toNat + p ≤ topN m IFL ∧ (wd m IFL (fo.toNat + p)).toNat < 2 ^ 32)
    (hps : psum m to tn.toNat ≤ cts.length) (p : Prog) (n : Nat) :
    RefC True (viOrderE p n m to tn tyn fo cno co cn fuel np)
      (OrderPost st a cts m to tn tyn fo cno co np fuel) (OrderErr st a cts m to tn tyn fo cno np fuel) := by
  obtain ⟨h1a, h1b, h1c⟩ := h1
  cases n with
  | zero => simp only [viOrderE, RefC_error]; exact fun _ _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  rw [viOrderE.arm1]
  rcases ha : allocW m IFL cn with _ | ⟨oo, m₁⟩
  · rw [liftE_none, viOrderE.k_ifl_alloc.none]; exact fun _ _ hk => absurd Err.cls_oob hk
  rw [liftE_some, viOrderE.k_ifl_alloc.arm1]
  obtain ⟨a1, a2, a3, a4⟩ := allocW_ok hT ha
  obtain ⟨-, -, a5, -, -⟩ := allocW_factsA (by decide) hT.1 (by have := hT.1; have := hT.2; omega) ha
  rw [hcn] at a4 a5
  have hR₁ : ArenaR m₁ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₁ a1.frame a hR
  have hD₁ : StateDR m₁ st := hD.frame a1.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hps₁ := psum_congr a1.ifr to
  have hkeep : ∀ i, 1 ≤ i → i ≤ topN m IFL → wd m₁ IFL i = wd m IFL i := a1.keep
  have hCN₁ : ∀ k, k < cts.length → (wd m₁ IFL (cno.toNat + k)).toNat < 2 ^ 32 := fun k hk => by
    rw [hkeep _ (by omega) (by omega)]; exact hCN k hk
  have hCt₁ : ListF (CtF b m₁) m₁ 10 co.toNat cts := hCt.ext a1 (fun _ _ x => x.ext a1)
  rw [← hps₁] at hfo hps
  have hcnt : ∀ k, cntF m₁ to k = cntF m to k := fun k => by simp only [cntF, wd, a1.ifr]
  have hsl := islice_ext (k := .name) a1 cno.toNat cts.length (by omega) hcnB
  have hpos : ∀ k' c', k' < tn.toNat → c' < cntF m to k' → psum m to k' + c' < psum m to tn.toNat := by
    intro k' c' h1 h2
    have := psum_mono m to (k' + 1) tn.toNat (by omega)
    rw [psum_succ] at this; omega
  have hfo' := fun p hp => (hfo p (by rw [hps₁]; exact hp)).1
  have hg := orderGo_ref (p := p) (fuel := fuel) (st := st) (oo := oo) (tyn := tyn) (fo := fo) hR₁ hD₁ hCt₁ hcn hCN₁ (by omega) hnp hco
    (by rw [a1.size]; omega) a2.1 hto (by omega)
    (fun p hp => by
      obtain ⟨f1, f2⟩ := hfo p hp
      exact ⟨by omega, by rw [hkeep _ (by omega) f1]; exact f2⟩) hps n m₁ 0 0
    (IOnly.refl _ _) (UInt64.le_iff_toNat_le.mpr (Nat.zero_le _)) (by simp [psum])
  rcases hgo : viOrderGoE p n m₁ to tn tyn fo cno co cn fuel np oo 0 0 with e2 | ⟨u, m₂⟩ <;> rw [hgo] at hg
  · rw [viOrderE.k_vi_order_go.none]
    intro _ htt hk
    obtain ⟨hcl, k, -, hk', c, hc', g1, g2, g3⟩ := hg trivial
      (fun k hk => by rw [hkeep _ (by omega) (by omega)]; exact htt k hk) hk
    simp only [hps₁, hcnt] at g1 g2 g3 hc'
    refine ⟨hcl, k, hk', c, hc', fun k' hk'' c' hc'' => ?_, fun c' hc'' => ?_, ?_⟩
    · obtain ⟨kk, e2⟩ := g1 k' (Nat.zero_le _) hk'' c' hc''
      rw [hsl, hkeep _ (by omega) (by have := hfo' _ (hpos k' c' (by omega) hc''); omega), hkeep _ (by omega) (by omega)] at e2
      exact ⟨kk, e2⟩
    · obtain ⟨kk, e2⟩ := g2 c' hc''
      rw [hsl, hkeep _ (by omega) (by have := hfo' _ (hpos k c' hk' (by omega)); omega), hkeep _ (by omega) (by omega)] at e2
      exact ⟨kk, e2⟩
    · rw [hsl, hkeep _ (by omega) (by have := hfo' _ (hpos k c hk' hc'); omega), hkeep _ (by omega) (by omega)] at g3
      exact g3
  rw [viOrderE.k_vi_order_go.arm1]
  obtain ⟨g1, -, g3⟩ := hg
  dsimp only at g1 g3
  have ht0 : topN m₂ IFL = topN m₁ IFL := by unfold topN; rw [g1.2 0 (by omega)]
  have hI : IExt m m₂ := ⟨a1.frame.trans (g1.1.mono (by simp) (by simp)), by rw [ht0]; exact a1.top,
    fun i h1 h2 => by rw [g1.2 i (by omega)]; exact a1.keep i h1 h2⟩
  refine ⟨a3, hI, ⟨by rw [g1.1.size]; exact a2.1, by rw [g1.1.size, ht0]; exact a2.2⟩,
    by rw [ht0, a4], fun k hk c hc => ?_⟩
  rw [← hcnt] at hc
  obtain ⟨kk, e1, e2⟩ := g3 k (Nat.zero_le _) hk c hc
  rw [hps₁] at e1 e2
  have hp : psum m to k + c < psum m to tn.toNat := by
    have := psum_mono m to (k + 1) tn.toNat (by omega)
    rw [psum_succ, ← hcnt] at this; omega
  obtain ⟨f1, -⟩ := hfo (psum m to k + c) (by rw [hps₁]; exact hp)
  rw [islice_ext a1 _ _ (by omega) hcnB, hkeep _ (by omega) (by omega),
    hkeep _ (by omega) (by omega)] at e2
  exact ⟨kk, e1, e2⟩

end L.Front.Ind
