module

public import ConAgua.Arena.InferBodyLet
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
public import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.Infer
import ConAgua.L.WordOff
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.WhnfIotaRefine2

@[expose] public section

/-!
# The application spines of both bodies (lane `defeq`)

`infer_spine_io`/`infer_app_io` (the io grade: no argument check) and `infer_spine`/
`infer_spine_arg`/`infer_app` (the full grade, `InferBodySpineF.lean`). Each has one unified model
and one refinement for both outcomes (`RefE` with `CorePost`). A spine's refinement is by induction
on the loop fuel of its model's loop (`spioLoop_ref`): the arguments are the slice `(ao, an)` below
the entry top `co`, the accumulator the slice `(co, cn)` at the top; a callee keeps the stack below
the top (`StackKept`), so the arguments survive it.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- A word store as a spec: the bound and the new memory. -/
theorem st64_spec (a : ArrId) (i v : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ st64 a i v
    ⦃fun _ s' => i.toNat < (s₀.mem.arr64 a).size ∧ s' = { s₀ with mem := s₀.mem.set64 a i v }; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [st64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [StateT.run_set, pure] at hrun
    cases hrun
    exact ⟨h, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
    cases hrun

theorem w_lt_false {a b : Word} (h : b ≤ a) : (a < b) = False := eq_false (UInt64.not_lt.mpr h)

/-- `infer_spine_io`'s unified model: the `whnf` slot through its run, `inst_list` lifted. -/
l_model spioE_spec (p : Prog) (hf : p.lookup "infer_spine_io" = some inferSpineIOL)
  fns [hf ↦ spioE list]
  specs [callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the spine specs need of a program. -/
structure SpineInferProg (p : Prog) : Prop where
  spineIO : p.lookup "infer_spine_io" = some inferSpineIOL
  appIO : p.lookup "infer_app_io" = some inferAppIOL

/-- The pushed accumulator's memory: the argument at `co + cn`, the top `co + cn + 1`. -/
def spPush (m : Mem) (co cn a : Word) : Mem := (m.set64 SPN (co + cn) a).set64 CTL 136 (co + (cn + 1))

theorem tfld_spPush (m : Mem) (co cn v t x f : Word) :
    tfld (spPush m co cn v) FORALL t x f = tfld m FORALL t x f := by
  simp only [tfld, spPush]
  rw [Mem.arr64_set64_ne _ _ _ _ _ (L.tierA_ne (by decide) t),
    Mem.arr64_set64_ne _ _ _ _ _ (L.tierA_ne (by decide) t)]

theorem lt_of_not_len64_le {m : Mem} {a : ArrId} {x : Word} (hsz : (m.arr64 a).size < 2 ^ 63)
    (h : ¬ m.len64 a ≤ x) : x.toNat < (m.arr64 a).size := by
  have h' := UInt64.not_le.mp h
  rw [UInt64.lt_iff_toNat_lt, Mem.len64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h'
  exact h'

theorem len64_not_lt {m : Mem} {co : Word} (hspn : (m.arr64 SPN).size < 2 ^ 63)
    (h : ¬ m.len64 SPN < co) : co.toNat ≤ (m.arr64 SPN).size := by
  have h' := UInt64.not_lt.mp h
  rw [UInt64.le_iff_toNat_le, Mem.len64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h'
  exact h'

/-! ## Pushing onto the accumulator -/

/-- **A push onto the accumulator at the top**: the slice grows by the word, the top with it, the
stack below the accumulator is kept. -/
theorem spPush_step {m m₀ : Mem} {co cn v : Word} {acc : Array EIdx}
    (hspn : (m.arr64 SPN).size < 2 ^ 63) (hacc : SpineR m co cn acc)
    (hb : ∀ j, j < co → spW m j = spW m₀ j) (hsz : (m.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbk : BKept m₀ m) (hpg : PoolGrew m₀ m)
    (h136 : (136 : Word).toNat < (m.arr64 CTL).size)
    (hbd : (co + cn).toNat < (m.arr64 SPN).size) (hv : HW v) :
    SpineR (spPush m co cn v) co (cn + 1) (acc.push (decE v)) ∧
      spTop (spPush m co cn v) = co + (cn + 1) ∧
      (∀ j, j < co → spW (spPush m co cn v) j = spW m₀ j) ∧
      ((spPush m co cn v).arr64 SPN).size = (m₀.arr64 SPN).size ∧
      (136 : Word).toNat < ((spPush m co cn v).arr64 CTL).size ∧
      BKept m₀ (spPush m co cn v) ∧ PoolGrew m₀ (spPush m co cn v) := by
  have hco_le := hacc.bound
  have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
  have hadd : (co + cn).toNat = co.toNat + cn.toNat := L.toNat_add_of_lt _ _ hcn64
  refine ⟨(hacc.push hspn (by rw [← hadd]; exact hbd) v hv).setCtl 136 (co + (cn + 1)), ?_, ?_,
    by simp only [spPush, L.Mem.size64_set64]; exact hsz, by simp only [spPush, L.Mem.size64_set64]; exact h136,
    hbk.trans (BKept.of_frame (spnCtl_frame m (co + cn) v (co + (cn + 1))) (by decide) (by decide)),
    hpg.trans (PoolGrew.of_frame (spnCtl_frame m (co + cn) v (co + (cn + 1))) (by decide) (by decide))⟩
  · unfold spTop spPush
    rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [L.Mem.size64_set64]; exact h136⟩]
  · intro j hj
    simp only [spPush]
    rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
      have := UInt64.lt_iff_toNat_lt.mp hj
      rw [← h, hadd] at this; omega)]
    exact hb j hj


/-! ## `infer_spine_io` refines `inferSpineIO`, both outcomes -/

/-- **A spine's exit, both outcomes**: `inst_list` at the accumulator (outside the verdict closure,
lifted), the top put back (`k` the model's continuation). -/
theorem spTail_ref (p : Prog) (hil : InstListOK p) {G : Prop} (n : Nat)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb co : Word) (m₀ : Mem)
    (hco : co = spTop m₀) {k : Except Err (List Word × Mem) → Except Err (List Word × Mem)}
    (hk0 : ∀ e, k (.error e) = .error e)
    (hk : ∀ r m₁, k (.ok (r, m₁)) = .ok ([r.headD 0], m₁.set64 CTL 136 co))
    (m : Mem) (a : AState) (M : ModeMaps) (ty cn : Word) (acc : Array EIdx)
    (hS : CoreS dn m a vis fe M eb) (ht : HW ty) (hacc : SpineR m co cn acc)
    (htop : spTop m = co + cn) (hb : ∀ j, j < co → spW m j = spW m₀ j)
    (hsz : (m.arr64 SPN).size = (m₀.arr64 SPN).size) (hbk : BKept m₀ m) (hpg : PoolGrew m₀ m) :
    RefE G (k (liftE (callW p n "inst_list" [ty, co, cn, 0] m)))
      (instantiateListFast coreWalkFuel (decE ty) acc 0) a (CorePost decH dn m₀ vis fe M eb ResH) := by
  have hco_le := hacc.bound
  have hspn := hS.spn
  have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
  have hadd : (co + cn).toNat = co.toNat + cn.toNat := L.toNat_add_of_lt _ _ hcn64
  rw [← bind_pure (instantiateListFast coreWalkFuel (decE ty) acc 0)]
  refine RefE.bind_callW hk0 (hil n ⟨m, Locals.init []⟩ a dn vis fe M eb ty co cn 0 acc hS ht hacc
    (by rw [htop, hadd]; exact Nat.le_refl _)) fun r₁ m₁ _ ⟨_, ⟨M', hS', hK', hSt'⟩, _, hrw⟩ => ?_
  rw [hk]
  have hjc : ∀ j : Word, j < co → j < spTop m := fun j hj => by
    rw [htop, UInt64.lt_iff_toNat_lt, hadd]; have := UInt64.lt_iff_toNat_lt.mp hj; omega
  have hg : StackGrew m₀ m₁ :=
    ⟨by rw [hSt'.top, htop, ← hco, UInt64.le_iff_toNat_le, hadd]; omega,
      by rw [hSt'.size, hsz], fun j hj => by rw [← hco] at hj; rw [hSt'.below j (hjc j hj), hb j hj],
      hbk.trans hSt'.bstk, hpg.trans hSt'.pool⟩
  have hkept := StackKept.restoreG' hg
  rw [show rdW (m₀.arr64 CTL) 136 = co by rw [hco]; rfl] at hkept
  exact RefE.ret rfl ⟨⟨M', hS'.frame_stk (MemFrame.setCtl m₁ 136 co) (by simp) (by simp), hK', hkept⟩, rfl, hrw⟩

/-- **The io spine's loop refines `inferSpineIO`, both outcomes**, by induction on the loop fuel: a
step's `whnf` (the slot's errors), a non-`∀` type after it rejects, the exit is `spTail_ref`. -/
theorem spioLoop_ref (p : Prog) (hil : InstListOK p) (N : Nat) (hk : KnotUpTo p N) (F : Nat)
    (hF : N ≤ F) (hN : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d ao an : Word) (args : Array EIdx) (eb co : Word) (hmode : mode < 4)
    (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) (har₀ : SpineR m₀ ao an args)
    (hco : co = spTop m₀) (hlo : ao.toNat + an.toNat ≤ co.toNat) :
    ∀ k, k ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (ty i cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe M eb → HW ty → SpineR m co cn acc → spTop m = co + cn →
      (∀ j, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      BKept m₀ m → PoolGrew m₀ m →
      RefE (InferG p N) (spioE.k_loop1 p N co (spioE.loop1 p k m mode vis d ty ao an co cn i))
        (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE ty) acc
          args i.toNat) a (CorePost decH dn m₀ vis fe M eb ResH) := by
  intro k
  induction k with
  | zero =>
    intro _ m a M ty i cn acc _ _ _ _ _ _ _ _
    rw [spioE.loop1.eq_1]; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro hkN m a M ty i cn acc hS ht hacc htop hb hsz hbk hpg
    rw [spioE.loop1.eq_2]
    have hspn := hS.spn
    have hco_le : co.toNat + cn.toNat ≤ (m.arr64 SPN).size := hacc.bound
    have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
    have hadd : (co + cn).toNat = co.toNat + cn.toNat := L.toNat_add_of_lt _ _ hcn64
    have hspT : (spTop m).toNat = co.toNat + cn.toNat := by rw [htop, hadd]
    have har : SpineR m ao an args := har₀.keepT co hsz hb hlo (hsz ▸ hspn)
    by_cases hlt : i < an
    · rw [ite_eq_left hlt]
      have hlt' : i.toNat < args.size := by rw [har₀.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hit : (i.toNat).toUInt64 = i := by simp
      have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
        have h := har.get i.toNat hlt'; rwa [hit] at h
      have hvv : HW (spW m (ao + i)) := by
        have h := har.lt i.toNat (by rw [← har.size]; exact hlt'); rwa [hit] at h
      have hi1 := L.toNat_add_one_of_word_lt _ _ hlt
      by_cases ht6 : tagW ty = 6
      · -- the ∀ step: the argument is pushed
        rw [ite_eq_left ht6]
        refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by rfl) fun c1 => ?_)
        refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by rfl) fun c2 => ?_)
        refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by rfl) fun c3 => ?_)
        rw [spioE.j1.eq_def]
        have c4 := lt_of_not_len64_le hspn c3
        have hv : viewOK m ty FORALL := ⟨c1, UInt64.not_le.mp c2⟩
        obtain ⟨-, -, hbody⟩ := view_forall m a hS.arena.base ty ht hv ht6
        have hvb := viewBind_forall m a hS.arena.base ty ht hv ht6
        obtain ⟨hacc', htop', hb', hsz', -, hbk', hpg'⟩ := spPush_step hspn hacc hb hsz hbk hpg
          hS.ctl136 c4 hvv
        have hS' := hS.frame_stk (spnCtl_frame m (co + cn) (spW m (ao + i)) (co + (cn + 1)))
          (by simp) (by simp)
        have hih := ih (by omega) _ a M _ (i + 1) (cn + 1) _ hS' hbody hacc' htop' hb' hsz' hbk' hpg'
        rw [hi1] at hih
        rw [show (m.set64 SPN (co + cn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136 (co + (cn + 1)) =
          spPush m co cn (spW m (ao + i)) from rfl, tfld_spPush]
        refine RefE.of_run_eq ?_ hih
        rw [inferSpineIO]
        simp only [hlt', dite_true, decE_tag_forallE_beq ty ht, ht6, decide_true, ite_true,
          StateT.run_bind, L.Arena.viewBind_run, hvb, except_ok_bind, hxi]
      · -- the `whnf` re-entry: the accumulator restarts at `#[a]`
        rw [ite_eq_right ht6]
        have hnfa : ((decE ty).tag == ETag.forallE) = false := by
          rw [decE_tag_forallE_beq ty ht]; simp [ht6]
        rw [inferSpineIO]
        simp only [hlt', dite_true, hnfa, Bool.false_eq_true, ite_false]
        -- `inst_list`, the slot `whnf`
        refine RefE.under (fun _ => rfl) (fun _ => spioE.k_inst_list_2.none ..) fun hx => RefE.bind_callW hx
          (hil k ⟨m, Locals.init []⟩ a dn vis fe M eb ty co cn 0 acc hS ht hacc (by rw [hspT]; exact Nat.le_refl _))
          fun r₁ m₁ _ ⟨_, ⟨M₁, hS₁, hK₁, hSt₁⟩, _, hrw1⟩ => ?_
        rw [Function.comp_apply, spioE.k_inst_list_2.arm1]
        refine RefE.under (fun _ => rfl) (fun _ => spioE.k_whnf.none ..) fun hx => RefE.bind_callE hx
          ((hk k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega) (by omega)
            ⟨hS₁, hmode, heb⟩ hrw1)
          (fun (hG : InferG p N) => (hG.knot k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega)
            (by omega) ⟨hS₁, hmode, heb⟩ hrw1) fun r₂ m₂ _ ⟨_, ⟨M₂, hS₂, hK₂, hSt₂⟩, _, hrw2⟩ => ?_
        rw [Function.comp_apply, spioE.k_whnf.eq_2]
        refine RefE.underIf (fun _ => rfl) (RefE.guardIf (by rfl)
          (fun g => (decE_tag_forallE_beq _ hrw2).trans (decide_eq_false g))
          (fun hb => of_decide_eq_false ((decE_tag_forallE_beq _ hrw2).symm.trans hb)) fun g1 _ => ?_)
        have g1' : tagW (r₂.headD 0) = 6 := by simpa using g1
        refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by rfl) fun g2 => ?_)
        refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by rfl) fun g3 => ?_)
        refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by rfl) fun g4 => ?_)
        rw [spioE.j1.eq_def]
        have g5 := lt_of_not_len64_le hS₂.spn g4
        have hSt12 := hSt₁.trans hSt₂
        have hb₂ : ∀ j, j < co → spW m₂ j = spW m₀ j := by
          intro j hj
          have hj' : j < spTop m := by
            rw [htop, UInt64.lt_iff_toNat_lt, hadd]
            have := UInt64.lt_iff_toNat_lt.mp hj; omega
          exact (hSt12.below j hj').trans (hb j hj)
        have hsz₂ : (m₂.arr64 SPN).size = (m₀.arr64 SPN).size := hSt12.size.trans hsz
        have hv : viewOK m₂ (r₂.headD 0) FORALL := ⟨g2, UInt64.not_le.mp g3⟩
        obtain ⟨-, -, hbody⟩ := view_forall m₂ _ hS₂.arena.base (r₂.headD 0) hrw2 hv g1'
        have hvb := viewBind_forall m₂ _ hS₂.arena.base (r₂.headD 0) hrw2 hv g1'
        have hacc0 := L.Arena.SpineR.nil_at m₂ co (by omega)
        obtain ⟨hacc', htop', hb', hsz', -, hbk', hpg'⟩ := spPush_step (cn := 0) hS₂.spn hacc0 hb₂
          hsz₂ (hbk.trans hSt12.bstk) (hpg.trans hSt12.pool) hS₂.ctl136 (by simpa using g5) hvv
        have hS' := hS₂.frame_stk (spnCtl_frame m₂ (co + 0) (spW m (ao + i)) (co + (0 + 1)))
          (by simp) (by simp)
        have hih := ih (by omega) _ _ M₂ _ (i + 1) 1 _ hS' hbody hacc' htop' hb' hsz' hbk' hpg'
        rw [hi1] at hih
        rw [show (m₂.set64 SPN co (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136 (co + 1) =
          spPush m₂ co 0 (spW m (ao + i)) by simp [spPush, spW], tfld_spPush]
        refine RefE.bind_right (by rw [L.Arena.viewBind_run, show decH r₂ = decE (r₂.headD 0) from rfl, hvb]) ?_
        rw [hxi]
        exact hih.mono fun _ _ _ h =>
          ⟨let ⟨M', hS', hK', hSt'⟩ := h.after; ⟨M', hS', hK₁.trans (hK₂.trans hK'), hSt'⟩,
            h.res, h.valid⟩
    · rw [ite_eq_right hlt]
      have hnlt : ¬ i.toNat < args.size := by
        rw [har₀.size]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      refine RefE.of_run_eq (T' := instantiateListFast coreWalkFuel (decE ty) acc 0)
        (by rw [inferSpineIO, dite_eq_right hnlt]) ?_
      simp only [spioE.k_loop1]
      exact spTail_ref p hil N dn vis fe eb co m₀ hco (k := spioE.k_inst_list p co) (fun _ => rfl)
        (fun _ _ => rfl) m a M ty cn acc hS ht hacc htop hb hsz hbk hpg

/-- **`infer_spine_io` refines `inferSpineIO`, both outcomes**, at the io view of the knot, the
head's type `ty` and the arguments the slice `(ao, an)` below the top. -/
theorem spio_ref (p : Prog) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ht : HW ty) (har : SpineR s₀.mem ao an args)
    (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (InferG p n) (spioE p (n + 1) s₀.mem mode vis d ty ao an)
      (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE ty) #[]
        args 0) a₀ (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  simp only [spioE]
  refine RefE.abort0 (by rfl) fun hc => ?_
  have hcle := len64_not_lt hS.spn hc
  exact spioLoop_ref p hil n hk F hF hn dn vis fe mode d ao an args eb _ hs.mode4 hs.eb_mode s₀.mem
    har rfl hlo (n + 1) (Nat.le_refl _) s₀.mem a₀ M ty 0 0 #[] hS ht (L.Arena.SpineR.nil_at _ _ hcle)
    (by simp [spTop]) (fun _ _ => rfl) rfl (BKept.refl _) (PoolGrew.refl _)

/-- **`infer_spine_io` refines `inferSpineIO`** (`spio_ref`'s ok half). -/
@[refines ConRon.Arena.inferSpineIO]
theorem inferSpineIO_refines (p : Prog) (hq : SpineInferProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ht : HW ty) (har : SpineR s₀.mem ao an args)
    (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "infer_spine_io" [mode, vis, d, ty, ao, an]
      (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE ty) #[]
        args 0) decH s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (spioE_spec p hq.spineIO (n + 1) s₀ mode vis d ty ao an)
    (spio_ref p hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty ao an args hs ht har hlo)

/-- `infer_spine_io` at every L fuel up to `n + 1`. -/
theorem inferSpineIO_any (p : Prog) (hq : SpineInferProg p) (hil : InstListOK p) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "infer_spine_io" [mode, vis, d, ty, ao, an]
      (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE ty) #[]
        args 0) decH s₀ a₀ dn vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, ty, ao, an, args, hs, ht, har, hlo =>
      inferSpineIO_refines p hq hil n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M
        eb mode d ty ao an args hs ht har hlo

/-- `infer_spine_io`'s error claim at every L fuel up to `n + 1` (`spio_ref`'s error half). -/
theorem inferSpineIO_anyE (p : Prog) (hq : SpineInferProg p) (hil : InstListOK p) :
    ∀ n, KnotUpTo p n → InferG p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p n "infer_spine_io" [mode, vis, d, ty, ao, an]
      (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE ty) #[]
        args 0) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hG, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, ty, ao, an, args, hs, ht, har, hlo =>
      RefE.coreSpecE (spioE_spec p hq.spineIO (n + 1) s₀ mode vis d ty ao an) hG.nv
        (hG.mono (by omega)) (spio_ref p hil n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn
          vis fe M eb mode d ty ao an args hs ht har hlo)

/-! ## `infer_app_io` -/

/-- **`head_and_args` at an `app` handle** refines `headAndArgs` with no hypothesis on the stack top
(`headAndArgs_refines` needs one for the empty slice of a non-`app` head). -/
theorem headAndArgs_app (p : Prog) (hp : SpineProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hR : ArenaR s₀.mem a₀) (v : Word) (hv : HW v) (h4 : tagW v = 4)
    (hspn : (s₀.mem.arr64 SPN).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "head_and_args" [v]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧ StackGrew s₀.mem s'.mem ∧
      HW (r.headD 0) ∧ r.tail.headD 0 = spTop s₀.mem ∧
      spTop s'.mem = spTop s₀.mem + r.tail.tail.headD 0 ∧
      ∃ xs, (headAndArgs (decE v)).run a₀ = .ok ((decE (r.headD 0), xs), a₀) ∧
        SpineR s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) xs; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs0 hrun
  subst hs0
  obtain ⟨hloc, hcall⟩ := M.of_run (P := fun x => x = s) rfl hrun (callW_spec p n "head_and_args" [v] s)
  cases n with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (haa_spec p hp.hargs n s v) hcall
  rw [ht] at hW
  refine ⟨hloc, ?_⟩
  simp only [haaW] at hW
  rw [ite_eq_left h4] at hW
  rcases h1 : callW p n "get_app_fn" [v] s.mem with _ | ⟨r₁, m₁⟩ <;> simp only [h1, reduceCtorEq] at hW
  rcases h2 : callW p n "get_app_args" [v] m₁ with _ | ⟨r₂, m₂⟩ <;> simp only [h2, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hW
  obtain ⟨hr0, hr1, hr2, hm⟩ := hW
  obtain ⟨t₁, ht₁, hm₁, -, hhw, hfnrun⟩ := triple_of_callW (getAppFn_refines' p hp.fn n s a₀ hR v hv) h1
  rw [ht₁] at hm₁
  subst hm₁
  obtain ⟨t₂, ht₂, -, hfr, hgrow, ho, htop, xs, hxs, hsr⟩ :=
    triple_of_callW (getAppArgs_refines' p hp.args hp.cnt hp.fill n s a₀ hR v hv hspn) h2
  rw [ht₂] at hfr hgrow htop hsr
  subst hm
  refine ⟨hfr, hgrow, by rw [← hr0]; exact hhw, by rw [← hr1]; exact ho,
    by rw [← hr2]; exact htop, xs.toArray, ?_, by rw [← hr1, ← hr2]; exact hsr⟩
  have htag : (decE v).tag = ETag.app := (decE_tag_app v hv).mpr h4
  rw [← hr0]
  simp [headAndArgs, htag, StateT.run_bind, hfnrun, except_ok_bind]
  simp only [StateT.run] at hxs ⊢
  simp only [hxs]
  rfl

/-- `infer_app_io`'s unified model: the `infer_io` slot and `infer_spine_io` through their runs,
`head_and_args` lifted. -/
l_model aioE_spec (p : Prog) (hf : p.lookup "infer_app_io" = some inferAppIOL)
  fns [hf ↦ aioE list]
  specs [callW_spec p n "head_and_args"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- `inferBodyIO`'s `.app` arm is `inferAppIOAt`. -/
@[refines_part ConRon.Arena.inferBodyIO "app"]
theorem inferBodyIO_app (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (f x : EIdx) (hv : a.store.view e = some (.app f x)) :
    (inferBodyIO r fe d e).run a = (inferAppIOAt r fe d e).run a := by
  simp only [inferBodyIO, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

/-- **`infer_app_io` refines `inferAppIOAt`, both outcomes**, at the io view of the knot, at an
`app` handle: the head's type (the `infer_io` slot), the spine's (`infer_spine_io`); `head_and_args`
claims nothing. -/
theorem aio_ref (p : Prog) (hq : SpineInferProg p) (hsp : SpineProg p)
    (hil : InstListOK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e)
    (h4 : tagW e = 4) :
    RefE (InferG p n) (aioE p (n + 1) s₀.mem mode vis d e)
      (inferAppIOAt (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  simp only [aioE, inferAppIOAt]
  refine RefE.bindLift (fun _ => rfl) fun r₁ m₁ hc1 => ?_
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, hha, hxs⟩ := triple_of_callW
    (headAndArgs_app p hsp n s₀ a₀ hS.arena.base e he h4 hS.spn) hc1
  rw [ht₁] at hf₁ hg₁ htop1 hxs
  refine ⟨_, _, hha, ?_⟩
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hb1 := hxs.bound
  have hspn₁ := hS₁.spn
  have hadd : (r₁.tail.headD 0 + r₁.tail.tail.headD 0).toNat =
      (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := L.toNat_add_of_lt _ _ (by omega)
  have htopN : (spTop m₁).toNat = (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := by
    rw [htop1, ← ho1, hadd]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ a₀ dn vis fe M eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  simp only [aioE.k_head_and_args]
  -- the slot `infer_io`, then `infer_spine_io`
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F ⟨m₁, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₁.headD 0)
    hF hn hs₁ hhw) (fun (hG : InferG p n) => (hG.knot n (Nat.le_refl _)).inferIO F ⟨m₁, Locals.init []⟩ a₀ dn vis
    fe M eb mode d (r₁.headD 0) hF hn hs₁ hhw) fun r₂ m₂ _ ⟨_, ⟨M₂, hS₂, hK₂, hSt₂⟩, _, hrw2⟩ => ?_
  have hxs₂ : SpineR m₂ (r₁.tail.headD 0) (r₁.tail.tail.headD 0) xs :=
    hxs.keep hSt₂.size hSt₂.below (by rw [htopN]; exact Nat.le_refl _) hspn₁
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  have hlo₂ : (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat ≤ (spTop m₂).toNat := by
    rw [hSt₂.1, htopN]; exact Nat.le_refl _
  simp only [aioE.k_infer_io]
  rw [← bind_pure (inferSpineIO _ _ _ _ _ _ _)]
  refine RefE.bind_callE (fun _ => rfl) (inferSpineIO_any p hq hil n hk F hF hn ⟨m₂, Locals.init []⟩ _ dn vis fe M₂
    eb mode d (r₂.headD 0) _ _ xs hs₂ hrw2 hxs₂ hlo₂) (fun hG => inferSpineIO_anyE p hq hil n hk hG F hF hn _ _ dn vis
    fe M₂ eb mode d (r₂.headD 0) _ _ xs hs₂ hrw2 hxs₂ hlo₂) fun r₃ m₃ _ ⟨_, ⟨M₃, hS₃, hK₃, hSt₃⟩, _, hrw3⟩ => ?_
  exact RefE.ret rfl ⟨⟨M₃, hS₃.frame_stk (MemFrame.setCtl m₃ 136 _) (by simp)
    (by simp), hK₂.trans hK₃, StackKept.restoreG' (hg₁.trans (hSt₂.trans hSt₃).toGrew)⟩, rfl, hrw3⟩

/-- **`infer_app_io` refines `inferAppIOAt`** (`aio_ref`'s ok half). -/
@[refines ConRon.Arena.inferAppIOAt]
theorem inferAppIO_refines (p : Prog) (hq : SpineInferProg p) (hsp : SpineProg p)
    (hil : InstListOK p) (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e)
    (h4 : tagW e = 4) :
    CoreSpec p (n + 1) "infer_app_io" [mode, vis, d, e]
      (inferAppIOAt (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE e)) decH
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (aioE_spec p hq.appIO (n + 1) s₀ mode vis d e)
    (aio_ref p hq hsp hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d e hs he h4)

end L.Arena
