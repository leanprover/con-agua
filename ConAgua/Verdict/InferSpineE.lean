import ConAgua.Verdict.InferArmsE
import ConAgua.Arena.RecFireCore

/-!
# Error refinements of the application spines (lane `verdicts-b`, helper `k1`)

The verdict claims of `infer_spine_io`, `infer_spine` (the loops, by induction on the loop fuel
as `spioFull_ref`/`spFull_ref`: the twin's step is the loop's), `infer_app_io`, `infer_app`.
A loop's errors are the `whnf` slot's (at the re-entry), `infer_spine_arg`'s (the full grade), a
non-`∀` type after `whnf` rejects ("function expected"); the capacity aborts and the callees
outside the verdict closure (`inst_list`, `head_and_args`) claim nothing. The loop's stores are in
bounds by the L code's own length checks and `CoreS.ctl136`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Store bounds from the L code's own checks -/

theorem lt_of_not_len64_le {m : Mem} {a : ArrId} {x : Word} (hsz : (m.arr64 a).size < 2 ^ 63)
    (h : ¬ m.len64 a ≤ x) : x.toNat < (m.arr64 a).size := by
  have h' := UInt64.not_le.mp h
  rw [UInt64.lt_iff_toNat_lt, Mem.len64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h'
  exact h'

theorem tfld_spPush (m : Mem) (co cn v t x f : Word) :
    tfld (spPush m co cn v) FORALL t x f = tfld m FORALL t x f := by
  simp only [tfld, spPush]
  rw [Mem.arr64_set64_ne _ _ _ _ _ (by intro h; have h' : 29 + 256 * (t &&& 1).toNat = (1 : Nat) := h; omega),
    Mem.arr64_set64_ne _ _ _ _ _ (by intro h; have h' : 29 + 256 * (t &&& 1).toNat = (144 : Nat) := h; omega)]

theorem spPush_zero (m : Mem) (co v : Word) :
    (m.set64 SPN co v).set64 CTL 136 (co + 1) = spPush m co 0 v := by
  simp [spPush]

theorem cls_abort0 {er : Err} (hk0 : er.cls ≠ 0) (h : Err.abort 0 = er) : False := by
  subst h; exact hk0 rfl

/-! ## `infer_spine_io` -/

l_model inferSpineIO_specE (p : Prog) (hf : p.lookup "infer_spine_io" = some inferSpineIOL)
  fns [hf ↦ inferSpineIOE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

/-- **The io spine's loop claims `inferSpineIO`'s failure** (by induction on the loop fuel, as
`spioFull_ref`): a failing step's `whnf` (the slot's claim) or its non-`∀` type (a reject). -/
theorem spioLoopE_ref (p : Prog) (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true)
    (N : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (F : Nat)
    (hF : N ≤ F) (hN : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d ao an : Word) (args : Array EIdx) (eb co : Word) (hmode : mode < 4)
    (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) (har₀ : SpineR m₀ ao an args)
    (_hco : co = spTop m₀) (hlo : ao.toNat + an.toNat ≤ co.toNat) :
    ∀ k, k ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (ty i cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe M eb → HW ty → SpineR m co cn acc → spTop m = co + cn →
      (∀ j, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      BKept m₀ m → PoolGrew m₀ m →
      ∀ er, er.cls ≠ 0 → inferSpineIOE.loop1 p k m mode vis d ty ao an co cn i = .error er →
      ErrClaim (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty)
        acc args i.toNat) a er := by
  intro k
  induction k with
  | zero =>
    intro _ m a M ty i cn acc _ _ _ _ _ _ _ _ er hk0 hF
    rw [inferSpineIOE.loop1.eq_1] at hF; cases hF; exact absurd rfl hk0
  | succ k ih =>
    intro hkN m a M ty i cn acc hS ht hacc htop hb hsz hbk hpg er hk0 hF
    rw [inferSpineIOE.loop1.eq_2] at hF
    have hspn := hS.spn
    have hco_le : co.toNat + cn.toNat ≤ (m.arr64 SPN).size := hacc.bound
    have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
    have hadd : (co + cn).toNat = co.toNat + cn.toNat := addW _ _ hcn64
    have hspT : (spTop m).toNat = co.toNat + cn.toNat := by rw [htop, hadd]
    have har : SpineR m ao an args := har₀.keepT co hsz hb hlo (hsz ▸ hspn)
    by_cases hlt : i < an
    · rw [if_pos hlt] at hF
      have hlt' : i.toNat < args.size := by rw [har₀.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hit : (i.toNat).toUInt64 = i := by simp
      have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
        have h := har.get i.toNat hlt'; rwa [hit] at h
      have hvv : HW (spW m (ao + i)) := by
        have h := har.lt i.toNat (by rw [← har.size]; exact hlt'); rwa [hit] at h
      have hi1 := succ_toNat_of_lt hlt
      by_cases ht6 : ty >>> 28 = 6
      · rw [if_pos ht6] at hF
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i c1
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i c2
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i c3
        rw [inferSpineIOE.j1.eq_def] at hF
        have c4 := lt_of_not_len64_le hspn c3
        have hv : viewOK m ty FORALL := ⟨c1, UInt64.not_le.mp c2⟩
        obtain ⟨-, -, hbody⟩ := view_forall m a hS.arena.1 ty ht hv ht6
        have hvb := viewBind_forall m a hS.arena.1 ty ht hv ht6
        obtain ⟨hacc', htop', hb', hsz', h136', hbk', hpg'⟩ := spPush_step hspn hacc hb hsz hbk hpg
          hS.ctl136 c4 hvv
        have hS' := hS.frame_stk (spnCtl_frame m (co + cn) (spW m (ao + i)) (co + (cn + 1)))
          (by simp) (by simp)
        have hF' : inferSpineIOE.loop1 p k (spPush m co cn (spW m (ao + i))) mode vis d
            (tfld m FORALL (tierW ty) (idxW ty) 1) ao an co (cn + 1) (i + 1) = .error er := by
          rw [← tfld_spPush m co cn (spW m (ao + i))]; exact hF
        have hih := ih (by omega) _ a M _ (i + 1) (cn + 1) _ hS' hbody hacc' htop' hb' hsz' hbk' hpg'
          er hk0 hF'
        rw [hi1] at hih
        refine ErrClaim.of_run_eq' (fun ce h => ?_) hih
        rw [← h, inferSpineIO]
        simp only [hlt', dite_true, tag_fa_beq ty ht, ht6, decide_true, ite_true, StateT.run_bind,
          viewBind_run', hvb, except_ok_bind, hxi]
      · rw [if_neg ht6] at hF
        have hnfa : ((decE ty).tag == ETag.forallE) = false := by rw [tag_fa_beq ty ht]; simp [ht6]
        cases h1 : callE p k "inst_list" [ty, co, cn, 0] m with
        | error e1 =>
          rw [h1, inferSpineIOE.k_inst_list_2.none] at hF; cases hF
          exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
        | ok q =>
        obtain ⟨r₁, m₁⟩ := q
        rw [h1, inferSpineIOE.k_inst_list_2.eq_2] at hF
        have hinst := hil k ⟨m, Locals.init []⟩ a dn vis fe M eb ty co cn 0 acc hS ht hacc
          (by rw [hspT]; exact Nat.le_refl _)
        have h₁ := CoreSpec.of_callW hinst (callW_of_callE h1)
        obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := h₁
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [h0] at hok1 hres1 hS₁
        have hpre : (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat
            (decE ty) acc args i.toNat).run a =
            ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE (r₁.headD 0)) >>= fun w =>
              if w.tag == ETag.forallE then
                (viewBind w >>= fun x => match x with
                  | none => failDanglingE
                  | some (_, body) => inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F))
                      fe d.toNat body #[args[i.toNat]] args (i.toNat + 1))
              else fail (.invalid "function expected")).run
              (AM.st (instantiateListFast coreWalkFuel (decE ty) acc 0) a) := by
          rw [inferSpineIO]
          simp only [hlt', dite_true, hnfa, Bool.false_eq_true, ite_false, StateT.run_bind,
            AM.run_of_ok _ _ hok1, except_ok_bind]
          rw [hres1]; rfl
        cases h2 : callE p k "whnf" [mode, vis, d, r₁.headD 0] m₁ with
        | error e2 =>
          rw [h2, inferSpineIOE.k_whnf.none] at hF; cases hF
          refine ErrClaim.of_run_eq' (fun ce h => hpre.trans h) ?_
          exact ErrClaim.bind_left (CoreSpecE.of_callE
            (s₀ := ⟨m₁, Locals.init []⟩) ((hkE k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
              mode d (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) h2)
        | ok q =>
        obtain ⟨r₂, m₂⟩ := q
        rw [h2] at hF
        have hw := CoreSpec.of_callW ((hk k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
          mode d (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) (callW_of_callE h2)
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := hw
        have hpre2 : (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat
            (decE ty) acc args i.toNat).run a =
            (if (decE (r₂.headD 0)).tag == ETag.forallE then
                (viewBind (decE (r₂.headD 0)) >>= fun x => match x with
                  | none => failDanglingE
                  | some (_, body) => inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F))
                      fe d.toNat body #[args[i.toNat]] args (i.toNat + 1))
              else fail (.invalid "function expected")).run
              (AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE (r₁.headD 0)))
                (AM.st (instantiateListFast coreWalkFuel (decE ty) acc 0) a)) := by
          rw [hpre, StateT.run_bind, AM.run_of_ok _ _ hok2, except_ok_bind, hres2]; rfl
        by_cases g1 : r₂.headD 0 >>> 28 ≠ 6
        · rw [inferSpineIOE.k_whnf.eq_def] at hF
          simp only [if_pos g1] at hF; cases hF
          have hfa : ((decE (r₂.headD 0)).tag == ETag.forallE) = false := by
            rw [tag_fa_beq _ hrw2]; simpa using g1
          refine ErrClaim.of_error (ce := .invalid "function expected") (hpre2.trans ?_) rfl
          rw [hfa]; rfl
        have g1' : r₂.headD 0 >>> 28 = 6 := by simpa using g1
        rw [inferSpineIOE.k_whnf.eq_def] at hF
        simp only [if_neg g1] at hF
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i g2
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i g3
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i g4
        rw [inferSpineIOE.j1.eq_def, spPush_zero] at hF
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
        obtain ⟨-, -, hbody⟩ := view_forall m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 hv g1'
        have hvb := viewBind_forall m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 hv g1'
        have hacc0 := SpineR.empty m₂ co (by omega)
        obtain ⟨hacc', htop', hb', hsz', h136', hbk', hpg'⟩ := spPush_step (cn := 0) hS₂.spn hacc0 hb₂
          hsz₂ (hbk.trans hSt12.bstk) (hpg.trans hSt12.pool) hS₂.ctl136 (by simpa using g5) hvv
        have hS' := hS₂.frame_stk (spnCtl_frame m₂ (co + 0) (spW m (ao + i)) (co + (0 + 1)))
          (by simp) (by simp)
        have hF' : inferSpineIOE.loop1 p k (spPush m₂ co 0 (spW m (ao + i))) mode vis d
            (tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 1) ao an co 1 (i + 1) =
            .error er := by
          rw [← tfld_spPush m₂ co 0 (spW m (ao + i))]; exact hF
        have hih := ih (by omega) _ _ M₂ _ (i + 1) 1 _ hS' hbody hacc' htop' hb' hsz' hbk' hpg' er hk0 hF'
        rw [hi1] at hih
        refine ErrClaim.of_run_eq' (fun ce h => hpre2.trans ?_) hih
        have hfa : ((decE (r₂.headD 0)).tag == ETag.forallE) = true := by
          rw [tag_fa_beq _ hrw2]; exact decide_eq_true g1'
        rw [← h]
        simp only [hfa, ite_true, StateT.run_bind, viewBind_run', hvb, except_ok_bind, hxi]
        rfl
    · rw [if_neg hlt] at hF; cases hF

/-- **`infer_spine_io`'s verdicts** (the error half of `inferSpineIO_refines`). -/
theorem inferSpineIO_refinesE (p : Prog) (hq : SpineInferProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ht : HW ty) (har : SpineR s₀.mem ao an args)
    (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpecE p (n + 1) "infer_spine_io" [mode, vis, d, ty, ao, an]
      (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty) #[]
        args 0) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferSpineIO_specE p hq.spineIO (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ty ao an) hc0 (Err.code_ne_of_cls hk0)
  simp only [inferSpineIOE] at hW
  have hS := hs.rel
  split at hW
  · exact absurd hW (fun h => cls_abort0 hk0 (Except.error.inj h))
  rename_i hc
  have hcle : (rdW (s₀.mem.arr64 CTL) 136).toNat ≤ (s₀.mem.arr64 SPN).size := len64_not_lt hS.spn hc
  cases hL : inferSpineIOE.loop1 p (n + 1) s₀.mem mode vis d ty ao an (rdW (s₀.mem.arr64 CTL) 136) 0 0
    with
  | error e' =>
    rw [hL] at hW; simp only [inferSpineIOE.k_loop1] at hW; cases hW
    have h := spioLoopE_ref p hil hnv n hk hkE F hF hn dn vis fe mode d ao an args eb _ hs.mode4
      hs.eb_mode s₀.mem har rfl hlo (n + 1) (Nat.le_refl _) s₀.mem a₀ M ty 0 0 #[] hS ht
      (SpineR.empty _ _ hcle) (by simp [spTop]) (fun _ _ => rfl) rfl (BKept.refl _)
      (PoolGrew.refl _) _ hk0 hL
    exact h
  | ok q =>
    obtain ⟨ty', cn', m'⟩ := q
    rw [hL] at hW; simp only [inferSpineIOE.k_loop1] at hW
    cases h1 : callE p n "inst_list" [ty', rdW (s₀.mem.arr64 CTL) 136, cn', 0] m' with
    | error e1 =>
      rw [h1, inferSpineIOE.k_inst_list.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
    | ok q => rw [h1, inferSpineIOE.k_inst_list.arm1] at hW; cases hW

/-! ## `infer_app_io` -/

l_model inferAppIO_specE (p : Prog) (hf : p.lookup "infer_app_io" = some inferAppIOL)
  fns [hf ↦ inferAppIOE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

/-- `infer_spine_io`'s error claim at every L fuel up to `n + 1`. -/
theorem inferSpineIO_anyE (p : Prog) (hq : SpineInferProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p n "infer_spine_io" [mode, vis, d, ty, ao, an]
      (inferSpineIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty) #[]
        args 0) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hkE, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, ty, ao, an, args, hs, ht, har, hlo =>
      inferSpineIO_refinesE p hq hil hnv n (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
        (by omega) s₀ a₀ dn vis fe M eb mode d ty ao an args hs ht har hlo

/-- **`infer_app_io`'s verdicts**: the head's type (the `infer_io` slot), the spine's;
`head_and_args` claims nothing. -/
theorem inferAppIO_refinesE (p : Prog) (hq : SpineInferProg p) (hsp : SpineProg p)
    (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e)
    (h4 : e >>> 28 = 4) :
    CoreSpecE p (n + 1) "infer_app_io" [mode, vis, d, e]
      (inferAppIOAt (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE e)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferAppIO_specE p hq.appIO (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d e) hc0 (Err.code_ne_of_cls hk0)
  simp only [inferAppIOE] at hW
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  cases hc1 : callE p n "head_and_args" [e] s₀.mem with
  | error e1 =>
    rw [hc1, inferAppIOE.k_head_and_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "head_and_args" (by simp)) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW; simp only [inferAppIOE.k_head_and_args] at hW
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, hha, hxs⟩ := triple_of_callE
    (headAndArgs_app p hsp n s₀ a₀ hS.arena.1 e he h4 hS.spn) hc1
  rw [ht₁] at hf₁ hg₁ htop1 hxs
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hb1 := hxs.bound
  have hspn₁ := hS₁.spn
  have hadd : (r₁.tail.headD 0 + r₁.tail.tail.headD 0).toNat =
      (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := addW _ _ (by omega)
  have htopN : (spTop m₁).toNat = (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := by
    rw [htop1, ← ho1, hadd]
  have hio : (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)).infer =
      (coreKnot (decMode mode) fe id F).inferIO := rfl
  simp only [inferAppIOAt]
  refine ErrClaim.bind_right hha ?_
  simp only [hio]
  cases hc2 : callE p n "infer_io" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [hc2, inferAppIOE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      (hKE.inferIO F ⟨m₁, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₁.headD 0) hF hn
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw) hc2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW; simp only [inferAppIOE.k_infer_io] at hW
  have h₂ := CoreSpec.of_callW (hK.inferIO F ⟨m₁, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw) (callW_of_callE hc2)
  obtain ⟨M₂, hS₂, hK₂, hSt₂⟩ := h₂.2.1
  have hxs₂ : SpineR m₂ (r₁.tail.headD 0) (r₁.tail.tail.headD 0) xs :=
    hxs.keep hSt₂.size hSt₂.below (by rw [htopN]; exact Nat.le_refl _) hspn₁
  refine ErrClaim.bind_ref h₂ ?_
  cases hc3 : callE p n "infer_spine_io" [mode, vis, d, r₂.headD 0, r₁.tail.headD 0,
      r₁.tail.tail.headD 0] m₂ with
  | error e3 =>
    rw [hc3, inferAppIOE.k_infer_spine_io.none] at hW; cases hW
    exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) (inferSpineIO_anyE p hq hil hnv n hk hkE F hF hn
      ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d (r₂.headD 0) _ _ xs ⟨hS₂, hs.mode4, hs.eb_mode⟩
      h₂.2.2.2 hxs₂ (by rw [hSt₂.1, htopN]; exact Nat.le_refl _)) hc3
  | ok q => rw [hc3] at hW; simp [inferAppIOE.k_infer_spine_io] at hW

/-! ## `infer_spine` -/

l_model inferSpine_specE (p : Prog) (hf : p.lookup "infer_spine" = some inferSpineL)
  fns [hf ↦ inferSpineE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

/-- **A failing argument check fails the step of `inferSpine`** (`spineArg_run`'s error half). -/
theorem spineArg_errClaim {β : Type} (r : CoreFnsA) (depth : Nat) (a dom : EIdx) (K : AM β)
    (s : AState) (e : Err) (h : ErrClaim (inferSpineArgT r depth a dom) s e) :
    ErrClaim (do
      let ta ← r.infer depth a
      if !(← defeqArg r depth a ta dom) then fail (.invalid "application type mismatch")
      else K) s e := by
  intro hk
  obtain ⟨ce, hce, hc⟩ := h hk
  refine ⟨ce, ?_, hc⟩
  simp only [inferSpineArgT, StateT.run_bind] at hce ⊢
  cases h1 : (r.infer depth a).run s with
  | error e' =>
    rw [h1] at hce
    have h' : (Except.error e' : Except CheckError (Unit × AState)) = .error ce := hce
    cases h'; rfl
  | ok q =>
  obtain ⟨ta, s₁⟩ := q
  rw [h1] at hce
  simp only [except_ok_bind] at hce ⊢
  cases h2 : (defeqArg r depth a ta dom).run s₁ with
  | error e' =>
    rw [h2] at hce
    have h' : (Except.error e' : Except CheckError (Unit × AState)) = .error ce := hce
    cases h'; rfl
  | ok q =>
  obtain ⟨b, s₂⟩ := q
  rw [h2] at hce
  simp only [except_ok_bind] at hce ⊢
  cases b with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at hce ⊢
    have h' : (Except.error (CheckError.invalid "application type mismatch") :
        Except CheckError (Unit × AState)) = .error ce := hce
    cases h'; rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hce
    cases hce

/-- `infer_spine_arg`'s error claim at every L fuel up to `n + 1`. -/
theorem inferSpineArg_anyE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hda : DefeqArgE p) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a dom : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW dom →
    CoreSpecE p n "infer_spine_arg" [mode, vis, d, a, dom]
      (inferSpineArgT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE dom)) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hkE, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, a, dom, hs, ha, hdom =>
      inferSpineArg_refinesE p hp hkp hq he hda n (hk.mono (by omega)) (hkE.mono (by omega)) F
        (by omega) (by omega) s₀ a₀ dn vis fe M eb mode d a dom hs ha hdom

/-- **The full spine's loop claims `inferSpine`'s failure** (by induction on the loop fuel, as
`spFull_ref`): a failing step's argument check (`infer_spine_arg`'s claim), its `whnf` (the slot's
claim) or its non-`∀` type (a reject). -/
theorem spLoopE_ref (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hda : DefeqArgE p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true)
    (N : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (F : Nat)
    (hF : N ≤ F) (hN : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d ao an : Word) (args : Array EIdx) (eb co : Word) (hmode : mode < 4)
    (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) (har₀ : SpineR m₀ ao an args)
    (hlo : ao.toNat + an.toNat ≤ co.toNat) :
    ∀ k, k ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (ty i cn : Word) (acc : Array EIdx),
      CoreS dn m a vis fe M eb → HW ty → SpineR m co cn acc → spTop m = co + cn →
      (∀ j, j < co → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      BKept m₀ m → PoolGrew m₀ m →
      ∀ er, er.cls ≠ 0 → inferSpineE.loop1 p k m mode vis d ty ao an co cn i = .error er →
      ErrClaim (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) acc args i.toNat)
        a er := by
  intro k
  induction k with
  | zero =>
    intro _ m a M ty i cn acc _ _ _ _ _ _ _ _ er hk0 hF
    rw [inferSpineE.loop1.eq_1] at hF; cases hF; exact absurd rfl hk0
  | succ k ih =>
    intro hkN m a M ty i cn acc hS ht hacc htop hb hsz hbk hpg er hk0 hF
    rw [inferSpineE.loop1.eq_2] at hF
    have hspn := hS.spn
    have hco_le : co.toNat + cn.toNat ≤ (m.arr64 SPN).size := hacc.bound
    have hcn64 : co.toNat + cn.toNat < 2 ^ 64 := by omega
    have hadd : (co + cn).toNat = co.toNat + cn.toNat := addW _ _ hcn64
    have hspT : (spTop m).toNat = co.toNat + cn.toNat := by rw [htop, hadd]
    have har : SpineR m ao an args := har₀.keepT co hsz hb hlo (hsz ▸ hspn)
    have h0 : (0 : Word).toNat = 0 := rfl
    have hkeep : ∀ {m₂ : Mem}, StackKept m m₂ → (∀ j, j < co → spW m₂ j = spW m₀ j) := by
      intro m₂ hSt j hj
      have hj' : j < spTop m := by
        rw [htop, UInt64.lt_iff_toNat_lt, hadd]
        have := UInt64.lt_iff_toNat_lt.mp hj; omega
      exact (hSt.below j hj').trans (hb j hj)
    by_cases hlt : i < an
    · rw [if_pos hlt] at hF
      have hlt' : i.toNat < args.size := by rw [har₀.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have hit : (i.toNat).toUInt64 = i := by simp
      have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
        have h := har.get i.toNat hlt'; rwa [hit] at h
      have hvv : HW (spW m (ao + i)) := by
        have h := har.lt i.toNat (by rw [← har.size]; exact hlt'); rwa [hit] at h
      have hi1 := succ_toNat_of_lt hlt
      by_cases ht6 : ty >>> 28 = 6
      · rw [if_pos ht6] at hF
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i c1
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i c2
        have hv : viewOK m ty FORALL := ⟨c1, UInt64.not_le.mp c2⟩
        obtain ⟨-, hdom, hbody⟩ := view_forall m a hS.arena.1 ty ht hv ht6
        have hvb := viewBind_forall m a hS.arena.1 ty ht hv ht6
        cases h1 : callE p k "inst_list" [tfld m FORALL (tierW ty) (idxW ty) 0, co, cn, 0] m with
        | error e1 =>
          rw [h1, inferSpineE.k_inst_list_2.none] at hF; cases hF
          exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
        | ok q =>
        obtain ⟨r₁, m₁⟩ := q
        rw [h1, inferSpineE.k_inst_list_2.arm1] at hF
        have hinst := hil k ⟨m, Locals.init []⟩ a dn vis fe M eb _ co cn 0 acc hS hdom hacc
          (by rw [hspT]; exact Nat.le_refl _)
        obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW hinst (callW_of_callE h1)
        rw [h0] at hok1 hres1 hS₁
        have hpre : (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) acc args
            i.toNat).run a =
            ((coreKnot (decMode mode) fe id F).infer d.toNat (decE (spW m (ao + i))) >>= fun ta =>
              defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE (spW m (ao + i))) ta
                (decE (r₁.headD 0)) >>= fun b =>
              if (!b) = true then fail (.invalid "application type mismatch")
              else inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat
                (decE (tfld m FORALL (tierW ty) (idxW ty) 1)) (acc.push (decE (spW m (ao + i)))) args
                (i.toNat + 1)).run
              (AM.st (instantiateListFast coreWalkFuel (decE (tfld m FORALL (tierW ty) (idxW ty) 0))
                acc 0) a) := by
          rw [inferSpine]
          simp only [hlt', dite_true, tag_fa_beq ty ht, ht6, decide_true, ite_true, StateT.run_bind,
            viewBind_run', hvb, except_ok_bind, hxi]
          rw [AM.run_of_ok _ _ hok1, except_ok_bind, hres1]; rfl
        cases h2 : callE p k "infer_spine_arg" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), r₁.headD 0]
            m₁ with
        | error e2 =>
          rw [h2, inferSpineE.k_infer_spine_arg.none] at hF; cases hF
          refine ErrClaim.of_run_eq' (fun ce h => hpre.trans h) (spineArg_errClaim _ _ _ _ _ _ _ ?_)
          exact CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩) (inferSpineArg_anyE p hp hkp hq he hda
            k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) ⟨m₁, Locals.init []⟩ _
            dn vis fe M₁ eb mode d _ (r₁.headD 0) ⟨hS₁, hmode, heb⟩ hvv hrw1) h2
        | ok q =>
        obtain ⟨r₂, m₂⟩ := q
        rw [h2, inferSpineE.k_infer_spine_arg.eq_2] at hF
        have harg := CoreSpec.of_callW (inferSpineArg_any p hp hkp hq he k (hk.mono (by omega)) F
          (by omega) (by omega) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d _ (r₁.headD 0)
          ⟨hS₁, hmode, heb⟩ hvv hrw1) (callW_of_callE h2)
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, -, -⟩ := harg
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i g4
        rw [inferSpineE.j1.eq_def] at hF
        have g5 := lt_of_not_len64_le hS₂.spn g4
        have hSt12 := hSt₁.trans hSt₂
        have hacc₂ : SpineR m₂ co cn acc :=
          hacc.keep hSt12.size hSt12.below (by rw [hspT]; exact Nat.le_refl _) hspn
        obtain ⟨hacc', htop', hb', hsz', -, hbk', hpg'⟩ := spPush_step hS₂.spn hacc₂ (hkeep hSt12)
          (hSt12.size.trans hsz) (hbk.trans hSt12.bstk) (hpg.trans hSt12.pool) hS₂.ctl136 g5 hvv
        have hS' := hS₂.frame_stk (spnCtl_frame m₂ (co + cn) (spW m (ao + i)) (co + (cn + 1)))
          (by simp) (by simp)
        have hih := ih (by omega) _ _ M₂ _ (i + 1) (cn + 1) _ hS' hbody hacc' htop' hb' hsz' hbk' hpg'
          er hk0 hF
        rw [hi1] at hih
        refine ErrClaim.of_run_eq' (fun ce h => hpre.trans ?_) hih
        rw [← h]
        exact spineArg_run _ _ _ _ _ _ _ (by rw [AM.run_of_ok _ _ hok2])
      · rw [if_neg ht6] at hF
        have hnfa : ((decE ty).tag == ETag.forallE) = false := by rw [tag_fa_beq ty ht]; simp [ht6]
        cases h1 : callE p k "inst_list" [ty, co, cn, 0] m with
        | error e1 =>
          rw [h1, inferSpineE.k_inst_list_3.none] at hF; cases hF
          exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
        | ok q =>
        obtain ⟨r₁, m₁⟩ := q
        rw [h1, inferSpineE.k_inst_list_3.arm1] at hF
        have hinst := hil k ⟨m, Locals.init []⟩ a dn vis fe M eb ty co cn 0 acc hS ht hacc
          (by rw [hspT]; exact Nat.le_refl _)
        obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW hinst (callW_of_callE h1)
        rw [h0] at hok1 hres1 hS₁
        have hpre : (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) acc args
            i.toNat).run a =
            ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE (r₁.headD 0)) >>= fun w =>
              if w.tag == ETag.forallE then
                (viewBind w >>= fun x => match x with
                  | none => failDanglingE
                  | some (dom, body) =>
                    (coreKnot (decMode mode) fe id F).infer d.toNat args[i.toNat] >>= fun ta =>
                    defeqArg (coreKnot (decMode mode) fe id F) d.toNat args[i.toNat] ta dom >>= fun b =>
                    if (!b) = true then fail (.invalid "application type mismatch")
                    else inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat body #[args[i.toNat]]
                      args (i.toNat + 1))
              else fail (.invalid "function expected")).run
              (AM.st (instantiateListFast coreWalkFuel (decE ty) acc 0) a) := by
          rw [inferSpine]
          simp only [hlt', dite_true, hnfa, Bool.false_eq_true, ite_false, StateT.run_bind,
            AM.run_of_ok _ _ hok1, except_ok_bind]
          rw [hres1]; rfl
        cases h2 : callE p k "whnf" [mode, vis, d, r₁.headD 0] m₁ with
        | error e2 =>
          rw [h2, inferSpineE.k_whnf.none] at hF; cases hF
          refine ErrClaim.of_run_eq' (fun ce h => hpre.trans h) ?_
          exact ErrClaim.bind_left (CoreSpecE.of_callE
            (s₀ := ⟨m₁, Locals.init []⟩) ((hkE k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
              mode d (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) h2)
        | ok q =>
        obtain ⟨r₂, m₂⟩ := q
        rw [h2] at hF
        have hw := CoreSpec.of_callW ((hk k (by omega)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
          mode d (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) (callW_of_callE h2)
        obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := hw
        have hpre2 : (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) acc args
            i.toNat).run a =
            (if (decE (r₂.headD 0)).tag == ETag.forallE then
                (viewBind (decE (r₂.headD 0)) >>= fun x => match x with
                  | none => failDanglingE
                  | some (dom, body) =>
                    (coreKnot (decMode mode) fe id F).infer d.toNat args[i.toNat] >>= fun ta =>
                    defeqArg (coreKnot (decMode mode) fe id F) d.toNat args[i.toNat] ta dom >>= fun b =>
                    if (!b) = true then fail (.invalid "application type mismatch")
                    else inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat body #[args[i.toNat]]
                      args (i.toNat + 1))
              else fail (.invalid "function expected")).run
              (AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE (r₁.headD 0)))
                (AM.st (instantiateListFast coreWalkFuel (decE ty) acc 0) a)) := by
          rw [hpre, StateT.run_bind, AM.run_of_ok _ _ hok2, except_ok_bind, hres2]; rfl
        by_cases g1 : r₂.headD 0 >>> 28 ≠ 6
        · rw [inferSpineE.k_whnf.abort1 _ _ _ _ _ _ _ _ _ _ _ _ g1] at hF; cases hF
          have hfa : ((decE (r₂.headD 0)).tag == ETag.forallE) = false := by
            rw [tag_fa_beq _ hrw2]; simpa using g1
          refine ErrClaim.of_error (ce := .invalid "function expected") (hpre2.trans ?_) rfl
          rw [hfa]; rfl
        have g1' : r₂.headD 0 >>> 28 = 6 := by simpa using g1
        rw [inferSpineE.k_whnf.eq_2] at hF
        simp only [if_neg g1] at hF
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i g2
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i g3
        have hv : viewOK m₂ (r₂.headD 0) FORALL := ⟨g2, UInt64.not_le.mp g3⟩
        obtain ⟨-, hdom, hbody⟩ := view_forall m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 hv g1'
        have hvb := viewBind_forall m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 hv g1'
        have hfa : ((decE (r₂.headD 0)).tag == ETag.forallE) = true := by
          rw [tag_fa_beq _ hrw2]; exact decide_eq_true g1'
        have hpre3 : (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) acc args
            i.toNat).run a =
            ((coreKnot (decMode mode) fe id F).infer d.toNat (decE (spW m (ao + i))) >>= fun ta =>
              defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE (spW m (ao + i))) ta
                (decE (tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)) >>= fun b =>
              if (!b) = true then fail (.invalid "application type mismatch")
              else inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat
                (decE (tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 1))
                #[decE (spW m (ao + i))] args (i.toNat + 1)).run
              (AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE (r₁.headD 0)))
                (AM.st (instantiateListFast coreWalkFuel (decE ty) acc 0) a)) := by
          rw [hpre2]
          simp only [hfa, ite_true, StateT.run_bind, viewBind_run', hvb, except_ok_bind, hxi]
        cases h3 : callE p k "infer_spine_arg" [mode, vis, d, rdW (m.arr64 SPN) (ao + i),
            tfld m₂ FORALL (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0] m₂ with
        | error e3 =>
          rw [h3, inferSpineE.k_infer_spine_arg_2.none] at hF; cases hF
          refine ErrClaim.of_run_eq' (fun ce h => hpre3.trans h) (spineArg_errClaim _ _ _ _ _ _ _ ?_)
          exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) (inferSpineArg_anyE p hp hkp hq he hda
            k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩ _
            dn vis fe M₂ eb mode d _ _ ⟨hS₂, hmode, heb⟩ hvv hdom) h3
        | ok q =>
        obtain ⟨r₃, m₃⟩ := q
        rw [h3, inferSpineE.k_infer_spine_arg_2.eq_2] at hF
        have harg := CoreSpec.of_callW (inferSpineArg_any p hp hkp hq he k (hk.mono (by omega)) F
          (by omega) (by omega) ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d _ _
          ⟨hS₂, hmode, heb⟩ hvv hdom) (callW_of_callE h3)
        obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, -, -⟩ := harg
        split at hF
        · exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
        rename_i g4
        rw [inferSpineE.j1.eq_def, spPush_zero] at hF
        have g5 := lt_of_not_len64_le hS₃.spn g4
        have hSt13 := hSt₁.trans (hSt₂.trans hSt₃)
        have hacc0 := SpineR.empty m₃ co (by omega)
        obtain ⟨hacc', htop', hb', hsz', -, hbk', hpg'⟩ := spPush_step (cn := 0) hS₃.spn hacc0
          (hkeep hSt13) (hSt13.size.trans hsz) (hbk.trans hSt13.bstk) (hpg.trans hSt13.pool) hS₃.ctl136
          (by simpa using g5) hvv
        have hS' := hS₃.frame_stk (spnCtl_frame m₃ (co + 0) (spW m (ao + i)) (co + (0 + 1)))
          (by simp) (by simp)
        have hih := ih (by omega) _ _ M₃ _ (i + 1) 1 _ hS' hbody hacc' htop' hb' hsz' hbk' hpg' er hk0 hF
        rw [hi1] at hih
        refine ErrClaim.of_run_eq' (fun ce h => hpre3.trans ?_) hih
        rw [← h]
        exact spineArg_run _ _ _ _ _ _ _ (by rw [AM.run_of_ok _ _ hok3])
    · rw [if_neg hlt] at hF; cases hF

/-- **`infer_spine`'s verdicts** (the error half of `inferSpine_refines`). -/
theorem inferSpine_refinesE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hda : DefeqArgE p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ht : HW ty) (har : SpineR s₀.mem ao an args)
    (hlo : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpecE p (n + 1) "infer_spine" [mode, vis, d, ty, ao, an]
      (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) #[] args 0) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferSpine_specE p hq.spine (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ty ao an) hc0 (Err.code_ne_of_cls hk0)
  rw [inferSpineE.eq_2] at hW
  have hS := hs.rel
  split at hW
  · exact absurd hW (fun h => cls_abort0 hk0 (Except.error.inj h))
  rename_i hc
  have hcle : (rdW (s₀.mem.arr64 CTL) 136).toNat ≤ (s₀.mem.arr64 SPN).size := len64_not_lt hS.spn hc
  cases hL : inferSpineE.loop1 p (n + 1) s₀.mem mode vis d ty ao an (rdW (s₀.mem.arr64 CTL) 136) 0 0
    with
  | error e' =>
    rw [hL, inferSpineE.k_loop1.none] at hW; cases hW
    exact spLoopE_ref p hp hkp hq he hda hil hnv n hk hkE F hF hn dn vis fe mode d ao an args eb _
      hs.mode4 hs.eb_mode s₀.mem har hlo (n + 1) (Nat.le_refl _) s₀.mem a₀ M ty 0 0 #[] hS ht
      (SpineR.empty _ _ hcle) (by simp [spTop]) (fun _ _ => rfl) rfl (BKept.refl _)
      (PoolGrew.refl _) _ hk0 hL
  | ok q =>
    obtain ⟨ty', cn', m'⟩ := q
    rw [hL, inferSpineE.k_loop1.arm1] at hW
    cases h1 : callE p n "inst_list" [ty', rdW (s₀.mem.arr64 CTL) 136, cn', 0] m' with
    | error e1 =>
      rw [h1, inferSpineE.k_inst_list.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
    | ok q => rw [h1, inferSpineE.k_inst_list.arm1] at hW; cases hW

/-! ## `infer_app` -/

l_model inferApp_specE (p : Prog) (hf : p.lookup "infer_app" = some inferAppL)
  fns [hf ↦ inferAppE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

/-- `infer_spine`'s error claim at every L fuel up to `n + 1`. -/
theorem inferSpine_anyE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (he : IsEagerReduceH p) (hda : DefeqArgE p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty ao an : Word) (args : Array EIdx), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p n "infer_spine" [mode, vis, d, ty, ao, an]
      (inferSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) #[] args 0) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hkE, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, ty, ao, an, args, hs, ht, har, hlo =>
      inferSpine_refinesE p hp hkp hq he hda hil hnv n (hk.mono (by omega)) (hkE.mono (by omega)) F
        (by omega) (by omega) s₀ a₀ dn vis fe M eb mode d ty ao an args hs ht har hlo

/-- **`infer_app`'s verdicts**: the head's type (the `infer` slot), the spine's;
`head_and_args` claims nothing. -/
theorem inferApp_refinesE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p) (hq : SpineFProg p)
    (hsp : SpineProg p) (he : IsEagerReduceH p) (hda : DefeqArgE p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hHe : HW e)
    (h4 : e >>> 28 = 4) :
    CoreSpecE p (n + 1) "infer_app" [mode, vis, d, e]
      (inferApp (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferApp_specE p hq.app (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d e) hc0 (Err.code_ne_of_cls hk0)
  simp only [inferAppE] at hW
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  cases hc1 : callE p n "head_and_args" [e] s₀.mem with
  | error e1 =>
    rw [hc1, inferAppE.k_head_and_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "head_and_args" (by simp)) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW; simp only [inferAppE.k_head_and_args] at hW
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, hha, hxs⟩ := triple_of_callE
    (headAndArgs_app p hsp n s₀ a₀ hS.arena.1 e hHe h4 hS.spn) hc1
  rw [ht₁] at hf₁ hg₁ htop1 hxs
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hb1 := hxs.bound
  have hspn₁ := hS₁.spn
  have hadd : (r₁.tail.headD 0 + r₁.tail.tail.headD 0).toNat =
      (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := addW _ _ (by omega)
  have htopN : (spTop m₁).toNat = (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := by
    rw [htop1, ← ho1, hadd]
  simp only [inferApp]
  refine ErrClaim.bind_right hha ?_
  cases hc2 : callE p n "infer" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [hc2, inferAppE.k_infer.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      (hKE.infer F ⟨m₁, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₁.headD 0) hF hn
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw) hc2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW; simp only [inferAppE.k_infer] at hW
  have h₂ := CoreSpec.of_callW (hK.infer F ⟨m₁, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw) (callW_of_callE hc2)
  obtain ⟨M₂, hS₂, hK₂, hSt₂⟩ := h₂.2.1
  have hxs₂ : SpineR m₂ (r₁.tail.headD 0) (r₁.tail.tail.headD 0) xs :=
    hxs.keep hSt₂.size hSt₂.below (by rw [htopN]; exact Nat.le_refl _) hspn₁
  refine ErrClaim.bind_ref h₂ ?_
  cases hc3 : callE p n "infer_spine" [mode, vis, d, r₂.headD 0, r₁.tail.headD 0,
      r₁.tail.tail.headD 0] m₂ with
  | error e3 =>
    rw [hc3, inferAppE.k_infer_spine.none] at hW; cases hW
    exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) (inferSpine_anyE p hp hkp hq he hda hil hnv n hk
      hkE F hF hn ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d (r₂.headD 0) _ _ xs
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.2.2.2 hxs₂ (by rw [hSt₂.1, htopN]; exact Nat.le_refl _)) hc3
  | ok q => rw [hc3] at hW; simp [inferAppE.k_infer_spine] at hW

end L.Arena
