module

public import ConAgua.Arena.RefECore
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.KnotE
public import ConAgua.Verdict.WhnfModels2E
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.L.WordOff
import ConAgua.Arena.Inst1Refine
import ConAgua.Arena.WhnfCoreProj
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.RecLayout.CIDec
import all ConAgua.Arena.WhnfCore

@[expose] public section

/-!
# `whnf_app` refines `whnfApp` (split from `WhnfCoreApp.lean`)

One refinement over the loop's unified model (`whnfAppE`, `Verdict/WhnfModels2E.lean`), both
outcomes, by induction on the L fuel (`appLoop_ref`, `app_ref`); its errors are `iota_rec_at`'s
(`AppG`). The loop's ι step `whnf_app_iota` (the recursor's lookup) over its own unified model
(`whnfAppIotaE`, `appIota_ref`). `WhnfCoreApp.lean` has the helpers and `beta_peel`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`whnf_app_iota`'s model** (generated, both outcomes): the recursor's lookup, then
`iota_rec_at` through its run. -/
l_model whnfAppIotaE_spec (p : Prog) (hf : p.lookup "whnf_app_iota" = some whnfAppIotaL)
  fns [hf ↦ whnfAppIotaE list]
  specs [callW_spec p n "env_find", callW_spec p n "ls_node"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- The `viewConst` projection of a `const` handle past its view checks. -/
theorem viewConst_w (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) :
    a.store.viewConst (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0),
      decI (tfld m CONST (tierW h) (idxW h) 1)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  simp only [EStore.viewConst, EStore.persGetConst]
  rw [proj_tier m a hR h hh (fun t i => t.getConst i) hv.1]
  simp only [ETables.getConst, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
  rw [hk]
  simp [hn, hu, decI_word]

/-- The next spine node of the walk: the saved node (`same`), else `mk_app(v, a)`. -/
def apW (p : Prog) (k : Nat) (m : Mem) (v same a node : Word) : Option (Word × Mem) :=
  if same ≠ 0 then some (node, m)
  else match callW p k "mk_app" [v, a] m with
    | none => none
    | some (r, m₁) => some (r.headD 0, m₁)

/-- The twin's `whnfApp` after the ι step's answer. -/
def appStepT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (hd ap : EIdx)
    (va : Array EIdx) (same2 : Bool) (args nodes : Array EIdx) (i : Nat) (step : Option EIdx) :
    AM WhnfStep :=
  match step with
  | none => whnfApp mode r fe depth ap hd va same2 args nodes (i + 1)
  | some e2 => do
    let e3 ← mkAppNFrom e2 args (i + 1)
    pure (WhnfStep.cont e3)

theorem whnfApp_nolam (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (v hd : EIdx) (vargs : Array EIdx) (same : Bool) (args nodes : Array EIdx) (i : Nat)
    (hi : i < args.size) (hv : (v.tag == ETag.lam) = false) :
    whnfApp mode r fe depth v hd vargs same args nodes i =
      (show AM WhnfStep from do
        let ap ← internAppRebuilt nodes[i]! same v args[i]
        let step ← whnfAppIota mode r fe depth hd (vargs.push args[i]) (vargs.push args[i]).size
        appStepT mode r fe depth hd ap (vargs.push args[i]) (ap == nodes[i]!) args nodes i step) := by
  rw [whnfApp]
  simp only [hi, dite_true, hv, Bool.false_eq_true, ite_false]
  rfl

section appRef0
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **The next spine node refines `internAppRebuilt`**: the saved node, or `mk_app`'s interning. -/
theorem apW_ref (k : Nat) (m : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb : Word) (hS : CoreS dn m a vis fe MM eb)
    (v same aW nW : Word) (_hv : HW v) (_ha : HW aW) (hnW : HW nW) (ap : Word) (m₁ : Mem)
    (h : apW p k m v same aW nW = some (ap, m₁)) :
    ∃ a₁, (internAppRebuilt (decE nW) (same != 0) (decE v) (decE aW)).run a = .ok (decE ap, a₁) ∧
      CoreS dn m₁ a₁ vis fe MM eb ∧ StackKept m m₁ ∧ HW ap := by
  unfold apW at h
  by_cases hs : same ≠ 0
  · simp only [hs, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb : (same != 0) = true := by simpa using hs
    refine ⟨a, ?_, hS, StackKept.refl _, hnW⟩
    simp only [internAppRebuilt, hb, ite_true]; rfl
  · simp only [hs, ↓reduceIte] at h
    have hs' : same = 0 := by simpa using hs
    have hb : (same != 0) = false := by simp [hs']
    cases hc : callW p k "mk_app" [v, aW] m with
    | none => rw [hc] at h; simp at h
    | some q =>
    obtain ⟨r, m'⟩ := q
    rw [hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hok, hD, hres, hfr, hhw⟩ := callW_mkApp p hp.spine k ⟨m, Locals.init []⟩ a hS.arena
      v aW r m' hc
    have hrun := AM.run_of_ok _ _ hok
    refine ⟨AM.st (internE (.app (decE v) (decE aW))) a, ?_, ?_, StackKept.of_app_frame hfr, hhw⟩
    · simp only [internAppRebuilt, hb, Bool.false_eq_true, ite_false]
      rw [hrun, hres]
    · exact hS.of_app hD (Keeps.run (keeps_cpl_internApp _ _) hrun) hfr

end appRef0
/-! ## The ι step's claim and what the `app` arm's errors assume -/

/-- `iota_rec_at`'s error claim at fuel `N + 1` (the shape of `IotaRecAtOK`: the caller's
record `q`, exactly `mI + 1` arguments). -/
def IotaRecAtE (p : Prog) : Prop :=
  ∀ N, KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d c us q so sn : Word) (xs : Array EIdx) (cv : IConstantVal) (mI rP : Nat)
    (isK : Bool) (rules : List IRecRule), N ≤ F → N ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW c → HW us →
    decCI (erecP s₀.mem) q.toNat = some (.recInfo cv mI rP isK rules) →
    fe.find? (decI c) = some (.recInfo cv mI rP isK rules) →
    SpineR s₀.mem so sn xs → xs.size = mI + 1 →
    so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p (N + 1) "iota_rec_at" [mode, vis, d, c, us, q, so, sn]
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
        (decI c) (decI us) cv mI rP isK rules xs) s₀ a₀

/-- **What the `app` arm's errors assume** at L fuel `n` (`whnf_app`, `whnf_core_app2`,
`whnf_core_app`): the knot's slots' claims and `iota_rec_at`'s. -/
structure AppG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  iota : IotaRecAtE p
  /-- the verdict closure (`whnf_app_iota`'s error half: its lookups have `Option` models) -/
  nv : closedNV p _root_.L.Checker.nvFns = true

theorem AppG.mono {p : Prog} {n m : Nat} (h : AppG p n) (hm : m ≤ n) : AppG p m :=
  ⟨h.knot.mono hm, h.iota, h.nv⟩

/-! ## `whnf_app_iota` refines `whnfAppIota`, both outcomes -/

section appIota
variable (p : Prog) (hp : WhnfCoreProg p) (hcc : CoreCallees p)

include hp hcc in
/-- **`whnf_app_iota` refines `whnfAppIota`, both outcomes** (the spine loop's ι step at the
accumulated slice `(vo, vn)`): the recursor's lookup, then `iota_rec_at` at exactly `mI + 1`
arguments; its errors are `iota_rec_at`'s (`AppG`). -/
@[refines ConRon.Arena.whnfAppIota]
theorem appIota_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d hd vo vn : Word) (va : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hhd : HW hd) (hva : SpineR s₀.mem vo vn va)
    (hlo : vo.toNat + vn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (AppG p n) (whnfAppIotaE p (n + 1) s₀.mem mode vis d hd vo vn)
      (whnfAppIota (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
        (decE hd) va va.size) a₀ (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  have hS := hs.rel
  have hR := hS.arena.base
  have hW0 : HW 0 := by unfold HW; decide
  have hnone : ∀ (m' : Mem), m' = s₀.mem →
      CorePost decOptR dn s₀.mem vis fe MM eb ResW ([0, 0], m') none a₀ := fun m' hm => by
    subst hm; exact CorePost.ret hS (by simp [decOptR, decOpt]) ⟨hW0, hW0⟩
  unfold whnfAppIota
  by_cases g3 : tagW hd ≠ 3
  · simp only [whnfAppIotaE, g3, ne_eq, not_false_eq_true, ↓reduceIte]
    refine RefE.ret ?_ (hnone _ rfl)
    simp only [decE_tag_const_beq hd hhd, show ¬ tagW hd = 3 from g3, decide_false,
      Bool.false_eq_true, ↓reduceIte]; rfl
  have g3' : tagW hd = 3 := by simpa using g3
  simp only [whnfAppIotaE, g3', ne_eq, not_true_eq_false, ↓reduceIte]
  refine RefE.abort0 (by decide) fun c1 => ?_
  refine RefE.abort0 (by decide) fun c2 => ?_
  have hvo : viewOK s₀.mem hd CONST := ⟨c1, by simpa using c2⟩
  have hvc := viewConst_w s₀.mem a₀ hR hd hhd hvo
  obtain ⟨_, _, -, -, -, hw0, hw1⟩ := view_const_words s₀.mem a₀ hR hd hhd hvo g3'
  simp only [decE_tag_const_beq hd hhd, g3', decide_true, ↓reduceIte]
  refine RefE.bind_right (show (viewConst (decE hd)).run a₀ = .ok (_, a₀) from rfl) ?_
  rw [hvc]
  dsimp only
  generalize hc0 : tfld s₀.mem CONST (tierW hd) (idxW hd) 0 = cw at hw0 ⊢
  generalize hu0 : tfld s₀.mem CONST (tierW hd) (idxW hd) 1 = uw at hw1 ⊢
  cases n with
  | zero =>
    rw [callW_zero, liftE_none, whnfAppIotaE.k_env_find.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  refine RefE.onlySim (fun _ => whnfAppIotaE.k_env_find.eq_1 ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  obtain ⟨s', hs', h1', -, hfind, hdec⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (envFind_refines p hp.envrow hp.baserow hp.envfind (N + 1) _ vis _ hS.env hw0) h1
  have hm₁ : s₀.mem = m₁ := (hs'.symm.trans h1').symm
  subst hm₁
  dsimp only [whnfAppIotaE.k_env_find]
  by_cases f0 : r₁.headD 0 = 0
  · rw [ite_eq_left f0]
    have hn : fe.find? (decI cw) = none := by rw [hfind]; simp only [envFound, f0, ↓reduceIte]
    rw [hn]; exact RefE.ret rfl (hnone _ rfl)
  rw [ite_eq_right f0]
  obtain ⟨ci, hci⟩ := hdec f0
  have hfind' : fe.find? (decI cw) = some ci := by
    rw [hfind]; simp only [envFound, f0, ↓reduceIte]; exact hci
  rw [hfind']
  by_cases k5 : erRd s₀.mem (r₁.tail.headD 0) ≠ 5
  · erw [ite_eq_left k5]
    have hnr := (decCI_rec_rd (erRdOK s₀.mem) hci).2 k5
    cases ci <;> first | exact absurd rfl (hnr _ _ _ _ _) | exact RefE.ret rfl (hnone _ rfl)
  have k5 : erRd s₀.mem (r₁.tail.headD 0) = 5 := Classical.not_not.mp k5
  erw [ite_eq_right (by simpa [erRd] using k5)]
  obtain ⟨cv, rules, rfl, hcv, -⟩ := (decCI_rec_rd (erRdOK s₀.mem) hci).1 k5
  obtain ⟨-, -, -, hlen, -, -⟩ := decCV_rd_ci (erRdOK s₀.mem) hcv
  generalize hq : r₁.tail.headD 0 = q at *
  dsimp only
  have hvsz : va.size = vn.toNat := hva.size
  by_cases v0 : vn = 0
  · rw [ite_eq_left v0]
    rw [ite_eq_left (by rw [hvsz, v0]; simp)]
    exact RefE.ret rfl (hnone _ rfl)
  rw [ite_eq_right v0]
  have v0' : vn.toNat ≠ 0 := fun h => v0 (UInt64.toNat_inj.mp (by simpa using h))
  have hsub : (vn - 1).toNat = vn.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  generalize hkw : erRd s₀.mem (q + CI.recMajor) = kw at *
  have hkw' := hkw
  simp only [erRd] at hkw'
  by_cases m1 : vn - 1 ≠ kw
  · erw [ite_eq_left (by rw [hkw']; exact m1)]
    rw [ite_eq_left (by
      rw [hvsz]; intro h; apply m1; apply UInt64.toNat_inj.mp; rw [hsub]; omega)]
    exact RefE.ret rfl (hnone _ rfl)
  have m1 : vn - 1 = kw := Classical.not_not.mp m1
  erw [ite_eq_right (by rw [hkw']; exact fun h => h m1)]
  have hsz1 : va.size = kw.toNat + 1 := by
    rw [hvsz, ← m1, hsub]; omega
  rw [ite_eq_right (fun h => h hsz1)]
  refine RefE.onlySim (fun _ => whnfAppIotaE.k_ls_node.eq_1 ..) (fun _ _ h => h) fun rl m2 c2 => ?_
  obtain ⟨t2, ht2, hs2, hne2, hr2⟩ := triple_of_callW (lsNode_spec p hp.lsn (N + 1) ⟨s₀.mem, Locals.init []⟩ _) c2
  have hm2 : s₀.mem = m2 := by rw [← ht2, hs2]
  subst hm2
  obtain ⟨o, l, hol⟩ : ∃ o l, rl = [o, l] := by
    rcases lsNodeW_cases s₀.mem uw with h' | ⟨o, l, h'⟩
    · rw [hr2] at hne2; exact absurd h' hne2
    · exact ⟨o, l, by rw [hr2]; exact h'⟩
  have hvl := lsNodeW_viewLen hR hw1 (by rw [← hr2, hol])
  subst hol
  have hlr : (viewLsLen (decI uw)).run a₀ = .ok (some l.toNat, a₀) := by
    show Except.ok (a₀.store.lss.viewLen _, a₀) = _; rw [hvl]
  refine RefE.bind_right hlr ?_
  dsimp only [whnfAppIotaE.k_ls_node]
  simp only [List.tail_cons, List.headD_cons]
  by_cases u1 : l ≠ erRd s₀.mem (q + (CI.cv + CV.lpsLen))
  · erw [ite_eq_left (by simpa [erRd] using u1)]
    rw [ite_eq_left (by rw [hlen]; exact fun h => u1 (UInt64.toNat_inj.mp h))]
    exact RefE.ret rfl (hnone _ rfl)
  have u1 : l = erRd s₀.mem (q + (CI.cv + CV.lpsLen)) := Classical.not_not.mp u1
  erw [ite_eq_right (by simpa [erRd] using u1)]
  rw [ite_eq_right (by rw [hlen, u1]; exact fun h => h rfl)]
  have hpre : SlotPre ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  rw [← bind_pure (iotaRecAt _ _ _ _ _ _ _ _ _ _ _ _)]
  refine RefE.bind_callE (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => whnfAppIotaE.k_iota_rec_at.eq_1 ..)
    (hcc.iota N (hk.mono (by omega)) F _ a₀ dn vis fe MM eb mode d cw uw q _ _ va cv _ _ _ rules (by omega)
      (by omega) hpre hw0 hw1 hci hfind' hva hsz1 hlo)
    (fun hG => hG.iota N (hk.mono (by omega)) (hG.knot.mono (by omega)) F _ a₀ dn vis fe MM eb mode d cw uw q
      _ _ va cv _ _ _ rules (by omega) (by omega) hpre hw0 hw1 hci hfind' hva hsz1 hlo)
    fun r₃ m₃ _ hI => ?_
  obtain ⟨-, hA, hres, hrw⟩ := hI
  dsimp only [whnfAppIotaE.k_iota_rec_at]
  exact RefE.ret rfl ⟨hA, rfl, hrw⟩

end appIota

/-- The stack top put back after a run that kept the stack below it (the store's bound not
needed: `StackKept.restoreG'`). -/
theorem StackKept.restoreTop {m₀ m : Mem} (hb : ∀ j : Word, j < spTop m₀ → spW m j = spW m₀ j)
    (hle : spTop m₀ ≤ spTop m) (hsz : (m.arr64 SPN).size = (m₀.arr64 SPN).size) (hbk : BKept m₀ m)
    (hpg : PoolGrew m₀ m) : StackKept m₀ (m.set64 CTL 136 (spTop m₀)) :=
  StackKept.restoreG' ⟨hle, hsz, hb, hbk, hpg⟩

/-! ## `whnf_app` refines `whnfApp`, both outcomes -/

theorem apW_same {p : Prog} {k : Nat} {m : Mem} {v same aW nW : Word} (hs : same ≠ 0) :
    apW p k m v same aW nW = some (nW, m) := by
  simp [apW, hs]

section appRef
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)

include hp hcc in
/-- **The `whnf_app` loop refines `whnfApp`, both outcomes**, by induction on the L fuel: its
errors are `iota_rec_at`'s (`AppG`). -/
theorem appLoop_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (mode vis d hd vo ao an top : Word) (args nodes : Array EIdx)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (eb : Word) (m₀ : Mem)
    (hmode : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hhd : HW hd)
    (har₀ : SpineR m₀ ao an args) (hno₀ : SpineR m₀ (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) (hvot : vo.toNat ≤ top.toNat)
    (htop0 : top = spTop m₀) (hspn0 : (m₀.arr64 SPN).size < 2 ^ 63) :
    ∀ (k : Nat), k ≤ n + 1 → ∀ (a : AState) (m : Mem) (v vn same i : Word) (va : Array EIdx)
      (MM : ModeMaps),
      CoreS dn m a vis fe MM eb → HW v → SpineR m vo vn va → spTop m = vo + vn →
      top.toNat ≤ (vo + vn).toNat → (∀ j : Word, j < top → spW m j = spW m₀ j) →
      (m.arr64 SPN).size = (m₀.arr64 SPN).size → BKept m₀ m → PoolGrew m₀ m →
      RefE (AppG p n)
        (whnfAppE.k_loop1 p top (whnfAppE.loop1 p k m mode vis d v hd vo vn same ao an i top))
        (whnfApp (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE v) (decE hd) va
          (same != 0) args nodes i.toNat) a (CorePost decStep dn m₀ vis fe MM eb ResW) := by
  subst htop0
  intro k
  induction k with
  | zero =>
    intro _ a m v vn same i va MM _ _ _ _ _ _ _ _ _
    simp only [whnfAppE.loop1]; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro hkn a m v vn same i va MM hS hv hva htop htv hb hsz hbk hpg
    have hspn := hS.spn
    have hvn64 : vo.toNat + vn.toNat < 2 ^ 64 := by have := hva.bound; omega
    have hadd : (vo + vn).toNat = vo.toNat + vn.toNat := L.toNat_add_of_lt _ _ hvn64
    have hlt_args : args.size = an.toNat := har₀.size
    have hle0 : spTop m₀ ≤ spTop m := by
      rw [UInt64.le_iff_toNat_le, htop]; exact htv
    simp only [whnfAppE.loop1]
    by_cases hlt : ¬ i < an
    · rw [ite_eq_right hlt]
      have hnlt : ¬ i.toNat < args.size := by
        rw [hlt_args]; exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      have hrun : (whnfApp (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE v)
          (decE hd) va (same != 0) args nodes i.toNat).run a = .ok (.done (decE v), a) := by
        rw [whnfApp]; simp only [hnlt, dite_false]; rfl
      exact RefE.ret hrun ⟨⟨MM, hS.frame_stk (MemFrame.setCtl m 136 _) (by simp) (by simp),
        KeptAll.refl _ _, StackKept.restoreTop hb hle0 hsz hbk hpg⟩, by simp [decStep],
        ⟨by simp [HW], hv⟩⟩
    have hlt : i < an := Classical.not_not.mp hlt
    rw [ite_eq_left hlt]
    have hlt' : i.toNat < args.size := by
      rw [hlt_args]; exact UInt64.lt_iff_toNat_lt.mp hlt
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp
      have := UInt64.lt_iff_toNat_lt.mp hlt
      have := an.toNat_lt
      omega
    have hjtop : ∀ j : Word, j < spTop m₀ → j < spTop m := fun j hj => by
      rw [htop, UInt64.lt_iff_toNat_lt, hadd]
      have := UInt64.lt_iff_toNat_lt.mp hj; omega
    have haoT : ao.toNat + an.toNat ≤ (spTop m₀).toNat := by omega
    have hnoT : (ao + an).toNat + an.toNat ≤ (spTop m₀).toNat := by
      have := har₀.bound
      rw [L.toNat_add_of_lt _ _ (by omega)]; omega
    have har : SpineR m ao an args := har₀.keepT _ hsz hb haoT hspn0
    have hno : SpineR m (ao + an) an nodes := hno₀.keepT _ hsz hb hnoT hspn0
    have hit : (i.toNat).toUInt64 = i := by simp
    have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
      have h := har.get i.toNat hlt'
      rwa [hit] at h
    have hvv : (spW m (ao + i)).toNat < 2 ^ 32 := by
      have h := har.lt i.toNat (by rw [← har.size]; exact hlt')
      rwa [hit] at h
    by_cases hlam : tagW v = 5
    · rw [ite_eq_left hlam]
      refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by decide) fun c1 => ?_)
      refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by decide) fun c2 => ?_)
      refine RefE.under (fun _ => rfl) (fun _ => rfl) fun hx =>
        RefE.onlySim hx (fun _ _ h => h) fun r₁ m₁ hcall => ?_
      cases k with
      | zero => rw [callW_zero] at hcall; cases hcall
      | succ k' =>
      have hvw : viewOK m v LAM := ⟨c1, UInt64.not_le.mp c2⟩
      obtain ⟨-, -, hbody1⟩ := view_lam m a hS.arena.base v hv hvw hlam
      have hvb := viewBind_lam m a hS.arena.base v hv hvw hlam
      have hii1 : i ≤ i + 1 := by
        rw [UInt64.le_iff_toNat_le, hi1]; omega
      have hi1an : i + 1 ≤ an := by
        rw [UInt64.le_iff_toNat_le, hi1]; have := UInt64.lt_iff_toNat_lt.mp hlt; omega
      have hbeta := betaPeel_refines' p hp hcc.instRange k' ⟨m, Locals.init []⟩ a dn vis fe MM eb _
        i ao an (i + 1) args hS hbody1 hii1 hi1an har (by rw [htop, hadd]; omega)
      obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW hbeta hcall
      rw [hi1] at hok hS' hres
      have hlamtag : ((decE v).tag == ETag.lam) = true := by
        rw [decE_tag_lam_beq v hv]; simp [hlam]
      have hrun : (whnfApp (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE v)
          (decE hd) va (same != 0) args nodes i.toNat).run a =
          .ok (AM.res (betaPeel (decE (tfld m LAM (tierW v) (idxW v) 1))
            i.toNat args (i.toNat + 1)) a,
            AM.st (betaPeel (decE (tfld m LAM (tierW v) (idxW v) 1))
            i.toNat args (i.toNat + 1)) a) := by
        rw [whnfApp]
        simp only [hlt', dite_true, hlamtag, ite_true, StateT.run_bind, L.Arena.viewBind_run, hvb,
          except_ok_bind]
        exact AM.run_of_ok _ _ hok
      simp only [Function.comp_apply, whnfAppE.k_beta_peel, whnfAppE.k_loop1, reduceCtorEq, ite_false,
        Sig.retVal, Sig.retOr]
      exact RefE.ret hrun ⟨⟨M', hS'.frame_stk (MemFrame.setCtl m₁ 136 _) (by simp) (by simp), hK',
        StackKept.restoreTop (fun j hj => by rw [hSt'.below j (hjtop j hj)]; exact hb j hj)
          (by rw [hSt'.top]; exact hle0) (hSt'.size.trans hsz) (hbk.trans hSt'.bstk)
          (hpg.trans hSt'.pool)⟩, hres, hrw⟩
    -- the next spine node, the push, then the ι step
    rw [ite_eq_right hlam]
    have hnodeget : nodes[i.toNat]! = decE (rdW (m.arr64 SPN) (ao + an + i)) := by
      have hi2 : i.toNat < nodes.size := by rw [hno.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have h := hno.get i.toNat hi2
      have hit2 : (ao + an) + (i.toNat).toUInt64 = ao + an + i := by rw [hit]
      rw [getElem!_pos nodes i.toNat hi2, h, hit2]; rfl
    have hnW : HW (rdW (m.arr64 SPN) (ao + an + i)) := by
      have h := hno.lt i.toNat (UInt64.lt_iff_toNat_lt.mp hlt)
      rwa [hit] at h
    have hnotlam : ((decE v).tag == ETag.lam) = false := by
      rw [decE_tag_lam_beq v hv]; simp [hlam]
    have hunf := whnfApp_nolam (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
      (decE v) (decE hd) va (same != 0) args nodes i.toNat hlt' hnotlam
    have hxi' : args[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := hxi
    rw [hnodeget, hxi'] at hunf
    dsimp only at hunf
    rw [hunf]
    have rest : ∀ ap m₁, apW p k m v same (rdW (m.arr64 SPN) (ao + i))
        (rdW (m.arr64 SPN) (ao + an + i)) = some (ap, m₁) →
        RefE (AppG p n) (whnfAppE.k_loop1 p (spTop m₀) (whnfAppE.j1 p k mode vis d v hd vo vn ao an
          i (spTop m₀) (rdW (m.arr64 SPN) (ao + i)) (rdW (m.arr64 SPN) (ao + an + i)) ap m₁))
          (do
            let ap ← internAppRebuilt (decE (rdW (m.arr64 SPN) (ao + an + i))) (same != 0) (decE v)
              (decE (rdW (m.arr64 SPN) (ao + i)))
            let step ← whnfAppIota (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
              (decE hd) (va.push (decE (rdW (m.arr64 SPN) (ao + i))))
              (va.push (decE (rdW (m.arr64 SPN) (ao + i)))).size
            appStepT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE hd) ap
              (va.push (decE (rdW (m.arr64 SPN) (ao + i))))
              (ap == decE (rdW (m.arr64 SPN) (ao + an + i))) args nodes i.toNat step) a
          (CorePost decStep dn m₀ vis fe MM eb ResW) := by
      intro ap m₁ hapE
      obtain ⟨a₁, hrunAp, hS₁, hSt₁, hapW⟩ := apW_ref p hp k m a dn vis fe MM eb hS v same
        (rdW (m.arr64 SPN) (ao + i)) (rdW (m.arr64 SPN) (ao + an + i)) hv hvv hnW ap m₁ hapE
      refine RefE.bind_right hrunAp ?_
      simp only [whnfAppE.j1]
      refine RefE.underIf (fun _ => rfl) (RefE.abort0 (by decide) fun hlen => ?_)
      -- the stack top is in bounds (it is `vo + vn ≠ 0`)
      have hc136 : (136 : Word).toNat < (m₁.arr64 CTL).size := by
        have ht1 : spTop m₁ = vo + vn := hSt₁.1.trans htop
        refine Classical.byContradiction fun hc => ?_
        have : spTop m₁ = 0 := by
          unfold spTop rdW
          rw [Array.getElem?_eq_none (by omega)]; rfl
        rw [this] at ht1
        have h0 : (vo + vn).toNat = 0 := by rw [← ht1]; rfl
        rw [hadd] at h0
        have := UInt64.lt_iff_toNat_lt.mp hlt
        omega
      have hbd : vo.toNat + vn.toNat < (m₁.arr64 SPN).size := by
        have h : ¬ UInt64.ofNat (m₁.arr64 SPN).size ≤ vo + vn := hlen
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by
          have := hSt₁.size; omega), hadd] at h
        omega
      have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hSt₁.size ▸ hspn
      have hva₁ : SpineR m₁ vo vn va :=
        hva.keep hSt₁.size hSt₁.below (by rw [htop, hadd]; exact Nat.le_refl _) hspn
      have hvo1 : vo + vn + 1 = vo + (vn + 1) := UInt64.add_assoc _ _ _
      have hfr := spnCtl_frame m₁ (vo + vn) (rdW (m.arr64 SPN) (ao + i)) (vo + (vn + 1))
      have hS₂ := hS₁.frame_stk hfr (by simp) (by simp)
      have hva₂ : SpineR ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
          (vo + (vn + 1))) vo (vn + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) :=
        (hva₁.push hspn₁ hbd _ hvv).setCtl 136 (vo + (vn + 1))
      have htop₂ : spTop ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
          (vo + (vn + 1))) = vo + (vn + 1) := by
        unfold spTop
        rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [L.Mem.size64_set64]; exact hc136⟩]
      have hvn1 : (vn + 1).toNat = vn.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have hadd2 : (vo + (vn + 1)).toNat = vo.toNat + vn.toNat + 1 := by
        rw [← UInt64.add_assoc, L.toNat_add_of_lt _ _ (by rw [hadd]; have : (1 : Word).toNat = 1 := rfl; omega),
          hadd]
        have : (1 : Word).toNat = 1 := rfl
        omega
      have htv₂ : (spTop m₀).toNat ≤ (vo + (vn + 1)).toNat := by rw [hadd2]; omega
      have hb₂ : ∀ j : Word, j < spTop m₀ →
          spW ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136 (vo + (vn + 1)))
            j = spW m₀ j := by
        intro j hj
        rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
          have := UInt64.lt_iff_toNat_lt.mp hj
          rw [← h, hadd] at this; omega), hSt₁.below j (hjtop j hj)]
        exact hb j hj
      have hsz₂ : (((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
          (vo + (vn + 1))).arr64 SPN).size = (m₀.arr64 SPN).size := by
        simp only [L.Mem.size64_set64]; exact hSt₁.size.trans hsz
      have hbk₂ := hbk.trans (hSt₁.bstk.trans (BKept.of_frame hfr (by decide) (by decide)))
      have hpg₂ := hpg.trans (hSt₁.pool.trans (PoolGrew.of_frame hfr (by decide) (by decide)))
      have hsame : ((if ap = rdW (m.arr64 SPN) (ao + an + i) then (1 : Word) else 0) != 0) =
          (decE ap == decE (rdW (m.arr64 SPN) (ao + an + i))) := by
        rw [← evalW_eq_ne ap _ hapW hnW]; simp [Cmp.evalW, Cmp.eval]
      generalize hm₂ : ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
        (vo + (vn + 1))) = m₂ at hS₂ hva₂ htop₂ hb₂ hsz₂ hbk₂ hpg₂
      cases k with
      | zero =>
        exact RefE.under (fun _ => rfl) (fun _ => by simp only [whnfAppE.k_whnf_app_iota.eq_1]) fun hx =>
          RefE.callE_zero hx
      | succ k' =>
      have hIo := appIota_ref p hp hcc k' (hk.mono (by omega)) F
        (by omega) (by omega) ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode d hd vo (vn + 1) _
        ⟨hS₂, hmode, hebm⟩ hhd hva₂ (by rw [htop₂, hadd2]; omega)
      refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩)
        (x := fun c => whnfAppE.k_loop1 p (spTop m₀) (whnfAppE.k_whnf_app_iota p (k' + 1) mode vis d v
          hd vo (vn + 1) (if ap = rdW (m.arr64 SPN) (ao + an + i) then 1 else 0) ao an i (spTop m₀)
          ap c)) (fun _ => by simp only [whnfAppE.k_whnf_app_iota.eq_1, whnfAppE.k_loop1])
        (RefE.coreSpec (whnfAppIotaE_spec p hp.appIota (k' + 1) ⟨m₂, Locals.init []⟩ mode vis d hd vo (vn + 1))
          hIo)
        (fun hG => RefE.coreSpecE (whnfAppIotaE_spec p hp.appIota (k' + 1) ⟨m₂, Locals.init []⟩ mode vis d hd
          vo (vn + 1)) hG.nv (hG.mono (by omega)) hIo) (fun rr m₃ _ hI => ?_)
      obtain ⟨-, ⟨M', hS₃, hK₃, hSt₃⟩, hresI, hrwI⟩ := hI
      have hva₃ : SpineR m₃ vo (vn + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) :=
        hva₂.keep hSt₃.size hSt₃.below (by rw [htop₂, hadd2]; omega) (hsz₂ ▸ hspn0)
      have htop₃ : spTop m₃ = vo + (vn + 1) := hSt₃.1.trans htop₂
      have hb₃ : ∀ j : Word, j < spTop m₀ → spW m₃ j = spW m₀ j := fun j hj => by
        rw [hSt₃.below j (by rw [htop₂, UInt64.lt_iff_toNat_lt, hadd2]
                             have := UInt64.lt_iff_toNat_lt.mp hj; omega)]
        exact hb₂ j hj
      have hsz₃ : (m₃.arr64 SPN).size = (m₀.arr64 SPN).size := hSt₃.size.trans hsz₂
      rw [whnfAppE.k_whnf_app_iota.eq_2]
      by_cases hz : rr.headD 0 ≠ 0
      · rw [ite_eq_left hz]
        have hopt : decOptR rr = some (decE (rr.tail.headD 0)) := decOpt_ne _ _ hz
        rw [hopt]
        simp only [appStepT]
        refine RefE.under (fun _ => rfl) (fun _ => rfl) fun hx =>
          RefE.onlySim hx (fun _ _ h => h) fun r' m₄ hcM => ?_
        have hx3 : SpineR m₃ ao an args := har₀.keepT _ hsz₃ hb₃ haoT hspn0
        obtain ⟨hok2, hD2, hres2, hfr2, hhw2⟩ := callW_mkAppNFrom p hp.spine (k' + 1)
          ⟨m₃, Locals.init []⟩ _ hS₃.arena (rr.tail.headD 0) ao an (i + 1) args hrwI.2 hx3
          (by rw [hi1]; have := UInt64.lt_iff_toNat_lt.mp hlt; omega) r' m₄ hcM
        have hcpl := Keeps.run (keeps_cpl_mkAppNFrom (decE (rr.tail.headD 0)) args
          (i + 1).toNat) (AM.run_of_ok _ _ hok2)
        have hS₄ := hS₃.of_app hD2 hcpl hfr2
        rw [hi1] at hok2 hres2 hS₄
        have hSt4 := StackKept.of_app_frame hfr2
        simp only [Function.comp_apply, whnfAppE.k_mk_app_n_from, whnfAppE.k_loop1, reduceCtorEq,
          ite_false, Sig.retVal, Sig.retOr]
        have hr2 := AM.run_of_ok _ _ hok2
        rw [hres2] at hr2
        refine RefE.ret (by simp only [StateT.run_bind, hr2, except_ok_bind]; rfl)
          ⟨⟨M', hS₄.frame_stk (MemFrame.setCtl m₄ 136 _) (by simp) (by simp), hK₃,
            StackKept.restoreTop (fun j hj => by
              rw [hSt4.below j (by
                rw [htop₃, UInt64.lt_iff_toNat_lt, hadd2]
                have := UInt64.lt_iff_toNat_lt.mp hj; omega)]
              exact hb₃ j hj) (by rw [hSt4.top, htop₃, UInt64.le_iff_toNat_le, hadd2]; omega)
              (hSt4.size.trans hsz₃) ((hbk₂.trans hSt₃.bstk).trans hSt4.bstk)
              ((hpg₂.trans hSt₃.pool).trans hSt4.pool)⟩, by simp [decStep],
            ⟨by simp [HW], hhw2⟩⟩
      rw [ite_eq_right hz]
      have hz' : rr.headD 0 = 0 := by simpa using hz
      have hopt : decOptR rr = none := by unfold decOptR decOpt; rw [ite_eq_left hz']
      rw [hopt]
      simp only [appStepT]
      have := ih (by omega) _ m₃ ap (vn + 1) (if ap = rdW (m.arr64 SPN) (ao + an + i) then 1 else 0)
        (i + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i))))
        M' hS₃ hapW hva₃ htop₃ (by rw [hadd2]; omega) hb₃ hsz₃ (hbk₂.trans hSt₃.bstk)
        (hpg₂.trans hSt₃.pool)
      rw [hi1, hsame] at this
      exact this.mono fun _ _ _ h => by
        obtain ⟨M'', h1, h2, h3⟩ := h.after
        exact ⟨⟨M'', h1, hK₃.trans h2, h3⟩, h.res, h.valid⟩
    by_cases hs : same ≠ 0
    · rw [ite_eq_left hs]; exact rest _ _ (apW_same hs)
    rw [ite_eq_right hs]
    refine RefE.under (fun _ => rfl) (fun _ => by simp only [whnfAppE.k_mk_app]) fun hx =>
      RefE.onlySim hx (fun _ _ h => h) fun r₁ m₁ hmk => ?_
    simp only [Function.comp_apply, whnfAppE.k_mk_app]
    exact rest _ _ (by simp [apW, hs, hmk])

include hp hcc in
/-- **`whnf_app` refines `whnfApp`, both outcomes**: `vargs` the slice `(vo, vn)` at the top of the
stack, the spine's arguments and nodes the slices `(ao, an)`, `(ao + an, an)` below it. -/
theorem app_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v hd vo vn same ao an i : Word)
    (vargs args nodes : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v)
    (hhd : HW hd) (hva : SpineR s₀.mem vo vn vargs) (htop : spTop s₀.mem = vo + vn)
    (har : SpineR s₀.mem ao an args) (hno : SpineR s₀.mem (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) :
    RefE (AppG p n) (whnfAppE p (n + 1) s₀.mem mode vis d v hd vo vn same ao an i)
      (whnfApp (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE v) (decE hd) vargs
        (same != 0) args nodes i.toNat) a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  have hS := hs.rel
  have hvn64 : vo.toNat + vn.toNat < 2 ^ 64 := by have := hva.bound; have := hS.spn; omega
  have hadd : (vo + vn).toNat = vo.toNat + vn.toNat := L.toNat_add_of_lt _ _ hvn64
  exact appLoop_ref p hp hcc n hk F hF hn mode vis d hd vo ao an (spTop s₀.mem) args nodes dn fe
    eb s₀.mem hs.mode4 hs.eb_mode hhd har hno hlo (by rw [htop, hadd]; omega) rfl hS.spn (n + 1)
    (Nat.le_refl _) a₀ s₀.mem v vn same i vargs MM hS hv hva htop (by rw [htop]; exact Nat.le_refl _)
    (fun _ _ => rfl) rfl (BKept.refl _) (PoolGrew.refl _)

include hp hcc in
/-- **`whnf_app` refines `whnfApp`** (`app_ref`'s ok half). -/
theorem whnfApp_refines' (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v hd vo vn same ao an i : Word)
    (vargs args nodes : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v)
    (hhd : HW hd) (hva : SpineR s₀.mem vo vn vargs) (htop : spTop s₀.mem = vo + vn)
    (har : SpineR s₀.mem ao an args) (hno : SpineR s₀.mem (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) :
    CoreSpec p (n + 1) "whnf_app" [mode, vis, d, v, hd, vo, vn, same, ao, an, i]
      (whnfApp (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE v) (decE hd) vargs
        (same != 0) args nodes i.toNat) decStep s₀ a₀ dn vis fe MM eb ResW :=
  RefE.coreSpec (whnfAppE_spec p hp.app (n + 1) s₀ mode vis d v hd vo vn same ao an i)
    (app_ref p hp hcc n hk F hF hn s₀ a₀ dn vis fe MM eb mode d v hd vo vn same ao an i vargs args
      nodes hs hv hhd hva htop har hno hlo)

end appRef

end L.Arena
