module

public import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.L.ModelGen
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfIotaRefine2
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 5 (`iota_certs_full_aux`, `iota_certs_full`)

Split from `WhnfIotaRefine4.lean` (size limit). The L function is split into small ones
(`iota_certs_full_forall`/`_flush`/`_check`/`_parts`, `spn_get`, `ctl_get`, `expr_view_ok`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `iota_certs_full_aux`, `iota_certs_full_forall`, `iota_certs_full` -/

/-- Model of `iota_certs_full_parts`. -/
def icfPartsW (m : Mem) (h : Word) : Option (List Word) :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m FORALL (tierW h) ≤ idxW h then none
  else some [tfld m FORALL (tierW h) (idxW h) 0,
    tfld m FORALL (tierW h) (idxW h) 1]

theorem icfParts_spec (p : Prog) (hp : p.lookup "iota_certs_full_parts" = some iotaCertsFullPartsL)
    (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_parts" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ icfPartsW s₀.mem h = some [r.headD 0, r.tail.headD 0];
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullPartsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] <;>
    finish [icfPartsW, tierW, idxW]

/-- Model of `spn_get`. -/
def spnGetW (m : Mem) (k : Word) : Option Word :=
  if k.toNat < (m.arr64 SPN).size then some (rdW (m.arr64 SPN) k) else none

theorem spnGet_spec (p : Prog) (hp : p.lookup "spn_get" = some spnGetL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "spn_get" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ spnGetW s₀.mem k = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, spnGetL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish [spnGetW, rdW]


/-- The count index of a tag's table (`CTL[c + tier]`), `none` past the last tag. -/
def evoCnt (g : Word) : Option TRec :=
  if g = 0 then some BVAR else if g = 1 then some FVAR else if g = 2 then some SORT
  else if g = 3 then some CONST else if g = 4 then some APP else if g = 5 then some LAM
  else if g = 6 then some FORALL else if g = 7 then some LET else if g = 8 then some LIT
  else if g = 9 then some PROJ else none

/-- The index `expr_view_ok` checks against the count: the wide index for an `app`, else narrow. -/
def evoIx (h : Word) : Word := if tagW h = 4 then idxA h else idxW h

/-- Model of `expr_view_ok`. -/
def evoW (m : Mem) (h : Word) : Option Word :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else match evoCnt (tagW h) with
    | none => none
    | some c => if tcnt m c (tierW h) ≤ evoIx h then none else some 0

theorem exprViewOk_spec (p : Prog) (hp : p.lookup "expr_view_ok" = some exprViewOkL) (n : Nat)
    (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "expr_view_ok" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ evoW s₀.mem h = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, exprViewOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] <;>
    finish [evoW, evoCnt, evoIx, tierW, idxW]


/-- Model of `ctl_get`. -/
def ctlGetW (m : Mem) (k : Word) : Option Word :=
  if k.toNat < (m.arr64 CTL).size then some (rdW (m.arr64 CTL) k) else none

theorem ctlGet_spec (p : Prog) (hp : p.lookup "ctl_get" = some ctlGetL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ctl_get" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ ctlGetW s₀.mem k = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ctlGetL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish [ctlGetW, rdW]


/-- Reading the stack: the entry at `ao + i` is `args[i]`'s handle word. -/
theorem spine_entry (m : Mem) (ao an i : Word) (args : Array EIdx) (hargs : SpineR m ao an args)
    (hi : i < an) :
    i.toNat < args.size ∧ HW (spW m (ao + i)) ∧ args[i.toNat]'(by rw [hargs.size]; exact hi) =
      decE (spW m (ao + i)) := by
  have hi' : i.toNat < an.toNat := hi
  have hsz : i.toNat < args.size := by rw [hargs.size]; exact hi'
  have e : ao + i.toNat.toUInt64 = ao + i := by rw [toUInt64_toNat_self]
  refine ⟨hsz, ?_, ?_⟩
  · have := hargs.lt i.toNat hi'
    rw [e] at this
    exact this
  · have := hargs.get i.toNat hsz
    rw [e] at this
    exact this

/-- **A handle that passes `expr_view_ok` views.** -/
theorem evo_view (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : HW h) (w : Word)
    (hev : evoW m h = some w) :
    (∃ v, a.store.view (decE h) = some v) ∧
    (tagW h = 0 → ∃ x, a.store.view (decE h) = some (.bvar x)) ∧
    (tagW h = 6 → ∃ ty body, a.store.view (decE h) = some (.forallE ty body)) ∧
    (tagW h ≠ 0 → tagW h ≠ 6 → ∀ v, a.store.view (decE h) = some v →
      (∀ ty body, v ≠ .forallE ty body) ∧ (∀ x, v ≠ .bvar x)) := by
  simp only [evoW] at hev
  obtain ⟨g1, hev⟩ := of_ite_none hev
  cases hc : evoCnt (tagW h) with
  | none => rw [hc] at hev; cases hev
  | some c =>
  rw [hc] at hev
  simp only at hev
  by_cases g2 : tcnt m c (tierW h) ≤ evoIx h
  · rw [ite_eq_left g2] at hev; cases hev
  have hvn : tagW h ≠ 4 → viewOK m h c := fun t => ⟨g1, UInt64.not_le.mp (by simpa [evoIx, t] using g2)⟩
  have hva : tagW h = 4 → ¬ tcnt m c (tierW h) ≤ idxA h := fun t => by simpa [evoIx, t] using g2
  simp only [evoCnt] at hc
  by_cases t0 : tagW h = 0
  · simp [t0] at hc
    subst hc
    have hv := hvn (by rw [t0]; decide)
    have := view_bvar m a hR h hh hv t0
    refine ⟨⟨_, this⟩, fun _ => ⟨_, this⟩, fun h6 => by rw [t0] at h6; exact absurd h6 (by decide),
      fun h0 => absurd t0 h0⟩
  by_cases t1 : tagW h = 1
  · simp [t1] at hc
    subst hc
    have hv := hvn (by rw [t1]; decide)
    obtain ⟨i, ty, hvw⟩ := view_fvar m a hR h hh hv t1
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t1] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t2 : tagW h = 2
  · simp [t2] at hc
    subst hc
    have hv := hvn (by rw [t2]; decide)
    obtain ⟨u, hvw⟩ := view_sort m a hR h hh hv t2
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t2] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t3 : tagW h = 3
  · simp [t3] at hc
    subst hc
    have hv := hvn (by rw [t3]; decide)
    obtain ⟨n, us, hvw⟩ := view_const m a hR h hh hv t3
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t3] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t4 : tagW h = 4
  · simp [t4] at hc
    subst hc
    have hv : viewOKA m h := ⟨g1, UInt64.not_le.mp (hva t4)⟩
    obtain ⟨hvw, -⟩ := view_app m a hR h hh hv t4
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t4] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t5 : tagW h = 5
  · simp [t5] at hc
    subst hc
    have hv := hvn (by rw [t5]; decide)
    obtain ⟨hvw, -⟩ := view_lam m a hR h hh hv t5
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t5] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t6 : tagW h = 6
  · simp [t6] at hc
    subst hc
    have hv := hvn (by rw [t6]; decide)
    obtain ⟨hvw, -⟩ := view_forall m a hR h hh hv t6
    exact ⟨⟨_, hvw⟩, fun h0 => absurd t6 (by rw [h0]; decide), fun _ => ⟨_, _, hvw⟩,
      fun _ h6 => absurd t6 h6⟩
  by_cases t7 : tagW h = 7
  · simp [t7] at hc
    subst hc
    have hv := hvn (by rw [t7]; decide)
    obtain ⟨hvw, -⟩ := view_let m a hR h hh hv t7
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => absurd h6 t6, fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t8 : tagW h = 8
  · simp [t8] at hc
    subst hc
    have hv := hvn (by rw [t8]; decide)
    obtain ⟨l, hvw⟩ := view_lit m a hR h hh hv t8
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => absurd h6 t6, fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t9 : tagW h = 9
  · simp [t9] at hc
    subst hc
    have hv := hvn (by rw [t9]; decide)
    obtain ⟨hvw, -⟩ := view_proj m a hR h hh hv t9
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => absurd h6 t6, fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  simp [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] at hc


/-! ### The models, both outcomes -/

/-- **The family's models, both outcomes** (generated; `infer`, `defeq` through their runs, the
readers and `inst_list` lifted). -/
l_model icfE_spec (p : Prog) (hp : IotaProg4 p)
  fns [hp.iotaCertsFullCheck ↦ icfCheckE list, hp.iotaCertsFullAux ↦ icfAuxE list,
    hp.iotaCertsFullForall ↦ icfForallE list, hp.iotaCertsFullFlush ↦ icfFlushE list,
    hp.iotaCertsFull ↦ icfTopE list]
  specs [callW_spec p n "inst_list", callW_spec p n "iota_certs_full_parts", callW_spec p n "spn_get",
    callW_spec p n "expr_view_ok", callW_spec p n "ctl_get"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ### The twin, by arms -/

/-- The domain check of the `forallE` arm (the twin's three steps, `iota_certs_full_check`). -/
def icfChkT (r : CoreFnsA) (d : Nat) (ty : EIdx) (acc : Array EIdx) (arg : EIdx) : AM Bool := do
  let ty2 ← instantiateListFast coreWalkFuel ty acc 0
  let ta ← r.infer d arg
  r.defeq d ta ty2

section icfRun
variable (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (acc args : Array EIdx) (i : Nat)

theorem icf_run_done (hi : ¬ i < args.size) (a : AState) :
    (iotaCertsFullAux r fe d h acc args i).run a = .ok (true, a) := by
  rw [iotaCertsFullAux]; simp [hi]; rfl

/-- The `forallE` arm: the check, then the body on the pushed accumulator. -/
theorem icf_eq_forall (hi : i < args.size) (a : AState) (ty body : EIdx)
    (hv : a.store.view h = some (.forallE ty body)) :
    (iotaCertsFullAux r fe d h acc args i).run a =
      (icfChkT r d ty acc args[i] >>= fun b =>
        if b then iotaCertsFullAux r fe d body (acc.push args[i]) args (i + 1) else pure false).run a := by
  have hv' : (view h).run a = .ok (.forallE ty body, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, icfChkT, bind_assoc]

/-- The `bvar` arm with a pending accumulator: flush it, then look again. -/
theorem icf_eq_flush (hi : i < args.size) (a : AState) (x : Nat)
    (hv : a.store.view h = some (.bvar x)) (h0 : acc.size ≠ 0) :
    (iotaCertsFullAux r fe d h acc args i).run a =
      (instantiateListFast coreWalkFuel h acc 0 >>= fun ty2 =>
        iotaCertsFullAux r fe d ty2 #[] args i).run a := by
  have hv' : (view h).run a = .ok (.bvar x, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h0, ↓reduceIte]

theorem icf_run_other (hi : i < args.size) (a : AState)
    (hn1 : ∀ ty body, a.store.view h ≠ some (.forallE ty body))
    (hn2 : ∀ x, a.store.view h ≠ some (.bvar x)) (v : ENodeView) (hv : a.store.view h = some v) :
    (iotaCertsFullAux r fe d h acc args i).run a = .ok (false, a) := by
  have hv' : (view h).run a = .ok (v, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind]
  cases v with
  | forallE ty body => exact absurd hv (hn1 _ _)
  | bvar x => exact absurd hv (hn2 _)
  | _ => simp; rfl

theorem icf_run_nil (hi : i < args.size) (a : AState) (x : Nat) (hv : a.store.view h = some (.bvar x))
    (h0 : acc.size = 0) :
    (iotaCertsFullAux r fe d h acc args i).run a = .ok (false, a) := by
  have hv' : (view h).run a = .ok (.bvar x, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h0, ↓reduceIte]
  rfl

end icfRun

/-! ### The refinements -/

/-- **The domain check refines its three twin steps, both outcomes**: the errors are the `infer`
and `defeq` slots'. -/
theorem icfCheck_ref (p : Prog) (hil : InstListOK p) (K F : Nat) (hk : KnotUpTo p K) (hnF : K ≤ F)
    (hn62 : K ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ty aco acn arg : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hty : HW ty) (harg : HW arg) (acc : Array EIdx) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hacc : SpineR m aco acn acc)
    (htop : aco.toNat + acn.toNat ≤ (spTop m).toNat) :
    RefE (KnotUpToE p K) (icfCheckE p (K + 1) m mode vis d ty aco acn arg)
      (icfChkT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE ty) acc (decE arg)) a
      (CorePost decBool dn m vis fe M eb ResH) := by
  rw [icfCheckE.eq_2]
  refine RefE.bind_callW (fun _ => icfCheckE.k_inst_list.eq_1 ..)
    (hil K ⟨m, Locals.init []⟩ a dn vis fe M eb ty aco acn 0 acc hS hty hacc htop)
    fun r1 m1 _ h1 => RefE.after_core (w := id) h1 fun M1 hS1 _ => ?_
  rw [icfCheckE.k_inst_list.eq_2]
  refine RefE.bind_callE (x := icfCheckE.k_infer p K mode vis d (r1.headD 0)) (fun _ => rfl)
    ((hk K (Nat.le_refl _)).infer F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d arg hnF hn62
      ⟨hS1, hm4, hebm⟩ harg)
    (fun hG => (hG K (Nat.le_refl _)).infer F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d arg hnF hn62
      ⟨hS1, hm4, hebm⟩ harg) fun r2 m2 _ h2 => RefE.after_core (w := id) h2 fun M2 hS2 _ => ?_
  rw [icfCheckE.k_infer.eq_2, ← bind_pure ((coreKnot (decMode mode) (decEager mode) fe id F).defeq _ _ _)]
  refine RefE.bind_callE (x := icfCheckE.k_defeq p) (fun _ => icfCheckE.k_defeq.eq_1 ..)
    ((hk K (Nat.le_refl _)).defeq F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d _ _ hnF hn62
      ⟨hS2, hm4, hebm⟩ h2.resOk h1.resOk)
    (fun hG => (hG K (Nat.le_refl _)).defeq F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d _ _ hnF hn62
      ⟨hS2, hm4, hebm⟩ h2.resOk h1.resOk) fun r3 m3 _ h3 => ?_
  rw [icfCheckE.k_defeq.eq_2]
  exact RefE.ret rfl ⟨h3.after, rfl, h3.resOk⟩

/-- **The three functions' refinement, both outcomes** (`cond` is the case the helper handles; the
model `fE` at fuel `N + 1`). The errors are the slots'. -/
def ICFRef (p : Prog) (fE : Prog → Nat → Mem → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Except Err (List Word × Mem)) (cond : Word → Word → Word → Prop) (N F : Nat) : Prop :=
  KnotUpTo p N → N ≤ F → N ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h aco acn ao an i : Word) (acc args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW h → cond h an i →
    SpineR s₀.mem aco acn acc → SpineR s₀.mem ao an args → aco + acn = spTop s₀.mem →
    ao.toNat + an.toNat ≤ aco.toNat →
    RefE (KnotUpToE p N) (fE p (N + 1) s₀.mem mode vis d h aco acn ao an i)
      (iotaCertsFullAux (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) acc args i.toNat) a₀
      (GrowPost decBool dn s₀.mem vis fe MM eb ResH)

theorem icfForall_ref (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (N F : Nat)
    (hA : ∀ N', N = N' + 1 → ICFRef p icfAuxE (fun _ _ _ => True) N' F) :
    ICFRef p icfForallE (fun h an i => tagW h = 6 ∧ i < an) N F := by
  intro hk hnF hn62 s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS hm4 hebm hh
    ⟨h6, hi⟩ hacc hargs htop hao
  rw [icfForallE.eq_2]
  cases N with
  | zero =>
    rw [callW_zero, liftE_none, icfForallE.k_iota_certs_full_parts.eq_1]; exact RefE.of_cls0 rfl
  | succ N' =>
  have hk' : KnotUpTo p N' := hk.mono (by omega)
  rcases c1 : callW p (N' + 1) "iota_certs_full_parts" [h] s₀.mem with _ | ⟨pr, m0⟩
  · rw [liftE_none, icfForallE.k_iota_certs_full_parts.eq_1]; exact RefE.of_cls0 rfl
  rw [liftE_some, icfForallE.k_iota_certs_full_parts.eq_2]
  obtain ⟨t1, ht1, -, hmem1, hparts⟩ := triple_of_callW
    (icfParts_spec p hp.iotaCertsFullParts N' ⟨s₀.mem, Locals.init []⟩ h) c1
  obtain rfl : m0 = s₀.mem := by rw [← ht1]; exact hmem1
  -- the stored node
  simp only [icfPartsW] at hparts
  obtain ⟨g1, hparts⟩ := of_ite_none hparts
  obtain ⟨g2, hparts⟩ := of_ite_none hparts
  simp only [Option.some.injEq] at hparts
  obtain ⟨hvw, hn1, hn2⟩ := view_forall s₀.mem a₀ hS.arena.base h hh ⟨g1, UInt64.not_le.mp g2⟩ h6
  simp only [List.cons.injEq, and_true] at hparts
  obtain ⟨hp0, hp1⟩ := hparts
  rw [hp0] at hvw hn1
  rw [hp1] at hvw hn2
  -- the argument
  rcases c2 : callW p (N' + 1) "spn_get" [ao + i] s₀.mem with _ | ⟨ra, m00⟩
  · rw [liftE_none, icfForallE.k_spn_get.eq_1]; exact RefE.of_cls0 rfl
  rw [liftE_some, icfForallE.k_spn_get.eq_2]
  obtain ⟨t2, ht2, -, hmem2, hget⟩ := triple_of_callW
    (spnGet_spec p hp.spnGet N' ⟨s₀.mem, Locals.init []⟩ (ao + i)) c2
  obtain rfl : m00 = s₀.mem := by rw [← ht2]; exact hmem2
  obtain ⟨hisz, hargw, hargget⟩ := spine_entry s₀.mem ao an i args hargs hi
  have hra : ra.headD 0 = spW s₀.mem (ao + i) := by
    simp only [spnGetW] at hget
    split at hget
    · simp only [Option.some.injEq] at hget; rw [← hget]; rfl
    · cases hget
  rw [← hra] at hargw hargget
  -- the check
  have hbd := hacc.bound
  have hspn := hS.spn
  have h263 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
  have hsum : (aco + acn).toNat = aco.toNat + acn.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have htopc : aco.toNat + acn.toNat ≤ (spTop s₀.mem).toNat := by
    rw [← htop, hsum]; exact Nat.le_refl _
  have hchk := icfCheck_ref p hil N' F hk' (by omega) (by omega) dn vis fe eb mode d (pr.headD 0) aco acn
    (ra.headD 0) hm4 hebm hn1 hargw acc s₀.mem a₀ MM hS hacc htopc
  rw [← hargget] at hchk
  refine RefE.of_run_eq (icf_eq_forall _ fe d.toNat (decE h) acc args i.toNat hisz a₀ _ _ hvw) ?_
  rcases hcv : icfCheckE p (N' + 1) s₀.mem mode vis d (pr.headD 0) aco acn (ra.headD 0) with e3 | ⟨rr, m3⟩
  · rw [icfForallE.k_iota_certs_full_check.eq_1]
    rw [hcv] at hchk
    exact RefE.bind_left fun hG => hchk (hG.mono (Nat.le_succ N'))
  rw [hcv] at hchk
  obtain ⟨b, a3, hrun3, hP3⟩ := hchk
  rw [icfForallE.k_iota_certs_full_check.eq_2]
  refine RefE.bind_right hrun3 ?_
  obtain ⟨⟨M3, hS3, hK3, hSt3⟩, hb, hwok⟩ := hP3
  by_cases hok0 : rr.headD 0 = 0
  · rw [ite_eq_left hok0]
    have hb' : b = false := by rw [hb]; simp only [decBool, hok0]; rfl
    subst hb'
    exact RefE.ret rfl ⟨⟨M3, hS3, hK3, hSt3.toGrew⟩, rfl, by show HW (0 : Word); unfold HW; decide⟩
  rw [ite_eq_right hok0]
  have hb' : b = true := by rw [hb]; simpa [decBool] using hok0
  subst hb'
  refine RefE.ite_pos rfl ?_
  refine RefE.abort0 (by rfl) fun hlen => ?_
  have hsz3 : (m3.arr64 SPN).size = (s₀.mem.arr64 SPN).size := hSt3.size
  have hg1 : (aco + acn).toNat < (m3.arr64 SPN).size := by
    have h' := UInt64.not_le.mp hlen
    rw [UInt64.lt_iff_toNat_lt, Mem.len64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h'
    exact h'
  have hg2 : (136 : Word).toNat < (m3.arr64 CTL).size := hS3.ctl136
  have htop3 : spTop m3 = aco + acn := by rw [hSt3.1, ← htop]
  have hq1 : (aco + acn).toNat + 1 < 2 ^ 64 := by omega
  obtain ⟨hfr, hsp', hgrew, hslot, hsz⟩ := push_step m3 (aco + acn) (ra.headD 0) hg1 hg2 htop3 hq1
  have hS3p := hS3.frame_stk hfr (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have hacc3 : SpineR m3 aco acn acc := hacc.keep hSt3.size hSt3.below htopc hS.spn
  have hpush := (SpineR.push hacc3 hS3.spn (by rw [← hsum]; exact hg1) (ra.headD 0) hargw).setCtl 136
    (aco + acn + 1)
  have hargs3 : SpineR m3 ao an args := hargs.keep hSt3.size hSt3.below (by omega) hS.spn
  have htop3' : aco.toNat + acn.toNat ≤ (spTop m3).toNat := by rw [htop3, hsum]; exact Nat.le_refl _
  have hargs3p : SpineR _ ao an args := hargs3.keep hgrew.size hgrew.below (by omega) hS3.spn
  have htopp : aco + (acn + 1) =
      spTop ((m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1)) := by
    rw [hsp', UInt64.add_assoc]
  have hgr := hSt3.toGrew.trans hgrew
  generalize (m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1) = m3p at *
  have hi1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hi
  have hE4 := hA N' rfl hk' (by omega) (by omega) ⟨m3p, Locals.init []⟩ a3 dn vis fe M3 eb mode d
    (pr.tail.headD 0) aco (acn + 1) ao an (i + 1) (acc.push (decE (ra.headD 0))) args hS3p hm4 hebm hn2
    trivial hpush hargs3p htopp hao
  rw [hi1] at hE4
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N'))
    (by rw [hargget]) (fun _ _ _ h => ⟨CoreAfterG.compK hK3 hgr h.after, h.res, h.valid⟩) hE4

theorem icfFlush_ref (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (N F : Nat)
    (hA : ∀ N', N = N' + 1 → ICFRef p icfAuxE (fun _ _ _ => True) N' F) :
    ICFRef p icfFlushE (fun h an i => tagW h = 0 ∧ i < an) N F := by
  intro hk hnF hn62 s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS hm4 hebm hh
    ⟨h0, hi⟩ hacc hargs htop hao
  rw [icfFlushE.eq_2]
  cases N with
  | zero => rw [callW_zero, liftE_none, icfFlushE.k_expr_view_ok.eq_1]; exact RefE.of_cls0 rfl
  | succ N' =>
  have hk' : KnotUpTo p N' := hk.mono (by omega)
  rcases c0 : callW p (N' + 1) "expr_view_ok" [h] s₀.mem with _ | ⟨rv, m0⟩
  · rw [liftE_none, icfFlushE.k_expr_view_ok.eq_1]; exact RefE.of_cls0 rfl
  rw [liftE_some, icfFlushE.k_expr_view_ok.eq_2]
  obtain ⟨t0, ht0, -, hmem0, hev⟩ := triple_of_callW
    (exprViewOk_spec p hp.exprViewOk N' ⟨s₀.mem, Locals.init []⟩ h) c0
  obtain rfl : m0 = s₀.mem := by rw [← ht0]; exact hmem0
  obtain ⟨-, hB, -, -⟩ := evo_view s₀.mem a₀ hS.arena.base h hh _ hev
  obtain ⟨x, hvx⟩ := hB h0
  have hisz : i.toNat < args.size := by rw [hargs.size]; exact hi
  by_cases hacn : acn = 0
  · rw [ite_eq_left hacn]
    have hsz : acc.size = 0 := by rw [hacc.size, hacn]; rfl
    exact RefE.ret (icf_run_nil _ fe d.toNat (decE h) acc args i.toNat hisz a₀ x hvx hsz)
      (GrowPost.of_core (CorePost.ret hS rfl (by unfold ResH HW; decide)))
  rw [ite_eq_right hacn]
  have hbd := hacc.bound
  have hspn := hS.spn
  have h263 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
  have hsum : (aco + acn).toNat = aco.toNat + acn.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have htopc : aco.toNat + acn.toNat ≤ (spTop s₀.mem).toNat := by
    rw [← htop, hsum]; exact Nat.le_refl _
  rcases c1 : callW p (N' + 1) "inst_list" [h, aco, acn, 0] s₀.mem with _ | ⟨r1, m1⟩
  · rw [liftE_none, icfFlushE.k_inst_list.eq_1]; exact RefE.of_cls0 rfl
  rw [liftE_some, icfFlushE.k_inst_list.eq_2]
  have h1 := CoreSpec.of_callW
    (hil (N' + 1) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb h aco acn 0 acc hS hh hacc htopc) c1
  refine RefE.of_run_eq (icf_eq_flush _ fe d.toNat (decE h) acc args i.toNat hisz a₀ x hvx
    (by rw [hacc.size]; intro h0; exact hacn (UInt64.toNat_inj.mp (by simpa using h0)))) ?_
  refine RefE.bind_growK (w := id) h1 fun M1 hS1 hSt1 => ?_
  have hr1 : HW (r1.headD 0) := h1.resOk
  have hsp1 : spTop m1 = aco + acn := by rw [hSt1.1, ← htop]
  have hnil : SpineR m1 (aco + acn) 0 #[] := SpineR.nil_at m1 _ (by rw [hsum, hSt1.size]; omega)
  have hargs1 : SpineR m1 ao an args := hargs.keep hSt1.size hSt1.below
    (by show ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat; omega) hS.spn
  have hE := hA N' rfl hk' (by omega) (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d
    (r1.headD 0) (aco + acn) 0 ao an i #[] args hS1 hm4 hebm hr1 trivial hnil hargs1
    (by rw [UInt64.add_zero]; exact hsp1.symm) (by omega)
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N')) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩) hE

theorem icfAux_ref (p : Prog) (hp : IotaProg4 p) (N F : Nat)
    (hFo : ∀ N', N = N' + 1 → ICFRef p icfForallE (fun h an i => tagW h = 6 ∧ i < an) N' F)
    (hFl : ∀ N', N = N' + 1 → ICFRef p icfFlushE (fun h an i => tagW h = 0 ∧ i < an) N' F) :
    ICFRef p icfAuxE (fun _ _ _ => True) N F := by
  intro hk hnF hn62 s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS hm4 hebm hh
    _ hacc hargs htop hao
  rw [icfAuxE.eq_2]
  by_cases hi : ¬ i < an
  · rw [ite_eq_right hi]
    have hi' : ¬ i.toNat < args.size := by rw [hargs.size]; exact hi
    exact RefE.ret (icf_run_done _ fe d.toNat (decE h) acc args i.toNat hi' a₀)
      (GrowPost.of_core (CorePost.ret hS rfl (by unfold ResH HW; decide)))
  have hi := Classical.not_not.mp hi
  rw [ite_eq_left hi]
  by_cases h6 : tagW h = 6
  · rw [ite_eq_left h6]
    cases N with
    | zero => rw [icfForallE.eq_1, icfCheckE.k_defeq.eq_1]; exact RefE.of_cls0 rfl
    | succ N' =>
    exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N')) rfl
      (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
      (hFo N' rfl (hk.mono (by omega)) (by omega) (by omega) s₀ a₀ dn vis fe MM eb mode d h aco acn ao
        an i acc args hS hm4 hebm hh ⟨h6, hi⟩ hacc hargs htop hao)
  rw [ite_eq_right h6]
  by_cases h0 : tagW h = 0
  · rw [ite_eq_left h0]
    cases N with
    | zero => rw [icfFlushE.eq_1, icfCheckE.k_defeq.eq_1]; exact RefE.of_cls0 rfl
    | succ N' =>
    exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N')) rfl
      (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
      (hFl N' rfl (hk.mono (by omega)) (by omega) (by omega) s₀ a₀ dn vis fe MM eb mode d h aco acn ao
        an i acc args hS hm4 hebm hh ⟨h0, hi⟩ hacc hargs htop hao)
  rw [ite_eq_right h0]
  cases N with
  | zero => rw [callW_zero, liftE_none, icfAuxE.k_expr_view_ok.eq_1]; exact RefE.of_cls0 rfl
  | succ N' =>
  rcases c1 : callW p (N' + 1) "expr_view_ok" [h] s₀.mem with _ | ⟨rv, m1⟩
  · rw [liftE_none, icfAuxE.k_expr_view_ok.eq_1]; exact RefE.of_cls0 rfl
  rw [liftE_some, icfAuxE.k_expr_view_ok.eq_2]
  obtain ⟨t1, ht1, -, hmem1, hev⟩ := triple_of_callW
    (exprViewOk_spec p hp.exprViewOk N' ⟨s₀.mem, Locals.init []⟩ h) c1
  obtain rfl : m1 = s₀.mem := by rw [← ht1]; exact hmem1
  obtain ⟨⟨v, hv⟩, -, -, hD⟩ := evo_view s₀.mem a₀ hS.arena.base h hh _ hev
  obtain ⟨hn1, hn2⟩ := hD h0 h6 v hv
  exact RefE.ret (icf_run_other _ fe d.toNat (decE h) acc args i.toNat
    (by rw [hargs.size]; exact hi) a₀ (fun ty body hc => by rw [hv] at hc; exact hn1 ty body (Option.some.inj hc))
    (fun x hc => by rw [hv] at hc; exact hn2 x (Option.some.inj hc)) v hv)
    (GrowPost.of_core (CorePost.ret hS rfl (by unfold ResH HW; decide)))

theorem icf_all (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (F N : Nat) :
    ICFRef p icfAuxE (fun _ _ _ => True) N F ∧
    ICFRef p icfForallE (fun h an i => tagW h = 6 ∧ i < an) N F ∧
    ICFRef p icfFlushE (fun h an i => tagW h = 0 ∧ i < an) N F := by
  induction N with
  | zero =>
    exact ⟨icfAux_ref p hp 0 F (fun _ h => absurd h (by simp)) (fun _ h => absurd h (by simp)),
      icfForall_ref p hp hil 0 F (fun _ h => absurd h (by simp)),
      icfFlush_ref p hp hil 0 F (fun _ h => absurd h (by simp))⟩
  | succ N ih =>
    exact ⟨icfAux_ref p hp (N + 1) F (fun N' h => by cases Nat.succ.inj h; exact ih.2.1)
        (fun N' h => by cases Nat.succ.inj h; exact ih.2.2),
      icfForall_ref p hp hil (N + 1) F (fun N' h => by cases Nat.succ.inj h; exact ih.1),
      icfFlush_ref p hp hil (N + 1) F (fun N' h => by cases Nat.succ.inj h; exact ih.1)⟩

/-- **`iota_certs_full` refines `iotaCertsFull`, both outcomes**: the errors are the slots'. -/
theorem icfTop_ref (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d h ao an : Word) (args : Array EIdx) (hS : CoreS dn s₀.mem a₀ vis fe MM eb)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hh : HW h) (hargs : SpineR s₀.mem ao an args)
    (htop : ao + an = spTop s₀.mem) :
    RefE (KnotUpToE p n) (icfTopE p (n + 1) s₀.mem mode vis d h ao an)
      (iotaCertsFull (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) args.toList) a₀
      (CorePost decBool dn s₀.mem vis fe MM eb ResH) := by
  rw [icfTopE.eq_2]
  cases n with
  | zero => rw [callW_zero, liftE_none, icfTopE.k_ctl_get]; exact RefE.of_cls0 rfl
  | succ n' =>
  refine RefE.onlySim (fun _ => by rw [icfTopE.k_ctl_get])
    (fun _ _ c0 => triple_of_callW (ctlGet_spec p hp.ctlGet n' ⟨s₀.mem, Locals.init []⟩ 136) c0)
    fun t m0 ⟨t0, ht0, _, hmem0, hget⟩ => ?_
  obtain rfl : m0 = s₀.mem := by rw [← ht0]; exact hmem0
  rw [icfTopE.k_ctl_get]
  have ht : t.headD 0 = rdW (s₀.mem.arr64 CTL) 136 := by
    simp only [ctlGetW] at hget
    split at hget
    · simp only [Option.some.injEq] at hget; rw [← hget]
    · cases hget
  have htop' : t.headD 0 = ao + an := by rw [ht]; exact htop.symm
  have hbd := hargs.bound
  have hspn := hS.spn
  have h263 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
  have hsum : (ao + an).toNat = ao.toNat + an.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hnil : SpineR s₀.mem (t.headD 0) 0 #[] :=
    SpineR.nil_at s₀.mem _ (by rw [htop', hsum]; omega)
  have hE := (icf_all p hp hil F n').1 (hk.mono (by omega)) (by omega) (by omega) ⟨s₀.mem, Locals.init []⟩
    a₀ dn vis fe MM eb mode d h (t.headD 0) 0 ao an 0 #[] args hS hm4 hebm hh trivial
    hnil hargs (by rw [UInt64.add_zero, htop']; exact htop) (by rw [htop', hsum]; omega)
  have hT : iotaCertsFull (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) args.toList =
      iotaCertsFullAux (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) #[] args
        (0 : Word).toNat := by
    simp only [iotaCertsFull, Array.toArray_toList]; rfl
  rw [hT]
  refine RefE.tailMap_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ n')) rfl
    (fun v y a' hv => ?_) hE
  rw [ht]
  exact GrowPost.restore hv [v.1.headD 0] rfl hv.valid

/-! ### The ok halves (`@[refines]` shapes) -/

/-- The three functions' common statement (`cond` is the case the helper handles). -/
def ICFSpec (p : Prog) (f : FnName) (cond : Word → Word → Word → Prop) (N : Nat) : Prop :=
  ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 → KnotUpTo p N →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h aco acn ao an i : Word) (acc args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW h → cond h an i →
    SpineR s₀.mem aco acn acc → SpineR s₀.mem ao an args → aco + acn = spTop s₀.mem →
    ao.toNat + an.toNat ≤ aco.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p (N + 1)) f [mode, vis, d, h, aco, acn, ao, an, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (iotaCertsFullAux (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) acc args
        i.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (iotaCertsFullAux (coreKnot (decMode mode) (decEager mode) fe id F) fe
        d.toNat (decE h) acc args i.toNat) a₀) vis fe MM eb ∧
      AM.res (iotaCertsFullAux (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) acc args
        i.toNat) a₀ = decBool r ∧ ResH r; ⊤⦄

/-- **`iota_certs_full_aux` refines `iotaCertsFullAux`** (`icf_all`'s ok half). Statement changes:
the shape of `rec_fire_args`' (a triple with `CoreAfterG`: the accumulator pushes leave the stack
top raised, `CoreSpec` requires it kept); `n ≤ 2 ^ 62`, the eager bit, `ao + an ≤ aco`. The L
function is split (`iota_certs_full_forall`/`_flush`/`_check`/`_parts`, `spn_get`, `expr_view_ok`:
`vcgen` fuel, and the twin's `view` of a handle needs the L side to check it). -/
theorem iotaCertsFullAux_refines' (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (n : Nat) :
    ICFSpec p "iota_certs_full_aux" (fun _ _ _ => True) n :=
  fun F hnF hn62 hk s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS hm4 hebm hh hc hacc
      hargs htop hao =>
    triple_post (RefE.triple ((icfE_spec p hp (n + 1)).2.1 s₀ mode vis d h aco acn ao an i)
      ((icf_all p hp hil F n).1 hk hnF hn62 s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS
        hm4 hebm hh hc hacc hargs htop hao))
      fun _ _ ⟨hl, _, _, hT, hR⟩ => ⟨hl, hR.growRef hT⟩

/-- **`iota_certs_full` refines `iotaCertsFull`** (`icfTop_ref`'s ok half). Statement changes:
`n ≤ 2 ^ 62`, the eager bit. -/
theorem iotaCertsFull_refines' (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h ao an : Word) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW h →
    SpineR s₀.mem ao an args → ao + an = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_certs_full" [mode, vis, d, h, ao, an]
      (iotaCertsFull (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) args.toList) decBool s₀
      a₀ dn vis fe MM eb :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d h ao an args hS hm4 hebm hh hargs htop =>
    RefE.coreSpec ((icfE_spec p hp (n + 1)).2.2.2.2 s₀ mode vis d h ao an)
      (icfTop_ref p hp hil n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d h ao an args hS hm4 hebm hh
        hargs htop)

end L.Arena
