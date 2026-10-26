import ConAgua.Arena.WhnfIotaRefine4

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

/-- Model of `iota_certs_full_check` (callees at fuel `n`). -/
def icfCheckW (p : Prog) (n : Nat) (m : Mem) (mode vis d ty aco acn arg : Word) :
    Option (List Word × Mem) :=
  match callW p n "inst_list" [ty, aco, acn, 0] m with
  | none => none
  | some (ty2, m1) =>
  match callW p n "infer" [mode, vis, d, arg] m1 with
  | none => none
  | some (ta, m2) =>
  match callW p n "defeq" [mode, vis, d, ta.headD 0, ty2.headD 0] m2 with
  | none => none
  | some (ok, m3) => some ([ok.headD 0], m3)

theorem icfCheck_spec (p : Prog) (hp : p.lookup "iota_certs_full_check" = some iotaCertsFullCheckL)
    (n : Nat) (s₀ : St) (mode vis d ty aco acn arg : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_check" [mode, vis, d, ty, aco, acn, arg]
    ⦃fun r s' => LocEq s' s₀ ∧
      icfCheckW p n s₀.mem mode vis d ty aco acn arg = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullCheckL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "inst_list", callW_spec p n "infer", callW_spec p n "defeq"] <;>
    finish [icfCheckW]

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
      tcntM, evalE_tierE, evalE_idxE] <;>
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish [spnGetW, rdW]

/-- Model of `iota_certs_full_forall` (callees at fuel `n`). -/
def icfForallW (p : Prog) (n : Nat) (m : Mem) (mode vis d h aco acn ao an i : Word) :
    Option (List Word × Mem) :=
  match callW p n "iota_certs_full_parts" [h] m with
  | none => none
  | some (pr, m0) =>
  match callW p n "spn_get" [ao + i] m0 with
  | none => none
  | some (ra, m00) =>
  match callW p n "iota_certs_full_check"
      [mode, vis, d, pr.headD 0, aco, acn, ra.headD 0] m00 with
  | none => none
  | some (ok, m3) =>
  if ok.headD 0 = 0 then some ([0], m3)
  else if (aco + acn).toNat < (m3.arr64 SPN).size ∧ (136 : Word).toNat < (m3.arr64 CTL).size then
    match callW p n "iota_certs_full_aux"
        [mode, vis, d, pr.tail.headD 0, aco, acn + 1, ao, an, i + 1]
        ((m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1)) with
    | none => none
    | some (r, m4) => some ([r.headD 0], m4)
  else none

theorem icfForall_spec (p : Prog) (hp : p.lookup "iota_certs_full_forall" = some iotaCertsFullForallL)
    (n : Nat) (s₀ : St) (mode vis d h aco acn ao an i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_forall" [mode, vis, d, h, aco, acn, ao, an, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      icfForallW p n s₀.mem mode vis d h aco acn ao an i = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullForallL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "iota_certs_full_parts", callW_spec p n "spn_get",
    callW_spec p n "iota_certs_full_check", callW_spec p n "iota_certs_full_aux"] <;>
  simp_all [icfForallW, Cmp.eval, BinOp.eval, Mem.len64, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ,
    Sig.retVal, Sig.retOr, CTL, size_set64]

/-- The count index of a tag's table (`CTL[c + tier]`), `none` past the last tag. -/
def evoCnt (g : Word) : Option TRec :=
  if g = 0 then some BVAR else if g = 1 then some FVAR else if g = 2 then some SORT
  else if g = 3 then some CONST else if g = 4 then some APP else if g = 5 then some LAM
  else if g = 6 then some FORALL else if g = 7 then some LET else if g = 8 then some LIT
  else if g = 9 then some PROJ else none

/-- Model of `expr_view_ok`. -/
def evoW (m : Mem) (h : Word) : Option Word :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else match evoCnt (h >>> 28) with
    | none => none
    | some c => if tcnt m c (tierW h) ≤ idxW h then none else some 0

theorem exprViewOk_spec (p : Prog) (hp : p.lookup "expr_view_ok" = some exprViewOkL) (n : Nat)
    (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "expr_view_ok" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ evoW s₀.mem h = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, exprViewOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE] <;>
    finish [evoW, evoCnt, tierW, idxW]

/-- Model of `iota_certs_full_flush` (callees at fuel `n`). -/
def icfFlushW (p : Prog) (n : Nat) (m : Mem) (mode vis d h aco acn ao an i : Word) :
    Option (List Word × Mem) :=
  match callW p n "expr_view_ok" [h] m with
  | none => none
  | some (_, m0) =>
  if acn = 0 then some ([0], m0)
  else match callW p n "inst_list" [h, aco, acn, 0] m0 with
    | none => none
    | some (ty2, m1) =>
      match callW p n "iota_certs_full_aux" [mode, vis, d, ty2.headD 0, aco + acn, 0, ao, an, i] m1 with
      | none => none
      | some (r, m') => some ([r.headD 0], m')

theorem icfFlush_spec (p : Prog) (hp : p.lookup "iota_certs_full_flush" = some iotaCertsFullFlushL)
    (n : Nat) (s₀ : St) (mode vis d h aco acn ao an i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_flush" [mode, vis, d, h, aco, acn, ao, an, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      icfFlushW p n s₀.mem mode vis d h aco acn ao an i = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullFlushL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "inst_list", callW_spec p n "iota_certs_full_aux",
    callW_spec p n "expr_view_ok"] <;>
  simp_all [icfFlushW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ,
    Sig.retVal, Sig.retOr]

/-- Model of `iota_certs_full_aux` (callees at fuel `n`). -/
def icfAuxW (p : Prog) (n : Nat) (m : Mem) (mode vis d h aco acn ao an i : Word) :
    Option (List Word × Mem) :=
  if i < an then
    if h >>> 28 = 6 then
      match callW p n "iota_certs_full_forall" [mode, vis, d, h, aco, acn, ao, an, i] m with
      | none => none
      | some (r, m') => some ([r.headD 0], m')
    else if h >>> 28 = 0 then
      match callW p n "iota_certs_full_flush" [mode, vis, d, h, aco, acn, ao, an, i] m with
      | none => none
      | some (r, m') => some ([r.headD 0], m')
    else match callW p n "expr_view_ok" [h] m with
      | none => none
      | some (_, m') => some ([0], m')
  else some ([1], m)

theorem icfAux_spec (p : Prog) (hp : p.lookup "iota_certs_full_aux" = some iotaCertsFullAuxL)
    (n : Nat) (s₀ : St) (mode vis d h aco acn ao an i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full_aux" [mode, vis, d, h, aco, acn, ao, an, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      icfAuxW p n s₀.mem mode vis d h aco acn ao an i = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullAuxL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "iota_certs_full_forall", callW_spec p n "iota_certs_full_flush",
      callW_spec p n "expr_view_ok"] <;>
    finish [icfAuxW, Locals.init_cons_zero, Locals.init_cons_succ]


section icfRun
variable (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (acc args : Array EIdx) (i : Nat)

theorem icf_run_done (hi : ¬ i < args.size) (a : AState) :
    (iotaCertsFullAux r fe d h acc args i).run a = .ok (true, a) := by
  rw [iotaCertsFullAux]; simp [hi]; rfl

theorem icf_run_stop (hi : i < args.size) (a a1 a2 a3 : AState) (ty body ty2 ta : EIdx)
    (hv : a.store.view h = some (.forallE ty body))
    (h1 : (instantiateListFast coreWalkFuel ty acc 0).run a = .ok (ty2, a1))
    (h2 : (r.infer d args[i]).run a1 = .ok (ta, a2))
    (h3 : (r.defeq d ta ty2).run a2 = .ok (false, a3)) :
    (iotaCertsFullAux r fe d h acc args i).run a = .ok (false, a3) := by
  have hv' : (view h).run a = .ok (.forallE ty body, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h1, h2, h3]
  simp; rfl

theorem icf_run_cont (hi : i < args.size) (a a1 a2 a3 a4 : AState) (ty body ty2 ta : EIdx) (b : Bool)
    (hv : a.store.view h = some (.forallE ty body))
    (h1 : (instantiateListFast coreWalkFuel ty acc 0).run a = .ok (ty2, a1))
    (h2 : (r.infer d args[i]).run a1 = .ok (ta, a2))
    (h3 : (r.defeq d ta ty2).run a2 = .ok (true, a3))
    (h4 : (iotaCertsFullAux r fe d body (acc.push args[i]) args (i + 1)).run a3 = .ok (b, a4)) :
    (iotaCertsFullAux r fe d h acc args i).run a = .ok (b, a4) := by
  have hv' : (view h).run a = .ok (.forallE ty body, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h1, h2, h3]
  simp [h4]

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

theorem icf_run_flush (hi : i < args.size) (a a1 a2 : AState) (x : Nat) (ty2 : EIdx) (b : Bool)
    (hv : a.store.view h = some (.bvar x)) (h0 : acc.size ≠ 0)
    (h1 : (instantiateListFast coreWalkFuel h acc 0).run a = .ok (ty2, a1))
    (h2 : (iotaCertsFullAux r fe d ty2 #[] args i).run a1 = .ok (b, a2)) :
    (iotaCertsFullAux r fe d h acc args i).run a = .ok (b, a2) := by
  have hv' : (view h).run a = .ok (.bvar x, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h0, h1, h2, ↓reduceIte]

end icfRun


/-! ### The refinement of the three functions -/

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
      AM.ok (iotaCertsFullAux (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args
        i.toNat) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem (AM.st (iotaCertsFullAux (coreKnot (decMode mode) fe id F) fe
        d.toNat (decE h) acc args i.toNat) a₀) vis fe MM eb ∧
      AM.res (iotaCertsFullAux (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args
        i.toNat) a₀ = decBool r ∧ ResH r; ⊤⦄

/-- **The domain check refines its three twin steps.** -/
theorem icfCheck_ok (p : Prog) (hil : InstListOK p) (K F : Nat) (hk : KnotUpTo p K) (hnF : K ≤ F)
    (hn62 : K ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ty aco acn arg : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hty : HW ty) (harg : HW arg) (acc : Array EIdx) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hacc : SpineR m aco acn acc)
    (htop : aco.toNat + acn.toNat ≤ (spTop m).toNat) (rr : List Word) (m3 : Mem)
    (h : icfCheckW p K m mode vis d ty aco acn arg = some (rr, m3)) :
    ∃ (ty2 ta : EIdx) (a1 a2 a3 : AState) (b : Bool),
      (instantiateListFast coreWalkFuel (decE ty) acc 0).run a = .ok (ty2, a1) ∧
      ((coreKnot (decMode mode) fe id F).infer d.toNat (decE arg)).run a1 = .ok (ta, a2) ∧
      ((coreKnot (decMode mode) fe id F).defeq d.toNat ta ty2).run a2 = .ok (b, a3) ∧
      CoreAfter dn m m3 a3 vis fe M eb ∧ (rr.headD 0 != 0) = b ∧ HW (rr.headD 0) := by
  simp only [icfCheckW] at h
  rcases c1 : callW p K "inst_list" [ty, aco, acn, 0] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at h
  obtain ⟨ok1, ⟨M1, hS1, hK1, hSt1⟩, res1, hr1⟩ := CoreSpec.of_callW
    (hil K ⟨m, Locals.init []⟩ a dn vis fe M eb ty aco acn 0 acc hS hty hacc htop) c1
  rcases c2 : callW p K "infer" [mode, vis, d, arg] m1 with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at h
  obtain ⟨ok2, ⟨M2, hS2, hK2, hSt2⟩, res2, hr2⟩ := CoreSpec.of_callW
    ((hk K (Nat.le_refl _)).infer F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d arg hnF hn62
      ⟨hS1, hm4, hebm⟩ harg) c2
  rcases c3 : callW p K "defeq" [mode, vis, d, r2.headD 0, r1.headD 0] m2 with _ | ⟨r3, m3'⟩ <;>
    simp only [c3, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨ok3, ⟨M3, hS3, hK3, hSt3⟩, res3, hr3⟩ := CoreSpec.of_callW
    ((hk K (Nat.le_refl _)).defeq F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d _ _ hnF hn62
      ⟨hS2, hm4, hebm⟩ hr2 hr1) c3
  have hrun1 := AM.run_of_ok _ _ ok1
  have hrun2 := AM.run_of_ok _ _ ok2
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res1] at hrun1
  rw [res2] at hrun2
  rw [res3] at hrun3
  exact ⟨_, _, _, _, _, _, hrun1, hrun2, hrun3, ⟨M3, hS3, hK1.trans (hK2.trans hK3),
    hSt1.trans (hSt2.trans hSt3)⟩, rfl, hr3⟩


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

theorem icfForall_ok (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (N : Nat)
    (hA : ∀ N', N = N' + 1 → ICFSpec p "iota_certs_full_aux" (fun _ _ _ => True) N') :
    ICFSpec p "iota_certs_full_forall" (fun h an i => h >>> 28 = 6 ∧ i < an) N := by
  intro F hnF hn62 hk s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS hm4 hebm hh
    ⟨h6, hi⟩ hacc hargs htop hao
  refine triple_post (icfForall_spec p hp.iotaCertsFullForall N s₀ mode vis d h aco acn ao an i)
    fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [icfForallW] at hW
  cases N with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N' =>
  have hA' := hA N' rfl
  have hk' : KnotUpTo p N' := hk.mono (by omega)
  rcases c1 : callW p (N' + 1) "iota_certs_full_parts" [h] s₀.mem with _ | ⟨pr, m0⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨t1, ht1, -, hmem1, hparts⟩ := triple_of_callW
    (icfParts_spec p hp.iotaCertsFullParts N' ⟨s₀.mem, Locals.init []⟩ h) c1
  obtain rfl : m0 = s₀.mem := by rw [← ht1]; exact hmem1
  -- the stored node
  simp only [icfPartsW] at hparts
  obtain ⟨g1, hparts⟩ := of_ite_none hparts
  obtain ⟨g2, hparts⟩ := of_ite_none hparts
  simp only [Option.some.injEq] at hparts
  obtain ⟨hvw, hn1, hn2⟩ := view_forall s₀.mem a₀ hS.arena.1 h hh ⟨g1, UInt64.not_le.mp g2⟩ h6
  simp only [List.cons.injEq, and_true] at hparts
  obtain ⟨hp0, hp1⟩ := hparts
  rw [hp0] at hvw hn1
  rw [hp1] at hvw hn2
  -- the argument
  rcases c2 : callW p (N' + 1) "spn_get" [ao + i] s₀.mem with _ | ⟨ra, m00⟩ <;>
    simp only [c2, reduceCtorEq] at hW
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
  rcases c3 : callW p (N' + 1) "iota_certs_full_check"
      [mode, vis, d, pr.headD 0, aco, acn, ra.headD 0] s₀.mem with _ | ⟨ok, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨t3, ht3, -, hchk⟩ := triple_of_callW
    (icfCheck_spec p hp.iotaCertsFullCheck N' ⟨s₀.mem, Locals.init []⟩ mode vis d (pr.headD 0) aco acn
      (ra.headD 0)) c3
  rw [ht3] at hchk
  have hbd := hacc.bound
  have hspn := hS.spn
  have h263 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
  have htopc : aco.toNat + acn.toNat ≤ (spTop s₀.mem).toNat := by
    rw [← htop, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _
  have hty : HW (pr.headD 0) := hn1
  obtain ⟨ty2, ta, a1, a2, a3, b, hr1, hr2, hr3, hCA3, hbk, hwok⟩ := icfCheck_ok p hil N' F hk'
    (by omega) (by omega) dn vis fe eb mode d (pr.headD 0) aco acn (ra.headD 0) hm4 hebm hty hargw
    acc s₀.mem a₀ MM hS hacc htopc [ok.headD 0] m3 hchk
  rw [← hargget] at hr2
  have hbody : args.size = an.toNat := hargs.size
  have hr1' : (instantiateListFast coreWalkFuel (decE (pr.headD 0)) acc 0).run a₀ = .ok (ty2, a1) := hr1
  by_cases hok0 : ok.headD 0 = 0
  · rw [ite_eq_left (by simpa using hok0)] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b = false := by rw [← hbk, hok0]; rfl
    subst hb
    have hrun := icf_run_stop (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args i.toNat
      hisz a₀ a1 a2 a3 _ _ ty2 ta hvw hr1' hr2 hr3
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine ⟨hokF, ?_, ?_, ?_⟩
    · rw [hstF]; exact hCA3.toG
    · rw [hresF]; show false = (r.headD 0 != 0); rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  · rw [ite_eq_right (by simpa using hok0)] at hW
    obtain ⟨hg, hW⟩ := of_ite_none' hW
    rcases c4 : callW p (N' + 1) "iota_certs_full_aux"
        [mode, vis, d, pr.tail.headD 0, aco, acn + 1, ao, an, i + 1]
        ((m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1)) with _ | ⟨r4, m4⟩ <;>
      simp only [c4, reduceCtorEq] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨M3, hS3, hK3, hSt3⟩ := hCA3
    have hb : b = true := by
      rw [← hbk]; simpa using hok0
    subst hb
    have htop3 : spTop m3 = aco + acn := by rw [hSt3.1, ← htop]
    have hq1 : (aco + acn).toNat + 1 < 2 ^ 64 := by
      have : (aco + acn).toNat < (m3.arr64 SPN).size := hg.1
      have hsz3 : (m3.arr64 SPN).size = (s₀.mem.arr64 SPN).size := hSt3.size
      omega
    obtain ⟨hfr, hsp', hgrew, hslot, hsz⟩ := push_step m3 (aco + acn) (ra.headD 0) hg.1 hg.2 htop3 hq1
    have hS3p := hS3.frame_stk hfr (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
    have hacc3 : SpineR m3 aco acn acc := hacc.keep hSt3.size hSt3.below htopc hS.spn
    have htop3' : aco.toNat + acn.toNat ≤ (spTop m3).toNat := by rw [htop3]; exact (by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _)
    have hsum : (aco + acn).toNat = aco.toNat + acn.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hpush := (SpineR.push hacc3 hS3.spn (by rw [← hsum]; exact hg.1) (ra.headD 0) hargw).setCtl 136
      (aco + acn + 1)
    have hargs3 : SpineR m3 ao an args := hargs.keep hSt3.size hSt3.below (by omega) hS.spn
    have hargs3p : SpineR _ ao an args := hargs3.keep hgrew.size hgrew.below (by omega) hS3.spn
    have htopp : aco + (acn + 1) = spTop ((m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1)) := by
      rw [hsp', UInt64.add_assoc]
    generalize (m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1) = m3p at *
    have hi1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hi
    obtain ⟨t4, ht4, -, hok4, hCAG4, hres4, hr4⟩ := triple_of_callW
      (hA' F (by omega) (by omega) hk' ⟨m3p, Locals.init []⟩ a3 dn vis fe M3 eb mode d (pr.tail.headD 0) aco (acn + 1) ao an
        (i + 1) (acc.push (decE (ra.headD 0))) args hS3p hm4 hebm hn2 trivial hpush hargs3p htopp hao) c4
    rw [hi1] at hok4 hCAG4 hres4
    rw [ht4] at hCAG4
    have hrun4 := AM.run_of_ok _ _ hok4
    rw [hres4] at hrun4
    have hrun := icf_run_cont (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args i.toNat
      hisz a₀ a1 a2 a3 _ _ _ _ _ (decBool r4) hvw hr1' hr2 hr3 (by rw [hargget]; exact hrun4)
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    obtain ⟨M4, hS4, hK4, hGr4⟩ := hCAG4
    refine ⟨hokF, ?_, ?_, ?_⟩
    · rw [hstF]
      exact ⟨M4, hS4, hK3.trans hK4, hSt3.toGrew.trans (hgrew.trans hGr4)⟩
    · rw [hresF]; have hr' : r4.headD 0 = r.headD 0 := by simpa using hr
      simp only [decBool, hr']
    · have hr' : r4.headD 0 = r.headD 0 := by simpa using hr
      unfold ResH HW at hr4 ⊢; rw [← hr']; exact hr4


/-- **A handle that passes `expr_view_ok` views.** -/
theorem evo_view (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : HW h) (w : Word)
    (hev : evoW m h = some w) :
    (∃ v, a.store.view (decE h) = some v) ∧
    (h >>> 28 = 0 → ∃ x, a.store.view (decE h) = some (.bvar x)) ∧
    (h >>> 28 = 6 → ∃ ty body, a.store.view (decE h) = some (.forallE ty body)) ∧
    (h >>> 28 ≠ 0 → h >>> 28 ≠ 6 → ∀ v, a.store.view (decE h) = some v →
      (∀ ty body, v ≠ .forallE ty body) ∧ (∀ x, v ≠ .bvar x)) := by
  simp only [evoW] at hev
  obtain ⟨g1, hev⟩ := of_ite_none hev
  cases hc : evoCnt (h >>> 28) with
  | none => rw [hc] at hev; cases hev
  | some c =>
  rw [hc] at hev
  simp only at hev
  by_cases g2 : tcnt m c (tierW h) ≤ idxW h
  · rw [ite_eq_left g2] at hev; cases hev
  have hv : viewOK m h c := ⟨g1, UInt64.not_le.mp g2⟩
  simp only [evoCnt] at hc
  by_cases t0 : h >>> 28 = 0
  · simp [t0] at hc
    subst hc
    have := view_bvar m a hR h hh hv t0
    refine ⟨⟨_, this⟩, fun _ => ⟨_, this⟩, fun h6 => by rw [t0] at h6; exact absurd h6 (by decide),
      fun h0 => absurd t0 h0⟩
  by_cases t1 : h >>> 28 = 1
  · simp [t1] at hc
    subst hc
    obtain ⟨i, ty, hvw⟩ := view_fvar m a hR h hh hv t1
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t1] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t2 : h >>> 28 = 2
  · simp [t2] at hc
    subst hc
    obtain ⟨u, hvw⟩ := view_sort m a hR h hh hv t2
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t2] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t3 : h >>> 28 = 3
  · simp [t3] at hc
    subst hc
    obtain ⟨n, us, hvw⟩ := view_const m a hR h hh hv t3
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t3] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t4 : h >>> 28 = 4
  · simp [t4] at hc
    subst hc
    obtain ⟨hvw, -⟩ := view_app m a hR h hh hv t4
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t4] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t5 : h >>> 28 = 5
  · simp [t5] at hc
    subst hc
    obtain ⟨hvw, -⟩ := view_lam m a hR h hh hv t5
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => by rw [t5] at h6; exact absurd h6 (by decide),
      fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t6 : h >>> 28 = 6
  · simp [t6] at hc
    subst hc
    obtain ⟨hvw, -⟩ := view_forall m a hR h hh hv t6
    exact ⟨⟨_, hvw⟩, fun h0 => absurd t6 (by rw [h0]; decide), fun _ => ⟨_, _, hvw⟩,
      fun _ h6 => absurd t6 h6⟩
  by_cases t7 : h >>> 28 = 7
  · simp [t7] at hc
    subst hc
    obtain ⟨hvw, -⟩ := view_let m a hR h hh hv t7
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => absurd h6 t6, fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t8 : h >>> 28 = 8
  · simp [t8] at hc
    subst hc
    obtain ⟨l, hvw⟩ := view_lit m a hR h hh hv t8
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => absurd h6 t6, fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  by_cases t9 : h >>> 28 = 9
  · simp [t9] at hc
    subst hc
    obtain ⟨hvw, -⟩ := view_proj m a hR h hh hv t9
    refine ⟨⟨_, hvw⟩, fun h0 => absurd h0 t0, fun h6 => absurd h6 t6, fun _ _ v hv' => ?_⟩
    rw [hvw] at hv'; cases hv'; exact ⟨fun _ _ => by simp, fun _ => by simp⟩
  simp [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] at hc


theorem icfFlush_ok (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (N : Nat)
    (hA : ∀ N', N = N' + 1 → ICFSpec p "iota_certs_full_aux" (fun _ _ _ => True) N') :
    ICFSpec p "iota_certs_full_flush" (fun h an i => h >>> 28 = 0 ∧ i < an) N := by
  intro F hnF hn62 hk s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS hm4 hebm hh
    ⟨h0, hi⟩ hacc hargs htop hao
  refine triple_post (icfFlush_spec p hp.iotaCertsFullFlush N s₀ mode vis d h aco acn ao an i) fun
    r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [icfFlushW] at hW
  cases N with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N' =>
  have hA' := hA N' rfl
  have hk' : KnotUpTo p N' := hk.mono (by omega)
  rcases c0 : callW p (N' + 1) "expr_view_ok" [h] s₀.mem with _ | ⟨rv, m0⟩ <;>
    simp only [c0, reduceCtorEq] at hW
  obtain ⟨t0, ht0, -, hmem0, hev⟩ := triple_of_callW
    (exprViewOk_spec p hp.exprViewOk N' ⟨s₀.mem, Locals.init []⟩ h) c0
  obtain rfl : m0 = s₀.mem := by rw [← ht0]; exact hmem0
  obtain ⟨-, hB, -, -⟩ := evo_view s₀.mem a₀ hS.arena.1 h hh _ hev
  obtain ⟨x, hvx⟩ := hB h0
  by_cases hacn : acn = 0
  · rw [ite_eq_left hacn] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hsz : acc.size = 0 := by rw [hacc.size, hacn]; rfl
    have hrun := icf_run_nil (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args i.toNat
      (by rw [hargs.size]; exact hi) a₀ x hvx hsz
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine ⟨hokF, ?_, ?_, ?_⟩
    · rw [hstF, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, (StackKept.refl _).toGrew⟩
    · rw [hresF]; show false = (r.headD 0 != 0); rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [ite_eq_right hacn] at hW
  rcases c1 : callW p (N' + 1) "inst_list" [h, aco, acn, 0] s₀.mem with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  have hbd := hacc.bound
  have hspn := hS.spn
  have h263 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
  have hsum : (aco + acn).toNat = aco.toNat + acn.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have htopc : aco.toNat + acn.toNat ≤ (spTop s₀.mem).toNat := by
    rw [← htop, hsum]; exact Nat.le_refl _
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    (hil (N' + 1) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb h aco acn 0 acc hS hh hacc htopc) c1
  rcases c2 : callW p (N' + 1) "iota_certs_full_aux"
      [mode, vis, d, r1.headD 0, aco + acn, 0, ao, an, i] m1 with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hsp1 : spTop m1 = aco + acn := by rw [hSt1.1, ← htop]
  have hsz1 : (m1.arr64 SPN).size = (s₀.mem.arr64 SPN).size := hSt1.size
  have hnil : SpineR m1 (aco + acn) 0 #[] := SpineR.nil_at m1 _ (by rw [hsum]; omega)
  have hargs1 : SpineR m1 ao an args := hargs.keep hSt1.size hSt1.below (by omega) hS.spn
  obtain ⟨t2, ht2, -, hok2, hCAG2, hres2, hr2⟩ := triple_of_callW
    (hA' F (by omega) (by omega) hk' ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d (r1.headD 0)
      (aco + acn) 0 ao an i #[] args hS1 hm4 hebm hr1 trivial hnil hargs1
      (by rw [UInt64.add_zero]; exact hsp1.symm) (by omega)) c2
  rw [ht2] at hCAG2
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  have hrun := icf_run_flush (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args i.toNat
    (by rw [hargs.size]; exact hi) a₀ _ _ x _ (decBool r2) hvx
    (by rw [hacc.size]; intro h0; exact hacn (UInt64.toNat_inj.mp (by simpa using h0))) hrun1 hrun2
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨M2, hS2, hK2, hGr2⟩ := hCAG2
  have hr' : r2.headD 0 = r.headD 0 := by simpa using hr
  refine ⟨hokF, ?_, ?_, ?_⟩
  · rw [hstF]; exact ⟨M2, hS2, hK1.trans hK2, hSt1.toGrew.trans hGr2⟩
  · rw [hresF]; simp only [decBool, hr']
  · unfold ResH HW at hr2 ⊢; rw [← hr']; exact hr2


theorem icfAux_ok (p : Prog) (hp : IotaProg4 p) (N : Nat)
    (hFo : ∀ N', N = N' + 1 →
      ICFSpec p "iota_certs_full_forall" (fun h an i => h >>> 28 = 6 ∧ i < an) N')
    (hFl : ∀ N', N = N' + 1 →
      ICFSpec p "iota_certs_full_flush" (fun h an i => h >>> 28 = 0 ∧ i < an) N') :
    ICFSpec p "iota_certs_full_aux" (fun _ _ _ => True) N := by
  intro F hnF hn62 hk s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS hm4 hebm hh
    _ hacc hargs htop hao
  refine triple_post (icfAux_spec p hp.iotaCertsFullAux N s₀ mode vis d h aco acn ao an i) fun r s'
    ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [icfAuxW] at hW
  by_cases hni : ¬ i < an
  · rw [ite_eq_right hni] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hi' : ¬ i.toNat < args.size := by rw [hargs.size]; exact hni
    have hrun := icf_run_done (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args i.toNat
      hi' a₀
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    have hr0 : r.headD 0 = 1 := by simpa using hr.symm
    refine ⟨hokF, ?_, ?_, ?_⟩
    · rw [hstF, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, (StackKept.refl _).toGrew⟩
    · rw [hresF]; show true = (r.headD 0 != 0); rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  have hi := Classical.not_not.mp hni
  rw [ite_eq_left hi] at hW
  by_cases h6 : h >>> 28 = 6
  · rw [ite_eq_left h6] at hW
    cases N with
    | zero => rw [callW_zero] at hW; cases hW
    | succ N' =>
    rcases c1 : callW p (N' + 1) "iota_certs_full_forall" [mode, vis, d, h, aco, acn, ao, an, i]
        s₀.mem with _ | ⟨r1, m1⟩ <;> simp only [c1, reduceCtorEq] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨t1, ht1, -, hok1, hCAG1, hres1, hr1⟩ := triple_of_callW
      (hFo N' rfl F (by omega) (by omega) (hk.mono (by omega)) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM
        eb mode d h aco acn ao an i acc args hS hm4 hebm hh ⟨h6, hi⟩ hacc hargs htop hao) c1
    rw [ht1] at hCAG1
    have hr' : r1.headD 0 = r.headD 0 := by simpa using hr
    refine ⟨hok1, hCAG1, ?_, ?_⟩
    · rw [hres1]; simp only [decBool, hr']
    · unfold ResH HW at hr1 ⊢; rw [← hr']; exact hr1
  rw [ite_eq_right h6] at hW
  by_cases h0 : h >>> 28 = 0
  · rw [ite_eq_left h0] at hW
    cases N with
    | zero => rw [callW_zero] at hW; cases hW
    | succ N' =>
    rcases c1 : callW p (N' + 1) "iota_certs_full_flush" [mode, vis, d, h, aco, acn, ao, an, i]
        s₀.mem with _ | ⟨r1, m1⟩ <;> simp only [c1, reduceCtorEq] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨t1, ht1, -, hok1, hCAG1, hres1, hr1⟩ := triple_of_callW
      (hFl N' rfl F (by omega) (by omega) (hk.mono (by omega)) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM
        eb mode d h aco acn ao an i acc args hS hm4 hebm hh ⟨h0, hi⟩ hacc hargs htop hao) c1
    rw [ht1] at hCAG1
    have hr' : r1.headD 0 = r.headD 0 := by simpa using hr
    refine ⟨hok1, hCAG1, ?_, ?_⟩
    · rw [hres1]; simp only [decBool, hr']
    · unfold ResH HW at hr1 ⊢; rw [← hr']; exact hr1
  rw [ite_eq_right h0] at hW
  cases N with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N' =>
  rcases c1 : callW p (N' + 1) "expr_view_ok" [h] s₀.mem with _ | ⟨rv, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨t1, ht1, -, hmem1, hev⟩ := triple_of_callW
    (exprViewOk_spec p hp.exprViewOk N' ⟨s₀.mem, Locals.init []⟩ h) c1
  obtain rfl : m1 = s₀.mem := by rw [← ht1]; exact hmem1
  obtain ⟨⟨v, hv⟩, -, -, hD⟩ := evo_view s₀.mem a₀ hS.arena.1 h hh _ hev
  obtain ⟨hn1, hn2⟩ := hD h0 h6 v hv
  have hrun := icf_run_other (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args i.toNat
    (by rw [hargs.size]; exact hi) a₀ (fun ty body hc => by rw [hv] at hc; exact hn1 ty body (Option.some.inj hc))
    (fun x hc => by rw [hv] at hc; exact hn2 x (Option.some.inj hc)) v hv
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
  have hr0 : r.headD 0 = 0 := by simpa using hr.symm
  refine ⟨hokF, ?_, ?_, ?_⟩
  · rw [hstF, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, (StackKept.refl _).toGrew⟩
  · rw [hresF]; show false = (r.headD 0 != 0); rw [hr0]; rfl
  · unfold ResH HW; rw [hr0]; decide


theorem icf_all (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (N : Nat) :
    ICFSpec p "iota_certs_full_aux" (fun _ _ _ => True) N ∧
    ICFSpec p "iota_certs_full_forall" (fun h an i => h >>> 28 = 6 ∧ i < an) N ∧
    ICFSpec p "iota_certs_full_flush" (fun h an i => h >>> 28 = 0 ∧ i < an) N := by
  induction N with
  | zero =>
    exact ⟨icfAux_ok p hp 0 (fun _ h => absurd h (by simp)) (fun _ h => absurd h (by simp)),
      icfForall_ok p hp hil 0 (fun _ h => absurd h (by simp)),
      icfFlush_ok p hp hil 0 (fun _ h => absurd h (by simp))⟩
  | succ N ih =>
    exact ⟨icfAux_ok p hp (N + 1) (fun N' h => by cases Nat.succ.inj h; exact ih.2.1)
        (fun N' h => by cases Nat.succ.inj h; exact ih.2.2),
      icfForall_ok p hp hil (N + 1) (fun N' h => by cases Nat.succ.inj h; exact ih.1),
      icfFlush_ok p hp hil (N + 1) (fun N' h => by cases Nat.succ.inj h; exact ih.1)⟩

/-- **`iota_certs_full_aux` refines `iotaCertsFullAux`.** Statement changes: the shape of
`rec_fire_args`' (a triple with `CoreAfterG`: the accumulator pushes leave the stack top raised,
`CoreSpec` requires it kept); `n ≤ 2 ^ 62`, the eager bit, `ao + an ≤ aco`. The L function is split
(`iota_certs_full_forall`/`_flush`/`_check`/`_parts`, `spn_get`, `expr_view_ok`: `vcgen` fuel, and
the twin's `view` of a handle needs the L side to check it). -/
theorem iotaCertsFullAux_refines' (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (n : Nat) :
    ICFSpec p "iota_certs_full_aux" (fun _ _ _ => True) n := (icf_all p hp hil n).1

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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
    finish [ctlGetW, rdW]

/-- Model of `iota_certs_full`. -/
def icfTopW (p : Prog) (n : Nat) (m : Mem) (mode vis d h ao an : Word) :
    Option (List Word × Mem) :=
  match callW p n "ctl_get" [136] m with
  | none => none
  | some (t, m0) =>
  match callW p n "iota_certs_full_aux" [mode, vis, d, h, t.headD 0, 0, ao, an, 0] m0 with
  | none => none
  | some (r, m') =>
    if (136 : Word).toNat < (m'.arr64 CTL).size then
      some ([r.headD 0], m'.set64 CTL 136 (t.headD 0))
    else none

theorem iotaCertsFull_spec (p : Prog) (hp : p.lookup "iota_certs_full" = some iotaCertsFullL)
    (n : Nat) (s₀ : St) (mode vis d h ao an : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_certs_full" [mode, vis, d, h, ao, an]
    ⦃fun r s' => LocEq s' s₀ ∧ icfTopW p n s₀.mem mode vis d h ao an = some ([r.headD 0], s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaCertsFullL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "ctl_get", callW_spec p n "iota_certs_full_aux"] <;>
  simp_all [icfTopW, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ,
    Sig.retVal, Sig.retOr, CTL]

/-- **`iota_certs_full` refines `iotaCertsFull`.** Statement changes: `n ≤ 2 ^ 62`, the eager bit. -/
theorem iotaCertsFull_refines' (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h ao an : Word) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW h →
    SpineR s₀.mem ao an args → ao + an = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_certs_full" [mode, vis, d, h, ao, an]
      (iotaCertsFull (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) args.toList) decBool s₀
      a₀ dn vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d h ao an args hS hm4 hebm hh hargs htop
  refine triple_post (iotaCertsFull_spec p hp.iotaCertsFull n s₀ mode vis d h ao an) fun r s'
    ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [icfTopW] at hW
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ n' =>
  rcases c0 : callW p (n' + 1) "ctl_get" [136] s₀.mem with _ | ⟨t, m0⟩ <;>
    simp only [c0, reduceCtorEq] at hW
  obtain ⟨t0, ht0, -, hmem0, hget⟩ := triple_of_callW
    (ctlGet_spec p hp.ctlGet n' ⟨s₀.mem, Locals.init []⟩ 136) c0
  obtain rfl : m0 = s₀.mem := by rw [← ht0]; exact hmem0
  have ht : t.headD 0 = rdW (s₀.mem.arr64 CTL) 136 := by
    simp only [ctlGetW] at hget
    split at hget
    · simp only [Option.some.injEq] at hget; rw [← hget]
    · cases hget
  have htop' : t.headD 0 = ao + an := by rw [ht]; exact htop.symm
  rcases c1 : callW p (n' + 1) "iota_certs_full_aux"
      [mode, vis, d, h, t.headD 0, 0, ao, an, 0] s₀.mem with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨g136', hW⟩ := of_ite_none' hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hbd := hargs.bound
  have hspn := hS.spn
  have h263 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
  have hsum : (ao + an).toNat = ao.toNat + an.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hnil : SpineR s₀.mem (t.headD 0) 0 #[] :=
    SpineR.nil_at s₀.mem _ (by rw [htop', hsum]; omega)
  obtain ⟨t1, ht1, -, hok1, hCAG1, hres1, hr1⟩ := triple_of_callW
    ((icf_all p hp hil n').1 F (by omega) (by omega) (hk.mono (by omega)) ⟨s₀.mem, Locals.init []⟩ a₀
      dn vis fe MM eb mode d h (t.headD 0) 0 ao an 0 #[] args hS hm4 hebm hh trivial
      hnil hargs (by rw [UInt64.add_zero, htop']; exact htop) (by rw [htop', hsum]; omega)) c1
  rw [ht1] at hCAG1
  obtain ⟨M1, hS1, hK1, hGr1⟩ := hCAG1
  have hT : iotaCertsFull (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) args.toList =
      iotaCertsFullAux (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) #[] args
        (0 : Word).toNat := by
    simp only [iotaCertsFull, Array.toArray_toList]; rfl
  rw [hT, ← hm]
  have hrest : StackKept s₀.mem (m1.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136)) :=
    StackKept.restoreG hGr1 g136'
  rw [← ht] at hrest
  refine ⟨hok1, ⟨M1, ?_, hK1, hrest⟩, ?_, ?_⟩
  · exact hS1.frame_stk (MemFrame.setCtl m1 136 _) (by simp) (by simp)
  · rw [hres1]
    have hr' : r1.headD 0 = r.headD 0 := by simpa using hr
    simp only [decBool, hr']
  · have hr' : r1.headD 0 = r.headD 0 := by simpa using hr
    unfold ResH HW at hr1 ⊢; rw [← hr']; exact hr1

end L.Arena
