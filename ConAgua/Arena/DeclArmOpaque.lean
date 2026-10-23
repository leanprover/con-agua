import ConAgua.Arena.DeclReducePin
import ConAgua.Arena.DeclArmLoop

/-!
# The opaque arm `check_decl_opaque(i, vis)` (lane `decls3`)

`checkDecl`'s `.opaqueDecl` arm: the constant check, the opaque check (the push of `axiomInfo cv`),
then for `Lean.reduceNat`/`Lean.reduceBool` the install pin (`check_reduce_pin`) at the pushed
view. At the loop's relation through the arms' text (`DeclArmLoop.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsR DeclAt CVAt dw)

section model
variable (p : Prog)

/-- After `check_reduce_pin`: the pushed view. -/
def cdoK6 (w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m6) => some ([w], m6)

/-- After the `reduceBool` pin: the install pin for the two reduce operations. -/
def cdoK5 (n : Nat) (vis nm v w a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if nm = a ∨ nm = r5.headD 0 then cdoK6 w (callW p n "check_reduce_pin" [vis, w, nm, v] m5)
    else some ([w], m5)

/-- After the `reduceNat` pin. -/
def cdoK4 (n : Nat) (vis nm v w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => cdoK5 p n vis nm v w (r4.headD 0) (pinAtW m4 44)

/-- After `check_opaque_val`. -/
def cdoK3 (n : Nat) (vis nm v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => cdoK4 p n vis nm v (r3.headD 0) (pinAtW m3 43)

/-- After `check_constant_val`. -/
def cdoK2 (n : Nat) (vis q nm v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => cdoK3 p n vis nm v (callW p n "check_opaque_val" [vis, q] m2)

/-- After `erec_ci`. -/
def cdoK1 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cdoK2 p n vis (r1.headD 0) (rdW (m1.arr64 EREC) (r1.headD 0 + 1))
      (rdW (m1.arr64 EREC) (r1.headD 0 + 5))
      (callW p n "check_constant_val" [vis, r1.headD 0 + 1] m1)

/-- **The model of `check_decl_opaque(i, vis)`.** -/
def cdoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => cdoK1 p n vis (erecCiW n m i 0)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (i vis q nm v w a : Word)
  (r1 r2 r3 r4 r5 r6 : List Word)
theorem cdoW_step : cdoW p (n + 1) m i vis = cdoK1 p n vis (erecCiW n m i 0) := rfl
theorem cdoK1_some : cdoK1 p n vis (some (r1, m1)) =
    cdoK2 p n vis (r1.headD 0) (rdW (m1.arr64 EREC) (r1.headD 0 + 1))
      (rdW (m1.arr64 EREC) (r1.headD 0 + 5))
      (callW p n "check_constant_val" [vis, r1.headD 0 + 1] m1) := rfl
theorem cdoK2_some : cdoK2 p n vis q nm v (some (r2, m2)) =
    cdoK3 p n vis nm v (callW p n "check_opaque_val" [vis, q] m2) := rfl
theorem cdoK3_some : cdoK3 p n vis nm v (some (r3, m3)) =
    cdoK4 p n vis nm v (r3.headD 0) (pinAtW m3 43) := rfl
theorem cdoK4_some : cdoK4 p n vis nm v w (some (r4, m4)) =
    cdoK5 p n vis nm v w (r4.headD 0) (pinAtW m4 44) := rfl
theorem cdoK5_some : cdoK5 p n vis nm v w a (some (r5, m5)) =
    if nm = a ∨ nm = r5.headD 0 then cdoK6 w (callW p n "check_reduce_pin" [vis, w, nm, v] m5)
    else some ([w], m5) := rfl
theorem cdoK6_some : cdoK6 w (some (r6, m6)) = some ([w], m6) := rfl
end arms

grind_pattern [ind_grind] cdoW_step => cdoW p (n + 1) m i vis
grind_pattern [ind_grind] cdoK1_some => cdoK1 p n vis (some (r1, m1))
grind_pattern [ind_grind] cdoK2_some => cdoK2 p n vis q nm v (some (r2, m2))
grind_pattern [ind_grind] cdoK3_some => cdoK3 p n vis nm v (some (r3, m3))
grind_pattern [ind_grind] cdoK4_some => cdoK4 p n vis nm v w (some (r4, m4))
grind_pattern [ind_grind] cdoK5_some => cdoK5 p n vis nm v w a (some (r5, m5))
grind_pattern [ind_grind] cdoK6_some => cdoK6 w (some (r6, m6))

set_option maxHeartbeats 1600000 in
theorem cdo_specW (hp : p.lookup "check_decl_opaque" = some checkDeclOpaque) (hR : RecProg p)
    (hpa : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_opaque" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdoW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclOpaque]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erecCi_specW p hR n,
        callW_spec p n "check_constant_val", callW_spec p n "check_opaque_val",
        pinAt_specW p hpa n, callW_spec p n "check_reduce_pin"] <;>
      finish (gen := 20) [rdW_eq]

end model

local notation "V" => ConLeche.CheckMode.verified

/-- **The opaque arm at the stage relation.** -/
theorem cdoW_ok {p : Prog} (hV : ValProg p) (hC : CrpProg p) {dn : NIdx → Option ConLeche.Name}
    (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {i : Word}
    {r : List Word} {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal}
    {v : EIdx} (h : cdoW p n m i vis = some (r, m')) (hS : StageR dn vis fe m a)
    (hD : DeclsR (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .opaqueDecl cv v) :
    ∃ fe' a', (checkDecl V pins fe (.opaqueDecl cv v)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ IWGrow m m' := by
  cases n with
  | zero => simp [cdoW] at h
  | succ n =>
  rw [cdoW_step] at h
  cases h1 : erecCiW n m i 0 with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdoK1_some] at h
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_ok (ci := .axiomInfo cv) h1 hS hD hi (by rw [hd]; rfl)
  rw [hd] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq : r1.headD 0 = q at h hci1 hcv1 hval1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.2.2.1; have := hS1.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  have hq5 : (q + 5).toNat = q.toNat + 5 := toNat_add_small q 5 (by omega)
  -- the name and value words
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hval1
  rw [rdW_of_get? hq1.symm (erecP_get hwn), rdW_of_get? hq5.symm (erecP_get hwv)] at h
  -- `check_constant_val`
  cases h2 : callW p n "check_constant_val" [vis, q + 1] m1 with
  | none => rw [h2] at h; cases h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cdoK2_some] at h
  obtain ⟨s2, hs2, -, hok2, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (checkConstantVal_refines p hV n ⟨m1, Locals.init []⟩ a dn fe vis (q + 1) cv hS1
      (by rw [hq1]; exact hcv1) (by omega)) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  generalize AM.st (checkConstantVal V fe cv) a = a2 at hrun2 hS2
  -- `check_opaque_val`
  cases h3 : callW p n "check_opaque_val" [vis, q] s2.mem with
  | none => rw [h3] at h; cases h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, cdoK3_some] at h
  have hx2 : ArrExt (erecP m1) (erecP s2.mem) := IWGrow.erecPExt hg2
  obtain ⟨s3, hs3, -, hok3, hS3, hg3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (checkOpaqueVal_refines p hV n ⟨s2.mem, Locals.init []⟩ a2 dn fe vis q cv (decI wv) hS2
      (ArrExt.decCI hx2 hci1) (ArrExt.hd? hx2 hval1)) h3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  have hres3 : AM.res (checkOpaqueVal V fe cv (decI wv)) a2 = fe.push (.axiomInfo cv) := by
    obtain ⟨a', hr, -, -⟩ := dvW_ok (p := p) hV.rcp "type mismatch in opaque"
      (by
        obtain ⟨s', hs', -, hW'⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
          (ov_specW p hV n ⟨s2.mem, Locals.init []⟩ vis q) h3
        rw [hs'] at hW'; exact hW') hS2 (ArrExt.decCI hx2 hci1)
        (by have := ArrExt.decCV hx2 (decCI_cv hci1 (.inr rfl)); exact this)
        (ArrExt.hd? hx2 hval1)
    rw [← checkOpaqueVal_dvT] at hr
    simp [AM.res, hr]
  rw [hres3] at hS3 hrun3
  generalize AM.st (checkOpaqueVal V fe cv (decI wv)) a2 = a3 at hrun3 hS3
  generalize hfe2 : fe.push (.axiomInfo cv) = fe2 at hS3 hrun3
  -- the two pins
  cases h4 : pinAtW s3.mem 43 with
  | none => rw [h4] at h; cases h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, cdoK4_some] at h
  obtain ⟨hm4, hr4, -, -⟩ := pinAtW_ok h4 hS3.1.pins
  rw [hm4] at h
  cases h5 : pinAtW s3.mem 44 with
  | none => rw [h5] at h; cases h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, cdoK5_some] at h
  obtain ⟨hm5, hr5, -, -⟩ := pinAtW_ok h5 hS3.1.pins
  subst hm5
  have e4 : r4.headD 0 = pinW s3.mem (1 + (43 : Word).toNat) := by rw [hr4]; rfl
  have e5 : r5.headD 0 = pinW s3.mem (1 + (44 : Word).toNat) := by rw [hr5]; rfl
  have hflag : pinW s3.mem 0 ≠ 0 := by intro h0; simp [pinAtW, h0] at h4
  have hF := hS3.1.pins.full hflag
  have hcont : (reduceOpNames.run a3) =
      .ok ((List.range' 44 2).map (fun j => decI (pinW s3.mem j)), a3) := reduceOpNames_run hF
  have hiff := contains_pins hF hwnl 44 2 (by omega) (by omega)
  have hvis : fe.visibleBelow = vis.toNat := hS.1.env.vis
  by_cases hin : wn = r4.headD 0 ∨ wn = r5.headD 0
  · rw [if_pos hin] at h
    rw [e4, e5] at hin
    have hc : ((List.range' 44 2).map fun j => (decI (pinW s3.mem j) : NIdx)).contains (decI wn) =
        true := by
      rw [hiff]
      rcases hin with e | e
      · exact ⟨44, by omega, by omega, e.symm⟩
      · exact ⟨45, by omega, by omega, e.symm⟩
    cases h6 : callW p n "check_reduce_pin" [vis, r3.headD 0, wn, wv] s3.mem with
    | none => rw [h6] at h; cases h
    | some rm6 =>
    obtain ⟨r6, m6⟩ := rm6
    rw [h6, cdoK6_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨s6, hs6, -, hok6, hS6, hg6, -⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
      (checkReducePin_refines p hC dn hdn vis (r3.headD 0) fe2 wn wv hwnl hwvl n
        ⟨s3.mem, Locals.init []⟩ a3 hS3) h6
    subst hs6
    have hrun6 := AM.run_of_ok _ _ hok6
    refine ⟨fe2, _, ?_, by simpa using hS6, hg1.trans (hg2.trans (hg3.trans hg6))⟩
    show (do checkConstantVal V fe cv
             let fe2 ← checkOpaqueVal V fe cv (decI wv)
             if (← reduceOpNames).contains cv.name then
               checkReducePin V (fe2.restrictTo fe.visibleBelow) fe2 cv.name (decI wv)
             pure fe2).run a = _
    simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, hcont, hname, hc, if_true, hvis]
    simp only [hrun6, exc_ok_bind', StateT.run_pure]
    rfl
  · rw [if_neg hin] at h
    rw [e4, e5] at hin
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc : ((List.range' 44 2).map fun j => (decI (pinW s3.mem j) : NIdx)).contains (decI wn) =
        false := by
      cases hcb : ((List.range' 44 2).map fun j => (decI (pinW s3.mem j) : NIdx)).contains (decI wn)
      · rfl
      exfalso
      rw [hiff] at hcb
      obtain ⟨j, hj1, hj2, e⟩ := hcb
      apply hin
      have : j = 44 ∨ j = 45 := by omega
      rcases this with rfl | rfl
      · exact .inl e.symm
      · exact .inr e.symm
    refine ⟨fe2, _, ?_, by simpa using hS3, hg1.trans (hg2.trans hg3)⟩
    show (do checkConstantVal V fe cv
             let fe2 ← checkOpaqueVal V fe cv (decI wv)
             if (← reduceOpNames).contains cv.name then
               checkReducePin V (fe2.restrictTo fe.visibleBelow) fe2 cv.name (decI wv)
             pure fe2).run a = _
    simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, hcont, hname, hc, Bool.false_eq_true,
      if_false, StateT.run_pure]
    rfl

/-- **`check_decl_opaque` refines `checkDecl`'s `.opaqueDecl` arm** at the loop's relation
(through the core's, the walks' and the ROM stubs). -/
theorem checkDeclOpaque_loop' {p : Prog} (hA : ArmProg p) (hV : ValProg p) (hC : CrpProg p)
    (hp : p.lookup "check_decl_opaque" = some checkDeclOpaque) (pins : List INatOpPinSet)
    (dn : NIdx → Option ConLeche.Name) (hdn : DnInj dn) (ds : Array IDeclaration) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (i : Word) (cv : IConstantVal) (v : EIdx), i.toNat < ds.size →
      ds[i.toNat]? = some (.opaqueDecl cv v) → LoopR pins dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl_opaque" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl V pins fe (.opaqueDecl cv v)) a₀ ∧
      LoopR pins dn s'.mem (AM.st (checkDecl V pins fe (.opaqueDecl cv v)) a₀) (r.headD 0)
        (AM.res (checkDecl V pins fe (.opaqueDecl cv v)) a₀) pend ds; ⊤⦄ := by
  intro n s₀ a₀ vis fe pend i cv v hi hd hR
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (cdo_specW p hp hV.rcp hC.red.pa n s₀ i vis)
  obtain ⟨hf, -⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (hA.closed.memFrame n (f := "check_decl_opaque") (by decide) [i, vis] s₀)
  subst hs
  have hd' : ds[i.toNat] = .opaqueDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨fe', a', hrun', hS', hg'⟩ :=
    cdoW_ok (pins := pins) hV hC hdn hW ⟨hR.check, hR.iw⟩ hR.decls hi hd'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hloc, hok, ?_⟩
  rw [hst, hres]
  exact hR.of_step hS' hf (IWGrow.erecPExt hg')

end L.Arena
