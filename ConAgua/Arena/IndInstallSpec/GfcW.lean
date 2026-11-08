module

import ConAgua.Arena.RecGenSpec.DecB
public import ConAgua.Arena.RecGenSpec.DecCIIndCv
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPosSpec.CrLook
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.RecClassSpec.MjProg
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndPosSpec.NoGoStep
import all ConAgua.Arena.RecGen

@[expose] public section

/-!
# GfcW

`gftLoop`, `genRecCheckFormerTys'`, `genRecCheckFormerTys_eq`, `gftW`, `gftW_exit`, `gftW_step` and the lemmas only they use.
-/


/-!
# Refinements of `IndInstall`, part 38 (lane `indproofs4`, helper `grc`): `gen_rec_check`'s loops

Three `while`-loop helpers of `gen_rec_check_prep` (`RecGen.lean`), each loop a named block
(`lblk`, spliced back by `rfl`) with a word model by fuel:

* `gen_rec_check_former_tys(cvTas)`: `cvTas.map (·.type)` into a fresh slice (`gftW`);
* `gen_rec_check_former_tys_c(vis, cvTas, ms2)`: `ms2.mapM (classFormerTy fe cvTas)` into a fresh
  slice (`gfcW`, through `classFormerTy_refines`);
* `gen_rec_check_minor_ok(slots, ctors)`: the minor premises counted (`mk1W`, through
  `class_slot_is_minor`'s `0`/`1`) against the classes' constructors summed (`mk2W`; a sum past
  `2^64` returns `0`, as the twin's comparison is then false).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `gen_rec_check_former_tys`: `cvTas.map (·.type)` -/

l_model gft_spec (p : Prog) (hp : p.lookup "gen_rec_check_former_tys" = some genRecCheckFormerTys)
  fns [hp ↦ gftW list]
  specs [callW_spec p n "iw_alloc"]
  grind [arena_grind] extra [ld64_rd_spec]

section rel
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}

/-- **The loop writes the types.** -/
theorem gftW_ok (p : Prog) (s0 m1 : Mem) (o l q : Word) (cvTas : List IConstantVal)
    (hcv : PSlR decCVp cvTas o l s0) (hq : q.toNat = iwTop s0) (hT : iwTop m1 = q.toNat + l.toNat)
    (f : Nat) : ∀ (m m' : Mem) (j : Word), gftW.loop1 p f m o l q j = some m' →
    StageR vis fe m a → IWGrow s0 m → iwTop m = iwTop m1 → MFr [] [] m1 m → j ≤ l →
    decHL m q.toNat j.toNat = some ((cvTas.map (·.type)).take j.toNat) →
    StageR vis fe m' a ∧ IWGrow s0 m' ∧ iwTop m' = iwTop m1 ∧ MFr [] [] m1 m' ∧
      decHL m' q.toNat l.toNat = some (cvTas.map (·.type)) := by
  sorry

end rel

/-- **`gen_rec_check_former_tys` is `cvTas.map (·.type)`**, a fresh slice. -/
theorem genRecCheckFormerTys_refines {p : Prog} (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "gen_rec_check_former_tys" = some genRecCheckFormerTys) (n : Nat) (s₀ : St) (a : AState)
    {vis : Word} {fe : IFEnv} (cO cL : Word) (cvTas : List IConstantVal)
    (hS : StageR vis fe s₀.mem a) (hcv : PSlR decCVp cvTas cO cL s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_former_tys" [cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR vis fe s'.mem a ∧ IWGrow s₀.mem s'.mem ∧ MFr [] [] s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat = some (cvTas.map (·.type)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (gft_spec p hp (n + 1) s₀ cO cL) ?_
  rintro r s' ⟨hl, hm⟩
  rw [gftW.arm1] at hm
  obtain ⟨⟨r0, m0⟩, c0, hm⟩ := of_K hm rfl; rw [gftW.k_iw_alloc.arm1] at hm
  cases c1 : gftW.loop1 p (n + 1) m0 cO cL (r0.headD 0) 0 with
  | none => rw [c1] at hm; cases hm
  | some mF =>
  rw [c1, gftW.k_loop1.arm1] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, hs0, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p ha n _ cL) c0
  simp only at hs0 hw0; subst hs0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hS
  obtain ⟨hSF, hgF, htF, hfF, hdF⟩ := gftW_ok p s₀.mem s0.mem cO cL (r0.headD 0) cvTas hcv hq0 (by omega) (n + 1)
    s0.mem mF 0 c1 hS0 hg0 rfl (MFr.refl _ _ _) UInt64.zero_le (by simp [decHL, hslice?])
  rw [← hmF]
  refine ⟨hl, hSF, hgF, (allocW_mfr hw0).trans hfF, by simpa using hdF, ?_⟩
  simp only [List.headD_cons, List.tail_cons]; omega

/-! ## `gen_rec_check_former_tys_c`: `ms2.mapM (classFormerTy fe cvTas)` -/

l_model gfc_spec (p : Prog) (hp : p.lookup "gen_rec_check_former_tys_c" = some genRecCheckFormerTysC)
  fns [hp ↦ gfcW list]
  specs [callW_spec p n "iw_alloc", callW_spec p n "class_former_ty"]
  grind [arena_grind] extra [ld64_rd_spec]

/- ronsync2 stage 2: commented out (a section at a removed L function)
section rel
variable {p : Prog} (P : CftProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
include P

omit P in
/-- **The loop refines `ms.mapM (classFormerTy fe cvTas)`** from cursor `j`. -/
theorem gfcW_ok (s0 : Mem) (co cl mo ml q : Word) (cvTas : List IConstantVal) (ms : List TargetMajor)
    (hcv : PSlR decCVp cvTas co cl s0) (hms : PSlR decTM ms mo ml s0) (hq : q.toNat = iwTop s0)
    (J : Mem → AState → Prop)
    (hJiw : ∀ m m' a, J m a → MemFrame [IW] [200] m m' → StageR vis fe m' a → J m' a)
    (hcft : ∀ (k : Nat) (m m1 : Mem) (a : AState) (mp : Word) (M : TargetMajor) (r : List Word), J m a →
      StageR vis fe m a → M ∈ ms → DecB (fun m => decTM m mp.toNat) m M →
      decPL m (decCVp m) co.toNat cl.toNat = some cvTas → co.toNat + cl.toNat < 2 ^ 64 →
      callW p k "class_former_ty" [vis, co, cl, mp] m = some (r, m1) →
      ∃ x a1, (ConRon.Arena.classFormerTy fe cvTas M).run a = .ok (x, a1) ∧ StageR vis fe m1 a1 ∧
        IWGrow m m1 ∧ decW0E m1 r x ∧ J m1 a1)
    (k : Nat) : ∀ (m m' : Mem) (a : AState) (j : Word) (acc : List EIdx),
    gfcW.loop1 p k m vis co cl mo ml q j = some m' →
    StageR vis fe m a → J m a → IWGrow s0 m → q.toNat + ml.toNat ≤ iwTop m → j ≤ ml →
    decHL m q.toNat j.toNat = some acc →
    ∃ rest a', ((ms.drop j.toNat).mapM (ConRon.Arena.classFormerTy fe cvTas)).run a = .ok (rest, a') ∧
      StageR vis fe m' a' ∧ IWGrow s0 m' ∧ q.toNat + ml.toNat ≤ iwTop m' ∧
      decHL m' q.toNat ml.toNat = some (acc ++ rest) ∧ J m' a' := by
  induction k with
  | zero => intro m m' a j acc h; simp [gfcW.loop1] at h
  | succ k ih =>
  intro m m' a j acc h hS hJ hg ht hjl hacc
  have hlen : ms.length = ml.toNat := decPL_length _ hms.dec
  have hjl' : j.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : ¬ j < ml
  · rw [gfcW.loop1.arm2 (hc1 := hj)] at h
    cases h
    have hj' : j.toNat = ml.toNat := by
      have : ¬ j.toNat < ml.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    refine ⟨[], a, ?_, hS, hg, ht, by rw [← hj']; simpa using hacc, hJ⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  simp only [Decidable.not_not] at hj
  rw [gfcW.loop1.arm1 (hc1 := hj)] at h
  have hjn : j.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hj
  obtain ⟨hI1, hE1, hsz, hEs, -⟩ := hS.iw
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hI1 hsz
  have hgt : iwTop s0 ≤ iwTop m := hg.iw
  -- class `j`
  have hmsm := hms.grow (fun q => decTM_mono q) hg
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hmsm.1 j.toNat hjn
  obtain ⟨-, hvm⟩ := rec2IwN_trunc hv
  have hrv : (rdW (m.arr64 IW) (mo + j)).toNat = v := rd_iwN hvm (by have := hmsm.2; omega)
  have hM : DecB (fun m' => decTM m' (rdW (m.arr64 IW) (mo + j)).toNat) m (ms[j.toNat]'(by omega)) := by
    show decTM (truncM m) _ = _; rw [hrv]; exact hdv
  have hcvm := hcv.grow (fun q => OMono.decCVp q) hg
  have hdcv : decPL m (decCVp m) co.toNat cl.toNat = some cvTas :=
    hcvm.1.get (OMono.decPL (fun q => OMono.decCVp q) _ _)
  rcases c1 : callW p k "class_former_ty" [vis, co, cl, rdW (m.arr64 IW) (mo + j)] m with _ | ⟨r1, m1⟩
  · rw [c1] at h; simp [gfcW.k_class_former_ty] at h
  rw [c1, gfcW.k_class_former_ty.arm1] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, ⟨hr1, he1⟩, hJ1⟩ := hcft k m m1 a _ _ r1 hJ hS (List.getElem_mem _) hM hdcv
    (by have := hcvm.2; omega) c1
  obtain ⟨hS1', hI1', hsz1, -, -⟩ := hS1.iw
  have hacc1 : decHL m1 q.toNat j.toNat = some acc := by
    rw [decHL_grow hg1 (by omega)]; exact hacc
  have hqj : q.toNat + j.toNat < (m1.arr64 IW).size := by have := hg1.iw; omega
  have hdec := decHL_write m1 q j (r1.headD 0) acc hr1 hsz1 hqj hacc1
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hqj' : (q + j).toNat = q.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨rest, a', hrun, hS', hg', ht', hdec', hJ'⟩ := ih _ m' a1 (j + 1) (acc ++ [x]) h (hS1.set_iw _ _)
    (hJiw _ _ _ hJ1 ((MemFrame.set64 _ IW (by decide) _ _).mono (by simp) (by simp)) (hS1.set_iw _ _))
    ((hg.trans hg1).set_iw _ _ (by rw [hqj']; omega)) (by rw [cnsTop_set]; have := hg1.iw; omega)
    (UInt64.le_iff_toNat_le.mpr (by rw [hj1]; omega)) (by rw [hj1, hdec, he1])
  refine ⟨x :: rest, a', ?_, hS', hg', ht', by simpa using hdec', hJ'⟩
  rw [List.drop_eq_getElem_cons (by omega), List.mapM_cons]
  rw [hj1] at hrun
  simp only [StateT.run_bind, hrun1, except_ok_bind, hrun]
  rfl

end rel
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`gen_rec_check_former_tys_c` refines `ms.mapM (classFormerTy fe cvTas)`**: the classes' formers,
a fresh slice; each `class_former_ty` call by the contract `hcft`, an invariant `J` kept. -/
theorem genRecCheckFormerTysC_refinesJ {p : Prog} (P : CftProg p)
    (hp : p.lookup "gen_rec_check_former_tys_c" = some genRecCheckFormerTysC) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cO cL mO mL : Word)
    (cvTas : List IConstantVal) (ms : List TargetMajor) (hS : StageR vis fe s₀.mem a₀)
    (hcv : PSlR decCVp cvTas cO cL s₀.mem) (hms : PSlR decTM ms mO mL s₀.mem)
    (J : Mem → AState → Prop)
    (hJiw : ∀ m m' a, J m a → MemFrame [IW] [200] m m' → StageR vis fe m' a → J m' a)
    (hcft : ∀ (k : Nat) (m m1 : Mem) (a : AState) (mp : Word) (M : TargetMajor) (r : List Word), J m a →
      StageR vis fe m a → M ∈ ms → DecB (fun m => decTM m mp.toNat) m M →
      decPL m (decCVp m) cO.toNat cL.toNat = some cvTas → cO.toNat + cL.toNat < 2 ^ 64 →
      callW p k "class_former_ty" [vis, cO, cL, mp] m = some (r, m1) →
      ∃ x a1, (ConRon.Arena.classFormerTy fe cvTas M).run a = .ok (x, a1) ∧ StageR vis fe m1 a1 ∧
        IWGrow m m1 ∧ decW0E m1 r x ∧ J m1 a1)
    (hJ : J s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_former_tys_c" [vis, cO, cL, mO, mL]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ms.mapM (ConRon.Arena.classFormerTy fe cvTas)) a₀ ∧
      StageR vis fe s'.mem (AM.st (ms.mapM (ConRon.Arena.classFormerTy fe cvTas)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (ms.mapM (ConRon.Arena.classFormerTy fe cvTas)) a₀) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      J s'.mem (AM.st (ms.mapM (ConRon.Arena.classFormerTy fe cvTas)) a₀); ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (gfc_spec p hp (n + 1) s₀ vis cO cL mO mL) ?_
  rintro r s' ⟨hl, hm⟩
  rw [gfcW.arm1] at hm
  obtain ⟨⟨r0, m0⟩, c0, hm⟩ := of_K hm rfl; rw [gfcW.k_iw_alloc.arm1] at hm
  cases c1 : gfcW.loop1 p (n + 1) m0 vis cO cL mO mL (r0.headD 0) 0 with
  | none => rw [c1] at hm; cases hm
  | some mF =>
  rw [c1, gfcW.k_loop1.arm1] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, hs0, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p P.alloc n _ mL) c0
  simp only at hs0 hw0; subst hs0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hS
  obtain ⟨rest, a', run, hSF, hgF, htF, hdF, hJF⟩ := gfcW_ok dn vis fe s₀.mem cO cL mO mL (r0.headD 0) cvTas ms
    hcv hms hq0 J hJiw hcft (n + 1) s0.mem mF a₀ 0 [] c1 hS0 (hJiw _ _ _ hJ (allocW_iwFrame hw0) hS0) hg0 (by omega)
    UInt64.zero_le (by simp [decHL, hslice?])
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hdF
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  rw [← hmF]
  refine ⟨hl, hok, by rw [hst]; exact hSF, hgF, by simpa [hres] using hdF, ?_, by rw [hst]; exact hJF⟩
  simp only [List.headD_cons, List.tail_cons]; omega
-/

/-! ## `gen_rec_check_minor_ok`: the minor premises against the constructors -/

/-- `class_slot_is_minor` as a word: `1` at a minor premise, else `0`. -/
theorem classSlotIsMinor_val (p : Prog) (hp : p.lookup "class_slot_is_minor" = some classSlotIsMinor)
    (n : Nat) (s₀ : St) (q : Word) (cs : ClassSlot) (hq : decCS s₀.mem q.toNat = some cs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_slot_is_minor" [q]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = if cs.isMinor then 1 else 0; ⊤⦄ := by
  have key := iwN_rdW (decCS_tag hq) q.toNat_lt
  rw [UInt64.ofNat_toNat] at key
  rw [invoke_eq _ hp]
  simp only [callFn, classSlotIsMinor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    cases hm : cs.isMinor <;> simp only [hm] at key ⊢ <;>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [UInt64.ofNat_toNat]

l_model mk_spec (p : Prog) (hp : p.lookup "gen_rec_check_minor_ok" = some genRecCheckMinorOk)
  fns [hp ↦ mkW list]
  specs [callW_spec p n "class_slot_is_minor"]
  grind [arena_grind] extra [ld64_rd_spec]

/-- **The slot loop counts the minor premises.** -/
theorem mkW_loop1_ok {p : Prog} (hm : p.lookup "class_slot_is_minor" = some classSlotIsMinor) (so sl : Word)
    (slots : List ClassSlot) (k : Nat) : ∀ (m m' : Mem) (j c c' : Word),
    mkW.loop1 p k m so sl j c = some (c', m') →
    decPL m (decCS m) so.toNat sl.toNat = some slots → so.toNat + sl.toNat < 2 ^ 64 → j ≤ sl →
    c.toNat = ((slots.take j.toNat).filter ConRon.Arena.ClassSlot.isMinor).length →
    m' = m ∧ c'.toNat = (slots.filter ConRon.Arena.ClassSlot.isMinor).length := by
  induction k with
  | zero => intro m m' j c c' h; simp [mkW.loop1] at h
  | succ k ih =>
  intro m m' j c c' h hsl hb hjl hc
  have hlen : slots.length = sl.toNat := decPL_length _ hsl
  have hjl' : j.toNat ≤ sl.toNat := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : ¬ j < sl
  · rw [mkW.loop1.arm2 (hc1 := hj)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hj' : j.toNat = sl.toNat := by
      have : ¬ j.toNat < sl.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    refine ⟨rfl, ?_⟩
    rw [hc, hj', List.take_of_length_le (by omega)]
  simp only [Decidable.not_not] at hj
  rw [mkW.loop1.arm1 (hc1 := hj)] at h
  have hjn : j.toNat < sl.toNat := UInt64.lt_iff_toNat_lt.mp hj
  obtain ⟨v, hv, hcs⟩ := decPL_getH m hsl j.toNat hjn
  have hrv : (rdW (m.arr64 IW) (so + j)).toNat = v := rd_iwN hv (by omega)
  rcases c1 : callW p k "class_slot_is_minor" [rdW (m.arr64 IW) (so + j)] m with _ | ⟨r1, m1⟩
  · rw [c1] at h; simp [mkW.k_class_slot_is_minor] at h
  rw [c1, mkW.k_class_slot_is_minor.arm1] at h
  obtain ⟨s1, hs1, hst, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classSlotIsMinor_val p hm k _ _ _ (by rw [hrv]; exact hcs)) c1
  subst hs1; subst hst; simp only at h
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hcl : c.toNat ≤ j.toNat := by
    rw [hc]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_take]; exact Nat.min_le_left _ _)
  refine ih m m' (j + 1) _ c' h hsl hb (UInt64.le_iff_toNat_le.mpr (by omega)) ?_
  rw [hj1, List.take_add_one, List.getElem?_eq_getElem (by omega), List.filter_append]
  simp only [Option.toList_some, List.length_append]
  rw [← hc, hr1]
  cases hmn : (slots[j.toNat]'(by omega)).isMinor <;> simp [hmn, UInt64.toNat_add] <;> omega

/-- **The constructor loop sums the classes' constructors** (past `2^64`: the early `0`), and
the comparison is the count's. -/
theorem mkW_loop2_ok (p : Prog) (m : Mem) (co cl : Word) (ctors : List (List ClassCtor)) (c : Word)
    (hct : decPL m (decLH m (decPL m (decCC m))) co.toNat cl.toNat = some ctors)
    (hb : co.toNat + cl.toNat < 2 ^ 64) (hsz : (m.arr64 IW).size < 2 ^ 64) (f : Nat) :
    ∀ (j t : Word) (r : List Word) (m' : Mem), mkW.loop2 p f m co cl j c t = some (r, m') → j ≤ cl →
    t.toNat = ((ctors.take j.toNat).map List.length).sum →
    r = [if c.toNat = (ctors.map List.length).sum then 1 else 0] ∧ m' = m := by
  have hlen : ctors.length = cl.toNat := decPL_length _ hct
  induction f with
  | zero => intro j t r m' h; simp [mkW.loop2] at h
  | succ f ih =>
  intro j t r m' h hjl ht
  have hjl' : j.toNat ≤ cl.toNat := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : ¬ j < cl
  · rw [mkW.loop2.arm3 (hc1 := hj)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hj' : j.toNat = cl.toNat := by
      have : ¬ j.toNat < cl.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    rw [hj', List.take_of_length_le (by omega)] at ht
    refine ⟨?_, rfl⟩
    simp only [← ht]
    by_cases e : c = t
    · subst e; simp
    · have : c.toNat ≠ t.toNat := fun h' => e (UInt64.toNat_inj.mp h')
      simp [e, this]
  simp only [Decidable.not_not] at hj
  have hjn : j.toNat < cl.toNat := UInt64.lt_iff_toNat_lt.mp hj
  obtain ⟨v, hv, hcv⟩ := decPL_getH m hct j.toNat hjn
  have hrv : (rdW (m.arr64 IW) (co + j)).toNat = v := rd_iwN hv (by omega)
  -- the header `[off, len]` at `v`
  simp only [decLH, decAt, bind, Option.bind_eq_some_iff] at hcv
  obtain ⟨o, -, l, hl, hpl⟩ := hcv
  have hll : (ctors[j.toNat]'(by omega)).length = l := decPL_length _ hpl
  have hv1 : (rdW (m.arr64 IW) (co + j) + 1).toNat = v + 1 := by
    have := iwN_lt hl; rw [UInt64.toNat_add, hrv]; simp; omega
  have hrl : (rdW (m.arr64 IW) (rdW (m.arr64 IW) (co + j) + 1)).toNat = l := by
    have := iwN_rdW hl (by have := iwN_lt hl; omega)
    have e : UInt64.ofNat (v + 1) = rdW (m.arr64 IW) (co + j) + 1 := by
      apply UInt64.toNat_inj.mp; rw [hv1]; simp; have := iwN_lt hl; omega
    rw [← e, this.1]; simp; omega
  generalize hw : rdW (m.arr64 IW) (rdW (m.arr64 IW) (co + j) + 1) = w at h hrl
  have hsum : ((ctors.take (j.toNat + 1)).map List.length).sum = t.toNat + l := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.map_append, List.sum_append, ← ht]
    simp [hll]
  have hle : ((ctors.take (j.toNat + 1)).map List.length).sum ≤ (ctors.map List.length).sum := by
    have e := congrArg (fun xs => (xs.map List.length).sum) (List.take_append_drop (j.toNat + 1) ctors)
    simp only [List.map_append, List.sum_append] at e
    omega
  by_cases ho : t + w < t
  · rw [mkW.loop2.arm1 (hc1 := hj) (hc2 := by rw [hw]; exact ho)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hov : 2 ^ 64 ≤ t.toNat + w.toNat := by
      have h1 := UInt64.lt_iff_toNat_lt.mp ho
      rw [UInt64.toNat_add] at h1
      rcases Nat.lt_or_ge (t.toNat + w.toNat) (2 ^ 64) with hc' | hc'
      · rw [Nat.mod_eq_of_lt hc'] at h1; omega
      · exact hc'
    have : ¬ c.toNat = (ctors.map List.length).sum := by have := c.toNat_lt; omega
    exact ⟨by simp [this], rfl⟩
  rw [mkW.loop2.arm2 (hc1 := hj) (hc2 := by rw [hw]; exact ho), hw] at h
  have hnov : t.toNat + w.toNat < 2 ^ 64 := by
    rcases Nat.lt_or_ge (t.toNat + w.toNat) (2 ^ 64) with hc' | hc'
    · exact hc'
    · exfalso; apply ho; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
      have := t.toNat_lt; have := w.toNat_lt; omega
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ih (j + 1) _ r m' h (UInt64.le_iff_toNat_le.mpr (by omega)) ?_
  rw [hj1, hsum, UInt64.toNat_add, Nat.mod_eq_of_lt hnov, hrl]

/-- **`gen_rec_check_minor_ok` compares the minor premises with the constructors.** -/
theorem genRecCheckMinorOk_refines {p : Prog} (hm : p.lookup "class_slot_is_minor" = some classSlotIsMinor)
    (hp : p.lookup "gen_rec_check_minor_ok" = some genRecCheckMinorOk) (n : Nat) (s₀ : St)
    (so sl co cl : Word) (slots : List ClassSlot) (ctors : List (List ClassCtor))
    (hsl : decPL s₀.mem (decCS s₀.mem) so.toNat sl.toNat = some slots) (hslb : so.toNat + sl.toNat < 2 ^ 64)
    (hct : decPL s₀.mem (decLH s₀.mem (decPL s₀.mem (decCC s₀.mem))) co.toNat cl.toNat = some ctors)
    (hctb : co.toNat + cl.toNat < 2 ^ 64) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_minor_ok" [so, sl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 != 0) = ((slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum); ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (mk_spec p hp (n + 1) s₀ so sl co cl) ?_
  rintro r s' ⟨hl, hmk⟩
  rw [mkW.arm1] at hmk
  obtain ⟨⟨c, m1⟩, c1, hmk⟩ := of_K hmk rfl; rw [mkW.k_loop1.arm1] at hmk
  obtain ⟨rfl, hc⟩ := mkW_loop1_ok hm so sl slots (n + 1) s₀.mem m1 0 0 c c1 hsl hslb UInt64.zero_le (by simp)
  obtain ⟨this, hmem⟩ := mkW_loop2_ok p s₀.mem co cl ctors c hct hctb hsz (n + 1) 0 0 _ _ hmk UInt64.zero_le (by simp)
  refine ⟨hl, hmem, ?_⟩
  rw [this, ← hc]
  by_cases e : c.toNat = (ctors.map List.length).sum <;> simp [e]

end L.Ind

end
