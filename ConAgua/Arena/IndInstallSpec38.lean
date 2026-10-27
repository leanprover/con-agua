import ConAgua.Arena.RecGenSpec.DecB
import ConAgua.Arena.RecGenSpec.DecCIIndCv
import ConAgua.Arena.RecGenSpec.DecCNWords
set_option linter.unusedSectionVars false

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

/-- The loop of `genRecCheckFormerTys` (RecGen.lean), named for its spec. -/
-- con-ron: none — `genRecCheckFormerTys`' own loop (`rfl`), a named block for the proof
def gftLoop : Stmt := lblk (cvTasOff, cvTasLen, q, j) {
  while j < cvTasLen { IW.u64[q + j] := EREC.u64[IW.u64[cvTasOff + j] + 3]; j += 1 }
}

/-- `genRecCheckFormerTys`, its loop spliced from `gftLoop`. -/
-- con-ron: none — `genRecCheckFormerTys` itself (`rfl`), its loop a named block for the proof
def genRecCheckFormerTys' : FunDecl := lfn (cvTasOff, cvTasLen) locals (q, j) {
  q := call iw_alloc(cvTasLen);
  j := 0;
  ⟪gftLoop⟫;
  return (q, cvTasLen)
}

theorem genRecCheckFormerTys_eq : genRecCheckFormerTys = genRecCheckFormerTys' := rfl

/-- **The model of the loop** at fuel `f`: word `j` of the result the type word of constant `j`. -/
def gftW : Nat → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _ => none
  | f + 1, m, o, l, q, j =>
    if j < l then
      gftW f (m.set64 IW (q + j) (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + j) + 3))) o l q (j + 1)
    else some m

section arms
variable (f : Nat) (m : Mem) (o l q j : Word)
theorem gftW_exit (h : ¬ j < l) : gftW (f + 1) m o l q j = some m := by simp only [gftW]; rw [ite_eq_right h]
theorem gftW_step (h : j < l) : gftW (f + 1) m o l q j =
    gftW f (m.set64 IW (q + j) (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + j) + 3))) o l q (j + 1) := by
  simp only [gftW]; rw [ite_eq_left h]
end arms

def gftK2 (q l : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m => some ([q, l], m)

def gftK1 (n : Nat) (o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => gftK2 (r.headD 0) l (gftW (n + 1) m o l (r.headD 0) 0)

/-- **The model of `gen_rec_check_former_tys`** (exec fuel `n + 1`). -/
def gftF (p : Prog) (n : Nat) (m : Mem) (o l : Word) : Option (List Word × Mem) :=
  gftK1 n o l (callW p n "iw_alloc" [l] m)

theorem gftK2_some (q l : Word) (m : Mem) : gftK2 q l (some m) = some ([q, l], m) := rfl
theorem gftK1_some (n : Nat) (o l : Word) (r : List Word) (m : Mem) :
    gftK1 n o l (some (r, m)) = gftK2 (r.headD 0) l (gftW (n + 1) m o l (r.headD 0) 0) := rfl
theorem gftF_eq (p : Prog) (n : Nat) (m : Mem) (o l : Word) :
    gftF p n m o l = gftK1 n o l (callW p n "iw_alloc" [l] m) := rfl

attribute [ind_grind] gftW_exit gftW_step gftK2_some gftK1_some

theorem gftLoop_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f gftLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      gftW f s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) = some s'.mem; ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := gftLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem gft_spec (p : Prog) (hp : p.lookup "gen_rec_check_former_tys" = some genRecCheckFormerTys) (n : Nat)
    (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "gen_rec_check_former_tys" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ gftF p n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, genRecCheckFormerTys_eq]
  simp only [callFn, genRecCheckFormerTys']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "iw_alloc",
      fun s => Triple.step_exec (gftLoop_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [gftF_eq]

section rel
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}

/-- **The loop writes the types.** -/
theorem gftW_ok (s0 m1 : Mem) (o l q : Word) (cvTas : List IConstantVal)
    (hcv : PSlR decCVp cvTas o l s0) (hq : q.toNat = iwTop s0) (hT : iwTop m1 = q.toNat + l.toNat)
    (f : Nat) : ∀ (m m' : Mem) (j : Word), gftW f m o l q j = some m' →
    StageR dn vis fe m a → IWGrow s0 m → iwTop m = iwTop m1 → MFr [] [] m1 m → j ≤ l →
    decHL m q.toNat j.toNat = some ((cvTas.map (·.type)).take j.toNat) →
    StageR dn vis fe m' a ∧ IWGrow s0 m' ∧ iwTop m' = iwTop m1 ∧ MFr [] [] m1 m' ∧
      decHL m' q.toNat l.toNat = some (cvTas.map (·.type)) := by
  induction f with
  | zero => intro m m' j h; simp [gftW] at h
  | succ f ih =>
  intro m m' j h hS hg ht hfr hjl hacc
  have hlen : cvTas.length = l.toNat := decPL_length _ hcv.1
  have hjl' : j.toNat ≤ l.toNat := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : ¬ j < l
  · rw [gftW_exit (h := hj)] at h
    cases h
    have hj' : j.toNat = l.toNat := by
      have : ¬ j.toNat < l.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    refine ⟨hS, hg, ht, hfr, ?_⟩
    rw [← hj', hacc, List.take_of_length_le (by simp; omega)]
  simp only [Decidable.not_not] at hj
  rw [gftW_step (h := hj)] at h
  have hjn : j.toNat < l.toNat := UInt64.lt_iff_toNat_lt.mp hj
  obtain ⟨hI1, hE1, hsz, hEs, -⟩ := hS.2
  have hT0 := hcv.2
  have hgt : iwTop s0 ≤ iwTop m := hg.1
  -- constant `j`
  have hdm : decPL m (decCVp m) o.toNat l.toNat = some cvTas :=
    (hcv.grow (fun q => OMono.decCVp q) hg).1.get (OMono.decPL (fun q => OMono.decCVp q) _ _)
  obtain ⟨v, hv, hcvj⟩ := decPL_getH m hdm j.toNat hjn
  have hrv : (rdW (m.arr64 IW) (o + j)).toNat = v := rd_iwN hv (by have := (rdW (s0.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hT0; omega)
  obtain ⟨w, hw, hw32, hty⟩ := decCV_typeW hcvj
  have hvs : v + 3 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hw).1
  have hv3 : (rdW (m.arr64 IW) (o + j) + 3).toNat = v + 3 := by
    rw [UInt64.toNat_add, hrv]; simp; omega
  have hrw : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + j) + 3) = w := rdW_of_get? hv3.symm hw
  rw [hrw] at h
  -- the write
  have hqj : q.toNat + j.toNat < (m.arr64 IW).size := by omega
  have hdec := decHL_write m q j w _ hw32 hsz hqj hacc
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hqj' : (q + j).toNat = q.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
  refine ih _ m' (j + 1) h (hS.set_iw _ _) (hg.set_iw _ _ (by rw [hqj']; omega))
    (by rw [cnsTop_set]; exact ht) (hfr.trans (MFr.set_iw _ _ _)) ?_ ?_
  · exact UInt64.le_iff_toNat_le.mpr (by rw [hj1]; omega)
  · rw [hj1, hdec, List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem (by omega)]
    simp [hty]

end rel

/-- **`gen_rec_check_former_tys` is `cvTas.map (·.type)`**, a fresh slice. -/
theorem genRecCheckFormerTys_refines {p : Prog} (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "gen_rec_check_former_tys" = some genRecCheckFormerTys) (n : Nat) (s₀ : St) (a : AState)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (cO cL : Word) (cvTas : List IConstantVal)
    (hS : StageR dn vis fe s₀.mem a) (hcv : PSlR decCVp cvTas cO cL s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_former_tys" [cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a ∧ IWGrow s₀.mem s'.mem ∧ MFr [] [] s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat = some (cvTas.map (·.type)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (gft_spec p hp n s₀ cO cL) ?_
  rintro r s' ⟨hl, hm⟩
  rw [gftF_eq] at hm
  obtain ⟨⟨r0, m0⟩, c0, hm⟩ := of_K hm rfl; rw [gftK1_some] at hm
  cases c1 : gftW (n + 1) m0 cO cL (r0.headD 0) 0 with
  | none => rw [c1] at hm; cases hm
  | some mF =>
  rw [c1, gftK2_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, hs0, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p ha n _ cL) c0
  simp only at hs0 hw0; subst hs0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hS
  obtain ⟨hSF, hgF, htF, hfF, hdF⟩ := gftW_ok s₀.mem s0.mem cO cL (r0.headD 0) cvTas hcv hq0 (by omega) (n + 1)
    s0.mem mF 0 c1 hS0 hg0 rfl (MFr.refl _ _ _) UInt64.zero_le (by simp [decHL, hslice?])
  rw [← hmF]
  refine ⟨hl, hSF, hgF, (allocW_mfr hw0).trans hfF, by simpa using hdF, ?_⟩
  simp only [List.headD_cons, List.tail_cons]; omega

/-! ## `gen_rec_check_former_tys_c`: `ms2.mapM (classFormerTy fe cvTas)` -/

/-- The loop of `genRecCheckFormerTysC` (RecGen.lean), named for its spec. -/
-- con-ron: none — `genRecCheckFormerTysC`' own loop (`rfl`), a named block for the proof
def gfcLoop : Stmt := lblk (vis, cvTasOff, cvTasLen, ms2Off, ms2Len, q, j, e) {
  while j < ms2Len {
    e := call class_former_ty(vis, cvTasOff, cvTasLen, IW.u64[ms2Off + j]);
    IW.u64[q + j] := e;
    j += 1
  }
}

/-- `genRecCheckFormerTysC`, its loop spliced from `gfcLoop`. -/
-- con-ron: none — `genRecCheckFormerTysC` itself (`rfl`), its loop a named block for the proof
def genRecCheckFormerTysC' : FunDecl := lfn (vis, cvTasOff, cvTasLen, ms2Off, ms2Len)
    locals (q, j, e) {
  q := call iw_alloc(ms2Len);
  j := 0;
  ⟪gfcLoop⟫;
  return (q, ms2Len)
}

theorem genRecCheckFormerTysC_eq : genRecCheckFormerTysC = genRecCheckFormerTysC' := rfl

section model
variable (p : Prog)

/-- After `class_former_ty`: the write, then the rest. -/
def gfcK (q j : Word) (rest : Mem → Option Mem) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => rest (m.set64 IW (q + j) (r.headD 0))

/-- **The model of the loop** at fuel `k`, from cursor `j`. -/
def gfcW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, co, cl, mo, ml, q, j =>
    if j < ml then
      gfcK q j (fun m' => gfcW k m' vis co cl mo ml q (j + 1))
        (callW p k "class_former_ty" [vis, co, cl, rdW (m.arr64 IW) (mo + j)] m)
    else some m

end model

section arms
variable (p : Prog) (k : Nat) (m : Mem) (vis co cl mo ml q j : Word) (r : List Word)
  (rest : Mem → Option Mem)
theorem gfcK_some : gfcK q j rest (some (r, m)) = rest (m.set64 IW (q + j) (r.headD 0)) := rfl
theorem gfcW_exit (h : ¬ j < ml) : gfcW p (k + 1) m vis co cl mo ml q j = some m := by
  simp only [gfcW]; rw [ite_eq_right h]
theorem gfcW_step (h : j < ml) : gfcW p (k + 1) m vis co cl mo ml q j =
    gfcK q j (fun m' => gfcW p k m' vis co cl mo ml q (j + 1))
      (callW p k "class_former_ty" [vis, co, cl, rdW (m.arr64 IW) (mo + j)] m) := by
  simp only [gfcW]; rw [ite_eq_left h]
end arms

def gfcF2 (q l : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m => some ([q, l], m)

def gfcF1 (p : Prog) (n : Nat) (vis co cl mo ml : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => gfcF2 (r.headD 0) ml (gfcW p (n + 1) m vis co cl mo ml (r.headD 0) 0)

/-- **The model of `gen_rec_check_former_tys_c`** (exec fuel `n + 1`). -/
def gfcF (p : Prog) (n : Nat) (m : Mem) (vis co cl mo ml : Word) : Option (List Word × Mem) :=
  gfcF1 p n vis co cl mo ml (callW p n "iw_alloc" [ml] m)

theorem gfcF2_some (q l : Word) (m : Mem) : gfcF2 q l (some m) = some ([q, l], m) := rfl
theorem gfcF1_some (p : Prog) (n : Nat) (vis co cl mo ml : Word) (r : List Word) (m : Mem) :
    gfcF1 p n vis co cl mo ml (some (r, m)) =
      gfcF2 (r.headD 0) ml (gfcW p (n + 1) m vis co cl mo ml (r.headD 0) 0) := rfl
theorem gfcF_eq (p : Prog) (n : Nat) (m : Mem) (vis co cl mo ml : Word) :
    gfcF p n m vis co cl mo ml = gfcF1 p n vis co cl mo ml (callW p n "iw_alloc" [ml] m) := rfl

attribute [ind_grind] gfcK_some gfcW_exit gfcW_step gfcF2_some gfcF1_some

theorem gfcLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k gfcLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧
      gfcW p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6) =
        some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := gfcLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
        callW_spec p k "class_former_ty"] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem gfc_spec (p : Prog) (hp : p.lookup "gen_rec_check_former_tys_c" = some genRecCheckFormerTysC)
    (n : Nat) (s₀ : St) (vis co cl mo ml : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "gen_rec_check_former_tys_c" [vis, co, cl, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ gfcF p n s₀.mem vis co cl mo ml = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, genRecCheckFormerTysC_eq]
  simp only [callFn, genRecCheckFormerTysC']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "iw_alloc",
      fun s => Triple.step_exec (gfcLoop_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [gfcF_eq, loc_init4]

section rel
variable {p : Prog} (P : CftProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
include P

/-- **The loop refines `ms.mapM (classFormerTy fe cvTas)`** from cursor `j`. -/
theorem gfcW_ok (s0 : Mem) (co cl mo ml q : Word) (cvTas : List IConstantVal) (ms : List TargetMajor)
    (hcv : PSlR decCVp cvTas co cl s0) (hms : PSlR decTM ms mo ml s0) (hq : q.toNat = iwTop s0)
    (J : Mem → AState → Prop)
    (hJiw : ∀ m m' a, J m a → MemFrame [IW] [200] m m' → StageR dn vis fe m' a → J m' a)
    (hcft : ∀ (k : Nat) (m m1 : Mem) (a : AState) (mp : Word) (M : TargetMajor) (r : List Word), J m a →
      StageR dn vis fe m a → M ∈ ms → DecB (fun m => decTM m mp.toNat) m M →
      decPL m (decCVp m) co.toNat cl.toNat = some cvTas → co.toNat + cl.toNat < 2 ^ 64 →
      callW p k "class_former_ty" [vis, co, cl, mp] m = some (r, m1) →
      ∃ x a1, (ConRon.Arena.classFormerTy fe cvTas M).run a = .ok (x, a1) ∧ StageR dn vis fe m1 a1 ∧
        IWGrow m m1 ∧ decW0E m1 r x ∧ J m1 a1)
    (k : Nat) : ∀ (m m' : Mem) (a : AState) (j : Word) (acc : List EIdx),
    gfcW p k m vis co cl mo ml q j = some m' →
    StageR dn vis fe m a → J m a → IWGrow s0 m → q.toNat + ml.toNat ≤ iwTop m → j ≤ ml →
    decHL m q.toNat j.toNat = some acc →
    ∃ rest a', ((ms.drop j.toNat).mapM (ConRon.Arena.classFormerTy fe cvTas)).run a = .ok (rest, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow s0 m' ∧ q.toNat + ml.toNat ≤ iwTop m' ∧
      decHL m' q.toNat ml.toNat = some (acc ++ rest) ∧ J m' a' := by
  induction k with
  | zero => intro m m' a j acc h; simp [gfcW] at h
  | succ k ih =>
  intro m m' a j acc h hS hJ hg ht hjl hacc
  have hlen : ms.length = ml.toNat := decPL_length _ hms.1
  have hjl' : j.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : ¬ j < ml
  · rw [gfcW_exit (h := hj)] at h
    cases h
    have hj' : j.toNat = ml.toNat := by
      have : ¬ j.toNat < ml.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    refine ⟨[], a, ?_, hS, hg, ht, by rw [← hj']; simpa using hacc, hJ⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  simp only [Decidable.not_not] at hj
  rw [gfcW_step (h := hj)] at h
  have hjn : j.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hj
  obtain ⟨hI1, hE1, hsz, hEs, -⟩ := hS.2
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hI1 hsz
  have hgt : iwTop s0 ≤ iwTop m := hg.1
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
  · rw [c1] at h; simp [gfcK] at h
  rw [c1, gfcK_some] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, ⟨hr1, he1⟩, hJ1⟩ := hcft k m m1 a _ _ r1 hJ hS (List.getElem_mem _) hM hdcv
    (by have := hcvm.2; omega) c1
  obtain ⟨hS1', hI1', hsz1, -, -⟩ := hS1.2
  have hacc1 : decHL m1 q.toNat j.toNat = some acc := by
    rw [decHL_grow hg1 (by omega)]; exact hacc
  have hqj : q.toNat + j.toNat < (m1.arr64 IW).size := by have := hg1.1; omega
  have hdec := decHL_write m1 q j (r1.headD 0) acc hr1 hsz1 hqj hacc1
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hqj' : (q + j).toNat = q.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨rest, a', hrun, hS', hg', ht', hdec', hJ'⟩ := ih _ m' a1 (j + 1) (acc ++ [x]) h (hS1.set_iw _ _)
    (hJiw _ _ _ hJ1 ((MemFrame.set64 _ IW (by decide) _ _).mono (by simp) (by simp)) (hS1.set_iw _ _))
    ((hg.trans hg1).set_iw _ _ (by rw [hqj']; omega)) (by rw [cnsTop_set]; have := hg1.1; omega)
    (UInt64.le_iff_toNat_le.mpr (by rw [hj1]; omega)) (by rw [hj1, hdec, he1])
  refine ⟨x :: rest, a', ?_, hS', hg', ht', by simpa using hdec', hJ'⟩
  rw [List.drop_eq_getElem_cons (by omega), List.mapM_cons]
  rw [hj1] at hrun
  simp only [StateT.run_bind, hrun1, except_ok_bind, hrun]
  rfl

end rel

/-- **`gen_rec_check_former_tys_c` refines `ms.mapM (classFormerTy fe cvTas)`**: the classes' formers,
a fresh slice; each `class_former_ty` call by the contract `hcft`, an invariant `J` kept. -/
theorem genRecCheckFormerTysC_refinesJ {p : Prog} (P : CftProg p)
    (hp : p.lookup "gen_rec_check_former_tys_c" = some genRecCheckFormerTysC) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cO cL mO mL : Word)
    (cvTas : List IConstantVal) (ms : List TargetMajor) (hS : StageR dn vis fe s₀.mem a₀)
    (hcv : PSlR decCVp cvTas cO cL s₀.mem) (hms : PSlR decTM ms mO mL s₀.mem)
    (J : Mem → AState → Prop)
    (hJiw : ∀ m m' a, J m a → MemFrame [IW] [200] m m' → StageR dn vis fe m' a → J m' a)
    (hcft : ∀ (k : Nat) (m m1 : Mem) (a : AState) (mp : Word) (M : TargetMajor) (r : List Word), J m a →
      StageR dn vis fe m a → M ∈ ms → DecB (fun m => decTM m mp.toNat) m M →
      decPL m (decCVp m) cO.toNat cL.toNat = some cvTas → cO.toNat + cL.toNat < 2 ^ 64 →
      callW p k "class_former_ty" [vis, cO, cL, mp] m = some (r, m1) →
      ∃ x a1, (ConRon.Arena.classFormerTy fe cvTas M).run a = .ok (x, a1) ∧ StageR dn vis fe m1 a1 ∧
        IWGrow m m1 ∧ decW0E m1 r x ∧ J m1 a1)
    (hJ : J s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_former_tys_c" [vis, cO, cL, mO, mL]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ms.mapM (ConRon.Arena.classFormerTy fe cvTas)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ms.mapM (ConRon.Arena.classFormerTy fe cvTas)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (ms.mapM (ConRon.Arena.classFormerTy fe cvTas)) a₀) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      J s'.mem (AM.st (ms.mapM (ConRon.Arena.classFormerTy fe cvTas)) a₀); ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (gfc_spec p hp n s₀ vis cO cL mO mL) ?_
  rintro r s' ⟨hl, hm⟩
  rw [gfcF_eq] at hm
  obtain ⟨⟨r0, m0⟩, c0, hm⟩ := of_K hm rfl; rw [gfcF1_some] at hm
  cases c1 : gfcW p (n + 1) m0 vis cO cL mO mL (r0.headD 0) 0 with
  | none => rw [c1] at hm; cases hm
  | some mF =>
  rw [c1, gfcF2_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, hs0, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p P.alloc n _ mL) c0
  simp only at hs0 hw0; subst hs0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hS
  obtain ⟨rest, a', run, hSF, hgF, htF, hdF, hJF⟩ := gfcW_ok P dn vis fe s₀.mem cO cL mO mL (r0.headD 0) cvTas ms
    hcv hms hq0 J hJiw hcft (n + 1) s0.mem mF a₀ 0 [] c1 hS0 (hJiw _ _ _ hJ (allocW_iwFrame hw0) hS0) hg0 (by omega)
    UInt64.zero_le (by simp [decHL, hslice?])
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hdF
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  rw [← hmF]
  refine ⟨hl, hok, by rw [hst]; exact hSF, hgF, by simpa [hres] using hdF, ?_, by rw [hst]; exact hJF⟩
  simp only [List.headD_cons, List.tail_cons]; omega

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

/-- The slot loop of `genRecCheckMinorOk` (RecGen.lean), named for its spec. -/
-- con-ron: none — `genRecCheckMinorOk`' own loop (`rfl`), a named block for the proof
def mkLoop1 : Stmt := lblk (slotsOff, slotsLen, ctorsOff, ctorsLen, j, s, minorCnt, ctorSum, hdr) {
  while j < slotsLen {
    s := call class_slot_is_minor(IW.u64[slotsOff + j]);
    minorCnt := minorCnt + s;
    j += 1
  }
}

/-- The constructor loop of `genRecCheckMinorOk` (RecGen.lean), named for its spec. -/
-- con-ron: none — `genRecCheckMinorOk`' own loop (`rfl`), a named block for the proof
def mkLoop2 : Stmt := lblk (slotsOff, slotsLen, ctorsOff, ctorsLen, j, s, minorCnt, ctorSum, hdr) {
  while j < ctorsLen {
    hdr := IW.u64[ctorsOff + j];
    if ctorSum + IW.u64[hdr + 1] < ctorSum { return 0 };
    ctorSum := ctorSum + IW.u64[hdr + 1];
    j += 1
  }
}

/-- `genRecCheckMinorOk`, its loops spliced. -/
-- con-ron: none — `genRecCheckMinorOk` itself (`rfl`), its loops named blocks for the proof
def genRecCheckMinorOk' : FunDecl := lfn (slotsOff, slotsLen, ctorsOff, ctorsLen)
    locals (j, s, minorCnt, ctorSum, hdr) {
  minorCnt := 0;
  j := 0;
  ⟪mkLoop1⟫;
  ctorSum := 0;
  j := 0;
  ⟪mkLoop2⟫;
  return u64(minorCnt == ctorSum)
}

theorem genRecCheckMinorOk_eq : genRecCheckMinorOk = genRecCheckMinorOk' := rfl

section model
variable (p : Prog)

/-- After `class_slot_is_minor`: the rest at its word. -/
def mk1K (rest : Word → Mem → Option (Word × Mem)) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) => rest (r.headD 0) m

/-- **The model of the slot loop** at fuel `k`: the count at the exit, and the memory. -/
def mk1W : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, so, sl, j, c =>
    if j < sl then
      mk1K (fun s m' => mk1W k m' so sl (j + 1) (c + s))
        (callW p k "class_slot_is_minor" [rdW (m.arr64 IW) (so + j)] m)
    else some (c, m)

end model

/-- **The model of the constructor loop** at fuel `f`: the loop's signal and the sum. -/
def mk2W : Nat → Mem → Word → Word → Word → Word → Option (Sig × Word)
  | 0, _, _, _, _, _ => none
  | f + 1, m, co, cl, j, t =>
    if j < cl then
      if t + rdW (m.arr64 IW) (rdW (m.arr64 IW) (co + j) + 1) < t then some (.ret [0], t)
      else mk2W f m co cl (j + 1) (t + rdW (m.arr64 IW) (rdW (m.arr64 IW) (co + j) + 1))
    else some (.normal, t)

section arms
variable (p : Prog) (k : Nat) (m : Mem) (so sl co cl j c t : Word) (r : List Word)
  (rest : Word → Mem → Option (Word × Mem))
theorem mk1K_some : mk1K rest (some (r, m)) = rest (r.headD 0) m := rfl
theorem mk1W_exit (h : ¬ j < sl) : mk1W p (k + 1) m so sl j c = some (c, m) := by
  simp only [mk1W]; rw [ite_eq_right h]
theorem mk1W_step (h : j < sl) : mk1W p (k + 1) m so sl j c =
    mk1K (fun s m' => mk1W p k m' so sl (j + 1) (c + s))
      (callW p k "class_slot_is_minor" [rdW (m.arr64 IW) (so + j)] m) := by
  simp only [mk1W]; rw [ite_eq_left h]
theorem mk2W_exit (h : ¬ j < cl) : mk2W (k + 1) m co cl j t = some (.normal, t) := by
  simp only [mk2W]; rw [ite_eq_right h]
theorem mk2W_ovf (h : j < cl) (ho : t + rdW (m.arr64 IW) (rdW (m.arr64 IW) (co + j) + 1) < t) :
    mk2W (k + 1) m co cl j t = some (.ret [0], t) := by
  simp only [mk2W]; rw [ite_eq_left h, ite_eq_left ho]
theorem mk2W_step (h : j < cl) (ho : ¬ t + rdW (m.arr64 IW) (rdW (m.arr64 IW) (co + j) + 1) < t) :
    mk2W (k + 1) m co cl j t = mk2W k m co cl (j + 1) (t + rdW (m.arr64 IW) (rdW (m.arr64 IW) (co + j) + 1)) := by
  simp only [mk2W]; rw [ite_eq_left h, ite_eq_right ho]
end arms

/-- After the constructor loop: its signal, else the comparison. -/
def mkF2 (c : Word) (m : Mem) : Option (Sig × Word) → Option (List Word × Mem)
  | none => none
  | some (sg, t) => some (sg.retOr [if c = t then 1 else 0], m)

/-- After the slot loop: the constructor loop. -/
def mkF1 (n : Nat) (co cl : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (c, m) => mkF2 c m (mk2W (n + 1) m co cl 0 0)

/-- **The model of `gen_rec_check_minor_ok`** (exec fuel `n + 1`). -/
def mkF (p : Prog) (n : Nat) (m : Mem) (so sl co cl : Word) : Option (List Word × Mem) :=
  mkF1 n co cl (mk1W p (n + 1) m so sl 0 0)

theorem mkF2_some (c : Word) (m : Mem) (sg : Sig) (t : Word) :
    mkF2 c m (some (sg, t)) = some (sg.retOr [if c = t then 1 else 0], m) := rfl
theorem mkF1_some (n : Nat) (co cl c : Word) (m : Mem) :
    mkF1 n co cl (some (c, m)) = mkF2 c m (mk2W (n + 1) m co cl 0 0) := rfl
theorem mkF_eq (p : Prog) (n : Nat) (m : Mem) (so sl co cl : Word) :
    mkF p n m so sl co cl = mkF1 n co cl (mk1W p (n + 1) m so sl 0 0) := rfl

attribute [ind_grind] mk1K_some mk1W_exit mk1W_step mk2W_exit mk2W_ovf mk2W_step mkF2_some mkF1_some

theorem mkLoop1_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k mkLoop1
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
      mk1W p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 4) (s₀.loc 6) = some (s'.loc 6, s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := mkLoop1) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        callW_spec p k "class_slot_is_minor"] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem mkLoop2_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f mkLoop2
    ⦃fun r s' => s'.mem = s₀.mem ∧ s'.loc 6 = s₀.loc 6 ∧ r ≠ .brk ∧
      mk2W f s₀.mem (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 7) = some (r, s'.loc 7); ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := mkLoop2) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem mk_spec (p : Prog) (hp : p.lookup "gen_rec_check_minor_ok" = some genRecCheckMinorOk)
    (n : Nat) (s₀ : St) (so sl co cl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "gen_rec_check_minor_ok" [so, sl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ mkF p n s₀.mem so sl co cl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, genRecCheckMinorOk_eq]
  simp only [callFn, genRecCheckMinorOk']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (mkLoop1_spec p (n + 1) s),
      fun s => Triple.step_exec (mkLoop2_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [mkF_eq]

/-- **The slot loop counts the minor premises.** -/
theorem mk1W_ok {p : Prog} (hm : p.lookup "class_slot_is_minor" = some classSlotIsMinor) (so sl : Word)
    (slots : List ClassSlot) (k : Nat) : ∀ (m m' : Mem) (j c c' : Word),
    mk1W p k m so sl j c = some (c', m') →
    decPL m (decCS m) so.toNat sl.toNat = some slots → so.toNat + sl.toNat < 2 ^ 64 → j ≤ sl →
    c.toNat = ((slots.take j.toNat).filter ConRon.Arena.ClassSlot.isMinor).length →
    m' = m ∧ c'.toNat = (slots.filter ConRon.Arena.ClassSlot.isMinor).length := by
  induction k with
  | zero => intro m m' j c c' h; simp [mk1W] at h
  | succ k ih =>
  intro m m' j c c' h hsl hb hjl hc
  have hlen : slots.length = sl.toNat := decPL_length _ hsl
  have hjl' : j.toNat ≤ sl.toNat := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : ¬ j < sl
  · rw [mk1W_exit (h := hj)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hj' : j.toNat = sl.toNat := by
      have : ¬ j.toNat < sl.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    refine ⟨rfl, ?_⟩
    rw [hc, hj', List.take_of_length_le (by omega)]
  simp only [Decidable.not_not] at hj
  rw [mk1W_step (h := hj)] at h
  have hjn : j.toNat < sl.toNat := UInt64.lt_iff_toNat_lt.mp hj
  obtain ⟨v, hv, hcs⟩ := decPL_getH m hsl j.toNat hjn
  have hrv : (rdW (m.arr64 IW) (so + j)).toNat = v := rd_iwN hv (by omega)
  rcases c1 : callW p k "class_slot_is_minor" [rdW (m.arr64 IW) (so + j)] m with _ | ⟨r1, m1⟩
  · rw [c1] at h; simp [mk1K] at h
  rw [c1, mk1K_some] at h
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
theorem mk2W_ok (m : Mem) (co cl : Word) (ctors : List (List ClassCtor)) (c : Word)
    (hct : decPL m (decLH m (decPL m (decCC m))) co.toNat cl.toNat = some ctors)
    (hb : co.toNat + cl.toNat < 2 ^ 64) (hsz : (m.arr64 IW).size < 2 ^ 64) (f : Nat) :
    ∀ (j t t' : Word) (sg : Sig), mk2W f m co cl j t = some (sg, t') → j ≤ cl →
    t.toNat = ((ctors.take j.toNat).map List.length).sum →
    sg.retOr [if c = t' then 1 else 0] = [if c.toNat = (ctors.map List.length).sum then 1 else 0] := by
  have hlen : ctors.length = cl.toNat := decPL_length _ hct
  induction f with
  | zero => intro j t t' sg h; simp [mk2W] at h
  | succ f ih =>
  intro j t t' sg h hjl ht
  have hjl' : j.toNat ≤ cl.toNat := UInt64.le_iff_toNat_le.mp hjl
  by_cases hj : ¬ j < cl
  · rw [mk2W_exit (h := hj)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hj' : j.toNat = cl.toNat := by
      have : ¬ j.toNat < cl.toNat := fun e => hj (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    rw [hj', List.take_of_length_le (by omega)] at ht
    simp only [Sig.retOr, ← ht]
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
  · rw [mk2W_ovf (h := hj) (ho := by rw [hw]; exact ho)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hov : 2 ^ 64 ≤ t.toNat + w.toNat := by
      have h1 := UInt64.lt_iff_toNat_lt.mp ho
      rw [UInt64.toNat_add] at h1
      rcases Nat.lt_or_ge (t.toNat + w.toNat) (2 ^ 64) with hc' | hc'
      · rw [Nat.mod_eq_of_lt hc'] at h1; omega
      · exact hc'
    have : ¬ c.toNat = (ctors.map List.length).sum := by have := c.toNat_lt; omega
    simp [Sig.retOr, this]
  rw [mk2W_step (h := hj) (ho := by rw [hw]; exact ho), hw] at h
  have hnov : t.toNat + w.toNat < 2 ^ 64 := by
    rcases Nat.lt_or_ge (t.toNat + w.toNat) (2 ^ 64) with hc' | hc'
    · exact hc'
    · exfalso; apply ho; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
      have := t.toNat_lt; have := w.toNat_lt; omega
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ih (j + 1) _ t' sg h (UInt64.le_iff_toNat_le.mpr (by omega)) ?_
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
  refine triple_post (mk_spec p hp n s₀ so sl co cl) ?_
  rintro r s' ⟨hl, hmk⟩
  rw [mkF_eq] at hmk
  obtain ⟨⟨c, m1⟩, c1, hmk⟩ := of_K hmk rfl; rw [mkF1_some] at hmk
  obtain ⟨rfl, hc⟩ := mk1W_ok hm so sl slots (n + 1) s₀.mem m1 0 0 c c1 hsl hslb UInt64.zero_le (by simp)
  obtain ⟨⟨sg, t⟩, c2, hmk⟩ := of_K hmk rfl; rw [mkF2_some] at hmk
  obtain ⟨rfl, hmem⟩ := Prod.mk.inj (Option.some.inj hmk)
  have := mk2W_ok s₀.mem co cl ctors c hct hctb hsz (n + 1) 0 0 t sg c2 UInt64.zero_le (by simp)
  refine ⟨hl, hmem.symm, ?_⟩
  rw [this, ← hc]
  by_cases e : c.toNat = (ctors.map List.length).sum <;> simp [e]

end L.Ind
