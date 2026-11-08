module

public import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RecGenSpec.IwNLtSize
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.RecSim
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndDecStab
import all ConAgua.Arena.RecGen

@[expose] public section

/-!
# ClassMinorSlot: `ConRon.Arena.ClassSlot.isMinor`, `ConRon.Arena.classLeafAt`, `class_minor_slot`'s scan

The refinement theorems `classSlotIsMinor_refines`, `classLeafAt_refines`, `class_minor_slot`'s scan lemmas (`cmsGo_decB`) and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ClassSlot.isMinor` -/

/-- **`class_slot_is_minor` is `ClassSlot.isMinor`.** -/
@[refines ConRon.Arena.ClassSlot.isMinor]
theorem classSlotIsMinor_refines (p : Prog) (hp : p.lookup "class_slot_is_minor" = some classSlotIsMinor)
    (n : Nat) (s₀ : St) (q : Word) (cs : ClassSlot) (hq : decCS s₀.mem q.toNat = some cs)
    (hq1 : q.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_slot_is_minor" [q]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0 != 0) = cs.isMinor; ⊤⦄ := by
  have key := iwN_rdW (decCS_tag hq) hq1
  rw [invoke_eq _ hp]
  simp only [callFn, classSlotIsMinor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [UInt64.ofNat_toNat]

section arms
variable (n : Nat) (m : Mem) (off rem j c cc cnt rS rOff rLen : Word)

theorem classMinorSlotGoW_oob (hrem : rem ≠ 0) (hp : ¬ (off + j).toNat < (m.arr64 IW).size) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = none := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp]

theorem classMinorSlotGoW_oob2 (hrem : rem ≠ 0) (hp : (off + j).toNat < (m.arr64 IW).size)
    (hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = none) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = none := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp, hh]

end arms

grind_pattern [ind_grind] classMinorSlotGoW_oob => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_oob2 => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
theorem classMinorSlotGo_spec (p : Prog) (hp : p.lookup "class_minor_slot_go" = some classMinorSlotGo)
    (n : Nat) : ∀ (s₀ : St) (off rem j c cc cnt rS rOff rLen : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_minor_slot_go"
      [off, rem, j, c, cc, cnt, rS, rOff, rLen]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      ∃ x y z w, classMinorSlotGoW n s₀.mem off rem j c cc cnt rS rOff rLen = some (x, y, z, w) ∧
        r = [x, y, z, w]; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off rem j c cc cnt rS rOff rLen; rw [invoke_eq _ hp]; simp only [callFn, classMinorSlotGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off rem j c cc cnt rS rOff rLen
    rw [invoke_eq _ hp]
    simp only [callFn, classMinorSlotGo]
    -- the model's arm at `rem = 0` as a fact: the model's term occurs only under the `∃` of the
    -- post, where E-matching does not find it
    have hb := classMinorSlotGoW_base n s₀.mem off rem j c cc cnt rS rOff rLen
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

theorem hitsFrom_eq (c : Nat) (C : NIdx) : ∀ (j : Nat) (sls : List ClassSlot),
    (List.range sls.length).filterMap (fun s =>
      match (sls[s]? : Option ClassSlot) with
      | some (.minor c' C' ihs) => if c' == c && C' == C then some (j + s, ihs) else none
      | _ => none) = hitsFrom c C j sls := by
  intro j sls
  induction sls generalizing j with
  | nil => simp [hitsFrom]
  | cons sl sls ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons]
    rw [List.filterMap_map]
    have e : ((fun s => match (sls[s]? : Option ClassSlot) with
          | some (.minor c' C' ihs) => if c' == c && C' == C then some (j + 1 + s, ihs) else none
          | _ => none)) = (fun s => match ((sl :: sls)[s]? : Option ClassSlot) with
          | some (.minor c' C' ihs) => if c' == c && C' == C then some (j + s, ihs) else none
          | _ => none) ∘ Nat.succ := by
      funext s
      simp only [Function.comp, List.getElem?_cons_succ]
      have : j + (s + 1) = j + 1 + s := by omega
      simp only [this, Nat.succ_eq_add_one]
    erw [← e, ih (j + 1)]
    cases sl with
    | motive k => simp [hitsFrom]
    | minor c' C' ihs => by_cases hh : (c' == c && C' == C) = true <;> simp [hitsFrom, hh]

theorem leafAt_spec (p : Prog) (hp : p.lookup "class_leaf_at" = some classLeafAtL)
    (hv : p.lookup "e_view" = some eView) (had : AdF p) (n : Nat) (s₀ : St) (mm leaf : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_leaf_at" [mm, leaf]
    ⦃fun r s' => LocEq s' s₀ ∧ leafAtW s₀.mem mm leaf = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classLeafAtL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      gafF_spec p had n, eView_spec p hv n] <;>
    finish (gen := 20) [leafAtW, rdW_eq]

theorem leafAtW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (Mp leaf : Word) (bigM : TargetMajor) (r : List Word) (hS : StageR vis fe m a)
    (hl : H leaf) (hM : decTM m Mp.toNat = some bigM) (hMt : Mp.toNat < iwTop m)
    (h : leafAtW m Mp leaf = some (r, m')) :
    ∃ b a', (ConRon.Arena.classLeafAt bigM (decI leaf)).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b ∧ (r.headD 0).toNat ≤ 1 := by
  simp only [leafAtW] at h
  rcases hs : gafF m [CWF, leaf] with _ | ⟨r1, m1⟩ <;> simp only [hs, reduceCtorEq] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, hd1, hd2⟩ := gafF_ok dn vis fe CWF leaf hl m m1 a r1 hs hS
  rw [CWF_eq] at hrun1
  generalize hw : r1.headD 0 = w at hd1 hd2 h
  have e1 : (decI leaf : EIdx) = decE leaf := rfl
  by_cases hf : tagW w ≠ 3
  · rw [ite_eq_left hf] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨false, a1, ?_, hS1, hg1, by simp, by simp⟩
    have hct := decE_tag_eq w hd1 3 (by decide)
    have : ¬ (decE w).tag = ETag.const := fun hc => hf (by simpa using hct.mp hc)
    have htag' : ((decE w).tag == ETag.const) = false := by simpa using this
    simp only [ConRon.Arena.classLeafAt, StateT.run_bind]
    rw [hrun1]
    simp only [bind, Except.bind]
    rw [← hd2, show (decI w : EIdx) = decE w from rfl]
    simp only [htag', Bool.false_eq_true, ite_false]
    rfl
  · have hf3 : tagW w = 3 := by simpa using hf
    rw [ite_eq_right hf] at h
    obtain ⟨hev, h⟩ := of_ite_none h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨v, hv, hR⟩ := eViewW_ok m1 a1 hS1.check.arena.base w hev
    have hhead := eViewW_head3 m1 w hev hf3
    have hdec : ∃ nn us : _, v = ENodeView.const nn us ∧ (eViewW m1 w).tail.headD 0 = (eViewW m1 w).getD 1 0 ∧
        ((eViewW m1 w).getD 1 0).toNat < 2 ^ 32 ∧ decI ((eViewW m1 w).getD 1 0) = nn := by
      cases v with
      | const nn us =>
        simp only [ViewR] at hR
        refine ⟨nn, us, rfl, ?_, hR.2.1, hR.2.2.1⟩
        cases hh : eViewW m1 w with
        | nil => exact absurd hh hev
        | cons a1' t => cases t <;> simp
      | lit l => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR) (by decide)
      | _ => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
    obtain ⟨nn, us, rfl, ht1, hnlt, hnd⟩ := hdec
    obtain ⟨wi, hwi1, hwi2, hwi3⟩ := iwH_rdW (decTM_ind hM) (by have := Mp.toNat_lt; omega)
    rw [UInt64.ofNat_toNat] at hwi1
    have hwi1' : rdW (m1.arr64 IW) Mp = wi := by
      have := hg1.iwGet Mp.toNat hMt
      simp only [rdW] at hwi1 ⊢
      rw [show (m1.arr64 IW)[Mp.toNat]? = (m.arr64 IW)[Mp.toNat]? from this]; exact hwi1
    rw [ht1, hwi1']
    generalize hnI : (eViewW m1 w).getD 1 0 = nI at hnlt hnd ⊢
    have hvc := EStore.viewConst_of_view_r _ _ _ _ hv
    have hct := decE_tag_eq w hd1 3 (by decide)
    have htag0 : (decE w).tag = ETag.const := hct.mpr hf3
    have htag : ((decE w).tag == ETag.const) = true := by simpa using htag0
    have hiff : (nI = wi) ↔ (decI nI : NIdx) = decI wi := ⟨fun hh => by rw [hh], fun hh => by
      simpa only [decI_word_self _ hnlt, decI_word_self wi hwi2] using congrArg (fun x : NIdx => x.word.toUInt64) hh⟩
    refine ⟨(nn == bigM.ind), a1, ?_, hS1, hg1, ?_, ?_⟩
    · have e2 : (ConRon.Arena.viewConst (decE w)).run a1 = .ok (a1.store.viewConst (decE w), a1) := rfl
      rw [hvc] at e2
      simp only [ConRon.Arena.classLeafAt, StateT.run_bind]
      rw [hrun1]
      simp only [bind, Except.bind]
      rw [← hd2, show (decI w : EIdx) = decE w from rfl]
      simp only [htag, ite_true]
      simp only [StateT.run] at e2 ⊢
      simp only [StateT.bind, e2]
      rfl
    · by_cases hq : nI = wi
      · simp [hq, show nn = bigM.ind by rw [← hnd, ← hwi3, hq]]
      · simp [hq, show ¬ nn = bigM.ind from fun hh => hq (hiff.mpr (by rw [hnd, hh, hwi3]))]
    · by_cases hq : nI = wi <;> simp [hq]

/-- **`class_leaf_at` refines `classLeafAt`** (through the `get_app_fn` stub and `e_view`). -/
@[refines ConRon.Arena.classLeafAt]
theorem classLeafAt_refines (p : Prog) (hp : p.lookup "class_leaf_at" = some classLeafAtL)
    (hv : p.lookup "e_view" = some eView) (had : AdF p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (Mp leaf : Word) (bigM : TargetMajor)
    (hS : StageR vis fe s₀.mem a₀) (hl : H leaf) (hM : decTM s₀.mem Mp.toNat = some bigM)
    (hMt : Mp.toNat < iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_leaf_at" [Mp, leaf]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classLeafAt bigM (decI leaf)) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.classLeafAt bigM (decI leaf)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      ((r.headD 0 != 0) = AM.res (ConRon.Arena.classLeafAt bigM (decI leaf)) a₀ ∧ (r.headD 0).toNat ≤ 1);
      ⊤⦄ := by
  refine triple_post (leafAt_spec p hp hv had n s₀ Mp leaf) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨b, a', hrun, hS', hg, h1, h2⟩ := leafAtW_ok dn vis fe _ _ a₀ Mp leaf bigM r hS hl hM hMt hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.classLeafAt bigM (decI leaf)) a₀ a' b hrun
  exact ⟨hl', hok, by rw [hst]; exact hS', hg, by rw [hres]; exact ⟨h1, h2⟩⟩

/-! ## `class_stream_recs`'s reading -/

/-- The recursor shapes' constant records, as `class_stream_recs` reads them: slice entry `j` is a
pointer to a shape whose first word points to the constant `cvs[j]`, all below the pools' tops. -/
def RecsOK (m : Mem) (ro rl : Nat) (cvs : List IConstantVal) : Prop :=
  ro + rl ≤ iwTop m ∧ cvs.length = rl ∧ ∀ j, j < rl → ∃ p0 q cv, iwN m (ro + j) = some p0 ∧
    p0 + 1 ≤ iwTop m ∧ iwN m p0 = some q ∧ decCVp m q = some cv ∧ CVExt m q ∧ cvs[j]? = some cv

theorem RecsOK_grow {m m' : Mem} (hg : IWGrow m m') {ro rl : Nat} {cvs : List IConstantVal}
    (h : RecsOK m ro rl cvs) : RecsOK m' ro rl cvs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.iw, h2, fun j hj => ?_⟩
  obtain ⟨p0, q, cv, hp0, hp1, hq, hcv, hext, hcvs⟩ := h3 j hj
  have hiw : ∀ i, i < iwTop m → iwN m' i = iwN m i := fun i hi => by
    simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet i hi]
  refine ⟨p0, q, cv, ?_, Nat.le_trans hp1 hg.iw, ?_, ?_, CVExt_grow hg hext, hcvs⟩
  · rw [hiw _ (by omega)]; exact hp0
  · rw [hiw _ (by omega)]; exact hq
  · rw [decCVp_grow_r hg hext]; exact hcv

theorem RecsOK_cons {m : Mem} {ro rl : Nat} {cv : IConstantVal} {cvs : List IConstantVal}
    (h : RecsOK m ro (rl + 1) (cv :: cvs)) :
    (∃ p0 q, iwN m ro = some p0 ∧ p0 + 1 ≤ iwTop m ∧ iwN m p0 = some q ∧ decCVp m q = some cv ∧
      CVExt m q) ∧ RecsOK m (ro + 1) rl cvs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, by omega, by simpa using h2, fun j hj => ?_⟩
  · obtain ⟨p0, q, cv', hp0, hp1, hq, hcv, hext, hcvs⟩ := h3 0 (by omega)
    simp only [Nat.add_zero, List.getElem?_cons_zero, Option.some.injEq] at hp0 hcvs
    subst hcvs
    exact ⟨p0, q, hp0, hp1, hq, hcv, hext⟩
  · obtain ⟨p0, q, cv', hp0, hp1, hq, hcv, hext, hcvs⟩ := h3 (j + 1) (by omega)
    simp only [List.getElem?_cons_succ] at hcvs
    refine ⟨p0, q, cv', ?_, hp1, hq, hcv, hext, hcvs⟩
    have : ro + 1 + j = ro + (j + 1) := by omega
    rw [this]; exact hp0

/-- What `class_stream_recs` returns: a slice of constant pointers decoding to the constants. -/
def CsRes (m' : Mem) (r : List Word) (cvs : List IConstantVal) : Prop :=
  ∃ ptrs, decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ptrs ∧
    decPL m' (decCVp m') (r.headD 0).toNat (r.tail.headD 0).toNat = some cvs ∧
    (∀ q ∈ ptrs, CVExt m' q) ∧ (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'

local notation "V" => ConLeche.CheckMode.verified

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `class_minor_slot`'s slice, decoded below the tops -/

/-- **The scan's result words**: the initial ones, or the words 3 and 4 of the record at the
result's slot index. -/
theorem cmsGo_words (n : Nat) : ∀ (m : Mem) (off rem j c cc cnt rS rOff rLen x y z w : Word),
    classMinorSlotGoW n m off rem j c cc cnt rS rOff rLen = some (x, y, z, w) →
    (y = rS ∧ z = rOff ∧ w = rLen) ∨
    (z = rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + y) + 3) ∧ w = rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + y) + 4)) := by
  induction n with
  | zero => intro m off rem j c cc cnt rS rOff rLen x y z w h; simp [classMinorSlotGoW] at h
  | succ n ih =>
  intro m off rem j c cc cnt rS rOff rLen x y z w h
  by_cases hrem : rem = 0
  · rw [classMinorSlotGoW_base n m off rem j c cc cnt rS rOff rLen hrem] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact .inl ⟨rfl, rfl, rfl⟩
  by_cases hp : (off + j).toNat < (m.arr64 IW).size
  rotate_left
  · rw [classMinorSlotGoW_oob n m off rem j c cc cnt rS rOff rLen hrem hp] at h; cases h
  rcases hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc with _ | b
  · rw [classMinorSlotGoW_oob2 n m off rem j c cc cnt rS rOff rLen hrem hp hh] at h; cases h
  cases b with
  | false =>
    rw [classMinorSlotGoW_miss n m off rem j c cc cnt rS rOff rLen hrem hp hh] at h
    rcases ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ h with ⟨rfl, rfl, rfl⟩ | h2
    · exact .inl ⟨rfl, rfl, rfl⟩
    · exact .inr h2
  | true =>
    rw [classMinorSlotGoW_hit n m off rem j c cc cnt rS rOff rLen hrem hp hh] at h
    rcases ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ h with ⟨rfl, rfl, rfl⟩ | h2
    · exact .inr ⟨rfl, rfl⟩
    · exact .inr h2

/-- A hit of the twin's scan is a minor slot of the list. -/
theorem hitsFrom_get (c : Nat) (C : NIdx) : ∀ (j : Nat) (sls : List ClassSlot) (s : Nat)
    (ihs : List (Nat × Nat)), (s, ihs) ∈ hitsFrom c C j sls →
    j ≤ s ∧ sls[s - j]? = some (.minor c C ihs)
  | _, [], _, _, h => by simp [hitsFrom] at h
  | j, .motive k :: sls, s, ihs, h => by
    simp only [hitsFrom] at h
    obtain ⟨h1, h2⟩ := hitsFrom_get c C (j + 1) sls s ihs h
    refine ⟨by omega, ?_⟩
    rw [show s - j = (s - (j + 1)) + 1 by omega]; simpa using h2
  | j, .minor c' C' ihs' :: sls, s, ihs, h => by
    simp only [hitsFrom] at h
    split at h
    · rename_i hc
      simp only [List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp
      · obtain ⟨h1, h2⟩ := hitsFrom_get c C (j + 1) sls s ihs h
        refine ⟨by omega, ?_⟩
        rw [show s - j = (s - (j + 1)) + 1 by omega]; simpa using h2
    · obtain ⟨h1, h2⟩ := hitsFrom_get c C (j + 1) sls s ihs h
      refine ⟨by omega, ?_⟩
      rw [show s - j = (s - (j + 1)) + 1 by omega]; simpa using h2

/-- **`class_minor_slot`'s scan with the class reading decoded below the tops**: the twin's unique
hit's slice is decoded below the tops too. -/
theorem cmsGo_decB (n : Nat) {m : Mem} {rd c cc x y z w : Word} {R : ClassRead} {s : Nat}
    {ihs : List (Nat × Nat)}
    (hg : classMinorSlotGoW n m (rdW (m.arr64 IW) rd) (rdW (m.arr64 IW) (rd + 1)) 0 c cc 0 0 0 0 =
      some (x, y, z, w))
    (hR : DecB (fun m => decCR m rd.toNat) m R) (hh : hitsFrom c.toNat (decI cc) 0 R.slots = [(s, ihs)])
    (e1 : y = UInt64.ofNat s) (e2 : decPL m (decNN m) z.toNat w.toNat = some ihs)
    (hsz : (m.arr64 IW).size + 5 < 2 ^ 64) :
    DecB (fun m => decPL m (decNN m) z.toNat w.toNat) m ihs := by
  have hR0 : decCR (truncM m) rd.toNat = some R := hR
  rcases cmsGo_words n _ _ _ _ _ _ _ _ _ _ _ _ _ _ hg with ⟨-, rfl, rfl⟩ | ⟨hz, hw⟩
  · have : ihs = [] := by simpa [decPL] using e2.symm
    subst this
    show decPL (truncM m) _ _ _ = _
    simp [decPL]
  -- the hit record, decoded below the tops
  simp only [decCR, bind, Option.bind_eq_some_iff, pure] at hR0
  obtain ⟨slots, hsl, rcs, -, hRe⟩ := hR0
  cases hRe
  obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hsl
  have hmem : (s, ihs) ∈ hitsFrom c.toNat (decI cc) 0 slots := by rw [hh]; simp
  obtain ⟨-, hget⟩ := hitsFrom_get c.toNat (decI cc) 0 slots s ihs hmem
  simp only [Nat.sub_zero] at hget
  have hsl' : s < slots.length := by
    rcases (List.getElem?_eq_some_iff.mp hget) with ⟨h1, -⟩; exact h1
  have hsl2 : s < l := by rw [← decPL_length _ hdec]; exact hsl'
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hdec s hsl2
  rw [List.getElem?_eq_getElem hsl'] at hget
  have hslot : slots[s] = .minor c.toNat (decI cc) ihs := Option.some.inj hget
  rw [hslot] at hdv
  obtain ⟨-, -, -, o', l', h3, h4, hd⟩ := decCS_minor hdv
  -- the words
  have hsz64 : (m.arr64 IW).size < 2 ^ 64 := by omega
  obtain ⟨-, ho'⟩ := rec2IwN_trunc ho
  obtain ⟨-, hl'⟩ := rec2IwN_trunc hl
  obtain ⟨-, hv'⟩ := rec2IwN_trunc hv
  obtain ⟨-, h3'⟩ := rec2IwN_trunc h3
  obtain ⟨-, h4'⟩ := rec2IwN_trunc h4
  have hrd : rdW (m.arr64 IW) rd = UInt64.ofNat o := by
    have := iwN_rdW_at (w := rd) (k := 0) (by simpa using ho') hsz64; simpa using this.1
  have hy : y = UInt64.ofNat s := e1
  have hos : (UInt64.ofNat o : Word) + UInt64.ofNat s = UInt64.ofNat (o + s) := by
    apply UInt64.toNat_inj.mp
    have := iwN_lt_size hv'; have := rd.toNat_lt; have := (iwN_rdW ho' (by omega)).2
    rw [UInt64.toNat_add]; simp <;> omega
  have hvw := iwN_rdW hv' (by have := iwN_lt_size hv'; omega)
  have hv3 : UInt64.ofNat v + 3 = UInt64.ofNat (v + 3) := by
    apply UInt64.toNat_inj.mp; have := iwN_lt_size h3'; rw [UInt64.toNat_add]; simp <;> omega
  have hv4 : UInt64.ofNat v + 4 = UInt64.ofNat (v + 4) := by
    apply UInt64.toNat_inj.mp; have := iwN_lt_size h4'; rw [UInt64.toNat_add]; simp <;> omega
  have hz' : z = UInt64.ofNat o' := by
    rw [hz, hrd, hy, hos, hvw.1, hv3, (iwN_rdW h3' (by have := iwN_lt_size h3'; omega)).1]
  have hw' : w = UInt64.ofNat l' := by
    rw [hw, hrd, hy, hos, hvw.1, hv4, (iwN_rdW h4' (by have := iwN_lt_size h4'; omega)).1]
  rw [hz', hw', UInt64.toNat_ofNat_of_lt' (iwN_rdW h3' (by have := iwN_lt_size h3'; omega)).2,
    UInt64.toNat_ofNat_of_lt' (iwN_rdW h4' (by have := iwN_lt_size h4'; omega)).2]
  exact hd

end L.Ind

end

end
