module

import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecGenSpec.CkcW
public import ConAgua.Arena.RecGenSpec.DecCIIndCv
public import ConAgua.Arena.IlpRd
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.IndPosSpec.EntryW
import ConAgua.Arena.IndPosSpec.EnvFindWHit
import ConAgua.Arena.RecSim
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndDecStab
import all ConAgua.Arena.RecGen
import ConAgua.Arena.FormerNZRef

@[expose] public section

/-!
# CftW

`cftW`, `cftW_mem`, `cftW_out`, `cftW_ext`, `classFormerTy_spec`, `FtRd`, `cftW_ok`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `class_former_ty`** (its `family_telescope` and `inst_lp_fast` read through `cR`). -/
def cftW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | N + 1, m, vis, o, l, mp =>
    if rdW (m.arr64 IW) (mp + 8) ≠ 0 then
      if rdW (m.arr64 IW) (mp + 8) - 1 < l then
        some ([erRd m (rdW (m.arr64 IW) (o + (rdW (m.arr64 IW) (mp + 8) - 1)) + 3)], m)
      else cftK1 (binternW m 0)
    else cftK2 cR N vis mp (findRes m vis (rdW (m.arr64 IW) mp)) m

section arms
variable (cR : CallM) (N : Nat) (m : Mem) (vis o l mp : Word)
theorem cftW_mem (h : rdW (m.arr64 IW) (mp + 8) ≠ 0) (h2 : rdW (m.arr64 IW) (mp + 8) - 1 < l) :
    cftW cR (N + 1) m vis o l mp =
      some ([erRd m (rdW (m.arr64 IW) (o + (rdW (m.arr64 IW) (mp + 8) - 1)) + 3)], m) := by
  simp only [cftW]; rw [ite_eq_left h, ite_eq_left h2]
theorem cftW_out (h : rdW (m.arr64 IW) (mp + 8) ≠ 0) (h2 : ¬ rdW (m.arr64 IW) (mp + 8) - 1 < l) :
    cftW cR (N + 1) m vis o l mp = cftK1 (binternW m 0) := by
  simp only [cftW]; rw [ite_eq_left h, ite_eq_right h2]
theorem cftW_ext (h : ¬ rdW (m.arr64 IW) (mp + 8) ≠ 0) :
    cftW cR (N + 1) m vis o l mp = cftK2 cR N vis mp (findRes m vis (rdW (m.arr64 IW) mp)) m := by
  simp only [cftW]; rw [ite_eq_right h]
end arms

grind_pattern [ind_grind] cftW_mem => cftW cR (N + 1) m vis o l mp
grind_pattern [ind_grind] cftW_out => cftW cR (N + 1) m vis o l mp
grind_pattern [ind_grind] cftW_ext => cftW cR (N + 1) m vis o l mp

theorem classFormerTy_spec (p : Prog) (h : CftProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat) (s₀ : St)
    (vis o l mp : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_former_ty" [vis, o, l, mp]
    ⦃fun r s' => LocEq s' s₀ ∧ cftW cR N s₀.mem vis o l mp = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.cft]
  simp only [callFn, classFormerTyL]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internBVar_spec p h.bf h.bp h.ib N, envFind_spec p h.rowGet h.baseGet h.find N,
        erToIw_specW p h.alloc h.copy h.eti N, hcR N "family_telescope", hcR N "inst_lp_fast"] <;>
      finish (gen := 20) [rdW_eq, L.St.setLocs_mem, cftK2]

/-! ## The relation to the twin -/

/-- **The contract of a reading of `family_telescope`** at an inductive's record `q` (decoding to
`.indInfo cv caps`), at call points satisfying `Pre`, which it keeps. -/
def FtRd (cR : CallM) (mode : ConLeche.CheckMode) (vis : Word) (fe : IFEnv) (Pre : Mem → AState → Prop) : Prop :=
  ∀ (k : Nat) (q : Word) (cv : IConstantVal) (caps : IIndCaps) (m m' : Mem) (a : AState) (r : List Word),
    Pre m a → StageR vis fe m a → decCI (erecP m) q.toNat = some (.indInfo cv caps) →
    cR k "family_telescope" [vis, q + 1, q + 5] m = some (r, m') →
    ∃ x a', (familyTelescope mode fe cv caps).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      decW0E m' r x ∧ AFr m m' ∧ Pre m' a'

/-- The levels' slice of a decoded constant value (any reader). -/
theorem decCV_sliceR {a : Nat → Option Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w1 w2, a (q + 1) = some w1 ∧ a (q + 2) = some w2 ∧
      hslice? a w1.toNat w2.toNat = some cv.levelParams := by
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, -, lv, hlv, ty, -, rfl⟩ := h
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho2, l', hl2, hsl⟩ := hlv
  simp only [nat?, Option.map_eq_some_iff] at ho2 hl2
  obtain ⟨w1, hw1, rfl⟩ := ho2
  obtain ⟨w2, hw2, rfl⟩ := hl2
  exact ⟨w1, w2, hw1, hw2, hsl⟩

theorem cftW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {N : Nat} {m m' : Mem} {o l mp : Word} {r : List Word} {M : TargetMajor} {cvTas : List IConstantVal}
    (mode : ConLeche.CheckMode) (cR : CallM) {Pre : Mem → AState → Prop} (hI : IlpRd cR dn vis fe Pre)
    (hF : FtRd cR mode vis fe Pre)
    (hPre : ∀ m m' a, Pre m a → StageR vis fe m' a → MemFrame [IW] [200] m m' → Pre m' a) (hP : Pre m a)
    (h : cftW cR N m vis o l mp = some (r, m')) (hS : StageR vis fe m a)
    (hM : DecB (fun m => decTM m mp.toNat) m M) (hcv : decPL m (decCVp m) o.toNat l.toNat = some cvTas)
    (hol : o.toNat + l.toNat < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.classFormerTy mode fe cvTas M).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0E m' r x ∧ AFr m m' := by
  cases N with
  | zero => simp [cftW] at h
  | succ N =>
  have hsz := hS.iw.iwSize
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨k, hk, hmem⟩ := decTM_member hM0
  have hrk := iwN_rdW_at (w := mp) (k := 8) hk hsz
  rw [show UInt64.ofNat 8 = (8 : Word) from rfl] at hrk
  have hlen := decPL_length m hcv
  by_cases hk0 : rdW (m.arr64 IW) (mp + 8) ≠ 0
  · have hk0' : k ≠ 0 := by intro e; apply hk0; rw [hrk.1, e]; rfl
    have hmem' : M.member = some (k - 1) := by rw [hmem]; simp [decON, hk0']
    have hkw : rdW (m.arr64 IW) (mp + 8) - 1 = UInt64.ofNat (k - 1) := by
      rw [hrk.1]; apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hrk.2]; simp; omega),
        UInt64.toNat_ofNat_of_lt' hrk.2, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)]
      simp
    by_cases hlt : rdW (m.arr64 IW) (mp + 8) - 1 < l
    · rw [cftW_mem (h := hk0) (h2 := hlt)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hkw] at hlt ⊢
      have hlt' : k - 1 < l.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hlt
        rwa [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)] at this
      obtain ⟨v, hv, hcvv⟩ := decPL_getH m hcv (k - 1) hlt'
      have hrv := iwN_rdW_at (w := o) (k := k - 1) hv hsz
      rw [hrv.1]
      have hv64 := hrv.2
      have hty := decCVp_type (q := UInt64.ofNat v) (by rw [UInt64.toNat_ofNat_of_lt' hv64]; exact hcvv)
        (by
          rw [UInt64.toNat_ofNat_of_lt' hv64]
          simp only [decCVp, decCV, bind, Option.bind_eq_some_iff] at hcvv
          obtain ⟨_, _, _, _, _, hty, -⟩ := hcvv
          obtain ⟨w, hw, -⟩ := hd?_some hty
          have := erecP_lt64 hw; omega)
      refine ⟨_, a, ?_, hS, IWGrow.refl m, ⟨hty.1, hty.2⟩, AFr.refl _⟩
      simp only [ConRon.Arena.classFormerTy, hmem', List.getElem?_eq_getElem (by omega : k - 1 < cvTas.length)]
      rfl
    · rw [cftW_out (h := hk0) (h2 := hlt)] at h
      obtain ⟨⟨e, m1⟩, hb, h⟩ := of_K h rfl
      rw [cftK1_some] at h
      obtain ⟨hbig, h⟩ := of_ite_none h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨a1, hrun, hS1, hg1⟩ := internBVar_stage hS 0 hb
      have hge : ¬ k - 1 < cvTas.length := by
        rw [hkw] at hlt; intro h'; apply hlt
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; have := hrk.2; omega)]
        omega
      refine ⟨_, a1, ?_, hS1, hg1, ⟨?_, rfl⟩, binternW_afr hb⟩
      · simp only [ConRon.Arena.classFormerTy, hmem', List.getElem?_eq_none (by omega : cvTas.length ≤ k - 1)]
        exact hrun
      · show e.toNat < 2 ^ 32
        have : ¬ (4294967296 : Word).toNat ≤ e.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x); simpa using this
  · rw [cftW_ext (h := hk0)] at h
    have hk00 : k = 0 := by
      have := congrArg UInt64.toNat ((show rdW (m.arr64 IW) (mp + 8) = 0 by simpa using hk0).symm.trans hrk.1)
      rw [UInt64.toNat_ofNat_of_lt' hrk.2] at this; exact this.symm
    have hmem' : M.member = none := by rw [hmem, hk00]; rfl
    obtain ⟨wi, hwi, hwiH, hwiE⟩ := iwH_rdW_at (w := mp) (k := 0) (by simpa using decTM_ind hM0) hsz
    rw [show mp + UInt64.ofNat 0 = mp by simp] at hwi
    rw [hwi] at h
    have hE := hS.check.env
    unfold cftK2 at h
    obtain ⟨hf0, h⟩ := of_ite_none h
    obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hwiH hf0
    have hfci : fe.find? M.ind = some ci := by rw [← hwiE, hfind, hci]
    generalize findRes m vis wi = r2 at h hf0 hci
    obtain ⟨hk3, h⟩ := of_ite_none h
    obtain ⟨kk, hkk, hcase⟩ := decCI_ind_cases hci
    have hkr := erec_nat (m := m) (w := r2.tail.headD 0) (c := 0) (by simpa using hkk) (by decide)
    rw [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at hkr
    have hkind : kk = 3 := by
      have := congrArg UInt64.toNat ((show erRd m (r2.tail.headD 0) = 3 by simpa using hk3).symm.trans hkr.1)
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; exact hkr.2)] at this; exact this.symm
    obtain ⟨-, cv, caps, rfl, -⟩ := hcase.resolve_right (fun ⟨hne, _⟩ => hne hkind)
    -- the telescope
    obtain ⟨⟨rt, m3⟩, h3, h⟩ := of_K h rfl
    rw [cftKF_some] at h
    obtain ⟨x3, a3, hrun3, hS3, hg3, ⟨hx32, hx3⟩, hA3, hP3⟩ := hF N _ cv caps m m3 a rt hP hS hci h3
    -- the levels
    have hcvP := (decCI_indInfo_iff.mp hci).2.1
    have hcv3 : decCV (erecP m3) ((r2.tail.headD 0).toNat + 1) = some cv := ArrExt.decCV (IWGrow.ext hg3) hcvP
    obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_sliceR hcv3
    have hq64 := erecP_lt64 hw2
    have e1 : erRd m3 (r2.tail.headD 0 + 2) = w1 :=
      L.Arena.erRd_of _ _ (by rw [show (r2.tail.headD 0 + 2).toNat = (r2.tail.headD 0).toNat + 1 + 1 by
        rw [UInt64.toNat_add, show (2 : Word).toNat = 2 from rfl]; omega]; exact hw1)
    have e2 : erRd m3 (r2.tail.headD 0 + 3) = w2 :=
      L.Arena.erRd_of _ _ (by rw [show (r2.tail.headD 0 + 3).toNat = (r2.tail.headD 0).toNat + 1 + 2 by
        rw [UInt64.toNat_add, show (3 : Word).toNat = 3 from rfl]; omega]; exact hw2)
    rw [e1, e2] at h
    obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl
    rw [cftK3_some] at h
    obtain ⟨hS4, hg4, hdec4, -, -⟩ := erToIwW_stage h4 hS3 (k := .name) (xs := cv.levelParams) hsl
    have hM4 : decTM m4 mp.toNat = some M := hM.stab (decTM_mono _) m4 (hg3.trans hg4)
    obtain ⟨wu, hwu, hwuH, hwuE⟩ := iwH_rdW_at (w := mp) (k := 1) (decTM_lvls' hM4) hS4.iw.iwSize
    rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at hwu
    rw [hwu] at h
    obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h rfl
    rw [cftK4_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨x, a5, hrun5, ⟨hS5, hg5, hx5⟩, -, hA5⟩ := hI N CWF (r4.headD 0) (r4.tail.headD 0) wu (rt.headD 0)
      cv.levelParams m4 m5 a3 r5 hwuH hx32 (hPre _ _ _ hP3 hS4 (erToIwW_iwFr h4)) hS4 hdec4 h5
    rw [CWF_eq, hwuE, hx3] at hrun5
    refine ⟨x, a5, ?_, hS5, (hg3.trans hg4).trans hg5, hx5, (hA3.trans (erToIwW_afr h4)).trans hA5⟩
    simp only [ConRon.Arena.classFormerTy, hmem', hfci, StateT.run_bind, hrun3]
    exact hrun5

end L.Ind

end
