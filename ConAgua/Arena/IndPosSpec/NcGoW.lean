module

public import ConAgua.Arena.IndPosSpec.EntryW
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndPosSpec.EnvFindWHit
public import ConAgua.Arena.IndPosSpec.RootHoles
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPosSpec.DpGoW
import ConRon.Bridge.Grind
import all ConAgua.Arena.IndPos
import ConAgua.L.WordOff
import ConAgua.Arena.EtaRescueRef

@[expose] public section

/-!
# NcGoW

The models and specs of `nest_container_ctors_go`, `nest_container_ctors` and `nest_container`
(generated), and their refinement of `nestContainer`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

l_model ncGo_spec (p : Prog) (hl : NtLook p)
  fns [hl.hgo ↦ ncGoW list]
  specs [envFind_spec p hl.hg hl.hb hl.hf n, nestCtorEntry_spec p hl.hs hl.hv hl.he hl.hst hl.ad n,
    posRec2_specW p hl.ha hl.h2 n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

l_model nc_spec (p : Prog) (hl : NtLook p)
  fns [hl.hcc ↦ ncWf list]
  specs [iwAlloc_specW p hl.ha n, ncGo_spec p hl n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]


theorem CNOk.agree {m m' : Mem} {p : Nat} {x : IConstantVal × Nat} {P : Nat → Prop} (h : CNOk m p x P)
    (hR : RdS m m' P) (hE : ArrExt (erecP m) (erecP m')) : CNOk m' p x P := by
  obtain ⟨h0, h1, q, hq, hcv, hn⟩ := h
  exact ⟨h0, h1, q, by rw [iwN_agree hR h0]; exact hq, hE.decCV hcv, by rw [iwN_agree hR h1]; exact hn⟩

theorem CNOk.mono {m : Mem} {p : Nat} {x : IConstantVal × Nat} {P Q : Nat → Prop} (h : CNOk m p x P)
    (hq : ∀ i, P i → Q i) : CNOk m p x Q := ⟨hq _ h.1, hq _ h.2.1, h.2.2⟩

/-- The twin's per-name step of `nestContainer`'s `filterMapM`. -/
def ncF (fe : IFEnv) (C : NIdx) (n : NIdx) : AM (Option (IConstantVal × Nat × Nat)) :=
  match fe.find? n with
  | some ci => ConRon.Arena.nestCtorEntry C ci
  | none => pure none

def ncProj (c : IConstantVal × Nat × Nat) : IConstantVal × Nat := (c.1, c.2.2)

theorem GrowX.erecP {q n : Nat} {m m' : Mem} (h : GrowX q n m m') : ArrExt (erecP m) (erecP m') :=
  (⟨h.er, h.erGet, h.er1, h.er1Get⟩ : ErecGrow m m').ext

theorem nestCtorEntry_some {C : NIdx} {cv : IConstantVal} {nPc nF : Nat} {a a' : AState}
    {x : IConstantVal × Nat × Nat}
    (h : (ConRon.Arena.nestCtorEntry C (.ctorInfo cv nPc nF)).run a = .ok (some x, a')) :
    x = (cv, nPc, nF) := by
  simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind] at h
  cases h1 : (stripPis (nPc + nF) cv.type).run a with
  | error e => rw [h1] at h; contradiction
  | ok p =>
    obtain ⟨o, a1⟩ := p
    simp only [h1, except_ok_bind] at h
    cases o with
    | none => exact absurd h (by simp [StateT.run, StateT.pure, pure, Except.pure])
    | some q =>
      simp only [StateT.run_bind] at h
      cases h2 : (getAppFn coreWalkFuel q.2).run a1 with
      | error e => rw [h2] at h; contradiction
      | ok p2 =>
        obtain ⟨hd, a2⟩ := p2
        simp only [h2, except_ok_bind] at h
        split at h
        · simp only [StateT.run_bind] at h
          cases h3 : (viewConst hd).run a2 with
          | error e => rw [h3] at h; contradiction
          | ok p3 =>
            obtain ⟨o3, a3⟩ := p3
            simp only [h3, except_ok_bind] at h
            cases o3 with
            | none =>
              simp only [failDanglingE] at h
              exact absurd h (by
                simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift,
                  Except.bind, bind])
            | some nu =>
              obtain ⟨n0, u0⟩ := nu
              simp only at h
              split at h
              · simp only [StateT.run, StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
                  Option.some.injEq] at h
                exact h.1.symm
              · exact absurd h (by simp [StateT.run, StateT.pure, pure, Except.pure])
        · exact absurd h (by simp [StateT.run, StateT.pure, pure, Except.pure])

theorem CsAt.agree {m m' : Mem} {o : Nat} {xs : List (IConstantVal × Nat)} {P : Nat → Prop}
    (h : CsAt m o xs P) (hR : RdS m m' P) (hE : ArrExt (erecP m) (erecP m'))
    (hw : ∀ i < xs.length, (m'.arr64 IW)[o + i]? = (m.arr64 IW)[o + i]?) : CsAt m' o xs P :=
  fun i hi => let ⟨w, h1, h2⟩ := h i hi; ⟨w, by rw [hw i hi]; exact h1, h2.agree hR hE⟩

theorem CsAt.mono {m : Mem} {o : Nat} {xs : List (IConstantVal × Nat)} {P Q : Nat → Prop}
    (h : CsAt m o xs P) (hq : ∀ i, P i → Q i) : CsAt m o xs Q :=
  fun i hi => let ⟨w, h1, h2⟩ := h i hi; ⟨w, h1, h2.mono hq⟩

theorem CsAt.grow {m m' : Mem} {o : Nat} {xs : List (IConstantVal × Nat)}
    (h : CsAt m o xs (· < iwTop m)) (hb : o + xs.length ≤ iwTop m) (hg : IWGrow m m') :
    CsAt m' o xs (· < iwTop m') :=
  (h.agree (RdS.of_grow hg) (GrowX.of_grow (q := 0) (n := 0) hg).erecP
    (fun i hi => hg.iwGet _ (by omega))).mono fun _ hx => Nat.lt_of_lt_of_le hx hg.iw

/-- A decoded constant's name word is read. -/
theorem decCV_rd {a : Nat → Option Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a q = some w := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, -⟩ := h
  obtain ⟨w, hw, -⟩ := hd?_some hx
  exact ⟨w, hw⟩

/-- A slice after word `co` is the slice at the word `co + 1` (a read word is below `2 ^ 64`). -/
theorem hslice?_wshift {k : IdxKind} {a : Nat → Option Word} {co : Word} {n : Nat} {xs : List (Idx k)}
    (h : hslice? a (co.toNat + 1) n = some xs) (ha : ∀ i v, a i = some v → i < 2 ^ 64) :
    hslice? a (co + 1).toNat n = some xs := by
  cases n with
  | zero => simpa [hslice?] using h
  | succ n =>
    have h' := h
    rw [hslice?_succ] at h'
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
    obtain ⟨x, hx, -⟩ := h'
    obtain ⟨w, hw, -⟩ := hd?_some hx
    rw [L.toNat_add_of_lt _ _ (by have := ha _ _ hw; simpa using this)]
    simpa using h

/-- The recursive call of `nest_container_ctors_go` passes its two results on. -/
theorem ncGoW.j1_some {n : Nat} {vis C co cl cs ol fp : Word} {m m' : Mem} {r : List Word}
    (h : ncGoW.j1 n vis C co cl cs ol fp m = some (r, m')) :
    ∃ r', ncGoW n m vis C (co + 1) (cl - 1) cs ol fp = some (r', m') ∧ r.headD 0 = r'.headD 0 ∧
      r.tail.headD 0 = r'.tail.headD 0 := by
  rw [ncGoW.j1.arm1] at h
  rcases e : ncGoW n m vis C (co + 1) (cl - 1) cs ol fp with _ | ⟨r', m''⟩ <;> rw [e] at h
  · cases h
  rw [ncGoW.k_nest_container_ctors_go.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨r', rfl, rfl, rfl⟩

theorem ncGoW_ok (fe : IFEnv) (vis C cs : Word) (N : Nat)
    (hC : H C) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (co cl ol fp : Word) (ns : List NIdx)
      (acc : List (IConstantVal × Nat × Nat)) (r : List Word),
    ncGoW k m vis C co cl cs ol fp = some (r, m') → StageR vis fe m a →
    hslice? (erecP m) co.toNat cl.toNat = some ns → cs.toNat + N ≤ iwTop m →
    ol.toNat = acc.length → acc.length + cl.toNat ≤ N →
    CsAt m cs.toNat (acc.map ncProj) (OutR cs.toNat N (iwTop m)) →
    fp.toNat = (acc.head?.map (·.2.1)).getD 0 →
    ∃ ys a', (ns.filterMapM (ncF fe (decI C))).run a = .ok (ys, a') ∧ StageR vis fe m' a' ∧
      GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ys.length ∧
      CsAt m' cs.toNat ((acc ++ ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
      (r.tail.headD 0).toNat = ((acc ++ ys).head?.map (·.2.1)).getD 0 ∧ ys.length ≤ ns.length := by
  induction k with
  | zero => intro m m' a co cl ol fp ns acc r h; simp [ncGoW.eq_1] at h
  | succ k ih =>
    intro m m' a co cl ol fp ns acc r h hS hns hreg hol hN hacc hfp
    have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.iw.iwSize
    by_cases hc0 : cl = 0
    · rw [ncGoW.arm1 (hc1 := hc0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc0
      have : ns = [] := by simpa [hslice?] using hns.symm
      subst this
      refine ⟨[], a, rfl, hS, GrowX.of_grow (IWGrow.refl _), by simp [hol], by simpa using hacc,
        by simpa using hfp, by simp⟩
    have hcl : cl.toNat ≠ 0 := fun e => hc0 (UInt64.toNat_inj.mp (by simpa using e))
    have hcl1 : (cl - 1).toNat = cl.toNat - 1 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
    -- the name
    obtain ⟨cl', hcl'⟩ : ∃ c', cl.toNat = c' + 1 := ⟨cl.toNat - 1, by omega⟩
    rw [hcl', hslice?_succ] at hns
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hns
    obtain ⟨n, hn, ns', hns', rfl⟩ := hns
    obtain ⟨w, hw, hwH, rfl⟩ := hd?_some hn
    have hwE : erRd m co = w := (erRd_of_erecP hw).1
    have hns1 : ∀ {b : Nat → Option Word}, ArrExt (erecP m) b → hslice? b (co + 1).toNat (cl - 1).toNat = some ns' :=
      fun hb => by rw [hcl1, show cl.toNat - 1 = cl' by omega]; exact hb.hslice? (hslice?_wshift hns' fun _ _ e => erecP_lt64 e)
    have hE := hS.check.env
    rw [List.filterMapM_cons]
    by_cases hf0 : (findRes m vis w).headD 0 = 0
    · -- not found
      rw [ncGoW.arm3 (hc1 := hc0) (hc2 := by rw [erRd_foldN, hwE]; exact hf0)] at h
      obtain ⟨r', h, e1, e2⟩ := ncGoW.j1_some h
      have hfind := findRes_miss hE hwH hf0
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3, h4⟩ := ih m m' a (co + 1) (cl - 1) ol fp ns' acc r' h hS
        (hns1 fun _ _ e => e) hreg hol (by omega) hacc hfp
      refine ⟨ys, a', ?_, hS', hGX, e1 ▸ h1, h2, e2 ▸ h3, by simp; omega⟩
      simp only [ncF, hfind, StateT.run_bind]
      exact hrun
    rw [ncGoW.arm2 (hc1 := hc0) (hc2 := by rw [erRd_foldN, hwE]; exact hf0)] at h
    simp only [erRd_foldN, hwE] at h
    obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hwH hf0
    rw [hci] at hfind
    generalize (findRes m vis w).tail.headD 0 = ciq at h hfind hci
    rcases hent : entryW m C ciq with _ | ⟨r2, m2⟩ <;> rw [hent] at h; · rw [ncGoW.k_nest_ctor_entry.none] at h; cases h
    obtain ⟨x, a1, hrun1, hS2, hg2, hout⟩ := entryW_ok hC hent hS hci
    have hE2 : ArrExt (erecP m) (erecP m2) := (GrowX.of_grow (q := 0) (n := 0) hg2).erecP
    have hstep : ncF fe (decI C) (decI w) = ConRon.Arena.nestCtorEntry (decI C) ci := by
      simp only [ncF, hfind]
    rw [hstep]
    have hlen : (acc.map ncProj).length = acc.length := List.length_map ..
    cases x with
    | none =>
      have hr2 : r2 = [0, 0, 0, 0] := hout
      subst hr2
      rw [ncGoW.k_nest_ctor_entry.arm2 (hc1 := rfl)] at h
      obtain ⟨r', h, e1, e2⟩ := ncGoW.j1_some h
      have hacc2 : CsAt m2 cs.toNat (acc.map ncProj) (OutR cs.toNat N (iwTop m)) :=
        hacc.agree ((RdS.of_grow hg2).mono fun _ hi => hi.1) hE2
          (fun i hi => hg2.iwGet _ (by rw [hlen] at hi; omega))
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3, h4⟩ := ih m2 m' a1 (co + 1) (cl - 1) ol fp ns' acc r' h hS2
        (hns1 hE2)
        (by have := hg2.iw; omega) hol (by omega)
        (hacc2.mono fun _ hx => ⟨Nat.lt_of_lt_of_le hx.1 hg2.iw, hx.2⟩) hfp
      refine ⟨ys, a', ?_, hS', (GrowX.of_grow hg2).trans hGX, e1 ▸ h1, h2, e2 ▸ h3, by simp; omega⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind]
      exact hrun
    | some c =>
      obtain ⟨cv, nPc, nF⟩ := c
      obtain ⟨hr2, -, hs⟩ := hout
      subst hr2
      rw [ncGoW.k_nest_ctor_entry.arm1 (hc1 := by simp)] at h
      simp only [List.tail_cons, List.headD_cons] at h
      have hci' : ci = .ctorInfo cv nPc nF := by
        cases ci with
        | ctorInfo cv' nPc' nF' _ =>
          have := nestCtorEntry_some hrun1
          simp only [Prod.mk.injEq] at this
          obtain ⟨rfl, rfl, rfl⟩ := this; rfl
        | _ => exact absurd hrun1 (by simp [ConRon.Arena.nestCtorEntry, StateT.run, StateT.pure, pure, Except.pure])
      subst hci'
      have hcvE : decCV (erecP m) (ciq.toNat + 1) = some cv := L.Arena.decCI_ctor_cv hci
      have hciq1 : (ciq + 1).toNat = ciq.toNat + 1 :=
        L.toNat_add_of_lt _ _ (show ciq.toNat + 1 < 2 ^ 64 by
          obtain ⟨_, e⟩ := decCV_rd hcvE; have := erecP_lt64 e; simpa using this)
      have hU : UInt64.size = 2 ^ 64 := rfl
      have hnF : (UInt64.ofNat nF).toNat = nF := UInt64.toNat_ofNat_of_lt' (by omega)
      have hnPc : (UInt64.ofNat nPc).toNat = nPc := UInt64.toNat_ofNat_of_lt' (by omega)
      have htopb : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hsz
      rcases hrec : posRecW m2 [ciq + 1, UInt64.ofNat nF] with _ | ⟨q3, m3⟩ <;> rw [hrec] at h; · rw [ncGoW.k_rec2.none] at h; cases h
      obtain ⟨hS3, hg3, hq3, ht3, hget3⟩ := posRecW_stage hrec hS2 (by simp)
      simp only [List.length_cons, List.length_nil] at ht3
      have hcol : (cs + ol).toNat = cs.toNat + ol.toNat := L.toNat_add_of_lt _ _ (by omega)
      have hS4 := hS3.set_iw (cs + ol) q3
      have hg23 := hg2.trans hg3
      have hGX4 : GrowX cs.toNat N m (m3.set64 IW (cs + ol) q3) :=
        (GrowX.of_grow hg23).trans (GrowX.set m3 _ _ (by omega))
      have hE4 : ArrExt (erecP m) (erecP (m3.set64 IW (cs + ol) q3)) := hGX4.erecP
      have ht4 : iwTop (m3.set64 IW (cs + ol) q3) = iwTop m3 := by
        simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      have hsz3 : cs.toNat + ol.toNat < (m3.arr64 IW).size := by
        have := hS3.iw.iw; have := hg23.iw; omega
      have hnew : CNOk (m3.set64 IW (cs + ol) q3) q3.toNat (cv, nF)
          (OutR cs.toNat N (iwTop (m3.set64 IW (cs + ol) q3))) := by
        have hg2' := hg2.iw
        refine ⟨⟨by rw [ht4]; omega, Or.inr (by omega)⟩, ⟨by rw [ht4]; omega, Or.inr (by omega)⟩,
          (ciq + 1).toNat, ?_, by rw [hciq1]; exact hE4.decCV hcvE, ?_⟩
        · have := hget3 0 (by simp)
          simp only [iwN, nat?, iwA, aread_apply, set64IW_get]
          rw [ite_eq_right (by omega)]; simp at this; simp [this]
        · have := hget3 1 (by simp)
          simp only [iwN, nat?, iwA, aread_apply, set64IW_get]
          rw [ite_eq_right (by omega)]; simp at this; simp [this, hnF]
      have hacc4 : CsAt (m3.set64 IW (cs + ol) q3) cs.toNat
          ((acc ++ [(cv, nPc, nF)]).map ncProj) (OutR cs.toNat N (iwTop (m3.set64 IW (cs + ol) q3))) := by
        intro i hi
        simp only [List.map_append, List.length_append, List.length_map, List.map_cons, List.map_nil,
          List.length_cons, List.length_nil] at hi
        by_cases hia : i < acc.length
        · obtain ⟨w', hw1, hw2⟩ := hacc i (by rw [hlen]; exact hia)
          refine ⟨w', ?_, ?_⟩
          · rw [set64IW_get, ite_eq_right (by omega), hg23.iwGet _ (by omega)]; exact hw1
          · simp only [List.map_append, List.map_cons, List.map_nil]
            rw [List.getElem_append_left (by rw [hlen]; exact hia)]
            exact (hw2.agree hGX4.rd hE4).mono fun _ hx =>
              ⟨Nat.lt_of_lt_of_le hx.1 (by rw [ht4]; exact hg23.iw), hx.2⟩
        · have hie : i = acc.length := by omega
          subst hie
          refine ⟨q3, ?_, ?_⟩
          · rw [set64IW_get, ite_eq_left ⟨by omega, by omega⟩]
          · simp only [List.map_append, List.map_cons, List.map_nil]
            rw [List.getElem_append_right (by rw [hlen]; exact Nat.le_refl _)]
            simp only [hlen, Nat.sub_self, List.getElem_cons_zero, ncProj]
            exact hnew
      have hol1 : (ol + 1).toNat = acc.length + 1 := by
        rw [L.toNat_add_of_lt _ _ (show ol.toNat + (1 : Word).toNat < 2 ^ 64 by simp; omega)]; simp [hol]
      have hrest : ∀ fp' : Word, fp'.toNat = ((acc ++ [(cv, nPc, nF)]).head?.map (·.2.1)).getD 0 →
          ncGoW.j1 k vis C co cl cs (ol + 1) fp' (m3.set64 IW (cs + ol) q3) = some (r, m') →
          ∃ ys a', (List.filterMapM (ncF fe (decI C)) ns').run a1 = .ok (ys, a') ∧ StageR vis fe m' a' ∧
            GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ((cv, nPc, nF) :: ys).length ∧
            CsAt m' cs.toNat ((acc ++ (cv, nPc, nF) :: ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
            (r.tail.headD 0).toNat = ((acc ++ (cv, nPc, nF) :: ys).head?.map (·.2.1)).getD 0 ∧
            ys.length ≤ ns'.length := by
        intro fp' hfp' h'
        obtain ⟨r', h', e1, e2⟩ := ncGoW.j1_some h'
        obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3, h4⟩ := ih _ m' a1 (co + 1) (cl - 1) (ol + 1) fp' ns'
          (acc ++ [(cv, nPc, nF)]) r' h' hS4
          (hns1 hE4)
          (by rw [ht4]; have := hg23.iw; omega) (by rw [hol1]; simp) (by simp; omega) hacc4 hfp'
        refine ⟨ys, a', hrun, hS', hGX4.trans hGX, by rw [e1, h1]; simp; omega, ?_, ?_, h4⟩
        · simpa using h2
        · rw [e2]; simpa using h3
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3, h4⟩ : ∃ ys a', (List.filterMapM (ncF fe (decI C)) ns').run a1 =
          .ok (ys, a') ∧ StageR vis fe m' a' ∧
            GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ((cv, nPc, nF) :: ys).length ∧
            CsAt m' cs.toNat ((acc ++ (cv, nPc, nF) :: ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
            (r.tail.headD 0).toNat = ((acc ++ (cv, nPc, nF) :: ys).head?.map (·.2.1)).getD 0 ∧
            ys.length ≤ ns'.length := by
        by_cases h0 : ol = 0
        · rw [ncGoW.k_rec2.arm1 (hc1 := h0), ncGoW.j2.arm1] at h
          have : acc = [] := List.eq_nil_of_length_eq_zero (by rw [← hol, h0]; rfl)
          subst this
          exact hrest _ (by simp [hnPc]) h
        · rw [ncGoW.k_rec2.arm2 (hc1 := h0), ncGoW.j2.arm1] at h
          have hne : acc ≠ [] := fun e => h0 (UInt64.toNat_inj.mp (by rw [hol, e]; rfl))
          obtain ⟨c0, acc', rfl⟩ := List.exists_cons_of_ne_nil hne
          exact hrest _ (by simpa using hfp) h
      refine ⟨(cv, nPc, nF) :: ys, a', ?_, hS', hGX, h1, h2, h3, by simp; omega⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, hrun, StateT.run_pure]
      rfl

theorem ncW_ok (fe : IFEnv) (vis C : Word) (hC : H C)
    (k : Nat) (m m' : Mem) (a : AState) (co cl : Word) (ns : List NIdx) (r : List Word)
    (h : ncWf (k + 1) m vis C co cl = some (r, m')) (hS : StageR vis fe m a)
    (hns : hslice? (erecP m) co.toNat cl.toNat = some ns) :
    ∃ ys a', (ns.filterMapM (ncF fe (decI C))).run a = .ok (ys, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ (r.tail.headD 0).toNat = ys.length ∧ (r.headD 0).toNat + ys.length ≤ iwTop m' ∧
      CsAt m' (r.headD 0).toNat (ys.map ncProj) (· < iwTop m') ∧
      (r.tail.tail.headD 0).toNat = (ys.head?.map (·.2.1)).getD 0 := by
  rw [ncWf.arm1] at h
  rcases hal : allocW m cl with _ | ⟨cs, m1⟩ <;> rw [hal] at h; · rw [ncWf.k_iw_alloc.none] at h; cases h
  rw [ncWf.k_iw_alloc.arm1] at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  have hqt : cs.toNat = iwTop m := by simp only [iwTop, hqd]
  rcases hgo : ncGoW k m1 vis C co cl cs 0 0 with _ | ⟨r1, m2⟩ <;> rw [hgo] at h; · rw [ncWf.k_nest_container_ctors_go.none] at h; cases h
  rw [ncWf.k_nest_container_ctors_go.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hE1 : ArrExt (erecP m) (erecP m1) := (GrowX.of_grow (q := 0) (n := 0) hg1).erecP
  obtain ⟨ys, a', hrun, hS2, hGX, h1, h2, h3, h4⟩ := ncGoW_ok fe vis C cs cl.toNat hC k m1 m2 a co cl 0 0 ns []
    r1 hgo hS1 (hE1.hslice? hns) (by omega) (by simp) (by simp) (fun i hi => by simp at hi) (by simp)
  have hgr : IWGrow m m2 := hGX.grow' hg1 (by omega)
  have hle : ys.length ≤ cl.toNat := by
    have := mapM_opt_length _ _ _ hns; simp at this; omega
  refine ⟨ys, a', hrun, hS2, hgr, by simpa using h1, ?_, ?_, by simpa using h3⟩
  · simp only [List.headD_cons]; have := hGX.1; omega
  · intro i hi
    obtain ⟨w, hw, hc⟩ := h2 i (by simpa using hi)
    exact ⟨w, by simpa using hw, by simpa using hc.mono fun _ hx => hx.1⟩

theorem decCaps_ctors {a : Nat → Option Word} {q : Nat} {caps : IIndCaps}
    (h : decCaps a q = some caps) :
    nat? a (q + 12) = some caps.nparams ∧ hlist? a (q + 13) = some caps.ctors := by
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, np, hnp, cts, hcts, heq⟩ := h
  cases Option.some.inj heq
  exact ⟨hnp, hcts⟩

/-- A number read off the constant records is the word L reads there. -/
theorem erecP_rdN {m : Mem} {i v : Nat} {x : Word} (h : nat? (erecP m) i = some v) (hx : x.toNat = i) :
    (erRd m x).toNat = v := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  rw [(erRd_of_erecP (by rw [hx]; exact hw)).1]

/-- A decoded number's word is read. -/
theorem nat?_rd {a : Nat → Option Word} {i v : Nat} (h : nat? a i = some v) : ∃ w, a i = some w := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  exact ⟨w, hw⟩

theorem nestContainer_ind {fe : IFEnv} {C : NIdx} {cv : IConstantVal} {caps : IIndCaps}
    (h : fe.find? C = some (.indInfo cv caps)) :
    ConRon.Arena.nestContainer fe C = (do
      let cs ← caps.ctors.filterMapM (ncF fe C)
      match cs with
      | [] => pure (some (caps.nparams, []))
      | c :: _ => pure (some (c.2.1, cs.map fun c => (c.1, c.2.2)))) := by
  simp only [ConRon.Arena.nestContainer, h]
  rfl

theorem nestContainer_none {fe : IFEnv} {C : NIdx} (h : ∀ cv caps, fe.find? C ≠ some (.indInfo cv caps)) :
    ConRon.Arena.nestContainer fe C = pure none := by
  simp only [ConRon.Arena.nestContainer]

end L.Ind

end
