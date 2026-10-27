import ConAgua.Arena.IndPosSpec.EntryW
import ConAgua.Arena.IndPosSpec.EnvFindWHit
import ConAgua.Arena.IndPosSpec.RootHoles

/-!
# NcGoW

`ncGoW_done`, `ncGoW_step`, `ncK1_miss`, `ncK1_hit`, `ncK2_miss`, `ncK2_hit` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (k : Nat) (m m1 m2 m3 : Mem) (vis C co cl cs ol fp nPc q : Word) (r r2 : List Word)
theorem ncGoW_done (h : cl = 0) : ncGoW (k + 1) m vis C co cl cs ol fp = some ([ol, fp], m) := by
  simp [ncGoW, h]
theorem ncGoW_step (h : ¬ cl = 0) : ncGoW (k + 1) m vis C co cl cs ol fp =
    ncK1 k vis C co cl cs ol fp (envFindW m (rdW (m.arr64 EREC) co) vis) := by simp [ncGoW, h]
theorem ncK1_miss (h : r.headD 0 = 0) : ncK1 k vis C co cl cs ol fp (some (r, m1)) =
    ncGoW k m1 vis C (co + 1) (cl - 1) cs ol fp := by rw [ncK1, ite_eq_left h]
theorem ncK1_hit (h : ¬ r.headD 0 = 0) : ncK1 k vis C co cl cs ol fp (some (r, m1)) =
    ncK2 k vis C co cl cs ol fp (entryW m1 C (r.tail.headD 0)) := by rw [ncK1, ite_eq_right h]
theorem ncK2_miss (h : r2.headD 0 = 0) : ncK2 k vis C co cl cs ol fp (some (r2, m2)) =
    ncGoW k m2 vis C (co + 1) (cl - 1) cs ol fp := by rw [ncK2, ite_eq_left h]
theorem ncK2_hit (h : ¬ r2.headD 0 = 0) : ncK2 k vis C co cl cs ol fp (some (r2, m2)) =
    ncK3 k vis C co cl cs ol fp (r2.tail.tail.headD 0)
      (posRecW m2 [r2.tail.headD 0, r2.tail.tail.tail.headD 0]) := by rw [ncK2, ite_eq_right h]
theorem ncK3_first (h : ol = 0) : ncK3 k vis C co cl cs ol fp nPc (some (q, m3)) =
    ncGoW k (m3.set64 IW (cs + ol) q) vis C (co + 1) (cl - 1) cs (ol + 1) nPc := by rw [ncK3, ite_eq_left h]
theorem ncK3_next (h : ¬ ol = 0) : ncK3 k vis C co cl cs ol fp nPc (some (q, m3)) =
    ncGoW k (m3.set64 IW (cs + ol) q) vis C (co + 1) (cl - 1) cs (ol + 1) fp := by rw [ncK3, ite_eq_right h]
end arms
attribute [ind_grind] ncGoW_done ncGoW_step ncK1_miss ncK1_hit ncK2_miss ncK2_hit ncK3_first ncK3_next

def ncB (cs : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([cs, r.headD 0, r.tail.headD 0], m2)
/-- The model of `nest_container_ctors` at exec fuel `k + 1`. -/
def ncW (k : Nat) (m : Mem) (vis C co cl : Word) : Option (List Word × Mem) :=
  match allocW m cl with
  | none => none
  | some (cs, m1) => ncB cs (ncGoW k m1 vis C co cl cs 0 0)
def ncWf : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, C, co, cl => ncW k m vis C co cl
theorem ncB_some (cs : Word) (r : List Word) (m2 : Mem) :
    ncB cs (some (r, m2)) = some ([cs, r.headD 0, r.tail.headD 0], m2) := rfl
attribute [ind_grind] ncB_some

def ntK2 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.tail.headD 0 = 0 then some ([1, rdW (m2.arr64 EREC) (q + 5 + 12), r2.headD 0, 0], m2)
    else some ([1, r2.tail.tail.headD 0, r2.headD 0, r2.tail.headD 0], m2)
def ntK1 (k : Nat) (vis C : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0], m1)
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then some ([0, 0, 0, 0], m1)
    else ntK2 (r.tail.headD 0) (ncWf k m1 vis C (rdW (m1.arr64 EREC) (r.tail.headD 0 + 5 + 13))
      (rdW (m1.arr64 EREC) (r.tail.headD 0 + 5 + 14)))
/-- The model of `nest_container(vis, C)` at exec fuel `k + 1`. -/
def ntW (k : Nat) (m : Mem) (vis C : Word) : Option (List Word × Mem) := ntK1 k vis C (envFindW m C vis)

section arms
variable (k : Nat) (m1 m2 : Mem) (vis C q : Word) (r r2 : List Word)
theorem ntK2_empty (h : r2.tail.headD 0 = 0) :
    ntK2 q (some (r2, m2)) = some ([1, rdW (m2.arr64 EREC) (q + 5 + 12), r2.headD 0, 0], m2) := by
  rw [ntK2, ite_eq_left h]
theorem ntK2_cons (h : ¬ r2.tail.headD 0 = 0) :
    ntK2 q (some (r2, m2)) = some ([1, r2.tail.tail.headD 0, r2.headD 0, r2.tail.headD 0], m2) := by
  rw [ntK2, ite_eq_right h]
theorem ntK1_miss (h : r.headD 0 = 0) : ntK1 k vis C (some (r, m1)) = some ([0, 0, 0, 0], m1) := by
  rw [ntK1, ite_eq_left h]
theorem ntK1_noind (h : ¬ r.headD 0 = 0) (h3 : rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    ntK1 k vis C (some (r, m1)) = some ([0, 0, 0, 0], m1) := by rw [ntK1, ite_eq_right h, ite_eq_left h3]
theorem ntK1_ind (h : ¬ r.headD 0 = 0) (h3 : ¬ rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    ntK1 k vis C (some (r, m1)) = ntK2 (r.tail.headD 0) (ncWf k m1 vis C
      (rdW (m1.arr64 EREC) (r.tail.headD 0 + 5 + 13)) (rdW (m1.arr64 EREC) (r.tail.headD 0 + 5 + 14))) := by
  rw [ntK1, ite_eq_right h, ite_eq_right h3]
end arms
attribute [ind_grind] ntK2_empty ntK2_cons ntK1_miss ntK1_noind ntK1_ind

section spec
variable (p : Prog) (hl : NtLook p)

set_option maxHeartbeats 1000000 in
include hl in
theorem ncGo_spec (k : Nat) : ∀ (s₀ : St) (vis C co cl cs ol fp : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_container_ctors_go" [vis, C, co, cl, cs, ol, fp]
    ⦃fun r s' => LocEq s' s₀ ∧
      ncGoW k s₀.mem vis C co cl cs ol fp = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ vis C co cl cs ol fp
    rw [invoke_eq _ hl.hgo]; simp only [callFn, nestContainerCtorsGo]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ vis C co cl cs ol fp
    simp only [invoke_eq _ hl.hgo, callFn, nestContainerCtorsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        envFind_specW p hl.hx hl.hg hl.hf k, nestCtorEntry_spec p hl.hs hl.hv hl.he hl.hst hl.ad k,
        posRec2_specW p hl.ha hl.h2 k, ih] <;>
      finish (gen := 20) [rdW_eq, St.setLocs_mem']

include hl in
theorem nc_spec (k : Nat) (s₀ : St) (vis C co cl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_container_ctors" [vis, C, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ ncWf k s₀.mem vis C co cl = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hcc, callFn, nestContainerCtors]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iwAlloc_specW p hl.ha k, ncGo_spec p hl k] <;>
      finish (gen := 20) [ncWf, ncW]

include hl in
theorem nt_spec (k : Nat) (s₀ : St) (vis C : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_container" [vis, C]
    ⦃fun r s' => LocEq s' s₀ ∧ ntW k s₀.mem vis C = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hnt, callFn, nestContainer]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      envFind_specW p hl.hx hl.hg hl.hf k, nc_spec p hl k] <;>
    finish (gen := 20) [ntW, rdW_eq]

end spec

theorem decCI_ctor_cv {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {nPc nF : Nat} (h : decCI a dn p = some (.ctorInfo cv nPc nF)) :
    decCV a (p + 1) = some cv := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  match k, h with
  | 0, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 1, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 2, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 3, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 4, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv', h1, _, _, _, _, h2⟩ := h
    cases h2; exact h1
  | 5, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 6, h => simp_all []
  | (_ + 7), h => simp_all

theorem erecP_ext_of {m m' : Mem} (h1 : erTop m ≤ erTop m')
    (h2 : ∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) : ArrExt (erecP m) (erecP m') := by
  intro i v hv
  have hlt : i < erTop m := by
    have := (Array.getElem?_eq_some_iff.mp hv).1
    simp only [erecP, Array.size_extract, erecTop] at this
    simp only [erTop]; omega
  rw [erecP_getE (by omega), h2 i hlt, ← erecP_getE hlt]; exact hv

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
  erecP_ext_of h.2.1 h.2.2.2

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
    (fun i hi => hg.2.2.1 _ (by omega))).mono fun _ hx => Nat.lt_of_lt_of_le hx hg.1

theorem ncGoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis C cs : Word) (N : Nat)
    (hC : H C) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (co cl ol fp : Word) (ns : List NIdx)
      (acc : List (IConstantVal × Nat × Nat)) (r : List Word),
    ncGoW k m vis C co cl cs ol fp = some (r, m') → StageR dn vis fe m a →
    hslice? (erecP m) co.toNat cl.toNat = some ns → cs.toNat + N ≤ iwTop m →
    ol.toNat = acc.length → acc.length + cl.toNat ≤ N →
    CsAt m cs.toNat (acc.map ncProj) (OutR cs.toNat N (iwTop m)) →
    fp.toNat = (acc.head?.map (·.2.1)).getD 0 →
    ∃ ys a', (ns.filterMapM (ncF fe (decI C))).run a = .ok (ys, a') ∧ StageR dn vis fe m' a' ∧
      GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ys.length ∧
      CsAt m' cs.toNat ((acc ++ ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
      (r.tail.headD 0).toNat = ((acc ++ ys).head?.map (·.2.1)).getD 0 ∧ ys.length ≤ ns.length := by
  induction k with
  | zero => intro m m' a co cl ol fp ns acc r h; simp [ncGoW] at h
  | succ k ih =>
    intro m m' a co cl ol fp ns acc r h hS hns hreg hol hN hacc hfp
    have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
    by_cases hc0 : cl = 0
    · rw [ncGoW_done k m vis C co cl cs ol fp hc0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc0
      have : ns = [] := by simpa [hslice?] using hns.symm
      subst this
      refine ⟨[], a, rfl, hS, GrowX.of_grow (IWGrow.refl _), by simp [hol], by simpa using hacc,
        by simpa using hfp, by simp⟩
    rw [ncGoW_step k m vis C co cl cs ol fp hc0] at h
    have hcl : cl.toNat ≠ 0 := fun e => hc0 (UInt64.toNat_inj.mp (by simpa using e))
    have hcl1 : (cl - 1).toNat = cl.toNat - 1 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
    -- the name
    obtain ⟨cl', hcl'⟩ : ∃ c', cl.toNat = c' + 1 := ⟨cl.toNat - 1, by omega⟩
    rw [hcl', hslice?_succ] at hns
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hns
    obtain ⟨n, hn, ns', hns', rfl⟩ := hns
    obtain ⟨w, hw, hwH, rfl⟩ := hd?_some hn
    have hwE : rdW (m.arr64 EREC) co = w := by simp [rdW, erecP_get hw]
    have hco : co.toNat < erTop m := by
      have := (Array.getElem?_eq_some_iff.mp hw).1; have := erecP_size_le m; omega
    have hco1 : (co + 1).toNat = co.toNat + 1 :=
      word_add_toNat (show co.toNat + 1 < 2 ^ 64 by have := hS.2.2.1; have := hS.2.2.2.2.1; omega)
    rw [hwE] at h
    have hE := hS.1.env
    rw [List.filterMapM_cons]
    rcases hef : envFindW m w vis with _ | ⟨r1, m1⟩ <;> rw [hef] at h; · simp [ncK1] at h
    have hm1 := envFindW_mem hef
    rw [hm1] at h hef
    by_cases hf0 : r1.headD 0 = 0
    · -- not found
      rw [ncK1_miss (h := hf0)] at h
      obtain ⟨-, hfind⟩ := envFindW_miss hef hE hwH hf0
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3, h4⟩ := ih m m' a (co + 1) (cl - 1) ol fp ns' acc r h hS
        (by rw [hco1, hcl1]; simpa [hcl'] using hns') hreg hol (by omega) hacc hfp
      refine ⟨ys, a', ?_, hS', hGX, h1, h2, h3, by simp; omega⟩
      simp only [ncF, hfind, StateT.run_bind]
      exact hrun
    rw [ncK1_hit (h := hf0)] at h
    obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hwH hf0
    rw [hci] at hfind
    generalize r1.tail.headD 0 = ciq at h hfind hci
    rcases hent : entryW m C ciq with _ | ⟨r2, m2⟩ <;> rw [hent] at h; · simp [ncK2] at h
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
      rw [ncK2_miss (h := rfl)] at h
      have hacc2 : CsAt m2 cs.toNat (acc.map ncProj) (OutR cs.toNat N (iwTop m)) :=
        hacc.agree ((RdS.of_grow hg2).mono fun _ hi => hi.1) hE2
          (fun i hi => hg2.2.2.1 _ (by rw [hlen] at hi; omega))
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3, h4⟩ := ih m2 m' a1 (co + 1) (cl - 1) ol fp ns' acc r h hS2
        (by rw [hco1, hcl1, show cl.toNat - 1 = cl' by omega]; exact hE2.hslice? hns')
        (by have := hg2.1; omega) hol (by omega)
        (hacc2.mono fun _ hx => ⟨Nat.lt_of_lt_of_le hx.1 hg2.1, hx.2⟩) hfp
      refine ⟨ys, a', ?_, hS', (GrowX.of_grow hg2).trans hGX, h1, h2, h3, by simp; omega⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind]
      exact hrun
    | some c =>
      obtain ⟨cv, nPc, nF⟩ := c
      obtain ⟨hr2, -, hs⟩ := hout
      subst hr2
      rw [ncK2_hit (h := by simp)] at h
      simp only [List.tail_cons, List.headD_cons] at h
      have hci' : ci = .ctorInfo cv nPc nF := by
        cases ci with
        | ctorInfo cv' nPc' nF' =>
          have := nestCtorEntry_some hrun1
          simp only [Prod.mk.injEq] at this
          obtain ⟨rfl, rfl, rfl⟩ := this; rfl
        | _ => exact absurd hrun1 (by simp [ConRon.Arena.nestCtorEntry, StateT.run, StateT.pure, pure, Except.pure])
      subst hci'
      have hcvE : decCV (erecP m) (ciq.toNat + 1) = some cv := decCI_ctor_cv hci
      have hciqb : ciq.toNat < erTop m := by
        have := decCI_idx hci; have := erecP_size_le m; omega
      have hciq1 : (ciq + 1).toNat = ciq.toNat + 1 :=
        word_add_toNat (show ciq.toNat + 1 < 2 ^ 64 by have := hS.2.2.1; have := hS.2.2.2.2.1; omega)
      have hU : UInt64.size = 2 ^ 64 := rfl
      have hnF : (UInt64.ofNat nF).toNat = nF := UInt64.toNat_ofNat_of_lt' (by omega)
      have hnPc : (UInt64.ofNat nPc).toNat = nPc := UInt64.toNat_ofNat_of_lt' (by omega)
      have htopb : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hsz
      rcases hrec : posRecW m2 [ciq + 1, UInt64.ofNat nF] with _ | ⟨q3, m3⟩ <;> rw [hrec] at h; · simp [ncK3] at h
      obtain ⟨hS3, hg3, hq3, ht3, hget3⟩ := posRecW_stage hrec hS2 (by simp)
      simp only [List.length_cons, List.length_nil] at ht3
      have hcol : (cs + ol).toNat = cs.toNat + ol.toNat := word_add_toNat (by omega)
      have hS4 := hS3.set_iw (cs + ol) q3
      have hg23 := hg2.trans hg3
      have hGX4 : GrowX cs.toNat N m (m3.set64 IW (cs + ol) q3) :=
        (GrowX.of_grow hg23).trans (GrowX.set m3 _ _ (by omega))
      have hE4 : ArrExt (erecP m) (erecP (m3.set64 IW (cs + ol) q3)) := hGX4.erecP
      have ht4 : iwTop (m3.set64 IW (cs + ol) q3) = iwTop m3 := by
        simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      have hsz3 : cs.toNat + ol.toNat < (m3.arr64 IW).size := by
        have := hS3.2.1; have := hg23.1; omega
      have hnew : CNOk (m3.set64 IW (cs + ol) q3) q3.toNat (cv, nF)
          (OutR cs.toNat N (iwTop (m3.set64 IW (cs + ol) q3))) := by
        have hg2' := hg2.1
        refine ⟨⟨by rw [ht4]; omega, Or.inr (by omega)⟩, ⟨by rw [ht4]; omega, Or.inr (by omega)⟩,
          (ciq + 1).toNat, ?_, by rw [hciq1]; exact hE4.decCV hcvE, ?_⟩
        · have := hget3 0 (by simp)
          simp only [iwN, nat?, iwA, set64IW_get]
          rw [ite_eq_right (by omega)]; simp at this; simp [this]
        · have := hget3 1 (by simp)
          simp only [iwN, nat?, iwA, set64IW_get]
          rw [ite_eq_right (by omega)]; simp at this; simp [this, hnF]
      have hacc4 : CsAt (m3.set64 IW (cs + ol) q3) cs.toNat
          ((acc ++ [(cv, nPc, nF)]).map ncProj) (OutR cs.toNat N (iwTop (m3.set64 IW (cs + ol) q3))) := by
        intro i hi
        simp only [List.map_append, List.length_append, List.length_map, List.map_cons, List.map_nil,
          List.length_cons, List.length_nil] at hi
        by_cases hia : i < acc.length
        · obtain ⟨w', hw1, hw2⟩ := hacc i (by rw [hlen]; exact hia)
          refine ⟨w', ?_, ?_⟩
          · rw [set64IW_get, ite_eq_right (by omega), hg23.2.2.1 _ (by omega)]; exact hw1
          · simp only [List.map_append, List.map_cons, List.map_nil]
            rw [List.getElem_append_left (by rw [hlen]; exact hia)]
            exact (hw2.agree hGX4.2.2.1 hE4).mono fun _ hx =>
              ⟨Nat.lt_of_lt_of_le hx.1 (by rw [ht4]; exact hg23.1), hx.2⟩
        · have hie : i = acc.length := by omega
          subst hie
          refine ⟨q3, ?_, ?_⟩
          · rw [set64IW_get, ite_eq_left ⟨by omega, by omega⟩]
          · simp only [List.map_append, List.map_cons, List.map_nil]
            rw [List.getElem_append_right (by rw [hlen]; exact Nat.le_refl _)]
            simp only [hlen, Nat.sub_self, List.getElem_cons_zero, ncProj]
            exact hnew
      have hol1 : (ol + 1).toNat = acc.length + 1 := by
        rw [word_add_toNat (show ol.toNat + (1 : Word).toNat < 2 ^ 64 by simp; omega)]; simp [hol]
      have hrest : ∀ fp' : Word, fp'.toNat = ((acc ++ [(cv, nPc, nF)]).head?.map (·.2.1)).getD 0 →
          ncGoW k (m3.set64 IW (cs + ol) q3) vis C (co + 1) (cl - 1) cs (ol + 1) fp' = some (r, m') →
          ∃ ys a', (List.filterMapM (ncF fe (decI C)) ns').run a1 = .ok (ys, a') ∧ StageR dn vis fe m' a' ∧
            GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ((cv, nPc, nF) :: ys).length ∧
            CsAt m' cs.toNat ((acc ++ (cv, nPc, nF) :: ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
            (r.tail.headD 0).toNat = ((acc ++ (cv, nPc, nF) :: ys).head?.map (·.2.1)).getD 0 ∧
            ys.length ≤ ns'.length := by
        intro fp' hfp' h'
        obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3, h4⟩ := ih _ m' a1 (co + 1) (cl - 1) (ol + 1) fp' ns'
          (acc ++ [(cv, nPc, nF)]) r h' hS4
          (by rw [hco1, hcl1, show cl.toNat - 1 = cl' by omega]; exact hE4.hslice? hns')
          (by rw [ht4]; have := hg23.1; omega) (by rw [hol1]; simp) (by simp; omega) hacc4 hfp'
        refine ⟨ys, a', hrun, hS', hGX4.trans hGX, by rw [h1]; simp; omega, ?_, ?_, h4⟩
        · simpa using h2
        · simpa using h3
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3, h4⟩ : ∃ ys a', (List.filterMapM (ncF fe (decI C)) ns').run a1 =
          .ok (ys, a') ∧ StageR dn vis fe m' a' ∧
            GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ((cv, nPc, nF) :: ys).length ∧
            CsAt m' cs.toNat ((acc ++ (cv, nPc, nF) :: ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
            (r.tail.headD 0).toNat = ((acc ++ (cv, nPc, nF) :: ys).head?.map (·.2.1)).getD 0 ∧
            ys.length ≤ ns'.length := by
        by_cases h0 : ol = 0
        · rw [ncK3_first (h := h0)] at h
          have : acc = [] := List.eq_nil_of_length_eq_zero (by rw [← hol, h0]; rfl)
          subst this
          exact hrest _ (by simp [hnPc]) h
        · rw [ncK3_next (h := h0)] at h
          have hne : acc ≠ [] := fun e => h0 (UInt64.toNat_inj.mp (by rw [hol, e]; rfl))
          obtain ⟨c0, acc', rfl⟩ := List.exists_cons_of_ne_nil hne
          exact hrest _ (by simpa using hfp) h
      refine ⟨(cv, nPc, nF) :: ys, a', ?_, hS', hGX, h1, h2, h3, by simp; omega⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, hrun, StateT.run_pure]
      rfl

theorem ncW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis C : Word) (hC : H C)
    (k : Nat) (m m' : Mem) (a : AState) (co cl : Word) (ns : List NIdx) (r : List Word)
    (h : ncW k m vis C co cl = some (r, m')) (hS : StageR dn vis fe m a)
    (hns : hslice? (erecP m) co.toNat cl.toNat = some ns) :
    ∃ ys a', (ns.filterMapM (ncF fe (decI C))).run a = .ok (ys, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.tail.headD 0).toNat = ys.length ∧ (r.headD 0).toNat + ys.length ≤ iwTop m' ∧
      CsAt m' (r.headD 0).toNat (ys.map ncProj) (· < iwTop m') ∧
      (r.tail.tail.headD 0).toNat = (ys.head?.map (·.2.1)).getD 0 := by
  unfold ncW at h
  rcases hal : allocW m cl with _ | ⟨cs, m1⟩ <;> rw [hal] at h; · simp at h
  simp only at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  have hqt : cs.toNat = iwTop m := by simp only [iwTop, hqd]
  rcases hgo : ncGoW k m1 vis C co cl cs 0 0 with _ | ⟨r1, m2⟩ <;> rw [hgo] at h; · simp [ncB] at h
  rw [ncB_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hE1 : ArrExt (erecP m) (erecP m1) := (GrowX.of_grow (q := 0) (n := 0) hg1).erecP
  obtain ⟨ys, a', hrun, hS2, hGX, h1, h2, h3, h4⟩ := ncGoW_ok dn fe vis C cs cl.toNat hC k m1 m2 a co cl 0 0 ns []
    r1 hgo hS1 (hE1.hslice? hns) (by omega) (by simp) (by simp) (fun i hi => by simp at hi) (by simp)
  have hgr : IWGrow m m2 := hGX.grow' hg1 (by omega)
  have hle : ys.length ≤ cl.toNat := by
    have := mapM_opt_length _ _ _ hns; simp at this; omega
  refine ⟨ys, a', hrun, hS2, hgr, by simpa using h1, ?_, ?_, by simpa using h3⟩
  · simp only [List.headD_cons]; have := hGX.1; omega
  · intro i hi
    obtain ⟨w, hw, hc⟩ := h2 i (by simpa using hi)
    exact ⟨w, by simpa using hw, by simpa using hc.mono fun _ hx => hx.1⟩

theorem decCaps_ctors {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {caps : IIndCaps}
    (h : decCaps a dn q = some caps) :
    nat? a (q + 12) = some caps.nparams ∧ hlist? a (q + 13) = some caps.ctors := by
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, np, hnp, cts, hcts, heq⟩ := h
  cases Option.some.inj heq
  exact ⟨hnp, hcts⟩

/-- A number read off the constant records below their top is the word L reads there. -/
theorem erecP_rdN {m : Mem} {i v : Nat} {x : Word} (h : nat? (erecP m) i = some v) (hx : x.toNat = i) :
    (rdW (m.arr64 EREC) x).toNat = v := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  simp [rdW, hx, erecP_get hw]

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

theorem ntW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis C : Word) (hC : H C)
    (k : Nat) (m m' : Mem) (a : AState) (r : List Word)
    (h : ntW k m vis C = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ x a', (ConRon.Arena.nestContainer fe (decI C)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ NcOut m' r x := by
  have hE := hS.1.env
  unfold ntW at h
  rcases hef : envFindW m C vis with _ | ⟨r1, m1⟩ <;> rw [hef] at h; · simp [ntK1] at h
  have hm1 := envFindW_mem hef
  rw [hm1] at h hef
  by_cases hf0 : r1.headD 0 = 0
  · rw [ntK1_miss (h := hf0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨-, hfind⟩ := envFindW_miss hef hE hC hf0
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    rw [nestContainer_none (fun cv caps e => by rw [hfind] at e; cases e)]; rfl
  obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hC hf0
  rw [hci] at hfind
  have hciq := decCI_idx hci
  have hsz := erecP_size_le m
  by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
  · rw [ntK1_noind (h := hf0) (h3 := h3)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    rw [nestContainer_none (fun cv caps e => by
      rw [hfind] at e; cases e
      have hk := decCI_indInfo_kind hci
      exact h3 (by
        have := erecP_rdN hk rfl
        exact UInt64.toNat_inj.mp (by rw [this]; rfl)))]; rfl
  rw [ntK1_ind (h := hf0) (h3 := h3)] at h
  generalize r1.tail.headD 0 = ciq at h hfind hci h3 hciq
  have hk3 : nat? (erecP m) ciq.toNat = some 3 := by
    have : (erecP m)[ciq.toNat]? = (m.arr64 EREC)[ciq.toNat]? := erecP_getE (by omega)
    simp only [nat?, this]
    have hb : ciq.toNat < (m.arr64 EREC).size := by have := hS.2.2.1; omega
    have : rdW (m.arr64 EREC) ciq = 3 := by simpa using h3
    simp [rdW, hb] at this ⊢; rw [this]; rfl
  obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3
  obtain ⟨hnp, hcts⟩ := decCaps_ctors hcaps
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hcts
  obtain ⟨o, ho, l, hl, hns⟩ := hcts
  have hlI := nat?_idx hl
  have hb : ciq.toNat + 5 + 13 + 1 < 2 ^ 64 := by have := hS.2.2.2.2.1; have := hS.2.2.1; omega
  have e13 : (ciq + 5 + 13).toNat = ciq.toNat + 5 + 13 := by
    rw [word_add_toNat (by simp; omega), word_add_toNat (by simp; omega)]; rfl
  have e14 : (ciq + 5 + 14).toNat = ciq.toNat + 5 + 13 + 1 := by
    rw [word_add_toNat (by simp; omega), word_add_toNat (by simp; omega)]; rfl
  have e12 : (ciq + 5 + 12).toNat = ciq.toNat + 5 + 12 := by
    rw [word_add_toNat (by simp; omega), word_add_toNat (by simp; omega)]; rfl
  have ro := erecP_rdN ho e13
  have rl := erecP_rdN hl e14
  generalize rdW (m.arr64 EREC) (ciq + 5 + 13) = co at h ro
  generalize rdW (m.arr64 EREC) (ciq + 5 + 14) = cl at h rl
  rw [nestContainer_ind hfind]
  cases k with
  | zero => simp [ncWf, ntK2] at h
  | succ k =>
  simp only [ncWf] at h
  rcases hnc : ncW k m vis C co cl with _ | ⟨r2, m2⟩ <;> rw [hnc] at h; · simp [ntK2] at h
  obtain ⟨ys, a', hrun, hS2, hg2, h1, h2, h3', h4⟩ := ncW_ok dn fe vis C hC k m m2 a co cl caps.ctors r2 hnc hS
    (by rw [ro, rl]; exact hns)
  have hrun' : (do
      let cs ← List.filterMapM (ncF fe (decI C)) caps.ctors
      match cs with
      | [] => pure (some (caps.nparams, []))
      | c :: _ => pure (some (c.2.1, cs.map fun c => (c.1, c.2.2))) : AM _).run a =
      .ok ((match ys with
        | [] => some (caps.nparams, [])
        | c :: _ => some (c.2.1, ys.map fun c => (c.1, c.2.2))), a') := by
    simp only [StateT.run_bind, hrun, except_ok_bind]; cases ys <;> rfl
  cases ys with
  | nil =>
    rw [ntK2_empty (h := by apply UInt64.toNat_inj.mp; simpa using h1)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨_, a', hrun', hS2, hg2, rfl, ?_, rfl, by simpa using h2, by simpa using h3'⟩
    have hnpI := nat?_idx hnp
    have : (m2.arr64 EREC)[ciq.toNat + 5 + 12]? = (erecP m)[ciq.toNat + 5 + 12]? := by
      rw [hg2.2.2.2 _ (by omega), erecP_getE (by omega)]
    simp only [List.tail_cons, List.headD_cons]
    simp only [nat?, Option.map_eq_some_iff] at hnp
    obtain ⟨w, hw, hw'⟩ := hnp
    rw [← hw']
    simp [rdW, e12, this, hw]
  | cons c ys =>
    rw [ntK2_cons (h := fun e => by rw [e] at h1; simp at h1)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨_, a', hrun', hS2, hg2, rfl, by simpa using h4, by simpa using h1, by simpa using h2,
      by rw [show (fun c : IConstantVal × Nat × Nat => (c.fst, c.snd.snd)) = ncProj from rfl]; simpa using h3'⟩

end L.Ind

end
