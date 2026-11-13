module

public import ConAgua.Arena.DefEqStuckGo
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.IndView
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConRon.Bridge.Grind
import ConAgua.L.WordOff
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Arena.EtaRescueRef
import ConAgua.Arena.IndRecRead
import ConAgua.Arena.Inst1Refine

@[expose] public section

/-!
# `struct_eta_cert_wtb`, `struct_eta_cert_with`, `struct_eta_cert` (lane `defeq`, helper `defeq-top`)

`structEtaCertWith` in L's pieces: the constructor's head and spine (`with`), the type's head
and spine (`wtb`, `setWtbT`), then `go` (`DefEqStuckGo.lean`). The slices pushed on the way stay
on the stack until `with` puts the top back (`GrowPost.restore`). One refinement per piece for
both outcomes (`RefE` over its unified model, `Verdict/WhnfModels7E.lean`); the errors are the
knot's slots' and `defeq_lst`'s (`SetG`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Records -/

/-- The kind word of a decoded record says whether it is an inductive. -/
theorem decCI_indK {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {ci : IConstantInfo} (h : decCI R q.toNat = some ci) :
    (rd q = 3 → ∃ cv caps, ci = .indInfo cv caps) ∧
    (rd q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  cases hq : R q.toNat with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrd : rd q = w := hR.rd _ _ hq
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 3 = 3 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, -, caps, -, hc⟩ := h
    cases hc
    exact ⟨cv, caps, rfl⟩
  · intro hw cv caps hc
    subst hc
    have hne : w.toNat ≠ 3 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

/-! ## The twin, after the constructor's spine -/

/-- **`structEtaCertWith` past the constructor's spine**, copied. -/
def setWtbT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (aargs : List EIdx) (wtb : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel wtb
  if hh.tag == ETag.const then
    view hh >>= fun v => match v with
      | .const T us' =>
        match fe.find? T with
        | some (.indInfo cvT caps) =>
          match fe.findTable? T with
          | none => pure false
          | some tbl => do
            let targs ← getAppArgs coreWalkFuel wtb
            setGoT r fe depth b c us cvc T us' cvT caps tbl aargs targs
        | _ => pure false
      | _ => pure false
  else pure false

section wtbRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
  (cvc : IConstantVal) (aargs : List EIdx) (wtb : EIdx) (a : AState) (hh : EIdx)
  (hgaf : (getAppFn coreWalkFuel wtb).run a = .ok (hh, a))

include hgaf

theorem setWtbT_nonconst (ht : (hh.tag == ETag.const) = false) :
    (setWtbT r fe depth b c us cvc aargs wtb).run a = .ok (false, a) := by
  simp only [setWtbT, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem setWtbT_other (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const T us'))
    (hf : ∀ cv caps, fe.find? T ≠ some (.indInfo cv caps)) :
    (setWtbT r fe depth b c us cvc aargs wtb).run a = .ok (false, a) := by
  simp only [setWtbT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases hc : fe.find? T with _ | ⟨_ | _ | _ | ⟨cv, caps⟩ | _ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv caps)

theorem setWtbT_notbl (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const T us')) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (htb : fe.findTable? T = none) :
    (setWtbT r fe depth b c us cvc aargs wtb).run a = .ok (false, a) := by
  simp only [setWtbT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf,
    htb]
  rfl

theorem setWtbT_ind (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const T us')) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (tbl : IProjTable)
    (htb : fe.findTable? T = some tbl) (targs : List EIdx)
    (hargs : (getAppArgs coreWalkFuel wtb).run a = .ok (targs, a)) :
    (setWtbT r fe depth b c us cvc aargs wtb).run a =
      (setGoT r fe depth b c us cvc T us' cvT caps tbl aargs targs).run a := by
  simp only [setWtbT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf,
    htb, hargs]

end wtbRuns

/-- A step that only pushed (twin unchanged) in front of a run that grew the stack. -/
theorem growRef_preG {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (hg : StackGrew m₀ m₁)
    (h : GrowRef T a₀ dec dn m₁ vis fe M eb r m ok) : GrowRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, ⟨M'', hS'', hK'', hSt''⟩, hres, hr⟩ := h
  exact ⟨hok, ⟨M'', hS'', hK'', hg.trans hSt''⟩, hres, hr⟩

/-- **`struct_eta_cert_wtb` refines `setWtbT`, both outcomes** (its slices left on the stack): the
errors are `struct_eta_cert_go`'s. -/
@[refines_part ConRon.Arena.structEtaCertWith "the type's head and spine (setWtbT)"]
theorem secwtb_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us c pc ao an wtb : Word) (aargs : Array EIdx) (cvc : IConstantVal) (np nf : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b)
    (hus : HW us) (hcw : HW c) (hwtb : HW wtb)
    (hvus : ∃ x c', a₀.store.view x = some (.const c' (decI us)))
    {fam : NIdx} (hcvc : decCI (erecP s₀.mem) pc.toNat = some (.ctorInfo cvc np nf fam))
    (ha : SpineR s₀.mem ao an aargs) (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (SetG p n) (secwtbE p (n + 1) s₀.mem mode vis d b us c pc ao an wtb)
      (setWtbT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc
        aargs.toList (decE wtb)) a₀ (GrowPost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hR := hS.arena.base
  have hl : RefE (SetG p n) (.ok ([0], s₀.mem) : Except Err (List Word × Mem)) (pure false : AM Bool)
      a₀ (GrowPost decBool dn s₀.mem vis fe M eb ResH) :=
    RefE.ret rfl (GrowPost.of_core (CorePost.ret hS rfl hw0))
  simp only [secwtbE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppFn_callW hq.leaf hR hwtb h)
    fun r₁ m₁ ⟨e1, hh, hgaf⟩ => ?_
  subst e1
  dsimp only [secwtbE.k_get_app_fn]
  generalize r₁.headD 0 = h at hh hgaf
  by_cases h3 : tagW h ≠ 3
  · rw [ite_eq_left h3]
    exact RefE.of_run_eq (setWtbT_nonconst _ fe _ _ _ _ _ _ _ a₀ _ hgaf
      (by rw [decE_tag_const_beq _ hh]; simpa using h3)) hl
  rw [ite_eq_right h3]
  have h3' : tagW h = 3 := by simpa using h3
  refine RefE.abort0 (by decide) fun hsc => ?_
  refine RefE.abort0 (by decide) fun hcc => ?_
  have hvo : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR h hh hvo h3'
  have hct : ((decE h).tag == ETag.const) = true := by rw [decE_tag_const_beq _ hh]; simp [h3']
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 0 = k at hnw hv
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 1 = us2 at huw hv
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => envFind_callW hq.leaf.core hS.env hnw h)
    fun r₂ m₂ ⟨e2, hfind, hfound⟩ => ?_
  subst e2
  dsimp only [secwtbE.k_env_find]
  by_cases h0 : r₂.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    exact RefE.of_run_eq (setWtbT_other _ fe _ _ _ _ _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv caps e => by rw [hnone] at e; cases e)) hl
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hind := decCI_indK (erRdOK _) hci
  by_cases h4 : erRd s₀.mem (r₂.tail.headD 0) ≠ 3
  · erw [ite_eq_left h4]
    exact RefE.of_run_eq (setWtbT_other _ fe _ _ _ _ _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv caps e => hind.2 h4 cv caps (by rw [hfind'] at e; exact Option.some.inj e))) hl
  erw [ite_eq_right h4]
  obtain ⟨cvT, caps, hci_eq⟩ := hind.1 (by simpa using h4)
  rw [hci_eq] at hci
  -- the family's projection table
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (findTable_refines p hq.findTable _ _ vis k hS.env hnw) h)
    fun r₀ m₀ ⟨t₀, ht₀, hm₀, _, hft, hfs⟩ => ?_
  obtain rfl : m₀ = s₀.mem := ht₀.symm.trans hm₀
  dsimp only [secwtbE.k_find_table]
  by_cases hz : r₀.headD 0 = 0
  · rw [ite_eq_left hz]
    exact RefE.of_run_eq (setWtbT_notbl _ fe _ _ _ _ _ _ _ a₀ _ hgaf _ _ hct hv cvT caps
      (by rw [hfind', hci_eq]) (by rw [hft, tblFound, ite_eq_left hz])) hl
  rw [ite_eq_right hz]
  obtain ⟨tbl, htbl'⟩ := hfs hz
  have htbl : tblFound s₀.mem (r₀.headD 0) = some tbl := by rw [tblFound, ite_eq_right hz, htbl']
  -- the type's spine
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppArgs_callW hq.leaf.core.spine hS hwtb h)
    fun r₃ m₃ ⟨hf3, hg3, hr30, htop3, targs, hargs, hsp⟩ => ?_
  have hS₃ := hS.frame_stk hf3 (by simp) (by simp)
  have hep : erecP m₃ = erecP s₀.mem := erecP_frame hf3 (by simp [EREC, SPN]) (by simp [EREC, SPN, tier1]) (by simp)
    (by simp)
  simp only [secwtbE.k_get_app_args]
  refine RefE.of_run_eq (setWtbT_ind _ fe _ _ _ _ _ _ _ a₀ _ hgaf _ _ hct hv cvT caps
    (by rw [hfind', hci_eq]) tbl (by rw [hft, htbl]) targs hargs) ?_
  have hspn := hS.spn
  have hb3 := hsp.bound
  have hsz3 : (m₃.arr64 SPN).size < 2 ^ 63 := hg3.size ▸ hspn
  have htt : (r₃.headD 0).toNat + (r₃.tail.headD 0).toNat ≤ (spTop m₃).toNat := by
    have e := L.toNat_add_of_lt (r₃.headD 0) (r₃.tail.headD 0) (by omega)
    rw [htop3, ← hr30]; omega
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ n' =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ n')) rfl
    (fun _ _ _ h => ⟨CoreAfterG.compK (KeptAll.refl _ _) hg3 h.after, h.res, h.valid⟩)
    (secg_ref p hq hi hc n' (hk.mono (by omega)) F ⟨m₃, Locals.init []⟩ a₀ dn vis fe M eb mode d
      b us c pc k (r₂.tail.headD 0) (r₀.headD 0) us2 ao an (r₃.headD 0) (r₃.tail.headD 0) aargs
      targs.toArray cvc np nf cvT caps tbl (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ hb hus hcw
      hnw huw hvus ⟨_, _, hv⟩ (by rw [hep]; exact hcvc) (by rw [hep]; exact hci)
      (by simp only [tblFound] at htbl ⊢; rw [hep]; exact htbl) (ha.grew hg3 hat hspn) hsp
      (Nat.le_trans hat (UInt64.le_iff_toNat_le.mp hg3.1)) htt)

/-! ## `struct_eta_cert_with` -/

theorem structEtaCertWith_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b wtb : EIdx) :
    structEtaCertWith r fe depth a b wtb = (do
      let hh ← getAppFn coreWalkFuel a
      if hh.tag == ETag.const then
        view hh >>= fun v => match v with
          | .const c us =>
            match fe.find? c with
            | some (.ctorInfo cvc cnP cnF _) => do
              let aargs ← getAppArgs coreWalkFuel a
              if aargs.length = cnP + cnF then setWtbT r fe depth b c us cvc aargs wtb
              else pure false
            | _ => pure false
          | _ => pure false
      else pure false) := by rfl

/-- The top put back, then the verdict `v` (a model step of `stuck_app_cong`, `DefEqStuckApp.lean`). -/
def swRet (top v : Word) (m : Mem) : Option (Word × Mem) :=
  if (136 : Word).toNat < (m.arr64 CTL).size then some (v, m.set64 CTL 136 top) else none

section withRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b wtb : EIdx) (st : AState) (hh : EIdx)
  (hgaf : (getAppFn coreWalkFuel a).run st = .ok (hh, st))

include hgaf

theorem setWith_nonconst (ht : (hh.tag == ETag.const) = false) :
    (structEtaCertWith r fe depth a b wtb).run st = .ok (false, st) := by
  rw [structEtaCertWith_eq]
  simp only [StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem setWith_other (c : NIdx) (us : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const c us))
    (hf : ∀ cv np nf fam, fe.find? c ≠ some (.ctorInfo cv np nf fam)) :
    (structEtaCertWith r fe depth a b wtb).run st = .ok (false, st) := by
  rw [structEtaCertWith_eq]
  simp only [StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases hc : fe.find? c with _ | ⟨_ | _ | _ | _ | ⟨cv, np, nf⟩ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv np nf)

theorem setWith_ctor (c : NIdx) (us : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const c us)) (cvc : IConstantVal) (np nf : Nat)
    {fam : NIdx} (hf : fe.find? c = some (.ctorInfo cvc np nf fam)) (aargs : List EIdx)
    (hargs : (getAppArgs coreWalkFuel a).run st = .ok (aargs, st)) :
    (structEtaCertWith r fe depth a b wtb).run st =
      (if aargs.length = np + nf then setWtbT r fe depth b c us cvc aargs wtb else pure false).run st := by
  rw [structEtaCertWith_eq]
  simp only [StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf, hargs]

end withRuns

/-- The L count test is the twin's. -/
theorem count_iff (an npw nfw : Word) :
    an.toNat = npw.toNat + nfw.toNat ↔ (¬ an < nfw ∧ an - nfw = npw) := by
  constructor
  · intro h
    have h1 : ¬ an < nfw := by rw [UInt64.lt_iff_toNat_lt]; omega
    refine ⟨h1, UInt64.toNat_inj.mp ?_⟩
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega
  · rintro ⟨h1, h2⟩
    have h1' : nfw.toNat ≤ an.toNat := Nat.not_lt.mp (fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h))
    have := congrArg UInt64.toNat h2
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h1')] at this; omega

/-- **`struct_eta_cert_with` refines `structEtaCertWith`, both outcomes** (the top put back): the
errors are `struct_eta_cert_wtb`'s. -/
theorem secw_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b wtb : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hwtb : HW wtb) :
    RefE (SetG p n) (secwE p (n + 1) s₀.mem mode vis d a b wtb)
      (structEtaCertWith (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b) (decE wtb))
      a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hR := hS.arena.base
  have hl : RefE (SetG p n) (.ok ([0], s₀.mem) : Except Err (List Word × Mem)) (pure false : AM Bool)
      a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := RefE.ret rfl (CorePost.ret hS rfl hw0)
  simp only [secwE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppFn_callW hq.leaf hR ha h)
    fun r₁ m₁ ⟨e1, hh, hgaf⟩ => ?_
  subst e1
  dsimp only [secwE.k_get_app_fn]
  generalize r₁.headD 0 = h at hh hgaf
  by_cases h3 : tagW h ≠ 3
  · rw [ite_eq_left h3]
    exact RefE.of_run_eq (setWith_nonconst _ fe _ _ _ _ a₀ _ hgaf
      (by rw [decE_tag_const_beq _ hh]; simpa using h3)) hl
  rw [ite_eq_right h3]
  have h3' : tagW h = 3 := by simpa using h3
  refine RefE.abort0 (by decide) fun hsc => ?_
  refine RefE.abort0 (by decide) fun hcc => ?_
  have hvo : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR h hh hvo h3'
  have hct : ((decE h).tag == ETag.const) = true := by rw [decE_tag_const_beq _ hh]; simp [h3']
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 0 = k at hnw hv
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 1 = us at huw hv
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => envFind_callW hq.leaf.core hS.env hnw h)
    fun r₂ m₂ ⟨e2, hfind, hfound⟩ => ?_
  subst e2
  dsimp only [secwE.k_env_find]
  by_cases h0 : r₂.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    exact RefE.of_run_eq (setWith_other _ fe _ _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv np nf fam e => by rw [hnone] at e; cases e)) hl
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hctor := L.Arena.decCI_ctorR (erRdOK _) hci
  by_cases h4 : erRd s₀.mem (r₂.tail.headD 0) ≠ 4
  · erw [ite_eq_left h4]
    exact RefE.of_run_eq (setWith_other _ fe _ _ _ _ a₀ _ hgaf _ _ hct hv
      (fun cv np nf fam e => hctor.2 h4 cv np nf fam (by rw [hfind'] at e; exact Option.some.inj e))) hl
  erw [ite_eq_right h4]
  obtain ⟨cvc, hci_eq, -⟩ := hctor.1 (by simpa using h4)
  rw [hci_eq] at hci
  -- the constructor's spine
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppArgs_callW hq.leaf.core.spine hS ha h)
    fun r₃ m₃ ⟨hf3, hg3, hr30, htop3, aargs, hargs, hsp⟩ => ?_
  have hS₃ := hS.frame_stk hf3 (by simp) (by simp)
  have hep : erecP m₃ = erecP s₀.mem := erecP_frame hf3 (by simp [EREC, SPN]) (by simp [EREC, SPN, tier1]) (by simp)
    (by simp)
  have herec : ∀ x : Word, rdW (m₃.arr64 (tierA EREC (x >>> 40))) (x &&& 0xFFFFFFFFFF) = erRd s₀.mem x :=
    erRd_congr (hf3.1 EREC (by simp [EREC, SPN]) (by decide))
      (hf3.1 (tier1 EREC) (by simp [EREC, SPN, tier1]) (by decide))
  refine RefE.of_run_eq (setWith_ctor _ fe _ _ _ _ a₀ _ hgaf _ _ hct hv cvc _ _
    (by rw [hfind', hci_eq]) aargs hargs) ?_
  have hlen : aargs.length = (r₃.tail.headD 0).toNat := by simpa using hsp.size
  have hsz3 : (m₃.arr64 SPN).size < 2 ^ 63 := hg3.size ▸ hS.spn
  simp only [secwE.k_get_app_args, herec]
  by_cases hcnt : ¬ r₃.tail.headD 0 < erRd s₀.mem (r₂.tail.headD 0 + 6) ∧
      r₃.tail.headD 0 - erRd s₀.mem (r₂.tail.headD 0 + 6) =
        erRd s₀.mem (r₂.tail.headD 0 + 5)
  · rw [ite_eq_right (fun h => h.elim hcnt.1 (fun h' => h' hcnt.2))]
    rw [ite_eq_left (by rw [hlen]; exact (count_iff _ _ _).mpr hcnt)]
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ n' =>
    exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ n')) rfl
      (fun v _ _ h => (GrowPost.mk (CoreAfterG.compK (KeptAll.refl _ _) hg3 h.after) h.res
        h.valid).restore _ rfl h.valid)
      (secwtb_ref p hq hi hc n' (hk.mono (by omega)) F ⟨m₃, Locals.init []⟩ a₀ dn vis fe M eb mode
        d b us k (r₂.tail.headD 0) (r₃.headD 0) (r₃.tail.headD 0) wtb aargs.toArray cvc _ _
        (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ hb huw hnw hwtb ⟨_, _, hv⟩
        (by rw [hep]; exact hci) hsp (by
          have e := L.toNat_add_of_lt (r₃.headD 0) (r₃.tail.headD 0)
            (by have := hsp.bound; omega)
          rw [htop3, ← hr30]; omega))
  · rw [ite_eq_left (by
      by_cases hc1 : r₃.tail.headD 0 < erRd s₀.mem (r₂.tail.headD 0 + 6)
      · exact .inl hc1
      · exact .inr (fun e => hcnt ⟨hc1, e⟩))]
    rw [ite_eq_right (by rw [hlen, count_iff]; exact hcnt)]
    obtain ⟨hS', hK'⟩ := hS.restoreTop' hf3 hg3
    exact RefE.ret rfl ⟨⟨M, hS', KeptAll.refl _ _, hK'⟩, rfl, hw0⟩

theorem etaCtorShape_at (p : Prog) (hq : StuckProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
      (fe : IFEnv) (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
      CoreSpec p n "eta_ctor_shape" [vis, e] (etaCtorShape fe (decE e)) decBool s₀ a₀ dn vis fe MM eb
  | 0, s₀, a₀, dn, vis, fe, MM, eb, _, _, _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | n + 1, s₀, a₀, dn, vis, fe, MM, eb, e, hS, he =>
      etaCtorShape_refines p hq n s₀ a₀ dn vis fe MM eb e hS he

/-! ## `struct_eta_full_at`, `struct_eta_cert` -/

/-- **`struct_eta_full_at` refines `structEtaFullAt`, both outcomes**: the errors are the
`infer_io`, `whnf` slots' and `struct_eta_cert_with`'s. -/
theorem sefa_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (SetG p n) (sefaE p (n + 1) s₀.mem mode vis d a b)
      (structEtaFullAt (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [sefaE]
  unfold structEtaFullAt
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F _ _ dn vis fe M eb mode d b hF hn hs hb)
    (fun (hG : SetG p n) => (hG.knot n (Nat.le_refl _)).inferIO F _ _ dn vis fe M eb mode d b hF hn hs hb)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [sefaE.k_infer_io]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₂ eb mode d _ hF hn hs₂ h₂.resOk)
    (fun (hG : SetG p n) => (hG.knot n (Nat.le_refl _)).whnf F _ _ dn vis fe M₂ eb mode d _ hF hn hs₂
      h₂.resOk)
    fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [sefaE.k_whnf]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N)) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (secw_ref p hq hi hc N (hk.mono (Nat.le_succ N)) F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d
      a b (r₃.headD 0) (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb h₃.resOk)

/-! ## The partial-constructor arm: `eta_ctor_partial`, `struct_eta_expand`, `struct_eta_cert_partial` -/

/-- An ok run of a reading callee: the memory and the twin state kept, the result decoded. -/
def ReadPost {α : Type} (dec : List Word → α) (ok : List Word → Prop) (m : Mem) (a : AState)
    (v : List Word × Mem) (y : α) (a' : AState) : Prop :=
  v.2 = m ∧ a' = a ∧ y = dec v.1 ∧ ok v.1

/-- **`eta_ctor_partial_fam` refines `etaCtorPartialFam`, both outcomes** (the errors are aborts
and its callees' class-`0` failures): one lookup of the family `T`, no walk. -/
theorem ecpf_ref (p : Prog) (hq : StuckProg p) {G : Prop} (n : Nat) (m : Mem) (a₀ : AState)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a₀ vis fe M eb) (c k : Word) (hc : HW c) (hnw : HW k) :
    RefE G (ecpfE p n m vis c k) (pure (etaCtorPartialFam fe (decI c) (decI k)) : AM Bool) a₀
      (ReadPost decBool ResH m a₀) := by
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ n =>
  simp only [ecpfE]
  unfold etaCtorPartialFam
  have hl : RefE G (.ok ([0], m) : Except Err (List Word × Mem)) (pure false : AM Bool) a₀
      (ReadPost decBool ResH m a₀) := RefE.ret rfl ⟨rfl, rfl, rfl, hw0⟩
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => envFind_callW hq.leaf.core hS.env hnw h)
    fun r₃ m₃ ⟨e3, hfind, hfound⟩ => ?_
  subst m₃
  dsimp only [ecpfE.k_env_find]
  by_cases h0 : r₃.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    rw [hnone]; exact hl
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hind := decCI_indK (erRdOK _) hci
  rw [hfind']
  by_cases h4 : erRd m (r₃.tail.headD 0) ≠ 3
  · erw [ite_eq_left h4]
    rcases ci with _ | _ | _ | _ | _ | _ | _ <;> try exact hl
    all_goals exact absurd rfl (hind.2 h4 _ _)
  erw [ite_eq_right h4]
  obtain ⟨cvT, caps, rfl⟩ := hind.1 (by simpa using h4)
  have hIR := decCI_indCaps (erRdOK m) hci
  simp only
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (findTable_refines p hq.findTable n _ vis k hS.env hnw) h)
    fun r₄ m₄ hx4 => ?_
  obtain ⟨s4, hs4, hm4, -, htb, htbs⟩ := hx4
  have e4 : m₄ = m := hs4.symm.trans hm4
  rw [e4]
  dsimp only [ecpfE.k_find_table]
  simp only [L.Ind.erRd_foldN] at *
  rw [htb]
  by_cases g0 : r₄.headD 0 = 0
  · rw [ite_eq_left g0]
    simp only [tblFound, g0, ↓reduceIte]; exact hl
  rw [ite_eq_right g0]
  obtain ⟨tb, htb'⟩ := htbs g0
  have hT : tblFound m (r₄.headD 0) = some tb := by simp only [tblFound, g0, ↓reduceIte]; exact htb'
  obtain ⟨-, -, hcw, hcd, -⟩ := tblFound_words hT
  rw [hT]
  simp only
  have heta := hIR.eta
  by_cases g1 : erRd m (r₃.tail.headD 0 + (CI.indCaps + Caps.eta)) = 0
  · erw [ite_eq_left g1]
    rw [show caps.eta = false by rw [heta, g1]; rfl]
    exact hl
  erw [ite_eq_right g1]
  rw [show caps.eta = true by rw [heta]; simpa using g1]
  simp only [↓reduceIte]
  have hb : (tb.ctor == decI c) = decide (erRd m (r₄.headD 0 + 5) = c) := by
    rw [hcd]
    by_cases e : erRd m (r₄.headD 0 + 5) = c
    · rw [e, decide_eq_true rfl]; exact beq_self_eq_true _
    · have : ¬ (decI (erRd m (r₄.headD 0 + 5)) : NIdx) = decI c := fun h' => e (decI_inj hcw hc h')
      rw [decide_eq_false e]; exact beq_false_of_ne this
  rw [hb]
  by_cases e : erRd m (r₄.headD 0 + 5) = c
  · erw [ite_eq_left e]; rw [decide_eq_true e]; exact RefE.ret rfl ⟨rfl, rfl, rfl, hw1⟩
  · erw [ite_eq_right e]; rw [decide_eq_false e]; exact RefE.ret rfl ⟨rfl, rfl, rfl, hw0⟩

/-- `eta_ctor_partial`'s answer `(f, k)`: `some k` for a flag `f ≠ 0`. -/
def decOptNat (r : List Word) : Option Nat := if r.headD 0 = 0 then none else some (r.tail.headD 0).toNat

theorem toNat_add_of_not_lt' {a b : Word} (h : ¬ a + b < a) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  apply Nat.mod_eq_of_lt
  apply Classical.byContradiction; intro hc
  apply h; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  have := a.toNat_lt; have := b.toNat_lt
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- **`eta_ctor_partial` refines `etaCtorPartial`, both outcomes** (the stack top put back; the
errors are aborts and the callees' class-`0` failures). -/
theorem ecp_ref (p : Prog) (hq : StuckProg p) {G : Prop} (n : Nat) (m : Mem) (a₀ : AState)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a₀ vis fe M eb) (a : Word) (ha : HW a) :
    RefE G (ecpE p n m vis a) (etaCtorPartial fe (decE a)) a₀
      (CorePost decOptNat dn m vis fe M eb (fun _ => True)) := by
  have hR := hS.arena.base
  have hl : ∀ (m' : Mem) (a' : AState) (T : AM (Option Nat)), T.run a₀ = .ok (none, a') →
      CoreAfter dn m m' a' vis fe M eb →
      RefE G (.ok ([0, 0], m') : Except Err (List Word × Mem)) T a₀
        (CorePost decOptNat dn m vis fe M eb (fun _ => True)) :=
    fun m' a' T hT hA => RefE.ret hT ⟨hA, rfl, trivial⟩
  have hA0 : CoreAfter dn m m a₀ vis fe M eb := ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ n =>
  simp only [ecpE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppFn_callW hq.leaf hR ha h)
    fun r₁ m₁ hx => ?_
  obtain ⟨e1, hh, hgaf⟩ := hx
  rw [e1]
  dsimp only [ecpE.k_get_app_fn]
  unfold etaCtorPartial
  refine RefE.bind_right hgaf ?_
  generalize r₁.headD 0 = h at hh hgaf ⊢
  by_cases h3 : tagW h ≠ 3
  · rw [ite_eq_left h3, decE_tag_const_beq _ hh]
    simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact hl m a₀ _ rfl hA0
  rw [ite_eq_right h3]
  have h3' : tagW h = 3 := by simpa using h3
  refine RefE.abort0 (by decide) fun hsc => ?_
  refine RefE.abort0 (by decide) fun hcc => ?_
  have hvo : viewOK m h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, -⟩ := L.Ind.view_const_f m a₀ hR h hh hvo h3'
  rw [decE_tag_const_beq _ hh]
  simp only [h3', decide_true, ↓reduceIte]
  refine RefE.bind_right (view_run _ _ _ hv) ?_
  generalize tfld m CONST (tierW h) (idxW h) 0 = k at hnw hv ⊢
  simp only
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => envFind_callW hq.leaf.core hS.env hnw h)
    fun r₂ m₂ hx => ?_
  obtain ⟨e2, hfind, hfound⟩ := hx
  rw [e2]
  dsimp only [ecpE.k_env_find]
  by_cases h0 : r₂.headD 0 = 0
  · rw [ite_eq_left h0]
    have hnone : fe.find? (decI k) = none := by rw [hfind]; simp only [envFound, h0, ↓reduceIte]
    rw [hnone]; exact hl m a₀ _ rfl hA0
  rw [ite_eq_right h0]
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hctor := L.Arena.decCI_ctorR (erRdOK _) hci
  rw [hfind']
  by_cases h4 : erRd m (r₂.tail.headD 0) ≠ 4
  · erw [ite_eq_left h4]
    rcases ci with _ | _ | _ | _ | ⟨cv, np, nf, fam⟩ | _ | _ <;> try exact hl m a₀ _ rfl hA0
    exact absurd rfl (hctor.2 h4 cv np nf fam)
  erw [ite_eq_right h4]
  obtain ⟨cvc, hci_eq, hfw⟩ := hctor.1 (by simpa using h4)
  rw [hci_eq] at hci ⊢
  simp only [L.Ind.erRd_foldN] at *
  refine RefE.abort0 (by decide) fun hov => ?_
  have hsum := toNat_add_of_not_lt' hov
  try simp only
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => getAppArgs_callW hq.leaf.core.spine hS ha h)
    fun r₃ m₃ hx => ?_
  obtain ⟨hf3, hg3, -, -, aargs, hargs, hsp⟩ := hx
  refine RefE.bind_right hargs ?_
  dsimp only [ecpE.k_get_app_args]
  obtain ⟨hS', hK'⟩ := hS.restoreTop' hf3 hg3
  have hA' : CoreAfter dn m (m₃.set64 CTL 136 (rdW (m.arr64 CTL) 136)) a₀ vis fe M eb :=
    ⟨M, hS', KeptAll.refl _ _, hK'⟩
  have hlen : aargs.length = (r₃.tail.headD 0).toNat := by simpa using hsp.size
  generalize erRd m (r₂.tail.headD 0 + 5) = npw at hsum hov ⊢
  generalize erRd m (r₂.tail.headD 0 + 6) = nfw at hsum hov ⊢
  by_cases g : npw + nfw ≤ r₃.tail.headD 0
  · rw [ite_eq_left g, ite_eq_right (by rw [hlen, ← hsum]; exact Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp g))]
    exact hl _ a₀ _ rfl hA'
  rw [ite_eq_right g, ite_eq_left (by
    rw [hlen, ← hsum]; exact UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp g))]
  show RefE G _ (pure (etaCtorPartialFam fe (decI k) (decI (erRd m (r₂.tail.headD 0 + 7)))) >>=
    fun b => if b = true then pure (some (npw.toNat + nfw.toNat - aargs.length)) else pure none) a₀ _
  refine RefE.bindE (fun _ => rfl) (fun hg => hg) (ecpf_ref p hq _ _ a₀ hS' k
    (erRd m (r₂.tail.headD 0 + 7)) hnw hfw) fun v y a₁ _ hQ => ?_
  obtain ⟨e5, ha1, hy, -⟩ := hQ
  obtain ⟨r₅, m₅⟩ := v
  simp only at e5 hy
  subst a₁ y e5
  dsimp only [ecpE.k_eta_ctor_partial_fam]
  by_cases g5 : r₅.headD 0 = 0
  · rw [ite_eq_left g5, decBool_false_of g5]
    exact hl _ a₀ _ rfl hA'
  rw [ite_eq_right g5, decBool_true_of g5]
  have hlt : (r₃.tail.headD 0).toNat < npw.toNat + nfw.toNat := by
    rw [← hsum]; exact UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp g)
  refine RefE.ret rfl ⟨hA', ?_, trivial⟩
  simp only [decOptNat, List.headD_cons, List.tail_cons, (by decide : ¬ (1 : Word) = 0), ↓reduceIte, hlen]
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hsum]; omega)), hsum]

/-- **`struct_eta_full` refines `structEtaFull`, both outcomes**: the shape gate, then
`struct_eta_full_at`. -/
theorem sef_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (SetG p n) (sefE p (n + 1) s₀.mem mode vis d a b)
      (structEtaFull (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  simp only [sefE]
  unfold structEtaFull
  refine RefE.bind_callW (fun _ => rfl) (etaCtorShape_at p hq n s₀ a₀ dn vis fe M eb a hs.rel ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [sefE.k_eta_ctor_shape]
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, L.Arena.decBool_false_of h0]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl hw0)
  rw [ite_eq_right h0, L.Arena.decBool_true_of h0]
  simp only [↓reduceIte]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N)) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (sefa_ref p hq hi hc N (hk.mono (Nat.le_succ N)) F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
      a b (by omega) (by omega) ⟨hS₁, hs.mode4, hs.eb_mode⟩ ha hb)

theorem RefE.monoG {α β : Type} {G G' : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R : α → β → AState → Prop} (hG : G → G') (h : RefE G' x T a R) : RefE G x T a R := by
  cases x with
  | ok v => exact h
  | error e => exact fun hg => h (hG hg)

/-- `struct_eta_expand` past `k ≠ 0`, given the recursive call's refinement. -/
theorem see_step (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode k d a b ta : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (_ha : HW a) (_hb : HW b) (hta : HW ta) (hk0 : k ≠ 0)
    (hrec : ∀ (s₁ : St) (a₁ : AState) (M₁ : ModeMaps) (a2 b2 t2 : Word),
      SlotPre s₁ a₁ dn vis fe M₁ eb mode → HW a2 → HW b2 → HW t2 → d + 1 ≠ 0 →
      RefE (SetG p n) (seeE p n s₁.mem mode vis (k - 1) (d + 1) a2 b2 t2)
        (structEtaExpand (coreKnot (decMode mode) (decEager mode) fe id F) fe (k - 1).toNat (d + 1).toNat
          (decE a2) (decE b2) (decE t2)) a₁ (CorePost decBool dn s₁.mem vis fe M₁ eb ResH)) :
    RefE (SetG p n) (seeE p (n + 1) s₀.mem mode vis k d a b ta)
      (structEtaExpand (coreKnot (decMode mode) (decEager mode) fe id F) fe k.toNat d.toNat (decE a) (decE b)
        (decE ta)) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hkk : k.toNat = (k - 1).toNat + 1 := by
    have : k.toNat ≠ 0 := fun e => hk0 (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [seeE.eq_2, ite_eq_right hk0, hkk]
  simp only [structEtaExpand]
  rw [decE_tag_forallE_beq _ hta]
  by_cases h6 : tagW ta ≠ 6
  · rw [ite_eq_left h6]
    simp only [h6, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS rfl hw0)
  rw [ite_eq_right h6]
  have h6' : tagW ta = 6 := by simpa using h6
  simp only [h6', decide_true, ↓reduceIte]
  refine RefE.abort0 (by decide) fun hd => ?_
  refine RefE.abort0 (by decide) fun ht => ?_
  refine RefE.abort0 (by decide) fun hi => ?_
  have hvo : viewOK s₀.mem ta FORALL := ⟨ht, by simpa using hi⟩
  obtain ⟨-, hdom, hbody⟩ := view_forall s₀.mem _ hS.arena.base ta hta hvo h6'
  refine RefE.bind_right (by rw [L.Arena.viewBind_run, viewBind_forall s₀.mem _ hS.arena.base ta hta hvo h6']) ?_
  simp only
  refine RefE.bind_callW (fun _ => seeE.k_intern_fvar.none ..)
    (internFVar_coreSpec hq.body n s₀ hS d _ hdom)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  rw [seeE.k_intern_fvar.arm1]
  refine RefE.onlySim (fun _ => seeE.k_mk_app.none ..)
    (fun _ _ h => mkApp_core hq.leaf.core.spine hS₁ a (r₁.headD 0) _ h)
    fun r₂ m₂ h₂ => RefE.bind_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  rw [seeE.k_mk_app.arm1]
  refine RefE.onlySim (fun _ => seeE.k_mk_app_2.none ..)
    (fun _ _ h => mkApp_core hq.leaf.core.spine hS₂ b (r₁.headD 0) _ h)
    fun r₃ m₃ h₃ => RefE.bind_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  rw [seeE.k_mk_app_2.arm1]
  refine RefE.bind_callW (fun _ => seeE.k_inst1.none ..)
    (hc.inst1 n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb _ (r₁.headD 0) 0 hS₃ hbody h₁.resOk)
    fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  rw [seeE.k_inst1.arm1, ← L.toNat_add_one_of_ne _ hd]
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) id rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (hrec ⟨m₄, Locals.init []⟩ _ M₄ _ _ _ ⟨hS₄, hs.mode4, hs.eb_mode⟩ h₂.resOk h₃.resOk h₄.resOk hd)
/-- **`struct_eta_expand` refines `structEtaExpand`, both outcomes** (`k` missing arguments, `ta`
the constructor side's type): the errors are `struct_eta_full`'s. -/
theorem see_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode k d a b ta : Word), n ≤ F → n ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b → HW ta →
    RefE (SetG p n) (seeE p (n + 1) s₀.mem mode vis k d a b ta)
      (structEtaExpand (coreKnot (decMode mode) (decEager mode) fe id F) fe k.toNat d.toNat (decE a) (decE b)
        (decE ta)) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  intro n
  induction n with
  | zero =>
    intro hk F s₀ a₀ dn vis fe M eb mode k d a b ta hF hn hs ha hb hta
    by_cases hk0 : k = 0
    · rw [seeE.eq_2, ite_eq_left hk0]; exact RefE.of_cls0 (e := .outOfFuel) rfl
    exact see_step p hq hc 0 F s₀ a₀ dn vis fe M eb mode k d a b ta hs ha hb hta hk0
      fun _ _ _ _ _ _ _ _ _ _ _ => by rw [seeE.eq_1]; exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N ih =>
    intro hk F s₀ a₀ dn vis fe M eb mode k d a b ta hF hn hs ha hb hta
    by_cases hk0 : k = 0
    · rw [seeE.eq_2, ite_eq_left hk0, show k.toNat = 0 by simp [hk0]]
      exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) id rfl
        (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
        (sef_ref p hq hi hc N (hk.mono (Nat.le_succ N)) F s₀ a₀ dn vis fe M eb mode d a b (by omega)
          (by omega) hs ha hb |>.monoG (fun hG => hG.mono (Nat.le_succ N)) |>.monoG id)
    exact see_step p hq hc (N + 1) F s₀ a₀ dn vis fe M eb mode k d a b ta hs ha hb hta hk0
      fun s₁ a₁ M₁ a2 b2 t2 hs₁ ha2 hb2 ht2 _ =>
        (ih (hk.mono (Nat.le_succ N)) F s₁ a₁ dn vis fe M₁ eb mode (k - 1) (d + 1) a2 b2 t2 (by omega)
          (by omega) hs₁ ha2 hb2 ht2).monoG (fun hG => hG.mono (Nat.le_succ N))

/-- **`struct_eta_cert_partial` refines `structEtaCertPartial`, both outcomes**: the errors are
the `infer_io` and `defeq` slots' and `struct_eta_expand`'s. -/
theorem secp_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d k a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (SetG p n) (secpE p (n + 1) s₀.mem mode vis d k a b)
      (structEtaCertPartial (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat k.toNat (decE a)
        (decE b)) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [secpE]
  unfold structEtaCertPartial
  refine RefE.bind_callW (fun _ => rfl) (ioNeutral_at p hq.leaf n s₀ a₀ dn vis fe M eb b hs.rel hb)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [secpE.k_io_neutral]
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, L.Arena.decBool_false_of h0]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl hw0)
  rw [ite_eq_right h0, L.Arena.decBool_true_of h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F _ _ dn vis fe M₁ eb mode d a hF hn hs₁ ha)
    (fun (hG : SetG p n) => (hG.knot n (Nat.le_refl _)).inferIO F _ _ dn vis fe M₁ eb mode d a hF hn hs₁ ha)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [secpE.k_infer_io]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F _ _ dn vis fe M₂ eb mode d b hF hn hs₂ hb)
    (fun (hG : SetG p n) => (hG.knot n (Nat.le_refl _)).inferIO F _ _ dn vis fe M₂ eb mode d b hF hn hs₂ hb)
    fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [secpE.k_infer_io_2]
  have hs₃ : SlotPre ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hS₃, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.defeq F _ _ dn vis fe M₃ eb mode d _ _ hF hn hs₃ h₃.resOk h₂.resOk)
    (fun (hG : SetG p n) => (hG.knot n (Nat.le_refl _)).defeq F _ _ dn vis fe M₃ eb mode d _ _ hF hn hs₃
      h₃.resOk h₂.resOk)
    fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  dsimp only [secpE.k_defeq]
  by_cases h40 : r₄.headD 0 = 0
  · rw [ite_eq_left h40, L.Arena.decBool_false_of h40]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl hw0)
  rw [ite_eq_right h40, L.Arena.decBool_true_of h40]
  simp only [↓reduceIte]
  cases n with
  | zero => rw [seeE.eq_1]; exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N)) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (see_ref p hq hi hc N (hk.mono (Nat.le_succ N)) F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode k d
      a b _ (by omega) (by omega) ⟨hS₄, hs.mode4, hs.eb_mode⟩ ha hb h₂.resOk)

/-- **`struct_eta_cert`'s partial-constructor arm**, both outcomes: `eta_ctor_partial`, then
`struct_eta_cert_partial` at the missing count. -/
theorem sec_partial (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (m₁ : Mem) (a₁ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M₁ : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode) (ha : HW a) (hb : HW b) :
    RefE (SetG p n) (secE.k_eta_ctor_partial p n mode vis d a b (ecpE p n m₁ vis a))
      (etaCtorPartial fe (decE a) >>= fun x => match x with
        | some k => structEtaCertPartial (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat k
            (decE a) (decE b)
        | none => pure false) a₁
      (CorePost decBool dn m₁ vis fe M₁ eb ResH) := by
  refine RefE.bindE (fun _ => rfl) (fun _ => trivial)
    (ecp_ref p hq (G := True) n m₁ a₁ hs.rel a ha) fun v y a₂ _ hQ => ?_
  obtain ⟨r, m₂⟩ := v
  obtain ⟨⟨M₂, hS₂, hK₂, hSt₂⟩, hy, -⟩ := hQ
  dsimp only at hy hS₂ hSt₂
  dsimp only [secE.k_eta_ctor_partial]
  by_cases h0 : r.headD 0 = 0
  · rw [ite_eq_left h0]
    have : y = none := by rw [hy]; simp only [decOptNat, h0, ↓reduceIte]
    subst this
    exact RefE.ret rfl ⟨⟨M₂, hS₂, hK₂, hSt₂⟩, rfl, hw0⟩
  rw [ite_eq_right h0]
  have : y = some (r.tail.headD 0).toNat := by rw [hy]; simp only [decOptNat, h0, ↓reduceIte]
  subst this
  simp only
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) id rfl
    (fun _ _ _ h => ⟨CoreAfter.comp hK₂ hSt₂ h.after, h.res, h.valid⟩)
    ((secp_ref p hq hi hc N (hk.mono (Nat.le_succ N)) F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d
      (r.tail.headD 0) a b (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb).monoG
        (fun hG => hG.mono (Nat.le_succ N)))

/-- **`struct_eta_cert` refines `structEtaCert`, both outcomes**: the shape gate, then
`struct_eta_full_at`, or the partial constructor's arm. -/
theorem sec_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (SetG p n) (secE p (n + 1) s₀.mem mode vis d a b)
      (structEtaCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  simp only [secE]
  unfold structEtaCert
  refine RefE.bind_callW (fun _ => rfl) (etaCtorShape_at p hq n s₀ a₀ dn vis fe M eb a hs.rel ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [secE.k_eta_ctor_shape]
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_right (by simpa using h0), L.Arena.decBool_false_of h0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact sec_partial p hq hi hc n hk F m₁ _ dn vis fe M₁ eb mode d a b hF hn
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ ha hb
  rw [ite_eq_left (by simpa using h0), L.Arena.decBool_true_of h0]
  simp only [↓reduceIte]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N)) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (sefa_ref p hq hi hc N (hk.mono (Nat.le_succ N)) F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
      a b (by omega) (by omega) ⟨hS₁, hs.mode4, hs.eb_mode⟩ ha hb)

/-- **`struct_eta_cert` refines `structEtaCert`** at the knot (`sec_ref`'s ok half). -/
@[refines ConRon.Arena.structEtaCert]
theorem setCert_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "struct_eta_cert" [mode, vis, d, a, b]
      (structEtaCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (secE_spec p hq.toCertProg (n + 1) s₀ mode vis d a b)
    (sec_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
