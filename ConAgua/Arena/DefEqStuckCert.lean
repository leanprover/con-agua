module

public import ConAgua.Arena.DefEqStuckGo
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Arena.IndView
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConRon.Bridge.Grind

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

theorem erecP_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (EREC : TieredArray) ∉ A) (hC : (129 : Word) ∉ C) : erecP m' = erecP m := by
  sorry

/-- The kind word of a decoded record says whether it is an inductive. -/
theorem decCI_indK {a b : Array Word} {q : Word}
    {ci : IConstantInfo} (h : decCI (aread a) q.toNat = some ci) (hab : ArrExt (aread a) (aread b))
    (hsz : b.size < 2 ^ 63) :
    (rdW b q = 3 → ∃ cv caps, ci = .indInfo cv caps) ∧
    (rdW b q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  sorry

/-! ## The twin, after the constructor's spine -/

/-- **`structEtaCertWith` past the constructor's spine**, copied. -/
def setWtbT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (aargs : List EIdx) (wtb : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel wtb
  if hh.tag == ETag.const then
    view hh >>= fun v => match v with
      | .const T us' =>
        match fe.find? T with
        | some (.indInfo cvT caps) => do
          let targs ← getAppArgs coreWalkFuel wtb
          setGoT r fe depth b c us cvc T us' cvT caps aargs targs
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

theorem setWtbT_ind (T : NIdx) (us' : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : a.store.view hh = some (.const T us')) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (targs : List EIdx)
    (hargs : (getAppArgs coreWalkFuel wtb).run a = .ok (targs, a)) :
    (setWtbT r fe depth b c us cvc aargs wtb).run a =
      (setGoT r fe depth b c us cvc T us' cvT caps aargs targs).run a := by
  simp only [setWtbT, StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv, hf,
    hargs]

end wtbRuns

/-- A step that only pushed (twin unchanged) in front of a run that grew the stack. -/
theorem growRef_preG {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (hg : StackGrew m₀ m₁)
    (h : GrowRef T a₀ dec dn m₁ vis fe M eb r m ok) : GrowRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, ⟨M'', hS'', hK'', hSt''⟩, hres, hr⟩ := h
  exact ⟨hok, ⟨M'', hS'', hK'', hg.trans hSt''⟩, hres, hr⟩

theorem addW_toNat {x y : Word} (h : x.toNat + y.toNat < 2 ^ 64) : (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

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
    (hcvc : decCI (erecP s₀.mem) pc.toNat = some (.ctorInfo cvc np nf))
    (ha : SpineR s₀.mem ao an aargs) (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (SetG p n) (secwtbE p (n + 1) s₀.mem mode vis d b us c pc ao an wtb)
      (setWtbT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc
        aargs.toList (decE wtb)) a₀ (GrowPost decBool dn s₀.mem vis fe M eb ResH) := by
  sorry

/-! ## `struct_eta_cert_with` -/

theorem structEtaCertWith_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b wtb : EIdx) :
    structEtaCertWith r fe depth a b wtb = (do
      let hh ← getAppFn coreWalkFuel a
      if hh.tag == ETag.const then
        view hh >>= fun v => match v with
          | .const c us =>
            match fe.find? c with
            | some (.ctorInfo cvc cnP cnF) => do
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
    (hf : ∀ cv np nf, fe.find? c ≠ some (.ctorInfo cv np nf)) :
    (structEtaCertWith r fe depth a b wtb).run st = .ok (false, st) := by
  rw [structEtaCertWith_eq]
  simp only [StateT.run_bind, hgaf, except_ok_bind, ht, ↓reduceIte, view_run _ _ _ hv]
  rcases hc : fe.find? c with _ | ⟨_ | _ | _ | _ | ⟨cv, np, nf⟩ | _ | _⟩ <;> try rfl
  all_goals exact absurd hc (hf cv np nf)

theorem setWith_ctor (c : NIdx) (us : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const c us)) (cvc : IConstantVal) (np nf : Nat)
    (hf : fe.find? c = some (.ctorInfo cvc np nf)) (aargs : List EIdx)
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
  sorry

theorem etaCtorShape_at (p : Prog) (hq : StuckProg p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
      (fe : IFEnv) (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
      CoreSpec p n "eta_ctor_shape" [vis, e] (etaCtorShape fe (decE e)) decBool s₀ a₀ dn vis fe MM eb
  | 0, s₀, a₀, dn, vis, fe, MM, eb, _, _, _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | n + 1, s₀, a₀, dn, vis, fe, MM, eb, e, hS, he =>
      etaCtorShape_refines p hq n s₀ a₀ dn vis fe MM eb e hS he

/-! ## `struct_eta_cert` -/

/-- **`struct_eta_cert` refines `structEtaCert`, both outcomes**: the errors are the `infer_io`,
`whnf` slots' and `struct_eta_cert_with`'s. -/
theorem sec_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (SetG p n) (secE p (n + 1) s₀.mem mode vis d a b)
      (structEtaCert (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  simp only [secE]
  unfold structEtaCert
  refine RefE.bind_callW (fun _ => rfl) (etaCtorShape_at p hq n s₀ a₀ dn vis fe M eb a hs.rel ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [secE.k_eta_ctor_shape]
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, decBool_false_of h0]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl hw0)
  rw [ite_eq_right h0, decBool_true_of h0]
  simp only [↓reduceIte]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.inferIO F _ _ dn vis fe M₁ eb mode d b hF hn hs₁ hb)
    (fun (hG : SetG p n) => (hG.knot n (Nat.le_refl _)).inferIO F _ _ dn vis fe M₁ eb mode d b hF hn hs₁ hb)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [secE.k_infer_io]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hK.whnf F _ _ dn vis fe M₂ eb mode d _ hF hn hs₂ h₂.resOk)
    (fun (hG : SetG p n) => (hG.knot n (Nat.le_refl _)).whnf F _ _ dn vis fe M₂ eb mode d _ hF hn hs₂
      h₂.resOk)
    fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [secE.k_whnf]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ N)) rfl
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (secw_ref p hq hi hc N (hk.mono (Nat.le_succ N)) F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d
      a b (r₃.headD 0) (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb h₃.resOk)

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
  RefE.coreSpec (secE_spec p hq.setCert hq.setWith hq.setWtb hq.setGo hq.setTail (n + 1) s₀ mode vis
    d a b) (sec_ref p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
