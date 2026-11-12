module

public import ConAgua.Arena.DefEqStuckGo
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.IndView
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConRon.Bridge.Grind
import ConAgua.L.WordOff

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


/-- A step that only pushed (twin unchanged) in front of a run that grew the stack. -/
theorem growRef_preG {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (hg : StackGrew m₀ m₁)
    (h : GrowRef T a₀ dec dn m₁ vis fe M eb r m ok) : GrowRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, ⟨M'', hS'', hK'', hSt''⟩, hres, hr⟩ := h
  exact ⟨hok, ⟨M'', hS'', hK'', hg.trans hSt''⟩, hres, hr⟩

/-! ## `struct_eta_cert_with` -/

/-- The top put back, then the verdict `v` (a model step of `stuck_app_cong`, `DefEqStuckApp.lean`). -/
def swRet (top v : Word) (m : Mem) : Option (Word × Mem) :=
  if (136 : Word).toNat < (m.arr64 CTL).size then some (v, m.set64 CTL 136 top) else none

section withRuns
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b wtb : EIdx) (st : AState) (hh : EIdx)
  (hgaf : (getAppFn coreWalkFuel a).run st = .ok (hh, st))

include hgaf

theorem setWith_nonconst (ht : (hh.tag == ETag.const) = false) :
    (structEtaCertWith r fe depth a b wtb).run st = .ok (false, st) := by
  sorry

theorem setWith_other (c : NIdx) (us : LsIdx) (ht : (hh.tag == ETag.const) = true)
    (hv : st.store.view hh = some (.const c us))
    (hf : ∀ cv np nf, fe.find? c ≠ some (.ctorInfo cv np nf)) :
    (structEtaCertWith r fe depth a b wtb).run st = .ok (false, st) := by
  sorry

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
  sorry

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
