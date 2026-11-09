module

public import ConAgua.Arena.IndMemoFns
import ConAgua.Arena.IndRealCrFKeep
public import ConAgua.Arena.ConstsResolveFRefine2
public import ConAgua.Arena.IndRealCrF

@[expose] public section

/-!
# `consts_resolve_ffast`'s walk memo across the checker's calls (lane `indproofs4`, helper `sw2`)

`consts_resolve_ffast`'s memo (`L.Stubs.CrOK`: array 155, `CTL[158]`) is written by that function
only, which keeps it well formed (`crfF_keepsCrOK`). So a writer outside those words keeps it
(`CrOK.frame`), and so does every call of a function of `imFns` in a program with
`IndMemoClosed` (`invoke_crOK`, `callW_crOK`: `imFns`' write set with `consts_resolve_ffast` a
trusted leaf). This is what the `StageT` callers of `consts_resolve_ffast` (the value guards, the
pin gates) thread to its real refinement `crfF_okT`, whose pre has the memo (`CrMemo = CrOK`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-- **`CrOK` across a writer outside `CRM` and `CTL[158]`.** -/
theorem CrOK.frame {A : List TieredArray} {C : List Word} {m m' : Mem} (h : L.Stubs.CrOK m)
    (hf : MemFrame A C m m') (hA : (L.Stubs.CRM : TieredArray) ∉ A) (hC : (158 : Word) ∉ C) : L.Stubs.CrOK m' :=
  let ⟨mp, hm⟩ := h
  ⟨mp, memoRV_frame (S := L.Stubs.crSch) (hS := L.Stubs.crSch_wf) (K := bmKey) (VR := L.Stubs.CrV)
    A C hA hC m m' hf (fun _ _ h => h) mp hm⟩

/-- **The frame relation of `IndMemoClosed` for `CrOK` alone.** -/
theorem crOK_wframe : WFrame CTL imA imC (fun m₀ m => L.Stubs.CrOK m₀ → L.Stubs.CrOK m) where
  refl _ h := h
  st64 m₀ m a i v h ha h0 := by
    rcases ha with ⟨hc, ha⟩ | ⟨rfl, hi⟩
    · exact CrOK.frame (h h0) (MemFrame.set64 m a hc i v)
        (fun hb => by simp at hb; subst hb; exact (imA_spec _ ha).2.1 rfl) (by simp)
    · exact CrOK.frame (h h0) (MemFrame.setCtl m i v) (by simp)
        (fun hx => by simp at hx; subst hx; exact (imC_spec _ hi).2.1 rfl)
  setG _ _ _ _ h h0 := CrOK.frame (h h0) (A := []) (C := [])
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩ (by simp) (by simp)

/-- **The leaves of `imFns` keep `CrOK`** (`consts_resolve_ffast` keeps its memo,
`struct_used_later` does not write it; their refinements prove it). -/
def CrLeaves (p : Prog) : Prop :=
  ∀ g ∈ imLeaves, ∀ n m₀ vs, ⦃fun s => L.Stubs.CrOK m₀ → L.Stubs.CrOK s.mem⦄
    invoke p (exec p n) g vs ⦃fun _ s => L.Stubs.CrOK m₀ → L.Stubs.CrOK s.mem; ⊤⦄

/-- **A call of a function of `imFns` keeps `CrOK`.** -/
theorem invoke_crOK {p : Prog} (hcl : IndMemoClosed p) (hl : CrLeaves p) (n : Nat)
    {f : FnName} (hf : f ∈ imFns) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun _ s => L.Stubs.CrOK s₀.mem → L.Stubs.CrOK s.mem; ⊤⦄ :=
  invoke_frameL p hcl crOK_wframe hl n f hf vs s₀

/-- The same through `callW`. -/
theorem callW_crOK {p : Prog} (hcl : IndMemoClosed p) (hl : CrLeaves p) {n : Nat}
    {f : FnName} (hf : f ∈ imFns) {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n f vs m = some (r, m')) (hI : L.Stubs.CrOK m) : L.Stubs.CrOK m' := by
  obtain ⟨s', hs', h⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (invoke_crOK hcl hl n hf vs _) hc
  exact hs' ▸ h hI

/-- **The program bundle of the `CrOK` threading**: `imFns`' write set and its leaves. -/
structure CrKeep (p : Prog) : Prop where
  closed : IndMemoClosed p
  leaves : CrLeaves p

/-- `CrOK` across a program call of a function of `imFns`. -/
theorem CrKeep.call {p : Prog} (hk : CrKeep p) {n : Nat} {f : FnName} (hf : f ∈ imFns)
    {vs : List Word} {m m' : Mem} {r : List Word} (hc : callW p n f vs m = some (r, m'))
    (hI : L.Stubs.CrOK m) : L.Stubs.CrOK m' :=
  callW_crOK hk.closed hk.leaves hf hc hI

end L.Arena
