import ConAgua.Arena.RecSim
import ConAgua.Arena.RecClassSpec
import ConAgua.Arena.IndInstallSpec

/-!
# Stable decodings (lane `indproofs2`, helper `rec`)

`StabD f m x`: the decoding `f` gives `x` at `m` and at every memory the pool grows to. A record
built below the pool's top decodes stably; a stable decoding stays stable as the pool grows
(`StabD.grow`), so a decoded argument is carried across every callee by `IWGrow` alone.

`SPL dec m o l xs`: the `IW` pointer slice `(o, l)` lies below the top and its pointers decode
stably to `xs` (each by `dec`); `SPL.decPL` gives the `decPL`, `SPL.cons` is `sl_cons` on it.
-/

open ConRon.Arena
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **A stable decoding**: `f` gives `x` at `m` and at every memory `m` grows to. -/
def StabD {α : Type} (f : Mem → Option α) (m : Mem) (x : α) : Prop :=
  ∀ m', IWGrow m m' → f m' = some x

namespace StabD
variable {α : Type} {f : Mem → Option α} {m m' : Mem} {x : α}

theorem get (h : StabD f m x) : f m = some x := h m (IWGrow.refl m)

theorem grow (h : StabD f m x) (hg : IWGrow m m') : StabD f m' x :=
  fun m'' hg' => h m'' (hg.trans hg')

theorem of_eq (h : ∀ m', IWGrow m m' → f m' = f m) (hf : f m = some x) : StabD f m x :=
  fun m' hg => (h m' hg).trans hf

end StabD

theorem iwN_grow {m m' : Mem} (hg : IWGrow m m') {i : Nat} (hi : i < iwTop m) : iwN m' i = iwN m i := by
  simp only [iwN, nat?, iwA]; rw [hg.2.2.1 i hi]

theorem iwH_grow {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {i : Nat} (hi : i < iwTop m) :
    (iwH m' i : Option (Idx k)) = iwH m i := by
  simp only [iwH, hd?, iwA]; rw [hg.2.2.1 i hi]

/-! ## Stable pointer slices -/

/-- Two lists related elementwise. -/
inductive FA2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : FA2 R [] []
  | cons {a b as bs} : R a b → FA2 R as bs → FA2 R (a :: as) (b :: bs)

theorem FA2.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, FA2 R as bs → FA2 S as bs
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h _ _ h1) (FA2.imp h h2)

theorem FA2.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, FA2 R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h2 => by simp [FA2.length_eq h2]

/-- **A stable pointer slice**: below the top, every pointer decoding stably by `dec`. -/
def SPL {α : Type} (dec : Mem → Nat → Option α) (m : Mem) (o l : Nat) (xs : List α) : Prop :=
  o + l ≤ iwTop m ∧ ∃ ps, decNL m o l = some ps ∧
    FA2 (fun q x => StabD (fun m => dec m q) m x) ps xs

namespace SPL
variable {α : Type} {dec : Mem → Nat → Option α} {m m' : Mem} {o l : Nat} {xs : List α}

theorem nil (o : Nat) (ho : o ≤ iwTop m) : SPL dec m o 0 [] :=
  ⟨by omega, [], by simp [decNL], FA2.nil⟩

theorem grow (h : SPL dec m o l xs) (hg : IWGrow m m') : SPL dec m' o l xs := by
  obtain ⟨hb, ps, hps, hf⟩ := h
  refine ⟨Nat.le_trans hb hg.1, ps, by rw [decNL_grow hg hb]; exact hps, ?_⟩
  exact FA2.imp (fun _ _ hq => hq.grow hg) hf

theorem mapM_of_forall₂ : ∀ {ps : List Nat} {xs : List α},
    FA2 (fun q x => StabD (fun m => dec m q) m x) ps xs → ps.mapM (dec m) = some xs
  | [], [], _ => rfl
  | q :: ps, x :: xs, .cons h1 h2 => by
    simp only [List.mapM_cons, h1.get, mapM_of_forall₂ h2]; rfl

theorem decPL (h : SPL dec m o l xs) : L.Ind.decPL m (dec m) o l = some xs := by
  obtain ⟨-, ps, hps, hf⟩ := h
  rw [decPL_eq_bind, hps]; exact mapM_of_forall₂ hf

theorem length (h : SPL dec m o l xs) : xs.length = l := by
  obtain ⟨-, ps, hps, hf⟩ := h
  rw [← hf.length_eq, decNL_length m hps]

theorem stab (h : SPL dec m o l xs) : StabD (fun m => L.Ind.decPL m (dec m) o l) m xs :=
  fun _ hg => (h.grow hg).decPL

/-- `sl_cons` of a stably decoding pointer onto a stable slice. -/
theorem cons {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {x o l : Word} {r : List Word} {y : α} (h : consW n m x o l = some (r, m'))
    (hS : StageR dn vis fe m a) (hl : SPL dec m o.toNat l.toNat xs)
    (hy : StabD (fun m => dec m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      SPL dec m' (r.headD 0).toNat (r.tail.headD 0).toNat (y :: xs) := by
  obtain ⟨hb, ps, hps, hf⟩ := hl
  obtain ⟨hS', hg, hdn, htop⟩ := consW_stageN h hS hb hps
  refine ⟨hS', hg, by omega, x.toNat :: ps, hdn, FA2.cons (hy.grow hg) ?_⟩
  exact FA2.imp (fun _ _ hq => hq.grow hg) hf

end SPL

end L.Ind
