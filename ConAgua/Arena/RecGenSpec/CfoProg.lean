import ConAgua.Arena.IndPosSpec.NoConstWf
import ConAgua.Arena.RecStab
import ConAgua.Arena.RecSim

/-!
# CfoProg

`rec2NoMR_ftd`, `rec2NoMR_iw`, `cfgK6`, `CfoProg`, `rec2SimNestOcc`, `AgreeA` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `noMR` across the callees -/

theorem rec2NoMR_ftd {m m' : Mem} {args r : List Word} {mp : Std.HashMap EIdx Bool}
    (h : ftdF m args = some (r, m')) (hM : noMR m mp) : noMR m' mp :=
  memoRG_frame noSch noSch_wf bmKey _ [] [] (by simp) (by simp) m m' (ftdF_frame h) mp hM

theorem rec2NoMR_iw {m m' : Mem} {mp : Std.HashMap EIdx Bool} (hf : MemFrame [IW] [200] m m')
    (hM : noMR m mp) : noMR m' mp :=
  memoRG_frame noSch noSch_wf bmKey _ [IW] [200] (by decide) (by decide) m m' hf mp hM

/-! ## `class_fields_of_go`: the model -/

/-- After the cons. -/
def cfgK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

/-- The lookups `class_fields_of` needs. -/
structure CfoProg (p : Prog) : Prop where
  no : NoLook p
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  r3 : p.lookup "rec3" = some rec3
  pb : p.lookup "pi_binders" = some piBinders
  hits : p.lookup "class_fields_of_hits" = some classFieldsOfHits
  mnc : p.lookup "member_names_copy" = some memberNamesCopy
  mn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  go : p.lookup "class_fields_of_go" = some classFieldsOfGo
  cfo : p.lookup "class_fields_of" = some classFieldsOfL
  ftd : FtdF p

/-! ## `class_fields_of_go` refines `classFieldsOf` -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

/-- `nest_occ` as a simulation: the twin keeps its state, the memo relation is reset to `∅`. -/
theorem rec2SimNestOcc (hS : StageR dn vis fe m a) {no nl e : Word} {names : List NIdx} (hh : H e)
    (hn : decHL m no.toNat nl.toNat = some names) (hnb : no.toNat + nl.toNat < 2 ^ 64)
    {mp0 : Std.HashMap EIdx Bool} (hM : noMR m mp0) (k : Nat) :
    RSim (noConstWf k m no nl 0 0 e) (ConRon.Arena.nestOcc names 0 0 (decI e)) a
      (fun b a' x => a' = a ∧ (b.1 != 0) = x ∧ noMR b.2 ∅ ∧ StageR dn vis fe b.2 a ∧ IWGrow m b.2 ∧
        MFr [NOM] [204, 205] m b.2) := by
  rintro ⟨r, m'⟩ h
  obtain ⟨x, hrun, hx, hM', hS', hg, hf⟩ := noConstWf_ok k dn fe vis m m' a no nl 0 0 e r names mp0 h hS hh
    hn hnb hM
  exact ⟨x, a, by simpa [decE_eq] using hrun, rfl, hx, hM', hS', hg, hf⟩

end sims

/-! ## Decodings stable above a bound (lane `indproofs4`, helper `cls`)

A result written into a slot of a slice allocated before it was computed is a write below the top,
which `IWGrow` does not allow; what is created after the allocation reads only words above the
slots. `AgreeA b m m'`: the pools grew and every word from `b` to the old top stayed;
`StabA b f m x`: `f` decodes `x` in every such memory (and so stably, `StabA.stabD`). -/

/-- The pools grew, keeping every word from `b` to the old top. -/
def AgreeA (b : Nat) (m m' : Mem) : Prop :=
  iwTop m ≤ iwTop m' ∧ erTop m ≤ erTop m' ∧
    (∀ i, b ≤ i → i < iwTop m → (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?) ∧
    (∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?)

theorem AgreeA.of_grow {b : Nat} {m m' : Mem} (h : IWGrow m m') : AgreeA b m m' :=
  ⟨h.1, h.2.1, fun i _ hi => h.2.2.1 i hi, h.2.2.2⟩

theorem AgreeA.trans {b : Nat} {m₁ m₂ m₃ : Mem} (h₁ : AgreeA b m₁ m₂) (h₂ : AgreeA b m₂ m₃) :
    AgreeA b m₁ m₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2.1 h₂.2.1,
    fun i hb hi => (h₂.2.2.1 i hb (Nat.lt_of_lt_of_le hi h₁.1)).trans (h₁.2.2.1 i hb hi),
    fun i hi => (h₂.2.2.2 i (Nat.lt_of_lt_of_le hi h₁.2.1)).trans (h₁.2.2.2 i hi)⟩

theorem AgreeA.iwN {b : Nat} {m m' : Mem} (h : AgreeA b m m') {i : Nat} (hb : b ≤ i) (hi : i < iwTop m) :
    iwN m' i = iwN m i := by
  simp only [L.Ind.iwN, nat?, iwA]; rw [h.2.2.1 i hb hi]

/-- `f` decodes `x` in every memory agreeing with `m` from `b` on. -/
def StabA {α : Type} (b : Nat) (f : Mem → Option α) (m : Mem) (x : α) : Prop :=
  ∀ m', AgreeA b m m' → f m' = some x

/-- **A pointer slice stable above `b`**: empty, or from `b` on below the top, every pointer
decoding stably above `b`. -/
def SPLA {α : Type} (b : Nat) (dec : Mem → Nat → Option α) (m : Mem) (o l : Nat) (xs : List α) : Prop :=
  (l = 0 ∨ b ≤ o) ∧ o + l ≤ iwTop m ∧ ∃ ps, decNL m o l = some ps ∧
    FA2 (fun q x => StabA b (fun m => dec m q) m x) ps xs

namespace SPLA
variable {α : Type} {b : Nat} {dec : Mem → Nat → Option α} {m m' : Mem} {o l : Nat} {xs : List α}

theorem decNL_agree (h : SPLA b dec m o l xs) (hA : AgreeA b m m') : decNL m' o l = decNL m o l := by
  rcases h.1 with h0 | hb
  · subst h0; rfl
  simp only [decNL]
  apply mapM_opt_congr
  intro j hj
  have := List.mem_range.mp hj
  exact hA.iwN (by omega) (by have := h.2.1; omega)

theorem mapM_of_forall₂ {m' : Mem} : ∀ {ps : List Nat} {xs : List α},
    FA2 (fun q x => dec m' q = some x) ps xs → ps.mapM (dec m') = some xs
  | [], [], _ => rfl
  | q :: ps, x :: xs, .cons h1 h2 => by
    simp only [List.mapM_cons, h1, mapM_of_forall₂ h2]; rfl

/-- The whole slice decodes stably above `b`. -/
theorem stab (h : SPLA b dec m o l xs) : StabA b (fun m => decPL m (dec m) o l) m xs := by
  intro m' hA
  obtain ⟨h1, h2, ps, hps, hf⟩ := h
  show decPL m' (dec m') o l = some xs
  rw [decPL_eq_bind, decNL_agree ⟨h1, h2, ps, hps, hf⟩ hA, hps]
  exact mapM_of_forall₂ (FA2.imp (fun _ _ hq => hq m' hA) hf)

end SPLA

end L.Ind

end
