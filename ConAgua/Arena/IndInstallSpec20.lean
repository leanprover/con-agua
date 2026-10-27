import ConAgua.Arena.IndPartsSpec8
import ConAgua.Arena.IndSumSpec.SumProg
import ConAgua.Arena.RecClassSpec.MjProg

/-!
# Refinements of `IndInstall`, part 20 (lane `indproofs2`, helper `install`): `checkAbsCtorSorts`,
`checkAbsCtorSortsAll`, the relation

Per constructor: the level parameters' check (`all_level_params_defined`'s stub), `NestCtx.hiAt`
(`nest_ctx_hi_at`, helper `pos`'s), the fields opened above the holes (`open_pis_at_fvars_f`'s
stub) and their sorts (`check_struct_field_sorts_i`, `installSimFsorts`).
-/

noncomputable section


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- One constructor's fields' universes, as the twin computes them after its level check. -/
def absOneAM (fe : IFEnv) (ctx : NestCtx) (b : Bool) (nF : Nat) (tyN : EIdx) : AM Unit := do
  let xq ← unwrapOr (← openPisAtFvarsF nF tyN (ctx.hiAt 0))
    (.internal "direct rec: abstracted constructor fields")
  let _ ← checkStructFieldSortsI V fe b false ctx.sort (ctx.hiAt 0) xq.1 [] nF
  pure ()

/-- A context word decoded below the tops. -/
theorem installCtxWord9 {m : Mem} {ctx : Word} {c : NestCtx}
    (hc : DecB (fun m => decCtx m ctx.toNat) m c) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (ctx + 9)) ∧ decI (rdW (m.arr64 IW) (ctx + 9)) = c.sort := by
  have hcT : decCtx (truncM m) ctx.toNat = some c := hc
  obtain ⟨-, -, -, -, -, h9, -⟩ := decCtx_some hcT
  obtain ⟨-, h9'⟩ := rec2IwH_trunc h9
  obtain ⟨v, hv, hv32, hve⟩ := iwH_rdW_at (w := ctx) (k := 9) h9' hsz
  rw [show (UInt64.ofNat 9 : Word) = 9 from rfl] at hv
  rw [hv]; exact ⟨hv32, hve⟩

/-- A pointer slice decoded below the tops, below the top unless empty (an empty slice's offset is
whatever its record holds). -/
def PSlR0 {α : Type} (f : Mem → Nat → Option α) (xs : List α) (o l : Word) (m : Mem) : Prop :=
  DecB (fun m => decPL m (f m) o.toNat l.toNat) m xs ∧ (l = 0 ∨ o.toNat + l.toNat ≤ iwTop m)

theorem PSlR0.grow {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {xs : List α} {o l : Word} {m m' : Mem} (h : PSlR0 f xs o l m) (hg : IWGrow m m') : PSlR0 f xs o l m' :=
  ⟨h.1.grow (OMono.decPL hf _ _) hg, h.2.imp id fun h2 => Nat.le_trans h2 hg.1⟩

theorem PSlR0.nil {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR0 f xs o l m) (hl : l = 0) : xs = [] := by
  have h1 := h.1; simp only [DecB, hl] at h1
  simpa [decPL] using h1.symm

theorem PSlR0.pslr {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR0 f xs o l m) (hl : l ≠ 0) : PSlR f xs o l m := ⟨h.1, h.2.resolve_left hl⟩

/-- The lookups of the fields' universes at the holes. -/
structure AbsProg (p : Prog) : Prop where
  hiAt : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  one : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne
  abs : p.lookup "check_abs_ctor_sorts" = some checkAbsCtorSorts
  all : p.lookup "check_abs_ctor_sorts_all" = some checkAbsCtorSortsAll
  sum : SumProg p

/-! ## `check_abs_ctor_sorts_all` -/

/-- A member's normal forms: a pointer to `[off, len]` of `[k.off, k.len, e]` pointers. -/
def decKES (m : Mem) (q : Nat) : Option (List (List NestFieldKind × EIdx)) :=
  decAt m (fun o l => decPL m (decKE m) o l) q

end L.Ind
