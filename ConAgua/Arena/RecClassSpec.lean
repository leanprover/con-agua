import ConAgua.Arena.IndSumSpec
import ConAgua.Arena.RecClass

/-!
# Refinements of `RecClass` (lane `induct`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decNL_succ (m : Mem) (off n : Nat) :
    decNL m off (n + 1) = (do
      let x ← iwN m off
      let xs ← decNL m (off + 1) n
      pure (x :: xs)) := by
  simp only [decNL, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

/-- **A decoding `IW` number slice is an `SlR` slice** of the numbers' words. -/
theorem slR_of_decNL (m : Mem) : ∀ (n off : Nat) (ns : List Nat),
    decNL m off n = some ns → off + n < 2 ^ 64 →
    ∃ ws, SlR m (UInt64.ofNat off) (UInt64.ofNat n) ws ∧ ns = ws.map UInt64.toNat := by
  intro n
  induction n with
  | zero =>
    intro off ns h _
    simp [decNL] at h
    exact ⟨[], by simpa using (SlR.nil (m := m) (o := UInt64.ofNat off)), by simp [h]⟩
  | succ n ih =>
    intro off ns h hb
    rw [decNL_succ] at h
    cases hx : iwN m off with
    | none => simp [hx] at h
    | some x =>
      cases hxs : decNL m (off + 1) n with
      | none => simp [hx, hxs] at h
      | some xs =>
        simp [hx, hxs] at h
        subst h
        obtain ⟨ws, hws, rfl⟩ := ih (off + 1) xs hxs (by omega)
        obtain ⟨e1, -⟩ := iwN_rdW hx (by omega)
        refine ⟨UInt64.ofNat x :: ws, ?_, ?_⟩
        · have e2 : UInt64.ofNat off + 1 = UInt64.ofNat (off + 1) := by simp [UInt64.ofNat_add]
          have e3 : UInt64.ofNat (n + 1) - 1 = UInt64.ofNat n := by simp [UInt64.ofNat_add]
          have hne : UInt64.ofNat (n + 1) ≠ 0 := by
            intro h0; have := congrArg UInt64.toNat h0; simp at this; omega
          rw [← e1]
          exact SlR.cons hne (by rw [e2, e3]; exact hws)
        · have := (iwN_rdW hx (by omega)).2
          simp; omega

/-! ## `class_of_motive_var` -/

theorem findIdx_toNat (ws : List Word) (x : Word) :
    (ws.map UInt64.toNat).findIdx? (· == x.toNat) = ws.findIdx? (· == x) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.findIdx?_cons, beq_iff_eq]
    have : (w.toNat = x.toNat) ↔ w = x := ⟨fun h => UInt64.toNat_inj.mp h, fun h => h ▸ rfl⟩
    by_cases h : w = x
    · simp [h]
    · simp [h, this, ih]

/-- **`class_of_motive_var` refines `classOfMotiveVar`**: `(1, i)` for `some i`, `(0, 0)` for
`none`; memory unchanged. -/
@[refines ConRon.Arena.classOfMotiveVar]
theorem classOfMotiveVar_refines (p : Prog) (hf : p.lookup "sl_find" = some slFind)
    (hp : p.lookup "class_of_motive_var" = some classOfMotiveVar) (n : Nat) (s₀ : St)
    (nP o l pv : Word) (ns : List Nat) (hd : decNL s₀.mem o.toNat l.toNat = some ns)
    (hb : o.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_of_motive_var" [nP, o, l, pv]
    ⦃fun r s' => s'.mem = s₀.mem ∧
      r = match ConRon.Arena.classOfMotiveVar nP.toNat ns pv.toNat with
        | some i => [1, UInt64.ofNat i]
        | none => [0, 0]; ⊤⦄ := by
  obtain ⟨ws, hws, rfl⟩ := slR_of_decNL s₀.mem _ _ _ hd hb
  simp only [UInt64.ofNat_toNat] at hws
  have hlen : ws.length < 2 ^ 64 := by
    have := decNL_length s₀.mem hd; simp at this; omega
  have key : ∀ r, findW n s₀.mem o l (pv - nP) = some r → nP ≤ pv →
      r = match ConRon.Arena.classOfMotiveVar nP.toNat (ws.map UInt64.toNat) pv.toNat with
        | some i => [1, UInt64.ofNat i]
        | none => [0, 0] := by
    intro r hr hle
    have hle' : nP.toNat ≤ pv.toNat := UInt64.le_iff_toNat_le.mp hle
    have hsub : (pv - nP).toNat = pv.toNat - nP.toNat := UInt64.toNat_sub_of_le _ _ hle
    rw [findW_ok n _ _ _ _ _ _ hws hr hlen]
    simp only [ConRon.Arena.classOfMotiveVar, hle', if_true, ← hsub, findIdx_toNat]
    cases List.findIdx? (fun x => x == pv - nP) ws <;> rfl
  have key2 : pv < nP →
      ConRon.Arena.classOfMotiveVar nP.toNat (ws.map UInt64.toNat) pv.toNat = none := by
    intro h
    have : ¬ nP.toNat ≤ pv.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; omega
    simp [ConRon.Arena.classOfMotiveVar, this]
  rw [invoke_eq _ hp]
  simp only [callFn, classOfMotiveVar]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, slFind_spec p hf n] <;>
    finish

end L.Ind
