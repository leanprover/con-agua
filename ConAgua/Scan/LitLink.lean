module

public import ConAgua.Scan.Lit
import ConAgua.Census.Attr
public import ConLeche.Frontend.Scan.Naive
public import ConAgua.Scan.Link
public import ConLeche.Frontend.Scan.Equiv.Scalars
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# `match_lit`/`scan_bool` against con-leche's `matchLit`/`scanBool`

`matchLitN` (Rust's loop, with `byte_at`) is a prefix test, as con-leche's `matchLit` is
(`ConLeche.Frontend.matchLit_eq`), as long as the literal has no `0` byte: past the end of the
input `byte_at` reads `0`, which no literal byte matches. `scanBool_run` composes this with the
L spec (`L.Scan.Lit.scanBool_spec`): whenever the L program returns, it returns con-leche's
`scanBool b i`, encoded as three words.
-/

namespace ConAgua.Scan

open ConLeche.Frontend L L.Scan.Lit

theorem matchLitN_eq_isPrefixOf (b : Array UInt8) (i : Nat) (L : List UInt8) (o n k : Nat)
    (hL : o + n ≤ L.length) (h0 : ∀ j (h : j < L.length), L[j] ≠ 0) :
    matchLitN b i L o n k = ((L.drop (o + k)).take (n - k)).isPrefixOf (b.toList.drop (i + k)) := by
  fun_induction matchLitN b i L o n k with
  | case1 k hk h ih =>
    rw [ih, show n - k = (n - (k + 1)) + 1 by omega,
      List.drop_eq_getElem_cons (show o + k < L.length by omega), List.take_succ_cons,
      show o + (k + 1) = o + k + 1 by omega, show i + (k + 1) = i + k + 1 by omega]
    have hb : i + k < b.size := by
      refine Classical.byContradiction fun hb => ?_
      simp only [byteAtN, Array.getD, show ¬ i + k < b.size from hb, dite_false] at h
      exact h0 (o + k) (by omega) (by simpa [show o + k < L.length by omega] using h.symm)
    rw [List.drop_eq_getElem_cons (l := b.toList) (i := i + k) (by simpa using hb), List.isPrefixOf_cons_cons]
    simp only [byteAtN, Array.getD, hb, dite_true, show o + k < L.length by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some] at h
    have h' : b[i + k] = L[o + k] := h
    simp [h']
  | case2 k hk h =>
    rw [show n - k = (n - (k + 1)) + 1 by omega,
      List.drop_eq_getElem_cons (show o + k < L.length by omega), List.take_succ_cons]
    by_cases hb : i + k < b.size
    · rw [List.drop_eq_getElem_cons (l := b.toList) (i := i + k) (by simpa using hb), List.isPrefixOf_cons_cons]
      simp only [byteAtN, Array.getD, hb, dite_true, show o + k < L.length by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some] at h
      have h' : b[i + k] ≠ L[o + k] := h
      simp [Ne.symm h']
    · rw [List.drop_eq_nil_of_le (show b.toList.length ≤ i + k by simp; omega)]
      rfl
  | case3 k hk =>
    rw [show n - k = 0 by omega]
    simp

theorem LITS_ne_zero : ∀ j (h : j < LITS.length), LITS[j] ≠ 0 := by decide

theorem lit_true : (LITS.drop 0).take 4 = lit "true" := by rw [lit_eq_toByteArray]; rfl
theorem lit_false : (LITS.drop 4).take 5 = lit "false" := by rw [lit_eq_toByteArray]; rfl

@[refines ConLeche.Frontend.matchLit]
theorem matchLit_eq_N (b : ByteArray) (i : USize) (hsize : b.size < USize.size) (s : String)
    (o n : Nat) (hs : (LITS.drop o).take n = lit s) (hL : o + n ≤ LITS.length)
    (hlen : s.toUTF8.size < USize.size) :
    matchLit b i s.toUTF8 0 = matchLitN b.data i.toNat LITS o n 0 := by
  rw [matchLit_lit b i s hlen, matchLitN_eq_isPrefixOf _ _ _ _ _ _ hL LITS_ne_zero, ← hs]
  simp [tailAt, bytes_eq_of_size_lt hsize]

/-- con-leche's `scanBool`, through the model. -/
theorem scanBool_eq_N (b : ByteArray) (i : USize) (hsize : b.size < USize.size) :
    ConLeche.Frontend.scanBool b i = match scanBoolN b.data i.toNat with
      | some (v, _) => .ok v (i + if v then 4 else 5)
      | none => .err ⟨i.toNat, .expectedBool⟩ := by
  unfold ConLeche.Frontend.scanBool scanBoolN
  rw [matchLit_eq_N b i hsize "true" 0 4 lit_true (by decide) (size_toUTF8_lt "true" 4 rfl (by decide)),
    matchLit_eq_N b i hsize "false" 4 5 lit_false (by decide) (size_toUTF8_lt "false" 5 rfl (by decide))]
  by_cases h1 : matchLitN b.data i.toNat LITS 0 4 0 <;> by_cases h2 : matchLitN b.data i.toNat LITS 4 5 0 <;>
    simp [h1, h2]

/-- `ScanRes Bool` as the three words `scan_bool` returns. -/
def encScan : ScanRes Bool → List Word
  | .ok v p => [1, if v then 1 else 0, p.toUInt64]
  | .err e => [0, 0, UInt64.ofNat e.offset]

/-- Partial correctness of the whole program: whenever `run` returns, it returns con-leche's
`scanBool b i`, and the memory is unchanged. -/
@[refines ConLeche.Frontend.scanBool]
theorem scanBool_run (b : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 64)
    (fuel : Nat) (i : USize) (hi : i.toNat + 5 < 2 ^ 64) (r : List Word) (m' : Mem)
    (h : run litProg fuel "scan_bool" [i.toUInt64] { bytes := #[b.data] } = .ok (r, m')) :
    r = encScan (ConLeche.Frontend.scanBool b i) ∧ m' = { bytes := #[b.data] } := by
  have hU := usize_size_eq64 h64
  simp only [run] at h
  cases hr : (invoke litProg (exec litProg fuel) "scan_bool" [i.toUInt64]).run
      { mem := { bytes := #[b.data] }, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok rs =>
    simp only [hr, Except.map] at h
    injection h with h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have := M.of_run (P := fun s => s = { mem := { bytes := #[b.data] }, loc := Locals.init [] }) rfl hr
      (scanBool_spec litProg rfl rfl b.data hb fuel _ rfl i.toUInt64 (by simpa using hi))
    refine ⟨?_, this.1 ▸ rfl⟩
    rw [this.2, scanBool_eq_N b i (by omega)]
    simp only [USize.toNat_toUInt64]
    cases hs : scanBoolN b.data i.toNat with
    | none => simp [encBool, encScan]
    | some vp =>
      obtain ⟨v, p⟩ := vp
      have hp : p = i.toNat + if v then 4 else 5 := by
        unfold scanBoolN at hs; split at hs <;> (try split at hs) <;> simp_all
      simp only [encBool, encScan, List.cons.injEq, and_true, true_and]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; cases v <;> simp at hp <;> omega),
        USize.toNat_toUInt64,
        USize.toNat_add, hp]
      cases v <;> simp [hU] <;> omega

end ConAgua.Scan
