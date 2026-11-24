module

public import ConAgua.Checker.Entry
public import ConAgua.Arena.FreezeBuf
import all ConAgua.Checker.Entry
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.FreezeSpec
import ConAgua.L.Blocks
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `check_b`'s seed re-read (lane compare2)

`seed_reread()` (`Checker/Entry.lean`): with a seed (`CTLF` nonempty) its phase words `rrWs`
(`CTL[128]`, `CTL[162‥173]`, `CTL[224]`) copied into `CTL`; in place (`CTLF` empty) nothing.

* `rereadMem x`: the memory after it; `seedReread_spec`.
* `rereadMem_ne`: it changes `CTL` alone; `rereadMem_empty`: in place it is the identity;
  `rereadMem_noop`: when `CTL` already holds the seed's words `rrWs`, it is the identity.
-/

namespace L.Checker

open L L.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- The seed words `seed_reread` copies: `128`, `162‥173`, `224`. -/
def rrWs : List Nat := 128 :: List.range' 162 12 ++ [224]

/-- `CTL`'s words `rrWs` are the seed's. -/
def CtlSeed (c f : Array Word) : Prop := ∀ k ∈ rrWs, c.getD k 0 = f.getD k 0

/-- **The memory after `seed_reread()`.** -/
def rereadMem (x : Mem) : Mem :=
  if x.len64 CTLF = 0 then x else
    (((x.set64 CTL 128 (rdW (x.arr64 CTLF) 128)).copy64 CTL 162 CTLF 162 12).set64 CTL 224
      (rdW (x.arr64 CTLF) 224))

theorem rereadMem_empty {x : Mem} (h : x.len64 CTLF = 0) : rereadMem x = x := by
  simp only [rereadMem, h, ite_true]

theorem rereadMem_ne (x : Mem) {t : TieredArray} (ht : t ≠ CTL) :
    (rereadMem x).arr64 t = x.arr64 t := by
  unfold rereadMem
  split
  · rfl
  · rw [Mem.arr64_set64_ne _ _ _ _ _ ht, arr64_copy64_ne _ _ _ _ _ _ ht, Mem.arr64_set64_ne _ _ _ _ _ ht]

theorem rereadMem_glob (x : Mem) : (rereadMem x).glob = x.glob := by
  unfold rereadMem; split
  · rfl
  · rw [show ∀ (m : Mem) a i v, (m.set64 a i v).glob = m.glob from fun _ _ _ _ => rfl,
      Mem.copy64_glob]; rfl

theorem rereadMem_bytes (x : Mem) : (rereadMem x).bytes = x.bytes := by
  unfold rereadMem; split
  · rfl
  · rw [show ∀ (m : Mem) a i v, (m.set64 a i v).bytes = m.bytes from fun _ _ _ _ => rfl,
      Mem.copy64_bytes]; rfl

theorem rereadMem_size (x : Mem) (t : TieredArray) :
    ((rereadMem x).arr64 t).size = (x.arr64 t).size := by
  unfold rereadMem; split
  · rfl
  · simp only [L.Mem.size64_set64, size_copy64]

/-- **The re-read is the identity** when `CTL` already holds the seed's words `rrWs`. -/
theorem rereadMem_noop (x : Mem)
    (h : x.len64 CTLF ≠ 0 → ∀ k ∈ rrWs, (x.arr64 CTL).getD k 0 = (x.arr64 CTLF).getD k 0) :
    (rereadMem x).arr64 CTL = x.arr64 CTL := by
  unfold rereadMem
  split
  · rfl
  rename_i hne
  have h := h hne
  have hc : (CTL : TieredArray) ≠ CTLF := by decide
  apply arr_eq_of_getD
  · simp only [L.Mem.size64_set64, size_copy64]
  intro k hk
  simp only [L.Mem.size64_set64, size_copy64] at hk
  have hr128 : rdW (x.arr64 CTLF) 128 = (x.arr64 CTLF).getD 128 0 := by
    simp [rdW, Array.getD_eq_getD_getElem?]
  have hr224 : rdW (x.arr64 CTLF) 224 = (x.arr64 CTLF).getD 224 0 := by
    simp [rdW, Array.getD_eq_getD_getElem?]
  rw [getD_set64_same, getD_copy64 (by decide) 12 _ 162 162 (by simp) (by simp)]
  simp only [L.Mem.size64_set64, size_copy64, getD_set64_same, Mem.arr64_set64_ne _ _ _ _ _ hc.symm,
    show UInt64.toNat 224 = 224 from rfl, show UInt64.toNat 162 = 162 from rfl,
    show UInt64.toNat 128 = 128 from rfl]
  by_cases h1 : k = 224 ∧ k < (x.arr64 CTL).size
  · rw [ite_eq_left h1, h1.1, hr224]; exact (h 224 (by simp [rrWs])).symm
  rw [ite_eq_right h1]
  by_cases h2 : 162 ≤ k ∧ k < 162 + 12 ∧ k < (x.arr64 CTL).size
  · rw [ite_eq_left h2, show 162 + (k - 162) = k by omega]
    exact (h k (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_range'_1.mpr ⟨h2.1, by omega⟩)))).symm
  rw [ite_eq_right h2]
  by_cases h3 : k = 128 ∧ k < (x.arr64 CTL).size
  · rw [ite_eq_left h3, h3.1, hr128]; exact (h 128 (by simp [rrWs])).symm
  rw [ite_eq_right h3]

theorem getElem_rdW (a : Array Word) (i : Word) (h : i.toNat < a.size) : a[i.toNat] = rdW a i :=
  (rdW_eq a i _ rfl h).symm

/-- **The re-read on a thread's arrays**: every array as before when `CTL` holds the seed's words. -/
theorem rereadMem_arr (x : Mem)
    (h : x.len64 CTLF ≠ 0 → ∀ k ∈ rrWs, (x.arr64 CTL).getD k 0 = (x.arr64 CTLF).getD k 0)
    (t : TieredArray) : (rereadMem x).arr64 t = x.arr64 t := by
  by_cases ht : t = CTL
  · subst ht; exact rereadMem_noop x h
  · exact rereadMem_ne x ht

/-- **After the re-read `CTL` holds the seed's words `rrWs`** (with a seed, `CTL` past `224`). -/
theorem rereadMem_rr (x : Mem) (h0 : x.len64 CTLF ≠ 0) (h1 : 224 < (x.arr64 CTL).size) :
    ∀ k ∈ rrWs, ((rereadMem x).arr64 CTL).getD k 0 = (x.arr64 CTLF).getD k 0 := by
  intro k hk
  have hk' := (by decide : ∀ k ∈ rrWs, k = 128 ∨ (162 ≤ k ∧ k < 174) ∨ k = 224) k hk
  have hc : (CTL : TieredArray) ≠ CTLF := by decide
  have hr128 : rdW (x.arr64 CTLF) 128 = (x.arr64 CTLF).getD 128 0 := by
    simp [rdW, Array.getD_eq_getD_getElem?]
  have hr224 : rdW (x.arr64 CTLF) 224 = (x.arr64 CTLF).getD 224 0 := by
    simp [rdW, Array.getD_eq_getD_getElem?]
  simp only [rereadMem, ite_eq_right h0]
  rw [getD_set64_same, getD_copy64 (by decide) 12 _ 162 162 (by simp) (by simp)]
  simp only [L.Mem.size64_set64, getD_set64_same, Mem.arr64_set64_ne _ _ _ _ _ hc.symm,
    show UInt64.toNat 224 = 224 from rfl, show UInt64.toNat 162 = 162 from rfl,
    show UInt64.toNat 128 = 128 from rfl, size_copy64]
  rcases hk' with rfl | hk2 | rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨rfl, by omega⟩, hr128]
  · rw [ite_eq_right (by omega), ite_eq_left ⟨hk2.1, by omega, by omega⟩, show 162 + (k - 162) = k by omega]
  · rw [ite_eq_left ⟨rfl, by omega⟩, hr224]

/-- **`seed_reread()`'s bounds**: with a seed, it returns only with `CTL` and `CTLF` past `224`. -/
theorem seedReread_bnd (p : Prog) (hp : p.lookup "seed_reread" = some seedRereadL) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "seed_reread" []
    ⦃fun _ _ => s₀.mem.len64 CTLF ≠ 0 → 224 < (s₀.mem.arr64 CTL).size ∧ 224 < (s₀.mem.arr64 CTLF).size;
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, seedRereadL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr]
    all_goals simp only [Cmp.eval] at *
    all_goals (try simp only [L.Mem.size64_set64, size_copy64, arr64_copy64_ne _ _ _ _ _ _
      (show (CTLF : TieredArray) ≠ CTL by decide), Mem.arr64_set64_ne _ _ _ _ _
      (show (CTLF : TieredArray) ≠ CTL by decide), show UInt64.toNat 224 = 224 from rfl] at *)
    all_goals first
      | assumption
      | (intro _; exact ⟨by assumption, by assumption⟩)
      | (intro h; simp_all)
      | (exfalso; simp_all)


/-- **`seed_reread()`'s spec.** -/
theorem seedReread_spec (p : Prog) (hp : p.lookup "seed_reread" = some seedRereadL) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "seed_reread" []
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = rereadMem s₀.mem ∧ r = [0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, seedRereadL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr]
    all_goals simp only [Cmp.eval] at *
    case vc1 | vc4 => simp only [LocEq]
    case vc3 | vc6 => rfl
    case vc2 =>
      have e1 : ∀ v, ((s₀.mem.set64 CTL 128 v).copy64 CTL 162 CTLF 162 (UInt64.toNat 12)).arr64 CTLF =
          s₀.mem.arr64 CTLF := fun v => by
        rw [arr64_copy64_ne _ _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      have hne : s₀.mem.len64 CTLF ≠ 0 := by
        intro h; simp [h] at ‹(_ != _) = true›
      simp only [getElem_rdW, e1]
      simp only [rereadMem, ite_eq_right hne]
      rfl
    case vc5 =>
      have he : s₀.mem.len64 CTLF = 0 := by
        have := ‹¬(_ != _) = true›
        simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using this
      rw [rereadMem_empty he]

/-- **`seed_reread()`'s spec with its bounds.** -/
theorem seedReread_spec' (p : Prog) (hp : p.lookup "seed_reread" = some seedRereadL) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "seed_reread" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = rereadMem s₀.mem ∧
      (s₀.mem.len64 CTLF ≠ 0 → 224 < (s₀.mem.arr64 CTL).size); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  have h1 := M.of_run (P := fun x => x = s₀) hs hrun (seedReread_spec p hp n s₀)
  have h2 := M.of_run (P := fun x => x = s₀) hs hrun (seedReread_bnd p hp n s₀)
  exact ⟨h1.1, h1.2.1, fun h => (h2 h).1⟩

end L.Checker
