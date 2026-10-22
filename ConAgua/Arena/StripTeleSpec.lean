import ConAgua.Arena.IndView
import ConAgua.Arena.IndMaster
import ConAgua.Arena.StripTele
import ConAgua.L.ProgHas

/-!
# `strip_pis`, `strip_lams` refine `stripPis`, `stripLams` (lane `indproofs3`, helper `stubs`)

The two strippers (`StripTele.lean`, lane `whnf3`) under the stage relation, replacing the stub
contracts `stripPis_spec`/`stripLams_spec` of `IndStubs.lean`.

* **The word model** `stripW tg n m [k, e]` (`tg` = `6` for `strip_pis`, `5` for `strip_lams`; `n`
  the L fuel of the call): the loop's model `stripGoW` at the loop's fuel, its callees by their
  models (`eViewW`, `allocW`). It does not depend on the program, so a caller's model calls it in
  place of the old `stubM "strip_pis"`, and only the caller's `vcgen` spec needs the lookups
  (`StripProg p`).
* **The relational lemma** `stripW_pis_ok`/`stripW_lams_ok`: a returning model run from the stage
  relation is a twin run of `stripPis k (decI e)` (`stripLams`) that keeps the twin state, with
  `KeepPost … decOLE` after — the stub contract's statement, with `stripW` for `stubM` and no
  further hypothesis. The domains are consecutive `IW` words from the old top; on `none` the top
  is put back.
* **The write set**: `stripW_frame` (`IW` and `CTL[200]` only), for the memo frames of callers.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `e_view` of a binder -/

/-- A returning `e_view` of a `forallE` handle: the view checks hold and the words are the
binder's. -/
theorem eViewW_forall (m : Mem) (h : Word) (hg : h >>> 28 = 6) (hne : eViewW m h ≠ []) :
    viewOK m h 30 ∧ eViewW m h = [6, rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2),
      rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1), 0] := by
  unfold eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, if_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, if_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  have n3 : ¬ h >>> 28 = 3 := by rw [hg]; decide
  have n4 : ¬ h >>> 28 = 4 := by rw [hg]; decide
  have n5 : ¬ h >>> 28 = 5 := by rw [hg]; decide
  simp only [n0, n1, n2, n3, n4, n5, hg, if_false, if_true] at hne ⊢
  by_cases c : rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, if_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-- A returning `e_view` of a `lam` handle. -/
theorem eViewW_lamS (m : Mem) (h : Word) (hg : h >>> 28 = 5) (hne : eViewW m h ≠ []) :
    viewOK m h 28 ∧ eViewW m h = [5, rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2),
      rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1), 0] := by
  unfold eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, if_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, if_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  have n3 : ¬ h >>> 28 = 3 := by rw [hg]; decide
  have n4 : ¬ h >>> 28 = 4 := by rw [hg]; decide
  simp only [n0, n1, n2, n3, n4, hg, if_false, if_true] at hne ⊢
  by_cases c : rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, if_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-! ## The word model -/

/-- **The model of the strippers' loop** (`tg` the binder tag: `6` `strip_pis`, `5` `strip_lams`)
at the loop's fuel, from count `n` and handle `h`; `k` the count wanted, `o` the pool's top at
entry. -/
def stripGoW (tg k o : Word) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | f + 1, m, n, h =>
    if n < k then
      if h >>> 28 ≠ tg then some ([0, 0, 0, 0], m.set64 CTL 200 o)
      else match eViewW m h with
        | [] => none
        | v => match allocW m 1 with
          | none => none
          | some (q, m1) =>
            stripGoW tg k o f (m1.set64 IW q (v.tail.headD 0)) (n + 1) (v.tail.tail.headD 0)
    else some ([1, o, k, h], m)

/-- **The model of `strip_pis(k, e)` (`tg = 6`) and `strip_lams(k, e)` (`tg = 5`)** at the call's
L fuel. -/
def stripW (tg : Word) : Nat → Mem → List Word → Option (List Word × Mem)
  | 0, _, _ => none
  | f + 1, m, args => stripGoW tg (args.headD 0) (rdW (m.arr64 CTL) 200) (f + 1) m 0 (args.tail.headD 0)

section arms
variable (tg k o : Word) (f : Nat) (m m1 : Mem) (n h q : Word)

theorem stripGoW_ge (hn : ¬ n < k) : stripGoW tg k o (f + 1) m n h = some ([1, o, k, h], m) := by
  simp only [stripGoW, hn, if_false]

theorem stripGoW_tag (hn : n < k) (hg : h >>> 28 ≠ tg) :
    stripGoW tg k o (f + 1) m n h = some ([0, 0, 0, 0], m.set64 CTL 200 o) := by
  simp only [stripGoW, if_pos hn, if_pos hg]

theorem stripGoW_step (hn : n < k) (hg : ¬ h >>> 28 ≠ tg) (hv : eViewW m h ≠ [])
    (ha : allocW m 1 = some (q, m1)) :
    stripGoW tg k o (f + 1) m n h = stripGoW tg k o f (m1.set64 IW q ((eViewW m h).tail.headD 0))
      (n + 1) ((eViewW m h).tail.tail.headD 0) := by
  simp only [stripGoW, if_pos hn, if_neg hg]
  repeat' split
  all_goals simp_all

end arms

/-! ## The `vcgen` specs -/

/-- The strippers' program: the two functions and their callees. -/
def stripProg : Prog :=
  [("strip_pis", stripPisL), ("strip_lams", stripLamsL), ("e_view", eView), ("iw_alloc", iwAlloc)]

/-- The program bundle of the strippers. -/
def StripProg (p : Prog) : Prop := ProgHas p stripProg

theorem stripPisLoop_spec (p : Prog) (hp : StripProg p) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f stripPisLoop
    ⦃fun r s' => r ≠ .brk ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 2 = s₀.loc 2 ∧
      stripGoW 6 (s₀.loc 0) (s₀.loc 2) f s₀.mem (s₀.loc 3) (s₀.loc 4) =
        some (r.retOr [1, s'.loc 2, s'.loc 0, s'.loc 4], s'.mem); ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := stripPisLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih,
        eView_spec p (hp.get "e_view") f, iwAlloc_specW p (hp.get "iw_alloc") f] <;>
      finish [stripGoW_ge, stripGoW_tag, stripGoW_step]

end L.Ind
