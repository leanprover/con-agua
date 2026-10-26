import ConAgua.Arena.PromotePi

/-!
# `promote_n` and `pn_arm`: models and specs

The template of `WhnfCoreSlot.lean`: a word-level model whose callees are `callW` runs, the L
spec one `vcgen` + `finish` with `callW_spec`, guarded equations per arm. `pnW` is `promote_n`
(the fuel test, the persistent test, the memo probe, the arm, the memo record), `pnArmW` is
`pn_arm` (the scratch view of a name record: `anonymous`, `str`, `num`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The models -/

/-- The first result word of a callee's run. -/
def hd1 : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) => some (r.headD 0, m)

/-- A memo record after the body's run: probe again, put, answer. -/
def memoK (S : MemoSch) (h : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    match msetG S m₁ h 0 (r.headD 0) with
    | none => none
    | some m₂ => some (r.headD 0, m₂)

/-- **The model of `promote_n(f, h)`.** -/
def pnW (p : Prog) (n : Nat) (m : Mem) (f h : Word) : Option (Word × Mem) :=
  if f = 0 then none
  else if tierW h = 0 then some (h, m)
  else if mfindG pnSch m h 0 = [] then none
  else if (mfindG pnSch m h 0).headD 0 ≠ 0 then
    some (mvG pnSch m ((mfindG pnSch m h 0).tail.headD 0), m)
  else memoK pnSch h (callW p n "pn_arm" [f - 1, h] m)

/-- After the prefix of a `str` name: intern the node. -/
def pnStrK (p : Prog) (n : Nat) (o l : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q, m₁) => hd1 (callW p n "pi_nstr" [q.headD 0, o, l] m₁)

/-- After the prefix of a `num` name: intern the node. -/
def pnNumK (p : Prog) (n : Nat) (u : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q, m₁) => hd1 (callW p n "pi_nnum" [q.headD 0, u] m₁)

/-- The `num` record's two words. -/
abbrev nnQ (m : Mem) (t i : Word) : Word := tfld m NNUM t i 0
abbrev nnU (m : Mem) (t i : Word) : Word := tfld m NNUM t i 1

/-- **The model of `pn_arm(f, h)`.** -/
def pnArmW (p : Prog) (n : Nat) (m : Mem) (f h : Word) : Option (Word × Mem) :=
  if 4294967295 < h then none
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if h >>> 28 = 0 then
    if tcnt m NANON (tierW h) ≤ idxW h then none
    else hd1 (callW p n "pi_nanon" [] m)
  else if h >>> 28 = 1 then
    if tcnt m NSTR (tierW h) ≤ idxW h then none
    else pnStrK p n (tfld m NSTR (tierW h) (idxW h) 1) (tfld m NSTR (tierW h) (idxW h) 2)
      (callW p n "promote_n" [f, tfld m NSTR (tierW h) (idxW h) 0] m)
  else if h >>> 28 = 2 then
    if tcnt m NNUM (tierW h) ≤ idxW h then none
    else pnNumK p n (nnU m (tierW h) (idxW h)) (callW p n "promote_n" [f, nnQ m (tierW h) (idxW h)] m)
  else none

/-! ## Guarded equations -/

section eqs
variable (p : Prog) (n : Nat) (m m₁ : Mem) (f h o l u : Word) (r q : List Word)

theorem hd1_some : hd1 (some (r, m)) = some (r.headD 0, m) := rfl

theorem memoK_some (S : MemoSch) (m₂ : Mem) (hs : msetG S m₁ h 0 (r.headD 0) = some m₂) :
    memoK S h (some (r, m₁)) = some (r.headD 0, m₂) := by
  simp only [memoK, hs]

theorem pnStrK_some : pnStrK p n o l (some (q, m₁)) = hd1 (callW p n "pi_nstr" [q.headD 0, o, l] m₁) :=
  rfl
theorem pnNumK_some : pnNumK p n u (some (q, m₁)) = hd1 (callW p n "pi_nnum" [q.headD 0, u] m₁) :=
  rfl

theorem pnW_pers (hf : f ≠ 0) (ht : tierW h = 0) : pnW p n m f h = some (h, m) := by
  simp [pnW, hf, ht]

theorem pnW_hit (hf : f ≠ 0) (ht : tierW h ≠ 0) (h0 : mfindG pnSch m h 0 ≠ [])
    (h1 : (mfindG pnSch m h 0).headD 0 ≠ 0) :
    pnW p n m f h = some (mvG pnSch m ((mfindG pnSch m h 0).tail.headD 0), m) := by
  unfold pnW; rw [if_neg hf, if_neg ht, if_neg h0, if_pos h1]

theorem pnW_miss (hf : f ≠ 0) (ht : tierW h ≠ 0) (h0 : mfindG pnSch m h 0 ≠ [])
    (h1 : (mfindG pnSch m h 0).headD 0 = 0) :
    pnW p n m f h = memoK pnSch h (callW p n "pn_arm" [f - 1, h] m) := by
  unfold pnW; rw [if_neg hf, if_neg ht, if_neg h0, if_neg (fun h2 => h2 h1)]

theorem pnArmW_anon (hh : ¬ 4294967295 < h) (hv : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hg : h >>> 28 = 0) (hc : ¬ tcnt m NANON (tierW h) ≤ idxW h) :
    pnArmW p n m f h = hd1 (callW p n "pi_nanon" [] m) := by
  rw [pnArmW]; simp only [hh, hv, hg, hc, ↓reduceIte]

theorem pnArmW_str (hh : ¬ 4294967295 < h) (hv : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hg : h >>> 28 = 1) (hc : ¬ tcnt m NSTR (tierW h) ≤ idxW h) :
    pnArmW p n m f h = pnStrK p n (tfld m NSTR (tierW h) (idxW h) 1) (tfld m NSTR (tierW h) (idxW h) 2)
      (callW p n "promote_n" [f, tfld m NSTR (tierW h) (idxW h) 0] m) := by
  rw [pnArmW]; simp only [hh, hv, hg, hc, ↓reduceIte]; simp

theorem pnArmW_num (hh : ¬ 4294967295 < h) (hv : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hg : h >>> 28 = 2) (hc : ¬ tcnt m NNUM (tierW h) ≤ idxW h) :
    pnArmW p n m f h = pnNumK p n (nnU m (tierW h) (idxW h))
      (callW p n "promote_n" [f, nnQ m (tierW h) (idxW h)] m) := by
  rw [pnArmW]; simp only [hh, hv, hg, hc, ↓reduceIte]; simp

end eqs

/-! ## The specs -/

section specs
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

theorem promoteN_spec (f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_n" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ pnW p n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_n")]
  simp only [callFn, promoteNL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec pnSch p _ (hp.get "pn_find") n, memoPutG_spec pnSch p _ (hp.get "pn_put") n,
      callW_spec p n "pn_arm", evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [pnW_pers, pnW_hit, pnW_miss, memoK_some, mvG, tierW]

theorem pnArm_spec (f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pn_arm" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ pnArmW p n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "pn_arm")]
  simp only [callFn, pnArm]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "pi_nanon", callW_spec p n "promote_n", callW_spec p n "pi_nstr",
      callW_spec p n "pi_nnum", evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    finish [pnArmW_anon, pnArmW_str, pnArmW_num, pnStrK_some, pnNumK_some, hd1_some, tierW,
      idxW]

end specs

end L.Arena
