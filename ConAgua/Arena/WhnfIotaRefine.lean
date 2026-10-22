import ConAgua.Arena.WhnfIota
import ConAgua.Arena.PinsNatOp

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs (primed)

Each theorem here is the `WhnfIota.lean` statement of the same name, primed, with the program
hypotheses made explicit (the lane owner swaps them in).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Decoding rule records -/

theorem decRule_fields (a : Array Word) (q : Nat) (rl : IRecRule) (h : decRule a q = some rl) :
    (∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ rl.ctor = decI w) ∧
    ∃ w, a[q + 9]? = some w ∧ rl.k = (w != 0) := by
  simp only [decRule, hd?, nat?, bool?, Option.bind_eq_bind] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨x, ⟨y, hy, rfl⟩, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    grind
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at h
    grind
  · simp at h

theorem mapM_option_get {α β : Type} (f : α → Option β) : ∀ (l : List α) (rs : List β),
    l.mapM f = some rs → rs.length = l.length ∧ ∀ j (hj : j < l.length), f l[j] = rs[j]? := by
  intro l
  induction l with
  | nil => intro rs h; simp at h; subst h; simp
  | cons x l ih =>
    intro rs h
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, ys, hys, h⟩ := h
    cases h
    obtain ⟨h1, h2⟩ := ih ys hys
    refine ⟨by simp [h1], fun j hj => ?_⟩
    cases j with
    | zero => simp [hy]
    | succ j => simpa using h2 j (by simpa using hj)

theorem decRules_get (a : Array Word) (off cnt : Nat) (rs : List IRecRule)
    (h : decRules a off cnt = some rs) :
    rs.length = cnt ∧ ∀ j, j < cnt → decRule a (off + 11 * j) = rs[j]? := by
  obtain ⟨h1, h2⟩ := mapM_option_get _ _ _ h
  simp at h1
  exact ⟨h1, fun j hj => by have := h2 j (by simpa using hj); simpa [List.getElem_range] using this⟩

/-- The model's index arithmetic does not wrap on a decoded record. -/
theorem rule_idx (a : Array Word) (ro i : Word) (rl : IRecRule)
    (hsz : a.size < 2 ^ 64) (h : decRule a (ro.toNat + 11 * i.toNat) = some rl) :
    (ro + 11 * i).toNat = ro.toNat + 11 * i.toNat ∧ ro.toNat + 11 * i.toNat < a.size := by
  obtain ⟨⟨w, hw, _⟩, _⟩ := decRule_fields a _ rl h
  have hlt : ro.toNat + 11 * i.toNat < a.size := by
    have := (Array.getElem?_eq_some_iff.mp hw).1; exact this
  refine ⟨?_, hlt⟩
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  simp
  omega

/-! ## `find_rule(ro, rc, c)` -/

/-- Model of the `find_rule` scan from index `i` with step bound `K` (`rc - i`). -/
def frW (E : Array Word) (ro rc c : Word) : Nat → Word → Option (List Word)
  | 0, _ => some [0, 0]
  | K + 1, i =>
    if i < rc then
      if h : (ro + 11 * i).toNat < E.size then
        if E[(ro + 11 * i).toNat] = c then some [1, ro + 11 * i] else frW E ro rc c K (i + 1)
      else none
    else some [0, 0]

theorem uint64_succ_toNat (n i : Word) (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  rw [UInt64.toNat_add]; simp
  have := n.toNat_lt
  have : i.toNat < n.toNat := h
  omega

theorem frW_done (E : Array Word) (ro rc c i : Word) (h : ¬ i < rc) :
    frW E ro rc c (rc.toNat - i.toNat) i = some [0, 0] := by
  cases hK : rc.toNat - i.toNat with
  | zero => rw [frW]
  | succ k => rw [frW]; simp [h]

theorem frW_step (E : Array Word) (ro rc c i : Word) (h : i < rc) :
    frW E ro rc c (rc.toNat - i.toNat) i =
      if h : (ro + 11 * i).toNat < E.size then
        if E[(ro + 11 * i).toNat] = c then some [1, ro + 11 * i]
        else frW E ro rc c (rc.toNat - (i + 1).toNat) (i + 1)
      else none := by
  have h1 := uint64_succ_toNat rc i h
  have : i.toNat < rc.toNat := h
  have hK : rc.toNat - i.toNat = (rc.toNat - (i + 1).toNat) + 1 := by omega
  rw [hK, frW]
  simp [h]

theorem findRuleLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k findRuleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      frW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) ((s₀.loc 1).toNat - (s₀.loc 3).toNat)
        (s₀.loc 3) = some (r.retOr [0, 0]); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := findRuleLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish [frW_done, frW_step]

theorem findRuleLoop_step_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p k) findRuleLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      frW (s₀.mem.arr64 EREC) (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) ((s₀.loc 1).toNat - (s₀.loc 3).toNat)
        (s₀.loc 3) = some (r.retOr [0, 0]); ⊤⦄ :=
  Triple.step_exec (findRuleLoop_spec p (k + 1) s₀)

theorem findRule_spec (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (k : Nat)
    (s₀ : St) (ro rc c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p k) "find_rule" [ro, rc, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      frW (s₀.mem.arr64 EREC) ro rc c rc.toNat 0 = some r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, findRuleL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, findRuleLoop_step_spec p k] <;>
      finish

/-- **The scan model computes `findRule`.** -/
theorem frW_rel (E : Array Word) (hsz : E.size < 2 ^ 64) (ro rc c : Word) (hc : HW c)
    (rules : List IRecRule) (hlen : rules.length = rc.toNat)
    (hget : ∀ j, j < rc.toNat → decRule E (ro.toNat + 11 * j) = rules[j]?) :
    ∀ (K : Nat) (i : Word) (L : List Word), rc.toNat - i.toNat = K →
      frW E ro rc c K i = some L →
      findRule (rules.drop i.toNat) (decI c) =
        (if L.headD 0 = 0 then none else decRule E (L.tail.headD 0).toNat) := by
  intro K
  induction K with
  | zero =>
    intro i L hK h
    rw [frW] at h
    cases h
    have : rules.drop i.toNat = [] := List.drop_eq_nil_of_le (by omega)
    simp [this, findRule]
  | succ K ih =>
    intro i L hK h
    have hi : i < rc := by
      have : i.toNat < rc.toNat := by omega
      exact this
    have hi' : i.toNat < rc.toNat := hi
    obtain ⟨rl, hrl⟩ : ∃ rl, rules[i.toNat]? = some rl :=
      ⟨rules[i.toNat], List.getElem?_eq_getElem (by omega)⟩
    have hdr := hget i.toNat hi'
    rw [hrl] at hdr
    obtain ⟨hw, hlt⟩ := rule_idx E ro i rl hsz hdr
    have hdrop : rules.drop i.toNat = rl :: rules.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
      simp [List.getElem?_eq_some_iff.mp hrl |>.2]
    obtain ⟨⟨w, hwE, hw32, hctor⟩, _⟩ := decRule_fields E _ rl hdr
    have hwE' : E[ro.toNat + 11 * i.toNat] = w := (Array.getElem?_eq_some_iff.mp hwE).2
    rw [frW] at h
    simp only [hi, ite_true, hw, hlt, dite_true] at h
    rw [hdrop, findRule]
    split at h
    · rename_i hEq
      cases h
      have hEq' : w = c := hwE'.symm.trans hEq
      subst hEq'
      simp [hctor, hw, hdr]
    · rename_i hEq
      have hne : ¬ w = c := fun e => hEq (hwE'.trans e)
      have hbeq : (rl.ctor == decI c) = false := by
        rw [hctor, decI_beq _ _ hw32 hc]; simpa using hne
      have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat rc i hi
      rw [hbeq]
      simp only [Bool.false_eq_true, ite_false]
      have := ih (i + 1) L (by omega) h
      rwa [h1] at this

/-- **`find_rule` refines `findRule`.** `HW c` (`decI` truncates) and a size bound on the pool
(the index arithmetic `ro + 11 * i` does not wrap) are added to the statement. -/
theorem findRule_refines' (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (n : Nat)
    (s₀ : St) (ro rc c : Word) (rules : List IRecRule) (hc : HW c)
    (hsz : (s₀.mem.arr64 EREC).size < 2 ^ 64)
    (hr : decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "find_rule" [ro, rc, c]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      findRule rules (decI c) = decRuleAt s₀.mem (r.headD 0) (r.tail.headD 0); ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hmem, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (findRule_spec p hp n s₀ ro rc c)
  obtain ⟨hl, hg⟩ := decRules_get _ _ _ _ hr
  have := frW_rel _ hsz ro rc c hc rules hl hg _ 0 r rfl hW
  refine ⟨hmem, hloc, ?_⟩
  simpa [decRuleAt] using this

/-! ## `rec_rule_k(ro, rc)` -/

/-- Model of `rec_rule_k`. -/
def rrkW (E : Array Word) (ro rc : Word) : Option Word :=
  if rc ≠ 1 then some 0
  else if h : (ro + 9).toNat < E.size then some E[(ro + 9).toNat] else none

theorem recRuleK_spec (p : Prog) (hp : p.lookup "rec_rule_k" = some recRuleKL) (k : Nat)
    (s₀ : St) (ro rc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p k) "rec_rule_k" [ro, rc]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      rrkW (s₀.mem.arr64 EREC) ro rc = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recRuleKL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [rrkW]

/-- **`rec_rule_k` refines `recRuleK`.** -/
theorem recRuleK_refines' (p : Prog) (hp : p.lookup "rec_rule_k" = some recRuleKL) (n : Nat)
    (s₀ : St) (ro rc : Word) (rules : List IRecRule)
    (hsz : (s₀.mem.arr64 EREC).size < 2 ^ 64)
    (hr : decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_rule_k" [ro, rc]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ (r.headD 0 != 0) = recRuleK rules; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hmem, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (recRuleK_spec p hp n s₀ ro rc)
  refine ⟨hmem, hloc, ?_⟩
  obtain ⟨hl, hg⟩ := decRules_get _ _ _ _ hr
  by_cases h1 : rc = 1
  · subst h1
    have hl1 : rules.length = 1 := by simpa using hl
    obtain ⟨rl, rfl⟩ : ∃ rl, rules = [rl] := by
      match rules, hl1 with
      | [x], _ => exact ⟨x, rfl⟩
    have hg0 := hg 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem?_cons_zero] at hg0
    obtain ⟨_, w, hw, hk⟩ := decRule_fields _ _ rl hg0
    have hlt := (Array.getElem?_eq_some_iff.mp hw).1
    have hro : (ro + 9).toNat = ro.toNat + 9 := by
      rw [UInt64.toNat_add]; simp; omega
    have hb : (ro + 9).toNat < (s₀.mem.arr64 EREC).size := by rw [hro]; exact hlt
    simp only [rrkW, ne_eq, not_true_eq_false, ↓reduceIte, hb, ↓reduceDIte, Option.some.injEq] at hW
    have hv : (s₀.mem.arr64 EREC)[ro.toNat + 9] = w := (Array.getElem?_eq_some_iff.mp hw).2
    simp only [recRuleK, hk]
    rw [← hW]
    simp only [hro]
    rw [hv]
  · simp only [rrkW, h1, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hW
    rw [← hW]
    have : rc.toNat ≠ 1 := fun h => h1 (UInt64.toNat_inj.mp (by simpa using h))
    simp only [recRuleK]
    match rules, hl with
    | [], _ => simp
    | [x], hl => simp at hl; omega
    | _ :: _ :: _, _ => simp

end L.Arena
