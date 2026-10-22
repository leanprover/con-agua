import ConAgua.Arena.DeclRomStubs

/-!
# Pin-selected ROM values: `reduceOpCvA`, `ofReducePinA`, `reduceDeclPin` (lane `decls3`)

Three twin functions of one shape: read a pin, compare the argument with it, intern one of two
con-leche values (`if c == pin then A else B`). In L: `pin_at(k)`, then `rom_cv`/`rom_expr` at one
of two ids. One model (`selW`) and one relational lemma (`selW_ok`) serve all three; through the
ROM stubs (`DeclRomStubs.lean`), so census `sorry`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind

/-! ## The model -/

/-- After the stub. -/
def selK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => some ([r2.headD 0], m2)

/-- After the pin read: one of the two ids. -/
def selK (f : FnName) (i j c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if c = r1.headD 0 then selK2 (stubM f m1 [i]) else selK2 (stubM f m1 [j])

/-- **The model**: `pin_at(k)`, then `f(i)` on a match, else `f(j)`. -/
def selW (m : Mem) (c k : Word) (f : FnName) (i j : Word) : Option (List Word × Mem) :=
  selK f i j c (pinAtW m k)

section arms
variable (f : FnName) (i j c : Word) (r1 r2 : List Word) (m1 m2 : Mem)
theorem selK_some : selK f i j c (some (r1, m1)) =
    if c = r1.headD 0 then selK2 (stubM f m1 [i]) else selK2 (stubM f m1 [j]) := rfl
theorem selK2_some : selK2 (some (r2, m2)) = some ([r2.headD 0], m2) := rfl
end arms

grind_pattern [ind_grind] selK_some => selK f i j c (some (r1, m1))
grind_pattern [ind_grind] selK2_some => selK2 (some (r2, m2))

/-! ## The relational lemma -/

/-- **A pin-selected ROM value is the twin's**: `do let x ← pinAt k; if c == x then T i else T j`. -/
theorem selW_ok {α : Type} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {c k : Word} {f : FnName} {i j : Word} {r : List Word}
    {T : Nat → AM α} {dec : Mem → List Word → α → Prop}
    (hT : ∀ w, (w = i ∨ w = j) → RelAM f [w] (StageR dn vis fe) (T w.toNat) (KeepPost dn vis fe dec))
    (hdec : ∀ m r x, dec m r x → dec m [r.headD 0] x)
    (h : selW m c k f i j = some (r, m')) (hS : StageR dn vis fe m a) (hc : c.toNat < 2 ^ 32) :
    ∃ x a', (do let y ← pinAt k.toNat; if (decI c : NIdx) == y then T i.toNat else T j.toNat).run a =
      .ok (x, a') ∧ KeepPost dn vis fe dec m m' a' r x := by
  unfold selW at h
  cases h1 : pinAtW m k with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, selK_some] at h
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.1.pins
  have e1 : r1.headD 0 = pinW m (1 + k.toNat) := by rw [hr1]; rfl
  have hbeq : ((decI c : NIdx) == decI (pinW m (1 + k.toNat))) = decide (c = pinW m (1 + k.toNat)) :=
    decI_beq c _ hc hl1
  have tail : ∀ w, (w = i ∨ w = j) → selK2 (stubM f m [w]) = some (r, m') →
      ∃ x a', (T w.toNat).run a = .ok (x, a') ∧ KeepPost dn vis fe dec m m' a' r x := by
    intro w hw h
    cases h2 : stubM f m [w] with
    | none => rw [h2] at h; cases h
    | some rm2 =>
    obtain ⟨r2, m2⟩ := rm2
    rw [h2, selK2_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, a', hrun, hS', hg, hd⟩ := hT w hw m m2 a r2 h2 hS
    exact ⟨x, a', hrun, hS', hg, hdec _ _ _ hd⟩
  rw [hm1] at h
  by_cases he : c = r1.headD 0
  · rw [if_pos he] at h
    obtain ⟨x, a', hrun, hP⟩ := tail i (.inl rfl) h
    rw [e1] at he
    refine ⟨x, a', ?_, hP⟩
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hbeq, he, decide_true, if_true,
      beq_self_eq_true]
    exact hrun
  · rw [if_neg he] at h
    obtain ⟨x, a', hrun, hP⟩ := tail j (.inr rfl) h
    rw [e1] at he
    refine ⟨x, a', ?_, hP⟩
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hbeq, he, decide_false, Bool.false_eq_true,
      if_false]
    exact hrun

theorem decRCV_head (m : Mem) (r : List Word) (x : IConstantVal) (h : decRCV m r x) :
    decRCV m [r.headD 0] x := h

theorem decW0E_head (m : Mem) (r : List Word) (x : EIdx) (h : decW0E m r x) :
    decW0E m [r.headD 0] x := h

/-! ## The three functions -/

section specs
variable (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL)
include hpa

theorem reduceOpCvA_specW (hp : p.lookup "reduce_op_cv_a" = some reduceOpCvAL) (n : Nat) (s₀ : St)
    (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_op_cv_a" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ selW s₀.mem c 43 "rom_cv" 6 7 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, reduceOpCvAL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n,
        stubM_spec p "rom_cv" n] <;>
      finish (gen := 20) [selW]

theorem ofReducePinA_specW (hp : p.lookup "of_reduce_pin_a" = some ofReducePinAL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_pin_a" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ selW s₀.mem c 45 "rom_cv" 8 9 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ofReducePinAL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n,
        stubM_spec p "rom_cv" n] <;>
      finish (gen := 20) [selW]

theorem reduceDeclPin_specW (hp : p.lookup "reduce_decl_pin" = some reduceDeclPinL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_decl_pin" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ selW s₀.mem c 43 "rom_expr" 0 1 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, reduceDeclPinL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n,
        stubM_spec p "rom_expr" n] <;>
      finish (gen := 20) [selW]

end specs

section refines
variable (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (a₀ : AState)
  (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word)
  (hS : StageR dn vis fe s₀.mem a₀) (hc : c.toNat < 2 ^ 32)
include hpa hS hc

/-- **`reduce_op_cv_a(c)` refines `reduceOpCvA`** (through `rom_cv`'s stub). -/
@[refines ConRon.Arena.reduceOpCvA]
theorem reduceOpCvA_refines (hp : p.lookup "reduce_op_cv_a" = some reduceOpCvAL) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_op_cv_a" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (reduceOpCvA (decI c)) a₀ ∧
      KeepPost dn vis fe decRCV s₀.mem s'.mem (AM.st (reduceOpCvA (decI c)) a₀) r
        (AM.res (reduceOpCvA (decI c)) a₀); ⊤⦄ := by
  refine triple_post (reduceOpCvA_specW p hpa hp n s₀ c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hP⟩ := selW_ok (T := romCvT)
    (fun w hw => romCv_spec dn vis fe w (by rcases hw with rfl | rfl <;> decide)) decRCV_head hm hS hc
  have e : reduceOpCvA (decI c) =
      (do let y ← pinAt (43 : Word).toNat
          if (decI c : NIdx) == y then romCvT (6 : Word).toNat else romCvT (7 : Word).toNat) := rfl
  rw [← e] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hP⟩

/-- **`of_reduce_pin_a(n)` refines `ofReducePinA`** (through `rom_cv`'s stub). -/
@[refines ConRon.Arena.ofReducePinA]
theorem ofReducePinA_refines (hp : p.lookup "of_reduce_pin_a" = some ofReducePinAL) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_pin_a" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ofReducePinA (decI c)) a₀ ∧
      KeepPost dn vis fe decRCV s₀.mem s'.mem (AM.st (ofReducePinA (decI c)) a₀) r
        (AM.res (ofReducePinA (decI c)) a₀); ⊤⦄ := by
  refine triple_post (ofReducePinA_specW p hpa hp n s₀ c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hP⟩ := selW_ok (T := romCvT)
    (fun w hw => romCv_spec dn vis fe w (by rcases hw with rfl | rfl <;> decide)) decRCV_head hm hS hc
  have e : ofReducePinA (decI c) =
      (do let y ← pinAt (45 : Word).toNat
          if (decI c : NIdx) == y then romCvT (8 : Word).toNat else romCvT (9 : Word).toNat) := rfl
  rw [← e] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hP⟩

/-- **`reduce_decl_pin(c)` refines `reduceDeclPin`** (through `rom_expr`'s stub). -/
@[refines ConRon.Arena.reduceDeclPin]
theorem reduceDeclPin_refines (hp : p.lookup "reduce_decl_pin" = some reduceDeclPinL) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_decl_pin" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (reduceDeclPin (decI c)) a₀ ∧
      KeepPost dn vis fe decW0E s₀.mem s'.mem (AM.st (reduceDeclPin (decI c)) a₀) r
        (AM.res (reduceDeclPin (decI c)) a₀); ⊤⦄ := by
  refine triple_post (reduceDeclPin_specW p hpa hp n s₀ c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hP⟩ := selW_ok (T := romExprT)
    (fun w hw => romExpr_spec dn vis fe w (by rcases hw with rfl | rfl <;> decide)) decW0E_head hm hS
    hc
  have e : reduceDeclPin (decI c) =
      (do let y ← pinAt (43 : Word).toNat
          if (decI c : NIdx) == y then romExprT (0 : Word).toNat else romExprT (1 : Word).toNat) :=
    rfl
  rw [← e] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hP⟩

end refines

end L.Arena
