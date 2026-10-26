import ConAgua.Arena.StrLitTy

/-!
# The `List` declaration tests under `CoreS` (helper `defeq2-str-list`)

`list_ty_ok`, `list_nil_ty_ok`, `list_cons_ty_ok`, each as a `callW` run refining its twin at the
decoded record. The shared pieces:

* `str_param_sort(pn)` as a prefix of the twin's `do` block (`paramSort_run`: the three level and
  sort internings, then any continuation on their results);
* the one-parameter test on `str_cv`'s level-parameter slice (`lp_one`, `lp_ne`);
* the `∀`-guard `faGuardW`/`faGuardT` (tag test, view, domain comparison, then a continuation on
  the body) with `faGuard_ok`, and `List.nil`'s `app`/`const`/`bvar 0` tail (`nilAppW` …).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

/-! ## Tag tests and views -/

theorem slTagB (e : Word) (hh : HW e) (t : UInt32) (k : Nat) (hk : k < 16) (ht : t = UInt32.ofNat k) :
    ((decE e).tag == t) = decide (e >>> 28 = UInt64.ofNat k) := by
  subst ht
  by_cases h : (decE e).tag = UInt32.ofNat k
  · rw [beq_iff_eq.mpr h, decide_eq_true ((decE_tag_eq e hh k hk).mp h)]
  · rw [beq_false_of_ne h, decide_eq_false (fun h' => h ((decE_tag_eq e hh k hk).mpr h'))]

theorem slViewR_app {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h4 : r.headD 0 = 4) :
    v = .app (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)) ∧ HW (r.tail.headD 0) ∧
      HW (r.tail.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h4] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h3, h5, h6⟩ := hr; rw [getD_one] at h1 h3; rw [getD_two] at h5 h6
       exact ⟨by rw [h3, h6], h1, h5⟩)

theorem slViewR_bvar {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h0 : r.headD 0 = 0) :
    v = .bvar (r.tail.headD 0).toNat := by
  cases v <;> simp only [L.Ind.ViewR, h0] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1⟩ := hr; rw [getD_one] at h1; rw [h1])

theorem slViewR_const {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h3 : r.headD 0 = 3) :
    v = .const (decI (r.tail.headD 0)) (decI (r.tail.tail.headD 0)) ∧ HW (r.tail.headD 0) ∧
      HW (r.tail.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h3] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h4, h5, h6⟩ := hr; rw [getD_one] at h1 h4; rw [getD_two] at h5 h6
       exact ⟨by rw [h4, h6], h1, h5⟩)

/-! ## The `∀`-guard -/

/-- The twins' `∀`-guard: `ty` is `∀ (_ : X), b` and `k b` holds. -/
def faGuardT (k : EIdx → AM Bool) (ty X : EIdx) : AM Bool :=
  if ty.tag == ETag.forallE then do
    match ← view ty with
    | .forallE d b => if d != X then pure false else k b
    | _ => pure false
  else pure false

/-- The L code's `∀`-guard: the tag test, `e_view`, the domain test, then `k` on the body. -/
def faGuardW (k : Word → Mem → Option (Word × Mem)) (p : Prog) (n : Nat) (m : Mem) (ty X : Word) :
    Option (Word × Mem) :=
  if ty >>> 28 ≠ 6 then some (0, m)
  else match callW p n "e_view" [ty] m with
    | none => none
    | some (g, m₁) => if g.tail.headD 0 ≠ X then some (0, m₁) else k (g.tail.tail.headD 0) m₁

theorem faGuard_ok {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat} {m m' : Mem}
    {a : AState} (hR : ArenaR m a) {k : Word → Mem → Option (Word × Mem)} {kT : EIdx → AM Bool}
    (hk : ∀ b w m', HW b → k b m = some (w, m') →
      (kT (decE b)).run a = .ok (w != 0, a) ∧ m' = m ∧ ResH [w])
    {ty X w : Word} (hty : HW ty) (hX : HW X) (h : faGuardW k p n m ty X = some (w, m')) :
    (faGuardT kT (decE ty) (decE X)).run a = .ok (w != 0, a) ∧ m' = m ∧ ResH [w] := by
  unfold faGuardW at h
  by_cases g6 : ty >>> 28 ≠ 6
  · rw [if_pos g6] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : ((decE ty).tag == ETag.forallE) = false := by
      rw [slTagB ty hty ETag.forallE 6 (by decide) rfl]; exact decide_eq_false g6
    refine ⟨?_, rfl, by unfold ResH HW; decide⟩
    simp only [faGuardT, ht]; rfl
  rw [if_neg g6] at h
  have g6' : ty >>> 28 = 6 := by simpa using g6
  rcases hc : callW p n "e_view" [ty] m with _ | ⟨g, m₁⟩ <;> simp only [hc, reduceCtorEq] at h
  obtain ⟨rfl, v, hv, hvr, hg⟩ := eView_callW_view hp hR hc
  obtain ⟨rfl, h1, h2⟩ := viewR_forall hvr (by rw [hg, g6'])
  have ht : ((decE ty).tag == ETag.forallE) = true := by
    rw [slTagB ty hty ETag.forallE 6 (by decide) rfl]; exact decide_eq_true g6'
  have hd : (decE (g.tail.headD 0) != decE X) = decide (g.tail.headD 0 ≠ X) := by
    rw [decE_eq, decE_eq, bne, decI_beq _ _ h1 hX]; simp
  by_cases c : g.tail.headD 0 ≠ X
  · rw [if_pos c] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, rfl, by unfold ResH HW; decide⟩
    simp only [faGuardT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hd,
      decide_eq_true c]
    rfl
  · rw [if_neg c] at h
    obtain ⟨hr, hm, hres⟩ := hk _ _ _ h2 h
    refine ⟨?_, hm, hres⟩
    simp only [faGuardT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hd,
      decide_eq_false c]
    exact hr

/-! ## The level-parameter slice -/

theorem lp_one {e : Array Word} {c : List Word} {lps : List NIdx}
    (hsl : hslice? e (c.headD 0).toNat (c.tail.headD 0).toNat = some lps) (h1 : c.tail.headD 0 = 1) :
    lps = [decI (rdW e (c.headD 0))] ∧ HW (rdW e (c.headD 0)) := by
  rw [h1] at hsl
  simp only [hslice?, hd?, show (1 : Word).toNat = 1 from rfl, List.range_one, List.mapM_cons,
    List.mapM_nil, Nat.add_zero] at hsl
  cases hw : e[(c.headD 0).toNat]? with
  | none => rw [hw] at hsl; simp at hsl
  | some w =>
  rw [hw] at hsl
  have hr : rdW e (c.headD 0) = w := strRdW hw
  rw [hr]
  by_cases hlt : w.toNat < 2 ^ 32
  · simp [hlt] at hsl
    exact ⟨by subst hsl; rfl, hlt⟩
  · simp [hlt] at hsl

theorem lp_ne {c : List Word} {lps : List NIdx} (hlen : lps.length = (c.tail.headD 0).toNat)
    (h1 : c.tail.headD 0 ≠ 1) (x : NIdx) : lps ≠ [x] := by
  intro e
  rw [e] at hlen
  exact h1 (UInt64.toNat_inj.mp (by rw [← hlen]; rfl))

/-! ## `str_param_sort` -/

/-- The model of `str_param_sort`. -/
def psW (p : Prog) (n : Nat) (m : Mem) (pn : Word) : Option (List Word × Mem) :=
  match callW p n "intern_param" [pn] m with
  | none => none
  | some (x, m₁) =>
    match callW p n "intern_succ" [x.headD 0] m₁ with
    | none => none
    | some (y, m₂) =>
      match callW p n "intern_sort" [y.headD 0] m₂ with
      | none => none
      | some (z, m₃) => some ([x.headD 0, z.headD 0], m₃)

theorem strParamSort_spec (p : Prog) (hp : p.lookup "str_param_sort" = some strParamSortL) (n : Nat)
    (s₀ : St) (pn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_param_sort" [pn]
    ⦃fun r s' => LocEq s' s₀ ∧ psW p n s₀.mem pn = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strParamSortL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "intern_param", callW_spec p n "intern_succ", callW_spec p n "intern_sort"] <;>
    finish [psW]

/-! ## The models of the three tests

Each L function's model is a chain of continuations, one per callee run (`…K`) or tag guard and
view (`…A`, `…B`, …). `list_ty_ok`'s spec closes by `finish` on one guarded equation per arm;
the two longer ones by `simp_all` on the definitions (`finish` runs out of case splits there:
every pair of call argument lists is a candidate). -/

section model
variable (p : Prog) (n : Nat)

/-- The `∀`-type comparison after `e_view`. -/
def faEqK (X Y : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (g, m) => some (if g.tail.headD 0 = X ∧ g.tail.tail.headD 0 = Y then 1 else 0, m)

/-- The `∀`-type comparison: `faEqW` as a guard and a continuation. -/
def faEqA (m : Mem) (ty X Y : Word) : Option (Word × Mem) :=
  if ty >>> 28 ≠ 6 then some (0, m) else faEqK X Y (callW p n "e_view" [ty] m)

/-! ### `list_nil_ty_ok`'s tail: `∀ (_ : so), List.{u} #0` -/

/-- After the bound variable's view: index `0`, then the comparison of the head constant. -/
def nilDK (l1 u1 li ps : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (g, m) => if g.tail.headD 0 ≠ 0 then some (0, m)
    else some (if l1 = li ∧ u1 = ps then 1 else 0, m)

/-- The argument `x` is a bound variable. -/
def nilD (m : Mem) (x l1 u1 li ps : Word) : Option (Word × Mem) :=
  if x >>> 28 ≠ 0 then some (0, m) else nilDK l1 u1 li ps (callW p n "e_view" [x] m)

/-- After the head's view. -/
def nilCK (x li ps : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (g, m) => nilD p n m x (g.tail.headD 0) (g.tail.tail.headD 0) li ps

/-- The head `f` is a constant. -/
def nilC (m : Mem) (f x li ps : Word) : Option (Word × Mem) :=
  if f >>> 28 ≠ 3 then some (0, m) else nilCK p n x li ps (callW p n "e_view" [f] m)

/-- After the body's view. -/
def nilBK (li ps : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (g, m) => nilC p n m (g.tail.headD 0) (g.tail.tail.headD 0) li ps

/-- The body `b` is an application. -/
def nilB (m : Mem) (b li ps : Word) : Option (Word × Mem) :=
  if b >>> 28 ≠ 4 then some (0, m) else nilBK p n li ps (callW p n "e_view" [b] m)

/-- After the type's view: the domain is `so`. -/
def nilAK (so li ps : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (g, m) => if g.tail.headD 0 ≠ so then some (0, m) else nilB p n m (g.tail.tail.headD 0) li ps

/-- The type `ty` is a `∀`. -/
def nilA (m : Mem) (ty so li ps : Word) : Option (Word × Mem) :=
  if ty >>> 28 ≠ 6 then some (0, m) else nilAK p n so li ps (callW p n "e_view" [ty] m)

/-! ### `list_cons_ty_ok`'s tail: `∀ (_ : so) (_ : #0), dom3 → cod3` -/

/-- After the second binder's view: the domain is `#0`. -/
def consBK (b0 d3 c3 : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (g, m) => if g.tail.headD 0 ≠ b0 then some (0, m) else faEqA p n m (g.tail.tail.headD 0) d3 c3

/-- The second binder. -/
def consB (m : Mem) (r b0 d3 c3 : Word) : Option (Word × Mem) :=
  if r >>> 28 ≠ 6 then some (0, m) else consBK p n b0 d3 c3 (callW p n "e_view" [r] m)

/-- After the type's view: the domain is `so`. -/
def consAK (so b0 d3 c3 : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (g, m) =>
    if g.tail.headD 0 ≠ so then some (0, m) else consB p n m (g.tail.tail.headD 0) b0 d3 c3

/-- The type `ty` is a `∀`. -/
def consA (m : Mem) (ty so b0 d3 c3 : Word) : Option (Word × Mem) :=
  if ty >>> 28 ≠ 6 then some (0, m) else consAK p n so b0 d3 c3 (callW p n "e_view" [ty] m)

/-! ### The prefixes -/

/-- `list_ty_ok` after `str_param_sort`. -/
def listK2 (ty : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (s, m) => faEqA p n m ty (s.tail.headD 0) (s.tail.headD 0)

/-- `list_ty_ok` after `str_cv`. -/
def listK1 : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c, m) => if c.tail.headD 0 ≠ 1 then some (0, m)
    else listK2 p n (c.tail.tail.headD 0)
      (callW p n "str_param_sort" [rdW (m.arr64 EREC) (c.headD 0)] m)

/-- **The model of `list_ty_ok`.** -/
def listK0 (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m) else listK1 p n (callW p n "str_cv" [q] m)

/-- `list_nil_ty_ok` after `pin_at(7)`. -/
def nilK4 (ty so ps : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (i, m) => nilA p n m ty so (i.headD 0) ps

/-- `list_nil_ty_ok` after `str_ls1`. -/
def nilK3 (ty so : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (l, m) => nilK4 p n ty so (l.headD 0) (callW p n "pin_at" [7] m)

/-- `list_nil_ty_ok` after `str_param_sort`. -/
def nilK2 (ty : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (s, m) => nilK3 p n ty (s.tail.headD 0) (callW p n "str_ls1" [s.headD 0] m)

/-- `list_nil_ty_ok` after `str_cv`. -/
def nilK1 : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c, m) => if c.tail.headD 0 ≠ 1 then some (0, m)
    else nilK2 p n (c.tail.tail.headD 0) (callW p n "str_param_sort" [rdW (m.arr64 EREC) (c.headD 0)] m)

/-- **The model of `list_nil_ty_ok`.** -/
def nilK0 (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m) else nilK1 p n (callW p n "str_cv" [q] m)

/-- `list_cons_ty_ok` after the second `mk_app`. -/
def consK10 (ty so b0 d3 : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c3, m) => consA p n m ty so b0 d3 (c3.headD 0)

/-- `list_cons_ty_ok` after the first `mk_app`. -/
def consK9 (ty so b0 b2 l1 : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d3, m) => consK10 p n ty so b0 (d3.headD 0) (callW p n "mk_app" [l1, b2] m)

/-- `list_cons_ty_ok` after `intern_const`. -/
def consK8 (ty so b0 b1 b2 : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (l1, m) => consK9 p n ty so b0 b2 (l1.headD 0) (callW p n "mk_app" [l1.headD 0, b1] m)

/-- `list_cons_ty_ok` after `intern_bvar(2)`. -/
def consK7 (ty so li ps b0 b1 : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m) => consK8 p n ty so b0 b1 (b2.headD 0) (callW p n "intern_const" [li, ps] m)

/-- `list_cons_ty_ok` after `intern_bvar(1)`. -/
def consK6 (ty so li ps b0 : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m) => consK7 p n ty so li ps b0 (b1.headD 0) (callW p n "intern_bvar" [2] m)

/-- `list_cons_ty_ok` after `intern_bvar(0)`. -/
def consK5 (ty so li ps : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b0, m) => consK6 p n ty so li ps (b0.headD 0) (callW p n "intern_bvar" [1] m)

/-- `list_cons_ty_ok` after `pin_at(7)`. -/
def consK4 (ty so ps : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (i, m) => consK5 p n ty so (i.headD 0) ps (callW p n "intern_bvar" [0] m)

/-- `list_cons_ty_ok` after `str_ls1`. -/
def consK3 (ty so : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (l, m) => consK4 p n ty so (l.headD 0) (callW p n "pin_at" [7] m)

/-- `list_cons_ty_ok` after `str_param_sort`. -/
def consK2 (ty : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (s, m) => consK3 p n ty (s.tail.headD 0) (callW p n "str_ls1" [s.headD 0] m)

/-- `list_cons_ty_ok` after `str_cv`. -/
def consK1 : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c, m) => if c.tail.headD 0 ≠ 1 then some (0, m)
    else consK2 p n (c.tail.tail.headD 0)
      (callW p n "str_param_sort" [rdW (m.arr64 EREC) (c.headD 0)] m)

/-- **The model of `list_cons_ty_ok`.** -/
def consK0 (m : Mem) (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m) else consK1 p n (callW p n "str_cv" [q] m)

/-! ### One equation per arm (`list_ty_ok`'s spec; the prefix steps for the refinements) -/

section arms
variable (m : Mem) (g : List Word) (found q ty so li ps x l1 u1 f b r b0 b1 b2 d3 c3 X Y : Word)

theorem faEqK_s : faEqK X Y (some (g, m)) =
    some (if g.tail.headD 0 = X ∧ g.tail.tail.headD 0 = Y then 1 else 0, m) := rfl
theorem faEqA_f (h : ty >>> 28 ≠ 6) : faEqA p n m ty X Y = some (0, m) := by
  simp only [faEqA, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem faEqA_t (h : ty >>> 28 = 6) : faEqA p n m ty X Y = faEqK X Y (callW p n "e_view" [ty] m) := by
  simp only [faEqA, h, ne_eq, not_true_eq_false, ↓reduceIte]



theorem listK2_s : listK2 p n ty (some (g, m)) = faEqA p n m ty (g.tail.headD 0) (g.tail.headD 0) := rfl
theorem listK1_f (h : g.tail.headD 0 ≠ 1) : listK1 p n (some (g, m)) = some (0, m) := by
  simp only [listK1, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem listK1_t (h : g.tail.headD 0 = 1) : listK1 p n (some (g, m)) =
    listK2 p n (g.tail.tail.headD 0)
      (callW p n "str_param_sort" [rdW (m.arr64 EREC) (g.headD 0)] m) := by
  simp only [listK1, h, ne_eq, not_true_eq_false, ↓reduceIte]
theorem listK0_f (h : found = 0) : listK0 p n m found q = some (0, m) := by
  simp only [listK0, h, ↓reduceIte]
theorem listK0_t (h : found ≠ 0) : listK0 p n m found q = listK1 p n (callW p n "str_cv" [q] m) := by
  simp only [listK0, h, ↓reduceIte]

theorem nilK4_s : nilK4 p n ty so ps (some (g, m)) = nilA p n m ty so (g.headD 0) ps := rfl
theorem nilK3_s : nilK3 p n ty so (some (g, m)) =
    nilK4 p n ty so (g.headD 0) (callW p n "pin_at" [7] m) := rfl
theorem nilK2_s : nilK2 p n ty (some (g, m)) =
    nilK3 p n ty (g.tail.headD 0) (callW p n "str_ls1" [g.headD 0] m) := rfl

theorem consK10_s : consK10 p n ty so b0 d3 (some (g, m)) = consA p n m ty so b0 d3 (g.headD 0) := rfl
theorem consK9_s : consK9 p n ty so b0 b2 l1 (some (g, m)) =
    consK10 p n ty so b0 (g.headD 0) (callW p n "mk_app" [l1, b2] m) := rfl
theorem consK8_s : consK8 p n ty so b0 b1 b2 (some (g, m)) =
    consK9 p n ty so b0 b2 (g.headD 0) (callW p n "mk_app" [g.headD 0, b1] m) := rfl
theorem consK7_s : consK7 p n ty so li ps b0 b1 (some (g, m)) =
    consK8 p n ty so b0 b1 (g.headD 0) (callW p n "intern_const" [li, ps] m) := rfl
theorem consK6_s : consK6 p n ty so li ps b0 (some (g, m)) =
    consK7 p n ty so li ps b0 (g.headD 0) (callW p n "intern_bvar" [2] m) := rfl
theorem consK5_s : consK5 p n ty so li ps (some (g, m)) =
    consK6 p n ty so li ps (g.headD 0) (callW p n "intern_bvar" [1] m) := rfl
theorem consK4_s : consK4 p n ty so ps (some (g, m)) =
    consK5 p n ty so (g.headD 0) ps (callW p n "intern_bvar" [0] m) := rfl
theorem consK3_s : consK3 p n ty so (some (g, m)) =
    consK4 p n ty so (g.headD 0) (callW p n "pin_at" [7] m) := rfl
theorem consK2_s : consK2 p n ty (some (g, m)) =
    consK3 p n ty (g.tail.headD 0) (callW p n "str_ls1" [g.headD 0] m) := rfl

end arms
end model

theorem listTy_spec (p : Prog) (hp : p.lookup "list_ty_ok" = some listTyOkL) (n : Nat) (s₀ : St)
    (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "list_ty_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ listK0 p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, listTyOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "str_cv", callW_spec p n "str_param_sort", callW_spec p n "e_view"] <;>
    finish (gen := 20) [listK0_f, listK0_t, listK1_f, listK1_t, listK2_s, faEqA_f, faEqA_t, faEqK_s,
      rdW_eq,
      St.setLocs_mem']

set_option maxHeartbeats 1000000 in
theorem listNil_spec (p : Prog) (hp : p.lookup "list_nil_ty_ok" = some listNilTyOkL) (n : Nat)
    (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "list_nil_ty_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ nilK0 p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, listNilTyOkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "str_cv", callW_spec p n "str_param_sort", callW_spec p n "str_ls1",
    callW_spec p n "pin_at", callW_spec p n "e_view"] <;>
  simp_all [-UInt64.toNat_add, nilK0, nilK1, nilK2, nilK3, nilK4, nilA, nilAK, nilB, nilBK, nilC,
      nilCK, nilD, nilDK, EREC, BinOp.eval, getElem_rdW', Cmp.eval, LocEq,
      St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
      Locals.init_cons_succ, Sig.retVal, Sig.retOr]

set_option maxHeartbeats 1000000 in
theorem listCons_spec (p : Prog) (hp : p.lookup "list_cons_ty_ok" = some listConsTyOkL) (n : Nat)
    (s₀ : St) (found q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "list_cons_ty_ok" [found, q]
    ⦃fun r s' => LocEq s' s₀ ∧ consK0 p n s₀.mem found q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, listConsTyOkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "str_cv", callW_spec p n "str_param_sort", callW_spec p n "str_ls1",
    callW_spec p n "pin_at", callW_spec p n "intern_bvar", callW_spec p n "intern_const",
    callW_spec p n "mk_app", callW_spec p n "e_view"] <;>
  simp_all [-UInt64.toNat_add, consK0, consK1, consK2, consK3, consK4, consK5, consK6, consK7,
      consK8, consK9, consK10, consA, consAK, consB, consBK, faEqA, faEqK, EREC, BinOp.eval,
      getElem_rdW', Cmp.eval, LocEq,
      St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
      Locals.init_cons_succ, Sig.retVal, Sig.retOr]


/-! ## The tails' refinements -/

/-- `List.nil`'s argument: the bound variable `#0`, then the head comparison `c`. -/
def nilDT (x : EIdx) (c : Bool) : AM Bool :=
  if x.tag == ETag.bvar then do
    match ← view x with
    | .bvar 0 => pure c
    | _ => pure false
  else pure false

/-- `List.nil`'s head: the constant `List.{u}`. -/
def nilCT (f x : EIdx) (li : NIdx) (ps : LsIdx) : AM Bool :=
  if f.tag == ETag.const then do
    match ← view f with
    | .const l1 us1 => nilDT x (l1 == li && us1 == ps)
    | _ => pure false
  else pure false

/-- `List.nil`'s body: an application. -/
def nilBT (b : EIdx) (li : NIdx) (ps : LsIdx) : AM Bool :=
  if b.tag == ETag.app then do
    match ← view b with
    | .app f x => nilCT f x li ps
    | _ => pure false
  else pure false

theorem ite01_bne (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P ∧ Q then (1 : Word) else 0) != 0) = (decide P && decide Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

section oks
variable {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat} {m m' : Mem} {a : AState}
  (hR : ArenaR m a)
include hp hR

theorem nilD_ok {x l1 u1 li ps w : Word} (hx : HW x) (hl1 : HW l1) (hu1 : HW u1) (hli : HW li)
    (hps : HW ps) (h : nilD p n m x l1 u1 li ps = some (w, m')) :
    (nilDT (decE x) ((decI l1 : NIdx) == decI li && (decI u1 : LsIdx) == decI ps)).run a =
      .ok (w != 0, a) ∧ m' = m ∧ ResH [w] := by
  unfold nilD at h
  by_cases g0 : x >>> 28 ≠ 0
  · rw [if_pos g0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : ((decE x).tag == ETag.bvar) = false := by
      rw [slTagB x hx ETag.bvar 0 (by decide) rfl]; exact decide_eq_false g0
    refine ⟨?_, rfl, by unfold ResH HW; decide⟩
    simp only [nilDT, ht]; rfl
  rw [if_neg g0] at h
  have g0' : x >>> 28 = 0 := by simpa using g0
  cases hc : callW p n "e_view" [x] m with
  | none => rw [hc] at h; cases h
  | some q =>
  obtain ⟨g, m₁⟩ := q
  rw [hc] at h; simp only [nilDK] at h
  obtain ⟨rfl, v, hv, hvr, hg⟩ := eView_callW_view hp hR hc
  have hv0 := slViewR_bvar hvr (by rw [hg, g0'])
  have ht : ((decE x).tag == ETag.bvar) = true := by
    rw [slTagB x hx ETag.bvar 0 (by decide) rfl]; exact decide_eq_true g0'
  rw [hv0] at hv
  by_cases ci : g.tail.headD 0 = 0
  · rw [if_neg (fun h => h ci)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, rfl, resH_ite01 _⟩
    have h0 : (g.tail.headD 0).toNat = 0 := by rw [ci]; rfl
    rw [h0] at hv
    simp only [nilDT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
    rw [decI_beq _ _ hl1 hli, decI_beq _ _ hu1 hps, ite01_bne]; rfl
  · rw [if_pos ci] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, rfl, by unfold ResH HW; decide⟩
    obtain ⟨k, hk⟩ : ∃ k, (g.tail.headD 0).toNat = k + 1 :=
      ⟨(g.tail.headD 0).toNat - 1, by
        have : (g.tail.headD 0).toNat ≠ 0 := fun h0 => ci (UInt64.toNat_inj.mp (by rw [h0]; rfl))
        omega⟩
    rw [hk] at hv
    simp only [nilDT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; rfl

theorem nilC_ok {f x li ps w : Word} (hf : HW f) (hx : HW x) (hli : HW li) (hps : HW ps)
    (h : nilC p n m f x li ps = some (w, m')) :
    (nilCT (decE f) (decE x) (decI li) (decI ps)).run a = .ok (w != 0, a) ∧ m' = m ∧ ResH [w] := by
  unfold nilC at h
  by_cases g3 : f >>> 28 ≠ 3
  · rw [if_pos g3] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : ((decE f).tag == ETag.const) = false := by
      rw [slTagB f hf ETag.const 3 (by decide) rfl]; exact decide_eq_false g3
    refine ⟨?_, rfl, by unfold ResH HW; decide⟩
    simp only [nilCT, ht]; rfl
  rw [if_neg g3] at h
  have g3' : f >>> 28 = 3 := by simpa using g3
  cases hc : callW p n "e_view" [f] m with
  | none => rw [hc] at h; cases h
  | some q =>
  obtain ⟨g, m₁⟩ := q
  rw [hc] at h; simp only [nilCK] at h
  obtain ⟨rfl, v, hv, hvr, hg⟩ := eView_callW_view hp hR hc
  obtain ⟨rfl, h1, h2⟩ := slViewR_const hvr (by rw [hg, g3'])
  have ht : ((decE f).tag == ETag.const) = true := by
    rw [slTagB f hf ETag.const 3 (by decide) rfl]; exact decide_eq_true g3'
  obtain ⟨hr, hm, hres⟩ := nilD_ok hp hR hx h1 h2 hli hps h
  refine ⟨?_, hm, hres⟩
  simp only [nilCT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  exact hr

theorem nilB_ok {b li ps w : Word} (hb : HW b) (hli : HW li) (hps : HW ps)
    (h : nilB p n m b li ps = some (w, m')) :
    (nilBT (decE b) (decI li) (decI ps)).run a = .ok (w != 0, a) ∧ m' = m ∧ ResH [w] := by
  unfold nilB at h
  by_cases g4 : b >>> 28 ≠ 4
  · rw [if_pos g4] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht : ((decE b).tag == ETag.app) = false := by
      rw [slTagB b hb ETag.app 4 (by decide) rfl]; exact decide_eq_false g4
    refine ⟨?_, rfl, by unfold ResH HW; decide⟩
    simp only [nilBT, ht]; rfl
  rw [if_neg g4] at h
  have g4' : b >>> 28 = 4 := by simpa using g4
  cases hc : callW p n "e_view" [b] m with
  | none => rw [hc] at h; cases h
  | some q =>
  obtain ⟨g, m₁⟩ := q
  rw [hc] at h; simp only [nilBK] at h
  obtain ⟨rfl, v, hv, hvr, hg⟩ := eView_callW_view hp hR hc
  obtain ⟨rfl, h1, h2⟩ := slViewR_app hvr (by rw [hg, g4'])
  have ht : ((decE b).tag == ETag.app) = true := by
    rw [slTagB b hb ETag.app 4 (by decide) rfl]; exact decide_eq_true g4'
  obtain ⟨hr, hm, hres⟩ := nilC_ok hp hR h1 h2 hli hps h
  refine ⟨?_, hm, hres⟩
  simp only [nilBT, ht, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  exact hr

end oks

theorem faEqA_eq (p : Prog) (n : Nat) (m : Mem) (ty X Y : Word) :
    faEqA p n m ty X Y = faEqW p n m ty X Y := by
  unfold faEqA faEqW
  split
  · rfl
  · cases callW p n "e_view" [ty] m with
    | none => rfl
    | some q => obtain ⟨g, m₁⟩ := q; rfl

theorem nilA_eq (p : Prog) (n : Nat) (m : Mem) (ty so li ps : Word) :
    nilA p n m ty so li ps = faGuardW (fun b m => nilB p n m b li ps) p n m ty so := by
  unfold nilA faGuardW
  split
  · rfl
  · cases callW p n "e_view" [ty] m with
    | none => rfl
    | some q => obtain ⟨g, m₁⟩ := q; rfl

theorem consB_eq (p : Prog) (n : Nat) (m : Mem) (r b0 d3 c3 : Word) :
    consB p n m r b0 d3 c3 = faGuardW (fun r2 m => faEqA p n m r2 d3 c3) p n m r b0 := by
  unfold consB faGuardW
  split
  · rfl
  · cases callW p n "e_view" [r] m with
    | none => rfl
    | some q => obtain ⟨g, m₁⟩ := q; rfl

theorem consA_eq (p : Prog) (n : Nat) (m : Mem) (ty so b0 d3 c3 : Word) :
    consA p n m ty so b0 d3 c3 = faGuardW (fun r1 m => consB p n m r1 b0 d3 c3) p n m ty so := by
  unfold consA faGuardW
  split
  · rfl
  · cases callW p n "e_view" [ty] m with
    | none => rfl
    | some q => obtain ⟨g, m₁⟩ := q; rfl

section oks2
variable {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat} {m m' : Mem} {a : AState}
  (hR : ArenaR m a)
include hp hR

theorem nilA_ok {ty so li ps w : Word} (hty : HW ty) (hso : HW so) (hli : HW li) (hps : HW ps)
    (h : nilA p n m ty so li ps = some (w, m')) :
    (faGuardT (fun b => nilBT b (decI li) (decI ps)) (decE ty) (decE so)).run a =
      .ok (w != 0, a) ∧ m' = m ∧ ResH [w] :=
  faGuard_ok (k := fun b m => nilB p n m b li ps) (kT := fun b => nilBT b (decI li) (decI ps))
    hp hR (fun _ _ _ hb hk => nilB_ok hp hR hb hli hps hk) hty hso
    ((nilA_eq p n m ty so li ps).symm.trans h)

theorem consB_ok {r b0 d3 c3 w : Word} (hr : HW r) (hb0 : HW b0) (hd3 : HW d3) (hc3 : HW c3)
    (h : consB p n m r b0 d3 c3 = some (w, m')) :
    (faGuardT (fun r2 => faEqT r2 (decE d3) (decE c3)) (decE r) (decE b0)).run a =
      .ok (w != 0, a) ∧ m' = m ∧ ResH [w] :=
  faGuard_ok (k := fun r2 m => faEqA p n m r2 d3 c3) (kT := fun r2 => faEqT r2 (decE d3) (decE c3))
    hp hR (fun b _ _ hb hk => faEqW_ok hp hR hb hd3 hc3 ((faEqA_eq p n m b d3 c3).symm.trans hk))
    hr hb0 ((consB_eq p n m r b0 d3 c3).symm.trans h)

theorem consA_ok {ty so b0 d3 c3 w : Word} (hty : HW ty) (hso : HW so) (hb0 : HW b0) (hd3 : HW d3)
    (hc3 : HW c3) (h : consA p n m ty so b0 d3 c3 = some (w, m')) :
    (faGuardT (fun r1 => faGuardT (fun r2 => faEqT r2 (decE d3) (decE c3)) r1 (decE b0))
      (decE ty) (decE so)).run a = .ok (w != 0, a) ∧ m' = m ∧ ResH [w] :=
  faGuard_ok (k := fun r1 m => consB p n m r1 b0 d3 c3)
    (kT := fun r1 => faGuardT (fun r2 => faEqT r2 (decE d3) (decE c3)) r1 (decE b0))
    hp hR (fun _ _ _ hb hk => consB_ok hp hR hb hb0 hd3 hc3 hk) hty hso
    ((consA_eq p n m ty so b0 d3 c3).symm.trans h)

end oks2

/-! ## The found constant's level-parameter names read back -/

/-- **A found constant's level-parameter names read back** (`StoreDen.constLps`). -/
theorem cv_lps {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}
    {m : Mem} {a : AState} {M : ModeMaps} (hS : CoreS dn m a vis fe M eb) {ci : IConstantInfo}
    (hfe : ∃ c, fe.find? c = some ci) :
    ∃ ks, ci.toConstantVal.levelParams.mapM (denoteN a.store.ns) = some ks := by
  obtain ⟨c, hc⟩ := hfe
  exact hS.den.constLps c ci hc

/-- The one level parameter of a found constant reads back (`cv_lps`). -/
theorem lp_den {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}
    {m : Mem} {a : AState} {M : ModeMaps} (hS : CoreS dn m a vis fe M eb) {ci : IConstantInfo}
    (hfe : ∃ c, fe.find? c = some ci) {pn : Word}
    (hlp : ci.toConstantVal.levelParams = [decI pn]) :
    ∃ x, denoteN a.store.ls.ns (decI pn) = some x := by
  obtain ⟨ks, hks⟩ := cv_lps hS hfe
  rw [hlp] at hks
  cases hx : denoteN a.store.ns (decI pn) with
  | none => simp [List.mapM_cons, hx] at hks
  | some x => exact ⟨x, hx⟩

/-- The twins' common prefix: the constant's value, one level parameter, its sort; then `k`. -/
def listPreT (k : IConstantVal → LIdx → EIdx → AM Bool) : Option IConstantInfo → AM Bool
  | some ci => do
    let cv := ci.toConstantVal
    match cv.levelParams with
    | [p] => do
      let pl ← internLNode (.param p)
      let sp ← internLNode (.succ pl)
      let sort ← internE (.sort sp)
      k cv pl sort
    | _ => pure false
  | none => pure false

/-- The models' common prefix: `str_cv`, one level parameter, `str_param_sort`; then `K2`. -/
def listPreW (p : Prog) (n : Nat) (K2 : Word → Option (List Word × Mem) → Option (Word × Mem)) (m : Mem)
    (found q : Word) : Option (Word × Mem) :=
  if found = 0 then some (0, m) else
  match callW p n "str_cv" [q] m with
  | none => none
  | some (c, m₁) => if c.tail.headD 0 ≠ 1 then some (0, m₁)
    else K2 (c.tail.tail.headD 0) (callW p n "str_param_sort" [rdW (m₁.arr64 EREC) (c.headD 0)] m₁)

section calls
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

/-- **`str_param_sort` as the prefix of a twin `do` block**: the level `param pn`, its successor,
the sort, then any continuation `k` on the level and the sort. -/
theorem paramSort_run (hS : CoreS dn m a vis fe M eb) {pn : Word} (hpn : HW pn)
    (hpd : ∃ x, denoteN a.store.ls.ns (decI pn) = some x) {r₁ : List Word}
    {m₁ : Mem} (h : callW p n "str_param_sort" [pn] m = some (r₁, m₁)) {β : Type} [Inhabited β]
    {k : LIdx → EIdx → AM β} {dec : List Word → β} {ok : List Word → Prop}
    (hk : ∀ M' a', HW (r₁.headD 0) → HW (r₁.tail.headD 0) →
      (∃ l, denoteL a'.store.ls (decI (r₁.headD 0)) = some l) → CoreS dn m₁ a' vis fe M' eb →
      CoreRef (k (decI (r₁.headD 0)) (decE (r₁.tail.headD 0))) a' dec dn m₁ vis fe M' eb r m' ok) :
    CoreRef (do
      let pl ← internLNode (.param (decI pn))
      let sp ← internLNode (.succ pl)
      let sort ← internE (.sort sp)
      k pl sort) a dec dn m vis fe M eb r m' ok := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strParamSort_spec p hp.strParamSort n _ pn) h
  unfold psW at hW
  rcases h1 : callW p n "intern_param" [pn] m with _ | ⟨x, n₁⟩
    <;> simp only [h1, reduceCtorEq] at hW
  rcases h2 : callW p n "intern_succ" [x.headD 0] n₁ with _ | ⟨y, n₂⟩
    <;> simp only [h2, reduceCtorEq] at hW
  rcases h3 : callW p n "intern_sort" [y.headD 0] n₂ with _ | ⟨z, n₃⟩
    <;> simp only [h3, reduceCtorEq] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, hm⟩ := hW
  rw [hm] at h3
  have R1 := param_call p hp hS hpn h1 hpd
  have hd1 := lnode_den (v := .param (decI pn)) hS
    (fun c hc => by simp [LNodeView.lchildren] at hc)
    (fun n hn => by
      simp only [LNodeView.nchildren, List.mem_cons, List.mem_nil_iff, or_false] at hn
      subst hn; exact hpd) R1 rfl
  refine coreRef_bind R1 (fun M₁ hS₁ => ?_)
  have R2 := succ_call p hp hS₁ R1.2.2.2 h2 hd1
  have hd2 := lnode_den (v := .succ (decLv x)) hS₁
    (fun c hc => by
      simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc
      subst hc; exact hd1)
    (fun n hn => by simp [LNodeView.nchildren] at hn) R2 rfl
  refine coreRef_bind R2 (fun M₂ hS₂ => ?_)
  have R3 := sort_call p hp hS₂ R2.2.2.2 h3 hd2
  have hp3 := ls_den (op := internE (.sort (decLv y))) (lnode_lvl (v := .succ (decLv x)) hd1 R2 rfl)
    (keeps_cpl_internSort _) R3 rfl
  refine coreRef_bind R3 (fun M₃ hS₃ => ?_)
  exact hk M₃ _ R1.2.2.2 R3.2.2.2 hp3 hS₃

/-- **The common prefix of the three tests refines the twins'**, given the tail `k` from the
sort on. -/
theorem listPre_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (hfe : ∀ ci, decFound dn m found q = some ci → ∃ x, fe.find? x = some ci)
    {K2 : Word → Option (List Word × Mem) → Option (Word × Mem)}
    {k : IConstantVal → LIdx → EIdx → AM Bool}
    (hn : ∀ ty, K2 ty none = none) (hW : listPreW p n K2 m found q = some (r.headD 0, m'))
    (hk : ∀ (cv : IConstantVal) (ty : Word) (s : List Word) (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState),
      cv.type = decE ty → HW ty → HW (s.headD 0) → HW (s.tail.headD 0) →
      (∃ l, denoteL a₂.store.ls (decI (s.headD 0)) = some l) → CoreS dn m₂ a₂ vis fe M₂ eb →
      K2 ty (some (s, m₂)) = some (r.headD 0, m') →
      CoreRef (k cv (decI (s.headD 0)) (decE (s.tail.headD 0))) a₂ decBool dn m₂ vis fe M₂ eb r m') :
    CoreRef (listPreT k (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  by_cases hf0 : found = 0
  · simp only [listPreW, hf0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    simp only [decFound, hf0, ↓reduceIte]
    exact cref_run (v := false) rfl (coreAfter_refl hS) (by rw [decBool, ← hr]; rfl)
      (by unfold ResH HW; rw [← hr]; decide)
  simp only [listPreW, hf0, ↓reduceIte] at hW
  obtain ⟨ci, hci⟩ := hdec hf0
  rw [show decFound dn m found q = some ci by simp only [decFound, hf0, ↓reduceIte, hci]]
  rcases h1 : callW p n "str_cv" [q] m with _ | ⟨c, m₁⟩ <;> simp only [h1, reduceCtorEq] at hW
  obtain ⟨hm₁, hsl, hlen, hty, hhw⟩ := cv_call p hp hS hci h1
  subst m₁
  have hfe' := hfe ci (by simp only [decFound, hf0, ↓reduceIte, hci])
  have hden := fun pn (hlp : ci.toConstantVal.levelParams = [decI pn]) => lp_den hS hfe' hlp
  dsimp only [listPreT]
  generalize ci.toConstantVal = cv at hsl hlen hty hden
  by_cases hl : c.tail.headD 0 ≠ 1
  · simp only [hl, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    split
    · rename_i x hx; exact absurd hx (lp_ne hlen hl x)
    · exact coreRef_ret hS (by rw [decBool, ← hr]; rfl) (by unfold ResH HW; rw [← hr]; decide)
  have hl' : c.tail.headD 0 = 1 := by simpa using hl
  simp only [hl', ne_eq, not_true_eq_false, ↓reduceIte] at hW
  obtain ⟨hlp, hw⟩ := lp_one hsl hl'
  rw [hlp]
  dsimp only
  rcases h2 : callW p n "str_param_sort" [rdW (m.arr64 EREC) (c.headD 0)] m with _ | ⟨s, m₂⟩
  · rw [h2, hn] at hW; cases hW
  rw [h2] at hW
  refine paramSort_run p hp hS hw (hden _ hlp) h2
    (fun M₂ a₂ hpl hso hpd₂ hS₂ => hk cv _ s m₂ M₂ a₂ hty hhw hpl hso hpd₂ hS₂ hW)

/-- **`list_ty_ok` refines `listTyOk`.** -/
@[refines ConRon.Arena.listTyOk]
theorem listTyOk_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (hfe : ∀ ci, decFound dn m found q = some ci → ∃ x, fe.find? x = some ci)
    (h : callW p n "list_ty_ok" [found, q] m = some (r, m')) :
    CoreRef (listTyOk (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (listTy_spec p hp.listTyOk n _ found q) h
  refine listPre_call (K2 := listK2 p n) p hp hS hdec hfe (fun _ => rfl) hW
    fun cv ty s m₂ M₂ a₂ hty hhw hpl hso hpd₂ hS₂ hW => ?_
  rw [listK2_s, faEqA_eq] at hW
  rw [hty]
  obtain ⟨hrun₂, hm, hres⟩ := faEqW_ok hp.eView hS₂.arena.1 hhw hso hso hW
  rw [hm]
  exact cref_run hrun₂ (coreAfter_refl hS₂) rfl hres

/-- **`list_nil_ty_ok` refines `listNilTyOk`.** -/
@[refines ConRon.Arena.listNilTyOk]
theorem listNilTyOk_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (hfe : ∀ ci, decFound dn m found q = some ci → ∃ x, fe.find? x = some ci)
    (h : callW p n "list_nil_ty_ok" [found, q] m = some (r, m')) :
    CoreRef (listNilTyOk (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (listNil_spec p hp.listNilTyOk n _ found q) h
  refine listPre_call (K2 := nilK2 p n) p hp hS hdec hfe (fun _ => rfl) hW
    fun cv ty s m₂ M₂ a₂ hty hhw hpl hso hpd₂ hS₂ hW => ?_
  rw [nilK2_s] at hW
  cases h3 : callW p n "str_ls1" [s.headD 0] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨l, m₃⟩ := q₃
  rw [h3, nilK3_s] at hW
  have R3 := ls1_call p hp hS₂ hpl hpd₂ h3
  refine coreRef_bind R3 (fun M₃ hS₃ => ?_)
  cases h4 : callW p n "pin_at" [7] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨i, m₄⟩ := q₄
  rw [h4, nilK4_s, nilA_eq] at hW
  obtain ⟨hm4, -, -, hi⟩ := callW_pinAt p hp.pinAt n m₃ 7 i m₄ h4
  subst hm4
  have hiw : HW (i.headD 0) := by rw [hi]; exact hS₃.pins.names_lt 7 (by decide)
  refine coreRef_bind (T₁ := pinList) (dec₁ := fun r => decI (r.headD 0))
    (cref_run (ok := ResH) ?_ (coreAfter_refl hS₃) rfl hiw) (fun M₄ hS₄ => ?_)
  · rw [hi]; exact pinAt_run hS₃.pins 7 (by decide)
  rw [hty]
  obtain ⟨hrun₄, hm, hres⟩ := nilA_ok hp.eView hS₄.arena.1 hhw hso hiw R3.2.2.2 hW
  rw [hm]
  exact cref_run hrun₄ (coreAfter_refl hS₄) rfl hres

/-- **`list_cons_ty_ok` refines `listConsTyOk`.** -/
@[refines ConRon.Arena.listConsTyOk]
theorem listConsTyOk_call (hS : CoreS dn m a vis fe M eb) {found q : Word}
    (hdec : found ≠ 0 → ∃ ci, decCI (erecP m) dn q.toNat = some ci)
    (hfe : ∀ ci, decFound dn m found q = some ci → ∃ x, fe.find? x = some ci)
    (h : callW p n "list_cons_ty_ok" [found, q] m = some (r, m')) :
    CoreRef (listConsTyOk (decFound dn m found q)) a decBool dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (listCons_spec p hp.listConsTyOk n _ found q) h
  refine listPre_call (K2 := consK2 p n) p hp hS hdec hfe (fun _ => rfl) hW
    fun cv ty s m₂ M₂ a₂ hty hhw hpl hso hpd₂ hS₂ hW => ?_
  rw [consK2_s] at hW
  cases h3 : callW p n "str_ls1" [s.headD 0] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨l, m₃⟩ := q₃
  rw [h3, consK3_s] at hW
  have R3 := ls1_call p hp hS₂ hpl hpd₂ h3
  have hl3 := ls1_den p hp hS₂ hpl h3 hpd₂
  refine coreRef_bind R3 (fun M₃ hS₃ => ?_)
  cases h4 : callW p n "pin_at" [7] m₃ with
  | none => rw [h4] at hW; cases hW
  | some q₄ =>
  obtain ⟨i, m₄⟩ := q₄
  rw [h4, consK4_s] at hW
  obtain ⟨hm4, -, -, hi⟩ := callW_pinAt p hp.pinAt n m₃ 7 i m₄ h4
  rw [hm4] at hW
  have hiw : HW (i.headD 0) := by rw [hi]; exact hS₃.pins.names_lt 7 (by decide)
  refine coreRef_bind (T₁ := pinList) (dec₁ := fun r => decI (r.headD 0))
    (cref_run (ok := ResH) ?_ (coreAfter_refl hS₃) rfl hiw) (fun M₄ hS₄ => ?_)
  · rw [hi]; exact pinAt_run hS₃.pins 7 (by decide)
  cases h5 : callW p n "intern_bvar" [0] m₃ with
  | none => rw [h5] at hW; cases hW
  | some q₅ =>
  obtain ⟨x0, m₅⟩ := q₅
  rw [h5, consK5_s] at hW
  have R5 := bvar_call p hp hS₄ h5
  refine coreRef_bind R5 (fun M₅ hS₅ => ?_)
  cases h6 : callW p n "intern_bvar" [1] m₅ with
  | none => rw [h6] at hW; cases hW
  | some q₆ =>
  obtain ⟨x1, m₆⟩ := q₆
  rw [h6, consK6_s] at hW
  have R6 := bvar_call p hp hS₅ h6
  refine coreRef_bind R6 (fun M₆ hS₆ => ?_)
  cases h7 : callW p n "intern_bvar" [2] m₆ with
  | none => rw [h7] at hW; cases hW
  | some q₇ =>
  obtain ⟨x2, m₇⟩ := q₇
  rw [h7, consK7_s] at hW
  have R7 := bvar_call p hp hS₆ h7
  refine coreRef_bind R7 (fun M₇ hS₇ => ?_)
  cases h8 : callW p n "intern_const" [i.headD 0, l.headD 0] m₇ with
  | none => rw [h8] at hW; cases hW
  | some q₈ =>
  obtain ⟨y1, m₈⟩ := q₈
  rw [h8, consK8_s] at hW
  have hl7 := lss_den (op := internE (.bvar 2)) (lss_den (op := internE (.bvar 1))
    (lss_den (op := internE (.bvar 0)) (lss_pin (op := pinList) hl3 hS₃.pins (i := 7) (by decide) rfl)
      (keeps_cpl_internBVar _) R5 rfl) (keeps_cpl_internBVar _) R6 rfl) (keeps_cpl_internBVar _) R7 rfl
  have R8 := const_call p hp hS₇ hiw R3.2.2.2 h8 hl7
  refine coreRef_bind R8 (fun M₈ hS₈ => ?_)
  cases h9 : callW p n "mk_app" [y1.headD 0, x1.headD 0] m₈ with
  | none => rw [h9] at hW; cases hW
  | some q₉ =>
  obtain ⟨y2, m₉⟩ := q₉
  rw [h9, consK9_s] at hW
  have R9 := app_call p hp hS₈ h9
  refine coreRef_bind R9 (fun M₉ hS₉ => ?_)
  cases h10 : callW p n "mk_app" [y1.headD 0, x2.headD 0] m₉ with
  | none => rw [h10] at hW; cases hW
  | some q₁₀ =>
  obtain ⟨y3, m₁₀⟩ := q₁₀
  rw [h10, consK10_s, consA_eq] at hW
  have R10 := app_call p hp hS₉ h10
  refine coreRef_bind R10 (fun M₁₀ hS₁₀ => ?_)
  rw [hty]
  obtain ⟨hrun₁₀, hm, hres⟩ := consA_ok hp.eView hS₁₀.arena.1 hhw hso R5.2.2.2 R9.2.2.2 R10.2.2.2 hW
  rw [hm]
  exact cref_run hrun₁₀ (coreAfter_refl hS₁₀) rfl hres

end calls

end L.Arena
