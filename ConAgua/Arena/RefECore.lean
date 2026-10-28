import ConAgua.Arena.Verdict

/-!
# The unified refinements of core functions

The `RefE` kit (`Verdict.lean`) for the functions that the knot's slots call (`whnf`, `infer`,
`defeq` and their pieces): their ok halves are `CoreRef`s (`WhnfBase.lean`), the twin's run with
the relation after it, the result decoded and valid. `CorePost` is that post as a structure
(`RefE … (CorePost …)`), and `RefE.coreSpec` / `CoreSpec.of_refE` give the knot's `CoreSpec` from
it. An arm that leaves a slice on the stack has `GrowPost` (`CoreAfterG`: the stack below the old
top kept, the top possibly grown) and `GrowRef`. A callee's ok run is threaded by
`RefE.bind_core` (kept stack) and `RefE.bind_grow`/`bind_growK` (grown).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## A kept stack: `CorePost` -/

/-- What a core function's run `v = (r, m)` from `m₀` gives besides the twin's result `y` and
final state `a'`: the relation after it, the result words decoded, their validity. -/
structure CorePost {α : Type} (dec : List Word → α) (dn : NIdx → Option ConLeche.Name) (m₀ : Mem)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop)
    (v : List Word × Mem) (y : α) (a' : AState) : Prop where
  after : CoreAfter dn m₀ v.2 a' vis fe M eb
  res : y = dec v.1
  valid : ok v.1

section corePost
open Std.WP
variable {α : Type} [Inhabited α] {T : AM α} {a : AState} {dec : List Word → α}
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
  {ok : List Word → Prop} {G Gs : Prop} {p : Prog} {n : Nat} {f : FnName} {args : List Word}
  {s₀ : St} {fx : Except Err (List Word × Mem)}

theorem CorePost.coreRef {m₀ m : Mem} {r : List Word} {y : α} {a' : AState}
    (hT : T.run a = .ok (y, a')) (h : CorePost dec dn m₀ vis fe M eb ok (r, m) y a') :
    CoreRef T a dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
  exact ⟨hok, hst ▸ h.after, hres.trans h.res, h.valid⟩

/-- The ok half as the core spec of the call. -/
theorem RefE.coreSpec
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ fx = .ok (r, s'.mem); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a (CorePost dec dn s₀.mem vis fe M eb ok)) :
    CoreSpec p n f args T dec s₀ a dn vis fe M eb ok :=
  L.M.triple_of_run fun _ _ _ hp hr => by
    obtain ⟨hl, _, _, hT, hR⟩ := L.M.of_run' (P := fun s => s = s₀) hp hr (RefE.triple hs h)
    exact ⟨hl, hR.coreRef hT⟩

end corePost

/-- A `CorePost` from a `CoreRef` (a callee's ok half). -/
theorem CoreRef.post {α : Type} [Inhabited α] {T : AM α} {a₀ : AState}
    {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok : List Word → Prop} {r : List Word}
    (h : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) :
    T.run a₀ = .ok (AM.res T a₀, AM.st T a₀) ∧
      CorePost dec dn m₀ vis fe M eb ok (r, m) (AM.res T a₀) (AM.st T a₀) :=
  ⟨AM.run_of_ok _ _ h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- A leaf: the twin returns at the start's state, the relation holds there. -/
theorem CorePost.ret {α : Type} {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok : List Word → Prop}
    {r : List Word} {y : α} (hS : CoreS dn m a vis fe M eb) (hy : y = dec r) (hr : ok r) :
    CorePost dec dn m vis fe M eb ok (r, m) y a :=
  ⟨⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hy, hr⟩

/-- **A core callee's ok run, then the rest**, both outcomes: the rest from the callee's state,
at any maps of the relation there, the stack kept across the callee. -/
theorem RefE.bind_core {α β γ : Type} [Inhabited γ] {G : Prop} {x : Except Err α} {T₁ : AM γ}
    {f : γ → AM β} {a₀ : AState} {dec₁ : List Word → γ} {dec : List Word → β}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r₁ : List Word} {ok₁ ok : List Word → Prop} {w : α → List Word × Mem}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackKept m₀ m₁ →
      RefE G x (f (dec₁ r₁)) (AM.st T₁ a₀)
        (fun v y a' => CorePost dec dn m₁ vis fe M' eb ok (w v) y a')) :
    RefE G x (T₁ >>= f) a₀ (fun v y a' => CorePost dec dn m₀ vis fe M eb ok (w v) y a') := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  exact RefE.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1])
    ((h₂ M' hS hSt).mono fun _ _ _ h => ⟨CoreAfter.comp hK hSt h.after, h.res, h.valid⟩)

/-- **The ok half of a unified core function** as its `CoreSpec`, for a model whose ok value is not
the pair `(r, m)` itself: `w` reads it back as the results and the memory (`RefE.coreSpec` for
`w = id`). -/
theorem CoreSpec.of_refE {α β : Type} [Inhabited β] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {s₀ : St} {Gs G : Prop} {fx : Except Err α} {V : List Word → St → α}
    {T : AM β} {a₀ : AState} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok : List Word → Prop} {w : α → List Word × Mem}
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a₀ (fun v y a' => CorePost dec dn s₀.mem vis fe M eb ok (w v) y a'))
    (hw : ∀ r s', (w (V r s')).2 = s'.mem ∧ dec (w (V r s')).1 = dec r ∧ (ok (w (V r s')).1 → ok r)) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok := by
  refine L.M.triple_of_run fun _ r s' hp hr => ?_
  obtain ⟨hl, y, a', hrun, hR⟩ := L.M.of_run (P := fun s => s = s₀) hp hr (RefE.triple hs h)
  obtain ⟨hm, hd, ho⟩ := hw r s'
  exact ⟨hl, CorePost.coreRef hrun ⟨hm ▸ hR.after, hR.res.trans hd, ho hR.valid⟩⟩

/-! ## Runs that leave their pushed slice on the stack -/

/-- **After a core run that left a slice on the stack**: as `CoreAfter`, the stack below the old top
kept, the top possibly grown. -/
def CoreAfterG (dn : NIdx → Option ConLeche.Name) (m₀ m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) : Prop :=
  ∃ M', CoreS dn m a vis fe M' eb ∧ KeptAll M M' eb ∧ StackGrew m₀ m

theorem CoreAfter.toG {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (h : CoreAfter dn m₀ m a vis fe M eb) :
    CoreAfterG dn m₀ m a vis fe M eb :=
  let ⟨M', hS, hK, hSt⟩ := h
  ⟨M', hS, hK, hSt.toGrew⟩

/-- `CoreRef` with `CoreAfterG`. -/
def GrowRef {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (r : List Word) (m : Mem) (ok : List Word → Prop := ResH) : Prop :=
  AM.ok T a₀ ∧ CoreAfterG dn m₀ m (AM.st T a₀) vis fe M eb ∧ AM.res T a₀ = dec r ∧ ok r

/-- `CorePost` with the stack grown (`CoreAfterG`, an arm that leaves a slice on the stack): what
a run `v = (r, m)` from `m₀` gives besides the twin's result `y` and final state `a'`. -/
structure GrowPost {α : Type} (dec : List Word → α) (dn : NIdx → Option ConLeche.Name) (m₀ : Mem)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop)
    (v : List Word × Mem) (y : α) (a' : AState) : Prop where
  after : CoreAfterG dn m₀ v.2 a' vis fe M eb
  res : y = dec v.1
  valid : ok v.1

theorem GrowPost.growRef {α : Type} [Inhabited α] {T : AM α} {a : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop} {m₀ m : Mem} {r : List Word} {y : α} {a' : AState}
    (hT : T.run a = .ok (y, a')) (h : GrowPost dec dn m₀ vis fe M eb ok (r, m) y a') :
    GrowRef T a dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
  exact ⟨hok, hst ▸ h.after, hres.trans h.res, h.valid⟩

/-- A run that ends with a pure answer `w`: its result list. -/
theorem CoreAfterG.compK {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m₂ : Mem} {a₂ : AState}
    {vis : Word} {fe : IFEnv} {M M' : ModeMaps} {eb : Word}
    (hK : KeptAll M M' eb) (hSt : StackGrew m₀ m₁)
    (h₂ : CoreAfterG dn m₁ m₂ a₂ vis fe M' eb) : CoreAfterG dn m₀ m₂ a₂ vis fe M eb := by
  obtain ⟨M'', hS', hK', hSt'⟩ := h₂
  exact ⟨M'', hS', hK.trans hK', hSt.trans hSt'⟩

/-- The ok half at a callee's run (`callW`), as `GrowRef`. -/
theorem RefE.growRefW {α : Type} [Inhabited α] {T : AM α} {a : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop} {G Gs : Prop} {p : Prog} {n : Nat} {f : FnName} {args : List Word}
    {s₀ : St} {fx : Except Err (List Word × Mem)}
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ fx = .ok (r, s'.mem); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a (GrowPost dec dn s₀.mem vis fe M eb ok)) {r : List Word} {m' : Mem}
    (hc : callW p n f args s₀.mem = some (r, m')) :
    GrowRef T a dec dn s₀.mem vis fe M eb r m' ok := by
  obtain ⟨s', rfl, -, y, a', hT, hR⟩ := RefE.run_okW hs h hc
  exact hR.growRef hT

/-- The arm's result word is the callee's (a tail call), after a run that kept the stack from `m₀`
to `m₁` (`hK`, `hSt`). -/
theorem GrowPost.of_tail {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv}
    {M M' : ModeMaps} {eb : Word} (hK : KeptAll M M' eb) (hSt : StackGrew m₀ m₁)
    (v : List Word × Mem) (y : EIdx) (a' : AState) (h : GrowPost decH dn m₁ vis fe M' eb ResH v y a') :
    GrowPost decH dn m₀ vis fe M eb ResH ([v.1.headD 0], v.2) y a' :=
  ⟨CoreAfterG.compK hK hSt h.after, h.res, h.valid⟩

theorem GrowPost.of_core {α : Type} {dec : List Word → α} {dn : NIdx → Option ConLeche.Name}
    {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok : List Word → Prop}
    {r : List Word} {y : α} {a' : AState} (h : CorePost dec dn m₀ vis fe M eb ok (r, m) y a') :
    GrowPost dec dn m₀ vis fe M eb ok (r, m) y a' :=
  let ⟨M', hS, hK, hSt⟩ := h.after
  ⟨⟨M', hS, hK, hSt.toGrew⟩, h.res, h.valid⟩

/-- A growing callee's ok run, then the rest, both outcomes. -/
theorem RefE.bind_grow {α β γ : Type} [Inhabited γ] {G : Prop} {x : Except Err α} {T₁ : AM γ}
    {f : γ → AM β} {a₀ : AState} {dec₁ : List Word → γ} {dec : List Word → β}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r₁ : List Word} {ok₁ ok : List Word → Prop} {w : α → List Word × Mem}
    (h₁ : GrowRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackGrew m₀ m₁ →
      RefE G x (f (dec₁ r₁)) (AM.st T₁ a₀)
        (fun v y a' => GrowPost dec dn m₁ vis fe M' eb ok (w v) y a')) :
    RefE G x (T₁ >>= f) a₀ (fun v y a' => GrowPost dec dn m₀ vis fe M eb ok (w v) y a') := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  exact RefE.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1])
    ((h₂ M' hS hSt).mono fun _ _ _ h =>
      let ⟨M'', hS'', hK'', hSt''⟩ := h.after
      ⟨⟨M'', hS'', hK.trans hK'', hSt.trans hSt''⟩, h.res, h.valid⟩)

/-- A kept-stack callee's ok run, then a growing rest, both outcomes. -/
theorem RefE.bind_growK {α β γ : Type} [Inhabited γ] {G : Prop} {x : Except Err α} {T₁ : AM γ}
    {f : γ → AM β} {a₀ : AState} {dec₁ : List Word → γ} {dec : List Word → β}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r₁ : List Word} {ok₁ ok : List Word → Prop} {w : α → List Word × Mem}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackKept m₀ m₁ →
      RefE G x (f (dec₁ r₁)) (AM.st T₁ a₀)
        (fun v y a' => GrowPost dec dn m₁ vis fe M' eb ok (w v) y a')) :
    RefE G x (T₁ >>= f) a₀ (fun v y a' => GrowPost dec dn m₀ vis fe M eb ok (w v) y a') := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  exact RefE.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1])
    ((h₂ M' hS hSt).mono fun _ _ _ h =>
      let ⟨M'', hS'', hK'', hSt''⟩ := h.after
      ⟨⟨M'', hS'', hK.trans hK'', hSt.toGrew.trans hSt''⟩, h.res, h.valid⟩)

end L.Arena
