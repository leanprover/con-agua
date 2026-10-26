module

public import ConAgua.L.DefAssign
public import ConAgua.L.Semantics

@[expose] public section

/-!
# Locals read only after they are assigned do not matter

`DaAg N D s₁ s₂`: equal memories, and equal locals on `D` (the locals defined so far) and on `N`.
**The theorem** (`exec_da`): if every local that `Stmt.da s (some D) R` says `s` may read before
it is defined is in `N`, then two runs of `exec p n s` from `DaAg N D` states end alike: the same
error, or the same signal from states with equal memories that agree again (on `D`, and, when
`s` ends normally, on the defined locals after `s`). Proof: induction on fuel, then on the
statement; every read sees equal values, every write writes equal values, a callee starts from
the same state (`Locals.init` of equal arguments).

The compiler (lane leafgen, step Z) zeroes only the locals of `needZero`: the others start from
whatever their register or frame slot holds, and `exec_da_ok`/`exec_da_error` carry the run from
that state back to the one from `Locals.init` (`Compiler/SimFun.lean`, `sim_fnBody0`).
-/

namespace L

/-- Equal memories, equal locals on `D` and on `N`. -/
def DaAg (N : Var → Prop) (D : List Var) (s₁ s₂ : St) : Prop :=
  s₁.mem = s₂.mem ∧ ∀ x, (x ∈ D ∨ N x) → s₁.loc x = s₂.loc x

/-- Two run results correspond: the same error, or the same value from states related by `Q`. -/
def DaRes {α : Type} (Q : α → St → St → Prop) : Except Err (α × St) → Except Err (α × St) → Prop
  | .ok r₁, .ok r₂ => r₁.1 = r₂.1 ∧ Q r₁.1 r₁.2 r₂.2
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

/-- Runs from `P`-related states correspond. -/
def DaSim {α : Type} (P : St → St → Prop) (Q : α → St → St → Prop) (x : M α) : Prop :=
  ∀ s₁ s₂, P s₁ s₂ → DaRes Q (x.run s₁) (x.run s₂)

section rsim
variable {P : St → St → Prop}

theorem DaSim.pure {α : Type} {Q : α → St → St → Prop} (a : α) (h : ∀ s₁ s₂, P s₁ s₂ → Q a s₁ s₂) :
    DaSim P Q (Pure.pure a : M α) :=
  fun s₁ s₂ hs => ⟨rfl, h s₁ s₂ hs⟩

theorem DaSim.throw {α : Type} {Q : α → St → St → Prop} (e : Err) :
    DaSim P Q (MonadExcept.throw e : M α) :=
  fun _ _ _ => (rfl : e = e)

theorem DaSim.bind {α β : Type} {Q : α → St → St → Prop} {T : β → St → St → Prop} {x : M α}
    {g : α → M β} (hx : DaSim P Q x) (hg : ∀ a, DaSim (Q a) T (g a)) : DaSim P T (x >>= g) := by
  intro s₁ s₂ h
  have h1 := hx s₁ s₂ h
  simp only [StateT.run_bind]
  revert h1
  cases x.run s₁ <;> cases x.run s₂ <;> intro h1
  · exact h1
  · exact h1.elim
  · exact h1.elim
  · rename_i r₁ r₂
    obtain ⟨e, h2⟩ := h1
    show DaRes T ((g r₁.1).run r₁.2) ((g r₂.1).run r₂.2)
    rw [← e]
    exact hg _ _ _ h2

theorem DaSim.get_bind {α : Type} {Q : α → St → St → Prop} {g : St → M α}
    (h : ∀ s₁ s₂, P s₁ s₂ → DaRes Q ((g s₁).run s₁) ((g s₂).run s₂)) : DaSim P Q (get >>= g) := by
  intro s₁ s₂ hs
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact h s₁ s₂ hs

theorem DaSim.modify {Q : PUnit → St → St → Prop} {f : St → St}
    (hf : ∀ s₁ s₂, P s₁ s₂ → Q ⟨⟩ (f s₁) (f s₂)) : DaSim P Q (modify f : M PUnit) :=
  fun s₁ s₂ h => ⟨rfl, hf s₁ s₂ h⟩

theorem DaSim.pre {α : Type} {P' : St → St → Prop} {Q : α → St → St → Prop} {x : M α}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → P s₁ s₂) (h : DaSim P Q x) : DaSim P' Q x :=
  fun s₁ s₂ hs => h s₁ s₂ (hP s₁ s₂ hs)

theorem DaSim.dite_pure {α : Type} {c : Prop} [Decidable c] {f : c → α} {e : Err} :
    DaSim P (fun _ => P) (if h : c then Pure.pure (f h) else MonadExcept.throw e : M α) := by
  split
  · exact DaSim.pure _ fun _ _ h => h
  · exact DaSim.throw _

theorem DaSim.ite {α : Type} {Q : α → St → St → Prop} {c : Prop} [Decidable c] {x y : M α}
    (hx : c → DaSim P Q x) (hy : ¬c → DaSim P Q y) : DaSim P Q (if c then x else y) := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

end rsim

/-! ## Agreement -/

section ag
variable {N : Var → Prop}

theorem DaAg.mono {D D' : List Var} {s₁ s₂ : St} (h : DaAg N D' s₁ s₂) (hD : ∀ x ∈ D, x ∈ D') :
    DaAg N D s₁ s₂ :=
  ⟨h.1, fun x hx => h.2 x (hx.elim (fun h => .inl (hD x h)) .inr)⟩

theorem DaAg.setLoc {D : List Var} {s₁ s₂ : St} (h : DaAg N D s₁ s₂) (x : Var) (v : Word) :
    DaAg N (insV x D) (s₁.setLoc x v) (s₂.setLoc x v) := by
  refine ⟨h.1, fun y hy => ?_⟩
  simp only [St.setLoc]
  by_cases e : y = x
  · simp [e]
  · simp only [e, ite_false]
    refine h.2 y (hy.elim (fun hy => .inl ?_) .inr)
    unfold insV at hy
    split at hy
    · exact hy
    · simpa [e] using hy

theorem DaAg.setLocs : ∀ (xs : List Var) (vs : List Word) {D : List Var} {s₁ s₂ : St},
    DaAg N D s₁ s₂ → DaAg N (xs ++ D) (s₁.setLocs xs vs) (s₂.setLocs xs vs)
  | [], _, _, _, _, h => h
  | x :: xs, vs, D, _, _, h => by
    have := DaAg.setLocs xs vs.tail (h.setLoc x (vs.headD 0))
    refine this.mono fun y hy => ?_
    simp only [List.mem_cons, List.mem_append] at hy ⊢
    unfold insV
    split
    · rcases hy with (rfl | hy) | hy
      · exact .inr (by simpa using ‹D.contains y = true›)
      · exact .inl hy
      · exact .inr hy
    · simp only [List.mem_cons]
      rcases hy with (hy | hy) | hy
      · exact .inr (.inl hy)
      · exact .inl hy
      · exact .inr (.inr hy)

theorem DaAg.mem_eq {D : List Var} {s₁ s₂ : St} (h : DaAg N D s₁ s₂) : s₁.mem = s₂.mem := h.1

end ag

/-! ## The analysis -/

theorem mem_rdA {D vs R : List Var} {x : Var} : x ∈ rdA D vs R ↔ x ∈ R ∨ (x ∈ vs ∧ x ∉ D) := by
  simp [rdA]

/-- The accumulated reads only grow. -/
theorem da_R : ∀ (s : Stmt) (D : Option (List Var)) (R : List Var), ∀ x ∈ R, x ∈ (Stmt.da s D R).2
  | _, none, _, x, hx => by simpa [Stmt.da] using hx
  | .skip, some _, _, _, hx => hx
  | .set _ _, some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .st8 .., some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .st64 .., some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .seq a b, some D, R, x, hx => by
    simp only [Stmt.da]
    exact da_R b _ _ x (da_R a _ _ x hx)
  | .ite c a b, some D, R, x, hx => by
    simp only [Stmt.da]
    exact da_R b _ _ x (da_R a _ _ x (mem_rdA.mpr (.inl hx)))
  | .while c a, some D, R, x, hx => by
    simp only [Stmt.da]
    exact da_R a _ _ x (mem_rdA.mpr (.inl hx))
  | .brk, some _, _, _, hx => hx
  | .ret _, some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .call .., some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .abort _, some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .gset .., some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .st64t .., some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .copy64 .., some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .copy8w .., some _, _, _, hx => mem_rdA.mpr (.inl hx)
  | .scan8 .., some _, _, _, hx => mem_rdA.mpr (.inl hx)

/-- The defined locals only grow. -/
theorem da_D : ∀ (s : Stmt) (D : List Var) (R : List Var) (D' : List Var),
    (Stmt.da s (some D) R).1 = some D' → ∀ x ∈ D, x ∈ D'
  | .skip, _, _, _, h, _, hx => by cases h; exact hx
  | .set y _, D, _, _, h, x, hx => by
    cases h; unfold insV; split
    · exact hx
    · exact List.mem_cons_of_mem _ hx
  | .st8 .., _, _, _, h, _, hx => by cases h; exact hx
  | .st64 .., _, _, _, h, _, hx => by cases h; exact hx
  | .seq a b, D, R, D', h, x, hx => by
    simp only [Stmt.da] at h
    cases h1 : (Stmt.da a (some D) R).1 with
    | none => rw [h1] at h; simp [Stmt.da] at h
    | some D1 =>
      rw [h1] at h
      exact da_D b D1 _ D' h x (da_D a D R D1 h1 x hx)
  | .ite c a b, D, R, D', h, x, hx => by
    simp only [Stmt.da] at h
    generalize h1 : (Stmt.da a (some D) (rdA D c.rv R)).1 = D1 at h
    generalize h2 : (Stmt.da b (some D) (Stmt.da a (some D) (rdA D c.rv R)).2).1 = D2 at h
    cases D1 <;> cases D2 <;> simp only [meetD, Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact da_D b D _ _ h2 x hx
    · exact da_D a D _ _ h1 x hx
    · simp only [List.mem_filter, List.contains_iff_mem]
      exact ⟨da_D a D _ _ h1 x hx, da_D b D _ _ h2 x hx⟩
  | .while .., _, _, _, h, _, hx => by cases h; exact hx
  | .brk, _, _, _, h, _, _ => by cases h
  | .ret _, _, _, _, h, _, _ => by cases h
  | .call xs _ _, _, _, _, h, _, hx => by cases h; exact List.mem_append_right _ hx
  | .abort _, _, _, _, h, _, _ => by cases h
  | .gset .., _, _, _, h, _, hx => by cases h; exact hx
  | .st64t .., _, _, _, h, _, hx => by cases h; exact hx
  | .copy64 .., _, _, _, h, _, hx => by cases h; exact hx
  | .copy8w .., _, _, _, h, _, hx => by cases h; exact hx
  | .scan8 y .., _, _, _, h, x, hx => by
    cases h; unfold insV; split
    · exact hx
    · exact List.mem_cons_of_mem _ hx

/-- The reads of `vs` are allowed. -/
def DaRd (N : Var → Prop) (D vs : List Var) : Prop := ∀ x ∈ vs, x ∈ D ∨ N x

theorem DaRd.left {N : Var → Prop} {D vs ws : List Var} (h : DaRd N D (vs ++ ws)) : DaRd N D vs :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem DaRd.right {N : Var → Prop} {D vs ws : List Var} (h : DaRd N D (vs ++ ws)) : DaRd N D ws :=
  fun x hx => h x (List.mem_append_right _ hx)

/-- Reads allowed from `D` given that `rdA D vs R` is in `N`. -/
theorem rdA_ok {N : Var → Prop} {D vs R : List Var} (h : ∀ x ∈ rdA D vs R, N x) :
    DaRd N D vs ∧ (∀ x ∈ R, N x) := by
  refine ⟨fun x hx => ?_, fun x hx => h x (mem_rdA.mpr (.inl hx))⟩
  by_cases hd : x ∈ D
  · exact .inl hd
  · exact .inr (h x (mem_rdA.mpr (.inr ⟨hx, hd⟩)))

/-! ## Expressions, conditions, arguments -/

section eval
variable {N : Var → Prop} {D : List Var}

theorem ld64_rsim (a : ArrId) (i : Word) : DaSim (DaAg N D) (fun _ => DaAg N D) (ld64 a i) := by
  unfold ld64
  refine DaSim.get_bind fun s₁ s₂ h => ?_
  dsimp only
  rw [h.1]
  exact DaSim.dite_pure s₁ s₂ h

theorem ld8_rsim (a : ArrId) (i : Word) : DaSim (DaAg N D) (fun _ => DaAg N D) (ld8 a i) := by
  unfold ld8
  refine DaSim.get_bind fun s₁ s₂ h => ?_
  dsimp only
  rw [h.1]
  exact DaSim.dite_pure s₁ s₂ h

theorem ld8x8_rsim (b : BSrc) (i : Word) : DaSim (DaAg N D) (fun _ => DaAg N D) (ld8x8 b i) := by
  unfold ld8x8
  refine DaSim.get_bind fun s₁ s₂ h => ?_
  dsimp only
  rw [h.1]
  exact DaSim.ite (fun _ => DaSim.pure _ fun _ _ h => h) (fun _ => DaSim.throw _) s₁ s₂ h

theorem st64_rsim (a : ArrId) (i v : Word) : DaSim (DaAg N D) (fun _ => DaAg N D) (st64 a i v) := by
  unfold st64
  refine DaSim.get_bind fun s₁ s₂ h => ?_
  rw [h.1]
  by_cases hc : i.toNat < (s₂.mem.arr64 a).size
  · simp only [hc, ↓reduceIte]
    exact ⟨rfl, ⟨by simp only, h.2⟩⟩
  · simp only [hc, ↓reduceIte]
    exact DaSim.throw _ s₁ s₂ h

theorem st8_rsim (a : ArrId) (i v : Word) : DaSim (DaAg N D) (fun _ => DaAg N D) (st8 a i v) := by
  unfold st8
  refine DaSim.get_bind fun s₁ s₂ h => ?_
  rw [h.1]
  by_cases hc : i.toNat < (s₂.mem.arr8 a).size
  · simp only [hc, ↓reduceIte]
    exact ⟨rfl, ⟨by simp only, h.2⟩⟩
  · simp only [hc, ↓reduceIte]
    exact DaSim.throw _ s₁ s₂ h

theorem evalE_rsim : ∀ (e : Expr), DaRd N D e.rv → DaSim (DaAg N D) (fun _ => DaAg N D) (evalE e) := by
  intro e
  induction e with
  | const w => intro _; rw [evalE]; exact DaSim.pure w fun _ _ h => h
  | var x =>
    intro hr; rw [evalE]
    exact DaSim.get_bind fun s₁ s₂ h => ⟨by simp only [h.2 x (hr x (by simp [Expr.rv]))], h⟩
  | bin op a b iha ihb =>
    intro hr; simp only [Expr.rv] at hr; rw [evalE]
    exact DaSim.bind (iha hr.left) fun _ => DaSim.bind (ihb hr.right) fun _ => DaSim.pure _ fun _ _ h => h
  | cmpw c a b iha ihb =>
    intro hr; simp only [Expr.rv] at hr; rw [evalE]
    exact DaSim.bind (iha hr.left) fun _ => DaSim.bind (ihb hr.right) fun _ => DaSim.pure _ fun _ _ h => h
  | ld8 a i ih =>
    intro hr; simp only [Expr.rv] at hr; rw [evalE]
    exact DaSim.bind (ih hr) fun _ => ld8_rsim a _
  | ld64 a i ih =>
    intro hr; simp only [Expr.rv] at hr; rw [evalE]
    exact DaSim.bind (ih hr) fun _ => ld64_rsim a _
  | len8 a =>
    intro _; rw [evalE]
    exact DaSim.get_bind fun s₁ s₂ h => ⟨by simp only [h.1], h⟩
  | len64 a =>
    intro _; rw [evalE]
    exact DaSim.get_bind fun s₁ s₂ h => ⟨by simp only [h.1], h⟩
  | ldc d i ih =>
    intro hr; simp only [Expr.rv] at hr; rw [evalE]
    exact DaSim.bind (ih hr) fun _ => by unfold ldc; exact DaSim.dite_pure
  | glob g =>
    intro _; rw [evalE]
    exact DaSim.get_bind fun s₁ s₂ h => ⟨by simp only [h.1], h⟩
  | ld64t a t i iht ihi =>
    intro hr; simp only [Expr.rv] at hr; rw [evalE]
    exact DaSim.bind (iht hr.left) fun _ => DaSim.bind (ihi hr.right) fun _ => ld64_rsim _ _
  | len64t a t ih =>
    intro hr; simp only [Expr.rv] at hr; rw [evalE]
    exact DaSim.bind (ih hr) fun u => DaSim.get_bind fun s₁ s₂ h => ⟨by simp only [h.1], h⟩
  | ld8x8 b i ih =>
    intro hr; simp only [Expr.rv] at hr; rw [evalE]
    exact DaSim.bind (ih hr) fun _ => ld8x8_rsim b _

theorem evalC_rsim : ∀ (c : Cond), DaRd N D c.rv → DaSim (DaAg N D) (fun _ => DaAg N D) (evalC c) := by
  intro c
  induction c with
  | cmp c a b =>
    intro hr; simp only [Cond.rv] at hr; rw [evalC]
    exact DaSim.bind (evalE_rsim a hr.left) fun _ => DaSim.bind (evalE_rsim b hr.right) fun _ =>
      DaSim.pure _ fun _ _ h => h
  | and p q ihp ihq =>
    intro hr; simp only [Cond.rv] at hr; rw [evalC]
    exact DaSim.bind (ihp hr.left) fun b => by
      cases b
      · exact DaSim.pure _ fun _ _ h => h
      · exact ihq hr.right
  | or p q ihp ihq =>
    intro hr; simp only [Cond.rv] at hr; rw [evalC]
    exact DaSim.bind (ihp hr.left) fun b => by
      cases b
      · exact ihq hr.right
      · exact DaSim.pure _ fun _ _ h => h
  | not p ih =>
    intro hr; simp only [Cond.rv] at hr; rw [evalC]
    exact DaSim.bind (ih hr) fun _ => DaSim.pure _ fun _ _ h => h

theorem evalArgs_rsim : ∀ (es : List Expr), DaRd N D (es.flatMap Expr.rv) →
    DaSim (DaAg N D) (fun _ => DaAg N D) (evalArgs es)
  | [], _ => by rw [evalArgs]; exact DaSim.pure _ fun _ _ h => h
  | e :: es, hr => by
    simp only [List.flatMap_cons] at hr
    rw [evalArgs]
    exact DaSim.bind (evalE_rsim e hr.left) fun _ => DaSim.bind (evalArgs_rsim es hr.right) fun _ =>
      DaSim.pure _ fun _ _ h => h

theorem warr_bind_rsim {β : Type} {Q : β → St → St → Prop} {w : WArr} (hw : DaRd N D w.rv)
    {g : ArrId → M β} (hg : ∀ a, DaSim (DaAg N D) Q (g a)) : DaSim (DaAg N D) Q (warr w >>= g) := by
  cases w with
  | plain a =>
    simp only [warr, pure_bind]
    exact hg a
  | tier a t =>
    simp only [WArr.rv] at hw
    simp only [warr, bind_assoc, pure_bind]
    exact DaSim.bind (evalE_rsim t hw) fun u => hg _

end eval

/-! ## Statements, calls, fuel -/

section stmt
variable {p : Prog} {N : Var → Prop}

/-- How two runs of a statement from `DaAg N D` states end: agreeing on `D`, and, when the
statement ends normally, its defined locals after are `some D'` and the states agree on `D'`. -/
def DaPost (N : Var → Prop) (D : List Var) (Dout : Option (List Var)) (r : Sig) (t₁ t₂ : St) : Prop :=
  DaAg N D t₁ t₂ ∧ (r = .normal → ∃ D', Dout = some D' ∧ DaAg N D' t₁ t₂)

/-- A continuation whose runs of every statement correspond, as `Stmt.da` says. -/
def DaKSim (N : Var → Prop) (k : Stmt → M Sig) : Prop :=
  ∀ st D R, (∀ x ∈ (Stmt.da st (some D) R).2, N x) →
    DaSim (DaAg N D) (DaPost N D (Stmt.da st (some D) R).1) (k st)

/-- A callee starts from the same state in both runs. -/
theorem invoke_rsim {D : List Var} (k : Stmt → M Sig) (f : FnName) (vs : List Word) :
    DaSim (DaAg N D) (fun _ => DaAg N D) (invoke p k f vs) := by
  unfold invoke lookupFn
  cases hl : p.lookup f with
  | none => intro s₁ s₂ _; exact (rfl : Err.noFun f = Err.noFun f)
  | some fd =>
    simp only [pure_bind]
    unfold callFn
    refine DaSim.get_bind fun s₁ s₂ h => ?_
    have e : ({ s₁ with loc := Locals.init vs } : St) = { s₂ with loc := Locals.init vs } := by
      rw [show s₁.mem = s₂.mem from h.1]
    simp only [StateT.run_bind, StateT.run_set, pure_bind]
    rw [e]
    cases (k fd.body).run { s₂ with loc := Locals.init vs } with
    | error e => exact (rfl : e = e)
    | ok r =>
      simp only [StateT.run_modify, StateT.run_pure]
      exact ⟨rfl, rfl, fun x hx => h.2 x hx⟩

theorem step_rsim {k : Stmt → M Sig} (hk : DaKSim N k) : DaKSim N (step p k) := by
  intro st
  induction st with
  | skip =>
    intro D R _; rw [step]
    exact DaSim.pure _ fun _ _ h => ⟨h, fun _ => ⟨D, rfl, h⟩⟩
  | brk =>
    intro D R _; rw [step]
    exact DaSim.pure _ fun _ _ h => ⟨h, fun e => by cases e⟩
  | abort e =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    exact DaSim.bind (evalE_rsim e (rdA_ok hR).1) fun _ => DaSim.throw _
  | set x e =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    exact DaSim.bind (evalE_rsim e (rdA_ok hR).1) fun v =>
      DaSim.bind (DaSim.modify (Q := fun _ => DaAg N (insV x D)) fun _ _ h => h.setLoc x v) fun _ =>
        DaSim.pure _ fun _ _ h => ⟨h.mono fun y hy => da_D (.set x e) D R _ rfl y hy, fun _ => ⟨_, rfl, h⟩⟩
  | gset g e =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    exact DaSim.bind (evalE_rsim e (rdA_ok hR).1) fun v =>
      DaSim.bind (DaSim.modify (Q := fun _ => DaAg N D) fun _ _ h => ⟨by simp only [St.setG, h.1], h.2⟩)
        fun _ => DaSim.pure _ fun _ _ h => ⟨h, fun _ => ⟨_, rfl, h⟩⟩
  | st8 a i e =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    have hr := (rdA_ok hR).1
    exact DaSim.bind (evalE_rsim i hr.left) fun _ => DaSim.bind (evalE_rsim e hr.right) fun _ =>
      DaSim.bind (st8_rsim a _ _) fun _ => DaSim.pure _ fun _ _ h => ⟨h, fun _ => ⟨_, rfl, h⟩⟩
  | st64 a i e =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    have hr := (rdA_ok hR).1
    exact DaSim.bind (evalE_rsim i hr.left) fun _ => DaSim.bind (evalE_rsim e hr.right) fun _ =>
      DaSim.bind (st64_rsim a _ _) fun _ => DaSim.pure _ fun _ _ h => ⟨h, fun _ => ⟨_, rfl, h⟩⟩
  | st64t a t i e =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    have hr := (rdA_ok hR).1
    exact DaSim.bind (evalE_rsim t hr.left.left) fun u => DaSim.bind (evalE_rsim i hr.left.right) fun _ =>
      DaSim.bind (evalE_rsim e hr.right) fun _ =>
        DaSim.bind (st64_rsim _ _ _) fun _ => DaSim.pure _ fun _ _ h => ⟨h, fun _ => ⟨_, rfl, h⟩⟩
  | seq a b iha ihb =>
    intro D R hR; rw [step]
    simp only [Stmt.da] at hR ⊢
    generalize hA : Stmt.da a (some D) R = A at hR ⊢
    obtain ⟨D1, R1⟩ := A
    have ha := iha D R (by rw [hA]; exact fun x hx => hR x (da_R b _ _ x hx))
    rw [hA] at ha
    refine DaSim.bind ha fun r => ?_
    cases r with
    | normal =>
      cases D1 with
      | none => exact fun s₁ s₂ h => absurd (h.2 rfl) (by simp)
      | some D1 =>
        have hD := da_D a D R D1 (by rw [hA])
        refine DaSim.pre (P := DaAg N D1) (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_)
        · obtain ⟨D', e, h'⟩ := h.2 rfl; cases e; exact h'
        · have hb := ihb D1 R1 hR s₁ s₂ h
          revert hb
          cases (step p k b).run s₁ <;> cases (step p k b).run s₂ <;> intro hb
          · exact hb
          · exact hb.elim
          · exact hb.elim
          · exact ⟨hb.1, hb.2.1.mono hD, hb.2.2⟩
    | brk => exact DaSim.pure _ fun _ _ h => ⟨h.1, fun e => by cases e⟩
    | ret v => exact DaSim.pure _ fun _ _ h => ⟨h.1, fun e => by cases e⟩
  | ite c a b iha ihb =>
    intro D R hR; rw [step]
    simp only [Stmt.da] at hR ⊢
    generalize hA : Stmt.da a (some D) (rdA D c.rv R) = A at hR ⊢
    obtain ⟨D1, R1⟩ := A
    generalize hB : Stmt.da b (some D) R1 = B at hR ⊢
    obtain ⟨D2, R2⟩ := B
    have hR1 : ∀ x ∈ R1, N x := fun x hx => hR x (by rw [← hB]; exact da_R b _ _ x hx)
    have hAR : (Stmt.da a (some D) (rdA D c.rv R)).2 = R1 := by rw [hA]
    have hc := rdA_ok (D := D) (vs := c.rv) (R := R) (N := N)
      (fun x hx => hR1 x (by rw [← hAR]; exact da_R a _ _ x hx))
    refine DaSim.bind (evalC_rsim c hc.1) fun v => ?_
    cases v with
    | true =>
      simp only [ite_true]
      have ha := iha D (rdA D c.rv R) (by rw [hA]; exact hR1)
      rw [hA] at ha
      refine fun s₁ s₂ h => ?_
      have := ha s₁ s₂ h
      revert this
      cases (step p k a).run s₁ <;> cases (step p k a).run s₂ <;> intro hb
      · exact hb
      · exact hb.elim
      · exact hb.elim
      · refine ⟨hb.1, hb.2.1, fun hn => ?_⟩
        obtain ⟨D', e, h'⟩ := hb.2.2 hn
        subst e
        cases D2 with
        | none => exact ⟨D', rfl, h'⟩
        | some D2 => exact ⟨_, rfl, h'.mono fun x hx => (List.mem_filter.mp hx).1⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hb' := ihb D R1 (by rw [hB]; exact hR)
      rw [hB] at hb'
      refine fun s₁ s₂ h => ?_
      have := hb' s₁ s₂ h
      revert this
      cases (step p k b).run s₁ <;> cases (step p k b).run s₂ <;> intro hb
      · exact hb
      · exact hb.elim
      · exact hb.elim
      · refine ⟨hb.1, hb.2.1, fun hn => ?_⟩
        obtain ⟨D', e, h'⟩ := hb.2.2 hn
        subst e
        cases D1 with
        | none => exact ⟨D', rfl, h'⟩
        | some D1 =>
          refine ⟨_, rfl, h'.mono fun x hx => ?_⟩
          simp only [List.mem_filter, List.contains_iff_mem] at hx
          exact hx.2
  | «while» c a ih =>
    intro D R hR
    have hw := hR
    rw [step]
    simp only [Stmt.da] at hR ⊢
    have hR0 : ∀ x ∈ rdA D c.rv R, N x := fun x hx => hR x (da_R a _ _ x hx)
    refine DaSim.bind (evalC_rsim c (rdA_ok hR0).1) fun v => ?_
    cases v with
    | false => exact DaSim.pure _ fun _ _ h => ⟨h, fun _ => ⟨D, rfl, h⟩⟩
    | true =>
      refine DaSim.bind (ih D (rdA D c.rv R) hR) fun r => ?_
      cases r with
      | normal =>
        refine DaSim.pre (fun s₁ s₂ h => h.1) ?_
        have := hk (.while c a) D R hw
        simp only [Stmt.da] at this
        exact this
      | brk => exact DaSim.pure _ fun _ _ h => ⟨h.1, fun _ => ⟨D, rfl, h.1⟩⟩
      | ret v => exact DaSim.pure _ fun _ _ h => ⟨h.1, fun e => by cases e⟩
  | ret es =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    exact DaSim.bind (evalArgs_rsim es (rdA_ok hR).1) fun _ =>
      DaSim.pure _ fun _ _ h => ⟨h, fun e => by cases e⟩
  | call xs f args =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    exact DaSim.bind (evalArgs_rsim args (rdA_ok hR).1) fun vs => DaSim.bind (invoke_rsim k f vs) fun rs =>
      DaSim.bind (DaSim.modify (Q := fun _ => DaAg N (xs ++ D)) fun _ _ h => h.setLocs xs rs) fun _ =>
        DaSim.pure _ fun _ _ h => ⟨h.mono fun y hy => List.mem_append_right _ hy, fun _ => ⟨_, rfl, h⟩⟩
  | copy64 d di s si n =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    have hr := (rdA_ok hR).1
    refine warr_bind_rsim hr.left.left.left.left fun da => DaSim.bind (evalE_rsim di hr.left.left.left.right) fun i =>
      warr_bind_rsim hr.left.left.right fun sa => DaSim.bind (evalE_rsim si hr.left.right) fun j =>
        DaSim.bind (evalE_rsim n hr.right) fun k => DaSim.get_bind fun s₁ s₂ h => ?_
    rw [h.1]
    by_cases hc : i.toNat + k.toNat ≤ (s₂.mem.arr64 da).size ∧
        j.toNat + k.toNat ≤ (s₂.mem.arr64 sa).size
    · simp only [hc, and_self, ↓reduceIte]
      exact ⟨rfl, ⟨by simp only, h.2⟩, fun _ => ⟨_, rfl, ⟨by simp only, h.2⟩⟩⟩
    · simp only [hc, ↓reduceIte]
      exact DaSim.throw _ s₁ s₂ h
  | copy8w d di b si n =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    have hr := (rdA_ok hR).1
    refine warr_bind_rsim hr.left.left.left fun da => DaSim.bind (evalE_rsim di hr.left.left.right) fun i =>
      DaSim.bind (evalE_rsim si hr.left.right) fun j =>
        DaSim.bind (evalE_rsim n hr.right) fun k => DaSim.get_bind fun s₁ s₂ h => ?_
    rw [h.1]
    by_cases hc : i.toNat + k.toNat ≤ (s₂.mem.arr64 da).size ∧
        j.toNat + k.toNat ≤ (s₂.mem.src8 b).size
    · simp only [hc, and_self, ↓reduceIte]
      exact ⟨rfl, ⟨by simp only, h.2⟩, fun _ => ⟨_, rfl, ⟨by simp only, h.2⟩⟩⟩
    · simp only [hc, ↓reduceIte]
      exact DaSim.throw _ s₁ s₂ h
  | scan8 x b i e c =>
    intro D R hR; simp only [Stmt.da] at hR ⊢; rw [step]
    have hr := (rdA_ok hR).1
    refine DaSim.bind (evalE_rsim i hr.left) fun vi => DaSim.bind (evalE_rsim e hr.right) fun ve =>
      DaSim.get_bind fun s₁ s₂ h => ?_
    dsimp only
    rw [h.1]
    exact DaSim.ite (fun _ => DaSim.bind (DaSim.modify (Q := fun _ => DaAg N (insV x D)) fun _ _ h => h.setLoc x _)
        fun _ => DaSim.pure _ fun _ _ h =>
          ⟨h.mono fun y hy => da_D (.scan8 x b i e c) D R _ rfl y hy, fun _ => ⟨_, rfl, h⟩⟩)
      (fun _ => DaSim.throw _) s₁ s₂ h

theorem exec_rsim : ∀ n, DaKSim N (exec p n)
  | 0 => fun _ _ _ _ => by
    rw [show exec p 0 = fun _ => throw .outOfFuel from funext fun _ => rfl]; exact DaSim.throw _
  | n + 1 => step_rsim (exec_rsim n)

end stmt

/-! ## The theorems -/

/-- **Locals read only after they are assigned do not matter.** -/
theorem exec_da {p : Prog} {N : Var → Prop} (n : Nat) (s : Stmt) (D R : List Var)
    (hR : ∀ x ∈ (Stmt.da s (some D) R).2, N x) {s₁ s₂ : St} (h : DaAg N D s₁ s₂) :
    DaRes (DaPost N D (Stmt.da s (some D) R).1) ((exec p n s).run s₁) ((exec p n s).run s₂) :=
  exec_rsim n s D R hR s₁ s₂ h

/-- A successful run from the first state: the second ends the same way, with the same memory. -/
theorem exec_da_ok {p : Prog} {N : Var → Prop} {n : Nat} {s : Stmt} {D R : List Var}
    (hR : ∀ x ∈ (Stmt.da s (some D) R).2, N x) {s₁ s₂ : St} (h : DaAg N D s₁ s₂) {r : Sig} {t₁ : St}
    (h1 : (exec p n s).run s₁ = .ok (r, t₁)) :
    ∃ t₂, (exec p n s).run s₂ = .ok (r, t₂) ∧ t₁.mem = t₂.mem := by
  have := exec_da (p := p) n s D R hR h
  rw [h1] at this
  revert this
  cases (exec p n s).run s₂ with
  | error e => intro h'; exact h'.elim
  | ok q =>
    obtain ⟨r₂, t₂⟩ := q
    intro h'
    obtain ⟨e, h''⟩ := h'
    dsimp only at e h''
    subst e
    exact ⟨t₂, rfl, h''.1.1⟩

/-- A failed run from the first state: the second fails the same way. -/
theorem exec_da_error {p : Prog} {N : Var → Prop} {n : Nat} {s : Stmt} {D R : List Var}
    (hR : ∀ x ∈ (Stmt.da s (some D) R).2, N x) {s₁ s₂ : St} (h : DaAg N D s₁ s₂) {e : Err}
    (h1 : (exec p n s).run s₁ = .error e) : (exec p n s).run s₂ = .error e := by
  have := exec_da (p := p) n s D R hR h
  rw [h1] at this
  revert this
  cases (exec p n s).run s₂ with
  | error e' => intro h'; exact congrArg _ h'.symm
  | ok q => intro h'; exact h'.elim

end L
