module

public import ConAgua.L.Semantics
import ConAgua.Front.Preserve

@[expose] public section

/-!
# Globals a call-closed function set never writes

`globsIn p G fs` is a `Bool` check of the program text: every function of `fs` that `p` defines
calls only into `fs` and has no `g := e` for a global with `G g = true`. Then every successful
run of `f ∈ fs` ends with those globals as they started (`invoke_keepsG`, `run_keepsG`).

This is the complement of `closedG` (`L/WriteSet.lean`, a list of the globals that may be
written): here the globals that may not be written are a predicate, so a check stays cheap when
almost every global may be written. Same induction (fuel, then statements). Lane parmode: phase
B's loop never writes `MODE`, `PLO`, `INIT`, `PHI` (`Checker/PhaseBReads.lean`).
-/

namespace L

/-- No write to a global `G` accepts; calls only functions `cf` accepts. -/
def Stmt.gsOk (G : GVar → Bool) (cf : FnName → Bool) : Stmt → Bool
  | .gset g _ => !G g
  | .seq s t => s.gsOk G cf && t.gsOk G cf
  | .ite _ s t => s.gsOk G cf && t.gsOk G cf
  | .while _ s => s.gsOk G cf
  | .call _ f _ => cf f
  | _ => true

/-- **The kept globals of a call-closed function set**: every function of `fs` that `p` defines
writes no global `G` accepts and calls only into `fs`. -/
def globsIn (p : Prog) (G : GVar → Bool) (fs : List FnName) : Bool :=
  fs.all fun f => match p.lookup f with
    | some fd => fd.body.gsOk G (fun g => decide (g ∈ fs))
    | none => true

theorem globsIn_lookup {p : Prog} {G : GVar → Bool} {fs : List FnName}
    (hp : globsIn p G fs = true) {f : FnName} (hf : f ∈ fs) {fd : FunDecl}
    (h : p.lookup f = some fd) : fd.body.gsOk G (fun g => decide (g ∈ fs)) = true := by
  simp only [globsIn, List.all_eq_true] at hp
  have := hp f hf
  simp only [h] at this
  exact this

/-- Every successful run of `x` keeps the globals `G` accepts. -/
def KeepsG {α : Type} (G : GVar → Bool) (x : M α) : Prop :=
  ∀ s r s', x.run s = .ok (r, s') → ∀ g, G g = true → s'.mem.glob g = s.mem.glob g

section keeps
variable {G : GVar → Bool}

theorem KeepsG.pure {α : Type} (a : α) : KeepsG G (Pure.pure a : M α) := by
  intro s r s' h g _
  have e : (Pure.pure a : M α).run s = .ok (a, s) := rfl
  rw [e] at h
  cases h
  rfl

theorem KeepsG.throw {α : Type} (e : Err) : KeepsG G (MonadExcept.throw e : M α) := by
  intro s r s' h
  cases h

theorem KeepsG.bind {α β : Type} {x : M α} {f : α → M β} (hx : KeepsG G x)
    (hf : ∀ a, KeepsG G (f a)) : KeepsG G (x >>= f) := by
  intro s r s' h g hg
  rw [StateT.run_bind] at h
  cases h1 : x.run s with
  | error e => rw [h1] at h; cases h
  | ok q =>
    rw [h1] at h
    exact (hf q.1 q.2 r s' h g hg).trans (hx s q.1 q.2 h1 g hg)

theorem KeepsG.get_bind {α : Type} {f : St → M α}
    (h : ∀ s r s', (f s).run s = .ok (r, s') → ∀ g, G g = true → s'.mem.glob g = s.mem.glob g) :
    KeepsG G (get >>= f) := by
  intro s r s' hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  exact h s r s' hr

theorem KeepsG.modify {f : St → St} (hf : ∀ s g, G g = true → (f s).mem.glob g = s.mem.glob g) :
    KeepsG G (_root_.modify f : M PUnit) := by
  intro s r s' h g hg
  have e : (_root_.modify f : M PUnit).run s = Except.ok (⟨⟩, f s) := rfl
  rw [e] at h
  cases h
  exact hf s g hg

/-- A state write that keeps the globals, then a computation that keeps them. -/
theorem KeepsG.set_bind {β : Type} {g' : PUnit → M β} (hg : KeepsG G (g' ⟨⟩)) {s t : St}
    (ht : ∀ g, G g = true → t.mem.glob g = s.mem.glob g) {r : β} {s' : St}
    (h : (MonadStateOf.set t >>= g' : M β).run s = .ok (r, s')) :
    ∀ g, G g = true → s'.mem.glob g = s.mem.glob g :=
  fun g hgg => (hg t r s' h g hgg).trans (ht g hgg)

theorem KeepsG.dite_pure {α : Type} {c : Prop} [Decidable c] {f : c → α} {e : Err} :
    KeepsG G (if h : c then Pure.pure (f h) else MonadExcept.throw e : M α) := by
  split
  · exact KeepsG.pure _
  · exact KeepsG.throw _

theorem KeepsG.ite {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : KeepsG G x)
    (hy : KeepsG G y) : KeepsG G (if c then x else y) := by
  split
  · exact hx
  · exact hy

end keeps

/-! ## Memory operations other than `setG` keep every global -/

theorem Mem.glob_copy64 (d : ArrId) (s : ArrId) :
    ∀ (n : Nat) (m : Mem) (di si : Word), (m.copy64 d di s si n).glob = m.glob
  | 0, _, _, _ => rfl
  | n + 1, m, di, si => by
    simp only [Mem.copy64]
    exact Mem.glob_copy64 d s n _ _ _

theorem Mem.glob_copy8w (d : ArrId) (b : Array UInt8) :
    ∀ (n : Nat) (m : Mem) (di si : Word), (m.copy8w d di b si n).glob = m.glob
  | 0, _, _, _ => rfl
  | n + 1, m, di, si => by
    simp only [Mem.copy8w]
    exact Mem.glob_copy8w d b n _ _ _

theorem St.setLocs_mem' : ∀ (s : St) (xs : List Var) (vs : List Word), (s.setLocs xs vs).mem = s.mem
  | _, [], _ => rfl
  | s, x :: xs, vs => St.setLocs_mem' (s.setLoc x (vs.headD 0)) xs vs.tail

/-! ## Expressions change no state -/

section eval
variable {G : GVar → Bool}

theorem ld64_keepsG (a : ArrId) (i : Word) : KeepsG G (ld64 a i) := by
  unfold ld64
  exact KeepsG.get_bind fun s => KeepsG.dite_pure s

theorem ld8_keepsG (a : ArrId) (i : Word) : KeepsG G (ld8 a i) := by
  unfold ld8
  exact KeepsG.get_bind fun s => KeepsG.dite_pure s

theorem ld8x8_keepsG (b : BSrc) (i : Word) : KeepsG G (ld8x8 b i) := by
  unfold ld8x8
  exact KeepsG.get_bind fun s => KeepsG.ite (KeepsG.pure _) (KeepsG.throw _) s

theorem st64_keepsG (a : ArrId) (i v : Word) : KeepsG G (st64 a i v) := by
  unfold st64
  refine KeepsG.get_bind fun s r s' h g _ => ?_
  split at h
  · cases h; rfl
  · cases h

theorem st8_keepsG (a : ArrId) (i v : Word) : KeepsG G (st8 a i v) := by
  unfold st8
  refine KeepsG.get_bind fun s r s' h g _ => ?_
  split at h
  · cases h; rfl
  · cases h

theorem evalE_keepsG : ∀ (e : Expr), KeepsG G (evalE e) := by
  intro e
  induction e with
  | const w => rw [evalE]; exact KeepsG.pure w
  | var x => rw [evalE]; exact KeepsG.get_bind fun s => KeepsG.pure _ s
  | bin op a b iha ihb =>
    rw [evalE]; exact KeepsG.bind iha fun _ => KeepsG.bind ihb fun _ => KeepsG.pure _
  | cmpw c a b iha ihb =>
    rw [evalE]; exact KeepsG.bind iha fun _ => KeepsG.bind ihb fun _ => KeepsG.pure _
  | ld8 a i ih => rw [evalE]; exact KeepsG.bind ih fun _ => ld8_keepsG a _
  | ld64 a i ih => rw [evalE]; exact KeepsG.bind ih fun _ => ld64_keepsG a _
  | len8 a => rw [evalE]; exact KeepsG.get_bind fun s => KeepsG.pure _ s
  | len64 a => rw [evalE]; exact KeepsG.get_bind fun s => KeepsG.pure _ s
  | ldc d i ih => rw [evalE]; exact KeepsG.bind ih fun _ => by unfold ldc; exact KeepsG.dite_pure
  | glob g => rw [evalE]; exact KeepsG.get_bind fun s => KeepsG.pure _ s
  | ld64t a t i iht ihi =>
    rw [evalE]; exact KeepsG.bind iht fun _ => KeepsG.bind ihi fun _ => ld64_keepsG _ _
  | len64t a t ih =>
    rw [evalE]; exact KeepsG.bind ih fun _ => KeepsG.get_bind fun s => KeepsG.pure _ s
  | ld8x8 b i ih => rw [evalE]; exact KeepsG.bind ih fun _ => ld8x8_keepsG b _

theorem evalC_keepsG : ∀ (c : Cond), KeepsG G (evalC c) := by
  intro c
  induction c with
  | cmp c a b =>
    rw [evalC]
    exact KeepsG.bind (evalE_keepsG a) fun _ => KeepsG.bind (evalE_keepsG b) fun _ => KeepsG.pure _
  | and p q ihp ihq =>
    rw [evalC]
    exact KeepsG.bind ihp fun b => by
      cases b
      · exact KeepsG.pure _
      · exact ihq
  | or p q ihp ihq =>
    rw [evalC]
    exact KeepsG.bind ihp fun b => by
      cases b
      · exact ihq
      · exact KeepsG.pure _
  | not p ih => rw [evalC]; exact KeepsG.bind ih fun _ => KeepsG.pure _

theorem evalArgs_keepsG : ∀ (es : List Expr), KeepsG G (evalArgs es)
  | [] => by rw [evalArgs]; exact KeepsG.pure _
  | e :: es => by
    rw [evalArgs]
    exact KeepsG.bind (evalE_keepsG e) fun _ => KeepsG.bind (evalArgs_keepsG es) fun _ =>
      KeepsG.pure _

theorem warr_keepsG (w : WArr) : KeepsG G (warr w) := by
  cases w with
  | plain a => exact KeepsG.pure a
  | tier a t => exact KeepsG.bind (evalE_keepsG t) fun _ => KeepsG.pure _

end eval

/-! ## Statements, calls, fuel -/

section stmt
variable {p : Prog} {G : GVar → Bool} {fs : List FnName}

/-- A continuation that keeps the globals on every checked statement. -/
def KKeepsG (G : GVar → Bool) (fs : List FnName) (k : Stmt → M Sig) : Prop :=
  ∀ st, st.gsOk G (fun g => decide (g ∈ fs)) = true → KeepsG G (k st)

theorem invoke_keepsG' (hp : globsIn p G fs = true) {k : Stmt → M Sig} (hk : KKeepsG G fs k)
    {f : FnName} (hf : f ∈ fs) (vs : List Word) : KeepsG G (invoke p k f vs) := by
  unfold invoke lookupFn
  cases hl : p.lookup f with
  | none => intro s r s' h; cases h
  | some fd =>
    simp only [pure_bind]
    unfold callFn
    refine KeepsG.get_bind fun s r s' h => ?_
    refine KeepsG.set_bind (s := s) (t := { mem := s.mem, loc := Locals.init vs }) ?_ (fun _ _ => rfl) h
    exact KeepsG.bind (hk _ (globsIn_lookup hp hf hl)) fun _ =>
      KeepsG.bind (KeepsG.modify fun _ _ _ => rfl) fun _ => KeepsG.pure _

theorem step_keepsG (hp : globsIn p G fs = true) {k : Stmt → M Sig} (hk : KKeepsG G fs k) :
    KKeepsG G fs (step p k) := by
  intro st
  induction st with
  | skip => intro _; rw [step]; exact KeepsG.pure _
  | brk => intro _; rw [step]; exact KeepsG.pure _
  | abort e => intro _; rw [step]; exact KeepsG.bind (evalE_keepsG e) fun _ => KeepsG.throw _
  | set x e =>
    intro _; rw [step]
    exact KeepsG.bind (evalE_keepsG e) fun _ =>
      KeepsG.bind (KeepsG.modify fun _ _ _ => rfl) fun _ => KeepsG.pure _
  | gset g' e =>
    intro hr; simp only [Stmt.gsOk, Bool.not_eq_eq_eq_not, Bool.not_true] at hr; rw [step]
    refine KeepsG.bind (evalE_keepsG e) fun v =>
      KeepsG.bind (KeepsG.modify fun s g hg => ?_) fun _ => KeepsG.pure _
    have hne : g ≠ g' := fun e => by rw [e, hr] at hg; cases hg
    simp only [St.setG, Mem.setG, hne, ite_false]
  | st8 a i e =>
    intro _; rw [step]
    exact KeepsG.bind (evalE_keepsG i) fun _ => KeepsG.bind (evalE_keepsG e) fun _ =>
      KeepsG.bind (st8_keepsG _ _ _) fun _ => KeepsG.pure _
  | st64 a i e =>
    intro _; rw [step]
    exact KeepsG.bind (evalE_keepsG i) fun _ => KeepsG.bind (evalE_keepsG e) fun _ =>
      KeepsG.bind (st64_keepsG _ _ _) fun _ => KeepsG.pure _
  | st64t a t i e =>
    intro _; rw [step]
    exact KeepsG.bind (evalE_keepsG t) fun _ => KeepsG.bind (evalE_keepsG i) fun _ =>
      KeepsG.bind (evalE_keepsG e) fun _ => KeepsG.bind (st64_keepsG _ _ _) fun _ => KeepsG.pure _
  | seq s t ihs iht =>
    intro hr; simp only [Stmt.gsOk, Bool.and_eq_true] at hr; rw [step]
    exact KeepsG.bind (ihs hr.1) fun r => by
      cases r
      · exact iht hr.2
      · exact KeepsG.pure _
      · exact KeepsG.pure _
  | ite c s t ihs iht =>
    intro hr; simp only [Stmt.gsOk, Bool.and_eq_true] at hr; rw [step]
    exact KeepsG.bind (evalC_keepsG c) fun b => by
      cases b
      · exact iht hr.2
      · exact ihs hr.1
  | «while» c s ih =>
    intro hr
    have hw := hr
    simp only [Stmt.gsOk] at hr; rw [step]
    exact KeepsG.bind (evalC_keepsG c) fun b => by
      cases b
      · exact KeepsG.pure _
      · exact KeepsG.bind (ih hr) fun r => by
          cases r
          · exact hk _ hw
          · exact KeepsG.pure _
          · exact KeepsG.pure _
  | ret es => intro _; rw [step]; exact KeepsG.bind (evalArgs_keepsG es) fun _ => KeepsG.pure _
  | call xs f args =>
    intro hr; simp only [Stmt.gsOk, decide_eq_true_eq] at hr; rw [step]
    exact KeepsG.bind (evalArgs_keepsG args) fun vs =>
      KeepsG.bind (invoke_keepsG' hp hk hr vs) fun rs =>
        KeepsG.bind (KeepsG.modify fun s _ _ => by rw [St.setLocs_mem']) fun _ => KeepsG.pure _
  | copy64 d di s si n =>
    intro _; rw [step]
    refine KeepsG.bind (warr_keepsG d) fun da => KeepsG.bind (evalE_keepsG di) fun i =>
      KeepsG.bind (warr_keepsG s) fun sa => KeepsG.bind (evalE_keepsG si) fun j =>
        KeepsG.bind (evalE_keepsG n) fun k => KeepsG.get_bind fun s₀ r s' h g _ => ?_
    split at h
    · exact (KeepsG.pure (G := G) Sig.normal _ r s' h g ‹_›).trans
        (congrFun (Mem.glob_copy64 da sa k.toNat s₀.mem i j) g)
    · cases h
  | copy8w d di b si n =>
    intro _; rw [step]
    refine KeepsG.bind (warr_keepsG d) fun da => KeepsG.bind (evalE_keepsG di) fun i =>
      KeepsG.bind (evalE_keepsG si) fun j =>
        KeepsG.bind (evalE_keepsG n) fun k => KeepsG.get_bind fun s₀ r s' h g _ => ?_
    split at h
    · exact (KeepsG.pure (G := G) Sig.normal _ r s' h g ‹_›).trans
        (congrFun (Mem.glob_copy8w da _ k.toNat s₀.mem i j) g)
    · cases h
  | scan8 x b i e c =>
    intro _; rw [step]
    exact KeepsG.bind (evalE_keepsG i) fun _ => KeepsG.bind (evalE_keepsG e) fun _ =>
      KeepsG.get_bind fun s => by
        dsimp only
        refine KeepsG.ite ?_ (KeepsG.throw _) s
        exact KeepsG.bind (KeepsG.modify fun _ _ _ => rfl) fun _ => KeepsG.pure _

theorem exec_keepsG (hp : globsIn p G fs = true) : ∀ n, KKeepsG G fs (exec p n)
  | 0 => fun _ _ s r s' h => by cases h
  | n + 1 => step_keepsG hp (exec_keepsG hp n)

end stmt

/-- **Kept globals.** A successful run of a function of a set that passes `globsIn` ends with
every global `G` accepts as it started. -/
theorem invoke_keepsG {p : Prog} {G : GVar → Bool} {fs : List FnName}
    (hp : globsIn p G fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word}
    {s : St} {r : List Word} {s' : St} (h : (invoke p (exec p n) f vs).run s = .ok (r, s'))
    {g : GVar} (hg : G g = true) : s'.mem.glob g = s.mem.glob g :=
  invoke_keepsG' hp (exec_keepsG hp n) hf vs s r s' h g hg

/-- The same for `L.run`. -/
theorem run_keepsG {p : Prog} {G : GVar → Bool} {fs : List FnName}
    (hp : globsIn p G fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word}
    {m : Mem} {r : List Word} {m' : Mem} (h : run p n f vs m = .ok (r, m'))
    {g : GVar} (hg : G g = true) : m'.glob g = m.glob g := by
  unfold run at h
  cases hr : (invoke p (exec p n) f vs).run { mem := m, loc := Locals.init [] } with
  | error e => rw [hr] at h; cases h
  | ok q =>
    rw [hr] at h
    cases h
    exact invoke_keepsG hp hf hr hg

end L
