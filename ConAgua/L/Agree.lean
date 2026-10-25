module

public import ConAgua.L.Semantics

@[expose] public section

/-!
# Non-interference: runs that read only agreeing arrays agree

`readsIn p S S8 fs` is a `Bool` check of the program text: every function of `fs` that `p`
defines calls only into `fs`, and every array its body names (loaded, stored, measured, copied
from or to, scanned) is a word array of `S` or a byte array of `S8`. The array sets are
predicates (`S S8 : ArrId → Bool`; a list `l` is `l.contains`). A tiered access
`a⟨t⟩` names both tiers, `a` and `a + tierOff`. Global variables are not restricted.
(`Stmt.rdOk` takes the callee set as a predicate too: `readsIn` uses membership in `fs`, the
per-function split for a large program (`Compiler/ReadSetSplit.lean`) a tree of name codes.)

`Agree S S8 m₁ m₂`: the two memories have the same word arrays in `S`, the same byte arrays in
`S8`, and the same globals. Everything else (other arrays, the number of arrays) may differ.

**The theorem** (`invoke_agree`): for `f ∈ fs` of a set that passes `readsIn`, two runs of
`invoke p (exec p n) f vs` from states that agree (memories `Agree`, equal locals) end the same
way: the same error, or the same returned values from final states that agree again. `run_agree`
is the same for `L.run`. The proof is the frame proof's induction (fuel, then statements): every
read sees equal data, every write writes equal data to an array of `S`/`S8` (or a global).

Why: lane parmode (docs/design/parmode.md, Step 4, piece (b2)). A worker runs `check_pending`
in a memory in which only the frozen images and the worker's own arrays have content; every other
array is empty. That memory agrees with the full sequential memory on `S` = frozen ∪ owned, so
the worker's run is the sequential one, which the sequential proof covers.
-/

namespace L

/-! ## The static check -/

/-- A byte source names only byte arrays of `S8` (constant data: none). -/
def BSrc.rdOk (S8 : ArrId → Bool) : BSrc → Bool
  | .arr a => S8 a
  | .rom _ => true

/-- Both tiers of the tiered array `a` are in `S`. -/
def tierOk (S : ArrId → Bool) (a : ArrId) : Bool := S a && S (a + tierOff)

/-- An expression names only word arrays of `S` and byte arrays of `S8`. -/
def Expr.rdOk (S S8 : ArrId → Bool) : Expr → Bool
  | .const _ => true
  | .var _ => true
  | .glob _ => true
  | .bin _ a b => a.rdOk S S8 && b.rdOk S S8
  | .cmpw _ a b => a.rdOk S S8 && b.rdOk S S8
  | .ld8 a i => S8 a && i.rdOk S S8
  | .ld64 a i => S a && i.rdOk S S8
  | .len8 a => S8 a
  | .len64 a => S a
  | .ldc _ i => i.rdOk S S8
  | .ld64t a t i => tierOk S a && t.rdOk S S8 && i.rdOk S S8
  | .len64t a t => tierOk S a && t.rdOk S S8
  | .ld8x8 s i => s.rdOk S8 && i.rdOk S S8

/-- A block operand names only word arrays of `S` (a tiered one: both tiers). -/
def WArr.rdOk (S S8 : ArrId → Bool) : WArr → Bool
  | .plain a => S a
  | .tier a t => tierOk S a && t.rdOk S S8

def Cond.rdOk (S S8 : ArrId → Bool) : Cond → Bool
  | .cmp _ a b => a.rdOk S S8 && b.rdOk S S8
  | .and p q => p.rdOk S S8 && q.rdOk S S8
  | .or p q => p.rdOk S S8 && q.rdOk S S8
  | .not p => p.rdOk S S8

/-- A statement names only word arrays of `S` and byte arrays of `S8`, and calls only
functions `cf` accepts. -/
def Stmt.rdOk (S S8 : ArrId → Bool) (cf : FnName → Bool) : Stmt → Bool
  | .skip => true
  | .brk => true
  | .abort e => e.rdOk S S8
  | .set _ e => e.rdOk S S8
  | .gset _ e => e.rdOk S S8
  | .st8 a i e => S8 a && i.rdOk S S8 && e.rdOk S S8
  | .st64 a i e => S a && i.rdOk S S8 && e.rdOk S S8
  | .st64t a t i e => tierOk S a && t.rdOk S S8 && i.rdOk S S8 && e.rdOk S S8
  | .seq s t => s.rdOk S S8 cf && t.rdOk S S8 cf
  | .ite c s t => c.rdOk S S8 && s.rdOk S S8 cf && t.rdOk S S8 cf
  | .while c s => c.rdOk S S8 && s.rdOk S S8 cf
  | .ret es => es.all (·.rdOk S S8)
  | .call _ f args => cf f && args.all (·.rdOk S S8)
  | .copy64 d di s si n =>
    d.rdOk S S8 && di.rdOk S S8 && s.rdOk S S8 && si.rdOk S S8 && n.rdOk S S8
  | .copy8w d di s si n =>
    d.rdOk S S8 && di.rdOk S S8 && s.rdOk S8 && si.rdOk S S8 && n.rdOk S S8
  | .scan8 _ s i e _ => s.rdOk S8 && i.rdOk S S8 && e.rdOk S S8

/-- **The read set of a call-closed function set**: every function of `fs` that `p` defines
names only arrays of `S` (words) and `S8` (bytes) and calls only into `fs`. -/
def readsIn (p : Prog) (S S8 : ArrId → Bool) (fs : List FnName) : Bool :=
  fs.all fun f => match p.lookup f with
    | some fd => fd.body.rdOk S S8 (fun g => decide (g ∈ fs))
    | none => true

theorem readsIn_lookup {p : Prog} {S S8 : ArrId → Bool} {fs : List FnName}
    (hp : readsIn p S S8 fs = true) {f : FnName} (hf : f ∈ fs) {fd : FunDecl}
    (h : p.lookup f = some fd) : fd.body.rdOk S S8 (fun g => decide (g ∈ fs)) = true := by
  simp only [readsIn, List.all_eq_true] at hp
  have := hp f hf
  simp only [h] at this
  exact this

/-! ## Agreeing memories, states, results -/

/-- The memories agree on the word arrays `S`, the byte arrays `S8` and the globals. -/
def Agree (S S8 : ArrId → Bool) (m₁ m₂ : Mem) : Prop :=
  (∀ a, S a = true → m₁.arr64 a = m₂.arr64 a) ∧ (∀ a, S8 a = true → m₁.arr8 a = m₂.arr8 a) ∧ m₁.glob = m₂.glob

/-- Agreeing memories and equal locals. -/
def StAgree (S S8 : ArrId → Bool) (s₁ s₂ : St) : Prop :=
  Agree S S8 s₁.mem s₂.mem ∧ s₁.loc = s₂.loc

/-- Two run results correspond: the same error, or the same value and agreeing states. -/
def ResAgree {α : Type} (S S8 : ArrId → Bool) : Except Err (α × St) → Except Err (α × St) → Prop
  | .ok r₁, .ok r₂ => r₁.1 = r₂.1 ∧ StAgree S S8 r₁.2 r₂.2
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

/-- A computation whose runs from agreeing states correspond. -/
def Sim {α : Type} (S S8 : ArrId → Bool) (x : M α) : Prop :=
  ∀ s₁ s₂, StAgree S S8 s₁ s₂ → ResAgree S S8 (x.run s₁) (x.run s₂)

section sim
variable {S S8 : ArrId → Bool}

theorem ResAgree.ok {α : Type} {a₁ a₂ : α} {s₁ s₂ : St} (ha : a₁ = a₂) (h : StAgree S S8 s₁ s₂) :
    ResAgree S S8 (.ok (a₁, s₁)) (.ok (a₂, s₂)) := ⟨ha, h⟩

theorem Sim.pure {α : Type} (a : α) : Sim S S8 (Pure.pure a : M α) :=
  fun _ _ h => ResAgree.ok rfl h

theorem Sim.throw {α : Type} (e : Err) : Sim S S8 (MonadExcept.throw e : M α) :=
  fun _ _ _ => (rfl : e = e)

theorem Sim.bind {α β : Type} {x : M α} {g : α → M β} (hx : Sim S S8 x)
    (hg : ∀ a, Sim S S8 (g a)) : Sim S S8 (x >>= g) := by
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
    show ResAgree S S8 ((g r₁.1).run r₁.2) ((g r₂.1).run r₂.2)
    rw [← e]
    exact hg _ _ _ h2

/-- A computation that starts by reading the state. -/
theorem Sim.get_bind {α : Type} {g : St → M α}
    (h : ∀ s₁ s₂, StAgree S S8 s₁ s₂ → ResAgree S S8 ((g s₁).run s₁) ((g s₂).run s₂)) :
    Sim S S8 (get >>= g) := by
  intro s₁ s₂ hs
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact h s₁ s₂ hs

theorem Sim.modify {f : St → St} (hf : ∀ s₁ s₂, StAgree S S8 s₁ s₂ → StAgree S S8 (f s₁) (f s₂)) :
    Sim S S8 (modify f : M PUnit) :=
  fun s₁ s₂ h => ResAgree.ok rfl (hf s₁ s₂ h)

theorem ResAgree.set {s₁ s₂ t₁ t₂ : St} (h : StAgree S S8 t₁ t₂) :
    ResAgree S S8 ((MonadStateOf.set t₁ : M PUnit).run s₁) ((MonadStateOf.set t₂ : M PUnit).run s₂) :=
  ResAgree.ok rfl h

theorem Sim.dite_pure {α : Type} {c : Prop} [Decidable c] {f : c → α} {e : Err} :
    Sim S S8 (if h : c then Pure.pure (f h) else MonadExcept.throw e : M α) := by
  split
  · exact Sim.pure _
  · exact Sim.throw _

theorem Sim.ite {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : c → Sim S S8 x)
    (hy : ¬c → Sim S S8 y) : Sim S S8 (if c then x else y) := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

/-- A state write of agreeing states, then a computation that runs alike. -/
theorem ResAgree.set_bind {β : Type} {g : PUnit → M β} (hg : Sim S S8 (g ⟨⟩)) {s₁ s₂ t₁ t₂ : St}
    (h : StAgree S S8 t₁ t₂) :
    ResAgree S S8 ((MonadStateOf.set t₁ >>= g : M β).run s₁) ((MonadStateOf.set t₂ >>= g : M β).run s₂) :=
  hg t₁ t₂ h

end sim

/-! ## Memory operations keep agreement -/

private theorem arr64_set64 (m : Mem) (a b : ArrId) (i v : Word) :
    (m.set64 a i v).arr64 b = if b = a then (m.arr64 a).set! i.toNat v else m.arr64 b := by
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?]
  by_cases hb : b = a
  · subst hb; by_cases h : b < m.words.size <;> simp [h]
  · simp only [hb, ite_false]; grind

private theorem arr8_set8 (m : Mem) (a b : ArrId) (i v : Word) :
    (m.set8 a i v).arr8 b = if b = a then (m.arr8 a).set! i.toNat v.toUInt8 else m.arr8 b := by
  simp only [Mem.set8, Mem.arr8, Array.getD_eq_getD_getElem?]
  by_cases hb : b = a
  · subst hb; by_cases h : b < m.bytes.size <;> simp [h]
  · simp only [hb, ite_false]; grind

section mem
variable {S S8 : ArrId → Bool} {m₁ m₂ : Mem}

theorem Agree.set64 (h : Agree S S8 m₁ m₂) {a : ArrId} (ha : S a = true) (i v : Word) :
    Agree S S8 (m₁.set64 a i v) (m₂.set64 a i v) := by
  refine ⟨fun b hb => ?_, fun b hb => h.2.1 b hb, h.2.2⟩
  rw [arr64_set64, arr64_set64, h.1 a ha, h.1 b hb]

theorem Agree.set8 (h : Agree S S8 m₁ m₂) {a : ArrId} (ha : S8 a = true) (i v : Word) :
    Agree S S8 (m₁.set8 a i v) (m₂.set8 a i v) := by
  refine ⟨fun b hb => h.1 b hb, fun b hb => ?_, h.2.2⟩
  rw [arr8_set8, arr8_set8, h.2.1 a ha, h.2.1 b hb]

theorem Agree.setG (h : Agree S S8 m₁ m₂) (g : GVar) (v : Word) :
    Agree S S8 (m₁.setG g v) (m₂.setG g v) := by
  refine ⟨h.1, h.2.1, ?_⟩
  simp only [Mem.setG, h.2.2]

theorem Agree.copy64 {d s : ArrId} (hd : S d = true) (hs : S s = true) :
    ∀ (n : Nat) {m₁ m₂ : Mem} (di si : Word), Agree S S8 m₁ m₂ →
      Agree S S8 (m₁.copy64 d di s si n) (m₂.copy64 d di s si n)
  | 0, _, _, _, _, h => h
  | n + 1, m₁, m₂, di, si, h => by
    simp only [Mem.copy64]
    rw [h.1 s hs]
    exact Agree.copy64 hd hs n _ _ (h.set64 hd _ _)

theorem Agree.copy8w {d : ArrId} (hd : S d = true) (b : Array UInt8) :
    ∀ (n : Nat) {m₁ m₂ : Mem} (di si : Word), Agree S S8 m₁ m₂ →
      Agree S S8 (m₁.copy8w d di b si n) (m₂.copy8w d di b si n)
  | 0, _, _, _, _, h => h
  | n + 1, m₁, m₂, di, si, h => by
    simp only [Mem.copy8w]
    exact Agree.copy8w hd b n _ _ (h.set64 hd _ _)

theorem Agree.src8 (h : Agree S S8 m₁ m₂) {s : BSrc} (hs : s.rdOk S8 = true) :
    m₁.src8 s = m₂.src8 s := by
  cases s with
  | arr a => simp only [BSrc.rdOk] at hs; exact h.2.1 a hs
  | rom d => rfl

theorem tierA_mem {S : ArrId → Bool} {a : ArrId} (h : tierOk S a = true) (t : Word) :
    S (tierA a t) = true := by
  simp only [tierOk, Bool.and_eq_true] at h
  have h2 : (t &&& 1).toNat < 2 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rcases (show (t &&& 1).toNat = 0 ∨ (t &&& 1).toNat = 1 by omega) with e | e <;>
    simp [tierA, e, h.1, h.2]

theorem StAgree.setLoc {s₁ s₂ : St} (h : StAgree S S8 s₁ s₂) (x : Var) (v : Word) :
    StAgree S S8 (s₁.setLoc x v) (s₂.setLoc x v) := by
  refine ⟨h.1, ?_⟩
  simp only [St.setLoc, h.2]

theorem StAgree.setLocs : ∀ (xs : List Var) (vs : List Word) {s₁ s₂ : St},
    StAgree S S8 s₁ s₂ → StAgree S S8 (s₁.setLocs xs vs) (s₂.setLocs xs vs)
  | [], _, _, _, h => h
  | x :: xs, vs, _, _, h => StAgree.setLocs xs vs.tail (h.setLoc x _)

end mem

/-! ## Expressions, conditions, arguments -/

section eval
variable {S S8 : ArrId → Bool}

theorem ld64_sim {a : ArrId} (ha : S a = true) (i : Word) : Sim S S8 (ld64 a i) := by
  unfold ld64
  refine Sim.get_bind fun s₁ s₂ h => ?_
  have e := h.1.1 a ha
  dsimp only
  revert e
  generalize s₁.mem.arr64 a = A₁
  generalize s₂.mem.arr64 a = A₂
  intro e; subst e
  exact Sim.dite_pure s₁ s₂ h

theorem ld8_sim {a : ArrId} (ha : S8 a = true) (i : Word) : Sim S S8 (ld8 a i) := by
  unfold ld8
  refine Sim.get_bind fun s₁ s₂ h => ?_
  have e := h.1.2.1 a ha
  dsimp only
  revert e
  generalize s₁.mem.arr8 a = A₁
  generalize s₂.mem.arr8 a = A₂
  intro e; subst e
  exact Sim.dite_pure s₁ s₂ h

theorem ld8x8_sim {b : BSrc} (hb : b.rdOk S8 = true) (i : Word) : Sim S S8 (ld8x8 b i) := by
  unfold ld8x8
  refine Sim.get_bind fun s₁ s₂ h => ?_
  dsimp only
  rw [h.1.src8 hb]
  generalize s₂.mem.src8 b = B
  exact Sim.ite (fun _ => Sim.pure _) (fun _ => Sim.throw _) s₁ s₂ h

theorem st64_sim {a : ArrId} (ha : S a = true) (i v : Word) : Sim S S8 (st64 a i v) := by
  unfold st64
  refine Sim.get_bind fun s₁ s₂ h => ?_
  rw [h.1.1 a ha]
  by_cases hc : i.toNat < (s₂.mem.arr64 a).size
  · simp only [hc, ↓reduceIte]
    exact ResAgree.set ⟨h.1.set64 ha i v, h.2⟩
  · simp only [hc, ↓reduceIte]
    exact Sim.throw _ s₁ s₂ h

theorem st8_sim {a : ArrId} (ha : S8 a = true) (i v : Word) : Sim S S8 (st8 a i v) := by
  unfold st8
  refine Sim.get_bind fun s₁ s₂ h => ?_
  rw [h.1.2.1 a ha]
  by_cases hc : i.toNat < (s₂.mem.arr8 a).size
  · simp only [hc, ↓reduceIte]
    exact ResAgree.set ⟨h.1.set8 ha i v, h.2⟩
  · simp only [hc, ↓reduceIte]
    exact Sim.throw _ s₁ s₂ h

theorem evalE_sim : ∀ (e : Expr), e.rdOk S S8 = true → Sim S S8 (evalE e) := by
  intro e
  induction e with
  | const w => intro _; rw [evalE]; exact Sim.pure w
  | var x => intro _; rw [evalE]; exact Sim.get_bind fun s₁ s₂ h => ResAgree.ok (by rw [h.2]) h
  | bin op a b iha ihb =>
    intro hr; simp only [Expr.rdOk, Bool.and_eq_true] at hr; rw [evalE]
    exact Sim.bind (iha hr.1) fun _ => Sim.bind (ihb hr.2) fun _ => Sim.pure _
  | cmpw c a b iha ihb =>
    intro hr; simp only [Expr.rdOk, Bool.and_eq_true] at hr; rw [evalE]
    exact Sim.bind (iha hr.1) fun _ => Sim.bind (ihb hr.2) fun _ => Sim.pure _
  | ld8 a i ih =>
    intro hr; simp only [Expr.rdOk, Bool.and_eq_true] at hr; rw [evalE]
    exact Sim.bind (ih hr.2) fun _ => ld8_sim hr.1 _
  | ld64 a i ih =>
    intro hr; simp only [Expr.rdOk, Bool.and_eq_true] at hr; rw [evalE]
    exact Sim.bind (ih hr.2) fun _ => ld64_sim hr.1 _
  | len8 a =>
    intro hr; simp only [Expr.rdOk] at hr; rw [evalE]
    exact Sim.get_bind fun s₁ s₂ h => ResAgree.ok (by simp only [Mem.len8, h.1.2.1 a hr]) h
  | len64 a =>
    intro hr; simp only [Expr.rdOk] at hr; rw [evalE]
    exact Sim.get_bind fun s₁ s₂ h => ResAgree.ok (by simp only [Mem.len64, h.1.1 a hr]) h
  | ldc d i ih =>
    intro hr; simp only [Expr.rdOk] at hr; rw [evalE]
    exact Sim.bind (ih hr) fun _ => by unfold ldc; exact Sim.dite_pure
  | glob g => intro _; rw [evalE]; exact Sim.get_bind fun s₁ s₂ h => ResAgree.ok (by rw [h.1.2.2]) h
  | ld64t a t i iht ihi =>
    intro hr; simp only [Expr.rdOk, Bool.and_eq_true] at hr; rw [evalE]
    exact Sim.bind (iht hr.1.2) fun _ => Sim.bind (ihi hr.2) fun _ => ld64_sim (tierA_mem hr.1.1 _) _
  | len64t a t ih =>
    intro hr; simp only [Expr.rdOk, Bool.and_eq_true] at hr; rw [evalE]
    exact Sim.bind (ih hr.2) fun u => Sim.get_bind fun s₁ s₂ h =>
      ResAgree.ok (by simp only [Mem.len64, h.1.1 _ (tierA_mem hr.1 u)]) h
  | ld8x8 b i ih =>
    intro hr; simp only [Expr.rdOk, Bool.and_eq_true] at hr; rw [evalE]
    exact Sim.bind (ih hr.2) fun _ => ld8x8_sim hr.1 _

theorem evalC_sim : ∀ (c : Cond), c.rdOk S S8 = true → Sim S S8 (evalC c) := by
  intro c
  induction c with
  | cmp c a b =>
    intro hr; simp only [Cond.rdOk, Bool.and_eq_true] at hr; rw [evalC]
    exact Sim.bind (evalE_sim a hr.1) fun _ => Sim.bind (evalE_sim b hr.2) fun _ => Sim.pure _
  | and p q ihp ihq =>
    intro hr; simp only [Cond.rdOk, Bool.and_eq_true] at hr; rw [evalC]
    exact Sim.bind (ihp hr.1) fun b => by
      cases b
      · exact Sim.pure _
      · exact ihq hr.2
  | or p q ihp ihq =>
    intro hr; simp only [Cond.rdOk, Bool.and_eq_true] at hr; rw [evalC]
    exact Sim.bind (ihp hr.1) fun b => by
      cases b
      · exact ihq hr.2
      · exact Sim.pure _
  | not p ih =>
    intro hr; simp only [Cond.rdOk] at hr; rw [evalC]
    exact Sim.bind (ih hr) fun _ => Sim.pure _

theorem evalArgs_sim : ∀ (es : List Expr), es.all (·.rdOk S S8) = true → Sim S S8 (evalArgs es)
  | [], _ => by rw [evalArgs]; exact Sim.pure _
  | e :: es, hr => by
    simp only [List.all_cons, Bool.and_eq_true] at hr
    rw [evalArgs]
    exact Sim.bind (evalE_sim e hr.1) fun _ => Sim.bind (evalArgs_sim es hr.2) fun _ => Sim.pure _

/-- A block operand of `S`, then a computation that runs alike for every array of `S`. -/
theorem warr_bind_sim {β : Type} {w : WArr} (hw : w.rdOk S S8 = true) {g : ArrId → M β}
    (hg : ∀ a, S a = true → Sim S S8 (g a)) : Sim S S8 (warr w >>= g) := by
  cases w with
  | plain a =>
    simp only [WArr.rdOk] at hw
    simp only [warr, pure_bind]
    exact hg a hw
  | tier a t =>
    simp only [WArr.rdOk, Bool.and_eq_true] at hw
    simp only [warr, bind_assoc, pure_bind]
    exact Sim.bind (evalE_sim t hw.2) fun u => hg _ (tierA_mem hw.1 u)

end eval

/-! ## Statements, calls, fuel -/

section stmt
variable {p : Prog} {S S8 : ArrId → Bool} {fs : List FnName}

/-- A continuation whose runs of every checked statement correspond. -/
def KSim (S S8 : ArrId → Bool) (fs : List FnName) (k : Stmt → M Sig) : Prop :=
  ∀ st, st.rdOk S S8 (fun g => decide (g ∈ fs)) = true → Sim S S8 (k st)

theorem invoke_sim (hp : readsIn p S S8 fs = true) {k : Stmt → M Sig} (hk : KSim S S8 fs k)
    {f : FnName} (hf : f ∈ fs) (vs : List Word) : Sim S S8 (invoke p k f vs) := by
  unfold invoke lookupFn
  cases hl : p.lookup f with
  | none => intro s₁ s₂ _; exact (rfl : Err.noFun f = Err.noFun f)
  | some fd =>
    simp only [pure_bind]
    unfold callFn
    refine Sim.get_bind fun s₁ s₂ h => ?_
    rw [show s₁.loc = s₂.loc from h.2]
    refine ResAgree.set_bind ?_ ⟨h.1, rfl⟩
    exact Sim.bind (hk _ (readsIn_lookup hp hf hl)) fun _ =>
      Sim.bind (Sim.modify fun _ _ h' => ⟨h'.1, rfl⟩) fun _ => Sim.pure _

theorem step_sim (hp : readsIn p S S8 fs = true) {k : Stmt → M Sig} (hk : KSim S S8 fs k) :
    KSim S S8 fs (step p k) := by
  intro st
  induction st with
  | skip => intro _; rw [step]; exact Sim.pure _
  | brk => intro _; rw [step]; exact Sim.pure _
  | abort e =>
    intro hr; simp only [Stmt.rdOk] at hr; rw [step]
    exact Sim.bind (evalE_sim e hr) fun _ => Sim.throw _
  | set x e =>
    intro hr; simp only [Stmt.rdOk] at hr; rw [step]
    exact Sim.bind (evalE_sim e hr) fun v =>
      Sim.bind (Sim.modify fun _ _ h => h.setLoc x v) fun _ => Sim.pure _
  | gset g e =>
    intro hr; simp only [Stmt.rdOk] at hr; rw [step]
    exact Sim.bind (evalE_sim e hr) fun v =>
      Sim.bind (Sim.modify fun _ _ h => ⟨h.1.setG g v, h.2⟩) fun _ => Sim.pure _
  | st8 a i e =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    exact Sim.bind (evalE_sim i hr.1.2) fun _ => Sim.bind (evalE_sim e hr.2) fun _ =>
      Sim.bind (st8_sim hr.1.1 _ _) fun _ => Sim.pure _
  | st64 a i e =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    exact Sim.bind (evalE_sim i hr.1.2) fun _ => Sim.bind (evalE_sim e hr.2) fun _ =>
      Sim.bind (st64_sim hr.1.1 _ _) fun _ => Sim.pure _
  | st64t a t i e =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    exact Sim.bind (evalE_sim t hr.1.1.2) fun u => Sim.bind (evalE_sim i hr.1.2) fun _ =>
      Sim.bind (evalE_sim e hr.2) fun _ =>
        Sim.bind (st64_sim (tierA_mem hr.1.1.1 u) _ _) fun _ => Sim.pure _
  | seq s t ihs iht =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    exact Sim.bind (ihs hr.1) fun r => by
      cases r
      · exact iht hr.2
      · exact Sim.pure _
      · exact Sim.pure _
  | ite c s t ihs iht =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    exact Sim.bind (evalC_sim c hr.1.1) fun b => by
      cases b
      · exact iht hr.2
      · exact ihs hr.1.2
  | «while» c s ih =>
    intro hr
    have hw := hr
    simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    exact Sim.bind (evalC_sim c hr.1) fun b => by
      cases b
      · exact Sim.pure _
      · exact Sim.bind (ih hr.2) fun r => by
          cases r
          · exact hk _ hw
          · exact Sim.pure _
          · exact Sim.pure _
  | ret es =>
    intro hr; simp only [Stmt.rdOk] at hr; rw [step]
    exact Sim.bind (evalArgs_sim es hr) fun _ => Sim.pure _
  | call xs f args =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hr; rw [step]
    exact Sim.bind (evalArgs_sim args hr.2) fun vs => Sim.bind (invoke_sim hp hk hr.1 vs) fun rs =>
      Sim.bind (Sim.modify fun _ _ h => h.setLocs xs rs) fun _ => Sim.pure _
  | copy64 d di s si n =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    refine warr_bind_sim hr.1.1.1.1 fun da hda => Sim.bind (evalE_sim di hr.1.1.1.2) fun i =>
      warr_bind_sim hr.1.1.2 fun sa hsa => Sim.bind (evalE_sim si hr.1.2) fun j =>
        Sim.bind (evalE_sim n hr.2) fun k => Sim.get_bind fun s₁ s₂ h => ?_
    rw [h.1.1 da hda, h.1.1 sa hsa]
    by_cases hc : i.toNat + k.toNat ≤ (s₂.mem.arr64 da).size ∧
        j.toNat + k.toNat ≤ (s₂.mem.arr64 sa).size
    · simp only [hc, and_self, ↓reduceIte]
      exact ResAgree.set_bind (g := fun _ => pure Sig.normal) (Sim.pure _)
        ⟨Agree.copy64 hda hsa _ _ _ h.1, h.2⟩
    · simp only [hc, ↓reduceIte]
      exact Sim.throw _ s₁ s₂ h
  | copy8w d di b si n =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    refine warr_bind_sim hr.1.1.1.1 fun da hda => Sim.bind (evalE_sim di hr.1.1.1.2) fun i =>
      Sim.bind (evalE_sim si hr.1.2) fun j =>
        Sim.bind (evalE_sim n hr.2) fun k => Sim.get_bind fun s₁ s₂ h => ?_
    rw [h.1.1 da hda, h.1.src8 hr.1.1.2]
    by_cases hc : i.toNat + k.toNat ≤ (s₂.mem.arr64 da).size ∧
        j.toNat + k.toNat ≤ (s₂.mem.src8 b).size
    · simp only [hc, and_self, ↓reduceIte]
      exact ResAgree.set_bind (g := fun _ => pure Sig.normal) (Sim.pure _)
        ⟨Agree.copy8w hda _ _ _ _ h.1, h.2⟩
    · simp only [hc, ↓reduceIte]
      exact Sim.throw _ s₁ s₂ h
  | scan8 x b i e c =>
    intro hr; simp only [Stmt.rdOk, Bool.and_eq_true] at hr; rw [step]
    refine Sim.bind (evalE_sim i hr.1.2) fun vi => Sim.bind (evalE_sim e hr.2) fun ve =>
      Sim.get_bind fun s₁ s₂ h => ?_
    dsimp only
    rw [h.1.src8 hr.1.1]
    generalize s₂.mem.src8 b = B
    exact Sim.ite (fun _ => Sim.bind (Sim.modify fun _ _ h => h.setLoc x _) fun _ => Sim.pure _)
      (fun _ => Sim.throw _) s₁ s₂ h

theorem exec_sim (hp : readsIn p S S8 fs = true) : ∀ n, KSim S S8 fs (exec p n)
  | 0 => fun _ _ => by rw [show exec p 0 = fun _ => throw .outOfFuel from funext fun _ => rfl]; exact Sim.throw _
  | n + 1 => step_sim hp (exec_sim hp n)

end stmt

/-! ## The theorems -/

/-- **Non-interference.** A function of a set whose bodies read only the word arrays `S` and the
byte arrays `S8` (and call only into the set) runs alike from two states that agree on them and
have the same locals: the same error, or the same results from states that agree again. -/
theorem invoke_agree {p : Prog} {S S8 : ArrId → Bool} {fs : List FnName}
    (hp : readsIn p S S8 fs = true) {f : FnName} (hf : f ∈ fs) (n : Nat) (vs : List Word)
    {s₁ s₂ : St} (hm : Agree S S8 s₁.mem s₂.mem) (hl : s₁.loc = s₂.loc) :
    ResAgree S S8 ((invoke p (exec p n) f vs).run s₁) ((invoke p (exec p n) f vs).run s₂) :=
  invoke_sim hp (exec_sim hp n) hf vs s₁ s₂ ⟨hm, hl⟩

/-- The same, for a successful run from the first state. -/
theorem invoke_agree_ok {p : Prog} {S S8 : ArrId → Bool} {fs : List FnName}
    (hp : readsIn p S S8 fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word}
    {s₁ s₂ : St} (hm : Agree S S8 s₁.mem s₂.mem) (hl : s₁.loc = s₂.loc) {rs : List Word}
    {s₁' : St} (h : (invoke p (exec p n) f vs).run s₁ = .ok (rs, s₁')) :
    ∃ s₂', (invoke p (exec p n) f vs).run s₂ = .ok (rs, s₂') ∧
      Agree S S8 s₁'.mem s₂'.mem ∧ s₁'.loc = s₂'.loc := by
  have := invoke_agree hp hf n vs hm hl
  rw [h] at this
  revert this
  cases (invoke p (exec p n) f vs).run s₂ with
  | error e => intro h'; exact h'.elim
  | ok r =>
    obtain ⟨r₁, r₂⟩ := r
    intro h'
    obtain ⟨e, h''⟩ := h'
    dsimp only at e h''
    subst e
    exact ⟨r₂, rfl, h''⟩

/-- Two results of `L.run` correspond: the same error, or the same values and agreeing final
memories. -/
def RunAgree (S S8 : ArrId → Bool) : Except Err (List Word × Mem) → Except Err (List Word × Mem) → Prop
  | .ok r₁, .ok r₂ => r₁.1 = r₂.1 ∧ Agree S S8 r₁.2 r₂.2
  | .error e₁, .error e₂ => e₁ = e₂
  | _, _ => False

/-- **Non-interference for `L.run`.** -/
theorem run_agree {p : Prog} {S S8 : ArrId → Bool} {fs : List FnName}
    (hp : readsIn p S S8 fs = true) {f : FnName} (hf : f ∈ fs) (n : Nat) (vs : List Word)
    {m₁ m₂ : Mem} (hm : Agree S S8 m₁ m₂) :
    RunAgree S S8 (run p n f vs m₁) (run p n f vs m₂) := by
  have := invoke_agree hp hf n vs (s₁ := { mem := m₁, loc := Locals.init [] })
    (s₂ := { mem := m₂, loc := Locals.init [] }) hm rfl
  unfold run
  revert this
  cases (invoke p (exec p n) f vs).run { mem := m₁, loc := Locals.init [] } <;>
    cases (invoke p (exec p n) f vs).run { mem := m₂, loc := Locals.init [] } <;>
    intro h
  · exact h
  · exact h.elim
  · exact h.elim
  · exact ⟨h.1, h.2.1⟩

/-- The same, for a successful run on the first memory. -/
theorem run_agree_ok {p : Prog} {S S8 : ArrId → Bool} {fs : List FnName}
    (hp : readsIn p S S8 fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word}
    {m₁ m₂ : Mem} (hm : Agree S S8 m₁ m₂) {rs : List Word} {m₁' : Mem}
    (h : run p n f vs m₁ = .ok (rs, m₁')) :
    ∃ m₂', run p n f vs m₂ = .ok (rs, m₂') ∧ Agree S S8 m₁' m₂' := by
  have := run_agree hp hf n vs hm
  rw [h] at this
  revert this
  cases run p n f vs m₂ with
  | error e => intro h'; exact h'.elim
  | ok r =>
    obtain ⟨r₁, r₂⟩ := r
    intro h'
    obtain ⟨e, h''⟩ := h'
    dsimp only at e h''
    subst e
    exact ⟨r₂, rfl, h''⟩

/-! ## Example

`sum` adds up word array `3` through the callee `get` and stores the total into tier `1` of the
tiered array `5` (word array `5 + tierOff = 261`). Its call closure reads only `3`, `5`, `261`. -/

/-- The body of `sum`. -/
def agreeExSum : Stmt :=
  .seq (.set 1 (.const 0))
    (.seq (.«while» (.cmp .ult (.var 0) (.len64 3))
        (.seq (.call [2] "get" [.var 0])
          (.seq (.set 1 (.bin .add (.var 1) (.var 2)))
            (.set 0 (.bin .add (.var 0) (.const 1))))))
      (.seq (.st64t 5 (.const 1) (.const 0) (.var 1)) (.ret [.var 1])))

/-- The word arrays `sum` reads. -/
def w3 : ArrId → Bool := ([3, 5, 261] : List ArrId).contains

/-- No byte arrays. -/
def none8 : ArrId → Bool := fun _ => false

/-- A tiny test program for the check (not the checker). -/
def agreeEx : Prog :=
  [("get", { nparams := 1, nlocals := 1, body := .ret [.ld64 3 (.var 0)] }),
   ("sum", { nparams := 0, nlocals := 3, body := agreeExSum })]

#guard readsIn agreeEx w3 none8 ["get", "sum"]
-- a tiered store names both tiers
#guard !readsIn agreeEx ([3, 5] : List ArrId).contains none8 ["get", "sum"]
-- the set must be call-closed
#guard !readsIn agreeEx w3 none8 ["sum"]

theorem agreeEx_reads : readsIn agreeEx w3 none8 ["get", "sum"] = true := by decide

/-- Two memories that agree on arrays `3`, `5`, `261` and the globals run `sum` alike (whatever
else they hold). -/
example (n : Nat) (m₁ m₂ : Mem) (h : Agree w3 none8 m₁ m₂) :
    RunAgree w3 none8 (run agreeEx n "sum" [] m₁) (run agreeEx n "sum" [] m₂) :=
  run_agree agreeEx_reads (by decide) n [] h

end L
