module

public import ConAgua.Compiler.Inline
public import ConAgua.L.DefAssignSim

@[expose] public section

set_option linter.unusedSimpArgs false

namespace L.Compiler

open L

/-! ## Expressions as values -/

/-- The value of an expression in a state (`evalE` without the state). -/
def Expr.ev (s : St) : Expr → Except Err Word
  | .const w => .ok w
  | .var x => .ok (s.loc x)
  | .bin op a b => do let x ← Expr.ev s a; let y ← Expr.ev s b; pure (op.eval x y)
  | .ld8 a i => do
    let j ← Expr.ev s i
    if h : j.toNat < (s.mem.arr8 a).size then pure (s.mem.arr8 a)[j.toNat].toUInt64 else .error .oob
  | .ld64 a i => do
    let j ← Expr.ev s i
    if h : j.toNat < (s.mem.arr64 a).size then pure (s.mem.arr64 a)[j.toNat] else .error .oob
  | .len8 a => .ok (s.mem.len8 a)
  | .len64 a => .ok (s.mem.len64 a)
  | .cmpw c a b => do let x ← Expr.ev s a; let y ← Expr.ev s b; pure (c.evalW x y)
  | .ldc d i => do
    let j ← Expr.ev s i
    if h : j.toNat < d.length then pure d[j.toNat].toUInt64 else .error .oob
  | .glob g => .ok (s.mem.glob g)
  | .ld64t a t i => do
    let u ← Expr.ev s t
    let j ← Expr.ev s i
    if h : j.toNat < (s.mem.arr64 (tierA a u)).size then pure (s.mem.arr64 (tierA a u))[j.toNat] else .error .oob
  | .len64t a t => do let u ← Expr.ev s t; pure (s.mem.len64 (tierA a u))
  | .ld8x8 b i => do
    let j ← Expr.ev s i
    if j.toNat + 8 ≤ (s.mem.src8 b).size then pure (le64 (s.mem.src8 b) j.toNat) else .error .oob
  | .ld32t a t i => do
    let u ← Expr.ev s t
    let j ← Expr.ev s i
    if h : (j / 2).toNat < (s.mem.arr64 (tierA a u)).size then pure (half32 (s.mem.arr64 (tierA a u))[(j / 2).toNat] j)
    else .error .oob
  | .ld32h a t i hi => do
    let u ← Expr.ev s t
    let j ← Expr.ev s i
    if h : j.toNat < (s.mem.arr64 (tierA a u)).size then pure (half32b hi (s.mem.arr64 (tierA a u))[j.toNat]) else .error .oob

theorem run_bind_ev {α β : Type} {x : M α} {f : α → M β} {s : St} {r : Except Err α} {g : α → Except Err β}
    (hx : x.run s = r.map (·, s)) (hf : ∀ a, (f a).run s = (g a).map (·, s)) :
    (x >>= f).run s = (r >>= g).map (·, s) := by
  rw [StateT.run_bind, hx]
  cases r with
  | error e => rfl
  | ok a => exact hf a

theorem run_pure_ev {α : Type} (a : α) (s : St) : (pure a : M α).run s = (pure a : Except Err α).map (·, s) := rfl

theorem run_get_ev {α : Type} {f : St → M α} {s : St} : (get >>= f).run s = (f s).run s := rfl

theorem run_dite_ev {α : Type} {c : Prop} [Decidable c] {a : c → α} {s : St} :
    (if h : c then pure (a h) else throw .oob : M α).run s =
      (if h : c then pure (a h) else .error .oob : Except Err α).map (·, s) := by
  split <;> rfl

theorem run_ite_ev {α : Type} {c : Prop} [Decidable c] {a : α} {s : St} :
    (if c then pure a else throw .oob : M α).run s = (if c then pure a else .error .oob : Except Err α).map (·, s) := by
  split <;> rfl

theorem evalE_run (e : Expr) (s : St) : (evalE e).run s = (Expr.ev s e).map (·, s) := by
  induction e generalizing s with
  | const w => rfl
  | var x => rfl
  | len8 a => rfl
  | len64 a => rfl
  | glob g => rfl
  | bin op a b iha ihb =>
    exact run_bind_ev (iha s) fun x => run_bind_ev (ihb s) fun y => run_pure_ev _ _
  | cmpw op a b iha ihb =>
    exact run_bind_ev (iha s) fun x => run_bind_ev (ihb s) fun y => run_pure_ev _ _
  | ld8 a i ih => exact run_bind_ev (ih s) fun j => run_dite_ev
  | ld64 a i ih => exact run_bind_ev (ih s) fun j => run_dite_ev
  | ldc d i ih => exact run_bind_ev (ih s) fun j => run_dite_ev
  | ld8x8 b i ih => exact run_bind_ev (ih s) fun j => run_ite_ev
  | len64t a t ih => exact run_bind_ev (ih s) fun u => run_pure_ev _ _
  | ld64t a t i iht ihi => exact run_bind_ev (iht s) fun u => run_bind_ev (ihi s) fun j => run_dite_ev
  | ld32t a t i iht ihi => exact run_bind_ev (iht s) fun u => run_bind_ev (ihi s) fun j => run_dite_ev
  | ld32h a t i hi iht ihi =>
    refine run_bind_ev (iht s) fun u => run_bind_ev (ihi s) fun j => ?_
    refine (run_bind_ev (x := L.ld64 (tierA a u) j) run_dite_ev fun w => run_pure_ev (half32b hi w) s).trans ?_
    split <;> rfl

def Cond.ev (s : St) : Cond → Except Err Bool
  | .cmp c a b => do let x ← Expr.ev s a; let y ← Expr.ev s b; pure (c.eval x y)
  | .and p q => do if (← Cond.ev s p) then Cond.ev s q else pure false
  | .or p q => do if (← Cond.ev s p) then pure true else Cond.ev s q
  | .not p => do pure (!(← Cond.ev s p))

def Exprs.ev (s : St) : List Expr → Except Err (List Word)
  | [] => pure []
  | e :: es => do let v ← Expr.ev s e; let vs ← Exprs.ev s es; pure (v :: vs)

def WArr.ev (s : St) : WArr → Except Err TieredArray
  | .plain a => pure a
  | .tier a t => do pure (tierA a (← Expr.ev s t))

theorem evalC_run (c : Cond) (s : St) : (evalC c).run s = (Cond.ev s c).map (·, s) := by
  induction c generalizing s with
  | cmp op a b => exact run_bind_ev (evalE_run a s) fun x => run_bind_ev (evalE_run b s) fun y => run_pure_ev _ _
  | and p q ihp ihq =>
    refine run_bind_ev (ihp s) fun x => ?_
    cases x
    · exact run_pure_ev _ _
    · exact ihq s
  | or p q ihp ihq =>
    refine run_bind_ev (ihp s) fun x => ?_
    cases x
    · exact ihq s
    · exact run_pure_ev _ _
  | not p ih => exact run_bind_ev (ih s) fun x => run_pure_ev _ _

theorem evalArgs_run (es : List Expr) (s : St) : (evalArgs es).run s = (Exprs.ev s es).map (·, s) := by
  induction es with
  | nil => rfl
  | cons e es ih => exact run_bind_ev (evalE_run e s) fun x => run_bind_ev ih fun y => run_pure_ev _ _

theorem warr_run (w : WArr) (s : St) : (warr w).run s = (WArr.ev s w).map (·, s) := by
  cases w with
  | plain a => rfl
  | tier a t => exact run_bind_ev (evalE_run t s) fun x => run_pure_ev _ _

/-! ## Shifted expressions -/

theorem Expr.sh_zero : ∀ e : Expr, Expr.sh 0 e = e
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => rfl
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ => by
    simp only [Expr.sh, Expr.sh_zero a, Expr.sh_zero b]
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => by simp only [Expr.sh, Expr.sh_zero i]

section shift
variable {o : Nat} {v s' : St}

theorem Expr.ev_sh (hm : v.mem = s'.mem) : ∀ (e : Expr), (∀ x < Expr.vb e, v.loc x = s'.loc (x + o)) →
    Expr.ev s' (Expr.sh o e) = Expr.ev v e := by
  intro e
  induction e with
  | var x => intro hl; simp [Expr.ev, Expr.sh, hl x (by simp [Expr.vb])]
  | bin _ a b iha ihb | cmpw _ a b iha ihb | ld64t _ a b iha ihb | ld32t _ a b iha ihb | ld32h _ a b _ iha ihb =>
    intro hl
    simp only [Expr.ev, Expr.sh, hm, iha fun x h => hl x (by simp only [Expr.vb, Cond.vb, Exprs.vb]; omega), ihb fun x h => hl x (by simp only [Expr.vb, Cond.vb, Exprs.vb]; omega)]
  | ld8 _ i ih | ld64 _ i ih | ldc _ i ih | len64t _ i ih | ld8x8 _ i ih =>
    intro hl
    simp only [Expr.ev, Expr.sh, hm, ih fun x h => hl x (by simpa [Expr.vb] using h)]
  | _ => intro _; simp [Expr.ev, Expr.sh, hm]

theorem Cond.ev_sh (hm : v.mem = s'.mem) : ∀ (c : Cond), (∀ x < Cond.vb c, v.loc x = s'.loc (x + o)) →
    Cond.ev s' (Cond.sh o c) = Cond.ev v c := by
  intro c
  induction c with
  | cmp _ a b =>
    intro hl
    simp only [Cond.ev, Cond.sh, Expr.ev_sh hm a fun x h => hl x (by simp only [Expr.vb, Cond.vb, Exprs.vb]; omega), Expr.ev_sh hm b fun x h => hl x (by simp only [Expr.vb, Cond.vb, Exprs.vb]; omega)]
  | and p q ihp ihq | or p q ihp ihq =>
    intro hl
    simp only [Cond.ev, Cond.sh, ihp fun x h => hl x (by simp only [Expr.vb, Cond.vb, Exprs.vb]; omega), ihq fun x h => hl x (by simp only [Expr.vb, Cond.vb, Exprs.vb]; omega)]
  | not p ih => intro hl; simp only [Cond.ev, Cond.sh, ih fun x h => hl x (by simpa [Cond.vb] using h)]

theorem Exprs.ev_sh (hm : v.mem = s'.mem) : ∀ (es : List Expr), (∀ x < Exprs.vb es, v.loc x = s'.loc (x + o)) →
    Exprs.ev s' (es.map (Expr.sh o)) = Exprs.ev v es := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    intro hl
    simp only [List.map_cons, Exprs.ev, Expr.ev_sh hm e fun x h => hl x (by simp only [Expr.vb, Cond.vb, Exprs.vb]; omega), ih fun x h => hl x (by simp only [Expr.vb, Cond.vb, Exprs.vb]; omega)]

theorem WArr.ev_sh (hm : v.mem = s'.mem) (w : WArr) (hl : ∀ x < WArr.vb w, v.loc x = s'.loc (x + o)) :
    WArr.ev s' (WArr.sh o w) = WArr.ev v w := by
  cases w with
  | plain a => rfl
  | tier a t => simp only [WArr.ev, WArr.sh, Expr.ev_sh hm t hl]

end shift

/-! ## Simple statements as functions of the state -/

/-- One step of a statement without a call, a loop, a branch, a sequence or an exit. -/
def sstep (s : St) : Stmt → Except Err (Sig × St)
  | .set x e => do let w ← Expr.ev s e; pure (.normal, s.setLoc x w)
  | .st8 a i e => do
    let j ← Expr.ev s i
    let w ← Expr.ev s e
    if j.toNat < (s.mem.arr8 a).size then pure (.normal, { s with mem := s.mem.set8 a j w }) else .error .oob
  | .st64 a i e => do
    let j ← Expr.ev s i
    let w ← Expr.ev s e
    if j.toNat < (s.mem.arr64 a).size then pure (.normal, { s with mem := s.mem.set64 a j w }) else .error .oob
  | .abort e => do let k ← Expr.ev s e; .error (.abort k)
  | .gset g e => do let w ← Expr.ev s e; pure (.normal, s.setG g w)
  | .st64t a t i e => do
    let u ← Expr.ev s t
    let j ← Expr.ev s i
    let w ← Expr.ev s e
    if j.toNat < (s.mem.arr64 (tierA a u)).size then pure (.normal, { s with mem := s.mem.set64 (tierA a u) j w })
    else .error .oob
  | .st32t a t i e => do
    let u ← Expr.ev s t
    let j ← Expr.ev s i
    let w ← Expr.ev s e
    if (j / 2).toNat < (s.mem.arr64 (tierA a u)).size then pure (.normal, { s with mem := s.mem.set32 (tierA a u) j w })
    else .error .oob
  | .copy64 d di sr si n => do
    let da ← WArr.ev s d
    let i ← Expr.ev s di
    let sa ← WArr.ev s sr
    let j ← Expr.ev s si
    let k ← Expr.ev s n
    if i.toNat + k.toNat ≤ (s.mem.arr64 da).size ∧ j.toNat + k.toNat ≤ (s.mem.arr64 sa).size then
      pure (.normal, { s with mem := s.mem.copy64 da i sa j k.toNat })
    else .error .oob
  | .copy8w d di sr si n => do
    let da ← WArr.ev s d
    let i ← Expr.ev s di
    let j ← Expr.ev s si
    let k ← Expr.ev s n
    if i.toNat + k.toNat ≤ (s.mem.arr64 da).size ∧ j.toNat + k.toNat ≤ (s.mem.src8 sr).size then
      pure (.normal, { s with mem := s.mem.copy8w da i (s.mem.src8 sr) j k.toNat })
    else .error .oob
  | .scan8 x sr i e c => do
    let vi ← Expr.ev s i
    let ve ← Expr.ev s e
    if vi ≤ ve ∧ ve.toNat ≤ (s.mem.src8 sr).size then
      pure (.normal, s.setLoc x (UInt64.ofNat (scanN (s.mem.src8 sr) c vi.toNat ve.toNat)))
    else .error .oob
  | _ => .ok (.normal, s)

/-- The statements `sstep` covers (`skip` included). -/
def Stmt.simple : Stmt → Bool
  | .skip | .set .. | .st8 .. | .st64 .. | .abort _ | .gset .. | .st64t .. | .st32t .. | .copy64 ..
  | .copy8w .. | .scan8 .. => true
  | _ => false

theorem run_bind_st {α β : Type} {x : M α} {f : α → M β} {s : St} {r : Except Err α}
    (hx : x.run s = r.map (·, s)) : (x >>= f).run s = r.bind fun a => (f a).run s := by
  rw [StateT.run_bind, hx]
  cases r <;> rfl

theorem st8_run' (a : ArrId) (j w : Word) (s : St) : (L.st8 a j w).run s =
    if j.toNat < (s.mem.arr8 a).size then .ok ((), { s with mem := s.mem.set8 a j w }) else .error .oob := by
  show (if j.toNat < (s.mem.arr8 a).size then (set { s with mem := s.mem.set8 a j w } : M Unit) else throw .oob).run s = _
  split <;> rfl

theorem st64_run' (a : TieredArray) (j w : Word) (s : St) : (L.st64 a j w).run s =
    if j.toNat < (s.mem.arr64 a).size then .ok ((), { s with mem := s.mem.set64 a j w }) else .error .oob := by
  show (if j.toNat < (s.mem.arr64 a).size then (set { s with mem := s.mem.set64 a j w } : M Unit) else throw .oob).run s = _
  split <;> rfl

theorem st32_run' (a : TieredArray) (j w : Word) (s : St) : (L.st32 a j w).run s =
    if (j / 2).toNat < (s.mem.arr64 a).size then .ok ((), { s with mem := s.mem.set32 a j w }) else .error .oob := by
  show (if (j / 2).toNat < (s.mem.arr64 a).size then (set { s with mem := s.mem.set32 a j w } : M Unit) else throw .oob).run s = _
  split <;> rfl

theorem step_simple (p : Prog) (k : Stmt → M Sig) (s : St) :
    ∀ u : Stmt, Stmt.simple u = true → (step p k u).run s = sstep s u
  | .skip, _ => rfl
  | .set x e, _ => by
    simp only [step, sstep]; rw [run_bind_st (evalE_run e s)]; cases Expr.ev s e <;> rfl
  | .st8 a i e, _ => by
    simp only [step, sstep]; rw [run_bind_st (evalE_run i s)]; cases Expr.ev s i <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run e s)]; cases Expr.ev s e <;> try rfl
    simp only [Except.bind]; rw [StateT.run_bind, st8_run']; split <;> rename_i h <;> simp only [bind, Except.bind, h, ite_true, ite_false] <;> rfl
  | .st64 a i e, _ => by
    simp only [step, sstep]; rw [run_bind_st (evalE_run i s)]; cases Expr.ev s i <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run e s)]; cases Expr.ev s e <;> try rfl
    simp only [Except.bind]; rw [StateT.run_bind, st64_run']; split <;> rename_i h <;> simp only [bind, Except.bind, h, ite_true, ite_false] <;> rfl
  | .abort e, _ => by
    simp only [step, sstep]; rw [run_bind_st (evalE_run e s)]; cases Expr.ev s e <;> rfl
  | .gset g e, _ => by
    simp only [step, sstep]; rw [run_bind_st (evalE_run e s)]; cases Expr.ev s e <;> rfl
  | .st64t a t i e, _ => by
    simp only [step, sstep]; rw [run_bind_st (evalE_run t s)]; cases Expr.ev s t <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run i s)]; cases Expr.ev s i <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run e s)]; cases Expr.ev s e <;> try rfl
    simp only [Except.bind]; rw [StateT.run_bind, st64_run']; split <;> rename_i h <;> simp only [bind, Except.bind, h, ite_true, ite_false] <;> rfl
  | .st32t a t i e, _ => by
    simp only [step, sstep]; rw [run_bind_st (evalE_run t s)]; cases Expr.ev s t <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run i s)]; cases Expr.ev s i <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run e s)]; cases Expr.ev s e <;> try rfl
    simp only [Except.bind]; rw [StateT.run_bind, st32_run']; split <;> rename_i h <;> simp only [bind, Except.bind, h, ite_true, ite_false] <;> rfl
  | .copy64 d di sr si n, _ => by
    simp only [step, sstep]; rw [run_bind_st (warr_run d s)]; cases WArr.ev s d <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run di s)]; cases Expr.ev s di <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (warr_run sr s)]; cases WArr.ev s sr <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run si s)]; cases Expr.ev s si <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run n s)]; cases Expr.ev s n <;> try rfl
    simp only [Except.bind]; rw [run_get_ev]; split <;> rename_i h <;> simp only [bind, Except.bind, h, ite_true, ite_false] <;> rfl
  | .copy8w d di sr si n, _ => by
    simp only [step, sstep]; rw [run_bind_st (warr_run d s)]; cases WArr.ev s d <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run di s)]; cases Expr.ev s di <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run si s)]; cases Expr.ev s si <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run n s)]; cases Expr.ev s n <;> try rfl
    simp only [Except.bind]; rw [run_get_ev]; split <;> rename_i h <;> simp only [bind, Except.bind, h, ite_true, ite_false] <;> rfl
  | .scan8 x sr i e c, _ => by
    simp only [step, sstep]; rw [run_bind_st (evalE_run i s)]; cases Expr.ev s i <;> try rfl
    simp only [Except.bind]; rw [run_bind_st (evalE_run e s)]; cases Expr.ev s e <;> try rfl
    simp only [Except.bind]; rw [run_get_ev]; split <;> rename_i h <;> simp only [bind, Except.bind, h, ite_true, ite_false] <;> rfl
  | .seq .., h | .ite .., h | .while .., h | .brk, h | .ret _, h | .call .., h => by simp [Stmt.simple] at h

/-! ## The shift relation -/

/-- `v`, the callee's frame, and `s'`, the caller's frame with the callee's locals at `o`: equal
memories, the callee's local `x < B` is the caller's `x + o`, and the caller's locals below `o`
are `c`. -/
structure AR (o B : Nat) (c : Locals) (v s' : St) : Prop where
  mem : v.mem = s'.mem
  loc : ∀ x < B, v.loc x = s'.loc (x + o)
  low : ∀ y < o, s'.loc y = c y

theorem AR.sub {o B : Nat} {c : Locals} {v s' : St} (h : AR o B c v s') {n : Nat} (hn : n ≤ B) :
    ∀ x < n, v.loc x = s'.loc (x + o) := fun x hx => h.loc x (by omega)

theorem AR.setLoc {o B : Nat} {c : Locals} {v s' : St} (h : AR o B c v s') (x : Var) (w : Word) :
    AR o B c (v.setLoc x w) (s'.setLoc (x + o) w) where
  mem := h.mem
  loc z hz := by
    simp only [St.setLoc]
    by_cases e : z = x
    · simp [e]
    · have : z + o ≠ x + o := by omega
      simp [e, this, h.loc z hz]
  low y hy := by
    have : y ≠ x + o := by omega
    simp [St.setLoc, this, h.low y hy]

theorem AR.withMem {o B : Nat} {c : Locals} {v s' : St} (h : AR o B c v s') (m : Mem) :
    AR o B c { v with mem := m } { s' with mem := m } := ⟨rfl, h.loc, h.low⟩

/-- Exact correspondence of two runs: the same error, or the same value from `Q`-related states. -/
def Ex {α : Type} (Q : α → St → St → Prop) (r' r : Except Err (α × St)) : Prop :=
  match r with
  | .error e => r' = .error e
  | .ok (a, v1) => ∃ s1', r' = .ok (a, s1') ∧ Q a v1 s1'

theorem Ex.ok {α : Type} {Q : α → St → St → Prop} {a : α} {v1 s1' : St} (h : Q a v1 s1') :
    Ex Q (.ok (a, s1')) (.ok (a, v1)) := ⟨_, rfl, h⟩

theorem Ex.err {α : Type} {Q : α → St → St → Prop} (e : Err) : Ex Q (.error e) (.error e) := rfl

section sstep
variable {o B : Nat} {c : Locals} {v s' : St} {b : Bool}

/-- **A shifted simple statement does what the statement does on the callee's frame.** -/
theorem sstep_sh (h : AR o B c v s') :
    ∀ (u u' : Stmt), Stmt.simple u = true → Stmt.sh o b u = some u' → Stmt.vb u ≤ B →
    Ex (fun sig v1 s1' => AR o B c v1 s1' ∧ sig = .normal) (sstep s' u') (sstep v u)
  | .skip, _, _, hu, _ => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu; exact Ex.ok ⟨h, rfl⟩
  | .set x e, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, Expr.ev_sh h.mem e (h.sub (n := Expr.vb e) (by omega))]
    cases Expr.ev v e with
    | error => exact Ex.err _
    | ok w => exact Ex.ok ⟨h.setLoc x w, rfl⟩
  | .st8 a i e, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [Expr.ev_sh h.mem i (h.sub (n := Expr.vb i) (by omega))]
    cases Expr.ev v i with
    | error => exact Ex.err _
    | ok iv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem e (h.sub (n := Expr.vb e) (by omega))]
    cases Expr.ev v e with
    | error => exact Ex.err _
    | ok ev =>
    try simp only [bind, Except.bind]
    split
    · exact Ex.ok ⟨h.withMem _, rfl⟩
    · exact Ex.err _
  | .st64 a i e, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [Expr.ev_sh h.mem i (h.sub (n := Expr.vb i) (by omega))]
    cases Expr.ev v i with
    | error => exact Ex.err _
    | ok iv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem e (h.sub (n := Expr.vb e) (by omega))]
    cases Expr.ev v e with
    | error => exact Ex.err _
    | ok ev =>
    try simp only [bind, Except.bind]
    split
    · exact Ex.ok ⟨h.withMem _, rfl⟩
    · exact Ex.err _
  | .abort e, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [Expr.ev_sh h.mem e (h.sub (n := Expr.vb e) (by omega))]
    cases Expr.ev v e with
    | error => exact Ex.err _
    | ok ev =>
    try simp only [bind, Except.bind]
    exact Ex.err _
  | .gset g e, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [Expr.ev_sh h.mem e (h.sub (n := Expr.vb e) (by omega))]
    cases Expr.ev v e with
    | error => exact Ex.err _
    | ok ev =>
    try simp only [bind, Except.bind]
    exact Ex.ok ⟨by rw [St.setG, St.setG, ← h.mem]; exact h.withMem _, rfl⟩
  | .st64t a t i e, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [Expr.ev_sh h.mem t (h.sub (n := Expr.vb t) (by omega))]
    cases Expr.ev v t with
    | error => exact Ex.err _
    | ok tv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem i (h.sub (n := Expr.vb i) (by omega))]
    cases Expr.ev v i with
    | error => exact Ex.err _
    | ok iv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem e (h.sub (n := Expr.vb e) (by omega))]
    cases Expr.ev v e with
    | error => exact Ex.err _
    | ok ev =>
    try simp only [bind, Except.bind]
    split
    · exact Ex.ok ⟨h.withMem _, rfl⟩
    · exact Ex.err _
  | .st32t a t i e, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [Expr.ev_sh h.mem t (h.sub (n := Expr.vb t) (by omega))]
    cases Expr.ev v t with
    | error => exact Ex.err _
    | ok tv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem i (h.sub (n := Expr.vb i) (by omega))]
    cases Expr.ev v i with
    | error => exact Ex.err _
    | ok iv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem e (h.sub (n := Expr.vb e) (by omega))]
    cases Expr.ev v e with
    | error => exact Ex.err _
    | ok ev =>
    try simp only [bind, Except.bind]
    split
    · exact Ex.ok ⟨h.withMem _, rfl⟩
    · exact Ex.err _
  | .copy64 d di sr si n, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [WArr.ev_sh h.mem d (h.sub (n := WArr.vb d) (by omega))]
    cases WArr.ev v d with
    | error => exact Ex.err _
    | ok dv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem di (h.sub (n := Expr.vb di) (by omega))]
    cases Expr.ev v di with
    | error => exact Ex.err _
    | ok div =>
    try simp only [bind, Except.bind]
    rw [WArr.ev_sh h.mem sr (h.sub (n := WArr.vb sr) (by omega))]
    cases WArr.ev v sr with
    | error => exact Ex.err _
    | ok srv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem si (h.sub (n := Expr.vb si) (by omega))]
    cases Expr.ev v si with
    | error => exact Ex.err _
    | ok siv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem n (h.sub (n := Expr.vb n) (by omega))]
    cases Expr.ev v n with
    | error => exact Ex.err _
    | ok nv =>
    try simp only [bind, Except.bind]
    split
    · exact Ex.ok ⟨h.withMem _, rfl⟩
    · exact Ex.err _
  | .copy8w d di sr si n, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [WArr.ev_sh h.mem d (h.sub (n := WArr.vb d) (by omega))]
    cases WArr.ev v d with
    | error => exact Ex.err _
    | ok dv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem di (h.sub (n := Expr.vb di) (by omega))]
    cases Expr.ev v di with
    | error => exact Ex.err _
    | ok div =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem si (h.sub (n := Expr.vb si) (by omega))]
    cases Expr.ev v si with
    | error => exact Ex.err _
    | ok siv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem n (h.sub (n := Expr.vb n) (by omega))]
    cases Expr.ev v n with
    | error => exact Ex.err _
    | ok nv =>
    try simp only [bind, Except.bind]
    split
    · exact Ex.ok ⟨h.withMem _, rfl⟩
    · exact Ex.err _
  | .scan8 x sr i e cl, _, _, hu, hb => by
    simp only [Stmt.sh, Option.some.injEq] at hu; subst hu
    simp only [Stmt.vb] at hb
    simp only [sstep, ← h.mem]
    rw [Expr.ev_sh h.mem i (h.sub (n := Expr.vb i) (by omega))]
    cases Expr.ev v i with
    | error => exact Ex.err _
    | ok iv =>
    try simp only [bind, Except.bind]
    rw [Expr.ev_sh h.mem e (h.sub (n := Expr.vb e) (by omega))]
    cases Expr.ev v e with
    | error => exact Ex.err _
    | ok ev =>
    try simp only [bind, Except.bind]
    split
    · exact Ex.ok ⟨h.setLoc x _, rfl⟩
    · exact Ex.err _
  | .seq .., _, hs, _, _ | .ite .., _, hs, _, _ | .while .., _, hs, _, _ | .brk, _, hs, _, _
  | .ret _, _, hs, _, _ | .call .., _, hs, _, _ => by simp [Stmt.simple] at hs

end sstep

theorem simple_sh {o : Nat} {b : Bool} : ∀ {u u' : Stmt}, Stmt.simple u = true → Stmt.sh o b u = some u' →
    Stmt.simple u' = true
  | .skip, _, _, h | .set .., _, _, h | .st8 .., _, _, h | .st64 .., _, _, h | .abort _, _, _, h
  | .gset .., _, _, h | .st64t .., _, _, h | .st32t .., _, _, h | .copy64 .., _, _, h | .copy8w .., _, _, h
  | .scan8 .., _, _, h => by simp only [Stmt.sh, Option.some.injEq] at h; subst h; rfl
  | .seq .., _, hs, _ | .ite .., _, hs, _ | .while .., _, hs, _ | .brk, _, hs, _ | .ret _, _, hs, _
  | .call .., _, hs, _ => by simp [Stmt.simple] at hs

/-! ## Steps of the compound statements as functions of the state -/

section steps
variable (p : Prog) (k : Stmt → M Sig) (s : St)

theorem step_seq_run (a b : Stmt) : (step p k (.seq a b)).run s =
    match (step p k a).run s with
    | .ok (.normal, s1) => (step p k b).run s1
    | .ok (r, s1) => .ok (r, s1)
    | .error e => .error e := by
  simp only [step, StateT.run_bind]
  rcases (step p k a).run s with e | ⟨r, s1⟩
  · rfl
  · cases r <;> rfl

theorem step_ite_run (cnd : Cond) (a b : Stmt) : (step p k (.ite cnd a b)).run s =
    match Cond.ev s cnd with
    | .ok true => (step p k a).run s
    | .ok false => (step p k b).run s
    | .error e => .error e := by
  simp only [step]
  rw [run_bind_st (evalC_run cnd s)]
  rcases Cond.ev s cnd with e | (_ | _) <;> rfl

theorem step_while_run (cnd : Cond) (a : Stmt) : (step p k (.while cnd a)).run s =
    match Cond.ev s cnd with
    | .ok true =>
      match (step p k a).run s with
      | .ok (.normal, s1) => (k (.while cnd a)).run s1
      | .ok (.brk, s1) => .ok (.normal, s1)
      | .ok (.ret vs, s1) => .ok (.ret vs, s1)
      | .error e => .error e
    | .ok false => .ok (.normal, s)
    | .error e => .error e := by
  simp only [step]
  rw [run_bind_st (evalC_run cnd s)]
  rcases Cond.ev s cnd with e | (_ | _)
  · rfl
  · rfl
  · simp only [Except.bind, ite_true]
    rw [StateT.run_bind]
    rcases (step p k a).run s with e | ⟨r, s1⟩
    · rfl
    · cases r <;> rfl

theorem step_brk_run : (step p k .brk).run s = .ok (.brk, s) := rfl

theorem step_ret_run (es : List Expr) : (step p k (.ret es)).run s = (Exprs.ev s es).map (fun vs => (.ret vs, s)) := by
  simp only [step]
  rw [run_bind_st (evalArgs_run es s)]
  cases Exprs.ev s es <;> rfl

end steps

/-! ## Shifted statements -/

section shiftStmt
variable {p p' : Prog} {o B : Nat} {c : Locals}

/-- The post of a shifted statement: related states, and a normal end (or a `break`, in a loop). -/
def ShQ (o B : Nat) (c : Locals) (inLoop : Bool) (sig : Sig) (v1 s1' : St) : Prop :=
  AR o B c v1 s1' ∧ (sig = .normal ∨ (inLoop = true ∧ sig = .brk))

/-- Continuations that run shifted loops as the loops. -/
def KSh (o B : Nat) (c : Locals) (k' k : Stmt → M Sig) : Prop :=
  ∀ (cnd : Cond) (b b' : Stmt), Stmt.sh o true b = some b' → Cond.vb cnd ≤ B → Stmt.vb b ≤ B →
    ∀ v s', AR o B c v s' →
      Ex (fun sig v1 s1' => AR o B c v1 s1' ∧ sig = .normal) ((k' (.while (Cond.sh o cnd) b')).run s')
        ((k (.while cnd b)).run v)

theorem shift_step {k' k : Stmt → M Sig} (hK : KSh o B c k' k) :
    ∀ (u : Stmt) (inLoop : Bool) (u' : Stmt), Stmt.sh o inLoop u = some u' → Stmt.vb u ≤ B →
    ∀ v s', AR o B c v s' → Ex (ShQ o B c inLoop) ((step p' k' u').run s') ((step p k u).run v) := by
  intro u
  induction u with
  | seq a b iha ihb =>
    intro inLoop u' hu hb v s' h
    simp only [Stmt.sh, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hu
    obtain ⟨a', ha, b', hb', rfl⟩ := hu
    simp only [Stmt.vb] at hb
    rw [step_seq_run, step_seq_run]
    have H := iha inLoop a' ha (by omega) v s' h
    revert H
    rcases (step p k a).run v with e | ⟨r, v1⟩
    · intro H; rw [H]; rfl
    · rintro ⟨s1', e1, hQ, hr⟩
      rw [e1]
      rcases hr with rfl | ⟨hl, rfl⟩
      · exact ihb inLoop b' hb' (by omega) v1 s1' hQ
      · exact Ex.ok ⟨hQ, .inr ⟨hl, rfl⟩⟩
  | ite cnd a b iha ihb =>
    intro inLoop u' hu hb v s' h
    simp only [Stmt.sh, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hu
    obtain ⟨a', ha, b', hb', rfl⟩ := hu
    simp only [Stmt.vb] at hb
    rw [step_ite_run, step_ite_run, Cond.ev_sh h.mem cnd (h.sub (n := Cond.vb cnd) (by omega))]
    rcases Cond.ev v cnd with e | (_ | _)
    · exact Ex.err _
    · exact ihb inLoop b' hb' (by omega) v s' h
    · exact iha inLoop a' ha (by omega) v s' h
  | «while» cnd a ih =>
    intro inLoop u' hu hb v s' h
    simp only [Stmt.sh, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hu
    obtain ⟨a', ha, rfl⟩ := hu
    simp only [Stmt.vb] at hb
    rw [step_while_run, step_while_run, Cond.ev_sh h.mem cnd (h.sub (n := Cond.vb cnd) (by omega))]
    rcases Cond.ev v cnd with e | (_ | _)
    · exact Ex.err _
    · exact Ex.ok ⟨h, .inl rfl⟩
    · have H := ih true a' ha (by omega) v s' h
      revert H
      rcases (step p k a).run v with e | ⟨r, v1⟩
      · intro H; rw [H]; rfl
      · rintro ⟨s1', e1, hQ, hr⟩
        rw [e1]
        rcases hr with rfl | ⟨-, rfl⟩
        · dsimp only
          have H2 := hK cnd a a' ha (by omega) (by omega) v1 s1' hQ
          revert H2
          rcases (k (.while cnd a)).run v1 with e | ⟨r2, v2⟩
          · intro H2; exact H2
          · rintro ⟨s2', e2, hQ2, rfl⟩
            exact ⟨s2', e2, hQ2, .inl rfl⟩
        · exact Ex.ok ⟨hQ, .inl rfl⟩
  | brk =>
    intro inLoop u' hu _ v s' h
    cases inLoop
    · simp [Stmt.sh] at hu
    · simp only [Stmt.sh, ite_true, Option.some.injEq] at hu
      subst hu
      exact Ex.ok ⟨h, .inr ⟨rfl, rfl⟩⟩
  | ret es => intro _ _ hu; simp [Stmt.sh] at hu
  | call xs f args => intro _ _ hu; simp [Stmt.sh] at hu
  | _ =>
    intro inLoop u' hu hb v s' h
    rw [step_simple p k v _ rfl, step_simple p' k' s' _ (simple_sh rfl hu)]
    have H := sstep_sh h _ _ rfl hu hb
    revert H
    generalize sstep v _ = r
    rcases r with e | ⟨r, v1⟩
    · exact id
    · rintro ⟨s1', e1, hQ, rfl⟩; exact ⟨s1', e1, hQ, .inl rfl⟩

/-- **Shifted loops run as the loops**, at the same fuel. -/
theorem shift_exec : ∀ n, KSh o B c (exec p' n) (exec p n)
  | 0 => fun _ _ _ _ _ _ _ _ _ => rfl
  | n + 1 => fun cnd b b' hb hc hbb v s' h => by
    have H := shift_step (p := p) (p' := p') (shift_exec n) (.while cnd b) false (.while (Cond.sh o cnd) b')
      (by simp [Stmt.sh, hb]) (by simp only [Stmt.vb]; omega) v s' h
    show Ex _ ((step p' (exec p' n) _).run s') ((step p (exec p n) _).run v)
    revert H
    rcases (step p (exec p n) (.while cnd b)).run v with e | ⟨r, v1⟩
    · exact id
    · rintro ⟨s1', e1, ⟨hQ, hr⟩⟩
      exact ⟨s1', e1, hQ, by simpa using hr⟩

end shiftStmt

/-! ## Exits as assignments -/

theorem Expr.ev_safe (s : St) : ∀ (e : Expr), Expr.safe e = true → ∃ w, Expr.ev s e = .ok w
  | .const _, _ | .var _, _ | .len8 _, _ | .len64 _, _ | .glob _, _ => ⟨_, rfl⟩
  | .bin _ a b, h | .cmpw _ a b, h => by
    simp only [Expr.safe, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := Expr.ev_safe s a h.1
    obtain ⟨y, hy⟩ := Expr.ev_safe s b h.2
    exact ⟨_, by simp only [Expr.ev, hx, hy]; rfl⟩
  | .ld8 .., h | .ld64 .., h | .ldc .., h | .ld64t .., h | .len64t .., h | .ld8x8 .., h | .ld32t .., h
  | .ld32h .., h => by simp [Expr.safe] at h

theorem Expr.safe_sh (o : Nat) : ∀ (e : Expr), Expr.safe (Expr.sh o e) = Expr.safe e
  | .bin _ a b | .cmpw _ a b => by simp only [Expr.sh, Expr.safe, Expr.safe_sh o a, Expr.safe_sh o b]
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ | .ld8 .. | .ld64 .. | .ldc .. | .ld64t .. | .len64t ..
  | .ld8x8 .. | .ld32t .. | .ld32h .. => rfl

theorem Exprs.ev_length {s : St} : ∀ {es : List Expr} {vs : List Word}, Exprs.ev s es = .ok vs → vs.length = es.length
  | [], vs, h => by simp only [Exprs.ev, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | e :: es, vs, h => by
    simp only [Exprs.ev] at h
    cases he : Expr.ev s e with
    | error => rw [he] at h; cases h
    | ok w =>
      rw [he] at h
      cases hes : Exprs.ev s es with
      | error => simp [hes, bind, Except.bind] at h
      | ok ws =>
        simp only [hes, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [Exprs.ev_length hes]

theorem Exprs.ev_safe (s : St) : ∀ (es : List Expr), es.all Expr.safe = true → ∃ ws, Exprs.ev s es = .ok ws
  | [], _ => ⟨_, rfl⟩
  | e :: es, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := Expr.ev_safe s e h.1
    obtain ⟨y, hy⟩ := Exprs.ev_safe s es h.2
    exact ⟨_, by simp only [Exprs.ev, hx, hy]; rfl⟩

theorem St.setLocs_mem : ∀ (s : St) (xs : List Var) (vs : List Word), (s.setLocs xs vs).mem = s.mem
  | _, [], _ => rfl
  | s, _ :: xs, vs => St.setLocs_mem (s.setLoc _ _) xs vs.tail

theorem St.setLocs_low : ∀ (s : St) (xs : List Var) (vs : List Word) (y : Var), y ∉ xs → (s.setLocs xs vs).loc y = s.loc y
  | _, [], _, _, _ => rfl
  | s, x :: xs, vs, y, hy => by
    simp only [List.mem_cons, not_or] at hy
    rw [St.setLocs, St.setLocs_low _ xs _ y hy.2]
    simp [St.setLoc, hy.1]

/-- **`xs := es` (shifted) sets `xs` to the values of `es` on the callee's frame**, or fails as
`return es` does. -/
theorem retAssign_run (p' : Prog) (k' : Stmt → M Sig) {o : Nat} {v : St} :
    ∀ (xs : List Var) (es : List Expr) (ra : Stmt) (s' : St), retAssign xs (es.map (Expr.sh o)) = some ra →
    (∀ x ∈ xs, x < o) → v.mem = s'.mem → (∀ z < Exprs.vb es, v.loc z = s'.loc (z + o)) →
    (step p' k' ra).run s' = (Exprs.ev v es).map (fun vs => (.normal, s'.setLocs xs vs))
  | [], es, ra, s', h, _, _, _ => by
    simp only [retAssign, List.all_map] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq] at h; subst h
      have hs' : es.all Expr.safe = true := by
        simpa [Function.comp_def, Expr.safe_sh] using hs
      obtain ⟨ws, hw⟩ := Exprs.ev_safe v es hs'
      rw [hw]; rfl
    · cases h
  | x :: xs, [], ra, s', h, hx, hm, _ => by
    simp only [List.map_nil, retAssign, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨r, hr, rfl⟩ := h
    rw [step_seq_run]
    have := retAssign_run p' k' xs [] r (s'.setLoc x 0) (by simpa using hr) (fun y hy => hx y (by simp [hy]))
      hm (fun z hz => by simp [Exprs.vb] at hz)
    simp only [step_simple p' k' s' (.set x (.const 0)) rfl, sstep, Expr.ev, bind, Except.bind, pure, Except.pure]
    rw [this]; rfl
  | x :: xs, e :: es, ra, s', h, hx, hm, hl => by
    simp only [List.map_cons, retAssign, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨r, hr, rfl⟩ := h
    rw [step_seq_run, step_simple p' k' s' _ rfl]
    simp only [sstep, Exprs.ev]
    rw [Expr.ev_sh hm e (fun z hz => hl z (by simp only [Exprs.vb]; omega))]
    cases Expr.ev v e with
    | error => rfl
    | ok w =>
      simp only [bind, Except.bind, pure, Except.pure]
      have hx0 : x < o := hx x (by simp)
      rw [retAssign_run p' k' xs es r (s'.setLoc x w) hr (fun y hy => hx y (by simp [hy])) hm (fun z hz => by
        rw [hl z (by simp only [Exprs.vb]; omega)]
        have : z + o ≠ x := fun e => absurd (e ▸ Nat.le_add_left o z) (Nat.not_le.mpr hx0)
        simp [St.setLoc, this])]
      cases Exprs.ev v es <;> rfl

/-! ## The converted body -/

theorem allExit_ne {p : Prog} {k : Stmt → M Sig} : ∀ (u : Stmt), Stmt.allExit u = true → ∀ v v1,
    (step p k u).run v ≠ .ok (.normal, v1)
  | .ret es, _, v, v1 => by
    rw [step_ret_run]; cases Exprs.ev v es <;> simp [Except.map]
  | .abort e, _, v, v1 => by
    rw [step_simple p k v _ rfl]; simp only [sstep]; cases Expr.ev v e <;> simp [bind, Except.bind]
  | .brk, _, v, v1 => by simp [step_brk_run]
  | .seq a b, h, v, v1 => by
    simp only [Stmt.allExit, Bool.or_eq_true] at h
    rw [step_seq_run]
    rcases ha : (step p k a).run v with e | ⟨r, v2⟩
    · simp
    · cases r with
      | normal =>
        rcases h with h | h
        · exact absurd ha (allExit_ne a h v v2)
        · exact allExit_ne b h v2 v1
      | _ => simp
  | .ite c a b, h, v, v1 => by
    simp only [Stmt.allExit, Bool.and_eq_true] at h
    rw [step_ite_run]
    rcases Cond.ev v c with e | (_ | _)
    · simp
    · exact allExit_ne b h.2 v v1
    · exact allExit_ne a h.1 v v1
  | .skip, h, _, _ | .set .., h, _, _ | .st8 .., h, _, _ | .st64 .., h, _, _ | .while .., h, _, _
  | .call .., h, _, _ | .gset .., h, _, _ | .st64t .., h, _, _ | .copy64 .., h, _, _ | .copy8w .., h, _, _
  | .scan8 .., h, _, _ | .st32t .., h, _, _ => by simp [Stmt.allExit] at h

section conv
variable {p p' : Prog} {o B : Nat} {c : Locals} {xs : List Var}

/-- What the converted statement does, after what the statement does on the callee's frame: a
normal end continues with `k`, an exit sets `xs`. -/
def ConvPost (p' : Prog) (k' : Stmt → M Sig) (o B : Nat) (c : Locals) (xs : List Var) (k : Stmt)
    (r' : Except Err (Sig × St)) : Except Err (Sig × St) → Prop
  | .error e => r' = .error e
  | .ok (.normal, v1) => ∃ s1', AR o B c v1 s1' ∧ r' = (step p' k' k).run s1'
  | .ok (.ret vs, v1) => ∃ s1', AR o B c v1 s1' ∧ r' = .ok (.normal, s1'.setLocs xs vs)
  | .ok (.brk, v1) => ∃ s1', AR o B c v1 s1' ∧ r' = .ok (.normal, s1'.setLocs xs [])

theorem conv_simple (k : Stmt) : ∀ u : Stmt, Stmt.simple u = true → (∀ e, u ≠ .abort e) →
    conv o xs u k = (Stmt.sh o false u).map (fun u' => .seq u' k)
  | .skip, _, _ | .set .., _, _ | .st8 .., _, _ | .st64 .., _, _ | .gset .., _, _ | .st64t .., _, _
  | .st32t .., _, _ | .copy64 .., _, _ | .copy8w .., _, _ | .scan8 .., _, _ => rfl
  | .abort e, _, h => absurd rfl (h e)
  | .seq .., hs, _ | .ite .., hs, _ | .while .., hs, _ | .brk, hs, _ | .ret _, hs, _ | .call .., hs, _ => by
    simp [Stmt.simple] at hs

/-- A statement shifted and continued by `k` (a simple statement, a loop, or an `if` without exits). -/
theorem conv_seq_sh {k' kk : Stmt → M Sig} (hK : KSh o B c k' kk) {u u_sh k : Stmt}
    (hu : Stmt.sh o false u = some u_sh) (hb : Stmt.vb u ≤ B) {v s' : St} (h : AR o B c v s') :
    ConvPost p' k' o B c xs k ((step p' k' (.seq u_sh k)).run s') ((step p kk u).run v) := by
  have H := shift_step (p := p) (p' := p') hK u false u_sh hu hb v s' h
  rw [step_seq_run]
  revert H
  rcases (step p kk u).run v with e | ⟨r, v1⟩
  · intro H; rw [H]; rfl
  · rintro ⟨s1', e1, hQ, hr⟩
    simp only [Bool.false_eq_true, false_and, or_false] at hr
    subst hr
    rw [e1]
    exact ⟨s1', hQ, rfl⟩

theorem conv_step {k' kk : Stmt → M Sig} (hK : KSh o B c k' kk) (hxs : ∀ x ∈ xs, x < o) :
    ∀ (u k u' : Stmt), conv o xs u k = some u' → Stmt.vb u ≤ B → ∀ v s', AR o B c v s' →
    ConvPost p' k' o B c xs k ((step p' k' u').run s') ((step p kk u).run v) := by
  intro u
  induction u with
  | seq a b iha ihb =>
    intro k u' hu hb v s' h
    simp only [conv, Option.bind_eq_bind, Option.bind_eq_some_iff] at hu
    obtain ⟨kb, hkb, hu⟩ := hu
    simp only [Stmt.vb] at hb
    have H := iha kb u' hu (by omega) v s' h
    rw [step_seq_run]
    revert H
    rcases (step p kk a).run v with e | ⟨r, v1⟩
    · exact id
    · cases r with
      | normal =>
        rintro ⟨s1', hQ, e1⟩
        rw [e1]
        exact ihb k kb hkb (by omega) v1 s1' hQ
      | brk => exact id
      | ret vs => exact id
  | ite cnd a b iha ihb =>
    intro k u' hu hb v s' h
    simp only [Stmt.vb] at hb
    have hc := Cond.ev_sh h.mem cnd (h.sub (n := Cond.vb cnd) (by omega))
    simp only [conv] at hu
    split at hu
    · rename_i hA
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hu
      obtain ⟨a', ha, b', hb', rfl⟩ := hu
      rw [step_ite_run, step_ite_run, hc]
      rcases Cond.ev v cnd with e | (_ | _)
      · rfl
      · exact ihb k b' hb' (by omega) v s' h
      · have H := iha .skip a' ha (by omega) v s' h
        have hne := allExit_ne (p := p) (k := kk) a hA v
        revert H hne
        rcases (step p kk a).run v with e | ⟨r, v1⟩
        · exact fun H _ => H
        · cases r with
          | normal => intro _ hne; exact absurd rfl (hne v1)
          | brk => exact fun H _ => H
          | ret vs => exact fun H _ => H
    · split at hu
      · rename_i _ hB
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hu
        obtain ⟨a', ha, b', hb', rfl⟩ := hu
        rw [step_ite_run, step_ite_run, hc]
        rcases Cond.ev v cnd with e | (_ | _)
        · rfl
        · have H := ihb .skip b' hb' (by omega) v s' h
          have hne := allExit_ne (p := p) (k := kk) b hB v
          revert H hne
          rcases (step p kk b).run v with e | ⟨r, v1⟩
          · exact fun H _ => H
          · cases r with
            | normal => intro _ hne; exact absurd rfl (hne v1)
            | brk => exact fun H _ => H
            | ret vs => exact fun H _ => H
        · exact iha k a' ha (by omega) v s' h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hu
        obtain ⟨u_sh, hsh, rfl⟩ := hu
        exact conv_seq_sh hK hsh (by simp only [Stmt.vb]; omega) h
  | «while» cnd a _ =>
    intro k u' hu hb v s' h
    simp only [conv, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hu
    obtain ⟨a', ha, rfl⟩ := hu
    exact conv_seq_sh hK (u := .while cnd a) (by simp [Stmt.sh, ha]) hb h
  | brk =>
    intro k u' hu _ v s' h
    simp only [conv] at hu
    rw [step_brk_run]
    refine ⟨s', h, ?_⟩
    rw [retAssign_run p' k' xs [] u' s' (by simpa using hu) hxs h.mem (fun z hz => by simp [Exprs.vb] at hz)]
    rfl
  | ret es =>
    intro k u' hu hb v s' h
    simp only [conv] at hu
    simp only [Stmt.vb] at hb
    rw [step_ret_run, retAssign_run p' k' xs es u' s' hu hxs h.mem (h.sub hb)]
    cases Exprs.ev v es with
    | error e => rfl
    | ok vs => exact ⟨s', h, rfl⟩
  | call => intro k u' hu; simp [conv] at hu
  | abort e =>
    intro k u' hu hb v s' h
    simp only [conv, Option.some.injEq] at hu
    subst hu
    rw [step_simple p kk v _ rfl, step_simple p' k' s' _ rfl]
    simp only [Stmt.vb] at hb
    simp only [sstep, Expr.ev_sh h.mem e (h.sub hb)]
    cases Expr.ev v e <;> rfl
  | _ =>
    intro k u' hu hb v s' h
    rw [conv_simple k _ rfl (by simp)] at hu
    simp only [Option.map_eq_some_iff] at hu
    obtain ⟨u_sh, hsh, rfl⟩ := hu
    exact conv_seq_sh hK hsh hb h

end conv

/-! ## The inlined call -/

theorem callFn_run (k : Stmt → M Sig) (fd : FunDecl) (vs : List Word) (s : St) :
    (callFn k fd vs).run s =
      match (k fd.body).run { s with loc := Locals.init vs } with
      | .error e => .error e
      | .ok (r, s1) => .ok (r.retVal, { s1 with loc := s.loc }) := by
  show ((k fd.body >>= fun r => modify (fun s' : St => { s' with loc := s.loc }) >>= fun _ => pure r.retVal) : M _).run
    { s with loc := Locals.init vs } = _
  rw [StateT.run_bind]
  rcases (k fd.body).run { s with loc := Locals.init vs } with e | ⟨r, s1⟩ <;> rfl

theorem step_call_run (p : Prog) (k : Stmt → M Sig) (s : St) (xs : List Var) (g : FnName) (args : List Expr) :
    (step p k (.call xs g args)).run s =
      match Exprs.ev s args with
      | .error e => .error e
      | .ok vs =>
        match p.lookup g with
        | none => .error (.noFun g)
        | some fd =>
          match (k fd.body).run { s with loc := Locals.init vs } with
          | .error e => .error e
          | .ok (r, s1) => .ok (.normal, ({ s1 with loc := s.loc } : St).setLocs xs r.retVal) := by
  simp only [step]
  rw [run_bind_st (evalArgs_run args s)]
  cases Exprs.ev s args with
  | error e => rfl
  | ok vs =>
    simp only [Except.bind, invoke, lookupFn]
    rw [StateT.run_bind, StateT.run_bind]
    cases p.lookup g with
    | none => rfl
    | some fd =>
      show (do let q ← (callFn k fd vs).run s; _) = _
      rw [callFn_run]
      dsimp only
      rcases (k fd.body).run { s with loc := Locals.init vs } with e | ⟨r, s1⟩ <;> rfl

theorem St.setLocs_agree {o : Nat} : ∀ (a b : St) (xs : List Var) (vs : List Word), (∀ y < o, a.loc y = b.loc y) →
    ∀ y < o, (a.setLocs xs vs).loc y = (b.setLocs xs vs).loc y
  | _, _, [], _, h => h
  | a, b, x :: xs, vs, h => St.setLocs_agree (a.setLoc x _) (b.setLoc x _) xs vs.tail fun y hy => by
      simp only [St.setLoc]; split <;> simp [h y hy]

/-- `zeroS`: the callee's zeroed locals. -/
theorem zeroS_run (p' : Prog) (k' : Stmt → M Sig) (o : Nat) : ∀ (zs : List Var) (s' : St), ∃ sz,
    (step p' k' (zeroS o zs)).run s' = .ok (.normal, sz) ∧ sz.mem = s'.mem ∧
    (∀ y, (∀ x ∈ zs, y ≠ x + o) → sz.loc y = s'.loc y) ∧ (∀ x ∈ zs, sz.loc (x + o) = 0)
  | [], s' => ⟨s', rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h⟩
  | x :: zs, s' => by
    obtain ⟨sz, h1, h2, h3, h4⟩ := zeroS_run p' k' o zs (s'.setLoc (x + o) 0)
    refine ⟨sz, ?_, h2, fun y hy => ?_, fun z hz => ?_⟩
    · rw [zeroS, step_seq_run, step_simple p' k' s' _ rfl]
      exact h1
    · rw [h3 y fun z hz => hy z (by simp [hz])]
      simp [St.setLoc, hy x (by simp)]
    · simp only [List.mem_cons] at hz
      by_cases hin : ∃ z' ∈ zs, z + o = z' + o
      · obtain ⟨z', hz', e⟩ := hin
        rw [e]; exact h4 z' hz'
      · rcases hz with rfl | hz
        · rw [h3 _ fun z' hz' e => hin ⟨z', hz', e⟩]; simp [St.setLoc]
        · exact absurd ⟨z, hz, rfl⟩ hin

theorem low_ne {o y x : Nat} (hy : y < o) : y ≠ x + o := fun e => absurd (e ▸ Nat.le_add_left o x) (Nat.not_le.mpr hy)

/-- `paramS`: the callee's parameters from the arguments, evaluated in the caller's frame. -/
theorem paramS_run (p' : Prog) (k' : Stmt → M Sig) (o : Nat) {v : St} : ∀ (args : List Expr) (i : Nat) (s' : St),
    v.mem = s'.mem → (∀ y < Exprs.vb args, v.loc y = s'.loc y) → Exprs.vb args ≤ o →
    (step p' k' (paramS o i args)).run s' =
      (Exprs.ev v args).map fun vs => (.normal, s'.setLocs ((List.range vs.length).map (· + i + o)) vs)
  | [], i, s', _, _, _ => rfl
  | a :: as, i, s', hm, hl, hb => by
    simp only [Exprs.vb] at hb hl
    rw [paramS, step_seq_run, step_simple p' k' s' _ rfl]
    simp only [sstep, Exprs.ev]
    have ha : Expr.ev s' a = Expr.ev v a := by
      have := Expr.ev_sh (o := 0) hm a (fun x hx => hl x (by omega))
      rwa [show Expr.sh 0 a = a from Expr.sh_zero a] at this
    rw [ha]
    cases Expr.ev v a with
    | error => rfl
    | ok w =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [paramS_run p' k' o as (i + 1) (s'.setLoc (i + o) w) hm (fun y hy => by
        rw [hl y (by omega)]; simp [St.setLoc, low_ne (x := i) (show y < o by omega)]) (by omega)]
      cases Exprs.ev v as with
      | error => rfl
      | ok ws =>
        simp only [Except.map, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
        show _ = Except.ok (_, (s'.setLoc (0 + i + o) w).setLocs _ ws)
        rw [Nat.zero_add]
        congr 4
        funext x
        show x + (i + 1) + o = x.succ + i + o
        simp only [Nat.succ_eq_add_one]; ac_rfl

theorem setLocs_range : ∀ (vs : List Word) (i : Nat) (s : St) (y : Nat),
    (s.setLocs ((List.range vs.length).map (· + i)) vs).loc y =
      if i ≤ y ∧ y < i + vs.length then vs.getD (y - i) 0 else s.loc y
  | [], i, s, y => by simp only [St.setLocs, List.length_nil, Nat.add_zero]; split <;> first | rfl | omega
  | w :: ws, i, s, y => by
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, St.setLocs, List.headD,
      List.tail, Nat.zero_add]
    have := setLocs_range ws (i + 1) (s.setLoc i w) y
    rw [show ((fun x => x + i) ∘ Nat.succ) = (· + (i + 1)) from funext fun x => by
      simp only [Function.comp_apply, Nat.succ_eq_add_one]; ac_rfl, this]
    simp only [St.setLoc]
    by_cases h1 : i + 1 ≤ y ∧ y < i + 1 + ws.length
    · have h1' : i ≤ y ∧ y < i + (ws.length + 1) := by omega
      simp only [h1, h1', ↓reduceIte]
      obtain ⟨d, rfl⟩ : ∃ d, y = i + 1 + d := ⟨y - (i + 1), by omega⟩
      rw [show i + 1 + d - i = d + 1 by omega, show i + 1 + d - (i + 1) = d by omega]
      simp
    · simp only [h1, ↓reduceIte]
      by_cases h2 : y = i
      · subst h2; simp
      · have h3 : ¬ (i ≤ y ∧ y < i + (ws.length + 1)) := by omega
        simp only [h2, h3, ↓reduceIte]

theorem Vars.lt_vb : ∀ {xs : List Nat} {x : Nat}, x ∈ xs → x < Vars.vb xs
  | y :: ys, x, h => by
    simp only [List.mem_cons] at h
    simp only [Vars.vb]
    rcases h with rfl | h
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (Vars.lt_vb h) (Nat.le_max_right _ _)

theorem DaAg.symm' {N : Var → Prop} {D : List Var} {a b : St} (h : DaAg N D a b) : DaAg N D b a :=
  ⟨h.1.symm, fun x hx => (h.2 x hx).symm⟩

/-! ## The caller's frame -/

/-- The caller's frame in the original and in the inlined program: equal memories, equal locals
below `o`. -/
structure CR (o : Nat) (v s' : St) : Prop where
  mem : v.mem = s'.mem
  loc : ∀ y < o, v.loc y = s'.loc y

/-- **A run of the inlined program refines one of the original**: running out of fuel refines
anything, an error the same error, a value the same value from `Q`-related states. -/
def Ref {α : Type} (Q : α → St → St → Prop) (r' r : Except Err (α × St)) : Prop :=
  match r' with
  | .error .outOfFuel => True
  | .error e => r = .error e
  | .ok (a, s1') => ∃ v1, r = .ok (a, v1) ∧ Q a v1 s1'

theorem Ref.err {α : Type} {Q : α → St → St → Prop} (e : Err) : Ref Q (.error e) (.error e) := by
  cases e <;> trivial

theorem Ref.ok {α : Type} {Q : α → St → St → Prop} {a : α} {v1 s1' : St} (h : Q a v1 s1') :
    Ref Q (.ok (a, s1')) (.ok (a, v1)) := ⟨v1, rfl, h⟩

/-- **The inlined call does what the call does.** -/
theorem inl_call {p p' : Prog} {n o : Nat} {fd : FunDecl} {xs : List Var} {g : FnName} {args : List Expr}
    {t' : Stmt} (hlk : p.lookup g = some fd) (hi : inlBody o fd xs args = some t')
    (hb : Stmt.vb (.call xs g args) ≤ o) {v s' : St} (h : CR o v s') :
    Ref (fun _ => CR o) ((step p' (exec p' n) t').run s') ((step p (exec p (n + 1)) (.call xs g args)).run v) := by
  simp only [inlBody] at hi
  split at hi
  case isFalse => cases hi
  rename_i hlen
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hi
  obtain ⟨en, hen, b, hbody, rfl⟩ := hi
  simp only [Stmt.vb] at hb
  have hxs : ∀ x ∈ xs, x < o := fun x hx =>
    Nat.lt_of_lt_of_le (Vars.lt_vb hx) (Nat.le_trans (Nat.le_max_left _ _) hb)
  obtain ⟨sz, hz1, hz2, hz3, hz4⟩ := zeroS_run p' (exec p' n) o (needZero fd.nparams fd.body) s'
  rw [step_seq_run, hz1]
  dsimp only
  rw [step_seq_run, paramS_run p' (exec p' n) o (v := v) args 0 sz (h.mem.trans hz2.symm)
    (fun y hy => by rw [h.loc y (by omega), hz3 y fun x _ => low_ne (by omega)]) (by omega)]
  rw [step_call_run]
  cases hev : Exprs.ev v args with
  | error e => exact Ref.err e
  | ok vs =>
    simp only [Except.map, hlk]
    have hvl : vs.length = fd.nparams := by
      rw [← hlen]; exact Exprs.ev_length hev
    -- the callee's frame in the caller's, and the run from it
    let sp : St := sz.setLocs ((List.range vs.length).map (· + 0 + o)) vs
    let vw : St := ⟨sp.mem, fun x => sp.loc (x + o)⟩
    have hsp : ∀ x : Nat, sp.loc (x + o) = if x < vs.length then vs.getD x 0 else sz.loc (x + o) := fun x => by
      have := setLocs_range vs o sz (x + o)
      show (sz.setLocs (List.map (fun x => x + 0 + o) _) vs).loc (x + o) = _
      rw [show (fun x => x + 0 + o) = (· + o) from funext fun _ => by simp, this]
      by_cases hx : x < vs.length
      · have hc : o ≤ x + o ∧ x + o < o + vs.length := by omega
        simp only [hx, hc, ↓reduceIte, Nat.add_sub_cancel, and_self]
      · have hc : ¬ (o ≤ x + o ∧ x + o < o + vs.length) := by omega
        simp only [hx, hc, ↓reduceIte]
    have hda : DaAg (fun x => x ∈ needZero fd.nparams fd.body) (List.range fd.nparams) vw
        { v with loc := Locals.init vs } := by
      refine ⟨?_, fun x hx => ?_⟩
      · show (sz.setLocs _ vs).mem = v.mem
        rw [St.setLocs_mem, hz2, h.mem]
      · show sp.loc (x + o) = Locals.init vs x
        rw [hsp x]
        simp only [Locals.init]
        by_cases hxl : x < vs.length
        · simp [hxl]
        · rcases hx with hx | hx
          · exact absurd (hvl ▸ List.mem_range.mp hx) hxl
          · simp only [hxl, ↓reduceIte, hz4 x hx]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hxl)]; rfl
    have hK := shift_exec (p := p) (p' := p') (o := o) (B := Stmt.vb fd.body) (c := sp.loc) n
    have H := conv_step (p := p) (p' := p') (xs := xs) hK hxs fd.body en b hbody (Nat.le_refl _) vw sp
      ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    have hR : ∀ x ∈ (Stmt.da fd.body (some (List.range fd.nparams)) []).2, x ∈ needZero fd.nparams fd.body :=
      fun x hx => hx
    change ConvPost p' (exec p' n) o (Stmt.vb fd.body) sp.loc xs en _ ((exec p (n + 1) fd.body).run vw) at H
    show Ref _ ((step p' (exec p' n) b).run sp) _
    -- the caller's locals below `o` are untouched
    have hlow : ∀ y < o, sp.loc y = v.loc y := fun y hy => by
      show (sz.setLocs _ vs).loc y = _
      rw [St.setLocs_low _ _ _ y (by
        simp only [List.mem_map, List.mem_range, not_exists, not_and]
        intro i _ e; exact low_ne (x := i + 0) hy e.symm), hz3 y fun x _ => low_ne hy, ← h.loc y hy]
    have fin : ∀ (r : Sig) (v1 s1' t2 : St), AR o (Stmt.vb fd.body) sp.loc v1 s1' → v1.mem = t2.mem →
        CR o (({ t2 with loc := v.loc } : St).setLocs xs r.retVal) (s1'.setLocs xs r.retVal) := by
      intro r v1 s1' t2 hA hm
      refine ⟨by rw [St.setLocs_mem, St.setLocs_mem, ← hm, hA.mem], ?_⟩
      exact St.setLocs_agree _ _ xs r.retVal fun y hy => by
        show v.loc y = s1'.loc y
        rw [hA.low y hy, hlow y hy]
    generalize hr : (exec p (n + 1) fd.body).run vw = r at H
    rcases r with e | ⟨sig, v1⟩
    · rw [exec_da_error hR hda hr]
      rw [H]; exact Ref.err e
    · obtain ⟨t2, ht2, hmem⟩ := exec_da_ok hR hda hr
      rw [ht2]
      dsimp only
      cases sig with
      | normal =>
        obtain ⟨s1', hA, e1⟩ := H
        rw [e1, retAssign_run p' (exec p' n) (v := v1) xs [] en s1' (by simpa using hen) hxs hA.mem
          (fun z hz => by simp [Exprs.vb] at hz)]
        exact Ref.ok (fin .normal v1 s1' t2 hA hmem)
      | brk =>
        obtain ⟨s1', hA, e1⟩ := H
        rw [e1]
        exact Ref.ok (fin .brk v1 s1' t2 hA hmem)
      | ret ws =>
        obtain ⟨s1', hA, e1⟩ := H
        rw [e1]
        exact Ref.ok (fin (.ret ws) v1 s1' t2 hA hmem)

end L.Compiler
