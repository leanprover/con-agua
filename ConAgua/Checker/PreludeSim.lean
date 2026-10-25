import ConAgua.Checker.Prelude
import ConAgua.L.FuelMono
import ConAgua.L.Blocks

/-!
# The prelude's copies of the frontend are the frontend on the prelude's bytes (lane `pipeline`)

`builtin_prelude` runs `pre_front_run`, the frontend with every function that reads the input
copied by `preFn` (`Checker/Prelude.lean`): `ld8 0 i` becomes `ldc preludeBytes i`, `len8 0` the
constant `preludeLenW`. **The simulation**: a returning run of a copy `pre_f` from state `s` is a
returning run of the original `f` from `s` with byte array `0` replaced by the prelude's bytes
(`St.setIn`), with the same results, ending in the copy's final state with byte array `0`
replaced the same way. So every spec of `f` is a spec of `pre_f` (`preSim_triple`).

The program's shape (`PreSimProg p t S`): every copied function `f` (its name in the tree `t`)
has its copy at `"pre_" ++ f`, stores no byte into array `0`, and calls only copied functions
(renamed by `preName`) or shared ones (`S`); a shared function reads and writes no byte of array
`0` and calls only shared functions.
-/

namespace L.Checker

open L L.Compiler
open Std.WP
open scoped Lean.Order

/-- Byte array `0` replaced by `x`. -/
def _root_.L.Mem.setIn (m : Mem) (x : Array UInt8) : Mem := { m with bytes := m.bytes.set! 0 x }

/-- Byte array `0` of the state's memory replaced by `x`. -/
def _root_.L.St.setIn (s : St) (x : Array UInt8) : St := { s with mem := s.mem.setIn x }

/-- The prelude's bytes, as the input array. -/
def preIn : Array UInt8 := preludeBytes.toArray

/-- A byte source other than byte array `0`. -/
def _root_.L.BSrc.noIn : BSrc → Bool
  | .arr a => a != 0
  | .rom _ => true

/-- No access to byte array `0`. -/
def _root_.L.Expr.noIn : Expr → Bool
  | .ld8 a i => a != 0 && i.noIn
  | .len8 a => a != 0
  | .ld64 _ i | .ldc _ i => i.noIn
  | .bin _ a b | .cmpw _ a b => a.noIn && b.noIn
  | .ld64t _ t i => t.noIn && i.noIn
  | .len64t _ t => t.noIn
  | .ld8x8 b i => b.noIn && i.noIn
  | _ => true

def _root_.L.WArr.noIn : WArr → Bool
  | .plain _ => true
  | .tier _ t => t.noIn

def _root_.L.Cond.noIn : Cond → Bool
  | .cmp _ a b => a.noIn && b.noIn
  | .and p q | .or p q => p.noIn && q.noIn
  | .not p => p.noIn

/-- No access to byte array `0` (no read, no store). -/
def _root_.L.Stmt.noIn : Stmt → Bool
  | .set _ e | .gset _ e => e.noIn
  | .st8 a i e => a != 0 && i.noIn && e.noIn
  | .st64 _ i e => i.noIn && e.noIn
  | .seq s t => s.noIn && t.noIn
  | .ite c s t => c.noIn && s.noIn && t.noIn
  | .while c s => c.noIn && s.noIn
  | .ret es | .call _ _ es => es.all Expr.noIn
  | .st64t _ t i e => t.noIn && i.noIn && e.noIn
  | .copy64 d di s si n => d.noIn && di.noIn && s.noIn && si.noIn && n.noIn
  | .copy8w d di s si n => d.noIn && di.noIn && s.noIn && si.noIn && n.noIn
  | .scan8 _ s i e _ => s.noIn && i.noIn && e.noIn
  | _ => true

/-- No store into byte array `0`. -/
def _root_.L.Stmt.noSt8In : Stmt → Bool
  | .st8 a _ _ => a != 0
  | .seq s t => s.noSt8In && t.noSt8In
  | .ite _ s t => s.noSt8In && t.noSt8In
  | .while _ s => s.noSt8In
  | _ => true

/-- Every call of the statement is to a name satisfying `P`. -/
def _root_.L.Stmt.callsIn (P : FnName → Bool) : Stmt → Bool
  | .seq s t => s.callsIn P && t.callsIn P
  | .ite _ s t => s.callsIn P && t.callsIn P
  | .while _ s => s.callsIn P
  | .call _ f _ => P f
  | _ => true

/-- `f` is copied (its name code is in the tree). -/
def isCopied (t : NTree) (f : FnName) : Bool := (t.find (nameCode f)).isSome

/-- **The program's shape for the simulation**: the copies of the functions in `t`, and the
shared functions `S` they call. -/
structure PreSimProg (p : Prog) (t : NTree) (S : FnName → Bool) : Prop where
  defined : ∀ f, isCopied t f = true → (p.lookup f).isSome = true
  copy : ∀ f fd, isCopied t f = true → p.lookup f = some fd →
    p.lookup ("pre_" ++ f) = some (preFn t fd) ∧ fd.body.noSt8In = true ∧
      fd.body.callsIn (fun g => isCopied t g || S g) = true
  shared : ∀ f fd, S f = true → p.lookup f = some fd →
    isCopied t f = false ∧ fd.body.noIn = true ∧ fd.body.callsIn S = true

/-! ## The input renaming on memory and states -/

@[simp] theorem _root_.L.St.setIn_mem (s : St) (x : Array UInt8) : (s.setIn x).mem = s.mem.setIn x := rfl
@[simp] theorem _root_.L.St.setIn_loc (s : St) (x : Array UInt8) : (s.setIn x).loc = s.loc := rfl

@[simp] theorem _root_.L.Mem.setIn_size (m : Mem) (x : Array UInt8) :
    (m.setIn x).bytes.size = m.bytes.size := by
  simp [Mem.setIn]

theorem _root_.L.Mem.arr8_setIn_ne {m : Mem} {x : Array UInt8} {a : ArrId} (ha : a ≠ 0) :
    (m.setIn x).arr8 a = m.arr8 a := by
  simp [Mem.setIn, Mem.arr8, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne, Ne.symm ha]

theorem _root_.L.Mem.arr8_setIn_zero {m : Mem} {x : Array UInt8} (h : 0 < m.bytes.size) :
    (m.setIn x).arr8 0 = x := by
  simp [Mem.setIn, Mem.arr8, Array.getD_eq_getD_getElem?, h]

theorem _root_.L.Mem.set8_setIn {m : Mem} {x : Array UInt8} {a : ArrId} (ha : a ≠ 0) (i v : Word) :
    (m.set8 a i v).setIn x = (m.setIn x).set8 a i v := by
  unfold Mem.set8
  rw [Mem.arr8_setIn_ne ha]
  simp only [Mem.setIn, Array.set!]
  rw [Array.setIfInBounds_comm _ _ (Ne.symm ha)]

theorem _root_.L.Mem.arr8_set8_ne {m : Mem} {a b : ArrId} (ha : a ≠ b) (i v : Word) :
    (m.set8 a i v).arr8 b = m.arr8 b := by
  simp [Mem.set8, Mem.arr8, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne, ha]

@[simp] theorem _root_.L.Mem.set8_size (m : Mem) (a : ArrId) (i v : Word) :
    (m.set8 a i v).bytes.size = m.bytes.size := by
  simp [Mem.set8]

@[simp] theorem _root_.L.Mem.arr64_setIn (m : Mem) (x : Array UInt8) (a : ArrId) :
    (m.setIn x).arr64 a = m.arr64 a := rfl

theorem _root_.L.Mem.copy64_setIn (m : Mem) (x : Array UInt8) (d : ArrId) (di : Word) (s : ArrId)
    (si : Word) (n : Nat) : (m.copy64 d di s si n).setIn x = (m.setIn x).copy64 d di s si n := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy64_succ, ih]; rfl

theorem _root_.L.Mem.copy8w_setIn (m : Mem) (x : Array UInt8) (d : ArrId) (di : Word) (b : Array UInt8)
    (si : Word) (n : Nat) : (m.copy8w d di b si n).setIn x = (m.setIn x).copy8w d di b si n := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy8w_succ, ih]; rfl

theorem _root_.L.St.setLocs_setIn (s : St) (x : Array UInt8) (xs : List Var) (vs : List Word) :
    (s.setIn x).setLocs xs vs = (s.setLocs xs vs).setIn x := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons y ys ih => exact ih (s.setLoc y (vs.headD 0)) vs.tail

theorem _root_.L.St.setLocs_mem (s : St) (xs : List Var) (vs : List Word) :
    (s.setLocs xs vs).mem = s.mem := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons y ys ih => exact ih (s.setLoc y (vs.headD 0)) vs.tail

/-- The copy's run keeps the input array and the number of byte arrays. -/
def Keep (s s1 : St) : Prop := s1.mem.arr8 0 = s.mem.arr8 0 ∧ s1.mem.bytes.size = s.mem.bytes.size

theorem Keep.refl (s : St) : Keep s s := ⟨rfl, rfl⟩

theorem Keep.of_mem {s s1 : St} (h : s1.mem = s.mem) : Keep s s1 := by
  unfold Keep; rw [h]; exact ⟨rfl, rfl⟩

theorem Keep.trans {s s1 s2 : St} (h1 : Keep s s1) (h2 : Keep s1 s2) : Keep s s2 :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem Keep.pos {s s1 : St} (h : Keep s s1) (h0 : 0 < s.mem.bytes.size) : 0 < s1.mem.bytes.size :=
  h.2 ▸ h0

theorem pure_run_ok {α : Type} {a b : α} {s s1 : St} (h : (pure a : M α).run s = .ok (b, s1)) :
    a = b ∧ s = s1 := by
  cases h; exact ⟨rfl, rfl⟩

theorem bind_sim {α β : Type} {x : M α} {g : α → M β} {s s' : St} {a : α} {r : β × St} {P : Prop}
    (hx : x.run s = .ok (a, s')) (H : (g a).run s' = .ok r ∧ P) : (x >>= g).run s = .ok r ∧ P :=
  ⟨run_bind_of hx H.1, H.2⟩

theorem keep_sim {X : Prop} {s s1 s2 : St} (hK : Keep s s1) (H : X ∧ Keep s1 s2) : X ∧ Keep s s2 :=
  ⟨H.1, hK.trans H.2⟩

/-! ## Expressions and conditions -/

/-- `ce` on `s` evaluates as `oe` on `s` with the input replaced. -/
def ERel (ce oe : Expr) : Prop := ∀ (s : St) (v : Word) (s1 : St), 0 < s.mem.bytes.size →
  (evalE ce).run s = .ok (v, s1) → s = s1 ∧ (evalE oe).run (s.setIn preIn) = .ok (v, s.setIn preIn)

def CRel (cc co : Cond) : Prop := ∀ (s : St) (v : Bool) (s1 : St), 0 < s.mem.bytes.size →
  (evalC cc).run s = .ok (v, s1) → s = s1 ∧ (evalC co).run (s.setIn preIn) = .ok (v, s.setIn preIn)

def ARel (ces oes : List Expr) : Prop := ∀ (s : St) (v : List Word) (s1 : St),
  0 < s.mem.bytes.size → (evalArgs ces).run s = .ok (v, s1) →
    s = s1 ∧ (evalArgs oes).run (s.setIn preIn) = .ok (v, s.setIn preIn)

theorem ERel.bin {op : BinOp} {ca cb oa ob : Expr} (ha : ERel ca oa) (hb : ERel cb ob) :
    ERel (.bin op ca cb) (.bin op oa ob) := by
  intro s v s1 h0 h
  simp only [evalE] at h ⊢
  obtain ⟨x, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := ha s x s2 h0 h1
  obtain ⟨y, s3, h3, h4⟩ := run_bind_ok h2
  obtain ⟨rfl, h3'⟩ := hb s y s3 h0 h3
  simp only [StateT.run_pure] at h4
  obtain ⟨rfl, rfl⟩ := h4
  exact ⟨rfl, run_bind_of h1' (run_bind_of h3' rfl)⟩

theorem ERel.cmpw {c : Cmp} {ca cb oa ob : Expr} (ha : ERel ca oa) (hb : ERel cb ob) :
    ERel (.cmpw c ca cb) (.cmpw c oa ob) := by
  intro s v s1 h0 h
  simp only [evalE] at h ⊢
  obtain ⟨x, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := ha s x s2 h0 h1
  obtain ⟨y, s3, h3, h4⟩ := run_bind_ok h2
  obtain ⟨rfl, h3'⟩ := hb s y s3 h0 h3
  simp only [StateT.run_pure] at h4
  obtain ⟨rfl, rfl⟩ := h4
  exact ⟨rfl, run_bind_of h1' (run_bind_of h3' rfl)⟩

/-- An index expression followed by a stateless read that agrees on the two states. -/
theorem ERel.load {ci oi : Expr} (hi : ERel ci oi) {fc fo : Word → M Word}
    (hf : ∀ (s : St) (j v : Word) (s1 : St), 0 < s.mem.bytes.size → (fc j).run s = .ok (v, s1) →
      s = s1 ∧ (fo j).run (s.setIn preIn) = .ok (v, s.setIn preIn))
    {ec eo : Expr} (hc : ∀ s, (evalE ec).run s = (evalE ci >>= fc).run s)
    (ho : ∀ s, (evalE eo).run s = (evalE oi >>= fo).run s) : ERel ec eo := by
  intro s v s1 h0 h
  rw [hc] at h; rw [ho]
  obtain ⟨j, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := hi s j s2 h0 h1
  obtain ⟨rfl, h2'⟩ := hf s j v s1 h0 h2
  exact ⟨rfl, run_bind_of h1' h2'⟩

theorem ld8_run (a : ArrId) (j : Word) (s : St) :
    (ld8 a j).run s = if h : j.toNat < (s.mem.arr8 a).size
      then .ok ((s.mem.arr8 a)[j.toNat].toUInt64, s) else .error .oob := by
  unfold ld8
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> rfl

theorem ld64_run (a : ArrId) (j : Word) (s : St) :
    (ld64 a j).run s = if h : j.toNat < (s.mem.arr64 a).size
      then .ok ((s.mem.arr64 a)[j.toNat], s) else .error .oob := by
  unfold ld64
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> rfl

theorem ldc_run (d : List UInt8) (j : Word) (s : St) :
    (ldc d j).run s = if h : j.toNat < d.length then .ok (d[j.toNat].toUInt64, s) else .error .oob := by
  unfold ldc
  split <;> rfl

theorem erel_ld8_ne {a : ArrId} (ha : a ≠ 0) {ci oi : Expr} (hi : ERel ci oi) :
    ERel (.ld8 a ci) (.ld8 a oi) := by
  refine ERel.load hi (fc := ld8 a) (fo := ld8 a) ?_ (fun _ => rfl) (fun _ => rfl)
  intro s j v s1 _ h
  rw [ld8_run] at h ⊢
  simp only [St.setIn_mem, Mem.arr8_setIn_ne ha]
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp_all
  · cases h

theorem erel_ld8_zero {ci oi : Expr} (hi : ERel ci oi) :
    ERel (.ldc preludeBytes ci) (.ld8 0 oi) := by
  refine ERel.load hi (fc := ldc preludeBytes) (fo := ld8 0) ?_ (fun _ => rfl) (fun _ => rfl)
  intro s j v s1 h0 h
  rw [ldc_run] at h; rw [ld8_run]
  simp only [St.setIn_mem, Mem.arr8_setIn_zero h0, preIn, List.size_toArray, List.getElem_toArray]
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp_all
  · cases h

theorem erel_ld64 {a : ArrId} {ci oi : Expr} (hi : ERel ci oi) : ERel (.ld64 a ci) (.ld64 a oi) := by
  refine ERel.load hi (fc := ld64 a) (fo := ld64 a) ?_ (fun _ => rfl) (fun _ => rfl)
  intro s j v s1 _ h
  rw [ld64_run] at h ⊢
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, dite_eq_left ‹_›⟩
  · cases h

theorem erel_ldc {d : List UInt8} {ci oi : Expr} (hi : ERel ci oi) : ERel (.ldc d ci) (.ldc d oi) := by
  refine ERel.load hi (fc := ldc d) (fo := ldc d) ?_ (fun _ => rfl) (fun _ => rfl)
  intro s j v s1 _ h
  rw [ldc_run] at h ⊢
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp_all
  · cases h

/-- A stateless leaf expression whose value on the renamed state is the copy's. -/
theorem erel_leaf {ec eo : Expr} (fc fo : St → Word) (hc : ∀ s, (evalE ec).run s = .ok (fc s, s))
    (ho : ∀ s, (evalE eo).run s = .ok (fo s, s))
    (hf : ∀ s, 0 < s.mem.bytes.size → fo (s.setIn preIn) = fc s) : ERel ec eo := by
  intro s v s1 h0 h
  rw [hc] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, by rw [ho, hf s h0]⟩

theorem erel_ld64t {a : ArrId} {ct ot ci oi : Expr} (ht : ERel ct ot) (hi : ERel ci oi) :
    ERel (.ld64t a ct ci) (.ld64t a ot oi) := by
  intro s v s1 h0 h
  simp only [evalE] at h ⊢
  obtain ⟨u, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := ht s u s2 h0 h1
  have := erel_ld64 (a := tierA a u) hi s v s1 h0 h2
  exact ⟨this.1, run_bind_of h1' this.2⟩

theorem erel_len64t {a : ArrId} {ct ot : Expr} (ht : ERel ct ot) :
    ERel (.len64t a ct) (.len64t a ot) := by
  intro s v s1 h0 h
  simp only [evalE] at h ⊢
  obtain ⟨u, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := ht s u s2 h0 h1
  have := erel_leaf (ec := .len64 (tierA a u)) (eo := .len64 (tierA a u))
    (fun s => s.mem.len64 (tierA a u)) (fun s => s.mem.len64 (tierA a u)) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) s v s1 h0 h2
  exact ⟨this.1, run_bind_of h1' this.2⟩

/-- A byte source of the copy reads, on a state, what the original's reads on the renamed state. -/
def BRel (cb ob : BSrc) : Prop := ∀ s : St, 0 < s.mem.bytes.size → (s.setIn preIn).mem.src8 ob = s.mem.src8 cb

theorem brel_preB : ∀ b, BRel (preB b) b
  | .arr a, s, h0 => by
    by_cases ha : a = 0
    · subst ha; simp [preB, Mem.src8, Mem.arr8_setIn_zero h0, preIn]
    · simp [preB, ha, Mem.src8, Mem.arr8_setIn_ne ha]
  | .rom d, _, _ => rfl

theorem brel_noIn : ∀ b, b.noIn = true → BRel b b
  | .arr a, h, s, _ => by
    simp only [BSrc.noIn, bne_iff_ne] at h
    simp [Mem.src8, Mem.arr8_setIn_ne h]
  | .rom d, _, _, _ => rfl

theorem ld8x8_run (b : BSrc) (j : Word) (s : St) :
    (ld8x8 b j).run s = if j.toNat + 8 ≤ (s.mem.src8 b).size
      then .ok (le64 (s.mem.src8 b) j.toNat, s) else .error .oob := by
  unfold ld8x8
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> rfl

theorem erel_ld8x8 {cb ob : BSrc} (hb : BRel cb ob) {ci oi : Expr} (hi : ERel ci oi) :
    ERel (.ld8x8 cb ci) (.ld8x8 ob oi) := by
  refine ERel.load hi (fc := ld8x8 cb) (fo := ld8x8 ob) ?_ (fun _ => rfl) (fun _ => rfl)
  intro s j v s1 h0 h
  rw [ld8x8_run] at h ⊢
  rw [hb s h0]
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp_all
  · cases h

theorem erel_preE : ∀ e, ERel (preE e) e
  | .const w => erel_leaf (fun _ => w) (fun _ => w) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  | .var x => erel_leaf (fun s => s.loc x) (fun s => s.loc x) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  | .glob g => erel_leaf (fun s => s.mem.glob g) (fun s => s.mem.glob g) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  | .len64 a => erel_leaf (fun s => s.mem.len64 a) (fun s => s.mem.len64 a) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  | .bin op a b => ERel.bin (erel_preE a) (erel_preE b)
  | .cmpw c a b => ERel.cmpw (erel_preE a) (erel_preE b)
  | .ld64 a i => erel_ld64 (erel_preE i)
  | .ldc d i => erel_ldc (erel_preE i)
  | .ld64t a t i => erel_ld64t (erel_preE t) (erel_preE i)
  | .len64t a t => erel_len64t (erel_preE t)
  | .ld8x8 b i => erel_ld8x8 (brel_preB b) (erel_preE i)
  | .ld8 a i => by
    by_cases ha : a = 0
    · subst ha; simp only [preE, ite_true]; exact erel_ld8_zero (erel_preE i)
    · simp only [preE, ha, ite_false]; exact erel_ld8_ne ha (erel_preE i)
  | .len8 a => by
    by_cases ha : a = 0
    · subst ha; simp only [preE, ite_true]
      refine erel_leaf (fun _ => preludeLenW) (fun s => s.mem.len8 0) (fun _ => rfl) (fun _ => rfl)
        (fun s h0 => ?_)
      simp only [Mem.len8, St.setIn_mem, Mem.arr8_setIn_zero h0, preIn, List.size_toArray, preludeLenW]
    · simp only [preE, ha, ite_false]
      refine erel_leaf (fun s => s.mem.len8 a) (fun s => s.mem.len8 a) (fun _ => rfl) (fun _ => rfl) (fun s _ => ?_)
      simp only [Mem.len8, St.setIn_mem, Mem.arr8_setIn_ne ha]

theorem erel_noIn : ∀ e, e.noIn = true → ERel e e
  | .const w, _ => erel_leaf (fun _ => w) (fun _ => w) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  | .var x, _ => erel_leaf (fun s => s.loc x) (fun s => s.loc x) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  | .glob g, _ => erel_leaf (fun s => s.mem.glob g) (fun s => s.mem.glob g) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  | .len64 a, _ => erel_leaf (fun s => s.mem.len64 a) (fun s => s.mem.len64 a) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  | .bin op a b, h => by
    simp only [Expr.noIn, Bool.and_eq_true] at h
    exact ERel.bin (erel_noIn a h.1) (erel_noIn b h.2)
  | .cmpw c a b, h => by
    simp only [Expr.noIn, Bool.and_eq_true] at h
    exact ERel.cmpw (erel_noIn a h.1) (erel_noIn b h.2)
  | .ld64 a i, h => erel_ld64 (erel_noIn i h)
  | .ldc d i, h => erel_ldc (erel_noIn i h)
  | .ld64t a t i, h => by
    simp only [Expr.noIn, Bool.and_eq_true] at h
    exact erel_ld64t (erel_noIn t h.1) (erel_noIn i h.2)
  | .len64t a t, h => erel_len64t (erel_noIn t h)
  | .ld8x8 b i, h => by
    simp only [Expr.noIn, Bool.and_eq_true] at h
    exact erel_ld8x8 (brel_noIn b h.1) (erel_noIn i h.2)
  | .ld8 a i, h => by
    simp only [Expr.noIn, Bool.and_eq_true, bne_iff_ne] at h
    exact erel_ld8_ne h.1 (erel_noIn i h.2)
  | .len8 a, h => by
    simp only [Expr.noIn, bne_iff_ne] at h
    refine erel_leaf (fun s => s.mem.len8 a) (fun s => s.mem.len8 a) (fun _ => rfl) (fun _ => rfl) (fun s _ => ?_)
    simp only [Mem.len8, St.setIn_mem, Mem.arr8_setIn_ne h]

/-- A block operand of the copy names, on a state, the original's array on the renamed state. -/
def WRel (cw ow : WArr) : Prop := ∀ (s : St) (a : ArrId) (s1 : St), 0 < s.mem.bytes.size →
  (warr cw).run s = .ok (a, s1) → s = s1 ∧ (warr ow).run (s.setIn preIn) = .ok (a, s.setIn preIn)

theorem wrel_of {ct ot : Expr} (ht : ERel ct ot) (a : ArrId) : WRel (.tier a ct) (.tier a ot) := by
  intro s b s1 h0 h
  simp only [warr] at h ⊢
  obtain ⟨u, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := ht s u s2 h0 h1
  obtain ⟨rfl, rfl⟩ := pure_run_ok h2
  exact ⟨rfl, run_bind_of h1' rfl⟩

theorem wrel_plain (a : ArrId) : WRel (.plain a) (.plain a) := by
  intro s b s1 _ h
  obtain ⟨rfl, rfl⟩ := pure_run_ok h
  exact ⟨rfl, rfl⟩

theorem wrel_preW : ∀ w, WRel (preW w) w
  | .plain a => wrel_plain a
  | .tier a t => wrel_of (erel_preE t) a

theorem wrel_noIn : ∀ w, w.noIn = true → WRel w w
  | .plain a, _ => wrel_plain a
  | .tier a t, h => wrel_of (erel_noIn t h) a

theorem CRel.cmp {c : Cmp} {ca cb oa ob : Expr} (ha : ERel ca oa) (hb : ERel cb ob) :
    CRel (.cmp c ca cb) (.cmp c oa ob) := by
  intro s v s1 h0 h
  simp only [evalC] at h ⊢
  obtain ⟨x, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := ha s x s2 h0 h1
  obtain ⟨y, s3, h3, h4⟩ := run_bind_ok h2
  obtain ⟨rfl, h3'⟩ := hb s y s3 h0 h3
  simp only [StateT.run_pure] at h4
  obtain ⟨rfl, rfl⟩ := h4
  exact ⟨rfl, run_bind_of h1' (run_bind_of h3' rfl)⟩

theorem CRel.and {cp cq op oq : Cond} (hp : CRel cp op) (hq : CRel cq oq) :
    CRel (.and cp cq) (.and op oq) := by
  intro s v s1 h0 h
  simp only [evalC] at h ⊢
  obtain ⟨x, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := hp s x s2 h0 h1
  cases x
  · obtain ⟨rfl, rfl⟩ := pure_run_ok h2
    exact ⟨rfl, run_bind_of h1' rfl⟩
  · obtain ⟨rfl, h'⟩ := hq s v s1 h0 h2
    exact ⟨rfl, run_bind_of h1' h'⟩

theorem CRel.or {cp cq op oq : Cond} (hp : CRel cp op) (hq : CRel cq oq) :
    CRel (.or cp cq) (.or op oq) := by
  intro s v s1 h0 h
  simp only [evalC] at h ⊢
  obtain ⟨x, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := hp s x s2 h0 h1
  cases x
  · obtain ⟨rfl, h'⟩ := hq s v s1 h0 h2
    exact ⟨rfl, run_bind_of h1' h'⟩
  · obtain ⟨rfl, rfl⟩ := pure_run_ok h2
    exact ⟨rfl, run_bind_of h1' rfl⟩

theorem CRel.not {cp op : Cond} (hp : CRel cp op) : CRel (.not cp) (.not op) := by
  intro s v s1 h0 h
  simp only [evalC] at h ⊢
  obtain ⟨x, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := hp s x s2 h0 h1
  simp only [StateT.run_pure] at h2
  obtain ⟨rfl, rfl⟩ := h2
  exact ⟨rfl, run_bind_of h1' rfl⟩

theorem crel_preC : ∀ c, CRel (preC c) c
  | .cmp _ a b => CRel.cmp (erel_preE a) (erel_preE b)
  | .and p q => CRel.and (crel_preC p) (crel_preC q)
  | .or p q => CRel.or (crel_preC p) (crel_preC q)
  | .not p => CRel.not (crel_preC p)

theorem crel_noIn : ∀ c, c.noIn = true → CRel c c
  | .cmp c a b, h => by
    simp only [Cond.noIn, Bool.and_eq_true] at h
    exact CRel.cmp (erel_noIn a h.1) (erel_noIn b h.2)
  | .and p q, h => by
    simp only [Cond.noIn, Bool.and_eq_true] at h
    exact CRel.and (crel_noIn p h.1) (crel_noIn q h.2)
  | .or p q, h => by
    simp only [Cond.noIn, Bool.and_eq_true] at h
    exact CRel.or (crel_noIn p h.1) (crel_noIn q h.2)
  | .not p, h => CRel.not (crel_noIn p h)

theorem ARel.nil : ARel [] [] := by
  intro s v s1 _ h
  simp only [evalArgs, StateT.run_pure] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem ARel.cons {ce oe : Expr} {ces oes : List Expr} (he : ERel ce oe) (hs : ARel ces oes) :
    ARel (ce :: ces) (oe :: oes) := by
  intro s v s1 h0 h
  simp only [evalArgs] at h ⊢
  obtain ⟨x, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨rfl, h1'⟩ := he s x s2 h0 h1
  obtain ⟨y, s3, h3, h4⟩ := run_bind_ok h2
  obtain ⟨rfl, h3'⟩ := hs s y s3 h0 h3
  simp only [StateT.run_pure] at h4
  obtain ⟨rfl, rfl⟩ := h4
  exact ⟨rfl, run_bind_of h1' (run_bind_of h3' rfl)⟩

theorem arel_preE : ∀ es, ARel (es.map preE) es
  | [] => ARel.nil
  | e :: es => ARel.cons (erel_preE e) (arel_preE es)

theorem arel_noIn : ∀ es, es.all Expr.noIn = true → ARel es es
  | [], _ => ARel.nil
  | e :: es, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ARel.cons (erel_noIn e h.1) (arel_noIn es h.2)

/-! ## Statements -/

/-- A copy statement `c` and the original `o` it simulates. -/
inductive Sim (t : NTree) (S : FnName → Bool) : Stmt → Stmt → Prop
  | skip : Sim t S .skip .skip
  | brk : Sim t S .brk .brk
  | abort (e : Expr) : Sim t S (.abort e) (.abort e)
  | set (x : Var) {ce oe : Expr} : ERel ce oe → Sim t S (.set x ce) (.set x oe)
  | gset (g : GVar) {ce oe : Expr} : ERel ce oe → Sim t S (.gset g ce) (.gset g oe)
  | st8 {a : ArrId} {ci oi ce oe : Expr} : a ≠ 0 → ERel ci oi → ERel ce oe →
      Sim t S (.st8 a ci ce) (.st8 a oi oe)
  | st64 (a : ArrId) {ci oi ce oe : Expr} : ERel ci oi → ERel ce oe →
      Sim t S (.st64 a ci ce) (.st64 a oi oe)
  | st64t (a : ArrId) {ct ot ci oi ce oe : Expr} : ERel ct ot → ERel ci oi → ERel ce oe →
      Sim t S (.st64t a ct ci ce) (.st64t a ot oi oe)
  | copy64 {cd od cs os : WArr} {cdi odi csi osi cn on : Expr} : WRel cd od → ERel cdi odi →
      WRel cs os → ERel csi osi → ERel cn on →
      Sim t S (.copy64 cd cdi cs csi cn) (.copy64 od odi os osi on)
  | copy8w {cd od : WArr} {cs os : BSrc} {cdi odi csi osi cn on : Expr} : WRel cd od → ERel cdi odi →
      BRel cs os → ERel csi osi → ERel cn on →
      Sim t S (.copy8w cd cdi cs csi cn) (.copy8w od odi os osi on)
  | scan8 (x : Var) {cs os : BSrc} {ci oi ce oe : Expr} (c : List UInt8) : BRel cs os → ERel ci oi →
      ERel ce oe → Sim t S (.scan8 x cs ci ce c) (.scan8 x os oi oe c)
  | seq {c₁ c₂ o₁ o₂ : Stmt} : Sim t S c₁ o₁ → Sim t S c₂ o₂ → Sim t S (.seq c₁ c₂) (.seq o₁ o₂)
  | ite {cc co : Cond} {c₁ c₂ o₁ o₂ : Stmt} : CRel cc co → Sim t S c₁ o₁ → Sim t S c₂ o₂ →
      Sim t S (.ite cc c₁ c₂) (.ite co o₁ o₂)
  | while {cc co : Cond} {c o : Stmt} : CRel cc co → Sim t S c o →
      Sim t S (.while cc c) (.while co o)
  | ret {ces oes : List Expr} : ARel ces oes → Sim t S (.ret ces) (.ret oes)
  | callC (xs : List Var) {g : FnName} {ca oa : List Expr} : isCopied t g = true → ARel ca oa →
      Sim t S (.call xs ("pre_" ++ g) ca) (.call xs g oa)
  | callS (xs : List Var) {g : FnName} {ca oa : List Expr} : S g = true → ARel ca oa →
      Sim t S (.call xs g ca) (.call xs g oa)

theorem preName_copied {t : NTree} {g : FnName} (h : isCopied t g = true) :
    preName t g = "pre_" ++ g := by
  unfold isCopied at h; unfold preName
  cases hf : t.find (nameCode g) <;> simp_all

theorem preName_shared {t : NTree} {g : FnName} (h : isCopied t g = false) : preName t g = g := by
  unfold isCopied at h; unfold preName
  cases hf : t.find (nameCode g) <;> simp_all

theorem sim_preS {t : NTree} {S : FnName → Bool} : ∀ s : Stmt, s.noSt8In = true →
    s.callsIn (fun g => isCopied t g || S g) = true → Sim t S (preS t s) s
  | .skip, _, _ => .skip
  | .brk, _, _ => .brk
  | .abort e, _, _ => .abort e
  | .set x e, _, _ => .set x (erel_preE e)
  | .gset g e, _, _ => .gset g (erel_preE e)
  | .st8 a i e, h, _ => by
    simp only [Stmt.noSt8In, bne_iff_ne] at h
    exact .st8 h (erel_preE i) (erel_preE e)
  | .st64 a i e, _, _ => .st64 a (erel_preE i) (erel_preE e)
  | .st64t a tt i e, _, _ => .st64t a (erel_preE tt) (erel_preE i) (erel_preE e)
  | .copy64 d di s si n, _, _ =>
    .copy64 (wrel_preW d) (erel_preE di) (wrel_preW s) (erel_preE si) (erel_preE n)
  | .copy8w d di s si n, _, _ =>
    .copy8w (wrel_preW d) (erel_preE di) (brel_preB s) (erel_preE si) (erel_preE n)
  | .scan8 x s i e c, _, _ => .scan8 x c (brel_preB s) (erel_preE i) (erel_preE e)
  | .ret es, _, _ => .ret (arel_preE es)
  | .seq s u, h, hc => by
    simp only [Stmt.noSt8In, Stmt.callsIn, Bool.and_eq_true] at h hc
    exact .seq (sim_preS s h.1 hc.1) (sim_preS u h.2 hc.2)
  | .ite c s u, h, hc => by
    simp only [Stmt.noSt8In, Stmt.callsIn, Bool.and_eq_true] at h hc
    exact .ite (crel_preC c) (sim_preS s h.1 hc.1) (sim_preS u h.2 hc.2)
  | .while c s, h, hc => by
    simp only [Stmt.noSt8In, Stmt.callsIn] at h hc
    exact .while (crel_preC c) (sim_preS s h hc)
  | .call xs g args, _, hc => by
    simp only [Stmt.callsIn, Bool.or_eq_true] at hc
    simp only [preS]
    cases hg : isCopied t g
    · rw [preName_shared hg]
      simp only [hg, Bool.false_eq_true, false_or] at hc
      exact .callS xs hc (arel_preE args)
    · rw [preName_copied hg]
      exact .callC xs hg (arel_preE args)

theorem sim_noIn {t : NTree} {S : FnName → Bool} : ∀ s : Stmt, s.noIn = true →
    s.callsIn S = true → Sim t S s s
  | .skip, _, _ => .skip
  | .brk, _, _ => .brk
  | .abort e, _, _ => .abort e
  | .set x e, h, _ => .set x (erel_noIn e h)
  | .gset g e, h, _ => .gset g (erel_noIn e h)
  | .st8 a i e, h, _ => by
    simp only [Stmt.noIn, Bool.and_eq_true, bne_iff_ne] at h
    exact .st8 h.1.1 (erel_noIn i h.1.2) (erel_noIn e h.2)
  | .st64 a i e, h, _ => by
    simp only [Stmt.noIn, Bool.and_eq_true] at h
    exact .st64 a (erel_noIn i h.1) (erel_noIn e h.2)
  | .st64t a tt i e, h, _ => by
    simp only [Stmt.noIn, Bool.and_eq_true] at h
    exact .st64t a (erel_noIn tt h.1.1) (erel_noIn i h.1.2) (erel_noIn e h.2)
  | .copy64 d di s si n, h, _ => by
    simp only [Stmt.noIn, Bool.and_eq_true] at h
    exact .copy64 (wrel_noIn d h.1.1.1.1) (erel_noIn di h.1.1.1.2) (wrel_noIn s h.1.1.2)
      (erel_noIn si h.1.2) (erel_noIn n h.2)
  | .copy8w d di s si n, h, _ => by
    simp only [Stmt.noIn, Bool.and_eq_true] at h
    exact .copy8w (wrel_noIn d h.1.1.1.1) (erel_noIn di h.1.1.1.2) (brel_noIn s h.1.1.2)
      (erel_noIn si h.1.2) (erel_noIn n h.2)
  | .scan8 x s i e c, h, _ => by
    simp only [Stmt.noIn, Bool.and_eq_true] at h
    exact .scan8 x c (brel_noIn s h.1.1) (erel_noIn i h.1.2) (erel_noIn e h.2)
  | .ret es, h, _ => .ret (arel_noIn es h)
  | .seq s u, h, hc => by
    simp only [Stmt.noIn, Stmt.callsIn, Bool.and_eq_true] at h hc
    exact .seq (sim_noIn s h.1 hc.1) (sim_noIn u h.2 hc.2)
  | .ite c s u, h, hc => by
    simp only [Stmt.noIn, Stmt.callsIn, Bool.and_eq_true] at h hc
    exact .ite (crel_noIn c h.1.1) (sim_noIn s h.1.2 hc.1) (sim_noIn u h.2 hc.2)
  | .while c s, h, hc => by
    simp only [Stmt.noIn, Stmt.callsIn, Bool.and_eq_true] at h hc
    exact .while (crel_noIn c h.1) (sim_noIn s h.2 hc)
  | .call xs g args, h, hc => .callS xs hc (arel_noIn args h)

/-! ## Runs -/

/-- `k` runs the copy `c` as the original `o`. -/
def KRel (k : Stmt → M Sig) (c o : Stmt) : Prop := ∀ (s : St) (r : Sig) (s1 : St),
  0 < s.mem.bytes.size → (k c).run s = .ok (r, s1) →
    (k o).run (s.setIn preIn) = .ok (r, s1.setIn preIn) ∧ Keep s s1

theorem lookupFn_ok {p : Prog} {f : FnName} {s : St} {fd : FunDecl} {s1 : St}
    (h : (lookupFn p f).run s = .ok (fd, s1)) : p.lookup f = some fd ∧ s = s1 := by
  unfold lookupFn at h
  cases hp : p.lookup f with
  | none => rw [hp] at h; cases h
  | some fd' =>
    rw [hp] at h
    simp only [StateT.run_pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem lookupFn_run {p : Prog} {f : FnName} {fd : FunDecl} (h : p.lookup f = some fd) (s : St) :
    (lookupFn p f).run s = .ok (fd, s) := by
  unfold lookupFn; rw [h]; rfl

theorem callFn_sim {k : Stmt → M Sig} {dc dd : FunDecl} (hk : KRel k dc.body dd.body)
    (vs : List Word) (s : St) (r : List Word) (s1 : St) (h0 : 0 < s.mem.bytes.size)
    (h : (callFn k dc vs).run s = .ok (r, s1)) :
    (callFn k dd vs).run (s.setIn preIn) = .ok (r, s1.setIn preIn) ∧ Keep s s1 := by
  unfold callFn at h ⊢
  obtain ⟨s2, s3, h3, h4⟩ := run_bind_ok h
  simp only [StateT.run_get] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨u, s4, h5, h6⟩ := run_bind_ok h4
  simp only [StateT.run_set] at h5
  obtain ⟨-, rfl⟩ := h5
  obtain ⟨rr, s5, h7, h8⟩ := run_bind_ok h6
  obtain ⟨u2, s6, h9, h10⟩ := run_bind_ok h8
  simp only [StateT.run_modify] at h9
  obtain ⟨-, rfl⟩ := h9
  simp only [StateT.run_pure] at h10
  obtain ⟨rfl, rfl⟩ := h10
  obtain ⟨h7', hK⟩ := hk { s with loc := Locals.init vs } rr s5 h0 h7
  refine ⟨?_, hK⟩
  refine run_bind_of (s' := s.setIn preIn) (a := s.setIn preIn) rfl ?_
  refine run_bind_of (a := ()) (s' := { s with loc := Locals.init vs }.setIn preIn) rfl ?_
  refine run_bind_of h7' ?_
  refine run_bind_of (a := ()) (s' := { s5 with loc := s.loc }.setIn preIn) rfl ?_
  rfl

/-- The runs of the copies and of the shared functions at fuel `n`. -/
def KSim (p : Prog) (t : NTree) (S : FnName → Bool) (n : Nat) : Prop :=
  ∀ c o, Sim t S c o → KRel (exec p n) c o

theorem invoke_sim_copy {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S)
    (n : Nat) (ih : KSim p t S n) (g : FnName) (hg : isCopied t g = true) (vs : List Word) (s : St)
    (r : List Word) (s1 : St) (h0 : 0 < s.mem.bytes.size)
    (h : (invoke p (exec p n) ("pre_" ++ g) vs).run s = .ok (r, s1)) :
    (invoke p (exec p n) g vs).run (s.setIn preIn) = .ok (r, s1.setIn preIn) ∧ Keep s s1 := by
  unfold invoke at h ⊢
  obtain ⟨fd', s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨hl', rfl⟩ := lookupFn_ok h1
  obtain ⟨fd, hl⟩ := Option.isSome_iff_exists.mp (hP.defined g hg)
  obtain ⟨hc, hst, hcl⟩ := hP.copy g fd hg hl
  rw [hc] at hl'; cases hl'
  obtain ⟨H, hK⟩ := callFn_sim (ih _ _ (sim_preS _ hst hcl)) vs s r s1 h0 h2
  exact ⟨run_bind_of (lookupFn_run hl _) H, hK⟩

theorem invoke_sim_shared {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S)
    (n : Nat) (ih : KSim p t S n) (g : FnName) (hg : S g = true) (vs : List Word) (s : St)
    (r : List Word) (s1 : St) (h0 : 0 < s.mem.bytes.size)
    (h : (invoke p (exec p n) g vs).run s = .ok (r, s1)) :
    (invoke p (exec p n) g vs).run (s.setIn preIn) = .ok (r, s1.setIn preIn) ∧ Keep s s1 := by
  unfold invoke at h ⊢
  obtain ⟨fd, s2, h1, h2⟩ := run_bind_ok h
  obtain ⟨hl, rfl⟩ := lookupFn_ok h1
  obtain ⟨-, hn, hcl⟩ := hP.shared g fd hg hl
  obtain ⟨H, hK⟩ := callFn_sim (ih _ _ (sim_noIn _ hn hcl)) vs s r s1 h0 h2
  exact ⟨run_bind_of (lookupFn_run hl _) H, hK⟩

theorem st8_run (a : ArrId) (j v : Word) (s : St) :
    (st8 a j v).run s = if j.toNat < (s.mem.arr8 a).size
      then .ok ((), { s with mem := s.mem.set8 a j v }) else .error .oob := by
  unfold st8
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> rfl

theorem st64_run (a : ArrId) (j v : Word) (s : St) :
    (st64 a j v).run s = if j.toNat < (s.mem.arr64 a).size
      then .ok ((), { s with mem := s.mem.set64 a j v }) else .error .oob := by
  unfold st64
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split <;> rfl

theorem step_sim {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S)
    (n : Nat) (ihn : KSim p t S n) {c o : Stmt} (hs : Sim t S c o) :
    KRel (step p (exec p n)) c o := by
  induction hs with
  | «skip» =>
    intro s r s1 _ h
    obtain ⟨rfl, rfl⟩ := pure_run_ok h
    exact ⟨rfl, Keep.refl _⟩
  | brk =>
    intro s r s1 _ h
    obtain ⟨rfl, rfl⟩ := pure_run_ok h
    exact ⟨rfl, Keep.refl _⟩
  | «abort» =>
    intro s r s1 _ h
    simp only [step] at h
    obtain ⟨v, s2, h1, h2⟩ := run_bind_ok h
    cases h2
  | set x he =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨v, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := he s v s2 h0 h1
    obtain ⟨u, s3, h3, h4⟩ := run_bind_ok h2
    simp only [setLoc, StateT.run_modify] at h3
    obtain ⟨-, rfl⟩ := h3
    obtain ⟨rfl, rfl⟩ := pure_run_ok h4
    exact ⟨run_bind_of h1' (run_bind_of (a := ()) (s' := (s.setLoc x v).setIn preIn) rfl rfl),
      Keep.of_mem rfl⟩
  | gset g he =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨v, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := he s v s2 h0 h1
    obtain ⟨u, s3, h3, h4⟩ := run_bind_ok h2
    simp only [setG, StateT.run_modify] at h3
    obtain ⟨-, rfl⟩ := h3
    obtain ⟨rfl, rfl⟩ := pure_run_ok h4
    exact ⟨run_bind_of h1' (run_bind_of (a := ()) (s' := (s.setG g v).setIn preIn) rfl rfl),
      ⟨rfl, rfl⟩⟩
  | st8 ha hi he =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨j, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := hi s j s2 h0 h1
    obtain ⟨v, s3, h3, h4⟩ := run_bind_ok h2
    obtain ⟨rfl, h3'⟩ := he s v s3 h0 h3
    obtain ⟨u, s4, h5, h6⟩ := run_bind_ok h4
    obtain ⟨rfl, rfl⟩ := pure_run_ok h6
    rw [st8_run] at h5
    split at h5
    · rename_i hlt
      simp only [Except.ok.injEq, Prod.mk.injEq] at h5
      obtain ⟨-, rfl⟩ := h5
      refine ⟨run_bind_of h1' (run_bind_of h3' (run_bind_of (a := ())
        (s' := ({ s with mem := s.mem.set8 _ j v } : St).setIn preIn) ?_ rfl)),
        Mem.arr8_set8_ne ha j v, Mem.set8_size _ _ _ _⟩
      rw [st8_run, ite_eq_left (by simpa [Mem.arr8_setIn_ne ha] using hlt)]
      simp only [St.setIn, Mem.set8_setIn ha]
    · cases h5
  | st64 a hi he =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨j, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := hi s j s2 h0 h1
    obtain ⟨v, s3, h3, h4⟩ := run_bind_ok h2
    obtain ⟨rfl, h3'⟩ := he s v s3 h0 h3
    obtain ⟨u, s4, h5, h6⟩ := run_bind_ok h4
    obtain ⟨rfl, rfl⟩ := pure_run_ok h6
    rw [st64_run] at h5
    split at h5
    · rename_i hlt
      simp only [Except.ok.injEq, Prod.mk.injEq] at h5
      obtain ⟨-, rfl⟩ := h5
      refine ⟨run_bind_of h1' (run_bind_of h3' (run_bind_of (a := ())
        (s' := ({ s with mem := s.mem.set64 a j v } : St).setIn preIn) ?_ rfl)), rfl, rfl⟩
      rw [st64_run]
      exact ite_eq_left hlt
    · cases h5
  | st64t a ht hi he =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨u, s0, h0', h00⟩ := run_bind_ok h
    obtain ⟨rfl, h0''⟩ := ht s u s0 h0 h0'
    obtain ⟨j, s2, h1, h2⟩ := run_bind_ok h00
    obtain ⟨rfl, h1'⟩ := hi s j s2 h0 h1
    obtain ⟨v, s3, h3, h4⟩ := run_bind_ok h2
    obtain ⟨rfl, h3'⟩ := he s v s3 h0 h3
    obtain ⟨w, s4, h5, h6⟩ := run_bind_ok h4
    obtain ⟨rfl, rfl⟩ := pure_run_ok h6
    rw [st64_run] at h5
    split at h5
    · rename_i hlt
      simp only [Except.ok.injEq, Prod.mk.injEq] at h5
      obtain ⟨-, rfl⟩ := h5
      refine ⟨run_bind_of h0'' (run_bind_of h1' (run_bind_of h3' (run_bind_of (a := ())
        (s' := ({ s with mem := s.mem.set64 (tierA a u) j v } : St).setIn preIn) ?_ rfl))), rfl, rfl⟩
      rw [st64_run]
      exact ite_eq_left hlt
    · cases h5
  | copy64 hd hdi hs hsi hn =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨da, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := hd s da s2 h0 h1
    obtain ⟨i, s3, h3, h4⟩ := run_bind_ok h2
    obtain ⟨rfl, h3'⟩ := hdi s i s3 h0 h3
    obtain ⟨sa, s5, h5, h6⟩ := run_bind_ok h4
    obtain ⟨rfl, h5'⟩ := hs s sa s5 h0 h5
    obtain ⟨j, s7, h7, h8⟩ := run_bind_ok h6
    obtain ⟨rfl, h7'⟩ := hsi s j s7 h0 h7
    obtain ⟨k, s9, h9, h10⟩ := run_bind_ok h8
    obtain ⟨rfl, h9'⟩ := hn s k s9 h0 h9
    obtain ⟨st, s11, h11, h12⟩ := run_bind_ok h10
    simp only [StateT.run_get] at h11
    obtain ⟨rfl, rfl⟩ := h11
    split at h12
    · rename_i hc
      obtain ⟨u, s13, h13, h14⟩ := run_bind_ok h12
      simp only [StateT.run_set] at h13
      obtain ⟨-, rfl⟩ := h13
      obtain ⟨rfl, rfl⟩ := pure_run_ok h14
      refine ⟨run_bind_of h1' (run_bind_of h3' (run_bind_of h5' (run_bind_of h7' (run_bind_of h9'
        (run_bind_of (a := s.setIn preIn) (s' := s.setIn preIn) rfl ?_))))),
        Mem.copy64_arr8 _ _ _ _ _ _ _, by simp [Mem.copy64_bytes]⟩
      simp only [St.setIn_mem, Mem.arr64_setIn, hc, and_self, ↓reduceIte]
      refine run_bind_of (a := ()) (s' := ({ s with mem := s.mem.copy64 da i sa j k.toNat } : St).setIn preIn) ?_ rfl
      simp only [StateT.run_set, St.setIn, Mem.copy64_setIn]
      rfl
    · cases h12
  | copy8w hd hdi hs hsi hn =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨da, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := hd s da s2 h0 h1
    obtain ⟨i, s3, h3, h4⟩ := run_bind_ok h2
    obtain ⟨rfl, h3'⟩ := hdi s i s3 h0 h3
    obtain ⟨j, s7, h7, h8⟩ := run_bind_ok h4
    obtain ⟨rfl, h7'⟩ := hsi s j s7 h0 h7
    obtain ⟨k, s9, h9, h10⟩ := run_bind_ok h8
    obtain ⟨rfl, h9'⟩ := hn s k s9 h0 h9
    obtain ⟨st, s11, h11, h12⟩ := run_bind_ok h10
    simp only [StateT.run_get] at h11
    obtain ⟨rfl, rfl⟩ := h11
    have hb := hs s h0
    split at h12
    · rename_i hc
      obtain ⟨u, s13, h13, h14⟩ := run_bind_ok h12
      simp only [StateT.run_set] at h13
      obtain ⟨-, rfl⟩ := h13
      obtain ⟨rfl, rfl⟩ := pure_run_ok h14
      refine ⟨run_bind_of h1' (run_bind_of h3' (run_bind_of h7' (run_bind_of h9'
        (run_bind_of (a := s.setIn preIn) (s' := s.setIn preIn) rfl ?_)))),
        Mem.copy8w_arr8 _ _ _ _ _ _ _, by simp [Mem.copy8w_bytes]⟩
      simp only [St.setIn_mem] at hb
      simp only [St.setIn_mem, Mem.arr64_setIn, hb, hc, and_self, ↓reduceIte]
      refine run_bind_of (a := ())
        (s' := ({ s with mem := s.mem.copy8w da i (s.mem.src8 _) j k.toNat } : St).setIn preIn) ?_ rfl
      simp only [StateT.run_set, St.setIn, St.setIn_mem, hb, Mem.copy8w_setIn]
      rfl
    · cases h12
  | scan8 x c hs hi he =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨vi, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := hi s vi s2 h0 h1
    obtain ⟨ve, s3, h3, h4⟩ := run_bind_ok h2
    obtain ⟨rfl, h3'⟩ := he s ve s3 h0 h3
    obtain ⟨st, s11, h11, h12⟩ := run_bind_ok h4
    simp only [StateT.run_get] at h11
    obtain ⟨rfl, rfl⟩ := h11
    have hb := hs s h0
    simp only [St.setIn_mem] at hb
    split at h12
    · rename_i hc
      obtain ⟨u, s13, h13, h14⟩ := run_bind_ok h12
      simp only [setLoc, StateT.run_modify] at h13
      obtain ⟨-, rfl⟩ := h13
      obtain ⟨rfl, rfl⟩ := pure_run_ok h14
      refine ⟨run_bind_of h1' (run_bind_of h3'
        (run_bind_of (a := s.setIn preIn) (s' := s.setIn preIn) rfl ?_)), Keep.of_mem rfl⟩
      simp only [St.setIn_mem, hb]
      rw [if_pos hc]
      rfl
    · cases h12
  | seq _ _ ih1 ih2 =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨a, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨h1', hK⟩ := ih1 s a s2 h0 h1
    refine bind_sim h1' (keep_sim hK ?_)
    cases a with
    | normal => exact ih2 s2 r s1 (hK.pos h0) h2
    | brk => obtain ⟨rfl, rfl⟩ := pure_run_ok h2; exact ⟨rfl, Keep.refl _⟩
    | ret v => obtain ⟨rfl, rfl⟩ := pure_run_ok h2; exact ⟨rfl, Keep.refl _⟩
  | ite hc _ _ ih1 ih2 =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨b, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := hc s b s2 h0 h1
    refine bind_sim h1' ?_
    cases b
    · exact ih2 s r s1 h0 h2
    · exact ih1 s r s1 h0 h2
  | «while» hc hb ihb =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨b, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := hc s b s2 h0 h1
    refine bind_sim h1' ?_
    cases b
    · obtain ⟨rfl, rfl⟩ := pure_run_ok h2; exact ⟨rfl, Keep.refl _⟩
    · obtain ⟨a, s3, h3, h4⟩ := run_bind_ok h2
      obtain ⟨h3', hK⟩ := ihb s a s3 h0 h3
      refine bind_sim h3' (keep_sim hK ?_)
      cases a with
      | normal => exact ihn _ _ (.while hc hb) s3 r s1 (hK.pos h0) h4
      | brk => obtain ⟨rfl, rfl⟩ := pure_run_ok h4; exact ⟨rfl, Keep.refl _⟩
      | ret v => obtain ⟨rfl, rfl⟩ := pure_run_ok h4; exact ⟨rfl, Keep.refl _⟩
  | ret ha =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨vs, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := ha s vs s2 h0 h1
    obtain ⟨rfl, rfl⟩ := pure_run_ok h2
    exact ⟨run_bind_of h1' rfl, Keep.refl _⟩
  | callC xs hg ha =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨vs, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := ha s vs s2 h0 h1
    obtain ⟨rs, s3, h3, h4⟩ := run_bind_ok h2
    obtain ⟨h3', hK⟩ := invoke_sim_copy hP n ihn _ hg vs s rs s3 h0 h3
    obtain ⟨u, s4, h5, h6⟩ := run_bind_ok h4
    simp only [setLocs, StateT.run_modify] at h5
    obtain ⟨-, rfl⟩ := h5
    obtain ⟨rfl, rfl⟩ := pure_run_ok h6
    refine ⟨run_bind_of h1' (run_bind_of h3' (run_bind_of (a := ())
      (s' := (s3.setLocs xs rs).setIn preIn) ?_ rfl)), hK.trans (Keep.of_mem (St.setLocs_mem _ _ _))⟩
    simp only [setLocs, StateT.run_modify, St.setLocs_setIn]
    rfl
  | callS xs hg ha =>
    intro s r s1 h0 h
    simp only [step] at h ⊢
    obtain ⟨vs, s2, h1, h2⟩ := run_bind_ok h
    obtain ⟨rfl, h1'⟩ := ha s vs s2 h0 h1
    obtain ⟨rs, s3, h3, h4⟩ := run_bind_ok h2
    obtain ⟨h3', hK⟩ := invoke_sim_shared hP n ihn _ hg vs s rs s3 h0 h3
    obtain ⟨u, s4, h5, h6⟩ := run_bind_ok h4
    simp only [setLocs, StateT.run_modify] at h5
    obtain ⟨-, rfl⟩ := h5
    obtain ⟨rfl, rfl⟩ := pure_run_ok h6
    refine ⟨run_bind_of h1' (run_bind_of h3' (run_bind_of (a := ())
      (s' := (s3.setLocs xs rs).setIn preIn) ?_ rfl)), hK.trans (Keep.of_mem (St.setLocs_mem _ _ _))⟩
    simp only [setLocs, StateT.run_modify, St.setLocs_setIn]
    rfl

theorem ksim {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S) :
    ∀ n, KSim p t S n
  | 0 => fun _ _ _ s r s1 _ h => by cases h
  | n + 1 => fun _ _ hs => step_sim hP n (ksim hP n) hs

/-- **The simulation.** -/
theorem preSim {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S) (n : Nat)
    (f : FnName) (hf : isCopied t f = true) (vs : List Word) (s : St) (r : List Word) (s' : St)
    (h0 : 0 < s.mem.bytes.size)
    (h : (invoke p (exec p n) ("pre_" ++ f) vs).run s = .ok (r, s')) :
    (invoke p (exec p n) f vs).run (s.setIn preIn) = .ok (r, s'.setIn preIn) ∧
      s'.mem.arr8 0 = s.mem.arr8 0 := by
  obtain ⟨h1, h2, -⟩ := invoke_sim_copy hP n (ksim hP n) f hf vs s r s' h0 h
  exact ⟨h1, h2⟩

/-- **A spec of `f` is a spec of its copy**, on the memory with the prelude's bytes as input. -/
theorem preSim_triple {p : Prog} {t : NTree} {S : FnName → Bool} (hP : PreSimProg p t S)
    (n : Nat) (f : FnName) (hf : isCopied t f = true) (vs : List Word)
    (s₀ : St) (h0 : 0 < s₀.mem.bytes.size) {Q : List Word → St → Prop}
    (hQ : ⦃fun s => s = s₀.setIn preIn⦄ invoke p (exec p n) f vs ⦃fun r s => Q r s; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) ("pre_" ++ f) vs
    ⦃fun r s => Q r (s.setIn preIn) ∧ s.mem.arr8 0 = s₀.mem.arr8 0; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨h1, h2⟩ := preSim hP n f hf vs s r s' (hs ▸ h0) hrun
  exact ⟨M.of_run (P := fun x => x = s₀.setIn preIn) (by rw [hs]) h1 hQ, hs ▸ h2⟩

end L.Checker
