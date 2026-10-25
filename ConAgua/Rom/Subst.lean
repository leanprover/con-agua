import ConAgua.L.Logic
import ConAgua.L.Blocks

/-!
# The pin-data substitution lemma (lane `romload`)

The harness loads the pin-data buffer into byte array `PB`. A program that never stores to `PB`
runs exactly as the program in which every read `PB.u8[i]` is the constant read `ldc bs i` and
every `len(PB.u8)` is the constant `bs.length`, where `bs` is the buffer (`Prog.subPB`). So the
pin readers' proofs can be about ROM readers over `bs` (DESIGN.md, "The pin data as an input").
-/

namespace L.Rom

/-- The pin-data byte array. -/
abbrev PB : ArrId := 1

end L.Rom

namespace L
open L.Rom

/-- A block's byte source `PB ↦` the constant bytes `bs`. -/
def BSrc.subPB (bs : List UInt8) : BSrc → BSrc
  | .arr a => if a = PB then .rom bs else .arr a
  | .rom d => .rom d

/-- `PB.u8[i] ↦ ldc bs i`, `len(PB.u8) ↦ bs.length`. -/
def Expr.subPB (bs : List UInt8) : Expr → Expr
  | .const w => .const w
  | .var x => .var x
  | .bin op a b => .bin op (subPB bs a) (subPB bs b)
  | .ld8 a i => if a = PB then .ldc bs (subPB bs i) else .ld8 a (subPB bs i)
  | .ld64 a i => .ld64 a (subPB bs i)
  | .len8 a => if a = PB then .const (UInt64.ofNat bs.length) else .len8 a
  | .len64 a => .len64 a
  | .cmpw c a b => .cmpw c (subPB bs a) (subPB bs b)
  | .ldc d i => .ldc d (subPB bs i)
  | .glob g => .glob g
  | .ld64t a t i => .ld64t a (subPB bs t) (subPB bs i)
  | .len64t a t => .len64t a (subPB bs t)
  | .ld8x8 b i => .ld8x8 (b.subPB bs) (subPB bs i)

def WArr.subPB (bs : List UInt8) : WArr → WArr
  | .plain a => .plain a
  | .tier a t => .tier a (t.subPB bs)

def Cond.subPB (bs : List UInt8) : Cond → Cond
  | .cmp c a b => .cmp c (a.subPB bs) (b.subPB bs)
  | .and p q => .and (subPB bs p) (subPB bs q)
  | .or p q => .or (subPB bs p) (subPB bs q)
  | .not p => .not (subPB bs p)

def Stmt.subPB (bs : List UInt8) : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x (e.subPB bs)
  | .st8 a i e => .st8 a (i.subPB bs) (e.subPB bs)
  | .st64 a i e => .st64 a (i.subPB bs) (e.subPB bs)
  | .seq s t => .seq (subPB bs s) (subPB bs t)
  | .ite c s t => .ite (c.subPB bs) (subPB bs s) (subPB bs t)
  | .while c s => .while (c.subPB bs) (subPB bs s)
  | .brk => .brk
  | .ret es => .ret (es.map (Expr.subPB bs))
  | .call xs f args => .call xs f (args.map (Expr.subPB bs))
  | .abort e => .abort (e.subPB bs)
  | .gset g e => .gset g (e.subPB bs)
  | .st64t a t i e => .st64t a (t.subPB bs) (i.subPB bs) (e.subPB bs)
  | .copy64 d di s si n => .copy64 (d.subPB bs) (di.subPB bs) (s.subPB bs) (si.subPB bs) (n.subPB bs)
  | .copy8w d di s si n => .copy8w (d.subPB bs) (di.subPB bs) (s.subPB bs) (si.subPB bs) (n.subPB bs)
  | .scan8 x s i e c => .scan8 x (s.subPB bs) (i.subPB bs) (e.subPB bs) c

-- con-ron: none — a proof device (the pin data as constant data), no twin
def FunDecl.subPB (bs : List UInt8) (fd : FunDecl) : FunDecl := { fd with body := fd.body.subPB bs }

def Prog.subPB (bs : List UInt8) (p : Prog) : Prog := p.map fun d => (d.1, d.2.subPB bs)

/-- No `st8 PB _ _` anywhere. -/
def Stmt.noSt8PB : Stmt → Bool
  | .st8 a _ _ => a != PB
  | .seq s t => s.noSt8PB && t.noSt8PB
  | .ite _ s t => s.noSt8PB && t.noSt8PB
  | .while _ s => s.noSt8PB
  | _ => true

def Prog.noSt8PB (p : Prog) : Bool := p.all (·.2.body.noSt8PB)

end L

namespace L.Rom
open L
open Std.WP
open scoped Lean.Order

/-! ## Agreement of two computations on states holding `bs` in `PB` -/

/-- The invariant: byte array `PB` holds `bs`. -/
def Inv (bs : List UInt8) (s : St) : Prop := s.mem.arr8 PB = bs.toArray

/-- `x` and `y` run alike from every state satisfying the invariant, and `y` keeps it. -/
def Agree (bs : List UInt8) {α : Type} (x y : M α) : Prop :=
  ∀ s, Inv bs s → x.run s = y.run s ∧ ∀ a s', y.run s = .ok (a, s') → Inv bs s'

variable {bs : List UInt8} {α β : Type}

theorem Agree.bind {x y : M α} {f g : α → M β} (hx : Agree bs x y)
    (hf : ∀ a, Agree bs (f a) (g a)) : Agree bs (x >>= f) (y >>= g) := by
  intro s hs
  obtain ⟨h1, h2⟩ := hx s hs
  simp only [StateT.run_bind, h1]
  cases hy : y.run s with
  | error e => exact ⟨rfl, fun a s' h => by cases h⟩
  | ok p =>
    obtain ⟨a, s'⟩ := p
    obtain ⟨h3, h4⟩ := hf a s' (h2 a s' hy)
    exact ⟨h3, h4⟩

theorem Agree.pure (a : α) : Agree bs (pure a : M α) (pure a) := fun s hs =>
  ⟨rfl, fun a s' h => by simp [StateT.run_pure] at h; obtain ⟨-, rfl⟩ := h; exact hs⟩

theorem Agree.throw (e : Err) : Agree bs (throw e : M α) (throw e) := fun _ _ =>
  ⟨rfl, fun a s' h => by cases h⟩

theorem Agree.get_bind {f g : St → M α} (h : ∀ t, Inv bs t → Agree bs (f t) (g t)) :
    Agree bs (get >>= f) (get >>= g) := by
  intro s hs
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact h s hs s hs

theorem Agree.set {t : St} (ht : Inv bs t) : Agree bs (set t : M PUnit) (set t) := fun _ _ =>
  ⟨rfl, fun a s' h => by simp [StateT.run_set] at h; obtain ⟨-, rfl⟩ := h; exact ht⟩

theorem Agree.modify {g : St → St} (hg : ∀ s, Inv bs s → Inv bs (g s)) :
    Agree bs (modify g : M PUnit) (modify g) := fun s hs =>
  ⟨rfl, fun a s' h => by simp [StateT.run_modify] at h; obtain ⟨-, rfl⟩ := h; exact hg s hs⟩

theorem Agree.dite {c : Prop} [Decidable c] {x y : c → M α} {x' y' : ¬c → M α}
    (h1 : ∀ h, Agree bs (x h) (y h)) (h2 : ∀ h, Agree bs (x' h) (y' h)) :
    Agree bs (if h : c then x h else x' h) (if h : c then y h else y' h) := by
  by_cases hc : c <;> simp only [hc, ↓reduceDIte] <;> simp_all

/-! ## Expressions -/

theorem Agree.ld8 (a : ArrId) (v : Word) : Agree bs (L.ld8 a v) (L.ld8 a v) :=
  Agree.get_bind fun _ _ => Agree.dite (fun _ => Agree.pure _) (fun _ => Agree.throw _)

theorem Agree.ld64 (a : ArrId) (v : Word) : Agree bs (L.ld64 a v) (L.ld64 a v) :=
  Agree.get_bind fun _ _ => Agree.dite (fun _ => Agree.pure _) (fun _ => Agree.throw _)

theorem Agree.ldc (d : List UInt8) (v : Word) : Agree bs (L.ldc d v) (L.ldc d v) :=
  Agree.dite (fun _ => Agree.pure _) (fun _ => Agree.throw _)

theorem Agree.ldc_ld8 (v : Word) : Agree bs (L.ldc bs v) (L.ld8 PB v) := by
  intro s hs
  have hs' : s.mem.arr8 PB = bs.toArray := hs
  refine ⟨?_, (Agree.ld8 PB v s hs).2⟩
  simp only [L.ldc, L.ld8, StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hc : v.toNat < bs.length
  · have hc' : v.toNat < (s.mem.arr8 PB).size := by simpa [hs'] using hc
    simp only [hc, hc', ↓reduceDIte]
    simp [hs']
  · have hc' : ¬ v.toNat < (s.mem.arr8 PB).size := by simpa [hs'] using hc
    simp only [hc, hc', ↓reduceDIte]

theorem src8_subPB {s : St} (hs : Inv bs s) (b : BSrc) : s.mem.src8 (b.subPB bs) = s.mem.src8 b := by
  cases b with
  | arr a =>
    simp only [BSrc.subPB]
    split
    · subst a; simp only [Mem.src8]; exact hs.symm
    · rfl
  | rom d => rfl

theorem Agree.ld8x8 (b : BSrc) (v : Word) : Agree bs (L.ld8x8 (b.subPB bs) v) (L.ld8x8 b v) :=
  Agree.get_bind fun t ht => by
    simp only [src8_subPB ht]
    split
    · exact Agree.pure _
    · exact Agree.throw _

theorem evalE_subPB (e : Expr) : Agree bs (evalE (e.subPB bs)) (evalE e) := by
  induction e with
  | const w => exact Agree.pure _
  | var x => exact Agree.get_bind fun _ _ => Agree.pure _
  | bin op a b iha ihb =>
    exact Agree.bind iha fun _ => Agree.bind ihb fun _ => Agree.pure _
  | ld8 a i ih =>
    simp only [Expr.subPB]
    split
    · subst a; exact Agree.bind ih fun v => Agree.ldc_ld8 v
    · exact Agree.bind ih fun v => Agree.ld8 a v
  | ld64 a i ih => exact Agree.bind ih fun v => Agree.ld64 a v
  | len8 a =>
    simp only [Expr.subPB]
    split
    · subst a
      intro s hs
      refine ⟨?_, (Agree.get_bind (bs := bs) (g := fun t => (pure (t.mem.len8 PB) : M Word))
        (fun _ _ => Agree.pure _) s hs).2⟩
      have hs' : s.mem.arr8 PB = bs.toArray := hs
      simp [evalE, Mem.len8, hs']
    · exact Agree.get_bind fun _ _ => Agree.pure _
  | len64 a => exact Agree.get_bind fun _ _ => Agree.pure _
  | cmpw c a b iha ihb =>
    exact Agree.bind iha fun _ => Agree.bind ihb fun _ => Agree.pure _
  | ldc d i ih => exact Agree.bind ih fun v => Agree.ldc d v
  | glob g => exact Agree.get_bind fun _ _ => Agree.pure _
  | ld64t a t i iht ihi =>
    exact Agree.bind iht fun u => Agree.bind ihi fun v => Agree.ld64 (tierA a u) v
  | len64t a t ih =>
    exact Agree.bind ih fun _ => Agree.get_bind fun _ _ => Agree.pure _
  | ld8x8 b i ih => exact Agree.bind ih fun v => Agree.ld8x8 b v

theorem warr_subPB (w : WArr) : Agree bs (warr (w.subPB bs)) (warr w) := by
  cases w with
  | plain a => exact Agree.pure _
  | tier a t => exact Agree.bind (evalE_subPB t) fun _ => Agree.pure _

theorem evalC_subPB (c : Cond) : Agree bs (evalC (c.subPB bs)) (evalC c) := by
  induction c with
  | cmp c a b =>
    exact Agree.bind (evalE_subPB a) fun _ => Agree.bind (evalE_subPB b) fun _ => Agree.pure _
  | and p q ihp ihq =>
    exact Agree.bind ihp fun b => by cases b <;> first | exact ihq | exact Agree.pure _
  | or p q ihp ihq =>
    exact Agree.bind ihp fun b => by cases b <;> first | exact ihq | exact Agree.pure _
  | not p ih => exact Agree.bind ih fun _ => Agree.pure _

theorem evalArgs_subPB (es : List Expr) :
    Agree bs (evalArgs (es.map (Expr.subPB bs))) (evalArgs es) := by
  induction es with
  | nil => exact Agree.pure _
  | cons e es ih =>
    exact Agree.bind (evalE_subPB e) fun _ => Agree.bind ih fun _ => Agree.pure _

/-! ## Statements -/

theorem arr8_set8_ne (m : Mem) {a b : ArrId} (h : a ≠ b) (i v : Word) :
    (m.set8 a i v).arr8 b = m.arr8 b := by
  simp only [Mem.set8, Mem.arr8, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne h]

theorem St.setLocs_mem (s : St) (xs : List Var) (vs : List Word) : (s.setLocs xs vs).mem = s.mem := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons x xs ih => simp only [St.setLocs, ih]; rfl

theorem lookup_subPB (p : Prog) (f : FnName) :
    (Prog.subPB bs p).lookup f = (p.lookup f).map (FunDecl.subPB bs) := by
  induction p with
  | nil => rfl
  | cons d p ih =>
    simp only [Prog.subPB, List.map_cons, List.lookup] at ih ⊢
    split <;> simp_all

theorem noSt8PB_of_lookup {p : Prog} (hp : Prog.noSt8PB p = true) {f : FnName} {fd : FunDecl}
    (h : p.lookup f = some fd) : fd.body.noSt8PB = true := by
  induction p with
  | nil => simp at h
  | cons d p ih =>
    simp only [Prog.noSt8PB, List.all_cons, Bool.and_eq_true] at hp
    simp only [List.lookup] at h
    split at h
    · cases h; exact hp.1
    · exact ih hp.2 h

theorem invoke_agree {p : Prog} (hp : Prog.noSt8PB p = true) {k k' : Stmt → M Sig}
    (hk : ∀ st, st.noSt8PB = true → Agree bs (k' (st.subPB bs)) (k st)) (f : FnName)
    (vs : List Word) : Agree bs (invoke (Prog.subPB bs p) k' f vs) (invoke p k f vs) := by
  cases h : p.lookup f with
  | none =>
    have h' : (Prog.subPB bs p).lookup f = none := by rw [lookup_subPB, h]; rfl
    have e1 : lookupFn p f = throw (.noFun f) := by simp [lookupFn, h]
    have e2 : lookupFn (Prog.subPB bs p) f = throw (.noFun f) := by simp [lookupFn, h']
    simp only [invoke, e1, e2]
    exact fun _ _ => ⟨rfl, fun _ _ h => by cases h⟩
  | some fd =>
    have h' : (Prog.subPB bs p).lookup f = some (fd.subPB bs) := by rw [lookup_subPB, h]; rfl
    rw [invoke_eq vs h, invoke_eq vs h']
    exact Agree.get_bind fun t ht =>
      Agree.bind (Agree.set ht) fun _ =>
        Agree.bind (hk _ (noSt8PB_of_lookup hp h)) fun _ =>
          Agree.bind (Agree.modify fun _ h => h) fun _ => Agree.pure _

theorem step_agree {p : Prog} (hp : Prog.noSt8PB p = true) {k k' : Stmt → M Sig}
    (hk : ∀ st, st.noSt8PB = true → Agree bs (k' (st.subPB bs)) (k st)) (st : Stmt)
    (hst : st.noSt8PB = true) :
    Agree bs (step (Prog.subPB bs p) k' (st.subPB bs)) (step p k st) := by
  induction st with
  | skip => exact Agree.pure _
  | set x e =>
    exact Agree.bind (evalE_subPB e) fun _ =>
      Agree.bind (Agree.modify fun _ h => h) fun _ => Agree.pure _
  | st8 a i e =>
    have ha : a ≠ PB := by simpa [Stmt.noSt8PB] using hst
    exact Agree.bind (evalE_subPB i) fun _ => Agree.bind (evalE_subPB e) fun _ =>
      Agree.bind (Agree.get_bind fun t ht => by
        split
        · exact Agree.set ((arr8_set8_ne t.mem ha _ _).trans ht)
        · exact Agree.throw _) fun _ => Agree.pure _
  | st64 a i e =>
    exact Agree.bind (evalE_subPB i) fun _ => Agree.bind (evalE_subPB e) fun _ =>
      Agree.bind (Agree.get_bind fun t ht => by
        split
        · exact Agree.set ht
        · exact Agree.throw _) fun _ => Agree.pure _
  | st64t a t i e =>
    exact Agree.bind (evalE_subPB t) fun _ => Agree.bind (evalE_subPB i) fun _ =>
      Agree.bind (evalE_subPB e) fun _ =>
      Agree.bind (Agree.get_bind fun t ht => by
        split
        · exact Agree.set ht
        · exact Agree.throw _) fun _ => Agree.pure _
  | copy64 d di s si n =>
    exact Agree.bind (warr_subPB d) fun _ => Agree.bind (evalE_subPB di) fun _ =>
      Agree.bind (warr_subPB s) fun _ => Agree.bind (evalE_subPB si) fun _ =>
      Agree.bind (evalE_subPB n) fun _ => Agree.get_bind fun t ht => by
        split
        · exact Agree.bind (Agree.set (by simp only [Inv, Mem.copy64_arr8]; exact ht)) fun _ => Agree.pure _
        · exact Agree.throw _
  | copy8w d di s si n =>
    exact Agree.bind (warr_subPB d) fun _ => Agree.bind (evalE_subPB di) fun _ =>
      Agree.bind (evalE_subPB si) fun _ =>
      Agree.bind (evalE_subPB n) fun _ => Agree.get_bind fun t ht => by
        simp only [src8_subPB ht]
        split
        · exact Agree.bind (Agree.set (by simp only [Inv, Mem.copy8w_arr8]; exact ht)) fun _ => Agree.pure _
        · exact Agree.throw _
  | scan8 x s i e c =>
    exact Agree.bind (evalE_subPB i) fun _ => Agree.bind (evalE_subPB e) fun _ =>
      Agree.get_bind fun t ht => by
        simp only [src8_subPB ht]
        split
        · exact Agree.bind (Agree.modify fun _ h => h) fun _ => Agree.pure _
        · exact Agree.throw _
  | seq s t ihs iht =>
    simp only [Stmt.noSt8PB, Bool.and_eq_true] at hst
    exact Agree.bind (ihs hst.1) fun r => by
      cases r <;> first | exact iht hst.2 | exact Agree.pure _
  | ite c s t ihs iht =>
    simp only [Stmt.noSt8PB, Bool.and_eq_true] at hst
    exact Agree.bind (evalC_subPB c) fun b => by
      cases b
      · exact iht hst.2
      · exact ihs hst.1
  | «while» c s ih =>
    have hs : s.noSt8PB = true := hst
    exact Agree.bind (evalC_subPB c) fun b => by
      cases b
      · exact Agree.pure _
      · exact Agree.bind (ih hs) fun r => by
          cases r
          · exact hk (.while c s) hst
          · exact Agree.pure _
          · exact Agree.pure _
  | brk => exact Agree.pure _
  | ret es => exact Agree.bind (evalArgs_subPB es) fun _ => Agree.pure _
  | call xs f args =>
    exact Agree.bind (evalArgs_subPB args) fun vs =>
      Agree.bind (invoke_agree hp hk f vs) fun _ =>
        Agree.bind (Agree.modify fun s h => (congrArg (Mem.arr8 · PB)
          (St.setLocs_mem s xs _)).trans h) fun _ => Agree.pure _
  | abort e => exact Agree.bind (evalE_subPB e) fun _ => Agree.throw _
  | gset g e =>
    exact Agree.bind (evalE_subPB e) fun _ =>
      Agree.bind (Agree.modify fun _ h => h) fun _ => Agree.pure _

theorem exec_agree {p : Prog} (hp : Prog.noSt8PB p = true) (n : Nat) :
    ∀ st, st.noSt8PB = true →
      Agree bs (exec (Prog.subPB bs p) n (st.subPB bs)) (exec p n st) := by
  induction n with
  | zero => intro _ _; exact Agree.throw _
  | succ n ih => exact step_agree hp ih

/-! ## The exported theorems -/

theorem invoke_subPB {p : Prog} (hp : Prog.noSt8PB p = true) (n : Nat) (f : FnName)
    (vs : List Word) {s : St} (hs : s.mem.arr8 PB = bs.toArray) :
    (invoke (Prog.subPB bs p) (exec (Prog.subPB bs p) n) f vs).run s =
      (invoke p (exec p n) f vs).run s :=
  (invoke_agree hp (exec_agree hp n) f vs s hs).1

/-- Triple transfer: a spec of the substituted program is a spec of the program. -/
theorem triple_subPB {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {P : St → Prop}
    {Q : List Word → St → Prop} (hp : Prog.noSt8PB p = true)
    (hP : ∀ s, P s → s.mem.arr8 PB = bs.toArray)
    (h : ⦃fun s => P s⦄ invoke (Prog.subPB bs p) (exec (Prog.subPB bs p) n) f vs
      ⦃fun r s' => Q r s'; ⊤⦄) :
    ⦃fun s => P s⦄ invoke p (exec p n) f vs ⦃fun r s' => Q r s'; ⊤⦄ :=
  M.triple_of_run fun s _ _ hs hrun =>
    M.of_run hs ((invoke_subPB hp n f vs (hP s hs)).trans hrun) h

/-! ## Sanity check -/

/-- `f() = [PB.u8[0], len(PB.u8)]`. -/
def testProg : Prog := [("f", { nparams := 0, nlocals := 0, body := .ret [.ld8 PB (.const 0), .len8 PB] })]

#guard Prog.noSt8PB testProg
#guard match L.run testProg 4 "f" [] { bytes := #[#[], #[7, 8, 9]] } with
  | .ok (r, _) => r == [7, 3] | _ => false
#guard match L.run (Prog.subPB [7, 8, 9] testProg) 4 "f" [] {} with
  | .ok (r, _) => r == [7, 3] | _ => false

end L.Rom
