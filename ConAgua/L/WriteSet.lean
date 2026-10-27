module

public import ConAgua.L.Logic
public import ConAgua.Front.Preserve
import ConAgua.L.Blocks
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Write sets from the program text

`Preserve.lean` proves once that a program without `st8` keeps the byte arrays and the sizes.
The same induction gives a frame for every function of a *call-closed* set `fs` whose bodies
store only into word arrays of `A` and into words of the control array `ctl` listed in `C`. A
`ctl` index must be a literal `k`, or `k + (e &&& 1)`, which can only be `k` or `k + 1` (the
tier-indexed counts of the stores, `CTL[k + (t & 1)]`). The check `closedW` is a `Bool` function
of the text, so a concrete program's write set is `by decide +kernel`.

The frame itself is abstract here (`WFrame`): any reflexive relation on memories closed under
the allowed stores. `Arena/Frame.lean` instantiates it with `MemFrame` (the arena's layout:
`CTL` is array 1). Lane `scale`'s spike, made layout-agnostic (DESIGN.md, "The relation's architecture").

Global variables (`GVar`) are not restricted by `closedW` (a `WFrame` is closed under every global
write). Their write sets are lists of names, `closedG p G fs` (section "Global variables" below):
every run of `f ∈ fs` keeps the globals outside `G` (`GFrame`), and `Triple.gframe` adds that to a
callee's spec for its caller's `vcgen`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L

/-- The control-array words a store index can name, if the text bounds it. -/
def ctlIdx : Expr → Option (List Word)
  | .const k => some [k]
  | .bin .add (.const k) (.bin .and _ (.const 1)) => some [k, k + 1]
  | _ => none

/-- A block destination allowed by the write set: never `ctl`, both tiers of a tiered one. -/
def WArr.okW (ctl : ArrId) (A : List ArrId) : WArr → Bool
  | .plain a => a ≠ ctl && a ∈ A
  | .tier a _ => a ≠ ctl && a + tierOff ≠ ctl && a ∈ A && a + tierOff ∈ A

/-- Stores only into word arrays of `A` (never `ctl`) and into `ctl` words of `C`, no byte
stores; calls only into `fs` (global variables: any). -/
def Stmt.okW (ctl : ArrId) (A : List ArrId) (C : List Word) (fs : List FnName) : Stmt → Bool
  | .st8 .. => false
  | .st64 a i _ =>
    if a = ctl then (match ctlIdx i with | some ws => ws.all (· ∈ C) | none => false)
    else a ∈ A
  | .st64t a _ _ _ => a ≠ ctl && a + tierOff ≠ ctl && a ∈ A && a + tierOff ∈ A
  | .copy64 d .. | .copy8w d .. => d.okW ctl A
  | .seq s t => s.okW ctl A C fs && t.okW ctl A C fs
  | .ite _ s t => s.okW ctl A C fs && t.okW ctl A C fs
  | .while _ s => s.okW ctl A C fs
  | .call _ f _ => f ∈ fs
  | _ => true

/-- **The write set of a call-closed function set**: every function of `fs` that `p` defines
satisfies `okW`. -/
def closedW (ctl : ArrId) (p : Prog) (A : List ArrId) (C : List Word) (fs : List FnName) : Bool :=
  fs.all fun f => match p.lookup f with
    | some fd => fd.body.okW ctl A C fs
    | none => true

theorem closedW_lookup {ctl : ArrId} {p : Prog} {A : List ArrId} {C : List Word}
    {fs : List FnName} (hp : closedW ctl p A C fs = true) {f : FnName} (hf : f ∈ fs) {fd : FunDecl}
    (h : p.lookup f = some fd) : fd.body.okW ctl A C fs = true := by
  simp only [closedW, List.all_eq_true] at hp
  have := hp f hf
  simp only [h] at this
  exact this

/-- `closedW` reads only the lookups of `fs`: a program that agrees with a concrete one on them
has its write set. This is how a program predicate (`LiftProg p`, …) gets its write set from the
concrete program's, which is `by decide +kernel`. -/
theorem closedW_of_agree {ctl : ArrId} {p q : Prog} {A : List ArrId} {C : List Word}
    {fs : List FnName} (hq : closedW ctl q A C fs = true)
    (hpq : ∀ f ∈ fs, p.lookup f = q.lookup f) : closedW ctl p A C fs = true := by
  simp only [closedW, List.all_eq_true] at hq ⊢
  intro f hf
  rw [hpq f hf]
  exact hq f hf

/-- A frame relation for the write set `(A, C)` of control array `ctl`: reflexive, and closed under
every word store the check allows. -/
structure WFrame (ctl : ArrId) (A : List ArrId) (C : List Word) (Fr : Mem → Mem → Prop) : Prop where
  refl : ∀ m, Fr m m
  st64 : ∀ m₀ m a i v, Fr m₀ m → (a ≠ ctl ∧ a ∈ A) ∨ (a = ctl ∧ i ∈ C) → Fr m₀ (m.set64 a i v)
  /-- A frame over the arrays does not look at the global variables (their write sets are
  `closedG`'s). -/
  setG : ∀ m₀ m g v, Fr m₀ m → Fr m₀ (m.setG g v)

theorem and_one_cases (x : Word) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h : (x &&& 1).toNat < 2 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have : (x &&& 1).toNat = 0 ∨ (x &&& 1).toNat = 1 := by omega
  rcases this with h0 | h1
  · left; exact UInt64.toNat_inj.mp (by simpa using h0)
  · right; exact UInt64.toNat_inj.mp (by simpa using h1)

theorem and_one_mem (k x : Word) : k + (x &&& 1) ∈ [k, k + 1] := by
  rcases and_one_cases x with h | h <;> simp [h]

/-- A tier word `t ≤ 1` is its own low bit: `CTL[k + (t & 1)]` is `CTL[k + t]`. -/
theorem and_one_of_le (t : Word) (h : t ≤ 1) : t &&& 1 = t := by
  have : t.toNat ≤ 1 := h
  rcases (show t.toNat = 0 ∨ t.toNat = 1 by omega) with h | h
  · rw [UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm)]; decide
  · rw [UInt64.toNat_inj.mp (h.trans UInt64.toNat_one.symm)]; decide

/-- A tier's array is the array or its tier-1 twin. -/
theorem tierA_cases (a : ArrId) (t : Word) : tierA a t = a ∨ tierA a t = a + tierOff := by
  rcases and_one_cases t with h | h <;> simp [tierA, h]

theorem ctlIdx_sound (e : Expr) (ws : List Word) (he : ctlIdx e = some ws) :
    ∀ s₀ : St, ⦃fun s => s = s₀⦄ evalE e ⦃fun j s => s = s₀ ∧ j ∈ ws; ⊤⦄ := by
  unfold ctlIdx at he
  split at he
  · cases he; intro s₀; vcgen [evalE] <;> grind
  · rename_i k x
    cases he; intro s₀
    vcgen [evalE, evalE_same x] <;> grind [and_one_mem, BinOp.eval]
  · cases he

section frame
variable {ctl : ArrId} {A : List ArrId} {C : List Word} {fs : List FnName} {Fr : Mem → Mem → Prop}

/-- A continuation that keeps the frame on `okW` statements. -/
def FrK (ctl : ArrId) (A : List ArrId) (C : List Word) (fs : List FnName) (Fr : Mem → Mem → Prop)
    (k : Stmt → M Sig) : Prop :=
  ∀ st, st.okW ctl A C fs = true → ∀ m₀, ⦃fun s => Fr m₀ s.mem⦄ k st ⦃fun _ s => Fr m₀ s.mem; ⊤⦄

theorem invoke_fr (p : Prog) (hp : closedW ctl p A C fs = true) (k : Stmt → M Sig)
    (hk : FrK ctl A C fs Fr k) (f : FnName) (hf : f ∈ fs) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => Fr m₀ s.mem⦄ invoke p k f vs ⦃fun _ s => Fr m₀ s.mem; ⊤⦄ := by
  cases h : p.lookup f with
  | none => simp only [invoke, lookupFn, h]; vcgen <;> grind
  | some fd =>
    rw [invoke_eq _ h]
    have hb := closedW_lookup hp hf h
    simp only [callFn]
    vcgen [hk fd.body hb m₀] <;> grind

theorem st64_fr (hW : WFrame ctl A C Fr) (m₀ : Mem) (a : ArrId) (j v : Word) :
    ⦃fun s => Fr m₀ s.mem ∧ ((a ≠ ctl ∧ a ∈ A) ∨ (a = ctl ∧ j ∈ C))⦄ L.st64 a j v
    ⦃fun _ s => Fr m₀ s.mem; ⊤⦄ := by
  have := hW.st64
  vcgen [L.st64] <;> grind

theorem WFrame.copy64 (hW : WFrame ctl A C Fr) {m₀ m : Mem} (h : Fr m₀ m) {a : ArrId}
    (ha : a ≠ ctl ∧ a ∈ A) (di : Word) (s : ArrId) (si : Word) (n : Nat) :
    Fr m₀ (m.copy64 a di s si n) := by
  induction n generalizing m di si with
  | zero => exact h
  | succ n ih => exact ih (hW.st64 _ _ _ _ _ h (.inl ha)) _ _

theorem WFrame.copy8w (hW : WFrame ctl A C Fr) {m₀ m : Mem} (h : Fr m₀ m) {a : ArrId}
    (ha : a ≠ ctl ∧ a ∈ A) (di : Word) (b : Array UInt8) (si : Word) (n : Nat) :
    Fr m₀ (m.copy8w a di b si n) := by
  induction n generalizing m di si with
  | zero => exact h
  | succ n ih => exact ih (hW.st64 _ _ _ _ _ h (.inl ha)) _ _

theorem warr_okW (w : WArr) (hw : w.okW ctl A = true) (s₀ : St) :
    ⦃fun s => s = s₀⦄ warr w ⦃fun a s => s = s₀ ∧ a ≠ ctl ∧ a ∈ A; ⊤⦄ := by
  cases w with
  | plain a =>
    simp only [WArr.okW, Bool.and_eq_true, decide_eq_true_eq] at hw
    vcgen [warr] <;> grind
  | tier a t =>
    simp only [WArr.okW, Bool.and_eq_true, decide_eq_true_eq] at hw
    have := tierA_cases a
    vcgen [warr, evalE_same t] <;> grind

theorem step_fr (p : Prog) (hp : closedW ctl p A C fs = true) (hW : WFrame ctl A C Fr)
    (k : Stmt → M Sig) (hk : FrK ctl A C fs Fr k) : FrK ctl A C fs Fr (step p k) := by
  intro st hst m₀
  induction st with
  | «skip» => vcgen [step] <;> grind
  | set x e => vcgen [step, setLoc, evalE_same e] <;> grind [St.setLoc_mem]
  | st8 a i e => simp [Stmt.okW] at hst
  | st64 a i e =>
    by_cases hc : a = ctl
    · subst hc
      simp only [Stmt.okW, ite_true] at hst
      split at hst
      · rename_i ws hws
        simp only [List.all_eq_true, decide_eq_true_eq] at hst
        vcgen [step, ctlIdx_sound i ws hws, evalE_same e, st64_fr hW m₀] <;> grind
      · simp at hst
    · simp only [Stmt.okW, hc, ite_false, decide_eq_true_eq] at hst
      vcgen [step, evalE_same i, evalE_same e, st64_fr hW m₀] <;> grind
  | st64t a t i e =>
    simp only [Stmt.okW, Bool.and_eq_true, decide_eq_true_eq] at hst
    have := tierA_cases a
    vcgen [step, evalE_same t, evalE_same i, evalE_same e, st64_fr hW m₀] <;> grind
  | copy64 d di s si n =>
    simp only [Stmt.okW] at hst
    have h1 : ∀ m a di s si n, Fr m₀ m → a ≠ ctl ∧ a ∈ A → Fr m₀ (m.copy64 a di s si n) :=
      fun _ _ _ _ _ _ h ha => hW.copy64 h ha _ _ _ _
    vcgen [step, warr_okW d hst, warr_same s, evalE_same di, evalE_same si, evalE_same n] <;> grind
  | copy8w d di s si n =>
    simp only [Stmt.okW] at hst
    have h1 : ∀ m a di b si n, Fr m₀ m → a ≠ ctl ∧ a ∈ A → Fr m₀ (m.copy8w a di b si n) :=
      fun _ _ _ _ _ _ h ha => hW.copy8w h ha _ _ _ _
    vcgen [step, warr_okW d hst, evalE_same di, evalE_same si, evalE_same n] <;> grind
  | scan8 x s i e c => vcgen [step, setLoc, evalE_same i, evalE_same e] <;> grind [St.setLoc_mem]
  | seq s t ihs iht =>
    simp only [Stmt.okW, Bool.and_eq_true] at hst
    vcgen [step, ihs hst.1, iht hst.2] <;> grind
  | ite c s t ihs iht =>
    simp only [Stmt.okW, Bool.and_eq_true] at hst
    vcgen [step, evalC_same c, ihs hst.1, iht hst.2] <;> grind
  | «while» c s ih =>
    vcgen [step, evalC_same c, ih hst, hk (.while c s) hst m₀] <;> grind
  | brk => vcgen [step] <;> grind
  | ret es => vcgen [step, evalArgs_same es] <;> grind
  | «call» xs f args =>
    simp only [Stmt.okW, decide_eq_true_eq] at hst
    vcgen [step, setLocs, evalArgs_same args, invoke_fr p hp k hk f hst m₀] <;>
      grind [St.setLocs_mem']
  | «abort» e => vcgen [step, evalE_same e] <;> grind
  | gset g e =>
    have := hW.setG
    vcgen [step, setG, evalE_same e] <;> grind [St.setG_mem]

theorem exec_fr (p : Prog) (hp : closedW ctl p A C fs = true) (hW : WFrame ctl A C Fr) (n : Nat) :
    FrK ctl A C fs Fr (exec p n) := by
  induction n with
  | zero => intro st _ m₀; vcgen [exec] <;> grind
  | succ n ih => exact step_fr p hp hW (exec p n) ih

/-- **The frame of a call, from the text**, as a triple: a call of `f ∈ fs` from `s₀` ends in a
memory that is a frame of `s₀`'s. -/
theorem invoke_frame (p : Prog) (hp : closedW ctl p A C fs = true) (hW : WFrame ctl A C Fr)
    (n : Nat) (f : FnName) (hf : f ∈ fs) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun _ s => Fr s₀.mem s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  exact M.of_run (P := fun t => Fr s.mem t.mem) (hW.refl _) hrun
    (invoke_fr p hp _ (exec_fr p hp hW n) f hf s.mem vs)

/-- **The frame of a run, from the text**: a run of `f ∈ fs` ends in a frame of its start. -/
theorem run_frame (p : Prog) (hp : closedW ctl p A C fs = true) (hW : WFrame ctl A C Fr)
    (f : FnName) (hf : f ∈ fs) (n : Nat) (vs : List Word) (m : Mem) (rs : List Word) (m' : Mem)
    (h : run p n f vs m = .ok (rs, m')) : Fr m m' := by
  simp only [run] at h
  cases hr : (invoke p (exec p n) f vs).run { mem := m, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    obtain ⟨r, s'⟩ := r
    simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact M.of_run (P := fun s => Fr m s.mem) (hW.refl m) hr
      (invoke_fr p hp _ (exec_fr p hp hW n) f hf m vs)

end frame

/-! ## Global variables: write sets by name

A global's write set is a list of names. `closedG p G fs`: every function of the call-closed set
`fs` writes only the globals in `G` (array stores are not restricted here; `closedW` is about
those). Every run of `f ∈ fs` then keeps every other global (`GFrame`): the frame of a global is
by construction, with no arithmetic on indices. -/

/-- Writes only globals in `G`; calls only into `fs`. -/
def Stmt.okG (G : List GVar) (fs : List FnName) : Stmt → Bool
  | .gset g _ => g ∈ G
  | .seq s t => s.okG G fs && t.okG G fs
  | .ite _ s t => s.okG G fs && t.okG G fs
  | .while _ s => s.okG G fs
  | .call _ f _ => f ∈ fs
  | _ => true

/-- **The global write set of a call-closed function set.** -/
def closedG (p : Prog) (G : List GVar) (fs : List FnName) : Bool :=
  fs.all fun f => match p.lookup f with
    | some fd => fd.body.okG G fs
    | none => true

/-- Membership in a literal list of globals, by their numbers (for `grind`). -/
@[lang_grind =] theorem GVar.mem_cons (g h : GVar) (G : List GVar) :
    (g ∈ h :: G) = (g.id = h.id ∨ g ∈ G) := by
  simp only [List.mem_cons, eq_iff_iff]
  constructor
  · rintro (e | e)
    · exact Or.inl (congrArg GVar.id e)
    · exact Or.inr e
  · rintro (e | e)
    · left; cases g; cases h; simp_all
    · exact Or.inr e

@[lang_grind =] theorem GVar.mem_nil (g : GVar) : (g ∈ ([] : List GVar)) = False := by simp

/-- The globals outside `G` are those of `m`. -/
def GFrame (G : List GVar) (m m' : Mem) : Prop := ∀ g, g ∉ G → m'.glob g = m.glob g

theorem GFrame.glob {G : List GVar} {m m' : Mem} (h : GFrame G m m') {g : GVar} (hg : g ∉ G) :
    m'.glob g = m.glob g := h g hg

grind_pattern [lang_grind] GFrame.glob => GFrame G m m', m'.glob g

theorem GFrame.refl (G : List GVar) (m : Mem) : GFrame G m m := fun _ _ => rfl

theorem GFrame.set64 {G : List GVar} {m₀ m : Mem} (h : GFrame G m₀ m) (a : ArrId) (i v : Word) :
    GFrame G m₀ (m.set64 a i v) := h

theorem GFrame.set8 {G : List GVar} {m₀ m : Mem} (h : GFrame G m₀ m) (a : ArrId) (i v : Word) :
    GFrame G m₀ (m.set8 a i v) := h

theorem GFrame.copy64 {G : List GVar} {m₀ m : Mem} (h : GFrame G m₀ m) (d : ArrId) (di : Word)
    (s : ArrId) (si : Word) (n : Nat) : GFrame G m₀ (m.copy64 d di s si n) := fun g hg => by
  rw [Mem.copy64_glob]; exact h g hg

theorem GFrame.copy8w {G : List GVar} {m₀ m : Mem} (h : GFrame G m₀ m) (d : ArrId) (di : Word)
    (b : Array UInt8) (si : Word) (n : Nat) : GFrame G m₀ (m.copy8w d di b si n) := fun g hg => by
  rw [Mem.copy8w_glob]; exact h g hg

theorem GFrame.setG {G : List GVar} {m₀ m : Mem} (h : GFrame G m₀ m) {g : GVar} (hg : g ∈ G)
    (v : Word) : GFrame G m₀ (m.setG g v) := fun g' hg' => by
  simp only [Mem.setG]
  rw [ite_eq_right (fun (e : g' = g) => hg' (e ▸ hg))]
  exact h g' hg'

theorem closedG_lookup {p : Prog} {G : List GVar} {fs : List FnName} (hp : closedG p G fs = true)
    {f : FnName} (hf : f ∈ fs) {fd : FunDecl} (h : p.lookup f = some fd) : fd.body.okG G fs = true := by
  simp only [closedG, List.all_eq_true] at hp
  have := hp f hf
  simp only [h] at this
  exact this

/-- `closedG` reads only the lookups of `fs` (as `closedW_of_agree`). -/
theorem closedG_of_agree {p q : Prog} {G : List GVar} {fs : List FnName}
    (hq : closedG q G fs = true) (hpq : ∀ f ∈ fs, p.lookup f = q.lookup f) :
    closedG p G fs = true := by
  simp only [closedG, List.all_eq_true] at hq ⊢
  intro f hf
  rw [hpq f hf]
  exact hq f hf

section gframe
variable {G : List GVar} {fs : List FnName}

/-- A continuation that keeps the globals outside `G` on `okG` statements. -/
def GK (G : List GVar) (fs : List FnName) (k : Stmt → M Sig) : Prop :=
  ∀ st, st.okG G fs = true → ∀ m₀, ⦃fun s => GFrame G m₀ s.mem⦄ k st ⦃fun _ s => GFrame G m₀ s.mem; ⊤⦄

theorem invoke_g (p : Prog) (hp : closedG p G fs = true) (k : Stmt → M Sig) (hk : GK G fs k)
    (f : FnName) (hf : f ∈ fs) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => GFrame G m₀ s.mem⦄ invoke p k f vs ⦃fun _ s => GFrame G m₀ s.mem; ⊤⦄ := by
  cases h : p.lookup f with
  | none => simp only [invoke, lookupFn, h]; vcgen <;> grind
  | some fd =>
    rw [invoke_eq _ h]
    have hb := closedG_lookup hp hf h
    simp only [callFn]
    vcgen [hk fd.body hb m₀] <;> grind

theorem step_g (p : Prog) (hp : closedG p G fs = true) (k : Stmt → M Sig) (hk : GK G fs k) :
    GK G fs (step p k) := by
  intro st hst m₀
  induction st with
  | «skip» => vcgen [step] <;> grind
  | set x e => vcgen [step, setLoc, evalE_same e] <;> grind [St.setLoc_mem]
  | st8 a i e => vcgen [step, L.st8, evalE_same i, evalE_same e] <;> grind [GFrame.set8]
  | st64 a i e => vcgen [step, L.st64, evalE_same i, evalE_same e] <;> grind [GFrame.set64]
  | st64t a t i e =>
    vcgen [step, L.st64, evalE_same t, evalE_same i, evalE_same e] <;> grind [GFrame.set64]
  | copy64 d di s si n =>
    vcgen [step, warr_same d, warr_same s, evalE_same di, evalE_same si, evalE_same n] <;>
      grind [GFrame.copy64]
  | copy8w d di s si n =>
    vcgen [step, warr_same d, evalE_same di, evalE_same si, evalE_same n] <;> grind [GFrame.copy8w]
  | scan8 x s i e c => vcgen [step, setLoc, evalE_same i, evalE_same e] <;> grind [St.setLoc_mem]
  | seq s t ihs iht =>
    simp only [Stmt.okG, Bool.and_eq_true] at hst
    vcgen [step, ihs hst.1, iht hst.2] <;> grind
  | ite c s t ihs iht =>
    simp only [Stmt.okG, Bool.and_eq_true] at hst
    vcgen [step, evalC_same c, ihs hst.1, iht hst.2] <;> grind
  | «while» c s ih =>
    vcgen [step, evalC_same c, ih hst, hk (.while c s) hst m₀] <;> grind
  | brk => vcgen [step] <;> grind
  | ret es => vcgen [step, evalArgs_same es] <;> grind
  | «call» xs f args =>
    simp only [Stmt.okG, decide_eq_true_eq] at hst
    vcgen [step, setLocs, evalArgs_same args, invoke_g p hp k hk f hst m₀] <;>
      grind [St.setLocs_mem']
  | «abort» e => vcgen [step, evalE_same e] <;> grind
  | gset g e =>
    simp only [Stmt.okG, decide_eq_true_eq] at hst
    vcgen [step, setG, evalE_same e] <;> grind [GFrame.setG, St.setG_mem]

theorem exec_g (p : Prog) (hp : closedG p G fs = true) (n : Nat) : GK G fs (exec p n) := by
  induction n with
  | zero => intro st _ m₀; vcgen [exec] <;> grind
  | succ n ih => exact step_g p hp (exec p n) ih

/-- **The global frame of a call**: a call of `f ∈ fs` keeps every global outside `G`. -/
theorem invoke_gframe (p : Prog) (hp : closedG p G fs = true) (n : Nat) (f : FnName) (hf : f ∈ fs)
    (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun _ s => GFrame G s₀.mem s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  exact M.of_run (P := fun t => GFrame G s.mem t.mem) (GFrame.refl _ _) hrun
    (invoke_g p hp _ (exec_g p hp n) f hf s.mem vs)

/-- **The global frame of a run**: a run of `f ∈ fs` keeps every global outside `G`. -/
theorem run_gframe (p : Prog) (hp : closedG p G fs = true) (f : FnName) (hf : f ∈ fs) (n : Nat)
    (vs : List Word) (m : Mem) (rs : List Word) (m' : Mem) (h : run p n f vs m = .ok (rs, m')) :
    GFrame G m m' := by
  simp only [run] at h
  cases hr : (invoke p (exec p n) f vs).run { mem := m, loc := Locals.init [] } with
  | error e => simp [hr, Except.map] at h
  | ok r =>
    obtain ⟨r, s'⟩ := r
    simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact M.of_run (P := fun s => GFrame G m s.mem) (GFrame.refl _ m) hr
      (invoke_g p hp _ (exec_g p hp n) f hf m vs)

/-- **A callee spec, with the global frame**: a triple about `invoke p (exec p n) f vs` also
keeps every global outside `G`. Pass it to the caller's `vcgen` in place of the plain spec;
`grind` then reads the untouched globals through `GFrame.glob` (with `GVar.mem_cons`). -/
theorem Triple.gframe {p : Prog} (hp : closedG p G fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat}
    {vs : List Word} {s₀ : St} {Q : List Word → St → Prop}
    (h : ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun r s => Q r s; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun r s => Q r s ∧ GFrame G s₀.mem s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  exact ⟨M.of_run (P := fun s => s = s₀) hs hrun h,
    M.of_run (P := fun s => s = s₀) hs hrun (invoke_gframe p hp n f hf vs s₀)⟩

end gframe

end L
