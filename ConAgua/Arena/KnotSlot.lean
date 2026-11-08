module

public import ConAgua.Arena.Knot
import ConAgua.Arena.WhnfDeltaSlot
public import ConAgua.Arena.SimLib
public import ConAgua.Arena.KnotE
public import ConAgua.Arena.RefECore
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreSlot
import ConAgua.L.ModelGen
public import ConAgua.Checker.NoVerdictFns
import all ConAgua.Arena.Knot

@[expose] public section

/-!
# The knot's `infer`, `infer_io`, `defeq`, `defeq_e` slots one level up (lane `defeq`)

`infer(mode, vis, d, e)` (`Knot.lean`) refines the `infer` slot of `coreKnot mode eager fe id (F + 1)`:
a memo hit (`inferC`, array 99, at the mode's eager bit) answers the entry, a miss runs
`infer_body` (the body, `inferBody (coreKnot … F)`), records it and answers it. The same for
`infer_io` (`inferIOC`, array 100, the body at the io view) and `defeq` (`defeqC`, array 101, key
`(a, b ∣ eb << 32)`, `Bool` values). The pattern of `WhnfDeltaSlot.lean`'s `whnf`, without the
stuck tags: a word-level model (`memoSlotW`), the L spec by `vcgen` + `finish`, the
refinement from the body's spec (`InferBodySpec`, …, hypotheses) and the memo lemmas; `defeq` and
`is_def_eq_core` by their unified models, one refinement for both outcomes (`dsl_ref`, `ice_ref`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- What the slot specs need of a program: the four slots and their memos' `find`/`put`. -/
structure KnotProg (p : Prog) : Prop where
  infer : p.lookup "infer" = some inferSlotL
  inferIO : p.lookup "infer_io" = some inferIOSlotL
  defeq : p.lookup "defeq" = some defeqSlotL
  defeqE : p.lookup "defeq_e" = some defeqESlotL
  inFind : p.lookup "in_find" = some (memoFindG inSch)
  inPut : p.lookup "in_put" = some (memoPutG inSch)
  ioFind : p.lookup "io_find" = some (memoFindG ioSch)
  ioPut : p.lookup "io_put" = some (memoPutG ioSch)
  deFind : p.lookup "de_find" = some (memoFindG deSch)
  dePut : p.lookup "de_put" = some (memoPutG deSch)

/-! ## The models -/

/-- **The model of a one-call forwarder** (`defeq_e`, the entry points): the callee's run, its
first result word. -/
def call1W (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (m : Mem) : Option (Word × Mem) :=
  match callW p n f vs m with
  | none => none
  | some (r, m') => some (r.headD 0, m')

theorem call1W_some (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (m m' : Mem) (r : List Word)
    (h : callW p n f vs m = some (r, m')) : call1W p n f vs m = some (r.headD 0, m') := by
  simp only [call1W, h]

/-- **A refinement spec applies to a forwarded run** whose decoding reads the first word. -/
theorem CoreSpec.of_call1W {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (h : CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb)
    (hdec : ∀ r r' : List Word, r.headD 0 = r'.headD 0 → dec r = dec r') {r : List Word} {m' : Mem}
    (hc : call1W p n f args s₀.mem = some (r.headD 0, m')) :
    CoreRef T a₀ dec dn s₀.mem vis fe M eb r m' := by
  rcases hcall : callW p n f args s₀.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hcall, call1W, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  obtain ⟨hw, rfl⟩ := hc
  obtain ⟨h1, h2, h3, h4⟩ := CoreSpec.of_callW h hcall
  exact ⟨h1, h2, h3.trans (hdec _ _ hw), by unfold ResH at h4 ⊢; rw [← hw]; exact h4⟩

/-! ## `defeqC`'s `find; put` at the eager bit -/

/-- `dKeyG`'s decoding at two handle words and an eager bit. -/
theorem dKeyG_dk (a b eb : Word) (hb : b.toNat < 2 ^ 32) (heb : eb ≤ 1) :
    dKeyG.dk a (genW b eb) = ((decE a, decE b), eb) := by
  have hg : eb.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at heb; simp at heb; omega
  show (pairKey.dk a (genW b eb &&& 0xFFFFFFFF), genW b eb >>> 32) = _
  rw [genW_lo b eb hb, genW_hi b eb hb hg]; rfl

/-- **A `find; put` of `defeqC`** at the eager bit `eb` is the twin field's insert (the `Bool`
twin of `ModeR.setE`). -/
theorem ModeR.setD {S : MemoSch} {m : Mem} {M : Std.HashMap ((EIdx × EIdx) × Word) Bool} {eb : Word}
    {t te : Std.HashMap (EIdx × EIdx) Bool} (hS : S.WF) (h : ModeR S dKeyG VB m M eb t te)
    (heb : eb ≤ 1) (a b r : Word) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) (m' : Mem)
    (hs : msetG S m a (genW b eb) r = some m') :
    ModeR S dKeyG VB m' (M.insert ((decE a, decE b), eb) (decB r)) eb
      (t.insert (decE a, decE b) (decB r)) te := by
  have hok : dKeyG.ok a (genW b eb) := by
    show (pairKey (k₁ := .expr) (k₂ := .expr)).ok a (genW b eb &&& 0xFFFFFFFF); rw [genW_lo b eb hb]; exact ⟨ha, hb⟩
  have hR := memoRV_set S hS dKeyG VB (fun _ _ _ _ _ h => h) m M h.memo a (genW b eb) r hok
    (decB r) rfl m' hs
  rw [dKeyG_dk a b eb hb heb] at hR
  refine ⟨hR, bank_set M eb t h.cur _ _, fun h0 => ?_, h.empty⟩
  exact bank_other M eb 1 te (h.stored h0) (by rw [h0]; decide) _ _

/-! ## The relation across the slots' memo `find; put` -/

/-- `inferC` gains an entry (at `inSch`: array 99, `CTL` 102/103). -/
theorem CoreS.set_in {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG inSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        inferC := a.caches.inferC.insert (decE e) (decE x) } } vis fe
      { M with inf := M.inf.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [(INM : TieredArray)] [103] m m' := msetG_frame inSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have c := hS.core
  exact hS.set_core hf ⟨c.wc.frame1 hf, c.wk.frame1 hf, c.wh.frame1 hf, c.inf.setE
    (coreSch_wf _ _ (by decide) (by decide)) c.eb1 e x he hx m' hs, c.io.frame1 hf, c.de.frame1 hf,
    c.eb1, c.ct.frame1 hf, c.cv.frame1 hf, c.rr.frame1 hf, c.lq.frame1 hf, c.lsq.frame1 hf⟩
    rfl rfl rfl

/-- `inferIOC` gains an entry (at `ioSch`: array 100, `CTL` 104/105). -/
theorem CoreS.set_io {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (e x : Word)
    (he : HW e) (hx : HW x) (hs : msetG ioSch m e (genW 0 eb) x = some m') :
    CoreS dn m' { a with caches := { a.caches with
        inferIOC := a.caches.inferIOC.insert (decE e) (decE x) } } vis fe
      { M with io := M.io.insert (decE e, eb) (decE x) } eb ∧ StackKept m m' := by
  have hf : MemFrame [(IOM : TieredArray)] [105] m m' := msetG_frame ioSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
  have c := hS.core
  exact hS.set_core hf ⟨c.wc.frame1 hf, c.wk.frame1 hf, c.wh.frame1 hf,
    c.inf.frame1 hf, c.io.setE (coreSch_wf _ _ (by decide) (by decide)) c.eb1 e x he hx m' hs,
    c.de.frame1 hf, c.eb1, c.ct.frame1 hf, c.cv.frame1 hf, c.rr.frame1 hf, c.lq.frame1 hf,
    c.lsq.frame1 hf⟩ rfl rfl rfl

/-- `defeqC` gains a verdict (at `deSch`: array 101, `CTL` 106/107, key
`(a, genW b eb)`). -/
theorem CoreS.set_de {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (x y r : Word)
    (hx : HW x) (hy : HW y) (hs : msetG deSch m x (genW y eb) r = some m') :
    CoreS dn m' { a with caches := { a.caches with
        defeqC := a.caches.defeqC.insert (decE x, decE y) (decB r) } } vis fe
      { M with de := M.de.insert ((decE x, decE y), eb) (decB r) } eb ∧ StackKept m m' := by
  have hf : MemFrame [(DEM : TieredArray)] [107] m m' := msetG_frame deSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ r hs
  have c := hS.core
  exact hS.set_core hf ⟨c.wc.frame1 hf, c.wk.frame1 hf, c.wh.frame1 hf,
    c.inf.frame1 hf, c.io.frame1 hf, c.de.setD (coreSch_wf _ _ (by decide) (by decide)) c.eb1 x y r
    hx hy m' hs, c.eb1, c.ct.frame1 hf, c.cv.frame1 hf, c.rr.frame1 hf, c.lq.frame1 hf,
    c.lsq.frame1 hf⟩ rfl rfl rfl

/-- `KeptAll` across a `infer` memo insert. -/
theorem KeptAll.inf {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with inf := M'.inf.insert (k, eb) v } eb := fun h0 =>
  let ⟨a1, b1, c1, d1, e1, f1⟩ := h h0; ⟨a1, b1, c1, d1.insert h0 k v, e1, f1⟩

/-- `KeptAll` across a `infer_io` memo insert. -/
theorem KeptAll.io {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx) (v : EIdx) :
    KeptAll M { M' with io := M'.io.insert (k, eb) v } eb := fun h0 =>
  let ⟨a1, b1, c1, d1, e1, f1⟩ := h h0; ⟨a1, b1, c1, d1, e1.insert h0 k v, f1⟩

/-- `KeptAll` across a `defeq` memo insert. -/
theorem KeptAll.de {M M' : ModeMaps} {eb : Word} (h : KeptAll M M' eb) (k : EIdx × EIdx) (v : Bool) :
    KeptAll M { M' with de := M'.de.insert (k, eb) v } eb := fun h0 =>
  let ⟨a1, b1, c1, d1, e1, f1⟩ := h h0; ⟨a1, b1, c1, d1, e1, f1.insert h0 k v⟩

/-! ## The twin's slots -/

section twin
variable (mode : ConLeche.CheckMode) (eager : Bool) (fe : IFEnv) (F : Nat) (d : Nat) (e x y : EIdx) (a : AState)

theorem knot_infer_hit (v : EIdx) (hm : a.caches.inferC[e]? = some v) :
    ((coreKnot mode eager fe id (F + 1)).infer d e).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_infer_miss (hm : a.caches.inferC[e]? = none) (v : EIdx) (a₁ : AState)
    (hb : (inferBody (coreKnot mode eager fe id F) fe d e).run a = .ok (v, a₁)) :
    ((coreKnot mode eager fe id (F + 1)).infer d e).run a =
      .ok (v, { a₁ with caches := { a₁.caches with inferC := a₁.caches.inferC.insert e v } }) := by
  simp [coreKnot, hm, StateT.run_bind, hb, inferSet]; rfl

theorem knot_inferIO_hit (v : EIdx) (hm : a.caches.inferIOC[e]? = some v) :
    ((coreKnot mode eager fe id (F + 1)).inferIO d e).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_inferIO_miss (hm : a.caches.inferIOC[e]? = none) (v : EIdx) (a₁ : AState)
    (hb : (inferBodyIO (CoreFnsA.ioView (coreKnot mode eager fe id F)) fe d e).run a = .ok (v, a₁)) :
    ((coreKnot mode eager fe id (F + 1)).inferIO d e).run a =
      .ok (v, { a₁ with caches := { a₁.caches with
        inferIOC := a₁.caches.inferIOC.insert e v } }) := by
  simp [coreKnot, hm, StateT.run_bind, hb, inferIOSet]; rfl

theorem knot_defeq_hit (v : Bool) (hm : a.caches.defeqC[(x, y)]? = some v) :
    ((coreKnot mode eager fe id (F + 1)).defeq d x y).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_defeq_miss (hm : a.caches.defeqC[(x, y)]? = none) (v : Bool) (a₁ : AState)
    (hb : (defeqBody mode eager (coreKnot mode eager fe id F) fe d x y).run a = .ok (v, a₁)) :
    ((coreKnot mode eager fe id (F + 1)).defeq d x y).run a =
      .ok (v, { a₁ with caches := { a₁.caches with
        defeqC := a₁.caches.defeqC.insert (x, y) v } }) := by
  simp [coreKnot, hm, StateT.run_bind, hb, defeqSet]; rfl

end twin

/-! ## The bodies' specs (hypotheses of the slot theorems) -/

/-- `infer_body(mode, vis, d, e)` refines `inferBody` at the knot one level down, at every
`F ≥ n` (the shape of `WhnfLoopSpec`). -/
def InferBodySpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    KnotUpTo p n →
    CoreSpec p n "infer_body" [mode, vis, d, e]
      (inferBody (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE e)) decH s₀ a₀ dn vis fe MM eb

/-- `infer_body_io(mode, vis, d, e)` refines `inferBodyIO` at the io view of the knot one level
down. -/
def InferIOBodySpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    KnotUpTo p n →
    CoreSpec p n "infer_body_io" [mode, vis, d, e]
      (inferBodyIO (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE e)) decH
      s₀ a₀ dn vis fe MM eb

/-- `defeq_body(mode, vis, d, a, b)` refines `defeqBody` at the knot one level down. -/
def DefeqBodySpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW x → HW y → KnotUpTo p n →
    CoreSpec p n "defeq_body" [mode, vis, d, x, y]
      (defeqBody (decMode mode) (decEager mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE x) (decE y))
      decBool s₀ a₀ dn vis fe MM eb

/-- **`defeq_body`'s error spec** (the error half of `DefeqBodySpec`): under the same hypotheses
and the error knot up to `n`. -/
def DefeqBodySpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW x → HW y → KnotUpTo p n → KnotUpToE p n →
    CoreSpecE p n "defeq_body" [mode, vis, d, x, y]
      (defeqBody (decMode mode) (decEager mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE x) (decE y)) s₀ a₀

/-- **What the `defeq` slot's errors claim from**: `defeq_body`'s claim and the error knot at the
body's fuel. -/
structure SlotBodyG (p : Prog) (n : Nat) : Prop where
  body : DefeqBodySpecE p n
  knot : KnotUpToE p n

/-- At a memo miss the twin's slot fails where its body does. -/
theorem knot_defeq_missE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (x y : EIdx)
    (a : AState) (hm : a.caches.defeqC[(x, y)]? = none) {e : Err}
    (h : ErrClaim (defeqBody mode eager (coreKnot mode eager fe id F) fe d x y) a e) :
    ErrClaim ((coreKnot mode eager fe id (F + 1)).defeq d x y) a e := by
  refine ErrClaim.of_run_eq (fun ce hce => ?_) h
  simp [coreKnot, hm, StateT.run_bind, hce]
  rfl

/-- `infer_body`'s error claim (the error half of `InferBodySpec`). -/
def InferBodySpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n → KnotUpToE p n →
    CoreSpecE p n "infer_body" [mode, vis, d, e]
      (inferBody (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE e)) s₀ a₀

/-- `infer_body_io`'s error claim (the error half of `InferIOBodySpec`). -/
def InferIOBodySpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n → KnotUpToE p n →
    CoreSpecE p n "infer_body_io" [mode, vis, d, e]
      (inferBodyIO (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decE e)) s₀ a₀

/-- **What the `infer` slot's errors claim from**: `infer_body`'s claim and the error knot at the
body's fuel. -/
structure InferSlotBodyG (p : Prog) (n : Nat) : Prop where
  body : InferBodySpecE p n
  knot : KnotUpToE p n

/-- **What the `infer_io` slot's errors claim from**: `infer_body_io`'s claim and the error knot. -/
structure InferIOSlotBodyG (p : Prog) (n : Nat) : Prop where
  body : InferIOBodySpecE p n
  knot : KnotUpToE p n

theorem knot_infer_missE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (e : EIdx) (a : AState)
    (hm : a.caches.inferC[e]? = none) (ce : CheckError)
    (hb : (inferBody (coreKnot mode eager fe id F) fe d e).run a = .error ce) :
    ((coreKnot mode eager fe id (F + 1)).infer d e).run a = .error ce := by
  simp [coreKnot, hm, StateT.run_bind, hb]; rfl

theorem knot_inferIO_missE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (e : EIdx)
    (a : AState) (hm : a.caches.inferIOC[e]? = none) (ce : CheckError)
    (hb : (inferBodyIO (CoreFnsA.ioView (coreKnot mode eager fe id F)) fe d e).run a = .error ce) :
    ((coreKnot mode eager fe id (F + 1)).inferIO d e).run a = .error ce := by
  simp [coreKnot, hm, StateT.run_bind, hb]; rfl

/-- **The `infer` slot's model, both outcomes** (the memo's probes and put lifted, `infer_body`
through its run). -/
l_model islE_spec (p : Prog) (hf : p.lookup "infer" = some inferSlotL)
  fns [hf ↦ islE list]
  specs [callW_spec p n "in_find", callW_spec p n "in_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The `infer_io` slot's model, both outcomes.** -/
l_model isloE_spec (p : Prog) (hf : p.lookup "infer_io" = some inferIOSlotL)
  fns [hf ↦ isloE list]
  specs [callW_spec p n "io_find", callW_spec p n "io_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The `defeq` slot's model, both outcomes** (generated; the memo's probes and put lifted,
`defeq_body` through its run). -/
l_model dslE_spec (p : Prog) (hf : p.lookup "defeq" = some defeqSlotL)
  fns [hf ↦ dslE list]
  specs [callW_spec p n "de_find", callW_spec p n "de_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## The slots refine the knot's slots -/

section slots
variable (p : Prog) (hp : KnotProg p)

include hp in
/-- **`infer` refines the knot's `infer` slot, both outcomes**, from `infer_body`'s spec at L-fuel
`n` and `KnotUpTo p n`: the errors are `infer_body`'s at a memo miss; the memo's probes and put claim
nothing. -/
theorem isl_ref (n : Nat) (hk : KnotUpTo p n) (hb : InferBodySpec p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word) (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (InferSlotBodyG p n) (islE p (n + 1) s₀.mem mode vis d e)
      ((coreKnot (decMode mode) (decEager mode) fe id F).infer d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hS := hs.rel
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  simp only [islE]
  rw [hkey]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => callW_memoFind hp.inFind h)
    fun r₁ m₁ ⟨hm, hne, hr⟩ => ?_
  subst hm hr
  have hf := hS.core.inf.findE hS.core.eb1 e he hne
  simp only [islE.k_in_find]
  by_cases h2 : (mfindG inSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
  · rw [ite_eq_left h2]
    exact RefE.ret (knot_infer_hit _ fe F' d.toNat _ a₀ _ (hf.1 h2).1) (CorePost.ret hS rfl (hf.1 h2).2)
  rw [ite_eq_right h2]
  have hmiss := hf.2 (by simpa using h2)
  rcases h3 : callE p n "infer_body" [mode, vis, d, e] s₀.mem with e3 | ⟨r₃, m₃⟩
  · exact fun hG => ErrClaim.of_run_err (fun ce h => knot_infer_missE _ fe F' d.toNat _ a₀ hmiss ce h)
      (CoreSpecE.of_callE (hG.body F' s₀ a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he hk
        hG.knot) h3)
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW
    (hb F' s₀ a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he hk) (callW_of_callE h3)
  simp only [islE.k_infer_body]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  simp only [islE.k_in_find_2]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₅ m₅ h5 => ?_
  simp only [islE.k_in_put]
  have hset := callW_memoSet hp.inFind hp.inPut h4 h5
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_in e (r₃.headD 0) he hrw hset
  have hrun := knot_infer_miss _ fe F' d.toNat _ a₀ hmiss _ _ (AM.run_of_ok _ _ hok)
  rw [hres] at hrun
  exact RefE.ret hrun ⟨⟨_, hS₂, hK₁.inf _ _, hSt₁.trans hSt₂⟩, rfl, hrw⟩

include hp in
/-- **`infer` refines the knot's `infer` slot**: `InferSlot p (n + 1)` from `infer_body`'s spec at
L-fuel `n` and `KnotUpTo p n` (`isl_ref`'s ok half). -/
@[refines_part ConRon.Arena.coreKnot "infer"]
theorem infer_refines (n : Nat) (hk : KnotUpTo p n) (hb : InferBodySpec p n) :
    InferSlot p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    RefE.coreSpec (islE_spec p hp.infer (n + 1) s₀ mode vis d e)
      (isl_ref p hp n hk hb F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he)

include hp in
/-- **`infer_io` refines the knot's `inferIO` slot, both outcomes**, from `infer_body_io`'s spec at L-fuel
`n` and `KnotUpTo p n`: the errors are `infer_body_io`'s at a memo miss; the memo's probes and put claim
nothing. -/
theorem islo_ref (n : Nat) (hk : KnotUpTo p n) (hb : InferIOBodySpec p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word) (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (InferIOSlotBodyG p n) (isloE p (n + 1) s₀.mem mode vis d e)
      ((coreKnot (decMode mode) (decEager mode) fe id F).inferIO d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hS := hs.rel
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  simp only [isloE]
  rw [hkey]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => callW_memoFind hp.ioFind h)
    fun r₁ m₁ ⟨hm, hne, hr⟩ => ?_
  subst hm hr
  have hf := hS.core.io.findE hS.core.eb1 e he hne
  simp only [isloE.k_io_find]
  by_cases h2 : (mfindG ioSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
  · rw [ite_eq_left h2]
    exact RefE.ret (knot_inferIO_hit _ fe F' d.toNat _ a₀ _ (hf.1 h2).1) (CorePost.ret hS rfl (hf.1 h2).2)
  rw [ite_eq_right h2]
  have hmiss := hf.2 (by simpa using h2)
  rcases h3 : callE p n "infer_body_io" [mode, vis, d, e] s₀.mem with e3 | ⟨r₃, m₃⟩
  · exact fun hG => ErrClaim.of_run_err (fun ce h => knot_inferIO_missE _ fe F' d.toNat _ a₀ hmiss ce h)
      (CoreSpecE.of_callE (hG.body F' s₀ a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he hk
        hG.knot) h3)
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW
    (hb F' s₀ a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he hk) (callW_of_callE h3)
  simp only [isloE.k_infer_body_io]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  simp only [isloE.k_io_find_2]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₅ m₅ h5 => ?_
  simp only [isloE.k_io_put]
  have hset := callW_memoSet hp.ioFind hp.ioPut h4 h5
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_io e (r₃.headD 0) he hrw hset
  have hrun := knot_inferIO_miss _ fe F' d.toNat _ a₀ hmiss _ _ (AM.run_of_ok _ _ hok)
  rw [hres] at hrun
  exact RefE.ret hrun ⟨⟨_, hS₂, hK₁.io _ _, hSt₁.trans hSt₂⟩, rfl, hrw⟩

include hp in
/-- **`infer_io` refines the knot's `inferIO` slot**: `InferIOSlot p (n + 1)` from `infer_body_io`'s spec at
L-fuel `n` and `KnotUpTo p n` (`islo_ref`'s ok half). -/
@[refines_part ConRon.Arena.coreKnot "inferIO"]
theorem inferIO_refines (n : Nat) (hk : KnotUpTo p n) (hb : InferIOBodySpec p n) :
    InferIOSlot p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    RefE.coreSpec (isloE_spec p hp.inferIO (n + 1) s₀ mode vis d e)
      (islo_ref p hp n hk hb F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he)

include hp in
/-- **`defeq` refines the knot's `defeq` slot, both outcomes**, from `defeq_body`'s spec at L-fuel
`n` and `KnotUpTo p n`: the errors are `defeq_body`'s at a memo miss. -/
theorem dsl_ref (n : Nat) (hk : KnotUpTo p n) (hb : DefeqBodySpec p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d x y : Word) (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hx : HW x) (hy : HW y) :
    RefE (SlotBodyG p n) (dslE p (n + 1) s₀.mem mode vis d x y)
      ((coreKnot (decMode mode) (decEager mode) fe id F).defeq d.toNat (decE x) (decE y)) a₀
      (CorePost decBool dn s₀.mem vis fe MM eb ResH) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hS := hs.rel
  have hkey : y ||| (mode >>> 1 &&& 1) <<< 32 = genW y eb := by rw [hs.eb_mode]; rfl
  simp only [dslE]
  rw [hkey]
  refine RefE.onlySim (fun _ => dslE.k_de_find.none ..) (fun _ _ h => callW_memoFind hp.deFind h)
    fun r₁ m₁ ⟨hm, hne, hr⟩ => ?_
  subst hm hr
  have hf := hS.core.de.findD hS.core.eb1 x y hx hy hne
  simp only [dslE.k_de_find]
  by_cases h2 : (mfindG deSch s₀.mem x (genW y eb)).headD 0 ≠ 0
  · rw [ite_eq_left h2]
    exact RefE.ret (knot_defeq_hit _ fe F' d.toNat _ _ a₀ _ (hf.1 h2))
      (CorePost.ret hS (by simp only [decBool, decB]; split <;> simp_all [mvG]) (by
        unfold ResH HW; split <;> decide))
  rw [ite_eq_right h2]
  have hmiss := hf.2 (by simpa using h2)
  rcases h3 : callE p n "defeq_body" [mode, vis, d, x, y] s₀.mem with e | ⟨r₃, m₃⟩
  · exact fun hG => knot_defeq_missE _ fe F' d.toNat _ _ a₀ hmiss
      (CoreSpecE.of_callE (hG.body F' s₀ a₀ dn vis fe MM eb mode d x y (by omega) (by omega) hs hx hy hk
        hG.knot) h3)
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW
    (hb F' s₀ a₀ dn vis fe MM eb mode d x y (by omega) (by omega) hs hx hy hk) (callW_of_callE h3)
  simp only [dslE.k_defeq_body]
  refine RefE.onlySim (fun _ => dslE.k_de_find_2.none ..) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  simp only [dslE.k_de_find_2]
  refine RefE.onlySim (fun _ => dslE.k_de_put.none ..) (fun _ _ h => h) fun r₅ m₅ h5 => ?_
  simp only [dslE.k_de_put]
  have hset := callW_memoSet hp.deFind hp.dePut h4 h5
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_de x y (r₃.headD 0) hx hy hset
  have hrun := knot_defeq_miss _ fe F' d.toNat _ _ a₀ hmiss _ _ (AM.run_of_ok _ _ hok)
  rw [hres] at hrun
  exact RefE.ret hrun ⟨⟨_, hS₂, hK₁.de _ _, hSt₁.trans hSt₂⟩, by simp only [decBool, List.headD_cons],
    hrw⟩

include hp in
/-- **`defeq` refines the knot's `defeq` slot**: `DefeqSlot p (n + 1)` from `defeq_body`'s spec
at L-fuel `n` and `KnotUpTo p n` (`dsl_ref`'s ok half). -/
@[refines_part ConRon.Arena.coreKnot "defeq"]
theorem defeq_refines (n : Nat) (hk : KnotUpTo p n) (hb : DefeqBodySpec p n) :
    DefeqSlot p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d x y hF hn hs hx hy =>
    RefE.coreSpec (dslE_spec p hp.defeq (n + 1) s₀ mode vis d x y)
      (dsl_ref p hp n hk hb F s₀ a₀ dn vis fe MM eb mode d x y hF hn hs hx hy)

end slots

/-! ## The eager slot

From an eager mode the twin's `defeqE` moves nothing and is the `defeq` slot
(`knot_defeqE_eager`). From a plain mode it is the `defeq` slot of the knot at `mode.toEager`
on the eager set (`enterC`), then the sets swap back (`leaveC`, `knot_defeqE_plain`). In L both
sets live in one memo told apart by the eager bit, and `defeq_e` is `defeq` at the mode word with
bit 1 set: the relation at `eb = 0` on the twin's state is the relation at `eb = 1` on the entered
state, at the same maps (`CoreS.enter`: the eager tower's six tables are bank `1`, the stored
set is empty), and after the run the plain banks are kept (`KeptAll` at `eb = 1`), so the left
state is related at `eb = 0` again (`CoreS.leave`). No change to `CoreS`/`SlotPre` is needed. -/

theorem mode_cases (mode : Word) (h : mode < 4) : mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 3 := by
  have h' : mode.toNat < 4 := UInt64.lt_iff_toNat_lt.mp h
  simp only [← UInt64.toNat_inj, UInt64.reduceToNat]
  omega

theorem mode_eager (mode : Word) (h : mode < 4) (he : (decMode mode).eager = true) :
    mode ||| 2 = mode := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> revert he <;> decide

theorem mode_plain (mode : Word) (h : mode < 4) (he : (decMode mode).eager = false) :
    decMode (mode ||| 2) = (decMode mode).toEager ∧ (mode >>> 1) &&& 1 = 0 ∧ mode ||| 2 < 4 ∧
      (1 : Word) = ((mode ||| 2) >>> 1) &&& 1 := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> revert he <;> decide

theorem knot_defeqE_eager (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (x y : EIdx)
    (h : mode.eager = true) :
    (coreKnot mode eager fe id (F + 1)).defeqE d x y = (coreKnot mode eager fe id (F + 1)).defeq d x y := by
  cases mode <;> simp_all [ConLeche.CheckMode.eager, coreKnot, enterEager, leaveEager,
    ConLeche.CheckMode.toEager]

/-- The caches after `enterEager false`: the stored eager set in the six fields, the eager slot
empty. -/
def enterC (c : Caches) : Caches :=
  { c with whnfCoreC := c.eagerMemos.whnfCoreC, whnfCoreCheapC := c.eagerMemos.whnfCoreCheapC,
           whnfC := c.eagerMemos.whnfC, inferC := c.eagerMemos.inferC,
           inferIOC := c.eagerMemos.inferIOC, defeqC := c.eagerMemos.defeqC,
           eagerMemos := ModeMemos.empty }
/-- The caches after `leaveEager (some mm)`: the six fields stored back as the eager set, `mm`
in the six fields. -/
def leaveC (c : Caches) (mm : ModeMemos) : Caches :=
  { c with eagerMemos := c.modeMemos,
           whnfCoreC := mm.whnfCoreC, whnfCoreCheapC := mm.whnfCoreCheapC, whnfC := mm.whnfC,
           inferC := mm.inferC, inferIOC := mm.inferIOC, defeqC := mm.defeqC }
/-- **The eager slot from a plain mode** is the `defeq` slot of the knot at `mode.toEager`, run
on the entered caches, then left. -/
theorem knot_defeqE_plain (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (x y : EIdx) (a : AState)
    (h : mode.eager = false) (v : Bool) (a₁ : AState)
    (hr : ((coreKnot mode true fe id (F + 1)).defeq d x y).run
      { a with caches := enterC a.caches } = .ok (v, a₁)) :
    ((coreKnot mode eager fe id (F + 1)).defeqE d x y).run a =
      .ok (v, { a₁ with caches := leaveC a₁.caches a.caches.modeMemos }) := by
  simp only [coreKnot, id] at hr ⊢
  simp only [enterEager, h, Bool.false_eq_true, ite_false]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind] at hr ⊢
  cases hc : (a.caches.eagerMemos.defeqC)[(x, y)]? with
  | some w =>
    simp only [enterC, hc, StateT.run_pure] at hr
    cases hr
    simp only [StateT.run_bind, leaveEager, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind]
    rfl
  | none =>
    simp only [enterC, hc, StateT.run_bind] at hr
    cases hb : (defeqBody mode true (coreKnot mode true fe id F) fe d x y).run
        { a with caches := enterC a.caches } with
    | error e => simp only [enterC] at hb; simp only [hb] at hr; cases hr
    | ok q =>
      simp only [enterC] at hb
      simp only [hb, except_ok_bind, defeqSet, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind] at hr
      cases hr
      simp only [StateT.run_bind, hb, leaveEager, defeqSet, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind, except_ok_bind]
      rfl

/-- A mode memo at eager bit `0` is, on the entered caches, the memo at eager bit `1`. -/
theorem ModeR.enter {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
    {VR : Mem → Word → ν → Prop} {m : Mem} {M : Std.HashMap (κ × Word) ν}
    {t te : Std.HashMap κ ν} (h : ModeR S K VR m M 0 t te) : ModeR S K VR m M 1 te ∅ :=
  ⟨h.memo, h.stored rfl, fun h => absurd h (by decide), fun _ => rfl⟩

/-- A mode memo at eager bit `1` whose plain bank was kept is, on the left caches, the memo at
eager bit `0`. -/
theorem ModeR.leave {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
    {VR : Mem → Word → ν → Prop} {m : Mem} {M M' : Std.HashMap (κ × Word) ν}
    {t t' te' : Std.HashMap κ ν} (h : ModeR S K VR m M' 1 t' te') (h0 : Bank M 0 t)
    (hk : Kept0 M M') : ModeR S K VR m M' 0 t t' :=
  ⟨h.memo, fun k => (h0 k).trans (hk k).symm, fun _ => h.cur, fun h => absurd rfl h⟩

/-- **Entering the eager tower**: the relation at `eb = 0` is the relation at `eb = 1` on the
entered caches, at the same maps. -/
theorem CoreS.enter {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} (hS : CoreS dn m a vis fe M 0) :
    CoreS dn m { a with caches := enterC a.caches } vis fe M 1 :=
  ⟨hS.arena.caches_irrel _,
    ⟨hS.core.wc.enter, hS.core.wk.enter, hS.core.wh.enter, hS.core.inf.enter, hS.core.io.enter,
      hS.core.de.enter, by decide, hS.core.ct, hS.core.cv, hS.core.rr, hS.core.lq, hS.core.lsq⟩,
    hS.pins, hS.env, fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf, hS.erec,
    hS.spn, hS.memos, hS.bstk, hS.den.caches rfl rfl rfl, hS.mode⟩

/-- **Leaving the eager tower**: after an eager run that kept the plain banks, the relation at
`eb = 0` holds on the left caches. -/
theorem CoreS.leave {dn : NIdx → Option ConLeche.Name} {m m₀ : Mem} {a a₁ : AState} {vis : Word}
    {fe : IFEnv} {M M' : ModeMaps} (hS : CoreS dn m a₁ vis fe M' 1) (h0 : CoreRM m₀ a.caches M 0)
    (hK : KeptAll M M' 1) :
    CoreS dn m { a₁ with caches := leaveC a₁.caches a.caches.modeMemos } vis fe M' 0 := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hK (by decide)
  exact ⟨hS.arena.caches_irrel _,
    ⟨hS.core.wc.leave h0.wc.cur k1, hS.core.wk.leave h0.wk.cur k2, hS.core.wh.leave h0.wh.cur k3,
      hS.core.inf.leave h0.inf.cur k4, hS.core.io.leave h0.io.cur k5,
      hS.core.de.leave h0.de.cur k6, by decide, hS.core.ct, hS.core.cv, hS.core.rr, hS.core.lq,
      hS.core.lsq⟩,
    hS.pins, hS.env, fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf, hS.erec,
    hS.spn, hS.memos, hS.bstk, hS.den.caches rfl rfl rfl, hS.mode⟩

/-- `defeq_e(mode, vis, d, a, b)` refines the knot's eager slot `defeqE`. -/
def DefeqESlot (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW x → HW y →
    CoreSpec p n "defeq_e" [mode, vis, d, x, y]
      ((coreKnot (decMode mode) (decEager mode) fe id F).defeqE d.toNat (decE x) (decE y)) decBool s₀ a₀ dn vis fe
      M eb

/-- **A failure of the eager tower's `defeq` slot from a plain mode** is the eager slot's. -/
theorem knot_defeqE_plainE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (x y : EIdx)
    (a : AState) (h : mode.eager = false) (ce : CheckError)
    (hr : ((coreKnot mode true fe id (F + 1)).defeq d x y).run
      { a with caches := enterC a.caches } = .error ce) :
    ((coreKnot mode eager fe id (F + 1)).defeqE d x y).run a = .error ce := by
  simp only [coreKnot, id] at hr ⊢
  simp only [enterEager, h, Bool.false_eq_true, ite_false]
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind] at hr ⊢
  cases hc : (a.caches.eagerMemos.defeqC)[(x, y)]? with
  | some w =>
    simp only [enterC, hc, StateT.run_pure] at hr
    cases hr
  | none =>
    simp only [enterC, hc, StateT.run_bind] at hr
    cases hb : (defeqBody mode true (coreKnot mode true fe id F) fe d x y).run
        { a with caches := enterC a.caches } with
    | error e =>
      simp only [enterC] at hb; simp only [hb] at hr
      cases hr
      simp only [StateT.run_bind, hb]
      rfl
    | ok q =>
      simp only [enterC] at hb
      simp only [hb, except_ok_bind, defeqSet, StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_pure, pure_bind] at hr
      cases hr

/-- **`defeq_e`'s unified model**: the `defeq` slot at the mode word with bit 1 set, through its
run. -/
l_model deE_spec (p : Prog) (hf : p.lookup "defeq_e" = some defeqESlotL)
  fns [hf ↦ deE list] grind [arena_grind] unified

section eager
variable (p : Prog) (hp : KnotProg p)

/-- **`defeq_e` refines the knot's eager slot, both outcomes**: from the `defeq` slot at L-fuel `n`
(at the mode word with bit 1 set); its errors are that slot's. -/
theorem de_ref (n : Nat) (hd : DefeqSlot p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb mode d x y : Word)
    (hF : n + 1 ≤ F) (hn2 : n + 1 ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hx : HW x)
    (hy : HW y) :
    RefE (DefeqSlotE p n) (deE p (n + 1) s₀.mem mode vis d x y)
      ((coreKnot (decMode mode) (decEager mode) fe id F).defeqE d.toNat (decE x) (decE y)) a₀
      (CorePost decBool dn s₀.mem vis fe MM eb ResH) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [deE]
  cases he : (decMode mode).eager with
  | true =>
    rw [mode_eager mode hs.mode4 he, knot_defeqE_eager _ fe F' d.toNat _ _ he]
    rcases hc : callE p n "defeq" [mode, vis, d, x, y] s₀.mem with e | ⟨r, m⟩
    · exact fun hG => CoreSpecE.of_callE (hG (F' + 1) s₀ a₀ dn vis fe MM eb mode d x y (by omega)
        (by omega) hs hx hy) hc
    obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW (hd (F' + 1) s₀ a₀ dn vis fe MM eb mode d x y (by omega)
      (by omega) hs hx hy) (callW_of_callE hc)).post
    exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩
  | false =>
    obtain ⟨hdm, heb0, hm4, heb1⟩ := mode_plain mode hs.mode4 he
    have heb : eb = 0 := hs.eb_mode.trans heb0
    subst heb
    have hpre : SlotPre s₀ { a₀ with caches := enterC a₀.caches } dn vis fe MM 1 (mode ||| 2) :=
      ⟨hs.rel.enter, hm4, heb1⟩
    rcases hc : callE p n "defeq" [mode ||| 2, vis, d, x, y] s₀.mem with e | ⟨r, m⟩
    · intro hG
      have hE := CoreSpecE.of_callE
        (hG (F' + 1) s₀ _ dn vis fe MM 1 (mode ||| 2) d x y (by omega) (by omega) hpre hx hy) hc
      rw [hdm] at hE
      exact ErrClaim.of_run_err (fun ce h => knot_defeqE_plainE _ fe F' d.toNat _ _ a₀ he ce h) hE
    obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW
      (hd (F' + 1) s₀ _ dn vis fe MM 1 (mode ||| 2) d x y (by omega) (by omega) hpre hx hy)
      (callW_of_callE hc)
    rw [hdm] at hok hres hS'
    have hrun := knot_defeqE_plain (decMode mode) fe F' d.toNat (decE x) (decE y) a₀ he _ _
      (AM.run_of_ok _ _ hok)
    exact RefE.ret hrun ⟨⟨M', hS'.leave hs.rel.core hK', fun h => absurd rfl h, hSt'⟩, hres, hrw⟩

include hp in
/-- **`defeq_e` refines the knot's eager slot**: `DefeqESlot p (n + 1)` from the `defeq` slot at
L-fuel `n` (`de_ref`'s ok half). -/
@[refines_part ConRon.Arena.coreKnot "defeqE"]
theorem defeqE_refines (n : Nat) (hd : DefeqSlot p n) : DefeqESlot p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d x y hF hn2 hs hx hy =>
    RefE.coreSpec (deE_spec p hp.defeqE (n + 1) s₀ mode vis d x y)
      (de_ref p n hd F s₀ a₀ dn vis fe MM eb mode d x y hF hn2 hs hx hy)

end eager

/-! ## The entry points (the verified mode) -/

/-- What the entry points need of a program. -/
structure KnotEntryProg (p : Prog) : Prop where
  inferTypeCore : p.lookup "infer_type_core" = some inferTypeCoreL
  isDefEqCore : p.lookup "is_def_eq_core" = some isDefEqCoreL
  ensureSortCore : p.lookup "ensure_sort_core" = some ensureSortCoreL

/-- A level handle result word. -/
def decLv (r : List Word) : LIdx := decI (r.headD 0)

/-- `ensure_sort(mode, vis, d, e)` refines `ensureSort` at the knot (`ensureSort_refines`,
`InferLeaves.lean`, proves it from the knot's `whnf` slot). -/
def EnsureSortSpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW e →
    CoreSpec p n "ensure_sort" [mode, vis, d, e]
      (ensureSort (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE e)) decLv s₀ a₀ dn vis fe M eb

/-- **`is_def_eq_core`'s model, both outcomes** (generated; the `defeq` slot through its run). -/
l_model iceE_spec (p : Prog) (hf : p.lookup "is_def_eq_core" = some isDefEqCoreL)
  fns [hf ↦ iceE list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] unified

section entry
variable (p : Prog) (hp : KnotEntryProg p)

theorem slotPre_zero {s₀ : St} {a₀ : AState} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} (hS : CoreS dn s₀.mem a₀ vis fe M 0) :
    SlotPre s₀ a₀ dn vis fe M 0 0 := ⟨hS, by decide, by decide⟩

omit hp in
/-- **`is_def_eq_core` refines `isDefEqCore`, both outcomes**, at the verified mode, from the
`defeq` slot: the errors are the slot's. -/
theorem ice_ref (n : Nat) (hd : DefeqSlot p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep x y : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (hx : HW x) (hy : HW y) :
    RefE (DefeqSlotE p n) (iceE p (n + 1) s₀.mem vis dep x y)
      (isDefEqCore .verified fe F dep.toNat (decE x) (decE y)) a₀
      (CorePost decBool dn s₀.mem vis fe M 0 ResH) := by
  simp only [iceE]
  rcases h1 : callE p n "defeq" [0, vis, dep, x, y] s₀.mem with e | ⟨r, m⟩
  · exact fun hdE => CoreSpecE.of_callE (hdE F s₀ a₀ dn vis fe M 0 0 dep x y hF hn (slotPre_zero hS)
      hx hy) h1
  obtain ⟨hrun, hP⟩ := (CoreSpec.of_callW (hd F s₀ a₀ dn vis fe M 0 0 dep x y hF hn (slotPre_zero hS)
    hx hy) (callW_of_callE h1)).post
  exact RefE.ret hrun ⟨hP.after, hP.res.trans (by simp only [decBool, List.headD_cons]), hP.valid⟩

include hp in
/-- **`is_def_eq_core` refines `isDefEqCore`** at the verified mode, from the `defeq` slot
(`ice_ref`'s ok half). -/
@[refines_part ConRon.Arena.isDefEqCore "from DefeqSlot"]
theorem isDefEqCore_refines (n : Nat) (hd : DefeqSlot p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep x y : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (hx : HW x) (hy : HW y) :
    CoreSpec p (n + 1) "is_def_eq_core" [vis, dep, x, y]
      (isDefEqCore .verified fe F dep.toNat (decE x) (decE y)) decBool s₀ a₀ dn vis fe M 0 :=
  RefE.coreSpec (iceE_spec p hp.isDefEqCore (n + 1) s₀ vis dep x y)
    (ice_ref p n hd F s₀ a₀ dn vis fe M dep x y hF hn hS hx hy)

end entry

end L.Arena
