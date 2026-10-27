import ConAgua.Arena.Knot
import ConAgua.Arena.WhnfDeltaSlot
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The knot's `infer`, `infer_io`, `defeq`, `defeq_e` slots one level up (lane `defeq`)

`infer(mode, vis, d, e)` (`Knot.lean`) refines the `infer` slot of `coreKnot mode fe id (F + 1)`:
a memo hit (`inferC`, array 99, at the mode's eager bit) answers the entry, a miss runs
`infer_body` (the body, `inferBody (coreKnot … F)`), records it and answers it. The same for
`infer_io` (`inferIOC`, array 100, the body at the io view) and `defeq` (`defeqC`, array 101, key
`(a, b ∣ eb << 32)`, `Bool` values). The pattern of `WhnfDeltaSlot.lean`'s `whnf`, without the
stuck tags: a word-level model (`memoSlotW`, `memoSlotD`), the L spec by `vcgen` + `finish`, the
refinement from the body's spec (`InferBodySpec`, …, hypotheses) and the memo lemmas.
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

/-- A `Bool` memo around a body (`defeq`): as `memoSlotW`, but a hit answers the verdict word
`u64(v != 0)`. -/
def memoSlotD (S : MemoSch) (m : Mem) (e k : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  if mfindG S m e k = [] then none
  else if (mfindG S m e k).headD 0 ≠ 0 then
    some (Cmp.evalW .ne (mvG S m ((mfindG S m e k).tail.headD 0)) 0, m)
  else match res with
    | none => none
    | some (r, m₁) =>
      match msetG S m₁ e k (r.headD 0) with
      | none => none
      | some m₂ => some (r.headD 0, m₂)

section arms
variable (S : MemoSch) (m m₁ m₂ : Mem) (e k : Word) (r : List Word)

theorem memoSlotD_hit (res : Option (List Word × Mem)) (h0 : mfindG S m e k ≠ [])
    (h1 : (mfindG S m e k).headD 0 ≠ 0) :
    memoSlotD S m e k res = some (Cmp.evalW .ne (mvG S m ((mfindG S m e k).tail.headD 0)) 0, m) := by
  unfold memoSlotD; simp only [h0, h1, ite_false, ite_true, ne_eq, not_false_eq_true]

theorem memoSlotD_miss (h0 : mfindG S m e k ≠ []) (h1 : (mfindG S m e k).headD 0 = 0)
    (h2 : msetG S m₁ e k (r.headD 0) = some m₂) :
    memoSlotD S m e k (some (r, m₁)) = some (r.headD 0, m₂) := by
  unfold memoSlotD
  rw [ite_eq_right h0, ite_eq_right (by simp only [ne_eq, Decidable.not_not]; exact h1)]
  simp only [h2]

end arms

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

/-! ## The L specs -/

section spec
variable (p : Prog) (hp : KnotProg p)

include hp in
theorem infer_spec (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memoSlotW inSch s₀.mem e (ebKey mode)
      (callW p n "infer_body" [mode, vis, d, e] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.infer]
  simp only [callFn, inferSlotL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec inSch p _ hp.inFind n, memoPutG_spec inSch p _ hp.inPut n,
      callW_spec p n "infer_body"] <;>
    finish [memoSlotW_hit, memoSlotW_miss, mvG, ebKey]

include hp in
theorem inferIO_spec (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_io" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memoSlotW ioSch s₀.mem e (ebKey mode)
      (callW p n "infer_body_io" [mode, vis, d, e] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.inferIO]
  simp only [callFn, inferIOSlotL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec ioSch p _ hp.ioFind n, memoPutG_spec ioSch p _ hp.ioPut n,
      callW_spec p n "infer_body_io"] <;>
    finish [memoSlotW_hit, memoSlotW_miss, mvG, ebKey]

include hp in
theorem defeq_spec (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ memoSlotD deSch s₀.mem a (b ||| ebKey mode)
      (callW p n "defeq_body" [mode, vis, d, a, b] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.defeq]
  simp only [callFn, defeqSlotL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec deSch p _ hp.deFind n, memoPutG_spec deSch p _ hp.dePut n,
      callW_spec p n "defeq_body"] <;>
    finish [memoSlotD_hit, memoSlotD_miss, mvG, ebKey]

include hp in
theorem defeqE_spec (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_e" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ call1W p n "defeq" [mode ||| 2, vis, d, a, b] s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.defeqE]
  simp only [callFn, defeqESlotL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "defeq"] <;>
    finish [call1W_some]

end spec

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
  have hf : MemFrame [99] [103] m m' := msetG_frame inSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
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
  have hf : MemFrame [100] [105] m m' := msetG_frame ioSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ x hs
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
  have hf : MemFrame [101] [107] m m' := msetG_frame deSch (coreSch_wf _ _ (by decide) (by decide)) m m' _ _ r hs
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
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (F : Nat) (d : Nat) (e x y : EIdx) (a : AState)

theorem knot_infer_hit (v : EIdx) (hm : a.caches.inferC[e]? = some v) :
    ((coreKnot mode fe id (F + 1)).infer d e).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_infer_miss (hm : a.caches.inferC[e]? = none) (v : EIdx) (a₁ : AState)
    (hb : (inferBody (coreKnot mode fe id F) fe d e).run a = .ok (v, a₁)) :
    ((coreKnot mode fe id (F + 1)).infer d e).run a =
      .ok (v, { a₁ with caches := { a₁.caches with inferC := a₁.caches.inferC.insert e v } }) := by
  simp [coreKnot, hm, StateT.run_bind, hb, inferSet]; rfl

theorem knot_inferIO_hit (v : EIdx) (hm : a.caches.inferIOC[e]? = some v) :
    ((coreKnot mode fe id (F + 1)).inferIO d e).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_inferIO_miss (hm : a.caches.inferIOC[e]? = none) (v : EIdx) (a₁ : AState)
    (hb : (inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id F)) fe d e).run a = .ok (v, a₁)) :
    ((coreKnot mode fe id (F + 1)).inferIO d e).run a =
      .ok (v, { a₁ with caches := { a₁.caches with
        inferIOC := a₁.caches.inferIOC.insert e v } }) := by
  simp [coreKnot, hm, StateT.run_bind, hb, inferIOSet]; rfl

theorem knot_defeq_hit (v : Bool) (hm : a.caches.defeqC[(x, y)]? = some v) :
    ((coreKnot mode fe id (F + 1)).defeq d x y).run a = .ok (v, a) := by
  simp [coreKnot, hm]; rfl

theorem knot_defeq_miss (hm : a.caches.defeqC[(x, y)]? = none) (v : Bool) (a₁ : AState)
    (hb : (defeqBody mode (coreKnot mode fe id F) fe d x y).run a = .ok (v, a₁)) :
    ((coreKnot mode fe id (F + 1)).defeq d x y).run a =
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
      (inferBody (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decH s₀ a₀ dn vis fe MM eb

/-- `infer_body_io(mode, vis, d, e)` refines `inferBodyIO` at the io view of the knot one level
down. -/
def InferIOBodySpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    KnotUpTo p n →
    CoreSpec p n "infer_body_io" [mode, vis, d, e]
      (inferBodyIO (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE e)) decH
      s₀ a₀ dn vis fe MM eb

/-- `defeq_body(mode, vis, d, a, b)` refines `defeqBody` at the knot one level down. -/
def DefeqBodySpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW x → HW y → KnotUpTo p n →
    CoreSpec p n "defeq_body" [mode, vis, d, x, y]
      (defeqBody (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE x) (decE y))
      decBool s₀ a₀ dn vis fe MM eb

/-! ## The slots refine the knot's slots -/

section slots
variable (p : Prog) (hp : KnotProg p)

include hp in
/-- **`infer` refines the knot's `infer` slot**: `InferSlot p (n + 1)` from `infer_body`'s spec
at L-fuel `n` and `KnotUpTo p n`. -/
@[refines_part ConRon.Arena.coreKnot "infer"]
theorem infer_refines (n : Nat) (hk : KnotUpTo p n) (hb : InferBodySpec p n) :
    InferSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (infer_spec p hp n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [ebKey_eq mode eb hs.eb_mode] at hW
  unfold memoSlotW at hW
  obtain ⟨h0, hW⟩ := of_ite_none hW
  have hf := hS.core.inf.findE hS.core.eb1 e he h0
  by_cases h1 : (mfindG inSch s.mem e (genW 0 eb)).headD 0 ≠ 0
  · rw [ite_eq_left h1] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
      (knot_infer_hit _ fe F' d.toNat _ a₀ _ (hf.1 h1).1)
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact (hf.1 h1).2⟩
    rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [ite_eq_right h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  rcases hcall : callW p n "infer_body" [mode, vis, d, e] s.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hcall, reduceCtorEq] at hW
  have hbody := hb F' s a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he hk
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
  rcases hset : msetG inSch m₁ e (genW 0 eb) (r₁.headD 0) with _ | m₂ <;> simp only [hset, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_in e (r₁.headD 0) he hrw hset
  have hrun := knot_infer_miss _ fe F' d.toNat _ a₀ hmiss _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok', ?_, by rw [hres', hres]; simp only [decH, hr],
    by unfold ResH; rw [← hr]; exact hrw⟩
  rw [hst', ← hm, hres]
  exact ⟨_, hS₂, hK₁.inf _ _, hSt₁.trans hSt₂⟩

include hp in
/-- **`infer_io` refines the knot's `inferIO` slot**: `InferIOSlot p (n + 1)` from `infer_body_io`'s
spec
at L-fuel `n` and `KnotUpTo p n`. -/
@[refines_part ConRon.Arena.coreKnot "inferIO"]
theorem inferIO_refines (n : Nat) (hk : KnotUpTo p n) (hb : InferIOBodySpec p n) :
    InferIOSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (inferIO_spec p hp n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [ebKey_eq mode eb hs.eb_mode] at hW
  unfold memoSlotW at hW
  obtain ⟨h0, hW⟩ := of_ite_none hW
  have hf := hS.core.io.findE hS.core.eb1 e he h0
  by_cases h1 : (mfindG ioSch s.mem e (genW 0 eb)).headD 0 ≠ 0
  · rw [ite_eq_left h1] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
      (knot_inferIO_hit _ fe F' d.toNat _ a₀ _ (hf.1 h1).1)
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact (hf.1 h1).2⟩
    rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [ite_eq_right h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  rcases hcall : callW p n "infer_body_io" [mode, vis, d, e] s.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hcall, reduceCtorEq] at hW
  have hbody := hb F' s a₀ dn vis fe MM eb mode d e (by omega) (by omega) hs he hk
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
  rcases hset : msetG ioSch m₁ e (genW 0 eb) (r₁.headD 0) with _ | m₂ <;> simp only [hset, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_io e (r₁.headD 0) he hrw hset
  have hrun := knot_inferIO_miss _ fe F' d.toNat _ a₀ hmiss _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok', ?_, by rw [hres', hres]; simp only [decH, hr],
    by unfold ResH; rw [← hr]; exact hrw⟩
  rw [hst', ← hm, hres]
  exact ⟨_, hS₂, hK₁.io _ _, hSt₁.trans hSt₂⟩

theorem evalW_ne_decB (v : Word) : (Cmp.evalW .ne v 0 != 0) = decB v := by
  unfold Cmp.evalW Cmp.eval decB; by_cases h : v = 0 <;> simp [h]

theorem evalW_ne_hw (v : Word) : HW (Cmp.evalW .ne v 0) := by
  unfold Cmp.evalW HW; split <;> decide

include hp in
/-- **`defeq` refines the knot's `defeq` slot**: `DefeqSlot p (n + 1)` from `defeq_body`'s spec
at L-fuel `n` and `KnotUpTo p n`. -/
@[refines_part ConRon.Arena.coreKnot "defeq"]
theorem defeq_refines (n : Nat) (hk : KnotUpTo p n) (hb : DefeqBodySpec p n) :
    DefeqSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d x y hF hn2 hs hx hy
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeq_spec p hp n s₀ mode vis d x y)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hkey : y ||| ebKey mode = genW y eb := by rw [hs.eb_mode]; rfl
  rw [hkey] at hW
  unfold memoSlotD at hW
  obtain ⟨h0, hW⟩ := of_ite_none hW
  have hf := hS.core.de.findD hS.core.eb1 x y hx hy h0
  by_cases h1 : (mfindG deSch s.mem x (genW y eb)).headD 0 ≠ 0
  · rw [ite_eq_left h1] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
      (knot_defeq_hit _ fe F' d.toNat _ _ a₀ _ (hf.1 h1))
    refine ⟨hok, ?_, by rw [hres, decBool, ← hr, evalW_ne_decB],
      by unfold ResH; rw [← hr]; exact evalW_ne_hw _⟩
    rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [ite_eq_right h1] at hW
  have hmiss := hf.2 (by simpa using h1)
  rcases hcall : callW p n "defeq_body" [mode, vis, d, x, y] s.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hcall, reduceCtorEq] at hW
  have hbody := hb F' s a₀ dn vis fe MM eb mode d x y (by omega) (by omega) hs hx hy hk
  obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
  rcases hset : msetG deSch m₁ x (genW y eb) (r₁.headD 0) with _ | m₂ <;> simp only [hset, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_de x y (r₁.headD 0) hx hy hset
  have hrun := knot_defeq_miss _ fe F' d.toNat _ _ a₀ hmiss _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok', ?_, by rw [hres', hres]; simp only [decBool, hr],
    by unfold ResH; rw [← hr]; exact hrw⟩
  rw [hst', ← hm, hres]
  exact ⟨_, hS₂, hK₁.de _ _, hSt₁.trans hSt₂⟩

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
    (coreKnot mode fe id (F + 1)).defeqE d x y = (coreKnot mode fe id (F + 1)).defeq d x y := by
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
    (hr : ((coreKnot mode.toEager fe id (F + 1)).defeq d x y).run
      { a with caches := enterC a.caches } = .ok (v, a₁)) :
    ((coreKnot mode fe id (F + 1)).defeqE d x y).run a =
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
    cases hb : (defeqBody mode.toEager (coreKnot mode.toEager fe id F) fe d x y).run
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
      ((coreKnot (decMode mode) fe id F).defeqE d.toNat (decE x) (decE y)) decBool s₀ a₀ dn vis fe
      M eb

section eager
variable (p : Prog) (hp : KnotProg p)

include hp in
/-- **`defeq_e` refines the knot's eager slot**: `DefeqESlot p (n + 1)` from the `defeq` slot at
L-fuel `n` (`DefeqSlot p n`, at the mode word with bit 1 set). -/
@[refines_part ConRon.Arena.coreKnot "defeqE"]
theorem defeqE_refines (n : Nat) (hd : DefeqSlot p n) : DefeqESlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d x y hF hn2 hs hx hy
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqE_spec p hp n s₀ mode vis d x y)
  subst hs0
  refine ⟨hloc, ?_⟩
  rcases hcall : callW p n "defeq" [mode ||| 2, vis, d, x, y] s.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hcall, call1W, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hdec : decBool r₁ = decBool r := by simp only [decBool, hr]
  have hok₁ : ResH r₁ → ResH r := fun h => by unfold ResH at h ⊢; rw [← hr]; exact h
  cases he : (decMode mode).eager with
  | true =>
    rw [mode_eager mode hs.mode4 he] at hcall
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW
      (hd (F' + 1) s a₀ dn vis fe MM eb mode d x y (by omega) (by omega) hs hx hy) hcall
    rw [knot_defeqE_eager _ fe F' d.toNat _ _ he]
    exact ⟨hok, hm ▸ hA, hres.trans hdec, hok₁ hrw⟩
  | false =>
    obtain ⟨hdm, heb0, hm4, heb1⟩ := mode_plain mode hs.mode4 he
    have heb : eb = 0 := hs.eb_mode.trans heb0
    subst heb
    have hpre : SlotPre s { a₀ with caches := enterC a₀.caches } dn vis fe MM 1 (mode ||| 2) :=
      ⟨hs.rel.enter, hm4, heb1⟩
    obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW
      (hd (F' + 1) s _ dn vis fe MM 1 (mode ||| 2) d x y (by omega) (by omega) hpre hx hy) hcall
    rw [hdm] at hok hres hS'
    have hrun := knot_defeqE_plain (decMode mode) fe F' d.toNat (decE x) (decE y) a₀ he _ _
      (AM.run_of_ok _ _ hok)
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hok', ?_, by rw [hres', hres, hdec], hok₁ hrw⟩
    rw [hst', ← hm]
    exact ⟨M', hS'.leave hs.rel.core hK', fun h => absurd rfl h, hSt'⟩

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
      (ensureSort (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decLv s₀ a₀ dn vis fe M eb

section entry
variable (p : Prog) (hp : KnotEntryProg p)

include hp in
theorem inferTypeCore_spec (n : Nat) (s₀ : St) (vis dep e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_type_core" [vis, dep, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      call1W p n "infer" [0, vis, dep, e] s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.inferTypeCore]
  simp only [callFn, inferTypeCoreL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "infer"] <;>
    finish [call1W_some]

include hp in
theorem isDefEqCore_spec (n : Nat) (s₀ : St) (vis dep a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "is_def_eq_core" [vis, dep, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      call1W p n "defeq" [0, vis, dep, a, b] s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.isDefEqCore]
  simp only [callFn, isDefEqCoreL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "defeq"] <;>
    finish [call1W_some]

include hp in
theorem ensureSortCore_spec (n : Nat) (s₀ : St) (vis dep t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ensure_sort_core" [vis, dep, t]
    ⦃fun r s' => LocEq s' s₀ ∧
      call1W p n "ensure_sort" [0, vis, dep, t] s₀.mem = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ensureSortCore]
  simp only [callFn, ensureSortCoreL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "ensure_sort"] <;>
    finish [call1W_some]

theorem slotPre_zero {s₀ : St} {a₀ : AState} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} (hS : CoreS dn s₀.mem a₀ vis fe M 0) :
    SlotPre s₀ a₀ dn vis fe M 0 0 := ⟨hS, by decide, by decide⟩

include hp in
/-- **`infer_type_core` refines `inferTypeCore`** at the verified mode and every fuel `F ≥ n`
(`checkFuel` among them), from the `infer` slot at L-fuel `n`. -/
@[refines_part ConRon.Arena.inferTypeCore "from InferSlot"]
theorem inferTypeCore_refines (n : Nat) (hi : InferSlot p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep e : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    CoreSpec p (n + 1) "infer_type_core" [vis, dep, e]
      (inferTypeCore .verified fe F dep.toNat (decE e)) decH s₀ a₀ dn vis fe M 0 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferTypeCore_spec p hp n s₀ vis dep e)
  subst hs0
  exact ⟨hloc, CoreSpec.of_call1W (hi F s a₀ dn vis fe M 0 0 dep e hF hn (slotPre_zero hS) he)
    (fun r r' h => by simp only [decH, h]) hW⟩

include hp in
/-- **`is_def_eq_core` refines `isDefEqCore`** at the verified mode, from the `defeq` slot. -/
@[refines_part ConRon.Arena.isDefEqCore "from DefeqSlot"]
theorem isDefEqCore_refines (n : Nat) (hd : DefeqSlot p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep x y : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (hx : HW x) (hy : HW y) :
    CoreSpec p (n + 1) "is_def_eq_core" [vis, dep, x, y]
      (isDefEqCore .verified fe F dep.toNat (decE x) (decE y)) decBool s₀ a₀ dn vis fe M 0 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (isDefEqCore_spec p hp n s₀ vis dep x y)
  subst hs0
  exact ⟨hloc, CoreSpec.of_call1W (hd F s a₀ dn vis fe M 0 0 dep x y hF hn (slotPre_zero hS) hx hy)
    (fun r r' h => by simp only [decBool, h]) hW⟩

include hp in
/-- `ensure_sort_core` refines `ensureSortCore` at the verified mode, from `ensure_sort`'s spec
(`ensureSortCore_refines`, `InferLeaves.lean`, discharges it from the knot). -/
theorem ensureSortCore_of_spec (n : Nat) (hs : EnsureSortSpec p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (dep t : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hS : CoreS dn s₀.mem a₀ vis fe M 0) (ht : HW t) :
    CoreSpec p (n + 1) "ensure_sort_core" [vis, dep, t]
      (ensureSortCore .verified fe F dep.toNat (decE t)) decLv s₀ a₀ dn vis fe M 0 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (ensureSortCore_spec p hp n s₀ vis dep t)
  subst hs0
  exact ⟨hloc, CoreSpec.of_call1W (hs F s a₀ dn vis fe M 0 0 dep t hF hn (slotPre_zero hS) ht)
    (fun r r' h => by simp only [decLv, h]) hW⟩

end entry

end L.Arena
