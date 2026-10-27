import ConAgua.Arena.ConstsResolveF
import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
set_option linter.unusedSectionVars false

/-!
# `consts_resolve_ffast` refines `constsResolveFFast` (lane `tails`)

`ConstsResolveF.lean`'s L code (lane `stubs`) under the inductive stage's relation `StageR`, in the
`RefAM` shape of `IndStubs.lean`'s contract `constsResolveFFast_spec`.

* **Models from the calls.** Every function's word model is written over `callW` of its callees
  (`DeclNatBase.lean`'s style), so each `vcgen` spec only matches the text; the callees' meaning
  enters in the relational lemmas (`pin_at`: `pinAt_model`; `env_find`: `envFindW_found`; `e_view`:
  `eViewW_ok`; `is_str_lit`: `islW`, `viewLit_ok`).
* **The memo.** The twin threads its memo (`Std.HashMap EIdx Bool`) through the walk; the L table
  `CRM` (`crSch`) is related to it by the memo library's `MemoRV` at key `(h, 0)` (`bmKey`) and the
  value relation `CrV` (the word is `0` or `1`, and decodes to the Bool). The twin's walk changes
  no state; the L walk writes only `CRM` and `CTL[158‥159]`, which `StageR` does not read
  (`StageR.frame_hi`).
* **Fuel.** The counter word `f` is the twin's fuel (`4000000000` = `coreWalkFuel` at the entry);
  the induction is on L's fuel.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Stubs

open L.Arena L.Ind

/-- What the specs need of the program. -/
structure CrfProg (p : Prog) : Prop where
  entry : p.lookup "consts_resolve_ffast" = some constsResolveFFastL
  go : p.lookup "crf_go" = some crfGo
  leaf : p.lookup "cr_leaf" = some crLeaf
  lit : p.lookup "cr_lit_pins" = some crLitPins
  pf : p.lookup "pin_found" = some pinFound
  find : p.lookup "crm_find" = some (memoFindG crSch)
  put : p.lookup "crm_put" = some (memoPutG crSch)
  clear : p.lookup "crm_clear" = some (memoClearG crSch)
  view : p.lookup "e_view" = some eView
  isl : p.lookup "is_str_lit" = some isStrLitL
  ef : p.lookup "env_find" = some envFindL
  erg : p.lookup "env_row_get" = some envRowGetL
  eix : p.lookup "env_ix" = some envIxL
  pin : p.lookup "pin_at" = some pinAtL

/-! ## The models over the calls, and their specs -/

section models
variable (p : Prog) (k : Nat)

/-- `pin_found(vis, i)`. -/
def pfW (m : Mem) (vis i : Word) : Option (List Word × Mem) :=
  ntBW (callW p k "pin_at" [i] m) fun r1 m1 =>
  ntBW (callW p k "env_find" [r1.headD 0, vis] m1) fun r2 m2 => some ([r2.headD 0], m2)

/-- `cr_lit_pins`' chain of `pin_found` calls: the answers so far `acc`, the pins still to ask
`ks`, the last call's result. -/
def clpL (vis : Word) : Bool → List Word → Option (List Word × Mem) → Option (List Word × Mem)
  | _, _, none => none
  | z, [], some (r, m) => some ([if z || r.headD 0 == 0 then 0 else 1], m)
  | z, k' :: ks, some (r, m) => clpL vis (z || r.headD 0 == 0) ks (callW p k "pin_found" [vis, k'] m)

/-- `cr_lit_pins(vis, s)`: three pins for a `Nat` literal (`s = 0`), ten for a `String` one. -/
def clpW (m : Mem) (vis s : Word) : Option (List Word × Mem) :=
  if s = 0 then clpL p k vis false [2, 3] (callW p k "pin_found" [vis, 1] m)
  else clpL p k vis false [2, 3, 5, 6, 7, 8, 9, 10, 12] (callW p k "pin_found" [vis, 1] m)

/-- `cr_leaf(vis, g, x, h)`. -/
def clW (m : Mem) (vis g x h : Word) : Option (List Word × Mem) :=
  if g = 8 then
    ntBW (callW p k "is_str_lit" [h] m) fun rs ms =>
    ntBW (callW p k "cr_lit_pins" [vis, rs.headD 0] ms) fun r mr => some ([r.headD 0], mr)
  else if g = 3 then
    ntBW (callW p k "env_find" [x, vis] m) fun r mr => some ([r.headD 0], mr)
  else some ([1], m)

/-- The tail of every compound node: probe again, record `r`, return it. -/
def crfT2 (r : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, mp) => some ([r], mp)

def crfT1 (h r : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, mf) => crfT2 r (callW p k "crm_put" [h, 0, r, rf.headD 0, rf.tail.headD 0] mf)

def crfT (m : Mem) (h r : Word) : Option (List Word × Mem) :=
  crfT1 p k h r (callW p k "crm_find" [h, 0] m)

/-- The `fvar` arm, after the annotation. -/
def crfFv (h : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, ma) => crfT p k ma h (ra.headD 0)

/-- The two-child arms (`app`, `lam`, `forallE`). -/
def crfB2 (h a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, mb) => crfT p k mb h (if a ≠ 0 ∧ rb.headD 0 ≠ 0 then 1 else 0)

def crfB1 (vis f h y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, ma) => crfB2 p k h (ra.headD 0) (callW p k "crf_go" [vis, f - 1, y] ma)

/-- The `letE` arm. -/
def crfL3 (h a b : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, mc) => crfT p k mc h (if a ≠ 0 ∧ b ≠ 0 ∧ rc.headD 0 ≠ 0 then 1 else 0)

def crfL2 (vis f h w a : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, mb) => crfL3 p k h a (rb.headD 0) (callW p k "crf_go" [vis, f - 1, w] mb)

def crfL1 (vis f h y w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, ma) => crfL2 p k vis f h w (ra.headD 0) (callW p k "crf_go" [vis, f - 1, y] ma)

/-- The `proj` arm: the child, then the structure name. -/
def crfP2 (h r : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (re, me) => crfT p k me h (if re.headD 0 ≠ 0 ∧ r ≠ 0 then 1 else 0)

def crfP1 (vis h x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, mr) => crfP2 p k h (rr.headD 0) (callW p k "env_find" [x, vis] mr)

/-- `crf_go` on a memo miss at a compound node (the view's words `rv`). -/
def crfN (m : Mem) (vis f h : Word) (rv : List Word) : Option (List Word × Mem) :=
  if rv.headD 0 = 1 then crfFv p k h (callW p k "crf_go" [vis, f - 1, rv.tail.tail.headD 0] m)
  else if rv.headD 0 = 4 ∨ rv.headD 0 = 5 ∨ rv.headD 0 = 6 then
    crfB1 p k vis f h (rv.tail.tail.headD 0) (callW p k "crf_go" [vis, f - 1, rv.tail.headD 0] m)
  else if rv.headD 0 = 7 then
    crfL1 p k vis f h (rv.tail.tail.headD 0) (rv.tail.tail.tail.headD 0)
      (callW p k "crf_go" [vis, f - 1, rv.tail.headD 0] m)
  else crfP1 p k vis h (rv.tail.headD 0)
    (callW p k "crf_go" [vis, f - 1, rv.tail.tail.tail.headD 0] m)

/-- After the probe. -/
def crfM (vis f h : Word) (rv : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, mf) =>
    if rf.headD 0 ≠ 0 then some ([rdW (mf.arr64 CRM) (rf.tail.headD 0 * 4 + 3)], mf)
    else crfN p k mf vis f h rv

/-- A leaf's answer. -/
def crfLf : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, mr) => some ([r.headD 0], mr)

/-- After the view. -/
def crfV (vis f h : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, mv) =>
    if rv.headD 0 = 0 ∨ rv.headD 0 = 2 ∨ rv.headD 0 = 3 ∨ rv.headD 0 = 8 then
      crfLf (callW p k "cr_leaf" [vis, rv.headD 0, rv.tail.headD 0, h] mv)
    else crfM p k vis f h rv (callW p k "crm_find" [h, 0] mv)

/-- `crf_go(vis, f, h)`. -/
def crfW (m : Mem) (vis f h : Word) : Option (List Word × Mem) :=
  if f = 0 then none else crfV p k vis f h (callW p k "e_view" [h] m)

/-- `consts_resolve_ffast(vis, e)`. -/
def crffW (m : Mem) (vis e : Word) : Option (List Word × Mem) :=
  ntBW (callW p k "crm_clear" [] m) fun _ mc =>
  ntBW (callW p k "crf_go" [vis, 4000000000, e] mc) fun r mr => some ([r.headD 0], mr)

end models

theorem clpL_none (p : Prog) (k : Nat) (vis : Word) (z : Bool) (ks : List Word) :
    clpL p k vis z ks none = none := by cases ks <;> rfl
theorem clpL_nil (p : Prog) (k : Nat) (vis : Word) (z : Bool) (r : List Word) (m : Mem) :
    clpL p k vis z [] (some (r, m)) = some ([if z || r.headD 0 == 0 then 0 else 1], m) := rfl
theorem clpL_cons (p : Prog) (k : Nat) (vis k' : Word) (z : Bool) (ks r : List Word) (m : Mem) :
    clpL p k vis z (k' :: ks) (some (r, m)) =
      clpL p k vis (z || r.headD 0 == 0) ks (callW p k "pin_found" [vis, k'] m) := rfl


theorem pf_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "pin_found" [vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧ pfW p k s₀.mem vis i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.pf]
  simp only [callFn, pinFound]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p k "pin_at", callW_spec p k "env_find"] <;>
    finish (gen := 20) [pfW, ntBW]

-- The two paths' goals are closed by rewriting (`simp_all`): the locals through the `LocEq`
-- chain, the model's `pin_found` chain by the calls' posts. `grind` took ~80 s here (splitting
-- the ten-way `&&`).
theorem clp_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "cr_lit_pins" [vis, s]
    ⦃fun r s' => LocEq s' s₀ ∧ clpW p k s₀.mem vis s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.lit]
  simp only [callFn, crLitPins]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, callW_spec p k "pin_found"]
  all_goals simp_all only [Cond.pval, Expr.pval, Cmp.eval, LocEq, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_cons, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Locals.init_nil,
    Nat.reduceEqDiff, clpW, clpL_cons, clpL_nil, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, Bool.false_or, or_assoc, Classical.not_and_iff_not_or_not, Decidable.not_not,
    Sig.retVal, Sig.retOr, ite_true, ite_false, or_false, or_true]

theorem cl_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis g x h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "cr_leaf" [vis, g, x, h]
    ⦃fun r s' => LocEq s' s₀ ∧ clW p k s₀.mem vis g x h = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.leaf]
  simp only [callFn, crLeaf]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k "is_str_lit",
      callW_spec p k "cr_lit_pins", callW_spec p k "env_find"] <;>
    finish (gen := 20) [clW, ntBW]

set_option maxHeartbeats 6400000 in
theorem crf_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis f h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "crf_go" [vis, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ crfW p k s₀.mem vis f h = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.go]
  simp only [callFn, crfGo]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64,
    callW_spec p k "e_view", callW_spec p k "cr_leaf", callW_spec p k "crm_find",
    callW_spec p k "crm_put", callW_spec p k "crf_go", callW_spec p k "env_find"]
  all_goals (try simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, St.setLocs_cons, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
    Nat.reduceEqDiff, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true,
    Bool.or_eq_true] at *)
  all_goals grind (gen := 20) (instances := 20000) [lang_grind, arena_grind, crfW, crfV, crfLf,
    crfM, crfN, crfP1, crfP2, crfL1, crfL2, crfL3, crfB1, crfB2, crfFv, crfT, crfT1, crfT2]

theorem crff_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "consts_resolve_ffast" [vis, e]
    ⦃fun r s' => LocEq s' s₀ ∧ crffW p k s₀.mem vis e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.entry]
  simp only [callFn, constsResolveFFastL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k "crm_clear",
      callW_spec p k "crf_go"] <;>
    finish (gen := 20) [crffW, ntBW]

/-! ## The callees' meaning -/

section rel
variable {p : Prog} (hp : CrfProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include hp

theorem envFindW_01 {m m1 : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) :
    r.headD 0 = 0 ∨ r.headD 0 = 1 := by
  unfold envFindW at h
  split at h; · simp at h
  split at h; · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; simp
  split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; simp)

/-- **`env_find(w, vis)` as a call**: memory unchanged, and the word says whether `w` has a row in
the environment. -/
theorem envFind_callW {n : Nat} {m m' : Mem} {w : Word} {r : List Word}
    (hE : EnvR dn m vis fe) (hw : w.toNat < 2 ^ 32)
    (hc : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ r.headD 0 = if (fe.find? (decI w)).isSome then 1 else 0 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_specW p hp.eix hp.erg hp.ef n _ w vis) hc
  obtain ⟨hm, hf, hci⟩ := envFindW_found hW hE hw
  refine ⟨hm, ?_⟩
  rw [hf]
  simp only at hci
  rcases envFindW_01 hp hW with h0 | h1
  · rw [h0]; simp [decFound]
  · obtain ⟨ci, hci⟩ := hci (by rw [h1]; decide)
    rw [h1]
    simp only [decFound, ite_eq_right (show (1 : Word) ≠ 0 by decide), hci, Option.isSome_some,
      ↓reduceIte]

theorem ite_beq0 (c : Bool) : ((if c = true then (1 : Word) else 0) == 0) = !c := by
  cases c <;> rfl

/-- **`pin_found(vis, i)`**: memory unchanged, the flag set, `i < 51`, and the word says whether
pin `i`'s name has a row. -/
theorem pf_callW {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {a : AState}
    (hS : StageR dn vis fe m a) (hc : callW p n "pin_found" [vis, i] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ i.toNat < 51 ∧
      r.headD 0 = (if (fe.find? (decI (pinW m (1 + i.toNat)))).isSome then 1 else 0) ∧
      (r.headD 0 == 0) = !(fe.find? (decI (pinW m (1 + i.toNat)))).isSome := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hW := callW_model (M := fun mm => pfW p n mm vis i) (pf_spec p hp n · vis i) hc
  unfold pfW at hW
  cases h1 : callW p n "pin_at" [i] m with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨r1, m1⟩ := q
  rw [h1, bW_some] at hW
  obtain ⟨rfl, h0, hi, hr1⟩ := pinAt_model hp.pin h1 rfl
  cases h2 : callW p n "env_find" [r1.headD 0, vis] m1 with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨r2, m2⟩ := q
  rw [h2, bW_some, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  have hF := hS.1.pins.full h0
  have hlt := hF.names_lt _ hi
  rw [hr1] at h2
  obtain ⟨rfl, hv⟩ := envFind_callW hp hS.1.env hlt h2
  refine ⟨rfl, h0, hi, hv, ?_⟩
  show (r2.headD 0 == 0) = _
  rw [hv]; exact ite_beq0 hp _

/-- Whether every pin of `ks` has a row (the twin's `&&` of `isSome`s). -/
def pinsFound (fe : IFEnv) (m : Mem) (ks : List Word) : Bool :=
  ks.all fun k => (fe.find? (decI (pinW m (1 + k.toNat)))).isSome

/-- **`cr_lit_pins`' chain**: the memory unchanged, the flag set, and the answer is `0` iff a zero
was seen before or a pin of `k₀ :: ks` has no row. -/
theorem clpL_callW {n : Nat} {m : Mem} {a : AState} (hS : StageR dn vis fe m a) :
    ∀ (ks : List Word) (z : Bool) (k₀ : Word) (r : List Word) (m' : Mem),
    clpL p n vis z ks (callW p n "pin_found" [vis, k₀] m) = some (r, m') →
    m' = m ∧ pinW m 0 ≠ 0 ∧
      r = [if z || !pinsFound fe m (k₀ :: ks) then 0 else 1] := by
  intro ks
  induction ks with
  | nil =>
    intro z k₀ r m' h
    cases hc : callW p n "pin_found" [vis, k₀] m with
    | none => rw [hc, clpL_none] at h; cases h
    | some q =>
    obtain ⟨r0, m0⟩ := q
    rw [hc, clpL_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, h0, -, -, hz⟩ := pf_callW hp hS hc
    refine ⟨rfl, h0, ?_⟩
    simp only [pinsFound, List.all_cons, List.all_nil, Bool.and_true, hz]
  | cons k ks ih =>
    intro z k₀ r m' h
    cases hc : callW p n "pin_found" [vis, k₀] m with
    | none => rw [hc, clpL_none] at h; cases h
    | some q =>
    obtain ⟨r0, m0⟩ := q
    rw [hc, clpL_cons] at h
    obtain ⟨rfl, h0, -, -, hz⟩ := pf_callW hp hS hc
    obtain ⟨rfl, -, hr⟩ := ih _ k r m' h
    refine ⟨rfl, h0, ?_⟩
    rw [hr]
    simp only [pinsFound, List.all_cons, hz, Bool.not_and, Bool.or_assoc]

end rel

end L.Stubs
