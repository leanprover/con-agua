module

public import ConAgua.Arena.Refine
public import ConAgua.Arena.NatSized
public import ConAgua.Arena.SlotGrow
public import ConRon.Arena.Core
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.NatSized
import all ConAgua.Arena.Refine

@[expose] public section

/-!
# The size refusal and the `Nat.add` arm

`lit_nat_sized` against the twin's `litNatSized` (the run's maximum `Nat` size, `PINS[72]`), and
`nat_add_lit` against `natOpResult`'s `Nat.add` arm, `litNatSized (a + b)`. An arm that may refuse
is refined by `NatRes`: a handle word is the twin's `some`, a sentinel (`NatSized.lean`) the twin's
failure with the matching message.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open ConRon.Arena (AM AState EIdx ENodeView internE)

namespace L.Arena

/-- The `Nat.add` arm of `natOpResult` (`Arena/Core.lean`), verbatim: the sum, refused above the
run's maximum `Nat` size. -/
def natAddArm (a b : Nat) : AM (Option EIdx) := ConRon.Arena.litNatSized (a + b)

/-- The twin's error of a refused `Nat` computation, by the L sentinel (`NatSized.lean`). -/
def natRefusal (r : Word) : ConRon.Arena.CheckError :=
  if r = natRefusedPowExp then
    .invalid "the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer"
  else if r = natRefusedPowSize then
    .invalid "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size; raise it with --max-nat-size"
  else if r = natRefusedShlExp then
    .invalid "the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer"
  else
    .invalid "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size"

/-- **The outcome of an arm that may refuse**: a handle word (`< 2^63`) is the twin's `some`, a
sentinel (`≥ 2^63`) the twin's failure with the matching message. -/
def NatRes (R : Mem → AState → Prop) (arm : AM (Option EIdx)) (a₀ : AState) (r : Word) (m' : Mem) :
    Prop :=
  (r.toNat < 2 ^ 63 → AM.ok arm a₀ ∧ R m' (AM.st arm a₀) ∧ AM.res arm a₀ = some (decE r)) ∧
  (2 ^ 63 ≤ r.toNat → arm.run a₀ = .error (natRefusal r))

/-- `litNatSized` at the run's maximum: the refusal, or the intern. -/
theorem litNatSized_run (n : Nat) (a : AState) :
    (ConRon.Arena.litNatSized n).run a =
      if a.pins.maxNatSize < 8 * (n.log2 / 64 + 1) then
        .error (.invalid "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size")
      else (do let x ← internE (.lit (.natVal n)); pure (some x) : AM (Option EIdx)).run a := by
  simp only [ConRon.Arena.litNatSized, ConRon.Arena.natSizeRefused, ConRon.Arena.natSizeBytes,
    ConRon.Arena.maxNatSizeM, StateT.run_bind]
  by_cases h : a.pins.maxNatSize < 8 * (n.log2 / 64 + 1) <;>
    simp [h, StateT.run, StateT.get, StateT.pure, StateT.bind, StateT.lift, ConRon.Arena.fail, throwThe,
      MonadExceptOf.throw, get, getThe, MonadStateOf.get, pure, bind, Except.bind, Except.pure] <;> rfl

/-- A handle word masked to its 32 bits decodes as itself. -/
theorem decE_mask32 (y : Word) : decE (y &&& 4294967295) = decE y := by
  simp only [decE]; congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_and]
  rw [show (4294967295 : Word).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

/-- A refused numeral: the sentinel `natRefusedSize`. -/
theorem NatRes.refusedSize {R : Mem → AState → Prop} {arm : AM (Option EIdx)} {a₀ : AState}
    {m' : Mem} (h : arm.run a₀ = .error (.invalid
      "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size")) :
    NatRes R arm a₀ natRefusedSize m' :=
  ⟨fun h' => absurd h' (by decide), fun _ => by rw [h]; rfl⟩

/-- An interned numeral: a masked handle word, the intern's run. -/
theorem NatRes.ofIntern {R : Mem → AState → Prop} {arm : AM (Option EIdx)} {a₀ : AState}
    {m' : Mem} {r : Word} (n : Nat) (h : Word) (hr : r = h &&& 4294967295)
    (hrun : arm.run a₀ = (do let x ← internE (.lit (.natVal n)); pure (some x) : AM (Option EIdx)).run a₀)
    (hok : AM.ok (internE (.lit (.natVal n))) a₀) (hR : R m' (AM.st (internE (.lit (.natVal n))) a₀))
    (hres : AM.res (internE (.lit (.natVal n))) a₀ = decE h) :
    NatRes R arm a₀ r m' := by
  subst hr
  have hlt : (h &&& 4294967295).toNat < 2 ^ 63 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hrun' : arm.run a₀ = .ok (some (decE h), AM.st (internE (.lit (.natVal n))) a₀) := by
    rw [hrun, StateT.run_bind, AM.run_of_ok _ _ hok, hres]; rfl
  refine ⟨fun _ => ?_, fun h' => absurd h' (by omega)⟩
  simp only [AM.ok, AM.st, AM.res, hrun', decE_mask32]
  exact ⟨trivial, hR, trivial⟩

/-- **`size_bytes`**: `8 · max(l, 1)` for a limb count below `2^61`. -/
theorem sizeBytes_spec (p : Prog) (hp : p.lookup "size_bytes" = some sizeBytesL) (n : Nat) (s₀ : St)
    (l : Word) (hl : l.toNat < 2 ^ 61) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "size_bytes" [l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ (r.headD 0).toNat = 8 * max l.toNat 1; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, sizeBytesL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, reduceIte,
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, Locals.init, List.getD_cons_zero,
      List.getD_cons_succ]
    all_goals grind

/-- **`nat_size_refused`**: the maximum `PINS[72]` is below `8 · max(l, 1)`. -/
theorem natSizeRefused_spec (p : Prog) (hz : p.lookup "size_bytes" = some sizeBytesL)
    (hp : p.lookup "nat_size_refused" = some natSizeRefusedL) (n : Nat) (s₀ : St)
    (l : Word) (hl : l.toNat < 2 ^ 61) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nat_size_refused" [l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 = if (rdW (s₀.mem.arr64 PINS) 72).toNat < 8 * max l.toNat 1 then 1 else 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natSizeRefusedL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, sizeBytes_spec p hz n]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, reduceIte,
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, Locals.init, List.getD_cons_zero,
      List.getD_cons_succ, rdW, Cmp.evalW, Cmp.eval, UInt64.lt_iff_toNat_lt, L.St.setLocs_mem,
      List.headD_eq_head?_getD]
    all_goals grind

section refine
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpa : p.lookup "nat_add" = some natAdd) (hpn : p.lookup "nat_add_lit" = some natAddLit)
  (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m)
  (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  /- The spec of `intern_lit` that milestone 4 proves: interning the slice `(o, l)` is the
  arena's `internE` of the literal the slice denotes. -/
  (hI : ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
    (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      R s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ = decE (r.headD 0); ⊤⦄)

variable (hz : p.lookup "size_bytes" = some sizeBytesL)
  (hsr : p.lookup "nat_size_refused" = some natSizeRefusedL)
  (hls : p.lookup "lit_nat_sized" = some litNatSizedL)

include hz hsr hls hpool hI in
/-- **`lit_nat_sized` refines `litNatSized`**: the sentinel where the twin refuses the numeral
(the maximum is `PINS[72]`), else the intern's handle, masked. -/
@[refines ConRon.Arena.litNatSized]
theorem litNatSized_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (hmx : (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize)
    (o l : Word) (hs : SliceOK s₀.mem o l) (hn : Norm (vpool s₀.mem) o.toNat l.toNat)
    (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lit_nat_sized" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatRes R (ConRon.Arena.litNatSized (pv (vpool s₀.mem) o.toNat l.toNat)) a₀ (r.headD 0) s'.mem;
      ⊤⦄ := by
  have hok := hpool _ _ hR
  have hl : l.toNat < 2 ^ 61 := by have := hok.top41; simp only [SliceOK] at hs; omega
  have hsz := sizeBytes_pv (vpool s₀.mem) o.toNat l.toNat hn
  have hrun := litNatSized_run (pv (vpool s₀.mem) o.toNat l.toNat) a₀
  rw [hsz, ← hmx] at hrun
  rw [invoke_eq _ hls]
  simp only [callFn, litNatSizedL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, natSizeRefused_spec p hz hsr n,
      hI a₀ n]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval, reduceIte,
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals simp only [St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, L.St.setLoc_mem,
      List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals simp only [LocEq, Sig.retVal, Sig.retOr, List.headD_cons] at *
    all_goals first
      | (simp_all [Locals.init, List.getD_cons_zero, List.getD_cons_succ]; done)
      | (apply NatRes.refusedSize; rw [hrun, ite_eq_left]; apply Classical.byContradiction; intro hc; simp_all)
      | (refine NatRes.ofIntern (pv (vpool s₀.mem) o.toNat l.toNat) _ rfl ?_ ?_ ?_ ?_ <;> (try rw [hrun, ite_eq_right]) <;> simp_all [Locals.init, List.getD_cons_zero, List.getD_cons_succ])

include hpl hpc hpt hpa hpn hz hsr hls hpool hgrow hI in
/-- **`nat_add_lit` refines `natOpResult`'s `Nat.add` arm** (`litNatSized (a + b)`): a handle word
where the arena arm interns the sum, the sentinel where it refuses it (`NatRes`). -/
@[refines_part ConRon.Arena.natOpResult "Nat.add"]
theorem natAddLit_refines (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (hmx : (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_add_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatRes R (natAddArm (pv (vpool s₀.mem) oa.toNat la.toNat) (pv (vpool s₀.mem) ob.toNat lb.toNat))
        a₀ (r.headD 0) s'.mem; ⊤⦄ := by
  have hok := hpool _ _ hR
  have hm0 : s₀.mem.flag = 0 → s₀.mem.top.toNat < 2 ^ 40 := fun hf => by
    rcases hmode with h | h
    · exact absurd hf h
    · exact h
  rw [invoke_eq _ hpn]
  simp only [callFn, natAddLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, ld64, natAdd_spec p hpl hpc hpt hpa n,
      litNatSized_refines p R hpool hI hz hsr hls n (a₀ := a₀)]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons, St.setLocs_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, reduceIte] at *)
    all_goals (first | grind [lang_grind, arena_grind, natAddArm, LocEq] | (trace_state; sorry))

end refine

end L.Arena
