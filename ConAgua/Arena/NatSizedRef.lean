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
sentinel (`≥ 2^63`) the twin's failure with the matching message. A handle word is below
`2^32`. -/
def NatRes (R : Mem → AState → Prop) (arm : AM (Option EIdx)) (a₀ : AState) (r : Word) (m' : Mem) :
    Prop :=
  (r.toNat < 2 ^ 63 → AM.ok arm a₀ ∧ R m' (AM.st arm a₀) ∧ AM.res arm a₀ = some (decE r) ∧
    r.toNat < 2 ^ 32) ∧
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
  have hlt32 : (h &&& 4294967295).toNat < 2 ^ 32 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hlt : (h &&& 4294967295).toNat < 2 ^ 63 := by omega
  have hrun' : arm.run a₀ = .ok (some (decE h), AM.st (internE (.lit (.natVal n))) a₀) := by
    rw [hrun, StateT.run_bind, AM.run_of_ok _ _ hok, hres]; rfl
  refine ⟨fun _ => ?_, fun h' => absurd h' (by omega)⟩
  simp only [AM.ok, AM.st, AM.res, hrun', decE_mask32]
  exact ⟨trivial, hR, trivial, hlt32⟩

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
    all_goals (try simp only [Cmp.eval, BinOp.eval,
      beq_iff_eq] at *)
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, Locals.init]
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
    all_goals (try simp only at *)
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, Locals.init, rdW, Cmp.evalW, Cmp.eval, UInt64.lt_iff_toNat_lt, L.St.setLocs_mem,
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
    all_goals (try simp only [Cmp.eval, BinOp.eval, bne_iff_ne, ne_eq] at *)
    all_goals simp only [St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, L.St.setLoc_mem,
      Locals.init_cons_zero, Locals.init_cons_succ, reduceIte] at *
    all_goals simp only [LocEq, Sig.retVal, Sig.retOr, List.headD_cons] at *
    all_goals first
      | (simp_all [Locals.init]; done)
      | (apply NatRes.refusedSize; rw [hrun, ite_eq_left]; apply Classical.byContradiction; intro hc; simp_all)
      | (refine NatRes.ofIntern (pv (vpool s₀.mem) o.toNat l.toNat) _ rfl ?_ ?_ ?_ ?_ <;> (try rw [hrun, ite_eq_right]) <;> simp_all [Locals.init])

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
      Locals.init_cons_zero, Locals.init_cons_succ, reduceIte] at *)
    all_goals grind [lang_grind, arena_grind, natAddArm, LocEq]

end refine

/-! ## The `pow` and `shiftLeft` guards -/

/-- The twin's `powRefused` condition, at a maximum `m`. -/
def powRefusedN (m a b : Nat) : Prop := ¬ a ≤ 1 ∧ b ≠ 0 ∧ m / b < 8 * (a.log2 / 64 + 1)

instance (m a b : Nat) : Decidable (powRefusedN m a b) := by unfold powRefusedN; infer_instance

/-- `powGuard` at the run's maximum: the exponent refusal, the size refusal, or nothing. -/
theorem powGuard_run (a b : Nat) (st : AState) :
    (ConRon.Arena.powGuard a b).run st =
      if 4294967295 < b then
        .error (.invalid "the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer")
      else if powRefusedN st.pins.maxNatSize a b then
        .error (.invalid "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size; raise it with --max-nat-size")
      else .ok ((), st) := by
  simp only [ConRon.Arena.powGuard, ConRon.Arena.powRefused, ConRon.Arena.natSizeBytes,
    ConRon.Arena.maxNatSizeM, powRefusedN]
  by_cases h1 : 4294967295 < b
  · simp [h1, StateT.run, ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
  by_cases h2 : a ≤ 1 <;> by_cases h3 : b = 0 <;>
    by_cases h4 : st.pins.maxNatSize / b < 8 * (a.log2 / 64 + 1) <;>
    simp [h1, h2, h3, h4, StateT.run, StateT.get, StateT.pure, StateT.bind, StateT.lift,
      ConRon.Arena.fail, throwThe, MonadExceptOf.throw, get, getThe, MonadStateOf.get, pure, bind,
      Except.bind, Except.pure] <;> rfl

/-- The twin's `shiftLeftRefused` condition, at a maximum `m`. -/
def shlRefusedN (m a b : Nat) : Prop := m < 8 * (a.log2 / 64 + 1) + b / 8 + 1

instance (m a b : Nat) : Decidable (shlRefusedN m a b) := by unfold shlRefusedN; infer_instance

/-- `shiftLeftGuard` at the run's maximum. -/
theorem shiftLeftGuard_run (a b : Nat) (st : AState) :
    (ConRon.Arena.shiftLeftGuard a b).run st =
      if a = 0 then .ok ((), st)
      else if 4294967295 < b then
        .error (.invalid "the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer")
      else if shlRefusedN st.pins.maxNatSize a b then
        .error (.invalid "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size")
      else .ok ((), st) := by
  simp only [ConRon.Arena.shiftLeftGuard, ConRon.Arena.shiftLeftRefused, ConRon.Arena.natSizeBytes,
    ConRon.Arena.maxNatSizeM, shlRefusedN]
  by_cases h0 : a = 0
  · simp [h0, StateT.run, StateT.pure, pure]; rfl
  by_cases h1 : 4294967295 < b
  · simp [h0, h1, StateT.run, ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.lift]; rfl
  by_cases h4 : st.pins.maxNatSize < 8 * (a.log2 / 64 + 1) + b / 2 ^ 3 + 1 <;>
    simp [h0, h1, h4, Nat.shiftRight_eq_div_pow, StateT.run, StateT.get, StateT.pure, StateT.bind, StateT.lift,
      ConRon.Arena.fail, throwThe, MonadExceptOf.throw, get, getThe, MonadStateOf.get, pure, bind,
      Except.bind, Except.pure] <;> rfl

/-- `pow_refused`'s condition on the words it reads: a base that is not `0` or the one limb `1`,
a nonzero exponent, and the maximum below `8 · max(la, 1) · e`. -/
def powRefusedW (m : Word) (la x e : Word) : Prop :=
  la ≠ 0 ∧ ¬ (la = 1 ∧ x = 1) ∧ e ≠ 0 ∧ m.toNat < 8 * max la.toNat 1 * e.toNat

instance (m la x e : Word) : Decidable (powRefusedW m la x e) := by unfold powRefusedW; infer_instance

/-- The high word of a product is nonzero exactly when the product reaches `2^64`. -/
theorem mulhi_ne_zero (a b : Word) :
    UInt64.ofNat (a.toNat * b.toNat / 2 ^ 64) ≠ 0 ↔ 2 ^ 64 ≤ a.toNat * b.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  have hq : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    exact Nat.mul_lt_mul_of_lt_of_lt ha hb
  constructor
  · intro h
    apply Classical.byContradiction; intro hc
    apply h; rw [Nat.div_eq_of_lt (by omega)]; rfl
  · intro h e
    have h1 : 1 ≤ a.toNat * b.toNat / 2 ^ 64 :=
      (Nat.le_div_iff_mul_le (by decide)).mpr (by rw [Nat.one_mul]; exact h)
    have h2 : (UInt64.ofNat (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat / 2 ^ 64 :=
      UInt64.toNat_ofNat_of_lt' hq
    rw [e, UInt64.toNat_zero] at h2
    omega

theorem rdW_prd (m : Mem) (x : Word) :
    rdW (m.arr64 (tierA POOL (x >>> 40))) (x &&& 1099511627775) = prd m x := rfl

/-- An in-bounds read is `rdW`. -/
private theorem getElem_rdW (a : Array Word) (i : Word) (h : i.toNat < a.size) : a[i.toNat] = rdW a i := by
  simp [rdW, h]

theorem powW_big {m la x e s : Word} (hla : la ≠ 0) (hx : ¬ (la = 1 ∧ x = 1)) (he : e ≠ 0)
    (hs : s.toNat = 8 * max la.toNat 1) (hmh : 2 ^ 64 ≤ s.toNat * e.toNat) :
    powRefusedW m la x e := by
  refine ⟨hla, hx, he, ?_⟩
  have := m.toNat_lt; rw [hs] at hmh; omega

theorem powW_small {m la x e s : Word} (hla : la ≠ 0) (hx : ¬ (la = 1 ∧ x = 1)) (he : e ≠ 0)
    (hs : s.toNat = 8 * max la.toNat 1) (hlt : s.toNat * e.toNat < 2 ^ 64) :
    (m < s * e) = powRefusedW m la x e := by
  apply propext
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mul, Nat.mod_eq_of_lt hlt, hs]
  exact ⟨fun h => ⟨hla, hx, he, h⟩, fun h => h.2.2.2⟩

/-- `pow_refused`'s refusal by the high word of `s · e`. -/
theorem powW_one {m la x e s : Word} (hla : ¬ la = 0) (hx : ¬ (la = 1 ∧ x = 1)) (he : ¬ e = 0)
    (hs : s.toNat = 8 * max la.toNat 1) (hmh : ¬ UInt64.ofNat (s.toNat * e.toNat / 2 ^ 64) = 0) :
    (1 : Word) = if powRefusedW m la x e then 1 else 0 := by
  rw [ite_eq_left (powW_big hla hx he hs ((mulhi_ne_zero s e).mp hmh))]

/-- `pow_refused`'s comparison when `s · e` fits in a word. -/
theorem powW_lt {m la x e s : Word} (hla : ¬ la = 0) (hx : ¬ (la = 1 ∧ x = 1)) (he : ¬ e = 0)
    (hs : s.toNat = 8 * max la.toNat 1) (hmh : ¬ ¬ UInt64.ofNat (s.toNat * e.toNat / 2 ^ 64) = 0) :
    (if m < s * e then (1 : Word) else 0) = if powRefusedW m la x e then 1 else 0 := by
  have hlt : s.toNat * e.toNat < 2 ^ 64 := by
    have : ¬ 2 ^ 64 ≤ s.toNat * e.toNat := fun h => hmh ((mulhi_ne_zero s e).mpr h)
    omega
  have hq := powW_small (m := m) hla hx he hs hlt
  by_cases h : m < s * e
  · have h' : powRefusedW m la x e := hq ▸ h
    simp [h, h']
  · have h' : ¬ powRefusedW m la x e := hq ▸ h
    simp [h, h']

/-- `shift_left_refused`'s comparison: no word wraps (`la < 2^41`, a pool slice). -/
theorem shlW_cmp (m s e la : Word) (hs : s.toNat = 8 * max la.toNat 1) (hl : la.toNat < 2 ^ 41) :
    (if m < s + (e >>> 3) + 1 then (1 : Word) else 0) =
      if m.toNat < 8 * max la.toNat 1 + e.toNat / 8 + 1 then 1 else 0 := by
  have he : (e >>> 3).toNat = e.toNat / 8 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have h3 : e.toNat / 8 < 2 ^ 61 := by have := e.toNat_lt; omega
  have hmx : max la.toNat 1 < 2 ^ 41 := Nat.max_lt.mpr ⟨hl, by decide⟩
  have hsum : (s + (e >>> 3) + 1).toNat = 8 * max la.toNat 1 + e.toNat / 8 + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, he, hs]; simp only [UInt64.toNat_one]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  by_cases h : m.toNat < 8 * max la.toNat 1 + e.toNat / 8 + 1
  · rw [ite_eq_left h, ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hsum]; exact h)]
  · rw [ite_eq_right h, ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hsum]; exact h)]

/-- **`pow_refused`**: its condition `powRefusedW` at the maximum `PINS[72]` and the base's limb
`x` (where `la = 1`). -/
theorem powRefused_spec (p : Prog) (hz : p.lookup "size_bytes" = some sizeBytesL)
    (hp : p.lookup "pow_refused" = some powRefusedL) (n : Nat) (s₀ : St) (oa la e : Word)
    (hok : PoolOK s₀.mem) (ha : SliceOK s₀.mem oa la) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pow_refused" [oa, la, e]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 = if powRefusedW (rdW (s₀.mem.arr64 PINS) 72) la (prd s₀.mem oa) e then 1 else 0);
      ⊤⦄ := by
  have hl : la.toNat < 2 ^ 61 := by have := hok.top41; simp only [SliceOK] at ha; omega
  have h41 := hok.top41
  have hoa : oa.toNat < 2 ^ 41 := by simp only [SliceOK] at ha; omega
  rw [invoke_eq _ hp]
  simp only [callFn, powRefusedL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, sizeBytes_spec p hz n]
    all_goals (try simp only [Cmp.eval, BinOp.eval,
      beq_iff_eq, bne_iff_ne, ne_eq, LocEq, Sig.retVal, Sig.retOr] at *)
    all_goals (try simp only [Locals.init_cons_zero, Locals.init_cons_succ, St.setLocs_cons,
      St.setLocs_nil, St.setLoc_loc, L.St.setLoc_mem, List.headD_cons, Cmp.evalW] at *)
    all_goals subst_vars
    all_goals (try simp (disch := assumption) only [getElem_rdW, Cmp.eval, ite_true, reduceIte,
      Nat.reduceEqDiff, decide_eq_true_eq, rdW_prd] at *)
    all_goals first
      | grind [arena_grind, vpool_ld, powRefusedW, Sig.retVal, mulhi_ne_zero, Locals.init, List.getD_cons_zero, List.getD_cons_succ]
      | (obtain ⟨hloc, hmem, hs⟩ : _ ∧ _ ∧ (_ : Word).toNat = 8 * max _ 1 := by assumption
         simp only [hloc, hmem, Locals.init_cons_zero, Locals.init_cons_succ] at *
         first
          | (refine powW_one ?_ ?_ ?_ hs ?_ <;> first | assumption | (intro h; simp_all))
          | (refine powW_lt ?_ ?_ ?_ hs ?_ <;> first | assumption | (intro h; simp_all)))

/-- **`shift_left_refused`**: the twin's `shiftLeftRefused` at the maximum `PINS[72]`, for a
normalised base. -/
theorem shiftLeftRefused_spec (p : Prog) (hz : p.lookup "size_bytes" = some sizeBytesL)
    (hp : p.lookup "shift_left_refused" = some shiftLeftRefusedL) (n : Nat) (s₀ : St) (la e : Word)
    (hl : la.toNat < 2 ^ 41) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "shift_left_refused" [la, e]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 = if (rdW (s₀.mem.arr64 PINS) 72).toNat < 8 * max la.toNat 1 + e.toNat / 8 + 1
        then 1 else 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, shiftLeftRefusedL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, sizeBytes_spec p hz n]
    all_goals (try simp only [BinOp.eval] at *)
    case vc3 _ _ s₂ hA hb =>
      obtain ⟨hloc, hmem, hs⟩ := hA
      have hl1 : (s₂.setLocs [2] rs).loc 1 = e := by
        simp only [St.setLocs_cons, St.setLocs_nil, St.setLoc_loc, LocEq] at hloc ⊢
        rw [hloc]; rfl
      have hl2 : (s₂.setLocs [2] rs).loc 2 = rs.headD 0 := by
        simp only [St.setLocs_cons, St.setLocs_nil, St.setLoc_loc]; rfl
      have hm : (s₂.setLocs [2] rs).mem = s₀.mem := by
        simp only [St.setLocs_cons, St.setLocs_nil, L.St.setLoc_mem]; exact hmem
      simp only [Locals.init_cons_zero] at hs
      simp only [hl1, hl2, hm, Sig.retVal, Sig.retOr, List.headD_cons, Cmp.evalW, Cmp.eval] at hb ⊢
      rw [getElem_rdW _ _ hb]
      simp only [decide_eq_true_eq]
      exact shlW_cmp _ _ _ _ hs hl
    all_goals simp_all [LocEq, Locals.init, L.St.setLocs_mem,
      List.headD_eq_head?_getD]
    all_goals omega

end L.Arena
