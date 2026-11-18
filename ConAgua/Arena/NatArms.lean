module

public import ConAgua.Arena.Tiers
public import ConRon.Arena.Core
public import ConAgua.Arena.NatGcd
public import ConAgua.Arena.NatCmp
import ConAgua.Arena.NatBitsNat
public import ConAgua.Arena.NatPow
public import ConAgua.Arena.NatPowNat
public import ConAgua.Arena.NatSizedRef
public import ConAgua.Arena.NatShr
public import ConAgua.Arena.NatShl
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
meta import ConAgua.Arena.Tiers
meta import ConAgua.Arena.NatGcd
meta import ConAgua.Arena.NatCmp
meta import ConAgua.Arena.NatBitsNat
meta import ConAgua.Arena.NatPow
meta import ConAgua.Arena.NatShr
meta import ConAgua.Arena.NatShl
meta import ConAgua.Arena.GrindAttr
meta import ConAgua.Arena.NatGrindAttr
meta import ConAgua.L.GrindAttr
meta import Std.Tactic.BVDecide.Normalize.BitVec
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.ArenaRel
public import ConAgua.Arena.NatBits

@[expose] public section

/-!
# The `Nat` arms of `natBinOpResult`, refined under `ArenaR`

`natBinOpResult` (`vendor/con-ron/ConRon/Arena/Core.lean`) runs one arm per operation; an arm with a literal result is
`do let x ← internE (.lit (.natVal (F a b))); pure (some x)` (`litArm F`). `natAddArm`
(`Refine.lean`) is the `+` arm; this file does the others, following `natAddLit_refines`:

* **One generic theorem for the arms whose pool function appends at the top**
  (`topLit_refines`): an L wrapper `topLit f` (`o := CTL[0]; l := call f(…); h :=
  call intern_lit(o, l); return h`) refines `litArm F`, given `f`'s spec in the shape of
  `natAdd_spec` (`TopSpec p f F`: the result at the old top denotes `F a b`, normalised, the pool
  grew). Instances: `-`, `*`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`; `pred` (`natLitToConstructor`'s `n - 1`) is `-` with
  a one-limb `1` written at the top first.
* **The arms whose pool function returns a slice**: `pow` (with con-leche's exponent bound,
  `none` above `2^24`), `/` and `%` (`nat_divmod`'s two slices).
* Under `ArenaR`, as `natAddLit_arms` (`PinsNatOp.lean`).

The arms are stated over their arguments; the pin reads before them are not modelled (lane `nat2`
in DESIGN.md: one toolchain's pin set). The operands are normalised slices (as every `lit`
record's slice is), which `nat_shr` and `nat_divmod` need for `b`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The generic arm -/

/-- The arm of `natBinOpResult` with the literal result `F a b`. -/
def litArm (F : Nat → Nat → Nat) (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (F a b)))
  pure (some x)

/-- `natAddLit` with `f` for `nat_add`: `o := CTL[0]; l := call f(oa, la, ob, lb);
h := call intern_lit(o, l); return h`. -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
@[no_expose] def topLit (f : FnName) : FunDecl :=
  ⟨4, 7, .seq (.set 4 (.ld64 CTL (.const 0)))
    (.seq (.call [5] f [.var 0, .var 1, .var 2, .var 3])
      (.seq (.call [6] "intern_lit" [.var 4, .var 5]) (.ret [.var 6])))⟩

/-- `topLit` with the size refusal (`lit_nat_sized`) in place of `intern_lit`: the `sub` and `mul`
arms (`litNatSized (a - b)`, `litNatSized (a * b)`). -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
-- con-ron: ConRon/Arena/Core.lean:1093-1103 ConRon.Arena.litNatSized
@[no_expose, l_impl ConRon.Arena.natBinOpResult ConRon.Arena.litNatSized] def topLitS (f : FnName) : FunDecl :=
  ⟨4, 7, .seq (.set 4 (.ld64 CTL (.const 0)))
    (.seq (.call [5] f [.var 0, .var 1, .var 2, .var 3])
      (.seq (.call [6] "lit_nat_sized" [.var 4, .var 5]) (.ret [.var 6])))⟩

/-- The spec of a pool function that appends `F a b` at the top (`natAdd_spec`'s shape), for
normalised operands. -/
def TopSpec (p : Prog) (f : FnName) (F : Nat → Nat → Nat) : Prop :=
  ∀ (n : Nat) (s₀ : St) (oa la ob lb : Word), PoolOK s₀.mem → SliceOK s₀.mem oa la →
    SliceOK s₀.mem ob lb → Norm (vpool s₀.mem) oa.toNat la.toNat →
    Norm (vpool s₀.mem) ob.toNat lb.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        F (pv (vpool s₀.mem) oa.toNat la.toNat) (pv (vpool s₀.mem) ob.toNat lb.toNat) ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄

/-- `intern_lit`'s spec under a state relation `R` (`natAddLit_refines`'s `hI`). -/
def InternSpec (p : Prog) (R : Mem → AState → Prop) : Prop :=
  ∀ (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word), R s₀.mem a₀ →
    SliceOK s₀.mem o l → Norm (vpool s₀.mem) o.toNat l.toNat →
    (s₀.mem.flag = 0 → o.toNat < 2 ^ 40) →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      R s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0); ⊤⦄

/-! ## The mode across a pool function -/

theorem Grows.flag {m m' : Mem} (hg : Grows m m') : m'.flag = m.flag := by
  rw [hg.frame.flag, Mem.flag_set64_top]
grind_pattern [arena_grind] Grows.flag => Grows m m', m'.flag

/-- A pool function keeps the mode: the top stays in tier 0 while the flag is `0`. -/
theorem ModeOK.grows {m m' : Mem} (h : ModeOK m) (hg : Grows m m') : ModeOK m' := by
  rcases h with h | h
  · exact Or.inl (by rw [hg.flag]; exact h)
  · have := hg.tier
    exact Or.inr (by omega)
grind_pattern [arena_grind] ModeOK.grows => Grows m m', ModeOK m'

/-- What `intern_lit` needs of a slice a pool function returned, under the mode at entry. -/
theorem Grows.slice0 {m m' : Mem} {o l : Word} (h : ModeOK m) (hg : Grows m m')
    (hs : SliceOK m' o l) : m'.flag = 0 → o.toNat < 2 ^ 40 :=
  (h.grows hg).slice0 hs
grind_pattern [arena_grind] Grows.slice0 => Grows m m', SliceOK m' o l

/-- The top after a pool function, under the mode at entry (keyed on the flag, for a slice
at the old top). -/
theorem Grows.top0 {m m' : Mem} (h : ModeOK m) (hg : Grows m m') :
    m.top.toNat ≤ m'.top.toNat ∧ (m'.flag = 0 → m'.top.toNat < 2 ^ 40) :=
  ⟨hg.le, fun hf => by
    rcases h.grows hg with h | h
    · exact absurd hf h
    · exact h⟩
grind_pattern [arena_grind] Grows.top0 => Grows m m', m'.flag

section generic
variable (p : Prog) (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m) (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : InternSpec p R)

include hpool hgrow hI in
/-- **`topLit f` refines `litArm F`** whenever `f` appends `F a b` at the top. -/
theorem topLit_refines (g f : FnName) (F : Nat → Nat → Nat) (hg : p.lookup g = some (topLit f))
    (hF : TopSpec p f F) (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) g [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (litArm F (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (litArm F (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (litArm F (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ := by
  have hok := hpool _ _ hR
  rw [invoke_eq _ hg]
  simp only [callFn, topLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalArgs, setLoc, setLocs, ld64, hF n, hI a₀ n] <;>
      finish [litArm]

variable (hz : p.lookup "size_bytes" = some sizeBytesL)
  (hsr : p.lookup "nat_size_refused" = some natSizeRefusedL)
  (hls : p.lookup "lit_nat_sized" = some litNatSizedL)

include hpool hgrow hI hz hsr hls in
/-- **`topLitS f` refines `litNatSized (F a b)`** whenever `f` appends `F a b` at the top: the
handle, or the size refusal's sentinel (`NatRes`). -/
theorem topLitS_refines (g f : FnName) (F : Nat → Nat → Nat) (hg : p.lookup g = some (topLitS f))
    (hF : TopSpec p f F) (n : Nat) (s₀ : St) (a₀ : AState) (hR : R s₀.mem a₀)
    (hmx : (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) g [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatRes R (ConRon.Arena.litNatSized (F (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat))) a₀ (r.headD 0) s'.mem; ⊤⦄ := by
  have hok := hpool _ _ hR
  rw [invoke_eq _ hg]
  simp only [callFn, topLitS]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalArgs, setLoc, setLocs, ld64, hF n,
      litNatSized_refines p R hpool hI hz hsr hls n (a₀ := a₀)]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons, St.setLocs_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, reduceIte] at *)
    all_goals grind [lang_grind, arena_grind, LocEq]

end generic

/-! ## The arms with a slice result: `/`, `%` -/

/-- `nat_div_lit(oa, la, ob, lb)`: the quotient slice of `nat_divmod`, interned. -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natDivLit : FunDecl := lfn (oa, la, ob, lb) locals (o, l, h) {
  (o, l) := call nat_divmod(oa, la, ob, lb);
  h := call intern_lit(o, l);
  return h
}

/-- `nat_mod_lit(oa, la, ob, lb)`: the remainder slice of `nat_divmod`, interned. -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natModLit : FunDecl := lfn (oa, la, ob, lb) locals (q, ql, o, l, h) {
  (q, ql, o, l) := call nat_divmod(oa, la, ob, lb);
  h := call intern_lit(o, l);
  return h
}

section divmod
variable (p : Prog) (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m) (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : InternSpec p R)
  (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpc : p.lookup "add_carry" = some addCarry)
  (hp1 : p.lookup "div_shl1" = some divShl1) (hp2 : p.lookup "div_sub" = some divSub)
  (hp3 : p.lookup "div_add" = some divAdd) (hp4 : p.lookup "div_step" = some divStep)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpd : p.lookup "nat_divmod" = some natDivmod)

include hpool hgrow hI hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd in
theorem natDivLit_refines (hg : p.lookup "nat_div_lit" = some natDivLit) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀) (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la)
    (hb : SliceOK s₀.mem ob lb) (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat)
    (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_div_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (litArm (· / ·) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (litArm (· / ·) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (litArm (· / ·) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ := by
  have hok := hpool _ _ hR
  rw [invoke_eq _ hg]
  simp only [callFn, natDivLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalArgs, setLoc, setLocs,
        natDivmod_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd n, hI a₀ n] <;>
      finish [litArm]

include hpool hgrow hI hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd in
theorem natModLit_refines (hg : p.lookup "nat_mod_lit" = some natModLit) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀) (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la)
    (hb : SliceOK s₀.mem ob lb) (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat)
    (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_mod_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (litArm (· % ·) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (litArm (· % ·) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (litArm (· % ·) (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ := by
  have hok := hpool _ _ hR
  rw [invoke_eq _ hg]
  simp only [callFn, natModLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalArgs, setLoc, setLocs,
        natDivmod_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd n, hI a₀ n] <;>
      finish [litArm]

end divmod

/-! ## `pred`: `-` with a one-limb `1` -/

/-- `nat_pred_lit(oa, la)`: write the limb `1` at the top, subtract it, intern the result. -/
-- con-ron: ConRon/Arena/Core.lean:551-562 ConRon.Arena.natLitToConstructor
@[no_expose, l_impl ConRon.Arena.natLitToConstructor]
def natPredLit : FunDecl := lfn (oa, la) locals (o, l, h, pt, pb) {
  o := CTL.u64[0];
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  if len(POOL⟨pt⟩) <= pb { abort };
  POOL⟨pt⟩[pb] := 1;
  CTL.u64[0] := o + 1;
  l := call nat_sub(oa, la, o, 1);
  h := call intern_lit(o + 1, l);
  return h
}

/-- The `Nat.pred` arm (`Arena/Core.lean:1004`), verbatim. -/
def natPredArm (a : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (a - 1))); pure (some x)

section pred
variable (p : Prog) (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m) (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : InternSpec p R)
  (hpl : p.lookup "nat_limb" = some natLimb) (hps : p.lookup "sub_borrow" = some subBorrow)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_sub" = some natSub)

include hpool hgrow hI hpl hps hpt hpn in
theorem natPredLit_refines (hg : p.lookup "nat_pred_lit" = some natPredLit) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀) (oa la : Word) (ha : SliceOK s₀.mem oa la)
    (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_pred_lit" [oa, la]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀ ∧
      R s'.mem (AM.st (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀) ∧
      AM.res (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀ =
        some (decE (r.headD 0)); ⊤⦄ := by
  have hok := hpool _ _ hR
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  rw [invoke_eq _ hg]
  simp only [callFn, natPredLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      natSub_spec p hpl hps hpt hpn n, hI a₀ n]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, natop_grind, natPredArm]

end pred

/-! ## `pow`, behind the guard -/

/-- `nat_pow_lit(oa, la, ob, lb)`: the cited `Nat.pow` clause's guard (`powGuard`: an exponent
above `2^32 - 1` refused whatever the base, the sentinel `natRefusedPowExp`; a result above the
maximum, `pow_refused`, `natRefusedPowSize`; `NatSized.lean`), then the power (`pow_nat`), interned. An
exponent of two or more limbs is at least `2^64` (`b` normalised). -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
-- con-ron: ConRon/Arena/Core.lean:1114-1124 ConRon.Arena.powGuard
@[no_expose, l_impl ConRon.Arena.natBinOpResult ConRon.Arena.powGuard]
def natPowLit : FunDecl := lfn (oa, la, ob, lb) locals (e, r, o, l, h) {
  if 1 < lb { return 9223372036854775810 };
  if lb == 1 { e := POOL⦃ob⦄ };
  if 4294967295 < e { return 9223372036854775810 };
  r := call pow_refused(oa, la, e);
  if r != 0 { return 9223372036854775811 };
  (o, l) := call pow_nat(oa, la, e);
  h := call intern_lit(o, l);
  return h & 4294967295
}

/-- `nat_shl_lit(oa, la, ob, lb)`: the cited `Nat.shiftLeft` clause's guard (`shiftLeftGuard`:
`0 <<< b` computes; an amount above `2^32 - 1` is refused, the sentinel `natRefusedShlExp`; a
result above the maximum, `shift_left_refused`, `natRefusedSize`), then the shift. -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
-- con-ron: ConRon/Arena/Core.lean:1132-1142 ConRon.Arena.shiftLeftGuard
@[no_expose, l_impl ConRon.Arena.natBinOpResult ConRon.Arena.shiftLeftGuard]
def natShlLit : FunDecl := lfn (oa, la, ob, lb) locals (e, r, o, l, h) {
  if la != 0 {
    if 1 < lb { return 9223372036854775812 };
    if lb == 1 { e := POOL⦃ob⦄ };
    if 4294967295 < e { return 9223372036854775812 };
    r := call shift_left_refused(la, e);
    if r != 0 { return 9223372036854775809 }
  };
  o := CTL.u64[0];
  l := call nat_shl(oa, la, ob, lb);
  h := call intern_lit(o, l);
  return h & 4294967295
}

/-- The `Nat.pow` arm (`Arena/Core.lean:1008-1012`), verbatim. -/
def natPowArm (a b : Nat) : AM (Option EIdx) := do
  ConRon.Arena.powGuard a b
  let x ← internE (.lit (.natVal (a ^ b))); pure (some x)

/-- An optional handle as two words: a flag and the handle. -/
def decOpt (f h : Word) : Option EIdx := if f = 0 then none else some (decE h)

@[arena_grind =] theorem decOpt_zero (h : Word) : decOpt 0 h = none := rfl
theorem decOpt_ne (f h : Word) (hf : f ≠ 0) : decOpt f h = some (decE h) := by
  simp [decOpt, hf]
grind_pattern [arena_grind] decOpt_ne => decOpt f h

/-- A normalised slice of two or more limbs is at least `2^64`. -/
theorem pv_two_limbs (p : Array Word) (o l : Nat) (hn : Norm p o l) (hl : 2 ≤ l) :
    2 ^ 64 ≤ pv p o l := by
  have := pv_ge_wt p o l (by omega) hn
  have : wt 1 ≤ wt (l - 1) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega))
  have : wt 1 = 2 ^ 64 := rfl
  omega

section pow
variable (p : Prog) (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m) (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : InternSpec p R)
  (hph : p.lookup "mac_hi" = some macHi) (hpt : p.lookup "nat_trim" = some natTrim)
  (hpm : p.lookup "nat_mul" = some natMul) (hpn : p.lookup "nat_pow" = some natPow)

/-- A power whose exponent is known to be `0` (`grind` does not rewrite an exponent by an equation). -/
theorem pow_of_eq_zero (a b : Nat) (h : b = 0) : a ^ b = 1 := by subst h; rfl

/-- An empty slice, from a bound. -/
theorem pv_of_lt_one (v : Array Word) (o l : Nat) (h : l < 1) : pv v o l = 0 := by
  obtain rfl : l = 0 := by omega
  rfl

variable (hz : p.lookup "size_bytes" = some sizeBytesL)
  (hpr : p.lookup "pow_refused" = some powRefusedL) (hpw : p.lookup "pow_nat" = some powNatL)
  (hps : p.lookup "nat_shl" = some natShl) (hlp : p.lookup "limb_push" = some limbPushL)

/-- A refused arm: a sentinel (`≥ 2^63`), the twin's failure with its message. -/
theorem NatRes.refused {R : Mem → AState → Prop} {arm : AM (Option EIdx)} {a₀ : AState}
    {m' : Mem} {r : Word} (hr : 2 ^ 63 ≤ r.toNat) (h : arm.run a₀ = .error (natRefusal r)) :
    NatRes R arm a₀ r m' :=
  ⟨fun h' => absurd h' (by omega), fun _ => h⟩

/-- `natPowArm` at the run's maximum: the two refusals of `powGuard`, or the power interned. -/
theorem natPowArm_run (a b : Nat) (st : AState) :
    (natPowArm a b).run st =
      if 4294967295 < b then .error (natRefusal natRefusedPowExp)
      else if powRefusedN st.pins.maxNatSize a b then .error (natRefusal natRefusedPowSize)
      else (do let x ← internE (.lit (.natVal (a ^ b))); pure (some x) : AM (Option EIdx)).run st := by
  simp only [natPowArm, StateT.run_bind, powGuard_run]
  by_cases h1 : 4294967295 < b
  · simp only [h1, ↓reduceIte]; rfl
  · by_cases h2 : powRefusedN st.pins.maxNatSize a b
    · simp only [h1, h2, ↓reduceIte]; rfl
    · simp only [h1, h2, ↓reduceIte]; rfl

/-- The one-limb slice at a pool address is that limb. -/
theorem pv_one_prd (m : Mem) (o : Word) (h : o.toNat < 2 ^ 41) :
    pv (vpool m) o.toNat 1 = (prd m o).toNat := by
  simp [pv, wt, vpool_getD m o h]

/-- `pow_refused`'s word condition is the twin's `powRefused` (a normalised base). -/
theorem powRefusedW_iff (m : Mem) (mx oa la e : Word) (hn : Norm (vpool m) oa.toNat la.toNat)
    (hoa : oa.toNat < 2 ^ 41) :
    powRefusedW mx la (prd m oa) e ↔
      powRefusedN mx.toNat (pv (vpool m) oa.toNat la.toNat) e.toNat := by
  have hsz := sizeBytes_pv (vpool m) oa.toNat la.toNat hn
  unfold powRefusedW powRefusedN
  rw [hsz]
  have ha1 : pv (vpool m) oa.toNat la.toNat ≤ 1 ↔ la = 0 ∨ (la = 1 ∧ prd m oa = 1) := by
    by_cases h0 : la = 0
    · subst h0; simp [pv]
    by_cases h1 : la = 1
    · subst h1
      rw [show (1 : Word).toNat = 1 from rfl] at hn ⊢
      rw [pv_one_prd m oa hoa]
      have hnz : prd m oa ≠ 0 := by
        have := hn (by decide); simpa [vpool_getD m oa hoa] using this
      constructor
      · intro h; right; refine ⟨rfl, ?_⟩
        apply UInt64.toNat_inj.mp
        have : (prd m oa).toNat ≠ 0 := fun e => hnz (UInt64.toNat_inj.mp (by simpa using e))
        simp; omega
      · rintro (h | ⟨-, h⟩)
        · exact absurd h (by decide)
        · rw [h]; decide
    · have h2 : 2 ≤ la.toNat := by
        have : la.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
        have : la.toNat ≠ 1 := fun e => h1 (UInt64.toNat_inj.mp (by simpa using e))
        omega
      have := pv_two_limbs _ _ _ hn h2
      constructor
      · intro h; omega
      · rintro (h | ⟨h, -⟩) <;> simp_all
  have he0 : e ≠ 0 ↔ e.toNat ≠ 0 := by
    constructor
    · intro h e'; exact h (UInt64.toNat_inj.mp (by simpa using e'))
    · intro h e'; exact h (by simp [e'])
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨fun h => ?_, he0.mp h2, ?_⟩
    · rcases ha1.mp h with h | h
      · exact h0 h
      · exact h1 h
    · rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (he0.mp h2))]; exact h3
  · rintro ⟨h0, h2, h3⟩
    refine ⟨fun h => h0 (ha1.mpr (Or.inl h)), fun h => h0 (ha1.mpr (Or.inr h)), he0.mpr h2, ?_⟩
    rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero h2)] at h3

include hpool hgrow hI hph hpt hpm hpn hz hpr hpw hps hlp in
/-- **`nat_pow_lit` refines the `Nat.pow` arm** (`powGuard`, then the power): the handle, or the
guard's sentinel (`NatRes`). -/
theorem natPowLit_refines (hg : p.lookup "nat_pow_lit" = some natPowLit) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀) (hmx : (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_pow_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatRes R (natPowArm (pv (vpool s₀.mem) oa.toNat la.toNat) (pv (vpool s₀.mem) ob.toNat lb.toNat))
        a₀ (r.headD 0) s'.mem; ⊤⦄ := by
  have hok := hpool _ _ hR
  have hbig := pv_two_limbs (vpool s₀.mem) ob.toNat lb.toNat hnb
  have h41 := hok.top41
  have hoa : oa.toNat < 2 ^ 41 := by simp only [SliceOK] at ha; omega
  have hob : 0 < lb.toNat → ob.toNat < 2 ^ 41 := fun _ => by simp only [SliceOK] at hb; omega
  have hrun := natPowArm_run (pv (vpool s₀.mem) oa.toNat la.toNat) (pv (vpool s₀.mem) ob.toNat lb.toNat) a₀
  rw [← hmx] at hrun
  rw [invoke_eq _ hg]
  simp only [callFn, natPowLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      powRefused_spec p hz hpr n, powNat_spec p hph hpt hpm hpn hps hpw hlp n, hI a₀ n]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons, St.setLocs_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval, reduceIte, beq_iff_eq,
      bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals try simp only [
      List.headD_cons, Locals.init_nil, reduceIte,
      Nat.reduceEqDiff, LocEq, Sig.retVal, Sig.retOr] at *
    case vc2 _ _ h =>
      apply NatRes.refused (by decide)
      rw [hrun, ite_eq_left]
      have := hbig (by simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at h; exact h); omega
    case vc4 _ _ _ hbd hl1 hX =>
      simp only [BinOp.eval, Locals.init_cons_zero, Locals.init_cons_succ] at hbd
      rw [prd_ld _ _ hbd] at hX
      subst hl1
      apply NatRes.refused (by decide)
      rw [hrun, ite_eq_left]
      rw [show (1 : Word).toNat = 1 from rfl, pv_one_prd _ _ (hob (by decide))]
      exact UInt64.lt_iff_toNat_lt.mp hX
    case vc6 _ _ _ hbd s hl1 hX hr hA =>
      simp only [BinOp.eval, Locals.init_cons_zero, Locals.init_cons_succ] at hbd
      obtain ⟨-, -, hrs⟩ := hA
      simp only [prd_ld _ _ hbd] at hX hrs
      subst hl1
      have hb1 : pv (vpool s₀.mem) ob.toNat (1 : Word).toNat = (prd s₀.mem ob).toNat :=
        pv_one_prd s₀.mem ob (hob (by decide))
      have hW : powRefusedW (rdW (s₀.mem.arr64 PINS) 72) la (prd s₀.mem oa) (prd s₀.mem ob) := by
        refine Classical.byContradiction fun hc => ?_
        rw [ite_eq_right hc] at hrs; exact hr hrs
      rw [powRefusedW_iff _ _ _ _ _ hna hoa, ← hb1] at hW
      apply NatRes.refused (by decide)
      rw [hrun, ite_eq_right (by rw [hb1]; exact fun h => hX (UInt64.lt_iff_toNat_lt.mpr h)), ite_eq_left hW]
    case vc8 _ _ _ hbd _ _ _ s₁ _ hl1 hX hr hP hA hI =>
      simp only [BinOp.eval, Locals.init_cons_zero, Locals.init_cons_succ] at hbd
      obtain ⟨hl2, hm2, hrs⟩ := hA
      obtain ⟨hl1', -, -, -, -, hpv⟩ := hP
      obtain ⟨-, hok', hR', hres'⟩ := hI
      simp only [prd_ld _ _ hbd] at hX hrs hl2
      subst hl1
      have hb1 : pv (vpool s₀.mem) ob.toNat (1 : Word).toNat = (prd s₀.mem ob).toNat :=
        pv_one_prd s₀.mem ob (hob (by decide))
      have hW : ¬ powRefusedW (rdW (s₀.mem.arr64 PINS) 72) la (prd s₀.mem oa) (prd s₀.mem ob) := by
        intro hc; rw [ite_eq_left hc] at hrs; exact hr (by rw [hrs]; decide)
      rw [powRefusedW_iff _ _ _ _ _ hna hoa, ← hb1] at hW
      rw [hl2, hm2] at hpv
      simp (config := { decide := true }) only [St.setLoc_loc, Locals.init_cons_zero, Locals.init_cons_succ, reduceIte] at hpv
      rw [hpv, ← hb1] at hok' hR' hres'
      refine NatRes.ofIntern _ _ rfl ?_ hok' hR' hres'
      rw [hrun, ite_eq_right (by rw [hb1]; exact fun h => hX (UInt64.lt_iff_toNat_lt.mpr h)), ite_eq_right hW]
    case vc14 _ _ _ _ s _ _ _ hA =>
      obtain ⟨hloc, hmem, -⟩ := hA
      rw [hmem, show s.loc 0 = oa by rw [hloc]; rfl, show s.loc 1 = la by rw [hloc]; rfl]; exact ha
    case vc15 _ _ _ hbd s _ hX _ hA =>
      obtain ⟨hloc, -, -⟩ := hA
      rw [show s.loc 4 = _ by rw [hloc]; try rfl]
      have := UInt64.not_lt.mp hX
      exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp this) (by decide)
    case vc21 _ _ _ _ _ hr _ hA =>
      obtain ⟨-, -, hrs⟩ := hA
      exact (hr (by simpa [powRefusedW] using hrs)).elim
    case vc23 _ _ h1 _ _ _ _ _ hl1 _ _ hA hP hI =>
      have hl0 : lb.toNat = 0 := by
        simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at h1
        have : lb.toNat ≠ 1 := fun e => hl1 (UInt64.toNat_inj.mp (by simpa using e))
        simp at h1; omega
      have hb0 : pv (vpool s₀.mem) ob.toNat lb.toNat = 0 := by rw [hl0]; rfl
      obtain ⟨hl1', -, -, -, -, hpv⟩ := hP
      obtain ⟨hl2, hm2, -⟩ := hA
      obtain ⟨-, hok', hR', hres'⟩ := hI
      rw [hl2, hm2] at hpv
      simp only [Locals.init_cons_zero, Locals.init_cons_succ, Locals.init_nil, UInt64.toNat_zero] at hpv
      rw [hpv] at hok' hR' hres'
      rw [hb0] at hrun ⊢
      refine NatRes.ofIntern _ _ rfl ?_ hok' hR' hres'
      rw [hrun, ite_eq_right (by decide), ite_eq_right (by simp [powRefusedN])]
    all_goals first
      | (simp_all [Locals.init]; done)
      | (grind [arena_grind, lang_grind]; done)

end pow


/-! ## `beq`, `ble`: a `Bool` constant -/

/-- `nat_beq_lit(oa, la, ob, lb, t, f, us)`: intern the constant `t` (`Bool.true`'s name) if the
two values are equal, else `f`, at the level list `us` (the empty one). The three handles are
the pins `boolTrueName`, `boolFalseName`, `emptyLevels`, which the caller reads. -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natBeqLit : FunDecl := lfn (oa, la, ob, lb, t, f, us) locals (c, h) {
  c := call nat_cmp(oa, la, ob, lb);
  if c != 1 { t := f };
  h := call intern_const(t, us);
  return h
}

/-- `nat_ble_lit`: as `nat_beq_lit`, `t` unless `a > b`. -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natBleLit : FunDecl := lfn (oa, la, ob, lb, t, f, us) locals (c, h) {
  c := call nat_cmp(oa, la, ob, lb);
  if c == 2 { t := f };
  h := call intern_const(t, us);
  return h
}

/-- The `Nat.beq` arm (`Arena/Core.lean:1027-1030`), verbatim. -/
def natBeqArm (a b : Nat) : AM (Option EIdx) := do
  let n ← if a = b then boolTrueName else boolFalseName
  let x ← constE n
  pure (some x)

/-- The `Nat.ble` arm (`Arena/Core.lean:1031-1034`), verbatim. -/
def natBleArm (a b : Nat) : AM (Option EIdx) := do
  let n ← if a <= b then boolTrueName else boolFalseName
  let x ← constE n
  pure (some x)

/-! ## `gcd` -/

/-- `nat_gcd_lit(oa, la, ob, lb)`: `nat_gcd`'s slice, interned. -/
-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natGcdLit : FunDecl := lfn (oa, la, ob, lb) locals (o, l, h) {
  (o, l) := call nat_gcd(oa, la, ob, lb);
  h := call intern_lit(o, l);
  return h
}

/-- The `Nat.gcd` arm (`Arena/Core.lean:1015-1016`), verbatim. -/
def natGcdArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.gcd a b))); pure (some x)

section gcd
variable (p : Prog) (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m) (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : InternSpec p R)
  (hpl : p.lookup "nat_limb" = some natLimb)
  (hps : p.lookup "sub_borrow" = some subBorrow) (hpc : p.lookup "add_carry" = some addCarry)
  (hp1 : p.lookup "div_shl1" = some divShl1) (hp2 : p.lookup "div_sub" = some divSub)
  (hp3 : p.lookup "div_add" = some divAdd) (hp4 : p.lookup "div_step" = some divStep)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpd : p.lookup "nat_divmod" = some natDivmod)
  (hps' : p.lookup "gcd_step" = some gcdStep) (hpg : p.lookup "nat_gcd" = some natGcd)

include hpool hgrow hI hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd hps' hpg in
theorem natGcdLit_refines (hg : p.lookup "nat_gcd_lit" = some natGcdLit) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀) (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la)
    (hb : SliceOK s₀.mem ob lb) (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_gcd_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natGcdArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (natGcdArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natGcdArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ := by
  have hok := hpool _ _ hR
  rw [invoke_eq _ hg]
  simp only [callFn, natGcdLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalArgs, setLoc, setLocs,
        natGcd_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd hps' hpg n, hI a₀ n] <;>
      finish [natGcdArm]

end gcd

/-! ## The arms, verbatim (`Arena/Core.lean:1004-1026`) -/

def natSubArm (a b : Nat) : AM (Option EIdx) := ConRon.Arena.litNatSized (a - b)
def natMulArm (a b : Nat) : AM (Option EIdx) := ConRon.Arena.litNatSized (a * b)
def natLandArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.land a b))); pure (some x)
def natLorArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.lor a b))); pure (some x)
def natXorArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.xor a b))); pure (some x)
def natShlArm (a b : Nat) : AM (Option EIdx) := do
  ConRon.Arena.shiftLeftGuard a b
  let x ← internE (.lit (.natVal (Nat.shiftLeft a b))); pure (some x)
def natShrArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.shiftRight a b))); pure (some x)

section shl
variable (p : Prog) (R : Mem → AState → Prop)
  (hpool : ∀ m a, R m a → PoolOK m) (hgrow : ∀ m m' a, R m a → Grows m m' → R m' a)
  (hI : InternSpec p R)
  (hpt : p.lookup "nat_trim" = some natTrim) (hps : p.lookup "nat_shl" = some natShl)
  (hz : p.lookup "size_bytes" = some sizeBytesL)
  (hsl : p.lookup "shift_left_refused" = some shiftLeftRefusedL)

/-- `natShlArm` at the run's maximum: `0 <<< b` computes, else the two refusals of
`shiftLeftGuard`, or the shift interned. -/
theorem natShlArm_run (a b : Nat) (st : AState) :
    (natShlArm a b).run st =
      if a ≠ 0 ∧ 4294967295 < b then .error (natRefusal natRefusedShlExp)
      else if a ≠ 0 ∧ shlRefusedN st.pins.maxNatSize a b then .error (natRefusal natRefusedSize)
      else (do let x ← internE (.lit (.natVal (Nat.shiftLeft a b))); pure (some x) :
        AM (Option EIdx)).run st := by
  simp only [natShlArm, StateT.run_bind, shiftLeftGuard_run]
  by_cases h0 : a = 0
  · simp only [h0, ↓reduceIte, ne_eq, not_true_eq_false, false_and]; rfl
  by_cases h1 : 4294967295 < b
  · simp only [h0, h1, ↓reduceIte, ne_eq, not_false_eq_true, and_self]; rfl
  · by_cases h2 : shlRefusedN st.pins.maxNatSize a b
    · simp only [h0, h1, h2, ↓reduceIte, ne_eq, not_false_eq_true, and_self, and_false]; rfl
    · simp only [h0, h1, h2, ↓reduceIte, ne_eq, not_false_eq_true, and_false]; rfl

include hpool hgrow hI hpt hps hz hsl in
/-- **`nat_shl_lit` refines the `Nat.shiftLeft` arm** (`shiftLeftGuard`, then the shift): the
handle, or the guard's sentinel (`NatRes`). -/
theorem natShlLit_refines (hg : p.lookup "nat_shl_lit" = some natShlLit) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀) (hmx : (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_shl_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatRes R (natShlArm (pv (vpool s₀.mem) oa.toNat la.toNat) (pv (vpool s₀.mem) ob.toNat lb.toNat))
        a₀ (r.headD 0) s'.mem; ⊤⦄ := by
  have hok := hpool _ _ hR
  have hbig := pv_two_limbs (vpool s₀.mem) ob.toNat lb.toNat hnb
  have h41 := hok.top41
  have hla : la.toNat < 2 ^ 41 := by simp only [SliceOK] at ha; omega
  have hob : 0 < lb.toNat → ob.toNat < 2 ^ 41 := fun _ => by simp only [SliceOK] at hb; omega
  have ha0 : pv (vpool s₀.mem) oa.toNat la.toNat = 0 ↔ la = 0 := by
    constructor
    · intro h; apply Classical.byContradiction; intro hl
      have hl' : 0 < la.toNat := Nat.pos_of_ne_zero fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
      have := pv_ge_wt _ _ _ hl' hna; have : 0 < wt (la.toNat - 1) := Nat.pow_pos (by decide) 
      omega
    · intro h; subst h; rfl
  have hsz := sizeBytes_pv (vpool s₀.mem) oa.toNat la.toNat hna
  have hrun := natShlArm_run (pv (vpool s₀.mem) oa.toNat la.toNat) (pv (vpool s₀.mem) ob.toNat lb.toNat) a₀
  rw [← hmx] at hrun
  rw [invoke_eq _ hg]
  simp only [callFn, natShlLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      shiftLeftRefused_spec p hz hsl n, natShl_spec p hpt hps n, hI a₀ n]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons, St.setLocs_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval, reduceIte, beq_iff_eq,
      bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals try simp only [St.setLocs_cons, St.setLocs_nil, L.St.setLoc_mem,
      List.headD_cons, Locals.init_nil, reduceIte,
      Nat.reduceEqDiff, Sig.retVal, Sig.retOr] at *
    case vc2 _ _ h hla =>
      have hb : 4294967295 < pv (vpool s₀.mem) ob.toNat lb.toNat := by
        have := hbig (by simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at h; exact h); omega
      apply NatRes.refused (by decide)
      rw [hrun, ite_eq_left ⟨fun h0 => hla (ha0.mp h0), hb⟩]
    case vc4 _ _ _ hbd hla hl1 hX =>
      simp only [BinOp.eval, Locals.init_cons_zero, Locals.init_cons_succ] at hbd
      rw [prd_ld _ _ hbd] at hX
      subst hl1
      have hb : 4294967295 < pv (vpool s₀.mem) ob.toNat (1 : Word).toNat := by
        rw [show (1 : Word).toNat = 1 from rfl, pv_one_prd _ _ (hob (by decide))]
        exact UInt64.lt_iff_toNat_lt.mp hX
      apply NatRes.refused (by decide)
      rw [hrun, ite_eq_left ⟨fun h0 => hla (ha0.mp h0), hb⟩]
    case vc6 _ _ _ hbd _ hla hl1 hX hr hA =>
      simp only [BinOp.eval, Locals.init_cons_zero, Locals.init_cons_succ] at hbd
      obtain ⟨-, -, hrs⟩ := hA
      simp only [prd_ld _ _ hbd] at hX hrs
      subst hl1
      have hb1 : pv (vpool s₀.mem) ob.toNat (1 : Word).toNat = (prd s₀.mem ob).toNat :=
        pv_one_prd s₀.mem ob (hob (by decide))
      have hW : shlRefusedN (rdW (s₀.mem.arr64 PINS) 72).toNat (pv (vpool s₀.mem) oa.toNat la.toNat)
          (pv (vpool s₀.mem) ob.toNat (1 : Word).toNat) := by
        refine Classical.byContradiction fun hc => hr ?_
        rw [hrs, ite_eq_right]; unfold shlRefusedN at hc; rw [hsz, hb1] at hc; exact hc
      apply NatRes.refused (by decide)
      rw [hrun, ite_eq_right (fun h => hX (UInt64.lt_iff_toNat_lt.mpr (hb1 ▸ h.2))),
        ite_eq_left ⟨fun h0 => hla (ha0.mp h0), hW⟩]
    case vc8 _ _ _ hbd _ s₂ hc _ s₁ _ hla hl1 hX hr hP hA hI =>
      simp only [BinOp.eval, Locals.init_cons_zero, Locals.init_cons_succ] at hbd
      obtain ⟨hl₁, -, -, -, -, hpv, -, -⟩ := hP
      obtain ⟨hl₂, hm₂, hrs⟩ := hA
      obtain ⟨-, hok', hR', hres'⟩ := hI
      simp only [prd_ld _ _ hbd] at hX hrs hl₂
      subst hl1
      have hb1 : pv (vpool s₀.mem) ob.toNat (1 : Word).toNat = (prd s₀.mem ob).toNat :=
        pv_one_prd s₀.mem ob (hob (by decide))
      have hW : ¬ shlRefusedN (rdW (s₀.mem.arr64 PINS) 72).toNat (pv (vpool s₀.mem) oa.toNat la.toNat)
          (pv (vpool s₀.mem) ob.toNat (1 : Word).toNat) := by
        intro hc; apply hr; rw [hrs, ite_eq_left]
        · decide
        · unfold shlRefusedN at hc; rw [hsz, hb1] at hc; exact hc
      simp only [St.setLocs_cons, St.setLocs_nil, L.St.setLoc_mem] at hc
      have h6 : s₁.loc 6 = s₂.mem.top := by
        rw [hl₁.loc 6, St.setLoc_loc]; exact (Mem.top_eq _ hc).symm
      have h0 : s₂.loc 0 = oa := by rw [hl₂.loc 0]; rfl
      have h1 : s₂.loc 1 = la := by rw [hl₂.loc 1]; rfl
      have h2 : s₂.loc 2 = ob := by rw [hl₂.loc 2]; rfl
      have h3 : s₂.loc 3 = 1 := by rw [hl₂.loc 3]; rfl
      rw [h0, h1, h2, h3, hm₂] at hpv
      rw [h6, hm₂, hpv, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq'] at hok' hR' hres'
      refine NatRes.ofIntern _ _ rfl ?_ hok' hR' hres'
      rw [hrun, ite_eq_right (fun h => hX (UInt64.lt_iff_toNat_lt.mpr (hb1 ▸ h.2))),
        ite_eq_right (fun h => hW h.2)]
    case vc20 _ _ h1 _ hla hl1 hr _ hA =>
      have hl0 : lb.toNat = 0 := by
        have : lb.toNat ≠ 1 := fun e => hl1 (UInt64.toNat_inj.mp (by simpa using e))
        simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at h1; simp at h1; omega
      have hb0 : pv (vpool s₀.mem) ob.toNat lb.toNat = 0 := by rw [hl0]; rfl
      obtain ⟨-, -, hrs⟩ := hA
      try simp only [Locals.init_cons_zero, Locals.init_cons_succ, Locals.init_nil] at hrs
      have hW : shlRefusedN (rdW (s₀.mem.arr64 PINS) 72).toNat (pv (vpool s₀.mem) oa.toNat la.toNat)
          (pv (vpool s₀.mem) ob.toNat lb.toNat) := by
        refine Classical.byContradiction fun hc => hr ?_
        rw [hrs, ite_eq_right]; unfold shlRefusedN at hc; rw [hsz, hb0] at hc; simpa using hc
      apply NatRes.refused (by decide)
      rw [hrun, ite_eq_right (fun h => by rw [hb0] at h; exact absurd h.2 (by decide)),
        ite_eq_left ⟨fun h0 => hla (ha0.mp h0), hW⟩]
    case vc22 _ _ h1 _ s₂ hc _ s₁ _ hla hl1 hr _ hA hP hI =>
      have hl0 : lb.toNat = 0 := by
        have : lb.toNat ≠ 1 := fun e => hl1 (UInt64.toNat_inj.mp (by simpa using e))
        simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at h1; simp at h1; omega
      have hb0 : pv (vpool s₀.mem) ob.toNat lb.toNat = 0 := by rw [hl0]; rfl
      obtain ⟨hl₂, hm₂, hrs⟩ := hA
      obtain ⟨hl₁, -, -, -, -, hpv, -, -⟩ := hP
      obtain ⟨-, hok', hR', hres'⟩ := hI
      try simp only [Locals.init_cons_zero, Locals.init_cons_succ, Locals.init_nil] at hrs
      have hW : ¬ shlRefusedN (rdW (s₀.mem.arr64 PINS) 72).toNat (pv (vpool s₀.mem) oa.toNat la.toNat)
          (pv (vpool s₀.mem) ob.toNat lb.toNat) := by
        intro hc; apply hr; rw [hrs, ite_eq_left]
        · decide
        · unfold shlRefusedN at hc; rw [hsz, hb0] at hc; simpa using hc
      simp only [St.setLocs_cons, St.setLocs_nil, L.St.setLoc_mem] at hc
      have h6 : s₁.loc 6 = s₂.mem.top := by
        rw [hl₁.loc 6, St.setLoc_loc]; exact (Mem.top_eq _ hc).symm
      have h0 : s₂.loc 0 = oa := by rw [hl₂.loc 0]; rfl
      have h1' : s₂.loc 1 = la := by rw [hl₂.loc 1]; rfl
      have h2 : s₂.loc 2 = ob := by rw [hl₂.loc 2]; rfl
      have h3 : s₂.loc 3 = lb := by rw [hl₂.loc 3]; rfl
      rw [h0, h1', h2, h3, hm₂] at hpv
      rw [h6, hm₂, hpv, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq'] at hok' hR' hres'
      refine NatRes.ofIntern _ _ rfl ?_ hok' hR' hres'
      rw [hrun, ite_eq_right (fun h => by rw [hb0] at h; exact absurd h.2 (by decide)),
        ite_eq_right (fun h => hW h.2)]
    case vc32 _ _ hc _ s₁ _ hla hP hI =>
      have ha00 : pv (vpool s₀.mem) oa.toNat la.toNat = 0 := ha0.mpr (Classical.not_not.mp hla)
      obtain ⟨hl₁, -, -, -, -, hpv, -, -⟩ := hP
      obtain ⟨-, hok', hR', hres'⟩ := hI
      have h6 : s₁.loc 6 = s₀.mem.top := by
        rw [hl₁.loc 6, St.setLoc_loc]; exact (Mem.top_eq _ hc).symm
      rw [h6, hpv, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq'] at hok' hR' hres'
      refine NatRes.ofIntern _ _ rfl ?_ hok' hR' hres'
      rw [hrun, ite_eq_right (fun h => h.1 ha00), ite_eq_right (fun h => h.1 ha00)]
    all_goals first
      | (simp_all []; done)
      | (grind [arena_grind, lang_grind]; done)

end shl
def natDivArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (a / b))); pure (some x)
def natModArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (a % b))); pure (some x)

/-! ## The operation codes and the dispatch

`NatBinOp` in L is a word: `natBinOpW` (`add` `1` … `shiftRight` `14`, the twin's constructor order;
`0` is "no operation", `natBinOpOptW`). The operation with code `k` has its name at pin word
`15 + k` (`nat_bin_op_of_name`, `WhnfDelta.lean`).

`nat_bin_op_result(op, oa, la, ob, lb)`: `natBinOpResult`, one arm per operation code, in the twin's
order. Returns `(1, h)` for `some h` and `(2, s)` for a refusal (the sentinel `s` of
`NatSized.lean`, from the `add`, `sub`, `mul`, `pow`, `shiftLeft` arms). The `beq`/`ble` arms read
the `Bool` constructors' and the empty level list's pins (`PINS` word `1 + PIN_*`). A code outside `1‥14` is no operation: `abort` (never reached: the code comes from
`nat_bin_op_of_name`). Refined in `PinsNatOp.lean`. -/

/-- The word code of a `Nat` operation (`decNatBinOp`'s inverse). -/
def natBinOpW : NatBinOp → Word
  | .add => 1 | .sub => 2 | .mul => 3 | .pow => 4 | .beq => 5 | .ble => 6 | .div => 7
  | .mod => 8 | .gcd => 9 | .land => 10 | .lor => 11 | .xor => 12 | .shiftLeft => 13
  | .shiftRight => 14

/-- The word code of an optional operation: `0` for none. -/
def natBinOpOptW : Option NatBinOp → Word
  | none => 0
  | some o => natBinOpW o

/-- **The operation a word codes** (the relation between L's code and the twin's `NatBinOp`). -/
def decNatBinOp (w : Word) : Option NatBinOp :=
  if w = 1 then some .add else if w = 2 then some .sub else if w = 3 then some .mul
  else if w = 4 then some .pow else if w = 5 then some .beq else if w = 6 then some .ble
  else if w = 7 then some .div else if w = 8 then some .mod else if w = 9 then some .gcd
  else if w = 10 then some .land else if w = 11 then some .lor else if w = 12 then some .xor
  else if w = 13 then some .shiftLeft else if w = 14 then some .shiftRight else none

theorem decNatBinOp_optW (o : Option NatBinOp) : decNatBinOp (natBinOpOptW o) = o := by
  rcases o with _ | o
  · rfl
  · cases o <;> rfl

theorem natBinOpW_ne_zero (o : NatBinOp) : natBinOpW o ≠ 0 := by cases o <;> decide

theorem natBinOpW_lt (o : NatBinOp) : (natBinOpW o).toNat < 15 := by cases o <;> decide

-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natBinOpResultL : FunDecl := lfn (op, oa, la, ob, lb) locals (h) {
  if op == 1 { h := call nat_add_lit(oa, la, ob, lb); return (1 + (h >> 63), h) };
  if op == 2 { h := call nat_sub_lit(oa, la, ob, lb); return (1 + (h >> 63), h) };
  if op == 3 { h := call nat_mul_lit(oa, la, ob, lb); return (1 + (h >> 63), h) };
  if op == 4 { h := call nat_pow_lit(oa, la, ob, lb); return (1 + (h >> 63), h) };
  if op == 5 {
    h := call nat_beq_lit(oa, la, ob, lb, PINS.u64[31], PINS.u64[32], PINS.u64[52]);
    return (1, h)
  };
  if op == 6 {
    h := call nat_ble_lit(oa, la, ob, lb, PINS.u64[31], PINS.u64[32], PINS.u64[52]);
    return (1, h)
  };
  if op == 7 { h := call nat_div_lit(oa, la, ob, lb); return (1, h) };
  if op == 8 { h := call nat_mod_lit(oa, la, ob, lb); return (1, h) };
  if op == 9 { h := call nat_gcd_lit(oa, la, ob, lb); return (1, h) };
  if op == 10 { h := call nat_land_lit(oa, la, ob, lb); return (1, h) };
  if op == 11 { h := call nat_lor_lit(oa, la, ob, lb); return (1, h) };
  if op == 12 { h := call nat_xor_lit(oa, la, ob, lb); return (1, h) };
  if op == 13 { h := call nat_shl_lit(oa, la, ob, lb); return (1 + (h >> 63), h) };
  if op == 14 { h := call nat_shr_lit(oa, la, ob, lb); return (1, h) };
  abort
}

/-! ## The program -/

/-- The pool functions, the `lit` store, and one L arm per operation. -/
def natArmProg : Prog := storeProg ++
  [("sub_borrow", subBorrow), ("nat_sub", natSub), ("mac_hi", macHi), ("mul_row", mulRow), ("sub_row", subRow),
   ("mul_zeros", mulZeros), ("kara_sum", karaSum), ("kara_prods", karaProds), ("kara_mid", karaMid), ("mul_win", mulWin), ("nat_mul", natMul),
   ("nat_land", natLand), ("nat_lor", natLor), ("nat_xor", natXor), ("nat_shl", natShl),
   ("nat_shr", natShr),
   ("nat_sub_lit", topLitS "nat_sub"), ("nat_mul_lit", topLitS "nat_mul"),
   ("nat_land_lit", topLit "nat_land"), ("nat_lor_lit", topLit "nat_lor"),
   ("nat_xor_lit", topLit "nat_xor"), ("nat_shl_lit", natShlLit),
   ("nat_shr_lit", topLit "nat_shr"),
   ("nat_pow", natPow), ("pow_nat", powNatL), ("limb_push", limbPushL), ("pow_refused", powRefusedL), ("shift_left_refused", shiftLeftRefusedL), ("div_shl1", divShl1), ("div_sub", divSub), ("div_add", divAdd),
   ("div_step", divStep), ("nat_divmod", natDivmod),
   ("nat_pred_lit", natPredLit), ("nat_pow_lit", natPowLit), ("nat_div_lit", natDivLit),
   ("nat_mod_lit", natModLit),
   ("nat_cmp", natCmp), ("const_find", constFind), ("const_push", constPush),
   ("intern_const", internConst), ("nat_beq_lit", natBeqLit), ("nat_ble_lit", natBleLit),
   ("gcd_step", gcdStep), ("nat_gcd", natGcd), ("nat_gcd_lit", natGcdLit),
   ("nat_bin_op_result", natBinOpResultL)]

/- `6 - 1 = 5`, `7 % 8 = 7`, `7 * 5 = 35` (at pool offset 9) and `35 / 5 = 7`: three nodes, and
the quotient finds `7`'s node again. -/
#guard
  let m : Mem := Mem.ofWords [(POOL, #[5, 7, 6, 8] ++ Array.replicate 60 0), (CTL, #[4] ++ Array.replicate 63 0),
    (REC, Array.replicate 64 0), (SLOT, Array.replicate consTestWords 0),
    (PINS, Array.replicate 72 0 ++ #[134217728])]
  let go (m : Mem) (f : FnName) (args : List Word) : Option (Word × Mem) :=
    match run natArmProg 100000 f args m with
    | .ok (r, m') => some (r.headD 0, m')
    | .error _ => none
  match go m "nat_pred_lit" [2, 1] with
  | some (h₁, m) => match go m "nat_mod_lit" [1, 1, 3, 1] with
    | some (h₂, m) => match go m "nat_mul_lit" [1, 1, 0, 1] with
      | some (h₃, m) => match go m "nat_div_lit" [9, 1, 0, 1] with
        | some (h₄, _) => [h₁, h₂, h₃, h₄] == [0x20000000, 0x20000001, 0x20000002, 0x20000001]
        | none => false
      | none => false
    | none => false
  | none => false

/-! ## The pool functions' specs in `TopSpec` form -/

theorem natSub_top : TopSpec natArmProg "nat_sub" (fun a b => a - b) :=
  fun n s₀ oa la ob lb hok ha hb _ _ => natSub_spec natArmProg rfl rfl rfl rfl n s₀ oa la ob lb hok ha hb

theorem natMul_top : TopSpec natArmProg "nat_mul" (fun a b => a * b) :=
  fun n s₀ oa la ob lb hok ha hb _ _ => natMul_spec natArmProg rfl rfl rfl n s₀ oa la ob lb hok ha hb

theorem natLand_top : TopSpec natArmProg "nat_land" Nat.land := by
  intro n s₀ oa la ob lb hok ha hb _ _
  have := natLand_spec natArmProg rfl rfl rfl n s₀ oa la ob lb hok ha hb
  simpa only [← land_bv] using this

theorem natLor_top : TopSpec natArmProg "nat_lor" Nat.lor := by
  intro n s₀ oa la ob lb hok ha hb _ _
  have := natLor_spec natArmProg rfl rfl rfl n s₀ oa la ob lb hok ha hb
  simpa only [← lor_bv] using this

theorem natXor_top : TopSpec natArmProg "nat_xor" Nat.xor := by
  intro n s₀ oa la ob lb hok ha hb _ _
  have := natXor_spec natArmProg rfl rfl rfl n s₀ oa la ob lb hok ha hb
  simpa only [← xor_bv] using this

theorem natShl_top : TopSpec natArmProg "nat_shl" Nat.shiftLeft := by
  intro n s₀ oa la ob lb hok ha hb _ _
  have := natShl_spec natArmProg rfl rfl n s₀ oa la ob lb hok ha hb
  simpa only [← Nat.shiftLeft_eq, Nat.shiftLeft_eq'] using this

theorem natShr_top : TopSpec natArmProg "nat_shr" Nat.shiftRight := by
  intro n s₀ oa la ob lb hok ha hb _ hnb
  have := natShr_spec natArmProg rfl rfl rfl n s₀ oa la ob lb hok ha hb hnb
  simpa only [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq'] using this

/-! ## Under `ArenaR` -/

/-- `intern_lit` in `natArmProg` under `ArenaR`. -/
theorem internLit_arms : InternSpec natArmProg ArenaR :=
  internLit_refinesA natArmProg rfl rfl rfl rfl rfl rfl

/-- The arm refinement for `natArmProg` under `ArenaR`, with the operands' slices given. -/
abbrev ArmRefinesA (g : FnName) (arm : Nat → Nat → AM (Option EIdx)) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState), ArenaR s₀.mem a₀ → ∀ (oa la ob lb : Word),
    SliceOK s₀.mem oa la → SliceOK s₀.mem ob lb →
    Norm (vpool s₀.mem) oa.toNat la.toNat → Norm (vpool s₀.mem) ob.toNat lb.toNat →
    ModeOK s₀.mem →
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) g [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (arm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄

theorem topLit_refinesA (g f : FnName) (F : Nat → Nat → Nat)
    (hg : natArmProg.lookup g = some (topLit f)) (hF : TopSpec natArmProg f F) :
    ArmRefinesA g (litArm F) :=
  fun n s₀ a₀ hR oa la ob lb ha hb hna hnb hmode =>
    topLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms g f F hg hF n s₀ a₀ hR
      oa la ob lb ha hb hna hnb hmode

/-- The refinement of an arm that may refuse (`NatRes`), at the run's maximum `PINS[72]`. -/
abbrev ArmRefinesS (g : FnName) (arm : Nat → Nat → AM (Option EIdx)) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState), ArenaR s₀.mem a₀ →
    (rdW (s₀.mem.arr64 PINS) 72).toNat = a₀.pins.maxNatSize → ∀ (oa la ob lb : Word),
    SliceOK s₀.mem oa la → SliceOK s₀.mem ob lb →
    Norm (vpool s₀.mem) oa.toNat la.toNat → Norm (vpool s₀.mem) ob.toNat lb.toNat →
    ModeOK s₀.mem →
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) g [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      NatRes ArenaR (arm (pv (vpool s₀.mem) oa.toNat la.toNat) (pv (vpool s₀.mem) ob.toNat lb.toNat))
        a₀ (r.headD 0) s'.mem; ⊤⦄

theorem topLitS_refinesA (g f : FnName) (F : Nat → Nat → Nat)
    (hg : natArmProg.lookup g = some (topLitS f)) (hF : TopSpec natArmProg f F) :
    ArmRefinesS g (fun a b => ConRon.Arena.litNatSized (F a b)) :=
  fun n s₀ a₀ hR hmx oa la ob lb ha hb hna hnb hmode =>
    topLitS_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl g f F hg hF n s₀ a₀ hR
      hmx oa la ob lb ha hb hna hnb hmode

/-- **`nat_sub_lit` refines `natBinOpResult`'s `Nat.sub` arm under `ArenaR`.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.sub"]
theorem natSubLit_refinesA : ArmRefinesS "nat_sub_lit" natSubArm :=
  topLitS_refinesA "nat_sub_lit" "nat_sub" _ rfl natSub_top
/-- **`nat_mul_lit` refines the `Nat.mul` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.mul"]
theorem natMulLit_refinesA : ArmRefinesS "nat_mul_lit" natMulArm :=
  topLitS_refinesA "nat_mul_lit" "nat_mul" _ rfl natMul_top
/-- **`nat_land_lit` refines the `Nat.land` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.land"]
theorem natLandLit_refinesA : ArmRefinesA "nat_land_lit" natLandArm :=
  topLit_refinesA "nat_land_lit" "nat_land" _ rfl natLand_top
/-- **`nat_lor_lit` refines the `Nat.lor` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.lor"]
theorem natLorLit_refinesA : ArmRefinesA "nat_lor_lit" natLorArm :=
  topLit_refinesA "nat_lor_lit" "nat_lor" _ rfl natLor_top
/-- **`nat_xor_lit` refines the `Nat.xor` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.xor"]
theorem natXorLit_refinesA : ArmRefinesA "nat_xor_lit" natXorArm :=
  topLit_refinesA "nat_xor_lit" "nat_xor" _ rfl natXor_top
/-- **`nat_shl_lit` refines the `Nat.shiftLeft` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.shiftLeft"]
theorem natShlLit_refinesA : ArmRefinesS "nat_shl_lit" natShlArm :=
  fun n s₀ a₀ hR hmx oa la ob lb ha hb hna hnb hmode =>
    natShlLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl n s₀ a₀ hR
      hmx oa la ob lb ha hb hna hnb hmode
/-- **`nat_shr_lit` refines the `Nat.shiftRight` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.shiftRight"]
theorem natShrLit_refinesA : ArmRefinesA "nat_shr_lit" natShrArm :=
  topLit_refinesA "nat_shr_lit" "nat_shr" _ rfl natShr_top

/-- **`nat_div_lit` refines the `Nat.div` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.div"]
theorem natDivLit_refinesA : ArmRefinesA "nat_div_lit" natDivArm :=
  fun n s₀ a₀ hR oa la ob lb ha hb _ hnb hmode =>
    natDivLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hnb hmode

/-- **`nat_mod_lit` refines the `Nat.mod` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.mod"]
theorem natModLit_refinesA : ArmRefinesA "nat_mod_lit" natModArm :=
  fun n s₀ a₀ hR oa la ob lb ha hb _ hnb hmode =>
    natModLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hnb hmode

/-- **`nat_pred_lit` refines the `Nat.pred` arm.** -/
@[refines_part ConRon.Arena.natLitToConstructor "n - 1"]
theorem natPredLit_refinesA (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (oa la : Word) (ha : SliceOK s₀.mem oa la) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_pred_lit" [oa, la]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀) ∧
      AM.res (natPredArm (pv (vpool s₀.mem) oa.toNat la.toNat)) a₀ =
        some (decE (r.headD 0)); ⊤⦄ :=
  natPredLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
    (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl n s₀ a₀ hR
    oa la ha hmode

/-- **`nat_pow_lit` refines the `Nat.pow` arm**, its guard included. -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.pow"]
theorem natPowLit_refinesA : ArmRefinesS "nat_pow_lit" natPowArm :=
  fun n s₀ a₀ hR hmx oa la ob lb ha hb hna hnb hmode =>
    natPowLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl n s₀ a₀ hR hmx oa la ob lb ha hb hna hnb hmode

/-- **`nat_beq_lit` refines the `Nat.beq` arm under `ArenaR`**, given what the three pin reads
return in the arena state (they read it and do not change it). -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.beq"]
theorem natBeqLit_refinesA (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (oa la ob lb t f us : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat)
    (ht : t.toNat < 2 ^ 32) (hf : f.toNat < 2 ^ 32) (hu : us.toNat < 2 ^ 32)
    (hT : boolTrueName.run a₀ = .ok (decI t, a₀)) (hF : boolFalseName.run a₀ = .ok (decI f, a₀))
    (hE : emptyLevels.run a₀ = .ok (decI us, a₀)) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_beq_lit" [oa, la, ob, lb, t, f, us]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natBeqArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (natBeqArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natBeqArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ := by
  have hok := hR.lit.1
  have hT' := AM.of_run_ok _ _ _ _ hT
  have hF' := AM.of_run_ok _ _ _ _ hF
  have hE' := AM.of_run_ok _ _ _ _ hE
  have := hok.ctl; have := hok.cap; have := hok.top; have := hok.ptop0; have := hok.inTier; clear hok
  simp only [SliceOK] at ha hb
  rw [invoke_eq _ (show natArmProg.lookup "nat_beq_lit" = some natBeqLit from rfl)]
  simp only [callFn, natBeqLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natcmp_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        natCmp_spec natArmProg rfl n, internConst_refinesA natArmProg rfl rfl rfl a₀ n] <;>
      finish [natBeqArm, constE, decE_eq]

/-- **`nat_ble_lit` refines the `Nat.ble` arm under `ArenaR`**, given the three pin reads. -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.ble"]
theorem natBleLit_refinesA (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (oa la ob lb t f us : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hna : Norm (vpool s₀.mem) oa.toNat la.toNat)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat)
    (ht : t.toNat < 2 ^ 32) (hf : f.toNat < 2 ^ 32) (hu : us.toNat < 2 ^ 32)
    (hT : boolTrueName.run a₀ = .ok (decI t, a₀)) (hF : boolFalseName.run a₀ = .ok (decI f, a₀))
    (hE : emptyLevels.run a₀ = .ok (decI us, a₀)) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_ble_lit" [oa, la, ob, lb, t, f, us]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natBleArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (natBleArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natBleArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = some (decE (r.headD 0)); ⊤⦄ := by
  have hok := hR.lit.1
  have hT' := AM.of_run_ok _ _ _ _ hT
  have hF' := AM.of_run_ok _ _ _ _ hF
  have hE' := AM.of_run_ok _ _ _ _ hE
  have := hok.ctl; have := hok.cap; have := hok.top; have := hok.ptop0; have := hok.inTier; clear hok
  simp only [SliceOK] at ha hb
  rw [invoke_eq _ (show natArmProg.lookup "nat_ble_lit" = some natBleLit from rfl)]
  simp only [callFn, natBleLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natcmp_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        natCmp_spec natArmProg rfl n, internConst_refinesA natArmProg rfl rfl rfl a₀ n] <;>
      finish [natBleArm, constE, decE_eq]

/-- **`nat_gcd_lit` refines the `Nat.gcd` arm.** -/
@[refines_part ConRon.Arena.natBinOpResult "Nat.gcd"]
theorem natGcdLit_refinesA : ArmRefinesA "nat_gcd_lit" natGcdArm :=
  fun n s₀ a₀ hR oa la ob lb ha hb hna hnb hmode =>
    natGcdLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hna hnb hmode

end L.Arena
