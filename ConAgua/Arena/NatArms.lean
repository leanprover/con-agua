import ConAgua.Arena.Tiers
import ConAgua.Arena.NatGcd
import ConAgua.Arena.NatCmp
import ConAgua.Arena.NatBitsNat
import ConAgua.Arena.NatPow
import ConAgua.Arena.NatShr
import ConAgua.Arena.NatShl
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The `Nat` arms of `natOpResult`, refined under `ArenaR`

`natOpResult` (`vendor/con-ron/ConRon/Arena/Core.lean:998`) reads the operation's pins and then
runs one arm per operation; an arm with a literal result is
`do let x ← internE (.lit (.natVal (F a b))); pure (some x)` (`litArm F`). `natAddArm`
(`Refine.lean`) is the `+` arm; this file does the others, following `natAddLit_refines`:

* **One generic theorem for the arms whose pool function appends at the top**
  (`topLit_refines`): an L wrapper `topLit f` (`o := CTL[0]; l := call f(…); h :=
  call intern_lit(o, l); return h`) refines `litArm F`, given `f`'s spec in the shape of
  `natAdd_spec` (`TopSpec p f F`: the result at the old top denotes `F a b`, normalised, the pool
  grew). Instances: `-`, `*`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`; `pred` is `-` with
  a one-limb `1` written at the top first.
* **The arms whose pool function returns a slice**: `pow` (with con-leche's exponent bound,
  `none` above `2^24`), `/` and `%` (`nat_divmod`'s two slices).
* Under `ArenaR`, as `natAddLit_refinesA`.

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

/-- The arm of `natOpResult` with the literal result `F a b`. -/
def litArm (F : Nat → Nat → Nat) (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (F a b)))
  pure (some x)

/-- `natAddLit` with `f` for `nat_add`: `o := CTL[0]; l := call f(oa, la, ob, lb);
h := call intern_lit(o, l); return h`. -/
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
def topLit (f : FnName) : FunDecl :=
  ⟨4, 7, .seq (.set 4 (.ld64 CTL (.const 0)))
    (.seq (.call [5] f [.var 0, .var 1, .var 2, .var 3])
      (.seq (.call [6] "intern_lit" [.var 4, .var 5]) (.ret [.var 6])))⟩

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
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs, ld64, hF n, hI a₀ n] <;>
      finish [litArm]

end generic

/-! ## The arms with a slice result: `/`, `%` -/

/-- `nat_div_lit(oa, la, ob, lb)`: the quotient slice of `nat_divmod`, interned. -/
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
@[l_impl ConRon.Arena.natOpResult]
def natDivLit : FunDecl := lfn (oa, la, ob, lb) locals (o, l, h) {
  (o, l) := call nat_divmod(oa, la, ob, lb);
  h := call intern_lit(o, l);
  return h
}

/-- `nat_mod_lit(oa, la, ob, lb)`: the remainder slice of `nat_divmod`, interned. -/
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
@[l_impl ConRon.Arena.natOpResult]
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
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs,
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
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs,
        natDivmod_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd n, hI a₀ n] <;>
      finish [litArm]

end divmod

/-! ## `pred`: `-` with a one-limb `1` -/

/-- `nat_pred_lit(oa, la)`: write the limb `1` at the top, subtract it, intern the result. -/
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
@[l_impl ConRon.Arena.natOpResult]
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

/-- Pushing one limb at the top is growing the pool. -/
theorem Grows.push1 (m : Mem) (t v : Word) (ht : t = m.top) (h : PoolOK m)
    (hs : (t &&& 1099511627775).toNat < (m.arr64 (tierA POOL (t >>> 40))).size) :
    Grows m ((m.set64 (tierA POOL (t >>> 40)) (t &&& 1099511627775) v).set64 CTL 0 (t + 1)) := by
  subst ht
  have h41 := h.top41
  have hsz := h.small.tier (m.top >>> 40)
  apply Grows.write m _ 1 h (PFrame.set64 _ _ _ (PFrame.refl m))
  · rw [vpool_stidx0 m m.top v h41 hs (by omega)]
    exact Agree.set _ _ _ _ _ (Agree.refl _ _) (Nat.le_refl _)
  · simp only [show (1 : Word).toNat = 1 from rfl]; omega
grind_pattern [arena_grind] Grows.push1 =>
  (m.set64 (tierA POOL (t >>> 40)) (t &&& 1099511627775) v).set64 CTL 0 (t + 1)

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
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        natSub_spec p hpl hps hpt hpn n, hI a₀ n] <;>
      finish (gen := 20) [natPredArm]

end pred

/-! ## `pow`, with con-leche's exponent bound -/

/-- `nat_pow_lit(oa, la, ob, lb)`: `(0, 0)` (the arm's `none`) for an exponent above `2^24`,
else `(1, h)` with `h` the interned power. An exponent of two or more limbs is at least `2^64`
(`b` normalised). -/
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
@[l_impl ConRon.Arena.natOpResult]
def natPowLit : FunDecl := lfn (oa, la, ob, lb) locals (e, o, l, h) {
  if 1 < lb { return (0, 0) };
  if lb == 1 { e := POOL⦃ob⦄ };
  if 16777216 < e { return (0, 0) };
  (o, l) := call nat_pow(oa, la, e);
  h := call intern_lit(o, l);
  return (1, h)
}

/-- The `Nat.pow` arm (`Arena/Core.lean:1008-1012`), verbatim. -/
def natPowArm (a b : Nat) : AM (Option EIdx) :=
  if b > 16777216 then pure none
  else do let x ← internE (.lit (.natVal (a ^ b))); pure (some x)

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

include hpool hgrow hI hph hpt hpm hpn in
theorem natPowLit_refines (hg : p.lookup "nat_pow_lit" = some natPowLit) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : R s₀.mem a₀) (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la)
    (hb : SliceOK s₀.mem ob lb)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_pow_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natPowArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      R s'.mem (AM.st (natPowArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natPowArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = decOpt (r.headD 0) (r.tail.headD 0); ⊤⦄ := by
  have hok := hpool _ _ hR
  have hbig := pv_two_limbs (vpool s₀.mem) ob.toNat lb.toNat hnb
  have hb1 := hb.1
  have h41 := hok.top41
  rw [invoke_eq _ hg]
  simp only [callFn, natPowLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natop_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        natPow_spec p hph hpt hpm hpn n, hI a₀ n] <;>
      finish (gen := 20) [natPowArm]

end pow

/-! ## `beq`, `ble`: a `Bool` constant -/

/-- `nat_beq_lit(oa, la, ob, lb, t, f, us)`: intern the constant `t` (`Bool.true`'s name) if the
two values are equal, else `f`, at the level list `us` (the empty one). The three handles are
the pins `boolTrueName`, `boolFalseName`, `emptyLevels`, which the caller reads. -/
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
@[l_impl ConRon.Arena.natOpResult]
def natBeqLit : FunDecl := lfn (oa, la, ob, lb, t, f, us) locals (c, h) {
  c := call nat_cmp(oa, la, ob, lb);
  if c != 1 { t := f };
  h := call intern_const(t, us);
  return h
}

/-- `nat_ble_lit`: as `nat_beq_lit`, `t` unless `a > b`. -/
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
@[l_impl ConRon.Arena.natOpResult]
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
-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult
@[l_impl ConRon.Arena.natOpResult]
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
      vcgen [exec, step, evalE, evalArgs, setLoc, setLocs,
        natGcd_spec p hpl hps hpc hp1 hp2 hp3 hp4 hpt hpd hps' hpg n, hI a₀ n] <;>
      finish [natGcdArm]

end gcd

/-! ## The arms, verbatim (`Arena/Core.lean:1004-1026`) -/

def natSubArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (a - b))); pure (some x)
def natMulArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (a * b))); pure (some x)
def natLandArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.land a b))); pure (some x)
def natLorArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.lor a b))); pure (some x)
def natXorArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.xor a b))); pure (some x)
def natShlArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.shiftLeft a b))); pure (some x)
def natShrArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (Nat.shiftRight a b))); pure (some x)
def natDivArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (a / b))); pure (some x)
def natModArm (a b : Nat) : AM (Option EIdx) := do
  let x ← internE (.lit (.natVal (a % b))); pure (some x)

/-! ## The dispatch (lane `pinsenv`)

`nat_op_result(c, oa, la, ob, lb)`: `natOpResult` (`Arena/Core.lean:998`) with the fifteen pin
reads as reads of `PINS` (word `1 + PIN_*`, after the flag) and the arms in the twin's order.
Returns `(1, h)` for `some h`, `(0, 0)` for `none` (`decOpt`). Refined in `PinsNatOp.lean`. -/
/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natOpResultL : FunDecl := lfn (c, oa, la, ob, lb) locals (f, h) {
  if PINS.u64[0] == 0 { abort };
  if c == PINS.u64[15] { h := call nat_pred_lit(oa, la); return (1, h) };
  if c == PINS.u64[16] { h := call nat_add_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[17] { h := call nat_sub_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[18] { h := call nat_mul_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[19] { (f, h) := call nat_pow_lit(oa, la, ob, lb); return (f, h) };
  if c == PINS.u64[22] { h := call nat_div_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[23] { h := call nat_mod_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[24] { h := call nat_gcd_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[25] { h := call nat_land_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[26] { h := call nat_lor_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[27] { h := call nat_xor_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[28] { h := call nat_shl_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[29] { h := call nat_shr_lit(oa, la, ob, lb); return (1, h) };
  if c == PINS.u64[20] {
    h := call nat_beq_lit(oa, la, ob, lb, PINS.u64[31], PINS.u64[32], PINS.u64[52]);
    return (1, h)
  };
  if c == PINS.u64[21] {
    h := call nat_ble_lit(oa, la, ob, lb, PINS.u64[31], PINS.u64[32], PINS.u64[52]);
    return (1, h)
  };
  return (0, 0)
}

/-! ## The program -/

/-- The pool functions, the `lit` store, and one L arm per operation. -/
def natArmProg : Prog := storeProg ++
  [("sub_borrow", subBorrow), ("nat_sub", natSub), ("mac_hi", macHi), ("nat_mul", natMul),
   ("nat_land", natLand), ("nat_lor", natLor), ("nat_xor", natXor), ("nat_shl", natShl),
   ("nat_shr", natShr),
   ("nat_sub_lit", topLit "nat_sub"), ("nat_mul_lit", topLit "nat_mul"),
   ("nat_land_lit", topLit "nat_land"), ("nat_lor_lit", topLit "nat_lor"),
   ("nat_xor_lit", topLit "nat_xor"), ("nat_shl_lit", topLit "nat_shl"),
   ("nat_shr_lit", topLit "nat_shr"),
   ("nat_pow", natPow), ("div_shl1", divShl1), ("div_sub", divSub), ("div_add", divAdd),
   ("div_step", divStep), ("nat_divmod", natDivmod),
   ("nat_pred_lit", natPredLit), ("nat_pow_lit", natPowLit), ("nat_div_lit", natDivLit),
   ("nat_mod_lit", natModLit),
   ("nat_cmp", natCmp), ("const_find", constFind), ("const_push", constPush),
   ("intern_const", internConst), ("nat_beq_lit", natBeqLit), ("nat_ble_lit", natBleLit),
   ("gcd_step", gcdStep), ("nat_gcd", natGcd), ("nat_gcd_lit", natGcdLit),
   ("nat_op_result", natOpResultL)]

/- `6 - 1 = 5`, `7 % 8 = 7`, `7 * 5 = 35` (at pool offset 9) and `35 / 5 = 7`: three nodes, and
the quotient finds `7`'s node again. -/
#guard
  let m : Mem := { words := #[(#[5, 7, 6, 8] ++ Array.replicate 60 0), #[4] ++ Array.replicate 63 0,
    Array.replicate 64 0, Array.replicate consTestWords 0] }
  let go (m : Mem) (f : FnName) (args : List Word) : Option (Word × Mem) :=
    match run natArmProg 100000 f args m with
    | .ok (r, m') => some (r.headD 0, m')
    | .error _ => none
  match go m "nat_pred_lit" [2, 1] with
  | some (h₁, m) => match go m "nat_mod_lit" [1, 1, 3, 1] with
    | some (h₂, m) => match go m "nat_mul_lit" [1, 1, 0, 1] with
      | some (h₃, m) => match go m "nat_div_lit" [9, 1, 0, 1] with
        | some (h₄, _) => [h₁, h₂, h₃, h₄] == [0x80000000, 0x80000001, 0x80000002, 0x80000001]
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

/-- **`nat_sub_lit` refines `natOpResult`'s `Nat.sub` arm under `ArenaR`.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.sub"]
theorem natSubLit_refinesA : ArmRefinesA "nat_sub_lit" natSubArm :=
  topLit_refinesA "nat_sub_lit" "nat_sub" _ rfl natSub_top
/-- **`nat_mul_lit` refines the `Nat.mul` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.mul"]
theorem natMulLit_refinesA : ArmRefinesA "nat_mul_lit" natMulArm :=
  topLit_refinesA "nat_mul_lit" "nat_mul" _ rfl natMul_top
/-- **`nat_land_lit` refines the `Nat.land` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.land"]
theorem natLandLit_refinesA : ArmRefinesA "nat_land_lit" natLandArm :=
  topLit_refinesA "nat_land_lit" "nat_land" _ rfl natLand_top
/-- **`nat_lor_lit` refines the `Nat.lor` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.lor"]
theorem natLorLit_refinesA : ArmRefinesA "nat_lor_lit" natLorArm :=
  topLit_refinesA "nat_lor_lit" "nat_lor" _ rfl natLor_top
/-- **`nat_xor_lit` refines the `Nat.xor` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.xor"]
theorem natXorLit_refinesA : ArmRefinesA "nat_xor_lit" natXorArm :=
  topLit_refinesA "nat_xor_lit" "nat_xor" _ rfl natXor_top
/-- **`nat_shl_lit` refines the `Nat.shiftLeft` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.shiftLeft"]
theorem natShlLit_refinesA : ArmRefinesA "nat_shl_lit" natShlArm :=
  topLit_refinesA "nat_shl_lit" "nat_shl" _ rfl natShl_top
/-- **`nat_shr_lit` refines the `Nat.shiftRight` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.shiftRight"]
theorem natShrLit_refinesA : ArmRefinesA "nat_shr_lit" natShrArm :=
  topLit_refinesA "nat_shr_lit" "nat_shr" _ rfl natShr_top

/-- **`nat_div_lit` refines the `Nat.div` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.div"]
theorem natDivLit_refinesA : ArmRefinesA "nat_div_lit" natDivArm :=
  fun n s₀ a₀ hR oa la ob lb ha hb _ hnb hmode =>
    natDivLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hnb hmode

/-- **`nat_mod_lit` refines the `Nat.mod` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.mod"]
theorem natModLit_refinesA : ArmRefinesA "nat_mod_lit" natModArm :=
  fun n s₀ a₀ hR oa la ob lb ha hb _ hnb hmode =>
    natModLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hnb hmode

/-- **`nat_pred_lit` refines the `Nat.pred` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.pred"]
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

/-- **`nat_pow_lit` refines the `Nat.pow` arm**, including its `none` above `2^24`. -/
@[refines_part ConRon.Arena.natOpResult "Nat.pow"]
theorem natPowLit_refinesA (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀)
    (oa la ob lb : Word) (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke natArmProg (exec natArmProg n) "nat_pow_lit" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (natPowArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ ∧
      ArenaR s'.mem (AM.st (natPowArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀) ∧
      AM.res (natPowArm (pv (vpool s₀.mem) oa.toNat la.toNat)
        (pv (vpool s₀.mem) ob.toNat lb.toNat)) a₀ = decOpt (r.headD 0) (r.tail.headD 0); ⊤⦄ :=
  natPowLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
    (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl n s₀ a₀ hR
    oa la ob lb ha hb hnb hmode

/-- **`nat_beq_lit` refines the `Nat.beq` arm under `ArenaR`**, given what the three pin reads
return in the arena state (they read it and do not change it). -/
@[refines_part ConRon.Arena.natOpResult "Nat.beq"]
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
  simp only [PoolOK, SliceOK] at hok ha hb
  rw [invoke_eq _ (show natArmProg.lookup "nat_beq_lit" = some natBeqLit from rfl)]
  simp only [callFn, natBeqLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natcmp_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        natCmp_spec natArmProg rfl n, internConst_refinesA natArmProg rfl rfl rfl a₀ n] <;>
      finish [natBeqArm, constE, decE_eq]

/-- **`nat_ble_lit` refines the `Nat.ble` arm under `ArenaR`**, given the three pin reads. -/
@[refines_part ConRon.Arena.natOpResult "Nat.ble"]
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
  simp only [PoolOK, SliceOK] at hok ha hb
  rw [invoke_eq _ (show natArmProg.lookup "nat_ble_lit" = some natBleLit from rfl)]
  simp only [callFn, natBleLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, natcmp_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        natCmp_spec natArmProg rfl n, internConst_refinesA natArmProg rfl rfl rfl a₀ n] <;>
      finish [natBleArm, constE, decE_eq]

/-- **`nat_gcd_lit` refines the `Nat.gcd` arm.** -/
@[refines_part ConRon.Arena.natOpResult "Nat.gcd"]
theorem natGcdLit_refinesA : ArmRefinesA "nat_gcd_lit" natGcdArm :=
  fun n s₀ a₀ hR oa la ob lb ha hb hna hnb hmode =>
    natGcdLit_refines natArmProg ArenaR (fun _ _ h => h.lit.1)
      (fun m m' a hR hg => ArenaR.grow m m' hg a hR) internLit_arms rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl n s₀ a₀ hR oa la ob lb ha hb hna hnb hmode

end L.Arena
