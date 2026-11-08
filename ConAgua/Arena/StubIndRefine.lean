module

public import ConAgua.Arena.StubInd
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.WhnfM2CRefine5
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfIotaRefine6
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.DeclCanonSpec
public import ConAgua.Arena.DeclNatBase
public import ConAgua.Arena.WhnfEntry
public import ConAgua.Arena.WhnfIota
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.WhnfEntry

@[expose] public section

/-!
# `rec_rule_bits` refines `recRuleBits` (lane `tails`)

`StubInd.lean`'s `ctor_family`, `rec_rule_k_of`, `rec_rule_eta_of`, `rec_rule_bits` (lane
`stubs`), under the inductive stage's relation `StageR` in its `RefAM` shape (for lane
`indproofs3`'s `IndStubs.recRuleBits_spec`). Every function here reads only: the memory and the
twin's state are unchanged. The shared prefix `ctor_family(vis, c)` is `iota_ctor_never_prop`'s
(`WhnfIotaRefine6.lean`): the constructor's record, its type's Π-result's head (`pi_result_f`,
`get_app_fn_f` at `CWF`, the twin's `coreWalkFuel`), the head's name (`const_name_of`) and its
record; `CFOut` says what its two words mean for the twin, as a tail `famTail g hh` that both bits
share.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Stubs

open L.Arena L.Ind

/-! ## Models (callees through `callW`) and their specs -/

/-- The fuel adapter `get_app_fn_f(f, e)`: `get_app_fn(e)` at `f = CWF`. -/
def gaffW (p : Prog) (n : Nat) (m : Mem) (f e : Word) : Option (List Word × Mem) :=
  if f ≠ CWF then none else
  ntBW (callW p n "get_app_fn" [e] m) fun r m' => some ([r.headD 0], m')

/-- The fuel adapter `pi_result_f(f, e)`: `pi_result(e)` at `f = CWF`. -/
def pirfW (p : Prog) (n : Nat) (m : Mem) (f e : Word) : Option (List Word × Mem) :=
  if f ≠ CWF then none else
  ntBW (callW p n "pi_result" [e] m) fun r m' => some ([r.headD 0], m')

theorem gaff_spec (p : Prog) (hp : p.lookup "get_app_fn_f" = some getAppFnFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "get_app_fn_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ gaffW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, getAppFnFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "get_app_fn"] <;>
    finish (gen := 20) [gaffW, ntBW, CWF]

theorem pirf_spec (p : Prog) (hp : p.lookup "pi_result_f" = some piResultFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_result_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pirfW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, piResultFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "pi_result"] <;>
    finish (gen := 20) [pirfW, ntBW, CWF]

/-- The model of `ctor_family(vis, c)` (callees at fuel `n`). -/
def cfW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "env_find" [c, vis] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0, 0, 0], m1) else
  if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 4 then some ([0, 0, 0], m1) else
  ntBW (callW p n "pi_result_f" [CWF, rdW (m1.arr64 EREC) (r1.tail.headD 0 + 4)] m1) fun r2 m2 =>
  ntBW (callW p n "get_app_fn_f" [CWF, r2.headD 0] m2) fun r3 m3 =>
  if tagW (r3.headD 0) ≠ 3 then some ([r1.tail.headD 0, 0, 0], m3) else
  ntBW (callW p n "const_name_of" [r3.headD 0] m3) fun r4 m4 =>
  ntBW (callW p n "env_find" [r4.headD 0, vis] m4) fun r5 m5 =>
  if r5.headD 0 = 0 then some ([r1.tail.headD 0, 0, 0], m5) else
  if rdW (m5.arr64 EREC) (r5.tail.headD 0) ≠ 3 then some ([r1.tail.headD 0, 0, 0], m5) else
  some ([r1.tail.headD 0, r5.tail.headD 0, 1], m5)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cf_spec (p : Prog) (hp : p.lookup "ctor_family" = some ctorFamily) (n : Nat) (s₀ : St)
    (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ctor_family" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ cfW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  sorry

-/

/-- The model of `rec_rule_k_of(vis, c)`. -/
def kofW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "ctor_family" [vis, c] m) fun r m1 =>
  if r.tail.tail.headD 0 = 0 then some ([0], m1) else
  if rdW (m1.arr64 EREC) (r.tail.headD 0 + 11) ≠ 0 ∧ rdW (m1.arr64 EREC) (r.headD 0 + 6) = 0 then
    some ([1], m1)
  else some ([0], m1)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem kof_spec (p : Prog) (hp : p.lookup "rec_rule_k_of" = some recRuleKOfL) (n : Nat)
    (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rec_rule_k_of" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ kofW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  sorry

-/

/-- The model of `rec_rule_eta_of(vis, c)`. -/
def eofW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "ctor_family" [vis, c] m) fun r m1 =>
  if r.tail.tail.headD 0 = 0 then some ([0], m1) else
  if rdW (m1.arr64 EREC) (r.tail.headD 0 + 5) = 0 then some ([0], m1) else
  if rdW (m1.arr64 EREC) (r.tail.headD 0 + 6) ≠ c then some ([0], m1) else
  ntBW (callW p n "er_sl_eq" [rdW (m1.arr64 EREC) (r.headD 0 + 2), rdW (m1.arr64 EREC) (r.headD 0 + 3),
    rdW (m1.arr64 EREC) (r.tail.headD 0 + 2), rdW (m1.arr64 EREC) (r.tail.headD 0 + 3)] m1) fun x m2 =>
  some ([x.headD 0], m2)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem eof_spec (p : Prog) (hp : p.lookup "rec_rule_eta_of" = some recRuleEtaOfL) (n : Nat)
    (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rec_rule_eta_of" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ eofW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  sorry

-/

/-- The model of `rec_rule_bits(vis, c)`. -/
def rrbW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rec_rule_k_of" [vis, c] m) fun k m1 =>
  ntBW (callW p n "rec_rule_eta_of" [vis, c] m1) fun e m2 => some ([k.headD 0, e.headD 0], m2)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem rrb_spec (p : Prog) (hp : p.lookup "rec_rule_bits" = some recRuleBitsL) (n : Nat)
    (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rec_rule_bits" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rrbW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  sorry

-/

/-! ## The records' fields (decoded on the record pool itself) -/

section fields
variable {b : Array Word} {dn : NIdx → Option ConLeche.Name}

theorem rdW_off {q : Word} {k : Nat} {w : Word} (hsz : b.size < 2 ^ 64) (hk : k < 64)
    (h : b[q.toNat + k]? = some w) : rdW b (q + UInt64.ofNat k) = w := by
  have hlt : q.toNat + k < b.size := (Array.getElem?_eq_some_iff.mp h).1
  have e : (q + UInt64.ofNat k).toNat = q.toNat + k := by
    rw [UInt64.toNat_add]
    have : (UInt64.ofNat k).toNat = k := by simp; omega
    rw [this]; omega
  simp [rdW, e, h]

theorem nat?_w {i k : Nat} (h : nat? (aread b) i = some k) : ∃ w, b[i]? = some w ∧ w.toNat = k := by
  simp only [nat?, Option.map_eq_some_iff] at h; exact h

theorem bool?_w {i : Nat} {x : Bool} (h : bool? (aread b) i = some x) : ∃ w, b[i]? = some w ∧ (w != 0) = x := by
  simp only [bool?, Option.map_eq_some_iff] at h; exact h

theorem hd?_w {k : IdxKind} {i : Nat} {x : Idx k} (h : hd? (aread b) i = some x) :
    ∃ w, b[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, h⟩ := h
  split at h
  · exact ⟨w, hw, by assumption, (Option.some.inj h).symm⟩
  · cases h

theorem decCV_lp {q : Nat} {cv : IConstantVal} (h : decCV (aread b) q = some cv) :
    hlist? (aread b) (q + 1) = some cv.levelParams := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, ls, hls, _, _, hq⟩ := h
  rw [← Option.some.inj hq]; exact hls

theorem decCV_ty {q : Nat} {cv : IConstantVal} (h : decCV (aread b) q = some cv) :
    hd? (aread b) (q + 3) = some cv.type := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, hd, hq⟩ := h
  rw [← Option.some.inj hq]; exact hd

/-- A constructor record's words. -/
theorem decCI_ctorW {q : Nat} {cv : IConstantVal} {np nf : Nat}
    (h : decCI (aread b) q = some (.ctorInfo cv np nf)) :
    nat? (aread b) q = some 4 ∧ decCV (aread b) (q + 1) = some cv ∧ nat? (aread b) (q + 6) = some nf := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_false, and_false] at h
  obtain ⟨cv', hcv, np', -, nf', hnf, hc⟩ := h
  simp only [IConstantInfo.ctorInfo.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  exact ⟨hk, hcv, hnf⟩

/-- An inductive record's words. -/
theorem decCI_indW {q : Nat} {cv : IConstantVal} {caps : IIndCaps}
    (h : decCI (aread b) q = some (.indInfo cv caps)) :
    nat? (aread b) q = some 3 ∧ decCV (aread b) (q + 1) = some cv ∧ decCaps (aread b) (q + 5) = some caps := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_false, and_false] at h
  obtain ⟨cv', hcv, caps', hcaps, hc⟩ := h
  simp only [IConstantInfo.indInfo.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨hk, hcv, hcaps⟩

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem decCaps_w {q : Nat} {caps : IIndCaps} (h : decCaps (aread b) q = some caps) :
    bool? (aread b) q = some caps.eta ∧ hd? (aread b) (q + 1) = some caps.etaCtor ∧ bool? (aread b) (q + 6) = some caps.ruleK := by
  sorry

-/

end fields

/-! ## The twin's shared block -/

/-- The twin's block both bits share, after the constructor `cv`'s lookup: its type's Π-result's
head; if a `const` naming an inductive `cvT`/`caps`, `g cvT caps`, else `false`. -/
def famBlk (fe : IFEnv) (g : IConstantVal → IIndCaps → Bool) (cv : IConstantVal) : AM Bool := do
  let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cv.type)
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T _ =>
      match fe.find? T with
      | some (.indInfo cvT caps) => pure (g cvT caps)
      | _ => pure false
    | _ => pure false
  else pure false

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem recRuleKOf_blk (fe : IFEnv) (ctor : NIdx) :
    recRuleKOf fe ctor = (match fe.find? ctor with
      | some (.ctorInfo cvj _ cnF) => famBlk fe (fun _ caps => caps.ruleK && cnF == 0) cvj
      | _ => pure false) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem recRuleEtaOf_blk (fe : IFEnv) (ctor : NIdx) :
    recRuleEtaOf fe ctor = (match fe.find? ctor with
      | some (.ctorInfo cvj _ _) => famBlk fe (fun cvT caps =>
          caps.eta && caps.etaCtor == ctor && cvj.levelParams == cvT.levelParams) cvj
      | _ => pure false) := by
  sorry

-/

section famRun
variable (fe : IFEnv) (g : IConstantVal → IIndCaps → Bool) (cv : IConstantVal) (a : AState)
  (pr hh : EIdx)
  (hpr : (piResult coreWalkFuel cv.type).run a = .ok (pr, a))
  (hga : (getAppFn coreWalkFuel pr).run a = .ok (hh, a))
include hpr hga

theorem famBlk_not (ht : hh.tag ≠ ETag.const) : (famBlk fe g cv).run a = .ok (false, a) := by
  have : (hh.tag == ETag.const) = false := by simpa using ht
  simp only [famBlk, StateT.run_bind, hpr, except_ok_bind, hga, this]
  simp; rfl

theorem famBlk_other (T : NIdx) (us : LsIdx) (hv : a.store.view hh = some (.const T us))
    (ht : hh.tag = ETag.const) (hf : ∀ cvT caps, fe.find? T ≠ some (.indInfo cvT caps)) :
    (famBlk fe g cv).run a = .ok (false, a) := by
  simp only [famBlk, StateT.run_bind, hpr, except_ok_bind, hga, ht, beq_self_eq_true, ↓reduceIte,
    view_run hh a _ hv]
  cases hfi : fe.find? T with
  | none => simp; rfl
  | some ci =>
    cases ci with
    | indInfo cvT caps => exact absurd hfi (hf cvT caps)
    | _ => simp; rfl

theorem famBlk_ind (T : NIdx) (us : LsIdx) (hv : a.store.view hh = some (.const T us))
    (ht : hh.tag = ETag.const) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) :
    (famBlk fe g cv).run a = .ok (g cvT caps, a) := by
  simp only [famBlk, StateT.run_bind, hpr, except_ok_bind, hga, ht, beq_self_eq_true, ↓reduceIte,
    view_run hh a _ hv, hf]
  rfl

end famRun

/-! ## `ctor_family` against the twin -/

/-- The lookups the refinements need. -/
structure RrbProg (p : Prog) : Prop where
  envrow : p.lookup "env_row_get" = some envRowGetL
  envfind : p.lookup "env_find" = some envFindL
  pires : p.lookup "pi_result" = some piResultL
  gaf : p.lookup "get_app_fn" = some getAppFnL
  pirf : p.lookup "pi_result_f" = some piResultFL
  gaff : p.lookup "get_app_fn_f" = some getAppFnFL
  cno : p.lookup "const_name_of" = some constNameOfL
  ersl : p.lookup "er_sl_eq" = some L.Ind.erSlEq

/-- The twin's lookup of `c` followed by the shared block at `G` (the bit's test, given the
constructor's value and field count). -/
def famT (fe : IFEnv) (G : IConstantVal → Nat → IConstantVal → IIndCaps → Bool) (c : NIdx) :
    AM Bool :=
  match fe.find? c with
  | some (.ctorInfo cvj _ nF) => famBlk fe (G cvj nF) cvj
  | _ => pure false

/-- **What `ctor_family`'s three words mean**: at flag `0` the twin's lookup-and-block answers
`false` for every test `G`; at flag `≠ 0` the words are the records of the constructor and of the
inductive, and the block answers `G` at them. -/
def CFOut (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (a : AState) (m : Mem) (c : Word)
    (r : List Word) : Prop :=
  ∀ G : IConstantVal → Nat → IConstantVal → IIndCaps → Bool,
    (r.tail.tail.headD 0 = 0 → (famT fe G (decI c)).run a = .ok (false, a)) ∧
    (r.tail.tail.headD 0 ≠ 0 → ∃ cvj np nF cvT caps,
      decCI (erecP m) (r.headD 0).toNat = some (.ctorInfo cvj np nF) ∧
      decCI (erecP m) (r.tail.headD 0).toNat = some (.indInfo cvT caps) ∧
      (famT fe G (decI c)).run a = .ok (G cvj nF cvT caps, a))

theorem famT_none {fe : IFEnv} {G : IConstantVal → Nat → IConstantVal → IIndCaps → Bool} {c : NIdx}
    {a : AState} (h : ∀ cv np nf, fe.find? c ≠ some (.ctorInfo cv np nf)) :
    (famT fe G c).run a = .ok (false, a) := by
  unfold famT
  cases hf : fe.find? c with
  | none => rfl
  | some ci =>
    cases ci with
    | ctorInfo cv np nf => exact absurd hf (h cv np nf)
    | _ => rfl

theorem rdW_of_get {b : Array Word} {q : Word} {w : Word} (h : b[q.toNat]? = some w) : rdW b q = w := by
  simp [rdW, h]

/-- A found row that is not of kind `k` is not that kind's record. -/
theorem kind_of_rdW {b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word} {ci : IConstantInfo}
    (h : decCI (aread b) q.toNat = some ci) :
    ((∃ cv caps, ci = .indInfo cv caps) ↔ rdW b q = 3) ∧
      ((∃ cv nP nF, ci = .ctorInfo cv nP nF) ↔ rdW b q = 4) := by
  obtain ⟨w, hw, h3, h4⟩ := decCI_kind34 b dn q.toNat ci h
  rw [rdW_of_get hw]; exact ⟨h3, h4⟩

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cfW_ok {p : Prog} (hp : RrbProg p) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (m m' : Mem) (a : AState) (hS : StageR vis fe m a) (c : Word) (hc : H c)
    (r : List Word) (hW : cfW p n m vis c = some (r, m')) :
    m' = m ∧ CFOut dn fe a m c r := by
  sorry

-- RS2E

/-! ## The two bits and the rule's bits -/

theorem erSlEq_spec' (p : Prog) (hp : p.lookup "er_sl_eq" = some L.Ind.erSlEq) (n : Nat) :
    ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_sl_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r.headD 0 = if erSlEqB (s₀.mem.arr64 EREC) o1 l1 o2 l2 then 1 else 0; ⊤⦄ := by
  sorry

section bits
variable {p : Prog} (hp : RrbProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
include hp

theorem cf_call (k : Nat) (m m1 : Mem) (a : AState) (hS : StageR vis fe m a) (c : Word) (hc : H c)
    (rf : List Word) (h : callW p k "ctor_family" [vis, c] m = some (rf, m1)) :
    m1 = m ∧ CFOut dn fe a m c rf := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rec_rule_k_of(vis, c)` refines `recRuleKOf fe c`** (the K bit). -/
theorem recRuleKOf_ref (c : Word) (hc : H c) :
    CallRef p "rec_rule_k_of" [vis, c] (StageR vis fe) (recRuleKOf fe (decI c))
      (KeepPost vis fe decW0B) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rec_rule_eta_of(vis, c)` refines `recRuleEtaOf fe c`** (the η-rescue bit). -/
theorem recRuleEtaOf_ref (c : Word) (hc : H c) :
    CallRef p "rec_rule_eta_of" [vis, c] (StageR vis fe) (recRuleEtaOf fe (decI c))
      (KeepPost vis fe decW0B) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rec_rule_bits(vis, c)` refines `recRuleBits fe rl`** for a rule with constructor `c`: the
two words are the rule's new bits. -/
theorem recRuleBits_ref (c : Word) (hc : H c) (rl : IRecRule) (hrl : rl.ctor = decI c) :
    CallRef p "rec_rule_bits" [vis, c] (StageR vis fe) (recRuleBits fe rl)
      (KeepPost vis fe (fun _ r (x : IRecRule) =>
        x = { rl with k := r.headD 0 != 0, eta := r.tail.headD 0 != 0 })) := by
  sorry

-/

end bits

/-! ## The census theorems (`RefAM`, the shape of `IndStubs.lean`'s contracts) -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rec_rule_k_of` refines `recRuleKOf`** under `StageR`. -/
@[refines ConRon.Arena.recRuleKOf]
theorem recRuleKOf_refines {p : Prog} (hp : RrbProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (c : Word) (hc : H c) :
    RefAM p "rec_rule_k_of" [vis, c] (StageR vis fe) (recRuleKOf fe (decI c))
      (KeepPost vis fe decW0B) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rec_rule_eta_of` refines `recRuleEtaOf`** under `StageR`. -/
@[refines ConRon.Arena.recRuleEtaOf]
theorem recRuleEtaOf_refines {p : Prog} (hp : RrbProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (c : Word) (hc : H c) :
    RefAM p "rec_rule_eta_of" [vis, c] (StageR vis fe) (recRuleEtaOf fe (decI c))
      (KeepPost vis fe decW0B) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`rec_rule_bits` refines `recRuleBits`** under `StageR`: the shape of
`IndStubs.recRuleBits_spec`. -/
@[refines ConRon.Arena.recRuleBits]
theorem recRuleBits_refines {p : Prog} (hp : RrbProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (c : Word) (hc : H c) (rl : IRecRule) (hrl : rl.ctor = decI c) :
    RefAM p "rec_rule_bits" [vis, c] (StageR vis fe) (recRuleBits fe rl)
      (KeepPost vis fe (fun _ r (x : IRecRule) =>
        x = { rl with k := r.headD 0 != 0, eta := r.tail.headD 0 != 0 })) := by
  sorry

-/

end L.Stubs
