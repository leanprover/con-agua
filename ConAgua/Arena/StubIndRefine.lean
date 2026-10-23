import ConAgua.Arena.StubInd
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.DeclCanonSpec
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclNatBase
import ConAgua.Arena.DeclNatDeps
import ConAgua.Arena.WhnfM2CRefine5
import ConAgua.Census.Attr

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

theorem rdW_of_lt {a : Array Word} {x : Word} (h : x.toNat < a.size) : rdW a x = a[x.toNat] := by
  simp [rdW, h]

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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "get_app_fn"] <;>
    finish (gen := 20) [gaffW, ntBW, CWF]

theorem pirf_spec (p : Prog) (hp : p.lookup "pi_result_f" = some piResultFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_result_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pirfW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, piResultFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "pi_result"] <;>
    finish (gen := 20) [pirfW, ntBW, CWF]

/-- The model of `ctor_family(vis, c)` (callees at fuel `n`). -/
def cfW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "env_find" [c, vis] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0, 0, 0], m1) else
  if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 4 then some ([0, 0, 0], m1) else
  ntBW (callW p n "pi_result_f" [CWF, rdW (m1.arr64 EREC) (r1.tail.headD 0 + 4)] m1) fun r2 m2 =>
  ntBW (callW p n "get_app_fn_f" [CWF, r2.headD 0] m2) fun r3 m3 =>
  if r3.headD 0 >>> 28 ≠ 3 then some ([r1.tail.headD 0, 0, 0], m3) else
  ntBW (callW p n "const_name_of" [r3.headD 0] m3) fun r4 m4 =>
  ntBW (callW p n "env_find" [r4.headD 0, vis] m4) fun r5 m5 =>
  if r5.headD 0 = 0 then some ([r1.tail.headD 0, 0, 0], m5) else
  if rdW (m5.arr64 EREC) (r5.tail.headD 0) ≠ 3 then some ([r1.tail.headD 0, 0, 0], m5) else
  some ([r1.tail.headD 0, r5.tail.headD 0, 1], m5)

theorem cf_spec (p : Prog) (hp : p.lookup "ctor_family" = some ctorFamily) (n : Nat) (s₀ : St)
    (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ctor_family" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ cfW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ctorFamily]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "env_find", callW_spec p n "pi_result_f", callW_spec p n "get_app_fn_f",
    callW_spec p n "const_name_of"] <;>
    finish (gen := 20) [cfW, ntBW, CWF]

/-- The model of `rec_rule_k_of(vis, c)`. -/
def kofW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "ctor_family" [vis, c] m) fun r m1 =>
  if r.tail.tail.headD 0 = 0 then some ([0], m1) else
  if rdW (m1.arr64 EREC) (r.tail.headD 0 + 11) ≠ 0 ∧ rdW (m1.arr64 EREC) (r.headD 0 + 6) = 0 then
    some ([1], m1)
  else some ([0], m1)

theorem kof_spec (p : Prog) (hp : p.lookup "rec_rule_k_of" = some recRuleKOfL) (n : Nat)
    (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rec_rule_k_of" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ kofW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recRuleKOfL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "ctor_family"] <;>
    finish (gen := 20) [kofW, ntBW, CWF]

/-- The model of `rec_rule_eta_of(vis, c)`. -/
def eofW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "ctor_family" [vis, c] m) fun r m1 =>
  if r.tail.tail.headD 0 = 0 then some ([0], m1) else
  if rdW (m1.arr64 EREC) (r.tail.headD 0 + 5) = 0 then some ([0], m1) else
  if rdW (m1.arr64 EREC) (r.tail.headD 0 + 6) ≠ c then some ([0], m1) else
  ntBW (callW p n "er_sl_eq" [rdW (m1.arr64 EREC) (r.headD 0 + 2), rdW (m1.arr64 EREC) (r.headD 0 + 3),
    rdW (m1.arr64 EREC) (r.tail.headD 0 + 2), rdW (m1.arr64 EREC) (r.tail.headD 0 + 3)] m1) fun x m2 =>
  some ([x.headD 0], m2)

theorem eof_spec (p : Prog) (hp : p.lookup "rec_rule_eta_of" = some recRuleEtaOfL) (n : Nat)
    (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rec_rule_eta_of" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ eofW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recRuleEtaOfL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "ctor_family",
    callW_spec p n "er_sl_eq"] <;>
    finish (gen := 20) [eofW, ntBW, CWF]

/-- The model of `rec_rule_bits(vis, c)`. -/
def rrbW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "rec_rule_k_of" [vis, c] m) fun k m1 =>
  ntBW (callW p n "rec_rule_eta_of" [vis, c] m1) fun e m2 => some ([k.headD 0, e.headD 0], m2)

theorem rrb_spec (p : Prog) (hp : p.lookup "rec_rule_bits" = some recRuleBitsL) (n : Nat)
    (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rec_rule_bits" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rrbW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recRuleBitsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "rec_rule_k_of",
    callW_spec p n "rec_rule_eta_of"] <;>
    finish (gen := 20) [rrbW, ntBW, CWF]

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

theorem rdW_at {q : Word} {w : Word} (h : b[q.toNat]? = some w) : rdW b q = w := by
  simp [rdW, h]

theorem nat?_w {i k : Nat} (h : nat? b i = some k) : ∃ w, b[i]? = some w ∧ w.toNat = k := by
  simp only [nat?, Option.map_eq_some_iff] at h; exact h

theorem bool?_w {i : Nat} {x : Bool} (h : bool? b i = some x) : ∃ w, b[i]? = some w ∧ (w != 0) = x := by
  simp only [bool?, Option.map_eq_some_iff] at h; exact h

theorem hd?_w {k : IdxKind} {i : Nat} {x : Idx k} (h : hd? b i = some x) :
    ∃ w, b[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, h⟩ := h
  split at h
  · exact ⟨w, hw, by assumption, (Option.some.inj h).symm⟩
  · cases h

theorem decCV_lp {q : Nat} {cv : IConstantVal} (h : decCV b q = some cv) :
    hlist? b (q + 1) = some cv.levelParams := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, ls, hls, _, _, hq⟩ := h
  rw [← Option.some.inj hq]; exact hls

theorem decCV_ty {q : Nat} {cv : IConstantVal} (h : decCV b q = some cv) :
    hd? b (q + 3) = some cv.type := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, hd, hq⟩ := h
  rw [← Option.some.inj hq]; exact hd

/-- A constructor record's words. -/
theorem decCI_ctorW {q : Nat} {cv : IConstantVal} {np nf : Nat}
    (h : decCI b dn q = some (.ctorInfo cv np nf)) :
    nat? b q = some 4 ∧ decCV b (q + 1) = some cv ∧ nat? b (q + 6) = some nf := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_false, and_false,
      false_and, exists_const] at h
  obtain ⟨cv', hcv, np', -, nf', hnf, hc⟩ := h
  simp only [IConstantInfo.ctorInfo.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  exact ⟨hk, hcv, hnf⟩

/-- An inductive record's words. -/
theorem decCI_indW {q : Nat} {cv : IConstantVal} {caps : IIndCaps}
    (h : decCI b dn q = some (.indInfo cv caps)) :
    nat? b q = some 3 ∧ decCV b (q + 1) = some cv ∧ decCaps b dn (q + 5) = some caps := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_false, and_false,
      false_and, exists_const] at h
  obtain ⟨cv', hcv, caps', hcaps, hc⟩ := h
  simp only [IConstantInfo.indInfo.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨hk, hcv, hcaps⟩

theorem decCaps_w {q : Nat} {caps : IIndCaps} (h : decCaps b dn q = some caps) :
    bool? b q = some caps.eta ∧ hd? b (q + 1) = some caps.etaCtor ∧ bool? b (q + 6) = some caps.ruleK := by
  simp only [decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨e1, h1, e2, h2, _, _, _, _, _, _, _, _, e7, h7, _, _, _, _, _, _, _, _, e⟩ := h
  cases Option.some.inj e; exact ⟨h1, h2, h7⟩

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

theorem recRuleKOf_blk (fe : IFEnv) (ctor : NIdx) :
    recRuleKOf fe ctor = (match fe.find? ctor with
      | some (.ctorInfo cvj _ cnF) => famBlk fe (fun _ caps => caps.ruleK && cnF == 0) cvj
      | _ => pure false) := by
  unfold recRuleKOf famBlk
  rcases fe.find? ctor with _ | ⟨⟩ <;> rfl

theorem recRuleEtaOf_blk (fe : IFEnv) (ctor : NIdx) :
    recRuleEtaOf fe ctor = (match fe.find? ctor with
      | some (.ctorInfo cvj _ _) => famBlk fe (fun cvT caps =>
          caps.eta && caps.etaCtor == ctor && cvj.levelParams == cvT.levelParams) cvj
      | _ => pure false) := by
  unfold recRuleEtaOf famBlk
  rcases fe.find? ctor with _ | ⟨⟩ <;> rfl

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
  envix : p.lookup "env_ix" = some envIxL
  envrow : p.lookup "env_row_get" = some envRowGetL
  envfind : p.lookup "env_find" = some envFindL
  pires : p.lookup "pi_result" = some piResultL
  gaf : p.lookup "get_app_fn" = some getAppFnL
  pirf : p.lookup "pi_result_f" = some piResultFL
  gaff : p.lookup "get_app_fn_f" = some getAppFnFL
  cno : p.lookup "const_name_of" = some constNameOfL
  ersl : p.lookup "er_sl_eq" = some L.Ind.erSlEq
  cf : p.lookup "ctor_family" = some ctorFamily
  kof : p.lookup "rec_rule_k_of" = some recRuleKOfL
  eof : p.lookup "rec_rule_eta_of" = some recRuleEtaOfL
  bits : p.lookup "rec_rule_bits" = some recRuleBitsL

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
      decCI (m.arr64 EREC) dn (r.headD 0).toNat = some (.ctorInfo cvj np nF) ∧
      decCI (m.arr64 EREC) dn (r.tail.headD 0).toNat = some (.indInfo cvT caps) ∧
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
    (h : decCI b dn q.toNat = some ci) :
    ((∃ cv caps, ci = .indInfo cv caps) ↔ rdW b q = 3) ∧
      ((∃ cv nP nF, ci = .ctorInfo cv nP nF) ↔ rdW b q = 4) := by
  obtain ⟨w, hw, h3, h4⟩ := decCI_kind34 b dn q.toNat ci h
  rw [rdW_of_get hw]; exact ⟨h3, h4⟩

theorem cfW_ok {p : Prog} (hp : RrbProg p) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (m m' : Mem) (a : AState) (hS : StageR dn vis fe m a) (c : Word) (hc : H c)
    (r : List Word) (hW : cfW p n m vis c = some (r, m')) :
    m' = m ∧ CFOut dn fe a m c r := by
  have hR := hS.1.arena.1
  have hE := hS.1.env
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  simp only [cfW] at hW
  cases n with
  | zero => simp [callW_zero] at hW
  | succ k =>
  cases c1 : callW p (k + 1) "env_find" [c, vis] m with
  | none => rw [c1] at hW; simp at hW
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, bW_some] at hW
  obtain ⟨t1, ht1, hm1, -, hfind1⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind (k + 1) ⟨m, Locals.init []⟩ vis c hE hc) c1
  obtain ⟨t1', ht1', -, -, hfound1⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind (k + 1) ⟨m, Locals.init []⟩ vis c hc) c1
  have e_m1 : m = m1 := by rw [← ht1, hm1]
  subst e_m1
  simp only at hfind1 hfound1
  by_cases h0 : r1.headD 0 = 0
  · rw [if_pos h0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hnone : fe.find? (decI c) = none := by rw [hfind1, decFound, if_pos h0]
    refine ⟨rfl, fun G => ⟨fun _ => famT_none (fun cv np nf h => by rw [hnone] at h; cases h),
      fun h => absurd rfl h⟩⟩
  rw [if_neg h0] at hW
  obtain ⟨htag1, hrow1, hq1⟩ := hfound1 h0
  obtain ⟨ci, hci⟩ := hE.found_some c hc htag1 hrow1
  have hfi : fe.find? (decI c) = some ci := by
    rw [hfind1]; simp only [decFound, h0, ↓reduceIte, hq1]; exact hci
  rw [← hq1] at hci
  have hciB := ArrExt.decCI (erecP_ext m) hci
  have hk := kind_of_rdW hciB
  by_cases h4 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 4
  · rw [if_pos h4] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨rfl, fun G => ⟨fun _ => famT_none (fun cv np nf h => ?_), fun h => absurd rfl h⟩⟩
    rw [hfi] at h
    exact h4 (hk.2.mp ⟨cv, np, nf, Option.some.inj h⟩)
  rw [if_neg h4] at hW
  have h4' : rdW (m.arr64 EREC) (r1.tail.headD 0) = 4 := by simpa using h4
  obtain ⟨cvj, np, nF, rfl⟩ := hk.2.mpr h4'
  obtain ⟨-, hcv, hnf⟩ := decCI_ctorW hciB
  obtain ⟨tw, htw, htw32, hty⟩ := hd?_w (decCV_ty hcv)
  have hty4 : rdW (m.arr64 EREC) (r1.tail.headD 0 + 4) = tw :=
    rdW_off (k := 4) hsz (by decide) (by rw [show (r1.tail.headD 0).toNat + 4 =
      (r1.tail.headD 0).toNat + 1 + 3 by omega]; exact htw)
  -- `pi_result_f` at `CWF`
  cases c2 : callW p (k + 1) "pi_result_f" [CWF, rdW (m.arr64 EREC) (r1.tail.headD 0 + 4)] m with
  | none => rw [c2] at hW; simp at hW
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, bW_some] at hW
  have c2' := callW_model (M := fun mm => pirfW p k mm CWF (rdW (m.arr64 EREC) (r1.tail.headD 0 + 4)))
    (fun s => pirf_spec p hp.pirf k s CWF (rdW (m.arr64 EREC) (r1.tail.headD 0 + 4))) c2
  simp only [pirfW, ne_eq, not_true_eq_false, ↓reduceIte] at c2'
  cases c2'' : callW p k "pi_result" [rdW (m.arr64 EREC) (r1.tail.headD 0 + 4)] m with
  | none => rw [c2''] at c2'; simp at c2'
  | some q2' =>
  obtain ⟨r2', m2'⟩ := q2'
  rw [c2'', bW_some] at c2'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c2')
  rw [hty4] at c2''
  obtain ⟨t2, ht2, hm2, -, hHW2, hrun2⟩ := triple_of_callW
    (piResult_refines' p hp.pires k ⟨m, Locals.init []⟩ a hR tw htw32) c2''
  have e_m2p : m = m2' := by rw [← ht2, hm2]
  subst e_m2p
  -- `get_app_fn_f` at `CWF`
  cases c3 : callW p (k + 1) "get_app_fn_f" [CWF, [r2'.headD 0].headD 0] m with
  | none => rw [c3] at hW; simp at hW
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, bW_some] at hW
  have c3' := callW_model (M := fun mm => gaffW p k mm CWF (r2'.headD 0)) (fun s => gaff_spec p hp.gaff k s CWF (r2'.headD 0)) c3
  simp only [gaffW, ne_eq, not_true_eq_false, ↓reduceIte] at c3'
  cases c3'' : callW p k "get_app_fn" [r2'.headD 0] m with
  | none => rw [c3''] at c3'; simp at c3'
  | some q3' =>
  obtain ⟨r3', m3'⟩ := q3'
  rw [c3'', bW_some] at c3'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c3')
  obtain ⟨t3, ht3, hm3, -, hHW3, hrun3⟩ := triple_of_callW
    (getAppFn_refines' p hp.gaf k ⟨m, Locals.init []⟩ a hR (r2'.headD 0) hHW2) c3''
  have e_m3p : m = m3' := by rw [← ht3, hm3]
  subst e_m3p
  have hpr : (piResult coreWalkFuel cvj.type).run a = .ok (decE (r2'.headD 0), a) := by
    rw [hty]; exact hrun2
  have hga : (getAppFn coreWalkFuel (decE (r2'.headD 0))).run a = .ok (decE (r3'.headD 0), a) := hrun3
  have hblk : ∀ G : IConstantVal → Nat → IConstantVal → IIndCaps → Bool,
      famT fe G (decI c) = famBlk fe (G cvj nF) cvj := fun G => by simp only [famT, hfi]
  simp only [List.headD_cons] at hW
  by_cases h3n : ¬ r3'.headD 0 >>> 28 = 3
  · have h3' := h3n
    simp only [ne_eq, h3', not_false_eq_true, ↓reduceIte] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨rfl, fun G => ⟨fun _ => ?_, fun h => absurd rfl h⟩⟩
    rw [hblk]
    exact famBlk_not fe _ cvj a _ _ hpr hga (fun ht => h3' ((decE_tag_eq _ hHW3 3 (by decide)).mp ht))
  have h3' : r3'.headD 0 >>> 28 = 3 := Decidable.not_not.mp h3n
  simp only [ne_eq, h3', not_true_eq_false, ↓reduceIte] at hW
  have htag : (decE (r3'.headD 0)).tag = ETag.const := (decE_tag_eq _ hHW3 3 (by decide)).mpr h3'
  -- `const_name_of`
  cases c4 : callW p (k + 1) "const_name_of" [r3'.headD 0] m with
  | none => rw [c4] at hW; simp at hW
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, bW_some] at hW
  obtain ⟨t4, ht4, -, hm4, hcno⟩ := triple_of_callW
    (constNameOf_spec p hp.cno k ⟨m, Locals.init []⟩ (r3'.headD 0)) c4
  have e_m4 : m = m4 := by rw [← ht4, hm4]
  subst e_m4
  simp only [cnoW] at hcno
  by_cases g1 : tierW (r3'.headD 0) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [if_pos g1] at hcno; cases hcno
  rw [if_neg g1] at hcno
  by_cases g2 : rdW (m.arr64 CTL) (18 + tierW (r3'.headD 0)) ≤ idxW (r3'.headD 0)
  · rw [if_pos g2] at hcno; cases hcno
  rw [if_neg g2] at hcno
  simp only [Option.some.injEq] at hcno
  have hvc : viewOK m (r3'.headD 0) 18 := ⟨g1, UInt64.not_le.mp g2⟩
  obtain ⟨hvw, hn32, -⟩ := L.Arena.view_const_f m a hR (r3'.headD 0) hHW3 hvc h3'
  rw [hcno] at hvw hn32
  -- the head's record
  cases c5 : callW p (k + 1) "env_find" [r4.headD 0, vis] m with
  | none => rw [c5] at hW; simp at hW
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, bW_some] at hW
  obtain ⟨t5, ht5, hm5, -, hfind5⟩ := triple_of_callW
    (envFind_refines p hp.envix hp.envrow hp.envfind (k + 1) ⟨m, Locals.init []⟩ vis _ hE hn32) c5
  obtain ⟨t5', ht5', -, -, hfound5⟩ := triple_of_callW
    (envFind_found p hp.envix hp.envrow hp.envfind (k + 1) ⟨m, Locals.init []⟩ vis _ hn32) c5
  have e_m5 : m = m5 := by rw [← ht5, hm5]
  subst e_m5
  simp only at hfind5 hfound5
  by_cases h5 : r5.headD 0 = 0
  · rw [if_pos h5] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hnone : fe.find? (decI (r4.headD 0)) = none := by rw [hfind5, decFound, if_pos h5]
    refine ⟨rfl, fun G => ⟨fun _ => ?_, fun h => absurd rfl h⟩⟩
    rw [hblk]
    exact famBlk_other fe _ cvj a _ _ hpr hga _ _ hvw htag
      (fun cvT caps hc => by rw [hnone] at hc; cases hc)
  rw [if_neg h5] at hW
  obtain ⟨htag5, hrow5, hq5⟩ := hfound5 h5
  obtain ⟨ci5, hci5⟩ := hE.found_some (r4.headD 0) hn32 htag5 hrow5
  have hfi5 : fe.find? (decI (r4.headD 0)) = some ci5 := by
    rw [hfind5]; simp only [decFound, h5, ↓reduceIte, hq5]; exact hci5
  rw [← hq5] at hci5
  have hci5B := ArrExt.decCI (erecP_ext m) hci5
  have hk5 := kind_of_rdW hci5B
  by_cases h33 : rdW (m.arr64 EREC) (r5.tail.headD 0) ≠ 3
  · rw [if_pos h33] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨rfl, fun G => ⟨fun _ => ?_, fun h => absurd rfl h⟩⟩
    rw [hblk]
    exact famBlk_other fe _ cvj a _ _ hpr hga _ _ hvw htag (fun cvT caps hc => by
      rw [hfi5] at hc; exact h33 (hk5.1.mp ⟨cvT, caps, Option.some.inj hc⟩))
  rw [if_neg h33] at hW
  obtain ⟨cvT, caps, rfl⟩ := hk5.1.mpr (by simpa using h33)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  refine ⟨rfl, fun G => ⟨fun h => absurd h (by simp), fun _ => ⟨cvj, np, nF, cvT, caps, hciB, hci5B, ?_⟩⟩⟩
  rw [hblk]
  exact famBlk_ind fe _ cvj a _ _ hpr hga _ _ hvw htag cvT caps hfi5

end L.Stubs
