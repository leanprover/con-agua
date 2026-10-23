import ConAgua.Arena.StubInd
import ConAgua.Arena.WhnfIotaRefine6
import ConAgua.Arena.DeclCanonSpec
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclNatBase
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
  if r1.headD 0 = 0 then some ([0, 0], m1) else
  if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 4 then some ([0, 0], m1) else
  ntBW (callW p n "pi_result_f" [CWF, rdW (m1.arr64 EREC) (r1.tail.headD 0 + 4)] m1) fun r2 m2 =>
  ntBW (callW p n "get_app_fn_f" [CWF, r2.headD 0] m2) fun r3 m3 =>
  if r3.headD 0 >>> 28 ≠ 3 then some ([r1.tail.headD 0, 0], m3) else
  ntBW (callW p n "const_name_of" [r3.headD 0] m3) fun r4 m4 =>
  ntBW (callW p n "env_find" [r4.headD 0, vis] m4) fun r5 m5 =>
  if r5.headD 0 = 0 then some ([r1.tail.headD 0, 0], m5) else
  if rdW (m5.arr64 EREC) (r5.tail.headD 0) ≠ 3 then some ([r1.tail.headD 0, 0], m5) else
  some ([r1.tail.headD 0, r5.tail.headD 0], m5)

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
  if r.tail.headD 0 = 0 then some ([0], m1) else
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
  if r.tail.headD 0 = 0 then some ([0], m1) else
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

end L.Stubs
