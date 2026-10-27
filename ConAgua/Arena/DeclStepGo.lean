import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclRec
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

noncomputable section

/-!
# Phase A's step body, `install_step_go`, refines `installStepGo` (lane `decls2`)

`install_step_go(i, vis)` reads the record's kind and name, asks `pin_in` whether a definition or
an opaque is pinned, and goes to `check_decl` (the pinned names and every other kind) or to
`install_value` (the guard-and-install arm). This file: `pin_in`'s model and meaning, the twin's
name lists under the pin table, the arm's twin (`ivT`), the models. The refinement itself, under
`StageT`, is `CheckerT.lean`'s `installStepGo_specT` (lane `loopt2`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

/-! ## `pin_in(x, k, hi)` -/

/-- The model of `pin_in` (the memory is unchanged). -/
def pinInW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, x, k, hi =>
    if pinW m 0 = 0 then none
    else if hi ≤ k then some 0
    else if rdW (m.arr64 PINS) k = x then some 1
    else pinInW n m x (k + 1) hi

section arms
variable (n : Nat) (m : Mem) (x k hi : Word)
theorem pinInW_empty (h0 : pinW m 0 = 0) : pinInW (n + 1) m x k hi = none := by simp [pinInW, h0]
theorem pinInW_end (h0 : pinW m 0 ≠ 0) (h : hi ≤ k) : pinInW (n + 1) m x k hi = some 0 := by
  simp [pinInW, h0, h]
theorem pinInW_hit (h0 : pinW m 0 ≠ 0) (h : ¬ hi ≤ k) (h2 : rdW (m.arr64 PINS) k = x) :
    pinInW (n + 1) m x k hi = some 1 := by simp [pinInW, h0, h, h2]
theorem pinInW_next (h0 : pinW m 0 ≠ 0) (h : ¬ hi ≤ k) (h2 : rdW (m.arr64 PINS) k ≠ x) :
    pinInW (n + 1) m x k hi = pinInW n m x (k + 1) hi := by simp [pinInW, h0, h, h2]
end arms

grind_pattern [ind_grind] pinInW_empty => pinInW (n + 1) m x k hi
grind_pattern [ind_grind] pinInW_end => pinInW (n + 1) m x k hi
grind_pattern [ind_grind] pinInW_hit => pinInW (n + 1) m x k hi
grind_pattern [ind_grind] pinInW_next => pinInW (n + 1) m x k hi

theorem pinIn_specW (p : Prog) (hp : p.lookup "pin_in" = some pinIn) (n : Nat) :
    ∀ (s₀ : St) (x k hi : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_in" [x, k, hi]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ pinInW n s₀.mem x k hi = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ x k hi; rw [invoke_eq _ hp]; simp only [callFn, pinIn]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ x k hi
    rw [invoke_eq _ hp]
    simp only [callFn, pinIn]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq, pinW_eq]

/-- **What `pin_in` answers**: `x` is one of the words `PINS[k‥hi)`. -/
theorem pinInW_ok (n : Nat) : ∀ (m : Mem) (x k hi : Word) (c : Word),
    pinInW n m x k hi = some c → hi.toNat ≤ 71 →
    (c ≠ 0 ↔ ∃ j, k.toNat ≤ j ∧ j < hi.toNat ∧ rdW (m.arr64 PINS) (UInt64.ofNat j) = x) := by
  induction n with
  | zero => intro m x k hi c h; simp [pinInW] at h
  | succ n ih =>
    intro m x k hi c h hh
    by_cases h0 : pinW m 0 = 0
    · rw [pinInW_empty n m x k hi h0] at h; cases h
    by_cases h1 : hi ≤ k
    · rw [pinInW_end n m x k hi h0 h1] at h
      cases h
      have : hi.toNat ≤ k.toNat := UInt64.le_iff_toNat_le.mp h1
      simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
      intro j hj hj2; omega
    · have hlt : k.toNat < hi.toNat := by
        have : ¬ hi.toNat ≤ k.toNat := fun h' => h1 (UInt64.le_iff_toNat_le.mpr h'); omega
      by_cases h2 : rdW (m.arr64 PINS) k = x
      · rw [pinInW_hit n m x k hi h0 h1 h2] at h
        cases h
        refine ⟨fun _ => ⟨k.toNat, Nat.le_refl _, hlt, by simpa using h2⟩, fun _ => by decide⟩
      · rw [pinInW_next n m x k hi h0 h1 h2] at h
        have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        rw [ih m x (k + 1) hi c h hh, hk1]
        constructor
        · rintro ⟨j, h3, h4, h5⟩; exact ⟨j, by omega, h4, h5⟩
        · rintro ⟨j, h3, h4, h5⟩
          refine ⟨j, ?_, h4, h5⟩
          rcases Nat.lt_or_ge k.toNat j with hj | hj
          · omega
          · have : j = k.toNat := by omega
            subst this
            exact absurd (by simpa using h5) h2

/-! ## The pinned names, under a filled pin table -/

theorem natOpNames_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    natOpNames.run a = .ok ((List.range' 15 7).map (fun j => decI (pinW m j)), a) := by
  simp [natOpNames, natPredName, natAddName, natSubName, natMulName, natPowName, natBeqName,
    natBleName, pinNatPred, pinNatAdd, pinNatSub, pinNatMul, pinNatPow, pinNatBeq, pinNatBle,
    PIN_NAT_PRED, PIN_NAT_ADD, PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE,
    StateT.run_bind, pinAt_run h, exc_ok_bind', List.range']
  rfl

theorem natDivModNames_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    natDivModNames.run a = .ok ((List.range' 22 8).map (fun j => decI (pinW m j)), a) := by
  simp [natDivModNames, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
    natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand, pinNatLor,
    pinNatXor, pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD, PIN_NAT_GCD,
    PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    StateT.run_bind, pinAt_run h, exc_ok_bind', List.range']
  rfl

theorem reduceOpNames_run {m : Mem} {a : AState} (h : PinsFull m a.pins) :
    reduceOpNames.run a = .ok ((List.range' 44 2).map (fun j => decI (pinW m j)), a) := by
  simp [reduceOpNames, reduceNatName, reduceBoolName, pinReduceNat, pinReduceBool,
    PIN_REDUCE_NAT, PIN_REDUCE_BOOL, StateT.run_bind, pinAt_run h, exc_ok_bind', List.range']
  rfl

/-- A `pin_in` answer means a filled pin table. -/
theorem pinInW_flag {n : Nat} {m : Mem} {x k hi c : Word} (h : pinInW n m x k hi = some c) :
    pinW m 0 ≠ 0 := by
  cases n with
  | zero => simp [pinInW] at h
  | succ n => intro h0; rw [pinInW_empty n m x k hi h0] at h; cases h

/-- **A pinned name list's `contains`, as word equality** (the pinned names are handle words). -/
theorem contains_pins {m : Mem} {p : Pins} (hF : PinsFull m p) {x : Word} (hx : x.toNat < 2 ^ 32)
    (lo cnt : Nat) (h1 : 1 ≤ lo) (h2 : lo + cnt ≤ 52) :
    ((List.range' lo cnt).map fun j => (decI (pinW m j) : NIdx)).contains (decI x) = true ↔
      ∃ j, lo ≤ j ∧ j < lo + cnt ∧ pinW m j = x := by
  rw [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨j, hj, he⟩
    rw [List.mem_range'] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    have hlt : (pinW m (lo + 1 * k)).toNat < 2 ^ 32 := by
      have := hF.names_lt (lo + 1 * k - 1) (by omega)
      rwa [show 1 + (lo + 1 * k - 1) = lo + 1 * k by omega] at this
    exact ⟨lo + 1 * k, by omega, by omega, decI_inj hlt hx he⟩
  · rintro ⟨j, hj1, hj2, rfl⟩
    refine ⟨j, ?_, rfl⟩
    rw [List.mem_range']
    exact ⟨j - lo, by omega, by omega⟩

theorem rdW_pins (m : Mem) (j : Nat) (hj : j < 2 ^ 64) :
    rdW (m.arr64 PINS) (UInt64.ofNat j) = pinW m j := by
  have : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hj)
  simp [rdW, pinW, this]

/-- **`pin_in` against a twin name list**: a nonzero answer is the twin's `contains`. -/
theorem pinIn_contains {m : Mem} {p : Pins} (hF : PinsFull m p) {n : Nat} {x k hi c : Word}
    (h : pinInW n m x k hi = some c) (hx : x.toNat < 2 ^ 32) (h1 : 1 ≤ k.toNat) (hk : k ≤ hi)
    (h2 : hi.toNat ≤ 52) :
    (c ≠ 0) ↔ ((List.range' k.toNat (hi.toNat - k.toNat)).map
      fun j => (decI (pinW m j) : NIdx)).contains (decI x) = true := by
  have hk' : k.toNat ≤ hi.toNat := UInt64.le_iff_toNat_le.mp hk
  rw [pinInW_ok n m x k hi c h (by omega), contains_pins hF hx _ _ h1 (by omega)]
  constructor
  · rintro ⟨j, a, b, e⟩; exact ⟨j, a, by omega, by rw [← rdW_pins m j (by omega)]; exact e⟩
  · rintro ⟨j, a, b, e⟩; exact ⟨j, a, by omega, by rw [rdW_pins m j (by omega)]; exact e⟩

/-! ## The twin's two arms -/

/-- **`installStepGo`'s guard-and-install arm** (what `install_value` refines). -/
def ivT (fe : IFEnv) : IDeclaration → AM (IFEnv × Option ValueGroup)
  | .defnDecl cv value hint => do
    installHeader fe cv
    installValueGuards fe cv value
    pure (fe.push (.defnInfo cv value hint), some ⟨.defn, cv, value⟩)
  | .thmDecl cv value => do
    installHeader fe cv
    pure (fe.push (.thmInfo cv), some ⟨.thm, cv, value⟩)
  | .opaqueDecl cv value => do
    installHeader fe cv
    installValueGuards fe cv value
    pure (fe.push (.axiomInfo cv), some ⟨.opaque, cv, value⟩)
  | _ => pure (fe, none)

/-- **`installStepGo`'s `checkDecl` arm.** -/
def cdT (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) (d : IDeclaration) :
    AM (IFEnv × Option ValueGroup) := do
  pure (← checkDecl mode pins fe d, none)

/-- The pinned definitions' names (`natOpNames ++ natDivModNames`), as the pin table holds them. -/
def pinnedDefnL (m : Mem) : List NIdx :=
  (List.range' 15 7).map (fun j => decI (pinW m j)) ++ (List.range' 22 8).map (fun j => decI (pinW m j))

/-- The pinned opaques' names (`reduceOpNames`). -/
def pinnedOpaqueL (m : Mem) : List NIdx := (List.range' 44 2).map (fun j => decI (pinW m j))

theorem pinnedDefnL_eq (m : Mem) :
    pinnedDefnL m = (List.range' 15 15).map (fun j => decI (pinW m j)) := by
  simp [pinnedDefnL, List.range']

section twin
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (fe : IFEnv) {m : Mem} {a : AState}

theorem installStepGo_defn (h : PinsFull m a.pins) (cv : IConstantVal) (v : EIdx)
    (hint : ConLeche.ReducibilityHint) :
    (installStepGo mode pins fe (.defnDecl cv v hint)).run a =
      if (pinnedDefnL m).contains cv.name then (cdT mode pins fe (.defnDecl cv v hint)).run a
      else (ivT fe (.defnDecl cv v hint)).run a := by
  simp only [installStepGo, StateT.run_bind, natOpNames_run h, exc_ok_bind',
    natDivModNames_run h, pinnedDefnL, List.contains_append]
  split <;> simp [cdT, ivT, StateT.run_bind]

theorem installStepGo_opaque (h : PinsFull m a.pins) (cv : IConstantVal) (v : EIdx) :
    (installStepGo mode pins fe (.opaqueDecl cv v)).run a =
      if (pinnedOpaqueL m).contains cv.name then (cdT mode pins fe (.opaqueDecl cv v)).run a
      else (ivT fe (.opaqueDecl cv v)).run a := by
  simp only [installStepGo, StateT.run_bind, reduceOpNames_run h, exc_ok_bind', pinnedOpaqueL]
  by_cases hc : ((List.range' 44 2).map (fun j => (decI (pinW m j) : NIdx))).contains cv.name = true
  · simp only [hc, ite_true]; rfl
  · simp only [hc, ite_false, Bool.false_eq_true]; rfl

end twin

/-! ## The model of `install_step_go` (its two big callees through `callW`) -/

section model
variable (p : Prog)

/-- `check_decl`'s result as `install_step_go` returns it. -/
def istgCD : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, 0, 0], m)

/-- `install_value`'s result as `install_step_go` returns it. -/
def istgIV : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, 1, r.tail.headD 0], m)

/-- A pinnable kind: `pin_in`'s answer picks `check_decl` or `install_value(i, vis, ck, vk)`. -/
def istgPin (n : Nat) (i vis ck vk : Word) (m0 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some c =>
    if c ≠ 0 then istgCD (callW p n "check_decl" [i, vis] m0)
    else istgIV (callW p n "install_value" [i, vis, ck, vk] m0)

/-- After `iw_reset`: the record's kind and name. -/
def istgK0 (n : Nat) (i vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m0) =>
    if rdW (m0.arr64 DECL) (1 + 8 * i) = 2 then
      istgPin p n i vis 1 0 m0 (pinInW n m0 (rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295) 15 30)
    else if rdW (m0.arr64 DECL) (1 + 8 * i) = 3 then
      istgIV (callW p n "install_value" [i, vis, 2, 1] m0)
    else if rdW (m0.arr64 DECL) (1 + 8 * i) = 4 then
      istgPin p n i vis 0 2 m0 (pinInW n m0 (rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295) 44 46)
    else istgCD (callW p n "check_decl" [i, vis] m0)

/-- **The model of `install_step_go`.** -/
def istgW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => istgK0 p n i vis (iwResetW m)

section arms
variable (n : Nat) (m m0 : Mem) (i vis ck vk c : Word) (r0 : List Word)
theorem istgW_step : istgW p (n + 1) m i vis = istgK0 p n i vis (iwResetW m) := rfl
theorem istgK0_some : istgK0 p n i vis (some (r0, m0)) =
    if rdW (m0.arr64 DECL) (1 + 8 * i) = 2 then
      istgPin p n i vis 1 0 m0 (pinInW n m0 (rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295) 15 30)
    else if rdW (m0.arr64 DECL) (1 + 8 * i) = 3 then
      istgIV (callW p n "install_value" [i, vis, 2, 1] m0)
    else if rdW (m0.arr64 DECL) (1 + 8 * i) = 4 then
      istgPin p n i vis 0 2 m0 (pinInW n m0 (rdW (m0.arr64 DECL) (2 + 8 * i) &&& 4294967295) 44 46)
    else istgCD (callW p n "check_decl" [i, vis] m0) := rfl
theorem istgPin_some : istgPin p n i vis ck vk m0 (some c) =
    if c ≠ 0 then istgCD (callW p n "check_decl" [i, vis] m0)
    else istgIV (callW p n "install_value" [i, vis, ck, vk] m0) := rfl
end arms

grind_pattern [ind_grind] istgW_step => istgW p (n + 1) m i vis
grind_pattern [ind_grind] istgK0_some => istgK0 p n i vis (some (r0, m0))
grind_pattern [ind_grind] istgPin_some => istgPin p n i vis ck vk m0 (some c)

/-- The lookups `install_step_go`'s body needs. -/
structure IstgProg (p : Prog) : Prop where
  go : p.lookup "install_step_go" = some installStepGoL
  reset : p.lookup "iw_reset" = some iwReset
  pin : p.lookup "pin_in" = some pinIn

set_option maxHeartbeats 1600000 in
theorem istg_specW (h : IstgProg p) (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step_go" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ istgW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.go]
  simp only [callFn, installStepGoL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        iwReset_specW p h.reset n, pinIn_specW p h.pin n,
        callW_spec p n "check_decl", callW_spec p n "install_value"] <;>
      finish (gen := 20) [istgCD, istgIV, rdW_eq]

end model

/-! ## The loop's relation around the body -/

theorem decI_mask {k : IdxKind} (w : Word) : (decI (w &&& 4294967295) : Idx k) = decI w := by
  have : (w &&& 4294967295).toUInt32 = w.toUInt32 := by
    apply UInt32.toNat_inj.mp
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_and]
    have : (4294967295 : Word).toNat = 2 ^ 32 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  simp [decI, this]

theorem mask_lt (w : Word) : (w &&& 4294967295).toNat < 2 ^ 32 := by
  simp only [UInt64.toNat_and]
  have : (4294967295 : Word).toNat = 2 ^ 32 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by decide)

theorem stepC_200 : (200 : Word) ∈ stepC := by decide +kernel

/-- **`iw_reset` keeps the loop's relation.** -/
theorem LoopR.reset {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (h : LoopR pins dn m a vis fe pend ds) : LoopR pins dn (m.set64 CTL 200 0) a vis fe pend ds := by
  have hf : MemFrame stepA stepC m (m.set64 CTL 200 0) :=
    (MemFrame.setCtl m 200 0).mono (by simp) (by simpa using stepC_200)
  refine h.of_step (iwReset_stage ⟨h.check, h.iw⟩).1 hf ?_
  rw [erecP_reset]; exact fun _ _ h => h

/-- `cdT` from a `checkDecl` run. -/
theorem cdT_run {mode : ConLeche.CheckMode} {pins : List INatOpPinSet} {fe fe' : IFEnv}
    {d : IDeclaration} {a a' : AState} (h : (checkDecl mode pins fe d).run a = .ok (fe', a')) :
    (cdT mode pins fe d).run a = .ok ((fe', none), a') := by
  simp only [cdT, StateT.run_bind, h, exc_ok_bind']; rfl

/-! ## `install_value(i, vis, ck, vk)`: model and `vcgen` spec -/

section ivModel
variable (p : Prog)

mutual
/-- **The model of `install_value`** (`install_header` and `env_push` through `callW`: the
header's run is a call of the program, so the callers keep what its write set keeps; the push's
spec needs the name word's bound, which only the relational lemma knows), the value's guards
reading the program's own walks (`realCall p`). -/
def ivW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, i, vis, ck, vk => ivK1 n vis vk (erecCiW n m i ck)

def ivK1 (n : Nat) (vis vk : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ivK2 n vis vk (r1.headD 0) (callW p n "install_header" [vis, r1.headD 0 + 1] m1)

def ivK2 (n : Nat) (vis vk q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) =>
    if vk ≠ 1 then ivK3 n vis vk q (ivgW (realCall p) n m2 vis (q + 1) (rdW (m2.arr64 EREC) (q + 5)))
    else ivK4 vis vk q (callW p n "env_push" [vis, q] m2)

def ivK3 (n : Nat) (vis vk q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => ivK4 vis vk q (callW p n "env_push" [vis, q] m3)

def ivK4 (_vis vk q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ivK5 (r4.headD 0) (erecVgW m4 q vk)

def ivK5 (v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([v, r5.headD 0], m5)
end

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (i vis ck vk q v : Word) (r1 r2 r3 r4 r5 : List Word)
theorem ivW_step : ivW p (n + 1) m i vis ck vk = ivK1 p n vis vk (erecCiW n m i ck) := rfl
theorem ivK1_some : ivK1 p n vis vk (some (r1, m1)) =
    ivK2 p n vis vk (r1.headD 0) (callW p n "install_header" [vis, r1.headD 0 + 1] m1) := rfl
theorem ivK2_some : ivK2 p n vis vk q (some (r2, m2)) =
    if vk ≠ 1 then ivK3 p n vis vk q (ivgW (realCall p) n m2 vis (q + 1) (rdW (m2.arr64 EREC) (q + 5)))
    else ivK4 p vis vk q (callW p n "env_push" [vis, q] m2) := rfl
theorem ivK3_some : ivK3 p n vis vk q (some (r3, m3)) =
    ivK4 p vis vk q (callW p n "env_push" [vis, q] m3) := rfl
theorem ivK4_some : ivK4 p vis vk q (some (r4, m4)) = ivK5 p (r4.headD 0) (erecVgW m4 q vk) := rfl
theorem ivK5_some : ivK5 p v (some (r5, m5)) = some ([v, r5.headD 0], m5) := rfl
end arms

grind_pattern [ind_grind] ivW_step => ivW p (n + 1) m i vis ck vk
grind_pattern [ind_grind] ivK1_some => ivK1 p n vis vk (some (r1, m1))
grind_pattern [ind_grind] ivK2_some => ivK2 p n vis vk q (some (r2, m2))
grind_pattern [ind_grind] ivK3_some => ivK3 p n vis vk q (some (r3, m3))
grind_pattern [ind_grind] ivK4_some => ivK4 p vis vk q (some (r4, m4))
grind_pattern [ind_grind] ivK5_some => ivK5 p v (some (r5, m5))

set_option maxHeartbeats 1600000 in
theorem iv_specW (hv : p.lookup "install_value" = some installValueL) (hR : RecProg p)
    (hC : CvgProg p) (n : Nat) (s₀ : St) (i vis ck vk : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_value" [i, vis, ck, vk]
    ⦃fun r s' => LocEq s' s₀ ∧ ivW p n s₀.mem i vis ck vk = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hv]
  simp only [callFn, installValueL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        erecCi_specW p hR n, callW_spec p n "install_header",
        ivg_specW p hC (realCall p) (realCall_spec p) n, callW_spec p n "env_push",
        erecVg_specW p hR n] <;>
      finish (gen := 20) [rdW_eq]

end ivModel

/-- The constant-record and value-group kinds of `install_value`'s call for a record. -/
def IvArgs (ck vk : Word) : IDeclaration → Prop
  | .defnDecl .. => ck = 1 ∧ vk = 0
  | .thmDecl .. => ck = 2 ∧ vk = 1
  | .opaqueDecl .. => ck = 0 ∧ vk = 2
  | _ => False

/-! ## `install_value`'s text -/

/-- `install_value`'s text: this lane's functions, lane `induct`'s library and stubs, the
environment. -/
def ivProg : Prog := declStepFns ++ L.Ind.libFns ++ L.Ind.stubFns ++ envProg

/-- The functions `install_value` reaches. -/
def ivFns : List FnName :=
  ["install_value", "erec_ci", "erec_alloc", "dlp_copy", "install_header", "env_find",
   "env_row_get", "env_ix", "reserved_contains", "reserved_from", "cv_lps",
   "er_to_iw", "iw_alloc", "er_copy", "sl_nodup", "sl_contains", "loose_bvars_bounded_fast",
   "has_fvar_fast", "all_level_params_defined", "consts_resolve_ffast", "install_value_guards",
   "env_push", "env_row_set", "erec_vg"]

/-- A program with `install_value`'s text. -/
structure IvProg (p : Prog) : Prop extends TextProg p ivProg ivFns where
  bvb : BvbProg p
  hf : HfF p

section ivLookups
variable {p : Prog} (h : IvProg p)
include h
theorem IvProg.iv : p.lookup "install_value" = some installValueL :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem IvProg.recP : RecProg p := by
  constructor <;> exact (h.agree _ (by decide) (by decide)).trans rfl
theorem IvProg.ih : IhProg p := by
  constructor <;> first | exact h.bvb | exact h.hf | exact (h.agree _ (by decide) (by decide)).trans rfl
end ivLookups

end L.Arena
