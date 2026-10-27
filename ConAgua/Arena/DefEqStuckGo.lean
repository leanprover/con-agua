import ConAgua.Arena.DefEqStuckWith
import ConAgua.Arena.DefEqLeaves2
import ConAgua.Census.Attr

/-!
# `struct_eta_cert_go` refines `structEtaCertWith`'s keys (lane `defeq`, helper `defeq-top`)

The twin's `let reserved ← …; match ← viewLsLen us' …; let slots ← towerSlotsAll …; if … then
…` (`setGoT`). Under `CoreS` the pin reads and `viewLsLen` have no effect (`setGoT_run`), so L's
pure calls (`er_slice_eq`, `reserved_contains`, `ls_node`) run first and the one effect,
`tower_slots_all`, is the twin's. The decoded records: `decCI_ctorLp` (a constructor's level
parameters), `decCI_indCaps` (an inductive's level parameters and η caps).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The records -/

/-- **A constructor record's level parameters**: the slice at `p + 2`, `p + 3`. -/
theorem decCI_ctorLp {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {cv : IConstantVal} {np nf : Nat} (h : decCI a dn q.toNat = some (.ctorInfo cv np nf))
    (hab : ArrExt a b) (hsz : b.size < 2 ^ 63) :
    hslice? a (rdW b (q + 2)).toNat (rdW b (q + 3)).toNat = some cv.levelParams := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
  all_goals (rw [hk] at h)
  all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq,
    and_false, exists_false, Option.pure_def] at h
  obtain ⟨cv', hcv, np', -, nf', -, hc⟩ := h
  cases hc
  simp only [decCV, hlist?, nat?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.some.injEq] at hcv
  obtain ⟨nm, -, ls, ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩, ty, -, rfl⟩ := hcv
  have h2 : rdW b (q + 2) = wo := rdW_ext hab hsz (k := 2) (by decide) (by simpa [Nat.add_assoc] using hwo)
  have h3 : rdW b (q + 3) = wc := rdW_ext hab hsz (k := 3) (by decide) (by simpa [Nat.add_assoc] using hwc)
  rw [h2, h3]; exact hs

/-- **An inductive record's level parameters and η/unit caps.** -/
structure IndRecR (b : Array Word) (a : Array Word) (q : Word) (cv : IConstantVal) (caps : IIndCaps) :
    Prop where
  lp : hslice? a (rdW b (q + 2)).toNat (rdW b (q + 3)).toNat = some cv.levelParams
  eta : caps.eta = (rdW b (q + 5) != 0)
  etaCtor : caps.etaCtor = decI (rdW b (q + 6))
  etaCtor_hw : HW (rdW b (q + 6))
  etaParams : caps.etaParams = (rdW b (q + 7)).toNat
  etaFields : caps.etaFields = (rdW b (q + 8)).toNat
  unitlike : caps.unitlike = (rdW b (q + 9) != 0)
  unitParams : caps.unitParams = (rdW b (q + 10)).toNat

theorem decCI_indCaps {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a dn q.toNat = some (.indInfo cv caps))
    (hab : ArrExt a b) (hsz : b.size < 2 ^ 63) : IndRecR b a q cv caps := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
  all_goals (rw [hk] at h)
  all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq,
    and_false, exists_false, Option.pure_def] at h
  obtain ⟨cv', hcv, caps', hcaps, hc⟩ := h
  cases hc
  simp only [decCV, hlist?, nat?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.some.injEq] at hcv
  obtain ⟨nm, -, ls, ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩, ty, -, rfl⟩ := hcv
  have h2 : rdW b (q + 2) = wo := rdW_ext hab hsz (k := 2) (by decide) (by simpa [Nat.add_assoc] using hwo)
  have h3 : rdW b (q + 3) = wc := rdW_ext hab hsz (k := 3) (by decide) (by simpa [Nat.add_assoc] using hwc)
  simp only [decCaps, bool?, hd?, nat?, hlist?, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hcaps
  obtain ⟨e, ⟨we, hwe, rfl⟩, ec, ⟨wec, hwec, hec⟩, ep, ⟨wep, hwep, rfl⟩, ef, ⟨wef, hwef, rfl⟩,
    ul, ⟨wul, hwul, rfl⟩, up, ⟨wup, hwup, rfl⟩, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hcaps
  have h5 : rdW b (q + 5) = we := rdW_ext hab hsz (k := 5) (by decide) (by simpa [Nat.add_assoc] using hwe)
  have h6 : rdW b (q + 6) = wec := rdW_ext hab hsz (k := 6) (by decide) (by simpa [Nat.add_assoc] using hwec)
  have h7 : rdW b (q + 7) = wep := rdW_ext hab hsz (k := 7) (by decide) (by simpa [Nat.add_assoc] using hwep)
  have h8 : rdW b (q + 8) = wef := rdW_ext hab hsz (k := 8) (by decide) (by simpa [Nat.add_assoc] using hwef)
  have h9 : rdW b (q + 9) = wul := rdW_ext hab hsz (k := 9) (by decide) (by simpa [Nat.add_assoc] using hwul)
  have h10 : rdW b (q + 10) = wup := rdW_ext hab hsz (k := 10) (by decide) (by simpa [Nat.add_assoc] using hwup)
  split at hec
  · rename_i hlt
    cases hec
    exact ⟨by rw [h2, h3]; exact hs, by rw [h5], by rw [h6], by rw [h6]; exact hlt, by rw [h7],
      by rw [h8], by rw [h9], by rw [h10]⟩
  · cases hec

/-! ## The twin -/

/-- **`structEtaCertWith` once both heads and spines are known**, copied. -/
def setGoT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (aargs targs : List EIdx) : AM Bool := do
  let reserved ← reservedBasisNames
  match ← viewLsLen us' with
  | none => failDanglingLs
  | some uslen =>
  let slots ← (pure (towerSlotsAll fe T caps.etaFields) : AM Bool)
  if caps.eta = true ∧ caps.etaCtor = c ∧
      reserved.contains T = false ∧ reserved.contains c = false ∧
      targs.length = caps.etaParams ∧
      uslen = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧ slots = true then
    setTailT r fe depth b us T us' caps.etaParams caps.etaFields aargs targs
  else pure false

theorem pinsReady_of {m : Mem} {a : AState} (hP : PinsFull m a.pins) : pinsReady a = true := by
  simp [pinsReady, hP.names_size, pinCount]

theorem reservedBasisNames_run {m : Mem} {a : AState} (hP : PinsFull m a.pins) :
    reservedBasisNames.run a = .ok (a.pins.reserved, a) := by
  simp only [reservedBasisNames, pinReserved, StateT.run_bind, StateT.run_get, pure_bind,
    pinsReady_of hP, ↓reduceIte]
  rfl

theorem reservedContainsT_run {m : Mem} {a : AState} (hP : PinsFull m a.pins) (n : NIdx) :
    (reservedContainsT n).run a = .ok (a.pins.reserved.contains n, a) := by
  simp only [reservedContainsT, StateT.run_bind, reservedBasisNames_run hP, except_ok_bind]
  rfl

/-- `setGoT`'s test and tail, at the reserved names `rs`, the level list's length and `slots`. -/
def setGoK (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (aargs targs : List EIdx) (rs : List NIdx) (uslen : Nat) (slots : Bool) : AM Bool :=
  if caps.eta = true ∧ caps.etaCtor = c ∧
      rs.contains T = false ∧ rs.contains c = false ∧
      targs.length = caps.etaParams ∧
      uslen = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧ slots = true then
    setTailT r fe depth b us T us' caps.etaParams caps.etaFields aargs targs
  else pure false

/-- **`setGoT` from `towerSlotsAll` on**, under the pins and a level list that has a length. -/
theorem setGoT_run (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (aargs targs : List EIdx) {m : Mem} {a : AState} (hP : PinsFull m a.pins) (uslen : Nat)
    (hv : a.store.lss.viewLen us' = some uslen) :
    (setGoT r fe depth b c us cvc T us' cvT caps aargs targs).run a =
      ((pure (towerSlotsAll fe T caps.etaFields) : AM Bool) >>=
        setGoK r fe depth b c us cvc T us' cvT caps aargs targs a.pins.reserved uslen).run a := by
  simp only [setGoT, StateT.run_bind, reservedBasisNames_run hP, except_ok_bind, viewLsLen_run, hv]
  rfl

/-! ## The model of `struct_eta_cert_go` -/

section sgK
variable (p : Prog) (n : Nat) (m0 : Mem) (mode vis d b us c pc T q us2 ao an to tn : Word)

/-- After `tower_slots_all`: the tests (record words read at entry, `m0`), then the tail. -/
def sgK5 (lpe r1 r2 uslen : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if rdW (m0.arr64 EREC) (q + 5) = 0 then some (0, m)
    else if rdW (m0.arr64 EREC) (q + 6) ≠ c then some (0, m)
    else if r1 ≠ 0 then some (0, m)
    else if r2 ≠ 0 then some (0, m)
    else if tn ≠ rdW (m0.arr64 EREC) (q + 7) then some (0, m)
    else if uslen ≠ rdW (m0.arr64 EREC) (q + 3) then some (0, m)
    else if lpe = 0 then some (0, m)
    else if r.headD 0 = 0 then some (0, m)
    else call1W p n "struct_eta_cert_tail" [mode, vis, d, b, us, T, us2, ao, an, to, tn,
      rdW (m0.arr64 EREC) (q + 7), rdW (m0.arr64 EREC) (q + 8)] m

def sgK4 (lpe r1 r2 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => sgK5 p n m0 mode vis d b us c T q us2 ao an to tn lpe r1 r2 (r.tail.headD 0)
      (callW p n "tower_slots_all" [vis, T, rdW (m0.arr64 EREC) (q + 8)] m)

def sgK3 (lpe r1 : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => sgK4 p n m0 mode vis d b us c T q us2 ao an to tn lpe r1 (r.headD 0)
      (callW p n "ls_node" [us2] m)

def sgK2 (lpe : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => sgK3 p n m0 mode vis d b us c T q us2 ao an to tn lpe (r.headD 0)
      (callW p n "reserved_contains_w" [c] m)

/-- **The model of `struct_eta_cert_go`** past `er_slice_eq`'s run. -/
def sgK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => sgK2 p n m0 mode vis d b us c T q us2 ao an to tn (r.headD 0)
      (callW p n "reserved_contains_w" [T] m)

variable (lpe r1 r2 : Word) (r : List Word) (m : Mem)
theorem sgK1_some : sgK1 p n m0 mode vis d b us c T q us2 ao an to tn (some (r, m)) =
    sgK2 p n m0 mode vis d b us c T q us2 ao an to tn (r.headD 0)
      (callW p n "reserved_contains_w" [T] m) := rfl
theorem sgK2_some : sgK2 p n m0 mode vis d b us c T q us2 ao an to tn lpe (some (r, m)) =
    sgK3 p n m0 mode vis d b us c T q us2 ao an to tn lpe (r.headD 0)
      (callW p n "reserved_contains_w" [c] m) := rfl
theorem sgK3_some : sgK3 p n m0 mode vis d b us c T q us2 ao an to tn lpe r1 (some (r, m)) =
    sgK4 p n m0 mode vis d b us c T q us2 ao an to tn lpe r1 (r.headD 0)
      (callW p n "ls_node" [us2] m) := rfl
theorem sgK4_some : sgK4 p n m0 mode vis d b us c T q us2 ao an to tn lpe r1 r2 (some (r, m)) =
    sgK5 p n m0 mode vis d b us c T q us2 ao an to tn lpe r1 r2 (r.tail.headD 0)
      (callW p n "tower_slots_all" [vis, T, rdW (m0.arr64 EREC) (q + 8)] m) := rfl

end sgK

theorem setGo_spec (p : Prog) (hq : StuckProg p) (n : Nat) (s₀ : St)
    (mode vis d b us c pc T q us2 ao an to tn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_eta_cert_go"
      [mode, vis, d, b, us, c, pc, T, q, us2, ao, an, to, tn]
    ⦃fun r s' => LocEq s' s₀ ∧ sgK1 p n s₀.mem mode vis d b us c T q us2 ao an to tn
      (callW p n "er_slice_eq" [rdW (s₀.mem.arr64 EREC) (pc + 2), rdW (s₀.mem.arr64 EREC) (pc + 3),
        rdW (s₀.mem.arr64 EREC) (q + 2), rdW (s₀.mem.arr64 EREC) (q + 3)] s₀.mem) =
        some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.setGo]
  simp only [callFn, structEtaCertGoL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec,
      callW_spec p n "er_slice_eq", callW_spec p n "reserved_contains_w", callW_spec p n "ls_node",
      callW_spec p n "tower_slots_all", callW_spec p n "struct_eta_cert_tail"] <;>
  simp_all [sgK1, sgK2, sgK3, sgK4, sgK5, call1W, LocEq, BinOp.eval, St.setLocs_cons, EREC,
    Cmp.eval, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ]

section sgKarms
variable (p : Prog) (n : Nat) (m0 : Mem) (mode vis d b us c T q us2 ao an to tn : Word)
  (lpe r1 r2 uslen : Word) (r : List Word) (m : Mem)

/-- The tests of `struct_eta_cert_go`, all passed. -/
def sgOK : Prop :=
  rdW (m0.arr64 EREC) (q + 5) ≠ 0 ∧ rdW (m0.arr64 EREC) (q + 6) = c ∧ r1 = 0 ∧ r2 = 0 ∧
    tn = rdW (m0.arr64 EREC) (q + 7) ∧ uslen = rdW (m0.arr64 EREC) (q + 3) ∧ lpe ≠ 0 ∧ r.headD 0 ≠ 0

theorem sgK5_yes (h : sgOK m0 c q tn lpe r1 r2 uslen r) :
    sgK5 p n m0 mode vis d b us c T q us2 ao an to tn lpe r1 r2 uslen (some (r, m)) =
      call1W p n "struct_eta_cert_tail" [mode, vis, d, b, us, T, us2, ao, an, to, tn,
        rdW (m0.arr64 EREC) (q + 7), rdW (m0.arr64 EREC) (q + 8)] m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [sgK5, h1, h2, h3, h4, h5, h6, h7, h8, ne_eq, not_true_eq_false,
    ↓reduceIte]

theorem sgK5_no (h : ¬ sgOK m0 c q tn lpe r1 r2 uslen r) :
    sgK5 p n m0 mode vis d b us c T q us2 ao an to tn lpe r1 r2 uslen (some (r, m)) = some (0, m) := by
  unfold sgK5
  by_cases h1 : rdW (m0.arr64 EREC) (q + 5) = 0
  · simp only [h1, ↓reduceIte]
  by_cases h2 : rdW (m0.arr64 EREC) (q + 6) ≠ c
  · simp only [h1, h2, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h3 : r1 ≠ 0
  · simp only [h1, h2, h3, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h4 : r2 ≠ 0
  · simp only [h1, h2, h3, h4, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h5 : tn ≠ rdW (m0.arr64 EREC) (q + 7)
  · simp only [h1, h2, h3, h4, h5, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h6 : uslen ≠ rdW (m0.arr64 EREC) (q + 3)
  · simp only [h1, h2, h3, h4, h5, h6, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h7 : lpe = 0
  · simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]
  by_cases h8 : r.headD 0 = 0
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]
  exact absurd ⟨h1, by simpa using h2, by simpa using h3, by simpa using h4, by simpa using h5,
    by simpa using h6, h7, h8⟩ h

end sgKarms

/-- **A grow spec applies to a forwarded run** whose decoding reads the first word. -/
theorem GrowSpec.of_call1W {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (h : GrowSpec p n f args T dec s₀ a₀ dn vis fe M eb)
    (hdec : ∀ r r' : List Word, r.headD 0 = r'.headD 0 → dec r = dec r') {r : List Word} {m' : Mem}
    (hc : call1W p n f args s₀.mem = some (r.headD 0, m')) :
    GrowRef T a₀ dec dn s₀.mem vis fe M eb r m' := by
  rcases hcall : callW p n f args s₀.mem with _ | ⟨r₁, m₁⟩ <;> simp only [hcall, call1W, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  obtain ⟨hw, rfl⟩ := hc
  obtain ⟨h1, h2, h3, h4⟩ := GrowSpec.of_callW h hcall
  exact ⟨h1, h2, h3.trans (hdec _ _ hw), by unfold ResH at h4 ⊢; rw [← hw]; exact h4⟩

/-- A core run whose twin has no effect, in front of a run that grew the stack. -/
theorem growRef_pre {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (hA : CoreAfter dn m₀ m₁ a₀ vis fe M eb)
    (h : ∀ M', CoreS dn m₁ a₀ vis fe M' eb → GrowRef T a₀ dec dn m₁ vis fe M' eb r m ok) :
    GrowRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨M', hS, hK, hSt⟩ := hA
  obtain ⟨hok, ⟨M'', hS'', hK'', hSt''⟩, hres, hr⟩ := h M' hS
  exact ⟨hok, ⟨M'', hS'', hK.trans hK'', hSt.toGrew.trans hSt''⟩, hres, hr⟩

/-- A `reserved_contains` run: the twin unchanged, the verdict the pins' list's. -/
theorem reservedContains_callW {p : Prog} (hc : StuckCallees p) {n : Nat}
    {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {x : Word} (hx : HW x)
    {r : List Word} (hcall : callW p n "reserved_contains_w" [x] m = some (r, m')) :
    CoreAfter dn m m' a vis fe M eb ∧ decBool r = a.pins.reserved.contains (decI x) := by
  have h := CoreSpec.of_callW (hc.reservedContains n ⟨m, Locals.init []⟩ a dn vis fe M eb x hS hx) hcall
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (reservedContainsT_run hS.pins (decI x))
  refine ⟨hst ▸ h.2.1, ?_⟩
  rw [← h.2.2.1, hres]

/-- A `const` node's level list at a state, read back after `towerSlotsAll`. -/
theorem constLs_after_tower {fe : IFEnv} {T : NIdx} {nF : Nat} {a : AState} {x : EIdx} {c : NIdx}
    {us : LsIdx} (hv : a.store.view x = some (.const c us)) :
    (AM.st (pure (towerSlotsAll fe T nF) : AM Bool) a).store.view x = some (.const c us) := hv

/-- **`struct_eta_cert_go` refines `setGoT`** at the knot (the projections' slice left on the
stack). -/
@[refines_part ConRon.Arena.structEtaCertWith "the keys, then the tail (setGoT)"]
theorem setGo_refines (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us c pc T q us2 ao an to tn : Word) (aargs targs : Array EIdx)
    (cvc : IConstantVal) (np nf : Nat) (cvT : IConstantVal) (caps : IIndCaps) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hus : HW us)
    (hcw : HW c) (hT : HW T) (hus2 : HW us2)
    (hvus : ∃ x c', a₀.store.view x = some (.const c' (decI us)))
    (hvus2 : ∃ x c', a₀.store.view x = some (.const c' (decI us2)))
    (hcvc : decCI (erecP s₀.mem) dn pc.toNat = some (.ctorInfo cvc np nf))
    (hcvT : decCI (erecP s₀.mem) dn q.toNat = some (.indInfo cvT caps))
    (ha : SpineR s₀.mem ao an aargs) (ht : SpineR s₀.mem to tn targs)
    (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (htt : to.toNat + tn.toNat ≤ (spTop s₀.mem).toNat) :
    GrowSpec p (n + 1) "struct_eta_cert_go" [mode, vis, d, b, us, c, pc, T, q, us2, ao, an, to, tn]
      (setGoT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc (decI T)
        (decI us2) cvT caps aargs.toList targs.toList) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (setGo_spec p hq n s₀ mode vis d b us c pc T q us2 ao an to tn)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hspn := hS.spn
  have hIR := decCI_indCaps hcvT (erecP_ext _) hS.erec
  have hCL := decCI_ctorLp hcvc (erecP_ext _) hS.erec
  -- `er_slice_eq`: memory unchanged
  obtain ⟨r₁, m₁, hc1, hW1⟩ := callW_cases rfl hW
  cases n with
  | zero => rw [callW_zero] at hc1; cases hc1
  | succ n' =>
  obtain ⟨t₁, ht₁, hm₁, -, hr₁, -⟩ := triple_of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
    (erSliceEq_refines p hq.ers n' ⟨s.mem, Locals.init []⟩ _ _ _ _ cvc.levelParams cvT.levelParams
      hS.erec hCL hIR.lp) hc1
  have em₁ : m₁ = s.mem := by rw [← ht₁]; exact hm₁
  subst em₁
  rw [sgK1_some] at hW1
  -- the two reserved-name tests: the twin unchanged
  obtain ⟨r₂, m₂, hc2, hW2⟩ := callW_cases rfl hW1
  obtain ⟨hA₂, hr₂⟩ := reservedContains_callW hc hS hT hc2
  refine growRef_pre hA₂ (fun M₂ hS₂ => ?_)
  obtain ⟨_, _, _, hst₂⟩ := hA₂
  rw [sgK2_some] at hW2
  obtain ⟨r₃, m₃, hc3, hW3⟩ := callW_cases rfl hW2
  obtain ⟨hA₃, hr₃⟩ := reservedContains_callW hc hS₂ hcw hc3
  refine growRef_pre hA₃ (fun M₃ hS₃ => ?_)
  obtain ⟨_, _, _, hst₃⟩ := hA₃
  rw [sgK3_some] at hW3
  -- `ls_node`: memory unchanged, the length
  obtain ⟨r₄, m₄, hc4, hW4⟩ := callW_cases rfl hW3
  obtain ⟨t₄, ht₄, ht₄s, hne, hr₄⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
    (lsNode_spec p hq.leaf.core.lsn (n' + 1) ⟨m₃, Locals.init []⟩ us2) hc4
  have em₄ : m₄ = m₃ := by rw [← ht₄, ht₄s]
  subst em₄
  rw [hr₄] at hne
  have hvl := defeq_lsNodeW_viewLen hS₃.arena.1 hus2 hne
  rw [← hr₄] at hvl
  rw [sgK4_some] at hW4
  -- `tower_slots_all`: the effect
  obtain ⟨r₅, m₅, hc5, hW5⟩ := callW_cases rfl hW4
  have h₅ := CoreSpec.of_callW (hc.towerSlots (n' + 1) ⟨m₄, Locals.init []⟩ a₀ dn vis fe M₃ eb T _ hS₃
    hT) hc5
  rw [← hIR.etaFields] at h₅
  obtain ⟨_, _, _, hst₅⟩ := h₅.2.1
  refine growRef_congrS (setGoT_run _ _ _ _ _ _ _ _ _ _ _ _ _ hS.pins _ hvl) ?_
  refine growRef_bindS (GrowRef.of_core h₅) (fun M₅ hS₅ => ?_)
  unfold setGoK
  -- the tests
  have hlenT : targs.toList.length = tn.toNat := by simpa using ht.size
  have hlpT : cvT.levelParams.length = (rdW (s.mem.arr64 EREC) (q + 3)).toNat := hslice?_length hIR.lp
  have hiff : (caps.eta = true ∧ caps.etaCtor = decI c ∧
      a₀.pins.reserved.contains (decI T) = false ∧ a₀.pins.reserved.contains (decI c) = false ∧
      targs.toList.length = caps.etaParams ∧
      (r₄.tail.headD 0).toNat = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧ decBool r₅ = true) ↔
      sgOK s.mem c q tn (r₁.headD 0) (r₂.headD 0) (r₃.headD 0) (r₄.tail.headD 0) r₅ := by
    unfold sgOK
    rw [hIR.eta, hIR.etaCtor, ← hr₂, ← hr₃, hlenT, hIR.etaParams, hlpT]
    have e2 : decI (rdW (s.mem.arr64 EREC) (q + 6)) = (decI c : NIdx) ↔
        rdW (s.mem.arr64 EREC) (q + 6) = c :=
      ⟨fun h => decI_inj hIR.etaCtor_hw hcw h, fun h => by rw [h]⟩
    have e7 : cvc.levelParams = cvT.levelParams ↔ r₁.headD 0 ≠ 0 := by
      have h1 : decBool r₁ = decide (cvc.levelParams = cvT.levelParams) := hr₁
      unfold decBool at h1
      by_cases he : cvc.levelParams = cvT.levelParams
      · simp only [he, decide_true, bne_iff_ne, ne_eq] at h1; exact ⟨fun _ => h1, fun _ => he⟩
      · simp only [he, decide_false, bne_eq_false_iff_eq] at h1
        exact ⟨fun h => absurd h he, fun h => absurd h1 h⟩
    rw [e2, e7]
    simp only [decBool, bne_iff_ne, ne_eq, bne_eq_false_iff_eq,
      UInt64.toNat_inj]
  by_cases hok : sgOK s.mem c q tn (r₁.headD 0) (r₂.headD 0) (r₃.headD 0) (r₄.tail.headD 0) r₅
  · rw [sgK5_yes (h := hok)] at hW5
    rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr hok))]
    have hk₅ := hst₂.trans (hst₃.trans hst₅)
    have htop : spTop m₅ = spTop s.mem := hk₅.1
    have hg := GrowSpec.of_call1W (s₀ := ⟨m₅, Locals.init []⟩)
      (setTail_refines p hq hi hc n' (hk.mono (by omega)) F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb
        mode d b us T us2 ao an to tn _ _ aargs targs (by omega) (by omega)
        ⟨hS₅, hs.mode4, hs.eb_mode⟩ hb hus hT hus2
        (by obtain ⟨x, c', hx⟩ := hvus
            exact (hc.den _ _ _ _ _ _ _ hS₅).constLs _ _ _ (constLs_after_tower hx))
        (by obtain ⟨x, c', hx⟩ := hvus2
            exact (hc.den _ _ _ _ _ _ _ hS₅).constLs _ _ _ (constLs_after_tower hx))
        (ha.keep hk₅.size hk₅.below hat hspn)
        (ht.keep hk₅.size hk₅.below htt hspn) (by rw [htop]; exact hat) (by rw [htop]; exact htt))
      (fun r r' h => by simp only [decBool, h]) hW5
    rw [← hIR.etaParams, ← hIR.etaFields] at hg
    exact hg
  · rw [sgK5_no (h := hok)] at hW5
    obtain ⟨hr, rfl⟩ := some_pair_inj hW5
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hok (hiff.mp h)))]
    exact growRef_pure hS₅ rfl (decBool_false_of hr.symm).symm (by unfold ResH; rw [← hr]; exact hw0)

end L.Arena
