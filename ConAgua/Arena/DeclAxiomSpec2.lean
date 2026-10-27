import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# `Lean.trustCompiler`: `find_pinned_cv`, `trust_compiler_ok` (lane `decls3`)

`find_pinned_cv(vis, n, k, id)` is one clause of `trustCompilerOk`: the stored constant `n` has the
pinned shape (`k = 3`: an inductive; `k = 4`: a constructor without parameters and fields), and its
constant value matches `rom_cv(id)`. Its relational lemma says what the twin's clause does
(`fpcShape`: the shape test as a partial function), and `trust_compiler_ok` chains two clauses and
the axiom's own pin. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The pinned shape `k` of a stored constant: its constant value when it has the shape. -/
def fpcShape (k : Word) : IConstantInfo → Option IConstantVal
  | .indInfo cv _ => if k = 3 then some cv else none
  | .ctorInfo cv nP nF => if k = 4 ∧ nP = 0 ∧ nF = 0 then some cv else none
  | _ => none

section model
variable (p : Prog)

/-- After `rom_cv(id)`: the comparison. -/
def fpcK2 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => mpW m2 (q + 1) (r2.headD 0)

/-- After the lookup: the shape tests. -/
def fpcK1 (n : Nat) (k id : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ k then some ([0], m1)
    else if k = 4 ∧ (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 5) ≠ 0 ∨
        rdW (m1.arr64 EREC) (r1.tail.headD 0 + 6) ≠ 0) then some ([0], m1)
    else fpcK2 (r1.tail.headD 0) (callW p n "rom_cv" [id] m1)

/-- **The model of `find_pinned_cv(vis, n, k, id)`.** -/
def fpcW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, vis, nm, k, id => fpcK1 p n k id (envFindW m nm vis)

section arms
variable (n : Nat) (m m1 m2 : Mem) (vis nm k id q : Word) (r1 r2 : List Word)
theorem fpcW_step : fpcW p (n + 1) m vis nm k id = fpcK1 p n k id (envFindW m nm vis) := rfl
theorem fpcK1_some : fpcK1 p n k id (some (r1, m1)) =
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ k then some ([0], m1)
    else if k = 4 ∧ (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 5) ≠ 0 ∨
        rdW (m1.arr64 EREC) (r1.tail.headD 0 + 6) ≠ 0) then some ([0], m1)
    else fpcK2 (r1.tail.headD 0) (callW p n "rom_cv" [id] m1) := rfl
theorem fpcK2_some : fpcK2 q (some (r2, m2)) = mpW m2 (q + 1) (r2.headD 0) := rfl
end arms

grind_pattern [ind_grind] fpcW_step => fpcW p (n + 1) m vis nm k id
grind_pattern [ind_grind] fpcK1_some => fpcK1 p n k id (some (r1, m1))
grind_pattern [ind_grind] fpcK2_some => fpcK2 q (some (r2, m2))

/-- The lookups of the compiler-trust family. -/
structure TcoProg (p : Prog) : Prop where
  red : RedProg p
  fpc : p.lookup "find_pinned_cv" = some findPinnedCv
  tco : p.lookup "trust_compiler_ok" = some trustCompilerOkL

set_option maxHeartbeats 1600000 in
theorem fpc_specW (h : TcoProg p) (n : Nat) (s₀ : St) (vis nm k id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "find_pinned_cv" [vis, nm, k, id]
    ⦃fun r s' => LocEq s' s₀ ∧ fpcW p n s₀.mem vis nm k id = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.fpc]
  simp only [callFn, findPinnedCv]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p h.red.ih.ix h.red.ih.rowGet h.red.ih.find n, callW_spec p n "rom_cv",
        mp_specW p h.red.canon h.red.mp n] <;>
      finish (gen := 20) [rdW_eq, mpW]

end model

/-- The counts of a stored constructor, as words. -/
theorem ctor_counts {a : Array Word} {q : Word} {np nf : Nat} (hsz : a.size < 2 ^ 64)
    (hnp : nat? a (q.toNat + 5) = some np) (hnf : nat? a (q.toNat + 6) = some nf) :
    ((rdW a (q + 5) ≠ 0 ∨ rdW a (q + 6) ≠ 0) ↔ ¬ (np = 0 ∧ nf = 0)) := by
  obtain ⟨w5, e5, rfl⟩ := natD hnp
  obtain ⟨w6, e6, rfl⟩ := natD hnf
  have hq5 : (q + 5).toNat = q.toNat + 5 := by
    have := (Array.getElem?_eq_some_iff.mp e5).1; rw [UInt64.toNat_add]; simp; omega
  have hq6 : (q + 6).toNat = q.toNat + 6 := by
    have := (Array.getElem?_eq_some_iff.mp e6).1; rw [UInt64.toNat_add]; simp; omega
  have r5 : rdW a (q + 5) = w5 := by simp [rdW, hq5, e5]
  have r6 : rdW a (q + 6) = w6 := by simp [rdW, hq6, e6]
  rw [r5, r6]
  have i5 : w5 = 0 ↔ w5.toNat = 0 := ⟨fun h => by simp [h], fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
  have i6 : w6 = 0 ↔ w6.toNat = 0 := ⟨fun h => by simp [h], fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
  rw [Ne, Ne, i5, i6]
  omega

/-- **The shape tests on a stored record, failing**: the twin's shape does not match. -/
theorem fpc_fail {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q k : Word}
    {ci : IConstantInfo} (hsz : a.size < 2 ^ 64) (hk : k = 3 ∨ k = 4) (h : decCI a dn q.toNat = some ci)
    (hf : rdW a q ≠ k ∨ (k = 4 ∧ (rdW a (q + 5) ≠ 0 ∨ rdW a (q + 6) ≠ 0))) :
    fpcShape k ci = none := by
  obtain ⟨wk, e, hk'⟩ := ciD h
  have ew : rdW a q = wk := by simp [rdW, e]
  rw [ew] at hf
  have hw : wk = UInt64.ofNat wk.toNat := by simp
  rcases hk' with ⟨h1, cv, -, rfl⟩ | ⟨h1, cv, v, hi, -, -, -, rfl⟩ | ⟨h1, cv, -, rfl⟩ |
      ⟨h1, cv, caps, -, -, rfl⟩ | ⟨h1, cv, np, nf, -, hnp, hnf, rfl⟩ |
      ⟨h1, cv, mi, rp, o, c, rules, -, -, -, -, -, -, rfl⟩
  · simp [fpcShape]
  · simp [fpcShape]
  · simp [fpcShape]
  · -- an inductive: the kind word is `3`
    rw [hw, h1] at hf
    simp only [fpcShape]
    rcases hk with rfl | rfl
    · simp at hf
    · simp
  · -- a constructor: the kind word is `4`, the counts decide
    rw [hw, h1] at hf
    simp only [fpcShape]
    rcases hk with rfl | rfl
    · simp
    · rcases hf with hf | ⟨-, hf⟩
      · simp at hf
      · rw [ctor_counts hsz hnp hnf] at hf
        simp [hf]
  · simp [fpcShape]

/-- **The shape tests on a stored record, passing**: the twin's shape matches, with the constant
value at `q + 1`. -/
theorem fpc_pass {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q k : Word}
    {ci : IConstantInfo} (hsz : a.size < 2 ^ 64) (hk : k = 3 ∨ k = 4)
    (h : decCI a dn q.toNat = some ci) (hkw : rdW a q = k)
    (hc : ¬ (k = 4 ∧ (rdW a (q + 5) ≠ 0 ∨ rdW a (q + 6) ≠ 0))) :
    ∃ cv, fpcShape k ci = some cv ∧ decCV a (q.toNat + 1) = some cv := by
  obtain ⟨wk, e, hk'⟩ := ciD h
  have ew : rdW a q = wk := by simp [rdW, e]
  rw [ew] at hkw
  subst hkw
  rcases hk' with ⟨h1, cv, -, rfl⟩ | ⟨h1, cv, v, hi, -, -, -, rfl⟩ | ⟨h1, cv, -, rfl⟩ |
      ⟨h1, cv, caps, hcv, -, rfl⟩ | ⟨h1, cv, np, nf, hcv, hnp, hnf, rfl⟩ |
      ⟨h1, cv, mi, rp, o, c, rules, -, -, -, -, -, -, rfl⟩ <;>
    rcases hk with hk | hk <;> rw [hk] at h1 <;> simp at h1
  · exact ⟨cv, by simp [fpcShape, hk], hcv⟩
  · have h0 : np = 0 ∧ nf = 0 := by
      have hcc := ctor_counts hsz hnp hnf
      by_cases hx : np = 0 ∧ nf = 0
      · exact hx
      · exact absurd ⟨hk, hcc.mpr hx⟩ hc
    exact ⟨cv, by simp [fpcShape, hk, h0], hcv⟩

/-- A matching shape's constant value decodes where the record does. -/
theorem fpcShape_cv {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {k : Word}
    {ci : IConstantInfo} {cv : IConstantVal} (h : decCI a dn q = some ci)
    (hs : fpcShape k ci = some cv) : decCV a (q + 1) = some cv := by
  obtain ⟨wk, -, hk'⟩ := ciD h
  rcases hk' with ⟨-, cv', -, rfl⟩ | ⟨-, cv', v, hi, -, -, -, rfl⟩ | ⟨-, cv', -, rfl⟩ |
      ⟨-, cv', caps, hcv, -, rfl⟩ | ⟨-, cv', np, nf, hcv, -, -, rfl⟩ |
      ⟨-, cv', mi, rp, o, c, rules, -, -, -, -, -, -, rfl⟩ <;>
    simp only [fpcShape] at hs <;> (try cases hs)
  · split at hs <;> cases hs; exact hcv
  · split at hs <;> cases hs; exact hcv

/-- What one clause of `trustCompilerOk` does: with the pinned shape, the pin's intern and the
comparison; otherwise `false` and nothing. -/
def FpcT (fe : IFEnv) (nm : NIdx) (k : Word) (T : AM IConstantVal) (a : AState) (b : Bool)
    (a' : AState) : Prop :=
  ((fe.find? nm).bind (fpcShape k)).elim (b = false ∧ a' = a)
    (fun cvT => (do let pin ← T; pure (decide (cvT = pin)) : AM Bool).run a = .ok (b, a'))

/-- **`find_pinned_cv` against the twin's clause**, at the model level. -/
theorem fpcW_ok {p : Prog} (hR : L.Rom.RomRefs p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k id : Word} {r : List Word}
    (hW : fpcW p n m vis nm k id = some (r, m')) (hS : StageR dn vis fe m a)
    (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4) (hid : id.toNat < 10) :
    ∃ b a', StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧
      FpcT fe (decI nm) k (romCvT id.toNat) a b a' := by
  cases n with
  | zero => simp [fpcW] at hW
  | succ n =>
  rw [fpcW_step] at hW
  rcases h1 : envFindW m nm vis with _ | ⟨r1, m1⟩ <;> simp only [h1, fpcK1, reduceCtorEq] at hW
  by_cases hf : r1.headD 0 = 0
  · rw [ite_eq_left hf] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.1.env hnm hf
    exact ⟨false, a, hS, IWGrow.refl _, by simp [decW0B], by simp [FpcT, hfind]⟩
  rw [ite_eq_right hf] at hW
  obtain ⟨rfl, hptr, hfind, htag, hrc⟩ := envFindW_hit h1 hS.1.env hnm hf
  obtain ⟨ci, hci⟩ := envR_row_dec hS.1.env nm hnm htag hrc
  rw [hptr] at hW
  generalize hq : rowP m1 nm = q at hW hci hfind
  have hsz := hS.2.2.2.2.1
  have hciA : decCI (m1.arr64 EREC) dn q.toNat = some ci := ArrExt.decCI (erecP_ext m1) hci
  have hbind : (fe.find? (decI nm)).bind (fpcShape k) = fpcShape k ci := by rw [hfind, hci]; rfl
  by_cases hfail : rdW (m1.arr64 EREC) q ≠ k ∨
      (k = 4 ∧ (rdW (m1.arr64 EREC) (q + 5) ≠ 0 ∨ rdW (m1.arr64 EREC) (q + 6) ≠ 0))
  · have hnone := fpc_fail hsz hk hciA hfail
    have hW' : some ([(0 : Word)], m1) = some (r, m') := by
      rw [← hW]
      by_cases h2 : rdW (m1.arr64 EREC) q ≠ k
      · rw [ite_eq_left h2]
      · rw [ite_eq_right h2]
        rcases hfail with h1 | h1
        · exact absurd h1 h2
        · rw [ite_eq_left h1]
    simp only [Option.some.injEq, Prod.mk.injEq] at hW'
    obtain ⟨rfl, rfl⟩ := hW'
    exact ⟨false, a, hS, IWGrow.refl _, by simp [decW0B], by simp [FpcT, hbind, hnone]⟩
  have hkw : rdW (m1.arr64 EREC) q = k := by
    by_cases hne : rdW (m1.arr64 EREC) q = k
    · exact hne
    · exact absurd (.inl hne) hfail
  have hc : ¬ (k = 4 ∧ (rdW (m1.arr64 EREC) (q + 5) ≠ 0 ∨ rdW (m1.arr64 EREC) (q + 6) ≠ 0)) :=
    fun hx => hfail (.inr hx)
  rw [ite_eq_right (by simpa using hkw), ite_eq_right hc] at hW
  obtain ⟨cvT, hshape, -⟩ := fpc_pass hsz hk hciA hkw hc
  have hcvP := fpcShape_cv hci hshape
  -- the pin
  rcases h2 : callW p n "rom_cv" [id] m1 with _ | ⟨r2, m2⟩ <;> simp only [h2, fpcK2, reduceCtorEq] at hW
  obtain ⟨pin, a2, hrun2, hS2, hg2, hpin⟩ := hR.cv dn vis fe id hid n m1 a r2 m2 hS h2
  have hq1b : q.toNat + 1 < 2 ^ 64 := by
    obtain ⟨w, hw, -, -⟩ := decCV_typeW hcvP
    have := erecP_bound hw hS.2; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 hq1b
  have hcv2 : decCV (erA m2) (q + 1).toNat = some cvT := by
    rw [hq1]; exact ArrExt.decCV (IWGrow.erecExt hg2) hcvP
  obtain ⟨hm3, hrun3, hd3⟩ := mpW_ok (a := a2) hW hS2.2.2.2.2.1 hcv2
    (DecB.get ⟨fun _ _ _ he h => he.2.decCV h⟩ hpin)
  subst hm3
  refine ⟨_, a2, hS2, hg2, hd3, ?_⟩
  simp only [FpcT, hbind, hshape, Option.elim, StateT.run_bind, hrun2, exc_ok_bind']
  rw [matchesPin_eq] at hrun3
  exact hrun3

/-! ## `trust_compiler_ok(vis, q)` -/

section tco
variable (p : Prog)

/-- After `rom_cv(4)`: the axiom's own pin. -/
def tcoK5 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => mpW m5 q (r5.headD 0)

/-- After the `True.intro` clause. -/
def tcoK4 (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then some ([0], m4) else tcoK5 q (callW p n "rom_cv" [4] m4)

/-- After the `True.intro` pin. -/
def tcoK3 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tcoK4 p n q (callW p n "find_pinned_cv" [vis, r3.headD 0, 4, 3] m3)

/-- After the `True` clause. -/
def tcoK2 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => if r2.headD 0 = 0 then some ([0], m2) else tcoK3 p n vis q (pinAtW m2 41)

/-- After the `True` pin. -/
def tcoK1 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => tcoK2 p n vis q (callW p n "find_pinned_cv" [vis, r1.headD 0, 3, 2] m1)

/-- **The model of `trust_compiler_ok(vis, q)`.** -/
def tcoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q => tcoK1 p n vis q (pinAtW m 40)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis q : Word) (r1 r2 r3 r4 r5 : List Word)
theorem tcoW_step : tcoW p (n + 1) m vis q = tcoK1 p n vis q (pinAtW m 40) := rfl
theorem tcoK1_some : tcoK1 p n vis q (some (r1, m1)) =
    tcoK2 p n vis q (callW p n "find_pinned_cv" [vis, r1.headD 0, 3, 2] m1) := rfl
theorem tcoK2_some : tcoK2 p n vis q (some (r2, m2)) =
    if r2.headD 0 = 0 then some ([0], m2) else tcoK3 p n vis q (pinAtW m2 41) := rfl
theorem tcoK3_some : tcoK3 p n vis q (some (r3, m3)) =
    tcoK4 p n q (callW p n "find_pinned_cv" [vis, r3.headD 0, 4, 3] m3) := rfl
theorem tcoK4_some : tcoK4 p n q (some (r4, m4)) =
    if r4.headD 0 = 0 then some ([0], m4) else tcoK5 q (callW p n "rom_cv" [4] m4) := rfl
theorem tcoK5_some : tcoK5 q (some (r5, m5)) = mpW m5 q (r5.headD 0) := rfl
end arms

grind_pattern [ind_grind] tcoW_step => tcoW p (n + 1) m vis q
grind_pattern [ind_grind] tcoK1_some => tcoK1 p n vis q (some (r1, m1))
grind_pattern [ind_grind] tcoK2_some => tcoK2 p n vis q (some (r2, m2))
grind_pattern [ind_grind] tcoK3_some => tcoK3 p n vis q (some (r3, m3))
grind_pattern [ind_grind] tcoK4_some => tcoK4 p n q (some (r4, m4))
grind_pattern [ind_grind] tcoK5_some => tcoK5 q (some (r5, m5))

set_option maxHeartbeats 1600000 in
theorem tco_specW (h : TcoProg p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "trust_compiler_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ tcoW p n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tco]
  simp only [callFn, trustCompilerOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p h.red.pa n,
        callW_spec p n "find_pinned_cv", callW_spec p n "rom_cv",
        mp_specW p h.red.canon h.red.mp n] <;>
      finish (gen := 20) [mpW]

end tco

/-! ### The twin's clauses, flattened -/

/-- A clause of the twin's environment-shape tests: the stored constant has the pinned shape `k`,
and its constant value matches the pin `T`. -/
def clauseT (fe : IFEnv) (nm : NIdx) (k : Word) (T : AM IConstantVal) : AM Bool :=
  match (fe.find? nm).bind (fpcShape k) with
  | some cvT => do cvT.matchesPin (← T)
  | none => pure false

theorem clauseT_of_fpc {fe : IFEnv} {nm : NIdx} {k : Word} {T : AM IConstantVal} {a a' : AState}
    {b : Bool} (h : FpcT fe nm k T a b a') : (clauseT fe nm k T).run a = .ok (b, a') := by
  unfold FpcT at h
  unfold clauseT
  cases hb : (fe.find? nm).bind (fpcShape k) with
  | none => rw [hb] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | some cvT =>
    rw [hb] at h
    simp only [Option.elim] at h
    simp only [matchesPin_eq]
    exact h

/-- `trustCompilerOk` as two clauses and the axiom's pin. -/
theorem trustCompilerOk_eq (fe : IFEnv) (cv : IConstantVal) :
    trustCompilerOk fe cv = (do
      let t ← trueName
      let b ← clauseT fe t 3 trueCvA
      if !b then pure false else do
        let ti ← trueIntroName
        let b2 ← clauseT fe ti 4 trueIntroCvA
        if !b2 then pure false else cv.matchesPin (← trustCompilerA)) := by
  unfold trustCompilerOk
  congr 1; funext t
  unfold clauseT
  cases hf : fe.find? t with
  | none => simp
  | some ci =>
    cases ci with
    | indInfo cvT caps =>
      simp only [Option.bind_some, fpcShape, ite_true, bind_assoc]
      congr 1; funext pin
      simp only [matchesPin_eq, pure_bind]
      split <;> try rfl
      congr 1; funext ti
      cases hf2 : fe.find? ti with
      | none => simp
      | some ci2 =>
        cases ci2 with
        | ctorInfo cvTi nP nF =>
          simp only [Option.bind_some, fpcShape]
          by_cases e : nP = 0 ∧ nF = 0
          · obtain ⟨rfl, rfl⟩ := e
            simp only [and_self, ite_true, bind_assoc, pure_bind]
          · rcases Nat.eq_zero_or_pos nP with h0 | h0 <;> rcases Nat.eq_zero_or_pos nF with h1 | h1 <;>
              simp_all [Nat.pos_iff_ne_zero]
        | _ => simp [fpcShape]
    | _ => simp [fpcShape]

/-- A `find_pinned_cv` call's run, against its clause. -/
theorem fpc_call {p : Prog} (h : TcoProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k id : Word} {r : List Word}
    (hc : callW p n "find_pinned_cv" [vis, nm, k, id] m = some (r, m'))
    (hS : StageR dn vis fe m a) (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4)
    (hid : id.toNat < 10) :
    ∃ b a', (clauseT fe (decI nm) k (romCvT id.toNat)).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fpc_specW p h n ⟨m, Locals.init []⟩ vis nm k id) hc
  rw [hs'] at hW
  obtain ⟨b, a', hS', hg, hd, hF⟩ := fpcW_ok h.red.rom hW hS hnm hk hid
  exact ⟨b, a', clauseT_of_fpc hF, hS', hg, hd⟩

/-- **`trust_compiler_ok(vis, q)` refines `trustCompilerOk`** at the model level. -/
theorem tcoW_ok {p : Prog} (h : TcoProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal} (hW : tcoW p n m vis q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    ∃ b a', (trustCompilerOk fe cv).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  cases n with
  | zero => simp [tcoW] at hW
  | succ n =>
  rw [tcoW_step] at hW
  rw [trustCompilerOk_eq]
  -- the `True` clause
  rcases h1 : pinAtW m 40 with _ | ⟨r1, m1⟩ <;> simp only [h1, tcoK1, reduceCtorEq] at hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.1.pins
  rw [hm1, hr1] at hW
  simp only [List.headD_cons] at hW
  simp only [trueName, pinTrue, show PIN_TRUE = (40 : Word).toNat from rfl, StateT.run_bind, hrun1,
    exc_ok_bind']
  rcases h2 : callW p n "find_pinned_cv" [vis, pinW m (1 + (40 : Word).toNat), 3, 2] m with _ | ⟨r2, m2⟩ <;> simp only [h2, tcoK2, reduceCtorEq] at hW
  obtain ⟨b2, a2, hrun2, hS2, hg2, hd2⟩ := fpc_call h h2 hS hl1 (.inl rfl) (by decide)
  have hrun2' : (clauseT fe (decI (pinW m (1 + (40 : Word).toNat))) 3 trueCvA).run a =
      .ok (b2, a2) := hrun2
  simp only [hrun2', exc_ok_bind']
  by_cases e2 : r2.headD 0 = 0
  · rw [ite_eq_left e2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b2 = false := by rw [← hd2.1]; simpa using e2
    exact ⟨false, a2, by simp [hb]; rfl, hS2, hg2, by simp [decW0B]⟩
  rw [ite_eq_right e2] at hW
  have hb2 : b2 = true := by rw [← hd2.1]; simpa using e2
  simp only [hb2, Bool.not_true, Bool.false_eq_true, ite_false]
  -- the `True.intro` clause
  rcases h3 : pinAtW m2 41 with _ | ⟨r3, m3⟩ <;> simp only [h3, tcoK3, reduceCtorEq] at hW
  obtain ⟨hm3, hr3, hl3, hrun3⟩ := pinAtW_ok h3 hS2.1.pins
  rw [hm3, hr3] at hW
  simp only [List.headD_cons] at hW
  simp only [trueIntroName, pinTrueIntro, show PIN_TRUE_INTRO = (41 : Word).toNat from rfl,
    StateT.run_bind, hrun3, exc_ok_bind']
  rcases h4 : callW p n "find_pinned_cv" [vis, pinW m2 (1 + (41 : Word).toNat), 4, 3] m2 with _ | ⟨r4, m4⟩ <;> simp only [h4, tcoK4, reduceCtorEq] at hW
  obtain ⟨b4, a4, hrun4, hS4, hg4, hd4⟩ := fpc_call h h4 hS2 hl3 (.inr rfl) (by decide)
  have hrun4' : (clauseT fe (decI (pinW m2 (1 + (41 : Word).toNat))) 4 trueIntroCvA).run a2 =
      .ok (b4, a4) := hrun4
  simp only [hrun4', exc_ok_bind']
  by_cases e4 : r4.headD 0 = 0
  · rw [ite_eq_left e4] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b4 = false := by rw [← hd4.1]; simpa using e4
    exact ⟨false, a4, by simp [hb]; rfl, hS4, hg2.trans hg4, by simp [decW0B]⟩
  rw [ite_eq_right e4] at hW
  have hb4 : b4 = true := by rw [← hd4.1]; simpa using e4
  simp only [hb4, Bool.not_true, Bool.false_eq_true, ite_false]
  -- the axiom's pin
  rcases h5 : callW p n "rom_cv" [4] m4 with _ | ⟨r5, m5⟩ <;> simp only [h5, tcoK5, reduceCtorEq] at hW
  obtain ⟨pin, a5, hrun5, hS5, hg5, hpin⟩ := h.red.rom.cv dn vis fe 4 (by decide) n m4 a4 r5 m5 hS4 h5
  have hrun5' : trustCompilerA.run a4 = .ok (pin, a5) := hrun5
  have hg := hg2.trans (hg4.trans hg5)
  have hq5 : decCV (erA m5) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg) hq
  obtain ⟨hm6, hrun6, hd6⟩ := mpW_ok (a := a5) hW hS5.2.2.2.2.1 hq5
    (DecB.get ⟨fun _ _ _ he h => he.2.decCV h⟩ hpin)
  subst hm6
  refine ⟨_, a5, ?_, hS5, hg, hd6⟩
  simp only [StateT.run_bind, hrun5', exc_ok_bind']
  exact hrun6

/-- **`trust_compiler_ok(vis, q)` refines `trustCompilerOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.trustCompilerOk]
theorem trustCompilerOk_refines (p : Prog) (h : TcoProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "trust_compiler_ok" [vis, q]
      (fun m a => StageR dn vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (trustCompilerOk fe cv) (KeepPost dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hq⟩
  refine triple_post (tco_specW p h n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := tcoW_ok h hm hS hq
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

end L.Arena
