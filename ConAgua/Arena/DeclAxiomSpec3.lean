import ConAgua.Arena.DeclAxiomSpec2
import ConAgua.Arena.DeclCanonSpec2

/-!
# The standard axioms: `find_pinned`, `std_axiom_ok` (lane `decls3`)

`find_pinned(vis, n, k, a, b, id)` is one clause of `stdAxiomOk`: the stored constant `n` has the
pinned shape (`k = 3` an inductive, `4` a constructor with counts `a`, `b`, `5` a recursor with
counts `a`, `b`) and its constant value matches the pin `rom_ci(id)`'s (`ci_to_cv`, helper
`decls3-canon`). `std_axiom_ok(vis, q)` runs the pinned `Eq` test and three clauses for `propext`,
or three clauses for `Classical.choice`. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The pinned shape `(k, a, b)` of a stored constant: its constant value when it has the shape. -/
def fpShape (k a b : Word) : IConstantInfo → Option IConstantVal
  | .indInfo cv _ => if k = 3 then some cv else none
  | .ctorInfo cv nP nF => if k = 4 ∧ nP = a.toNat ∧ nF = b.toNat then some cv else none
  | .recInfo cv mI rP _ => if k = 5 ∧ mI = a.toNat ∧ rP = b.toNat then some cv else none
  | _ => none

/-- The two counts of a stored constructor or recursor, as words against `a`, `b`. -/
theorem counts_words {arr : Array Word} {q a b : Word} {x y : Nat} (hsz : arr.size < 2 ^ 64)
    (hx : nat? arr (q.toNat + 5) = some x) (hy : nat? arr (q.toNat + 6) = some y) :
    ((rdW arr (q + 5) ≠ a ∨ rdW arr (q + 6) ≠ b) ↔ ¬ (x = a.toNat ∧ y = b.toNat)) := by
  obtain ⟨w5, e5, rfl⟩ := natD hx
  obtain ⟨w6, e6, rfl⟩ := natD hy
  have hq5 : (q + 5).toNat = q.toNat + 5 := by
    have := (Array.getElem?_eq_some_iff.mp e5).1; rw [UInt64.toNat_add]; simp; omega
  have hq6 : (q + 6).toNat = q.toNat + 6 := by
    have := (Array.getElem?_eq_some_iff.mp e6).1; rw [UInt64.toNat_add]; simp; omega
  have r5 : rdW arr (q + 5) = w5 := by simp [rdW, hq5, e5]
  have r6 : rdW arr (q + 6) = w6 := by simp [rdW, hq6, e6]
  rw [r5, r6]
  have i5 : w5 = a ↔ w5.toNat = a.toNat := ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.mp h⟩
  have i6 : w6 = b ↔ w6.toNat = b.toNat := ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.mp h⟩
  rw [Ne, Ne, i5, i6]
  omega

/-- **The shape tests, failing**: the twin's shape does not match. -/
theorem fp_fail {arr : Array Word} {dn : NIdx → Option ConLeche.Name} {q k a b : Word}
    {ci : IConstantInfo} (hsz : arr.size < 2 ^ 64) (hk : k = 3 ∨ k = 4 ∨ k = 5)
    (h : decCI arr dn q.toNat = some ci)
    (hf : rdW arr q ≠ k ∨ (k ≠ 3 ∧ (rdW arr (q + 5) ≠ a ∨ rdW arr (q + 6) ≠ b))) :
    fpShape k a b ci = none := by
  obtain ⟨wk, e, hk'⟩ := ciD h
  have ew : rdW arr q = wk := by simp [rdW, e]
  rw [ew] at hf
  have hw : wk = UInt64.ofNat wk.toNat := by simp
  rcases hk' with ⟨h1, cv, -, rfl⟩ | ⟨h1, cv, v, hi, -, -, -, rfl⟩ | ⟨h1, cv, -, rfl⟩ |
      ⟨h1, cv, caps, -, -, rfl⟩ | ⟨h1, cv, np, nf, -, hnp, hnf, rfl⟩ |
      ⟨h1, cv, mi, rp, o, c, rules, -, hmi, hrp, -, -, -, rfl⟩
  · simp [fpShape]
  · simp [fpShape]
  · simp [fpShape]
  · rw [hw, h1] at hf
    simp only [fpShape]
    rcases hk with rfl | rfl | rfl
    · rcases hf with hf | ⟨hf, -⟩ <;> simp at hf
    · simp
    · simp
  · rw [hw, h1] at hf
    simp only [fpShape]
    rcases hk with rfl | rfl | rfl
    · simp
    · rcases hf with hf | ⟨-, hf⟩
      · simp at hf
      · rw [counts_words hsz hnp hnf] at hf
        simp only [true_and]; simp [hf]
    · simp
  · rw [hw, h1] at hf
    simp only [fpShape]
    rcases hk with rfl | rfl | rfl
    · simp
    · simp
    · rcases hf with hf | ⟨-, hf⟩
      · simp at hf
      · rw [counts_words hsz hmi hrp] at hf
        simp only [true_and]; simp [hf]

/-- **The shape tests, passing**: the twin's shape matches. -/
theorem fp_pass {arr : Array Word} {dn : NIdx → Option ConLeche.Name} {q k a b : Word}
    {ci : IConstantInfo} (hsz : arr.size < 2 ^ 64) (hk : k = 3 ∨ k = 4 ∨ k = 5)
    (h : decCI arr dn q.toNat = some ci) (hkw : rdW arr q = k)
    (hc : ¬ (k ≠ 3 ∧ (rdW arr (q + 5) ≠ a ∨ rdW arr (q + 6) ≠ b))) :
    ∃ cv, fpShape k a b ci = some cv := by
  obtain ⟨wk, e, hk'⟩ := ciD h
  have ew : rdW arr q = wk := by simp [rdW, e]
  rw [ew] at hkw
  subst hkw
  rcases hk' with ⟨h1, cv, -, rfl⟩ | ⟨h1, cv, v, hi, -, -, -, rfl⟩ | ⟨h1, cv, -, rfl⟩ |
      ⟨h1, cv, caps, hcv, -, rfl⟩ | ⟨h1, cv, np, nf, hcv, hnp, hnf, rfl⟩ |
      ⟨h1, cv, mi, rp, o, c, rules, hcv, hmi, hrp, -, -, -, rfl⟩ <;>
    rcases hk with hk | hk | hk <;> rw [hk] at h1 <;> simp at h1
  · exact ⟨cv, by simp [fpShape, hk]⟩
  · have hcc := counts_words (a := a) (b := b) hsz hnp hnf
    have h0 : np = a.toNat ∧ nf = b.toNat := by
      by_cases hx : np = a.toNat ∧ nf = b.toNat
      · exact hx
      · exact absurd ⟨by rw [hk]; decide, hcc.mpr hx⟩ hc
    exact ⟨cv, by simp [fpShape, hk, h0]⟩
  · have hcc := counts_words (a := a) (b := b) hsz hmi hrp
    have h0 : mi = a.toNat ∧ rp = b.toNat := by
      by_cases hx : mi = a.toNat ∧ rp = b.toNat
      · exact hx
      · exact absurd ⟨by rw [hk]; decide, hcc.mpr hx⟩ hc
    exact ⟨cv, by simp [fpShape, hk, h0]⟩

/-- A matching shape's constant value decodes where the record does. -/
theorem fpShape_cv {arr : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {k a b : Word}
    {ci : IConstantInfo} {cv : IConstantVal} (h : decCI arr dn q = some ci)
    (hs : fpShape k a b ci = some cv) : decCV arr (q + 1) = some cv := by
  obtain ⟨wk, -, hk'⟩ := ciD h
  rcases hk' with ⟨-, cv', -, rfl⟩ | ⟨-, cv', v, hi, -, -, -, rfl⟩ | ⟨-, cv', -, rfl⟩ |
      ⟨-, cv', caps, hcv, -, rfl⟩ | ⟨-, cv', np, nf, hcv, -, -, rfl⟩ |
      ⟨-, cv', mi, rp, o, c, rules, hcv, -, -, -, -, -, rfl⟩ <;>
    simp only [fpShape] at hs <;> (try cases hs)
  · split at hs <;> cases hs; exact hcv
  · split at hs <;> cases hs; exact hcv
  · split at hs <;> cases hs; exact hcv

/-- What one clause of `stdAxiomOk` does. -/
def FpT (fe : IFEnv) (nm : NIdx) (k a b : Word) (T : AM IConstantVal) (a0 : AState) (res : Bool)
    (a' : AState) : Prop :=
  ((fe.find? nm).bind (fpShape k a b)).elim (res = false ∧ a' = a0)
    (fun cvT => (do let pin ← T; pure (decide (cvT = pin)) : AM Bool).run a0 = .ok (res, a'))

/-- The pin of a clause: the ROM constant's constant value. -/
def romPinT (id : Nat) : AM IConstantVal := do return (← romCiT id).toConstantVal

section model
variable (p : Prog)

/-- After `ci_to_cv`: the comparison. -/
def fpK3 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => mpW m3 (q + 1) (r3.headD 0)

/-- After `rom_ci(id)`. -/
def fpK2 (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => fpK3 q (callW p n "ci_to_cv" [r2.headD 0] m2)

/-- After the lookup: the shape tests. -/
def fpK1 (n : Nat) (k ca cb id : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ k then some ([0], m1)
    else if k ≠ 3 ∧ (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 5) ≠ ca ∨
        rdW (m1.arr64 EREC) (r1.tail.headD 0 + 6) ≠ cb) then some ([0], m1)
    else fpK2 p n (r1.tail.headD 0) (callW p n "rom_ci" [id] m1)

/-- **The model of `find_pinned(vis, n, k, a, b, id)`.** -/
def fpW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nm, k, ca, cb, id => fpK1 p n k ca cb id (envFindW m nm vis)

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (vis nm k ca cb id q : Word) (r1 r2 r3 : List Word)
theorem fpW_step : fpW p (n + 1) m vis nm k ca cb id = fpK1 p n k ca cb id (envFindW m nm vis) :=
  rfl
theorem fpK1_some : fpK1 p n k ca cb id (some (r1, m1)) =
    if r1.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ k then some ([0], m1)
    else if k ≠ 3 ∧ (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 5) ≠ ca ∨
        rdW (m1.arr64 EREC) (r1.tail.headD 0 + 6) ≠ cb) then some ([0], m1)
    else fpK2 p n (r1.tail.headD 0) (callW p n "rom_ci" [id] m1) := rfl
theorem fpK2_some : fpK2 p n q (some (r2, m2)) = fpK3 q (callW p n "ci_to_cv" [r2.headD 0] m2) :=
  rfl
theorem fpK3_some : fpK3 q (some (r3, m3)) = mpW m3 (q + 1) (r3.headD 0) := rfl
end arms

grind_pattern [ind_grind] fpW_step => fpW p (n + 1) m vis nm k ca cb id
grind_pattern [ind_grind] fpK1_some => fpK1 p n k ca cb id (some (r1, m1))
grind_pattern [ind_grind] fpK2_some => fpK2 p n q (some (r2, m2))
grind_pattern [ind_grind] fpK3_some => fpK3 q (some (r3, m3))

/-- The lookups of the standard axioms' test. -/
structure StdProg (p : Prog) : Prop where
  red : RedProg p
  fp : p.lookup "find_pinned" = some findPinned
  std : p.lookup "std_axiom_ok" = some stdAxiomOkL

set_option maxHeartbeats 1600000 in
theorem fp_specW (h : StdProg p) (n : Nat) (s₀ : St) (vis nm k ca cb id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "find_pinned" [vis, nm, k, ca, cb, id]
    ⦃fun r s' => LocEq s' s₀ ∧ fpW p n s₀.mem vis nm k ca cb id = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.fp]
  simp only [callFn, findPinned]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p h.red.ih.ix h.red.ih.rowGet h.red.ih.find n, callW_spec p n "rom_ci",
        callW_spec p n "ci_to_cv", mp_specW p h.red.canon h.red.mp n] <;>
      finish (gen := 20) [rdW_eq, mpW]

end model

/-- **`find_pinned` against the twin's clause**, at the model level. -/
theorem fpW_ok {p : Prog} (h : StdProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k ca cb id : Word} {r : List Word}
    (hW : fpW p n m vis nm k ca cb id = some (r, m')) (hS : StageR dn vis fe m a)
    (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4 ∨ k = 5) (hid : id.toNat < 8) :
    ∃ b a', StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧
      FpT fe (decI nm) k ca cb (romPinT id.toNat) a b a' := by
  cases n with
  | zero => simp [fpW] at hW
  | succ n =>
  rw [fpW_step] at hW
  rcases h1 : envFindW m nm vis with _ | ⟨r1, m1⟩ <;> simp only [h1, fpK1, reduceCtorEq] at hW
  by_cases hf : r1.headD 0 = 0
  · rw [if_pos hf] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.1.env hnm hf
    exact ⟨false, a, hS, IWGrow.refl _, by simp [decW0B], by simp [FpT, hfind]⟩
  rw [if_neg hf] at hW
  obtain ⟨rfl, hptr, hfind, htag, hrc⟩ := envFindW_hit h1 hS.1.env hnm hf
  obtain ⟨ci, hci⟩ := envR_row_dec hS.1.env nm hnm htag hrc
  rw [hptr] at hW
  generalize hq : rowP m1 nm = q at hW hci hfind
  have hsz := hS.2.2.2.2.1
  have hciA : decCI (m1.arr64 EREC) dn q.toNat = some ci := ArrExt.decCI (erecP_ext m1) hci
  have hbind : (fe.find? (decI nm)).bind (fpShape k ca cb) = fpShape k ca cb ci := by
    rw [hfind, hci]; rfl
  by_cases hfail : rdW (m1.arr64 EREC) q ≠ k ∨
      (k ≠ 3 ∧ (rdW (m1.arr64 EREC) (q + 5) ≠ ca ∨ rdW (m1.arr64 EREC) (q + 6) ≠ cb))
  · have hnone := fp_fail hsz hk hciA hfail
    have hW' : some ([(0 : Word)], m1) = some (r, m') := by
      rw [← hW]
      by_cases h2 : rdW (m1.arr64 EREC) q ≠ k
      · rw [if_pos h2]
      · rw [if_neg h2]
        rcases hfail with h1 | h1
        · exact absurd h1 h2
        · rw [if_pos h1]
    simp only [Option.some.injEq, Prod.mk.injEq] at hW'
    obtain ⟨rfl, rfl⟩ := hW'
    exact ⟨false, a, hS, IWGrow.refl _, by simp [decW0B], by simp [FpT, hbind, hnone]⟩
  have hkw : rdW (m1.arr64 EREC) q = k := by
    by_cases hne : rdW (m1.arr64 EREC) q = k
    · exact hne
    · exact absurd (.inl hne) hfail
  have hc : ¬ (k ≠ 3 ∧ (rdW (m1.arr64 EREC) (q + 5) ≠ ca ∨ rdW (m1.arr64 EREC) (q + 6) ≠ cb)) :=
    fun hx => hfail (.inr hx)
  rw [if_neg (by simpa using hkw), if_neg hc] at hW
  obtain ⟨cvT, hshape⟩ := fp_pass hsz hk hciA hkw hc
  have hcvP := fpShape_cv hci hshape
  -- the pin's constant
  rcases h2 : callW p n "rom_ci" [id] m1 with _ | ⟨r2, m2⟩ <;> simp only [h2, fpK2, reduceCtorEq] at hW
  obtain ⟨pci, a2, hrun2, hS2, hg2, hpci⟩ := h.red.rom.ci dn vis fe id hid n m1 a r2 m2 hS h2
  have hpciP : decCI (erecP m2) dn (r2.headD 0).toNat = some pci :=
    ArrExt.decCI (truncM_erecP m2) hpci
  -- its constant value
  rcases h3 : callW p n "ci_to_cv" [r2.headD 0] m2 with _ | ⟨r3, m3⟩ <;> simp only [h3, fpK3, reduceCtorEq] at hW
  obtain ⟨s3, hs3, -, hok3, hS3, hg3, hcv3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (ciToCv_refines p h.red.canon dn vis fe (r2.headD 0) pci n ⟨m2, Locals.init []⟩ a2
      ⟨hS2, hpciP⟩) h3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  generalize AM.res (pure pci.toConstantVal : AM IConstantVal) a2 = pin at hrun3 hcv3
  generalize AM.st (pure pci.toConstantVal : AM IConstantVal) a2 = a3 at hrun3 hS3
  have hq1b : q.toNat + 1 < 2 ^ 64 := by
    obtain ⟨w, hw, -, -⟩ := decCV_typeW hcvP
    have := erecP_bound hw hS.2; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 hq1b
  have hg := hg2.trans hg3
  have hcvS : decCV (erA s3.mem) (q + 1).toNat = some cvT := by
    rw [hq1]; exact ArrExt.decCV (IWGrow.erecExt hg) hcvP
  obtain ⟨hm4, hrun4, hd4⟩ := mpW_ok (a := a3) hW hS3.2.2.2.2.1 hcvS
    (ArrExt.decCV (erecP_ext s3.mem) hcv3)
  subst hm4
  refine ⟨_, a3, hS3, hg, hd4, ?_⟩
  simp only [FpT, hbind, hshape, Option.elim, romPinT, StateT.run_bind, hrun2, exc_ok_bind', hrun3]
  rw [matchesPin_eq] at hrun4
  exact hrun4

/-! ## `stdAxiomOk`, flattened -/

/-- A clause of `stdAxiomOk`: the stored constant has the pinned shape, its constant value matches
the pin. -/
def clausePT (fe : IFEnv) (nm : NIdx) (k a b : Word) (T : AM IConstantVal) : AM Bool :=
  match (fe.find? nm).bind (fpShape k a b) with
  | some cvT => do cvT.matchesPin (← T)
  | none => pure false

theorem stdAxiomOk_eq (fe : IFEnv) (cv : IConstantVal) :
    stdAxiomOk fe cv = (do
      let pn ← propextName
      if cv.name == pn then do
        let en ← pinEq
        let ea ← eqA
        if fe.find? en != some ea then pure false else do
          let b1 ← clausePT fe (← iffName) 3 0 0 (romPinT 2)
          if !b1 then pure false else do
            let b2 ← clausePT fe (← iffIntroName) 4 2 2 (romPinT 3)
            if !b2 then pure false else do
              let b3 ← clausePT fe (← iffRecName) 5 4 4 (romPinT 4)
              if !b3 then pure false else cv.matchesPin (← propextA)
      else do
        let cn ← choiceName
        if cv.name == cn then do
          let b1 ← clausePT fe (← nonemptyName) 3 0 0 (romPinT 5)
          if !b1 then pure false else do
            let b2 ← clausePT fe (← nonemptyIntroName) 4 1 1 (romPinT 6)
            if !b2 then pure false else do
              let b3 ← clausePT fe (← nonemptyRecName) 5 3 3 (romPinT 7)
              if !b3 then pure false else cv.matchesPin (← choiceA)
        else pure false) := by
  unfold stdAxiomOk clausePT romPinT
  simp only [bind_assoc]
  congr 1; funext pn
  split
  congr 1; funext en; congr 1; funext ea
  split
  rfl
  rotate_left
  congr 1; funext cn
  split
  rotate_left
  rfl
  all_goals
    congr 1; funext x1
    cases h1 : fe.find? x1 with
    | none => simp [h1]
    | some c1 =>
      cases c1
      all_goals try (simp [h1, fpShape]; done)
      simp only [h1, Option.bind_some, fpShape, ↓reduceIte, bind_assoc, pure_bind]
      congr 1; funext c; congr 1; funext b
      split
      · rfl
      congr 1; funext x2
      cases h2 : fe.find? x2 with
      | none => simp [h2]
      | some c2 =>
        cases c2
        all_goals try (simp [h2, fpShape]; done)
        simp only [h2, Option.bind_some, fpShape, true_and, bind_assoc, pure_bind]
        split
        · rename_i heq
          simp only [Option.some.injEq, IConstantInfo.ctorInfo.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          simp only [UInt64.reduceToNat, and_self, ↓reduceIte, bind_assoc, pure_bind]
          congr 1; funext c; congr 1; funext b
          split
          · rfl
          congr 1; funext x3
          cases h3 : fe.find? x3 with
          | none => simp [h3]
          | some c3 =>
            cases c3
            all_goals try (simp [h3, fpShape]; done)
            simp only [h3, Option.bind_some, fpShape, true_and, bind_assoc, pure_bind]
            split
            · rename_i heq
              simp only [Option.some.injEq, IConstantInfo.recInfo.injEq] at heq
              obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
              simp only [UInt64.reduceToNat, and_self, ↓reduceIte, bind_assoc, pure_bind]
              congr 1
            · rename_i hne
              rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hne _ _ rfl)]
              simp
        · rename_i hne
          rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hne _ rfl)]
          simp

theorem clausePT_of_fp {fe : IFEnv} {nm : NIdx} {k ca cb : Word} {T : AM IConstantVal}
    {a a' : AState} {b : Bool} (h : FpT fe nm k ca cb T a b a') :
    (clausePT fe nm k ca cb T).run a = .ok (b, a') := by
  unfold FpT at h
  unfold clausePT
  cases hb : (fe.find? nm).bind (fpShape k ca cb) with
  | none => rw [hb] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | some cvT =>
    rw [hb] at h
    simp only [Option.elim] at h
    simp only [matchesPin_eq]
    exact h

end L.Arena
