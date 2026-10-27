import ConAgua.Arena.DeclNatBase
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# The structural-`Nat` gate: the name lists and the dependency tables (lane `decls3`, helper `decls3-nat`)

`nat_op_names`, `nat_div_mod_names`, `nat_op_deps`, `nat_op_deps_stored` refine `natOpNames`,
`natDivModNames`, `natOpDeps`, `natOpDepsStored` on the stage relation, through the `CallRef`
primitives of `DeclNatBase.lean`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of the structural-`Nat` gate's proofs: master's functions (the real ones), the
pool library, and this module's functions. -/
structure NatGateProg (p : Prog) : Prop extends MasterProg p where
  lIwAlloc : p.lookup "iw_alloc" = some iwAlloc
  lRec2 : p.lookup "rec2" = some rec2
  lRec3 : p.lookup "rec3" = some rec3
  lSlNew1 : p.lookup "sl_new1" = some slNew1
  lSlContains : p.lookup "sl_contains" = some slContains
  lEView : p.lookup "e_view" = some eView
  lNatOpNames : p.lookup "nat_op_names" = some natOpNamesL
  lNatDivModNames : p.lookup "nat_div_mod_names" = some natDivModNamesL
  lNatOpPinsA : p.lookup "nat_op_pins_a" = some natOpPinsAL
  lNatOpPinsB : p.lookup "nat_op_pins_b" = some natOpPinsBL
  lNatOpPinsC : p.lookup "nat_op_pins_c" = some natOpPinsCL
  lNatOpPins : p.lookup "nat_op_pins" = some natOpPinsL
  lNatOpDeps : p.lookup "nat_op_deps" = some natOpDepsL
  lNatOpDepsStored : p.lookup "nat_op_deps_stored" = some natOpDepsStoredL

/-! ## `pin_at` as a model -/

def pinAtW (m : Mem) (i : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else if 51 ≤ i then none else some ([rdW (m.arr64 PINS) (1 + i)], m)

theorem pinAt_specW (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St)
    (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ pinAtW s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinAtW, pinW_eq, rdW_eq]

/-- A returning `pin_at(i)`: memory unchanged, flag set, `i < 51`, the word of slot `j = 1 + i`. -/
theorem pinAt_model {p : Prog} (hp : p.lookup "pin_at" = some pinAtL) {n : Nat} {m m' : Mem}
    {i : Word} {r : List Word} (h : callW p n "pin_at" [i] m = some (r, m')) {j : Nat}
    (hj : 1 + i.toNat = j) : m' = m ∧ pinW m 0 ≠ 0 ∧ i.toNat < 51 ∧ r.headD 0 = pinW m j := by
  obtain ⟨s', rfl, -, hmod⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinAt_specW p hp n _ i) h
  change pinAtW m i = some (r, s'.mem) at hmod
  unfold pinAtW at hmod
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at hmod
  rw [ite_eq_right h0] at hmod
  by_cases h1 : 51 ≤ i
  · simp [h1] at hmod
  rw [ite_eq_right h1] at hmod
  simp only [Option.some.injEq, Prod.mk.injEq] at hmod
  obtain ⟨rfl, hm⟩ := hmod
  have hi : i.toNat < 51 := by
    have : ¬ (51 : Word).toNat ≤ i.toNat := fun e => h1 (UInt64.le_iff_toNat_le.mpr e)
    simpa using this
  refine ⟨hm.symm, h0, hi, ?_⟩
  have e1 : (1 + i).toNat = 1 + i.toNat := by rw [UInt64.toNat_add]; simp; omega
  simp [rdW, pinW, e1, hj]

/-- `pin_at(i)` as a pure read: the memory is unchanged, and the word is slot `1 + i`. -/
theorem pinAt_pure (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ pinW s₀.mem 0 ≠ 0 ∧ i.toNat < 51 ∧
      r = [pinW s₀.mem (1 + i.toNat)] ∧ s'.mem = s₀.mem; ⊤⦄ := by
  refine triple_post (pinAt_specW p hp n s₀ i) ?_
  rintro r s' ⟨hl, hm⟩
  unfold pinAtW at hm
  by_cases h0 : pinW s₀.mem 0 = 0
  · simp [h0] at hm
  rw [ite_eq_right h0] at hm
  by_cases h1 : 51 ≤ i
  · simp [h1] at hm
  rw [ite_eq_right h1] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, hm⟩ := hm
  have hi : i.toNat < 51 := by
    have : ¬ (51 : Word).toNat ≤ i.toNat := fun e => h1 (UInt64.le_iff_toNat_le.mpr e)
    simpa using this
  have e1 : (1 + i).toNat = 1 + i.toNat := by rw [UInt64.toNat_add]; simp; omega
  exact ⟨hl, h0, hi, by simp [rdW, pinW, e1], hm.symm⟩

theorem decHL_words {k : IdxKind} (m : Mem) : ∀ (ws : List Word) (o : Nat),
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → (∀ j < ws.length, (iwA m)[o + j]? = ws[j]?) →
    (decHL m o ws.length : Option (List (Idx k))) = some (ws.map decI)
  | [], o, _, _ => by simp [decHL, hslice?]
  | w :: ws, o, hlt, hget => by
    simp only [List.length_cons, decHL, hslice?_succ]
    have h0 : (iwA m)[o]? = some w := by simpa using hget 0 (by simp)
    have hw : w.toNat < 2 ^ 32 := hlt w (by simp)
    have ih := decHL_words (k := k) m ws (o + 1) (fun x hx => hlt x (by simp [hx]))
      (fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hget (j + 1) (by simpa using hj))
    simp only [decHL] at ih
    simp [hd?, h0, hw, ih]

/-- A freshly written handle slice keeps the stage relation and decodes. -/
theorem slice_keep {κ : IdxKind} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {ws : List Word} {q k : Word} (hS : StageR dn vis fe m a)
    (hrec : RecPost m m' [q] ws) (hlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hk : k.toNat = ws.length) :
    KeepPost dn vis fe (decRL (fun m => (decHL m : Nat → Nat → Option (List (Idx κ)))) 0) m m' a [q, k]
      (ws.map (decI : Word → Idx κ)) := by
  obtain ⟨hq, hKeep, hroom, htop, hget⟩ := hrec
  have hq' : q.toNat = iwTop m := by simp only [List.headD_cons] at hq; rw [hq]; rfl
  refine ⟨hKeep.stage hS, hKeep.1, ?_, ?_⟩
  · simp only [List.getD_cons_zero, List.getD_cons_succ, hq']
    rw [show k.toNat = ws.length from hk]
    exact decHL_words (k := κ) m' ws _ hlt (fun j hj => hget j hj)
  · simp only [List.getD_cons_zero, List.getD_cons_succ, hq', hk, htop]; omega

section names
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

def natOpNamesW (p : Prog) (n : Nat) (m : Mem) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else
  ntBW (callW p n "iw_alloc" [7] m) fun rq mq =>
  some ([rq.headD 0, 7], (((((((mq.set64 IW (rq.headD 0) (pinW m 15)).set64 IW (rq.headD 0 + 1) (pinW m 16)).set64 IW (rq.headD 0 + 2) (pinW m 17)).set64 IW (rq.headD 0 + 3) (pinW m 18)).set64 IW (rq.headD 0 + 4) (pinW m 19)).set64 IW (rq.headD 0 + 5) (pinW m 20)).set64 IW (rq.headD 0 + 6) (pinW m 21)))

theorem natOpNames_specW (p : Prog) (hp : p.lookup "nat_op_names" = some natOpNamesL)
    (hpin : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_op_names" []
    ⦃fun r s' => LocEq s' s₀ ∧ natOpNamesW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpNamesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      pinAt_pure p hpin n, callW_spec p n "iw_alloc"] <;>
    finish (gen := 20) [natOpNamesW, ntBW]

theorem natOpNames_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) :
    (natOpNames).run a = .ok ([decI (pinW m 15), decI (pinW m 16), decI (pinW m 17), decI (pinW m 18), decI (pinW m 19), decI (pinW m 20), decI (pinW m 21)], a) := by
  simp [natOpNames, StateT.run_bind, pinAt_run hF, exc_ok_bind', StateT.run_map] <;> rfl

theorem natOpNames_ref (hN : NatGateProg p) :
    CallRef p "nat_op_names" [] (StageR dn vis fe) natOpNames
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := by
  refine CallRef.of_succ fun k m a r m' hS hc => ?_
  have hw := callW_model (M := fun mm => natOpNamesW p k mm) (natOpNames_specW p hN.lNatOpNames hN.lPinAt k ·) hc
  unfold natOpNamesW at hw
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at hw; cases hw
  rw [ite_eq_right h0] at hw
  cases hq : callW p k "iw_alloc" [7] m with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  obtain ⟨hq0, hmq, hKeep, hroom, htop⟩ := iwAlloc_fref p hN.lIwAlloc 7 k m rq mq hS.2 hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hF := hS.1.pins.full h0
  have hlt : ∀ w ∈ [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21], w.toNat < 2 ^ 32 := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hF.names_lt 14 (by decide)
    · exact hF.names_lt 15 (by decide)
    · exact hF.names_lt 16 (by decide)
    · exact hF.names_lt 17 (by decide)
    · exact hF.names_lt 18 (by decide)
    · exact hF.names_lt 19 (by decide)
    · exact hF.names_lt 20 (by decide)
  have hrec := recPost_wr m [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21] 7 rfl hS.2 (by simpa [iwTop] using hroom)
  subst hmq
  rw [hq0]
  have echain : ((((((((allocMem m 7).set64 IW (rdW (m.arr64 CTL) 200) (pinW m 15)).set64 IW (rdW (m.arr64 CTL) 200 + 1) (pinW m 16)).set64 IW (rdW (m.arr64 CTL) 200 + 2) (pinW m 17)).set64 IW (rdW (m.arr64 CTL) 200 + 3) (pinW m 18)).set64 IW (rdW (m.arr64 CTL) 200 + 4) (pinW m 19)).set64 IW (rdW (m.arr64 CTL) 200 + 5) (pinW m 20)).set64 IW (rdW (m.arr64 CTL) 200 + 6) (pinW m 21)) = wrIW (allocMem m 7) (rdW (m.arr64 CTL) 200) [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21] := by
    simp [wrIW, UInt64.add_assoc]
  rw [echain]
  exact ⟨_, a, natOpNames_run hF, slice_keep hS hrec hlt rfl⟩

@[refines ConRon.Arena.natOpNames]
theorem natOpNames_refines (hN : NatGateProg p) :
    RefAM p "nat_op_names" [] (StageR dn vis fe) natOpNames
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) :=
  (natOpNames_ref hN).refAM

def natDivModNamesW (p : Prog) (n : Nat) (m : Mem) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else
  ntBW (callW p n "iw_alloc" [8] m) fun rq mq =>
  some ([rq.headD 0, 8], ((((((((mq.set64 IW (rq.headD 0) (pinW m 22)).set64 IW (rq.headD 0 + 1) (pinW m 23)).set64 IW (rq.headD 0 + 2) (pinW m 24)).set64 IW (rq.headD 0 + 3) (pinW m 25)).set64 IW (rq.headD 0 + 4) (pinW m 26)).set64 IW (rq.headD 0 + 5) (pinW m 27)).set64 IW (rq.headD 0 + 6) (pinW m 28)).set64 IW (rq.headD 0 + 7) (pinW m 29)))

theorem natDivModNames_specW (p : Prog) (hp : p.lookup "nat_div_mod_names" = some natDivModNamesL)
    (hpin : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_div_mod_names" []
    ⦃fun r s' => LocEq s' s₀ ∧ natDivModNamesW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natDivModNamesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      pinAt_pure p hpin n, callW_spec p n "iw_alloc"] <;>
    finish (gen := 20) [natDivModNamesW, ntBW]

theorem natDivModNames_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) :
    (natDivModNames).run a = .ok ([decI (pinW m 22), decI (pinW m 23), decI (pinW m 24), decI (pinW m 25), decI (pinW m 26), decI (pinW m 27), decI (pinW m 28), decI (pinW m 29)], a) := by
  simp [natDivModNames, StateT.run_bind, pinAt_run hF, exc_ok_bind', StateT.run_map] <;> rfl

theorem natDivModNames_ref (hN : NatGateProg p) :
    CallRef p "nat_div_mod_names" [] (StageR dn vis fe) natDivModNames
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := by
  refine CallRef.of_succ fun k m a r m' hS hc => ?_
  have hw := callW_model (M := fun mm => natDivModNamesW p k mm) (natDivModNames_specW p hN.lNatDivModNames hN.lPinAt k ·) hc
  unfold natDivModNamesW at hw
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at hw; cases hw
  rw [ite_eq_right h0] at hw
  cases hq : callW p k "iw_alloc" [8] m with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  obtain ⟨hq0, hmq, hKeep, hroom, htop⟩ := iwAlloc_fref p hN.lIwAlloc 8 k m rq mq hS.2 hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hF := hS.1.pins.full h0
  have hlt : ∀ w ∈ [pinW m 22, pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28, pinW m 29], w.toNat < 2 ^ 32 := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hF.names_lt 21 (by decide)
    · exact hF.names_lt 22 (by decide)
    · exact hF.names_lt 23 (by decide)
    · exact hF.names_lt 24 (by decide)
    · exact hF.names_lt 25 (by decide)
    · exact hF.names_lt 26 (by decide)
    · exact hF.names_lt 27 (by decide)
    · exact hF.names_lt 28 (by decide)
  have hrec := recPost_wr m [pinW m 22, pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28, pinW m 29] 8 rfl hS.2 (by simpa [iwTop] using hroom)
  subst hmq
  rw [hq0]
  have echain : (((((((((allocMem m 8).set64 IW (rdW (m.arr64 CTL) 200) (pinW m 22)).set64 IW (rdW (m.arr64 CTL) 200 + 1) (pinW m 23)).set64 IW (rdW (m.arr64 CTL) 200 + 2) (pinW m 24)).set64 IW (rdW (m.arr64 CTL) 200 + 3) (pinW m 25)).set64 IW (rdW (m.arr64 CTL) 200 + 4) (pinW m 26)).set64 IW (rdW (m.arr64 CTL) 200 + 5) (pinW m 27)).set64 IW (rdW (m.arr64 CTL) 200 + 6) (pinW m 28)).set64 IW (rdW (m.arr64 CTL) 200 + 7) (pinW m 29)) = wrIW (allocMem m 8) (rdW (m.arr64 CTL) 200) [pinW m 22, pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28, pinW m 29] := by
    simp [wrIW, UInt64.add_assoc]
  rw [echain]
  exact ⟨_, a, natDivModNames_run hF, slice_keep hS hrec hlt rfl⟩

@[refines ConRon.Arena.natDivModNames]
theorem natDivModNames_refines (hN : NatGateProg p) :
    RefAM p "nat_div_mod_names" [] (StageR dn vis fe) natDivModNames
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) :=
  (natDivModNames_ref hN).refAM

end names

/-! ## `nat_op_deps` -/

theorem decI_beq_word {κ : IdxKind} {x y : Word} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    ((decI x : Idx κ) == decI y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; rw [beq_self_eq_true]; simp
  · have : (decI x : Idx κ) ≠ decI y := fun e => h (by
      rw [(decI_eq_iff x hx _).mp e]; exact decI_word_self y hy)
    rw [beq_false_of_ne this]; simp [h]

/-- A freshly written slice, from the allocation and the words written. -/
theorem emit_keep {κ : IdxKind} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}
    (hal : p.lookup "iw_alloc" = some iwAlloc) {k : Nat} {m mq m' : Mem} {a : AState}
    {rq r : List Word} {N : Word} {ws : List Word} (hS : StageR dn vis fe m a)
    (hN : N.toNat = ws.length) (hlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hq : callW p k "iw_alloc" [N] m = some (rq, mq)) (hr : r = [rq.headD 0, N])
    (hm : m' = wrIW mq (rq.headD 0) ws) :
    KeepPost dn vis fe (decRL (fun m => (decHL m : Nat → Nat → Option (List (Idx κ)))) 0) m m' a r
      (ws.map (decI : Word → Idx κ)) := by
  obtain ⟨hq0, hmq, hKeep, hroom, htop⟩ := iwAlloc_fref p hal N k m rq mq hS.2 hq
  have hrec := recPost_wr m ws N hN hS.2 (by simpa [iwTop, hN] using hroom)
  subst hmq; subst hr; rw [hq0]; rw [hq0] at hm; subst hm
  exact slice_keep hS hrec hlt hN

section pins
variable {p : Prog}

def natOpPinsAW (m : Mem) (q : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else some ([0], ((((((((m.set64 IW (q) (pinW m 15)).set64 IW (q + 1) (pinW m 16)).set64 IW (q + 2) (pinW m 17)).set64 IW (q + 3) (pinW m 18)).set64 IW (q + 4) (pinW m 19)).set64 IW (q + 5) (pinW m 20)).set64 IW (q + 6) (pinW m 21)).set64 IW (q + 7) (pinW m 22)))

theorem natOpPinsA_specW (p : Prog) (hp : p.lookup "nat_op_pins_a" = some natOpPinsAL)
    (hpin : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nat_op_pins_a" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ natOpPinsAW s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpPinsAL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      pinAt_pure p hpin n] <;>
    finish (gen := 20) [natOpPinsAW]

theorem natOpPinsA_fref (hp : p.lookup "nat_op_pins_a" = some natOpPinsAL)
    (hpin : p.lookup "pin_at" = some pinAtL) (q : Word) :
    FRef p "nat_op_pins_a" [q] (fun _ => True)
      (fun m m' _r => pinW m 0 ≠ 0 ∧ m' = wrIW m q [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21, pinW m 22]) := by
  intro n m _r m' _ hc
  obtain ⟨s', rfl, hl, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natOpPinsA_specW p hp hpin n _ q) hc
  change natOpPinsAW m q = some (_r, s'.mem) at hw
  unfold natOpPinsAW at hw
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at hw; cases hw
  rw [ite_eq_right h0] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, hm⟩ := hw
  refine ⟨h0, ?_⟩
  rw [← hm]
  simp [wrIW, UInt64.add_assoc]

def natOpPinsBW (m : Mem) (q : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else some ([0], (((((((m.set64 IW (q) (pinW m 23)).set64 IW (q + 1) (pinW m 24)).set64 IW (q + 2) (pinW m 25)).set64 IW (q + 3) (pinW m 26)).set64 IW (q + 4) (pinW m 27)).set64 IW (q + 5) (pinW m 28)).set64 IW (q + 6) (pinW m 29)))

theorem natOpPinsB_specW (p : Prog) (hp : p.lookup "nat_op_pins_b" = some natOpPinsBL)
    (hpin : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nat_op_pins_b" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ natOpPinsBW s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpPinsBL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      pinAt_pure p hpin n] <;>
    finish (gen := 20) [natOpPinsBW]

theorem natOpPinsB_fref (hp : p.lookup "nat_op_pins_b" = some natOpPinsBL)
    (hpin : p.lookup "pin_at" = some pinAtL) (q : Word) :
    FRef p "nat_op_pins_b" [q] (fun _ => True)
      (fun m m' _r => pinW m 0 ≠ 0 ∧ m' = wrIW m q [pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28, pinW m 29]) := by
  intro n m _r m' _ hc
  obtain ⟨s', rfl, hl, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natOpPinsB_specW p hp hpin n _ q) hc
  change natOpPinsBW m q = some (_r, s'.mem) at hw
  unfold natOpPinsBW at hw
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at hw; cases hw
  rw [ite_eq_right h0] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, hm⟩ := hw
  refine ⟨h0, ?_⟩
  rw [← hm]
  simp [wrIW, UInt64.add_assoc]

def natOpPinsCW (m : Mem) (q : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else some ([0], ((((((m.set64 IW (q) (pinW m 2)).set64 IW (q + 1) (pinW m 3)).set64 IW (q + 2) (pinW m 4)).set64 IW (q + 3) (pinW m 31)).set64 IW (q + 4) (pinW m 32)).set64 IW (q + 5) (pinW m 30)))

theorem natOpPinsC_specW (p : Prog) (hp : p.lookup "nat_op_pins_c" = some natOpPinsCL)
    (hpin : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nat_op_pins_c" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ natOpPinsCW s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpPinsCL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      pinAt_pure p hpin n] <;>
    finish (gen := 20) [natOpPinsCW]

theorem natOpPinsC_fref (hp : p.lookup "nat_op_pins_c" = some natOpPinsCL)
    (hpin : p.lookup "pin_at" = some pinAtL) (q : Word) :
    FRef p "nat_op_pins_c" [q] (fun _ => True)
      (fun m m' _r => pinW m 0 ≠ 0 ∧ m' = wrIW m q [pinW m 2, pinW m 3, pinW m 4, pinW m 31, pinW m 32, pinW m 30]) := by
  intro n m _r m' _ hc
  obtain ⟨s', rfl, hl, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (natOpPinsC_specW p hp hpin n _ q) hc
  change natOpPinsCW m q = some (_r, s'.mem) at hw
  unfold natOpPinsCW at hw
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at hw; cases hw
  rw [ite_eq_right h0] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, hm⟩ := hw
  refine ⟨h0, ?_⟩
  rw [← hm]
  simp [wrIW, UInt64.add_assoc]

/-- The 21 words `nat_op_pins` writes. -/
def pinRecW (m : Mem) : List Word :=
  [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21, pinW m 22,
   pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28, pinW m 29,
   pinW m 2, pinW m 3, pinW m 4, pinW m 31, pinW m 32, pinW m 30]

def natOpPinsW (p : Prog) (n : Nat) (m : Mem) : Option (List Word × Mem) :=
  ntBW (callW p n "iw_alloc" [21] m) fun rq mq =>
  ntBW (callW p n "nat_op_pins_a" [rq.headD 0] mq) fun _ ma =>
  ntBW (callW p n "nat_op_pins_b" [rq.headD 0 + 8] ma) fun _ mb =>
  ntBW (callW p n "nat_op_pins_c" [rq.headD 0 + 15] mb) fun _ mc => some ([rq.headD 0], mc)

theorem natOpPins_specW (p : Prog) (hp : p.lookup "nat_op_pins" = some natOpPinsL) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_op_pins" []
    ⦃fun r s' => LocEq s' s₀ ∧ natOpPinsW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpPinsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "iw_alloc", callW_spec p n "nat_op_pins_a", callW_spec p n "nat_op_pins_b",
      callW_spec p n "nat_op_pins_c"] <;>
    finish (gen := 20) [natOpPinsW, ntBW]

theorem pinW_wrIW (m : Mem) (q : Word) (ws : List Word) (j : Nat) :
    pinW (wrIW m q ws) j = pinW m j := by
  simp only [pinW, wrIW_arr_ne ws m q PINS (by decide)]

theorem pinW_allocMem (m : Mem) (k : Word) (j : Nat) : pinW (allocMem m k) j = pinW m j := by
  simp only [pinW, allocMem, Mem.arr64_set64_ne _ _ _ _ _ (show PINS ≠ CTL by decide)]

/-- **`nat_op_pins`**: the record of the pin words, a fresh slice of the pool. -/
theorem natOpPins_fref (hN : NatGateProg p) :
    FRef p "nat_op_pins" [] (fun m => IWOK m)
      (fun m m' r => pinW m 0 ≠ 0 ∧ RecPost m m' r (pinRecW m) ∧ m'.arr64 PINS = m.arr64 PINS ∧
        r = [r.headD 0]) := by
  refine FRef.of_succ fun k m r m' hI hc => ?_
  have hw := callW_model (M := fun mm => natOpPinsW p k mm) (natOpPins_specW p hN.lNatOpPins k ·) hc
  unfold natOpPinsW at hw
  cases hq : callW p k "iw_alloc" [21] m with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  cases ha : callW p k "nat_op_pins_a" [rq.headD 0] mq with
  | none => rw [ha] at hw; simp at hw
  | some qa =>
  obtain ⟨ra, ma⟩ := qa
  rw [ha, bW_some] at hw
  cases hb : callW p k "nat_op_pins_b" [rq.headD 0 + 8] ma with
  | none => rw [hb] at hw; simp at hw
  | some qb =>
  obtain ⟨rb, mb⟩ := qb
  rw [hb, bW_some] at hw
  cases hc' : callW p k "nat_op_pins_c" [rq.headD 0 + 15] mb with
  | none => rw [hc'] at hw; simp at hw
  | some qc =>
  obtain ⟨rc, mc⟩ := qc
  rw [hc', bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨hq0, hmq, hKeep, hroom, htop⟩ := iwAlloc_fref p hN.lIwAlloc 21 k m rq mq hI hq
  obtain ⟨h0a, hma⟩ := natOpPinsA_fref hN.lNatOpPinsA hN.lPinAt (rq.headD 0) k mq ra ma trivial ha
  obtain ⟨h0b, hmb⟩ := natOpPinsB_fref hN.lNatOpPinsB hN.lPinAt (rq.headD 0 + 8) k ma rb mb trivial hb
  obtain ⟨h0c, hmc⟩ := natOpPinsC_fref hN.lNatOpPinsC hN.lPinAt (rq.headD 0 + 15) k mb rc mc trivial hc'
  have h0 : pinW m 0 ≠ 0 := by
    rw [← pinW_allocMem m 21 0, ← hmq]; exact h0a
  subst hmq
  subst hma
  subst hmb
  subst hmc
  simp only [pinW_wrIW, pinW_allocMem] at *
  have hroom' : iwTop m + (pinRecW m).length ≤ (m.arr64 IW).size := by
    simpa [iwTop, pinRecW] using hroom
  have hrec := recPost_wr m (pinRecW m) 21 rfl hI hroom'
  have hcomp : wrIW (wrIW (wrIW (allocMem m 21) (rdW (m.arr64 CTL) 200)
        [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21, pinW m 22])
        (rdW (m.arr64 CTL) 200 + 8) [pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28, pinW m 29])
        (rdW (m.arr64 CTL) 200 + 15) [pinW m 2, pinW m 3, pinW m 4, pinW m 31, pinW m 32, pinW m 30] =
      wrIW (allocMem m 21) (rdW (m.arr64 CTL) 200) (pinRecW m) := by
    simp [wrIW, UInt64.add_assoc, pinRecW]
  rw [hq0]
  rw [hcomp]
  refine ⟨h0, hrec.1.symm ▸ hrec, ?_, rfl⟩
  rw [wrIW_arr_ne _ _ _ _ (by decide)]
  simp only [allocMem, Mem.arr64_set64_ne _ _ _ _ _ (show PINS ≠ CTL by decide)]

end pins

/-! ## `nat_op_deps` -/

theorem KeepPost.of_grow {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {α : Type}
    {dec : Mem → List Word → α → Prop} {m1 m m' : Mem} {a : AState} {r : List Word} {x : α}
    (h : KeepPost dn vis fe dec m1 m' a r x) (hg : IWGrow m m1) : KeepPost dn vis fe dec m m' a r x :=
  ⟨h.1, hg.trans h.2.1, h.2.2⟩

end L.Ind
