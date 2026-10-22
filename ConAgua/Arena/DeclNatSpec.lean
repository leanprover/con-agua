import ConAgua.Arena.DeclNatBase

/-!
# The structural-`Nat` gate: the name lists and the dependency tables (lane `decls3`, helper `decls3-nat`)

`nat_op_names`, `nat_div_mod_names`, `nat_op_deps`, `nat_op_deps_stored` refine `natOpNames`,
`natDivModNames`, `natOpDeps`, `natOpDepsStored` on the stage relation, through the `CallRef`
primitives of `DeclNatBase.lean`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
  rw [if_neg h0] at hmod
  by_cases h1 : 51 ≤ i
  · simp [h1] at hmod
  rw [if_neg h1] at hmod
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
  rw [if_neg h0] at hm
  by_cases h1 : 51 ≤ i
  · simp [h1] at hm
  rw [if_neg h1] at hm
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
  · simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, hq']
    rw [show k.toNat = ws.length from hk]
    exact decHL_words (k := κ) m' ws _ hlt (fun j hj => hget j hj)
  · simp only [List.getD_cons_zero, List.getD_cons_succ, hq', hk, htop]; omega

section names
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

def natOpNamesW (p : Prog) (n : Nat) (m : Mem) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else
  bW (callW p n "iw_alloc" [7] m) fun rq mq =>
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
    finish (gen := 20) [natOpNamesW, bW]

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
  · rw [if_pos h0] at hw; cases hw
  rw [if_neg h0] at hw
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
  bW (callW p n "iw_alloc" [8] m) fun rq mq =>
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
    finish (gen := 20) [natDivModNamesW, bW]

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
  · rw [if_pos h0] at hw; cases hw
  rw [if_neg h0] at hw
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

end L.Ind
