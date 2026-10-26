import ConAgua.Arena.PromoteTblRef2

/-!
# `promote_new` refines `promoteNew` under the loop's relation
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Front (DECL DLP DeclsF)

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`promote_new_consts` refines `promoteNewConsts`**, at the memo the caller holds. -/
theorem pconsts_rel {pins : List INatOpPinSet} (dn : NIdx → Option ConLeche.Name) (n : Nat) (m : Mem)
    (a : AState) (pm : PMemo) (k vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (ds : Array IDeclaration) (r : List Word) (m' : Mem) (hP : PMemoR m pm)
    (hR : LoopR pins dn m a vis fe pend ds) (hk : k.toNat ≤ vis.toNat)
    (hc : callW p n "promote_new_consts" [k, vis] m = some (r, m')) :
    ∃ a' pm' fe', (promoteNewConsts pm coreWalkFuel k.toNat fe).run a = .ok ((pm', fe'), a') ∧
      LoopR pins dn m' a' vis fe' pend ds ∧ PMemoR m' pm' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteNewConsts_spec p hp n ⟨m, Locals.init []⟩ k vis) hc
  simp only at hW
  rw [hs'] at hW
  obtain ⟨⟨consts, tables⟩, idx, vb, tbls⟩ := fe
  by_cases hk0 : k = 0
  · have hm : m = m' := by simpa [newCW, hk0] using hW
    subst hm
    have hk0' : k.toNat = 0 := by rw [hk0]; rfl
    refine ⟨a, pm, ⟨⟨consts, tables⟩, idx, vb, tbls⟩, ?_, hR, hP⟩
    simp [promoteNewConsts, hk0']; rfl
  have hk0' : (k.toNat == 0) = false := by
    have : k.toNat ≠ 0 := fun h => hk0 (UInt64.toNat_inj.mp (by simpa using h))
    simpa using this
  obtain ⟨a', pm', L', hrun, hLoop, hP'⟩ := pnew_main p hp dn n m a pm k vis consts tables idx vb tbls
    pend ds m' hP hR hk hk0 hW
  refine ⟨a', pm', _, ?_, hLoop, hP'⟩
  simp only [promoteNewConsts, hk0', Bool.false_eq_true, ↓reduceIte]
  rw [run_bind_ok hrun]; rfl

/-- **`promote_new_tables` refines `promoteNewTables`**, at the memo the caller holds. -/
theorem ptablesNew_rel {pins : List INatOpPinSet} (dn : NIdx → Option ConLeche.Name) (n : Nat) (m : Mem)
    (a : AState) (pm : PMemo) (kt vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (ds : Array IDeclaration) (r : List Word) (m' : Mem) (hP : PMemoR m pm)
    (hR : LoopR pins dn m a vis fe pend ds)
    (hc : callW p n "promote_new_tables" [kt] m = some (r, m')) :
    ∃ a' pm' fe', (promoteNewTables pm coreWalkFuel kt.toNat fe).run a = .ok ((pm', fe'), a') ∧
      LoopR pins dn m' a' vis fe' pend ds ∧ PMemoR m' pm' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteNewTables_spec p hp n ⟨m, Locals.init []⟩ kt) hc
  simp only at hW
  rw [hs'] at hW
  obtain ⟨⟨consts, tables⟩, idx, vb, tbls⟩ := fe
  by_cases hk0 : kt = 0
  · have hm : m = m' := by simpa [newTW, hk0] using hW
    subst hm
    have hk0' : kt.toNat = 0 := by rw [hk0]; rfl
    refine ⟨a, pm, ⟨⟨consts, tables⟩, idx, vb, tbls⟩, ?_, hR, hP⟩
    simp [promoteNewTables, hk0']; rfl
  have hk0' : (kt.toNat == 0) = false := by
    have : kt.toNat ≠ 0 := fun h => hk0 (UInt64.toNat_inj.mp (by simpa using h))
    simpa using this
  obtain ⟨a', pm', L', hrun, hLoop, hP'⟩ := ptnew_main p hp dn n m a pm kt vis consts tables idx vb tbls
    pend ds m' hP hR hk0 hW
  refine ⟨a', pm', _, ?_, hLoop, hP'⟩
  simp only [promoteNewTables, hk0', Bool.false_eq_true, ↓reduceIte]
  rw [run_bind_ok hrun]; rfl

theorem promoteNew_rel {pins : List INatOpPinSet} (dn : NIdx → Option ConLeche.Name) (n : Nat) (m : Mem) (a : AState)
    (pm : PMemo) (k kt vis fresh : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (ds : Array IDeclaration) (r : List Word) (m' : Mem)
    (hpm : if fresh = 0 then PMemoR m pm else pm = PMemo.empty)
    (hR : LoopR pins dn m a vis fe pend ds) (hk : k.toNat ≤ vis.toNat)
    (hc : callW p n "promote_new" [k, kt, vis, fresh] m = some (r, m')) :
    ∃ a' pm' fe', (promoteNew pm coreWalkFuel k.toNat kt.toNat fe).run a = .ok ((pm', fe'), a') ∧
      LoopR pins dn m' a' vis fe' pend ds := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteNew_specW p hp n ⟨m, Locals.init []⟩ k kt vis fresh) hc
  simp only at hW
  rw [hs'] at hW
  simp only [newW] at hW
  -- the memo: the caller's, or cleared
  obtain ⟨m₁, hm₁, hP₁, hR₁⟩ : ∃ m₁, (if fresh ≠ 0 then
      (callW p n "promote_clear" [] m).bind fun r => some r.2 else some m) = some m₁ ∧
      PMemoR m₁ pm ∧ LoopR pins dn m₁ a vis fe pend ds := by
    by_cases hf : fresh = 0
    · rw [if_pos hf] at hpm
      exact ⟨m, by rw [if_neg (by simpa using hf)], hpm, hR⟩
    · rw [if_neg hf] at hpm
      rw [if_pos (by simpa using hf)] at hW ⊢
      cases n with
      | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
      | succ n =>
      cases hcl : callW p (n + 1) "promote_clear" [] m with
      | none => rw [hcl] at hW; cases hW
      | some x =>
      obtain ⟨rc, m₁⟩ := x
      obtain ⟨s1, hs1, -, hW1⟩ := callW_triple (promoteClear_spec p hp n ⟨m, Locals.init []⟩) hcl
      rw [hs1] at hW1
      obtain ⟨pm0, hP0⟩ := hR.pmemo
      obtain ⟨hP1, hf1⟩ := clear_rel hP0 hW1
      rw [hpm]
      have hD₁ : ArenaD m₁ a :=
        ⟨ArenaR.frame_ext _ _ (by simp) (by simp) m _ hf1 a hR.check.arena.1,
          DerR.frameM _ _ m _ hf1 (by simp) a hR.check.arena.2⟩
      have hT₁ : erecTop m₁ = erecTop m := by simp only [erecTop]; rw [hf1.2.1 129 (by simp)]
      have hEE₁ : m₁.arr64 EREC = m.arr64 EREC := hf1.1 EREC (by simp) (by decide)
      obtain ⟨hiw1, hiw2, hiw3, hiw4, hiw5⟩ := hR.iw
      refine ⟨m₁, rfl, hP1, ?_⟩
      exact LoopR.of_frame hR hD₁ hf1 (fun b hb => by simp at hb)
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        rfl (ErecGrow.of_eq hEE₁ hT₁) (by rw [hEE₁, hT₁]; exact hiw2) hP1
        (hR.check.env.frame (fun b hb => by simp at hb)
          (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hf1)
        (hR.check.mode.frame hf1 (by simp) (by simp))
  rw [hm₁, Option.bind_some] at hW
  -- the constants, then the tables, at one memo
  obtain ⟨⟨r₁, m₂⟩, hc1, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a₂, pm₂, fe₂, hrun₂, hR₂, hP₂⟩ := pconsts_rel p hp dn n m₁ a pm k vis fe pend ds r₁ m₂ hP₁ hR₁ hk hc1
  cases hc2 : callW p n "promote_new_tables" [kt] m₂ with
  | none => rw [hc2] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₃⟩ := x
  rw [hc2, memK_some] at hW
  have hm3 : m₃ = m' := Option.some.inj hW
  subst hm3
  obtain ⟨a₃, pm₃, fe₃, hrun₃, hR₃, -⟩ := ptablesNew_rel p hp dn n m₂ a₂ pm₂ kt vis fe₂ pend ds r₂ m₃ hP₂ hR₂ hc2
  refine ⟨a₃, pm₃, fe₃, ?_, hR₃⟩
  simp only [promoteNew]
  rw [run_bind_ok hrun₂]; exact hrun₃

end rel

end L.Arena
