import ConAgua.Arena.PromoteCIRef30

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

theorem promoteNew_rel {pins : List INatOpPinSet} (dn : NIdx → Option ConLeche.Name) (n : Nat) (m : Mem) (a : AState)
    (pm : PMemo) (k vis fresh : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (ds : Array IDeclaration) (r : List Word) (m' : Mem)
    (hpm : if fresh = 0 then PMemoR m pm else pm = PMemo.empty)
    (hR : LoopR pins dn m a vis fe pend ds) (hk : k.toNat ≤ vis.toNat)
    (hc : callW p n "promote_new" [k, vis, fresh] m = some (r, m')) :
    ∃ a' pm' fe', (promoteNew pm coreWalkFuel k.toNat fe).run a = .ok ((pm', fe'), a') ∧
      LoopR pins dn m' a' vis fe' pend ds := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteNew_specW p hp n ⟨m, Locals.init []⟩ k vis fresh) hc
  simp only at hW
  rw [hs', newW_eq] at hW
  obtain ⟨⟨consts⟩, idx, vb⟩ := fe
  by_cases hk0 : k = 0
  · rw [if_pos hk0] at hW
    have hm : m = m' := Option.some.inj hW
    subst hm
    have hk0' : k.toNat = 0 := by rw [hk0]; rfl
    refine ⟨a, pm, ⟨⟨consts⟩, idx, vb⟩, ?_, hR⟩
    simp [promoteNew, hk0']; rfl
  rw [if_neg hk0] at hW
  have hk0' : (k.toNat == 0) = false := by
    have : k.toNat ≠ 0 := fun h => hk0 (UInt64.toNat_inj.mp (by simpa using h))
    simpa using this
  by_cases hf : fresh = 0
  · rw [if_neg (by simpa using hf)] at hW
    simp only [Option.bind_some] at hW
    rw [if_pos hf] at hpm
    obtain ⟨a', pm', L', hrun, hLoop⟩ := pnew_main p hp dn n m a pm k vis consts idx vb pend ds m'
      hpm hR hk hW
    refine ⟨a', pm', _, ?_, hLoop⟩
    simp only [promoteNew, hk0', Bool.false_eq_true, ↓reduceIte]
    rw [run_bind_ok hrun]; rfl
  · rw [if_pos (by simpa using hf)] at hW
    rw [if_neg hf] at hpm
    cases n with
    | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
    | succ n =>
    cases hcl : callW p (n + 1) "promote_clear" [] m with
    | none => rw [hcl] at hW; cases hW
    | some x =>
    obtain ⟨rc, m₁⟩ := x
    rw [hcl] at hW
    simp only [Option.bind_some] at hW
    obtain ⟨s1, hs1, -, hW1⟩ := callW_triple (promoteClear_spec p hp n ⟨m, Locals.init []⟩) hcl
    rw [hs1] at hW1
    obtain ⟨pm0, hP0⟩ := hR.pmemo
    obtain ⟨hP1, hf1⟩ := clear_rel hP0 hW1
    rw [hpm] at *
    have hD₁ : ArenaD m₁ a :=
      ⟨ArenaR.frame_ext _ _ (by simp) (by simp) m _ hf1 a hR.check.arena.1,
        DerR.frameM _ _ m _ hf1 (by simp) a hR.check.arena.2⟩
    have hT₁ : erecTop m₁ = erecTop m := by simp only [erecTop]; rw [hf1.2.1 129 (by simp)]
    have hEE₁ : m₁.arr64 EREC = m.arr64 EREC := hf1.1 EREC (by simp) (by decide)
    obtain ⟨hiw1, hiw2, hiw3, hiw4, hiw5⟩ := hR.iw
    have hR₁ : LoopR pins dn m₁ a vis ⟨⟨consts⟩, idx, vb⟩ pend ds :=
      LoopR.of_frame hR hD₁ hf1 (fun b hb => by simp at hb)
        (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        rfl (ErecGrow.of_eq hEE₁ hT₁) (by rw [hEE₁, hT₁]; exact hiw2) hP1
        (hR.check.env.frame (fun b hb => by simp at hb)
          (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) hf1)
    obtain ⟨a', pm', L', hrun, hLoop⟩ := pnew_main p hp dn (n + 1) m₁ a PMemo.empty k vis consts idx vb pend ds m'
      hP1 hR₁ hk hW
    refine ⟨a', pm', ⟨⟨L' ++ consts.drop k.toNat⟩,
      indexPromoted (eraseInstalled idx (consts.take k.toNat)) vb L', vb⟩, ?_, hLoop⟩
    simp only [promoteNew, hk0', Bool.false_eq_true, ↓reduceIte]
    rw [run_bind_ok hrun]; rfl

end rel

end L.Arena
