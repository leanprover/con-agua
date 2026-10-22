import ConAgua.Arena.IndPos2SpecG
import ConAgua.Arena.IndInstallSpec3
import ConAgua.Arena.WhnfCoreProj

/-! # `IndPos2`'s leaves, continued (lane `indproofs2`, helper `pos`, fork E): `nestInstType`
(with `nest_occ_any`, `nest_inst_type_ty`), `nestGrowGroup`. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_occ_any`: `xs.anyM (nestOcc names lo hi ·)` -/

mutual
def noaW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, lo, hi, off, l =>
    if l = 0 then some ([0], m) else noaK k no nl lo hi off l (noConstWf k m no nl lo hi (rdW (m.arr64 IW) off))
def noaK (k : Nat) (no nl lo hi off l : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m1) => if b ≠ 0 then some ([1], m1) else noaW k m1 no nl lo hi (off + 1) (l - 1)
end

section arms
variable (k : Nat) (m m1 : Mem) (no nl lo hi off l b : Word)
theorem noaW_nil (h : l = 0) : noaW (k + 1) m no nl lo hi off l = some ([0], m) := by simp [noaW, h]
theorem noaW_cons (h : ¬ l = 0) : noaW (k + 1) m no nl lo hi off l =
    noaK k no nl lo hi off l (noConstWf k m no nl lo hi (rdW (m.arr64 IW) off)) := by simp [noaW, h]
theorem noaK_hit (h : b ≠ 0) : noaK k no nl lo hi off l (some (b, m1)) = some ([1], m1) := by rw [noaK, if_pos h]
theorem noaK_miss (h : ¬ b ≠ 0) : noaK k no nl lo hi off l (some (b, m1)) =
    noaW k m1 no nl lo hi (off + 1) (l - 1) := by rw [noaK, if_neg h]
end arms
attribute [ind_grind] noaW_nil noaW_cons noaK_hit noaK_miss

theorem nestOccAny_spec (p : Prog) (hl : NoLook p) (hp : p.lookup "nest_occ_any" = some nestOccAnyL)
    (k : Nat) : ∀ (s₀ : St) (no nl lo hi off ln : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_occ_any" [no, nl, lo, hi, off, ln]
    ⦃fun r s' => LocEq s' s₀ ∧ noaW k s₀.mem no nl lo hi off ln = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ no nl lo hi off ln
    rw [invoke_eq _ hp]; simp only [callFn, nestOccAnyL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ no nl lo hi off ln
    rw [invoke_eq _ hp]
    simp only [callFn, nestOccAnyL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nestOcc_spec' p hl k, ih] <;>
      finish (gen := 20) [Locals.init_cons_zero]

theorem noaW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis no nl lo hi : Word) (names : List NIdx)
    (hMno : ∀ (m2 : Mem) (a2 : AState), StageR dn vis fe m2 a2 → ∃ mp0, noMR m2 mp0) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (xs : List EIdx) (r : List Word),
    noaW k m no nl lo hi off l = some (r, m') → StageR dn vis fe m a →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat ≤ iwTop m →
    decHL m off.toNat l.toNat = some xs → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    ∃ b, (xs.anyM (fun x => ConRon.Arena.nestOcc names lo.toNat hi.toNat x)).run a = .ok (b, a) ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) := by
  induction k with
  | zero => intro m m' a off l xs r h; simp [noaW] at h
  | succ k ih =>
    intro m m' a off l xs r h hS hn hnb hxs hxb
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hl0 : l = 0
    · rw [noaW_nil (h := hl0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hl0
      have : xs = [] := by simpa [decHL, hslice?] using hxs.symm
      subst this
      exact ⟨false, rfl, hS, IWGrow.refl _, rfl⟩
    rw [noaW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hxs2 := hxs
    simp only [decHL] at hxs2
    rw [hl', hslice?_succ] at hxs2
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hxs2
    obtain ⟨x, hx, xs', hxs', rfl⟩ := hxs2
    obtain ⟨hxH, hxd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.expr) (by simpa [iwH, iwA] using hx)
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hxb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨mp0, hM0⟩ := hMno m a hS
    cases hno : noConstWf k m no nl lo hi (rdW (m.arr64 IW) off) with
    | none => rw [hno] at h; simp [noaK] at h
    | some pr =>
    obtain ⟨b1, m1⟩ := pr
    rw [hno] at h
    obtain ⟨c1, hrun1, hc1, -, hS1, hg1⟩ := noConstWf_ok k dn fe vis m m1 a no nl lo hi _ b1 names mp0 hno hS hxH
      hn (by omega) hM0
    rw [decE_eq, hxd] at hrun1
    rw [List.anyM_cons]
    by_cases hb : b1 ≠ 0
    · rw [noaK_hit (h := hb)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : c1 = true := by rw [← hc1]; simpa using hb
      subst this
      refine ⟨true, ?_, hS1, hg1, rfl⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, if_true]; rfl
    · rw [noaK_miss (h := hb)] at h
      have : c1 = false := by rw [← hc1]; simpa using hb
      subst this
      obtain ⟨b, hrun, hS', hg', hr⟩ := ih m1 m' a (off + 1) (l - 1) xs' r h hS1
        (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hn) (by have := hg1.1; omega)
        (by rw [hoff1, hl1, decHL_agree (RdS.of_grow hg1) (fun j hj => by have := hxb (j + 1) (by omega); omega)]
            simpa [decHL] using hxs')
        (fun j hj => by rw [hoff1, hl1] at *; have := hxb (j + 1) (by omega); have := hg1.1; omega)
      refine ⟨b, ?_, hS', hg1.trans hg', hr⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, if_false]
      exact hrun

end L.Ind
