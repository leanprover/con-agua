import ConAgua.Arena.DeclDivModSpec.Cons
import ConAgua.Arena.IndInstallSpec.DomsW

/-!
# InstW

`instW_ok`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem instW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (ao al e : Word) (args : List EIdx) (r : List Word),
    instW n m ao al e = some (r, m') → StageR dn vis fe m a → H e →
    decHL m ao.toNat al.toNat = some args → ao.toNat + al.toNat < 2 ^ 64 →
    ao.toNat + al.toNat ≤ iwTop m →
    ∃ x a', (ConRon.Arena.instPisWith args (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x := by
  induction n with
  | zero => intro dn fe vis m m' a ao al e args r h; simp [instW] at h
  | succ n ih =>
    intro dn fe vis m m' a ao al e args r h hS he hdec hb hit
    by_cases hal : al = 0
    · rw [instW_nil n m ao al e hal] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : args = [] := by
        have h0 : al.toNat = 0 := by rw [hal]; rfl
        rw [h0] at hdec; simpa [decHL, hslice?] using hdec.symm
      subst this
      exact ⟨some (decI e), a, rfl, hS, IWGrow.refl _, rfl, he, rfl⟩
    · have hl1 : al.toNat = (al.toNat - 1) + 1 := by have := toNat_ne_zero' hal; omega
      rw [hl1, decHL, hslice?_succ] at hdec
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdec
      obtain ⟨xa, hxa, rest, hrest, rfl⟩ := hdec
      by_cases hpi : e >>> 28 ≠ 6
      · rw [instW_nopi n m ao al e hal hpi] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
        have ht : ¬ ((decI e : EIdx).tag == ETag.forallE) = true := by
          rw [tag_forall_iff e he]; simpa using hpi
        simp only [ConRon.Arena.instPisWith, ht]; rfl
      · rw [instW_pi n m ao al e hal hpi] at h
        have he6 : e >>> 28 = 6 := by simpa using hpi
        cases hvl : eViewW m e with
        | nil => rw [hvl] at h; simp [instK1] at h
        | cons g vt =>
          have hne : eViewW m e ≠ [] := by rw [hvl]; simp
          rw [hvl] at h
          rw [instK1_ok n m ao al _ (by simp)] at h
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.1.arena.1 e hne
          rw [hvl] at hvr
          have ht : (decE e).tag = ETag.forallE := by
            have h1 : ((decI e : EIdx).tag == ETag.forallE) = true := by
              rw [tag_forall_iff e he, he6]; decide
            exact beq_iff_eq.mp h1
          obtain ⟨ty, bd, rfl⟩ := EStore.view_forall a.store (decE e) ht v hv
          simp only [ViewR, getD1_eq] at hvr
          obtain ⟨-, -, -, hy1, hy2⟩ := hvr
          have hy2' : (vt.tail.headD 0).toNat < 2 ^ 32 := by simpa using hy1
          have hy3 : decE (vt.tail.headD 0) = bd := by simpa using hy2
          have hbind : a.store.viewBind (decE e) = some (ty, bd) :=
            EStore.viewBind_of_view _ _ ht ty bd hv
          have hlt0 : ao.toNat < 2 ^ 64 := ao.toNat_lt
          obtain ⟨wa, hwa_eq, hwa_lt, hwa_dec⟩ := iwH_rdW hxa hlt0
          rw [UInt64.ofNat_toNat] at hwa_eq
          rw [hwa_eq] at h
          simp only [List.tail_cons] at h
          rcases hst : i1F m [CWF, vt.tail.headD 0, wa, 0] with _ | ⟨rb, m1⟩ <;> rw [hst] at h; · simp [instK2] at h
          rw [instK2_some] at h
          obtain ⟨x1, a1, hrun1, hS1, hg1, hlt1, hdec1⟩ :=
            i1F_ok dn vis fe (vt.tail.headD 0) wa 0 hy2' m m1 a rb hst hS
          rcases hw : instW n m1 (ao + 1) (al - 1) (rb.headD 0) with _ | ⟨r3, m3⟩ <;> rw [hw] at h; · simp [instK3] at h
          rw [instK3_some] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hao1 : (ao + 1).toNat = ao.toNat + 1 := toNat_add_one' (by omega)
          have hal1 : (al - 1).toNat = al.toNat - 1 := toNat_sub_one' hal
          have hdec' : decHL m1 (ao + 1).toNat (al - 1).toNat = some rest := by
            rw [hao1, hal1, decHL_grow hg1 (by omega)]; exact hrest
          obtain ⟨x3, a3, hrun3, hS3, hg3, hout3⟩ :=
            ih dn fe vis m1 m3 a1 (ao + 1) (al - 1) (rb.headD 0) rest r3 hw hS1 hlt1 hdec'
              (by rw [hao1, hal1]; omega) (by rw [hao1, hal1]; have := hg1.1; omega)
          refine ⟨x3, a3, ?_, hS3, hg1.trans hg3, ?_⟩
          · have htag : ((decI e : EIdx).tag == ETag.forallE) = true := by
              rw [tag_forall_iff e he, he6]; decide
            simp only [ConRon.Arena.instPisWith, htag, ite_true, StateT.run_bind]
            rw [show (decI e : EIdx) = decE e from rfl, viewBind_run, except_ok_bind, hbind]
            simp only [StateT.run_bind]
            rw [show (decI (vt.tail.headD 0) : EIdx) = bd from hy3, hwa_dec, CWF_eq,
              show (0 : Word).toNat = 0 from rfl] at hrun1
            rw [hrun1]
            simp only [except_ok_bind]
            rw [← hdec1]
            exact hrun3
          · cases x3 with
            | none =>
              simp only [decOE] at hout3 ⊢
              exact hout3
            | some e3 =>
              simp only [decOE, decW0E] at hout3 ⊢
              obtain ⟨h1, h2, h3⟩ := hout3
              exact ⟨h1, by simpa using h2, by simpa using h3⟩

end L.Ind

end
