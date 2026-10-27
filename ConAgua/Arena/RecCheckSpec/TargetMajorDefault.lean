import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
import ConAgua.Arena.IndSumSpec.StructProjArgP

/-!
# TargetMajorDefault: `ConRon.Arena.targetMajorDefault`

The refinement theorems `targetMajorDefault_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A decoded constructor pair's name word. -/
theorem decCN_nameW {m : Mem} {p : Nat} {x : IConstantVal × Nat} (h : decCN m p = some x)
    (hp : p < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (UInt64.ofNat p)) = w ∧ w.toNat < 2 ^ 32 ∧
      x.1.name = decI w := by
  simp only [decCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, nF, -, rfl⟩ := h
  have hr := iwN_rdW hq hp
  obtain ⟨w, hw, hw32, hn⟩ := decCV_name hcv
  refine ⟨w, ?_, hw32, hn⟩
  rw [hr.1]
  have : (UInt64.ofNat q).toNat = q := by simp; have := hr.2; omega
  simp only [rdW, this]
  have hw' : (m.arr64 EREC)[q]? = some w := hw
  rw [hw']; rfl

theorem chnW_ok (n : Nat) : ∀ (m : Mem) (co cl name r : Word) (ctors : List (IConstantVal × Nat)),
    chnW n m co cl name = some r → decPL m (decCN m) co.toNat cl.toNat = some ctors →
    name.toNat < 2 ^ 32 → co.toNat + cl.toNat < 2 ^ 64 →
    (r != 0) = ctors.any (fun c => c.1.name == (decI name : NIdx)) ∧ r.toNat ≤ 1 := by
  induction n with
  | zero => intro m co cl name r ctors h; simp [chnW] at h
  | succ n ih =>
    intro m co cl name r ctors h hd hn hb
    by_cases hl : cl = 0
    · rw [chnW_nil n m co cl name hl] at h
      simp only [Option.some.injEq] at h
      subst h
      have hz : cl.toNat = 0 := by rw [hl]; rfl
      rw [hz] at hd
      simp [decPL] at hd
      subst hd
      simp
    · obtain ⟨hsum, hco1⟩ := toNat_succ_of_lt hb hl
      obtain ⟨l1, hl1⟩ : ∃ l1, cl.toNat = l1 + 1 := ⟨cl.toNat - 1, by
        have : cl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
        omega⟩
      rw [hl1] at hd
      obtain ⟨pp, x, ys, rfl, hp, hx, hys⟩ := decPL_cons hd
      have hrd := iwN_rdW hp (by omega)
      rw [UInt64.ofNat_toNat] at hrd
      obtain ⟨w, hw, hw32, hname⟩ := decCN_nameW hx hrd.2
      have hiff : (w = name) ↔ (x.1.name == (decI name : NIdx)) = true := by
        rw [hname, beq_iff_eq, decI_eq_iff w hw32, decI_word_self name hn]
      rw [← hrd.1] at hw
      by_cases he : w = name
      · rw [chnW_hit n m co cl name hl (by rw [hw]; exact he)] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [List.any_cons, hiff.mp he]
      · rw [chnW_next n m co cl name hl (by rw [hw]; exact he)] at h
        have hys' : decPL m (decCN m) (co + 1).toNat (cl - 1).toNat = some ys := by
          have hl1' : (cl - 1).toNat = l1 := by omega
          rw [hco1, hl1']; exact hys
        have := ih m (co + 1) (cl - 1) name r ys h hys' hn (by omega)
        have hne : ¬ (x.1.name == (decI name : NIdx)) = true := fun e => he (hiff.mpr e)
        simpa [List.any_cons, hne] using this

/-- **`target_major_default` refines `targetMajorDefault`** (through the stub `intern_nanon`, `pin_word`
and `mk_target_major`). -/
@[refines ConRon.Arena.targetMajorDefault]
theorem targetMajorDefault_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hpw : p.lookup "pin_word" = some pinWordL) (hm : p.lookup "mk_target_major" = some mkTargetMajor)
    (hp : p.lookup "target_major_default" = some targetMajorDefault) (hna : NaF p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_major_default" []
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok ConRon.Arena.targetMajorDefault a₀ ∧
      StageR dn vis fe s'.mem (AM.st ConRon.Arena.targetMajorDefault a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decTM s'.mem (r.headD 0).toNat = some (AM.res ConRon.Arena.targetMajorDefault a₀); ⊤⦄ := by
  refine triple_post (targetMajorDefault_spec p ha hpw hm hp hna n s₀) ?_
  rintro r s' ⟨hl, hw⟩
  obtain ⟨tm, a', hrun, hS', hg, hd⟩ := tmdW_ok dn vis fe _ _ a₀ r hw hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd⟩

end L.Ind

end
