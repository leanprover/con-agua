import ConAgua.Arena.IndRealMemoCr
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Census.Attr

/-!
# FieldDomsResolve: `ConRon.Arena.fieldDomsResolve`, `ConRon.Arena.idxArgsResolve`

The refinement theorems `fieldDomsResolve_refines`, `idxArgsResolve_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The relational lemmas -/

theorem fdrW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (v o l : Word) (xs : List EIdx) (r : List Word),
    fdrW n m v o l = some (r, m') → StageR dn v fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m → AbsOK m →
    ∃ b a', (fieldDomsResolve fe xs).run a = .ok (b, a') ∧ KeepPost dn v fe decW0B m m' a' r b ∧
      AbsOK m' := by
  induction n with
  | zero => intro m m' a v o l xs r h; simp [fdrW] at h
  | succ n ih =>
    intro m m' a v o l xs r h hS hd hb ht hA
    by_cases hl : l = 0
    · subst hl
      rw [fdrW_nil n m v o 0 rfl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : xs = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨true, a, rfl, ⟨hS, IWGrow.refl m, by simp [decW0B]⟩, hA⟩
    · obtain ⟨w, xs', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [fdrW_cons n m v o l hl, hw] at h
      obtain ⟨ra, m1, h1, h⟩ := kSome_inv h (by simp [fdrK1]) (fun _ _ => rfl)
      rw [fdrK1_some] at h
      obtain ⟨t, a1, hrun1, hS1, hg1, ht32, hteq⟩ := ftdF_ok dn v fe w hw32 m m1 a ra h1 hS
      have hA1 := ftdF_afr h1 hA
      obtain ⟨rb, m2, h2, h⟩ := kSome_inv h (by simp [fdrK2]) (fun _ _ => rfl)
      obtain ⟨c, a2, hrun2, ⟨hS2, hg2, hceq, hc1⟩, hA2⟩ :=
        crfF_ok dn v fe (ra.headD 0) ht32 m1 m2 a1 rb h2 ⟨hS1, hA1⟩
      have hrun12 : ∀ (k : Bool → AM Bool),
          (do let t ← fvarTypeD (decI w); let c ← constsResolveFFast fe t; k c).run a = (k c).run a2 := by
        intro k
        simp only [StateT.run_bind]
        rw [hrun1]
        simp only [bind, Except.bind]
        rw [← hteq, hrun2]
      by_cases hz : rb.headD 0 = 0
      · rw [fdrK2_no n m2 v o l rb hz] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hc : c = false := by rw [← hceq, hz]; rfl
        subst hc
        refine ⟨false, a2, ?_, ⟨hS2, hg1.trans hg2, by simp [decW0B]⟩, hA2⟩
        have := hrun12 (fun c => if c then fieldDomsResolve fe xs' else pure false)
        simp only [fieldDomsResolve]
        rw [this]; rfl
      · rw [fdrK2_yes n m2 v o l rb hz] at h
        have hc : c = true := by rw [← hceq]; exact bne_iff_ne.mpr hz
        subst hc
        obtain ⟨r3, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
        rw [resK_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hg12 := hg1.trans hg2
        obtain ⟨b3, a3, hrun3, ⟨hS3, hg3, hd3, hd31⟩, hA3⟩ := ih m2 m3 a2 v (o + 1) (l - 1) xs' r3 h3 hS2
          (by rw [decHL_grow hg12 (by omega)]; exact hd') (by omega) (by have := hg12.1; omega) hA2
        refine ⟨b3, a3, ?_, ⟨hS3, hg12.trans hg3, by simpa [decW0B] using And.intro hd3 hd31⟩, hA3⟩
        have := hrun12 (fun c => if c then fieldDomsResolve fe xs' else pure false)
        simp only [fieldDomsResolve]
        rw [this]; exact hrun3

theorem iarW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (v o l : Word) (xs : List EIdx) (r : List Word),
    iarW n m v o l = some (r, m') → StageR dn v fe m a → decHL m o.toNat l.toNat = some xs →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m → AbsOK m →
    ∃ b a', (idxArgsResolve fe xs).run a = .ok (b, a') ∧ KeepPost dn v fe decW0B m m' a' r b ∧
      AbsOK m' := by
  induction n with
  | zero => intro m m' a v o l xs r h; simp [iarW] at h
  | succ n ih =>
    intro m m' a v o l xs r h hS hd hb ht hA
    by_cases hl : l = 0
    · subst hl
      rw [iarW_nil n m v o 0 rfl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : xs = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨true, a, rfl, ⟨hS, IWGrow.refl m, by simp [decW0B]⟩, hA⟩
    · obtain ⟨w, xs', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [iarW_cons n m v o l hl, hw] at h
      obtain ⟨rb, m2, h2, h⟩ := kSome_inv h (by simp [iarK]) (fun _ _ => rfl)
      obtain ⟨c, a2, hrun2, ⟨hS2, hg2, hceq, hc1⟩, hA2⟩ :=
        crfF_ok dn v fe w hw32 m m2 a rb h2 ⟨hS, hA⟩
      have hrun12 : ∀ (k : Bool → AM Bool),
          (do let c ← constsResolveFFast fe (decI w); k c).run a = (k c).run a2 := by
        intro k
        simp only [StateT.run_bind]
        rw [hrun2]
        rfl
      by_cases hz : rb.headD 0 = 0
      · rw [iarK_no n m2 v o l rb hz] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hc : c = false := by rw [← hceq, hz]; rfl
        subst hc
        refine ⟨false, a2, ?_, ⟨hS2, hg2, by simp [decW0B]⟩, hA2⟩
        have := hrun12 (fun c => if c then idxArgsResolve fe xs' else pure false)
        simp only [idxArgsResolve]
        rw [this]; rfl
      · rw [iarK_yes n m2 v o l rb hz] at h
        have hc : c = true := by rw [← hceq]; exact bne_iff_ne.mpr hz
        subst hc
        obtain ⟨r3, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
        rw [resK'_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨b3, a3, hrun3, ⟨hS3, hg3, hd3, hd31⟩, hA3⟩ := ih m2 m3 a2 v (o + 1) (l - 1) xs' r3 h3 hS2
          (by rw [decHL_grow hg2 (by omega)]; exact hd') (by omega) (by have := hg2.1; omega) hA2
        refine ⟨b3, a3, ?_, ⟨hS3, hg2.trans hg3, by simpa [decW0B] using And.intro hd3 hd31⟩, hA3⟩
        have := hrun12 (fun c => if c then idxArgsResolve fe xs' else pure false)
        simp only [idxArgsResolve]
        rw [this]; exact hrun3

/-! ## The census theorems -/

/-- **`field_doms_resolve` refines `fieldDomsResolve`** (through `fvar_type_d`, `consts_resolve_ffast`,
with the walk memos `AbsOK`), at the view `vis0` of the pre-block environment `fe₀`. -/
@[refines ConRon.Arena.fieldDomsResolve]
theorem fieldDomsResolve_refines (p : Prog)
    (hp : p.lookup "field_doms_resolve" = some fieldDomsResolveL) (hftd : FtdF p) (hcr : CrfF p) (n : Nat)
    (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe₀ : IFEnv) (vis0 o l : Word) (xs : List EIdx)
    (hS : StageR dn vis0 fe₀ s₀.mem a₀) (hd : decHL s₀.mem o.toNat l.toNat = some xs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "field_doms_resolve" [vis0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (fieldDomsResolve fe₀ xs) a₀ ∧
      KeepPost dn vis0 fe₀ decW0B s₀.mem s'.mem (AM.st (fieldDomsResolve fe₀ xs) a₀) r
        (AM.res (fieldDomsResolve fe₀ xs) a₀) ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (fdrW_spec p hp hftd hcr n s₀ vis0 o l) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hpost, hA'⟩ := fdrW_ok dn fe₀ n _ _ a₀ vis0 o l xs r hm hS hd hb ht hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hpost, hA'⟩

/-- **`idx_args_resolve` refines `idxArgsResolve`** (through `consts_resolve_ffast`, with the walk
memos `AbsOK`),
at the view `vis0` of the pre-block environment `fe₀`. -/
@[refines ConRon.Arena.idxArgsResolve]
theorem idxArgsResolve_refines (p : Prog)
    (hp : p.lookup "idx_args_resolve" = some idxArgsResolveL) (hcr : CrfF p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe₀ : IFEnv) (vis0 o l : Word) (xs : List EIdx)
    (hS : StageR dn vis0 fe₀ s₀.mem a₀) (hd : decHL s₀.mem o.toNat l.toNat = some xs)
    (hb : o.toNat + l.toNat < 2 ^ 64) (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "idx_args_resolve" [vis0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (idxArgsResolve fe₀ xs) a₀ ∧
      KeepPost dn vis0 fe₀ decW0B s₀.mem s'.mem (AM.st (idxArgsResolve fe₀ xs) a₀) r
        (AM.res (idxArgsResolve fe₀ xs) a₀) ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (iarW_spec p hp hcr n s₀ vis0 o l) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hpost, hA'⟩ := iarW_ok dn fe₀ n _ _ a₀ vis0 o l xs r hm hS hd hb ht hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hpost, hA'⟩

/-! ## `class_rule_ok_domains` (moved from `RecGenSpec/CfhW.lean`) -/

end L.Ind

end
