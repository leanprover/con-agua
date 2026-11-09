module

public import ConAgua.Arena.ProjGuardRowsOpf
public import ConAgua.Arena.Verdict
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IndRealFvtD
import ConAgua.Arena.CallF
import ConAgua.Arena.WhnfCoreRefine
import all ConAgua.Arena.Infer

@[expose] public section

/-!
# `proj_guard_rows` refines `projGuardRows` under `CoreS` (`pgr_ok`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind (IW)

/-- **`proj_guard_rows_at`'s word model** (`struct_used_later`, `fvar_type_d` lifted). -/
l_model pgraW_spec (p : Prog) (hf : p.lookup "proj_guard_rows_at" = some projGuardRowsAtL)
  fns [hf ↦ pgraW]
  specs [callW_spec p n "struct_used_later", callW_spec p n "fvar_type_d"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

/-- **`proj_guard_rows`' word model** (its callees lifted). -/
l_model pgrW_spec (p : Prog) (hf : p.lookup "proj_guard_rows" = some projGuardRowsL)
  fns [hf ↦ pgrW list]
  specs [callW_spec p n "env_find", callW_spec p n "const_ty_at",
    callW_spec p n "open_pis_at_fvars_f", callW_spec p n "proj_guard_rows_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]


end L.Arena

namespace L.Ind

open L.Arena

/-- **The guard rows on the stack**: row `i` at `ro + 2 i` (its depth) and `ro + 2 i + 1` (its
term). (`RowsAt` of `ProjGuardRef.lean`.) -/
def GRows (m : Mem) (ro : Word) (rows : Array (Nat × EIdx)) : Prop :=
  ∀ (i : Word) (h : i.toNat < rows.size), (spW m (ro + 2 * i)).toNat = (rows[i.toNat]'h).1 ∧
    HW (spW m (ro + 2 * i + 1)) ∧ decE (spW m (ro + 2 * i + 1)) = (rows[i.toNat]'h).2

/-! ## The twin's steps -/

theorem pgraT_done (cty : EIdx) (nP idx : Nat) (fvs : List EIdx) (j : Nat) (out : Array (Nat × EIdx))
    (a : AState) (h : idx < j) : (projGuardRowsAt cty nP idx fvs j out).run a = .ok (out, a) := by
  rw [projGuardRowsAt]; simp [h]; rfl

theorem pgraT_step (cty : EIdx) (nP idx : Nat) (fvs : List EIdx) (j : Nat) (out : Array (Nat × EIdx))
    (a a1 : AState) (u : Bool) (h : ¬ idx < j)
    (hu : ((if j == idx then pure true else structUsedLater cty nP j : AM Bool)).run a = .ok (u, a1)) :
    (projGuardRowsAt cty nP idx fvs j out).run a =
      (if !u then projGuardRowsAt cty nP idx fvs (j + 1) out
       else match fvs[nP + j]? with
         | some x => do
           let ty ← fvarTypeD x
           projGuardRowsAt cty nP idx fvs (j + 1) (out.push (nP + j, ty))
         | none => projGuardRowsAt cty nP idx fvs (j + 1) out).run a1 := by
  rw [projGuardRowsAt]
  by_cases hji : j = idx
  · subst hji
    simp only [beq_self_eq_true, ↓reduceIte] at hu
    cases hu
    simp [h]; rfl
  · have hne : (j == idx) = false := by simpa using hji
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hu
    simp only [gt_iff_lt, h, ↓reduceIte, hne, Bool.false_eq_true, StateT.run_bind, hu]
    rfl

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}

/-- **`proj_guard_rows_at` refines `projGuardRowsAt` under `CoreS`**: the rows of fields `j, …,
idx` read off the opened telescope's pool slice `(fo, fvs)`, appended to the rows `out` at `ro`
on the stack (the top just past them). -/
theorem pgra_ok (p : Prog) (hf : p.lookup "proj_guard_rows_at" = some projGuardRowsAtL)
    (hus : UsF p) (hfd : p.lookup "fvar_type_d" = some fvarTypeDL)
    (hev : p.lookup "e_view" = some eView) (cty nP idx fo fn ro : Word) (fvs : List EIdx)
    (hc : H cty) (hB : nP.toNat + idx.toNat + 1 < 2 ^ 64) (hfn : fn.toNat = fvs.length) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (M : ModeMaps) (j rn w : Word) (out : Array (Nat × EIdx)),
      pgraW p n m cty nP idx fo fn j ro rn = some (w, m') →
      CoreS dn m a vis fe M eb → IWOK m → (∃ mp, hbMR m mp) → IWSl m fo fvs →
      j.toNat ≤ idx.toNat + 1 → GRows m ro out → rn.toNat = out.size →
      (spTop m).toNat = ro.toNat + 2 * rn.toNat → ro.toNat + 2 * rn.toNat ≤ (m.arr64 SPN).size →
      ∃ y a' M', (projGuardRowsAt (decI cty) nP.toNat idx.toNat fvs j.toNat out).run a = .ok (y, a') ∧
        CoreS dn m' a' vis fe M' eb ∧ KeptAll M M' eb ∧ IWOK m' ∧ IWGrow m m' ∧
        (∃ mp, hbMR m' mp) ∧ GRows m' ro y ∧ w.toNat = y.size ∧
        (spTop m').toNat = ro.toNat + 2 * w.toNat ∧ ro.toNat + 2 * w.toNat ≤ (m'.arr64 SPN).size ∧
        StackGrew m m' ∧ a'.store = a.store := by
  intro n
  induction n with
  | zero => intro m m' a M j rn w out h; rw [pgraW.eq_1] at h; cases h
  | succ n ih =>
  intro m m' a M j rn w out h hS hI hM hsl hj hrows hrn htop hro
  have hspn := hS.spn
  by_cases hlt : idx < j
  · rw [pgraW.arm1 _ _ _ _ _ _ _ _ _ _ _ hlt] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨out, a, M, pgraT_done _ _ _ _ _ _ _ (UInt64.lt_iff_toNat_lt.mp hlt), hS, KeptAll.refl _ _,
      hI, IWGrow.refl _, hM, hrows, hrn, htop, hro, StackGrew.refl _, rfl⟩
  have hjle : j.toNat ≤ idx.toNat := by
    exact Nat.le_of_not_lt (fun h' => hlt (UInt64.lt_iff_toNat_lt.mpr h'))
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hnpj : (nP + j).toNat = nP.toNat + j.toNat := by rw [UInt64.toNat_add]; omega
  -- the `used` flag: a word `u` (the twin's `Bool`), the state after
  obtain ⟨u, uw, m1, a1, hJ, hrunU, huw, hS1, hI1, hg1, hM1, hSt1, hst1⟩ :
      ∃ (u : Bool) (uw : Word) (m1 : Mem) (a1 : AState),
        pgraW.j1 p n cty nP idx fo fn j ro rn uw m1 = some (w, m') ∧
        ((if j.toNat == idx.toNat then pure true else
            structUsedLater (decI cty) nP.toNat j.toNat : AM Bool)).run a = .ok (u, a1) ∧
        (uw ≠ 0 ↔ u = true) ∧ CoreS dn m1 a1 vis fe M eb ∧ IWOK m1 ∧ IWGrow m m1 ∧
        (∃ mp, hbMR m1 mp) ∧ StackKept m m1 ∧ a1.store = a.store := by
    by_cases hji : j = idx
    · rw [pgraW.arm2 _ _ _ _ _ _ _ _ _ _ _ hlt hji] at h
      refine ⟨true, 1, m, a, h, by simp [hji]; rfl, by simp, hS, hI, IWGrow.refl _, hM,
        StackKept.refl _, rfl⟩
    · rw [pgraW.arm3 _ _ _ _ _ _ _ _ _ _ _ hlt hji] at h
      rcases hcu : callW p n "struct_used_later" [cty, nP, j] m with _ | ⟨r1, m1⟩
      · rw [hcu, pgraW.k_struct_used_later.none] at h; cases h
      rw [hcu, pgraW.k_struct_used_later.arm1] at h
      obtain ⟨s'', hm, -, hu⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (structUsedLater_specV hus n _ [cty, nP, j]) (callW_mono hcu (Nat.le_add_right n 2))
      rw [hm] at hu
      obtain ⟨b, a1, hrun, hb, hM1, hS1, hSt1, hI1, hg1, hst1⟩ :=
        ustW_okC (cty := cty) (nP := nP) (j := j) n (by have := hB; have := hjle; omega) hc hS hI hM hu
      have hne : (j.toNat == idx.toNat) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact hji (UInt64.toNat_inj.mp e)
      refine ⟨b, r1.headD 0, m1, a1, h, by simp only [hne, Bool.false_eq_true, ↓reduceIte]; exact hrun,
        by rw [hb]; cases b <;> simp, hS1, hI1, hg1, hM1, hSt1, hst1⟩
  have hsl1 := hsl.grow hg1
  have hrows1 : GRows m1 ro out := fun i hi => by
    have hb := hrows i hi
    have e1 : (ro + 2 * i).toNat = ro.toNat + 2 * i.toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    have e2 : (ro + 2 * i + 1).toNat = ro.toNat + 2 * i.toNat + 1 := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    rw [hSt1.below _ (UInt64.lt_iff_toNat_lt.mpr (by omega)),
      hSt1.below _ (UInt64.lt_iff_toNat_lt.mpr (by omega))]
    exact hb
  have htop1 : (spTop m1).toNat = ro.toNat + 2 * rn.toNat := by rw [hSt1.top]; exact htop
  have hro1 : ro.toNat + 2 * rn.toNat ≤ (m1.arr64 SPN).size := by rw [hSt1.size]; exact hro
  have hstep := pgraT_step (decI cty) nP.toNat idx.toNat fvs j.toNat out a a1 u
    (by omega) hrunU
  -- the recursion without a new row
  have hskip : ∀ (m2 : Mem), pgraW p n m1 cty nP idx fo fn (j + 1) ro rn = some (w, m2) → m2 = m' →
      ∀ (T : AM (Array (Nat × EIdx))), T.run a1 =
        (projGuardRowsAt (decI cty) nP.toNat idx.toNat fvs (j.toNat + 1) out).run a1 →
      (projGuardRowsAt (decI cty) nP.toNat idx.toNat fvs j.toNat out).run a = T.run a1 →
      ∃ y a' M', (projGuardRowsAt (decI cty) nP.toNat idx.toNat fvs j.toNat out).run a = .ok (y, a') ∧
        CoreS dn m' a' vis fe M' eb ∧ KeptAll M M' eb ∧ IWOK m' ∧ IWGrow m m' ∧
        (∃ mp, hbMR m' mp) ∧ GRows m' ro y ∧ w.toNat = y.size ∧
        (spTop m').toNat = ro.toNat + 2 * w.toNat ∧ ro.toNat + 2 * w.toNat ≤ (m'.arr64 SPN).size ∧
        StackGrew m m' ∧ a'.store = a.store := by
    intro m2 h2 hm2 T hT hrT
    subst hm2
    obtain ⟨y, a', M', hrun', hS', hK', hI', hg', hM', hrows', hw', htop', hro', hSt', hst'⟩ :=
      ih m1 m2 a1 M (j + 1) rn w out h2 hS1 hI1 hM1 hsl1 (by omega) hrows1 hrn htop1 hro1
    rw [hj1] at hrun'
    exact ⟨y, a', M', by rw [hrT, hT, hrun'], hS', hK', hI', hg1.trans hg', hM', hrows', hw', htop', hro',
      hSt1.toGrew.trans hSt', hst'.trans hst1⟩
  by_cases hfv : uw ≠ 0 ∧ nP + j < fn
  · rw [pgraW.j1.arm1 _ _ _ _ _ _ _ _ _ _ _ _ hfv] at hJ
    have hu : u = true := huw.mp hfv.1
    have hlen : nP.toNat + j.toNat < fvs.length := by
      have := UInt64.lt_iff_toNat_lt.mp hfv.2; omega
    obtain ⟨w0, hw0, hH0, hd0⟩ := hsl1.2 _ hlen
    have hrd : rdW (m1.arr64 IW) (fo + nP + j) = w0 := by
      have hfo : (fo + nP + j).toNat = fo.toNat + (nP.toNat + j.toNat) := by
        have := hsl1.1; have := hI1.iw; have := hI1.iwSize
        rw [UInt64.toNat_add, UInt64.toNat_add]; omega
      simp [rdW, hfo, hw0]
    rw [hrd] at hJ
    rcases hcf : callW p n "fvar_type_d" [w0] m1 with _ | ⟨r2, m2⟩
    · rw [hcf, pgraW.k_fvar_type_d.none] at hJ; cases hJ
    rw [hcf] at hJ
    obtain ⟨s'', hm, -, hft⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (ftdAd_spec p hfd hev n _ w0) hcf
    rw [hm] at hft
    obtain ⟨hm21, hrunF, hlt2⟩ := ftdW_ok m1 m2 a1 hS1.arena.base w0 hH0 r2 hft
    rw [hm21] at hJ
    by_cases hab : Mem.len64 m1 (SPN : TieredArray) ≤ ro + 2 * rn + 1
    · rw [pgraW.k_fvar_type_d.abort1 _ _ _ _ _ _ _ _ _ _ _ _ hab] at hJ; cases hJ
    rw [pgraW.k_fvar_type_d.arm1 _ _ _ _ _ _ _ _ _ _ _ _ hab] at hJ
    have hsz1 := hS1.spn
    have hro2 : (ro + 2 * rn).toNat = ro.toNat + 2 * rn.toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    have hro3 : (ro + 2 * rn + 1).toNat = ro.toNat + 2 * rn.toNat + 1 := by
      rw [UInt64.toNat_add, hro2]; simp; omega
    have hroom : ro.toNat + 2 * rn.toNat + 1 < (m1.arr64 SPN).size := by
      have h1 := hab
      simp only [Mem.len64, UInt64.le_iff_toNat_le, hro3] at h1
      have : (UInt64.ofNat (m1.arr64 SPN).size).toNat = (m1.arr64 SPN).size := by
        simp; omega
      omega
    generalize hm3 : ((m1.set64 SPN (ro + 2 * rn) (nP + j)).set64 SPN (ro + 2 * rn + 1)
      (r2.headD 0)).set64 CTL 136 (ro + 2 * rn + 2) = m3 at hJ
    have hf3 : MemFrame [SPN] [136] m1 m3 := by
      rw [← hm3]
      exact (((MemFrame.set64 m1 SPN (by decide) _ _).trans (MemFrame.set64 _ SPN (by decide) _ _)).mono
        (by simp) (by simp)).trans ((MemFrame.setCtl _ 136 _).mono (by simp) (by simp))
    have hS3 := hS1.frame_stk hf3 (by simp) (by simp)
    obtain ⟨hI3, hg3⟩ := iwKeep hf3 (by decide) (by decide) hI1
    have hM3 := hbMR_keep hf3 (by decide) (by decide) hM1
    have hctl := hS1.ctl136
    have hspn3 : ∀ x : Word, spW m3 x = if x = ro + 2 * rn + 1 then r2.headD 0
        else if x = ro + 2 * rn then nP + j else spW m1 x := by
      intro x; rw [← hm3]; simp only [spW]
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), rdW_set64E, rdW_set64E]
      have e1 : (ro + 2 * rn).toNat < (m1.arr64 SPN).size := by omega
      have e2 : (ro + 2 * rn + 1).toNat < ((m1.set64 SPN (ro + 2 * rn) (nP + j)).arr64 SPN).size := by
        rw [Mem.size_arr64_set64]; omega
      by_cases ha : x = ro + 2 * rn + 1
      · subst ha; rw [if_pos ⟨rfl, rfl, e2⟩, if_pos rfl]
      · by_cases hb : x = ro + 2 * rn
        · subst hb
          rw [if_neg (fun h => ha h.2.1.symm), if_pos ⟨rfl, rfl, e1⟩, if_neg ha, if_pos rfl]
        · rw [if_neg (fun h => ha h.2.1.symm), if_neg (fun h => hb h.2.1.symm), if_neg ha, if_neg hb]
    have htop3 : spTop m3 = ro + 2 * rn + 2 := by
      rw [← hm3]; simp only [spTop]
      rw [rdW_set64E, ite_eq_left ⟨rfl, rfl, by
        rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; simp; omega⟩]
    have hrn1 : (rn + 1).toNat = rn.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hsz3 : (m3.arr64 SPN).size = (m1.arr64 SPN).size := hf3.size SPN
    let out' := out.push (nP.toNat + j.toNat, decI (r2.headD 0))
    have hrows3 : GRows m3 ro out' := by
      intro i hi
      simp only [out', Array.size_push] at hi
      have e1 : (ro + 2 * i).toNat = ro.toNat + 2 * i.toNat := by
        simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
      have e2 : (ro + 2 * i + 1).toNat = ro.toNat + 2 * i.toNat + 1 := by
        rw [UInt64.toNat_add, e1]; simp; omega
      by_cases hir : i.toNat < out.size
      · have hb := hrows1 i hir
        have n1 : ro + 2 * i ≠ ro + 2 * rn + 1 := fun e => by
          have := congrArg UInt64.toNat e; rw [e1, hro3] at this; omega
        have n2 : ro + 2 * i ≠ ro + 2 * rn := fun e => by
          have := congrArg UInt64.toNat e; rw [e1, hro2] at this; omega
        have n3 : ro + 2 * i + 1 ≠ ro + 2 * rn + 1 := fun e => by
          have := congrArg UInt64.toNat e; rw [e2, hro3] at this; omega
        have n4 : ro + 2 * i + 1 ≠ ro + 2 * rn := fun e => by
          have := congrArg UInt64.toNat e; rw [e2, hro2] at this; omega
        rw [hspn3, hspn3, if_neg n1, if_neg n2, if_neg n3, if_neg n4]
        simp only [out', Array.getElem_push, hir, ↓reduceDIte]
        exact hb
      · have hie : i = rn := UInt64.toNat_inj.mp (by omega)
        subst hie
        have hidx : i.toNat = out.size := by omega
        simp only [out', Array.getElem_push, hidx, Nat.lt_irrefl, ↓reduceDIte]
        rw [hspn3, hspn3, if_neg (fun e => by
            have := congrArg UInt64.toNat e; rw [hro2, hro3] at this; omega), if_pos rfl, if_pos rfl]
        exact ⟨by simp [hnpj], hlt2, by simp; rfl⟩
    obtain ⟨y, a', M', hrun', hS', hK', hI', hg', hM', hrows', hw', htop', hro', hSt', hst'⟩ :=
      ih m3 m' a1 M (j + 1) (rn + 1) w out' hJ hS3 hI3 hM3 (hsl1.grow hg3) (by omega) hrows3
        (by rw [hrn1, hrn]; simp [out'])
        (by rw [htop3, hrn1]; rw [UInt64.toNat_add, hro2]; simp; omega)
        (by rw [hrn1, hsz3]; omega)
    have hSt3 : StackGrew m1 m3 := StackGrew.of_spnFrame hf3
      (by rw [htop3, UInt64.le_iff_toNat_le, UInt64.toNat_add, hro2, htop1]; simp; omega)
      (fun x hx => by
        have hx' := UInt64.lt_iff_toNat_lt.mp hx
        rw [htop1] at hx'
        rw [hspn3, if_neg (fun e => by subst e; omega), if_neg (fun e => by subst e; omega)])
    refine ⟨y, a', M', ?_, hS', hK', hI', hg1.trans (hg3.trans hg'), hM', hrows', hw', htop', hro',
      hSt1.toGrew.trans (hSt3.trans hSt'), hst'.trans hst1⟩
    rw [hstep, hu]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [List.getElem?_eq_getElem hlen, ← hd0]
    simp only [StateT.run_bind]
    rw [show (decE w0 : EIdx) = decI w0 from rfl, hrunF]
    rw [hj1] at hrun'
    exact hrun'
  · rw [pgraW.j1.arm2 _ _ _ _ _ _ _ _ _ _ _ _ hfv] at hJ
    refine hskip m' hJ rfl _ rfl ?_
    rw [hstep]
    by_cases hu : u = true
    · subst hu
      have hge : ¬ nP.toNat + j.toNat < fvs.length := by
        intro hl; apply hfv; refine ⟨huw.mpr rfl, UInt64.lt_iff_toNat_lt.mpr ?_⟩; omega
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [List.getElem?_eq_none (by omega)]
    · simp only [Bool.not_eq_true] at hu; subst hu; simp

end

end L.Ind
