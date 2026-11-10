module

public import ConAgua.Arena.ProjGuardRowsOpf
public import ConAgua.Arena.ProjGuardRef
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.WhnfCoreRefine
public import ConAgua.Arena.StrLitExt
import all ConAgua.Arena.Infer
import ConAgua.Arena.ProjGuardRowsCI
import ConAgua.Arena.IndSumSpec.StructUsedHb
public import ConAgua.Arena.IndTwin

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
theorem pgra_ok (p : Prog) (_hf : p.lookup "proj_guard_rows_at" = some projGuardRowsAtL)
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
      · subst ha; rw [ite_eq_left ⟨rfl, rfl, e2⟩, ite_eq_left rfl]
      · by_cases hb : x = ro + 2 * rn
        · subst hb
          rw [ite_eq_right (fun h => ha h.2.1.symm), ite_eq_left ⟨rfl, rfl, e1⟩, ite_eq_right ha, ite_eq_left rfl]
        · rw [ite_eq_right (fun h => ha h.2.1.symm), ite_eq_right (fun h => hb h.2.1.symm), ite_eq_right ha, ite_eq_right hb]
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
        rw [hspn3, hspn3, ite_eq_right n1, ite_eq_right n2, ite_eq_right n3, ite_eq_right n4]
        simp only [out', Array.getElem_push, hir, ↓reduceDIte]
        exact hb
      · have hie : i = rn := UInt64.toNat_inj.mp (by omega)
        subst hie
        have hidx : i.toNat = out.size := by omega
        simp only [out', Array.getElem_push, hidx, Nat.lt_irrefl, ↓reduceDIte]
        rw [hspn3, hspn3, ite_eq_right (fun e => by
                  have := congrArg UInt64.toNat e; rw [hro2, hro3] at this; omega), ite_eq_left rfl, ite_eq_left rfl]
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
        rw [hspn3, ite_eq_right (fun e => by subst e; omega), ite_eq_right (fun e => by subst e; omega)])
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

/-! ## `proj_guard_rows` -/

/-- `openPisAtFvarsF` keeps the caches, the pins and the level store. -/
theorem keepsW_opfGo : ∀ (n : Nat) (acc : Array EIdx) (h : EIdx) (i : Nat),
    Keeps cpl (openPisAtFvarsFGo acc n h i) := by
  intro n
  induction n with
  | zero => intro acc h i; rw [openPisAtFvarsFGo]
            exact Keeps.bind (keepsW_instListFast _ _ _ _) fun _ => Keeps.pure _
  | succ n ih =>
    intro acc h i; rw [openPisAtFvarsFGo]
    split
    · refine Keeps.bind (keeps_view _) fun v => ?_
      split
      · exact Keeps.bind (keepsW_instListFast _ _ _ _) fun _ => Keeps.bind (keepsW_internE _) fun _ =>
          Keeps.bind (ih _ _ _) fun x => by split <;> exact Keeps.pure _
      · exact Keeps.pure _
    · exact Keeps.pure _

theorem keepsW_opa : ∀ (n : Nat) (h : EIdx) (i : Nat), Keeps cpl (openPisAtFvars n h i) := by
  intro n
  induction n with
  | zero => intro h i; rw [openPisAtFvars]; exact Keeps.pure _
  | succ n ih =>
    intro h i; rw [openPisAtFvars]
    split
    · refine Keeps.bind (keeps_view _) fun v => ?_
      split
      · exact Keeps.bind (keepsW_internE _) fun _ => Keeps.bind (keepsW_inst1Fast _ _ _ _) fun _ =>
          Keeps.bind (ih _ _) fun x => by split <;> exact Keeps.pure _
      · exact Keeps.pure _
    · exact Keeps.pure _

theorem keepsW_opfF (n : Nat) (e : EIdx) (i : Nat) : Keeps cpl (openPisAtFvarsF n e i) := by
  unfold openPisAtFvarsF
  exact Keeps.bind (keepsW_opfGo _ _ _ _) fun x => by split <;> first | exact Keeps.pure _ | exact keepsW_opa _ _ _

/-- A table record's parameter count (word `q + 5`) and constructor (word `q + 6`). -/
theorem decTbl_npc {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {tbl : IProjTable} (h : decTbl R q.toNat = some tbl) :
    tbl.numParams = (rd (q + 5)).toNat ∧ HW (rd (q + 6)) ∧ tbl.ctor = decI (rd (q + 6)) := by
  unfold decTbl at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨sn, -, lp, -, np, hnp, ct, hct, nf, -, bs, -, rfl⟩ := h
  obtain ⟨w, hw, hw32, rfl⟩ := hd?_eq hct
  have e : rd (q + 6) = w := hR.offN (k := 6) hw (by decide)
  simp only [nat?, Option.map_eq_some_iff] at hnp
  obtain ⟨v, hv, rfl⟩ := hnp
  have e5 : rd (q + 5) = v := hR.offN (k := 5) hv (by decide)
  rw [e, e5]
  exact ⟨rfl, hw32, rfl⟩

/-- A constant record's name (word `q + 1`). -/
theorem decCV_nameRd {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} (h : decCV R (q.toNat + 1) = some cv) :
    HW (rd (q + 1)) ∧ cv.name = decI (rd (q + 1)) := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨nm, hn, ls, -, ty, -, hc⟩ := h
  cases hc
  obtain ⟨w, hw, hl, rfl⟩ := hd?_eq hn
  have e : rd (q + 1) = w := hR.offN (k := 1) hw (by decide)
  rw [e]; exact ⟨hl, rfl⟩

theorem cv_eta (cv : IConstantVal) : cv = ⟨cv.name, cv.levelParams, cv.type⟩ := rfl

/-- What `proj_guard_rows`' refinement needs of a program. -/
structure PgrProg (p : Prog) : Prop where
  pgr : p.lookup "proj_guard_rows" = some projGuardRowsL
  pgra : p.lookup "proj_guard_rows_at" = some projGuardRowsAtL
  envFind : p.lookup "env_find" = some envFindL
  envRowGet : p.lookup "env_row_get" = some envRowGetL
  baseRowGet : p.lookup "base_row_get" = some baseRowGetL
  ftd : p.lookup "fvar_type_d" = some fvarTypeDL
  eView : p.lookup "e_view" = some eView
  us : UsF p
  opf : OpfF p
  cl : CoreStageClosed p


/-! ## `constTyAt` only extends the store (`EMono`) -/

section emono
open L.Arena

theorem emono_internNNode (v : NNodeView) : EMono (internNNode v) := by
  unfold EMono; intro a r a' h
  simp only [internNNode, StateT.run_bind, StateT.run_get, pure_bind] at h
  emono_close (EStore.internName_ext _ _)

theorem emono_internName : ∀ n : ConLeche.Name, EMono (internName n)
  | .anonymous => by simp only [internName]; exact emono_internNNode _
  | .str p s => by simp only [internName]; exact EMono.bind (emono_internName p) fun _ => emono_internNNode _
  | .num p k => by simp only [internName]; exact EMono.bind (emono_internName p) fun _ => emono_internNNode _

theorem emono_internLevel : ∀ u : ConLeche.Level, EMono (internLevel u)
  | .zero => by simp only [internLevel]; exact emono_internLNode _
  | .succ u => by simp only [internLevel]; exact EMono.bind (emono_internLevel u) fun _ => emono_internLNode _
  | .max u v => by
    simp only [internLevel]
    exact EMono.bind (emono_internLevel u) fun _ => EMono.bind (emono_internLevel v) fun _ =>
      emono_internLNode _
  | .imax u v => by
    simp only [internLevel]
    exact EMono.bind (emono_internLevel u) fun _ => EMono.bind (emono_internLevel v) fun _ =>
      emono_internLNode _
  | .param n => by simp only [internLevel]; exact EMono.bind (emono_internName n) fun _ => emono_internLNode _

theorem emono_internLevelList : ∀ us : List ConLeche.Level, EMono (internLevelList us)
  | [] => by simp only [internLevelList]; exact EMono.pure _
  | u :: us => by
    simp only [internLevelList]
    exact EMono.bind (emono_internLevel u) fun _ => EMono.bind (emono_internLevelList us) fun _ =>
      EMono.pure _

theorem emono_internLevels (us : List ConLeche.Level) : EMono (internLevels us) := by
  unfold internLevels
  exact EMono.bind (emono_internLevelList us) fun _ => emono_internLsNode _

theorem emono_derivedE (h : EIdx) : EMono (derivedE h) := EMono.of_keeps (keeps_derivedE h)
/-- A primitive that reads the state and writes back only its caches or memos. -/
macro "prim_keeps' " d:ident : tactic => `(tactic| (
  unfold Keeps; intro a r a' h
  simp only [$d:ident, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | (simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind] at h; cases h; rfl)
    | (exfalso; revert h; simp [ConRon.Arena.fail, failDanglingLs, throwThe, MonadExceptOf.throw, throw,
        StateT.run, StateT.lift, bind, Except.bind, Functor.map, Except.map]; done)))

theorem emono_readLevelM (h : LIdx) : EMono (readLevelM h) := EMono.of_keeps (by prim_keeps' readLevelM)
theorem emono_readNameM (h : NIdx) : EMono (readNameM h) := EMono.of_keeps (by prim_keeps' readNameM)
theorem emono_readLevelsM (h : LsIdx) : EMono (readLevelsM h) :=
  EMono.of_keeps (by prim_keeps' readLevelsM)
theorem emono_readNamesM : ∀ hs : List NIdx, EMono (readNamesM hs)
  | [] => by simp only [readNamesM]; exact EMono.pure _
  | h :: hs => by
    simp only [readNamesM]
    exact EMono.bind (emono_readNameM h) fun _ => EMono.bind (emono_readNamesM hs) fun _ => EMono.pure _
theorem emono_instLPGet (k : EIdx × Nat) : EMono (instLPGet k) := EMono.of_keeps (by prim_keeps instLPGet)
theorem emono_instLPSet (k : EIdx × Nat) (r : EIdx) : EMono (instLPSet k r) :=
  EMono.of_keeps (by prim_keeps instLPSet)
theorem emono_instLPClear : EMono instLPClear := EMono.of_keeps (by prim_keeps instLPClear)
theorem emono_instLPLGet (k : LIdx) : EMono (instLPLGet k) := EMono.of_keeps (by prim_keeps instLPLGet)
theorem emono_instLPLSet (k r : LIdx) : EMono (instLPLSet k r) := EMono.of_keeps (by prim_keeps instLPLSet)
theorem emono_instLPLsGet (k : LsIdx) : EMono (instLPLsGet k) :=
  EMono.of_keeps (by prim_keeps instLPLsGet)
theorem emono_instLPLsSet (k r : LsIdx) : EMono (instLPLsSet k r) :=
  EMono.of_keeps (by prim_keeps instLPLsSet)

theorem emono_substLMemoAt (ks : List ConLeche.Name) (us : List ConLeche.Level) (u : LIdx) :
    EMono (substLMemoAt ks us u) := by
  unfold substLMemoAt
  refine EMono.bind (emono_instLPLGet _) fun o => ?_
  split
  · exact EMono.pure _
  · exact EMono.bind (emono_readLevelM _) fun _ => EMono.bind (emono_internLevel _) fun _ =>
      EMono.bind (emono_instLPLSet _ _) fun _ => EMono.pure _

theorem emono_substLsMemoAt (ks : List ConLeche.Name) (us : List ConLeche.Level) (vs : LsIdx) :
    EMono (substLsMemoAt ks us vs) := by
  unfold substLsMemoAt
  refine EMono.bind (emono_instLPLsGet _) fun o => ?_
  split
  · exact EMono.pure _
  · exact EMono.bind (emono_readLevelsM _) fun _ => EMono.bind (emono_internLevels _) fun _ =>
      EMono.bind (emono_instLPLsSet _ _) fun _ => EMono.pure _

/-- One step of `instLPGo`'s `succ` case. -/
macro "emono_lp" " using " ih:term : tactic => `(tactic| (
  repeat' (first
    | exact EMono.pure _ | exact EMono.fail _ | exact $ih _
    | exact emono_view _ | exact emono_derivedE _ | exact emono_internE _
    | exact emono_internLamE _ _ | exact emono_internForallEE _ _
    | exact emono_instLPGet _ | exact emono_instLPSet _ _
    | exact emono_substLMemoAt _ _ _ | exact emono_substLsMemoAt _ _ _
    | (unfold internRebuiltSort) | (unfold internRebuiltConst) | (unfold internRebuiltFVar)
    | (unfold internRebuiltApp) | (unfold internRebuiltLam) | (unfold internRebuiltForallE)
    | (unfold internRebuiltLetE) | (unfold internRebuiltProj)
    | (unfold internSortE) | (unfold internConstE) | (unfold internFVarE) | (unfold internAppE)
    | (unfold internLetEE) | (unfold internProjE)
    | (unfold instLPArmFVar) | (unfold instLPArmApp) | (unfold instLPArmLam)
    | (unfold instLPArmForallE) | (unfold instLPArmLet) | (unfold instLPArmProj)
    | with_reducible apply EMono.bind | apply EMono.ite | intro _ | split | (dsimp only))))

theorem emono_instLPGo (ks : List ConLeche.Name) (us : List ConLeche.Level) (F : Nat) :
    ∀ h, EMono (instLPGo ks us F h) := by
  induction F with
  | zero => intro h; rw [instLPGo_zero]; exact EMono.fail _
  | succ F ih =>
    intro h; rw [instLPGo_succ]
    emono_lp using ih

theorem emono_instLPFast (F : Nat) (ks : List NIdx) (us : LsIdx) (e : EIdx) :
    EMono (instLPFast F ks us e) := by
  unfold instLPFast
  refine EMono.bind (emono_derivedE _) fun d => ?_
  split
  · exact EMono.pure _
  · exact EMono.bind (emono_readNamesM _) fun _ => EMono.bind (emono_readLevelsM _) fun _ =>
      EMono.bind emono_instLPClear fun _ => EMono.bind (emono_instLPGo _ _ _ _) fun _ =>
      EMono.bind emono_instLPClear fun _ => EMono.pure _

theorem emono_constTyAt (cv : IConstantVal) (us : LsIdx) : EMono (constTyAt cv us) := by
  unfold constTyAt
  refine EMono.bind (EMono.of_keeps (by unfold Keeps; intro a r a' h; cases h; rfl)) fun s => ?_
  split
  · exact EMono.pure _
  · refine EMono.bind (emono_instLPFast _ _ _ _) fun r => ?_
    unfold EMono; intro a x a' h
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, StateT.run_pure] at h
    cases h; exact Ext.refl _

/-- **`constTyAt` keeps every level readback** (it only extends the store). -/
theorem constTyAt_lkept (cv : IConstantVal) (us : LsIdx) : LKept (constTyAt cv us) := by
  intro a x a' h l u hd
  have he := emono_constTyAt cv us
  unfold EMono at he
  exact (he a x a' h).lss.ls.lvl l u hd

end emono

theorem pgrT_none (fe : IFEnv) (entry : IProjEntry) (us : LsIdx) (a : AState)
    (h : fe.find? entry.ctor = none) : (projGuardRows fe entry us).run a = .ok (none, a) := by
  simp [projGuardRows, h]; rfl

theorem pgrT_some (fe : IFEnv) (entry : IProjEntry) (us : LsIdx) (a a2 a3 : AState) (ci : IConstantInfo)
    (cty : EIdx) (x : Option (List EIdx × EIdx)) (h : fe.find? entry.ctor = some ci)
    (h2 : (constTyAt ci.toConstantVal us).run a = .ok (cty, a2))
    (h3 : (openPisAtFvarsF (entry.numParams + entry.idx + 1) cty 0).run a2 = .ok (x, a3)) :
    (projGuardRows fe entry us).run a =
      (match x with
       | some (fvs, _) => do
         let rows ← projGuardRowsAt ci.toConstantVal.type entry.numParams entry.idx fvs 0 #[]
         pure (some rows)
       | none => pure none : AM (Option (Array (Nat × EIdx)))).run a3 := by
  simp only [projGuardRows, h, StateT.run_bind, h2, except_ok_bind, h3]
  rcases x with _ | ⟨fvs, b⟩ <;> rfl

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}

/-- **`proj_guard_rows` refines `projGuardRows` under `CoreS`** (the pool's `IWOK` and the `hb` memo
at entry; the L code aborts where the parameter count plus field index wraps; `constTyAt_lkept` for the level
readbacks): `env_find`, `const_ty_at` (`ConstTyAtOK`), `open_pis_at_fvars_f` (`opfF_okC`),
`proj_guard_rows_at` (`pgra_ok`). -/
theorem pgr_okH (p : Prog) (hP : PgrProg p) (hCT : ConstTyAtOK p)
    (n : Nat) (m m' : Mem) (a : AState) (M : ModeMaps) (q i us : Word) (tbl : IProjTable)
    (r : List Word) (hS : CoreS dn m a vis fe M eb) (hI : IWOK m) (hM : ∃ mp, hbMR m mp)
    (hq : decTbl (erecP m) q.toNat = some tbl) (hus : HW us)
    (h : callW p n "proj_guard_rows" [vis, q, i, us] m = some (r, m')) :
    ∃ y a', (projGuardRows fe (tbl.entry i.toNat) (decI us)).run a = .ok (y, a') ∧
      CoreAfterG dn m m' a' vis fe M eb ∧
      (∀ h l, denoteL a.store.ls h = some l → denoteL a'.store.ls h = some l) ∧ PgrRes m m' r y ∧
      IWOK m' ∧ IWGrow m m' ∧ ∃ mp, hbMR m' mp := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pgrW_spec p hP.pgr n _ vis q i us) h
  rw [hs'] at hW
  clear h hs'
  rcases n with _ | n
  · cases hW
  obtain ⟨hnp, hct32, hct⟩ := decTbl_npc (erRdOK m) hq
  simp only [pgrW] at hW
  rw [erRd_congr rfl rfl, erRd_congr rfl rfl] at hW
  rcases c1 : callW p n "env_find" [erRd m (q + 6), vis] m with _ | ⟨r1, m1⟩
  · rw [c1, pgrW.k_env_find.none] at hW; cases hW
  rw [c1] at hW
  obtain ⟨s1, hs1, hm1, -, hfind, hdec⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p hP.envRowGet hP.baseRowGet hP.envFind n _ vis _ hS.env hct32) c1
  have hm1' : m1 = m := hs1 ▸ hm1
  subst hm1'
  have hctor : (tbl.entry i.toNat).ctor = decI (erRd m1 (q + 6)) := hct
  by_cases g1 : r1.headD 0 = 0
  · rw [pgrW.k_env_find.arm1 _ _ _ _ _ _ _ g1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hn : fe.find? (tbl.entry i.toNat).ctor = none := by
      rw [hctor, hfind]; simp only [envFound, g1, ↓reduceIte]
    exact ⟨none, a, pgrT_none _ _ _ _ hn, ⟨M, hS, KeptAll.refl _ _, StackGrew.refl _⟩,
      fun _ _ h => h, rfl, hI, IWGrow.refl _, hM⟩
  obtain ⟨ci, hci⟩ := hdec g1
  have hfind' : fe.find? (tbl.entry i.toNat).ctor = some ci := by
    rw [hctor, hfind]; simp only [envFound, g1, ↓reduceIte]; exact hci
  rw [pgrW.k_env_find.arm2 _ _ _ _ _ _ _ g1] at hW
  generalize hc : r1.tail.headD 0 = c at hW hci
  have hcv := decCI_cvA hci
  obtain ⟨hlps, -, hty, hty32⟩ := L.Arena.decCV_rd (erRdOK m1) hcv
  obtain ⟨hnn32, hnn⟩ := decCV_nameRd (erRdOK m1) hcv
  simp only [erRd_congr rfl rfl] at hW
  -- `const_ty_at`
  rcases c2 : callW p n "const_ty_at" [erRd m1 (c + 1), erRd m1 (c + 2), erRd m1 (c + 3),
      erRd m1 (c + 4), us] m1 with _ | ⟨r2, m2⟩
  · rw [c2, pgrW.k_const_ty_at.none] at hW; cases hW
  by_cases gk : erRd m1 (q + 5) + i + 1 ≤ erRd m1 (q + 5)
  · rw [c2, pgrW.k_const_ty_at.abort1 (hc1 := gk)] at hW; cases hW
  rw [c2, pgrW.k_const_ty_at.arm1 (hc1 := gk)] at hW
  have hB : tbl.numParams + i.toNat + 1 < 2 ^ 64 := by
    have hnp' : tbl.numParams = (erRd m1 (q + 5)).toNat := hnp
    rw [hnp']
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_add] at gk
    have := (erRd m1 (q + 5)).toNat_lt; have := i.toNat_lt
    simp at gk; omega
  have h2 := CoreSpec.of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (hCT n ⟨m1, Locals.init []⟩ a dn vis fe M eb _ _ _ _ us _ hS hnn32 hty32 hus hlps) c2
  have hcvE : ci.toConstantVal = ⟨decI (erRd m1 (c + 1)), ci.toConstantVal.levelParams,
      decE (erRd m1 (c + 4))⟩ := by
    rw [cv_eta ci.toConstantVal, hnn, hty]; rfl
  have hrun2 : (constTyAt ci.toConstantVal (decI us)).run a =
      .ok (decE (r2.headD 0), AM.st (constTyAt ci.toConstantVal (decI us)) a) := by
    rw [hcvE, AM.run_of_ok _ _ h2.run, h2.res]; rfl
  obtain ⟨M2, hS2, hK2, hSt2⟩ := h2.after
  rw [← hcvE] at hS2
  have hr2 : HW (r2.headD 0) := h2.resOk
  have hfr2 := callW_coreFrame hP.cl (mem_stageCoreFns (List.mem_append_right _ (coreFn_of (by decide))) (by simp [coreLeafOnly])) c2
  obtain ⟨hI2, hg2⟩ := hfr2.2 hI
  have hM2 := callW_coreHb hP.cl (mem_stageCoreFns (List.mem_append_right _ (coreFn_of (by decide))) (by simp [coreLeafOnly])) c2 hM
  generalize ha2 : AM.st (constTyAt ci.toConstantVal (decI us)) a = a2 at hrun2 hS2
  -- `open_pis_at_fvars_f`
  rcases c3 : callW p n "open_pis_at_fvars_f" [erRd m1 (q + 5) + i + 1, r2.headD 0, 0] m2 with
    _ | ⟨r3, m3⟩
  · rw [c3, pgrW.k_open_pis_at_fvars_f.none] at hW; cases hW
  rw [c3] at hW
  have hopf := callW_opfFC hP.opf c3
  obtain ⟨x3, a3, M3, hrun3, hS3, hK3, hSt3, htb, hres3⟩ := opfF_okC _ _ _ hr2 hopf hS2 hI2
  obtain ⟨hI3, hg3⟩ := opfF_grow hopf hI2
  have hM3 := hbMR_keep (opfF_frame hopf) (by decide) (by decide) hM2
  have hkp := (keepsW_opfF _ _ _).run hrun3
  have hk3 : (erRd m1 (q + 5) + i + 1).toNat = (tbl.entry i.toNat).numParams + (tbl.entry i.toNat).idx + 1 := by
    show _ = tbl.numParams + i.toNat + 1
    rw [hnp] at hB ⊢
    rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
  rw [hk3] at hrun3
  have hrunT := pgrT_some fe (tbl.entry i.toNat) (decI us) a a2 a3 ci _ x3 hfind' hrun2 hrun3
  have hlk2 : ∀ h l, denoteL a.store.ls h = some l → denoteL a2.store.ls h = some l :=
    fun h l hd => constTyAt_lkept _ _ a _ a2 hrun2 h l hd
  have hlk3 : a3.store.lss = a2.store.lss := by
    simp only [cpl, Prod.mk.injEq] at hkp; exact hkp.2.2
  cases x3 with
  | none =>
    have g3 : r3.headD 0 = 0 := hres3
    rw [pgrW.k_open_pis_at_fvars_f.arm1 _ _ _ _ _ _ _ g3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨none, a3, by rw [hrunT]; rfl, ⟨M3, hS3, hK2.trans hK3, (hSt2.trans hSt3).toGrew⟩,
      fun h l hd => by have := hlk2 h l hd; simp only [EStore.ls] at this ⊢; rw [hlk3]; exact this,
      rfl, hI3, hg2.trans hg3, hM3⟩
  | some fb =>
    obtain ⟨fvs, b⟩ := fb
    obtain ⟨g3, hfn, hsl, -, -⟩ := hres3
    rw [pgrW.k_open_pis_at_fvars_f.arm2 _ _ _ _ _ _ _ (by rw [g3]; decide)] at hW
    -- the records are kept across `const_ty_at` and `open_pis_at_fvars_f`
    have hE0 : m3.arr64 EREC = m1.arr64 EREC :=
      ((opfF_frame hopf).arr EREC (by decide) (by decide)).trans (hfr2.1.arr EREC coreFrA_erec (by decide))
    have hE1 : m3.arr64 (tier1 EREC) = m1.arr64 (tier1 EREC) :=
      ((opfF_frame hopf).arr (tier1 EREC) (by decide) (by decide)).trans
        (hfr2.1.arr (tier1 EREC) coreFrA_erec1 (by decide))
    rw [erRd_congr hE0 hE1] at hW
    generalize hro : rdW (m3.arr64 CTL) 136 = ro at hW
    rcases c4 : callW p n "proj_guard_rows_at" [erRd m1 (c + 4), erRd m1 (q + 5), i, r3.tail.headD 0,
        r3.tail.tail.headD 0, 0, ro, 0] m3 with _ | ⟨r4, m4⟩
    · rw [c4, pgrW.k_proj_guard_rows_at.none] at hW; cases hW
    rw [c4, pgrW.k_proj_guard_rows_at.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (pgraW_spec p hP.pgra n _ _ _ _ _ _ _ _ _) c4
    rw [hs4] at hW4
    have htop3 : spTop m3 = spTop m1 := hSt3.top.trans hSt2.top
    have hro' : ro = spTop m1 := by rw [← hro, ← htop3]; rfl
    have hsz31 : (m3.arr64 SPN).size = (m1.arr64 SPN).size := hSt3.size.trans hSt2.size
    have htb' : (spTop m1).toNat ≤ (m1.arr64 SPN).size := by
      rw [← hSt2.top, ← hSt2.size]; exact htb
    obtain ⟨y, a4, M4, hrun4, hS4, hK4, hI4, hg4, hM4, hrows4, hw4, htop4, -, hSt4, hst4⟩ :=
      pgra_ok p hP.pgra hP.us hP.ftd hP.eView _ _ _ _ _ ro fvs hty32
        (by rw [← hnp]; exact hB) hfn n m3 m4 a3 M3 0 0 (r4.headD 0) #[] hW4 hS3 hI3 hM3 hsl
        (by simp) (fun i hi => absurd hi (by simp)) rfl
        (by rw [hro', htop3]; simp) (by rw [hro', hsz31]; simpa using htb')
    have hty' : ci.toConstantVal.type = decI (erRd m1 (c + 4)) := hty
    refine ⟨some y, a4, ?_, ⟨M4, hS4, hK2.trans (hK3.trans hK4), (hSt2.trans hSt3).toGrew.trans hSt4⟩,
      fun h l hd => by
        have := hlk2 h l hd; simp only [EStore.ls] at this ⊢; rw [hst4, hlk3]; exact this,
      ⟨by simp, by simp [hro'], hw4.symm, by rw [← hro']; exact hrows4,
        by rw [htop4, ← hro', hw4]; simp⟩, hI4, hg2.trans (hg3.trans hg4), hM4⟩
    rw [hrunT]
    simp only [StateT.run_bind, hty']
    rw [show (tbl.entry i.toNat).numParams = (erRd m1 (q + 5)).toNat from hnp,
      show (tbl.entry i.toNat).idx = i.toNat from rfl]
    rw [show (0 : Nat) = (0 : Word).toNat from rfl, hrun4]
    rfl

end

end L.Ind
