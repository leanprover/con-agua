import ConAgua.Arena.IndSumSpec
import ConAgua.Arena.IndInstall

/-!
# Refinements of `IndInstall` (lane `induct`)

`check_block_doms_at` refines `ConRon.Arena.checkBlockDomsAt .verified`, by the lane's template
(`IndSumSpec.lean`'s `struct_ps_at_go`): a word model `domsW` that calls the stubs' word models
(`stubM`) and itself, a `vcgen` spec of `domsW` with no twin values in sight, a relational lemma
(by induction on the model's fuel) using the stubs' `RelAM` facts, and the census theorem by
`triple_post` + `AM.of_run_ok`.
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `domsW`: the word model of `check_block_doms_at` -/

mutual
/-- **The model of `check_block_doms_at`.** `j = 0`: `return 0`, no callee touched. Otherwise:
abort if either index is out of the (logical) list length, else call `fvar_type_d` then
`is_def_eq_core`, then recurse at `j - 1`. -/
def domsW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, off, fo, fl, dO, dl, j =>
    if j = 0 then some ([0], m)
    else if fl ≤ j - 1 then none
    else if dl ≤ j - 1 then none
    else
      domsK1 n vis off fo fl dO dl j (rdW (m.arr64 IW) (dO + (j - 1)))
        (stubM "fvar_type_d" m [rdW (m.arr64 IW) (fo + (j - 1))])

/-- After `fvar_type_d`: call `is_def_eq_core`. -/
def domsK1 (n : Nat) (vis off fo fl dO dl j b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) =>
    domsK2 n vis off fo fl dO dl j
      (stubM "is_def_eq_core" m1 [vis, off + (j - 1), ra.headD 0, b])

/-- After `is_def_eq_core`: `unless ok do abort`, then the recursive call. -/
def domsK2 (n : Nat) (vis off fo fl dO dl j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) =>
    if rb.headD 0 = 0 then none else domsK3 (domsW n m2 vis off fo fl dO dl (j - 1))

/-- After the recursive call: `u := call …; return u` returns the callee's first word. -/
def domsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (vis off fo fl dO dl j b : Word) (ra rb : List Word)

theorem domsW_zero (hj : j = 0) : domsW (n + 1) m vis off fo fl dO dl j = some ([0], m) := by
  simp [domsW, hj]
theorem domsW_abortF (hj : j ≠ 0) (hfl : fl ≤ j - 1) :
    domsW (n + 1) m vis off fo fl dO dl j = none := by simp [domsW, hj, hfl]
theorem domsW_abortD (hj : j ≠ 0) (hfl : ¬ fl ≤ j - 1) (hdl : dl ≤ j - 1) :
    domsW (n + 1) m vis off fo fl dO dl j = none := by simp [domsW, hj, hfl, hdl]
theorem domsW_cons (hj : j ≠ 0) (hfl : ¬ fl ≤ j - 1) (hdl : ¬ dl ≤ j - 1) :
    domsW (n + 1) m vis off fo fl dO dl j =
      domsK1 n vis off fo fl dO dl j (rdW (m.arr64 IW) (dO + (j - 1)))
        (stubM "fvar_type_d" m [rdW (m.arr64 IW) (fo + (j - 1))]) := by
  simp [domsW, hj, hfl, hdl]
theorem domsK1_some :
    domsK1 n vis off fo fl dO dl j b (some (ra, m1)) =
      domsK2 n vis off fo fl dO dl j
        (stubM "is_def_eq_core" m1 [vis, off + (j - 1), ra.headD 0, b]) := by
  rw [domsK1]
theorem domsK2_abort (heq : rb.headD 0 = 0) : domsK2 n vis off fo fl dO dl j (some (rb, m2)) = none := by
  rw [domsK2, if_pos heq]
theorem domsK2_ok (heq : rb.headD 0 ≠ 0) :
    domsK2 n vis off fo fl dO dl j (some (rb, m2)) = domsK3 (domsW n m2 vis off fo fl dO dl (j - 1)) := by
  rw [domsK2, if_neg heq]
theorem domsK3_some (r : List Word) (m : Mem) : domsK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] domsW_zero => domsW (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] domsW_abortF => domsW (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] domsW_abortD => domsW (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] domsW_cons => domsW (n + 1) m vis off fo fl dO dl j
grind_pattern [ind_grind] domsK1_some => domsK1 n vis off fo fl dO dl j b (some (ra, m1))
grind_pattern [ind_grind] domsK2_abort => domsK2 n vis off fo fl dO dl j (some (rb, m2))
grind_pattern [ind_grind] domsK3_some => domsK3 (some (r, m))
grind_pattern [ind_grind] domsK2_ok => domsK2 n vis off fo fl dO dl j (some (rb, m2))

/-! ## `domsW_spec`: the `vcgen` proof against the L code (no twin values) -/

section spec
variable (p : Prog) (hp : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
include hp

theorem domsW_spec (n : Nat) : ∀ (s₀ : St) (vis off fo fl dO dl j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun r s' => LocEq s' s₀ ∧ domsW n s₀.mem vis off fo fl dO dl j = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis off fo fl dO dl j
    rw [invoke_eq _ hp]; simp only [callFn, checkBlockDomsAt]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis off fo fl dO dl j
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockDomsAt]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "fvar_type_d" n, stubM_spec p "is_def_eq_core" n, ih] <;>
      finish (gen := 20)

end spec

/-! ## `domsW_ok`: the relational lemma, by induction on the model's fuel -/

theorem mapM_opt_congr {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..), mapM_opt_congr f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem decHL_grow {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {o l : Nat}
    (h : o + l ≤ iwTop m) : (decHL m' o l : Option (List (Idx k))) = decHL m o l := by
  simp only [decHL, hslice?]
  apply mapM_opt_congr
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [hd?, iwA]
  rw [hg.2.2.1 (o + j) (by omega)]

theorem decHL_getI {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (j : Nat) (hj : j < l) :
    iwH m (o + j) = some (xs[j]'(by rw [decHL_length m h]; exact hj)) := by
  have hl := decHL_length m h
  simp only [decHL, hslice?] at h
  have hget := mapM_opt_get (fun j => hd? (iwA m) (o + j)) (List.range l) xs h j (by simpa using hj)
  simpa [iwH] using hget

theorem decHL_get' {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (j : Nat) (hj : j < l) (hb : o + l < 2 ^ 64) :
    ∃ w, rdW (m.arr64 IW) (UInt64.ofNat (o + j)) = w ∧ w.toNat < 2 ^ 32 ∧
      xs[j]'(by rw [decHL_length m h]; exact hj) = decI w := by
  obtain ⟨w, h1, h2, h3⟩ := iwH_rdW (decHL_getI h j hj) (by omega)
  exact ⟨w, h1, h2, h3.symm⟩

theorem domsW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (m m' : Mem)
    (a : AState) (vis off fo fl dO dl j : Word) (fvs doms : List EIdx) (r : List Word),
    domsW n m vis off fo fl dO dl j = some (r, m') →
    StageR dn vis fe m a → decHL m fo.toNat fl.toNat = some fvs → decHL m dO.toNat dl.toNat = some doms →
    fo.toNat + fl.toNat < 2 ^ 64 → dO.toNat + dl.toNat < 2 ^ 64 → fo.toNat + fl.toNat ≤ iwTop m → dO.toNat + dl.toNat ≤ iwTop m → off.toNat + fl.toNat < 2 ^ 64 →
    j.toNat ≤ fl.toNat → j.toNat ≤ dl.toNat →
    ∃ a', (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat).run a = .ok ((), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  induction n with
  | zero => intro dn fe m m' a vis off fo fl dO dl j fvs doms r h; simp [domsW] at h
  | succ n ih =>
    intro dn fe m m' a vis off fo fl dO dl j fvs doms r h hStage hfvs hdoms hfob hdob hfot hdot hoob hjf hjd
    have hfvl := decHL_length m hfvs
    have hdol := decHL_length m hdoms
    by_cases hj : j = 0
    · subst hj
      rw [domsW_zero n m vis off fo fl dO dl 0 rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hm⟩ := h
      subst hm
      refine ⟨a, ?_, hStage, IWGrow.refl m⟩
      have hj0 : (0 : Word).toNat = 0 := rfl
      rw [hj0]
      rfl
    · have hjpos : 1 ≤ j.toNat := by
        rcases Nat.eq_zero_or_pos j.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hj
        · omega
      have hj1 : (j - 1).toNat = j.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hjpos))]
        simp
      by_cases hfl : fl ≤ j - 1
      · rw [domsW_abortF n m vis off fo fl dO dl j hj hfl] at h; simp at h
      by_cases hdl : dl ≤ j - 1
      · rw [domsW_abortD n m vis off fo fl dO dl j hj hfl hdl] at h; simp at h
      rw [domsW_cons n m vis off fo fl dO dl j hj hfl hdl] at h
      have hjm1f : j.toNat - 1 < fl.toNat := by
        have : ¬ fl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hfl
        omega
      have hjm1d : j.toNat - 1 < dl.toNat := by
        have : ¬ dl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hdl
        omega
      have hfoeq : fo + (j - 1) = UInt64.ofNat (fo.toNat + (j.toNat - 1)) := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
      have hdoeq : dO + (j - 1) = UInt64.ofNat (dO.toNat + (j.toNat - 1)) := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, hj1]; simp
      obtain ⟨wa, hwa_eq, hwa_lt, hwa_dec⟩ := decHL_get' hfvs (j.toNat - 1) hjm1f hfob
      obtain ⟨wb, hwb_eq, hwb_lt, hwb_dec⟩ := decHL_get' hdoms (j.toNat - 1) hjm1d hdob
      rw [hfoeq] at h
      rw [hdoeq] at h
      rw [hwa_eq] at h
      rw [hwb_eq] at h
      cases hra : stubM "fvar_type_d" m [wa] with
      | none => rw [hra] at h; simp [domsK1] at h
      | some ram1 =>
        obtain ⟨ra, m1⟩ := ram1
        rw [hra, domsK1_some] at h
        obtain ⟨x1, a1, hrun1, hStage1, hg1, hw1lt, hw1eq⟩ :=
          fvarTypeD_spec dn vis fe wa hwa_lt m m1 a ra hra hStage
        cases hrb : stubM "is_def_eq_core" m1 [vis, off + (j - 1), ra.headD 0, wb] with
        | none => rw [hrb] at h; simp [domsK2] at h
        | some rbm2 =>
          obtain ⟨rb, m2⟩ := rbm2
          rw [hrb] at h
          by_cases heq0 : rb.headD 0 = 0
          · rw [domsK2_abort (heq := heq0) ..] at h; simp at h
          · rw [domsK2_ok (heq := heq0) ..] at h
            obtain ⟨x2, a2, hrun2, hStage2, hg2, hb2eq, hb2lt⟩ :=
              isDefEqCore_spec dn vis fe (off + (j - 1)) (ra.headD 0) wb hw1lt hwb_lt m1 m2 a1 rb
                hrb hStage1
            have hdep : (off + (j - 1)).toNat = off.toNat + (j.toNat - 1) := by
              rw [UInt64.toNat_add, hj1]; exact Nat.mod_eq_of_lt (by omega)
            rw [hdep] at hrun2
            have hfvsij : fvs[j.toNat - 1]? = some (decI wa) := by
              rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < fvs.length)]
              exact congrArg some hwa_dec
            have hdomsij : doms[j.toNat - 1]? = some (decI wb) := by
              rw [List.getElem?_eq_getElem (by omega : j.toNat - 1 < doms.length)]
              exact congrArg some hwb_dec
            cases hw : domsW n m2 vis off fo fl dO dl (j - 1) with
            | none => rw [hw] at h; simp [domsK3] at h
            | some rm3 =>
            obtain ⟨r3, m3⟩ := rm3
            rw [hw, domsK3_some] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, hm3⟩ := h
            subst hm3
            obtain ⟨a', hrun3, hStage3, hg3⟩ := ih dn fe m2 m3 a2 vis off fo fl dO dl (j - 1) fvs doms r3
              hw hStage2 (by rw [decHL_grow (hg1.trans hg2)]; exact hfvs; omega) (by rw [decHL_grow (hg1.trans hg2)]; exact hdoms; omega) hfob hdob (by have := (hg1.trans hg2).1; omega) (by have := (hg1.trans hg2).1; omega) hoob (by omega) (by omega)
            rw [hj1] at hrun3
            refine ⟨a', ?_, hStage3, (hg1.trans hg2).trans hg3⟩
            have hjeq : j.toNat = (j.toNat - 1) + 1 := by omega
            have hv2 : x2 = true := by
              rw [← hb2eq]
              simpa using heq0
            rw [hjeq]
            show (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms ((j.toNat - 1) + 1)).run a =
              .ok ((), a')
            simp only [ConRon.Arena.checkBlockDomsAt, unwrapOr, hfvsij, hdomsij, pure_bind,
              StateT.run_bind]
            rw [hrun1]
            simp only [bind, Except.bind]
            rw [← hw1eq, hrun2]
            simp only [bind, Except.bind, hv2, StateT.run_pure]
            exact hrun3

/-! ## The census theorem -/

section census
variable (p : Prog) (hp : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
include hp

/-- **`check_block_doms_at` refines `checkBlockDomsAt .verified`.** -/
@[refines ConRon.Arena.checkBlockDomsAt]
theorem checkBlockDomsAt_refines (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis off fo fl dO dl j : Word)
    (fvs doms : List EIdx) (hStage : StageR dn vis fe s₀.mem a₀)
    (hfvs : decHL s₀.mem fo.toNat fl.toNat = some fvs)
    (hdoms : decHL s₀.mem dO.toNat dl.toNat = some doms)
    (hfob : fo.toNat + fl.toNat < 2 ^ 64) (hdob : dO.toNat + dl.toNat < 2 ^ 64)
    (hfot : fo.toNat + fl.toNat ≤ iwTop s₀.mem) (hdot : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hoob : off.toNat + fl.toNat < 2 ^ 64) (hjf : j.toNat ≤ fl.toNat) (hjd : j.toNat ≤ dl.toNat) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_doms_at" [vis, off, fo, fl, dO, dl, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.checkBlockDomsAt V fe off.toNat fvs doms j.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (domsW_spec p hp n s₀ vis off fo fl dO dl j) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hStage', hg⟩ := domsW_ok n dn fe s₀.mem s'.mem a₀ vis off fo fl dO dl j fvs doms r hm
    hStage hfvs hdoms hfob hdob hfot hdot hoob hjf hjd
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hStage', hg⟩

end census

end L.Ind
