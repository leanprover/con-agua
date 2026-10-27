import ConAgua.Arena.IndRealCrF
import ConAgua.Arena.IndSumSpec.StructElimLevel
import ConAgua.Arena.IndInstallSpec.DomsW

/-!
# StructProjArgP: `ConRon.Arena.structProjArgP`, `ConRon.Arena.structProjPs`, `ConRon.Arena.structPsAt`

The refinement theorems `structProjArgP_refines`, `structPsAt_refines`, `structProjPs_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **Inverting a model continuation** (`K none = none`, `K (some (r, m)) = body r m`): a result
of `K o` comes from a result of `o`. Replaces `cases h : o | none => … | some …` blocks. -/
theorem kSome_inv {β γ : Type} {K : Option (β × Mem) → Option γ} {body : β → Mem → Option γ}
    {o : Option (β × Mem)} {y : γ} (h : K o = some y) (hn : K none = none)
    (hs : ∀ r m, K (some (r, m)) = body r m) : ∃ r m, o = some (r, m) ∧ body r m = some y := by
  rcases o with _ | ⟨r, m⟩
  · rw [hn] at h; cases h
  · exact ⟨r, m, rfl, hs r m ▸ h⟩

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_struct_doms_at` -/

mutual
/-- **The model of `check_struct_doms_at`**: `domsW` returning no words. -/
def sdomsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, off, fo, fl, dO, dl, j =>
    if j = 0 then some ([], m)
    else if fl ≤ j - 1 then none
    else if dl ≤ j - 1 then none
    else
      sdomsK1 cR n vis off fo fl dO dl j (rdW (m.arr64 IW) (dO + (j - 1)))
        (ftdF m [rdW (m.arr64 IW) (fo + (j - 1))])

/-- After `fvar_type_d`. -/
def sdomsK1 (cR : CallM) (n : Nat) (vis off fo fl dO dl j b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) =>
    sdomsK2 cR n vis off fo fl dO dl j
      (cR n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, b] m1)

/-- After `is_def_eq_core`. -/
def sdomsK2 (cR : CallM) (n : Nat) (vis off fo fl dO dl j : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) =>
    if rb.headD 0 = 0 then none else sdomsK3 (sdomsW cR n m2 vis off fo fl dO dl (j - 1))

/-- After the recursive call (its result discarded). -/
def sdomsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([], m)
end

/-- `sdomsW` is `domsW` with the result words dropped. -/
theorem sdomsW_eq (cR : CallM) (n : Nat) : ∀ (m : Mem) (vis off fo fl dO dl j : Word),
    sdomsW cR n m vis off fo fl dO dl j =
      (domsW cR n m vis off fo fl dO dl j).map (fun r => ([], r.2)) := by
  induction n with
  | zero => intro m vis off fo fl dO dl j; simp [sdomsW, domsW]
  | succ n ih =>
    intro m vis off fo fl dO dl j
    simp only [sdomsW, domsW]
    split <;> try rfl
    split <;> try rfl
    split <;> try rfl
    cases ftdF m [rdW (m.arr64 IW) (fo + (j - 1))] with
    | none => simp [sdomsK1, domsK1]
    | some x =>
      obtain ⟨ra, m1⟩ := x
      simp only [sdomsK1, domsK1]
      cases cR n "is_def_eq_core" [vis, off + (j - 1), ra.headD 0, rdW (m.arr64 IW) (dO + (j - 1))] m1 with
      | none => simp [sdomsK2, domsK2]
      | some y =>
        obtain ⟨rb, m2⟩ := y
        simp only [sdomsK2, domsK2]
        split <;> try rfl
        rw [ih]
        cases domsW cR n m2 vis off fo fl dO dl (j - 1) with
        | none => simp [sdomsK3, domsK3]
        | some z => rfl

/-- The twins agree on successful runs (they differ in the error message only). -/
theorem checkStructDomsAt_of_block (fe : IFEnv) (off : Nat) (fvs doms : List EIdx) :
    ∀ (j : Nat) (a a' : AState),
    (ConRon.Arena.checkBlockDomsAt V fe off fvs doms j).run a = .ok ((), a') →
    (ConRon.Arena.checkStructDomsAt V fe off fvs doms j).run a = .ok ((), a') := by
  intro j
  induction j with
  | zero => intro a a' h; simpa [ConRon.Arena.checkBlockDomsAt, ConRon.Arena.checkStructDomsAt] using h
  | succ j ih =>
    intro a a' h
    simp only [ConRon.Arena.checkBlockDomsAt, ConRon.Arena.checkStructDomsAt] at h ⊢
    cases hf : fvs[j]? with
    | none => simp [hf, unwrapOr] at h; cases h
    | some x =>
    cases hd : doms[j]? with
    | none => simp [hf, hd, unwrapOr] at h; cases h
    | some y =>
    simp only [hf, hd, unwrapOr, pure_bind, StateT.run_bind] at h ⊢
    cases h1 : (fvarTypeD x).run a with
    | error e => rw [h1] at h; cases h
    | ok v =>
    obtain ⟨t, a1⟩ := v
    simp only [h1] at h ⊢
    simp only [bind, Except.bind] at h ⊢
    cases h2 : (isDefEqCore V fe checkFuel (off + j) t y).run a1 with
    | error e => rw [h2] at h; cases h
    | ok w =>
    obtain ⟨bv, a2⟩ := w
    simp only [h2] at h ⊢
    cases bv with
    | false => simp [fail] at h; cases h
    | true => simp only at h ⊢; exact ih _ _ (by simpa using h)

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Slices, head first -/

/-- **A decoding slice of length `l ≥ 1`**: its head is the word at `o`, its tail decodes at
`o + 1`. -/
theorem decHL_cons {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)}
    (h : decHL m o.toNat l.toNat = some xs) (hl : l ≠ 0) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ∃ w xs', xs = decI w :: xs' ∧ rdW (m.arr64 IW) o = w ∧ w.toNat < 2 ^ 32 ∧
      decHL m (o + 1).toNat (l - 1).toNat = some xs' := by
  have hl1 : 1 ≤ l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
    · omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hlm : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hl1))]; simp
  rw [ho1, hlm]
  have hs : l.toNat = (l.toNat - 1) + 1 := by omega
  rw [hs] at h
  simp only [decHL] at h
  rw [hslice?_succ] at h
  cases hx : hd? (iwA m) o.toNat with
  | none => rw [hx] at h; cases h
  | some x =>
    cases ht : (hslice? (iwA m) (o.toNat + 1) (l.toNat - 1) : Option (List (Idx k))) with
    | none => rw [hx, ht] at h; cases h
    | some xs' =>
      rw [hx, ht] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW (m := m) (i := o.toNat) (x := x) hx (by omega)
      refine ⟨w, xs', by rw [← h, hw3], by simpa using hw1, hw2, ht⟩

/-! ## `field_doms_resolve`, `idx_args_resolve` -/

mutual
/-- **The model of `field_doms_resolve`.** -/
def fdrW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, v, o, l =>
    if l = 0 then some ([1], m)
    else fdrK1 n v o l (ftdF m [rdW (m.arr64 IW) o])
/-- After `fvar_type_d`. -/
def fdrK1 (n : Nat) (v o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m1) => fdrK2 n v o l (crfF m1 [v, ra.headD 0])
/-- After `consts_resolve_ffast`. -/
def fdrK2 (n : Nat) (v o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) => if rb.headD 0 = 0 then some ([0], m2) else resK (fdrW n m2 v (o + 1) (l - 1))
/-- After a recursive call: its first word. -/
def resK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

mutual
/-- **The model of `idx_args_resolve`.** -/
def iarW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, v, o, l =>
    if l = 0 then some ([1], m)
    else iarK n v o l (crfF m [v, rdW (m.arr64 IW) o])
/-- After `consts_resolve_ffast`. -/
def iarK (n : Nat) (v o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m2) => if rb.headD 0 = 0 then some ([0], m2) else resK' (iarW n m2 v (o + 1) (l - 1))
/-- After a recursive call: its first word. -/
def resK' : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (v o l : Word) (ra rb r : List Word)
theorem fdrW_nil (hl : l = 0) : fdrW (n + 1) m v o l = some ([1], m) := by simp [fdrW, hl]
theorem fdrW_cons (hl : l ≠ 0) :
    fdrW (n + 1) m v o l = fdrK1 n v o l (ftdF m [rdW (m.arr64 IW) o]) := by
  simp [fdrW, hl]
theorem fdrK1_some : fdrK1 n v o l (some (ra, m1)) =
    fdrK2 n v o l (crfF m1 [v, ra.headD 0]) := by rw [fdrK1]
theorem fdrK2_no (h : rb.headD 0 = 0) : fdrK2 n v o l (some (rb, m2)) = some ([0], m2) := by
  rw [fdrK2, ite_eq_left h]
theorem fdrK2_yes (h : rb.headD 0 ≠ 0) :
    fdrK2 n v o l (some (rb, m2)) = resK (fdrW n m2 v (o + 1) (l - 1)) := by rw [fdrK2, ite_eq_right h]
theorem resK_some : resK (some (r, m)) = some ([r.headD 0], m) := rfl
theorem iarW_nil (hl : l = 0) : iarW (n + 1) m v o l = some ([1], m) := by simp [iarW, hl]
theorem iarW_cons (hl : l ≠ 0) :
    iarW (n + 1) m v o l = iarK n v o l (crfF m [v, rdW (m.arr64 IW) o]) := by
  simp [iarW, hl]
theorem iarK_no (h : rb.headD 0 = 0) : iarK n v o l (some (rb, m2)) = some ([0], m2) := by
  rw [iarK, ite_eq_left h]
theorem iarK_yes (h : rb.headD 0 ≠ 0) :
    iarK n v o l (some (rb, m2)) = resK' (iarW n m2 v (o + 1) (l - 1)) := by rw [iarK, ite_eq_right h]
theorem resK'_some : resK' (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] fdrW_nil => fdrW (n + 1) m v o l
grind_pattern [ind_grind] fdrW_cons => fdrW (n + 1) m v o l
grind_pattern [ind_grind] fdrK1_some => fdrK1 n v o l (some (ra, m1))
grind_pattern [ind_grind] fdrK2_no => fdrK2 n v o l (some (rb, m2))
grind_pattern [ind_grind] fdrK2_yes => fdrK2 n v o l (some (rb, m2))
grind_pattern [ind_grind] resK_some => resK (some (r, m))
grind_pattern [ind_grind] iarW_nil => iarW (n + 1) m v o l
grind_pattern [ind_grind] iarW_cons => iarW (n + 1) m v o l
grind_pattern [ind_grind] iarK_no => iarK n v o l (some (rb, m2))
grind_pattern [ind_grind] iarK_yes => iarK n v o l (some (rb, m2))
grind_pattern [ind_grind] resK'_some => resK' (some (r, m))

section spec
variable (p : Prog)

theorem fdrW_spec (hp : p.lookup "field_doms_resolve" = some fieldDomsResolveL) (hftd : FtdF p) (hcr : CrfF p)
    (n : Nat) :
    ∀ (s₀ : St) (v o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "field_doms_resolve" [v, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ fdrW n s₀.mem v o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ v o l; rw [invoke_eq _ hp]; simp only [callFn, fieldDomsResolveL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ v o l
    rw [invoke_eq _ hp]
    simp only [callFn, fieldDomsResolveL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ftdF_spec0 p hftd n, crfF_spec p hcr n, ih] <;>
      finish (gen := 20)

theorem iarW_spec (hp : p.lookup "idx_args_resolve" = some idxArgsResolveL) (hcr : CrfF p) (n : Nat) :
    ∀ (s₀ : St) (v o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "idx_args_resolve" [v, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ iarW n s₀.mem v o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ v o l; rw [invoke_eq _ hp]; simp only [callFn, idxArgsResolveL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ v o l
    rw [invoke_eq _ hp]
    simp only [callFn, idxArgsResolveL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        crfF_spec p hcr n, ih] <;>
      finish (gen := 20)

end spec

/-! ## The relational lemmas -/

theorem toNat_succ_of_lt {o l : Word} (hb : o.toNat + l.toNat < 2 ^ 64) (hl : l ≠ 0) :
    (o + 1).toNat + (l - 1).toNat = o.toNat + l.toNat ∧ (o + 1).toNat = o.toNat + 1 := by
  have hl1 : 1 ≤ l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
    · omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hlm : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hl1))]; simp
  omega

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_proj_arg_p`: `t.j` -/

/-- After `mk_proj`. -/
def spaK2 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (e, m2) => some ([e], m2)
/-- After `intern_bvar`. -/
def spaK (T j : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m1) => spaK2 (mkProjW m1 T j b)
/-- **The model of `struct_proj_arg_p`.** -/
def spaW (m : Mem) (T j : Word) : Option (List Word × Mem) := spaK T j (binternW m 0)

theorem spaK_some (T j b : Word) (m1 : Mem) : spaK T j (some (b, m1)) = spaK2 (mkProjW m1 T j b) := rfl
theorem spaK2_some (e : Word) (m2 : Mem) : spaK2 (some (e, m2)) = some ([e], m2) := rfl
grind_pattern [ind_grind] spaK_some => spaK T j (some (b, m1))
grind_pattern [ind_grind] spaK2_some => spaK2 (some (e, m2))

theorem spaW_spec (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
    (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
    (hp : p.lookup "struct_proj_arg_p" = some structProjArgPL) (n : Nat) (s₀ : St) (T j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_arg_p" [T, j]
    ⦃fun r s' => LocEq s' s₀ ∧ spaW s₀.mem T j = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structProjArgPL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        internBVar_spec p hpf hpp hib n, mkProj_spec p hd hjf hjp hji hmp n] <;>
      finish [spaW]

/-- **`struct_proj_arg_p` refines `structProjArgP`** under the stage relation. -/
@[refines ConRon.Arena.structProjArgP]
theorem structProjArgP_refines (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
    (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
    (hp : p.lookup "struct_proj_arg_p" = some structProjArgPL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (T j : Word)
    (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_arg_p" [T, j]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjArgP (decI T) j.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (structProjArgP (decI T) j.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      AM.res (structProjArgP (decI T) j.toNat) a₀ = decE (r.headD 0); ⊤⦄ := by
  refine triple_post (spaW_spec p hd hpf hpp hib hjf hjp hji hmp hp n s₀ T j) ?_
  rintro r s' ⟨hl, hm⟩
  simp only [spaW] at hm
  obtain ⟨b, m1, h1, hm⟩ := kSome_inv hm rfl (fun _ _ => rfl)
  rw [spaK_some] at hm
  obtain ⟨e, m2, h2, hm⟩ := kSome_inv hm rfl (fun _ _ => rfl)
  rw [spaK2_some] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨a1, hr1, hS1, hg1⟩ := internBVar_stage hS 0 h1
  obtain ⟨a2, hr2, hS2, hg2⟩ := mkProj_stage hS1 T j b h2
  have hrun : (structProjArgP (decI T) j.toNat).run a₀ = .ok (decE e, a2) := by
    simp only [structProjArgP, StateT.run_bind]
    rw [show (0 : Word).toNat = 0 from rfl] at hr1
    rw [hr1]
    exact hr2
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS2, hg1.trans hg2, by rw [hres]; rfl⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_ps_at`, `struct_proj_ps`: the spine wrappers -/

/-- **The model of `struct_ps_at`** (the callee runs at the caller's fuel less one). -/
def psAtW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, o, nP => psK3 (psGoW n m o nP nP 0)

theorem psAtW_succ (n : Nat) (m : Mem) (o nP : Word) :
    psAtW (n + 1) m o nP = psK3 (psGoW n m o nP nP 0) := rfl
grind_pattern [ind_grind] psAtW_succ => psAtW (n + 1) m o nP

/-- **The model of `struct_proj_ps`.** -/
def projPsW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, nP => psK3 (psAtW n m 1 nP)

theorem projPsW_succ (n : Nat) (m : Mem) (nP : Word) :
    projPsW (n + 1) m nP = psK3 (psAtW n m 1 nP) := rfl
grind_pattern [ind_grind] projPsW_succ => projPsW (n + 1) m nP

section
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hp : p.lookup "struct_ps_at" = some structPsAtL)
include ha hc hsc hpf hpp hib hg hp

theorem psAtW_spec (n : Nat) (s₀ : St) (o nP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_ps_at" [o, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ psAtW n s₀.mem o nP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structPsAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        structPsAtGo_spec p ha hc hsc hpf hpp hib hg n] <;>
      finish

theorem projPsW_spec (hq : p.lookup "struct_proj_ps" = some structProjPsL) (n : Nat) (s₀ : St)
    (nP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_ps" [nP]
    ⦃fun r s' => LocEq s' s₀ ∧ projPsW n s₀.mem nP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq]
  simp only [callFn, structProjPsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        psAtW_spec p ha hc hsc hpf hpp hib hg hp n] <;>
      finish

end

/-- The model of `struct_ps_at` refines `structPsAt`. -/
theorem psAtW_ok (n : Nat) (m m' : Mem) (a : AState) (o nP : Word) (r : List Word)
    (h : psAtW n m o nP = some (r, m')) (hR : ArenaR m a) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hon : o.toNat + nP.toNat < 2 ^ 64) :
    ∃ xs a', (structPsAt o.toNat nP.toNat).run a = .ok (xs, a') ∧
      ArenaR m' a' ∧ IWGrow m m' ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  cases n with
  | zero => cases h
  | succ n =>
    rw [psAtW_succ] at h
    obtain ⟨r0, m0, hg, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [psK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨xs, a', hrun, hR', hgr, hs, hd, ht⟩ :=
      psGoW_ok n m m0 a o nP nP 0 r0 hg hR hsz hc hon (by simp)
    exact ⟨xs, a', by simpa [structPsAt] using hrun, hR', hgr, hs, by simpa using hd, by simpa using ht⟩

/-- **`struct_ps_at` refines `structPsAt`** under `ArenaR`. -/
@[refines ConRon.Arena.structPsAt]
theorem structPsAt_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
    (hp : p.lookup "struct_ps_at" = some structPsAtL) (n : Nat) (s₀ : St) (a₀ : AState)
    (o nP : Word) (hR : ArenaR s₀.mem a₀) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hc2 : 200 < (s₀.mem.arr64 CTL).size) (hon : o.toNat + nP.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_ps_at" [o, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structPsAt o.toNat nP.toNat) a₀ ∧
      ArenaR s'.mem (AM.st (structPsAt o.toNat nP.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structPsAt o.toNat nP.toNat) a₀); ⊤⦄ := by
  refine triple_post (psAtW_spec p ha hc hsc hpf hpp hib hg hp n s₀ o nP) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', hrun, hR', hgr, -, hd, -⟩ := psAtW_ok n _ _ _ _ _ _ hm hR hsz hc2 hon
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hR', hgr, by rw [hres]; exact hd⟩

/-- **`struct_proj_ps` refines `structProjPs`** under `ArenaR`. -/
@[refines ConRon.Arena.structProjPs]
theorem structProjPs_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
    (hp : p.lookup "struct_ps_at" = some structPsAtL)
    (hq : p.lookup "struct_proj_ps" = some structProjPsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (nP : Word) (hR : ArenaR s₀.mem a₀) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hc2 : 200 < (s₀.mem.arr64 CTL).size) (hon : 1 + nP.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_ps" [nP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjPs nP.toNat) a₀ ∧
      ArenaR s'.mem (AM.st (structProjPs nP.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structProjPs nP.toNat) a₀); ⊤⦄ := by
  refine triple_post (projPsW_spec p ha hc hsc hpf hpp hib hg hp hq n s₀ nP) ?_
  rintro r s' ⟨hl, hm⟩
  cases n with
  | zero => cases hm
  | succ n =>
  rw [projPsW_succ] at hm
  obtain ⟨r0, m0, h1, hm⟩ := kSome_inv hm rfl (fun _ _ => rfl)
  rw [psK3_some] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨xs, a', hrun, hR', hgr, -, hd, -⟩ := psAtW_ok n _ _ _ _ _ _ h1 hR hsz hc2 (by simpa using hon)
  have hrun' : (structProjPs nP.toNat).run a₀ = .ok (xs, a') := by simpa [structProjPs] using hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  exact ⟨hl, hok, by rw [hst]; exact hR', hgr, by rw [hres]; simpa using hd⟩

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `whnf_telescope` -/

/-- After `sl_cons`: the slice and the sort. -/
def wtK6 (s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ro, m5) => some ([ro.headD 0, ro.tail.headD 0, s], m5)

mutual
/-- **The model of `whnf_telescope`.** -/
def wtW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, i, n, e => wtK1 cR k vis i n (cR k "whnf_top" [vis, i, e] m)
/-- After `whnf`: the view. -/
def wtK1 (cR : CallM) (k : Nat) (vis i n : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => wtK2 cR k vis i n m1 (eViewW m1 (r1.headD 0))
/-- The view's arms. -/
def wtK2 (cR : CallM) (k : Nat) (vis i n : Word) (m1 : Mem) (v : List Word) : Option (List Word × Mem) :=
  if v.headD 0 = 2 ∧ n = 0 then some ([0, 0, v.tail.headD 0], m1)
  else if v.headD 0 = 6 ∧ n ≠ 0 then
    wtK3 cR k vis i n (v.tail.headD 0) (v.tail.tail.headD 0) (fvinternW m1 i (v.tail.headD 0))
  else none
/-- After `intern_fvar`. -/
def wtK3 (cR : CallM) (k : Nat) (vis i n x y : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (fv, m2) =>
    if 4294967296 ≤ fv then none
    else wtK4 cR k vis i n x (i1F m2 [CWF, y, fv, 0])
/-- After `instantiate1_fast`: the recursion. -/
def wtK4 (cR : CallM) (k : Nat) (vis i n x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m3) => wtK5 k x (wtW cR k m3 vis (i + 1) (n - 1) (rb.headD 0))
/-- After the recursion: the cons. -/
def wtK5 (k : Nat) (x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m4) => wtK6 (rr.tail.tail.headD 0) (consW k m4 x (rr.headD 0) (rr.tail.headD 0))
end

section arms
variable (cR : CallM) (k : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis i n e x y s fv : Word) (v r1 rb rr ro : List Word)
theorem wtK2_none (h1 : ¬ (v.headD 0 = 2 ∧ n = 0)) (h2 : ¬ (v.headD 0 = 6 ∧ n ≠ 0)) :
    wtK2 cR k vis i n m1 v = none := by simp only [wtK2, ite_eq_right h1, ite_eq_right h2]
theorem wtK3_big (h : 4294967296 ≤ fv) : wtK3 cR k vis i n x y (some (fv, m2)) = none := by
  simp [wtK3, h]
end arms

grind_pattern [ind_grind] wtK2_none => wtK2 cR k vis i n m1 v
grind_pattern [ind_grind] wtK3_big => wtK3 cR k vis i n x y (some (fv, m2))
local notation "V" => ConLeche.CheckMode.verified

/-! ### The twin, one level unfolded

`whnfTelescope` is structural recursion that matches under a bind, so Lean generates no equation
lemma for it (PLAN.md's vcgen gaps). `wtArm` is its body after the view, and `whnfTelescope_eq`
the unfolding, by `Nat.brecOn` and a case split on the view. -/

/-- The arms of `whnfTelescope` after the view. -/
def wtArm (mode : ConLeche.CheckMode) (fe : IFEnv) (i : Nat) :
    ENodeView → Nat → AM (List EIdx × LIdx)
  | .sort s, 0 => pure ([], s)
  | .sort _, _ + 1 => fail (.invalid "direct sum: type former does not reduce to a telescope")
  | .forallE _ _, 0 => fail (.invalid "direct sum: type former does not reduce to a sort")
  | .forallE dom body, n + 1 => do
      let fv ← internE (.fvar i dom)
      let b ← instantiate1Fast coreWalkFuel body fv 0
      let x ← whnfTelescope mode fe (i + 1) n b
      pure (dom :: x.1, x.2)
  | _, 0 => fail (.invalid "direct sum: type former does not reduce to a sort")
  | _, _ + 1 => fail (.invalid "direct sum: type former does not reduce to a telescope")

theorem whnfTelescope_eq (mode : ConLeche.CheckMode) (fe : IFEnv) (i n : Nat) (e : EIdx) :
    whnfTelescope mode fe i n e = (do
      let e' ← whnf mode fe checkFuel i e
      let v ← view e'
      wtArm mode fe i v n) := by
  cases n <;>
  · delta whnfTelescope
    dsimp only [Nat.brecOn, Nat.brecOn.go, whnfTelescope._f]
    refine congrArg (whnf mode fe checkFuel i e >>= ·) (funext fun e' => ?_)
    refine congrArg (view e' >>= ·) (funext fun v => ?_)
    cases v <;> first | rfl |
      (simp only [wtArm]; delta whnfTelescope; dsimp only [Nat.brecOn, Nat.brecOn.go])

end L.Ind

end
