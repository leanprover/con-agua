import ConAgua.Arena.IndSumSpec10
import ConAgua.Arena.IndSumSpec6
import ConAgua.Arena.DeclHeader

/-!
# `check_struct_proj_table` refines `checkStructProjTable` (lane `indproofs2`)

Stage 5, the projection table: the bodies (`struct_proj_bodies`), their scoping
(`check_struct_proj_table_scoped`, the twin's `bodies.toList.allM`, through four stubs), the
reserved name (`proj_table_name`, a stub), its absence (`env_find`), the three lists copied into
`EREC` (`er_from_iw`, plumbing with no twin: the copy decodes as the list), the 14-word `projInfo`
record (`decTbl`), and the push (`env_push`, lane `decls2`'s).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `er_from_iw` -/

/-- After the rest of the copy. -/
def efgK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

/-- **The model of `er_from_iw_go(q, o, l)`** at exec fuel `n`. -/
def efgW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, o, l =>
    if l = 0 then some ([0], m)
    else efgK (efgW n (m.set64 EREC q (rdW (m.arr64 IW) o)) (q + 1) (o + 1) (l - 1))

theorem efgW_nil (n : Nat) (m : Mem) (q o l : Word) (h : l = 0) : efgW (n + 1) m q o l = some ([0], m) := by
  simp [efgW, h]
theorem efgW_cons (n : Nat) (m : Mem) (q o l : Word) (h : l ≠ 0) : efgW (n + 1) m q o l =
    efgK (efgW n (m.set64 EREC q (rdW (m.arr64 IW) o)) (q + 1) (o + 1) (l - 1)) := by simp [efgW, h]
theorem efgK_some (r : List Word) (m : Mem) : efgK (some (r, m)) = some ([0], m) := rfl
attribute [ind_grind] efgW_nil efgW_cons efgK_some

theorem efgW_spec (p : Prog) (hp : p.lookup "er_from_iw_go" = some erFromIwGo) (n : Nat) :
    ∀ (s₀ : St) (q o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "er_from_iw_go" [q, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ efgW n s₀.mem q o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ q o l; rw [invoke_eq _ hp]; simp only [callFn, erFromIwGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q o l
    rw [invoke_eq _ hp]
    simp only [callFn, erFromIwGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- After the copy. -/
def efK2 (q l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([q, l], m)
/-- After the allocation. -/
def efK1 (n : Nat) (o l : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m) => efK2 q l (efgW n m q o l)
/-- **The model of `er_from_iw(o, l)`** at callee fuel `n`. -/
def efW (n : Nat) (m : Mem) (o l : Word) : Option (List Word × Mem) := efK1 n o l (erAllocW m l)

theorem efK1_some (n : Nat) (o l q : Word) (m : Mem) : efK1 n o l (some (q, m)) = efK2 q l (efgW n m q o l) :=
  rfl
theorem efK2_some (q l : Word) (r : List Word) (m : Mem) : efK2 q l (some (r, m)) = some ([q, l], m) := rfl
attribute [ind_grind] efK1_some efK2_some

theorem efW_spec (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hg : p.lookup "er_from_iw_go" = some erFromIwGo) (hp : p.lookup "er_from_iw" = some erFromIw)
    (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "er_from_iw" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ efW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erFromIw]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, erecAlloc_specW p ha n,
      efgW_spec p hg n] <;>
    finish (gen := 20) [efW]

/-- The copy loop writes the slice's words. -/
theorem efgW_mem (n : Nat) : ∀ (m m' : Mem) (q o l : Word) (r ws : List Word),
    efgW n m q o l = some (r, m') → SlR m o l ws → m' = wrER m q ws := by
  induction n with
  | zero => intro m m' q o l r ws h; simp [efgW] at h
  | succ n ih =>
    intro m m' q o l r ws h hs
    cases hs with
    | nil =>
      rw [efgW_nil n m q o 0 rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    | @cons _ _ ws hl hs =>
      rw [efgW_cons n m q o l hl] at h
      cases h1 : efgW n (m.set64 EREC q (rdW (m.arr64 IW) o)) (q + 1) (o + 1) (l - 1) with
      | none => rw [h1] at h; cases h
      | some x =>
        obtain ⟨r1, m1⟩ := x
        rw [h1, efgK_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        show m1 = wrER (m.set64 EREC q (rdW (m.arr64 IW) o)) (q + 1) ws
        have hI : (m.set64 EREC q (rdW (m.arr64 IW) o)).arr64 IW = m.arr64 IW :=
          Mem.arr64_set64_ne _ _ _ _ _ (by decide)
        exact ih _ _ _ _ _ _ _ h1 (slR_congr hI hs)

/-- Handle words at `q, q + 1, …` decode as the handle list. -/
theorem sumHslice_of_get {k : IdxKind} {a : Array Word} : ∀ (ws : List Word) (q : Nat),
    (∀ j < ws.length, a[q + j]? = ws[j]?) → (∀ w ∈ ws, H w) →
    (hslice? a q ws.length : Option (List (Idx k))) = some (ws.map decI)
  | [], q, _, _ => by simp [hslice?]
  | w :: ws, q, h, hw => by
    simp only [List.length_cons, hslice?_succ, List.map_cons]
    have h0 : a[q]? = some w := by simpa using h 0 (by simp)
    have ih := sumHslice_of_get (k := k) ws (q + 1) (fun j hj => by
      have := h (j + 1) (by simpa using hj); rw [show q + 1 + j = q + (j + 1) by omega]; simpa using this)
      (fun v hv => hw v (by simp [hv]))
    have hw0 : H w := hw w (by simp)
    simp [hd?, h0, hw0, ih]

/-- **`er_from_iw` under the stage relation**: a fresh `EREC` slice (at the old record top) holding
the `IW` list, decoded in the record pool below its new top. -/
theorem efW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (n : Nat)
    {m m' : Mem} {o l : Word} {r : List Word} {xs : List EIdx} (h : efW n m o l = some (r, m'))
    (hS : StageR dn vis fe m a) (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = l ∧ (r.headD 0).toNat = erTop m ∧
      hslice? (erecP m') (r.headD 0).toNat l.toNat = some xs ∧ erTop m' = erTop m + l.toNat := by
  unfold efW at h
  cases hal : erAllocW m l with
  | none => rw [hal] at h; cases h
  | some y =>
  obtain ⟨q, m1⟩ := y
  rw [hal, efK1_some] at h
  cases hc : efgW n m1 q o l with
  | none => rw [hc] at h; cases h
  | some y =>
  obtain ⟨r2, m2⟩ := y
  rw [hc, efK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨ws, hws, rfl, hwl⟩ := slR_of_decHL m _ _ xs hd (hS.lt64 hb)
  simp only [UInt64.ofNat_toNat] at hws
  have hI1 : m1.arr64 IW = m.arr64 IW := by
    simp only [erAllocW] at hal; split at hal; · cases hal
    split at hal; · cases hal
    simp only [Option.some.injEq, Prod.mk.injEq] at hal; obtain ⟨-, rfl⟩ := hal
    simp only [erAllocMem]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hm2 := efgW_mem n m1 m2 q o l r2 ws hc (slR_congr hI1 hws)
  subst hm2
  have hlen := slR_length hws
  obtain ⟨hS', hg, hq, htop, hget⟩ := erRec_stage hal hS ws hlen.symm
  refine ⟨hS', hg, rfl, hq, ?_, by rw [htop, hlen]⟩
  simp only [List.headD_cons]
  rw [← hlen]
  apply sumHslice_of_get ws q.toNat _ hwl
  intro j hj
  rw [erecP_getE (by rw [htop]; omega), hget j hj]

/-! ## `check_struct_proj_table_scoped` -/

/-- After the rest. -/
def sctK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
/-- After `loose_bvars_bounded_fast`: the verdict. -/
def sctK4 (rest : Mem → Option (List Word × Mem)) (r1 r2 r3 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m) => if r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r4.headD 0 = 1 then sctK5 (rest m) else some ([0], m)
/-- After `consts_resolve_ffast`. -/
def sctK3 (rest : Mem → Option (List Word × Mem)) (nP b r1 r2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m) => sctK4 rest r1 r2 (r3.headD 0)
      (stubM "loose_bvars_bounded_fast" m [CWF, nP + 1, b])
/-- After `all_level_params_defined`. -/
def sctK2 (rest : Mem → Option (List Word × Mem)) (vis nP b r1 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => sctK3 rest nP b r1 (r2.headD 0) (stubM "consts_resolve_ffast" m [vis, b])
/-- After `has_fvar_fast`. -/
def sctK1 (rest : Mem → Option (List Word × Mem)) (vis nP lo ll b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => sctK2 rest vis nP b (r1.headD 0) (stubM "all_level_params_defined" m [lo, ll, b])

/-- **The model of `check_struct_proj_table_scoped(vis, nP, lo, ll, bO, bL)`** at exec fuel `n`. -/
def sctW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nP, lo, ll, bO, bL =>
    if bL = 0 then some ([1], m)
    else sctK1 (fun m' => sctW n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (stubM "has_fvar_fast" m [CWF, rdW (m.arr64 IW) bO])

section arms
variable (rest : Mem → Option (List Word × Mem)) (n : Nat) (m : Mem)
  (vis nP lo ll bO bL b r1 r2 r3 : Word) (r : List Word)
theorem sctW_nil (h : bL = 0) : sctW (n + 1) m vis nP lo ll bO bL = some ([1], m) := by simp [sctW, h]
theorem sctW_cons (h : bL ≠ 0) : sctW (n + 1) m vis nP lo ll bO bL =
    sctK1 (fun m' => sctW n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (stubM "has_fvar_fast" m [CWF, rdW (m.arr64 IW) bO]) := by simp [sctW, h]
theorem sctK5_some : sctK5 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem sctK4_yes (h : r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1) :
    sctK4 rest r1 r2 r3 (some (r, m)) = sctK5 (rest m) := by simp only [sctK4]; rw [if_pos h]
theorem sctK4_no (h : ¬ (r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1)) :
    sctK4 rest r1 r2 r3 (some (r, m)) = some ([0], m) := by simp only [sctK4]; rw [if_neg h]
theorem sctK3_some : sctK3 rest nP b r1 r2 (some (r, m)) =
    sctK4 rest r1 r2 (r.headD 0) (stubM "loose_bvars_bounded_fast" m [CWF, nP + 1, b]) := rfl
theorem sctK2_some : sctK2 rest vis nP b r1 (some (r, m)) =
    sctK3 rest nP b r1 (r.headD 0) (stubM "consts_resolve_ffast" m [vis, b]) := rfl
theorem sctK1_some : sctK1 rest vis nP lo ll b (some (r, m)) =
    sctK2 rest vis nP b (r.headD 0) (stubM "all_level_params_defined" m [lo, ll, b]) := rfl
end arms
attribute [ind_grind] sctW_nil sctW_cons sctK5_some sctK4_yes sctK4_no sctK3_some sctK2_some sctK1_some

theorem sctW_spec (p : Prog) (hp : p.lookup "check_struct_proj_table_scoped" = some checkStructProjTableScopedL)
    (n : Nat) : ∀ (s₀ : St) (vis nP lo ll bO bL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_proj_table_scoped" [vis, nP, lo, ll, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧ sctW n s₀.mem vis nP lo ll bO bL = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis nP lo ll bO bL; rw [invoke_eq _ hp]; simp only [callFn, checkStructProjTableScopedL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis nP lo ll bO bL
    rw [invoke_eq _ hp]
    simp only [callFn, checkStructProjTableScopedL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "has_fvar_fast" n, stubM_spec p "all_level_params_defined" n,
        stubM_spec p "consts_resolve_ffast" n, stubM_spec p "loose_bvars_bounded_fast" n, ih] <;>
      finish (gen := 30) (instances := 5000) [rdW_eq]

/-- The twin's per-body scoping test (`checkStructProjTable`'s `allM` body, verbatim). -/
def scopeT (fe : IFEnv) (lps : List NIdx) (nP : Nat) (b : EIdx) : AM Bool := do
  pure (!(← hasFvarFast coreWalkFuel b) &&
    (← allLevelParamsDefined lps b) &&
    (← constsResolveFFast fe b) &&
    (← looseBVarsBoundedFast coreWalkFuel (nP + 1) b))

theorem sumB01 {r : Word} {b : Bool} (h : (r != 0) = b) (hl : r.toNat ≤ 1) :
    (r = 1 ↔ b = true) ∧ (r = 0 ↔ b = false) := by
  subst h
  have : r = 0 ∨ r = 1 := by
    rcases (show r.toNat = 0 ∨ r.toNat = 1 by omega) with h | h
    · exact .inl (UInt64.toNat_inj.mp (by simpa using h))
    · exact .inr (UInt64.toNat_inj.mp (by simpa using h))
  rcases this with rfl | rfl <;> decide

/-- **`check_struct_proj_table_scoped`'s model refines the twin's `bodies.toList.allM`**. -/
theorem sctW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (nP lo ll : Word)
    (lps : List NIdx) (hnP : nP.toNat + 1 < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (bO bL : Word) (bs : List EIdx),
    StageR dn vis fe m a → decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    decHL m bO.toNat bL.toNat = some bs → bO.toNat + bL.toNat ≤ iwTop m →
    Sim (sctW n m vis nP lo ll bO bL) (bs.allM (scopeT fe lps nP.toNat)) a
      (fun r b m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b ∧
        (r.headD 0).toNat ≤ 1) := by
  induction n with
  | zero => intro m a bO bL bs _ _ _ _ _; exact Sim.of_none
  | succ n ih =>
  intro m a bO bL bs hS hlps hlb hbs hbb
  by_cases hl : bL = 0
  · rw [sctW_nil (h := hl)]
    have : bs = [] := by
      subst hl; have := decHL_length m hbs; simp at this; exact this
    subst this
    exact Sim.ret ⟨hS, IWGrow.refl _, rfl, by decide⟩
  rw [sctW_cons (h := hl)]
  obtain ⟨w, bs', rfl, hw, hwl, hbs'⟩ := decHL_cons hbs hl (hS.lt64 hbb)
  rw [hw]
  simp only [List.allM, scopeT, bind_assoc, pure_bind]
  have hcwf : CWF.toNat = coreWalkFuel := CWF_eq
  have h1 := hasFvarFast_spec dn vis fe CWF w hwl
  rw [hcwf] at h1
  refine Sim.bindK (K := sctK1 _ vis nP lo ll w) rfl (fun _ _ => rfl) (sumSim_of_relAM h1 hS)
    fun r1 a1 m1 s1 hQ => ?_
  obtain ⟨hS1, hg1, hb1, hl1⟩ := hQ
  rw [sctK1_some]
  refine Sim.bindK (K := sctK2 _ vis nP w (r1.headD 0)) rfl (fun _ _ => rfl)
    (sumSim_of_relAM (allLevelParamsDefined_spec dn vis fe lo ll w hwl lps)
      ⟨hS1, by rw [decHL_grow hg1 hlb]; exact hlps⟩) fun r2 a2 m2 s2 hQ => ?_
  obtain ⟨hS2, hg2, hb2, hl2⟩ := hQ
  rw [sctK2_some]
  refine Sim.bindK (K := sctK3 _ nP w (r1.headD 0) (r2.headD 0)) rfl (fun _ _ => rfl)
    (sumSim_of_relAM (constsResolveFFast_spec dn vis fe w hwl) hS2) fun r3 a3 m3 s3 hQ => ?_
  obtain ⟨hS3, hg3, hb3, hl3⟩ := hQ
  rw [sctK3_some]
  have h4 := looseBVarsBoundedFast_spec dn vis fe CWF (nP + 1) w hwl
  rw [hcwf, sumToNat_succ (by omega)] at h4
  refine Sim.bindK (K := sctK4 _ (r1.headD 0) (r2.headD 0) (r3.headD 0)) rfl (fun _ _ => rfl)
    (sumSim_of_relAM h4 hS3) fun r4 a4 m4 s4 hQ => ?_
  obtain ⟨hS4, hg4, hb4, hl4⟩ := hQ
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  obtain ⟨-, e1⟩ := sumB01 hb1 hl1
  obtain ⟨e2, -⟩ := sumB01 hb2 hl2
  obtain ⟨e3, -⟩ := sumB01 hb3 hl3
  obtain ⟨e4, -⟩ := sumB01 hb4 hl4
  by_cases hc : r1.headD 0 = 0 ∧ r2.headD 0 = 1 ∧ r3.headD 0 = 1 ∧ r4.headD 0 = 1
  · rw [sctK4_yes (h := hc)]
    have ht : (!a1 && a2 && a3 && a4) = true := by
      rw [e1.mp hc.1, e2.mp hc.2.1, e3.mp hc.2.2.1, e4.mp hc.2.2.2]; rfl
    simp only [ht]
    have hT := hS.lt64 hbb
    have hbL : bL.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
    have hb1' : (bO + 1).toNat + (bL - 1).toNat ≤ iwTop m := by
      rw [sumToNat_succ (by omega), sumToNat_pred hl]; omega
    refine sumSim_map (K := sctK5) rfl (fun _ _ => rfl)
      (ih m4 s4 (bO + 1) (bL - 1) bs' hS4 (by rw [decHL_grow hg14 hlb]; exact hlps)
        (by have := hg14.1; omega) (by rw [decHL_grow hg14 hb1']; exact hbs') (by have := hg14.1; omega))
      fun r b m' a' hQ => ⟨hQ.1, hg14.trans hQ.2.1, by simpa using hQ.2.2.1, by simpa using hQ.2.2.2⟩
  · rw [sctK4_no (h := hc)]
    have ht : (!a1 && a2 && a3 && a4) = false := by
      cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> simp_all
    simp only [ht]
    exact Sim.ret ⟨hS4, hg14, rfl, by decide⟩


/-! ## `check_struct_proj_table`: the word model -/

/-- The memory after the `projInfo` record's fourteen writes. -/
def tblMem (m : Mem) (q tn T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 off : Word) : Mem :=
  (((((((((((((m.set64 EREC q 6).set64 EREC (q + 1) tn).set64 EREC (q + 2) T).set64 EREC (q + 3) lo2
    ).set64 EREC (q + 4) ll2).set64 EREC (q + 5) nP).set64 EREC (q + 6) C).set64 EREC (q + 7) nF
    ).set64 EREC (q + 8) rs).set64 EREC (q + 9) bo2).set64 EREC (q + 10) bl2).set64 EREC (q + 11) go2
    ).set64 EREC (q + 12) gl2).set64 EREC (q + 13) off

theorem tblMem_eq (m : Mem) (q tn T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 off : Word) :
    tblMem m q tn T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 off =
      wrER m q [6, tn, T, lo2, ll2, nP, C, nF, rs, bo2, bl2, go2, gl2, off] := by
  simp only [tblMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl,
    show q + 9 + 1 = q + 10 by ac_rfl, show q + 10 + 1 = q + 11 by ac_rfl,
    show q + 11 + 1 = q + 12 by ac_rfl, show q + 12 + 1 = q + 13 by ac_rfl]

/-- After `env_push`. -/
def tblK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) => some ([rv.headD 0], m)
/-- After the record's allocation: the writes, the push. -/
def tblK8 (p : Prog) (n : Nat) (vis tn T nP C nF rs off lo2 ll2 bo2 bl2 go2 gl2 : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m) => tblK9 (callW p (n + 1) "env_push" [vis, q]
      (tblMem m q tn T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 off))
/-- After the guards' copy. -/
def tblK7 (p : Prog) (n : Nat) (vis tn T nP C nF rs off lo2 ll2 bo2 bl2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rg, m) => tblK8 p n vis tn T nP C nF rs off lo2 ll2 bo2 bl2 (rg.headD 0) (rg.tail.headD 0)
      (erAllocW m 14)
/-- After the bodies' copy. -/
def tblK6 (p : Prog) (n : Nat) (vis tn T nP C nF rs off go gl lo2 ll2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m) => tblK7 p n vis tn T nP C nF rs off lo2 ll2 (rb.headD 0) (rb.tail.headD 0)
      (efW n m go gl)
/-- After the level parameters' copy. -/
def tblK5 (p : Prog) (n : Nat) (vis tn T nP C nF rs off go gl bO bL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rl, m) => tblK6 p n vis tn T nP C nF rs off go gl (rl.headD 0) (rl.tail.headD 0)
      (efW n m bO bL)
/-- After `env_find`: the name must be free. -/
def tblK4 (p : Prog) (n : Nat) (vis tn T lo ll nP C nF rs off go gl bO bL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m) => if rf.headD 0 ≠ 0 then none
    else tblK5 p n vis tn T nP C nF rs off go gl bO bL (efW n m lo ll)
/-- After `proj_table_name`. -/
def tblK3 (p : Prog) (n : Nat) (vis T lo ll nP C nF rs off go gl bO bL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m) => tblK4 p n vis (rt.headD 0) T lo ll nP C nF rs off go gl bO bL
      (envFindW m (rt.headD 0) vis)
/-- After the scoping check. -/
def tblK2 (p : Prog) (n : Nat) (vis T lo ll nP C nF rs off go gl bO bL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs', m) => if bL ≠ nF then none else if rs'.headD 0 ≠ 1 then none
    else tblK3 p n vis T lo ll nP C nF rs off go gl bO bL (stubM "proj_table_name" m [T])
/-- After `struct_proj_bodies`. -/
def tblK1 (p : Prog) (n : Nat) (vis T lo ll nP C nF rs off go gl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m) => if rb.headD 0 = 0 then none
    else tblK2 p n vis T lo ll nP C nF rs off go gl (rb.tail.headD 0) (rb.tail.tail.headD 0)
      (sctW (n + 1) m vis nP lo ll (rb.tail.headD 0) (rb.tail.tail.headD 0))

/-- **The model of `check_struct_proj_table(T, C, lo, ll, nP, nF, rs, go, gl, off, cvCa, vis)`**
(its callees at exec fuel `n + 1`). -/
def tblW (p : Prog) (n : Nat) (m : Mem) (T C lo ll nP nF rs go gl off cvCa vis : Word) :
    Option (List Word × Mem) :=
  tblK1 p n vis T lo ll nP C nF rs off go gl (spbW (n + 1) m T nP nF (rdW (m.arr64 EREC) (cvCa + 3)))

section arms
variable (p : Prog) (n : Nat) (m : Mem)
  (vis tn T lo ll nP C nF rs off go gl bO bL lo2 ll2 bo2 bl2 go2 gl2 q : Word) (r : List Word)
theorem tblK9_some : tblK9 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem tblK8_some : tblK8 p n vis tn T nP C nF rs off lo2 ll2 bo2 bl2 go2 gl2 (some (q, m)) =
    tblK9 (callW p (n + 1) "env_push" [vis, q]
      (tblMem m q tn T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 off)) := rfl
theorem tblK7_some : tblK7 p n vis tn T nP C nF rs off lo2 ll2 bo2 bl2 (some (r, m)) =
    tblK8 p n vis tn T nP C nF rs off lo2 ll2 bo2 bl2 (r.headD 0) (r.tail.headD 0) (erAllocW m 14) := rfl
theorem tblK6_some : tblK6 p n vis tn T nP C nF rs off go gl lo2 ll2 (some (r, m)) =
    tblK7 p n vis tn T nP C nF rs off lo2 ll2 (r.headD 0) (r.tail.headD 0) (efW n m go gl) := rfl
theorem tblK5_some : tblK5 p n vis tn T nP C nF rs off go gl bO bL (some (r, m)) =
    tblK6 p n vis tn T nP C nF rs off go gl (r.headD 0) (r.tail.headD 0) (efW n m bO bL) := rfl
theorem tblK4_found (h : r.headD 0 ≠ 0) :
    tblK4 p n vis tn T lo ll nP C nF rs off go gl bO bL (some (r, m)) = none := by
  simp only [tblK4]; rw [if_pos h]
theorem tblK4_free (h : r.headD 0 = 0) :
    tblK4 p n vis tn T lo ll nP C nF rs off go gl bO bL (some (r, m)) =
      tblK5 p n vis tn T nP C nF rs off go gl bO bL (efW n m lo ll) := by
  simp only [tblK4]; rw [if_neg ((fun e => e h))]
theorem tblK3_some : tblK3 p n vis T lo ll nP C nF rs off go gl bO bL (some (r, m)) =
    tblK4 p n vis (r.headD 0) T lo ll nP C nF rs off go gl bO bL (envFindW m (r.headD 0) vis) := rfl
theorem tblK2_len (h : bL ≠ nF) :
    tblK2 p n vis T lo ll nP C nF rs off go gl bO bL (some (r, m)) = none := by
  simp only [tblK2]; rw [if_pos h]
theorem tblK2_bad (h : bL = nF) (h1 : r.headD 0 ≠ 1) :
    tblK2 p n vis T lo ll nP C nF rs off go gl bO bL (some (r, m)) = none := by
  simp only [tblK2]; rw [if_neg ((fun e => e h)), if_pos h1]
theorem tblK2_ok (h : bL = nF) (h1 : r.headD 0 = 1) :
    tblK2 p n vis T lo ll nP C nF rs off go gl bO bL (some (r, m)) =
      tblK3 p n vis T lo ll nP C nF rs off go gl bO bL (stubM "proj_table_name" m [T]) := by
  simp only [tblK2]; rw [if_neg ((fun e => e h)), if_neg ((fun e => e h1))]
theorem tblK1_no (h : r.headD 0 = 0) :
    tblK1 p n vis T lo ll nP C nF rs off go gl (some (r, m)) = none := by
  simp only [tblK1]; rw [if_pos h]
theorem tblK1_yes (h : r.headD 0 ≠ 0) :
    tblK1 p n vis T lo ll nP C nF rs off go gl (some (r, m)) =
      tblK2 p n vis T lo ll nP C nF rs off go gl (r.tail.headD 0) (r.tail.tail.headD 0)
        (sctW (n + 1) m vis nP lo ll (r.tail.headD 0) (r.tail.tail.headD 0)) := by
  simp only [tblK1]; rw [if_neg h]
end arms
attribute [ind_grind] tblK9_some tblK8_some tblK7_some tblK6_some tblK5_some tblK4_found tblK4_free
  tblK3_some tblK2_len tblK2_bad tblK2_ok tblK1_no tblK1_yes

/-- The program lookups of `check_struct_proj_table`. -/
structure TblProg (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hsc : p.lookup "sl_cons" = some slCons
  hv : p.lookup "e_view" = some eView
  hd : p.lookup "der_b" = some derB
  hpf : p.lookup "bvar_find" = some bvarFind
  hpp : p.lookup "bvar_push" = some bvarPush
  hib : p.lookup "intern_bvar" = some internBVar
  hjf : p.lookup "proj_find" = some projFind
  hjp : p.lookup "proj_push" = some projPush
  hji : p.lookup "intern_proj" = some internProj
  hmp : p.lookup "mk_proj" = some mkProj
  hap : p.lookup "struct_proj_arg_p" = some structProjArgPL
  hpg : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL
  hgo : p.lookup "struct_ps_at_go" = some structPsAtGoL
  hps : p.lookup "struct_ps_at" = some structPsAtL
  hpj : p.lookup "struct_proj_ps" = some structProjPsL
  hspb : p.lookup "struct_proj_bodies" = some structProjBodiesL
  hsct : p.lookup "check_struct_proj_table_scoped" = some checkStructProjTableScopedL
  hix : p.lookup "env_ix" = some envIxL
  hrg : p.lookup "env_row_get" = some envRowGetL
  hfind : p.lookup "env_find" = some envFindL
  hea : p.lookup "erec_alloc" = some erecAlloc
  hefg : p.lookup "er_from_iw_go" = some erFromIwGo
  hef : p.lookup "er_from_iw" = some erFromIw
  htbl : p.lookup "check_struct_proj_table" = some checkStructProjTableL

set_option maxHeartbeats 4000000 in
theorem tblW_spec (p : Prog) (hP : TblProg p) (n : Nat) (s₀ : St)
    (T C lo ll nP nF rs go gl off cvCa vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_struct_proj_table"
      [T, C, lo, ll, nP, nF, rs, go, gl, off, cvCa, vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      tblW p n s₀.mem T C lo ll nP nF rs go gl off cvCa vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.htbl]
  simp only [callFn, checkStructProjTableL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      spbW_spec p hP.ha hP.hc hP.hsc hP.hv hP.hd hP.hpf hP.hpp hP.hib hP.hjf hP.hjp hP.hji hP.hmp hP.hap
        hP.hpg hP.hgo hP.hps hP.hpj hP.hspb (n + 1),
      sctW_spec p hP.hsct (n + 1), stubM_spec p "proj_table_name" (n + 1),
      envFind_specW p hP.hix hP.hrg hP.hfind (n + 1), efW_spec p hP.hea hP.hefg hP.hef n,
      erecAlloc_specW p hP.hea (n + 1), callW_spec p (n + 1) "env_push"] <;>
    finish (gen := 30) (instances := 5000) [tblW, tblMem, rdW_eq]

end L.Ind
