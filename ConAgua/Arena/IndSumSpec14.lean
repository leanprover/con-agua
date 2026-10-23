import ConAgua.Arena.IndSumSpec12
import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.IndSumSpec6
import ConAgua.Arena.DeclHeader
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndSumSpec2C

/-!
# `check_struct_proj_table` refines `checkStructProjTable` (lane `indproofs2`)

Stage 5, the projection table: the bodies (`struct_proj_bodies`), their scoping
(`check_struct_proj_table_scoped`, the twin's `bodies.toList.allM`, through four stubs), the
reserved name (`proj_table_name`, a stub), its absence (`env_find`), the three lists copied into
`EREC` (`er_from_iw`, plumbing with no twin: the copy decodes as the list), the 14-word `projInfo`
record (`decTbl`), and the push (`env_push`, lane `decls2`'s).
-/


noncomputable section

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
    {m m' : Mem} {o l : Word} {r : List Word} {kk : IdxKind} {xs : List (Idx kk)}
    (h : efW n m o l = some (r, m'))
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
      (lbbF m [CWF, nP + 1, b])
/-- After `all_level_params_defined`. -/
def sctK2 (rest : Mem → Option (List Word × Mem)) (vis nP b r1 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => sctK3 rest nP b r1 (r2.headD 0) (crfF m [vis, b])
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
      (hffF m [CWF, rdW (m.arr64 IW) bO])

section arms
variable (rest : Mem → Option (List Word × Mem)) (n : Nat) (m : Mem)
  (vis nP lo ll bO bL b r1 r2 r3 : Word) (r : List Word)
theorem sctW_nil (h : bL = 0) : sctW (n + 1) m vis nP lo ll bO bL = some ([1], m) := by simp [sctW, h]
theorem sctW_cons (h : bL ≠ 0) : sctW (n + 1) m vis nP lo ll bO bL =
    sctK1 (fun m' => sctW n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (hffF m [CWF, rdW (m.arr64 IW) bO]) := by simp [sctW, h]
theorem sctK5_some : sctK5 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem sctK4_yes (h : r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1) :
    sctK4 rest r1 r2 r3 (some (r, m)) = sctK5 (rest m) := by simp only [sctK4]; rw [if_pos h]
theorem sctK4_no (h : ¬ (r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1)) :
    sctK4 rest r1 r2 r3 (some (r, m)) = some ([0], m) := by simp only [sctK4]; rw [if_neg h]
theorem sctK3_some : sctK3 rest nP b r1 r2 (some (r, m)) =
    sctK4 rest r1 r2 (r.headD 0) (lbbF m [CWF, nP + 1, b]) := rfl
theorem sctK2_some : sctK2 rest vis nP b r1 (some (r, m)) =
    sctK3 rest nP b r1 (r.headD 0) (crfF m [vis, b]) := rfl
theorem sctK1_some : sctK1 rest vis nP lo ll b (some (r, m)) =
    sctK2 rest vis nP b (r.headD 0) (stubM "all_level_params_defined" m [lo, ll, b]) := rfl
end arms
attribute [ind_grind] sctW_nil sctW_cons sctK5_some sctK4_yes sctK4_no sctK3_some sctK2_some sctK1_some

theorem sctW_spec (p : Prog) (hb : BvbProg p) (hf : HfF p) (hcr : CrfF p)
    (hp : p.lookup "check_struct_proj_table_scoped" = some checkStructProjTableScopedL) (n : Nat) : ∀ (s₀ : St) (vis nP lo ll bO bL : Word),
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
        hffF_spec p hf n, stubM_spec p "all_level_params_defined" n,
        crfF_spec p hcr n, lbbF_spec p hb n, ih] <;>
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
    decHL m bO.toNat bL.toNat = some bs → bO.toNat + bL.toNat ≤ iwTop m → AbsOK m →
    Sim (sctW n m vis nP lo ll bO bL) (bs.allM (scopeT fe lps nP.toNat)) a
      (fun r b m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 != 0) = b ∧
        (r.headD 0).toNat ≤ 1 ∧ AbsOK m') := by
  induction n with
  | zero => intro m a bO bL bs _ _ _ _ _ _; exact Sim.of_none
  | succ n ih =>
  intro m a bO bL bs hS hlps hlb hbs hbb hA
  by_cases hl : bL = 0
  · rw [sctW_nil (h := hl)]
    have : bs = [] := by
      subst hl; have := decHL_length m hbs; simp at this; exact this
    subst this
    exact Sim.ret ⟨hS, IWGrow.refl _, rfl, by decide, hA⟩
  rw [sctW_cons (h := hl)]
  obtain ⟨w, bs', rfl, hw, hwl, hbs'⟩ := decHL_cons hbs hl (hS.lt64 hbb)
  rw [hw]
  simp only [List.allM, scopeT, bind_assoc, pure_bind]
  have hcwf : CWF.toNat = coreWalkFuel := CWF_eq
  have h1 := hffF_ok dn vis fe CWF w hwl
  rw [hcwf] at h1
  refine Sim.bindK (K := sctK1 _ vis nP lo ll w) rfl (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) (sumSim_of_relW h1 hS) fun _ _ e => (show AFr _ _ from AFr.of_frame (hffF_frame e)) hA)
    fun r1 a1 m1 s1 hQ => ?_
  obtain ⟨⟨hS1, hg1, hb1, hl1⟩, hA1⟩ := hQ
  rw [sctK1_some]
  refine Sim.bindK (K := sctK2 _ vis nP w (r1.headD 0)) rfl (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) (sumSim_of_relAM (allLevelParamsDefined_spec dn vis fe lo ll w hwl lps)
      ⟨hS1, by rw [decHL_grow hg1 hlb]; exact hlps⟩) fun _ _ e => AbsOK.stub (by decide) hA1 e)
    fun r2 a2 m2 s2 hQ => ?_
  obtain ⟨⟨hS2, hg2, hb2, hl2⟩, hA2⟩ := hQ
  rw [sctK2_some]
  refine Sim.bindK (K := sctK3 _ nP w (r1.headD 0) (r2.headD 0)) rfl (fun _ _ => rfl)
    (sumSim_of_relW (crfF_ok dn vis fe w hwl) ⟨hS2, hA2⟩) fun r3 a3 m3 s3 hQ => ?_
  obtain ⟨⟨hS3, hg3, hb3, hl3⟩, hA3⟩ := hQ
  rw [sctK3_some]
  have h4 := lbbF_ok dn vis fe CWF (nP + 1) w hwl
  rw [hcwf, sumToNat_succ (by omega)] at h4
  refine Sim.bindK (K := sctK4 _ (r1.headD 0) (r2.headD 0) (r3.headD 0)) rfl (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) (sumSim_of_relW h4 hS3) fun _ _ e => (show AFr _ _ from AFr.of_frame (lbbF_frame e)) hA3)
    fun r4 a4 m4 s4 hQ => ?_
  obtain ⟨⟨hS4, hg4, hb4, hl4⟩, hA4⟩ := hQ
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
        (by have := hg14.1; omega) (by rw [decHL_grow hg14 hb1']; exact hbs') (by have := hg14.1; omega) hA4)
      fun r b m' a' hQ => ⟨hQ.1, hg14.trans hQ.2.1, by simpa using hQ.2.2.1, by simpa using hQ.2.2.2.1,
        hQ.2.2.2.2⟩
  · rw [sctK4_no (h := hc)]
    have ht : (!a1 && a2 && a3 && a4) = false := by
      cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> simp_all
    simp only [ht]
    exact Sim.ret ⟨hS4, hg14, rfl, by decide, hA4⟩


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
    else tblK3 p n vis T lo ll nP C nF rs off go gl bO bL (ptF m [T])
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
      tblK3 p n vis T lo ll nP C nF rs off go gl bO bL (ptF m [T]) := by
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
  hpt : PtF p
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
  hbb : BvbProg p
  hhf : HfF p
  hix : p.lookup "env_ix" = some envIxL
  hrg : p.lookup "env_row_get" = some envRowGetL
  hfind : p.lookup "env_find" = some envFindL
  hea : p.lookup "erec_alloc" = some erecAlloc
  hefg : p.lookup "er_from_iw_go" = some erFromIwGo
  hef : p.lookup "er_from_iw" = some erFromIw
  htbl : p.lookup "check_struct_proj_table" = some checkStructProjTableL
  hrec : RecProg p
  hi1 : I1lF p
  hcr : CrfF p

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
        hP.hpg hP.hgo hP.hps hP.hpj hP.hspb hP.hi1 (n + 1),
      sctW_spec p hP.hbb hP.hhf hP.hcr hP.hsct (n + 1), ptF_spec p hP.hpt (n + 1),
      envFind_specW p hP.hix hP.hrg hP.hfind (n + 1), efW_spec p hP.hea hP.hefg hP.hef n,
      erecAlloc_specW p hP.hea (n + 1), callW_spec p (n + 1) "env_push"] <;>
    finish (gen := 30) (instances := 5000) [tblW, tblMem, rdW_eq]

/-! ## `check_struct_proj_table`: the relation to the twin -/

/-- **The `projInfo` record's decoding**, from its fourteen words and the three copied slices. -/
theorem sumDecTbl {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {tn T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 off : Word} {lps : List NIdx} {bodies : List EIdx}
    {guards : List LIdx}
    (hw : ∀ i < 14, a[q + i]? = [6, tn, T, lo2, ll2, nP, C, nF, rs, bo2, bl2, go2, gl2, off][i]?)
    (htn : H tn) (hT : H T) (hC : H C) (hrs : H rs)
    (hl : hslice? a lo2.toNat ll2.toNat = some lps) (hb : hslice? a bo2.toNat bl2.toNat = some bodies)
    (hg : hslice? a go2.toNat gl2.toNat = some guards) :
    decCI a dn q = some (.projInfo ⟨decI T, decI tn, lps, nP.toNat, decI C, nF.toNat, decI rs,
      bodies.toArray, guards, off.toNat⟩) := by
  have h0 : a[q]? = some 6 := by simpa using hw 0 (by decide)
  have h1 := hw 1 (by decide); have h2 := hw 2 (by decide); have h3 := hw 3 (by decide)
  have h4 := hw 4 (by decide); have h5 := hw 5 (by decide); have h6 := hw 6 (by decide)
  have h7 := hw 7 (by decide); have h8 := hw 8 (by decide); have h9 := hw 9 (by decide)
  have h10 := hw 10 (by decide); have h11 := hw 11 (by decide); have h12 := hw 12 (by decide)
  have h13 := hw 13 (by decide)
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have e3 : q + 3 + 1 = q + 4 := rfl
  have e9 : q + 9 + 1 = q + 10 := rfl
  have e11 : q + 11 + 1 = q + 12 := rfl
  simp only [decCI, decTbl, hlist?, nat?, hd?, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    e3, e9, e11, Option.map_some, Option.bind_eq_bind, Option.bind_some, htn, hT, hC, hrs, if_true,
    hl, hb, hg]
  rfl

/-- **`check_struct_proj_table`'s model refines `checkStructProjTable`**: the view returned relates
the environment with the projection table pushed. -/
theorem tblW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (p : Prog) (hP : TblProg p)
    (n : Nat) (m : Mem) (a : AState) (T C lo ll nP nF rs go gl off cvCaw : Word) (lps : List NIdx)
    (guards : List LIdx) (cvCa : IConstantVal) (hS : StageR dn vis fe m a) (hT : H T) (hC : H C)
    (hrs : H rs) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hgs : decHL m go.toNat gl.toNat = some guards) (hgb : go.toNat + gl.toNat ≤ iwTop m)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) m cvCa) (hA : AbsOK m) :
    Sim (tblW p n m T C lo ll nP nF rs go gl off cvCaw vis)
      (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat (decI rs) guards off.toNat cvCa fe) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m') := by
  unfold tblW checkStructProjTable
  obtain ⟨w, hw, hwl, hwd⟩ := sumTypeWord (DecB.get (OMono.decCVp _) hcv) hS.2.2.2.2.1
  rw [hw, ← hwd]
  -- `struct_proj_bodies`
  refine Sim.bindK (K := tblK1 p n vis T lo ll nP C nF rs off go gl) rfl (fun _ _ => rfl)
    (fun r m' e => by
      obtain ⟨x, a', h1, h2⟩ := spbW_ok dn vis fe (n + 1) m m' a T nP nF w r e hS hwl (by omega)
        nF.toNat_lt hA
      exact ⟨x, a', h1, h2⟩) fun rb ob m1 a1 hQ => ?_
  obtain ⟨hS1, hg1, hdec1, hA1⟩ := hQ
  by_cases h10 : rb.headD 0 = 0
  · rw [tblK1_no (h := h10)]; exact Sim.of_none
  rw [tblK1_yes (h := h10)]
  cases ob with
  | none => exact absurd hdec1 h10
  | some bodies =>
  obtain ⟨-, hbd, hbb⟩ := hdec1
  refine Sim.bind_twin (x := bodies) (a₁ := a1) rfl ?_
  have hlps1 : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow hg1 hlb]; exact hlps
  have hlb1 : lo.toNat + ll.toNat ≤ iwTop m1 := by have := hg1.1; omega
  -- the scoping
  refine Sim.bindK (K := tblK2 p n vis T lo ll nP C nF rs off go gl _ _) rfl (fun _ _ => rfl)
    (sctW_ok nP lo ll lps hnP (n + 1) m1 a1 _ _ bodies.toList hS1 hlps1 hlb1 hbd hbb hA1)
    fun rs' sok m2 a2 hQ => ?_
  obtain ⟨hS2, hg2, hsok, hsl, -⟩ := hQ
  by_cases hlen0 : rb.tail.tail.headD 0 ≠ nF
  · rw [tblK2_len (h := hlen0)]; exact Sim.of_none
  have hlen : rb.tail.tail.headD 0 = nF := Decidable.of_not_not hlen0
  by_cases h10' : rs'.headD 0 ≠ 1
  · rw [tblK2_bad (h := hlen) (h1 := h10')]; exact Sim.of_none
  have h1 : rs'.headD 0 = 1 := Decidable.of_not_not h10'
  rw [tblK2_ok (h := hlen) (h1 := h1)]
  have hsz : bodies.size = nF.toNat := by
    rw [← Array.length_toList, decHL_length m1 hbd, hlen]
  have hsok' : sok = true := (sumB01 hsok hsl).1.mp h1
  subst hsok'
  simp only [hsz, and_self, ite_true]
  -- `proj_table_name`
  refine Sim.bindK (K := tblK3 p n vis T lo ll nP C nF rs off go gl _ _) rfl (fun _ _ => rfl)
    (sumSim_of_relW (ptF_ok dn vis fe T hT) hS2) fun rt tn m3 a3 hQ => ?_
  obtain ⟨hS3, hg3, htnl, htn⟩ := hQ
  subst htn
  rw [tblK3_some]
  -- `env_find`
  cases hf : envFindW m3 (rt.headD 0) vis with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rf, m4⟩ := y
  by_cases hf0 : rf.headD 0 ≠ 0
  · rw [tblK4_found (h := hf0)]; exact Sim.of_none
  have hf0' : rf.headD 0 = 0 := Decidable.of_not_not hf0
  rw [tblK4_free (h := hf0')]
  obtain ⟨hm43, hmiss⟩ := envFindW_miss hf hS3.1.env htnl hf0'
  rw [hm43]
  simp only [hmiss, Option.isNone_none, ite_true]
  -- the three copies
  have hg13 := (hg1.trans hg2).trans hg3
  cases h5 : efW n m3 lo ll with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rl, m5⟩ := y
  obtain ⟨hS5, hg5, hrl1, hrl0, hsl5, ht5⟩ := efW_stage n h5 hS3
    (by rw [decHL_grow hg13 hlb]; exact hlps) (by have := hg13.1; omega)
  rw [tblK5_some]
  have hg25 := (hg2.trans hg3).trans hg5
  cases h6 : efW n m5 (rb.tail.headD 0) (rb.tail.tail.headD 0) with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rb2, m6⟩ := y
  obtain ⟨hS6, hg6, hrb1, hrb0, hsl6, ht6⟩ := efW_stage n h6 hS5
    (by rw [decHL_grow hg25 hbb]; exact hbd) (by have := hg25.1; omega)
  rw [tblK6_some]
  have hg06 := (((hg1.trans hg2).trans hg3).trans hg5).trans hg6
  cases h7 : efW n m6 go gl with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rg, m7⟩ := y
  obtain ⟨hS7, hg7, hrg1, hrg0, hsl7, ht7⟩ := efW_stage n h7 hS6
    (by rw [decHL_grow hg06 hgb]; exact hgs) (by have := hg06.1; omega)
  rw [tblK7_some]
  -- the record
  cases h8 : erAllocW m7 14 with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨q, m8⟩ := y
  rw [tblK8_some, tblMem_eq]
  obtain ⟨hSM, hgM, hq, htM, hget⟩ := erRec_stage h8 hS7
    [6, rt.headD 0, T, rl.headD 0, rl.tail.headD 0, nP, C, nF, rs, rb2.headD 0, rb2.tail.headD 0,
      rg.headD 0, rg.tail.headD 0, off] rfl
  generalize hM : wrER m8 q _ = M at hSM hgM htM hget
  have hPE : ∀ i < 14, (erecP M)[q.toNat + i]? = (M.arr64 EREC)[q.toNat + i]? :=
    fun i hi => erecP_getE (by simp at htM; omega)
  have he6 := IWGrow.erecPExtR (hg6.trans hg7 |>.trans hgM)
  have he7 := IWGrow.erecPExtR (hg7.trans hgM)
  have he5 := IWGrow.erecPExtR ((hg6.trans hg7).trans hgM)
  have hci := sumDecTbl (a := erecP M) (dn := dn) (q := q.toNat)
    (fun i hi => by rw [hPE i hi, hget i (by simpa using hi)]) htnl hT hC hrs
    (by rw [hrl1]; exact ArrExt.hslice? he5 hsl5) (by rw [hrb1]; exact ArrExt.hslice? he7 hsl6)
    (by rw [hrg1]; exact ArrExt.hslice? (IWGrow.erecPExtR hgM) hsl7)
  -- `env_push`
  have hq1 : (rdW (M.arr64 EREC) (q + 1)).toNat < 2 ^ 32 := by
    have h1 := hget 1 (by simp)
    have hlt : q.toNat + 1 < (M.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp (by simpa using h1)).1
    rw [rdW_of_get? (by rw [sumToNat_succ (by have := hSM.2.2.2.2.1; omega)]) (by simpa using h1)]
    simpa using htnl
  cases hc : callW p (n + 1) "env_push" [vis, q] M with
  | none => exact Sim.of_none
  | some y =>
  obtain ⟨rv, m9⟩ := y
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨M, Locals.init []⟩)
    (envPush_specW p hP.hrec (n + 1) ⟨M, Locals.init []⟩ vis q hq1) hc
  subst hs4
  obtain ⟨hS9, hg9⟩ := envPushW_ok hW4 hSM hci
  rw [tblK9_some]
  refine Sim.ret ⟨by simpa using hS9, ?_⟩
  exact ((((((hg1.trans hg2).trans hg3).trans hg5).trans hg6).trans hg7).trans hgM).trans hg9


/-- **`check_struct_proj_table` refines `checkStructProjTable`** (through the stubs
`proj_table_name`, `has_fvar_fast`, `all_level_params_defined`, `consts_resolve_ffast`,
`loose_bvars_bounded_fast`, and `struct_proj_bodies`' `inst_pis_at_lift`,
`instantiate1_lift_fast`, with the walk memos `AbsOK`): from the stage relation at `vis` of `fe`, the level parameters and the
guards decoded below the pool's top and the constructor below the record pool's top, a returning run
returns the view of `fe` with the `projInfo` table pushed. -/
@[refines ConRon.Arena.checkStructProjTable]
theorem checkStructProjTable_refines (p : Prog) (hP : TblProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (T C lo ll nP nF rs go gl off cvCaw vis : Word)
    (lps : List NIdx) (guards : List LIdx) (cvCa : IConstantVal) (hS : StageR dn vis fe s₀.mem a₀)
    (hT : H T) (hC : H C) (hrs : H rs) (hnP : nP.toNat + 1 < 2 ^ 64)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hgs : decHL s₀.mem go.toNat gl.toNat = some guards) (hgb : go.toNat + gl.toNat ≤ iwTop s₀.mem)
    (hcv : DecB (fun m => decCVp m cvCaw.toNat) s₀.mem cvCa) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_struct_proj_table"
      [T, C, lo, ll, nP, nF, rs, go, gl, off, cvCaw, vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat (decI rs) guards off.toNat
        cvCa fe) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkStructProjTable (decI T) (decI C) lps nP.toNat nF.toNat
        (decI rs) guards off.toNat cvCa fe) a₀) s'.mem (AM.st (checkStructProjTable (decI T) (decI C)
          lps nP.toNat nF.toNat (decI rs) guards off.toNat cvCa fe) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (tblW_spec p hP n s₀ T C lo ll nP nF rs go gl off cvCaw vis) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hS', hg'⟩ := (tblW_ok p hP n _ a₀ T C lo ll nP nF rs go gl off cvCaw lps guards cvCa hS hT
    hC hrs hnP hlps hlb hgs hgb hcv hA).run hm
  exact ⟨hl, hok, hS', hg'⟩

/-! ## The walk memos across the table's steps -/

theorem efgW_afr : ∀ (n : Nat) (m m' : Mem) (q o l : Word) (r : List Word),
    efgW n m q o l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [efgW] at h
  | n + 1, m, m', q, o, l, r, h => by
    simp only [efgW, efgK.eq_def] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    · refine AFr.trans (set64ER_afr m q (rdW (m.arr64 IW) o)) ?_
      afr_auto h [efgW_afr n _ _ _ _ _ _]

theorem efW_afr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : efW n m o l = some (r, m')) :
    AFr m m' := by
  simp only [efW, efK1.eq_def, efK2.eq_def] at h
  afr_auto h [erAllocW_afr, efgW_afr _ _ _ _ _ _ _]

theorem envPushW_afr {m m' : Mem} {vis q : Word} {r : List Word} (h : envPushW m vis q = some (r, m')) :
    AFr m m' := by
  simp only [envPushW] at h
  split at h; · cases h
  split at h; · cases h
  split at h
  rotate_left
  · cases h
  rename_i hc
  obtain ⟨ht, -⟩ := hc
  have hrow : rowArr (rdW (m.arr64 EREC) (q + 1)) ∈ [132, 133, 134, ECON] := by
    simp only [rowArr, List.mem_cons]
    have : rowTag (rdW (m.arr64 EREC) (q + 1)) = 0 ∨ rowTag (rdW (m.arr64 EREC) (q + 1)) = 1 ∨
        rowTag (rdW (m.arr64 EREC) (q + 1)) = 2 := by omega
    rcases this with h0 | h0 | h0 <;> simp [h0]
  have hne : rowArr (rdW (m.arr64 EREC) (q + 1)) ≠ CTL := by simp only [rowArr, CTL, ArrId]; omega
  have h49 : memoFreeA [rowArr (rdW (m.arr64 EREC) (q + 1))] = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with h | h | h | h <;> rw [h] <;> decide
  have hf1 : AFr m (rowSet m (rdW (m.arr64 EREC) (q + 1)) (vis + 1) q) := by
    unfold rowSet
    exact (AFr.set64 m _ hne h49 _ _).trans (AFr.set64 _ _ hne h49 _ _)
  simp only [envPushK] at h
  split at h; · cases h
  split at h
  rotate_left
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact hf1.trans ((AFr.set64 _ ECON (by decide) (by decide) _ _).trans (AFr.setCtl _ 128 (by decide) _))


end L.Ind
