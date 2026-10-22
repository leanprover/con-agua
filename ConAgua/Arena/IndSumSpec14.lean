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

end L.Ind
