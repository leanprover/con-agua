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
structure stored (`env_find`), its table not taken (`find_table`), the three lists copied into
`EREC` (`er_from_iw`, plumbing with no twin: the copy decodes as the list), the 13-word table
record (`decTbl`), and the push (`env_push_table`).
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
      obtain ⟨r1, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [efgK_some] at h
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
  obtain ⟨q, m1, hal, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [efK1_some] at h
  obtain ⟨r2, m2, hc, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [efK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
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
def sctK1 (c : CallM) (n : Nat) (rest : Mem → Option (List Word × Mem)) (vis nP lo ll b : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => sctK2 rest vis nP b (r1.headD 0) (c n "all_level_params_defined" [lo, ll, b] m)

/-- **The model of `check_struct_proj_table_scoped(vis, nP, lo, ll, bO, bL)`** at exec fuel `n`,
reading `all_level_params_defined` through `c` (`stubCall`: the stub contract; `realCall p`: the
program's own call, `IndRealSctC.lean`). -/
def sctW (c : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nP, lo, ll, bO, bL =>
    if bL = 0 then some ([1], m)
    else sctK1 c n (fun m' => sctW c n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (hffF m [CWF, rdW (m.arr64 IW) bO])

section arms
variable (c : CallM) (rest : Mem → Option (List Word × Mem)) (n : Nat) (m : Mem)
  (vis nP lo ll bO bL b r1 r2 r3 : Word) (r : List Word)
theorem sctW_nil (h : bL = 0) : sctW c (n + 1) m vis nP lo ll bO bL = some ([1], m) := by simp [sctW, h]
theorem sctW_cons (h : bL ≠ 0) : sctW c (n + 1) m vis nP lo ll bO bL =
    sctK1 c n (fun m' => sctW c n m' vis nP lo ll (bO + 1) (bL - 1)) vis nP lo ll (rdW (m.arr64 IW) bO)
      (hffF m [CWF, rdW (m.arr64 IW) bO]) := by simp [sctW, h]
theorem sctK5_some : sctK5 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem sctK4_yes (h : r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1) :
    sctK4 rest r1 r2 r3 (some (r, m)) = sctK5 (rest m) := by simp only [sctK4]; rw [ite_eq_left h]
theorem sctK4_no (h : ¬ (r1 = 0 ∧ r2 = 1 ∧ r3 = 1 ∧ r.headD 0 = 1)) :
    sctK4 rest r1 r2 r3 (some (r, m)) = some ([0], m) := by simp only [sctK4]; rw [ite_eq_right h]
theorem sctK3_some : sctK3 rest nP b r1 r2 (some (r, m)) =
    sctK4 rest r1 r2 (r.headD 0) (lbbF m [CWF, nP + 1, b]) := rfl
theorem sctK2_some : sctK2 rest vis nP b r1 (some (r, m)) =
    sctK3 rest nP b r1 (r.headD 0) (crfF m [vis, b]) := rfl
theorem sctK1_some : sctK1 c n rest vis nP lo ll b (some (r, m)) =
    sctK2 rest vis nP b (r.headD 0) (c n "all_level_params_defined" [lo, ll, b] m) := rfl
end arms
attribute [ind_grind] sctW_nil sctW_cons sctK5_some sctK4_yes sctK4_no sctK3_some sctK2_some sctK1_some

theorem sctW_spec (p : Prog) (hb : BvbProg p) (hf : HfF p) (hcr : CrfF p)
    (hp : p.lookup "check_struct_proj_table_scoped" = some checkStructProjTableScopedL)
    (c : CallM) (hc : CallSpec p c) (n : Nat) : ∀ (s₀ : St) (vis nP lo ll bO bL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_struct_proj_table_scoped" [vis, nP, lo, ll, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧ sctW c n s₀.mem vis nP lo ll bO bL = some (r, s'.mem); ⊤⦄ := by
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
        hffF_spec p hf n, hc n "all_level_params_defined",
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

/-! ## `check_struct_proj_table`: the word model -/

/-- The memory after the table record's thirteen writes. -/
def tblMem (m : Mem) (q T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 : Word) : Mem :=
  ((((((((((((m.set64 EREC q 6).set64 EREC (q + 1) 0).set64 EREC (q + 2) T).set64 EREC (q + 3) lo2
    ).set64 EREC (q + 4) ll2).set64 EREC (q + 5) nP).set64 EREC (q + 6) C).set64 EREC (q + 7) nF
    ).set64 EREC (q + 8) rs).set64 EREC (q + 9) bo2).set64 EREC (q + 10) bl2).set64 EREC (q + 11) go2
    ).set64 EREC (q + 12) gl2

theorem tblMem_eq (m : Mem) (q T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 : Word) :
    tblMem m q T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 =
      wrER m q [6, 0, T, lo2, ll2, nP, C, nF, rs, bo2, bl2, go2, gl2] := by
  simp only [tblMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl,
    show q + 9 + 1 = q + 10 by ac_rfl, show q + 10 + 1 = q + 11 by ac_rfl,
    show q + 11 + 1 = q + 12 by ac_rfl]

/-- After `env_push_table`: the view, unchanged. -/
def tblK9 (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([vis], m)
/-- After the record's allocation: the writes, the push. -/
def tblK8 (p : Prog) (n : Nat) (vis T nP C nF rs lo2 ll2 bo2 bl2 go2 gl2 : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m) => tblK9 vis (callW p (n + 1) "env_push_table" [q]
      (tblMem m q T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2))
/-- After the guards' copy. -/
def tblK7 (p : Prog) (n : Nat) (vis T nP C nF rs lo2 ll2 bo2 bl2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rg, m) => tblK8 p n vis T nP C nF rs lo2 ll2 bo2 bl2 (rg.headD 0) (rg.tail.headD 0)
      (erAllocW m 13)
/-- After the bodies' copy. -/
def tblK6 (p : Prog) (n : Nat) (vis T nP C nF rs go gl lo2 ll2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m) => tblK7 p n vis T nP C nF rs lo2 ll2 (rb.headD 0) (rb.tail.headD 0)
      (efW n m go gl)
/-- After the level parameters' copy. -/
def tblK5 (p : Prog) (n : Nat) (vis T nP C nF rs go gl bO bL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rl, m) => tblK6 p n vis T nP C nF rs go gl (rl.headD 0) (rl.tail.headD 0)
      (efW n m bO bL)
/-- After `find_table`: the table must not be taken. -/
def tblK4 (p : Prog) (n : Nat) (vis T lo ll nP C nF rs go gl bO bL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m) => if rt.headD 0 ≠ 0 then none
    else tblK5 p n vis T nP C nF rs go gl bO bL (efW n m lo ll)
/-- After `env_find`: the structure must be stored. -/
def tblK3 (p : Prog) (n : Nat) (vis T lo ll nP C nF rs go gl bO bL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m) => if rf.headD 0 = 0 then none
    else tblK4 p n vis T lo ll nP C nF rs go gl bO bL (callW p (n + 1) "find_table" [vis, T] m)
/-- After the scoping check. -/
def tblK2 (p : Prog) (n : Nat) (vis T lo ll nP C nF rs go gl bO bL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs', m) => if bL ≠ nF then none else if rs'.headD 0 ≠ 1 then none
    else tblK3 p n vis T lo ll nP C nF rs go gl bO bL (envFindW m T vis)
/-- After `struct_proj_bodies`. -/
def tblK1 (c : CallM) (p : Prog) (n : Nat) (vis T lo ll nP C nF rs go gl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m) => if rb.headD 0 = 0 then none
    else tblK2 p n vis T lo ll nP C nF rs go gl (rb.tail.headD 0) (rb.tail.tail.headD 0)
      (sctW c (n + 1) m vis nP lo ll (rb.tail.headD 0) (rb.tail.tail.headD 0))

/-- **The model of `check_struct_proj_table(T, C, lo, ll, nP, nF, rs, go, gl, cvCa, vis)`**
(its callees at exec fuel `n + 1`; `check_struct_proj_table_scoped` reads `all_level_params_defined`
through `c`). -/
def tblW (c : CallM) (p : Prog) (n : Nat) (m : Mem) (T C lo ll nP nF rs go gl cvCa vis : Word) :
    Option (List Word × Mem) :=
  tblK1 c p n vis T lo ll nP C nF rs go gl (spbW (n + 1) m T nP nF (rdW (m.arr64 EREC) (cvCa + 3)))

section arms
variable (c : CallM) (p : Prog) (n : Nat) (m : Mem)
  (vis T lo ll nP C nF rs go gl bO bL lo2 ll2 bo2 bl2 go2 gl2 q : Word) (r : List Word)
theorem tblK9_some : tblK9 vis (some (r, m)) = some ([vis], m) := rfl
theorem tblK8_some : tblK8 p n vis T nP C nF rs lo2 ll2 bo2 bl2 go2 gl2 (some (q, m)) =
    tblK9 vis (callW p (n + 1) "env_push_table" [q]
      (tblMem m q T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2)) := rfl
theorem tblK7_some : tblK7 p n vis T nP C nF rs lo2 ll2 bo2 bl2 (some (r, m)) =
    tblK8 p n vis T nP C nF rs lo2 ll2 bo2 bl2 (r.headD 0) (r.tail.headD 0) (erAllocW m 13) := rfl
theorem tblK6_some : tblK6 p n vis T nP C nF rs go gl lo2 ll2 (some (r, m)) =
    tblK7 p n vis T nP C nF rs lo2 ll2 (r.headD 0) (r.tail.headD 0) (efW n m go gl) := rfl
theorem tblK5_some : tblK5 p n vis T nP C nF rs go gl bO bL (some (r, m)) =
    tblK6 p n vis T nP C nF rs go gl (r.headD 0) (r.tail.headD 0) (efW n m bO bL) := rfl
theorem tblK4_taken (h : r.headD 0 ≠ 0) :
    tblK4 p n vis T lo ll nP C nF rs go gl bO bL (some (r, m)) = none := by
  simp only [tblK4]; rw [ite_eq_left h]
theorem tblK4_free (h : r.headD 0 = 0) :
    tblK4 p n vis T lo ll nP C nF rs go gl bO bL (some (r, m)) =
      tblK5 p n vis T nP C nF rs go gl bO bL (efW n m lo ll) := by
  simp only [tblK4]; rw [ite_eq_right ((fun e => e h))]
theorem tblK3_missing (h : r.headD 0 = 0) :
    tblK3 p n vis T lo ll nP C nF rs go gl bO bL (some (r, m)) = none := by
  simp only [tblK3]; rw [ite_eq_left h]
theorem tblK3_found (h : r.headD 0 ≠ 0) :
    tblK3 p n vis T lo ll nP C nF rs go gl bO bL (some (r, m)) =
      tblK4 p n vis T lo ll nP C nF rs go gl bO bL (callW p (n + 1) "find_table" [vis, T] m) := by
  simp only [tblK3]; rw [ite_eq_right h]
theorem tblK2_len (h : bL ≠ nF) :
    tblK2 p n vis T lo ll nP C nF rs go gl bO bL (some (r, m)) = none := by
  simp only [tblK2]; rw [ite_eq_left h]
theorem tblK2_bad (h : bL = nF) (h1 : r.headD 0 ≠ 1) :
    tblK2 p n vis T lo ll nP C nF rs go gl bO bL (some (r, m)) = none := by
  simp only [tblK2]; rw [ite_eq_right ((fun e => e h)), ite_eq_left h1]
theorem tblK2_ok (h : bL = nF) (h1 : r.headD 0 = 1) :
    tblK2 p n vis T lo ll nP C nF rs go gl bO bL (some (r, m)) =
      tblK3 p n vis T lo ll nP C nF rs go gl bO bL (envFindW m T vis) := by
  simp only [tblK2]; rw [ite_eq_right ((fun e => e h)), ite_eq_right ((fun e => e h1))]
theorem tblK1_no (h : r.headD 0 = 0) :
    tblK1 c p n vis T lo ll nP C nF rs go gl (some (r, m)) = none := by
  simp only [tblK1]; rw [ite_eq_left h]
theorem tblK1_yes (h : r.headD 0 ≠ 0) :
    tblK1 c p n vis T lo ll nP C nF rs go gl (some (r, m)) =
      tblK2 p n vis T lo ll nP C nF rs go gl (r.tail.headD 0) (r.tail.tail.headD 0)
        (sctW c (n + 1) m vis nP lo ll (r.tail.headD 0) (r.tail.tail.headD 0)) := by
  simp only [tblK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] tblK9_some tblK8_some tblK7_some tblK6_some tblK5_some tblK4_taken tblK4_free
  tblK3_missing tblK3_found tblK2_len tblK2_bad tblK2_ok tblK1_no tblK1_yes

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
  hbb : BvbProg p
  hhf : HfF p
  hix : p.lookup "env_ix" = some envIxL
  hrg : p.lookup "env_row_get" = some envRowGetL
  hfind : p.lookup "env_find" = some envFindL
  htix : p.lookup "tbl_ix" = some tblIxL
  htrg : p.lookup "tbl_row_get" = some tblRowGetL
  htrs : p.lookup "tbl_row_set" = some tblRowSetL
  hftab : p.lookup "find_table" = some findTableL
  hept : p.lookup "env_push_table" = some envPushTableL
  hea : p.lookup "erec_alloc" = some erecAlloc
  hefg : p.lookup "er_from_iw_go" = some erFromIwGo
  hef : p.lookup "er_from_iw" = some erFromIw
  htbl : p.lookup "check_struct_proj_table" = some checkStructProjTableL
  hrec : RecProg p
  hi1 : I1lF p
  hipal : IpalF p
  hcr : CrfF p

set_option maxHeartbeats 4000000 in
theorem tblW_spec (p : Prog) (hP : TblProg p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St)
    (T C lo ll nP nF rs go gl cvCa vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "check_struct_proj_table"
      [T, C, lo, ll, nP, nF, rs, go, gl, cvCa, vis]
    ⦃fun r s' => LocEq s' s₀ ∧
      tblW c p n s₀.mem T C lo ll nP nF rs go gl cvCa vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.htbl]
  simp only [callFn, checkStructProjTableL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    spbW_spec p hP.ha hP.hc hP.hsc hP.hv hP.hd hP.hpf hP.hpp hP.hib hP.hjf hP.hjp hP.hji hP.hmp hP.hap
      hP.hpg hP.hgo hP.hps hP.hpj hP.hspb hP.hi1 hP.hipal (n + 1),
    sctW_spec p hP.hbb hP.hhf hP.hcr hP.hsct c hc (n + 1),
    envFind_specW p hP.hix hP.hrg hP.hfind (n + 1), callW_spec p (n + 1) "find_table",
    efW_spec p hP.hea hP.hefg hP.hef n, erecAlloc_specW p hP.hea (n + 1),
    callW_spec p (n + 1) "env_push_table"]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
    reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
  all_goals grind (gen := 30) (instances := 5000) [lang_grind, arena_grind, ind_grind, tblW, tblMem, rdW_eq]

/-! ## `check_struct_proj_table`: the relation to the twin -/

/-- **The table record's decoding**, from its thirteen words and the three copied slices. -/
theorem sumDecTbl {a : Array Word} {q : Nat}
    {T lo2 ll2 nP C nF rs bo2 bl2 go2 gl2 : Word} {lps : List NIdx} {bodies : List EIdx}
    {guards : List LIdx}
    (hw : ∀ i < 13, a[q + i]? = [6, 0, T, lo2, ll2, nP, C, nF, rs, bo2, bl2, go2, gl2][i]?)
    (hT : H T) (hC : H C) (hrs : H rs)
    (hl : hslice? a lo2.toNat ll2.toNat = some lps) (hb : hslice? a bo2.toNat bl2.toNat = some bodies)
    (hg : hslice? a go2.toNat gl2.toNat = some guards) :
    decTbl a q = some ⟨decI T, lps, nP.toNat, decI C, nF.toNat, decI rs, bodies.toArray, guards⟩ := by
  have h2 := hw 2 (by decide); have h3 := hw 3 (by decide)
  have h4 := hw 4 (by decide); have h5 := hw 5 (by decide); have h6 := hw 6 (by decide)
  have h7 := hw 7 (by decide); have h8 := hw 8 (by decide); have h9 := hw 9 (by decide)
  have h10 := hw 10 (by decide); have h11 := hw 11 (by decide); have h12 := hw 12 (by decide)
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have e3 : q + 3 + 1 = q + 4 := rfl
  have e9 : q + 9 + 1 = q + 10 := rfl
  have e11 : q + 11 + 1 = q + 12 := rfl
  simp only [decTbl, hlist?, nat?, hd?, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    e3, e9, e11, Option.map_some, Option.bind_eq_bind, Option.bind_some, hT, hC, hrs, ite_true,
    hl, hb, hg]
  rfl

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
  have hrow : rowArr (rdW (m.arr64 EREC) (q + 1)) ∈ [132, 133, 134, ECON, 140, 141, 142] := by
    have htr : rowTier (rdW (m.arr64 EREC) (q + 1)) < 2 := Nat.mod_lt _ (by decide)
    rcases (by omega : rowTag (rdW (m.arr64 EREC) (q + 1)) = 0 ∨ rowTag (rdW (m.arr64 EREC) (q + 1)) = 1 ∨
      rowTag (rdW (m.arr64 EREC) (q + 1)) = 2) with h1 | h1 | h1 <;>
    rcases (by omega : rowTier (rdW (m.arr64 EREC) (q + 1)) = 0 ∨
      rowTier (rdW (m.arr64 EREC) (q + 1)) = 1) with h2 | h2 <;>
    simp [rowArr, h1, h2]
  have hne : rowArr (rdW (m.arr64 EREC) (q + 1)) ≠ CTL := by simp only [rowArr, CTL, ArrId]; omega
  have h49 : memoFreeA [rowArr (rdW (m.arr64 EREC) (q + 1))] = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with h | h | h | h | h | h | h <;> rw [h] <;> decide
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
