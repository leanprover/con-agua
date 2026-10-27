import ConAgua.Arena.IndRealSpine
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# RecTW

`eViewShape`, `eViewSpec4`, `piBW`, `piBK1`, `piBK2`, `piBK3` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `e_view` with the result's shape -/

theorem eViewShape (p : Prog) (hp : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "e_view" [h]
    ⦃fun r _ => r = [r.headD 0, r.getD 1 0, r.getD 2 0, r.getD 3 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, eView]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld,
        evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
      finish [List.getD_cons_zero, List.getD_cons_succ]

/-- `e_view`'s spec with its four result words spelt out. -/
theorem eViewSpec4 (p : Prog) (hp : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "e_view" [h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = eViewW s₀.mem h ∧
      r = [r.headD 0, r.getD 1 0, r.getD 2 0, r.getD 3 0]; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  have h1 := M.of_run (P := fun s => s = s₀) hs hrun (eView_spec p hp n s₀ h)
  have h2 := M.of_run (P := fun s => s = s₀) hs hrun (eViewShape p hp n s₀ h)
  exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩

/-! ## `pi_binders` -/

mutual
/-- **The model of `pi_binders`** (the L fuel `n`; the word `fuel` is the twin's). -/
def piBW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, fuel, h =>
    if fuel = 0 then none
    else if h >>> 28 ≠ 6 then some ([0, 0, h], m)
    else piBK1 n m fuel (eViewW m h)

/-- After `e_view`. -/
def piBK1 (n : Nat) (m : Mem) (fuel : Word) (r : List Word) : Option (List Word × Mem) :=
  if r = [] then none
  else piBK2 n fuel (r.getD 1 0) (piBW n m (fuel - 1) (r.getD 2 0))

/-- After the recursive call. -/
def piBK2 (n : Nat) (_fuel ty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m1) => piBK3 (rs.getD 2 0) (consW n m1 ty (rs.headD 0) (rs.getD 1 0))

/-- After `sl_cons`. -/
def piBK3 (be : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0, r.getD 1 0, be], m2)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (fuel h ty be : Word) (r rs : List Word)
theorem piBW_fuel0 (hf : fuel = 0) : piBW (n + 1) m fuel h = none := by simp [piBW, hf]
theorem piBW_leaf (hf : fuel ≠ 0) (hg : h >>> 28 ≠ 6) :
    piBW (n + 1) m fuel h = some ([0, 0, h], m) := by simp [piBW, hf, hg]
theorem piBW_node (hf : fuel ≠ 0) (hg : ¬ h >>> 28 ≠ 6) :
    piBW (n + 1) m fuel h = piBK1 n m fuel (eViewW m h) := by simp [piBW, hf, hg]
theorem piBK1_nil : piBK1 n m fuel [] = none := by simp [piBK1]
theorem piBK1_ne (hr : r ≠ []) :
    piBK1 n m fuel r = piBK2 n fuel (r.getD 1 0) (piBW n m (fuel - 1) (r.getD 2 0)) := by
  simp [piBK1, hr]
theorem piBK2_some : piBK2 n fuel ty (some (rs, m1)) =
    piBK3 (rs.getD 2 0) (consW n m1 ty (rs.headD 0) (rs.getD 1 0)) := rfl
theorem piBK3_some : piBK3 be (some (r, m2)) = some ([r.headD 0, r.getD 1 0, be], m2) := rfl
end arms

grind_pattern [ind_grind] piBW_fuel0 => piBW (n + 1) m fuel h
grind_pattern [ind_grind] piBW_leaf => piBW (n + 1) m fuel h
grind_pattern [ind_grind] piBW_node => piBW (n + 1) m fuel h
grind_pattern [ind_grind] piBK1_ne => piBK1 n m fuel r
grind_pattern [ind_grind] piBK2_some => piBK2 n fuel ty (some (rs, m1))
grind_pattern [ind_grind] piBK3_some => piBK3 be (some (r, m2))

theorem consW_two {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) : r = [r.headD 0, r.getD 1 0] := by
  simp only [consW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, ite_false] at h
  rcases hal : allocW m (l + 1) with _ | ⟨q, m1⟩
  · simp [hal] at h
  simp only [hal] at h
  rcases hcp : copyW (n - 1) (m1.set64 IW q x) (q + 1) o l with _ | m2
  · simp [hcp] at h
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

theorem slConsSpec2 (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hp : p.lookup "sl_cons" = some slCons) (n : Nat)
    (s₀ : St) (x o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "sl_cons" [x, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ consW n s₀.mem x o l = some (r, s'.mem) ∧
      r = [r.headD 0, r.getD 1 0]; ⊤⦄ :=
  triple_post (slCons_specW p ha hc hp n s₀ x o l) (fun _r _s' ⟨h1, h2⟩ => ⟨h1, h2, consW_two h2⟩)

theorem piBW_ok (n : Nat) : ∀ (m m' : Mem) (a : AState) (fuel h : Word) (rs : List Word),
    ArenaR m a → piBW n m fuel h = some (rs, m') → h.toNat < 2 ^ 32 →
    (m.arr64 IW).size < 2 ^ 64 → 200 < (m.arr64 CTL).size →
    ∃ bs e, (ConRon.Arena.piBinders fuel.toNat (decE h)).run a = .ok ((bs, e), a) ∧
      rs = [rs.headD 0, rs.getD 1 0, rs.getD 2 0] ∧
      decHL m' (rs.headD 0).toNat (rs.getD 1 0).toNat = some bs ∧
      (rs.getD 2 0).toNat < 2 ^ 32 ∧ decE (rs.getD 2 0) = e ∧
      IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
      (rs.headD 0).toNat + (rs.getD 1 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a fuel h rs _ hh; simp [piBW] at hh
  | succ n ih =>
    intro m m' a fuel h rs hR hpb hh hsz hc
    by_cases hf : fuel = 0
    · rw [piBW_fuel0 n m fuel h hf] at hpb; simp at hpb
    by_cases hg : h >>> 28 ≠ 6
    · rw [piBW_leaf n m fuel h hf hg] at hpb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpb)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
        (fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0)))
      have htag : (decE h).tag ≠ ETag.forallE := fun h' => hg ((decE_tag_forall h hh).mp h')
      refine ⟨[], decE h, ?_, rfl, ?_, hh, rfl, IWGrow.refl m, MemFrame.refl _ _ m, by simp⟩
      · rw [hk, ConRon.Arena.piBinders]; simp [htag]; rfl
      · simp [decHL, hslice?]
    · rw [piBW_node n m fuel h hf hg] at hpb
      have hg6 : h >>> 28 = 6 := by simpa using hg
      by_cases hr : eViewW m h = []
      · rw [hr, piBK1_nil] at hpb; simp at hpb
      obtain ⟨hvok, hew⟩ := eViewW_forall m h hg6 hr
      rw [piBK1_ne n m fuel _ hr] at hpb
      obtain ⟨rs1, m1, hrec, hpb⟩ := ipK_inv hpb (by simp [piBK2])
      rw [piBK2_some] at hpb
      obtain ⟨r2, m2, hcons, hpb⟩ := ipK_inv hpb (by simp [piBK3])
      rw [piBK3_some] at hpb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpb)
      obtain ⟨hvw, hty, hb⟩ := view_forall m a hR h hh hvok hg6
      have hty2 : ((eViewW m h).getD 1 0).toNat < 2 ^ 32 := by rw [hew]; exact hty
      have hb2 : ((eViewW m h).getD 2 0).toNat < 2 ^ 32 := by rw [hew]; exact hb
      have hbeq : (eViewW m h).getD 2 0 = tfld m FORALL (tierW h) (idxW h) 1 := by
        rw [hew]; rfl
      have hteq : (eViewW m h).getD 1 0 = tfld m FORALL (tierW h) (idxW h) 0 := by
        rw [hew]; rfl
      have hfm1 : (fuel - 1).toNat = fuel.toNat - 1 := by
        have : fuel.toNat ≠ 0 := fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0))
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
      obtain ⟨bs1, e1, hrun1, hsh1, hdec1, hbe1, hbe2, hg1, hf1, hle1⟩ :=
        ih m m1 a (fuel - 1) _ rs1 hR hrec hb2 hsz hc
      have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hf1.2.2.1 IW]; exact hsz
      have hc1 : 200 < (m1.arr64 CTL).size := by rw [hf1.2.2.1 CTL]; exact hc
      obtain ⟨hr2, hdec2, hg2, hf2, hl1, htop2⟩ :=
        consW_dec hcons hsz1 hc1 hle1 hty2 hdec1
      have hk : fuel.toNat = (fuel.toNat - 1) + 1 := by
        have : fuel.toNat ≠ 0 := fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      refine ⟨decE ((eViewW m h).getD 1 0) :: bs1, e1, ?_, ?_, ?_, ?_, ?_, hg1.trans hg2,
        hf1.trans hf2, ?_⟩
      · rw [hk, ConRon.Arena.piBinders, (decE_tag_forall h hh).mpr hg6]
        have hvb := viewBind_forall m a hR h hh hvok hg6
        rw [← hbeq, ← hteq] at hvb
        simp only [beq_self_eq_true, ite_true, StateT.run_bind, viewBind_run' _ a, hvb,
          except_ok_bind]
        rw [← hfm1]
        rw [hrun1]
        rfl
      · simp
      · simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
        rw [hr2]
        simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
        exact hdec2
      · simp only [List.getD_cons_succ, List.getD_cons_zero]; exact hbe1
      · simp only [List.getD_cons_succ, List.getD_cons_zero]; exact hbe2
      · rw [hr2]
        simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
        omega

theorem viewConst_run' (h : EIdx) (a : AState) :
    (viewConst h).run a = .ok (a.store.viewConst h, a) := rfl

theorem mapM_opt_congr3 {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..),
      mapM_opt_congr3 f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- A decoded handle slice below the pool's top survives growth. -/
theorem decHL_grow3 {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {o l : Nat}
    (h : o + l ≤ iwTop m) : (decHL m' o l : Option (List (Idx k))) = decHL m o l := by
  simp only [decHL, hslice?]
  apply mapM_opt_congr3
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [hd?, iwA]
  rw [hg.2.2.1 (o + j) (by omega)]

/-- A returning `e_view` of a `const` handle. -/
theorem eViewW_const (m : Mem) (h : Word) (hg : h >>> 28 = 3) (hne : eViewW m h ≠ []) :
    viewOK m h CONST ∧ eViewW m h = [3, tfld m CONST (tierW h) (idxW h) 0,
      tfld m CONST (tierW h) (idxW h) 1, 0] := by
  unfold eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, ite_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, ite_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  simp only [hg, ite_true] at hne ⊢
  by_cases c : tcnt m CONST (tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, ite_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-- The `viewConst` projection of a `const` handle. -/
theorem viewConst_ok (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) :
    a.store.viewConst (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0),
      decI (tfld m CONST (tierW h) (idxW h) 1)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  simp only [EStore.viewConst, EStore.persGetConst]
  rw [proj_tier m a hR h hh (fun t i => t.getConst i) hv.1]
  simp only [ETables.getConst, Tbl.node?, decE_idx]
  rw [hk]
  simp [hn, hu, decI_word]

/-! ## `rec_target_of` -/

mutual
/-- **The model of `rec_target_of`**: strip the telescope, look at the major's domain head. -/
def recTW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, mI, ty => recTK1 n no nl (stripF 6 m [mI, ty])

/-- After `strip_pis`. -/
def recTK1 (n : Nat) (no nl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([nl], m1)
    else if r.tail.tail.tail.headD 0 >>> 28 ≠ 6 then some ([nl], m1)
    else recTK2 n no nl m1 (eViewW m1 (r.tail.tail.tail.headD 0))

/-- After the major's `e_view`. -/
def recTK2 (n : Nat) (no nl : Word) (m1 : Mem) : List Word → Option (List Word × Mem)
  | [] => none
  | v => recTK3 n no nl (gafF m1 [CWF, v.getD 1 0])

/-- After `get_app_fn`. -/
def recTK3 (n : Nat) (no nl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) =>
    if r.headD 0 >>> 28 ≠ 3 then some ([nl], m3)
    else recTK4 n no nl m3 (eViewW m3 (r.headD 0))

/-- After the head's `e_view`. -/
def recTK4 (n : Nat) (no nl : Word) (m3 : Mem) : List Word → Option (List Word × Mem)
  | [] => none
  | v => recTK5 nl m3 (findW n m3 no nl (v.getD 1 0))

/-- After `sl_find`. -/
def recTK5 (nl : Word) (m3 : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some rf => if rf.headD 0 = 0 then some ([nl], m3) else some ([rf.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m3 : Mem) (no nl mI ty : Word) (r v rf : List Word)
theorem recTW_step : recTW (n + 1) m no nl mI ty = recTK1 n no nl (stripF 6 m [mI, ty]) := rfl
theorem recTK1_some_nil (h : r.headD 0 = 0) : recTK1 n no nl (some (r, m1)) = some ([nl], m1) := by
  simp only [recTK1]; rw [ite_eq_left h]
theorem recTK1_some_nf (h : r.headD 0 ≠ 0) (h2 : r.tail.tail.tail.headD 0 >>> 28 ≠ 6) :
    recTK1 n no nl (some (r, m1)) = some ([nl], m1) := by
  simp only [recTK1]; rw [ite_eq_right h, ite_eq_left h2]
theorem recTK1_some_f (h : r.headD 0 ≠ 0) (h2 : ¬ r.tail.tail.tail.headD 0 >>> 28 ≠ 6) :
    recTK1 n no nl (some (r, m1)) =
      recTK2 n no nl m1 (eViewW m1 (r.tail.tail.tail.headD 0)) := by
  simp only [recTK1]; rw [ite_eq_right h, ite_eq_right h2]
theorem recTK2_nil : recTK2 n no nl m1 [] = none := rfl
theorem recTK2_ne (h : v ≠ []) :
    recTK2 n no nl m1 v = recTK3 n no nl (gafF m1 [CWF, v.getD 1 0]) := by
  cases v with
  | nil => exact absurd rfl h
  | cons a as => rfl
theorem recTK3_some_nc (h : r.headD 0 >>> 28 ≠ 3) : recTK3 n no nl (some (r, m3)) = some ([nl], m3) := by
  simp only [recTK3]; rw [ite_eq_left h]
theorem recTK3_some_c (h : ¬ r.headD 0 >>> 28 ≠ 3) :
    recTK3 n no nl (some (r, m3)) = recTK4 n no nl m3 (eViewW m3 (r.headD 0)) := by
  simp only [recTK3]; rw [ite_eq_right h]
theorem recTK4_nil : recTK4 n no nl m3 [] = none := rfl
theorem recTK4_ne (h : v ≠ []) :
    recTK4 n no nl m3 v = recTK5 nl m3 (findW n m3 no nl (v.getD 1 0)) := by
  cases v with
  | nil => exact absurd rfl h
  | cons a as => rfl
theorem recTK5_miss (h : rf.headD 0 = 0) : recTK5 nl m3 (some rf) = some ([nl], m3) := by
  simp only [recTK5]; rw [ite_eq_left h]
theorem recTK5_hit (h : rf.headD 0 ≠ 0) : recTK5 nl m3 (some rf) = some ([rf.tail.headD 0], m3) := by
  simp only [recTK5]; rw [ite_eq_right h]
end arms

grind_pattern [ind_grind] recTW_step => recTW (n + 1) m no nl mI ty
grind_pattern [ind_grind] recTK1_some_nil => recTK1 n no nl (some (r, m1))
grind_pattern [ind_grind] recTK1_some_nf => recTK1 n no nl (some (r, m1))
grind_pattern [ind_grind] recTK1_some_f => recTK1 n no nl (some (r, m1))
grind_pattern [ind_grind] recTK2_ne => recTK2 n no nl m1 v
grind_pattern [ind_grind] recTK3_some_nc => recTK3 n no nl (some (r, m3))
grind_pattern [ind_grind] recTK3_some_c => recTK3 n no nl (some (r, m3))
grind_pattern [ind_grind] recTK4_ne => recTK4 n no nl m3 v
grind_pattern [ind_grind] recTK5_miss => recTK5 nl m3 (some rf)
grind_pattern [ind_grind] recTK5_hit => recTK5 nl m3 (some rf)

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
  (hp : p.lookup "rec_target_of" = some recTargetOf) (hst : StripProg p) (had : AdF p)
include hv hf hp hst had

theorem recTargetOf_spec (n : Nat) (s₀ : St) (no nl mI ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_target_of" [no, nl, mI, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ recTW n s₀.mem no nl mI ty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, recTargetOf]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stripPis_specF p hst n, gafF_spec p had n, eViewSpec4 p hv n,
        slFind_spec p hf n] <;>
      finish (gen := 20)

end spec

theorem decE_tag_const (e : Word) (hh : e.toNat < 2 ^ 32) :
    ((decE e).tag = ETag.const) ↔ e >>> 28 = 3 := decE_tag_eq e hh 3 (by decide)

theorem findIdx_decI_parts (ws : List Word) (x : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) :
    ((ws.map (decI : Word → NIdx)).findIdx? (· == (decI x : NIdx))) = ws.findIdx? (· == x) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.findIdx?_cons]
    have hw := hws w (List.mem_cons_self ..)
    rw [L.Arena.decI_beq w x hw hx]
    by_cases h : w = x
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, beq_iff_eq]
      rw [ih (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))]

theorem recTW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl mI ty : Word) (r : List Word) (names : List NIdx),
    recTW n m no nl mI ty = some (r, m') → StageR dn vis fe m a → ty.toNat < 2 ^ 32 →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat < 2 ^ 64 →
    no.toNat + nl.toNat ≤ iwTop m →
    ∃ t a', (ConRon.Arena.recTargetOf names mI.toNat (decI ty)).run a = .ok (t, a') ∧
      r = [UInt64.ofNat t] ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  intro dn fe vis m m' a no nl mI ty r names hrt hS hty hnames hb hbt
  cases n with
  | zero => simp [recTW] at hrt
  | succ n =>
  have hnl : nl.toNat = names.length := (decHL_length m hnames).symm
  have hnlw : [UInt64.ofNat names.length] = [nl] := by rw [← hnl, ofNat_toNat_word nl]
  rw [recTW_step] at hrt
  obtain ⟨r1, m1, hra, hrt⟩ := ipK_inv hrt (by simp [recTK1])
  obtain ⟨x1, a1, hrun1, hS1, hg1, hdec1⟩ := stripF_pis_ok dn vis fe mI ty hty m m1 a r1 hra hS
  have hty' : (decI ty : EIdx) = decE ty := rfl
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hdec1
    rw [recTK1_some_nil n m1 no nl r1 h0] at hrt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrt)
    refine ⟨names.length, a1, ?_, hnlw.symm, hS1, hg1⟩
    · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind]
      rfl
  | some q =>
    obtain ⟨l1, e1⟩ := q
    obtain ⟨h1, -, hbl, hbe⟩ := hdec1
    have h1ne : r1.headD 0 ≠ 0 := by rw [h1]; decide
    have hd3 : r1.drop 3 = r1.tail.tail.tail := by
      rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
    rw [hd3] at hbl hbe
    have hR1 : ArenaR m1 a1 := hS1.1.arena.1
    have hnamesz : names.length = nl.toNat := hnl.symm
    by_cases hg6 : r1.tail.tail.tail.headD 0 >>> 28 ≠ 6
    · rw [recTK1_some_nf n m1 no nl r1 h1ne hg6] at hrt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrt)
      have htag : e1.tag ≠ ETag.forallE := by
        rw [← hbe]; exact fun h' => hg6 ((decE_tag_forall _ hbl).mp h')
      refine ⟨names.length, a1, ?_, hnlw.symm, hS1, hg1⟩
      · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind]
        simp [htag]
        rfl
    · have hg6' : r1.tail.tail.tail.headD 0 >>> 28 = 6 := by simpa using hg6
      rw [recTK1_some_f n m1 no nl r1 h1ne hg6] at hrt
      by_cases hr : eViewW m1 (r1.tail.tail.tail.headD 0) = []
      · rw [hr, recTK2_nil] at hrt; simp at hrt
      obtain ⟨hvok, hew⟩ := eViewW_forall m1 _ hg6' hr
      rw [recTK2_ne n m1 no nl _ hr] at hrt
      obtain ⟨hvw, hty2, hb2⟩ := view_forall m1 a1 hR1 _ hbl hvok hg6'
      have hdomw : (eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0 =
          tfld m1 FORALL (tierW (r1.tail.tail.tail.headD 0)) (idxW (r1.tail.tail.tail.headD 0)) 0 := by rw [hew]; rfl
      have hdomlt : ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0).toNat < 2 ^ 32 := by
        rw [hdomw]; exact hty2
      obtain ⟨r3, m3, hra3, hrt⟩ := ipK_inv hrt (by simp [recTK3])
      obtain ⟨x3, a3, hrun3, hS3, hg3, hdl3, hdI3⟩ :=
        gafF_ok dn vis fe CWF _ hdomlt m1 m3 a1 r3 hra3 hS1
      have hR3 : ArenaR m3 a3 := hS3.1.arena.1
      have hvb := viewBind_forall m1 a1 hR1 _ hbl hvok hg6'
      have hrun3' : StateT.run (getAppFn coreWalkFuel (decE
          ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0))) a1 = Except.ok (x3, a3) := by
        rw [← CWF_eq]; exact hrun3
      subst hbe
      have hvb' : a1.store.viewBind (decI (r1.tail.tail.tail.headD 0)) = some
          (decE ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0),
           decE ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 2 0)) := by
        rw [hew]; exact hvb
      have hftag : ((decI (r1.tail.tail.tail.headD 0) : EIdx).tag == ETag.forallE) = true := by
        simp only [beq_iff_eq]; exact (decE_tag_forall _ hbl).mpr hg6'
      by_cases hc : r3.headD 0 >>> 28 ≠ 3
      · rw [recTK3_some_nc n m3 no nl r3 hc] at hrt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrt)
        have htag : x3.tag ≠ ETag.const := by
          rw [← hdI3]; exact fun h' => hc ((decE_tag_const _ hdl3).mp h')
        refine ⟨names.length, a3, ?_, hnlw.symm, hS3, hg1.trans hg3⟩
        · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind, hftag,
            ite_true, viewBind_run' _ a1, hvb']
          have hctag : (x3.tag == ETag.const) = false := by
            simpa using htag
          simp only [hrun3', except_ok_bind, hctag]
          rfl
      · have hc3 : r3.headD 0 >>> 28 = 3 := by simpa using hc
        rw [recTK3_some_c n m3 no nl r3 hc] at hrt
        by_cases hr2 : eViewW m3 (r3.headD 0) = []
        · rw [hr2, recTK4_nil] at hrt; simp at hrt
        obtain ⟨hvok2, hew2⟩ := eViewW_const m3 _ hc3 hr2
        rw [recTK4_ne n m3 no nl _ hr2] at hrt
        obtain ⟨hvc, hn2, hu2⟩ := view_const_f m3 a3 hR3 _ hdl3 hvok2 hc3
        have hxw : (eViewW m3 (r3.headD 0)).getD 1 0 =
            tfld m3 CONST (tierW (r3.headD 0)) (idxW (r3.headD 0)) 0 := by
          rw [hew2]; rfl
        have hxlt : ((eViewW m3 (r3.headD 0)).getD 1 0).toNat < 2 ^ 32 := by rw [hxw]; exact hn2
        have hvcc := viewConst_ok m3 a3 hR3 _ hdl3 hvok2
        have hnames3 : decHL m3 no.toNat nl.toNat = some names := by
          rw [decHL_grow3 (hg1.trans hg3) hbt]; exact hnames
        obtain ⟨ws, hws, hnm, hwlt⟩ := slR_of_decHL m3 nl.toNat no.toNat names hnames3 hb
        rw [ofNat_toNat_word, ofNat_toNat_word] at hws
        have hlen : ws.length < 2 ^ 64 := by
          have := decHL_length m3 hnames3
          rw [hnm] at this; simp at this; omega
        rcases hf : findW n m3 no nl ((eViewW m3 (r3.headD 0)).getD 1 0) with _ | rf
        · rw [hf] at hrt; simp [recTK5] at hrt
        have hfk := findW_ok n m3 no nl _ rf ws hws hf hlen
        have hfi := findIdx_decI_parts ws _ hwlt hxlt
        rw [← hnm] at hfi
        have hctag : (x3.tag == ETag.const) = true := by
          simp only [beq_iff_eq]; rw [← hdI3]; exact (decE_tag_const _ hdl3).mpr hc3
        have hvcc' : a3.store.viewConst x3 = some
            (decI ((eViewW m3 (r3.headD 0)).getD 1 0), decI ((eViewW m3 (r3.headD 0)).getD 2 0)) := by
          rw [← hdI3, hew2]; exact hvcc
        rw [hf] at hrt
        by_cases hf0 : rf.headD 0 = 0
        · rw [recTK5_miss m3 nl rf hf0] at hrt
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrt)
          have hnone : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).getD 1 0) = none := by
            rw [hfk] at hf0
            cases h' : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).getD 1 0) with
            | none => rfl
            | some i => rw [h'] at hf0; simp at hf0
          refine ⟨names.length, a3, ?_, hnlw.symm, hS3, hg1.trans hg3⟩
          · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind, hftag,
              ite_true, viewBind_run' _ a1, hvb', hrun3', hctag, viewConst_run', hvcc', hfi, hnone]
            rfl
        · rw [recTK5_hit m3 nl rf hf0] at hrt
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrt)
          obtain ⟨i, hi⟩ : ∃ i, ws.findIdx? (· == (eViewW m3 (r3.headD 0)).getD 1 0) = some i := by
            rw [hfk] at hf0
            cases h' : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).getD 1 0) with
            | none => rw [h'] at hf0; simp at hf0
            | some i => exact ⟨i, rfl⟩
          refine ⟨i, a3, ?_, ?_, hS3, hg1.trans hg3⟩
          · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind, hftag,
              ite_true, viewBind_run' _ a1, hvb', hrun3', hctag, viewConst_run', hvcc', hfi, hi]
            rfl
          · rw [hfk, hi]; rfl

/-! ## `block_counts` -/

/-- The pure tail of `block_counts`: from the binder count `bl`, the result's tag `g` and the
recursor data. -/
def bcPure (nPd k nC nR bl g rOk rMI rRP : Word) : List Word :=
  if g = 2 then
    (if bl < nPd then [0, 0, 0] else [1, nPd, bl - nPd])
  else if rOk = 0 then [0, 0, 0]
  else if rRP < nC + k ∨ rMI < rRP then [0, 0, 0]
  else if rRP - (nC + k) = nPd then [1, nPd, rMI - rRP]
  else if k < nR ∧ nPd + nR + nC ≤ rRP then [1, nPd, rMI - rRP]
  else [0, 0, 0]

section pure
variable (nPd k nC nR bl g rOk rMI rRP : Word)
theorem bcPure_sort_lt (hg : g = 2) (h : bl < nPd) : bcPure nPd k nC nR bl g rOk rMI rRP = [0, 0, 0] := by
  simp [bcPure, hg, h]
theorem bcPure_sort_ge (hg : g = 2) (h : ¬ bl < nPd) :
    bcPure nPd k nC nR bl g rOk rMI rRP = [1, nPd, bl - nPd] := by simp [bcPure, hg, h]
theorem bcPure_norec (hg : g ≠ 2) (h : rOk = 0) : bcPure nPd k nC nR bl g rOk rMI rRP = [0, 0, 0] := by
  simp [bcPure, hg, h]
theorem bcPure_badrp (hg : g ≠ 2) (h0 : rOk ≠ 0) (h : rRP < nC + k ∨ rMI < rRP) :
    bcPure nPd k nC nR bl g rOk rMI rRP = [0, 0, 0] := by simp [bcPure, hg, h0, h]
theorem bcPure_eq1 (hg : g ≠ 2) (h0 : rOk ≠ 0) (h : ¬ (rRP < nC + k ∨ rMI < rRP))
    (h1 : rRP - (nC + k) = nPd) : bcPure nPd k nC nR bl g rOk rMI rRP = [1, nPd, rMI - rRP] := by
  simp only [bcPure, hg, h0, h, h1]; simp
theorem bcPure_eq2 (hg : g ≠ 2) (h0 : rOk ≠ 0) (h : ¬ (rRP < nC + k ∨ rMI < rRP))
    (h1 : ¬ rRP - (nC + k) = nPd) (h2 : k < nR ∧ nPd + nR + nC ≤ rRP) :
    bcPure nPd k nC nR bl g rOk rMI rRP = [1, nPd, rMI - rRP] := by
  simp only [bcPure, hg, h0, h, h1, h2]; simp
theorem bcPure_none (hg : g ≠ 2) (h0 : rOk ≠ 0) (h : ¬ (rRP < nC + k ∨ rMI < rRP))
    (h1 : ¬ rRP - (nC + k) = nPd) (h2 : ¬ (k < nR ∧ nPd + nR + nC ≤ rRP)) :
    bcPure nPd k nC nR bl g rOk rMI rRP = [0, 0, 0] := by
  simp only [bcPure, hg, h0, h, h1, h2]; simp
end pure

/-- **The model of `block_counts_head`**: `(bl, g)` and the memory. -/
def bchW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, cvT => bchK1 n (piBW n m CWF (rdW (m.arr64 EREC) (cvT + 3)))
where
  bchK1 (_n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (rs, m1) => bchK2 (rs.getD 1 0) m1 (eViewW m1 (rs.getD 2 0))
  bchK2 (bl : Word) (m1 : Mem) : List Word → Option (List Word × Mem)
    | [] => none
    | v => some ([bl, v.headD 0], m1)

section arms
variable (n : Nat) (m m1 : Mem) (cvT bl : Word) (rs v : List Word)
theorem bchW_step : bchW (n + 1) m cvT =
    bchW.bchK1 n (piBW n m CWF (rdW (m.arr64 EREC) (cvT + 3))) := rfl
theorem bchK1_some : bchW.bchK1 n (some (rs, m1)) =
    bchW.bchK2 (rs.getD 1 0) m1 (eViewW m1 (rs.getD 2 0)) := rfl
theorem bchK2_ne (h : v ≠ []) : bchW.bchK2 bl m1 v = some ([bl, v.headD 0], m1) := by
  cases v with
  | nil => exact absurd rfl h
  | cons a as => rfl
end arms

grind_pattern [ind_grind] bchW_step => bchW (n + 1) m cvT
grind_pattern [ind_grind] bchK1_some => bchW.bchK1 n (some (rs, m1))
grind_pattern [ind_grind] bchK2_ne => bchW.bchK2 bl m1 v

/-- After `block_counts_head`: the arithmetic tail. -/
def bcK (nPd k nC nR rOk rMI rRP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => some (bcPure nPd k nC nR (r1.headD 0) (r1.getD 1 0) rOk rMI rRP, m1)

/-- **The model of `block_counts`.** -/
def bcW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, nPd, k, nC, nR, cvT, rOk, rMI, rRP => bcK nPd k nC nR rOk rMI rRP (bchW n m cvT)

theorem bcK_some (nPd k nC nR rOk rMI rRP : Word) (r1 : List Word) (m1 : Mem) :
    bcK nPd k nC nR rOk rMI rRP (some (r1, m1)) =
      some (bcPure nPd k nC nR (r1.headD 0) (r1.getD 1 0) rOk rMI rRP, m1) := rfl
theorem bcW_def (n : Nat) (m : Mem) (nPd k nC nR cvT rOk rMI rRP : Word) :
    bcW (n + 1) m nPd k nC nR cvT rOk rMI rRP = bcK nPd k nC nR rOk rMI rRP (bchW n m cvT) := rfl
grind_pattern [ind_grind] bcK_some => bcK nPd k nC nR rOk rMI rRP (some (r1, m1))
grind_pattern [ind_grind] bcW_def => bcW (n + 1) m nPd k nC nR cvT rOk rMI rRP

theorem arenaR_frame_iw {m m' : Mem} {a : AState} (hf : MemFrame [IW] [200] m m')
    (h : ArenaR m a) : ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, IW])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf h

theorem sort_head_iff (m1 : Mem) (res : Word) (v : ENodeView) (hv : ViewR (eViewW m1 res) v) :
    (eViewW m1 res).headD 0 = 2 ↔ ∃ u, v = .sort u := by
  cases v with
  | sort u => exact ⟨fun _ => ⟨u, rfl⟩, fun _ => hv.1⟩
  | _ =>
    simp only [ViewR] at hv
    constructor
    · intro hh; first | rw [hv.1] at hh | rw [hv] at hh
      exact absurd hh (by decide)
    · rintro ⟨u, hu⟩; cases hu

theorem bchW_ok (n : Nat) (m m1 : Mem) (a : AState) (cvT : Word) (r1 : List Word)
    (hR : ArenaR m a) (h : bchW n m cvT = some (r1, m1))
    (hty : (rdW (m.arr64 EREC) (cvT + 3)).toNat < 2 ^ 32)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size) :
    ∃ bs res v, (ConRon.Arena.piBinders coreWalkFuel (decE (rdW (m.arr64 EREC) (cvT + 3)))).run a
        = .ok ((bs, res), a) ∧ r1 = [r1.headD 0, r1.getD 1 0] ∧ (r1.headD 0).toNat = bs.length ∧
      a.store.view res = some v ∧ ((r1.getD 1 0 = 2) ↔ ∃ u, v = .sort u) ∧
      IWGrow m m1 ∧ MemFrame [IW] [200] m m1 := by
  cases n with
  | zero => simp [bchW] at h
  | succ n =>
    rw [bchW_step] at h
    rcases hp : piBW n m CWF (rdW (m.arr64 EREC) (cvT + 3)) with _ | ⟨rs, m1'⟩ <;> rw [hp] at h
    · simp [bchW.bchK1] at h
    rw [bchK1_some] at h
    by_cases hr : eViewW m1' (rs.getD 2 0) = []
    · rw [hr] at h; simp [bchW.bchK2] at h
    rw [bchK2_ne _ _ _ hr] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨bs, e, hrun, hsh, hdec, hb1, hb2, hg, hf, -⟩ :=
      piBW_ok n m m1' a CWF _ rs hR hp hty hsz hc
    have hR1 : ArenaR m1' a := arenaR_frame_iw hf hR
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m1' a hR1 _ hr
    have hlen := decHL_length m1' hdec
    refine ⟨bs, e, v, ?_, rfl, ?_, ?_, ?_, hg, hf⟩
    · rw [← CWF_eq]; exact hrun
    · simp only [List.headD_cons]; exact hlen.symm
    · rw [← hb2]; exact hv
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact sort_head_iff _ _ _ hvr

theorem decCVp_type {m : Mem} {q : Word} {cv : IConstantVal} (h : decCVp m q.toNat = some cv)
    (hb : q.toNat + 3 < 2 ^ 64) :
    (rdW (m.arr64 EREC) (q + 3)).toNat < 2 ^ 32 ∧ decE (rdW (m.arr64 EREC) (q + 3)) = cv.type := by
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, -, lv, -, ty, hty, hcv⟩ := h
  have hty' : ty = cv.type := by rw [← hcv]
  rcases hw : (erA m)[q.toNat + 3]? with _ | w
  · simp [hd?, hw] at hty
  by_cases hl : w.toNat < 2 ^ 32
  · simp [hd?, hw, hl] at hty
    have e : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
    have hrd : rdW (m.arr64 EREC) (q + 3) = w := by
      simp only [rdW, e]; exact (by simpa [erA] using hw : (m.arr64 EREC)[q.toNat + 3]? = some w) ▸ rfl
    rw [hrd]
    exact ⟨hl, by rw [← hty', ← hty]; rfl⟩
  · simp [hd?, hw, hl] at hty

/-- `Option (Nat × Nat)` as the words `(ok, a, b)`. -/
def encONN : Option (Nat × Nat) → List Word
  | none => [0, 0, 0]
  | some (p, q) => [1, UInt64.ofNat p, UInt64.ofNat q]

/-- The Nat-level tail of `blockCounts?` past the sort test. -/
def bcTail (nPd k nC nR : Nat) : Option (Nat × Nat) → Option (Nat × Nat)
  | none => none
  | some (mI, rP) =>
    if rP < nC + k || mI < rP then none
    else if rP - (nC + k) == nPd then some (nPd, mI - rP)
    else if k < nR && nPd + nR + nC ≤ rP then some (nPd, mI - rP)
    else none

theorem bcTail_snd {nPd k nC nR p q : Nat} {rr : Option (Nat × Nat)}
    (e : bcTail nPd k nC nR rr = some (p, q)) (hb : ∀ x y, rr = some (x, y) → x < 2 ^ 64) :
    q < 2 ^ 64 := by
  cases rr with
  | none => cases e
  | some xy =>
    obtain ⟨x, y⟩ := xy
    have := hb x y rfl
    simp only [bcTail] at e
    repeat' (split at e)
    all_goals (try simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at e)
    all_goals omega

theorem bcTail_run (nPd k nC nR : Nat) (rr : Option (Nat × Nat)) (a : AState) :
    (match rr with
      | none => (pure none : AM (Option (Nat × Nat)))
      | some (mI, rP) =>
        if rP < nC + k || mI < rP then pure none
        else if rP - (nC + k) == nPd then pure (some (nPd, mI - rP))
        else if k < nR && nPd + nR + nC ≤ rP then pure (some (nPd, mI - rP))
        else pure none).run a = .ok (bcTail nPd k nC nR rr, a) := by
  cases rr with
  | none => rfl
  | some q =>
    obtain ⟨mI, rP⟩ := q
    simp only [bcTail]
    repeat' split
    all_goals rfl

theorem bcPure_nonsort (nPd k nC nR bl g rOk rMI rRP : Word) (hg : g ≠ 2)
    (h1 : nPd.toNat < 2 ^ 32) (h2 : k.toNat < 2 ^ 32) (h3 : nC.toNat < 2 ^ 32)
    (h4 : nR.toNat < 2 ^ 32) (h5 : rMI.toNat < 2 ^ 32) (h6 : rRP.toNat < 2 ^ 32) :
    bcPure nPd k nC nR bl g rOk rMI rRP = encONN (bcTail nPd.toNat k.toNat nC.toNat nR.toNat
      (if rOk = 0 then none else some (rMI.toNat, rRP.toNat))) := by
  by_cases h0 : rOk = 0
  · rw [bcPure_norec _ _ _ _ _ _ _ _ _ hg h0, ite_eq_left h0]; rfl
  rw [ite_eq_right h0]
  simp only [bcTail]
  have e1 : (nC + k).toNat = nC.toNat + k.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have e2 : (nPd + nR + nC).toNat = nPd.toNat + nR.toNat + nC.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
  by_cases c1 : rRP < nC + k ∨ rMI < rRP
  · rw [bcPure_badrp _ _ _ _ _ _ _ _ _ hg h0 c1]
    have : (rRP.toNat < nC.toNat + k.toNat || rMI.toNat < rRP.toNat) = true := by
      rcases c1 with c | c
      · have := UInt64.lt_iff_toNat_lt.mp c; rw [e1] at this; simp [this]
      · have := UInt64.lt_iff_toNat_lt.mp c; simp [this]
    rw [ite_eq_left this]; rfl
  · have c1' : (rRP.toNat < nC.toNat + k.toNat || rMI.toNat < rRP.toNat) = false := by
      have a1 : ¬ rRP < nC + k := fun h => c1 (Or.inl h)
      have a2 : ¬ rMI < rRP := fun h => c1 (Or.inr h)
      have b1 := (not_congr UInt64.lt_iff_toNat_lt).mp a1
      have b2 := (not_congr UInt64.lt_iff_toNat_lt).mp a2
      rw [e1] at b1
      simp [b1, b2]
    rw [ite_eq_right (by simp [c1'])]
    have hle : (nC + k).toNat ≤ rRP.toNat := by
      have a1 : ¬ rRP < nC + k := fun h => c1 (Or.inl h)
      have b1 := (not_congr UInt64.lt_iff_toNat_lt).mp a1; omega
    have hle2 : nC + k ≤ rRP := UInt64.le_iff_toNat_le.mpr hle
    have hsub : (rRP - (nC + k)).toNat = rRP.toNat - (nC.toNat + k.toNat) := by
      rw [UInt64.toNat_sub_of_le _ _ hle2, e1]
    have hrm : rRP ≤ rMI := by
      have a2 : ¬ rMI < rRP := fun h => c1 (Or.inr h)
      exact UInt64.not_lt.mp a2
    have hsub2 : UInt64.ofNat (rMI.toNat - rRP.toNat) = rMI - rRP := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ hrm, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
    by_cases c2 : rRP - (nC + k) = nPd
    · rw [bcPure_eq1 _ _ _ _ _ _ _ _ _ hg h0 c1 c2]
      have : (rRP.toNat - (nC.toNat + k.toNat) == nPd.toNat) = true := by
        rw [← hsub, c2]; simp
      rw [ite_eq_left this]
      simp only [encONN, hsub2, ofNat_toNat_word]
    · have c2' : (rRP.toNat - (nC.toNat + k.toNat) == nPd.toNat) = false := by
        rw [← hsub]; simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => c2 (UInt64.toNat_inj.mp h)
      rw [ite_eq_right (by simp [c2'])]
      by_cases c3 : k < nR ∧ nPd + nR + nC ≤ rRP
      · rw [bcPure_eq2 _ _ _ _ _ _ _ _ _ hg h0 c1 c2 c3]
        have : (k.toNat < nR.toNat && nPd.toNat + nR.toNat + nC.toNat ≤ rRP.toNat) = true := by
          have a := UInt64.lt_iff_toNat_lt.mp c3.1
          have b := UInt64.le_iff_toNat_le.mp c3.2
          rw [e2] at b
          simp [a, b]
        rw [ite_eq_left this]
        simp only [encONN, hsub2, ofNat_toNat_word]
      · rw [bcPure_none _ _ _ _ _ _ _ _ _ hg h0 c1 c2 c3]
        have : (k.toNat < nR.toNat && nPd.toNat + nR.toNat + nC.toNat ≤ rRP.toNat) = false := by
          by_cases a : k < nR
          · have b : ¬ nPd + nR + nC ≤ rRP := fun h => c3 ⟨a, h⟩
            have b' := (not_congr UInt64.le_iff_toNat_le).mp b
            rw [e2] at b'
            simp [b']
          · have a' := (not_congr UInt64.lt_iff_toNat_lt).mp a
            simp [a']
        rw [ite_eq_right (by simp [this])]; rfl

theorem bcW_ok (n : Nat) (m m' : Mem) (a : AState) (nPd k nC nR cvT rOk rMI rRP : Word)
    (r : List Word) (cv : IConstantVal) (rr : Option (Nat × Nat))
    (hR : ArenaR m a) (h : bcW n m nPd k nC nR cvT rOk rMI rRP = some (r, m'))
    (hcv : decCVp m cvT.toNat = some cv) (hb : cvT.toNat + 3 < 2 ^ 64)
    (hrr : rr = if rOk = 0 then none else some (rMI.toNat, rRP.toNat))
    (h1 : nPd.toNat < 2 ^ 32) (h2 : k.toNat < 2 ^ 32) (h3 : nC.toNat < 2 ^ 32)
    (h4 : nR.toNat < 2 ^ 32) (h5 : rMI.toNat < 2 ^ 32) (h6 : rRP.toNat < 2 ^ 32)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size) :
    ∃ x, (ConRon.Arena.blockCounts? nPd.toNat k.toNat nC.toNat nR.toNat cv rr).run a = .ok (x, a) ∧
      r = encONN x ∧ (∀ p q, x = some (p, q) → q < 2 ^ 64) ∧ IWGrow m m' ∧
      MemFrame [IW] [200] m m' := by
  cases n with
  | zero => simp [bcW] at h
  | succ n =>
  rw [bcW_def] at h
  obtain ⟨r1, m1, hh, h⟩ := ipK_inv h (by simp [bcK])
  rw [bcK_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hty32, hty⟩ := decCVp_type hcv hb
  obtain ⟨bs, res, v, hrun, hsh, hlen, hview, hiff, hg, hf⟩ :=
    bchW_ok n m m1 a cvT r1 hR hh hty32 hsz hc
  have hvr := view_run res a v hview
  have hl32 : (r1.headD 0).toNat = bs.length := hlen
  by_cases hs : r1.getD 1 0 = 2
  · obtain ⟨u, rfl⟩ := hiff.mp hs
    by_cases hl : r1.headD 0 < nPd
    · have hlt : ¬ nPd.toNat ≤ bs.length := by
        have := UInt64.lt_iff_toNat_lt.mp hl; omega
      refine ⟨none, ?_, ?_, by simp, hg, hf⟩
      · unfold ConRon.Arena.blockCounts?
        rw [← hty]
        simp only [StateT.run_bind, hrun, except_ok_bind, hvr]
        rw [ite_eq_right hlt]; rfl
      · rw [bcPure_sort_lt _ _ _ _ _ _ _ _ _ hs hl]; rfl
    · have hge : nPd.toNat ≤ bs.length := by
        have := (not_congr UInt64.lt_iff_toNat_lt).mp hl; omega
      refine ⟨some (nPd.toNat, bs.length - nPd.toNat), ?_, ?_, fun p q e => by
        simp only [Option.some.injEq, Prod.mk.injEq] at e; have := (r1.headD 0).toNat_lt; omega, hg, hf⟩
      · unfold ConRon.Arena.blockCounts?
        rw [← hty]
        simp only [StateT.run_bind, hrun, except_ok_bind, hvr]
        rw [ite_eq_left hge]; rfl
      · rw [bcPure_sort_ge _ _ _ _ _ _ _ _ _ hs hl]
        simp only [encONN]
        have e1 : UInt64.ofNat nPd.toNat = nPd := ofNat_toNat_word nPd
        have e2 : UInt64.ofNat (bs.length - nPd.toNat) = r1.headD 0 - nPd := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
          have := (r1.headD 0).toNat_lt
          rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; omega
        rw [e1, e2]
  · have hns : ∀ u, v ≠ ENodeView.sort u := fun u hu => hs (hiff.mpr ⟨u, hu⟩)
    refine ⟨bcTail nPd.toNat k.toNat nC.toNat nR.toNat rr, ?_, ?_, fun p q e => ?_, hg, hf⟩
    rotate_left 2
    · subst hrr
      split at e
      · cases e
      · refine bcTail_snd e fun x y hxy => ?_
        simp only [Option.some.injEq, Prod.mk.injEq] at hxy; omega
    · unfold ConRon.Arena.blockCounts?
      rw [← hty]
      simp only [StateT.run_bind, hrun, except_ok_bind, hvr]
      cases v with
      | sort u => exact absurd rfl (hns u)
      | _ => exact bcTail_run _ _ _ _ rr a
    · rw [bcPure_nonsort _ _ _ _ _ _ _ _ _ hs h1 h2 h3 h4 h5 h6, hrr]

end L.Ind

end
