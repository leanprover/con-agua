module

public import ConAgua.Arena.IndRealSpine
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndParts
import ConAgua.L.ModelGen

@[expose] public section

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
        evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] <;>
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
    else if tagW h ≠ 6 then some ([0, 0, h], m)
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
theorem piBW_leaf (hf : fuel ≠ 0) (hg : tagW h ≠ 6) :
    piBW (n + 1) m fuel h = some ([0, 0, h], m) := by simp [piBW, hf, hg]
theorem piBW_node (hf : fuel ≠ 0) (hg : ¬ tagW h ≠ 6) :
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
    by_cases hg : tagW h ≠ 6
    · rw [piBW_leaf n m fuel h hf hg] at hpb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpb)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
        (fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0)))
      have htag : (decE h).tag ≠ ETag.forallE := fun h' => hg ((decE_tag_forallE h hh).mp h')
      refine ⟨[], decE h, ?_, rfl, ?_, hh, rfl, IWGrow.refl m, MemFrame.refl _ _ m, by simp⟩
      · rw [hk, ConRon.Arena.piBinders]; simp [htag]; rfl
      · simp [decHL, hslice?]
    · rw [piBW_node n m fuel h hf hg] at hpb
      have hg6 : tagW h = 6 := by simpa using hg
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
      have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hf1.size IW]; exact hsz
      have hc1 : 200 < (m1.arr64 CTL).size := by rw [hf1.size CTL]; exact hc
      obtain ⟨hr2, hdec2, hg2, hf2, hl1, htop2⟩ :=
        consW_dec hcons hsz1 hc1 hle1 hty2 hdec1
      have hk : fuel.toNat = (fuel.toNat - 1) + 1 := by
        have : fuel.toNat ≠ 0 := fun h0 => hf (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      refine ⟨decE ((eViewW m h).getD 1 0) :: bs1, e1, ?_, ?_, ?_, ?_, ?_, hg1.trans hg2,
        hf1.trans hf2, ?_⟩
      · rw [hk, ConRon.Arena.piBinders, (decE_tag_forallE h hh).mpr hg6]
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
  simp only [hd?, iwA, aread_apply, aread_apply]
  rw [hg.iwGet (o + j) (by omega)]

/-- A returning `e_view` of a `const` handle. -/
theorem eViewW_const (m : Mem) (h : Word) (hg : tagW h = 3) (hne : eViewW m h ≠ []) :
    viewOK m h CONST ∧ eViewW m h = [3, tfld m CONST (tierW h) (idxW h) 0,
      tfld m CONST (tierW h) (idxW h) 1, 0] := by
  unfold eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, ite_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, ite_false] at hne ⊢
  have n0 : ¬ tagW h = 0 := by rw [hg]; decide
  have n1 : ¬ tagW h = 1 := by rw [hg]; decide
  have n2 : ¬ tagW h = 2 := by rw [hg]; decide
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
  simp only [ETables.getConst, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
  rw [hk]
  simp [hn, hu, decI_word]

/-! ## `rec_target_of` -/

/-- **`rec_target_of` is its model `recTW`** (generated): strip the telescope, look at the
major's domain head. -/
l_model recTargetOf_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "rec_target_of" = some recTargetOf)
    (hst : StripProg p) (had : AdF p)
  fns [hp ↦ recTW list]
  specs [stripPis_specF p hst n, gafF_spec p had n, eViewSpec4 p hv n, slFind_spec p hf n]
  grind [arena_grind, ind_grind]

theorem recTW_ok (n : Nat) : ∀ (_dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl mI ty : Word) (r : List Word) (names : List NIdx),
    recTW n m no nl mI ty = some (r, m') → StageR vis fe m a → ty.toNat < 2 ^ 32 →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat < 2 ^ 64 →
    no.toNat + nl.toNat ≤ iwTop m →
    ∃ t a', (ConRon.Arena.recTargetOf names mI.toNat (decI ty)).run a = .ok (t, a') ∧
      r = [UInt64.ofNat t] ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  intro _dn fe vis m m' a no nl mI ty r names hrt hS hty hnames hb hbt
  cases n with
  | zero => simp [recTW] at hrt
  | succ n =>
  have hnl : nl.toNat = names.length := (decHL_length m hnames).symm
  have hnlw : [UInt64.ofNat names.length] = [nl] := by rw [← hnl, ofNat_toNat_word nl]
  rw [recTW.arm1] at hrt
  obtain ⟨r1, m1, hra, hrt⟩ := ipK_inv hrt (by simp [recTW.k_strip_pis])
  obtain ⟨x1, a1, hrun1, hS1, hg1, hdec1⟩ := stripF_pis_ok vis fe mI ty hty m m1 a r1 hra hS
  have hty' : (decI ty : EIdx) = decE ty := rfl
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hdec1
    rw [recTW.k_strip_pis.arm1 n no nl r1 m1 h0] at hrt
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
    have hR1 : ArenaR m1 a1 := hS1.check.arena.base
    have hnamesz : names.length = nl.toNat := hnl.symm
    by_cases hg6 : tagW (r1.tail.tail.tail.headD 0) ≠ 6
    · rw [recTW.k_strip_pis.arm2 n no nl r1 m1 h1ne hg6] at hrt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrt)
      have htag : e1.tag ≠ ETag.forallE := by
        rw [← hbe]; exact fun h' => hg6 ((decE_tag_forallE _ hbl).mp h')
      refine ⟨names.length, a1, ?_, hnlw.symm, hS1, hg1⟩
      · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind]
        simp [htag]
        rfl
    · have hg6' : tagW (r1.tail.tail.tail.headD 0) = 6 := by simpa using hg6
      by_cases hr : eViewW m1 (r1.tail.tail.tail.headD 0) = []
      · rw [recTW.k_strip_pis.abort1 n no nl r1 m1 h1ne hg6' hr] at hrt; cases hrt
      obtain ⟨hvok, hew⟩ := eViewW_forall m1 _ hg6' hr
      rw [recTW.k_strip_pis.arm3 n no nl r1 m1 h1ne hg6' hr] at hrt
      obtain ⟨hvw, hty2, hb2⟩ := view_forall m1 a1 hR1 _ hbl hvok hg6'
      have hdomw : (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0 =
          tfld m1 FORALL (tierW (r1.tail.tail.tail.headD 0)) (idxW (r1.tail.tail.tail.headD 0)) 0 := by rw [hew]; rfl
      have hdomlt : ((eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0).toNat < 2 ^ 32 := by
        rw [hdomw]; exact hty2
      obtain ⟨r3, m3, hra3, hrt⟩ := ipK_inv hrt (by simp [recTW.k_get_app_fn_f])
      obtain ⟨x3, a3, hrun3, hS3, hg3, hdl3, hdI3⟩ :=
        gafF_ok vis fe CWF _ hdomlt m1 m3 a1 r3 hra3 hS1
      have hR3 : ArenaR m3 a3 := hS3.check.arena.base
      have hvb := viewBind_forall m1 a1 hR1 _ hbl hvok hg6'
      have hrun3' : StateT.run (getAppFn coreWalkFuel (decE
          ((eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0))) a1 = Except.ok (x3, a3) := by
        rw [← CWF_eq]; exact hrun3
      subst hbe
      have hvb' : a1.store.viewBind (decI (r1.tail.tail.tail.headD 0)) = some
          (decE ((eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0),
           decE ((eViewW m1 (r1.tail.tail.tail.headD 0)).getD 2 0)) := by
        rw [hew]; exact hvb
      have hftag : ((decI (r1.tail.tail.tail.headD 0) : EIdx).tag == ETag.forallE) = true := by
        simp only [beq_iff_eq]; exact (decE_tag_forallE _ hbl).mpr hg6'
      by_cases hc : tagW (r3.headD 0) ≠ 3
      · rw [recTW.k_get_app_fn_f.arm1 n no nl r3 m3 hc] at hrt
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
      · have hc3 : tagW (r3.headD 0) = 3 := by simpa using hc
        by_cases hr2 : eViewW m3 (r3.headD 0) = []
        · rw [recTW.k_get_app_fn_f.abort1 n no nl r3 m3 hc3 hr2] at hrt; cases hrt
        obtain ⟨hvok2, hew2⟩ := eViewW_const m3 _ hc3 hr2
        rw [recTW.k_get_app_fn_f.arm2 n no nl r3 m3 hc3 hr2] at hrt
        obtain ⟨hvc, hn2, hu2⟩ := view_const_f m3 a3 hR3 _ hdl3 hvok2 hc3
        have hxw : (eViewW m3 (r3.headD 0)).tail.headD 0 =
            tfld m3 CONST (tierW (r3.headD 0)) (idxW (r3.headD 0)) 0 := by
          rw [hew2]; rfl
        have hxlt : ((eViewW m3 (r3.headD 0)).tail.headD 0).toNat < 2 ^ 32 := by rw [hxw]; exact hn2
        have hvcc := viewConst_ok m3 a3 hR3 _ hdl3 hvok2
        have hnames3 : decHL m3 no.toNat nl.toNat = some names := by
          rw [decHL_grow3 (hg1.trans hg3) hbt]; exact hnames
        obtain ⟨ws, hws, hnm, hwlt⟩ := slR_of_decHL m3 nl.toNat no.toNat names hnames3 hb
        rw [ofNat_toNat_word, ofNat_toNat_word] at hws
        have hlen : ws.length < 2 ^ 64 := by
          have := decHL_length m3 hnames3
          rw [hnm] at this; simp at this; omega
        rcases hf : findW n m3 no nl ((eViewW m3 (r3.headD 0)).tail.headD 0) with _ | rf
        · rw [hf] at hrt; simp [recTW.k_sl_find] at hrt
        have hfk := findW_ok n m3 no nl _ rf ws hws hf hlen
        have hfi := findIdx_map_decI (k := .name) _ hxlt ws hwlt
        rw [← hnm] at hfi
        have hctag : (x3.tag == ETag.const) = true := by
          simp only [beq_iff_eq]; rw [← hdI3]; exact (decE_tag_const _ hdl3).mpr hc3
        have hvcc' : a3.store.viewConst x3 = some
            (decI ((eViewW m3 (r3.headD 0)).tail.headD 0), decI ((eViewW m3 (r3.headD 0)).getD 2 0)) := by
          rw [← hdI3, hew2]; exact hvcc
        rw [hf] at hrt
        by_cases hf0 : rf.headD 0 = 0
        · rw [recTW.k_sl_find.arm1 nl m3 rf hf0] at hrt
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrt)
          have hnone : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).tail.headD 0) = none := by
            rw [hfk] at hf0
            cases h' : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).tail.headD 0) with
            | none => rfl
            | some i => rw [h'] at hf0; simp at hf0
          refine ⟨names.length, a3, ?_, hnlw.symm, hS3, hg1.trans hg3⟩
          · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind, hftag,
              ite_true, viewBind_run' _ a1, hvb', hrun3', hctag, viewConst_run', hvcc', hfi, hnone]
            rfl
        · rw [recTW.k_sl_find.arm2 nl m3 rf hf0] at hrt
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrt)
          obtain ⟨i, hi⟩ : ∃ i, ws.findIdx? (· == (eViewW m3 (r3.headD 0)).tail.headD 0) = some i := by
            rw [hfk] at hf0
            cases h' : ws.findIdx? (· == (eViewW m3 (r3.headD 0)).tail.headD 0) with
            | none => rw [h'] at hf0; simp at hf0
            | some i => exact ⟨i, rfl⟩
          refine ⟨i, a3, ?_, ?_, hS3, hg1.trans hg3⟩
          · simp only [ConRon.Arena.recTargetOf, StateT.run_bind, hrun1, except_ok_bind, hftag,
              ite_true, viewBind_run' _ a1, hvb', hrun3', hctag, viewConst_run', hvcc', hfi, hi]
            rfl
          · rw [hfk, hi]; rfl

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

theorem decCVp_type {m : Mem} {q : Word} {cv : IConstantVal} (h : decCVp m q.toNat = some cv)
    (hb : q.toNat + 3 < 2 ^ 64) :
    (erRd m (q + 3)).toNat < 2 ^ 32 ∧ decE (erRd m (q + 3)) = cv.type := by
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, -, lv, -, ty, hty, hcv⟩ := h
  have hty' : ty = cv.type := by rw [← hcv]
  have e : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  rcases hw : erA m (q.toNat + 3) with _ | w
  · simp [hd?, hw] at hty
  have hrd : erRd m (q + 3) = w := erRd_of_erA (by rw [e]; exact hw)
  by_cases hl : w.toNat < 2 ^ 32
  · simp [hd?, hw, hl] at hty
    rw [hrd]
    exact ⟨hl, by rw [← hty', ← hty]; rfl⟩
  · simp [hd?, hw, hl] at hty

end L.Ind

end
