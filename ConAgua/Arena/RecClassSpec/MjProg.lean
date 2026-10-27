import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndRealOpf
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.IndDecStab

/-!
# MjProg

`rec2IwN_trunc`, `rec2IwH_trunc`, `rec2CG_parts`, `rec2DecTM_parts`, `TMR`, `MjProg` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Reading below the tops -/

theorem rec2IwN_trunc {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) :
    i < iwTop m ∧ iwN m i = some v := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨hi, by simp [iwN, nat?, hw']⟩

theorem rec2IwH_trunc {k : IdxKind} {m : Mem} {i : Nat} {x : Idx k} (h : iwH (truncM m) i = some x) :
    i < iwTop m ∧ iwH m i = some x := by
  obtain ⟨w, hw, hl, hx⟩ := hd?_some h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  refine ⟨hi, ?_⟩
  simp only [iwH, hd?, iwA] at hw' ⊢
  simp [hw', hl, hx]

/-- The fields of a class generator decoded below the tops. -/
theorem rec2CG_parts {m : Mem} {g : Nat} {G : ClassGen} (h : DecB (fun m => decCG m g) m G) :
    iwN m g = some G.nP ∧ g + 13 < iwTop m ∧
    (∃ o l, iwN m (g + 3) = some o ∧ iwN m (g + 4) = some l ∧
      DecB (fun m => decPL m (decTM m) o l) m G.cls) ∧
    (∃ o l, iwN m (g + 5) = some o ∧ iwN m (g + 6) = some l ∧
      DecB (fun m => (decHL m o l : Option (List EIdx))) m G.formerTys) ∧
    iwH m (g + 11) = some G.elim ∧
    (∃ o l, iwN m (g + 12) = some o ∧ iwN m (g + 13) = some l ∧
      DecB (fun m => (decHL m o l : Option (List EIdx))) m G.pre) := by
  have h' : decCG (truncM m) g = some G := h
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, rfl⟩ := h'
  obtain ⟨o3, l3, h3, h4, hc⟩ := decAt_some hcls
  obtain ⟨o5, l5, h5, h6, hf⟩ := decAt_some hft
  obtain ⟨o12, l12, h12, h13, hp⟩ := decAt_some hpre
  refine ⟨(rec2IwN_trunc hnP).2, (rec2IwN_trunc h13).1, ⟨o3, l3, (rec2IwN_trunc h3).2,
    (rec2IwN_trunc h4).2, hc⟩, ⟨o5, l5, (rec2IwN_trunc h5).2, (rec2IwN_trunc h6).2, hf⟩,
    (rec2IwH_trunc hel).2, ⟨o12, l12, (rec2IwN_trunc h12).2, (rec2IwN_trunc h13).2, hp⟩⟩

theorem rec2DecTM_parts {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m p = some M.ind ∧ iwH m (p + 1) = some M.lvls ∧
    (∃ o l, iwN m (p + 2) = some o ∧ iwN m (p + 3) = some l ∧ decHL m o l = some M.ds) ∧
    iwN m (p + 4) = some M.nPc ∧ iwN m (p + 5) = some M.nIdx := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, ds, hds, w4, h4, w3, h3, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact ⟨h5, ha1, decAt_some hds, h4, h3⟩

/-- `target_major_at`'s record: decoded, its `ds` slice decoded below the tops. -/
def TMR (m' : Mem) (q : Nat) (tm : TargetMajor) : Prop :=
  decTM m' q = some tm ∧
    ∀ o l, iwN m' (q + 2) = some o → iwN m' (q + 3) = some l →
      DecB (fun m => (decHL m o l : Option (List EIdx))) m' tm.ds

/-! ## `class_gen_major`: the model -/

/-- The lookups `class_gen_major` needs. -/
structure MjProg (p : Prog) : Prop where
  ad : AdF p
  hi1 : I1Prog p
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  app : p.lookup "sl_append" = some slAppend
  pw : p.lookup "pin_word" = some pinWordL
  mtm : p.lookup "mk_target_major" = some mkTargetMajor
  tmd : p.lookup "target_major_default" = some targetMajorDefault
  tma : p.lookup "target_major_at" = some targetMajorAt
  na : NaF p
  bf : p.lookup "bvar_find" = some bvarFind
  bp : p.lookup "bvar_push" = some bvarPush
  ib : p.lookup "intern_bvar" = some internBVar
  egd : p.lookup "expr_get_d" = some exprGetD
  ev : p.lookup "e_view" = some eView
  ipw : p.lookup "inst_pis_with" = some instPisWith
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  mjt : p.lookup "class_gen_major_tail" = some classGenMajorTail
  mci : p.lookup "class_gen_major_ci" = some classGenMajorCi
  mjo : p.lookup "class_gen_major_open" = some classGenMajorOpen
  mj : p.lookup "class_gen_major" = some classGenMajor
  opf : OpfF p

theorem rec2DecB_PL_top {α : Type} {f : Mem → Nat → Option α} {m : Mem} {o l : Nat} {xs : List α}
    (h : DecB (fun m => decPL m (f m) o l) m xs) (hl : l ≠ 0) : o + l ≤ iwTop m := by
  obtain ⟨v, hv, -⟩ := decPL_getH (truncM m) h (l - 1) (by omega)
  have := (rec2IwN_trunc hv).1
  omega

/-- A word read at a decoded record field. -/
theorem rec2RdN {m : Mem} {w : Word} {k v : Nat} (h : iwN m (w.toNat + k) = some v)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    rdW (m.arr64 IW) (w + UInt64.ofNat k) = UInt64.ofNat v ∧ (UInt64.ofNat v : Word).toNat = v := by
  have := iwN_rdW_at h hsz
  exact ⟨this.1, UInt64.toNat_ofNat_of_lt' this.2⟩

theorem rec2MapM_genBinder (g : ClassGen) : ∀ xs : List EIdx, xs.mapM g.binder = fvarTypeDs xs
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, fvarTypeDs, ConRon.Arena.ClassGen.binder, rec2MapM_genBinder g xs]

/-- The lookups `class_gen_motive_ty` needs. -/
structure MtProg (p : Prog) : Prop extends MjProg p where
  sf : p.lookup "sort_find" = some sortFind
  sp : p.lookup "sort_push" = some sortPush
  isort : p.lookup "intern_sort" = some internSort
  db : p.lookup "der_b" = some derB
  ff : p.lookup "forall_find" = some forallFind
  fp : p.lookup "forall_push" = some forallPush
  ifa : p.lookup "intern_forall" = some internForallL
  mkf : p.lookup "mk_forall" = some mkForall
  ct : p.lookup "close_telescope" = some closeTelescope
  ab : AbF p
  mot : p.lookup "class_gen_motive_ty" = some classGenMotiveTy

end L.Ind

end
