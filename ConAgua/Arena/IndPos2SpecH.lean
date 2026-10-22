import ConAgua.Arena.IndPos2SpecG
import ConAgua.Arena.IndInstallSpec3
import ConAgua.Arena.WhnfCoreProj

/-! # `IndPos2`'s leaves, continued (lane `indproofs2`, helper `pos`, fork E): `nestInstType`
(with `nest_occ_any`, `nest_inst_type_ty`), `nestGrowGroup`. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_occ_any`: `xs.anyM (nestOcc names lo hi ·)` -/

mutual
def noaW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, lo, hi, off, l =>
    if l = 0 then some ([0], m) else noaK k no nl lo hi off l (noConstWf k m no nl lo hi (rdW (m.arr64 IW) off))
def noaK (k : Nat) (no nl lo hi off l : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m1) => if b ≠ 0 then some ([1], m1) else noaW k m1 no nl lo hi (off + 1) (l - 1)
end

section arms
variable (k : Nat) (m m1 : Mem) (no nl lo hi off l b : Word)
theorem noaW_nil (h : l = 0) : noaW (k + 1) m no nl lo hi off l = some ([0], m) := by simp [noaW, h]
theorem noaW_cons (h : ¬ l = 0) : noaW (k + 1) m no nl lo hi off l =
    noaK k no nl lo hi off l (noConstWf k m no nl lo hi (rdW (m.arr64 IW) off)) := by simp [noaW, h]
theorem noaK_hit (h : b ≠ 0) : noaK k no nl lo hi off l (some (b, m1)) = some ([1], m1) := by rw [noaK, if_pos h]
theorem noaK_miss (h : ¬ b ≠ 0) : noaK k no nl lo hi off l (some (b, m1)) =
    noaW k m1 no nl lo hi (off + 1) (l - 1) := by rw [noaK, if_neg h]
end arms
attribute [ind_grind] noaW_nil noaW_cons noaK_hit noaK_miss

theorem nestOccAny_spec (p : Prog) (hl : NoLook p) (hp : p.lookup "nest_occ_any" = some nestOccAnyL)
    (k : Nat) : ∀ (s₀ : St) (no nl lo hi off ln : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_occ_any" [no, nl, lo, hi, off, ln]
    ⦃fun r s' => LocEq s' s₀ ∧ noaW k s₀.mem no nl lo hi off ln = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ no nl lo hi off ln
    rw [invoke_eq _ hp]; simp only [callFn, nestOccAnyL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ no nl lo hi off ln
    rw [invoke_eq _ hp]
    simp only [callFn, nestOccAnyL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nestOcc_spec' p hl k, ih] <;>
      finish (gen := 20) [Locals.init_cons_zero]

theorem noaW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis no nl lo hi : Word) (names : List NIdx)
    (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (xs : List EIdx) (r : List Word),
    noaW k m no nl lo hi off l = some (r, m') → StageR dn vis fe m a →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat ≤ iwTop m →
    decHL m off.toNat l.toNat = some xs → (∀ j < l.toNat, off.toNat + j < iwTop m) → PosMR m →
    ∃ b, (xs.anyM (fun x => ConRon.Arena.nestOcc names lo.toNat hi.toNat x)).run a = .ok (b, a) ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' := by
  induction k with
  | zero => intro m m' a off l xs r h; simp [noaW] at h
  | succ k ih =>
    intro m m' a off l xs r h hS hn hnb hxs hxb hP
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hl0 : l = 0
    · rw [noaW_nil (h := hl0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hl0
      have : xs = [] := by simpa [decHL, hslice?] using hxs.symm
      subst this
      exact ⟨false, rfl, hS, IWGrow.refl _, rfl, hP⟩
    rw [noaW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hxs2 := hxs
    simp only [decHL] at hxs2
    rw [hl', hslice?_succ] at hxs2
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hxs2
    obtain ⟨x, hx, xs', hxs', rfl⟩ := hxs2
    obtain ⟨hxH, hxd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.expr) (by simpa [iwH, iwA] using hx)
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hxb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨mp0, hM0⟩ := hP.no
    cases hno : noConstWf k m no nl lo hi (rdW (m.arr64 IW) off) with
    | none => rw [hno] at h; simp [noaK] at h
    | some pr =>
    obtain ⟨b1, m1⟩ := pr
    rw [hno] at h
    obtain ⟨c1, hrun1, hc1, hM1, hS1, hg1, hf1⟩ := noConstWf_ok k dn fe vis m m1 a no nl lo hi _ b1 names mp0 hno hS hxH
      hn (by omega) hM0
    have hP1 := hP.setNo hf1 ⟨∅, hM1⟩
    rw [decE_eq, hxd] at hrun1
    rw [List.anyM_cons]
    by_cases hb : b1 ≠ 0
    · rw [noaK_hit (h := hb)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : c1 = true := by rw [← hc1]; simpa using hb
      subst this
      refine ⟨true, ?_, hS1, hg1, rfl, hP1⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, if_true]; rfl
    · rw [noaK_miss (h := hb)] at h
      have : c1 = false := by rw [← hc1]; simpa using hb
      subst this
      obtain ⟨b, hrun, hS', hg', hr, hP'⟩ := ih m1 m' a (off + 1) (l - 1) xs' r h hS1
        (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hn) (by have := hg1.1; omega)
        (by rw [hoff1, hl1, decHL_agree (RdS.of_grow hg1) (fun j hj => by have := hxb (j + 1) (by omega); omega)]
            simpa [decHL] using hxs')
        (fun j hj => by rw [hoff1, hl1] at *; have := hxb (j + 1) (by omega); have := hg1.1; omega) hP1
      refine ⟨b, ?_, hS', hg1.trans hg', hr, hP'⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, if_false]
      exact hrun


/-! ## `nest_inst_type(_ty)`: word models -/

theorem viewLsLen_specE (p : Prog) (hl : p.lookup "ls_node" = some lsNode)
    (hp : p.lookup "view_ls_len" = some viewLsLenL) (n : Nat) (s₀ : St) (us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "view_ls_len" [us]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ lsNodeW s₀.mem us ≠ [] ∧
      r = [1, (lsNodeW s₀.mem us).tail.headD 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, viewLsLenL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lsNode_spec p hl n] <;>
      finish (gen := 20)

def ntyK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => if r6.headD 0 = 0 then none else some ([r6.tail.headD 0], m6)
def ntyK5 (k : Nat) (key : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => ntyK6 (instW k m5 (rdW (m5.arr64 IW) (key + 2)) (rdW (m5.arr64 IW) (key + 3)) (r5.headD 0))
def ntyK4 (k : Nat) (key cvC : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ntyK5 k key (stubM "inst_lp_fast" m4 [CWF, r4.headD 0, r4.tail.headD 0,
      rdW (m4.arr64 IW) (key + 1), rdW (m4.arr64 EREC) (cvC + 3)])
def ntyK3 (k : Nat) (key cvC : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => if r3.headD 0 = 0 then none else ntyK4 k key cvC (cvLpsW k m3 cvC)
def ntyK1 (k : Nat) (key : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then none
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then none
    else if lsNodeW m1 (rdW (m1.arr64 IW) (key + 1)) = [] then none
    else if (lsNodeW m1 (rdW (m1.arr64 IW) (key + 1))).tail.headD 0 ≠
        rdW (m1.arr64 EREC) (r.tail.headD 0 + 1 + 2) then none
    else ntyK3 k key (r.tail.headD 0 + 1) (stubM "strip_pis" m1 [rdW (m1.arr64 IW) (key + 3),
      rdW (m1.arr64 EREC) (r.tail.headD 0 + 1 + 3)])
/-- The model of `nest_inst_type_ty(vis, key)` at exec fuel `k + 1`. -/
def ntyW (k : Nat) (m : Mem) (vis key : Word) : Option (List Word × Mem) :=
  ntyK1 k key (envFindW m (rdW (m.arr64 IW) key) vis)

section arms
variable (k : Nat) (m1 m3 m4 m5 m6 : Mem) (key cvC : Word) (r r3 r4 r5 r6 : List Word)
theorem ntyK6_none (h : r6.headD 0 = 0) : ntyK6 (some (r6, m6)) = none := by rw [ntyK6, if_pos h]
theorem ntyK6_some (h : ¬ r6.headD 0 = 0) : ntyK6 (some (r6, m6)) = some ([r6.tail.headD 0], m6) := by
  rw [ntyK6, if_neg h]
theorem ntyK5_some : ntyK5 k key (some (r5, m5)) =
    ntyK6 (instW k m5 (rdW (m5.arr64 IW) (key + 2)) (rdW (m5.arr64 IW) (key + 3)) (r5.headD 0)) := rfl
theorem ntyK4_some : ntyK4 k key cvC (some (r4, m4)) = ntyK5 k key (stubM "inst_lp_fast" m4 [CWF, r4.headD 0,
    r4.tail.headD 0, rdW (m4.arr64 IW) (key + 1), rdW (m4.arr64 EREC) (cvC + 3)]) := rfl
theorem ntyK3_none (h : r3.headD 0 = 0) : ntyK3 k key cvC (some (r3, m3)) = none := by rw [ntyK3, if_pos h]
theorem ntyK3_some (h : ¬ r3.headD 0 = 0) : ntyK3 k key cvC (some (r3, m3)) = ntyK4 k key cvC (cvLpsW k m3 cvC) := by
  rw [ntyK3, if_neg h]
theorem ntyK1_eq (r : List Word) (m1 : Mem) : ntyK1 k key (some (r, m1)) =
    if r.headD 0 = 0 then none
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then none
    else if lsNodeW m1 (rdW (m1.arr64 IW) (key + 1)) = [] then none
    else if (lsNodeW m1 (rdW (m1.arr64 IW) (key + 1))).tail.headD 0 ≠
        rdW (m1.arr64 EREC) (r.tail.headD 0 + 1 + 2) then none
    else ntyK3 k key (r.tail.headD 0 + 1) (stubM "strip_pis" m1 [rdW (m1.arr64 IW) (key + 3),
      rdW (m1.arr64 EREC) (r.tail.headD 0 + 1 + 3)]) := rfl
end arms
attribute [ind_grind] ntyK6_none ntyK6_some ntyK5_some ntyK4_some ntyK3_none ntyK3_some ntyK1_eq

/-- The lookups of `nest_inst_type_ty`. -/
structure NtyLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hls : p.lookup "ls_node" = some lsNode
  hvl : p.lookup "view_ls_len" = some viewLsLenL
  hc : p.lookup "er_copy" = some erCopy
  he : p.lookup "er_to_iw" = some erToIw
  hcv : p.lookup "cv_lps" = some cvLps
  hv : p.lookup "e_view" = some eView
  hip : p.lookup "inst_pis_with" = some instPisWith
  hp : p.lookup "nest_inst_type_ty" = some nestInstTypeTyL

theorem nestInstTypeTy_spec (p : Prog) (hl : NtyLook p) (k : Nat) (s₀ : St) (vis key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_inst_type_ty" [vis, key]
    ⦃fun r s' => LocEq s' s₀ ∧ ntyW k s₀.mem vis key = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hl.hp]
  simp only [callFn, nestInstTypeTyL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      envFind_specW p hl.hx hl.hg hl.hf k, viewLsLen_specE p hl.hls hl.hvl k,
      stubM_spec p "strip_pis" k, cvLps_spec p hl.ha hl.hc hl.he hl.hcv k,
      stubM_spec p "inst_lp_fast" k, instPisWith_spec p hl.hv hl.hip k] <;>
    finish (gen := 20) [ntyW, rdW_eq, Locals.init_cons_zero]


/-- `nest_inst_type_ty` at any exec fuel. -/
def ntyWf : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, vis, key => ntyW k m vis key

theorem nestInstTypeTy_spec' (p : Prog) (hl : NtyLook p) (k : Nat) (s₀ : St) (vis key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_inst_type_ty" [vis, key]
    ⦃fun r s' => LocEq s' s₀ ∧ ntyWf k s₀.mem vis key = some ([r.headD 0], s'.mem); ⊤⦄ := by
  cases k with
  | zero => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | succ k => exact nestInstTypeTy_spec p hl k s₀ vis key

def nitK5 (ty : Word) (rs : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => if r5.headD 0 = 0 then none else some ([rs.getD 1 0, ty], m5)
def nitK4 (ctx ty : Word) (rs v : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 ≠ 0 then none else nitK5 ty rs (lveW m4 (v.tail.headD 0) (rdW (m4.arr64 IW) (ctx + 9)))
def nitK2 (k : Nat) (ctx hi ty : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m2) =>
    if eViewW m2 (rs.getD 2 0) = [] then none
    else if (eViewW m2 (rs.getD 2 0)).headD 0 ≠ 2 then none
    else nitK4 ctx ty rs (eViewW m2 (rs.getD 2 0))
      (noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
        (rs.headD 0) (rs.getD 1 0))
def nitK1 (k : Nat) (ctx hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => nitK2 k ctx hi (r1.headD 0) (piBW k m1 CWF (r1.headD 0))
/-- The model of `nest_inst_type(vis, ctx, hi, key)` at exec fuel `k + 1`. -/
def nitW (k : Nat) (m : Mem) (vis ctx hi key : Word) : Option (List Word × Mem) :=
  nitK1 k ctx hi (ntyWf k m vis key)

section arms
variable (k : Nat) (m1 m2 m4 m5 : Mem) (ctx hi ty : Word) (r1 rs r4 r5 v : List Word)
theorem nitK5_none (h : r5.headD 0 = 0) : nitK5 ty rs (some (r5, m5)) = none := by rw [nitK5, if_pos h]
theorem nitK5_some (h : ¬ r5.headD 0 = 0) : nitK5 ty rs (some (r5, m5)) = some ([rs.getD 1 0, ty], m5) := by
  rw [nitK5, if_neg h]
theorem nitK4_occ (h : r4.headD 0 ≠ 0) : nitK4 ctx ty rs v (some (r4, m4)) = none := by rw [nitK4, if_pos h]
theorem nitK4_ok (h : ¬ r4.headD 0 ≠ 0) : nitK4 ctx ty rs v (some (r4, m4)) =
    nitK5 ty rs (lveW m4 (v.tail.headD 0) (rdW (m4.arr64 IW) (ctx + 9))) := by rw [nitK4, if_neg h]
theorem nitK2_eq : nitK2 k ctx hi ty (some (rs, m2)) =
    if eViewW m2 (rs.getD 2 0) = [] then none
    else if (eViewW m2 (rs.getD 2 0)).headD 0 ≠ 2 then none
    else nitK4 ctx ty rs (eViewW m2 (rs.getD 2 0))
      (noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
        (rs.headD 0) (rs.getD 1 0)) := rfl
theorem nitK1_some : nitK1 k ctx hi (some (r1, m1)) = nitK2 k ctx hi (r1.headD 0) (piBW k m1 CWF (r1.headD 0)) := rfl
end arms
attribute [ind_grind] nitK5_none nitK5_some nitK4_occ nitK4_ok nitK2_eq nitK1_some

/-- The lookups of `nest_inst_type`. -/
structure NitLook (p : Prog) : Prop where
  ty : NtyLook p
  no : NoLook p
  hc2 : p.lookup "iw_copy" = some iwCopy
  hs : p.lookup "sl_cons" = some slCons
  hpb : p.lookup "pi_binders" = some piBinders
  hoa : p.lookup "nest_occ_any" = some nestOccAnyL
  hlf : p.lookup "lvl_eq_fueled" = some lvlEqFueled
  hp : p.lookup "nest_inst_type" = some nestInstTypeL

theorem nestInstType_spec (p : Prog) (hl : NitLook p) (k : Nat) (s₀ : St) (vis ctx hi key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_inst_type" [vis, ctx, hi, key]
    ⦃fun r s' => LocEq s' s₀ ∧ nitW k s₀.mem vis ctx hi key = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hl.hp]
  simp only [callFn, nestInstTypeL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      nestInstTypeTy_spec' p hl.ty k, piBinders_spec p hl.ty.ha hl.hc2 hl.ty.hv hl.hs hl.hpb k,
      eView_spec p hl.ty.hv k, nestOccAny_spec p hl.no hl.hoa k, lvlEqFueled_spec p hl.hlf k] <;>
    finish (gen := 20) [nitW, rdW_eq, Locals.init_cons_zero, List.getD_cons_zero, List.getD_cons_succ]

end L.Ind
