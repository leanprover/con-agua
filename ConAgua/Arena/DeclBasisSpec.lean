module

import ConAgua.Arena.DeclValRef
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.DeclRec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndPosSpec.EnvFindWHit
public import ConAgua.Arena.DeclBase
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.Verdict
public import ConAgua.Checker.NoVerdictFns
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.Pins
import ConAgua.L.WordOff

@[expose] public section

/-!
# Pin reads, `of_reduce_op`, `install_basis_decl(s)` (lane `decls3`)

* `pin_at(i)`'s twin read (`pinAtW_ok`; the model `pinAtW` is `DeclRec.lean`'s).
* `of_reduce_op(n)` refines `ofReduceOp` (pin reads only).
* `install_basis_decl(vis, c)` refines `installBasisDecl` (the duplicate check, the push) and
  `install_basis_decls(vis, o, l)` refines `installBasisDecls` (an `IW` slice of constant-record
  pointers).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-! ## `pin_at(i)` -/

/-- **A pin read is the twin's** (`pinAt`), the memory unchanged. -/
theorem pinAtW_ok {m m' : Mem} {a : AState} {i : Word} {r : List Word}
    (h : pinAtW m i = some (r, m')) (hP : PinsR m a.pins) (h51 : i ≠ 51 := by decide) :
    m' = m ∧ r = [pinW m (1 + i.toNat)] ∧ (pinW m (1 + i.toNat)).toNat < 2 ^ 32 ∧
      (pinAt i.toNat).run a = .ok (decI (pinW m (1 + i.toNat)), a) := by
  unfold pinAtW at h
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at h
  rw [ite_eq_right h0] at h
  by_cases hi : 52 ≤ i
  · simp [hi] at h
  rw [ite_eq_right hi, ite_eq_right h51] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hF := hP.full h0
  have hi' : i.toNat < 51 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hi)
    have : i.toNat ≠ 51 := fun e => h51 (UInt64.toNat_inj.mp (by simpa using e))
    simp at *; omega
  have e : rdW (m.arr64 PINS) (1 + i) = pinW m (1 + i.toNat) := by
    simp only [rdW, pinW]
    congr 2
    rw [UInt64.toNat_add]; simp; omega
  rw [e]
  exact ⟨rfl, rfl, hF.names_lt i.toNat hi', pinAt_run hF i.toNat hi'⟩

/-- **Slot `51`'s read is the twin's** (`pinAt 51`, word `71`), the memory unchanged. -/
theorem pinAtW_ok51 {m m' : Mem} {a : AState} {r : List Word}
    (h : pinAtW m 51 = some (r, m')) (hP : PinsR m a.pins) :
    m' = m ∧ r = [pinW m 71] ∧ (pinW m 71).toNat < 2 ^ 32 ∧
      (pinAt 51).run a = .ok (decI (pinW m 71), a) := by
  unfold pinAtW at h
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at h
  simp only [h0, ite_false, show ¬ (52 : Word) ≤ 51 by decide, ite_true, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hF := hP.full h0
  exact ⟨rfl, rfl, hF.quotMk_lt, pinAt_run51 hF⟩

/-! ## `of_reduce_op(n)` -/

l_model oro_specW (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "of_reduce_op" = some ofReduceOpL)
  fns [hp ↦ oroW list]
  specs [pinAt_specW p hpa n]
  grind [arena_grind]

/-- The last pin read of `of_reduce_op`: its first word. -/
theorem oroW_k2 {x : Option (List Word × Mem)} {r : List Word} {m' : Mem}
    (h : oroW.k_pin_at_2 x = some (r, m')) : ∃ r0, x = some (r0, m') ∧ r = [r0.headD 0] := by
  rcases x with _ | ⟨r0, m0⟩
  · rw [oroW.k_pin_at_2.none] at h; cases h
  · rw [oroW.k_pin_at_2.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨r0, rfl, rfl⟩

theorem oroW_ok {m m' : Mem} {a : AState} {w : Word} {r : List Word}
    (h : oroW m w = some (r, m')) (hP : PinsR m a.pins) (hw : w.toNat < 2 ^ 32) :
    m' = m ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (ofReduceOp (decI w)).run a = .ok (decI (r.headD 0), a) := by
  rw [oroW.arm1] at h
  cases h1 : pinAtW m 45 with
  | none => rw [h1, oroW.k_pin_at.none] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1] at h
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hP
  have hbeq : ((decI w : NIdx) == decI (pinW m (1 + (45 : Word).toNat))) =
      decide (w = pinW m (1 + (45 : Word).toNat)) := decI_beq w _ hw hl1
  have e1 : r1.headD 0 = pinW m (1 + (45 : Word).toNat) := by rw [hr1]; rfl
  by_cases he : w = r1.headD 0
  · rw [oroW.k_pin_at.arm1 w r1 m1 he, hm1] at h
    obtain ⟨r0, h2, rfl⟩ := oroW_k2 h
    obtain ⟨hm, hr, hl, hrun⟩ := pinAtW_ok h2 hP
    subst hr
    rw [e1] at he
    refine ⟨hm, hl, ?_⟩
    simp only [ofReduceOp, ofReduceNatName, pinOfReduceNat, reduceNatName, pinReduceNat,
      StateT.run_bind, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl, hrun1, exc_ok_bind', he]
    simpa [PIN_REDUCE_NAT, PIN_REDUCE_BOOL] using hrun
  · rw [oroW.k_pin_at.arm2 w r1 m1 he, hm1] at h
    obtain ⟨r0, h2, rfl⟩ := oroW_k2 h
    obtain ⟨hm, hr, hl, hrun⟩ := pinAtW_ok h2 hP
    subst hr
    rw [e1] at he
    refine ⟨hm, hl, ?_⟩
    simp only [ofReduceOp, ofReduceNatName, pinOfReduceNat, reduceBoolName, pinReduceBool,
      StateT.run_bind, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl, hrun1, exc_ok_bind',
      hbeq, he, decide_false, Bool.false_eq_true, ite_false]
    simpa [PIN_REDUCE_NAT, PIN_REDUCE_BOOL] using hrun

local notation "V" => ConLeche.CheckMode.verified

/-- **`of_reduce_op(n)` refines `ofReduceOp`** (pin reads; the memory unchanged). -/
@[refines ConRon.Arena.ofReduceOp]
theorem ofReduceOp_refines (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "of_reduce_op" = some ofReduceOpL) (n : Nat) (s₀ : St) (a₀ : AState)
    (_dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis w : Word)
    (hS : StageR vis fe s₀.mem a₀) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_op" [w]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ofReduceOp (decI w)) a₀ ∧
      KeepPost vis fe decW0N s₀.mem s'.mem (AM.st (ofReduceOp (decI w)) a₀) r
        (AM.res (ofReduceOp (decI w)) a₀); ⊤⦄ := by
  refine triple_post (oro_specW p hpa hp n s₀ w) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmem, hrl, hrun⟩ := oroW_ok hm hS.check.pins hw
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_, ?_, hrl, by rw [hres]⟩
  · rw [hst, hmem]; exact hS
  · rw [hmem]; exact IWGrow.refl _

/-! ## `install_basis_decl(vis, c)` and `install_basis_decls(vis, o, l)` -/

/-- The lookups the basis install needs. -/
structure BasisProg (p : Prog) : Prop where
  ibd : p.lookup "install_basis_decl" = some installBasisDeclL
  ibds : p.lookup "install_basis_decls" = some installBasisDeclsL
  rcp : RecProg p
  erg : p.lookup "env_row_get" = some envRowGetL
  brg : p.lookup "base_row_get" = some baseRowGetL
  ef : p.lookup "env_find" = some envFindL

/-- **`env_find(w, vis)` as a call**: the memory unchanged, the result the twin's `find?`. -/
theorem envFind_callB {p : Prog} (hB : BasisProg p) {vis : Word} {fe : IFEnv} {w : Word}
    (_hw : w.toNat < 2 ^ 32) {n : Nat} {m m' : Mem} {r : List Word}
    (_hE : EnvR m vis fe) (h : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ r = findRes m vis w := by
  obtain ⟨s', rfl, h1, -, h3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_spec p hB.erg hB.brg hB.ef n _ vis w) h
  exact ⟨h1, h3⟩

section models
variable (p : Prog)

/-- **The model of `install_basis_decl(vis, c)`, both outcomes**: `env_find`, `env_push`
(outside the verdict closure) through their `Option` models. -/
l_model installBasisDecl_specE (p : Prog) (hB : BasisProg p)
  fns [hB.ibd ↦ installBasisDeclE]
  specs [callW_spec p n "env_find", callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end models

/-! ### The relational lemmas -/

/-- The cut record pool is the record pool below its top. -/
theorem truncM_erecP (m : Mem) : ArrExt (erA (truncM m)) (erecP m) := by
  intro i v h
  exact truncM_er_get h

/-- What `install_basis_decl` gives besides the twin's environment `fe'` (from `m`): the stage
over the result word, the growth. -/
structure IbdPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : Word) (m' : Mem) (fe' : IFEnv)
    (a' : AState) : Prop where
  stage : StageR r fe' m' a'
  grow : IWGrow m m'

/-- **`install_basis_decl` refines `installBasisDecl`, both outcomes**: a duplicate declaration
rejects (`env_find` hits), else the push. -/
theorem ibd_ref {p : Prog} (hB : BasisProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {c : Word} {ci : IConstantInfo}
    (hS : StageR vis fe m a) (hci : decCI (erecP m) c.toNat = some ci) :
    RefE True (installBasisDeclE p n m vis c) (installBasisDecl fe ci) a
      (fun v fe' a' => IbdPost dn m v.1 v.2 fe' a') := by
  obtain ⟨w, hw1, hwl, hname⟩ := decCI_name hci
  have ew : rdW (m.arr64 (tierA EREC ((c + 1) >>> 40))) ((c + 1) &&& 1099511627775) = w :=
    (erRd_add (j := 1) hw1 (by omega)).1
  cases n with
  | zero => rw [installBasisDeclE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [installBasisDeclE.arm1, ew]
  refine RefE.onlySim (fun _ => installBasisDeclE.k_env_find.none ..) (fun _ _ h => h) fun r1 m1 h1 => ?_
  obtain ⟨rfl, rfl⟩ := envFind_callB hB hwl hS.check.env h1
  by_cases hb : (findRes m1 vis w).headD 0 ≠ 0
  · rw [installBasisDeclE.k_env_find.abort1 p _ _ _ _ _ hb]
    obtain ⟨-, ci', hci'⟩ := findRes_hit hS.check.env hwl hb
    have : (fe.find? ci.name).isSome = true := by
      rw [hname, (findRes_hit hS.check.env hwl hb).1, hci']; rfl
    simp only [installBasisDecl, fail_bindAM]
    exact fun _ => ErrClaim.ite_neg (by simp [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] at this ⊢; exact this)
      (ErrClaim.fail _ _ rfl)
  rw [installBasisDeclE.k_env_find.arm1 p _ _ _ _ _ (by simpa using hb)]
  have hfind := findRes_miss hS.check.env hwl (by simpa using hb)
  refine RefE.onlySim (fun _ => installBasisDeclE.k_env_push.none ..) (fun _ _ h => h) fun r2 m2 h2 => ?_
  rw [installBasisDeclE.k_env_push.arm1]
  obtain ⟨hS2, hg2⟩ := envPush_stage hB.rcp.rs hB.rcp.push h2 hS hci
  refine RefE.ret ?_ ⟨by simpa using hS2, hg2⟩
  simp [installBasisDecl, hname, hfind, StateT.run_pure]
  rfl


/-- The basis list's decoding: an `IW` slice of constant-record pointers. -/
def basisDec (_dn : NIdx → Option ConLeche.Name) (o l : Nat) (m : Mem) :
    Option (List IConstantInfo) :=
  decPL m (fun q => decCI (erA m) q) o l

theorem basisDec_mono (dn : NIdx → Option ConLeche.Name) (o l : Nat) :
    OMono (basisDec dn o l) :=
  OMono.decPL (f := fun m q => decCI (erA m) q) (fun _ => ⟨fun _ _ _ he h => he.2.decCI h⟩) o l

/-- **The model of `install_basis_decls(vis, o, l)`, both outcomes** (the recursion is the
model's own; `install_basis_decl` by its unified model). -/
l_model installBasisDecls_specE (p : Prog) (hB : BasisProg p)
  fns [hB.ibds ↦ installBasisDeclsE]
  specs [installBasisDecl_specE p hB n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`install_basis_decls` refines `installBasisDecls`, both outcomes**, by induction on the
fuel (the recursion is the model's): the head by `ibd_ref`, the rest by the induction
hypothesis. -/
theorem ibds_ref {p : Prog} (hB : BasisProg p) (dn : NIdx → Option ConLeche.Name) :
    ∀ (n : Nat) {m : Mem} {vis : Word} {fe : IFEnv} {a : AState} {o l : Word}
      {cis : List IConstantInfo}, StageR vis fe m a → DecB (basisDec dn o.toNat l.toNat) m cis →
      RefE True (installBasisDeclsE p n m vis o l) (installBasisDecls fe cis) a
        (fun v fe' a' => IbdPost dn m v.1 v.2 fe' a') := by
  intro n
  induction n with
  | zero => intros; rw [installBasisDeclsE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n ih =>
  intro m vis fe a o l cis hS hD
  by_cases hl : l = 0
  · rw [installBasisDeclsE.arm1 p n m vis o l hl]
    subst hl
    have : cis = [] := by
      simpa [DecB, basisDec, decPL] using hD.symm
    subst this
    exact RefE.ret rfl ⟨hS, IWGrow.refl _⟩
  rw [installBasisDeclsE.arm2 p n m vis o l hl]
  obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by
    have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hD' : basisDec dn o.toNat (k + 1) (truncM m) = some cis := by rw [← hk]; exact hD
  cases cis with
  | nil => have := decPL_length (truncM m) hD'; simp at this
  | cons ci cs =>
  obtain ⟨v, hv, hci⟩ := decPL_head hD'
  have hext := (IWGrow.refl m).truncExt
  have hvm : iwN m o.toNat = some v := hext.1.nat? hv
  have hci' : decCI (erecP m) v = some ci := ArrExt.decCI (truncM_erecP m) hci
  obtain ⟨w0, hw0, rfl⟩ : ∃ w0, iwA m o.toNat = some w0 ∧ w0.toNat = v := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
  have ew : rdW (m.arr64 IW) o = w0 := by simp [rdW, iwA, aread_apply] at hw0 ⊢; simp [hw0]
  rw [ew]
  have h1 := ibd_ref (dn := dn) hB n hS hci'
  simp only [installBasisDecls]
  rcases e1 : installBasisDeclE p n m vis w0 with e1 | ⟨r1, m1⟩ <;> rw [e1] at h1
  · rw [installBasisDeclsE.k_install_basis_decl.none]; exact RefE.bind_left h1
  obtain ⟨fe1, a1, hrun1, hR1⟩ := h1
  rw [installBasisDeclsE.k_install_basis_decl.arm1]
  refine RefE.bind_right hrun1 ?_
  have hob : o.toNat + 1 < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hw0).1
    have := hS.iw.iwSize; simp only [iwA] at *; omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := L.toNat_add_ofNat_of_lt o 1 hob
  have hl1 : (l - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hDt : DecB (basisDec dn (o + 1).toNat (l - 1).toNat) m cs := by
    rw [ho1, hl1]; exact decPL_tail hD'
  exact (ih hR1.stage (DecB.grow (basisDec_mono dn _ _) hR1.grow hDt)).mono
    fun _ _ _ hR => ⟨hR.stage, hR1.grow.trans hR.grow⟩


local notation "V" => ConLeche.CheckMode.verified

/-- **`install_basis_decl(vis, c)` refines `installBasisDecl`**. -/
@[refines ConRon.Arena.installBasisDecl]
theorem installBasisDecl_refines (p : Prog) (hp : BasisProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word) (ci : IConstantInfo)
    (hS : StageR vis fe s₀.mem a₀) (hci : decCI (erecP s₀.mem) c.toNat = some ci) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decl" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installBasisDecl fe ci) a₀ ∧
      StageR (r.headD 0) (AM.res (installBasisDecl fe ci) a₀) s'.mem
        (AM.st (installBasisDecl fe ci) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (installBasisDecl_specE p hp n s₀ vis c) (ibd_ref (dn := dn) hp n hS hci)) ?_
  rintro r s' ⟨hl, fe', a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hR.stage, hR.grow⟩


/-- **`install_basis_decls(vis, o, l)` refines `installBasisDecls`** (an `IW` slice of
constant-record pointers decoded below the tops). -/
@[refines ConRon.Arena.installBasisDecls]
theorem installBasisDecls_refines (p : Prog) (hp : BasisProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis o l : Word) (cis : List IConstantInfo)
    (hS : StageR vis fe s₀.mem a₀) (hD : DecB (basisDec dn o.toNat l.toNat) s₀.mem cis) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decls" [vis, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installBasisDecls fe cis) a₀ ∧
      StageR (r.headD 0) (AM.res (installBasisDecls fe cis) a₀) s'.mem
        (AM.st (installBasisDecls fe cis) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (installBasisDecls_specE p hp n s₀ vis o l)
    (ibds_ref hp dn n hS hD)) ?_
  rintro r s' ⟨hl, fe', a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hR.stage, hR.grow⟩


end L.Arena
