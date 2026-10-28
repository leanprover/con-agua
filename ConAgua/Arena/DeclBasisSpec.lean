import ConAgua.Arena.DeclValRef
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.DeclRec
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Pin reads, `of_reduce_op`, `install_basis_decl(s)` (lane `decls3`)

* `pin_at(i)` as a word model (`pinAtW`) and its twin read (`pinAtW_ok`).
* `of_reduce_op(n)` refines `ofReduceOp` (pin reads only; sorry-free).
* `install_basis_decl(vis, c)` refines `installBasisDecl` (the duplicate check, the push) and
  `install_basis_decls(vis, o, l)` refines `installBasisDecls` (an `IW` slice of constant-record
  pointers), sorry-free.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-! ## `pin_at(i)` -/

/-- **The model of `pin_at(i)`**: the flag, the slot bound, the slot. -/
def pinAtW (m : Mem) (i : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else if 51 ≤ i then none else some ([rdW (m.arr64 PINS) (1 + i)], m)

theorem pinAt_specW (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St)
    (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ pinAtW s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinAtW, pinW_eq, rdW_eq]

/-- **A pin read is the twin's** (`pinAt`), the memory unchanged. -/
theorem pinAtW_ok {m m' : Mem} {a : AState} {i : Word} {r : List Word}
    (h : pinAtW m i = some (r, m')) (hP : PinsR m a.pins) :
    m' = m ∧ r = [pinW m (1 + i.toNat)] ∧ (pinW m (1 + i.toNat)).toNat < 2 ^ 32 ∧
      (pinAt i.toNat).run a = .ok (decI (pinW m (1 + i.toNat)), a) := by
  unfold pinAtW at h
  by_cases h0 : pinW m 0 = 0
  · simp [h0] at h
  rw [ite_eq_right h0] at h
  by_cases hi : 51 ≤ i
  · simp [hi] at h
  rw [ite_eq_right hi] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hF := hP.full h0
  have hi' : i.toNat < 51 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hi); simpa using this
  have e : rdW (m.arr64 PINS) (1 + i) = pinW m (1 + i.toNat) := by
    simp only [rdW, pinW]
    congr 2
    rw [UInt64.toNat_add]; simp; omega
  rw [e]
  exact ⟨rfl, rfl, hF.names_lt i.toNat hi', pinAt_run hF i.toNat hi'⟩

/-! ## `of_reduce_op(n)` -/

/-- After the `ofReduceNat` pin. -/
def oroK (n : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if n = r1.headD 0 then pinAtW m1 43 else pinAtW m1 44

/-- **The model of `of_reduce_op(n)`.** -/
def oroW (m : Mem) (n : Word) : Option (List Word × Mem) := oroK n (pinAtW m 45)

theorem oroK_some (n : Word) (r1 : List Word) (m1 : Mem) :
    oroK n (some (r1, m1)) = if n = r1.headD 0 then pinAtW m1 43 else pinAtW m1 44 := rfl

grind_pattern [ind_grind] oroK_some => oroK n (some (r1, m1))

theorem oro_specW (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "of_reduce_op" = some ofReduceOpL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_op" [w]
    ⦃fun r s' => LocEq s' s₀ ∧ oroW s₀.mem w = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ofReduceOpL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n] <;>
      finish (gen := 20) [oroW, pinAtW]

theorem oroW_ok {m m' : Mem} {a : AState} {w : Word} {r : List Word}
    (h : oroW m w = some (r, m')) (hP : PinsR m a.pins) (hw : w.toNat < 2 ^ 32) :
    m' = m ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (ofReduceOp (decI w)).run a = .ok (decI (r.headD 0), a) := by
  unfold oroW at h
  cases h1 : pinAtW m 45 with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, oroK_some] at h
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hP
  have hbeq : ((decI w : NIdx) == decI (pinW m (1 + (45 : Word).toNat))) =
      decide (w = pinW m (1 + (45 : Word).toNat)) := decI_beq w _ hw hl1
  have e1 : r1.headD 0 = pinW m (1 + (45 : Word).toNat) := by rw [hr1]; rfl
  by_cases he : w = r1.headD 0
  · rw [ite_eq_left he, hm1] at h
    obtain ⟨hm, hr, hl, hrun⟩ := pinAtW_ok h hP
    subst hr
    rw [e1] at he
    refine ⟨hm, hl, ?_⟩
    simp only [ofReduceOp, ofReduceNatName, pinOfReduceNat, reduceNatName, pinReduceNat,
      StateT.run_bind, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl, hrun1, exc_ok_bind', he]
    simpa [PIN_REDUCE_NAT, PIN_REDUCE_BOOL] using hrun
  · rw [ite_eq_right he, hm1] at h
    obtain ⟨hm, hr, hl, hrun⟩ := pinAtW_ok h hP
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
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis w : Word)
    (hS : StageR dn vis fe s₀.mem a₀) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_op" [w]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ofReduceOp (decI w)) a₀ ∧
      KeepPost dn vis fe decW0N s₀.mem s'.mem (AM.st (ofReduceOp (decI w)) a₀) r
        (AM.res (ofReduceOp (decI w)) a₀); ⊤⦄ := by
  refine triple_post (oro_specW p hpa hp n s₀ w) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmem, hrl, hrun⟩ := oroW_ok hm hS.1.pins hw
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_, ?_, hrl, by rw [hres]⟩
  · rw [hst, hmem]; exact hS
  · rw [hmem]; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## `install_basis_decl(vis, c)` and `install_basis_decls(vis, o, l)` -/

/-- The lookups the basis install needs. -/
structure BasisProg (p : Prog) : Prop where
  ibd : p.lookup "install_basis_decl" = some installBasisDeclL
  ibds : p.lookup "install_basis_decls" = some installBasisDeclsL
  ih : IhProg p
  rcp : RecProg p

section models
variable (p : Prog)

/-- **The model of `install_basis_decl(vis, c)`, both outcomes**: `env_find`, `env_push`
(outside the verdict closure) through their `Option` models. -/
l_model installBasisDecl_specE (p : Prog) (hB : BasisProg p)
  fns [hB.ibd ↦ installBasisDeclE]
  specs [envFind_specW p hB.ih.ix hB.ih.rowGet hB.ih.find n, callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end models

/-! ### The relational lemmas -/

/-- The cut record pool is the record pool below its top. -/
theorem truncM_erecP (m : Mem) : ArrExt (erA (truncM m)) (erecP m) := by
  intro i v h
  obtain ⟨hi, hv⟩ := truncM_er_get h
  rw [erecP_getE hi]; exact hv

/-- What `install_basis_decl` gives besides the twin's environment `fe'` (from `m`): the stage
over the result word, the growth. -/
structure IbdPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : Word) (m' : Mem) (fe' : IFEnv)
    (a' : AState) : Prop where
  stage : StageR dn r fe' m' a'
  grow : IWGrow m m'

/-- **`install_basis_decl` refines `installBasisDecl`, both outcomes**: a duplicate declaration
rejects (`env_find` hits), else the push. -/
theorem ibd_ref {p : Prog} (hB : BasisProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {c : Word} {ci : IConstantInfo}
    (hS : StageR dn vis fe m a) (hci : decCI (erecP m) dn c.toNat = some ci) :
    RefE True (installBasisDeclE p n m vis c) (installBasisDecl fe ci) a
      (fun v fe' a' => IbdPost dn m v.1 v.2 fe' a') := by
  obtain ⟨w, hw1, hwl, hname⟩ := decCI_name hci
  have hcb : c.toNat + 1 < 2 ^ 64 := erecP_bound hw1 hS.2
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 hcb
  have ew : rdW (m.arr64 EREC) (c + 1) = w := rdW_of_get? hc1.symm (erecP_get hw1)
  cases n with
  | zero => rw [installBasisDeclE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [installBasisDeclE.arm1, ew]
  rcases h1 : envFindW m w vis with _ | ⟨r1, m1⟩
  · rw [liftE_none, installBasisDeclE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  by_cases hb : r1.headD 0 ≠ 0
  · rw [installBasisDeclE.k_env_find.abort1 p _ _ _ _ _ hb]
    have : (fe.find? ci.name).isSome = true := by
      rw [hname]; exact envFindW_hitSome h1 hS.1.env hwl hb
    simp only [installBasisDecl, fail_bindAM]
    exact fun _ => ErrClaim.ite_neg (by simp [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] at this ⊢; exact this)
      (ErrClaim.fail _ _ rfl)
  rw [installBasisDeclE.k_env_find.arm1 p _ _ _ _ _ (by simpa using hb)]
  obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.1.env hwl (by simpa using hb)
  have hw : (rdW (m1.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by rw [ew]; exact hwl
  rcases h2 : callW p n "env_push" [vis, c] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, installBasisDeclE.k_env_push.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, installBasisDeclE.k_env_push.arm1]
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (envPush_specW p hB.rcp n ⟨m1, Locals.init []⟩ vis c hw) h2
  subst hs2
  obtain ⟨hS2, hg2⟩ := envPushW_ok hW2 hS hci
  refine RefE.ret ?_ ⟨by simpa using hS2, hg2⟩
  simp [installBasisDecl, hname, hfind, StateT.run_pure]
  rfl

/-- The basis list's decoding: an `IW` slice of constant-record pointers. -/
def basisDec (dn : NIdx → Option ConLeche.Name) (o l : Nat) (m : Mem) :
    Option (List IConstantInfo) :=
  decPL m (fun q => decCI (erA m) dn q) o l

theorem basisDec_mono (dn : NIdx → Option ConLeche.Name) (o l : Nat) :
    OMono (basisDec dn o l) :=
  OMono.decPL (f := fun m q => decCI (erA m) dn q) (fun _ => ⟨fun _ _ _ he h => he.2.decCI h⟩) o l

/-- **The model of `install_basis_decls(vis, o, l)`, both outcomes** (the recursion is the
model's own; `install_basis_decl` by its unified model). -/
l_model installBasisDecls_specE (p : Prog) (hB : BasisProg p)
  fns [hB.ibds ↦ installBasisDeclsE]
  specs [installBasisDecl_specE p hB n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`install_basis_decls` refines `installBasisDecls`, both outcomes**, by induction on the
fuel (the recursion is the model's): the head by `ibd_ref`, the rest by the induction
hypothesis. -/
theorem ibds_ref {p : Prog} (hB : BasisProg p) (dn : NIdx → Option ConLeche.Name) :
    ∀ (n : Nat) {m : Mem} {vis : Word} {fe : IFEnv} {a : AState} {o l : Word}
      {cis : List IConstantInfo}, StageR dn vis fe m a → DecB (basisDec dn o.toNat l.toNat) m cis →
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
  have hci' : decCI (erecP m) dn v = some ci := ArrExt.decCI (truncM_erecP m) hci
  obtain ⟨w0, hw0, rfl⟩ : ∃ w0, (iwA m)[o.toNat]? = some w0 ∧ w0.toNat = v := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
  have ew : rdW (m.arr64 IW) o = w0 := by simp [rdW, iwA] at hw0 ⊢; simp [hw0]
  rw [ew]
  have h1 := ibd_ref hB n hS hci'
  simp only [installBasisDecls]
  rcases e1 : installBasisDeclE p n m vis w0 with e1 | ⟨r1, m1⟩ <;> rw [e1] at h1
  · rw [installBasisDeclsE.k_install_basis_decl.none]; exact RefE.bind_left h1
  obtain ⟨fe1, a1, hrun1, hR1⟩ := h1
  rw [installBasisDeclsE.k_install_basis_decl.arm1]
  refine RefE.bind_right hrun1 ?_
  have hob : o.toNat + 1 < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hw0).1
    have := hS.2.2.2.1; simp only [iwA] at *; omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_add_small o 1 hob
  have hl1 : (l - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hDt : DecB (basisDec dn (o + 1).toNat (l - 1).toNat) m cs := by
    rw [ho1, hl1]; exact decPL_tail hD'
  exact (ih hR1.stage (DecB.grow (basisDec_mono dn _ _) hR1.grow hDt)).mono
    fun _ _ _ hR => ⟨hR.stage, hR1.grow.trans hR.grow⟩

local notation "V" => ConLeche.CheckMode.verified

/-- **`install_basis_decl(vis, c)` refines `installBasisDecl`** (sorry-free). -/
@[refines ConRon.Arena.installBasisDecl]
theorem installBasisDecl_refines (p : Prog) (hp : BasisProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word) (ci : IConstantInfo)
    (hS : StageR dn vis fe s₀.mem a₀) (hci : decCI (erecP s₀.mem) dn c.toNat = some ci) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decl" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installBasisDecl fe ci) a₀ ∧
      StageR dn (r.headD 0) (AM.res (installBasisDecl fe ci) a₀) s'.mem
        (AM.st (installBasisDecl fe ci) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (installBasisDecl_specE p hp n s₀ vis c) (ibd_ref hp n hS hci)) ?_
  rintro r s' ⟨hl, fe', a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hR.stage, hR.grow⟩

/-- **`install_basis_decls(vis, o, l)` refines `installBasisDecls`** (an `IW` slice of
constant-record pointers decoded below the tops; sorry-free). -/
@[refines ConRon.Arena.installBasisDecls]
theorem installBasisDecls_refines (p : Prog) (hp : BasisProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis o l : Word) (cis : List IConstantInfo)
    (hS : StageR dn vis fe s₀.mem a₀) (hD : DecB (basisDec dn o.toNat l.toNat) s₀.mem cis) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decls" [vis, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installBasisDecls fe cis) a₀ ∧
      StageR dn (r.headD 0) (AM.res (installBasisDecls fe cis) a₀) s'.mem
        (AM.st (installBasisDecls fe cis) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (installBasisDecls_specE p hp n s₀ vis o l)
    (ibds_ref hp dn n hS hD)) ?_
  rintro r s' ⟨hl, fe', a', hrun, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hR.stage, hR.grow⟩

end L.Arena
