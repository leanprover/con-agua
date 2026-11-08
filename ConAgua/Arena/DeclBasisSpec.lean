module

import ConAgua.Arena.DeclValRef
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.DeclRec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.DeclBase
public import ConAgua.Arena.DeclHeader
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.Verdict
public import ConAgua.Checker.NoVerdictFns
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.Pins

@[expose] public section

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
  sorry

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
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n] <;>
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
    (hS : StageR vis fe s₀.mem a₀) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_op" [w]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ofReduceOp (decI w)) a₀ ∧
      KeepPost vis fe decW0N s₀.mem s'.mem (AM.st (ofReduceOp (decI w)) a₀) r
        (AM.res (ofReduceOp (decI w)) a₀); ⊤⦄ := by
  sorry

/-! ## `install_basis_decl(vis, c)` and `install_basis_decls(vis, o, l)` -/

/-- The lookups the basis install needs. -/
structure BasisProg (p : Prog) : Prop where
  ibd : p.lookup "install_basis_decl" = some installBasisDeclL
  ibds : p.lookup "install_basis_decls" = some installBasisDeclsL
  rcp : RecProg p

section models
variable (p : Prog)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `install_basis_decl(vis, c)`, both outcomes**: `env_find`, `env_push`
(outside the verdict closure) through their `Option` models. -/
l_model installBasisDecl_specE (p : Prog) (hB : BasisProg p)
  fns [hB.ibd ↦ installBasisDeclE]
  specs [callW_spec p n "env_find", callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

end models

/-! ### The relational lemmas -/

/-- The cut record pool is the record pool below its top. -/
theorem truncM_erecP (m : Mem) : ArrExt (erA (truncM m)) (erecP m) := by
  sorry

/-- What `install_basis_decl` gives besides the twin's environment `fe'` (from `m`): the stage
over the result word, the growth. -/
structure IbdPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : Word) (m' : Mem) (fe' : IFEnv)
    (a' : AState) : Prop where
  stage : StageR r fe' m' a'
  grow : IWGrow m m'

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`install_basis_decl` refines `installBasisDecl`, both outcomes**: a duplicate declaration
rejects (`env_find` hits), else the push. -/
theorem ibd_ref {p : Prog} (hB : BasisProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} (n : Nat) {m : Mem} {c : Word} {ci : IConstantInfo}
    (hS : StageR vis fe m a) (hci : decCI (erecP m) c.toNat = some ci) :
    RefE True (installBasisDeclE p n m vis c) (installBasisDecl fe ci) a
      (fun v fe' a' => IbdPost dn m v.1 v.2 fe' a') := by
  sorry

-/

/-- The basis list's decoding: an `IW` slice of constant-record pointers. -/
def basisDec (dn : NIdx → Option ConLeche.Name) (o l : Nat) (m : Mem) :
    Option (List IConstantInfo) :=
  decPL m (fun q => decCI (erA m) q) o l

theorem basisDec_mono (dn : NIdx → Option ConLeche.Name) (o l : Nat) :
    OMono (basisDec dn o l) :=
  OMono.decPL (f := fun m q => decCI (erA m) q) (fun _ => ⟨fun _ _ _ he h => he.2.decCI h⟩) o l

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `install_basis_decls(vis, o, l)`, both outcomes** (the recursion is the
model's own; `install_basis_decl` by its unified model). -/
l_model installBasisDecls_specE (p : Prog) (hB : BasisProg p)
  fns [hB.ibds ↦ installBasisDeclsE]
  specs [installBasisDecl_specE p hB n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`install_basis_decls` refines `installBasisDecls`, both outcomes**, by induction on the
fuel (the recursion is the model's): the head by `ibd_ref`, the rest by the induction
hypothesis. -/
theorem ibds_ref {p : Prog} (hB : BasisProg p) (dn : NIdx → Option ConLeche.Name) :
    ∀ (n : Nat) {m : Mem} {vis : Word} {fe : IFEnv} {a : AState} {o l : Word}
      {cis : List IConstantInfo}, StageR vis fe m a → DecB (basisDec dn o.toNat l.toNat) m cis →
      RefE True (installBasisDeclsE p n m vis o l) (installBasisDecls fe cis) a
        (fun v fe' a' => IbdPost dn m v.1 v.2 fe' a') := by
  sorry

-/

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`install_basis_decl(vis, c)` refines `installBasisDecl`** (sorry-free). -/
@[refines ConRon.Arena.installBasisDecl]
theorem installBasisDecl_refines (p : Prog) (hp : BasisProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word) (ci : IConstantInfo)
    (hS : StageR vis fe s₀.mem a₀) (hci : decCI (erecP s₀.mem) c.toNat = some ci) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decl" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installBasisDecl fe ci) a₀ ∧
      StageR (r.headD 0) (AM.res (installBasisDecl fe ci) a₀) s'.mem
        (AM.st (installBasisDecl fe ci) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`install_basis_decls(vis, o, l)` refines `installBasisDecls`** (an `IW` slice of
constant-record pointers decoded below the tops; sorry-free). -/
@[refines ConRon.Arena.installBasisDecls]
theorem installBasisDecls_refines (p : Prog) (hp : BasisProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis o l : Word) (cis : List IConstantInfo)
    (hS : StageR vis fe s₀.mem a₀) (hD : DecB (basisDec dn o.toNat l.toNat) s₀.mem cis) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_basis_decls" [vis, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installBasisDecls fe cis) a₀ ∧
      StageR (r.headD 0) (AM.res (installBasisDecls fe cis) a₀) s'.mem
        (AM.st (installBasisDecls fe cis) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  sorry

-/

end L.Arena
