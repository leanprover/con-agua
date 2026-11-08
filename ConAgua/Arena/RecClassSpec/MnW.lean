module

public import ConAgua.Arena.RecClassSpec.ClassGenRecTy
public import ConAgua.Arena.RecClassSpec.MnProg
import ConAgua.Arena.RecClassSpec.PdWAfr
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndPosSpec.SnocWStage
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.IndSim
import ConAgua.Arena.RecClassSpec.MkTMWAfr
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RecClassSpec.Rec2AppendWDec
import ConAgua.Arena.RecClassSpec.Rec2SimTMA
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.RecClass

@[expose] public section

/-!
# MnW

`loc_init12`, `rec2IhF`, `rec2IhParts_specF`, `classGenMinorTyIh1Close_spec`, `iclW`, `classGenMinorTyIh1Tail_spec` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem loc_init12 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: r) 12 = x12 :=
  rfl

/-- `class_gen_ih_parts` at every fuel. -/
def rec2IhF (n : Nat) (m : Mem) (g t tele w d : Word) : Option (List Word × Mem) :=
  fuelW n (ihW m g t tele w d)

theorem rec2IhParts_specF (p : Prog) (hp : p.lookup "class_gen_ih_parts" = some classGenIhParts)
    (had : AdF p) (hopf : OpfF p) (n : Nat) (s₀ : St) (g t tele w d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_ih_parts" [g, t, tele, w, d]
    ⦃fun r s' => LocEq s' s₀ ∧ rec2IhF n s₀.mem g t tele w d = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact classGenIhParts_spec p hp had hopf n s₀ g t tele w d

l_model classGenMinorTyIh1Close_spec (p : Prog) (h : MnProg p)
  fns [h.icl ↦ iclW list]
  specs [ftdsF_spec p h.ad n, closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct h.ab n]
  grind [arena_grind]

l_model classGenMinorTyIh1Tail_spec (p : Prog) (h : MnProg p)
  fns [h.it ↦ itW list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, mknF_spec p h.ad n,
    rec2MotVar_specF p h.toMtProg h.fvf h.fvp h.ifv h.sv h.ms h.mv n,
    slSnoc_specW p h.alloc h.copy h.snoc n, classGenMinorTyIh1Close_spec p h n]
  grind [arena_grind]

l_model classGenMinorTyIh1_spec (p : Prog) (h : MnProg p)
  fns [h.i1 ↦ i1W list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, rec2IhParts_specF p h.ihp h.ad h.opf n,
    classGenMinorTyIh1Tail_spec p h n]
  grind [arena_grind]

/-! ## `class_gen_minor_ty_ihs_go` -/

def isK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([1, r4.headD 0, r4.tail.headD 0], m4)

def isK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m)

def isK2 (n : Nat) (ih : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else isK4 (consW n m2 ih (r2.tail.headD 0) (r2.tail.tail.headD 0))

/-- The tag of field `i`'s kind (`0` past the kinds). -/
def isTag (m : Mem) (x i : Word) : Word :=
  if i < rdW (m.arr64 IW) (x + 3) then rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (x + 2) + i))
  else 0

/-- Field `i`'s kind record. -/
def isKp (m : Mem) (x i : Word) : Word := rdW (m.arr64 IW) (rdW (m.arr64 IW) (x + 2) + i)

mutual
/-- **The model of `class_gen_minor_ty_ihs_go`.** -/
def misW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, x, d, nF, wso, wsl, fvso, fvsl, i, l =>
    if nF ≤ i then some ([1, 0, 0], m)
    else if isTag m x i = 1 then
      if d + nF < d then none
      else if d + nF + l < d + nF then none
      else isK1 n g x d nF wso wsl fvso fvsl i l
        (i1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
          i (d + nF + l))
    else isK3 (misW n m g x d nF wso wsl fvso fvsl (i + 1) l)
def isK1 (n : Nat) (g x d nF wso wsl fvso fvsl i l : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0, 0], m1)
    else isK2 n (r1.tail.headD 0) (misW n m1 g x d nF wso wsl fvso fvsl (i + 1) (l + 1))
end

/-! ## Arms -/

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 : Mem)
  (g t c x d e tele xso xsl idxo idxl fvso fvsl wso wsl i l nF fx mt body ih nPc fo fl ihso ihsl rao ral
    capp mc lvls ds0 dl0 res cc : Word) (r r1 r2 r3 r4 r5 r6 r7 : List Word)
theorem misW_end (h : nF ≤ i) : misW (n + 1) m g x d nF wso wsl fvso fvsl i l = some ([1, 0, 0], m) := by
  simp only [misW]; rw [ite_eq_left h]
theorem misW_rec (h : ¬ nF ≤ i) (ht : isTag m x i = 1) (h1 : ¬ d + nF < d) (h2 : ¬ d + nF + l < d + nF) :
    misW (n + 1) m g x d nF wso wsl fvso fvsl i l = isK1 n g x d nF wso wsl fvso fvsl i l
      (i1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
        i (d + nF + l)) := by
  simp only [misW]; rw [ite_eq_right h, ite_eq_left ht, ite_eq_right h1, ite_eq_right h2]
theorem misW_ov1 (h : ¬ nF ≤ i) (ht : isTag m x i = 1) (h1 : d + nF < d) :
    misW (n + 1) m g x d nF wso wsl fvso fvsl i l = none := by
  simp only [misW]; rw [ite_eq_right h, ite_eq_left ht, ite_eq_left h1]
theorem misW_ov2 (h : ¬ nF ≤ i) (ht : isTag m x i = 1) (h1 : ¬ d + nF < d) (h2 : d + nF + l < d + nF) :
    misW (n + 1) m g x d nF wso wsl fvso fvsl i l = none := by
  simp only [misW]; rw [ite_eq_right h, ite_eq_left ht, ite_eq_right h1, ite_eq_left h2]
theorem misW_ord (h : ¬ nF ≤ i) (ht : ¬ isTag m x i = 1) :
    misW (n + 1) m g x d nF wso wsl fvso fvsl i l = isK3 (misW n m g x d nF wso wsl fvso fvsl (i + 1) l) := by
  simp only [misW]; rw [ite_eq_right h, ite_eq_right ht]
theorem isK1_fail (h : r1.headD 0 = 0) : isK1 n g x d nF wso wsl fvso fvsl i l (some (r1, m1)) =
    some ([0, 0, 0], m1) := by rw [isK1, ite_eq_left h]
theorem isK1_ok (h : r1.headD 0 ≠ 0) : isK1 n g x d nF wso wsl fvso fvsl i l (some (r1, m1)) =
    isK2 n (r1.tail.headD 0) (misW n m1 g x d nF wso wsl fvso fvsl (i + 1) (l + 1)) := by rw [isK1, ite_eq_right h]
theorem isK2_fail (h : r2.headD 0 = 0) : isK2 n ih (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [isK2, ite_eq_left h]
theorem isK2_ok (h : r2.headD 0 ≠ 0) : isK2 n ih (some (r2, m2)) =
    isK4 (consW n m2 ih (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by rw [isK2, ite_eq_right h]
theorem isK3_some : isK3 (some (r, m)) = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m) := rfl
theorem isK4_some : isK4 (some (r4, m4)) = some ([1, r4.headD 0, r4.tail.headD 0], m4) := rfl
end arms

attribute [ind_grind] misW_end misW_rec misW_ov1 misW_ov2 misW_ord isK1_fail isK1_ok
  isK2_fail isK2_ok isK3_some isK4_some

section specs
variable (p : Prog) (h : MnProg p)
include h

set_option maxHeartbeats 1000000 in
theorem classGenMinorTyIhsGo_spec (n : Nat) : ∀ (s₀ : St) (g x d nF wso wsl fvso fvsl i l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty_ihs_go" [g, x, d, nF, wso, wsl, fvso, fvsl, i, l]
    ⦃fun r s' => LocEq s' s₀ ∧ misW n s₀.mem g x d nF wso wsl fvso fvsl i l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ g x d nF wso wsl fvso fvsl i l
    rw [invoke_eq _ h.isg]; simp only [callFn, classGenMinorTyIhsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ g x d nF wso wsl fvso fvsl i l
    rw [invoke_eq _ h.isg]
    simp only [callFn, classGenMinorTyIhsGo]
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec,
      classGenMinorTyIh1_spec p h n, slCons_specW p h.alloc h.copy h.cons n, ih]
    all_goals subst_vars
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, isTag, isKp, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9]

end specs

/-! ## `class_gen_minor_ty_close`, `_concl2`, `_concl`, `_body`, `class_gen_minor_ty` -/

l_model classGenMinorTyClose_spec (p : Prog) (h : MnProg p)
  fns [h.mcl ↦ mcW list]
  specs [ftdsF_spec p h.ad n, slAppend_specW p h.alloc h.copy h.app n,
    closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct h.ab n]
  grind [arena_grind]

l_model classGenMinorTyConcl2_spec (p : Prog) (h : MnProg p)
  fns [h.c2 ↦ c2W list]
  specs [rec2MotVar_specF p h.toMtProg h.fvf h.fvp h.ifv h.sv h.ms h.mv n,
    slSnoc_specW p h.alloc h.copy h.snoc n, mknF_spec p h.ad n, classGenMinorTyClose_spec p h n]
  grind [arena_grind]

l_model classGenMinorTyConcl_spec (p : Prog) (h : MnProg p)
  fns [h.cc ↦ cW list]
  specs [gaaF_spec p h.ad n, internConst_spec p h.cf h.cp h.ic n,
    slAppend_specW p h.alloc h.copy h.app n, mknF_spec p h.ad n, classGenMinorTyConcl2_spec p h n]
  grind [arena_grind]

l_model classGenMinorTyBody_spec (p : Prog) (h : MnProg p)
  fns [h.bd ↦ bW list]
  specs [opfF_spec p h.opf n, targetPiDomsWith_spec p h.ev h.copy h.alloc h.cons h.tpd h.hi1 n,
    classGenMinorTyIhsGo_spec p h n, classGenMinorTyConcl_spec p h n]
  grind [arena_grind] finish [rdW_eq] gen 20

def cK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def mnK1 (n : Nat) (g c x d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cK4 (bW n m1 g c x d (rdW (m1.arr64 IW) (r1.headD 0 + 1)) (rdW (m1.arr64 IW) (r1.headD 0 + 2))
      (rdW (m1.arr64 IW) (r1.headD 0 + 3)) (rdW (m1.arr64 IW) (r1.headD 0 + 4)))

/-- **The model of `class_gen_minor_ty`.** -/
def mnW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, g, c, x, d =>
    mnK1 n g c x d (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c)

section arms2
variable (n : Nat) (m m1 : Mem) (g c x d : Word) (r r1 : List Word)
theorem cK4_some : cK4 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem mnW_eq : mnW (n + 1) m g c x d =
    mnK1 n g c x d (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c) := rfl
theorem mnK1_some : mnK1 n g c x d (some (r1, m1)) =
    cK4 (bW n m1 g c x d (rdW (m1.arr64 IW) (r1.headD 0 + 1)) (rdW (m1.arr64 IW) (r1.headD 0 + 2))
      (rdW (m1.arr64 IW) (r1.headD 0 + 3)) (rdW (m1.arr64 IW) (r1.headD 0 + 4))) := rfl
end arms2

attribute [ind_grind] cK4_some mnW_eq mnK1_some

section specs
variable (p : Prog) (h : MnProg p)
include h

theorem classGenMinorCi_spec (n : Nat) (s₀ : St) (ci : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ci" [ci]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r = [rdW (s₀.mem.arr64 IW) (ci + 1), rdW (s₀.mem.arr64 IW) (ci + 2), rdW (s₀.mem.arr64 IW) (ci + 3),
        rdW (s₀.mem.arr64 IW) (ci + 4)]; ⊤⦄ := by
  rw [invoke_eq _ h.mnci]
  simp only [callFn, classGenMinorCi]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64]
  all_goals (try simp only [Locals.init, List.getD_cons_zero, BinOp.eval] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq]

theorem classGenMinorTy_spec (n : Nat) (s₀ : St) (g c x d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty" [g, c, x, d]
    ⦃fun r s' => LocEq s' s₀ ∧ mnW n s₀.mem g c x d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.mn]
  simp only [callFn, classGenMinorTy]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma h.na n, classGenMinorCi_spec p h n,
    classGenMinorTyBody_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init,
    List.getD_cons_zero, List.getD_cons_succ, BinOp.eval, Nat.reduceEqDiff, reduceIte] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq]

end specs

/-! ## Relational lemmas: the inductive hypothesis -/

theorem rec2CG_cls {m : Mem} {g : Nat} {G : ClassGen} (h : decCG m g = some G) :
    decAt m (decPL m (decTM m)) (g + 3) = some G.cls := by
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, rfl⟩ := h
  exact hcls

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem rec2SimIh (n : Nat) {m : Mem} {a : AState} (hS : StageR vis fe m a) {g : Word} {G : ClassGen}
    (hG : DecB (fun m => decCG m g.toNat) m G) (t tele : Word) {w : Word} (hw : H w) (d : Word)
    (hA : AbsOK m) :
    RSim (rec2IhF n m g t tele w d) (G.ihParts t.toNat tele.toNat (decI w) d.toNat) a
      (fun b a' x => (StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ IhRes b.2 b.1 x) ∧ AbsOK b.2) := by
  sorry

/-- `class_gen_minor_ty_ih1`, in continuation form: the twin's body of `ihsGo` at one recursive
field, then `REST` at the inductive hypothesis. -/
theorem i1W_sim {β γ : Type} (n : Nat) (m : Mem) (a : AState) (g t tele wso wsl fvso fvsl i e : Word)
    (G : ClassGen) (ws fvs : List EIdx) (hS : StageR vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hws : decHL m wso.toNat wsl.toNat = some ws) (hwb : wso.toNat + wsl.toNat ≤ iwTop m)
    (hfvs : decHL m fvso.toNat fvsl.toNat = some fvs) (hfb : fvso.toNat + fvsl.toNat ≤ iwTop m)
    (hA : AbsOK m)
    (K : Option (List Word × Mem) → Option β) (hK : K none = none) (REST : EIdx → AM (Option γ))
    (Q : β → AState → Option γ → Prop)
    (hnone : ∀ m' a', StageR vis fe m' a' → IWGrow m m' → AbsOK m' →
      RSim (K (some ([0, 0], m'))) (pure none) a' Q)
    (hsome : ∀ m' a' w, StageR vis fe m' a' → IWGrow m m' → H w → AbsOK m' →
      RSim (K (some ([1, w], m'))) (REST (decI w)) a' Q) :
    RSim (K (i1W (n + 1) m g t tele wso wsl fvso fvsl i e)) (do
      let w ← ConRon.Arena.exprGetD ws i.toNat
      let __do_lift ← G.ihParts t.toNat tele.toNat w e.toNat
      match __do_lift with
      | none => pure none
      | some (xs, idx) => do
        let f ← ConRon.Arena.exprGetD fvs i.toNat
        let fx ← mkAppN f xs
        let mt ← G.motVar t.toNat
        let body ← mkAppN mt (idx ++ [fx])
        let bs ← List.mapM G.binder xs
        let ih ← ConRon.Arena.closeTelescope bs e.toNat body
        REST ih) a Q := by
  sorry

end sims

/-! ## The inductive hypotheses -/

/-- The twin's `recs` from field `i` on. -/
def rec2Recs (X : ClassCtor) (i : Nat) : List (Nat × Nat × Nat) :=
  (List.range' i (X.nF - i)).filterMap fun j =>
    match X.kinds.getD j .ordinary with
    | .recursive t tele => some (j, t, tele)
    | .ordinary => none

theorem rec2Recs_zero (X : ClassCtor) : rec2Recs X 0 = (List.range X.nF).filterMap (fun i =>
    match X.kinds.getD i ClassField.ordinary with
    | ClassField.recursive t tele => some (i, t, tele)
    | ClassField.ordinary => none) := by
  simp [rec2Recs, List.range_eq_range']

theorem rec2Recs_end {X : ClassCtor} {i : Nat} (h : X.nF ≤ i) : rec2Recs X i = [] := by
  simp [rec2Recs, show X.nF - i = 0 by omega]

theorem rec2Recs_step {X : ClassCtor} {i : Nat} (h : i < X.nF) : rec2Recs X i =
    (match X.kinds.getD i .ordinary with
     | .recursive t tele => [(i, t, tele)]
     | .ordinary => []) ++ rec2Recs X (i + 1) := by
  simp only [rec2Recs]
  rw [show X.nF - i = (X.nF - (i + 1)) + 1 by omega, List.range'_succ, List.filterMap_cons]
  cases X.kinds.getD i .ordinary <;> simp

/-- The kinds' words: the tag of field `i` and, at a recursive field, its class and telescope. -/
theorem rec2IsTag {m : Mem} {x i : Word} {X : ClassCtor} (hX : decCC m x.toNat = some X)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (X.kinds.getD i.toNat .ordinary = .ordinary → isTag m x i ≠ 1) ∧
    (∀ t tele, X.kinds.getD i.toNat .ordinary = .recursive t tele →
      isTag m x i = 1 ∧ rdW (m.arr64 IW) (isKp m x i + 1) = UInt64.ofNat t ∧ t < 2 ^ 64 ∧
      rdW (m.arr64 IW) (isKp m x i + 2) = UInt64.ofNat tele ∧ tele < 2 ^ 64) := by
  simp only [decCC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hX
  obtain ⟨q, hq, cv, hcv, nF, hnF, ks, hks, y4, hy4, y5, hy5, rfl⟩ := hX
  obtain ⟨ko, kl, hko, hkl, hkd⟩ := decAt_some hks
  obtain ⟨e2, -⟩ := rec2RdN (w := x) (k := 2) hko hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := x) (k := 3) (by simpa [Nat.add_assoc] using hkl) hsz
  have kllt : kl < 2 ^ 64 := (iwN_rdW_at (w := x) (k := 3) (by simpa [Nat.add_assoc] using hkl) hsz).2
  have kolt : ko < 2 ^ 64 := (iwN_rdW_at (w := x) (k := 2) hko hsz).2
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at e2 e3
  have hlen := decPL_length m hkd
  simp only [isTag, isKp, e2, e3]
  by_cases hi : i.toNat < kl
  · have hilt : i < UInt64.ofNat kl := UInt64.lt_iff_toNat_lt.mpr (by rw [t3]; exact hi)
    obtain ⟨v, hv, hcf⟩ := decPL_getH m hkd i.toNat hi
    have hvlt := iwN_lt hv
    have ev : rdW (m.arr64 IW) (UInt64.ofNat ko + i) = UInt64.ofNat v := by
      have := (iwN_rdW hv (by omega)).1
      rwa [show UInt64.ofNat (ko + i.toNat) = UInt64.ofNat ko + i by simp [UInt64.ofNat_add]] at this
    have vlt := (iwN_rdW hv (by omega)).2
    have hget : ks.getD i.toNat .ordinary = ks[i.toNat]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i.toNat < ks.length)]
    rw [hget]
    simp only [ite_eq_left hilt, ev]
    revert hcf
    generalize ks[i.toNat]'(by omega) = k
    intro hcf
    simp only [decCF, bind, Option.bind_eq_some_iff] at hcf
    obtain ⟨tg, htg, hk⟩ := hcf
    obtain ⟨etg, -⟩ := rec2RdN (w := UInt64.ofNat v) (k := 0) (by simpa [UInt64.toNat_ofNat_of_lt' vlt] using htg) hsz
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at etg
    have tglt := (iwN_rdW htg (by have := iwN_lt htg; omega)).2
    match tg, hk with
    | 0, hk =>
      simp only [pure, Option.some.injEq] at hk; subst hk
      exact ⟨fun _ => (by rw [etg]; decide), fun t tele e => (by cases e)⟩
    | 1, hk =>
      simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hk
      obtain ⟨t, ht, tele, htele, rfl⟩ := hk
      obtain ⟨e1, -⟩ := rec2RdN (w := UInt64.ofNat v) (k := 1) (by simpa [UInt64.toNat_ofNat_of_lt' vlt] using ht) hsz
      obtain ⟨e2', -⟩ := rec2RdN (w := UInt64.ofNat v) (k := 2) (by simpa [UInt64.toNat_ofNat_of_lt' vlt] using htele) hsz
      simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at e1 e2'
      refine ⟨fun e => (by cases e), fun t' tele' e => ?_⟩
      cases e
      exact ⟨by rw [etg]; rfl, e1, (iwN_rdW ht (by have := iwN_lt ht; omega)).2, e2',
        (iwN_rdW htele (by have := iwN_lt htele; omega)).2⟩
    | (_ + 2), hk => simp at hk
  · have hilt : ¬ i < UInt64.ofNat kl := fun x => hi (by have := UInt64.lt_iff_toNat_lt.mp x; rwa [t3] at this)
    have hget : ks.getD i.toNat .ordinary = .ordinary := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ks.length ≤ i.toNat)]
    rw [hget]
    simp only [ite_eq_right hilt]
    exact ⟨fun _ => (by decide), fun t tele e => (by cases e)⟩

theorem misW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (G : ClassGen) (X : ClassCtor)
    (hns : G.nP + G.slots.length < 2 ^ 64) (g x d nF wso wsl fvso fvsl : Word) (ws fvs : List EIdx)
    (hnF : nF.toNat = X.nF) (n : Nat) :
    ∀ (m : Mem) (a : AState) (i l : Word), StageR vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    DecB (fun m => decCC m x.toNat) m X →
    decHL m wso.toNat wsl.toNat = some ws → wso.toNat + wsl.toNat ≤ iwTop m →
    decHL m fvso.toNat fvsl.toNat = some fvs → fvso.toNat + fvsl.toNat ≤ iwTop m →
    l.toNat ≤ i.toNat → i.toNat ≤ X.nF → AbsOK m →
    RSim (misW n m g x d nF wso wsl fvso fvsl i l)
      (ConRon.Arena.ClassGen.minorTy.ihsGo G X d.toNat fvs ws l.toNat (rec2Recs X i.toNat)) a
      (fun b a' o => StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [misW] at hb
  | succ n ih =>
  intro m a i l hS hG hX hws hwb hfvs hfb hli hiX hA
  have hsz := hS.iw.iwSize
  by_cases hend : nF ≤ i
  · rw [misW_end (h := hend)]
    have : X.nF ≤ i.toNat := by rw [← hnF]; exact UInt64.le_iff_toNat_le.mp hend
    rw [rec2Recs_end this, ConRon.Arena.ClassGen.minorTy.ihsGo.eq_1]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, ⟨rfl, by simp [decHL, hslice?], by simp⟩, hA⟩
  have hlt : i.toNat < X.nF := by
    rw [← hnF]; exact UInt64.lt_iff_toNat_lt.mp (by simpa using hend)
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := nF.toNat_lt; omega
  rw [rec2Recs_step hlt]
  obtain ⟨hord, hrec⟩ := rec2IsTag (hX.get (decCC_mono _)) hsz (i := i)
  cases hk : X.kinds.getD i.toNat .ordinary with
  | ordinary =>
    rw [misW_ord (h := hend) (ht := hord hk)]
    simp only [List.nil_append]
    have hih := ih m a (i + 1) l hS hG hX hws hwb hfvs hfb (by omega) (by omega) hA
    rw [hi1] at hih
    refine RSim.bindPure (K := isK3) rfl hih ?_
    rintro ⟨r, m'⟩ o a' - ⟨hS', hg', ho, hA'⟩
    refine RSim.pure_some ⟨hS', hg', ?_, hA'⟩
    cases o with
    | none => exact ho
    | some ihs => exact ho
  | recursive t tele =>
  obtain ⟨ht, et, tlt, ete, telelt⟩ := hrec t tele hk
  simp only [List.singleton_append]
  by_cases ov1 : d + nF < d
  · rw [misW_ov1 (h := hend) (ht := ht) (h1 := ov1)]; exact RSim.none
  by_cases ov2 : d + nF + l < d + nF
  · rw [misW_ov2 (h := hend) (ht := ht) (h1 := ov1) (h2 := ov2)]; exact RSim.none
  have he : (d + nF + l).toNat = d.toNat + X.nF + l.toNat := by
    have a1 : ¬ (d + nF).toNat < d.toNat := fun x => ov1 (UInt64.lt_iff_toNat_lt.mpr x)
    have a2 : ¬ (d + nF + l).toNat < (d + nF).toNat := fun x => ov2 (UInt64.lt_iff_toNat_lt.mpr x)
    rw [UInt64.toNat_add] at a1
    rw [UInt64.toNat_add (d + nF)] at a2
    have b1 := d.toNat_lt; have b2 := nF.toNat_lt; have b3 := l.toNat_lt
    have c1 : (d + nF).toNat = d.toNat + nF.toNat := by rw [UInt64.toNat_add]; omega
    rw [UInt64.toNat_add, c1, ← hnF]; rw [c1] at a2; omega
  have tt : (UInt64.ofNat t : Word).toNat = t := UInt64.toNat_ofNat_of_lt' tlt
  have tte : (UInt64.ofNat tele : Word).toNat = tele := UInt64.toNat_ofNat_of_lt' telelt
  rw [ConRon.Arena.ClassGen.minorTy.ihsGo.eq_2, ← he, ← tt, ← tte]
  rw [misW_rec (h := hend) (ht := ht) (h1 := ov1) (h2 := ov2), et, ete]
  rcases n with _ | n
  · intro b hb; simp [i1W, isK1] at hb
  refine i1W_sim n m a g _ _ wso wsl fvso fvsl i (d + nF + l) G ws fvs hS hG hns hws hwb hfvs hfb hA
    (isK1 (n + 1) g x d nF wso wsl fvso fvsl i l) (by simp [isK1]) _ _ ?_ ?_
  · intro m' a' hS' hg' hA'
    rw [isK1_fail (h := rfl)]
    exact RSim.pure_some ⟨hS', hg', rfl, hA'⟩
  · intro m' a' w hS' hg' hw hA'
    rw [isK1_ok (h := by simp)]
    simp only [List.tail_cons, List.headD_cons]
    have hl1 : (l + 1).toNat = l.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := nF.toNat_lt; omega
    have hih := ih m' a' (i + 1) (l + 1) hS' (hG.grow (decCG_mono _) hg') (hX.grow (decCC_mono _) hg')
      (by rw [decHL_grow hg' hwb]; exact hws) (Nat.le_trans hwb hg'.iw)
      (by rw [decHL_grow hg' hfb]; exact hfvs) (Nat.le_trans hfb hg'.iw) (by omega) (by omega) hA'
    rw [hi1, hl1] at hih
    refine RSim.bind (K := isK2 (n + 1) w) rfl hih ?_
    rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho, hA2⟩
    dsimp only at hS2 hg2 ho
    rcases o with _ | ihs
    · rw [isK2_fail (h := ho)]; exact RSim.pure_some ⟨hS2, hg'.trans hg2, rfl, hA2⟩
    obtain ⟨h21, hd2, hb2⟩ := ho
    rw [isK2_ok (h := by rw [h21]; decide)]
    refine RSim.lstep (K := isK4) rfl fun ⟨r3, m3⟩ h3 => ?_
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hw hd2
    rw [isK4_some]
    exact RSim.pure_some ⟨hS3, hg'.trans (hg2.trans hg3), ⟨rfl, by simpa using hd3,
      by simp only [List.tail_cons, List.headD_cons]; exact Nat.le_of_eq ht3⟩, consW_afr h3 hA2⟩

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- The model of `class_gen_minor_ty_concl2` simulates the twin's tail of `minorTy`. -/
theorem c2W_sim (n : Nat) (m : Mem) (a : AState) (g c d nPc fo fl ihso ihsl rao ral capp : Word)
    (G : ClassGen) (NPC : Nat) (fvs ihs ra : List EIdx) (hS : StageR vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hnpc : nPc.toNat = NPC)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hihs : decHL m ihso.toNat ihsl.toNat = some ihs) (hib : ihso.toNat + ihsl.toNat ≤ iwTop m)
    (hra : decHL m rao.toNat ral.toNat = some ra) (hrb : rao.toNat + ral.toNat ≤ iwTop m) (hcapp : H capp)
    (hA : AbsOK m) :
    RSim (c2W (n + 1) m g c d nPc fo fl ihso ihsl rao ral capp) (do
      let mc ← G.motVar c.toNat
      let concl ← mkAppN mc (List.drop NPC ra ++ [decI capp])
      let fbs ← List.mapM G.binder fvs
      let r ← ConRon.Arena.closeTelescope (fbs ++ ihs) d.toNat concl
      pure (some r)) a (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  sorry

end sims

/-- The constructor's name word, read through its record. -/
theorem rec2CCName {m : Mem} {x : Word} {X : ClassCtor} (hX : decCC m x.toNat = some X)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (rdW (m.arr64 IW) x) = w ∧ H w ∧ decI w = X.cv.name := by
  sorry

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem cW_sim (n : Nat) (m : Mem) (a : AState) (g c x d lvls ds0 dl0 nPc fo fl res ihso ihsl : Word)
    (G : ClassGen) (X : ClassCtor) (LV : LsIdx) (NPC : Nat) (DS fvs ihs : List EIdx) (hS : StageR vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) (hres : H res) (hlv : H lvls) (hlvd : decI lvls = LV)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m DS) (hnpc : nPc.toNat = NPC)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hihs : decHL m ihso.toNat ihsl.toNat = some ihs) (hib : ihso.toNat + ihsl.toNat ≤ iwTop m)
    (hA : AbsOK m) :
    RSim (cW (n + 1) m g c x d lvls ds0 dl0 nPc fo fl res ihso ihsl) (do
      let ra ← getAppArgs coreWalkFuel (decI res)
      let cc ← internE (.const X.cv.name LV)
      let capp ← mkAppN cc (DS ++ fvs)
      let mc ← G.motVar c.toNat
      let concl ← mkAppN mc (List.drop NPC ra ++ [capp])
      let fbs ← List.mapM G.binder fvs
      let r ← ConRon.Arena.closeTelescope (fbs ++ ihs) d.toNat concl
      pure (some r)) a (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  sorry

end sims

/-- The decoded result of `class_gen_minor_ty`. -/
theorem mnW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c x d : Word) (G : ClassGen) (X : ClassCtor) (hS : StageR vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) (hA : AbsOK m) :
    RSim (mnW n m g c x d) (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  sorry

end L.Ind

end

end
