import ConAgua.Arena.RecClassSpec.ClassGenRecTy
import ConAgua.Arena.RecClassSpec.MnProg
import ConAgua.Arena.RecClassSpec.PdWAfr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

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
  grind [arena_grind] simp []

l_model classGenMinorTyIh1Tail_spec (p : Prog) (h : MnProg p)
  fns [h.it ↦ itW list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, mknF_spec p h.ad n,
    rec2MotVar_specF p h.toMtProg h.fvf h.fvp h.ifv h.sv h.ms h.mv n,
    slSnoc_specW p h.alloc h.copy h.snoc n, classGenMinorTyIh1Close_spec p h n]
  grind [arena_grind] simp []

l_model classGenMinorTyIh1_spec (p : Prog) (h : MnProg p)
  fns [h.i1 ↦ i1W list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, rec2IhParts_specF p h.ihp h.ad h.opf n,
    classGenMinorTyIh1Tail_spec p h n]
  grind [arena_grind] simp []

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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec,
      classGenMinorTyIh1_spec p h n, slCons_specW p h.alloc h.copy h.cons n, ih]
    all_goals subst_vars
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq,
      decide_eq_true_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, isTag, isKp, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9]

end specs

/-! ## `class_gen_minor_ty_close`, `_concl2`, `_concl`, `_body`, `class_gen_minor_ty` -/

l_model classGenMinorTyClose_spec (p : Prog) (h : MnProg p)
  fns [h.mcl ↦ mcW list]
  specs [ftdsF_spec p h.ad n, slAppend_specW p h.alloc h.copy h.app n,
    closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct h.ab n]
  grind [arena_grind] simp []

l_model classGenMinorTyConcl2_spec (p : Prog) (h : MnProg p)
  fns [h.c2 ↦ c2W list]
  specs [rec2MotVar_specF p h.toMtProg h.fvf h.fvp h.ifv h.sv h.ms h.mv n,
    slSnoc_specW p h.alloc h.copy h.snoc n, mknF_spec p h.ad n, classGenMinorTyClose_spec p h n]
  grind [arena_grind] simp []

l_model classGenMinorTyConcl_spec (p : Prog) (h : MnProg p)
  fns [h.cc ↦ cW list]
  specs [gaaF_spec p h.ad n, internConst_spec p h.cf h.cp h.ic n,
    slAppend_specW p h.alloc h.copy h.app n, mknF_spec p h.ad n, classGenMinorTyConcl2_spec p h n]
  grind [arena_grind] simp [rdW_eq]

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
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64]
  all_goals (try simp only [Locals.init, List.getD_cons_zero,
    BinOp.eval] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq]

theorem classGenMinorTy_spec (n : Nat) (s₀ : St) (g c x d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty" [g, c, x, d]
    ⦃fun r s' => LocEq s' s₀ ∧ mnW n s₀.mem g c x d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.mn]
  simp only [callFn, classGenMinorTy]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma h.na n, classGenMinorCi_spec p h n,
    classGenMinorTyBody_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ,
    BinOp.eval, Nat.reduceEqDiff, reduceIte] at *)
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

theorem rec2SimIh (n : Nat) {m : Mem} {a : AState} (hS : StageR dn vis fe m a) {g : Word} {G : ClassGen}
    (hG : DecB (fun m => decCG m g.toNat) m G) (t tele : Word) {w : Word} (hw : H w) (d : Word)
    (hA : AbsOK m) :
    RSim (rec2IhF n m g t tele w d) (G.ihParts t.toNat tele.toNat (decI w) d.toNat) a
      (fun b a' x => (StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ IhRes b.2 b.1 x) ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rintro ⟨r, m'⟩ h
  obtain ⟨res, a', hrun, hS', hg, hres, hA'⟩ := ihW_ok dn vis fe m m' a g t tele w d G r hS hw
    (rec2CG_cls (hG.get (decCG_mono _))) hS.2.2.2.1 hA h
  exact ⟨res, a', hrun, ⟨hS', hg, hres⟩, hA'⟩

/-- `class_gen_minor_ty_ih1`, in continuation form: the twin's body of `ihsGo` at one recursive
field, then `REST` at the inductive hypothesis. -/
theorem i1W_sim {β γ : Type} (n : Nat) (m : Mem) (a : AState) (g t tele wso wsl fvso fvsl i e : Word)
    (G : ClassGen) (ws fvs : List EIdx) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hws : decHL m wso.toNat wsl.toNat = some ws) (hwb : wso.toNat + wsl.toNat ≤ iwTop m)
    (hfvs : decHL m fvso.toNat fvsl.toNat = some fvs) (hfb : fvso.toNat + fvsl.toNat ≤ iwTop m)
    (hA : AbsOK m)
    (K : Option (List Word × Mem) → Option β) (hK : K none = none) (REST : EIdx → AM (Option γ))
    (Q : β → AState → Option γ → Prop)
    (hnone : ∀ m' a', StageR dn vis fe m' a' → IWGrow m m' → AbsOK m' →
      RSim (K (some ([0, 0], m'))) (pure none) a' Q)
    (hsome : ∀ m' a' w, StageR dn vis fe m' a' → IWGrow m m' → H w → AbsOK m' →
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
  rw [i1W.arm1]
  refine RSim.bind (K := fun o => K (i1W.k_expr_get_d n g t tele fvso fvsl i e o)) hK
    (RSim.withF (rec2SimExprGetD n hS hws (hS.lt64 hwb)) (fun _ hb => exprGetDF_afr hb)) ?_
  rintro ⟨r1, m1⟩ w a1 - ⟨⟨hS1, hg1, hwH, hwd⟩, hf1⟩
  have hA1 := hf1 hA
  dsimp only at hS1 hg1 hwH hwd
  subst hwd
  rw [i1W.k_expr_get_d.arm1]
  refine RSim.bind (K := fun o => K (i1W.k_class_gen_ih_parts n g t fvso fvsl i e o)) hK
    (rec2SimIh n hS1 (hG.grow (decCG_mono _) hg1) t tele hwH e hA1) ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨⟨hS2, hg2, ho⟩, hA2⟩
  dsimp only at hS2 hg2 ho
  have hg12 := hg1.trans hg2
  rcases o with _ | p2
  · rw [i1W.k_class_gen_ih_parts.arm1 (hc1 := ho)]; exact hnone m2 a2 hS2 hg12 hA2
  obtain ⟨xs, idx⟩ := p2
  obtain ⟨h21, hxs, hxb, hidx, hidb⟩ := ho
  rw [i1W.k_class_gen_ih_parts.arm2 (hc1 := by rw [h21]; decide)]
  rcases n with _ | n
  · rw [show (itW 0 _ _ _ _ _ _ _ _ _ _ _) = none from rfl]; exact (by rw [show i1W.k_class_gen_minor_ty_ih1_tail none = none from rfl, hK]; exact RSim.none)
  rw [itW.arm1]
  refine RSim.bind (K := fun o => K (i1W.k_class_gen_minor_ty_ih1_tail (itW.k_expr_get_d n g t _ _ _ _ e o))) hK
    (RSim.withF (rec2SimExprGetD n hS2 (by rw [decHL_grow hg12 hfb]; exact hfvs) (hS2.lt64 (Nat.le_trans hfb hg12.1)))
      (fun _ hb => exprGetDF_afr hb)) ?_
  rintro ⟨r3, m3⟩ f a3 - ⟨⟨hS3, hg3, hfH, hfd⟩, hf3⟩
  dsimp only at hS3 hg3 hfH hfd
  subst hfd
  rw [itW.k_expr_get_d.arm1]
  refine RSim.bind (K := fun o => K (i1W.k_class_gen_minor_ty_ih1_tail (itW.k_mk_app_n_f n g t _ _ _ _ e o))) hK
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hfH xs).sim ⟨hS3, by rw [decHL_grow hg3 hxb]; exact hxs⟩)
      (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r4, m4⟩ fx a4 - ⟨⟨hS4, hg4, hfxH, hfxd⟩, hf4⟩
  dsimp only at hS4 hg4 hfxH hfxd
  subst hfxd
  rw [itW.k_mk_app_n_f.arm1]
  have hg24 := hg3.trans hg4
  refine RSim.bind (K := fun o => K (i1W.k_class_gen_minor_ty_ih1_tail (itW.k_class_gen_mot_var n _ _ _ _ e (r4.headD 0) o))) hK
    (RSim.withF (rec2SimMotVar n hS4 t (hG.grow (decCG_mono _) (hg12.trans hg24)) hns)
      (fun _ hb => rec2MotVarF_afr hb)) ?_
  rintro ⟨r5, m5⟩ mt a5 - ⟨⟨hS5, hg5, hmtH, hmtd⟩, hf5⟩
  dsimp only at hS5 hg5 hmtH hmtd
  subst hmtd
  rw [itW.k_class_gen_mot_var.arm1]
  have hg25 := hg24.trans hg5
  refine RSim.lstep (K := fun o => K (i1W.k_class_gen_minor_ty_ih1_tail (itW.k_sl_snoc n _ _ e (r5.headD 0) o))) hK fun ⟨r6, m6⟩ h6 => ?_
  obtain ⟨hr6, hd6, hg6, -, -, ht6⟩ := snocW_dec h6 hS5.2.2.2.1 hS5.2.2.2.2.2 (Nat.le_trans hidb hg25.1) hfxH
    (by rw [decHL_grow hg25 hidb]; exact hidx)
  have hS6 := snocW_stage h6 hS5
  have hA6 := snocW_afr h6 (hf5 (hf4 (hf3 hA2)))
  rw [itW.k_sl_snoc.arm1, hr6]
  simp only [List.headD_cons, List.tail_cons]
  refine RSim.bind (K := fun o => K (i1W.k_class_gen_minor_ty_ih1_tail (itW.k_mk_app_n_f_2 n _ _ e o))) hK
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hmtH (idx ++ [decI (r4.headD 0)])).sim ⟨hS6, hd6⟩)
      (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r7, m7⟩ body a7 - ⟨⟨hS7, hg7, hbH, hbd⟩, hf7⟩
  dsimp only at hS7 hg7 hbH hbd
  subst hbd
  rw [itW.k_mk_app_n_f_2.arm1]
  have hg27 := hg25.trans (hg6.trans hg7)
  rw [rec2MapM_genBinder]
  -- `class_gen_minor_ty_ih1_close`
  rcases n with _ | n
  · rw [show (iclW 0 _ _ _ _ _) = none from rfl]
    exact (by rw [show itW.k_class_gen_minor_ty_ih1_close none = none from rfl, show i1W.k_class_gen_minor_ty_ih1_tail none = none from rfl, hK]; exact RSim.none)
  rw [iclW.arm1]
  refine RSim.bind (K := fun o => K (i1W.k_class_gen_minor_ty_ih1_tail (itW.k_class_gen_minor_ty_ih1_close (iclW.k_fvar_type_ds n e (r7.headD 0) o)))) hK
    (RSim.withF ((ftdsF_ok dn vis fe _ _ xs).sim
      ⟨hS7, by rw [decHL_grow hg27 hxb]; exact hxs, fun _ => Nat.le_trans hxb hg27.1⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r8, m8⟩ bs a8 - ⟨⟨hS8, hg8, hbs, hbb⟩, hf8⟩
  dsimp only at hS8 hg8 hbs hbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hbs hbb
  by_cases hov : e + r8.tail.headD 0 < e
  · rw [iclW.k_fvar_type_ds.abort1 (hc1 := hov)]; simp only [show itW.k_class_gen_minor_ty_ih1_close none = none from rfl, show i1W.k_class_gen_minor_ty_ih1_tail none = none from rfl, hK]
    exact RSim.none
  rw [iclW.k_fvar_type_ds.arm1 (hc1 := hov)]
  have hel : e.toNat + (r8.tail.headD 0).toNat < 2 ^ 64 := by
    have := nctAddNowrap (a := r8.tail.headD 0) (b := e) (by rwa [UInt64.add_comm]); omega
  refine RSim.bind (K := fun o => K (i1W.k_class_gen_minor_ty_ih1_tail (itW.k_class_gen_minor_ty_ih1_close (iclW.k_close_telescope o)))) hK (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m8 b.2 ∧ decW0E b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r9, m9⟩ h9
    obtain ⟨x, a', hrun, hS', hg, hx, hA9⟩ := closeW_ok n dn fe vis m8 m9 a8 _ _ e _ bs r9 h9 hS8 hbH hbs
      (hS8.lt64 hbb) hbb hel (hf8 (hf7 hA6))
    exact ⟨x, a', hrun, hS', hg, hx, hA9⟩
  rintro ⟨r9, m9⟩ ih a9 - ⟨hS9, hg9, ⟨hih, hihd⟩, hA9⟩
  dsimp only at hS9 hg9 hih hihd
  subst hihd
  simp only [iclW.k_close_telescope.arm1, itW.k_class_gen_minor_ty_ih1_close.arm1, i1W.k_class_gen_minor_ty_ih1_tail.arm1, List.headD_cons, List.tail_cons]
  exact hsome m9 a9 _ hS9 (hg12.trans (hg27.trans (hg8.trans hg9))) hih hA9

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
    ∀ (m : Mem) (a : AState) (i l : Word), StageR dn vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    DecB (fun m => decCC m x.toNat) m X →
    decHL m wso.toNat wsl.toNat = some ws → wso.toNat + wsl.toNat ≤ iwTop m →
    decHL m fvso.toNat fvsl.toNat = some fvs → fvso.toNat + fvsl.toNat ≤ iwTop m →
    l.toNat ≤ i.toNat → i.toNat ≤ X.nF → AbsOK m →
    RSim (misW n m g x d nF wso wsl fvso fvsl i l)
      (ConRon.Arena.ClassGen.minorTy.ihsGo G X d.toNat fvs ws l.toNat (rec2Recs X i.toNat)) a
      (fun b a' o => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ decIHO b.2 b.1 o ∧ AbsOK b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [misW] at hb
  | succ n ih =>
  intro m a i l hS hG hX hws hwb hfvs hfb hli hiX hA
  have hsz := hS.2.2.2.1
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
      (by rw [decHL_grow hg' hwb]; exact hws) (Nat.le_trans hwb hg'.1)
      (by rw [decHL_grow hg' hfb]; exact hfvs) (Nat.le_trans hfb hg'.1) (by omega) (by omega) hA'
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
    (G : ClassGen) (NPC : Nat) (fvs ihs ra : List EIdx) (hS : StageR dn vis fe m a)
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
  rw [c2W.arm1]
  refine RSim.bind (K := c2W.k_class_gen_mot_var n d nPc fo fl ihso ihsl rao ral capp) rfl
    (RSim.withF (rec2SimMotVar n hS c hG hns) (fun _ hb => rec2MotVarF_afr hb)) ?_
  rintro ⟨r1, m1⟩ mc a1 - ⟨⟨hS1, hg1, hmcH, hmcd⟩, hf1⟩
  dsimp only at hS1 hg1 hmcH hmcd
  subst hmcd
  have hk1 : c2W.k_class_gen_mot_var n d nPc fo fl ihso ihsl rao ral capp (some (r1, m1)) =
      c2W.k_sl_snoc n d fo fl ihso ihsl (r1.headD 0)
        (snocW n m1 (if nPc < ral then rao + nPc else rao) (if nPc < ral then ral - nPc else 0) capp) := by
    by_cases hc : nPc < ral
    · rw [c2W.k_class_gen_mot_var.arm1 (hc1 := hc)]; simp only [c2W.j1, hc, ↓reduceIte]
    · rw [c2W.k_class_gen_mot_var.arm2 (hc1 := hc)]; simp only [c2W.j1, hc, ↓reduceIte]
  rw [hk1]
  have hra1 : decHL m1 rao.toNat ral.toNat = some ra := by rw [decHL_grow hg1 hrb]; exact hra
  have hrb1 := Nat.le_trans hrb hg1.1
  have hsl : decHL m1 (if nPc < ral then rao + nPc else rao).toNat (if nPc < ral then ral - nPc else 0).toNat =
      some (ra.drop NPC) ∧
      (if nPc < ral then rao + nPc else rao).toNat + (if nPc < ral then ral - nPc else 0).toNat ≤ iwTop m1 := by
    have hlen := decHL_length m1 hra1
    by_cases hc : nPc < ral
    · have hc' : nPc.toNat < ral.toNat := UInt64.lt_iff_toNat_lt.mp hc
      have e1 : (rao + nPc).toNat = rao.toNat + nPc.toNat := by
        rw [UInt64.toNat_add]; have := hS1.lt64 hrb1; omega
      have e2 : (ral - nPc).toNat = ral.toNat - nPc.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hc)]
      simp only [ite_eq_left hc, e1, e2]
      rw [← hnpc]
      exact ⟨decHL_drop nPc.toNat hra1 (by omega), by omega⟩
    · have hc' : ral.toNat ≤ nPc.toNat := by
        have : ¬ nPc.toNat < ral.toNat := fun x => hc (UInt64.lt_iff_toNat_lt.mpr x)
        omega
      simp only [ite_eq_right hc]
      rw [List.drop_eq_nil_of_le (by rw [← hnpc]; omega)]
      exact ⟨by simp [decHL, hslice?], by simp; omega⟩
  refine RSim.lstep (K := c2W.k_sl_snoc n d fo fl ihso ihsl (r1.headD 0)) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hr2, hd2, hg2, -, -, ht2⟩ := snocW_dec h2 hS1.2.2.2.1 hS1.2.2.2.2.2 hsl.2 hcapp hsl.1
  have hS2 := snocW_stage h2 hS1
  have hA2 := snocW_afr h2 (hf1 hA)
  rw [c2W.k_sl_snoc.arm1, hr2]
  simp only [List.headD_cons, List.tail_cons]
  refine RSim.bind (K := c2W.k_mk_app_n_f n d fo fl ihso ihsl) rfl
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hmcH (ra.drop NPC ++ [decI capp])).sim ⟨hS2, hd2⟩)
      (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r3, m3⟩ body a3 - ⟨⟨hS3, hg3, hbH, hbd⟩, hf3⟩
  dsimp only at hS3 hg3 hbH hbd
  subst hbd
  rw [c2W.k_mk_app_n_f.arm1, rec2MapM_genBinder]
  have hg13 := hg1.trans (hg2.trans hg3)
  rcases n with _ | n
  · intro b hb; simp [mcW, c2W.k_class_gen_minor_ty_close] at hb
  rw [mcW.arm1]
  refine RSim.bind (K := fun o => c2W.k_class_gen_minor_ty_close (mcW.k_fvar_type_ds n ihso ihsl d (r3.headD 0) o)) rfl
    (RSim.withF ((ftdsF_ok dn vis fe _ _ fvs).sim
      ⟨hS3, by rw [decHL_grow hg13 hfb]; exact hfvs, fun _ => Nat.le_trans hfb hg13.1⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r4, m4⟩ fbs a4 - ⟨⟨hS4, hg4, hfbs, hfbb⟩, hf4⟩
  dsimp only at hS4 hg4 hfbs hfbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hfbs hfbb
  rw [mcW.k_fvar_type_ds.arm1]
  have hg14 := hg13.trans hg4
  refine RSim.lstep (K := fun o => c2W.k_class_gen_minor_ty_close (mcW.k_sl_append n d (r3.headD 0) o)) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hS5, hg5, hd5, hb5⟩ := rec2AppendW_dec h5 hS4 (decHL_decB hfbs hfbb)
    (by rw [decHL_grow hg14 hib]; exact hihs) (Nat.le_trans hib hg14.1)
  by_cases hov : d + r5.tail.headD 0 < d
  · rw [mcW.k_sl_append.abort1 (hc1 := hov)]; exact RSim.none
  rw [mcW.k_sl_append.arm1 (hc1 := hov)]
  have hdl : d.toNat + (r5.tail.headD 0).toNat < 2 ^ 64 := by
    have := nctAddNowrap (a := r5.tail.headD 0) (b := d) (by rwa [UInt64.add_comm]); omega
  refine RSim.bind (K := fun o => c2W.k_class_gen_minor_ty_close (mcW.k_close_telescope o)) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m5 b.2 ∧ decW0E b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r6, m6⟩ h6
    obtain ⟨x, a', hrun, hS', hg, hx, hA6⟩ := closeW_ok n dn fe vis m5 m6 a4 _ _ d _ _ r6 h6 hS5 hbH hd5
      (hS5.lt64 hb5) hb5 hdl (appendW_afr h5 (hf4 (hf3 hA2)))
    exact ⟨x, a', hrun, hS', hg, hx, hA6⟩
  rintro ⟨r6, m6⟩ x a6 - ⟨hS6, hg6, hx, hA6⟩
  simp only [mcW.k_close_telescope.arm1, c2W.k_class_gen_minor_ty_close.arm1]
  exact RSim.pure_some ⟨⟨hS6, hg14.trans (hg5.trans hg6), rfl, by simpa [decW0E] using hx⟩, hA6⟩

end sims

/-- The constructor's name word, read through its record. -/
theorem rec2CCName {m : Mem} {x : Word} {X : ClassCtor} (hX : decCC m x.toNat = some X)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (rdW (m.arr64 IW) x) = w ∧ H w ∧ decI w = X.cv.name := by
  simp only [decCC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hX
  obtain ⟨q, hq, cv, hcv, nF, hnF, ks, hks, y4, hy4, y5, hy5, rfl⟩ := hX
  obtain ⟨eq, tq⟩ := rec2RdN (w := x) (k := 0) (by simpa using hq) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at eq
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv
  obtain ⟨nm, hnm, lps, hlps, ty, hty, rfl⟩ := hcv
  obtain ⟨w, hw, hwl, hwd⟩ := hd?_some hnm
  exact ⟨w, by rw [eq]; exact rdW_of_get? tq.symm hw, hwl, hwd.symm⟩

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem cW_sim (n : Nat) (m : Mem) (a : AState) (g c x d lvls ds0 dl0 nPc fo fl res ihso ihsl : Word)
    (G : ClassGen) (X : ClassCtor) (LV : LsIdx) (NPC : Nat) (DS fvs ihs : List EIdx) (hS : StageR dn vis fe m a)
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
  rw [cW.arm1]
  refine RSim.bind (K := cW.k_get_app_args_f n g c x d lvls ds0 dl0 nPc fo fl ihso ihsl) rfl
    (RSim.withF (simGetAppArgs hS hres) (fun _ hb => gaaF_afr hb)) ?_
  rintro ⟨r1, m1⟩ ra a1 - ⟨⟨hS1, hg1, hra, hrb⟩, hf1⟩
  dsimp only at hS1 hg1 hra hrb
  simp only [getD_zero, Nat.zero_add, getD_one] at hra hrb
  rw [cW.k_get_app_args_f.arm1]
  obtain ⟨nw, enw, hnwH, hnwd⟩ := rec2CCName (hX.stab (decCC_mono _) m1 hg1) hS1.2.2.2.1
  rw [enw]
  subst hlvd
  refine RSim.bind (K := cW.k_intern_const n g c d ds0 dl0 nPc fo fl ihso ihsl (r1.headD 0) (r1.tail.headD 0)) rfl
    (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m1 b.2 ∧ x = decE b.1 ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨cc, m2⟩ h2
    obtain ⟨a', hrun, hS', hg⟩ := internConst_stage hS1 nw lvls hnwH hlv h2
    rw [hnwd] at hrun
    exact ⟨decE cc, a', hrun, hS', hg, rfl, ceinternW_afr h2 (hf1 hA)⟩
  rintro ⟨cc, m2⟩ ccx a2 - ⟨hS2, hg2, rfl, hA2⟩
  dsimp only at hS2 hg2
  by_cases hbig : 4294967296 ≤ cc
  · rw [cW.k_intern_const.abort1 (hc1 := hbig)]; exact RSim.none
  rw [cW.k_intern_const.arm1 (hc1 := hbig)]
  have hccH : H cc := by
    have : ¬ (4294967296 : Word).toNat ≤ cc.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg12 := hg1.trans hg2
  refine RSim.lstep (K := cW.k_sl_append n g c d nPc fo fl ihso ihsl (r1.headD 0) (r1.tail.headD 0) cc) rfl
    fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hd3, hb3⟩ := rec2AppendW_dec h3 hS2 (hds.grow (OMono.decHL _ _) hg12)
    (by rw [decHL_grow hg12 hfb]; exact hfvs) (Nat.le_trans hfb hg12.1)
  rw [cW.k_sl_append.arm1]
  refine RSim.bind (K := cW.k_mk_app_n_f n g c d nPc fo fl ihso ihsl (r1.headD 0) (r1.tail.headD 0)) rfl
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hccH (DS ++ fvs)).sim ⟨hS3, hd3⟩) (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r4, m4⟩ capp a4 - ⟨⟨hS4, hg4, hcH, hcd⟩, hf4⟩
  dsimp only at hS4 hg4 hcH hcd
  subst hcd
  rw [cW.k_mk_app_n_f.arm1]
  have hg14 := hg12.trans (hg3.trans hg4)
  rcases n with _ | n
  · intro b hb; simp [c2W, cW.k_class_gen_minor_ty_concl2] at hb
  refine RSim.bindPure (K := cW.k_class_gen_minor_ty_concl2) rfl (c2W_sim n m4 a4 g c d nPc fo fl ihso ihsl _ _ _ G NPC fvs ihs ra hS4
    (hG.grow (decCG_mono _) hg14) hns hnpc (by rw [decHL_grow hg14 hfb]; exact hfvs) (Nat.le_trans hfb hg14.1)
    (by rw [decHL_grow hg14 hib]; exact hihs) (Nat.le_trans hib hg14.1)
    (by rw [decHL_grow (hg2.trans (hg3.trans hg4)) hrb]; exact hra) (Nat.le_trans hrb (hg2.trans (hg3.trans hg4)).1)
    hcH (hf4 (appendW_afr h3 hA2))) ?_
  rintro ⟨r5, m5⟩ o a5 - ⟨⟨hS5, hg5, ho⟩, hA5⟩
  rw [cW.k_class_gen_minor_ty_concl2.arm1]
  refine RSim.pure_some ⟨⟨hS5, hg14.trans hg5, ?_⟩, hA5⟩
  cases o with
  | none => exact ho
  | some e => obtain ⟨h1, h2⟩ := ho; exact ⟨by simpa using h1, by simpa [decW0E] using h2⟩

end sims

/-- The decoded result of `class_gen_minor_ty`. -/
theorem mnW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c x d : Word) (G : ClassGen) (X : ClassCtor) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) (hA : AbsOK m) :
    RSim (mnW n m g c x d) (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [mnW_eq]
  unfold ConRon.Arena.ClassGen.minorTy
  have hsz := hS.2.2.2.1
  obtain ⟨-, hgt, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4]
  have htop := hS.2.1
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by omega); omega
    · have := rec2DecB_PL_top hcls hl; omega
  refine RSim.bind (K := mnK1 n g c x d) rfl (RSim.withF (rec2SimTMA dn vis fe n m a _ _ c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)) (fun _ hb => tmaW_afr hb)) ?_
  rintro ⟨r1, m1⟩ tm a1 - ⟨⟨hS1, hg1, hTM, hds⟩, hf1⟩
  have hA1 := hf1 hA
  dsimp only at hS1 hg1 hTM hds
  rw [mnK1_some]
  have hsz1 := hS1.2.2.2.1
  obtain ⟨-, hlv, ⟨o, l, ho, hl, -⟩, hnpc, -⟩ := rec2DecTM_parts hTM
  have hds1 := hds o l ho hl
  obtain ⟨vl, evl, hvl, dvl⟩ := iwH_rdW_at (w := r1.headD 0) (k := 1) hlv hsz1
  obtain ⟨eo, to⟩ := rec2RdN (w := r1.headD 0) (k := 2) ho hsz1
  obtain ⟨el, tl⟩ := rec2RdN (w := r1.headD 0) (k := 3) hl hsz1
  obtain ⟨en, tn⟩ := rec2RdN (w := r1.headD 0) (k := 4) hnpc hsz1
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at evl eo el en
  rw [evl, eo, el, en]
  rw [← to, ← tl] at hds1
  rcases n with _ | n
  · intro b hb; simp [bW, cK4] at hb
  rw [bW.arm1]
  -- the constructor's words
  have hX1 := hX.stab (decCC_mono _) m1 hg1
  obtain ⟨hnF, htyD, htyN⟩ := rec2CC_parts hX1
  obtain ⟨enF, tnF⟩ := rec2RdN (w := x) (k := 1) hnF hsz1
  obtain ⟨vD, evD, hvD, dvD⟩ := iwH_rdW_at (w := x) (k := 4) htyD hsz1
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at enF evD
  rw [enF, evD]
  have ho := simOpenPisF (k := UInt64.ofNat X.nF) (i := d) hS1 hA1 hvD
  rw [tnF, dvD] at ho
  refine RSim.bind (K := fun o => cK4 (bW.k_open_pis_at_fvars_f n g c x d vl _ _ _ o)) rfl ho ?_
  rintro ⟨r2, m2⟩ o2 a2 - ⟨⟨hS2, hg2, ho2⟩, hA2⟩
  dsimp only at hS2 hg2 ho2
  rcases o2 with _ | p2
  · rw [bW.k_open_pis_at_fvars_f.arm1 (hc1 := ho2)]; exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, rfl⟩, hA2⟩
  obtain ⟨fvs, res⟩ := p2
  obtain ⟨h21, ⟨hfvs, hfb⟩, hrH, hrd⟩ := ho2
  simp only [getD_one, getD_two, Nat.reduceAdd] at hfvs hfb
  simp only [drop3_headD] at hrH hrd
  rw [bW.k_open_pis_at_fvars_f.arm2 (hc1 := by rw [h21]; decide)]
  have hg12 := hg1.trans hg2
  have hX2 := hX.stab (decCC_mono _) m2 hg12
  obtain ⟨-, -, htyN2⟩ := rec2CC_parts hX2
  obtain ⟨vN, evN, hvN, dvN⟩ := iwH_rdW_at (w := x) (k := 5) htyN2 hS2.2.2.2.1
  simp only [show UInt64.ofNat 5 = (5 : Word) from rfl] at evN
  rw [evN]
  refine RSim.bind (K := fun o => cK4 (bW.k_target_pi_doms_with n g c x d vl _ _ _ _ _ _ o)) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m2 b.2 ∧ PdRes b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r3, m3⟩ h3
    obtain ⟨res', a', hrun, hS', hg, hres⟩ := pdW_ok dn vis fe n m2 m3 a2 _ _ vN r3 fvs h3 hS2 hvN hfvs
      (hS2.lt64 hfb) hfb
    rw [dvN] at hrun
    exact ⟨res', a', hrun, hS', hg, hres, pdW_afr _ _ _ _ _ _ _ h3 hA2⟩
  rintro ⟨r3, m3⟩ o3 a3 - ⟨hS3, hg3, ho3, hA3⟩
  dsimp only at hS3 hg3 ho3
  rcases o3 with _ | ws
  · rw [bW.k_target_pi_doms_with.arm1 (hc1 := ho3)]; exact RSim.pure_some ⟨⟨hS3, hg12.trans hg3, rfl⟩, hA3⟩
  obtain ⟨h31, hws, hwb⟩ := ho3
  rw [bW.k_target_pi_doms_with.arm2 (hc1 := by rw [h31]; decide)]
  have hg13 := hg12.trans hg3
  have hX3 := hX.grow (decCC_mono _) hg13
  obtain ⟨hnF3, -, -⟩ := rec2CC_parts (hX3.get (decCC_mono _))
  obtain ⟨enF3, -⟩ := rec2RdN (w := x) (k := 1) hnF3 hS3.2.2.2.1
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at enF3
  rw [enF3]
  have hi := misW_sim dn vis fe G X hns g x d (UInt64.ofNat X.nF) _ _ _ _ ws fvs tnF n m3 a3 0 0 hS3
    (hG.grow (decCG_mono _) hg13) hX3 hws hwb (by rw [decHL_grow hg3 hfb]; exact hfvs)
    (Nat.le_trans hfb hg3.1) (by simp) (by simp) hA3
  simp only [UInt64.toNat_zero] at hi
  have hr : rec2Recs X 0 = (List.range X.nF).filterMap (fun i =>
      match X.kinds.getD i ClassField.ordinary with
      | ClassField.recursive t tele => some (i, t, tele)
      | ClassField.ordinary => none) := rec2Recs_zero X
  refine RSim.bind (K := fun o => cK4 (bW.k_class_gen_minor_ty_ihs_go n g c x d vl _ _ _ _ _ _ o)) rfl
    (hr.symm ▸ hi : RSim _ (ConRon.Arena.ClassGen.minorTy.ihsGo G X d.toNat fvs ws 0 _) a3 _) ?_
  rintro ⟨r4, m4⟩ o4 a4 - ⟨hS4, hg4, ho4, hA4⟩
  dsimp only at hS4 hg4 ho4
  rcases o4 with _ | ihs
  · rw [bW.k_class_gen_minor_ty_ihs_go.arm1 (hc1 := ho4)]; exact RSim.pure_some ⟨⟨hS4, hg13.trans hg4, rfl⟩, hA4⟩
  obtain ⟨h41, hihs, hib⟩ := ho4
  rw [bW.k_class_gen_minor_ty_ihs_go.arm2 (hc1 := by rw [h41]; decide)]
  have hg14 := hg13.trans hg4
  rcases n with _ | n
  · intro b hb; simp [cW, bW.k_class_gen_minor_ty_concl, cK4] at hb
  have hc := cW_sim (dn := dn) (vis := vis) (fe := fe) n m4 a4 g c x d vl _ _ _ _ _ _ _ _ G X tm.lvls tm.nPc
    tm.ds fvs ihs hS4 (hG.grow (decCG_mono _) hg14) hns (hX.grow (decCC_mono _) hg14) hrH hvl dvl
    (hds1.grow (OMono.decHL _ _) (hg2.trans (hg3.trans hg4))) tn (by rw [decHL_grow (hg3.trans hg4) hfb]; exact hfvs)
    (Nat.le_trans hfb (hg3.trans hg4).1) hihs hib hA4
  rw [hrd] at hc
  refine RSim.bindPure (K := fun o => cK4 (bW.k_class_gen_minor_ty_concl o)) rfl hc ?_
  rintro ⟨r5, m5⟩ o5 a5 - ⟨⟨hS5, hg5, ho5⟩, hA5⟩
  simp only [bW.k_class_gen_minor_ty_concl.arm1, cK4_some]
  refine RSim.pure_some ⟨⟨hS5, hg14.trans hg5, ?_⟩, hA5⟩
  cases o5 with
  | none => exact ho5
  | some e => obtain ⟨h1, h2⟩ := ho5; exact ⟨by simpa using h1, by simpa [decW0E] using h2⟩

end L.Ind

end

end
