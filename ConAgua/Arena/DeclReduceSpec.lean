module

public import ConAgua.Rom.CIReadSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclCvg
import ConAgua.L.ModelGen
import ConAgua.Arena.WhnfDeltaRefine
public import ConAgua.Arena.IndCallM
public import ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.DeclArms
public import ConAgua.Arena.IndRealWalk

@[expose] public section

/-!
# Pin-selected ROM values: `reduceOpCvA`, `ofReducePinA`, `reduceDeclPin` (lane `decls3`)

Three twin functions of one shape: read a pin, compare the argument with it, intern one of two
con-leche values (`if c == pin then A else B`). In L: `pin_at(k)`, then `rom_cv`/`rom_expr_pin` at one
of two ids. One model (`selW`) and one relational lemma (`selW_ok`) serve all three; through the
ROM readers' refinements (`RomRefs`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-! ## The model -/

/-- After the stub. -/
def selK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => some ([r2.headD 0], m2)

/-- After the pin read: one of the two ids. -/
def selK (p : Prog) (n : Nat) (f : FnName) (i j c : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if c = r1.headD 0 then selK2 (callW p n f [i] m1) else selK2 (callW p n f [j] m1)

/-- **The model**: `pin_at(k)`, then `f(i)` on a match, else `f(j)`. -/
def selW (p : Prog) : Nat → Mem → Word → Word → FnName → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, c, k, f, i, j => selK p n f i j c (pinAtW m k)

section arms
variable (p : Prog) (n : Nat) (f : FnName) (i j c : Word) (r1 r2 : List Word) (m1 m2 : Mem)
theorem selK_some : selK p n f i j c (some (r1, m1)) =
    if c = r1.headD 0 then selK2 (callW p n f [i] m1) else selK2 (callW p n f [j] m1) := rfl
theorem selK2_some : selK2 (some (r2, m2)) = some ([r2.headD 0], m2) := rfl
end arms

grind_pattern [ind_grind] selK_some => selK p n f i j c (some (r1, m1))
grind_pattern [ind_grind] selK2_some => selK2 (some (r2, m2))

/-! ## The relational lemma -/

/-- **A pin-selected ROM value is the twin's**: `do let x ← pinAt k; if c == x then T i else T j`. -/
theorem selW_ok {α : Type} {vis : Word} {fe : IFEnv}
    {a : AState} {p : Prog} {n : Nat} {m m' : Mem} {c k : Word} {f : FnName} {i j : Word}
    {r : List Word} {T : Nat → AM α} {dec : Mem → List Word → α → Prop}
    (hT : ∀ w, (w = i ∨ w = j) →
      L.Rom.RomRef p f [w] (StageR vis fe) (T w.toNat) (KeepPost vis fe dec))
    (hdec : ∀ m r x, dec m r x → dec m [r.headD 0] x)
    (h : selW p n m c k f i j = some (r, m')) (hS : StageR vis fe m a) (hc : c.toNat < 2 ^ 32) (hk51 : k ≠ 51) :
    ∃ x a', (do let y ← pinAt k.toNat; if (decI c : NIdx) == y then T i.toNat else T j.toNat).run a =
      .ok (x, a') ∧ KeepPost vis fe dec m m' a' r x := by
  cases n with
  | zero => simp [selW] at h
  | succ n =>
  simp only [selW] at h
  rcases h1 : pinAtW m k with _ | ⟨r1, m1⟩ <;> simp only [h1, selK, reduceCtorEq] at h
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.check.pins hk51
  have e1 : r1.headD 0 = pinW m (1 + k.toNat) := by rw [hr1]; rfl
  have hbeq : ((decI c : NIdx) == decI (pinW m (1 + k.toNat))) = decide (c = pinW m (1 + k.toNat)) :=
    decI_beq c _ hc hl1
  have tail : ∀ w, (w = i ∨ w = j) → selK2 (callW p n f [w] m) = some (r, m') →
      ∃ x a', (T w.toNat).run a = .ok (x, a') ∧ KeepPost vis fe dec m m' a' r x := by
    intro w hw h
    rcases h2 : callW p n f [w] m with _ | ⟨r2, m2⟩ <;> simp only [h2, selK2, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨x, a', hrun, hS', hg, hd⟩ := hT w hw n m a r2 m2 hS h2
    exact ⟨x, a', hrun, hS', hg, hdec _ _ _ hd⟩
  rw [hm1] at h
  by_cases he : c = r1.headD 0
  · rw [ite_eq_left he] at h
    obtain ⟨x, a', hrun, hP⟩ := tail i (.inl rfl) h
    rw [e1] at he
    refine ⟨x, a', ?_, hP⟩
    simp only [StateT.run_bind, hrun1, L.Arena.except_ok_bind, he, ite_true,
      beq_self_eq_true]
    exact hrun
  · rw [ite_eq_right he] at h
    obtain ⟨x, a', hrun, hP⟩ := tail j (.inr rfl) h
    rw [e1] at he
    refine ⟨x, a', ?_, hP⟩
    simp only [StateT.run_bind, hrun1, L.Arena.except_ok_bind, hbeq, he, decide_false, Bool.false_eq_true,
      ite_false]
    exact hrun

theorem decRCV_head (m : Mem) (r : List Word) (x : IConstantVal) (h : decRCV m r x) :
    decRCV m [r.headD 0] x := h

theorem decW0E_head (m : Mem) (r : List Word) (x : EIdx) (h : decW0E m r x) :
    decW0E m [r.headD 0] x := h

/-! ## The three functions -/

section specs
variable (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL)
include hpa

theorem reduceOpCvA_specW (hp : p.lookup "reduce_op_cv_a" = some reduceOpCvAL) (n : Nat) (s₀ : St)
    (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_op_cv_a" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ selW p n s₀.mem c 43 "rom_cv" 6 7 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, reduceOpCvAL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n,
        callW_spec p n "rom_cv"] <;>
      finish (gen := 20) [selW]

theorem ofReducePinA_specW (hp : p.lookup "of_reduce_pin_a" = some ofReducePinAL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_pin_a" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ selW p n s₀.mem c 45 "rom_cv" 8 9 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ofReducePinAL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n,
        callW_spec p n "rom_cv"] <;>
      finish (gen := 20) [selW]

theorem reduceDeclPin_specW (hp : p.lookup "reduce_decl_pin" = some reduceDeclPinL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_decl_pin" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ selW p n s₀.mem c 43 "rom_expr_pin" 0 1 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, reduceDeclPinL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n,
        callW_spec p n "rom_expr_pin"] <;>
      finish (gen := 20) [selW]

end specs

section refines
variable (p : Prog) (hpa : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (a₀ : AState)
  (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis c : Word)
  (hS : StageR vis fe s₀.mem a₀) (hc : c.toNat < 2 ^ 32) (hR : L.Rom.RomRefs p)
include hpa hS hc hR

/-- **`reduce_op_cv_a(c)` refines `reduceOpCvA`** (through `rom_cv`'s stub). -/
@[refines ConRon.Arena.reduceOpCvA]
theorem reduceOpCvA_refines (hp : p.lookup "reduce_op_cv_a" = some reduceOpCvAL) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_op_cv_a" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (reduceOpCvA (decI c)) a₀ ∧
      KeepPost vis fe decRCV s₀.mem s'.mem (AM.st (reduceOpCvA (decI c)) a₀) r
        (AM.res (reduceOpCvA (decI c)) a₀); ⊤⦄ := by
  refine triple_post (reduceOpCvA_specW p hpa hp n s₀ c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hP⟩ := selW_ok (T := romCvT)
    (fun w hw => hR.cv vis fe w (by rcases hw with rfl | rfl <;> decide)) decRCV_head hm hS hc (by decide)
  have e : reduceOpCvA (decI c) =
      (do let y ← pinAt (43 : Word).toNat
          if (decI c : NIdx) == y then romCvT (6 : Word).toNat else romCvT (7 : Word).toNat) := rfl
  rw [← e] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hP⟩

/-- **`of_reduce_pin_a(n)` refines `ofReducePinA`** (through `rom_cv`'s stub). -/
@[refines ConRon.Arena.ofReducePinA]
theorem ofReducePinA_refines (hp : p.lookup "of_reduce_pin_a" = some ofReducePinAL) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_pin_a" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ofReducePinA (decI c)) a₀ ∧
      KeepPost vis fe decRCV s₀.mem s'.mem (AM.st (ofReducePinA (decI c)) a₀) r
        (AM.res (ofReducePinA (decI c)) a₀); ⊤⦄ := by
  refine triple_post (ofReducePinA_specW p hpa hp n s₀ c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hP⟩ := selW_ok (T := romCvT)
    (fun w hw => hR.cv vis fe w (by rcases hw with rfl | rfl <;> decide)) decRCV_head hm hS hc (by decide)
  have e : ofReducePinA (decI c) =
      (do let y ← pinAt (45 : Word).toNat
          if (decI c : NIdx) == y then romCvT (8 : Word).toNat else romCvT (9 : Word).toNat) := rfl
  rw [← e] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hP⟩

/-- **`reduce_decl_pin(c)` refines `reduceDeclPin`** (through `rom_expr_pin`'s stub). -/
@[refines ConRon.Arena.reduceDeclPin]
theorem reduceDeclPin_refines (hp : p.lookup "reduce_decl_pin" = some reduceDeclPinL) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_decl_pin" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (reduceDeclPin (decI c)) a₀ ∧
      KeepPost vis fe decW0E s₀.mem s'.mem (AM.st (reduceDeclPin (decI c)) a₀) r
        (AM.res (reduceDeclPin (decI c)) a₀); ⊤⦄ := by
  refine triple_post (reduceDeclPin_specW p hpa hp n s₀ c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hP⟩ := selW_ok (T := romExprT)
    (fun w hw => hR.expr vis fe w (by rcases hw with rfl | rfl <;> decide)) decW0E_head hm hS
    hc (by decide)
  have e : reduceDeclPin (decI c) =
      (do let y ← pinAt (43 : Word).toNat
          if (decI c : NIdx) == y then romExprT (0 : Word).toNat else romExprT (1 : Word).toNat) :=
    rfl
  rw [← e] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hP⟩

end refines

/-! ## `const_e(n)` under the stage relation -/

/-- **`const_e(n)` refines `constE`** at the run level, under the stage relation. -/
theorem constE_stage {p : Prog} (hp : p.lookup "const_e" = some constEL)
    (hpw : p.lookup "pin_word" = some pinWordL) (hcf : p.lookup "const_find" = some constFind)
    (hcp : p.lookup "const_push" = some constPush) (hic : p.lookup "intern_const" = some internConst)
    {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {nm : Word} {r : List Word}
    (h : callW p n "const_e" [nm] m = some (r, m')) (hS : StageR vis fe m a)
    (hnm : nm.toNat < 2 ^ 32) :
    ∃ a', (constE (decI nm)).run a = .ok (decE (r.headD 0), a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' := by
  cases n with
  | zero => simp [callW_zero] at h
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (constE_spec p hp (n + 1) ⟨m, Locals.init []⟩ nm) h
  subst hs'
  simp only [constEW] at hW
  rcases h1 : callW p n "pin_word" [52] m with _ | ⟨r1, m1⟩ <;> rw [h1] at hW
  · cases hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinWord_specW p hpw n ⟨m, Locals.init []⟩ 52) h1
  subst hs1
  have hflag : pinW m 0 ≠ 0 := by intro h0; simp [pinWordW, h0] at hW1
  simp only [pinWordW, hflag, ite_false, Option.some.injEq, Prod.mk.injEq] at hW1
  obtain ⟨rfl, hm1⟩ := hW1
  have hF := hS.check.pins.full hflag
  have hz : rdW (m.arr64 PINS) 52 = pinW m 52 := by simp [rdW, pinW]
  simp only [List.headD_cons, hz, constEW.k_pin_word] at hW
  rcases h2 : callW p n "intern_const" [nm, pinW m 52] s1.mem with _ | ⟨r2, m2⟩ <;> simp only [h2, constEW.k_intern_const] at hW
  · cases hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (internConst_spec p hcf hcp hic n ⟨s1.mem, Locals.init []⟩ nm (pinW m 52)) h2
  rw [hs2, ← hm1] at hW2
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS nm (pinW m 52) hnm hF.lv_lt.1 hW2
  refine ⟨a2, ?_, hS2, hg2⟩
  rw [constE_run hF, ← hr]
  exact hrun2

/-! ## `reduce_cert_var(c)` -/

section rcv
variable (p : Prog)

/-- The lookups of `reduce_cert_var`. -/
structure RcvProg (p : Prog) : Prop where
  rcv : p.lookup "reduce_cert_var" = some reduceCertVarL
  pa : p.lookup "pin_at" = some pinAtL
  ce : p.lookup "const_e" = some constEL
  pw : p.lookup "pin_word" = some pinWordL
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  ff : p.lookup "fvar_find" = some fvarFind
  fp : p.lookup "fvar_push" = some fvarPush
  fi : p.lookup "intern_fvar" = some internFVar

/-- **The model of `reduce_cert_var(c)`.** -/
l_model rcv_specW (p : Prog) (h : RcvProg p)
  fns [h.rcv ↦ rcvW list]
  specs [pinAt_specW p h.pa n, callW_spec p n "const_e", internFVar_spec p h.ff h.fp h.fi n]
  grind [arena_grind, ind_grind]

end rcv

theorem reduceCertVar_eq (c : NIdx) :
    reduceCertVar c = (do
      let rn ← pinAt 43
      let nm ← (if c == rn then pinAt 1 else pinAt 29)
      let t ← constE nm
      internE (.fvar 0 t)) := by
  simp only [reduceCertVar, reduceElemTy, reduceElemName, reduceNatName, pinReduceNat, pinNat,
    boolName, pinBool, PIN_REDUCE_NAT, PIN_NAT, PIN_BOOL, bind_assoc]

/-- **`reduce_cert_var(c)` refines `reduceCertVar`** (pin reads, `const_e`, `intern_fvar`;
proved). -/
@[refines ConRon.Arena.reduceCertVar]
theorem reduceCertVar_refines (p : Prog) (hp : RcvProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis c : Word)
    (hS : StageR vis fe s₀.mem a₀) (hc : c.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reduce_cert_var" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (reduceCertVar (decI c)) a₀ ∧
      StageR vis fe s'.mem (AM.st (reduceCertVar (decI c)) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      AM.res (reduceCertVar (decI c)) a₀ = decE (r.headD 0); ⊤⦄ := by
  refine triple_post (rcv_specW p hp n s₀ c) ?_
  rintro r s' ⟨hl, h⟩
  cases n with
  | zero => rw [rcvW.eq_1] at h; cases h
  | succ n =>
  rw [rcvW.arm1] at h
  rcases h1 : pinAtW s₀.mem 43 with _ | ⟨r1, m1⟩ <;> rw [h1] at h
  · rw [rcvW.k_pin_at.none] at h; cases h
  rw [rcvW.k_pin_at.eq_2, ← apply_ite (rcvW.k_pin_at_2 p n)] at h
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.check.pins
  subst hm1
  generalize s₀.mem = m1 at *
  have e1 : r1.headD 0 = pinW m1 (1 + (43 : Word).toNat) := by rw [hr1]; rfl
  have hbeq : ((decI c : NIdx) == decI (pinW m1 (1 + (43 : Word).toNat))) =
      decide (c = pinW m1 (1 + (43 : Word).toNat)) := decI_beq c _ hc hl1
  -- the element's name: one of two pins
  generalize hpick : (if c = r1.headD 0 then pinAtW m1 1 else pinAtW m1 29) = pk at h
  cases pk with
  | none => rw [rcvW.k_pin_at_2.none] at h; cases h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [rcvW.k_pin_at_2.arm1, rcvW.j1.arm1] at h
  have hname : m2 = m1 ∧ (r2.headD 0).toNat < 2 ^ 32 ∧
      ((if (decI c : NIdx) == decI (pinW m1 (1 + (43 : Word).toNat)) then pinAt 1 else pinAt 29) :
        AM NIdx).run a₀ = .ok (decI (r2.headD 0), a₀) := by
    by_cases he : c = r1.headD 0
    · rw [ite_eq_left he] at hpick
      obtain ⟨hm, hr, hl, hrun⟩ := pinAtW_ok hpick hS.check.pins
      rw [e1] at he
      subst hr
      refine ⟨hm, hl, ?_⟩
      simp only [he, List.headD_cons]
      simpa using hrun
    · rw [ite_eq_right he] at hpick
      obtain ⟨hm, hr, hl, hrun⟩ := pinAtW_ok hpick hS.check.pins
      rw [e1] at he
      subst hr
      refine ⟨hm, hl, ?_⟩
      simp only [hbeq, he, decide_false, Bool.false_eq_true, ite_false, List.headD_cons]
      simpa using hrun
  obtain ⟨rfl, hnl, hrun2⟩ := hname
  -- `const_e`
  rcases h3 : callW p n "const_e" [r2.headD 0] m2 with _ | ⟨r3, m3⟩ <;> rw [h3] at h
  · rw [rcvW.k_const_e.none] at h; cases h
  obtain ⟨a3, hrun3, hS3, hg3⟩ := constE_stage hp.ce hp.pw hp.cf hp.cp hp.ic h3 hS hnl
  by_cases hb : 4294967296 ≤ r3.headD 0
  · rw [rcvW.k_const_e.abort1 p r3 m3 hb] at h; cases h
  rw [rcvW.k_const_e.arm1 p r3 m3 hb] at h
  have ht : (r3.headD 0).toNat < 2 ^ 32 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hb); simpa using this
  -- `intern_fvar`
  rcases h4 : fvinternW m3 0 (r3.headD 0) with _ | ⟨r4, m4⟩ <;> rw [h4] at h
  · rw [rcvW.k_intern_fvar.none] at h; cases h
  rw [rcvW.k_intern_fvar.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a4, hrun4, hS4, hg4⟩ := internFVar_stage hS3 0 (r3.headD 0) ht h4
  have hrun : (reduceCertVar (decI c)).run a₀ = .ok (decE r4, a4) := by
    rw [reduceCertVar_eq]
    rw [show (43 : Nat) = (43 : Word).toNat from rfl, StateT.run_bind, hrun1, L.Arena.except_ok_bind,
      StateT.run_bind, hrun2, L.Arena.except_ok_bind, StateT.run_bind, hrun3, L.Arena.except_ok_bind]
    exact hrun4
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS4, hg3.trans hg4, by rw [hres]; rfl⟩

/-! ## `reduce_pin_guard(vis, c)` -/

/-- **The model of `reduce_pin_guard(vis, c)`**, `all_level_params_defined` and
`consts_resolve_ffast` read through `cl` (`stubCall` for the `StageR` proof, `realCall p` under
`StageT`). -/
l_model rpg_specW (p : Prog) (hb : BvbProg p) (hf : HfF p)
    (hp : p.lookup "reduce_pin_guard" = some reducePinGuardL) (cl : CallM) (hcl : CallSpec p cl)
  fns [hp ↦ rpgW list]
  specs [callW_spec p n "reduce_decl_pin", lbbF_spec p hb n, hffF_spec p hf n,
    hcl n "all_level_params_defined", hcl n "consts_resolve_ffast"]
  grind [arena_grind, ind_grind]


end L.Arena
