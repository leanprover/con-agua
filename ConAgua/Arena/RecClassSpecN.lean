import ConAgua.Arena.RecClassSpecM

/-!
# `RecClass`: `classGenRule` — models and specs (lane `indproofs2`, helper `rec2`)
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem loc_init13 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: r) 13 =
      x13 := rfl
theorem loc_init14 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Word) (r : List Word) :
    Locals.init (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: r)
      14 = x14 := rfl
theorem loc_init15 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Word) (r : List Word) :
    Locals.init
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: r)
      15 = x15 := rfl

/-! ## Lookups, `find_slot`, `pvars_go` -/

/-- The lookups `class_gen_rule` needs. -/
structure RuProg (p : Prog) extends PbProg p : Prop where
  lf : p.lookup "lam_find" = some lamFind
  lp : p.lookup "lam_push" = some lamPush
  il : p.lookup "intern_lam" = some internLamL
  mkl : p.lookup "mk_lam" = some mkLam
  cl : p.lookup "close_lams" = some closeLams
  cro : p.lookup "class_rec_of" = some classRecOf
  fsg : p.lookup "class_gen_rule_find_slot_go" = some classGenRuleFindSlotGo
  fs : p.lookup "class_gen_rule_find_slot" = some classGenRuleFindSlot
  pv : p.lookup "class_gen_rule_pvars_go" = some classGenRulePvarsGo
  c1c : p.lookup "class_gen_rule_call1_close" = some classGenRuleCall1Close
  c1t : p.lookup "class_gen_rule_call1_tail" = some classGenRuleCall1Tail
  c1 : p.lookup "class_gen_rule_call1" = some classGenRuleCall1
  cg : p.lookup "class_gen_rule_calls_go" = some classGenRuleCallsGo
  rc : p.lookup "class_gen_rule_close" = some classGenRuleClose
  rb : p.lookup "class_gen_rule_body" = some classGenRuleBody
  ru : p.lookup "class_gen_rule" = some classGenRule

l_model findSlotGo_spec (p : Prog) (h : RuProg p)
  fns [h.fsg ↦ fsgW list]
  grind [arena_grind] simp [rdW_eq]

l_model findSlot_spec (p : Prog) (h : RuProg p)
  fns [h.fs ↦ gfsW list]
  specs [findSlotGo_spec p h n]
  grind [arena_grind] simp [rdW_eq]

l_model pvarsGo_spec (p : Prog) (h : RuProg p)
  fns [h.pv ↦ pvW list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n,
    slotVar_spec p h.pw h.sf h.sp h.isort h.fvf h.fvp h.ifv h.sv n, slCons_specW p h.alloc h.copy h.cons n]
  grind [arena_grind] finish [rdW_eq] gen 20

/-- The step of `pvW` with the two reads of `v` as one call argument. -/
theorem pvW_step' {n : Nat} {m : Mem} {g rP i : Word} (h : ¬ rP ≤ i) : pvW (n + 1) m g rP i =
    pvW.k_expr_get_d n g rP i
      (if i < rdW (m.arr64 IW) (g + 0) then
        fuelW n (exprGetDW m (rdW (m.arr64 IW) (g + 1)) (rdW (m.arr64 IW) (g + 2)) i)
      else slotVarW m g (i - rdW (m.arr64 IW) (g + 0))) := by
  by_cases hc : i < rdW (m.arr64 IW) (g + 0)
  · rw [pvW.arm2 (hc1 := h) (hc2 := hc), ite_eq_left hc]
  · rw [pvW.arm3 (hc1 := h) (hc2 := hc), ite_eq_right hc]

/-! ## One call -/

l_model call1Close_spec (p : Prog) (h : RuProg p)
  fns [h.c1c ↦ c1cW list]
  specs [ftdsF_spec p h.ad n, closeLams_spec p h.db h.lf h.lp h.il h.mkl h.cl h.ab n]
  grind [arena_grind] simp []

l_model call1Tail_spec (p : Prog) (h : RuProg p)
  fns [h.c1t ↦ c1tW list]
  specs [rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, mknF_spec p h.ad n,
    internConst_spec p h.cf h.cp h.ic n, slAppend_specW p h.alloc h.copy h.app n,
    slSnoc_specW p h.alloc h.copy h.snoc n, call1Close_spec p h n]
  grind [arena_grind] simp []

def c1K3 (n : Nat) (fvso fvsl pvo pvl rlvls xso xsl idxo idxl i e : Word) (m2 : Mem) :
    Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r3 =>
    if r3.headD 0 = 0 then some ([0, 0], m2)
    else fcK (c1tW n m2 fvso fvsl pvo pvl rlvls xso xsl idxo idxl (r3.tail.headD 0) i e)

def c1K2 (n : Nat) (t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else c1K3 n fvso fvsl pvo pvl rlvls (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0)
      (r2.tail.tail.tail.tail.headD 0) i e m2 (classRecOfW n m2 rco rcl cgo cgl t)

def c1K1 (n : Nat) (g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (rec2IhF n m1 g t tele (r1.headD 0) e)

/-- **The model of `class_gen_rule_call1`.** -/
def c1W : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, t, tele, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, i, e =>
    c1K1 n g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (fuelW n (exprGetDW m wso wsl i))

section arms1
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (next : Mem → Option (List Word × Mem))
  (g x so sl j c cn rP i v e app fvso fvsl pvo pvl rlvls xso xsl idxo idxl r t tele wso wsl rco rcl cgo cgl
    nn s fo fl ihso ihsl body sv rc fx : Word) (r1 r2 r3 r4 r5 r6 : List Word)
theorem c1W_eq : c1W (n + 1) m g t tele wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e =
    c1K1 n g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (fuelW n (exprGetDW m wso wsl i)) := rfl
theorem c1K1_some : c1K1 n g t tele fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (some (r1, m1)) =
    c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (rec2IhF n m1 g t tele (r1.headD 0) e) := rfl
theorem c1K2_fail (h : r2.headD 0 = 0) : c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (some (r2, m2)) =
    some ([0, 0], m2) := by rw [c1K2, ite_eq_left h]
theorem c1K2_ok (h : r2.headD 0 ≠ 0) : c1K2 n t fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e (some (r2, m2)) =
    c1K3 n fvso fvsl pvo pvl rlvls (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0)
      (r2.tail.tail.tail.tail.headD 0) i e m2 (classRecOfW n m2 rco rcl cgo cgl t) := by rw [c1K2, ite_eq_right h]
theorem c1K3_fail (h : r3.headD 0 = 0) : c1K3 n fvso fvsl pvo pvl rlvls xso xsl idxo idxl i e m2 (some r3) =
    some ([0, 0], m2) := by rw [c1K3, ite_eq_left h]
theorem c1K3_ok (h : r3.headD 0 ≠ 0) : c1K3 n fvso fvsl pvo pvl rlvls xso xsl idxo idxl i e m2 (some r3) =
    fcK (c1tW n m2 fvso fvsl pvo pvl rlvls xso xsl idxo idxl (r3.tail.headD 0) i e) := by rw [c1K3, ite_eq_right h]
end arms1

attribute [ind_grind] c1W_eq c1K1_some c1K2_fail c1K2_ok c1K3_fail c1K3_ok

section specs
variable (p : Prog) (h : RuProg p)
include h

theorem call1_spec (n : Nat) (s₀ : St) (g t tele wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_call1"
      [g, t, tele, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, i, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      c1W n s₀.mem g t tele wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl i e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.c1]
  simp only [callFn, classGenRuleCall1]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
    rec2ExprGetD_specF p h.bf h.bp h.ib h.egd n, rec2IhParts_specF p h.ihp h.ad h.opf n,
    classRecOf_spec p h.cro n, call1Tail_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10, loc_init11, loc_init12, loc_init13, loc_init14, loc_init15]

end specs

/-! ## The calls -/

mutual
/-- **The model of `class_gen_rule_calls_go`.** -/
def cgW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, x, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, e, nn, i =>
    if nn = 0 then some ([1, 0, 0], m)
    else if isTag m x i = 1 then
      cgK1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i
        (c1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
          pvo pvl rlvls rco rcl cgo cgl i e)
    else isK3 (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1))
def cgK1 (n : Nat) (g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0, 0], m1)
    else isK2 n (r1.tail.headD 0)
      (cgW n m1 g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1))
end

/-! ## Arms -/

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (next : Mem → Option (List Word × Mem))
  (g x so sl j c cn rP i v e app fvso fvsl pvo pvl rlvls xso xsl idxo idxl r t tele wso wsl rco rcl cgo cgl
    nn s fo fl ihso ihsl body sv rc fx : Word) (r1 r2 r3 r4 r5 r6 : List Word)
theorem cgW_end (h : nn = 0) : cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
    some ([1, 0, 0], m) := by simp only [cgW]; rw [ite_eq_left h]
theorem cgW_rec (h : ¬ nn = 0) (ht : isTag m x i = 1) :
    cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
      cgK1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i
        (c1W n m g (rdW (m.arr64 IW) (isKp m x i + 1)) (rdW (m.arr64 IW) (isKp m x i + 2)) wso wsl fvso fvsl
          pvo pvl rlvls rco rcl cgo cgl i e) := by
  simp only [cgW]; rw [ite_eq_right h, ite_eq_left ht]
theorem cgW_ord (h : ¬ nn = 0) (ht : ¬ isTag m x i = 1) :
    cgW (n + 1) m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i =
      isK3 (cgW n m g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1)) := by
  simp only [cgW]; rw [ite_eq_right h, ite_eq_right ht]
theorem cgK1_fail (h : r1.headD 0 = 0) :
    cgK1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i (some (r1, m1)) = some ([0, 0, 0], m1) := by
  rw [cgK1, ite_eq_left h]
theorem cgK1_ok (h : r1.headD 0 ≠ 0) :
    cgK1 n g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i (some (r1, m1)) =
      isK2 n (r1.tail.headD 0) (cgW n m1 g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e (nn - 1) (i + 1)) := by
  rw [cgK1, ite_eq_right h]
end arms

attribute [ind_grind] cgW_end cgW_rec cgW_ord cgK1_fail cgK1_ok

section specs
variable (p : Prog) (h : RuProg p)
include h

set_option maxHeartbeats 2000000 in
theorem callsGo_spec (n : Nat) : ∀ (s₀ : St) (g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule_calls_go"
      [g, x, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, e, nn, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      cgW n s₀.mem g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intros
    rw [invoke_eq _ h.cg]; simp only [callFn, classGenRuleCallsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ g x wso wsl fvso fvsl pvo pvl rlvls rco rcl cgo cgl e nn i
    rw [invoke_eq _ h.cg]
    simp only [callFn, classGenRuleCallsGo]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      call1_spec p h n, slCons_specW p h.alloc h.copy h.cons n, ih]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
      BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq,
      decide_eq_true_eq] at *)
    all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, rdW_eq, isTag, isKp, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9, loc_init10, loc_init11, loc_init12, loc_init13, loc_init14, loc_init15]

end specs

/-! ## The closing, the body, the rule -/

l_model ruleClose_spec (p : Prog) (h : RuProg p)
  fns [h.rc ↦ grcW list]
  specs [slotVar_spec p h.pw h.sf h.sp h.isort h.fvf h.fvp h.ifv h.sv n,
    slAppend_specW p h.alloc h.copy h.app n, mknF_spec p h.ad n, ftdsF_spec p h.ad n,
    closeLams_spec p h.db h.lf h.lp h.il h.mkl h.cl h.ab n]
  grind [arena_grind] simp [rdW_eq]

l_model ruleBody_spec (p : Prog) (h : RuProg p)
  fns [h.rb ↦ rbW list]
  specs [targetPiDomsWith_spec p h.ev h.copy h.alloc h.cons h.tpd h.hi1 n, pvarsGo_spec p h n,
    callsGo_spec p h n, ruleClose_spec p h n]
  grind [arena_grind] simp [rdW_eq]

def ruK2 (n : Nat) (g rco rcl cgo cgl rlvls x rP s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else fcK (rbW n m2 g rco rcl cgo cgl rlvls x rP s (r2.tail.headD 0) (r2.tail.tail.headD 0))

def ruK1 (n : Nat) (g rco rcl cgo cgl rlvls x rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else ruK2 n g rco rcl cgo cgl rlvls x rP (r1.tail.headD 0)
      (opfF m1 [rdW (m1.arr64 IW) (x + 1), rdW (m1.arr64 IW) (x + 4), rP])

/-- **The model of `class_gen_rule`.** -/
def ruW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, rco, rcl, cgo, cgl, rlvls, c, x =>
    ruK1 n g rco rcl cgo cgl rlvls x (rdW (m.arr64 IW) (g + 13))
      (gfsW n m g c (rdW (m.arr64 EREC) (rdW (m.arr64 IW) x)))

section arms2
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (next : Mem → Option (List Word × Mem))
  (g x so sl j c cn rP i v e app fvso fvsl pvo pvl rlvls xso xsl idxo idxl r t tele wso wsl rco rcl cgo cgl
    nn s fo fl ihso ihsl body sv rc fx : Word) (r1 r2 r3 r4 r5 r6 : List Word)
theorem ruW_eq : ruW (n + 1) m g rco rcl cgo cgl rlvls c x = ruK1 n g rco rcl cgo cgl rlvls x
    (rdW (m.arr64 IW) (g + 13)) (gfsW n m g c (rdW (m.arr64 EREC) (rdW (m.arr64 IW) x))) := rfl
theorem ruK1_fail (h : r1.headD 0 = 0) : ruK1 n g rco rcl cgo cgl rlvls x rP (some (r1, m1)) = some ([0, 0], m1) := by
  rw [ruK1, ite_eq_left h]
theorem ruK1_ok (h : r1.headD 0 ≠ 0) : ruK1 n g rco rcl cgo cgl rlvls x rP (some (r1, m1)) =
    ruK2 n g rco rcl cgo cgl rlvls x rP (r1.tail.headD 0)
      (opfF m1 [rdW (m1.arr64 IW) (x + 1), rdW (m1.arr64 IW) (x + 4), rP]) := by
  rw [ruK1, ite_eq_right h]
theorem ruK2_fail (h : r2.headD 0 = 0) : ruK2 n g rco rcl cgo cgl rlvls x rP s (some (r2, m2)) = some ([0, 0], m2) := by
  rw [ruK2, ite_eq_left h]
theorem ruK2_ok (h : r2.headD 0 ≠ 0) : ruK2 n g rco rcl cgo cgl rlvls x rP s (some (r2, m2)) =
    fcK (rbW n m2 g rco rcl cgo cgl rlvls x rP s (r2.tail.headD 0) (r2.tail.tail.headD 0)) := by
  rw [ruK2, ite_eq_right h]
end arms2

attribute [ind_grind] ruW_eq ruK1_fail ruK1_ok ruK2_fail ruK2_ok

section specs
variable (p : Prog) (h : RuProg p)
include h

theorem classGenRule_spec (n : Nat) (s₀ : St) (g rco rcl cgo cgl rlvls c x : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_gen_rule" [g, rco, rcl, cgo, cgl, rlvls, c, x]
    ⦃fun r s' => LocEq s' s₀ ∧ ruW n s₀.mem g rco rcl cgo cgl rlvls c x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ru]
  simp only [callFn, classGenRule]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    findSlot_spec p h n, opfF_spec p h.opf n, ruleBody_spec p h n]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init, List.getD_cons_zero, List.getD_cons_succ, Cmp.eval,
    BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq] at *)
  all_goals grind (gen := 20) (instances := 5000) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

end specs

end L.Ind
