import ConAgua.Arena.RecCheckSpec13


noncomputable section

/-!
# `RecCheck`: `targetK53`, the L side (lane `indproofs3`, helper `rec`)

K.53′ at one recorded field: `strip_pis` (stub), the telescope check (`target_k53_tele`: both sides
erased by `erase_each`, compared by `sl_eq`), the head check (`target_k53_heads`: `get_app_fn_f`,
`get_app_args_f` stubs, `e_view`), the argument check (`target_k53_args`: erased indices, the
leaf's class `intern_const` + `mk_app_n_f` (stub) + `nest_occ`, then `target_class_match`).
L: `erase_each` is the twin's `mapM` as a self-recursion consing each result (`sl_cons`, D18); a
handle guard after `intern_const` (`mk_app_n_f`'s contract takes a handle).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Callees at any exec fuel -/

def eftF : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, e => eftW n m e

def noF : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lo, hi, e => noConstW n m no nl lo hi e

/-! ## `erase_each` -/

def eeK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m) => some ([rc.headD 0, rc.tail.headD 0], m)

def eeK1 (n : Nat) (v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => eeK2 (consW n m v (rr.headD 0) (rr.tail.headD 0))

mutual
def eeW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if l = 0 then some ([0, 0], m) else eeK0 n o l (eftF n m (rdW (m.arr64 IW) o))
def eeK0 (n : Nat) (o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) => eeK1 n (rv.headD 0) (eeW n m (o + 1) (l - 1))
end

section arms
variable (n : Nat) (m : Mem) (o l v : Word) (rv rr rc : List Word)
theorem eeW_nil (h : l = 0) : eeW (n + 1) m o l = some ([0, 0], m) := by simp [eeW, h]
theorem eeW_cons (h : ¬ l = 0) : eeW (n + 1) m o l = eeK0 n o l (eftF n m (rdW (m.arr64 IW) o)) := by
  simp [eeW, h]
theorem eeK0_some : eeK0 n o l (some (rv, m)) = eeK1 n (rv.headD 0) (eeW n m (o + 1) (l - 1)) := by
  simp [eeK0]
theorem eeK1_some : eeK1 n v (some (rr, m)) = eeK2 (consW n m v (rr.headD 0) (rr.tail.headD 0)) := rfl
theorem eeK2_some : eeK2 (some (rc, m)) = some ([rc.headD 0, rc.tail.headD 0], m) := rfl
end arms
attribute [ind_grind] eeW_nil eeW_cons eeK0_some eeK1_some eeK2_some

/-- The lookups of `target_k53`. -/
structure K53Look (p : Prog) : Prop where
  tmn : TmnLook p
  hv : p.lookup "e_view" = some eView
  ad : AdF p
  sc : p.lookup "sl_contains" = some slContains
  nf : p.lookup "no_find" = some (memoFindG noSch)
  np : p.lookup "no_put" = some (memoPutG noSch)
  ngo : p.lookup "nest_occ_go" = some nestOccGo
  nnode : p.lookup "nest_occ_node" = some nestOccNode
  ncl : p.lookup "no_clear" = some (memoClearG noSch)
  no : p.lookup "nest_occ" = some nestOcc
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  eq : p.lookup "sl_eq" = some slEq
  ee : p.lookup "erase_each" = some eraseEach
  tte : p.lookup "target_k53_tele" = some targetK53Tele
  tkh : p.lookup "target_k53_heads" = some targetK53Heads
  tka : p.lookup "target_k53_args" = some targetK53Args
  tk : p.lookup "target_k53" = some targetK53
  strip : StripProg p

theorem eftF_spec (p : Prog) (L : RcLook p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erase_fvar_tys" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ eftF n s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact eraseFVarTys_spec p L.rx L.eft n s₀ e

theorem noF_spec (p : Prog) (L : K53Look p) (n : Nat) (s₀ : St) (no nl lo hi e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ" [no, nl, lo, hi, e]
    ⦃fun r s' => LocEq s' s₀ ∧ noF n s₀.mem no nl lo hi e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact nestOcc_spec p L.hv L.sc L.nf L.np L.ngo L.nnode L.ncl L.no n s₀ no nl lo hi e

theorem ee_spec (p : Prog) (L : K53Look p) (n : Nat) :
    ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erase_each" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ eeW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l; rw [invoke_eq _ L.ee]; simp only [callFn, eraseEach]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l
    rw [invoke_eq _ L.ee]
    simp only [callFn, eraseEach]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
      eftF_spec p L.tmn.tcm.tp.rc n, slCons_specW p L.tmn.tcm.ha L.tmn.tcm.ic L.tmn.tcm.sc n]
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init_nil,
        Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
        reduceIte, beq_iff_eq] at *)
    all_goals grind (gen := 10) [lang_grind, arena_grind, ind_grind, rdW_eq]

/-! ## `target_k53_tele` -/

def tteK3 (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => some ([e], m)

def tteK2 (n : Nat) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => tteK3 m (eqW n m (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0))

def tteK1 (n : Nat) (teo tel : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => tteK2 n r1 (eeW n m teo tel)

def tteW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, bso, bsl, teo, tel => tteK1 n teo tel (eeW n m bso bsl)

section arms
variable (n : Nat) (m : Mem) (bso bsl teo tel e : Word) (r1 r2 : List Word)
theorem tteW_succ : tteW (n + 1) m bso bsl teo tel = tteK1 n teo tel (eeW n m bso bsl) := rfl
theorem tteK1_some : tteK1 n teo tel (some (r1, m)) = tteK2 n r1 (eeW n m teo tel) := rfl
theorem tteK2_some : tteK2 n r1 (some (r2, m)) =
    tteK3 m (eqW n m (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)) := rfl
theorem tteK3_some : tteK3 m (some e) = some ([e], m) := rfl
end arms
attribute [ind_grind] tteW_succ tteK1_some tteK2_some tteK3_some

theorem tte_spec (p : Prog) (L : K53Look p) (n : Nat) (s₀ : St) (bso bsl teo tel : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53_tele" [bso, bsl, teo, tel]
    ⦃fun r s' => LocEq s' s₀ ∧ tteW n s₀.mem bso bsl teo tel = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
    rw [invoke_eq _ L.tte]
    simp only [callFn, targetK53Tele]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ee_spec p L n, slEq_spec p L.eq n]
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init_nil,
        Locals.init_cons_zero, Locals.init_cons_succ, Nat.reduceEqDiff,
        reduceIte] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

/-! ## `target_k53_args` -/

def tkaK8 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def tkaK7 (cR : CallM) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (occ, m) =>
    if occ = 0 then some ([0], m)
    else tkaK8 (tcmF cR n m vis q fto ftl (rdW (m.arr64 IW) (Mc + 11)) (rdW (m.arr64 IW) (Mc + 12))
      (rdW (m.arr64 IW) (Mc + 1)) (rdW (m.arr64 IW) (Mc + 2)) (rdW (m.arr64 IW) (Mc + 3)) usp lao lpl)

def tkaK6 (cR : CallM) (n : Nat) (vis q fto ftl Mc usp lao lpl app : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rn, m) => tkaK7 cR n vis q fto ftl Mc usp lao lpl (noF n m (rn.headD 0) (rn.tail.headD 0) 0 0 app)

def tkaK5 (cR : CallM) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => tkaK6 cR n vis q fto ftl Mc usp lao lpl (ra.headD 0) (memberNamesW n m q)

def tkaK4 (cR : CallM) (vis q fto ftl Mc usp lao lpl : Word) (n : Nat) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m) =>
    if 4294967296 ≤ hd then none
    else tkaK5 cR n vis q fto ftl Mc usp lao lpl (mknF m [hd, lao, lpl])

def tkaK3 (cR : CallM) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e =>
    if e = 0 then some ([0], m)
    else tkaK4 cR vis q fto ftl Mc usp lao (if lal < K then lal else K) n (ceinternW m ip usp)

def tkaK2 (cR : CallM) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => tkaK3 cR n vis q fto ftl Mc ip usp lao lal K m
      (eqW n m (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0))

def tkaK1 (cR : CallM) (n : Nat) (vis q fto ftl Mc ip usp lao lal mao mal K : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => tkaK2 cR n vis q fto ftl Mc ip usp lao lal K r1
      (eeW n m (if mal < K then mao else mao + K) (if mal < K then 0 else mal - K))

/-- **The model of `target_k53_args`** (exec fuel; `K` the class's parameter count, read once). -/
def tkaW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, fto, ftl, Mc, ip, usp, lao, lal, mao, mal =>
    tkaK1 cR n vis q fto ftl Mc ip usp lao lal mao mal (rdW (m.arr64 IW) (Mc + 4))
      (eeW n m (if lal < rdW (m.arr64 IW) (Mc + 4) then lao else lao + rdW (m.arr64 IW) (Mc + 4))
        (if lal < rdW (m.arr64 IW) (Mc + 4) then 0 else lal - rdW (m.arr64 IW) (Mc + 4)))

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis q fto ftl Mc ip usp lao lal mao mal lpl app hd e occ K : Word)
  (r r1 r2 ra rn : List Word)
theorem tkaW_succ : tkaW cR (n + 1) m vis q fto ftl Mc ip usp lao lal mao mal =
    tkaK1 cR n vis q fto ftl Mc ip usp lao lal mao mal (rdW (m.arr64 IW) (Mc + 4))
      (eeW n m (if lal < rdW (m.arr64 IW) (Mc + 4) then lao else lao + rdW (m.arr64 IW) (Mc + 4))
        (if lal < rdW (m.arr64 IW) (Mc + 4) then 0 else lal - rdW (m.arr64 IW) (Mc + 4))) := rfl
theorem tkaK1_some : tkaK1 cR n vis q fto ftl Mc ip usp lao lal mao mal K (some (r1, m)) =
    tkaK2 cR n vis q fto ftl Mc ip usp lao lal K r1
      (eeW n m (if mal < K then mao else mao + K) (if mal < K then 0 else mal - K)) := rfl
theorem tkaK2_some : tkaK2 cR n vis q fto ftl Mc ip usp lao lal K r1 (some (r2, m)) =
    tkaK3 cR n vis q fto ftl Mc ip usp lao lal K m
      (eqW n m (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)) := rfl
theorem tkaK3_no (h : e = 0) : tkaK3 cR n vis q fto ftl Mc ip usp lao lal K m (some e) = some ([0], m) := by
  simp only [tkaK3]; rw [ite_eq_left h]
theorem tkaK3_yes (h : ¬ e = 0) : tkaK3 cR n vis q fto ftl Mc ip usp lao lal K m (some e) =
    tkaK4 cR vis q fto ftl Mc usp lao (if lal < K then lal else K) n (ceinternW m ip usp) := by
  simp only [tkaK3]; rw [ite_eq_right h]
theorem tkaK4_big (h : 4294967296 ≤ hd) : tkaK4 cR vis q fto ftl Mc usp lao lpl n (some (hd, m)) = none := by
  simp only [tkaK4]; rw [ite_eq_left h]
theorem tkaK4_ok (h : ¬ 4294967296 ≤ hd) : tkaK4 cR vis q fto ftl Mc usp lao lpl n (some (hd, m)) =
    tkaK5 cR n vis q fto ftl Mc usp lao lpl (mknF m [hd, lao, lpl]) := by
  simp only [tkaK4]; rw [ite_eq_right h]
theorem tkaK5_some : tkaK5 cR n vis q fto ftl Mc usp lao lpl (some (ra, m)) =
    tkaK6 cR n vis q fto ftl Mc usp lao lpl (ra.headD 0) (memberNamesW n m q) := rfl
theorem tkaK6_some : tkaK6 cR n vis q fto ftl Mc usp lao lpl app (some (rn, m)) =
    tkaK7 cR n vis q fto ftl Mc usp lao lpl (noF n m (rn.headD 0) (rn.tail.headD 0) 0 0 app) := rfl
theorem tkaK7_no (h : occ = 0) : tkaK7 cR n vis q fto ftl Mc usp lao lpl (some (occ, m)) = some ([0], m) := by
  simp only [tkaK7]; rw [ite_eq_left h]
theorem tkaK7_yes (h : ¬ occ = 0) : tkaK7 cR n vis q fto ftl Mc usp lao lpl (some (occ, m)) =
    tkaK8 (tcmF cR n m vis q fto ftl (rdW (m.arr64 IW) (Mc + 11)) (rdW (m.arr64 IW) (Mc + 12))
      (rdW (m.arr64 IW) (Mc + 1)) (rdW (m.arr64 IW) (Mc + 2)) (rdW (m.arr64 IW) (Mc + 3)) usp lao lpl) := by
  simp only [tkaK7]; rw [ite_eq_right h]
theorem tkaK8_some : tkaK8 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] tkaW_succ tkaK1_some tkaK2_some tkaK3_no tkaK3_yes tkaK4_big tkaK4_ok tkaK5_some
  tkaK6_some tkaK7_no tkaK7_yes tkaK8_some

set_option maxHeartbeats 8000000 in
theorem tka_spec (p : Prog) (L : K53Look p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis q fto ftl Mc ip usp lao lal mao mal : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53_args" [vis, q, fto, ftl, Mc, ip, usp, lao, lal, mao, mal]
    ⦃fun r s' => LocEq s' s₀ ∧ tkaW cR n s₀.mem vis q fto ftl Mc ip usp lao lal mao mal = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
    rw [invoke_eq _ L.tka]
    simp only [callFn, targetK53Args]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, ee_spec p L n, slEq_spec p L.eq n,
      internConst_spec p L.cf L.cp L.ic n, mknF_spec p L.ad n,
      blockShapeMemberNames_spec p L.tmn.tcm.ha L.tmn.tcm.mnc L.tmn.tcm.mn n, noF_spec p L n,
      tcmF_spec p L.tmn.tcm cR hcR n]
    all_goals (try clear hcR)
    -- `LocEq` unfolded, the callee posts' `s'.loc = …` serve `simp` as rewrites (`*`): the
    -- locals are resolved before `grind`, not by its E-matching through the chain (78 s -> ~5 s).
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init_nil,
        Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
        reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals grind (gen := 40) (instances := 20000) [lang_grind, arena_grind, ind_grind]

end L.Ind
