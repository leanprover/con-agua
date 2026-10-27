import ConAgua.Arena.LdRd
import ConAgua.Arena.RecCheckSpec.TkhK2
import ConAgua.Arena.RecCheckSpec.TruncSl
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# Tka

`eeK0_some`, `eeK1_some`, `eeK2_some`, `eftF_spec`, `noF_spec`, `ee_spec` and the lemmas only they use.
-/

section

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

section arms
variable (n : Nat) (m : Mem) (o l v : Word) (rv rr rc : List Word)
theorem eeK0_some : eeK0 n o l (some (rv, m)) = eeK1 n (rv.headD 0) (eeW n m (o + 1) (l - 1)) := by
  simp [eeK0]
theorem eeK1_some : eeK1 n v (some (rr, m)) = eeK2 (consW n m v (rr.headD 0) (rr.tail.headD 0)) := rfl
theorem eeK2_some : eeK2 (some (rc, m)) = some ([rc.headD 0, rc.tail.headD 0], m) := rfl
end arms
attribute [ind_grind] eeK0_some eeK1_some eeK2_some

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
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
      reduceIte, beq_iff_eq] at *)
    all_goals grind (gen := 10) [lang_grind, arena_grind, ind_grind, rdW_eq]

section arms
variable (n : Nat) (m : Mem) (bso bsl teo tel e : Word) (r1 r2 : List Word)
theorem tteK1_some : tteK1 n teo tel (some (r1, m)) = tteK2 n r1 (eeW n m teo tel) := rfl
theorem tteK2_some : tteK2 n r1 (some (r2, m)) =
    tteK3 m (eqW n m (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)) := rfl
theorem tteK3_some : tteK3 m (some e) = some ([e], m) := rfl
end arms
attribute [ind_grind] tteK1_some tteK2_some tteK3_some

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
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Nat.reduceEqDiff, reduceIte] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

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
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
      reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals grind (gen := 40) (instances := 20000) [lang_grind, arena_grind, ind_grind]

end L.Ind

end
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

def tkhK1 (cR : CallM) (n : Nat) (vis q fto ftl Mc leafW majDom : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rl, m) => tkhK2 cR n vis q fto ftl Mc leafW majDom (rl.headD 0) (gafF m [CWF, majDom])

/-- **The model of `target_k53_heads`** (exec fuel). -/
def tkhW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, fto, ftl, Mc, leafW, majDom =>
    tkhK1 cR n vis q fto ftl Mc leafW majDom (gafF m [CWF, leafW])

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis q fto ftl Mc leafW majDom lh ip usp ii : Word) (r rl rm ra rb : List Word)
theorem tkhW_succ : tkhW cR (n + 1) m vis q fto ftl Mc leafW majDom =
    tkhK1 cR n vis q fto ftl Mc leafW majDom (gafF m [CWF, leafW]) := rfl
theorem tkhK1_some : tkhK1 cR n vis q fto ftl Mc leafW majDom (some (rl, m)) =
    tkhK2 cR n vis q fto ftl Mc leafW majDom (rl.headD 0) (gafF m [CWF, majDom]) := rfl
theorem tkhK2_l (h : lh >>> 28 ≠ 3) : tkhK2 cR n vis q fto ftl Mc leafW majDom lh (some (rm, m)) = some ([0], m) := by
  simp only [tkhK2]; rw [ite_eq_left h]
theorem tkhK2_m (h : ¬ lh >>> 28 ≠ 3) (h2 : rm.headD 0 >>> 28 ≠ 3) :
    tkhK2 cR n vis q fto ftl Mc leafW majDom lh (some (rm, m)) = some ([0], m) := by
  simp only [tkhK2]; rw [ite_eq_right h, ite_eq_left h2]
theorem tkhK2_ok (h : ¬ lh >>> 28 ≠ 3) (h2 : ¬ rm.headD 0 >>> 28 ≠ 3) (h3 : ¬ eViewW m lh = [])
    (h4 : ¬ eViewW m (rm.headD 0) = []) :
    tkhK2 cR n vis q fto ftl Mc leafW majDom lh (some (rm, m)) =
    tkhK3 cR n vis q fto ftl Mc majDom ((eViewW m lh).tail.headD 0) ((eViewW m lh).tail.tail.headD 0)
      ((eViewW m (rm.headD 0)).tail.headD 0) (gaaF m [CWF, leafW]) := by
  simp only [tkhK2]; rw [ite_eq_right h, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
theorem tkhK3_some : tkhK3 cR n vis q fto ftl Mc majDom ip usp ii (some (ra, m)) =
    tkhK4 cR n vis q fto ftl Mc ip usp ii ra (gaaF m [CWF, majDom]) := rfl
theorem tkhK4_i (h : ip ≠ ii) : tkhK4 cR n vis q fto ftl Mc ip usp ii ra (some (rb, m)) = some ([0], m) := by
  simp only [tkhK4]; rw [ite_eq_left h]
theorem tkhK4_l (h : ¬ ip ≠ ii) (h2 : ra.tail.headD 0 ≠ rb.tail.headD 0) :
    tkhK4 cR n vis q fto ftl Mc ip usp ii ra (some (rb, m)) = some ([0], m) := by
  simp only [tkhK4]; rw [ite_eq_right h, ite_eq_left h2]
theorem tkhK4_ok (h : ¬ ip ≠ ii) (h2 : ¬ ra.tail.headD 0 ≠ rb.tail.headD 0) :
    tkhK4 cR n vis q fto ftl Mc ip usp ii ra (some (rb, m)) =
    tkhK5 (tkaW cR n m vis q fto ftl Mc ip usp (ra.headD 0) (ra.tail.headD 0) (rb.headD 0) (rb.tail.headD 0)) := by
  simp only [tkhK4]; rw [ite_eq_right h, ite_eq_right h2]
theorem tkhK5_some : tkhK5 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] tkhW_succ tkhK1_some tkhK2_l tkhK2_m tkhK2_ok tkhK3_some tkhK4_i tkhK4_l tkhK4_ok tkhK5_some

set_option maxHeartbeats 2000000 in
theorem tkh_spec (p : Prog) (L : K53Look p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis q fto ftl Mc leafW majDom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53_heads" [vis, q, fto, ftl, Mc, leafW, majDom]
    ⦃fun r s' => LocEq s' s₀ ∧ tkhW cR n s₀.mem vis q fto ftl Mc leafW majDom = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
    rw [invoke_eq _ L.tkh]
    simp only [callFn, targetK53Heads]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, gafF_spec p L.ad n,
      gaaF_spec p L.ad n, eView_spec p L.hv n, tka_spec p L cR hcR n]
    all_goals subst_vars
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte,
      bne_iff_ne, ne_eq] at *)
    all_goals grind (gen := 40) (instances := 20000) [lang_grind, arena_grind, ind_grind, loc_init4, loc_init5,
      loc_init6]

/-! ## `target_k53` -/

def tkK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def tkK2 (cR : CallM) (n : Nat) (vis q fto ftl Mc majDom leafW : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m) =>
    if rt.headD 0 = 0 then some ([0], m) else tkK3 (tkhW cR n m vis q fto ftl Mc leafW majDom)

def tkK1 (cR : CallM) (n : Nat) (vis q fto ftl Mc teo tel majDom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m) =>
    if rs.headD 0 = 0 then some ([0], m)
    else tkK2 cR n vis q fto ftl Mc majDom (rs.tail.tail.tail.headD 0)
      (tteW n m (rs.tail.headD 0) (rs.tail.tail.headD 0) teo tel)

/-- **The model of `target_k53`** (exec fuel). -/
def tkW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, fto, ftl, Mc, teo, tel, majDom, f =>
    tkK1 cR n vis q fto ftl Mc teo tel majDom (stripF 6 m [tel, f])

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis q fto ftl Mc teo tel majDom f leafW : Word) (r rs rt : List Word)
theorem tkW_succ : tkW cR (n + 1) m vis q fto ftl Mc teo tel majDom f =
    tkK1 cR n vis q fto ftl Mc teo tel majDom (stripF 6 m [tel, f]) := rfl
theorem tkK1_no (h : rs.headD 0 = 0) : tkK1 cR n vis q fto ftl Mc teo tel majDom (some (rs, m)) = some ([0], m) := by
  simp only [tkK1]; rw [ite_eq_left h]
theorem tkK1_ok (h : ¬ rs.headD 0 = 0) : tkK1 cR n vis q fto ftl Mc teo tel majDom (some (rs, m)) =
    tkK2 cR n vis q fto ftl Mc majDom (rs.tail.tail.tail.headD 0)
      (tteW n m (rs.tail.headD 0) (rs.tail.tail.headD 0) teo tel) := by
  simp only [tkK1]; rw [ite_eq_right h]
theorem tkK2_no (h : rt.headD 0 = 0) : tkK2 cR n vis q fto ftl Mc majDom leafW (some (rt, m)) = some ([0], m) := by
  simp only [tkK2]; rw [ite_eq_left h]
theorem tkK2_ok (h : ¬ rt.headD 0 = 0) : tkK2 cR n vis q fto ftl Mc majDom leafW (some (rt, m)) =
    tkK3 (tkhW cR n m vis q fto ftl Mc leafW majDom) := by
  simp only [tkK2]; rw [ite_eq_right h]
theorem tkK3_some : tkK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] tkW_succ tkK1_no tkK1_ok tkK2_no tkK2_ok tkK3_some

theorem tk_spec (p : Prog) (L : K53Look p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis q fto ftl Mc teo tel majDom f : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53" [vis, q, fto, ftl, Mc, teo, tel, majDom, f]
    ⦃fun r s' => LocEq s' s₀ ∧ tkW cR n s₀.mem vis q fto ftl Mc teo tel majDom f = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
    rw [invoke_eq _ L.tk]
    simp only [callFn, targetK53]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, stripPis_specF p L.strip n,
        tte_spec p L n, tkh_spec p L cR hcR n] <;>
      finish (gen := 40) (instances := 20000) [loc_init4, loc_init5, loc_init6, loc_init7, loc_init8]

end L.Ind

end

end
