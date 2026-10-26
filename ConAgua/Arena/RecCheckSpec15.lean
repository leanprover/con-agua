import ConAgua.Arena.RecCheckSpec14

/-!
# `RecCheck`: `targetK53`, the L side continued (lane `indproofs3`, helper `rec`)

`target_k53_heads` and `target_k53` (models and specs); `RecCheckSpec14` has `erase_each`,
`target_k53_tele`, `target_k53_args`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_k53_heads` -/

def tkhK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def tkhK4 (cR : CallM) (n : Nat) (vis q fto ftl Mc ip usp ii : Word) (ra : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m) =>
    if ip ≠ ii then some ([0], m)
    else if ra.tail.headD 0 ≠ rb.tail.headD 0 then some ([0], m)
    else tkhK5 (tkaW cR n m vis q fto ftl Mc ip usp (ra.headD 0) (ra.tail.headD 0) (rb.headD 0) (rb.tail.headD 0))

def tkhK3 (cR : CallM) (n : Nat) (vis q fto ftl Mc majDom ip usp ii : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m) => tkhK4 cR n vis q fto ftl Mc ip usp ii ra (gaaF m [CWF, majDom])

def tkhK2 (cR : CallM) (n : Nat) (vis q fto ftl Mc leafW majDom lh : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rm, m) =>
    if lh >>> 28 ≠ 3 then some ([0], m)
    else if rm.headD 0 >>> 28 ≠ 3 then some ([0], m)
    else if eViewW m lh = [] then none
    else if eViewW m (rm.headD 0) = [] then none
    else tkhK3 cR n vis q fto ftl Mc majDom ((eViewW m lh).tail.headD 0) ((eViewW m lh).tail.tail.headD 0)
      ((eViewW m (rm.headD 0)).tail.headD 0) (gaaF m [CWF, leafW])

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
theorem tkhK2_v1 (h : ¬ lh >>> 28 ≠ 3) (h2 : ¬ rm.headD 0 >>> 28 ≠ 3) (h3 : eViewW m lh = []) :
    tkhK2 cR n vis q fto ftl Mc leafW majDom lh (some (rm, m)) = none := by
  simp only [tkhK2]; rw [ite_eq_right h, ite_eq_right h2, ite_eq_left h3]
theorem tkhK2_v2 (h : ¬ lh >>> 28 ≠ 3) (h2 : ¬ rm.headD 0 >>> 28 ≠ 3) (h3 : ¬ eViewW m lh = [])
    (h4 : eViewW m (rm.headD 0) = []) :
    tkhK2 cR n vis q fto ftl Mc leafW majDom lh (some (rm, m)) = none := by
  simp only [tkhK2]; rw [ite_eq_right h, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
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
attribute [ind_grind] tkhW_succ tkhK1_some tkhK2_l tkhK2_m tkhK2_v1 tkhK2_v2 tkhK2_ok tkhK3_some tkhK4_i tkhK4_l tkhK4_ok tkhK5_some

set_option maxHeartbeats 2000000 in
theorem tkh_spec (p : Prog) (L : K53Look p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis q fto ftl Mc leafW majDom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53_heads" [vis, q, fto, ftl, Mc, leafW, majDom]
    ⦃fun r s' => LocEq s' s₀ ∧ tkhW cR n s₀.mem vis q fto ftl Mc leafW majDom = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
    rw [invoke_eq _ L.tkh]
    simp only [callFn, targetK53Heads]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, gafF_spec p L.ad n,
        gaaF_spec p L.ad n, eView_spec p L.hv n, tka_spec p L cR hcR n] <;>
      finish (gen := 40) (instances := 20000) [loc_init4, loc_init5, loc_init6]

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
