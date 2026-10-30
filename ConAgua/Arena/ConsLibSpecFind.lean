module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
public import ConAgua.Arena.SlotGrowSpec
public import ConAgua.L.PureEval
public import ConAgua.Arena.ConsLibSpecBase
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The cons-table library specs: `X_find` (lane conslib)

`consFindG_spec`: `X_find(t, k, h)` returns `cprobeW` (the probe model, generic in the match).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `X_find`: the probe -/

/-- The find's probe from its state `s` (the loop's variables). -/
abbrev fprobe (C : ConsSch) (s : St) : List Word :=
  cprobeW (s.mem.arr64 (tierA C.sa (s.loc 0))) (C.mtM s.mem (fkeys C s) (s.loc 0)) C.exact
    (s.loc (7 + C.nk + C.mloc)) (s.loc (6 + C.nk)) (s.loc (2 + C.nk)) (s.loc (8 + C.nk + C.mloc))
    (s.loc (3 + C.nk)) (s.loc (4 + C.nk))

theorem argsOf_setLoc_addc (base nk a c : Nat) (ha : base + 1 ≤ a) (s : St) (v : Word) :
    argsOf base (nk + 1) (s.setLoc (a + nk + c) v) = argsOf base (nk + 1) s :=
  argsOf_setLoc base (nk + 1) _ (by omega) s v

theorem argsOf_setLoc_addc0 (base nk a c : Nat) (ha : base ≤ a) (s : St) (v : Word) :
    argsOf base nk (s.setLoc (a + nk + c) v) = argsOf base nk s :=
  argsOf_setLoc base nk _ (by omega) s v

theorem addc_eq_add (a b nk c : Nat) (h : b < a) : (a + nk + c = b + nk) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem add_eq_addc (a b nk c : Nat) (h : b < a) : (b + nk = a + nk + c) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem addc_eq_addc (a b nk c : Nat) (h : a ≠ b) : (a + nk + c = b + nk + c) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem lit_eq_addc (a b nk c : Nat) (h : a < b) : (a = b + nk + c) = False := by
  simp only [eq_iff_iff, iff_false]; omega

/-- `cf_loop`'s spec at fuel `n` (the induction's statement). -/
def CfLoopSpec (p : Prog) (C : ConsSch) (n : Nat) : Prop :=
  ∀ s₀ : St, ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 1 C.nk s₀)⦄
    exec p n (cfLoop C)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (fprobe C s₀) = fprobe C s₀; ⊤⦄

/-! The induction step, one theorem per shape of the match (elaborated in parallel). -/

theorem cfLoop_succ_exact (p : Prog) (C : ConsSch) (n : Nat) (ih : CfLoopSpec p C n)
    (hx : C.exact = true) : CfLoopSpec p C (n + 1) := by
  intro s₀
  unfold CfLoopSpec at ih
  rw [exec, step_while (w := cfLoop C) rfl]
  simp only [kfLoad, kfKey, kfMatch, cfHit, cfAdv, condOf, hx, ↓reduceIte, List.map,
    mapS, mapE, mapC, lvF, fvF, L.Notation.blk, Nat.reduceLT, Nat.reduceEqDiff]
  vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
    Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide),
    argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 4 (by decide),
    argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide),
    argsOf_setLoc_add 1 C.nk 5 (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
    argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc,
    lit_eq_addc, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind]

theorem cfLoop_succ_none (p : Prog) (C : ConsSch) (hM : CMatchOK p C) (n : Nat)
    (ih : CfLoopSpec p C n) (hx : C.exact = false) (hm : C.mpre = none) :
    CfLoopSpec p C (n + 1) := by
  intro s₀
  unfold CfLoopSpec at ih
  rw [exec, step_while (w := cfLoop C) rfl]
  unfold CMatchOK at hM
  simp only [hm] at hM
  simp only [kfLoad, kfKey, kfMatch, cfHit, cfAdv, condOf, hx, Bool.false_eq_true,
    ↓reduceIte, seqO, hm, List.map, mapS, mapE, mapC, lvF, fvF, L.Notation.blk, Nat.reduceLT,
    Nat.reduceEqDiff]
  vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
    Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide),
    argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 4 (by decide),
    argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide),
    argsOf_setLoc_add 1 C.nk 5 (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
    argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc,
    lit_eq_addc, ↓reduceIte, hM] at *)
  all_goals grind [lang_grind, arena_grind]

theorem cfLoop_succ_some (p : Prog) (C : ConsSch) (hM : CMatchOK p C) (n : Nat)
    (ih : CfLoopSpec p C n) (hx : C.exact = false) (b : Stmt) (hm : C.mpre = some b)
    (hml : 1 ≤ C.mloc) : CfLoopSpec p C (n + 1) := by
  intro s₀
  unfold CfLoopSpec at ih
  rw [exec, step_while (w := cfLoop C) rfl]
  unfold CMatchOK at hM
  simp only [hm] at hM
  simp only [kfLoad, kfKey, kfMatch, cfHit, cfAdv, condOf, hx, Bool.false_eq_true,
    ↓reduceIte, seqO, hm, List.map, mapS, mapE, mapC, lvF, fvF, L.Notation.blk, Nat.reduceLT,
    Nat.reduceEqDiff]
  vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, hM n, ih]
  all_goals (try simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
    Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide),
    argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 4 (by decide),
    argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide),
    argsOf_setLoc_add 1 C.nk 5 (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
    argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc,
    lit_eq_addc, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind]

theorem cfLoop_spec (p : Prog) (C : ConsSch) (hM : CMatchOK p C) (hml : C.mpre ≠ none → 1 ≤ C.mloc)
    (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 1 C.nk s₀)⦄
    exec p n (cfLoop C)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (fprobe C s₀) = fprobe C s₀; ⊤⦄ := by
  revert s₀
  change CfLoopSpec p C n
  induction n with
  | zero => intro s₀; vcgen [exec] <;> grind
  | succ n ih =>
    cases hx : C.exact with
    | true => exact cfLoop_succ_exact p C n ih hx
    | false =>
    cases hm : C.mpre with
    | none => exact cfLoop_succ_none p C hM n ih hx hm
    | some b => exact cfLoop_succ_some p C hM n ih hx b hm (hml (by simp [hm]))

theorem cfLoop_step_spec (p : Prog) (C : ConsSch) (hM : CMatchOK p C)
    (hml : C.mpre ≠ none → 1 ≤ C.mloc) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 1 C.nk s₀)⦄
    step p (exec p n) (cfLoop C)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (fprobe C s₀) = fprobe C s₀; ⊤⦄ :=
  Triple.step_exec (cfLoop_spec p C hM hml (n + 1) s₀)

/-! ### Arguments -/

theorem init_key (pre ks rest : List Word) (i : Nat) (hi : i < ks.length) :
    Locals.init (pre ++ (ks ++ rest)) (i + pre.length) = ks[i] := by
  simp only [Locals.init]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem init_past (pre ks rest : List Word) (a : Nat) :
    Locals.init (pre ++ (ks ++ rest)) (a + pre.length + ks.length) = Locals.init rest a := by
  simp only [Locals.init]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
  congr 2; omega

theorem init_oob (vs : List Word) (x : Nat) (h : vs.length ≤ x) : Locals.init vs x = 0 := by
  simp [Locals.init, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem ofNat_zero' : UInt64.ofNat 0 = 0 := rfl

theorem init_last (t : Word) (as : List Word) (j : Word) (k : Nat) (h : as.length = k) :
    Locals.init (t :: (as ++ [j])) (1 + k) = j := by
  subst h; simpa [Locals.init] using init_past [t] as [j] 0

theorem init_past2 (t : Word) (as : List Word) (j : Word) (k a : Nat) (h : as.length = k)
    (ha : 2 ≤ a) : Locals.init (t :: (as ++ [j])) (a + k) = 0 := by
  apply init_oob
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

theorem argsOf_init (pre ks rest : List Word) (m : Mem) :
    argsOf pre.length ks.length { mem := m, loc := Locals.init (pre ++ (ks ++ rest)) } = ks := by
  unfold argsOf
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact init_key pre ks rest i (by simpa using h2)

theorem argsOf_init1 (t : Word) (as : List Word) (j : Word) (k : Nat) (h : as.length = k)
    (m : Mem) : argsOf 1 k { mem := m, loc := Locals.init (t :: (as ++ [j])) } = as := by
  subst h; exact argsOf_init [t] as [j] m


/-- `nk` words of a call's arguments from `base` on. -/
def argsL (base nk : Nat) (vs : List Word) : List Word :=
  (List.range nk).map fun i => Locals.init vs (i + base)

theorem argsOf_mk (base nk : Nat) (m : Mem) (vs : List Word) :
    argsOf base nk { mem := m, loc := Locals.init vs } = argsL base nk vs := rfl

theorem argsL_eq (pre ks rest : List Word) (k : Nat) (hk : ks.length = k) :
    argsL pre.length k (pre ++ (ks ++ rest)) = ks := by
  subst hk; exact argsOf_init pre ks rest default

theorem argsL_app (t : Word) (ks rest : List Word) (k : Nat) (h : ks.length = k) :
    argsL 1 k (t :: (ks ++ rest)) = ks := by
  subst h; simpa using argsL_eq [t] ks rest ks.length rfl

theorem argsL_key (t h : Word) (ks : List Word) (k : Nat) (hks : ks.length = k) :
    argsL 1 (k + 1) (t :: (ks ++ [h])) = ks ++ [h] := by
  have := argsL_eq [t] (ks ++ [h]) [] (k + 1) (by simp [hks])
  simpa using this

theorem kwE_pval (C : ConsSch) (s : St) :
    Expr.pval s (kwE C) = kwQ C (argsOf 1 C.nk s) (s.loc (1 + C.nk)) := by
  unfold kwE kwQ
  cases hx : C.exact
  · simp [Expr.pval]
  · simp only [↓reduceIte]
    rcases hn : C.nk with _ | _ | nk
    · rfl
    · simp [Expr.pval, argsOf]
    · have h0 : 0 < nk + 1 + 1 := by omega
      have h1 : 1 < nk + 1 + 1 := by omega
      simp [Expr.pval, argsOf, BinOp.eval, List.getD_eq_getElem?_getD, h0, h1]

/-- **`X_find(t, k, h)`** returns the probe of tier `t` from the home slot of `h` (for any
argument list: `t`, the key, `h` and the initial step count are its words `0`, `1 ‥ nk`,
`nk + 1`, `nk + 4`). -/
theorem consFindG_specV (p : Prog) (C : ConsSch) (hM : CMatchOK p C)
    (hml : C.mpre ≠ none → 1 ≤ C.mloc)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsL 1 C.nk vs)⦄
    invoke p (exec p n) C.fname vs
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 (tierA C.sa (Locals.init vs 0)))
        (C.mtM s₀.mem (argsL 1 (C.nk + 1) vs) (Locals.init vs 0))
        C.exact (kwQ C (argsL 1 C.nk vs) (Locals.init vs (1 + C.nk)))
        (baseW s₀.mem (Locals.init vs 0)) (knW C.sa s₀.mem (Locals.init vs 0))
        (krW C.sa s₀.mem (Locals.init vs 0))
        (homeW (Locals.init vs (1 + C.nk)) (knW C.sa s₀.mem (Locals.init vs 0)))
        (Locals.init vs (4 + C.nk)); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, consFindG, kfHead, mapS, mapE, fvF, L.Notation.blk,
    Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, cfLoop_step_spec p C hM hml n]
    all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
        Expr.pval, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add1 1 C.nk 2 (by decide),
        argsOf_setLoc_add 1 C.nk 2 (by decide), argsOf_setLoc_add1 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 6 (by decide),
        argsOf_setLoc_add 1 C.nk 6 (by decide), argsOf_setLoc_addc 1 C.nk 7 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 7 C.mloc (by decide), argsOf_setLoc_addc 1 C.nk 8 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 8 C.mloc (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc,
        lit_eq_addc, kwE_pval,
        zero_ne_add 2 C.nk (by decide), zero_ne_add 3 C.nk (by decide), zero_ne_add 6 C.nk (by decide), argsOf_mk,
        ↓reduceIte] at *)
    all_goals grind [lang_grind, arena_grind, knW, koW, krW, homeW, baseW]

/-- `X_find(t, k, h)` at a key of `nk` words. -/
theorem consFindG_spec (p : Prog) (C : ConsSch) (hM : CMatchOK p C)
    (hml : C.mpre ≠ none → 1 ≤ C.mloc)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (t : Word) (ks : List Word)
    (hks : ks.length = C.nk) (h : Word) (hk : C.keyOK s₀.mem ks) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.fname (t :: (ks ++ [h]))
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 (tierA C.sa t)) (C.mtM s₀.mem (ks ++ [h]) t) C.exact (kwQ C ks h)
        (baseW s₀.mem t) (knW C.sa s₀.mem t) (krW C.sa s₀.mem t) (homeW h (knW C.sa s₀.mem t)) 0; ⊤⦄ := by
  have ek := argsL_key t h ks C.nk hks
  have ek' := argsL_app t ks [h] C.nk hks
  have eh := init_last t ks h C.nk hks
  have ez := init_past2 t ks h C.nk 4 hks (by decide)
  vcgen [consFindG_specV p C hM hml hp n s₀]
  all_goals simp_all [Locals.init_cons_zero]


end L.Arena
