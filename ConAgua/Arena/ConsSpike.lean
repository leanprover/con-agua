import ConAgua.Arena.Store
import ConAgua.L.PureEval

/-! Spike (lane conslib, not landed): a generic probe `X_find` for a variable number of keys
and an instance-supplied match (a prelude block and a condition), and its spec, proved once. -/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena.Spike

def mapE (f : Var → Var) : Expr → Expr
  | .var x => .var (f x)
  | .bin op a b => .bin op (mapE f a) (mapE f b)
  | .ld8 a i => .ld8 a (mapE f i)
  | .ld64 a i => .ld64 a (mapE f i)
  | .cmpw c a b => .cmpw c (mapE f a) (mapE f b)
  | .ldc d i => .ldc d (mapE f i)
  | e => e

def mapC (f : Var → Var) : Cond → Cond
  | .cmp c a b => .cmp c (mapE f a) (mapE f b)
  | .and p q => .and (mapC f p) (mapC f q)
  | .or p q => .or (mapC f p) (mapC f q)
  | .not p => .not (mapC f p)

def mapS (f : Var → Var) : Stmt → Stmt
  | .set x e => .set (f x) (mapE f e)
  | .st8 a i e => .st8 a (mapE f i) (mapE f e)
  | .st64 a i e => .st64 a (mapE f i) (mapE f e)
  | .seq s t => .seq (mapS f s) (mapS f t)
  | .ite c s t => .ite (mapC f c) (mapS f s) (mapS f t)
  | .while c s => .while (mapC f c) (mapS f s)
  | .ret es => .ret (es.map (mapE f))
  | .call xs g args => .call (xs.map f) g (args.map (mapE f))
  | .gset g e => .gset g (mapE f e)
  | s => s

/-- A cons table's find: slot array, number of keys, the match (prelude and condition, written
with the find's own variables: `t` 0, `h` 1, keys `2 ‥ nk + 1`, then `n j d v b m`). -/
structure CSch where
  sa : ArrId
  nk : Nat
  mpre : Stmt
  mc : Cond

/-- The generic variables `t h n j d v b m` (0‥7) as the find's: the loop variables past the keys. -/
def lv (nk : Nat) (x : Var) : Var := if x < 2 then x else x + nk

def cfHead (sa : ArrId) : Stmt := lblk (t, h, n, j, d, v, b, m) {
  n := sa.u64[len(sa.u64) - 1] + ⟪SN0⟫;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n)
}
def cfSlot (sa : ArrId) : Stmt := lblk (t, h, n, j, d, v, b, m) {
  v := sa.u64[j * 2 + t];
  if v <= b { return (0, 0, j, d) };
  v := v - b
}
def cfHit : Stmt := lblk (t, h, n, j, d, v, b, m) { return (1, v - 1, j, d) }
def cfAdv : Stmt := lblk (t, h, n, j, d, v, b, m) {
  j := (j + 1) * u64(j + 1 < n);
  d += 1
}

def cfLoop (C : CSch) : Stmt :=
  .while (.cmp .ult (.var (4 + C.nk)) (.var (2 + C.nk)))
    (.seq (mapS (lv C.nk) (cfSlot C.sa))
      (.seq C.mpre (.seq (.ite C.mc (mapS (lv C.nk) cfHit) .skip) (mapS (lv C.nk) cfAdv))))

def consFindG (C : CSch) : FunDecl :=
  { nparams := C.nk + 2, nlocals := C.nk + 8,
    body := .seq (mapS (lv C.nk) (cfHead C.sa)) (.seq (cfLoop C) .abort) }

/-- The keys of a state. -/
def keysOf (nk : Nat) (s : St) : List Word := (List.range nk).map fun i => s.loc (i + 2)

/-- The probe model, for a node match `mt`. -/
def cprobeW (sl : Array Word) (mt : Word → Bool) (t b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if mt (slotV sl b (j * 2 + t) - 1) then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else cprobeW sl mt t b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega


theorem rd64_rdW (m : Mem) (a : ArrId) (i : Word) : rd64 m a i = rdW (m.arr64 a) i := by
  simp [rd64, rdW, Array.getD_eq_getD_getElem?]

section probeArms
variable (sl : Array Word) (mt : Word → Bool) (t b n j d : Word)

theorem cprobeW_free (x : Word) (hd : d < n) (hx : x = j * 2 + t) (hv : rdW sl x ≤ b) :
    cprobeW sl mt t b n j d = [0, 0, j, d] := by
  subst hx; rw [cprobeW]; simp [hd, slotV, slotRd, hv]

theorem cprobeW_hit (x : Word) (hd : d < n) (hx : x = j * 2 + t) (hv : ¬ rdW sl x ≤ b)
    (hm : mt (rdW sl x - b - 1) = true) :
    cprobeW sl mt t b n j d = [1, rdW sl x - b - 1, j, d] := by
  subst hx
  have ne : rdW sl (j * 2 + t) - b ≠ 0 := fun h => hv (by grind)
  rw [cprobeW]; simp [hd, slotV, slotRd, hv, ne, hm]

theorem cprobeW_next (x : Word) (j' d' : Word) (hd : d < n) (hx : x = j * 2 + t)
    (hv : ¬ rdW sl x ≤ b) (hm : mt (rdW sl x - b - 1) = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    cprobeW sl mt t b n j d = cprobeW sl mt t b n j' d' := by
  subst hx hj' hd'
  have ne : rdW sl (j * 2 + t) - b ≠ 0 := fun h => hv (by grind)
  rw [cprobeW]; simp [hd, slotV, slotRd, hv, ne, hm]

theorem cprobeW_end (hd : ¬ d < n) : cprobeW sl mt t b n j d = [] := by
  rw [cprobeW]; simp only [hd, ↓reduceIte]

end probeArms

grind_pattern [arena_grind] cprobeW_free => cprobeW sl mt t b n j d, rdW sl x
grind_pattern [arena_grind] cprobeW_hit => cprobeW sl mt t b n j d, rdW sl x
grind_pattern [arena_grind] cprobeW_next =>
  cprobeW sl mt t b n j d, rdW sl x, cprobeW sl mt t b n j' d'
grind_pattern [arena_grind] cprobeW_end => cprobeW sl mt t b n j d

/-- Every local but `x` is kept. -/
def Keep1 (x : Var) (s s' : St) : Prop := ∀ z, z ≠ x → s'.loc z = s.loc z

theorem Keep1.loc {x : Var} {s s' : St} (h : Keep1 x s s') (z : Var) (hx : z ≠ x) :
    s'.loc z = s.loc z := h z hx

grind_pattern [lang_grind] Keep1.loc => Keep1 x s s', s'.loc z

theorem keysOf_setLoc (nk x : Nat) (hx : nk + 2 ≤ x) (s : St) (v : Word) :
    keysOf nk (s.setLoc x v) = keysOf nk s := by
  unfold keysOf; apply List.map_congr_left; intro i hi
  have := List.mem_range.mp hi
  have h2 : ¬ (i + 2 : Nat) = x := Nat.ne_of_lt (by omega)
  simp only [St.setLoc_loc]; exact ite_eq_right_iff.mpr (fun h => absurd h h2)

theorem keysOf_keep1 (nk x : Nat) (hx : nk + 2 ≤ x) (s s' : St) (h : Keep1 x s s') :
    keysOf nk s' = keysOf nk s := by
  unfold keysOf; apply List.map_congr_left; intro i hi
  have := List.mem_range.mp hi
  have h2 : ¬ (i + 2 : Nat) = x := Nat.ne_of_lt (by omega)
  exact h (i + 2) h2

theorem keysOf_setLoc_add (nk a : Nat) (ha : 2 ≤ a) (s : St) (v : Word) :
    keysOf nk (s.setLoc (a + nk) v) = keysOf nk s := keysOf_setLoc nk _ (by omega) s v

grind_pattern [lang_grind] keysOf_keep1 => Keep1 x s s', keysOf nk s'
grind_pattern [lang_grind] keysOf_setLoc => keysOf nk (s.setLoc x v)

theorem zero_ne_add (a nk : Nat) (h : 0 < a) : (0 = a + nk) = False := by
  simp only [eq_iff_iff, iff_false]; omega

/-- **The instance's match obligation**: the prelude writes at most `m` (`7 + nk`) and nothing in
memory, and then the condition is `mt` of the node `v - 1` (`v` at `5 + nk`). -/
def MatchOK (p : Prog) (C : CSch) (mt : Mem → List Word → Word → Word → Bool) : Prop :=
  ∀ (k : Stmt → M Sig) (s₀ : St),
    ⦃fun s => s = s₀⦄
    step p k C.mpre
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep1 (7 + C.nk) s₀ s' ∧
      Cond.pval s' C.mc = mt s₀.mem (keysOf C.nk s₀) (s₀.loc 0) (s₀.loc (5 + C.nk) - 1); ⊤⦄

theorem keysOf_congr (nk : Nat) (s s' : St) (h : ∀ x, x < nk + 2 → s'.loc x = s.loc x) :
    keysOf nk s' = keysOf nk s := by
  simp only [keysOf, List.map_inj_left, List.mem_range]
  intro i hi; exact h _ (by omega)

theorem cfLoop_spec (p : Prog) (C : CSch) (mt : Mem → List Word → Word → Word → Bool)
    (hM : MatchOK p C mt) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (cfLoop C)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (cprobeW (s₀.mem.arr64 C.sa) (mt s₀.mem (keysOf C.nk s₀) (s₀.loc 0)) (s₀.loc 0)
        (s₀.loc (6 + C.nk)) (s₀.loc (2 + C.nk)) (s₀.loc (3 + C.nk)) (s₀.loc (4 + C.nk))) =
      cprobeW (s₀.mem.arr64 C.sa) (mt s₀.mem (keysOf C.nk s₀) (s₀.loc 0)) (s₀.loc 0)
        (s₀.loc (6 + C.nk)) (s₀.loc (2 + C.nk)) (s₀.loc (3 + C.nk)) (s₀.loc (4 + C.nk)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := cfLoop C) rfl]
    simp only [cfSlot, cfHit, cfAdv, mapS, mapE, mapC, lv, L.Notation.blk, List.map]
    vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, hM (exec p n), ih]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
      Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff, Nat.reduceEqDiff, rd64_rdW, zero_ne_add, keysOf_setLoc_add C.nk 3 (by decide), keysOf_setLoc_add C.nk 4 (by decide), keysOf_setLoc_add C.nk 5 (by decide),
      ite_true, ite_false, Nat.reduceLT, Nat.lt_irrefl, Nat.not_lt] at *)
    all_goals (try grind [lang_grind, arena_grind])

end L.Arena.Spike
