module

public import ConAgua.Arena.ConsLib
public import ConAgua.L.PureEval
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow

@[expose] public section

/-!
# The cons-table library: the specs of the templates, proved once (lane conslib)

A table instance supplies, besides its `ConsSch`, one obligation per fragment (`ConsOK`): the
match prelude and condition compute `mtM` (`MatchOK`), the growth's hash block computes `hsM`
(`HashOK`), `ihash` computes `qhM` (`IHashOK`), the record words are `vsM` of the push's inputs
and read no memory (`RecOK`), the room test is `roomM` (`RoomOK`), the skip word is `skM`
(`SkipOK`). From them:

* `consFindG_spec`: `X_find(t, k, h)` returns `cprobeW` (the probe model, generic in the match);
* `consPushG_spec`: `X_push(t, args, j)` appends node `cntC` and grows (`pushMC`, `growIf`);
* `consInternG_spec`: `intern_X(k)` returns the handle and memory of `consInternM C m k`, **the**
  L model of every intern table.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Variables and frames -/

/-- `nk` variables from `base` on (a function's key words). -/
def argsOf (base nk : Nat) (s : St) : List Word := (List.range nk).map fun i => s.loc (i + base)

/-- Every local but `x` is kept. -/
def Keep1 (x : Var) (s s' : St) : Prop := ∀ z, z ≠ x → s'.loc z = s.loc z

theorem Keep1.loc {x : Var} {s s' : St} (h : Keep1 x s s') (z : Var) (hx : z ≠ x) :
    s'.loc z = s.loc z := h z hx

grind_pattern [lang_grind] Keep1.loc => Keep1 x s s', s'.loc z

theorem argsOf_setLoc (base nk x : Nat) (hx : base + nk ≤ x) (s : St) (v : Word) :
    argsOf base nk (s.setLoc x v) = argsOf base nk s := by
  unfold argsOf; apply List.map_congr_left; intro i hi
  have := List.mem_range.mp hi
  have h2 : ¬ (i + base : Nat) = x := Nat.ne_of_lt (by omega)
  simp only [St.setLoc_loc]; exact ite_eq_right_iff.mpr (fun h => absurd h h2)

theorem argsOf_keep1 (base nk x : Nat) (hx : base + nk ≤ x) (s s' : St) (h : Keep1 x s s') :
    argsOf base nk s' = argsOf base nk s := by
  unfold argsOf; apply List.map_congr_left; intro i hi
  have := List.mem_range.mp hi
  exact h (i + base) (Nat.ne_of_lt (by omega))

grind_pattern [lang_grind] argsOf_keep1 => Keep1 x s s', argsOf base nk s'
grind_pattern [lang_grind] argsOf_setLoc => argsOf base nk (s.setLoc x v)

theorem argsOf_setLoc_add (base nk a : Nat) (ha : base ≤ a) (s : St) (v : Word) :
    argsOf base nk (s.setLoc (a + nk) v) = argsOf base nk s :=
  argsOf_setLoc base nk _ (by omega) s v

theorem zero_ne_add (a nk : Nat) (h : 0 < a) : (0 = a + nk) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem rd64_rdW (m : Mem) (a : ArrId) (i : Word) : rd64 m a i = rdW (m.arr64 a) i := by
  simp [rd64, rdW, Array.getD_eq_getD_getElem?]

/-! ## The probe model -/

/-- The probe of tier `t` (slot base `b`, `n` slots) from slot `j` after `d` steps, for a node
match `mt`: `[1, i, j, d]` (node `i` at slot `j`), `[0, 0, j, d]` (free slot `j`), `[]` (no free
slot in `n` steps; the find aborts). -/
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

/-! ## The obligations of an instance -/

section obligations
variable (p : Prog) (C : ConsSch)

/-- The key of a find state: variables `1 ‥ nk`. -/
abbrev fkeys (s : St) : List Word := argsOf 1 C.nk s

/-- **The match**: the prelude (if any) writes at most the match's own variable `7 + nk` and no
memory; then the condition is `mtM` of node `v - 1` (`v` at `5 + nk`) of tier `t`. -/
def MatchOK : Prop :=
  match C.mpre with
  | none => ∀ s : St, Cond.pval s C.mc = C.mtM s.mem (fkeys C s) (s.loc 0) (s.loc (5 + C.nk) - 1)
  | some b => ∀ (k : Stmt → M Sig) (s₀ : St),
    ⦃fun s => s = s₀⦄
    step p k b
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep1 (7 + C.nk) s₀ s' ∧
      Cond.pval s' C.mc = C.mtM s₀.mem (fkeys C s₀) (s₀.loc 0) (s₀.loc (5 + C.nk) - 1); ⊤⦄

/-- An expression that reads only local variables. -/
def LocOnly (e : Expr) : Prop := ∀ s s' : St, s.loc = s'.loc → Expr.pval s e = Expr.pval s' e

/-- **The record words** read only the push's variables, and are `vsM` of its inputs
(variables `1 ‥ np`). -/
def RecOK : Prop :=
  (∀ e ∈ C.recW, LocOnly e) ∧ ∀ s : St, C.recW.map (Expr.pval s) = C.vsM (argsOf 1 C.np s)

/-- **The room test** is `roomM` of the memory, the tier and the count (`c` at `np + 2`). -/
def RoomOK : Prop :=
  ∀ s : St, Cond.pval s C.room = C.roomM s.mem (s.loc 0) (s.loc (C.np + 2))

/-- **The key's hash**: `ihash` sets `h` (`nk`) to `qhM` of the key and changes nothing else. -/
def IHashOK : Prop :=
  ∀ (k : Stmt → M Sig) (s₀ : St),
    ⦃fun s => s = s₀⦄
    step p k C.ihash
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      LocEq s' (s₀.setLoc C.nk (C.qhM s₀.mem (argsOf 0 C.nk s₀))); ⊤⦄

/-- **The skip word** is `skM` of the key. -/
def SkipOK : Prop :=
  ∀ e, C.skipW = some e → ∀ s : St, Expr.pval s e = C.skM (argsOf 0 C.nk s)

/-- **An instance's obligations.** -/
structure ConsOK : Prop where
  match_ : MatchOK p C
  ghash : HashOK p C.GS (C.np + 4) C.hsM
  ihash : IHashOK p C
  recs : RecOK C
  room : RoomOK C
  skips : SkipOK C
  push_np : C.nk ≤ C.np ∧ C.np ≤ C.nk + 1

end obligations

/-! ## `X_find`: the probe -/

theorem cfLoop_spec (p : Prog) (C : ConsSch) (hM : MatchOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (cfLoop C)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (fkeys C s₀) (s₀.loc 0)) (s₀.loc 0)
        (s₀.loc (6 + C.nk)) (s₀.loc (2 + C.nk)) (s₀.loc (3 + C.nk)) (s₀.loc (4 + C.nk))) =
      cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (fkeys C s₀) (s₀.loc 0)) (s₀.loc 0)
        (s₀.loc (6 + C.nk)) (s₀.loc (2 + C.nk)) (s₀.loc (3 + C.nk)) (s₀.loc (4 + C.nk)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := cfLoop C) rfl]
    unfold MatchOK at hM
    cases hm : C.mpre with
    | none =>
      simp only [hm] at hM
      simp only [cfLoad, cfHit, cfAdv, seqs, seqO, hm, List.map, mapS, mapE, mapC, lvF,
        L.Notation.blk]
      vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, ih]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval, hM,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdW, zero_ne_add, argsOf_setLoc_add 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add 1 C.nk 5 (by decide),
        ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
      all_goals grind [lang_grind, arena_grind]
    | some b =>
      simp only [hm] at hM
      simp only [cfLoad, cfHit, cfAdv, seqs, seqO, hm, List.map, mapS, mapE, mapC, lvF,
        L.Notation.blk]
      vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, hM (exec p n), ih]
      all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdW, zero_ne_add, argsOf_setLoc_add 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add 1 C.nk 5 (by decide),
        ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
      all_goals grind [lang_grind, arena_grind]

theorem cfLoop_step_spec (p : Prog) (C : ConsSch) (hM : MatchOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (cfLoop C)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (fkeys C s₀) (s₀.loc 0)) (s₀.loc 0)
        (s₀.loc (6 + C.nk)) (s₀.loc (2 + C.nk)) (s₀.loc (3 + C.nk)) (s₀.loc (4 + C.nk))) =
      cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (fkeys C s₀) (s₀.loc 0)) (s₀.loc 0)
        (s₀.loc (6 + C.nk)) (s₀.loc (2 + C.nk)) (s₀.loc (3 + C.nk)) (s₀.loc (4 + C.nk)); ⊤⦄ :=
  Triple.step_exec (cfLoop_spec p C hM (n + 1) s₀)

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

theorem argsOf_init (pre ks rest : List Word) (m : Mem) :
    argsOf pre.length ks.length { mem := m, loc := Locals.init (pre ++ (ks ++ rest)) } = ks := by
  unfold argsOf
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact init_key pre ks rest i (by simpa using h2)

/-- **`X_find(t, k, h)`** returns the probe of tier `t` from the home slot of `h`. -/
theorem consFindG_spec (p : Prog) (C : ConsSch) (hM : MatchOK p C)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (t : Word) (ks : List Word)
    (hks : ks.length = C.nk) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.fname (t :: (ks ++ [h]))
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem ks t) t (baseW s₀.mem t) (gnW C.sa s₀.mem)
        (homeW h (gnW C.sa s₀.mem)) 0; ⊤⦄ := by
  have ek : ∀ m, argsOf 1 C.nk { mem := m, loc := Locals.init (t :: (ks ++ [h])) } = ks :=
    fun m => by rw [← hks]; exact argsOf_init [t] ks [h] m
  have e0 : Locals.init (t :: (ks ++ [h])) 0 = t := rfl
  have eh : Locals.init (t :: (ks ++ [h])) (1 + C.nk) = h := by
    rw [← hks]; simpa [Locals.init] using init_past [t] ks [h] 0
  have ez : ∀ a : Nat, 2 ≤ a → Locals.init (t :: (ks ++ [h])) (a + C.nk) = 0 := fun a ha => by
    apply init_oob
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  rw [invoke_eq _ hp]
  simp only [callFn, consFindG, cfHead, seqs, List.map, mapS, mapE, lvF, L.Notation.blk]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalArgs, setLoc, cfLoop_step_spec p C hM n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdW, argsOf_setLoc_add 1 C.nk 2 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add 1 C.nk 6 (by decide),
        zero_ne_add 2 C.nk (by decide), zero_ne_add 3 C.nk (by decide),
        zero_ne_add 4 C.nk (by decide), zero_ne_add 6 C.nk (by decide), ek, e0, eh,
        ez 4 (by decide), ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
    all_goals grind [lang_grind, arena_grind, gnW, gexpW, homeW, baseW]

end L.Arena
