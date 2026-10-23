module

public import ConAgua.Arena.ConsLib
public import ConAgua.L.PureEval
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow

@[expose] public section

/-!
# The cons-table library: the specs of the templates, proved once (lane conslib)

A table instance supplies, besides its `ConsSch`, one obligation per fragment (`ConsOK`): the
match prelude and condition compute `mtM` (`CMatchOK`), the growth's hash block computes `hsM`
(`HashOK`), `ihash` computes `qhM` (`IHashOK`), the record words are `vsM` of the push's inputs
and read no memory (`CRecOK`), the room test is `roomM` (`RoomOK`), the skip word is `skM`
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

theorem argsOf_keepLo (base nk o : Nat) (h : base + nk ≤ o) (s s' : St) (hk : KeepLo o s s') :
    argsOf base nk s' = argsOf base nk s := by
  unfold argsOf; apply List.map_congr_left; intro i hi
  have := List.mem_range.mp hi
  exact hk (i + base) (by omega)

grind_pattern [lang_grind] argsOf_keepLo => KeepLo o s s', argsOf base nk s'

theorem argsOf_setLoc_add1 (base nk a : Nat) (ha : base + 1 ≤ a) (s : St) (v : Word) :
    argsOf base (nk + 1) (s.setLoc (a + nk) v) = argsOf base (nk + 1) s :=
  argsOf_setLoc base (nk + 1) _ (by omega) s v

theorem argsOf_setLoc_add (base nk a : Nat) (ha : base ≤ a) (s : St) (v : Word) :
    argsOf base nk (s.setLoc (a + nk) v) = argsOf base nk s :=
  argsOf_setLoc base nk _ (by omega) s v

theorem zero_ne_add (a nk : Nat) (h : 0 < a) : (0 = a + nk) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem self_ne_add (a nk : Nat) (h : 0 < a) : (nk = a + nk) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem lit_eq_add_false (a b x : Nat) (h : a < b) : (a = b + x) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem add_eq_lit_false (a b x : Nat) (h : a < b) : (b + x = a) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem rd64_rdWC (m : Mem) (a : ArrId) (i : Word) : rd64 m a i = rdW (m.arr64 a) i := by
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

/-- The key of a find state and its hash: variables `1 ‥ nk + 1`. -/
abbrev fkeys (s : St) : List Word := argsOf 1 (C.nk + 1) s

/-- **The match**: the prelude (if any) writes at most the match's own variable `7 + nk` and no
memory; then the condition is `mtM` of node `v - 1` (`v` at `5 + nk`) of tier `t`. -/
def CMatchOK : Prop :=
  match C.mpre with
  | none => ∀ s : St, Cond.pval s C.mc = C.mtM s.mem (fkeys C s) (s.loc 0) (s.loc (5 + C.nk) - 1)
  | some b => ∀ (n : Nat) (s₀ : St),
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 1 C.nk s₀)⦄
    step p (exec p n) b
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep1 (7 + C.nk) s₀ s' ∧
      Cond.pval s' C.mc = C.mtM s₀.mem (fkeys C s₀) (s₀.loc 0) (s₀.loc (5 + C.nk) - 1); ⊤⦄

/-- An expression that reads only local variables. -/
def LocOnly (e : Expr) : Prop := ∀ s s' : St, s.loc = s'.loc → Expr.pval s e = Expr.pval s' e

/-- **The record words** read only the push's variables, and are `vsM` of its inputs
(variables `1 ‥ np`). -/
def CRecOK : Prop :=
  (∀ e ∈ C.recW, LocOnly e) ∧ ∀ s : St, C.recW.map (Expr.pval s) = C.vsM (argsOf 1 C.np s)

/-- **The room test** is `roomM` of the memory, the tier and the count (`c` at `np + 2`). -/
def RoomOK : Prop :=
  ∀ s : St, Cond.pval s C.room = C.roomM s.mem (s.loc 0) (s.loc (2 + C.np))

/-- **The key's hash**: `ihash` sets `h` (`nk`) to `qhM` of the key and changes nothing else. -/
def IHashOK : Prop :=
  ∀ (n : Nat) (s₀ : St),
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 0 C.nk s₀)⦄
    step p (exec p n) C.ihash
    ⦃fun r s' => r = .normal ∧ s' = s₀.setLoc C.nk (C.qhM s₀.mem (argsOf 0 C.nk s₀)); ⊤⦄

/-- **The column's prelude** keeps the inputs and the memory and sets `x` (`4 + np`) to `colM` of
the inputs. -/
def PreOK : Prop :=
  match C.pre with
  | none => C.col = none
  | some b => ∀ (n : Nat) (s₀ : St),
    ⦃fun s => s = s₀⦄
    step p (exec p n) b
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ KeepLo (2 + C.np) s₀ s' ∧
      s'.loc (4 + C.np) = C.colM s₀.mem (argsOf 1 C.np s₀); ⊤⦄

/-- **The skip word** is `skM` of the key. -/
def SkipOK : Prop :=
  ∀ e, C.skipW = some e → ∀ s : St, Expr.pval s e = C.skM (argsOf 0 C.nk s)

/-- **An instance's obligations.** -/
structure ConsOK : Prop where
  match_ : CMatchOK p C
  ghash : HashOK p C.GS (4 + C.xloc + C.np) C.hsM
  ihash : IHashOK p C
  pre : PreOK p C
  colA : ∀ A, C.col = some A → A ≠ C.sa ∧ A ≠ CTL ∧ A ≠ C.ra
  recs : CRecOK C
  room : RoomOK C
  skips : SkipOK C
  push_np : C.nk ≤ C.np ∧ C.np ≤ 1 + C.nk
  arrs : C.ra ≠ CTL ∧ C.sa ≠ CTL ∧ C.ra ≠ C.sa

end obligations

theorem ConsOK.room_eq {p : Prog} {C : ConsSch} (hO : ConsOK p C) (s : St) :
    Cond.pval s C.room = C.roomM s.mem (s.loc 0) (s.loc (2 + C.np)) := hO.room s

/-! ## `X_find`: the probe -/

theorem cfLoop_spec (p : Prog) (C : ConsSch) (hM : CMatchOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 1 C.nk s₀)⦄
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
    unfold CMatchOK at hM
    cases hm : C.mpre with
    | none =>
      simp only [hm] at hM
      simp only [cfLoad, cfHit, cfAdv, seqs, seqO, hm, List.map, mapS, mapE, mapC, lvF,
        L.Notation.blk]
      vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, ih]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval, hM,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide), argsOf_setLoc_add 1 C.nk 3 (by decide),
        argsOf_setLoc_add1 1 C.nk 4 (by decide), argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide), argsOf_setLoc_add 1 C.nk 5 (by decide),
        ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
      all_goals grind [lang_grind, arena_grind]
    | some b =>
      simp only [hm] at hM
      simp only [cfLoad, cfHit, cfAdv, seqs, seqO, hm, List.map, mapS, mapE, mapC, lvF,
        L.Notation.blk]
      vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, hM n, ih]
      all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide), argsOf_setLoc_add 1 C.nk 3 (by decide),
        argsOf_setLoc_add1 1 C.nk 4 (by decide), argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide), argsOf_setLoc_add 1 C.nk 5 (by decide),
        ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
      all_goals grind [lang_grind, arena_grind]

theorem cfLoop_step_spec (p : Prog) (C : ConsSch) (hM : CMatchOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 1 C.nk s₀)⦄
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

/-- **`X_find(t, k, h)`** returns the probe of tier `t` from the home slot of `h` (for any
argument list: `t`, the key, `h` and the initial step count are its words `0`, `1 ‥ nk`,
`nk + 1`, `nk + 4`). -/
theorem consFindG_specV (p : Prog) (C : ConsSch) (hM : CMatchOK p C)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsL 1 C.nk vs)⦄
    invoke p (exec p n) C.fname vs
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (argsL 1 (C.nk + 1) vs) (Locals.init vs 0))
        (Locals.init vs 0) (baseW s₀.mem (Locals.init vs 0)) (gnW C.sa s₀.mem)
        (homeW (Locals.init vs (1 + C.nk)) (gnW C.sa s₀.mem)) (Locals.init vs (4 + C.nk)); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, consFindG, cfHead, seqs, List.map, mapS, mapE, lvF, L.Notation.blk]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalArgs, setLoc, cfLoop_step_spec p C hM n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add1 1 C.nk 2 (by decide), argsOf_setLoc_add 1 C.nk 2 (by decide),
        argsOf_setLoc_add1 1 C.nk 3 (by decide), argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 6 (by decide), argsOf_setLoc_add 1 C.nk 6 (by decide),
        zero_ne_add 2 C.nk (by decide), zero_ne_add 3 C.nk (by decide),
        zero_ne_add 4 C.nk (by decide), zero_ne_add 6 C.nk (by decide), argsOf_mk,
        ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
    all_goals grind [lang_grind, arena_grind, gnW, gexpW, homeW, baseW]

/-- `X_find(t, k, h)` at a key of `nk` words. -/
theorem consFindG_spec (p : Prog) (C : ConsSch) (hM : CMatchOK p C)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (t : Word) (ks : List Word)
    (hks : ks.length = C.nk) (h : Word) (hk : C.keyOK s₀.mem ks) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.fname (t :: (ks ++ [h]))
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (ks ++ [h]) t) t (baseW s₀.mem t) (gnW C.sa s₀.mem)
        (homeW h (gnW C.sa s₀.mem)) 0; ⊤⦄ := by
  have ek := argsL_key t h ks C.nk hks
  have ek' := argsL_app t ks [h] C.nk hks
  have eh := init_last t ks h C.nk hks
  have ez := init_past2 t ks h C.nk 4 hks (by decide)
  vcgen [consFindG_specV p C hM hp n s₀]
  all_goals simp_all [Locals.init_cons_zero]

/-! ## `X_push`: the append -/

/-- The node count of tier `t`. -/
def cntC (C : ConsSch) (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (C.ca + t)

/-- The push's room checks: the handle index, the table's own test. -/
def pushOKC (C : ConsSch) (m : Mem) (t : Word) : Bool :=
  decide (cntC C m t < (134217728 : Word)) && !C.roomM m t (cntC C m t)

/-- Write the words `vs` into array `ra` from word `k + f`. -/
def wrRecK (ra : ArrId) (k : Word) : Mem → Word → List Word → Mem
  | m, _, [] => m
  | m, f, v :: vs => wrRecK ra k (m.set64 ra (k + f) v) (f + 1) vs

/-- After the record: register node `c` of tier `t` at slot `j`, count it. -/
def tailM (C : ConsSch) (t j c : Word) (m : Mem) : Mem :=
  (m.set64 C.sa (j * 2 + t) (rdW (m.arr64 CTL) SCB * t + c + 1)).set64 CTL (C.ca + (t &&& 1)) (c + 1)

/-- **The memory after the append** of node `c` (record `vs`) to tier `t`, registered at `j`. -/
def pushMC (C : ConsSch) (m : Mem) (t : Word) (vs : List Word) (j c : Word) : Mem :=
  tailM C t j c (wrRecK C.ra (c * C.st + t * C.w) m 0 vs)

/-- The derived column's write, `col[2 c + t] := x` (none without a column). -/
def colW (C : ConsSch) (t c x : Word) (m : Mem) : Mem :=
  match C.col with
  | none => m
  | some A => m.set64 A (c * 2 + t) x

/-- **The memory after the append** with the derived column's word `x`. -/
def pushMX (C : ConsSch) (m : Mem) (t : Word) (vs : List Word) (x j c : Word) : Mem :=
  colW C t c x (pushMC C m t vs j c)

theorem pushMX_none {C : ConsSch} (h : C.col = none) (m : Mem) (t : Word) (vs : List Word)
    (x j c : Word) : pushMX C m t vs x j c = pushMC C m t vs j c := by
  simp [pushMX, colW, h]

/-- The growth if node count `c + 1` passes half of the slot count `g + SN0` read before. -/
def growK (C : ConsSch) (g c : Word) (m : Mem) : Option Mem :=
  if g + SN0 < (c + 1) * 2 then growM C.sa C.ca C.hsM m else some m

theorem growIf_growK (C : ConsSch) (m₀ M : Mem) (c : Word) :
    growIf C.sa C.ca C.hsM m₀ M c = growK C (gexpW C.sa m₀) c M := rfl

theorem cpRest_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpRest C)
    ⦃fun r s' => r = .ret [s₁.loc (2 + C.np)] ∧
      growK C (s₁.loc (5 + C.xloc + C.np)) (s₁.loc (2 + C.np))
        (colW C (s₁.loc 0) (s₁.loc (2 + C.np)) (s₁.loc (4 + C.np))
          (tailM C (s₁.loc 0) (s₁.loc (1 + C.np)) (s₁.loc (2 + C.np)) s₁.mem)) = some s'.mem; ⊤⦄ := by
  have hsa := hO.arrs.2.1
  cases hc : C.col with
  | none =>
    simp only [cpRest, cpTail, cpGrowIf, cpColW, hc, Option.map_none, seqO, seqs, List.map, mapS,
      mapE, lvF, L.Notation.blk]
    vcgen [step, evalE_spec, evalC_spec, evalArgs, st64,
      growBlkG_spec p C.GS C.sa C.ca rfl rfl (4 + C.xloc + C.np) C.hsM hO.ghash n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, ↓reduceIte, Nat.add_eq_zero_iff,
          false_and, and_false, Sig.retVal, colW, hc] at *)
    all_goals grind [lang_grind, arena_grind, growK, tailM, baseW]
  | some A =>
    have hA := hO.colA A hc
    simp only [cpRest, cpTail, cpGrowIf, cpColW, hc, Option.map_some, seqO, seqs, List.map, mapS,
      mapE, lvF, L.Notation.blk]
    vcgen [step, evalE_spec, evalC_spec, evalArgs, st64,
      growBlkG_spec p C.GS C.sa C.ca rfl rfl (4 + C.xloc + C.np) C.hsM hO.ghash n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, ↓reduceIte, Nat.add_eq_zero_iff,
          false_and, and_false, Sig.retVal, colW, hc] at *)
    all_goals grind [lang_grind, arena_grind, growK, tailM, baseW]

theorem cpWr_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) :
    ∀ (es : List Expr), (∀ e ∈ es, LocOnly e) → ∀ (f : Nat) (s₁ : St),
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpWr C f es (cpRest C))
    ⦃fun r s' => r = .ret [s₁.loc (2 + C.np)] ∧
      growK C (s₁.loc (5 + C.xloc + C.np)) (s₁.loc (2 + C.np))
        (colW C (s₁.loc 0) (s₁.loc (2 + C.np)) (s₁.loc (4 + C.np))
          (tailM C (s₁.loc 0) (s₁.loc (1 + C.np)) (s₁.loc (2 + C.np))
            (wrRecK C.ra (s₁.loc (3 + C.np)) s₁.mem (UInt64.ofNat f) (es.map (Expr.pval s₁))))) =
        some s'.mem; ⊤⦄ := by
  intro es
  induction es with
  | nil => intro _ f s₁; simp only [cpWr, List.map_nil, wrRecK]; exact cpRest_spec p C hO n s₁
  | cons e es ih =>
    intro hl f s₁
    have hes : ∀ e' ∈ es, LocOnly e' := fun e' h => hl e' (List.mem_cons_of_mem _ h)
    have hmap : ∀ s : St, s.loc = s₁.loc → es.map (Expr.pval s) = es.map (Expr.pval s₁) :=
      fun s h => List.map_congr_left (fun e' he' => hes e' he' s s₁ h)
    have ef : UInt64.ofNat (f + 1) = UInt64.ofNat f + 1 := by simp [UInt64.ofNat_add]
    have e0 : UInt64.ofNat 0 = 0 := rfl
    simp only [cpWr]
    by_cases hf0 : f = 0
    · subst hf0
      simp only [↓reduceIte]
      vcgen [step, evalE_spec, st64, ih hes (0 + 1)]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, List.map_cons, wrRecK, ef, e0,
        UInt64.add_zero, Nat.zero_add] at *)
      all_goals (try simp only [hmap _ rfl] at *)
      all_goals grind
    · simp only [hf0, ↓reduceIte]
      vcgen [step, evalE_spec, st64, ih hes (f + 1)]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Expr.pval, List.map_cons,
        wrRecK, ef] at *)
      all_goals (try simp only [hmap _ rfl] at *)
      all_goals grind

/-- **`X_push(t, args, j)`** appends node `cntC` to tier `t` (record `vsM args`, column word
`colM args`) at slot `j`, then grows if the tier passed half load (any argument list: `t`, the
inputs, `j` are its words `0`, `1 ‥ np`, `np + 1`). -/
theorem consPushG_specV (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hp : p.lookup C.pname = some (consPushG C)) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.pname vs
    ⦃fun r s' => LocEq s' s₀ ∧ pushOKC C s₀.mem (Locals.init vs 0) = true ∧
      r = [cntC C s₀.mem (Locals.init vs 0)] ∧
      growIf C.sa C.ca C.hsM s₀.mem (pushMX C s₀.mem (Locals.init vs 0) (C.vsM (argsL 1 C.np vs))
        (C.colM s₀.mem (argsL 1 C.np vs)) (Locals.init vs (1 + C.np))
        (cntC C s₀.mem (Locals.init vs 0)))
        (cntC C s₀.mem (Locals.init vs 0)) = some s'.mem; ⊤⦄ := by
  have hV := hO.recs.2
  have hPO := hO.pre
  unfold PreOK at hPO
  rw [invoke_eq _ hp]
  simp only [callFn, consPushG, cpHead, cpMid, seqs, List.map, mapS, mapE, mapC, lvF, L.Notation.blk]
  cases hpre : C.pre with
  | none =>
    simp only [hpre] at hPO
    simp only [seqO]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64,
        cpWr_spec p C hO n C.recW hO.recs.1 0]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
          Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add 1 C.np 2 (by decide),
          argsOf_setLoc_add 1 C.np 3 (by decide),
          zero_ne_add 1 C.np (by decide), zero_ne_add 2 C.np (by decide),
argsOf_setLoc_add 1 C.np (5 + C.xloc) (by omega), zero_ne_add (5 + C.xloc) C.np (by omega),
          lit_eq_add_false 0 5 C.xloc (by decide), lit_eq_add_false 1 5 C.xloc (by decide),
          lit_eq_add_false 2 5 C.xloc (by decide), lit_eq_add_false 3 5 C.xloc (by decide),
          lit_eq_add_false 4 5 C.xloc (by decide), add_eq_lit_false 2 5 C.xloc (by decide),
          add_eq_lit_false 3 5 C.xloc (by decide), add_eq_lit_false 4 5 C.xloc (by decide),
          add_eq_lit_false 1 5 C.xloc (by decide), Nat.add_comm C.np 1,
          zero_ne_add 3 C.np (by decide), argsOf_mk,
          hO.room_eq, hO.recs.2, mapC, ofNat_zero', pushMX, colW, hPO,
          ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false, growIf_growK, pushMC, pushOKC,
          cntC] at *)
      all_goals grind [lang_grind, arena_grind, gexpW]
  | some b =>
    simp only [hpre] at hPO
    simp only [seqO]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, hPO n,
        cpWr_spec p C hO n C.recW hO.recs.1 0]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
          Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add 1 C.np 2 (by decide),
          argsOf_setLoc_add 1 C.np 3 (by decide),
          zero_ne_add 1 C.np (by decide), zero_ne_add 2 C.np (by decide),
argsOf_setLoc_add 1 C.np (5 + C.xloc) (by omega), zero_ne_add (5 + C.xloc) C.np (by omega),
          lit_eq_add_false 0 5 C.xloc (by decide), lit_eq_add_false 1 5 C.xloc (by decide),
          lit_eq_add_false 2 5 C.xloc (by decide), lit_eq_add_false 3 5 C.xloc (by decide),
          lit_eq_add_false 4 5 C.xloc (by decide), add_eq_lit_false 2 5 C.xloc (by decide),
          add_eq_lit_false 3 5 C.xloc (by decide), add_eq_lit_false 4 5 C.xloc (by decide),
          add_eq_lit_false 1 5 C.xloc (by decide), Nat.add_comm C.np 1,
          zero_ne_add 3 C.np (by decide), argsOf_mk,
          hO.room_eq, hO.recs.2, mapC, ofNat_zero', pushMX,
          ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false, growIf_growK, pushMC, pushOKC,
          cntC] at *)
      all_goals (obtain ⟨hm1, hk1, hx1⟩ := ‹_ ∧ KeepLo _ _ _ ∧ _›
                 have e0 := hk1 0 (by omega)
                 have e1 := hk1 (1 + C.np) (by omega)
                 have ea := argsOf_keepLo 1 C.np (2 + C.np) (by omega) _ _ hk1
                 simp only [argsOf_mk] at ea e0 e1
                 simp only [e0, e1, ea, hm1, hx1, Nat.add_comm 1 C.np] at *)
      all_goals grind [lang_grind, arena_grind, gexpW]

/-- `X_push(t, args, j)` at `np` inputs. -/
theorem consPushG_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hp : p.lookup C.pname = some (consPushG C)) (n : Nat) (s₀ : St) (t : Word)
    (as : List Word) (has : as.length = C.np) (j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.pname (t :: (as ++ [j]))
    ⦃fun r s' => LocEq s' s₀ ∧ pushOKC C s₀.mem t = true ∧ r = [cntC C s₀.mem t] ∧
      growIf C.sa C.ca C.hsM s₀.mem (pushMX C s₀.mem t (C.vsM as) (C.colM s₀.mem as) j
        (cntC C s₀.mem t)) (cntC C s₀.mem t) = some s'.mem; ⊤⦄ := by
  have ek := argsL_eq [t] as [j] C.np has
  have ej := init_last t as j C.np has
  simp only [List.length_singleton, List.singleton_append] at ek
  vcgen [consPushG_specV p C hO hp n s₀]
  all_goals simp_all [Locals.init_cons_zero]

/-! ## `intern_X`: the model and the spec -/

/-- The scratch-skip word `intern_X` computes: the table's skip word if the scratch tier is open. -/
def skipC (C : ConsSch) (m : Mem) (ks : List Word) : Word :=
  match C.skipW with
  | some _ => if rdW (m.arr64 CTL) 1 ≠ 0 then C.skM ks else 0
  | none => 0

/-- The push's inputs: the key, and the hash if the record stores it. -/
def pushArgs (C : ConsSch) (ks : List Word) (h : Word) : List Word :=
  ks ++ (if C.nk < C.np then [h] else [])

/-- The append of the key's record to tier `t` at slot `j`, with the handle (base `B`). -/
def pushC (C : ConsSch) (m : Mem) (t B : Word) (ks : List Word) (h j : Word) : Option (Word × Mem) :=
  if pushOKC C m t then
    match growIf C.sa C.ca C.hsM m (pushMX C m t (C.vsM (pushArgs C ks h)) (C.colM m (pushArgs C ks h))
      j (cntC C m t)) (cntC C m t) with
    | some m' => some (B + cntC C m t, m')
    | none => none
  else none

/-- The probe of tier `t` for key `ks` (hash `h`). -/
def probeC (C : ConsSch) (m : Mem) (ks : List Word) (h t : Word) : List Word :=
  cprobeW (m.arr64 C.sa) (C.mtM m (ks ++ [h]) t) t (baseW m t) (gnW C.sa m) (homeW h (gnW C.sa m)) 0

/-- **The L model of `intern_X(k)`**: the handle and the memory after, `none` where the L code
aborts. The persistent probe unless skipped, the scratch probe if the scratch tier is open, the
append to the tier the store is in. -/
def consInternM (C : ConsSch) (m : Mem) (ks : List Word) : Option (Word × Mem) :=
  let h := C.qhM m ks
  let rs₀ := probeC C m ks h 0
  let rs₁ := probeC C m ks h 1
  if skipC C m ks = 0 ∧ rs₀ = [] then none
  else if skipC C m ks = 0 ∧ rs₀.headD 0 ≠ 0 then some (C.P + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (C.S + rs₁.tail.headD 0, m)
    else pushC C m 1 C.S ks h (rs₁.tail.tail.headD 0)
  else pushC C m 0 C.P ks h (rs₀.tail.tail.headD 0)

theorem ConsOK.ihash_spec {p : Prog} {C : ConsSch} (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 0 C.nk s₀)⦄
    step p (exec p n) C.ihash
    ⦃fun r s' => r = .normal ∧ s' = s₀.setLoc C.nk (C.qhM s₀.mem (argsOf 0 C.nk s₀)); ⊤⦄ :=
  hO.ihash n s₀

theorem evalArgs_spec (es : List Expr) (s₀ : St) :
    ⦃fun s => s = s₀⦄ evalArgs es ⦃fun vs s' => s' = s₀ ∧ vs = es.map (Expr.pval s₀); ⊤⦄ := by
  induction es with
  | nil => vcgen [evalArgs] <;> grind
  | cons e es ih => vcgen [evalArgs, evalE_spec e s₀, ih] <;> grind

theorem map_keyArgs (nk : Nat) (extra : List Expr) (s : St) :
    (keyArgs nk extra).map (Expr.pval s) = argsOf 0 nk s ++ extra.map (Expr.pval s) := by
  simp [keyArgs, argsOf, Expr.pval]

theorem argsOf_self (m : Mem) (ks : List Word) (k : Nat) (h : ks.length = k) :
    argsOf 0 k { mem := m, loc := Locals.init ks } = ks := by
  subst h; simpa using argsOf_init [] ks [] m

theorem init_app_past (t : Word) (ks rest : List Word) (k a : Nat) (h : ks.length = k) :
    Locals.init (t :: (ks ++ rest)) (a + 1 + k) = Locals.init rest a := by
  subst h; simpa [Nat.add_assoc, Nat.add_comm] using init_past [t] ks rest a

theorem keyArgs_len (nk : Nat) (extra : List Expr) : (keyArgs nk extra).length = nk + extra.length := by
  simp [keyArgs]

theorem map_hOpt (C : ConsSch) (s : St) :
    (hOpt C).map (Expr.pval s) = if C.nk < C.np then [s.loc C.nk] else [] := by
  unfold hOpt; split <;> simp [Expr.pval]

theorem argsL_push (C : ConsSch) (hn : C.nk ≤ C.np ∧ C.np ≤ 1 + C.nk) (t h j : Word)
    (ks : List Word) (hks : ks.length = C.nk) :
    argsL 1 C.np (t :: (ks ++ ((if C.nk < C.np then [h] else []) ++ [j]))) = pushArgs C ks h := by
  unfold pushArgs
  rw [← List.append_assoc]
  apply argsL_app
  split <;> simp <;> omega

theorem init_push_j (C : ConsSch) (hn : C.nk ≤ C.np ∧ C.np ≤ 1 + C.nk) (t h j : Word)
    (ks : List Word) (hks : ks.length = C.nk) :
    Locals.init (t :: (ks ++ ((if C.nk < C.np then [h] else []) ++ [j]))) (1 + C.np) = j := by
  rw [← List.append_assoc]
  apply init_last
  split <;> simp <;> omega

-- the no-skip arm's normalising `simp` needs more than the default (heartbeats, not search)
set_option maxHeartbeats 800000 in
/-- **`intern_X(k)`** returns the handle and the memory of `consInternM`. -/
theorem consInternG_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hpf : p.lookup C.fname = some (consFindG C)) (hpp : p.lookup C.pname = some (consPushG C))
    (fn : FnName)
    (hpi : p.lookup fn = some (consInternG C)) (n : Nat) (s₀ : St) (ks : List Word)
    (hks : ks.length = C.nk) (hk : C.keyOK s₀.mem ks) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) fn ks
    ⦃fun r s' => LocEq s' s₀ ∧ consInternM C s₀.mem ks = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hn := hO.push_np
  rw [invoke_eq _ hpi]
  simp only [callFn]
  cases hsk : C.skipW with
  | some e =>
    have he := hO.skips e hsk
    simp only [consInternG, hsk, seqs, ciFind, ciHit, ciScr, ciEnd, ciPush, ciOpen]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs_spec, setLoc, setLocs, hO.ihash_spec n,
        consFindG_specV p C hO.match_ hpf n, consPushG_specV p C hO hpp n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, List.map_cons, map_keyArgs,
        List.map_append, map_hOpt] at *)
      all_goals subst_vars
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, hO.skips e hsk,
        Nat.left_eq_add, Nat.add_eq_left, Nat.add_right_cancel_iff, Nat.reduceEqDiff,
        argsOf_setLoc 0 C.nk C.nk (by omega), argsOf_setLoc_add 0 C.nk 1 (by omega),
        argsOf_setLoc_add 0 C.nk 2 (by omega), argsOf_setLoc_add 0 C.nk 3 (by omega),
        argsOf_setLoc_add 0 C.nk 4 (by omega), argsOf_setLoc_add 0 C.nk 5 (by omega),
        argsOf_self _ ks C.nk hks, argsL_key _ _ ks C.nk hks, argsL_app _ ks _ C.nk hks,
        Locals.init_cons_zero,
        init_last _ ks _ C.nk hks, init_past2 _ ks _ C.nk 4 hks (by decide),
        argsL_push C hn _ _ _ ks hks, init_push_j C hn _ _ _ ks hks, List.map_nil,
        self_ne_add 1 C.nk (by decide), ↓reduceIte] at *)
      all_goals (simp only [consInternM, skipC, hsk, probeC, pushC, Sig.retVal, List.headD_cons,
        bne_iff_ne, beq_iff_eq, ne_eq, LocEq, Sig.retOr] at *)
      all_goals (simp_all)
  | none =>
    simp only [consInternG, hsk, seqs, ciFind, ciHit, ciScr, ciEnd, ciPush, ciOpen]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs_spec, setLoc, setLocs, hO.ihash_spec n,
        consFindG_specV p C hO.match_ hpf n, consPushG_specV p C hO hpp n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, List.map_cons, map_keyArgs,
        List.map_append, map_hOpt] at *)
      all_goals subst_vars
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem,
        Nat.left_eq_add, Nat.add_eq_left, Nat.add_right_cancel_iff, Nat.reduceEqDiff,
        argsOf_setLoc 0 C.nk C.nk (by omega), argsOf_setLoc_add 0 C.nk 1 (by omega),
        argsOf_setLoc_add 0 C.nk 2 (by omega), argsOf_setLoc_add 0 C.nk 3 (by omega),
        argsOf_setLoc_add 0 C.nk 4 (by omega), argsOf_setLoc_add 0 C.nk 5 (by omega),
        argsOf_self _ ks C.nk hks, argsL_key _ _ ks C.nk hks, argsL_app _ ks _ C.nk hks,
        Locals.init_cons_zero,
        init_last _ ks _ C.nk hks, init_past2 _ ks _ C.nk 4 hks (by decide),
        argsL_push C hn _ _ _ ks hks, init_push_j C hn _ _ _ ks hks, List.map_nil,
        self_ne_add 1 C.nk (by decide), ↓reduceIte] at *)
      all_goals (simp only [consInternM, skipC, hsk, probeC, pushC, Sig.retVal, List.headD_cons,
        bne_iff_ne, beq_iff_eq, ne_eq, LocEq, Sig.retOr] at *)
      all_goals (simp_all)


/-! ## What an interning does to memory -/

/-- **An interning hits** (the memory is unchanged) **or appends** node `cntC` to a tier, with its
growth. -/
theorem consInternM_cases {C : ConsSch} {m m₁ : Mem} {ks : List Word} {r : Word}
    (h : consInternM C m ks = some (r, m₁)) :
    m₁ = m ∨ ∃ t j, t ≤ 1 ∧ pushOKC C m t = true ∧
      growIf C.sa C.ca C.hsM m (pushMX C m t (C.vsM (pushArgs C ks (C.qhM m ks)))
        (C.colM m (pushArgs C ks (C.qhM m ks))) j (cntC C m t))
        (cntC C m t) = some m₁ ∧ r = (if t = 0 then C.P else C.S) + cntC C m t := by
  simp only [consInternM, pushC] at h
  repeat' split at h
  all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals first
    | exact .inl h.2.symm
    | (obtain ⟨rfl, rfl⟩ := h
       first
         | exact .inr ⟨1, _, by decide, ‹_›, ‹_›, by simp⟩
         | exact .inr ⟨0, _, by decide, ‹_›, ‹_›, by simp⟩)

end L.Arena
