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
  ∀ s : St, Cond.pval s C.room = C.roomM s.mem (s.loc 0) (s.loc (2 + C.np))

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
  ghash : HashOK p C.GS (4 + C.np) C.hsM
  ihash : IHashOK p C
  recs : RecOK C
  room : RoomOK C
  skips : SkipOK C
  push_np : C.nk ≤ C.np ∧ C.np ≤ 1 + C.nk
  arrs : C.ra ≠ CTL ∧ C.sa ≠ CTL ∧ C.ra ≠ C.sa

end obligations

theorem ConsOK.room_eq {p : Prog} {C : ConsSch} (hO : ConsOK p C) (s : St) :
    Cond.pval s C.room = C.roomM s.mem (s.loc 0) (s.loc (2 + C.np)) := hO.room s

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

/-- **`X_find(t, k, h)`** returns the probe of tier `t` from the home slot of `h` (for any
argument list: `t`, the key, `h` and the initial step count are its words `0`, `1 ‥ nk`,
`nk + 1`, `nk + 4`). -/
theorem consFindG_specV (p : Prog) (C : ConsSch) (hM : MatchOK p C)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.fname vs
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (argsL 1 C.nk vs) (Locals.init vs 0))
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
        Nat.reduceEqDiff, rd64_rdW, argsOf_setLoc_add 1 C.nk 2 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add 1 C.nk 6 (by decide),
        zero_ne_add 2 C.nk (by decide), zero_ne_add 3 C.nk (by decide),
        zero_ne_add 4 C.nk (by decide), zero_ne_add 6 C.nk (by decide), argsOf_mk,
        ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
    all_goals grind [lang_grind, arena_grind, gnW, gexpW, homeW, baseW]

/-- `X_find(t, k, h)` at a key of `nk` words. -/
theorem consFindG_spec (p : Prog) (C : ConsSch) (hM : MatchOK p C)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (t : Word) (ks : List Word)
    (hks : ks.length = C.nk) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.fname (t :: (ks ++ [h]))
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem ks t) t (baseW s₀.mem t) (gnW C.sa s₀.mem)
        (homeW h (gnW C.sa s₀.mem)) 0; ⊤⦄ := by
  have ek := argsL_eq [t] ks [h] C.nk hks
  have eh := init_last t ks h C.nk hks
  have ez := init_past2 t ks h C.nk 4 hks (by decide)
  simp only [List.length_singleton, List.singleton_append] at ek
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

/-- The growth if node count `c + 1` passes half of the slot count `g + SN0` read before. -/
def growK (C : ConsSch) (g c : Word) (m : Mem) : Option Mem :=
  if g + SN0 < (c + 1) * 2 then growM C.sa C.ca C.hsM m else some m

theorem growIf_growK (C : ConsSch) (m₀ M : Mem) (c : Word) :
    growIf C.sa C.ca C.hsM m₀ M c = growK C (gexpW C.sa m₀) c M := rfl

theorem cpRest_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpRest C)
    ⦃fun r s' => r = .ret [s₁.loc (2 + C.np)] ∧
      growK C (s₁.loc (5 + C.np)) (s₁.loc (2 + C.np))
        (tailM C (s₁.loc 0) (s₁.loc (1 + C.np)) (s₁.loc (2 + C.np)) s₁.mem) = some s'.mem; ⊤⦄ := by
  have hsa := hO.arrs.2.1
  simp only [cpRest, cpTail, cpGrowIf, seqs, List.map, mapS, mapE, lvF, L.Notation.blk]
  vcgen [step, evalE_spec, evalC_spec, evalArgs, st64,
    growBlkG_spec p C.GS C.sa C.ca rfl rfl (4 + C.np) C.hsM hO.ghash n]
  all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdW, ↓reduceIte, Nat.add_eq_zero_iff,
        false_and, and_false, Sig.retVal] at *)
  all_goals grind [lang_grind, arena_grind, growK, tailM, baseW]

theorem cpWr_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) :
    ∀ (es : List Expr), (∀ e ∈ es, LocOnly e) → ∀ (f : Nat) (s₁ : St),
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpWr C f es (cpRest C))
    ⦃fun r s' => r = .ret [s₁.loc (2 + C.np)] ∧
      growK C (s₁.loc (5 + C.np)) (s₁.loc (2 + C.np))
        (tailM C (s₁.loc 0) (s₁.loc (1 + C.np)) (s₁.loc (2 + C.np))
          (wrRecK C.ra (s₁.loc (3 + C.np)) s₁.mem (UInt64.ofNat f) (es.map (Expr.pval s₁)))) =
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

/-- **`X_push(t, args, j)`** appends node `cntC` to tier `t` (record `vsM args`) at slot `j`,
then grows if the tier passed half load (any argument list: `t`, the inputs, `j` are its words
`0`, `1 ‥ np`, `np + 1`). -/
theorem consPushG_specV (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hp : p.lookup C.pname = some (consPushG C)) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.pname vs
    ⦃fun r s' => LocEq s' s₀ ∧ pushOKC C s₀.mem (Locals.init vs 0) = true ∧
      r = [cntC C s₀.mem (Locals.init vs 0)] ∧
      growIf C.sa C.ca C.hsM s₀.mem (pushMC C s₀.mem (Locals.init vs 0) (C.vsM (argsL 1 C.np vs))
        (Locals.init vs (1 + C.np)) (cntC C s₀.mem (Locals.init vs 0)))
        (cntC C s₀.mem (Locals.init vs 0)) = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, consPushG, cpHead, cpMid, seqs, List.map, mapS, mapE, mapC, lvF, L.Notation.blk]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64,
      cpWr_spec p C hO n C.recW hO.recs.1 0]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdW, argsOf_setLoc_add 1 C.np 2 (by decide),
        argsOf_setLoc_add 1 C.np 3 (by decide), argsOf_setLoc_add 1 C.np 5 (by decide),
        zero_ne_add 1 C.np (by decide), zero_ne_add 2 C.np (by decide),
        zero_ne_add 3 C.np (by decide), zero_ne_add 5 C.np (by decide), argsOf_mk,
        hO.room_eq, hO.recs.2, mapC, ofNat_zero',
        ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false, growIf_growK, pushMC, pushOKC,
        cntC] at *)
    all_goals grind [lang_grind, arena_grind, gexpW]

/-- `X_push(t, args, j)` at `np` inputs. -/
theorem consPushG_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hp : p.lookup C.pname = some (consPushG C)) (n : Nat) (s₀ : St) (t : Word)
    (as : List Word) (has : as.length = C.np) (j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.pname (t :: (as ++ [j]))
    ⦃fun r s' => LocEq s' s₀ ∧ pushOKC C s₀.mem t = true ∧ r = [cntC C s₀.mem t] ∧
      growIf C.sa C.ca C.hsM s₀.mem (pushMC C s₀.mem t (C.vsM as) j (cntC C s₀.mem t))
        (cntC C s₀.mem t) = some s'.mem; ⊤⦄ := by
  have ek := argsL_eq [t] as [j] C.np has
  have ej := init_last t as j C.np has
  simp only [List.length_singleton, List.singleton_append] at ek
  vcgen [consPushG_specV p C hO hp n s₀]
  all_goals simp_all [Locals.init_cons_zero]

end L.Arena
