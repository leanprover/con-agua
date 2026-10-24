module

public import ConAgua.Arena.ConsLib
public import ConAgua.Arena.SlotGrowSpec
public import ConAgua.L.PureEval
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow

@[expose] public section

/-!
# The cons-table library: the specs of the templates, proved once (lane conslib)

A table instance supplies, besides its `ConsSch`, one obligation per fragment (`ConsOK`): the
match prelude and condition compute `mtM` (`CMatchOK`), `ihash` computes `qhM` (`IHashOK`, and
spliced at `gO + 14`, `IHashAtOK`), the record words are `vsM` of the push's inputs
and read no memory (`CRecOK`), the room test is `roomM` (`RoomOK`), the skip word is `skM`
(`SkipOK`). From them:

* `consFindG_spec`: `X_find(t, k, h)` returns `cprobeW` (the probe model, generic in the match);
* `consPushG_spec`: `X_push(t, args, j)` appends node `cntC` and grows (`pushMC`, `kgrowIf`);
* `consInternG_spec`: `intern_X(k)` returns the handle and memory of `consInternM C m k`, **the**
  L model of every intern table.
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

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

/-- A triple whose precondition adds a pure fact `K` follows from one that may assume `K` (for an
obligation whose fragment needs the key precondition). -/
theorem triple_pre_and {α : Type} {x : M α} {s₀ : St} {K : Prop} {Q : α → St → Prop}
    (h : K → ⦃fun s => s = s₀⦄ x ⦃Q; ⊤⦄) : ⦃fun s => s = s₀ ∧ K⦄ x ⦃Q; ⊤⦄ :=
  ⟨fun s ⟨hs, hk⟩ => (h hk).le_wp s hs⟩

/-! ## The probe model -/

/-- The probe of a tier's table (first word `r`, `n` slots, slot base `b`) for the key word `q`
from slot `j` after `d` steps, for a node match `mt` (not run on an exact table, `ex`):
`[1, i, j, d]` (node `i` at slot `j`, its key word `q`), `[0, 0, j, d]` (free slot `j`), `[]` (no
free slot in `n` steps; the find aborts). -/
def cprobeW (sl : Array Word) (mt : Word → Bool) (ex : Bool) (q b n r j d : Word) : List Word :=
  if d < n then
    if slotV sl b (r + j * 2) = 0 then [0, 0, j, d]
    else if rdW sl (r + j * 2 + 1) = q ∧ (ex = true ∨ mt (slotV sl b (r + j * 2) - 1) = true) then
      [1, slotV sl b (r + j * 2) - 1, j, d]
    else cprobeW sl mt ex q b n r ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl : Array Word) (mt : Word → Bool) (ex : Bool) (q b n r j d : Word)

theorem cprobeW_free (hd : d < n) (hv : rdW sl (r + j * 2) ≤ b) :
    cprobeW sl mt ex q b n r j d = [0, 0, j, d] := by
  rw [cprobeW]; simp [hd, slotV, slotRd, hv]

theorem cprobeW_hitX (hd : d < n) (hv : ¬ rdW sl (r + j * 2) ≤ b)
    (hk : rdW sl (r + j * 2 + 1) = q) (he : ex = true) :
    cprobeW sl mt ex q b n r j d = [1, rdW sl (r + j * 2) - b - 1, j, d] := by
  have ne : rdW sl (r + j * 2) - b ≠ 0 := fun h => hv (by grind)
  rw [cprobeW]; simp [hd, slotV, slotRd, hv, ne, hk, he]

theorem cprobeW_hitM (hd : d < n) (hv : ¬ rdW sl (r + j * 2) ≤ b)
    (hk : rdW sl (r + j * 2 + 1) = q) (hm : mt (rdW sl (r + j * 2) - b - 1) = true) :
    cprobeW sl mt ex q b n r j d = [1, rdW sl (r + j * 2) - b - 1, j, d] := by
  have ne : rdW sl (r + j * 2) - b ≠ 0 := fun h => hv (by grind)
  rw [cprobeW]; simp [hd, slotV, slotRd, hv, ne, hk, hm]

theorem cprobeW_nextK (j' d' : Word) (hd : d < n) (hv : ¬ rdW sl (r + j * 2) ≤ b)
    (hk : ¬ rdW sl (r + j * 2 + 1) = q)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    cprobeW sl mt ex q b n r j d = cprobeW sl mt ex q b n r j' d' := by
  subst hj' hd'
  have ne : rdW sl (r + j * 2) - b ≠ 0 := fun h => hv (by grind)
  rw [cprobeW]; simp [hd, slotV, slotRd, hv, ne, hk]

theorem cprobeW_nextM (j' d' : Word) (hd : d < n) (hv : ¬ rdW sl (r + j * 2) ≤ b)
    (he : ex = false) (hm : mt (rdW sl (r + j * 2) - b - 1) = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    cprobeW sl mt ex q b n r j d = cprobeW sl mt ex q b n r j' d' := by
  subst hj' hd'
  have ne : rdW sl (r + j * 2) - b ≠ 0 := fun h => hv (by grind)
  rw [cprobeW]; simp [hd, slotV, slotRd, hv, ne, he, hm]

theorem cprobeW_end (hd : ¬ d < n) : cprobeW sl mt ex q b n r j d = [] := by
  rw [cprobeW]; simp only [hd, ↓reduceIte]

end probeArms

grind_pattern [arena_grind] cprobeW_free => cprobeW sl mt ex q b n r j d, rdW sl (r + j * 2)
grind_pattern [arena_grind] cprobeW_hitX =>
  cprobeW sl mt ex q b n r j d, rdW sl (r + j * 2), rdW sl (r + j * 2 + 1)
grind_pattern [arena_grind] cprobeW_hitM =>
  cprobeW sl mt ex q b n r j d, rdW sl (r + j * 2), rdW sl (r + j * 2 + 1)
grind_pattern [arena_grind] cprobeW_nextK =>
  cprobeW sl mt ex q b n r j d, rdW sl (r + j * 2 + 1), cprobeW sl mt ex q b n r j' d'
grind_pattern [arena_grind] cprobeW_nextM =>
  cprobeW sl mt ex q b n r j d, rdW sl (r + j * 2), cprobeW sl mt ex q b n r j' d'
grind_pattern [arena_grind] cprobeW_end => cprobeW sl mt ex q b n r j d

/-- The key word of a query `ks` with hash `h` (`kwE`): an exact table's key packed into a word,
else the hash. -/
def kwQ (C : ConsSch) (ks : List Word) (h : Word) : Word :=
  if C.exact then
    match C.nk with
    | 0 => 0
    | 1 => ks.getD 0 0
    | _ => ks.getD 0 0 ||| ks.getD 1 0 <<< 32
  else h

/-- The key words an exact table's key word packs (`khashB`'s unpacking). -/
def unpackK : Nat → Word → List Word
  | 0, _ => []
  | 1, q => [q]
  | _, q => [q &&& 4294967295, q >>> 32]

/-- **The growth's hash of a key word** (`khashB`): the key word itself (a fingerprint), or the
key's hash of the key unpacked from it (exact). -/
def ghC (C : ConsSch) (m : Mem) (q : Word) : Word :=
  if C.exact then C.qhM m (unpackK C.nk q) else q

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

/-- **The key's hash, spliced at `o`** (`ihashAt`, the push's and the growth's recomputation):
it sets `o + nk` to `qhM` of the key words `o ‥ o + nk - 1` and changes nothing else. -/
def IHashAtOK (o : Nat) : Prop :=
  ∀ (n : Nat) (s₀ : St),
    ⦃fun s => s = s₀⦄
    step p (exec p n) (ihashAt C o)
    ⦃fun r s' => r = .normal ∧ s' = s₀.setLoc (o + C.nk) (C.qhM s₀.mem (argsOf o C.nk s₀)); ⊤⦄

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
  ihash : IHashOK p C
  /-- The push (a fingerprint table without a stored hash) and the growth (an exact table) run
  `ihash` at `gO + 14`. -/
  ihashG : C.exact = true ∨ C.np = C.nk → IHashAtOK p C (gO C + 14)
  /-- A fingerprint table without a stored hash reruns `ihash` after the record is written: its
  hash reads no memory. -/
  qpure : C.exact = false → C.np = C.nk → ∀ m m' ks, C.qhM m ks = C.qhM m' ks
  pre : PreOK p C
  colA : ∀ A, C.col = some A → A ≠ C.sa ∧ A ≠ CTL ∧ A ≠ C.ra
  recs : CRecOK C
  room : RoomOK C
  skips : SkipOK C
  push_np : C.nk ≤ C.np ∧ C.np ≤ 1 + C.nk
  arrs : C.ra ≠ CTL ∧ C.sa ≠ CTL ∧ C.ra ≠ C.sa
  /-- The match's prelude has a local of its own (the find's key word follows it). -/
  mloc : C.mpre ≠ none → 1 ≤ C.mloc
  /-- An exact key has at most two words. -/
  exnk : C.exact = true → C.nk ≤ 2

end obligations

theorem ConsOK.room_eq {p : Prog} {C : ConsSch} (hO : ConsOK p C) (s : St) :
    Cond.pval s C.room = C.roomM s.mem (s.loc 0) (s.loc (2 + C.np)) := hO.room s

/-! ## `X_find`: the probe -/

/-- The find's probe from its state `s` (the loop's variables). -/
abbrev fprobe (C : ConsSch) (s : St) : List Word :=
  cprobeW (s.mem.arr64 C.sa) (C.mtM s.mem (fkeys C s) (s.loc 0)) C.exact
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

set_option maxHeartbeats 2000000 in
theorem cfLoop_spec (p : Prog) (C : ConsSch) (hM : CMatchOK p C) (hml : C.mpre ≠ none → 1 ≤ C.mloc)
    (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsOf 1 C.nk s₀)⦄
    exec p n (cfLoop C)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (fprobe C s₀) = fprobe C s₀; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := cfLoop C) rfl]
    unfold CMatchOK at hM
    cases hx : C.exact with
    | true =>
      simp only [kfLoad, kfKey, kfMatch, cfHit, cfAdv, condOf, hx, ↓reduceIte, List.map,
        mapS, mapE, mapC, lvF, fvF, L.Notation.blk, Nat.reduceLT, Nat.reduceEqDiff]
      vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, ih]
      all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 4 (by decide),
        argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide),
        argsOf_setLoc_add 1 C.nk 5 (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc, addc_eq_addc,
        lit_eq_addc, ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
      all_goals grind [lang_grind, arena_grind]
    | false =>
    cases hm : C.mpre with
    | none =>
      simp only [hm] at hM
      simp only [kfLoad, kfKey, kfMatch, cfHit, cfAdv, condOf, hx, Bool.false_eq_true,
        ↓reduceIte, seqs, seqO, hm, List.map, mapS, mapE, mapC, lvF, fvF, L.Notation.blk, Nat.reduceLT, Nat.reduceEqDiff]
      vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, ih]
      all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval, hM,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 4 (by decide),
        argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide),
        argsOf_setLoc_add 1 C.nk 5 (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc, addc_eq_addc,
        lit_eq_addc, ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
      all_goals grind [lang_grind, arena_grind]
    | some b =>
      have hml := hml (by simp [hm])
      simp only [hm] at hM
      simp only [kfLoad, kfKey, kfMatch, cfHit, cfAdv, condOf, hx, Bool.false_eq_true,
        ↓reduceIte, seqs, seqO, hm, List.map, mapS, mapE, mapC, lvF, fvF, L.Notation.blk, Nat.reduceLT, Nat.reduceEqDiff]
      vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, hM n, ih]
      all_goals (try simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 4 (by decide),
        argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide),
        argsOf_setLoc_add 1 C.nk 5 (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc, addc_eq_addc,
        lit_eq_addc, ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
      all_goals grind [lang_grind, arena_grind]

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
      simp [Expr.pval, argsOf, BinOp.eval, List.getD_eq_getElem?_getD, List.getElem?_range, h0, h1]

/-- **`X_find(t, k, h)`** returns the probe of tier `t` from the home slot of `h` (for any
argument list: `t`, the key, `h` and the initial step count are its words `0`, `1 ‥ nk`,
`nk + 1`, `nk + 4`). -/
theorem consFindG_specV (p : Prog) (C : ConsSch) (hM : CMatchOK p C)
    (hml : C.mpre ≠ none → 1 ≤ C.mloc)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀ ∧ C.keyOK s₀.mem (argsL 1 C.nk vs)⦄
    invoke p (exec p n) C.fname vs
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (argsL 1 (C.nk + 1) vs) (Locals.init vs 0))
        C.exact (kwQ C (argsL 1 C.nk vs) (Locals.init vs (1 + C.nk)))
        (baseW s₀.mem (Locals.init vs 0)) (knW C.sa s₀.mem (Locals.init vs 0))
        (krW C.sa s₀.mem (Locals.init vs 0))
        (homeW (Locals.init vs (1 + C.nk)) (knW C.sa s₀.mem (Locals.init vs 0)))
        (Locals.init vs (4 + C.nk)); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, consFindG, kfHead, seqs, List.map, mapS, mapE, mapC, fvF, L.Notation.blk,
    Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, cfLoop_step_spec p C hM hml n]
    all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add1 1 C.nk 2 (by decide),
        argsOf_setLoc_add 1 C.nk 2 (by decide), argsOf_setLoc_add1 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 6 (by decide),
        argsOf_setLoc_add 1 C.nk 6 (by decide), argsOf_setLoc_addc 1 C.nk 7 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 7 C.mloc (by decide), argsOf_setLoc_addc 1 C.nk 8 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 8 C.mloc (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc, addc_eq_addc,
        lit_eq_addc, kwE_pval,
        zero_ne_add 2 C.nk (by decide), zero_ne_add 3 C.nk (by decide),
        zero_ne_add 4 C.nk (by decide), zero_ne_add 6 C.nk (by decide), argsOf_mk,
        ↓reduceIte, Nat.add_eq_zero_iff, false_and, and_false] at *)
    all_goals grind [lang_grind, arena_grind, knW, koW, krW, homeW, baseW]

/-- `X_find(t, k, h)` at a key of `nk` words. -/
theorem consFindG_spec (p : Prog) (C : ConsSch) (hM : CMatchOK p C)
    (hml : C.mpre ≠ none → 1 ≤ C.mloc)
    (hp : p.lookup C.fname = some (consFindG C)) (n : Nat) (s₀ : St) (t : Word) (ks : List Word)
    (hks : ks.length = C.nk) (h : Word) (hk : C.keyOK s₀.mem ks) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.fname (t :: (ks ++ [h]))
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = cprobeW (s₀.mem.arr64 C.sa) (C.mtM s₀.mem (ks ++ [h]) t) C.exact (kwQ C ks h)
        (baseW s₀.mem t) (knW C.sa s₀.mem t) (krW C.sa s₀.mem t) (homeW h (knW C.sa s₀.mem t)) 0; ⊤⦄ := by
  have ek := argsL_key t h ks C.nk hks
  have ek' := argsL_app t ks [h] C.nk hks
  have eh := init_last t ks h C.nk hks
  have ez := init_past2 t ks h C.nk 4 hks (by decide)
  vcgen [consFindG_specV p C hM hml hp n s₀]
  all_goals simp_all [Locals.init_cons_zero]

/-! ## The growth block

`kgrowBlk C` (`kgrowB` with its variables renamed by `gmap`): its loops' specs, then the block's,
against `SlotGrowSpec.lean`'s models. Variables (`gO` + …): `n2` 0, `n` 1, `H` 2, `Q` 3, `ob` 4,
`nb` 5, `x` 6, `e` 7, `v` 8, `q` 9, `h` 10, `j` 11, `d` 12, `bt` 13, the `ihash` block from 14. -/

theorem gmap_lit (C : ConsSch) (k : Nat) (h : k ≠ 0) : gmap C k = gO C + (k - 1) := by
  simp [gmap, h]

theorem gmap_zero (C : ConsSch) : gmap C 0 = 0 := rfl

theorem zero_eq_addlit (a k : Nat) (h : 0 < k) : (0 = a + k) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem addlit_eq_zero (a k : Nat) (h : 0 < k) : (a + k = 0) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem self_eq_addlit (a k : Nat) (h : 0 < k) : (a = a + k) = False := by
  simp only [eq_iff_iff, iff_false]; omega

theorem addlit_eq_self (a k : Nat) (h : 0 < k) : (a + k = a) = False := by
  simp only [eq_iff_iff, iff_false]; omega

section zero
variable (sa : ArrId) (x e : Word) (m : Mem)

theorem kzeroW_done (h : e = 0) : kzeroW sa x e.toNat m = m := by
  subst h; rfl

theorem kzeroW_step (h : ¬ e = 0) :
    kzeroW sa x e.toNat m = kzeroW sa (x + 8) (e - 1).toNat ((((((((m.set64 sa x 0).set64 sa (x + 1) 0).set64 sa
      (x + 2) 0).set64 sa (x + 3) 0).set64 sa (x + 4) 0).set64 sa (x + 5) 0).set64 sa (x + 6) 0).set64
      sa (x + 7) 0) := by
  have h1 : e.toNat = (e - 1).toNat + 1 := by
    have : e.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [h1]; rfl

end zero

grind_pattern [arena_grind] kzeroW_done => kzeroW sa x e.toNat m
grind_pattern [arena_grind] kzeroW_step => kzeroW sa x e.toNat m

theorem kzeroL_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kzeroL C))
    ⦃fun r s' => r = .normal ∧ Keep2 (gO C + 6) (gO C + 7) s₀ s' ∧
      s'.mem = kzeroW C.sa (s₀.loc (gO C + 6)) (s₀.loc (gO C + 7)).toNat s₀.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kzeroL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, st64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.reduceEqDiff,
    bne_iff_ne, ne_eq, rd64_rdWC, self_eq_addlit, addlit_eq_self, zero_eq_addlit, addlit_eq_zero,
    ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep2]

theorem kzeroL_step_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kzeroL C))
    ⦃fun r s' => r = .normal ∧ Keep2 (gO C + 6) (gO C + 7) s₀ s' ∧
      s'.mem = kzeroW C.sa (s₀.loc (gO C + 6)) (s₀.loc (gO C + 7)).toNat s₀.mem; ⊤⦄ :=
  Triple.step_exec (kzeroL_spec p C (n + 1) s₀)

theorem kprobeW_free (sl : Array Word) (nb n j d : Word) (hv : rdW sl (nb + j * 2) = 0) :
    kprobeW sl nb n j d = some j := by
  rw [kprobeW]; simp [hv]

theorem kprobeW_next (sl : Array Word) (nb n j d : Word) (hv : ¬ rdW sl (nb + j * 2) = 0)
    (hd : ¬ n ≤ d) :
    kprobeW sl nb n j d = kprobeW sl nb n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1) := by
  rw [kprobeW]; simp [hv, hd]

grind_pattern [arena_grind] kprobeW_free => kprobeW sl nb n j d, rdW sl (nb + j * 2)
grind_pattern [arena_grind] kprobeW_next => kprobeW sl nb n j d, rdW sl (nb + j * 2)

theorem kprobeL_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kprobeL C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 11) (gO C + 12) s₀ s' ∧
      kprobeW (s₀.mem.arr64 C.sa) (s₀.loc (gO C + 5)) (s₀.loc (gO C)) (s₀.loc (gO C + 11))
        (s₀.loc (gO C + 12)) = some (s'.loc (gO C + 11)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kprobeL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, Nat.reduceSub, Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.reduceEqDiff,
    bne_iff_ne, ne_eq, rd64_rdWC, self_eq_addlit, addlit_eq_self, zero_eq_addlit, addlit_eq_zero,
    ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep2]

theorem kprobeL_step_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kprobeL C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 11) (gO C + 12) s₀ s' ∧
      kprobeW (s₀.mem.arr64 C.sa) (s₀.loc (gO C + 5)) (s₀.loc (gO C)) (s₀.loc (gO C + 11))
        (s₀.loc (gO C + 12)) = some (s'.loc (gO C + 11)); ⊤⦄ :=
  Triple.step_exec (kprobeL_spec p C (n + 1) s₀)

theorem mapE_shiftE (f : Var → Var) (o o' : Nat) (hf : ∀ x, f (x + o) = x + o') :
    ∀ e, mapE f (shiftE o e) = shiftE o' e
  | .const _ => rfl
  | .var x => by simp [mapE, shiftE, hf]
  | .bin op a b => by simp [mapE, shiftE, mapE_shiftE f o o' hf a, mapE_shiftE f o o' hf b]
  | .ld8 a i => by simp [mapE, shiftE, mapE_shiftE f o o' hf i]
  | .ld64 a i => by simp [mapE, shiftE, mapE_shiftE f o o' hf i]
  | .len8 _ => rfl
  | .len64 _ => rfl
  | .cmpw c a b => by simp [mapE, shiftE, mapE_shiftE f o o' hf a, mapE_shiftE f o o' hf b]
  | .ldc d i => by simp [mapE, shiftE, mapE_shiftE f o o' hf i]
  | .glob _ => rfl

theorem mapC_shiftC (f : Var → Var) (o o' : Nat) (hf : ∀ x, f (x + o) = x + o') :
    ∀ c, mapC f (shiftC o c) = shiftC o' c
  | .cmp c a b => by simp [mapC, shiftC, mapE_shiftE f o o' hf]
  | .and p q => by simp [mapC, shiftC, mapC_shiftC f o o' hf p, mapC_shiftC f o o' hf q]
  | .or p q => by simp [mapC, shiftC, mapC_shiftC f o o' hf p, mapC_shiftC f o o' hf q]
  | .not p => by simp [mapC, shiftC, mapC_shiftC f o o' hf p]

/-- A renaming after a shift is a shift. -/
theorem mapS_shiftS (f : Var → Var) (o o' : Nat) (hf : ∀ x, f (x + o) = x + o') :
    ∀ s, mapS f (shiftS o s) = shiftS o' s
  | .skip => rfl
  | .set x e => by simp [mapS, shiftS, hf, mapE_shiftE f o o' hf]
  | .st8 a i e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .st64 a i e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .seq s t => by simp [mapS, shiftS, mapS_shiftS f o o' hf s, mapS_shiftS f o o' hf t]
  | .ite c s t => by
    simp [mapS, shiftS, mapC_shiftC f o o' hf, mapS_shiftS f o o' hf s, mapS_shiftS f o o' hf t]
  | .while c s => by simp [mapS, shiftS, mapC_shiftC f o o' hf, mapS_shiftS f o o' hf s]
  | .brk => rfl
  | .ret es => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .call xs g args => by simp [mapS, shiftS, mapE_shiftE f o o' hf, hf]
  | .abort => rfl
  | .gset g e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]

theorem argsOf_zero (o : Nat) (s : St) : argsOf o 0 s = [] := rfl
theorem argsOf_one (o : Nat) (s : St) : argsOf o 1 s = [s.loc o] := by simp [argsOf]
theorem argsOf_two (o : Nat) (s : St) : argsOf o 2 s = [s.loc o, s.loc (o + 1)] := by
  simp [argsOf, List.range_succ, Nat.add_comm]

theorem mapS_seqs (f : Var → Var) (t : Stmt) :
    ∀ l : List Stmt, mapS f (seqs l t) = seqs (l.map (mapS f)) (mapS f t)
  | [] => rfl
  | s :: l => by simp [seqs, mapS, mapS_seqs f t l]

theorem gmap_ihash (C : ConsSch) : mapS (gmap C) (ihashAt C 15) = ihashAt C (gO C + 14) :=
  mapS_shiftS _ 15 (gO C + 14) (fun x => by
    have h1 : ∀ y : Nat, y + 15 ≠ 0 := fun y => by omega
    have h2 : ∀ y : Nat, y + 15 - 1 = y + 14 := fun y => by omega
    simp only [gmap, h1, ite_false]; rw [h2]; ac_rfl) C.ihash

/-- **The growth's hash** (`khashB`, renamed): `h` (`gO + 10`) becomes `ghC` of the key word `q`
(`gO + 9`); the variables below `gO + 14` but `h` are kept. -/
theorem khash_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (khashB C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      (∀ z, z < gO C + 14 → z ≠ gO C + 10 → s'.loc z = s₀.loc z) ∧
      s'.loc (gO C + 10) = ghC C s₀.mem (s₀.loc (gO C + 9)); ⊤⦄ := by
  unfold khashB
  cases hx : C.exact with
  | false =>
    simp (disch := decide) only [Bool.false_eq_true, ↓reduceIte, mapS, mapE, gmap_lit, Nat.reduceSub]
    vcgen [step, evalE_spec, setLoc]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval] at *)
    all_goals grind [ghC]
  | true =>
    have hnk := hO.exnk hx
    have hI := hO.ihashG (.inl hx)
    simp only [↓reduceIte, mapS_seqs, mapS, gmap_ihash]
    rcases (by omega : C.nk = 0 ∨ C.nk = 1 ∨ C.nk = 2) with hn | hn | hn
    · simp (disch := decide) only [hn, seqs, List.map, mapS, mapE, gmap_lit, Nat.reduceSub,
        Nat.add_zero]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_zero, argsOf_one, argsOf_two, St.setLoc_loc, St.setLoc_mem] at *)
      all_goals grind
    · simp (disch := decide) only [hn, seqs, List.map, mapS, mapE, gmap_lit, Nat.reduceSub]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_zero, argsOf_one, argsOf_two, St.setLoc_loc, St.setLoc_mem] at *)
      all_goals grind
    · simp (disch := decide) only [hn, seqs, List.map, mapS, mapE, gmap_lit, Nat.reduceSub]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, BinOp.eval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_zero, argsOf_one, argsOf_two, St.setLoc_loc, St.setLoc_mem] at *)
      all_goals grind

section walk
variable (sa : ArrId) (G : Mem → Word → Word) (n nb bt e x : Word) (m : Mem)

theorem kwalkW_done (h : e = 0) : kwalkW sa G n nb bt e.toNat x m = some m := by
  subst h; rfl

theorem toNat_pred (h : ¬ e = 0) : e.toNat = (e - 1).toNat + 1 := by
  have : e.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

theorem kwalkW_dead (h : ¬ e = 0) (hv : ¬ bt < rdW (m.arr64 sa) x) :
    kwalkW sa G n nb bt e.toNat x m = kwalkW sa G n nb bt (e - 1).toNat (x + 2) m := by
  rw [toNat_pred e h, kwalkW]; simp [hv]

theorem kwalkW_live (h : ¬ e = 0) (hv : bt < rdW (m.arr64 sa) x)
    (hs : (kprobeW (m.arr64 sa) nb n (homeW (G m (rdW (m.arr64 sa) (x + 1))) n) 0).isSome) :
    kwalkW sa G n nb bt e.toNat x m = kwalkW sa G n nb bt (e - 1).toNat (x + 2)
      ((m.set64 sa (nb + (kprobeW (m.arr64 sa) nb n (homeW (G m (rdW (m.arr64 sa) (x + 1))) n) 0).getD 0 * 2)
        (rdW (m.arr64 sa) x)).set64 sa
        (nb + (kprobeW (m.arr64 sa) nb n (homeW (G m (rdW (m.arr64 sa) (x + 1))) n) 0).getD 0 * 2 + 1)
        (rdW (m.arr64 sa) (x + 1))) := by
  rw [toNat_pred e h, kwalkW]
  cases hj : kprobeW (m.arr64 sa) nb n (homeW (G m (rdW (m.arr64 sa) (x + 1))) n) 0 <;> simp_all

end walk

grind_pattern [arena_grind] kwalkW_done => kwalkW sa G n nb bt e.toNat x m
grind_pattern [arena_grind] kwalkW_dead => kwalkW sa G n nb bt e.toNat x m, rdW (m.arr64 sa) x
grind_pattern [arena_grind] kwalkW_live =>
  kwalkW sa G n nb bt e.toNat x m, kprobeW (m.arr64 sa) nb n (homeW (G m (rdW (m.arr64 sa) (x + 1))) n) 0

theorem homeW_eq (h n : Word) :
    UInt64.ofNat (((h * golden) ^^^ ((h * golden) >>> 32)).toNat * n.toNat / 2 ^ 64) = homeW h n :=
  rfl

theorem kwalkL_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kwalkL C))
    ⦃fun r s' => r = .normal ∧ KeepLo (gO C) s₀ s' ∧
      kwalkW C.sa (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 5)) (s₀.loc (gO C + 13))
        (s₀.loc (gO C + 7)).toNat (s₀.loc (gO C + 6)) s₀.mem = some s'.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kwalkL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, Nat.reduceSub, Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, st64, ih, khash_spec p C hO n,
    kprobeL_step_spec p C n]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.reduceEqDiff,
    bne_iff_ne, ne_eq, rd64_rdWC, self_eq_addlit, addlit_eq_self, zero_eq_addlit, addlit_eq_zero,
    homeW_eq, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep2, KeepLo]

theorem kwalkL_step_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kwalkL C))
    ⦃fun r s' => r = .normal ∧ KeepLo (gO C) s₀ s' ∧
      kwalkW C.sa (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 5)) (s₀.loc (gO C + 13))
        (s₀.loc (gO C + 7)).toNat (s₀.loc (gO C + 6)) s₀.mem = some s'.mem; ⊤⦄ :=
  Triple.step_exec (kwalkL_spec p C hO (n + 1) s₀)

#exit
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
  sorry -- KSTP: proof pending
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
  sorry -- KSTP: proof pending
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
  sorry -- KSTP: proof pending

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
  sorry -- KSTP: proof pending
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

/-! ## The memory outside the slot array -/

theorem arr64_size_set64 (m : Mem) (a b : ArrId) (i v : Word) :
    ((m.set64 a i v).arr64 b).size = (m.arr64 b).size := by
  by_cases e : b = a
  · subst e; exact Mem.size_arr64_set64 m b i v
  · rw [Mem.arr64_set64_ne _ _ _ _ _ e]

theorem wrRecK_size (ra : ArrId) (k : Word) (b : ArrId) :
    ∀ (vs : List Word) (m : Mem) (f : Word), ((wrRecK ra k m f vs).arr64 b).size = (m.arr64 b).size := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih => intro m f; rw [wrRecK, ih, arr64_size_set64]

theorem wrRecK_words (ra : ArrId) (k : Word) :
    ∀ (vs : List Word) (m : Mem) (f : Word), (wrRecK ra k m f vs).words.size = m.words.size := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih => intro m f; rw [wrRecK, ih, Mem.words_size_set64]


/-- The memory after the append of the key's node to tier `t`, outside the slot array: the
record, the count, the column. -/
def pushRec (C : ConsSch) (m : Mem) (t : Word) (ks : List Word) : Mem :=
  colW C t (cntC C m t) (C.colM m (pushArgs C ks (C.qhM m ks)))
    ((wrRecK C.ra (cntC C m t * C.st + t * C.w) m 0 (C.vsM (pushArgs C ks (C.qhM m ks)))).set64
      CTL (C.ca + (t &&& 1)) (cntC C m t + 1))

theorem colW_arr (C : ConsSch) (t c x : Word) (m : Mem) (b : ArrId) (hb : C.col ≠ some b) :
    (colW C t c x m).arr64 b = m.arr64 b := by
  unfold colW; split
  · rfl
  · rename_i A hA; exact Mem.arr64_set64_ne _ _ _ _ _ (fun e => hb (e ▸ hA))

theorem colW_size (C : ConsSch) (t c x : Word) (m : Mem) (b : ArrId) :
    ((colW C t c x m).arr64 b).size = (m.arr64 b).size := by
  unfold colW; split
  · rfl
  · exact arr64_size_set64 _ _ _ _ _

theorem colW_words (C : ConsSch) (t c x : Word) (m : Mem) :
    (colW C t c x m).words.size = m.words.size := by
  unfold colW; split
  · rfl
  · exact Mem.words_size_set64 _ _ _ _

theorem arr64_set64_congr {M₁ M₂ : Mem} {a b : ArrId} (h : M₁.arr64 a = M₂.arr64 a)
    (hb : M₁.arr64 b = M₂.arr64 b) (i v : Word) :
    (M₁.set64 a i v).arr64 b = (M₂.set64 a i v).arr64 b := by
  by_cases e : b = a
  · subst e; simp only [Mem.arr64_set64_same, h]
  · simp only [Mem.arr64_set64_ne _ _ _ _ _ e, hb]

/-- Two memories agree outside array `sa`. -/
def OutSa (sa : ArrId) (M₁ M₂ : Mem) : Prop := ∀ b, b ≠ sa → M₁.arr64 b = M₂.arr64 b

theorem OutSa.set64 {sa : ArrId} {M₁ M₂ : Mem} (h : OutSa sa M₁ M₂) {a : ArrId} (ha : a ≠ sa)
    (i v : Word) : OutSa sa (M₁.set64 a i v) (M₂.set64 a i v) :=
  fun b hb => arr64_set64_congr (h a ha) (h b hb) i v

theorem OutSa.set64_sa {sa : ArrId} {M₁ M₂ : Mem} (h : OutSa sa M₁ M₂) (i v : Word) :
    OutSa sa (M₁.set64 sa i v) M₂ :=
  fun b hb => (Mem.arr64_set64_ne _ _ _ _ _ hb).trans (h b hb)

theorem OutSa.colW (C : ConsSch) (hcol : ∀ A, C.col = some A → A ≠ C.sa) {M₁ M₂ : Mem} (h : OutSa C.sa M₁ M₂) (t c x : Word) :
    OutSa C.sa (colW C t c x M₁) (colW C t c x M₂) := by
  unfold L.Arena.colW; split
  · exact h
  · rename_i A hA; exact h.set64 (hcol A hA) _ _

/-- **An interning hits** (the memory is unchanged) **or appends** node `cntC` to tier `t`: the
handle is the tier's base plus the count, and outside the slot array the memory is `pushRec`. -/
theorem consInternM_outA {C : ConsSch} {m : Mem} (hsc : C.sa ≠ CTL)
    (hcol : ∀ A, C.col = some A → A ≠ C.sa) {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) :
    m' = m ∨ ∃ t, t ≤ 1 ∧ pushOKC C m t = true ∧ w = (if t = 0 then C.P else C.S) + cntC C m t ∧
      (∀ b, b ≠ C.sa → m'.arr64 b = (pushRec C m t ks).arr64 b) ∧
      (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size := by
  rcases consInternM_cases h with e | ⟨t, j, ht, hok, hg, hr⟩
  · exact .inl e
  refine .inr ⟨t, ht, hok, hr, ?_⟩
  obtain ⟨g1, g2, g3⟩ := growIf_frame _ _ _ _ _ _ _ hg
  refine ⟨fun b hb => ?_, fun b => ?_, ?_⟩
  · rw [g1 b hb]
    simp only [pushMX, pushMC, tailM, pushRec]
    refine OutSa.colW C hcol (fun b hb => ?_) _ _ _ b hb
    refine OutSa.set64 (fun b hb => ?_) hsc.symm _ _ b hb
    exact OutSa.set64_sa (fun _ _ => rfl) _ _ b hb
  · rw [g2 b]
    simp only [pushMX, pushMC, tailM, colW_size, arr64_size_set64, wrRecK_size]
  · rw [g3]
    simp only [pushMX, pushMC, tailM, colW_words, Mem.words_size_set64, wrRecK_words]



-- The model is opaque outside the library: users read it through the lemmas above and in
-- `ConsLibRel.lean`.
attribute [irreducible] consInternM

end L.Arena
