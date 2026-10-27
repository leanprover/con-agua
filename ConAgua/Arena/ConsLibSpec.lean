module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
public import ConAgua.Arena.ConsLib
public import ConAgua.Arena.SlotGrowSpec
public import ConAgua.L.PureEval
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

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
  /-- The arrays are tier-0 ids (tier 1 is `+ 256`). -/
  lt : C.ra < 256 ∧ C.sa < 256 ∧ ∀ A, C.col = some A → A < 256
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
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 4 (by decide),
        argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide),
        argsOf_setLoc_add 1 C.nk 5 (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc,
        lit_eq_addc, ↓reduceIte] at *)
      all_goals grind [lang_grind, arena_grind]
    | false =>
    cases hm : C.mpre with
    | none =>
      simp only [hm] at hM
      simp only [kfLoad, kfKey, kfMatch, cfHit, cfAdv, condOf, hx, Bool.false_eq_true,
        ↓reduceIte, seqO, hm, List.map, mapS, mapE, mapC, lvF, fvF, L.Notation.blk, Nat.reduceLT, Nat.reduceEqDiff]
      vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, ih]
      all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval, hM,
        Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
        Nat.reduceEqDiff, rd64_rdWC, zero_ne_add, argsOf_setLoc_add1 1 C.nk 3 (by decide),
        argsOf_setLoc_add 1 C.nk 3 (by decide), argsOf_setLoc_add1 1 C.nk 4 (by decide),
        argsOf_setLoc_add 1 C.nk 4 (by decide), argsOf_setLoc_add1 1 C.nk 5 (by decide),
        argsOf_setLoc_add 1 C.nk 5 (by decide), argsOf_setLoc_addc 1 C.nk 9 C.mloc (by decide),
        argsOf_setLoc_addc0 1 C.nk 9 C.mloc (by decide), addc_eq_add, add_eq_addc,
        lit_eq_addc, ↓reduceIte] at *)
      all_goals grind [lang_grind, arena_grind]
    | some b =>
      have hml := hml (by simp [hm])
      simp only [hm] at hM
      simp only [kfLoad, kfKey, kfMatch, cfHit, cfAdv, condOf, hx, Bool.false_eq_true,
        ↓reduceIte, seqO, hm, List.map, mapS, mapE, mapC, lvF, fvF, L.Notation.blk, Nat.reduceLT, Nat.reduceEqDiff]
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

/-- **The zero loop**, renamed by `f` (its tier at `a`, `x` at `xv`, `e` at `ev`). -/
theorem kzeroLs_spec (p : Prog) (sa : ArrId) (f : Var → Var) (a xv ev : Var) (h0 : f 0 = a)
    (h7 : f 7 = xv) (h8 : f 8 = ev) (hax : a ≠ xv) (hae : a ≠ ev) (hxe : xv ≠ ev) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS f (kzeroLs sa))
    ⦃fun r s' => r = .normal ∧ Keep2 xv ev s₀ s' ∧
      s'.mem = kzeroW (tierA sa (s₀.loc a)) (s₀.loc xv) (s₀.loc ev).toNat s₀.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS f (kzeroLs sa)) rfl]
  simp only [mapS, mapE, mapC, h0, h7, h8]
  vcgen [step, evalE_spec, evalC_spec, setLoc, st64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, bne_iff_ne, ne_eq, ↓reduceIte, hax, hae,
    hxe, Ne.symm hxe] at *)
  all_goals grind [lang_grind, arena_grind, Keep2]

theorem kzeroL_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kzeroL C))
    ⦃fun r s' => r = .normal ∧ Keep2 (gO C + 6) (gO C + 7) s₀ s' ∧
      s'.mem = kzeroW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 6)) (s₀.loc (gO C + 7)).toNat s₀.mem; ⊤⦄ :=
  kzeroLs_spec p C.sa (gmap C) 0 (gO C + 6) (gO C + 7) rfl (gmap_lit C 7 (by decide))
    (gmap_lit C 8 (by decide)) (show (0 : Nat) ≠ gO C + 6 by simp only [gO]; omega)
    (show (0 : Nat) ≠ gO C + 7 by simp only [gO]; omega) (show gO C + 6 ≠ gO C + 7 by omega) n s₀

theorem kzeroL_step_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kzeroL C))
    ⦃fun r s' => r = .normal ∧ Keep2 (gO C + 6) (gO C + 7) s₀ s' ∧
      s'.mem = kzeroW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 6)) (s₀.loc (gO C + 7)).toNat s₀.mem; ⊤⦄ :=
  Triple.step_exec (kzeroL_spec p C (n + 1) s₀)

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
  | .ld64t a t i => by simp [mapE, shiftE, mapE_shiftE f o o' hf t, mapE_shiftE f o o' hf i]
  | .len64t a t => by simp [mapE, shiftE, mapE_shiftE f o o' hf t]
  | .ld8x8 b i => by simp [mapE, shiftE, mapE_shiftE f o o' hf i]

theorem mapW_shiftW (f : Var → Var) (o o' : Nat) (hf : ∀ x, f (x + o) = x + o') :
    ∀ w, mapW f (shiftW o w) = shiftW o' w
  | .plain _ => rfl
  | .tier a t => by simp [mapW, shiftW, mapE_shiftE f o o' hf t]

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
  | .abort e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .gset g e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .st64t a t i e => by simp [mapS, shiftS, mapE_shiftE f o o' hf]
  | .copy64 d di s si n => by simp [mapS, shiftS, mapE_shiftE f o o' hf, mapW_shiftW f o o' hf]
  | .copy8w d di s si n => by simp [mapS, shiftS, mapE_shiftE f o o' hf, mapW_shiftW f o o' hf]
  | .scan8 x s i e c => by simp [mapS, shiftS, mapE_shiftE f o o' hf, hf]

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
    · simp (disch := decide) only [hn, seqs, List.map, mapE, gmap_lit, Nat.reduceSub,
        Nat.add_zero]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_zero] at *)
      all_goals grind
    · simp (disch := decide) only [hn, seqs, List.map, mapS, mapE, gmap_lit, Nat.reduceSub]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_one, St.setLoc_loc] at *)
      all_goals grind
    · simp (disch := decide) only [hn, seqs, List.map, mapS, mapE, gmap_lit, Nat.reduceSub]
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, BinOp.eval, ] at *)
      all_goals (simp only [hn, ghC, hx, ↓reduceIte, unpackK, argsOf_two, St.setLoc_loc] at *)
      all_goals grind

theorem homeW_eq (h n : Word) :
    UInt64.ofNat (((h * golden) ^^^ ((h * golden) >>> 32)).toNat * n.toNat / 2 ^ 64) = homeW h n :=
  rfl

theorem word_toNat_pred (e : Word) (h : ¬ e = 0) : e.toNat = (e - 1).toNat + 1 := by
  have : e.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

theorem self_ne_addlit (a k : Nat) (h : 0 < k) : a ≠ a + k := by omega

theorem addlit_ne_addlit (a i j : Nat) (h : i ≠ j) : a + i ≠ a + j := by omega

theorem lt_ne_addlit (z a k : Nat) (h : z < a) : z ≠ a + k := by omega

theorem zero_lt_gO (C : ConsSch) : 0 < gO C := by simp only [gO]; omega

theorem zero_eq_gO (C : ConsSch) : (0 = gO C) = False := by
  simp only [gO, eq_iff_iff, iff_false]; omega

theorem gO_eq_zero (C : ConsSch) : (gO C = 0) = False := by
  simp only [gO, eq_iff_iff, iff_false]; omega

/-- Sequential composition, with the intermediate assertion `R`. -/
theorem triple_seq {p : Prog} {k : Stmt → M Sig} {a b : Stmt} {s₀ : St} {Q : Sig → St → Prop}
    (R : St → Prop)
    (ha : ⦃fun s => s = s₀⦄ step p k a ⦃fun r s => r = .normal ∧ R s; ⊤⦄)
    (hb : ∀ s₁, R s₁ → ⦃fun s => s = s₁⦄ step p k b ⦃Q; ⊤⦄) :
    ⦃fun s => s = s₀⦄ step p k (.seq a b) ⦃Q; ⊤⦄ := by
  vcgen [step, ha, hb] <;> assumption

/-- A weaker postcondition. -/
theorem triple_weaken {p : Prog} {k : Stmt → M Sig} {a : Stmt} {s₀ : St} {Q Q' : Sig → St → Prop}
    (ha : ⦃fun s => s = s₀⦄ step p k a ⦃Q; ⊤⦄) (h : ∀ r s, Q r s → Q' r s) :
    ⦃fun s => s = s₀⦄ step p k a ⦃Q'; ⊤⦄ := by
  vcgen [ha] <;> grind

/-! ### The mark loop -/

section mark
variable (sa : ArrId) (bt x e : Word) (m : Mem)

theorem kmarkW_done (h : e = 0) : kmarkW sa bt e.toNat x m = m := by
  subst h; rfl

theorem kmarkW_live (h : ¬ e = 0) (hv : bt < rdW (m.arr64 sa) x) :
    kmarkW sa bt e.toNat x m = kmarkW sa bt (e - 1).toNat (x + 2) (m.set64 sa x (rdW (m.arr64 sa) x + MARK)) := by
  rw [word_toNat_pred e h, kmarkW]; simp [hv]

theorem kmarkW_dead (h : ¬ e = 0) (hv : ¬ bt < rdW (m.arr64 sa) x) :
    kmarkW sa bt e.toNat x m = kmarkW sa bt (e - 1).toNat (x + 2) m := by
  rw [word_toNat_pred e h, kmarkW]; simp [hv]

end mark

grind_pattern [arena_grind] kmarkW_done => kmarkW sa bt e.toNat x m
grind_pattern [arena_grind] kmarkW_live => kmarkW sa bt e.toNat x m, rdW (m.arr64 sa) x
grind_pattern [arena_grind] kmarkW_dead => kmarkW sa bt e.toNat x m, rdW (m.arr64 sa) x

/-- Every local but `x`, `y` and `z` is kept. -/
def Keep3 (x y z : Var) (s s' : St) : Prop := ∀ w, w ≠ x → w ≠ y → w ≠ z → s'.loc w = s.loc w

theorem Keep3.loc {x y z : Var} {s s' : St} (h : Keep3 x y z s s') (w : Var) (hx : w ≠ x)
    (hy : w ≠ y) (hz : w ≠ z) : s'.loc w = s.loc w := h w hx hy hz

grind_pattern [lang_grind] Keep3.loc => Keep3 x y z s s', s'.loc w

theorem kmarkL_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kmarkL C))
    ⦃fun r s' => r = .normal ∧ Keep3 (gO C + 6) (gO C + 7) (gO C + 8) s₀ s' ∧
      s'.mem = kmarkW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 7)).toNat
        (s₀.loc (gO C + 6)) s₀.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kmarkL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, st64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.reduceEqDiff,
    bne_iff_ne, ne_eq, rd64_rdWC, zero_eq_addlit,
    ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep3]

theorem kmarkL_step_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kmarkL C))
    ⦃fun r s' => r = .normal ∧ Keep3 (gO C + 6) (gO C + 7) (gO C + 8) s₀ s' ∧
      s'.mem = kmarkW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 7)).toNat
        (s₀.loc (gO C + 6)) s₀.mem; ⊤⦄ :=
  Triple.step_exec (kmarkL_spec p C (n + 1) s₀)

/-! ### The re-insertion's probe -/

theorem kprobeW_stop (sl : Array Word) (ob N i bt j d : Word)
    (hc : ¬ (j ≠ i ∧ bt < rdW sl (ob + j * 2) ∧ rdW sl (ob + j * 2) < MARK)) :
    kprobeW sl ob N i bt j d = some j := by
  rw [kprobeW]; simp only [hc, ↓reduceIte]

theorem kprobeW_next (sl : Array Word) (ob N i bt j d : Word)
    (hc : j ≠ i ∧ bt < rdW sl (ob + j * 2) ∧ rdW sl (ob + j * 2) < MARK) (hd : ¬ N ≤ d) :
    kprobeW sl ob N i bt j d = kprobeW sl ob N i bt ((j + 1) * (if j + 1 < N then 1 else 0)) (d + 1) := by
  rw [kprobeW]; simp only [hc, hd, ne_eq, not_false_eq_true, and_self, ↓reduceIte]

theorem kprobeL_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kprobeL C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 11) (gO C + 12) s₀ s' ∧
      kprobeW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0))) (s₀.loc (gO C + 4)) (s₀.loc (gO C))
        (s₀.loc (gO C + 2)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 11)) (s₀.loc (gO C + 12)) =
        some (s'.loc (gO C + 11)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kprobeL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub, Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.reduceEqDiff,
    bne_iff_ne, ne_eq, rd64_rdWC, self_eq_addlit, zero_eq_addlit,
    Bool.and_eq_true, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep2, kprobeW_stop, kprobeW_next]

theorem kprobeL_step_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kprobeL C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ Keep2 (gO C + 11) (gO C + 12) s₀ s' ∧
      kprobeW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0))) (s₀.loc (gO C + 4)) (s₀.loc (gO C))
        (s₀.loc (gO C + 2)) (s₀.loc (gO C + 13)) (s₀.loc (gO C + 11)) (s₀.loc (gO C + 12)) =
        some (s'.loc (gO C + 11)); ⊤⦄ :=
  Triple.step_exec (kprobeL_spec p C (n + 1) s₀)

/-! ### Taking and placing an entry -/

/-- **Take the marked entry** of slot `H`: the budget `e` was not `0` and drops by one, `v`
unmarked, `q` its key word, `j` the home of its hash in the doubled table, `d = 0`. -/
theorem kpickB_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kpickB C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      (∀ z, z < gO C + 14 → z ≠ gO C + 7 → z ≠ gO C + 8 → z ≠ gO C + 9 → z ≠ gO C + 10 →
        z ≠ gO C + 11 → z ≠ gO C + 12 → s'.loc z = s₀.loc z) ∧
      ¬ s₀.loc (gO C + 7) = 0 ∧ s'.loc (gO C + 7) = s₀.loc (gO C + 7) - 1 ∧
      s'.loc (gO C + 8) = s₀.loc (gO C + 8) - MARK ∧
      s'.loc (gO C + 9) = rdW (s₀.mem.arr64 (tierA C.sa (s₀.loc 0)))
        (s₀.loc (gO C + 4) + s₀.loc (gO C + 2) * 2 + 1) ∧
      s'.loc (gO C + 11) = homeW (ghC C s₀.mem (s'.loc (gO C + 9))) (s₀.loc (gO C)) ∧
      s'.loc (gO C + 12) = 0; ⊤⦄ := by
  unfold kpickB
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub, Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, khash_spec p C hO n]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, beq_iff_eq, rd64_rdWC, zero_eq_addlit, homeW_eq, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, lt_ne_addlit]

/-- **Place the entry** at slot `j` (`kplaceW`): the memory and the next value word `v`. -/
theorem kplaceB_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kplaceB C))
    ⦃fun r s' => r = .normal ∧ Keep3 (gO C + 5) (gO C + 6) (gO C + 8) s₀ s' ∧
      s'.mem = (kplaceW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 4)) (s₀.loc (gO C + 2))
        (s₀.loc (gO C + 11)) (s₀.loc (gO C + 8)) (s₀.loc (gO C + 9)) s₀.mem).1 ∧
      s'.loc (gO C + 8) = (kplaceW (tierA C.sa (s₀.loc 0)) (s₀.loc (gO C + 4)) (s₀.loc (gO C + 2))
        (s₀.loc (gO C + 11)) (s₀.loc (gO C + 8)) (s₀.loc (gO C + 9)) s₀.mem).2; ⊤⦄ := by
  unfold kplaceB
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, st64]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_left_cancel_iff, Nat.reduceEqDiff, beq_iff_eq, rd64_rdWC, zero_eq_addlit, ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, Keep3, kplaceW]

/-! ### The re-insertion loops -/

/-- The variables the re-insertion loops keep: the push's (below `gO`), `n2 n H ob bt`. -/
def KeepR (C : ConsSch) (s s' : St) : Prop :=
  KeepLo (gO C) s s' ∧ s'.loc (gO C) = s.loc (gO C) ∧ s'.loc (gO C + 1) = s.loc (gO C + 1) ∧
    s'.loc (gO C + 4) = s.loc (gO C + 4) ∧ s'.loc (gO C + 13) = s.loc (gO C + 13)

theorem kinnerW_done (sa : ArrId) (G : Mem → Word → Word) (N ob bt i e v : Word) (m : Mem)
    (hv : ¬ MARK ≤ v) : kinnerW sa G N ob bt i e v m = some (m, e) := by
  rw [kinnerW]; simp [hv]

theorem kinnerW_more (sa : ArrId) (G : Mem → Word → Word) (N ob bt i e v : Word) (m : Mem)
    (hv : MARK ≤ v) (he : ¬ e = 0) (j : Word)
    (hj : kprobeW (m.arr64 sa) ob N i bt (homeW (G m (rdW (m.arr64 sa) (ob + i * 2 + 1))) N) 0 = some j) :
    kinnerW sa G N ob bt i e v m =
      kinnerW sa G N ob bt i (e - 1)
        (kplaceW sa ob i j (v - MARK) (rdW (m.arr64 sa) (ob + i * 2 + 1)) m).2
        (kplaceW sa ob i j (v - MARK) (rdW (m.arr64 sa) (ob + i * 2 + 1)) m).1 := by
  rw [kinnerW]; simp only [hv, he, hj, ↓reduceIte]

theorem kinnerL_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (kinnerL C))
    ⦃fun r s' => r = .normal ∧ KeepR C s₀ s' ∧ s'.loc (gO C + 2) = s₀.loc (gO C + 2) ∧
      kinnerW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 7)) (s₀.loc (gO C + 8)) s₀.mem =
        some (s'.mem, s'.loc (gO C + 7)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (kinnerL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit,
    Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, kpickB_spec p C hO n, kprobeL_step_spec p C n,
    kplaceB_spec p C n, ih]
  all_goals (simp (disch := decide) only [Cmp.eval,
    Expr.pval, Cond.pval] at *)
  all_goals grind [lang_grind, arena_grind, KeepR, KeepLo, Keep2, Keep3, kinnerW_done,
    kinnerW_more, lt_ne_addlit]

theorem kinnerL_step_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kinnerL C))
    ⦃fun r s' => r = .normal ∧ KeepR C s₀ s' ∧ s'.loc (gO C + 2) = s₀.loc (gO C + 2) ∧
      kinnerW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 7)) (s₀.loc (gO C + 8)) s₀.mem =
        some (s'.mem, s'.loc (gO C + 7)); ⊤⦄ :=
  Triple.step_exec (kinnerL_spec p C hO (n + 1) s₀)

theorem krehashW_done (sa : ArrId) (G : Mem → Word → Word) (N n ob bt i e : Word) (m : Mem)
    (hi : ¬ i < n) : krehashW sa G N n ob bt i e m = some m := by
  rw [krehashW]; simp [hi]

theorem krehashW_step (sa : ArrId) (G : Mem → Word → Word) (N n ob bt i e : Word) (m m' : Mem)
    (e' : Word) (hi : i < n)
    (h : kinnerW sa G N ob bt i e (rdW (m.arr64 sa) (ob + i * 2)) m = some (m', e')) :
    krehashW sa G N n ob bt i e m = krehashW sa G N n ob bt (i + 1) e' m' := by
  rw [krehashW]; simp [hi, h]

theorem krehashL_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mapS (gmap C) (krehashL C))
    ⦃fun r s' => r = .normal ∧ KeepLo (gO C) s₀ s' ∧
      krehashW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 7)) s₀.mem = some s'.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
  rw [exec, step_while (w := mapS (gmap C) (krehashL C)) rfl]
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero,
    Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64, kinnerL_step_spec p C hO n, ih]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, self_eq_addlit, zero_eq_addlit,
    ↓reduceIte] at *)
  all_goals grind [lang_grind, arena_grind, KeepR, KeepLo, krehashW_done, krehashW_step,
    lt_ne_addlit]

theorem krehashL_step_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (krehashL C))
    ⦃fun r s' => r = .normal ∧ KeepLo (gO C) s₀ s' ∧
      krehashW (tierA C.sa (s₀.loc 0)) (ghC C) (s₀.loc (gO C)) (s₀.loc (gO C + 1)) (s₀.loc (gO C + 4))
        (s₀.loc (gO C + 13)) (s₀.loc (gO C + 2)) (s₀.loc (gO C + 7)) s₀.mem = some s'.mem; ⊤⦄ :=
  Triple.step_exec (krehashL_spec p C hO (n + 1) s₀)

/-! ### The growth block -/

theorem kgrowH1_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kgrowH1 C))
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ KeepLo (gO C) s₀ s' ∧
      s'.loc (gO C) = knW C.sa s₀.mem (s₀.loc 0) * 2 ∧
      s'.loc (gO C + 1) = knW C.sa s₀.mem (s₀.loc 0) ∧
      s'.loc (gO C + 3) = s₀.mem.len64 (tierA C.sa (s₀.loc 0)) - 2 ∧
      s'.loc (gO C + 4) = koW C.sa s₀.mem (s₀.loc 0) + 2 ∧
      s'.loc (gO C + 5) = koW C.sa s₀.mem (s₀.loc 0); ⊤⦄ := by
  unfold kgrowH1
  simp (disch := decide) only [mapS, mapE, gmap_lit, gmap_zero, Nat.reduceSub,
    Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, self_eq_addlit, addlit_eq_self, zero_eq_addlit, zero_eq_gO, ↓reduceIte] at *)
  all_goals grind [lang_grind, KeepLo, knW, koW, lt_ne_addlit]

theorem kgrowH2_spec (p : Prog) (C : ConsSch) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁⦄
    step p (exec p n) (mapS (gmap C) (kgrowH2 C))
    ⦃fun r s' => r = .normal ∧ ¬ s₁.loc (gO C + 3) < s₁.loc (gO C + 5) + s₁.loc (gO C) * 2 ∧
      s'.mem = s₁.mem.set64 (tierA C.sa (s₁.loc 0)) 0 (s₁.loc (gO C) - SN0) ∧ s'.loc = s₁.loc; ⊤⦄ := by
  unfold kgrowH2
  simp (disch := decide) only [mapS, mapE, mapC, gmap_lit, gmap_zero, Nat.reduceSub,
    Nat.add_zero]
  vcgen [step, evalE_spec, evalC_spec, setLoc, st64]
  all_goals (simp (disch := decide) only [BinOp.eval, Cmp.eval,
    Expr.pval, Cond.pval] at *)
  all_goals grind [lang_grind]

theorem kgrowH3_spec (p : Prog) (C : ConsSch) (n : Nat) (s₂ : St) :
    ⦃fun s => s = s₂⦄
    step p (exec p n) (mapS (gmap C) kgrowH3)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₂.mem ∧ Keep2 (gO C + 6) (gO C + 7) s₂ s' ∧
      s'.loc (gO C + 6) = s₂.loc (gO C + 4) + s₂.loc (gO C + 1) * 2 ∧
      s'.loc (gO C + 7) = s₂.loc (gO C + 1) >>> 2; ⊤⦄ := by
  unfold kgrowH3
  simp (disch := decide) only [mapS, mapE, gmap_lit, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ↓reduceIte] at *)
  all_goals grind [lang_grind, Keep2]

theorem kgrowH4_spec (p : Prog) (C : ConsSch) (n : Nat) (s₂ : St) :
    ⦃fun s => s = s₂⦄
    step p (exec p n) (mapS (gmap C) kgrowH4)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₂.mem ∧ Keep3 (gO C + 6) (gO C + 7) (gO C + 13) s₂ s' ∧
      s'.loc (gO C + 13) = rdW (s₂.mem.arr64 CTL) SCB * s₂.loc 0 ∧
      s'.loc (gO C + 6) = s₂.loc (gO C + 4) ∧ s'.loc (gO C + 7) = s₂.loc (gO C + 1); ⊤⦄ := by
  unfold kgrowH4
  simp (disch := decide) only [mapS, mapE, gmap_lit, gmap_zero, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc, ld64]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem, BinOp.eval,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, rd64_rdWC, ↓reduceIte] at *)
  all_goals grind [lang_grind, Keep3]

theorem kgrowH5_spec (p : Prog) (C : ConsSch) (n : Nat) (s₂ : St) :
    ⦃fun s => s = s₂⦄
    step p (exec p n) (mapS (gmap C) kgrowH5)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₂.mem ∧ Keep2 (gO C + 2) (gO C + 7) s₂ s' ∧
      s'.loc (gO C + 2) = 0 ∧ s'.loc (gO C + 7) = s₂.loc (gO C + 1); ⊤⦄ := by
  unfold kgrowH5
  simp (disch := decide) only [mapS, mapE, gmap_lit, Nat.reduceSub]
  vcgen [step, evalE_spec, evalC_spec, setLoc]
  all_goals (simp (disch := decide) only [St.setLoc_loc, St.setLoc_mem,
    Expr.pval, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ↓reduceIte] at *)
  all_goals grind [lang_grind, Keep2]

/-- **The growth's head**: the room check passed, the count word written, `n2 n ob` and the
zero loop's `x e` set. -/
theorem kgrowH_spec (p : Prog) (C : ConsSch) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mapS (gmap C) (kgrowH C))
    ⦃fun r s' => r = .normal ∧ KeepLo (gO C) s₀ s' ∧
      ¬ s₀.mem.len64 (tierA C.sa (s₀.loc 0)) - 2 <
        koW C.sa s₀.mem (s₀.loc 0) + knW C.sa s₀.mem (s₀.loc 0) * 2 * 2 ∧
      s'.mem = s₀.mem.set64 (tierA C.sa (s₀.loc 0)) 0 (knW C.sa s₀.mem (s₀.loc 0) * 2 - SN0) ∧
      s'.loc (gO C) = knW C.sa s₀.mem (s₀.loc 0) * 2 ∧
      s'.loc (gO C + 1) = knW C.sa s₀.mem (s₀.loc 0) ∧
      s'.loc (gO C + 4) = koW C.sa s₀.mem (s₀.loc 0) + 2 ∧
      s'.loc (gO C + 6) = koW C.sa s₀.mem (s₀.loc 0) + 2 + knW C.sa s₀.mem (s₀.loc 0) * 2 ∧
      s'.loc (gO C + 7) = knW C.sa s₀.mem (s₀.loc 0) >>> 2; ⊤⦄ := by
  unfold kgrowH
  simp only [mapS]
  refine triple_seq _ (kgrowH1_spec p C n s₀) (fun s₁ h₁ => ?_)
  obtain ⟨m1, k1, a0, a1, a3, a4, a5⟩ := h₁
  refine triple_seq _ (kgrowH2_spec p C n s₁) (fun s₂ h₂ => ?_)
  obtain ⟨hc, m2, l2⟩ := h₂
  refine triple_weaken (kgrowH3_spec p C n s₂) (fun r s ⟨hr, m3, k3, b6, b7⟩ => ?_)
  have e0 : s₁.loc 0 = s₀.loc 0 := k1 0 (zero_lt_gO C)
  have g : ∀ z, z = gO C ∨ z = gO C + 1 ∨ z = gO C + 4 → s.loc z = s₁.loc z := fun z hz => by
    rcases hz with rfl | rfl | rfl
    · rw [k3 _ (self_ne_addlit _ _ (by decide)) (self_ne_addlit _ _ (by decide)), l2]
    all_goals rw [k3 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)), l2]
  refine ⟨hr, fun z hz => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k3 z (lt_ne_addlit _ _ _ hz) (lt_ne_addlit _ _ _ hz), l2, k1 z hz]
  · rw [a3, a5, a0] at hc; exact hc
  · rw [m3, m2, m1, e0, a0]
  · rw [g _ (.inl rfl), a0]
  · rw [g _ (.inr (.inl rfl)), a1]
  · rw [g _ (.inr (.inr rfl)), a4]
  · rw [b6, l2, a4, a1]
  · rw [b7, l2, a1]

theorem kzeroW_arr (sa : ArrId) (x : Word) (e : Nat) (m : Mem) (b : ArrId) (hb : b ≠ sa) :
    (kzeroW sa x e m).arr64 b = m.arr64 b := (kzeroW_fr sa e x m).1 b hb

/-- **The growth block** (renamed into the push): it keeps the push's variables (below `gO`) and
leaves `kgrowM`'s memory. -/
theorem kgrowBlk_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (kgrowBlk C)
    ⦃fun r s' => r = .normal ∧ KeepLo (gO C) s₀ s' ∧
      kgrowM C.sa (ghC C) (s₀.loc 0) s₀.mem = some s'.mem; ⊤⦄ := by
  have hsc : ∀ t, tierA C.sa t ≠ CTL := fun t => by
    simpa using tierA_ne hO.lt.2.1 (show CTL < 256 by decide) hO.arrs.2.1 t 0
  unfold kgrowBlk kgrowB
  simp only [mapS]
  refine triple_seq _ (kgrowH_spec p C n s₀) (fun s₃ h₃ => ?_)
  obtain ⟨k3, hc, m3, a0, a1, a4, b6, b7⟩ := h₃
  refine triple_seq _ (kzeroL_step_spec p C n s₃) (fun s₄ h₄ => ?_)
  obtain ⟨k4, m4⟩ := h₄
  refine triple_seq _ (kgrowH4_spec p C n s₄) (fun s₅ h₅ => ?_)
  obtain ⟨m5, k5, c13, c6, c7⟩ := h₅
  refine triple_seq _ (kmarkL_step_spec p C n s₅) (fun s₆ h₆ => ?_)
  obtain ⟨k6, m6⟩ := h₆
  refine triple_seq _ (kgrowH5_spec p C n s₆) (fun s₇ h₇ => ?_)
  obtain ⟨m7, k7, d2, d7⟩ := h₇
  refine triple_weaken (krehashL_step_spec p C hO n s₇) (fun r s ⟨hr, k8, hw⟩ => ?_)
  -- the variables, back to `s₀`
  have t0 : ∀ z, z < gO C → s₇.loc z = s₀.loc z := fun z hz => by
    have h1 := lt_ne_addlit z (gO C) 6 hz; have h2 := lt_ne_addlit z (gO C) 7 hz
    have h3 := lt_ne_addlit z (gO C) 8 hz; have h4 := lt_ne_addlit z (gO C) 13 hz
    have h5 := lt_ne_addlit z (gO C) 2 hz
    rw [k7 z h5 h2, k6 z h1 h2 h3, k5 z h1 h2 h4, k4 z h1 h2, k3 z hz]
  have e0 := t0 0 (zero_lt_gO C)
  refine ⟨hr, fun z hz => by rw [k8 z hz, t0 z hz], ?_⟩
  have kk : ∀ z, z = gO C ∨ z = gO C + 1 ∨ z = gO C + 4 → s₇.loc z = s₃.loc z := fun z hz => by
    rcases hz with rfl | rfl | rfl
    · rw [k7 _ (self_ne_addlit _ _ (by decide)) (self_ne_addlit _ _ (by decide)),
        k6 _ (self_ne_addlit _ _ (by decide)) (self_ne_addlit _ _ (by decide)) (self_ne_addlit _ _ (by decide)),
        k5 _ (self_ne_addlit _ _ (by decide)) (self_ne_addlit _ _ (by decide)) (self_ne_addlit _ _ (by decide)),
        k4 _ (self_ne_addlit _ _ (by decide)) (self_ne_addlit _ _ (by decide))]
    all_goals rw [k7 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)),
        k6 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)),
        k5 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)),
        k4 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide))]
  have v0 : s₇.loc (gO C) = knW C.sa s₀.mem (s₀.loc 0) * 2 := by rw [kk _ (.inl rfl), a0]
  have v1 : s₇.loc (gO C + 1) = knW C.sa s₀.mem (s₀.loc 0) := by rw [kk _ (.inr (.inl rfl)), a1]
  have v4 : s₇.loc (gO C + 4) = koW C.sa s₀.mem (s₀.loc 0) + 2 := by rw [kk _ (.inr (.inr rfl)), a4]
  have s40 : s₄.loc 0 = s₀.loc 0 := by
    rw [k4 0 (lt_ne_addlit _ _ _ (zero_lt_gO C)) (lt_ne_addlit _ _ _ (zero_lt_gO C)),
      k3 0 (zero_lt_gO C)]
  have v13 : s₇.loc (gO C + 13) = rdW (s₀.mem.arr64 CTL) SCB * s₀.loc 0 := by
    rw [k7 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)),
      k6 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)),
      c13, m4, kzeroW_arr _ _ _ _ _ (Ne.symm (hsc _)), m3,
      Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (hsc _)), s40]
  have s50 : s₅.loc 0 = s₀.loc 0 := by
    rw [k5 0 (lt_ne_addlit _ _ _ (zero_lt_gO C)) (lt_ne_addlit _ _ _ (zero_lt_gO C))
      (lt_ne_addlit _ _ _ (zero_lt_gO C)), s40]
  have s30 : s₃.loc 0 = s₀.loc 0 := k3 0 (zero_lt_gO C)
  have n4 : s₄.loc (gO C + 1) = knW C.sa s₀.mem (s₀.loc 0) := by
    rw [k4 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)), a1]
  have o4 : s₄.loc (gO C + 4) = koW C.sa s₀.mem (s₀.loc 0) + 2 := by
    rw [k4 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide)), a4]
  have n6 : s₆.loc (gO C + 1) = knW C.sa s₀.mem (s₀.loc 0) := by
    rw [k6 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide))
      (addlit_ne_addlit _ _ _ (by decide)),
      k5 _ (addlit_ne_addlit _ _ _ (by decide)) (addlit_ne_addlit _ _ _ (by decide))
      (addlit_ne_addlit _ _ _ (by decide)), n4]
  have bt5 : s₅.loc (gO C + 13) = rdW (s₀.mem.arr64 CTL) SCB * s₀.loc 0 := by
    rw [c13, m4, kzeroW_arr _ _ _ _ _ (Ne.symm (hsc _)), m3,
      Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (hsc _)), s40]
  rw [d2, d7, n6, v0, v1, v4, v13, e0, m7, m6, s50, bt5, c6, c7, o4, n4, m5, m4, s30, b6, b7, m3] at hw
  rw [kgrowM, ite_eq_right hc]
  exact hw



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

/-- After the record: register node `c` of tier `t` at slot `j` of its table (the value word,
and the key word `q`), count it. -/
def tailM (C : ConsSch) (t j c q : Word) (m : Mem) : Mem :=
  ((m.set64 (tierA C.sa t) (krW C.sa m t + j * 2) (rdW (m.arr64 CTL) SCB * t + c + 1)).set64
    (tierA C.sa t) (krW C.sa m t + j * 2 + 1) q).set64 CTL (C.ca + (t &&& 1)) (c + 1)

/-- **The memory after the append** of node `c` (record `vs`, key word `q`) to tier `t`,
registered at `j`. -/
def pushMC (C : ConsSch) (m : Mem) (t : Word) (vs : List Word) (j c q : Word) : Mem :=
  tailM C t j c q (wrRecK (tierA C.ra t) (c * C.w) m 0 vs)

/-- The derived column's write, `col⟨t⟩[c] := x` (none without a column). -/
def colW (C : ConsSch) (t c x : Word) (m : Mem) : Mem :=
  match C.col with
  | none => m
  | some A => m.set64 (tierA A t) c x

/-- **The memory after the append** with the derived column's word `x`. -/
def pushMX (C : ConsSch) (m : Mem) (t : Word) (vs : List Word) (x j c q : Word) : Mem :=
  colW C t c x (pushMC C m t vs j c q)

theorem pushMX_none {C : ConsSch} (h : C.col = none) (m : Mem) (t : Word) (vs : List Word)
    (x j c q : Word) : pushMX C m t vs x j c q = pushMC C m t vs j c q := by
  simp [pushMX, colW, h]

/-- The growth of tier `t` if node count `c + 1` passes 3/4 of its slot count `g + SN0` (`g` its
count word, read before the push's writes). -/
def growK (C : ConsSch) (t g c : Word) (m : Mem) : Option Mem :=
  if (g + SN0) * 3 < (c + 1) * 4 then kgrowM C.sa (ghC C) t m else some m

/-- **A push's tail**: from the memory `m` after the push's writes, grow tier `t` if node count
`c + 1` passes 3/4 of its slot count in the memory `m₀` before them. -/
def kgrowIf (C : ConsSch) (t : Word) (m₀ m : Mem) (c : Word) : Option Mem :=
  if knW C.sa m₀ t * 3 < (c + 1) * 4 then kgrowM C.sa (ghC C) t m else some m

theorem kgrowIf_growK (C : ConsSch) (t : Word) (m₀ M : Mem) (c : Word) :
    kgrowIf C t m₀ M c = growK C t (rdW (m₀.arr64 (tierA C.sa t)) 0) c M := rfl

/-- The key word a push stores, from its inputs `as` (`cpKey`): the key's hash recomputed (a
fingerprint table without a stored hash), else the key word of the key and the stored hash. -/
def kwP (C : ConsSch) (m : Mem) (as : List Word) : Word :=
  if C.exact then kwQ C as 0
  else if C.nk < C.np then as.getD C.nk 0
  else C.qhM m (as.take C.nk)

theorem kwP_mem (p : Prog) {C : ConsSch} (hO : ConsOK p C) (m m' : Mem) (as : List Word) :
    kwP C m as = kwP C m' as := by
  have hn := hO.push_np
  unfold kwP; split
  · rfl
  · split
    · rfl
    · rename_i hx hlt
      exact hO.qpure (by simpa using hx) (by omega) _ _ _

theorem argsOf_take (base nk np : Nat) (h : nk ≤ np) (s : St) :
    (argsOf base np s).take nk = argsOf base nk s := by
  simp only [argsOf, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem argsOf_getD (base nk np : Nat) (h : nk < np) (s : St) :
    (argsOf base np s).getD nk 0 = s.loc (nk + base) := by
  simp [argsOf, List.getD_eq_getElem?_getD, h]

/-! ### Copying the key words -/

/-- `s` with the words `1 ‥ k` copied to `o ‥ o + k - 1`. -/
def copyS (o : Nat) : Nat → St → St
  | 0, s => s
  | k + 1, s => (copyS o k s).setLoc (o + k) (s.loc (1 + k))

theorem copyS_mem (o k : Nat) (s : St) : (copyS o k s).mem = s.mem := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [copyS, St.setLoc_mem, ih]

theorem copyS_loc (o k : Nat) (s : St) (x : Nat) :
    (copyS o k s).loc x = if o ≤ x ∧ x < o + k then s.loc (x - o + 1) else s.loc x := by
  induction k with
  | zero =>
    simp only [copyS, Nat.add_zero]
    split
    · rename_i h; omega
    · rfl
  | succ k ih =>
    simp only [copyS, St.setLoc_loc, ih]
    by_cases hx : x = o + k
    · subst hx
      simp only [↓reduceIte, show o ≤ o + k ∧ o + k < o + (k + 1) from ⟨by omega, by omega⟩, and_self]
      rw [show o + k - o + 1 = 1 + k by omega]
    · simp only [hx, ↓reduceIte]
      by_cases h1 : o ≤ x ∧ x < o + k
      · simp only [h1, show o ≤ x ∧ x < o + (k + 1) from ⟨h1.1, by omega⟩, and_self, ↓reduceIte]
      · simp only [h1, ↓reduceIte]
        rw [ite_eq_right (fun h => h1 ⟨h.1, by omega⟩)]

theorem seqs_append_one (l : List Stmt) (x t : Stmt) : seqs (l ++ [x]) t = seqs l (.seq x t) := by
  induction l with
  | nil => rfl
  | cons y l ih => simp [seqs, ih]

theorem copies_spec (p : Prog) (n o : Nat) :
    ∀ (k : Nat), k + 1 ≤ o → ∀ (t : Stmt) (s₀ : St) (Q : Sig → St → Prop),
      ⦃fun s => s = copyS o k s₀⦄ step p (exec p n) t ⦃Q; ⊤⦄ →
      ⦃fun s => s = s₀⦄
      step p (exec p n) (seqs ((List.range k).map fun i => .set (o + i) (.var (1 + i))) t) ⦃Q; ⊤⦄
  | 0, _, t, s₀, Q, ht => ht
  | k + 1, hk, t, s₀, Q, ht => by
    rw [List.range_succ, List.map_append, List.map_singleton, seqs_append_one]
    refine copies_spec p n o k (by omega) _ s₀ Q ?_
    refine triple_seq (· = copyS o (k + 1) s₀) ?_ (fun s₁ h₁ => h₁ ▸ ht)
    have e : (copyS o k s₀).loc (1 + k) = s₀.loc (1 + k) := by
      rw [copyS_loc]; rw [ite_eq_right (by omega)]
    vcgen [step, evalE_spec, setLoc]
    rename_i h
    subst h
    simp only [Expr.pval, e]
    rfl

theorem argsOf_copyS (o k : Nat) (_hk : k + 1 ≤ o) (s : St) : argsOf o k (copyS o k s) = argsOf 1 k s := by
  simp only [argsOf]
  apply List.map_congr_left
  intro i hi
  have := List.mem_range.mp hi
  rw [copyS_loc, ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel]

/-! ### The tail -/

/-- The key word the push computes from its state `s` (after the record). -/
abbrev pkw (C : ConsSch) (s : St) : Word := kwP C s.mem (argsOf 1 C.np s)

theorem cpKey_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpKey C)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₁.mem ∧ KeepLo (gO C + 2) s₁ s' ∧
      s'.loc (gO C + 2) = pkw C s₁; ⊤⦄ := by
  have hn := hO.push_np
  unfold cpKey
  cases hx : C.exact with
  | true =>
    simp only [↓reduceIte]
    vcgen [step, evalE_spec, setLoc]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, kwE_pval, kwP, hx, ↓reduceIte, kwQ] at *)
    all_goals grind [lang_grind, KeepLo, argsOf]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : C.nk < C.np
    · simp only [hlt, ↓reduceIte]
      vcgen [step, evalE_spec, setLoc]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval] at *)
      all_goals (simp only [kwP, hx, Bool.false_eq_true, ↓reduceIte, hlt,
        argsOf_getD 1 C.nk C.np hlt] at *)
      all_goals grind [lang_grind, KeepLo]
    · have he : C.np = C.nk := by omega
      simp only [hlt, ↓reduceIte]
      have hI := hO.ihashG (.inr he)
      refine copies_spec p n (gO C + 14) C.nk (by simp [gO]; omega) _ s₁ _ ?_
      vcgen [step, evalE_spec, setLoc, hI n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, Expr.pval, argsOf_copyS _ _
        (show C.nk + 1 ≤ gO C + 14 by simp [gO]; omega)] at *)
      all_goals (simp only [kwP, hx, he, Bool.false_eq_true, Nat.lt_irrefl, ↓reduceIte,
        argsOf_take 1 C.nk C.nk (Nat.le_refl _)] at *)
      all_goals grind [lang_grind, KeepLo, copyS_loc, copyS_mem]

theorem cpRest_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) (s₁ : St)
    (hg : s₁.loc (gO C + 1) = rdW (s₁.mem.arr64 (tierA C.sa (s₁.loc 0))) 0) :
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpRest C)
    ⦃fun r s' => r = .ret [s₁.loc (2 + C.np)] ∧
      growK C (s₁.loc 0) (s₁.loc (gO C + 1)) (s₁.loc (2 + C.np))
        (colW C (s₁.loc 0) (s₁.loc (2 + C.np)) (s₁.loc (4 + C.np))
          (tailM C (s₁.loc 0) (s₁.loc (1 + C.np)) (s₁.loc (2 + C.np)) (pkw C s₁) s₁.mem)) =
        some s'.mem; ⊤⦄ := by
  have hsa := hO.arrs.2.1
  have hgO : 4 + C.np ≤ gO C := by simp only [gO]; omega
  simp only [cpRest, seqs]
  refine triple_seq _ (cpKey_spec p C hO n s₁) (fun s₂ h₂ => ?_)
  obtain ⟨m2, k2, q2⟩ := h₂
  have l0 : s₂.loc 0 = s₁.loc 0 := k2 0 (by omega)
  have l1 : s₂.loc (1 + C.np) = s₁.loc (1 + C.np) := k2 _ (by omega)
  have l2 : s₂.loc (2 + C.np) = s₁.loc (2 + C.np) := k2 _ (by omega)
  have l4 : s₂.loc (4 + C.np) = s₁.loc (4 + C.np) := k2 _ (by omega)
  have lg : s₂.loc (gO C + 1) = s₁.loc (gO C + 1) := k2 _ (by omega)
  cases hc : C.col with
  | none =>
    simp only [cpSlot, cpCnt, cpGrowIf, cpColW, hc, Option.map_none, seqO, mapS, mapE, lvF, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub]
    vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, st64, kgrowBlk_spec p C hO n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, ↓reduceIte, colW, hc] at *)
    all_goals grind [lang_grind, growK, tailM, krW, knW, koW]
  | some A =>
    have hA := hO.colA A hc
    simp only [cpSlot, cpCnt, cpGrowIf, cpColW, hc, Option.map_some, seqO, mapS, mapE, lvF, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub]
    vcgen [step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, st64, kgrowBlk_spec p C hO n]
    all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, rd64_rdWC, ↓reduceIte, colW, hc] at *)
    all_goals grind [lang_grind, growK, tailM, krW, knW, koW]

theorem cpWr_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C) (n : Nat) :
    ∀ (es : List Expr), (∀ e ∈ es, LocOnly e) → ∀ (f : Nat) (s₁ : St),
    s₁.loc (gO C + 1) = rdW (s₁.mem.arr64 (tierA C.sa (s₁.loc 0))) 0 →
    ⦃fun s => s = s₁⦄
    step p (exec p n) (cpWr C f es (cpRest C))
    ⦃fun r s' => r = .ret [s₁.loc (2 + C.np)] ∧
      growK C (s₁.loc 0) (s₁.loc (gO C + 1)) (s₁.loc (2 + C.np))
        (colW C (s₁.loc 0) (s₁.loc (2 + C.np)) (s₁.loc (4 + C.np))
          (tailM C (s₁.loc 0) (s₁.loc (1 + C.np)) (s₁.loc (2 + C.np)) (pkw C s₁)
            (wrRecK (tierA C.ra (s₁.loc 0)) (s₁.loc (3 + C.np)) s₁.mem (UInt64.ofNat f)
              (es.map (Expr.pval s₁))))) =
        some s'.mem; ⊤⦄ := by
  have hrs := hO.arrs.2.2
  intro es
  induction es with
  | nil =>
    intro _ f s₁ hg
    simp only [cpWr, List.map_nil, wrRecK]
    exact cpRest_spec p C hO n s₁ hg
  | cons e es ih =>
    intro hl f s₁ hg
    have hes : ∀ e' ∈ es, LocOnly e' := fun e' h => hl e' (List.mem_cons_of_mem _ h)
    have hmap : ∀ s : St, s.loc = s₁.loc → es.map (Expr.pval s) = es.map (Expr.pval s₁) :=
      fun s h => List.map_congr_left (fun e' he' => hes e' he' s s₁ h)
    have ef : UInt64.ofNat (f + 1) = UInt64.ofNat f + 1 := by simp [UInt64.ofNat_add]
    have e0 : UInt64.ofNat 0 = 0 := rfl
    have hkw : ∀ (M : Mem), pkw C { mem := M, loc := s₁.loc } = pkw C s₁ := fun M => by
      simp only [pkw, argsOf]; exact kwP_mem p hO _ _ _
    have hsa : ∀ (k v : Word), (s₁.mem.set64 (tierA C.ra (s₁.loc 0)) k v).arr64
        (tierA C.sa (s₁.loc 0)) = s₁.mem.arr64 (tierA C.sa (s₁.loc 0)) :=
      fun k v => Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (tierA_ne hO.lt.1 hO.lt.2.1 hrs _ _))
    simp only [cpWr]
    by_cases hf0 : f = 0
    · subst hf0
      simp only [↓reduceIte]
      vcgen [step, evalE_spec, st64, ih hes (0 + 1)]
      all_goals (simp only [Expr.pval, List.map_cons, wrRecK, ef, e0,
        UInt64.add_zero, Nat.zero_add, hkw, hsa] at *)
      all_goals (try simp only [hmap _ rfl] at *)
      all_goals grind
    · simp only [hf0, ↓reduceIte]
      vcgen [step, evalE_spec, st64, ih hes (f + 1)]
      all_goals (simp only [BinOp.eval, Expr.pval, List.map_cons,
        wrRecK, ef, hkw, hsa] at *)
      all_goals (try simp only [hmap _ rfl] at *)
      all_goals grind

theorem addnp_eq_gO (C : ConsSch) (k j : Nat) (h : k < 4 + j) : (k + C.np = gO C + j) = False := by
  simp only [gO, eq_iff_iff, iff_false]; omega

theorem gO_eq_addnp (C : ConsSch) (k j : Nat) (h : k < 4 + j) : (gO C + j = k + C.np) = False := by
  simp only [gO, eq_iff_iff, iff_false]; omega

theorem argsOf_setLoc_gO (C : ConsSch) (j : Nat) (s : St) (v : Word) :
    argsOf 1 C.np (s.setLoc (gO C + j) v) = argsOf 1 C.np s :=
  argsOf_setLoc 1 C.np _ (by simp only [gO]; omega) s v

theorem pkw_init (p : Prog) {C : ConsSch} (hO : ConsOK p C) (m m' : Mem) (vs : List Word) :
    pkw C { mem := m, loc := Locals.init vs } = kwP C m' (argsL 1 C.np vs) := by
  simp only [pkw, argsOf_mk]; exact kwP_mem p hO _ _ _

/-- **`X_push(t, args, j)`** appends node `cntC` to tier `t` (record `vsM args`, column word
`colM args`, key word `kwP args`) at slot `j`, then grows the tier if it passed 3/4 load (any
argument list: `t`, the inputs, `j` are its words `0`, `1 ‥ np`, `np + 1`). -/
theorem consPushG_specV (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hp : p.lookup C.pname = some (consPushG C)) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.pname vs
    ⦃fun r s' => LocEq s' s₀ ∧ pushOKC C s₀.mem (Locals.init vs 0) = true ∧
      r = [cntC C s₀.mem (Locals.init vs 0)] ∧
      kgrowIf C (Locals.init vs 0) s₀.mem (pushMX C s₀.mem (Locals.init vs 0)
        (C.vsM (argsL 1 C.np vs)) (C.colM s₀.mem (argsL 1 C.np vs)) (Locals.init vs (1 + C.np))
        (cntC C s₀.mem (Locals.init vs 0)) (kwP C s₀.mem (argsL 1 C.np vs)))
        (cntC C s₀.mem (Locals.init vs 0)) = some s'.mem; ⊤⦄ := by
  have hV := hO.recs.2
  have hPO := hO.pre
  unfold PreOK at hPO
  rw [invoke_eq _ hp]
  simp only [callFn, consPushG, cpHead, cpMid, seqs, List.map, mapS, mapE, mapC, lvF, L.Notation.blk]
  rcases Classical.em (C.w = 1) with hw | hw <;> simp only [hw, ↓reduceIte, mapS, mapE, lvF] <;>
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
          Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
          Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add 1 C.np 2 (by decide),
          argsOf_setLoc_add 1 C.np 3 (by decide), zero_ne_add 2 C.np (by decide),
          zero_ne_add 3 C.np (by decide), argsOf_mk,
          addnp_eq_gO C 1 1 (by decide), addnp_eq_gO C 2 1 (by decide), addnp_eq_gO C 3 1 (by decide),
          argsOf_setLoc_gO,
          hO.room_eq, hO.recs.2, ofNat_zero', pushMX, colW, hPO,
          ↓reduceIte, kgrowIf_growK, pushMC, pushOKC,
          cntC, hw, UInt64.mul_one] at *)
      all_goals grind [lang_grind, arena_grind]
  | some b =>
    simp only [hpre] at hPO
    simp only [seqO]
    cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs, setLoc, ld64, hPO n,
        cpWr_spec p C hO n C.recW hO.recs.1 0]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, BinOp.eval, Cmp.eval,
          Expr.pval, Cond.pval, decide_eq_true_eq, Nat.add_right_cancel_iff,
          Nat.reduceEqDiff, rd64_rdWC, argsOf_setLoc_add 1 C.np 2 (by decide),
          argsOf_setLoc_add 1 C.np 3 (by decide), zero_ne_add 2 C.np (by decide),
          zero_ne_add 3 C.np (by decide), argsOf_mk,
          addnp_eq_gO C 1 1 (by decide), addnp_eq_gO C 2 1 (by decide), addnp_eq_gO C 3 1 (by decide), addnp_eq_gO C 4 1 (by decide),
          argsOf_setLoc_gO,
          hO.room_eq, hO.recs.2, ofNat_zero', pushMX,
          ↓reduceIte, kgrowIf_growK, pushMC, pushOKC,
          cntC, hw, UInt64.mul_one] at *)
      all_goals (obtain ⟨hm1, hk1, hx1⟩ := ‹_ ∧ KeepLo _ _ _ ∧ _›
                 have e0 := hk1 0 (by omega)
                 have e1 := hk1 (1 + C.np) (by omega)
                 have ea := argsOf_keepLo 1 C.np (2 + C.np) (by omega) _ _ hk1
                 simp only [argsOf_mk] at ea e0 e1
                 simp only [e0, ea, hm1, hx1, Nat.add_comm 1 C.np] at *)
      all_goals grind [lang_grind, arena_grind]

/-- `X_push(t, args, j)` at `np` inputs. -/
theorem consPushG_spec (p : Prog) (C : ConsSch) (hO : ConsOK p C)
    (hp : p.lookup C.pname = some (consPushG C)) (n : Nat) (s₀ : St) (t : Word)
    (as : List Word) (has : as.length = C.np) (j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) C.pname (t :: (as ++ [j]))
    ⦃fun r s' => LocEq s' s₀ ∧ pushOKC C s₀.mem t = true ∧ r = [cntC C s₀.mem t] ∧
      kgrowIf C t s₀.mem (pushMX C s₀.mem t (C.vsM as) (C.colM s₀.mem as) j
        (cntC C s₀.mem t) (kwP C s₀.mem as)) (cntC C s₀.mem t) = some s'.mem; ⊤⦄ := by
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
    match kgrowIf C t m (pushMX C m t (C.vsM (pushArgs C ks h)) (C.colM m (pushArgs C ks h))
      j (cntC C m t) (kwP C m (pushArgs C ks h))) (cntC C m t) with
    | some m' => some (B + cntC C m t, m')
    | none => none
  else none

/-- The probe of tier `t` for key `ks` (hash `h`). -/
def probeC (C : ConsSch) (m : Mem) (ks : List Word) (h t : Word) : List Word :=
  cprobeW (m.arr64 (tierA C.sa t)) (C.mtM m (ks ++ [h]) t) C.exact (kwQ C ks h) (baseW m t)
    (knW C.sa m t)
    (krW C.sa m t) (homeW h (knW C.sa m t)) 0

/-- An exact two-word key with a word at or above `2^32`: `intern_X` aborts (`ciChk`; its key
word could not pack the key). -/
def bigK (C : ConsSch) (ks : List Word) : Prop :=
  C.exact = true ∧ C.nk = 2 ∧ (ks.getD 0 0 ||| ks.getD 1 0) >>> 32 ≠ 0

instance (C : ConsSch) (ks : List Word) : Decidable (bigK C ks) := by
  unfold bigK; infer_instance

theorem ciChk_pos {C : ConsSch} (h : C.exact = true ∧ C.nk = 2) :
    ciChk C = [.ite (.cmp .ne (.bin .shr (.bin .or (.var 0) (.var 1)) (.const 32)) (.const 0))
      (.abort (.const R_CAP_KEY)) .skip] := by
  simp only [ciChk, h, and_self, ↓reduceIte]

theorem ciChk_neg {C : ConsSch} (h : ¬ (C.exact = true ∧ C.nk = 2)) : ciChk C = [] := by
  simp only [ciChk, h, ↓reduceIte]

theorem kwP_pushArgs (C : ConsSch) (m : Mem) (ks : List Word) (hks : ks.length = C.nk) :
    kwP C m (pushArgs C ks (C.qhM m ks)) = kwQ C ks (C.qhM m ks) := by
  have ht : (pushArgs C ks (C.qhM m ks)).take C.nk = ks := by
    simp [pushArgs, ← hks]
  cases hx : C.exact
  · simp only [kwP, kwQ, hx, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hlt
      simp [pushArgs, hlt, List.getD_eq_getElem?_getD, hks]
    · rw [ht]
  · simp only [kwP, kwQ, hx, ↓reduceIte]
    split
    · rfl
    · rename_i h1
      simp only [pushArgs, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · rename_i h0 h1
      have a0 : C.nk ≠ 0 := h0
      have a1 : C.nk ≠ 1 := h1
      simp only [pushArgs, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

/-- **The L model of `intern_X(k)`**: the handle and the memory after, `none` where the L code
aborts (an oversized exact key, a full table). The persistent probe unless skipped, the scratch probe if the scratch tier is open, the
append to the tier the store is in. -/
def consInternM (C : ConsSch) (m : Mem) (ks : List Word) : Option (Word × Mem) :=
  let h := C.qhM m ks
  let rs₀ := probeC C m ks h 0
  let rs₁ := probeC C m ks h 1
  if bigK C ks then none
  else if skipC C m ks = 0 ∧ rs₀ = [] then none
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
set_option maxHeartbeats 1600000 in
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
  have hml := hO.mloc
  rw [invoke_eq _ hpi]
  simp only [callFn]
  cases hsk : C.skipW with
  | some e =>
    have he := hO.skips e hsk
    by_cases hb : C.exact = true ∧ C.nk = 2
    all_goals rw [consInternG.eq_def]; simp only [hsk]
    all_goals (first | rw [ciChk_pos hb] | rw [ciChk_neg hb])
    all_goals simp only [seqs, List.cons_append, List.nil_append, ciFind, ciHit, ciScr, ciEnd,
      ciPush, ciOpen]
    all_goals cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs_spec, setLoc, setLocs, hO.ihash_spec n,
        consFindG_specV p C hO.match_ hml hpf n, consPushG_specV p C hO hpp n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        List.headD_cons, List.tail_cons, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, rd64_rdWC, List.map_cons, map_keyArgs,
        List.map_append, map_hOpt] at *)
      all_goals subst_vars
      all_goals (simp only [hO.skips e hsk, Nat.add_right_cancel_iff, Nat.reduceEqDiff,
        argsOf_setLoc 0 C.nk C.nk (by omega), argsOf_setLoc_add 0 C.nk 1 (by omega),
        argsOf_setLoc_add 0 C.nk 2 (by omega), argsOf_setLoc_add 0 C.nk 3 (by omega),
        argsOf_setLoc_add 0 C.nk 4 (by omega), argsOf_setLoc_add 0 C.nk 5 (by omega),
        argsOf_self _ ks C.nk hks, argsL_key _ _ ks C.nk hks, argsL_app _ ks _ C.nk hks,
        Locals.init_cons_zero,
        init_last _ ks _ C.nk hks, init_past2 _ ks _ C.nk 4 hks (by decide),
        argsL_push C hn _ _ _ ks hks, init_push_j C hn _ _ _ ks hks, List.map_nil,
        self_ne_add 1 C.nk (by decide), ↓reduceIte] at *)
      all_goals (simp only [consInternM, skipC, hsk, probeC, pushC, Sig.retVal, List.headD_cons,
        bne_iff_ne, beq_iff_eq, ne_eq, LocEq, Sig.retOr, bigK] at *)
      all_goals (simp_all [Locals.init])
  | none =>
    by_cases hb : C.exact = true ∧ C.nk = 2
    all_goals rw [consInternG.eq_def]; simp only [hsk]
    all_goals (first | rw [ciChk_pos hb] | rw [ciChk_neg hb])
    all_goals simp only [seqs, List.cons_append, List.nil_append, ciFind, ciHit, ciScr, ciEnd,
      ciPush, ciOpen]
    all_goals cases n with
    | zero => vcgen [exec] <;> grind
    | succ n =>
      vcgen [exec, step, evalE_spec, evalC_spec, evalArgs_spec, setLoc, setLocs, hO.ihash_spec n,
        consFindG_specV p C hO.match_ hml hpf n, consPushG_specV p C hO hpp n]
      all_goals (simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        List.headD_cons, List.tail_cons, BinOp.eval, Cmp.eval,
        Expr.pval, Cond.pval, rd64_rdWC, List.map_cons, map_keyArgs,
        List.map_append, map_hOpt] at *)
      all_goals subst_vars
      all_goals (simp only [Nat.add_right_cancel_iff, Nat.reduceEqDiff,
        argsOf_setLoc 0 C.nk C.nk (by omega),
        argsOf_setLoc_add 0 C.nk 2 (by omega), argsOf_setLoc_add 0 C.nk 3 (by omega),
        argsOf_setLoc_add 0 C.nk 4 (by omega), argsOf_setLoc_add 0 C.nk 5 (by omega),
        argsOf_self _ ks C.nk hks, argsL_key _ _ ks C.nk hks, argsL_app _ ks _ C.nk hks,
        Locals.init_cons_zero,
        init_last _ ks _ C.nk hks, init_past2 _ ks _ C.nk 4 hks (by decide),
        argsL_push C hn _ _ _ ks hks, init_push_j C hn _ _ _ ks hks, List.map_nil, ↓reduceIte] at *)
      all_goals (simp only [consInternM, skipC, hsk, probeC, pushC, Sig.retVal, List.headD_cons,
        bne_iff_ne, ne_eq, LocEq, Sig.retOr, bigK] at *)
      all_goals (simp_all [Locals.init])

/-! ## What an interning does to memory -/

/-- **An interning hits** (the memory is unchanged) **or appends** node `cntC` to a tier, with its
growth. -/
theorem consInternM_cases {C : ConsSch} {m m₁ : Mem} {ks : List Word} {r : Word}
    (h : consInternM C m ks = some (r, m₁)) :
    m₁ = m ∨ ∃ t j, t ≤ 1 ∧ pushOKC C m t = true ∧
      kgrowIf C t m (pushMX C m t (C.vsM (pushArgs C ks (C.qhM m ks)))
        (C.colM m (pushArgs C ks (C.qhM m ks))) j (cntC C m t)
        (kwP C m (pushArgs C ks (C.qhM m ks))))
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

/-- **The growth writes only the slot array** (and keeps every size). -/
theorem kgrowIf_frame (C : ConsSch) (t : Word) (m₀ m m' : Mem) (c : Word)
    (h : kgrowIf C t m₀ m c = some m') :
    (∀ b, b ≠ tierA C.sa t → m'.arr64 b = m.arr64 b) ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
      m'.words.size = m.words.size := by
  change GFr (tierA C.sa t) m m'
  unfold kgrowIf at h
  split at h
  · exact kgrowM_fr _ _ _ _ _ h
  · cases h; exact GFr.refl _ _

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
    ((wrRecK (tierA C.ra t) (cntC C m t * C.w) m 0 (C.vsM (pushArgs C ks (C.qhM m ks)))).set64
      CTL (C.ca + (t &&& 1)) (cntC C m t + 1))

theorem colW_arr (C : ConsSch) (t c x : Word) (m : Mem) (b : ArrId)
    (hb : ∀ A, C.col = some A → tierA A t ≠ b) :
    (colW C t c x m).arr64 b = m.arr64 b := by
  unfold colW; split
  · rfl
  · rename_i A hA; exact Mem.arr64_set64_ne _ _ _ _ _ (fun e => hb A hA e.symm)

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

theorem OutSa.colW (C : ConsSch) (t : Word) (hcol : ∀ A, C.col = some A → tierA A t ≠ tierA C.sa t)
    {M₁ M₂ : Mem} (h : OutSa (tierA C.sa t) M₁ M₂) (c x : Word) :
    OutSa (tierA C.sa t) (colW C t c x M₁) (colW C t c x M₂) := by
  unfold L.Arena.colW; split
  · exact h
  · rename_i A hA; exact h.set64 (hcol A hA) _ _

/-- **An interning hits** (the memory is unchanged) **or appends** node `cntC` to tier `t`: the
handle is the tier's base plus the count, and outside the slot array the memory is `pushRec`. -/
theorem consInternM_outA {C : ConsSch} {m : Mem} (hsc : C.sa ≠ CTL)
    (hcol : ∀ A, C.col = some A → A ≠ C.sa) (hl : C.sa < 256 ∧ ∀ A, C.col = some A → A < 256)
    {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) :
    m' = m ∨ ∃ t, t ≤ 1 ∧ pushOKC C m t = true ∧ w = (if t = 0 then C.P else C.S) + cntC C m t ∧
      (∀ b, b ≠ tierA C.sa t → m'.arr64 b = (pushRec C m t ks).arr64 b) ∧
      (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size := by
  rcases consInternM_cases h with e | ⟨t, j, ht, hok, hg, hr⟩
  · exact .inl e
  refine .inr ⟨t, ht, hok, hr, ?_⟩
  obtain ⟨g1, g2, g3⟩ := kgrowIf_frame _ _ _ _ _ _ hg
  refine ⟨fun b hb => ?_, fun b => ?_, ?_⟩
  · rw [g1 b hb]
    simp only [pushMX, pushMC, tailM, pushRec]
    refine OutSa.colW C t (fun A hA => tierA_ne (hl.2 A hA) hl.1 (hcol A hA) t t)
      (fun b hb => ?_) _ _ b hb
    refine OutSa.set64 (fun b hb => ?_)
      (by simpa using (tierA_ne (show CTL < 256 by decide) hl.1 (Ne.symm hsc) 0 t)) _ _ b hb
    exact OutSa.set64_sa (OutSa.set64_sa (fun _ _ => rfl) _ _) _ _ b hb
  · rw [g2 b]
    simp only [pushMX, pushMC, tailM, colW_size, arr64_size_set64, wrRecK_size]
  · rw [g3]
    simp only [pushMX, pushMC, tailM, colW_words, Mem.words_size_set64, wrRecK_words]



-- The model is opaque outside the library: users read it through the lemmas above and in
-- `ConsLibRel.lean`.
attribute [irreducible] consInternM

end L.Arena
