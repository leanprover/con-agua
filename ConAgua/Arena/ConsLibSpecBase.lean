module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
public import ConAgua.Arena.SlotGrowSpec
public import ConAgua.L.PureEval
public import ConAgua.Arena.ConsLib
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The cons-table library specs: the shared vocabulary (lane conslib)

The probe model, the obligations of an instance (`ConsOK`), the argument-list lemmas. Split from
`ConsLibSpec.lean`; the find, growth and push/intern specs build on it.
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

theorem rd64_rdWC (m : Mem) (a : TieredArray) (i : Word) : rd64 m a i = rdW (m.arr64 a) i := by
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


end L.Arena
