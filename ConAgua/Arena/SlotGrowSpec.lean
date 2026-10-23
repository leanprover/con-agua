module

public import ConAgua.Arena.SlotGrow
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The growth block's model and spec (lane slotgrow)

The models of the loops of `growB` (`SlotGrow.lean`), each a function of the memory and the loop's
variables that returns `none` where the L code aborts, and the spec of the block as spliced into a
push (`growBlkG S o`): it keeps the push's own variables (below `o`) and leaves the memory
`growM S.sa S.ca H m`, where `H m t i` is the hash the schema's `hash` block computes for node
`i` of tier `t` (`HashOK`).

The table relation's side (the growth re-registers every node, so every node is found again) is
`StoreLib.lean`'s `storeR_growIf`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The growth exponent of slot array `sa`: its last word. -/
def gexpW (sa : ArrId) (m : Mem) : Word := rdW (m.arr64 sa) (m.len64 sa - 1)

/-- The slot count of a tier of the table with slot array `sa`. -/
def gnW (sa : ArrId) (m : Mem) : Word := SN0 <<< gexpW sa m

/-- The probe loop: from slot `j` of tier `t` after `d` steps, the first free slot (`none`: the
abort after `n` steps). -/
def gprobeW (sl : Array Word) (t n j d : Word) : Option Word :=
  if rdW sl (j * 2 + t) = 0 then some j
  else if n ≤ d then none
  else gprobeW sl t n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by
    have := ‹¬ n ≤ d›; simp only [UInt64.le_iff_toNat_le] at this; omega
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- The node loop: register nodes `i, …, c - 1` of tier `t` (slot base `b`) among `n` slots,
`H` the hash of a node. -/
def gnodesW (sa : ArrId) (H : Mem → Word → Word → Word) (n t b c i : Word) (m : Mem) :
    Option Mem :=
  if i < c then
    match gprobeW (m.arr64 sa) t n (homeW (H m t i) n) 0 with
    | none => none
    | some j => gnodesW sa H n t b c (i + 1) (m.set64 sa (j * 2 + t) (b + i + 1))
  else some m
termination_by c.toNat - i.toNat
decreasing_by
  have : i.toNat < c.toNat := UInt64.lt_iff_toNat_lt.mp ‹i < c›
  have := c.toNat_lt
  have : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- The tier loop: register the nodes of tiers `t, …, 1`. -/
def gtiersW (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (n t : Word) (m : Mem) :
    Option Mem :=
  if t < 2 then
    match gnodesW sa H n t (rdW (m.arr64 CTL) SCB * t) (rdW (m.arr64 CTL) (ca + t)) 0 m with
    | none => none
    | some m' => gtiersW sa ca H n (t + 1) m'
  else some m
termination_by 2 - t.toNat
decreasing_by
  have : t.toNat < 2 := UInt64.lt_iff_toNat_lt.mp ‹t < 2›
  have : (t + 1).toNat = t.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- Eight zero words of `sa` from `k`. -/
def zero8 (sa : ArrId) (k : Word) (m : Mem) : Mem :=
  (((((((m.set64 sa k 0).set64 sa (k + 1) 0).set64 sa (k + 2) 0).set64 sa (k + 3) 0).set64 sa
    (k + 4) 0).set64 sa (k + 5) 0).set64 sa (k + 6) 0).set64 sa (k + 7) 0

/-- The zero loop: the words `[k, n)` of `sa`, eight at a time. (Where `k + 8` would wrap, the
L code's stores are out of bounds: the model stops.) -/
def gzeroW (sa : ArrId) (n k : Word) (m : Mem) : Mem :=
  if k < n ∧ k.toNat + 8 < 2 ^ 64 then gzeroW sa n (k + 8) (zero8 sa k m) else m
termination_by n.toNat - k.toNat
decreasing_by
  have : k.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp ‹k < n ∧ _›.1
  have : (k + 8).toNat = k.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  omega

/-- **The growth**: the memory after `growB`, `none` where it aborts. -/
def growM (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m : Mem) : Option Mem :=
  if (m.len64 sa - 1) >>> 1 < gnW sa m * 2 then none
  else gtiersW sa ca H (gnW sa m * 2) 0
    (gzeroW sa (gnW sa m * 2) 0 (m.set64 sa (m.len64 sa - 1) (gexpW sa m + 1)))

/-- **A push's tail**: from the memory `m` after the push's writes, grow if node count `c + 1`
passes half the slot count of the memory `m₀` before them (the push reads the exponent first). -/
def growIf (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word) :
    Option Mem :=
  if gnW sa m₀ < (c + 1) * 2 then growM sa ca H m else some m

theorem growIf_grow (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word)
    (h : gnW sa m₀ < (c + 1) * 2) : growIf sa ca H m₀ m c = growM sa ca H m := by
  simp [growIf, h]

theorem growIf_keep (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m : Mem) (c : Word)
    (h : ¬ gnW sa m₀ < (c + 1) * 2) : growIf sa ca H m₀ m c = some m := by
  simp [growIf, h]

/-- **The growth writes only the slot array** (and keeps every size). -/
theorem growIf_frame (sa : ArrId) (ca : Word) (H : Mem → Word → Word → Word) (m₀ m m' : Mem)
    (c : Word) (h : growIf sa ca H m₀ m c = some m') :
    (∀ b, b ≠ sa → m'.arr64 b = m.arr64 b) ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
      m'.words.size = m.words.size := by
  sorry

/-- The schema's `hash` block, spliced at `o`, sets `h` (`o + 5`) to `H m t i` (`t` at `o + 2`,
`i` at `o + 3`) and changes nothing else. -/
def HashOK (p : Prog) (S : GrowSch) (o : Nat) (H : Mem → Word → Word → Word) : Prop :=
  ∀ (k : Stmt → M Sig) (s₀ : St),
    ⦃fun s => s = s₀⦄
    step p k (shiftS o S.hash)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧
      LocEq s' (s₀.setLoc (o + 5) (H s₀.mem (s₀.loc (o + 2)) (s₀.loc (o + 3)))); ⊤⦄

/-- The variables below `o` are kept. -/
def KeepLo (o : Nat) (s s' : St) : Prop := ∀ x, x < o → s'.loc x = s.loc x

theorem KeepLo.loc {o : Nat} {s s' : St} (h : KeepLo o s s') (x : Var) (hx : x < o) :
    s'.loc x = s.loc x := h x hx

grind_pattern [lang_grind] KeepLo.loc => KeepLo o s s', s'.loc x

/-- **The growth block spliced at `o`**: it keeps the variables below `o`, completes normally, and
leaves `growM`'s memory. -/
theorem growBlkG_spec (p : Prog) (S : GrowSch) (sa : ArrId) (ca : Word) (hsa : S.sa = sa)
    (hca : S.ca = ca) (o : Nat) (H : Mem → Word → Word → Word) (hH : HashOK p S o H) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (growBlkG S o)
    ⦃fun r s' => r = .normal ∧ KeepLo o s₀ s' ∧ growM sa ca H s₀.mem = some s'.mem; ⊤⦄ := by
  sorry

end L.Arena
