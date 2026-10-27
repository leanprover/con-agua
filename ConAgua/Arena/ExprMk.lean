module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.LpCol
public import ConAgua.Arena.AppStore
public import ConAgua.Arena.LetStore
public import ConAgua.Arena.LamStore
public import ConAgua.Arena.ForallStore
public import ConAgua.Arena.ProjStore
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The derived loose-bvar range of expression nodes, and the `mk_*` constructors that keep it

con-ron's store keeps a **derived word** per node (`Tbl.der`, `EStore.derived`, `derOfView`):
a 32-bit hash, the loose-bvar range, the fvar range and a level-param flag, packed
(`packData`). The expression walks read its range field before anything else
(`liftLooseBVarsGo`, `instantiate1Go`, … cut off at `bvarOfData (derived h) ≤ c`), so L must know
it exactly. L keeps **the range fields and the level-parameter bit** (the hash is `mixHash`,
opaque: no verdict reads the hash bits, only a parent's hash does); for the five compound tables in one word array per table, indexed as
the records (`2 i + t`), packed by `packBFL` (bvar range bits 0‥14, fvar range 15‥29, `lp` bit 30;
helper `whnf4-d23` added the bit, deviation D23; the leaves' bits are in their own columns,
`LpCol.lean`):

| array | table | count words |
|---|---|---|
| 42 `ADER` | `app` | `CTL[4], CTL[5]` |
| 43 `LADER` | `lam` | `CTL[28], CTL[29]` |
| 44 `FADER` | `forallE` | `CTL[30], CTL[31]` |
| 45 `LEDER` | `letE` | `CTL[20], CTL[21]` |
| 46 `PJDER` | `proj` | `CTL[32], CTL[33]` |

A leaf's range is a function of its record (`bvar i`: `satSucc i`; the others `0`), so it is not
stored. `der_b(h)` returns the range field of `derived h` as the arena computes it, including its
`0` for a handle that does not view (scratch tier closed, index past the count, unknown tag).

**Writers.** `mk_app(f, a)`, `mk_lam`, `mk_forall`, `mk_let`, `mk_proj` are the expression
constructors walks call: `intern_*` first, then, **if the table grew** (its two counts changed),
the new node's range at `idx * 2 + tier` of the result. A hit writes nothing (the node's range is
already there). `mk_app`, `mk_lam` and `mk_forall` read the children's ranges (`der_b`) only on
that miss, as the twin's `EStore.intern` computes `derOfView` only on a miss (lane `derb`); they
read them after the append, with the new node's slot zeroed first, which reads the same as the
memory before (`der_pushZ`). `mk_let`/`mk_proj` (rare) still read them before `intern_*`. The
compound tables' `intern_*` are internal from now on: a node interned by them directly would have
no range (`DerRel.lean`'s relation would fail for it).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena


/-! ## `der_b(h)`: the range field of `derived h` -/

/-- **The model of `der_b`.** The five compound arms read a word packed by `packBF` (bvar range
in bits 0‥14, fvar range in bits 15‥29, `derFW` below): `& 32767` is `packBF_bvar`. -/
def derBW (m : Mem) (h : Word) : Word :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then 0
  else if h >>> 28 = 0 then
    if tcnt m BVAR (tierW h) ≤ idxW h then 0
    else satSuccW (tfld m BVAR (tierW h) (idxW h) 0)
  else if h >>> 28 = 4 then
    if tcnt m APP (tierW h) ≤ idxW h then 0
    else tfld m APP_DER (tierW h) (idxW h) 0 &&& 32767
  else if h >>> 28 = 5 then
    if tcnt m LAM (tierW h) ≤ idxW h then 0
    else tfld m LAM_DER (tierW h) (idxW h) 0 &&& 32767
  else if h >>> 28 = 6 then
    if tcnt m FORALL (tierW h) ≤ idxW h then 0
    else tfld m FORALL_DER (tierW h) (idxW h) 0 &&& 32767
  else if h >>> 28 = 7 then
    if tcnt m LET (tierW h) ≤ idxW h then 0
    else tfld m LET_DER (tierW h) (idxW h) 0 &&& 32767
  else if h >>> 28 = 9 then
    if tcnt m PROJ (tierW h) ≤ idxW h then 0
    else tfld m PROJ_DER (tierW h) (idxW h) 0 &&& 32767
  else 0

/-- **The model of the second result of `der_b`: the fvar range** (lane `exprops3`). `bvar`/`sort`/
`const`/`lit` have no free variables (`0`); `fvar`'s own range is `satSucc` of its own index
(`FVREC`, as the `bvar` arm reads `BREC`: the record alone determines it); the five compound arms
read the SAME packed word shifted and masked (`(>> 15) & 32767` is `packBFL_fvar`). -/
def derFW (m : Mem) (h : Word) : Word :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then 0
  else if h >>> 28 = 1 then
    if tcnt m FVAR (tierW h) ≤ idxW h then 0
    else satSuccW (tfld m FVAR (tierW h) (idxW h) 0)
  else if h >>> 28 = 4 then
    if tcnt m APP (tierW h) ≤ idxW h then 0
    else (tfld m APP_DER (tierW h) (idxW h) 0 >>> 15) &&& 32767
  else if h >>> 28 = 5 then
    if tcnt m LAM (tierW h) ≤ idxW h then 0
    else (tfld m LAM_DER (tierW h) (idxW h) 0 >>> 15) &&& 32767
  else if h >>> 28 = 6 then
    if tcnt m FORALL (tierW h) ≤ idxW h then 0
    else (tfld m FORALL_DER (tierW h) (idxW h) 0 >>> 15) &&& 32767
  else if h >>> 28 = 7 then
    if tcnt m LET (tierW h) ≤ idxW h then 0
    else (tfld m LET_DER (tierW h) (idxW h) 0 >>> 15) &&& 32767
  else if h >>> 28 = 9 then
    if tcnt m PROJ (tierW h) ≤ idxW h then 0
    else (tfld m PROJ_DER (tierW h) (idxW h) 0 >>> 15) &&& 32767
  else 0

/-- con-ron: none — reads L's derived-range array (the twin's `bvarOfData (derived h)`); returns the
bvar range and, as a second result, the fvar range (`derFW`; lane `exprops3`), as a third the
level-parameter bit (`exprLPW`, the twin's `lpOfData (derived h)`; helper `whnf4-d23`). The tags
are tested in order of frequency on Init (`app` 4, `bvar` 0, `const` 3, `lam` 5, `fvar` 1, `forallE` 6,
`sort` 2, `proj` 9, `letE` 7; lane `derb`); the tests are disjoint, so the order changes no result. -/
def derB : FunDecl := lfn (h) locals (g, t, i, x) {
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { return (0, 0, 0) };
  if g == 4 { if APP⟨t⟩.count <= i { return (0, 0, 0) }; x := APP_DER⟨t, i⟩; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  if g == 0 {
    if BVAR⟨t⟩.count <= i { return (0, 0, 0) };
    x := BVAR⟨t, i⟩.i;
    return ((x + 1) * u64(x < 32767) + 32767 * u64(32767 <= x), 0, 0)
  };
  if g == 3 { if CONST⟨t⟩.count <= i { return (0, 0, 0) }; return (0, 0, CONST_LP⟨t, i⟩) };
  if g == 5 { if LAM⟨t⟩.count <= i { return (0, 0, 0) }; x := LAM_DER⟨t, i⟩; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { return (0, 0, 0) };
    x := FVAR⟨t, i⟩.i;
    return (0, (x + 1) * u64(x < 32767) + 32767 * u64(32767 <= x), FVAR_LP⟨t, i⟩)
  };
  if g == 6 { if FORALL⟨t⟩.count <= i { return (0, 0, 0) }; x := FORALL_DER⟨t, i⟩; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  if g == 2 { if SORT⟨t⟩.count <= i { return (0, 0, 0) }; return (0, 0, SORT_LP⟨t, i⟩) };
  if g == 9 { if PROJ⟨t⟩.count <= i { return (0, 0, 0) }; x := PROJ_DER⟨t, i⟩; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  if g == 7 { if LET⟨t⟩.count <= i { return (0, 0, 0) }; x := LET_DER⟨t, i⟩; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  return (0, 0, 0)
}

set_option maxHeartbeats 1000000 in
theorem derB_spec (p : Prog) (hp : p.lookup "der_b" = some derB) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "der_b" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = derBW s₀.mem h ∧
      r.tail.headD 0 = derFW s₀.mem h ∧ r.tail.tail.headD 0 = exprLPW s₀.mem h; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, derB]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
      finish [derBW, derFW, exprLPW, tierW, idxW, satSuccW]

attribute [arena_grind =] mkK_some

/-! ## The memory after an append, as `der_b` reads it

`mk_app`/`mk_lam`/`mk_forall` read the children's ranges only after `intern_*` appended a node
(as the twin's `EStore.intern` computes `derOfView` only on a miss), so they read the memory
AFTER the append. Before reading, they zero the new node's range slot: then every handle reads
the same range, fvar range and level-parameter bit as before the append, the new node itself
included (before: past the count, `0`; after: the zeroed slot, `0`). -/

theorem rdW_set64E (m : Mem) (a b : ArrId) (k v x : Word) :
    rdW ((m.set64 a k v).arr64 b) x =
      if b = a ∧ k = x ∧ k.toNat < (m.arr64 a).size then v else rdW (m.arr64 b) x := by
  by_cases h : b = a
  · subst h; rw [Mem.arr64_set64_same]
    simp only [rdW, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; grind
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]; simp [h]

theorem Mem.set64_set64_same (m : Mem) (a : ArrId) (i v w : Word) :
    (m.set64 a i v).set64 a i w = m.set64 a i w := by
  have := Mem.arr64_set64_same m a i v
  simp only [Mem.set64] at this ⊢
  rw [this]
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]

theorem slot_eq_iff {i c t u : Word} (hi : i < 134217728) (hc : c < 134217728) (ht : t ≤ 1)
    (hu : u ≤ 1) : i * 2 + t = c * 2 + u ↔ i = c ∧ t = u := by
  constructor
  · intro h
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.toNat_mul, show (2 : Word).toNat = 2 from rfl, show (1 : Word).toNat = 1 from rfl,
      show (134217728 : Word).toNat = 134217728 from rfl] at *
    omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem h01 (x : Word) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj] at *
  have : (1 : Word).toNat = 1 := rfl; have : (0 : Word).toNat = 0 := rfl; omega

theorem idxW_lt (h : Word) : idxW h < 134217728 := by
  simp only [idxW, UInt64.lt_iff_toNat_lt, UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- The memory after appending node `c = CTL[k + t]` to a binary table (records `R`, one packed
word `f | a << 32` per node; slot array `S`, range words `D`, each tiered), outside the slot
array (the library's `pushRec`), with the new node's range slot zeroed. -/
def pushZ (R _S D : ArrId) (k : Word) (m : Mem) (t f a : Word) : Mem :=
  let c := rdW (m.arr64 CTL) (k + t)
  (((m.set64 (tierA R t) (c * 1 + 0) (f ||| a <<< 32)).set64 CTL (k + (t &&& 1))
    (c + 1)).set64 (tierA D t) c 0)

/-- The three binary tables `mk_*` read lazily. -/
def BinTbl (R S D : ArrId) (k : Word) : Prop :=
  (R = AREC ∧ S = ASLOT ∧ D = ADER ∧ k = 4) ∨ (R = LAREC ∧ S = LASLOT ∧ D = LADER ∧ k = 28) ∨
    (R = FAREC ∧ S = FASLOT ∧ D = FADER ∧ k = 30)

section pushZ
variable {R S D : ArrId} {k : Word} (m : Mem) (t f a : Word)

theorem pushZ_arr (b : ArrId) (h1 : b ≠ CTL) (h2 : b ≠ tierA R t) (h4 : b ≠ tierA D t) :
    (pushZ R S D k m t f a).arr64 b = m.arr64 b := by
  simp [pushZ, Mem.arr64_set64_ne, *]

theorem pushZ_ctl (hT : BinTbl R S D k) (ht : t ≤ 1) (x : Word) :
    rdW ((pushZ R S D k m t f a).arr64 CTL) x =
      if k + t = x ∧ (k + t).toNat < (m.arr64 CTL).size then rdW (m.arr64 CTL) (k + t) + 1
      else rdW (m.arr64 CTL) x := by
  rcases hT with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  rcases h01 t ht with rfl | rfl <;>
  simp [pushZ, Mem.arr64_set64_ne, rdW_set64E, CTL, ADER, AREC, LADER, LAREC,
    FADER, FAREC]

theorem pushZ_der (hT : BinTbl R S D k) (ht : t ≤ 1) (x : Word) :
    rdW ((pushZ R S D k m t f a).arr64 (tierA D t)) x =
      if rdW (m.arr64 CTL) (k + t) = x ∧
          (rdW (m.arr64 CTL) (k + t)).toNat < (m.arr64 (tierA D t)).size then 0
      else rdW (m.arr64 (tierA D t)) x := by
  rcases hT with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  rcases h01 t ht with rfl | rfl <;>
  simp [pushZ, Mem.arr64_set64_ne, rdW_set64E, CTL, ADER, AREC, LADER, LAREC,
    FADER, FAREC] <;> rfl

/-- A field of a store other than the pushed table's records and range column is unchanged. -/
theorem tfld_pushZ_other (X : TRec) (hX : X.arr < 256) (hc : X.arr ≠ CTL) (hR : X.arr ≠ R)
    (hD : X.arr ≠ D) (hRl : R < 256) (hDl : D < 256) (u i g : Word) :
    tfld (pushZ R S D k m t f a) X u i g = tfld m X u i g := by
  simp only [tfld]
  rw [pushZ_arr m t f a _ (by simpa using tierA_ne hX (show CTL < 256 by decide) hc u 0)
    (tierA_ne hX hRl hR u t) (tierA_ne hX hDl hD u t)]

/-- A word of the pushed table's range column (`w = 1`): the new node's is `0`, the others as
before. -/
theorem tfld_pushZ_der (hT : BinTbl R S D k) (ht : t ≤ 1) (X : TRec) (hX : X.arr = D)
    (hw : X.w = 1) (u : Word) (hu : u ≤ 1) (i : Word) :
    tfld (pushZ R S D k m t f a) X u i 0 =
      if u = t ∧ rdW (m.arr64 CTL) (k + t) = i ∧
          (rdW (m.arr64 CTL) (k + t)).toNat < (m.arr64 (tierA D t)).size then 0
      else tfld m X u i 0 := by
  have hDl : D < 256 := by
    rcases hT with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ <;> decide
  have hRl : R < 256 := by
    rcases hT with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩ <;> decide
  have hRD : R ≠ D := by
    rcases hT with ⟨rfl, -, rfl, -⟩ | ⟨rfl, -, rfl, -⟩ | ⟨rfl, -, rfl, -⟩ <;> decide
  have had : X.ad i 0 = i := by simp [TRec.ad, hw]
  simp only [tfld, had, hX]
  by_cases hut : u = t
  · subst hut; rw [pushZ_der m u f a hT ht]
    simp only [true_and, apply_ite (X.ex 0), TRec.ex_zero]
  · have hDc : D ≠ CTL := by
      rcases hT with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ <;> decide
    have hDc' : tierA D u ≠ CTL := by
      simpa using (tierA_ne hDl (show CTL < 256 by decide) hDc u 0)
    rw [pushZ_arr m t f a _ hDc' (tierA_ne hDl hRl (Ne.symm hRD) u t) (tierA_ne_tier _ hu ht hut)]
    simp [hut]

set_option linter.unusedSimpArgs false in
/-- **The append, with the new slot zeroed, changes none of `der_b`'s three reads**, for every
handle: a handle other than the new node reads what it read before (another tier's array, or
another index), and the new node reads `0` (before: its index was past the count). -/
theorem der_pushZ (hT : BinTbl R S D k) (ht : t ≤ 1) (hc : rdW (m.arr64 CTL) (k + t) < 134217728)
    (h : Word) :
    derBW (pushZ R S D k m t f a) h = derBW m h ∧ derFW (pushZ R S D k m t f a) h = derFW m h ∧
      exprLPW (pushZ R S D k m t f a) h = exprLPW m h := by
  have hctl := pushZ_ctl m t f a hT ht
  have hid := idxW_lt h
  have htw := tierW_le h
  have hcnt : ∀ X : TRec, tcnt (pushZ R S D k m t f a) X (tierW h) =
      if k + t = X.ca + tierW h ∧ (k + t).toNat < (m.arr64 CTL).size then
        rdW (m.arr64 CTL) (k + t) + 1 else tcnt m X (tierW h) := fun X => by
    simp only [tcnt, hctl]
  have h1 : rdW ((pushZ R S D k m t f a).arr64 CTL) 1 = rdW (m.arr64 CTL) 1 := by
    rw [hctl]
    rcases hT with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
      rcases h01 t ht with rfl | rfl <;> simp
  have key : rdW (m.arr64 CTL) (k + t) ≤ idxW h → ¬rdW (m.arr64 CTL) (k + t) + 1 ≤ idxW h →
      idxW h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (134217728 : Word).toNat = 134217728 from rfl] at *
    omega
  have key2 : idxW h < rdW (m.arr64 CTL) (k + t) + 1 → ¬ idxW h < rdW (m.arr64 CTL) (k + t) →
      idxW h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (134217728 : Word).toNat = 134217728 from rfl] at *
    omega
  have oob : ∀ (b : ArrId) x, ¬x.toNat < (m.arr64 b).size → rdW (m.arr64 b) x = 0 := by
    intro b x hx; simp only [rdW]; grind
  have hRl : R < 256 := by
    rcases hT with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩ <;> decide
  have hDl : D < 256 := by
    rcases hT with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ <;> decide
  have ho : ∀ X : TRec, X.arr < 256 → X.arr ≠ CTL → X.arr ≠ R → X.arr ≠ D → ∀ u i g,
      tfld (pushZ R S D k m t f a) X u i g = tfld m X u i g :=
    fun X h1 h2 h3 h4 => tfld_pushZ_other m t f a X h1 h2 h3 h4 hRl hDl
  have hd : ∀ X : TRec, X.arr = D → X.w = 1 → ∀ i, tfld (pushZ R S D k m t f a) X (tierW h) i 0 =
      if tierW h = t ∧ rdW (m.arr64 CTL) (k + t) = i ∧
          (rdW (m.arr64 CTL) (k + t)).toNat < (m.arr64 (tierA D t)).size then 0
      else tfld m X (tierW h) i 0 :=
    fun X h1 h2 i => tfld_pushZ_der m t f a hT ht X h1 h2 _ htw i
  rcases hT with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    rcases h01 t ht with rfl | rfl
  all_goals simp (config := {decide := true}) only [derBW, derFW, exprLPW, h1, hcnt]
  all_goals simp only [ho BVAR (by decide) (by decide) (by decide) (by decide), ho FVAR (by decide) (by decide) (by decide) (by decide), ho FVAR_LP (by decide) (by decide) (by decide) (by decide), ho SORT_LP (by decide) (by decide) (by decide) (by decide),
    ho CONST_LP (by decide) (by decide) (by decide) (by decide), ho LET_DER (by decide) (by decide) (by decide) (by decide), ho PROJ_DER (by decide) (by decide) (by decide) (by decide)]
  all_goals try simp only [ho APP_DER (by decide) (by decide) (by decide) (by decide)]
  all_goals try simp only [ho LAM_DER (by decide) (by decide) (by decide) (by decide)]
  all_goals try simp only [ho FORALL_DER (by decide) (by decide) (by decide) (by decide)]
  all_goals try simp only [hd APP_DER rfl rfl]
  all_goals try simp only [hd LAM_DER rfl rfl]
  all_goals try simp only [hd FORALL_DER rfl rfl]
  all_goals
    rcases h01 _ htw with e | e <;> simp only [e] <;>
      simp (config := {decide := true}) only [CTL, ADER, LADER, FADER, APP, LAM, FORALL, BVAR,
        FVAR, LET, PROJ, SORT, CONST, UInt64.add_zero, ite_false, ite_true, true_and, false_and,
        and_false, and_true, tcnt, tfld, TRec.ad, TRec.wd, TRec.ex, tierA_zero, tierA_one] at * <;>
      grind (splits := 24)

end pushZ

/-- The index and tier fields of the handle word `G * 2^27 + c` (`G` = tag * 2 + tier). -/
theorem hw_fields (G c : Word) (hc : c < 134217728) :
    idxW (G * 134217728 + c) = c ∧ tierW (G * 134217728 + c) = G % 2 := by
  simp only [UInt64.lt_iff_toNat_lt, show (134217728 : Word).toNat = 134217728 from rfl] at hc
  constructor
  · apply UInt64.toNat_inj.mp
    simp only [idxW, UInt64.toNat_and]
    rw [show (134217727 : Word).toNat = 2 ^ 27 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [UInt64.toNat_add, UInt64.toNat_mul, show (134217728 : Word).toNat = 134217728 from rfl]
    omega
  · apply UInt64.toNat_inj.mp
    simp only [tierW, UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_mul,
      UInt64.toNat_mod, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
      show (134217728 : Word).toNat = 134217728 from rfl, show (2 : Word).toNat = 2 from rfl,
      show (27 : Word).toNat = 27 from rfl, show (1 : Word).toNat = 1 from rfl,
      show 2 ^ (27 % 64) = 134217728 from rfl]
    omega

/-- `der_b`'s three reads do not look at the binary tables' slot arrays (a growth changes only
those, lane slotgrow). -/
theorem der_congr {S : ArrId} (hS : S = ASLOT ∨ S = LASLOT ∨ S = FASLOT) (t : Word) {m₂ m₃ : Mem}
    (hf : ∀ b, b ≠ tierA S t → m₂.arr64 b = m₃.arr64 b) (h : Word) :
    derBW m₂ h = derBW m₃ h ∧ derFW m₂ h = derFW m₃ h ∧ exprLPW m₂ h = exprLPW m₃ h := by
  have hS' : S < 256 := by rcases hS with rfl | rfl | rfl <;> decide
  have hf' : ∀ b : ArrId, b < 256 → b ≠ S → m₂.arr64 b = m₃.arr64 b ∧
      m₂.arr64 (b + 256) = m₃.arr64 (b + 256) := fun b hb hbS =>
    ⟨hf _ (by simpa using tierA_ne hb hS' hbS 0 t), hf _ (by simpa using tierA_ne hb hS' hbS 1 t)⟩
  have e := fun (b : ArrId) (hb : b < 256) (hbS : b ≠ S) => hf' b hb hbS
  rcases hS with rfl | rfl | rfl <;>
  simp only [derBW, derFW, exprLPW, (e CTL (by decide) (by decide)).1,
    tcnt_arr_eq _ (e CTL (by decide) (by decide)).1,
    tfld_arr_eq (R := BVAR) (e BREC (by decide) (by decide)).1 (e BREC (by decide) (by decide)).2,
    tfld_arr_eq (R := APP_DER) (e ADER (by decide) (by decide)).1 (e ADER (by decide) (by decide)).2,
    tfld_arr_eq (R := LAM_DER) (e LADER (by decide) (by decide)).1 (e LADER (by decide) (by decide)).2,
    tfld_arr_eq (R := FORALL_DER) (e FADER (by decide) (by decide)).1 (e FADER (by decide) (by decide)).2,
    tfld_arr_eq (R := LET_DER) (e LEDER (by decide) (by decide)).1 (e LEDER (by decide) (by decide)).2,
    tfld_arr_eq (R := PROJ_DER) (e PJDER (by decide) (by decide)).1 (e PJDER (by decide) (by decide)).2,
    tfld_arr_eq (R := FVAR) (e FVREC (by decide) (by decide)).1 (e FVREC (by decide) (by decide)).2,
    tfld_arr_eq (R := FVAR_LP) (e FVLP (by decide) (by decide)).1 (e FVLP (by decide) (by decide)).2,
    tfld_arr_eq (R := SORT_LP) (e SOLP (by decide) (by decide)).1 (e SOLP (by decide) (by decide)).2,
    tfld_arr_eq (R := CONST_LP) (e CLP (by decide) (by decide)).1 (e CLP (by decide) (by decide)).2,
    and_self]

theorem ainternW_grow {m m₁ : Mem} {f a r : Word} (hI : ainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 4 ≠ cnt2 m 4) :
    ∃ t, t ≤ 1 ∧ acnt m t < 134217728 ∧
      (∀ b, b ≠ tierA ASLOT t → m₁.arr64 b = (pushRec appCS m t [f, a]).arr64 b) ∧
      idxW r = acnt m t ∧ tierW r = t := by
  rcases consInternM_outA (C := appCS) (by decide) (fun A h => by simp [appCS] at h)
    ⟨by decide, fun A h => by simp [appCS] at h⟩ hI with
    rfl | ⟨t, ht, hok, rfl, he, -, -⟩
  · exact absurd rfl hc
  have h : acnt m t < 134217728 := by
    rw [← apushOK_eqC] at hok
    simp only [apushOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  refine ⟨t, ht, h, he, ?_⟩
  rcases h01 t ht with rfl | rfl
  · rw [show appCS.P = 8 * 134217728 from rfl]; exact hw_fields _ _ h
  · rw [show appCS.S = 9 * 134217728 from rfl]; exact hw_fields _ _ h

/-- After a miss of `intern_app` (the counts changed), the zeroed slot hides the append from
`der_b`'s three reads. -/
theorem ainternW_der {m m₁ : Mem} {f a r q u : Word} (hI : ainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 4 ≠ cnt2 m 4)
    (hq : q = r &&& (134217727 : Word)) (hu : u = (r >>> (27 : Word)) &&& 1) (x : Word) :
    derBW (m₁.set64 (tierA ADER u) q 0) x = derBW m x ∧
      derFW (m₁.set64 (tierA ADER u) q 0) x = derFW m x ∧
      exprLPW (m₁.set64 (tierA ADER u) q 0) x = exprLPW m x := by
  obtain ⟨t, ht, hc', he, hi, htr⟩ := ainternW_grow hI hc
  simp only [idxW, tierW] at hi htr
  rw [hq, hu, hi, htr]
  have ez : (pushRec appCS m t [f, a]).set64 (tierA ADER t) (acnt m t) 0 =
      pushZ AREC ASLOT ADER 4 m t f a := by
    simp only [pushRec, colW, appCS, cntC, acnt, pushZ, pushArgs]; rfl
  obtain ⟨e1, e2, e3⟩ := der_congr (.inl rfl) t
    (fun b hb => (OutSa.set64 (fun b hb => he b hb)
      (tierA_ne (a := ADER) (b := ASLOT) (by decide) (by decide) (by decide) t t) _ _ b hb).trans
      (by rw [ez])) x
  obtain ⟨f1, f2, f3⟩ := der_pushZ (R := AREC) (S := ASLOT) (D := ADER) (k := 4) m t f a
    (.inl ⟨rfl, rfl, rfl, rfl⟩) ht hc' x
  exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩

grind_pattern [arena_grind] ainternW_der => ainternW m f a, (r, m₁), derBW (Mem.set64 m₁ (tierA ADER u) q 0) x

theorem lainternW_grow {m m₁ : Mem} {f a r : Word} (hI : lainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 28 ≠ cnt2 m 28) :
    ∃ t, t ≤ 1 ∧ lacnt m t < 134217728 ∧
      (∀ b, b ≠ tierA LASLOT t → m₁.arr64 b = (pushRec lamCS m t [f, a]).arr64 b) ∧
      idxW r = lacnt m t ∧ tierW r = t := by
  rcases consInternM_outA (C := lamCS) (by decide) (fun A h => by simp [lamCS] at h)
    ⟨by decide, fun A h => by simp [lamCS] at h⟩ hI with
    rfl | ⟨t, ht, hok, rfl, he, -, -⟩
  · exact absurd rfl hc
  have h : lacnt m t < 134217728 := by
    rw [← lapushOK_eqC] at hok
    simp only [lapushOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  refine ⟨t, ht, h, he, ?_⟩
  rcases h01 t ht with rfl | rfl
  · rw [show lamCS.P = 10 * 134217728 from rfl]; exact hw_fields _ _ h
  · rw [show lamCS.S = 11 * 134217728 from rfl]; exact hw_fields _ _ h

/-- After a miss of `intern_lam` (the counts changed), the zeroed slot hides the append from
`der_b`'s three reads. -/
theorem lainternW_der {m m₁ : Mem} {f a r q u : Word} (hI : lainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 28 ≠ cnt2 m 28)
    (hq : q = r &&& (134217727 : Word)) (hu : u = (r >>> (27 : Word)) &&& 1) (x : Word) :
    derBW (m₁.set64 (tierA LADER u) q 0) x = derBW m x ∧
      derFW (m₁.set64 (tierA LADER u) q 0) x = derFW m x ∧
      exprLPW (m₁.set64 (tierA LADER u) q 0) x = exprLPW m x := by
  obtain ⟨t, ht, hc', he, hi, htr⟩ := lainternW_grow hI hc
  simp only [idxW, tierW] at hi htr
  rw [hq, hu, hi, htr]
  have ez : (pushRec lamCS m t [f, a]).set64 (tierA LADER t) (lacnt m t) 0 =
      pushZ LAREC LASLOT LADER 28 m t f a := by
    simp only [pushRec, colW, lamCS, cntC, lacnt, pushZ, pushArgs]; rfl
  obtain ⟨e1, e2, e3⟩ := der_congr (.inr (.inl rfl)) t
    (fun b hb => (OutSa.set64 (fun b hb => he b hb)
      (tierA_ne (a := LADER) (b := LASLOT) (by decide) (by decide) (by decide) t t) _ _ b hb).trans
      (by rw [ez])) x
  obtain ⟨f1, f2, f3⟩ := der_pushZ (R := LAREC) (S := LASLOT) (D := LADER) (k := 28) m t f a
    (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)) ht hc' x
  exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩

grind_pattern [arena_grind] lainternW_der => lainternW m f a, (r, m₁), derBW (Mem.set64 m₁ (tierA LADER u) q 0) x

theorem fainternW_grow {m m₁ : Mem} {f a r : Word} (hI : fainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 30 ≠ cnt2 m 30) :
    ∃ t, t ≤ 1 ∧ facnt m t < 134217728 ∧
      (∀ b, b ≠ tierA FASLOT t → m₁.arr64 b = (pushRec forallCS m t [f, a]).arr64 b) ∧
      idxW r = facnt m t ∧ tierW r = t := by
  rcases consInternM_outA (C := forallCS) (by decide) (fun A h => by simp [forallCS] at h)
    ⟨by decide, fun A h => by simp [forallCS] at h⟩ hI with
    rfl | ⟨t, ht, hok, rfl, he, -, -⟩
  · exact absurd rfl hc
  have h : facnt m t < 134217728 := by
    rw [← fapushOK_eqC] at hok
    simp only [fapushOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  refine ⟨t, ht, h, he, ?_⟩
  rcases h01 t ht with rfl | rfl
  · rw [show forallCS.P = 12 * 134217728 from rfl]; exact hw_fields _ _ h
  · rw [show forallCS.S = 13 * 134217728 from rfl]; exact hw_fields _ _ h

/-- After a miss of `intern_forall` (the counts changed), the zeroed slot hides the append from
`der_b`'s three reads. -/
theorem fainternW_der {m m₁ : Mem} {f a r q u : Word} (hI : fainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 30 ≠ cnt2 m 30)
    (hq : q = r &&& (134217727 : Word)) (hu : u = (r >>> (27 : Word)) &&& 1) (x : Word) :
    derBW (m₁.set64 (tierA FADER u) q 0) x = derBW m x ∧
      derFW (m₁.set64 (tierA FADER u) q 0) x = derFW m x ∧
      exprLPW (m₁.set64 (tierA FADER u) q 0) x = exprLPW m x := by
  obtain ⟨t, ht, hc', he, hi, htr⟩ := fainternW_grow hI hc
  simp only [idxW, tierW] at hi htr
  rw [hq, hu, hi, htr]
  have ez : (pushRec forallCS m t [f, a]).set64 (tierA FADER t) (facnt m t) 0 =
      pushZ FAREC FASLOT FADER 30 m t f a := by
    simp only [pushRec, colW, forallCS, cntC, facnt, pushZ, pushArgs]; rfl
  obtain ⟨e1, e2, e3⟩ := der_congr (.inr (.inr rfl)) t
    (fun b hb => (OutSa.set64 (fun b hb => he b hb)
      (tierA_ne (a := FADER) (b := FASLOT) (by decide) (by decide) (by decide) t t) _ _ b hb).trans
      (by rw [ez])) x
  obtain ⟨f1, f2, f3⟩ := der_pushZ (R := FAREC) (S := FASLOT) (D := FADER) (k := 30) m t f a
    (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩)) ht hc' x
  exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩

grind_pattern [arena_grind] fainternW_der => fainternW m f a, (r, m₁), derBW (Mem.set64 m₁ (tierA FADER u) q 0) x

/-! ## `mk_app(f, a)` -/

/-- **The model of `mk_app`.** The written word packs both ranges (`packBF`): `der_b` reads it
back apart. -/
def mkAppW (m : Mem) (f a : Word) : Option (Word × Mem) :=
  if (f ||| a) >>> 32 ≠ 0 then none
  else mkK ADER 4 (cnt2 m 4)
    (packBFL (maxW (derBW m f) (derBW m a)) (maxW (derFW m f) (derFW m a))
      (exprLPW m f ||| exprLPW m a)) (ainternW m f a)

/-- con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
def mkApp : FunDecl := lfn (f, a) locals (x, y, s, r, q, xf, yf, xl, yl, tr) {
  if (f | a) >> 32 != 0 { abort };
  s := CTL.u64[4] + CTL.u64[5];
  r := call intern_app(f, a);
  if CTL.u64[4] + CTL.u64[5] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(ADER⟨tr⟩) <= q { abort };
    ADER⟨tr⟩[q] := 0;
    (x, xf, xl) := call der_b(f);
    (y, yf, yl) := call der_b(a);
    ADER⟨tr⟩[q] := x + (y - x) * u64(x < y) + (xf + (yf - xf) * u64(xf < yf)) * 32768 + (xl | yl) * 1073741824
  };
  return r
}

/-! ## `mk_lam(ty, body)`, `mk_forall(ty, body)` -/

/-- **The model of `mk_lam`.** The fvar range is NOT `satPred`'d across the binder (a `fvar` is
not de Bruijn, so the binder does not shift it; con-ron's `derOfBind`, `Store.lean`). -/
def mkLamW (m : Mem) (t b : Word) : Option (Word × Mem) :=
  if (t ||| b) >>> 32 ≠ 0 then none
  else mkK LADER 28 (cnt2 m 28)
    (packBFL (maxW (derBW m t) (satPredW (derBW m b))) (maxW (derFW m t) (derFW m b))
      (exprLPW m t ||| exprLPW m b))
    (lainternW m t b)

/-- con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
def mkLam : FunDecl := lfn (t, b) locals (x, y, s, r, q, xf, yf, xl, yl, tr) {
  if (t | b) >> 32 != 0 { abort };
  s := CTL.u64[28] + CTL.u64[29];
  r := call intern_lam(t, b);
  if CTL.u64[28] + CTL.u64[29] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(LADER⟨tr⟩) <= q { abort };
    LADER⟨tr⟩[q] := 0;
    (x, xf, xl) := call der_b(t);
    (y, yf, yl) := call der_b(b);
    y := y - u64(0 < y) + u64(y == 32767);
    LADER⟨tr⟩[q] := x + (y - x) * u64(x < y) + (xf + (yf - xf) * u64(xf < yf)) * 32768 + (xl | yl) * 1073741824
  };
  return r
}

/-- **The model of `mk_forall`.** -/
def mkForallW (m : Mem) (t b : Word) : Option (Word × Mem) :=
  if (t ||| b) >>> 32 ≠ 0 then none
  else mkK FADER 30 (cnt2 m 30)
    (packBFL (maxW (derBW m t) (satPredW (derBW m b))) (maxW (derFW m t) (derFW m b))
      (exprLPW m t ||| exprLPW m b))
    (fainternW m t b)

/-- con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
def mkForall : FunDecl := lfn (t, b) locals (x, y, s, r, q, xf, yf, xl, yl, tr) {
  if (t | b) >> 32 != 0 { abort };
  s := CTL.u64[30] + CTL.u64[31];
  r := call intern_forall(t, b);
  if CTL.u64[30] + CTL.u64[31] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(FADER⟨tr⟩) <= q { abort };
    FADER⟨tr⟩[q] := 0;
    (x, xf, xl) := call der_b(t);
    (y, yf, yl) := call der_b(b);
    y := y - u64(0 < y) + u64(y == 32767);
    FADER⟨tr⟩[q] := x + (y - x) * u64(x < y) + (xf + (yf - xf) * u64(xf < yf)) * 32768 + (xl | yl) * 1073741824
  };
  return r
}

/-! ## `mk_let(ty, val, body)` -/

/-- **The model of `mk_let`.** -/
def mkLetW (m : Mem) (t v b : Word) : Option (Word × Mem) :=
  if (t ||| v ||| b) >>> 32 ≠ 0 then none
  else mkK LEDER 20 (cnt2 m 20)
    (packBFL (maxW (maxW (derBW m t) (derBW m v)) (satPredW (derBW m b)))
      (maxW (maxW (derFW m t) (derFW m v)) (derFW m b))
      (exprLPW m t ||| exprLPW m v ||| exprLPW m b))
    (leinternW m t v b)

/-- con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
def mkLet : FunDecl := lfn (t, v, b) locals (x, y, z, s, r, q, xf, yf, zf, xl, yl, zl, tr) {
  if (t | v | b) >> 32 != 0 { abort };
  (x, xf, xl) := call der_b(t);
  (y, yf, yl) := call der_b(v);
  (z, zf, zl) := call der_b(b);
  s := CTL.u64[20] + CTL.u64[21];
  r := call intern_letE(t, v, b);
  if CTL.u64[20] + CTL.u64[21] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(LEDER⟨tr⟩) <= q { abort };
    x := x + (y - x) * u64(x < y);
    z := z - u64(0 < z) + u64(z == 32767);
    xf := xf + (yf - xf) * u64(xf < yf);
    LEDER⟨tr⟩[q] := x + (z - x) * u64(x < z) + (xf + (zf - xf) * u64(xf < zf)) * 32768 + (xl | yl | zl) * 1073741824
  };
  return r
}

/-! ## `mk_proj(n, i, e)` -/

/-- **The model of `mk_proj`.** -/
def mkProjW (m : Mem) (n i e : Word) : Option (Word × Mem) :=
  if (n ||| e) >>> 32 ≠ 0 then none
  else mkK PJDER 32 (cnt2 m 32) (packBFL (derBW m e) (derFW m e) (exprLPW m e)) (pjinternW m n i e)

/-- con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
def mkProj : FunDecl := lfn (n, i, e) locals (x, s, r, q, xf, xl, tr) {
  if (n | e) >> 32 != 0 { abort };
  (x, xf, xl) := call der_b(e);
  s := CTL.u64[32] + CTL.u64[33];
  r := call intern_proj(n, i, e);
  if CTL.u64[32] + CTL.u64[33] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(PJDER⟨tr⟩) <= q { abort };
    PJDER⟨tr⟩[q] := x + xf * 32768 + xl * 1073741824
  };
  return r
}

/-! ## The store arithmetic as named functions

The `mk_*` stores compute `maxW`, `satPredW` and `packBF` inline; these equations name the evaluated
L expressions, so `finish` matches them instead of unfolding the arithmetic (and case-splitting on
its comparisons) inside every spec (lane `exprops4`: `mkLet_spec` went from > 10 min to seconds). -/

theorem maxW_L (x y : Word) :
    BinOp.add.eval x (BinOp.mul.eval (BinOp.sub.eval y x) (Cmp.ult.evalW x y)) = maxW x y := by
  simp [BinOp.eval, Cmp.evalW, Cmp.eval, maxW]

theorem satPredW_L (y : Word) :
    BinOp.add.eval (BinOp.sub.eval y (Cmp.ult.evalW 0 y)) (Cmp.eq.evalW y 32767) = satPredW y := by
  simp [BinOp.eval, Cmp.evalW, Cmp.eval, satPredW]

theorem packBF_L (b f : Word) : BinOp.add.eval b (BinOp.mul.eval f 32768) = packBF b f := rfl

theorem packBFL_L (b f l : Word) :
    BinOp.add.eval (packBF b f) (BinOp.mul.eval l 1073741824) = packBFL b f l := rfl

/-! ## The specs -/


section specs
variable (p : Prog) (hd : p.lookup "der_b" = some derB)

include hd in
theorem mkApp_spec (hpf : p.lookup "app_find" = some appFind)
    (hpp : p.lookup "app_push" = some appPush) (hpi : p.lookup "intern_app" = some internApp)
    (hp : p.lookup "mk_app" = some mkApp) (n : Nat) (s₀ : St) (f a : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_app" [f, a]
    ⦃fun r s' => LocEq s' s₀ ∧ mkAppW s₀.mem f a = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkApp]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
        derB_spec p hd n, internApp_spec p hpf hpp hpi n] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [Mem.set64_set64_same, mkAppW, maxW_L, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

include hd in
theorem mkLam_spec (hpf : p.lookup "lam_find" = some lamFind)
    (hpp : p.lookup "lam_push" = some lamPush) (hpi : p.lookup "intern_lam" = some internLamL)
    (hp : p.lookup "mk_lam" = some mkLam) (n : Nat) (s₀ : St) (t b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_lam" [t, b]
    ⦃fun r s' => LocEq s' s₀ ∧ mkLamW s₀.mem t b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkLam]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
        derB_spec p hd n, internLamL_spec p hpf hpp hpi n] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [Mem.set64_set64_same, mkLamW, maxW_L, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

include hd in
theorem mkForall_spec (hpf : p.lookup "forall_find" = some forallFind)
    (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
    (hp : p.lookup "mk_forall" = some mkForall) (n : Nat) (s₀ : St) (t b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_forall" [t, b]
    ⦃fun r s' => LocEq s' s₀ ∧ mkForallW s₀.mem t b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkForall]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
        derB_spec p hd n, internForallL_spec p hpf hpp hpi n] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [Mem.set64_set64_same, mkForallW, maxW_L, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

include hd in
theorem mkLet_spec (hpf : p.lookup "letE_find" = some letFind)
    (hpp : p.lookup "letE_push" = some letPush) (hpi : p.lookup "intern_letE" = some internLet)
    (hp : p.lookup "mk_let" = some mkLet) (n : Nat) (s₀ : St) (t v b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_let" [t, v, b]
    ⦃fun r s' => LocEq s' s₀ ∧ mkLetW s₀.mem t v b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkLet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
        derB_spec p hd n, internLet_spec p hpf hpp hpi n] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [mkLetW, maxW_L, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

include hd in
theorem mkProj_spec (hpf : p.lookup "proj_find" = some projFind)
    (hpp : p.lookup "proj_push" = some projPush) (hpi : p.lookup "intern_proj" = some internProj)
    (hp : p.lookup "mk_proj" = some mkProj) (n : Nat) (s₀ : St) (nm i e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mk_proj" [nm, i, e]
    ⦃fun r s' => LocEq s' s₀ ∧ mkProjW s₀.mem nm i e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkProj]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
        derB_spec p hd n, internProj_spec p hpf hpp hpi n] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [mkProjW, maxW_L, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

end specs

end L.Arena
