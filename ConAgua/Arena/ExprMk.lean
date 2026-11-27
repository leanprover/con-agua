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
import ConAgua.Arena.LdRd
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.L.WordOff
import ConAgua.Arena.StoreRel

@[expose] public section

/-!
# The derived loose-bvar range of expression nodes, and the `mk_*` constructors that keep it

con-ron's store keeps a **derived word** per node (`Tbl.der`, `EStore.derived`, `derOfView`):
a 32-bit hash, the loose-bvar range, the fvar range and a level-param flag, packed
(`packData`). The expression walks read its range field before anything else
(`liftLooseBVarsGo`, `instantiate1Go`, … cut off at `bvarOfData (derived h) ≤ c`), so L must know
it exactly. L keeps **the range fields and the level-parameter bit** (the hash, `mix32` of the children's hashes, is
opaque: no verdict reads the hash bits, only a parent's hash does); for the five compound tables in one tiered array per table,
as packed 32-bit elements (two per word, `Arena/P32.lean`: `A⟨t⟩.u32[i]`, read as `pcol m A t i`),
element `i` of tier `t` the derived word of node `i`, packed by `packBFL` (bvar range bits 0‥14, fvar range 15‥29, `lp` bit 30;
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
`0` for a handle that does not view (scratch tier closed, index past the count, unknown tag), with
the fvar range and the level-parameter bit; `der_bv(h)` returns the range field alone, for the
walks' cut-offs.

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
  else if tagW h = 0 then
    if tcnt m BVAR (tierW h) ≤ idxW h then 0
    else satSuccW (tfld m BVAR (tierW h) (idxW h) 0)
  else if tagW h = 4 then
    if tcnt m APP (tierW h) ≤ idxG h then 0
    else pcol m ADER (tierW h) (idxG h) &&& 32767
  else if tagW h = 5 then
    if tcnt m LAM (tierW h) ≤ idxW h then 0
    else pcol m LADER (tierW h) (idxW h) &&& 32767
  else if tagW h = 6 then
    if tcnt m FORALL (tierW h) ≤ idxW h then 0
    else pcol m FADER (tierW h) (idxW h) &&& 32767
  else if tagW h = 7 then
    if tcnt m LET (tierW h) ≤ idxW h then 0
    else pcol m LEDER (tierW h) (idxW h) &&& 32767
  else if tagW h = 9 then
    if tcnt m PROJ (tierW h) ≤ idxW h then 0
    else pcol m PJDER (tierW h) (idxW h) &&& 32767
  else 0

/-- **The model of the second result of `der_b`: the fvar range** (lane `exprops3`). `bvar`/`sort`/
`const`/`lit` have no free variables (`0`); `fvar`'s own range is `satSucc` of its own index
(`FVREC`, as the `bvar` arm reads `BREC`: the record alone determines it); the five compound arms
read the SAME packed word shifted and masked (`(>> 15) & 32767` is `packBFL_fvar`). -/
def derFW (m : Mem) (h : Word) : Word :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then 0
  else if tagW h = 1 then
    if tcnt m FVAR (tierW h) ≤ idxW h then 0
    else satSuccW (tfld m FVAR (tierW h) (idxW h) 0)
  else if tagW h = 4 then
    if tcnt m APP (tierW h) ≤ idxG h then 0
    else (pcol m ADER (tierW h) (idxG h) >>> 15) &&& 32767
  else if tagW h = 5 then
    if tcnt m LAM (tierW h) ≤ idxW h then 0
    else (pcol m LADER (tierW h) (idxW h) >>> 15) &&& 32767
  else if tagW h = 6 then
    if tcnt m FORALL (tierW h) ≤ idxW h then 0
    else (pcol m FADER (tierW h) (idxW h) >>> 15) &&& 32767
  else if tagW h = 7 then
    if tcnt m LET (tierW h) ≤ idxW h then 0
    else (pcol m LEDER (tierW h) (idxW h) >>> 15) &&& 32767
  else if tagW h = 9 then
    if tcnt m PROJ (tierW h) ≤ idxW h then 0
    else (pcol m PJDER (tierW h) (idxW h) >>> 15) &&& 32767
  else 0

/-- con-ron: none — reads L's derived-range array (the twin's `bvarOfData (derived h)`); returns the
bvar range and, as a second result, the fvar range (`derFW`; lane `exprops3`), as a third the
level-parameter bit (`exprLPW`, the twin's `lpOfData (derived h)`; helper `whnf4-d23`). The tags
are tested in order of frequency on Init (`app` 4, `bvar` 0, `const` 3, `lam` 5, `fvar` 1, `forallE` 6,
`sort` 2, `proj` 9, `letE` 7; lane `derb`); the tests are disjoint, so the order changes no result. -/
@[no_expose] def derB : FunDecl := lfn (h) locals (g, t, i, x) {
  g := ⟦h⟧.tag;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { return (0, 0, 0) };
  if g == 4 { i := ⟦h⟧.gidx; if APP⟨t⟩.count <= i { return (0, 0, 0) }; x := ADER⟨t⟩.u32[i]; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  if g == 0 {
    if BVAR⟨t⟩.count <= i { return (0, 0, 0) };
    x := BVAR⟨t, i⟩.i;
    if x < 32767 { return (x + 1, 0, 0) };
    return (32767, 0, 0)
  };
  if g == 3 { if CONST⟨t⟩.count <= i { return (0, 0, 0) }; return (0, 0, CONST_LP⟨t, i⟩) };
  if g == 5 { if LAM⟨t⟩.count <= i { return (0, 0, 0) }; x := LADER⟨t⟩.u32[i]; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { return (0, 0, 0) };
    x := FVAR⟨t, i⟩.i;
    if x < 32767 { return (0, x + 1, FVAR_LP⟨t, i⟩) };
    return (0, 32767, FVAR_LP⟨t, i⟩)
  };
  if g == 6 { if FORALL⟨t⟩.count <= i { return (0, 0, 0) }; x := FADER⟨t⟩.u32[i]; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  if g == 2 { if SORT⟨t⟩.count <= i { return (0, 0, 0) }; return (0, 0, SORT_LP⟨t, i⟩) };
  if g == 9 { if PROJ⟨t⟩.count <= i { return (0, 0, 0) }; x := PJDER⟨t⟩.u32[i]; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  if g == 7 { if LET⟨t⟩.count <= i { return (0, 0, 0) }; x := LEDER⟨t⟩.u32[i]; return (x & 32767, (x >> 15) & 32767, x >> 30) };
  return (0, 0, 0)
}

/-- con-ron: none — `der_b`'s first result alone (`derBW`), for the expression walks that read only
the bvar range (`il_go`, `ilg_go`, `il_bvar`, `inst_go`, `lift_go`, `bvar_b`): one result
register, and the `const`, `fvar` and `sort` arms fall through to the final `0` without a read.
The `bvar` arm saturates by a branch, as `der_b`'s does. -/
@[no_expose] def derBv : FunDecl := lfn (h) locals (g, t, i, x) {
  g := ⟦h⟧.tag;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { return 0 };
  if g == 4 { i := ⟦h⟧.gidx; if APP⟨t⟩.count <= i { return 0 }; x := ADER⟨t⟩.u32[i]; return x & 32767 };
  if g == 0 {
    if BVAR⟨t⟩.count <= i { return 0 };
    x := BVAR⟨t, i⟩.i;
    if x < 32767 { return x + 1 };
    return 32767
  };
  if g == 5 { if LAM⟨t⟩.count <= i { return 0 }; x := LADER⟨t⟩.u32[i]; return x & 32767 };
  if g == 6 { if FORALL⟨t⟩.count <= i { return 0 }; x := FADER⟨t⟩.u32[i]; return x & 32767 };
  if g == 9 { if PROJ⟨t⟩.count <= i { return 0 }; x := PJDER⟨t⟩.u32[i]; return x & 32767 };
  if g == 7 { if LET⟨t⟩.count <= i { return 0 }; x := LEDER⟨t⟩.u32[i]; return x & 32767 };
  return 0
}

/-- `der_b` after its three decodes (`g`, `t`, `i`): the dispatch. -/
def derTailS : Stmt := seqDrop 3 derB.body

/-- The decoded locals of `der_b`. -/
def DerLocs (s : St) : Prop :=
  s.loc 1 = tagW (s.loc 0) ∧ s.loc 2 = tierW (s.loc 0) ∧ s.loc 3 = idxW (s.loc 0)

theorem derTail_spec (p : Prog) (n : Nat) (s₁ : St) (hL : DerLocs s₁) :
    ⦃fun s => s = s₁⦄ step p (exec p n) derTailS
    ⦃fun r s' => s'.mem = s₁.mem ∧ r.retVal.headD 0 = derBW s₁.mem (s₁.loc 0) ∧
      r.retVal.tail.headD 0 = derFW s₁.mem (s₁.loc 0) ∧
      r.retVal.tail.tail.headD 0 = exprLPW s₁.mem (s₁.loc 0); ⊤⦄ := by
  obtain ⟨h1, h2, h3⟩ := hL
  simp only [derTailS, derB, seqDrop]
  vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, ld32_pcol_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  all_goals subst_vars
  all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq, h1, h2, h3] at *)
  all_goals (try simp_all [derBW, derFW, exprLPW, BVAR, APP, LAM, FORALL, LET, PROJ, FVAR, FVAR_LP, SORT, SORT_LP, CONST, CONST_LP, Sig.retVal, Sig.retOr])
  all_goals grind [lang_grind, arena_grind, derBW, derFW, exprLPW, tierW, idxW, satSuccW]

/-- **`der_b`**: the three decodes, then the dispatch (`derTail_spec`, over the named locals:
its 160 goals see `g`, `t`, `i` as `DerLocs`, not as the decodes' `setLoc` chain; 18 s -> 5 s). -/
theorem derB_spec (p : Prog) (hp : p.lookup "der_b" = some derB) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "der_b" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = derBW s₀.mem h ∧
      r.tail.headD 0 = derFW s₀.mem h ∧ r.tail.tail.headD 0 = exprLPW s₀.mem h; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn]
  cases n with
  | zero => simp only [derB]; vcgen [exec] <;> grind
  | succ n =>
    rw [← seqTake_drop 3 derB.body, show seqDrop 3 derB.body = derTailS from rfl]
    simp only [derB, seqTake]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, derTail_spec p n]
    all_goals subst_vars
    all_goals (try simp only [DerLocs, St.setLoc_loc, L.St.setLoc_mem, Nat.reduceEqDiff,
      Locals.init_cons_zero, reduceIte] at *)
    all_goals grind [lang_grind, arena_grind, LocEq]

/-- `der_bv` after its three decodes: the dispatch. -/
def derBvTailS : Stmt := seqDrop 3 derBv.body

theorem derBvTail_spec (p : Prog) (n : Nat) (s₁ : St) (hL : DerLocs s₁) :
    ⦃fun s => s = s₁⦄ step p (exec p n) derBvTailS
    ⦃fun r s' => s'.mem = s₁.mem ∧ r.retVal.headD 0 = derBW s₁.mem (s₁.loc 0); ⊤⦄ := by
  obtain ⟨h1, h2, h3⟩ := hL
  simp only [derBvTailS, derBv, seqDrop]
  vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, ld32_pcol_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  all_goals subst_vars
  all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval,
      reduceIte, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq, h1, h2, h3] at *)
  all_goals grind [lang_grind, arena_grind, derBW, tierW, idxW, satSuccW, Sig.retVal, Sig.retOr]

/-- **`der_bv`**: `der_b`'s first result (`derB_spec`'s first conjunct), with `derB_spec`'s
structure: the three decodes, then the dispatch (`derBvTail_spec`). -/
theorem derBv_spec (p : Prog) (hp : p.lookup "der_bv" = some derBv) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "der_bv" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = derBW s₀.mem h; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn]
  cases n with
  | zero => simp only [derBv]; vcgen [exec] <;> grind
  | succ n =>
    rw [← seqTake_drop 3 derBv.body, show seqDrop 3 derBv.body = derBvTailS from rfl]
    simp only [derBv, seqTake]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, derBvTail_spec p n]
    all_goals subst_vars
    all_goals (try simp only [DerLocs, St.setLoc_loc, L.St.setLoc_mem, Nat.reduceEqDiff,
      Locals.init_cons_zero, reduceIte] at *)
    all_goals grind [lang_grind, arena_grind, LocEq]

attribute [arena_grind =] mkK_some

/-! ## The memory after an append, as `der_b` reads it

`mk_app`/`mk_lam`/`mk_forall` read the children's ranges only after `intern_*` appended a node
(as the twin's `EStore.intern` computes `derOfView` only on a miss), so they read the memory
AFTER the append. Before reading, they zero the new node's range slot: then every handle reads
the same range, fvar range and level-parameter bit as before the append, the new node itself
included (before: past the count, `0`; after: the zeroed slot, `0`). -/

theorem Mem.set64_set64_same (m : Mem) (a : TieredArray) (i v w : Word) :
    (m.set64 a i v).set64 a i w = m.set64 a i w := by
  simp only [Mem.set64, Mem.mk.injEq, true_and, and_true]
  funext s'
  by_cases h : s' = a
  · subst h
    simp [Mem.arr64, Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
  · simp [h]

theorem setHalf32_setHalf32 (w i u v : Word) : setHalf32 (setHalf32 w i u) i v = setHalf32 w i v := by
  apply UInt64.toNat_inj.mp
  have := w.toNat_lt; have := u.toNat_lt; have := v.toNat_lt
  simp only [setHalf32_toNat]
  split <;> omega

/-- A second 32-bit store to the same element replaces the first. -/
theorem Mem.set32_set32_same (m : Mem) (A : TieredArray) (i u v : Word) :
    (m.set32 A i u).set32 A i v = m.set32 A i v := by
  simp only [Mem.set32]
  by_cases h : (i / 2).toNat < (m.arr64 A).size
  · rw [Mem.arr64_set64_same, Mem.set64_set64_same]
    have h2 : i.toNat / 2 < (m.arr64 A).size := by simpa [UInt64.toNat_div] using h
    have hv : setHalf32 (((m.arr64 A).set! (i / 2).toNat
        (setHalf32 ((m.arr64 A).getD (i / 2).toNat 0) i u)).getD (i / 2).toNat 0) i v =
        setHalf32 ((m.arr64 A).getD (i / 2).toNat 0) i v := by
      simp [Array.getD, h2, setHalf32_setHalf32]
    rw [hv]
  · have e : ∀ x, m.set64 A (i / 2) x = m := fun x => by
      simp only [Mem.set64, Array.set!_eq_setIfInBounds, Array.setIfInBounds, h, ↓reduceDIte]
      cases m; simp only [Mem.mk.injEq, and_true, true_and]; funext s'; split <;> simp_all [Mem.arr64]
    rw [e, e]

theorem slot_eq_iff {i c t u : Word} (hi : i < 2147483648) (hc : c < 2147483648) (ht : t ≤ 1)
    (hu : u ≤ 1) : i * 2 + t = c * 2 + u ↔ i = c ∧ t = u := by
  constructor
  · intro h
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.toNat_mul, show (2 : Word).toNat = 2 from rfl, show (1 : Word).toNat = 1 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  · rintro ⟨rfl, rfl⟩; rfl

/-- The memory after appending node `c = CTL[k + t]` to a binary table (records `R`, one packed
word `f | a << 32` per node; slot array `S`, range words `D`, each tiered), outside the slot
array (the library's `pushRec`), with the new node's range slot zeroed. -/
def pushZ (R _S D : ArrId) (k : Word) (m : Mem) (t f a : Word) : Mem :=
  let c := rdW (m.arr64 CTL) (k + t)
  (((m.set64 (tierA R t) (c * 1 + 0) (f ||| a <<< 32)).set64 CTL (k + (t &&& 1))
    (c + 1)).set32 (tierA D t) c 0)

/-- The three binary tables `mk_*` read lazily. -/
def BinTbl (R S D : ArrId) (k : Word) : Prop :=
  (R = AREC ∧ S = ASLOT ∧ D = ADER ∧ k = 4) ∨ (R = LAREC ∧ S = LASLOT ∧ D = LADER ∧ k = 28) ∨
    (R = FAREC ∧ S = FASLOT ∧ D = FADER ∧ k = 30)

section pushZ
variable {R S D : ArrId} {k : Word} (m : Mem) (t f a : Word)

theorem pushZ_arr (b : TieredArray) (h1 : b ≠ CTL) (h2 : b ≠ tierA R t) (h4 : b ≠ tierA D t) :
    (pushZ R S D k m t f a).arr64 b = m.arr64 b := by
  simp [pushZ, Mem.arr64_set64_ne, Mem.arr64_set32_ne, *]

theorem pushZ_ctl (hT : BinTbl R S D k) (ht : t ≤ 1) (x : Word) :
    rdW ((pushZ R S D k m t f a).arr64 CTL) x =
      if k + t = x ∧ (k + t).toNat < (m.arr64 CTL).size then rdW (m.arr64 CTL) (k + t) + 1
      else rdW (m.arr64 CTL) x := by
  rcases hT with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl <;>
  simp [pushZ, Mem.arr64_set64_ne, Mem.arr64_set32_ne, L.Arena.rdW_set64, CTL, ADER, AREC, LADER, LAREC,
    FADER, FAREC]

theorem pushZ_der (hT : BinTbl R S D k) (ht : t ≤ 1) (x : Word) :
    p32Get ((pushZ R S D k m t f a).arr64 (tierA D t)) x =
      if rdW (m.arr64 CTL) (k + t) = x ∧
          (rdW (m.arr64 CTL) (k + t) / 2).toNat < (m.arr64 (tierA D t)).size then 0
      else p32Get (m.arr64 (tierA D t)) x := by
  rcases hT with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl <;>
  simp [pushZ, p32Get_set32, Mem.arr64_set64_ne, CTL, ADER, AREC, LADER, LAREC,
    FADER, FAREC]

/-- A field of a store other than the pushed table's records and range column is unchanged. -/
theorem tfld_pushZ_other (X : TRec) (hc : X.arr ≠ CTL) (hR : X.arr ≠ R)
    (hD : X.arr ≠ D) (u i g : Word) :
    tfld (pushZ R S D k m t f a) X u i g = tfld m X u i g := by
  simp only [tfld]
  rw [pushZ_arr m t f a _ (ne_tierA (Ne.symm hc) u).symm (L.tierA_ne_tierA hR u t) (L.tierA_ne_tierA hD u t)]

/-- An element of a packed column other than the pushed table's range column is unchanged. -/
theorem pcol_pushZ_other (A : ArrId) (hc : A ≠ CTL) (hR : A ≠ R) (hD : A ≠ D) (u i : Word) :
    pcol (pushZ R S D k m t f a) A u i = pcol m A u i := by
  simp only [pcol]
  rw [pushZ_arr m t f a _ (ne_tierA (Ne.symm hc) u).symm (L.tierA_ne_tierA hR u t) (L.tierA_ne_tierA hD u t)]

/-- An element of the pushed table's range column: the new node's is `0`, the others as before. -/
theorem pcol_pushZ_der (hT : BinTbl R S D k) (ht : t ≤ 1) (u : Word) (hu : u ≤ 1) (i : Word) :
    pcol (pushZ R S D k m t f a) D u i =
      if u = t ∧ rdW (m.arr64 CTL) (k + t) = i ∧
          (rdW (m.arr64 CTL) (k + t) / 2).toNat < (m.arr64 (tierA D t)).size then 0
      else pcol m D u i := by
  have hRD : R ≠ D := by
    rcases hT with ⟨rfl, -, rfl, -⟩ | ⟨rfl, -, rfl, -⟩ | ⟨rfl, -, rfl, -⟩ <;> decide
  simp only [pcol]
  by_cases hut : u = t
  · subst hut; rw [pushZ_der m u f a hT ht]
    simp only [true_and]
  · have hDc : D ≠ CTL := by
      rcases hT with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ <;> decide
    have hDc' : tierA D u ≠ CTL := (ne_tierA (Ne.symm hDc) u).symm
    rw [pushZ_arr m t f a _ hDc' (L.tierA_ne_tierA (Ne.symm hRD) u t) (tierA_ne_tier _ hu ht hut)]
    simp [hut]

/-! The three tables, one theorem each (elaborated in parallel). -/

set_option linter.unusedSimpArgs false in
theorem der_pushZ_A (hT : BinTbl R S D k) (hsel : R = AREC ∧ S = ASLOT ∧ D = ADER ∧ k = 4)
    (ht : t ≤ 1) (hc : rdW (m.arr64 CTL) (k + t) < 1073741824) (h : Word) :
    derBW (pushZ R S D k m t f a) h = derBW m h ∧ derFW (pushZ R S D k m t f a) h = derFW m h ∧
      exprLPW (pushZ R S D k m t f a) h = exprLPW m h := by
  have hctl := pushZ_ctl m t f a hT ht
  have hid := idxW_lt h
  have hidA := idxG_lt h
  have htw := tierW_le h
  have hcnt : ∀ X : TRec, tcnt (pushZ R S D k m t f a) X (tierW h) =
      if k + t = X.ca + tierW h ∧ (k + t).toNat < (m.arr64 CTL).size then
        rdW (m.arr64 CTL) (k + t) + 1 else tcnt m X (tierW h) := fun X => by
    simp only [tcnt, hctl]
  have h1 : rdW ((pushZ R S D k m t f a).arr64 CTL) 1 = rdW (m.arr64 CTL) 1 := by
    rw [hctl]
    rcases hT with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
      rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl <;> simp
  have key : rdW (m.arr64 CTL) (k + t) ≤ idxW h → ¬rdW (m.arr64 CTL) (k + t) + 1 ≤ idxW h →
      idxW h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have key2 : idxW h < rdW (m.arr64 CTL) (k + t) + 1 → ¬ idxW h < rdW (m.arr64 CTL) (k + t) →
      idxW h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have keyA : rdW (m.arr64 CTL) (k + t) ≤ idxG h → ¬rdW (m.arr64 CTL) (k + t) + 1 ≤ idxG h →
      idxG h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have key2A : idxG h < rdW (m.arr64 CTL) (k + t) + 1 → ¬ idxG h < rdW (m.arr64 CTL) (k + t) →
      idxG h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have oob : ∀ (b : TieredArray) x, ¬x.toNat < (m.arr64 b).size → rdW (m.arr64 b) x = 0 := by
    intro b x hx; simp only [rdW]; grind
  have ho : ∀ X : TRec, X.arr ≠ CTL → X.arr ≠ R → X.arr ≠ D → ∀ u i g,
      tfld (pushZ R S D k m t f a) X u i g = tfld m X u i g :=
    fun X h2 h3 h4 => tfld_pushZ_other m t f a X h2 h3 h4
  have oobP : ∀ (b : TieredArray) x, ¬(x / 2).toNat < (m.arr64 b).size → p32Get (m.arr64 b) x = 0 :=
    fun b x hx => p32Get_oob _ _ hx
  have hoP : ∀ A : ArrId, A ≠ CTL → A ≠ R → A ≠ D → ∀ u i,
      pcol (pushZ R S D k m t f a) A u i = pcol m A u i :=
    fun A h2 h3 h4 => pcol_pushZ_other m t f a A h2 h3 h4
  have hd : ∀ i, pcol (pushZ R S D k m t f a) D (tierW h) i =
      if tierW h = t ∧ rdW (m.arr64 CTL) (k + t) = i ∧
          (rdW (m.arr64 CTL) (k + t) / 2).toNat < (m.arr64 (tierA D t)).size then 0
      else pcol m D (tierW h) i :=
    fun i => pcol_pushZ_der m t f a hT ht _ htw i
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hsel
  rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl
  all_goals simp (config := {decide := true}) only [derBW, derFW, exprLPW, h1, hcnt]
  all_goals simp only [ho BVAR (by decide) (by decide) (by decide), ho FVAR (by decide) (by decide) (by decide), ho FVAR_LP (by decide) (by decide) (by decide), ho SORT_LP (by decide) (by decide) (by decide),
    ho CONST_LP (by decide) (by decide) (by decide), hoP LEDER (by decide) (by decide) (by decide), hoP PJDER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP ADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP LADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP FADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hd]
  all_goals
    rcases L.eq_zero_or_eq_one_of_le_one _ htw with e | e <;> simp only [e] <;>
      simp (config := {decide := true}) only [CTL, ADER, LADER, FADER, APP, LAM, FORALL, BVAR,
        FVAR, LET, PROJ, SORT, CONST, UInt64.add_zero, ite_false, ite_true, true_and, false_and,
        and_false, and_true, tcnt, tfld, pcol, TRec.ad, TRec.wd, TRec.ex, L.tierA_zero, L.tierA_one] at * <;>
      grind (splits := 24)

set_option linter.unusedSimpArgs false in
theorem der_pushZ_LA (hT : BinTbl R S D k) (hsel : R = LAREC ∧ S = LASLOT ∧ D = LADER ∧ k = 28)
    (ht : t ≤ 1) (hc : rdW (m.arr64 CTL) (k + t) < 1073741824) (h : Word) :
    derBW (pushZ R S D k m t f a) h = derBW m h ∧ derFW (pushZ R S D k m t f a) h = derFW m h ∧
      exprLPW (pushZ R S D k m t f a) h = exprLPW m h := by
  have hctl := pushZ_ctl m t f a hT ht
  have hid := idxW_lt h
  have hidA := idxG_lt h
  have htw := tierW_le h
  have hcnt : ∀ X : TRec, tcnt (pushZ R S D k m t f a) X (tierW h) =
      if k + t = X.ca + tierW h ∧ (k + t).toNat < (m.arr64 CTL).size then
        rdW (m.arr64 CTL) (k + t) + 1 else tcnt m X (tierW h) := fun X => by
    simp only [tcnt, hctl]
  have h1 : rdW ((pushZ R S D k m t f a).arr64 CTL) 1 = rdW (m.arr64 CTL) 1 := by
    rw [hctl]
    rcases hT with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
      rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl <;> simp
  have key : rdW (m.arr64 CTL) (k + t) ≤ idxW h → ¬rdW (m.arr64 CTL) (k + t) + 1 ≤ idxW h →
      idxW h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have key2 : idxW h < rdW (m.arr64 CTL) (k + t) + 1 → ¬ idxW h < rdW (m.arr64 CTL) (k + t) →
      idxW h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have keyA : rdW (m.arr64 CTL) (k + t) ≤ idxG h → ¬rdW (m.arr64 CTL) (k + t) + 1 ≤ idxG h →
      idxG h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have key2A : idxG h < rdW (m.arr64 CTL) (k + t) + 1 → ¬ idxG h < rdW (m.arr64 CTL) (k + t) →
      idxG h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have oob : ∀ (b : TieredArray) x, ¬x.toNat < (m.arr64 b).size → rdW (m.arr64 b) x = 0 := by
    intro b x hx; simp only [rdW]; grind
  have ho : ∀ X : TRec, X.arr ≠ CTL → X.arr ≠ R → X.arr ≠ D → ∀ u i g,
      tfld (pushZ R S D k m t f a) X u i g = tfld m X u i g :=
    fun X h2 h3 h4 => tfld_pushZ_other m t f a X h2 h3 h4
  have oobP : ∀ (b : TieredArray) x, ¬(x / 2).toNat < (m.arr64 b).size → p32Get (m.arr64 b) x = 0 :=
    fun b x hx => p32Get_oob _ _ hx
  have hoP : ∀ A : ArrId, A ≠ CTL → A ≠ R → A ≠ D → ∀ u i,
      pcol (pushZ R S D k m t f a) A u i = pcol m A u i :=
    fun A h2 h3 h4 => pcol_pushZ_other m t f a A h2 h3 h4
  have hd : ∀ i, pcol (pushZ R S D k m t f a) D (tierW h) i =
      if tierW h = t ∧ rdW (m.arr64 CTL) (k + t) = i ∧
          (rdW (m.arr64 CTL) (k + t) / 2).toNat < (m.arr64 (tierA D t)).size then 0
      else pcol m D (tierW h) i :=
    fun i => pcol_pushZ_der m t f a hT ht _ htw i
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hsel
  rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl
  all_goals simp (config := {decide := true}) only [derBW, derFW, exprLPW, h1, hcnt]
  all_goals simp only [ho BVAR (by decide) (by decide) (by decide), ho FVAR (by decide) (by decide) (by decide), ho FVAR_LP (by decide) (by decide) (by decide), ho SORT_LP (by decide) (by decide) (by decide),
    ho CONST_LP (by decide) (by decide) (by decide), hoP LEDER (by decide) (by decide) (by decide), hoP PJDER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP ADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP LADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP FADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hd]
  all_goals
    rcases L.eq_zero_or_eq_one_of_le_one _ htw with e | e <;> simp only [e] <;>
      simp (config := {decide := true}) only [CTL, ADER, LADER, FADER, APP, LAM, FORALL, BVAR,
        FVAR, LET, PROJ, SORT, CONST, UInt64.add_zero, ite_false, ite_true, true_and, false_and,
        and_false, and_true, tcnt, tfld, pcol, TRec.ad, TRec.wd, TRec.ex, L.tierA_zero, L.tierA_one] at * <;>
      grind (splits := 24)

set_option linter.unusedSimpArgs false in
theorem der_pushZ_FA (hT : BinTbl R S D k) (hsel : R = FAREC ∧ S = FASLOT ∧ D = FADER ∧ k = 30)
    (ht : t ≤ 1) (hc : rdW (m.arr64 CTL) (k + t) < 1073741824) (h : Word) :
    derBW (pushZ R S D k m t f a) h = derBW m h ∧ derFW (pushZ R S D k m t f a) h = derFW m h ∧
      exprLPW (pushZ R S D k m t f a) h = exprLPW m h := by
  have hctl := pushZ_ctl m t f a hT ht
  have hid := idxW_lt h
  have hidA := idxG_lt h
  have htw := tierW_le h
  have hcnt : ∀ X : TRec, tcnt (pushZ R S D k m t f a) X (tierW h) =
      if k + t = X.ca + tierW h ∧ (k + t).toNat < (m.arr64 CTL).size then
        rdW (m.arr64 CTL) (k + t) + 1 else tcnt m X (tierW h) := fun X => by
    simp only [tcnt, hctl]
  have h1 : rdW ((pushZ R S D k m t f a).arr64 CTL) 1 = rdW (m.arr64 CTL) 1 := by
    rw [hctl]
    rcases hT with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
      rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl <;> simp
  have key : rdW (m.arr64 CTL) (k + t) ≤ idxW h → ¬rdW (m.arr64 CTL) (k + t) + 1 ≤ idxW h →
      idxW h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have key2 : idxW h < rdW (m.arr64 CTL) (k + t) + 1 → ¬ idxW h < rdW (m.arr64 CTL) (k + t) →
      idxW h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have keyA : rdW (m.arr64 CTL) (k + t) ≤ idxG h → ¬rdW (m.arr64 CTL) (k + t) + 1 ≤ idxG h →
      idxG h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have key2A : idxG h < rdW (m.arr64 CTL) (k + t) + 1 → ¬ idxG h < rdW (m.arr64 CTL) (k + t) →
      idxG h = rdW (m.arr64 CTL) (k + t) := by
    simp only [UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.lt_iff_toNat_lt, show (1 : Word).toNat = 1 from rfl,
      show (1073741824 : Word).toNat = 1073741824 from rfl, show (1140850688 : Word).toNat = 1140850688 from rfl,
      show (2147483648 : Word).toNat = 2147483648 from rfl] at *
    omega
  have oob : ∀ (b : TieredArray) x, ¬x.toNat < (m.arr64 b).size → rdW (m.arr64 b) x = 0 := by
    intro b x hx; simp only [rdW]; grind
  have ho : ∀ X : TRec, X.arr ≠ CTL → X.arr ≠ R → X.arr ≠ D → ∀ u i g,
      tfld (pushZ R S D k m t f a) X u i g = tfld m X u i g :=
    fun X h2 h3 h4 => tfld_pushZ_other m t f a X h2 h3 h4
  have oobP : ∀ (b : TieredArray) x, ¬(x / 2).toNat < (m.arr64 b).size → p32Get (m.arr64 b) x = 0 :=
    fun b x hx => p32Get_oob _ _ hx
  have hoP : ∀ A : ArrId, A ≠ CTL → A ≠ R → A ≠ D → ∀ u i,
      pcol (pushZ R S D k m t f a) A u i = pcol m A u i :=
    fun A h2 h3 h4 => pcol_pushZ_other m t f a A h2 h3 h4
  have hd : ∀ i, pcol (pushZ R S D k m t f a) D (tierW h) i =
      if tierW h = t ∧ rdW (m.arr64 CTL) (k + t) = i ∧
          (rdW (m.arr64 CTL) (k + t) / 2).toNat < (m.arr64 (tierA D t)).size then 0
      else pcol m D (tierW h) i :=
    fun i => pcol_pushZ_der m t f a hT ht _ htw i
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hsel
  rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl
  all_goals simp (config := {decide := true}) only [derBW, derFW, exprLPW, h1, hcnt]
  all_goals simp only [ho BVAR (by decide) (by decide) (by decide), ho FVAR (by decide) (by decide) (by decide), ho FVAR_LP (by decide) (by decide) (by decide), ho SORT_LP (by decide) (by decide) (by decide),
    ho CONST_LP (by decide) (by decide) (by decide), hoP LEDER (by decide) (by decide) (by decide), hoP PJDER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP ADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP LADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hoP FADER (by decide) (by decide) (by decide)]
  all_goals try simp only [hd]
  all_goals
    rcases L.eq_zero_or_eq_one_of_le_one _ htw with e | e <;> simp only [e] <;>
      simp (config := {decide := true}) only [CTL, ADER, LADER, FADER, APP, LAM, FORALL, BVAR,
        FVAR, LET, PROJ, SORT, CONST, UInt64.add_zero, ite_false, ite_true, true_and, false_and,
        and_false, and_true, tcnt, tfld, pcol, TRec.ad, TRec.wd, TRec.ex, L.tierA_zero, L.tierA_one] at * <;>
      grind (splits := 24)

/-- **The append, with the new slot zeroed, changes none of `der_b`'s three reads**, for every
handle: a handle other than the new node reads what it read before (another tier's array, or
another index), and the new node reads `0` (before: its index was past the count). -/
theorem der_pushZ (hT : BinTbl R S D k) (ht : t ≤ 1) (hc : rdW (m.arr64 CTL) (k + t) < 1073741824)
    (h : Word) :
    derBW (pushZ R S D k m t f a) h = derBW m h ∧ derFW (pushZ R S D k m t f a) h = derFW m h ∧
      exprLPW (pushZ R S D k m t f a) h = exprLPW m h := by
  rcases hT with hs | hs | hs
  · exact der_pushZ_A m t f a (.inl hs) hs ht hc h
  · exact der_pushZ_LA m t f a (.inr (.inl hs)) hs ht hc h
  · exact der_pushZ_FA m t f a (.inr (.inr hs)) hs ht hc h

end pushZ

/-- The index and tier fields of a narrow handle word `t · 2^31 + g · 2^26 + c` (`hdW`). -/
theorem hw_fieldsN (g t c : Word) (hg : g.toNat < 16) (ht : t ≤ 1) (hc : c < 67108864) :
    idxW (hdW g t c) = c ∧ tierW (hdW g t c) = t := by
  have hc' : c.toNat < 2 ^ 26 := UInt64.lt_iff_toNat_lt.mp hc
  exact ⟨hdW_idx g t c hg ht hc', hdW_tier g t c hg ht hc'⟩

/-- The index and tier fields of a wide handle word `t · 2^31 + 2^30 + c` (`hdA`). -/
theorem hw_fieldsA (t c : Word) (ht : t ≤ 1) (hc : c < 1073741824) :
    idxA (hdA t c) = c ∧ tierW (hdA t c) = t := by
  have hc' : c.toNat < 2 ^ 30 := UInt64.lt_iff_toNat_lt.mp hc
  exact ⟨hdA_idx t c ht hc', hdA_tier t c ht hc'⟩

/-- `der_b`'s three reads do not look at the binary tables' slot arrays (a growth changes only
those, lane slotgrow). -/
theorem der_congr {S : ArrId} (hS : S = ASLOT ∨ S = LASLOT ∨ S = FASLOT) (t : Word) {m₂ m₃ : Mem}
    (hf : ∀ b, b ≠ tierA S t → m₂.arr64 b = m₃.arr64 b) (h : Word) :
    derBW m₂ h = derBW m₃ h ∧ derFW m₂ h = derFW m₃ h ∧ exprLPW m₂ h = exprLPW m₃ h := by
  have e : ∀ b : ArrId, b ≠ S → m₂.arr64 b = m₃.arr64 b ∧
      m₂.arr64 (tier1 b) = m₃.arr64 (tier1 b) := fun b hbS =>
    ⟨hf _ (ne_tierA hbS t), hf _ (by simpa using L.tierA_ne_tierA hbS 1 t)⟩
  rcases hS with rfl | rfl | rfl <;>
  simp only [derBW, derFW, exprLPW, (e CTL (by decide)).1,
    tcnt_arr_eq _ (e CTL (by decide)).1,
    tfld_arr_eq (R := BVAR) (e BREC (by decide)).1 (e BREC (by decide)).2,
    pcol_arr_eq (A := ADER) (e ADER (by decide)).1 (e ADER (by decide)).2,
    pcol_arr_eq (A := LADER) (e LADER (by decide)).1 (e LADER (by decide)).2,
    pcol_arr_eq (A := FADER) (e FADER (by decide)).1 (e FADER (by decide)).2,
    pcol_arr_eq (A := LEDER) (e LEDER (by decide)).1 (e LEDER (by decide)).2,
    pcol_arr_eq (A := PJDER) (e PJDER (by decide)).1 (e PJDER (by decide)).2,
    tfld_arr_eq (R := FVAR) (e FVREC (by decide)).1 (e FVREC (by decide)).2,
    tfld_arr_eq (R := FVAR_LP) (e FVLP (by decide)).1 (e FVLP (by decide)).2,
    tfld_arr_eq (R := SORT_LP) (e SOLP (by decide)).1 (e SOLP (by decide)).2,
    tfld_arr_eq (R := CONST_LP) (e CLP (by decide)).1 (e CLP (by decide)).2,
    and_self]

theorem ainternW_grow {m m₁ : Mem} {f a r : Word} (hI : ainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 4 ≠ cnt2 m 4) :
    ∃ t, t ≤ 1 ∧ acnt m t < 1073741824 ∧
      (∀ b, b ≠ tierA ASLOT t → m₁.arr64 b = (pushRec appCS m t [f, a]).arr64 b) ∧
      idxA r = acnt m t ∧ tierW r = t := by
  rcases consInternM_outA (C := appCS) (by decide) (fun A h => by simp [appCS] at h) hI with
    rfl | ⟨t, ht, hok, rfl, he, -⟩
  · exact absurd rfl hc
  have h : acnt m t < 1073741824 := by
    rw [← apushOK_eqC] at hok
    simp only [apushOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  refine ⟨t, ht, h, he, ?_⟩
  rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl
  · rw [show (if (0 : Word) = 0 then appCS.P else appCS.S) + cntC appCS m 0 = hdA 0 (acnt m 0) by simp [appCS, appP, hdA, cntC, acnt]]
    exact hw_fieldsA _ _ (by decide) h
  · rw [show (if (1 : Word) = 0 then appCS.P else appCS.S) + cntC appCS m 1 = hdA 1 (acnt m 1) by simp [appCS, appS, hdA, cntC, acnt]]
    exact hw_fieldsA _ _ (by decide) h

theorem OutSa.set32 {sa : TieredArray} {M₁ M₂ : Mem} (h : OutSa sa M₁ M₂) {a : TieredArray} (ha : a ≠ sa)
    (i v : Word) : OutSa sa (M₁.set32 a i v) (M₂.set32 a i v) := by
  simp only [Mem.set32, h a ha]
  exact h.set64 ha _ _

/-- After a miss of `intern_app` (the counts changed), the zeroed slot hides the append from
`der_b`'s three reads. -/
theorem ainternW_der {m m₁ : Mem} {f a r q u : Word} (hI : ainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 4 ≠ cnt2 m 4)
    (hq : q = idxA r) (hu : u = tierW r) (x : Word) :
    derBW (m₁.set32 (tierA ADER u) q 0) x = derBW m x ∧
      derFW (m₁.set32 (tierA ADER u) q 0) x = derFW m x ∧
      exprLPW (m₁.set32 (tierA ADER u) q 0) x = exprLPW m x := by
  obtain ⟨t, ht, hc', he, hi, htr⟩ := ainternW_grow hI hc
  rw [hq, hu, hi, htr]
  have ez : (pushRec appCS m t [f, a]).set32 (tierA ADER t) (acnt m t) 0 =
      pushZ AREC ASLOT ADER 4 m t f a := by
    simp only [pushRec, colW, appCS, cntC, acnt, pushZ, pushArgs]; rfl
  obtain ⟨e1, e2, e3⟩ := der_congr (.inl rfl) t
    (fun b hb => (OutSa.set32 (fun b hb => he b hb)
      (L.tierA_ne_tierA (a := ADER) (b := ASLOT) (by decide) t t) _ _ b hb).trans
      (by rw [ez])) x
  obtain ⟨f1, f2, f3⟩ := der_pushZ (R := AREC) (S := ASLOT) (D := ADER) (k := 4) m t f a
    (.inl ⟨rfl, rfl, rfl, rfl⟩) ht hc' x
  exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩

grind_pattern [arena_grind] ainternW_der => ainternW m f a, (r, m₁), derBW (Mem.set32 m₁ (tierA ADER u) q 0) x

theorem lainternW_grow {m m₁ : Mem} {f a r : Word} (hI : lainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 28 ≠ cnt2 m 28) :
    ∃ t, t ≤ 1 ∧ lacnt m t < 67108864 ∧
      (∀ b, b ≠ tierA LASLOT t → m₁.arr64 b = (pushRec lamCS m t [f, a]).arr64 b) ∧
      idxW r = lacnt m t ∧ tierW r = t := by
  rcases consInternM_outA (C := lamCS) (by decide) (fun A h => by simp [lamCS] at h) hI with
    rfl | ⟨t, ht, hok, rfl, he, -⟩
  · exact absurd rfl hc
  have h : lacnt m t < 67108864 := by
    rw [← lapushOK_eqC] at hok
    simp only [lapushOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  refine ⟨t, ht, h, he, ?_⟩
  rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl
  · rw [show (if (0 : Word) = 0 then lamCS.P else lamCS.S) + cntC lamCS m 0 = hdW 5 0 (lacnt m 0) by simp [lamCS, lamP, hdW, cntC, lacnt]]
    exact hw_fieldsN _ _ _ (by decide) (by decide) h
  · rw [show (if (1 : Word) = 0 then lamCS.P else lamCS.S) + cntC lamCS m 1 = hdW 5 1 (lacnt m 1) by simp [lamCS, lamS, hdW, cntC, lacnt]]
    exact hw_fieldsN _ _ _ (by decide) (by decide) h

/-- After a miss of `intern_lam` (the counts changed), the zeroed slot hides the append from
`der_b`'s three reads. -/
theorem lainternW_der {m m₁ : Mem} {f a r q u : Word} (hI : lainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 28 ≠ cnt2 m 28)
    (hq : q = idxW r) (hu : u = tierW r) (x : Word) :
    derBW (m₁.set32 (tierA LADER u) q 0) x = derBW m x ∧
      derFW (m₁.set32 (tierA LADER u) q 0) x = derFW m x ∧
      exprLPW (m₁.set32 (tierA LADER u) q 0) x = exprLPW m x := by
  obtain ⟨t, ht, hc', he, hi, htr⟩ := lainternW_grow hI hc
  rw [hq, hu, hi, htr]
  have ez : (pushRec lamCS m t [f, a]).set32 (tierA LADER t) (lacnt m t) 0 =
      pushZ LAREC LASLOT LADER 28 m t f a := by
    simp only [pushRec, colW, lamCS, cntC, lacnt, pushZ, pushArgs]; rfl
  obtain ⟨e1, e2, e3⟩ := der_congr (.inr (.inl rfl)) t
    (fun b hb => (OutSa.set32 (fun b hb => he b hb)
      (L.tierA_ne_tierA (a := LADER) (b := LASLOT) (by decide) t t) _ _ b hb).trans
      (by rw [ez])) x
  obtain ⟨f1, f2, f3⟩ := der_pushZ (R := LAREC) (S := LASLOT) (D := LADER) (k := 28) m t f a
    (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)) ht (UInt64.lt_of_lt_of_le hc' (by decide)) x
  exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩

grind_pattern [arena_grind] lainternW_der => lainternW m f a, (r, m₁), derBW (Mem.set32 m₁ (tierA LADER u) q 0) x

theorem fainternW_grow {m m₁ : Mem} {f a r : Word} (hI : fainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 30 ≠ cnt2 m 30) :
    ∃ t, t ≤ 1 ∧ facnt m t < 67108864 ∧
      (∀ b, b ≠ tierA FASLOT t → m₁.arr64 b = (pushRec forallCS m t [f, a]).arr64 b) ∧
      idxW r = facnt m t ∧ tierW r = t := by
  rcases consInternM_outA (C := forallCS) (by decide) (fun A h => by simp [forallCS] at h) hI with
    rfl | ⟨t, ht, hok, rfl, he, -⟩
  · exact absurd rfl hc
  have h : facnt m t < 67108864 := by
    rw [← fapushOK_eqC] at hok
    simp only [fapushOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1
  refine ⟨t, ht, h, he, ?_⟩
  rcases L.eq_zero_or_eq_one_of_le_one t ht with rfl | rfl
  · rw [show (if (0 : Word) = 0 then forallCS.P else forallCS.S) + cntC forallCS m 0 = hdW 6 0 (facnt m 0) by simp [forallCS, forallP, hdW, cntC, facnt]]
    exact hw_fieldsN _ _ _ (by decide) (by decide) h
  · rw [show (if (1 : Word) = 0 then forallCS.P else forallCS.S) + cntC forallCS m 1 = hdW 6 1 (facnt m 1) by simp [forallCS, forallS, hdW, cntC, facnt]]
    exact hw_fieldsN _ _ _ (by decide) (by decide) h

/-- After a miss of `intern_forall` (the counts changed), the zeroed slot hides the append from
`der_b`'s three reads. -/
theorem fainternW_der {m m₁ : Mem} {f a r q u : Word} (hI : fainternW m f a = some (r, m₁))
    (hc : cnt2 m₁ 30 ≠ cnt2 m 30)
    (hq : q = idxW r) (hu : u = tierW r) (x : Word) :
    derBW (m₁.set32 (tierA FADER u) q 0) x = derBW m x ∧
      derFW (m₁.set32 (tierA FADER u) q 0) x = derFW m x ∧
      exprLPW (m₁.set32 (tierA FADER u) q 0) x = exprLPW m x := by
  obtain ⟨t, ht, hc', he, hi, htr⟩ := fainternW_grow hI hc
  rw [hq, hu, hi, htr]
  have ez : (pushRec forallCS m t [f, a]).set32 (tierA FADER t) (facnt m t) 0 =
      pushZ FAREC FASLOT FADER 30 m t f a := by
    simp only [pushRec, colW, forallCS, cntC, facnt, pushZ, pushArgs]; rfl
  obtain ⟨e1, e2, e3⟩ := der_congr (.inr (.inr rfl)) t
    (fun b hb => (OutSa.set32 (fun b hb => he b hb)
      (L.tierA_ne_tierA (a := FADER) (b := FASLOT) (by decide) t t) _ _ b hb).trans
      (by rw [ez])) x
  obtain ⟨f1, f2, f3⟩ := der_pushZ (R := FAREC) (S := FASLOT) (D := FADER) (k := 30) m t f a
    (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩)) ht (UInt64.lt_of_lt_of_le hc' (by decide)) x
  exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩

grind_pattern [arena_grind] fainternW_der => fainternW m f a, (r, m₁), derBW (Mem.set32 m₁ (tierA FADER u) q 0) x

/-! ## `mk_app(f, a)` -/

/-- **The model of `mk_app`.** The written word packs both ranges (`packBF`): `der_b` reads it
back apart. -/
def mkAppW (m : Mem) (f a : Word) : Option (Word × Mem) :=
  if (f ||| a) >>> 32 ≠ 0 then none
  else mkK ADER 4 (cnt2 m 4)
    (packBFL (maxW (derBW m f) (derBW m a)) (maxW (derFW m f) (derFW m a))
      (exprLPW m f ||| exprLPW m a)) (ainternW m f a)

/-- con-ron: ConRon/Arena/Monad.lean:221-247 ConRon.Arena.internNodeE -/
@[no_expose] def mkApp : FunDecl := lfn (f, a) locals (x, y, s, r, q, xf, yf, xl, yl, tr) {
  if (f | a) >> 32 != 0 { abort };
  s := CTL.u64[4] + CTL.u64[5];
  r := call intern_app(f, a);
  if CTL.u64[4] + CTL.u64[5] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.aidx;
    if len(ADER⟨tr⟩) * 2 <= q { abort };
    ADER⟨tr⟩.u32[q] := 0;
    (x, xf, xl) := call der_b(f);
    (y, yf, yl) := call der_b(a);
    if x < y { x := y };
    if xf < yf { xf := yf };
    ADER⟨tr⟩.u32[q] := x + xf * 32768 + (xl | yl) * 1073741824
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

/-- con-ron: ConRon/Arena/Monad.lean:221-247 ConRon.Arena.internNodeE -/
@[no_expose] def mkLam : FunDecl := lfn (t, b) locals (x, y, s, r, q, xf, yf, xl, yl, tr) {
  if (t | b) >> 32 != 0 { abort };
  s := CTL.u64[28] + CTL.u64[29];
  r := call intern_lam(t, b);
  if CTL.u64[28] + CTL.u64[29] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(LADER⟨tr⟩) * 2 <= q { abort };
    LADER⟨tr⟩.u32[q] := 0;
    (x, xf, xl) := call der_b(t);
    (y, yf, yl) := call der_b(b);
    y := y - u64(0 < y) + u64(y == 32767);
    if x < y { x := y };
    if xf < yf { xf := yf };
    LADER⟨tr⟩.u32[q] := x + xf * 32768 + (xl | yl) * 1073741824
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

/-- con-ron: ConRon/Arena/Monad.lean:221-247 ConRon.Arena.internNodeE -/
@[no_expose] def mkForall : FunDecl := lfn (t, b) locals (x, y, s, r, q, xf, yf, xl, yl, tr) {
  if (t | b) >> 32 != 0 { abort };
  s := CTL.u64[30] + CTL.u64[31];
  r := call intern_forall(t, b);
  if CTL.u64[30] + CTL.u64[31] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(FADER⟨tr⟩) * 2 <= q { abort };
    FADER⟨tr⟩.u32[q] := 0;
    (x, xf, xl) := call der_b(t);
    (y, yf, yl) := call der_b(b);
    y := y - u64(0 < y) + u64(y == 32767);
    if x < y { x := y };
    if xf < yf { xf := yf };
    FADER⟨tr⟩.u32[q] := x + xf * 32768 + (xl | yl) * 1073741824
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

/-- con-ron: ConRon/Arena/Monad.lean:221-247 ConRon.Arena.internNodeE -/
@[no_expose] def mkLet : FunDecl := lfn (t, v, b) locals (x, y, z, s, r, q, xf, yf, zf, xl, yl, zl, tr) {
  if (t | v | b) >> 32 != 0 { abort };
  (x, xf, xl) := call der_b(t);
  (y, yf, yl) := call der_b(v);
  (z, zf, zl) := call der_b(b);
  s := CTL.u64[20] + CTL.u64[21];
  r := call intern_letE(t, v, b);
  if CTL.u64[20] + CTL.u64[21] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(LEDER⟨tr⟩) * 2 <= q { abort };
    if x < y { x := y };
    z := z - u64(0 < z) + u64(z == 32767);
    if x < z { x := z };
    if xf < yf { xf := yf };
    if xf < zf { xf := zf };
    LEDER⟨tr⟩.u32[q] := x + xf * 32768 + (xl | yl | zl) * 1073741824
  };
  return r
}

/-! ## `mk_proj(n, i, e)` -/

/-- **The model of `mk_proj`.** -/
def mkProjW (m : Mem) (n i e : Word) : Option (Word × Mem) :=
  if (n ||| e) >>> 32 ≠ 0 then none
  else mkK PJDER 32 (cnt2 m 32) (packBFL (derBW m e) (derFW m e) (exprLPW m e)) (pjinternW m n i e)

/-- con-ron: ConRon/Arena/Monad.lean:221-247 ConRon.Arena.internNodeE -/
@[no_expose] def mkProj : FunDecl := lfn (n, i, e) locals (x, s, r, q, xf, xl, tr) {
  if (n | e) >> 32 != 0 { abort };
  (x, xf, xl) := call der_b(e);
  s := CTL.u64[32] + CTL.u64[33];
  r := call intern_proj(n, i, e);
  if CTL.u64[32] + CTL.u64[33] != s {
    tr := ⟦r⟧.tier;
    q := ⟦r⟧.idx;
    if len(PJDER⟨tr⟩) * 2 <= q { abort };
    PJDER⟨tr⟩.u32[q] := x + xf * 32768 + xl * 1073741824
  };
  return r
}

/-! ## The store arithmetic as named functions

The `mk_*` stores compute `satPredW` and `packBF` inline; these equations name the evaluated
L expressions, so `finish` matches them instead of unfolding the arithmetic (and case-splitting on
its comparisons) inside every spec (lane `exprops4`: `mkLet_spec` went from > 10 min to seconds).
Each `maxW` is a branch, which `step_maxIf_spec` names. -/

/-- **A `max` by a branch**, `if x < y { x := y }` (the `mk_*` writers; cheaper than the `u64`
product form `x + (y - x) * u64(x < y)`): it sets `x` to `maxW x y`. Stated over any post, so that
`vcgen` applies it at the `if` (an explicit spec outranks `step`'s equations) instead of splitting
the writer's proof at the comparison. -/
theorem step_maxIf_spec (p : Prog) (k : Stmt → M Sig) (x y : Var) (Q : Sig → St → Prop) E :
    ⦃fun s => Q .normal (s.setLoc x (maxW (s.loc x) (s.loc y)))⦄
    step p k (.ite (.cmp .ult (.var x) (.var y)) (.set x (.var y)) .skip)
    ⦃Q; E⦄ := by
  vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, step, evalC, evalE, setLoc] <;> rename_i s hq hc <;> obtain ⟨m, l⟩ := s
  · have e : maxW (l x) (l y) = l y := by grind [maxW, Cmp.eval]
    rwa [e] at hq
  · have e : (St.setLoc ⟨m, l⟩ x (maxW (l x) (l y))) = ⟨m, l⟩ := by
      simp only [St.setLoc, St.mk.injEq, true_and]; funext z; grind [maxW, Cmp.eval]
    rwa [e] at hq

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, st64, st32,
        derB_spec p hd n, internApp_spec p hpf hpp hpi n, step_maxIf_spec p] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [Mem.set64_set64_same, Mem.set32_set32_same, p32Len, mkAppW, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, st64, st32,
        derB_spec p hd n, internLamL_spec p hpf hpp hpi n, step_maxIf_spec p] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [Mem.set64_set64_same, Mem.set32_set32_same, p32Len, mkLamW, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, st64, st32,
        derB_spec p hd n, internForallL_spec p hpf hpp hpi n, step_maxIf_spec p] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [Mem.set64_set64_same, Mem.set32_set32_same, p32Len, mkForallW, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, st64, st32,
        derB_spec p hd n, internLet_spec p hpf hpp hpi n, step_maxIf_spec p] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [p32Len, mkLetW, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE, st64, st32,
        derB_spec p hd n, internProj_spec p hpf hpp hpi n] <;>
      -- gen 20: the chain of three `der_b` results through `setLocs` is deeper than the default
      finish (gen := 20) [p32Len, mkProjW, satPredW_L, packBF_L, packBFL_L, derPutW, cnt2, tierW, idxW]

end specs

end L.Arena
