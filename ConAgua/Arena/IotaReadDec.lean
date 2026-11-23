module

public import ConAgua.Arena.IndDecStab
public import ConRon.Arena.Inductives.IotaRead

@[expose] public section

/-!
# The ι reading rule's records in L (lane ronsync8, the interface of stage 3a)

The twin's ι reading rule (`ConRon/Arena/Inductives/IotaRead.lean`, con-leche #622) passes two
records between its functions: a recursor's frame `IotaRec` (read once per recursor,
`iotaRecOf`) and a rule's parts `IIotaParts` (`iotaPartsOfAt`, `iotaPartsAt`). In L both are
result words, their lists `IW` slices (`off, len`), as `strip_pis` answers its domains:

* `IotaRec` — seven words `[preO, preL, minO, minL, us, parO, parL]`: the rule prefix (handles),
  the minor premises' positions (numbers), the major's level list (a handle), its parameters
  (handles). `Option IotaRec` is `ok` then the seven (`iota_rec_of`, `iota_read_major`).
* `IIotaParts` — seven words `[fdO, fdL, idxO, idxL, us, parO, parL]`: the fields' domains, the
  indices, the levels, the parameters. `Option IIotaParts` is `ok` then the seven
  (`iota_parts_of_at`); `Option (IIotaParts × List EIdx)` is `ok`, the seven, then the
  constructor's parameter domains `pdO, pdL` (`iota_parts_at`, `iota_parts_at_body`).

A caller passes a record on as its words (the L functions take them as arguments, in this
order). Every slice is below the `IW` top (`decRL`), so a record stays decoded while the pool
grows (`decIR_grow`, `decIP_grow`).

The L functions and their signatures (the helpers of the port implement them):

| twin | L | arguments → results |
|---|---|---|
| `piTele fuel e` | `pi_tele(e)` | `→ (n, body)` |
| `motiveLevel? pre nIdx body` | `motive_level(preO, preL, nIdx, body)` | `→ (ok, u)` |
| `iotaFrame cv mI rP` | `iota_frame(q, mI, rP)` | `→ (ok, preO, preL, domO, domL, body, u)` |
| `isMinorAt pre mot q` | `is_minor_at(preO, preL, mot, q)` | `→ b` |
| `minorsFrom pre mot q` | `minors_from(preO, preL, mot, q)` | `→ (o, l)` |
| `iotaRecMajor pre doms nIdx rP k` | `iota_read_major(preO, preL, domO, domL, nIdx, rP, k)` | `→ (ok, IotaRec)` |
| `iotaRecOf cv mI rP` | `iota_rec_of(q, mI, rP)` | `→ (ok, IotaRec)` |
| `iotaPartsOfAt rr rP nIdx i rl` | `iota_parts_of_at(IotaRec…, rP, nIdx, i, r)` | `→ (ok, IIotaParts)` |
| `iotaPartsAt cvj cnP mI rP rl` | `iota_parts_at(qj, cnP, mI, rP, r)` | `→ (ok, IIotaParts, pdO, pdL)` |
| `iotaPartsRel fe cnP cv rl p' p pd` | `iota_parts_rel(vis, cnP, q, r, …)` | `→ b` |
| `recsRead fe recs` | `recs_read(vis, o, l)` | `→ b` |
| `blockReadsAt fe p` | `block_reads_at(vis, …)` | `→ (b, vis')` |

`q`/`qj` a constant value's `EREC` address (`CV`), `r` a recursor rule's (`decRules`'s layout).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **A recursor's frame** `x`, the seven words of `r` from word `i` on. -/
def decIRAt (i : Nat) (m : Mem) (r : List Word) (x : IotaRec) : Prop :=
  decRL (fun m => decHL m) i m r x.pre ∧ decRL (fun m => decNL m) (i + 2) m r x.minors ∧
    ((r.getD (i + 4) 0).toNat < 2 ^ 32 ∧ decI (r.getD (i + 4) 0) = x.us) ∧ decRL (fun m => decHL m) (i + 5) m r x.params

/-- `Option IotaRec` as `(ok, IotaRec)`. -/
def decOIR (m : Mem) (r : List Word) : Option IotaRec → Prop
  | none => r.headD 0 = 0
  | some x => r.headD 0 = 1 ∧ decIRAt 1 m r x

/-- **A rule's parts** `x`, the seven words of `r` from word `i` on. -/
def decIPAt (i : Nat) (m : Mem) (r : List Word) (x : IIotaParts) : Prop :=
  decRL (fun m => decHL m) i m r x.fieldDoms ∧ decRL (fun m => decHL m) (i + 2) m r x.idx ∧
    ((r.getD (i + 4) 0).toNat < 2 ^ 32 ∧ decI (r.getD (i + 4) 0) = x.us) ∧ decRL (fun m => decHL m) (i + 5) m r x.params

/-- `Option IIotaParts` as `(ok, IIotaParts)`. -/
def decOIP (m : Mem) (r : List Word) : Option IIotaParts → Prop
  | none => r.headD 0 = 0
  | some x => r.headD 0 = 1 ∧ decIPAt 1 m r x

/-- `Option (IIotaParts × List EIdx)` as `(ok, IIotaParts, pdO, pdL)`. -/
def decOIPD (m : Mem) (r : List Word) : Option (IIotaParts × List EIdx) → Prop
  | none => r.headD 0 = 0
  | some (x, pd) => r.headD 0 = 1 ∧ decIPAt 1 m r x ∧ decRL (fun m => decHL m) 8 m r pd

/-! ## Stability as the pool grows -/

theorem decRL_hl_grow {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {i : Nat} {r : List Word}
    {xs : List (Idx k)} (h : decRL (fun m => decHL m) i m r xs) :
    decRL (fun m => decHL m) i m' r xs :=
  ⟨decHL_grow' hg h.2 h.1, Nat.le_trans h.2 hg.iw⟩

theorem decRL_nl_grow {m m' : Mem} (hg : IWGrow m m') {i : Nat} {r : List Word}
    {xs : List Nat} (h : decRL (fun m => decNL m) i m r xs) :
    decRL (fun m => decNL m) i m' r xs :=
  ⟨(decNL_decB h.1 h.2).stab (OMono.decNL _ _) m' hg, Nat.le_trans h.2 hg.iw⟩

theorem decIRAt_grow {m m' : Mem} (hg : IWGrow m m') {i : Nat} {r : List Word} {x : IotaRec}
    (h : decIRAt i m r x) : decIRAt i m' r x :=
  ⟨decRL_hl_grow hg h.1, decRL_nl_grow hg h.2.1, h.2.2.1, decRL_hl_grow hg h.2.2.2⟩

theorem decIPAt_grow {m m' : Mem} (hg : IWGrow m m') {i : Nat} {r : List Word} {x : IIotaParts}
    (h : decIPAt i m r x) : decIPAt i m' r x :=
  ⟨decRL_hl_grow hg h.1, decRL_hl_grow hg h.2.1, h.2.2.1, decRL_hl_grow hg h.2.2.2⟩

theorem decOIR_grow {m m' : Mem} (hg : IWGrow m m') {r : List Word} {x : Option IotaRec}
    (h : decOIR m r x) : decOIR m' r x := by
  cases x with
  | none => exact h
  | some x => exact ⟨h.1, decIRAt_grow hg h.2⟩

theorem decOIP_grow {m m' : Mem} (hg : IWGrow m m') {r : List Word} {x : Option IIotaParts}
    (h : decOIP m r x) : decOIP m' r x := by
  cases x with
  | none => exact h
  | some x => exact ⟨h.1, decIPAt_grow hg h.2⟩

theorem decOIPD_grow {m m' : Mem} (hg : IWGrow m m') {r : List Word}
    {x : Option (IIotaParts × List EIdx)} (h : decOIPD m r x) : decOIPD m' r x := by
  cases x with
  | none => exact h
  | some x => exact ⟨h.1, decIPAt_grow hg h.2.1, decRL_hl_grow hg h.2.2⟩

/-- The records' words as a caller passes them on: `decIRAt` at the start of a word list. -/
theorem decIRAt_drop {m : Mem} {i : Nat} {r : List Word} {x : IotaRec} (h : decIRAt i m r x) :
    decIRAt 0 m (r.drop i) x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp_all [decRL, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm, Nat.add_left_comm]

theorem decIPAt_drop {m : Mem} {i : Nat} {r : List Word} {x : IIotaParts} (h : decIPAt i m r x) :
    decIPAt 0 m (r.drop i) x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp_all [decRL, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm, Nat.add_left_comm]

end L.Ind
