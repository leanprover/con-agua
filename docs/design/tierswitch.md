# Lane `tierswitch`: the store library on tiered arrays (journal)

Branch `tierswitch`, worktree `_tmp/wt/tierswitch`. Goal: fix D35. Every node store keeps one
word array per tier (tier `t` of array `a` is array `a + 256`, lane tierarr's `ld64t`/`st64t`),
as con-ron keeps one `Tbl` per constructor per tier (handle bit 27). Background:
docs/design/tierarr.md (the compiler feature, KSTP on tiered arrays), docs/design/tieracc.md (the
accessors that confine the layout to the store library).

## Phase 1: the L side, unproved

### Layout

* **Records** (`TRec.ld`/`st`, `ConsLib.cpMid`/`cpWr`): node `i` of tier `t` at
  `ra⟨t⟩[i * w + f]` (was `ra[i * 2w + t * w + f]`). `TRec.ad R j f = j * w + f` (no tier).
* **Counts**: unchanged, `CTL[ca + t]`.
* **Slot tables** (KSTP, `ConsLib`): one table per tier array `sa⟨t⟩`, one formula for both
  tiers: words `0`, `1` hold `n − SN0` and the offset `o`; the table starts at word `2 + o`;
  growth ping-pongs `o = 0 ↔ 4 n'` upward and aborts if `2 + o' + 2 n' > len`. Gone: tier 1's
  mirrored `len − o − 2n`, the half bound `H`. `consMinWords` = `2 + 2 SN0` = 18 per tier array.
* **Columns** (DER 42–46, HP/LP 55–61): `col⟨t⟩[i]` (was `col[2 i + t]`); the `mk_*` writes take
  the tier in a local (`tr`, a store's tier must be simple).
* **Matchers** (`lit_match`, `ls_match`, `nstr_match`, the `mc` conditions): `REC⟨t⟩[i * w + f]`.
* **Room tests**: per tier, `len(R⟨t⟩) >> log w <= c` (was `len(R) >> log 2w`).
* **Entry** (`Checker/Entry.lean`): `wordArrays` = 318 (tier-1 ids up to `61 + 256`),
  `slotArrs` also lists the tier-1 slot arrays.
