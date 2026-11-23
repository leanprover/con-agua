# Lane ronsync8: the con-ron sync de06320f → 8021ddac

Lane of 2026-11-23 (Opus), con-ron `de06320f → 8021ddac` (Tasks #161–#173), con-leche `600d3b58 → bc667610`.
Followed by lane `compare` (verified `--compare` on two lean4export files, upstream #165/#612).

## 0. Stage 0: footprint and stage plan

`_tmp/bump-8021ddac/report.{txt,md,json}` (the coordinator's step 1), then ronsync6's classifier
(`_tmp/ronsync8/fp.py`, outside the repository).

**Upstream.** con-ron definitions: 58 changed, 447 new, 5 removed (most new ones are `--compare`
#165 and modular checking #166); con-leche 51 changed, 148 new. Types: only `ConLeche.Literal`
(the hash, #547/#598) reaches us. `pins/`: one variant file renamed (label only).
Patches: con-leche/0001 and con-ron/0002 conflict.

**Toolchain.** Upstream moved to v4.36.0; ours is nightly-2026-10-20 (4.37.0-nightly, after
v4.36's branch point), and upstream had already adapted to the per-conjunct `vcgen`. The new
trees build on our toolchain with the patch series (§2): no toolchain bump.

**L items** to re-check: 26 (39 markers in 10 files; one gone, `natOpStoredOkAll`).

**Proof declarations**: the report counts 612 mentioning declarations; about 400 of them are
textual hits of short twin names (`NeedsSt.rules`, `Args.closed`, `MixedStep.scoped`,
`ImpsD.isEmpty`, …). Without those: **213 in 97 files**.

| form | count | lines |
|---|---:|---:|
| call-by-call walks (`callW`) | 14 | 1 886 |
| model-arm walks | 4 | 235 |
| declarative, ≤ 12 lines | 1 | 12 |
| declarative, longer | 14 | 557 |
| manual, > 12 lines | 44 | 2 989 |
| manual, ≤ 12 lines | 65 | 652 |

Hand specs: 1 (`check_a`). Theorems with a positional `⟨…⟩` of ≥ 5 parts: 56.

**New twin code to port** (uncited): `Arena/Inductives/IotaRead.lean` (#622, the ι reading rule,
~30 functions); every building block it calls has an L function already.

**Final statements likely to change**: `Final/Twin.lean`'s `SeqAccepts` and three lemmas of
`Final/TwinVerdict.lean` (`checkJobList … I` → `checkJobList … none I`, the twin's new `J`).

**The ROM**: not touched (the ι rule's names are interned from bytes in code, as `name_rec`).

**Kind of sync**: an L-code sync (≈ 30 ported, ≈ 10 changed functions) plus one mechanical
statement change (`J = none`). Ladder estimate: 10–20 % of the failing theorems (the `none`
rule), the rest the port's re-proofs.
