# Lane recoffs: named record offsets

**Question** (the user, 2026-11-13): instead of the compiler-owned record layout (lrecords
R1/R2), the cheaper middle ground: "never use literals in the code/proof, but defs, so that to
change the layout you just need to change a few lines". The test: compact `IIndCaps` (15 words, 7
of them dead since ronsync3/ronsync4) and count the lines that change outside the layout files.

## 1. Inventory (master 8ea7eccbf)

Script `_tmp/recoffs/inv.py` (comment-stripped; generated `Checker/Prog*`/`Asm*` excluded; L text =
inside `lfn`/`lblk` blocks). Line counts.

**L code.**

| what | lines | files | largest |
|---|---:|---:|---|
| `EREC⦃e + N⦄` reads | 339 | 29 | DeclArmsCanon 42, WhnfIotaRec 28, BasisL 26, DefEq 25 |
| `EREC⦃q⦄` (offset 0: kind, name, eta) | 119 | 28 | |
| `erec_put`/`er_put5`/`er_copy_er(d + N, …)` writes | 169 | 13 | RecCheck 30, CIRead 27, BasisL 23 |
| record sizes `erec_alloc(N)`, size tables `n := 20` | 14 + 4 | 11 | |
| `IW.u64[x + N]` (inductive-stage scratch records) | 563 | 13 | DeclArmsNat 129, RecGen 82 |
| front `DECL`/`DLP`/`DIND[q + N]` | 45 | 6 | IndApply 17 |

Offsets by value (EREC reads): `+3` 122, `+5` 68, `+2` 61, `+1` 53, `+6` 39, `+4` 32, `+7` 28,
`+8` 19, `+9` 13, `+10‥19` 26.

**Proofs.**

| what | lines | files |
|---|---:|---:|
| `erRd m (x + N)` | 524 | 87 |
| `erecP`/`erA m (x.toNat + N)` | 156 | 52 |
| decoder words `nat?/hd?/hlist? a (q + N)` | 106 | 21 |
| `callW … "erec_put" [x + N, …]` | 26 | 4 |
| decoder unfolds (`simp/unfold [… decCI/decCV/decCaps/decRule/decTbl …]`) | 187 | 86 |
| `set64 IW (… + N)` / `rdW (arr64 IW) (… + N)` | 672 | 139 |

**How proofs use them.** (1) Decoder equations: the same extraction fact re-proved in several
files by unfolding the decoder and fixing the offset (`PosFt.decCaps_counts`,
`FormerNZRef.decCI_ind_nz`, `InferProj2.decCI_indNC`, `NcGoW.decCaps_ctors`,
`NestBlockOfKey` (`q + 15`/`q + 16`), `ClassNPcOf.decCI_ind_cases`, `QuotCiT.decCaps_sh`,
`DeclAndPinIndDec.decCaps_reloc`, `IndRecRead.decCI_indCaps`). (2) Syntactic matching: a model
or a hand-written statement must say `q + 12` where the L text does. (3) Omega bounds and frames
(`(q + k).toNat = q.toNat + k`, `EKeep`/`Holds` ranges `c ≤ i < c + 15`, `wd_set_ne … omega`
chains). (4) Hand-written comparison models (`capsEqBB`, `ciEqRestB`).

## 2. Named offsets: design

* `ConAgua/Arena/RecLayout/Caps.lean` (`L.Caps.eta`, `nIdx`, `neverZero`, `allOff`, `allLen`,
  `nparams`, `ctorsOff`, `ctorsLen`, `size`), `RecLayout/CI.lean` (`L.CI.kind`, `cv`, `indCaps`,
  `indSize`): one `Word` def per field, the layout facts (`f.toNat < size.toNat`, slice length
  word after offset word) next to them.
* `RecLayout/CapsDec.lean`: the decoder's facts once: `decCaps_eq_some` (word by word),
  `decCaps_of`, `decCaps_rd` (at L's word addresses, any `RdOK` reader), `decCaps_congr`
  (record carried to another reader), `decCI_indInfo`, `decCI_indInfo_rd` (an `indInfo`
  record's caps at `q + (CI.indCaps + Caps.f)`).
* L text: `EREC⦃q + ⟪Caps.nparams⟫⦄`, `EREC⦃p + ⟪CI.indCaps + Caps.nIdx⟫⦄`,
  `erec_alloc(⟪CI.indSize⟫)`. The compiler evaluates the constant: `checker.s` unchanged.
* A field at offset 0 (`eta`, the kind word) stays `EREC⦃q⦄`: `q + ⟪Caps.eta⟫` compiles to an
  extra `add` (the compiler folds no `+ 0`).

**Finding: the defs must be `@[reducible]`.** With a plain or `@[irreducible]` def the generated
`l_model` proofs slow down by 2–3× and time out (ClassNPcOf's `step1`: 200 000 heartbeats; 21.7 s
for the module with 2 000 000 vs 8.9 s with numerals): `grind` meets `UInt64.toNat Caps.nparams`
atoms where it would have seen numerals (a `grind`-attribute of value equations did not help).
With `@[reducible]` the generated proofs evaluate the names as before (8.9 s), and statements keep
the names where they are written. The cost: a proof that still says `q + 17` keeps working
(reducible defeq), so a leftover literal is only found by changing the layout: step 3.

### Batch 1: the caps record's reads by name (this landing)

* The decoder (`decCaps`, `decCI`'s `indInfo` arm) reads at `q + Caps.f.toNat`,
  `p + CI.indCaps.toNat`.
* L: every read of a caps field (`IndPos`, `IndPos2`, `RecClass`, `WhnfIota`, `Infer`, `DefEq`'s
  three η reads, `DeclArmsCanon`'s `caps_eq_*`), `rci_caps`' field writes, the copy
  `er_copy_er(r + ⟪CI.indCaps⟫, p + ⟪CI.indCaps⟫, ⟪Caps.size⟫)`, the record sizes
  `⟪CI.indSize⟫` (`rci_ci`, `ci_at_lps`, `ind_rec_copy`, `ind_info_rec`, `ind_type`).
  Construction code that writes a whole record positionally (`block_caps_fin`'s three `rec5`s,
  `ind_info_rec`'s three `er_put5`s, the front's `ind_caps`) is left for batch 3 (builders).
* Deleted duplicates, now `CapsDec` lemmas: `PosFt.decCaps_counts`, `FormerNZRef.decCI_ind_nz`,
  `decCI_ind_n`, `QuotCiT.decCaps_sh`, `NestBlockOfKey.decCI_indInfo_bound` (and its 15/16-word
  arithmetic in `nestBlockOf_key`); restated over names: `InferProj2.decCI_indNC`,
  `IndRecRead.decCI_indCaps`, `ClassNPcOf.decCI_ind_cases`, `DeclAndPinIndDec.decCaps_reloc`
  (and `relocK`'s size), `QuotCiT.ciCopy` (any offset `o ≥ 5`).
* `checker.s`, `pins.bin` unchanged (`asm_file.py --check`), the `Prog*` files unchanged
  (`checker_prog.py --check`).
* Unfold sites left outside `RecLayout/`: 8, all in the whole-record writers' proofs
  (`IcaW` 3, `IndInstallRefine2` 3, `CIReadRefCaps` 1, `CIReadRefCI` 1), which batch 3 rewrites.
* 45 files, +514/−312 lines (with the three new `RecLayout` files, about 280 lines).
