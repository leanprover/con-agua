# Lane ctlglobals: the spine top `CTL[136]` as a named global (pilot, measured, not landed)

`docs/design/lrecords.md` §7.5 scoped the ten hot non-count `CTL` slots and proposed a pilot on
`CTL[136]` (the top of the spine stack `SPN`) before deciding on the per-call slots `200`, `136`,
`192`, `137`. This is that pilot. Base: master bc0cd49b. The work in progress is on branch
`ctlglobals-wip` (0e4d3a70); it does not build end to end.

**Verdict: no-go** for the four per-call slots as a batch, and no landing of the pilot. The
machine-code gain is nil, the proof saving is real but small for the work, and the frame
infrastructure the change needs is a wide change to `MemFrame` (§3). Details and numbers below.

## 1. What was done

* **Global.** `SPTOP : L.GVar := ⟨0⟩` (`Arena/Globals.lean`; ids `1`‥`7` stay free). Id `0` keeps
  `checkerTab.ng` at 12, so the table and the stub's save area do not move.
* **L code.** The 122 accesses `CTL.u64[136]` in 18 files became `SPTOP`. The one indirect read,
  `top := call ctl_get(136)` in `iota_certs_full`, became `top := SPTOP`; `ctl_get` had no other
  caller, so `ctlGetL`, its model `ctlGetW`, its spec and its entries in seven function lists go.
* **Spine relation.** `spTop m := m.glob SPTOP`; `spTop_setG`, `spTop_set64` (simp), `SpineR.setG`
  (replaces `SpineR.setCtl`), `spW_setG` (replaces `spW_setCtl`).
* **Frames (§3).** A global is named in a write set's word list by its slot `g.slot = 2^32 + id`;
  `MemFrame`'s fourth conjunct, the vacuous `m.SameShape m'` (`True`), became "every global whose
  slot is not in `C` is kept". `closedW`/`okWB` allow `g := e` only for `g.slot ∈ C`.
* **Converted and checked** (each module elaborates with no error or warning): `WhnfBase`,
  `WhnfCoreRefine`, `WhnfCoreApp`, `WhnfSpineArgs`, `WhnfIota`, `WhnfIotaRefine5`, and the frame
  infrastructure below `WhnfBase` (the full build reaches every module that does not import a spine
  file).
* **Not done:** 35 files that still carry `CTL[136]` bound conditions (127 lines: `InferBodySpine*`,
  `DefEqStuck*`, `InferBodyBind`, `IndReal*`, `InstLP*`, `WhnfIota*Refine*`, …), the generated
  error models `Verdict/WhnfModels{2,5,6,7}E.lean` (their `grind` now meets `St.setG`/`Mem.setG`;
  `WhnfBase` tags the global lemmas `arena_grind` for that, not yet checked), `checker_prog.py` and
  `asm_file.py`, the gates.

## 2. Measurements

**`checker.s`.** Compiled from master's `checkerProg` with every `CTL[136]` access (and the
`ctl_get(136)` call) rewritten to the global (a script over the program, `_tmp/ctlglobals/EmitG.lean`,
so the numbers hold before the proofs): 214 993 → 214 678 lines (−315). A constant-index `CTL` access
is four instructions (length compare, branch, base load, load or store), a global one; about 105 sites
lose three each. Verdicts: `scripts/diff-e2e.py --bin` agrees on all 634 fixtures.

**Run time** (`scripts/bench.py`, interleaved, cpus 90–91 pinned, machine load 13–24):

| fixture set | instructions | cycles | wall |
|---|---:|---:|---:|
| `init` (Lean's `Init`, 273 416 M instructions on master) | −0.47 % (272 127 M) | −2 % | within noise (spread 33–73 %) |
| `arena/good/init-prelude` | −0.2 % | | within noise |
| `default` (13 fixtures) | ±0.00 % (identical except `c04a`, −0.02 %) | +0.6 % | +1.1 % (noise) |

The spine top is touched once or twice per `whnf`/`infer` step; three instructions of an
L1-resident bounds check do not show.

**Proof lines** (diff against the merge base, branch `ctlglobals-wip`):

| part | net lines |
|---|---:|
| frame infrastructure: `GVar.slot`, `MemFrame`'s global conjunct, `Mem.KeepG` (the models' global frame), `closedW`/`okWB`/`WFrame.setG` | +81 |
| `WhnfBase` (new lemmas, the `arena_grind` tags) | +19 |
| converted spine files (`WhnfCoreApp` −23, `WhnfCoreRefine` −9, `WhnfIotaRefine5` −33, `WhnfSpineArgs` −6, `WhnfIota` −5) | −76 |
| 116 files of mechanical renames (`rdW (m.arr64 CTL) 136` → `m.glob SPTOP`, `set64 CTL 136` → `setG SPTOP`, `[136]` → `[SPTOP.slot]` in frames, `MemFrame.setCtl _ 136` → `MemFrame.setG _ SPTOP`, `SameShape` → `KeepG` on the model frames) | 0 |
| **total so far** | **+16** (129 files) |

Where the saving comes from: the `(136 : Word).toNat < (m.arr64 CTL).size` facts. Every spec of a
writer of the top carried one in its post (the L store's bounds check), every loop invariant and
restore lemma (`StackKept.restore`, `peel_restore`, `peelFull_ref`) took one, and every call site
threaded it (`size_set64` rewrites, `by_cases` on it, `of_ite_none` on the model's guard). In the
converted files these went, at about 3–6 lines each. The renames are line-neutral.

**Elaboration time**, `lake env lean` per module, base and branch back to back, two rounds:
`WhnfCoreRefine` 1.6/1.6 s → 1.6/1.5 s, `WhnfCoreApp` 2.0/2.1 s → 1.9/1.9 s, `WhnfSpineArgs`
1.7/1.7 s → 1.7/1.7 s. No change beyond noise.

**Frames and side conditions that disappear.** In the converted files: the `CTL`-size bound in every
spec post and loop invariant of a top writer, and the `rdW_set64`/`ite_eq_left ⟨rfl, rfl, …⟩`
read-backs of the top (now `spTop_setG`, `rfl`). Frames do **not** disappear: a function that moves
the top still names it in its `MemFrame` list (`[SPN] [SPTOP.slot]` for `[SPN] [136]`), and the
`StackKept.of_*` lemmas still need the slot outside `C` (§3).

## 3. Why frames stay: globals in `MemFrame`

`lrecords.md` §7.5 expected that "a global write leaves every array, so the slot entries of
`MemFrame` lists go", with the global's own frame from the program text (`closedG`, `globsIn`).
The proofs say otherwise. About 95 places derive "the top is kept" from a callee's `MemFrame`
(`StackKept.of_frame`, `of_const_frame`, `of_app_frame`, …, 72 uses; `hf.2.1 136 _`, 23 uses), and
most of those frames come from the store library's models (`consInternM_frame` over
`consInternM_out`, `pushRec`, `kgrowM`), not from a text check. Two ways:

* **Globals outside `MemFrame`** (the existing design: `WFrame` closed under every `setG`, globals by
  `closedG`). Every one of those ~95 sites then needs a separate "the global is kept" fact for its
  callee: a `globsIn` check per call-closed family carried in the program bundles
  (`WhnfDeltaProg'`, `IotaProg'`, …) and an extra argument at each `StackKept.of_*` use, threaded
  through the generic arena-frame lemmas (`InstLPWalkStep`, `CoreWalks`, `DefEqLeaves2`, …).
  Estimated +200 to +300 lines for the top alone.
* **Globals inside `MemFrame`** (what the branch does). `MemFrame A C m m'` keeps every global
  whose slot is not in `C`; writers of a global list its slot. Callers need nothing new. The cost is
  that every producer of a `MemFrame` must now show the globals kept: free for `set64`/`setCtl`/
  `refl`/`trans`/`mono` and for the text check, but the model frames carried the vacuous
  `SameShape`, so 26 files switch it to a real `Mem.KeepG` (`m'.glob = m.glob`), proved through
  `set64` by `rfl`. Most are mechanical; a few consumers took the vacuous fact and now take
  `trivial`. +81 lines, a change to `Arena/Frame.lean`, `L/WriteSet.lean` and the store library's
  model lemmas (`ConsLibSpec`, `SlotGrowSpec`, `IndCopy*`, `Freeze*`, `LevelHeapRel`, `Scratch*`):
  a `--wide` entry, and in files the model-generation lane is converting.

The second is the right design if globals are pursued (the other slots then reuse it), but it does
not remove frame entries; it renames them.

## 4. Projection and recommendation

| slot | bound facts on master (`(k : Word).toNat < … CTL.size`) | L accesses | expected net lines | work |
|---|---:|---:|---:|---|
| 136 (finish the pilot) | 142 (127 left) | 122 | −150 to −350 (incl. the +81 infrastructure) | 8–11 h more: 35 files by hand, 4 generated model files, program and `checker.s` regeneration, gates |
| 200 (`IW` top) | 72 | 7 | −100 to −200 | 6–8 h (114 frame lists renamed; the inductive stage's proofs) |
| 192 (`LH` top) | 3 | 21 | about 0 | 2–3 h of renames for nothing |
| 137 (`BSTK` top) | 7 | 9 | about 0 | 1–2 h of renames for nothing |

Run time: nothing measurable for any of them (136 is the hottest; 200, 192, 137 are touched less).

**No-go.** The case for the globals was frame entries and side conditions; the frame entries stay
(§3) and only the `CTL`-size side conditions go, which pays for slots 136 and 200 at roughly 20–30
net lines per hour of work, and not at all for 192 and 137. Against it: a wide change to `MemFrame`
and the store library's model frames, colliding with the model-generation work, and the first-pass
estimate (8–14 h for all four) was low by about half for the top alone. If the `CTL`-size bounds
become a real obstacle later (a lane that needs `CTL` resized or tiered), `ctlglobals-wip` holds the
frame infrastructure and the first converted files; merge it after the model-generation lane has
landed, infrastructure first as its own `--wide` entry.

New L code keeps using named globals for new tops and counters (the existing rule); this verdict is
only about migrating existing slots.

No twin deviation: con-ron has no field for the spine top (it recurses and keeps lists), and the
value and its updates are unchanged.
