# Lane syncproc: the re-proof ladder and the sync protocol

Lane of 2026-11-09 (Opus). It takes recommendations 1 and 3 of `docs/design/reproof.md` (approved by
the user: "let's refine our process, there are plenty more syncs coming"). It builds the re-proof
ladder (rec. 1) and writes the interface-first, statements-first protocol into PLAN.md, "Bumping
the twin" (rec. 3). Rec. 2 (one vocabulary file per invariant, with attributes) touches proofs that
ronsync2 is still changing, so it is a follow-up lane: §5 is its brief. Nothing of ronsync2's was
touched. Its branches were read with git, and the measurements ran in scratch worktrees at its
commits.

## 1. What was built

**`scripts/reproof-ladder.py`** (its docstring is the manual). After a sync has changed the
statements, it takes every theorem that fails to elaborate or uses `sorry` and tries, in order:

1. **master**: the base revision's proof text, verbatim, under the current statement;
2. **codemod**: the same after the sync's regex rules;
3. **vocab**: the same with the sync's vocabulary added (rule sections tried in order, or a hook
   module that rec. 2 fills, §5);
4. otherwise the theorem stays at `sorry` (with `--write`) and gets a ticket: file, line,
   declaration, the last rung tried, the first error.

Design points:

* **Matching by name.** A Lean-aware splitter (comments, strings and brackets lexed; namespaces
  tracked; doc comments, attributes and `set_option … in` attached to their declaration) cuts
  each file into top-level declarations, and each theorem into its statement and its proof at
  the first `:=` at bracket depth 0. An equation-style theorem is cut at its first `|` arm. The
  base declaration is looked up by qualified name: first in the same file, then anywhere in the
  base tree (moved or split files), then through a `rename OLD NEW` rule, then by its last name
  component when that is unique. Only the proof comes from the base; the statement is always the
  current one.
* **Only text that elaborates.** Every rung elaborates the whole module with all its candidates
  in place. The module is a copy under the run directory, elaborated with `scripts/lake env lean`
  and the lakefile's `leanOptions` passed as `-D` (the prototype left out `autoImplicit=false`).
  A theorem is closed when no error and no `sorry` warning falls inside it. Once a theorem is
  closed, its text stays fixed for the later rungs. With `--write`, the final text (closed
  theorems at their candidate, the rest at `sorry`) is elaborated once more before it replaces
  the file (atomically). A theorem that breaks only in that final check goes back to `sorry`.
  A file that still fails outside the re-proved theorems is not written.
* **A partial tree.** A file whose imports are not built is reported as `blocked` and skipped. The
  ladder looks only at what fails now, so after a build round it is simply rerun (idempotent).
  While it runs it holds the worktree's `scripts/lake` lock, so no build can start under it.
  A crash in one file is reported and does not stop the others.
* **Resources.** `--jobs 2` lean processes at a time (each `LEAN_NUM_THREADS=1` by default), a
  per-run `--timeout` (900 s) and a per-process-tree RSS limit `--mem-gb 15` (polled; the tree is
  killed above it). SIGTERM/SIGINT kill the running lean processes.
* **Report.** `_tmp/ladder/<worktree>/report.md` (closed per rung and per variant, blocked files,
  the remaining theorems by file), `report.json`, `tickets.tsv`, and `closed/`, the candidate texts
  of the closed theorems (also without `--write`).
* **Replay mode** (`--decls`): exactly the listed theorems, whatever state they are in. This is how
  the ladder is measured on a finished sync. It puts the base's proof back and sees which rung
  closes it.

**`scripts/sync-rules/<sync>.txt`**, one rules file per sync, kept in the repository. It records
the sync's mechanical edits and is the template for the next sync. Format: `[codemod]` with
`sub REGEX ==> REPL` lines; `[vocab NAME]` sections with `sub`, `sub-if IDENT …` (only when the
file mentions `IDENT`) and `use NAME`; `[names]` with `rename OLD NEW`; `vocab_hook FILE.py`. The
first one is `scripts/sync-rules/ronsync2.txt`: reproof.md §3's five codemod rules (`dn` dropped,
`rdW (X.arr64 EREC)` → `erRd X`, `X.set64 EREC` → `erecPutMem X`, `IWGrow.erecPExtR` →
`.ext`), and its V2/V3 vocabulary as the two sections `readers` and `readers+`.

What changed from the prototype (`reproof-proto`: `_proto/tools/exp.py`, `decls.py`): the
prototype matched declarations by bare name, by the first `:= by` anywhere in the text, and
against a pickled pair of declaration tables. It wrote candidates into the worktree's file and
restored it afterwards, ran every variant on every sample theorem, and counted a theorem as
closed by the errors within an estimated line range. The script cuts at depth 0 with
namespaces. It never edits the worktree except through a verified `--write`. It runs a rung only
for the theorems still open, computes exact line spans of the assembled text, and also counts
`sorry` warnings.

## 2. Validation

### 2.1 reproof.md's sample (64 theorems of 10 files)

Replay at `ronsync2-p3e-defn 0108e00f1`, base `09a78343a`, the ronsync2 rules, `--jobs 2`:

| rung | closed | cumulative | reproof.md |
|---|---:|---:|---:|
| (i) master | 19 | 19 | V0: 19 |
| (ii) codemod | 11 | 30 | V1: 30 |
| (iii) vocab (`readers` 3, `readers+` 2) | 5 | 35 | V2/V3: 35 |
| left | 29 | | 29 |

The result is the same theorem for theorem. 33 lean runs, 2.1 min wall, peak 1.3 GB per run.
The first run closed 18 by master. The 19th, `hslice?_bound`, is an equation-style theorem: the
prototype's `:= by` search happened to cut it inside a `have`, and the script now cuts it at its
arms.

### 2.2 ronsync2's stage-2 tree (`3ac31ede5`)

STAGE2

### 2.3 What it would have saved

SAVED

## 3. Using it in the next sync

PLAN.md, "Bumping the twin", step 3 a–d, in short:

1. L code first, then the interface stage (one owner), then the statements. Write the rules file
   `scripts/sync-rules/<sync>.txt` while restating: every mechanical rename, dropped argument or
   reader swap becomes one rule.
2. Build what builds (`LEAN_NUM_THREADS=2 scripts/lake build ConAgua`; failed modules block their
   importers), then, in the sync's worktree:
   `scripts/reproof-ladder.py --rules scripts/sync-rules/<sync>.txt --write`
   (default: the .lean files changed since the merge-base with master; failing = errors or
   `sorry` after one elaboration). Rerun the build, then the ladder again, until no file is
   `blocked`. On a tree that already builds with sorries, `--failing sorry` skips the first
   elaboration.
3. Check `report.md`: a rung that closes nothing is a missing rule. Add the rule and rerun with
   `--steps codemod,vocab`: rung (i) was already tried, and the theorems it closed are no longer
   failing.
4. Hand `tickets.tsv` to the helpers, grouped by file. The ticket's rung and first error say what
   kind of work it is: `statement` = the statement still fails, `no base proof` = new or renamed
   (add a `rename` rule), otherwise a real re-proof.

Cost: about 3 lean runs per file (one per rung whose candidate differs, plus the final check),
each 1–90 s. COST

## 4. PLAN.md

"Bumping the twin", step 3, now has the proof stages a–d:

* a. **Interface first, one owner**: the invariants, encodings and reader/writer APIs the change
  touches, with frame lemmas and attributes, in one file per invariant or encoding before the
  fan-out. One name per fact, and new shared lemmas go through the owner. No positional
  construction or destructuring of an invariant outside its own file.
* b. **Statements first**, then re-proving. Never comment a declaration out, and no "comment out,
  then restore" rounds.
* c. **The ladder** before any helper starts. Write the rules as you restate, and rerun after each
  build round.
* d. **Fan out the tickets**. The brief names the files each helper owns and its reply address
  (the lead's agent id). Helpers message only the lead. A rename of a shared name is the owner's,
  done once as a rule.

The fan-out rule in "Process rules" also gains the reply address. These are the process failures
of ronsync2 that its journal and briefs record. The stage-2 sorry-out and comment-out left
~1430 `sorry`s and ~1180 commented-out declarations, and ~45 restore rounds followed
(`_tmp/ronsync2/brief3.md`). Helpers messaged "main" and the coordinator, so the p3e briefs had to
add "send messages only to the lead at agent id …, never to main or the coordinator"
(`_tmp/ronsync2/p3e-worker.md`). Five names arose for one pool-growth fact (reproof.md §4).
Merges needed rename fix-ups: `ba8547d2c` "renames against clashes", `9d56f1a05` "p3a renames",
`614d1db40` across 15 files.

## 5. Brief for the follow-up lane: the vocabulary files (reproof.md rec. 2)

Start after ronsync2 has landed, from master. Goal: a sync that moves an encoding again
should need no edit in a declarative proof, and none in a proof that only frames an
invariant. Rung (iii) of the ladder then becomes "the attribute set", instead of text pasted
into tactic calls. reproof.md §3 found that pasting text blindly broke 10 proofs that rung (i)
closes.

**Files** (names and places as of `ronsync2-p3b d41542ea5`; re-grep on master):

* `ConAgua/Arena/ErecVocab.lean` (new): the two-tier record pool's vocabulary, moved here with
  its names unchanged: `aread`/`aread_apply` (`EnvRec.lean:153`), `erecP` (`Tiers.lean:469`),
  `erRd` (`IndLibSpec.lean:715`), `erRd_get` (`IndPosSpec/NestBlockOfKey.lean:67`), `erRd_foldN`
  (`DeclNatGate.lean:84`), `erecP_getE`/`erecP_lt*` (`DeclRec.lean:260`), the `erecPutMem` lemmas
  (`IndIface.lean:500`), and the tagged-load specs `ld64_rdT_spec` and `evalE_tld`, `tld`, … from
  `ErecRd.lean:242`. Where the definitions themselves cannot move (import cycles), keep them and
  move the lemmas. The test is that no file outside the vocabulary file and the definitions'
  own files proves a fact about `arr64 EREC` (336 occurrences in proofs at ronsync2's end).
* `ConAgua/Arena/IWFrame.lean` (new), or the bottom of `IndIface.lean`, beside `IWOK`
  (`IndIface.lean:295`) and `IWGrow` (`:317`): the frame lemmas `IWOK.frame` (`DeclBase.lean:52`),
  `IWOK.of_keep` (`IndLibSpec.lean:454`), the one `IWGrow` extension lemma (`IWGrow.ext`; delete
  the aliases `erecExt`/`erecPExt`/`erecPExtR`/`erExt` if any are left), and an `IWOK_iff` in grind
  shape (reproof's `_proto/GrindFrame.lean` on branch `reproof-proto`: `grind [IWOK_iff, iwTop,
  erTop, erecTop1, MemFrame.arr, MemFrame.size, MemFrame.ctl]` closed the sample's 6 frame goals
  in 224 ms).
* Then remove every positional construction and destructuring of `IWOK`/`IWGrow` outside those
  files (`obtain ⟨h1, …, h9⟩ := …`, `⟨…⟩ : IWOK m`): use field names, `IWOK.frame` with its
  defaulted premises, or the grind call. Find them with `git grep -n -E "IWOK|IWGrow"` filtered
  for an anonymous constructor or `obtain ⟨`.

**Attributes.** The project's sets are `arena_grind` (`GrindAttr.lean`, ~600 `grind [… arena_grind]`
calls) and `ind_grind` (`IndGrindAttr.lean`, the inductive stage). The pool's equations over
named projections (`aread_apply`, `erRd_get`, `erRd_foldN`, `erecPutMem_*`) go into
`arena_grind`. The `IWOK`/`IWGrow` frame lemmas go into `ind_grind`, as `grind_pattern`s where
a lemma has no usable left-hand side. No proof in the tree uses `@[spec]`: `vcgen` gets its
specs as terms (PLAN.md's recipe). So first find out (≤ 30 min) whether this toolchain's `vcgen`
reads a spec attribute set. If it does, tag `ld64_rdT_spec` and the tagged-load `evalE_*` lemmas.
If it does not, the vocabulary file exports one named list per encoding, for instance a macro
`erec_specs` that expands into those terms (check that `vcgen [erec_specs, …]` elaborates), and
the ladder hook adds it to `vcgen [` lists. Keep `finish`'s default grind set untouched:
`finish` is core grind's `finish`, so a lemma tagged `@[grind]` reaches every `finish` in the
tree, and that is exactly the cost below.

**The cost con-ron warns about.** A global grind/simp rule costs time in every module that
imports it. con-ron measured +0.8 G instructions per module for one `→` rule. Measure before
and after, on the 20 largest `vcgen`/`grind` modules that import the vocabulary (pick them from
`_tmp/buildstats/buildstats.md`, "Top files by elaboration time", filtered by import closure):
`perf stat -e instructions:u` of `scripts/lake env lean -DautoImplicit=false
-DrelaxedAutoImplicit=false F.lean`, `LEAN_NUM_THREADS=1`, 3 runs, median. Accept a total rise below
2 % and no single module above 10 %. Above that, narrow the rule: a tighter `grind_pattern`, or
the lemma only in the set and not `@[grind]`, so that only proofs naming the set pay. Report
the table in the lane's journal.

**The ladder hook.** Write `scripts/sync-rules/vocab_attr.py` (`candidates(proof, ctx)`, see the
script's docstring) and name it in each future sync's rules file (`vocab_hook vocab_attr.py`).
Variants, in order: (1) the codemod text with the encoding's set added to `grind [`, `sym only [`
and `finish [` lists that lack it; (2) the same with the spec list added to `vcgen [`; (3) an
`obtain ⟨…⟩ := h.ok`/`h.iw` positional destructuring replaced by `have := h.iw` and the
following `exact hN` lines by `grind [IWOK_iff, ind_grind]`. Measure on reproof.md's sample: in
the ladder's replay mode (`--decls`, the sample list is in §2.1's run directory
`_tmp/syncproc/sample.txt`, reproduced in §6) at ronsync2's end, rebased onto the vocabulary
files. The 9 "one vocabulary entry" theorems of reproof.md §3 should close at rung (i)/(ii),
since their master proofs then find the lemmas through the set; the 4 positional `IWOK` ones
should close after the destructuring rule. Report the new 19/30/35 line.

**Out of scope there**: the tagged store primitive and sealed tiers (rec. 4) and the lockstep
tactic (rec. 5).
