# Lane reproof: could better automation have saved ronsync2's re-proving?

A study lane (2026-11-09, Opus). Question (user): look at one of ronsync2's changes, follow its ripple
through the proofs, and decide whether re-proving by hand was the right way, and what reliable
automation would take. Everything here is read off ronsync2's branches with git (`master 09a78343` →
`ronsync2-p3e-defn 0108e00f`, the union of `ronsync2`, `-p3a`…`-p3e-defn`, `-p3e-w2`); nothing of
theirs was touched. The prototypes and the scripts that produced the numbers are on branch
`reproof-proto` (`_proto/`, a commit on top of `ronsync2-p3e-defn`), not on master.

## 1. The change studied: the two-tier record pool

`EREC` became tiered (ronsync2 journal §4): tier 0 holds the stream index's and the pins' records, tier
1 a job's own; a record address carries its tier in bit 40; reads are the tagged load `EREC⦃a⦄`, writes
the L call `erec_put(a, v)`; decoders read through a reader `Nat → Option Word` (`erecP m`, `aread`)
instead of an `Array Word`. On the proof side this is `IWOK` 5 → 9 fields, `IWGrow` 4 → 6, `erA` from an
array to a reader, `erRd`/`erRdT` for `rdW (m.arr64 EREC)`, `erecP_getE` with a `2^40` premise, write
sets that exclude `tier1 EREC` and `CTL[130]`, `ErecKeptRec` over both tiers, and so on.

It is the clearer example than the install phase going away: that change is mostly *new* code (98 new
proof files, 31 k lines: `IndDeclConsts*`, `Quot*`, `Jobs`, `ProjGuard*`, …, genuinely new
refinements of new twin functions), so it says little about re-proving. The tier change touched
existing proofs almost everywhere and added no mathematics.

Confounder: in the same sync, `dn` (the `PropWhen` names) disappeared from `StageR`, `KeepPost`,
`CheckR`, `decCI`, … . It is counted separately below; it is the purest mechanical edit of the sync.

## 2. What the re-proving consisted of

### 2.1 Size and time

| | |
|---|---|
| `ConAgua/` net diff | 990 files, +67.5 k / −60.5 k |
| proof files (no L, no generated) | added 98 files / 31.0 k lines; deleted 66 / 15.6 k; modified 826 |
| gross churn (sum over 822 commits touching `ConAgua/`) | +133.8 k / −126.8 k, i.e. twice the net: the stage-2 "comment out", then ~45 "restore rounds" |
| agent time, sum of gaps ≤ 45 min between a helper's commits | 66 agent-hours (a lower bound: first commits and long thinking gaps are not counted) |
| of which commits whose subject names tiers/`IWOK`/`erRd`/`erec_put`/readers | 175 commits, 12.6 h; frames/keeps/closures another 9.1 h (109 commits) |

### 2.2 Declarations, master vs `ronsync2-p3e-defn` (by name, generated files excluded)

| status | decls | changed lines |
|---|---:|---:|
| unchanged | 18 684 | 0 |
| only `dn` removed | 450 | 955 |
| statement changed, proof identical | 1 043 | 2 333 |
| proof changed, statement identical | 1 882 | 9 032 |
| both changed | 1 455 | 22 671 |
| new | 2 457 | (35 k lines) |
| gone | 2 016 | (28.7 k lines) |

The 4 506 modified declarations carry 30.4 k changed lines. Tagging each declaration's token-level
change: 1 162 of them (17.4 k changed lines) touch the tier vocabulary (`erRd`, `erecP`, `aread`,
`erec_put`, `tier1`, `IWOK` fields, `2^40`); 1 150 touch `dn`; 975 touch frame vocabulary (write
sets, `Keep`, `Frame`, `closedA`, …). 689 declarations are changed *only* in tagged tokens (454 only
`dn`, 170 only reader renames).

Layout leaks on master that the change had to rewrite: 2 768 occurrences of `arr64 EREC` in proofs
(336 left after), 1 166 of `rdW (… .arr64 EREC)` in 150 files, 258 decoder signatures over
`a : Array Word`, 189 `EREC.u64[…] :=` stores that became 189 `call erec_put` (each one a callee in a
model, a spec premise `hpu : p.lookup "erec_put" = …` at 47 sites, and a frame leaf).

### 2.3 By kind (from the diffs)

* **Statement-only threading** — a premise or field passed through: `dn` (2 265 edited lines,
  450 declarations changed only by it), `hS.iw.erSize`/`hsz` premises dropped, `erecP_getE (…) (by
  have := hS.iw.er; have := hS.iw.erCap; omega)` added at the call sites (`614d1db40`).
* **Reader swap** — `rdW (m.arr64 EREC) x` → `erRd m x`, `Array Word` → `Nat → Option Word`, `+
  aread_apply` in `simp only` (372 occurrences), `vcgen […, ld64_rdT_spec, evalE_tld, tld, …]`,
  `finish (gen := 20) [rdW_eq, erRd_get]`.
* **Invariant-preservation boilerplate** — positional `obtain ⟨h1, h2, h3, h4, h5⟩ := hA.ok` grown
  to nine with four new `by rw [hf.arr (tier1 EREC) …]; exact h6` lines. `94cb1ef5a` ("PrepRef:
  pPrepCore_ok restored", +275 lines) differs from master in exactly that: 20 lines in three copies.
* **Frame/footprint facts** — write sets and closures regenerated or restated to exclude both tiers
  and `CTL 129/130` (`bbc4b2260`, `3e85a21a5`), "leaves" for the new `erec_put` callee
  (`closedWL`), new `*Closed`/`*Frame`/`*Leaves` files.
* **Address and bounds arithmetic** — tagged offsets below `2^40` (`erOff`, `erTier`, `cap_check` on
  both tiers), and the decoders' old `(m.arr64 EREC).size` bound reasoning replaced by `erecP_lt64`.
* **Restoring master's proof unchanged** — 1 043 declarations end with master's proof verbatim; the
  commits "restored", "re-proved", "master proofs restored" (171 commits, 8.5 h) are mostly this.
* **Genuinely new reasoning** — the tier machinery itself (`erecPutMem_arr`, `ErecGrow`, the
  `RdOK` readers, `IWOK.frame` with defaulted tier-1 premises): a few hundred lines in
  `IndIface`, `Tiers`, `ErecRd`, `DeclBase`.

### 2.4 Short declarative proofs vs long manual ones (the user's question)

Proof form of the 1 162 tier-touched declarations, final text:

| form | decls | changed lines | lines |
|---|---:|---:|---:|
| declarative, ≤ 12 lines with `vcgen`/`finish`/`grind`/`sym` | 95 | 241 | 1 312 |
| short manual (≤ 12 lines, none of those) | 321 | 2 455 | 2 911 |
| long manual (> 12 lines, none of those) | 372 | 10 419 | 26 958 |
| `vcgen`/`grind` but 13–40 or > 40 lines | 20 | 230 | 1 303 |
| term proofs and definitions (hand-written `…W` models 66, `l_model` 72, L 30) | 354 | 4 094 | 7 271 |

A declarative proof cost **2.5 changed lines** on average, always a vocabulary entry
(`finish (gen := 20) [natSuccOkW, ntBW, tierW, idxW, erRd]`); a long manual one **28**. The long
manual ones by shape: 208 walk a hand-written `…W` model by `rcases h : callW …`/`triple_of_callW`
(6 916 changed lines, e.g. `cdf_ref`, `ccv_ref`, `caps_rel`); 122 are decoder lemmas (2 356); 36
frame/invariant proofs (1 045, e.g. `pass_ref`). The manual work sits in the model walks: the
model's shape moved (`erRd_foldN`, an extra call for `erec_put`), so every
`rw [ite_eq_left (by simpa using hl)] at hw` and positional `obtain` had to be redone.

## 3. Candidates, tested on a sample

**The sample.** 64 tier- or `dn`-touched lemmas of ten files (DeclCanonSpec, BoolCtorTyped,
DeclNatGuard, DeclNatLit, DeclNatTy, DomsW, BlockRecNameSetOk, MemberNames, StripTeleSpec,
PrepRef; 365 changed lines in ronsync2): master's proof put under ronsync2's new statement, the
module elaborated (`lake env lean`, `LEAN_NUM_THREADS=2`, each file 1–45 s), a lemma counted closed
when it has no error. Variants (`_proto/tools/exp.py`):

* **V0** master's proof verbatim: **19 / 64** close. Most of DeclCanonSpec's `vcgen` specs (11) need
  no edit at all, although ronsync2 edited them.
* **V1** a sync codemod, five regex rules (drop `dn`, `rdW (X.arr64 EREC)` → `erRd X`,
  `IWGrow.erecPExtR` → `.ext`, `X.set64 EREC` → `erecPutMem X`): **30 / 64**.
* **V2/V3** V1 plus the new reader lemmas added to `simp only`/`vcgen`/`finish` lists, the dropped
  `iw.erSize` premise removed: **35 / 64** (a blind add hurts as often as it helps: the `vcgen`
  additions broke 10 DeclCanonSpec proofs that V0 closes, so the vocabulary has to be an attribute
  set chosen once, not text pasted into every call).

The 29 left, read one by one: 9 declarative proofs that need one vocabulary entry (`erRd`,
`erRd_get`, the tagged-load specs) — automatic once those lemmas carry the project's grind/spec
attributes; 7 decoder lemmas that reasoned about `(m.arr64 EREC).size` (`cvWordsAt`, `natCvWords`,
`tagWord`, `lpsW_dec`, `memberNamesW_dec`, `decCI_tag`, `erToIwW_decS`) — never touched had
master's statements used a reader API; 4 positional `IWOK` proofs (`StageR.set_iw/set_top`,
`stripTW_ok`, `pPrepCore_ok`); 6 manual model walks whose `ite` rewriting no longer matches
(`natIndOk/ZeroOk/SuccOk_ref`, `natOpCod_ref`, `natOpStoredOk_ref`, `boolCtorOk_ref`); 3 genuine
interface changes (`pinFind_call`'s new premise, `partsGH`'s `decPLB`, `brwW_sim`'s `nrF_ok`).

So **35 of 64 (55 %) need nothing but a script, 55 (86 %) are mechanical given the right
vocabulary, encapsulation and bundling, 6 (9 %) are manual walks, 3 (5 %) are real.**

**(a) Encapsulation** (the pool behind an interface, as ConsLib). The 7 decoder lemmas and most of
the 1 166 `rdW (… .arr64 EREC)` rewrites exist only because master's statements read the array.
ronsync2 has now built that interface (`erecP`, `erRd`/`erRdT`, `RdOK` readers, decoders over a
reader), so the next layout change of `EREC` stays inside `ErecRd`/`Tiers` — as long as new proofs
do not reach under it (336 `arr64 EREC` are still in proofs). The remaining leak is the write side:
`erec_put` is an L *call*, so every model with a store got a callee, a spec premise and a frame leaf.
A tagged store primitive (`EREC⦃a⦄ := v`, the twin of the tagged load) would keep writes as stores
whose model rule is generic. Saving on this change: the reader half ~7 of 64 lemmas and most of the
reader-swap lines; the store half ~189 model call sites. Cost: the read API is done; the store
primitive is a compiler and semantics change (~1–2 days, it belongs to the L-array line of work).
Fits early cutoff well (a change behind the API rebuilds the API's importers only by statement).

**(b) Generated frames.** Already there: `closedA`/`closedW`/`closedWL` decided on the program text,
the function lists by `scripts/*_fns.py`, `run_keeps` for `Stable` predicates. The tier change cost
here was updating the lists and adding leaves for `erec_put`, not proving frames. What upstream did
instead is better: **frame by construction** (con-ron DESIGN, Task #141: "the frame of the bracket is
the tier being `&`"; "not taken: a frame proved by walking the ~800 definitions phase A reaches").
The L analogue is a sealed tier in the semantics (a store into a sealed tier faults), so "a job does
not write tier 0" is one theorem about the semantics, not a write set per caller. Cost ~2 days
(semantics + compiler lemma); saves every tier-0 frame fact of this and later syncs.

**(c) grind/simp annotation sets.** Measured (`_proto/GrindFrame.lean`, `GrindStage.lean`): `grind
[IWOK_iff, iwTop, erTop, erecTop1, MemFrame.arr, MemFrame.size, MemFrame.ctl]` closes the `IWOK`
and `IWGrow` frame goals of the sample (set of `IW`, set of the `CTL` top, a four-array literal
write set, `IWGrow` over a frame keeping the pool), and master's `StageR.set_iw/set_top` restated
with grind for the `IWOK` part: 6 of 6 goals by grind (plus 3 by the `frame_inv` macro over the
existing frame lemmas), 224 ms of grind for `GrindFrame.lean`'s four, under 2 s and well under 1 GB
per file. A
grind proof names no field, so it survives `IWOK` growing to nine. Reliability on the declarative
proofs: 9 of the 29 failures are one missing attribute each. None of the new reader lemmas carries
`@[arena_grind]` or `@[spec]` today; they are scattered (`erRd_foldN` in `DeclNatGate`, `erRd_get` in
`NestBlockOfKey`, `ld64_rdT_spec` in `ErecRd`). Saving: ~14 % of the sample's lemmas; cost: 2–4 h
(one vocabulary file, attributes, a check that the `vcgen` modules stay within budget).

**(d) Invariant bundling.** `IWOK.frame`'s tier-1 premises with `:= by decide` defaults kept its
callers unchanged; the positional `⟨h1, …, h5⟩` destructurings did not (4 of 64 sample lemmas,
`94cb1ef5a`'s 20 lines in three copies). Rule: never build or destructure an invariant positionally
outside its own file; use field names, an `of_frame` lemma with defaulted side conditions, or grind.
Cost: a lint-level rule; saving small but certain.

**(e) A dedicated tactic.** Baseline from the twins' history:

* con-ron Task #120 (2026-10-13) built `bridge_frame`/`bridge_fwd`/`vc_arm`, later `bridge_auto`
  (`ConRon/BridgeTactic.lean`, 2 358 lines of meta code, precompiled) for Theorem 1's verification
  conditions, which had been closed *by position* (`case vc15 => rename_i …`; 286 `case vcN` lines
  rewritten at every con-leche sync though "nothing mathematical had moved"). It searched the
  context for frame facts (`Ext` chains, `CheckOK.mono`, denotations carried along) and keyed arms
  by their branch hypothesis.
* Tasks #121–#123 (2026-10-14) replaced it by `sym only [bridge_grind, …] => vcgen [f, callee specs]
  <;> finish`: 2 255 lines of custom tactic → 0, the twenty modules 1 105 G → 379 G instructions
  (−66 %). What the grind form does better: no search code to maintain, the frame chain is grind's
  order solver (`grind_pattern denote_ext_le`), failures are a goal grind could not close rather than
  a search that fell through, and the cost was lower. The price was restating lemmas in grind shape
  (equations over named projections, no `∃` in premises, no `fun` reaching grind, one unconditional
  equation per twin function: con-ron CLAUDE.md, "Theorem 1 verification conditions").
* But con-ron kept a custom tactic where the problem is not a VC: `Refine2/Tactic/Lockstep.lean`
  (2 670 lines, Theorem 2): two programs stepped bind by bind, the callee picking a registered
  `@[lockstep]` lemma, a stuck goal pointing at the bind where the two programs diverge. Its own
  docs say why it is modelled on Aeneas's `progress`, not on `mvcgen`.

Our long manual proofs are of the second kind: 208 of the 372 tier-touched long manual proofs walk
a hand-written `…W` model against the twin's monadic code call by call (`rcases h : callW p n "f" …
with _ | ⟨r, m⟩`, `triple_of_callW`, `rw [ite_eq_left …] at hW`). Two fixes, in order:
(1) where the `…W` model is only a step between L and the twin, state the refinement directly over
the generated `l_model` and prove it declaratively (con-ron #123's recipe), so the model's shape
stops mattering; (2) where it stays a call-by-call zip of two programs, a `lockstep`-style tactic
keyed by the callee, with `@[ref_step]` lemmas (each `…_ref`/`CallRef`), is justified: it is what
con-ron kept. Throwaway sketch (`frame_inv` in `_proto/GrindFrame.lean`) only for the frame part,
where grind already suffices, so no frame solver is needed. For the lockstep part: cost 3–5 days for
a first version (con-ron's took two rounds and a "tactic owner"), plus restating the walks; risk:
one more piece of shared core, elaboration time to measure per module (con-ron's precompiled meta
code was 2.3 G against 2.5 G of hand cases), memory not an issue at these sizes. It fits early
cutoff (a tactic lives in its own module; proofs are not exported).

## 4. Stepping back: upstream and the process

**Upstream's effort for the same change.** con-ron #141 + #143 changed `proof/ConRon/{Refine*,
Bridge}` by +42 k / −47 k lines in ~11 h of wall time (#141: 30 commits over 3.2 h; #143: 232 commits
over 7.9 h, parallel Theorem 1 / Theorem 2 lanes), against ronsync2's +67 k / −60 k in ~26 h. The
difference is not the twin side (ours mirrored it, `FoldOK` at a job's view took the set theory like
upstream's `view_foldOK V`); it is the memory encoding, which has no upstream counterpart: upstream's
two tiers are a Lean structure behind a `&` borrow, ours are bit 40 of an address in a flat array.
Upstream's own note on the core tier: "gained the two arguments and nothing else: a mechanical
pass". Mirroring upstream's proof structure more directly would not have removed our layout
reasoning; giving L the same *kind* of guarantee (sealed tier, tagged store) would.

**Process.** Three things cost more than any tactic would have saved:

* *Comment out, then restore.* Stage 2 commented out or sorried a large share of the proofs to get
  the L code building, and ~45 restore rounds put master's text back: the gross churn is twice the
  net diff, and 1 043 declarations end with master's proof unchanged. V0 shows 30 % of the sampled
  tier-touched lemmas needed no edit at all. A **re-proof ladder** run on every declaration that
  fails after the statements change — master's proof; then the codemod; then with the vocabulary
  attributes; then `sorry` with a ticket — would have done that in one pass (the sample: 55 %
  closed with no agent involved; each file 1–45 s).
* *Parallel helpers re-invented the vocabulary.* `IWGrow.erecExt`, `.erecPExt`, `.erecPExtR`,
  `.ext`, `.erExt` (five names for one fact), `IWOK.frame` and `IWOK.of_keep`, and merge fix-ups
  renaming between them (`614d1db40`: 15 files). A short "interface first" stage, one owner, before
  the fan-out — the invariants, the reader API, their frame lemmas and attributes in one file —
  would have stopped that (con-ron #123 did the same: lanes wrote candidates, one owner consolidated).
* *Statements first.* The ladder only works when the new statements are in place; ronsync2 restated
  and proved in one go per area.

## 5. Recommendation (ranked; hours are agent-hours)

| # | what | build cost | saving per sync of this size | notes |
|---|---|---:|---:|---|
| 1 | **Re-proof ladder** (`scripts/`, after the statements change: master proof → codemod rules kept per sync → with the attributes → sorry list), run before any helper starts | 6–8 h | 15–25 h (the restore rounds, and ~55 % of re-proved lemmas) | measured on 64 lemmas; no risk to the build (it only proposes text) |
| 2 | **One vocabulary file per invariant/encoding**, its lemmas `@[arena_grind]`/`@[spec]`, `IWOK`/`IWGrow` frames by grind; never build or destructure an invariant positionally | 3–4 h | 4–8 h | grind measured: 6 goals, 224 ms |
| 3 | **Interface-first stage, one owner**, then fan-out | 0 (process) | 5–10 h | removes the duplicate-lemma and merge-rename churn |
| 4 | **L: tagged store primitive and sealed tiers** (frame by construction) | 15–25 h | 5–10 h on any sync that moves a pool's layout | part of the L-array line of work; also removes the `erec_put` leaves |
| 5 | **Declarative refinements over the generated models**, and a `lockstep`-style tactic for the call-by-call walks that remain | 30–50 h | 10–20 h (the 208 model walks: ~40 % of the tier change's manual lines) | con-ron's history: grind form for VCs, a custom tactic kept only for lockstep |

The first three pay back within one sync; 4 and 5 are structural and pay back over several.

Out of scope here and not checked: the elaboration-time effect of item 2 on the big `vcgen` modules
(con-ron measured the global-rule cost per module: +0.8 G for one `→` rule), and how much of the
208 walks can be restated over `l_model` without a model change.
