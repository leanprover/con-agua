# Lane `conslib`: one encapsulated cons-table library (journal)

Branch `conslib`, worktree `_tmp/wt/conslib`. Task: the 19 intern (hash-cons) tables get one
library, `ConsLib` (L code + proofs, modelled on `MemoLib`), so that the tables' internals (slot
layout, probing, growth; later lane compopt2's K and S) change in the library only, without touching
the code or proofs of the tables' users.

## Step 1: survey (2026-10-23)

### What is generic already

* **The relation** is generic since the store library (`StoreLib.lean`): `Schema` (record array,
  slot array, width, `CTL` count index, tag), `TierR`/`StoreR` (one tier / both tiers of an L table
  represent the arena's `Tbl`: same nodes in order, same key → handle map, slots index the nodes,
  `GrowR`), `internM`/`pushM` (the L model of an `intern_*`, generic in the schema, but taking the
  two probe results and the room test as arguments), `intern_correctG` (the refinement, once).
* **The growth** is a generic splice (`growBlkG`, `SlotGrow*.lean`), with a per-table hash block
  and its obligation `HashOK`.

### What is not, and where it leaks

* **The L code** is 19 hand copies: `X_find` (the probe, match inline or a call of `X_match`),
  `X_push` (room checks, record words, slot, count, derived columns, growth splice),
  `intern_X` (hash, scratch skip, two probes, push). With them 19 copies of the probe model
  (`aprobeW`, …), the push memory (`apushMem`), the intern model (`ainternW`) and their vcgen
  specs (~300 lines per `XStore.lean`, ~200 per `XRefine.lean`).
* **Users see the models.** A census of the per-table names (`XStore`/`XRefine` declarations)
  used outside those 38 files: 294 files. Most are harmless (the program entries `app_find`,
  `appFind` in `p.lookup` hypotheses and program lists, the arrays `AREC`/`ASLOT` in footprints,
  the relations `AppR`, `ARecRel`), but these look inside a table:
  * `XinternW` (the intern model) with `XinternW_eq` (to `internM appSch … (aprobeW …) …`),
    `XprobeW_arm`, `XpushOK_room`, `XMt`, then `probe_homeG` (116 uses) to feed the probe results
    into generic lemmas that **live in user files**: `internM_frame` (Frame, 111 uses),
    `internM_hw` (WhnfCoreApp, 29), `internM_pw` (PromoteFlag, 22), `internM_lt`
    (IndRealNames), `hit_idx_lt`/`hitIdx_lt`/`probe_hit_lt` (3 copies), `storeR_flag`
    (PromoteFlag), `storeR_frame` (Frame), `storeR_init` (ArenaRel), `storeR_node` (View),
    `storeR_cnt` (IndApplyRefine), `storeR_resetMem` (ScratchRefine), `cnt_tier` (LpColRel).
    Each of them unfolds `internM` (`split at hI` over its arms) or destructures `StoreR`
    positionally (`obtain ⟨-, -, hT0, hT1, -⟩ := hR`, `hT.2.2.2.1.2.1`): slotgrow's fifth
    conjunct and its `pushM`/`growIf` changed all of them.
  * `ExprMk`'s `XinternW_grow` (3 copies) restate the push's memory effect
    (`growIf ASLOT 4 ahash m (apushMem m t f a j (acnt m t)) … = some m₁`) to show that the
    derived column `der_b` reads are unchanged; `LpColRel.internMD` writes a column then grows.
  * `CapCheck`/`RomProgInit`/`arenaR_init` know the slot arrays' minimum size (17 words).

### Can the L code be runtime-generic?

No: L array accesses name their array statically (`Expr.ld64 a i`, `a : ArrId`), so a function
cannot take "its table" as an argument. As in `MemoLib`, the generic L code is a **template**: a
Lean function from a schema to a `FunDecl` (`consFindG C : FunDecl`), each table's functions are
instances (`appFind := consFindG appCS`), the names and the program entries stay, and the specs
are proved once for a variable schema. The only performance question is what the template emits
where the tables differ today, mainly the match in the probe loop: inline word compares (app, lam,
forall, const, fvar, max, imax, nnum, let, proj, bvar, sort, succ, param) or a call of a match
function (lit, ls, nstr). Measured below.

## Measurement: inline match vs a call per probe step

`_tmp/conslib/callmatch.py` rewrites master's program file (964bb7e3): every `X_find` with an
inline match (8 tables: app, lam, forall, const, fvar, max, imax, nnum) calls `X_cm(t, i, keys)`
instead, i.e. what a template with "the match is a function" would emit.
`bench.py --set default --reps 3 --no-ref` (cpus 90-91, load ~45), geometric means vs master:

| | instructions | wall |
|---|---:|---:|
| master (inline match) | 1.000 | 1.000 |
| call per probe step | 1.012 | 1.005 |
| con-ron | 0.655 | 0.855 |

c03d +1.8% instructions, beta-ladder +1.0%, c04a +1.5%; wall within noise. Small, but it buys
nothing: an inline match is as easy to prove generically (below). So the template keeps the
match inline (an instance-supplied condition, with an optional prelude block for the slice
tables that call `X_match`), and emits today's code for every find.

## Design

### Layers

1. **`ConsLib.lean` (L code, templates).** `ConsSch`, one per table: the `Schema` (record array,
   slot array, width, `CTL` count index, tag), the number of key words `nk`, and the table's own
   pieces as L fragments: the match (`mpre : Stmt`, `mc : Cond`), the record words the push
   writes (`rec : List Expr`), the push's derived-column prelude / writes / room conditions
   (`pre`, `post`, `room`; `CLP`, `FVLP`, `SOLP`, `SHP`, `MHP`, `LSHP` today), the key hash of
   `intern_X` (`ihash`: inline FNV-1a or `call lit_hash`), the growth hash (`ghash`, the existing
   `GrowSch.hash`), the scratch skip (`skip : Option Expr`). Templates `consFindG C`,
   `consPushG C`, `consInternG C : FunDecl` (find, push with the growth spliced, intern). Each
   table's functions keep their names and program entries: `appFind := consFindG appCS`, so no
   `p.lookup "app_find" = some appFind` hypothesis and no program list changes.
   Variables: the template's own variables come after the table's key words (`lv nk`); an
   instance's fragments are written with the template's numbering for its `nk` (concrete).
2. **`ConsLibSpec.lean` (specs, once).** Per fragment one **obligation** (as `HashOK` today):
   `MatchOK p C mt` (the prelude writes only `m`, then `mc` is `mt mem keys t i`), `HashOK`
   (`ihash`/`ghash` compute `qh`/`hs`), `ColOK` (`pre`/`post` write only the table's derived
   arrays, as `ex`), `RoomOK`. Given them, `consFindG_spec`, `consPushG_spec`,
   `consInternG_spec` are proved once for a variable schema. The intern spec's post is
   `consInternM C s₀.mem keys = some (r, s'.mem)`: **one** generic model (the probe model
   `cprobeW`, the push memory, the growth).
3. **`ConsLibRel.lean` (the abstract relation and the user API, once).** `ConsR C m on tbP tbS`
   (today's `StoreR`: each tier represents the arena's `Tbl`, i.e. the twin's `HashMap2`: same
   nodes in order, same key → handle map; slots index the nodes; growth state) and the lemmas
   users need, stated over `consInternM`/`ConsR` only:
   * refinement: `consIntern_correct` (today's `intern_correctG`, its probe/room/match/new-record
     premises discharged inside the library from the instance obligations);
   * footprint: `consInternM_frame` (`MemFrame [ra, sa, derived arrays] [ca, ca + 1]`),
     `consR_frame` (a write outside the footprint keeps `ConsR`), `consR_flag`, `consR_reset`,
     `consR_init`, `consR_mono`;
   * result facts: handle `< 2^32` (`internM_lt`/`internM_hw`), `PW` (`internM_pw`), the node
     count (`storeR_cnt`, `cnt_tier`), node lookup (`storeR_node`, `tierR_cons_hit`), and for a
     miss: the result is node `cnt m t` of tier `t`, the count goes up by one, the derived
     columns are written as `ex` (what `ExprMk.ainternW_grow` and `LpColRel.internMD` need,
     without `growIf`/`pushMem`);
   * `ConsR`, `consInternM` and the probe model are `@[irreducible]` outside the library, so a
     user cannot unfold them (the lemmas above are the whole interface).
4. **Per table (`XStore.lean`, `XRefine.lean`).** Only data and small proofs: the arrays, the
   `ConsSch` value, the fragments' obligations (vcgen on a few lines each), the record relation
   `R` and hash `hs`, the arena lens, `MatchOK`/`NewOK` of the key decoding. Compatibility names
   as one-line definitions/corollaries: `ainternW m f a := consInternM appCS m [f, a]`,
   `AppR := ConsR appCS …`, `internApp_spec`, `internApp_refines`, `aintern_correct`,
   `ainternW_eq` (as long as a user still needs it; removed in step 3).

### What a change of the table's internals touches afterwards

K (key, or a fingerprint, in the slot), S (per-tier slot regions), a cheaper growth: the slot
layout lives in the probe model, `consFindG`/`consPushG`, the growth and `ConsR`'s slot
invariant, all in the library; the instances do not mention slots (the fragments see the node
index `v - 1` only). Two exceptions, both small and known: (a) an exact key packed into the slot
(compopt2's `f | a << 32`, no record read on a hit) needs a per-table `packed : Option Expr`
fragment (one line in app, lam, forall); a hash fingerprint needs nothing; (b) the slot arrays'
minimum size (`CapCheck`, `arenaR_init`: 17 words) becomes a library constant `consMinWords` that
`CapCheck` reads.

### Feasibility check (spike, not landed)

`ConAgua/Arena/ConsSpike.lean` (branch only): the generic probe loop of `consFindG` for a
variable key count and an opaque instance match (prelude + condition, obligation `MatchOK`), and
its spec against `cprobeW`, proved once by `vcgen [step, evalE_spec, evalC_spec, …, hM, ih]`,
a normalising `simp` and `grind` (2 s, 1.8 GB). Symbolic variable indices (`3 + C.nk`) need only
`Nat.add_right_cancel_iff`, `keysOf_setLoc` and a `Keep1` frame predicate with a grind pattern.

### Plan

* **Pilot (step 2):** `ConsLib*.lean`; `app` on it (`AppStore`/`AppRefine` shrink to the
  instance); every statement other files use stays (`internApp_spec`, `ainternW`, `ainternW_eq`,
  `aintern_correct`, `internApp_refines`, `appSch`, `ARecRel`, `AppR`, `ahash`, `appProg`,
  `apushMem`/`acnt`/`apushOK` as long as ExprMk needs them). Check: the program file differs from
  master's only where the template's push normalises a shape (none for `app`).
* **Step 3:** the other 18 tables in batches of 4–6 (helpers, disjoint files); then the users,
  file by file, onto the lemma set above (the generic lemmas now in Frame, PromoteFlag,
  WhnfCoreApp, IndRealNames, View, ArenaRel, ScratchRefine, LpColRel, IndApplyRefine move into
  `ConsLibRel`); then `@[irreducible]`.
* **Step 4:** K and S inside the library, with compopt2's final numbers.
