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

## Step 2: the pilot (`app`), 2026-10-23

Approved by the coordinator: templates with the match inline, `ConsSch` per table, specs once,
`ConsLibRel` as the user API, the leaked generic lemmas moved into the library.

* `ConsLib.lean` (module): `mapE/mapC/mapS`, `lvF` (template variable → function variable),
  `seqs`/`seqO` (right-nested blocks, as `lfn` writes them), `condOf`/`rhsOf` (an instance writes
  a fragment's condition / expression with `lblk`), `ConsSch` (arrays, words, names, fragments,
  and the models the obligations are stated against: `mtM qhM hsM vsM roomM skM`), the templates
  `consFindG`, `consPushG` (record words by `cpWr`, tail `cpRest`, growth `growBlkG` at
  `np + 4`), `consInternG` (with or without the scratch skip).
* `ConsLibSpec.lean` (module): the obligations (`CMatchOK`, `HashOK` of the growth, `IHashOK`,
  `CRecOK`, `RoomOK`, `SkipOK`, bundled as `ConsOK`), the probe model `cprobeW`, the push model
  (`cntC`, `pushOKC`, `wrRecK`, `tailM`, `pushMC`, `growK`), **the intern model `consInternM`**,
  and the specs `consFindG_spec(V)`, `consPushG_spec(V)`, `consInternG_spec` (the `V` forms take
  any argument list, so `vcgen` can use them where the arguments are a computed list; the others
  are corollaries at `t :: (ks ++ [h])`), `consInternM_cases` (hit, or append node `cntC` with
  its growth: the generic form of `ExprMk.ainternW_grow`). Sorry-free, 13 s, 1.3 GB.
  Symbolic variable indices need: indices written `k + C.nk` (never `C.nk + k`), `argsOf_setLoc*`,
  `Keep1`, `zero_ne_add`/`self_ne_add`; and closed lemma terms in `simp only [...] at *` (a local
  `have` in the list is itself rewritten to `True`). `omega` does not see facts stated on `Var`
  (`abbrev Var := Nat`): annotate `(a : Nat)`.
* `app` on it: `appCS`, `appFind := consFindG appCS`, …, obligations `appOK` (five one-line
  proofs and the existing `appHash_ok`); `appFind_spec`, `appPush_spec`, `internApp_spec` keep
  their statements as corollaries; `aprobeW` is `cprobeW` at the `app` match, `ainternW` is
  `consInternM appCS m [f, a]`; `AppRefine.ainternW_eq` keeps its statement. ExprMk's
  `ainternW_grow` keeps its statement, proved from `consInternM_cases`.
* Byte identity: `repr (consFindG appCS) = repr appFind` (and push, intern) against master's
  definitions (`#eval`, before replacing them); program-file diff below.

### compopt2's final slot scheme (for step 4, relayed by the coordinator)

KSTP (`scripts/compopt2/slotk2.py --sep --pertier --pingpong`, branch compopt2): per tier its
own half of the slot array, its own `n_t` and region base `b_t ∈ {0, Q}` (last two words of the
half), slot = (value, key `f | a << 32`), find reads only slots, growth of the pushing tier only,
into the other region (zeroed streaming), walking the old region's slots in order. Measured vs
master: c03d 0.874/0.912 (cycles/wall), beta-ladder 0.863/0.889, c04a 0.857/0.857, Init
0.895/0.894, RSS ×1.20–1.27. Implemented inside the library once the 19 tables are migrated.

## Step 3a: all 19 tables on the library (2026-10-23)

Library additions (only `ConsLib*.lean` changed for them; app adapted mechanically):
* **Derived columns**: `xloc`, `pre` (prelude computing `x` at `4 + np`), `col` (the push writes
  `col[2 c + t] := x` after the count), `colM`; obligation `PreOK`; model `pushMX = colW ∘
  pushMC` (`internMD`'s shape).
* **Key preconditions**: `keyOK` (e.g. the pool slice in bounds), assumed by the match prelude
  and the key hash (`IHashOK` and `CMatchOK` are stated for `exec p n` with it); specs take
  `hk : keyOK m ks`. `triple_pre_and` turns a fragment spec with hypotheses into one with a
  precondition.
* **The match sees the hash**: the find's `mtM` gets `ks ++ [h]` (slice tables compare the
  stored hash).
* `ConsLib` no longer imports `Store.lean` (it imports `SlotGrowSpec`, `Pool`), so `Store.lean`
  (lit) can use it.

Tables: app (pilot); lam, forall, let, proj (helper a); bvar, param, zero, nanon, nnum
(helper b); const, fvar, sort, succ, max, imax (helper c, columns); lit and lit-str (two schemas
on one table), ls (column with a loop prelude), nstr (this lane). Every public statement other
files use is kept; the per-table probe loops, their specs and probe-arm lemmas are gone (no
users). Changed proofs outside the table files: `ExprMk` (`ainternW_grow`, `lainternW_grow`,
`fainternW_grow` from `consInternM_cases`). Changed statements (no users outside the table
files): growth-hash lemmas of width-1 tables (offset `4 + np`), `litFind_spec`/`litPush_spec`
take the lit obligations' hypotheses.

Program text: byte-identical for app, lam, forall, let, proj, nnum (find/push/intern) and every
find except the slice tables'. Normalised, same semantics: width-1 pushes (`k := c * 2 + t`),
merged room tests (`||`), no-skip interns (an unused `sk` local), slice-table finds (`b` before
`m`), the ls prelude's nesting. `asm/checker.s` regenerated.

Elaboration: Store files 0.6–1.7 s (Sort/Level 10 s, the prelude spec), Refine 1–2.6 s; the
old per-table probe-loop proofs took up to 9 s each. `ConsLibSpec` 13 s.

Library wishes from the helpers (step 3b): a generic `consInternM = internM` bridge (the same 7
lines in every `XRefine`), a shared room-test lemma (`pushOKC` against the old `XpushOK`), the
no-skip intern without the `sk` local.
