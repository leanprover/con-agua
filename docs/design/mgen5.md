# Lane mgen5: family conversions of wide-reach hand models

Fifth lane on `l_model` (`ConAgua/L/ModelGen.lean`; earlier: `docs/design/mgen.md`,
`docs/design/mgen3.md`, `docs/design/mgen4.md`). mgen4 §4 listed the hand models that are
unfolded by name in many files and called each a family conversion like its batch 7 (RxMapW:
generate, bridge to the hand shape the users walk, simplify the users where cheap), with no
generator change needed. This lane does those, `rom_name`, and the two bounds cases, and samples
the specs without a model. Same constraints as every lane: no L program change, no final
statement change, no new axiom, no heartbeats raised. Rule (user, 2026-11-10): a slower module is
accepted; only > ~3× or > ~60 s per module blocks.

## 1. Inventory (master b7003b70)

mgen4's script, rerun as `_tmp/mgen5/inv.py` (outside the repository): 252 hand-specified
functions, 1 073 `l_model` commands; 185 hand specs have no model in their post. The families
the task names, with the files that mention the model (besides its own):

| model | function(s) | files | owner |
|---|---|---:|---|
| `nIdxsW` | `block_shape_n_idxs` | 4 | helper `mgen5-parts` |
| `lpsW` | `block_shape_lps` | 6 | `mgen5-parts` |
| `psGoW` | (`IndSumSpec/StructElimLevel`) | 4 | `mgen5-parts` |
| `tmdW` | `target_major_default` | 4 | helper `mgen5-rec` |
| `stripTW`, `stripF` | `strip_lams`, `strip_pis` | 1 | `mgen5-rec` |
| `bvbW` | `bvar_b` | 10 | `mgen5-rec` |
| `eftW`, `eftF`, `eeW`, `tteW` | the `erase_fvar_tys` family | 2–3 | `mgen5-rec` |
| `romNameW` | `rom_name` | 9 | helper `mgen5-rom` |
| `romNamesToW` | `rom_names_to` (`PINS` bound) | 0 | `mgen5-rom` |
| `getDW` | `sl_getd` | 4 | lead |
| `selW` | `reduce_op_cv_a`, `of_reduce_pin_a`, `reduce_decl_pin` | 0 | lead |
| `lhPushW` | `lh_push` (`CTL` size bound) | 2 | lead |

## 2. Lead conversions

### `selW`: three pin-selected ROM readers

`reduce_op_cv_a`, `of_reduce_pin_a` and `reduce_decl_pin` shared one hand model `selW p n m c k f i
j` (`pin_at(k)`, then `f(i)` or `f(j)`) and one relational lemma `selW_ok`. Each is now an
`l_model` (default recipe, callee specs `pinAt_specW`, `callW_spec`); the generated models
`rocaW`, `orpaW`, `rdpW` are `selW` at their constants by a four-line bridge each
(`rocaW_selW`: `cases` on the fuel, the pin read and the callee), so `selW_ok` and the three
refinements stay as they were. Gone: the three hand specs, `selK`'s and `selK2`'s arm lemmas and
their patterns. `DeclReduceSpec.lean` +49 −57; 10.9 → 12.1 G instructions, 2.2 → 2.3 s, 1051 →
1055 MB.

### `getDW` (`sl_getd`): kept

`getDW m o l i d` is a total word (`if l ≤ i then d else IW.u64[o + i]`), the pure post `r.headD 0
= getDW …` of `slGetD_specW`, and five `l_model`s take that spec as a callee, so the word is
inlined in their generated models. A generated `ro` model is `Option Word`: the five callers'
models would get a continuation per call instead of the word, and the four files that reason
about `getDW` (`getDW_handle'`, `getDW_nat`, `getDW_head`, `MapOKStep`) would need a bridge back
to the word. The hand spec is ten lines; nothing to gain. mgen4 §4 already counts it among the
total word models kept as vocabulary.

### `lh_push`: kept (the `CTL` size bound)

`lhPushW` returns `none` when `(m.arr64 CTL).size ≤ 192`. L has no such test (the store
`CTL.u64[192] := o + 1` aborts out of bounds); a generated model treats an out-of-bounds store as
no change, so it drops the case. Its user `lhPushW_ext` needs it: the heap top advances by one
(`(htop m').toNat = (htop m).toNat + 1`) only if `CTL[192]` is in bounds. Neither generator
option covers it:
* `guards` reads guards off a *callee's* post; `lh_push` has no callee;
* `pre [192 < (s₀.mem.arr64 CTL).size]` makes the fact a hypothesis of the spec, which
  `lh_push`'s callers must then discharge: `lv_zero`'s hand spec and `lp_substl`'s (they pass
  `lhPush_spec` to `vcgen`), and through `zeroW_ok` the refinements that call `lv_zero`
  (`FormerNZRef`, `ProjGuardRef` three times, `PropReadRefine`, `LevelSubstL`), whose states
  (`CoreS`, `LvR`) carry no `CTL` size (`IWOK.ctl : 200 < (m.arr64 CTL).size` lives in the
  inductive stage relation, not in `CoreS`).
Threading a `CTL`-size hypothesis through `zeroW_ok` and its six callers to save a ten-line spec
is no win. The same holds for `lh_mk` (`lhMkW`, the same guard). This is a case for a generator
option that models a store's bound as a guard (`none` out of bounds), not for a lane.

## 3. The 185 specs without a model in their post

Classified by their posts (script over `_tmp/mgen5/inv.json`), and 22 read by hand (random
sample, seed 5: `scan_opaque`, `nat_mod_lit`, `class_gen_major`, `class_key_of`, `utf8_char`,
`key_at_g2`, `caps_eq_a`, `str_code`, `nat_add`, `class_rules_ok`, `ci_eq_rest`,
`check_block_idx_sorts`, `nest_accept_group`, `class_minor_slot_go`, `hints_val`,
`class_recs_rules_ok`, `stk_push`, `key_at_g6`, `block_shape_major_idx_at`, `match_lit`,
`scan_binder_info`, `install_basis_decls`):

| kind | count | example | could a generated spec replace the hand proof? |
|---|---:|---|---|
| refinement triples (`AM.ok …`, `@[refines]`) | 61 | `install_basis_decls`, `check_block_idx_sorts` | no: these are the refinement layer itself, 6–7-line proofs that chain the callees' refinements through `vcgen`; a generated model would be a new intermediate plus a simulation lemma, more text than now |
| a value over the input bytes (`r = [fN b i]`) | 48 | `scan_opaque`, `key_at_g2`, `match_lit` | no: `fN` is the twin-shaped spec over `List UInt8` (`refines_part`), not a word model; a generated `ro` model needs a bridge `fW m i = some (fN (m.arr8 IN) i)` whose proof is the hand proof (8–20 lines) |
| a total memory effect (`G ∧ s'.mem = F`) | 32 | `stk_push`, `nat_mul`, `tbl_own_set` | no: callers' `l_model`s read this shape as a total callee (inlined, `G` a guard); a generated `Option` model would put a continuation into every caller's model |
| other value/relation posts | 33 | `nat_add` (`PFrame`, `Agree`, `pv … = pv … + pv …`), `nat_trim`, `skip_digits` | no: the post is the relation the callers need, over `Nat` values of limb slices |
| a Boolean predicate (`r.headD 0 = if PB … then 1 else 0`) | 10 | `caps_eq_a`, `ci_eq_rest` | no: as for the byte values (the predicate is the spec; 9-line proofs) |
| a model under `∃` | 1 | `class_minor_slot_go` (`∃ x y z w, classMinorSlotGoW … = some (x, y, z, w)`) | its model checks `(m.arr64 IW).size` (two out-of-bounds arms that its users take): a bounds case |

Yield: none of the 22 sampled, and by the classification at most the one `∃` case of the 185,
which is a bounds case. These hand proofs are short (median about 10 lines) and their posts are
the vocabulary the callers' generated models and the refinements use; a generated spec would add
a bridge per function at least as long as the proof it replaces. Not converted.
