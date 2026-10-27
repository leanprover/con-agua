import ConAgua.Arena.DeclCvg

/-!
# `lvl_eq_c` under the stage relation, given the core's twin invariants (lane `decls3`)

Lane `whnf`'s `lvlEqC_refines` proves `lvl_eq_c(u, v)` refines `lvlEq?` under `CoreS`. The stage
relation `StageR = CheckR ∧ IWOK` has all of `CoreS` but the **twin-side invariants**
(`TwinOK`: the readback caches hold readbacks, the name store is well formed — facts about the
twin's state alone, true of every reachable state) and two size bounds, and the callers do not
know that the level handles they compare **denote** (the `CoreS.lvl_den` gap of lane `whnf`).

`lvlEqC_stage` is the bridge, sorry-free: from `StageR`, `TwinOK`, a filled pin table and the
two denotations, a run of `lvl_eq_c` is a run of `lvlEq?`, `StageR` and `TwinOK` hold after it,
and the pools are untouched (its write set from the text, `lvlText_closed`). What is left for the
stub spec `lvlEqStub_spec` (`IndStubs.lean`, the one `sorry`) is to carry `TwinOK` in the stage
relation and the denotation of the compared handles in the callees' posts (DESIGN.md, lane
`decls3`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open L.Ind

/-- **The twin-side invariants `CoreS` has beyond `CheckR`**, and its two size bounds. -/
structure TwinOK (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (fe : IFEnv) : Prop where
  readL : ReadLCOK a
  readLs : ReadLsCOK a
  nwf : NStoreWF a.store.lss.ls.ns
  erec : (m.arr64 EREC).size < 2 ^ 63
  spn : (m.arr64 SPN).size < 2 ^ 63
  memos : CoreMemos m
  bstk : (m.arr64 145).size < 2 ^ 63
  /-- Stored levels read back (`StoreDen.lean`). -/
  den : StoreDen dn m a fe

/-- The stage relation with the twin invariants and a filled pin table is `CoreS` (outside the
eager tower). -/
theorem StageR.coreS {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hS : StageR dn vis fe m a) (hT : TwinOK dn m a fe) (hflag : pinW m 0 ≠ 0) :
    ∃ M, CoreS dn m a vis fe M 0 := by
  obtain ⟨M, hM⟩ := hS.1.core
  exact ⟨M, ⟨hS.1.arena, hM, hS.1.pins.full hflag, hS.1.env, hT.readL, hT.readLs, hT.nwf, hT.erec,
    hT.spn, hT.memos, hT.bstk, hT.den, hS.1.mode⟩⟩

/-- `CoreS` (outside the eager tower) is `CheckR` and the twin invariants. -/
theorem CoreS.checkR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {M : ModeMaps} (hS : CoreS dn m a vis fe M 0) :
    CheckR dn m a vis fe ∧ TwinOK dn m a fe :=
  ⟨⟨hS.arena, ⟨M, hS.core⟩, ⟨fun _ => hS.pins⟩, hS.env, hS.mode⟩,
    ⟨hS.readL, hS.readLs, hS.nwf, hS.erec, hS.spn, hS.memos, hS.bstk, hS.den⟩⟩

/-! ## `lvl_eq_c`'s write set -/

/-- The arrays `lvl_eq_c` may write: all a step may, but the pools. -/
def lvlA : List ArrId := stepA.filter fun b => b ≠ IW ∧ b ≠ EREC

/-- The `CTL` words `lvl_eq_c` may write: all a step may, but the pools' tops. -/
def lvlC : List Word := stepC.filter fun x => x ≠ 129 ∧ x ≠ 200

/-- The functions `lvl_eq_c` reaches. -/
def lvlFns : List FnName :=
  ["lvl_eq_c", "lq_find", "lvl_eq_rec", "lvl_eq", "lv_equiv", "lv_eq", "lv_node", "lv_simp",
   "lh_mk", "lv_comb", "lv_leq", "lv_rest", "lv_imax", "lv_cases", "lv_cases_at", "lv_subsimp",
   "lv_subst", "lv_imax_l", "lv_dist1", "lv_dist2", "lv_imax_r", "lq_put"]

theorem lvlText_closed : closedA cvgProg lvlA lvlC lvlFns = true := by decide +kernel

theorem lvlA_erec : EREC ∉ lvlA := by simp [lvlA]

end L.Arena
