import ConAgua.Arena.InstLPWalkRef3
import ConAgua.Arena.InstLPKeys

/-!
# `inst_lp` refines `instLPFast coreWalkFuel` under `CoreS` (`InstLPOK`)

`inst_lp_core(ko, kc, us, e)`: the cut-off on `e`'s level-parameter bit (`der_b`, `derLW_ok`),
else the values' slice (`ls_node(us)`: a stored list, which reads back by `StoreDen.lsAll`), the
keys checked to be stored names (`keys_ok`: they read back, `keysOkW_names`), the three memo
clears (`ilw_clears`: the twin's `instLPClear`), the walk at `coreWalkFuel` (`ilwGo_ok`), the clears
again. `inst_lp(po, pl, us, e)`: the keys copied from the record pool onto the spine stack
(`keys_push`), the core, the stack top put back.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The walk's program and its entries'. -/
structure ILWEntryProg (p : Prog) : Prop where
  all : ILWAllProg p
  keys : p.lookup "keys_ok" = some keysOk

theorem ilw_coreRef {T : AM EIdx} {a a' : AState} {v : EIdx} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
    (hrun : T.run a = .ok (v, a')) (hA : CoreAfter dn m m' a' vis fe M eb) (hv : v = decH r)
    (hr : ResH r) : CoreRef T a decH dn m vis fe M eb r m' := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hok, hst ▸ hA, hres.trans hv, hr⟩

/-- One walk-memo clear through `callW`: the stamp check and the cleared memory. -/
theorem ilw_clearCall {p : Prog} {k : Nat} {f : FnName} (S : MemoSch) (hf : p.lookup f = some (memoClearG S))
    {m m' : Mem} {r : List Word} (h : callW p k f [] m = some (r, m')) :
    rdW (m.arr64 CTL) S.cs + 2 ≠ 0 ∧ m' = mclearG S m := by
  obtain ⟨s', hs', -, hw, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (memoClearG_spec S p f hf k _) h
  exact ⟨hw, hs'.symm.trans hm⟩

/-- **The three clears before (or after) the walk** keep `CoreS`: the memo stamps only. -/
theorem ilw_clears_core {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hLP : LPMemos (mclearG lplsSch (mclearG lplSch (mclearG lpSch m)))) :
    CoreS dn (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) a vis fe M eb ∧
      StackKept m (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) := by
  have f1 := mclearG_frame lpSch m
  have f2 := mclearG_frame lplSch (mclearG lpSch m)
  have f3 := mclearG_frame lplsSch (mclearG lplSch (mclearG lpSch m))
  have hf : MemFrame [] [lpSch.cs, lpSch.cs + 1, lplSch.cs, lplSch.cs + 1, lplsSch.cs, lplsSch.cs + 1] m
      (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) :=
    ((f1.mono (by simp) (by simp)).trans (f2.mono (by simp) (by simp))).trans (f3.mono (by simp) (by simp))
  have hD : ArenaD (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) a :=
    ⟨hS.arena.1.frame (by simp) (by simp [arenaCtl, storeCtl, memoCtl, lpSch, lplSch, lplsSch]) hf,
      DerR.frameM _ _ _ _ hf (by simp) a hS.arena.2⟩
  exact hS.of_walk hD rfl hf (by simp) (by simp [lpSch, lplSch, lplsSch])
    (hS.memos.frameLP hf hLP (by simp) (by simp [lpSch, lplSch, lplsSch])) (by simp)
    (by simp [lpSch, lplSch, lplsSch]) (by simp) (by simp [lpSch, lplSch, lplsSch])

end L.Arena
