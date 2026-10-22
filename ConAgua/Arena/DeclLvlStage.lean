import ConAgua.Arena.DeclCvg
import ConAgua.Arena.WhnfIotaRefine4

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

set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind

/-- **The twin-side invariants `CoreS` has beyond `CheckR`**, and its two size bounds. -/
structure TwinOK (m : Mem) (a : AState) : Prop where
  readL : ReadLCOK a
  readLs : ReadLsCOK a
  nwf : NStoreWF a.store.lss.ls.ns
  erec : (m.arr64 EREC).size < 2 ^ 63
  spn : (m.arr64 SPN).size < 2 ^ 63
  memos : CoreMemos m
  bstk : (m.arr64 145).size < 2 ^ 63

/-- The stage relation with the twin invariants and a filled pin table is `CoreS` (outside the
eager tower). -/
theorem StageR.coreS {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hS : StageR dn vis fe m a) (hT : TwinOK m a) (hflag : pinW m 0 ≠ 0) :
    ∃ M, CoreS dn m a vis fe M 0 := by
  obtain ⟨M, hM⟩ := hS.1.core
  exact ⟨M, ⟨hS.1.arena, hM, hS.1.pins.full hflag, hS.1.env, hT.readL, hT.readLs, hT.nwf, hT.erec,
    hT.spn, hT.memos, hT.bstk⟩⟩

/-- `CoreS` (outside the eager tower) is `CheckR` and the twin invariants. -/
theorem CoreS.checkR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {M : ModeMaps} (hS : CoreS dn m a vis fe M 0) :
    CheckR dn m a vis fe ∧ TwinOK m a :=
  ⟨⟨hS.arena, ⟨M, hS.core⟩, ⟨fun _ => hS.pins⟩, hS.env⟩,
    ⟨hS.readL, hS.readLs, hS.nwf, hS.erec, hS.spn, hS.memos, hS.bstk⟩⟩

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

theorem lvlFns_sub : ∀ f ∈ lvlFns, f ∈ cvgFns := by decide

theorem lvlA_iw : IW ∉ lvlA := by simp [lvlA]
theorem lvlA_erec : EREC ∉ lvlA := by simp [lvlA]
theorem lvlC_129 : (129 : Word) ∉ lvlC := by simp [lvlC]
theorem lvlC_200 : (200 : Word) ∉ lvlC := by simp [lvlC]

/-- **`lvl_eq_c` under the stage relation**, given the twin invariants, a filled pin table and the
two levels' denotations (sorry-free; through lane `whnf`'s `lvlEqC_refines`). -/
theorem lvlEqC_stage {p : Prog} (hC : CvgProg p) (hL : LvlCacheProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {u v : Word} {r : List Word}
    (h : callW p n "lvl_eq_c" [u, v] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hT : TwinOK m a) (hflag : pinW m 0 ≠ 0) (hu : H u) (hv : H v) (lu lv : ConLeche.Level)
    (hdu : denoteL a.store.ls (decI u) = some lu) (hdv : denoteL a.store.ls (decI v) = some lv) :
    ∃ a', (lvlEq? (decI u) (decI v)).run a = .ok (decO (r.headD 0), a') ∧
      StageR dn vis fe m' a' ∧ TwinOK m' a' ∧ IWGrow m m' ∧ HW (r.headD 0) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [lvlEqC_small p hL.c n hn] at h; cases h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨M, hCS⟩ := StageR.coreS hS hT hflag
  obtain ⟨s', hs', -, hok, ⟨M', hCS', -, -⟩, hres, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvlEqC_refines p hL k ⟨m, Locals.init []⟩ a dn vis fe M 0 hCS u v hu hv lu lv hdu hdv) h
  subst hs'
  obtain ⟨s'', hs'', hf, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_memFrame (closedW_of_agree lvlText_closed (fun f hf => hC f (lvlFns_sub f hf))) (k + 2)
      (f := "lvl_eq_c") (by decide) [u, v] ⟨m, Locals.init []⟩) h
  rw [hs''] at hf
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  obtain ⟨hCR, hT'⟩ := hCS'.checkR
  have hI : s'.mem.arr64 IW = m.arr64 IW := hf.1 _ lvlA_iw (by decide)
  have hE : s'.mem.arr64 EREC = m.arr64 EREC := hf.1 _ lvlA_erec (by decide)
  have h129 : rdW (s'.mem.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 _ lvlC_129
  have h200 : rdW (s'.mem.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 _ lvlC_200
  refine ⟨_, hrun, ⟨hCR, IWOK.frame hf lvlA_iw lvlA_erec lvlC_129 lvlC_200 hS.2⟩, hT', ?_, hw⟩
  refine ⟨by simp [iwTop, h200], by simp [erTop, h129], fun i _ => by rw [hI],
    fun i _ => by rw [hE]⟩

end L.Arena
