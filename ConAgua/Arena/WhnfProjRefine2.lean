module

public import ConAgua.Arena.WhnfProjRefine
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.RecLayout.TblDec
import ConAgua.Arena.WhnfDelta
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.WhnfCore
import all ConAgua.Arena.Env
import all ConAgua.Arena.WhnfProj

@[expose] public section

/-!
# `find_proj` refines `IFEnv.findProj?` under `CoreS` (lane `whnf3`, helper `whnf3-proj`)

`find_proj` reads the table component (`find_table`) and the record's `numFields`; it writes
nothing, so its refinement is `CoreSpec.of_pure` over a word-level triple (`findProj_word`), and
`ProjFound` follows from the same triple.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem run_of_callW {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m : Mem} {r : List Word}
    {m' : Mem} (h : callW p n f vs m = some (r, m')) : run p n f vs m = .ok (r, m') := by
  simp only [callW] at h
  simp only [run]
  split at h
  · rename_i q hq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [hq]; simp [Except.map, h.1, h.2]
  · cases h

/-! ## `find_proj` -/

theorem decTbl_numFields {R : Nat → Option Word} {q : Nat} {tbl : IProjTable} (h : decTbl R q = some tbl) :
    ∃ w, R (q + ProjTbl.numFields.toNat) = some w ∧ tbl.numFields = w.toNat := by
  obtain ⟨-, -, -, -, h7, -⟩ := decTbl_eq_some.mp h
  simp only [nat?, Option.map_eq_some_iff] at h7
  obtain ⟨w, hw, e⟩ := h7
  exact ⟨w, hw, e.symm⟩

/-- The model of `find_proj` past `find_table`'s run: `(flag, record, memory)`. -/
def findProjK (T i : Word) (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  if 4294967295 < T then none else
  match res with
  | none => none
  | some (r, m₁) =>
    if r.headD 0 = 0 then some (0, 0, m₁)
    else if i < erRd m₁ (r.headD 0 - 1 + ProjTbl.numFields) then some (1, r.headD 0 - 1, m₁)
    else some (0, 0, m₁)

theorem findProj_spec (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St) (vis T i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "find_proj" [vis, T, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      findProjK T i (callW p n "find_table" [vis, T] s₀.mem) = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.findProj]
  simp only [callFn, findProjL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      evalE_tld, tld, ld64_rdT_spec, callW_spec p n "find_table"] <;>
    finish [findProjK, erRd]

/-- **`find_proj` as words**: memory unchanged; the twin's lookup is the decoded answer; when the
flag is set, the record decodes to a table the environment holds at that structure. -/
theorem findProj_word (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St)
    {fe : IFEnv} (vis T i : Word) (hE : EnvR s₀.mem vis fe)
    (_hsz : (s₀.mem.arr64 EREC).size < 2 ^ 63) {r : List Word} {s' : St}
    (hW : findProjK T i (callW p n "find_table" [vis, T] s₀.mem) = some (r.headD 0, r.tail.headD 0, s'.mem)) :
    s'.mem = s₀.mem ∧ r.headD 0 ≤ 1 ∧
      fe.findProj? (decI T) i.toNat = decEntry (erecP s₀.mem) (r.headD 0) (r.tail.headD 0) i.toNat ∧
      (r.headD 0 ≠ 0 → ∃ tbl, decTbl (erecP s₀.mem) (r.tail.headD 0).toNat = some tbl ∧
        fe.findTable? (decI T) = some tbl) := by
  unfold findProjK at hW
  by_cases hT : 4294967295 < T
  · rw [ite_eq_left hT] at hW; cases hW
  rw [ite_eq_right hT] at hW
  have hw : T.toNat < 2 ^ 32 := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hT); simp at this; omega
  cases hc : callW p n "find_table" [vis, T] s₀.mem with
  | none => rw [hc] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hft, hfs⟩ := triple_of_callW
    (findTable_refines (p := p) ⟨hp.envRowGet, hp.baseRowGet, hp.envFind, hp.tblOwnGet, hp.tblBaseGet,
      hp.rawTable, hp.findTable⟩ n s₀ vis T hE hw) hc
  rw [ht₁] at hm₁; subst hm₁
  simp only at hW
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨e0, -, em⟩ := hW
    refine ⟨em.symm, by rw [← e0]; decide, ?_, fun h => absurd e0.symm h⟩
    rw [IFEnv.findProj?, hft, tblFound, ite_eq_left h0, ← e0]; simp [decEntry]
  rw [ite_eq_right h0] at hW
  have h1 : (r₁.headD 0 - 1).toNat = (r₁.headD 0).toNat - 1 := by
    have : (r₁.headD 0).toNat ≠ 0 := fun h' => h0 (UInt64.toNat_inj.mp (by simpa using h'))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega))]; simp
  obtain ⟨tbl, htbl⟩ := hfs h0
  have hfT : fe.findTable? (decI T) = some tbl := by rw [hft, tblFound, ite_eq_right h0, htbl]
  rw [← h1] at htbl
  obtain ⟨w, hw7, hnf⟩ := decTbl_numFields htbl
  have hrd : erRd s₀.mem (r₁.headD 0 - 1 + ProjTbl.numFields) = w := (erRdOK s₀.mem).at _ rfl hw7
  rw [hrd] at hW
  by_cases bi : i < w
  · rw [ite_eq_left bi] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨e0, e1, em⟩ := hW
    refine ⟨em.symm, by rw [← e0]; decide, ?_, fun _ => ⟨tbl, by rw [← e1]; exact htbl, hfT⟩⟩
    simp only [IFEnv.findProj?, hfT, hnf]
    rw [ite_eq_left (UInt64.lt_iff_toNat_lt.mp bi), ← e0, ← e1]
    simp only [decEntry, show ((1 : Word) = 0) = False by decide, ite_false, htbl, Option.map_some]
  · rw [ite_eq_right bi] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨e0, -, em⟩ := hW
    refine ⟨em.symm, by rw [← e0]; decide, ?_, fun h => absurd e0.symm h⟩
    simp only [IFEnv.findProj?, hfT, hnf]
    rw [ite_eq_right (mt UInt64.lt_iff_toNat_lt.mpr bi), ← e0]; simp [decEntry]

/-- **`find_proj` refines `IFEnv.findProj?`** under `CoreS`. -/
@[refines ConRon.Arena.IFEnv.findProj?]
theorem findProj_refines (p : Prog) (hp : ProjProg p) : FindProjOK p := by
  intro n s₀ a₀ dn vis fe M eb T i hS hT
  cases n with
  | zero => exact L.Arena.CoreSpec.zero hp.findProj _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  refine CoreSpec.of_pure p (n + 1) "find_proj" [vis, T, i] _ _ s₀ a₀ dn vis fe M eb _ hS
    (by unfold AM.ok; exact trivial) rfl ?_
  refine triple_post (findProj_spec p hp n s₀ vis T i) fun r s' ⟨hloc, hW⟩ => ?_
  obtain ⟨hm, h1, hres, -⟩ := findProj_word p hp n s₀ vis T i hS.env hS.erec hW
  refine ⟨hloc, hm, hres, ?_⟩
  unfold ResH HW
  have := UInt64.le_iff_toNat_le.mp h1
  have e : (1 : Word).toNat = 1 := rfl
  omega

/-- **`find_proj` answers a record that decodes, a table the environment holds** (`ProjFound`). -/
theorem projFound (p : Prog) (hp : ProjProg p) : ProjFound p := by
  intro n m a₀ dn vis fe M eb T i r m' hS hc hr
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (findProj_spec p hp n _ vis T i) hc
  obtain ⟨-, -, -, hf⟩ := findProj_word p hp n ⟨m, Locals.init []⟩ vis T i hS.env hS.erec hW
  obtain ⟨tbl, htbl, hft⟩ := hf hr
  exact ⟨tbl, htbl, decI T, hft⟩

end L.Arena
