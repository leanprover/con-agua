import ConAgua.Arena.WhnfProjRefine
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.WhnfDelta
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

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

/-! ## `env_find` as a word model -/

/-- The model of `env_find`. -/
def efW (m : Mem) (w vis : Word) : Word × Word :=
  if rowC m w = 0 then (0, 0) else if rowC m w - 1 < vis then (1, rowP m w) else (0, 0)

theorem envFind_specWP (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) (w vis : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧ r.headD 0 = (efW s₀.mem w vis).1 ∧
      r.tail.headD 0 = (efW s₀.mem w vis).2; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, envRowGet_spec p hx hg n] <;>
      finish [efW]

/-! ## `find_proj` -/

theorem decTbl_numFields {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl a q = some tbl) :
    ∃ w, a[q + 7]? = some w ∧ tbl.numFields = w.toNat := by
  cases h7 : nat? a (q + 7) with
  | none => simp [decTbl, h7] at h
  | some k =>
    simp [decTbl, h7] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
    simp only [nat?, Option.map_eq_some_iff] at h7
    obtain ⟨w, hw, rfl⟩ := h7
    exact ⟨w, hw, rfl⟩

theorem rdW_some {a : Array Word} {x : Word} (h : rdW a x ≠ 0) : a[x.toNat]? = some (rdW a x) := by
  simp only [rdW] at h ⊢
  cases e : a[x.toNat]? with
  | none => rw [e] at h; simp at h
  | some v => rfl

/-- The twin's answer from the table lookup's answer. -/
def fpRes (o : Option IProjTable) (i : Nat) : Option IProjEntry :=
  match o with
  | some tbl => if i < tbl.numFields then some (tbl.entry i) else none
  | none => none

/-- The twin's side of `find_proj`, from the table lookup's answer `r` (`find_table`). -/
theorem findProj_of_tbl {fe : IFEnv} {m : Mem} (T : NIdx) (i : Nat) (r : Word)
    (hr : fe.findTable? T = tblOut m r) (hs : r ≠ 0 → (tblOut m r).isSome) :
    (r = 0 → fe.findProj? T i = none) ∧
    (r ≠ 0 → ∃ tbl w, decTbl (m.arr64 EREC) (r - 1).toNat = some tbl ∧ fe.findTable? T = some tbl ∧
      (m.arr64 EREC)[(r - 1).toNat + 7]? = some w ∧ tbl.numFields = w.toNat ∧
      fe.findProj? T i = if i < w.toNat then some (tbl.entry i) else none) := by
  refine ⟨fun h0 => by simp [IFEnv.findProj?, hr, h0, tblOut], fun h0 => ?_⟩
  have h1 : (r - 1).toNat = r.toNat - 1 := by
    have : r.toNat ≠ 0 := fun h' => h0 (UInt64.toNat_inj.mp (by simpa using h'))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have hr' : fe.findTable? T = decTbl (erecP m) (r.toNat - 1) := by simp [hr, tblOut, h0]
  have hs' := hs h0
  simp only [tblOut, h0, ite_false] at hs'
  obtain ⟨tbl, e⟩ := Option.isSome_iff_exists.mp hs'
  have ht := ArrExt.decTbl (erecP_ext m) e
  obtain ⟨w, hw7, hnf⟩ := decTbl_numFields ht
  refine ⟨tbl, w, by rw [h1]; exact ht, by rw [hr', e], by rw [h1]; exact hw7, hnf, ?_⟩
  simp only [IFEnv.findProj?, hr', e, hnf]

/-- The model of `find_proj` past `find_table`'s run: `(flag, record, memory)`. -/
def findProjK (T i : Word) (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  if 4294967295 < T then none else
  match res with
  | none => none
  | some (r, m₁) =>
    if r.headD 0 = 0 then some (0, 0, m₁)
    else if i < rdW (m₁.arr64 EREC) (r.headD 0 - 1 + 7) then some (1, r.headD 0 - 1, m₁)
    else some (0, 0, m₁)

theorem findProj_spec (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St) (vis T i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "find_proj" [vis, T, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      findProjK T i (callW p n "find_table" [vis, T] s₀.mem) = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.findProj]
  simp only [callFn, findProjL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "find_table"] <;>
    finish [findProjK]

/-- **`find_proj` as words**: memory unchanged; the twin's lookup is the decoded answer; when the
flag is set, the record decodes to a table the environment holds at that structure. -/
theorem findProj_word (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St)
    {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis T i : Word) (hE : EnvR dn s₀.mem vis fe)
    (hsz : (s₀.mem.arr64 EREC).size < 2 ^ 63) {r : List Word} {s' : St}
    (hW : findProjK T i (callW p n "find_table" [vis, T] s₀.mem) = some (r.headD 0, r.tail.headD 0, s'.mem)) :
    s'.mem = s₀.mem ∧ r.headD 0 ≤ 1 ∧
      fe.findProj? (decI T) i.toNat = decEntry (s₀.mem.arr64 EREC) (r.headD 0) (r.tail.headD 0) i.toNat ∧
      (r.headD 0 ≠ 0 → ∃ tbl, decTbl (s₀.mem.arr64 EREC) (r.tail.headD 0).toNat = some tbl ∧
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
    (findTable_refines p hp.envix hp.envrow hp.tblix hp.tblrow hp.findTable n s₀ vis T hE hw) hc
  rw [ht₁] at hm₁; subst hm₁
  obtain ⟨k0, k1⟩ := findProj_of_tbl (fe := fe) (m := s₀.mem) (decI T) i.toNat (r₁.headD 0) hft hfs
  simp only at hW
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨e0, -, em⟩ := hW
    refine ⟨em.symm, by rw [← e0]; decide, ?_, fun h => absurd e0.symm h⟩
    rw [k0 h0, ← e0]; simp [decEntry]
  rw [ite_eq_right h0] at hW
  obtain ⟨tbl, w, htbl, hfT, hw7, hnf, hfp⟩ := k1 h0
  have hq7 : (r₁.headD 0 - 1 + 7).toNat = (r₁.headD 0 - 1).toNat + 7 := by
    have hlt := (Array.getElem?_eq_some_iff.mp hw7).1
    rw [UInt64.toNat_add, show (7 : Word).toNat = 7 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have hrd : rdW (s₀.mem.arr64 EREC) (r₁.headD 0 - 1 + 7) = w := by
    simp only [rdW, hq7, hw7, Option.getD_some]
  rw [hrd] at hW
  by_cases bi : i < w
  · rw [ite_eq_left bi] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨e0, e1, em⟩ := hW
    refine ⟨em.symm, by rw [← e0]; decide, ?_, fun _ => ⟨tbl, by rw [← e1]; exact htbl, hfT⟩⟩
    rw [hfp, ite_eq_left (UInt64.lt_iff_toNat_lt.mp bi), ← e0, ← e1]
    simp only [decEntry, show ((1 : Word) = 0) = False by decide, ite_false, htbl, Option.map_some]
  · rw [ite_eq_right bi] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨e0, -, em⟩ := hW
    refine ⟨em.symm, by rw [← e0]; decide, ?_, fun h => absurd e0.symm h⟩
    rw [hfp, ite_eq_right (mt UInt64.lt_iff_toNat_lt.mpr bi), ← e0]; simp [decEntry]

/-- **`find_proj` refines `IFEnv.findProj?`** under `CoreS`. -/
@[refines ConRon.Arena.IFEnv.findProj?]
theorem findProj_refines (p : Prog) (hp : ProjProg p) : FindProjOK p := by
  intro n s₀ a₀ dn vis fe M eb T i hS hT
  cases n with
  | zero => exact CoreSpec.zeroW hp.findProj _ _ _ _ _ _ _ _ _ _ _
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
