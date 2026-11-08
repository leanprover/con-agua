module

public import ConAgua.Arena.WhnfProjRefine
import ConAgua.Arena.CoreWalks
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

/-! ## `env_find` as a word model -/

/-! ## `find_proj` -/

theorem decTbl_numFields {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl (aread a) q = some tbl) :
    ∃ w, a[q + 7]? = some w ∧ tbl.numFields = w.toNat := by
  sorry

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
  sorry

/-- **`find_proj` as words**: memory unchanged; the twin's lookup is the decoded answer; when the
flag is set, the record decodes to a table the environment holds at that structure. -/
theorem findProj_word (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St)
    {fe : IFEnv} (vis T i : Word) (hE : EnvR s₀.mem vis fe)
    (hsz : (s₀.mem.arr64 EREC).size < 2 ^ 63) {r : List Word} {s' : St}
    (hW : findProjK T i (callW p n "find_table" [vis, T] s₀.mem) = some (r.headD 0, r.tail.headD 0, s'.mem)) :
    s'.mem = s₀.mem ∧ r.headD 0 ≤ 1 ∧
      fe.findProj? (decI T) i.toNat = decEntry (erecP s₀.mem) (r.headD 0) (r.tail.headD 0) i.toNat ∧
      (r.headD 0 ≠ 0 → ∃ tbl, decTbl (erecP s₀.mem) (r.tail.headD 0).toNat = some tbl ∧
        fe.findTable? (decI T) = some tbl) := by
  sorry

/-- **`find_proj` refines `IFEnv.findProj?`** under `CoreS`. -/
@[refines ConRon.Arena.IFEnv.findProj?]
theorem findProj_refines (p : Prog) (hp : ProjProg p) : FindProjOK p := by
  sorry

/-- **`find_proj` answers a record that decodes, a table the environment holds** (`ProjFound`). -/
theorem projFound (p : Prog) (hp : ProjProg p) : ProjFound p := by
  sorry

end L.Arena
