import ConAgua.Arena.WhnfProjRefine

/-!
# `find_proj` refines `IFEnv.findProj?` under `CoreS` (lane `whnf3`, helper `whnf3-proj`)

* **The write set** (`projProgC_closed`, from the text): `proj_table_name`, `find_proj` and their
  callees write the pool and its top, and the name tables `str`/`num` with their counts, nothing
  else: `ErecKept`'s `find_proj` half and the `EREC` reads after the name interning.
* **`env_find` as a word model** (`efW`, `envFind_specW`): its answer from the rows, so that a found
  row is known to decode (`EnvR.row_dec`: `EnvR`'s keys and values).
* **`find_proj`** (`fpW`, `findProj_refines`, `projFound`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The write set -/

/-- The projection lookup's functions, as a concrete program for the text check. -/
def projProgC : Prog :=
  [("lit_hash", litHash), ("limbs_eq", limbsEq), ("nstr_match", nsMatch), ("nstr_find", nsFind),
   ("nstr_push", nsPush), ("intern_nstr", internNStr), ("nnum_find", nnumFind),
   ("nnum_push", nnumPush), ("intern_nnum", internNNum), ("env_ix", envIxL),
   ("env_row_get", envRowGetL), ("env_find", envFindL), ("proj_table_name", projTableNameL),
   ("find_proj", findProjL)]

def projFns : List FnName := projProgC.map (·.1)

/-- The pool (0), the `str` (35, 36) and `num` (37, 38) name tables. -/
def projA : List ArrId := [0, 35, 36, 37, 38]
/-- The pool top (0) and the two tables' counts (36‥39). -/
def projC : List Word := [0, 36, 37, 38, 39]

theorem projProgC_closed : closedA projProgC projA projC projFns = true := by decide +kernel

theorem ProjProg.closed {p : Prog} (hp : ProjProg p) : closedA p projA projC projFns = true :=
  closedW_of_agree projProgC_closed (by
    simp only [projFns, projProgC, List.map_cons, List.map_nil, List.forall_mem_cons,
      List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨hp.litHash.trans rfl, hp.limbsEq.trans rfl, hp.nsMatch.trans rfl, hp.nsFind.trans rfl,
      hp.nsPush.trans rfl, hp.nstr.trans rfl, hp.nnFind.trans rfl, hp.nnPush.trans rfl,
      hp.nnum.trans rfl, hp.envix.trans rfl, hp.envrow.trans rfl, hp.envfind.trans rfl,
      hp.ptn.trans rfl, hp.findProj.trans rfl⟩)

theorem run_of_callW {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m : Mem} {r : List Word}
    {m' : Mem} (h : callW p n f vs m = some (r, m')) : run p n f vs m = .ok (r, m') := by
  simp only [callW] at h
  simp only [run]
  split at h
  · rename_i q hq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [hq]; simp [Except.map, h.1, h.2]
  · cases h

/-- **A run of `find_proj` or `proj_table_name` changes only the pool and the name tables.** -/
theorem proj_frame {p : Prog} (hp : ProjProg p) {f : FnName} (hf : f ∈ projFns) {n : Nat}
    {vs : List Word} {m : Mem} {r : List Word} {m' : Mem} (h : callW p n f vs m = some (r, m')) :
    MemFrame projA projC m m' :=
  (run_memFrame hp.closed hf (run_of_callW h)).1

theorem proj_frame_erec {p : Prog} (hp : ProjProg p) {f : FnName} (hf : f ∈ projFns) {n : Nat}
    {vs : List Word} {m : Mem} {r : List Word} {m' : Mem} (h : callW p n f vs m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC ∧ rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 :=
  ⟨(proj_frame hp hf h).1 EREC (by simp [projA, EREC]) (by decide),
    (proj_frame hp hf h).2.1 129 (by simp [projC])⟩

/-! ## `env_find` as a word model -/

/-- The model of `env_find`. -/
def efW (m : Mem) (w vis : Word) : Word × Word :=
  if rowC m w = 0 then (0, 0) else if rowC m w - 1 < vis then (1, rowP m w) else (0, 0)

theorem envFind_specW (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
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

/-- **A row that exists decodes** (`EnvR`'s keys and values). -/
theorem EnvR.row_dec {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
    (h0 : rowC m w ≠ 0) : ∃ ci, decCI (erecP m) dn (rowP m w).toNat = some ci := by
  have hk := h.keys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.vals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  have hv := hv h0
  simp only [rowW, h0, ite_false, Option.map_some] at hk
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => rw [e] at hk; cases hk
  | some r =>
    rw [e] at hv
    exact ⟨r.2, by simpa using hv.symm⟩

/-! ## `find_proj` -/

/-- The model of `find_proj`: `(flag, record, memory)`. -/
def fpW (p : Prog) (n : Nat) (m : Mem) (vis t i : Word) : Option (Word × Word × Mem) :=
  match callW p n "proj_table_name" [t] m with
  | none => none
  | some (r₁, m₁) =>
    if 4294967296 ≤ r₁.headD 0 then none
    else match callW p n "env_find" [r₁.headD 0, vis] m₁ with
      | none => none
      | some (r₂, m₂) =>
        if r₂.headD 0 = 0 then some (0, 0, m₂)
        else if rdW (m₂.arr64 EREC) (r₂.tail.headD 0) ≠ 6 then some (0, 0, m₂)
        else if i < rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 7) then some (1, r₂.tail.headD 0, m₂)
        else some (0, 0, m₂)

theorem findProj_spec (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St) (vis t i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "find_proj" [vis, t, i]
    ⦃fun r s' => LocEq s' s₀ ∧ fpW p n s₀.mem vis t i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.findProj]
  simp only [callFn, findProjL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "proj_table_name", callW_spec p n "env_find"] <;>
    finish [fpW]

/-- The twin's answer from the lookup's result. -/
def fpRes (o : Option IConstantInfo) (i : Nat) : Option IProjEntry :=
  match o with
  | some (.projInfo tbl) => if i < tbl.numFields then some (tbl.entry i) else none
  | _ => none

theorem findProj_run (fe : IFEnv) (T : NIdx) (i : Nat) (a a' : AState) (nm : NIdx)
    (h : (projTableName T).run a = .ok (nm, a')) :
    (fe.findProj? T i).run a = .ok (fpRes (fe.find? nm) i, a') := by
  simp only [IFEnv.findProj?, StateT.run_bind, h]
  cases e : fe.find? nm with
  | none => simp [e, fpRes, bind, Except.bind, pure, StateT.pure, Except.pure] <;> rfl
  | some ci => cases ci <;> simp [e, fpRes, bind, Except.bind, pure, StateT.pure, Except.pure] <;> rfl

/-! ## Decoding a projection table record -/

theorem decTbl_numFields {a : Array Word} {q : Nat} {tbl : IProjTable} (h : decTbl a q = some tbl) :
    ∃ w, a[q + 7]? = some w ∧ tbl.numFields = w.toNat := by
  cases h7 : nat? a (q + 7) with
  | none => simp [decTbl, h7] at h
  | some k =>
    simp [decTbl, h7] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
    simp only [nat?, Option.map_eq_some_iff] at h7
    obtain ⟨w, hw, rfl⟩ := h7
    exact ⟨w, hw, rfl⟩

theorem decCI_six {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {ci : IConstantInfo}
    (h : decCI a dn q = some ci) (h6 : a[q]? = some 6) :
    ∃ tbl, ci = .projInfo tbl ∧ decTbl a q = some tbl := by
  have e6 : (6 : Word).toNat = 6 := rfl
  simp [decCI, nat?, h6, e6] at h
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨tbl, ht, rfl⟩ := h
  exact ⟨tbl, rfl, ht⟩

theorem decCI_proj {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {tbl : IProjTable}
    (h : decCI a dn q = some (.projInfo tbl)) : a[q]? = some 6 := by
  cases hq : a[q]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
    simp [decCI, nat?, hq] at h
    split at h <;> simp_all [Option.bind_eq_some_iff]
    rename_i h6
    exact UInt64.toNat_inj.mp (by rw [h6]; rfl)

end L.Arena
