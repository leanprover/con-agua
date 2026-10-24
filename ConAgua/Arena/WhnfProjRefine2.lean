import ConAgua.Arena.WhnfProjRefine

/-!
# `find_proj` refines `IFEnv.findProj?` under `CoreS` (lane `whnf3`, helper `whnf3-proj`)

* **The write set** (`projProgC_closed`, from the text): `proj_table_name`, `find_proj` and their
  callees write the pool and its top, and the name tables `str`/`num` with their counts, nothing
  else: `ErecKept`'s `find_proj` half and the `EREC` reads after the name interning.
* **`env_find` as a word model** (`efW`, `envFind_specWP`): its answer from the rows, so that a found
  row is known to decode (`EnvR.row_decP`: `EnvR`'s keys and values).
* **`find_proj`** (`findProjW`, `findProj_refines`, `projFound`).
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
def projWA : List ArrId := [0, 35, 36, 37, 38]
/-- The pool top (0) and the two tables' counts (36‥39). -/
def projC : List Word := [0, 36, 37, 38, 39]

theorem projProgC_closed : closedA projProgC projWA projC projFns = true := by decide +kernel

theorem ProjProg.closed {p : Prog} (hp : ProjProg p) : closedA p projWA projC projFns = true :=
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
    MemFrame projWA projC m m' :=
  (run_memFrame hp.closed hf (run_of_callW h)).1

theorem proj_frame_erec {p : Prog} (hp : ProjProg p) {f : FnName} (hf : f ∈ projFns) {n : Nat}
    {vs : List Word} {m : Mem} {r : List Word} {m' : Mem} (h : callW p n f vs m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC ∧ rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 :=
  ⟨(proj_frame hp hf h).1 EREC (by simp [projWA, EREC]) (by decide),
    (proj_frame hp hf h).2.1 129 (by simp [projC])⟩

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

/-- **A row that exists decodes** (`EnvR`'s keys and values). -/
theorem EnvR.row_decP {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
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
def findProjW (p : Prog) (n : Nat) (m : Mem) (vis t i : Word) : Option (Word × Word × Mem) :=
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
    ⦃fun r s' => LocEq s' s₀ ∧ findProjW p n s₀.mem vis t i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.findProj]
  simp only [callFn, findProjL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "proj_table_name", callW_spec p n "env_find"] <;>
    finish [findProjW]

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

theorem rowC_lt_iff (c vis : Word) (h0 : c ≠ 0) : (c - 1 < vis) ↔ (c.toNat - 1 < vis.toNat) := by
  have hc : 1 ≤ c.toNat := by
    have : c.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
    omega
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using hc)]
  simp

theorem rdW_some {a : Array Word} {x : Word} (h : rdW a x ≠ 0) : a[x.toNat]? = some (rdW a x) := by
  simp only [rdW] at h ⊢
  cases e : a[x.toNat]? with
  | none => rw [e] at h; simp at h
  | some v => rfl

/-- **`find_proj` refines `IFEnv.findProj?`** under `CoreS`. -/
@[refines ConRon.Arena.IFEnv.findProj?]
theorem findProj_refines (p : Prog) (hp : ProjProg p) : FindProjOK p := by
  intro n s₀ a₀ dn vis fe M eb T i hS hT
  cases n with
  | zero => exact CoreSpec.zeroW hp.findProj _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (findProj_spec p hp n s₀ vis T i)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold findProjW at hW
  rcases hc1 : callW p n "proj_table_name" [T] s.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [hc1, reduceCtorEq] at hW
  by_cases c1 : 4294967296 ≤ r₁.headD 0
  · rw [if_pos c1] at hW; cases hW
  rw [if_neg c1] at hW
  obtain ⟨ok1, ⟨M1, hS1, hK1, hSt1⟩, res1, -⟩ :=
    CoreSpec.of_callW (projTableName_refines p hp n s a₀ dn vis fe M eb T hS) hc1
  obtain ⟨hE1, h129⟩ := proj_frame_erec hp (by decide) hc1
  have hw : (r₁.headD 0).toNat < 2 ^ 32 := by
    have := mt UInt64.le_iff_toNat_le.mpr c1
    have e : (4294967296 : Word).toNat = 4294967296 := rfl
    rw [e] at this; omega
  rcases hc2 : callW p n "env_find" [r₁.headD 0, vis] m₁ with _ | ⟨r₂, m₂⟩ <;>
    simp only [hc2, reduceCtorEq] at hW
  obtain ⟨s₂, hs₂, hmem, -, ht, hf, hq⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (envFind_specWP p hp.envix hp.envrow hp.envfind n _ _ vis hw) hc2
  have hm2 : m₂ = m₁ := by rw [← hs₂]; exact hmem
  subst hm2
  have hrunT := findProj_run fe (decI T) i.toNat a₀ _ _ (AM.run_of_ok _ _ ok1)
  rw [res1] at hrunT
  obtain ⟨okT, stT, resT⟩ := AM.of_run_ok _ _ _ _ hrunT
  have hfind := EnvR.find?_eq hS1.env (r₁.headD 0) hw ht
  have hEs : m₂.arr64 EREC = s.mem.arr64 EREC := hE1
  -- the result words and the twin's answer, by the model's branches
  have key : s'.mem = m₂ ∧ r.headD 0 ≤ 1 ∧ fpRes (fe.find? (decI (r₁.headD 0))) i.toNat =
      decEntry (s.mem.arr64 EREC) (r.headD 0) (r.tail.headD 0) i.toNat := by
    simp only [efW] at hf hq
    by_cases b0 : r₂.headD 0 = 0
    · rw [if_pos b0] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, -, hm⟩ := hW
      refine ⟨hm.symm, by rw [← hr0]; decide, ?_⟩
      rw [← hr0, show decEntry (s.mem.arr64 EREC) 0 (r.tail.headD 0) i.toNat = none by simp [decEntry]]
      rw [hfind]
      by_cases z : rowC m₂ (r₁.headD 0) = 0
      · rw [if_pos z]; rfl
      · rw [if_neg z] at hf ⊢
        by_cases lt : rowC m₂ (r₁.headD 0) - 1 < vis
        · rw [if_pos lt] at hf; rw [b0] at hf; cases hf
        · rw [if_neg (mt (rowC_lt_iff _ _ z).mpr lt)]; rfl
    rw [if_neg b0] at hW
    -- a visible row
    have z : rowC m₂ (r₁.headD 0) ≠ 0 := fun z => by rw [if_pos z] at hf; exact b0 hf
    rw [if_neg z] at hf hq
    have lt : rowC m₂ (r₁.headD 0) - 1 < vis := Classical.byContradiction fun lt => by
      rw [if_neg lt] at hf; exact b0 hf
    rw [if_pos lt] at hf hq
    simp only at hq
    rw [hfind, if_neg z, if_pos ((rowC_lt_iff _ _ z).mp lt), ← hq]
    obtain ⟨ci, hci⟩ := EnvR.row_decP hS1.env (r₁.headD 0) hw ht z
    rw [← hq] at hci
    rw [hci]
    have hciF := ArrExt.decCI (erecP_ext m₂) hci
    by_cases b6 : rdW (m₂.arr64 EREC) (r₂.tail.headD 0) ≠ 6
    · rw [if_pos b6] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, -, hm⟩ := hW
      refine ⟨hm.symm, by rw [← hr0]; decide, ?_⟩
      rw [← hr0, show decEntry (s.mem.arr64 EREC) 0 (r.tail.headD 0) i.toNat = none by simp [decEntry]]
      cases ci with
      | projInfo tbl =>
        have := decCI_proj hciF
        simp only [rdW, this, Option.getD_some] at b6
        exact absurd rfl b6
      | _ => rfl
    rw [if_neg b6] at hW
    have b6' : rdW (m₂.arr64 EREC) (r₂.tail.headD 0) = 6 := by simpa using b6
    have h6 : (m₂.arr64 EREC)[(r₂.tail.headD 0).toNat]? = some 6 := by
      rw [rdW_some (by rw [b6']; decide), b6']
    obtain ⟨tbl, rfl, htbl⟩ := decCI_six hciF h6
    obtain ⟨w, hw7, hnf⟩ := decTbl_numFields htbl
    have hq7 : (r₂.tail.headD 0 + 7).toNat = (r₂.tail.headD 0).toNat + 7 := by
      have hsz : (r₂.tail.headD 0).toNat < (m₂.arr64 EREC).size := by
        have := (Array.getElem?_eq_some_iff.mp h6).1; exact this
      have := hS1.erec
      rw [UInt64.toNat_add]
      have e7 : (7 : Word).toNat = 7 := rfl
      rw [e7]; exact Nat.mod_eq_of_lt (by omega)
    have hrd7 : rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 7) = w := by
      simp only [rdW, hq7, hw7, Option.getD_some]
    rw [hrd7] at hW
    simp only [fpRes, hnf]
    by_cases bi : i < w
    · rw [if_pos bi] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      refine ⟨hm.symm, by rw [← hr0]; decide, ?_⟩
      rw [if_pos (UInt64.lt_iff_toNat_lt.mp bi), ← hr0, ← hr1]
      have h10 : ((1 : Word) = 0) = False := by decide
      simp only [decEntry, h10, ite_false, ← hEs, htbl, Option.map_some]
    · rw [if_neg bi] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, -, hm⟩ := hW
      refine ⟨hm.symm, by rw [← hr0]; decide, ?_⟩
      rw [if_neg (mt UInt64.lt_iff_toNat_lt.mpr bi), ← hr0]
      simp [decEntry]
  refine ⟨okT, ⟨M1, by rw [stT, key.1]; exact hS1, hK1, by rw [key.1]; exact hSt1⟩, ?_, ?_⟩
  · rw [resT]; exact key.2.2
  · unfold ResH HW
    have h1 := UInt64.le_iff_toNat_le.mp key.2.1
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
  simp only at hW
  unfold findProjW at hW
  rcases hc1 : callW p n "proj_table_name" [T] m with _ | ⟨r₁, m₁⟩ <;>
    simp only [hc1, reduceCtorEq] at hW
  by_cases c1 : 4294967296 ≤ r₁.headD 0
  · rw [if_pos c1] at hW; cases hW
  rw [if_neg c1] at hW
  obtain ⟨-, ⟨M1, hS1, -, -⟩, -, -⟩ :=
    CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩) (projTableName_refines p hp n _ a₀ dn vis fe M eb T hS) hc1
  obtain ⟨hE1, -⟩ := proj_frame_erec hp (by decide) hc1
  have hw : (r₁.headD 0).toNat < 2 ^ 32 := by
    have := mt UInt64.le_iff_toNat_le.mpr c1
    have e : (4294967296 : Word).toNat = 4294967296 := rfl
    rw [e] at this; omega
  rcases hc2 : callW p n "env_find" [r₁.headD 0, vis] m₁ with _ | ⟨r₂, m₂⟩ <;>
    simp only [hc2, reduceCtorEq] at hW
  obtain ⟨s₂, hs₂, hmem, -, ht, hf, hq⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (envFind_specWP p hp.envix hp.envrow hp.envfind n _ _ vis hw) hc2
  have hm2 : m₂ = m₁ := by rw [← hs₂]; exact hmem
  subst hm2
  simp only [efW] at hf hq
  by_cases b0 : r₂.headD 0 = 0
  · rw [if_pos b0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    exact absurd hW.1.symm hr
  rw [if_neg b0] at hW
  have z : rowC m₂ (r₁.headD 0) ≠ 0 := fun z => by rw [if_pos z] at hf; exact b0 hf
  rw [if_neg z] at hf hq
  have lt : rowC m₂ (r₁.headD 0) - 1 < vis := Classical.byContradiction fun lt => by
    rw [if_neg lt] at hf; exact b0 hf
  rw [if_pos lt] at hf hq
  simp only at hq
  by_cases b6 : rdW (m₂.arr64 EREC) (r₂.tail.headD 0) ≠ 6
  · rw [if_pos b6] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    exact absurd hW.1.symm hr
  rw [if_neg b6] at hW
  have hq2 : r.tail.headD 0 = r₂.tail.headD 0 := by
    split at hW <;> simp only [Option.some.injEq, Prod.mk.injEq] at hW
    · exact hW.2.1.symm
    · exact absurd hW.1.symm hr
  obtain ⟨ci, hci⟩ := EnvR.row_decP hS1.env (r₁.headD 0) hw ht z
  rw [← hq] at hci
  have hciF := ArrExt.decCI (erecP_ext m₂) hci
  have b6' : rdW (m₂.arr64 EREC) (r₂.tail.headD 0) = 6 := by simpa using b6
  have h6 : (m₂.arr64 EREC)[(r₂.tail.headD 0).toNat]? = some 6 := by
    rw [rdW_some (by rw [b6']; decide), b6']
  obtain ⟨tbl, hct, htbl⟩ := decCI_six hciF h6
  refine ⟨tbl, by rw [hq2, ← hE1]; exact htbl, decI (r₁.headD 0), ?_⟩
  rw [EnvR.find?_eq hS1.env (r₁.headD 0) hw ht, if_neg z, if_pos ((rowC_lt_iff _ _ z).mp lt), ← hq,
    hci, hct]

end L.Arena
