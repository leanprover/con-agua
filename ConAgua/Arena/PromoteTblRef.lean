import ConAgua.Arena.PromoteCIRef30

/-!
# The table side of the promotion: `erase_installed_tables`, `promote_proj_tables`,
`index_promoted_tables`, `promote_new_tables`

The tables a step installed are the newest `ETAB` slots (`IEnv.tables` newest first, `ETAB` oldest
first), as the constants are the newest `ECON` slots: the walks mirror `erase_installed`,
`promote_ci_list`, `index_promoted` (`PromoteCIRef24.lean`, `27`, `28`), over `TablesAt` and
`decTbl` instead of `ConstsAt` and `decCI`, the rows written by `tbl_row_set` (`EnvR.setTblRow`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The table-row arrays (both tiers). -/
abbrev tblArrs : List ArrId := [TIXA, TIXS, TIXN, 385, 386, 387]

theorem tblArr_mem (w : Word) (hw : rowTag w ≤ 2) : tblArr w ∈ tblArrs := by
  rcases tblArr_cases w hw with h | h | h | h | h | h <;> rw [h] <;> decide

theorem tblSet_frame (m : Mem) (w v : Word) (hw : rowTag w ≤ 2) :
    MemFrame tblArrs [] m (tblSet m w v) := by
  have hne : tblArr w ≠ CTL := by
    rcases tblArr_cases w hw with h | h | h | h | h | h <;> rw [h] <;> decide
  exact (MemFrame.set64 m (tblArr w) hne (tixW w) v).mono
    (by simpa using tblArr_mem w hw) (by simp)

theorem promoteProjTables_nil (pm : PMemo) (fuel : Nat) :
    promoteProjTables pm fuel [] = pure (pm, []) := by
  rw [promoteProjTables]
theorem promoteProjTables_cons (pm : PMemo) (fuel : Nat) (t : IProjTable) (ts : List IProjTable) :
    promoteProjTables pm fuel (t :: ts) = (do
      let (m, t) ← promoteProjTable pm fuel t
      let (m, ts) ← promoteProjTables m fuel ts
      pure (m, t :: ts)) := by
  rw [promoteProjTables]

theorem eraseInstalledTables_cons (tbls : Std.HashMap NIdx IProjTable) (t : IProjTable)
    (ts : List IProjTable) :
    eraseInstalledTables tbls (t :: ts) = eraseInstalledTables (tbls.erase t.structName) ts := by
  rw [eraseInstalledTables]

theorem indexPromotedTables_cons (tbls : Std.HashMap NIdx IProjTable) (t : IProjTable)
    (ts : List IProjTable) :
    indexPromotedTables tbls (t :: ts) = (indexPromotedTables tbls ts).insert t.structName t := by
  rw [indexPromotedTables]

/-- A write to the table rows keeps the arena, the promotion memos. -/
theorem arenaD_tbl {m m' : Mem} {a : AState} {pm : PMemo} (hD : ArenaD m a) (hP : PMemoR m pm)
    (hf : MemFrame tblArrs [] m m') : ArenaD m' a ∧ PMemoR m' pm :=
  ⟨⟨ArenaR.frame (by decide) (by simp) hf hD.1,
    DerR.frameM _ _ m _ hf (by decide) a hD.2⟩,
    hP.frame (by decide) (by simp) hf⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem tblAt_call {n : Nat} {j : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "tbl_at" [j] m = some (r, m')) :
    m' = m ∧ j.toNat < (m.arr64 ETAB).size ∧ g0 r = rdW (m.arr64 ETAB) j := by
  obtain ⟨s', rfl, h1, -, h3, h4⟩ := callW_triple (tblAt_spec p (hp.get "tbl_at") n ⟨m, Locals.init []⟩ j) hc
  exact ⟨h1, h3, h4⟩

theorem tblPut_call {n : Nat} {j q : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "tbl_put" [j, q] m = some (r, m')) :
    m' = m.set64 ETAB j q ∧ j.toNat < (m.arr64 ETAB).size := by
  obtain ⟨s', rfl, h1, -, h3⟩ := callW_triple (tblPut_spec p (hp.get "tbl_put") n ⟨m, Locals.init []⟩ j q) hc
  exact ⟨h1, h3⟩

theorem tblRowSet_call {n : Nat} {w v : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "tbl_row_set" [w, v] m = some (r, m')) :
    m' = tblSet m w v ∧ rowTag w ≤ 2 ∧ tblIx w < (m.arr64 (tblArr w)).size := by
  obtain ⟨s', rfl, h1, -, h3, h4⟩ := callW_triple
    (tblRowSet_spec p (hp.get "tbl_ix") (hp.get "tbl_row_set") n ⟨m, Locals.init []⟩ w v) hc
  exact ⟨h1, h3, h4⟩

theorem tblCnt_call {n : Nat} {m m' : Mem} {r : List Word}
    (hc : callW p n "tbl_cnt" [] m = some (r, m')) :
    m' = m ∧ g0 r = rdW (m.arr64 CTL) 133 := by
  obtain ⟨s', rfl, h1, -, h3⟩ := callW_triple (tblCnt_spec p (hp.get "tbl_cnt") n ⟨m, Locals.init []⟩) hc
  exact ⟨h1, h3⟩

/-- The structure name word of a table record in the pool, read by `erec_rd1(q + 2)`. -/
theorem tblName_call {n : Nat} {q : Word} {m m' : Mem} {r : List Word} {t : IProjTable}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (ht : decTbl (erecP m) q.toNat = some t)
    (hc : callW p n "erec_rd1" [q + 2] m = some (r, m')) :
    m' = m ∧ (g0 r).toNat < 2 ^ 32 ∧ t.structName = decI (g0 r) ∧ q.toNat + 2 < (m.arr64 EREC).size := by
  obtain ⟨w, hwA, hwl, hname⟩ := decTbl_name ht
  have hwm := erecP_get hwA
  have hlt : q.toNat + 2 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hwm).1
  have e2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hm0, hr0, -⟩ := rd1_call p hp hc
  rw [rd1W_of hsz (by rw [e2]; simpa using hwm)] at hr0
  subst hr0
  exact ⟨hm0, hwl, hname, hlt⟩

/-- **`erase_installed_tables` refines `eraseInstalledTables`.** -/
theorem eraseT_rel (dn : NIdx → Option ConLeche.Name) : ∀ (n : Nat) (m : Mem) (vis j k : Word)
    (fe : IFEnv) (installed : List IProjTable) (r : List Word) (m' : Mem),
    EnvR dn m vis fe → (m.arr64 EREC).size < 2 ^ 64 → k.toNat = installed.length →
    installed.length ≤ j.toNat + 1 →
    TablesAt (erecP m) (m.arr64 ETAB) j.toNat installed →
    callW p n "erase_installed_tables" [j, k] m = some (r, m') →
    EnvR dn m' vis ⟨fe.env, fe.idx, fe.visibleBelow, eraseInstalledTables fe.tbls installed⟩ ∧
      MemFrame tblArrs [] m m' := by
  intro n
  induction n with
  | zero => intro m vis j k fe installed r m' _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m vis j k fe installed r m' hE hsz hk hj hcon hc
  obtain ⟨s', hs', -, hW⟩ := callW_triple (eraseInstalledTables_spec p hp n ⟨m, Locals.init []⟩ j k) hc
  simp only at hW
  rw [hs'] at hW
  simp only [eraseTW] at hW
  cases installed with
  | nil =>
    have hk0 : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    rw [if_pos hk0] at hW
    have hm : m = m' := Option.some.inj hW
    subst hm
    exact ⟨by simpa [eraseInstalledTables] using hE, MemFrame.refl _ _ _⟩
  | cons t ts =>
    have hk0 : k ≠ 0 := by
      intro h; rw [h] at hk; simp at hk
    rw [if_neg hk0] at hW
    obtain ⟨⟨ptr, hptr, hdec⟩, hrest⟩ := hcon
    obtain ⟨⟨rq, m0⟩, hq, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hm0, -, hrq⟩ := tblAt_call p hp hq
    subst m0
    rw [hrq, pci_rdW_of_get? _ j (by simpa using hptr)] at hW
    obtain ⟨⟨rw', m0'⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hm0', hwl, hname, -⟩ := tblName_call p hp hsz hdec hrd
    subst m0'
    obtain ⟨⟨z, m1⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hm1, hrt, hrb⟩ := tblRowSet_call p hp hcb
    subst m1
    generalize g0 rw' = w at hwl hname hrt hrb hcb hW
    have hE1 : EnvR dn (tblSet m w 0) vis
        ⟨fe.env, fe.idx, fe.visibleBelow, fe.tbls.erase t.structName⟩ := by
      refine hE.setTblRow w 0 hwl hrt hrb _ none ?_ (by simp) (fun h => absurd rfl h)
      intro nn
      rw [Std.HashMap.getElem?_erase, hname]
      by_cases e : nn.word.toUInt64 = w
      · have : decI w = nn := (decI_eq_iff w hwl nn).mpr e.symm
        simp [e, this]
      · have : ¬ decI w = nn := fun h => e ((decI_eq_iff w hwl nn).mp h).symm
        simp [e, this]
    have hfr := tblSet_frame m w 0 hrt
    have hEE : (tblSet m w 0).arr64 EREC = m.arr64 EREC := hfr.1 EREC (by decide) (by decide)
    have hET : (tblSet m w 0).arr64 ETAB = m.arr64 ETAB := hfr.1 ETAB (by decide) (by decide)
    have hP1 : erecP (tblSet m w 0) = erecP m := erecP_congr hEE (hfr.2.1 129 (by simp))
    have hszz : ((tblSet m w 0).arr64 EREC).size < 2 ^ 64 := by rw [hEE]; exact hsz
    have hlenk : (k - 1).toNat = ts.length := by
      rw [toNat_sub1 k hk0]; simp at hk; omega
    have hjn : ts = [] ∨ j ≠ 0 := by
      by_cases h : j = 0
      · left
        cases ts with
        | nil => rfl
        | cons c0 cs0 => simp only [List.length_cons] at hj; rw [h] at hj; simp at hj
      · exact .inr h
    have hj1 : ts.length ≤ (j - 1).toNat + 1 := by
      rcases hjn with h | h
      · subst h; simp
      · rw [toNat_sub1 j h]; simp only [List.length_cons] at hj; have := toNat_pred j h; omega
    have hcon' : TablesAt (erecP (tblSet m w 0)) ((tblSet m w 0).arr64 ETAB) (j - 1).toNat ts := by
      rcases hjn with h | h
      · subst h; trivial
      · rw [toNat_sub1 j h, hP1, hET]; exact hrest
    cases hcc : callW p n "erase_installed_tables" [j - 1, k - 1] (tblSet m w 0) with
    | none => rw [hcc] at hW; cases hW
    | some y =>
    obtain ⟨z2, m3⟩ := y
    rw [hcc, memK_some] at hW
    have hm3 : m3 = m' := Option.some.inj hW
    subst hm3
    obtain ⟨hEf, hfr2⟩ := ih (tblSet m w 0) vis (j - 1) (k - 1) _ ts z2 m3 hE1 hszz hlenk hj1 hcon' hcc
    refine ⟨?_, hfr.trans hfr2⟩
    rw [eraseInstalledTables_cons]
    exact hEf

/-- **`index_promoted_tables` refines `indexPromotedTables`.** -/
theorem indexT_rel (dn : NIdx → Option ConLeche.Name) : ∀ (n : Nat) (m : Mem) (vis j k : Word)
    (fe : IFEnv) (installed : List IProjTable) (r : List Word) (m' : Mem),
    EnvR dn m vis fe → (m.arr64 EREC).size < 2 ^ 64 → k.toNat = installed.length →
    installed.length ≤ j.toNat + 1 →
    TablesAt (erecP m) (m.arr64 ETAB) j.toNat installed →
    callW p n "index_promoted_tables" [j, k] m = some (r, m') →
    EnvR dn m' vis ⟨fe.env, fe.idx, fe.visibleBelow, indexPromotedTables fe.tbls installed⟩ ∧
      MemFrame tblArrs [] m m' := by
  intro n
  induction n with
  | zero => intro m vis j k fe installed r m' _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m vis j k fe installed r m' hE hsz hk hj hcon hc
  obtain ⟨s', hs', -, hW⟩ := callW_triple (indexPromotedTables_spec p hp n ⟨m, Locals.init []⟩ j k) hc
  simp only at hW
  rw [hs'] at hW
  simp only [indexTW] at hW
  cases installed with
  | nil =>
    have hk0 : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    rw [if_pos hk0] at hW
    have hm : m = m' := Option.some.inj hW
    subst hm
    exact ⟨by simpa [indexPromotedTables] using hE, MemFrame.refl _ _ _⟩
  | cons t ts =>
    have hk0 : k ≠ 0 := by
      intro h; rw [h] at hk; simp at hk
    rw [if_neg hk0] at hW
    obtain ⟨⟨ptr, hptr, hdec⟩, hrest⟩ := hcon
    have hlenk : (k - 1).toNat = ts.length := by
      rw [toNat_sub1 k hk0]; simp at hk; omega
    have hjn : ts = [] ∨ j ≠ 0 := by
      by_cases h : j = 0
      · left
        cases ts with
        | nil => rfl
        | cons c0 cs0 => simp only [List.length_cons] at hj; rw [h] at hj; simp at hj
      · exact .inr h
    have hj1 : ts.length ≤ (j - 1).toNat + 1 := by
      rcases hjn with h | h
      · subst h; simp
      · rw [toNat_sub1 j h]; simp only [List.length_cons] at hj; have := toNat_pred j h; omega
    have hcon' : TablesAt (erecP m) (m.arr64 ETAB) (j - 1).toNat ts := by
      rcases hjn with h | h
      · subst h; trivial
      · rw [toNat_sub1 j h]; exact hrest
    -- the tail first
    obtain ⟨⟨z0, m1⟩, hc0, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hE1, hfr1⟩ := ih m vis (j - 1) (k - 1) fe ts z0 m1 hE hsz hlenk hj1 hcon' hc0
    have hEE : m1.arr64 EREC = m.arr64 EREC := hfr1.1 EREC (by decide) (by decide)
    have hET : m1.arr64 ETAB = m.arr64 ETAB := hfr1.1 ETAB (by decide) (by decide)
    have hP1 : erecP m1 = erecP m := erecP_congr hEE (hfr1.2.1 129 (by simp))
    have hsz1 : (m1.arr64 EREC).size < 2 ^ 64 := by rw [hEE]; exact hsz
    rw [← hP1] at hdec
    rw [← hET] at hptr
    -- the head
    obtain ⟨⟨rq, m2⟩, hq, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hm2, -, hrq⟩ := tblAt_call p hp hq
    subst m2
    rw [hrq, pci_rdW_of_get? _ j (by simpa using hptr)] at hW
    obtain ⟨⟨rw', m2'⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hm2', hwl, hname, hlt⟩ := tblName_call p hp hsz1 hdec hrd
    subst m2'
    cases hcb : callW p n "tbl_row_set" [g0 rw', ptr + 1] m1 with
    | none => rw [hcb] at hW; cases hW
    | some y =>
    obtain ⟨z3, m3⟩ := y
    rw [hcb, memK_some] at hW
    have hm3 : m3 = m' := Option.some.inj hW
    subst hm3
    obtain ⟨hm4, hrt, hrb⟩ := tblRowSet_call p hp hcb
    subst hm4
    generalize g0 rw' = w at hwl hname hrt hrb hcb
    have hq1 : (ptr + 1).toNat = ptr.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hne : ptr + 1 ≠ 0 := fun e => by rw [e] at hq1; simp at hq1
    have hE2 : EnvR dn (tblSet m1 w (ptr + 1)) vis
        ⟨fe.env, fe.idx, fe.visibleBelow, (indexPromotedTables fe.tbls ts).insert t.structName t⟩ := by
      refine hE1.setTblRow w (ptr + 1) hwl hrt hrb _ (some t) ?_ (by simp [hne])
        (fun _ => by rw [hq1, Nat.add_sub_cancel, hdec])
      intro nn
      rw [Std.HashMap.getElem?_insert, hname]
      by_cases e : nn.word.toUInt64 = w
      · have : decI w = nn := (decI_eq_iff w hwl nn).mpr e.symm
        simp [e, this]
      · have : ¬ decI w = nn := fun h => e ((decI_eq_iff w hwl nn).mp h).symm
        simp [e, this]
    refine ⟨?_, hfr1.trans (tblSet_frame m1 w (ptr + 1) hrt)⟩
    rw [indexPromotedTables_cons]
    exact hE2

/-- **`promote_proj_tables` refines `promoteProjTables`**: the slots `j, …, j - k + 1` hold the
promoted records, the other slots are untouched. -/
theorem ptables_rel : ∀ (n : Nat) (m : Mem) (a : AState)
    (pm : PMemo) (f j k : Word) (D : Nat) (installed : List IProjTable) (r : List Word)
    (m' : Mem), ArenaD m a → PMemoR m pm → (m.arr64 EREC).size < 2 ^ 64 →
    erecTop m ≤ (m.arr64 EREC).size → k.toNat = installed.length →
    installed.length ≤ j.toNat + 1 →
    TablesAt (preE m D) (m.arr64 ETAB) j.toNat installed → D ≤ erecTop m →
    callW p n "promote_proj_tables" [f, j, k] m = some (r, m') →
    ∃ a' pm' installed', (promoteProjTables pm f.toNat installed).run a =
        .ok ((pm', installed'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ cp a' = cp a ∧
      MemFrame (ETAB :: EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧ installed'.length = installed.length ∧
      TablesAt (erecP m') (m'.arr64 ETAB) j.toNat installed' ∧
      (∀ i, (j.toNat < i ∨ i + installed.length ≤ j.toNat) →
        (m'.arr64 ETAB)[i]? = (m.arr64 ETAB)[i]?) ∧
      (m'.arr64 ETAB).size = (m.arr64 ETAB).size := by
  intro n
  induction n with
  | zero => intro m a pm f j k D installed r m' _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f j k D installed r m' hD hP hsz hts hk hj hcon hDt hc
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteProjTables_spec p hp n ⟨m, Locals.init []⟩ f j k) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ptsW] at hW
  cases installed with
  | nil =>
    have hk0 : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    rw [if_pos hk0] at hW
    have hm : m = m' := Option.some.inj hW
    subst hm
    refine ⟨a, pm, [], ?_, hD, hP, rfl, MemFrame.refl _ _ _, TierKeep.refl _, ErecGrow.refl _, hts, rfl,
      trivial, fun _ _ => rfl, rfl⟩
    rw [promoteProjTables_nil]; rfl
  | cons t ts =>
    have hk0 : k ≠ 0 := by
      intro h; rw [h] at hk; simp at hk
    rw [if_neg hk0] at hW
    obtain ⟨⟨ptr, hptr, hdec⟩, hrest⟩ := hcon
    have hbd := (Array.getElem?_eq_some_iff.mp hptr).1
    obtain ⟨⟨rq, m0⟩, hq, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hm0, -, hrq⟩ := tblAt_call p hp hq
    subst m0
    rw [hrq, pci_rdW_of_get? _ j (by simpa using hptr)] at hW
    obtain ⟨⟨dl, m1⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    have hpre := preE_size_le m D
    have hb := pmDecTbl_bound hdec
    obtain ⟨a1, pm1, t', hrun1, hD1, hP1, hcp1, hfr1, htk1, hg1, hts1, hptr1, hptr13, hdec1⟩ :=
      proj_rel p hp n m a pm f ptr D t dl m1 hD hP hsz hts hdec (by omega) hDt hca
    have hE1 : m1.arr64 ETAB = m.arr64 ETAB :=
      hfr1.1 ETAB (fun h => by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h (by decide)
        · rcases vg_arrs ETAB (List.mem_cons.mpr (Or.inr h)) with h' | h' | h' <;>
            (simp only [ETAB, ArrId] at h'; omega)) (by decide)
    have hsz1 : (m1.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
    obtain ⟨⟨z0, m1'⟩, hpu, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hm1', -⟩ := tblPut_call p hp hpu
    subst m1'
    cases hcb : callW p n "promote_proj_tables" [f, j - 1, k - 1] (m1.set64 ETAB j (g0 dl)) with
    | none => rw [hcb] at hW; cases hW
    | some x =>
    obtain ⟨z, m3⟩ := x
    rw [hcb, memK_some] at hW
    have hm3 : m3 = m' := Option.some.inj hW
    subst hm3
    have hE2 : (m1.set64 ETAB j (g0 dl)).arr64 ETAB = (m1.arr64 ETAB).set! j.toNat (g0 dl) :=
      Mem.arr64_set64_same _ _ _ _
    have hfs : MemFrame [ETAB] [] m1 (m1.set64 ETAB j (g0 dl)) :=
      MemFrame.set64 m1 ETAB (by decide) _ _
    have hlenk : (k - 1).toNat = ts.length := by
      rw [toNat_sub1 k hk0]; simp at hk; omega
    have hjn : ts = [] ∨ j ≠ 0 := by
      by_cases h : j = 0
      · left
        cases ts with
        | nil => rfl
        | cons c0 cs0 => simp only [List.length_cons] at hj; rw [h] at hj; simp at hj
      · exact .inr h
    have hj1 : ts.length ≤ (j - 1).toNat + 1 := by
      rcases hjn with h | h
      · subst h; simp
      · rw [toNat_sub1 j h]; simp only [List.length_cons] at hj; have := toNat_pred j h; omega
    obtain ⟨hDf, hPf⟩ : ArenaD (m1.set64 ETAB j (g0 dl)) a1 ∧
        PMemoR (m1.set64 ETAB j (g0 dl)) pm1 :=
      ⟨⟨ArenaR.frame_ext _ _ (by simp [ETAB]) (by simp) m1 _ hfs a1 hD1.1,
        DerR.frameM _ _ m1 _ hfs (by simp [ETAB]) a1 hD1.2⟩,
        hP1.frame (by simp [ETAB]) (by simp) hfs⟩
    have hEE : (m1.set64 ETAB j (g0 dl)).arr64 EREC = m1.arr64 EREC :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hT2 : erecTop (m1.set64 ETAB j (g0 dl)) = erecTop m1 := by
      simp only [erecTop]; rw [hfs.2.1 129 (by simp)]
    have hg12 : ErecGrow m1 (m1.set64 ETAB j (g0 dl)) := ErecGrow.of_eq hEE hT2
    have hEtab : ∀ i, i ≠ j.toNat → ((m1.set64 ETAB j (g0 dl)).arr64 ETAB)[i]? = (m.arr64 ETAB)[i]? := by
      intro i hi
      rw [hE2, arr_set!_get?, if_neg (by omega), hE1]
    have hcon' : TablesAt (preE (m1.set64 ETAB j (g0 dl)) D)
        ((m1.set64 ETAB j (g0 dl)).arr64 ETAB) (j - 1).toNat ts := by
      rcases hjn with h | h
      · subst h; trivial
      · rw [toNat_sub1 j h]
        refine TablesAt.mono (A := preE m D) ?_ ts (j.toNat - 1) (by have := toNat_pred j h; omega)
          (fun i hi1 hi2 => hEtab i (by have := toNat_pred j h; omega)) hrest
        exact preE_ext (fun i hi => by
          rw [hEE]; exact hg1.2.1 i (by omega))
    obtain ⟨a3, pm3, ts', hrun3, hD3, hP3, hcp3, hfr3, htk3, hg3, hts3, hlen3, hcons3, hout3, hsz3E⟩ :=
      ih (m1.set64 ETAB j (g0 dl)) a1 pm1 f (j - 1) (k - 1) D ts z m3 hDf hPf
        (by rw [hEE]; exact hsz1) (by rw [hEE, hT2]; exact hts1) hlenk hj1 hcon'
        (by rw [hT2]; have := hg1.1; omega) hcb
    have hext : ErecGrow m1 m3 := hg12.trans hg3
    refine ⟨a3, pm3, t' :: ts', ?_, hD3, hP3, hcp3.trans hcp1, ?_,
      htk1.trans ((TierKeep.of_frame hfs (by simp)).trans htk3), hg1.trans hext, hts3, ?_, ?_, ?_, ?_⟩
    · rw [promoteProjTables_cons, run_bind_ok hrun1]
      simp only
      rw [run_bind_ok hrun3]; rfl
    · exact ((hfr1.mono (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)).trans
        (hfs.mono (by simp) (by simp))).trans hfr3
    · simp [hlen3]
    · have hj_out : (j - 1).toNat < j.toNat ∨ j.toNat + ts.length ≤ (j - 1).toNat := by
        rcases hjn with h | h
        · subst h; simp; omega
        · rw [toNat_sub1 j h]; have := toNat_pred j h; omega
      have hbd' : j.toNat < (m1.arr64 ETAB).size := by rw [hE1]; exact hbd
      refine ⟨⟨g0 dl, ?_, hext.ext.decTbl ?_⟩, ?_⟩
      · rw [hout3 _ hj_out, hE2, arr_set!_get?, if_pos ⟨rfl, hbd'⟩]
      · have : (g0 dl).toNat = (dl.headD 0).toNat := rfl
        rw [this]; exact hdec1
      · rcases hjn with h | h
        · subst h; have : ts' = [] := List.length_eq_zero_iff.mp (by simpa using hlen3)
          subst this; trivial
        · rw [← toNat_sub1 j h]; exact hcons3
    · intro i hi
      simp only [List.length_cons] at hi
      have hne : i ≠ j.toNat := by omega
      have hi' : (j - 1).toNat < i ∨ i + ts.length ≤ (j - 1).toNat := by
        rcases hjn with h | h
        · subst h; simp; omega
        · rw [toNat_sub1 j h]; have := toNat_pred j h; omega
      rw [hout3 i hi', hEtab i hne]
    · rw [hsz3E, hE2]; simp [hE1]

end rel

end L.Arena
