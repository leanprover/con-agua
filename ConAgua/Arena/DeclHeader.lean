import ConAgua.Arena.DeclCvg
import ConAgua.Arena.IndRealWalk

/-!
# `install_header` refines `installHeader` (lane `decls2`, helper `decls2-header`)

On lane `indproofs`' template, as `install_value_guards` in `DeclCvg.lean`: word models of
`install_header` and of its real callees (`env_row_get`/`env_find` without a handle bound,
`reserved_from`/`reserved_contains` by fuel), their `vcgen` specs, and the relational lemma
`ihW_ok` (a model run from the stage relation is a successful twin run of `installHeader`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-! ## `env_row_get`, `env_find` as word models (no bound on the name word) -/

/-- The row's first word as `env_row_get` reads it. -/
def rowCW (m : Mem) (w : Word) : Word := rdW (m.arr64 (selArr (rowSelW w))) (ixW w)

/-- The row's second word as `env_row_get` reads it. -/
def rowPW (m : Mem) (w : Word) : Word := rdW (m.arr64 (selArr (rowSelW w))) (ixW w + 1)

theorem rowGet_specW (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hp : p.lookup "env_row_get" = some envRowGetL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "env_row_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ tagW w ≤ 2 ∧ r.headD 0 = rowCW s₀.mem w ∧
      r.tail.headD 0 = rowPW s₀.mem w; ⊤⦄ := by
  have hts : (rowSelW w).toNat = 2 * (tagW w).toNat + rowTier w := by
    rw [rowSelW_toNat, tagW_toNat]
  have htr : rowTier w < 2 := Nat.mod_lt _ (by decide)
  rw [invoke_eq _ hp]
  simp only [callFn, envRowGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, envIx_spec p hx n] <;>
      finish [rowCW, rowPW, rdW_eq, selArr]

/-- **The model of `env_find(w, vis)`** (it leaves the memory alone). -/
def envFindW (m : Mem) (w vis : Word) : Option (List Word × Mem) :=
  if 2 < tagW w then none
  else if rowCW m w = 0 then some ([0, 0], m)
  else if rowCW m w - 1 < vis then some ([1, rowPW m w], m)
  else some ([0, 0], m)

theorem envFind_specW (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) (w vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ envFindW s₀.mem w vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, rowGet_specW p hx hg n] <;>
      finish [envFindW]

theorem rowCW_eq (m : Mem) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : tagW w ≤ 2) :
    rowCW m w = rowC m w := by
  have h1 := tagW_toNat w
  have h2 := ixW_toNat w hw
  have ht' : rowTag w ≤ 2 := by rw [← h1]; exact UInt64.le_iff_toNat_le.mp ht
  simp only [rowCW, rowC, ht', if_true, rdW, h2]
  simp [selArr_rowSelW w ht']

/-- **A miss of `env_find` is a miss of `find?`**. -/
theorem envFindW_miss {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem}
    {w : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) (hE : EnvR dn m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : r.headD 0 = 0) : m1 = m ∧ fe.find? (decI w) = none := by
  unfold envFindW at h
  by_cases ht : 2 < tagW w
  · simp [ht] at h
  rw [if_neg ht] at h
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => ht (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  rw [EnvR.find?_eq hE w hw htag, ← rowCW_eq m w hw ht2]
  by_cases hc : rowCW m w = 0
  · rw [if_pos hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, by simp [hc]⟩
  rw [if_neg hc] at h
  by_cases hv : rowCW m w - 1 < vis
  · rw [if_pos hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0
  rw [if_neg hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
  refine ⟨h.2.symm, ?_⟩
  have hc' : (rowCW m w).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
  have : ¬ (rowCW m w).toNat - 1 < vis.toNat := by
    intro e; apply hv; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simpa using e
  simp [hc, this]

/-! ## `reserved_from`, `reserved_contains` -/

/-- The model of `reserved_from(x, j)`. -/
def resFromW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, x, j =>
    if 16 ≤ j then some 0
    else if rdW (m.arr64 PINS) (55 + j) = x then some 1
    else resFromW n m x (j + 1)

section arms
variable (n : Nat) (m : Mem) (x j : Word)
theorem resFromW_step : resFromW (n + 1) m x j =
    if 16 ≤ j then some 0
    else if rdW (m.arr64 PINS) (55 + j) = x then some 1
    else resFromW n m x (j + 1) := rfl
end arms

grind_pattern [ind_grind] resFromW_step => resFromW (n + 1) m x j

/-- The model of `reserved_contains(x)`. -/
def resContW : Nat → Mem → Word → Option Word
  | 0, _, _ => none
  | n + 1, m, x => if pinW m 0 = 0 then none else resFromW n m x 0

theorem resContW_step (n : Nat) (m : Mem) (x : Word) :
    resContW (n + 1) m x = if pinW m 0 = 0 then none else resFromW n m x 0 := rfl

grind_pattern [ind_grind] resContW_step => resContW (n + 1) m x

theorem resFrom_spec (p : Prog) (hp : p.lookup "reserved_from" = some reservedFrom) (n : Nat) :
    ∀ (s₀ : St) (x j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reserved_from" [x, j]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ resFromW n s₀.mem x j = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ x j; rw [invoke_eq _ hp]; simp only [callFn, reservedFrom]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ x j
    rw [invoke_eq _ hp]
    simp only [callFn, reservedFrom]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem resCont_spec (p : Prog) (hf : p.lookup "reserved_from" = some reservedFrom)
    (hp : p.lookup "reserved_contains" = some reservedContains) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reserved_contains" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ resContW n s₀.mem x = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, reservedContains]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, resFrom_spec p hf n] <;>
      finish (gen := 20) [pinW_eq]

/-- A miss of `reserved_from` from `j`: none of the reserved words from `j` on is `x`. -/
theorem resFromW_miss (n : Nat) : ∀ (m : Mem) (x j : Word), j.toNat ≤ 16 →
    resFromW n m x j = some 0 → ∀ i, j.toNat ≤ i → i < 16 → pinW m (55 + i) ≠ x := by
  induction n with
  | zero => intro m x j _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j hj h i hi hi16
    rw [resFromW_step] at h
    have hn16 : ¬ 16 ≤ j := by
      rw [UInt64.le_iff_toNat_le]; simp; omega
    rw [if_neg hn16] at h
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · rw [if_pos he] at h; simp at h
    rw [if_neg he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rcases Nat.lt_or_ge j.toNat i with hlt | hge
    · exact ih m x (j + 1) (by omega) h i (by omega) hi16
    · have hij : i = j.toNat := by omega
      subst hij
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he

/-- **A miss of `reserved_contains` is a miss of `reservedBasisNames`.** -/
theorem resContW_miss {m : Mem} {a : AState} {n : Nat} {x : Word} (hx : x.toNat < 2 ^ 32)
    (h : resContW n m x = some 0) (hP : PinsR m a.pins) :
    ∃ l, reservedBasisNames.run a = .ok (l, a) ∧ l.contains (decI x) = false := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [if_pos h0] at h; simp at h
  rw [if_neg h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  have hm := resFromW_miss n m x 0 (by simp) h
  rw [Bool.eq_false_iff]
  intro hc
  simp only [List.contains_iff_mem, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, e⟩ := hc
  exact hm i (Nat.zero_le _) hi ((decI_eq_iff _ (hF.reserved_lt i hi) _).mp e ▸ decI_word_self x hx)

/-! ## `install_header(vis, q)` -/

/-- The lookups `install_header`'s spec needs (the stubs need none). -/
structure IhProg (p : Prog) : Prop where
  ih : p.lookup "install_header" = some installHeaderL
  ix : p.lookup "env_ix" = some envIxL
  rowGet : p.lookup "env_row_get" = some envRowGetL
  find : p.lookup "env_find" = some envFindL
  resF : p.lookup "reserved_from" = some reservedFrom
  resC : p.lookup "reserved_contains" = some reservedContains
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "cv_lps" = some cvLps
  cont : p.lookup "sl_contains" = some slContains
  nodup : p.lookup "sl_nodup" = some slNodup
  bvb : BvbProg p
  hf : HfF p

mutual
/-- **The model of `install_header`** (the name `x` and the type `t` read from `EREC` first). -/
def ihW (cR : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q =>
    ihK1 cR n vis q (rdW (m.arr64 EREC) q) (rdW (m.arr64 EREC) (q + 3))
      (envFindW m (rdW (m.arr64 EREC) q) vis)

def ihK1 (cR : CallM) (n : Nat) (vis q x t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 ≠ 0 then none else ihK2 cR n vis q x t m1 (resContW n m1 x)

def ihK2 (cR : CallM) (n : Nat) (vis q x t : Word) (m1 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some c => if c ≠ 0 then none else ihK4 cR n vis t (cvLpsW n m1 q)

def ihK4 (cR : CallM) (n : Nat) (vis t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ihK5 cR n vis t r4 m4 (nodupW n m4 (r4.headD 0) (r4.tail.headD 0))

def ihK5 (cR : CallM) (n : Nat) (vis t : Word) (r4 : List Word) (m4 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some d =>
    if d = 0 then none else ihK6 cR n vis t r4 (lbbF m4 [4000000000, 0, t])

def ihK6 (cR : CallM) (n : Nat) (vis t : Word) (r4 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    if r6.headD 0 = 0 then none else ihK7 cR n vis t r4 (hffF m6 [4000000000, t])

def ihK7 (cR : CallM) (n : Nat) (vis t : Word) (r4 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) =>
    if r7.headD 0 ≠ 0 then none
    else ihK8 cR n vis t (cR n "all_level_params_defined" [r4.headD 0, r4.tail.headD 0, t] m7)

def ihK8 (cR : CallM) (n : Nat) (vis t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m8) =>
    if r8.headD 0 = 0 then none else ihK9 (cR n "consts_resolve_ffast" [vis, t] m8)

def ihK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r9, m9) => if r9.headD 0 = 0 then none else some ([0], m9)
end

section arms
variable (cR : CallM) (n : Nat) (m m1 m4 m6 m7 m8 m9 : Mem) (vis q x t : Word) (c d : Word)
  (r1 r4 r6 r7 r8 r9 : List Word)
theorem ihW_step : ihW cR (n + 1) m vis q =
    ihK1 cR n vis q (rdW (m.arr64 EREC) q) (rdW (m.arr64 EREC) (q + 3))
      (envFindW m (rdW (m.arr64 EREC) q) vis) := rfl
theorem ihK1_some : ihK1 cR n vis q x t (some (r1, m1)) =
    if r1.headD 0 ≠ 0 then none else ihK2 cR n vis q x t m1 (resContW n m1 x) := rfl
theorem ihK2_some : ihK2 cR n vis q x t m1 (some c) =
    if c ≠ 0 then none else ihK4 cR n vis t (cvLpsW n m1 q) := rfl
theorem ihK4_some : ihK4 cR n vis t (some (r4, m4)) =
    ihK5 cR n vis t r4 m4 (nodupW n m4 (r4.headD 0) (r4.tail.headD 0)) := rfl
theorem ihK5_some : ihK5 cR n vis t r4 m4 (some d) =
    if d = 0 then none
    else ihK6 cR n vis t r4 (lbbF m4 [4000000000, 0, t]) := rfl
theorem ihK6_some : ihK6 cR n vis t r4 (some (r6, m6)) =
    if r6.headD 0 = 0 then none else ihK7 cR n vis t r4 (hffF m6 [4000000000, t]) :=
  rfl
theorem ihK7_some : ihK7 cR n vis t r4 (some (r7, m7)) =
    if r7.headD 0 ≠ 0 then none
    else ihK8 cR n vis t (cR n "all_level_params_defined" [r4.headD 0, r4.tail.headD 0, t] m7) := rfl
theorem ihK8_some : ihK8 cR n vis t (some (r8, m8)) =
    if r8.headD 0 = 0 then none else ihK9 (cR n "consts_resolve_ffast" [vis, t] m8) := rfl
theorem ihK9_some : ihK9 (some (r9, m9)) = if r9.headD 0 = 0 then none else some ([0], m9) := rfl
end arms

grind_pattern [ind_grind] ihW_step => ihW cR (n + 1) m vis q
grind_pattern [ind_grind] ihK1_some => ihK1 cR n vis q x t (some (r1, m1))
grind_pattern [ind_grind] ihK2_some => ihK2 cR n vis q x t m1 (some c)
grind_pattern [ind_grind] ihK4_some => ihK4 cR n vis t (some (r4, m4))
grind_pattern [ind_grind] ihK5_some => ihK5 cR n vis t r4 m4 (some d)
grind_pattern [ind_grind] ihK6_some => ihK6 cR n vis t r4 (some (r6, m6))
grind_pattern [ind_grind] ihK7_some => ihK7 cR n vis t r4 (some (r7, m7))
grind_pattern [ind_grind] ihK8_some => ihK8 cR n vis t (some (r8, m8))
grind_pattern [ind_grind] ihK9_some => ihK9 (some (r9, m9))

theorem ih_specW (p : Prog) (h : IhProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_header" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ihW cR n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ih]
  simp only [callFn, installHeaderL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p h.ix h.rowGet h.find n, resCont_spec p h.resF h.resC n,
        cvLps_specW p h.alloc h.copy h.eti h.lps n, slNodup_spec p h.cont h.nodup n,
        lbbF_spec p h.bvb n, hffF_spec p h.hf n,
        hcR n "all_level_params_defined", hcR n "consts_resolve_ffast",
        hcR n "unresolved_consts_error"] <;>
      finish (gen := 20)

/-! ## The relational lemma -/

end L.Arena
