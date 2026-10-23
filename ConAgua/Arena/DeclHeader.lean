import ConAgua.Arena.DeclCvg
import ConAgua.Arena.IndRealIpf


noncomputable section

/-!
# `install_header` refines `installHeader` (lane `decls2`, helper `decls2-header`)

On lane `indproofs`' template, as `install_value_guards` in `DeclCvg.lean`: word models of
`install_header` and of its real callees (`env_row_get`/`env_find` without a handle bound,
`reserved_from`/`reserved_contains` by fuel), their `vcgen` specs, and the relational lemma
`ihW_ok` (a model run from the stage relation is a successful twin run of `installHeader`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-! ## `env_row_get`, `env_find` as word models (no bound on the name word) -/

/-- The row's first word as `env_row_get` reads it. -/
def rowCW (m : Mem) (w : Word) : Word :=
  if tagW w = 0 then rdW (m.arr64 EIXA) (ixW w)
  else if tagW w = 1 then rdW (m.arr64 EIXS) (ixW w) else rdW (m.arr64 EIXN) (ixW w)

/-- The row's second word as `env_row_get` reads it. -/
def rowPW (m : Mem) (w : Word) : Word :=
  if tagW w = 0 then rdW (m.arr64 EIXA) (ixW w + 1)
  else if tagW w = 1 then rdW (m.arr64 EIXS) (ixW w + 1) else rdW (m.arr64 EIXN) (ixW w + 1)

theorem rowGet_specW (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hp : p.lookup "env_row_get" = some envRowGetL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "env_row_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ tagW w ≤ 2 ∧ r.headD 0 = rowCW s₀.mem w ∧
      r.tail.headD 0 = rowPW s₀.mem w; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envRowGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, envIx_spec p hx n] <;>
      finish [rowCW, rowPW, rdW_eq]

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
  have : rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2 := by omega
  rcases this with h | h | h
  · have : tagW w = 0 := UInt64.toNat_inj.mp (by rw [h1, h]; rfl)
    simp [this, h, EIXA]
  · have : tagW w = 1 := UInt64.toNat_inj.mp (by rw [h1, h]; rfl)
    simp [this, h, EIXS]
  · have : tagW w = 2 := UInt64.toNat_inj.mp (by rw [h1, h]; rfl)
    simp [this, h, EIXN]

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
  ipf : IpfF p

mutual
/-- **The model of `install_header`** (the name `x` and the type `t` read from `EREC` first). -/
def ihW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q =>
    ihK1 n vis q (rdW (m.arr64 EREC) q) (rdW (m.arr64 EREC) (q + 3))
      (envFindW m (rdW (m.arr64 EREC) q) vis)

def ihK1 (n : Nat) (vis q x t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 ≠ 0 then none else ihK2 n vis q x t m1 (resContW n m1 x)

def ihK2 (n : Nat) (vis q x t : Word) (m1 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some c => if c ≠ 0 then none else ihK3 n vis q t (ipfF m1 [x])

def ihK3 (n : Nat) (vis q t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => if r3.headD 0 ≠ 0 then none else ihK4 n vis t (cvLpsW n m3 q)

def ihK4 (n : Nat) (vis t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ihK5 vis t r4 m4 (nodupW n m4 (r4.headD 0) (r4.tail.headD 0))

def ihK5 (vis t : Word) (r4 : List Word) (m4 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some d =>
    if d = 0 then none else ihK6 vis t r4 (stubM "loose_bvars_bounded_fast" m4 [4000000000, 0, t])

def ihK6 (vis t : Word) (r4 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    if r6.headD 0 = 0 then none else ihK7 vis t r4 (stubM "has_fvar_fast" m6 [4000000000, t])

def ihK7 (vis t : Word) (r4 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) =>
    if r7.headD 0 ≠ 0 then none
    else ihK8 vis t (stubM "all_level_params_defined" m7 [r4.headD 0, r4.tail.headD 0, t])

def ihK8 (vis t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m8) =>
    if r8.headD 0 = 0 then none else ihK9 (stubM "consts_resolve_ffast" m8 [vis, t])

def ihK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r9, m9) => if r9.headD 0 = 0 then none else some ([0], m9)
end

section arms
variable (n : Nat) (m m1 m3 m4 m6 m7 m8 m9 : Mem) (vis q x t : Word) (c d : Word)
  (r1 r3 r4 r6 r7 r8 r9 : List Word)
theorem ihW_step : ihW (n + 1) m vis q =
    ihK1 n vis q (rdW (m.arr64 EREC) q) (rdW (m.arr64 EREC) (q + 3))
      (envFindW m (rdW (m.arr64 EREC) q) vis) := rfl
theorem ihK1_some : ihK1 n vis q x t (some (r1, m1)) =
    if r1.headD 0 ≠ 0 then none else ihK2 n vis q x t m1 (resContW n m1 x) := rfl
theorem ihK2_some : ihK2 n vis q x t m1 (some c) =
    if c ≠ 0 then none else ihK3 n vis q t (ipfF m1 [x]) := rfl
theorem ihK3_some : ihK3 n vis q t (some (r3, m3)) =
    if r3.headD 0 ≠ 0 then none else ihK4 n vis t (cvLpsW n m3 q) := rfl
theorem ihK4_some : ihK4 n vis t (some (r4, m4)) =
    ihK5 vis t r4 m4 (nodupW n m4 (r4.headD 0) (r4.tail.headD 0)) := rfl
theorem ihK5_some : ihK5 vis t r4 m4 (some d) =
    if d = 0 then none
    else ihK6 vis t r4 (stubM "loose_bvars_bounded_fast" m4 [4000000000, 0, t]) := rfl
theorem ihK6_some : ihK6 vis t r4 (some (r6, m6)) =
    if r6.headD 0 = 0 then none else ihK7 vis t r4 (stubM "has_fvar_fast" m6 [4000000000, t]) :=
  rfl
theorem ihK7_some : ihK7 vis t r4 (some (r7, m7)) =
    if r7.headD 0 ≠ 0 then none
    else ihK8 vis t (stubM "all_level_params_defined" m7 [r4.headD 0, r4.tail.headD 0, t]) := rfl
theorem ihK8_some : ihK8 vis t (some (r8, m8)) =
    if r8.headD 0 = 0 then none else ihK9 (stubM "consts_resolve_ffast" m8 [vis, t]) := rfl
theorem ihK9_some : ihK9 (some (r9, m9)) = if r9.headD 0 = 0 then none else some ([0], m9) := rfl
end arms

grind_pattern [ind_grind] ihW_step => ihW (n + 1) m vis q
grind_pattern [ind_grind] ihK1_some => ihK1 n vis q x t (some (r1, m1))
grind_pattern [ind_grind] ihK2_some => ihK2 n vis q x t m1 (some c)
grind_pattern [ind_grind] ihK3_some => ihK3 n vis q t (some (r3, m3))
grind_pattern [ind_grind] ihK4_some => ihK4 n vis t (some (r4, m4))
grind_pattern [ind_grind] ihK5_some => ihK5 vis t r4 m4 (some d)
grind_pattern [ind_grind] ihK6_some => ihK6 vis t r4 (some (r6, m6))
grind_pattern [ind_grind] ihK7_some => ihK7 vis t r4 (some (r7, m7))
grind_pattern [ind_grind] ihK8_some => ihK8 vis t (some (r8, m8))
grind_pattern [ind_grind] ihK9_some => ihK9 (some (r9, m9))

theorem ih_specW (p : Prog) (h : IhProg p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_header" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ihW n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ih]
  simp only [callFn, installHeaderL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p h.ix h.rowGet h.find n, resCont_spec p h.resF h.resC n,
        cvLps_specW p h.alloc h.copy h.eti h.lps n, slNodup_spec p h.cont h.nodup n,
        ipfF_spec p h.ipf n,
        stubM_spec p "loose_bvars_bounded_fast" n, stubM_spec p "has_fvar_fast" n,
        stubM_spec p "all_level_params_defined" n, stubM_spec p "consts_resolve_ffast" n] <;>
      finish (gen := 20)

/-! ## The relational lemma -/

/-- **`install_header` refines `installHeader`** at the model level. The record `q` is below the
record pool's top (`erecP`), so it survives the stub calls before `cv_lps`. -/
theorem ihW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : ihW n m vis q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) :
    ∃ a', (installHeader fe cv).run a = .ok ((), a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  have hq0 : decCV (erA m) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt (IWGrow.refl m)) hq
  obtain ⟨wx, hwx, hwxl, hname⟩ := decCV_name hq0
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hq0
  have ex : rdW (m.arr64 EREC) q = wx := rdW_of_get? rfl hwx
  have et : rdW (m.arr64 EREC) (q + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hwt
  cases n with
  | zero => simp [ihW] at h
  | succ n =>
  rw [ihW_step, ex, et] at h
  -- `env_find(x, vis)`
  cases h1 : envFindW m wx vis with
  | none => rw [h1] at h; simp [ihK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ihK1_some] at h
  by_cases hb1 : r1.headD 0 ≠ 0
  · rw [if_pos hb1] at h; simp at h
  rw [if_neg hb1] at h
  obtain ⟨rfl, hfind⟩ := envFindW_miss h1 hS.1.env hwxl (by simpa using hb1)
  -- `reserved_contains(x)`
  cases h2 : resContW n m1 wx with
  | none => rw [h2] at h; simp [ihK2] at h
  | some c =>
  rw [h2, ihK2_some] at h
  by_cases hb2 : c ≠ 0
  · rw [if_pos hb2] at h; simp at h
  rw [if_neg hb2] at h
  have hc0 : c = 0 := by simpa using hb2
  subst hc0
  obtain ⟨rl, hrunR, hrl⟩ := resContW_miss hwxl h2 hS.1.pins
  -- `is_proj_fn_shape(x)`
  cases h3 : ipfF m1 [wx] with
  | none => rw [h3] at h; simp [ihK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, ihK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    ipfF_ok dn vis fe wx hwxl m1 m3 a r3 h3 hS
  by_cases hb3 : r3.headD 0 ≠ 0
  · rw [if_pos hb3] at h; simp at h
  rw [if_neg hb3] at h
  -- `cv_lps(q)`
  have hq3 : decCV (erA m3) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg3) hq
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq3
  have e1 : rdW (m3.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m3.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m3.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => simp [cvLpsW, ihK4] at h
  | succ n =>
  rw [cvLpsW_step, e1, e2] at h
  cases h4 : erToIwW n m3 w1 w2 with
  | none => rw [h4] at h; simp [ihK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, ihK4_some] at h
  obtain ⟨-, hr4t, hdec4, hS4, hg4, htop4⟩ := erToIwW_stage h4 hS3 hsrc
  rw [hr4t] at h
  have hdecL : decHL m4 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [hdec4]; exact hsl
  -- `sl_nodup(o, l)`
  cases h5 : nodupW (n + 1) m4 (r4.headD 0) w2 with
  | none => rw [h5] at h; simp [ihK5] at h
  | some d =>
  rw [h5, ihK5_some] at h
  by_cases hb5 : d = 0
  · rw [if_pos hb5] at h; simp at h
  rw [if_neg hb5] at h
  have htopb : iwTop m4 < 2 ^ 64 := by simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws, hws, hlps, hwsl⟩ := slR_of_decHL m4 _ _ _ hdecL (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  have hd := nodupW_ok _ _ _ _ _ _ hws h5
  have hnd : nameNodup cv.levelParams = true := by
    rw [hlps, nameNodup_map ws hwsl]
    by_cases hn : ws.Nodup
    · simp [hn]
    · simp [hn] at hd; exact absurd hd hb5
  -- the four walks, as in `ivgW_ok`
  cases h6 : stubM "loose_bvars_bounded_fast" m4 [4000000000, 0, wt] with
  | none => rw [h6] at h; simp [ihK6] at h
  | some rm6 =>
  obtain ⟨r6, m6⟩ := rm6
  rw [h6, ihK6_some] at h
  obtain ⟨x6, a6, hrun6, hS6, hg6, hx6, -⟩ :=
    looseBVarsBoundedFast_spec dn vis fe 4000000000 0 wt hwtl m4 m6 a3 r6 h6 hS4
  by_cases hb6 : r6.headD 0 = 0
  · rw [if_pos hb6] at h; simp at h
  rw [if_neg hb6] at h
  cases h7 : stubM "has_fvar_fast" m6 [4000000000, wt] with
  | none => rw [h7] at h; simp [ihK7] at h
  | some rm7 =>
  obtain ⟨r7, m7⟩ := rm7
  rw [h7, ihK7_some] at h
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7, -⟩ :=
    hasFvarFast_spec dn vis fe 4000000000 wt hwtl m6 m7 a6 r7 h7 hS6
  by_cases hb7 : r7.headD 0 ≠ 0
  · rw [if_pos hb7] at h; simp at h
  rw [if_neg hb7, hr4t] at h
  cases h8 : stubM "all_level_params_defined" m7 [r4.headD 0, w2, wt] with
  | none => rw [h8] at h; simp [ihK8] at h
  | some rm8 =>
  obtain ⟨r8, m8⟩ := rm8
  rw [h8, ihK8_some] at h
  have hdec7 : decHL m7 (r4.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg6.trans hg7) (by omega), hdecL]
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8, -⟩ :=
    allLevelParamsDefined_spec dn vis fe (r4.headD 0) w2 wt hwtl cv.levelParams m7 m8 a7 r8 h8
      ⟨hS7, hdec7⟩
  by_cases hb8 : r8.headD 0 = 0
  · rw [if_pos hb8] at h; simp at h
  rw [if_neg hb8] at h
  cases h9 : stubM "consts_resolve_ffast" m8 [vis, wt] with
  | none => rw [h9] at h; simp [ihK9] at h
  | some rm9 =>
  obtain ⟨r9, m9⟩ := rm9
  rw [h9, ihK9_some] at h
  obtain ⟨x9, a9, hrun9, hS9, hg9, hx9, -⟩ :=
    constsResolveFFast_spec dn vis fe wt hwtl m8 m9 a8 r9 h9 hS8
  by_cases hb9 : r9.headD 0 = 0
  · rw [if_pos hb9] at h; simp at h
  rw [if_neg hb9] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have ex3 : x3 = false := by rw [← hx3]; simpa using hb3
  have ex6 : x6 = true := by rw [← hx6]; simpa using hb6
  have ex7 : x7 = false := by rw [← hx7]; simpa using hb7
  have ex8 : x8 = true := by rw [← hx8]; simpa using hb8
  have ex9 : x9 = true := by rw [← hx9]; simpa using hb9
  rw [fuelW] at hrun6 hrun7
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun6
  rw [← hname] at hfind hrun3 hrl
  rw [← hty] at hrun6 hrun7 hrun8 hrun9
  refine ⟨a9, ?_, hS9, hg3.trans (hg4.trans (hg6.trans (hg7.trans (hg8.trans hg9))))⟩
  simp only [installHeader, StateT.run_bind, hfind, Option.isSome_none, Bool.false_eq_true,
    if_false, hrunR, exc_ok_bind', hrl, hrun3, ex3, hnd, hrun6, ex6, hrun7, ex7, hrun8, ex8,
    hrun9, ex9, if_true, StateT.run_pure]
  rfl

/-- **`install_header` refines `installHeader`**: from the stage relation, with the constant
value `q` a record below the pool's top, a returning run is a successful twin run, the stage
relation holds after it, and the pool only grew. -/
@[refines ConRon.Arena.installHeader]
theorem installHeader_refines (p : Prog) (hp : IhProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q : Word) (cv : IConstantVal)
    (hStage : StageR dn vis fe s₀.mem a₀) (hq : decCV (erecP s₀.mem) q.toNat = some cv)
    (hqb : q.toNat + 3 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_header" [vis, q]
    ⦃fun _r s' => LocEq s' s₀ ∧ AM.ok (installHeader fe cv) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (installHeader fe cv) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (ih_specW p hp n s₀ vis q) ?_
  rintro _r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hStage', hg⟩ := ihW_ok hm hStage hq hqb
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hStage', hg⟩

end L.Arena
