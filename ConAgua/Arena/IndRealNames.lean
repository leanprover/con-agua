import ConAgua.Arena.CallF
import ConAgua.Arena.StubNames
import ConAgua.Arena.RecSim
import ConAgua.Front.ApplyExprRefine
import ConAgua.Arena.DeclMasterStage
import ConAgua.Arena.StageInst1
import ConAgua.Arena.LevelInternRef
import ConAgua.Arena.PromoteLsRef
import ConAgua.Arena.InstLPRef
import ConAgua.Arena.WhnfProjRefine

/-!
# Name and level-list interning stubs discharged (lane `indproofs4`, helper `indproofs4-names`)

The recipe of `IndReal.lean` (`callF` models, `relW_callF`-style facts) for the stage's name and
level-list interning callees. Their owners proved them under `ArenaR` (master's `intern_*`
refinements); here they are related under the stage relation `StageR`, by the store-growth lemmas
the stage already uses (`internNAnon_stage`, `StageR.of_walk`, `ArenaD.grow`).

* `intern_nanon` (`naF`): master's `nainternW` (`internNAnon_spec`) and `internNAnon_stage`; the
  handle is below `2^32` by the store relation (`consInternM_lt`: a hit is a node below the tier's
  count, an append the count itself, both below `2^27`).
-/

set_option linter.deprecated false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## A handle an `intern_*` model returns is below `2^32` -/

/-! ## `intern_nanon` (master's `internNAnon_spec`, `internNAnon_stage`) -/

/-- `intern_nanon` and its callees. -/
def naProg : Prog :=
  [("intern_nanon", internNAnon), ("nanon_find", nanonFind), ("nanon_push", nanonPush)]

def naFns : List FnName := naProg.map (·.1)

/-- `intern_nanon` writes the `anonymous` table and its counts. -/
theorem naProg_closed : closedA naProg [NAREC, NASLOT] [34, 35] naFns = true := by decide +kernel

/-- The program bundle. -/
abbrev NaF (p : Prog) : Prop := ProgHas p naProg

/-- **The model of `intern_nanon`.** -/
noncomputable def naF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF naProg "intern_nanon" m args

theorem naF_spec (p : Prog) (hp : NaF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "intern_nanon" args
    ⦃fun r s' => LocEq s' s₀ ∧ naF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec naProg_closed (hp.agree naFns) (by decide) n s₀ args

/-- `naF` is master's word model. -/
theorem naF_W {m m' : Mem} {r : List Word} (h : naF m [] = some (r, m')) :
    nainternW m = some (r.headD 0, m') := by
  obtain ⟨n, hc⟩ := callF_run h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internNAnon_spec naProg rfl rfl rfl n _) hc
  rw [← hs']; exact hW

/-- `nainternW`'s handle is below `2^32`. -/
theorem nainternW_lt {m m' : Mem} {a : AState} {w : Word} (hR : NAnonR m a)
    (hI : nainternW m = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt nanonCS_wf hR hI

/-- **`intern_nanon`'s model refines `internNNode .anonymous`** (replaces
`IndStubs.internNanonStub_spec`). -/
theorem naF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RelW naF [] (StageR dn vis fe) (internNNode .anonymous) (KeepPost dn vis fe decW0N) := by
  intro m m' a r hc hS
  have hW := naF_W hc
  obtain ⟨a', hrun, hS', hg, -, -⟩ := internNAnon_stage hS hW
  exact ⟨_, a', hrun, hS', hg, nainternW_lt hS.1.arena.1.nanon hW, rfl⟩

/-- `intern_nanon` writes the `anonymous` table only. -/
theorem naF_frame {m m' : Mem} {args r : List Word} (h : naF m args = some (r, m')) :
    MemFrame [NAREC, NASLOT] [34, 35] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame naProg_closed (by decide) (run_of_callW hc)).1

/-! ## Pool scratch: `pool_room`, `iw_pool`, and growing the pool above its top -/

/-- **The model of `pool_room(k)`**: `k` words reserved at the pool top. -/
def prW (m : Mem) (k : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 0 + k < rdW (m.arr64 CTL) 0 then none
  else if m.len64 POOL < rdW (m.arr64 CTL) 0 + k then none
  else some (rdW (m.arr64 CTL) 0, m.set64 CTL 0 (rdW (m.arr64 CTL) 0 + k))

theorem poolRoom_specW (p : Prog) (hp : p.lookup "pool_room" = some L.Stubs.poolRoom) (n : Nat)
    (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pool_room" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ prW s₀.mem k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.poolRoom]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
    finish [prW]

/-- No call returns at fuel `0`. -/
theorem callW_zero_false {p : Prog} {f : FnName} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p 0 f vs m = some (r, m')) : False := by
  obtain ⟨_, _, h'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_exec_zero p f vs (fun s => s = ⟨m, Locals.init []⟩)) h
  exact h'

theorem callW_pr {p : Prog} (hp : p.lookup "pool_room" = some L.Stubs.poolRoom) {n : Nat}
    {m m' : Mem} {k : Word} {r : List Word} (h : callW p n "pool_room" [k] m = some (r, m')) :
    prW m k = some (r.headD 0, m') := by
  cases n with
  | zero => exact (callW_zero_false h).elim
  | succ n =>
    obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (poolRoom_specW p hp n _ k) h
    rw [← hs']; exact hW

/-- `prW`, unfolded: the old top, the top raised. -/
theorem prW_some {m m' : Mem} {k o : Word} (h : prW m k = some (o, m')) :
    o = m.top ∧ m' = m.set64 CTL 0 (m.top + k) ∧ m.top.toNat + k.toNat < 2 ^ 64 ∧
      m.top.toNat + k.toNat ≤ (m.arr64 POOL).size := by
  simp only [prW] at h
  by_cases c1 : rdW (m.arr64 CTL) 0 + k < rdW (m.arr64 CTL) 0
  · rw [if_pos c1] at h; cases h
  rw [if_neg c1] at h
  by_cases c2 : m.len64 POOL < rdW (m.arr64 CTL) 0 + k
  · rw [if_pos c2] at h; cases h
  rw [if_neg c2] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have e : (rdW (m.arr64 CTL) 0 + k).toNat = (rdW (m.arr64 CTL) 0).toNat + k.toNat := add_nc _ _ c1
  have hno : (rdW (m.arr64 CTL) 0).toNat + k.toNat < 2 ^ 64 := by
    rw [← e]; exact UInt64.toNat_lt _
  have hs := mt UInt64.lt_iff_toNat_lt.mpr c2
  rw [len64_eq, e] at hs
  have ef : (UInt64.ofNat (m.arr64 POOL).size).toNat ≤ (m.arr64 POOL).size := by
    simp; omega
  refine ⟨rfl, rfl, hno, ?_⟩
  simp only [top_rdW]
  by_cases hb : (m.arr64 POOL).size < 2 ^ 64
  · have : (UInt64.ofNat (m.arr64 POOL).size).toNat = (m.arr64 POOL).size := by simp; omega
    omega
  · omega

/-- **A pool write above the original top** keeps a growth a growth. -/
theorem grows_set_above {m m' : Mem} (hg : Grows m m') {q x : Word} (hq : m.top.toNat ≤ q.toNat) :
    Grows m (m'.set64 POOL q x) := by
  obtain ⟨hfr, hag, ht1, ht2, hps⟩ := hg
  have htop' : (m'.set64 POOL q x).top = m'.top := by
    simp only [top_rdW, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide)]
  refine ⟨?_, fun j hj => ?_, by rw [htop']; exact ht1, by rw [htop', size_set64]; exact ht2,
    by rw [size_set64, hps]⟩
  · rw [htop']; exact Frame.set64 _ _ _ _ _ hfr
  · rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    have : ¬ q.toNat = j := by omega
    simp only [this, if_false]
    exact hag j hj

/-- **The model of `iw_pool(s, d, l)`**: `POOL[d + j] := IW[s + j]`. -/
def iwpW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, s, d, l =>
    if l = 0 then some m
    else iwpW n (m.set64 POOL d (rdW (m.arr64 IW) s)) (s + 1) (d + 1) (l - 1)

theorem iwpW_nil (n : Nat) (m : Mem) (s d l : Word) (h : l = 0) :
    iwpW (n + 1) m s d l = some m := by simp [iwpW, h]
theorem iwpW_cons (n : Nat) (m : Mem) (s d l : Word) (h : l ≠ 0) :
    iwpW (n + 1) m s d l = iwpW n (m.set64 POOL d (rdW (m.arr64 IW) s)) (s + 1) (d + 1) (l - 1) := by
  simp [iwpW, h]
grind_pattern [arena_grind] iwpW_nil => iwpW (n + 1) m s d l
grind_pattern [arena_grind] iwpW_cons => iwpW (n + 1) m s d l

theorem iwPool_specW (p : Prog) (hp : p.lookup "iw_pool" = some L.Stubs.iwPool) (n : Nat) :
    ∀ (s₀ : St) (s d l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "iw_pool" [s, d, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ iwpW n s₀.mem s d l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ s d l; rw [invoke_eq _ hp]; simp only [callFn, L.Stubs.iwPool]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ s d l
    rw [invoke_eq _ hp]
    simp only [callFn, L.Stubs.iwPool]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish

theorem callW_ip {p : Prog} (hp : p.lookup "iw_pool" = some L.Stubs.iwPool) {n : Nat}
    {m m' : Mem} {s d l : Word} {r : List Word} (h : callW p n "iw_pool" [s, d, l] m = some (r, m')) :
    iwpW n m s d l = some m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwPool_specW p hp n _ s d l) h
  rw [← hs']; exact hW

/-- **`iw_pool` copies the `IW` slice to the pool** above the top: a growth (given one), the
slice, nothing written below `d`, and nothing else written. -/
theorem iwpW_ok {m₀ : Mem} : ∀ (n : Nat) (m m' : Mem) (s d l : Word), iwpW n m s d l = some m' →
    Grows m₀ m → m₀.top.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 POOL).size →
    (m.arr64 POOL).size < 2 ^ 63 → s.toNat + l.toNat < 2 ^ 64 →
    Grows m₀ m' ∧ MemFrame [POOL] [] m m' ∧
      (∀ i : Word, i.toNat < d.toNat → rdW (m'.arr64 POOL) i = rdW (m.arr64 POOL) i) ∧
      sliceL (m'.arr64 POOL) d.toNat l.toNat = sliceL (m.arr64 IW) s.toNat l.toNat := by
  intro n
  induction n with
  | zero => intro m m' s d l h; simp [iwpW] at h
  | succ n ih =>
    intro m m' s d l h hg hd hdl hsz hs
    by_cases hl : l = 0
    · rw [iwpW_nil n m s d l hl] at h; cases h; subst hl
      exact ⟨hg, MemFrame.refl _ _ _, fun _ _ => rfl, by simp [sliceL]⟩
    rw [iwpW_cons n m s d l hl] at h
    have hl1 : 1 ≤ l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hl
      · omega
    have hd1 : (d + 1).toNat = d.toNat + 1 := toNat_succ_lt (by omega)
    have hs1 : (s + 1).toNat = s.toNat + 1 := toNat_succ_lt (by omega)
    have hlm : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hsz₁ : ((m.set64 POOL d (rdW (m.arr64 IW) s)).arr64 POOL).size = (m.arr64 POOL).size :=
      Mem.size_arr64_set64 _ _ _ _
    have hg₁ := grows_set_above hg (x := rdW (m.arr64 IW) s) hd
    obtain ⟨hg', hf, hbl, hsl⟩ := ih _ _ _ _ _ h hg₁ (by rw [hd1]; omega)
      (by rw [hsz₁, hd1, hlm]; omega) (by rw [hsz₁]; exact hsz) (by rw [hs1, hlm]; omega)
    refine ⟨hg', (MemFrame.set64 _ _ (by decide) _ _).trans hf, fun i hi => ?_, ?_⟩
    · rw [hbl i (by rw [hd1]; omega), rdW_set64]
      have : ¬ d = i := fun e => by subst e; omega
      simp [this]
    · obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
      rw [hk, sliceL_succ, sliceL_succ]
      have hiw : (m.set64 POOL d (rdW (m.arr64 IW) s)).arr64 IW = m.arr64 IW :=
        Mem.arr64_set64_ne _ _ _ _ _ (by decide)
      rw [hd1, hs1, hlm, hk, hiw] at hsl
      simp only [Nat.add_sub_cancel] at hsl
      rw [hsl]
      congr 1
      have e1 := hbl d (by rw [hd1]; omega)
      have e2 : rdW ((m.set64 POOL d (rdW (m.arr64 IW) s)).arr64 POOL) d = rdW (m.arr64 IW) s := by
        rw [rdW_set64]; simp [show d.toNat < (m.arr64 POOL).size by omega]
      simp only [rdW] at e1 e2 ⊢
      rw [e1, e2]

/-! ## `name_rec(n)` (the pool bytes `rec`, master's `intern_nstr`) -/

/-- `name_rec` and its callees. -/
def nrProg : Prog :=
  [("name_rec", L.Stubs.nameRecL), ("pool_room", L.Stubs.poolRoom), ("intern_nstr", internNStr),
   ("lit_hash", litHash), ("limbs_eq", limbsEq), ("nstr_match", nsMatch), ("nstr_find", nsFind),
   ("nstr_push", nsPush)]

def nrFns : List FnName := nrProg.map (·.1)

/-- `name_rec` writes the pool (and its top) and the `str` table. -/
theorem nrProg_closed : closedA nrProg [POOL, NSREC, NSSLOT] [0, 36, 37] nrFns = true := by
  decide +kernel

abbrev NrF (p : Prog) : Prop := ProgHas p nrProg

/-- **The model of `name_rec`.** -/
noncomputable def nrF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF nrProg "name_rec" m args

theorem nrF_spec (p : Prog) (hp : NrF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "name_rec" args
    ⦃fun r s' => LocEq s' s₀ ∧ nrF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec nrProg_closed (hp.agree nrFns) (by decide) n s₀ args

/-- The three bytes `rec` at `o`. -/
def recBytes (m : Mem) (o : Word) : Mem :=
  ((m.set64 POOL o 114).set64 POOL (o + 1) 101).set64 POOL (o + 2) 99

/-- `name_rec`'s body over its callees' runs. -/
def nrW (p : Prog) (n : Nat) (m : Mem) (x : Word) : Option (Word × Mem) :=
  match callW p n "pool_room" [3] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "intern_nstr" [x, r₁.headD 0, 3] (recBytes m₁ (r₁.headD 0)) with
    | none => none
    | some (r₂, m₂) => if 4294967296 ≤ r₂.headD 0 then none else some (r₂.headD 0, m₂)

theorem nameRec_specW (p : Prog) (hp : p.lookup "name_rec" = some L.Stubs.nameRecL) (n : Nat)
    (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "name_rec" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ nrW p n s₀.mem x = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.nameRecL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "pool_room", callW_spec p n "intern_nstr"] <;>
    finish [nrW, recBytes]

theorem strWords_recB : strWords "rec" = [114, 101, 99] := by decide

/-- **The bytes after the reserved room grow the pool and hold `rec`.** -/
theorem recBytes_ok (m : Mem) (hpool : PoolOK m) (hno : m.top.toNat + 3 < 2 ^ 64)
    (hs : m.top.toNat + 3 ≤ (m.arr64 POOL).size) :
    Grows m (recBytes (m.set64 CTL 0 (m.top + 3)) m.top) ∧
      SliceOK (recBytes (m.set64 CTL 0 (m.top + 3)) m.top) m.top 3 ∧
      sliceL ((recBytes (m.set64 CTL 0 (m.top + 3)) m.top).arr64 POOL) m.top.toNat 3 = strWords "rec" ∧
      ((recBytes (m.set64 CTL 0 (m.top + 3)) m.top).arr64 POOL).size = (m.arr64 POOL).size := by
  have hc := hpool.2.1
  have e1 : (m.top + 1).toNat = m.top.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (m.top + 2).toNat = m.top.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (m.top + 3).toNat = m.top.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have g0 := grows_top m (m.top + 3) hc (by omega) (by omega)
  have g1 := grows_set_above g0 (q := m.top) (x := 114) (Nat.le_refl _)
  have g2 := grows_set_above g1 (q := m.top + 1) (x := 101) (by omega)
  have g3 := grows_set_above g2 (q := m.top + 2) (x := 99) (by omega)
  have htop : (recBytes (m.set64 CTL 0 (m.top + 3)) m.top).top = m.top + 3 := by
    simp only [recBytes, top_rdW, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide)]
    exact Mem.top_set64 _ _ hc
  have hsz : ((recBytes (m.set64 CTL 0 (m.top + 3)) m.top).arr64 POOL).size = (m.arr64 POOL).size := by
    simp only [recBytes, size_set64]
  refine ⟨g3, by simp only [SliceOK, htop, e3]; simp, ?_, hsz⟩
  rw [strWords_recB]
  simp only [sliceL, recBytes, Mem.arr64_set64_ne _ _ _ _ _ (show POOL ≠ CTL by decide),
    Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, e1, e2,
    List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds]
  simp (config := { decide := true }) [show m.top.toNat < (m.arr64 POOL).size by omega,
    show m.top.toNat + 1 < (m.arr64 POOL).size by omega, show m.top.toNat + 2 < (m.arr64 POOL).size by omega]

/-- **`name_rec`'s model refines `internNNode (.str n "rec")`** (replaces `IndStubs.nameRec_spec`). -/
theorem nrF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x : Word) (hx : H x) :
    RelW nrF [x] (StageR dn vis fe) (internNNode (.str (decI x) "rec")) (KeepPost dn vis fe decW0N) := by
  intro m m' a r hc hS
  obtain ⟨n', hc'⟩ := callF_run hc
  cases n' with
  | zero => exact (callW_zero_false hc').elim
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (nameRec_specW nrProg rfl n _ x) hc'
  simp only at hs' hW
  rw [hs'] at hW
  unfold nrW at hW
  cases h1 : callW nrProg n "pool_room" [3] m with
  | none => rw [h1] at hW; cases hW
  | some q1 =>
  obtain ⟨r₁, m₁⟩ := q1
  rw [h1] at hW
  simp only at hW
  obtain ⟨ho, hm₁, hno, hroom⟩ := prW_some (callW_pr rfl h1)
  rw [ho, hm₁] at hW
  have hpool : PoolOK m := hS.1.arena.1.lit.1
  obtain ⟨hg, hsl, hk, hsz⟩ := recBytes_ok m hpool hno hroom
  generalize hm₂ : recBytes (m.set64 CTL 0 (m.top + 3)) m.top = m₂ at hW hg hsl hk hsz
  cases h2 : callW nrProg n "intern_nstr" [x, m.top, 3] m₂ with
  | none => rw [h2] at hW; cases hW
  | some q2 =>
  obtain ⟨r₂, m₃⟩ := q2
  rw [h2] at hW
  simp only at hW
  by_cases c : 4294967296 ≤ r₂.headD 0
  · rw [if_pos c] at hW; cases hW
  rw [if_neg c] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  have hR₂ : ArenaR m₂ a := ArenaR.grow m m₂ hg a hS.1.arena.1
  have hps : (m.arr64 POOL).size < 2 ^ 63 := hpool.2.2.1
  obtain ⟨s₃, hs₃, -, hok, hR₃, hres⟩ := triple_of_callW
    (internNStr_refinesA nrProg rfl rfl rfl rfl rfl rfl a n ⟨m₂, Locals.init []⟩ x m.top 3 hR₂ hx hsl
      "rec" hk) h2
  obtain ⟨s₃', hs₃', -, hI⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internNStr_spec nrProg rfl rfl rfl rfl rfl rfl n _ x m.top 3 (by simp only; omega)
      (by simp only; omega)) h2
  simp only at hs₃ hR₃ hs₃' hI
  rw [hs₃] at hR₃
  rw [hs₃'] at hI
  have hfr : MemFrame [POOL, NSREC, NSSLOT] [0, 36, 37] m m₃ :=
    ((grows_frame m m₂ hg).mono (by simp) (by simp)).trans
      ((consInternM_frame nstrCS_wf hI).mono (by simp [nstrCS]) (by simp [nstrCS]))
  obtain ⟨a', hrun, hS', hg', -, -⟩ := stage_of_name hS (internNNode_str_run (decI x) "rec" a) hok hR₃
    hres hfr (by simp [POOL, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
  rw [hr] at hrun c
  refine ⟨decI (r.headD 0), a', hrun, hS', hg', ?_, rfl⟩
  have := mt UInt64.le_iff_toNat_le.mpr c
  have e : (4294967296 : Word).toNat = 4294967296 := rfl
  rw [e] at this; omega

/-! ## `intern_ls_iw(o, l)` (the `IW` slice to the pool, master's `intern_ls`) -/

/-- `intern_ls_iw` and its callees. -/
def ilProg : Prog :=
  [("intern_ls_iw", L.Stubs.internLsIwL), ("pool_room", L.Stubs.poolRoom),
   ("iw_pool", L.Stubs.iwPool), ("intern_ls", internLs), ("lit_hash", litHash),
   ("limbs_eq", limbsEq), ("ls_match", lsMatch), ("ls_find", lsFind), ("ls_push", lsPush)]

def ilFns : List FnName := ilProg.map (·.1)

/-- `intern_ls_iw` writes the pool (and its top) and the list table with its column. -/
theorem ilProg_closed : closedA ilProg [POOL, LSREC, LSSLOT, LSHP] [0, 40, 41] ilFns = true := by
  decide +kernel

abbrev IlF (p : Prog) : Prop := ProgHas p ilProg

/-- **The model of `intern_ls_iw`.** -/
noncomputable def ilF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ilProg "intern_ls_iw" m args

theorem ilF_spec (p : Prog) (hp : IlF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "intern_ls_iw" args
    ⦃fun r s' => LocEq s' s₀ ∧ ilF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ilProg_closed (hp.agree ilFns) (by decide) n s₀ args

theorem ilF_frame {m m' : Mem} {args r : List Word} (h : ilF m args = some (r, m')) :
    MemFrame [POOL, LSREC, LSSLOT, LSHP] [0, 40, 41] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ilProg_closed (by decide) (run_of_callW hc)).1

/-- `intern_ls_iw`'s body over its callees' runs. -/
def ilwW (p : Prog) (n : Nat) (m : Mem) (o l : Word) : Option (Word × Mem) :=
  match callW p n "pool_room" [l] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "iw_pool" [o, r₁.headD 0, l] m₁ with
    | none => none
    | some (_, m₂) =>
      match callW p n "intern_ls" [r₁.headD 0, l] m₂ with
      | none => none
      | some (r₃, m₃) => if 4294967296 ≤ r₃.headD 0 then none else some (r₃.headD 0, m₃)

theorem internLsIw_specW (p : Prog) (hp : p.lookup "intern_ls_iw" = some L.Stubs.internLsIwL)
    (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "intern_ls_iw" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwW p n s₀.mem o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.internLsIwL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "pool_room", callW_spec p n "iw_pool", callW_spec p n "intern_ls"] <;>
    finish [ilwW]

/-- A decoded handle slice is the words of its list, inside the array. -/
theorem hslice_lsWords {a : Array Word} : ∀ (l o : Nat) (us : List LIdx), hslice? a o l = some us →
    sliceL a o l = lsWords us ∧ (0 < l → o + l ≤ a.size)
  | 0, o, us, h => by
    simp [hslice?] at h; subst h; simp [sliceL, lsWords]
  | l + 1, o, us, h => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    obtain ⟨ih, hb⟩ := hslice_lsWords l (o + 1) ys hys
    cases hw : a[o]? with
    | none => simp [hd?, hw] at hx
    | some w =>
    simp only [hd?, hw, bind, Option.bind_some] at hx
    by_cases hw32 : w.toNat < 2 ^ 32
    · rw [if_pos hw32] at hx
      cases hx
      have ho : o < a.size := (Array.getElem?_eq_some_iff.mp hw).1
      refine ⟨?_, fun _ => ?_⟩
      · rw [sliceL_succ, ih, hw]
        simp only [Option.getD_some, lsWords, List.map_cons, List.cons.injEq, and_true]
        exact ((word_decI _ w hw32).mpr rfl).symm
      · rcases Nat.eq_zero_or_pos l with h0 | h0
        · subst h0; omega
        · have := hb h0; omega
    · rw [if_neg hw32] at hx; cases hx

/-- **`intern_ls_iw`'s model refines `internLsNode us`** at the `IW` slice decoding to `us`
(replaces `IndStubs.internLsIw_spec`). -/
theorem ilF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (o l : Word)
    (us : List LIdx) :
    RelW ilF [o, l] (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some us)
      (internLsNode us) (KeepPost dn vis fe (fun _ r (x : LsIdx) => H (r.headD 0) ∧ decI (r.headD 0) = x)) := by
  rintro m m' a r hc ⟨hS, hd⟩
  obtain ⟨n', hc'⟩ := callF_run hc
  cases n' with
  | zero => exact (callW_zero_false hc').elim
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internLsIw_specW ilProg rfl n _ o l) hc'
  simp only at hs' hW
  rw [hs'] at hW
  unfold ilwW at hW
  cases h1 : callW ilProg n "pool_room" [l] m with
  | none => rw [h1] at hW; cases hW
  | some q1 =>
  obtain ⟨r₁, m₁⟩ := q1
  rw [h1] at hW
  simp only at hW
  obtain ⟨ho, hm₁, hno, hroom⟩ := prW_some (callW_pr rfl h1)
  rw [ho] at hW
  cases h2 : callW ilProg n "iw_pool" [o, m.top, l] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q2 =>
  obtain ⟨r₂, m₂⟩ := q2
  rw [h2] at hW
  simp only at hW
  cases h3 : callW ilProg n "intern_ls" [m.top, l] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q3 =>
  obtain ⟨r₃, m₃⟩ := q3
  rw [h3] at hW
  simp only at hW
  by_cases c : 4294967296 ≤ r₃.headD 0
  · rw [if_pos c] at hW; cases hW
  rw [if_neg c] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  have hpool : PoolOK m := hS.1.arena.1.lit.1
  have hc0 := hpool.2.1
  have hps : (m.arr64 POOL).size < 2 ^ 63 := hpool.2.2.1
  have htl : (m.top + l).toNat = m.top.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have g0 : Grows m m₁ := by rw [hm₁]; exact grows_top m _ hc0 (by omega) (by omega)
  have hpsz₁ : (m₁.arr64 POOL).size = (m.arr64 POOL).size := by rw [hm₁, size_set64]
  have hiw₁ : m₁.arr64 IW = m.arr64 IW := by rw [hm₁, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨hsl, hb⟩ := hslice_lsWords l.toNat o.toNat us hd
  have hIW := hS.2.2.2.1
  have hol : o.toNat + l.toNat < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · rw [h0]; exact Nat.lt_of_lt_of_le (UInt64.toNat_lt o) (by omega)
    · have := hb h0; simp only [iwA] at this; omega
  obtain ⟨hg, hf₂, -, hsl₂⟩ := iwpW_ok n m₁ m₂ o m.top l (callW_ip rfl h2) g0 (Nat.le_refl _)
    (by rw [hpsz₁]; exact hroom) (by rw [hpsz₁]; exact hps) hol
  rw [hiw₁] at hsl₂
  have hpsz₂ : (m₂.arr64 POOL).size = (m.arr64 POOL).size := by rw [hf₂.2.2.1 POOL, hpsz₁]
  have htop₂ : m₂.top = m.top + l := by
    have e := hf₂.2.1 0 (by simp)
    simp only [top_rdW] at e ⊢
    rw [e, hm₁]; exact Mem.top_set64 _ _ hc0
  have hA₂ : ArenaD m₂ a := ArenaD.grow m m₂ hg a hS.1.arena
  obtain ⟨s₃, hs₃, -, hI⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internLs_spec ilProg rfl rfl rfl rfl rfl rfl n _ m.top l (by simp only; omega)
      (by simp only; omega)) h3
  simp only at hs₃ hI
  rw [hs₃] at hI
  obtain ⟨ok, hA₃, res, hf₃⟩ := L.Front.internLs_D m₂ a hA₂ (r₃.headD 0) m₃ m.top l
    (by show m.top.toNat + l.toNat ≤ m₂.top.toNat; rw [htop₂, htl]; exact Nat.le_refl _)
    us (by rw [hsl₂]; simpa [iwA] using hsl) hI
  have hrun := AM.run_of_ok _ _ ok
  rw [res] at hrun
  obtain ⟨hca, hpi, -⟩ := internLsNode_keep _ _ _ _ hrun
  have hfr : MemFrame [POOL, LSREC, LSSLOT, LSHP] [0, 40, 41] m m₃ :=
    ((grows_frame m m₂ hg).mono (by simp) (by simp)).trans
      (hf₃.mono (by simp [lsSch]) (by simp [lsSch]))
  obtain ⟨hS', hg'⟩ := StageR.of_walk hS hA₃ hfr (by simp [POOL, LSREC, LSSLOT, LSHP]) (by simp)
    (by simp only [cp, hca, hpi])
  rw [hr] at hrun c
  refine ⟨_, _, hrun, hS', hg', ?_, rfl⟩
  have := mt UInt64.le_iff_toNat_le.mpr c
  have e : (4294967296 : Word).toNat = 4294967296 := rfl
  rw [e] at this; show (r.headD 0).toNat < 2 ^ 32; omega

/-! ## `proj_table_name(T)` (the bytes `projTable`, master's `intern_nstr`, `intern_nnum`) -/

/-- `nninternW`'s handle is below `2^32`. -/
theorem nninternW_lt {m m' : Mem} {a : AState} {pre u w : Word} (hR : NNumR m a)
    (hI : nninternW m pre u = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt nnumCS_wf hR hI

/-- `proj_table_name` and its callees. -/
def ptProg : Prog :=
  [("proj_table_name", projTableNameL), ("intern_nstr", internNStr), ("lit_hash", litHash),
   ("limbs_eq", limbsEq), ("nstr_match", nsMatch), ("nstr_find", nsFind), ("nstr_push", nsPush),
   ("intern_nnum", internNNum), ("nnum_find", nnumFind), ("nnum_push", nnumPush)]

def ptFns : List FnName := ptProg.map (·.1)

/-- `proj_table_name` writes the pool (and its top) and the `str` and `num` tables. -/
theorem ptProg_closed :
    closedA ptProg [POOL, NSREC, NSSLOT, NNREC, NNSLOT] [0, 36, 37, 38, 39] ptFns = true := by
  decide +kernel

abbrev PtF (p : Prog) : Prop := ProgHas p ptProg

/-- **The model of `proj_table_name`.** -/
noncomputable def ptF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ptProg "proj_table_name" m args

theorem ptF_spec (p : Prog) (hp : PtF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "proj_table_name" args
    ⦃fun r s' => LocEq s' s₀ ∧ ptF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ptProg_closed (hp.agree ptFns) (by decide) n s₀ args

theorem ptF_frame {m m' : Mem} {args r : List Word} (h : ptF m args = some (r, m')) :
    MemFrame [POOL, NSREC, NSSLOT, NNREC, NNSLOT] [0, 36, 37, 38, 39] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ptProg_closed (by decide) (run_of_callW hc)).1

/-- `ptnW_spec` from the one lookup. -/
theorem ptnW_spec' (p : Prog) (hp : p.lookup "proj_table_name" = some projTableNameL) (n : Nat)
    (s₀ : St) (t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_table_name" [t]
    ⦃fun r s' => LocEq s' s₀ ∧ ptnW p n s₀.mem t = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, projTableNameL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "intern_nstr", callW_spec p n "intern_nnum"] <;>
    finish [ptnW, ptMem, ptBytes]

/-- **`proj_table_name`'s model refines `projTableName`** under the stage relation (replaces
`IndStubs.projTableName_spec`; lane `whnf`'s `projTableName_refines` is under `CoreS`). -/
theorem ptF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (t : Word) (ht : H t) :
    RelW ptF [t] (StageR dn vis fe) (projTableName (decI t)) (KeepPost dn vis fe decW0N) := by
  intro m m' a r hc hS
  obtain ⟨n', hc'⟩ := callF_run hc
  cases n' with
  | zero => exact (callW_zero_false hc').elim
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ptnW_spec' ptProg rfl n _ t) hc'
  simp only at hs' hW
  rw [hs'] at hW
  unfold ptnW at hW
  by_cases c1 : 4294967295 < t
  · rw [if_pos c1] at hW; cases hW
  rw [if_neg c1] at hW
  by_cases c2 : (2 : Word) < (t >>> 28)
  · rw [if_pos c2] at hW; cases hW
  rw [if_neg c2] at hW
  by_cases c3 : ((t >>> 27) &&& 1) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [if_pos c3] at hW; cases hW
  rw [if_neg c3] at hW
  by_cases c4 : rdW (m.arr64 CTL) ((34 : Word) + (t >>> (28 : Word)) * (2 : Word) +
      ((t >>> (27 : Word)) &&& 1)) ≤ (t &&& 134217727)
  · rw [if_pos c4] at hW; cases hW
  rw [if_neg c4] at hW
  by_cases c5 : rdW (m.arr64 CTL) 0 + 9 < rdW (m.arr64 CTL) 0
  · rw [if_pos c5] at hW; cases hW
  rw [if_neg c5] at hW
  by_cases c6 : m.len64 POOL < rdW (m.arr64 CTL) 0 + 9
  · rw [if_pos c6] at hW; cases hW
  rw [if_neg c6] at hW
  have hpool : PoolOK m := hS.1.arena.1.lit.1
  obtain ⟨hctl, hc0, hps, htop⟩ := hpool
  generalize ho : rdW (m.arr64 CTL) 0 = o at hW c5 c6
  have hot : o = m.top := ho.symm
  have ef : (UInt64.ofNat (m.arr64 POOL).size).toNat = (m.arr64 POOL).size := by
    simp; omega
  have hno : o.toNat + 9 < 2 ^ 64 := by
    have := mt UInt64.lt_iff_toNat_lt.mpr c5
    rw [UInt64.toNat_add] at this; simp at this; omega
  have h9 : (o + 9).toNat = o.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have hsz : o.toNat + 9 ≤ (m.arr64 POOL).size := by
    have := mt UInt64.lt_iff_toNat_lt.mpr c6
    rw [len64_eq, ef, h9] at this
    omega
  have hg : Grows m (ptMem m o) := by
    rw [hot]; exact grows_ptMem m ⟨hctl, hc0, hps, htop⟩ (by rw [← hot]; omega) (by rw [← hot]; omega)
  have hR1 : ArenaR (ptMem m o) a := ArenaR.grow m _ hg a hS.1.arena.1
  have hm1top : (ptMem m o).top = o + 9 := Mem.top_set64 _ _ (by rw [ptBytes_ctl]; exact hc0)
  have hsl : SliceOK (ptMem m o) o 9 := by
    simp only [SliceOK, hm1top, h9]; simp
  have hpsz : ((ptMem m o).arr64 POOL).size = (m.arr64 POOL).size := by
    simp only [ptMem, ptBytes, size_set64]
  have hk := ptMem_slice m o hno hsz
  cases hc1 : callW ptProg n "intern_nstr" [t, o, 9] (ptMem m o) with
  | none => rw [hc1] at hW; cases hW
  | some q1 =>
  obtain ⟨r₁, m₂⟩ := q1
  rw [hc1] at hW
  simp only at hW
  by_cases c7 : 4294967296 ≤ r₁.headD 0
  · rw [if_pos c7] at hW; cases hW
  rw [if_neg c7] at hW
  obtain ⟨s₂, hs₂, -, hok1, hR2, hres1⟩ := triple_of_callW
    (internNStr_refinesA ptProg rfl rfl rfl rfl rfl rfl a n ⟨ptMem m o, Locals.init []⟩ t o 9 hR1 ht
      hsl "projTable" hk) hc1
  obtain ⟨s₂', hs₂', -, hW1⟩ := triple_of_callW (s₀ := ⟨ptMem m o, Locals.init []⟩)
    (internNStr_spec ptProg rfl rfl rfl rfl rfl rfl n _ t o 9 (by simp only; omega)
      (by simp only; rw [hpsz]; simpa using hsz)) hc1
  simp only at hs₂ hR2 hs₂' hW1
  rw [hs₂] at hR2
  rw [hs₂'] at hW1
  have hfr : MemFrame [POOL, NSREC, NSSLOT] [0, 36, 37] m m₂ :=
    ((grows_frame m _ hg).mono (by simp) (by simp)).trans
      ((consInternM_frame nstrCS_wf hW1).mono (by simp [nstrCS]) (by simp [nstrCS]))
  obtain ⟨a1, hrun1, hS1, hg1, -, -⟩ := stage_of_name hS (internNNode_str_run (decI t) "projTable" a)
    hok1 hR2 hres1 hfr (by simp [POOL, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
  have hr1 : (r₁.headD 0).toNat < 2 ^ 32 := by
    have := mt UInt64.le_iff_toNat_le.mpr c7
    have e : (4294967296 : Word).toNat = 4294967296 := rfl
    rw [e] at this; omega
  cases hc2 : callW ptProg n "intern_nnum" [r₁.headD 0, 0] m₂ with
  | none => rw [hc2] at hW; cases hW
  | some q2 =>
  obtain ⟨r₂, m₃⟩ := q2
  rw [hc2] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  obtain ⟨s₃, hs₃, -, hW2⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internNNum_spec ptProg rfl rfl rfl n _ (r₁.headD 0) 0) hc2
  simp only at hs₃ hW2
  rw [hs₃] at hW2
  obtain ⟨a2, hrun2, hS2, hg2, -, -⟩ := internNNum_stage hS1 (r₁.headD 0) 0 hr1 hW2
  rw [hr] at hrun2 hW2
  refine ⟨decI (r.headD 0), a2, ?_, hS2, hg1.trans hg2, nninternW_lt hS1.1.arena.1.nnum hW2, rfl⟩
  simp only [projTableName, StateT.run_bind, hrun1]
  exact hrun2

end L.Ind
