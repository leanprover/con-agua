import ConAgua.Arena.CallF
import ConAgua.Arena.StubNames
import ConAgua.Arena.RecSim
import ConAgua.Front.ApplyExprRefine
import ConAgua.Arena.DeclMasterStage
import ConAgua.Arena.StageInst1
import ConAgua.Arena.LevelInternRef
import ConAgua.Arena.PromoteLsRef

/-!
# Name and level-list interning stubs discharged (lane `indproofs4`, helper `indproofs4-names`)

The recipe of `IndReal.lean` (`callF` models, `relW_callF`-style facts) for the stage's name and
level-list interning callees. Their owners proved them under `ArenaR` (master's `intern_*`
refinements); here they are related under the stage relation `StageR`, by the store-growth lemmas
the stage already uses (`internNAnon_stage`, `StageR.of_walk`, `ArenaD.grow`).

* `intern_nanon` (`naF`): master's `nainternW` (`internNAnon_spec`) and `internNAnon_stage`; the
  handle is below `2^32` by the store relation (`internM_lt`: a hit is a node below the tier's
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

theorem hdW_lt (tag : UInt32) (htag : tag.toNat < 16) (t i : Word) (ht : t ≤ 1)
    (hi : i.toNat < 2 ^ 27) : (hdW tag.toUInt64 t i).toNat < 2 ^ 32 := by
  have ht' : t.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp ht
  have htg : tag.toUInt64.toNat = tag.toNat := UInt32.toNat_toUInt64 tag
  simp only [hdW, UInt64.toNat_add, UInt64.toNat_mul, htg]
  simp only [UInt64.reduceToNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

section lt
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)

/-- A hit of a probe of tier `t` is a node below the tier's count, so below `2^27`. -/
theorem probe_hit_lt {m : Mem} {t : Word} {tb : Tbl α (Idx k) δ} (hT : TierR S R hs m t tb)
    {mt : Word → Bool} {x : Word} {rs : List Word} (hP : ProbeOKG S m t mt x rs) (hr : rs ≠ [])
    (hh : rs.headD 0 ≠ 0) : (rs.tail.headD 0).toNat < 2 ^ 27 := by
  obtain ⟨hm, hs1, hs2, hj⟩ := (hP hr).1 hh
  obtain ⟨-, hcap, -, -, -, -, ⟨hsl, -⟩⟩ := hT
  have h1 := hsl _ hj
  have hi : (rs.tail.headD 0).toNat < tb.nodes.size := by grind
  omega

/-- **An `intern_*` model's handle is below `2^32`**, from the store relation. -/
theorem internM_lt (hS : S.WF) {m : Mem} {on : Bool} {tbP tbS : Tbl α (Idx k) δ}
    (hR : StoreR S R hs m on tbP tbS) {sk : Word} {pk : Word → Bool} {vs rs₀ rs₁ : List Word}
    {mt₀ mt₁ : Word → Bool} {x₀ x₁ : Word} (hP0 : ProbeOKG S m 0 mt₀ x₀ rs₀)
    (hP1 : ProbeOKG S m 1 mt₁ x₁ rs₁) (hpk : ∀ t, pk t = true → PushRoom S m t) {w : Word}
    {m' : Mem} (hI : internM S m sk pk vs rs₀ rs₁ = some (w, m')) : w.toNat < 2 ^ 32 := by
  obtain ⟨-, -, hT0, hT1⟩ := hR
  have htag := hS.tag
  simp only [internM] at hI
  split at hI
  · simp at hI
  split at hI
  · rename_i _ h
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    rw [← hI.1]
    exact hdW_lt _ htag _ _ (by decide)
      (probe_hit_lt S R hs hT0 hP0 (by grind) h.2)
  split at hI
  · split at hI
    · simp at hI
    split at hI
    · rename_i _ _ h1
      simp only [Option.some.injEq, Prod.mk.injEq] at hI
      rw [← hI.1]
      exact hdW_lt _ htag _ _ (by decide) (probe_hit_lt S R hs hT1 hP1 ‹_› h1)
    split at hI
    · rename_i h
      simp only [Option.some.injEq, Prod.mk.injEq] at hI
      rw [← hI.1]
      exact hdW_lt _ htag _ _ (by decide) (hpk 1 h).1
    · simp at hI
  split at hI
  · rename_i h
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    rw [← hI.1]
    exact hdW_lt _ htag _ _ (by decide) (hpk 0 h).1
  · simp at hI

end lt

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
  rw [nainternW_eq] at hI
  exact internM_lt nanonSch NaRecRel nahash nanonSch_wf hR
    (probe_homeG nanonSch m 0 _ _ (naprobeW_arm m 0) _)
    (probe_homeG nanonSch m 1 _ _ (naprobeW_arm m 1) _) (napushOK_room m) hI

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
theorem callW_zero {p : Prog} {f : FnName} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p 0 f vs m = some (r, m')) : False := by
  obtain ⟨_, _, h'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (invoke_exec_zero p f vs (fun s => s = ⟨m, Locals.init []⟩)) h
  exact h'

theorem callW_pr {p : Prog} (hp : p.lookup "pool_room" = some L.Stubs.poolRoom) {n : Nat}
    {m m' : Mem} {k : Word} {r : List Word} (h : callW p n "pool_room" [k] m = some (r, m')) :
    prW m k = some (r.headD 0, m') := by
  cases n with
  | zero => exact (callW_zero h).elim
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
def ipW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, s, d, l =>
    if l = 0 then some m
    else ipW n (m.set64 POOL d (rdW (m.arr64 IW) s)) (s + 1) (d + 1) (l - 1)

theorem ipW_nil (n : Nat) (m : Mem) (s d l : Word) (h : l = 0) :
    ipW (n + 1) m s d l = some m := by simp [ipW, h]
theorem ipW_cons (n : Nat) (m : Mem) (s d l : Word) (h : l ≠ 0) :
    ipW (n + 1) m s d l = ipW n (m.set64 POOL d (rdW (m.arr64 IW) s)) (s + 1) (d + 1) (l - 1) := by
  simp [ipW, h]
grind_pattern [arena_grind] ipW_nil => ipW (n + 1) m s d l
grind_pattern [arena_grind] ipW_cons => ipW (n + 1) m s d l

theorem iwPool_specW (p : Prog) (hp : p.lookup "iw_pool" = some L.Stubs.iwPool) (n : Nat) :
    ∀ (s₀ : St) (s d l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "iw_pool" [s, d, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ ipW n s₀.mem s d l = some s'.mem; ⊤⦄ := by
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
    ipW n m s d l = some m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwPool_specW p hp n _ s d l) h
  rw [← hs']; exact hW

/-- **`iw_pool` copies the `IW` slice to the pool** above the top: a growth (given one), the
slice, nothing written below `d`, and nothing else written. -/
theorem ipW_ok {m₀ : Mem} : ∀ (n : Nat) (m m' : Mem) (s d l : Word), ipW n m s d l = some m' →
    Grows m₀ m → m₀.top.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 POOL).size →
    (m.arr64 POOL).size < 2 ^ 63 → s.toNat + l.toNat < 2 ^ 64 →
    Grows m₀ m' ∧ MemFrame [POOL] [] m m' ∧
      (∀ i : Word, i.toNat < d.toNat → rdW (m'.arr64 POOL) i = rdW (m.arr64 POOL) i) ∧
      sliceL (m'.arr64 POOL) d.toNat l.toNat = sliceL (m.arr64 IW) s.toNat l.toNat := by
  intro n
  induction n with
  | zero => intro m m' s d l h; simp [ipW] at h
  | succ n ih =>
    intro m m' s d l h hg hd hdl hsz hs
    by_cases hl : l = 0
    · rw [ipW_nil n m s d l hl] at h; cases h; subst hl
      exact ⟨hg, MemFrame.refl _ _ _, fun _ _ => rfl, by simp [sliceL]⟩
    rw [ipW_cons n m s d l hl] at h
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

theorem nrF_frame {m m' : Mem} {args r : List Word} (h : nrF m args = some (r, m')) :
    MemFrame [POOL, NSREC, NSSLOT] [0, 36, 37] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame nrProg_closed (by decide) (run_of_callW hc)).1

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

theorem strWords_rec : strWords "rec" = [114, 101, 99] := by decide

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
  rw [strWords_rec]
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
  | zero => exact (callW_zero hc').elim
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
  rw [nsinternW_eq] at hI
  have hfr : MemFrame [POOL, NSREC, NSSLOT] [0, 36, 37] m m₃ :=
    ((grows_frame m m₂ hg).mono (by simp) (by simp)).trans
      ((internM_frame _ nstrSch_wf _ _ _ _ _ _ _ _ hI).mono (by simp [nstrSch]) (by simp [nstrSch]))
  obtain ⟨a', hrun, hS', hg', -, -⟩ := stage_of_name hS (internNNode_str_run (decI x) "rec" a) hok hR₃
    hres hfr (by simp [POOL, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
  rw [hr] at hrun c
  refine ⟨decI (r.headD 0), a', hrun, hS', hg', ?_, rfl⟩
  have := mt UInt64.le_iff_toNat_le.mpr c
  have e : (4294967296 : Word).toNat = 4294967296 := rfl
  rw [e] at this; omega

end L.Ind
