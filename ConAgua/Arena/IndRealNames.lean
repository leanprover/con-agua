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

/-! ## A pool write at a tagged address plus an offset -/

theorem vpool_st_k (X : Mem) (T k v : Word) (h41 : T.toNat < 2 ^ 41)
    (hsz : (X.arr64 (tierA 0 (T >>> 40))).size ≤ 2 ^ 40)
    (hk : (T &&& 1099511627775).toNat + k.toNat < (X.arr64 (tierA 0 (T >>> 40))).size) :
    vpool (X.set64 (tierA 0 (T >>> 40)) ((T &&& 1099511627775) + k) v) = (vpool X).set! (T + k).toNat v :=
  vpool_stidx X T k v h41 (by rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega) hsz (by omega)

/-! ## `intern_nanon` (master's `internNAnon_spec`, `internNAnon_stage`) -/

/-- `intern_nanon` and its callees. -/
def naProg : Prog :=
  [("intern_nanon", internNAnon), ("nanon_find", nanonFind), ("nanon_push", nanonPush)]

def naFns : List FnName := naProg.map (·.1)

/-- `intern_nanon` writes the `anonymous` table and its counts. -/
theorem naProg_closed : closedA naProg [NAREC, NAREC + 256, NASLOT, NASLOT + 256] [34, 35] naFns = true := by decide +kernel

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
    MemFrame [NAREC, NAREC + 256, NASLOT, NASLOT + 256] [34, 35] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame naProg_closed (by decide) (run_of_callW hc)).1

/-! ## Pool scratch: `pool_room`, `iw_pool`, and growing the pool above its top -/

/-- **The model of `pool_room(k)`**: `k` words reserved at the pool top (inside the top's tier). -/
def prW (m : Mem) (k : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 0 + k < rdW (m.arr64 CTL) 0 then none
  else if m.len64 (tierA 0 (rdW (m.arr64 CTL) 0 >>> 40)) < (rdW (m.arr64 CTL) 0 &&& 1099511627775) + k then none
  else some (rdW (m.arr64 CTL) 0, m.set64 CTL 0 (rdW (m.arr64 CTL) 0 + k))

theorem poolRoom_specW (p : Prog) (hp : p.lookup "pool_room" = some L.Stubs.poolRoom) (n : Nat)
    (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pool_room" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ prW s₀.mem k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.poolRoom]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64] <;>
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

/-- `prW`, unfolded: the old top, the top raised, the room inside the top's tier array. -/
theorem prW_some {m m' : Mem} {k o : Word} (h : prW m k = some (o, m')) (hp : pcap m < 2 ^ 64) :
    o = m.top ∧ m' = m.set64 CTL 0 (m.top + k) ∧ m.top.toNat + k.toNat < 2 ^ 64 ∧
      (m.top &&& 1099511627775).toNat + k.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size := by
  simp only [prW] at h
  obtain ⟨c1, h⟩ := of_ite_none h
  obtain ⟨c2, h⟩ := of_ite_none h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have e : (rdW (m.arr64 CTL) 0 + k).toNat = (rdW (m.arr64 CTL) 0).toNat + k.toNat := add_nc _ _ c1
  have hno : (rdW (m.arr64 CTL) 0).toNat + k.toNat < 2 ^ 64 := by
    rw [← e]; exact UInt64.toNat_lt _
  simp only [← top_rdW] at c2 hno ⊢
  have hsz := pcap_tier m (m.top >>> 40) hp
  have hsplit := tag_split m.top
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hik : ((m.top &&& 1099511627775) + k).toNat = (m.top &&& 1099511627775).toNat + k.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp c2)
  rw [hlen, hik] at this
  refine ⟨?_, ?_, hno, this⟩ <;> first | rfl | trivial

/-- A pool store `POOL⟨⦃T⦄.tier⟩[⦃T⦄.idx + k] := x` at or above the original top, inside the tier's
array, keeps a growth a growth. -/
theorem grows_pset_k {m₀ m : Mem} (hg : Grows m₀ m) (hok : PoolOK m₀) {T k x : Word}
    (hT : T.toNat < 2 ^ 41) (hq : m₀.top.toNat ≤ (T + k).toNat)
    (hi : (T &&& 1099511627775).toNat + k.toNat < (m.arr64 (tierA 0 (T >>> 40))).size) :
    Grows m₀ (m.set64 (tierA 0 (T >>> 40)) ((T &&& 1099511627775) + k) x) := by
  have hpc : pcap m < 2 ^ 64 := by rw [hg.pcapEq]; have := hok.2.2.1; omega
  have hsz := pcap_tier m (T >>> 40) hpc
  have hv := vpool_st_k m T k x hT (by omega) hi
  have hne : tierA 0 (T >>> 40) ≠ CTL := Ne.symm (tierA_pool_ne _ _ (by decide) (by decide))
  have htop : (m.set64 (tierA 0 (T >>> 40)) ((T &&& 1099511627775) + k) x).top = m.top := L.Rom.top_set64_arr _ _ _ _ hne
  obtain ⟨hf, ha, hle, hcap, hpe, ht, hin⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htop]; exact PFrame.set64 _ _ _ hf
  · rw [hv]; exact Agree.set _ _ _ _ _ ha hq
  · rw [htop]; exact hle
  · rw [htop, pcap_set64]; exact hcap
  · rw [pcap_set64]; exact hpe
  · rw [htop]; exact ht
  · rw [htop, size_set64]; exact hin

/-- `grows_pset_k` at `k = 0` (the store `POOL⟨⦃T⦄.tier⟩[⦃T⦄.idx] := x`). -/
theorem grows_pset0 {m₀ m : Mem} (hg : Grows m₀ m) (hok : PoolOK m₀) {T x : Word}
    (hT : T.toNat < 2 ^ 41) (hq : m₀.top.toNat ≤ T.toNat)
    (hi : (T &&& 1099511627775).toNat < (m.arr64 (tierA 0 (T >>> 40))).size) :
    Grows m₀ (m.set64 (tierA 0 (T >>> 40)) (T &&& 1099511627775) x) := by
  have h := grows_pset_k hg hok (T := T) (k := 0) (x := x) hT (by simpa using hq) (by simpa using hi)
  simpa using h

/-- Raising the top by `k` words inside the top's tier array grows the pool. -/
theorem grows_raise (m : Mem) (k : Word) (hok : PoolOK m)
    (hk : (m.top &&& 1099511627775).toNat + k.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size) :
    Grows m (m.set64 CTL 0 (m.top + k)) :=
  Grows.write m m k hok (PFrame.refl _) (Agree.refl _ _) hk

/-- **The model of `iw_pool(s, d, l)`**: `POOL⦃d + j⦄ := IW[s + j]` (each store decodes `d`'s tier). -/
def iwpW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, s, d, l =>
    if l = 0 then some m
    else iwpW n (m.set64 (tierA 0 (d >>> 40)) (d &&& 1099511627775) (rdW (m.arr64 IW) s)) (s + 1) (d + 1) (l - 1)

theorem iwpW_nil (n : Nat) (m : Mem) (s d l : Word) (h : l = 0) :
    iwpW (n + 1) m s d l = some m := by simp [iwpW, h]
theorem iwpW_cons (n : Nat) (m : Mem) (s d l : Word) (h : l ≠ 0) :
    iwpW (n + 1) m s d l =
      iwpW n (m.set64 (tierA 0 (d >>> 40)) (d &&& 1099511627775) (rdW (m.arr64 IW) s)) (s + 1) (d + 1) (l - 1) := by
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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64, ih] <;>
      finish

theorem callW_ip {p : Prog} (hp : p.lookup "iw_pool" = some L.Stubs.iwPool) {n : Nat}
    {m m' : Mem} {s d l : Word} {r : List Word} (h : callW p n "iw_pool" [s, d, l] m = some (r, m')) :
    iwpW n m s d l = some m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwPool_specW p hp n _ s d l) h
  rw [← hs']; exact hW

/-- The next address of a tier, inside the tier. -/
theorem tag_succ (d : Word) (hd : d.toNat < 2 ^ 41) (hi : (d &&& 1099511627775).toNat + 1 < 2 ^ 40) :
    (d + 1) >>> 40 = d >>> 40 ∧ ((d + 1) &&& 1099511627775).toNat = (d &&& 1099511627775).toNat + 1 ∧
      (d + 1).toNat = d.toNat + 1 := by
  have e : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have s1 := tag_split d
  have s2 := tag_split (d + 1)
  have i1 := tag_idx_lt d
  have i2 := tag_idx_lt (d + 1)
  have ht : ((d + 1) >>> 40).toNat = (d >>> 40).toNat := by omega
  exact ⟨UInt64.toNat_inj.mp ht, by omega, e⟩

/-- **`iw_pool` copies the `IW` slice to the pool** above the top, inside the top's tier: a growth
(given one), the slice, nothing below `d` changed, and only the pool's arrays written. -/
theorem iwpW_ok {m₀ : Mem} (hok : PoolOK m₀) : ∀ (n : Nat) (m m' : Mem) (s d l : Word), iwpW n m s d l = some m' →
    Grows m₀ m → m₀.top.toNat ≤ d.toNat → d.toNat < 2 ^ 41 →
    (d &&& 1099511627775).toNat + l.toNat ≤ (m.arr64 (tierA 0 (d >>> 40))).size → s.toNat + l.toNat < 2 ^ 64 →
    Grows m₀ m' ∧ MemFrame [POOL, POOL1] [] m m' ∧
      (∀ i, i < d.toNat → (vpool m')[i]? = (vpool m)[i]?) ∧
      sliceL (vpool m') d.toNat l.toNat = sliceL (m.arr64 IW) s.toNat l.toNat := by
  intro n
  induction n with
  | zero => intro m m' s d l h; simp [iwpW] at h
  | succ n ih =>
    intro m m' s d l h hg hd hd41 hdl hs
    by_cases hl : l = 0
    · rw [iwpW_nil n m s d l hl] at h; cases h; subst hl
      exact ⟨hg, MemFrame.refl _ _ _, fun _ _ => rfl, by simp [sliceL]⟩
    rw [iwpW_cons n m s d l hl] at h
    have hl1 : 1 ≤ l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
    have hpc : pcap m < 2 ^ 64 := by rw [hg.pcapEq]; have := hok.2.2.1; omega
    have hsz := pcap_tier m (d >>> 40) hpc
    have hsplit := tag_split d
    have htier := tag_tier_le d hd41
    obtain ⟨et, ei, ed⟩ := tag_succ d hd41 (by omega)
    have hs1 : (s + 1).toNat = s.toNat + 1 := toNat_succ_lt (by omega)
    have hlm : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hne : tierA 0 (d >>> 40) ≠ CTL := Ne.symm (tierA_pool_ne _ _ (by decide) (by decide))
    have hg₁ := grows_pset0 hg hok (x := rdW (m.arr64 IW) s) hd41 hd (by omega)
    have hv₁ := vpool_stidx0 m d (rdW (m.arr64 IW) s) hd41 (by omega) (by omega)
    obtain ⟨hg', hf, hbl, hsl⟩ := ih _ _ _ _ _ h hg₁ (by omega) (by omega)
      (by rw [et, ei, hlm, size_set64]; omega) (by rw [hs1, hlm]; omega)
    have hmem : tierA 0 (d >>> 40) ∈ [POOL, POOL1] := by
      rcases tierA_pool (d >>> 40) with e | e <;> simp [e]
    refine ⟨hg', ((MemFrame.set64 _ _ hne _ _).mono (by simpa using hmem) (by simp)).trans hf,
      fun i hi => ?_, ?_⟩
    · rw [hbl i (by omega), hv₁, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      have : d.toNat ≠ i := by omega
      simp [this]
    · obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
      rw [hk, sliceL_succ, sliceL_succ]
      have hiw : (m.set64 (tierA 0 (d >>> 40)) (d &&& 1099511627775) (rdW (m.arr64 IW) s)).arr64 IW = m.arr64 IW :=
        arr64_set64_tier_ne _ _ _ _ _ ⟨by decide, by decide⟩
      rw [ed, hs1, hlm, hk, hiw] at hsl
      simp only [Nat.add_sub_cancel] at hsl
      rw [hsl]
      congr 1
      have e1 := hbl d.toNat (by omega)
      rw [e1, hv₁, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [vpool_size, show d.toNat < 2 ^ 41 from hd41, rdW]

/-! ## `name_rec(n)` (the pool bytes `rec`, master's `intern_nstr`) -/

/-- `name_rec` and its callees. -/
def nrProg : Prog :=
  [("name_rec", L.Stubs.nameRecL), ("pool_room", L.Stubs.poolRoom), ("intern_nstr", internNStr),
   ("lit_hash", litHash), ("limbs_eq", limbsEq), ("nstr_match", nsMatch), ("nstr_find", nsFind),
   ("nstr_push", nsPush)]

def nrFns : List FnName := nrProg.map (·.1)

/-- `name_rec` writes the pool (and its top) and the `str` table. -/
theorem nrProg_closed : closedA nrProg [POOL, POOL1, NSREC, NSREC + 256, NSSLOT, NSSLOT + 256] [0, 36, 37] nrFns = true := by
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
  ((m.set64 (tierA 0 (o >>> 40)) (o &&& 1099511627775) 114).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 1) 101).set64
    (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 2) 99

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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
      callW_spec p n "pool_room", callW_spec p n "intern_nstr"] <;>
    finish [nrW, recBytes]

theorem strWords_recB : strWords "rec" = [114, 101, 99] := by decide

/-- **The bytes after the reserved room grow the pool and hold `rec`.** -/
theorem recBytes_ok (m : Mem) (hpool : PoolOK m)
    (hroom : (m.top &&& 1099511627775).toNat + 3 ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size) :
    Grows m (recBytes (m.set64 CTL 0 (m.top + 3)) m.top) ∧
      SliceOK (recBytes (m.set64 CTL 0 (m.top + 3)) m.top) m.top 3 ∧
      sliceL (vpool (recBytes (m.set64 CTL 0 (m.top + 3)) m.top)) m.top.toNat 3 = strWords "rec" := by
  have hc := hpool.2.1
  have h41 := hpool.top41
  have hsz := hpool.small.tier (m.top >>> 40)
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top h41
  have hne : tierA 0 (m.top >>> 40) ≠ CTL := Ne.symm (tierA_pool_ne _ _ (by decide) (by decide))
  have hX : (m.set64 CTL 0 (m.top + 3)).arr64 (tierA 0 (m.top >>> 40)) = m.arr64 (tierA 0 (m.top >>> 40)) :=
    Mem.arr64_set64_ne _ _ _ _ _ hne
  have e1 : (m.top + 1).toNat = m.top.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (m.top + 2).toNat = m.top.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (m.top + 3).toNat = m.top.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have g0 := grows_raise m 3 hpool (by simpa using hroom)
  have g1 := grows_pset0 g0 hpool (T := m.top) (x := 114) h41 (Nat.le_refl _) (by rw [hX]; omega)
  have g2 := grows_pset_k g1 hpool (T := m.top) (k := 1) (x := 101) h41 (by rw [e1]; omega)
    (by rw [size_set64, hX]; simp only [UInt64.reduceToNat]; omega)
  have g3 := grows_pset_k g2 hpool (T := m.top) (k := 2) (x := 99) h41 (by rw [e2]; omega)
    (by rw [size_set64, size_set64, hX]; simp only [UInt64.reduceToNat]; omega)
  have htop : (recBytes (m.set64 CTL 0 (m.top + 3)) m.top).top = m.top + 3 := by
    simp only [recBytes]
    rw [L.Rom.top_set64_arr _ _ _ _ hne, L.Rom.top_set64_arr _ _ _ _ hne, L.Rom.top_set64_arr _ _ _ _ hne]
    exact Mem.top_set64 _ _ hc
  refine ⟨g3, SliceOK.fresh g3 htop, ?_⟩
  have hv : vpool (recBytes (m.set64 CTL 0 (m.top + 3)) m.top) =
      (((vpool m).set! m.top.toNat 114).set! (m.top + 1).toNat 101).set! (m.top + 2).toNat 99 := by
    simp only [recBytes]
    rw [vpool_st_k _ _ _ _ h41 (by simp only [Mem.size_arr64_set64, hX]; omega)
        (by simp only [Mem.size_arr64_set64, hX, UInt64.reduceToNat]; omega),
      vpool_st_k _ _ _ _ h41 (by simp only [Mem.size_arr64_set64, hX]; omega)
        (by simp only [Mem.size_arr64_set64, hX, UInt64.reduceToNat]; omega),
      vpool_stidx0 _ _ _ h41 (by simp only [hX]; omega) (by simp only [hX]; omega),
      vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]
  have b0 : m.top.toNat < 2199023255552 := by omega
  have b1 : m.top.toNat + 1 < 2199023255552 := by omega
  have b2 : m.top.toNat + 2 < 2199023255552 := by omega
  rw [hv, strWords_recB]
  simp only [sliceL, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, vpool_size, e1, e2]
  simp (config := { decide := true }) [b0, b1, b2]

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
  rcases h1 : callW nrProg n "pool_room" [3] m with _ | ⟨r₁, m₁⟩
  · rw [h1] at hW; cases hW
  rw [h1] at hW
  simp only at hW
  have hpool : PoolOK m := hS.1.arena.1.lit.1
  obtain ⟨ho, hm₁, hno, hroom⟩ := prW_some (callW_pr rfl h1) (by have := hpool.2.2.1; omega)
  rw [ho, hm₁] at hW
  obtain ⟨hg, hsl, hk⟩ := recBytes_ok m hpool hroom
  generalize hm₂ : recBytes (m.set64 CTL 0 (m.top + 3)) m.top = m₂ at hW hg hsl hk
  rcases h2 : callW nrProg n "intern_nstr" [x, m.top, 3] m₂ with _ | ⟨r₂, m₃⟩
  · rw [h2] at hW; cases hW
  rw [h2] at hW
  simp only at hW
  obtain ⟨c, hW⟩ := of_ite_none hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hR₂ : ArenaR m₂ a := ArenaR.grow m m₂ hg a hS.1.arena.1
  have hmo₂ : ModeOK m₂ := hS.1.mode.grows hg
  have hpc₂ : pcap m₂ < 2 ^ 64 := by rw [hg.pcapEq]; have := hpool.2.2.1; omega
  have hcap₂ : m.top.toNat + (3 : Word).toNat ≤ pcap m₂ := by have := hsl.le; have := hg.cap; omega
  obtain ⟨s₃, hs₃, -, hok, hR₃, hres⟩ := triple_of_callW
    (internNStr_refinesA nrProg rfl rfl rfl rfl rfl rfl a n ⟨m₂, Locals.init []⟩ x m.top 3 hR₂ hx hsl
      "rec" hk (ModeOK.slice0 hmo₂ hsl)) h2
  obtain ⟨s₃', hs₃', -, hI⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internNStr_spec nrProg rfl rfl rfl rfl rfl rfl n _ x m.top 3 hpc₂ hcap₂) h2
  simp only at hs₃ hR₃ hs₃' hI
  rw [hs₃] at hR₃
  rw [hs₃'] at hI
  have hfr : MemFrame [POOL, POOL1, NSREC, NSREC + 256, NSSLOT, NSSLOT + 256] [0, 36, 37] m m₃ :=
    ((grows_frame m m₂ hg).mono (by simp) (by simp)).trans
      ((consInternM_frame nstrCS_wf hI).mono (by simp [ConsSch.wset, nstrCS]) (by simp [ConsSch.wset, nstrCS]))
  have hmo₃ : ModeOK m₃ := hmo₂.frame (consInternM_frame nstrCS_wf hI) (by simp [nstrCS]) (by simp [nstrCS])
  obtain ⟨a', hrun, hS', hg', -, -⟩ := stage_of_name hS (internNNode_str_run (decI x) "rec" a) hok hR₃
    hres hfr (by simp [POOL, POOL1, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩) hmo₃
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
theorem ilProg_closed : closedA ilProg [POOL, POOL1, LSREC, LSREC + 256, LSSLOT, LSSLOT + 256, LSHP, LSHP + 256] [0, 40, 41] ilFns = true := by
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
    MemFrame [POOL, POOL1, LSREC, LSREC + 256, LSSLOT, LSSLOT + 256, LSHP, LSHP + 256] [0, 40, 41] m m' := by
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64,
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
  rcases h1 : callW ilProg n "pool_room" [l] m with _ | ⟨r₁, m₁⟩
  · rw [h1] at hW; cases hW
  rw [h1] at hW
  simp only at hW
  have hpool : PoolOK m := hS.1.arena.1.lit.1
  obtain ⟨ho, hm₁, hno, hroom⟩ := prW_some (callW_pr rfl h1) (by have := hpool.2.2.1; omega)
  rw [ho] at hW
  rcases h2 : callW ilProg n "iw_pool" [o, m.top, l] m₁ with _ | ⟨r₂, m₂⟩
  · rw [h2] at hW; cases hW
  rw [h2] at hW
  simp only at hW
  rcases h3 : callW ilProg n "intern_ls" [m.top, l] m₂ with _ | ⟨r₃, m₃⟩
  · rw [h3] at hW; cases hW
  rw [h3] at hW
  simp only at hW
  obtain ⟨c, hW⟩ := of_ite_none hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hc0 := hpool.2.1
  have h41 := hpool.top41
  have hsz := hpool.small.tier (m.top >>> 40)
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top h41
  have hne : tierA 0 (m.top >>> 40) ≠ CTL := Ne.symm (tierA_pool_ne _ _ (by decide) (by decide))
  have htl : (m.top + l).toNat = m.top.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have g0 : Grows m m₁ := by rw [hm₁]; exact grows_raise m l hpool hroom
  have hiw₁ : m₁.arr64 IW = m.arr64 IW := by rw [hm₁, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have htier₁ : m₁.arr64 (tierA 0 (m.top >>> 40)) = m.arr64 (tierA 0 (m.top >>> 40)) := by
    rw [hm₁, Mem.arr64_set64_ne _ _ _ _ _ hne]
  obtain ⟨hsl, hb⟩ := hslice_lsWords l.toNat o.toNat us hd
  have hIW := hS.2.2.2.1
  have hol : o.toNat + l.toNat < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · rw [h0]; exact Nat.lt_of_lt_of_le (UInt64.toNat_lt o) (by omega)
    · have := hb h0; simp only [iwA] at this; omega
  obtain ⟨hg, hf₂, -, hsl₂⟩ := iwpW_ok hpool n m₁ m₂ o m.top l (callW_ip rfl h2) g0 (Nat.le_refl _) h41
    (by rw [htier₁]; exact hroom) hol
  rw [hiw₁] at hsl₂
  have htop₂ : m₂.top = m.top + l := by
    have e := hf₂.2.1 0 (by simp)
    simp only [top_rdW] at e ⊢
    rw [e, hm₁]; exact Mem.top_set64 _ _ hc0
  have hA₂ : ArenaD m₂ a := ArenaD.grow m m₂ hg a hS.1.arena
  have hmo₂ : ModeOK m₂ := hS.1.mode.grows hg
  have hsl₂' : SliceOK m₂ m.top l := SliceOK.fresh hg htop₂
  have hpc₂ : pcap m₂ < 2 ^ 64 := by rw [hg.pcapEq]; have := hpool.2.2.1; omega
  have hcap₂ : m.top.toNat + l.toNat ≤ pcap m₂ := by have := hsl₂'.le; have := hg.cap; omega
  obtain ⟨s₃, hs₃, -, hI⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internLs_spec ilProg rfl rfl rfl rfl rfl rfl n _ m.top l hpc₂ hcap₂) h3
  simp only at hs₃ hI
  rw [hs₃] at hI
  obtain ⟨ok, hA₃, res, hf₃⟩ := L.Front.internLs_D m₂ a hA₂ (r₃.headD 0) m₃ m.top l hsl₂'
    us (by rw [hsl₂]; simpa [iwA] using hsl) (ModeOK.slice0 hmo₂ hsl₂') hI
  have hrun := AM.run_of_ok _ _ ok
  rw [res] at hrun
  obtain ⟨hca, hpi, -⟩ := internLsNode_keep _ _ _ _ hrun
  have hfr : MemFrame [POOL, POOL1, LSREC, LSREC + 256, LSSLOT, LSSLOT + 256, LSHP, LSHP + 256] [0, 40, 41] m m₃ :=
    ((grows_frame m m₂ hg).mono (by simp) (by simp)).trans
      (hf₃.mono (by simp [lsSch]) (by simp [lsSch]))
  obtain ⟨hS', hg'⟩ := StageR.of_walkM hS hA₃ hfr (by simp [POOL, POOL1, LSREC, LSSLOT, LSHP]) (by simp)
    (by simp only [cp, hca, hpi]) (hmo₂.frame hf₃ (by simp [lsSch]) (by simp [lsSch]))
  rw [hr] at hrun c
  refine ⟨_, _, hrun, hS', hg', ?_, rfl⟩
  have := mt UInt64.le_iff_toNat_le.mpr c
  have e : (4294967296 : Word).toNat = 4294967296 := rfl
  rw [e] at this; show (r.headD 0).toNat < 2 ^ 32; omega

end L.Ind
