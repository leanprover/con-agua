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
  if m.len64 (tierA 0 (rdW (m.arr64 CTL) 0 >>> 40)) < (rdW (m.arr64 CTL) 0 &&& 1099511627775) then none
  else if m.len64 (tierA 0 (rdW (m.arr64 CTL) 0 >>> 40)) - (rdW (m.arr64 CTL) 0 &&& 1099511627775) < k then none
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

/-- `prW`, unfolded: the old top, the top raised, the room inside the top's tier. -/
theorem prW_some {m m' : Mem} {k o : Word} (hp : PoolOK m) (h : prW m k = some (o, m')) :
    o = m.top ∧ m' = m.set64 CTL 0 (m.top + k) ∧
      (m.top &&& 1099511627775).toNat + k.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size := by
  have ht : rdW (m.arr64 CTL) 0 = m.top := rfl
  simp only [prW, ht] at h
  obtain ⟨c1, h⟩ := of_ite_none h
  obtain ⟨c2, h⟩ := of_ite_none h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hsz := hp.small.tier (m.top >>> 40)
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    rw [len64_eq]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have c2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp c2)
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp c1), hlen] at c2'
  have c1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp c1)
  rw [hlen] at c1'
  exact ⟨rfl, rfl, by omega⟩

/-- **The model of `iw_pool(s, d, l)`**: `POOL[d + j] := IW[s + j]`. -/
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

/-- **`iw_pool` copies the `IW` slice to the pool** at the tagged address `d` (inside `d`'s tier
array): it writes only the pool's tiers, nothing below `d`, and the slice at `d` is `IW`'s. -/
theorem iwpW_ok : ∀ (n : Nat) (m m' : Mem) (s d l : Word), iwpW n m s d l = some m' →
    d.toNat < 2 ^ 41 →
    (d &&& 1099511627775).toNat + l.toNat ≤ (m.arr64 (tierA 0 (d >>> 40))).size →
    (m.arr64 (tierA 0 (d >>> 40))).size < 2 ^ 40 →
    s.toNat + l.toNat < 2 ^ 64 →
    PFrame m m' ∧ MemFrame [POOL, POOL1] [] m m' ∧ Agree (vpool m') (vpool m) d.toNat ∧
      sliceL (vpool m') d.toNat l.toNat = sliceL (m.arr64 IW) s.toNat l.toNat := by
  intro n
  induction n with
  | zero => intro m m' s d l h; simp [iwpW] at h
  | succ n ih =>
    intro m m' s d l h hd hk hsz hb
    by_cases hl : l = 0
    · rw [iwpW_nil n m s d l hl] at h; cases h; subst hl
      exact ⟨PFrame.refl _, MemFrame.refl _ _ _, Agree.refl _ _, by simp [sliceL]⟩
    rw [iwpW_cons n m s d l hl] at h
    have hl1 : 1 ≤ l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
    have hi := tag_idx_toNat d
    have ht := tag_tier_toNat d
    have hd1 : (d + 1).toNat = d.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hb1 : (s + 1).toNat = s.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hlm : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have htd : (d + 1) >>> 40 = d >>> 40 := tag_tier_eq (by rw [hd1]; omega)
    have hid : ((d + 1) &&& 1099511627775).toNat = (d &&& 1099511627775).toNat + 1 := by
      rw [tag_idx_toNat, hd1]; omega
    generalize hv : rdW (m.arr64 IW) s = v at h
    generalize hm₁ : m.set64 (tierA 0 (d >>> 40)) (d &&& 1099511627775) v = m₁ at h
    have hsz₁ : (m₁.arr64 (tierA 0 (d >>> 40))).size = (m.arr64 (tierA 0 (d >>> 40))).size := by
      rw [← hm₁, Mem.size_arr64_set64]
    have hvp : vpool m₁ = (vpool m).set! d.toNat v := by
      rw [← hm₁]; exact vpool_stidx0 m d v hd (by omega) (by omega)
    have hiw : m₁.arr64 IW = m.arr64 IW := by
      rw [← hm₁]; exact Mem.arr64_set64_ne _ _ _ _ _ (tierA_pool_ne _ IW (by decide) (by decide))
    obtain ⟨hf, hmf, hag, hsl⟩ := ih _ _ _ _ _ h (by omega) (by rw [htd, hid, hsz₁, hlm]; omega)
      (by rw [htd, hsz₁]; exact hsz) (by rw [hb1, hlm]; omega)
    have hpf : PFrame m m₁ := by rw [← hm₁]; exact PFrame.set64 _ _ _ (PFrame.refl m)
    have hmf₁ : MemFrame [POOL, POOL1] [] m m₁ := by
      rw [← hm₁]
      refine (MemFrame.set64 m _ (tierA_pool_ne _ CTL (by decide) (by decide)).symm _ _).mono ?_ (by simp)
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      rcases tierA_pool (d >>> 40) with e | e <;> rw [e] <;> simp
    have hdlt : d.toNat < (vpool m).size := by rw [vpool_size]; exact hd
    refine ⟨hpf.trans hf, hmf₁.trans hmf, fun j hj => ?_, ?_⟩
    · rw [hag j (by rw [hd1]; omega), hvp, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [show d.toNat ≠ j by omega]
    · obtain ⟨k, hk'⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
      rw [hk', sliceL_succ, sliceL_succ]
      rw [hd1, hb1, hlm, hk', hiw] at hsl
      simp only [Nat.add_sub_cancel] at hsl
      rw [hsl, hag d.toNat (by rw [hd1]; omega), hvp, ← hv]
      simp [Array.set!_eq_setIfInBounds, hdlt, rdW]

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
    (hk : (m.top &&& 1099511627775).toNat + 3 ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size) :
    Grows m (recBytes (m.set64 CTL 0 (m.top + 3)) m.top) ∧
      SliceOK (recBytes (m.set64 CTL 0 (m.top + 3)) m.top) m.top 3 ∧
      sliceL (vpool (recBytes (m.set64 CTL 0 (m.top + 3)) m.top)) m.top.toNat 3 = strWords "rec" := by
  have hsz := hpool.small.tier (m.top >>> 40)
  have h41 := hpool.top41
  have hc := hpool.2.1
  have hil := tag_idx_lt m.top
  have hsplit := tag_split m.top
  have e1 : (m.top + 1).toNat = m.top.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (m.top + 2).toNat = m.top.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (m.top + 3).toNat = m.top.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  generalize hX : m.set64 CTL 0 (m.top + 3) = X
  have hXa : X.arr64 (tierA 0 (m.top >>> 40)) = m.arr64 (tierA 0 (m.top >>> 40)) := by
    rw [← hX]; exact Mem.arr64_set64_ne _ _ _ _ _ (tierA_pool_ne _ CTL (by decide) (by decide)).symm
  have hXv : vpool X = vpool m := by rw [← hX]; exact vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩
  have hXc : 0 < (X.arr64 CTL).size := by rw [← hX, Mem.size_arr64_set64]; exact hc
  have hXt : X.top = m.top + 3 := by rw [← hX]; exact Mem.top_set64 _ _ hc
  have hv : vpool (recBytes X m.top) =
      (((vpool m).set! m.top.toNat 114).set! (m.top + 1).toNat 101).set! (m.top + 2).toNat 99 := by
    simp only [recBytes]
    rw [vpool_st_k _ _ _ _ h41 (by simp only [Mem.size_arr64_set64, hXa]; omega)
        (by simp only [Mem.size_arr64_set64, hXa, UInt64.reduceToNat]; omega),
      vpool_st_k _ _ _ _ h41 (by simp only [Mem.size_arr64_set64, hXa]; omega)
        (by simp only [Mem.size_arr64_set64, hXa, UInt64.reduceToNat]; omega),
      vpool_stidx0 _ _ _ h41 (by rw [hXa]; omega) (by rw [hXa]; omega), hXv]
  have hpf : PFrame X (recBytes X m.top) := by
    simp only [recBytes]; repeat apply PFrame.set64
    exact PFrame.refl _
  have htop : (recBytes X m.top).top = m.top + 3 := by rw [hpf.top, hXt]
  have hg : Grows m (recBytes X m.top) := by
    apply Grows.intro m _ hpool
    · rw [htop, hX]; exact hpf
    · rw [hv]
      repeat refine Agree.set _ _ _ _ _ ?_ (by omega)
      exact Agree.refl _ _
    · rw [htop, e3]; omega
    · rw [htop, e3]; omega
  refine ⟨hg, SliceOK.fresh hg htop, ?_⟩
  rw [hv, strWords_recB]
  simp only [sliceL, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, vpool_size, e1, e2]
  simp (config := { decide := true }) [show m.top.toNat < 2199023255552 by omega,
    show m.top.toNat + 1 < 2199023255552 by omega, show m.top.toNat + 2 < 2199023255552 by omega]

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
  obtain ⟨ho, hm₁, hroom⟩ := prW_some hpool (callW_pr rfl h1)
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
  have hps : pcap m < 2 ^ 63 := hpool.2.2.1
  have hcap : m.top.toNat + 3 ≤ pcap m₂ := by
    have := hsl.le; have := hg.cap; simp only [UInt64.reduceToNat] at *; omega
  have hpc : pcap m₂ < 2 ^ 64 := by rw [hg.pcapEq]; omega
  obtain ⟨s₃, hs₃, -, hok, hR₃, hres⟩ := triple_of_callW
    (internNStr_refinesA nrProg rfl rfl rfl rfl rfl rfl a n ⟨m₂, Locals.init []⟩ x m.top 3 hR₂ hx hsl
      "rec" hk (ModeOK.slice0 (hS.1.mode.grows hg) hsl)) h2
  obtain ⟨s₃', hs₃', -, hI⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internNStr_spec nrProg rfl rfl rfl rfl rfl rfl n _ x m.top 3 hpc
      (by simpa using hcap)) h2
  simp only at hs₃ hR₃ hs₃' hI
  rw [hs₃] at hR₃
  rw [hs₃'] at hI
  have hfr : MemFrame [POOL, POOL1, NSREC, NSREC + 256, NSSLOT, NSSLOT + 256] [0, 36, 37] m m₃ :=
    ((grows_frame m m₂ hg).mono (by simp) (by simp)).trans
      ((consInternM_frame nstrCS_wf hI).mono (by simp [ConsSch.wset, nstrCS]) (by simp [ConsSch.wset, nstrCS]))
  obtain ⟨a', hrun, hS', hg', -, -⟩ := stage_of_name hS (internNNode_str_run (decI x) "rec" a) hok hR₃
    hres hfr (by simp [POOL, POOL1, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
    ((hS.1.mode.grows hg).frame (consInternM_frame nstrCS_wf hI) (by simp [ConsSch.wset, nstrCS])
      (by simp [ConsSch.wset, nstrCS]))
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
  obtain ⟨ho, hm₁, hroom⟩ := prW_some hpool (callW_pr rfl h1)
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
  have hps : pcap m < 2 ^ 63 := hpool.2.2.1
  have h41 := hpool.top41
  have hsz := hpool.small.tier (m.top >>> 40)
  have hil := tag_idx_lt m.top
  have hsplit := tag_split m.top
  have htl : (m.top + l).toNat = m.top.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hiw₁ : m₁.arr64 IW = m.arr64 IW := by rw [hm₁, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hta₁ : m₁.arr64 (tierA 0 (m.top >>> 40)) = m.arr64 (tierA 0 (m.top >>> 40)) := by
    rw [hm₁]; exact Mem.arr64_set64_ne _ _ _ _ _ (tierA_pool_ne _ CTL (by decide) (by decide)).symm
  have hv₁ : vpool m₁ = vpool m := by rw [hm₁]; exact vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩
  obtain ⟨hsl, hb⟩ := hslice_lsWords l.toNat o.toNat us hd
  have hIW := hS.2.2.2.1
  have hol : o.toNat + l.toNat < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · rw [h0]; exact Nat.lt_of_lt_of_le (UInt64.toNat_lt o) (by omega)
    · have := hb h0; simp only [iwA] at this; omega
  obtain ⟨hf₂, -, hag₂, hsl₂⟩ := iwpW_ok n m₁ m₂ o m.top l (callW_ip rfl h2) h41
    (by rw [hta₁]; exact hroom) (by rw [hta₁]; exact hsz) hol
  rw [hiw₁] at hsl₂
  have htop₂ : m₂.top = m.top + l := by rw [hf₂.top, hm₁]; exact Mem.top_set64 _ _ hc0
  have hg : Grows m m₂ := by
    apply Grows.intro m _ hpool
    · rw [htop₂, ← hm₁]; exact hf₂
    · rw [← hv₁]; exact hag₂
    · rw [htop₂, htl]; omega
    · rw [htop₂, htl]; omega
  have hA₂ : ArenaD m₂ a := ArenaD.grow m m₂ hg a hS.1.arena
  have hq : SliceOK m₂ m.top l := SliceOK.fresh hg htop₂
  have hcap : m.top.toNat + l.toNat ≤ pcap m₂ := by have := hq.le; have := hg.cap; omega
  have hpc : pcap m₂ < 2 ^ 64 := by rw [hg.pcapEq]; omega
  obtain ⟨s₃, hs₃, -, hI⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internLs_spec ilProg rfl rfl rfl rfl rfl rfl n _ m.top l hpc hcap) h3
  simp only at hs₃ hI
  rw [hs₃] at hI
  obtain ⟨ok, hA₃, res, hf₃⟩ := L.Front.internLs_D m₂ a hA₂ (r₃.headD 0) m₃ m.top l hq
    us (by rw [hsl₂]; simpa [iwA] using hsl) (ModeOK.slice0 (hS.1.mode.grows hg) hq) hI
  have hrun := AM.run_of_ok _ _ ok
  rw [res] at hrun
  obtain ⟨hca, hpi, -⟩ := internLsNode_keep _ _ _ _ hrun
  have hfr : MemFrame [POOL, POOL1, LSREC, LSREC + 256, LSSLOT, LSSLOT + 256, LSHP, LSHP + 256] [0, 40, 41] m m₃ :=
    ((grows_frame m m₂ hg).mono (by simp) (by simp)).trans
      (hf₃.mono (by simp [lsSch]) (by simp [lsSch]))
  obtain ⟨hS', hg'⟩ := StageR.of_walkM hS hA₃ hfr (by simp [POOL, POOL1, LSREC, LSSLOT, LSHP]) (by simp)
    (by simp only [cp, hca, hpi]) ((hS.1.mode.grows hg).frame hf₃ (by simp [lsSch]) (by simp [lsSch]))
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
    closedA ptProg [POOL, POOL1, NSREC, NSREC + 256, NSSLOT, NSSLOT + 256, NNREC, NNREC + 256, NNSLOT, NNSLOT + 256] [0, 36, 37, 38, 39] ptFns = true := by
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
    MemFrame [POOL, POOL1, NSREC, NSREC + 256, NSSLOT, NSSLOT + 256, NNREC, NNREC + 256, NNSLOT, NNSLOT + 256] [0, 36, 37, 38, 39] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ptProg_closed (by decide) (run_of_callW hc)).1

set_option maxHeartbeats 2000000 in
/-- `ptnW_spec` from the one lookup. -/
theorem ptnW_spec' (p : Prog) (hp : p.lookup "proj_table_name" = some projTableNameL) (n : Nat)
    (s₀ : St) (t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_table_name" [t]
    ⦃fun r s' => LocEq s' s₀ ∧ ptnW p n s₀.mem t = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, projTableNameL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64, evalE_tierE, evalE_idxE,
      callW_spec p n "intern_nstr", callW_spec p n "intern_nnum"] <;>
    finish [ptnW, ptMem, ptBytes, tierW, idxW, nameCnt]

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
  obtain ⟨c1, hW⟩ := of_ite_none hW
  obtain ⟨c2, hW⟩ := of_ite_none hW
  obtain ⟨c3, hW⟩ := of_ite_none hW
  by_cases c4 : nameCnt m (t >>> 28) ((t >>> 27) &&& 1) ≤ (t &&& 134217727)
  · rw [if_pos c4] at hW; cases hW
  rw [if_neg c4] at hW
  obtain ⟨c5, hW⟩ := of_ite_none hW
  obtain ⟨c6, hW⟩ := of_ite_none hW
  have hpool : PoolOK m := hS.1.arena.1.lit.1
  generalize ho : rdW (m.arr64 CTL) 0 = o at hW c5 c6
  have hot : o = m.top := ho.symm
  subst hot
  obtain ⟨hg, hsl, hk⟩ := ptMem_facts m hpool c6
  have hR1 : ArenaR (ptMem m m.top) a := ArenaR.grow m _ hg a hS.1.arena.1
  have hcap : m.top.toNat + 9 ≤ pcap (ptMem m m.top) := by
    have := hsl.le; have := hg.cap; simp only [UInt64.reduceToNat] at *; omega
  have hpc : pcap (ptMem m m.top) < 2 ^ 64 := by rw [hg.pcapEq]; have := hpool.2.2.1; omega
  rcases hc1 : callW ptProg n "intern_nstr" [t, m.top, 9] (ptMem m m.top) with _ | ⟨r₁, m₂⟩
  · rw [hc1] at hW; cases hW
  rw [hc1] at hW
  simp only at hW
  obtain ⟨c7, hW⟩ := of_ite_none hW
  obtain ⟨s₂, hs₂, -, hok1, hR2, hres1⟩ := triple_of_callW
    (internNStr_refinesA ptProg rfl rfl rfl rfl rfl rfl a n ⟨ptMem m m.top, Locals.init []⟩ t m.top 9 hR1 ht
      hsl "projTable" hk (ModeOK.slice0 (hS.1.mode.grows hg) hsl)) hc1
  obtain ⟨s₂', hs₂', -, hW1⟩ := triple_of_callW (s₀ := ⟨ptMem m m.top, Locals.init []⟩)
    (internNStr_spec ptProg rfl rfl rfl rfl rfl rfl n _ t m.top 9 hpc (by simpa using hcap)) hc1
  simp only at hs₂ hR2 hs₂' hW1
  rw [hs₂] at hR2
  rw [hs₂'] at hW1
  have hfr : MemFrame [POOL, POOL1, NSREC, NSREC + 256, NSSLOT, NSSLOT + 256] [0, 36, 37] m m₂ :=
    ((grows_frame m _ hg).mono (by simp) (by simp)).trans
      ((consInternM_frame nstrCS_wf hW1).mono (by simp [ConsSch.wset, nstrCS]) (by simp [ConsSch.wset, nstrCS]))
  obtain ⟨a1, hrun1, hS1, hg1, -, -⟩ := stage_of_name hS (internNNode_str_run (decI t) "projTable" a)
    hok1 hR2 hres1 hfr (by simp [POOL, POOL1, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
    ((hS.1.mode.grows hg).frame (consInternM_frame nstrCS_wf hW1) (by simp [ConsSch.wset, nstrCS])
      (by simp [ConsSch.wset, nstrCS]))
  have hr1 : (r₁.headD 0).toNat < 2 ^ 32 := by
    have := mt UInt64.le_iff_toNat_le.mpr c7
    have e : (4294967296 : Word).toNat = 4294967296 := rfl
    rw [e] at this; omega
  rcases hc2 : callW ptProg n "intern_nnum" [r₁.headD 0, 0] m₂ with _ | ⟨r₂, m₃⟩
  · rw [hc2] at hW; cases hW
  rw [hc2] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
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
