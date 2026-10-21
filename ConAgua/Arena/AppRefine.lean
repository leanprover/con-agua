import ConAgua.Arena.StoreRel
import ConAgua.Arena.AppStore

/-!
# The `app` store refines the arena's `app` tables

The second store relation, written in the style of `LitRefine.lean` for the record
`AppNode { f a : EIdx }` (`ConAgua/Arena/AppStore.lean` has the L code). `AppR m a`: the scratch
flag is the arena's, and each tier of the L `app` store represents the arena's `app` table of that
tier (`ATierRel`): node `i` holds the two handle words of `tb.nodes[i]`, the cons table maps each
node's key to its handle `hdW 4 t i` and points only at nodes with its key, and the slots satisfy
the linear-probing invariant. `internApp_refines`: `intern_app(f, a)` refines
`internE (.app (decE f) (decE a))` under `AppR`.

Not represented: the derived column (`derOfApp`, through `mixHash`) and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `app` cons key. -/
abbrev appKey (f a : EIdx) : AppNode := ⟨f, a⟩

/-- `a` with the scratch / persistent `app` table replaced. -/
def withScrApps (a : AState) (t : Tbl AppNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with apps := t } } }
def withPersApps (a : AState) (t : Tbl AppNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with apps := t } } }

/-- The arena's scratch skip at an `app` view (`EStore.persFindMaybe`). -/
def skA (a : AState) (f x : EIdx) : Bool :=
  if a.store.scratchOn then (if f.isPersistent then !x.isPersistent else true) else false

/-- The arena's persistent probe at an `app` view, after the skip. -/
def pfA (a : AState) (f x : EIdx) : Option EIdx :=
  if skA a f x then none else a.store.pers.apps.cons[appKey f x]?

theorem persFindMaybe_app (a : AState) (f x : EIdx) :
    a.store.persFindMaybe (.app f x) = pfA a f x := by
  simp [EStore.persFindMaybe, pfA, skA, EStore.eViewHasScratchChild, ETables.find?, Tbl.find?]

/-- `internE` at an `app` node, unfolded. -/
theorem internE_app_run (f x : EIdx) (a : AState) :
    (internE (.app f x)).run a =
      match pfA a f x with
      | some h => .ok (h, a)
      | none =>
        if a.store.scratchOn then
          match a.store.scr.apps.cons[appKey f x]? with
          | some h => .ok (h, a)
          | none =>
            if a.store.scr.apps.size < Idx.idxCap then
              .ok (Idx.mk ETag.app Idx.tierS (UInt32.ofNat a.store.scr.apps.size),
                withScrApps a (a.store.scr.apps.push (appKey f x) (a.store.derOfView (.app f x))
                    (Idx.mk ETag.app Idx.tierS (UInt32.ofNat a.store.scr.apps.size))))
            else .error (.native "arena: expression constructor array full")
        else
          if a.store.pers.apps.size < Idx.idxCap then
            .ok (Idx.mk ETag.app Idx.tierP (UInt32.ofNat a.store.pers.apps.size),
              withPersApps a (a.store.pers.apps.push (appKey f x) (a.store.derOfView (.app f x))
                  (Idx.mk ETag.app Idx.tierP (UInt32.ofNat a.store.pers.apps.size))))
          else .error (.native "arena: expression constructor array full") := by
  simp only [internE, internNodeE, EStore.find?, EStore.intern, ETables.find?, Tbl.find?,
    ETables.sizeOf, ETables.push, StateT.run_bind, StateT.run_get, pure_bind, persFindMaybe_app]
  cases hp : pfA a f x <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.apps.cons[appKey f x]? <;>
    simp only [hp, hs, hc, Bool.false_eq_true, ↓reduceIte, appKey, ite_self] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrApps, withPersApps, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

attribute [store_grind] acnt nSlotsA

/-! ## The probe run -/

/-- The first `d` slots of the run from `x` hold nodes that do not match. -/
def ANoMatch (m : Mem) (t f a x : Word) (d : Nat) : Prop :=
  ∀ e < d, rdW (m.arr64 ASLOT) (walkW (nSlotsA m) x e * 2 + t) ≠ 0 ∧
    amatchW (m.arr64 AREC) t (rdW (m.arr64 ASLOT) (walkW (nSlotsA m) x e * 2 + t) - 1) f a = false

/-- What a result `rs` of the probe of tier `t` from slot `x` says (as `ProbeOK`). -/
def AProbeOK (m : Mem) (t f a x : Word) (rs : List Word) : Prop :=
  rs ≠ [] →
    (rs.headD 0 ≠ 0 → amatchW (m.arr64 AREC) t (rs.tail.headD 0) f a = true ∧
      rdW (m.arr64 ASLOT) (rs.tail.tail.headD 0 * 2 + t) = rs.tail.headD 0 + 1 ∧
      rdW (m.arr64 ASLOT) (rs.tail.tail.headD 0 * 2 + t) ≠ 0 ∧ rs.tail.tail.headD 0 < nSlotsA m) ∧
    (rs.headD 0 = 0 → rs.tail.tail.headD 0 = walkW (nSlotsA m) x (rs.tail.tail.tail.headD 0).toNat ∧
      rdW (m.arr64 ASLOT) (rs.tail.tail.headD 0 * 2 + t) = 0 ∧
      ANoMatch m t f a x (rs.tail.tail.tail.headD 0).toNat)

theorem aprobe_ok (m : Mem) (t f a x : Word) (hx : x < nSlotsA m) :
    ∀ (k : Nat) (d : Word), (nSlotsA m).toNat - d.toNat = k → ANoMatch m t f a x d.toNat →
      AProbeOK m t f a x (aprobeW (m.arr64 ASLOT) (m.arr64 AREC) t f a (nSlotsA m)
        (walkW (nSlotsA m) x d.toNat) d) := by
  intro k
  induction k with
  | zero => intro d hk _; rw [aprobeW]; grind [AProbeOK]
  | succ k ih =>
    intro d hk hnm
    have := ih (d + 1)
    clear ih
    have hd : d < nSlotsA m := by grind
    have hd1 : (d + 1).toNat = d.toNat + 1 := by grind
    specialize this (by grind)
    rw [hd1, walkW_succ] at this
    rw [aprobeW]
    by_cases h0 : rdW (m.arr64 ASLOT) (walkW (nSlotsA m) x d.toNat * 2 + t) = 0
    · simp only [hd, h0, ↓reduceIte]; grind [AProbeOK]
    by_cases hm : amatchW (m.arr64 AREC) t (rdW (m.arr64 ASLOT) (walkW (nSlotsA m) x d.toNat * 2 + t) - 1)
        f a
    · simp only [hd, h0, hm, ↓reduceIte]; grind [store_grind, AProbeOK]
    · simp only [hd, h0, hm, ↓reduceIte, Bool.false_eq_true]
      exact this (by grind [ANoMatch])

/-- The probe `app_find` makes, from the home slot. -/
theorem aprobe_home (m : Mem) (t f a : Word) :
    AProbeOK m t f a (homeW (appHashW f a) (nSlotsA m)) (aprobeW (m.arr64 ASLOT) (m.arr64 AREC) t f a
      (nSlotsA m) (homeW (appHashW f a) (nSlotsA m)) 0) := by
  by_cases hn : nSlotsA m = 0
  · rw [aprobeW]; simp [hn, AProbeOK]
  · exact aprobe_ok m t f a _ (homeW_lt _ _ (by grind)) _ 0 rfl (by simp [ANoMatch])

/-! ## The relation between L memory and the arena's `app` tables -/

/-- Node `i` of tier `t` holds the `app` node `k`: its two handle words. -/
def ARecRel (m : Mem) (t i : Word) (k : AppNode) : Prop :=
  rdW (m.arr64 AREC) (i * 4 + t * 2) = k.f.word.toUInt64 ∧
  rdW (m.arr64 AREC) (i * 4 + t * 2 + 1) = k.a.word.toUInt64

/-- The home slot of node `i` of tier `t`. -/
def ahome (m : Mem) (t i : Word) : Word :=
  homeW (appHashW (rdW (m.arr64 AREC) (i * 4 + t * 2)) (rdW (m.arr64 AREC) (i * 4 + t * 2 + 1)))
    (nSlotsA m)

/-- The slots of tier `t` index its `c` nodes, and node `i` lies on the run from its home slot,
after occupied slots. -/
def ASlotsOK (m : Mem) (t : Word) (c : Nat) : Prop :=
  (∀ j : Word, j < nSlotsA m → (rdW (m.arr64 ASLOT) (j * 2 + t)).toNat ≤ c) ∧
  ∀ i : Word, i.toNat < c → ∃ d : Nat,
    rdW (m.arr64 ASLOT) (walkW (nSlotsA m) (ahome m t i) d * 2 + t) = i + 1 ∧
    ∀ e < d, rdW (m.arr64 ASLOT) (walkW (nSlotsA m) (ahome m t i) e * 2 + t) ≠ 0

/-- Tier `t` of the L `app` store represents the arena table `tb` (as `TierRel`). -/
def ATierRel (m : Mem) (t : Word) (tb : Tbl AppNode EIdx UInt64) : Prop :=
  (acnt m t).toNat = tb.nodes.size ∧ tb.nodes.size ≤ 134217728 ∧
  4 * tb.nodes.size ≤ (m.arr64 AREC).size ∧
  (∀ (i : Word) k, tb.nodes[i.toNat]? = some k → ARecRel m t i k) ∧
  (∀ (i : Word) k, tb.nodes[i.toNat]? = some k → tb.cons[k]? = some (decE (hdW 4 t i))) ∧
  (∀ k x, tb.cons[k]? = some x → tb.nodes[(hix x).toNat]? = some k) ∧
  ASlotsOK m t tb.nodes.size

/-- **The state relation** of the `app` store: the scratch flag is the arena's, and both tiers
represent the arena's `app` tables. -/
def AppR (m : Mem) (a : AState) : Prop :=
  6 ≤ (m.arr64 CTL).size ∧ (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn ∧
  ATierRel m 0 a.store.pers.apps ∧ ATierRel m 1 a.store.scr.apps

/-! ## The memory after `app_push` -/

section push
variable (m : Mem) (t f a J c : Word)

@[store_grind =] theorem apm_size (b : ArrId) :
    ((apushMem m t f a J c).arr64 b).size = (m.arr64 b).size := by
  grind [apushMem, size_set64]

@[store_grind =] theorem apm_ctl (x : Word) :
    rdW ((apushMem m t f a J c).arr64 CTL) x =
      if x = 4 + t ∧ (4 + t).toNat < (m.arr64 CTL).size then c + 1 else rdW (m.arr64 CTL) x := by
  grind [apushMem, rdW_set64, size_set64]

@[store_grind =] theorem apm_slot (x : Word) :
    rdW ((apushMem m t f a J c).arr64 ASLOT) x =
      if x = J * 2 + t ∧ (J * 2 + t).toNat < (m.arr64 ASLOT).size then c + 1
      else rdW (m.arr64 ASLOT) x := by
  grind [apushMem, rdW_set64, size_set64]

@[store_grind =] theorem apm_rec (x : Word) (hc : (c * 4 + t * 2 + 1).toNat < (m.arr64 AREC).size)
    (hw : (c * 4 + t * 2).toNat + 1 < 2 ^ 64) :
    rdW ((apushMem m t f a J c).arr64 AREC) x =
      if x = c * 4 + t * 2 then f else if x = c * 4 + t * 2 + 1 then a
      else rdW (m.arr64 AREC) x := by
  grind [apushMem, rdW_set64, size_set64]

end push

/-- A node's relation depends only on its two words. -/
theorem ARecRel_frame (m m' : Mem) (t i : Word) (k : AppNode)
    (h0 : rdW (m'.arr64 AREC) (i * 4 + t * 2) = rdW (m.arr64 AREC) (i * 4 + t * 2))
    (h1 : rdW (m'.arr64 AREC) (i * 4 + t * 2 + 1) = rdW (m.arr64 AREC) (i * 4 + t * 2 + 1)) :
    ARecRel m' t i k = ARecRel m t i k := by
  simp only [ARecRel, h0, h1]

/-! ## Hit and miss -/

section tier
variable (m : Mem) (t : Word) (tb : Tbl AppNode EIdx UInt64) (hT : ATierRel m t tb)
  (f a : Word) (hf : f.toNat < 2 ^ 32) (ha : a.toNat < 2 ^ 32)

include hT hf ha in
/-- **Matching is equality of `app` nodes**, on a node of a represented tier. -/
theorem amatchW_iff (i : Word) (k : AppNode) (hk : tb.nodes[i.toNat]? = some k) :
    amatchW (m.arr64 AREC) t i f a = true ↔ k = appKey (decE f) (decE a) := by
  have hr := hT.2.2.2.1 i k hk
  have := word_decE k.f f hf
  have := word_decE k.a a ha
  obtain ⟨kf, ka⟩ := k
  grind [amatchW, ARecRel]

include hT hf ha in
/-- A probe hit is the arena's cons hit, at the same handle. -/
theorem atier_hit (x : Word) (rs : List Word) (hP : AProbeOK m t f a x rs) (hr : rs ≠ [])
    (hh : rs.headD 0 ≠ 0) :
    tb.cons[appKey (decE f) (decE a)]? = some (decE (hdW 4 t (rs.tail.headD 0))) := by
  have := amatchW_iff m t tb hT f a hf ha (rs.tail.headD 0)
  obtain ⟨-, -, -, -, hsome, -, ⟨hsl, -⟩⟩ := hT
  have := hsl (rs.tail.tail.headD 0)
  have := hsome (rs.tail.headD 0)
  clear hsl hsome
  grind [AProbeOK]

include hT hf ha in
/-- A probe miss from the home slot: the node is not in the tier. -/
theorem atier_miss (rs : List Word)
    (hP : AProbeOK m t f a (homeW (appHashW f a) (nSlotsA m)) rs) (hr : rs ≠ [])
    (hh : rs.headD 0 = 0) :
    tb.cons[appKey (decE f) (decE a)]? = none := by
  cases hc : tb.cons[appKey (decE f) (decE a)]? with
  | none => rfl
  | some x =>
    exfalso
    have := amatchW_iff m t tb hT f a hf ha (hix x)
    grind [AProbeOK, ATierRel, ASlotsOK, ANoMatch, amatchW, ahome]

include hT hf ha in
/-- `app_push` at the free slot the probe from the home slot stopped at represents the arena's
append. -/
theorem atier_push (ht : t ≤ 1) (rs : List Word)
    (hP : AProbeOK m t f a (homeW (appHashW f a) (nSlotsA m)) rs) (hr : rs ≠ [])
    (hh : rs.headD 0 = 0) (hok : apushOK m t = true) (hctl : 6 ≤ (m.arr64 CTL).size) (dd : UInt64) :
    ATierRel (apushMem m t f a (rs.tail.tail.headD 0) (acnt m t)) t
      (tb.push (appKey (decE f) (decE a)) dd (decE (hdW 4 t (acnt m t)))) := by
  have hmiss := atier_miss m t tb hT f a hf ha rs hP hr hh
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hrun⟩ := hT
  simp only [ATierRel, ASlotsOK, Tbl.push_nodes, Tbl.push_cons, Array.size_push]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear hrec hsome hback hsl hrun; grind [store_grind, apushOK]
  · clear hrec hsome hback hsl hrun; grind [store_grind, apushOK]
  · clear hrec hsome hback hsl hrun; grind [store_grind, apushOK]
  · intro i k hk
    rw [Array.getElem?_push] at hk
    split at hk
    · cases hk
      have : i = acnt m t := UInt64.toNat_inj.mp (by omega)
      subst this
      have hb : (acnt m t * 4 + t * 2 + 1).toNat < (m.arr64 AREC).size ∧
          (acnt m t * 4 + t * 2).toNat + 1 < 2 ^ 64 := by
        clear hrec hsome hback hsl hrun; grind [store_grind, apushOK]
      simp only [ARecRel, apm_rec _ _ _ _ _ _ _ hb.1 hb.2]
      have := word_decE (decE f) f hf
      have := word_decE (decE a) a ha
      clear hrec hsome hback hsl hrun
      grind
    · have := hrec i k hk
      rw [ARecRel_frame _ _ t i k]
      · exact this
      all_goals clear hrec hsome hback hsl hrun; grind [store_grind, apushOK]
  · intro i k hk
    clear hrec hback hsl hrun
    grind [store_grind, apushOK]
  · intro k x hk
    clear hrec hsome hsl hrun
    grind [store_grind, apushOK]
  · intro j hj
    clear hrec hsome hback hrun
    grind [store_grind, apushOK, AProbeOK]
  · intro i hi
    clear hsome hback hsl
    by_cases hic : i = acnt m t
    · subst hic
      refine ⟨(rs.tail.tail.tail.headD 0).toNat, ?_, ?_⟩
      · grind [store_grind, apushOK, AProbeOK, ahome]
      · grind [store_grind, apushOK, AProbeOK, ANoMatch, ahome]
    · obtain ⟨d, hd1, hd2⟩ := hrun i (by grind)
      have := hrec i
      have : ahome (apushMem m t f a (rs.tail.tail.headD 0) (acnt m t)) t i = ahome m t i := by
        clear hd1 hd2 hrec hrun; grind [store_grind, apushOK, ahome]
      refine ⟨d, ?_, ?_⟩
      · clear hrec hrun; grind [store_grind, apushOK, AProbeOK]
      · clear hrec hrun; grind [store_grind, apushOK, AProbeOK]

end tier

/-- Appending to tier `t` leaves the other tier represented. -/
theorem atier_other (m : Mem) (t t' f a J : Word) (ht : t ≤ 1) (ht' : t' ≤ 1) (hne : t' ≠ t)
    (tb : Tbl AppNode EIdx UInt64) (hT : ATierRel m t' tb) (hok : apushOK m t = true) :
    ATierRel (apushMem m t f a J (acnt m t)) t' tb := by
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hrun⟩ := hT
  refine ⟨?_, hcap, ?_, ?_, hsome, hback, ?_, ?_⟩
  · clear hrec hsome hback hsl hrun; grind [store_grind, apushOK]
  · clear hrec hsome hback hsl hrun; grind [store_grind, apushOK]
  · intro i k hk
    have := hrec i k hk
    rw [ARecRel_frame _ _ t' i k]
    · exact this
    all_goals clear hrec hsome hback hsl hrun; grind [store_grind, apushOK]
  · intro j hj
    clear hrec hsome hback hrun
    grind [store_grind, apushOK]
  · intro i hi
    obtain ⟨d, hd1, hd2⟩ := hrun i (by grind)
    have := hrec i
    clear hsome hback hsl hrun
    have : ahome (apushMem m t f a J (acnt m t)) t' i = ahome m t' i := by
      clear hd1 hd2 hrec; grind [store_grind, apushOK, ahome]
    refine ⟨d, ?_, ?_⟩
    · clear hrec; grind [store_grind, apushOK]
    · clear hrec; grind [store_grind, apushOK]


/-! ## The arena side, one equation per path -/

section arena
variable (f x : EIdx) (a : AState) (y : EIdx)

theorem internE_app_hitP (hs : skA a f x = false)
    (h0 : a.store.pers.apps.cons[appKey f x]? = some y) :
    (internE (.app f x)).run a = .ok (y, a) := by
  rw [internE_app_run]; simp [pfA, hs, h0]

theorem internE_app_hitS (h0 : pfA a f x = none) (hs : a.store.scratchOn = true)
    (h1 : a.store.scr.apps.cons[appKey f x]? = some y) :
    (internE (.app f x)).run a = .ok (y, a) := by
  rw [internE_app_run]; simp [h0, hs, h1]

theorem internE_app_pushS (h0 : pfA a f x = none) (hs : a.store.scratchOn = true)
    (h1 : a.store.scr.apps.cons[appKey f x]? = none)
    (hc : a.store.scr.apps.nodes.size < 134217728) :
    (internE (.app f x)).run a = .ok (decE (hdW 4 1 (UInt64.ofNat a.store.scr.apps.nodes.size)),
      withScrApps a (a.store.scr.apps.push (appKey f x) (a.store.derOfView (.app f x))
        (decE (hdW 4 1 (UInt64.ofNat a.store.scr.apps.nodes.size))))) := by
  rw [internE_app_run, show Idx.tierS = UInt32.ofNat 1 from rfl, mk_eq]
  simp [h0, hs, h1, Tbl.size, Idx.idxCap, hc, ETag.app]

theorem internE_app_pushP (h0 : pfA a f x = none) (hs : a.store.scratchOn = false)
    (hc : a.store.pers.apps.nodes.size < 134217728) :
    (internE (.app f x)).run a = .ok (decE (hdW 4 0 (UInt64.ofNat a.store.pers.apps.nodes.size)),
      withPersApps a (a.store.pers.apps.push (appKey f x) (a.store.derOfView (.app f x))
        (decE (hdW 4 0 (UInt64.ofNat a.store.pers.apps.nodes.size))))) := by
  rw [internE_app_run, show Idx.tierP = UInt32.ofNat 0 from rfl, mk_eq]
  simp [h0, hs, Tbl.size, Idx.idxCap, hc, ETag.app]

end arena

/-- The L skip test is the arena's. -/
theorem askipW_eq (m : Mem) (a : AState) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (askipW m f x = 0) = (skA a (decE f) (decE x) = false) := by
  have := bit27_or f x
  simp only [askipW, skA, isPersistent_decE f hf, isPersistent_decE x hx, ← hfl]
  grind

section with_
variable (a : AState) (t : Tbl AppNode EIdx UInt64)
@[store_grind =] theorem withScrApps_scr : (withScrApps a t).store.scr.apps = t := rfl
@[store_grind =] theorem withScrApps_pers : (withScrApps a t).store.pers.apps = a.store.pers.apps := rfl
@[store_grind =] theorem withScrApps_on : (withScrApps a t).store.scratchOn = a.store.scratchOn := rfl
@[store_grind =] theorem withPersApps_pers : (withPersApps a t).store.pers.apps = t := rfl
@[store_grind =] theorem withPersApps_scr : (withPersApps a t).store.scr.apps = a.store.scr.apps := rfl
@[store_grind =] theorem withPersApps_on :
    (withPersApps a t).store.scratchOn = a.store.scratchOn := rfl
end with_

/-- The memory after `app_push` relates to the arena's state after its append. -/
theorem AppR_push (m : Mem) (a a' : AState) (t f x J : Word) (ht : t ≤ 1) (hR : AppR m a)
    (hflag : a'.store.scratchOn = a.store.scratchOn)
    (h0 : ATierRel (apushMem m t f x J (acnt m t)) 0 a'.store.pers.apps)
    (h1 : ATierRel (apushMem m t f x J (acnt m t)) 1 a'.store.scr.apps) :
    AppR (apushMem m t f x J (acnt m t)) a' := by
  obtain ⟨hctl, hfl, -, -⟩ := hR
  refine ⟨?_, ?_, h0, h1⟩ <;> grind [store_grind]

/-! ## `intern_app` refines `internE (.app _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : AppR m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
  (hx : x.toNat < 2 ^ 32)

include hR hf hx in
/-- **`intern_app`'s model refines the arena's `internE` at an `app` node.** -/
theorem aintern_correct (w : Word) (m' : Mem) (hI : ainternW m f x = some (w, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a ∧
    AppR m' (AM.st (internE (.app (decE f) (decE x))) a) ∧
    AM.res (internE (.app (decE f) (decE x))) a = decE w := by
  obtain ⟨hctl, hflag, hT0, hT1⟩ := id hR
  have hP0 := aprobe_home m 0 f x
  have hP1 := aprobe_home m 1 f x
  have hit0 := atier_hit m 0 _ hT0 f x hf hx _ _ hP0
  have hit1 := atier_hit m 1 _ hT1 f x hf hx _ _ hP1
  have miss0 := atier_miss m 0 _ hT0 f x hf hx _ hP0
  have miss1 := atier_miss m 1 _ hT1 f x hf hx _ hP1
  have hsk := askipW_eq m a f x hf hx hflag
  simp only [ainternW] at hI
  split at hI
  · simp at hI
  split at hI
  · -- persistent hit
    obtain ⟨hok, hst, hres⟩ :=
      AM.of_run_ok _ _ _ _ (internE_app_hitP _ _ a _ (by grind) (hit0 (by grind) (by grind)))
    grind [appP, hdW]
  have hpf : pfA a (decE f) (decE x) = none := by grind [pfA]
  split at hI
  · split at hI
    · simp at hI
    split at hI
    · -- scratch hit
      obtain ⟨hok, hst, hres⟩ :=
        AM.of_run_ok _ _ _ _ (internE_app_hitS _ _ a _ hpf (by grind) (hit1 ‹_› ‹_›))
      grind [appS, hdW]
    split at hI
    · -- scratch append
      have hsz : a.store.scr.apps.nodes.size < 134217728 := by grind [apushOK, ATierRel]
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
        (internE_app_pushS _ _ a hpf (by grind) (miss1 ‹_› (by grind)) hsz)
      have e : UInt64.ofNat a.store.scr.apps.nodes.size = acnt m 1 := by grind [ATierRel]
      rw [e] at hst hres
      have hp1 := atier_push m 1 _ hT1 f x hf hx (by decide) _ hP1 ‹_› (by grind) ‹_› hctl
        (a.store.derOfView (.app (decE f) (decE x)))
      simp only [Option.some.injEq, Prod.mk.injEq] at hI
      obtain ⟨rfl, rfl⟩ := hI
      rw [hst, hres]
      refine ⟨hok, AppR_push m a _ 1 f x _ (by decide) hR rfl ?_ hp1, by grind [appS, hdW]⟩
      exact atier_other m 1 0 f x _ (by decide) (by decide) (by decide) _ hT0 ‹_›
    · simp at hI
  split at hI
  · -- persistent append
    have hsz : a.store.pers.apps.nodes.size < 134217728 := by grind [apushOK, ATierRel]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
      (internE_app_pushP _ _ a hpf (by grind) hsz)
    have e : UInt64.ofNat a.store.pers.apps.nodes.size = acnt m 0 := by grind [ATierRel]
    rw [e] at hst hres
    have hp0 := atier_push m 0 _ hT0 f x hf hx (by decide) _ hP0 (by grind [askipW]) (by grind [askipW]) ‹_› hctl
      (a.store.derOfView (.app (decE f) (decE x)))
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    rw [hst, hres]
    refine ⟨hok, AppR_push m a _ 0 f x _ (by decide) hR rfl hp0 ?_, by grind [appP, hdW]⟩
    exact atier_other m 0 1 f x _ (by decide) (by decide) (by decide) _ hT1 ‹_›
  · simp at hI

end intern

/-- `intern_app` refines `internE (.app _ _)` under `AppR`. -/
theorem internApp_refines (p : Prog) (hpf : p.lookup "app_find" = some appFind)
    (hpp : p.lookup "app_push" = some appPush) (hp : p.lookup "intern_app" = some internApp)
    (a₀ : AState) (n : Nat) (s₀ : St) (f x : Word) (hR : AppR s₀.mem a₀) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_app" [f, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.app (decE f) (decE x))) a₀ ∧
      AppR s'.mem (AM.st (internE (.app (decE f) (decE x))) a₀) ∧
      AM.res (internE (.app (decE f) (decE x))) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internApp_spec p hpf hpp hp n s₀ f x)
  subst hs
  exact ⟨hloc, aintern_correct s.mem a₀ hR f x hf hx _ _ hI⟩

end L.Arena
