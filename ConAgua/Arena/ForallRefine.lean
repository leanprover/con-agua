import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.ForallStore

/-!
# The `forallE` store refines the arena's `forallE` tables

An instance of the store library (`StoreLib.lean`) for the binder record `BindNode { ty body :
EIdx }` (`ConAgua/Arena/ForallStore.lean` has the L code), `lam`'s other array, `app`'s shape (two
handle fields). The schema `forallSch` (`FAREC`, `FASLOT`, one packed word per node, counts at
`CTL[30 + t]`, tag `6`); the record relation `FaRecRel` (the two halves of the word are `ty`'s and `body`'s
handle words); the node hash `fahash` (`forallHashW` of the two halves); the lens `forallLens`; the
scratch skip (`skFa`, `faskipW_eq`). `ForallR m a` is the library's `ConsR` for the two `forallE`
tables.

As `lam`, `internE` at `forallE` does not go through `internNodeE`; it is `internForallEE`
(`ConRon/Arena/Monad.lean`), which probes with `EStore.findBind ETag.forallE ty b`
(`persFindBindMaybe`/`bindHasScratchChild`, then the scratch `ETables.findBind` if open), tests
`bindSizeOf` at the tier the append goes to, then calls `EStore.internForallE =
EStore.internBind ETag.forallE`, which re-probes and pushes via `ETables.pushBind` — `lam`'s
`internE_lam_run` reasoning (`LamRefine.lean`), at `ETag.forallE` and the `foralls` table.

`internForall_refines`: `intern_forall(ty, body)` refines `internE (.forallE (decE ty) (decE
body))` under `ForallR`.

Not represented: the derived column (`derOfBindAt`, through `mixHash`) and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `forallE` cons key. -/
abbrev faKey (ty body : EIdx) : BindNode := ⟨ty, body⟩

/-- `a` with the scratch / persistent `forallE` table replaced. -/
def withScrForalls (a : AState) (t : Tbl BindNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with foralls := t } } }
def withPersForalls (a : AState) (t : Tbl BindNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with foralls := t } } }

/-- The arena's two `forallE` tables. -/
def forallLens : Lens BindNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.foralls
  getS a := a.store.scr.foralls
  setP := withPersForalls
  setS := withScrForalls
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- The arena's scratch skip at a `forallE` record (`EStore.bindHasScratchChild`). -/
def skFa (a : AState) (ty body : EIdx) : Bool :=
  if a.store.scratchOn then (if ty.isPersistent then !body.isPersistent else true) else false

/-- The arena's persistent probe at a `forallE` record, after the skip. -/
def pfFa (a : AState) (ty body : EIdx) : Option EIdx :=
  if skFa a ty body then none else a.store.pers.foralls.cons[faKey ty body]?

/-- `ETag.forallE` is not `ETag.lam`: collapses the `if tag == ETag.lam` arms of
`ETables.findBind`/`bindSizeOf`/`pushBind` at tag `ETag.forallE` to their `forallE` branch. -/
theorem forallE_ne_lam : (ETag.forallE == ETag.lam) = false := by decide

theorem persFindBindMaybe_forall (a : AState) (ty body : EIdx) :
    a.store.persFindBindMaybe ETag.forallE ⟨ty, body⟩ = pfFa a ty body := by
  simp [EStore.persFindBindMaybe, pfFa, skFa, EStore.bindHasScratchChild, faKey,
    ETables.findBind, Tbl.find?, forallE_ne_lam]

/-- `internE` at a `forallE` node is the library's protocol, the persistent probe after the skip.
`lam`'s `internE_lam_run` (`LamRefine.lean`) reasoning, at `ETag.forallE` and `foralls`. -/
theorem internE_forall_run (ty b : EIdx) (a : AState) :
    (internE (.forallE ty b)).run a =
      protoRun forallLens (faKey ty b) ETag.forallE (pfFa a ty b) (a.store.derOfBindAt 23 ty b)
        (.native "arena: expression constructor array full") a := by
  simp only [internE, internForallEE, EStore.findBind, EStore.internForallE, EStore.internBind,
    ETables.findBind, ETables.bindSizeOf, ETables.pushBind, Tbl.find?, StateT.run_bind,
    StateT.run_get, pure_bind, persFindBindMaybe_forall, forallE_ne_lam]
  cases hp : pfFa a ty b <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.foralls.cons[faKey ty b]? <;>
    simp only [hs, hc, faKey, ite_self, protoRun, forallLens] <;>
    (repeat' split) <;>
      first
      | rfl
      | simp_all [withScrForalls, withPersForalls, fail,
          throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
          StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `forallE` tables -/

/-- The `forallE` schema: `FAREC`, `FASLOT`, one packed word per node, the counts at `CTL[30 + t]`. -/
def forallSch : Schema := ⟨FAREC, FASLOT, 1, 30, ETag.forallE⟩

theorem forallSch_wf : forallSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_fa0 (m : Mem) (t i : Word) :
    fld forallSch m t i 0 = rdW (m.arr64 (tierA FAREC t)) i := by
  simp [fld, Schema.ad, forallSch]

/-- Node `i` of tier `t` holds the `forallE` node `k`: its two handle words. -/
def FaRecRel (m : Mem) (t i : Word) (k : BindNode) : Prop :=
  tfld m FORALL t i 0 = k.ty.word.toUInt64 ∧
  tfld m FORALL t i 1 = k.body.word.toUInt64

/-- `FaRecRel` in the raw words (inside the store library). -/
theorem FaRecRel_raw (m : Mem) (t i : Word) (k : BindNode) :
    FaRecRel m t i k ↔
    rdW (m.arr64 (tierA FAREC t)) i &&& 4294967295 = k.ty.word.toUInt64 ∧
    rdW (m.arr64 (tierA FAREC t)) i >>> 32 = k.body.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `forallE` store: the library's relation for the two `forallE`
tables. -/
def ForallR (m : Mem) (a : AState) : Prop :=
  ConsR forallCS FaRecRel m a.store.scratchOn a.store.pers.foralls a.store.scr.foralls

/-- A node's relation and hash depend only on its record word. -/
theorem faFrame : RFrame forallSch FaRecRel fahash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_fa0, fld_fa0] at h0
  exact ⟨fun a h => by simpa only [FaRecRel_raw, h0] using h, by simp only [fahash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `forall_find` on node `i` of tier `t`. -/
def faMt (m : Mem) (ty body t i : Word) : Bool := famatchW (m.arr64 (tierA FAREC t)) t i ty body

section query
variable (m : Mem) (ty body : Word) (hty : ty.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32)

include hty hbody in
/-- **Matching is equality of `forallE` nodes.** -/
theorem faMatchOK : MatchOK FaRecRel (faMt m ty body) m (faKey (decE ty) (decE body)) := by
  intro t i k hr
  have := word_decI k.ty ty hty
  have := word_decI k.body body hbody
  obtain ⟨kty, kbody⟩ := k
  grind [faMt, famatchW, FaRecRel_raw, decE_eq]

theorem faHomeOK : HomeOK fahash (faMt m ty body) m (forallHashW ty body) := by
  intro t i hm
  simp only [faMt, famatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [fahash, hm.1, hm.2]

include hty hbody in
/-- The record `forall_push` writes holds the node. -/
theorem faNewOK :
    NewOKR forallSch FaRecRel fahash m [ty ||| body <<< 32] (faKey (decE ty) (decE body))
      (forallHashW ty body) := by
  intro t ht hroom _
  have e0 : fld forallSch (newRecM forallSch m t [ty ||| body <<< 32]) t (cntW forallSch m t) 0 =
      ty ||| body <<< 32 := by
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM forallSch forallSch_wf] <;> simp only [forallSch, Schema.ad] at * <;> grind
  rw [fld_fa0] at e0
  have := word_decI (decE ty) ty hty
  have := word_decI (decE body) body hbody
  simp only [FaRecRel_raw, fahash, faKey, e0, pack_lo ty body hty hbody, pack_hi ty body hty hbody]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem fapushOK_room (m : Mem) (t : Word) (h : fapushOK m t = true) : PushRoom forallSch m t := by
  simp only [fapushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, facnt, forallSch, len64_eq] at *
  grind

/-- **The `forall` table's shape.** -/
theorem forallCS_wf : forallCS.WF where
  sch := forallSch_wf
  P := by decide
  S := by decide
  col A h := by simp [forallCS] at h
  colRoom A h := by simp [forallCS] at h
  colLt A h := by
    simp only [forallCS, reduceCtorEq] at h; (try subst h); (try decide)
  room m t h := (fapushOK_room m t ((fapushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, forallCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun _ => rfl
    mt := by
      intro m ks h t i hl
      obtain ⟨a, b, rfl⟩ := list_two ks (by simpa [forallCS] using hl)
      simp [forallCS, famatchW, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ]
    hs := by intro m t i; simp [forallCS, famatchW, fahash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ]
    qh := fun _ _ _ => rfl
    vs := by
      intro ks h hl f hf
      simp only [nkW, forallCS, ↓reduceIte, Nat.lt_one_iff] at hf
      subst hf; simp [pushArgs, forallCS, recK, kwQ] }

/-- The L skip test is the arena's. -/
theorem faskipW_eq (m : Mem) (a : AState) (ty body : Word) (hty : ty.toNat < 2 ^ 32)
    (hbody : body.toNat < 2 ^ 32) (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (faskipW m ty body = 0) = (skFa a (decE ty) (decE body) = false) := by
  have := bit27_or ty body
  simp only [faskipW, skFa, isPersistent_decE ty hty, isPersistent_decE body hbody, ← hfl]
  grind

/-! ## `intern_forall` refines `internE (.forallE _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : ForallR m a) (ty body : Word) (hty : ty.toNat < 2 ^ 32)
  (hbody : body.toNat < 2 ^ 32)

include hR hty hbody in
/-- **`intern_forall`'s model refines the arena's `internE` at a `forallE` node.** -/
theorem faintern_correct (w : Word) (m' : Mem) (hI : fainternW m ty body = some (w, m')) :
    AM.ok (internE (.forallE (decE ty) (decE body))) a ∧
    ForallR m' (AM.st (internE (.forallE (decE ty) (decE body))) a) ∧
    AM.res (internE (.forallE (decE ty) (decE body))) a = decE w :=
  consIntern_correct forallCS_wf faFrame (colFree_none _ rfl) forallLens a hR _ _ _ _ _
    (internE_forall_run _ _ a) (skFa a (decE ty) (decE body)) rfl [ty, body]
    (faskipW_eq m a ty body hty hbody (ConsR.flag hR))
    (fun h => by simp only [skFa] at h; split at h <;> simp_all [forallLens])
    ⟨rfl, faMatchOK m ty body hty hbody, faHomeOK m ty body, faNewOK m ty body hty hbody⟩ w m' hI

end intern

end L.Arena
