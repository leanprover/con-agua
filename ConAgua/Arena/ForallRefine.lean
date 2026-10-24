import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.ForallStore

/-!
# The `forallE` store refines the arena's `forallE` tables

An instance of the store library (`StoreLib.lean`) for the binder record `BindNode { ty body :
EIdx }` (`ConAgua/Arena/ForallStore.lean` has the L code), `lam`'s other array, `app`'s shape (two
handle fields). The schema `forallSch` (`FAREC`, `FASLOT`, two words per node, counts at
`CTL[30 + t]`, tag `6`); the record relation `FaRecRel` (the two words are `ty`'s and `body`'s
handle words); the node hash `fahash` (`forallHashW` of the two words); the lens `forallLens`; the
scratch skip (`skFa`, `faskipW_eq`). `ForallR m a` is the library's `StoreR` for the two `forallE`
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

set_option linter.unusedSimpArgs false

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
    simp only [hp, hs, hc, faKey, ite_self, protoRun, forallLens] <;>
    (repeat' split) <;>
      first
      | rfl
      | simp_all [StateT.run_set, StateT.run_pure, withScrForalls, withPersForalls, fail,
          throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
          StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `forallE` tables -/

/-- The `forallE` schema: `FAREC`, `FASLOT`, two words per node, the counts at `CTL[30 + t]`. -/
def forallSch : Schema := ⟨FAREC, FASLOT, 2, 4, 30, ETag.forallE⟩

theorem forallSch_wf : forallSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_fa0 (m : Mem) (t i : Word) :
    fld forallSch m t i 0 = rdW (m.arr64 FAREC) (i * 4 + t * 2) := by
  simp [fld, Schema.ad, forallSch]
theorem fld_fa (m : Mem) (t i f : Word) :
    fld forallSch m t i f = rdW (m.arr64 FAREC) (i * 4 + t * 2 + f) := rfl

/-- Node `i` of tier `t` holds the `forallE` node `k`: its two handle words. -/
def FaRecRel (m : Mem) (t i : Word) (k : BindNode) : Prop :=
  rdW (m.arr64 FAREC) (i * 4 + t * 2) = k.ty.word.toUInt64 ∧
  rdW (m.arr64 FAREC) (i * 4 + t * 2 + 1) = k.body.word.toUInt64

/-- **The state relation** of the `forallE` store: the library's relation for the two `forallE`
tables. -/
def ForallR (m : Mem) (a : AState) : Prop :=
  ConsR forallCS FaRecRel m a.store.scratchOn a.store.pers.foralls a.store.scr.foralls

/-- A node's relation and hash depend only on its two words. -/
theorem faFrame : RFrame forallSch FaRecRel fahash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_fa0, fld_fa0] at h0
  rw [fld_fa, fld_fa] at h1
  exact ⟨fun a h => by simpa only [FaRecRel, h0, h1] using h, by simp only [fahash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `forall_find` on node `i` of tier `t`. -/
def faMt (m : Mem) (ty body t i : Word) : Bool := famatchW (m.arr64 FAREC) t i ty body

section query
variable (m : Mem) (ty body : Word) (hty : ty.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32)

include hty hbody in
/-- **Matching is equality of `forallE` nodes.** -/
theorem faMatchOK : MatchOK FaRecRel (faMt m ty body) m (faKey (decE ty) (decE body)) := by
  intro t i k hr
  have := word_decI k.ty ty hty
  have := word_decI k.body body hbody
  obtain ⟨kty, kbody⟩ := k
  grind [faMt, famatchW, FaRecRel, decE_eq]

theorem faHomeOK : HomeOK fahash (faMt m ty body) m (forallHashW ty body) := by
  intro t i hm
  simp only [faMt, famatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [fahash, hm.1, hm.2]

include hty hbody in
/-- The record `forall_push` writes holds the node. -/
theorem faNewOK :
    NewOKR forallSch FaRecRel fahash m [ty, body] (faKey (decE ty) (decE body))
      (forallHashW ty body) := by
  intro t ht hroom
  have e : ∀ g, g < 2 → fld forallSch (recW forallSch m t [ty, body]) t
      (cntW forallSch m t) g = [ty, body].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_recW forallSch forallSch_wf] <;> simp only [forallSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_fa0] at e0
  rw [fld_fa] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decE ty) ty hty
  have := word_decI (decE body) body hbody
  simp only [FaRecRel, fahash, faKey, e0, e1]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem fapushOK_room (m : Mem) (t : Word) (h : fapushOK m t = true) : PushRoom forallSch m t := by
  simp only [fapushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 FAREC) 2
  simp only [PushRoom, cntW, facnt, forallSch, len64_eq] at *
  grind

/-- **The `forall` table's shape.** -/
theorem forallCS_wf : forallCS.WF where
  sch := forallSch_wf
  P := by decide
  S := by decide
  col A h := by simp [forallCS] at h
  colRoom A h := by simp [forallCS] at h
  room m t h := (fapushOK_room m t ((fapushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, forallCS, hk]

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

/-- `intern_forall` refines `internE (.forallE _ _)` under `ForallR`. -/
theorem internForall_refines (p : Prog) (hpf : p.lookup "forall_find" = some forallFind)
    (hpp : p.lookup "forall_push" = some forallPush)
    (hp : p.lookup "intern_forall" = some internForallL) (a₀ : AState) (n : Nat) (s₀ : St)
    (ty body : Word) (hR : ForallR s₀.mem a₀) (hty : ty.toNat < 2 ^ 32)
    (hbody : body.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_forall" [ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.forallE (decE ty) (decE body))) a₀ ∧
      ForallR s'.mem (AM.st (internE (.forallE (decE ty) (decE body))) a₀) ∧
      AM.res (internE (.forallE (decE ty) (decE body))) a₀ = decE (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internForallL_spec p hpf hpp hp n s₀ ty body)
    (Sim.ofOkD (faintern_correct s₀.mem a₀ hR ty body hty hbody))

end L.Arena
