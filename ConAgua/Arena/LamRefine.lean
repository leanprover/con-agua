import ConAgua.Arena.StoreLib
import ConAgua.Arena.SimLib
import ConAgua.Arena.LamStore

/-!
# The `lam` store refines the arena's `lam` tables

An instance of the store library (`StoreLib.lean`) for the binder record `BindNode { ty body :
EIdx }` (`ConAgua/Arena/LamStore.lean` has the L code), `app`'s shape (two handle fields). The
schema `lamSch` (`LAREC`, `LASLOT`, two words per node, counts at `CTL[28 + t]`, tag `5`); the
record relation `LaRecRel` (the two words are `ty`'s and `body`'s handle words); the node hash
`lahash` (`lamHashW` of the two words); the lens `lamLens`; the scratch skip (`skLa`,
`laskipW_eq`). `LamR m a` is the library's `StoreR` for the two `lam` tables.

**The one new thing** (`internE_lam_run`): unlike `app`, `internE` at `lam` does not go through
`internNodeE`; it is `internLamE` (`ConRon/Arena/Monad.lean`), which probes with
`EStore.findBind ETag.lam ty b` (`persFindBindMaybe` with skip `bindHasScratchChild`, then the
scratch `ETables.findBind` if the scratch tier is open), tests `bindSizeOf` at the tier the append
goes to, then calls `EStore.internLam = EStore.internBind ETag.lam`, which **re-probes** (the same
`persFindBindMaybe`/`findBind`, on the same store, so the same `none`) and pushes via
`ETables.pushBind`. The unfolding proof needs one more case split than `app`'s (`internE_app_run`)
for this re-probe, and `ETables.pushBind`'s own `if tag == ETag.lam` arm (always taken here, `rfl`
through `ETag.lam == ETag.lam`); otherwise the two theorems are the same shape.

`internLam_refines`: `intern_lam(ty, body)` refines `internE (.lam (decE ty) (decE body))` under
`LamR`.

Not represented: the derived column (`derOfBindAt`, through `mixHash`) and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `lam` cons key. -/
abbrev laKey (ty body : EIdx) : BindNode := ⟨ty, body⟩

/-- `a` with the scratch / persistent `lam` table replaced. -/
def withScrLams (a : AState) (t : Tbl BindNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with lams := t } } }
def withPersLams (a : AState) (t : Tbl BindNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with lams := t } } }

/-- The arena's two `lam` tables. -/
def lamLens : Lens BindNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.lams
  getS a := a.store.scr.lams
  setP := withPersLams
  setS := withScrLams
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- The arena's scratch skip at a `lam` record (`EStore.bindHasScratchChild`). -/
def skLa (a : AState) (ty body : EIdx) : Bool :=
  if a.store.scratchOn then (if ty.isPersistent then !body.isPersistent else true) else false

/-- The arena's persistent probe at a `lam` record, after the skip. -/
def pfLa (a : AState) (ty body : EIdx) : Option EIdx :=
  if skLa a ty body then none else a.store.pers.lams.cons[laKey ty body]?

theorem persFindBindMaybe_lam (a : AState) (ty body : EIdx) :
    a.store.persFindBindMaybe ETag.lam ⟨ty, body⟩ = pfLa a ty body := by
  simp [EStore.persFindBindMaybe, pfLa, skLa, EStore.bindHasScratchChild, laKey, ETables.findBind,
    Tbl.find?]

/-- `internE` at a `lam` node is the library's protocol, the persistent probe after the skip.
Unlike `app` (`internE_app_run`), `internLamE` probes with `EStore.findBind`, tests the capacity
at the tier the append goes to, then calls `EStore.internLam`, which **re-probes** the same store
(so the same answer, `none`, on this path) before it pushes: the proof needs one more case split
on the re-probe than `app`'s, and `ETables.pushBind`'s own `if tag == ETag.lam` (always taken). -/
theorem internE_lam_run (ty b : EIdx) (a : AState) :
    (internE (.lam ty b)).run a =
      protoRun lamLens (laKey ty b) ETag.lam (pfLa a ty b) (a.store.derOfBindAt 19 ty b)
        (.native "arena: expression constructor array full") a := by
  simp only [internE, internLamE, EStore.findBind, EStore.internLam, EStore.internBind,
    ETables.findBind, ETables.bindSizeOf, ETables.pushBind, Tbl.find?, StateT.run_bind,
    StateT.run_get, pure_bind, persFindBindMaybe_lam]
  cases hp : pfLa a ty b <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.lams.cons[laKey ty b]? <;>
    simp only [hp, hs, hc, laKey, ite_self, protoRun, lamLens] <;>
    (repeat' split) <;>
      first
      | rfl
      | simp_all [StateT.run_set, StateT.run_pure, withScrLams, withPersLams, fail,
          throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
          StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `lam` tables -/

/-- The `lam` schema: `LAREC`, `LASLOT`, two words per node, the counts at `CTL[28 + t]`. -/
def lamSch : Schema := ⟨LAREC, LASLOT, 2, 4, 28, ETag.lam⟩

theorem lamSch_wf : lamSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_la0 (m : Mem) (t i : Word) :
    fld lamSch m t i 0 = rdW (m.arr64 LAREC) (i * 4 + t * 2) := by
  simp [fld, Schema.ad, lamSch]
theorem fld_la (m : Mem) (t i f : Word) :
    fld lamSch m t i f = rdW (m.arr64 LAREC) (i * 4 + t * 2 + f) := rfl

/-- Node `i` of tier `t` holds the `lam` node `k`: its two handle words. -/
def LaRecRel (m : Mem) (t i : Word) (k : BindNode) : Prop :=
  rdW (m.arr64 LAREC) (i * 4 + t * 2) = k.ty.word.toUInt64 ∧
  rdW (m.arr64 LAREC) (i * 4 + t * 2 + 1) = k.body.word.toUInt64

/-- **The state relation** of the `lam` store: the library's relation for the two `lam` tables. -/
def LamR (m : Mem) (a : AState) : Prop :=
  StoreR lamSch LaRecRel lahash m a.store.scratchOn a.store.pers.lams a.store.scr.lams

/-- A node's relation and hash depend only on its two words. -/
theorem laFrame : RFrame lamSch LaRecRel lahash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_la0, fld_la0] at h0
  rw [fld_la, fld_la] at h1
  exact ⟨fun a h => by simpa only [LaRecRel, h0, h1] using h, by simp only [lahash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `lam_find` on node `i` of tier `t`. -/
def laMt (m : Mem) (ty body t i : Word) : Bool := lamatchW (m.arr64 LAREC) t i ty body

section query
variable (m : Mem) (ty body : Word) (hty : ty.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32)

include hty hbody in
/-- **Matching is equality of `lam` nodes.** -/
theorem laMatchOK : MatchOK LaRecRel (laMt m ty body) m (laKey (decE ty) (decE body)) := by
  intro t i k hr
  have := word_decI k.ty ty hty
  have := word_decI k.body body hbody
  obtain ⟨kty, kbody⟩ := k
  grind [laMt, lamatchW, LaRecRel, decE_eq]

theorem laHomeOK : HomeOK lahash (laMt m ty body) m (lamHashW ty body) := by
  intro t i hm
  simp only [laMt, lamatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [lahash, hm.1, hm.2]

include hty hbody in
/-- The record `lam_push` writes holds the node. -/
theorem laNewOK :
    NewOK lamSch LaRecRel lahash m [ty, body] (laKey (decE ty) (decE body)) (lamHashW ty body) := by
  intro t j ht hroom
  have e : ∀ g, g < 2 → fld lamSch (pushG lamSch m t [ty, body] j (cntW lamSch m t)) t
      (cntW lamSch m t) g = [ty, body].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_pushG lamSch lamSch_wf] <;> simp only [lamSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_la0] at e0
  rw [fld_la] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decE ty) ty hty
  have := word_decI (decE body) body hbody
  simp only [LaRecRel, lahash, laKey, e0, e1]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem laprobeW_arm (m : Mem) (ty body t : Word) :
    ∀ j d, laprobeW (m.arr64 LASLOT) (m.arr64 LAREC) t ty body (baseW m t) (nSlotsLa m) j d =
      probeArm lamSch m t (laMt m ty body t) (laprobeW (m.arr64 LASLOT) (m.arr64 LAREC) t ty body
        (baseW m t) (nSlotsLa m)) j d := by
  intro j d; rw [laprobeW, cprobeW]; rfl

theorem lapushOK_room (m : Mem) (t : Word) (h : lapushOK m t = true) : PushRoom lamSch m t := by
  simp only [lapushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 LAREC) 2
  simp only [PushRoom, cntW, lacnt, lamSch, len64_eq] at *
  grind

theorem lapushMem_eq (m : Mem) (t ty body j c : Word) :
    lapushMem m t ty body j c = pushG lamSch m t [ty, body] j c := by
  simp [lapushMem, pushG, wrRec, Schema.ad, lamSch]

theorem lainternW_eq (m : Mem) (ty body : Word) :
    lainternW m ty body = internM lamSch m (laskipW m ty body) (lapushOK m) [ty, body]
      (laprobeW (m.arr64 LASLOT) (m.arr64 LAREC) 0 ty body (baseW m 0) (nSlotsLa m)
        (homeW (lamHashW ty body) (nSlotsLa m)) 0)
      (laprobeW (m.arr64 LASLOT) (m.arr64 LAREC) 1 ty body (baseW m 1) (nSlotsLa m)
        (homeW (lamHashW ty body) (nSlotsLa m)) 0)
      lahash := by
  have e0 : ∀ x, hdW lamSch.tag.toUInt64 0 x = lamP + x := fun x => by
    simp [hdW, lamSch, lamP, ETag.lam]
  have e1 : ∀ x, hdW lamSch.tag.toUInt64 1 x = lamS + x := fun x => by
    simp [hdW, lamSch, lamS, ETag.lam]
  have ep : ∀ t, pushOKC lamCS m t = lapushOK m t := fun t => (lapushOK_eqC m t).symm
  have em : ∀ t j c, pushMC lamCS m t (lamCS.vsM (pushArgs lamCS [ty, body] (lamHashW ty body))) j c =
      pushG lamSch m t [ty, body] j c := by
    intro t j c; rw [← lapushMem_eq, lapushMem_eqC]; rfl
  have ec : ∀ t, cntC lamCS m t = cntW lamSch m t := fun t => rfl
  have eh : lamCS.qhM m [ty, body] = lamHashW ty body := rfl
  simp only [lainternW, consInternM, internM, pushM, pushC, ep, em, ec, e0, e1, eh]
  rfl

/-- The L skip test is the arena's. -/
theorem laskipW_eq (m : Mem) (a : AState) (ty body : Word) (hty : ty.toNat < 2 ^ 32)
    (hbody : body.toNat < 2 ^ 32) (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (laskipW m ty body = 0) = (skLa a (decE ty) (decE body) = false) := by
  have := bit27_or ty body
  simp only [laskipW, skLa, isPersistent_decE ty hty, isPersistent_decE body hbody, ← hfl]
  grind

/-! ## `intern_lam` refines `internE (.lam _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : LamR m a) (ty body : Word) (hty : ty.toNat < 2 ^ 32)
  (hbody : body.toNat < 2 ^ 32)

include hR hty hbody in
/-- **`intern_lam`'s model refines the arena's `internE` at a `lam` node.** -/
theorem laintern_correct (w : Word) (m' : Mem) (hI : lainternW m ty body = some (w, m')) :
    AM.ok (internE (.lam (decE ty) (decE body))) a ∧
    LamR m' (AM.st (internE (.lam (decE ty) (decE body))) a) ∧
    AM.res (internE (.lam (decE ty) (decE body))) a = decE w := by
  rw [lainternW_eq] at hI
  exact intern_correctG lamSch LaRecRel lahash lamSch_wf laFrame lamLens a m hR _ _ _ _ _
    (internE_lam_run _ _ a) (skLa a (decE ty) (decE body)) rfl _
    (laskipW_eq m a ty body hty hbody hR.2.1)
    (fun h => by simp only [skLa] at h; split at h <;> simp_all [lamLens]) _ _
    (laMatchOK m ty body hty hbody) (laHomeOK m ty body) _ _
    (probe_homeG lamSch m 0 _ _ (laprobeW_arm m ty body 0) _)
    (probe_homeG lamSch m 1 _ _ (laprobeW_arm m ty body 1) _) _ (lapushOK_room m) _ rfl
    (laNewOK m ty body hty hbody) w m' hI

end intern

/-- `intern_lam` refines `internE (.lam _ _)` under `LamR`. -/
theorem internLam_refines (p : Prog) (hpf : p.lookup "lam_find" = some lamFind)
    (hpp : p.lookup "lam_push" = some lamPush) (hp : p.lookup "intern_lam" = some internLamL)
    (a₀ : AState) (n : Nat) (s₀ : St) (ty body : Word) (hR : LamR s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lam" [ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.lam (decE ty) (decE body))) a₀ ∧
      LamR s'.mem (AM.st (internE (.lam (decE ty) (decE body))) a₀) ∧
      AM.res (internE (.lam (decE ty) (decE body))) a₀ = decE (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internLamL_spec p hpf hpp hp n s₀ ty body)
    (Sim.ofOkD (laintern_correct s₀.mem a₀ hR ty body hty hbody))

end L.Arena
