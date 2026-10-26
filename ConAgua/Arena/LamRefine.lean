import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.LamStore

/-!
# The `lam` store refines the arena's `lam` tables

An instance of the store library (`StoreLib.lean`) for the binder record `BindNode { ty body :
EIdx }` (`ConAgua/Arena/LamStore.lean` has the L code), `app`'s shape (two handle fields). The
schema `lamSch` (`LAREC`, `LASLOT`, one packed word per node, counts at `CTL[28 + t]`, tag `5`); the
record relation `LaRecRel` (the two halves of the word are `ty`'s and `body`'s handle words); the node hash
`lahash` (`lamHashW` of the two halves); the lens `lamLens`; the scratch skip (`skLa`,
`laskipW_eq`). `LamR m a` is the library's `ConsR` for the two `lam` tables.

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
    simp only [hs, hc, laKey, protoRun, lamLens] <;>
    (repeat' split) <;>
      first
      | rfl
      | simp_all [withScrLams, withPersLams, fail,
          throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
          StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `lam` tables -/

/-- The `lam` schema: `LAREC`, `LASLOT`, one packed word per node, the counts at `CTL[28 + t]`. -/
def lamSch : Schema := ⟨LAREC, LASLOT, 1, 28, ETag.lam⟩

theorem lamSch_wf : lamSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_la0 (m : Mem) (t i : Word) :
    fld lamSch m t i 0 = rdW (m.arr64 (tierA LAREC t)) i := by
  simp [fld, Schema.ad, lamSch]

/-- Node `i` of tier `t` holds the `lam` node `k`: its two handle words. -/
def LaRecRel (m : Mem) (t i : Word) (k : BindNode) : Prop :=
  tfld m LAM t i 0 = k.ty.word.toUInt64 ∧
  tfld m LAM t i 1 = k.body.word.toUInt64

/-- `LaRecRel` in the raw words (inside the store library). -/
theorem LaRecRel_raw (m : Mem) (t i : Word) (k : BindNode) :
    LaRecRel m t i k ↔
    rdW (m.arr64 (tierA LAREC t)) i &&& 4294967295 = k.ty.word.toUInt64 ∧
    rdW (m.arr64 (tierA LAREC t)) i >>> 32 = k.body.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `lam` store: the library's relation for the two `lam` tables. -/
def LamR (m : Mem) (a : AState) : Prop :=
  ConsR lamCS LaRecRel m a.store.scratchOn a.store.pers.lams a.store.scr.lams

/-- A node's relation and hash depend only on its record word. -/
theorem laFrame : RFrame lamSch LaRecRel lahash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_la0, fld_la0] at h0
  exact ⟨fun a h => by simpa only [LaRecRel_raw, h0] using h, by simp only [lahash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `lam_find` on node `i` of tier `t`. -/
def laMt (m : Mem) (ty body t i : Word) : Bool := lamatchW (m.arr64 (tierA LAREC t)) t i ty body

section query
variable (m : Mem) (ty body : Word) (hty : ty.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32)

include hty hbody in
/-- **Matching is equality of `lam` nodes.** -/
theorem laMatchOK : MatchOK LaRecRel (laMt m ty body) m (laKey (decE ty) (decE body)) := by
  intro t i k hr
  have := word_decI k.ty ty hty
  have := word_decI k.body body hbody
  obtain ⟨kty, kbody⟩ := k
  grind [laMt, lamatchW, LaRecRel_raw, decE_eq]

theorem laHomeOK : HomeOK lahash (laMt m ty body) m (lamHashW ty body) := by
  intro t i hm
  simp only [laMt, lamatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [lahash, hm.1, hm.2]

include hty hbody in
/-- The record `lam_push` writes holds the node. -/
theorem laNewOK :
    NewOKR lamSch LaRecRel lahash m [ty ||| body <<< 32] (laKey (decE ty) (decE body)) (lamHashW ty body) := by
  intro t ht hroom _
  have e0 : fld lamSch (newRecM lamSch m t [ty ||| body <<< 32]) t (cntW lamSch m t) 0 =
      ty ||| body <<< 32 := by
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM lamSch lamSch_wf] <;> simp only [lamSch, Schema.ad] at * <;> grind
  rw [fld_la0] at e0
  have := word_decI (decE ty) ty hty
  have := word_decI (decE body) body hbody
  simp only [LaRecRel_raw, lahash, laKey, e0, pack_lo ty body hty hbody, pack_hi ty body hty hbody]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem lapushOK_room (m : Mem) (t : Word) (h : lapushOK m t = true) : PushRoom lamSch m t := by
  simp only [lapushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, lacnt, lamSch, len64_eq] at *
  grind

/-- **The `lam` table's shape.** -/
theorem lamCS_wf : lamCS.WF where
  sch := lamSch_wf
  P := by decide
  S := by decide
  col A h := by simp [lamCS] at h
  colRoom A h := by simp [lamCS] at h
  colLt A h := by
    simp only [lamCS, reduceCtorEq] at h; (try subst h); (try decide)
  room m t h := (lapushOK_room m t ((lapushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, lamCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun _ => rfl
    mt := by
      intro m ks h t i hl
      obtain ⟨a, b, rfl⟩ := list_two ks (by simpa [lamCS] using hl)
      simp [lamCS, lamatchW, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ]
    hs := by intro m t i; simp [lamCS, lamatchW, lahash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ]
    qh := fun _ _ _ => rfl
    vs := by
      intro ks h hl f hf
      simp only [nkW, lamCS, ↓reduceIte, Nat.lt_one_iff] at hf
      subst hf; simp [pushArgs, lamCS, recK, kwQ] }

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
    AM.res (internE (.lam (decE ty) (decE body))) a = decE w :=
  consIntern_correct lamCS_wf laFrame (colFree_none _ rfl) lamLens a hR _ _ _ _ _
    (internE_lam_run _ _ a) (skLa a (decE ty) (decE body)) rfl [ty, body]
    (laskipW_eq m a ty body hty hbody (ConsR.flag hR))
    (fun h => by simp only [skLa] at h; split at h <;> simp_all [lamLens])
    ⟨rfl, laMatchOK m ty body hty hbody, laHomeOK m ty body, laNewOK m ty body hty hbody⟩ w m' hI

end intern

end L.Arena
