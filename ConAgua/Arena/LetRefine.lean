import ConAgua.Arena.StoreLib
import ConAgua.Arena.SimLib
import ConAgua.Arena.LetStore

/-!
# The `letE` store refines the arena's `letE` tables

The tenth table on the store library, `app`'s shape at three fields instead of two: the record
`LetNode { ty val body : EIdx }` (`ConAgua/Arena/LetStore.lean` has the L code). The schema
`letSch` (`LEREC`, `LESLOT`, three words per node, counts at `CTL[20 + t]`, tag `7`), the record
relation `LeRecRel` (the three words are the children's handle words), the node hash `lehash`,
the lens `letLens`; the scratch skip (`skLe`, `leskipW_eq`), `app`'s pattern at three fields
(two applications of `bit27_or`, since `|||` is left-associative: `ty ||| val ||| body` is
`(ty ||| val) ||| body`). `LetR m a` is the library's `StoreR` for the two `letE` tables.
`internLet_refines`: `intern_letE(ty, val, body)` refines
`internE (.letE (decE ty) (decE val) (decE body))` under `LetR`.

Not represented: the derived column (`derOfLetAt`, through `mixHash`) and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `letE` cons key. -/
abbrev letKey (ty val body : EIdx) : LetNode := ⟨ty, val, body⟩

/-- `a` with the scratch / persistent `letE` table replaced. -/
def withScrLets (a : AState) (t : Tbl LetNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with lets := t } } }
def withPersLets (a : AState) (t : Tbl LetNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with lets := t } } }

/-- The arena's two `letE` tables. -/
def letLens : Lens LetNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.lets
  getS a := a.store.scr.lets
  setP := withPersLets
  setS := withScrLets
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- The arena's scratch skip at a `letE` view (`EStore.persFindMaybe`). -/
def skLe (a : AState) (ty val body : EIdx) : Bool :=
  if a.store.scratchOn then
    (if ty.isPersistent then (if val.isPersistent then !body.isPersistent else true) else true)
  else false

/-- The arena's persistent probe at a `letE` view, after the skip. -/
def pfLe (a : AState) (ty val body : EIdx) : Option EIdx :=
  if skLe a ty val body then none else a.store.pers.lets.cons[letKey ty val body]?

theorem persFindMaybe_let (a : AState) (ty val body : EIdx) :
    a.store.persFindMaybe (.letE ty val body) = pfLe a ty val body := by
  simp [EStore.persFindMaybe, pfLe, skLe, EStore.eViewHasScratchChild, ETables.find?, Tbl.find?]

/-- `internE` at a `letE` node is the library's protocol, the persistent probe after the skip. -/
theorem internE_let_run (ty val body : EIdx) (a : AState) :
    (internE (.letE ty val body)).run a =
      protoRun letLens (letKey ty val body) ETag.letE (pfLe a ty val body)
        (a.store.derOfView (.letE ty val body)) (.native "arena: expression constructor array full")
        a := by
  simp only [internE, internNodeE, EStore.find?, EStore.intern, ETables.find?, Tbl.find?,
    ETables.sizeOf, ETables.push, StateT.run_bind, StateT.run_get, pure_bind, persFindMaybe_let]
  cases hp : pfLe a ty val body <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.lets.cons[letKey ty val body]? <;>
    simp only [hp, hs, hc, Bool.false_eq_true, ↓reduceIte, letKey, ite_self, protoRun, letLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrLets, withPersLets, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `letE` tables -/

/-- The `letE` schema: `LEREC`, `LESLOT`, three words per node, the counts at `CTL[20 + t]`. -/
def letSch : Schema := ⟨LEREC, LESLOT, 3, 6, 20, ETag.letE⟩

theorem letSch_wf : letSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_let0 (m : Mem) (t i : Word) :
    fld letSch m t i 0 = rdW (m.arr64 LEREC) (i * 6 + t * 3) := by
  simp [fld, Schema.ad, letSch]
theorem fld_let (m : Mem) (t i f : Word) :
    fld letSch m t i f = rdW (m.arr64 LEREC) (i * 6 + t * 3 + f) := rfl

/-- Node `i` of tier `t` holds `letE k.ty k.val k.body`: its three handle words. -/
def LeRecRel (m : Mem) (t i : Word) (k : LetNode) : Prop :=
  rdW (m.arr64 LEREC) (i * 6 + t * 3) = k.ty.word.toUInt64 ∧
  rdW (m.arr64 LEREC) (i * 6 + t * 3 + 1) = k.val.word.toUInt64 ∧
  rdW (m.arr64 LEREC) (i * 6 + t * 3 + 2) = k.body.word.toUInt64

/-- The hash of node `i` of tier `t`. -/
def lehash (m : Mem) (t i : Word) : Word :=
  letHashW (rdW (m.arr64 LEREC) (i * 6 + t * 3)) (rdW (m.arr64 LEREC) (i * 6 + t * 3 + 1))
    (rdW (m.arr64 LEREC) (i * 6 + t * 3 + 2))

/-- **The state relation** of the `letE` store: the library's relation for the two `letE`
tables. -/
def LetR (m : Mem) (a : AState) : Prop :=
  StoreR letSch LeRecRel lehash m a.store.scratchOn a.store.pers.lets a.store.scr.lets

/-- A node's relation and hash depend only on its three words. -/
theorem letFrame : RFrame letSch LeRecRel lehash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  have h2 := hf 2 (by decide)
  rw [fld_let0, fld_let0] at h0
  rw [fld_let, fld_let] at h1
  rw [fld_let, fld_let] at h2
  exact ⟨fun a h => by simpa only [LeRecRel, h0, h1, h2] using h,
    by simp only [lehash, h0, h1, h2]⟩

/-! ## The query's obligations -/

/-- The match of `letE_find` on node `i` of tier `t`. -/
def leMt (m : Mem) (ty val body t i : Word) : Bool := lematchW (m.arr64 LEREC) t i ty val body

section query
variable (m : Mem) (ty val body : Word) (hty : ty.toNat < 2 ^ 32) (hval : val.toNat < 2 ^ 32)
  (hbody : body.toNat < 2 ^ 32)

include hty hval hbody in
/-- **Matching is equality of `letE` nodes.** -/
theorem letMatchOK :
    MatchOK LeRecRel (leMt m ty val body) m (letKey (decE ty) (decE val) (decE body)) := by
  intro t i k hr
  have := word_decI k.ty ty hty
  have := word_decI k.val val hval
  have := word_decI k.body body hbody
  obtain ⟨kty, kval, kbody⟩ := k
  grind [leMt, lematchW, LeRecRel, decE_eq]

theorem letHomeOK : HomeOK lehash (leMt m ty val body) m (letHashW ty val body) := by
  intro t i hm
  simp only [leMt, lematchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [lehash, hm.1.1, hm.1.2, hm.2]

include hty hval hbody in
/-- The record `letE_push` writes holds the node. -/
theorem letNewOK :
    NewOK letSch LeRecRel lehash m [ty, val, body]
      (letKey (decE ty) (decE val) (decE body)) (letHashW ty val body) := by
  intro t j ht hroom
  have e : ∀ g, g < 3 → fld letSch (pushG letSch m t [ty, val, body] j (cntW letSch m t)) t
      (cntW letSch m t) g = [ty, val, body].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_pushG letSch letSch_wf] <;> simp only [letSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  rw [fld_let0] at e0
  rw [fld_let] at e1
  rw [fld_let] at e2
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (2 : Word).toNat = 0 + 1 + 1 from rfl, show (0 : Word).toNat = 0 from rfl] at e0 e1 e2
  have := word_decI (decE ty) ty hty
  have := word_decI (decE val) val hval
  have := word_decI (decE body) body hbody
  simp only [LeRecRel, lehash, letKey, e0, e1, e2]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem leprobeW_arm (m : Mem) (ty val body t : Word) :
    ∀ j d, leprobeW (m.arr64 LESLOT) (m.arr64 LEREC) t ty val body (baseW m t) (nSlotsLe m) j d =
      probeArm letSch m t (leMt m ty val body t)
        (leprobeW (m.arr64 LESLOT) (m.arr64 LEREC) t ty val body (baseW m t) (nSlotsLe m)) j d := by
  intro j d; rw [leprobeW]; rfl

theorem lepushOK_room (m : Mem) (t : Word) (h : lepushOK m t = true) : PushRoom letSch m t := by
  simp only [lepushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, lecnt, letSch, len64_eq] at *
  grind

theorem lepushMem_eq (m : Mem) (t ty val body j c : Word) :
    lepushMem m t ty val body j c = pushG letSch m t [ty, val, body] j c := by
  simp [lepushMem, pushG, wrRec, Schema.ad, letSch]

theorem leinternW_eq (m : Mem) (ty val body : Word) :
    leinternW m ty val body = internM letSch m (leskipW m ty val body) (lepushOK m) [ty, val, body]
      (leprobeW (m.arr64 LESLOT) (m.arr64 LEREC) 0 ty val body (baseW m 0) (nSlotsLe m)
        (homeW (letHashW ty val body) (nSlotsLe m)) 0)
      (leprobeW (m.arr64 LESLOT) (m.arr64 LEREC) 1 ty val body (baseW m 1) (nSlotsLe m)
        (homeW (letHashW ty val body) (nSlotsLe m)) 0) := by
  have e0 : ∀ x, hdW letSch.tag.toUInt64 0 x = letP + x := fun x => by
    simp [hdW, letSch, letP, ETag.letE]
  have e1 : ∀ x, hdW letSch.tag.toUInt64 1 x = letS + x := fun x => by
    simp [hdW, letSch, letS, ETag.letE]
  simp only [leinternW, internM, lepushMem_eq, e0, e1]
  rfl

/-- The L skip test is the arena's (two applications of `bit27_or`, matching `|||`'s left
associativity). -/
theorem leskipW_eq (m : Mem) (a : AState) (ty val body : Word) (hty : ty.toNat < 2 ^ 32)
    (hval : val.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32)
    (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (leskipW m ty val body = 0) = (skLe a (decE ty) (decE val) (decE body) = false) := by
  have h1 := bit27_or ty val
  have h2 := bit27_or (ty ||| val) body
  simp only [leskipW, skLe, isPersistent_decE ty hty, isPersistent_decE val hval,
    isPersistent_decE body hbody, ← hfl]
  grind

/-! ## `intern_letE` refines `internE (.letE _ _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : LetR m a) (ty val body : Word) (hty : ty.toNat < 2 ^ 32)
  (hval : val.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32)

include hR hty hval hbody in
/-- **`intern_letE`'s model refines the arena's `internE` at a `letE` node.** -/
theorem leintern_correct (w : Word) (m' : Mem) (hI : leinternW m ty val body = some (w, m')) :
    AM.ok (internE (.letE (decE ty) (decE val) (decE body))) a ∧
    LetR m' (AM.st (internE (.letE (decE ty) (decE val) (decE body))) a) ∧
    AM.res (internE (.letE (decE ty) (decE val) (decE body))) a = decE w := by
  rw [leinternW_eq] at hI
  exact intern_correctG letSch LeRecRel lehash letSch_wf letFrame letLens a m hR _ _ _ _ _
    (internE_let_run _ _ _ a) (skLe a (decE ty) (decE val) (decE body)) rfl _
    (leskipW_eq m a ty val body hty hval hbody hR.2.1)
    (fun h => by simp only [skLe] at h; split at h <;> simp_all [letLens]) _ _
    (letMatchOK m ty val body hty hval hbody) (letHomeOK m ty val body) _ _
    (probe_homeG letSch m 0 _ _ (leprobeW_arm m ty val body 0) _)
    (probe_homeG letSch m 1 _ _ (leprobeW_arm m ty val body 1) _) _ (lepushOK_room m) _ rfl
    (letNewOK m ty val body hty hval hbody) w m' hI

end intern

/-- `intern_letE` refines `internE (.letE _ _ _)` under `LetR`. -/
theorem internLet_refines (p : Prog) (hpf : p.lookup "letE_find" = some letFind)
    (hpp : p.lookup "letE_push" = some letPush) (hp : p.lookup "intern_letE" = some internLet)
    (a₀ : AState) (n : Nat) (s₀ : St) (ty val body : Word) (hR : LetR s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hval : val.toNat < 2 ^ 32) (hbody : body.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_letE" [ty, val, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.letE (decE ty) (decE val) (decE body))) a₀ ∧
      LetR s'.mem (AM.st (internE (.letE (decE ty) (decE val) (decE body))) a₀) ∧
      AM.res (internE (.letE (decE ty) (decE val) (decE body))) a₀ = decE (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internLet_spec p hpf hpp hp n s₀ ty val body)
    (Sim.ofOkD (leintern_correct s₀.mem a₀ hR ty val body hty hval hbody))

end L.Arena
