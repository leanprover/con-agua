import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.LetStore
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The `letE` store refines the arena's `letE` tables

The tenth table on the store library, `app`'s shape at three fields instead of two: the record
`LetNode { ty val body : EIdx }` (`ConAgua/Arena/LetStore.lean` has the L code). The schema
`letSch` (`LEREC`, `LESLOT`, two words per node, counts at `CTL[20 + t]`, tag `7`), the record
relation `LeRecRel` (the three fields are the children's handle words), the node hash `lehash`,
the lens `letLens`; the scratch skip (`skLe`, `leskipW_eq`), `app`'s pattern at three fields
(two applications of `bit27_or`, since `|||` is left-associative: `ty ||| val ||| body` is
`(ty ||| val) ||| body`). `LetR m a` is the library's `ConsR` for the two `letE` tables.
`internLet_refines`: `intern_letE(ty, val, body)` refines
`internE (.letE (decE ty) (decE val) (decE body))` under `LetR`.

Not represented: the derived column (`derOfLetAt`, through `mixHash`) and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


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
    simp only [hs, hc, Bool.false_eq_true, ↓reduceIte, letKey, protoRun, letLens] <;>
    (try split) <;> simp_all [withScrLets, withPersLets, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `letE` tables -/

/-- The `letE` schema: `LEREC`, `LESLOT`, two words per node, the counts at `CTL[20 + t]`. -/
def letSch : Schema := ⟨LEREC, LESLOT, 2, 20, ETag.letE⟩

theorem letSch_wf : letSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_let0 (m : Mem) (t i : Word) :
    fld letSch m t i 0 = rdW (m.arr64 (tierA LEREC t)) (i * 2) := by
  simp [fld, Schema.ad, letSch]
theorem fld_let (m : Mem) (t i f : Word) :
    fld letSch m t i f = rdW (m.arr64 (tierA LEREC t)) (i * 2 + f) := rfl

/-- Node `i` of tier `t` holds `letE k.ty k.val k.body`: its three handle words. -/
def LeRecRel (m : Mem) (t i : Word) (k : LetNode) : Prop :=
  tfld m LET t i 0 = k.ty.word.toUInt64 ∧
  tfld m LET t i 1 = k.val.word.toUInt64 ∧
  tfld m LET t i 2 = k.body.word.toUInt64

/-- `LeRecRel` in the raw words (inside the store library). -/
theorem LeRecRel_raw (m : Mem) (t i : Word) (k : LetNode) :
    LeRecRel m t i k ↔
    rdW (m.arr64 (tierA LEREC t)) (i * 2) &&& 4294967295 = k.ty.word.toUInt64 ∧
    rdW (m.arr64 (tierA LEREC t)) (i * 2) >>> 32 = k.val.word.toUInt64 ∧
    rdW (m.arr64 (tierA LEREC t)) (i * 2 + 1) = k.body.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `letE` store: the library's relation for the two `letE`
tables. -/
def LetR (m : Mem) (a : AState) : Prop :=
  ConsR letCS LeRecRel m a.store.scratchOn a.store.pers.lets a.store.scr.lets

/-- A node's relation and hash depend only on its two words. -/
theorem letFrame : RFrame letSch LeRecRel lehash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_let0, fld_let0] at h0
  rw [fld_let, fld_let] at h1
  exact ⟨fun a h => by simpa only [LeRecRel_raw, h0, h1] using h,
    by simp only [lehash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `letE_find` on node `i` of tier `t`. -/
def leMt (m : Mem) (ty val body t i : Word) : Bool := lematchW (m.arr64 (tierA LEREC t)) t i ty val body

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
  grind [leMt, lematchW, LeRecRel_raw, decE_eq]

theorem letHomeOK : HomeOK lehash (leMt m ty val body) m (letHashW ty val body) := by
  intro t i hm
  simp only [leMt, lematchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [lehash, hm.1.1, hm.1.2, hm.2]

include hty hval hbody in
/-- The record `letE_push` writes holds the node. -/
theorem letNewOK :
    NewOKR letSch LeRecRel lehash m [ty ||| val <<< 32, body]
      (letKey (decE ty) (decE val) (decE body)) (letHashW ty val body) := by
  intro t ht hroom _
  have e : ∀ g, g < 2 → fld letSch (newRecM letSch m t [ty ||| val <<< 32, body]) t
      (cntW letSch m t) g = [ty ||| val <<< 32, body].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM letSch letSch_wf] <;> simp only [letSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_let0] at e0
  rw [fld_let] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decE ty) ty hty
  have := word_decI (decE val) val hval
  have := word_decI (decE body) body hbody
  simp only [LeRecRel_raw, lehash, letKey, e0, e1, pack_lo ty val hty hval, pack_hi ty val hty hval]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem lepushOK_room (m : Mem) (t : Word) (h : lepushOK m t = true) : PushRoom letSch m t := by
  simp only [lepushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, lecnt, letSch, len64_eq] at *
  grind

/-- **The `let` table's shape.** -/
theorem letCS_wf : letCS.WF where
  sch := letSch_wf
  P := by decide
  S := by decide
  col A h := by simp [letCS] at h
  colRoom A h := by simp [letCS] at h
  colLt A h := by
    simp only [letCS, reduceCtorEq] at h; (try subst h); (try decide)
  room m t h := (lepushOK_room m t ((lepushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, letCS, hk]
  ex h := by simp [letCS] at h

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
    AM.res (internE (.letE (decE ty) (decE val) (decE body))) a = decE w :=
  consIntern_correct letCS_wf letFrame (colFree_none _ rfl) letLens a hR _ _ _ _ _
    (internE_let_run _ _ _ a) (skLe a (decE ty) (decE val) (decE body)) rfl [ty, val, body]
    (leskipW_eq m a ty val body hty hval hbody (ConsR.flag hR))
    (fun h => by simp only [skLe] at h; split at h <;> simp_all [letLens])
    ⟨rfl, letMatchOK m ty val body hty hval hbody, letHomeOK m ty val body,
      letNewOK m ty val body hty hval hbody⟩ w m' hI

end intern

end L.Arena
