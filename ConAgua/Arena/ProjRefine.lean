import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.ProjStore

/-!
# The `proj` store refines the arena's `proj` tables

The record `ProjNode { n : NIdx, i : Nat, e : EIdx }` (`ConAgua/Arena/ProjStore.lean` has the L
code), `letE`'s shape at three fields, but the middle one is a plain `Nat` (as `bvar`'s field is)
and the two others are handles of *different* kinds (a name, an expression), as for `const`'s two
fields. The schema `projSch` (`PJREC`, `PJSLOT`, two words per node, counts at `CTL[32 + t]`,
tag `9`); the record relation `PJRecRel` (the first and third words are the children's handle
words, decoded at their own kinds `.name`/`.expr`; the middle word is the index, as for `bvar`);
the node hash `pjhash`; the lens `projLens`; the scratch skip (`skPj`, `pjskipW_eq`) tests only
`n` and `e` (`eViewHasScratchChild (.proj n _ e) = if n.isPersistent then !e.isPersistent else
true`), one application of `bit27_or` as `app`'s two-field skip does (the index `i` is not a
handle and is not tested). `ProjR m a` is the library's `ConsR` for the two `proj` tables.
`internProj_refines`: `intern_proj(n, u, e)` refines
`internE (.proj (decI (k := .name) n) u.toNat (decE e))` under `ProjR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `proj` cons key. -/
abbrev pjKey (n : NIdx) (i : Nat) (e : EIdx) : ProjNode := ⟨n, i, e⟩

/-- `a` with the scratch / persistent `proj` table replaced. -/
def withScrProjs (a : AState) (t : Tbl ProjNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with projs := t } } }
def withPersProjs (a : AState) (t : Tbl ProjNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with projs := t } } }

/-- The arena's two `proj` tables. -/
def projLens : Lens ProjNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.projs
  getS a := a.store.scr.projs
  setP := withPersProjs
  setS := withScrProjs
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- The arena's scratch skip at a `proj` view (`EStore.persFindMaybe`): only `n` and `e` are
tested. -/
def skPj (a : AState) (n : NIdx) (e : EIdx) : Bool :=
  if a.store.scratchOn then (if n.isPersistent then !e.isPersistent else true) else false

/-- The arena's persistent probe at a `proj` view, after the skip. -/
def pfPj (a : AState) (n : NIdx) (i : Nat) (e : EIdx) : Option EIdx :=
  if skPj a n e then none else a.store.pers.projs.cons[pjKey n i e]?

theorem persFindMaybe_proj (a : AState) (n : NIdx) (i : Nat) (e : EIdx) :
    a.store.persFindMaybe (.proj n i e) = pfPj a n i e := by
  simp [EStore.persFindMaybe, pfPj, skPj, EStore.eViewHasScratchChild, ETables.find?, Tbl.find?]

/-- `internE` at a `proj` node is the library's protocol, the persistent probe after the skip. -/
theorem internE_proj_run (n : NIdx) (i : Nat) (e : EIdx) (a : AState) :
    (internE (.proj n i e)).run a =
      protoRun projLens (pjKey n i e) ETag.proj (pfPj a n i e) (a.store.derOfView (.proj n i e))
        (.native "arena: expression constructor array full") a := by
  simp only [internE, internNodeE, EStore.find?, EStore.intern, ETables.find?, Tbl.find?,
    ETables.sizeOf, ETables.push, StateT.run_bind, StateT.run_get, pure_bind, persFindMaybe_proj]
  cases hp : pfPj a n i e <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.projs.cons[pjKey n i e]? <;>
    simp only [hs, hc, Bool.false_eq_true, ↓reduceIte, pjKey, protoRun, projLens] <;>
    (try split) <;> simp_all [withScrProjs, withPersProjs, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `proj` tables -/

/-- The `proj` schema: `PJREC`, `PJSLOT`, two words per node, the counts at `CTL[32 + t]`. -/
def projSch : Schema := ⟨PJREC, PJSLOT, 2, 32, ETag.proj⟩

theorem projSch_wf : projSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_pj0 (m : Mem) (t i : Word) :
    fld projSch m t i 0 = rdW (m.arr64 (tierA PJREC t)) (i * 2) := by
  simp [fld, Schema.ad, projSch]
theorem fld_pj (m : Mem) (t i f : Word) :
    fld projSch m t i f = rdW (m.arr64 (tierA PJREC t)) (i * 2 + f) := rfl

/-- Node `i` of tier `t` holds `proj k.n k.i k.e`: the two handle words and the index word. -/
def PJRecRel (m : Mem) (t i : Word) (k : ProjNode) : Prop :=
  tfld m PROJ t i 0 = k.n.word.toUInt64 ∧
  (tfld m PROJ t i 1).toNat = k.i ∧
  tfld m PROJ t i 2 = k.e.word.toUInt64

/-- `PJRecRel` in the raw words (inside the store library). -/
theorem PJRecRel_raw (m : Mem) (t i : Word) (k : ProjNode) :
    PJRecRel m t i k ↔
    rdW (m.arr64 (tierA PJREC t)) (i * 2) &&& 4294967295 = k.n.word.toUInt64 ∧
    (rdW (m.arr64 (tierA PJREC t)) (i * 2 + 1)).toNat = k.i ∧
    rdW (m.arr64 (tierA PJREC t)) (i * 2) >>> 32 = k.e.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `proj` store: the library's relation for the two `proj`
tables. -/
def ProjR (m : Mem) (a : AState) : Prop :=
  ConsR projCS PJRecRel m a.store.scratchOn a.store.pers.projs a.store.scr.projs

/-- A node's relation and hash depend only on its two words. -/
theorem projFrame : RFrame projSch PJRecRel pjhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_pj0, fld_pj0] at h0
  rw [fld_pj, fld_pj] at h1
  exact ⟨fun a h => by simpa only [PJRecRel_raw, h0, h1] using h,
    by simp only [pjhash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `proj_find` on node `i` of tier `t`. -/
def pjMt (m : Mem) (n u e t i : Word) : Bool := pjmatchW (m.arr64 (tierA PJREC t)) t i n u e

section query
variable (m : Mem) (n u e : Word) (hn : n.toNat < 2 ^ 32) (he : e.toNat < 2 ^ 32)

include hn he in
/-- **Matching is equality of `proj` nodes.** -/
theorem pjMatchOK :
    MatchOK PJRecRel (pjMt m n u e) m (pjKey (decI (k := .name) n) u.toNat (decE e)) := by
  intro t i k hr
  have := word_decI k.n n hn
  have := word_decI k.e e he
  obtain ⟨kn, ki, ke⟩ := k
  simp only [PJRecRel_raw] at hr
  simp only [pjMt, pjmatchW, Bool.and_eq_true, beq_iff_eq, pjKey, ProjNode.mk.injEq, decE_eq]
  grind [UInt64.toNat_inj]

theorem pjHomeOK : HomeOK pjhash (pjMt m n u e) m (projHashW n u e) := by
  intro t i hm
  simp only [pjMt, pjmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [pjhash, hm.1.1, hm.1.2, hm.2]

include hn he in
/-- The record `proj_push` writes holds the node. -/
theorem pjNewOK :
    NewOKR projSch PJRecRel pjhash m [n ||| e <<< 32, u]
      (pjKey (decI (k := .name) n) u.toNat (decE e)) (projHashW n u e) := by
  intro t ht hroom _
  have e3 : ∀ g, g < 2 → fld projSch (newRecM projSch m t [n ||| e <<< 32, u]) t
      (cntW projSch m t) g = [n ||| e <<< 32, u].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM projSch projSch_wf] <;> simp only [projSch, Schema.ad] at * <;> grind
  have e0 := e3 0 (by decide)
  have e1 := e3 1 (by decide)
  rw [fld_pj0] at e0
  rw [fld_pj] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decI (k := .name) n) n hn
  have := word_decI (decE e) e he
  simp only [PJRecRel_raw, pjhash, pjKey, e0, e1, pack_lo n e hn he, pack_hi n e hn he]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem pjpushOK_room (m : Mem) (t : Word) (h : pjpushOK m t = true) : PushRoom projSch m t := by
  simp only [pjpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, pjcnt, projSch, len64_eq] at *
  grind

/-- **The `proj` table's shape.** -/
theorem projCS_wf : projCS.WF where
  sch := projSch_wf
  P := by decide
  S := by decide
  col A h := by simp [projCS] at h
  colRoom A h := by simp [projCS] at h
  colLt A h := by
    simp only [projCS, reduceCtorEq] at h; (try subst h); (try decide)
  room m t h := (pjpushOK_room m t ((pjpushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, projCS, hk]
  ex h := by simp [projCS] at h

/-- The L skip test is the arena's (one application of `bit27_or`, the index `i` not tested). -/
theorem pjskipW_eq (m : Mem) (a : AState) (n e : Word) (hn : n.toNat < 2 ^ 32)
    (he : e.toNat < 2 ^ 32) (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (pjskipW m n e = 0) = (skPj a (decI (k := .name) n) (decE e) = false) := by
  have := bit27_or n e
  simp only [pjskipW, skPj, isPersistent_decI (k := .name) n hn, isPersistent_decE e he, ← hfl]
  grind

/-! ## `intern_proj` refines `internE (.proj _ _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : ProjR m a) (n u e : Word) (hn : n.toNat < 2 ^ 32)
  (he : e.toNat < 2 ^ 32)

include hR hn he in
/-- **`intern_proj`'s model refines the arena's `internE` at a `proj` node.** -/
theorem pjintern_correct (w : Word) (m' : Mem) (hI : pjinternW m n u e = some (w, m')) :
    AM.ok (internE (.proj (decI (k := .name) n) u.toNat (decE e))) a ∧
    ProjR m' (AM.st (internE (.proj (decI (k := .name) n) u.toNat (decE e))) a) ∧
    AM.res (internE (.proj (decI (k := .name) n) u.toNat (decE e))) a = decE w :=
  consIntern_correct projCS_wf projFrame (colFree_none _ rfl) projLens a hR _ _ _ _ _
    (internE_proj_run _ _ _ a) (skPj a (decI (k := .name) n) (decE e)) rfl [n, u, e]
    (pjskipW_eq m a n e hn he (ConsR.flag hR))
    (fun h => by simp only [skPj] at h; split at h <;> simp_all [projLens])
    ⟨rfl, pjMatchOK m n u e hn he, pjHomeOK m n u e, pjNewOK m n u e hn he⟩ w m' hI

end intern

end L.Arena
