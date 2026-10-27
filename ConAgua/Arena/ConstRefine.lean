import ConAgua.Arena.ConstStore
import ConAgua.Arena.LpColRel
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The `const` store refines the arena's `const` tables

The ninth table on the store library, the `app` shape with a mixed-kind key: the record
`ConstNode { n : NIdx, us : LsIdx }` (`ConAgua/Arena/ConstStore.lean` has the L code; its
variable names `f`/`a` stand for `n`/`us`). The schema `constSch` (`CREC`, `CSLOT`, two words per
node, counts at `CTL[18 + t]`, tag `3`); the record relation `CeRecRel` (the two halves of the word are the
children's handle words); the node hash `cehash` (`constHashW` of the two halves); the lens
`constLens`; the scratch skip (`skCe`, `ceskipW_eq`), `app`'s pattern with the two fields decoded
at their own kinds (`.name`, `.levels`) instead of both at `.expr` —
`isPersistent_decI`/`word_decI`/`decI` (`StoreRel.lean`) are already `IdxKind`-generic, so this
needed no library change beyond the `isPersistent_decI` generalisation `sort` already used.
`ConstR m a` is the library's `ConsR` for the two `const` tables. `internConst_refines`:
`intern_const(n, us)` refines `internE (.const (decI n) (decI us))` under `ConstR`.

Not represented: the derived column (`derOfConst`, through `mixHash`) and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `const` cons key. -/
abbrev constKey (f : NIdx) (a : LsIdx) : ConstNode := ⟨f, a⟩

/-- `a` with the scratch / persistent `const` table replaced. -/
def withScrConsts (a : AState) (t : Tbl ConstNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with consts := t } } }
def withPersConsts (a : AState) (t : Tbl ConstNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with consts := t } } }

/-- The arena's two `const` tables. -/
def constLens : Lens ConstNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.consts
  getS a := a.store.scr.consts
  setP := withPersConsts
  setS := withScrConsts
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- The arena's scratch skip at a `const` view (`EStore.persFindMaybe`). -/
def skCe (a : AState) (f : NIdx) (x : LsIdx) : Bool :=
  if a.store.scratchOn then (if f.isPersistent then !x.isPersistent else true) else false

/-- The arena's persistent probe at a `const` view, after the skip. -/
def pfCe (a : AState) (f : NIdx) (x : LsIdx) : Option EIdx :=
  if skCe a f x then none else a.store.pers.consts.cons[constKey f x]?

theorem persFindMaybe_const (a : AState) (f : NIdx) (x : LsIdx) :
    a.store.persFindMaybe (.const f x) = pfCe a f x := by
  simp [EStore.persFindMaybe, pfCe, skCe, EStore.eViewHasScratchChild, ETables.find?, Tbl.find?]

/-- `internE` at a `const` node is the library's protocol, the persistent probe after the skip. -/
theorem internE_const_run (f : NIdx) (x : LsIdx) (a : AState) :
    (internE (.const f x)).run a =
      protoRun constLens (constKey f x) ETag.const (pfCe a f x) (a.store.derOfView (.const f x))
        (.native "arena: expression constructor array full") a := by
  simp only [internE, internNodeE, EStore.find?, EStore.intern, ETables.find?, Tbl.find?,
    ETables.sizeOf, ETables.push, StateT.run_bind, StateT.run_get, pure_bind, persFindMaybe_const]
  cases hp : pfCe a f x <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.consts.cons[constKey f x]? <;>
    simp only [hs, hc, Bool.false_eq_true, ↓reduceIte, constKey, protoRun, constLens] <;>
    (try split) <;> simp_all [withScrConsts, withPersConsts, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `const` tables -/

/-- The `const` schema: `CREC`, `CSLOT`, one packed word per node, the counts at `CTL[18 + t]`. -/
def constSch : Schema := ⟨CREC, CSLOT, 1, 18, ETag.const⟩

theorem constSch_wf : constSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_const0 (m : Mem) (t i : Word) : fld constSch m t i 0 = rdW (m.arr64 (tierA CREC t)) i := by
  simp [fld, Schema.ad, constSch]

/-- Node `i` of tier `t` holds the `const` node `k`: its two handle words. -/
def CeRecRel (m : Mem) (t i : Word) (k : ConstNode) : Prop :=
  tfld m CONST t i 0 = k.n.word.toUInt64 ∧
  tfld m CONST t i 1 = k.us.word.toUInt64

/-- `CeRecRel` in the raw words (inside the store library). -/
theorem CeRecRel_raw (m : Mem) (t i : Word) (k : ConstNode) :
    CeRecRel m t i k ↔
    rdW (m.arr64 (tierA CREC t)) i &&& 4294967295 = k.n.word.toUInt64 ∧
    rdW (m.arr64 (tierA CREC t)) i >>> 32 = k.us.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `const` store: the library's relation for the two `const` tables. -/
def ConstR (m : Mem) (a : AState) : Prop :=
  ConsR constCS CeRecRel m a.store.scratchOn a.store.pers.consts a.store.scr.consts

/-- A node's relation and hash depend only on its record word. -/
theorem constFrame : RFrame constSch CeRecRel cehash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_const0, fld_const0] at h0
  exact ⟨fun a h => by simpa only [CeRecRel_raw, h0] using h, by simp only [cehash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `const_find` on node `i` of tier `t`. -/
def ceMt (m : Mem) (f a t i : Word) : Bool := cematchW (m.arr64 (tierA CREC t)) t i f a

section query
variable (m : Mem) (f a : Word) (hf : f.toNat < 2 ^ 32) (ha : a.toNat < 2 ^ 32)

include hf ha in
/-- **Matching is equality of `const` nodes.** -/
theorem constMatchOK : MatchOK CeRecRel (ceMt m f a) m (constKey ((decI (k := .name) f)) ((decI (k := .levels) a))) := by
  intro t i k hr
  have := word_decI k.n f hf
  have := word_decI k.us a ha
  obtain ⟨kn, kus⟩ := k
  grind [ceMt, cematchW, CeRecRel_raw]

theorem constHomeOK : HomeOK cehash (ceMt m f a) m (constHashW f a) := by
  intro t i hm
  simp only [ceMt, cematchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [cehash, hm.1, hm.2]

include hf ha in
/-- The record `const_push` writes holds the node. -/
theorem constNewOK : NewOKR constSch CeRecRel cehash m [f ||| a <<< 32] (constKey ((decI (k := .name) f)) ((decI (k := .levels) a))) (constHashW f a) := by
  intro t ht hroom _
  have e0 : fld constSch (newRecM constSch m t [f ||| a <<< 32]) t (cntW constSch m t) 0 =
      f ||| a <<< 32 := by
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM constSch constSch_wf] <;> simp only [constSch, Schema.ad] at * <;> grind
  rw [fld_const0] at e0
  have := word_decI ((decI (k := .name) f)) f hf
  have := word_decI ((decI (k := .levels) a)) a ha
  simp only [CeRecRel_raw, cehash, constKey, e0, pack_lo f a hf ha, pack_hi f a hf ha]
  grind

end query

/-! ## The bridges from the L models -/

theorem cepushOK_room (m : Mem) (t : Word) (h : cepushOK m t = true) : PushRoom constSch m t := by
  simp only [cepushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [PushRoom, cntW, cecnt, constSch, len64_eq] at *
  grind

/-- **The `const` table's shape.** -/
theorem constCS_wf : constCS.WF where
  sch := constSch_wf
  P := by decide
  S := by decide
  col A h := by
    simp only [constCS, Option.some.injEq] at h; subst h
    exact ⟨by decide, by decide, by decide, fun m u k x t i => by
      simp only [constCS, cehash, Mem.arr64_set64_ne _ _ _ _ _
        (tierA_ne (by decide) (by decide) (show CREC ≠ CLP by decide) t u)]⟩
  room m t h := (cepushOK_room m t ((cepushOK_eqC m t).trans h)).2
  colRoom A h m t ht hp := by
    simp only [constCS, Option.some.injEq] at h; subst h
    rw [← cepushOK_eqC] at hp
    simp only [cepushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact colRoom_of m CLP _ t hp.2
  colLt A h := by
    simp only [constCS, Option.some.injEq] at h; subst h; decide
  vs ks h hk := by simp [pushArgs, constCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun _ => rfl
    mt := by
      intro m ks h t i hl
      obtain ⟨a, b, rfl⟩ := list_two ks (by simpa [constCS] using hl)
      simp [constCS, cematchW, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ]
    hs := by intro m t i; simp [constCS, cematchW, cehash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ]
    qh := fun _ _ _ => rfl
    vs := by
      intro ks h hl f hf
      simp only [nkW, constCS, ↓reduceIte, Nat.lt_one_iff] at hf
      subst hf; simp [pushArgs, constCS, recK, kwQ] }

/-- `CeRecRel` does not read the column. -/
theorem constColFree : ColFree constCS CeRecRel := by
  intro A h m u k x t i a hr
  simp only [constCS, Option.some.injEq] at h; subst h
  simpa only [CeRecRel_raw, Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne (by decide) (by decide) (show CREC ≠ CLP by decide) t u)] using hr

/-- **What `intern_const` changes**: the table's arrays, the column, the counts. -/
theorem ceinternW_frame (m : Mem) (f a : Word) (w : Word) (m' : Mem) (hI : ceinternW m f a = some (w, m')) :
    MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m m' :=
  consInternM_frame constCS_wf hI

theorem constLocal : RLocal constSch CeRecRel cehash [] [] := by
  intro m m' hra _ _; simp only [constSch] at hra
  exact ⟨fun t i k h => by simpa only [CeRecRel_raw, hra] using h, fun t i => by simp only [cehash, hra]⟩

/-- The L skip test is the arena's. -/
theorem ceskipW_eq (m : Mem) (a : AState) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (ceskipW m f x = 0) = (skCe a ((decI (k := .name) f)) ((decI (k := .levels) x)) = false) := by
  have := bit27_or f x
  simp only [ceskipW, skCe, isPersistent_decI (k := .name) f hf, isPersistent_decI (k := .levels) x hx, ← hfl]
  grind

/-! ## `intern_const` refines `internE (.const _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : ConstR m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
  (hx : x.toNat < 2 ^ 32)

include hR hf hx in
/-- **`intern_const`'s model refines the arena's `internE` at a `const` node.** -/
theorem ceintern_correct (w : Word) (m' : Mem) (hI : ceinternW m f x = some (w, m')) :
    AM.ok (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a ∧
    ConstR m' (AM.st (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a) ∧
    AM.res (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a = decI w :=
  consIntern_correct constCS_wf constFrame constColFree constLens a hR _ _ _ _ _
    (internE_const_run _ _ a) (skCe a ((decI (k := .name) f)) ((decI (k := .levels) x))) rfl [f, x]
    (ceskipW_eq m a f x hf hx (ConsR.flag hR))
    (fun h => by simp only [skCe] at h; split at h <;> simp_all [constLens])
    ⟨rfl, constMatchOK m f x hf hx, constHomeOK m f x, constNewOK m f x hf hx⟩ w m' hI

include hR hf hx in
/-- **The column across `intern_const`**: the new node's word is its record's bit (`hb`). -/
theorem ceintern_lp (hC : ColT2 constLens CLP lpW m a)
    (hb : lsHPW m x = b2w (a.store.lsder (decI x)).hasParam) (w : Word) (m' : Mem)
    (hI : ceinternW m f x = some (w, m')) :
    ColT2 constLens CLP lpW m' (AM.st (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a) := by
  obtain ⟨hok, hX, hres⟩ := ceintern_correct m a hR f x hf hx w m' hI
  have hcs := AM.proto_casesG constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok
  exact colMkC constCS_wf rfl constLens lpW hR hX hC hI hcs
    (by show lsHPW m x = _; rw [hb, lpW, lp_derConst])

end intern

end L.Arena
