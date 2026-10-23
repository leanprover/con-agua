import ConAgua.Arena.StoreLib
import ConAgua.Arena.SimLib
import ConAgua.Arena.ConstStore
import ConAgua.Arena.LpColRel

/-!
# The `const` store refines the arena's `const` tables

The ninth table on the store library, the `app` shape with a mixed-kind key: the record
`ConstNode { n : NIdx, us : LsIdx }` (`ConAgua/Arena/ConstStore.lean` has the L code; its
variable names `f`/`a` stand for `n`/`us`). The schema `constSch` (`CREC`, `CSLOT`, two words per
node, counts at `CTL[18 + t]`, tag `3`); the record relation `CeRecRel` (the two words are the
children's handle words); the node hash `cehash` (`constHashW` of the two words); the lens
`constLens`; the scratch skip (`skCe`, `ceskipW_eq`), `app`'s pattern with the two fields decoded
at their own kinds (`.name`, `.levels`) instead of both at `.expr` —
`isPersistent_decI`/`word_decI`/`decI` (`StoreRel.lean`) are already `IdxKind`-generic, so this
needed no library change beyond the `isPersistent_decI` generalisation `sort` already used.
`ConstR m a` is the library's `StoreR` for the two `const` tables. `internConst_refines`:
`intern_const(n, us)` refines `internE (.const (decI n) (decI us))` under `ConstR`.

Not represented: the derived column (`derOfConst`, through `mixHash`) and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

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
    simp only [hp, hs, hc, Bool.false_eq_true, ↓reduceIte, constKey, ite_self, protoRun, constLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrConsts, withPersConsts, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `const` tables -/

/-- The `const` schema: `CREC`, `CSLOT`, two words per node, the counts at `CTL[18 + t]`. -/
def constSch : Schema := ⟨CREC, CSLOT, 2, 4, 18, ETag.const⟩

theorem constSch_wf : constSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_const0 (m : Mem) (t i : Word) : fld constSch m t i 0 = rdW (m.arr64 CREC) (i * 4 + t * 2) := by
  simp [fld, Schema.ad, constSch]
theorem fld_const (m : Mem) (t i f : Word) :
    fld constSch m t i f = rdW (m.arr64 CREC) (i * 4 + t * 2 + f) := rfl

/-- Node `i` of tier `t` holds the `const` node `k`: its two handle words. -/
def CeRecRel (m : Mem) (t i : Word) (k : ConstNode) : Prop :=
  rdW (m.arr64 CREC) (i * 4 + t * 2) = k.n.word.toUInt64 ∧
  rdW (m.arr64 CREC) (i * 4 + t * 2 + 1) = k.us.word.toUInt64

/-- **The state relation** of the `const` store: the library's relation for the two `const` tables. -/
def ConstR (m : Mem) (a : AState) : Prop :=
  StoreR constSch CeRecRel cehash m a.store.scratchOn a.store.pers.consts a.store.scr.consts

/-- A node's relation and hash depend only on its two words. -/
theorem constFrame : RFrame constSch CeRecRel cehash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_const0, fld_const0] at h0
  rw [fld_const, fld_const] at h1
  exact ⟨fun a h => by simpa only [CeRecRel, h0, h1] using h, by simp only [cehash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `const_find` on node `i` of tier `t`. -/
def ceMt (m : Mem) (f a t i : Word) : Bool := cematchW (m.arr64 CREC) t i f a

section query
variable (m : Mem) (f a : Word) (hf : f.toNat < 2 ^ 32) (ha : a.toNat < 2 ^ 32)

include hf ha in
/-- **Matching is equality of `const` nodes.** -/
theorem constMatchOK : MatchOK CeRecRel (ceMt m f a) m (constKey ((decI (k := .name) f)) ((decI (k := .levels) a))) := by
  intro t i k hr
  have := word_decI k.n f hf
  have := word_decI k.us a ha
  obtain ⟨kn, kus⟩ := k
  grind [ceMt, cematchW, CeRecRel]

theorem constHomeOK : HomeOK cehash (ceMt m f a) m (constHashW f a) := by
  intro t i hm
  simp only [ceMt, cematchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [cehash, hm.1, hm.2]

include hf ha in
/-- The record `const_push` writes holds the node. -/
theorem constNewOK : NewOK constSch CeRecRel cehash m [f, a] (constKey ((decI (k := .name) f)) ((decI (k := .levels) a))) (constHashW f a) := by
  intro t j ht hroom
  have e : ∀ g, g < 2 → fld constSch (pushG constSch m t [f, a] j (cntW constSch m t)) t
      (cntW constSch m t) g = [f, a].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_pushG constSch constSch_wf] <;> simp only [constSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_const0] at e0
  rw [fld_const] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI ((decI (k := .name) f)) f hf
  have := word_decI ((decI (k := .levels) a)) a ha
  simp only [CeRecRel, cehash, constKey, e0, e1]
  grind

end query

/-! ## The bridges from the L models -/

theorem ceprobeW_arm (m : Mem) (f a t : Word) :
    ∀ j d, ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) t f a (baseW m t) (nSlotsCe m) j d =
      probeArm constSch m t (ceMt m f a t) (ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) t f a (baseW m t) (nSlotsCe m)) j d := by
  intro j d; rw [ceprobeW]; rfl

theorem cepushOK_room (m : Mem) (t : Word) (h : cepushOK m t = true) : PushRoom constSch m t := by
  simp only [cepushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 CREC) 2
  simp only [PushRoom, cntW, cecnt, constSch, len64_eq] at *
  grind

theorem cepushMem_eq (m : Mem) (t f a j c : Word) :
    cepushMem m t f a j c = (pushG constSch m t [f, a] j c).set64 CLP (c * 2 + t) (lsHPW m a) := by
  simp [cepushMem, pushG, wrRec, Schema.ad, constSch]

theorem ceinternW_eq (m : Mem) (f a : Word) :
    ceinternW m f a = internMD constSch CLP (lsHPW m a) m (ceskipW m f a) (cepushOK m) [f, a]
      (ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) 0 f a (baseW m 0) (nSlotsCe m) (homeW (constHashW f a) (nSlotsCe m)) 0)
      (ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) 1 f a (baseW m 1) (nSlotsCe m) (homeW (constHashW f a) (nSlotsCe m)) 0) := by
  have e0 : ∀ x, hdW constSch.tag.toUInt64 0 x = constP + x := fun x => by
    simp [hdW, constSch, constP, ETag.const]
  have e1 : ∀ x, hdW constSch.tag.toUInt64 1 x = constS + x := fun x => by
    simp [hdW, constSch, constS, ETag.const]
  simp only [ceinternW, internMD, cepushMem_eq, e0, e1]
  rfl

/-- **What `intern_const` changes**: the table's arrays, the column, the counts. -/
theorem ceinternW_frame (m : Mem) (f a : Word) (w : Word) (m' : Mem) (hI : ceinternW m f a = some (w, m')) :
    MemFrame [CREC, CSLOT, CLP] [18, 19] m m' := by
  rw [ceinternW_eq] at hI
  exact internMD_frame constSch constSch_wf CLP (by decide) _ _ _ _ _ _ _ _ _ hI

/-- `intern_const`'s model as the library's interning and the `mk_*` tail (`mkK`), given the count
words. -/
theorem ceinternW_eqK (m : Mem) (f a : Word) (hctl : constSch.ca.toNat + 2 ≤ (m.arr64 CTL).size) :
    ceinternW m f a = mkK CLP constSch.ca (cnt2 m constSch.ca) (lsHPW m a)
      (internM constSch m (ceskipW m f a) (cepushOK m) [f, a]
      (ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) 0 f a (baseW m 0) (nSlotsCe m) (homeW (constHashW f a) (nSlotsCe m)) 0)
      (ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) 1 f a (baseW m 1) (nSlotsCe m) (homeW (constHashW f a) (nSlotsCe m)) 0)) := by
  rw [ceinternW_eq]
  refine internMD_mkK constSch constSch_wf _ _ _ _ _ _ _ _ hctl (fun t ht hp => ?_)
  simp only [cepushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨h1, -⟩, h2⟩, -⟩ := hp
  exact ⟨h1, col_room _ _ _ ht h1 h2⟩

theorem constLocal : RLocal constSch CeRecRel cehash [] [] := by
  intro m m' hra _ _; simp only [constSch] at hra
  exact ⟨fun t i k h => by simpa only [CeRecRel, hra] using h, fun t i => by simp only [cehash, hra]⟩

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
/-- The library's half of `intern_const` (before the column). -/
theorem ceintern_core (w : Word) (m₁ : Mem)
    (hI : internM constSch m (ceskipW m f x) (cepushOK m) [f, x]
      (ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) 0 f x (baseW m 0) (nSlotsCe m) (homeW (constHashW f x) (nSlotsCe m)) 0)
      (ceprobeW (m.arr64 CSLOT) (m.arr64 CREC) 1 f x (baseW m 1) (nSlotsCe m) (homeW (constHashW f x) (nSlotsCe m)) 0) =
      some (w, m₁)) :
    AM.ok (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a ∧
    ConstR m₁ (AM.st (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a) ∧
    AM.res (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a = decI w :=
  intern_correctG constSch CeRecRel cehash constSch_wf constFrame constLens a m hR _ _ _ _ _
    (internE_const_run _ _ a) (skCe a ((decI (k := .name) f)) ((decI (k := .levels) x))) rfl _ (ceskipW_eq m a f x hf hx hR.2.1)
    (fun h => by simp only [skCe] at h; split at h <;> simp_all [constLens]) _ _
    (constMatchOK m f x hf hx) (constHomeOK m f x) _ _
    (probe_homeG constSch m 0 _ _ (ceprobeW_arm m f x 0) _)
    (probe_homeG constSch m 1 _ _ (ceprobeW_arm m f x 1) _) _ (cepushOK_room m) _ rfl
    (constNewOK m f x hf hx) w m₁ hI

include hR hf hx in
/-- **`intern_const`'s model refines the arena's `internE` at an `app` node.** -/
theorem ceintern_correct (w : Word) (m' : Mem) (hI : ceinternW m f x = some (w, m')) :
    AM.ok (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a ∧
    ConstR m' (AM.st (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a) ∧
    AM.res (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a = decI w := by
  rw [ceinternW_eqK m f x hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := ceintern_core m a hR f x hf hx w m₁ h₁
  exact ⟨hok, storeR_frame constSch CeRecRel cehash constSch_wf [] [] constLocal [CLP] []
    (by simp [Apart, constSch, CREC, CSLOT, CLP, SCB, POOL, CTL]) m₁ m'
    (derPutW_frame CLP (by decide) _ m₁ m' _ _ _ hput) _ _ _ hX, hres⟩

include hR hf hx in
/-- **The column across `intern_const`**: the new node's word is its record's bit (`hb`). -/
theorem ceintern_lp (hC : ColT2 constLens CLP lpW m a)
    (hb : lsHPW m x = b2w (a.store.lsder (decI x)).hasParam) (w : Word) (m' : Mem)
    (hI : ceinternW m f x = some (w, m')) :
    ColT2 constLens CLP lpW m' (AM.st (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a) := by
  rw [ceinternW_eqK m f x hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := ceintern_core m a hR f x hf hx w m₁ h₁
  have hcs := AM.proto_casesG constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok
  have hfr : m₁.arr64 CLP = m.arr64 CLP :=
    (internM_frame _ constSch_wf _ _ _ _ _ _ _ _ h₁).1 CLP (by simp [constSch, CREC, CSLOT, CLP])
      (by decide)
  exact colMk constSch constSch_wf CeRecRel cehash constLens CLP lpW m m₁ m' a _ _ _ _ _ _ hR hX hC hfr
    hcs hres.symm (by rw [hb]; rw [lpW, lp_derConst]) hput

end intern

/-- `intern_const` refines `internE (.const _ _)` under `ConstR`. -/
theorem internConst_refines (p : Prog) (hpf : p.lookup "const_find" = some constFind)
    (hpp : p.lookup "const_push" = some constPush) (hp : p.lookup "intern_const" = some internConst)
    (a₀ : AState) (n : Nat) (s₀ : St) (f x : Word) (hR : ConstR s₀.mem a₀) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_const" [f, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a₀ ∧
      ConstR s'.mem (AM.st (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a₀) ∧
      AM.res (internE (.const ((decI (k := .name) f)) ((decI (k := .levels) x)))) a₀ = decI (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internConst_spec p hpf hpp hp n s₀ f x)
    (Sim.ofOkD (ceintern_correct s₀.mem a₀ hR f x hf hx))

end L.Arena
