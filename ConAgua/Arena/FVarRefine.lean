import ConAgua.Arena.StoreLib
import ConAgua.Arena.FVarStore

/-!
# The `fvar` store refines the arena's `fvar` tables

The record `FVarNode { idx : Nat, ty : EIdx }` (`ConAgua/Arena/FVarStore.lean` has the L code),
`app`'s shape at two fields, but the first is a plain `Nat` (as `bvar`'s only field is) and only
the second is a handle. The schema `fvarSch` (`FVREC`, `FVSLOT`, two words per node, counts at
`CTL[26 + t]`, tag `1`), the record relation `FVRecRel` (the index word is `k.idx`, as for `bvar`;
the second word is `k.ty`'s handle word, as for `app`'s fields), the node hash `fvhash`, the lens
`fvarLens`; the scratch skip (`skFv`, `fvskipW_eq`) tests only the `ty` word (`eViewHasScratchChild
(.fvar _ ty) = !ty.isPersistent`, unconditional on `idx`), `sort`'s one-field skip pattern grafted
onto a two-word record. `FVarR m a` is the library's `StoreR` for the two `fvar` tables.
`internFVar_refines`: `intern_fvar(u, ty)` refines `internE (.fvar u.toNat (decE ty))` under
`FVarR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `fvar` cons key. -/
abbrev fvKey (idx : Nat) (ty : EIdx) : FVarNode := ⟨idx, ty⟩

/-- `a` with the scratch / persistent `fvar` table replaced. -/
def withScrFVars (a : AState) (t : Tbl FVarNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with fvars := t } } }
def withPersFVars (a : AState) (t : Tbl FVarNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with fvars := t } } }

/-- The arena's two `fvar` tables. -/
def fvarLens : Lens FVarNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.fvars
  getS a := a.store.scr.fvars
  setP := withPersFVars
  setS := withScrFVars
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- The arena's scratch skip at an `fvar` view (`EStore.persFindMaybe`): only `ty` is tested. -/
def skFv (a : AState) (ty : EIdx) : Bool :=
  if a.store.scratchOn then !ty.isPersistent else false

/-- The arena's persistent probe at an `fvar` view, after the skip. -/
def pfFv (a : AState) (idx : Nat) (ty : EIdx) : Option EIdx :=
  if skFv a ty then none else a.store.pers.fvars.cons[fvKey idx ty]?

theorem persFindMaybe_fvar (a : AState) (idx : Nat) (ty : EIdx) :
    a.store.persFindMaybe (.fvar idx ty) = pfFv a idx ty := by
  simp [EStore.persFindMaybe, pfFv, skFv, EStore.eViewHasScratchChild, ETables.find?, Tbl.find?]

/-- `internE` at an `fvar` node is the library's protocol, the persistent probe after the skip. -/
theorem internE_fvar_run (idx : Nat) (ty : EIdx) (a : AState) :
    (internE (.fvar idx ty)).run a =
      protoRun fvarLens (fvKey idx ty) ETag.fvar (pfFv a idx ty) (a.store.derOfView (.fvar idx ty))
        (.native "arena: expression constructor array full") a := by
  simp only [internE, internNodeE, EStore.find?, EStore.intern, ETables.find?, Tbl.find?,
    ETables.sizeOf, ETables.push, StateT.run_bind, StateT.run_get, pure_bind, persFindMaybe_fvar]
  cases hp : pfFv a idx ty <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.fvars.cons[fvKey idx ty]? <;>
    simp only [hp, hs, hc, Bool.false_eq_true, ↓reduceIte, fvKey, ite_self, protoRun, fvarLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrFVars, withPersFVars, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `fvar` tables -/

/-- The `fvar` schema: `FVREC`, `FVSLOT`, two words per node, the counts at `CTL[26 + t]`. -/
def fvarSch : Schema := ⟨FVREC, FVSLOT, 2, 4, 26, ETag.fvar⟩

theorem fvarSch_wf : fvarSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_fvar0 (m : Mem) (t i : Word) :
    fld fvarSch m t i 0 = rdW (m.arr64 FVREC) (i * 4 + t * 2) := by
  simp [fld, Schema.ad, fvarSch]
theorem fld_fvar (m : Mem) (t i f : Word) :
    fld fvarSch m t i f = rdW (m.arr64 FVREC) (i * 4 + t * 2 + f) := rfl

/-- Node `i` of tier `t` holds `fvar k.idx k.ty`: its first word is the index, its second the
child's handle word. -/
def FVRecRel (m : Mem) (t i : Word) (k : FVarNode) : Prop :=
  (rdW (m.arr64 FVREC) (i * 4 + t * 2)).toNat = k.idx ∧
  rdW (m.arr64 FVREC) (i * 4 + t * 2 + 1) = k.ty.word.toUInt64

/-- The hash of node `i` of tier `t`. -/
def fvhash (m : Mem) (t i : Word) : Word :=
  fvarHashW (rdW (m.arr64 FVREC) (i * 4 + t * 2)) (rdW (m.arr64 FVREC) (i * 4 + t * 2 + 1))

/-- **The state relation** of the `fvar` store: the library's relation for the two `fvar`
tables. -/
def FVarR (m : Mem) (a : AState) : Prop :=
  StoreR fvarSch FVRecRel fvhash m a.store.scratchOn a.store.pers.fvars a.store.scr.fvars

/-- A node's relation and hash depend only on its two words. -/
theorem fvarFrame : RFrame fvarSch FVRecRel fvhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_fvar0, fld_fvar0] at h0
  rw [fld_fvar, fld_fvar] at h1
  exact ⟨fun a h => by simpa only [FVRecRel, h0, h1] using h, by simp only [fvhash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `fvar_find` on node `i` of tier `t`. -/
def fvMt (m : Mem) (u ty t i : Word) : Bool := fvmatchW (m.arr64 FVREC) t i u ty

section query
variable (m : Mem) (u ty : Word) (hty : ty.toNat < 2 ^ 32)

include hty in
/-- **Matching is equality of `fvar` nodes**: the index word and the child's handle word. -/
theorem fvMatchOK : MatchOK FVRecRel (fvMt m u ty) m (fvKey u.toNat (decE ty)) := by
  intro t i k hr
  have := word_decI k.ty ty hty
  obtain ⟨kidx, kty⟩ := k
  simp only [FVRecRel] at hr
  simp only [fvMt, fvmatchW, Bool.and_eq_true, beq_iff_eq, fvKey, FVarNode.mk.injEq, decE_eq]
  grind [UInt64.toNat_inj]

theorem fvHomeOK : HomeOK fvhash (fvMt m u ty) m (fvarHashW u ty) := by
  intro t i hm
  simp only [fvMt, fvmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [fvhash, hm.1, hm.2]

include hty in
/-- The record `fvar_push` writes holds the node. -/
theorem fvNewOK : NewOK fvarSch FVRecRel fvhash m [u, ty] (fvKey u.toNat (decE ty))
    (fvarHashW u ty) := by
  intro t j ht hroom
  have e : ∀ g, g < 2 → fld fvarSch (pushG fvarSch m t [u, ty] j (cntW fvarSch m t)) t
      (cntW fvarSch m t) g = [u, ty].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_pushG fvarSch fvarSch_wf] <;> simp only [fvarSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_fvar0] at e0
  rw [fld_fvar] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decE ty) ty hty
  simp only [FVRecRel, fvhash, fvKey, e0, e1]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem fvprobeW_arm (m : Mem) (u ty t : Word) :
    ∀ j d, fvprobeW (m.arr64 FVSLOT) (m.arr64 FVREC) t u ty (nSlotsFv m) j d =
      probeArm fvarSch m t (fvMt m u ty t)
        (fvprobeW (m.arr64 FVSLOT) (m.arr64 FVREC) t u ty (nSlotsFv m)) j d := by
  intro j d; rw [fvprobeW]; rfl

theorem fvpushOK_room (m : Mem) (t : Word) (h : fvpushOK m t = true) : PushRoom fvarSch m t := by
  simp only [fvpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 FVREC) 2
  simp only [PushRoom, cntW, fvcnt, fvarSch, len64_eq] at *
  grind

theorem fvpushMem_eq (m : Mem) (t u ty j c : Word) :
    fvpushMem m t u ty j c = pushG fvarSch m t [u, ty] j c := by
  simp [fvpushMem, pushG, wrRec, Schema.ad, fvarSch]

theorem fvinternW_eq (m : Mem) (u ty : Word) :
    fvinternW m u ty = internM fvarSch m (fvskipW m ty) (fvpushOK m) [u, ty]
      (fvprobeW (m.arr64 FVSLOT) (m.arr64 FVREC) 0 u ty (nSlotsFv m)
        (homeW (fvarHashW u ty) (nSlotsFv m)) 0)
      (fvprobeW (m.arr64 FVSLOT) (m.arr64 FVREC) 1 u ty (nSlotsFv m)
        (homeW (fvarHashW u ty) (nSlotsFv m)) 0) := by
  have e0 : ∀ x, hdW fvarSch.tag.toUInt64 0 x = fvarP + x := fun x => by
    simp [hdW, fvarSch, fvarP, ETag.fvar]
  have e1 : ∀ x, hdW fvarSch.tag.toUInt64 1 x = fvarS + x := fun x => by
    simp [hdW, fvarSch, fvarS, ETag.fvar]
  simp only [fvinternW, internM, fvpushMem_eq, e0, e1]
  rfl

/-- The L skip test is the arena's. -/
theorem fvskipW_eq (m : Mem) (a : AState) (ty : Word) (hty : ty.toNat < 2 ^ 32)
    (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (fvskipW m ty = 0) = (skFv a (decE ty) = false) := by
  simp only [fvskipW, skFv, isPersistent_decE ty hty, ← hfl]
  grind

/-! ## `intern_fvar` refines `internE (.fvar _ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : FVarR m a) (u ty : Word) (hty : ty.toNat < 2 ^ 32)

include hR hty in
/-- **`intern_fvar`'s model refines the arena's `internE` at an `fvar` node.** -/
theorem fvintern_correct (w : Word) (m' : Mem) (hI : fvinternW m u ty = some (w, m')) :
    AM.ok (internE (.fvar u.toNat (decE ty))) a ∧
    FVarR m' (AM.st (internE (.fvar u.toNat (decE ty))) a) ∧
    AM.res (internE (.fvar u.toNat (decE ty))) a = decE w := by
  rw [fvinternW_eq] at hI
  exact intern_correctG fvarSch FVRecRel fvhash fvarSch_wf fvarFrame fvarLens a m hR _ _ _ _ _
    (internE_fvar_run _ _ a) (skFv a (decE ty)) rfl _ (fvskipW_eq m a ty hty hR.2.1)
    (fun h => by simp only [skFv] at h; split at h <;> simp_all [fvarLens]) _ _
    (fvMatchOK m u ty hty) (fvHomeOK m u ty) _ _
    (probe_homeG fvarSch m 0 _ _ (fvprobeW_arm m u ty 0) _)
    (probe_homeG fvarSch m 1 _ _ (fvprobeW_arm m u ty 1) _) _ (fvpushOK_room m) _ rfl
    (fvNewOK m u ty hty) w m' hI

end intern

/-- `intern_fvar` refines `internE (.fvar _ _)` under `FVarR`. -/
theorem internFVar_refines (p : Prog) (hpf : p.lookup "fvar_find" = some fvarFind)
    (hpp : p.lookup "fvar_push" = some fvarPush) (hp : p.lookup "intern_fvar" = some internFVar)
    (a₀ : AState) (n : Nat) (s₀ : St) (u ty : Word) (hR : FVarR s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_fvar" [u, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.fvar u.toNat (decE ty))) a₀ ∧
      FVarR s'.mem (AM.st (internE (.fvar u.toNat (decE ty))) a₀) ∧
      AM.res (internE (.fvar u.toNat (decE ty))) a₀ = decE (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internFVar_spec p hpf hpp hp n s₀ u ty)
  subst hs
  exact ⟨hloc, fvintern_correct s.mem a₀ hR u ty hty _ _ hI⟩

end L.Arena
