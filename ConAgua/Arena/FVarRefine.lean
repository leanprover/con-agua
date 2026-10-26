import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.SimLib
import ConAgua.Arena.FVarStore
import ConAgua.Arena.LpColRel

/-!
# The `fvar` store refines the arena's `fvar` tables

The record `FVarNode { idx : Nat, ty : EIdx }` (`ConAgua/Arena/FVarStore.lean` has the L code),
`app`'s shape at two fields, but the first is a plain `Nat` (as `bvar`'s only field is) and only
the second is a handle. The schema `fvarSch` (`FVREC`, `FVSLOT`, two words per node, counts at
`CTL[26 + t]`, tag `1`), the record relation `FVRecRel` (the index word is `k.idx`, as for `bvar`;
the second word is `k.ty`'s handle word, as for `app`'s fields), the node hash `fvhash`, the lens
`fvarLens`; the scratch skip (`skFv`, `fvskipW_eq`) tests only the `ty` word (`eViewHasScratchChild
(.fvar _ ty) = !ty.isPersistent`, unconditional on `idx`), `sort`'s one-field skip pattern grafted
onto a two-word record. `FVarR m a` is the library's `ConsR` for the two `fvar` tables.
`internFVar_refines`: `intern_fvar(u, ty)` refines `internE (.fvar u.toNat (decE ty))` under
`FVarR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


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
    simp only [hs, hc, Bool.false_eq_true, ↓reduceIte, fvKey, protoRun, fvarLens] <;>
    (try split) <;> simp_all [withScrFVars, withPersFVars, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `fvar` tables -/

/-- The `fvar` schema: `FVREC`, `FVSLOT`, two words per node, the counts at `CTL[26 + t]`. -/
def fvarSch : Schema := ⟨FVREC, FVSLOT, 2, 26, ETag.fvar⟩

theorem fvarSch_wf : fvarSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_fvar0 (m : Mem) (t i : Word) :
    fld fvarSch m t i 0 = rdW (m.arr64 (tierA FVREC t)) (i * 2) := by
  simp [fld, Schema.ad, fvarSch]
theorem fld_fvar (m : Mem) (t i f : Word) :
    fld fvarSch m t i f = rdW (m.arr64 (tierA FVREC t)) (i * 2 + f) := rfl

/-- Node `i` of tier `t` holds `fvar k.idx k.ty`: its first word is the index, its second the
child's handle word. -/
def FVRecRel (m : Mem) (t i : Word) (k : FVarNode) : Prop :=
  (tfld m FVAR t i 0).toNat = k.idx ∧
  tfld m FVAR t i 1 = k.ty.word.toUInt64

/-- `FVRecRel` in the raw words (inside the store library). -/
theorem FVRecRel_raw (m : Mem) (t i : Word) (k : FVarNode) :
    FVRecRel m t i k ↔
    (rdW (m.arr64 (tierA FVREC t)) (i * 2)).toNat = k.idx ∧
    rdW (m.arr64 (tierA FVREC t)) (i * 2 + 1) = k.ty.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `fvar` store: the library's relation for the two `fvar`
tables. -/
def FVarR (m : Mem) (a : AState) : Prop :=
  ConsR fvarCS FVRecRel m a.store.scratchOn a.store.pers.fvars a.store.scr.fvars

/-- A node's relation and hash depend only on its two words. -/
theorem fvarFrame : RFrame fvarSch FVRecRel fvhash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  rw [fld_fvar0, fld_fvar0] at h0
  rw [fld_fvar, fld_fvar] at h1
  exact ⟨fun a h => by simpa only [FVRecRel_raw, h0, h1] using h, by simp only [fvhash, h0, h1]⟩

/-! ## The query's obligations -/

/-- The match of `fvar_find` on node `i` of tier `t`. -/
def fvMt (m : Mem) (u ty t i : Word) : Bool := fvmatchW (m.arr64 (tierA FVREC t)) t i u ty

section query
variable (m : Mem) (u ty : Word) (hty : ty.toNat < 2 ^ 32)

include hty in
/-- **Matching is equality of `fvar` nodes**: the index word and the child's handle word. -/
theorem fvMatchOK : MatchOK FVRecRel (fvMt m u ty) m (fvKey u.toNat (decE ty)) := by
  intro t i k hr
  have := word_decI k.ty ty hty
  obtain ⟨kidx, kty⟩ := k
  simp only [FVRecRel_raw] at hr
  simp only [fvMt, fvmatchW, Bool.and_eq_true, beq_iff_eq, fvKey, FVarNode.mk.injEq, decE_eq]
  grind [UInt64.toNat_inj]

theorem fvHomeOK : HomeOK fvhash (fvMt m u ty) m (fvarHashW u ty) := by
  intro t i hm
  simp only [fvMt, fvmatchW, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [fvhash, hm.1, hm.2]

include hty in
/-- The record `fvar_push` writes holds the node. -/
theorem fvNewOK : NewOKR fvarSch FVRecRel fvhash m [u, ty] (fvKey u.toNat (decE ty))
    (fvarHashW u ty) := by
  intro t ht hroom _
  have e : ∀ g, g < 2 → fld fvarSch (newRecM fvarSch m t [u, ty]) t
      (cntW fvarSch m t) g = [u, ty].getD g.toNat 0 := by
    intro g hg
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM fvarSch fvarSch_wf] <;> simp only [fvarSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  rw [fld_fvar0] at e0
  rw [fld_fvar] at e1
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl] at e0 e1
  have := word_decI (decE ty) ty hty
  simp only [FVRecRel_raw, fvhash, fvKey, e0, e1]
  grind [decE_eq]

end query

/-! ## The bridges from the L models -/

theorem fvpushOK_room (m : Mem) (t : Word) (h : fvpushOK m t = true) : PushRoom fvarSch m t := by
  simp only [fvpushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA FVREC t)) 1
  simp only [PushRoom, cntW, fvcnt, fvarSch, len64_eq] at *
  grind

/-- **The `fvar` table's shape.** -/
theorem fvarCS_wf : fvarCS.WF where
  sch := fvarSch_wf
  P := by decide
  S := by decide
  col A h := by
    simp only [fvarCS, Option.some.injEq] at h; subst h
    exact ⟨by decide, by decide, by decide, fun m u k x t i => by
      simp only [fvarCS, fvhash, Mem.arr64_set64_ne _ _ _ _ _
        (tierA_ne (by decide) (by decide) (show FVREC ≠ FVLP by decide) t u)]⟩
  room m t h := (fvpushOK_room m t ((fvpushOK_eqC m t).trans h)).2
  colRoom A h m t ht hp := by
    simp only [fvarCS, Option.some.injEq] at h; subst h
    rw [← fvpushOK_eqC] at hp
    simp only [fvpushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact colRoom_of m FVLP _ t hp.2
  colLt A h := by
    simp only [fvarCS, Option.some.injEq] at h; subst h; decide
  vs ks h hk := by simp [pushArgs, fvarCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun h => absurd h (by decide)
    mt := by
      intro m ks h t i hl
      obtain ⟨a, b, rfl⟩ := list_two ks (by simpa [fvarCS] using hl)
      simp [fvarCS, fvmatchW, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    hs := by intro m t i; simp [fvarCS, fvmatchW, fvhash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl, show UInt64.ofNat 1 = 1 from rfl]
    qh := fun _ _ _ => rfl
    vs := by intro ks h hl f hf; simp [pushArgs, fvarCS, nkW, recK] at hf ⊢ <;> omega }

/-- `FVRecRel` does not read the column. -/
theorem fvarColFree : ColFree fvarCS FVRecRel := by
  intro A h m u k x t i a hr
  simp only [fvarCS, Option.some.injEq] at h; subst h
  simpa only [FVRecRel_raw, Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne (by decide) (by decide) (show FVREC ≠ FVLP by decide) t u)] using hr

/-- **What `intern_fvar` changes**: the table's arrays, the column, the counts. -/
theorem fvinternW_frame (m : Mem) (u ty : Word) (w : Word) (m' : Mem) (hI : fvinternW m u ty = some (w, m')) :
    MemFrame [FVREC, FVREC + 256, FVSLOT, FVSLOT + 256, FVLP, FVLP + 256] [26, 27] m m' :=
  consInternM_frame fvarCS_wf hI

theorem fvarLocal : RLocal fvarSch FVRecRel fvhash [] [] := by
  intro m m' hra _ _; simp only [fvarSch] at hra
  exact ⟨fun t i k h => by simpa only [FVRecRel_raw, hra] using h, fun t i => by simp only [fvhash, hra]⟩

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
    AM.res (internE (.fvar u.toNat (decE ty))) a = decE w :=
  consIntern_correct fvarCS_wf fvarFrame fvarColFree fvarLens a hR _ _ _ _ _
    (internE_fvar_run _ _ a) (skFv a (decE ty)) rfl [u, ty]
    (fvskipW_eq m a ty hty (ConsR.flag hR))
    (fun h => by simp only [skFv] at h; split at h <;> simp_all [fvarLens])
    ⟨rfl, fvMatchOK m u ty hty, fvHomeOK m u ty, fvNewOK m u ty hty⟩ w m' hI

include hR hty in
/-- **The column across `intern_fvar`**: the new node's word is its record's bit (`hb`). -/
theorem fvintern_lp (hC : ColT2 fvarLens FVLP lpW m a)
    (hb : exprLPW m ty = b2w (ConLeche.lpOfData (a.store.derived (decE ty)))) (w : Word) (m' : Mem)
    (hI : fvinternW m u ty = some (w, m')) :
    ColT2 fvarLens FVLP lpW m' (AM.st (internE (.fvar u.toNat (decE ty))) a) := by
  obtain ⟨hok, hX, hres⟩ := fvintern_correct m a hR u ty hty w m' hI
  have hcs := AM.proto_casesG fvarLens _ _ _ _ _ _ a (internE_fvar_run _ _ a) hok
  exact colMkC fvarCS_wf rfl fvarLens lpW hR hX hC hI hcs
    (by show exprLPW m ty = _; rw [hb, lpW, lp_derFVar])

end intern

end L.Arena
