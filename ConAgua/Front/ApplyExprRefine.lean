import ConAgua.Front.ApplyExpr
import ConAgua.Front.NatDecLink
import ConAgua.Front.StateDR
import ConAgua.Census.Attr

/-!
# `apply_expr` refines con-ron's `parseExprEntryD`

`applyExprW_refines`: if `apply_expr(pl, idx, a, c, d)`'s model succeeds on fields `f` that con-leche's
scanner relates to the expression record `r` (`ExprR`, `ExprIface.lean`), then
`parseExprEntryD st i r` succeeds and the memory after is related to its arena state by `ArenaD`
and to its parse state by `StateDR`.

The leaf interns (`sort`, `const`, `lit`, the level list) keep `DerR`: a leaf's range is `0`
(`bvarOfData` of its derived word), and the level-list table is outside the expression tiers.
These lemmas (`internSort_D`, `internConst_D`, `internLit_D`, `internLs_D`) are of the shape of
`DerRel.lean`'s `internBVar_D` and could move there.
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConRon.Arena ConLeche
open ConRon.Arena.Frontend
open ConLeche.Frontend
open L.Front.Fields (rdNatN NONE itemsN listN Fld)
open ConAgua.Front.FieldsLink

set_option linter.unusedSimpArgs false

namespace L.Front

/-! ## The leaf interns under `ArenaD` -/

theorem bvar_derSort (st : EStore) (u : LIdx) : bvarOfData (st.derOfView (.sort u)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfSort]
  exact bvarOfData_pack _ _ _ _ (by decide) (by decide)

theorem bvar_derConst (st : EStore) (n : NIdx) (us : LsIdx) :
    bvarOfData (st.derOfView (.const n us)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfConst]
  exact bvarOfData_pack _ _ _ _ (by decide) (by decide)

theorem bvar_derLit (st : EStore) (l : ConLeche.Literal) :
    bvarOfData (st.derOfView (.lit l)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfLit]
  exact bvarOfData_pack _ _ _ _ (by decide) (by decide)

section leaves
variable (m : Mem) (a : AState) (hA : ArenaD m a) (r : Word) (m' : Mem)
include hA

theorem internBVar_DF (u : Word) (hI : binternW m u = some (r, m')) :
    AM.ok (internE (.bvar u.toNat)) a ∧ ArenaD m' (AM.st (internE (.bvar u.toNat)) a) ∧
    AM.res (internE (.bvar u.toNat)) a = decE r ∧
    MemFrame [bvarSch.ra, bvarSch.sa] [bvarSch.ca, bvarSch.ca + 1] m m' := by
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hA u r m' hI
  have hI₂ := hI; rw [binternW_eq] at hI₂
  exact ⟨hok, hD, hres, internM_frame _ bvarSch_wf _ _ _ _ _ _ _ _ hI₂⟩

theorem internSort_D (u : Word) (hu : u.toNat < 2 ^ 32) (hI : sointernW m u = some (r, m')) :
    AM.ok (internE (.sort (decI u))) a ∧ ArenaD m' (AM.st (internE (.sort (decI u))) a) ∧
    AM.res (internE (.sort (decI u))) a = decI r ∧
    MemFrame [sortSch.ra, sortSch.sa] [sortSch.ca, sortSch.ca + 1] m m' := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := sointern_correct m a hR.sort u hu _ _ hI
  have hI₂ := hI; rw [sointernW_eq] at hI₂
  have hfr := internM_frame _ sortSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases sortLens _ _ _ _ _ _ a (internE_sort_run _ a) hok
  have hR₁ := hR.lift_sort _ _ _ _ hX hfr
    (AM.st_proto sortLens _ _ _ _ _ _ a (internE_sort_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [sortSch, SOREC, SOSLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres, hfr⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, ⟨derT_push hD₁.sort.1 _ _ _ (bvar_derSort _ _), hD₁.sort.2⟩,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, ⟨hD₁.sort.1, derT_push hD₁.sort.2 _ _ _ (bvar_derSort _ _)⟩,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩

theorem internConst_D (f x : Word) (hf : f.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32)
    (hI : ceinternW m f x = some (r, m')) :
    AM.ok (internE (.const (decI f) (decI x))) a ∧
    ArenaD m' (AM.st (internE (.const (decI f) (decI x))) a) ∧
    AM.res (internE (.const (decI f) (decI x))) a = decI r ∧
    MemFrame [constSch.ra, constSch.sa] [constSch.ca, constSch.ca + 1] m m' := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := ceintern_correct m a hR.const f x hf hx _ _ hI
  have hI₂ := hI; rw [ceinternW_eq] at hI₂
  have hfr := internM_frame _ constSch_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok
  have hR₁ := hR.lift_const _ _ _ _ hX hfr
    (AM.st_proto constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [constSch, CREC, CSLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres, hfr⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, ⟨derT_push hD₁.const.1 _ _ _ (bvar_derConst _ _ _),
      hD₁.const.2⟩, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, ⟨hD₁.const.1, derT_push hD₁.const.2 _ _ _
      (bvar_derConst _ _ _)⟩, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩

theorem internLit_D (o l : Word) (hq : SliceOK m o l) (hn : Norm (m.arr64 POOL) o.toNat l.toNat)
    (hI : internW m o l = some (r, m')) :
    AM.ok (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a ∧
    ArenaD m' (AM.st (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a) ∧
    AM.res (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a = decE r ∧
    MemFrame [litSch.ra, litSch.sa] [litSch.ca, litSch.ca + 1] m m' := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := intern_correct m a hR.lit o l hq hn _ _ hI
  have hI₂ := hI; rw [internW_eq] at hI₂
  have hfr := internM_frame _ litS_wf _ _ _ _ _ _ _ _ hI₂
  have hcs := AM.proto_cases litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok
  have hR₁ := hR.lift_lit _ _ _ _ hX hfr
    (AM.st_proto litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [litSch, REC, SLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres, hfr⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨derT_push hD₁.lit.1 _ _ _ (bvar_derLit _ _), hD₁.lit.2⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨hD₁.lit.1, derT_push hD₁.lit.2 _ _ _ (bvar_derLit _ _)⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩

theorem internLs_D (o l : Word) (hq : SliceOK m o l) (us : List LIdx)
    (hk : sliceL (m.arr64 POOL) o.toNat l.toNat = lsWords us) (hI : lsinternW m o l = some (r, m')) :
    AM.ok (internLsNode us) a ∧ ArenaD m' (AM.st (internLsNode us) a) ∧
    AM.res (internLsNode us) a = decI r ∧
    MemFrame [lsSch.ra, lsSch.sa] [lsSch.ca, lsSch.ca + 1] m m' := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := lsintern_correct m a hR.lit.1 hR.ls o l hq us hk _ _ hI
  have hI₂ := hI; rw [lsinternW_eq] at hI₂
  have hfr := internM_frame _ lsSch_wf _ _ _ _ _ _ _ _ hI₂
  have hst := AM.st_proto lsLens _ _ _ _ _ _ a (internLsNode_run us a) hok
  exact ⟨hok, ⟨hR.lift_ls _ _ _ _ hX hfr hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩) hst (DerR.frameT hfr (by tapart) hD)⟩, hres, hfr⟩

end leaves

/-! ## Frames: nothing at or above array 64 changes -/

/-- No word array at or above `64` (`NID`, `LID`, `EID`) changes. -/
def Above64 (m m' : Mem) : Prop := ∀ B : ArrId, 64 ≤ B → m'.arr64 B = m.arr64 B

theorem Above64.trans {m₁ m₂ m₃ : Mem} (h₁ : Above64 m₁ m₂) (h₂ : Above64 m₂ m₃) : Above64 m₁ m₃ :=
  fun B hB => (h₂ B hB).trans (h₁ B hB)

theorem MemFrame.above {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64) : Above64 m m' :=
  fun B hB => hf.1 B (fun h => absurd (hA B h) (Nat.not_lt.mpr hB)) (fun h => by subst h; exact absurd hB (by decide))

theorem StateDR.above {m m' : Mem} {st : StateD} (h : StateDR m st) (hf : Above64 m m') :
    StateDR m' st :=
  ⟨by rw [hf NID (by decide)]; exact h.names, by rw [hf LID (by decide)]; exact h.levels,
    by rw [hf EID (by decide)]; exact h.exprs,
    by rw [hf DECL (by decide), hf DLP (by decide)]; exact h.decls⟩

theorem mkK_above (A : ArrId) (hA : A < 64) (hC : A ≠ CTL) (c s d r : Word) (m m' : Mem)
    (x : Option (Word × Mem)) (hx : ∀ r₁ m₁, x = some (r₁, m₁) → Above64 m m₁)
    (h : mkK A c s d x = some (r, m')) : Above64 m m' := by
  match x, hx, h with
  | some (r₁, m₁), hx, h =>
    rw [mkK_some] at h
    split at h
    · cases h
    · rename_i m₂ hP
      cases h
      exact (hx _ _ rfl).trans (MemFrame.above (derPutW_frame A hC _ _ _ _ _ _ hP)
        (by simpa using hA))

theorem mkAppW_above {m m' : Mem} {f x r : Word} (h : mkAppW m f x = some (r, m')) : Above64 m m' := by
  unfold mkAppW at h; split at h; · cases h
  exact mkK_above ADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [ainternW_eq] at hx
    exact MemFrame.above (internM_frame _ appSch_wf _ _ _ _ _ _ _ _ hx) (by simp [appSch, AREC, ASLOT])) h
theorem mkLamW_above {m m' : Mem} {f x r : Word} (h : mkLamW m f x = some (r, m')) : Above64 m m' := by
  unfold mkLamW at h; split at h; · cases h
  exact mkK_above LADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [lainternW_eq] at hx
    exact MemFrame.above (internM_frame _ lamSch_wf _ _ _ _ _ _ _ _ hx) (by simp [lamSch, LAREC, LASLOT])) h
theorem mkForallW_above {m m' : Mem} {f x r : Word} (h : mkForallW m f x = some (r, m')) :
    Above64 m m' := by
  unfold mkForallW at h; split at h; · cases h
  exact mkK_above FADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [fainternW_eq] at hx
    exact MemFrame.above (internM_frame _ forallSch_wf _ _ _ _ _ _ _ _ hx)
      (by simp [forallSch, FAREC, FASLOT])) h
theorem mkLetW_above {m m' : Mem} {t v x r : Word} (h : mkLetW m t v x = some (r, m')) :
    Above64 m m' := by
  unfold mkLetW at h; split at h; · cases h
  exact mkK_above LEDER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [leinternW_eq] at hx
    exact MemFrame.above (internM_frame _ letSch_wf _ _ _ _ _ _ _ _ hx) (by simp [letSch, LEREC, LESLOT])) h
theorem mkProjW_above {m m' : Mem} {n i e r : Word} (h : mkProjW m n i e = some (r, m')) :
    Above64 m m' := by
  unfold mkProjW at h; split at h; · cases h
  exact mkK_above PJDER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    rw [pjinternW_eq] at hx
    exact MemFrame.above (internM_frame _ projSch_wf _ _ _ _ _ _ _ _ hx) (by simp [projSch, PJREC, PJSLOT])) h

/-! ## The twin's node -/

/-- The node `parseExprEntryD` interns for a record (its `match`). -/
def exprOp (st : StateD) : ExprRec → AM EIdx
  | .bvar k => internE (.bvar k)
  | .sort u => do internE (.sort (← st.level u))
  | .const n us => do
    let nm ← st.name n
    let ls ← us.mapM st.level
    let lsh ← internLsNode ls
    internE (.const nm lsh)
  | .app f a => do internE (.app (← st.expr f) (← st.expr a))
  | .lam ty bd => do internE (.lam (← st.expr ty) (← st.expr bd))
  | .forallE ty bd => do internE (.forallE (← st.expr ty) (← st.expr bd))
  | .letE ty vl bd => do internE (.letE (← st.expr ty) (← st.expr vl) (← st.expr bd))
  | .proj tn ix s => do internE (.proj (← st.name tn) ix (← st.expr s))
  | .natVal n => internE (.lit (.natVal n))
  | .strVal s => internE (.lit (.strVal s))

theorem parseExprEntryD_eq (st : StateD) (i : Nat) (r : ExprRec) :
    parseExprEntryD st i r = (st.freshExpr i >>= fun _ => exprOp st r >>= fun e =>
      pure { st with exprs := st.exprs.insert i e }) := by
  cases r <;> simp only [parseExprEntryD, exprOp, bind_assoc]

/-- The node of `r` interned at the handle `w`, from `a`, with `ArenaD` and the tables after. -/
def NodeOK (st : StateD) (r : ExprRec) (a : AState) (m₁ : Mem) (w : Word) : Prop :=
  AM.ok (exprOp st r) a ∧ ArenaD m₁ (AM.st (exprOp st r) a) ∧ AM.res (exprOp st r) a = decI w ∧
    StateDR m₁ st

/-- A bound table entry: the table's value, a 32-bit handle, and the id is not `NONE`. -/
theorem tbl_read {k : IdxKind} {m : Mem} {b : ArrId} {t : IdTable (Idx k)} (h : TblR (m.arr64 b) t)
    (i : Word) (hok : tblOK m b i = true) :
    t.get? i.toNat = some (decI (tblW m b i)) ∧ (tblW m b i).toNat < 2 ^ 32 ∧ i ≠ NONE := by
  obtain ⟨h1, h2⟩ := h.read _ _ _ _ hok
  refine ⟨h1, h2, fun hn => ?_⟩
  have hs := h.size
  simp only [tblOK, Bool.and_eq_true, decide_eq_true_eq, Mem.len64, UInt64.lt_iff_toNat_lt] at hok
  rw [toNat_ofNat_size _ hs, hn] at hok
  have : NONE.toNat = 2 ^ 64 - 1 := rfl
  omega

theorem itemR_eq {x : Word} {n : Nat} (h : ItemR x n) (hx : x ≠ NONE) : n = x.toNat := (h hx).symm

section node
variable (b : ByteArray) (m m₁ : Mem) (hm : m.arr8 IN = b.data) (a : AState) (st : StateD)
  (hA : ArenaD m a) (hD : StateDR m st) (w : Word)
include hA hD

theorem node_bvar (k : Nat) (x y z : Word) (hx : ItemR x k) (hI : nodeW b.data m 8 x y z = some (w, m₁)) :
    NodeOK st (.bvar k) a m₁ w := by
  simp only [nodeW, ↓reduceIte] at hI
  split at hI
  · cases hI
  rename_i hn
  rw [itemR_eq hx hn]
  obtain ⟨h1, h2, h3, hf⟩ := internBVar_DF m a hA w m₁ x hI
  exact ⟨h1, h2, h3, hD.above (MemFrame.above hf (by simp [bvarSch, BREC, BSLOT]))⟩

theorem node_sort (u : Nat) (x y z : Word) (hx : ItemR x u) (hI : nodeW b.data m 9 x y z = some (w, m₁)) :
    NodeOK st (.sort u) a m₁ w := by
  simp only [nodeW, show (9 : Word) ≠ 8 by decide, ↓reduceIte] at hI
  split at hI
  · rename_i hok
    obtain ⟨hg, hw, hn⟩ := tbl_read hD.levels x hok
    rw [itemR_eq hx hn]
    have hop : exprOp st (.sort x.toNat) = internE (.sort (decI (tblW m LID x))) := by
      simp [exprOp, StateD.level, hg]
    obtain ⟨h1, h2, h3, hf⟩ := internSort_D m a hA w m₁ _ hw hI
    unfold NodeOK; rw [hop]
    exact ⟨h1, h2, h3, hD.above (MemFrame.above hf (by simp [sortSch, SOREC, SOSLOT]))⟩
  · cases hI

theorem node_bin (k : Word) (hk : k = 10 ∨ k = 11 ∨ k = 12) (x y z : Word) (p q : Nat)
    (hx : ItemR x p) (hy : ItemR y q) (r : ExprRec)
    (hr : r = (if k = 10 then ExprRec.app else if k = 11 then ExprRec.lam else ExprRec.forallE) p q)
    (hI : nodeW b.data m k x y z = some (w, m₁)) : NodeOK st r a m₁ w := by
  have hk8 : k ≠ 8 := by rcases hk with rfl | rfl | rfl <;> decide
  have hk9 : k ≠ 9 := by rcases hk with rfl | rfl | rfl <;> decide
  simp only [nodeW, hk8, hk9, hk, ↓reduceIte, binW] at hI
  split at hI
  · rename_i hok
    obtain ⟨hgx, hwx, hnx⟩ := tbl_read hD.exprs x hok.1
    obtain ⟨hgy, hwy, hny⟩ := tbl_read hD.exprs y hok.2
    rw [itemR_eq hx hnx, itemR_eq hy hny] at hr
    rcases hk with rfl | rfl | rfl
    · simp only [↓reduceIte] at hI hr; subst hr
      have hop : exprOp st (.app x.toNat y.toNat) =
          internE (.app (decI (tblW m EID x)) (decI (tblW m EID y))) := by
        simp [exprOp, StateD.expr, hgx, hgy]
      obtain ⟨h1, h2, h3⟩ := mkApp_ok m a hA _ _ _ _ hI
      unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkAppW_above hI)⟩
    · simp only [show (11 : Word) ≠ 10 by decide, ↓reduceIte] at hI hr; subst hr
      have hop : exprOp st (.lam x.toNat y.toNat) =
          internE (.lam (decI (tblW m EID x)) (decI (tblW m EID y))) := by
        simp [exprOp, StateD.expr, hgx, hgy]
      obtain ⟨h1, h2, h3⟩ := mkLam_ok m a hA _ _ _ _ hI
      unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkLamW_above hI)⟩
    · simp only [show (12 : Word) ≠ 10 by decide, show (12 : Word) ≠ 11 by decide,
        ↓reduceIte] at hI hr; subst hr
      have hop : exprOp st (.forallE x.toNat y.toNat) =
          internE (.forallE (decI (tblW m EID x)) (decI (tblW m EID y))) := by
        simp [exprOp, StateD.expr, hgx, hgy]
      obtain ⟨h1, h2, h3⟩ := mkForall_ok m a hA _ _ _ _ hI
      unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkForallW_above hI)⟩
  · cases hI

theorem node_let (x y z : Word) (p q t : Nat) (hx : ItemR x p) (hy : ItemR y q) (hz : ItemR z t)
    (hI : nodeW b.data m 13 x y z = some (w, m₁)) : NodeOK st (.letE p q t) a m₁ w := by
  simp only [nodeW, show (13 : Word) ≠ 8 by decide, show (13 : Word) ≠ 9 by decide,
    show (13 : Word) ≠ 10 by decide, show (13 : Word) ≠ 11 by decide,
    show (13 : Word) ≠ 12 by decide, false_or, or_false, ↓reduceIte, letW] at hI
  split at hI
  · rename_i hok
    obtain ⟨hgx, -, hnx⟩ := tbl_read hD.exprs x hok.1
    obtain ⟨hgy, -, hny⟩ := tbl_read hD.exprs y hok.2.1
    obtain ⟨hgz, -, hnz⟩ := tbl_read hD.exprs z hok.2.2
    rw [itemR_eq hx hnx, itemR_eq hy hny, itemR_eq hz hnz]
    have hop : exprOp st (.letE x.toNat y.toNat z.toNat) =
        internE (.letE (decI (tblW m EID x)) (decI (tblW m EID y)) (decI (tblW m EID z))) := by
      simp [exprOp, StateD.expr, hgx, hgy, hgz]
    obtain ⟨h1, h2, h3⟩ := mkLet_ok m a hA _ _ _ _ _ hI
    unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkLetW_above hI)⟩
  · cases hI

theorem node_proj (x y z : Word) (p q t : Nat) (hx : ItemR x p) (hy : ItemR y q) (hz : ItemR z t)
    (hI : nodeW b.data m 14 x y z = some (w, m₁)) : NodeOK st (.proj p q t) a m₁ w := by
  simp only [nodeW, show (14 : Word) ≠ 8 by decide, show (14 : Word) ≠ 9 by decide,
    show (14 : Word) ≠ 10 by decide, show (14 : Word) ≠ 11 by decide,
    show (14 : Word) ≠ 12 by decide, show (14 : Word) ≠ 13 by decide, false_or, or_false,
    ↓reduceIte, projW] at hI
  split at hI
  · rename_i hok
    obtain ⟨hgx, -, hnx⟩ := tbl_read hD.names x hok.2.1
    obtain ⟨hgz, -, hnz⟩ := tbl_read hD.exprs z hok.2.2
    rw [itemR_eq hx hnx, itemR_eq hy hok.1, itemR_eq hz hnz]
    have hop : exprOp st (.proj x.toNat y.toNat z.toNat) =
        internE (.proj (decI (tblW m NID x)) y.toNat (decI (tblW m EID z))) := by
      simp [exprOp, StateD.expr, StateD.name, hgx, hgz]
    obtain ⟨h1, h2, h3⟩ := mkProj_ok m a hA _ _ _ _ _ hI
    unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkProjW_above hI)⟩
  · cases hI

theorem node_lit (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (x y z : Word)
    (n : Nat) (hv : NatValR b y z n) (hI : nodeW b.data m 16 x y z = some (w, m₁)) :
    NodeOK st (.natVal n) a m₁ w := by
  simp only [nodeW, show (16 : Word) ≠ 8 by decide, show (16 : Word) ≠ 9 by decide,
    show (16 : Word) ≠ 10 by decide, show (16 : Word) ≠ 11 by decide,
    show (16 : Word) ≠ 12 by decide, show (16 : Word) ≠ 13 by decide,
    show (16 : Word) ≠ 14 by decide, show (16 : Word) ≠ 15 by decide, false_or, or_false,
    ↓reduceIte, litW] at hI
  obtain ⟨hcd, -, hdig, hn⟩ := natValR_decN b h64 hsize y z n hv
  cases hN : natDecW b.data m y z with
  | none => rw [hN, litK_none] at hI; cases hI
  | some q =>
  obtain ⟨r, m₂⟩ := q
  obtain ⟨l, rfl, hg, hsl, hnm, hpv⟩ :=
    natDecW_val b.data m m₂ y z r hA.1.lit.1 (UInt64.le_of_lt hcd) hdig hN
  rw [hN] at hI
  simp only [litK, List.headD_cons, List.tail_cons] at hI
  by_cases c1 : m₂.len64 POOL < m.top
  · simp [c1] at hI
  by_cases c2 : m₂.len64 POOL - m.top < l
  · simp [c2] at hI
  simp only [c1, c2, if_false] at hI
  have hA' := ArenaD.grow m m₂ hg a hA
  obtain ⟨h1, h2, h3, hf⟩ := internLit_D m₂ a hA' w m₁ m.top l hsl hnm hI
  rw [hpv, ← hn] at h1 h2 h3
  exact ⟨h1, h2, h3, (hD.frame (grows_frame _ _ hg) (by tapart) (by tapart)).above
    (MemFrame.above hf (by simp [litSch, REC, SLOT]))⟩

omit hA hD in
/-- A universe list whose items are bound level ids: `mapM st.level` is pure. -/
theorem mapM_level (hL : TblR (m.arr64 LID) st.levels) :
    ∀ (xs : List Word) (us : List Nat), ItemsR xs us → (∀ x ∈ xs, tblOK m LID x = true) →
      us.mapM st.level = pure (xs.map fun x => decI (tblW m LID x))
  | [], [], _, _ => rfl
  | x :: xs, u :: us, ⟨hx, hxs⟩, hok => by
    obtain ⟨hg, -, hn⟩ := tbl_read hL x (hok x (by simp))
    rw [List.mapM_cons, itemR_eq hx hn,
      mapM_level hL xs us hxs (fun y hy => hok y (by simp [hy]))]
    simp [StateD.level, hg]
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

omit hA hD in
theorem lsWords_map (xs : List Word) (hw : ∀ x ∈ xs, (tblW m LID x).toNat < 2 ^ 32) :
    lsWords (xs.map fun x => (decI (tblW m LID x) : LIdx)) = xs.map (tblW m LID) := by
  simp only [lsWords, List.map_map]
  apply List.map_congr_left
  intro x hx
  exact (word_decI (decI (tblW m LID x) : LIdx) _ (hw x hx)).mpr rfl

theorem node_const (x c z : Word) (nm : Nat) (us : List Nat) (hx : ItemR x nm)
    (hus : ItemsR (listN b.data c) us) (hI : nodeW b.data m 15 x c z = some (w, m₁)) :
    NodeOK st (.const nm us) a m₁ w := by
  simp only [nodeW, show (15 : Word) ≠ 8 by decide, show (15 : Word) ≠ 9 by decide,
    show (15 : Word) ≠ 10 by decide, show (15 : Word) ≠ 11 by decide,
    show (15 : Word) ≠ 12 by decide, show (15 : Word) ≠ 13 by decide,
    show (15 : Word) ≠ 14 by decide, false_or, or_false, ↓reduceIte, constW] at hI
  have hok : tblOK m NID x = true :=
    Classical.byContradiction fun hok => by simp [hok] at hI
  simp only [hok, ↓reduceIte] at hI
  obtain ⟨hgn, hwn, hn⟩ := tbl_read hD.names x hok
  rw [itemR_eq hx hn]
  cases hP : lsPutW b.data m c with
  | none => simp [hP, constK] at hI
  | some m₂ =>
  simp only [hP, constK] at hI
  cases hL : lsinternW m₂ m.top (lsPutL b.data c) with
  | none => simp [hL, constK2] at hI
  | some p =>
  obtain ⟨g, m₃⟩ := p
  simp only [hL, constK2] at hI
  have hg32 : g < 0x100000000 :=
    Classical.byContradiction fun h => by simp [h] at hI
  simp only [hg32, ↓reduceIte] at hI
  have hg32' : g.toNat < 2 ^ 32 := by simpa [UInt64.lt_iff_toNat_lt] using hg32
  -- `ls_put`: the pool grew by the items' level handles
  obtain ⟨hW, hc, hps, htop⟩ := hA.1.lit.1
  have hlen : (m.len64 POOL).toNat = (m.arr64 POOL).size := by
    simp only [Mem.len64]; exact toNat_ofNat_size _ hps
  unfold lsPutW at hP
  split at hP
  · cases hP
  rename_i hle
  obtain ⟨F1, F3, F4, F5, F6, F7, F8⟩ := lsLoopM_facts b.data m.top m (c + 1) 0 m₂ hP
    (by simpa using htop) hps
  obtain ⟨F2, F9⟩ := F8 hc
  simp only [UInt64.toNat_zero, Nat.zero_add, Nat.add_zero] at F1 F4 F5 F6
  have hcnt := (lsCntN b.data (c + 1) 0).toNat_lt
  have htc : (m.top + lsCntN b.data (c + 1) 0).toNat = m.top.toNat + (lsCntN b.data (c + 1) 0).toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hg : Grows m m₂ := ⟨F9, fun j hj => F5 j hj, by rw [F2, htc]; omega,
    by rw [F2, htc]; omega, F3⟩
  have hab : Above64 m m₂ := fun B hB => by
    rw [F9.2.2 B (fun h => by subst h; exact absurd hB (by decide)),
      Mem.arr64_set64_ne _ _ _ _ _ (fun h => by subst h; exact absurd hB (by decide))]
  have hA₂ := ArenaD.grow m m₂ hg a hA
  -- the twin's universe list
  have hxs : itemsN b.data (c + 1) = listN b.data c := rfl
  rw [hxs] at F1 F6 F7
  have hmap := mapM_level m st hD.levels _ us hus F7
  have hwl : ∀ y ∈ listN b.data c, (tblW m LID y).toNat < 2 ^ 32 :=
    fun y hy => (tbl_read hD.levels y (F7 y hy)).2.1
  have hk : sliceL (m₂.arr64 POOL) m.top.toNat (lsPutL b.data c).toNat =
      lsWords ((listN b.data c).map fun y => (decI (tblW m LID y) : LIdx)) := by
    rw [lsWords_map m _ hwl, sliceL, List.ext_getElem_iff]
    simp only [lsPutL, F1, List.length_ofFn, List.length_map, true_and]
    intro k hk₁ hk₂
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [F6 k (by simpa using hk₂)]; rfl
  have hq : SliceOK m₂ m.top (lsPutL b.data c) := by
    simp only [SliceOK, F2, htc, lsPutL]; omega
  obtain ⟨l1, l2, l3, lf⟩ := internLs_D m₂ a hA₂ g m₃ m.top _ hq _ hk hL
  obtain ⟨c1, c2, c3, cf⟩ := internConst_D m₃ _ l2 w m₁ (tblW m NID x) g hwn hg32' hI
  have hop : exprOp st (.const x.toNat us) =
      (internLsNode ((listN b.data c).map fun y => (decI (tblW m LID y) : LIdx)) >>= fun lsh =>
        internE (.const (decI (tblW m NID x)) lsh)) := by
    simp [exprOp, StateD.name, hgn, hmap]
  have hok' : AM.ok (exprOp st (.const x.toNat us)) a := by
    rw [hop, AM.ok_bind, l3]; exact ⟨l1, c1⟩
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hop] at hok' ⊢; rw [AM.st_bind _ _ _ hok', l3]; exact c2
  · rw [hop, AM.res_bind _ _ _ l1, l3]; exact c3
  · exact ((hD.above hab).above (MemFrame.above lf (by simp [lsSch, LSREC, LSSLOT]))).above
      (MemFrame.above cf (by simp [constSch, CREC, CSLOT]))

/-- **Every expression kind**: the node the fields `f` describe is interned. -/
theorem node_ok (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (f : Fld)
    (r : ExprRec) (hE : ExprR b r f)
    (hI : nodeW b.data m f.pl f.a f.c f.d = some (w, m₁)) : NodeOK st r a m₁ w := by
  cases r with
  | bvar k => obtain ⟨hp, hx⟩ := hE; rw [hp] at hI; exact node_bvar b m m₁ a st hA hD w k _ _ _ hx hI
  | sort u => obtain ⟨hp, hx⟩ := hE; rw [hp] at hI; exact node_sort b m m₁ a st hA hD w u _ _ _ hx hI
  | app p q =>
    obtain ⟨hp, hx, hy⟩ := hE; rw [hp] at hI
    exact node_bin b m m₁ a st hA hD w 10 (.inl rfl) _ _ _ p q hx hy _ rfl hI
  | lam p q =>
    obtain ⟨hp, hx, hy⟩ := hE; rw [hp] at hI
    exact node_bin b m m₁ a st hA hD w 11 (.inr (.inl rfl)) _ _ _ p q hx hy _ rfl hI
  | forallE p q =>
    obtain ⟨hp, hx, hy⟩ := hE; rw [hp] at hI
    exact node_bin b m m₁ a st hA hD w 12 (.inr (.inr rfl)) _ _ _ p q hx hy _ rfl hI
  | letE p q t =>
    obtain ⟨hp, hx, hy, hz⟩ := hE; rw [hp] at hI
    exact node_let b m m₁ a st hA hD w _ _ _ p q t hx hy hz hI
  | proj p q t =>
    obtain ⟨hp, hx, hy, hz⟩ := hE; rw [hp] at hI
    exact node_proj b m m₁ a st hA hD w _ _ _ p q t hx hy hz hI
  | const nm us =>
    obtain ⟨hp, hx, hus⟩ := hE; rw [hp] at hI
    exact node_const b m m₁ a st hA hD w _ _ _ nm us hx hus hI
  | natVal n =>
    obtain ⟨hp, -, hv⟩ := hE; rw [hp] at hI
    exact node_lit b m m₁ a st hA hD w h64 hsize _ _ _ n hv hI
  | strVal s =>
    obtain ⟨hp, -⟩ := hE; rw [hp] at hI
    simp [nodeW] at hI

end node

/-- An unbound table entry: the id is not `NONE`. -/
theorem tbl_fresh_ne {k : IdxKind} {m : Mem} {b : ArrId} {t : IdTable (Idx k)}
    (h : TblR (m.arr64 b) t) (i : Word) (hf : tblFresh m b i = true) : i ≠ NONE := by
  intro hn
  have hs := h.size
  simp only [tblFresh, Bool.and_eq_true, decide_eq_true_eq, Mem.len64,
    UInt64.lt_iff_toNat_lt] at hf
  rw [toNat_ofNat_size _ hs, hn] at hf
  have : NONE.toNat = 2 ^ 64 - 1 := rfl
  omega

/-- **`apply_expr`'s model refines `parseExprEntryD`**: on fields `f` that con-leche's scanner
relates to the expression record `r` (`ExprR`) and an index word read for `i`, a successful
`apply_expr` is a successful `parseExprEntryD st i r`, with `ArenaD` and `StateDR` after. -/
@[refines_part ConRon.Arena.Frontend.parseExprEntryD "every kind but strVal"]
theorem applyExprW_refines (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (m m' : Mem) (a₀ : AState)
    (st : StateD) (hA : ArenaD m a₀) (hD : StateDR m st) (f : Fld) (i : Nat) (r : ExprRec)
    (hI : ItemR f.idx i) (hE : ExprR b r f)
    (h : applyExprW b.data m f.pl f.idx f.a f.c f.d = some m') :
    AM.ok (parseExprEntryD st i r) a₀ ∧ ArenaD m' (AM.st (parseExprEntryD st i r) a₀) ∧
      StateDR m' (AM.res (parseExprEntryD st i r) a₀) := by
  unfold applyExprW at h
  have hfr : tblFresh m EID f.idx = true :=
    Classical.byContradiction fun hf => by simp [hf] at h
  simp only [hfr, ↓reduceIte] at h
  have hnone := hD.exprs.fresh _ _ _ _ hfr
  rw [itemR_eq hI (tbl_fresh_ne hD.exprs _ hfr)]
  obtain ⟨w, m₁, hN, hw, hi, rfl⟩ := putK_eq h
  obtain ⟨h1, h2, h3, h4⟩ := node_ok b m m₁ a₀ st hA hD w h64 hsize f r hE hN
  have hfresh : st.freshExpr f.idx.toNat = pure () := by
    simp [StateD.freshExpr, IdTable.bound_eq, hnone]
  rw [parseExprEntryD_eq, hfresh, pure_bind]
  obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
    (fun e => { st with exprs := st.exprs.insert f.idx.toNat e }) a₀ h1
  refine ⟨hok₂, by rw [hst₂]; exact ArenaD.setT _ _ h2 _ (.inr (.inr rfl)) _ _, ?_⟩
  rw [hres₂, h3]
  exact h4.putExpr (MemFrame.refl [] [] m₁) (by simp) (by simp) (by simp) f.idx w hi hw _
    (fun j => IdTable.get?_insert _ _ _ _) rfl rfl

end L.Front
