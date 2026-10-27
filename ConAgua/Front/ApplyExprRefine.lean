import ConAgua.Front.NatDecLink
import ConAgua.Front.UnescapeLink
import ConAgua.Front.StateDR
import Std.Tactic.BVDecide.Normalize.Prop

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
open L.Front.Unescape (strPutEscW)


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
    MemFrame [bvarSch.ra, bvarSch.ra + 256, bvarSch.sa, bvarSch.sa + 256] [bvarSch.ca, bvarSch.ca + 1] m m' := by
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hA u r m' hI
  have hI₂ := hI
  exact ⟨hok, hD, hres, consInternM_frame bvarCS_wf hI₂⟩

theorem internSort_D (u : Word) (hu : u.toNat < 2 ^ 32) (hI : sointernW m u = some (r, m')) :
    AM.ok (internE (.sort (decI u))) a ∧ ArenaD m' (AM.st (internE (.sort (decI u))) a) ∧
    AM.res (internE (.sort (decI u))) a = decI r ∧
    MemFrame [sortSch.ra, sortSch.ra + 256, sortSch.sa, sortSch.sa + 256, SOLP, SOLP + 256] [sortSch.ca, sortSch.ca + 1] m m' := by
  obtain ⟨hok, hD', hres⟩ := L.Arena.internSort_D m a hA u r hu m' hI
  exact ⟨hok, hD', hres, sointernW_frame (hI := hI)⟩

theorem internConst_D (f x : Word) (hf : f.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32)
    (hI : ceinternW m f x = some (r, m')) :
    AM.ok (internE (.const (decI f) (decI x))) a ∧
    ArenaD m' (AM.st (internE (.const (decI f) (decI x))) a) ∧
    AM.res (internE (.const (decI f) (decI x))) a = decI r ∧
    MemFrame [constSch.ra, constSch.ra + 256, constSch.sa, constSch.sa + 256, CLP, CLP + 256] [constSch.ca, constSch.ca + 1] m m' := by
  obtain ⟨hok, hD', hres⟩ := L.Arena.internConst_D m a hA f x r hf hx m' hI
  exact ⟨hok, hD', hres, ceinternW_frame (hI := hI)⟩

theorem internLit_D (o l : Word) (hq : SliceOK m o l) (hn : Norm (vpool m) o.toNat l.toNat)
    (hq0 : m.flag = 0 → o.toNat < 2 ^ 40) (hI : internW m o l = some (r, m')) :
    AM.ok (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a ∧
    ArenaD m' (AM.st (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a) ∧
    AM.res (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a = decE r ∧
    MemFrame [litSch.ra, litSch.ra + 256, litSch.sa, litSch.sa + 256] [litSch.ca, litSch.ca + 1] m m' := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := intern_correct m a hR.lit o l hq hn hq0 _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame litCS_wf hI₂
  have hcs := AM.proto_cases litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok
  have hR₁ := hR.lift_lit _ _ _ _ hX hfr
    (AM.st_proto litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [ConsSch.wset, litCS, litCSk, REC, SLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres, hfr⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨derT_push hD₁.lit.1 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩, hD₁.lit.2⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨hD₁.lit.1, derT_push hD₁.lit.2 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩

theorem internLitStr_D (o l : Word) (hq : SliceOK m o l) (s : String)
    (hk : sliceL (vpool m) o.toNat l.toNat = strWords s) (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)
    (hI : internWStr m o l = some (r, m')) :
    AM.ok (internE (.lit (.strVal s))) a ∧
    ArenaD m' (AM.st (internE (.lit (.strVal s))) a) ∧
    AM.res (internE (.lit (.strVal s))) a = decE r ∧
    MemFrame [litSch.ra, litSch.ra + 256, litSch.sa, litSch.sa + 256] [litSch.ca, litSch.ca + 1] m m' := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := internStr_correct m a hR.lit o l hq s hk hq0 _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame litStrCS_wf hI₂
  have hcs := AM.proto_cases litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok
  have hR₁ := hR.lift_lit _ _ _ _ hX hfr
    (AM.st_proto litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [ConsSch.wset, litStrCS, litCSk, REC, SLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres, hfr⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨derT_push hD₁.lit.1 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩, hD₁.lit.2⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨hD₁.lit.1, derT_push hD₁.lit.2 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩

theorem internLs_D (o l : Word) (hq : SliceOK m o l) (us : List LIdx)
    (hk : sliceL (vpool m) o.toNat l.toNat = lsWords us) (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)
    (hI : lsinternW m o l = some (r, m')) :
    AM.ok (internLsNode us) a ∧ ArenaD m' (AM.st (internLsNode us) a) ∧
    AM.res (internLsNode us) a = decI r ∧
    MemFrame [lsSch.ra, lsSch.ra + 256, lsSch.sa, lsSch.sa + 256, LSHP, LSHP + 256] [lsSch.ca, lsSch.ca + 1] m m' := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := lsintern_correct m a hR.lit.1 hR.ls o l hq us hk hq0 _ _ hI
  have hLp := lsintern_hp m a hR.lit.1 hR.ls o l hq us hk hq0 hR.lsHp (lsOrW_ok m a hR o l hq us hk) _ _ hI
  have hfr := (lsinternW_frame (hI := hI))
  have hst := AM.st_proto lsLens _ _ _ _ _ _ a (internLsNode_run us a) hok
  exact ⟨hok, ⟨hR.lift_ls _ _ _ _ ⟨hX, hLp⟩ hfr hst, derR_lss _ (fun _ _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩) hst (DerR.frameT hfr (by tapart) hD)⟩, hres, hfr⟩

end leaves

/-! ## Frames: nothing at or above array 64 changes -/

/-- No word array and no `CTL` word at or above `64` (the id tables) changes, but the store tier's
tier-1 arrays `256‥319`. -/
def Above64 (m m' : Mem) : Prop :=
  MemFrame lowTierArrs ((List.range 64).map UInt64.ofNat) m m'

theorem Above64.trans {m₁ m₂ m₃ : Mem} (h₁ : Above64 m₁ m₂) (h₂ : Above64 m₂ m₃) : Above64 m₁ m₃ :=
  MemFrame.trans h₁ h₂

theorem MemFrame.above {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64 := by tctl) : Above64 m m' :=
  hf.mono (fun b hb => low_tier_mem b (hA b hb))
    (fun x hx => by
      have := hC x hx
      simp only [List.mem_map, List.mem_range]
      exact ⟨x.toNat, this, by simp⟩)

theorem not_low_tier (b : Nat) (h : 64 ≤ b ∧ b < 256) : b ∉ lowTierArrs := by
  simp only [lowTierArrs, List.mem_append, List.mem_range, List.mem_map, not_or, not_exists, not_and]
  exact ⟨by omega, fun y hy e => by omega⟩

theorem StateDR.above {m m' : Mem} {st : StateD} (h : StateDR m st) (hf : Above64 m m') :
    StateDR m' st :=
  h.frame hf (not_low_tier _ (by simp [NID])) (not_low_tier _ (by simp [LID]))
    (not_low_tier _ (by simp [EID])) (not_low_tier _ (by simp [DECL])) (not_low_tier _ (by simp [DLP]))
    (fun x hx h => by
      simp only [idArrs, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [lowTierArrs, List.mem_append, List.mem_range, List.mem_map] at hx
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hx with hx | ⟨y, hy, hy'⟩ <;>
        first | (revert hx; decide) | (have h' : (y : Nat) + 256 = _ := hy'; omega)) (fun x hx => by
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      intro h
      have h2 : (UInt64.ofNat n).toNat < 64 := by
        rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]; exact hn
      simp only [idCtl, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h <;> rw [h] at h2 <;> simp at h2)

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
        (fun b hb => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact .inl hA
          · exact .inr ⟨Nat.le_add_left _ _, Nat.add_lt_add_right hA 256⟩))

theorem mkAppW_above {m m' : Mem} {f x r : Word} (h : mkAppW m f x = some (r, m')) : Above64 m m' := by
  unfold mkAppW at h; split at h; · cases h
  exact mkK_above ADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact MemFrame.above (consInternM_frame appCS_wf hx) (by simp [ConsSch.wset, appCS, AREC, ASLOT])) h
theorem mkLamW_above {m m' : Mem} {f x r : Word} (h : mkLamW m f x = some (r, m')) : Above64 m m' := by
  unfold mkLamW at h; split at h; · cases h
  exact mkK_above LADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact MemFrame.above (consInternM_frame lamCS_wf hx) (by simp [ConsSch.wset, lamCS, LAREC, LASLOT])) h
theorem mkForallW_above {m m' : Mem} {f x r : Word} (h : mkForallW m f x = some (r, m')) :
    Above64 m m' := by
  unfold mkForallW at h; split at h; · cases h
  exact mkK_above FADER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact MemFrame.above (consInternM_frame forallCS_wf hx)
      (by simp [ConsSch.wset, forallCS, FAREC, FASLOT])) h
theorem mkLetW_above {m m' : Mem} {t v x r : Word} (h : mkLetW m t v x = some (r, m')) :
    Above64 m m' := by
  unfold mkLetW at h; split at h; · cases h
  exact mkK_above LEDER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact MemFrame.above (consInternM_frame letCS_wf hx) (by simp [ConsSch.wset, letCS, LEREC, LESLOT])) h
theorem mkProjW_above {m m' : Mem} {n i e r : Word} (h : mkProjW m n i e = some (r, m')) :
    Above64 m m' := by
  unfold mkProjW at h; split at h; · cases h
  exact mkK_above PJDER (by decide) (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx => by
    exact MemFrame.above (consInternM_frame projCS_wf hx) (by simp [ConsSch.wset, projCS, PJREC, PJSLOT])) h

theorem mkK_mode (A : ArrId) (hC : A ≠ CTL) (c s d r : Word) (m m' : Mem)
    (x : Option (Word × Mem)) (hx : ∀ r₁ m₁, x = some (r₁, m₁) → ModeOK m → ModeOK m₁)
    (h : mkK A c s d x = some (r, m')) (hmo : ModeOK m) : ModeOK m' := by
  match x, hx, h with
  | some (r₁, m₁), hx, h =>
    rw [mkK_some] at h
    split at h
    · cases h
    · rename_i m₂ hP
      cases h
      exact MemFrame.modeOK (derPutW_frame A hC _ _ _ _ _ _ hP) (by simp) (by simp) (hx _ _ rfl hmo)

theorem mkAppW_mode {m m' : Mem} {f x r : Word} (h : mkAppW m f x = some (r, m')) (hmo : ModeOK m) :
    ModeOK m' := by
  unfold mkAppW at h; split at h; · cases h
  exact mkK_mode ADER (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx =>
    MemFrame.modeOK (consInternM_frame appCS_wf hx) (by decide) (by decide)) h hmo
theorem mkLamW_mode {m m' : Mem} {f x r : Word} (h : mkLamW m f x = some (r, m')) (hmo : ModeOK m) :
    ModeOK m' := by
  unfold mkLamW at h; split at h; · cases h
  exact mkK_mode LADER (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx =>
    MemFrame.modeOK (consInternM_frame lamCS_wf hx) (by decide) (by decide)) h hmo
theorem mkForallW_mode {m m' : Mem} {f x r : Word} (h : mkForallW m f x = some (r, m'))
    (hmo : ModeOK m) : ModeOK m' := by
  unfold mkForallW at h; split at h; · cases h
  exact mkK_mode FADER (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx =>
    MemFrame.modeOK (consInternM_frame forallCS_wf hx) (by decide) (by decide)) h hmo
theorem mkLetW_mode {m m' : Mem} {t v x r : Word} (h : mkLetW m t v x = some (r, m'))
    (hmo : ModeOK m) : ModeOK m' := by
  unfold mkLetW at h; split at h; · cases h
  exact mkK_mode LEDER (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx =>
    MemFrame.modeOK (consInternM_frame letCS_wf hx) (by decide) (by decide)) h hmo
theorem mkProjW_mode {m m' : Mem} {n i e r : Word} (h : mkProjW m n i e = some (r, m'))
    (hmo : ModeOK m) : ModeOK m' := by
  unfold mkProjW at h; split at h; · cases h
  exact mkK_mode PJDER (by decide) _ _ _ _ _ _ _ (fun r₁ m₁ hx =>
    MemFrame.modeOK (consInternM_frame projCS_wf hx) (by decide) (by decide)) h hmo

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
    StateDR m₁ st ∧ ModeOK m₁

/-- A bound table entry: the table's value, a 32-bit handle, and the id is not `NONE`. -/
theorem tbl_read {k : IdxKind} {m : Mem} {b : ArrId} {t : IdTable (Idx k)} (h : TblR m b t)
    (i : Word) (hok : tblOK m b i = true) :
    t.get? i.toNat = some (decI (tblW m b i)) ∧ (tblW m b i).toNat < 2 ^ 32 ∧ i ≠ NONE := by
  obtain ⟨h1, h2⟩ := h.read _ _ _ _ hok
  exact ⟨h1, h2, tblOK_ne_tomb i hok⟩

theorem itemR_eq {x : Word} {n : Nat} (h : ItemR x n) (hx : x ≠ NONE) : n = x.toNat := (h hx).symm

section node
variable (b : ByteArray) (m m₁ : Mem) (hm : m.arr8 IN = b.data) (a : AState) (st : StateD)
  (hA : ArenaD m a) (hD : StateDR m st) (hmode : ModeOK m) (w : Word)
include hA hD hmode

theorem node_bvar (k : Nat) (x y z : Word) (hx : ItemR x k) (hI : nodeW b.data m 8 x y z = some (w, m₁)) :
    NodeOK st (.bvar k) a m₁ w := by
  simp only [nodeW, ↓reduceIte] at hI
  split at hI
  · cases hI
  rename_i hn
  rw [itemR_eq hx hn]
  obtain ⟨h1, h2, h3, hf⟩ := internBVar_DF m a hA w m₁ x hI
  exact ⟨h1, h2, h3, hD.above (MemFrame.above hf (by simp [bvarSch, BREC, BSLOT])),
    MemFrame.modeOK hf (by decide) (by decide) hmode⟩

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
    exact ⟨h1, h2, h3, hD.above (MemFrame.above hf (by simp [sortSch, SOREC, SOSLOT, SOLP])),
      MemFrame.modeOK hf (by decide) (by decide) hmode⟩
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
      unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkAppW_above hI), mkAppW_mode hI hmode⟩
    · simp only [show (11 : Word) ≠ 10 by decide, ↓reduceIte] at hI hr; subst hr
      have hop : exprOp st (.lam x.toNat y.toNat) =
          internE (.lam (decI (tblW m EID x)) (decI (tblW m EID y))) := by
        simp [exprOp, StateD.expr, hgx, hgy]
      obtain ⟨h1, h2, h3⟩ := mkLam_ok m a hA _ _ _ _ hI
      unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkLamW_above hI), mkLamW_mode hI hmode⟩
    · simp only [show (12 : Word) ≠ 10 by decide, show (12 : Word) ≠ 11 by decide,
        ↓reduceIte] at hI hr; subst hr
      have hop : exprOp st (.forallE x.toNat y.toNat) =
          internE (.forallE (decI (tblW m EID x)) (decI (tblW m EID y))) := by
        simp [exprOp, StateD.expr, hgx, hgy]
      obtain ⟨h1, h2, h3⟩ := mkForall_ok m a hA _ _ _ _ hI
      unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkForallW_above hI), mkForallW_mode hI hmode⟩
  · cases hI

theorem node_let (x y z : Word) (p q t : Nat) (hx : ItemR x p) (hy : ItemR y q) (hz : ItemR z t)
    (hI : nodeW b.data m 13 x y z = some (w, m₁)) : NodeOK st (.letE p q t) a m₁ w := by
  simp only [nodeW, show (13 : Word) ≠ 8 by decide, show (13 : Word) ≠ 9 by decide,
    show (13 : Word) ≠ 10 by decide, show (13 : Word) ≠ 11 by decide,
    show (13 : Word) ≠ 12 by decide, or_false, ↓reduceIte, letW] at hI
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
    unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkLetW_above hI), mkLetW_mode hI hmode⟩
  · cases hI

theorem node_proj (x y z : Word) (p q t : Nat) (hx : ItemR x p) (hy : ItemR y q) (hz : ItemR z t)
    (hI : nodeW b.data m 14 x y z = some (w, m₁)) : NodeOK st (.proj p q t) a m₁ w := by
  simp only [nodeW, show (14 : Word) ≠ 8 by decide, show (14 : Word) ≠ 9 by decide,
    show (14 : Word) ≠ 10 by decide, show (14 : Word) ≠ 11 by decide,
    show (14 : Word) ≠ 12 by decide, show (14 : Word) ≠ 13 by decide, or_false,
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
    unfold NodeOK; rw [hop]; exact ⟨h1, h2, h3, hD.above (mkProjW_above hI), mkProjW_mode hI hmode⟩
  · cases hI

theorem node_lit (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (x y z : Word)
    (n : Nat) (hv : NatValR b y z n) (hI : nodeW b.data m 16 x y z = some (w, m₁)) :
    NodeOK st (.natVal n) a m₁ w := by
  simp only [nodeW, show (16 : Word) ≠ 8 by decide, show (16 : Word) ≠ 9 by decide,
    show (16 : Word) ≠ 10 by decide, show (16 : Word) ≠ 11 by decide,
    show (16 : Word) ≠ 12 by decide, show (16 : Word) ≠ 13 by decide,
    show (16 : Word) ≠ 14 by decide, show (16 : Word) ≠ 15 by decide, or_false,
    ↓reduceIte, litW] at hI
  obtain ⟨hcd, -, hdig, hn⟩ := natValR_decN b h64 hsize y z n hv
  cases hN : natDecW b.data m y z with
  | none => rw [hN, litK_none] at hI; cases hI
  | some q =>
  obtain ⟨r, m₂⟩ := q
  obtain ⟨l, rfl, hg, hsl, hnm, hpv⟩ :=
    natDecW_val b.data m m₂ y z r hA.1.lit.1 (UInt64.le_of_lt hcd) hdig hN
  rw [hN] at hI
  replace hI := litK_intern hI
  simp only [List.headD_cons, List.tail_cons] at hI
  have hA' := ArenaD.grow m m₂ hg a hA
  have hmo₂ := ModeOK.growsF hmode hg
  obtain ⟨h1, h2, h3, hf⟩ := internLit_D m₂ a hA' w m₁ m.top l hsl hnm (ModeOK.slice0 hmo₂ hsl) hI
  rw [hpv, ← hn] at h1 h2 h3
  exact ⟨h1, h2, h3, (hD.frame (grows_frame _ _ hg) (by tapart) (by tapart)).above
    (MemFrame.above hf (by simp [litSch, REC, SLOT])), MemFrame.modeOK hf (by decide) (by decide) hmo₂⟩

theorem node_lit_str (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (x y z : Word)
    (s : String) (hv : StrR b y z s) (hI : nodeW b.data m 17 x y z = some (w, m₁)) :
    NodeOK st (.strVal s) a m₁ w := by
  simp only [nodeW, show (17 : Word) ≠ 8 by decide, show (17 : Word) ≠ 9 by decide,
    show (17 : Word) ≠ 10 by decide, show (17 : Word) ≠ 11 by decide,
    show (17 : Word) ≠ 12 by decide, show (17 : Word) ≠ 13 by decide,
    show (17 : Word) ≠ 14 by decide, show (17 : Word) ≠ 15 by decide,
    show (17 : Word) ≠ 16 by decide, or_false,
    ↓reduceIte, litStrW] at hI
  split at hI
  · cases hI
  rename_i hc0
  cases hP : strPutEscW b.data m y z with
  | none => rw [hP, litStrK_none] at hI; cases hI
  | some q =>
  obtain ⟨l, m₂⟩ := q
  obtain ⟨hg, hsl, hk⟩ :=
    ConAgua.Front.UnescapeLink.strPutEsc_link h64 b hsize m m₂ hA.1.lit.1 y z s hv l hP
  rw [hP] at hI
  replace hI := litStrK_intern hI
  have hA' := ArenaD.grow m m₂ hg a hA
  have hmo₂ := ModeOK.growsF hmode hg
  obtain ⟨h1, h2, h3, hf⟩ := internLitStr_D m₂ a hA' w m₁ m.top l hsl s hk (ModeOK.slice0 hmo₂ hsl) hI
  exact ⟨h1, h2, h3, (hD.frame (grows_frame _ _ hg) (by tapart) (by tapart)).above
    (MemFrame.above hf (by simp [litSch, REC, SLOT])), MemFrame.modeOK hf (by decide) (by decide) hmo₂⟩

omit hA hD hmode in
/-- A universe list whose items are bound level ids: `mapM st.level` is pure. -/
theorem mapM_level (hL : TblR m LID st.levels) :
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

omit hA hD hmode in
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
    show (15 : Word) ≠ 14 by decide, or_false, ↓reduceIte, constW] at hI
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
  have hpok := hA.1.lit.1
  have hsm := hpok.small
  have h41 := hpok.top41
  have hsz := hsm.tier (m.top >>> 40)
  have hsp := tag_split m.top
  unfold lsPutW at hP
  split at hP
  · cases hP
  rename_i hle
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have ht' : (m.top &&& 1099511627775).toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    have := UInt64.not_lt.mp hle; rw [UInt64.le_iff_toNat_le, hlen] at this; exact this
  obtain ⟨F1, -, F4, F5, F6, F7, F8⟩ := lsLoopM_facts b.data m.top h41 m (c + 1) 0 m₂ hP
    (by simpa using ht') hsz
  obtain ⟨F2, F9⟩ := F8 hpok.2.1
  simp only [UInt64.toNat_zero, Nat.zero_add, Nat.add_zero] at F1 F4 F5 F6
  have htc : (m.top + lsCntN b.data (c + 1) 0).toNat = m.top.toNat + (lsCntN b.data (c + 1) 0).toNat := by
    rw [UInt64.toNat_add]; omega
  have hg : Grows m m₂ := Grows.intro m m₂ hpok F9 (fun j hj => F5 j hj) (by rw [F2, htc]; omega)
    (by rw [F2, htc]; omega)
  have hab : Above64 m m₂ := MemFrame.above (grows_frame _ _ hg) (by simp [POOL, POOL1])
  have hA₂ := ArenaD.grow m m₂ hg a hA
  -- the twin's universe list
  have hxs : itemsN b.data (c + 1) = listN b.data c := rfl
  rw [hxs] at F1 F6 F7
  have hmap := mapM_level m st hD.levels _ us hus F7
  have hwl : ∀ y ∈ listN b.data c, (tblW m LID y).toNat < 2 ^ 32 :=
    fun y hy => (tbl_read hD.levels y (F7 y hy)).2.1
  have hk : sliceL (vpool m₂) m.top.toNat (lsPutL b.data c).toNat =
      lsWords ((listN b.data c).map fun y => (decI (tblW m LID y) : LIdx)) := by
    rw [lsWords_map m _ hwl, sliceL, List.ext_getElem_iff]
    simp only [lsPutL, F1, List.length_ofFn, List.length_map, true_and]
    intro k hk₁ hk₂
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [F6 k (by simpa using hk₂)]; rfl
  have hq : SliceOK m₂ m.top (lsPutL b.data c) := SliceOK.fresh hg F2
  have hmo₂ := ModeOK.growsF hmode hg
  obtain ⟨l1, l2, l3, lf⟩ := internLs_D m₂ a hA₂ g m₃ m.top _ hq _ hk (ModeOK.slice0 hmo₂ hq) hL
  obtain ⟨c1, c2, c3, cf⟩ := internConst_D m₃ _ l2 w m₁ (tblW m NID x) g hwn hg32' hI
  have hop : exprOp st (.const x.toNat us) =
      (internLsNode ((listN b.data c).map fun y => (decI (tblW m LID y) : LIdx)) >>= fun lsh =>
        internE (.const (decI (tblW m NID x)) lsh)) := by
    simp [exprOp, StateD.name, hgn, hmap]
  have hok' : AM.ok (exprOp st (.const x.toNat us)) a := by
    rw [hop, AM.ok_bind, l3]; exact ⟨l1, c1⟩
  refine ⟨hok', ?_, ?_, ?_, MemFrame.modeOK cf (by decide) (by decide)
    (MemFrame.modeOK lf (by decide) (by decide) hmo₂)⟩
  · rw [hop] at hok' ⊢; rw [AM.st_bind _ _ _ hok', l3]; exact c2
  · rw [hop, AM.res_bind _ _ _ l1, l3]; exact c3
  · exact ((hD.above hab).above (MemFrame.above lf (by simp [lsSch, LSREC, LSSLOT, LSHP]))).above
      (MemFrame.above cf (by simp [constSch, CREC, CSLOT, CLP]))

/-- **Every expression kind**: the node the fields `f` describe is interned. -/
theorem node_ok (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63) (f : Fld)
    (r : ExprRec) (hE : ExprR b r f)
    (hI : nodeW b.data m f.pl f.a f.c f.d = some (w, m₁)) : NodeOK st r a m₁ w := by
  cases r with
  | bvar k => obtain ⟨hp, hx⟩ := hE; rw [hp] at hI; exact node_bvar b m m₁ a st hA hD hmode w k _ _ _ hx hI
  | sort u => obtain ⟨hp, hx⟩ := hE; rw [hp] at hI; exact node_sort b m m₁ a st hA hD hmode w u _ _ _ hx hI
  | app p q =>
    obtain ⟨hp, hx, hy⟩ := hE; rw [hp] at hI
    exact node_bin b m m₁ a st hA hD hmode w 10 (.inl rfl) _ _ _ p q hx hy _ rfl hI
  | lam p q =>
    obtain ⟨hp, hx, hy⟩ := hE; rw [hp] at hI
    exact node_bin b m m₁ a st hA hD hmode w 11 (.inr (.inl rfl)) _ _ _ p q hx hy _ rfl hI
  | forallE p q =>
    obtain ⟨hp, hx, hy⟩ := hE; rw [hp] at hI
    exact node_bin b m m₁ a st hA hD hmode w 12 (.inr (.inr rfl)) _ _ _ p q hx hy _ rfl hI
  | letE p q t =>
    obtain ⟨hp, hx, hy, hz⟩ := hE; rw [hp] at hI
    exact node_let b m m₁ a st hA hD hmode w _ _ _ p q t hx hy hz hI
  | proj p q t =>
    obtain ⟨hp, hx, hy, hz⟩ := hE; rw [hp] at hI
    exact node_proj b m m₁ a st hA hD hmode w _ _ _ p q t hx hy hz hI
  | const nm us =>
    obtain ⟨hp, hx, hus⟩ := hE; rw [hp] at hI
    exact node_const b m m₁ a st hA hD hmode w _ _ _ nm us hx hus hI
  | natVal n =>
    obtain ⟨hp, -, hv⟩ := hE; rw [hp] at hI
    exact node_lit b m m₁ a st hA hD hmode w h64 hsize _ _ _ n hv hI
  | strVal s =>
    obtain ⟨hp, hv⟩ := hE; rw [hp] at hI
    exact node_lit_str b m m₁ a st hA hD hmode w h64 hsize _ _ _ s hv hI

end node

/-- An unbound table entry: the id is not `NONE`. -/
theorem tbl_fresh_ne {m : Mem} {b : ArrId} (i : Word) (hf : tblFresh m b i = true) : i ≠ NONE :=
  tblFresh_ne_tomb i hf

/-- **`apply_expr`'s model refines `parseExprEntryD`**: on fields `f` that con-leche's scanner
relates to the expression record `r` (`ExprR`) and an index word read for `i`, a successful
`apply_expr` is a successful `parseExprEntryD st i r`, with `ArenaD` and `StateDR` after. -/
@[refines ConRon.Arena.Frontend.parseExprEntryD]
theorem applyExprW_refines (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (m m' : Mem) (a₀ : AState)
    (st : StateD) (hA : ArenaD m a₀) (hD : StateDR m st) (hmode : ModeOK m) (f : Fld) (i : Nat)
    (r : ExprRec) (hI : ItemR f.idx i) (hE : ExprR b r f)
    (h : applyExprW b.data m f.pl f.idx f.a f.c f.d = some m') :
    AM.ok (parseExprEntryD st i r) a₀ ∧ ArenaD m' (AM.st (parseExprEntryD st i r) a₀) ∧
      StateDR m' (AM.res (parseExprEntryD st i r) a₀) ∧ ModeOK m' := by
  unfold applyExprW at h
  have hfr : tblFresh m EID f.idx = true :=
    Classical.byContradiction fun hf => by simp [hf] at h
  simp only [hfr, ↓reduceIte] at h
  have hnone := hD.exprs.fresh _ _ _ _ hfr
  rw [itemR_eq hI (tbl_fresh_ne _ hfr)]
  obtain ⟨w, m₁, hN, hw, hp⟩ := putK_eq h
  obtain ⟨h1, h2, h3, h4, h5⟩ := node_ok b m m₁ a₀ st hA hD hmode w h64 hsize f r hE hN
  have hfresh : st.freshExpr f.idx.toNat = pure () := by
    simp [StateD.freshExpr, IdTable.bound_eq, hnone]
  rw [parseExprEntryD_eq, hfresh, pure_bind]
  obtain ⟨hok₂, hst₂, hres₂⟩ := AM.bind_pure _
    (fun e => { st with exprs := st.exprs.insert f.idx.toNat e }) a₀ h1
  refine ⟨hok₂, by rw [hst₂]; exact ArenaD.putT _ _ _ h2 EID (.inr (.inr rfl)) _ _ hp, ?_⟩
  rw [hres₂, h3]
  exact ⟨h4.putExpr (MemFrame.refl [] [] m₁) (by simp) (by simp) (by simp) f.idx w hp hw _
    (fun j => IdTable.get?_insert _ _ _ _) rfl rfl,
    MemFrame.modeOK (tblPutW_frame (.inr (.inr rfl)) hp) (h := h5)⟩

end L.Front
