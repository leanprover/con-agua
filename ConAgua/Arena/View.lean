module

public import ConAgua.Arena.ArenaRel

@[expose] public section

/-!
# The arena side of the expression view: what every walk's refinement shares

Factored out of `WalkRefine.lean` (lane `walk`) for the walks after it (`LiftRefine.lean`):

* **Handle words** (`decE_tag`, `decE_idx`, `decE_pers`): the tag is `⟦h⟧.tag`, the index
  `h & (2^27 - 1)`, persistence the tier bit, for `h < 2^32`; `decE_word`/`decI_word`: a handle's
  word decodes back to it.
* **The view, per tag** (`view_bvar`, `view_app`, …): under `ArenaR`, the L code's checks
  (`viewOK m h c`: the scratch tier open for a scratch handle, the index below the tier's count
  `CTL[c + t]`) and the tag, the arena's `view (decE h)` is the node the L record holds, its
  children decoded from the record's words (each below `2^32`). One lemma per tag, each one line
  of use in a walk's arm.
* **Running the view** (`view_run`), the arithmetic of branch-free arms (`maxW_toNat`, …), and
  `Except` plumbing (`except_ok_bind`).
-/

open ConRon.Arena

namespace L.Arena

/-! ## Handle words -/

/-! ## Nodes of a table -/

/-! ## The view -/

section view
variable (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)

include hR hh in
/-- Under the L code's scratch check, the arena's view of the handle reads the tier its bit
names. -/
theorem view_tier (hv : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) :
    a.store.view (decE h) = (if tierW h = 0 then a.store.pers else a.store.scr).get (decE h) := by
  have hfl := ConsR.flag hR.app
  unfold EStore.view
  rw [decE_pers h hh]
  by_cases ht : tierW h = 0
  · simp [ht]
  · have hon : a.store.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hv ⟨ht, h1⟩
    simp [ht, hon]

/-- A node of the tier the handle names, from a table relation and the count check at the index
`i` (the handle's narrow index `idxW h`, or `app`'s wide one `idxA h`). -/
theorem node_ofI {α : Type} [BEq α] [Hashable α] (C : ConsSch) (R : Mem → Word → Word → α → Prop)
    (tbl : ETables → Tbl α EIdx UInt64) (on : Bool)
    (hT : ConsR C R m on (tbl a.store.pers) (tbl a.store.scr)) (i : Word)
    (hc : i < cntC C m (tierW h)) :
    ∃ k, (tbl (if tierW h = 0 then a.store.pers else a.store.scr)).nodes[i.toNat]? = some k ∧
      R m (tierW h) i k := by
  obtain ⟨k, h1, h2⟩ := ConsR.node hT (tierW h) (tierW_le h) i hc
  refine ⟨k, ?_, h2⟩
  rw [apply_ite tbl]; exact h1

/-- A handle that passes a narrow store's count check is narrow (a wide word's narrow index is
`2^30` or more, the store's count at most `2^26`). -/
theorem narrow_of_cnt {α : Type} [BEq α] [Hashable α] {C : ConsSch} {R : Mem → Word → Word → α → Prop}
    {on : Bool} {P Q : Tbl α EIdx UInt64} (hT : ConsR C R m on P Q) (hcw : C.wide = false)
    (hc : idxW h < cntC C m (tierW h)) : h.toNat / 2 ^ 30 % 2 = 0 := by
  have e := ConsR.cnt hT (tierW h) (tierW_le h)
  have c := ConsR.cap hT (tierW h) (tierW_le h)
  have := UInt64.lt_iff_toNat_lt.mp hc
  simp only [hcw, capS, Bool.false_eq_true, ↓reduceIte] at c
  exact narrow_of_idxW_lt h (by omega)

/-- A node of the tier the handle names, from a table relation and the count check. -/
theorem node_of {α : Type} [BEq α] [Hashable α] (C : ConsSch) (R : Mem → Word → Word → α → Prop)
    (tbl : ETables → Tbl α EIdx UInt64) (on : Bool)
    (hT : ConsR C R m on (tbl a.store.pers) (tbl a.store.scr))
    (hc : idxW h < cntC C m (tierW h)) :
    ∃ k, (tbl (if tierW h = 0 then a.store.pers else a.store.scr)).nodes[(idxW h).toNat]? = some k ∧
      R m (tierW h) (idxW h) k := by
  obtain ⟨k, h1, h2⟩ := ConsR.node hT (tierW h) (tierW_le h) (idxW h) hc
  refine ⟨k, ?_, h2⟩
  rw [apply_ite tbl]; exact h1

end view

theorem get_bvar (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 0) :
    tb.get (decE h) = (tb.bvars.node? (idxW h).toNat).map fun r => .bvar r.i := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar]
theorem get_fvar (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 1) :
    tb.get (decE h) = (tb.fvars.node? (idxW h).toNat).map fun r => .fvar r.idx r.ty := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar, ETag.fvar]
theorem get_sort (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 2) :
    tb.get (decE h) = (tb.sorts.node? (idxW h).toNat).map fun r => .sort r.u := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar, ETag.fvar, ETag.sort]
theorem get_const (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 3) :
    tb.get (decE h) = (tb.consts.node? (idxW h).toNat).map fun r => .const r.n r.us := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar, ETag.fvar, ETag.sort, ETag.const]
/-- The `app` arm: the twin's `get` answers only for a wide word; a narrow word's wide index is
`2^30` or more (`idxA_narrow`), so the index bound `hn` (from the L count check) excludes it. -/
theorem get_app (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 4)
    (hn : (idxA h).toNat < 2 ^ 30) :
    tb.get (decE h) = (tb.apps.node? (idxA h).toNat).map fun r => .app r.f r.a := by
  have hw : h.toNat / 2 ^ 30 % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (h.toNat / 2 ^ 30) with e | e
    · exact absurd (idxA_narrow h e) (by omega)
    · exact e
  rw [decE_eq]
  simp [ETables.get, decI_tag h hh, hg, decI_isWide_true h hw, decI_idxA h hw, ETag.bvar,
    ETag.fvar, ETag.sort, ETag.const, ETag.app]
theorem get_lam (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 5) :
    tb.get (decE h) = (tb.lams.node? (idxW h).toNat).map fun r => .lam r.ty r.body := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam]
theorem get_forall (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 6) :
    tb.get (decE h) = (tb.foralls.node? (idxW h).toNat).map fun r => .forallE r.ty r.body := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE]
theorem get_proj (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 9) :
    tb.get (decE h) = (tb.projs.node? (idxW h).toNat).map fun r => .proj r.n r.i r.e := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
theorem get_let (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 7) :
    tb.get (decE h) = (tb.lets.node? (idxW h).toNat).map fun r => .letE r.ty r.val r.body := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE, ETag.letE]
theorem get_lit (tb : ETables) (h : Word) (hh : h.toNat < 2 ^ 32) (hg : tagW h = 8) :
    tb.get (decE h) = (tb.lits.node? (idxW h).toNat).map fun r => .lit r.l := by
  simp [ETables.get, decE_tag h hh, hg, decE_idx h (narrow_of_tagW h (by rw [hg]; decide)), ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
    ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit]

theorem view_run (h : EIdx) (a : AState) (v : ENodeView) (hv : a.store.view h = some v) :
    (view h).run a = .ok (v, a) := by
  simp [view, hv, StateT.run_bind, StateT.run_get]; rfl

/-! ## Arithmetic of the arms -/

theorem maxW_toNat (x y : Word) : (maxW x y).toNat = max x.toNat y.toNat := by
  simp only [maxW]
  by_cases h : x < y
  · have e : x + (y - x) = y := by rw [UInt64.add_comm, UInt64.sub_add_cancel]
    simp only [h, ↓reduceIte, UInt64.mul_one, e]
    have : x.toNat < y.toNat := h; omega
  · simp only [h, ↓reduceIte, UInt64.mul_zero, UInt64.add_zero]
    have : ¬ x.toNat < y.toNat := h; omega

theorem predW_toNat (z : Word) : (predW z).toNat = z.toNat - 1 := by
  simp only [predW]
  by_cases h : 0 < z
  · simp only [h, ↓reduceIte]
    have : 0 < z.toNat := h
    rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
  · simp only [h, ↓reduceIte, UInt64.sub_zero]
    have : ¬ 0 < z.toNat := h; omega

theorem decE_word (x : EIdx) : decE x.word.toUInt64 = x := by
  cases x; simp [decE]

theorem word_lt {k : IdxKind} (x : Idx k) : x.word.toUInt64.toNat < 2 ^ 32 := by
  simp; exact x.word.toNat_lt

theorem except_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

/-! ## The view, one lemma per tag -/

section viewTags
variable (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)

include hR hh

theorem view_bvar (hv : viewOK m h BVAR) (hg : tagW h = 0) :
    a.store.view (decE h) = some (.bvar (tfld m BVAR (tierW h) (idxW h) 0).toNat) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h bvarCS BRecRel (·.bvars) _ hR.bvar hv.2
  rw [view_tier m a hR h hh hv.1, get_bvar _ h hh hg, Tbl.node?, hk]
  simp only [BRecRel] at hkr; simp [hkr]

theorem view_fvar (hv : viewOK m h FVAR) (hg : tagW h = 1) :
    ∃ i ty, a.store.view (decE h) = some (.fvar i ty) := by
  obtain ⟨k, hk, -⟩ := node_of m a h fvarCS FVRecRel (·.fvars) _ hR.fvar hv.2
  exact ⟨_, _, by rw [view_tier m a hR h hh hv.1, get_fvar _ h hh hg, Tbl.node?, hk]; rfl⟩

/-- `view_fvar`, with the index and the child's handle word pinned to the record's two
words (`fvarRangeGo`'s `fvar` arm needs the index, unlike `bvarBoundGo`'s). -/
theorem view_fvar_idx (hv : viewOK m h FVAR) (hg : tagW h = 1) :
    a.store.view (decE h) = some (.fvar (tfld m FVAR (tierW h) (idxW h) 0).toNat
      (decE (tfld m FVAR (tierW h) (idxW h) 1))) ∧
    (tfld m FVAR (tierW h) (idxW h) 1).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hi, hty⟩ := node_of m a h fvarCS FVRecRel (·.fvars) _ hR.fvar hv.2
  rw [hty, decE_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_fvar _ h hh hg, Tbl.node?, hk, hi]; rfl, word_lt _⟩

theorem view_sort (hv : viewOK m h SORT) (hg : tagW h = 2) :
    ∃ u, a.store.view (decE h) = some (.sort u) := by
  obtain ⟨k, hk, -⟩ := node_of m a h sortCS SoRecRel (·.sorts) _ hR.sort hv.2
  exact ⟨_, by rw [view_tier m a hR h hh hv.1, get_sort _ h hh hg, Tbl.node?, hk]; rfl⟩

theorem view_const (hv : viewOK m h CONST) (hg : tagW h = 3) :
    ∃ n us, a.store.view (decE h) = some (.const n us) := by
  obtain ⟨k, hk, -⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  exact ⟨_, _, by rw [view_tier m a hR h hh hv.1, get_const _ h hh hg, Tbl.node?, hk]; rfl⟩

theorem view_lit (hv : viewOK m h LIT) (hg : tagW h = 8) :
    ∃ l, a.store.view (decE h) = some (.lit l) := by
  obtain ⟨k, hk, -⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
  exact ⟨_, by rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk]; rfl⟩

omit hh in
/-- An `app` index below its tier's count is below the cap `2^30` (so the handle is wide). -/
theorem app_idx_lt (hc : idxA h < tcnt m APP (tierW h)) : (idxA h).toNat < 2 ^ 30 := by
  have e := ConsR.cnt hR.app (tierW h) (tierW_le h)
  have c := ConsR.cap hR.app (tierW h) (tierW_le h)
  have := UInt64.lt_iff_toNat_lt.mp hc
  simp only [cntC, tcnt, appCS, capS, ↓reduceIte] at e c this ⊢
  omega

theorem view_app (hv : viewOKA m h) (hg : tagW h = 4) :
    a.store.view (decE h) = some (.app (decE (tfld m APP (tierW h) (idxA h) 0))
      (decE (tfld m APP (tierW h) (idxA h) 1))) ∧
    (tfld m APP (tierW h) (idxA h) 0).toNat < 2 ^ 32 ∧
    (tfld m APP (tierW h) (idxA h) 1).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hf, ha⟩ := node_ofI m a h appCS ARecRel (·.apps) _ hR.app (idxA h) hv.2
  rw [hf, ha, decE_word, decE_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_app _ h hh hg (app_idx_lt m a hR h hv.2), Tbl.node?, hk]; rfl,
    word_lt _, word_lt _⟩

theorem view_lam (hv : viewOK m h LAM) (hg : tagW h = 5) :
    a.store.view (decE h) = some (.lam (decE (tfld m LAM (tierW h) (idxW h) 0))
      (decE (tfld m LAM (tierW h) (idxW h) 1))) ∧
    (tfld m LAM (tierW h) (idxW h) 0).toNat < 2 ^ 32 ∧
    (tfld m LAM (tierW h) (idxW h) 1).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hf, ha⟩ := node_of m a h lamCS LaRecRel (·.lams) _ hR.lam hv.2
  rw [hf, ha, decE_word, decE_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_lam _ h hh hg, Tbl.node?, hk]; rfl, word_lt _,
    word_lt _⟩

theorem view_forall (hv : viewOK m h FORALL) (hg : tagW h = 6) :
    a.store.view (decE h) = some (.forallE (decE (tfld m FORALL (tierW h) (idxW h) 0))
      (decE (tfld m FORALL (tierW h) (idxW h) 1))) ∧
    (tfld m FORALL (tierW h) (idxW h) 0).toNat < 2 ^ 32 ∧
    (tfld m FORALL (tierW h) (idxW h) 1).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hf, ha⟩ := node_of m a h forallCS FaRecRel (·.foralls) _ hR.forallE hv.2
  rw [hf, ha, decE_word, decE_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_forall _ h hh hg, Tbl.node?, hk]; rfl, word_lt _,
    word_lt _⟩

theorem view_let (hv : viewOK m h LET) (hg : tagW h = 7) :
    a.store.view (decE h) = some (.letE (decE (tfld m LET (tierW h) (idxW h) 0))
      (decE (tfld m LET (tierW h) (idxW h) 1))
      (decE (tfld m LET (tierW h) (idxW h) 2))) ∧
    (tfld m LET (tierW h) (idxW h) 0).toNat < 2 ^ 32 ∧
    (tfld m LET (tierW h) (idxW h) 1).toNat < 2 ^ 32 ∧
    (tfld m LET (tierW h) (idxW h) 2).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hf, ha, hb⟩ := node_of m a h letCS LeRecRel (·.lets) _ hR.letE hv.2
  rw [hf, ha, hb, decE_word, decE_word, decE_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_let _ h hh hg, Tbl.node?, hk]; rfl, word_lt _,
    word_lt _, word_lt _⟩

theorem view_proj (hv : viewOK m h PROJ) (hg : tagW h = 9) :
    a.store.view (decE h) = some (.proj (decI (tfld m PROJ (tierW h) (idxW h) 0))
      (tfld m PROJ (tierW h) (idxW h) 1).toNat
      (decE (tfld m PROJ (tierW h) (idxW h) 2))) ∧
    (tfld m PROJ (tierW h) (idxW h) 0).toNat < 2 ^ 32 ∧
    (tfld m PROJ (tierW h) (idxW h) 2).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hn, hi, he⟩ := node_of m a h projCS PJRecRel (·.projs) _ hR.proj hv.2
  rw [hn, hi, he, decE_word, decI_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_proj _ h hh hg, Tbl.node?, hk]; rfl, word_lt _,
    word_lt _⟩

end viewTags

/-! ## The projections (`viewApp`, `viewBind`, …), one lemma each

The walks that test the tag before reading the store (`instantiate1Go`) read a node through the
store's projections; under `ArenaR` and the L checks they are the record's words, as `view`. -/

section projections
variable (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
include hR hh

/-- A projection at the tier the handle names. -/
theorem proj_tier {β : Type} (f : ETables → EIdx → Option β)
    (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) :
    (if (decE h).isPersistent then f a.store.pers (decE h)
      else if a.store.scratchOn then f a.store.scr (decE h) else none) =
      f (if tierW h = 0 then a.store.pers else a.store.scr) (decE h) := by
  have hfl := ConsR.flag hR.app
  rw [decE_pers h hh]
  by_cases ht : tierW h = 0
  · simp [ht]
  · have hon : a.store.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hs ⟨ht, h1⟩
    simp [ht, hon]

theorem viewBVar_ok (hv : viewOK m h BVAR) :
    a.store.viewBVar (decE h) = some (tfld m BVAR (tierW h) (idxW h) 0).toNat := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h bvarCS BRecRel (·.bvars) _ hR.bvar hv.2
  simp only [EStore.viewBVar, EStore.persGetBVar]
  rw [proj_tier m a hR h hh (fun t i => t.getBVar i) hv.1]
  simp only [ETables.getBVar, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.bvar rfl hv.2)]
  rw [hk]; simp only [BRecRel] at hkr; simp [hkr]

theorem viewApp_ok (hv : viewOKA m h) :
    a.store.viewApp (decE h) = some (decE (tfld m APP (tierW h) (idxA h) 0),
      decE (tfld m APP (tierW h) (idxA h) 1)) := by
  obtain ⟨k, hk, hf, ha⟩ := node_ofI m a h appCS ARecRel (·.apps) _ hR.app (idxA h) hv.2
  simp only [EStore.viewApp, EStore.persGetApp]
  rw [proj_tier m a hR h hh (fun t i => t.getApp i) hv.1]
  simp only [ETables.getApp, Tbl.node?]
  have hw : h.toNat / 2 ^ 30 % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (h.toNat / 2 ^ 30) with e | e
    · exact absurd (idxA_narrow h e) (by have := app_idx_lt m a hR h hv.2; omega)
    · exact e
  rw [decE_eq, decI_isWide_true h hw, decI_idxA h hw]
  rw [hk, hf, ha, decE_word, decE_word]; rfl

theorem viewBind_lam (hv : viewOK m h LAM) (hg : tagW h = 5) :
    a.store.viewBind (decE h) = some (decE (tfld m LAM (tierW h) (idxW h) 0),
      decE (tfld m LAM (tierW h) (idxW h) 1)) := by
  obtain ⟨k, hk, hf, ha⟩ := node_of m a h lamCS LaRecRel (·.lams) _ hR.lam hv.2
  simp only [EStore.viewBind, EStore.persGetBind]
  rw [proj_tier m a hR h hh (fun t i => t.getBind i) hv.1]
  simp only [ETables.getBind, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.lam rfl hv.2), decE_tag h hh, hg, ETag.lam]
  simp only [show ((5 : Word).toUInt32 == 5) = true from rfl, ↓reduceIte]
  rw [hk, hf, ha, decE_word, decE_word]; rfl

theorem viewBind_forall (hv : viewOK m h FORALL) (hg : tagW h = 6) :
    a.store.viewBind (decE h) = some (decE (tfld m FORALL (tierW h) (idxW h) 0),
      decE (tfld m FORALL (tierW h) (idxW h) 1)) := by
  obtain ⟨k, hk, hf, ha⟩ := node_of m a h forallCS FaRecRel (·.foralls) _ hR.forallE hv.2
  simp only [EStore.viewBind, EStore.persGetBind]
  rw [proj_tier m a hR h hh (fun t i => t.getBind i) hv.1]
  simp only [ETables.getBind, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.forallE rfl hv.2), decE_tag h hh, hg, ETag.lam, ETag.forallE]
  simp only [show ((6 : Word).toUInt32 == 5) = false from rfl,
    show ((6 : Word).toUInt32 == 6) = true from rfl, ↓reduceIte, Bool.false_eq_true]
  rw [hk, hf, ha, decE_word, decE_word]; rfl

theorem viewLet_ok (hv : viewOK m h LET) :
    a.store.viewLet (decE h) = some (decE (tfld m LET (tierW h) (idxW h) 0),
      decE (tfld m LET (tierW h) (idxW h) 1),
      decE (tfld m LET (tierW h) (idxW h) 2)) := by
  obtain ⟨k, hk, hf, ha, hb⟩ := node_of m a h letCS LeRecRel (·.lets) _ hR.letE hv.2
  simp only [EStore.viewLet, EStore.persGetLet]
  rw [proj_tier m a hR h hh (fun t i => t.getLet i) hv.1]
  simp only [ETables.getLet, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.letE rfl hv.2)]
  rw [hk, hf, ha, hb, decE_word, decE_word, decE_word]; rfl

theorem viewProj_ok (hv : viewOK m h PROJ) :
    a.store.viewProj (decE h) = some (decI (tfld m PROJ (tierW h) (idxW h) 0),
      (tfld m PROJ (tierW h) (idxW h) 1).toNat,
      decE (tfld m PROJ (tierW h) (idxW h) 2)) := by
  obtain ⟨k, hk, hn, hi, he⟩ := node_of m a h projCS PJRecRel (·.projs) _ hR.proj hv.2
  simp only [EStore.viewProj, EStore.persGetProj]
  rw [proj_tier m a hR h hh (fun t i => t.getProj i) hv.1]
  simp only [ETables.getProj, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.proj rfl hv.2)]
  rw [hk, hn, hi, he, decE_word, decI_word]; rfl

end projections

end L.Arena
