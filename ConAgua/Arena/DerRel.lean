import ConAgua.Arena.DerRelBase
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `DerR` across the interning and the `mk_*` constructors

The relation and the derived-word reads are in `DerRelBase.lean` (split off by helper
`whnf4-d23`; names unchanged).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The twin's interning, by cases -/

section proto
variable {α : Type} [BEq α] [Hashable α]

/-- The run of `protoRun`: a hit (state unchanged), or an append to the tier the store is in,
returning the handle of the new node. -/
theorem protoRun_cases (L : Lens α UInt64 .expr) (key : α) (tag : UInt32) (pf : Option EIdx)
    (d : UInt64) (err : CheckError) (a a' : AState) (y : EIdx)
    (h : protoRun L key tag pf d err a = .ok (y, a')) :
    a' = a ∨
    (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
      y = decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
      a' = L.setP a ((L.getP a).push key d y)) ∨
    (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
      y = decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
      a' = L.setS a ((L.getS a).push key d y)) := by
  unfold protoRun at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
  · split at h
    · rename_i hon
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact .inl h.2.symm
      · split at h
        · rename_i hc
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine .inr (.inr ⟨hon, by simpa [Tbl.size, Idx.idxCap] using hc, ?_, ?_⟩) <;>
            simp only [show Idx.tierS = UInt32.ofNat 1 from rfl, mk_eq, Tbl.size] <;> rfl
        · simp at h
    · rename_i hon
      split at h
      · rename_i hc
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine .inr (.inl ⟨by simpa using hon, by simpa [Tbl.size, Idx.idxCap] using hc, ?_, ?_⟩) <;>
          simp only [show Idx.tierP = UInt32.ofNat 0 from rfl, mk_eq, Tbl.size] <;> rfl
      · simp at h

end proto

/-! ## Handle words of a new node -/

theorem idxW_tierW_of_decE (r w : Word) (h : decE r = decE w) :
    idxW r = idxW w ∧ tierW r = tierW w := by
  have e : r.toUInt32 = w.toUInt32 := by
    simp only [decE] at h; exact Idx.ofWord.inj h
  have e' : r.toNat % 2 ^ 32 = w.toNat % 2 ^ 32 := by
    have := congrArg UInt32.toNat e; simpa [UInt64.toNat_toUInt32] using this
  constructor
  · apply UInt64.toNat_inj.mp
    simp only [idxW, UInt64.toNat_and]
    have : (134217727 : Word).toNat = 2 ^ 27 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]; omega
  · apply UInt64.toNat_inj.mp
    simp only [tierW, bit27_toNat]; omega

/-- The handle words of the node an append made: its index and tier. -/
theorem new_handle (r : Word) (g : UInt32) (t : Word) (n : Nat) (hg : g.toNat < 16) (ht : t ≤ 1)
    (hn : n < 2 ^ 27) (h : decE r = decI (hdW g.toUInt64 t (UInt64.ofNat n))) :
    idxW r = UInt64.ofNat n ∧ tierW r = t := by
  obtain ⟨h1, h2⟩ := idxW_tierW_of_decE r _ h
  obtain ⟨h3, h4⟩ := idxW_hdW g.toUInt64 t (UInt64.ofNat n) (by simpa using hg) ht
    (by simp; omega)
  exact ⟨h1.trans h3, h2.trans h4⟩

/-! ## One tier's derived words across a change -/

section derT
variable {α : Type} [BEq α] [Hashable α]

theorem lt_of_getElem? {β : Type} {xs : Array β} {i : Nat} {x : β} (h : xs[i]? = some x) :
    i < xs.size := by
  rcases Nat.lt_or_ge i xs.size with hl | hl
  · exact hl
  · rw [Array.getElem?_eq_none hl] at h; cases h

theorem derT_mono {tb : Tbl α EIdx UInt64} {P P' : Nat → α → UInt64 → Prop} (hD : DerT tb P)
    (h : ∀ i x d, i < tb.nodes.size → P i x d → P' i x d) : DerT tb P' :=
  ⟨hD.1, fun i x hx => h i x _ (lt_of_getElem? hx) (hD.2 i x hx)⟩

/-- An append keeps `DerT` if the new node's derived word satisfies `P`. -/
theorem derT_push {tb : Tbl α EIdx UInt64} {P : Nat → α → UInt64 → Prop} (hD : DerT tb P)
    (key : α) (d : UInt64) (y : EIdx) (hP : P tb.nodes.size key d) :
    DerT (tb.push key d y) P := by
  obtain ⟨hs, hn⟩ := hD
  have hp : (tb.push key d y).nodes = tb.nodes.push key ∧ (tb.push key d y).der = tb.der.push d := by
    cases tb; exact ⟨rfl, rfl⟩
  refine ⟨by rw [hp.1, hp.2]; simp [hs], fun i x hx => ?_⟩
  have hda : (tb.push key d y).derAt i = (tb.der.push d).getD i 0 := by
    simp only [Tbl.derAt, hp.2]; rfl
  rw [hp.1] at hx
  rw [hda]
  by_cases hi : i < tb.nodes.size
  · have hi' : i < tb.der.size := by rw [hs]; exact hi
    have := hn i x (by
      rw [Array.getElem?_eq_getElem hi]; rw [Array.getElem?_push_lt hi] at hx; exact hx)
    have e1 : (tb.der.push d).getD i 0 = tb.der[i] := by
      simp [Array.getD, Array.getElem_push_lt hi'] <;> intro h <;> omega
    have e2 : tb.derAt i = tb.der[i] := by simp [Tbl.derAt, Array.getD, hi']
    rw [e1]; rw [e2] at this; exact this
  · have hi' : i = tb.nodes.size := by
      have := lt_of_getElem? hx; simp at this; omega
    subst hi'
    rw [Array.getElem?_push_size] at hx
    obtain rfl := Option.some.inj hx
    have e1 : (tb.der.push d).getD tb.nodes.size 0 = d := by simp [Array.getD, ← hs]
    rw [e1]; exact hP

/-- `cP` across a memory change that keeps the entries' words. -/
theorem derT_cP {tb : Tbl α EIdx UInt64} {A : ArrId} {m m' : Mem} {t : Word}
    (hD : DerT tb (cP A m t))
    (h : ∀ i, i < tb.nodes.size → rdW (m'.arr64 (tierA A t)) (UInt64.ofNat i) =
      rdW (m.arr64 (tierA A t)) (UInt64.ofNat i)) : DerT tb (cP A m' t) :=
  derT_mono hD fun i _ _ hi hP => by simp only [cP] at hP ⊢; rw [h i hi]; exact hP

end derT

/-! ## The frame of `DerR` -/

/-- **`DerR` survives a writer of other arrays** (the five range columns in both tiers). -/
theorem DerR.frame (m m' : Mem) (a : AState) (hD : DerR m a)
    (h : ∀ B, B = ADER ∨ B = LADER ∨ B = FADER ∨ B = LEDER ∨ B = PJDER →
      ∀ t, m'.arr64 (tierA B t) = m.arr64 (tierA B t)) :
    DerR m' a := by
  have f := fun (B : ArrId) (hB : B = ADER ∨ B = LADER ∨ B = FADER ∨ B = LEDER ∨ B = PJDER)
    {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64) (hd : DerT2 a g (cP B m)) =>
    (⟨derT_cP hd.1 (fun i _ => by rw [h B hB]), derT_cP hd.2 (fun i _ => by rw [h B hB])⟩ :
      DerT2 a g (cP B m'))
  exact ⟨hD.bvar, hD.fvar, hD.sort, hD.const, hD.lit, f _ (by simp) _ hD.app,
    f _ (by simp) _ hD.lam, f _ (by simp) _ hD.forallE, f _ (by simp) _ hD.letE,
    f _ (by simp) _ hD.proj⟩

theorem DerR.frameM (A : List ArrId) (C : List Word) (m m' : Mem) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, (b < 42 ∨ 46 < b) ∧ (b < 298 ∨ 302 < b)) (a : AState) (hD : DerR m a) :
    DerR m' a :=
  DerR.frame m m' a hD fun B hB t => by
    rcases tierA_cases' B t with e | e <;> rw [e] <;>
      refine hf.1 _ (fun h => by
        have := hA _ h; rcases hB with rfl | rfl | rfl | rfl | rfl <;> revert this <;> decide) (by
        rcases hB with rfl | rfl | rfl | rfl | rfl <;> decide)

/-! ## The range field of a new node's derived word -/

theorem maxW_eq (x y : Word) : maxW x y = max x y := by
  apply UInt64.toNat_inj.mp; rw [maxW_toNat, toNat_max]

theorem satPredW_eq (x : Word) : satPredW x = satPred x := by
  simp only [satPredW, satPred]
  by_cases h1 : x = 32767
  · subst h1; decide
  by_cases h0 : x = 0
  · subst h0; decide
  have : 0 < x := by
    have : x.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
    exact UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
  simp [h1, h0, this]

theorem bvar_lt (x : UInt64) : (bvarOfData x).toNat < 32768 := bvarOfData_lt x
theorem fvar_lt (x : UInt64) : (fvarOfData x).toNat < 32768 := fvarOfData_lt x

theorem bvar_derBVar (st : EStore) (i : Nat) :
    bvarOfData (st.derOfView (.bvar i)) = satSucc i := by
  simp only [EStore.derOfView, EStore.derOfBVar]
  exact bvarOfData_pack _ _ _ _ (satSucc_lt i) (by decide)

theorem bvar_derApp (st : EStore) (f x : EIdx) :
    bvarOfData (st.derOfView (.app f x)) =
      max (bvarOfData (st.derived f)) (bvarOfData (st.derived x)) := by
  simp only [EStore.derOfView, EStore.derOfApp]
  exact bvarOfData_pack _ _ _ _ (max_lt_32768 (bvar_lt _) (bvar_lt _))
    (max_lt_32768 (fvar_lt _) (fvar_lt _))

theorem bvar_derBind (st : EStore) (tag : UInt64) (ty b : EIdx) :
    bvarOfData (st.derOfBindAt tag ty b) =
      max (bvarOfData (st.derived ty)) (satPred (bvarOfData (st.derived b))) := by
  simp only [EStore.derOfBindAt, derOfBind]
  exact bvarOfData_pack _ _ _ _ (max_lt_32768 (bvar_lt _) (satPred_lt (bvar_lt _)))
    (max_lt_32768 (fvar_lt _) (fvar_lt _))

theorem bvar_derLet (st : EStore) (ty v b : EIdx) :
    bvarOfData (st.derOfView (.letE ty v b)) =
      max (max (bvarOfData (st.derived ty)) (bvarOfData (st.derived v)))
        (satPred (bvarOfData (st.derived b))) := by
  simp only [EStore.derOfView, EStore.derOfLetAt, derOfLet]
  exact bvarOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvar_lt _) (bvar_lt _)) (satPred_lt (bvar_lt _)))
    (max_lt_32768 (max_lt_32768 (fvar_lt _) (fvar_lt _)) (fvar_lt _))

theorem bvar_derProj (st : EStore) (n : NIdx) (i : Nat) (e : EIdx) :
    bvarOfData (st.derOfView (.proj n i e)) = bvarOfData (st.derived e) := by
  simp only [EStore.derOfView, EStore.derOfProj]
  exact bvarOfData_pack _ _ _ _ (bvar_lt _) (fvar_lt _)

/-- A leaf other than `bvar` (`fvar`, `sort`, `const`, `lit`): range `0` (`zP`). -/
theorem bvar_derFVar (st : EStore) (idx : Nat) (ty : EIdx) :
    bvarOfData (st.derOfView (.fvar idx ty)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfFVar]
  exact bvarOfData_pack _ _ _ _ (by decide) (satSucc_lt idx)

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

/-! ### The fvar range of each arm (lane `exprops3`): no `satPred` across binders. -/

theorem fvar_derBVar (st : EStore) (i : Nat) : fvarOfData (st.derOfView (.bvar i)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfBVar]
  exact fvarOfData_pack _ _ _ _ (satSucc_lt i) (by decide)

theorem fvar_derApp (st : EStore) (f x : EIdx) :
    fvarOfData (st.derOfView (.app f x)) =
      max (fvarOfData (st.derived f)) (fvarOfData (st.derived x)) := by
  simp only [EStore.derOfView, EStore.derOfApp]
  exact fvarOfData_pack _ _ _ _ (max_lt_32768 (bvar_lt _) (bvar_lt _))
    (max_lt_32768 (fvar_lt _) (fvar_lt _))

theorem fvar_derBind (st : EStore) (tag : UInt64) (ty b : EIdx) :
    fvarOfData (st.derOfBindAt tag ty b) =
      max (fvarOfData (st.derived ty)) (fvarOfData (st.derived b)) := by
  simp only [EStore.derOfBindAt, derOfBind]
  exact fvarOfData_pack _ _ _ _ (max_lt_32768 (bvar_lt _) (satPred_lt (bvar_lt _)))
    (max_lt_32768 (fvar_lt _) (fvar_lt _))

theorem fvar_derLet (st : EStore) (ty v b : EIdx) :
    fvarOfData (st.derOfView (.letE ty v b)) =
      max (max (fvarOfData (st.derived ty)) (fvarOfData (st.derived v)))
        (fvarOfData (st.derived b)) := by
  simp only [EStore.derOfView, EStore.derOfLetAt, derOfLet]
  exact fvarOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvar_lt _) (bvar_lt _)) (satPred_lt (bvar_lt _)))
    (max_lt_32768 (max_lt_32768 (fvar_lt _) (fvar_lt _)) (fvar_lt _))

theorem fvar_derProj (st : EStore) (n : NIdx) (i : Nat) (e : EIdx) :
    fvarOfData (st.derOfView (.proj n i e)) = fvarOfData (st.derived e) := by
  simp only [EStore.derOfView, EStore.derOfProj]
  exact fvarOfData_pack _ _ _ _ (bvar_lt _) (fvar_lt _)

theorem fvar_derFVar (st : EStore) (idx : Nat) (ty : EIdx) :
    fvarOfData (st.derOfView (.fvar idx ty)) = satSucc idx := by
  simp only [EStore.derOfView, EStore.derOfFVar]
  exact fvarOfData_pack _ _ _ _ (by decide) (satSucc_lt idx)

theorem fvar_derSort (st : EStore) (u : LIdx) : fvarOfData (st.derOfView (.sort u)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfSort]
  exact fvarOfData_pack _ _ _ _ (by decide) (by decide)

theorem fvar_derConst (st : EStore) (n : NIdx) (us : LsIdx) :
    fvarOfData (st.derOfView (.const n us)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfConst]
  exact fvarOfData_pack _ _ _ _ (by decide) (by decide)

theorem fvar_derLit (st : EStore) (l : ConLeche.Literal) :
    fvarOfData (st.derOfView (.lit l)) = 0 := by
  simp only [EStore.derOfView, EStore.derOfLit]
  exact fvarOfData_pack _ _ _ _ (by decide) (by decide)

/-- The guard of every `mk_*`: the handle words are below `2^32`. -/
theorem or_shr32 (f x : Word) (h : (f ||| x) >>> 32 = 0) : f.toNat < 2 ^ 32 ∧ x.toNat < 2 ^ 32 := by
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_or, Nat.shiftRight_eq_div_pow] at this
  simp at this
  exact ⟨Nat.lt_of_le_of_lt Nat.left_le_or this, Nat.lt_of_le_of_lt Nat.right_le_or this⟩

theorem or_lt32 (f x : Word) (h : (f ||| x).toNat < 2 ^ 32) : f.toNat < 2 ^ 32 ∧ x.toNat < 2 ^ 32 := by
  rw [UInt64.toNat_or] at h
  exact ⟨Nat.lt_of_le_of_lt Nat.left_le_or h, Nat.lt_of_le_of_lt Nat.right_le_or h⟩

/-! ## The tail of a `mk_*`, generically -/

section derMk
variable {α : Type} [BEq α] [Hashable α] (C : ConsSch) (hW : C.WF)
  (R : Mem → Word → Word → α → Prop)
  (L : Lens α UInt64 .expr) (g : ETables → Tbl α EIdx UInt64)
  (hgP : ∀ a, L.getP a = g a.store.pers) (hgS : ∀ a, L.getS a = g a.store.scr)
  (hPP : ∀ a t, g (L.setP a t).store.pers = t) (hPS : ∀ a t, g (L.setP a t).store.scr = g a.store.scr)
  (hSP : ∀ a t, g (L.setS a t).store.pers = g a.store.pers)
  (hSS : ∀ a t, g (L.setS a t).store.scr = t)

include hW hgP hgS hPP hPS hSP hSS in
/-- **The tail of a `mk_*`**: after the interning (`m` to `m₁`, the arena `a` to `a'`, result
`r`) and `derPutW`, the compound table's `DerT2` holds of `a'` and `m'`, if the range written is
the new node's (`dd = bvarOfData d`); `m'` differs from `m₁` only in `A`. -/
theorem derMk (A : ArrId) (m m₁ m' : Mem) (a a' : AState) (key : α) (d : UInt64)
    (y : EIdx) (r dd : Word)
    (hT : ConsR C R m a.store.scratchOn (g a.store.pers) (g a.store.scr))
    (hT₁ : ConsR C R m₁ a'.store.scratchOn (g a'.store.pers) (g a'.store.scr))
    (hd : DerT2 a g (cP A m)) (hfr : ∀ t, m₁.arr64 (tierA A t) = m.arr64 (tierA A t))
    (hst : a' = a ∨
      (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW C.tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
        a' = L.setP a ((L.getP a).push key d y)) ∨
      (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
        y = decI (hdW C.tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
        a' = L.setS a ((L.getS a).push key d y)))
    (hres : decE r = y) (hdd : dd = packBFL (bvarOfData d) (fvarOfData d) (lpW d))
    (hput : derPutW A C.ca m₁ (cnt2 m C.ca) r dd = some m') :
    DerT2 a' g (cP A m') := by
  have hfrA : ∀ i t, rdW (m₁.arr64 (tierA A t)) (UInt64.ofNat i) =
      rdW (m.arr64 (tierA A t)) (UInt64.ofNat i) :=
    fun i t => by rw [hfr]

  have c0 := ConsR.cnt hT 0 (by decide)
  have c1 := ConsR.cnt hT 1 (by decide)
  have d0 := ConsR.cnt hT₁ 0 (by decide)
  have d1 := ConsR.cnt hT₁ 1 (by decide)
  have b0 := ConsR.cap hT 0 (by decide)
  have b1 := ConsR.cap hT 1 (by decide)
  simp only [ite_true, show (1 : Word) ≠ 0 by decide, ite_false] at c0 c1 d0 d1 b0 b1
  have htag : C.tag.toNat < 16 := by have := hW.sch.tag; simpa [ConsSch.sch] using this
  rcases hst with rfl | ⟨hoff, hsz, hy, rfl⟩ | ⟨hon', hsz, hy, rfl⟩
  · -- a hit: the counts did not move, nothing is written
    have e : cnt2 m₁ C.ca = cnt2 m C.ca := by
      rw [cnt2_eq, cnt2_eq, UInt64.toNat_inj.mp (c0.trans d0.symm),
        UInt64.toNat_inj.mp (c1.trans d1.symm)]
    simp only [derPutW, e, ite_true, Option.some.injEq] at hput
    subst hput
    exact ⟨derT_cP hd.1 (fun i _ => hfrA i 0), derT_cP hd.2 (fun i _ => hfrA i 1)⟩
  · -- an append to the persistent tier
    simp only [hPP, hPS, hgP] at d0 d1
    rw [hgP] at hsz hy
    have hpsz : ((g a.store.pers).push key d y).nodes.size = (g a.store.pers).nodes.size + 1 := by
      cases g a.store.pers; simp [Tbl.push]
    have ne : cnt2 m₁ C.ca ≠ cnt2 m C.ca := by
      intro e
      rw [cnt2_eq, cnt2_eq] at e
      have e' := congrArg UInt64.toNat e
      rw [UInt64.toNat_add, UInt64.toNat_add, d0, d1] at e'
      simp only [hpsz] at e'
      have := (cntC C m 0).toNat_lt; have := (cntC C m 1).toNat_lt; omega
    obtain ⟨hi, ht⟩ := new_handle r C.tag 0 _ htag (by decide) hsz (hres.trans hy)
    simp only [derPutW, ne, ite_false, hi, ht] at hput
    split at hput
    · cases hput
    rename_i hlen
    simp only [Option.some.injEq] at hput
    subst hput
    have hq : (UInt64.ofNat (g a.store.pers).nodes.size).toNat < (m₁.arr64 (tierA A 0)).size := by
      have h1 := UInt64.not_le.mp hlen
      rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat'] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.mod_le _ _)
    have rd : ∀ i, i < 2 ^ 27 → i ≠ (g a.store.pers).nodes.size →
        rdW ((m₁.set64 (tierA A 0) (UInt64.ofNat (g a.store.pers).nodes.size) dd).arr64 (tierA A 0))
          (UInt64.ofNat i) = rdW (m.arr64 (tierA A 0)) (UInt64.ofNat i) := by
      intro i hi hne
      rw [rdW_set64, ite_eq_right (fun h => hne (by
        have := congrArg UInt64.toNat h.2.1
        simp only [UInt64.toNat_ofNat'] at this
        omega)), hfrA]
    have ro : (m₁.set64 (tierA A 0) (UInt64.ofNat (g a.store.pers).nodes.size) dd).arr64 (tierA A 1) =
        m.arr64 (tierA A 1) := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne_tier A (by decide) (by decide) (by decide)), hfr]
    refine ⟨?_, ?_⟩
    · rw [hPP, hgP]
      refine derT_push (derT_cP hd.1 (fun i hi => rd i (by omega) (by omega))) key d y ?_
      simp only [cP]
      rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hq⟩, hdd]
    · rw [hPS]
      exact derT_cP hd.2 (fun i hi => by rw [ro])
  · -- an append to the scratch tier
    simp only [hSP, hSS, hgS] at d0 d1
    rw [hgS] at hsz hy
    have hpsz : ((g a.store.scr).push key d y).nodes.size = (g a.store.scr).nodes.size + 1 := by
      cases g a.store.scr; simp [Tbl.push]
    have ne : cnt2 m₁ C.ca ≠ cnt2 m C.ca := by
      intro e
      rw [cnt2_eq, cnt2_eq] at e
      have e' := congrArg UInt64.toNat e
      rw [UInt64.toNat_add, UInt64.toNat_add, d0, d1] at e'
      simp only [hpsz] at e'
      have := (cntC C m 0).toNat_lt; have := (cntC C m 1).toNat_lt; omega
    obtain ⟨hi, ht⟩ := new_handle r C.tag 1 _ htag (by decide) hsz (hres.trans hy)
    simp only [derPutW, ne, ite_false, hi, ht] at hput
    split at hput
    · cases hput
    rename_i hlen
    simp only [Option.some.injEq] at hput
    subst hput
    have hq : (UInt64.ofNat (g a.store.scr).nodes.size).toNat < (m₁.arr64 (tierA A 1)).size := by
      have h1 := UInt64.not_le.mp hlen
      rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat'] at h1
      exact Nat.lt_of_lt_of_le h1 (Nat.mod_le _ _)
    have rd : ∀ i, i < 2 ^ 27 → i ≠ (g a.store.scr).nodes.size →
        rdW ((m₁.set64 (tierA A 1) (UInt64.ofNat (g a.store.scr).nodes.size) dd).arr64 (tierA A 1))
          (UInt64.ofNat i) = rdW (m.arr64 (tierA A 1)) (UInt64.ofNat i) := by
      intro i hi hne
      rw [rdW_set64, ite_eq_right (fun h => hne (by
        have := congrArg UInt64.toNat h.2.1
        simp only [UInt64.toNat_ofNat'] at this
        omega)), hfrA]
    have ro : (m₁.set64 (tierA A 1) (UInt64.ofNat (g a.store.scr).nodes.size) dd).arr64 (tierA A 0) =
        m.arr64 (tierA A 0) := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne_tier A (by decide) (by decide) (by decide)), hfr]
    refine ⟨?_, ?_⟩
    · rw [hSP]
      exact derT_cP hd.1 (fun i hi => by rw [ro])
    · rw [hSS, hgS]
      refine derT_push (derT_cP hd.2 (fun i hi => rd i (by omega) (by omega))) key d y ?_
      simp only [cP]
      rw [rdW_set64, ite_eq_left ⟨rfl, rfl, hq⟩, hdd]

end derMk

/-! ## The `mk_*` constructors refine `internE` under `ArenaD` -/

/-- The twin's run of an interning, by cases (`protoRun_cases` through the run equation). -/
theorem AM.proto_cases {α : Type} [BEq α] [Hashable α] (L : Lens α UInt64 .expr) (op : AM EIdx)
    (key : α) (tag : UInt32) (pf : Option EIdx) (d : UInt64) (err : CheckError) (a : AState)
    (hrun : op.run a = protoRun L key tag pf d err a) (hok : AM.ok op a) :
    AM.st op a = a ∨
    (L.on a = false ∧ (L.getP a).nodes.size < 2 ^ 27 ∧
      AM.res op a = decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)) ∧
      AM.st op a = L.setP a ((L.getP a).push key d (AM.res op a))) ∨
    (L.on a = true ∧ (L.getS a).nodes.size < 2 ^ 27 ∧
      AM.res op a = decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)) ∧
      AM.st op a = L.setS a ((L.getS a).push key d (AM.res op a))) :=
  protoRun_cases L key tag pf d err a _ _ (hrun.symm.trans (AM.run_of_ok op a hok))

theorem cP_other {α : Type} [BEq α] [Hashable α] {a : AState} {g : ETables → Tbl α EIdx UInt64}
    {B : ArrId} {m m' : Mem} (hd : DerT2 a g (cP B m)) (h : m'.arr64 B = m.arr64 B)
    (h' : m'.arr64 (tier1 B) = m.arr64 (tier1 B)) : DerT2 a g (cP B m') :=
  ⟨derT_cP hd.1 (fun i _ => by simp only [tierA_zero, h]),
    derT_cP hd.2 (fun i _ => by simp only [tierA_one, h'])⟩

/-- **`mk_app` refines `internE (.app _ _)` under `ArenaD`.** -/
theorem mkApp_ok (m : Mem) (a : AState) (hA : ArenaD m a) (f x r : Word) (m' : Mem)
    (hI : mkAppW m f x = some (r, m')) :
    AM.ok (internE (.app (decE f) (decE x))) a ∧
    ArenaD m' (AM.st (internE (.app (decE f) (decE x))) a) ∧
    AM.res (internE (.app (decE f) (decE x))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkAppW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨hf, hx⟩ := or_shr32 f x (by simpa using hg)
  rcases hI₁ : ainternW m f x with _ | ⟨r₁, m₁⟩ <;> simp only [hI₁, mkK, reduceCtorEq] at hI
  rcases hP : derPutW ADER 4 m₁ (cnt2 m 4) r₁
      (packBFL (maxW (derBW m f) (derBW m x)) (maxW (derFW m f) (derFW m x))
        (exprLPW m f ||| exprLPW m x)) with _ | m₂ <;>
    simp only [hP, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := aintern_correct m a hR.app f x hf hx _ _ hI₁
  have hfr := consInternM_frame appCS_wf hI₁
  have hcs := AM.proto_cases appLens _ _ _ _ _ _ a (internE_app_run _ _ a) hok
  have hR₁ := hR.lift_app _ _ _ _ hX hfr (AM.st_proto appLens _ _ _ _ _ _ a (internE_app_run _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [ConsSch.wset, appCS, AREC, ASLOT]) a hD
  have hfr₂ := derPutW_frame ADER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk appCS appCS_wf ARecRel appLens (·.apps) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ADER m m₁ m₂ a _ _ _ _ r₁ _
    hR.app hR₁.app hD.app (hfr.tier ADER (by simp [ConsSch.wset, appCS, ADER, AREC, ASLOT]) (by simp [ConsSch.wset, appCS, ADER, AREC, ASLOT]) (by decide)) hcs hres.symm
    (by rw [maxW_eq, maxW_eq, derBW_ok m a hR hD f hf, derBW_ok m a hR hD x hx,
      derFW_ok m a hR hD f hf, derFW_ok m a hR hD x hx, bvar_derApp, fvar_derApp,
      derLW_ok m a hR hD f hf, derLW_ok m a hR hD x hx]; simp only [lpW, lp_derApp, b2w_or]) hP
  have o := fun B (hB : B ≠ ADER) (hB' : B ≠ tier1 ADER) (hC : B ≠ CTL) =>
    hfr₂.1 B (by simp [hB, hB']) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [ADER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit, hnew,
    cP_other hD₁.lam (o LADER (by decide) (by decide) (by decide))
      (o (tier1 LADER) (by decide) (by decide) (by decide)), cP_other hD₁.forallE (o FADER (by decide) (by decide) (by decide))
      (o (tier1 FADER) (by decide) (by decide) (by decide)),
    cP_other hD₁.letE (o LEDER (by decide) (by decide) (by decide))
      (o (tier1 LEDER) (by decide) (by decide) (by decide)), cP_other hD₁.proj (o PJDER (by decide) (by decide) (by decide))
      (o (tier1 PJDER) (by decide) (by decide) (by decide))⟩

/-- **`mk_lam` refines `internE (.lam _ _)` under `ArenaD`.** -/
theorem mkLam_ok (m : Mem) (a : AState) (hA : ArenaD m a) (t b r : Word) (m' : Mem)
    (hI : mkLamW m t b = some (r, m')) :
    AM.ok (internE (.lam (decE t) (decE b))) a ∧
    ArenaD m' (AM.st (internE (.lam (decE t) (decE b))) a) ∧
    AM.res (internE (.lam (decE t) (decE b))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkLamW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨ht, hb⟩ := or_shr32 t b (by simpa using hg)
  rcases hI₁ : lainternW m t b with _ | ⟨r₁, m₁⟩ <;> simp only [hI₁, mkK, reduceCtorEq] at hI
  rcases hP : derPutW LADER 28 m₁ (cnt2 m 28) r₁
      (packBFL (maxW (derBW m t) (satPredW (derBW m b))) (maxW (derFW m t) (derFW m b))
        (exprLPW m t ||| exprLPW m b)) with _ | m₂ <;>
    simp only [hP, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := laintern_correct m a hR.lam t b ht hb _ _ hI₁
  have hfr := consInternM_frame lamCS_wf hI₁
  have hcs := AM.proto_cases lamLens _ _ _ _ _ _ a (internE_lam_run _ _ a) hok
  have hR₁ := hR.lift_lam _ _ _ _ hX hfr (AM.st_proto lamLens _ _ _ _ _ _ a (internE_lam_run _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [ConsSch.wset, lamCS, LAREC, LASLOT]) a hD
  have hfr₂ := derPutW_frame LADER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk lamCS lamCS_wf LaRecRel lamLens (·.lams) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) LADER m m₁ m₂ a _ _ _ _ r₁ _
    hR.lam hR₁.lam hD.lam (hfr.tier LADER (by simp [ConsSch.wset, lamCS, LADER, LAREC, LASLOT]) (by simp [ConsSch.wset, lamCS, LADER, LAREC, LASLOT]) (by decide)) hcs
    hres.symm (by rw [maxW_eq, maxW_eq, satPredW_eq, derBW_ok m a hR hD t ht, derBW_ok m a hR hD b hb,
      derFW_ok m a hR hD t ht, derFW_ok m a hR hD b hb, bvar_derBind, fvar_derBind, derLW_ok m a hR hD t ht, derLW_ok m a hR hD b hb] <;>
      simp only [lpW, lp_derBind, b2w_or]) hP
  have o := fun B (hB : B ≠ LADER) (hB' : B ≠ tier1 LADER) (hC : B ≠ CTL) =>
    hfr₂.1 B (by simp [hB, hB']) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [LADER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit,
    cP_other hD₁.app (o ADER (by decide) (by decide) (by decide))
      (o (tier1 ADER) (by decide) (by decide) (by decide)), hnew,
    cP_other hD₁.forallE (o FADER (by decide) (by decide) (by decide))
      (o (tier1 FADER) (by decide) (by decide) (by decide)),
    cP_other hD₁.letE (o LEDER (by decide) (by decide) (by decide))
      (o (tier1 LEDER) (by decide) (by decide) (by decide)),
    cP_other hD₁.proj (o PJDER (by decide) (by decide) (by decide))
      (o (tier1 PJDER) (by decide) (by decide) (by decide))⟩

/-- **`mk_forall` refines `internE (.lam _ _)` under `ArenaD`.** -/
theorem mkForall_ok (m : Mem) (a : AState) (hA : ArenaD m a) (t b r : Word) (m' : Mem)
    (hI : mkForallW m t b = some (r, m')) :
    AM.ok (internE (.forallE (decE t) (decE b))) a ∧
    ArenaD m' (AM.st (internE (.forallE (decE t) (decE b))) a) ∧
    AM.res (internE (.forallE (decE t) (decE b))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkForallW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨ht, hb⟩ := or_shr32 t b (by simpa using hg)
  rcases hI₁ : fainternW m t b with _ | ⟨r₁, m₁⟩ <;> simp only [hI₁, mkK, reduceCtorEq] at hI
  rcases hP : derPutW FADER 30 m₁ (cnt2 m 30) r₁
      (packBFL (maxW (derBW m t) (satPredW (derBW m b))) (maxW (derFW m t) (derFW m b))
        (exprLPW m t ||| exprLPW m b)) with _ | m₂ <;>
    simp only [hP, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := faintern_correct m a hR.forallE t b ht hb _ _ hI₁
  have hfr := consInternM_frame forallCS_wf hI₁
  have hcs := AM.proto_cases forallLens _ _ _ _ _ _ a (internE_forall_run _ _ a) hok
  have hR₁ := hR.lift_forallE _ _ _ _ hX hfr (AM.st_proto forallLens _ _ _ _ _ _ a (internE_forall_run _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [ConsSch.wset, forallCS, FAREC, FASLOT]) a hD
  have hfr₂ := derPutW_frame FADER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk forallCS forallCS_wf FaRecRel forallLens (·.foralls) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) FADER m m₁ m₂ a _ _ _ _ r₁ _
    hR.forallE hR₁.forallE hD.forallE (hfr.tier FADER (by simp [ConsSch.wset, forallCS, FADER, FAREC, FASLOT]) (by simp [ConsSch.wset, forallCS, FADER, FAREC, FASLOT]) (by decide)) hcs
    hres.symm (by rw [maxW_eq, maxW_eq, satPredW_eq, derBW_ok m a hR hD t ht, derBW_ok m a hR hD b hb,
      derFW_ok m a hR hD t ht, derFW_ok m a hR hD b hb, bvar_derBind, fvar_derBind, derLW_ok m a hR hD t ht, derLW_ok m a hR hD b hb] <;>
      simp only [lpW, lp_derBind, b2w_or]) hP
  have o := fun B (hB : B ≠ FADER) (hB' : B ≠ tier1 FADER) (hC : B ≠ CTL) =>
    hfr₂.1 B (by simp [hB, hB']) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [FADER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit,
    cP_other hD₁.app (o ADER (by decide) (by decide) (by decide))
      (o (tier1 ADER) (by decide) (by decide) (by decide)),
    cP_other hD₁.lam (o LADER (by decide) (by decide) (by decide))
      (o (tier1 LADER) (by decide) (by decide) (by decide)), hnew,
    cP_other hD₁.letE (o LEDER (by decide) (by decide) (by decide))
      (o (tier1 LEDER) (by decide) (by decide) (by decide)),
    cP_other hD₁.proj (o PJDER (by decide) (by decide) (by decide))
      (o (tier1 PJDER) (by decide) (by decide) (by decide))⟩

/-- **`mk_let` refines `internE (.letE _ _ _)` under `ArenaD`.** -/
theorem mkLet_ok (m : Mem) (a : AState) (hA : ArenaD m a) (t v b r : Word) (m' : Mem)
    (hI : mkLetW m t v b = some (r, m')) :
    AM.ok (internE (.letE (decE t) (decE v) (decE b))) a ∧
    ArenaD m' (AM.st (internE (.letE (decE t) (decE v) (decE b))) a) ∧
    AM.res (internE (.letE (decE t) (decE v) (decE b))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkLetW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨htv, hb⟩ := or_shr32 _ b (by simpa using hg)
  obtain ⟨ht, hv⟩ := or_lt32 t v htv
  rcases hI₁ : leinternW m t v b with _ | ⟨r₁, m₁⟩ <;> simp only [hI₁, mkK, reduceCtorEq] at hI
  rcases hP : derPutW LEDER 20 m₁ (cnt2 m 20) r₁
      (packBFL (maxW (maxW (derBW m t) (derBW m v)) (satPredW (derBW m b)))
        (maxW (maxW (derFW m t) (derFW m v)) (derFW m b))
        (exprLPW m t ||| exprLPW m v ||| exprLPW m b)) with _ | m₂ <;>
    simp only [hP, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := leintern_correct m a hR.letE t v b ht hv hb _ _ hI₁
  have hfr := consInternM_frame letCS_wf hI₁
  have hcs := AM.proto_cases letLens _ _ _ _ _ _ a (internE_let_run _ _ _ a) hok
  have hR₁ := hR.lift_letE _ _ _ _ hX hfr
    (AM.st_proto letLens _ _ _ _ _ _ a (internE_let_run _ _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [ConsSch.wset, letCS, LEREC, LESLOT]) a hD
  have hfr₂ := derPutW_frame LEDER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk letCS letCS_wf LeRecRel letLens (·.lets) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) LEDER m m₁ m₂ a _ _ _ _ r₁ _
    hR.letE hR₁.letE hD.letE (hfr.tier LEDER (by simp [ConsSch.wset, letCS, LEDER, LEREC, LESLOT]) (by simp [ConsSch.wset, letCS, LEDER, LEREC, LESLOT]) (by decide)) hcs
    hres.symm (by rw [maxW_eq, maxW_eq, maxW_eq, maxW_eq, satPredW_eq, derBW_ok m a hR hD t ht,
      derBW_ok m a hR hD v hv, derBW_ok m a hR hD b hb, derFW_ok m a hR hD t ht,
      derFW_ok m a hR hD v hv, derFW_ok m a hR hD b hb, bvar_derLet, fvar_derLet,
      derLW_ok m a hR hD t ht, derLW_ok m a hR hD v hv, derLW_ok m a hR hD b hb] <;>
      simp only [lpW, lp_derLet, b2w_or]) hP
  have o := fun B (hB : B ≠ LEDER) (hB' : B ≠ tier1 LEDER) (hC : B ≠ CTL) =>
    hfr₂.1 B (by simp [hB, hB']) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [LEDER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit,
    cP_other hD₁.app (o ADER (by decide) (by decide) (by decide))
      (o (tier1 ADER) (by decide) (by decide) (by decide)),
    cP_other hD₁.lam (o LADER (by decide) (by decide) (by decide))
      (o (tier1 LADER) (by decide) (by decide) (by decide)),
    cP_other hD₁.forallE (o FADER (by decide) (by decide) (by decide))
      (o (tier1 FADER) (by decide) (by decide) (by decide)), hnew,
    cP_other hD₁.proj (o PJDER (by decide) (by decide) (by decide))
      (o (tier1 PJDER) (by decide) (by decide) (by decide))⟩

/-- **`mk_proj` refines `internE (.proj _ _ _)` under `ArenaD`.** -/
theorem mkProj_ok (m : Mem) (a : AState) (hA : ArenaD m a) (n i e r : Word) (m' : Mem)
    (hI : mkProjW m n i e = some (r, m')) :
    AM.ok (internE (.proj (decI n) i.toNat (decE e))) a ∧
    ArenaD m' (AM.st (internE (.proj (decI n) i.toNat (decE e))) a) ∧
    AM.res (internE (.proj (decI n) i.toNat (decE e))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  unfold mkProjW at hI
  split at hI
  · cases hI
  rename_i hg
  obtain ⟨hn, he⟩ := or_shr32 n e (by simpa using hg)
  rcases hI₁ : pjinternW m n i e with _ | ⟨r₁, m₁⟩ <;> simp only [hI₁, mkK, reduceCtorEq] at hI
  rcases hP : derPutW PJDER 32 m₁ (cnt2 m 32) r₁ (packBFL (derBW m e) (derFW m e) (exprLPW m e)) with _ | m₂ <;> simp only [hP, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hok, hX, hres⟩ := pjintern_correct m a hR.proj n i e hn he _ _ hI₁
  have hfr := consInternM_frame projCS_wf hI₁
  have hcs := AM.proto_cases projLens _ _ _ _ _ _ a (internE_proj_run _ _ _ a) hok
  have hR₁ := hR.lift_proj _ _ _ _ hX hfr
    (AM.st_proto projLens _ _ _ _ _ _ a (internE_proj_run _ _ _ a) hok)
  have hD₁ : DerR m₁ a := DerR.frameM _ _ m m₁ hfr (by simp [ConsSch.wset, projCS, PJREC, PJSLOT]) a hD
  have hfr₂ := derPutW_frame PJDER (by decide) _ _ _ _ _ _ hP
  have hnew := derMk projCS projCS_wf PJRecRel projLens (·.projs) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) PJDER m m₁ m₂
    a _ _ _ _ r₁ _ hR.proj hR₁.proj hD.proj
    (hfr.tier PJDER (by simp [ConsSch.wset, projCS, PJDER, PJREC, PJSLOT]) (by simp [ConsSch.wset, projCS, PJDER, PJREC, PJSLOT]) (by decide)) hcs
    hres.symm (by rw [derBW_ok m a hR hD e he, derFW_ok m a hR hD e he, bvar_derProj,
      fvar_derProj, derLW_ok m a hR hD e he]; simp only [lpW, lp_derProj]) hP
  have o := fun B (hB : B ≠ PJDER) (hB' : B ≠ tier1 PJDER) (hC : B ≠ CTL) =>
    hfr₂.1 B (by simp [hB, hB']) hC
  refine ⟨hok, ⟨ArenaR.frame_above _ _ (by simp [PJDER]) (by simp) _ _ hfr₂ _ hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h] at hnew ⊢ <;>
  exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const, hD₁.lit,
    cP_other hD₁.app (o ADER (by decide) (by decide) (by decide))
      (o (tier1 ADER) (by decide) (by decide) (by decide)),
    cP_other hD₁.lam (o LADER (by decide) (by decide) (by decide))
      (o (tier1 LADER) (by decide) (by decide) (by decide)),
    cP_other hD₁.forallE (o FADER (by decide) (by decide) (by decide))
      (o (tier1 FADER) (by decide) (by decide) (by decide)),
    cP_other hD₁.letE (o LEDER (by decide) (by decide) (by decide))
      (o (tier1 LEDER) (by decide) (by decide) (by decide)), hnew⟩

/-- **`intern_bvar` refines `internE (.bvar _)` under `ArenaD`** (a leaf: its range is
`satSucc i`, not stored in L, so the plain `intern_bvar` keeps `DerR`). -/
theorem internBVar_D (m : Mem) (a : AState) (hA : ArenaD m a) (u r : Word) (m' : Mem)
    (hI : binternW m u = some (r, m')) :
    AM.ok (internE (.bvar u.toNat)) a ∧ ArenaD m' (AM.st (internE (.bvar u.toNat)) a) ∧
    AM.res (internE (.bvar u.toNat)) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := bintern_correct m a hR.bvar u _ _ hI
  have hfr := consInternM_frame bvarCS_wf hI
  have hcs := AM.proto_cases bvarLens _ _ _ _ _ _ a (internE_bvar_run _ a) hok
  have hR₁ := hR.lift_bvar _ _ _ _ hX hfr
    (AM.st_proto bvarLens _ _ _ _ _ _ a (internE_bvar_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [ConsSch.wset, bvarCS, BREC, BSLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨⟨derT_push hD₁.bvar.1 _ _ _ ⟨bvar_derBVar _ _, fvar_derBVar _ _, lp_derBVar _ _⟩, hD₁.bvar.2⟩, hD₁.fvar, hD₁.sort,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨⟨hD₁.bvar.1, derT_push hD₁.bvar.2 _ _ _ ⟨bvar_derBVar _ _, fvar_derBVar _ _, lp_derBVar _ _⟩⟩, hD₁.fvar, hD₁.sort,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩

/-- **`intern_fvar` refines `internE (.fvar _ _)` under `ArenaD`** (a leaf: range `0`). -/
theorem internFVar_D (m : Mem) (a : AState) (hA : ArenaD m a) (u ty r : Word)
    (hty : ty.toNat < 2 ^ 32) (m' : Mem) (hI : fvinternW m u ty = some (r, m')) :
    AM.ok (internE (.fvar u.toNat (decE ty))) a ∧
    ArenaD m' (AM.st (internE (.fvar u.toNat (decE ty))) a) ∧
    AM.res (internE (.fvar u.toNat (decE ty))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := fvintern_correct m a hR.fvar u ty hty _ _ hI
  have hfr := fvinternW_frame m u ty _ _ hI
  have hcs := AM.proto_cases fvarLens _ _ _ _ _ _ a (internE_fvar_run _ _ a) hok
  have hR₁ := hR.lift_fvar _ _ _ _
    ⟨hX, fvintern_lp m a hR.fvar u ty hty hR.fvarLp (derLW_ok m a hR hD ty hty) _ _ hI⟩ hfr
    (AM.st_proto fvarLens _ _ _ _ _ _ a (internE_fvar_run _ _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [FVREC, FVSLOT, FVLP]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, ⟨derT_push hD₁.fvar.1 _ _ _ ⟨bvar_derFVar _ _ _, fvar_derFVar _ _ _⟩, hD₁.fvar.2⟩, hD₁.sort,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, ⟨hD₁.fvar.1, derT_push hD₁.fvar.2 _ _ _ ⟨bvar_derFVar _ _ _, fvar_derFVar _ _ _⟩⟩, hD₁.sort,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩

/-- **`intern_sort` refines `internE (.sort _)` under `ArenaD`** (a leaf: range `0`). -/
theorem internSort_D (m : Mem) (a : AState) (hA : ArenaD m a) (u r : Word)
    (hu : u.toNat < 2 ^ 32) (m' : Mem) (hI : sointernW m u = some (r, m')) :
    AM.ok (internE (.sort (decI u))) a ∧ ArenaD m' (AM.st (internE (.sort (decI u))) a) ∧
    AM.res (internE (.sort (decI u))) a = decI r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := sointern_correct m a hR.sort u hu _ _ hI
  have hfr := sointernW_frame m u _ _ hI
  have hcs := AM.proto_cases sortLens _ _ _ _ _ _ a (internE_sort_run _ a) hok
  have hR₁ := hR.lift_sort _ _ _ _
    ⟨hX, sointern_lp m a hR.sort u hu hR.sortLp (lvlHPW_ok m a hR u hu) _ _ hI⟩ hfr
    (AM.st_proto sortLens _ _ _ _ _ _ a (internE_sort_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [SOREC, SOSLOT, SOLP]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, ⟨derT_push hD₁.sort.1 _ _ _ ⟨bvar_derSort _ _, fvar_derSort _ _⟩, hD₁.sort.2⟩,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, ⟨hD₁.sort.1, derT_push hD₁.sort.2 _ _ _ ⟨bvar_derSort _ _, fvar_derSort _ _⟩⟩,
      hD₁.const, hD₁.lit, hD₁.app, hD₁.lam, hD₁.forallE, hD₁.letE, hD₁.proj⟩

/-- **`intern_const` refines `internE (.const _ _)` under `ArenaD`** (a leaf: range `0`). -/
theorem internConst_D (m : Mem) (a : AState) (hA : ArenaD m a) (f x r : Word)
    (hf : f.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32) (m' : Mem)
    (hI : ceinternW m f x = some (r, m')) :
    AM.ok (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a ∧
    ArenaD m' (AM.st (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a) ∧
    AM.res (internE (.const (decI (k := .name) f) (decI (k := .levels) x))) a = decI r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := ceintern_correct m a hR.const f x hf hx _ _ hI
  have hfr := ceinternW_frame m f x _ _ hI
  have hcs := AM.proto_cases constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok
  have hR₁ := hR.lift_const _ _ _ _
    ⟨hX, ceintern_lp m a hR.const f x hf hx hR.constLp (lsHPW_ok m a hR x hx) _ _ hI⟩ hfr
    (AM.st_proto constLens _ _ _ _ _ _ a (internE_const_run _ _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [CREC, CSLOT, CLP]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort,
      ⟨derT_push hD₁.const.1 _ _ _ ⟨bvar_derConst _ _ _, fvar_derConst _ _ _⟩, hD₁.const.2⟩, hD₁.lit, hD₁.app, hD₁.lam,
      hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort,
      ⟨hD₁.const.1, derT_push hD₁.const.2 _ _ _ ⟨bvar_derConst _ _ _, fvar_derConst _ _ _⟩⟩, hD₁.lit, hD₁.app, hD₁.lam,
      hD₁.forallE, hD₁.letE, hD₁.proj⟩

/-- **`intern_lit` refines `internE (.lit (.natVal _))` under `ArenaD`** (a leaf: range `0`). -/
theorem internLit_D (m : Mem) (a : AState) (hA : ArenaD m a) (o l r : Word)
    (hq : SliceOK m o l) (hn : Norm (vpool m) o.toNat l.toNat) (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)
    (m' : Mem) (hI : internW m o l = some (r, m')) :
    AM.ok (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a ∧
    ArenaD m' (AM.st (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a) ∧
    AM.res (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := intern_correct m a hR.lit o l hq hn hq0 _ _ hI
  have hfr := consInternM_frame litCS_wf hI
  have hcs := AM.proto_cases litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok
  have hR₁ := hR.lift_lit _ _ _ _ hX hfr
    (AM.st_proto litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [ConsSch.wset, litCS, litCSk, REC, SLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨derT_push hD₁.lit.1 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩, hD₁.lit.2⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨hD₁.lit.1, derT_push hD₁.lit.2 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩⟩, hD₁.app, hD₁.lam, hD₁.forallE,
      hD₁.letE, hD₁.proj⟩

/-- `DerR` reads only the store: a state with the same store (other memos, caches) has it too. -/
theorem DerR.of_store (m : Mem) (a a' : AState) (hD : DerR m a) (hs : a'.store = a.store) :
    DerR m a' := by
  have e : ∀ {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64)
      (P : Word → Nat → α → UInt64 → Prop), DerT2 a g P → DerT2 a' g P := by
    intro α _ _ g P h; unfold DerT2 at *; rw [hs]; exact h
  exact ⟨e _ _ hD.bvar, e _ _ hD.fvar, e _ _ hD.sort, e _ _ hD.const, e _ _ hD.lit, e _ _ hD.app,
    e _ _ hD.lam, e _ _ hD.forallE, e _ _ hD.letE, e _ _ hD.proj⟩

/-! ## The initial state -/

theorem derT_empty {α : Type} [BEq α] [Hashable α] (P : Nat → α → UInt64 → Prop) :
    DerT (Tbl.empty : Tbl α EIdx UInt64) P :=
  ⟨rfl, fun i x h => by simp [Tbl.empty] at h⟩

/-- **`DerR` holds initially**, at any memory: every table is empty. -/
theorem derR_init (m : Mem) : DerR m (AState.init EStore.empty) := by
  have e := fun {α : Type} [BEq α] [Hashable α] (P : Word → Nat → α → UInt64 → Prop) =>
    (⟨derT_empty (P 0), derT_empty (P 1)⟩ : DerT (Tbl.empty : Tbl α EIdx UInt64) (P 0) ∧
      DerT (Tbl.empty : Tbl α EIdx UInt64) (P 1))
  exact ⟨e _, e _, e _, e _, e _, e _, e _, e _, e _, e _⟩

/-- **`ArenaD` holds initially.** -/
theorem arenaD_init (sizes : List Nat) (hlen : 64 ≤ sizes.length) (hctl : 64 ≤ sizes[1]?.getD 0)
    (hpool : sizes[0]?.getD 0 < 2 ^ 40) (hpool1 : sizes[256]?.getD 0 < 2 ^ 40)
    (hsz : ∀ b, b < 64 ∨ (256 ≤ b ∧ b < 320) →
      consMinWords ≤ sizes[b]?.getD 0 ∧ sizes[b]?.getD 0 < 2 ^ 61) :
    ArenaD (initMem sizes) (AState.init EStore.empty) :=
  ⟨arenaR_init sizes hlen hctl hpool hpool1 hsz, derR_init _⟩

/-! ## Appending to the pool keeps `ArenaD`, and `natAddLit_refinesD` -/

/-- **Appending to the pool keeps `DerR`**: the five derived-range arrays (`42`‥`46`) are
untouched by a pool append (only `POOL`, `0`, and `CTL[0]` move). -/
theorem DerR.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hD : DerR m a) : DerR m' a :=
  DerR.frameM [POOL, POOL1] [0] m m' (grows_frame m m' hg) (by decide) a hD

/-- **Appending to the pool keeps `ArenaD`.** -/
theorem ArenaD.grow (m m' : Mem) (hg : Grows m m') (a : AState) (hA : ArenaD m a) : ArenaD m' a :=
  ⟨ArenaR.grow m m' hg a hA.1, DerR.grow m m' hg a hA.2⟩

/-- `intern_lit` refines `internE (.lit (.natVal _))` under `ArenaD`. -/
theorem internLit_refinesD (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hA : ArenaD s₀.mem a₀)
    (hq : SliceOK s₀.mem o l) (hn : Norm (vpool s₀.mem) o.toNat l.toNat)
    (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      ArenaD s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0); ⊤⦄ := by
  have hps := hA.1.lit.1.2.2.1
  have htop := hA.1.lit.1.2.2.2.1
  have hq1 := hq.le
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega) (by omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  exact ⟨hloc, internLit_D s.mem a₀ hA o l _ hq hn hq0 _ hI⟩

end L.Arena
