import ConAgua.Arena.IndInstallSpec23
import ConAgua.Arena.IndPos2SpecV

/-!
# Refinements of `IndInstall`, part 32 (lane `indproofs3`, helper `pos`): `checkBlockPositivity`'s
pieces

* `check_block_positivity_nfs(_member)`: the normal forms `outs.map (·.map (·.2))`, by recursion and
  `sl_cons` (D18), each member's handle slice behind a fresh `rec2` header (`decNFS`);
* the kinds `outs.map (·.map (·.1))`: `outs` itself, read by `decKSS` (a `(kinds, eidx)` record's
  first two words are its kinds' `[off, len]`);
* the fresh `NestState` (`check_block_positivity_init`) as `NSB`;
* `CssAt` (the positivity walk's view of the members' constructors) from their decoding with
  bounds (`decCNSB`, `checkBlockCtors_refines`' post).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Decoders of the results -/

/-- A member's normal forms: a pointer to `[off, len]` of handles. -/
def decNFS (m : Mem) (q : Nat) : Option (List EIdx) := decAt m (fun o l => decHL m o l) q

theorem decNFS_mono (q : Nat) : OMono (fun m => decNFS m q) :=
  OMono.decAt (fun o l => OMono.decHL o l) q

/-- A member's kinds: a pointer to `[off, len]` of pointers to `[k.off, k.len]` kinds slices. -/
def decKSS (m : Mem) (q : Nat) : Option (List (List NestFieldKind)) :=
  decAt m (fun o l => decPL m (fun v => decAt m (decKL m) v) o l) q

theorem decKSS_mono (q : Nat) : OMono (fun m => decKSS m q) :=
  OMono.decAt (fun o l => OMono.decPL (fun v => OMono.decAt (fun o l => decKL_mono o l) v) o l) q

theorem decKES_mono (q : Nat) : OMono (fun m => decKES m q) :=
  OMono.decAt (fun o l => OMono.decPL decKE_mono o l) q

theorem pos3_mapM_proj {α β γ : Type} (F : γ → Option α) (G : γ → Option β) (h : α → β)
    (hFG : ∀ c x, F c = some x → G c = some (h x)) :
    ∀ (L : List γ) (xs : List α), L.mapM F = some xs → L.mapM G = some (xs.map h)
  | [], xs, e => by simp at e; subst e; rfl
  | c :: L, xs, e => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at e ⊢
    obtain ⟨x, hx, ys, hys, rfl⟩ := e
    exact ⟨h x, hFG c x hx, ys.map h, pos3_mapM_proj F G h hFG L ys hys, rfl⟩

theorem pos3_decPL_proj {α β : Type} {m : Mem} {f : Nat → Option α} {g : Nat → Option β} (h : α → β)
    (hfg : ∀ v x, f v = some x → g v = some (h x)) {o l : Nat} {xs : List α}
    (e : decPL m f o l = some xs) : decPL m g o l = some (xs.map h) := by
  unfold decPL at e ⊢
  refine pos3_mapM_proj _ _ h (fun j x hx => ?_) _ _ e
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨v, hv, hx⟩ := hx
  exact ⟨v, hv, hfg v x hx⟩

theorem pos3_decAt_proj {α β : Type} {m : Mem} {g : Nat → Nat → Option (List α)}
    {g' : Nat → Nat → Option (List β)} (h : List α → List β)
    (hg : ∀ o l xs, g o l = some xs → g' o l = some (h xs)) {q : Nat} {xs : List α}
    (e : decAt m g q = some xs) : decAt m g' q = some (h xs) := by
  obtain ⟨o, l, ho, hl, hx⟩ := decAt_some e
  simp only [decAt, ho, hl, Option.bind_eq_bind, Option.bind_some]
  exact hg o l xs hx

/-- **The kinds are `outs` itself**: a `(kinds, eidx)` record read by its first two words. -/
theorem pos3_kinds {m : Mem} {o l : Nat} {outss : List (List (List NestFieldKind × EIdx))}
    (h : DecB (fun m => decPL m (decKES m) o l) m outss) :
    DecB (fun m => decPL m (decKSS m) o l) m (outss.map (·.map (·.1))) := by
  show decPL (truncM m) _ o l = _
  refine pos3_decPL_proj (List.map (·.1)) (fun v x hx => ?_) h
  refine pos3_decAt_proj (List.map (·.1)) (fun o' l' xs hxs => ?_) hx
  refine pos3_decPL_proj Prod.fst (fun w y hy => ?_) hxs
  simp only [decKE, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hy
  obtain ⟨k, hk, e, -, rfl⟩ := hy
  exact hk

/-! ## The constructors as the positivity walk reads them (`CssAt`) -/

theorem pos3_iwN_word {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) :
    ∃ w : Word, (m.arr64 IW)[i]? = some w ∧ w.toNat = v ∧ i < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨w, hw', rfl, hi⟩

/-- **`CssAt` from the constructors' decoding with bounds.** -/
theorem pos3_cssAt {m : Mem} {o l : Word} {css : List (List (IConstantVal × Nat))}
    (h : PSlR decCNSB css o l m) :
    l.toNat = css.length ∧ o.toNat + css.length ≤ iwTop m ∧ CssAt m o.toNat css := by
  have hlen : css.length = l.toNat := decPL_length _ h.1
  refine ⟨hlen.symm, by rw [hlen]; exact h.2, fun i hi => ?_⟩
  obtain ⟨v, hv, hcs⟩ := decPL_getH (truncM m) h.1 i (by omega)
  obtain ⟨hdr, hhdr, rfl, hi'⟩ := pos3_iwN_word hv
  obtain ⟨o', l', ho, hl, hb, hd⟩ := decCNSB_bound (m := m) (q := hdr.toNat) hcs
  obtain ⟨ow, how, rfl, hlt0⟩ := pos3_iwN_word ho
  obtain ⟨lw, hlw, rfl, hlt1⟩ := pos3_iwN_word hl
  refine ⟨hdr, ow, lw, hhdr, how, hlw, hi', hlt1, ?_, hb, fun j hj => ?_⟩
  · rw [← decPL_length _ hd]
  obtain ⟨w', hw', hx⟩ := decPL_getH (truncM m) hd j (by rw [← decPL_length _ hd]; exact hj)
  obtain ⟨w, hw, rfl, hwlt⟩ := pos3_iwN_word hw'
  refine ⟨w, hw, ?_⟩
  simp only [decCN, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx
  obtain ⟨q, hq, cv, hcv, nF, hnF, hx⟩ := hx
  obtain ⟨qw, hqw, rfl, hq0⟩ := pos3_iwN_word hq
  obtain ⟨nw, hnw, rfl, hq1⟩ := pos3_iwN_word hnF
  rw [← Option.some.inj hx]
  refine ⟨hq0, hq1, qw.toNat, by simp [iwN, nat?, iwA, hqw], decCVp_truncM hcv, by simp [iwN, nat?, iwA, hnw]⟩

/-- The constructors, read by `check_abs_ctor_sorts_all`. -/
theorem pos3_cns {m : Mem} {o l : Word} {css : List (List (IConstantVal × Nat))}
    (h : PSlR decCNSB css o l m) : PSlR0 decCNS css o l m := by
  refine ⟨?_, Or.inr h.2⟩
  show decPL (truncM m) _ o.toNat l.toNat = some css
  have := pos3_decPL_proj (m := truncM m) (g := decCNS (truncM m)) id
    (fun v x hx => decCNSB_decCNS (m := m) (q := v) hx) h.1
  rwa [List.map_id] at this

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `check_block_positivity_nfs_member` -/

/-- The lookups of the normal forms' builders. -/
structure NfsProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  rec2 : p.lookup "rec2" = some rec2
  mem : p.lookup "check_block_positivity_nfs_member" = some checkBlockPositivityNfsMember
  nfs : p.lookup "check_block_positivity_nfs" = some checkBlockPositivityNfs

/-- **`check_block_positivity_nfs_member` is its model `pnmW`** (generated). -/
l_model pnm_spec (p : Prog)
    (hp : p.lookup "check_block_positivity_nfs_member" = some checkBlockPositivityNfsMember)
  fns [hp ↦ pnmW]
  specs [callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- `sl_cons` of a handle onto a handle slice, under the stage relation. -/
theorem pos3_consH {p : Prog} (hP : NfsProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List EIdx}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hb : o.toNat + l.toNat ≤ iwTop m) (hx : x.toNat < 2 ^ 32) (hxs : decHL m o.toNat l.toNat = some xs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (decI x :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons n _ x o l) h
  obtain ⟨hS', hg, hd, ht⟩ := consW_stage hW hS hb hx hxs
  exact ⟨hS', hg, consW_mfr hW, hd, ht⟩

/-- **`check_block_positivity_nfs_member`'s model: the members' normal forms**, a fresh handle slice. -/
theorem pnmW_ok {p : Prog} (hP : NfsProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (n : Nat) : ∀ (m m' : Mem) (a : AState) (o l : Word) (pairs : List (List NestFieldKind × EIdx))
    (r : List Word), pnmW p n m o l = some (r, m') → StageR dn vis fe m a → PSlR0 decKE pairs o l m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (pairs.map (·.2)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a o l pairs r h; simp [pnmW.eq_1] at h
  | succ n ih =>
  intro m m' a o l pairs r h hS hpr
  by_cases hl : l = 0
  · rw [pnmW.arm1 p n m o l hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hpr.nil hl]
    exact ⟨hS, IWGrow.refl _, MFr.refl _ _ _, by simp [decHL, hslice?], by simp⟩
  rw [pnmW.arm2 p n m o l hl] at h
  obtain ⟨q, ⟨ks, e⟩, pairs', rfl, hw, hqb, hdq, hrest⟩ := partsPSl_cons (hpr.pslr hl) hl
  rw [hw] at h
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  -- the record's handle
  have hdqT : decKE (truncM m) q = some (ks, e) := hdq
  simp only [decKE, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at hdqT
  obtain ⟨-, -, ee, hee, -, rfl⟩ := hdqT
  obtain ⟨heelt, hee'⟩ := rec2IwH_trunc hee
  obtain ⟨ew, hew, hew32, hewe⟩ := iwH_rdW_at (w := UInt64.ofNat q) (k := 2) (by rw [hq']; exact hee')
    hS.2.2.2.1
  rw [show (UInt64.ofNat 2 : Word) = 2 from rfl] at hew
  -- the rest
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (pnmW.k_check_block_positivity_nfs_member.none ..)
  rw [pnmW.k_check_block_positivity_nfs_member.arm1] at h
  obtain ⟨hS1, hg1, hf1, hd1, hb1⟩ := ih m m1 a (o + 1) (l - 1) pairs' r1 h1 hS ⟨hrest.1, Or.inr hrest.2⟩
  have hTm : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hq2 : (UInt64.ofNat q + 2 : Word).toNat = q + 2 := by
    rw [UInt64.toNat_add, hq']; simp only [UInt64.reduceToNat]; omega
  have hew1 : rdW (m1.arr64 IW) (UInt64.ofNat q + 2) = ew := by
    rw [← hew]; simp only [rdW]
    rw [hq2, hg1.2.2.1 _ heelt]
  rw [hew1] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [pnmW.k_sl_cons.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS2, hg2, hf2, hd2, hb2⟩ := pos3_consH hP h2 hS1 hb1 hew32 hd1
  refine ⟨hS2, hg1.trans hg2, hf1.trans hf2, ?_, by simp only [List.headD_cons, List.tail_cons]; omega⟩
  simp only [List.headD_cons, List.tail_cons, List.map_cons, hd2, hewe]

/-! ## `check_block_positivity_nfs` -/

/-- **`check_block_positivity_nfs` is its model `pnfW`** (generated). -/
l_model pnf_spec (p : Prog) (hp : p.lookup "check_block_positivity_nfs" = some checkBlockPositivityNfs)
  fns [hp ↦ pnfW]
  specs [callW_spec p n "check_block_positivity_nfs_member", callW_spec p n "rec2", callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- **A `rec2` header `[off, len]` of a handle slice below the top**, decoded below the tops. -/
theorem pos3_rec2H {p : Prog} (hP : NfsProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List EIdx}
    (h : callW p n "rec2" [o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hx : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧ DecB (fun m => decNFS m (r.headD 0).toNat) m' xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h
  obtain ⟨-, -, -, hf, -, -⟩ := recW_post hW hS.2.2.2.2.2 hS.2.2.2.1 rfl
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  refine ⟨hS', hg, MFr.of_iw hf, ?_⟩
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM s'.mem) (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM s'.mem) ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hd := (decHL_decB hx hb).grow (OMono.decHL _ _) hg
  show decAt (truncM s'.mem) _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hd

/-- **`check_block_positivity_nfs`' model: `outs.map (·.map (·.2))`**, member by member behind fresh
headers. -/
theorem pnfW_ok {p : Prog} (hP : NfsProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (n : Nat) : ∀ (m m' : Mem) (a : AState) (s l : Word) (outss : List (List (List NestFieldKind × EIdx)))
    (r : List Word), pnfW p n m s l = some (r, m') → StageR dn vis fe m a → PSlR decKES outss s l m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧
      PSlR decNFS (outss.map (·.map (·.2))) (r.headD 0) (r.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' a s l outss r h; simp [pnfW.eq_1] at h
  | succ n ih =>
  intro m m' a s l outss r h hS hos
  by_cases hl : l = 0
  · rw [pnfW.arm1 p n m s l hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : outss = [] := by
      have h1 := hos.1; simp only [DecB, hl] at h1
      simpa [decPL] using h1.symm
    subst this
    exact ⟨hS, IWGrow.refl _, MFr.refl _ _ _, PSlR.nil decNFS m⟩
  rw [pnfW.arm2 p n m s l hl] at h
  obtain ⟨q, pairs, outss', rfl, hw, hqb, hdq, hrest⟩ := partsPSl_cons hos hl
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨po, pl, hpo, hpl, hpd, hpb⟩ := partsAt decKE_mono (show decAt (truncM m)
    (decPL (truncM m) (decKE (truncM m))) q = some pairs from hdq)
  obtain ⟨w1, -, -⟩ := partsIwRd hpo (w := UInt64.ofNat q) hq'
  obtain ⟨w2, -, -⟩ := partsIwRd hpl (w := UInt64.ofNat q + 1) (by
    have := partsIwLt hpl; have : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    rw [UInt64.toNat_add, hq']; simp; omega)
  rw [UInt64.ofNat_toNat] at w1 w2
  rw [hw, w1, w2] at h
  -- the member
  rcases h1 : callW p n "check_block_positivity_nfs_member" [po, pl] m with _ | ⟨r1, m1⟩
  · rw [h1] at h; simp [pnfW.k_check_block_positivity_nfs_member.none] at h
  rw [h1, pnfW.k_check_block_positivity_nfs_member.arm1] at h
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pnm_spec p hP.mem n _ po pl) h1
  obtain ⟨hS1, hg1, hf1, hd1, hb1⟩ := pnmW_ok hP n m s1.mem a po pl pairs r1 hW1 hS ⟨hpd, hpb⟩
  -- its header
  rcases h2 : callW p n "rec2" [r1.headD 0, r1.tail.headD 0] s1.mem with _ | ⟨r2, m2⟩
  · rw [h2] at h; simp [pnfW.k_rec2.none] at h
  rw [h2, pnfW.k_rec2.arm1] at h
  obtain ⟨hS2, hg2, hf2, hd2⟩ := pos3_rec2H hP h2 hS1 hd1 hb1
  -- the rest
  rcases h3 : pnfW p n m2 (s + 1) (l - 1) with _ | ⟨r3, m3⟩
  · rw [h3] at h; simp [pnfW.k_check_block_positivity_nfs.none] at h
  rw [h3, pnfW.k_check_block_positivity_nfs.arm1] at h
  have hg12 := hg1.trans hg2
  obtain ⟨hS3, hg3, hf3, hd3⟩ := ih m2 m3 a (s + 1) (l - 1) outss' r3 h3 hS2 (hrest.grow decKES_mono hg12)
  -- the cons
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl; rw [pnfW.k_sl_cons.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons n _ _ _ _) h4
  obtain ⟨hS4, hg4, hd4, ht4⟩ := partsConsPL decNFS_mono hW4 hS3 hd3.2 hd3.1 (hd2.grow (decNFS_mono _) hg3)
  refine ⟨hS4, (hg12.trans hg3).trans hg4, ((hf1.trans hf2).trans hf3).trans (consW_mfr hW4), ?_, ?_⟩
  · simpa using hd4
  · simp only [List.headD_cons, List.tail_cons]; omega

end L.Ind
