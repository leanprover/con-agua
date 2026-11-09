module

public import ConAgua.Arena.QuotAtT
public import ConAgua.Arena.QuotRecW
import ConAgua.Arena.InferLeaves

@[expose] public section

/-!
# A pin at a stream's names: `ci_at_lps` (lane `ronsync2`, stage 3)

`ci_at_lps(c, po, pl)` refines `IConstantInfo.atLps ci ps` (`CiAtLpsSim`): a fresh record of the
pin's kind (`erec_alloc`), its kind word and constant value (`cv_at_lps`, `cvAtLps_sim`), then per
kind the words copied (`er_copy_er`: an inductive's capabilities, a constructor's counts, a
definition's hint), a definition's value (`param_levels`, `inst_lp`), a recursor's rules
(`rules_at_lps_go`: each right-hand side by `inst_lp`, a `.levels` fire by `fire_levels_at`).
The words go to the region above the base state's top (`wrER_fresh`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## Decoding words copied to another place -/

section shift
variable {R R' : Nat → Option Word}

theorem nat?_sh {i i' : Nat} (e : R' i' = R i) : nat? R' i' = nat? R i := by simp only [nat?, e]
theorem bool?_sh {i i' : Nat} (e : R' i' = R i) : bool? R' i' = bool? R i := by simp only [bool?, e]
theorem hd?_sh {k : IdxKind} {i i' : Nat} (e : R' i' = R i) : (hd? R' i' : Option (Idx k)) = hd? R i := by
  simp only [hd?, e]

theorem hlist?_sh {k : IdxKind} {i i' : Nat} {xs : List (Idx k)} (e0 : R' i' = R i)
    (e1 : R' (i' + 1) = R (i + 1)) (he : ArrExt R R') (hx : hlist? R i = some xs) :
    hlist? R' i' = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨o, ho, c, hc, hs⟩ := hx
  exact ⟨o, by rw [nat?_sh e0]; exact ho, c, by rw [nat?_sh e1]; exact hc, he.hslice? hs⟩

/-- **An inductive's capabilities, copied**: the 15 words at `q'` are those at `q`, the slices they
point to read on. -/
theorem decCaps_sh {q q' : Nat} {x : IIndCaps} (hw : ∀ j < 15, R' (q' + j) = R (q + j))
    (he : ArrExt R R') (hx : decCaps R q = some x) : decCaps R' q' = some x := by
  have w : ∀ j < 15, R' (q' + j) = R (q + j) := hw
  have w0 : R' q' = R q := by simpa using w 0 (by omega)
  simp only [decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
  obtain ⟨e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e9, h9, e10, h10, e11, h11, e⟩ := hx
  exact ⟨e1, by rw [bool?_sh w0]; exact h1, e2, by rw [hd?_sh (w 1 (by omega))]; exact h2,
    e3, by rw [nat?_sh (w 2 (by omega))]; exact h3, e4, by rw [nat?_sh (w 3 (by omega))]; exact h4,
    e5, by rw [bool?_sh (w 4 (by omega))]; exact h5, e6, by rw [nat?_sh (w 5 (by omega))]; exact h6,
    e7, by rw [nat?_sh (w 6 (by omega))]; exact h7,
    e9, hlist?_sh (w 10 (by omega)) (w 11 (by omega)) he h9,
    e10, by rw [nat?_sh (w 12 (by omega))]; exact h10,
    e11, hlist?_sh (w 13 (by omega)) (w 14 (by omega)) he h11, e⟩

/-- A reducibility hint, copied (its two words). -/
theorem decHint_sh {q q' : Nat} {x : ConLeche.ReducibilityHint} (e0 : R' q' = R q)
    (e1 : R' (q' + 1) = R (q + 1)) (hx : decHint R q = some x) : decHint R' q' = some x := by
  simp only [decHint, nat?_sh e0, nat?_sh e1]; exact hx

end shift

/-! ## Addresses in a fresh region -/

/-- An address `c` words into a region of its tier. -/
theorem erAddr {r c : Word} (hc : erOff r + c.toNat < 2 ^ 40) (hr : r.toNat < 2 ^ 41) :
    (r + c).toNat = r.toNat + c.toNat ∧ erOff (r + c) = erOff r + c.toNat ∧
      ∀ X : Mem, erTopOf X (r + c) = erTopOf X r := by
  have h1 : (r + c).toNat = r.toNat + c.toNat := by
    rw [UInt64.toNat_add]; unfold erOff at hc; have := c.toNat_lt; omega
  have h2 : (r + c).toNat / 2 ^ 40 % 2 = r.toNat / 2 ^ 40 % 2 := by
    rw [h1]; unfold erOff at hc; omega
  refine ⟨h1, ?_, fun X => by simp only [erTopOf, h2]⟩
  unfold erOff at hc ⊢; rw [h1]; omega

/-- A constant value whose slice words point below a base: it decodes in every reader with the
same four words that extends the base. -/
theorem decCV_move {R R' R₀ : Nat → Option Word} {q : Nat} {cv : IConstantVal} {o l : Word}
    {xs : List NIdx} (h : decCV R q = some cv) (ho : R (q + 1) = some o) (hl : R (q + 2) = some l)
    (h0 : hslice? R₀ o.toNat l.toNat = some xs) (he : ArrExt R₀ R) (he' : ArrExt R₀ R')
    (hw : ∀ j < 4, R' (q + j) = R (q + j)) : decCV R' q = some cv := by
  have w0 : R' q = R q := by simpa using hw 0 (by omega)
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h ⊢
  obtain ⟨nm, hn, ps, hp, t, ht, e⟩ := h
  refine ⟨nm, by rw [hd?_sh w0]; exact hn, ps, ?_, t, by rw [hd?_sh (hw 3 (by omega))]; exact ht, e⟩
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff, nat?, ho, hl, Option.map_some,
    Option.some.injEq, exists_eq_left'] at hp ⊢
  have e1 := he.hslice? h0
  rw [hp] at e1; cases e1
  rw [show q + 1 + 1 = q + 2 by omega, hw 1 (by omega), hw 2 (by omega), ho, hl]
  simpa using he'.hslice? h0

/-! ## `ci_at_lps`: the record's head (`erec_alloc`, the kind word, `cv_at_lps`) -/

section pre
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **The state after the record's head**: the region `[r, r + nn)` allocated above `m`'s top, the
kind word and the constant value written, `StageT` after. -/
structure CiPre (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m3 : Mem)
    (a3 : AState) (r nn k : Word) (cv' : IConstantVal) : Prop where
  stT : StageT dn vis fe m3 a3
  grow : IWGrow m m3
  fr : MemFrame quotA quotC m m3
  base : erTopOf m r ≤ erOff r
  top : erOff r + nn.toNat ≤ erTopOf m3 r
  cap : erTopOf m3 r < 2 ^ 40
  r41 : r.toNat < 2 ^ 41
  kw : erecP m3 r.toNat = some k
  /-- The constant value decodes in every later reader keeping its four words. -/
  cvR : ∀ Y : Mem, (∀ j < 4, erecP Y (r.toNat + 1 + j) = erecP m3 (r.toNat + 1 + j)) →
    ArrExt (erecP m) (erecP Y) → decCV (erecP Y) (r.toNat + 1) = some cv'

/-- **The record's head**: `erec_alloc(nn)`, `erec_put(r, k)`, `cv_at_lps(r + 1, c + 1, po, pl)`. -/
theorem ciPre_of {p : Prog} (hP : QuotAtProg p) (n : Nat) {m m1 m2 m3 : Mem} {a : AState}
    {c po pl nn k : Word} {r1 r2 r3 : List Word} {ci : IConstantInfo} {ps : List NIdx}
    {psv : List ConLeche.Name}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a)
    (hci : decCI (erecP m) c.toNat = some ci)
    (hps : hslice? (erecP m) po.toNat pl.toNat = some ps)
    (hden : ConRon.Arena.Frontend.denoteNList a.store.ns ps = some psv) (hnn : 5 ≤ nn.toNat)
    (h1 : callW p n "erec_alloc" [nn] m = some (r1, m1))
    (h2 : callW p n "erec_put" [r1.headD 0, k] m1 = some (r2, m2))
    (h3 : callW p n "cv_at_lps" [r1.headD 0 + 1, c + 1, po, pl] m2 = some (r3, m3)) :
    ∃ cv' a3, (ci.toConstantVal.atLps ps).run a = .ok (cv', a3) ∧
      CiPre dn vis fe m m3 a3 (r1.headD 0) nn k cv' := by
  have hA := callW_erecAlloc hP.erAlloc h1
  have hqf1 := callW_quotFrame hP.quot (by decide) h1
  generalize r1.headD 0 = r at hA h2 h3 ⊢
  obtain ⟨hT1, hg1, hoff, htop, hr41⟩ := erAlloc_stageT hA hT
  have ⟨htop1, hcap1⟩ := hT1.stage.iw.topOf r
  have hm2 := callW_erecPut hP.erPut h2
  subst hm2
  obtain ⟨hS2, hg2, hf2⟩ := StageR.putFresh hT.stage hT1.stage hqf1 hg1 (v := k)
    (by rw [hoff]; exact Nat.le_refl _)
  have hT2 : StageT dn vis fe (erecPutMem m1 r k) a := StageT.of_wrER (ws := [k]) hT1 hS2
  have hkw : erecP (erecPutMem m1 r k) r.toNat = some k :=
    erecP_putMem_self (by omega) (by omega)
  obtain ⟨e1, eo1, et1⟩ := erAddr (c := 1) (by simp; omega) hr41
  simp only [UInt64.toNat_one] at e1 eo1
  have hcv := ArrExt.decCV hg2.ext (decCI_cvA hci)
  have et2 : erTopOf (erecPutMem m1 r k) r = erTopOf m1 r := by
    simp only [erTopOf, erecTop, erecTop1, erecPutMem_ctl]
  have hd0 : erTopOf m (r + 1) ≤ erOff (r + 1) := by rw [et1, eo1, hoff]; omega
  have hdt : erOff (r + 1) + 4 ≤ erTopOf (erecPutMem m1 r k) (r + 1) := by
    rw [et1, eo1, et2, htop, ← hoff]; omega
  have hlt : erOff r + nn.toNat < 2 ^ 40 := by omega
  have hd41 : (r + 1).toNat < 2 ^ 41 := by rw [e1]; unfold erOff at hlt; omega
  obtain ⟨cv', a3, hrun, hT3, hg3, hf3, hdec3, hout3, hpo3, hpl3, ht3⟩ :=
    cvAtLps_sim hP n hT.stage hT2 hok hf2 hg2 (d := r + 1) (c := c) hd0 hdt hd41 hcv hps hden r3 m3 h3
  refine ⟨cv', a3, hrun, ⟨hT3, hg3, hf3, by rw [hoff]; exact Nat.le_refl _, ?_, ?_, hr41, ?_, ?_⟩⟩
  · rw [ht3, et2, htop, ← hoff]; exact Nat.le_refl _
  · rw [ht3, et2]; omega
  · rw [hout3 _ fun j _ => by rw [e1]; omega]; exact hkw
  · intro Y hY he
    rw [e1] at hdec3 hpo3 hpl3
    exact decCV_move hdec3 hpo3 hpl3 hps hg3.ext he fun j hj => hY j hj

end pre

/-! ## The copies -/

theorem word_ofNat_succ (s : Word) (j : Nat) : s + 1 + UInt64.ofNat j = s + UInt64.ofNat (j + 1) := by
  rw [UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_one]; omega

/-- **`er_copy_er(d, s, l)` writes the source words** at `d`, provided no prefix of the copy
changes a source word it reads later (`hsrc`). -/
theorem erCopyErW_eq {p : Prog} (hp : p.lookup "erec_put" = some erecPut) :
    ∀ (k n : Nat) (m : Mem) (d s l : Word) (r : List Word) (m' : Mem), l.toNat = k →
    erCopyErW p n m d s l = some (r, m') →
    (∀ (ws : List Word) (j : Nat), ws.length ≤ j → j < k →
      erRdT (wrER m d ws) (s + UInt64.ofNat j) = erRdT m (s + UInt64.ofNat j)) →
    m' = wrER m d ((List.range k).map fun j => erRdT m (s + UInt64.ofNat j)) := by
  intro k
  induction k with
  | zero =>
    intro n m d s l r m' hl h _
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by simpa using hl)
    cases n with
    | zero => rw [erCopyErW.eq_1] at h; cases h
    | succ n =>
    rw [erCopyErW.arm1 p n m d s l hl0, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; rfl
  | succ k ih =>
    intro n m d s l r m' hl h hsrc
    have hl0 : l ≠ 0 := fun e => by subst e; simp at hl
    cases n with
    | zero => rw [erCopyErW.eq_1] at h; cases h
    | succ n =>
    rw [erCopyErW.arm2 p n m d s l hl0] at h
    cases h1 : callW p n "erec_put" [d, erRdT m s] m with
    | none => rw [h1] at h; simp [erCopyErW.k_erec_put.none] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, erCopyErW.k_erec_put.arm1] at h
    have hm1 := callW_erecPut hp h1
    subst hm1
    cases h2 : erCopyErW p n (erecPutMem m d (erRdT m s)) (d + 1) (s + 1) (l - 1) with
    | none => rw [h2] at h; simp [erCopyErW.k_er_copy_er.none] at h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, erCopyErW.k_er_copy_er.arm1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hl1 : (l - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hx : ∀ (ws : List Word) (j : Nat), ws.length ≤ j → j < k →
        erRdT (wrER (erecPutMem m d (erRdT m s)) (d + 1) ws) (s + 1 + UInt64.ofNat j) =
          erRdT m (s + UInt64.ofNat (j + 1)) := fun ws j hw hj => by
      rw [word_ofNat_succ]
      exact hsrc (erRdT m s :: ws) (j + 1) (by simp; omega) (by omega)
    have e := ih n _ (d + 1) (s + 1) (l - 1) r2 m2 hl1 h2 fun ws j hw hj => by
      rw [hx ws j hw hj, ← hx [] j (by simp) hj]; rfl
    rw [e, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [wrER]
    have e0 : s + UInt64.ofNat 0 = s := by simp
    rw [e0]
    congr 1
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply]
    have := hx [] j (by simp) (List.mem_range.mp hj)
    simp only [wrER] at this
    rw [this]

/-- **`spn_to_er(d, s, l)` writes the stack words** at `d` (the record writes leave `SPN`). -/
theorem spnToErW_eq {p : Prog} (hp : p.lookup "erec_put" = some erecPut) :
    ∀ (k n : Nat) (m : Mem) (d s l : Word) (r : List Word) (m' : Mem), l.toNat = k →
    spnToErW p n m d s l = some (r, m') →
    m' = wrER m d ((List.range k).map fun j => rdW (m.arr64 SPN) (s + UInt64.ofNat j)) := by
  intro k
  induction k with
  | zero =>
    intro n m d s l r m' hl h
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by simpa using hl)
    cases n with
    | zero => rw [spnToErW.eq_1] at h; cases h
    | succ n =>
    rw [spnToErW.arm1 p n m d s l hl0, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; rfl
  | succ k ih =>
    intro n m d s l r m' hl h
    have hl0 : l ≠ 0 := fun e => by subst e; simp at hl
    cases n with
    | zero => rw [spnToErW.eq_1] at h; cases h
    | succ n =>
    rw [spnToErW.arm2 p n m d s l hl0] at h
    cases h1 : callW p n "erec_put" [d, rdW (m.arr64 SPN) s] m with
    | none => rw [h1] at h; simp [spnToErW.k_erec_put.none] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, spnToErW.k_erec_put.arm1] at h
    have hm1 := callW_erecPut hp h1
    subst hm1
    cases h2 : spnToErW p n (erecPutMem m d (rdW (m.arr64 SPN) s)) (d + 1) (s + 1) (l - 1) with
    | none => rw [h2] at h; simp [spnToErW.k_spn_to_er.none] at h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, spnToErW.k_spn_to_er.arm1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hl1 : (l - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hS : (erecPutMem m d (rdW (m.arr64 SPN) s)).arr64 SPN = m.arr64 SPN :=
      (erecPutMem_frame m d _).arr SPN (by decide) (by decide)
    rw [ih n _ (d + 1) (s + 1) (l - 1) r2 m2 hl1 h2, List.range_succ_eq_map, List.map_cons,
      List.map_map, hS]
    simp only [wrER]
    have e0 : s + UInt64.ofNat 0 = s := by simp
    rw [e0]
    congr 2
    funext j
    simp only [Function.comp_apply, word_ofNat_succ]

end L.Ind
