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

/-- A word read at `i` is read at `i'` too. -/
def WAt (R R' : Nat → Option Word) (i i' : Nat) : Prop := ∀ w, R i = some w → R' i' = some w

theorem nat?_sh {i i' : Nat} {x : Nat} (e : WAt R R' i i') (h : nat? R i = some x) :
    nat? R' i' = some x := by
  simp only [nat?, Option.map_eq_some_iff] at h ⊢
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, e w hw, rfl⟩
theorem bool?_sh {i i' : Nat} {x : Bool} (e : WAt R R' i i') (h : bool? R i = some x) :
    bool? R' i' = some x := by
  simp only [bool?, Option.map_eq_some_iff] at h ⊢
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, e w hw, rfl⟩
theorem hd?_sh {k : IdxKind} {i i' : Nat} {x : Idx k} (e : WAt R R' i i') (h : hd? R i = some x) :
    hd? R' i' = some x := by
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨w, hw, h⟩ := h; exact ⟨w, e w hw, h⟩

theorem hlist?_sh {k : IdxKind} {i i' : Nat} {xs : List (Idx k)} (e0 : WAt R R' i i')
    (e1 : WAt R R' (i + 1) (i' + 1)) (he : ArrExt R R') (hx : hlist? R i = some xs) :
    hlist? R' i' = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨o, ho, c, hc, hs⟩ := hx
  exact ⟨o, nat?_sh e0 ho, c, nat?_sh e1 hc, he.hslice? hs⟩

/-- **An inductive's capabilities, copied**: the 15 words at `q'` are those at `q`, the slices they
point to read on. -/
theorem decCaps_sh {q q' : Nat} {x : IIndCaps} (w : ∀ j < 15, WAt R R' (q + j) (q' + j))
    (he : ArrExt R R') (hx : decCaps R q = some x) : decCaps R' q' = some x := by
  have w0 : WAt R R' q q' := by simpa using w 0 (by omega)
  simp only [decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
  obtain ⟨e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e9, h9, e10, h10, e11, h11, e⟩ := hx
  exact ⟨e1, bool?_sh w0 h1, e2, hd?_sh (w 1 (by omega)) h2,
    e3, nat?_sh (w 2 (by omega)) h3, e4, nat?_sh (w 3 (by omega)) h4,
    e5, bool?_sh (w 4 (by omega)) h5, e6, nat?_sh (w 5 (by omega)) h6,
    e7, nat?_sh (w 6 (by omega)) h7,
    e9, hlist?_sh (w 10 (by omega)) (w 11 (by omega)) he h9,
    e10, nat?_sh (w 12 (by omega)) h10,
    e11, hlist?_sh (w 13 (by omega)) (w 14 (by omega)) he h11, e⟩

/-- A reducibility hint, copied (its two words). -/
theorem decHint_sh {q q' : Nat} {x : ConLeche.ReducibilityHint} (e0 : WAt R R' q q')
    (e1 : WAt R R' (q + 1) (q' + 1)) (hx : decHint R q = some x) : decHint R' q' = some x := by
  simp only [decHint, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨k, hk, e⟩ := hx
  refine ⟨k, nat?_sh e0 hk, ?_⟩
  split at e
  · exact e
  · exact e
  · simp only [Option.bind_eq_some_iff, Option.pure_def] at e ⊢
    obtain ⟨y, hy, e⟩ := e; exact ⟨y, nat?_sh e1 hy, e⟩
  · exact e

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
  refine ⟨nm, hd?_sh (fun _ e => by rw [w0]; exact e) hn, ps, ?_, t,
    hd?_sh (fun _ e => by rw [hw 3 (by omega)]; exact e) ht, e⟩
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

/-- **`er_copy_er(d, s, l)` writes words at `d`**, each the source word as the copy reads it
(after the words before it). -/
theorem erCopyErW_eq {p : Prog} (hp : p.lookup "erec_put" = some erecPut) :
    ∀ (k n : Nat) (m : Mem) (d s l : Word) (r : List Word) (m' : Mem), l.toNat = k →
    erCopyErW p n m d s l = some (r, m') →
    ∃ ws : List Word, ws.length = k ∧ m' = wrER m d ws ∧
      ∀ j (hj : j < ws.length), ws[j] = erRdT (wrER m d (ws.take j)) (s + UInt64.ofNat j) := by
  intro k
  induction k with
  | zero =>
    intro n m d s l r m' hl h
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by simpa using hl)
    cases n with
    | zero => rw [erCopyErW.eq_1] at h; cases h
    | succ n =>
    rw [erCopyErW.arm1 p n m d s l hl0, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], rfl, h.2.symm, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro n m d s l r m' hl h
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
    obtain ⟨ws, hlen, rfl, hws⟩ := ih n _ (d + 1) (s + 1) (l - 1) r2 _ hl1 h2
    refine ⟨erRdT m s :: ws, by simp [hlen], rfl, fun j hj => ?_⟩
    cases j with
    | zero => simp [wrER]
    | succ j =>
      simp only [List.getElem_cons_succ, List.take_succ_cons, wrER]
      rw [hws j (by simpa using hj), word_ofNat_succ]

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

namespace L.Ind

open L.Arena

section copyFresh
variable {vis : Word} {fe : IFEnv}

/-- **`er_copy_er(d, s, l)` into a fresh region**: each word of the base `m₀` at `s` copied to `d`
(above the base's top), `StageR` and the growth and frame from the base after it, every other
address as before. -/
theorem erCopyEr_fresh {p : Prog} (hpc : p.lookup "er_copy_er" = some erCopyEr)
    (hp : p.lookup "erec_put" = some erecPut) {n : Nat} {m₀ m m' : Mem} {a₀ a : AState}
    {d s l : Word} {r : List Word} (h₀ : StageR vis fe m₀ a₀) (hS : StageR vis fe m a)
    (hf : MemFrame quotA quotC m₀ m) (hg : IWGrow m₀ m) (hd0 : erTopOf m₀ d ≤ erOff d)
    (hdt : erOff d + l.toNat ≤ erTopOf m d) (hd41 : d.toNat < 2 ^ 41)
    (h : callW p n "er_copy_er" [d, s, l] m = some (r, m')) :
    StageR vis fe m' a ∧ IWGrow m₀ m' ∧ MemFrame quotA quotC m₀ m' ∧
      (∀ j < l.toNat, ∀ w, erecP m₀ (s + UInt64.ofNat j).toNat = some w →
        erecP m' (d.toNat + j) = some w) ∧
      (∀ i, (∀ j < l.toNat, i % 2 ^ 41 ≠ (d.toNat + j) % 2 ^ 41) → erecP m' i = erecP m i) ∧
      ∃ ws, m' = wrER m d ws := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erCopyEr_specW p hpc n _ d s l) h
  obtain ⟨ws, hlen, e, hws⟩ := erCopyErW_eq hp l.toNat n m d s l r s'.mem rfl hW
  rw [e]
  obtain ⟨hS', hg', hf', hrd', hout⟩ := wrER_fresh h₀ ws m a d hS hf hg hd0 (by omega) hd41
  rw [hlen] at hrd' hout
  refine ⟨hS', hg', hf', fun j hj w hw => ?_, hout, _, rfl⟩
  rw [hrd' j hj, List.getElem?_eq_getElem (by omega), hws j (by omega)]
  have hgj := (wrER_fresh h₀ (ws.take j) m a d hS hf hg hd0 (by simp; omega) hd41).2.1
  rw [erRdT_of _ _ (hgj.ext _ _ hw)]

end copyFresh

/-! ## `ci_at_lps(c, po, pl)` -/

/-- The lookups `ci_at_lps` needs beyond `QuotAtProg`. -/
structure CiProg (p : Prog) : Prop extends QuotAtProg p where
  ciAt : p.lookup "ci_at_lps" = some ciAtLps
  erCopyEr : p.lookup "er_copy_er" = some erCopyEr

theorem ciJ1_inv {p : Prog} {n : Nat} {c po pl k nn : Word} {m m' : Mem} {res : List Word}
    (hW : ciAtLpsW.j1 p n c po pl k nn m = some (res, m')) :
    ∃ r1 m1 r2 m2 r3 m3, callW p n "erec_alloc" [nn] m = some (r1, m1) ∧
      callW p n "erec_put" [r1.headD 0, k] m1 = some (r2, m2) ∧
      callW p n "cv_at_lps" [r1.headD 0 + 1, c + 1, po, pl] m2 = some (r3, m3) ∧
      ciAtLpsW.k_cv_at_lps p n c po pl k (r1.headD 0) (some (r3, m3)) = some (res, m') := by
  simp only [ciAtLpsW.j1] at hW
  cases h1 : callW p n "erec_alloc" [nn] m with
  | none => rw [h1] at hW; simp [ciAtLpsW.k_erec_alloc] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at hW; simp only [ciAtLpsW.k_erec_alloc] at hW
  cases h2 : callW p n "erec_put" [r1.headD 0, k] m1 with
  | none => rw [h2] at hW; simp [ciAtLpsW.k_erec_put] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at hW; simp only [ciAtLpsW.k_erec_put] at hW
  cases h3 : callW p n "cv_at_lps" [r1.headD 0 + 1, c + 1, po, pl] m2 with
  | none => rw [h3] at hW; simp [ciAtLpsW.k_cv_at_lps] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at hW
  exact ⟨r1, m1, r2, m2, r3, m3, by first | rfl | exact h1, by first | rfl | exact h2,
    by first | rfl | exact h3, hW⟩

theorem word_toNat_add {c : Word} {k : Nat} (h : c.toNat + k < 2 ^ 64) :
    (c + UInt64.ofNat k).toNat = c.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega

/-- The kind word of a constant record. -/
def ciKind : IConstantInfo → Nat
  | .axiomInfo .. => 0 | .defnInfo .. => 1 | .thmInfo _ => 2 | .indInfo .. => 3
  | .ctorInfo .. => 4 | .recInfo .. => 5

theorem decCI_kindW {R : Nat → Option Word} {q : Nat} {ci : IConstantInfo} {w : Word}
    (h : decCI R q = some ci) (hw : R q = some w) : w.toNat = ciKind ci := by
  simp only [decCI, nat?, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  split at h <;> simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    reduceCtorEq] at h <;> grind [ciKind]

theorem erecP_lt64 {m : Mem} {i : Nat} {w : Word} (h : erecP m i = some w) : i < 2 ^ 64 := by
  unfold erecP at h; split at h
  · assumption
  · cases h

section ci
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **The copied tail** (`er_copy_er(r + 5, c + 5, l)`) after the record's head. -/
theorem ciCopy {p : Prog} (hP : CiProg p) {n : Nat} {m m3 m4 : Mem} {a a3 : AState}
    {r nn k c l : Word} {cv' : IConstantVal} {r4 : List Word} (hT : StageT dn vis fe m a)
    (hpre : CiPre dn vis fe m m3 a3 r nn k cv') (hl : 5 + l.toNat ≤ nn.toNat)
    (h : callW p n "er_copy_er" [r + 5, c + 5, l] m3 = some (r4, m4)) :
    StageT dn vis fe m4 a3 ∧ IWGrow m m4 ∧ erecP m4 r.toNat = some k ∧
      decCV (erecP m4) (r.toNat + 1) = some cv' ∧
      ∀ j < l.toNat, WAt (erecP m) (erecP m4) (c.toNat + 5 + j) (r.toNat + 5 + j) := by
  have hcap := hpre.cap
  have htop := hpre.top
  have hbase := hpre.base
  obtain ⟨e5, eo5, et5⟩ := erAddr (r := r) (c := 5) (by simp; omega) hpre.r41
  simp only [show (5 : Word).toNat = 5 from rfl] at e5 eo5
  have hq : erOff r + 5 + l.toNat < 2 ^ 40 := by omega
  have hr41 := hpre.r41
  unfold erOff at hq
  obtain ⟨hS4, hg4, -, hrd4, hout4, ws, rfl⟩ := erCopyEr_fresh hP.erCopyEr hP.erPut hT.stage
    hpre.stT.stage hpre.fr hpre.grow (by rw [et5, eo5]; omega) (by rw [et5, eo5]; omega)
    (by rw [e5]; omega) h
  have hT4 := StageT.of_wrER hpre.stT hS4
  have hoth : ∀ i, i < 5 → erecP (wrER m3 (r + 5) ws) (r.toNat + i) = erecP m3 (r.toNat + i) :=
    fun i hi => hout4 _ fun j hj => by rw [e5]; omega
  refine ⟨hT4, hg4, by simpa using (hoth 0 (by omega)).trans (by simpa using hpre.kw), ?_, ?_⟩
  · exact hpre.cvR _ (fun j hj => by
      have := hoth (1 + j) (by omega); rwa [← Nat.add_assoc] at this) hg4.ext
  · intro j hj w hw
    rw [show r.toNat + 5 + j = (r + 5).toNat + j by rw [e5]]
    refine hrd4 j hj w ?_
    have h5 : (5 : Word).toNat = 5 := rfl
    have := erecP_lt64 hw
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat', h5]
    rw [show (c.toNat + 5) % 2 ^ 64 + j % 2 ^ 64 = c.toNat + 5 + j by omega,
      Nat.mod_eq_of_lt this]; exact hw

/-- **`ci_at_lps(c, po, pl)` refines `ci.atLps ps`** under `StageT`: the fresh record after it. -/
theorem ciAtLps_sim {p : Prog} (hP : CiProg p) (n : Nat) {m : Mem} {a : AState} {c po pl : Word}
    {ci : IConstantInfo} {ps : List NIdx} {psv : List ConLeche.Name} {cc : ConLeche.ConstantInfo}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a) (hr : ConRon.Bridge.ReadOK a)
    (hci : decCI (erecP m) c.toNat = some ci)
    (hdc : ConRon.Arena.Frontend.denoteCI a.store ci = some cc)
    (hps : hslice? (erecP m) po.toNat pl.toNat = some ps)
    (hden : ConRon.Arena.Frontend.denoteNList a.store.ns ps = some psv) :
    Sim (callW p n "ci_at_lps" [c, po, pl] m) (ci.atLps ps) a
      (fun r ci' m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧
        decCI (erecP m') (r.headD 0).toNat = some ci') := by
  intro res m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ciAtLps_specW p hP.ciAt n _ c po pl) h
  cases n with
  | zero => simp [ciAtLpsW] at hW
  | succ n =>
  simp only [ciAtLpsW] at hW
  -- the kind word
  have hk0 : ∃ w, erecP m c.toNat = some w := by
    cases e : erecP m c.toNat with
    | none => simp [decCI, nat?, e] at hci
    | some w => exact ⟨w, rfl⟩
  obtain ⟨w, hw⟩ := hk0
  have ew : erRdT m c = w := erRdT_of _ _ hw
  simp only [show rdW (m.arr64 (tierA EREC (c >>> 40))) (c &&& 1099511627775) = erRdT m c from rfl,
    ew] at hW
  have hcv := decCI_cvA hci
  have hkd := decCI_kindW hci hw
  cases ci with
  | axiomInfo cv =>
    obtain rfl : w = 0 := UInt64.toNat_inj.mp hkd
    simp (config := { decide := true }) only [↓reduceIte] at hW
    obtain ⟨r1, m1, r2, m2, r3, m3, h1, h2, h3, hW⟩ := ciJ1_inv hW
    simp (config := { decide := true }) only [ciAtLpsW.k_cv_at_lps, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨cv', a3, hrun, hpre⟩ := ciPre_of hP.toQuotAtProg n hT hok hci hps hden (by decide) h1 h2 h3
    refine ⟨.axiomInfo cv', a3, ?_, hpre.stT, hpre.grow, ?_⟩
    · simp only [IConstantInfo.atLps, StateT.run_bind]
      rw [show (cv.atLps ps).run a = .ok (cv', a3) from hrun]; rfl
    · simp only [List.headD_cons, decCI, nat?, hpre.kw, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hpre.cvR _ (fun _ _ => rfl) hpre.grow.ext]
      rfl
  | defnInfo cv v hint => sorry
  | thmInfo cv =>
    obtain rfl : w = 2 := UInt64.toNat_inj.mp hkd
    simp (config := { decide := true }) only [↓reduceIte] at hW
    obtain ⟨r1, m1, r2, m2, r3, m3, h1, h2, h3, hW⟩ := ciJ1_inv hW
    simp (config := { decide := true }) only [ciAtLpsW.k_cv_at_lps, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨cv', a3, hrun, hpre⟩ := ciPre_of hP.toQuotAtProg n hT hok hci hps hden (by decide) h1 h2 h3
    refine ⟨.thmInfo cv', a3, ?_, hpre.stT, hpre.grow, ?_⟩
    · simp only [IConstantInfo.atLps, StateT.run_bind]
      rw [show (cv.atLps ps).run a = .ok (cv', a3) from hrun]; rfl
    · simp only [List.headD_cons, decCI, nat?, hpre.kw, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hpre.cvR _ (fun _ _ => rfl) hpre.grow.ext]
      rfl
  | indInfo cv caps =>
    obtain rfl : w = 3 := UInt64.toNat_inj.mp hkd
    have hci' := hci
    simp only [decCI, nat?, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      show (3 : Word).toNat = 3 from rfl, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, IConstantInfo.indInfo.injEq] at hci'
    obtain ⟨cv0, -, caps0, hcaps, -, rfl⟩ := hci'
    simp (config := { decide := true }) only [↓reduceIte] at hW
    obtain ⟨r1, m1, r2, m2, r3, m3, h1, h2, h3, hW⟩ := ciJ1_inv hW
    simp (config := { decide := true }) only [ciAtLpsW.k_cv_at_lps, ↓reduceIte] at hW
    cases h4 : callW p n "er_copy_er" [r1.headD 0 + 5, c + 5, 15] m3 with
    | none => rw [h4] at hW; simp [ciAtLpsW.k_er_copy_er] at hW
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4] at hW
    simp only [ciAtLpsW.k_er_copy_er, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨cv', a3, hrun, hpre⟩ := ciPre_of hP.toQuotAtProg n hT hok hci hps hden (by decide) h1 h2 h3
    obtain ⟨hT4, hg4, hk4, hcv4, hc4⟩ := ciCopy hP hT hpre (l := 15) (by decide) h4
    refine ⟨.indInfo cv' caps0, a3, ?_, hT4, hg4, ?_⟩
    · simp only [IConstantInfo.atLps, StateT.run_bind]
      rw [show (cv.atLps ps).run a = .ok (cv', a3) from hrun]; rfl
    · have hc := decCaps_sh (fun j hj => hc4 j hj) hg4.ext hcaps
      simp only [List.headD_cons, decCI, nat?, hk4, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hcv4, show (3 : Word).toNat = 3 from rfl, hc]
      rfl
  | ctorInfo cv np nf =>
    obtain rfl : w = 4 := UInt64.toNat_inj.mp hkd
    have hci' := hci
    simp only [decCI, nat?, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      show (4 : Word).toNat = 4 from rfl, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, IConstantInfo.ctorInfo.injEq, Option.map_eq_some_iff] at hci'
    obtain ⟨cv0, -, x5, ⟨w5, hw5, rfl⟩, x6, ⟨w6, hw6, rfl⟩, -, rfl, rfl⟩ := hci'
    simp (config := { decide := true }) only [↓reduceIte] at hW
    obtain ⟨r1, m1, r2, m2, r3, m3, h1, h2, h3, hW⟩ := ciJ1_inv hW
    simp (config := { decide := true }) only [ciAtLpsW.k_cv_at_lps, ↓reduceIte] at hW
    cases h4 : callW p n "er_copy_er" [r1.headD 0 + 5, c + 5, 2] m3 with
    | none => rw [h4] at hW; simp [ciAtLpsW.k_er_copy_er] at hW
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4] at hW
    simp only [ciAtLpsW.k_er_copy_er, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨cv', a3, hrun, hpre⟩ := ciPre_of hP.toQuotAtProg n hT hok hci hps hden (by decide) h1 h2 h3
    obtain ⟨hT4, hg4, hk4, hcv4, hc4⟩ := ciCopy hP hT hpre (l := 2) (by decide) h4
    refine ⟨.ctorInfo cv' w5.toNat w6.toNat, a3, ?_, hT4, hg4, ?_⟩
    · simp only [IConstantInfo.atLps, StateT.run_bind]
      rw [show (cv.atLps ps).run a = .ok (cv', a3) from hrun]; rfl
    · have e5 := hc4 0 (by decide) w5 (by simpa using hw5)
      have e6 := hc4 1 (by decide) w6 hw6
      simp only [Nat.add_zero] at e5
      rw [show (r1.headD 0).toNat + 5 + 1 = (r1.headD 0).toNat + 6 by omega] at e6
      simp only [List.headD_cons, decCI, nat?, hk4, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hcv4, show (4 : Word).toNat = 4 from rfl, e5, e6]
      rfl
  | recInfo cv mI rP isK rules => sorry

end ci

end L.Ind
