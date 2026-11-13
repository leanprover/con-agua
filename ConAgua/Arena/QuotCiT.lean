module

public import ConAgua.Arena.QuotAtT
import ConRon.Bridge.Checker.Canon
import ConAgua.Arena.RecLayout.CapsDec
import ConAgua.Arena.IlpRd
import ConAgua.L.WordOff
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.RecLayout.CIDec

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
  -- the value's four words in order (a whole-record copy): the offsets as numbers (`rec_unfold`)
  simp only [rec_unfold, UInt64.reduceToNat] at h ⊢
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
  have hcv := ArrExt.decCV hg2.ext (decCI_cv hci)
  have et2 : erTopOf (erecPutMem m1 r k) r = erTopOf m1 r := by
    simp only [erTopOf, erTop, erecTop1, erecPutMem_ctl]
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
      ∀ j (hj : j < ws.length), ws[j] = erRd (wrER m d (ws.take j)) (s + UInt64.ofNat j) := by
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
    rw [erCopyErW.arm2 p n m d s l hl0] at h; simp only [erRd_foldN] at h
    cases h1 : callW p n "erec_put" [d, erRd m s] m with
    | none => rw [h1] at h; simp [erCopyErW.k_erec_put.none] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, erCopyErW.k_erec_put.arm1] at h
    have hm1 := callW_erecPut hp h1
    subst hm1
    cases h2 : erCopyErW p n (erecPutMem m d (erRd m s)) (d + 1) (s + 1) (l - 1) with
    | none => rw [h2] at h; simp [erCopyErW.k_er_copy_er.none] at h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, erCopyErW.k_er_copy_er.arm1, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hl1 : (l - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨ws, hlen, rfl, hws⟩ := ih n _ (d + 1) (s + 1) (l - 1) r2 _ hl1 h2
    refine ⟨erRd m s :: ws, by simp [hlen], rfl, fun j hj => ?_⟩
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
  rw [erRd_of _ _ (hgj.ext _ _ hw)]

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
  try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
  cases h1 : callW p n "erec_alloc" [nn] m with
  | none => rw [h1] at hW; simp [ciAtLpsW.k_erec_alloc] at hW
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at hW; simp only [ciAtLpsW.k_erec_alloc] at hW
  try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
  cases h2 : callW p n "erec_put" [r1.headD 0, k] m1 with
  | none => rw [h2] at hW; simp [ciAtLpsW.k_erec_put] at hW
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at hW; simp only [ciAtLpsW.k_erec_put] at hW
  try simp only [rec_unfold] at hW
  cases h3 : callW p n "cv_at_lps" [r1.headD 0 + 1, c + 1, po, pl] m2 with
  | none => rw [h3] at hW; simp [ciAtLpsW.k_cv_at_lps] at hW
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at hW
  exact ⟨r1, m1, r2, m2, r3, m3, by first | rfl | exact h1, by first | rfl | exact h2,
    by first | rfl | exact h3, hW⟩

/-- The kind word of a constant record. -/
def ciKindQ : IConstantInfo → Nat
  | .axiomInfo .. => 0 | .defnInfo .. => 1 | .thmInfo _ => 2 | .indInfo .. => 3
  | .ctorInfo .. => 4 | .recInfo .. => 5

theorem decCI_kindW {R : Nat → Option Word} {q : Nat} {ci : IConstantInfo} {w : Word}
    (h : decCI R q = some ci) (hw : R q = some w) : w.toNat = ciKindQ ci := by
  simp only [decCI, nat?, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  split at h <;> simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    reduceCtorEq] at h <;> grind [ciKindQ]

section ci
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **The copied tail** (`er_copy_er(r + 5, c + 5, l)`) after the record's head. -/
theorem ciCopy {p : Prog} (hP : CiProg p) {n : Nat} {m m3 m4 : Mem} {a a3 : AState}
    {r nn k c o l : Word} {cv' : IConstantVal} {r4 : List Word} (hT : StageT dn vis fe m a)
    (hpre : CiPre dn vis fe m m3 a3 r nn k cv') (ho : 5 ≤ o.toNat) (hl : o.toNat + l.toNat ≤ nn.toNat)
    (h : callW p n "er_copy_er" [r + o, c + o, l] m3 = some (r4, m4)) :
    StageT dn vis fe m4 a3 ∧ IWGrow m m4 ∧ erecP m4 r.toNat = some k ∧
      decCV (erecP m4) (r.toNat + 1) = some cv' ∧
      ∀ j < l.toNat, WAt (erecP m) (erecP m4) (c.toNat + o.toNat + j) (r.toNat + o.toNat + j) := by
  have hcap := hpre.cap
  have htop := hpre.top
  have hbase := hpre.base
  obtain ⟨e5, eo5, et5⟩ := erAddr (r := r) (c := o) (by omega) hpre.r41
  have hq : erOff r + o.toNat + l.toNat < 2 ^ 40 := by omega
  have hr41 := hpre.r41
  unfold erOff at hq
  obtain ⟨hS4, hg4, -, hrd4, hout4, ws, rfl⟩ := erCopyEr_fresh hP.erCopyEr hP.erPut hT.stage
    hpre.stT.stage hpre.fr hpre.grow (by rw [et5, eo5]; omega) (by rw [et5, eo5]; omega)
    (by rw [e5]; omega) h
  have hT4 := StageT.of_wrER hpre.stT hS4
  have hoth : ∀ i, i < 5 → erecP (wrER m3 (r + o) ws) (r.toNat + i) = erecP m3 (r.toNat + i) :=
    fun i hi => hout4 _ fun j hj => by rw [e5]; omega
  refine ⟨hT4, hg4, by simpa using (hoth 0 (by omega)).trans (by simpa using hpre.kw), ?_, ?_⟩
  · exact hpre.cvR _ (fun j hj => by
      have := hoth (1 + j) (by omega); rwa [← Nat.add_assoc] at this) hg4.ext
  · intro j hj w hw
    rw [show r.toNat + o.toNat + j = (r + o).toNat + j by rw [e5]]
    refine hrd4 j hj w ?_
    have := L.Arena.erecP_lt64 hw
    have e : (c + o + UInt64.ofNat j).toNat = c.toNat + o.toNat + j := by
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat']; omega
    rw [e]; exact hw

/-- The four words of a decoded constant value exist. -/
theorem decCV_def {R : Nat → Option Word} {q : Nat} {cv : IConstantVal} (h : decCV R q = some cv) :
    ∀ j < 4, ∃ w, R (q + j) = some w := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  -- the value's four words in order: the offsets as numbers (`rec_unfold`)
  simp only [rec_unfold, UInt64.reduceToNat] at h
  obtain ⟨nm, hn, ps, hp, t, ht, -⟩ := h
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff, nat?, Option.map_eq_some_iff] at hp
  obtain ⟨o, ⟨w1, hw1, -⟩, l, ⟨w2, hw2, -⟩, -⟩ := hp
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hn ht
  obtain ⟨w0, hw0, -⟩ := hn
  obtain ⟨w3, hw3, -⟩ := ht
  intro j hj
  match j, hj with
  | 0, _ => exact ⟨w0, hw0⟩
  | 1, _ => exact ⟨w1, hw1⟩
  | 2, _ => exact ⟨w2, by rw [show q + 2 = q + 1 + 1 by omega]; exact hw2⟩
  | 3, _ => exact ⟨w3, hw3⟩

/-- **`CiPre` across a step that writes the record pool only above the current top** (`er_to_iw`,
`param_levels`, `inst_lp`, `erec_alloc`, the rules). -/
theorem CiPre.step {m m3 m' : Mem} {a3 a' : AState} {r nn k : Word} {cv' : IConstantVal}
    (hpre : CiPre dn vis fe m m3 a3 r nn k cv') (hT : StageT dn vis fe m' a') (hg : IWGrow m3 m')
    (hf : MemFrame quotA quotC m3 m') :
    CiPre dn vis fe m m' a' r nn k cv' := by
  have htop : erTopOf m3 r ≤ erTopOf m' r := by
    unfold erTopOf; split
    · exact hg.er
    · exact hg.er1
  have hcap := (hT.stage.iw.topOf r)
  have hcv3 := hpre.cvR m3 (fun _ _ => rfl) hpre.grow.ext
  refine ⟨hT, hpre.grow.trans hg, hpre.fr.trans hf, hpre.base, by have := hpre.top; omega,
    by omega, hpre.r41, hg.ext _ _ hpre.kw, fun Y hY hE => hpre.cvR Y ?_ hE⟩
  intro j hj
  obtain ⟨w, hw⟩ := decCV_def hcv3 j hj
  rw [hY j hj, hg.ext _ _ hw, hw]

/-- **`CiPre` across a word written at `r + j`** (`5 ≤ j < nn`), the twin unchanged. -/
theorem CiPre.put {m m3 : Mem} {a a3 : AState} {r nn k v : Word} {cv' : IConstantVal}
    (hT : StageT dn vis fe m a) (hpre : CiPre dn vis fe m m3 a3 r nn k cv') {o : Word}
    (ho : 5 ≤ o.toNat) (hon : o.toNat < nn.toNat) :
    CiPre dn vis fe m (erecPutMem m3 (r + o) v) a3 r nn k cv' ∧
      erecP (erecPutMem m3 (r + o) v) (r.toNat + o.toNat) = some v ∧
      ∀ i, i % 2 ^ 41 ≠ (r.toNat + o.toNat) % 2 ^ 41 →
        erecP (erecPutMem m3 (r + o) v) i = erecP m3 i := by
  have hcap := hpre.cap
  have htop := hpre.top
  have hbase := hpre.base
  have hr41 := hpre.r41
  obtain ⟨eo, eoo, eto⟩ := erAddr (r := r) (c := o) (by omega) hr41
  have hq : erOff r + nn.toNat < 2 ^ 40 := by omega
  unfold erOff at hq
  obtain ⟨hS, hg, hf⟩ := StageR.putFresh hT.stage hpre.stT.stage hpre.fr hpre.grow (v := v)
    (d := r + o) (by rw [eto, eoo]; omega)
  have hT' := StageT.of_wrER (ws := [v]) hpre.stT hS
  have et : ∀ x, erTopOf (erecPutMem m3 (r + o) v) x = erTopOf m3 x := fun x => by
    simp only [erTopOf, erTop, erecTop1, erecPutMem_ctl]
  have hsz := hpre.stT.stage.iw.topOf (r + o)
  have hoth : ∀ i, i % 2 ^ 41 ≠ (r.toNat + o.toNat) % 2 ^ 41 →
      erecP (erecPutMem m3 (r + o) v) i = erecP m3 i := fun i hi =>
    erecP_putMem_other (by rw [eo]; exact hi)
  refine ⟨⟨hT', hg, hf, hbase, by rw [et]; exact htop, by rw [et]; exact hcap, hr41, ?_, ?_⟩, ?_,
    hoth⟩
  · rw [hoth _ (by omega)]; exact hpre.kw
  · intro Y hY hE
    refine hpre.cvR Y (fun j hj => ?_) hE
    rw [hY j hj, hoth _ (by omega)]
  · have h1 := hsz.1
    rw [eto] at h1
    rw [← eo]; exact erecP_putMem_self (by rw [eoo, eto]; omega) (by rw [eoo]; omega)

/-- **A copied tail** (`er_copy_er(r + o, c + o, l)`, `5 ≤ o`) after the record's head: `CiPre`
after it, the source words at the copy, every other address as before. -/
theorem ciCopyO {p : Prog} (hP : CiProg p) {n : Nat} {m m3 m4 : Mem} {a a3 : AState}
    {r nn k c o l : Word} {cv' : IConstantVal} {r4 : List Word} (hT : StageT dn vis fe m a)
    (hpre : CiPre dn vis fe m m3 a3 r nn k cv') (ho : 5 ≤ o.toNat)
    (hl : o.toNat + l.toNat ≤ nn.toNat)
    (h : callW p n "er_copy_er" [r + o, c + o, l] m3 = some (r4, m4)) :
    CiPre dn vis fe m m4 a3 r nn k cv' ∧
      (∀ j < l.toNat, WAt (erecP m) (erecP m4) (c.toNat + o.toNat + j) (r.toNat + o.toNat + j)) ∧
      ∀ i, (∀ j < l.toNat, i % 2 ^ 41 ≠ (r.toNat + o.toNat + j) % 2 ^ 41) → erecP m4 i = erecP m3 i := by
  have hcap := hpre.cap
  have htop := hpre.top
  have hbase := hpre.base
  have hr41 := hpre.r41
  obtain ⟨eo, eoo, eto⟩ := erAddr (r := r) (c := o) (by omega) hr41
  have hq : erOff r + nn.toNat < 2 ^ 40 := by omega
  unfold erOff at hq
  obtain ⟨hS4, hg4, hf4, hrd4, hout4, ws, rfl⟩ := erCopyEr_fresh hP.erCopyEr hP.erPut hT.stage
    hpre.stT.stage hpre.fr hpre.grow (by rw [eto, eoo]; omega) (by rw [eto, eoo]; omega)
    (by rw [eo]; omega) h
  have hT4 := StageT.of_wrER hpre.stT hS4
  have hoth : ∀ i, i < 5 → erecP (wrER m3 (r + o) ws) (r.toNat + i) = erecP m3 (r.toNat + i) :=
    fun i hi => hout4 _ fun j hj => by rw [eo]; omega
  have et : ∀ x, erTopOf (wrER m3 (r + o) ws) x = erTopOf m3 x := fun x => by
    simp only [erTopOf, erTop, erecTop1, wrER_ctl]
  refine ⟨⟨hT4, hg4, hf4, hbase, by rw [et]; exact htop, by rw [et]; exact hcap, hr41,
    by simpa using (hoth 0 (by omega)).trans (by simpa using hpre.kw), ?_⟩, ?_,
    fun i hi => hout4 i (by rw [eo]; exact hi)⟩
  · intro Y hY hE
    refine hpre.cvR Y (fun j hj => ?_) hE
    rw [hY j hj]
    have := hoth (1 + j) (by omega); rwa [← Nat.add_assoc] at this
  · intro j hj w hw
    rw [show r.toNat + o.toNat + j = (r + o).toNat + j by rw [eo]]
    refine hrd4 j hj w ?_
    have := L.Arena.erecP_lt64 hw
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat']
    rw [show (c.toNat + o.toNat) % 2 ^ 64 + j % 2 ^ 64 = c.toNat + o.toNat + j by omega,
      Nat.mod_eq_of_lt this]; exact hw

/-- **`er_to_iw(po, pl)`, then `param_levels`** under `StageT`, the name slice `(po, pl)` decoded:
the twin's `paramLevels`, `StageT` after, the record pool's words unchanged. -/
theorem plStep {p : Prog} (hP : QuotAtProg p) {n : Nat} {m m4 m5 : Mem} {a : AState}
    {po pl : Word} {r4 r5 : List Word} {ps : List NIdx} {psv : List ConLeche.Name}
    (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a)
    (hps : hslice? (erecP m) po.toNat pl.toNat = some ps)
    (hden : ConRon.Arena.Frontend.denoteNList a.store.ns ps = some psv)
    (h1 : callW p n "er_to_iw" [po, pl] m = some (r4, m4))
    (h2 : callW p n "param_levels" [r4.headD 0, r4.tail.headD 0] m4 = some (r5, m5)) :
    ∃ us a5, (paramLevels ps).run a = .ok (us, a5) ∧ StageT dn vis fe m5 a5 ∧ IWGrow m m5 ∧
      MemFrame quotA quotC m m5 ∧ erecP m5 = erecP m ∧ erRd m5 = erRd m ∧
      H (r5.headD 0) ∧ decI (r5.headD 0) = us ∧ ConRon.Bridge.Frontend.IStepS a a5 ∧
      denoteLs a5.store.lss us = some (psv.map ConLeche.Level.param) := by
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erToIw_specW p hP.iwAlloc hP.erCopy hP.erToIw n _ po pl) h1
  obtain ⟨hS1, hg1, hdl1, htop1, -⟩ := erToIwW_stage hW1 hT.stage hps
  have hT1 := StageT.of_iw hT hS1 (erToIwW_iwFr hW1)
  rw [hs1] at hS1 hg1 hdl1 htop1 hT1
  obtain ⟨hpf1, he1⟩ := callW_plFrame hP.plc (by decide) h1
  have hqf1 := callW_quotFrame hP.quot (by decide) h1
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (plW_spec p hP.iwAlloc hP.iwCopy hP.slCons hP.slGet hP.paramFind hP.paramPush hP.internParam
      hP.plGo hP.pl hP.il n _ _ _) h2
  rw [hs2] at hW2
  obtain ⟨us, a1, hrun1, hH, hus, hS2, hg2⟩ := plW_sim (k := n) hS1 hdl1 (by omega) r5 m5 hW2
  obtain ⟨hpf2, he2⟩ := callW_plFrame hP.plc (by decide) h2
  have hqf2 := callW_quotFrame hP.quot (by decide) h2
  obtain ⟨hst1, hls1⟩ := ConRon.Bridge.paramLevels_run hok hden hrun1
  have hT2 : StageT dn vis fe m5 a1 := StageT.of_pl hT1 hS2 hst1 hpf2
  have hpf12 := hpf1.trans hpf2
  have hr2 := erRd_congr (m := m) (m' := m5) (hpf12.arr _ (plA_not (by simp [plBad])) (by decide))
    (hpf12.arr _ (plA_not (by simp [plBad])) (by decide))
  refine ⟨us, a1, hrun1, hT2, hg1.trans hg2, hqf1.trans hqf2, by rw [he2, he1], funext hr2, hH,
    hus, hst1, hls1⟩

/-- **`inst_lp(ko, kc, us, x)`** under `StageT` (through `CoreS`): the twin's `instLPFast`,
`StageT` after, the record pool unchanged. -/
theorem instStep {p : Prog} (hP : QuotAtProg p) {n : Nat} {m m' : Mem} {a : AState}
    {ko kc us x : Word} {r : List Word} {lps : List NIdx}
    (hT : StageT dn vis fe m a) (hH : H us) (hx : x.toNat < 2 ^ 32)
    (hl : hslice? (erecP m) ko.toNat kc.toNat = some lps)
    (h : callW p n "inst_lp" [ko, kc, us, x] m = some (r, m')) :
    ∃ e a', (instLPFast coreWalkFuel lps (decI us) (decE x)).run a = .ok (e, a') ∧
      StageT dn vis fe m' a' ∧ IWGrow m m' ∧ MemFrame quotA quotC m m' ∧ erecP m' = erecP m ∧
      erRd m' = erRd m ∧ decH r = e ∧ (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨M, hC⟩ := hT.core
  obtain ⟨s3, rfl, -, hok3, ⟨M', hC', -, -⟩, hres3, hrh3⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (hP.instLP n ⟨m, Locals.init []⟩ a dn vis fe M 0 _ _ us _ lps hC hx hH hl) h
  obtain ⟨hT3, hg3⟩ := StageT.of_core hP.core instLp_stageCore h hT hC'
  obtain ⟨hE3, hE13, hrd3, he3⟩ := callW_erec_closedT hP.coreErec instLp_core h
  have hqf3 := callW_quotFrame hP.quot (by decide) h
  have hrun3 := L.Arena.AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  exact ⟨_, _, hrun3, hT3, hg3, hqf3, he3, hrd3, rfl, hrh3⟩

/-- Two memories' record pools agree above the base `m₀`'s tops. -/
def AgreeAbove (m₀ M Y : Mem) : Prop :=
  ∀ a : Word, erTopOf m₀ a ≤ erOff a → erecP Y a.toNat = erecP M a.toNat

theorem agreeAbove_put {m₀ X : Mem} {b v : Word} (hb : erOff b < erTopOf m₀ b) :
    AgreeAbove m₀ X (erecPutMem X b v) := by
  intro a ha
  refine erecP_putMem_other fun e => ?_
  have h1 : a.toNat / 2 ^ 40 % 2 = b.toNat / 2 ^ 40 % 2 := by omega
  have h2 : erOff a = erOff b := by unfold erOff; omega
  have h3 : erTopOf m₀ a = erTopOf m₀ b := by simp only [erTopOf, h1]
  omega

theorem agreeAbove_of_out {m₀ X Y : Mem} {b : Word} {bt : Nat} (hb : erOff b < erTopOf m₀ b)
    (hbt : b.toNat = bt) (hout : ∀ i, i % 2 ^ 41 ≠ bt % 2 ^ 41 → erecP Y i = erecP X i) :
    AgreeAbove m₀ X Y := by
  intro a ha
  refine hout _ fun e => ?_
  subst hbt
  have h1 : a.toNat / 2 ^ 40 % 2 = b.toNat / 2 ^ 40 % 2 := by omega
  have h2 : erOff a = erOff b := by unfold erOff; omega
  have h3 : erTopOf m₀ a = erTopOf m₀ b := by simp only [erTopOf, h1]
  omega

theorem AgreeAbove.trans {m₀ X Y Z : Mem} (h1 : AgreeAbove m₀ X Y) (h2 : AgreeAbove m₀ Y Z) :
    AgreeAbove m₀ X Z := fun a ha => (h2 a ha).trans (h1 a ha)

theorem AgreeAbove.refl (m₀ X : Mem) : AgreeAbove m₀ X X := fun _ _ => rfl

/-- **A recursor's rules at new names** (`rules_at_lps_go(ko, kc, us, o, rl, d)`) under `StageT`:
the twin's two name readbacks and `rulesAtLps`, the fresh rules at `d` (above the base `m₀`'s
top, allocated in `m`), decoded in every later reader that extends the rules' origin `m₁` and
agrees above `m₀`. Open: each rule's right-hand side by `inst_lp`, a `.levels` fire by
`fire_levels_at` (`ls_node`, `keys_push`, `sle_go` under `CoreS`, `erec_alloc`, `spn_to_er`). -/
structure RulesAtSim (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop where
  go : ∀ (n : Nat) (vis : Word) (fe : IFEnv) (m₁ m₀ m : Mem) (a₀ a : AState)
    (ko kc us o rl d : Word) (lpsH ps : List NIdx) (rules : List IRecRule)
    (Rs : List ConLeche.RecRule) (lpsT psv : List ConLeche.Name),
    StageR vis fe m₀ a₀ → StageT dn vis fe m a → ConRon.Bridge.StateOK a →
    ConRon.Bridge.ReadOK a → IWGrow m₁ m₀ → MemFrame quotA quotC m₀ m → IWGrow m₀ m →
    erTopOf m₀ d ≤ erOff d → erOff d + 11 * rl.toNat ≤ erTopOf m d → d.toNat < 2 ^ 41 →
    hslice? (erecP m₀) ko.toNat kc.toNat = some lpsH → H us →
    ConRon.Arena.Frontend.denoteNList a.store.ns lpsH = some lpsT →
    ConRon.Arena.Frontend.denoteNList a.store.ns ps = some psv →
    denoteLs a.store.lss (decI us) = some (psv.map ConLeche.Level.param) →
    decRules (erecP m₁) o.toNat rl.toNat = some rules →
    ConRon.Arena.Frontend.denoteRules a.store rules = some Rs →
    Sim (callW p n "rules_at_lps_go" [ko, kc, us, o, rl, d] m)
      (do
        let lpsT ← readNamesM lpsH
        let psT ← readNamesM ps
        rulesAtLps lpsH (decI us) lpsT (psT.map ConLeche.Level.param) rules) a
      (fun _ rs' m' a' => StageT dn vis fe m' a' ∧ IWGrow m₀ m' ∧ MemFrame quotA quotC m₀ m' ∧
        ∀ Y : Mem, ArrExt (erecP m₁) (erecP Y) → AgreeAbove m₀ m' Y →
          decRules (erecP Y) d.toNat rl.toNat = some rs')

/-- **`ci_at_lps(c, po, pl)` refines `ci.atLps ps`** under `StageT`: the fresh record after it. -/
theorem ciAtLps_sim {p : Prog} (hP : CiProg p) (hR : RulesAtSim p dn) (n : Nat) {m : Mem} {a : AState} {c po pl : Word}
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
  try simp only [rec_unfold, UInt64.reduceAdd] at hW
  -- the kind word
  have hk0 : ∃ w, erecP m c.toNat = some w := by
    cases e : erecP m c.toNat with
    | none => simp [decCI, nat?, e] at hci
    | some w => exact ⟨w, rfl⟩
  obtain ⟨w, hw⟩ := hk0
  have ew : erRd m c = w := erRd_of _ _ hw
  simp only [show rdW (m.arr64 (tierA EREC (c >>> 40))) (c &&& 1099511627775) = erRd m c from rfl,
    ew] at hW
  have hcv := decCI_cv hci
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
    · simp only [List.headD_cons, decCI, rec_unfold, UInt64.reduceToNat, nat?, hpre.kw, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hpre.cvR _ (fun _ _ => rfl) hpre.grow.ext]
      rfl
  | defnInfo cv v hint =>
    obtain rfl : w = 1 := UInt64.toNat_inj.mp hkd
    have hci' := hci
    simp only [decCI, rec_unfold, UInt64.reduceToNat, nat?, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      show (1 : Word).toNat = 1 from rfl, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, IConstantInfo.defnInfo.injEq] at hci'
    obtain ⟨cv0, -, v0, hv0, hint0, hhint, -, rfl, rfl⟩ := hci'
    obtain ⟨cvd, xd, -, hcvd, -⟩ := ConRon.Bridge.denoteCI_defn_inv hdc
    simp (config := { decide := true }) only [↓reduceIte] at hW
    obtain ⟨r1, m1, r2, m2, r3, m3, h1, h2, h3, hW⟩ := ciJ1_inv hW
    simp (config := { decide := true }) only [ciAtLpsW.k_cv_at_lps, ↓reduceIte] at hW
    try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
    obtain ⟨cv', a3, hrun, hpre⟩ := ciPre_of hP.toQuotAtProg n hT hok hci hps hden (by decide) h1 h2 h3
    obtain ⟨hst3, -⟩ := ConRon.Bridge.IConstantVal.atLps_run hok hr hcvd hden hrun
    -- `er_to_iw`, `param_levels`
    cases h4 : callW p n "er_to_iw" [po, pl] m3 with
    | none => rw [h4] at hW; simp [ciAtLpsW.k_er_to_iw] at hW
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4] at hW; simp only [ciAtLpsW.k_er_to_iw] at hW
    try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
    cases h5 : callW p n "param_levels" [r4.headD 0, r4.tail.headD 0] m4 with
    | none => rw [h5] at hW; simp [ciAtLpsW.k_param_levels] at hW
    | some x5 =>
    obtain ⟨r5, m5⟩ := x5
    rw [h5] at hW; simp only [ciAtLpsW.k_param_levels] at hW
    try simp only [rec_unfold, UInt64.reduceAdd] at hW
    have hden3 := ConRon.Bridge.denoteNListE_ext hst3.ext _ _ hden
    obtain ⟨us, a5, hrun5, hT5, hg5, hf5, he5, hrd5, hH5, hus5, hst5, -⟩ :=
      plStep hP.toQuotAtProg hpre.stT hst3.ok (ArrExt.hslice? hpre.grow.ext hps) hden3 h4 h5
    have hpre5 := hpre.step hT5 hg5 hf5
    -- `inst_lp`
    have hcv5 : decCV (erecP m5) (c.toNat + 1) = some cv :=
      ArrExt.decCV hpre5.grow.ext (decCI_cv hci)
    obtain ⟨-, -, hlps, -⟩ := decCV_rd_ci (erRdOK m5) hcv5
    obtain ⟨wv, hwv, hwv32, rfl⟩ : ∃ wv, erecP m (c.toNat + 5) = some wv ∧ wv.toNat < 2 ^ 32 ∧
        decI wv = v0 := by
      simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv0
      obtain ⟨wv, hwv, h32⟩ := hv0
      split at h32
      · exact ⟨wv, hwv, by assumption, Option.some.inj h32⟩
      · cases h32
    have ev : erRd m5 (c + 5) = wv := erRd_of _ _ (by
      have := L.Arena.erecP_lt64 hwv
      have h5 : (5 : Word).toNat = 5 := rfl
      rw [UInt64.toNat_add, h5, Nat.mod_eq_of_lt (by omega)]; exact hpre5.grow.ext _ _ hwv)
    simp only [erRd_foldN, ev] at hW
    cases h6 : callW p n "inst_lp" [erRd m5 (c + 2), erRd m5 (c + 3), r5.headD 0, wv] m5 with
    | none => rw [h6] at hW; simp [ciAtLpsW.k_inst_lp] at hW
    | some x6 =>
    obtain ⟨r6, m6⟩ := x6
    rw [h6] at hW; simp only [ciAtLpsW.k_inst_lp] at hW
    try simp only [rec_unfold] at hW
    obtain ⟨e6, a6, hrun6, hT6, hg6, hf6, he6, -, hdec6, h32⟩ :=
      instStep hP.toQuotAtProg hT5 hH5 hwv32 hlps h6
    have hpre6 := hpre5.step hT6 hg6 hf6
    -- `erec_put(r + 5, v)`, `er_copy_er(r + 6, c + 6, 2)`
    cases h7 : callW p n "erec_put" [r1.headD 0 + 5, r6.headD 0] m6 with
    | none => rw [h7] at hW; simp [ciAtLpsW.k_erec_put_2] at hW
    | some x7 =>
    obtain ⟨r7, m7⟩ := x7
    rw [h7] at hW; simp only [ciAtLpsW.k_erec_put_2] at hW
    try simp only [rec_unfold] at hW
    rw [callW_erecPut hP.erPut h7] at hW
    obtain ⟨hpre7, hv7, hout7⟩ := hpre6.put (o := 5) (v := r6.headD 0) hT (by decide) (by decide)
    cases h8 : callW p n "er_copy_er" [r1.headD 0 + 6, c + 6, 2]
        (erecPutMem m6 (r1.headD 0 + 5) (r6.headD 0)) with
    | none => rw [h8] at hW; simp [ciAtLpsW.k_er_copy_er] at hW
    | some x8 =>
    obtain ⟨r8, m8⟩ := x8
    rw [h8] at hW
    simp only [ciAtLpsW.k_er_copy_er, Option.some.injEq, Prod.mk.injEq] at hW
    try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨hpre8, hc8, hout8⟩ := ciCopyO hP hT hpre7 (o := 6) (l := 2) (by decide) (by decide) h8
    refine ⟨.defnInfo cv' e6 hint0, a6, ?_, hpre8.stT, hpre8.grow, ?_⟩
    · simp only [IConstantInfo.atLps, StateT.run_bind]
      rw [show (cv.atLps ps).run a = .ok (cv', a3) from hrun]
      simp only [L.Arena.except_ok_bind]
      rw [show (paramLevels ps).run a3 = .ok (us, a5) from hrun5]
      simp only [L.Arena.except_ok_bind]
      rw [← hus5, ← decE_eq, hrun6]; rfl
    · have h6 : (6 : Word).toNat = 6 := rfl
      have h5 : (5 : Word).toNat = 5 := rfl
      have h2 : (2 : Word).toNat = 2 := rfl
      simp only [h6, h2] at hc8 hout8
      simp only [h5] at hv7
      have hr41 := hpre8.r41
      have e5 : erecP s'.mem ((r1.headD 0).toNat + 5) = some (r6.headD 0) := by
        rw [hout8 _ (fun j hj => by omega)]; exact hv7
      have hd5 : (hd? (erecP s'.mem) ((r1.headD 0).toNat + 5) : Option EIdx) = some e6 := by
        simp only [hd?, e5, Option.bind_eq_bind, Option.bind_some, h32, ↓reduceIte, ← hdec6, decH,
          decE_eq]
      have hh : decHint (erecP s'.mem) ((r1.headD 0).toNat + 6) = some hint0 :=
        decHint_sh (by simpa using hc8 0 (by decide)) (hc8 1 (by decide)) hhint
      simp only [List.headD_cons, decCI, rec_unfold, UInt64.reduceToNat, nat?, hpre8.kw, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hpre8.cvR _ (fun _ _ => rfl) hpre8.grow.ext,
        show (1 : Word).toNat = 1 from rfl, hd5, hh]
      rfl
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
    · simp only [List.headD_cons, decCI, rec_unfold, UInt64.reduceToNat, nat?, hpre.kw, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hpre.cvR _ (fun _ _ => rfl) hpre.grow.ext]
      rfl
  | indInfo cv caps =>
    obtain rfl : w = 3 := UInt64.toNat_inj.mp hkd
    have hci' := hci
    simp only [decCI, rec_unfold, UInt64.reduceToNat, nat?, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      show (3 : Word).toNat = 3 from rfl, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, IConstantInfo.indInfo.injEq] at hci'
    obtain ⟨cv0, -, caps0, hcaps, -, rfl⟩ := hci'
    simp (config := { decide := true }) only [↓reduceIte] at hW
    obtain ⟨r1, m1, r2, m2, r3, m3, h1, h2, h3, hW⟩ := ciJ1_inv hW
    simp (config := { decide := true }) only [ciAtLpsW.k_cv_at_lps, ↓reduceIte] at hW
    try simp only [rec_unfold] at hW
    cases h4 : callW p n "er_copy_er" [r1.headD 0 + 5, c + 5, 8] m3 with
    | none => rw [h4] at hW; simp [ciAtLpsW.k_er_copy_er] at hW
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4] at hW
    simp only [ciAtLpsW.k_er_copy_er, Option.some.injEq, Prod.mk.injEq] at hW
    try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨cv', a3, hrun, hpre⟩ := ciPre_of hP.toQuotAtProg n hT hok hci hps hden (by decide) h1 h2 h3
    obtain ⟨hT4, hg4, hk4, hcv4, hc4⟩ := ciCopy hP hT hpre (o := CI.indCaps) (l := Caps.size) CI.indCaps_ge
      (by first | decide | exact Nat.le_of_eq CI.indSize_toNat.symm) h4
    refine ⟨.indInfo cv' caps0, a3, ?_, hT4, hg4, ?_⟩
    · simp only [IConstantInfo.atLps, StateT.run_bind]
      rw [show (cv.atLps ps).run a = .ok (cv', a3) from hrun]; rfl
    · have hc := decCaps_congr (fun j hj => hc4 j hj) hg4.ext hcaps
      simp only [rec_unfold, UInt64.reduceToNat] at hc
      simp only [List.headD_cons, decCI, rec_unfold, UInt64.reduceToNat, nat?, hk4, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hcv4, show (3 : Word).toNat = 3 from rfl, hc]
      rfl
  | ctorInfo cv np nf fam =>
    obtain rfl : w = 4 := UInt64.toNat_inj.mp hkd
    have hci' := hci
    simp only [decCI, rec_unfold, UInt64.reduceToNat, nat?, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      show (4 : Word).toNat = 4 from rfl, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, IConstantInfo.ctorInfo.injEq, Option.map_eq_some_iff] at hci'
    obtain ⟨cv0, -, x5, ⟨w5, hw5, rfl⟩, x6, ⟨w6, hw6, rfl⟩, f7, hf7, -, rfl, rfl, rfl⟩ := hci'
    obtain ⟨w7, hw7, hw7l, rfl⟩ := hd?_some hf7
    simp (config := { decide := true }) only [↓reduceIte] at hW
    obtain ⟨r1, m1, r2, m2, r3, m3, h1, h2, h3, hW⟩ := ciJ1_inv hW
    simp (config := { decide := true }) only [ciAtLpsW.k_cv_at_lps, ↓reduceIte] at hW
    try simp only [rec_unfold, UInt64.reduceSub] at hW
    cases h4 : callW p n "er_copy_er" [r1.headD 0 + 5, c + 5, 3] m3 with
    | none => rw [h4] at hW; simp [ciAtLpsW.k_er_copy_er] at hW
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4] at hW
    simp only [ciAtLpsW.k_er_copy_er, Option.some.injEq, Prod.mk.injEq] at hW
    try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨cv', a3, hrun, hpre⟩ := ciPre_of hP.toQuotAtProg n hT hok hci hps hden (by decide) h1 h2 h3
    obtain ⟨hT4, hg4, hk4, hcv4, hc4⟩ := ciCopy hP hT hpre (o := 5) (l := 3) (by decide) (by decide) h4
    simp only [UInt64.reduceToNat] at hc4
    refine ⟨.ctorInfo cv' w5.toNat w6.toNat (decI w7), a3, ?_, hT4, hg4, ?_⟩
    · simp only [IConstantInfo.atLps, StateT.run_bind]
      rw [show (cv.atLps ps).run a = .ok (cv', a3) from hrun]; rfl
    · have e5 := hc4 0 (by decide) w5 (by simpa using hw5)
      have e6 := hc4 1 (by decide) w6 hw6
      have e7 := hc4 2 (by decide) w7 (by simpa [Nat.add_assoc] using hw7)
      simp only [Nat.add_zero] at e5
      rw [show (r1.headD 0).toNat + 5 + 1 = (r1.headD 0).toNat + 6 by omega] at e6
      rw [show (r1.headD 0).toNat + 5 + 2 = (r1.headD 0).toNat + 7 by omega] at e7
      simp only [List.headD_cons, decCI, rec_unfold, UInt64.reduceToNat, nat?, hd?, hk4, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hcv4, show (4 : Word).toNat = 4 from rfl, e5, e6, e7, hw7l, ite_true]
      rfl
  | recInfo cv mI rP isK rules =>
    obtain rfl : w = 5 := UInt64.toNat_inj.mp hkd
    have hci' := hci
    simp only [decCI, rec_unfold, UInt64.reduceToNat, nat?, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      show (5 : Word).toNat = 5 from rfl, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, IConstantInfo.recInfo.injEq, Option.map_eq_some_iff, bool?] at hci'
    obtain ⟨cv0, -, x5, ⟨w5, hw5, rfl⟩, x6, ⟨w6, hw6, rfl⟩, x9, ⟨w9, hw9, rfl⟩, x7, ⟨w7, hw7, rfl⟩,
      x8, ⟨w8, hw8, rfl⟩, rs0, hrs, -, rfl, rfl, rfl, rfl⟩ := hci'
    obtain ⟨cvd, Rsd, -, hcvd, hRsd⟩ := ConRon.Bridge.denoteCI_rec_inv hdc
    simp (config := { decide := true }) only [↓reduceIte] at hW
    obtain ⟨r1, m1, r2, m2, r3, m3, h1, h2, h3, hW⟩ := ciJ1_inv hW
    simp (config := { decide := true }) only [ciAtLpsW.k_cv_at_lps, ↓reduceIte] at hW
    try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
    obtain ⟨cv', a3, hrun, hpre⟩ := ciPre_of hP.toQuotAtProg n hT hok hci hps hden (by decide) h1 h2 h3
    obtain ⟨hst3, -⟩ := ConRon.Bridge.IConstantVal.atLps_run hok hr hcvd hden hrun
    -- `er_to_iw`, `param_levels`
    cases h4 : callW p n "er_to_iw" [po, pl] m3 with
    | none => rw [h4] at hW; simp [ciAtLpsW.k_er_to_iw_2] at hW
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4] at hW; simp only [ciAtLpsW.k_er_to_iw_2] at hW
    try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
    cases h5 : callW p n "param_levels" [r4.headD 0, r4.tail.headD 0] m4 with
    | none => rw [h5] at hW; simp [ciAtLpsW.k_param_levels_2] at hW
    | some x5 =>
    obtain ⟨r5, m5⟩ := x5
    rw [h5] at hW; simp only [ciAtLpsW.k_param_levels_2] at hW
    try simp only [rec_unfold] at hW
    have hden3 := ConRon.Bridge.denoteNListE_ext hst3.ext _ _ hden
    obtain ⟨us, a5, hrun5, hT5, hg5, hf5, he5, hrd5, hH5, hus5, hst5, hls5⟩ :=
      plStep hP.toQuotAtProg hpre.stT hst3.ok (ArrExt.hslice? hpre.grow.ext hps) hden3 h4 h5
    have hpre5 := hpre.step hT5 hg5 hf5
    -- the source words
    have hsrc : ∀ (X : Mem), IWGrow m X → ∀ (j : Nat) (wj : Word), erecP m (c.toNat + j) = some wj →
        erRd X (c + UInt64.ofNat j) = wj := fun X hX j wj hj => by
      have := L.Arena.erecP_lt64 hj
      exact erRd_of _ _ (by rw [L.toNat_add_ofNat_of_lt _ _ (by omega)]; exact hX.ext _ _ hj)
    have rd : ∀ x : Word, rdW (m5.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) = erRd m5 x :=
      fun _ => rfl
    simp only [rd, show c + 8 = c + UInt64.ofNat 8 from rfl, hsrc m5 hpre5.grow 8 w8 hw8] at hW
    by_cases hbig : (1152921504606846976 : Word) ≤ w8
    · simp [hbig] at hW
    simp only [hbig, ↓reduceIte] at hW
    have hw8l : w8.toNat < 2 ^ 60 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hbig); simpa using this
    have h11 : (11 * w8).toNat = 11 * w8.toNat := by
      rw [UInt64.toNat_mul]; simp only [show (11 : Word).toNat = 11 from rfl]; omega
    -- `erec_alloc(11 * rl)`
    cases h6 : callW p n "erec_alloc" [11 * w8] m5 with
    | none => rw [h6] at hW; simp [ciAtLpsW.k_erec_alloc_2] at hW
    | some x6 =>
    obtain ⟨r6, m6⟩ := x6
    rw [h6] at hW; simp only [ciAtLpsW.k_erec_alloc_2] at hW
    try simp only [rec_unfold, UInt64.reduceAdd] at hW
    obtain ⟨hT6, hg6, hoff6, htop6, hro41⟩ := erAlloc_stageT (callW_erecAlloc hP.erAlloc h6) hpre5.stT
    have hqf6 := callW_quotFrame hP.quot (by decide) h6
    have rd6 : ∀ x : Word, rdW (m6.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) = erRd m6 x :=
      fun _ => rfl
    have hcv5 : decCV (erecP m5) (c.toNat + 1) = some cv := ArrExt.decCV hpre5.grow.ext (decCI_cv hci)
    obtain ⟨-, -, hlps6, -⟩ := decCV_rd_ci (R := erecP m5) (rd := erRd m6)
      ⟨fun a v h => erRd_of _ _ (hg6.ext _ _ h), fun _ _ h => L.Arena.erecP_lt64 h⟩ hcv5
    simp only [rd6, show c + 7 = c + UInt64.ofNat 7 from rfl,
      hsrc m6 (hpre5.grow.trans hg6) 7 w7 hw7] at hW
    -- `rules_at_lps_go`
    cases h7 : callW p n "rules_at_lps_go" [erRd m6 (c + 2), erRd m6 (c + 3), r5.headD 0, w7, w8,
        r6.headD 0] m6 with
    | none => rw [h7] at hW; simp [ciAtLpsW.k_rules_at_lps_go] at hW
    | some x7 =>
    obtain ⟨r7, m7⟩ := x7
    rw [h7] at hW; simp only [ciAtLpsW.k_rules_at_lps_go] at hW
    try simp only [rec_unfold] at hW
    have hcvd5 := ConRon.Bridge.denoteCV_ext hcvd (hst3.ext.trans hst5.ext)
    have hden5 := ConRon.Bridge.denoteNListE_ext hst5.ext _ _ hden3
    have hr5 := (ConRon.Bridge.RStep.of_istep hst5 hst3.read).read
    have hcap6 := hT6.stage.iw.topOf (r6.headD 0)
    obtain ⟨rs', a7, hrun7, hT7, hg7, hf7, hdec7⟩ := hR.go n vis fe m m5 m6 _ a5 _ _ _ _ _ _
      cv.levelParams ps rs0 Rsd _ psv hpre5.stT.stage hT6 hst5.ok hr5 hpre5.grow hqf6 hg6
      (by rw [hoff6]; exact Nat.le_refl _) (by rw [htop6, hoff6, h11]; exact Nat.le_refl _) hro41
      hlps6 hH5 (ConRon.Bridge.denoteCV_inv hcvd5).2.1 hden5 (by rw [hus5]; exact hls5) hrs
      (ConRon.Bridge.denoteRules_ext (hst3.ext.trans hst5.ext) _ _ hRsd) r7 m7 h7
    have hpre7 := hpre5.step hT7 hg7 hf7
    -- `erec_put(r + 5, …)`
    have rd8 : ∀ x : Word, rdW (m7.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) = erRd m7 x :=
      fun _ => rfl
    simp only [rd8] at hW
    simp only [show c + 5 = c + UInt64.ofNat 5 from rfl, hsrc m7 hpre7.grow 5 w5 hw5] at hW
    cases h8 : callW p n "erec_put" [r1.headD 0 + 5, w5] m7 with
    | none => rw [h8] at hW; simp [ciAtLpsW.k_erec_put_3] at hW
    | some x8 =>
    obtain ⟨r8, m8⟩ := x8
    rw [h8] at hW; simp only [ciAtLpsW.k_erec_put_3] at hW
    try simp only [rec_unfold] at hW
    rw [callW_erecPut hP.erPut h8] at hW
    obtain ⟨hpre8, hv8, hout8⟩ := hpre7.put (o := 5) (v := w5) hT (by decide) (by decide)
    generalize erecPutMem m7 (r1.headD 0 + 5) w5 = m8 at hpre8 hv8 hout8 hW ⊢
    -- `erec_put(r + 6, …)`
    have rd9 : ∀ x : Word, rdW (m8.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) = erRd m8 x :=
      fun _ => rfl
    simp only [rd9] at hW
    simp only [show c + 6 = c + UInt64.ofNat 6 from rfl, hsrc m8 hpre8.grow 6 w6 hw6] at hW
    cases h9 : callW p n "erec_put" [r1.headD 0 + 6, w6] m8 with
    | none => rw [h9] at hW; simp [ciAtLpsW.k_erec_put_4] at hW
    | some x9 =>
    obtain ⟨r9, m9⟩ := x9
    rw [h9] at hW; simp only [ciAtLpsW.k_erec_put_4] at hW
    try simp only [rec_unfold] at hW
    rw [callW_erecPut hP.erPut h9] at hW
    obtain ⟨hpre9, hv9, hout9⟩ := hpre8.put (o := 6) (v := w6) hT (by decide) (by decide)
    generalize erecPutMem m8 (r1.headD 0 + 6) w6 = m9 at hpre9 hv9 hout9 hW ⊢
    -- `erec_put(r + 7, …)`
    have rd10 : ∀ x : Word, rdW (m9.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) = erRd m9 x :=
      fun _ => rfl
    cases h10 : callW p n "erec_put" [r1.headD 0 + 7, r6.headD 0] m9 with
    | none => rw [h10] at hW; simp [ciAtLpsW.k_erec_put_5] at hW
    | some x10 =>
    obtain ⟨r10, m10⟩ := x10
    rw [h10] at hW; simp only [ciAtLpsW.k_erec_put_5] at hW
    try simp only [rec_unfold] at hW
    rw [callW_erecPut hP.erPut h10] at hW
    obtain ⟨hpre10, hv10, hout10⟩ := hpre9.put (o := 7) (v := r6.headD 0) hT (by decide) (by decide)
    generalize erecPutMem m9 (r1.headD 0 + 7) (r6.headD 0) = m10 at hpre10 hv10 hout10 hW ⊢
    -- `erec_put(r + 8, …)`
    have rd11 : ∀ x : Word, rdW (m10.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) = erRd m10 x :=
      fun _ => rfl
    cases h11 : callW p n "erec_put" [r1.headD 0 + 8, w8] m10 with
    | none => rw [h11] at hW; simp [ciAtLpsW.k_erec_put_6] at hW
    | some x11 =>
    obtain ⟨r11, m11⟩ := x11
    rw [h11] at hW; simp only [ciAtLpsW.k_erec_put_6] at hW
    try simp only [rec_unfold] at hW
    rw [callW_erecPut hP.erPut h11] at hW
    obtain ⟨hpre11, hv11, hout11⟩ := hpre10.put (o := 8) (v := w8) hT (by decide) (by decide)
    generalize erecPutMem m10 (r1.headD 0 + 8) w8 = m11 at hpre11 hv11 hout11 hW ⊢
    -- `erec_put(r + 9, …)`
    have rd12 : ∀ x : Word, rdW (m11.arr64 (tierA EREC (x >>> 40))) (x &&& 1099511627775) = erRd m11 x :=
      fun _ => rfl
    simp only [rd12] at hW
    simp only [show c + 9 = c + UInt64.ofNat 9 from rfl, hsrc m11 hpre11.grow 9 w9 hw9] at hW
    cases h12 : callW p n "erec_put" [r1.headD 0 + 9, w9] m11 with
    | none => rw [h12] at hW; simp [ciAtLpsW.k_er_copy_er] at hW
    | some x12 =>
    obtain ⟨r12, m12⟩ := x12
    rw [h12] at hW; simp only [ciAtLpsW.k_er_copy_er] at hW
    try simp only [rec_unfold, UInt64.reduceAdd, UInt64.reduceSub] at hW
    rw [callW_erecPut hP.erPut h12] at hW
    obtain ⟨hpre12, hv12, hout12⟩ := hpre11.put (o := 9) (v := w9) hT (by decide) (by decide)
    generalize erecPutMem m11 (r1.headD 0 + 9) w9 = m12 at hpre12 hv12 hout12 hW ⊢
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    simp only [show (5 : Word).toNat = 5 from rfl, show (6 : Word).toNat = 6 from rfl,
      show (7 : Word).toNat = 7 from rfl, show (8 : Word).toNat = 8 from rfl,
      show (9 : Word).toNat = 9 from rfl] at hv8 hv9 hv10 hv11 hv12 hout8 hout9 hout10 hout11 hout12
    have hr41 := hpre5.r41
    have htop5 := hpre5.top
    have hcap5 := hpre5.cap
    have hq : erOff (r1.headD 0) + 10 < 2 ^ 40 := by
      have : (10 : Word).toNat = 10 := rfl; omega
    have hb : ∀ o : Word, o.toNat < 10 → erOff (r1.headD 0 + o) < erTopOf m5 (r1.headD 0 + o) ∧
        (r1.headD 0 + o).toNat = (r1.headD 0).toNat + o.toNat := fun o ho => by
      obtain ⟨e1, e2, e3⟩ := erAddr (r := r1.headD 0) (c := o) (by omega) hr41
      refine ⟨by rw [e2, e3]; have : (10 : Word).toNat = 10 := rfl; omega, e1⟩
    have hag : AgreeAbove m5 m7 s'.mem :=
      ((((agreeAbove_of_out (hb 5 (by decide)).1 (by rw [(hb 5 (by decide)).2]; rfl) hout8).trans
        (agreeAbove_of_out (hb 6 (by decide)).1 (by rw [(hb 6 (by decide)).2]; rfl) hout9)).trans
        (agreeAbove_of_out (hb 7 (by decide)).1 (by rw [(hb 7 (by decide)).2]; rfl) hout10)).trans
        (agreeAbove_of_out (hb 8 (by decide)).1 (by rw [(hb 8 (by decide)).2]; rfl) hout11)).trans
        (agreeAbove_of_out (hb 9 (by decide)).1 (by rw [(hb 9 (by decide)).2]; rfl) hout12)
    have hrs12 := hdec7 s'.mem hpre12.grow.ext hag
    unfold erOff at hq
    have ne : ∀ i j : Nat, i < 10 → j < 10 → i ≠ j →
        ((r1.headD 0).toNat + i) % 2 ^ 41 ≠ ((r1.headD 0).toNat + j) % 2 ^ 41 := fun i j hi hj hij => by
      omega
    have e5 : erecP s'.mem ((r1.headD 0).toNat + 5) = some w5 := by
      rw [hout12 _ (ne 5 9 (by omega) (by omega) (by omega)), hout11 _ (ne 5 8 (by omega) (by omega) (by omega)),
        hout10 _ (ne 5 7 (by omega) (by omega) (by omega)), hout9 _ (ne 5 6 (by omega) (by omega) (by omega)), hv8]
    have e6 : erecP s'.mem ((r1.headD 0).toNat + 6) = some w6 := by
      rw [hout12 _ (ne 6 9 (by omega) (by omega) (by omega)), hout11 _ (ne 6 8 (by omega) (by omega) (by omega)),
        hout10 _ (ne 6 7 (by omega) (by omega) (by omega)), hv9]
    have e7 : erecP s'.mem ((r1.headD 0).toNat + 7) = some (r6.headD 0) := by
      rw [hout12 _ (ne 7 9 (by omega) (by omega) (by omega)), hout11 _ (ne 7 8 (by omega) (by omega) (by omega)),
        hv10]
    have e8 : erecP s'.mem ((r1.headD 0).toNat + 8) = some w8 := by
      rw [hout12 _ (ne 8 9 (by omega) (by omega) (by omega)), hv11]
    refine ⟨.recInfo cv' w5.toNat w6.toNat (w9 != 0) rs', a7, ?_, hpre12.stT, hpre12.grow, ?_⟩
    · rw [hus5] at hrun7
      have e : (IConstantInfo.recInfo cv w5.toNat w6.toNat (w9 != 0) rs0).atLps ps =
          (do
            let cv2 ← cv.atLps ps
            let us ← paramLevels ps
            let rs ← (do
              let lpsT ← readNamesM cv.levelParams
              let psT ← readNamesM ps
              rulesAtLps cv.levelParams us lpsT (psT.map ConLeche.Level.param) rs0)
            pure (IConstantInfo.recInfo cv2 w5.toNat w6.toNat (w9 != 0) rs)) := by
        simp only [IConstantInfo.atLps, bind_assoc]
      rw [e, StateT.run_bind, show (cv.atLps ps).run a = .ok (cv', a3) from hrun]
      simp only [L.Arena.except_ok_bind]
      rw [StateT.run_bind, show (paramLevels ps).run a3 = .ok (us, a5) from hrun5]
      simp only [L.Arena.except_ok_bind]
      rw [StateT.run_bind, hrun7]
      rfl
    · simp only [List.headD_cons, decCI, rec_unfold, UInt64.reduceToNat, nat?, hpre12.kw, Option.map_some, Option.bind_eq_bind,
        Option.bind_some, hpre12.cvR _ (fun _ _ => rfl) hpre12.grow.ext,
        show (5 : Word).toNat = 5 from rfl, e5, e6, e7, e8, bool?, hv12, hrs12]
      rfl

/-- **`CiAtLpsSim` from the rules' simulation.** -/
theorem ciAtLpsSim_of {p : Prog} (hP : CiProg p) (hR : RulesAtSim p dn) : CiAtLpsSim p dn :=
  ⟨fun n _ _ _ _ _ _ _ _ _ _ _ hT hok hr hci hdc hps hden =>
    ciAtLps_sim hP hR n hT hok hr hci hdc hps hden⟩

/-- **The simulations `check_quot_record` takes**, from the quotient block reader's refinement,
the leaves' write set, `QuotDn` and the rules' simulation. -/
theorem quotSims_of' {p : Prog} (hP : CiProg p) (hp : p.lookup "quot_pin" = some quotPin)
    (hRom : ∀ vis fe, L.Rom.RomQuotRef p dn vis fe) (hcl : LeafClosed p) (hq : QuotDn dn)
    (hR : RulesAtSim p dn) : QuotSims p dn :=
  quotSims_of hP.toQuotAtProg (quotPinSim_of hp hRom hcl hq) (ciAtLpsSim_of hP hR)

end ci

end L.Ind
