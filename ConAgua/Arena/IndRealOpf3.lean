import ConAgua.Arena.IndRealOpf2

/-!
# `opf_go`, `opa_go` under the stage relation (lane `indproofs4`, helper `opf`)

By induction on the L fuel, a returning run of `opf_go(n, e, i, co, cn)` (`opa_go(n, e, i)`) from
`StageR ∧ AbsOK`, the twin's `acc` the stack slice `(co, cn)` with the top at `co + cn` (the top
`t`), is the twin's `openPisAtFvarsFGo acc n e i` (`openPisAtFvars n e i`) with `StageR ∧ AbsOK`
after; on success (`OGo`) the `n` free variables are the stack slice `(t, n)`, the top is `t + n`,
and the stack below `t` is kept. The fvar indices `i, i + 1, …` do not wrap: each step pushes, so
`i + (|SPN| - t) < 2^64` bounds them.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Stack slices -/

theorem wadd_toNat {o : Word} {i : Nat} (h : o.toNat + i < 2 ^ 64) :
    (o + i.toUInt64).toNat = o.toNat + i := by
  rw [UInt64.toNat_add]; simp [Nat.toUInt64]; omega

theorem wadd_toNat' {o c : Word} (h : o.toNat + c.toNat < 2 ^ 64) : (o + c).toNat = o.toNat + c.toNat := by
  rw [UInt64.toNat_add]; omega

theorem wsub1 {n : Word} (hn : n ≠ 0) : (n - 1).toNat + 1 = n.toNat := by
  have : n.toNat ≠ 0 := fun h => hn (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

theorem SpineR.empty' {m : Mem} {t : Word} (h : t.toNat ≤ (m.arr64 SPN).size) :
    SpineR m t 0 (([] : List EIdx).toArray) :=
  ⟨rfl, by simpa using h, fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩

/-- A push onto the slice's end. -/
theorem SpineR.push' {m m' : Mem} {o c x : Word} {acc : Array EIdx} (h : SpineR m o c acc)
    (hx : x.toNat < 2 ^ 32) (hsz : (m'.arr64 SPN).size = (m.arr64 SPN).size)
    (hroom : o.toNat + c.toNat < (m.arr64 SPN).size) (hw : (m.arr64 SPN).size < 2 ^ 64)
    (hsp : ∀ w, spW m' w = if w = o + c then x else spW m w) :
    SpineR m' o (c + 1) (acc.push (decE x)) := by
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hne : ∀ i, i < c.toNat → o + i.toUInt64 ≠ o + c := fun i hi he => by
    have := congrArg UInt64.toNat he
    rw [wadd_toNat (by omega), wadd_toNat' (by omega)] at this; omega
  have hcc : o + c.toNat.toUInt64 = o + c := by rw [word_ofNat_toNat]
  refine ⟨by simp [h.size, hc1], by rw [hsz, hc1]; omega, ?_, ?_⟩
  · intro i hi; rw [hc1] at hi; rw [hsp]
    rcases Nat.lt_or_ge i c.toNat with hi' | hi'
    · rw [if_neg (hne i hi')]; exact h.lt i hi'
    · have : i = c.toNat := by omega
      subst this; rw [hcc, if_pos rfl]; exact hx
  · intro i hi
    rw [Array.getElem_push]
    split
    · rename_i hi'
      rw [hsp, if_neg (hne i (by rw [← h.size]; exact hi'))]; exact h.get i hi'
    · have : i = c.toNat := by simp at hi; rw [← h.size]; omega
      subst this; rw [hsp, hcc, if_pos rfl]

/-- A word in front of the slice. -/
theorem SpineR.cons' {m : Mem} {t c x : Word} {l : List EIdx} (h : SpineR m (t + 1) c l.toArray)
    (hx : spW m t = x) (hxl : x.toNat < 2 ^ 32) (hb : t.toNat + 1 + c.toNat < 2 ^ 64) :
    SpineR m t (c + 1) (decE x :: l).toArray := by
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have ht1 : (t + 1).toNat = t.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl : l.length = c.toNat := by simpa using h.size
  have hj : ∀ j : Nat, t + (j + 1).toUInt64 = t + 1 + j.toUInt64 := fun j => by
    apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add, Nat.toUInt64]; omega
  refine ⟨by simp [hl, hc1], by have := h.bound; rw [ht1] at this; rw [hc1]; omega, ?_, ?_⟩
  · intro i hi; rw [hc1] at hi
    rcases i with _ | j
    · simp [hx, hxl]
    · rw [hj]; exact h.lt j (by omega)
  · intro i hi
    rcases i with _ | j
    · simp [hx]
    · simp only [List.getElem_toArray, List.getElem_cons_succ]
      rw [hj]
      have := h.get j (by simp; simp at hi; omega)
      simpa using this

/-- **The post of a telescope walk** from the stack top `t`, `n` binders: none, or the `n` free
variables the slice `(t, n)`, the top `t + n`, the stack below `t` kept. -/
def OGo (t n : Word) (m m' : Mem) (r : List Word) : Option (List EIdx × EIdx) → Prop
  | none => r.headD 0 = 0
  | some (fvs, b) => r.headD 0 = 1 ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧ decE (r.tail.headD 0) = b ∧
      rdW (m'.arr64 CTL) 136 = t + n ∧ SpineR m' t n fvs.toArray ∧
      (∀ w : Word, w.toNat < t.toNat → spW m' w = spW m w)

/-- One step's `OGo`: the recursive call's from `t + 1`, the pushed word at `t`. -/
theorem OGo.step {t n x : Word} {m m4 m5 : Mem} {r : List Word} {y : Option (List EIdx × EIdx)}
    (hn : n ≠ 0) (h : OGo (t + 1) (n - 1) m4 m5 r y) (hx : spW m4 t = x) (hxl : x.toNat < 2 ^ 32)
    (hsz : (m5.arr64 SPN).size < 2 ^ 64) (ht : t.toNat < (m5.arr64 SPN).size)
    (hsp : ∀ w : Word, w.toNat < t.toNat → spW m4 w = spW m w) :
    OGo t n m m5 [r.headD 0, r.tail.headD 0] (y.map (fun p => (decE x :: p.1, p.2))) := by
  cases y with
  | none => exact h
  | some p =>
    obtain ⟨fvs, b⟩ := p
    obtain ⟨h1, hb, hd, htop, hsl, hbel⟩ := h
    have ht1 : (t + 1).toNat = t.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hsn := hsl.bound
    rw [ht1] at hsn
    have hn1 := wsub1 hn
    refine ⟨h1, hb, hd, by rw [htop]; grind, ?_, ?_⟩
    · have hc := SpineR.cons' hsl (by rw [hbel t (by omega)]; exact hx) hxl (by omega)
      rwa [show n - 1 + 1 = n by grind] at hc
    · intro w hw; rw [hbel w (by omega), hsp w hw]

/-! ## The twin's steps -/

theorem opfGo_run_zero (acc : Array EIdx) (h : EIdx) (i : Nat) (a a' : AState) (d : EIdx)
    (hd : (instantiateListFast coreWalkFuel h acc 0).run a = .ok (d, a')) :
    (openPisAtFvarsFGo acc 0 h i).run a = .ok (some ([], d), a') := by
  simp [openPisAtFvarsFGo, hd]; rfl

theorem opfGo_run_nf (acc : Array EIdx) (n : Nat) (h : EIdx) (i : Nat) (a : AState)
    (htag : (h.tag == ETag.forallE) = false) :
    (openPisAtFvarsFGo acc (n + 1) h i).run a = .ok (none, a) := by
  simp [openPisAtFvarsFGo, htag]; rfl

theorem opfGo_run_step (acc : Array EIdx) (n : Nat) (h : EIdx) (i : Nat) (a a2 a3 a5 : AState)
    (dom body d fv : EIdx) (x : Option (List EIdx × EIdx))
    (htag : (h.tag == ETag.forallE) = true)
    (hv : (view h).run a = .ok (.forallE dom body, a))
    (hd : (instantiateListFast coreWalkFuel dom acc 0).run a = .ok (d, a2))
    (hf : (internE (.fvar i d)).run a2 = .ok (fv, a3))
    (hrec : (openPisAtFvarsFGo (acc.push fv) n body (i + 1)).run a3 = .ok (x, a5)) :
    (openPisAtFvarsFGo acc (n + 1) h i).run a = .ok (x.map (fun p => (fv :: p.1, p.2)), a5) := by
  cases x with
  | none => simp [openPisAtFvarsFGo, htag, StateT.run_bind, hv, except_ok_bind, hd, hf, hrec]; rfl
  | some p => simp [openPisAtFvarsFGo, htag, StateT.run_bind, hv, except_ok_bind, hd, hf, hrec]; rfl

theorem opa_run_zero (h : EIdx) (i : Nat) (a : AState) :
    (openPisAtFvars 0 h i).run a = .ok (some ([], h), a) := rfl

theorem opa_run_nf (n : Nat) (h : EIdx) (i : Nat) (a : AState)
    (htag : (h.tag == ETag.forallE) = false) :
    (openPisAtFvars (n + 1) h i).run a = .ok (none, a) := by
  simp [openPisAtFvars, htag]; rfl

theorem opa_run_step (n : Nat) (h : EIdx) (i : Nat) (a a2 a3 a5 : AState)
    (dom body fv b : EIdx) (x : Option (List EIdx × EIdx))
    (htag : (h.tag == ETag.forallE) = true)
    (hv : (view h).run a = .ok (.forallE dom body, a))
    (hf : (internE (.fvar i dom)).run a = .ok (fv, a2))
    (hb : (instantiate1Fast coreWalkFuel body fv 0).run a2 = .ok (b, a3))
    (hrec : (openPisAtFvars n b (i + 1)).run a3 = .ok (x, a5)) :
    (openPisAtFvars (n + 1) h i).run a = .ok (x.map (fun p => (fv :: p.1, p.2)), a5) := by
  cases x with
  | none => simp [openPisAtFvars, htag, StateT.run_bind, hv, except_ok_bind, hb, hf, hrec]; rfl
  | some p => simp [openPisAtFvars, htag, StateT.run_bind, hv, except_ok_bind, hb, hf, hrec]; rfl

/-! ## `opf_go` -/

theorem decE_tag_fa (e : Word) (he : e.toNat < 2 ^ 32) :
    ((decE e).tag == ETag.forallE) = decide (e >>> 28 = 6) := tagForallIff e he

theorem push_of_callW {k : Nat} {m m' : Mem} {x : Word} {r : List Word}
    (h : callW opfP k "spn_push" [x] m = some (r, m')) : spnPushW m x = some (r, m') := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (spnPush_spec opfP rfl k _ x) h
  rw [hs'] at hW; exact hW

section
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`opf_go` refines `openPisAtFvarsFGo`** under the stage relation and `AbsOK`, the twin's
`acc` the stack slice `(co, cn)` below the top. -/
@[refines ConRon.Arena.openPisAtFvarsFGo]
theorem opfGo_ok : ∀ (k : Nat) (m m' : Mem) (a : AState) (n e i co cn : Word) (acc : Array EIdx)
    (r : List Word), callW opfP k "opf_go" [n, e, i, co, cn] m = some (r, m') →
    StageR dn vis fe m a → AbsOK m → e.toNat < 2 ^ 32 → SpineR m co cn acc →
    rdW (m.arr64 CTL) 136 = co + cn →
    i.toNat + ((m.arr64 SPN).size - (co.toNat + cn.toNat)) < 2 ^ 64 →
    ∃ x a', (openPisAtFvarsFGo acc n.toNat (decE e) i.toNat).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
      OGo (co + cn) n m m' r x := by
  intro k
  induction k with
  | zero => intro m m' a n e i co cn acc r hc; rw [callW_zero] at hc; cases hc
  | succ k ih =>
  intro m m' a n e i co cn acc r hc hS hAb he hsl htop hib
  have c' := callW_model (M := fun mm => opfGoK opfP k mm n e i co cn)
    (fun s => opfGoK_spec opfP rfl k s n e i co cn) hc
  have hw63 : (m.arr64 SPN).size < 2 ^ 63 := hAb.2.2.2.2.2.2.1
  have hcc : (co + cn).toNat = co.toNat + cn.toNat := wadd_toNat' (by have := hsl.bound; omega)
  simp only [opfGoK] at c'
  by_cases hn : n = 0
  · rw [if_pos hn] at c'
    obtain ⟨r1, m1, h1, c'⟩ := ntBW_some c'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
    obtain ⟨a1, hrun1, hS1, hg1, hAb1, hspn1, htop1, hlt1⟩ := opfIl_ok hS hAb hsl he h1
    subst hn
    refine ⟨_, _, opfGo_run_zero acc (decE e) i.toNat a a1 _ hrun1, hS1, hg1, hAb1, by rw [hspn1], ?_⟩
    refine ⟨rfl, hlt1, rfl, by rw [htop1, htop]; simp, SpineR.empty' ?_, fun w _ => by
      simp only [spW, hspn1]⟩
    rw [hspn1, hcc]; exact hsl.bound
  rw [if_neg hn] at c'
  have hn1 := wsub1 hn
  by_cases hg : e >>> 28 ≠ 6
  · rw [if_pos hg] at c'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
    refine ⟨none, a, by rw [← hn1]; exact opfGo_run_nf acc _ _ _ a (by rw [decE_tag_fa e he]; simpa using hg),
      hS, IWGrow.refl _, hAb, rfl, rfl⟩
  rw [if_neg hg] at c'
  have hg6 : e >>> 28 = 6 := Decidable.not_not.mp hg
  obtain ⟨rv, m1, h1, c'⟩ := ntBW_some c'
  obtain ⟨hm1, hx, hy, hview⟩ := opfV_ok hS hg6 h1
  subst m1
  obtain ⟨rd, m2, h2, c'⟩ := ntBW_some c'
  obtain ⟨a2, hrun2, hS2, hg2, hAb2, hspn2, htop2, hlt2⟩ := opfIl_ok hS hAb hsl hx h2
  obtain ⟨rf, m3, h3, c'⟩ := ntBW_some c'
  obtain ⟨a3, hrun3, hS3, hg3, hAb3, hspn3, htop3, hlt3⟩ := opfFv_ok hS2 hAb2 hlt2 h3
  obtain ⟨ru, m4, h4, c'⟩ := ntBW_some c'
  obtain ⟨hS4, hg4, hAb4, hroom, htop4, hsp4, hsz4⟩ := spnPushW_ok hS3 hAb3 (push_of_callW h4)
  obtain ⟨rb, m5, h5, c'⟩ := ntBW_some c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
  have ht3 : rdW (m3.arr64 CTL) 136 = co + cn := htop3.trans (htop2.trans htop)
  have hs3 : m3.arr64 SPN = m.arr64 SPN := hspn3.trans hspn2
  rw [ht3] at hroom htop4 hsp4
  rw [hs3, hcc] at hroom
  have hsl4 : SpineR m4 co (cn + 1) (acc.push (decE (rf.headD 0))) :=
    SpineR.push' (hsl.of_spn hs3) hlt3 hsz4 (by rw [hs3]; exact hroom) (by rw [hs3]; omega) hsp4
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hcn1 : (cn + 1).toNat = cn.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨x5, a5, hrun5, hS5, hg5, hAb5, hsz5, hO⟩ := ih m4 m5 a3 (n - 1) _ (i + 1) co (cn + 1) _ rb h5
    hS4 hAb4 hy hsl4 (by rw [htop4]; grind) (by rw [hsz4, hs3, hi1, hcn1]; omega)
  have hrun := opfGo_run_step acc (n - 1).toNat (decE e) i.toNat a a2 a3 a5 _ _ _ _ x5
    (by rw [decE_tag_fa e he]; simpa using hg6) hview hrun2 hrun3 (by rw [← hi1]; exact hrun5)
  rw [hn1] at hrun
  have hsz : (m5.arr64 SPN).size = (m.arr64 SPN).size := by rw [hsz5, hsz4, hs3]
  refine ⟨_, _, hrun, hS5, hg2.trans (hg3.trans (hg4.trans hg5)), hAb5, hsz, ?_⟩
  rw [show co + (cn + 1) = co + cn + 1 by grind] at hO
  exact OGo.step hn hO (by rw [hsp4]; simp) hlt3 (by rw [hsz]; omega) (by rw [hsz, hcc]; omega)
    (fun w hw => by
      rw [hsp4, if_neg (fun h => by subst h; omega)]
      simp only [spW, hs3])

/-- **`opa_go` refines `openPisAtFvars`** under the stage relation and `AbsOK`, from the stack
top `t`. -/
@[refines ConRon.Arena.openPisAtFvars]
theorem opaGo_ok : ∀ (k : Nat) (m m' : Mem) (a : AState) (n e i : Word) (r : List Word),
    callW opfP k "opa_go" [n, e, i] m = some (r, m') →
    StageR dn vis fe m a → AbsOK m → e.toNat < 2 ^ 32 →
    (rdW (m.arr64 CTL) 136).toNat ≤ (m.arr64 SPN).size →
    i.toNat + ((m.arr64 SPN).size - (rdW (m.arr64 CTL) 136).toNat) < 2 ^ 64 →
    ∃ x a', (openPisAtFvars n.toNat (decE e) i.toNat).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
      OGo (rdW (m.arr64 CTL) 136) n m m' r x := by
  intro k
  induction k with
  | zero => intro m m' a n e i r hc; rw [callW_zero] at hc; cases hc
  | succ k ih =>
  intro m m' a n e i r hc hS hAb he htb hib
  have c' := callW_model (M := fun mm => opaGoK opfP k mm n e i)
    (fun s => opaGoK_spec opfP rfl k s n e i) hc
  have hw63 : (m.arr64 SPN).size < 2 ^ 63 := hAb.2.2.2.2.2.2.1
  simp only [opaGoK] at c'
  by_cases hn : n = 0
  · rw [if_pos hn] at c'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
    subst hn
    refine ⟨_, _, opa_run_zero (decE e) i.toNat a, hS, IWGrow.refl _, hAb, rfl, ?_⟩
    exact ⟨rfl, he, rfl, by simp, SpineR.empty' htb, fun w _ => rfl⟩
  rw [if_neg hn] at c'
  have hn1 := wsub1 hn
  by_cases hg : e >>> 28 ≠ 6
  · rw [if_pos hg] at c'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
    refine ⟨none, a, by rw [← hn1]; exact opa_run_nf _ _ _ a (by rw [decE_tag_fa e he]; simpa using hg),
      hS, IWGrow.refl _, hAb, rfl, rfl⟩
  rw [if_neg hg] at c'
  have hg6 : e >>> 28 = 6 := Decidable.not_not.mp hg
  obtain ⟨rv, m1, h1, c'⟩ := ntBW_some c'
  obtain ⟨hm1, hx, hy, hview⟩ := opfV_ok hS hg6 h1
  subst m1
  obtain ⟨rf, m2, h2, c'⟩ := ntBW_some c'
  obtain ⟨a2, hrun2, hS2, hg2, hAb2, hspn2, htop2, hlt2⟩ := opfFv_ok hS hAb hx h2
  obtain ⟨rb, m3, h3, c'⟩ := ntBW_some c'
  obtain ⟨a3, hrun3, hS3, hg3, hAb3, hspn3, htop3, hlt3⟩ := opfI1_ok hS2 hAb2 hy h3
  obtain ⟨ru, m4, h4, c'⟩ := ntBW_some c'
  obtain ⟨hS4, hg4, hAb4, hroom, htop4, hsp4, hsz4⟩ := spnPushW_ok hS3 hAb3 (push_of_callW h4)
  obtain ⟨ro, m5, h5, c'⟩ := ntBW_some c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
  generalize ht : rdW (m.arr64 CTL) 136 = t at htb hib ⊢
  have ht3 : rdW (m3.arr64 CTL) 136 = t := htop3.trans (htop2.trans ht)
  have hs3 : m3.arr64 SPN = m.arr64 SPN := hspn3.trans hspn2
  rw [ht3] at hroom htop4 hsp4
  rw [hs3] at hroom
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have ht1 : (t + 1).toNat = t.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨x5, a5, hrun5, hS5, hg5, hAb5, hsz5, hO⟩ := ih m4 m5 a3 (n - 1) _ (i + 1) ro h5
    hS4 hAb4 hlt3 (by rw [htop4, hsz4, hs3, ht1]; omega) (by rw [htop4, hsz4, hs3, hi1, ht1]; omega)
  have hrun := opa_run_step (n - 1).toNat (decE e) i.toNat a a2 a3 a5 _ _ _ _ x5
    (by rw [decE_tag_fa e he]; simpa using hg6) hview hrun2 hrun3 (by rw [← hi1]; exact hrun5)
  rw [hn1] at hrun
  have hsz : (m5.arr64 SPN).size = (m.arr64 SPN).size := by rw [hsz5, hsz4, hs3]
  refine ⟨_, _, hrun, hS5, hg2.trans (hg3.trans (hg4.trans hg5)), hAb5, hsz, ?_⟩
  rw [htop4] at hO
  exact OGo.step hn hO (by rw [hsp4]; simp) hlt2 (by rw [hsz]; omega) (by rw [hsz]; omega)
    (fun w hw => by
      rw [hsp4, if_neg (fun h => by subst h; omega)]
      simp only [spW, hs3])

/-! ## `open_pis_at_fvars_f` -/

theorem opfF_run (n : Nat) (e : EIdx) (i : Nat) (a a1 : AState) (x1 : Option (List EIdx × EIdx))
    (h1 : (openPisAtFvarsFGo #[] n e i).run a = .ok (x1, a1)) :
    (openPisAtFvarsF n e i).run a =
      match x1 with
      | some r => .ok (some r, a1)
      | none => (openPisAtFvars n e i).run a1 := by
  cases x1 <;> simp [openPisAtFvarsF, StateT.run_bind, h1, except_ok_bind] <;> rfl

/-- **The tail**: the stack slice `(co, n)` copied to a fresh pool slice, the top put back. -/
theorem opfTail_ok {k : Nat} {n co b : Word} {m2 m' : Mem} {a2 : AState} {fvs : List EIdx}
    {r : List Word} (hS : StageR dn vis fe m2 a2) (hAb : AbsOK m2) (hsl : SpineR m2 co n fvs.toArray)
    (hb : b.toNat < 2 ^ 32) (h : opfTail k n co b (allocW m2 n) = some (r, m')) :
    KeepPost dn vis fe decOLE m2 m' a2 r (some (fvs, decE b)) ∧ AbsOK m' := by
  obtain ⟨⟨q, m3⟩, ha, h⟩ := of_K h rfl; rw [opfTail_some] at h
  obtain ⟨r3, m4, c3, h⟩ := ntBW_some h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hsz1 : (m2.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  obtain ⟨hq, rfl, hroom⟩ := allocW_facts ha hsz1
  have hm4 := s2iW_wr k _ _ _ _ _ _ c3
  generalize hws : spnWs (allocMem m2 n) co n.toNat = ws at hm4
  have hspn2 : (allocMem m2 n).arr64 SPN = m2.arr64 SPN :=
    (allocMem_frame m2 n).1 SPN (by simp [SPN, IW]) (by decide)
  have hlen : n.toNat = ws.length := by rw [← hws, spnWs_length]
  have hrec := recPost_wr m2 ws n hlen hS.2 (by
    have : q.toNat = iwTop m2 := by rw [hq]; rfl
    rw [← hlen, ← this]; exact hroom)
  rw [← hq, ← hm4] at hrec
  have hget : ∀ i, i < n.toNat → ws[i]? = some (spW m2 (co + i.toUInt64)) := by
    intro i hi; rw [← hws, spnWs_get _ _ _ _ hi]; simp only [spW, hspn2]
  have hlt : ∀ w ∈ ws, w.toNat < 2 ^ 32 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hi' : i < n.toNat := by rw [hlen]; exact hi
    have := hget i hi'
    rw [List.getElem?_eq_getElem hi] at this
    rw [Option.some.inj this]; exact hsl.lt i hi'
  have hxs : ws.map (decI : Word → EIdx) = fvs := by
    apply List.ext_getElem
    · simp only [List.length_map]; rw [← hlen]; simpa using hsl.size.symm
    · intro i h1 h2
      simp only [List.getElem_map]
      have hi1 : i < ws.length := by simpa using h1
      have hi' : i < n.toNat := by rw [hlen]; exact hi1
      have := hget i hi'
      rw [List.getElem?_eq_getElem hi1] at this
      rw [Option.some.inj this]
      have hg := hsl.get i (by simpa using h2)
      simp only [List.getElem_toArray] at hg
      rw [hg]; rfl
  have hK := slice_keep (κ := .expr) hS hrec hlt hlen
  rw [hxs] at hK
  obtain ⟨hS3, hg3, hdec⟩ := hK
  obtain ⟨hS4, hg4⟩ := stageR_hi hS3 (MemFrame.setCtl m4 136 co) (by simp) (by simp) (by decide)
    (by decide)
  have hI4 : (m4.set64 CTL 136 co).arr64 IW = m4.arr64 IW := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have ht4 : iwTop (m4.set64 CTL 136 co) = iwTop m4 := by
    simp only [iwTop, rdW_set64]; simp
  have hfr : MemFrame [IW] [200, 136] m2 (m4.set64 CTL 136 co) := by
    rw [hm4]
    exact (((allocMem_frame m2 n).trans (wrIW_frame ws _ q)).mono (fun b hb => hb)
      (by simp)).trans ((MemFrame.setCtl _ 136 co).mono (by simp) (by simp))
  refine ⟨⟨hS4, hg3.trans hg4, rfl, ?_, ⟨hb, rfl⟩⟩, hAb.frameD hfr (by decide) (by decide)⟩
  obtain ⟨hd1, hd2⟩ := hdec
  refine ⟨?_, ?_⟩
  · simp only [List.getD_eq_getElem?_getD] at hd1 ⊢
    simpa [decHL, iwA, hI4] using hd1
  · simp only [List.getD_cons_succ, List.getD_cons_zero] at hd2 ⊢
    rw [ht4]; exact hd2

/-- **`open_pis_at_fvars_f` refines `openPisAtFvarsF`** under the stage relation and the walk
memos (replaces `IndStubs.openPisAtFvarsF_spec`; a first fvar index `≥ 2^63` aborts, deviation
D33, so the indices do not wrap); the memos are well formed after. -/
@[refines ConRon.Arena.openPisAtFvarsF]
theorem opfF_ok (k e i : Word) (he : H e) :
    RelW opfF [k, e, i] (fun m a => StageR dn vis fe m a ∧ AbsOK m)
      (openPisAtFvarsF k.toNat (decI e) i.toNat)
      (fun m m' a r x => KeepPost dn vis fe decOLE m m' a r x ∧ AbsOK m') := by
  intro m m' a r h ⟨hS, hAb⟩
  obtain ⟨N, hc⟩ := callF_run h
  rcases N with _ | K
  · rw [callW_zero] at hc; cases hc
  have c' := callW_model (M := fun mm => opfTopK opfP K mm k e i)
    (fun s => opfTopK_spec opfP rfl rfl rfl K s k e i) hc
  have hw63 : (m.arr64 SPN).size < 2 ^ 63 := hAb.2.2.2.2.2.2.1
  have hctl : 200 < (m.arr64 CTL).size := hS.2.2.2.2.2
  simp only [opfTopK] at c'
  obtain ⟨hsh, c'⟩ := of_ite_none c'
  have hi : i.toNat < 2 ^ 63 := by
    have h1 := congrArg UInt64.toNat (Decidable.not_not.mp hsh)
    rw [UInt64.toNat_shiftRight] at h1
    simp only [UInt64.toNat_zero, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod,
      Nat.reducePow] at h1
    have := i.toNat_lt
    omega
  generalize hco : rdW (m.arr64 CTL) 136 = co at c'
  obtain ⟨hlen, c'⟩ := of_ite_none c'
  have hcob : co.toNat ≤ (m.arr64 SPN).size := by
    have : ¬ (((m.arr64 SPN).size : Nat).toUInt64 < co) := hlen
    rw [UInt64.lt_iff_toNat_lt] at this
    have h2 : (((m.arr64 SPN).size : Nat).toUInt64).toNat = (m.arr64 SPN).size := by
      simp [Nat.toUInt64]; omega
    omega
  obtain ⟨r1, m1, h1, c'⟩ := ntBW_some c'
  obtain ⟨x1, a1, hrun1, hS1, hg1, hAb1, hsz1, hO1⟩ := opfGo_ok dn vis fe K m m1 a k e i co 0 #[] r1
    h1 hS hAb he (by simpa using SpineR.empty' (m := m) hcob) (by rw [hco]; simp) (by simp; omega)
  have hrun := opfF_run k.toNat (decE e) i.toNat a a1 x1 hrun1
  simp only [opfK2] at c'
  rw [show co + 0 = co by simp] at hO1
  cases x1 with
  | some p =>
    obtain ⟨fvs, b⟩ := p
    obtain ⟨h0, hb, hdb, -, hsl, -⟩ := hO1
    rw [if_neg (by rw [h0]; decide)] at c'
    obtain ⟨⟨hS', hg', hdec⟩, hAb'⟩ := opfTail_ok dn vis fe hS1 hAb1 hsl hb c'
    rw [hdb] at hdec
    exact ⟨_, _, hrun, ⟨hS', hg1.trans hg', hdec⟩, hAb'⟩
  | none =>
    rw [if_pos (show r1.headD 0 = 0 from hO1)] at c'
    obtain ⟨hS1', hg1'⟩ := stageR_hi hS1 (MemFrame.setCtl m1 136 co) (by simp) (by simp) (by decide)
      (by decide)
    have hAb1' := hAb1.frameD (MemFrame.setCtl m1 136 co) (by decide) (by decide)
    have hctl1 : 200 < (m1.arr64 CTL).size := hS1.2.2.2.2.2
    have htop1 : rdW ((m1.set64 CTL 136 co).arr64 CTL) 136 = co := by
      rw [rdW_set64E, ite_eq_left ⟨rfl, rfl, by simp; omega⟩]
    have hsz1' : ((m1.set64 CTL 136 co).arr64 SPN).size = (m.arr64 SPN).size := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hsz1]
    obtain ⟨r2, m2, h2, c'⟩ := ntBW_some c'
    simp only [opfK3] at c'
    obtain ⟨x2, a2, hrun2, hS2, hg2, hAb2, -, hO2⟩ := opaGo_ok dn vis fe K _ m2 a1 k e i r2 h2
      hS1' hAb1' he (by rw [htop1, hsz1']; exact hcob) (by rw [htop1, hsz1']; omega)
    rw [htop1] at hO2
    simp only at hrun
    rw [hrun2] at hrun
    cases x2 with
    | none =>
      rw [if_pos (show r2.headD 0 = 0 from hO2)] at c'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
      obtain ⟨hS3, hg3⟩ := stageR_hi hS2 (MemFrame.setCtl m2 136 co) (by simp) (by simp) (by decide)
        (by decide)
      exact ⟨_, _, hrun, ⟨hS3, hg1.trans (hg1'.trans (hg2.trans hg3)), rfl⟩,
        hAb2.frameD (MemFrame.setCtl m2 136 co) (by decide) (by decide)⟩
    | some p =>
      obtain ⟨fvs, b⟩ := p
      obtain ⟨h0, hb, hdb, -, hsl, -⟩ := hO2
      rw [if_neg (by rw [h0]; decide)] at c'
      obtain ⟨⟨hS', hg', hdec⟩, hAb'⟩ := opfTail_ok dn vis fe hS2 hAb2 hsl hb c'
      rw [hdb] at hdec
      exact ⟨_, _, hrun, ⟨hS', hg1.trans (hg1'.trans (hg2.trans hg')), hdec⟩, hAb'⟩

end

end L.Ind
