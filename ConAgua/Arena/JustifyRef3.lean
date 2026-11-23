module

public import ConAgua.Arena.JustifyModels
public import ConAgua.Arena.IndRealNames
public import ConAgua.Arena.QuotAtT
import ConAgua.Arena.Checker
import ConRon.Bridge.Rel
import ConRon.Bridge.Grind
import ConRon.Bridge.Frontend.Shared
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# `rec_names` refines `recNames` (lane compare, helper compare-cone)

`rec_names(d, o, l)` writes the names `m.str "rec"` of the `EREC` name slice `(o, l)` into the
fresh words `EREC[d‥d + l)` (allocated by its caller above a base state's top): each name by
`name_rec` (`nrF_ok`, an interning step of the twin's), each word by `erec_put` into the fresh
region (`StageR.putFresh`).
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind

/-- What `name_rec` writes: the pool and the `str` table. -/
def nrA : List TieredArray := [POOL, POOL1, NSREC, tier1 NSREC, NSSLOT, tier1 NSSLOT]

/-- What `rec_names` writes: `name_rec`'s and the record pool. -/
def rnA : List TieredArray := EREC :: tier1 EREC :: nrA

/-- The control words `name_rec` writes. -/
def nrC : List Word := [0, 36, 37]

section nr
variable {p : Prog}

theorem nr_frame (hp : NrF p) {n : Nat} {x : Word} {m m' : Mem} {r : List Word}
    (h : callW p n "name_rec" [x] m = some (r, m')) : MemFrame nrA nrC m m' := by
  rw [callW_agree nrProg_closed (hp.agree nrFns) n (by decide)] at h
  exact (run_memFrame nrProg_closed (by decide) (run_of_callW h)).1

theorem nr_of_callW (hp : NrF p) {n : Nat} {x : Word} {m m' : Mem} {r : List Word}
    (h : callW p n "name_rec" [x] m = some (r, m')) : nrF m [x] = some (r, m') :=
  callF_of_callW (by rw [← callW_agree nrProg_closed (hp.agree nrFns) n (by decide)]; exact h)

end nr

/-- The lookups of `rec_names`. -/
structure RnProg (p : Prog) : Prop where
  rn : p.lookup "rec_names" = some recNamesL
  nr : NrF p
  put : p.lookup "erec_put" = some erecPut

theorem nrA_quot : ∀ b ∈ rnA, b ∈ quotA := by decide
theorem nrC_quot : ∀ x ∈ nrC, x ∈ quotC := by
  intro x hx
  simp only [nrC, List.mem_cons, List.not_mem_nil, or_false] at hx
  simp only [quotC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  rcases hx with rfl | rfl | rfl
  · exact ⟨0, ⟨by omega, .inr (.inr (by decide))⟩, rfl⟩
  · exact ⟨36, ⟨by omega, .inr (.inr (by decide))⟩, rfl⟩
  · exact ⟨37, ⟨by omega, .inr (.inr (by decide))⟩, rfl⟩
/-- **`StageT` across `name_rec`**: its `StageR` post, the twin's interning step, its frame. -/
theorem StageT.of_nr {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a a' : AState} (hT : StageT dn vis fe m a) (hS : StageR vis fe m' a')
    (hs : ConRon.Bridge.Frontend.IStepS a a') (hf : MemFrame nrA nrC m m') :
    StageT dn vis fe m' a' :=
  ⟨hS, hT.twin.of_istep hs (by rw [hf.size]; exact hT.twin.erec) (by rw [hf.size]; exact hT.twin.spn)
    (by rw [hf.size]; exact hT.twin.bstk)
    (hT.twin.memos.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩),
    by simp only [pinW, hf.arr PINS (by decide) (by decide)]; exact hT.flag⟩

section rn
variable {p : Prog} (P : RnProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

/-- **`rec_names`' recursion**: from a base state `m₀` (the stage at `m₀`, the region
`[d, d + l)` above its top), the names `ms` of the slice `(o, l)` (decoded at the base, its end at
most `2 ^ 64`), interned `str "rec"` by the twin (`recNames`), written to `EREC[d‥d + l)`; the stage
with the twin's invariants kept, every other record word kept. -/
theorem recNames_loop {m₀ : Mem} {a₀ : AState} (h₀ : StageR vis fe m₀ a₀) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (d o l : Word) (r : List Word) (ms : List NIdx)
      (L : List ConLeche.Name) (out : List NIdx),
    recNamesW p n m d o l = some (r, m') →
    StageT dn vis fe m a → ConRon.Bridge.StateOK a → MemFrame quotA quotC m₀ m → IWGrow m₀ m →
    hslice? (erecP m₀) o.toNat l.toNat = some ms →
    Frontend.denoteNList a.store.ns ms = some L →
    erTopOf m₀ d ≤ erOff d → erOff d + l.toNat ≤ erTopOf m d → d.toNat + l.toNat < 2 ^ 41 →
    o.toNat + l.toNat ≤ 2 ^ 64 →
    ∃ rn a', (ConRon.Arena.recNames out ms).run a = .ok (out ++ rn, a') ∧
      StageT dn vis fe m' a' ∧ ConRon.Bridge.Frontend.IStepS a a' ∧ IWGrow m₀ m' ∧
      MemFrame quotA quotC m₀ m' ∧ MemFrame rnA nrC m m' ∧ erTopOf m' d = erTopOf m d ∧
      hslice? (erecP m') d.toNat l.toNat = some rn ∧
      ∀ i, (∀ j < l.toNat, i % 2 ^ 41 ≠ (d.toNat + j) % 2 ^ 41) → erecP m' i = erecP m i := by
  intro n
  induction n with
  | zero => intro m m' a d o l r ms L out h; rw [recNamesW.eq_1] at h; cases h
  | succ n ih =>
  intro m m' a d o l r ms L out h hT hok hf hg hms hL hd0 hdt hd41 ho64
  by_cases hl : l = 0
  · subst hl
    rw [recNamesW.arm1 _ _ _ _ _ _ rfl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [UInt64.toNat_zero, hslice?, List.range_zero, List.mapM_nil] at hms
    obtain rfl := (Option.some.inj hms).symm
    refine ⟨[], a, by simp [ConRon.Arena.recNames]; rfl, hT, ConRon.Bridge.Frontend.IStepS.refl hok,
      hg, hf, MemFrame.refl _ _ _, rfl, by simp [hslice?], fun _ _ => rfl⟩
  rw [recNamesW.arm2 _ _ _ _ _ _ hl] at h
  have hl0 : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simp [e]))
  obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
  have hl1 : (l - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  -- the slice's head
  rw [hk, hslice?_succ] at hms
  cases hx : (hd? (erecP m₀) o.toNat : Option NIdx) with
  | none => rw [hx] at hms; cases hms
  | some μ =>
  rw [hx] at hms
  cases hxs : (hslice? (erecP m₀) (o.toNat + 1) k : Option (List NIdx)) with
  | none => rw [hxs] at hms; simp at hms
  | some ms' =>
  rw [hxs] at hms
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hms
  subst hms
  obtain ⟨y, Ly, hy, hLy, rfl⟩ := ConRon.Bridge.denoteNList_cons_inv hL
  simp only [hd?, Option.bind_eq_bind] at hx
  cases hw : erecP m₀ o.toNat with
  | none => rw [hw] at hx; cases hx
  | some w =>
  rw [hw] at hx
  simp only [Option.bind_some] at hx
  split at hx
  · rename_i hw32
    obtain rfl := (Option.some.inj hx).symm
    have hwm : erecP m o.toNat = some w := hg.ext _ _ hw
    have hrd : erRd m o = w := erRd_of o w hwm
    rw [hrd] at h
    -- `name_rec`
    cases h1 : callW p n "name_rec" [w] m with
    | none => rw [h1, recNamesW.k_name_rec.eq_1] at h; cases h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, recNamesW.k_name_rec.arm1] at h
    have hf1 := nr_frame P.nr h1
    obtain ⟨n1, a1, hrun1, hS1, hg1, hr1l, hr1⟩ :=
      nrF_ok dn vis fe w hw32 m m1 a r1 (nr_of_callW P.nr h1) hT.stage
    obtain ⟨st1, hn1⟩ := ConRon.Bridge.Frontend.internNNode_sstep hok
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc
          exact ConRon.Bridge.nview_isSome_of_denote hy) hrun1
    have hT1 : StageT dn vis fe m1 a1 :=
      StageT.of_nr hT hS1 st1 hf1
    -- `erec_put(d, n1)`
    cases h2 : callW p n "erec_put" [d, r1.headD 0] m1 with
    | none => rw [h2, recNamesW.k_erec_put.eq_1] at h; cases h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, recNamesW.k_erec_put.arm1] at h
    have e2 := callW_erecPut P.put h2
    subst e2
    have hf01 : MemFrame quotA quotC m₀ m1 := hf.trans (hf1.mono (fun b hb => nrA_quot b
      (by simp only [rnA, List.mem_cons]; exact .inr (.inr hb))) nrC_quot)
    have hg01 : IWGrow m₀ m1 := hg.trans hg1
    obtain ⟨hS2, hg2, hfq2⟩ := StageR.putFresh h₀ hT1.stage hf01 hg01 hd0 (v := r1.headD 0)
    have hT2 : StageT dn vis fe (erecPutMem m1 d (r1.headD 0)) a1 :=
      StageT.of_wrER (ws := [r1.headD 0]) hT1 hS2
    have hc1 : ∀ x ∈ [(129 : Word), 130], rdW (m1.arr64 CTL) x = rdW (m.arr64 CTL) x :=
      fun x hx => hf1.ctl x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
    have htop1 : erTopOf m1 d = erTopOf m d := by
      simp only [erTopOf, erTop, erecTop1, hc1 129 (by simp), hc1 130 (by simp)]
    have htop2 : erTopOf (erecPutMem m1 d (r1.headD 0)) d = erTopOf m d := by
      rw [← htop1]; simp only [erTopOf, erTop, erecTop1, erecPutMem_ctl]
    obtain ⟨htopsz, hcap⟩ := hT.stage.iw.topOf d
    have hlt0 : erOff d < erTopOf m d := by omega
    have hself : erecP (erecPutMem m1 d (r1.headD 0)) d.toNat = some (r1.headD 0) := by
      have hsz : (m1.arr64 (erTier d)).size = (m.arr64 (erTier d)).size := hf1.size _
      have hb : erOff d < (m1.arr64 (erTier d)).size := by rw [hsz]; exact Nat.lt_of_lt_of_le hlt0 htopsz
      exact erecP_putMem_self (by rw [htop1]; exact hlt0) hb
    -- the rest
    have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hbit : (d + 1).toNat / 2 ^ 40 % 2 = d.toNat / 2 ^ 40 % 2 := by
      rw [hd1]; unfold erOff at hdt; omega
    have hTop : ∀ m' : Mem, erTopOf m' (d + 1) = erTopOf m' d := fun m' => by
      simp only [erTopOf, hbit]
    have hoff1 : erOff (d + 1) = erOff d + 1 := by
      simp only [erOff, hd1]; unfold erOff at hdt; omega
    cases h3 : recNamesW p n (erecPutMem m1 d (r1.headD 0)) (d + 1) (o + 1) (l - 1) with
    | none => rw [h3, recNamesW.k_rec_names.none] at h; cases h
    | some x3 =>
    obtain ⟨r3, m3⟩ := x3
    rw [h3, recNamesW.k_rec_names.arm1] at h
    obtain ⟨-, e3⟩ := Prod.mk.inj (Option.some.inj h)
    subst e3
    obtain ⟨rn, a', hrun', hT', hst', hg', hfq', hfr', htop', hsl', hout'⟩ :=
      ih _ m3 a1 (d + 1) (o + 1) (l - 1) r3 ms' Ly (out ++ [n1]) h3 hT2 st1.ok hfq2 hg2
        (by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0; rw [hl1]; simp only [hslice?, List.range_zero, List.mapM_nil] at hxs ⊢; exact hxs
          · have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
            rw [ho1, hl1]; exact hxs)
        (ConRon.Bridge.denoteNListE_ext st1.ext _ _ hLy)
        (by rw [hTop, hoff1]; omega) (by rw [hTop, htop2, hoff1, hl1]; omega)
        (by rw [hd1, hl1]; omega)
        (by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · rw [hl1, hk0]; exact Nat.le_of_lt (UInt64.toNat_lt _)
          · have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
            rw [ho1, hl1]; omega)
    refine ⟨n1 :: rn, a', ?_, hT', st1.trans hst', hg', hfq', ?_, ?_, ?_, ?_⟩
    · simp only [ConRon.Arena.recNames, StateT.run_bind, hrun1]
      simpa using hrun'
    · refine hf1.mono (fun b hb => by simp only [rnA, List.mem_cons]; exact .inr (.inr hb))
        (fun _ h => h) |>.trans ((erecPutMem_frame m1 d _).mono (by simp [rnA]) (by simp)) |>.trans hfr'
    · rw [← hTop m3, htop', hTop, htop2]
    · rw [hk, hslice?_succ]
      have h0 : erecP m3 d.toNat = some (r1.headD 0) := by
        rw [hout' d.toNat (fun j hj => by rw [hd1]; omega), hself]
      have hn1 : (decI (r1.headD 0) : NIdx) = n1 := hr1
      simp only [hd?, h0, Option.bind_eq_bind, Option.bind_some, hr1l, ↓reduceIte, hn1]
      rw [← hd1, ← hl1, hsl']; rfl
    · intro i hi
      rw [hout' i (fun j hj => by rw [hd1]; have := hi (j + 1) (by omega); rwa [show d.toNat + 1 + j = d.toNat + (j + 1) by omega])]
      rw [erecP_putMem_other (by have := hi 0 (by omega); simpa using this)]
      -- `name_rec` writes no record word
      have hE0 : m1.arr64 EREC = m.arr64 EREC := hf1.arr _ (by decide) (by decide)
      have hE1 : m1.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf1.arr _ (by decide) (by decide)
      have t0 : erTop m1 = erTop m := by simp only [erTop]; rw [hc1 129 (by simp)]
      have t1 : erecTop1 m1 = erecTop1 m := by simp only [erecTop1]; rw [hc1 130 (by simp)]
      simp only [erecP, hE0, hE1, t0, t1]
  · cases hx

end rn

end L.Arena
