module

public import ConAgua.Arena.DeclAndPinIndCopy
import ConAgua.Arena.DeclAndPinInd
public import ConAgua.Arena.DeclAndPinIndDec
public import ConAgua.Arena.WhnfBase
public import ConAgua.Front.StateDR
import ConAgua.L.WordOff

@[expose] public section

/-!
# The `And` pin's inductive arm, part 2c: what the copy's pieces leave

`erec_alloc` allocates in the tier of the scratch flag `CTL[1]` (`fT`, its top `fTop`, its tagged
base `fB`), and all of the copy's writes (`erec_put`) land there. `ErW W m m'`: a writer of the
flag's tier (only that tier's array and its top change, the top grows within the array) that
changes no word below the old top outside `W`. Allocations, `dind_copy` and the relocating writes
are `ErW`s; they compose (`ErW.trans`). `dindCopyW_get`: the words a copy leaves. The decoding
side reads through `erecP` (`erecP_f`: the flag's tier at `fB + y`).
-/

open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP trunc decCIs IndDeclAt dw)
open L.Ind (erAllocW erAllocMem erecAlloc erecPutMem erecPutMem_arr erecPutMem_ctl erTier erOff
  erTopOf erAllocW_spec IWOK IWGrow iwTop)

/-! ## The flag's tier -/

/-- The scratch flag `CTL[1]`. -/
def flg (m : Mem) : Word := rdW (m.arr64 CTL) 1
/-- The tier `erec_alloc` allocates in: `EREC` with the flag off, tier 1 with it on. -/
def fT (m : Mem) : TieredArray := if flg m = 0 then EREC else tier1 EREC
/-- That tier's top's `CTL` word. -/
def fC (m : Mem) : Word := if flg m = 0 then 129 else 130
/-- That tier's tagged base address. -/
def fB (m : Mem) : Nat := if flg m = 0 then 0 else 2 ^ 40
/-- That tier's top. -/
def fTop (m : Mem) : Nat := (rdW (m.arr64 CTL) (fC m)).toNat

theorem fC_ne1 (m : Mem) : (1 : Word) ≠ fC m := by unfold fC; split <;> decide
theorem fT_ne_ctl (m : Mem) : (CTL : TieredArray) ≠ fT m := by unfold fT; split <;> decide
theorem fT_ne_dlp (m : Mem) : (DLP : TieredArray) ≠ fT m := by unfold fT; split <;> decide
theorem fT_ne_decl (m : Mem) : (DECL : TieredArray) ≠ fT m := by unfold fT; split <;> decide

theorem f_of_flg {m m' : Mem} (e : flg m' = flg m) : fT m' = fT m ∧ fC m' = fC m ∧ fB m' = fB m := by
  simp [fT, fC, fB, e]

/-- The flag's tier, read off `CTL` alone. -/
theorem f_of_ctl {m m' : Mem} (e : m'.arr64 CTL = m.arr64 CTL) :
    flg m' = flg m ∧ fT m' = fT m ∧ fC m' = fC m ∧ fB m' = fB m ∧ fTop m' = fTop m := by
  have h1 : flg m' = flg m := by unfold flg; rw [e]
  obtain ⟨a, b, c⟩ := f_of_flg h1
  exact ⟨h1, a, b, c, by unfold fTop; rw [b, e]⟩

theorem fTop_le {m : Mem} (hW : IWOK m) : fTop m ≤ (m.arr64 (fT m)).size := by
  have h1 := hW.er; have h2 := hW.er1
  unfold fTop fC fT; split
  · exact h1
  · exact h2

theorem fCap {m : Mem} (hW : IWOK m) : (m.arr64 (fT m)).size < 2 ^ 40 := by
  have h1 := hW.erCap; have h2 := hW.er1Cap
  unfold fT; split
  · exact h1
  · exact h2

theorem fB_le (m : Mem) : fB m ≤ 2 ^ 40 := by unfold fB; split <;> omega

/-- **The flag's tier through `erecP`**: tagged address `fB + y` below the top is word `y`. -/
theorem erecP_f {m : Mem} (hW : IWOK m) {y : Nat} (hy : y < fTop m) :
    erecP m (fB m + y) = (m.arr64 (fT m))[y]? := by
  have hc := fCap hW
  have hl := fTop_le hW
  have hy40 : y < 2 ^ 40 := by omega
  unfold erecP
  by_cases hf : flg m = 0
  · have e1 : fB m = 0 := by simp [fB, hf]
    have e2 : fT m = EREC := by simp [fT, hf]
    have e3 : fTop m = erTop m := by simp [fTop, fC, hf, erTop]
    rw [e1, e2, Nat.zero_add, ite_eq_left (by omega), ite_eq_left (by omega), Nat.mod_eq_of_lt hy40,
      ite_eq_left (by omega)]
  · have e1 : fB m = 2 ^ 40 := by simp [fB, hf]
    have e2 : fT m = tier1 EREC := by simp [fT, hf]
    have e3 : fTop m = erecTop1 m := by simp [fTop, fC, hf, erecTop1]
    rw [e1, e2, ite_eq_left (by omega), ite_eq_right (by omega), show (2 ^ 40 + y) % 2 ^ 40 = y by omega,
      ite_eq_left (by omega)]

/-- A tagged address `fB + x` of the flag's tier: its tier and offset. -/
theorem erTier_f {m : Mem} {a : Word} {x : Nat} (ha : a.toNat = fB m + x) (hx : x < 2 ^ 40) :
    erTier a = fT m ∧ erOff a = x := by
  unfold erTier erOff fT
  rw [ha]
  by_cases hf : flg m = 0
  · have e1 : fB m = 0 := by simp [fB, hf]
    rw [e1]; simp only [hf, ite_true]
    rw [ite_eq_left (by omega)]; exact ⟨rfl, by omega⟩
  · have e1 : fB m = 2 ^ 40 := by simp [fB, hf]
    rw [e1]; simp only [hf, ite_false]
    rw [ite_eq_right (by omega)]; exact ⟨rfl, by omega⟩

/-- `erec_put` at `fB + x`: word `x` of the flag's tier, nothing else. -/
theorem erPut_f {m : Mem} {a v : Word} {x : Nat} (ha : a.toNat = fB m + x) (hx : x < 2 ^ 40) :
    (erecPutMem m a v).arr64 (fT m) = (m.arr64 (fT m)).setIfInBounds x v ∧
      (∀ b, b ≠ fT m → (erecPutMem m a v).arr64 b = m.arr64 b) := by
  obtain ⟨e1, e2⟩ := erTier_f ha hx
  refine ⟨by rw [erecPutMem_arr, ite_eq_left e1.symm, e2], fun b hb => ?_⟩
  rw [erecPutMem_arr, ite_eq_right (by rw [e1]; exact hb)]

theorem erPut_ctl (m : Mem) (a v : Word) :
    flg (erecPutMem m a v) = flg m ∧ fT (erecPutMem m a v) = fT m ∧ fC (erecPutMem m a v) = fC m ∧
      fB (erecPutMem m a v) = fB m ∧ fTop (erecPutMem m a v) = fTop m :=
  f_of_ctl (erecPutMem_ctl m a v)

theorem erPut_size (m : Mem) (a v : Word) (b : TieredArray) :
    ((erecPutMem m a v).arr64 b).size = (m.arr64 b).size := by
  rw [erecPutMem_arr]; split <;> simp

/-! ## Writers of the flag's tier -/

/-- **A writer of the flag's tier**: only that tier's array and its top change, the top grows
within the array, and below the old top only the words `W` admits change. -/
structure ErW (W : Nat → Prop) (m m' : Mem) : Prop where
  arr : ∀ b, b ≠ fT m → b ≠ CTL → m'.arr64 b = m.arr64 b
  ctl : ∀ x, x ≠ fC m → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x
  size : ∀ b, (m'.arr64 b).size = (m.arr64 b).size
  top : fTop m ≤ fTop m'
  room : fTop m' ≤ (m.arr64 (fT m)).size
  get : ∀ i < fTop m, ¬ W i → (m'.arr64 (fT m))[i]? = (m.arr64 (fT m))[i]?

namespace ErW
variable {W W' : Nat → Prop} {m m' : Mem}

theorem flg_eq (h : ErW W m m') : flg m' = flg m := h.ctl 1 (fC_ne1 m)
theorem fT_eq (h : ErW W m m') : fT m' = fT m := (f_of_flg h.flg_eq).1
theorem fC_eq (h : ErW W m m') : fC m' = fC m := (f_of_flg h.flg_eq).2.1
theorem fB_eq (h : ErW W m m') : fB m' = fB m := (f_of_flg h.flg_eq).2.2

theorem refl (W : Nat → Prop) (m : Mem) (h : fTop m ≤ (m.arr64 (fT m)).size) : ErW W m m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, Nat.le_refl _, h, fun _ _ _ => rfl⟩

theorem trans {m₁ m₂ m₃ : Mem} (h₁ : ErW W m₁ m₂) (h₂ : ErW W' m₂ m₃)
    (hW : ∀ i, i < fTop m₁ → W' i → W i) : ErW W m₁ m₃ := by
  have eT := h₁.fT_eq
  have eC := h₁.fC_eq
  refine ⟨fun b hb hc => (h₂.arr b (by rw [eT]; exact hb) hc).trans (h₁.arr b hb hc),
    fun x hx => (h₂.ctl x (by rw [eC]; exact hx)).trans (h₁.ctl x hx),
    fun b => (h₂.size b).trans (h₁.size b), Nat.le_trans h₁.top h₂.top, ?_, fun i hi hn => ?_⟩
  · have := h₂.room; rw [eT, h₁.size] at this; exact this
  · have := h₂.get i (Nat.lt_of_lt_of_le hi h₁.top) (fun hw => hn (hW i hi hw))
    rw [eT] at this
    exact this.trans (h₁.get i hi hn)

theorem mono (h : ErW W m m') (hW : ∀ i, W i → W' i) : ErW W' m m' :=
  ⟨h.arr, h.ctl, h.size, h.top, h.room, fun i hi hn => h.get i hi (fun hw => hn (hW i hw))⟩

theorem dlp (h : ErW W m m') : m'.arr64 DLP = m.arr64 DLP := h.arr DLP (fT_ne_dlp m) (by decide)
theorem decl (h : ErW W m m') : m'.arr64 DECL = m.arr64 DECL := h.arr DECL (fT_ne_decl m) (by decide)

/-- The frame of a writer: the record tiers and their tops. -/
theorem frame (h : ErW W m m') : MemFrame [EREC, tier1 EREC] [129, 130] m m' :=
  ⟨fun b hb hc => h.arr b (by unfold fT; split <;> (intro e; subst e; simp at hb)) hc,
   fun x hx => h.ctl x (by unfold fC; split <;> (intro e; subst e; simp at hx)), h.size⟩

theorem iwok (h : ErW W m m') (hW : IWOK m) : IWOK m' := by
  have hI : m'.arr64 L.Ind.IW = m.arr64 L.Ind.IW :=
    h.arr L.Ind.IW (by unfold fT; split <;> decide) (by decide)
  have h200 := h.ctl 200 (by unfold fC; split <;> decide)
  have hsC := h.size CTL
  have hs0 := h.size EREC
  have hs1 := h.size (tier1 EREC)
  have hr := h.room
  have hW1 := hW.er; have hW2 := hW.er1
  simp only [erTop, erecTop1] at hW1 hW2
  by_cases hf : flg m = 0
  · have eT : fT m = EREC := by simp [fT, hf]
    have eC : fC m = 129 := by simp [fC, hf]
    have e130 := h.ctl 130 (by rw [eC]; decide)
    have ht : fTop m' = (rdW (m'.arr64 CTL) 129).toNat := by simp [fTop, h.fC_eq, eC]
    rw [eT] at hr
    exact
      { iw := by simpa only [iwTop, hI, h200] using hW.iw
        er := by simp only [erTop]; omega
        iwSize := hI ▸ hW.iwSize, erSize := hs0 ▸ hW.erSize, ctl := hsC ▸ hW.ctl
        er1 := by simp only [erecTop1, e130, hs1]; exact hW2
        er1Size := hs1 ▸ hW.er1Size, erCap := hs0 ▸ hW.erCap, er1Cap := hs1 ▸ hW.er1Cap }
  · have eT : fT m = tier1 EREC := by simp [fT, hf]
    have eC : fC m = 130 := by simp [fC, hf]
    have e129 := h.ctl 129 (by rw [eC]; decide)
    have ht : fTop m' = (rdW (m'.arr64 CTL) 130).toNat := by simp [fTop, h.fC_eq, eC]
    rw [eT] at hr
    exact
      { iw := by simpa only [iwTop, hI, h200] using hW.iw
        er := by simp only [erTop, e129, hs0]; exact hW1
        iwSize := hI ▸ hW.iwSize, erSize := hs0 ▸ hW.erSize, ctl := hsC ▸ hW.ctl
        er1 := by simp only [erecTop1]; omega
        er1Size := hs1 ▸ hW.er1Size, erCap := hs0 ▸ hW.erCap, er1Cap := hs1 ▸ hW.er1Cap }

/-- A writer that changed nothing below the old top grows the pools. -/
theorem grow (h : ErW W m m') (hn : ∀ i, i < fTop m → ¬ W i) : ErecGrow m m' ∧ IWGrow m m' := by
  have hI : m'.arr64 L.Ind.IW = m.arr64 L.Ind.IW :=
    h.arr L.Ind.IW (by unfold fT; split <;> decide) (by decide)
  have h200 := h.ctl 200 (by unfold fC; split <;> decide)
  have ht := h.top
  have hg := h.get
  have hg' : ErecGrow m m' := by
    by_cases hf : flg m = 0
    · have eT : fT m = EREC := by simp [fT, hf]
      have eC : fC m = 129 := by simp [fC, hf]
      have e130 := h.ctl 130 (by rw [eC]; decide)
      have e1 := h.arr (tier1 EREC) (by rw [eT]; decide) (by decide)
      have ht' : fTop m' = erTop m' := by simp [fTop, h.fC_eq, eC, erTop]
      have ht0 : fTop m = erTop m := by simp [fTop, eC, erTop]
      rw [eT] at hg
      exact ⟨by omega, fun i hi => hg i (by omega) (hn i (by omega)),
        by simp [erecTop1, e130], fun i _ => by rw [e1]⟩
    · have eT : fT m = tier1 EREC := by simp [fT, hf]
      have eC : fC m = 130 := by simp [fC, hf]
      have e129 := h.ctl 129 (by rw [eC]; decide)
      have e0 := h.arr EREC (by rw [eT]; decide) (by decide)
      have ht' : fTop m' = erecTop1 m' := by simp [fTop, h.fC_eq, eC, erecTop1]
      have ht0 : fTop m = erecTop1 m := by simp [fTop, eC, erecTop1]
      rw [eT] at hg
      exact ⟨by simp [erTop, e129], fun i _ => by rw [e0], by omega,
        fun i hi => hg i (by omega) (hn i (by omega))⟩
  exact ⟨hg',
    { iw := by simp [iwTop, h200]
      er := hg'.top, iwGet := fun i _ => by rw [hI], erGet := hg'.get, er1 := hg'.top1
      er1Get := hg'.get1 }⟩

/-- A word below the old top that the writer kept, through `erecP`. -/
theorem erecP_keep (h : ErW W m m') (hW : IWOK m) {y : Nat} (hy : y < fTop m) (hn : ¬ W y) :
    erecP m' (fB m + y) = erecP m (fB m + y) := by
  have hW' := h.iwok hW
  rw [← h.fB_eq, erecP_f hW' (Nat.lt_of_lt_of_le hy h.top), h.fB_eq, erecP_f hW hy, h.fT_eq]
  exact h.get y hy hn

/-- **A word written below the top** (`erec_put` at `fB + x`). -/
theorem put {m : Mem} {a v : Word} {x : Nat} (ha : a.toNat = fB m + x) (hx : x < fTop m)
    (hW : IWOK m) : ErW (fun i => i = x) m (erecPutMem m a v) := by
  have hc := fCap hW
  have hl := fTop_le hW
  obtain ⟨h1, h2⟩ := erPut_f (v := v) ha (by omega)
  obtain ⟨-, -, -, -, et⟩ := erPut_ctl m a v
  refine ⟨fun b hb _ => h2 b hb, fun y _ => by rw [erecPutMem_ctl], erPut_size m a v, by omega,
    by rw [et]; exact hl, fun i _ hn => ?_⟩
  rw [h1, Array.getElem?_setIfInBounds, ite_eq_right (Ne.symm hn)]

end ErW

/-- The written word reads back. -/
theorem erPut_get_same {m : Mem} {a v : Word} {x : Nat} (ha : a.toNat = fB m + x)
    (hx : x < (m.arr64 (fT m)).size) (hc : (m.arr64 (fT m)).size < 2 ^ 40) :
    ((erecPutMem m a v).arr64 (fT m))[x]? = some v := by
  rw [(erPut_f (v := v) ha (by omega)).1, Array.getElem?_setIfInBounds, ite_eq_left rfl]
  simp [hx]

theorem erPut_get_ne {m : Mem} {a v : Word} {x i : Nat} (ha : a.toNat = fB m + x) (hx : x < 2 ^ 40)
    (hi : i ≠ x) : ((erecPutMem m a v).arr64 (fT m))[i]? = (m.arr64 (fT m))[i]? := by
  rw [(erPut_f (v := v) ha hx).1, Array.getElem?_setIfInBounds, ite_eq_right (Ne.symm hi)]

/-- **`erec_alloc(k)`**: the pointer is the tagged old top of the flag's tier, the top moves by
`k` within the array, nothing else changes. -/
theorem erAlloc_f {m m1 : Mem} {k o : Word} (h : erAllocW m k = some (o, m1)) (hW : IWOK m) :
    o.toNat = fB m + fTop m ∧ fTop m1 = fTop m + k.toNat ∧ (∀ W, ErW W m m1) ∧ IWOK m1 := by
  obtain ⟨-, hf, hoff, htop, hsz, htier, h41, hW1⟩ := erAllocW_spec h hW
  have hm1 : m1 = m.set64 CTL (fC m) (rdW (m.arr64 CTL) (fC m) + k) := by
    unfold erAllocW at h
    by_cases e : rdW (m.arr64 CTL) 1 = 0
    · simp only [e, ite_true] at h
      split at h
      · cases h
      split at h
      · cases h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [erAllocMem, fC, flg, e]
    · simp only [e, ite_false] at h
      split at h
      · cases h
      split at h
      · cases h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [erAllocMem, fC, flg, e]
  have hfr : MemFrame [] [fC m] m m1 := by rw [hm1]; exact MemFrame.setCtl _ _ _
  have hfl : flg m1 = flg m := hfr.ctl 1 (by simp [(fC_ne1 m)])
  obtain ⟨eT1, eC1, eB1⟩ := f_of_flg hfl
  have hT : ∀ m' : Mem, flg m' = flg m → erTopOf m' o = fTop m' ∧ erTier o = fT m := by
    intro m' e
    by_cases hb : o.toNat / 2 ^ 40 % 2 = 0
    · have h0 : flg m = 0 := htier.1 hb
      have h0' : flg m' = 0 := e.trans h0
      unfold erTopOf erTier fTop fC fT
      rw [ite_eq_left hb, ite_eq_left hb, ite_eq_left h0', ite_eq_left h0]
      exact ⟨rfl, rfl⟩
    · have h0 : ¬ flg m = 0 := fun h' => hb (htier.2 h')
      have h0' : ¬ flg m' = 0 := fun h' => h0 (e.symm.trans h')
      unfold erTopOf erTier fTop fC fT
      rw [ite_eq_right hb, ite_eq_right hb, ite_eq_right h0', ite_eq_right h0]
      exact ⟨rfl, rfl⟩
  obtain ⟨t0, tT⟩ := hT m rfl
  obtain ⟨t1, -⟩ := hT m1 hfl
  have hoN : o.toNat = fB m + fTop m := by
    rw [← t0, ← hoff]
    unfold erOff fB
    by_cases hb : o.toNat / 2 ^ 40 % 2 = 0
    · have : flg m = 0 := htier.1 hb
      simp only [this, ite_true]; omega
    · have : ¬ flg m = 0 := fun h' => hb (htier.2 h')
      simp only [this, ite_false]; omega
  refine ⟨hoN, by rw [← t1, htop, t0], fun W => ⟨fun b _ hc => hfr.arr b (by simp) hc,
    fun x hx => hfr.ctl x (by simpa using hx), hfr.size, by rw [← t1, htop, t0]; omega,
    by rw [← t1, ← tT]; exact hsz, fun i _ _ => by rw [hfr.arr _ (by simp) (fT_ne_ctl m).symm]⟩, hW1⟩

/-! ## `dind_copy` -/

/-- A non-empty `dind_copy` step: the source is not `0`, the rest copies from the next word. -/
theorem dindCopyW_succ {n : Nat} {m m' : Mem} {d s l : Word} (h : dindCopyW (n + 1) m d s l = some m')
    (hl : l ≠ 0) : s ≠ 0 ∧
      dindCopyW n (erecPutMem m d (rdW (m.arr64 DLP) s)) (d + 1) (s + 1) (l - 1) = some m' := by
  by_cases hs : s = 0
  · rw [dindCopyW.abort1 n m d s l hl hs] at h; cases h
  by_cases hg : decide ((d &&& 1099511627775).toNat < (m.arr64 (tierA EREC (d >>> 40))).size) = true
  · rw [dindCopyW.arm2 n m d s l hl hs hg] at h
    refine ⟨hs, ?_⟩
    revert h
    cases dindCopyW n (erecPutMem m d (rdW (m.arr64 DLP) s)) (d + 1) (s + 1) (l - 1) <;>
      simp [dindCopyW.k_dind_copy.none, dindCopyW.k_dind_copy.arm1]
  · rw [dindCopyW.abort2 n m d s l hl hs hg] at h; cases h

/-- **What `dind_copy(d, s, l)` leaves**: word `x + j` of the flag's tier the `DLP` word `s + j`
(`d` the tagged `fB + x`), all else as it was; a non-empty copy has a source other than `0`. -/
theorem dindCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word) (x : Nat), dindCopyW n m d s l = some m' →
    d.toNat = fB m + x → x + l.toNat ≤ (m.arr64 (fT m)).size → (m.arr64 (fT m)).size < 2 ^ 40 →
    (∀ b, b ≠ fT m → m'.arr64 b = m.arr64 b) ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
    (l ≠ 0 → s ≠ 0) ∧
    ∀ i, (m'.arr64 (fT m))[i]? =
      if x ≤ i ∧ i < x + l.toNat then
        some (rdW (m.arr64 DLP) (s + UInt64.ofNat (i - x)))
      else (m.arr64 (fT m))[i]? := by
  induction n with
  | zero => intro m m' d s l x h; rw [dindCopyW.eq_1] at h; cases h
  | succ n ih =>
    intro m m' d s l x h hd hsz hcap
    by_cases hl : l = 0
    · rw [dindCopyW.arm1 n m d s l hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, fun _ => rfl, fun h => absurd rfl h, fun i => ?_⟩
      have : ¬ (x ≤ i ∧ i < x + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, ite_false]
    obtain ⟨hs, h⟩ := dindCopyW_succ h hl
    have hl0 : 0 < l.toNat := by
      have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
      omega
    have hl1 : (l - 1).toNat = l.toNat - 1 := by
      have := l.toNat_lt
      rw [UInt64.toNat_sub]; simp; omega
    have hB := fB_le m
    have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨m1, hm1⟩ : ∃ m1, m1 = erecPutMem m d (rdW (m.arr64 DLP) s) := ⟨_, rfl⟩
    rw [← hm1] at h
    obtain ⟨hA1, hO1⟩ := erPut_f (m := m) (v := rdW (m.arr64 DLP) s) hd (by omega)
    rw [← hm1] at hA1 hO1
    obtain ⟨-, eT1, -, eB1, -⟩ := erPut_ctl m d (rdW (m.arr64 DLP) s)
    rw [← hm1] at eT1 eB1
    have hsz1 : ∀ b, (m1.arr64 b).size = (m.arr64 b).size := by rw [hm1]; exact erPut_size m _ _
    have hP1 : m1.arr64 DLP = m.arr64 DLP := hO1 DLP (fT_ne_dlp m)
    have hget1 : ∀ i, (m1.arr64 (fT m))[i]? = if i = x then some (rdW (m.arr64 DLP) s)
        else (m.arr64 (fT m))[i]? := by
      intro i
      rw [hA1, Array.getElem?_setIfInBounds]
      by_cases hi : x = i
      · subst hi; simp; omega
      · simp [hi, Ne.symm hi]
    obtain ⟨hA, hS, -, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) (x + 1) h
      (by rw [hd1, eB1, hd]; omega) (by rw [eT1, hsz1, hl1]; omega) (by rw [eT1, hsz1]; exact hcap)
    rw [eT1, hP1] at hG
    rw [eT1] at hA
    refine ⟨fun b hb => (hA b hb).trans (hO1 b hb), fun b => (hS b).trans (hsz1 b), fun _ => hs,
      fun i => ?_⟩
    rw [hG i, hl1]
    by_cases hi : x ≤ i ∧ i < x + l.toNat
    · rw [ite_eq_left hi]
      by_cases hid : i = x
      · subst hid
        have : ¬ (i + 1 ≤ i ∧ i < i + 1 + (l.toNat - 1)) := by omega
        rw [ite_eq_right this, hget1, ite_eq_left rfl]; simp
      · have h2 : x + 1 ≤ i ∧ i < x + 1 + (l.toNat - 1) := by omega
        rw [ite_eq_left h2]
        have e : i - x = (i - (x + 1)) + 1 := by omega
        rw [e, UInt64.ofNat_add]
        congr 2
        simp only [UInt64.ofNat_one]
        ac_rfl
    · rw [ite_eq_right hi, ite_eq_right (by omega), hget1, ite_eq_right (by omega)]

/-- `dind_copy` into an allocated region is a writer of that region. -/
theorem dindCopyW_EW {n : Nat} {m m' : Mem} {d s l : Word} {x : Nat} (h : dindCopyW n m d s l = some m')
    (hd : d.toNat = fB m + x) (hx : x + l.toNat ≤ fTop m) (hW : IWOK m) :
    ErW (fun i => x ≤ i ∧ i < x + l.toNat) m m' := by
  have hr := fTop_le hW
  obtain ⟨hA, hS, -, hG⟩ := dindCopyW_get n m m' d s l x h hd (by omega) (fCap hW)
  have hC : m'.arr64 CTL = m.arr64 CTL := hA CTL (fT_ne_ctl m)
  obtain ⟨-, -, -, -, et⟩ := f_of_ctl hC
  refine ⟨fun b hb _ => hA b hb, fun y _ => by rw [hC], hS, by omega, by omega, fun i _ hn => ?_⟩
  rw [hG i, ite_eq_right hn]

/-! ## Reading the front's pool -/

/-- A word the cut pool holds (not its word `0`) is the pool's, read at any word index naming it. -/
theorem rdW_of_trunc {P : Array Word} {t x : Nat} {w v : Word} (h : (trunc P t)[x]? = some v)
    (hx : x ≠ 0) (hw : w.toNat = x) : rdW P w = v := by
  obtain ⟨hP, -⟩ := L.Arena.trunc_get_some h hx
  simp [rdW, hw, hP]

theorem trunc_lt {P : Array Word} {t x : Nat} {v : Word} (h : (trunc P t)[x]? = some v)
    (hx : x ≠ 0) : x < P.size := (Array.getElem?_eq_some_iff.mp (L.Arena.trunc_get_some h hx).1).1

/-! ## `ind_rec_copy`'s record -/

/-- The relocating writes after the record's copy (`ircW.k_dind_copy_2`). -/
theorem ircW_kdc2 {k q r p p' : Word} {m6 m' : Mem}
    (h : ircW.k_dind_copy_2 k q r p (some m6) = some (p', m')) :
    p = p' ∧ (if k = 5 then erecPutMem (erecPutMem m6 (p + 2) q) (p + 7) r
      else erecPutMem m6 (p + 2) q) = m' := by
  -- a whole-record copy (`ind_rec_copy`): the offsets as numbers (`rec_unfold`)
  simp only [ircW.k_dind_copy_2, ircW.j2, rec_unfold, UInt64.reduceAdd] at h
  revert h
  repeat' split
  all_goals simp_all

/-- **The record's copy** (`nn` words from `s`, then word `2` := `q`, and for a recursor word
`7` := `r`), allocated at the top of the flag's tier. -/
theorem ircT_ok {n : Nat} {mx m' : Mem} {s q r nn kw p : Word}
    (h : ircW.j1 n s kw q r nn mx = some (p, m')) (hW : IWOK mx)
    (hnn : 3 ≤ nn.toNat) (h5 : kw = 5 → 8 ≤ nn.toNat) :
    p.toNat = fB mx + fTop mx ∧ fTop m' = fTop mx + nn.toNat ∧ ErW (fun i => fTop mx ≤ i) mx m' ∧
      s ≠ 0 ∧ ∀ k < nn.toNat, (m'.arr64 (fT mx))[fTop mx + k]? =
        some (if k = 2 then q else if k = 7 ∧ kw = 5 then r
          else rdW (mx.arr64 DLP) (s + UInt64.ofNat k)) := by
  rw [ircW.j1.arm1] at h
  cases ha : erAllocW mx nn with
  | none => rw [ha, ircW.k_erec_alloc_2.none] at h; cases h
  | some x =>
  obtain ⟨pp, m5⟩ := x
  rw [ha, ircW.k_erec_alloc_2.arm1] at h
  obtain ⟨hpp, ht5, hW5, hok5⟩ := erAlloc_f ha hW
  have hw5 := hW5 (fun _ => False)
  cases hd : dindCopyW n m5 pp s nn with
  | none => rw [hd, ircW.k_dind_copy_2.none] at h; cases h
  | some m6 =>
  rw [hd] at h
  obtain ⟨rfl, rfl⟩ := ircW_kdc2 h
  have hcap := fCap hW
  have hr0 := fTop_le hW
  have hB := fB_le mx
  have eT5 := hw5.fT_eq
  have eB5 := hw5.fB_eq
  have hP5 : m5.arr64 DLP = mx.arr64 DLP := hw5.dlp
  have hpp5 : pp.toNat = fB m5 + fTop mx := by rw [eB5]; exact hpp
  have hr5 : fTop m5 ≤ (m5.arr64 (fT m5)).size := fTop_le hok5
  have hsz5 : (m5.arr64 (fT m5)).size = (mx.arr64 (fT mx)).size := by rw [eT5, hw5.size]
  obtain ⟨hA6, hS6, hsrc, hG6⟩ :=
    dindCopyW_get n m5 m6 pp s nn (fTop mx) hd hpp5 (by omega) (fCap hok5)
  have hW6 := dindCopyW_EW hd hpp5 (by omega) hok5
  have hok6 := hW6.iwok hok5
  obtain ⟨-, eT6, -, eB6, et6⟩ := f_of_ctl (hA6 CTL (fT_ne_ctl m5))
  have hs0 : s ≠ 0 := hsrc (fun h0 => by subst h0; simp at hnn)
  have hp2 : (pp + 2).toNat = fB m6 + (fTop mx + 2) := by
    rw [UInt64.toNat_add, eB6, eB5]; simp; omega
  have hsz6 : (m6.arr64 (fT m6)).size = (mx.arr64 (fT mx)).size := by rw [eT6, hS6, hsz5]
  -- the first relocating write
  have hWa := ErW.put (v := q) hp2 (by rw [et6]; omega) hok6
  have hoka := hWa.iwok hok6
  obtain ⟨-, eTa, -, eBa, eta⟩ := erPut_ctl m6 (pp + 2) q
  have eTx6 : fT m6 = fT mx := eT6.trans eT5
  have hcp : ∀ k < nn.toNat, (m6.arr64 (fT mx))[fTop mx + k]? =
      some (rdW (mx.arr64 DLP) (s + UInt64.ofNat k)) := by
    intro k hk
    have := hG6 (fTop mx + k)
    rw [ite_eq_left (by omega), hP5, Nat.add_sub_cancel_left, eT5] at this
    exact this
  have e2 : ∀ k < nn.toNat, ((erecPutMem m6 (pp + 2) q).arr64 (fT mx))[fTop mx + k]? =
      if k = 2 then some q else some (rdW (mx.arr64 DLP) (s + UInt64.ofNat k)) := by
    intro k hk
    split
    · rename_i hk2; subst hk2; rw [← eTx6]; exact erPut_get_same hp2 (by omega) (by rw [hsz6]; exact hcap)
    · rw [← eTx6, erPut_get_ne hp2 (by omega) (by omega), eTx6, hcp k hk]
  have hWa' : ErW (fun i => fTop mx ≤ i) mx (erecPutMem m6 (pp + 2) q) :=
    ((hW5 _).trans hW6 (fun i _ hi => by omega)).trans hWa (fun i _ hi => by
      omega)
  have hta : fTop (erecPutMem m6 (pp + 2) q) = fTop mx + nn.toNat := by rw [eta, et6, ht5]
  by_cases hk5 : kw = 5
  · have h8 := h5 hk5
    simp only [hk5, ite_true]
    have hp7 : (pp + 7).toNat = fB (erecPutMem m6 (pp + 2) q) + (fTop mx + 7) := by
      rw [UInt64.toNat_add, eBa, eB6, eB5]; simp; omega
    have hWb := ErW.put (v := r) hp7 (by rw [hta]; omega) hoka
    obtain ⟨-, eTb, -, -, etb⟩ := erPut_ctl (erecPutMem m6 (pp + 2) q) (pp + 7) r
    have eTxa : fT (erecPutMem m6 (pp + 2) q) = fT mx := eTa.trans eTx6
    have hsza : ((erecPutMem m6 (pp + 2) q).arr64 (fT (erecPutMem m6 (pp + 2) q))).size =
        (mx.arr64 (fT mx)).size := by rw [eTa, erPut_size, hsz6]
    refine ⟨hpp, by rw [etb, hta], hWa'.trans hWb (fun i _ hi => by omega), hs0, fun k hk => ?_⟩
    by_cases hk7 : k = 7
    · subst hk7
      rw [← eTxa, erPut_get_same hp7 (by rw [hsza]; omega) (by rw [hsza]; exact hcap)]
      simp
    · rw [← eTxa, erPut_get_ne hp7 (by omega) (by omega), eTxa, e2 k hk]
      by_cases hk2 : k = 2 <;> simp [hk2, hk7]
  · simp only [hk5, ite_false]
    refine ⟨hpp, hta, hWa', hs0, fun k hk => ?_⟩
    rw [e2 k hk]
    by_cases hk2 : k = 2 <;> simp [hk2]

/-! ## From the copy's words to the relocation's premises -/

theorem shR_of_copy {P : Array Word} {B : Nat → Option Word} {t : Nat} {sW : Word} {p : Nat} {K : Nat → Prop}
    (hs0 : sW ≠ 0) (hP : P.size < 2 ^ 63)
    (hcopy : ∀ k, K k → B (p + k) = some (rdW P (sW + UInt64.ofNat k))) :
    ShR (aread (trunc P t)) B sW.toNat p K := by
  intro k v hk hv
  have hs : sW.toNat ≠ 0 := fun h0 => hs0 (UInt64.toNat_inj.mp (by simpa using h0))
  have hx : sW.toNat + k ≠ 0 := by omega
  have hlt := trunc_lt hv hx
  rw [hcopy k hk, rdW_of_trunc hv hx (L.toNat_add_ofNat_of_lt _ _ (by omega))]

/-- A slice of the cut pool whose copy is at `q`. -/
theorem slice_of_copy {P : Array Word} {B : Nat → Option Word} {t : Nat} {offW cntW : Word} {q : Nat}
    (hP : P.size < 2 ^ 63) (hne : cntW ≠ 0 → offW ≠ 0)
    (hcopy : ∀ j < cntW.toNat, B (q + j) = some (rdW P (offW + UInt64.ofNat j))) :
    ∀ j v, j < cntW.toNat → (trunc P t)[offW.toNat + j]? = some v → B (q + j) = some v := by
  intro j v hj hv
  have hc0 : cntW ≠ 0 := fun h0 => by subst h0; simp at hj
  have ho : offW.toNat ≠ 0 := fun h0 => hne hc0 (UInt64.toNat_inj.mp (by simpa using h0))
  have hx : offW.toNat + j ≠ 0 := by omega
  have hlt := trunc_lt hv hx
  rw [hcopy j hj, rdW_of_trunc hv hx (L.toNat_add_ofNat_of_lt _ _ (by omega))]

/-- A header word the cut pool holds at `s + k` is the pool's word at the word index `s + k`. -/
theorem hdr_of_trunc {P : Array Word} {t : Nat} {sW : Word} {k x : Nat} (hP : P.size < 2 ^ 63)
    (hs0 : sW ≠ 0) (hx : nat? (aread (trunc P t)) (sW.toNat + k) = some x) :
    (rdW P (sW + UInt64.ofNat k)).toNat = x := by
  simp only [nat?, Option.map_eq_some_iff] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hs : sW.toNat ≠ 0 := fun h0 => hs0 (UInt64.toNat_inj.mp (by simpa using h0))
  have hlt := trunc_lt hw (by omega)
  rw [rdW_of_trunc hw (by omega) (L.toNat_add_ofNat_of_lt _ _ (by omega))]

/-- **The relocation, from the copy's words.** -/
theorem decCI_of_copy {P : Array Word} {B : Nat → Option Word} {t : Nat}
    {sW qW rW : Word} {p : Nat} {c : IConstantInfo}
    (hc : decCI (aread (trunc P t)) sW.toNat = some c) (hF : FrontCI c) (hP : P.size < 2 ^ 63)
    (hs0 : sW ≠ 0)
    (hkind : ∀ kk, nat? (aread (trunc P t)) sW.toNat = some kk → ∀ k, relocK kk k →
      B (p + k) = some (rdW P (sW + UInt64.ofNat k)))
    (hq : B (p + 2) = some qW)
    (hl : ∀ j < (rdW P (sW + 3)).toNat,
      B (qW.toNat + j) = some (rdW P (rdW P (sW + 2) + UInt64.ofNat j)))
    (hl0 : rdW P (sW + 3) ≠ 0 → rdW P (sW + 2) ≠ 0)
    (hr : nat? (aread (trunc P t)) sW.toNat = some 5 → B (p + 7) = some rW ∧
      (∀ x < 11 * (rdW P (sW + 8)).toNat,
        B (rW.toNat + x) = some (rdW P (rdW P (sW + 7) + UInt64.ofNat x))) ∧
      (rdW P (sW + 8) ≠ 0 → rdW P (sW + 7) ≠ 0) ∧ (rdW P (sW + 8)).toNat < 2 ^ 60) :
    decCI B p = some c := by
  refine decCI_reloc (q := qW.toNat) (r := rW.toNat) hc hF
    (fun kk hkk => shR_of_copy hs0 hP (hkind kk hkk)) (by simp [nat?, hq]) ?_ ?_
  · intro off cnt hoff hcnt
    have e2 := hdr_of_trunc (k := 2) hP hs0 hoff
    have e3 := hdr_of_trunc (k := 3) hP hs0 hcnt
    simp only [show UInt64.ofNat 2 = 2 from rfl, show UInt64.ofNat 3 = 3 from rfl] at e2 e3
    rw [← e2, ← e3]
    exact slice_of_copy hP hl0 hl
  · intro h5
    obtain ⟨h7, hrs, hr0, hb⟩ := hr h5
    refine ⟨by simp [nat?, h7], fun off cnt hoff hcnt => ?_⟩
    have e7 := hdr_of_trunc (k := 7) hP hs0 hoff
    have e8 := hdr_of_trunc (k := 8) hP hs0 hcnt
    simp only [show UInt64.ofNat 7 = 7 from rfl, show UInt64.ofNat 8 = 8 from rfl] at e7 e8
    rw [← e7, ← e8]
    have hcw : (UInt64.ofNat (11 * (rdW P (sW + 8)).toNat)).toNat = 11 * (rdW P (sW + 8)).toNat :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)
    have hcp := slice_of_copy (t := t) (cntW := UInt64.ofNat (11 * (rdW P (sW + 8)).toNat)) hP
      (fun hne => hr0 (fun h0 => hne (by rw [h0]; rfl))) (fun j hj => hrs j (by rw [hcw] at hj; exact hj))
    intro x v hx hv
    exact hcp x v (by rw [hcw]; exact hx) hv

/-! ## `ind_rec_copy` -/

/-- **A record decoding robustly**: in every reader that agrees with `R` on `[lo, hi)`, the
record at `p` decodes to `c`. -/
def RecRob (R : Nat → Option Word) (lo hi p : Nat) (c : IConstantInfo) : Prop :=
  ∀ B : Nat → Option Word, (∀ i, lo ≤ i → i < hi → B i = R i) → decCI B p = some c


theorem decCI_front_kind {T : Array Word} {x : Nat}
    {c : IConstantInfo} (hc : decCI (aread T) x = some c) (hF : FrontCI c) :
    ∃ kk, nat? (aread T) x = some kk ∧ (kk = 3 ∨ kk = 4 ∨ kk = 5) := by
  unfold decCI at hc
  cases hk : nat? (aread T) x with
  | none => simp [hk] at hc
  | some kk =>
  refine ⟨kk, rfl, ?_⟩
  rw [hk] at hc
  simp only [bind, Option.bind_some] at hc
  rcases kk with _ | _ | _ | _ | _ | _ | kk
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨_, -, rfl⟩ := hc; exact hF.elim
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨_, -, _, -, _, -, rfl⟩ := hc; exact hF.elim
  · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨_, -, rfl⟩ := hc; exact hF.elim
  · simp
  · simp
  · simp
  · simp at hc


/-- The common end of `ind_rec_copy`'s three kinds: the record's copy at the top of `mx`, where
the level parameters (and a recursor's rules) were already copied. -/
theorem irc_fin {n : Nat} {m mx m' : Mem} {t : Nat}
    {s q r nn kw p : Word} {kk : Nat} {c : IConstantInfo}
    (hT : ircW.j1 n s kw q r nn mx = some (p, m'))
    (hwx : ErW (fun i => fTop m ≤ i) m mx) (hW : IWOK m)
    (hc : decCI (aread (trunc (m.arr64 DLP) t)) s.toNat = some c) (hF : FrontCI c)
    (hP : (m.arr64 DLP).size < 2 ^ 63)
    (hkk : nat? (aread (trunc (m.arr64 DLP) t)) s.toNat = some kk) (hkw : kw.toNat = kk)
    (hnn : nn.toNat = if kk = 3 then CI.indSize.toNat else if kk = 4 then 8 else 10) (hk345 : kk = 3 ∨ kk = 4 ∨ kk = 5)
    (hql : fB m + fTop m ≤ q.toNat)
    (hlr : q.toNat + (rdW (m.arr64 DLP) (s + 3)).toNat ≤ fB m + fTop mx)
    (hl : ∀ j < (rdW (m.arr64 DLP) (s + 3)).toNat, erecP mx (q.toNat + j) =
      some (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (s + 2) + UInt64.ofNat j)))
    (hl0 : rdW (m.arr64 DLP) (s + 3) ≠ 0 → rdW (m.arr64 DLP) (s + 2) ≠ 0)
    (hr : kk = 5 → fB m + fTop m ≤ r.toNat ∧
      r.toNat + 11 * (rdW (m.arr64 DLP) (s + 8)).toNat ≤ fB m + fTop mx ∧
      (∀ x < 11 * (rdW (m.arr64 DLP) (s + 8)).toNat, erecP mx (r.toNat + x) =
        some (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (s + 7) + UInt64.ofNat x))) ∧
      (rdW (m.arr64 DLP) (s + 8) ≠ 0 → rdW (m.arr64 DLP) (s + 7) ≠ 0) ∧
      (rdW (m.arr64 DLP) (s + 8)).toNat < 2 ^ 60) :
    ErW (fun i => fTop m ≤ i) m m' ∧ fB m + fTop m ≤ p.toNat ∧
      RecRob (erecP m') (fB m + fTop m) (fB m + fTop m') p.toNat c := by
  have hWx := hwx.iwok hW
  have hn3 : 3 ≤ nn.toNat := by
    have := CI.indSize_toNat; have := CI.indCaps_ge; rw [hnn]; split <;> (try split) <;> omega
  have hn5 : kw = 5 → 8 ≤ nn.toNat := fun h5 => by
    subst h5; rw [hnn]; simp at hkw; subst hkw; decide
  obtain ⟨hp, ht', hW', hs0, hwords⟩ := ircT_ok hT hWx hn3 hn5
  have hPx : mx.arr64 DLP = m.arr64 DLP := hwx.dlp
  have eBx := hwx.fB_eq
  have hmx := hwx.top
  have hW'' := hW'.iwok hWx
  have eB' := hW'.fB_eq
  have eT' := hW'.fT_eq
  have hall : ErW (fun i => fTop m ≤ i) m m' := hwx.trans hW' (fun i _ hi => by omega)
  rw [eBx] at hp
  refine ⟨hall, by omega, fun B hB => ?_⟩
  -- unchanged words of `mx` below its top
  have hkeep : ∀ i, fB m + fTop m ≤ i → i < fB m + fTop mx → B i = erecP mx i := fun i h1 h2 => by
    rw [hB i h1 (by omega)]
    obtain ⟨y, rfl⟩ : ∃ y, i = fB m + y := ⟨i - fB m, by omega⟩
    rw [← eBx]; exact hW'.erecP_keep hWx (by omega) (by omega)
  -- the copy's words
  have hnew : ∀ k < nn.toNat, B (p.toNat + k) = some (if k = 2 then q else if k = 7 ∧ kw = 5 then r
      else rdW (m.arr64 DLP) (s + UInt64.ofNat k)) := fun k hk => by
    rw [hB _ (by omega) (by omega), hp, Nat.add_assoc, ← eBx, ← eB', erecP_f hW'' (by omega), eT',
      hwords k hk, hPx]
  refine decCI_of_copy (qW := q) (rW := r) hc hF hP hs0 (fun kk' hkk' k hk => ?_) ?_ (fun j hj => ?_) hl0 (fun h5 => ?_)
  · rw [hkk] at hkk'; cases hkk'
    obtain ⟨hk1, hk2, hk7⟩ := hk
    have hkn : k < nn.toNat := by rw [hnn]; exact hk1
    rw [hnew k hkn]
    rw [ite_eq_right hk2, ite_eq_right (fun ⟨h7, h5⟩ => by subst h5; simp at hkw; exact hk7 hkw.symm h7)]
  · rw [hnew 2 (by omega)]; rfl
  · rw [hkeep _ (by omega) (by omega)]; exact hl j hj
  · have h5' : kk = 5 := by rw [hkk] at h5; cases h5; rfl
    obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hr h5'
    refine ⟨?_, fun x hx => ?_, hr4, hr5⟩
    · have hkw5 : kw = 5 := UInt64.toNat_inj.mp (by rw [hkw, h5']; rfl)
      have := hn5 hkw5
      rw [hnew 7 (by omega)]
      simp [hkw5]
    · rw [hkeep _ (by omega) (by omega)]; exact hr3 x hx

/-- **`ind_rec_copy(s)` copies a front constant record**: a writer above the old top of the flag's
tier, the copy at `p` decoding (robustly, `RecRob`) to the record's constant. -/
theorem ircW_ok {n : Nat} {m m' : Mem} {t : Nat}
    {s p : Word} {c : IConstantInfo} (h : ircW n m s = some (p, m'))
    (hc : decCI (aread (trunc (m.arr64 DLP) t)) s.toNat = some c) (hF : FrontCI c)
    (hP : (m.arr64 DLP).size < 2 ^ 63) (hW : IWOK m) :
    ErW (fun i => fTop m ≤ i) m m' ∧ fB m + fTop m ≤ p.toNat ∧
      RecRob (erecP m') (fB m + fTop m) (fB m + fTop m') p.toNat c := by
  cases n with
  | zero => rw [ircW.eq_1] at h; cases h
  | succ n =>
  rw [ircW.arm1] at h
  -- a whole-record copy (`ind_rec_copy`): the offsets as numbers (`rec_unfold`)
  try simp only [rec_unfold, UInt64.reduceAdd] at h
  obtain ⟨kk, hkk, hk345⟩ := decCI_front_kind hc hF
  obtain ⟨kw, hTk, rfl⟩ : ∃ kw, (trunc (m.arr64 DLP) t)[s.toNat]? = some kw ∧ kw.toNat = kk := by
    simpa [nat?] using hkk
  have hs0n : s.toNat ≠ 0 := fun h0 => by
    rw [h0] at hTk; have := trunc_get_zero hTk; subst this; simp at hk345
  have hkw : rdW (m.arr64 DLP) s = kw := rdW_of_trunc hTk hs0n rfl
  rw [hkw] at h
  have hB := fB_le m
  have hcap := fCap hW
  have hr0 := fTop_le hW
  cases ha1 : erAllocW m (rdW (m.arr64 DLP) (s + 3)) with
  | none => rw [ha1, ircW.k_erec_alloc.none] at h; cases h
  | some x =>
  obtain ⟨q, m1⟩ := x
  rw [ha1, ircW.k_erec_alloc.arm1] at h
  try simp only [rec_unfold, UInt64.reduceAdd] at h
  obtain ⟨hq, ht1, hW1, hok1⟩ := erAlloc_f ha1 hW
  have hw1 := hW1 (fun i => fTop m ≤ i)
  have hP1 : m1.arr64 DLP = m.arr64 DLP := hw1.dlp
  have eB1 := hw1.fB_eq
  have eT1 := hw1.fT_eq
  rw [hP1] at h
  cases hd2 : dindCopyW n m1 q (rdW (m.arr64 DLP) (s + 2)) (rdW (m.arr64 DLP) (s + 3)) with
  | none => rw [hd2, ircW.k_dind_copy.none] at h; cases h
  | some m2 =>
  rw [hd2] at h
  have hq1 : q.toNat = fB m1 + fTop m := by rw [eB1]; exact hq
  have hr1 := fTop_le hok1
  obtain ⟨-, -, hsrc2, hG2⟩ := dindCopyW_get n m1 m2 q _ _ (fTop m) hd2 hq1 (by omega) (fCap hok1)
  have hW2 := dindCopyW_EW hd2 hq1 (by omega) hok1
  have hw2 : ErW (fun i => fTop m ≤ i) m m2 := hw1.trans hW2 (fun i _ hi => by omega)
  have hok2 := hw2.iwok hW
  have hP2 : m2.arr64 DLP = m.arr64 DLP := hw2.dlp
  have eB2 := hw2.fB_eq
  have eT2 := hW2.fT_eq
  have hm2 := hW2.top
  have hl : ∀ j < (rdW (m.arr64 DLP) (s + 3)).toNat, erecP m2 (q.toNat + j) =
      some (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (s + 2) + UInt64.ofNat j)) := by
    intro j hj
    rw [hq, Nat.add_assoc, ← eB2, erecP_f hok2 (by omega), eT2, hG2, ite_eq_left (by omega),
      Nat.add_sub_cancel_left, hP1]
  have hlr : q.toNat + (rdW (m.arr64 DLP) (s + 3)).toNat ≤ fB m + fTop m2 := by omega
  rcases hk345 with h3 | h4 | h5
  · have e : kw = 3 := UInt64.toNat_inj.mp (by rw [h3]; rfl)
    subst e
    rw [ircW.k_dind_copy.arm1 n s 3 q m2 rfl] at h
    try simp only [rec_unfold, UInt64.reduceAdd] at h
    exact irc_fin h hw2 hW hc hF hP hkk rfl (by rfl) (Or.inl rfl) (by omega) hlr hl hsrc2
      (fun h5 => by simp at h5)
  · have e : kw = 4 := UInt64.toNat_inj.mp (by rw [h4]; rfl)
    subst e
    rw [ircW.k_dind_copy.arm2 n s 4 q m2 (by decide) rfl] at h
    try simp only [rec_unfold] at h
    exact irc_fin h hw2 hW hc hF hP hkk rfl (by rfl) (Or.inr (Or.inl rfl)) (by omega) hlr hl
      hsrc2 (fun h5 => by simp at h5)
  · have e : kw = 5 := UInt64.toNat_inj.mp (by rw [h5]; rfl)
    subst e
    have hg : ¬ 1152921504606846976 ≤ rdW (m2.arr64 DLP) (s + 8) := fun hg => by
      rw [ircW.k_dind_copy.abort1 n s 5 q m2 (by decide) (by decide) rfl hg] at h; cases h
    rw [ircW.k_dind_copy.arm3 n s 5 q m2 (by decide) (by decide) rfl hg, hP2] at h
    try simp only [rec_unfold] at h
    rw [hP2] at hg
    have hb : (rdW (m.arr64 DLP) (s + 8)).toNat < 2 ^ 60 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hg); simpa using this
    have h11 : (11 * rdW (m.arr64 DLP) (s + 8)).toNat = 11 * (rdW (m.arr64 DLP) (s + 8)).toNat := by
      rw [UInt64.toNat_mul]; simp; omega
    cases ha3 : erAllocW m2 (11 * rdW (m.arr64 DLP) (s + 8)) with
    | none => rw [ha3, ircW.k_erec_alloc_3.none] at h; cases h
    | some x =>
    obtain ⟨r, m3⟩ := x
    rw [ha3, ircW.k_erec_alloc_3.arm1] at h
    try simp only [rec_unfold] at h
    obtain ⟨hr, ht3, hW3, hok3⟩ := erAlloc_f ha3 hok2
    have hw3 := hW3 (fun i => fTop m2 ≤ i)
    have hP3 : m3.arr64 DLP = m.arr64 DLP := by rw [hw3.dlp, hP2]
    have eB3 := hw3.fB_eq
    rw [hP3] at h
    cases hd4 : dindCopyW n m3 r (rdW (m.arr64 DLP) (s + 7)) (11 * rdW (m.arr64 DLP) (s + 8)) with
    | none => rw [hd4, ircW.k_dind_copy_3.none] at h; cases h
    | some m4 =>
    rw [hd4, ircW.k_dind_copy_3.arm1] at h
    try simp only [rec_unfold, UInt64.reduceAdd] at h
    have hr3 : r.toNat = fB m3 + fTop m2 := by rw [eB3]; exact hr
    have hrr3 := fTop_le hok3
    have hcap2 := fCap hok2
    obtain ⟨-, -, hsrc4, hG4⟩ := dindCopyW_get n m3 m4 r _ _ (fTop m2) hd4 hr3 (by omega) (fCap hok3)
    have hW4 := dindCopyW_EW hd4 hr3 (by omega) hok3
    have hw34 : ErW (fun i => fTop m2 ≤ i) m2 m4 := hw3.trans hW4 (fun i _ hi => by omega)
    have hw4 : ErW (fun i => fTop m ≤ i) m m4 := hw2.trans hw34 (fun i _ hi => by omega)
    have hok4 := hw4.iwok hW
    have eB4 := hw34.fB_eq
    have eT4 := hW4.fT_eq
    have hm4 := hW4.top
    have hrN : (rdW (m.arr64 DLP) (s + 8)).toNat < 2 ^ 60 := hb
    refine irc_fin h hw4 hW hc hF hP hkk rfl (by rfl) (Or.inr (Or.inr rfl)) (by omega)
      (by omega) (fun j hj => ?_) hsrc2 (fun _ => ⟨by omega, by omega, fun x hx => ?_,
        fun h8 => hsrc4 (fun h0 => h8 (by
          apply UInt64.toNat_inj.mp; have := congrArg UInt64.toNat h0; rw [h11] at this; simp at this ⊢; omega)), hb⟩)
    · rw [hq, Nat.add_assoc, ← eB2, hw34.erecP_keep hok2 (by omega) (by omega), eB2, ← Nat.add_assoc,
        ← hq]
      exact hl j hj
    · rw [hr, Nat.add_assoc, ← eB4, erecP_f hok4 (by omega), eT4, hG4, ite_eq_left (by omega),
        Nat.add_sub_cancel_left, hP3]

/-! ## `ind_copy_go` -/

theorem decCIsR_succ (a : Nat → Option Word) (o k : Nat) :
    L.Front.decCIsR a o (k + 1) = (do
      let x ← (do let v ← nat? a o; decCI a v)
      let xs ← L.Front.decCIsR a (o + 1) k
      pure (x :: xs)) := by
  simp only [L.Front.decCIsR, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  simp only [Function.comp_def]
  congr 1; funext j; congr 2; omega

/-- The slot's write after a record's copy (`icgW.k_ind_rec_copy`), then the rest. -/
theorem icgW_krc {n : Nat} {o bo bl p : Word} {m1 m' : Mem}
    (h : icgW.k_ind_rec_copy n o bo bl (some (p, m1)) = some m') :
    icgW n (erecPutMem m1 o p) (o + 1) (bo + 1) (bl - 1) = some m' := by
  by_cases hg : decide ((o &&& 1099511627775).toNat < (m1.arr64 (tierA EREC (o >>> 40))).size) = true
  · rw [icgW.k_ind_rec_copy.arm1 n o bo bl p m1 hg] at h
    revert h
    cases icgW n (erecPutMem m1 o p) (o + 1) (bo + 1) (bl - 1) <;>
      simp [icgW.k_ind_copy_go.none, icgW.k_ind_copy_go.arm1]
  · rw [icgW.k_ind_rec_copy.abort1 n o bo bl p m1 hg] at h; cases h

/-- **`ind_copy_go(o, bo, bl)` copies a front block**: the slots `[x, x + bl)` (`o` the tagged
`fB + x`) and fresh records above the old top written, and in every reader agreeing with the
result from `o` to the new top the slots decode (`decCIsR`) to the block. -/
theorem icgW_ok {t : Nat} (n : Nat) :
    ∀ (m m' : Mem) (o bo bl : Word) (block : List IConstantInfo) (x : Nat), icgW n m o bo bl = some m' →
      decCIs (trunc (m.arr64 DLP) t) bo.toNat bl.toNat = some block → FrontBlock block →
      (m.arr64 DLP).size < 2 ^ 63 → IWOK m → o.toNat = fB m + x → x + bl.toNat ≤ fTop m →
      ErW (fun i => (x ≤ i ∧ i < x + bl.toNat) ∨ fTop m ≤ i) m m' ∧
      ∀ B : Nat → Option Word, (∀ i, fB m + x ≤ i → i < fB m + fTop m' → B i = erecP m' i) →
        L.Front.decCIsR B o.toNat bl.toNat = some block := by
  induction n with
  | zero => intro m m' o bo bl block x h; rw [icgW.eq_1] at h; cases h
  | succ n ih =>
  intro m m' o bo bl block x h hdec hFB hP hW ho hob
  by_cases hl : bl = 0
  · rw [icgW.arm1 n m o bo bl hl] at h
    cases h; subst hl
    simp only [UInt64.toNat_zero, decCIs_zero] at hdec
    cases hdec
    exact ⟨ErW.refl _ _ (fTop_le hW), fun _ _ => rfl⟩
  rw [icgW.arm2 n m o bo bl hl] at h
  have hl0 : bl.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hl1 : (bl - 1).toNat = bl.toNat - 1 := by
    have := bl.toNat_lt; rw [UInt64.toNat_sub]; simp; omega
  obtain ⟨k, hk⟩ : ∃ k, bl.toNat = k + 1 := ⟨bl.toNat - 1, by omega⟩
  rw [hk, decCIs_succ] at hdec
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdec
  obtain ⟨c, ⟨v, hv, hc⟩, cs, hcs, rfl⟩ := hdec
  obtain ⟨w, hw, rfl⟩ : ∃ w, (trunc (m.arr64 DLP) t)[bo.toNat]? = some w ∧ w.toNat = v := by
    simpa [nat?] using hv
  have hFc : FrontCI c := hFB c (by simp)
  have hbo : bo.toNat ≠ 0 := fun h0 => by
    rw [h0] at hw
    have := trunc_get_zero hw; subst this
    obtain ⟨kk, hkk, hk345⟩ := decCI_front_kind hc hFc
    simp only [nat?, Option.map_eq_some_iff, UInt64.toNat_zero] at hkk
    obtain ⟨a, ha, rfl⟩ := hkk
    simp only [aread_apply] at ha
    rw [hw] at ha; cases ha; simp at hk345
  have hrd : rdW (m.arr64 DLP) bo = w := rdW_of_trunc hw hbo rfl
  have hblt := trunc_lt hw hbo
  rw [hrd] at h
  cases hi : ircW n m w with
  | none => rw [hi, icgW.k_ind_rec_copy.none] at h; cases h
  | some y =>
  obtain ⟨p, m1⟩ := y
  rw [hi] at h
  replace h := icgW_krc h
  obtain ⟨hW1, hp1, hR1⟩ := ircW_ok hi hc hFc hP hW
  have hm1 := hW1.top
  have hok1 := hW1.iwok hW
  have eB1 := hW1.fB_eq
  have eT1 := hW1.fT_eq
  have hcap := fCap hW
  have hr0 := fTop_le hW
  have hB := fB_le m
  have ho' : o.toNat = fB m1 + x := by rw [eB1]; exact ho
  have hWs := ErW.put (v := p) ho' (by omega) hok1
  have hoks := hWs.iwok hok1
  obtain ⟨-, eTs, -, eBs, ets⟩ := erPut_ctl m1 o p
  have ho1 : (o + 1).toNat = o.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hbo1 : (bo + 1).toNat = bo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hP2 : (erecPutMem m1 o p).arr64 DLP = m.arr64 DLP := by
    rw [(erPut_f (v := p) ho' (by omega)).2 _ (fT_ne_dlp m1), hW1.dlp]
  obtain ⟨hW3, hB3⟩ := ih (erecPutMem m1 o p) m' (o + 1) (bo + 1) (bl - 1) cs (x + 1) h
    (by rw [hP2, hbo1, hl1, hk]; exact hcs) (fun c' hc' => hFB c' (by simp [hc']))
    (by rw [hP2]; exact hP) hoks (by rw [ho1, eBs, ho']; omega) (by rw [hl1, ets]; omega)
  have ht3 := hW3.top
  have eB3 := hW3.fB_eq
  have eT3 := hW3.fT_eq
  have hok3 := hW3.iwok hoks
  rw [ets] at ht3
  refine ⟨((hW1.mono (fun i hi => Or.inr hi)).trans hWs (fun i _ hi => by left; omega)).trans hW3
    (fun i _ hi => by rw [hl1, ets] at hi; omega), fun B hB' => ?_⟩
  rw [hk, decCIsR_succ]
  -- the slot
  have hslot : B o.toNat = some p := by
    rw [hB' _ (by omega) (by omega), ho', ← eBs, ← eB3, erecP_f hok3 (by omega),
      eT3, hW3.get _ (by rw [ets]; omega) (by rw [ets]; omega), eTs]
    exact erPut_get_same ho' (by rw [hW1.size]; rw [eT1]; omega) (by rw [hW1.size, eT1]; exact hcap)
  have hc' : decCI B p.toNat = some c := hR1 B fun i h1 h2 => by
    rw [hB' i (by omega) (by omega)]
    obtain ⟨y, rfl⟩ : ∃ y, i = fB m + y := ⟨i - fB m, by omega⟩
    rw [← eB1, ← eBs, hW3.erecP_keep hoks (by rw [ets]; omega) (by rw [ets]; omega),
      erecP_f hoks (by rw [ets]; omega), eTs, erPut_get_ne ho' (by omega) (by omega),
      ← erecP_f hok1 (by omega), eBs]
  have hcs' := hB3 B (fun i h1 h2 => hB' i (by rw [eBs, eB1] at h1; omega) (by rw [eBs, eB1] at h2; exact h2))
  rw [ho1, hl1, hk] at hcs'
  simp only [nat?, hslot, Option.map_some, bind, Option.bind_some, hc', Nat.add_sub_cancel] at hcs' ⊢
  rw [hcs']; rfl

/-! ## `ind_block_to_erec` -/

/-- Word `c + 8 i` of `DECL` is word `c - 1` of record `i` (`dw`), for a record that exists. -/
theorem rdW_dwI {D : Array Word} {i c : Word} {k : Nat} (hD : D.size < 2 ^ 63)
    (h0 : dw D i.toNat 0 ≠ 0) (hc : c.toNat = k + 1) (hk : k < 8) :
    rdW D (c + 8 * i) = dw D i.toNat k := by
  have hi : 1 + 8 * i.toNat < D.size := by
    refine Decidable.byContradiction fun hn => h0 ?_
    simp only [dw, Nat.add_zero]
    rw [Array.getElem?_eq_none (by omega)]; rfl
  have e : (c + 8 * i).toNat = 1 + 8 * i.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  simp only [rdW, dw, e]

/-- **`ind_block_to_erec(i)` on the front's inductive record `i`** (model level): the stage
relation kept, the pools grown, only the record tiers and their tops written, and the result a
slice of the record pool (in the flag's tier) decoding to the block. -/
theorem ibeW_ok {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {block : List IConstantInfo}
    {nP : Nat} {vis : Word} {fe : IFEnv} {a : AState}
    (h : ibeW n m i = some (r, m')) (hS : L.Ind.StageR vis fe m a)
    (hdecl : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP) (hFB : FrontBlock block)
    (hD : (m.arr64 DECL).size < 2 ^ 63) (hP : (m.arr64 DLP).size < 2 ^ 63) :
    L.Ind.StageR vis fe m' a ∧ L.Ind.IWGrow m m' ∧ MemFrame [EREC, tier1 EREC] [129, 130] m m' ∧
      r = [r.headD 0, r.tail.headD 0] ∧ (r.tail.headD 0).toNat = block.length ∧
      L.Front.decCIsR (erecP m') (r.headD 0).toNat (r.tail.headD 0).toNat = some block ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat < 2 ^ 64 := by
  have hW := hS.iw
  obtain ⟨h6, -, t, -, hdec⟩ := hdecl
  have h0 : dw (m.arr64 DECL) i.toNat 0 ≠ 0 := by rw [h6]; decide
  have e3 : rdW (m.arr64 DECL) (3 + 8 * i) = dw (m.arr64 DECL) i.toNat 2 := rdW_dwI hD h0 rfl (by decide)
  have e4 : rdW (m.arr64 DECL) (4 + 8 * i) = dw (m.arr64 DECL) i.toNat 3 := rdW_dwI hD h0 rfl (by decide)
  cases n with
  | zero => rw [ibeW.eq_1] at h; cases h
  | succ n =>
  rw [ibeW.arm1, e3, e4] at h
  cases ha : erAllocW m (dw (m.arr64 DECL) i.toNat 3) with
  | none => rw [ha, ibeW.k_erec_alloc.none] at h; cases h
  | some x =>
  obtain ⟨o, m1⟩ := x
  rw [ha, ibeW.k_erec_alloc.arm1] at h
  rcases hg : icgW n m1 o (dw (m.arr64 DECL) i.toNat 2) (dw (m.arr64 DECL) i.toNat 3) with _ | m2 <;>
    simp only [hg, ibeW.k_ind_copy_go.none, ibeW.k_ind_copy_go.arm1, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨ho, ht1, hW1, hok1⟩ := erAlloc_f ha hW
  have hw1 := hW1 (fun j => fTop m ≤ j)
  obtain ⟨hW2, hB2⟩ := icgW_ok n m1 m2 o _ _ block (fTop m) hg (by rw [hw1.dlp]; exact hdec) hFB
    (by rw [hw1.dlp]; exact hP) hok1 (by rw [hw1.fB_eq]; exact ho) (by omega)
  have hw : ErW (fun j => fTop m ≤ j) m m2 := hw1.trans hW2 (fun j _ hj => by omega)
  have hlen : block.length = (dw (m.arr64 DECL) i.toNat 3).toNat := by
    have := L.Ind.mapM_opt_length _ _ _ hdec; simpa using this
  obtain ⟨hgE, hgI⟩ := hw.grow (fun j hj hn => by omega)
  have hcap := fCap hok1
  have hr1 := fTop_le hok1
  have hB := fB_le m
  refine ⟨⟨CheckR.erGrow hS.check hw.frame hgE, hw.iwok hW⟩, hgI, hw.frame, rfl, by simp [hlen], ?_,
    by simp; rw [hw1.fT_eq] at hcap hr1; omega⟩
  simp only [List.headD_cons, List.tail_cons]
  exact hB2 (erecP m2) (fun j _ _ => rfl)

/-- `ind_block_to_erec`'s lookups. -/
structure IbeProg (p : Prog) : Prop where
  erec_alloc : p.lookup "erec_alloc" = some erecAlloc
  erec_put : p.lookup "erec_put" = some L.Ind.erecPut
  dind_copy : p.lookup "dind_copy" = some dindCopy
  ind_rec_copy : p.lookup "ind_rec_copy" = some indRecCopy
  ind_copy_go : p.lookup "ind_copy_go" = some indCopyGo
  ind_block_to_erec : p.lookup "ind_block_to_erec" = some indBlockToErec

/-- **`ind_block_to_erec(i)` copies the front's inductive record `i` into `EREC`** (`IndDeclAt`,
a block of the front's shape `FrontBlock`): the stage relation kept at the same twin state, the
pools grown, only the record tiers and their tops written, and the result `[o, l]` a slice of
record pointers in the record pool that decodes (`decCIsR`, in `erecP`) to the block. -/
theorem indBlockToErec_ok {p : Prog} (hp : IbeProg p) {n : Nat} {m m' : Mem} {i : Word}
    {r : List Word} {block : List IConstantInfo} {nP : Nat}
    {vis : Word} {fe : IFEnv} {a : AState}
    (hc : callW p n "ind_block_to_erec" [i] m = some (r, m')) (hS : L.Ind.StageR vis fe m a)
    (hdecl : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP) (hFB : FrontBlock block)
    (hD : (m.arr64 DECL).size < 2 ^ 63) (hP : (m.arr64 DLP).size < 2 ^ 63) :
    L.Ind.StageR vis fe m' a ∧ L.Ind.IWGrow m m' ∧ MemFrame [EREC, tier1 EREC] [129, 130] m m' ∧
      r = [r.headD 0, r.tail.headD 0] ∧ (r.tail.headD 0).toNat = block.length ∧
      L.Front.decCIsR (erecP m') (r.headD 0).toNat (r.tail.headD 0).toNat = some block ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat < 2 ^ 64 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (indBlockToErec_specW p hp.erec_alloc hp.erec_put hp.dind_copy hp.ind_rec_copy hp.ind_copy_go
      hp.ind_block_to_erec n ⟨m, Locals.init []⟩ i) hc
  exact ibeW_ok hW hS hdecl hFB hD hP

end L.Arena
