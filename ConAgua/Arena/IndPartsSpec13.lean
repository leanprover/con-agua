import ConAgua.Arena.IndPartsSpec12
import ConAgua.Arena.DeclHeader

/-!
# Refinements of `IndParts`, part 13 (lane `indproofs2`, helper `parts`): `blockShape?`'s pins

The reserved-name and level-parameter pins (`block_shape_pins_formers`/`_recs`/`_ctors`/`_ok`,
pure in the twin: one `Bool`), and the eliminator (`block_shape_large`). Shared pieces: a constant's
level parameters copied by `er_to_iw` (`partsLpsCopy`), `reserved_contains` against the twin's
`reservedBasisNames` (`partsResCont`).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `reserved_contains` -/

theorem resFromW_hit (n : Nat) : ∀ (m : Mem) (x j : Word) (b : Word), j.toNat ≤ 16 →
    resFromW n m x j = some b → b ≠ 0 → ∃ i, j.toNat ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x := by
  induction n with
  | zero => intro m x j b _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j b hj h hb
    rw [resFromW_step] at h
    by_cases h16 : 16 ≤ j
    · rw [ite_eq_left h16] at h; simp at h; exact absurd h.symm hb
    rw [ite_eq_right h16] at h
    have hj16 : j.toNat < 16 := by rw [UInt64.le_iff_toNat_le] at h16; simp at h16; omega
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · refine ⟨j.toNat, Nat.le_refl _, hj16, ?_⟩
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he
    rw [ite_eq_right he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨i, hi1, hi2, hi3⟩ := ih m x (j + 1) b (by omega) h hb
    exact ⟨i, by omega, hi2, hi3⟩

theorem resFromW_01 (n : Nat) : ∀ (m : Mem) (x j : Word) (b : Word), resFromW n m x j = some b →
    b = 0 ∨ b = 1 := by
  induction n with
  | zero => intro m x j b h; simp [resFromW] at h
  | succ n ih =>
    intro m x j b h
    rw [resFromW_step] at h
    split at h
    · simp at h; exact Or.inl h.symm
    split at h
    · simp at h; exact Or.inr h.symm
    exact ih _ _ _ _ h

/-- **`reserved_contains` is the twin's `reservedBasisNames.contains`.** -/
theorem partsResCont {m : Mem} {a : AState} {n : Nat} {x b : Word} (hx : x.toNat < 2 ^ 32)
    (h : resContW n m x = some b) (hP : PinsR m a.pins) :
    ∃ R, reservedBasisNames.run a = .ok (R, a) ∧ b = if R.contains (decI x) then 1 else 0 := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at h; simp at h
  rw [ite_eq_right h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  rcases resFromW_01 n m x 0 b h with rfl | rfl
  · have hm := resFromW_miss n m x 0 (by simp) h
    have : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, e⟩ := hc
      exact hm i (Nat.zero_le _) hi ((decI_eq_iff _ (hF.reserved_lt i hi) _).mp e ▸ decI_word_self x hx)
    rw [this]; rfl
  · obtain ⟨i, -, hi, he⟩ := resFromW_hit n m x 0 1 (by simp) h (by decide)
    have : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = true := by
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
      exact ⟨i, hi, by rw [he]⟩
    rw [this]; rfl

/-! ## A constant's level parameters, copied -/

theorem erCopyW_zero (n : Nat) (m : Mem) (d o o' : Word) : erCopyW n m d o 0 = erCopyW n m d o' 0 := by
  cases n <;> rfl

theorem partsErLt {m : Mem} {i v : Nat} (h : nat? (erA (truncM m)) i = some v) : i < erTop m := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, -⟩ := h; exact (truncM_er_get hx).1

theorem partsHslice_last {k : IdxKind} {a : Array Word} : ∀ (l o : Nat) (xs : List (Idx k)),
    hslice? a o (l + 1) = some xs → ∃ w, a[o + l]? = some w
  | 0, o, xs, h => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, -⟩ := h
    obtain ⟨w, hw, -, -⟩ := hd?_some hx
    exact ⟨w, by simpa using hw⟩
  | l + 1, o, xs, h => by
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, -, ys, hys, -⟩ := h
    obtain ⟨w, hw⟩ := partsHslice_last l (o + 1) ys hys
    exact ⟨w, by rw [show o + (l + 1) = o + 1 + l by omega]; exact hw⟩

theorem partsErToIw_zero (n : Nat) (m : Mem) (o : Word) : erToIwW n m o 0 = erToIwW n m 0 0 := by
  simp only [erToIwW]
  rcases allocW m 0 with _ | ⟨q, m1⟩
  · rfl
  · simp only; rw [erCopyW_zero _ _ _ o 0]

/-- **`er_to_iw` of an `EREC` handle slice decoded below the tops.** -/
theorem partsSliceCopy {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {o l : Word} {r : List Word} {xs : List NIdx} (h : erToIwW n m o l = some (r, m'))
    (hS : StageR dn vis fe m a) (hs : hslice? (erA (truncM m)) o.toNat l.toNat = some xs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  have hdl : ∀ {r m'} (o : Word), erToIwW n m o l = some (r, m') →
      o.toNat + l.toNat ≤ (m.arr64 EREC).size → hslice? (erA m) o.toNat l.toNat = some xs →
      StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
    intro r m' o h hsrc hs
    have hroom : iwTop m + l.toNat ≤ (m.arr64 IW).size := by
      simp only [erToIwW] at h
      rcases hal : allocW m l with _ | x
      · rw [hal] at h; cases h
      obtain ⟨hq', -, hr⟩ := allocW_facts hal hsz
      rw [hq'] at hr; simp only [iwTop]; omega
    obtain ⟨hr, hd, hg, hf, -, ht⟩ := erToIwW_dec (k := IdxKind.name) h hsz hc hEs hsrc
    subst hr
    simp only [List.headD_cons, List.tail_cons]
    refine ⟨stage_frame_iw hS hf (by simp only [iwTop] at ht hroom ⊢; omega), hg, ?_, ht⟩
    rw [hd, hs]
  have hs' : hslice? (erA m) o.toNat l.toNat = some xs := ArrExt.hslice? (IWGrow.refl m).truncExt.2 hs
  rcases Nat.eq_zero_or_pos l.toNat with h0 | hpos
  · have hl0 : l = 0 := UInt64.toNat_inj.mp (by simpa using h0)
    subst hl0
    rw [partsErToIw_zero] at h
    have : xs = [] := by simpa [hslice?] using hs.symm
    subst this
    exact hdl 0 h (by simp) (by simp [hslice?])
  · obtain ⟨w, hw⟩ := partsHslice_last (l.toNat - 1) o.toNat xs (by rw [Nat.sub_add_cancel hpos]; exact hs)
    have := (truncM_er_get hw).1
    have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
    exact hdl _ h (by omega) hs'

/-- `er_to_iw` of a constant's level-parameter slice (decoded below the tops), as a handle slice. -/
theorem partsLpsCopy {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Nat} {cv : IConstantVal} {r : List Word}
    (h : erToIwW n m (rdW (m.arr64 EREC) (UInt64.ofNat q + 1)) (rdW (m.arr64 EREC) (UInt64.ofNat q + 2)) =
      some (r, m'))
    (hS : StageR dn vis fe m a) (hcv : DecB (fun m => decCVp m q) m cv) (hq : q < 2 ^ 64) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  have hcv' : decCV (erA (truncM m)) q = some cv := hcv
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv'
  obtain ⟨nm, -, lv, hlv, ce, -, hcvT⟩ := hcv'
  have hlvE : lv = cv.levelParams := by rw [← hcvT]
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho, l', hl, hsl⟩ := hlv
  have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
  have hq2lt := partsErLt hl
  have hqw : (UInt64.ofNat q).toNat = q := UInt64.toNat_ofNat_of_lt' hq
  obtain ⟨w1, hw1b, -⟩ := partsErRd (IWGrow.refl m) ho (w := UInt64.ofNat q + 1)
    (by rw [UInt64.toNat_add, hqw]; simp; omega)
  obtain ⟨w2, hw2b, -⟩ := partsErRd (IWGrow.refl m) hl (w := UInt64.ofNat q + 2)
    (by rw [UInt64.toNat_add, hqw]; simp; omega)
  rw [w1, w2] at h
  exact partsSliceCopy h hS
    (by rw [UInt64.toNat_ofNat_of_lt' hw1b, UInt64.toNat_ofNat_of_lt' hw2b, hsl, hlvE])

/-! ## The pins: models -/

/-- After the recursive call: its answer. -/
def pinK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0], m2)

mutual
/-- **The model of `block_shape_pins_formers`.** -/
def bpfW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, cto, ctl, lo, ll =>
    if ctl = 0 then some ([1], m)
    else bpfK1 n cto ctl lo ll (rdW (m.arr64 IW) cto) m
      (resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cto)))
/-- After `reserved_contains`. -/
def bpfK1 (n : Nat) (cto ctl lo ll cv : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some b =>
    if b ≠ 0 then some ([0], m)
    else bpfK2 n cto ctl lo ll (erToIwW n m (rdW (m.arr64 EREC) (cv + 1)) (rdW (m.arr64 EREC) (cv + 2)))
/-- After `er_to_iw`. -/
def bpfK2 (n : Nat) (cto ctl lo ll : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m1) => bpfK3 n cto ctl lo ll m1 (eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll)
/-- After `sl_eq`. -/
def bpfK3 (n : Nat) (cto ctl lo ll : Word) (m1 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => if e = 0 then some ([0], m1) else pinK4 (bpfW n m1 (cto + 1) (ctl - 1) lo ll)
end

section arms
variable (n : Nat) (m m1 : Mem) (cto ctl lo ll cv b e : Word) (rp : List Word)
theorem bpfW_nil (h : ctl = 0) : bpfW (n + 1) m cto ctl lo ll = some ([1], m) := by simp [bpfW, h]
theorem bpfW_cons (h : ctl ≠ 0) : bpfW (n + 1) m cto ctl lo ll = bpfK1 n cto ctl lo ll (rdW (m.arr64 IW) cto) m
    (resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cto))) := by simp [bpfW, h]
theorem bpfK1_res (h : b ≠ 0) : bpfK1 n cto ctl lo ll cv m (some b) = some ([0], m) := by
  simp only [bpfK1]; exact ite_eq_left h
theorem bpfK1_ok (h : ¬ b ≠ 0) : bpfK1 n cto ctl lo ll cv m (some b) =
    bpfK2 n cto ctl lo ll (erToIwW n m (rdW (m.arr64 EREC) (cv + 1)) (rdW (m.arr64 EREC) (cv + 2))) := by
  simp only [bpfK1]; exact ite_eq_right h
theorem bpfK2_some : bpfK2 n cto ctl lo ll (some (rp, m1)) =
    bpfK3 n cto ctl lo ll m1 (eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll) := by simp [bpfK2]
theorem bpfK3_ne (h : e = 0) : bpfK3 n cto ctl lo ll m1 (some e) = some ([0], m1) := by
  simp only [bpfK3]; exact ite_eq_left h
theorem bpfK3_eq (h : ¬ e = 0) : bpfK3 n cto ctl lo ll m1 (some e) =
    pinK4 (bpfW n m1 (cto + 1) (ctl - 1) lo ll) := by simp only [bpfK3]; exact ite_eq_right h
theorem pinK4_some : pinK4 (some (rp, m1)) = some ([rp.headD 0], m1) := rfl
end arms
attribute [ind_grind] bpfW_nil bpfW_cons bpfK1_res bpfK1_ok bpfK2_some bpfK3_ne bpfK3_eq pinK4_some

/-- **The model of `block_shape_pins_recs`.** -/
def bprW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, ro, rl =>
    if rl = 0 then some ([1], m)
    else match resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro))) with
      | none => none
      | some b => if b ≠ 0 then some ([0], m) else pinK4 (bprW n m (ro + 1) (rl - 1))

section arms
variable (n : Nat) (m : Mem) (ro rl : Word)
theorem bprW_nil (h : rl = 0) : bprW (n + 1) m ro rl = some ([1], m) := by simp [bprW, h]
theorem bprW_cons (h : rl ≠ 0) : bprW (n + 1) m ro rl =
    (match resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro))) with
      | none => none
      | some b => if b ≠ 0 then some ([0], m) else pinK4 (bprW n m (ro + 1) (rl - 1))) := by
  simp only [bprW]; rw [ite_eq_right h]
end arms
attribute [ind_grind] bprW_nil bprW_cons

mutual
/-- **The model of `block_shape_pins_ctors`.** -/
def bpcW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, nP, cso, csl, lo, ll =>
    if csl = 0 then some ([1], m)
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) cso + 1) ≠ nP then some ([0], m)
    else bpcK1 n nP cso csl lo ll (rdW (m.arr64 IW) (rdW (m.arr64 IW) cso)) m
      (resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cso))))
/-- After `reserved_contains`. -/
def bpcK1 (n : Nat) (nP cso csl lo ll cv : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some b =>
    if b ≠ 0 then some ([0], m)
    else bpcK2 n nP cso csl lo ll (erToIwW n m (rdW (m.arr64 EREC) (cv + 1)) (rdW (m.arr64 EREC) (cv + 2)))
/-- After `er_to_iw`. -/
def bpcK2 (n : Nat) (nP cso csl lo ll : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m1) => bpcK3 n nP cso csl lo ll m1 (eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll)
/-- After `sl_eq`. -/
def bpcK3 (n : Nat) (nP cso csl lo ll : Word) (m1 : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some e => if e = 0 then some ([0], m1) else pinK4 (bpcW n m1 nP (cso + 1) (csl - 1) lo ll)
end

section arms
variable (n : Nat) (m m1 : Mem) (nP cso csl lo ll cv b e : Word) (rp : List Word)
theorem bpcW_nil (h : csl = 0) : bpcW (n + 1) m nP cso csl lo ll = some ([1], m) := by simp [bpcW, h]
theorem bpcW_np (h : csl ≠ 0) (h2 : rdW (m.arr64 IW) (rdW (m.arr64 IW) cso + 1) ≠ nP) :
    bpcW (n + 1) m nP cso csl lo ll = some ([0], m) := by simp [bpcW, h, h2]
theorem bpcW_cons (h : csl ≠ 0) (h2 : ¬ rdW (m.arr64 IW) (rdW (m.arr64 IW) cso + 1) ≠ nP) :
    bpcW (n + 1) m nP cso csl lo ll = bpcK1 n nP cso csl lo ll (rdW (m.arr64 IW) (rdW (m.arr64 IW) cso)) m
      (resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cso)))) := by
  simp only [bpcW]; rw [ite_eq_right h, ite_eq_right h2]
theorem bpcK1_res (h : b ≠ 0) : bpcK1 n nP cso csl lo ll cv m (some b) = some ([0], m) := by
  simp only [bpcK1]; exact ite_eq_left h
theorem bpcK1_ok (h : ¬ b ≠ 0) : bpcK1 n nP cso csl lo ll cv m (some b) =
    bpcK2 n nP cso csl lo ll (erToIwW n m (rdW (m.arr64 EREC) (cv + 1)) (rdW (m.arr64 EREC) (cv + 2))) := by
  simp only [bpcK1]; exact ite_eq_right h
theorem bpcK2_some : bpcK2 n nP cso csl lo ll (some (rp, m1)) =
    bpcK3 n nP cso csl lo ll m1 (eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll) := by simp [bpcK2]
theorem bpcK3_ne (h : e = 0) : bpcK3 n nP cso csl lo ll m1 (some e) = some ([0], m1) := by
  simp only [bpcK3]; exact ite_eq_left h
theorem bpcK3_eq (h : ¬ e = 0) : bpcK3 n nP cso csl lo ll m1 (some e) =
    pinK4 (bpcW n m1 nP (cso + 1) (csl - 1) lo ll) := by simp only [bpcK3]; exact ite_eq_right h
end arms
attribute [ind_grind] bpcW_nil bpcW_np bpcW_cons bpcK1_res bpcK1_ok bpcK2_some bpcK3_ne bpcK3_eq

section spec
variable (p : Prog) (hP : IndPartsProg4 p) (hrf : p.lookup "reserved_from" = some reservedFrom)
  (hrc : p.lookup "reserved_contains" = some reservedContains) (hec : p.lookup "er_copy" = some erCopy)
  (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
include hP hrf hrc

include hec het hseq in
theorem bpf_spec (hp : p.lookup "block_shape_pins_formers" = some blockShapePinsFormers) (n : Nat) :
    ∀ (s₀ : St) (cto ctl lo ll : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_pins_formers" [cto, ctl, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ bpfW n s₀.mem cto ctl lo ll = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ cto ctl lo ll; rw [invoke_eq _ hp]; simp only [callFn, blockShapePinsFormers]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cto ctl lo ll
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapePinsFormers]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, resCont_spec p hrf hrc n,
        erToIw_specW p hP.alloc hec het n, slEq_spec p hseq n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem bpr_spec (hp : p.lookup "block_shape_pins_recs" = some blockShapePinsRecs) (n : Nat) :
    ∀ (s₀ : St) (ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_pins_recs" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ bprW n s₀.mem ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ ro rl; rw [invoke_eq _ hp]; simp only [callFn, blockShapePinsRecs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ro rl
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapePinsRecs]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, resCont_spec p hrf hrc n, ih] <;>
      finish (gen := 20) [rdW_eq]

include hec het hseq in
theorem bpc_spec (hp : p.lookup "block_shape_pins_ctors" = some blockShapePinsCtors) (n : Nat) :
    ∀ (s₀ : St) (nP cso csl lo ll : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_pins_ctors" [nP, cso, csl, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ bpcW n s₀.mem nP cso csl lo ll = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ nP cso csl lo ll; rw [invoke_eq _ hp]; simp only [callFn, blockShapePinsCtors]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP cso csl lo ll
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapePinsCtors]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, resCont_spec p hrf hrc n,
        erToIw_specW p hP.alloc hec het n, slEq_spec p hseq n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

/-! ## The pins: relations -/

/-- **A constant's level parameters compared with `lps`** (`er_to_iw`, then `sl_eq`). -/
theorem partsLpsEq {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m1 : Mem} {q : Nat} {cv : IConstantVal} {rp : List Word} {lo ll e : Word} {lps : List NIdx}
    (h : erToIwW n m (rdW (m.arr64 EREC) (UInt64.ofNat q + 1)) (rdW (m.arr64 EREC) (UInt64.ofNat q + 2)) =
      some (rp, m1))
    (he : eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll = some e)
    (hS : StageR dn vis fe m a) (hcv : DecB (fun m => decCVp m q) m cv) (hq : q < 2 ^ 64)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m) :
    StageR dn vis fe m1 a ∧ IWGrow m m1 ∧ e = if cv.levelParams == lps then 1 else 0 := by
  obtain ⟨hS1, hg1, hd1, ht1⟩ := partsLpsCopy h hS hcv hq
  have hT : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
  obtain ⟨ws1, hs1, hn1, hl1⟩ := slR_of_decHL m1 _ _ _ hd1 (by omega)
  rw [ofNat_toNat_word, ofNat_toNat_word] at hs1
  have hl' : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow3 hg1 hlb]; exact hl
  obtain ⟨ws2, hs2, hn2, hl2⟩ := slR_of_decHL m1 _ _ _ hl' (by have := hg1.1; omega)
  rw [ofNat_toNat_word, ofNat_toNat_word] at hs2
  have hres := eqW_ok n m1 _ _ _ _ e ws1 ws2 hs1 hs2 he
  refine ⟨hS1, hg1, ?_⟩
  rw [hn1, hn2, map_decI_beq ws1 ws2 hl1 hl2, hres]
  by_cases hw : ws1 = ws2 <;> simp [hw]

theorem partsResR {a : AState} {R R' : List NIdx} (h : reservedBasisNames.run a = .ok (R, a))
    (h' : reservedBasisNames.run a = .ok (R', a)) : R' = R := by
  rw [h] at h'; simp only [Except.ok.injEq, Prod.mk.injEq] at h'; exact h'.1.symm

theorem ipIte01_ne {c : Bool} {b : Word} (h : b = if c then 1 else 0) : b ≠ 0 ↔ c = true := by
  subst h; cases c <;> simp

theorem ipIte01_eq {c : Bool} {b : Word} (h : b = if c then 1 else 0) : b = 0 ↔ c = false := by
  subst h; cases c <;> simp

/-- **`block_shape_pins_formers`**: no former's name reserved, every former at `lps`. -/
theorem bpfW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {lo ll : Word}
    {lps R : List NIdx} (hR : reservedBasisNames.run a = .ok (R, a)) (n : Nat) :
    ∀ (m m' : Mem) (cto ctl : Word) (cvTs : List IConstantVal) (r : List Word),
    bpfW n m cto ctl lo ll = some (r, m') → StageR dn vis fe m a → PSlR decCVp cvTs cto ctl m →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      r = [if cvTs.all (fun c => !R.contains c.name && c.levelParams == lps) then 1 else 0] := by
  induction n with
  | zero => intro m m' cto ctl cvTs r h; simp [bpfW] at h
  | succ n ih =>
    intro m m' cto ctl cvTs r h hS hts hl hlb
    by_cases hc : ctl = 0
    · rw [bpfW_nil n m cto ctl lo ll hc] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc; rw [partsPSl_nil hts]
      exact ⟨hS, IWGrow.refl _, rfl⟩
    rw [bpfW_cons n m cto ctl lo ll hc] at h
    obtain ⟨pc, cv, ts', rfl, hw, hpb, hcv, hts'⟩ := partsPSl_cons hts hc
    rw [hw] at h
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) hcv hpb
    obtain ⟨b, hb, h⟩ := ipK_inv1 h (by simp [bpfK1])
    obtain ⟨R', hR', hbv⟩ := partsResCont hnl hb hS.1.pins
    rw [partsResR hR hR', hne] at hbv
    by_cases hb0 : b ≠ 0
    · rw [bpfK1_res n m cto ctl lo ll _ b hb0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : R.contains cv.name = true := (ipIte01_ne hbv).mp hb0
      exact ⟨hS, IWGrow.refl _, by simp only [List.all_cons, this, Bool.not_true, Bool.false_and]; rfl⟩
    rw [bpfK1_ok n m cto ctl lo ll _ b hb0] at h
    have hcn : R.contains cv.name = false := Bool.eq_false_iff.mpr (mt (ipIte01_ne hbv).mpr hb0)
    obtain ⟨rp, m1, h1, h⟩ := ipK_inv h (by simp [bpfK2])
    rw [bpfK2_some] at h
    obtain ⟨e, he, h⟩ := ipK_inv1 h (by simp [bpfK3])
    obtain ⟨hS1, hg1, hev⟩ := partsLpsEq h1 he hS hcv hpb hl hlb
    by_cases he0 : e = 0
    · rw [bpfK3_ne n m1 cto ctl lo ll e he0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : (cv.levelParams == lps) = false := (ipIte01_eq hev).mp he0
      exact ⟨hS1, hg1, by simp only [List.all_cons, this, Bool.and_false, Bool.false_and]; rfl⟩
    rw [bpfK3_eq n m1 cto ctl lo ll e he0] at h
    have heq : (cv.levelParams == lps) = true := by simpa using mt (ipIte01_eq hev).mpr he0
    rcases h2 : bpfW n m1 (cto + 1) (ctl - 1) lo ll with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [pinK4_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hr2⟩ := ih m1 m2 (cto + 1) (ctl - 1) ts' r2 h2 hS1 (hts'.grow (fun _ => OMono.decCVp _) hg1)
      (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.1)
    refine ⟨hS2, hg1.trans hg2, ?_⟩
    rw [hr2]; simp only [List.all_cons, hcn, heq, Bool.not_false, Bool.true_and]; rfl

/-- **`block_shape_pins_recs`**: no recursor's name reserved. -/
theorem bprW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {R : List NIdx} (hR : reservedBasisNames.run a = .ok (R, a)) (n : Nat) :
    ∀ (m m' : Mem) (ro rl : Word) (rs : List (IConstantVal × Nat × Nat × List IRecRule)) (r : List Word),
    bprW n m ro rl = some (r, m') → StageR dn vis fe m a → PSlR decSR rs ro rl m →
    m' = m ∧ r = [if rs.all (fun r => !R.contains r.1.name) then 1 else 0] := by
  induction n with
  | zero => intro m m' ro rl rs r h; simp [bprW] at h
  | succ n ih =>
    intro m m' ro rl rs r h hS hrs
    by_cases hc : rl = 0
    · rw [bprW_nil n m ro rl hc] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc; rw [partsPSl_nil hrs]
      exact ⟨rfl, rfl⟩
    rw [bprW_cons n m ro rl hc] at h
    obtain ⟨pc, ⟨cv, mI, rP, rules⟩, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hc
    obtain ⟨⟨cvp, hcvp, hcv⟩, -, -⟩ := decSR_fields (show decSR (truncM m) pc = _ from hrs0)
    obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp (UInt64.toNat_ofNat_of_lt' hpb)
    rw [hw, hcw] at h
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) (show DecB (fun m => decCVp m cvp) m cv from hcv) hcvb
    rcases hb : resContW n m (rdW (m.arr64 EREC) (UInt64.ofNat cvp)) with _ | b <;> rw [hb] at h
    · cases h
    simp only at h
    obtain ⟨R', hR', hbv⟩ := partsResCont hnl hb hS.1.pins
    rw [partsResR hR hR', hne] at hbv
    by_cases hb0 : b ≠ 0
    · rw [ite_eq_left hb0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : R.contains cv.name = true := (ipIte01_ne hbv).mp hb0
      exact ⟨rfl, by simp only [List.all_cons, this, Bool.not_true, Bool.false_and]; rfl⟩
    rw [ite_eq_right hb0] at h
    have hcn : R.contains cv.name = false := Bool.eq_false_iff.mpr (mt (ipIte01_ne hbv).mpr hb0)
    rcases h2 : bprW n m (ro + 1) (rl - 1) with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [pinK4_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, hr2⟩ := ih m m2 (ro + 1) (rl - 1) rs' r2 h2 hS hrs'
    refine ⟨rfl, ?_⟩
    rw [hr2]; simp only [List.all_cons, hcn, Bool.not_false, Bool.true_and]; rfl

/-- **`block_shape_pins_ctors`**: every constructor at `nP` and `lps`, no name reserved. -/
theorem bpcW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {nP lo ll : Word}
    {lps R : List NIdx} (hR : reservedBasisNames.run a = .ok (R, a)) (n : Nat) :
    ∀ (m m' : Mem) (cso csl : Word) (cs : List (IConstantVal × Nat × Nat)) (r : List Word),
    bpcW n m nP cso csl lo ll = some (r, m') → StageR dn vis fe m a → PSlR decSC cs cso csl m →
    decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      r = [if cs.all (fun c => c.2.1 == nP.toNat && c.1.levelParams == lps && !R.contains c.1.name)
        then 1 else 0] := by
  induction n with
  | zero => intro m m' cso csl cs r h; simp [bpcW] at h
  | succ n ih =>
    intro m m' cso csl cs r h hS hcs hl hlb
    by_cases hc : csl = 0
    · rw [bpcW_nil n m nP cso csl lo ll hc] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc; rw [partsPSl_nil hcs]
      exact ⟨hS, IWGrow.refl _, rfl⟩
    obtain ⟨pc, ⟨cv0, nP0, nF0⟩, cs', rfl, hw, hpb, hc0, hcs'⟩ := partsPSl_cons hcs hc
    have hd0 : decSC (truncM m) pc = some (cv0, nP0, nF0) := hc0
    simp only [decSC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hd0
    obtain ⟨cvp, hcvp, cv, hcv, nP1, hnP, nF, hnF, e1, e2, e3⟩ := hd0
    subst e1 e2 e3
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hp1 : (UInt64.ofNat pc + 1).toNat = pc + 1 := by
      have := partsIwLt hnP; rw [UInt64.toNat_add, hpw]; simp; omega
    obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp hpw
    obtain ⟨hpw1, hnPb, -⟩ := partsIwRd hnP hp1
    have hnpeq : (UInt64.ofNat nP1 = nP) ↔ (nP1 == nP.toNat) = true := by
      simp only [beq_iff_eq]
      constructor
      · intro e; rw [← e, UInt64.toNat_ofNat_of_lt' hnPb]
      · intro e; rw [e, ofNat_toNat_word]
    by_cases hnp : rdW (m.arr64 IW) (rdW (m.arr64 IW) cso + 1) ≠ nP
    · rw [bpcW_np n m nP cso csl lo ll hc hnp] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rw [hw, hpw1] at hnp
      have : (nP1 == nP.toNat) = false := Bool.eq_false_iff.mpr (mt hnpeq.mpr hnp)
      exact ⟨hS, IWGrow.refl _, by simp only [List.all_cons, this, Bool.false_and]; rfl⟩
    rw [bpcW_cons n m nP cso csl lo ll hc hnp] at h
    have hnpt : (nP1 == nP.toNat) = true := by
      rw [hw, hpw1] at hnp; exact hnpeq.mp (by simpa using hnp)
    rw [hw, hcw] at h
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) (show DecB (fun m => decCVp m cvp) m cv from hcv) hcvb
    obtain ⟨b, hb, h⟩ := ipK_inv1 h (by simp [bpcK1])
    obtain ⟨R', hR', hbv⟩ := partsResCont hnl hb hS.1.pins
    rw [partsResR hR hR', hne] at hbv
    by_cases hb0 : b ≠ 0
    · rw [bpcK1_res n m nP cso csl lo ll _ b hb0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : R.contains cv.name = true := (ipIte01_ne hbv).mp hb0
      exact ⟨hS, IWGrow.refl _, by simp only [List.all_cons, this, Bool.not_true, Bool.and_false, Bool.false_and]; rfl⟩
    rw [bpcK1_ok n m nP cso csl lo ll _ b hb0] at h
    have hcn : R.contains cv.name = false := Bool.eq_false_iff.mpr (mt (ipIte01_ne hbv).mpr hb0)
    obtain ⟨rp, m1, h1, h⟩ := ipK_inv h (by simp [bpcK2])
    rw [bpcK2_some] at h
    obtain ⟨e, he, h⟩ := ipK_inv1 h (by simp [bpcK3])
    obtain ⟨hS1, hg1, hev⟩ := partsLpsEq h1 he hS (show DecB (fun m => decCVp m cvp) m cv from hcv) hcvb hl hlb
    by_cases he0 : e = 0
    · rw [bpcK3_ne n m1 nP cso csl lo ll e he0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : (cv.levelParams == lps) = false := (ipIte01_eq hev).mp he0
      exact ⟨hS1, hg1, by simp only [List.all_cons, this, Bool.and_false, Bool.false_and]; rfl⟩
    rw [bpcK3_eq n m1 nP cso csl lo ll e he0] at h
    have heq : (cv.levelParams == lps) = true := by simpa using mt (ipIte01_eq hev).mpr he0
    rcases h2 : bpcW n m1 nP (cso + 1) (csl - 1) lo ll with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [pinK4_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hr2⟩ := ih m1 m2 (cso + 1) (csl - 1) cs' r2 h2 hS1 (hcs'.grow decSC_mono hg1)
      (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.1)
    refine ⟨hS2, hg1.trans hg2, ?_⟩
    rw [hr2]; simp only [List.all_cons, hcn, heq, hnpt, Bool.not_false, Bool.true_and, Bool.and_true]; rfl

/-! ## `block_shape_pins_ok` -/

/-- **The model of `block_shape_pins_ok`** (at exec fuel `n + 1`). -/
def bpoW (n : Nat) (m : Mem) (nP cto ctl lo ll ro rl cso csl : Word) : Option (List Word × Mem) :=
  match bpfW n m cto ctl lo ll with
  | none => none
  | some (ra, m1) =>
    if ra.headD 0 = 0 then some ([0], m1)
    else match bprW n m1 ro rl with
      | none => none
      | some (rb, m2) =>
        if rb.headD 0 = 0 then some ([0], m2)
        else match bpcW n m2 nP cso csl lo ll with
          | none => none
          | some (rc, m3) => some ([rc.headD 0], m3)

theorem bpo_spec (p : Prog) (hP : IndPartsProg4 p) (hrf : p.lookup "reserved_from" = some reservedFrom)
    (hrc : p.lookup "reserved_contains" = some reservedContains) (hec : p.lookup "er_copy" = some erCopy)
    (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
    (hf : p.lookup "block_shape_pins_formers" = some blockShapePinsFormers)
    (hr : p.lookup "block_shape_pins_recs" = some blockShapePinsRecs)
    (hc : p.lookup "block_shape_pins_ctors" = some blockShapePinsCtors)
    (hp : p.lookup "block_shape_pins_ok" = some blockShapePinsOk) (n : Nat) (s₀ : St)
    (nP cto ctl lo ll ro rl cso csl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_pins_ok" [nP, cto, ctl, lo, ll, ro, rl, cso, csl]
    ⦃fun r s' => LocEq s' s₀ ∧ bpoW n s₀.mem nP cto ctl lo ll ro rl cso csl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapePinsOk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, bpf_spec p hP hrf hrc hec het hseq hf n,
      bpr_spec p hP hrf hrc hr n, bpc_spec p hP hrf hrc hec het hseq hc n] <;>
    finish (gen := 20) [bpoW]

theorem partsW01 {r : List Word} {b : Bool} (h : r = [if b then 1 else 0]) : (r.headD 0 = 0) ↔ b = false := by
  subst h; cases b <;> simp

/-- **`block_shape_pins_ok`**: the three pins, the twin's conjunction. -/
theorem bpoW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {nP cto ctl lo ll ro rl cso csl : Word} {r : List Word} {cvTs : List IConstantVal}
    {rs : List (IConstantVal × Nat × Nat × List IRecRule)} {cs : List (IConstantVal × Nat × Nat)}
    {lps R : List NIdx} (hR : reservedBasisNames.run a = .ok (R, a))
    (h : bpoW n m nP cto ctl lo ll ro rl cso csl = some (r, m')) (hS : StageR dn vis fe m a)
    (hts : PSlR decCVp cvTs cto ctl m) (hrs : PSlR decSR rs ro rl m) (hcs : PSlR decSC cs cso csl m)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      r = [if ((cvTs.all fun c => !R.contains c.name && c.levelParams == lps) &&
          (rs.all fun r => !R.contains r.1.name) &&
          (cs.all fun c => c.2.1 == nP.toNat && c.1.levelParams == lps && !R.contains c.1.name))
        then 1 else 0] := by
  unfold bpoW at h
  rcases h1 : bpfW n m cto ctl lo ll with _ | ⟨ra, m1⟩ <;> rw [h1] at h
  · cases h
  simp only at h
  obtain ⟨hS1, hg1, hra⟩ := bpfW_ok hR n m m1 cto ctl cvTs ra h1 hS hts hl hlb
  by_cases ha : ra.headD 0 = 0
  · rw [ite_eq_left ha] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [(partsW01 hra).mp ha]
    exact ⟨hS1, hg1, rfl⟩
  rw [ite_eq_right ha] at h
  have hat : (cvTs.all fun c => !R.contains c.name && c.levelParams == lps) = true := by
    simpa using mt (partsW01 hra).mpr ha
  rcases h2 : bprW n m1 ro rl with _ | ⟨rb, m2⟩ <;> rw [h2] at h
  · cases h
  simp only at h
  obtain ⟨hm2, hrb⟩ := bprW_ok hR n m1 m2 ro rl rs rb h2 hS1 (hrs.grow decSR_mono hg1)
  rw [hm2] at h
  by_cases hb : rb.headD 0 = 0
  · rw [ite_eq_left hb] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [hat, (partsW01 hrb).mp hb]
    exact ⟨hS1, hg1, rfl⟩
  rw [ite_eq_right hb] at h
  have hbt : (rs.all fun r => !R.contains r.1.name) = true := by simpa using mt (partsW01 hrb).mpr hb
  rcases h3 : bpcW n m1 nP cso csl lo ll with _ | ⟨rc, m3⟩ <;> rw [h3] at h
  · cases h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS3, hg3, hrc⟩ := bpcW_ok hR n m1 m3 cso csl cs rc h3 hS1 (hcs.grow decSC_mono hg1)
    (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.1)
  refine ⟨hS3, hg1.trans hg3, ?_⟩
  rw [hat, hbt, hrc]; simp only [Bool.true_and]; rfl

/-! ## `block_shape_large` -/

/-- The twin's eliminator choice. -/
def largeOf (lps : List NIdx) (cv : IConstantVal) : Option NIdx :=
  match cv.levelParams with
  | [] => none
  | elim :: relps => if relps == lps && !lps.contains elim then some elim else none

/-- `block_shape_large`'s `(ok, elim)` against the twin's `Option`. -/
def LargeR : Option NIdx → List Word → Prop
  | none, r => r.headD 0 = 0
  | some e, r => r.headD 0 = 1 ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = e

/-- **The model of `block_shape_large`.** -/
def bslW (n : Nat) (m : Mem) (cvR0 lo ll : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 EREC) (cvR0 + 2) = 0 then some ([0, 0], m)
  else match erToIwW n m (rdW (m.arr64 EREC) (cvR0 + 1) + 1) (rdW (m.arr64 EREC) (cvR0 + 2) - 1) with
    | none => none
    | some (rp, m1) =>
      match eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll with
      | none => none
      | some e =>
        if e = 0 then some ([0, 0], m1)
        else match containsW n m1 lo ll (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (cvR0 + 1))) with
          | none => none
          | some hs => if hs ≠ 0 then some ([0, 0], m1)
            else some ([1, rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (cvR0 + 1))], m1)

theorem bsl_spec (p : Prog) (hP : IndPartsProg4 p) (hec : p.lookup "er_copy" = some erCopy)
    (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
    (hp : p.lookup "block_shape_large" = some blockShapeLarge) (n : Nat) (s₀ : St) (cvR0 lo ll : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_shape_large" [cvR0, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ bslW n s₀.mem cvR0 lo ll = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeLarge]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, erToIw_specW p hP.alloc hec het n,
      slEq_spec p hseq n, slContains_spec p hP.contains n] <;>
    finish (gen := 20) [bslW, rdW_eq]

/-- **`block_shape_large`**: the twin's eliminator choice. -/
theorem bslW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {cvR0 lo ll : Word} {r : List Word} {cv : IConstantVal} {lps : List NIdx}
    (h : bslW n m cvR0 lo ll = some (r, m')) (hS : StageR dn vis fe m a)
    (hcv : DecB (fun m => decCVp m cvR0.toNat) m cv)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ LargeR (largeOf lps cv) r := by
  have hcv' : decCV (erA (truncM m)) cvR0.toNat = some cv := hcv
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv'
  obtain ⟨nm, -, lv, hlv, ce, -, hcvT⟩ := hcv'
  have hlvE : cv.levelParams = lv := by rw [← hcvT]
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho, l', hlw, hsl⟩ := hlv
  have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
  have hq2lt := partsErLt hlw
  obtain ⟨w1, hw1b, -⟩ := partsErRd (IWGrow.refl m) ho (w := cvR0 + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨w2, hw2b, -⟩ := partsErRd (IWGrow.refl m) hlw (w := cvR0 + 2) (by rw [UInt64.toNat_add]; simp; omega)
  unfold bslW at h
  rw [w1, w2] at h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases h0 : l' = 0
  · subst h0
    rw [ite_eq_left (show (UInt64.ofNat 0 : Word) = 0 from rfl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : lv = [] := by simpa [hslice?] using hsl.symm
    refine ⟨hS, IWGrow.refl _, ?_⟩
    simp only [largeOf, hlvE, this, LargeR]; rfl
  rw [ite_eq_right (by intro e; apply h0; have := congrArg UInt64.toNat e; rwa [UInt64.toNat_ofNat_of_lt' hw2b] at this)] at h
  obtain ⟨L, rfl⟩ : ∃ L, l' = L + 1 := ⟨l' - 1, by omega⟩
  rw [hslice?_succ] at hsl
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hsl
  obtain ⟨e, he, relps, hrel, rfl⟩ := hsl
  obtain ⟨w, hw, hwl, hwe⟩ := hd?_some he
  obtain ⟨hwlt, hw'⟩ := truncM_er_get hw
  simp only [erA] at hw'
  have hrdw : rdW (m.arr64 EREC) (UInt64.ofNat o') = w := rdW_of_get? (UInt64.toNat_ofNat_of_lt' hw1b).symm hw'
  rw [hrdw] at h
  have ho1 : (UInt64.ofNat o' + 1).toNat = o' + 1 := by rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hw1b]; simp; omega
  have hl1 : (UInt64.ofNat (L + 1) - 1).toNat = L := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hw2b]; simp)]
    rw [UInt64.toNat_ofNat_of_lt' hw2b]; simp
  rcases h1 : erToIwW n m (UInt64.ofNat o' + 1) (UInt64.ofNat (L + 1) - 1) with _ | ⟨rp, m1⟩ <;> rw [h1] at h
  · cases h
  simp only at h
  obtain ⟨hS1, hg1, hd1, ht1⟩ := partsSliceCopy h1 hS (by rw [ho1, hl1]; exact hrel)
  rcases he1 : eqW n m1 (rp.headD 0) (rp.tail.headD 0) lo ll with _ | ev <;> rw [he1] at h
  · cases h
  simp only at h
  have hT1 : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
  obtain ⟨ws1, hs1, hn1, hl1'⟩ := slR_of_decHL m1 _ _ _ hd1 (by omega)
  rw [ofNat_toNat_word, ofNat_toNat_word] at hs1
  have hl' : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow3 hg1 hlb]; exact hl
  obtain ⟨ws2, hs2, hn2, hl2⟩ := slR_of_decHL m1 _ _ _ hl' (by have := hg1.1; omega)
  rw [ofNat_toNat_word, ofNat_toNat_word] at hs2
  have hres := eqW_ok n m1 _ _ _ _ ev ws1 ws2 hs1 hs2 he1
  have hbeq : (relps == lps) = decide (ws1 = ws2) := by rw [hn1, hn2, map_decI_beq ws1 ws2 hl1' hl2]
  by_cases hev : ev = 0
  · rw [ite_eq_left hev] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : (relps == lps) = false := by
      rw [hbeq]; by_cases hw12 : ws1 = ws2
      · rw [hres, ite_eq_left hw12] at hev; exact absurd hev (by decide)
      · simp [hw12]
    refine ⟨hS1, hg1, ?_⟩
    simp only [largeOf, hlvE, this, Bool.false_and, LargeR]; rfl
  rw [ite_eq_right hev] at h
  have hrt : (relps == lps) = true := by
    rw [hbeq]; by_cases hw12 : ws1 = ws2
    · simp [hw12]
    · rw [hres, ite_eq_right hw12] at hev; exact absurd rfl hev
  rcases hc : containsW n m1 lo ll w with _ | hsv <;> rw [hc] at h
  · cases h
  simp only at h
  have hcv2 := containsW_ok n m1 lo ll w hsv ws2 hs2 hc
  have hcont : lps.contains e = ws2.contains w := by rw [hn2, hwe]; exact partsContains_decI ws2 w hl2 hwl
  by_cases hh : hsv ≠ 0
  · rw [ite_eq_left hh] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : lps.contains e = true := by rw [hcont]; exact (ipIte01_ne hcv2).mp hh
    refine ⟨hS1, hg1, ?_⟩
    simp only [largeOf, hlvE, hrt, this, Bool.not_true, Bool.and_false, LargeR]; rfl
  rw [ite_eq_right hh] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have : lps.contains e = false := by rw [hcont]; exact Bool.eq_false_iff.mpr (mt (ipIte01_ne hcv2).mpr hh)
  refine ⟨hS1, hg1, ?_⟩
  simp only [largeOf, hlvE, hrt, this, Bool.not_false, Bool.and_true, LargeR, ite_true]
  exact ⟨rfl, hwl, hwe.symm⟩

end L.Ind
