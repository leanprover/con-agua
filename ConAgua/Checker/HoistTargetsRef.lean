import ConAgua.Checker.HoistNatRef

/-!
# `hoist_targets_go` is the twin's `hoistTargetsGo` (lane `front4`)

The outer loop over the stream: every pinned `Nat` operation record (`isNatOpRecord`) pulls the
closures of its grounds (`natOpDeps`) ahead of it (`deps_ok`).
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

theorem dw_rdW (D : Array Word) (r : Word) (k : Nat) (hr : r.toNat < 2 ^ 59) (hk : k < 8) :
    rdW D (1 + 8 * r + UInt64.ofNat k) = dw D r.toNat k := by
  have : (1 + 8 * r + UInt64.ofNat k).toNat = 1 + 8 * r.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
    simp only [UInt64.toNat_one]
    have h8 : (8 : Word).toNat = 8 := rfl
    rw [h8]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 8 * r.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 1 + 8 * r.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 1 + 8 * r.toNat + k < 2 ^ 64)]
  simp only [rdW, dw, this]

theorem tgtR_frameA {m m' : Mem} {tg : Word} {c : Nat} {T : Std.HashMap Nat Nat}
    (hT : TgtR m tg c T) (htop : tg.toNat + c ≤ iwTop m) (hsz : iwTop m < 2 ^ 64) (hf : AFr m m') :
    TgtR m' tg c T := by
  refine ⟨fun k hk => ?_, hT.2⟩
  rw [← hT.1 k hk]
  have hn : (tg + UInt64.ofNat k).toNat = tg.toNat + k := addW_toNat _ _ (by omega)
  simp only [rdW, hn]
  rw [hf.2.1.2.2.1 _ (by omega)]

/-- **What the targets pass keeps**: everything but `IW`, `HSEEN`, `CTL[73‥74, 200]`; the `IW`
words below the targets; the pool only grows. -/
def LowFr (tg : Word) (m m' : Mem) : Prop :=
  MemFrame [IW, HSEEN] [73, 74, 200] m m' ∧
    (∀ x : Nat, x < tg.toNat → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?) ∧ iwTop m ≤ iwTop m'

theorem LowFr.refl (tg : Word) (m : Mem) : LowFr tg m m :=
  ⟨MemFrame.refl _ _ _, fun _ _ => rfl, Nat.le_refl _⟩

theorem LowFr.trans {tg : Word} {m₁ m₂ m₃ : Mem} (h₁ : LowFr tg m₁ m₂) (h₂ : LowFr tg m₂ m₃) :
    LowFr tg m₁ m₃ :=
  ⟨h₁.1.trans h₂.1, fun x hx => (h₂.2.1 x hx).trans (h₁.2.1 x hx), Nat.le_trans h₁.2.2 h₂.2.2⟩

theorem LowFr.ofHFr {tg ws : Word} {c : Nat} {m m' : Mem} (h : HFr tg ws c m m') : LowFr tg m m' :=
  ⟨h.1.mono (by simp) (by simp), fun x hx => h.2 x (Or.inl hx),
    by simp only [iwTop]; rw [h.1.2.1 200 (by decide)]; exact Nat.le_refl _⟩

theorem LowFr.ofAFr {tg : Word} {m m' : Mem} (h : AFr m m') (ht : tg.toNat ≤ iwTop m) : LowFr tg m m' :=
  ⟨h.1.mono (by simp) (by simp), fun x hx => h.2.1.2.2.1 x (by omega), h.2.1.1⟩

/-- The kind of a record decides whether it is a definition. -/
theorem defn_of_kind {D P : Array Word} {r : Nat} {d : IDeclaration} (hD : DeclAtF D P r d) :
    (dw D r 0 = 2 → ∃ cv v h, d = .defnDecl cv v h ∧ decI (dw D r 1) = cv.name) ∧
    (dw D r 0 ≠ 2 → isNatOpRecord d = pure none) := by
  cases d with
  | axiomDecl cv => exact ⟨fun h => (by simp [DeclAtF, DeclAt] at hD; rw [hD.1] at h; cases h),
      fun _ => rfl⟩
  | defnDecl cv v h =>
    simp only [DeclAtF, DeclAt] at hD
    exact ⟨fun _ => ⟨cv, v, h, rfl, hD.2.1.1⟩, fun h' => absurd hD.1 h'⟩
  | thmDecl cv v => exact ⟨fun h => (by simp [DeclAtF, DeclAt] at hD; rw [hD.1] at h; cases h),
      fun _ => rfl⟩
  | opaqueDecl cv v => exact ⟨fun h => (by simp [DeclAtF, DeclAt] at hD; rw [hD.1] at h; cases h),
      fun _ => rfl⟩
  | basisDecl _ => simp [DeclAtF, DeclAt] at hD
  | indDecl b nP => exact ⟨fun h => (by simp [DeclAtF, IndDeclAt] at hD; rw [hD.1] at h; cases h),
      fun _ => rfl⟩
  | quotDecl k cv => exact ⟨fun h => (by simp [DeclAtF, DeclAt] at hD; rw [hD.1] at h; cases h),
      fun _ => rfl⟩

/-- **`hoist_targets_go` is `hoistTargetsGo`** from position `i` on, the targets before all
`< i`. -/
theorem targets_ok {p : Prog} (hx : HoistExt p) {a : AState} {ds : Array IDeclaration}
    {idx : Std.HashMap NIdx Nat} {ord tg ws : Word} {c : Nat} (cw : Word) (hcw : cw.toNat = c) :
    ∀ (n : Nat) (m m' : Mem) (T : Std.HashMap Nat Nat) (iw r : Word),
    HEnv m a ds idx ord tg ws c → TgtR m tg c T → TgtV T c →
    (∀ (k t : Nat), T[k]? = some t → t < iw.toNat) → TLt T → iw.toNat ≤ c → PinsR m a.pins →
    hTargetsGoW p n m ord cw tg ws iw = some (r, m') →
    ∃ T'', (hoistTargetsGo ds idx T iw.toNat).run a = .ok (T'', a) ∧
      HEnv m' a ds idx ord tg ws c ∧ TgtR m' tg c T'' ∧ TgtV T'' c ∧ TLt T'' ∧ PinsR m' a.pins ∧
      LowFr tg m m' := by
  intro n
  induction n with
  | zero => intro m m' T iw r _ _ _ _ _ _ _ h; rw [hTargetsGoW.eq_1] at h; cases h
  | succ n ih =>
  intro m m' T iw r hE hT hTv hTi hlt hic hP h
  have hc := hE.c60
  have r1 := hE.rg1; have r2 := hE.rg2; have r3 := hE.rg3; have r4 := hE.isz; have r5 := hE.top
  rw [hoistTargetsGo.eq_def]
  by_cases hend : cw ≤ iw
  · rw [hTargetsGoW.arm1 _ _ _ _ _ _ _ _ hend] at h
    cases h
    have : ¬ iw.toNat < ds.size := by rw [hE.size]; rw [UInt64.le_iff_toNat_le] at hend; omega
    rw [dite_eq_right this]
    exact ⟨T, rfl, hE, hT, hTv, hlt, hP, LowFr.refl _ _⟩
  have hi : iw.toNat < c := by rw [UInt64.le_iff_toNat_le] at hend; omega
  have hids : iw.toNat < ds.size := hE.size ▸ hi
  rw [dite_eq_left hids]
  have hiw1 : (iw + 1).toNat = iw.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]; omega
  have hiw' : iw = UInt64.ofNat iw.toNat := by simp
  obtain ⟨hr59, hD, hok⟩ := hE.ordR iw.toNat hids
  rw [← hiw'] at hr59 hD hok
  generalize hrw : rdW (m.arr64 IW) (ord + iw) = rw at h hr59 hD hok
  have hkind : rdW (m.arr64 DECL) (1 + 8 * rw) = dw (m.arr64 DECL) rw.toNat 0 := by
    have := dw_rdW (m.arr64 DECL) rw 0 hr59 (by omega); simpa using this
  have hname : rdW (m.arr64 DECL) (1 + 8 * rw + 1) = dw (m.arr64 DECL) rw.toNat 1 := by
    have := dw_rdW (m.arr64 DECL) rw 1 hr59 (by omega); simpa using this
  -- the next position
  have hnext : ∀ (m₁ : Mem) (T₁ : Std.HashMap Nat Nat), HEnv m₁ a ds idx ord tg ws c →
      TgtR m₁ tg c T₁ → TgtV T₁ c → (∀ (k t : Nat), T₁[k]? = some t → t < iw.toNat + 1) → TLt T₁ →
      PinsR m₁ a.pins → hTargetsGoW p n m₁ ord cw tg ws (iw + 1) = some (r, m') →
      ∃ T'', (hoistTargetsGo ds idx T₁ (iw.toNat + 1)).run a = .ok (T'', a) ∧
        HEnv m' a ds idx ord tg ws c ∧ TgtR m' tg c T'' ∧ TgtV T'' c ∧ TLt T'' ∧ PinsR m' a.pins ∧
        LowFr tg m₁ m' := by
    intro m₁ T₁ hE₁ hT₁ hTv₁ hTi₁ hlt₁ hP₁ h₁
    have := ih m₁ m' T₁ (iw + 1) r hE₁ hT₁ hTv₁ (by rw [hiw1]; exact hTi₁) hlt₁ (by omega) hP₁ h₁
    rwa [hiw1] at this
  have hTi1 : ∀ (k t : Nat), T[k]? = some t → t < iw.toNat + 1 :=
    fun k t h => Nat.lt_succ_of_lt (hTi k t h)
  obtain ⟨hdef, hnot⟩ := defn_of_kind hD
  by_cases hk2 : rdW (m.arr64 DECL) (1 + 8 * rw) = 2
  · rw [hTargetsGoW.arm2 _ _ _ _ _ _ _ _ hend (by rw [hrw]; exact hk2), hrw] at h
    obtain ⟨cv, v, hh, hds, hcv⟩ := hdef (by rw [← hkind]; exact hk2)
    have hw : (dw (m.arr64 DECL) rw.toNat 1).toNat < 2 ^ 32 := (hok.1 (by rw [← hkind, hk2]; decide)).1
    rw [hname] at h
    cases hrec : hNatOpRecW p n m (dw (m.arr64 DECL) rw.toNat 1) with
    | none => rw [hrec, hTargetsGoW.k_nat_op_record.eq_1] at h; cases h
    | some rr =>
    obtain ⟨op, m₁⟩ := rr
    rw [hrec] at h
    obtain ⟨hPF, L₁, L₂, hL₁, hL₂, hop, hf₁⟩ :=
      natOpRec_ok p hx n m m₁ a _ op hE.iwok hP.full hw hrec
    have hE₁ := hE.frameA hf₁
    have hT₁ := tgtR_frameA hT (by omega) (by have := hE.iwok.1; omega) hf₁
    have hP₁ : PinsR m₁ a.pins := hP.congr (hf₁.1.1 PINS (by decide) (by decide))
    have hPF₁ : PinsFull m₁ a.pins := hPF.congr (hf₁.1.1 PINS (by decide) (by decide))
    -- the twin's test
    have hrun : (isNatOpRecord ds[iw.toNat]).run a =
        .ok ((if (L₁.contains cv.name || L₂.contains cv.name) = true then some cv.name else none), a) := by
      rw [hds]
      simp only [isNatOpRecord]
      rw [HoistTwin.run_bind, hL₁]
      simp only
      rw [HoistTwin.run_bind, hL₂]
      simp only
      split <;> rfl
    rw [HoistTwin.run_bind, hrun]
    rw [← hcv]
    by_cases hop0 : op ≠ 0
    · rw [ite_eq_left (hop.mp hop0)]
      simp only
      rw [hTargetsGoW.k_nat_op_record.arm1 _ _ _ _ _ _ _ _ _ _ hop0] at h
      rcases hdc : callW p n "nat_op_deps" [dw (m.arr64 DECL) rw.toNat 1] m₁ with _ | ⟨rs, m₂⟩ <;> rw [hdc] at h
      · simp [hTargetsGoW.k_nat_op_deps.eq_1] at h
      rw [hTargetsGoW.k_nat_op_deps.arm1] at h
      obtain ⟨gs, hgs, hG, hl, habove, hf₂⟩ :=
        natOpDepsCall_ok p hx n m₁ m₂ a _ rs hE₁.iwok hPF₁ hw hdc
      have hE₂ := hE₁.frameA hf₂
      have hT₂ := tgtR_frameA hT₁ (by have := hE₁.top; omega) (by have := hE₁.iwok.1; have := hE₁.isz; omega) hf₂
      rw [HoistTwin.run_bind, hgs]
      simp only
      rcases hdp : hDepsW n m₂ iw (rs.headD 0) (rs.tail.headD 0) 0 ord tg ws with _ | ⟨z, m₃⟩ <;> rw [hdp] at h
      · simp [hTargetsGoW.k_hoist_deps.eq_1] at h
      rw [hTargetsGoW.k_hoist_deps.arm1, hTargetsGoW.j1.arm1] at h
      rw [hiw'] at hdp
      have hsz2 : iwTop m₂ ≤ (m₂.arr64 IW).size := hf₂.2.2.1
      obtain ⟨T₃, hrun₃, hE₃, hT₃, hTv₃, hTi₃, hfr₃, hlt₃⟩ :=
        deps_ok hi (rs.headD 0) (rs.tail.headD 0) gs n m₂ m₃ T 0 z hE₂ hT₂ hTv
          (fun k t h => Nat.le_of_lt (hTi k t h)) hlt hG (by rw [hl]; simp)
          (fun hne => by have := (habove hne).1; have := hE.top; have := hf₁.2.1.1; omega)
          (by
            by_cases hne : gs = []
            · subst hne; simp only [List.length_nil] at hl; rw [hl]; have := (rs.headD 0).toNat_lt; omega
            · have := (habove hne).2; rw [← hl] at this; have := hE₂.isz; have := hf₂.2.2.1; omega)
          hdp
      rw [HoistTwin.run_bind, hrun₃]
      simp only
      have hP₃ : PinsR m₃ a.pins :=
        (hP₁.congr (hf₂.1.1 PINS (by decide) (by decide))).congr (hfr₃.1.1 PINS (by decide) (by decide))
      obtain ⟨T'', h1, h2, h3, h4, h5, h6, h7⟩ :=
        hnext m₃ T₃ hE₃ hT₃ hTv₃ (fun k t h => Nat.lt_succ_of_le (hTi₃ k t h)) hlt₃ hP₃ h
      exact ⟨T'', h1, h2, h3, h4, h5, h6, ((LowFr.ofAFr hf₁ (by omega)).trans
        ((LowFr.ofAFr hf₂ (by have := hE₁.top; omega)).trans (LowFr.ofHFr hfr₃))).trans h7⟩
    · rw [ite_eq_right (fun hh => hop0 (hop.mpr hh))]
      simp only
      rw [hTargetsGoW.k_nat_op_record.arm2 _ _ _ _ _ _ _ _ _ _ (Decidable.of_not_not hop0), hTargetsGoW.j1.arm1] at h
      obtain ⟨T'', h1, h2, h3, h4, h5, h6, h7⟩ := hnext m₁ T hE₁ hT₁ hTv hTi1 hlt hP₁ h
      exact ⟨T'', h1, h2, h3, h4, h5, h6, (LowFr.ofAFr hf₁ (by omega)).trans h7⟩
  · rw [hTargetsGoW.arm3 _ _ _ _ _ _ _ _ hend (by rw [hrw]; exact hk2), hTargetsGoW.j1.arm1] at h
    rw [hnot (by rw [← hkind]; exact hk2)]
    simp only [HoistTwin.run_bind]
    exact hnext m T hE hT hTv hTi1 hlt hP h

end L.Checker
