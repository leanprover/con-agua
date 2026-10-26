import ConAgua.Arena.PromoteTblRef

/-!
# `promote_new_tables` refines `promoteNewTables` under the loop's relation
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem ptnew_arrs : ∀ b ∈ tblArrs ++ ETAB :: EREC :: eArrs,
    ((b < 50 ∨ (54 < b ∧ b < 64)) ∨ ((132 ≤ b ∧ b ≤ 136) ∨ (140 ≤ b ∧ b ≤ 142)) ∨
      (146 ≤ b ∧ b ≤ 149) ∨ (256 ≤ b ∧ b < 306) ∨ (310 < b ∧ b < 320)) ∨
      ((129 ≤ b ∧ b ≤ 131) ∨ b = 143 ∨ (385 ≤ b ∧ b ≤ 387)) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · simp only [tblArrs, List.mem_cons, List.not_mem_nil, or_false] at hb
    right
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [TIXA, TIXS, TIXN]
  rcases List.mem_cons.mp hb with rfl | hb
  · right; right; left; rfl
  · rcases vg_arrs b hb with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl (.inl (by subst h; exact ⟨by decide, by decide⟩))))
    · exact .inl (.inr (.inr h))

/-- The arrays `promote_proj_tables` writes avoid the constant rows, `ECON` and the table rows. -/
theorem pts_arrs : ∀ b ∈ ETAB :: EREC :: eArrs,
    (b < 50 ∨ (54 < b ∧ b < 64)) ∨ b = 136 ∨ b = 143 ∨ (146 ≤ b ∧ b ≤ 149) ∨
      (256 ≤ b ∧ b < 306) ∨ (310 < b ∧ b < 320) := by
  intro b hb
  simp only [List.mem_cons] at hb
  rcases hb with rfl | rfl | hb
  · right; right; left; rfl
  · right; left; simp [EREC]
  · rcases vg_arrs b (List.mem_cons.mpr (Or.inr hb)) with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem ptnew_main {pins : List INatOpPinSet} (dn : NIdx → Option ConLeche.Name) (n : Nat) (m₁ : Mem)
    (a : AState) (pm : PMemo) (kt vis : Word) (consts : List IConstantInfo) (tables : List IProjTable)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (vb : Nat) (tbls : Std.HashMap NIdx IProjTable)
    (pend : Array PendingCheck) (ds : Array IDeclaration) (m' : Mem) (hP₁ : PMemoR m₁ pm)
    (hR₁ : LoopR pins dn m₁ a vis ⟨⟨consts, tables⟩, idx, vb, tbls⟩ pend ds)
    (hk0 : kt ≠ 0) (hW : newTW p n m₁ kt = some m') :
    ∃ a' pm' Lt', (promoteProjTables pm coreWalkFuel (tables.take kt.toNat)).run a =
        .ok ((pm', Lt'), a') ∧
      LoopR pins dn m' a' vis ⟨⟨consts, Lt' ++ tables.drop kt.toNat⟩, idx, vb,
        indexPromotedTables (eraseInstalledTables tbls (tables.take kt.toNat)) Lt'⟩ pend ds ∧
      PMemoR m' pm' := by
  have hE₁ := hR₁.check.env
  obtain ⟨hiw1, hiw2, hiw3, hiw4, hiw5⟩ := hR₁.iw
  have hsz₁ : (m₁.arr64 EREC).size < 2 ^ 64 := hiw4
  have hts₁ : erecTop m₁ ≤ (m₁.arr64 EREC).size := hiw2
  have hD₁ : ArenaD m₁ a := hR₁.check.arena
  simp only [newTW, if_neg hk0] at hW
  -- the count
  obtain ⟨⟨rc, m₁'⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm, hrc⟩ := tblCnt_call p hp hcc
  subst m₁'
  generalize hn0 : g0 rc = n0 at hW hrc
  obtain ⟨c, hc⟩ : ∃ c, c = if n0 < kt then n0 else kt := ⟨_, rfl⟩
  rw [← hc] at hW
  have hcn : c.toNat = min n0.toNat kt.toNat := by
    rw [hc]
    by_cases h : n0 < kt
    · rw [if_pos h]; have := UInt64.lt_iff_toNat_lt.mp h; omega
    · rw [if_neg h]; have := UInt64.not_lt.mp h; have := UInt64.le_iff_toNat_le.mp this; omega
  -- the tables
  have htabs := hE₁.tables
  rw [envTables_eq] at htabs
  have hlenv : tblCnt m₁ = n0.toNat := by simp only [tblCnt, hrc]
  rw [hlenv] at htabs
  have hlen : tables.length = n0.toNat := tdec_length _ _ htabs
  have hcle : c.toNat ≤ n0.toNat := by omega
  obtain ⟨Lc, B, hLB, hLl, hCA, hB⟩ := tdec_split c.toNat (n0.toNat - c.toNat) tables
    (by rw [show n0.toNat - c.toNat + c.toNat = n0.toNat by omega]; exact htabs)
  obtain ⟨htake, hdrop⟩ := take_drop_min Lc B n0.toNat kt.toNat (by rw [← hLB]; exact hlen)
    (by rw [hLl, hcn]) |> fun h => by rw [← hLB] at h; exact h
  have hjn : Lc = [] ∨ n0 ≠ 0 := by
    by_cases h : n0 = 0
    · left
      have : n0.toNat = 0 := by rw [h]; rfl
      exact List.length_eq_zero_iff.mp (by omega)
    · exact .inr h
  have hjt : Lc = [] ∨ (n0 - 1).toNat = n0.toNat - 1 := by
    rcases hjn with h | h
    · exact .inl h
    · exact .inr (toNat_sub1 n0 h)
  have hLlen : Lc.length = c.toNat := hLl
  have hj1 : Lc.length ≤ (n0 - 1).toNat + 1 := by
    rcases hjt with h | h
    · subst h; simp
    · rw [h]; omega
  have hCA' : TablesAt (erecP m₁) (m₁.arr64 ETAB) (n0 - 1).toNat Lc := by
    rcases hjt with h | h
    · subst h; trivial
    · rw [h]; have : n0.toNat - c.toNat + c.toNat - 1 = n0.toNat - 1 := by omega
      rw [this] at hCA; exact hCA
  -- erase
  obtain ⟨⟨r₁, m₂⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hE₂, hfr₂⟩ := eraseT_rel p hp dn n m₁ vis (n0 - 1) c _ Lc r₁ m₂ hE₁ hsz₁ hLl.symm hj1 hCA' hca
  obtain ⟨hD₂, hP₂⟩ := arenaD_tbl hD₁ hP₁ hfr₂
  have hEE₂ : m₂.arr64 EREC = m₁.arr64 EREC := hfr₂.1 EREC (by decide) (by decide)
  have hET₂ : m₂.arr64 ETAB = m₁.arr64 ETAB := hfr₂.1 ETAB (by decide) (by decide)
  have hT₂ : erecTop m₂ = erecTop m₁ := by simp only [erecTop]; rw [hfr₂.2.1 129 (by simp)]
  have hsz₂ : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hEE₂]; exact hsz₁
  have hts₂ : erecTop m₂ ≤ (m₂.arr64 EREC).size := by rw [hEE₂, hT₂]; exact hts₁
  have hP₂e : erecP m₂ = erecP m₁ := by
    rw [erecP_eq_preE, erecP_eq_preE, hT₂]; exact preE_congr hEE₂ _
  have hg₁₂ : ErecGrow m₁ m₂ := ErecGrow.of_eq hEE₂ hT₂
  have h133₂ : rdW (m₂.arr64 CTL) 133 = rdW (m₁.arr64 CTL) 133 := hfr₂.2.1 133 (by simp)
  -- promote
  obtain ⟨⟨r₂, m₃⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a₃, pm₃, Lt', hrun₃, hD₃, hP₃, hcp₃, hfr₃, htk₃, hg₂₃, hts₃, hlen₃, hcons₃, hout₃, hszE₃⟩ :=
    ptables_rel p hp n m₂ a pm L.Ind.CWF (n0 - 1) c (erecTop m₂) Lc r₂ m₃ hD₂ hP₂ hsz₂ hts₂ hLl.symm
      hj1 (by rw [← erecP_eq_preE, hP₂e, hET₂]; exact hCA') (Nat.le_refl _) hcb
  have hg₁₃ : ErecGrow m₁ m₃ := hg₁₂.trans hg₂₃
  have hX₃ : ∀ b : Nat, b ∉ ETAB :: EREC :: eArrs → b ≠ CTL → m₃.arr64 b = m₂.arr64 b :=
    fun b h1 h2 => hfr₃.1 b h1 h2
  have h133₃ : rdW (m₃.arr64 CTL) 133 = rdW (m₁.arr64 CTL) 133 := by
    rw [hfr₃.2.1 133 (fun h => by have := pnew_ctl _ h; simp at this), h133₂]
  have h128₃ : rdW (m₃.arr64 CTL) 128 = rdW (m₂.arr64 CTL) 128 :=
    hfr₃.2.1 128 (fun h => by have := pnew_ctl _ h; simp at this)
  have hrows₃ : ∀ b : Nat, 132 ≤ b → b < 143 → (b < 135 ∨ 140 ≤ b) → m₃.arr64 b = m₂.arr64 b := by
    intro b h1 h2 h3
    apply hX₃ b _ (fun h => by rw [h] at h1; simp [CTL] at h1)
    intro hb
    rcases pts_arrs b hb with h | h | h | h <;> (simp only [ArrId] at h; omega)
  have htr₃ : ∀ w, rowTag w ≤ 2 → m₃.arr64 (tblArr w) = m₂.arr64 (tblArr w) := fun w hw =>
    hX₃ _ (fun h => by
        have := tblArr_cases w hw
        rcases pts_arrs _ h with h' | h' | h' | h' <;> (simp only [ArrId] at h' this; omega))
      (by rcases tblArr_cases w hw with h | h | h | h | h | h <;> rw [h] <;> decide)
  -- the lists after the promotion
  have hBdec : tdec (erecP m₃) (m₃.arr64 ETAB) (n0.toNat - c.toNat) = some B := by
    refine tdec_mono hg₁₃.ext (n0.toNat - c.toNat) B (fun i hi => ?_) hB
    rw [hout₃ i (by rcases hjt with h | h
                    · subst h; simp only [List.length_nil]; omega
                    · rw [h]; omega), hET₂]
  have hcons₃' : TablesAt (erecP m₃) (m₃.arr64 ETAB) (n0.toNat - c.toNat + Lt'.length - 1) Lt' := by
    rcases hjt with h | h
    · subst h
      have : Lt' = [] := by simpa using hlen₃
      subst this; trivial
    · rw [hlen₃, hLlen]
      have : n0.toNat - c.toNat + c.toNat - 1 = n0.toNat - 1 := by omega
      rw [this, ← h]; exact hcons₃
  have htdec₃ := tdec_join Lt' (n0.toNat - c.toNat) B hcons₃' hBdec
  have hEnv₃t : envTables m₃ = some (Lt' ++ B) := by
    rw [envTables_eq]
    have : tblCnt m₃ = n0.toNat := by simp only [tblCnt, h133₃, hrc]
    rw [this]
    have e : n0.toNat - c.toNat + Lt'.length = n0.toNat := by rw [hlen₃, hLlen]; omega
    rw [← e]; exact htdec₃
  have hEnv₃c : envConsts dn m₃ = some consts := by
    have h0 := hE₂.consts
    rw [envConsts_eq] at h0 ⊢
    have hl : envLen m₃ = envLen m₂ := by simp only [envLen, h128₃]
    rw [hl]
    exact cdec_mono hg₂₃.ext _ _ (fun i _ => by
      rw [hX₃ ECON (fun h => by rcases pts_arrs _ h with h' | h' | h' | h' <;> (simp only [ECON, ArrId] at h'; omega))
        (by decide)]) h0
  have hE₃ : EnvR dn m₃ vis ⟨⟨consts, Lt' ++ B⟩, idx, vb, eraseInstalledTables tbls Lc⟩ :=
    (show EnvR dn m₂ vis ⟨⟨consts, tables⟩, idx, vb, eraseInstalledTables tbls Lc⟩ from hE₂).promoted
      hrows₃ htr₃ hg₂₃ consts (Lt' ++ B) hEnv₃c hEnv₃t
  have hsz₃ : (m₃.arr64 EREC).size < 2 ^ 64 := by rw [hg₂₃.2.2]; exact hsz₂
  -- index
  cases hcd : callW p n "index_promoted_tables" [n0 - 1, c] m₃ with
  | none => rw [hcd] at hW; cases hW
  | some x =>
  obtain ⟨r₃, m₄⟩ := x
  rw [hcd, memK_some] at hW
  have hm4 : m₄ = m' := Option.some.inj hW
  subst hm4
  have hL'c : Lt'.length = c.toNat := by rw [hlen₃, hLlen]
  obtain ⟨hE₄, hfr₄⟩ := indexT_rel p hp dn n m₃ vis (n0 - 1) c _ Lt' r₃ m₄ hE₃ hsz₃ hL'c.symm
    (by rw [hL'c]; rcases hjt with h | h
        · subst h; simp at hLl; omega
        · rw [h]; omega) hcons₃ hcd
  obtain ⟨hD₄, hP₄⟩ := arenaD_tbl hD₃ hP₃ hfr₄
  have hEE₄ : m₄.arr64 EREC = m₃.arr64 EREC := hfr₄.1 EREC (by decide) (by decide)
  have hT₄ : erecTop m₄ = erecTop m₃ := by simp only [erecTop]; rw [hfr₄.2.1 129 (by simp)]
  have hg₁₄ : ErecGrow m₁ m₄ := hg₁₃.trans (ErecGrow.of_eq hEE₄ hT₄)
  have hts₄ : erecTop m₄ ≤ (m₄.arr64 EREC).size := by rw [hEE₄, hT₄]; exact hts₃
  have hfA : MemFrame (tblArrs ++ ETAB :: EREC :: eArrs) (129 :: eCtl) m₁ m₄ :=
    ((hfr₂.mono (fun b hb => List.mem_append_left _ hb) (by simp)).trans
      (hfr₃.mono (fun b hb => List.mem_append_right _ hb) (fun x hx => hx))).trans
      (hfr₄.mono (fun b hb => List.mem_append_left _ hb) (by simp))
  have hrun₃' : (promoteProjTables pm coreWalkFuel (tables.take kt.toNat)).run a =
      .ok ((pm₃, Lt'), a₃) := by
    rw [htake, ← L.Ind.CWF_eq]; exact hrun₃
  refine ⟨a₃, pm₃, Lt', hrun₃', ?_⟩
  rw [htake, hdrop]
  have hfl : m₄.flag = m₁.flag := hfA.2.1 1 (by decide)
  have htk : TierKeep m₁ m₄ :=
    (TierKeep.of_frame hfr₂ (by simp)).trans (htk₃.trans (TierKeep.of_frame hfr₄ (by simp)))
  exact ⟨LoopR.of_frame hR₁ hD₄ hfA ptnew_arrs (fun x hx => .inl (pnew_ctl x hx)) hcp₃ hg₁₄ hts₄ hP₄
    hE₄ (ModeOK.of_keep hR₁.check.mode hfl htk), hP₄⟩

end rel

end L.Arena
