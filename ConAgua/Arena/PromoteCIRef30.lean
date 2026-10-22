import ConAgua.Arena.PromoteCIRef29

/-!
# `promote_new` refines `promoteNew`: the main part
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem cdec_length {dn : NIdx → Option ConLeche.Name} {A E : Array Word} :
    ∀ (j : Nat) (cs : List IConstantInfo), cdec dn A E j = some cs → cs.length = j
  | 0, cs, h => by simp [cdec] at h; subst h; rfl
  | j + 1, cs, h => by
    simp only [cdec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨p, hp, x, hx, xs, hxs, rfl⟩ := h
    simp [cdec_length j xs hxs]

theorem arenaD_rows {m m' : Mem} {a : AState} {pm : PMemo} (hD : ArenaD m a) (hP : PMemoR m pm)
    (hf : MemFrame [EIXA, EIXS, EIXN] [] m m') : ArenaD m' a ∧ PMemoR m' pm :=
  ⟨⟨ArenaR.frame_ext _ _ (by simp [EIXA, EIXS, EIXN]) (by simp) m _ hf a hD.1,
    DerR.frameM _ _ m _ hf (by simp [EIXA, EIXS, EIXN]) a hD.2⟩,
    hP.frame (by simp [EIXA, EIXS, EIXN]) (by simp) hf⟩

/-- The tail of `newW` after the memo is cleared. -/
def newRest (p : Prog) (n : Nat) (k vis : Word) (m₁ : Mem) : Option Mem :=
  if (m₁.arr64 CTL).size ≤ 128 then none
  else
  (callW p n "erase_installed" [rdW (m₁.arr64 CTL) 128 - 1,
      if rdW (m₁.arr64 CTL) 128 < k then rdW (m₁.arr64 CTL) 128 else k] m₁).bind fun r₁ =>
  (callW p n "promote_ci_list" [L.Ind.CWF, rdW (m₁.arr64 CTL) 128 - 1,
      if rdW (m₁.arr64 CTL) 128 < k then rdW (m₁.arr64 CTL) 128 else k] r₁.2).bind fun r₂ =>
  memK (callW p n "index_promoted" [vis, rdW (m₁.arr64 CTL) 128 - 1,
      if rdW (m₁.arr64 CTL) 128 < k then rdW (m₁.arr64 CTL) 128 else k] r₂.2)

theorem newW_eq (p : Prog) (n : Nat) (m : Mem) (k vis fresh : Word) :
    newW p n m k vis fresh = if k = 0 then some m else
      (if fresh ≠ 0 then (callW p n "promote_clear" [] m).bind fun r => some r.2 else some m).bind
        (newRest p n k vis) := rfl

theorem pnew_arrs : ∀ b ∈ EIXA :: EIXS :: EIXN :: ECON :: EREC :: eArrs,
    b < 50 ∨ (132 ≤ b ∧ b ≤ 136) ∨ (146 ≤ b ∧ b ≤ 149) := by
  intro b hb
  simp only [List.mem_cons] at hb
  rcases hb with rfl | rfl | rfl | rfl | hb
  · right; left; simp [EIXA]
  · right; left; simp [EIXS]
  · right; left; simp [EIXN]
  · right; left; simp [ECON]
  · rcases vg_arrs b (List.mem_cons.mpr hb) with h | h | h
    · exact .inl h
    · right; left; subst h; exact ⟨by decide, by decide⟩
    · exact .inr (.inr h)

theorem pnew_arrs' : ∀ b ∈ ECON :: EREC :: eArrs,
    b < 50 ∨ b = 135 ∨ b = 136 ∨ (146 ≤ b ∧ b ≤ 149) := by
  intro b hb
  simp only [List.mem_cons] at hb
  rcases hb with rfl | rfl | hb
  · right; left; simp [ECON]
  · right; right; left; simp [EREC]
  · rcases vg_arrs b (List.mem_cons.mpr (Or.inr hb)) with h | h | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))

theorem pnew_ctl : ∀ x ∈ (129 :: eCtl : List Word),
    x.toNat < 64 ∨ x.toNat = 129 ∨ (140 ≤ x.toNat ∧ x.toNat ≤ 147) := by
  intro x hx
  have := vg_ctl x (by simp only [List.mem_cons] at hx ⊢; rcases hx with h | h; exact Or.inl h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  exact this

theorem take_drop_min {α : Type} (L B : List α) (N K : Nat) (hN : (L ++ B).length = N)
    (hL : L.length = min N K) : (L ++ B).take K = L ∧ (L ++ B).drop K = B := by
  by_cases h : K ≤ N
  · have hK : L.length = K := by omega
    exact ⟨List.take_left' hK, List.drop_left' hK⟩
  · have hB : B = [] := by
      simp only [List.length_append] at hN
      exact List.length_eq_zero_iff.mp (by omega)
    subst hB
    simp only [List.append_nil] at *
    exact ⟨List.take_of_length_le (by omega), List.drop_of_length_le (by omega)⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem pnew_main (dn : NIdx → Option ConLeche.Name) (n : Nat) (m₁ : Mem) (a : AState)
    (pm : PMemo) (k vis : Word) (consts : List IConstantInfo)
    (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (vb : Nat) (pend : Array PendingCheck)
    (ds : Array IDeclaration) (m' : Mem) (hP₁ : PMemoR m₁ pm)
    (hR₁ : LoopR dn m₁ a vis ⟨⟨consts⟩, idx, vb⟩ pend ds) (hk : k.toNat ≤ vis.toNat)
    (hW : newRest p n k vis m₁ = some m') :
    ∃ a' pm' Lc', (promoteCIList pm coreWalkFuel (consts.take k.toNat)).run a =
        .ok ((pm', Lc'), a') ∧
      LoopR dn m' a' vis ⟨⟨Lc' ++ consts.drop k.toNat⟩,
        indexPromoted (eraseInstalled idx (consts.take k.toNat)) vb Lc', vb⟩ pend ds := by
  have hE₁ := hR₁.check.env
  have hvis : vb = vis.toNat := hR₁.check.env.vis
  subst hvis
  obtain ⟨hiw1, hiw2, hiw3, hiw4, hiw5⟩ := hR₁.iw
  have hsz₁ : (m₁.arr64 EREC).size < 2 ^ 64 := hiw4
  have hts₁ : erecTop m₁ ≤ (m₁.arr64 EREC).size := hiw2
  have hD₁ : ArenaD m₁ a := hR₁.check.arena
  simp only [newRest] at hW
  by_cases hs128 : (m₁.arr64 CTL).size ≤ 128
  · rw [if_pos hs128] at hW; cases hW
  rw [if_neg hs128] at hW
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 = rdW (m₁.arr64 CTL) 128 := ⟨_, rfl⟩
  rw [← hn0] at hW
  obtain ⟨c, hc⟩ : ∃ c, c = if n0 < k then n0 else k := ⟨_, rfl⟩
  rw [← hc] at hW
  have hcn : c.toNat = min n0.toNat k.toNat := by
    rw [hc]
    by_cases h : n0 < k
    · rw [if_pos h]; have := UInt64.lt_iff_toNat_lt.mp h; omega
    · rw [if_neg h]; have := UInt64.not_lt.mp h; have := UInt64.le_iff_toNat_le.mp this; omega
  -- the constants
  have hcons := hE₁.consts
  rw [envConsts_eq] at hcons
  have hlenv : envLen m₁ = n0.toNat := by simp only [envLen, hn0]
  rw [hlenv] at hcons
  have hlen : consts.length = n0.toNat := cdec_length _ _ hcons
  have hcle : c.toNat ≤ n0.toNat := by omega
  obtain ⟨Lc, B, hLB, hLl, hCA, hB⟩ := cdec_split c.toNat (n0.toNat - c.toNat) consts
    (by rw [show n0.toNat - c.toNat + c.toNat = n0.toNat by omega]; exact hcons)
  obtain ⟨htake, hdrop⟩ := take_drop_min Lc B n0.toNat k.toNat (by rw [← hLB]; exact hlen)
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
  have hCA' : ConstsAt dn (erecP m₁) (m₁.arr64 ECON) (n0 - 1).toNat Lc := by
    rcases hjt with h | h
    · subst h; trivial
    · rw [h]; have : n0.toNat - c.toNat + c.toNat - 1 = n0.toNat - 1 := by omega
      rw [this] at hCA; exact hCA
  have hclk : c.toNat = Lc.length := hLl.symm
  have hcL : Lc.length = c.toNat := hLl
  have hkc : c.toNat ≤ k.toNat := by omega
  -- erase
  cases hca : callW p n "erase_installed" [n0 - 1, c] m₁ with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₂⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hE₂, hfr₂⟩ := erase_rel p hp dn n m₁ vis (n0 - 1) c _ Lc r₁ m₂ hE₁ hsz₁ hLl.symm hj1 hCA' hca
  obtain ⟨hD₂, hP₂⟩ := arenaD_rows hD₁ hP₁ hfr₂
  have hEE₂ : m₂.arr64 EREC = m₁.arr64 EREC := hfr₂.1 EREC (by decide) (by decide)
  have hEC₂ : m₂.arr64 ECON = m₁.arr64 ECON := hfr₂.1 ECON (by decide) (by decide)
  have hT₂ : erecTop m₂ = erecTop m₁ := by simp only [erecTop]; rw [hfr₂.2.1 129 (by simp)]
  have hsz₂ : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hEE₂]; exact hsz₁
  have hts₂ : erecTop m₂ ≤ (m₂.arr64 EREC).size := by rw [hEE₂, hT₂]; exact hts₁
  have hP₂e : erecP m₂ = erecP m₁ := by
    rw [erecP_eq_preE, erecP_eq_preE, hT₂]; exact preE_congr hEE₂ _
  have hg₁₂ : ErecGrow m₁ m₂ := ErecGrow.of_eq hEE₂ hT₂
  have h128₂ : rdW (m₂.arr64 CTL) 128 = rdW (m₁.arr64 CTL) 128 := hfr₂.2.1 128 (by simp)
  -- promote
  cases hcb : callW p n "promote_ci_list" [L.Ind.CWF, n0 - 1, c] m₂ with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₃⟩ := x
  rw [hcb] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨a₃, pm₃, Lc', hrun₃, hD₃, hP₃, hcp₃, hfr₃, hg₂₃, hts₃, hlen₃, hcons₃, hout₃, hszE₃⟩ :=
    ciList_rel p hp dn n m₂ a pm L.Ind.CWF (n0 - 1) c (erecTop m₂) Lc r₂ m₃ hD₂ hP₂ hsz₂ hts₂ hLl.symm
      hj1 (by rw [← erecP_eq_preE, hP₂e, hEC₂]; exact hCA') (Nat.le_refl _) hcb
  have hg₁₃ : ErecGrow m₁ m₃ := hg₁₂.trans hg₂₃
  have hE128₃ : rdW (m₃.arr64 CTL) 128 = rdW (m₁.arr64 CTL) 128 := by
    rw [hfr₃.2.1 128 (by decide), h128₂]
  have hEC₃rows : ∀ b : Nat, 132 ≤ b → b < 135 → m₃.arr64 b = m₂.arr64 b := by
    intro b h1 h2
    apply hfr₃.1 b _ (by simp only [CTL]; omega)
    intro hb
    rcases pnew_arrs' b hb with h | h | h
    · omega
    · omega
    · omega
  -- the constants after the promotion
  have hBdec : cdec dn (erecP m₃) (m₃.arr64 ECON) (n0.toNat - c.toNat) = some B := by
    refine cdec_mono hg₁₃.ext (n0.toNat - c.toNat) B (fun i hi => ?_) hB
    rw [hout₃ i (by rcases hjt with h | h
                    · subst h; simp only [List.length_nil]; omega
                    · rw [h]; omega), hEC₂]
  have hcons₃' : ConstsAt dn (erecP m₃) (m₃.arr64 ECON) (n0.toNat - c.toNat + Lc'.length - 1) Lc' := by
    rcases hjt with h | h
    · subst h; simp at hlen₃; have : Lc' = [] := List.length_eq_zero_iff.mpr hlen₃; subst this; trivial
    · rw [hlen₃, hLlen]
      have : n0.toNat - c.toNat + c.toNat - 1 = n0.toNat - 1 := by omega
      rw [this, ← h]; exact hcons₃
  have hcdec₃ := cdec_join Lc' (n0.toNat - c.toNat) B hcons₃' hBdec
  have hEnv₃c : envConsts dn m₃ = some (Lc' ++ B) := by
    rw [envConsts_eq]
    have : envLen m₃ = n0.toNat := by simp only [envLen, hE128₃, hn0]
    rw [this]
    have e : n0.toNat - c.toNat + Lc'.length = n0.toNat := by rw [hlen₃, hLlen]; omega
    rw [← e]; exact hcdec₃
  have hE₃ : EnvR dn m₃ vis ⟨⟨Lc' ++ B⟩, eraseInstalled idx Lc, vis.toNat⟩ :=
    (show EnvR dn m₂ vis ⟨⟨consts⟩, eraseInstalled idx Lc, vis.toNat⟩ from hE₂).promoted hEC₃rows hg₂₃ (Lc' ++ B)
      hEnv₃c
  have hsz₃ : (m₃.arr64 EREC).size < 2 ^ 64 := by rw [hg₂₃.2.2]; exact hsz₂
  -- index
  cases hcd : callW p n "index_promoted" [vis, n0 - 1, c] m₃ with
  | none => rw [hcd] at hW; cases hW
  | some x =>
  obtain ⟨r₃, m₄⟩ := x
  rw [hcd, memK_some] at hW
  have hm4 : m₄ = m' := Option.some.inj hW
  subst hm4
  have hL'c : Lc'.length = c.toNat := by rw [hlen₃, hLlen]
  obtain ⟨hE₄, hfr₄⟩ := index_rel p hp dn n m₃ vis vis (n0 - 1) c _ Lc' r₃ m₄ hE₃ hsz₃ hL'c.symm
    (by rw [hL'c]; rcases hjt with h | h
        · subst h; simp at hLl; omega
        · rw [h]; omega)
    (by rw [hL'c]; omega) hcons₃ hcd
  obtain ⟨hD₄, hP₄⟩ := arenaD_rows hD₃ hP₃ hfr₄
  have hEE₄ : m₄.arr64 EREC = m₃.arr64 EREC := hfr₄.1 EREC (by decide) (by decide)
  have hT₄ : erecTop m₄ = erecTop m₃ := by simp only [erecTop]; rw [hfr₄.2.1 129 (by simp)]
  have hg₁₄ : ErecGrow m₁ m₄ := hg₁₃.trans (ErecGrow.of_eq hEE₄ hT₄)
  have hts₄ : erecTop m₄ ≤ (m₄.arr64 EREC).size := by rw [hEE₄, hT₄]; exact hts₃
  have hrowsub : ∀ b ∈ [EIXA, EIXS, EIXN], b ∈ EIXA :: EIXS :: EIXN :: ECON :: EREC :: eArrs := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp
  have hfA : MemFrame (EIXA :: EIXS :: EIXN :: ECON :: EREC :: eArrs) (129 :: eCtl) m₁ m₄ :=
    ((hfr₂.mono hrowsub (by simp)).trans
      (hfr₃.mono (fun b hb => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hb))) (fun x hx => hx))).trans (hfr₄.mono hrowsub (by simp))
  have hrun₃' : (promoteCIList pm coreWalkFuel (consts.take k.toNat)).run a =
      .ok ((pm₃, Lc'), a₃) := by
    rw [htake, ← L.Ind.CWF_eq]; exact hrun₃
  refine ⟨a₃, pm₃, Lc', hrun₃', ?_⟩
  rw [htake, hdrop]
  exact LoopR.of_frame hR₁ hD₄ hfA pnew_arrs pnew_ctl hcp₃ hg₁₄ hts₄ hP₄ hE₄

end rel

end L.Arena
