import ConAgua.Arena.FreezeTruncBase

/-!
# The truncation theorem, part 2: the relations over arrays that are not frozen (lane parmode)

`truncFrozen` keeps `CTL` and every array outside `fzSrcs` (`FreezeTruncBase.lean`). The frame
lemmas of the memos and caches (`memoRV_frame`, …) take a `MemFrame`, which also asks every
array to keep its size, which the frozen arrays do not; `memoRV_congr` is the memo relation's
congruence over exactly what it reads (its array and `CTL`), and the groups follow from it.
-/

namespace L.Arena

open ConRon.Arena

/-- `m'` agrees with `m` on `CTL` and on every array that is not frozen. -/
structure KeepNF (m m' : Mem) : Prop where
  ctl : m'.arr64 CTL = m.arr64 CTL
  arr : ∀ b, b ∉ fzSrcs → m'.arr64 b = m.arr64 b

theorem keepNF_trunc (m : Mem) : KeepNF m (truncFrozen m) :=
  ⟨truncFrozen_ctl m, truncFrozen_other m⟩

section memo
variable {κ ν : Type} [BEq κ] [Hashable κ]

/-- **The memo relation reads its array and `CTL` only.** -/
theorem memoRV_congr (S : MemoSch) (K : MemoKey κ) (VR : Mem → Word → ν → Prop) {m m' : Mem}
    (hb : m'.arr64 S.arr = m.arr64 S.arr) (hc : m'.arr64 CTL = m.arr64 CTL)
    (hV : ∀ w v, VR m w v → VR m' w v) {mp : Std.HashMap κ ν} (hR : MemoRV S K VR m mp) :
    MemoRV S K VR m' mp := by
  obtain ⟨g1, g2, g3, g4, -⟩ := reg_congr S m m' (fun f _ => by rw [hb]) (by rw [hc]) (by rw [hb])
  have hs : ∀ j, mstG S m' j = mstG S m j := fun j => by simp only [mstG, hb]
  have hk : ∀ j, mk1G S m' j = mk1G S m j := fun j => by simp only [mk1G, hb]
  have hk' : ∀ j, mk2G S m' j = mk2G S m j := fun j => by simp only [mk2G, hb]
  have hv : ∀ j, mvG S m' j = mvG S m j := fun j => by simp only [mvG, hb]
  obtain ⟨hctl, hep, ⟨r1, r2, r3, r4⟩, hlive, huniq, hrun⟩ := hR
  refine ⟨by rw [hc]; exact hctl, by rw [g1]; exact hep,
    ⟨by rw [g2, g3, g4]; exact r1, fun j hj => by rw [hs, g1]; exact r2 j (g4 ▸ hj),
      fun j h1 h2 => by rw [hs, g1]; exact r3 j (by rw [← g2, ← g3]; exact h1) (g4 ▸ h2),
      by rw [hb, g1]; exact r4⟩, ?_, ?_, ?_⟩
  · intro j hj hl ht; rw [g2, g3] at hj; rw [hs, g1] at hl; rw [hk] at ht; rw [hk, hk', hv]
    obtain ⟨h1, u, h2, h3⟩ := hlive j hj hl ht
    exact ⟨h1, u, h2, hV _ _ h3⟩
  · intro j j' hj hj' hl hl' ht hkk hkk'; rw [g2, g3] at hj hj'; rw [hs, g1] at hl hl'
    rw [hk] at ht; rw [hk, hk] at hkk; rw [hk', hk'] at hkk'
    exact huniq j j' hj hj' hl hl' ht hkk hkk'
  · intro x v hx
    obtain ⟨hdx, htx, d, h1, h2, h2', h3⟩ := hrun x v hx
    refine ⟨hdx, htx, d, ?_, ?_, ?_, fun e he => ?_⟩
    · rw [g2, g3, hs, g1]; exact h1
    · rw [g2, g3, hk]; exact h2
    · rw [g2, g3, hk']; exact h2'
    · rw [g2, g3, hs, g1]; exact h3 e he

/-- A memo whose value relation reads no memory, over an array that is not frozen. -/
theorem KeepNF.memoRV {S : MemoSch} {K : MemoKey κ} {VR : Mem → Word → ν → Prop} {m m' : Mem}
    (hk : KeepNF m m') (hS : S.arr ∉ fzSrcs) (hV : ∀ w v, VR m w v → VR m' w v)
    {mp : Std.HashMap κ ν} (hR : MemoRV S K VR m mp) : MemoRV S K VR m' mp :=
  memoRV_congr S K VR (hk.arr _ hS) hk.ctl hV hR

theorem KeepNF.memoRG {S : MemoSch} {K : MemoKey κ} {dv : Word → ν} {m m' : Mem}
    (hk : KeepNF m m') (hS : S.arr ∉ fzSrcs) {mp : Std.HashMap κ ν} (hR : MemoRG S K dv m mp) :
    MemoRG S K dv m' mp :=
  hk.memoRV hS (fun _ _ h => h) hR

end memo

/-! ## The groups -/

section groups
variable {m m' : Mem} (hk : KeepNF m m')
include hk

theorem KeepNF.memosR {ms : Memos} (h : MemosR m ms) : MemosR m' ms :=
  ⟨hk.memoRG (by decide) h.bvar, hk.memoRG (by decide) h.lift, hk.memoRG (by decide) h.inst1,
    hk.memoRG (by decide) h.fvar⟩

theorem KeepNF.modeR {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
    {VR : Mem → Word → ν → Prop} {M : Std.HashMap (κ × Word) ν} {eb : Word}
    {t te : Std.HashMap κ ν} (hS : S.arr ∉ fzSrcs) (hV : VConst VR) (h : ModeR S K VR m M eb t te) :
    ModeR S K VR m' M eb t te :=
  ⟨hk.memoRV hS (hV m m') h.memo, h.cur, h.stored, h.empty⟩

theorem KeepNF.coreR {c : Caches} (h : CoreR m c) : CoreR m' c := by
  obtain ⟨M, h⟩ := h
  exact ⟨M, hk.modeR (by decide) vh_const h.wc, hk.modeR (by decide) vh_const h.wk,
    hk.modeR (by decide) vh_const h.wh, hk.modeR (by decide) vh_const h.inf,
    hk.modeR (by decide) vh_const h.io, hk.modeR (by decide) vb_const h.de, h.eb1,
    hk.memoRV (by decide) (vh_const m m') h.ct, hk.memoRV (by decide) (vh_const m m') h.cv,
    hk.memoRV (by decide) (vh_const m m') h.rr, hk.memoRG (by decide) h.lq,
    hk.memoRG (by decide) h.lsq⟩

theorem KeepNF.lpMemos (h : LPMemos m) : LPMemos m' :=
  ⟨let ⟨mp, hm⟩ := h.1; ⟨mp, hk.memoRV (by decide) (fun _ _ h => h) hm⟩,
    let ⟨mp, hm⟩ := h.2.1; ⟨mp, hk.memoRV (by decide) (fun _ _ h => h) hm⟩,
    let ⟨mp, hm⟩ := h.2.2; ⟨mp, hk.memoRV (by decide) (fun _ _ h => h) hm⟩⟩

theorem KeepNF.coreMemos (h : CoreMemos m) : CoreMemos m' := by
  obtain ⟨⟨mp1, h1⟩, ⟨mp2, h2⟩, ⟨mp3, h3⟩, ⟨mp4, h4⟩, ⟨mp5, h5⟩, h6⟩ := h
  exact ⟨⟨mp1, hk.memoRG (by decide) h1⟩, ⟨mp2, hk.memoRG (by decide) h2⟩,
    ⟨mp3, hk.memoRG (by decide) h3⟩, ⟨mp4, hk.memoRG (by decide) h4⟩,
    ⟨mp5, hk.memoRG (by decide) h5⟩, hk.lpMemos h6⟩

theorem KeepNF.crOK (h : L.Stubs.CrOK m) : L.Stubs.CrOK m' := by
  obtain ⟨memo, h⟩ := h
  exact ⟨memo, hk.memoRV (by decide) (fun _ _ h => h) h⟩

theorem KeepNF.pmemoR {pm : PMemo} (h : PMemoR m pm) : PMemoR m' pm :=
  ⟨hk.memoRV (by decide) (fun _ _ h => h) h.n, hk.memoRV (by decide) (fun _ _ h => h) h.l,
    hk.memoRV (by decide) (fun _ _ h => h) h.ls, hk.memoRV (by decide) (fun _ _ h => h) h.e⟩

theorem KeepNF.declsF {ds : Array IDeclaration}
    (h : L.Front.DeclsF (m.arr64 L.Front.DECL) (m.arr64 L.Front.DLP) ds) :
    L.Front.DeclsF (m'.arr64 L.Front.DECL) (m'.arr64 L.Front.DLP) ds := by
  rw [hk.arr _ (by decide), hk.arr _ (by decide)]; exact h

end groups

end L.Arena
