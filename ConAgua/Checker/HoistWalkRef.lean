import ConAgua.Checker.HoistRefBase

/-!
# The hoist's walk refines `usedConsts` (lane `front4`)

`hoist_walk` and its arms, `hoist_rules_go`, `hoist_block_go`, `hoist_deps_of` against
`usedConstsGo`, `usedConstsRules`, `usedConstsBlock`, `IDeclaration.usedConsts`
(`ConRon/Arena/Frontend/NatOpGround.lean`). The twin collects the names a record references into an
array; L hands each to `hoist_note` as the walk finds it. The statements say: when L returns, the
twin returns (in the same state) the names `ns` (as words, `decI`), and L's memory is that of
`notesW` over `ns` except the visited set (`HSEEN`, `CTL[73‥74]`), which represents the twin's.
The walk counter `fu` is the twin's fuel exactly.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

set_option linter.unusedSimpArgs false

namespace L.Checker


theorem _root_.L.Arena.MemFrame.symmH {A : List ArrId} {C : List Word} {m m' : Mem} (h : MemFrame A C m m') :
    MemFrame A C m' m :=
  ⟨fun b hb hc => (h.1 b hb hc).symm, fun x hx => (h.2.1 x hx).symm, fun b => (h.2.2.1 b).symm,
    h.2.2.2.symm⟩

theorem _root_.L.Arena.MemFrame.set64_bothH {A : List ArrId} {C : List Word} {m₁ m₂ : Mem} (h : MemFrame A C m₁ m₂)
    (b : ArrId) (hb : b ≠ CTL) (k v : Word) : MemFrame A C (m₁.set64 b k v) (m₂.set64 b k v) := by
  refine ⟨fun b' hb' hc => ?_, fun x hx => ?_, fun b' => ?_, ?_⟩
  · by_cases e : b' = b
    · subst e; rw [Mem.arr64_set64_same, Mem.arr64_set64_same, h.1 b' hb' hc]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ e, Mem.arr64_set64_ne _ _ _ _ _ e, h.1 b' hb' hc]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hb), Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hb)]
    exact h.2.1 x hx
  · rw [size_set64, size_set64]; exact h.2.2.1 b'
  · rw [Mem.words_size_set64, Mem.words_size_set64]; exact h.2.2.2

theorem mfindG_congr (S : MemoSch) {m₁ m₂ : Mem} (ha : m₂.arr64 S.arr = m₁.arr64 S.arr)
    (hc : rdW (m₂.arr64 CTL) S.cs = rdW (m₁.arr64 CTL) S.cs) (k1 k2 : Word) :
    mfindG S m₂ k1 k2 = mfindG S m₁ k1 k2 := by
  simp only [mfindG, epG, nG, len64_eq, ha, hc]

/-- `hoist_note` writes `IW` only. -/
theorem hNoteW_iw {m x : Mem} {w i k tg ws sp sp' : Word} (h : hNoteW m w i k tg ws sp = some (sp', x)) :
    MemFrame [IW] [] m x := by
  simp only [hNoteW, hIxW] at h
  split at h
  · simp [hNoteW.k1] at h
  split at h
  · simp only [hNoteW.k1] at h
    split at h
    · simp at h; obtain ⟨-, rfl⟩ := h
      exact (MemFrame.set64 _ _ (by decide) _ _).trans (MemFrame.set64 _ _ (by decide) _ _)
    · simp at h; obtain ⟨-, rfl⟩ := h; exact MemFrame.refl _ _ _
  · simp only [hNoteW.k1] at h
    split at h
    · simp at h; obtain ⟨-, rfl⟩ := h
      exact (MemFrame.set64 _ _ (by decide) _ _).trans (MemFrame.set64 _ _ (by decide) _ _)
    · simp at h; obtain ⟨-, rfl⟩ := h; exact MemFrame.refl _ _ _

theorem notesW_iw {m x : Mem} {i k tg ws sp sp' : Word} {ns : List Word}
    (h : notesW m i k tg ws sp ns = some (sp', x)) : MemFrame [IW] [] m x := by
  induction ns generalizing m sp with
  | nil => simp [notesW] at h; obtain ⟨-, rfl⟩ := h; exact MemFrame.refl _ _ _
  | cons w rest ih =>
    simp only [notesW] at h
    split at h
    · cases h
    · rename_i sp₁ m₁ h1
      exact (hNoteW_iw h1).trans (ih h)

theorem hNoteW_frame {m₁ m₂ x₁ : Mem} {w i k tg ws sp sp' : Word}
    (hf : MemFrame [HSEEN] [73, 74] m₁ m₂) (h : hNoteW m₁ w i k tg ws sp = some (sp', x₁)) :
    ∃ x₂, hNoteW m₂ w i k tg ws sp = some (sp', x₂) ∧ MemFrame [HSEEN] [73, 74] x₁ x₂ := by
  have hfd : mfindG hnSch m₂ w 0 = mfindG hnSch m₁ w 0 :=
    mfindG_congr _ (hf.1 _ (by decide) (by decide)) (hf.2.1 _ (by decide)) _ _
  have hnix : m₂.arr64 HNIX = m₁.arr64 HNIX := hf.1 _ (by decide) (by decide)
  have hiw : m₂.arr64 IW = m₁.arr64 IW := hf.1 _ (by decide) (by decide)
  simp only [hNoteW, hIxW, hfd, hnix] at h ⊢
  by_cases h0 : mfindG hnSch m₁ w 0 = []
  · simp [h0, hNoteW.k1] at h
  by_cases h1 : (mfindG hnSch m₁ w 0).headD 0 = 0
  all_goals
    simp only [h0, h1, ite_false, ite_true, hNoteW.k1, hiw] at h ⊢
    split at h
    · rename_i hc
      rw [if_pos hc]
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, MemFrame.set64_bothH (MemFrame.set64_bothH hf _ (by decide) _ _) _ (by decide) _ _⟩
    · rename_i hc
      rw [if_neg hc]
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, hf⟩

theorem notesW_frame {m₁ m₂ x₁ : Mem} {i k tg ws sp sp' : Word} {ns : List Word}
    (hf : MemFrame [HSEEN] [73, 74] m₁ m₂) (h : notesW m₁ i k tg ws sp ns = some (sp', x₁)) :
    ∃ x₂, notesW m₂ i k tg ws sp ns = some (sp', x₂) ∧ MemFrame [HSEEN] [73, 74] x₁ x₂ := by
  induction ns generalizing m₁ m₂ sp with
  | nil => simp [notesW] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, hf⟩
  | cons w rest ih =>
    simp only [notesW] at h ⊢
    split at h
    · cases h
    · rename_i sp₁ y₁ h1
      obtain ⟨y₂, h2, hf2⟩ := hNoteW_frame hf h1
      rw [h2]
      exact ih hf2 h

/-! ## The visited set -/

theorem hsSch_wf : hsSch.WF := ⟨by decide, by decide⟩

theorem memoRG_congr {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey κ} {dv : Word → ν}
    {m : Mem} {mp mp' : Std.HashMap κ ν} (h : ∀ x : κ, mp'[x]? = mp[x]?) (hR : MemoRG S K dv m mp) :
    MemoRG S K dv m mp' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
  refine ⟨h1, h2, h3, fun j hj hs ht => ?_, h5, fun x v hx => h6 x v (by rw [← h x]; exact hx)⟩
  rw [h]; exact h4 j hj hs ht

theorem hashSet_insert_get (seen : Std.HashSet EIdx) (e x : EIdx) :
    (seen.insert e).inner[x]? = (seen.inner.insert e ())[x]? := by
  simp only [Std.HashSet.insert, Std.HashMap.getElem?_insertIfNew, Std.HashMap.getElem?_insert]
  split <;> split <;> simp_all

theorem seenR_hit {m : Mem} {seen : Std.HashSet EIdx} {e : Word} (hs : SeenR m seen)
    (he : e.toNat < 2 ^ 32) (hr : mfindG hsSch m e 0 ≠ []) (hh : (mfindG hsSch m e 0).headD 0 ≠ 0) :
    seen.contains (decE e) = true := by
  have := memoRG_hit hsSch bmKey (fun _ => ()) m _ hs e 0 hr hh ⟨he, rfl⟩
  simp only [Std.HashSet.contains, Std.HashMap.contains_eq_isSome_getElem?]
  exact (Option.isSome_iff_exists).mpr ⟨_, this⟩

theorem seenR_miss {m : Mem} {seen : Std.HashSet EIdx} {e : Word} (hs : SeenR m seen)
    (he : e.toNat < 2 ^ 32) (hr : mfindG hsSch m e 0 ≠ []) (hh : (mfindG hsSch m e 0).headD 0 = 0) :
    seen.contains (decE e) = false := by
  have := memoRG_miss hsSch bmKey (fun _ => ()) m _ hs e 0 ⟨he, rfl⟩ hr hh
  simp only [Std.HashSet.contains, Std.HashMap.contains_eq_isSome_getElem?]
  exact Option.isSome_eq_false_iff.mpr (by simpa [bmKey] using this)

theorem seenR_put {m m₀ : Mem} {seen : Std.HashSet EIdx} {e : Word} (hs : SeenR m seen)
    (he : e.toNat < 2 ^ 32) (hr : mfindG hsSch m e 0 ≠ [])
    (hp : mputG hsSch m e 0 1 ((mfindG hsSch m e 0).headD 0) ((mfindG hsSch m e 0).tail.headD 0) =
      some m₀) :
    SeenR m₀ (seen.insert (decE e)) ∧ MemFrame [HSEEN] [73, 74] m m₀ := by
  have hs' : msetG hsSch m e 0 1 = some m₀ := by rw [msetG_eq _ _ _ _ _ hr]; exact hp
  refine ⟨memoRG_congr (fun x => hashSet_insert_get seen (decE e) x)
    (memoRG_set hsSch hsSch_wf bmKey (fun _ => ()) m _ hs e 0 1 ⟨he, rfl⟩ m₀ hs'), ?_⟩
  exact (mputG_frame hsSch hsSch_wf m m₀ _ _ _ _ _ hp).mono (by simp) (by simp)

/-! ## What a walk returns -/

/-- The common conclusion: the twin's `x` from `a` returns (in `a`) a visited set `SeenR m'` and
`acc` extended by the names `ns`, whose notes from `m` give `m'` except the visited set. -/
def WRes (m m' : Mem) (i k tg ws sp sp' : Word) (acc : Array NIdx)
    (x : AM (Std.HashSet EIdx × Array NIdx)) (a : AState) : Prop :=
  ∃ (seen' : Std.HashSet EIdx) (ns : List Word),
    x.run a = .ok ((seen', acc ++ (ns.map decI).toArray), a) ∧
    (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ SeenR m' seen' ∧
    ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m'

section wres
variable {m m₀ m₁ m₂ : Mem} {i k tg ws sp sp₁ sp₂ : Word} {acc : Array NIdx} {a : AState}

theorem WRes.frame {x : AM (Std.HashSet EIdx × Array NIdx)} (h : WRes m m₁ i k tg ws sp sp₁ acc x a) :
    MemFrame [IW, HSEEN] [73, 74] m m₁ := by
  obtain ⟨_, _, _, _, _, mn, hn, hf⟩ := h
  exact ((notesW_iw hn).mono (by simp) (by simp)).trans (hf.mono (by simp) (by simp))

theorem WRes.arena {x : AM (Std.HashSet EIdx × Array NIdx)} (h : WRes m m₁ i k tg ws sp sp₁ acc x a)
    (hA : ArenaR m a) : ArenaR m₁ a :=
  ArenaR.frame_ext _ _ (by intro b hb; simp at hb; rcases hb with rfl | rfl <;> decide)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide) m m₁ h.frame a hA

theorem WRes.arr {x : AM (Std.HashSet EIdx × Array NIdx)} (h : WRes m m₁ i k tg ws sp sp₁ acc x a)
    (b : ArrId) (hb1 : b ≠ IW) (hb2 : b ≠ HSEEN) (hb3 : b ≠ CTL) : m₁.arr64 b = m.arr64 b :=
  h.frame.1 b (by simp [hb1, hb2]) hb3

theorem wres_pure {seen : Std.HashSet EIdx} (hs : SeenR m seen) :
    WRes m m i k tg ws sp sp acc (pure (seen, acc)) a :=
  ⟨seen, [], by simp only [List.map_nil, Array.append_empty]; rfl, by simp, hs, m, rfl,
    MemFrame.refl _ _ _⟩

theorem wres_pre {x : AM (Std.HashSet EIdx × Array NIdx)} (hf : MemFrame [HSEEN] [73, 74] m m₀)
    (h : WRes m₀ m₁ i k tg ws sp sp₁ acc x a) : WRes m m₁ i k tg ws sp sp₁ acc x a := by
  obtain ⟨seen', ns, hx, hw, hs, mn, hn, hf'⟩ := h
  obtain ⟨x₂, hn2, hf2⟩ := notesW_frame hf.symmH hn
  exact ⟨seen', ns, hx, hw, hs, x₂, hn2, hf2.symmH.trans hf'⟩

theorem wres_bind {X : AM (Std.HashSet EIdx × Array NIdx)}
    {f : Std.HashSet EIdx × Array NIdx → AM (Std.HashSet EIdx × Array NIdx)}
    (h1 : WRes m m₁ i k tg ws sp sp₁ acc X a)
    (h2 : ∀ seen₁ (ns₁ : List Word), SeenR m₁ seen₁ → (∀ w ∈ ns₁, w.toNat < 2 ^ 32) →
      WRes m₁ m₂ i k tg ws sp₁ sp₂ (acc ++ (ns₁.map decI).toArray)
        (f (seen₁, acc ++ (ns₁.map decI).toArray)) a) :
    WRes m m₂ i k tg ws sp sp₂ acc (X >>= f) a := by
  obtain ⟨seen₁, ns₁, hx, hw1, hs1, mn₁, hn1, hf1⟩ := h1
  obtain ⟨seen₂, ns₂, hy, hw2, hs2, mn₂, hn2, hf2⟩ := h2 seen₁ ns₁ hs1 hw1
  obtain ⟨x₂, hn2', hf2'⟩ := notesW_frame hf1.symmH hn2
  refine ⟨seen₂, ns₁ ++ ns₂, ?_, ?_, hs2, x₂, ?_, hf2'.symmH.trans hf2⟩
  · simp only [StateT.run_bind, hx, except_ok_bind, hy, List.map_append, ← List.append_toArray,
      Array.append_assoc]
  · intro w hw; rcases List.mem_append.mp hw with hw | hw
    · exact hw1 w hw
    · exact hw2 w hw
  · rw [notesW_append, hn1]; exact hn2'

end wres

section wres2
variable {m m₀ m₁ m₂ : Mem} {i k tg ws sp sp₁ sp₂ : Word} {acc : Array NIdx} {a : AState}

theorem wres_view {e : EIdx} {v : ENodeView} {f : ENodeView → AM (Std.HashSet EIdx × Array NIdx)}
    (hv : a.store.view e = some v) (h : WRes m m₁ i k tg ws sp sp₁ acc (f v) a) :
    WRes m m₁ i k tg ws sp sp₁ acc (view e >>= f) a := by
  obtain ⟨seen', ns, hx, hrest⟩ := h
  exact ⟨seen', ns, by rw [StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; exact hx, hrest⟩

/-- A note first: the name `w` pushed. -/
theorem wres_cons {x : AM (Std.HashSet EIdx × Array NIdx)} {w : Word} (hw : w.toNat < 2 ^ 32)
    (hn : hNoteW m w i k tg ws sp = some (sp₁, m₁))
    (h : WRes m₁ m₂ i k tg ws sp₁ sp₂ (acc.push (decI w)) x a) :
    WRes m m₂ i k tg ws sp sp₂ acc x a := by
  obtain ⟨seen', ns, hx, hws, hs, mn, hn', hf⟩ := h
  refine ⟨seen', w :: ns, ?_, ?_, hs, mn, ?_, hf⟩
  · rw [hx, List.map_cons, ← List.singleton_append, ← List.append_toArray, ← Array.append_assoc,
      Array.push_eq_append]
  · intro w' hw'; rcases List.mem_cons.mp hw' with rfl | hw'
    · exact hw
    · exact hws w' hw'
  · simp only [notesW, hn]; exact hn'

end wres2

/-! ## The walk -/

/-- What the model of `hoist_walk` at L fuel `n` says. -/
def WalkOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (e i k tg ws sp fu sp' : Word) (seen : Std.HashSet EIdx)
    (acc : Array NIdx),
    ArenaR m a → e.toNat < 2 ^ 32 → SeenR m seen →
    hWalkW n m e i k tg ws sp fu = some (sp', m') →
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat (decE e)) a

section walk
variable {n : Nat} {m m₁ m₂ : Mem} {i k tg ws sp sp₁ sp₂ fu : Word} {acc : Array NIdx} {a : AState}

/-- A walk after `X`. -/
theorem walk_then (ih : WalkOK n) {X : AM (Std.HashSet EIdx × Array NIdx)}
    {f : Std.HashSet EIdx × Array NIdx → AM (Std.HashSet EIdx × Array NIdx)} {c : Word}
    (hA : ArenaR m a) (h1 : WRes m m₁ i k tg ws sp sp₁ acc X a) (hc : c.toNat < 2 ^ 32)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat (decE c))
    (hb : hWalkW n m₁ c i k tg ws sp₁ fu = some (sp₂, m₂)) :
    WRes m m₂ i k tg ws sp sp₂ acc (X >>= f) a :=
  wres_bind h1 fun seen₁ ns₁ hs1 _ => by
    rw [hf]; exact ih _ _ _ _ _ _ _ _ _ _ _ _ _ (h1.arena hA) hc hs1 hb

theorem ctrW_toNat' (c : Word) (hc : c ≠ 0) : c.toNat = (c - 1).toNat + 1 := by
  have : c.toNat ≠ 0 := fun h => hc (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

end walk

section arms
variable {n : Nat} {m m' : Mem} {e i k tg ws sp fu sp' : Word} {seen : Std.HashSet EIdx}
  {acc : Array NIdx} {a : AState}
  {f : Std.HashSet EIdx × Array NIdx → AM (Std.HashSet EIdx × Array NIdx)}

/-- Two children `c1` (read in `m`) and `c2` (read in the memory after the first walk) of a record
array `R` the walks do not write. -/
theorem two_ok (ih : WalkOK n) (R : ArrId) (hR1 : R ≠ IW) (hR2 : R ≠ HSEEN) (hR3 : R ≠ CTL)
    (x1 x2 : Word) (hA : ArenaR m a) (hs : SeenR m seen)
    (h1w : (rdW (m.arr64 R) x1).toNat < 2 ^ 32) (h2w : (rdW (m.arr64 R) x2).toNat < 2 ^ 32)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat (decE (rdW (m.arr64 R) x2)))
    (hb : (match hWalkW n m (rdW (m.arr64 R) x1) i k tg ws sp fu with
      | none => none
      | some (sp, m₁) => hWalkW n m₁ (rdW (m₁.arr64 R) x2) i k tg ws sp fu) = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc
      (usedConstsGo seen acc fu.toNat (decE (rdW (m.arr64 R) x1)) >>= f) a := by
  cases h1 : hWalkW n m (rdW (m.arr64 R) x1) i k tg ws sp fu with
  | none => rw [h1] at hb; cases hb
  | some p =>
    obtain ⟨sp₁, m₁⟩ := p
    rw [h1] at hb
    simp only at hb
    have W1 := ih _ _ _ _ _ _ _ _ _ _ _ _ acc hA h1w hs h1
    rw [W1.arr R hR1 hR2 hR3] at hb
    exact walk_then ih hA W1 h2w hf hb

theorem app_ok (ih : WalkOK n) (hA : ArenaR m a) (hs : SeenR m seen) (he : e.toNat < 2 ^ 32)
    (hv : viewOK m e 4) (hg : e >>> 28 = 4)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat
      (decE (rdW (m.arr64 AREC) (idxW e * 4 + tierW e * 2 + 1))))
    (hb : hAppW (n + 1) m e i k tg ws sp fu = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat
      (decE (rdW (m.arr64 AREC) (idxW e * 4 + tierW e * 2))) >>= f) a := by
  obtain ⟨-, h1w, h2w⟩ := view_app m a hA e he hv hg
  rw [hAppW.arm1, hAppW.k1.eq_def] at hb
  exact two_ok ih AREC (by decide) (by decide) (by decide) _ _ hA hs h1w h2w hf hb

theorem lam_ok (ih : WalkOK n) (hA : ArenaR m a) (hs : SeenR m seen) (he : e.toNat < 2 ^ 32)
    (hv : viewOK m e 28) (hg : e >>> 28 = 5)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat
      (decE (rdW (m.arr64 LAREC) (idxW e * 4 + tierW e * 2 + 1))))
    (hb : hLamW (n + 1) m e i k tg ws sp fu = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat
      (decE (rdW (m.arr64 LAREC) (idxW e * 4 + tierW e * 2))) >>= f) a := by
  obtain ⟨-, h1w, h2w⟩ := view_lam m a hA e he hv hg
  rw [hLamW.arm1, hLamW.k1.eq_def] at hb
  exact two_ok ih LAREC (by decide) (by decide) (by decide) _ _ hA hs h1w h2w hf hb

theorem forall_ok (ih : WalkOK n) (hA : ArenaR m a) (hs : SeenR m seen) (he : e.toNat < 2 ^ 32)
    (hv : viewOK m e 30) (hg : e >>> 28 = 6)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat
      (decE (rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2 + 1))))
    (hb : hForallW (n + 1) m e i k tg ws sp fu = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat
      (decE (rdW (m.arr64 FAREC) (idxW e * 4 + tierW e * 2))) >>= f) a := by
  obtain ⟨-, h1w, h2w⟩ := view_forall m a hA e he hv hg
  rw [hForallW.arm1, hForallW.k1.eq_def] at hb
  exact two_ok ih FAREC (by decide) (by decide) (by decide) _ _ hA hs h1w h2w hf hb

theorem let_ok (ih : WalkOK n) (hA : ArenaR m a) (hs : SeenR m seen) (he : e.toNat < 2 ^ 32)
    (hv : viewOK m e 20) (hg : e >>> 28 = 7)
    (hf : ∀ s ac, f (s, ac) = (usedConstsGo s ac fu.toNat
      (decE (rdW (m.arr64 LEREC) (idxW e * 6 + tierW e * 3 + 1))) >>= fun x =>
        usedConstsGo x.1 x.2 fu.toNat (decE (rdW (m.arr64 LEREC) (idxW e * 6 + tierW e * 3 + 2)))))
    (hb : hLetW (n + 1) m e i k tg ws sp fu = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat
      (decE (rdW (m.arr64 LEREC) (idxW e * 6 + tierW e * 3))) >>= f) a := by
  obtain ⟨-, h1w, h2w, h3w⟩ := view_let m a hA e he hv hg
  rw [hLetW.arm1, hLetW.k2.eq_def] at hb
  cases h1 : hWalkW n m (rdW (m.arr64 LEREC) (idxW e * 6 + tierW e * 3)) i k tg ws sp fu with
  | none => rw [h1] at hb; cases hb
  | some p =>
    obtain ⟨sp₁, m₁⟩ := p
    rw [h1] at hb
    simp only at hb
    have W1 := ih _ _ _ _ _ _ _ _ _ _ _ _ acc hA h1w hs h1
    rw [hLetW.k1.eq_def] at hb
    refine wres_bind W1 fun seen₁ ns₁ hs1 _ => ?_
    rw [hf]
    have heq := W1.arr LEREC (by decide) (by decide) (by decide)
    rw [← heq] at h2w h3w ⊢
    exact two_ok ih LEREC (by decide) (by decide) (by decide) _ _ (W1.arena hA) hs1 h2w h3w
      (fun _ _ => rfl) hb

end arms

theorem frame_ext' {m m' : Mem} {a : AState} (hf : MemFrame [HSEEN] [73, 74] m m') (hA : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame_ext _ _ (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide) m m' hf a hA

theorem iw_arena {m m' : Mem} {a : AState} (hf : MemFrame [IW] [] m m') (hA : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame_ext _ _ (by intro b hb; simp at hb; subst hb; decide) (by simp) m m' hf a hA

theorem walk_step (n : Nat) (ih : ∀ n', n = n' + 1 → WalkOK n') : WalkOK (n + 1) := by
  intro m m' a e i k tg ws sp fu sp' seen acc hA he hs hb
  by_cases hfu : fu = 0
  · rw [hWalkW.eq_def] at hb; simp [hfu] at hb
  by_cases hr : mfindG hsSch m e 0 = []
  · rw [hWalkW.eq_def] at hb; simp [hfu, hr] at hb
  rw [ctrW_toNat' fu hfu, usedConstsGo.eq_2]
  by_cases hh : (mfindG hsSch m e 0).headD 0 ≠ 0
  · rw [hWalkW.arm1 n m e i k tg ws sp fu hfu hr hh] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    rw [seenR_hit hs he hr hh, if_pos rfl]
    exact wres_pure hs
  rw [hWalkW.arm2 n m e i k tg ws sp fu hfu hr hh] at hb
  rw [seenR_miss hs he hr (Decidable.of_not_not hh), if_neg Bool.false_ne_true]
  cases hp : mputG hsSch m e 0 1 ((mfindG hsSch m e 0).headD 0) ((mfindG hsSch m e 0).tail.headD 0) with
  | none => rw [hp] at hb; simp [hWalkW.k1.eq_def] at hb
  | some m₀ =>
  rw [hp] at hb
  obtain ⟨hs₀, hf₀⟩ := seenR_put hs he hr hp
  have hA₀ := frame_ext' hf₀ hA
  refine wres_pre hf₀ ?_
  by_cases hsc : tierW e ≠ 0 ∧ rdW (m₀.arr64 CTL) 1 = 0
  · rw [hWalkW.k1.eq_def] at hb; simp [hsc] at hb
  have vok : ∀ c0, ¬ rdW (m₀.arr64 CTL) (c0 + tierW e) ≤ idxW e → viewOK m₀ e c0 :=
    fun c0 hc => ⟨hsc, UInt64.not_le.mp hc⟩
  have bad : ∀ c0, rdW (m₀.arr64 CTL) (c0 + tierW e) ≤ idxW e →
      hWalkW.k1 n e i k tg ws sp fu (some m₀) = none → False := fun _ _ h => by rw [h] at hb; cases hb
  -- arms at `n`: `n = 0` is no call
  have arm0 : ∀ (X : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (Word × Mem)),
      (∀ m e i k tg ws sp fu, X 0 m e i k tg ws sp fu = none) →
      X n m₀ e i k tg ws sp (fu - 1) = some (sp', m') → ∃ n', n = n' + 1 := by
    intro X hX hx
    cases n with
    | zero => rw [hX] at hx; cases hx
    | succ n' => exact ⟨n', rfl⟩
  by_cases g3 : e >>> 28 = 3
  · by_cases hc : rdW (m₀.arr64 CTL) (18 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, hc])).elim
    rw [hWalkW.k1.arm1 n e i k tg ws sp fu m₀ hsc g3 hc] at hb
    obtain ⟨hv, hw, -⟩ := view_const_f m₀ a hA₀ e he (vok 18 hc) g3
    refine wres_view hv (wres_cons hw hb ?_)
    exact wres_pure (memoRG_frame hsSch hsSch_wf bmKey _ [IW] [] (by decide) (by decide) _ _
      (hNoteW_iw hb) _ hs₀)
  by_cases g4 : e >>> 28 = 4
  · by_cases hc : rdW (m₀.arr64 CTL) (4 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, hc])).elim
    rw [hWalkW.k1.arm2 n e i k tg ws sp fu m₀ hsc g3 g4 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hAppW.eq_def]) hb
    exact wres_view (view_app m₀ a hA₀ e he (vok 4 hc) g4).1
      (app_ok (ih n' rfl) hA₀ hs₀ he (vok 4 hc) g4 (fun _ _ => rfl) hb)
  by_cases g5 : e >>> 28 = 5
  · by_cases hc : rdW (m₀.arr64 CTL) (28 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, g5, hc])).elim
    rw [hWalkW.k1.arm3 n e i k tg ws sp fu m₀ hsc g3 g4 g5 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hLamW.eq_def]) hb
    exact wres_view (view_lam m₀ a hA₀ e he (vok 28 hc) g5).1
      (lam_ok (ih n' rfl) hA₀ hs₀ he (vok 28 hc) g5 (fun _ _ => rfl) hb)
  by_cases g6 : e >>> 28 = 6
  · by_cases hc : rdW (m₀.arr64 CTL) (30 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, g5, g6, hc])).elim
    rw [hWalkW.k1.arm4 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hForallW.eq_def]) hb
    exact wres_view (view_forall m₀ a hA₀ e he (vok 30 hc) g6).1
      (forall_ok (ih n' rfl) hA₀ hs₀ he (vok 30 hc) g6 (fun _ _ => rfl) hb)
  by_cases g7 : e >>> 28 = 7
  · by_cases hc : rdW (m₀.arr64 CTL) (20 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, g5, g6, g7, hc])).elim
    rw [hWalkW.k1.arm5 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hLetW.eq_def]) hb
    exact wres_view (view_let m₀ a hA₀ e he (vok 20 hc) g7).1
      (let_ok (ih n' rfl) hA₀ hs₀ he (vok 20 hc) g7 (fun _ _ => rfl) hb)
  by_cases g9 : e >>> 28 = 9
  · by_cases hc : rdW (m₀.arr64 CTL) (32 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, g5, g6, g7, g9, hc])).elim
    rw [hWalkW.k1.arm6 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hProjW.eq_def]) hb
    obtain ⟨hv, hnw, hxw⟩ := view_proj m₀ a hA₀ e he (vok 32 hc) g9
    refine wres_view hv ?_
    rw [hProjW.arm1, hProjW.k1.eq_def] at hb
    cases h1 : hNoteW m₀ (rdW (m₀.arr64 PJREC) (idxW e * 6 + tierW e * 3)) i k tg ws sp with
    | none => rw [h1] at hb; cases hb
    | some p =>
      obtain ⟨sp₁, m₁⟩ := p
      rw [h1] at hb
      simp only at hb
      have hfr := hNoteW_iw h1
      have heq : m₁.arr64 PJREC = m₀.arr64 PJREC := hfr.1 _ (by decide) (by decide)
      rw [heq] at hb
      exact wres_cons hnw h1 ((ih n' rfl) _ _ _ _ _ _ _ _ _ _ _ _ _
        (iw_arena hfr hA₀) hxw
        (memoRG_frame hsSch hsSch_wf bmKey _ [IW] [] (by decide) (by decide) _ _ hfr _ hs₀) hb)
  by_cases g1 : e >>> 28 = 1
  · by_cases hc : rdW (m₀.arr64 CTL) (26 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, g5, g6, g7, g9, g1, hc])).elim
    rw [hWalkW.k1.arm7 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 g1 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hFvarW.eq_def]) hb
    obtain ⟨hv, hxw⟩ := view_fvar_idx m₀ a hA₀ e he (vok 26 hc) g1
    rw [hFvarW.arm1] at hb
    exact wres_view hv ((ih n' rfl) _ _ _ _ _ _ _ _ _ _ _ _ _ hA₀ hxw hs₀ hb)
  have fin : hWalkW.k1 n e i k tg ws sp fu (some m₀) = some (sp, m₀) → sp = sp' ∧ m₀ = m' := by
    intro h; rw [h] at hb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb); exact ⟨rfl, rfl⟩
  by_cases g0 : e >>> 28 = 0
  · by_cases hc : rdW (m₀.arr64 CTL) (22 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, g5, g6, g7, g9, g1, g0, hc])).elim
    obtain ⟨rfl, rfl⟩ := fin (hWalkW.k1.arm8 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 g1 g0 hc)
    exact wres_view (view_bvar m₀ a hA₀ e he (vok 22 hc) g0) (wres_pure hs₀)
  by_cases g2 : e >>> 28 = 2
  · by_cases hc : rdW (m₀.arr64 CTL) (16 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, g5, g6, g7, g9, g1, g0, g2, hc])).elim
    obtain ⟨rfl, rfl⟩ := fin (hWalkW.k1.arm9 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 g1 g0 g2 hc)
    obtain ⟨_, hv⟩ := view_sort m₀ a hA₀ e he (vok 16 hc) g2
    exact wres_view hv (wres_pure hs₀)
  by_cases g8 : e >>> 28 = 8
  · by_cases hc : rdW (m₀.arr64 CTL) (2 + tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k1.eq_def]; simp [hsc, g3, g4, g5, g6, g7, g9, g1, g0, g2, g8, hc])).elim
    obtain ⟨rfl, rfl⟩ := fin (hWalkW.k1.arm10 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 g1 g0 g2 g8 hc)
    obtain ⟨_, hv⟩ := view_lit m₀ a hA₀ e he (vok 2 hc) g8
    exact wres_view hv (wres_pure hs₀)
  rw [hWalkW.k1.eq_def] at hb; simp [hsc, g3, g4, g5, g6, g7, g9, g1, g0, g2, g8] at hb

theorem walkOK (n : Nat) : WalkOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb; rw [hWalkW.eq_def] at hb; cases hb
    | succ n => exact walk_step n fun n' h => ih n' (by omega)

/-- **`hoist_walk` refines `usedConstsGo`.** -/
theorem hoistWalk_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (e i k tg ws sp fu sp' : Word) (seen : Std.HashSet EIdx)
      (acc : Array NIdx),
    ArenaR m a → e.toNat < 2 ^ 32 → SeenR m seen →
    hWalkW n m e i k tg ws sp fu = some (sp', m') →
    ∃ (seen' : Std.HashSet EIdx) (ns : List Word),
      (usedConstsGo seen acc fu.toNat (decE e)).run a = .ok ((seen', acc ++ (ns.map decI).toArray), a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ SeenR m' seen' ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' :=
  fun m m' a e i k tg ws sp fu sp' seen acc hA he hs hb =>
    walkOK n m m' a e i k tg ws sp fu sp' seen acc hA he hs hb

/-- The rules `rules` are the eleven-word records at `DIND[ro + 11 r ..]`, right-hand sides at
`+ 8`. -/
def RulesAt (m : Mem) (ro r : Word) (rules : List IRecRule) : Prop :=
  ∀ q (h : q < rules.length),
    (rdW (m.arr64 DIND) (ro + 11 * (r + UInt64.ofNat q) + 8)).toNat < 2 ^ 32 ∧
    rules[q].rhs = decE (rdW (m.arr64 DIND) (ro + 11 * (r + UInt64.ofNat q) + 8))

/-- **`hoist_rules_go` refines `usedConstsRules`.** -/
theorem hoistRulesGo_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k i tg ws sp ro rc r sp' : Word) (seen : Std.HashSet EIdx)
      (acc : Array NIdx) (rules : List IRecRule),
    ArenaR m a → SeenR m seen → r.toNat + rules.length = rc.toNat → RulesAt m ro r rules →
    hRulesGoW n m k i tg ws sp ro rc r = some (sp', m') →
    ∃ (seen' : Std.HashSet EIdx) (ns : List Word),
      (usedConstsRules seen acc rules).run a = .ok ((seen', acc ++ (ns.map decI).toArray), a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ SeenR m' seen' ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  sorry

/-- The block members `cs` are the constant records the pointers `DIND[o + q ‥ o + c)` point to
(`decCIs` below some `t` at most the pool's top, as `IndDeclAt`; the offset not `0`, the pool's
top, which `trunc` clears, and no pointer `0`), none of them a projection table (a parsed block has none). -/
def BlockAt (m : Mem) (o c q : Word) (cs : List IConstantInfo) : Prop :=
  (∃ t, t ≤ ((m.arr64 DLP)[0]?.getD 0).toNat ∧
    decCIs (trunc (m.arr64 DLP) t) (fun _ => none) (o.toNat + q.toNat) (c.toNat - q.toNat) = some cs) ∧
  o.toNat + c.toNat < 2 ^ 63 ∧ o.toNat ≠ 0 ∧
  (∀ j, q.toNat ≤ j → j < c.toNat → (m.arr64 DLP)[o.toNat + j]?.getD 0 ≠ 0) ∧
  q ≤ c ∧ ∀ ci ∈ cs, ci.isTowerEntry = false

/-- **`hoist_block_go` refines `usedConstsBlock`.** -/
theorem hoistBlockGo_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k i tg ws sp o c q sp' : Word) (seen : Std.HashSet EIdx)
      (acc : Array NIdx) (cs : List IConstantInfo),
    ArenaR m a → SeenR m seen → BlockAt m o c q cs →
    hBlockGoW n m k i tg ws sp o c q = some (sp', m') →
    ∃ (seen' : Std.HashSet EIdx) (ns : List Word),
      (usedConstsBlock seen acc cs).run a = .ok ((seen', acc ++ (ns.map decI).toArray), a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ SeenR m' seen' ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  sorry

/-- A record the hoist can walk: an inductive block has no projection table. -/
def WalkableDecl : IDeclaration → Prop
  | .indDecl b _ => ∀ ci ∈ b, ci.isTowerEntry = false
  | _ => True

/-- **`hoist_deps_of` refines `IDeclaration.usedConsts`** (record `r` of `DECL`, `x = 1 + 8 r`). -/
theorem hoistDepsOf_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k i r tg ws sp sp' : Word) (d : IDeclaration),
    ArenaR m a → (∃ seen, SeenR m seen) → r.toNat < 2 ^ 59 →
    DeclAtF (m.arr64 DECL) (m.arr64 DLP) r.toNat d → RecOK (m.arr64 DECL) (m.arr64 DLP) r.toNat → WalkableDecl d →
    hDepsOfW n m k i (1 + 8 * r) tg ws sp = some (sp', m') →
    ∃ ns : List Word,
      (IDeclaration.usedConsts d).run a = .ok ((ns.map decI).toArray, a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ (∃ seen', SeenR m' seen') ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  sorry

end L.Checker
