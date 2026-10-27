import ConAgua.Checker.HoistDecode
import ConAgua.Arena.IndView
import ConAgua.Checker.HoistRefBase
import ConRon.Arena.Frontend.NatOpGround

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
    mfindG S m₂ k1 k2 = mfindG S m₁ k1 k2 :=
  mfindG_eq_of S ha hc k1 k2

/-- `hoist_note` writes `IW` only. -/
theorem hNoteW_iw {m x : Mem} {w i k tg ws sp sp' : Word} (h : hNoteW m w i k tg ws sp = some (sp', x)) :
    MemFrame [IW] [] m x := by
  simp only [hNoteW, hIxW] at h
  split at h
  · simp [hNoteW.k_hoist_ix] at h
  split at h
  · simp only [hNoteW.k_hoist_ix] at h
    split at h
    · simp at h; obtain ⟨-, rfl⟩ := h
      exact (MemFrame.set64 _ _ (by decide) _ _).trans (MemFrame.set64 _ _ (by decide) _ _)
    · simp at h; obtain ⟨-, rfl⟩ := h; exact MemFrame.refl _ _ _
  · simp only [hNoteW.k_hoist_ix] at h
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
  · simp [h0, hNoteW.k_hoist_ix] at h
  by_cases h1 : (mfindG hnSch m₁ w 0).headD 0 = 0
  all_goals
    simp only [h0, h1, ite_false, ite_true, hNoteW.k_hoist_ix, hiw] at h ⊢
    split at h
    · rename_i hc
      rw [ite_eq_left hc]
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, MemFrame.set64_bothH (MemFrame.set64_bothH hf _ (by decide) _ _) _ (by decide) _ _⟩
    · rename_i hc
      rw [ite_eq_right hc]
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
  have e : (fun x => mp'[x]?) = (fun x => mp[x]?) := funext h
  unfold MemoRG MemoRV at hR ⊢
  rw [e]; exact hR

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
  ArenaR.frame_ext _ _ (by decide) (by simp) m m₁ h.frame a hA

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
array `R` the walks do not write (each child a function `g1`, `g2` of the array: a field). -/
theorem two_ok (ih : WalkOK n) (R : ArrId) (hR1 : R ≠ IW) (hR2 : R ≠ HSEEN) (hR3 : R ≠ CTL)
    (g1 g2 : Array Word → Word) (hA : ArenaR m a) (hs : SeenR m seen)
    (h1w : (g1 (m.arr64 R)).toNat < 2 ^ 32) (h2w : (g2 (m.arr64 R)).toNat < 2 ^ 32)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat (decE (g2 (m.arr64 R))))
    (hb : (match hWalkW n m (g1 (m.arr64 R)) i k tg ws sp fu with
      | none => none
      | some (sp, m₁) => hWalkW n m₁ (g2 (m₁.arr64 R)) i k tg ws sp fu) = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc
      (usedConstsGo seen acc fu.toNat (decE (g1 (m.arr64 R))) >>= f) a := by
  rcases h1 : hWalkW n m (g1 (m.arr64 R)) i k tg ws sp fu with _ | ⟨sp₁, m₁⟩ <;> rw [h1] at hb
  · cases hb
  simp only at hb
  have W1 := ih _ _ _ _ _ _ _ _ _ _ _ _ acc hA h1w hs h1
  rw [W1.arr R hR1 hR2 hR3] at hb
  exact walk_then ih hA W1 h2w hf hb

theorem tier_ok (a : ArrId) (t : Word)
    (h : ∀ b ∈ [a, tier1 a], b ≠ IW ∧ b ≠ HSEEN ∧ b ≠ CTL) :
    tierA a t ≠ IW ∧ tierA a t ≠ HSEEN ∧ tierA a t ≠ CTL := by
  rcases tierA_cases' a t with e | e <;> rw [e]
  · exact h a (by simp)
  · exact h (tier1 a) (by simp)

theorem app_ok (ih : WalkOK n) (hA : ArenaR m a) (hs : SeenR m seen) (he : e.toNat < 2 ^ 32)
    (hv : viewOK m e APP) (hg : e >>> 28 = 4)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat
      (decE (tfld m APP (tierW e) (idxW e) 1)))
    (hb : hAppW (n + 1) m e i k tg ws sp fu = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat
      (decE (tfld m APP (tierW e) (idxW e) 0)) >>= f) a := by
  obtain ⟨-, h1w, h2w⟩ := view_app m a hA e he hv hg
  rw [hAppW.arm1, hAppW.k_hoist_walk.eq_def] at hb
  obtain ⟨n1, n2, n3⟩ := tier_ok AREC (tierW e) (by decide)
  exact two_ok ih _ n1 n2 n3 (fun r => APP.ex 0 (rdW r (APP.ad (idxW e) 0)))
    (fun r => APP.ex 1 (rdW r (APP.ad (idxW e) 1))) hA hs h1w h2w hf hb

theorem lam_ok (ih : WalkOK n) (hA : ArenaR m a) (hs : SeenR m seen) (he : e.toNat < 2 ^ 32)
    (hv : viewOK m e LAM) (hg : e >>> 28 = 5)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat
      (decE (tfld m LAM (tierW e) (idxW e) 1)))
    (hb : hLamW (n + 1) m e i k tg ws sp fu = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat
      (decE (tfld m LAM (tierW e) (idxW e) 0)) >>= f) a := by
  obtain ⟨-, h1w, h2w⟩ := view_lam m a hA e he hv hg
  rw [hLamW.arm1, hLamW.k_hoist_walk.eq_def] at hb
  obtain ⟨n1, n2, n3⟩ := tier_ok LAREC (tierW e) (by decide)
  exact two_ok ih _ n1 n2 n3 (fun r => LAM.ex 0 (rdW r (LAM.ad (idxW e) 0)))
    (fun r => LAM.ex 1 (rdW r (LAM.ad (idxW e) 1))) hA hs h1w h2w hf hb

theorem forall_ok (ih : WalkOK n) (hA : ArenaR m a) (hs : SeenR m seen) (he : e.toNat < 2 ^ 32)
    (hv : viewOK m e FORALL) (hg : e >>> 28 = 6)
    (hf : ∀ s ac, f (s, ac) = usedConstsGo s ac fu.toNat
      (decE (tfld m FORALL (tierW e) (idxW e) 1)))
    (hb : hForallW (n + 1) m e i k tg ws sp fu = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat
      (decE (tfld m FORALL (tierW e) (idxW e) 0)) >>= f) a := by
  obtain ⟨-, h1w, h2w⟩ := view_forall m a hA e he hv hg
  rw [hForallW.arm1, hForallW.k_hoist_walk.eq_def] at hb
  obtain ⟨n1, n2, n3⟩ := tier_ok FAREC (tierW e) (by decide)
  exact two_ok ih _ n1 n2 n3 (fun r => FORALL.ex 0 (rdW r (FORALL.ad (idxW e) 0)))
    (fun r => FORALL.ex 1 (rdW r (FORALL.ad (idxW e) 1))) hA hs h1w h2w hf hb

theorem let_ok (ih : WalkOK n) (hA : ArenaR m a) (hs : SeenR m seen) (he : e.toNat < 2 ^ 32)
    (hv : viewOK m e LET) (hg : e >>> 28 = 7)
    (hf : ∀ s ac, f (s, ac) = (usedConstsGo s ac fu.toNat
      (decE (tfld m LET (tierW e) (idxW e) 1)) >>= fun x =>
        usedConstsGo x.1 x.2 fu.toNat (decE (tfld m LET (tierW e) (idxW e) 2))))
    (hb : hLetW (n + 1) m e i k tg ws sp fu = some (sp', m')) :
    WRes m m' i k tg ws sp sp' acc (usedConstsGo seen acc fu.toNat
      (decE (tfld m LET (tierW e) (idxW e) 0)) >>= f) a := by
  obtain ⟨-, h1w, h2w, h3w⟩ := view_let m a hA e he hv hg
  rw [hLetW.arm1, hLetW.k_hoist_walk.eq_def] at hb
  rcases h1 : hWalkW n m (tfld m LET (tierW e) (idxW e) 0) i k tg ws sp fu with _ | ⟨sp₁, m₁⟩ <;> rw [h1] at hb
  · cases hb
  simp only at hb
  have W1 := ih _ _ _ _ _ _ _ _ _ _ _ _ acc hA h1w hs h1
  rw [hLetW.k_hoist_walk_2.eq_def] at hb
  refine wres_bind W1 fun seen₁ ns₁ hs1 _ => ?_
  rw [hf]
  have heq := W1.arr LEREC (by decide) (by decide) (by decide)
  have heq' := W1.arr (tier1 LEREC) (by decide) (by decide) (by decide)
  simp only [tfld_arr_eq (R := LET) heq.symm heq'.symm] at h2w h3w ⊢
  obtain ⟨n1, n2, n3⟩ := tier_ok LEREC (tierW e) (by decide)
  exact two_ok ih _ n1 n2 n3 (fun r => LET.ex 1 (rdW r (LET.ad (idxW e) 1)))
    (fun r => LET.ex 2 (rdW r (LET.ad (idxW e) 2))) (W1.arena hA) hs1 h2w h3w
    (fun _ _ => rfl) hb

end arms

theorem frame_ext' {m m' : Mem} {a : AState} (hf : MemFrame [HSEEN] [73, 74] m m') (hA : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame_ext _ _ (by decide) (by simp) m m' hf a hA

theorem iw_arena {m m' : Mem} {a : AState} (hf : MemFrame [IW] [] m m') (hA : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame_ext _ _ (by decide) (by simp) m m' hf a hA

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
    rw [seenR_hit hs he hr hh, ite_eq_left rfl]
    exact wres_pure hs
  rw [hWalkW.arm2 n m e i k tg ws sp fu hfu hr (Decidable.of_not_not hh)] at hb
  rw [seenR_miss hs he hr (Decidable.of_not_not hh), ite_eq_right Bool.false_ne_true]
  rcases hp : mputG hsSch m e 0 1 ((mfindG hsSch m e 0).headD 0) ((mfindG hsSch m e 0).tail.headD 0) with _ | m₀ <;> rw [hp] at hb
  · simp [hWalkW.k_hs_put.eq_def] at hb
  obtain ⟨hs₀, hf₀⟩ := seenR_put hs he hr hp
  have hA₀ := frame_ext' hf₀ hA
  refine wres_pre hf₀ ?_
  by_cases hsc : tierW e ≠ 0 ∧ rdW (m₀.arr64 CTL) 1 = 0
  · rw [hWalkW.k_hs_put.eq_def] at hb; simp [hsc] at hb
  have vok : ∀ c0, ¬ tcnt m₀ c0 (tierW e) ≤ idxW e → viewOK m₀ e c0 :=
    fun c0 hc => ⟨hsc, UInt64.not_le.mp hc⟩
  have bad : ∀ c0, tcnt m₀ c0 (tierW e) ≤ idxW e →
      hWalkW.k_hs_put n e i k tg ws sp fu (some m₀) = none → False := fun _ _ h => by rw [h] at hb; cases hb
  -- arms at `n`: `n = 0` is no call
  have arm0 : ∀ (X : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (Word × Mem)),
      (∀ m e i k tg ws sp fu, X 0 m e i k tg ws sp fu = none) →
      X n m₀ e i k tg ws sp (fu - 1) = some (sp', m') → ∃ n', n = n' + 1 := by
    intro X hX hx
    cases n with
    | zero => rw [hX] at hx; cases hx
    | succ n' => exact ⟨n', rfl⟩
  by_cases g3 : e >>> 28 = 3
  · by_cases hc : tcnt m₀ CONST (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g3, hc])).elim
    rw [hWalkW.k_hs_put.arm1 n e i k tg ws sp fu m₀ hsc g3 hc] at hb
    obtain ⟨hv, hw, -⟩ := view_const_f m₀ a hA₀ e he (vok CONST hc) g3
    refine wres_view hv (wres_cons hw hb ?_)
    exact wres_pure (memoRG_frame hsSch hsSch_wf bmKey _ [IW] [] (by decide) (by decide) _ _
      (hNoteW_iw hb) _ hs₀)
  by_cases g4 : e >>> 28 = 4
  · by_cases hc : tcnt m₀ APP (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g4, hc])).elim
    rw [hWalkW.k_hs_put.arm2 n e i k tg ws sp fu m₀ hsc g3 g4 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hAppW.eq_def]) hb
    exact wres_view (view_app m₀ a hA₀ e he (vok APP hc) g4).1
      (app_ok (ih n' rfl) hA₀ hs₀ he (vok APP hc) g4 (fun _ _ => rfl) hb)
  by_cases g5 : e >>> 28 = 5
  · by_cases hc : tcnt m₀ LAM (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g5, hc])).elim
    rw [hWalkW.k_hs_put.arm3 n e i k tg ws sp fu m₀ hsc g3 g4 g5 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hLamW.eq_def]) hb
    exact wres_view (view_lam m₀ a hA₀ e he (vok LAM hc) g5).1
      (lam_ok (ih n' rfl) hA₀ hs₀ he (vok LAM hc) g5 (fun _ _ => rfl) hb)
  by_cases g6 : e >>> 28 = 6
  · by_cases hc : tcnt m₀ FORALL (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g6, hc])).elim
    rw [hWalkW.k_hs_put.arm4 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hForallW.eq_def]) hb
    exact wres_view (view_forall m₀ a hA₀ e he (vok FORALL hc) g6).1
      (forall_ok (ih n' rfl) hA₀ hs₀ he (vok FORALL hc) g6 (fun _ _ => rfl) hb)
  by_cases g7 : e >>> 28 = 7
  · by_cases hc : tcnt m₀ LET (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g7, hc])).elim
    rw [hWalkW.k_hs_put.arm5 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hLetW.eq_def]) hb
    exact wres_view (view_let m₀ a hA₀ e he (vok LET hc) g7).1
      (let_ok (ih n' rfl) hA₀ hs₀ he (vok LET hc) g7 (fun _ _ => rfl) hb)
  by_cases g9 : e >>> 28 = 9
  · by_cases hc : tcnt m₀ PROJ (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g9, hc])).elim
    rw [hWalkW.k_hs_put.arm6 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hProjW.eq_def]) hb
    obtain ⟨hv, hnw, hxw⟩ := view_proj m₀ a hA₀ e he (vok PROJ hc) g9
    refine wres_view hv ?_
    rw [hProjW.arm1, hProjW.k_hoist_note.eq_def] at hb
    rcases h1 : hNoteW m₀ (tfld m₀ PROJ (tierW e) (idxW e) 0) i k tg ws sp with _ | ⟨sp₁, m₁⟩ <;> rw [h1] at hb
    · cases hb
    simp only at hb
    have hfr := hNoteW_iw h1
    have heq : m₁.arr64 PJREC = m₀.arr64 PJREC := hfr.1 _ (by decide) (by decide)
    have heq' : m₁.arr64 (tier1 PJREC) = m₀.arr64 (tier1 PJREC) := hfr.1 _ (by decide) (by decide)
    rw [tfld_arr_eq (R := PROJ) heq heq'] at hb
    exact wres_cons hnw h1 ((ih n' rfl) _ _ _ _ _ _ _ _ _ _ _ _ _
      (iw_arena hfr hA₀) hxw
      (memoRG_frame hsSch hsSch_wf bmKey _ [IW] [] (by decide) (by decide) _ _ hfr _ hs₀) hb)
  by_cases g1 : e >>> 28 = 1
  · by_cases hc : tcnt m₀ FVAR (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g1, hc])).elim
    rw [hWalkW.k_hs_put.arm7 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 g1 hc] at hb
    obtain ⟨n', rfl⟩ := arm0 _ (fun _ _ _ _ _ _ _ _ => by rw [hFvarW.eq_def]) hb
    obtain ⟨hv, hxw⟩ := view_fvar_idx m₀ a hA₀ e he (vok FVAR hc) g1
    rw [hFvarW.arm1] at hb
    exact wres_view hv ((ih n' rfl) _ _ _ _ _ _ _ _ _ _ _ _ _ hA₀ hxw hs₀ hb)
  have fin : hWalkW.k_hs_put n e i k tg ws sp fu (some m₀) = some (sp, m₀) → sp = sp' ∧ m₀ = m' := by
    intro h; rw [h] at hb; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb); exact ⟨rfl, rfl⟩
  by_cases g0 : e >>> 28 = 0
  · by_cases hc : tcnt m₀ BVAR (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g0, hc])).elim
    obtain ⟨rfl, rfl⟩ := fin (hWalkW.k_hs_put.arm8 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 g1 g0 hc)
    exact wres_view (view_bvar m₀ a hA₀ e he (vok BVAR hc) g0) (wres_pure hs₀)
  by_cases g2 : e >>> 28 = 2
  · by_cases hc : tcnt m₀ SORT (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g2, hc])).elim
    obtain ⟨rfl, rfl⟩ := fin (hWalkW.k_hs_put.arm9 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 g1 g0 g2 hc)
    obtain ⟨_, hv⟩ := view_sort m₀ a hA₀ e he (vok SORT hc) g2
    exact wres_view hv (wres_pure hs₀)
  by_cases g8 : e >>> 28 = 8
  · by_cases hc : tcnt m₀ LIT (tierW e) ≤ idxW e
    · exact (bad _ hc (by rw [hWalkW.k_hs_put.eq_def]; simp [hsc, g8, hc])).elim
    obtain ⟨rfl, rfl⟩ := fin (hWalkW.k_hs_put.arm10 n e i k tg ws sp fu m₀ hsc g3 g4 g5 g6 g7 g9 g1 g0 g2 g8 hc)
    obtain ⟨_, hv⟩ := view_lit m₀ a hA₀ e he (vok LIT hc) g8
    exact wres_view hv (wres_pure hs₀)
  rw [hWalkW.k_hs_put.eq_def] at hb; simp [hsc, g3, g4, g5, g6, g7, g9, g1, g0, g2, g8] at hb

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
  intro m m' a k i tg ws sp ro rc r sp' seen acc rules hA hs hlen hR hb
  induction n generalizing m sp r seen acc rules with
  | zero => rw [hRulesGoW.eq_def] at hb; cases hb
  | succ n ih =>
    by_cases hc : rc ≤ r
    · rw [hRulesGoW.arm1 n m k i tg ws sp ro rc r hc] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have : rules = [] := List.eq_nil_of_length_eq_zero (by
        have := UInt64.le_iff_toNat_le.mp hc; omega)
      subst this
      exact wres_pure hs
    rw [hRulesGoW.arm2 n m k i tg ws sp ro rc r hc, hRulesGoW.k_hoist_walk.eq_def] at hb
    obtain _ | ⟨rule, rs⟩ := rules
    · exfalso; apply hc; rw [UInt64.le_iff_toNat_le]; simp at hlen; omega
    obtain ⟨hw0, hr0⟩ := hR 0 (by simp)
    have h0 : r + UInt64.ofNat 0 = r := by simp
    rw [h0] at hw0 hr0
    simp only [List.getElem_cons_zero] at hr0
    rcases h1 : hWalkW n m (rdW (m.arr64 DIND) (ro + 11 * r + 8)) i k tg ws sp 4000000000 with _ | ⟨sp₁, m₁⟩ <;> rw [h1] at hb
    · cases hb
    simp only at hb
    have W1 := walkOK n m m₁ a _ i k tg ws sp 4000000000 sp₁ seen acc hA hw0 hs h1
    rw [usedConstsRules.eq_2, hr0]
    refine wres_bind W1 fun seen₁ ns₁ hs1 _ => ?_
    have hr1 : (r + 1).toNat = r.toNat + 1 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hc)
      have := rc.toNat_lt
      rw [UInt64.toNat_add]; simp; omega
    have hD := W1.arr DIND (by decide) (by decide) (by decide)
    refine ih m₁ sp₁ (r + 1) seen₁ _ rs (W1.arena hA) hs1 (by simp at hlen; omega) ?_ hb
    intro q hq
    have hq' : r + UInt64.ofNat (q + 1) = r + 1 + UInt64.ofNat q := by
      apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add]; omega
    obtain ⟨h1', h2'⟩ := hR (q + 1) (by simp; omega)
    rw [hD, ← hq']
    exact ⟨h1', by simpa using h2'⟩

/-- The block members `cs` are the constant records the pointers `DIND[o + q ‥ o + c)` point to
(`decCIs` below some `t` at most the pool's top, as `IndDeclAt`; the offset not `0`, the pool's
top, which `trunc` clears, and no pointer `0`). -/
def BlockAt (m : Mem) (o c q : Word) (cs : List IConstantInfo) : Prop :=
  (∃ t, t ≤ ((m.arr64 DLP)[0]?.getD 0).toNat ∧
    decCIs (trunc (m.arr64 DLP) t) (fun _ => none) (o.toNat + q.toNat) (c.toNat - q.toNat) = some cs) ∧
  o.toNat + c.toNat < 2 ^ 63 ∧ o.toNat ≠ 0 ∧
  (∀ j, q.toNat ≤ j → j < c.toNat → (m.arr64 DLP)[o.toNat + j]?.getD 0 ≠ 0) ∧
  q ≤ c

/-- `BlockAt` without the bound on `o + c` (the decoding bounds the words read). -/
def BlockAt' (m : Mem) (o c q : Word) (cs : List IConstantInfo) : Prop :=
  (∃ t, t ≤ ((m.arr64 DLP)[0]?.getD 0).toNat ∧
    decCIs (trunc (m.arr64 DLP) t) (fun _ => none) (o.toNat + q.toNat) (c.toNat - q.toNat) = some cs) ∧
  o.toNat ≠ 0 ∧
  (∀ j, q.toNat ≤ j → j < c.toNat → (m.arr64 DLP)[o.toNat + j]?.getD 0 ≠ 0) ∧
  q ≤ c

theorem blockGo_ok' (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k i tg ws sp o c q sp' : Word) (seen : Std.HashSet EIdx)
      (acc : Array NIdx) (cs : List IConstantInfo),
    ArenaR m a → SeenR m seen → BlockAt' m o c q cs →
    hBlockGoW n m k i tg ws sp o c q = some (sp', m') →
    WRes m m' i k tg ws sp sp' acc (usedConstsBlock seen acc cs) a := by
  intro m m' a k i tg ws sp o c q sp' seen acc cs hA hs hB hb
  induction n generalizing m sp q seen acc cs with
  | zero => rw [hBlockGoW.eq_def] at hb; cases hb
  | succ n ih =>
    obtain ⟨⟨t, ht, hdec⟩, ho0, hptr, hqc⟩ := hB
    by_cases hc : c ≤ q
    · rw [hBlockGoW.arm1 n m k i tg ws sp o c q hc] at hb
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      have : c.toNat - q.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hc; omega
      rw [this] at hdec
      cases decCIs_zero hdec
      exact wres_pure hs
    have hqc' : q.toNat < c.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hc)
    have hk : c.toNat - q.toNat = (c.toNat - q.toNat - 1) + 1 := by omega
    rw [hk] at hdec
    obtain ⟨pN, ci, cs', hp, hci, hdec', rfl⟩ := decCIs_succ hdec
    have ht64 : t < 2 ^ 64 := Nat.lt_of_le_of_lt ht (UInt64.toNat_lt _)
    obtain ⟨pw, hpw, rfl⟩ : ∃ pw, (trunc (m.arr64 DLP) t)[o.toNat + q.toNat]? = some pw ∧
        pN = pw.toNat := by
      simp only [nat?] at hp
      cases h : (trunc (m.arr64 DLP) t)[o.toNat + q.toNat]? with
      | none => rw [h] at hp; cases hp
      | some pw => rw [h] at hp; exact ⟨pw, rfl, (Option.some.inj hp).symm⟩
    obtain ⟨hPp, hpt⟩ := trunc_get hpw (by omega)
    have hpi : (o + q).toNat = o.toNat + q.toNat := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hpd : rdW (m.arr64 DIND) (o + q) = pw := rdW_of hpi hPp
    have hpN : 0 < pw.toNat := by
      have := hptr q.toNat (Nat.le_refl _) hqc'
      rw [hPp] at this
      have h0 : pw ≠ 0 := by simpa using this
      exact Nat.pos_of_ne_zero fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
    obtain ⟨cv, kw, w, htc, hkw, hw4, hwl, hty, hrec⟩ := decCI_walk hci
    obtain ⟨hPk, -⟩ := trunc_get hkw hpN
    obtain ⟨hP4, h4t⟩ := trunc_get hw4 (by omega)
    have hp4 : (pw + 4).toNat = pw.toNat + 4 := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)
    rw [hBlockGoW.arm2 n m k i tg ws sp o c q hc, hpd, rdW_of hp4 hP4, hBlockGoW.k_hoist_walk.eq_def] at hb
    rcases h1 : hWalkW n m w i k tg ws sp 4000000000 with _ | ⟨sp₁, m₁⟩ <;> rw [h1] at hb
    · cases hb
    simp only at hb
    have W1 := walkOK n m m₁ a w i k tg ws sp 4000000000 sp₁ seen acc hA hwl hs h1
    have hD1 := W1.arr DIND (by decide) (by decide) (by decide)
    rw [hD1, rdW_of rfl hPk] at hb
    rw [usedConstsBlock.eq_2]
    simp only [htc, hty]
    refine wres_bind W1 fun seen₁ ns₁ hs1 _ => ?_
    have next : ∀ m₂ sp₂ seen₂ acc₂, ArenaR m₂ a → SeenR m₂ seen₂ → m₂.arr64 DLP = m.arr64 DLP →
        hBlockGoW n m₂ k i tg ws sp₂ o c (q + 1) = some (sp', m') →
        WRes m₂ m' i k tg ws sp₂ sp' acc₂ (usedConstsBlock seen₂ acc₂ cs') a := by
      intro m₂ sp₂ seen₂ acc₂ hA2 hs2 hP hb2
      have hq1 : (q + 1).toNat = q.toNat + 1 := by
        have := c.toNat_lt
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)
      refine ih m₂ sp₂ (q + 1) seen₂ acc₂ cs' hA2 hs2 ⟨⟨t, by rw [hP]; exact ht, ?_⟩, ho0,
        fun j h1 h2 => by rw [hP]; exact hptr j (by omega) h2,
        UInt64.le_iff_toNat_le.mpr (by omega)⟩ hb2
      rw [hP, hq1, show c.toNat - (q.toNat + 1) = c.toNat - q.toNat - 1 by omega, ← Nat.add_assoc]
      exact hdec'
    rcases hrec with ⟨h5, mi, rp, ow, cw, rules, rfl, h7, h8, hr⟩ | ⟨h5, hn⟩
    · rw [ite_eq_left h5] at hb
      obtain ⟨hP7, h7t⟩ := trunc_get h7 (by omega)
      obtain ⟨hP8, h8t⟩ := trunc_get h8 (by omega)
      have hp7 : (pw + 7).toNat = pw.toNat + 7 := by
        rw [UInt64.toNat_add, show (7 : Word).toNat = 7 from rfl]; exact Nat.mod_eq_of_lt (by omega)
      have hp8 : (pw + 8).toNat = pw.toNat + 8 := by
        rw [UInt64.toNat_add, show (8 : Word).toNat = 8 from rfl]; exact Nat.mod_eq_of_lt (by omega)
      rw [rdW_of hp7 hP7, rdW_of hp8 hP8, hBlockGoW.k_hoist_rules_go.eq_def] at hb
      obtain ⟨hlen, hrr⟩ := decRules_facts hr
      have hRA : RulesAt m₁ ow 0 rules := by
        intro q hq
        obtain ⟨w', hw', hl', hr'⟩ := hrr q hq
        obtain ⟨hPw, hwt⟩ := trunc_get hw' (by omega)
        rw [hD1, rdW_of (idx11 ow q (by omega)) hPw]
        exact ⟨hl', hr'⟩
      rcases h2 : hRulesGoW n m₁ k i tg ws sp₁ ow cw 0 with _ | ⟨sp₂, m₂⟩ <;> rw [h2] at hb
      · cases hb
      simp only [hBlockGoW.j1.eq_def] at hb
      have W2 : WRes m₁ m₂ i k tg ws sp₁ sp₂ (acc ++ (List.map decI ns₁).toArray)
          (usedConstsRules seen₁ (acc ++ (List.map decI ns₁).toArray) rules) a := hoistRulesGo_ok n m₁ m₂ a k i tg ws sp₁ ow cw 0 sp₂ seen₁
        (acc ++ (List.map decI ns₁).toArray) rules (W1.arena hA) hs1 (by simp; omega) hRA h2
      refine wres_bind W2 fun seen₂ ns₂ hs2 _ => ?_
      exact next m₂ sp₂ seen₂ _ (W2.arena (W1.arena hA)) hs2
        (by rw [W2.arr DLP (by decide) (by decide) (by decide), W1.arr DLP (by decide) (by decide) (by decide)]) hb
    · rw [ite_eq_right h5, hBlockGoW.j1.eq_def] at hb
      have N := next m₁ sp₁ seen₁ (acc ++ (List.map decI ns₁).toArray) (W1.arena hA) hs1 hD1 hb
      cases ci with
      | recInfo v mi rp rules => exact absurd rfl (hn v mi rp rules)
      | _ => simp only [pure_bind]; exact N

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
  intro m m' a k i tg ws sp o c q sp' seen acc cs hA hs hB hb
  obtain ⟨h1, -, h3⟩ := hB
  exact blockGo_ok' n m m' a k i tg ws sp o c q sp' seen acc cs hA hs ⟨h1, h3⟩ hb

theorem seenR_clear {m : Mem} {seen : Std.HashSet EIdx} (hs : SeenR m seen)
    (h0 : ¬ rdW (m.arr64 CTL) hsSch.cs + 2 = 0) :
    SeenR (mclearG hsSch m) ∅ ∧ MemFrame [HSEEN] [73, 74] m (mclearG hsSch m) := by
  refine ⟨memoRG_congr (fun x => ?_) (memoRG_clear hsSch hsSch_wf bmKey (fun _ => ()) m _ hs h0), ?_⟩
  · rw [Std.HashMap.getElem?_empty]; exact Std.HashMap.getElem?_empty
  · refine (mclearG_frame hsSch m).mono (by simp) ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide

/-- The finish of `usedConsts`: the array of a walk from `#[]`. -/
theorem fin_ok {m m' : Mem} {i k tg ws sp sp' : Word} {a : AState}
    {Y : AM (Std.HashSet EIdx × Array NIdx)} (h : WRes m m' i k tg ws sp sp' #[] Y a) :
    ∃ ns : List Word,
      (Y >>= fun p => pure p.2).run a = .ok ((ns.map decI).toArray, a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ (∃ seen', SeenR m' seen') ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  obtain ⟨seen', ns, hY, hw, hs, mn, hn, hf⟩ := h
  refine ⟨ns, ?_, hw, ⟨seen', hs⟩, mn, hn, hf⟩
  rw [StateT.run_bind, hY, except_ok_bind, Array.empty_append]; rfl

theorem fin2_ok {m m' : Mem} {i k tg ws sp sp' : Word} {a : AState}
    {X : AM (Std.HashSet EIdx × Array NIdx)}
    {G : Std.HashSet EIdx → Array NIdx → AM (Std.HashSet EIdx × Array NIdx)}
    (h : WRes m m' i k tg ws sp sp' #[] (X >>= fun x => G x.1 x.2) a) :
    ∃ ns : List Word,
      (X >>= fun x => (G x.1 x.2 >>= fun p => pure p.2)).run a = .ok ((ns.map decI).toArray, a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ (∃ seen', SeenR m' seen') ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  have := fin_ok h
  simpa only [bind_assoc] using this

/-- **`hoist_deps_of` refines `IDeclaration.usedConsts`** (record `r` of `DECL`, `x = 1 + 8 r`). -/
theorem hoistDepsOf_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k i r tg ws sp sp' : Word) (d : IDeclaration),
    ArenaR m a → (∃ seen, SeenR m seen) → r.toNat < 2 ^ 59 →
    DeclAtF (m.arr64 DECL) (m.arr64 DLP) r.toNat d → RecOK (m.arr64 DECL) (m.arr64 DLP) r.toNat →
    hDepsOfW n m k i (1 + 8 * r) tg ws sp = some (sp', m') →
    ∃ ns : List Word,
      (IDeclaration.usedConsts d).run a = .ok ((ns.map decI).toArray, a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ (∃ seen', SeenR m' seen') ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  intro m m' a k i r tg ws sp sp' d hA ⟨seen, hs⟩ hr hD hok hb
  cases n with
  | zero => rw [hDepsOfW.eq_def] at hb; cases hb
  | succ n =>
  by_cases h0 : rdW (m.arr64 CTL) hsSch.cs + 2 = 0
  · rw [hDepsOfW.eq_def] at hb; simp [h0] at hb
  obtain ⟨hs₀, hf₀⟩ := seenR_clear hs h0
  have hA₀ := frame_ext' hf₀ hA
  have hDe : (mclearG hsSch m).arr64 DECL = m.arr64 DECL := hf₀.1 _ (by decide) (by decide)
  have e0 := rdW_dw0 (m.arr64 DECL) r hr
  have e2 : rdW (m.arr64 DECL) (1 + 8 * r + 2) = dw (m.arr64 DECL) r.toNat 2 :=
    rdW_dw (m.arr64 DECL) r 2 hr (by decide)
  have e3 : rdW (m.arr64 DECL) (1 + 8 * r + 3) = dw (m.arr64 DECL) r.toNat 3 :=
    rdW_dw (m.arr64 DECL) r 3 hr (by decide)
  have e4 : rdW (m.arr64 DECL) (1 + 8 * r + 4) = dw (m.arr64 DECL) r.toNat 4 :=
    rdW_dw (m.arr64 DECL) r 4 hr (by decide)
  have e5 : rdW (m.arr64 DECL) (1 + 8 * r + 5) = dw (m.arr64 DECL) r.toNat 5 :=
    rdW_dw (m.arr64 DECL) r 5 hr (by decide)
  rw [hDepsOfW.eq_def] at hb
  simp only [h0, ite_false, hDe, e0, e2, e3, e4] at hb
  -- the kinds
  have one : ∀ {c : IConstantVal}, dw (m.arr64 DECL) r.toNat 0 ≠ 6 →
      decI (dw (m.arr64 DECL) r.toNat 4) = c.type →
      hWalkW n (mclearG hsSch m) (dw (m.arr64 DECL) r.toNat 4) i k tg ws sp 4000000000 = some (sp', m') →
      ∃ ns : List Word,
        (IDeclaration.usedConsts (.axiomDecl c)).run a = .ok ((ns.map decI).toArray, a) ∧
        (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ (∃ seen', SeenR m' seen') ∧
        ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
    intro c h6 hty hw
    have W := walkOK n _ m' a _ i k tg ws sp 4000000000 sp' ∅ #[] hA₀ (hok.1 h6).2.1 hs₀ hw
    simp only [IDeclaration.usedConsts]
    rw [← hty]
    exact fin_ok (wres_pre hf₀ W)
  have two : ∀ {c : IConstantVal} {v : EIdx}, dw (m.arr64 DECL) r.toNat 0 ≠ 6 →
      decI (dw (m.arr64 DECL) r.toNat 4) = c.type → decI (dw (m.arr64 DECL) r.toNat 5) = v →
      hDepsOfW.k_hoist_walk n k i (1 + 8 * r) tg ws
        (hWalkW n (mclearG hsSch m) (dw (m.arr64 DECL) r.toNat 4) i k tg ws sp 4000000000) =
        some (sp', m') →
      ∃ ns : List Word,
        (usedConstsGo ∅ #[] coreWalkFuel c.type >>= fun x =>
          (usedConstsGo x.1 x.2 coreWalkFuel v >>= fun p => pure p.2)).run a =
            .ok ((ns.map decI).toArray, a) ∧
        (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ (∃ seen', SeenR m' seen') ∧
        ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
    intro c v h6 hty hv hw
    rw [hDepsOfW.k_hoist_walk.eq_def] at hw
    rcases h1 : hWalkW n (mclearG hsSch m) (dw (m.arr64 DECL) r.toNat 4) i k tg ws sp 4000000000 with _ | ⟨sp₁, m₁⟩ <;> rw [h1] at hw
    · cases hw
    simp only at hw
    have W1 := walkOK n _ m₁ a _ i k tg ws sp 4000000000 sp₁ ∅ #[] hA₀ (hok.1 h6).2.1 hs₀ h1
    rw [W1.arr DECL (by decide) (by decide) (by decide), hDe, e5] at hw
    have W2 := walk_then (walkOK n) hA₀ W1 (hok.1 h6).2.2
      (f := fun x => usedConstsGo x.1 x.2 (4000000000 : Word).toNat
        (decE (dw (m.arr64 DECL) r.toNat 5))) (fun _ _ => rfl) hw
    rw [← hty, ← hv]
    exact fin2_ok (G := fun s ac => usedConstsGo s ac (4000000000 : Word).toNat
      (decE (dw (m.arr64 DECL) r.toNat 5))) (wres_pre hf₀ W2)
  cases d with
  | axiomDecl cv =>
    obtain ⟨h1, -, hty, -⟩ := hD
    rw [ite_eq_left h1] at hb
    exact one (by rw [h1]; decide) hty hb
  | defnDecl cv v hh =>
    obtain ⟨h2, ⟨-, hty, -⟩, hv, -⟩ := hD
    rw [ite_eq_right (by rw [h2]; decide), ite_eq_left (Or.inl h2)] at hb
    exact two (by rw [h2]; decide) hty hv hb
  | thmDecl cv v =>
    obtain ⟨h2, ⟨-, hty, -⟩, hv⟩ := hD
    rw [ite_eq_right (by rw [h2]; decide), ite_eq_left (Or.inr (Or.inl h2))] at hb
    exact two (by rw [h2]; decide) hty hv hb
  | opaqueDecl cv v =>
    obtain ⟨h2, ⟨-, hty, -⟩, hv⟩ := hD
    rw [ite_eq_right (by rw [h2]; decide), ite_eq_left (Or.inr (Or.inr h2))] at hb
    exact two (by rw [h2]; decide) hty hv hb
  | indDecl b nP =>
    obtain ⟨h6, -, t, ht, hdec⟩ := hD
    rw [ite_eq_right (by rw [h6]; decide), ite_eq_right (by rw [h6]; decide),
      ite_eq_right (by rw [h6]; exact fun h => h rfl)] at hb
    obtain ⟨ho0, hptr⟩ := hok.2 h6
    have hP : (mclearG hsSch m).arr64 DLP = m.arr64 DLP := hf₀.1 _ (by decide) (by decide)
    have hBA : BlockAt' (mclearG hsSch m) (dw (m.arr64 DECL) r.toNat 2) (dw (m.arr64 DECL) r.toNat 3) 0 b :=
      ⟨⟨t, by rw [hP]; exact ht, by rw [hP]; simpa using hdec⟩, ho0,
        fun j _ hj => by rw [hP]; exact hptr j hj, UInt64.zero_le⟩
    have W := blockGo_ok' n _ m' a k i tg ws sp _ _ 0 sp' ∅ #[] b hA₀ hs₀ hBA hb
    simp only [IDeclaration.usedConsts]
    exact fin_ok (wres_pre hf₀ W)
  | basisDecl kd => exact hD.elim
  | quotDecl qk cv =>
    obtain ⟨h5, -, -⟩ := hD
    rw [ite_eq_right (by rw [h5]; decide), ite_eq_right (by rw [h5]; decide), ite_eq_left (by rw [h5]; decide)] at hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
    exact ⟨[], rfl, by simp, ⟨∅, hs₀⟩, m, rfl, hf₀⟩

end L.Checker
