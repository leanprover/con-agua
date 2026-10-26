import ConAgua.Checker.HoistWalkRef
import ConAgua.Checker.HoistIndexRef
import ConAgua.Checker.HoistClosureTwin

/-!
# L's closure marks at push: the records it marks form a closed set (lane `front4`)

`hoist_closure(i, j, …)` marks `j`, then pops a record, walks it (`hoist_deps_of`) and has
`hoist_note` mark and push each successor that is not marked yet. The invariant: every marked
record not on the stack has been walked (the twin's `usedConsts` succeeds on it) and all its
successors are marked; every marked record is reachable from `j` through marked records; the stack
holds distinct marked records. At the end the newly marked set `N` is closed and reachable from
`j`, which is what `HoistTwin.closure_exact` needs to conclude that the twin's closure is `T₀`
plus `N ↦ i`.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind
open L.Checker.HoistTwin

namespace L.Checker

/-! ## The stack and the frame -/

/-- The stack `IW[ws ‥ ws + sp)`, as positions. -/
def stk (m : Mem) (ws sp : Word) : List Nat :=
  (List.range sp.toNat).map fun q => (rdW (m.arr64 IW) (ws + UInt64.ofNat q)).toNat

/-- The twin's constants of record `k` (`usedConsts` is deterministic; `[]` where it fails). -/
noncomputable def depsOf (ds : Array IDeclaration) (a : AState) (k : Nat) : List NIdx :=
  if h : k < ds.size then
    match (IDeclaration.usedConsts ds[k]).run a with
    | .ok (ns, _) => ns.toList
    | .error _ => []
  else []

/-- Record `k`'s constants are computed by the twin, in the same state. -/
def Good (ds : Array IDeclaration) (a : AState) (k : Nat) : Prop :=
  ∃ h : k < ds.size, (IDeclaration.usedConsts ds[k]).run a = .ok ((depsOf ds a k).toArray, a)

theorem good_of_run {ds : Array IDeclaration} {a : AState} {k : Nat} (h : k < ds.size)
    {ns : Array NIdx} (hr : (IDeclaration.usedConsts ds[k]).run a = .ok (ns, a)) :
    Good ds a k ∧ depsOf ds a k = ns.toList := by
  have hd : depsOf ds a k = ns.toList := by simp [depsOf, h, hr]
  exact ⟨⟨h, by rw [hd, hr]⟩, hd⟩

/-- **What the hoist's passes keep**: the `IW` words outside the targets and the stack, and every
other array but `HSEEN` and the `CTL` words but `73‥74`. -/
def HFr (tg ws : Word) (c : Nat) (m m' : Mem) : Prop :=
  MemFrame [IW, HSEEN] [73, 74] m m' ∧
    ∀ x : Nat, (x < tg.toNat ∨ ws.toNat + c ≤ x) → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?

theorem HFr.refl (tg ws : Word) (c : Nat) (m : Mem) : HFr tg ws c m m :=
  ⟨MemFrame.refl _ _ _, fun _ _ => rfl⟩

theorem HFr.trans {tg ws : Word} {c : Nat} {m₁ m₂ m₃ : Mem} (h₁ : HFr tg ws c m₁ m₂)
    (h₂ : HFr tg ws c m₂ m₃) : HFr tg ws c m₁ m₃ :=
  ⟨h₁.1.trans h₂.1, fun x hx => (h₂.2 x hx).trans (h₁.2 x hx)⟩

/-- **The hoist's setting**: the store, a visited set, the stream in the order `ord` (below
`2 ^ 60` records), the name index (positions of the stream), and three
disjoint slices of `IW`: `ord`, the targets `tg`, the stack `ws`, `c` words each. -/
structure HEnv (m : Mem) (a : AState) (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat)
    (ord tg ws : Word) (c : Nat) : Prop where
  arena : ArenaR m a
  seen : ∃ s, SeenR m s
  ordR : OrdR m ord ds
  size : ds.size = c
  c60 : c < 2 ^ 60
  nix : NixR m idx
  nixlt : ∀ (n : NIdx) (j : Nat), idx[n]? = some j → j < c
  rg1 : ord.toNat + c ≤ tg.toNat
  rg2 : tg.toNat + c ≤ ws.toNat
  rg3 : ws.toNat + c ≤ (m.arr64 IW).size
  isz : (m.arr64 IW).size < 2 ^ 64
  top : ws.toNat + c ≤ iwTop m
  iwok : IWOK m

theorem addW_toNat (x : Word) (k : Nat) (h : x.toNat + k < 2 ^ 64) :
    (x + UInt64.ofNat k).toNat = x.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega

theorem hnSch_wf : hnSch.WF := ⟨by decide, by decide⟩

/-- **The setting survives the hoist's passes.** -/
theorem HEnv.frame {m m' : Mem} {a : AState} {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {ord tg ws : Word} {c : Nat} (hE : HEnv m a ds idx ord tg ws c) (hf : HFr tg ws c m m')
    (hs : ∃ s, SeenR m' s) : HEnv m' a ds idx ord tg ws c := by
  have hD : ∀ b, b ∉ [IW, HSEEN] → b ≠ CTL → m'.arr64 b = m.arr64 b := hf.1.1
  have hDECL : m'.arr64 DECL = m.arr64 DECL := hD DECL (by decide) (by decide)
  have hDLP : m'.arr64 DLP = m.arr64 DLP := hD DLP (by decide) (by decide)
  have hsz : (m'.arr64 IW).size = (m.arr64 IW).size := hf.1.2.2.1 IW
  have htop : iwTop m' = iwTop m := by
    simp only [iwTop]; rw [hf.1.2.1 200 (by decide)]
  have hA : ∀ b ∈ [IW, HSEEN], 64 ≤ b ∧ b < 256 := by decide
  have hC : ∀ x ∈ ([73, 74] : List Word), 64 ≤ x.toNat := by simp
  refine ⟨ArenaR.frame_ext [IW, HSEEN] [73, 74] hA hC m m' hf.1 a hE.arena, hs,
    ?_, hE.size, hE.c60, ?_, hE.nixlt, hE.rg1, hE.rg2, by rw [hsz]; exact hE.rg3,
    by rw [hsz]; exact hE.isz, by rw [htop]; exact hE.top, ?_⟩
  · intro k hk
    have hk' : k < c := hE.size ▸ hk
    have hn : (ord + UInt64.ofNat k).toNat = ord.toNat + k :=
      addW_toNat ord k (by have := hE.rg1; have := hE.rg2; have := hE.rg3; have := hE.isz; omega)
    have hr : rdW (m'.arr64 IW) (ord + UInt64.ofNat k) = rdW (m.arr64 IW) (ord + UInt64.ofNat k) := by
      simp only [rdW, hn]
      rw [hf.2 _ (Or.inl (by have := hE.rg1; omega))]
    rw [hr, hDECL, hDLP]
    exact hE.ordR k hk
  · exact memoRV_frame hnSch hnSch_wf nmKey _ [IW, HSEEN] [73, 74] (by decide) (by decide) m m' hf.1
      (fun _ _ h => h) idx hE.nix
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hE.iwok
    have hER : m'.arr64 EREC = m.arr64 EREC := hD EREC (by decide) (by decide)
    have h129 : erTop m' = erTop m := by simp only [erTop]; rw [hf.1.2.1 129 (by decide)]
    refine ⟨by rw [htop, hsz]; exact h1, by rw [h129, hER]; exact h2, by rw [hsz]; exact h3,
      by rw [hER]; exact h4, by rw [hf.1.2.2.1 CTL]; exact h5⟩

/-- **What an allocation keeps**: `IW` and `CTL[200]` only, the pool grown. -/
def AFr (m m' : Mem) : Prop := MemFrame [IW] [200] m m' ∧ IWGrow m m' ∧ IWOK m'

theorem AFr.refl (m : Mem) (h : IWOK m) : AFr m m := ⟨MemFrame.refl _ _ _, IWGrow.refl m, h⟩

theorem AFr.trans {m₁ m₂ m₃ : Mem} (h₁ : AFr m₁ m₂) (h₂ : AFr m₂ m₃) : AFr m₁ m₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₂.2.2⟩

/-- **The setting survives an allocation.** -/
theorem HEnv.frameA {m m' : Mem} {a : AState} {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {ord tg ws : Word} {c : Nat} (hE : HEnv m a ds idx ord tg ws c) (hf : AFr m m') :
    HEnv m' a ds idx ord tg ws c := by
  have hD : ∀ b, b ∉ [IW] → b ≠ CTL → m'.arr64 b = m.arr64 b := hf.1.1
  have hDECL : m'.arr64 DECL = m.arr64 DECL := hD DECL (by decide) (by decide)
  have hDLP : m'.arr64 DLP = m.arr64 DLP := hD DLP (by decide) (by decide)
  have hsz : (m'.arr64 IW).size = (m.arr64 IW).size := hf.1.2.2.1 IW
  have hA : ∀ b ∈ [IW], 64 ≤ b ∧ b < 256 := by decide
  have hC : ∀ x ∈ ([200] : List Word), 64 ≤ x.toNat := by simp
  obtain ⟨s, hs⟩ := hE.seen
  refine ⟨ArenaR.frame_ext [IW] [200] hA hC m m' hf.1 a hE.arena,
    ⟨s, memoRG_frame hsSch hsSch_wf bmKey _ [IW] [200] (by decide) (by decide) m m' hf.1 _ hs⟩,
    ?_, hE.size, hE.c60, ?_, hE.nixlt, hE.rg1, hE.rg2, by rw [hsz]; exact hE.rg3,
    by rw [hsz]; exact hE.isz, Nat.le_trans hE.top hf.2.1.1, hf.2.2⟩
  · intro k hk
    have hk' : k < c := hE.size ▸ hk
    have hn : (ord + UInt64.ofNat k).toNat = ord.toNat + k :=
      addW_toNat ord k (by have := hE.rg1; have := hE.rg2; have := hE.rg3; have := hE.isz; omega)
    have hr : rdW (m'.arr64 IW) (ord + UInt64.ofNat k) = rdW (m.arr64 IW) (ord + UInt64.ofNat k) := by
      simp only [rdW, hn]
      rw [hf.2.1.2.2.1 _ (by have := hE.rg1; have := hE.rg2; have := hE.top; omega)]
    rw [hr, hDECL, hDLP]
    exact hE.ordR k hk
  · exact memoRV_frame hnSch hnSch_wf nmKey _ [IW] [200] (by decide) (by decide) m m' hf.1
      (fun _ _ h => h) idx hE.nix

/-! ## One note -/

theorem rdW_addr (A : Array Word) (x : Word) (k : Nat) (h : x.toNat + k < 2 ^ 64) :
    rdW A (x + UInt64.ofNat k) = A[x.toNat + k]?.getD 0 := by
  simp only [rdW, addW_toNat x k h]

theorem set64_addr (m : Mem) (x : Word) (k : Nat) (v : Word) (h : x.toNat + k < 2 ^ 64) :
    (m.set64 IW (x + UInt64.ofNat k) v).arr64 IW = (m.arr64 IW).set! (x.toNat + k) v := by
  rw [Mem.arr64_set64_same, addW_toNat x k h]

theorem tgW_ne_zero (t : Nat) (h : t + 1 < 2 ^ 64) : tgW (some t) ≠ 0 := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [tgW, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h] at this; simp at this

/-- A nodup list of positions below `c`, all marked, and one more unmarked position below `c`:
the list is shorter than `c`. -/
theorem nodup_len_lt {S : List Nat} {c j : Nat} (hS : S.Nodup) (hlt : ∀ x ∈ S, x < c)
    (hj : j < c) (hjS : j ∉ S) : S.length < c := by
  have h1 : (j :: S).Nodup := List.nodup_cons.mpr ⟨hjS, hS⟩
  have h2 : (j :: S) ⊆ List.range c := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_range.mpr hj
    · exact List.mem_range.mpr (hlt x hx)
  have := List.Nodup.length_le_of_subset h1 h2
  simp at this
  omega

theorem stk_length (m : Mem) (ws sp : Word) : (stk m ws sp).length = sp.toNat := by
  simp [stk]

/-- The targets' values are positions. -/
def TgtV (T : Std.HashMap Nat Nat) (c : Nat) : Prop := ∀ (x t : Nat), T[x]? = some t → t < c

/-- The stack holds distinct marked positions. -/
def StkOK (m : Mem) (ws sp : Word) (c : Nat) (T : Std.HashMap Nat Nat) : Prop :=
  (stk m ws sp).Nodup ∧ ∀ x ∈ stk m ws sp, x < c ∧ (T[x]?).isSome

/-- **One note**: `hoist_note` marks and pushes `j` when the name's first position `j` lies after
`i`, is not `k` and is not marked; otherwise nothing changes. -/
theorem note_ok {m m' : Mem} {a : AState} {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {ord tg ws : Word} {c : Nat} (hE : HEnv m a ds idx ord tg ws c) {T : Std.HashMap Nat Nat}
    (hT : TgtR m tg c T) (hTv : TgtV T c) {sp sp' : Word} (hS : StkOK m ws sp c T)
    {i k : Nat} (hi : i < c) (hk : k < c) {w : Word} (hw : w.toNat < 2 ^ 32)
    (h : hNoteW m w (UInt64.ofNat i) (UInt64.ofNat k) tg ws sp = some (sp', m')) :
    (∃ j, idx[(decI w : NIdx)]? = some j ∧ i < j ∧ j ≠ k ∧ T[j]? = none ∧
      sp'.toNat = sp.toNat + 1 ∧ MemFrame [IW] [] m m' ∧ HFr tg ws c m m' ∧
      TgtR m' tg c (T.insert j i) ∧
      stk m' ws sp' = stk m ws sp ++ [j]) ∨
    ((¬ ∃ j, idx[(decI w : NIdx)]? = some j ∧ i < j ∧ j ≠ k ∧ T[j]? = none) ∧ sp' = sp ∧ m' = m) := by
  have hc := hE.c60
  have r1 := hE.rg1; have r2 := hE.rg2; have r3 := hE.rg3; have r4 := hE.isz
  unfold hNoteW at h
  rcases hx : hIxW m w with _ | ⟨r, m₁⟩ <;> rw [hx] at h
  · cases h
  obtain ⟨hm1, hr⟩ := hoistIx_ok m m₁ w r idx hE.nix hw hx
  subst m₁
  cases ho : idx[(decI w : NIdx)]? with
  | none =>
    rw [ho] at hr
    simp only [tgW] at hr
    subst hr
    rw [hNoteW.k_hoist_ix.arm2 _ _ _ _ _ _ _ (by simp)] at h
    cases h
    exact Or.inr ⟨by simp, rfl, rfl⟩
  | some j =>
    rw [ho] at hr
    have hjc : j < c := hE.nixlt _ j ho
    simp only [tgW] at hr
    subst hr
    have hj1 : UInt64.ofNat (j + 1) - 1 = UInt64.ofNat j := by
      rw [UInt64.ofNat_add]; simp
    have htgj : tg + UInt64.ofNat (j + 1) - 1 = tg + UInt64.ofNat j := by
      rw [UInt64.sub_eq_add_neg, UInt64.add_assoc, ← UInt64.sub_eq_add_neg, hj1]
    have hrd : rdW (m.arr64 IW) (tg + UInt64.ofNat j) = tgW T[j]? := hT.1 j hjc
    -- the condition in `Nat`
    have hci : (UInt64.ofNat i + 1 < UInt64.ofNat (j + 1)) ↔ i < j := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
      simp only [UInt64.toNat_one]; omega
    have hck : (UInt64.ofNat (j + 1) ≠ UInt64.ofNat k + 1) ↔ j ≠ k := by
      rw [ne_eq, ne_eq, ← UInt64.toNat_inj, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
      simp only [UInt64.toNat_one]; omega
    have hcz : (rdW (m.arr64 IW) (tg + UInt64.ofNat (j + 1) - 1) = 0) ↔ T[j]? = none := by
      rw [htgj, hrd]
      cases hTj : T[j]? with
      | none => simp [tgW]
      | some t => simp only [reduceCtorEq, iff_false]; exact tgW_ne_zero t (by have := hTv j t hTj; omega)
    by_cases hcond : i < j ∧ j ≠ k ∧ T[j]? = none
    · obtain ⟨h1, h2, h3⟩ := hcond
      rw [hNoteW.k_hoist_ix.arm1 _ _ _ _ _ _ _ ⟨by
          intro e; have := congrArg UInt64.toNat e
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this; simp at this,
        hci.mpr h1, hck.mpr h2, hcz.mpr h3⟩] at h
      cases h
      left
      -- the stack is shorter than `c`
      have hjS : j ∉ stk m ws sp := fun hm => by
        have := (hS.2 j hm).2; rw [h3] at this; cases this
      have hlen : sp.toNat < c := by
        have := nodup_len_lt hS.1 (fun x hx => (hS.2 x hx).1) hjc hjS
        rwa [stk_length] at this
      have hspw : ws + sp = ws + UInt64.ofNat sp.toNat := by simp
      rw [htgj, hj1, hspw]
      have e1 := set64_addr m tg j (UInt64.ofNat i + 1) (by omega)
      have e2 := set64_addr (m.set64 IW (tg + UInt64.ofNat j) (UInt64.ofNat i + 1)) ws sp.toNat
        (UInt64.ofNat j) (by omega)
      rw [e1] at e2
      have hszIW : ((m.arr64 IW).set! (tg.toNat + j) (UInt64.ofNat i + 1)).size = (m.arr64 IW).size := by
        simp
      refine ⟨j, rfl, h1, h2, h3, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [UInt64.toNat_add, UInt64.toNat_one]; omega
      · exact (MemFrame.set64 m IW (by decide) _ _).trans
          ((MemFrame.set64 _ IW (by decide) _ _))
      · exact (MemFrame.set64 m IW (by decide) _ _).trans
          ((MemFrame.set64 _ IW (by decide) _ _)) |>.mono (by simp) (by simp)
      · intro x hx
        rw [e2]
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        rw [if_neg (by omega), if_neg (by omega)]
      · intro x hx
        rw [rdW_addr _ _ _ (by omega), e2]
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        rw [if_neg (by omega)]
        by_cases hxj : j = x
        · subst hxj
          rw [if_pos rfl, if_pos (by omega)]
          simp [Std.HashMap.getElem?_insert, tgW, UInt64.ofNat_add]
        · rw [if_neg (by omega)]
          rw [Std.HashMap.getElem?_insert, if_neg (by simpa using hxj), ← hT.1 x hx,
            rdW_addr _ _ _ (by omega)]
      · intro x hx
        rw [Std.HashMap.getElem?_insert, if_neg (by simp; omega)]
        exact hT.2 x hx
      · unfold stk
        rw [show (sp + 1).toNat = sp.toNat + 1 by rw [UInt64.toNat_add, UInt64.toNat_one]; omega,
          List.range_succ, List.map_append]
        congr 1
        · apply List.map_congr_left
          intro q hq
          have hq' := List.mem_range.mp hq
          rw [rdW_addr _ _ _ (by omega), rdW_addr _ _ _ (by omega), e2]
          simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
          rw [if_neg (by omega), if_neg (by omega)]
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
          rw [rdW_addr _ _ _ (by omega), e2]
          simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
          rw [if_pos trivial, if_pos (by rw [Array.size_setIfInBounds]; omega)]
          simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
    · rw [hNoteW.k_hoist_ix.arm2 _ _ _ _ _ _ _ (by
          rintro ⟨-, a1, a2, a3⟩; exact hcond ⟨hci.mp a1, hck.mp a2, hcz.mp a3⟩)] at h
      cases h
      right
      refine ⟨?_, rfl, rfl⟩
      rintro ⟨j', hj', a1, a2, a3⟩
      simp only [ho, Option.some.injEq] at hj'; subst hj'
      exact hcond ⟨a1, a2, a3⟩

theorem seen_frameIW {m m' : Mem} (hf : MemFrame [IW] [] m m') (h : ∃ s, SeenR m s) :
    ∃ s, SeenR m' s := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, memoRG_frame hsSch hsSch_wf bmKey _ [IW] [] (by decide) (by simp) m m' hf _ hs⟩

/-! ## The notes of one record -/

/-- **The notes of record `k`**: exactly the successors of `k` (through the constants `ns`) that
were not marked get marked `i` and pushed, each once. -/
theorem notes_ok {a : AState} {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {ord tg ws : Word} {c : Nat} {i k : Nat} (hi : i < c) (hk : k < c) :
    ∀ (ns : List Word) (m m' : Mem) (T : Std.HashMap Nat Nat) (sp sp' : Word),
    HEnv m a ds idx ord tg ws c → TgtR m tg c T → TgtV T c → StkOK m ws sp c T →
    (∀ w ∈ ns, w.toNat < 2 ^ 32) →
    notesW m (UInt64.ofNat i) (UInt64.ofNat k) tg ws sp ns = some (sp', m') →
    ∃ (T' : Std.HashMap Nat Nat) (new : List Nat), TgtR m' tg c T' ∧ TgtV T' c ∧
      MemFrame [IW] [] m m' ∧ HFr tg ws c m m' ∧ stk m' ws sp' = stk m ws sp ++ new ∧
      StkOK m' ws sp' c T' ∧ (∀ x : Nat, T'[x]? = if x ∈ new then some i else T[x]?) ∧
      (∀ x ∈ new, T[x]? = none ∧ Succ idx i (fun _ => ns.map decI) k x) ∧
      (∀ x : Nat, T[x]? = none → Succ idx i (fun _ => ns.map decI) k x → x ∈ new) := by
  intro ns
  induction ns with
  | nil =>
    intro m m' T sp sp' hE hT hTv hS _ h
    simp only [notesW, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨T, [], hT, hTv, MemFrame.refl _ _ _, HFr.refl _ _ _ _, by simp, hS, by simp, by simp, ?_⟩
    rintro x - ⟨n, hn, -⟩
    simp at hn
  | cons w ns ih =>
    intro m m' T sp sp' hE hT hTv hS hns h
    simp only [notesW] at h
    rcases h1 : hNoteW m w (UInt64.ofNat i) (UInt64.ofNat k) tg ws sp with _ | ⟨sp₁, m₁⟩ <;> rw [h1] at h
    · cases h
    have hw := hns w List.mem_cons_self
    rcases note_ok hE hT hTv hS hi hk hw h1 with
      ⟨j, hj, hij, hjk, hTj, hsp, hmf, hfr, hT₁, hstk⟩ | ⟨hno, hsp, hm⟩
    · have hE₁ := hE.frame hfr (seen_frameIW hmf hE.seen)
      have hTv₁ : TgtV (T.insert j i) c := by
        intro x t hx
        rw [Std.HashMap.getElem?_insert] at hx
        split at hx
        · cases hx; exact hi
        · exact hTv x t hx
      have hS₁ : StkOK m₁ ws sp₁ c (T.insert j i) := by
        rw [StkOK, hstk]
        refine ⟨?_, ?_⟩
        · refine List.nodup_append.mpr ⟨hS.1, by simp, ?_⟩
          intro x hx y hy e
          simp at hy; subst hy; subst e
          have := (hS.2 x hx).2; rw [hTj] at this; cases this
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · refine ⟨(hS.2 x hx).1, ?_⟩
            rw [Std.HashMap.getElem?_insert]
            split
            · rfl
            · exact (hS.2 x hx).2
          · simp at hx; subst hx
            exact ⟨hE.nixlt _ _ hj, by simp [Std.HashMap.getElem?_insert]⟩
      obtain ⟨T', new, hT', hTv', hmf', hfr', hstk', hS', hget, hnew, hall⟩ :=
        ih m₁ m' (T.insert j i) sp₁ sp' hE₁ hT₁ hTv₁ hS₁ (fun w hw => hns w (List.mem_cons_of_mem _ hw)) h
      refine ⟨T', j :: new, hT', hTv', hmf.trans hmf' |>.mono (by simp) (by simp), hfr.trans hfr',
        by rw [hstk', hstk]; simp, hS', ?_, ?_, ?_⟩
      · intro x
        rw [hget x, Std.HashMap.getElem?_insert]
        by_cases hx : x ∈ new
        · simp [hx]
        · by_cases e : j = x
          · subst e; simp
          · simp [hx, e, Ne.symm e]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hTj, decI w, by simp, hj, hij, hjk⟩
        · obtain ⟨h1, n, hn, h2⟩ := hnew x hx
          refine ⟨?_, n, by simp at hn ⊢; exact Or.inr hn, h2⟩
          rw [Std.HashMap.getElem?_insert] at h1
          split at h1
          · cases h1
          · exact h1
      · rintro x hx ⟨n, hn, h2⟩
        simp only [List.map_cons, List.mem_cons] at hn
        by_cases e : j = x
        · subst e; exact List.mem_cons_self
        · refine List.mem_cons_of_mem _ (hall x ?_ ?_)
          · rw [Std.HashMap.getElem?_insert, if_neg (by simpa using e)]; exact hx
          · rcases hn with hn | hn
            · subst hn
              rw [hj] at h2; obtain ⟨e1, -⟩ := h2; cases e1; exact absurd rfl e
            · exact ⟨n, hn, h2⟩
    · subst sp₁ m₁
      obtain ⟨T', new, hT', hTv', hmf', hfr', hstk', hS', hget, hnew, hall⟩ :=
        ih m m' T sp sp' hE hT hTv hS (fun w hw => hns w (List.mem_cons_of_mem _ hw)) h
      refine ⟨T', new, hT', hTv', hmf', hfr', hstk', hS', hget, ?_, ?_⟩
      · intro x hx
        obtain ⟨h1, n, hn, h2⟩ := hnew x hx
        exact ⟨h1, n, by simp at hn ⊢; exact Or.inr hn, h2⟩
      · rintro x hx ⟨n, hn, h2⟩
        simp only [List.map_cons, List.mem_cons] at hn
        rcases hn with hn | hn
        · subst hn
          exact absurd ⟨x, h2.1, h2.2.1, h2.2.2, hx⟩ hno
        · exact hall x hx ⟨n, hn, h2⟩

/-! ## The worklist -/

theorem stk_pop (m : Mem) (ws sp : Word) (h : sp ≠ 0) :
    stk m ws sp = stk m ws (sp - 1) ++ [(rdW (m.arr64 IW) (ws + sp - 1)).toNat] := by
  have h1 : sp.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  have h2 : (sp - 1).toNat = sp.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  unfold stk
  rw [h2]
  obtain ⟨q, hq⟩ : ∃ q, sp.toNat = q + 1 := ⟨sp.toNat - 1, by omega⟩
  have : ws + UInt64.ofNat q = ws + sp - 1 := by
    have e : sp = UInt64.ofNat q + 1 := by
      apply UInt64.toNat_inj.mp
      rw [hq, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_one]
      have := sp.toNat_lt; omega
    rw [e, ← UInt64.add_assoc, UInt64.add_sub_cancel]
  rw [hq, List.range_succ, List.map_append, Nat.add_sub_cancel]
  simp only [List.map_cons, List.map_nil, this]

theorem HoistTwin.ReachIn.mono {idx : Std.HashMap NIdx Nat} {i : Nat} {D : Nat → List NIdx}
    {N N' : Nat → Prop} {j k : Nat} (h : ReachIn idx i D N j k) (hN : ∀ x, N x → N' x) :
    ReachIn idx i D N' j k := by
  induction h with
  | base h => exact .base (hN _ h)
  | step _ hs hm ih => exact .step ih hs (hN _ hm)

/-- The closure's invariant at the targets `T`, the stack `S` (relative to the targets `T₀`
before it, the operation `i` and the start `j`). -/
structure CloseInv (ds : Array IDeclaration) (a : AState) (idx : Std.HashMap NIdx Nat) (i j : Nat)
    (T₀ T : Std.HashMap Nat Nat) (S : List Nat) : Prop where
  ext : ∀ x : Nat, T[x]? = T₀[x]? ∨ (T₀[x]? = none ∧ T[x]? = some i)
  stkNew : ∀ x ∈ S, T₀[x]? = none
  done : ∀ x : Nat, T₀[x]? = none → (T[x]?).isSome → x ∉ S →
    Good ds a x ∧ ∀ y, Succ idx i (depsOf ds a) x y → (T[y]?).isSome
  reach : ∀ x : Nat, T₀[x]? = none → (T[x]?).isSome →
    ReachIn idx i (depsOf ds a) (fun y => T₀[y]? = none ∧ (T[y]?).isSome) j x

/-- **The worklist keeps the invariant**, and ends with an empty stack. -/
theorem closeGo_ok {a : AState} {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {ord tg ws : Word} {c : Nat} {i j : Nat} (hi : i < c) (T₀ : Std.HashMap Nat Nat) :
    ∀ (n : Nat) (m m' : Mem) (T : Std.HashMap Nat Nat) (sp r : Word),
    HEnv m a ds idx ord tg ws c → TgtR m tg c T → TgtV T c → StkOK m ws sp c T →
    CloseInv ds a idx i j T₀ T (stk m ws sp) →
    hCloseGoW n m (UInt64.ofNat i) ord tg ws sp = some (r, m') →
    ∃ T', HEnv m' a ds idx ord tg ws c ∧ TgtR m' tg c T' ∧ TgtV T' c ∧ HFr tg ws c m m' ∧
      CloseInv ds a idx i j T₀ T' [] ∧ (∀ x : Nat, (T[x]?).isSome → T'[x]? = T[x]?) := by
  intro n
  induction n with
  | zero => intro m m' T sp r _ _ _ _ _ h; rw [hCloseGoW.eq_1] at h; cases h
  | succ n ih =>
  intro m m' T sp r hE hT hTv hS hI h
  by_cases h0 : sp = 0
  · rw [hCloseGoW.arm1 _ _ _ _ _ _ _ h0] at h
    cases h
    have hnil : stk m ws sp = [] := by subst h0; rfl
    rw [hnil] at hI
    exact ⟨T, hE, hT, hTv, HFr.refl _ _ _ _, hI, fun _ _ => rfl⟩
  rw [hCloseGoW.arm2 _ _ _ _ _ _ _ h0] at h
  have hc := hE.c60
  have r1 := hE.rg1; have r2 := hE.rg2; have r3 := hE.rg3; have r4 := hE.isz
  -- the top of the stack
  have hpop := stk_pop m ws sp h0
  generalize hkw : rdW (m.arr64 IW) (ws + sp - 1) = kw at hpop h
  have hkS : kw.toNat ∈ stk m ws sp := by rw [hpop]; simp
  have hkc : kw.toNat < c := (hS.2 _ hkS).1
  have hkw' : kw = UInt64.ofNat kw.toNat := by simp
  have hks : kw.toNat < ds.size := hE.size ▸ hkc
  obtain ⟨hr59, hD, hok⟩ := hE.ordR kw.toNat hks
  rw [← hkw'] at hr59 hD hok
  rcases hd : hDepsOfW n m kw (UInt64.ofNat i) (1 + 8 * rdW (m.arr64 IW) (ord + kw)) tg ws (sp - 1) with _ | ⟨sp₁, m₁⟩ <;> rw [hd] at h
  · simp [hCloseGoW.k_hoist_deps_of.eq_1] at h
  rw [hCloseGoW.k_hoist_deps_of.arm1] at h
  obtain ⟨ns, hrun, hns, hseen₁, mn, hnotes, hfr₁⟩ :=
    hoistDepsOf_ok n m m₁ a kw (UInt64.ofNat i) _ tg ws (sp - 1) sp₁ ds[kw.toNat] hE.arena hE.seen
      hr59 hD hok hd
  obtain ⟨hgood, hdeps⟩ := good_of_run hks hrun
  -- the stack below the top
  have hS₀ : StkOK m ws (sp - 1) c T := by
    rw [StkOK, hpop] at hS
    exact ⟨(List.nodup_append.mp hS.1).1, fun x hx => hS.2 x (List.mem_append_left _ hx)⟩
  rw [hkw'] at hnotes
  obtain ⟨T', new, hT', hTv', hmf', hfr', hstk', hS', hget, hnew, hall⟩ :=
    notes_ok hi hkc ns m mn T (sp - 1) sp₁ hE hT hTv hS₀ hns hnotes
  -- from `mn` to `m₁`: only the visited set differs
  have hIW : m₁.arr64 IW = mn.arr64 IW := hfr₁.1 IW (by decide) (by decide)
  have hfr : HFr tg ws c m m₁ := hfr'.trans
    ⟨hfr₁.mono (by simp) (by simp), fun x _ => by rw [hIW]⟩
  have hE₁ := hE.frame hfr hseen₁
  have hT₁ : TgtR m₁ tg c T' := ⟨fun x hx => by rw [hIW]; exact hT'.1 x hx, hT'.2⟩
  have hstk₁ : stk m₁ ws sp₁ = stk mn ws sp₁ := by simp only [stk, hIW]
  have hS₁ : StkOK m₁ ws sp₁ c T' := by rw [StkOK, hstk₁]; exact hS'
  have hT'x : ∀ x : Nat, (T[x]?).isSome → T'[x]? = T[x]? := by
    intro x hx
    rw [hget x]
    split
    · rename_i hxn; have := (hnew x hxn).1; rw [this] at hx; cases hx
    · rfl
  have hnew0 : ∀ x ∈ new, T₀[x]? = none := by
    intro x hx
    rcases hI.ext x with e | ⟨e, -⟩
    · rw [← e]; exact (hnew x hx).1
    · exact e
  have hSucc : ∀ y, Succ idx i (depsOf ds a) kw.toNat y → (T'[y]?).isSome := by
    intro y hy
    have hy' : Succ idx i (fun _ => ns.map decI) kw.toNat y := by
      obtain ⟨n', hn', h1⟩ := hy
      rw [hdeps] at hn'
      exact ⟨n', by simpa using hn', h1⟩
    cases hTy : T[y]? with
    | none => rw [hget y, if_pos (hall y hTy hy')]; rfl
    | some t => rw [hT'x y (by rw [hTy]; rfl), hTy]; rfl
  have hI₁ : CloseInv ds a idx i j T₀ T' (stk m₁ ws sp₁) := by
    rw [hstk₁, hstk']
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      rw [hget x]
      split
      · rename_i hx; exact Or.inr ⟨hnew0 x hx, rfl⟩
      · exact hI.ext x
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hI.stkNew x (by rw [hpop]; exact List.mem_append_left _ hx)
      · exact hnew0 x hx
    · intro x hx0 hxs hxS
      have hxn : x ∉ new := fun h => hxS (List.mem_append_right _ h)
      have hxT : T'[x]? = T[x]? := by rw [hget x, if_neg hxn]
      rw [hxT] at hxs
      by_cases e : x = kw.toNat
      · subst e; exact ⟨hgood, hSucc⟩
      · have hxS' : x ∉ stk m ws sp := by
          rw [hpop]; intro h
          rcases List.mem_append.mp h with h | h
          · exact hxS (List.mem_append_left _ h)
          · simp at h; exact e h
        obtain ⟨hg, hs⟩ := hI.done x hx0 hxs hxS'
        exact ⟨hg, fun y hy => by
          have := hs y hy; rw [hT'x y this]; exact this⟩
    · have hmono : ∀ y : Nat, (T₀[y]? = none ∧ (T[y]?).isSome) → (T₀[y]? = none ∧ (T'[y]?).isSome) :=
        fun y ⟨h1, h2⟩ => ⟨h1, by rw [hT'x y h2]; exact h2⟩
      intro x hx0 hxs
      by_cases hxn : x ∈ new
      · obtain ⟨-, hsx⟩ := hnew x hxn
        have hkT : (T[kw.toNat]?).isSome := (hS.2 _ hkS).2
        have hk0 : T₀[kw.toNat]? = none := hI.stkNew _ hkS
        refine .step ((hI.reach _ hk0 hkT).mono hmono) ?_ ⟨hx0, hxs⟩
        obtain ⟨n', hn', h1⟩ := hsx
        refine ⟨n', ?_, h1⟩
        rw [hdeps]; simpa using hn'
      · have hxT : T'[x]? = T[x]? := by rw [hget x, if_neg hxn]
        rw [hxT] at hxs
        exact (hI.reach x hx0 hxs).mono hmono
  obtain ⟨T'', hE'', hT'', hTv'', hfr'', hI'', hmono''⟩ :=
    ih m₁ m' T' sp₁ r hE₁ hT₁ hTv' hS₁ hI₁ h
  exact ⟨T'', hE'', hT'', hTv'', hfr.trans hfr'', hI'', fun x hx => by
    rw [hmono'' x (by rw [hT'x x hx]; exact hx), hT'x x hx]⟩

/-- Every moved record moves before itself. -/
def TLt (T : Std.HashMap Nat Nat) : Prop := ∀ (k t : Nat), T[k]? = some t → t < k

theorem reachIn_gt {idx : Std.HashMap NIdx Nat} {i : Nat} {D : Nat → List NIdx} {N : Nat → Prop}
    {j x : Nat} (h : HoistTwin.ReachIn idx i D N j x) (hij : i < j) : i < x := by
  induction h with
  | base _ => exact hij
  | step _ hs _ _ => obtain ⟨_, _, _, h2, _⟩ := hs; exact h2

theorem tgtR_congr {m : Mem} {tg : Word} {c : Nat} {T T' : Std.HashMap Nat Nat} (h : TgtR m tg c T)
    (e : ∀ k : Nat, T'[k]? = T[k]?) : TgtR m tg c T' :=
  ⟨fun k hk => by rw [e k]; exact h.1 k hk, fun k hk => by rw [e k]; exact h.2 k hk⟩

/-- **`hoist_closure` is the twin's `hoistClosure … ds.size T [j]`**: the twin succeeds, and L's
targets after are its map. -/
theorem closure_ok {a : AState} {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {ord tg ws : Word} {c : Nat} {i j : Nat} (hi : i < c) (hj : j < c) (n : Nat) (m m' : Mem)
    (T : Std.HashMap Nat Nat) (r : Word) (hE : HEnv m a ds idx ord tg ws c) (hT : TgtR m tg c T)
    (hTv : TgtV T c) (hTi : ∀ (k t : Nat), T[k]? = some t → t ≤ i) (hij : i < j) (hlt : TLt T)
    (h : hClosureW n m (UInt64.ofNat i) (UInt64.ofNat j) ord tg ws = some (r, m')) :
    ∃ T'', (hoistClosure ds idx i ds.size T [j]).run a = .ok (T'', a) ∧
      HEnv m' a ds idx ord tg ws c ∧ TgtR m' tg c T'' ∧ TgtV T'' c ∧ HFr tg ws c m m' ∧
      (∀ (k t : Nat), T''[k]? = some t → t ≤ i) ∧ (∀ k : Nat, (T[k]?).isSome → T''[k]? = T[k]?) ∧
      TLt T'' := by
  have hc := hE.c60
  have r1 := hE.rg1; have r2 := hE.rg2; have r3 := hE.rg3; have r4 := hE.isz
  cases n with
  | zero => rw [hClosureW.eq_1] at h; cases h
  | succ n =>
  have hrd : rdW (m.arr64 IW) (tg + UInt64.ofNat j) = tgW T[j]? := hT.1 j hj
  by_cases hm : rdW (m.arr64 IW) (tg + UInt64.ofNat j) ≠ 0
  · rw [hClosureW.arm1 _ _ _ _ _ _ _ hm] at h
    cases h
    have hTj : (T[j]?).isSome := by
      cases e : T[j]? with
      | none => rw [hrd, e] at hm; exact absurd rfl hm
      | some _ => rfl
    obtain ⟨T'', hrun, hget⟩ := closure_exact ds idx i a (depsOf ds a) (fun _ => False) T j hTi
      (fun _ h => h.elim) (fun _ h => h.elim) (Or.inr hTj) (fun _ h => h.elim)
    have e : ∀ k : Nat, T''[k]? = T[k]? := fun k => by rw [hget k]; simp
    exact ⟨T'', hrun, hE, tgtR_congr hT e, fun x t hx => hTv x t (by rw [← e x]; exact hx),
      HFr.refl _ _ _ _, fun x t hx => hTi x t (by rw [← e x]; exact hx), fun k _ => e k,
      fun x t hx => hlt x t (by rw [← e x]; exact hx)⟩
  rw [hClosureW.arm2 _ _ _ _ _ _ _ (Decidable.of_not_not hm)] at h
  have hTj : T[j]? = none := by
    cases e : T[j]? with
    | none => rfl
    | some t =>
      rw [hrd, e] at hm
      exact absurd (tgW_ne_zero t (by have := hTv j t e; omega)) hm
  -- the first push
  have e1 := set64_addr m tg j (UInt64.ofNat i + 1) (by omega)
  have e2 : ((m.set64 IW (tg + UInt64.ofNat j) (UInt64.ofNat i + 1)).set64 IW ws
      (UInt64.ofNat j)).arr64 IW = ((m.arr64 IW).set! (tg.toNat + j) (UInt64.ofNat i + 1)).set!
      ws.toNat (UInt64.ofNat j) := by
    rw [Mem.arr64_set64_same, e1]
  generalize hm₀ : (m.set64 IW (tg + UInt64.ofNat j) (UInt64.ofNat i + 1)).set64 IW ws
    (UInt64.ofNat j) = m₀ at e2 h
  have hmf₀ : MemFrame [IW] [] m m₀ := by
    rw [← hm₀]; exact (MemFrame.set64 m IW (by decide) _ _).trans (MemFrame.set64 _ IW (by decide) _ _)
  have hfr₀ : HFr tg ws c m m₀ := by
    refine ⟨hmf₀.mono (by simp) (by simp), fun x hx => ?_⟩
    rw [e2]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    rw [if_neg (by omega), if_neg (by omega)]
  have hE₀ := hE.frame hfr₀ (seen_frameIW hmf₀ hE.seen)
  have hT₀ : TgtR m₀ tg c (T.insert j i) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [rdW_addr _ _ _ (by omega), e2]
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      rw [if_neg (by omega)]
      by_cases hxj : j = x
      · subst hxj
        rw [if_pos rfl, if_pos (by omega)]
        simp [Std.HashMap.getElem?_insert, tgW, UInt64.ofNat_add]
      · rw [if_neg (by omega), Std.HashMap.getElem?_insert, if_neg (by simpa using hxj),
          ← hT.1 x hx, rdW_addr _ _ _ (by omega)]
    · rw [Std.HashMap.getElem?_insert, if_neg (by simp; omega)]; exact hT.2 x hx
  have hstk₀ : stk m₀ ws 1 = [j] := by
    simp only [stk, UInt64.toNat_one, List.range_one, List.map_cons, List.map_nil,
      List.cons.injEq, and_true]
    rw [rdW_addr _ _ _ (by omega), e2]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Nat.add_zero]
    rw [if_pos trivial, if_pos (by rw [Array.size_setIfInBounds]; omega)]
    simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
  have hTv₀ : TgtV (T.insert j i) c := by
    intro x t hx
    rw [Std.HashMap.getElem?_insert] at hx
    split at hx
    · cases hx; exact hi
    · exact hTv x t hx
  have hS₀ : StkOK m₀ ws 1 c (T.insert j i) := by
    rw [StkOK, hstk₀]
    exact ⟨by simp, by intro x hx; simp at hx; subst hx; exact ⟨hj, by simp [Std.HashMap.getElem?_insert]⟩⟩
  have hI₀ : CloseInv ds a idx i j T (T.insert j i) (stk m₀ ws 1) := by
    rw [hstk₀]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i e; simp at e; subst e; exact Or.inr ⟨hTj, rfl⟩
      · exact Or.inl rfl
    · intro x hx; simp at hx; subst hx; exact hTj
    · intro x hx0 hxs hxS
      rw [Std.HashMap.getElem?_insert] at hxs
      split at hxs
      · rename_i e; simp at e; subst e; exact absurd (List.mem_singleton_self _) hxS
      · rw [hx0] at hxs; cases hxs
    · intro x hx0 hxs
      rw [Std.HashMap.getElem?_insert] at hxs
      split at hxs
      · rename_i e; simp at e; subst e
        exact .base ⟨hTj, by simp [Std.HashMap.getElem?_insert]⟩
      · rw [hx0] at hxs; cases hxs
  obtain ⟨T', hE', hT', hTv', hfr', hI', hmono'⟩ :=
    closeGo_ok hi T n m₀ m' (T.insert j i) 1 r hE₀ hT₀ hTv₀ hS₀ hI₀ h
  -- the newly marked records form a closed set reachable from `j`
  let N : Nat → Prop := fun x => T[x]? = none ∧ (T'[x]?).isSome
  have hjT' : (T'[j]?).isSome := by
    rw [hmono' j (by simp [Std.HashMap.getElem?_insert])]; simp [Std.HashMap.getElem?_insert]
  obtain ⟨T'', hrun, hget⟩ := closure_exact ds idx i a (depsOf ds a) N T j hTi
    (fun k ⟨h0, hs⟩ => by
      obtain ⟨⟨hk, hr⟩, -⟩ := hI'.done k h0 hs (by simp)
      exact ⟨h0, hk, hr⟩)
    (fun k ⟨h0, hs⟩ y hy => by
      have := (hI'.done k h0 hs (by simp)).2 y hy
      cases e : T[y]? with
      | none => exact Or.inl ⟨e, this⟩
      | some _ => exact Or.inr rfl)
    (Or.inl ⟨hTj, hjT'⟩) (fun k ⟨h0, hs⟩ => hI'.reach k h0 hs)
  have e : ∀ k : Nat, T''[k]? = T'[k]? := by
    intro k
    rw [hget k]
    by_cases hk : N k
    · rw [if_pos hk]
      rcases hI'.ext k with e | ⟨-, e⟩
      · have := hk.2; rw [e, hk.1] at this; cases this
      · exact e.symm
    · rw [if_neg hk]
      rcases hI'.ext k with e | ⟨h0, e⟩
      · exact e.symm
      · exact absurd ⟨h0, by rw [e]; rfl⟩ hk
  refine ⟨T'', hrun, hE', tgtR_congr hT' e, fun x t hx => hTv' x t (by rw [← e x]; exact hx),
    hfr₀.trans hfr', fun x t hx => ?_, fun k hk => ?_, fun x t hx => ?_⟩
  · rw [e x] at hx
    rcases hI'.ext x with e' | ⟨-, e'⟩
    · rw [e'] at hx; exact hTi x t hx
    · rw [e'] at hx; cases hx; exact Nat.le_refl _
  · rw [e k]
    have h1 : ((T.insert j i)[k]?).isSome := by
      rw [Std.HashMap.getElem?_insert]; split
      · rfl
      · exact hk
    rw [hmono' k h1, Std.HashMap.getElem?_insert, if_neg]
    intro e'; simp at e'; subst e'; rw [hTj] at hk; cases hk
  · rw [e x] at hx
    rcases hI'.ext x with e' | ⟨h0, e'⟩
    · rw [e'] at hx; exact hlt x t hx
    · rw [e'] at hx; cases hx
      exact reachIn_gt (hI'.reach x h0 (by rw [e']; rfl)) hij

/-! ## The grounds of one operation -/

/-- The grounds `gs` are the name words `IW[o + q ‥]`. -/
def GrR (m : Mem) (o q : Word) (gs : List NIdx) : Prop :=
  ∀ p (h : p < gs.length), (rdW (m.arr64 IW) (o + UInt64.ofNat (q.toNat + p))).toNat < 2 ^ 32 ∧
    (decI (rdW (m.arr64 IW) (o + UInt64.ofNat (q.toNat + p))) : NIdx) = gs[p]

/-- **`hoist_deps` is the twin's `hoistDeps`** over the grounds `gs` (a slice above the stack). -/
theorem deps_ok {a : AState} {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {ord tg ws : Word} {c : Nat} {i : Nat} (hi : i < c) (o l : Word) :
    ∀ (gs : List NIdx) (n : Nat) (m m' : Mem) (T : Std.HashMap Nat Nat) (q r : Word),
    HEnv m a ds idx ord tg ws c → TgtR m tg c T → TgtV T c → (∀ (k t : Nat), T[k]? = some t → t ≤ i) →
    TLt T → GrR m o q gs → q.toNat + gs.length = l.toNat → (gs ≠ [] → ws.toNat + c ≤ o.toNat) →
    o.toNat + l.toNat < 2 ^ 64 →
    hDepsW n m (UInt64.ofNat i) o l q ord tg ws = some (r, m') →
    ∃ T'', (hoistTargetsGo.hoistDeps ds idx T i gs).run a = .ok (T'', a) ∧
      HEnv m' a ds idx ord tg ws c ∧ TgtR m' tg c T'' ∧ TgtV T'' c ∧
      (∀ (k t : Nat), T''[k]? = some t → t ≤ i) ∧ HFr tg ws c m m' ∧ TLt T'' := by
  intro gs
  induction gs with
  | nil =>
    intro n m m' T q r hE hT hTv hTi hlt _ hl _ _ h
    cases n with
    | zero => rw [hDepsW.eq_1] at h; cases h
    | succ n =>
    rw [hDepsW.arm1 _ _ _ _ _ _ _ _ _ (by rw [UInt64.le_iff_toNat_le]; simp at hl; omega)] at h
    cases h
    exact ⟨T, rfl, hE, hT, hTv, hTi, HFr.refl _ _ _ _, hlt⟩
  | cons g gs ih =>
    intro n m m' T q r hE hT hTv hTi hlt hG hl ho' hol h
    have ho := ho' (by simp)
    have hc := hE.c60
    cases n with
    | zero => rw [hDepsW.eq_1] at h; cases h
    | succ n =>
    have hq : q.toNat < l.toNat := by simp at hl; omega
    rw [hDepsW.arm2 _ _ _ _ _ _ _ _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at h
    obtain ⟨hw, hg⟩ := hG 0 (by simp)
    simp only [Nat.add_zero, UInt64.ofNat_toNat, List.getElem_cons_zero] at hw hg
    -- the next grounds, from `q + 1`
    have hq1 : (q + 1).toNat = q.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one]; have := l.toNat_lt; omega
    have hG1 : ∀ m₁ : Mem, HFr tg ws c m m₁ → GrR m₁ o (q + 1) gs := by
      intro m₁ hf p hp
      have hp' := hG (p + 1) (by simp; omega)
      have hadr : (o + UInt64.ofNat (q.toNat + (p + 1))).toNat = o.toNat + (q.toNat + (p + 1)) :=
        addW_toNat _ _ (by simp at hl; omega)
      have hrd : rdW (m₁.arr64 IW) (o + UInt64.ofNat ((q + 1).toNat + p)) =
          rdW (m.arr64 IW) (o + UInt64.ofNat (q.toNat + (p + 1))) := by
        rw [hq1, show q.toNat + 1 + p = q.toNat + (p + 1) by omega]
        simp only [rdW, hadr]
        rw [hf.2 _ (Or.inr (by omega))]
      rw [hrd]
      simpa using hp'
    have hl1 : (q + 1).toNat + gs.length = l.toNat := by rw [hq1]; simp at hl; omega
    rcases hx : hIxW m (rdW (m.arr64 IW) (o + q)) with _ | ⟨rw', m₁⟩ <;> rw [hx] at h
    · simp [hDepsW.k_hoist_ix.eq_1] at h
    obtain ⟨hm1, hr⟩ := hoistIx_ok m m₁ _ rw' idx hE.nix hw hx
    subst m₁
    rw [hg] at hr
    -- the twin's step
    simp only [hoistTargetsGo.hoistDeps]
    cases hgi : idx[g]? with
    | none =>
      rw [hgi] at hr; simp only [tgW] at hr; subst hr
      rw [hDepsW.k_hoist_ix.arm2 _ _ _ _ _ _ _ _ _ _ (by simp), hDepsW.j1.arm1] at h
      exact ih n m m' T (q + 1) r hE hT hTv hTi hlt (hG1 m (HFr.refl _ _ _ _)) hl1 (fun _ => ho) hol h
    | some jj =>
      rw [hgi] at hr; simp only [tgW] at hr; subst hr
      have hjc : jj < c := hE.nixlt g jj hgi
      have hci : (UInt64.ofNat i + 1 < UInt64.ofNat (jj + 1)) ↔ i < jj := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
        simp only [UInt64.toNat_one]; omega
      by_cases hij : i < jj
      · dsimp only
        rw [if_pos (by omega : jj > i)]
        have hne : UInt64.ofNat (jj + 1) ≠ 0 := by
          intro e; have := congrArg UInt64.toNat e
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this; simp at this
        rw [hDepsW.k_hoist_ix.arm1 _ _ _ _ _ _ _ _ _ _ ⟨hne, hci.mpr hij⟩] at h
        have hj1 : UInt64.ofNat (jj + 1) - 1 = UInt64.ofNat jj := by rw [UInt64.ofNat_add]; simp
        rw [hj1] at h
        rcases hcl : hClosureW n m (UInt64.ofNat i) (UInt64.ofNat jj) ord tg ws with _ | ⟨z, m₁⟩ <;> rw [hcl] at h
        · simp [hDepsW.k_hoist_closure.eq_1] at h
        rw [hDepsW.k_hoist_closure.arm1, hDepsW.j1.arm1] at h
        obtain ⟨T₁, hrun, hE₁, hT₁, hTv₁, hfr₁, hTi₁, -, hlt₁⟩ :=
          closure_ok hi hjc n m m₁ T z hE hT hTv hTi hij hlt hcl
        obtain ⟨T'', hrun', hE', hT', hTv', hTi', hfr', hlt'⟩ :=
          ih n m₁ m' T₁ (q + 1) r hE₁ hT₁ hTv₁ hTi₁ hlt₁ (hG1 m₁ hfr₁) hl1 (fun _ => ho) hol h
        refine ⟨T'', ?_, hE', hT', hTv', hTi', hfr₁.trans hfr', hlt'⟩
        rw [HoistTwin.run_bind, hrun]
        exact hrun'
      · dsimp only
        rw [if_neg (by omega)]
        rw [hDepsW.k_hoist_ix.arm2 _ _ _ _ _ _ _ _ _ _ (fun ⟨_, h2⟩ => hij (hci.mp h2)), hDepsW.j1.arm1] at h
        exact ih n m m' T (q + 1) r hE hT hTv hTi hlt (hG1 m (HFr.refl _ _ _ _)) hl1 (fun _ => ho) hol h

end L.Checker
