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
`2 ^ 60` records, every one walkable), the name index (positions of the stream), and three
disjoint slices of `IW`: `ord`, the targets `tg`, the stack `ws`, `c` words each. -/
structure HEnv (m : Mem) (a : AState) (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat)
    (ord tg ws : Word) (c : Nat) : Prop where
  arena : ArenaR m a
  seen : ∃ s, SeenR m s
  ordR : OrdR m ord ds
  size : ds.size = c
  c60 : c < 2 ^ 60
  walk : ∀ k (h : k < ds.size), WalkableDecl ds[k]
  nix : NixR m idx
  nixlt : ∀ (n : NIdx) (j : Nat), idx[n]? = some j → j < c
  rg1 : ord.toNat + c ≤ tg.toNat
  rg2 : tg.toNat + c ≤ ws.toNat
  rg3 : ws.toNat + c ≤ (m.arr64 IW).size
  isz : (m.arr64 IW).size < 2 ^ 64

theorem addW_toNat (x : Word) (k : Nat) (h : x.toNat + k < 2 ^ 64) :
    (x + UInt64.ofNat k).toNat = x.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  have : k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h]

theorem hnSch_wf : hnSch.WF := ⟨by decide, by decide⟩
theorem hsSch_wf : hsSch.WF := ⟨by decide, by decide⟩

/-- **The setting survives the hoist's passes.** -/
theorem HEnv.frame {m m' : Mem} {a : AState} {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {ord tg ws : Word} {c : Nat} (hE : HEnv m a ds idx ord tg ws c) (hf : HFr tg ws c m m')
    (hs : ∃ s, SeenR m' s) : HEnv m' a ds idx ord tg ws c := by
  have hD : ∀ b, b ∉ [IW, HSEEN] → b ≠ CTL → m'.arr64 b = m.arr64 b := hf.1.1
  have hDECL : m'.arr64 DECL = m.arr64 DECL := hD DECL (by decide) (by decide)
  have hDLP : m'.arr64 DLP = m.arr64 DLP := hD DLP (by decide) (by decide)
  have hsz : (m'.arr64 IW).size = (m.arr64 IW).size := hf.1.2.2.1 IW
  have hA : ∀ b ∈ [IW, HSEEN], 64 ≤ b := by
    intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide
  have hC : ∀ x ∈ ([73, 74] : List Word), 64 ≤ x.toNat := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  refine ⟨ArenaR.frame_ext [IW, HSEEN] [73, 74] hA hC m m' hf.1 a hE.arena, hs,
    ?_, hE.size, hE.c60, hE.walk, ?_, hE.nixlt, hE.rg1, hE.rg2, by rw [hsz]; exact hE.rg3,
    by rw [hsz]; exact hE.isz⟩
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
  simp only [tgW, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h] at this
  simp at this

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
      sp'.toNat = sp.toNat + 1 ∧ HFr tg ws c m m' ∧ TgtR m' tg c (T.insert j i) ∧
      stk m' ws sp' = stk m ws sp ++ [j]) ∨
    ((¬ ∃ j, idx[(decI w : NIdx)]? = some j ∧ i < j ∧ j ≠ k ∧ T[j]? = none) ∧ sp' = sp ∧ m' = m) := by
  have hc := hE.c60
  have r1 := hE.rg1; have r2 := hE.rg2; have r3 := hE.rg3; have r4 := hE.isz
  unfold hNoteW at h
  cases hx : hIxW m w with
  | none => rw [hx] at h; cases h
  | some rr =>
  obtain ⟨r, m₁⟩ := rr
  rw [hx] at h
  obtain ⟨hm1, hr⟩ := hoistIx_ok m m₁ w r idx hE.nix hw hx
  subst m₁
  cases ho : idx[(decI w : NIdx)]? with
  | none =>
    rw [ho] at hr
    simp only [tgW] at hr
    subst hr
    rw [hNoteW.k1.arm2 _ _ _ _ _ _ _ (by simp)] at h
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
      simp only [UInt64.toNat_one]
      rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 64)]
      omega
    have hck : (UInt64.ofNat (j + 1) ≠ UInt64.ofNat k + 1) ↔ j ≠ k := by
      have e0 : UInt64.ofNat (j + 1) = UInt64.ofNat j + 1 := by rw [UInt64.ofNat_add]; rfl
      rw [e0]
      constructor
      · intro h e; exact h (by rw [e])
      · intro h e
        apply h
        have e2 : UInt64.ofNat j = UInt64.ofNat k := by
          have := congrArg (· - 1) e
          simp only [UInt64.add_sub_cancel] at this
          exact this
        have := congrArg UInt64.toNat e2
        rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at this
        exact this
    have hcz : (rdW (m.arr64 IW) (tg + UInt64.ofNat (j + 1) - 1) = 0) ↔ T[j]? = none := by
      rw [htgj, hrd]
      cases hTj : T[j]? with
      | none => simp [tgW]
      | some t => simp only [reduceCtorEq, iff_false]; exact tgW_ne_zero t (by have := hTv j t hTj; omega)
    by_cases hcond : i < j ∧ j ≠ k ∧ T[j]? = none
    · obtain ⟨h1, h2, h3⟩ := hcond
      rw [hNoteW.k1.arm1 _ _ _ _ _ _ _ ⟨by
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
      refine ⟨j, rfl, h1, h2, h3, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [UInt64.toNat_add, UInt64.toNat_one]; omega
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
    · rw [hNoteW.k1.arm2 _ _ _ _ _ _ _ (by
          rintro ⟨-, a1, a2, a3⟩; exact hcond ⟨hci.mp a1, hck.mp a2, hcz.mp a3⟩)] at h
      cases h
      right
      refine ⟨?_, rfl, rfl⟩
      rintro ⟨j', hj', a1, a2, a3⟩
      simp only [ho, Option.some.injEq] at hj'; subst hj'
      exact hcond ⟨a1, a2, a3⟩

end L.Checker
