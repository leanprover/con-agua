import ConAgua.Arena.MemoLibRel
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Memo banks: generation-tagged keys (the mode-memo bank stack)

con-ron runs every eager comparison (`defeqE`) on emptied mode tables (`takeModeMemos`) and puts
the caller's tables back afterwards (`putModeMemos`), dropping what the eager run added; eager
comparisons nest without a structural bound in `.verified` mode (re-entry through `r.infer` in
`defeqLamsInner`, `etaCert`, `iotaCertsFullAux`). Instead of `D` banks selected by an eager-depth
word and cleared by epoch on entry, this library does the same with **one memo per table and a generation in the key**:

* `genKey K`: the key codec `K` with a generation `g < 2^32` in the high half of the second key
  word (`K`'s second word must be below `2^32`). The twin's table at generation `g` is the slice
  `Bank M g mp`: `mp[k]? = M[(k, g)]?` for the memo's whole map `M` (`MemoRV S (genKey K) VR m M`).
* `X_bank_enter()` (`MemoLib.lean`, `bankEnterG c`): a fresh generation `G + 1` (`CTL[c]` is the
  last one, `CTL[c + 1]` the current one), aborting at `2^32`; it returns the caller's generation,
  which the caller keeps in a local and restores with `X_bank_leave(s)`.
* `bank_enter`: after `X_bank_enter`, the new current bank is empty (`takeModeMemos`'s fresh
  tables) and the caller's bank still holds its table (what `putModeMemos` restores), with no
  memory written but two `CTL` words. `bank_set`/`bank_other`: an insert at the current
  generation is an insert in its bank and leaves every other bank alone.

So "clear the new bank by epoch" is free (a fresh generation has no entries), the depth bound `D`
becomes the generation bound `2^32` per memo clear, and the dead generations' entries stay until
the memo's `clear` (per declaration, `flushCaches`): a capacity cost, not a semantic one.
-/

open ConRon.Arena


namespace L.Arena

/-! ## The codec -/

theorem lo_hi (k : Word) : (k &&& (0xFFFFFFFF : Word)) ||| ((k >>> (32 : Word)) <<< (32 : Word)) = k := by
  apply UInt64.toNat_inj.mp
  have hk := k.toNat_lt
  have e1 : (k &&& (0xFFFFFFFF : Word)).toNat = k.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have e2 : ((k >>> (32 : Word)) <<< (32 : Word)).toNat = (k.toNat / 2 ^ 32) <<< 32 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  rw [UInt64.toNat_or, e1, e2, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
  rw [Nat.shiftLeft_eq]; omega

/-- The key codec `K` with a generation in the high half of the second word. -/
def genKey {κ : Type} (K : MemoKey κ) (_h2 : ∀ k1 k2, K.ok k1 k2 → k2.toNat < 2 ^ 32) :
    MemoKey (κ × Word) where
  dk k1 k2 := (K.dk k1 (k2 &&& 0xFFFFFFFF), k2 >>> 32)
  ek x := ((K.ek x.1).1, (K.ek x.1).2 ||| (x.2 <<< 32))
  ok k1 k2 := K.ok k1 (k2 &&& 0xFFFFFFFF)
  ek_dk k1 k2 h := by simp only [K.ek_dk _ _ h, lo_hi]
  ok_tomb k1 k2 h := K.ok_tomb _ _ h

/-! ## Banks of a generation-tagged map -/

section bank
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]

/-- The twin's table `mp` is the bank of generation `g` of the memo's map `M`. -/
def Bank (M : Std.HashMap (κ × Word) ν) (g : Word) (mp : Std.HashMap κ ν) : Prop :=
  ∀ k : κ, mp[k]? = M[(k, g)]?

/-- No entry of `M` has a generation above `G`. -/
def Fresh (M : Std.HashMap (κ × Word) ν) (G : Word) : Prop :=
  ∀ (k : κ) (g : Word) (v : ν), M[(k, g)]? = some v → g ≤ G

/-- An insert at the current generation is an insert in its bank. -/
theorem bank_set (M : Std.HashMap (κ × Word) ν) (g : Word) (mp : Std.HashMap κ ν)
    (h : Bank M g mp) (k : κ) (v : ν) : Bank (M.insert (k, g) v) g (mp.insert k v) := by
  intro k'
  rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert, h k']
  by_cases e : k = k' <;> simp [e]

/-- ... and leaves the banks of the other generations alone. -/
theorem bank_other (M : Std.HashMap (κ × Word) ν) (g g' : Word) (mp : Std.HashMap κ ν)
    (h : Bank M g' mp) (hne : g ≠ g') (k : κ) (v : ν) : Bank (M.insert (k, g) v) g' mp := by
  intro k'
  rw [Std.HashMap.getElem?_insert, h k']
  have : ¬ ((k, g) == (k', g')) = true := by simp [hne]
  simp [this]

theorem fresh_set (M : Std.HashMap (κ × Word) ν) (G g : Word) (hF : Fresh M G) (hg : g ≤ G)
    (k : κ) (v : ν) : Fresh (M.insert (k, g) v) G := by
  intro k' g' v' h
  rw [Std.HashMap.getElem?_insert] at h
  by_cases e : ((k, g) == (k', g')) = true
  · simp only [beq_iff_eq, Prod.mk.injEq] at e; rw [← e.2]; exact hg
  · simp only [e, Bool.false_eq_true, ↓reduceIte] at h; exact hF _ _ _ h

/-- **A fresh generation is an empty bank.** -/
theorem bank_fresh (M : Std.HashMap (κ × Word) ν) (G : Word) (hF : Fresh M G)
    (hG : (G + 1).toNat = G.toNat + 1) : Bank M (G + 1) ∅ := by
  intro k
  cases h : M[(k, G + 1)]? with
  | none => simp
  | some v => have := hF _ _ _ h; exfalso; rw [UInt64.le_iff_toNat_le] at this; omega

theorem fresh_mono (M : Std.HashMap (κ × Word) ν) (G : Word) (hF : Fresh M G)
    (hG : (G + 1).toNat = G.toNat + 1) : Fresh M (G + 1) := by
  intro k g v h; have := hF k g v h; rw [UInt64.le_iff_toNat_le] at this ⊢; omega

end bank

/-! ## The bank words and `X_bank_enter` -/

/-- The bank words of counter `c`: `CTL[c]` the last generation `G`, `CTL[c + 1]` the current. -/
def BankW (c : Word) (m : Mem) (G g : Word) : Prop :=
  rdW (m.arr64 CTL) c = G ∧ rdW (m.arr64 CTL) (c + 1) = g ∧ g ≤ G ∧ G.toNat < 2 ^ 32 ∧
    c.toNat + 1 < (m.arr64 CTL).size

theorem benterG_frame (c : Word) (m : Mem) : MemFrame [] [c, c + 1] m (benterG c m) :=
  ((MemFrame.setCtl m c _).mono (by simp) (by simp)).trans
    ((MemFrame.setCtl _ (c + 1) _).mono (by simp) (by simp))

section enter
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]

end enter

/-! ## `X_put` at the current generation -/

/-- The second key word at generation `g`. -/
def genW (k2 g : Word) : Word := k2 ||| (g <<< 32)

theorem genW_toNat (k2 g : Word) (hk : k2.toNat < 2 ^ 32) (hg : g.toNat < 2 ^ 32) :
    (genW k2 g).toNat = g.toNat * 2 ^ 32 + k2.toNat := by
  have e : (g <<< (32 : Word)).toNat = g.toNat <<< 32 := by
    rw [UInt64.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  unfold genW
  rw [UInt64.toNat_or, e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hk, Nat.shiftLeft_eq]

theorem genW_lo (k2 g : Word) (hk : k2.toNat < 2 ^ 32) : genW k2 g &&& 0xFFFFFFFF = k2 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  have e : (g <<< (32 : Word)).toNat = g.toNat % 2 ^ 32 * 2 ^ 32 := by
    rw [UInt64.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; have := g.toNat_lt; omega
  unfold genW
  rw [UInt64.toNat_or, e, Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hk,
    Nat.shiftLeft_eq]
  omega

theorem genW_hi (k2 g : Word) (hk : k2.toNat < 2 ^ 32) (hg : g.toNat < 2 ^ 32) :
    genW k2 g >>> 32 = g := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, genW_toNat k2 g hk hg]
  simp [Nat.shiftRight_eq_div_pow]
  omega

section put
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]

/-- **`find; put` at the current generation is an insert in the current bank**: the memo relation
over the whole map, the bank, freshness and the bank words all move along. -/
theorem bank_put (S : MemoSch) (hS : S.WF) (K : MemoKey κ)
    (h2 : ∀ k1 k2, K.ok k1 k2 → k2.toNat < 2 ^ 32) (VR : Mem → Word → ν → Prop)
    (hVS : VStable S VR) (c : Word) (hc : S.cs + 1 ≠ c ∧ S.cs + 1 ≠ c + 1)
    (m : Mem) (M : Std.HashMap (κ × Word) ν) (hR : MemoRV S (genKey K h2) VR m M)
    (G g : Word) (hB : BankW c m G g) (hF : Fresh M G) (mp : Std.HashMap κ ν) (hb : Bank M g mp)
    (k1 k2 w : Word) (hk : K.ok k1 k2) (x : ν) (hx : VR m w x) (m' : Mem)
    (hs : msetG S m k1 (genW k2 g) w = some m') :
    MemoRV S (genKey K h2) VR m' (M.insert (K.dk k1 k2, g) x) ∧
      Bank (M.insert (K.dk k1 k2, g) x) g (mp.insert (K.dk k1 k2) x) ∧
      Fresh (M.insert (K.dk k1 k2, g) x) G ∧ BankW c m' G g := by
  obtain ⟨hB1, hB2, hgG, hGl, hsz⟩ := hB
  have hk2 := h2 k1 k2 hk
  have hg : g.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at hgG; omega
  have hok : (genKey K h2).ok k1 (genW k2 g) := by
    show K.ok k1 (genW k2 g &&& 0xFFFFFFFF); rw [genW_lo k2 g hk2]; exact hk
  have hdk : (genKey K h2).dk k1 (genW k2 g) = (K.dk k1 k2, g) := by
    show (K.dk k1 (genW k2 g &&& 0xFFFFFFFF), genW k2 g >>> 32) = _
    rw [genW_lo k2 g hk2, genW_hi k2 g hk2 hg]
  have hR' := memoRV_set S hS (genKey K h2) VR hVS m M hR k1 (genW k2 g) w hok x hx m' hs
  rw [hdk] at hR'
  have hf := msetG_frame S hS m m' k1 (genW k2 g) w hs
  have hcw : ∀ y, y = c ∨ y = c + 1 → rdW (m'.arr64 CTL) y = rdW (m.arr64 CTL) y := by
    intro y hy; apply hf.2.1; simp only [List.mem_singleton]; rcases hy with rfl | rfl
    · exact Ne.symm hc.1
    · exact Ne.symm hc.2
  exact ⟨hR', bank_set M g mp hb _ x, fresh_set M G g hF hgG _ x,
    by rw [hcw c (.inl rfl)]; exact hB1, by rw [hcw (c + 1) (.inr rfl)]; exact hB2, hgG, hGl,
    by rw [hf.2.2.1]; exact hsz⟩

/-- **A probe at the current generation is a lookup in the current bank**: a hit is the bank's
entry, a miss its absence. -/
theorem bank_find (S : MemoSch) (K : MemoKey κ) (h2 : ∀ k1 k2, K.ok k1 k2 → k2.toNat < 2 ^ 32)
    (VR : Mem → Word → ν → Prop) (m : Mem) (M : Std.HashMap (κ × Word) ν)
    (hR : MemoRV S (genKey K h2) VR m M) (g : Word) (hg : g.toNat < 2 ^ 32)
    (mp : Std.HashMap κ ν) (hb : Bank M g mp) (k1 k2 : Word) (hk : K.ok k1 k2)
    (hr : mfindG S m k1 (genW k2 g) ≠ []) :
    ((mfindG S m k1 (genW k2 g)).headD 0 ≠ 0 →
      MemoV VR m (mvG S m ((mfindG S m k1 (genW k2 g)).tail.headD 0)) mp[K.dk k1 k2]?) ∧
    ((mfindG S m k1 (genW k2 g)).headD 0 = 0 → mp[K.dk k1 k2]? = none) := by
  have hk2 := h2 k1 k2 hk
  have hok : (genKey K h2).ok k1 (genW k2 g) := by
    show K.ok k1 (genW k2 g &&& 0xFFFFFFFF); rw [genW_lo k2 g hk2]; exact hk
  have hdk : (genKey K h2).dk k1 (genW k2 g) = (K.dk k1 k2, g) := by
    show (K.dk k1 (genW k2 g &&& 0xFFFFFFFF), genW k2 g >>> 32) = _
    rw [genW_lo k2 g hk2, genW_hi k2 g hk2 hg]
  rw [hb (K.dk k1 k2), ← hdk]
  exact ⟨fun hh => memoRV_hit S _ VR m M hR k1 _ hr hh hok,
    fun hh => memoRV_miss S _ VR m M hR k1 _ hok hr hh⟩

end put

/-! ## A test instance and a run

A mode memo of the shape of `whnfCoreC` (`EIdx → EIdx`, one-word keys): schema at array 2 and
`CTL[2]`, the bank counter at `CTL[4]` (current generation `CTL[5]`). The run below stores `70`
under key `7` at generation `0`, enters a bank (generation `1`), misses `7` there and stores `71`,
leaves, and finds `70` again: `putModeMemos` restored the caller's table. -/

abbrev tbSch : MemoSch := ⟨2, 2⟩

/-- The test program. -/
def tbProg : Prog :=
  [("t_find", memoFindG tbSch), ("t_put", memoPutG tbSch), ("t_enter", bankEnterG 4),
   ("t_leave", bankLeaveG 4)]

/-- `find` then `put` of `v` under `(k, g)`; the memory after. -/
def tbSet (m : Mem) (k g v : Word) : Option Mem :=
  match run tbProg 100 "t_find" [k, genW 0 g] m with
  | .ok (r, m) => match run tbProg 100 "t_put" [k, genW 0 g, v, r.headD 0, r.tail.headD 0] m with
    | .ok (_, m) => some m
    | .error _ => none
  | .error _ => none

/-- `find` of `(k, g)`: the value, `none` on a miss. -/
def tbGet (m : Mem) (k g : Word) : Option Word :=
  match run tbProg 100 "t_find" [k, genW 0 g] m with
  | .ok (r, _) => if r.headD 0 ≠ 0 then some (rdW (m.arr64 2) (r.tail.headD 0 * 4 + 3)) else none
  | .error _ => none

#guard
  let m : Mem := { words := #[#[], Array.replicate 8 0, Array.replicate 64 0] }
  match tbSet m 7 0 70 with
  | some m1 => match run tbProg 100 "t_enter" [] m1 with
    | .ok (s, m2) => tbGet m2 7 1 == none && s == [0] &&
      (match tbSet m2 7 1 71 with
       | some m3 => tbGet m3 7 1 == some 71 &&
         (match run tbProg 100 "t_leave" [0] m3 with
          | .ok (_, m4) => tbGet m4 7 0 == some 70 && tbGet m4 7 1 == some 71
          | .error _ => false)
       | none => false)
    | .error _ => false
  | none => false

end L.Arena
