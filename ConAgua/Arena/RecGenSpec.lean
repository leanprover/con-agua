import ConAgua.Arena.RecGen
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndInstallSpec

/-!
# Refinements of `RecGen` (lane `induct`, round 2)

`ClassSlot.isMinor` (a plain record-tag read, as `IndPartsSpec`'s `blockShapeK_refines`) and
`classMinorSlot` (now a small recursive helper, `classMinorSlotGo`, instead of its round-1 `while`
loop: its accumulator words are explicit parameters, so its refinement is plain induction on the
fuel, as `Walk.lean`'s `bbGo`/`bbNode` — not the subtler "the loop continues with the SAME
parameters, just shifted" argument `sl_contains`/`sl_nodup` need for their `while` loops, whose
varying state happens to be their own parameters).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ClassSlot.isMinor` -/

/-- A decoded `ClassSlot`'s tag word is `1` exactly when it is `.isMinor`. -/
theorem decCS_tag {m : Mem} {p : Nat} {cs : ClassSlot} (h : decCS m p = some cs) :
    iwN m p = some (if cs.isMinor then 1 else 0) := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨q, -, h⟩ := h
    obtain ⟨k, -, rfl⟩ := h
    simp [ht, ClassSlot.isMinor]
  | 1, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, -, h⟩ := h
    obtain ⟨b, -, h⟩ := h
    obtain ⟨c2, -, rfl⟩ := h
    simp [ht, ClassSlot.isMinor]
  | (k + 2), h => simp at h

/-- **`class_slot_is_minor` is `ClassSlot.isMinor`.** -/
@[refines ConRon.Arena.ClassSlot.isMinor]
theorem classSlotIsMinor_refines (p : Prog) (hp : p.lookup "class_slot_is_minor" = some classSlotIsMinor)
    (n : Nat) (s₀ : St) (q : Word) (cs : ClassSlot) (hq : decCS s₀.mem q.toNat = some cs)
    (hq1 : q.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_slot_is_minor" [q]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0 != 0) = cs.isMinor; ⊤⦄ := by
  have key := iwN_rdW (decCS_tag hq) hq1
  rw [invoke_eq _ hp]
  simp only [callFn, classSlotIsMinor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [UInt64.ofNat_toNat]

/-! ## `classMinorSlotGo`

The exec spec: the recursive helper's result is its word model, at every fuel — as `Walk.lean`'s
`bbGo`, by induction on the fuel, the self-call handled by the induction hypothesis (no "the loop
continues with the same parameters, shifted" argument is needed, since every quantity the twin's
scan carries — the remaining count, the current index, the running hit count and the last hit's
fields — is an explicit parameter of `class_minor_slot_go` here, not a `while`-loop local). -/

/-- Slot `p`'s hit test with the L code's guards: `none` when a read it makes is out of bounds,
`some false` on a miss, `some true` on a hit (`.minor`, class `c`, ctor `cc`). -/
def classMinorSlotHit (a : Array Word) (p c cc : Word) : Option Bool :=
  if p.toNat < a.size then
    if rdW a p = 1 then
      if (p + 1).toNat < a.size then
        if rdW a (p + 1) = c then
          if (p + 2).toNat < a.size then
            if rdW a (p + 2) = cc then
              if (p + 3).toNat < a.size ∧ (p + 4).toNat < a.size then some true else none
            else some false
          else none
        else some false
      else none
    else some false
  else none

section hitlemmas
variable (a : Array Word) (p c cc : Word)
theorem hit_oob0 (h : ¬ p.toNat < a.size) : classMinorSlotHit a p c cc = none := by
  simp only [classMinorSlotHit, ↓reduceIte, h]
theorem hit_t (h : p.toNat < a.size) (h1 : rdW a p ≠ 1) : classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1]
theorem hit_oob1 (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : ¬ (p + 1).toNat < a.size) :
    classMinorSlotHit a p c cc = none := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2]
theorem hit_c (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) ≠ c) : classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3]
theorem hit_oob2 (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : ¬ (p + 2).toNat < a.size) :
    classMinorSlotHit a p c cc = none := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4]
theorem hit_cc (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : (p + 2).toNat < a.size) (h5 : rdW a (p + 2) ≠ cc) :
    classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4, h5]
theorem hit_oob3 (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : (p + 2).toNat < a.size) (h5 : rdW a (p + 2) = cc)
    (h6 : ¬ ((p + 3).toNat < a.size ∧ (p + 4).toNat < a.size)) :
    classMinorSlotHit a p c cc = none := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4, h5, h6]
theorem hit_hit (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : (p + 2).toNat < a.size) (h5 : rdW a (p + 2) = cc)
    (h6 : (p + 3).toNat < a.size) (h7 : (p + 4).toNat < a.size) :
    classMinorSlotHit a p c cc = some true := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4, h5, h6, h7, and_self]
end hitlemmas

grind_pattern [ind_grind] hit_oob0 => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_t => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_oob1 => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_c => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_oob2 => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_cc => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_oob3 => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_hit => classMinorSlotHit a p c cc

/-- **The word model of `class_minor_slot_go`.** `off` is the slots' fixed base; `j` the current
index (so the slot under test is at `off + j`). -/
def classMinorSlotGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Word × Word × Word)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, off, rem, j, c, cc, cnt, rS, rOff, rLen =>
    if rem = 0 then some (cnt, rS, rOff, rLen)
    else if (off + j).toNat < (m.arr64 IW).size then
      match classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc with
      | none => none
      | some false => classMinorSlotGoW n m off (rem - 1) (j + 1) c cc cnt rS rOff rLen
      | some true => classMinorSlotGoW n m off (rem - 1) (j + 1) c cc (cnt + 1) j
          (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 3))
          (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 4))
    else none

section arms
variable (n : Nat) (m : Mem) (off rem j c cc cnt rS rOff rLen : Word)

theorem classMinorSlotGoW_base (hrem : rem = 0) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = some (cnt, rS, rOff, rLen) := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem]

theorem classMinorSlotGoW_oob (hrem : rem ≠ 0) (hp : ¬ (off + j).toNat < (m.arr64 IW).size) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = none := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp]

theorem classMinorSlotGoW_oob2 (hrem : rem ≠ 0) (hp : (off + j).toNat < (m.arr64 IW).size)
    (hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = none) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = none := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp, hh]

theorem classMinorSlotGoW_miss (hrem : rem ≠ 0) (hp : (off + j).toNat < (m.arr64 IW).size)
    (hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = some false) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen =
      classMinorSlotGoW n m off (rem - 1) (j + 1) c cc cnt rS rOff rLen := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp, hh]

theorem classMinorSlotGoW_hit (hrem : rem ≠ 0) (hp : (off + j).toNat < (m.arr64 IW).size)
    (hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = some true) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen =
      classMinorSlotGoW n m off (rem - 1) (j + 1) c cc (cnt + 1) j
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 3))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 4)) := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp, hh]

end arms

grind_pattern [ind_grind] classMinorSlotGoW_base => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_oob => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_oob2 => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_miss => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_hit => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen

theorem classMinorSlotGo_spec (p : Prog) (hp : p.lookup "class_minor_slot_go" = some classMinorSlotGo)
    (n : Nat) : ∀ (s₀ : St) (off rem j c cc cnt rS rOff rLen : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_minor_slot_go"
      [off, rem, j, c, cc, cnt, rS, rOff, rLen]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      ∃ x y z w, classMinorSlotGoW n s₀.mem off rem j c cc cnt rS rOff rLen = some (x, y, z, w) ∧
        r = [x, y, z, w]; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off rem j c cc cnt rS rOff rLen; rw [invoke_eq _ hp]; simp only [callFn, classMinorSlotGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off rem j c cc cnt rS rOff rLen
    rw [invoke_eq _ hp]
    simp only [callFn, classMinorSlotGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)


theorem iwN_lt {m : Mem} {i v : Nat} (h : iwN m i = some v) : i < (m.arr64 IW).size := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem iwN_off {m : Mem} {p k v : Nat} (h : iwN m (p + k) = some v) (hb : p + k < 2 ^ 64) :
    (UInt64.ofNat p + UInt64.ofNat k).toNat < (m.arr64 IW).size ∧
    rdW (m.arr64 IW) (UInt64.ofNat p + UInt64.ofNat k) = UInt64.ofNat v := by
  have e : UInt64.ofNat p + UInt64.ofNat k = UInt64.ofNat (p + k) := by simp [UInt64.ofNat_add]
  have hl := iwN_lt h
  rw [e]
  refine ⟨?_, (iwN_rdW h hb).1⟩
  simp; omega

theorem iwH_off {m : Mem} {k' : IdxKind} {p k : Nat} {x : Idx k'} (h : iwH m (p + k) = some x) (hb : p + k < 2 ^ 64) :
    (UInt64.ofNat p + UInt64.ofNat k).toNat < (m.arr64 IW).size ∧
    ∃ w, rdW (m.arr64 IW) (UInt64.ofNat p + UInt64.ofNat k) = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x := by
  have e : UInt64.ofNat p + UInt64.ofNat k = UInt64.ofNat (p + k) := by simp [UInt64.ofNat_add]
  have hl : p + k < (m.arr64 IW).size := by
    simp only [iwH, hd?, iwA] at h
    cases hw : (m.arr64 IW)[p + k]? with
    | none => simp [hw] at h
    | some w => exact (Array.getElem?_eq_some_iff.mp hw).1
  rw [e]
  refine ⟨by simp; omega, iwH_rdW h hb⟩


theorem decCS_motive {m : Mem} {p : Nat} {key : ClassKey} (h : decCS m p = some (.motive key)) :
    iwN m p = some 0 := by
  have := decCS_tag h
  simpa [ClassSlot.isMinor] using this

theorem decCS_minor {m : Mem} {p c' : Nat} {C' : NIdx} {ihs : List (Nat × Nat)}
    (h : decCS m p = some (.minor c' C' ihs)) :
    iwN m p = some 1 ∧ iwN m (p + 1) = some c' ∧ iwH m (p + 2) = some C' ∧
    ∃ o l, iwN m (p + 3) = some o ∧ iwN m (p + 4) = some l ∧ decPL m (decNN m) o l = some ihs := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, h => simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h; obtain ⟨_, _, h⟩ := h; obtain ⟨_, _, h⟩ := h; cases h
  | 1, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨b, hb, h⟩ := h
    obtain ⟨c2, hc2, h⟩ := h
    cases h
    obtain ⟨o, l, ho, hl, hg⟩ := decAt_some hc2
    exact ⟨ht, ha, hb, o, l, ho, hl, hg⟩
  | (k + 2), h => simp at h

theorem hit_of_decCS_miss {m : Mem} {p : Nat} {cs : ClassSlot} (c cc : Word) (hcc : cc.toNat < 2 ^ 32)
    (hp : decCS m p = some cs) (hb : p + 5 < 2 ^ 64)
    (hnot : ∀ ihs, cs ≠ .minor c.toNat (decI cc) ihs) :
    classMinorSlotHit (m.arr64 IW) (UInt64.ofNat p) c cc = some false := by
  have hp0 : p + 0 < 2 ^ 64 := by omega
  cases cs with
  | motive key =>
    have h0 := decCS_motive hp
    have h0' := iwN_off (k := 0) (by simpa using h0) hp0
    simp only [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at h0'
    apply hit_t _ _ c cc h0'.1
    rw [h0'.2]; decide
  | minor c' C' ihs =>
    obtain ⟨h0, h1, h2, o, l, h3, h4, hd⟩ := decCS_minor hp
    have h0' := iwN_off (k := 0) (by simpa using h0) hp0
    simp only [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at h0'
    have h1' := iwN_off (k := 1) h1 (by omega)
    simp only [show UInt64.ofNat 1 = 1 from rfl] at h1'
    obtain ⟨h2a, w, h2b, h2c, h2d⟩ := iwH_off (k := 2) h2 (by omega)
    simp only [show UInt64.ofNat 2 = 2 from rfl] at h2a h2b
    have h0v : rdW (m.arr64 IW) (UInt64.ofNat p) = 1 := by rw [h0'.2]; rfl
    by_cases hc : c' = c.toNat
    · have hC : C' ≠ decI cc := fun e => hnot ihs (by rw [hc, e])
      refine hit_cc _ _ c cc h0'.1 h0v h1'.1 ?_ h2a ?_
      · rw [h1'.2]; subst hc; simp
      · rw [h2b]; intro e; apply hC; rw [← h2d, e]
    · refine hit_c _ _ c cc h0'.1 h0v h1'.1 ?_
      rw [h1'.2]; intro e; apply hc
      have := congrArg UInt64.toNat e
      rw [UInt64.toNat_ofNat_of_lt' (by have := (iwN_rdW h1 (by omega)).2; exact this)] at this
      exact this

theorem hit_of_decCS_hit {m : Mem} {p : Nat} {ihs : List (Nat × Nat)} (c cc : Word)
    (hp : decCS m p = some (.minor c.toNat (decI cc) ihs)) (hcc : cc.toNat < 2 ^ 32)
    (hb : p + 5 < 2 ^ 64) :
    classMinorSlotHit (m.arr64 IW) (UInt64.ofNat p) c cc = some true ∧
    ∃ o l : Nat, rdW (m.arr64 IW) (UInt64.ofNat p + 3) = UInt64.ofNat o ∧
      rdW (m.arr64 IW) (UInt64.ofNat p + 4) = UInt64.ofNat l ∧ decPL m (decNN m) o l = some ihs ∧
      o < 2 ^ 64 ∧ l < 2 ^ 64 := by
  obtain ⟨h0, h1, h2, o, l, h3, h4, hd⟩ := decCS_minor hp
  have h0' := iwN_off (k := 0) (by simpa using h0) (by omega)
  simp only [show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at h0'
  have h1' := iwN_off (k := 1) h1 (by omega)
  simp only [show UInt64.ofNat 1 = 1 from rfl] at h1'
  obtain ⟨h2a, w, h2b, h2c, h2d⟩ := iwH_off (k := 2) h2 (by omega)
  simp only [show UInt64.ofNat 2 = 2 from rfl] at h2a h2b
  have h3' := iwN_off (k := 3) h3 (by omega)
  simp only [show UInt64.ofNat 3 = 3 from rfl] at h3'
  have h4' := iwN_off (k := 4) h4 (by omega)
  simp only [show UInt64.ofNat 4 = 4 from rfl] at h4'
  have h0v : rdW (m.arr64 IW) (UInt64.ofNat p) = 1 := by rw [h0'.2]; rfl
  have hc64 : c.toNat < 2 ^ 64 := c.toNat_lt
  refine ⟨hit_hit _ _ c cc h0'.1 h0v h1'.1 ?_ h2a ?_ h3'.1 h4'.1, o, l, h3'.2, h4'.2, hd, (iwN_rdW h3 (by omega)).2, (iwN_rdW h4 (by omega)).2⟩
  · rw [h1'.2]; simp
  · rw [h2b]
    have := congrArg (fun x : Idx IdxKind.name => x.word.toUInt64) h2d
    simpa only [decI_word_self w h2c, decI_word_self cc hcc] using this

theorem decPL_succ {α : Type} (m : Mem) (f : Nat → Option α) (o l : Nat) :
    decPL m f o (l + 1) = (do
      let x ← (do let p ← iwN m o; f p)
      let ys ← decPL m f (o + 1) l
      pure (x :: ys)) := by
  simp only [decPL, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range l))
  funext j
  simp only [Function.comp]
  congr 2
  omega

theorem decPL_cons {α : Type} {m : Mem} {f : Nat → Option α} {o l : Nat} {xs : List α}
    (h : decPL m f o (l + 1) = some xs) :
    ∃ p x ys, xs = x :: ys ∧ iwN m o = some p ∧ f p = some x ∧ decPL m f (o + 1) l = some ys := by
  rw [decPL_succ] at h
  cases hp : iwN m o with
  | none => simp [hp] at h
  | some p =>
    cases hf : f p with
    | none => simp [hp, hf] at h
    | some x =>
      cases hr : decPL m f (o + 1) l with
      | none => simp [hp, hf, hr] at h
      | some ys =>
        simp [hp, hf, hr] at h
        exact ⟨p, x, ys, h.symm, rfl, hf, rfl⟩

/-- The twin's hits of `classMinorSlot`, from index `j`. -/
def hitsFrom (c : Nat) (C : NIdx) : Nat → List ClassSlot → List (Nat × List (Nat × Nat))
  | _, [] => []
  | j, .motive _ :: sls => hitsFrom c C (j + 1) sls
  | j, .minor c' C' ihs :: sls =>
    if c' == c && C' == C then (j, ihs) :: hitsFrom c C (j + 1) sls else hitsFrom c C (j + 1) sls

/-- What the scan's result words say about the hits. -/
def GoRes (m : Mem) (hs : List (Nat × List (Nat × Nat))) (cnt rS rOff rLen x y z w : Word) : Prop :=
  x.toNat = cnt.toNat + hs.length ∧ (hs = [] → y = rS ∧ z = rOff ∧ w = rLen) ∧
  (∀ s ihs, hs.getLast? = some (s, ihs) →
    y = UInt64.ofNat s ∧ decPL m (decNN m) z.toNat w.toNat = some ihs)

theorem decCS_ptr_lt {m : Mem} {p : Nat} {cs : ClassSlot} (h : decCS m p = some cs) :
    p < (m.arr64 IW).size := by
  have := decCS_tag h
  exact iwN_lt this

theorem classMinorSlotGoW_ok (n : Nat) : ∀ (m : Mem) (off rem j c cc cnt rS rOff rLen x y z w : Word)
    (sls : List ClassSlot),
    classMinorSlotGoW n m off rem j c cc cnt rS rOff rLen = some (x, y, z, w) →
    decPL m (decCS m) (off + j).toNat rem.toNat = some sls → cc.toNat < 2 ^ 32 →
    (m.arr64 IW).size + 5 < 2 ^ 64 → (off + j).toNat + rem.toNat < 2 ^ 64 →
    j.toNat + rem.toNat < 2 ^ 64 → cnt.toNat + rem.toNat < 2 ^ 64 →
    GoRes m (hitsFrom c.toNat (decI cc) j.toNat sls) cnt rS rOff rLen x y z w := by
  induction n with
  | zero => intro m off rem j c cc cnt rS rOff rLen x y z w sls h; simp [classMinorSlotGoW] at h
  | succ n ih =>
    intro m off rem j c cc cnt rS rOff rLen x y z w sls h hdec hcc hsz hoff hjr hcnt
    by_cases hrem : rem = 0
    · rw [classMinorSlotGoW_base n m off rem j c cc cnt rS rOff rLen hrem] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have hr0 : rem.toNat = 0 := by rw [hrem]; rfl
      rw [hr0] at hdec
      simp [decPL] at hdec
      subst hdec
      simp [GoRes, hitsFrom]
    · have hrpos : 1 ≤ rem.toNat := by
        rcases Nat.eq_zero_or_pos rem.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hrem
        · omega
      obtain ⟨r1, hr1⟩ : ∃ r1, rem.toNat = r1 + 1 := ⟨rem.toNat - 1, by omega⟩
      rw [hr1] at hdec
      obtain ⟨pn, sl, sls', rfl, hpn, hsl, hdec'⟩ := decPL_cons hdec
      have hsz1 := iwN_lt hpn
      have hoj : UInt64.ofNat (off + j).toNat = off + j := UInt64.ofNat_toNat
      have hrdj := iwN_rdW hpn (by omega)
      rw [hoj] at hrdj
      have hlt : (off + j).toNat < (m.arr64 IW).size := hsz1
      have hpn64 : pn < 2 ^ 64 := hrdj.2
      have hpsz := decCS_ptr_lt hsl
      have hrem1 : (rem - 1).toNat = r1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hrpos))]; simp; omega
      have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hoff1 : (off + (j + 1)).toNat = (off + j).toNat + 1 := by
        have e : off + (j + 1) = (off + j) + 1 := by rw [UInt64.add_assoc]
        rw [e, UInt64.toNat_add]
        show ((off + j).toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hdec1 : decPL m (decCS m) (off + (j + 1)).toNat (rem - 1).toNat = some sls' := by
        rw [hoff1, hrem1]; exact hdec'
      have miss : (∀ ihs, sl ≠ .minor c.toNat (decI cc) ihs) →
          hitsFrom c.toNat (decI cc) j.toNat (sl :: sls') =
            hitsFrom c.toNat (decI cc) (j.toNat + 1) sls' →
          GoRes m (hitsFrom c.toNat (decI cc) j.toNat (sl :: sls')) cnt rS rOff rLen x y z w := by
        intro hnh hs
        have hmiss : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = some false := by
          rw [hrdj.1]
          exact hit_of_decCS_miss c cc hcc hsl (by omega) hnh
        rw [classMinorSlotGoW_miss n m off rem j c cc cnt rS rOff rLen hrem hlt hmiss] at h
        have := ih m off (rem - 1) (j + 1) c cc cnt rS rOff rLen x y z w sls' h hdec1 hcc hsz
          (by rw [hoff1, hrem1]; omega) (by rw [hj1, hrem1]; omega) (by rw [hrem1]; omega)
        rw [hs, ← hj1]
        exact this
      cases sl with
      | motive k =>
        exact miss (fun ihs e => by cases e) (by simp [hitsFrom])
      | minor c' C' ihs =>
        by_cases hh : c' = c.toNat ∧ C' = decI cc
        · obtain ⟨rfl, rfl⟩ := hh
          obtain ⟨hH, o, l, h3, h4, hd, ho, hl⟩ := hit_of_decCS_hit c cc hsl hcc (by omega)
          have hHit : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = some true := by
            rw [hrdj.1]; exact hH
          rw [classMinorSlotGoW_hit n m off rem j c cc cnt rS rOff rLen hrem hlt hHit, hrdj.1, h3, h4] at h
          have hcnt1 : (cnt + 1).toNat = cnt.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
          have := ih m off (rem - 1) (j + 1) c cc (cnt + 1) j (UInt64.ofNat o) (UInt64.ofNat l) x y z w sls' h hdec1 hcc hsz
            (by rw [hoff1, hrem1]; omega) (by rw [hj1, hrem1]; omega) (by rw [hcnt1, hrem1]; omega)
          obtain ⟨g1, g2, g3⟩ := this
          have hs : hitsFrom c.toNat (decI cc) j.toNat (.minor c.toNat (decI cc) ihs :: sls') =
              (j.toNat, ihs) :: hitsFrom c.toNat (decI cc) (j.toNat + 1) sls' := by
            simp [hitsFrom]
          rw [hs, ← hj1]
          refine ⟨by rw [g1, hcnt1]; simp; omega, fun hne => by simp at hne, ?_⟩
          intro s ihs' hlast
          by_cases hnil : hitsFrom c.toNat (decI cc) (j + 1).toNat sls' = []
          · rw [hnil] at hlast
            simp at hlast
            obtain ⟨rfl, rfl⟩ := hlast
            obtain ⟨e1, e2, e3⟩ := g2 hnil
            refine ⟨?_, ?_⟩
            · rw [e1]; simp
            · rw [e2, e3, UInt64.toNat_ofNat_of_lt' ho, UInt64.toNat_ofNat_of_lt' hl]; exact hd
          · have hl2 : (List.getLast? ((j.toNat, ihs) :: hitsFrom c.toNat (decI cc) (j + 1).toNat sls')) =
                (hitsFrom c.toNat (decI cc) (j + 1).toNat sls').getLast? := by
              cases hh : hitsFrom c.toNat (decI cc) (j + 1).toNat sls' with
              | nil => exact absurd hh hnil
              | cons a t => simp [List.getLast?_cons_cons]
            rw [hl2] at hlast
            exact g3 s ihs' hlast
        · refine miss (fun ihs' e => ?_) ?_
          · injection e with e1 e2 _
            exact hh ⟨e1, e2⟩
          · simp only [hitsFrom]
            have : ¬ (c' == c.toNat && C' == decI cc) = true := by
              intro e; simp at e; exact hh e
            simp [this]



/-! ## `class_minor_slot` -/

/-- The model of `class_minor_slot`. -/
def classMinorSlotW (n : Nat) (m : Mem) (rd c cc : Word) : Option (List Word) :=
  if rd.toNat < (m.arr64 IW).size ∧ (rd + 1).toNat < (m.arr64 IW).size then
    match classMinorSlotGoW n m (rdW (m.arr64 IW) rd) (rdW (m.arr64 IW) (rd + 1)) 0 c cc 0 0 0 0 with
    | none => none
    | some (x, y, z, w) => if x ≠ 1 then none else some [y, z, w]
  else none

theorem classMinorSlot_spec (p : Prog) (hgo : p.lookup "class_minor_slot_go" = some classMinorSlotGo)
    (hp : p.lookup "class_minor_slot" = some classMinorSlotL) (n : Nat) (s₀ : St) (rd c cc : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_minor_slot" [rd, c, cc]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ classMinorSlotW n s₀.mem rd c cc = some r; ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classMinorSlotL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      classMinorSlotGo_spec p hgo n] <;>
    finish [classMinorSlotW]

theorem hitsFrom_eq (c : Nat) (C : NIdx) : ∀ (j : Nat) (sls : List ClassSlot),
    (List.range sls.length).filterMap (fun s =>
      match (sls[s]? : Option ClassSlot) with
      | some (.minor c' C' ihs) => if c' == c && C' == C then some (j + s, ihs) else none
      | _ => none) = hitsFrom c C j sls := by
  intro j sls
  induction sls generalizing j with
  | nil => simp [hitsFrom]
  | cons sl sls ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons]
    rw [List.filterMap_map]
    have e : ((fun s => match (sls[s]? : Option ClassSlot) with
          | some (.minor c' C' ihs) => if c' == c && C' == C then some (j + 1 + s, ihs) else none
          | _ => none)) = (fun s => match ((sl :: sls)[s]? : Option ClassSlot) with
          | some (.minor c' C' ihs) => if c' == c && C' == C then some (j + s, ihs) else none
          | _ => none) ∘ Nat.succ := by
      funext s
      simp only [Function.comp, List.getElem?_cons_succ]
      have : j + (s + 1) = j + 1 + s := by omega
      simp only [this, Nat.succ_eq_add_one]
    rw [← e, ih (j + 1)]
    cases sl with
    | motive k => simp [hitsFrom]
    | minor c' C' ihs => by_cases hh : (c' == c && C' == C) = true <;> simp [hitsFrom, hh]


theorem decPL_le {α : Type} {m : Mem} {f : Nat → Option α} : ∀ {o l : Nat} {xs : List α},
    decPL m f o l = some xs → l = 0 ∨ o + l ≤ (m.arr64 IW).size := by
  intro o l
  induction l generalizing o with
  | zero => intro xs _; exact Or.inl rfl
  | succ l ih =>
    intro xs h
    obtain ⟨p, x, ys, -, hp, -, hr⟩ := decPL_cons h
    have h1 := iwN_lt hp
    rcases ih hr with h0 | h0
    · right; omega
    · right; omega

theorem classMinorSlotW_ok (n : Nat) (m : Mem) (rd c cc : Word) (R : ClassRead) (r : List Word)
    (hR : decCR m rd.toNat = some R) (hcc : cc.toNat < 2 ^ 32) (hsz : (m.arr64 IW).size + 5 < 2 ^ 64)
    (h : classMinorSlotW n m rd c cc = some r) :
    ∃ s ihs, (hitsFrom c.toNat (decI cc) 0 R.slots = [(s, ihs)]) ∧
      r.headD 0 = UInt64.ofNat s ∧ decPL m (decNN m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some ihs := by
  simp only [decCR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hR
  obtain ⟨slots, hsl, rcs, -, hRe⟩ := hR
  subst hRe
  obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hsl
  simp only at *
  have hrd64 : rd.toNat < 2 ^ 64 := rd.toNat_lt
  have ho' := iwN_rdW ho hrd64
  rw [UInt64.ofNat_toNat] at ho'
  have hl' := iwN_off (k := 1) hl (by have := iwN_lt hl; omega)
  rw [show UInt64.ofNat 1 = 1 from rfl, UInt64.ofNat_toNat] at hl'
  have hl1 : rdW (m.arr64 IW) (rd + 1) = UInt64.ofNat l := hl'.2
  have hl2 : (rd + 1).toNat < (m.arr64 IW).size := hl'.1
  have ho2 : rd.toNat < (m.arr64 IW).size := iwN_lt ho
  simp only [classMinorSlotW, ho2, hl2, and_self, if_true] at h
  rw [ho'.1, hl1] at h
  cases hg : classMinorSlotGoW n m (UInt64.ofNat o) (UInt64.ofNat l) 0 c cc 0 0 0 0 with
  | none => rw [hg] at h; simp at h
  | some xyzw =>
    obtain ⟨x, y, z, w⟩ := xyzw
    rw [hg] at h
    by_cases hx : x ≠ 1
    · simp [hx] at h
    simp only [hx, if_false, Option.some.injEq] at h
    subst h
    have hx1 : x = 1 := by simpa using hx
    have hol : o + l < 2 ^ 64 := by
      rcases decPL_le hdec with h0 | h0
      · have : o < 2 ^ 64 := ho'.2
        omega
      · omega
    have hlz : l < 2 ^ 64 := (iwN_rdW hl (by have := iwN_lt hl; omega)).2
    have hos : o < 2 ^ 64 := ho'.2
    have hg2 := classMinorSlotGoW_ok n m (UInt64.ofNat o) (UInt64.ofNat l) 0 c cc 0 0 0 0 x y z w slots hg
      (by simpa [UInt64.toNat_ofNat_of_lt' hos, UInt64.toNat_ofNat_of_lt' hlz] using hdec) hcc hsz
      (by simp [UInt64.toNat_ofNat_of_lt' hos, UInt64.toNat_ofNat_of_lt' hlz]; omega)
      (by simp [UInt64.toNat_ofNat_of_lt' hlz]; omega) (by simp [UInt64.toNat_ofNat_of_lt' hlz]; omega)
    obtain ⟨g1, g2, g3⟩ := hg2
    simp only [UInt64.toNat_zero, Nat.zero_add] at g1 g2 g3
    rw [hx1] at g1
    have hlen : (hitsFrom c.toNat (decI cc) 0 slots).length = 1 := by
      have : (1 : Word).toNat = 1 := rfl
      omega
    match hh : hitsFrom c.toNat (decI cc) 0 slots, hlen with
    | [(s, ihs)], _ =>
      rw [hh] at g3
      obtain ⟨e1, e2⟩ := g3 s ihs rfl
      exact ⟨s, ihs, rfl, by simpa using e1, by simpa using e2⟩


/-- **`class_minor_slot` refines `classMinorSlot`**: the twin succeeds (without touching the state)
with the unique `.minor c cc` slot, and the words are its position and `ihs` slice. -/
@[refines ConRon.Arena.classMinorSlot]
theorem classMinorSlot_refines (p : Prog)
    (hgo : p.lookup "class_minor_slot_go" = some classMinorSlotGo)
    (hp : p.lookup "class_minor_slot" = some classMinorSlotL) (n : Nat) (s₀ : St) (a₀ : AState)
    (rd c cc : Word) (R : ClassRead) (hR : decCR s₀.mem rd.toNat = some R) (hcc : cc.toNat < 2 ^ 32)
    (hsz : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_minor_slot" [rd, c, cc]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      AM.ok (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀ ∧
      AM.st (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀ = a₀ ∧
      r.headD 0 = UInt64.ofNat (AM.res (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀).1 ∧
      decPL s₀.mem (decNN s₀.mem) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat =
        some (AM.res (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀).2; ⊤⦄ := by
  refine triple_post (classMinorSlot_spec p hgo hp n s₀ rd c cc) ?_
  rintro r s' ⟨hl, hm, hw⟩
  obtain ⟨s, ihs, hh, e1, e2⟩ := classMinorSlotW_ok n s₀.mem rd c cc R r hR hcc hsz hw
  have hits := hitsFrom_eq c.toNat (decI cc) 0 R.slots
  simp only [Nat.zero_add] at hits
  have hrun : (ConRon.Arena.classMinorSlot R c.toNat (decI cc)).run a₀ = .ok ((s, ihs), a₀) := by
    simp only [ConRon.Arena.classMinorSlot]
    erw [hits, hh]
    rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hm, hok, hst, by rw [hres]; exact e1, by rw [hres]; exact e2⟩

end L.Ind
