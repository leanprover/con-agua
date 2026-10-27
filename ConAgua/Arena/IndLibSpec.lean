import ConAgua.Arena.IndIface
import ConAgua.Arena.Env
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The slice library's specs (lane `induct`)

The library functions of `IndIface.lean` are recursive on the slice (`o + 1`, `l - 1`), as lane
`levels`' `lv_mem` is; their word models take the L fuel, and the slice is related to its words
by the inductive `SlR` (no `Nat` offsets, so no overflow side conditions: lane `levels`' `NmsR`
finding). `slR_of_dec`: an `IW` slice that decodes (`decHL`, `Option`-valued over `Nat`
offsets) is an `SlR` slice of the handles' words.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The words of the `IW` slice `[o, o + l)`**, read as the recursive library reads them. -/
inductive SlR (m : Mem) : Word → Word → List Word → Prop
  | nil {o : Word} : SlR m o 0 []
  | cons {o l : Word} {ws : List Word} : l ≠ 0 → SlR m (o + 1) (l - 1) ws →
      SlR m o l (rdW (m.arr64 IW) o :: ws)

/-! ## `sl_contains` -/

/-- The model of `sl_contains`. -/
def containsW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, o, l, x =>
    if l = 0 then some 0
    else if rdW (m.arr64 IW) o = x then some 1
    else containsW n m (o + 1) (l - 1) x

section arms
variable (n : Nat) (m : Mem) (o l x : Word)
theorem containsW_nil (hl : l = 0) : containsW (n + 1) m o l x = some 0 := by simp [containsW, hl]
theorem containsW_hit (hl : l ≠ 0) (hx : rdW (m.arr64 IW) o = x) :
    containsW (n + 1) m o l x = some 1 := by simp [containsW, hl, hx]
theorem containsW_next (hl : l ≠ 0) (hx : rdW (m.arr64 IW) o ≠ x) :
    containsW (n + 1) m o l x = containsW n m (o + 1) (l - 1) x := by simp [containsW, hl, hx]
end arms

grind_pattern [ind_grind] containsW_nil => containsW (n + 1) m o l x
grind_pattern [ind_grind] containsW_hit => containsW (n + 1) m o l x
grind_pattern [ind_grind] containsW_next => containsW (n + 1) m o l x

section specs
variable (p : Prog)

theorem slContains_spec (hp : p.lookup "sl_contains" = some slContains) (n : Nat) :
    ∀ (s₀ : St) (o l x : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_contains" [o, l, x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ containsW n s₀.mem o l x = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l x; rw [invoke_eq _ hp]; simp only [callFn, slContains]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l x
    rw [invoke_eq _ hp]
    simp only [callFn, slContains]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

end specs

theorem containsW_ok (n : Nat) : ∀ (m : Mem) (o l x r : Word) (ws : List Word), SlR m o l ws →
    containsW n m o l x = some r → r = if ws.contains x then 1 else 0 := by
  induction n with
  | zero => intro m o l x r ws _ h; simp [containsW] at h
  | succ n ih =>
    intro m o l x r ws hs h
    cases hs with
    | nil => rw [containsW_nil n m o 0 x rfl] at h; simp at h; simp [h]
    | @cons _ _ ws hl hs =>
      by_cases e : rdW (m.arr64 IW) o = x
      · rw [containsW_hit n m o _ x hl e] at h; simp at h; simp [← h, e]
      · rw [containsW_next n m o _ x hl e] at h
        rw [ih _ _ _ _ _ _ hs h]
        simp [Ne.symm e]

/-! ## `sl_nodup`: `nameNodup` -/

/-- The model of `sl_nodup`. -/
def nodupW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if l = 0 then some 1
    else nodupK n m o l (containsW n m (o + 1) (l - 1) (rdW (m.arr64 IW) o))
where
  /-- After the membership test. -/
  nodupK (n : Nat) (m : Mem) (o l : Word) : Option Word → Option Word
    | none => none
    | some b => if b ≠ 0 then some 0 else nodupW n m (o + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (o l b : Word)
theorem nodupW_nil (hl : l = 0) : nodupW (n + 1) m o l = some 1 := by simp [nodupW, hl]
theorem nodupW_cons (hl : l ≠ 0) :
    nodupW (n + 1) m o l = nodupW.nodupK n m o l (containsW n m (o + 1) (l - 1) (rdW (m.arr64 IW) o)) := by
  simp [nodupW, hl]
theorem nodupK_hit (hb : b ≠ 0) : nodupW.nodupK n m o l (some b) = some 0 := by
  simp [nodupW.nodupK, hb]
theorem nodupK_miss (hb : b = 0) : nodupW.nodupK n m o l (some b) = nodupW n m (o + 1) (l - 1) := by
  simp [nodupW.nodupK, hb]
end arms

grind_pattern [ind_grind] nodupW_nil => nodupW (n + 1) m o l
grind_pattern [ind_grind] nodupW_cons => nodupW (n + 1) m o l
grind_pattern [ind_grind] nodupK_hit => nodupW.nodupK n m o l (some b)
grind_pattern [ind_grind] nodupK_miss => nodupW.nodupK n m o l (some b)

section specs
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains)
include hc

theorem slNodup_spec (hp : p.lookup "sl_nodup" = some slNodup) (n : Nat) :
    ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_nodup" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ nodupW n s₀.mem o l = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l; rw [invoke_eq _ hp]; simp only [callFn, slNodup]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l
    rw [invoke_eq _ hp]
    simp only [callFn, slNodup]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slContains_spec p hc n, ih] <;>
      finish (gen := 20)

end specs

/-- The twin's `nameNodup` over handle words. -/
theorem nameNodup_map (ws : List Word) (hw : ∀ w ∈ ws, w.toNat < 2 ^ 32) :
    nameNodup (ws.map decI) = (decide ws.Nodup) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw' : ∀ v ∈ ws, v.toNat < 2 ^ 32 := fun v hv => hw v (List.mem_cons_of_mem _ hv)
    simp only [List.map_cons, nameNodup, ih hw', List.nodup_cons]
    have : (ws.map (decI : Word → NIdx)).contains (decI w) = ws.contains w := by
      rw [Bool.eq_iff_iff]
      simp only [List.contains_iff_mem, List.mem_map]
      constructor
      · rintro ⟨v, hv, e⟩
        have := (decI_eq_iff w (hw w (List.mem_cons_self ..)) (decI v)).mp e.symm
        rw [this, decI_word_self v (hw' v hv)]; exact hv
      · intro h; exact ⟨w, h, rfl⟩
    rw [this]
    by_cases h : w ∈ ws <;> simp [h]

theorem nodupW_ok (n : Nat) : ∀ (m : Mem) (o l r : Word) (ws : List Word), SlR m o l ws →
    nodupW n m o l = some r → r = if ws.Nodup then 1 else 0 := by
  induction n with
  | zero => intro m o l r ws _ h; simp [nodupW] at h
  | succ n ih =>
    intro m o l r ws hs h
    cases hs with
    | nil => rw [nodupW_nil n m o 0 rfl] at h; simp at h; simp [h]
    | @cons _ _ ws hl hs =>
      rw [nodupW_cons n m o _ hl] at h
      cases e : containsW n m (o + 1) (_ - 1) (rdW (m.arr64 IW) o) with
      | none => rw [e] at h; simp [nodupW.nodupK] at h
      | some b =>
        rw [e] at h
        have hb := containsW_ok n _ _ _ _ _ _ hs e
        by_cases hb0 : b = 0
        · rw [nodupK_miss n m o _ b hb0] at h
          rw [ih _ _ _ _ _ hs h]
          have : ¬ rdW (m.arr64 IW) o ∈ ws := by
            intro hm
            have hc : ws.contains (rdW (m.arr64 IW) o) = true := List.contains_iff_mem.mpr hm
            rw [hb0, hc] at hb; simp at hb
          simp [List.nodup_cons, this]
        · rw [nodupK_hit n m o _ b hb0] at h
          simp at h
          have : rdW (m.arr64 IW) o ∈ ws := by
            by_cases hm : rdW (m.arr64 IW) o ∈ ws
            · exact hm
            · have hc : ws.contains (rdW (m.arr64 IW) o) = false := by
                simpa [List.contains_iff_mem] using hm
              rw [hc] at hb; simp at hb; exact absurd hb hb0
          simp [List.nodup_cons, this, ← h]

/-- **`sl_nodup` is `nameNodup`** on a slice of name handle words. -/
@[refines ConRon.Arena.nameNodup]
theorem slNodup_refines (p : Prog) (hc : p.lookup "sl_contains" = some slContains)
    (hp : p.lookup "sl_nodup" = some slNodup) (n : Nat) (s₀ : St) (o l : Word) (ws : List Word)
    (hs : SlR s₀.mem o l ws) (hw : ∀ w ∈ ws, w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_nodup" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 != 0) = nameNodup (ws.map decI); ⊤⦄ := by
  have h := slNodup_spec p hc hp n s₀ o l
  refine triple_post h ?_
  intro r s' ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  rw [nodupW_ok n _ _ _ _ _ hs h3, nameNodup_map ws hw]
  by_cases hn : ws.Nodup <;> simp [hn]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## From the `Option` decoders to `SlR` -/

theorem hslice?_succ {k : IdxKind} (a : Array Word) (off n : Nat) :
    (hslice? a off (n + 1) : Option (List (Idx k))) = (do
      let x ← hd? a off
      let xs ← hslice? a (off + 1) n
      pure (x :: xs)) := by
  simp only [hslice?, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

/-- **A decoding `IW` handle slice is an `SlR` slice** of handle words (offsets in range). -/
theorem slR_of_decHL {k : IdxKind} (m : Mem) : ∀ (n off : Nat) (ns : List (Idx k)),
    decHL m off n = some ns → off + n < 2 ^ 64 →
    ∃ ws, SlR m (UInt64.ofNat off) (UInt64.ofNat n) ws ∧ ns = ws.map decI ∧
      ∀ w ∈ ws, w.toNat < 2 ^ 32 := by
  intro n
  induction n with
  | zero =>
    intro off ns h _
    simp [decHL, hslice?] at h
    exact ⟨[], by simpa using (SlR.nil (m := m) (o := UInt64.ofNat off)), by simp [h], by simp⟩
  | succ n ih =>
    intro off ns h hb
    simp only [decHL, hslice?_succ] at h
    cases hx : (hd? (iwA m) off : Option (Idx k)) with
    | none => simp [hx] at h
    | some x =>
      cases hxs : (hslice? (iwA m) (off + 1) n : Option (List (Idx k))) with
      | none => simp [hx, hxs] at h
      | some xs =>
        simp [hx, hxs] at h
        obtain ⟨ws, hws, rfl, hlt⟩ := ih (off + 1) xs hxs (by omega)
        simp only [hd?] at hx
        cases hw : (iwA m)[off]? with
        | none => simp [hw] at hx
        | some w =>
          simp only [hw] at hx
          by_cases hwl : w.toNat < 2 ^ 32
          · simp [hwl] at hx
            subst h
            refine ⟨w :: ws, ?_, by simp [hx], ?_⟩
            · have e1 : rdW (m.arr64 IW) (UInt64.ofNat off) = w := by
                simp only [rdW, iwA] at hw ⊢
                have : (UInt64.ofNat off).toNat = off := by simp; omega
                rw [this, hw]; rfl
              have e2 : UInt64.ofNat off + 1 = UInt64.ofNat (off + 1) := by
                simp [UInt64.ofNat_add]
              have e3 : UInt64.ofNat (n + 1) - 1 = UInt64.ofNat n := by
                simp [UInt64.ofNat_add]
              have hne : UInt64.ofNat (n + 1) ≠ 0 := by
                intro h0
                have := congrArg UInt64.toNat h0
                simp at this; omega
              rw [← e1]
              exact SlR.cons hne (by rw [e2, e3]; exact hws)
            · intro v hv
              simp at hv
              rcases hv with rfl | hv
              · exact hwl
              · exact hlt v hv
          · simp [hwl] at hx

end L.Ind

namespace L.Ind

open L.Arena

/-! ## The decoders' list lemmas -/

theorem mapM_opt_length {α β : Type} (g : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM g = some ys → ys.length = xs.length
  | [], ys, h => by simp at h; simp [← h]
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hx : g x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM g with
      | none => simp [hx, hxs] at h
      | some zs =>
        simp [hx, hxs] at h
        subst h
        simp [mapM_opt_length g xs zs hxs]

theorem mapM_opt_get {α β : Type} (g : α → Option β) :
    ∀ (xs : List α) (ys : List β) (h : xs.mapM g = some ys) (j : Nat) (hj : j < xs.length),
      g xs[j] = some (ys[j]'(by rw [mapM_opt_length g xs ys h]; exact hj))
  | [], _, _, j, hj => by simp at hj
  | x :: xs, ys, h, j, hj => by
    simp only [List.mapM_cons] at h
    cases hx : g x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM g with
      | none => simp [hx, hxs] at h
      | some zs =>
        simp [hx, hxs] at h
        subst h
        cases j with
        | zero => simpa using hx
        | succ j => simpa using mapM_opt_get g xs zs hxs j (by simpa using hj)

section declemmas
variable (m : Mem)

theorem decHL_length {k : IdxKind} {o l : Nat} {xs : List (Idx k)} (h : decHL m o l = some xs) :
    xs.length = l := by
  simpa using mapM_opt_length _ _ _ h

theorem decNL_length {o l : Nat} {xs : List Nat} (h : decNL m o l = some xs) : xs.length = l := by
  simpa using mapM_opt_length _ _ _ h

theorem decPL_length {α : Type} {f : Nat → Option α} {o l : Nat} {xs : List α}
    (h : decPL m f o l = some xs) : xs.length = l := by
  simpa using mapM_opt_length _ _ _ h

end declemmas

end L.Ind

namespace L.Ind

open L.Arena

/-! ## The pool: `iw_alloc` -/

/-- The memory after `iw_alloc(k)`. -/
def allocMem (m : Mem) (k : Word) : Mem := m.set64 CTL 200 (rdW (m.arr64 CTL) 200 + k)

theorem iwAlloc_spec (p : Prog) (hp : p.lookup "iw_alloc" = some iwAlloc) (n : Nat) (s₀ : St)
    (k : Word) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "iw_alloc" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = allocMem s₀.mem k ∧
      r.headD 0 = rdW (s₀.mem.arr64 CTL) 200 ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + k.toNat ≤ (s₀.mem.arr64 IW).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iwAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [allocMem, Mem.len64]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Records: `rec2` -/

/-- The memory after `rec2(a, b)`. -/
def rec2Mem (m : Mem) (a b : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  ((allocMem m 2).set64 IW q a).set64 IW (q + 1) b

theorem rec2_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "rec2" = some rec2) (n : Nat) (s₀ : St) (a b : Word)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec2" [a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = rec2Mem s₀.mem a b ∧
      r.headD 0 = rdW (s₀.mem.arr64 CTL) 200 ∧
      (rdW (s₀.mem.arr64 CTL) 200).toNat + 2 ≤ (s₀.mem.arr64 IW).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, rec2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_spec p ha n] <;>
      finish [rec2Mem, allocMem]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Frames: the pool's writers keep the checker state -/

/-- **A writer of `IW` and `CTL[200]` keeps `CheckR`.** -/
theorem CheckR.frame_iw {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} (hf : MemFrame [IW] [200] m m') (h : CheckR dn m a vis fe) : CheckR dn m' a vis fe :=
  ⟨⟨ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, IW])
      (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf h.arena.1,
    DerR.frameM _ _ m m' hf (by decide) a h.arena.2⟩,
   h.core.frame (fun b hb => by simp at hb; subst hb; decide)
     (fun x hx => by simp at hx; subst hx; decide) hf,
   h.pins.frame (fun b hb => by simp at hb; subst hb; decide) hf,
   h.env.frame (fun b hb => by simp at hb; subst hb; decide)
     (fun x hx => by simp at hx; subst hx; decide) hf,
   h.mode.frame hf (by decide) (by decide)⟩

theorem allocMem_frame (m : Mem) (k : Word) : MemFrame [IW] [200] m (allocMem m k) :=
  MemFrame.mono (MemFrame.setCtl m 200 _) (by simp) (by simp)

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Growth -/

theorem IWGrow.refl (m : Mem) : IWGrow m m := ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem IWGrow.trans {m₁ m₂ m₃ : Mem} (h₁ : IWGrow m₁ m₂) (h₂ : IWGrow m₂ m₃) : IWGrow m₁ m₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2.1 h₂.2.1,
   fun i hi => (h₂.2.2.1 i (by have := h₁.1; omega)).trans (h₁.2.2.1 i hi),
   fun i hi => (h₂.2.2.2 i (by have := h₁.2.1; omega)).trans (h₁.2.2.2 i hi)⟩

/-- A write to `IW` at or above the top keeps the growth. -/
theorem IWGrow.set_iw {m m' : Mem} (h : IWGrow m m') (k v : Word) (hk : iwTop m ≤ k.toNat) :
    IWGrow m (m'.set64 IW k v) := by
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [iwTop, rdW_set64]; simp [show (CTL : ArrId) ≠ IW by decide]; exact h.1
  · simp only [erTop, rdW_set64]; simp [show (CTL : ArrId) ≠ IW by decide]; exact h.2.1
  · rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    have : ¬ (k.toNat = i) := by omega
    simp only [this, ite_false]; exact h.2.2.1 i hi
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.2.2.2 i hi

/-- Raising the top keeps the growth. -/
theorem IWGrow.set_top {m m' : Mem} (h : IWGrow m m') (t : Word) (ht : iwTop m' ≤ t.toNat)
    (hc : 200 < (m'.arr64 CTL).size) :
    IWGrow m (m'.set64 CTL 200 t) := by
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [iwTop, rdW_set64]; simp [hc]; have := h.1; simp only [iwTop] at this ht; omega
  · simp only [erTop, rdW_set64]; simp; exact h.2.1
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.2.2.1 i hi
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact h.2.2.2 i hi

end L.Ind

namespace L.Ind

open L.Arena

theorem allocMem_grow (m : Mem) (k : Word) (hk : iwTop m + k.toNat < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) : IWGrow m (allocMem m k) := by
  refine (IWGrow.refl m).set_top _ ?_ hc
  simp only [iwTop] at hk ⊢
  rw [UInt64.toNat_add]; simp; omega

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Reading decoded words -/

section reads
variable {m : Mem}

theorem iwN_rdW {i v : Nat} (h : iwN m i = some v) (hi : i < 2 ^ 64) :
    rdW (m.arr64 IW) (UInt64.ofNat i) = UInt64.ofNat v ∧ v < 2 ^ 64 := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have : (UInt64.ofNat i).toNat = i := by simp; omega
  simp only [rdW, this, hw, Option.getD_some]
  exact ⟨by simp, w.toNat_lt⟩

theorem iwH_rdW {k : IdxKind} {i : Nat} {x : Idx k} (h : iwH m i = some x) (hi : i < 2 ^ 64) :
    ∃ w, rdW (m.arr64 IW) (UInt64.ofNat i) = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x := by
  simp only [iwH, hd?, iwA] at h
  cases hw : (m.arr64 IW)[i]? with
  | none => simp [hw] at h
  | some w =>
    simp only [hw] at h
    by_cases hl : w.toNat < 2 ^ 32
    · simp [hl] at h
      have : (UInt64.ofNat i).toNat = i := by simp; omega
      exact ⟨w, by simp [rdW, this, hw], hl, h⟩
    · simp [hl] at h

theorem decAt_some {α : Type} {g : Nat → Nat → Option (List α)} {i : Nat} {xs : List α}
    (h : decAt m g i = some xs) : ∃ o l, iwN m i = some o ∧ iwN m (i + 1) = some l ∧ g o l = some xs := by
  simp only [decAt] at h
  cases ho : iwN m i with
  | none => simp [ho] at h
  | some o =>
    cases hl : iwN m (i + 1) with
    | none => simp [ho, hl] at h
    | some l => simp [ho, hl] at h; exact ⟨o, l, rfl, rfl, h⟩

end reads

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `sl_find`: `findIdx? (· == x)` -/

/-- The model of `sl_find`. -/
def findW : Nat → Mem → Word → Word → Word → Option (List Word)
  | 0, _, _, _, _ => none
  | n + 1, m, o, l, x =>
    if l = 0 then some [0, 0]
    else if rdW (m.arr64 IW) o = x then some [1, 0]
    else findK (findW n m (o + 1) (l - 1) x)
where
  /-- After the recursive call. -/
  findK : Option (List Word) → Option (List Word)
    | none => none
    | some r => if r.headD 0 = 0 then some [0, 0] else some [1, r.tail.headD 0 + 1]

section arms
variable (n : Nat) (m : Mem) (o l x : Word) (r : List Word)
theorem findW_nil (hl : l = 0) : findW (n + 1) m o l x = some [0, 0] := by simp [findW, hl]
theorem findW_hit (hl : l ≠ 0) (hx : rdW (m.arr64 IW) o = x) : findW (n + 1) m o l x = some [1, 0] := by
  simp [findW, hl, hx]
theorem findW_next (hl : l ≠ 0) (hx : rdW (m.arr64 IW) o ≠ x) :
    findW (n + 1) m o l x = findW.findK (findW n m (o + 1) (l - 1) x) := by simp [findW, hl, hx]
theorem findK_miss (h : r.headD 0 = 0) : findW.findK (some r) = some [0, 0] := by
  simp only [findW.findK]; rw [ite_eq_left h]
theorem findK_hit (h : r.headD 0 ≠ 0) : findW.findK (some r) = some [1, r.tail.headD 0 + 1] := by
  simp only [findW.findK]; rw [ite_eq_right h]
end arms

grind_pattern [ind_grind] findW_nil => findW (n + 1) m o l x
grind_pattern [ind_grind] findW_hit => findW (n + 1) m o l x
grind_pattern [ind_grind] findW_next => findW (n + 1) m o l x
grind_pattern [ind_grind] findK_miss => findW.findK (some r)
grind_pattern [ind_grind] findK_hit => findW.findK (some r)

theorem slFind_spec (p : Prog) (hp : p.lookup "sl_find" = some slFind) (n : Nat) :
    ∀ (s₀ : St) (o l x : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_find" [o, l, x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ findW n s₀.mem o l x = some r; ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l x; rw [invoke_eq _ hp]; simp only [callFn, slFind]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l x
    rw [invoke_eq _ hp]
    simp only [callFn, slFind]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

/-- **`sl_find` is `findIdx? (· == x)`** on the slice's words: `(1, i)` for the first index,
`(0, 0)` for none (index words below `2^64`: the slice is shorter). -/
theorem findW_ok (n : Nat) : ∀ (m : Mem) (o l x : Word) (r : List Word) (ws : List Word),
    SlR m o l ws → findW n m o l x = some r → ws.length < 2 ^ 64 →
    r = match ws.findIdx? (· == x) with
      | some i => [1, UInt64.ofNat i]
      | none => [0, 0] := by
  induction n with
  | zero => intro m o l x r ws _ h; simp [findW] at h
  | succ n ih =>
    intro m o l x r ws hs h hlen
    cases hs with
    | nil => rw [findW_nil n m o 0 x rfl] at h; simp at h; simp [h]
    | @cons _ _ ws hl hs =>
      by_cases e : rdW (m.arr64 IW) o = x
      · rw [findW_hit n m o _ x hl e] at h; simp at h; simp [← h, e, List.findIdx?_cons]
      · rw [findW_next n m o _ x hl e] at h
        cases hr : findW n m (o + 1) (_ - 1) x with
        | none => rw [hr] at h; simp [findW.findK] at h
        | some r' =>
          rw [hr] at h
          have := ih _ _ _ _ _ _ hs hr (by simp at hlen; omega)
          simp only [List.findIdx?_cons, beq_iff_eq, e, ite_false]
          cases hf : ws.findIdx? (· == x) with
          | none => rw [hf] at this; subst this; rw [findK_miss _ (by simp)] at h; simp at h; simp [h]
          | some i =>
            rw [hf] at this; subst this
            rw [findK_hit _ (by simp)] at h; simp at h
            simp [← h]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `sl_get`, `sl_getd`: one word of a slice (lane `indproofs`) -/

/-- The model of `sl_get(o, l, i)`: `none` (abort) past the end. -/
def getW (m : Mem) (o l i : Word) : Option Word :=
  if l ≤ i then none else some (rdW (m.arr64 IW) (o + i))

/-- The model of `sl_getd(o, l, i, d)`. -/
def getDW (m : Mem) (o l i d : Word) : Word :=
  if l ≤ i then d else rdW (m.arr64 IW) (o + i)

theorem slGet_specW (p : Prog) (hp : p.lookup "sl_get" = some slGet) (n : Nat) (s₀ : St)
    (o l i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_get" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ getW s₀.mem o l i = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slGet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [getW]

theorem slGetD_specW (p : Prog) (hp : p.lookup "sl_getd" = some slGetD) (n : Nat) (s₀ : St)
    (o l i d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_getd" [o, l, i, d]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = getDW s₀.mem o l i d; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slGetD]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [getDW]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## The stage relation across a store writer (lane `indproofs`) -/

/-- **A writer below array 64 and `CTL[64]` (an interning, a `mk_*`, a walk) keeps the stage
relation**, given its `ArenaD` after and the twin keeping caches and pins; the pool is
untouched, so it only grew. -/
theorem StageR.of_walkM {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m m' : Mem} {a a' : AState} {A : List ArrId} {C : List Word}
    (hS : StageR dn vis fe m a) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64) (hk : cp a' = cp a)
    (hmode : ModeOK m') :
    StageR dn vis fe m' a' ∧ IWGrow m m' := by
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW (fun h => by have := hA _ h; simp [IW] at this)
    (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (fun h => by have := hA _ h; simp [EREC] at this)
    (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 :=
    hf.2.1 200 (fun h => by have := hC _ h; simp at this)
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 :=
    hf.2.1 129 (fun h => by have := hC _ h; simp at this)
  refine ⟨⟨CheckR.of_walkM hS.1 hD hf hA hC hk hmode, ?_⟩, ?_⟩
  · simp only [IWOK, iwTop, erTop, hI, hE, h200, h129, hf.2.2.1 CTL]; exact hS.2
  · refine ⟨?_, ?_, fun i _ => by rw [hI], fun i _ => by rw [hE]⟩
    · simp only [iwTop, h200]; exact Nat.le_refl _
    · simp only [erTop, h129]; exact Nat.le_refl _

/-- `StageR.of_walkM` for a walk that keeps `CTL[0]` and `CTL[1]`. -/
theorem StageR.of_walk {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m m' : Mem} {a a' : AState} {A : List ArrId} {C : List Word}
    (hS : StageR dn vis fe m a) (hD : ArenaD m' a') (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64) (hk : cp a' = cp a)
    (h01 : (0 : Word) ∉ C ∧ (1 : Word) ∉ C := by decide) :
    StageR dn vis fe m' a' ∧ IWGrow m m' :=
  StageR.of_walkM hS hD hf hA hC hk (hS.1.mode.frame hf h01.1 h01.2)

end L.Ind
