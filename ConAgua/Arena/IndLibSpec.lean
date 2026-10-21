import ConAgua.Arena.IndIface
import ConAgua.Arena.IndGrindAttr

/-!
# The slice library's specs (lane `induct`)

The library functions of `IndIface.lean` are recursive on the slice (`o + 1`, `l - 1`), as lane
`levels`' `lv_mem` is; their word models take the L fuel, and the slice is related to its words
by the inductive `SlR` (no `Nat` offsets, so no overflow side conditions: lane `levels`' `NmsR`
finding). `slR_of_dec`: an `IW` slice that decodes (`decHL`, `Option`-valued over `Nat`
offsets) is an `SlR` slice of the handles' words.
-/

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
        simp [List.contains_cons, Ne.symm e]

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
