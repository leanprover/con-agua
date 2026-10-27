import ConAgua.Arena.DefEqMid
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# `defeq_lst`, `defeq_list_rev`: the twin's `defEqList` over two stack slices (lane `defeq`)

Each loop is a named block (`defeqLstLoop`, `defeqListRevLoop`) with a model by fuel (`lstW`,
`lrevW`: one `defeq` run per iteration, `callW`), the block's spec by induction + `vcgen`, and the
model's refinement by induction on the fuel (`lstW_ok`, `lrevW_ok`, as `coreLoopW_ok`): each
iteration's `defeq` call is the knot's slot at a smaller fuel (`KnotUpTo`). The slices are
`SpineR` at the entry memory `m₀` and below its stack top, so every later memory that keeps the
stack (`StackKept m₀ m`) holds the same words there.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Shared -/

/-- **A core run, then the rest of a `do` block**, also passing the stack kept from `m₀`. -/
theorem coreRef_bindS {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {f : α → AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackKept m₀ m₁ →
      CoreRef (f (dec₁ r₁)) (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok) :
    CoreRef (T₁ >>= f) a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  obtain ⟨hok2, hA2, hres2, hrw2⟩ := h₂ M' hS hSt
  have hT : (T₁ >>= f).run a₀ = (f (dec₁ r₁)).run (AM.st T₁ a₀) := by
    rw [StateT.run_bind, AM.run_of_ok _ _ h₁.1, h₁.2.2.1]; rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hT.trans (AM.run_of_ok _ _ hok2))
  exact ⟨hok, hst ▸ CoreAfter.comp hK hSt hA2, hres.trans hres2, hrw2⟩

/-- A stack word of a slice below the top, read from a later memory that kept the stack. -/
theorem slice_kept {m₀ m : Mem} {o c : Word} (hk : StackKept m₀ m)
    (ht : o.toNat + c.toNat ≤ (spTop m₀).toNat) (j : Word) (hj : j.toNat < c.toNat) :
    spW m (o + j) = spW m₀ (o + j) := by
  apply hk.below
  have h1 : (o + j).toNat = o.toNat + j.toNat := by
    rw [UInt64.toNat_add]; have := (spTop m₀).toNat_lt; omega
  rw [UInt64.lt_iff_toNat_lt, h1]; omega

/-- A slice's element `j` and its word. -/
theorem slice_get {m : Mem} {o c : Word} {xs : List EIdx} (h : SpineR m o c xs.toArray) (j : Word)
    (hj : j.toNat < c.toNat) :
    ∃ hl : j.toNat < xs.length, xs[j.toNat] = decE (spW m (o + j)) ∧ HW (spW m (o + j)) := by
  have hs := h.size
  simp only [List.size_toArray] at hs
  refine ⟨by omega, ?_, ?_⟩
  · have := h.get j.toNat (by simp only [List.size_toArray]; omega)
    simp only [List.getElem_toArray, Nat.toUInt64_eq, UInt64.ofNat_toNat] at this
    exact this
  · have := h.lt j.toNat hj
    simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat] at this
    exact this

theorem slice_len {m : Mem} {o c : Word} {xs : List EIdx} (h : SpineR m o c xs.toArray) :
    xs.length = c.toNat := by
  have hs := h.size; simpa using hs

theorem defEqList_cons (r : CoreFnsA) (fe : IFEnv) (d : Nat) (x y : EIdx) (xs ys : List EIdx) :
    defEqList r fe d (x :: xs) (y :: ys) =
      (r.defeq d x y >>= fun c => if c then defEqList r fe d xs ys else pure false) := by
  simp only [defEqList]

theorem defEqList_nil_left (r : CoreFnsA) (fe : IFEnv) (d : Nat) (ys : List EIdx) :
    defEqList r fe d [] ys = pure ys.isEmpty := by
  cases ys <;> simp [defEqList]

theorem defEqList_nil_right (r : CoreFnsA) (fe : IFEnv) (d : Nat) (xs : List EIdx) :
    defEqList r fe d xs [] = pure xs.isEmpty := by
  cases xs <;> simp [defEqList]

theorem exit_eq (L : List EIdx) (an bn : Word) (hL : L.isEmpty = true ↔ an.toNat = bn.toNat) :
    L.isEmpty = decBool [if an = bn then 1 else 0] := by
  rw [decBool_ite, Bool.eq_iff_iff, hL, decide_eq_true_iff]
  exact ⟨fun h => UInt64.toNat_inj.mp h, fun h => h ▸ rfl⟩

theorem resH_ite (c : Prop) [Decidable c] : ResH [if c then (1 : Word) else 0] := by
  unfold ResH HW; split <;> decide

/-! ## `defeq_lst` -/

/-- **`defeq_lst` is its model `lstW`** (generated; the loop is `lstW.loop1`). -/
l_model defeqLst_spec (p : Prog) (hp : p.lookup "defeq_lst" = some defeqLstL)
  fns [hp ↦ lstW]
  specs [callW_spec p n "defeq"]
  grind [arena_grind] simp []

section lstRef
variable (p : Prog)

/-- **The loop's model refines `defEqList`** on the slices from index `i`. -/
theorem lstW_ok (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d ao an bo bn : Word)
    (hmode : mode < 4) (m₀ : Mem) (xs ys : List EIdx) (hx : SpineR m₀ ao an xs.toArray)
    (hy : SpineR m₀ bo bn ys.toArray) (hxt : ao.toNat + an.toNat ≤ (spTop m₀).toNat)
    (hyt : bo.toNat + bn.toNat ≤ (spTop m₀).toNat) :
    ∀ k, k ≤ n + 1 → ∀ (i : Word) (m m' : Mem) (a : AState) (M : ModeMaps) (eb v : Word),
      CoreS dn m a vis fe M eb → eb = (mode >>> 1) &&& 1 → StackKept m₀ m → i ≤ an → i ≤ bn →
      lstW.loop1 p k m mode vis d ao an bo bn i = some (v, m') →
      CoreRef (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (xs.drop i.toNat)
        (ys.drop i.toNat)) a decBool dn m vis fe M eb [v] m' := by
  have hxl := slice_len hx
  have hyl := slice_len hy
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [lstW.loop1] at h
  | succ k ih =>
    intro hkn i m m' a M eb v hS heb hst hia hib h
    have hia' := UInt64.le_iff_toNat_le.mp hia
    have hib' := UInt64.le_iff_toNat_le.mp hib
    by_cases hex : an ≤ i ∨ bn ≤ i
    · rw [lstW.loop1.arm1 (hc1 := rfl) (hc2 := hex), Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hex' : an.toNat ≤ i.toNat ∨ bn.toNat ≤ i.toNat := by
        rcases hex with h | h
        · exact .inl (UInt64.le_iff_toNat_le.mp h)
        · exact .inr (UInt64.le_iff_toNat_le.mp h)
      have hab : (an = bn) ↔ an.toNat = bn.toNat := ⟨fun h => h ▸ rfl, UInt64.toNat_inj.mp⟩
      rcases hex' with h | h
      · rw [List.drop_eq_nil_of_le (as := xs) (by omega), defEqList_nil_left]
        refine coreRef_ret hS (exit_eq _ an bn ?_) (resH_ite (an = bn))
        simp only [List.isEmpty_iff, List.drop_eq_nil_iff, hyl]
        omega
      · rw [List.drop_eq_nil_of_le (as := ys) (by omega), defEqList_nil_right]
        refine coreRef_ret hS (exit_eq _ an bn ?_) (resH_ite (an = bn))
        simp only [List.isEmpty_iff, List.drop_eq_nil_iff, hxl]
        omega
    have hia2 : i.toNat < an.toNat := by
      rcases Nat.lt_or_ge i.toNat an.toNat with h | h
      · exact h
      · exact absurd (.inl (UInt64.le_iff_toNat_le.mpr h)) hex
    have hib2 : i.toNat < bn.toNat := by
      rcases Nat.lt_or_ge i.toNat bn.toNat with h | h
      · exact h
      · exact absurd (.inr (UInt64.le_iff_toNat_le.mpr h)) hex
    cases hc : callW p k "defeq" [mode, vis, d, spW m (ao + i), spW m (bo + i)] m with
    | none => rw [lstW.loop1.arm2 (hc1 := rfl) (hc2 := hex)] at h; simp only [spW] at hc; rw [hc, lstW.k_defeq.none] at h; cases h
    | some q =>
    obtain ⟨r, m₁⟩ := q
    rw [lstW.loop1.arm2 (hc1 := rfl) (hc2 := hex), show rdW (m.arr64 SPN) = spW m from rfl, hc] at h
    obtain ⟨hlx, hgx, hwx⟩ := slice_get hx i hia2
    obtain ⟨hly, hgy, hwy⟩ := slice_get hy i hib2
    rw [slice_kept hst hxt i hia2] at hc
    rw [slice_kept hst hyt i hib2] at hc
    have h₁ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      ((hk k (by omega)).defeq F _ a dn vis fe M eb mode d _ _ (by omega) (by omega)
        ⟨hS, hmode, heb⟩ hwx hwy) hc
    rw [List.drop_eq_getElem_cons hlx, List.drop_eq_getElem_cons hly, defEqList_cons, hgx, hgy]
    refine coreRef_bindS h₁ (fun M₁ hS₁ hst₁ => ?_)
    by_cases h0 : r.headD 0 = 0
    · rw [lstW.k_defeq.arm1 (hc1 := h0), Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [decBool_f h0]
      exact coreRef_ret hS₁ rfl resH_zero
    rw [lstW.k_defeq.arm2 (hc1 := h0)] at h
    rw [decBool_t h0, ite_eq_left rfl]
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; have := an.toNat_lt; omega
    have := ih (by omega) (i + 1) m₁ m' _ M₁ eb v hS₁ heb (hst.trans hst₁)
      (UInt64.le_iff_toNat_le.mpr (by omega)) (UInt64.le_iff_toNat_le.mpr (by omega)) h
    rw [hi1] at this
    exact this

/-- **`defeq_lst` refines `defEqList`** on two stack slices below the top, at the knot. -/
@[refines ConRon.Arena.defEqList]
theorem defeqLst_refines (hp : p.lookup "defeq_lst" = some defeqLstL) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ao an bo bn : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (xs ys : List EIdx)
    (hx : SpineR s₀.mem ao an xs.toArray) (hy : SpineR s₀.mem bo bn ys.toArray)
    (hxt : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (hyt : bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "defeq_lst" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat xs ys) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqLst_spec p hp (n + 1) s₀ mode vis d ao an bo bn)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [lstW.arm1] at hW
  have := lstW_ok p n hk F hF hn dn vis fe mode d ao an bo bn hs.mode4 s.mem xs ys hx hy hxt hyt
    (n + 1) (Nat.le_refl _) 0 s.mem s'.mem a₀ M eb (r.headD 0) hs.rel hs.eb_mode (StackKept.refl _)
    UInt64.zero_le UInt64.zero_le hW
  simp only [UInt64.toNat_zero, List.drop_zero] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨h1, h2, h3.trans (by simp [decBool]), h4⟩

end lstRef

/-! ## `defeq_list_rev` -/

/-- **`defeq_list_rev` is its model `lrevW`** (generated; the loop is `lrevW.loop1`). -/
l_model defeqListRev_spec (p : Prog) (hp : p.lookup "defeq_list_rev" = some defeqListRevL)
  fns [hp ↦ lrevW]
  specs [callW_spec p n "defeq"]
  grind [arena_grind] simp []


theorem take_rev_succ {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    (xs.take (i + 1)).reverse = xs[i] :: (xs.take i).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; simp

theorem word_pred (i : Word) (h : i ≠ 0) : (i - 1).toNat = i.toNat - 1 := by
  have : i.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp

section lrevRef
variable (p : Prog)

/-- **The loop's model refines `defEqList` on the reversed prefixes.** -/
theorem lrevW_ok (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d ao an bo bn : Word)
    (hmode : mode < 4) (m₀ : Mem) (xs ys : List EIdx) (hx : SpineR m₀ ao an xs.toArray)
    (hy : SpineR m₀ bo bn ys.toArray) (hxt : ao.toNat + an.toNat ≤ (spTop m₀).toNat)
    (hyt : bo.toNat + bn.toNat ≤ (spTop m₀).toNat) :
    ∀ k, k ≤ n + 1 → ∀ (i j : Word) (m m' : Mem) (a : AState) (M : ModeMaps) (eb v : Word),
      CoreS dn m a vis fe M eb → eb = (mode >>> 1) &&& 1 → StackKept m₀ m → i.toNat ≤ an.toNat →
      j.toNat ≤ bn.toNat → an.toNat - i.toNat = bn.toNat - j.toNat →
      lrevW.loop1 p k m mode vis d ao an bo bn i j = some (v, m') →
      CoreRef (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (xs.take i.toNat).reverse
        (ys.take j.toNat).reverse) a decBool dn m vis fe M eb [v] m' := by
  have hxl := slice_len hx
  have hyl := slice_len hy
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [lrevW.loop1] at h
  | succ k ih =>
    intro hkn i j m m' a M eb v hS heb hst hia hjb hd h
    have hab : (an = bn) ↔ an.toNat = bn.toNat := ⟨fun h => h ▸ rfl, UInt64.toNat_inj.mp⟩
    have h0i : (i = 0) ↔ i.toNat = 0 := ⟨fun h => h ▸ rfl, fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
    have h0j : (j = 0) ↔ j.toNat = 0 := ⟨fun h => h ▸ rfl, fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
    by_cases hex : i = 0 ∨ j = 0
    · rw [lrevW.loop1.arm1 (hc1 := rfl) (hc2 := hex), Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [h0i, h0j] at hex
      rcases hex with h | h
      · rw [h, List.take_zero, List.reverse_nil, defEqList_nil_left]
        refine coreRef_ret hS (exit_eq _ an bn ?_) (resH_ite (an = bn))
        simp only [List.isEmpty_reverse, List.isEmpty_iff,
          List.eq_nil_iff_length_eq_zero, List.length_take, hyl]
        omega
      · rw [h, List.take_zero, List.reverse_nil, defEqList_nil_right]
        refine coreRef_ret hS (exit_eq _ an bn ?_) (resH_ite (an = bn))
        simp only [List.isEmpty_reverse, List.isEmpty_iff,
          List.eq_nil_iff_length_eq_zero, List.length_take, hxl]
        omega
    have hi0 : i ≠ 0 := fun h => hex (.inl h)
    have hj0 : j ≠ 0 := fun h => hex (.inr h)
    have hi1 := word_pred i hi0
    have hj1 := word_pred j hj0
    have hin : i.toNat ≠ 0 := fun h => hi0 (h0i.mpr h)
    have hjn : j.toNat ≠ 0 := fun h => hj0 (h0j.mpr h)
    cases hc : callW p k "defeq" [mode, vis, d, spW m (ao + (i - 1)), spW m (bo + (j - 1))] m with
    | none => rw [lrevW.loop1.arm2 (hc1 := rfl) (hc2 := hex)] at h; simp only [spW] at hc; rw [hc, lrevW.k_defeq.none] at h; cases h
    | some q =>
    obtain ⟨r, m₁⟩ := q
    rw [lrevW.loop1.arm2 (hc1 := rfl) (hc2 := hex), show rdW (m.arr64 SPN) = spW m from rfl, hc] at h
    obtain ⟨hlx, hgx, hwx⟩ := slice_get hx (i - 1) (by omega)
    obtain ⟨hly, hgy, hwy⟩ := slice_get hy (j - 1) (by omega)
    rw [slice_kept hst hxt (i - 1) (by omega)] at hc
    rw [slice_kept hst hyt (j - 1) (by omega)] at hc
    have h₁ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      ((hk k (by omega)).defeq F _ a dn vis fe M eb mode d _ _ (by omega) (by omega)
        ⟨hS, hmode, heb⟩ hwx hwy) hc
    have ei : i.toNat = (i - 1).toNat + 1 := by omega
    have ej : j.toNat = (j - 1).toNat + 1 := by omega
    rw [ei, ej, take_rev_succ xs _ hlx, take_rev_succ ys _ hly, defEqList_cons, hgx, hgy]
    refine coreRef_bindS h₁ (fun M₁ hS₁ hst₁ => ?_)
    by_cases h0 : r.headD 0 = 0
    · rw [lrevW.k_defeq.arm1 (hc1 := h0), Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [decBool_f h0]
      exact coreRef_ret hS₁ rfl resH_zero
    rw [lrevW.k_defeq.arm2 (hc1 := h0)] at h
    rw [decBool_t h0, ite_eq_left rfl]
    exact ih (by omega) (i - 1) (j - 1) m₁ m' _ M₁ eb v hS₁ heb (hst.trans hst₁) (by omega)
      (by omega) (by omega) h

/-- **`defeq_list_rev` refines `defEqList` on the two reversed slices** (`defeqSpine`'s order). -/
@[refines_part ConRon.Arena.defeqSpine "the reversed argument lists"]
theorem defeqListRev_refines (hp : p.lookup "defeq_list_rev" = some defeqListRevL) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ao an bo bn : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (xs ys : List EIdx)
    (hx : SpineR s₀.mem ao an xs.toArray) (hy : SpineR s₀.mem bo bn ys.toArray)
    (hxt : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (hyt : bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "defeq_list_rev" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat xs.reverse ys.reverse) decBool s₀ a₀
      dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqListRev_spec p hp (n + 1) s₀ mode vis d ao an bo bn)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [lrevW.arm1] at hW
  have hxl := slice_len hx
  have hyl := slice_len hy
  have := lrevW_ok p n hk F hF hn dn vis fe mode d ao an bo bn hs.mode4 s.mem xs ys hx hy hxt hyt
    (n + 1) (Nat.le_refl _) an bn s.mem s'.mem a₀ M eb (r.headD 0) hs.rel hs.eb_mode
    (StackKept.refl _) (Nat.le_refl _) (Nat.le_refl _) (by omega) hW
  rw [← hxl, ← hyl, List.take_length, List.take_length] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨h1, h2, h3.trans (by simp [decBool]), h4⟩

end lrevRef

end L.Arena
