module

public import ConAgua.Arena.DeclCanonSpec
import ConAgua.Arena.SimLib
import ConRon.Bridge.Grind

@[expose] public section

/-!
# Record equalities in L, the relational lemmas (lane `decls3`, helper `decls3-canon`)

The word models of `DeclCanonSpec.lean` (`erSlEqB`, `cvEqB`, …, `ciEqB`) against the twin's
derived equalities: given the two records decode (`decCV`, `decCI`, …) to `x` and `y`, the model
answers `decide (x = y)`. Handles compare as words because `decI` is injective below `2^32`
(`decI_inj`); a `Bool` word is `bool?` (any nonzero word is `true`, `bEqB`); `PropWhen`'s names
decode through `dn`, which must be injective (`DnInj dn`: the store's `denoteN`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`dn` is injective**: two name handles with the same denotation are the same handle (the
name store's hash-consing, `denoteN_inj`). Needed only for `PropWhen`'s names (`pwEqB_ok`). -/
def DnInj (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (x y : NIdx) (n : ConLeche.Name), dn x = some n → dn y = some n → x = y

theorem bool_of_iff {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) : b = decide P := by
  cases b <;> simp_all

section rd
variable {R : Nat → Option Word} {rd : Word → Word}

theorem rdW_off {q k w : Word} (hR : RdOK R rd) (h : R (q.toNat + k.toNat) = some w) :
    rd (q + k) = w :=
  hR.off h rfl

theorem rdW_zero' (hR : RdOK R rd) {q w : Word} (h : R q.toNat = some w) : rd q = w := hR.rd _ _ h

/-- A handle word: read at `q + k`. -/
theorem hdW_ {kk : IdxKind} {q k : Word} {kn : Nat} {x : Idx kk} (hR : RdOK R rd)
    (hk : k.toNat = kn) (h : hd? R (q.toNat + kn) = some x) :
    ∃ w, rd (q + k) = w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  obtain ⟨w, hw, hlt, rfl⟩ := hd?_some h
  exact ⟨w, rdW_off hR (by rw [hk]; exact hw), hlt, rfl⟩

theorem hdW0_ (hR : RdOK R rd) {kk : IdxKind} {q : Word} {x : Idx kk} (h : hd? R q.toNat = some x) :
    ∃ w, rd q = w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  obtain ⟨w, hw, hlt, rfl⟩ := hd?_some h
  exact ⟨w, rdW_zero' hR hw, hlt, rfl⟩

theorem natD {i n : Nat} (h : nat? R i = some n) : ∃ w, R i = some w ∧ n = w.toNat := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem boolD {i : Nat} {b : Bool} (h : bool? R i = some b) : ∃ w, R i = some w ∧ b = (w != 0) := by
  simp only [bool?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem natW_ {q k : Word} {kn n : Nat} (hR : RdOK R rd) (hk : k.toNat = kn)
    (h : nat? R (q.toNat + kn) = some n) : ∃ w, rd (q + k) = w ∧ n = w.toNat := by
  obtain ⟨w, hw, rfl⟩ := natD h
  exact ⟨w, rdW_off hR (by rw [hk]; exact hw), rfl⟩

theorem boolW_ {q k : Word} {kn : Nat} {b : Bool} (hR : RdOK R rd) (hk : k.toNat = kn)
    (h : bool? R (q.toNat + kn) = some b) : ∃ w, rd (q + k) = w ∧ b = (w != 0) := by
  obtain ⟨w, hw, rfl⟩ := boolD h
  exact ⟨w, rdW_off hR (by rw [hk]; exact hw), rfl⟩

theorem boolW0_ (hR : RdOK R rd) {q : Word} {b : Bool} (h : bool? R q.toNat = some b) :
    ∃ w, rd q = w ∧ b = (w != 0) := by
  obtain ⟨w, hw, rfl⟩ := boolD h
  exact ⟨w, rdW_zero' hR hw, rfl⟩

end rd

theorem fld_nat {w w' : Word} : (w.toNat = w'.toNat) ↔ w = w' :=
  ⟨fun h => UInt64.toNat_inj.mp h, fun h => by rw [h]⟩

theorem fld_bool {w w' : Word} : ((w != 0) = (w' != 0)) ↔ bEqB w w' = true := by
  simp [bEqB]

/-! ## Slices -/

theorem hslice_len {kk : IdxKind} {R : Nat → Option Word} {o c : Nat} {xs : List (Idx kk)}
    (h : hslice? R o c = some xs) : xs.length = c := hslice?_lenR h

/-- A slice after its head: empty, or its offset `o + 1` without a wrap. -/
theorem hslice_shift {kk : IdxKind} {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd)
    {o : Word} {c : Nat} {xs : List (Idx kk)} (h : hslice? R (o.toNat + 1) c = some xs) :
    c = 0 ∨ (o + 1).toNat = o.toNat + 1 := by
  rcases c with _ | c
  · exact .inl rfl
  · right
    rw [hslice?_succ] at h
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, -⟩ := h
    obtain ⟨w, hw, -, -⟩ := hd?_some hx
    have := hR.lt _ _ hw
    rw [UInt64.toNat_add]; simp; omega

theorem slEqN_ok {kk : IdxKind} {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) :
    ∀ (c : Nat) (o1 o2 : Word) (xs ys : List (Idx kk)),
    hslice? R o1.toNat c = some xs → hslice? R o2.toNat c = some ys →
    slEqN rd c o1 o2 = decide (xs = ys)
  | 0, o1, o2, xs, ys, h1, h2 => by
    simp [hslice?] at h1 h2; subst h1; subst h2; simp [slEqN]
  | c + 1, o1, o2, xs, ys, h1, h2 => by
    rw [hslice?_succ] at h1 h2
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h1 h2
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h1
    obtain ⟨y, hy, ys', hys, rfl⟩ := h2
    obtain ⟨w1, hw1, hl1, rfl⟩ := hd?_some hx
    obtain ⟨w2, hw2, hl2, rfl⟩ := hd?_some hy
    have ih : slEqN rd c (o1 + 1) (o2 + 1) = decide (xs' = ys') := by
      rcases hslice_shift hR hxs with h0 | e1
      · subst h0
        simp [hslice?] at hxs hys; subst hxs; subst hys; simp [slEqN]
      rcases hslice_shift hR hys with h0 | e2
      · subst h0
        simp [hslice?] at hxs hys; subst hxs; subst hys; simp [slEqN]
      exact slEqN_ok hR c (o1 + 1) (o2 + 1) xs' ys' (by rw [e1]; exact hxs) (by rw [e2]; exact hys)
    have r1 : rd o1 = w1 := hR.rd _ _ hw1
    have r2 : rd o2 = w2 := hR.rd _ _ hw2
    rw [slEqN_succ, ih, r1, r2]
    have hi : ((decI w1 : Idx kk) = decI w2) ↔ w1 = w2 := decI_inj_iff hl1 hl2
    by_cases e : w1 = w2
    · subst e; simp
    · have : ¬ ((decI w1 : Idx kk) = decI w2) := fun h => e (hi.mp h)
      simp [e, this]

theorem erSlEqB_ok {kk : IdxKind} {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd)
    {o1 l1 o2 l2 : Word}
    {xs ys : List (Idx kk)} (h1 : hslice? R o1.toNat l1.toNat = some xs)
    (h2 : hslice? R o2.toNat l2.toNat = some ys) :
    erSlEqB rd o1 l1 o2 l2 = decide (xs = ys) := by
  have n1 := hslice_len h1
  have n2 := hslice_len h2
  by_cases hl : l1 = l2
  · subst hl
    simp only [erSlEqB, beq_self_eq_true, Bool.true_and]
    exact slEqN_ok hR _ o1 o2 xs ys h1 h2
  · have : xs ≠ ys := fun e => hl (UInt64.toNat_inj.mp (by rw [← n1, ← n2, e]))
    have hb : (l1 == l2) = false := by simpa using hl
    simp [erSlEqB, hb, this]

/-- A slice stored in a record: its words `q + i`, `q + i + 1` are `(off, len)`. -/
theorem hlistW_ {kk : IdxKind} {R : Nat → Option Word} {rd : Word → Word} {q k k1 : Word} {kn : Nat}
    {xs : List (Idx kk)} (hR : RdOK R rd) (hk : k.toNat = kn) (hk1 : k1.toNat = kn + 1)
    (h : hlist? R (q.toNat + kn) = some xs) :
    ∃ o l, rd (q + k) = o ∧ rd (q + k1) = l ∧ hslice? R o.toNat l.toNat = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, hs⟩ := h
  obtain ⟨wo, hwo, rfl⟩ := natW_ hR hk ho
  obtain ⟨wl, hwl, rfl⟩ := natW_ (q := q) (k := k1) (kn := kn + 1) hR hk1 hl
  exact ⟨wo, wl, hwo, hwl, hs⟩

/-! ## Constant values, hints, `PropWhen` -/

/-- A decoded constant value's words through the reader. -/
theorem cvFields {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} (h : decCV R q.toNat = some cv) :
    ∃ wn o l wt : Word, rd q = wn ∧ rd (q + 1) = o ∧ rd (q + 2) = l ∧ rd (q + 3) = wt ∧
      wn.toNat < 2 ^ 32 ∧ wt.toNat < 2 ^ 32 ∧ cv.name = decI wn ∧ cv.type = decI wt ∧
      hslice? R o.toNat l.toNat = some cv.levelParams := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, lps, hl, t, ht, e⟩ := h
  have e' := Option.some.inj e
  subst e'
  obtain ⟨wn, e0, hn32, rfl⟩ := hd?_some hn
  obtain ⟨wt, e3, ht32, rfl⟩ := hd?_some ht
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o, ho, c, hc', hs⟩ := hl
  simp only [nat?, Option.map_eq_some_iff] at ho hc'
  obtain ⟨wo, hwo, rfl⟩ := ho
  obtain ⟨wl, hwl, rfl⟩ := hc'
  exact ⟨wn, wo, wl, wt, hR.rd _ _ e0, hR.at 1 rfl hwo, hR.at 2 rfl hwl, hR.at 3 rfl e3,
    hn32, ht32, rfl, rfl, hs⟩

/-- **`cv_eq`'s model is the constant values' equality**, through any reader. -/
theorem cvEqB_ok {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q r : Word}
    {cv cv' : IConstantVal}
    (h1 : decCV R q.toNat = some cv) (h2 : decCV R r.toNat = some cv') :
    cvEqB rd q r = decide (cv = cv') := by
  obtain ⟨wn, o, l, wt, e0, e1, e2, e3, hn, ht, hcn, hct, hs⟩ := cvFields hR h1
  obtain ⟨wn', o', l', wt', e0', e1', e2', e3', hn', ht', hcn', hct', hs'⟩ := cvFields hR h2
  have hl := erSlEqB_ok hR hs hs'
  obtain ⟨cn, cl, ct⟩ := cv
  obtain ⟨cn', cl', ct'⟩ := cv'
  simp only at hcn hct hs hcn' hct' hs'
  subst hcn hct hcn' hct'
  simp only [cvEqB, e0, e0', e1, e1', e2, e2', e3, e3', hl]
  simp only [IConstantVal.mk.injEq, decI_inj_iff hn hn', decI_inj_iff ht ht']
  by_cases h1 : wn = wn' <;> by_cases h2 : cl = cl' <;>
    by_cases h3 : wt = wt' <;> simp [h1, h2, h3]

theorem hintD {R : Nat → Option Word} {q : Nat} {x : ConLeche.ReducibilityHint} (h : decHint R q = some x) :
    ∃ wk, R q = some wk ∧
      ((wk.toNat = 0 ∧ x = .opaque) ∨ (wk.toNat = 1 ∧ x = .abbrev) ∨
       (wk.toNat = 2 ∧ ∃ w, R (q + 1) = some w ∧ x = .regular w.toNat)) := by
  simp only [decHint, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨wk, e, rfl⟩ := natD hk
  refine ⟨wk, e, ?_⟩
  split at h
  · rename_i hh; simp at h; exact .inl ⟨hh, h.symm⟩
  · rename_i hh; simp at h; exact .inr (.inl ⟨hh, h.symm⟩)
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, hy, rfl⟩ := h
    obtain ⟨w, hw, rfl⟩ := natD hy
    exact .inr (.inr ⟨hh, w, hw, rfl⟩)
  · simp at h

theorem hintEqB_ok {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {h g : Word} {x y : ConLeche.ReducibilityHint}
    (hx : decHint R h.toNat = some x) (hy : decHint R g.toNat = some y) :
    hintEqB rd h g = decide (x = y) := by
  obtain ⟨wk, e, hx⟩ := hintD hx
  obtain ⟨wk', e', hy⟩ := hintD hy
  have r1 := rdW_zero' hR e
  have r2 := rdW_zero' hR e'
  simp only [hintEqB, r1, r2]
  have hwk : ∀ w : Word, w.toNat = 0 ↔ w = 0 := fun w => ⟨fun h => UInt64.toNat_inj.mp (by simpa using h), fun h => by simp [h]⟩
  have w2 : ∀ w : Word, w.toNat = 2 → w = 2 := fun w h => UInt64.toNat_inj.mp (by simpa using h)
  have w0 : ∀ w : Word, w.toNat = 0 → w = 0 := fun w h => UInt64.toNat_inj.mp (by simpa using h)
  have w1 : ∀ w : Word, w.toNat = 1 → w = 1 := fun w h => UInt64.toNat_inj.mp (by simpa using h)
  rcases hx with ⟨k0, rfl⟩ | ⟨k0, rfl⟩ | ⟨k0, w, hw, rfl⟩ <;>
  rcases hy with ⟨k1, rfl⟩ | ⟨k1, rfl⟩ | ⟨k1, w', hw', rfl⟩
  · rw [w0 _ k0, w0 _ k1]; simp
  · have : wk ≠ wk' := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  · have : wk ≠ wk' := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  · have : wk ≠ wk' := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  · rw [w1 _ k0, w1 _ k1]; simp
  · have : wk ≠ wk' := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  · have : wk ≠ wk' := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  · have : wk ≠ wk' := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  · rw [w2 _ k0, w2 _ k1]
    have a1 : rd (h + 1) = w := rdW_off hR (k := 1) (by simpa using hw)
    have a2 : rd (g + 1) = w' := rdW_off hR (k := 1) (by simpa using hw')
    simp only [a1, a2]
    by_cases e : w = w'
    · subst e; simp
    · have : ¬ w.toNat = w'.toNat := fun h => e (UInt64.toNat_inj.mp h)
      simp [e, this]

theorem mapM_dn_inj {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) :
    ∀ (ns ms : List NIdx) (l : List ConLeche.Name), ns.mapM dn = some l → ms.mapM dn = some l →
      ns = ms
  | [], [], _, _, _ => rfl
  | [], m :: ms, l, h1, h2 => by
    simp at h1; subst h1
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h2
    obtain ⟨_, _, _, _, e⟩ := h2; simp at e
  | n :: ns, [], l, h1, h2 => by
    simp at h2; subst h2
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
    obtain ⟨_, _, _, _, e⟩ := h1; simp at e
  | n :: ns, m :: ms, l, h1, h2 => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h1 h2
    obtain ⟨y, hy, ys, hys, rfl⟩ := h1
    obtain ⟨y', hy', ys', hys', e⟩ := h2
    obtain ⟨e1, e2⟩ := List.cons.inj e
    subst e1
    have := hdn n m _ hy hy'
    subst this
    rw [mapM_dn_inj hdn ns ms ys hys (by rw [← e2]; exact hys')]

theorem toNat_add_of_get {R : Nat → Option Word} {rd : Word → Word} {q k : Word} {kn : Nat} {w : Word} (hR : RdOK R rd)
    (hk : k.toNat = kn) (h : R (q.toNat + kn) = some w) : (q + k).toNat = q.toNat + kn := by
  have hlt := hR.lt _ _ h
  rw [UInt64.toNat_add, hk]; exact Nat.mod_eq_of_lt (by omega)

theorem erSlAtB_lit {rd : Word → Word} {q r i j : Word} (hj : i + 1 = j) :
    erSlAtB rd q r i = erSlEqB rd (rd (q + i)) (rd (q + j)) (rd (r + i)) (rd (r + j)) := by
  simp only [erSlAtB, ← hj, UInt64.add_assoc]

/-- A slice stored at words `i`, `i + 1` of a record, compared. -/
theorem slAt_ok {kk : IdxKind} {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q r i j : Word} {kn : Nat}
    {xs ys : List (Idx kk)} (hi : i.toNat = kn) (hj : j.toNat = kn + 1) (hij : i + 1 = j)
    (hx : hlist? R (q.toNat + kn) = some xs) (hy : hlist? R (r.toNat + kn) = some ys) :
    erSlAtB rd q r i = decide (xs = ys) := by
  obtain ⟨o, l, e1, e2, hs⟩ := hlistW_ (q := q) (k := i) (k1 := j) (kn := kn) hR hi hj hx
  obtain ⟨o', l', e1', e2', hs'⟩ := hlistW_ (q := r) (k := i) (k1 := j) (kn := kn) hR hi hj hy
  rw [erSlAtB_lit hij, e1, e2, e1', e2']
  exact erSlEqB_ok hR hs hs'

theorem capsEqAll_ok {R : Nat → Option Word} {rd : Word → Word}
    (hR : RdOK R rd) {q r : Word} {x y : IIndCaps}
    (hx : decCaps R q.toNat = some x) (hy : decCaps R r.toNat = some y) :
    capsEqAll rd q r = decide (x = y) := by
  simp only [decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx hy
  obtain ⟨b0, h0, c1, h1, n2, h2, n3, h3, b4, h4, n5, h5, n6, h6, al, h8, n12, h9, ct, h10, ex⟩ := hx
  have ex := Option.some.inj ex; subst ex
  obtain ⟨b0', h0', c1', h1', n2', h2', n3', h3', b4', h4', n5', h5', n6', h6', al', h8', n12',
    h9', ct', h10', ey⟩ := hy
  have ey := Option.some.inj ey; subst ey
  obtain ⟨w0, f0, rfl⟩ := boolW0_ hR h0
  obtain ⟨w0', f0', rfl⟩ := boolW0_ hR h0'
  obtain ⟨w1, f1, l1, rfl⟩ := hdW_ (q := q) (k := 1) (kn := 1) hR rfl h1
  obtain ⟨w1', f1', l1', rfl⟩ := hdW_ (q := r) (k := 1) (kn := 1) hR rfl h1'
  obtain ⟨w2, f2, rfl⟩ := natW_ (q := q) (k := 2) (kn := 2) hR rfl h2
  obtain ⟨w2', f2', rfl⟩ := natW_ (q := r) (k := 2) (kn := 2) hR rfl h2'
  obtain ⟨w3, f3, rfl⟩ := natW_ (q := q) (k := 3) (kn := 3) hR rfl h3
  obtain ⟨w3', f3', rfl⟩ := natW_ (q := r) (k := 3) (kn := 3) hR rfl h3'
  obtain ⟨w4, f4, rfl⟩ := boolW_ (q := q) (k := 4) (kn := 4) hR rfl h4
  obtain ⟨w4', f4', rfl⟩ := boolW_ (q := r) (k := 4) (kn := 4) hR rfl h4'
  obtain ⟨w5, f5, rfl⟩ := natW_ (q := q) (k := 5) (kn := 5) hR rfl h5
  obtain ⟨w5', f5', rfl⟩ := natW_ (q := r) (k := 5) (kn := 5) hR rfl h5'
  obtain ⟨w6, f6, rfl⟩ := natW_ (q := q) (k := 6) (kn := 6) hR rfl h6
  obtain ⟨w6', f6', rfl⟩ := natW_ (q := r) (k := 6) (kn := 6) hR rfl h6'
  obtain ⟨w12, f12, rfl⟩ := natW_ (q := q) (k := 12) (kn := 12) hR rfl h9
  obtain ⟨w12', f12', rfl⟩ := natW_ (q := r) (k := 12) (kn := 12) hR rfl h9'
  have hal := slAt_ok hR (q := q) (r := r) (i := 10) (j := 11) (kn := 10) rfl rfl rfl h8 h8'
  have hct := slAt_ok hR (q := q) (r := r) (i := 13) (j := 14) (kn := 13) rfl rfl rfl h10 h10'
  apply bool_of_iff
  simp only [capsEqAll, capsEqAB, capsEqBB, capsEqCB, f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5,
    f5', f6, f6', f12, f12', hal, hct, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    IIndCaps.mk.injEq, fld_nat, decI_inj_iff l1 l1', fld_bool]
  simp only [and_assoc]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a8, a9, a7, a10⟩
  · rintro ⟨a1, a2, a3, a4, a5, a6, a8, a9, a7, a10⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

/-! ## Recursor rules -/

theorem ruleFields {R : Nat → Option Word} {rd : Word → Word} {q : Word} {x : IRecRule} (hR : RdOK R rd)
    (h : decRule R q.toNat = some x) :
    ∃ w0 w1 w3 w8 : Word, rd q = w0 ∧ rd (q + 1) = w1 ∧
      rd (q + 3) = w3 ∧ rd (q + 8) = w8 ∧
      w0.toNat < 2 ^ 32 ∧ w8.toNat < 2 ^ 32 ∧ x.ctor = decI w0 ∧ x.nfields = w1.toNat ∧
      x.rhs = decI w8 ∧
      ((w3.toNat = 0 ∧ x.fire = .plain) ∨
       (w3.toNat = 1 ∧ ∃ (ls : List LIdx) (es : List EIdx), hlist? R (q.toNat + 4) = some ls ∧
          hlist? R (q.toNat + 6) = some es ∧ x.fire = .nested ls es) ∨
       (w3.toNat = 2 ∧ ∃ (ls : List LIdx), hlist? R (q.toNat + 4) = some ls ∧
          x.fire = .levels ls)) := by
  unfold decRule at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨t, h3, h⟩ := h
  obtain ⟨w3, e3a, rfl⟩ := natD h3
  have e3 : rd (q + 3) = w3 := rdW_off hR (k := 3) (by simpa using e3a)
  split at h
  · rename_i hh
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c, hc, nf, hnf, rhs, hrhs, ex⟩ := h
    subst ex
    obtain ⟨w0, e0, h0, rfl⟩ := hdW0_ hR hc
    obtain ⟨w1, e1, rfl⟩ := natW_ (q := q) (k := 1) (kn := 1) hR rfl hnf
    obtain ⟨w8, e8, h8, rfl⟩ := hdW_ (q := q) (k := 8) (kn := 8) hR rfl hrhs
    exact ⟨w0, w1, w3, w8, e0, e1, e3, e8, h0, h8, rfl, rfl, rfl, .inl ⟨hh, rfl⟩⟩
  · rename_i hh
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ls, hls, es, hes, c, hc, nf, hnf, rhs, hrhs, ex⟩ := h
    subst ex
    obtain ⟨w0, e0, h0, rfl⟩ := hdW0_ hR hc
    obtain ⟨w1, e1, rfl⟩ := natW_ (q := q) (k := 1) (kn := 1) hR rfl hnf
    obtain ⟨w8, e8, h8, rfl⟩ := hdW_ (q := q) (k := 8) (kn := 8) hR rfl hrhs
    exact ⟨w0, w1, w3, w8, e0, e1, e3, e8, h0, h8, rfl, rfl, rfl, .inr (.inl ⟨hh, ls, es, hls, hes, rfl⟩)⟩
  · rename_i hh
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ls, hls, c, hc, nf, hnf, rhs, hrhs, ex⟩ := h
    subst ex
    obtain ⟨w0, e0, h0, rfl⟩ := hdW0_ hR hc
    obtain ⟨w1, e1, rfl⟩ := natW_ (q := q) (k := 1) (kn := 1) hR rfl hnf
    obtain ⟨w8, e8, h8, rfl⟩ := hdW_ (q := q) (k := 8) (kn := 8) hR rfl hrhs
    exact ⟨w0, w1, w3, w8, e0, e1, e3, e8, h0, h8, rfl, rfl, rfl, .inr (.inr ⟨hh, ls, hls, rfl⟩)⟩
  · simp at h

theorem ruleEqButRhsB_ok {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q r : Word} {x y : IRecRule}
    (hx : decRule R q.toNat = some x) (hy : decRule R r.toNat = some y) :
    ruleEqButRhsB rd q r = decide ({ x with rhs := default } = { y with rhs := default }) := by
  obtain ⟨w0, w1, w3, w8, e0, e1, e3, e8, h0, h8, c0, c1, c8, hf⟩ := ruleFields hR hx
  obtain ⟨v0, v1, v3, v8, f0, f1, f3, f8, g0, g8, d0, d1, d8, hg⟩ := ruleFields hR hy
  obtain ⟨c, nf, fire, rhs⟩ := x
  obtain ⟨c', nf', fire', rhs'⟩ := y
  simp only at c0 c1 hf d0 d1 hg
  subst c0 c1 d0 d1
  have wN : ∀ (w : Word) (k : Nat), k < 2 ^ 64 → w.toNat = k → w = UInt64.ofNat k := fun w k hk h =>
    UInt64.toNat_inj.mp (by rw [h]; simp [UInt64.toNat_ofNat_of_lt' hk])
  rcases hf with ⟨k0, rfl⟩ | ⟨k0, ls, es, hls, hes, rfl⟩ | ⟨k0, ls, hls, rfl⟩ <;>
  rcases hg with ⟨k1, rfl⟩ | ⟨k1, ls', es', hls', hes', rfl⟩ | ⟨k1, ls', hls', rfl⟩ <;>
  (have a3 := wN _ _ (by decide) k0; have a3' := wN _ _ (by decide) k1; subst a3 a3')
  all_goals first
    | (simp [ruleEqButRhsB, ruleEqAB, e3, f3]; done)
    | skip
  · apply bool_of_iff
    simp only [ruleEqButRhsB, ruleEqAB, ruleEqBB, e0, e1, e3, f0, f1, f3,
      Bool.and_eq_true, beq_iff_eq, IRecRule.mk.injEq, fld_nat, decI_inj_iff h0 g0]
    simp
  · have s1 := slAt_ok hR (q := q) (r := r) (i := 4) (j := 5) (kn := 4) rfl rfl rfl hls hls'
    have s2 := slAt_ok hR (q := q) (r := r) (i := 6) (j := 7) (kn := 6) rfl rfl rfl hes hes'
    apply bool_of_iff
    simp only [ruleEqButRhsB, ruleEqAB, ruleEqBB, e0, e1, e3, f0, f1, f3,
      s1, s2, Bool.and_eq_true, beq_iff_eq, IRecRule.mk.injEq, fld_nat,
      decI_inj_iff h0 g0, IRecRuleFire.nested.injEq]
    simp [and_assoc]
  · have s1 := slAt_ok hR (q := q) (r := r) (i := 4) (j := 5) (kn := 4) rfl rfl rfl hls hls'
    apply bool_of_iff
    simp only [ruleEqButRhsB, ruleEqAB, ruleEqBB, e0, e1, e3, f0, f1, f3,
      s1, Bool.and_eq_true, beq_iff_eq, IRecRule.mk.injEq, fld_nat,
      decI_inj_iff h0 g0, IRecRuleFire.levels.injEq]
    simp [and_assoc]

theorem decRules_succ (R : Nat → Option Word) (o n : Nat) :
    decRules R o (n + 1) = (do
      let r ← decRule R o
      let rs ← decRules R (o + 11) n
      pure (r :: rs)) := by
  simp only [decRules, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

theorem decRule_ctor {R : Nat → Option Word} {q : Nat} {x : IRecRule} (h : decRule R q = some x) :
    hd? R q = some x.ctor := by
  unfold decRule at h
  rcases hk : nat? R (q + 3) with _ | k
  · simp [hk] at h
  · rcases k with _ | _ | _ | k <;>
      simp only [hk, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
    all_goals first
      | (obtain ⟨c, hc, nf, -, rh, -, rfl⟩ := h; exact hc)
      | (obtain ⟨x1, -, c, hc, nf, -, rh, -, rfl⟩ := h; exact hc)
      | (obtain ⟨x1, -, x2, -, c, hc, nf, -, rh, -, rfl⟩ := h; exact hc)
      | (simp at h)

theorem rule_eq_iff (x y : IRecRule) :
    ({ x with rhs := default } = { y with rhs := default } ∧ x.rhs = y.rhs) ↔ x = y := by
  obtain ⟨c, nf, fire, rhs⟩ := x
  obtain ⟨c', nf', fire', rhs'⟩ := y
  simp only [IRecRule.mk.injEq]
  grind

theorem rulesEqN_ok {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) :
    ∀ (c : Nat) (o1 o2 : Word) (xs ys : List IRecRule),
    decRules R o1.toNat c = some xs → decRules R o2.toNat c = some ys →
    rulesEqN rd c o1 o2 = decide (xs = ys) := by
  intro c
  induction c with
  | zero =>
    intro o1 o2 xs ys h1 h2
    simp [decRules] at h1 h2; subst h1; subst h2; simp [rulesEqN]
  | succ c ih =>
    intro o1 o2 xs ys h1 h2
    rw [decRules_succ] at h1 h2
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h1 h2
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h1
    obtain ⟨y, hy, ys', hys, rfl⟩ := h2
    obtain ⟨-, -, -, w8, -, -, -, e8, -, h8, -, -, c8, -⟩ := ruleFields (q := o1) hR hx
    obtain ⟨-, -, -, v8, -, -, -, f8, -, g8, -, -, d8, -⟩ := ruleFields (q := o2) hR hy
    have hrest : rulesEqN rd c (o1 + 11) (o2 + 11) = decide (xs' = ys') := by
      cases c with
      | zero =>
        simp [decRules] at hxs hys; subst hxs; subst hys; simp [rulesEqN]
      | succ c0 =>
        have g1 := hxs; have g2 := hys
        rw [decRules_succ] at g1 g2
        simp only [bind, Option.bind_eq_some_iff] at g1 g2
        obtain ⟨x1, hx1, -⟩ := g1
        obtain ⟨y1, hy1, -⟩ := g2
        obtain ⟨u, hu, -⟩ := hd?_some (decRule_ctor hx1)
        obtain ⟨u', hu', -⟩ := hd?_some (decRule_ctor hy1)
        have t1 : (o1 + 11).toNat = o1.toNat + 11 := by
          have := hR.lt _ _ hu; rw [UInt64.toNat_add]; simp; omega
        have t2 : (o2 + 11).toNat = o2.toNat + 11 := by
          have := hR.lt _ _ hu'; rw [UInt64.toNat_add]; simp; omega
        exact ih (o1 + 11) (o2 + 11) xs' ys' (by rw [t1]; exact hxs) (by rw [t2]; exact hys)
    rw [rulesEqN_succ, hrest, ruleEqButRhsB_ok hR hx hy, e8, f8]
    apply bool_of_iff
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.cons.injEq]
    rw [← rule_eq_iff x y, c8, d8, decI_inj_iff h8 g8]

theorem rulesEqB_ok {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {o1 l1 o2 l2 : Word}
    {xs ys : List IRecRule} (h1 : decRules R o1.toNat l1.toNat = some xs)
    (h2 : decRules R o2.toNat l2.toNat = some ys) :
    rulesEqB rd o1 l1 o2 l2 = decide (xs = ys) := by
  have n1 := mapM_opt_length _ _ _ h1
  have n2 := mapM_opt_length _ _ _ h2
  simp only [List.length_range] at n1 n2
  by_cases hl : l1 = l2
  · subst hl
    simp only [rulesEqB, beq_self_eq_true, Bool.true_and]
    exact rulesEqN_ok hR _ o1 o2 xs ys h1 h2
  · have : xs ≠ ys := fun e => hl (UInt64.toNat_inj.mp (by rw [← n1, ← n2, e]))
    have hb : (l1 == l2) = false := by simpa using hl
    simp [rulesEqB, hb, this]

/-! ## Constant records -/

theorem cvEqB_ok' {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {p q k : Word} {kn : Nat} (hk : k.toNat = kn)
    {cv cv' : IConstantVal} (hx : decCV R (p.toNat + kn) = some cv)
    (hy : decCV R (q.toNat + kn) = some cv') : cvEqB rd (p + k) (q + k) = decide (cv = cv') := by
  obtain ⟨w, hw, -⟩ := decCV_name hx
  obtain ⟨w', hw', -⟩ := decCV_name hy
  exact cvEqB_ok hR (by rw [toNat_add_of_get hR hk hw]; exact hx)
    (by rw [toNat_add_of_get hR hk hw']; exact hy)

theorem hintEqB_ok' {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {p q k : Word} {kn : Nat} (hk : k.toNat = kn)
    {x y : ConLeche.ReducibilityHint} (hx : decHint R (p.toNat + kn) = some x)
    (hy : decHint R (q.toNat + kn) = some y) : hintEqB rd (p + k) (q + k) = decide (x = y) := by
  obtain ⟨w, hw, -⟩ := hintD hx
  obtain ⟨w', hw', -⟩ := hintD hy
  exact hintEqB_ok hR (by rw [toNat_add_of_get hR hk hw]; exact hx)
    (by rw [toNat_add_of_get hR hk hw']; exact hy)

theorem capsEqAll_ok' {R : Nat → Option Word} {rd : Word → Word}
    (hR : RdOK R rd) {p q k : Word} {kn : Nat} (hk : k.toNat = kn) {x y : IIndCaps}
    (hx : decCaps R (p.toNat + kn) = some x) (hy : decCaps R (q.toNat + kn) = some y) :
    capsEqAll rd (p + k) (q + k) = decide (x = y) := by
  have b1 : ∀ {r : Word} {z : IIndCaps}, decCaps R (r.toNat + kn) = some z →
      ∃ w, R (r.toNat + kn) = some w := by
    intro r z h
    simp only [decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, -⟩ := h
    obtain ⟨w, hw, -⟩ := boolD hb
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := b1 hx
  obtain ⟨w', hw'⟩ := b1 hy
  exact capsEqAll_ok hR (by rw [toNat_add_of_get hR hk hw]; exact hx)
    (by rw [toNat_add_of_get hR hk hw']; exact hy)

theorem ciD {R : Nat → Option Word} {p : Nat} {x : IConstantInfo}
    (h : decCI R p = some x) :
    ∃ wk, R p = some wk ∧
      ((wk.toNat = 0 ∧ ∃ cv, decCV R (p + 1) = some cv ∧ x = .axiomInfo cv) ∨
       (wk.toNat = 1 ∧ ∃ cv v hi, decCV R (p + 1) = some cv ∧ hd? R (p + 5) = some v ∧
          decHint R (p + 6) = some hi ∧ x = .defnInfo cv v hi) ∨
       (wk.toNat = 2 ∧ ∃ cv, decCV R (p + 1) = some cv ∧ x = .thmInfo cv) ∨
       (wk.toNat = 3 ∧ ∃ cv caps, decCV R (p + 1) = some cv ∧ decCaps R (p + 5) = some caps ∧
          x = .indInfo cv caps) ∨
       (wk.toNat = 4 ∧ ∃ cv np nf, decCV R (p + 1) = some cv ∧ nat? R (p + 5) = some np ∧
          nat? R (p + 6) = some nf ∧ x = .ctorInfo cv np nf) ∨
       (wk.toNat = 5 ∧ ∃ cv mi rp o c k rules, decCV R (p + 1) = some cv ∧
          nat? R (p + 5) = some mi ∧ nat? R (p + 6) = some rp ∧
          nat? R (p + 7) = some o ∧ nat? R (p + 8) = some c ∧
          bool? R (p + 9) = some k ∧
          decRules R o c = some rules ∧ x = .recInfo cv mi rp k rules)) := by
  unfold decCI at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨wk, e, rfl⟩ := natD hk
  refine ⟨wk, e, ?_⟩
  split at h
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact .inl ⟨hh, cv, hcv, rfl⟩
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, v, hv, hi, hhi, rfl⟩ := h
    exact .inr (.inl ⟨hh, cv, v, hi, hcv, hv, hhi, rfl⟩)
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact .inr (.inr (.inl ⟨hh, cv, hcv, rfl⟩))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, caps, hc, rfl⟩ := h
    exact .inr (.inr (.inr (.inl ⟨hh, cv, caps, hcv, hc, rfl⟩)))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, np, hnp, nf, hnf, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inl ⟨hh, cv, np, nf, hcv, hnp, hnf, rfl⟩))))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, mi, hmi, rp, hrp, k, hkk, o, ho, c, hc, rules, hr, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inr
      ⟨hh, cv, mi, rp, o, c, k, rules, hcv, hmi, hrp, ho, hc, hkk, hr, rfl⟩))))
  · simp at h

/-- **A decoded record's constant value sits at `p + 1`** (every kind holds it inline, the twin's
pure `toConstantVal`). -/
theorem ciD_cv {R : Nat → Option Word} {p : Nat} {x : IConstantInfo}
    (h : decCI R p = some x) : decCV R (p + 1) = some x.toConstantVal := by
  obtain ⟨_, _, hx⟩ := ciD h
  rcases hx with ⟨-, cv, hcv, rfl⟩ | ⟨-, cv, _, _, hcv, -, -, rfl⟩ | ⟨-, cv, hcv, rfl⟩ |
    ⟨-, cv, _, hcv, -, rfl⟩ | ⟨-, cv, _, _, hcv, -, -, rfl⟩ |
    ⟨-, cv, _, _, _, _, _, _, hcv, -, -, -, -, -, -, rfl⟩ <;> exact hcv

theorem ciEqB_ok {R : Nat → Option Word} {rd : Word → Word}
    (hR : RdOK R rd) {p q : Word} {x y : IConstantInfo}
    (hx : decCI R p.toNat = some x) (hy : decCI R q.toNat = some y) :
    ciEqB rd p q = decide (x = y) := by
  obtain ⟨wk, e, hx⟩ := ciD hx
  obtain ⟨wk', e', hy⟩ := ciD hy
  have r1 := rdW_zero' hR e
  have r2 := rdW_zero' hR e'
  have wl : ∀ (w : Word) (n : Nat) (hn : n < 2 ^ 64), w.toNat = n → w = UInt64.ofNat n := fun w n hn h =>
    UInt64.toNat_inj.mp (by rw [h]; simp [UInt64.toNat_ofNat_of_lt' hn])
  rcases hx with ⟨k0, cv, hcv, rfl⟩ | ⟨k0, cv, v, hi, hcv, hv, hhi, rfl⟩ | ⟨k0, cv, hcv, rfl⟩ |
      ⟨k0, cv, caps, hcv, hcaps, rfl⟩ | ⟨k0, cv, np, nf, hcv, hnp, hnf, rfl⟩ |
      ⟨k0, cv, mi, rp, o, c, k, rules, hcv, hmi, hrp, ho, hc, hk, hr, rfl⟩ <;>
  rcases hy with ⟨k1, cv', hcv', rfl⟩ | ⟨k1, cv', v', hi', hcv', hv', hhi', rfl⟩ | ⟨k1, cv', hcv', rfl⟩ |
      ⟨k1, cv', caps', hcv', hcaps', rfl⟩ | ⟨k1, cv', np', nf', hcv', hnp', hnf', rfl⟩ |
      ⟨k1, cv', mi', rp', o', c', k', rules', hcv', hmi', hrp', ho', hc', hk', hr', rfl⟩
  all_goals first
    | (have hne : wk ≠ wk' := fun h => by have := congrArg UInt64.toNat h; omega
       simp [ciEqB, r1, r2, hne]; done)
    | skip
  · have a1 : wk = 0 := wl wk 0 (by decide) k0
    have a2 : wk' = 0 := wl wk' 0 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hR (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB]
    simp [c1]
  · have a1 : wk = 1 := wl wk 1 (by decide) k0
    have a2 : wk' = 1 := wl wk' 1 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hR (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    obtain ⟨w5, f5, u5, rfl⟩ := hdW_ (q := p) (k := 5) (kn := 5) hR rfl hv
    obtain ⟨v5, g5, t5, rfl⟩ := hdW_ (q := q) (k := 5) (kn := 5) hR rfl hv'
    have c2 := hintEqB_ok' hR (p := p) (q := q) (k := 6) (kn := 6) rfl hhi hhi'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB, f5, g5, c1, c2]
    simp [decI_inj_iff u5 t5]
  · have a1 : wk = 2 := wl wk 2 (by decide) k0
    have a2 : wk' = 2 := wl wk' 2 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hR (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB]
    simp [c1]
  · have a1 : wk = 3 := wl wk 3 (by decide) k0
    have a2 : wk' = 3 := wl wk' 3 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hR (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    have c2 := capsEqAll_ok' hR (p := p) (q := q) (k := 5) (kn := 5) rfl hcaps hcaps'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB, c1, c2]
    simp
  · have a1 : wk = 4 := wl wk 4 (by decide) k0
    have a2 : wk' = 4 := wl wk' 4 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hR (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    obtain ⟨w5, f5, rfl⟩ := natW_ (q := p) (k := 5) (kn := 5) hR rfl hnp
    obtain ⟨v5, g5, rfl⟩ := natW_ (q := q) (k := 5) (kn := 5) hR rfl hnp'
    obtain ⟨w6, f6, rfl⟩ := natW_ (q := p) (k := 6) (kn := 6) hR rfl hnf
    obtain ⟨v6, g6, rfl⟩ := natW_ (q := q) (k := 6) (kn := 6) hR rfl hnf'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB, f5, g5, f6, g6, c1]
    simp [fld_nat]
  · have a1 : wk = 5 := wl wk 5 (by decide) k0
    have a2 : wk' = 5 := wl wk' 5 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hR (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    obtain ⟨w5, f5, rfl⟩ := natW_ (q := p) (k := 5) (kn := 5) hR rfl hmi
    obtain ⟨v5, g5, rfl⟩ := natW_ (q := q) (k := 5) (kn := 5) hR rfl hmi'
    obtain ⟨w6, f6, rfl⟩ := natW_ (q := p) (k := 6) (kn := 6) hR rfl hrp
    obtain ⟨v6, g6, rfl⟩ := natW_ (q := q) (k := 6) (kn := 6) hR rfl hrp'
    obtain ⟨w7, f7, rfl⟩ := natW_ (q := p) (k := 7) (kn := 7) hR rfl ho
    obtain ⟨v7, g7, rfl⟩ := natW_ (q := q) (k := 7) (kn := 7) hR rfl ho'
    obtain ⟨w8, f8, rfl⟩ := natW_ (q := p) (k := 8) (kn := 8) hR rfl hc
    obtain ⟨v8, g8, rfl⟩ := natW_ (q := q) (k := 8) (kn := 8) hR rfl hc'
    obtain ⟨w9, f9, rfl⟩ := boolW_ (q := p) (k := 9) (kn := 9) hR rfl hk
    obtain ⟨v9, g9, rfl⟩ := boolW_ (q := q) (k := 9) (kn := 9) hR rfl hk'
    have c2 := rulesEqB_ok hR hr hr'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB, f5, g5, f6, g6, f7, g7, f8, g8, f9, g9, c1, c2]
    simp [fld_nat, fld_bool, and_assoc]
    intros; exact And.comm

end L.Ind

