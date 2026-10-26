import ConAgua.Arena.DeclCanonSpec
import ConAgua.Arena.PinsNatOp

/-!
# Record equalities in L, the relational lemmas (lane `decls3`, helper `decls3-canon`)

The word models of `DeclCanonSpec.lean` (`erSlEqB`, `cvEqB`, …, `ciEqB`) against the twin's
derived equalities: given the two records decode (`decCV`, `decCI`, …) to `x` and `y`, the model
answers `decide (x = y)`. Handles compare as words because `decI` is injective below `2^32`
(`decI_inj`); a `Bool` word is `bool?` (any nonzero word is `true`, `bEqB`); `PropWhen`'s names
decode through `dn`, which must be injective (`DnInj dn`: the store's `denoteN`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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
variable {a : Array Word}

theorem rdW_off {q k w : Word} (hsz : a.size < 2 ^ 64) (h : a[q.toNat + k.toNat]? = some w) :
    rdW a (q + k) = w := by
  have hlt : q.toNat + k.toNat < a.size := (Array.getElem?_eq_some_iff.mp h).1
  have : (q + k).toNat = q.toNat + k.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  simp [rdW, this, h]

theorem rdW_zero' {q w : Word} (h : a[q.toNat]? = some w) : rdW a q = w := by simp [rdW, h]

theorem toNat_succ_lt {o : Word} (hsz : a.size < 2 ^ 64) {w : Word} (h : a[o.toNat]? = some w) :
    (o + 1).toNat = o.toNat + 1 := by
  have hlt : o.toNat < a.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [UInt64.toNat_add]; simp; omega

/-- A handle word: read at `q + k`. -/
theorem hdW_ {kk : IdxKind} {q k : Word} {kn : Nat} {x : Idx kk} (hsz : a.size < 2 ^ 64)
    (hk : k.toNat = kn) (h : hd? a (q.toNat + kn) = some x) :
    ∃ w, rdW a (q + k) = w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  obtain ⟨w, hw, hlt, rfl⟩ := hd?_some h
  exact ⟨w, rdW_off hsz (by rw [hk]; exact hw), hlt, rfl⟩

theorem hdW0_ {kk : IdxKind} {q : Word} {x : Idx kk} (h : hd? a q.toNat = some x) :
    ∃ w, rdW a q = w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  obtain ⟨w, hw, hlt, rfl⟩ := hd?_some h
  exact ⟨w, rdW_zero' hw, hlt, rfl⟩

theorem natD {i n : Nat} (h : nat? a i = some n) : ∃ w, a[i]? = some w ∧ n = w.toNat := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem boolD {i : Nat} {b : Bool} (h : bool? a i = some b) : ∃ w, a[i]? = some w ∧ b = (w != 0) := by
  simp only [bool?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem natW_ {q k : Word} {kn n : Nat} (hsz : a.size < 2 ^ 64) (hk : k.toNat = kn)
    (h : nat? a (q.toNat + kn) = some n) : ∃ w, rdW a (q + k) = w ∧ n = w.toNat := by
  obtain ⟨w, hw, rfl⟩ := natD h
  exact ⟨w, rdW_off hsz (by rw [hk]; exact hw), rfl⟩

theorem boolW_ {q k : Word} {kn : Nat} {b : Bool} (hsz : a.size < 2 ^ 64) (hk : k.toNat = kn)
    (h : bool? a (q.toNat + kn) = some b) : ∃ w, rdW a (q + k) = w ∧ b = (w != 0) := by
  obtain ⟨w, hw, rfl⟩ := boolD h
  exact ⟨w, rdW_off hsz (by rw [hk]; exact hw), rfl⟩

theorem boolW0_ {q : Word} {b : Bool} (h : bool? a q.toNat = some b) :
    ∃ w, rdW a q = w ∧ b = (w != 0) := by
  obtain ⟨w, hw, rfl⟩ := boolD h
  exact ⟨w, rdW_zero' hw, rfl⟩

end rd

theorem fld_nat {w w' : Word} : (w.toNat = w'.toNat) ↔ w = w' :=
  ⟨fun h => UInt64.toNat_inj.mp h, fun h => by rw [h]⟩

theorem fld_hd {kk : IdxKind} {w w' : Word} (hw : w.toNat < 2 ^ 32) (hw' : w'.toNat < 2 ^ 32) :
    ((decI w : Idx kk) = decI w') ↔ w = w' :=
  ⟨decI_inj hw hw', fun h => by rw [h]⟩

theorem fld_bool {w w' : Word} : ((w != 0) = (w' != 0)) ↔ bEqB w w' = true := by
  simp [bEqB]

/-! ## Slices -/

theorem hslice_len {kk : IdxKind} {a : Array Word} {o c : Nat} {xs : List (Idx kk)}
    (h : hslice? a o c = some xs) : xs.length = c := by
  have := mapM_opt_length _ _ _ h
  simpa using this

theorem slEqN_ok {kk : IdxKind} {a : Array Word} (hsz : a.size < 2 ^ 64) :
    ∀ (c : Nat) (o1 o2 : Word) (xs ys : List (Idx kk)),
    hslice? a o1.toNat c = some xs → hslice? a o2.toNat c = some ys →
    slEqN a c o1 o2 = decide (xs = ys)
  | 0, o1, o2, xs, ys, h1, h2 => by
    simp [hslice?] at h1 h2; subst h1; subst h2; simp [slEqN]
  | c + 1, o1, o2, xs, ys, h1, h2 => by
    rw [hslice?_succ] at h1 h2
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h1 h2
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h1
    obtain ⟨y, hy, ys', hys, rfl⟩ := h2
    obtain ⟨w1, hw1, hl1, rfl⟩ := hd?_some hx
    obtain ⟨w2, hw2, hl2, rfl⟩ := hd?_some hy
    have e1 := toNat_succ_lt hsz hw1
    have e2 := toNat_succ_lt hsz hw2
    have ih := slEqN_ok hsz c (o1 + 1) (o2 + 1) xs' ys' (by rw [e1]; exact hxs) (by rw [e2]; exact hys)
    rw [slEqN_succ, ih, rdW_zero' hw1, rdW_zero' hw2]
    have hi : ((decI w1 : Idx kk) = decI w2) ↔ w1 = w2 := fld_hd hl1 hl2
    by_cases e : w1 = w2
    · subst e; simp
    · have : ¬ ((decI w1 : Idx kk) = decI w2) := fun h => e (hi.mp h)
      simp [e, this]

theorem erSlEqB_ok {kk : IdxKind} {a : Array Word} (hsz : a.size < 2 ^ 64) {o1 l1 o2 l2 : Word}
    {xs ys : List (Idx kk)} (h1 : hslice? a o1.toNat l1.toNat = some xs)
    (h2 : hslice? a o2.toNat l2.toNat = some ys) :
    erSlEqB a o1 l1 o2 l2 = decide (xs = ys) := by
  have n1 := hslice_len h1
  have n2 := hslice_len h2
  by_cases hl : l1 = l2
  · subst hl
    simp only [erSlEqB, beq_self_eq_true, Bool.true_and]
    exact slEqN_ok hsz _ o1 o2 xs ys h1 h2
  · have : xs ≠ ys := fun e => hl (UInt64.toNat_inj.mp (by rw [← n1, ← n2, e]))
    have hb : (l1 == l2) = false := by simpa using hl
    simp [erSlEqB, hb, this]

/-- A slice stored in a record: its words `q + i`, `q + i + 1` are `(off, len)`. -/
theorem hlistW_ {kk : IdxKind} {a : Array Word} {q k k1 : Word} {kn : Nat} {xs : List (Idx kk)}
    (hsz : a.size < 2 ^ 64) (hk : k.toNat = kn) (hk1 : k1.toNat = kn + 1)
    (h : hlist? a (q.toNat + kn) = some xs) :
    ∃ o l, rdW a (q + k) = o ∧ rdW a (q + k1) = l ∧ hslice? a o.toNat l.toNat = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, hs⟩ := h
  obtain ⟨wo, hwo, rfl⟩ := natW_ hsz hk ho
  obtain ⟨wl, hwl, rfl⟩ := natW_ (q := q) (k := k1) (kn := kn + 1) hsz hk1 hl
  exact ⟨wo, wl, hwo, hwl, hs⟩

/-! ## Constant values, hints, `PropWhen` -/

theorem cvFields {a : Array Word} {q : Word} {cv : IConstantVal} (hsz : a.size < 2 ^ 64)
    (h : decCV a q.toNat = some cv) :
    ∃ wn o l wt : Word, rdW a q = wn ∧ rdW a (q + 1) = o ∧ rdW a (q + 2) = l ∧ rdW a (q + 3) = wt ∧
      wn.toNat < 2 ^ 32 ∧ wt.toNat < 2 ^ 32 ∧ cv.name = decI wn ∧ cv.type = decI wt ∧
      hslice? a o.toNat l.toNat = some cv.levelParams := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, lps, hl, t, ht, e⟩ := h
  have e' := Option.some.inj e
  subst e'
  obtain ⟨wn, e0, hn32, rfl⟩ := hdW0_ hn
  obtain ⟨o, l, e1, e2, hs⟩ := hlistW_ (q := q) (k := 1) (k1 := 2) (kn := 1) hsz rfl rfl hl
  obtain ⟨wt, e3, ht32, rfl⟩ := hdW_ (q := q) (k := 3) (kn := 3) hsz rfl ht
  exact ⟨wn, o, l, wt, e0, e1, e2, e3, hn32, ht32, rfl, rfl, hs⟩

theorem cvEqB_ok {a : Array Word} (hsz : a.size < 2 ^ 64) {q r : Word} {cv cv' : IConstantVal}
    (h1 : decCV a q.toNat = some cv) (h2 : decCV a r.toNat = some cv') :
    cvEqB a q r = decide (cv = cv') := by
  obtain ⟨wn, o, l, wt, e0, e1, e2, e3, hn, ht, hcn, hct, hs⟩ := cvFields hsz h1
  obtain ⟨wn', o', l', wt', e0', e1', e2', e3', hn', ht', hcn', hct', hs'⟩ := cvFields hsz h2
  have hl := erSlEqB_ok hsz hs hs'
  obtain ⟨cn, cl, ct⟩ := cv
  obtain ⟨cn', cl', ct'⟩ := cv'
  simp only at hcn hct hs hcn' hct' hs'
  subst hcn hct hcn' hct'
  simp only [cvEqB, e0, e0', e1, e1', e2, e2', e3, e3', hl]
  simp only [IConstantVal.mk.injEq, fld_hd hn hn', fld_hd ht ht']
  by_cases h1 : wn = wn' <;> by_cases h2 : cl = cl' <;>
    by_cases h3 : wt = wt' <;> simp [h1, h2, h3]

theorem hintD {a : Array Word} {q : Nat} {x : ConLeche.ReducibilityHint} (h : decHint a q = some x) :
    ∃ wk, a[q]? = some wk ∧
      ((wk.toNat = 0 ∧ x = .opaque) ∨ (wk.toNat = 1 ∧ x = .abbrev) ∨
       (wk.toNat = 2 ∧ ∃ w, a[q + 1]? = some w ∧ x = .regular w.toNat)) := by
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

theorem hintEqB_ok {a : Array Word} (hsz : a.size < 2 ^ 64) {h g : Word} {x y : ConLeche.ReducibilityHint}
    (hx : decHint a h.toNat = some x) (hy : decHint a g.toNat = some y) :
    hintEqB a h g = decide (x = y) := by
  obtain ⟨wk, e, hx⟩ := hintD hx
  obtain ⟨wk', e', hy⟩ := hintD hy
  have r1 := rdW_zero' e
  have r2 := rdW_zero' e'
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
    have a1 : rdW a (h + 1) = w := rdW_off hsz (k := 1) (by simpa using hw)
    have a2 : rdW a (g + 1) = w' := rdW_off hsz (k := 1) (by simpa using hw')
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

theorem pwD {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat} {x : ConLeche.PropWhen}
    (h : decPW a dn q = some x) :
    ∃ wk, a[q]? = some wk ∧ ((wk.toNat = 0 ∧ x = .never) ∨
      (wk.toNat = 1 ∧ ∃ (ns : List NIdx) (names : List ConLeche.Name), hlist? a (q + 1) = some ns ∧ ns.mapM dn = some names ∧
        x = .ifAllZero names)) := by
  simp only [decPW, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨wk, e, rfl⟩ := natD hk
  refine ⟨wk, e, ?_⟩
  split at h
  · rename_i hh; simp at h; exact .inl ⟨hh, h.symm⟩
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨ns, hns, names, hnames, rfl⟩ := h
    exact .inr ⟨hh, ns, names, hns, hnames, rfl⟩
  · simp at h

theorem pwEqB_ok {a : Array Word} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hsz : a.size < 2 ^ 64) {q r : Word} {x y : ConLeche.PropWhen}
    (hx : decPW a dn q.toNat = some x) (hy : decPW a dn r.toNat = some y) :
    pwEqB a q r = decide (x = y) := by
  obtain ⟨wk, e, hx⟩ := pwD hx
  obtain ⟨wk', e', hy⟩ := pwD hy
  have r1 := rdW_zero' e
  have r2 := rdW_zero' e'
  simp only [pwEqB, r1, r2]
  have w0 : ∀ w : Word, w.toNat = 0 → w = 0 := fun w h => UInt64.toNat_inj.mp (by simpa using h)
  have w1 : ∀ w : Word, w.toNat = 1 → w = 1 := fun w h => UInt64.toNat_inj.mp (by simpa using h)
  rcases hx with ⟨k0, rfl⟩ | ⟨k0, ns, names, hns, hnames, rfl⟩ <;>
  rcases hy with ⟨k1, rfl⟩ | ⟨k1, ms, names', hms, hnames', rfl⟩
  · rw [w0 _ k0, w0 _ k1]; simp
  · have : wk ≠ wk' := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  · have : wk ≠ wk' := fun e => by have := congrArg UInt64.toNat e; omega
    simp [this]
  · rw [w1 _ k0, w1 _ k1]
    obtain ⟨o, l, e1, e2, hs⟩ := hlistW_ (q := q) (k := 1) (k1 := 2) (kn := 1) hsz rfl rfl hns
    obtain ⟨o', l', e1', e2', hs'⟩ := hlistW_ (q := r) (k := 1) (k1 := 2) (kn := 1) hsz rfl rfl hms
    have hl := erSlEqB_ok hsz hs hs'
    simp only [e1, e2, e1', e2', hl]
    have hiff : ns = ms ↔ names = names' := by
      constructor
      · rintro rfl; rw [hnames] at hnames'; exact Option.some.inj hnames'
      · rintro rfl; exact mapM_dn_inj hdn ns ms _ hnames hnames'
    have hiff2 : decide (ns = ms) = decide (ConLeche.PropWhen.ifAllZero names = .ifAllZero names') := by
      simp [hiff]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    exact hiff2

theorem toNat_add_of_get {a : Array Word} {q k : Word} {kn : Nat} {w : Word} (hsz : a.size < 2 ^ 64)
    (hk : k.toNat = kn) (h : a[q.toNat + kn]? = some w) : (q + k).toNat = q.toNat + kn := by
  have hlt : q.toNat + kn < a.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [UInt64.toNat_add, hk]; exact Nat.mod_eq_of_lt (by omega)

theorem pwEqB_ok' {a : Array Word} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hsz : a.size < 2 ^ 64) {q r k : Word} {kn : Nat} (hk : k.toNat = kn) {x y : ConLeche.PropWhen}
    (hx : decPW a dn (q.toNat + kn) = some x) (hy : decPW a dn (r.toNat + kn) = some y) :
    pwEqB a (q + k) (r + k) = decide (x = y) := by
  obtain ⟨wk, e, -⟩ := pwD hx
  obtain ⟨wk', e', -⟩ := pwD hy
  exact pwEqB_ok hdn hsz (by rw [toNat_add_of_get hsz hk e]; exact hx)
    (by rw [toNat_add_of_get hsz hk e']; exact hy)

theorem erSlAtB_lit {a : Array Word} {q r i j : Word} (hj : i + 1 = j) :
    erSlAtB a q r i = erSlEqB a (rdW a (q + i)) (rdW a (q + j)) (rdW a (r + i)) (rdW a (r + j)) := by
  simp only [erSlAtB, ← hj, UInt64.add_assoc]

/-- A slice stored at words `i`, `i + 1` of a record, compared. -/
theorem slAt_ok {kk : IdxKind} {a : Array Word} (hsz : a.size < 2 ^ 64) {q r i j : Word} {kn : Nat}
    {xs ys : List (Idx kk)} (hi : i.toNat = kn) (hj : j.toNat = kn + 1) (hij : i + 1 = j)
    (hx : hlist? a (q.toNat + kn) = some xs) (hy : hlist? a (r.toNat + kn) = some ys) :
    erSlAtB a q r i = decide (xs = ys) := by
  obtain ⟨o, l, e1, e2, hs⟩ := hlistW_ (q := q) (k := i) (k1 := j) (kn := kn) hsz hi hj hx
  obtain ⟨o', l', e1', e2', hs'⟩ := hlistW_ (q := r) (k := i) (k1 := j) (kn := kn) hsz hi hj hy
  rw [erSlAtB_lit hij, e1, e2, e1', e2']
  exact erSlEqB_ok hsz hs hs'

theorem capsEqAll_ok {a : Array Word} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hsz : a.size < 2 ^ 64) {q r : Word} {x y : IIndCaps}
    (hx : decCaps a dn q.toNat = some x) (hy : decCaps a dn r.toNat = some y) :
    capsEqAll a q r = decide (x = y) := by
  simp only [decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx hy
  obtain ⟨b0, h0, c1, h1, n2, h2, n3, h3, b4, h4, n5, h5, b6, h6, pw, h7, al, h8, n12, h9, ct, h10, ex⟩ := hx
  have ex := Option.some.inj ex; subst ex
  obtain ⟨b0', h0', c1', h1', n2', h2', n3', h3', b4', h4', n5', h5', b6', h6', pw', h7', al', h8', n12',
    h9', ct', h10', ey⟩ := hy
  have ey := Option.some.inj ey; subst ey
  obtain ⟨w0, f0, rfl⟩ := boolW0_ h0
  obtain ⟨w0', f0', rfl⟩ := boolW0_ h0'
  obtain ⟨w1, f1, l1, rfl⟩ := hdW_ (q := q) (k := 1) (kn := 1) hsz rfl h1
  obtain ⟨w1', f1', l1', rfl⟩ := hdW_ (q := r) (k := 1) (kn := 1) hsz rfl h1'
  obtain ⟨w2, f2, rfl⟩ := natW_ (q := q) (k := 2) (kn := 2) hsz rfl h2
  obtain ⟨w2', f2', rfl⟩ := natW_ (q := r) (k := 2) (kn := 2) hsz rfl h2'
  obtain ⟨w3, f3, rfl⟩ := natW_ (q := q) (k := 3) (kn := 3) hsz rfl h3
  obtain ⟨w3', f3', rfl⟩ := natW_ (q := r) (k := 3) (kn := 3) hsz rfl h3'
  obtain ⟨w4, f4, rfl⟩ := boolW_ (q := q) (k := 4) (kn := 4) hsz rfl h4
  obtain ⟨w4', f4', rfl⟩ := boolW_ (q := r) (k := 4) (kn := 4) hsz rfl h4'
  obtain ⟨w5, f5, rfl⟩ := natW_ (q := q) (k := 5) (kn := 5) hsz rfl h5
  obtain ⟨w5', f5', rfl⟩ := natW_ (q := r) (k := 5) (kn := 5) hsz rfl h5'
  obtain ⟨w6, f6, rfl⟩ := boolW_ (q := q) (k := 6) (kn := 6) hsz rfl h6
  obtain ⟨w6', f6', rfl⟩ := boolW_ (q := r) (k := 6) (kn := 6) hsz rfl h6'
  obtain ⟨w12, f12, rfl⟩ := natW_ (q := q) (k := 12) (kn := 12) hsz rfl h9
  obtain ⟨w12', f12', rfl⟩ := natW_ (q := r) (k := 12) (kn := 12) hsz rfl h9'
  have hpw := pwEqB_ok' hdn hsz (q := q) (r := r) (k := 7) (kn := 7) rfl h7 h7'
  have hal := slAt_ok hsz (q := q) (r := r) (i := 10) (j := 11) (kn := 10) rfl rfl rfl h8 h8'
  have hct := slAt_ok hsz (q := q) (r := r) (i := 13) (j := 14) (kn := 13) rfl rfl rfl h10 h10'
  apply bool_of_iff
  simp only [capsEqAll, capsEqAB, capsEqBB, capsEqCB, f0, f0', f1, f1', f2, f2', f3, f3', f4, f4', f5,
    f5', f6, f6', f12, f12', hpw, hal, hct, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    IIndCaps.mk.injEq, fld_nat, fld_hd l1 l1', fld_bool]
  simp only [and_assoc]

/-! ## Recursor rules -/

theorem ruleFields {a : Array Word} {q : Word} {x : IRecRule} (hsz : a.size < 2 ^ 64)
    (h : decRule a q.toNat = some x) :
    ∃ w0 w1 w2 w3 w8 w9 w10 : Word, rdW a q = w0 ∧ rdW a (q + 1) = w1 ∧ rdW a (q + 2) = w2 ∧
      rdW a (q + 3) = w3 ∧ rdW a (q + 8) = w8 ∧ rdW a (q + 9) = w9 ∧ rdW a (q + 10) = w10 ∧
      w0.toNat < 2 ^ 32 ∧ w8.toNat < 2 ^ 32 ∧ x.ctor = decI w0 ∧ x.nfields = w1.toNat ∧
      x.ctorParams = w2.toNat ∧ x.rhs = decI w8 ∧ x.k = (w9 != 0) ∧ x.eta = (w10 != 0) ∧
      ((w3.toNat = 0 ∧ x.fire = .plain) ∨
       (w3.toNat = 1 ∧ ∃ (ls : List LIdx) (es : List EIdx), hlist? a (q.toNat + 4) = some ls ∧
          hlist? a (q.toNat + 6) = some es ∧ x.fire = .nested ls es)) ∧
      q.toNat + 11 < 2 ^ 64 := by
  unfold decRule at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨t, h3, h⟩ := h
  obtain ⟨w3, e3a, rfl⟩ := natD h3
  have e3 : rdW a (q + 3) = w3 := rdW_off hsz (k := 3) (by simpa using e3a)
  split at h
  · rename_i hh
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c, hc, nf, hnf, cp, hcp, rhs, hrhs, k, hk, eta, he, ex⟩ := h
    subst ex
    obtain ⟨w0, e0, h0, rfl⟩ := hdW0_ hc
    obtain ⟨w1, e1, rfl⟩ := natW_ (q := q) (k := 1) (kn := 1) hsz rfl hnf
    obtain ⟨w2, e2, rfl⟩ := natW_ (q := q) (k := 2) (kn := 2) hsz rfl hcp
    obtain ⟨w8, e8, h8, rfl⟩ := hdW_ (q := q) (k := 8) (kn := 8) hsz rfl hrhs
    obtain ⟨w9, e9, rfl⟩ := boolW_ (q := q) (k := 9) (kn := 9) hsz rfl hk
    obtain ⟨w10, e10a, rfl⟩ := boolD he
    have e10 : rdW a (q + 10) = w10 := rdW_off hsz (k := 10) (by simpa using e10a)
    exact ⟨w0, w1, w2, w3, w8, w9, w10, e0, e1, e2, e3, e8, e9, e10, h0, h8, rfl, rfl, rfl, rfl,
      rfl, rfl, .inl ⟨hh, rfl⟩, by have := (Array.getElem?_eq_some_iff.mp e10a).1; omega⟩
  · rename_i hh
    simp only [Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ls, hls, es, hes, c, hc, nf, hnf, cp, hcp, rhs, hrhs, k, hk, eta, he, ex⟩ := h
    subst ex
    obtain ⟨w0, e0, h0, rfl⟩ := hdW0_ hc
    obtain ⟨w1, e1, rfl⟩ := natW_ (q := q) (k := 1) (kn := 1) hsz rfl hnf
    obtain ⟨w2, e2, rfl⟩ := natW_ (q := q) (k := 2) (kn := 2) hsz rfl hcp
    obtain ⟨w8, e8, h8, rfl⟩ := hdW_ (q := q) (k := 8) (kn := 8) hsz rfl hrhs
    obtain ⟨w9, e9, rfl⟩ := boolW_ (q := q) (k := 9) (kn := 9) hsz rfl hk
    obtain ⟨w10, e10a, rfl⟩ := boolD he
    have e10 : rdW a (q + 10) = w10 := rdW_off hsz (k := 10) (by simpa using e10a)
    exact ⟨w0, w1, w2, w3, w8, w9, w10, e0, e1, e2, e3, e8, e9, e10, h0, h8, rfl, rfl, rfl, rfl,
      rfl, rfl, .inr ⟨hh, ls, es, hls, hes, rfl⟩, by have := (Array.getElem?_eq_some_iff.mp e10a).1; omega⟩
  · simp at h

theorem ruleEqButRhsB_ok {a : Array Word} (hsz : a.size < 2 ^ 64) {q r : Word} {x y : IRecRule}
    (hx : decRule a q.toNat = some x) (hy : decRule a r.toNat = some y) :
    ruleEqButRhsB a q r = decide ({ x with rhs := default } = { y with rhs := default }) := by
  obtain ⟨w0, w1, w2, w3, w8, w9, w10, e0, e1, e2, e3, e8, e9, e10, h0, h8, c0, c1, c2, c8, c9, c10, hf, hb⟩ :=
    ruleFields hsz hx
  obtain ⟨v0, v1, v2, v3, v8, v9, v10, f0, f1, f2, f3, f8, f9, f10, g0, g8, d0, d1, d2, d8, d9, d10, hg, hb'⟩ :=
    ruleFields hsz hy
  obtain ⟨c, nf, cp, fire, rhs, k, eta⟩ := x
  obtain ⟨c', nf', cp', fire', rhs', k', eta'⟩ := y
  simp only at c0 c1 c2 c9 c10 hf d0 d1 d2 d9 d10 hg
  subst c0 c1 c2 c9 c10 d0 d1 d2 d9 d10
  have w0' : ∀ w : Word, w.toNat = 0 → w = 0 := fun w h => UInt64.toNat_inj.mp (by simpa using h)
  have w1' : ∀ w : Word, w.toNat = 1 → w = 1 := fun w h => UInt64.toNat_inj.mp (by simpa using h)
  rcases hf with ⟨k0, rfl⟩ | ⟨k0, ls, es, hls, hes, rfl⟩ <;>
  rcases hg with ⟨k1, rfl⟩ | ⟨k1, ls', es', hls', hes', rfl⟩
  · have a3 := w0' _ k0
    have a3' := w0' _ k1
    subst a3 a3'
    apply bool_of_iff
    simp only [ruleEqButRhsB, ruleEqAB, ruleEqBB, e0, e1, e2, e3, f0, f1, f2, f3, e9, e10, f9, f10,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, IRecRule.mk.injEq, fld_nat, fld_hd h0 g0, fld_bool]
    simp [and_assoc]
  · have a3 := w0' _ k0
    have a3' := w1' _ k1
    subst a3 a3'
    simp [ruleEqButRhsB, ruleEqAB, e3, f3]
  · have a3 := w1' _ k0
    have a3' := w0' _ k1
    subst a3 a3'
    simp [ruleEqButRhsB, ruleEqAB, e3, f3]
  · have a3 := w1' _ k0
    have a3' := w1' _ k1
    subst a3 a3'
    have s1 := slAt_ok hsz (q := q) (r := r) (i := 4) (j := 5) (kn := 4) rfl rfl rfl hls hls'
    have s2 := slAt_ok hsz (q := q) (r := r) (i := 6) (j := 7) (kn := 6) rfl rfl rfl hes hes'
    apply bool_of_iff
    simp only [ruleEqButRhsB, ruleEqAB, ruleEqBB, e0, e1, e2, e3, f0, f1, f2, f3, e9, e10, f9, f10,
      s1, s2, if_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, IRecRule.mk.injEq, fld_nat,
      fld_hd h0 g0, fld_bool, IRecRuleFire.nested.injEq]
    simp [and_assoc]

theorem decRules_succ (a : Array Word) (o n : Nat) :
    decRules a o (n + 1) = (do
      let r ← decRule a o
      let rs ← decRules a (o + 11) n
      pure (r :: rs)) := by
  simp only [decRules, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

theorem rule_eq_iff (x y : IRecRule) :
    ({ x with rhs := default } = { y with rhs := default } ∧ x.rhs = y.rhs) ↔ x = y := by
  obtain ⟨c, nf, cp, fire, rhs, k, eta⟩ := x
  obtain ⟨c', nf', cp', fire', rhs', k', eta'⟩ := y
  simp only [IRecRule.mk.injEq]
  grind

theorem rulesEqN_ok {a : Array Word} (hsz : a.size < 2 ^ 64) :
    ∀ (c : Nat) (o1 o2 : Word) (xs ys : List IRecRule),
    decRules a o1.toNat c = some xs → decRules a o2.toNat c = some ys →
    rulesEqN a c o1 o2 = decide (xs = ys)
  | 0, o1, o2, xs, ys, h1, h2 => by
    simp [decRules] at h1 h2; subst h1; subst h2; simp [rulesEqN]
  | c + 1, o1, o2, xs, ys, h1, h2 => by
    rw [decRules_succ] at h1 h2
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h1 h2
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h1
    obtain ⟨y, hy, ys', hys, rfl⟩ := h2
    obtain ⟨w0, w1, w2, w3, w8, w9, w10, e0, e1, e2, e3, e8, e9, e10, h0, h8, c0, c1, c2, c8, c9, c10, hf, hb⟩ :=
      ruleFields (q := o1) hsz hx
    obtain ⟨v0, v1, v2, v3, v8, v9, v10, f0, f1, f2, f3, f8, f9, f10, g0, g8, d0, d1, d2, d8, d9, d10, hg, hb'⟩ :=
      ruleFields (q := o2) hsz hy
    have t1 : (o1 + 11).toNat = o1.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
    have t2 : (o2 + 11).toNat = o2.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
    have ih := rulesEqN_ok hsz c (o1 + 11) (o2 + 11) xs' ys' (by rw [t1]; exact hxs) (by rw [t2]; exact hys)
    rw [rulesEqN_succ, ih, ruleEqButRhsB_ok hsz hx hy, e8, f8]
    apply bool_of_iff
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.cons.injEq]
    rw [← rule_eq_iff x y, c8, d8, fld_hd h8 g8]

theorem rulesEqB_ok {a : Array Word} (hsz : a.size < 2 ^ 64) {o1 l1 o2 l2 : Word}
    {xs ys : List IRecRule} (h1 : decRules a o1.toNat l1.toNat = some xs)
    (h2 : decRules a o2.toNat l2.toNat = some ys) :
    rulesEqB a o1 l1 o2 l2 = decide (xs = ys) := by
  have n1 := mapM_opt_length _ _ _ h1
  have n2 := mapM_opt_length _ _ _ h2
  simp only [List.length_range] at n1 n2
  by_cases hl : l1 = l2
  · subst hl
    simp only [rulesEqB, beq_self_eq_true, Bool.true_and]
    exact rulesEqN_ok hsz _ o1 o2 xs ys h1 h2
  · have : xs ≠ ys := fun e => hl (UInt64.toNat_inj.mp (by rw [← n1, ← n2, e]))
    have hb : (l1 == l2) = false := by simpa using hl
    simp [rulesEqB, hb, this]

/-! ## Constant records -/

theorem cvEqB_ok' {a : Array Word} (hsz : a.size < 2 ^ 64) {p q k : Word} {kn : Nat} (hk : k.toNat = kn)
    {cv cv' : IConstantVal} (hx : decCV a (p.toNat + kn) = some cv)
    (hy : decCV a (q.toNat + kn) = some cv') : cvEqB a (p + k) (q + k) = decide (cv = cv') := by
  obtain ⟨w, hw, -⟩ := decCV_name hx
  obtain ⟨w', hw', -⟩ := decCV_name hy
  exact cvEqB_ok hsz (by rw [toNat_add_of_get hsz hk hw]; exact hx)
    (by rw [toNat_add_of_get hsz hk hw']; exact hy)

theorem hintEqB_ok' {a : Array Word} (hsz : a.size < 2 ^ 64) {p q k : Word} {kn : Nat} (hk : k.toNat = kn)
    {x y : ConLeche.ReducibilityHint} (hx : decHint a (p.toNat + kn) = some x)
    (hy : decHint a (q.toNat + kn) = some y) : hintEqB a (p + k) (q + k) = decide (x = y) := by
  obtain ⟨w, hw, -⟩ := hintD hx
  obtain ⟨w', hw', -⟩ := hintD hy
  exact hintEqB_ok hsz (by rw [toNat_add_of_get hsz hk hw]; exact hx)
    (by rw [toNat_add_of_get hsz hk hw']; exact hy)

theorem capsEqAll_ok' {a : Array Word} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hsz : a.size < 2 ^ 64) {p q k : Word} {kn : Nat} (hk : k.toNat = kn) {x y : IIndCaps}
    (hx : decCaps a dn (p.toNat + kn) = some x) (hy : decCaps a dn (q.toNat + kn) = some y) :
    capsEqAll a (p + k) (q + k) = decide (x = y) := by
  have b1 : ∀ {r : Word} {z : IIndCaps}, decCaps a dn (r.toNat + kn) = some z →
      a[r.toNat + kn]? ≠ none := by
    intro r z h
    simp only [decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, -⟩ := h
    obtain ⟨w, hw, -⟩ := boolD hb
    rw [hw]; simp
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (b1 hx)
  obtain ⟨w', hw'⟩ := Option.ne_none_iff_exists'.mp (b1 hy)
  exact capsEqAll_ok hdn hsz (by rw [toNat_add_of_get hsz hk hw]; exact hx)
    (by rw [toNat_add_of_get hsz hk hw']; exact hy)

theorem ciD {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {x : IConstantInfo}
    (h : decCI a dn p = some x) :
    ∃ wk, a[p]? = some wk ∧
      ((wk.toNat = 0 ∧ ∃ cv, decCV a (p + 1) = some cv ∧ x = .axiomInfo cv) ∨
       (wk.toNat = 1 ∧ ∃ cv v hi, decCV a (p + 1) = some cv ∧ hd? a (p + 5) = some v ∧
          decHint a (p + 6) = some hi ∧ x = .defnInfo cv v hi) ∨
       (wk.toNat = 2 ∧ ∃ cv, decCV a (p + 1) = some cv ∧ x = .thmInfo cv) ∨
       (wk.toNat = 3 ∧ ∃ cv caps, decCV a (p + 1) = some cv ∧ decCaps a dn (p + 5) = some caps ∧
          x = .indInfo cv caps) ∨
       (wk.toNat = 4 ∧ ∃ cv np nf, decCV a (p + 1) = some cv ∧ nat? a (p + 5) = some np ∧
          nat? a (p + 6) = some nf ∧ x = .ctorInfo cv np nf) ∨
       (wk.toNat = 5 ∧ ∃ cv mi rp o c rules, decCV a (p + 1) = some cv ∧ nat? a (p + 5) = some mi ∧
          nat? a (p + 6) = some rp ∧ nat? a (p + 7) = some o ∧ nat? a (p + 8) = some c ∧
          decRules a o c = some rules ∧ x = .recInfo cv mi rp rules))) := by
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
    obtain ⟨cv, hcv, mi, hmi, rp, hrp, o, ho, c, hc, rules, hr, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inr ⟨hh, cv, mi, rp, o, c, rules, hcv, hmi, hrp, ho, hc, hr, rfl⟩))))
  · simp at h

theorem ciEqB_ok {a : Array Word} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hsz : a.size < 2 ^ 64) {p q : Word} {x y : IConstantInfo}
    (hx : decCI a dn p.toNat = some x) (hy : decCI a dn q.toNat = some y) :
    ciEqB a p q = decide (x = y) := by
  obtain ⟨wk, e, hx⟩ := ciD hx
  obtain ⟨wk', e', hy⟩ := ciD hy
  have r1 := rdW_zero' e
  have r2 := rdW_zero' e'
  have wl : ∀ (w : Word) (n : Nat) (hn : n < 2 ^ 64), w.toNat = n → w = UInt64.ofNat n := fun w n hn h =>
    UInt64.toNat_inj.mp (by rw [h]; simp [UInt64.toNat_ofNat_of_lt' hn])
  rcases hx with ⟨k0, cv, hcv, rfl⟩ | ⟨k0, cv, v, hi, hcv, hv, hhi, rfl⟩ | ⟨k0, cv, hcv, rfl⟩ |
      ⟨k0, cv, caps, hcv, hcaps, rfl⟩ | ⟨k0, cv, np, nf, hcv, hnp, hnf, rfl⟩ |
      ⟨k0, cv, mi, rp, o, c, rules, hcv, hmi, hrp, ho, hc, hr, rfl⟩ <;>
  rcases hy with ⟨k1, cv', hcv', rfl⟩ | ⟨k1, cv', v', hi', hcv', hv', hhi', rfl⟩ | ⟨k1, cv', hcv', rfl⟩ |
      ⟨k1, cv', caps', hcv', hcaps', rfl⟩ | ⟨k1, cv', np', nf', hcv', hnp', hnf', rfl⟩ |
      ⟨k1, cv', mi', rp', o', c', rules', hcv', hmi', hrp', ho', hc', hr', rfl⟩
  all_goals first
    | (have hne : wk ≠ wk' := fun h => by have := congrArg UInt64.toNat h; omega
       simp [ciEqB, r1, r2, hne]; done)
    | skip
  · -- axiom
    have a1 : wk = 0 := wl wk 0 (by decide) k0
    have a2 : wk' = 0 := wl wk' 0 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hsz (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB]
    simp [c1]
  · -- defn
    have a1 : wk = 1 := wl wk 1 (by decide) k0
    have a2 : wk' = 1 := wl wk' 1 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hsz (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    obtain ⟨w5, f5, u5, rfl⟩ := hdW_ (q := p) (k := 5) (kn := 5) hsz rfl hv
    obtain ⟨v5, g5, t5, rfl⟩ := hdW_ (q := q) (k := 5) (kn := 5) hsz rfl hv'
    have c2 := hintEqB_ok' hsz (p := p) (q := q) (k := 6) (kn := 6) rfl hhi hhi'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB, f5, g5, c1, c2]
    simp [fld_hd u5 t5, and_assoc]
  · -- thm
    have a1 : wk = 2 := wl wk 2 (by decide) k0
    have a2 : wk' = 2 := wl wk' 2 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hsz (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB]
    simp [c1]
  · -- ind
    have a1 : wk = 3 := wl wk 3 (by decide) k0
    have a2 : wk' = 3 := wl wk' 3 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hsz (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    have c2 := capsEqAll_ok' hdn hsz (p := p) (q := q) (k := 5) (kn := 5) rfl hcaps hcaps'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB, c1, c2]
    simp
  · -- ctor
    have a1 : wk = 4 := wl wk 4 (by decide) k0
    have a2 : wk' = 4 := wl wk' 4 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hsz (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    obtain ⟨w5, f5, rfl⟩ := natW_ (q := p) (k := 5) (kn := 5) hsz rfl hnp
    obtain ⟨v5, g5, rfl⟩ := natW_ (q := q) (k := 5) (kn := 5) hsz rfl hnp'
    obtain ⟨w6, f6, rfl⟩ := natW_ (q := p) (k := 6) (kn := 6) hsz rfl hnf
    obtain ⟨v6, g6, rfl⟩ := natW_ (q := q) (k := 6) (kn := 6) hsz rfl hnf'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB, f5, g5, f6, g6, c1]
    simp [fld_nat, and_assoc]
  · -- rec
    have a1 : wk = 5 := wl wk 5 (by decide) k0
    have a2 : wk' = 5 := wl wk' 5 (by decide) k1
    subst a1 a2
    have c1 := cvEqB_ok' hsz (p := p) (q := q) (k := 1) (kn := 1) rfl hcv hcv'
    obtain ⟨w5, f5, rfl⟩ := natW_ (q := p) (k := 5) (kn := 5) hsz rfl hmi
    obtain ⟨v5, g5, rfl⟩ := natW_ (q := q) (k := 5) (kn := 5) hsz rfl hmi'
    obtain ⟨w6, f6, rfl⟩ := natW_ (q := p) (k := 6) (kn := 6) hsz rfl hrp
    obtain ⟨v6, g6, rfl⟩ := natW_ (q := q) (k := 6) (kn := 6) hsz rfl hrp'
    obtain ⟨w7, f7, rfl⟩ := natW_ (q := p) (k := 7) (kn := 7) hsz rfl ho
    obtain ⟨v7, g7, rfl⟩ := natW_ (q := q) (k := 7) (kn := 7) hsz rfl ho'
    obtain ⟨w8, f8, rfl⟩ := natW_ (q := p) (k := 8) (kn := 8) hsz rfl hc
    obtain ⟨v8, g8, rfl⟩ := natW_ (q := q) (k := 8) (kn := 8) hsz rfl hc'
    have c2 := rulesEqB_ok hsz hr hr'
    apply bool_of_iff
    simp only [ciEqB, r1, r2, ciEqRestB, f5, g5, f6, g6, f7, g7, f8, g8, c1, c2]
    simp [fld_nat, and_assoc]

end L.Ind

namespace L.Arena

open L.Ind

theorem rowPW_eq (m : Mem) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : tagW w ≤ 2) :
    rowPW m w = rowP m w := by
  have h1 := tagW_toNat w
  have h2 := ixW_succ w hw
  have ht' : rowTag w ≤ 2 := by rw [← h1]; exact UInt64.le_iff_toNat_le.mp ht
  simp only [rowPW, rowP, ht', if_true, rdW, h2]
  simp [selArr_rowSelW w ht']

/-- **A hit of `env_find` is a hit of `find?`**: the record pointer is the row's, and the lookup
decodes there. -/
theorem envFindW_hit {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem}
    {w : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) (hE : EnvR dn m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : r.headD 0 ≠ 0) :
    m1 = m ∧ r.tail.headD 0 = rowP m w ∧ fe.find? (decI w) = decCI (erecP m) dn (rowP m w).toNat ∧
      rowTag w ≤ 2 ∧ rowC m w ≠ 0 := by
  unfold envFindW at h
  obtain ⟨ht, h⟩ := of_ite_none h
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => ht (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  rw [EnvR.find?_eq hE w hw htag, ← rowCW_eq m w hw ht2]
  by_cases hc : rowCW m w = 0
  · rw [if_pos hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0
  rw [if_neg hc] at h
  by_cases hv : rowCW m w - 1 < vis
  · rw [if_pos hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc' : (rowCW m w).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
    refine ⟨rfl, by simpa using rowPW_eq m w hw ht2, ?_, htag, hc⟩
    have : (rowCW m w).toNat - 1 < vis.toNat := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
        (UInt64.le_iff_toNat_le.mpr (by simp; omega))] at hv
      simpa using hv
    simp [hc, this]
  · rw [if_neg hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0

end L.Arena

namespace L.Ind

open L.Arena

theorem envR_row_dec {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) :
    rowTag w ≤ 2 → rowC m w ≠ 0 → ∃ ci, decCI (erecP m) dn (rowP m w).toNat = some ci := by
  intro ht h0
  have hk := h.keys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.vals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  have hv := hv h0
  simp only [rowW, h0, ite_false, Option.map_some] at hk
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => simp [e] at hk
  | some r =>
    simp only [e, Option.map_some] at hv
    exact ⟨r.2, hv.symm⟩

/-- A finished call of `find_is`, against the twin's lookup and comparison. -/
theorem findIsW_ok {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv}
    {m : Mem} {a : AState} (hS : StageR dn vis fe m a) {nm pin w : Word} (hn : nm.toNat < 2 ^ 32)
    {c' : IConstantInfo} (hc' : decCI (erA m) dn pin.toNat = some c')
    (h : findIsW m nm vis pin = some w) :
    (w != 0) = (fe.find? (decI nm) == some c') ∧ w.toNat ≤ 1 := by
  unfold findIsW at h
  cases h1 : envFindW m nm vis with
  | none => rw [h1] at h; simp at h
  | some rm =>
  obtain ⟨rr, m1⟩ := rm
  rw [h1] at h
  simp only at h
  by_cases h0 : rr.headD 0 = 0
  · rw [if_pos h0] at h; simp only [Option.some.injEq] at h; subst h
    obtain ⟨-, hfind⟩ := envFindW_miss h1 hS.1.env hn h0
    rw [hfind]; simp
  · rw [if_neg h0] at h; simp only [Option.some.injEq] at h
    obtain ⟨-, hptr, hfind, htag, hrc⟩ := envFindW_hit h1 hS.1.env hn h0
    have hsz : (erA m).size < 2 ^ 64 := hS.2.2.2.2.1
    obtain ⟨ci, hci⟩ := envR_row_dec hS.1.env nm hn htag hrc
    have hci0 : decCI (erA m) dn (rowP m nm).toNat = some ci := ArrExt.decCI (erecP_ext m) hci
    have hptr' : rr.tail.headD 0 = rowP m nm := hptr
    rw [hfind, hci]
    have hq := ciEqB_ok hdn hsz (p := rr.tail.headD 0) (q := pin) (x := ci) (y := c')
      (by rw [hptr']; exact hci0) hc'
    subst h
    simp only [erA] at hq
    rw [hq]
    by_cases e : ci = c'
    · subst e; simp
    · simp [e]

/-- The shape every pure equality spec has. -/
theorem refAM_pure {α : Type} [Inhabited α] (p : Prog) (f : FnName) (args : List Word)
    (pre : Mem → AState → Prop) (x : α) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (dec : Mem → List Word → α → Prop)
    (hpre : ∀ m a, pre m a → StageR dn vis fe m a)
    (h : ∀ (n : Nat) (s₀ : St) (a₀ : AState), pre s₀.mem a₀ →
      ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ dec s₀.mem r x; ⊤⦄) :
    RefAM p f args pre (pure x) (KeepPost dn vis fe dec) := by
  intro n s₀ a₀ hp
  refine triple_post (h n s₀ a₀ hp) ?_
  rintro r s' ⟨hl, hm, hd⟩
  refine ⟨hl, by simp [AM.ok_pure], ?_⟩
  simp only [AM.st_pure, AM.res_pure]
  rw [hm]
  exact ⟨hpre _ _ hp, IWGrow.refl _, hd⟩

section refs
variable (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
include hp

/-- **`find_is(vis, n, pin)` refines `fe.find? n == some c'`.** -/
theorem findIs_spec (hdn : DnInj dn) (nm pin : Word) (c' : IConstantInfo) :
    RefAM p "find_is" [vis, nm, pin]
      (fun m a => StageR dn vis fe m a ∧ H nm ∧ decCI (erA m) dn pin.toNat = some c')
      (pure (fe.find? (decI nm) == some c') : AM Bool) (KeepPost dn vis fe decW0B) := by
  refine refAM_pure p _ _ _ _ dn vis fe _ (fun m a h => h.1) ?_
  intro n s₀ a₀ ⟨hS, hn, hc'⟩
  refine triple_post (findIs_spec' p hp n s₀ nm vis pin) ?_
  rintro rr s' ⟨hl, hm, hr⟩
  obtain ⟨h1, h2⟩ := findIsW_ok hdn hS hn hc' hr
  exact ⟨hl, hm, h1, h2⟩

end refs

end L.Ind
