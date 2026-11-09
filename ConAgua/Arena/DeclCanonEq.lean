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
    (hk : k.toNat = kn) (h : hd? (aread a) (q.toNat + kn) = some x) :
    ∃ w, rdW a (q + k) = w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  obtain ⟨w, hw, hlt, rfl⟩ := hd?_some h
  exact ⟨w, rdW_off hsz (by rw [hk]; exact hw), hlt, rfl⟩

theorem hdW0_ {kk : IdxKind} {q : Word} {x : Idx kk} (h : hd? (aread a) q.toNat = some x) :
    ∃ w, rdW a q = w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  obtain ⟨w, hw, hlt, rfl⟩ := hd?_some h
  exact ⟨w, rdW_zero' hw, hlt, rfl⟩

theorem natD {i n : Nat} (h : nat? (aread a) i = some n) : ∃ w, a[i]? = some w ∧ n = w.toNat := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem boolD {i : Nat} {b : Bool} (h : bool? (aread a) i = some b) : ∃ w, a[i]? = some w ∧ b = (w != 0) := by
  simp only [bool?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h; exact ⟨w, hw, rfl⟩

theorem natW_ {q k : Word} {kn n : Nat} (hsz : a.size < 2 ^ 64) (hk : k.toNat = kn)
    (h : nat? (aread a) (q.toNat + kn) = some n) : ∃ w, rdW a (q + k) = w ∧ n = w.toNat := by
  obtain ⟨w, hw, rfl⟩ := natD h
  exact ⟨w, rdW_off hsz (by rw [hk]; exact hw), rfl⟩

theorem boolW_ {q k : Word} {kn : Nat} {b : Bool} (hsz : a.size < 2 ^ 64) (hk : k.toNat = kn)
    (h : bool? (aread a) (q.toNat + kn) = some b) : ∃ w, rdW a (q + k) = w ∧ b = (w != 0) := by
  obtain ⟨w, hw, rfl⟩ := boolD h
  exact ⟨w, rdW_off hsz (by rw [hk]; exact hw), rfl⟩

theorem boolW0_ {q : Word} {b : Bool} (h : bool? (aread a) q.toNat = some b) :
    ∃ w, rdW a q = w ∧ b = (w != 0) := by
  obtain ⟨w, hw, rfl⟩ := boolD h
  exact ⟨w, rdW_zero' hw, rfl⟩

end rd

theorem fld_nat {w w' : Word} : (w.toNat = w'.toNat) ↔ w = w' :=
  ⟨fun h => UInt64.toNat_inj.mp h, fun h => by rw [h]⟩

theorem fld_bool {w w' : Word} : ((w != 0) = (w' != 0)) ↔ bEqB w w' = true := by
  simp [bEqB]

/-! ## Slices -/

theorem hslice_len {kk : IdxKind} {a : Array Word} {o c : Nat} {xs : List (Idx kk)}
    (h : hslice? (aread a) o c = some xs) : xs.length = c := by
  have := mapM_opt_length _ _ _ h
  simpa using this

theorem slEqN_ok {kk : IdxKind} {a : Array Word} (hsz : a.size < 2 ^ 64) :
    ∀ (c : Nat) (o1 o2 : Word) (xs ys : List (Idx kk)),
    hslice? (aread a) o1.toNat c = some xs → hslice? (aread a) o2.toNat c = some ys →
    slEqN a c o1 o2 = decide (xs = ys) := by
  sorry

theorem erSlEqB_ok {kk : IdxKind} {a : Array Word} (hsz : a.size < 2 ^ 64) {o1 l1 o2 l2 : Word}
    {xs ys : List (Idx kk)} (h1 : hslice? (aread a) o1.toNat l1.toNat = some xs)
    (h2 : hslice? (aread a) o2.toNat l2.toNat = some ys) :
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
    (h : hlist? (aread a) (q.toNat + kn) = some xs) :
    ∃ o l, rdW a (q + k) = o ∧ rdW a (q + k1) = l ∧ hslice? (aread a) o.toNat l.toNat = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, hs⟩ := h
  obtain ⟨wo, hwo, rfl⟩ := natW_ hsz hk ho
  obtain ⟨wl, hwl, rfl⟩ := natW_ (q := q) (k := k1) (kn := kn + 1) hsz hk1 hl
  exact ⟨wo, wl, hwo, hwl, hs⟩

/-! ## Constant values, hints, `PropWhen` -/

theorem cvFields {a : Array Word} {q : Word} {cv : IConstantVal} (hsz : a.size < 2 ^ 64)
    (h : decCV (aread a) q.toNat = some cv) :
    ∃ wn o l wt : Word, rdW a q = wn ∧ rdW a (q + 1) = o ∧ rdW a (q + 2) = l ∧ rdW a (q + 3) = wt ∧
      wn.toNat < 2 ^ 32 ∧ wt.toNat < 2 ^ 32 ∧ cv.name = decI wn ∧ cv.type = decI wt ∧
      hslice? (aread a) o.toNat l.toNat = some cv.levelParams := by
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨n, hn, lps, hl, t, ht, e⟩ := h
  have e' := Option.some.inj e
  subst e'
  obtain ⟨wn, e0, hn32, rfl⟩ := hdW0_ hn
  obtain ⟨o, l, e1, e2, hs⟩ := hlistW_ (q := q) (k := 1) (k1 := 2) (kn := 1) hsz rfl rfl hl
  obtain ⟨wt, e3, ht32, rfl⟩ := hdW_ (q := q) (k := 3) (kn := 3) hsz rfl ht
  exact ⟨wn, o, l, wt, e0, e1, e2, e3, hn32, ht32, rfl, rfl, hs⟩

theorem cvEqB_ok {a : Array Word} (hsz : a.size < 2 ^ 64) {q r : Word} {cv cv' : IConstantVal}
    (h1 : decCV (aread a) q.toNat = some cv) (h2 : decCV (aread a) r.toNat = some cv') :
    cvEqB a q r = decide (cv = cv') := by
  obtain ⟨wn, o, l, wt, e0, e1, e2, e3, hn, ht, hcn, hct, hs⟩ := cvFields hsz h1
  obtain ⟨wn', o', l', wt', e0', e1', e2', e3', hn', ht', hcn', hct', hs'⟩ := cvFields hsz h2
  have hl := erSlEqB_ok hsz hs hs'
  obtain ⟨cn, cl, ct⟩ := cv
  obtain ⟨cn', cl', ct'⟩ := cv'
  simp only at hcn hct hs hcn' hct' hs'
  subst hcn hct hcn' hct'
  simp only [cvEqB, e0, e0', e1, e1', e2, e2', e3, e3', hl]
  simp only [IConstantVal.mk.injEq, decI_inj_iff hn hn', decI_inj_iff ht ht']
  by_cases h1 : wn = wn' <;> by_cases h2 : cl = cl' <;>
    by_cases h3 : wt = wt' <;> simp [h1, h2, h3]

theorem hintD {a : Array Word} {q : Nat} {x : ConLeche.ReducibilityHint} (h : decHint (aread a) q = some x) :
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
    (hx : decHint (aread a) h.toNat = some x) (hy : decHint (aread a) g.toNat = some y) :
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

theorem toNat_add_of_get {a : Array Word} {q k : Word} {kn : Nat} {w : Word} (hsz : a.size < 2 ^ 64)
    (hk : k.toNat = kn) (h : a[q.toNat + kn]? = some w) : (q + k).toNat = q.toNat + kn := by
  have hlt : q.toNat + kn < a.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [UInt64.toNat_add, hk]; exact Nat.mod_eq_of_lt (by omega)

theorem erSlAtB_lit {a : Array Word} {q r i j : Word} (hj : i + 1 = j) :
    erSlAtB a q r i = erSlEqB a (rdW a (q + i)) (rdW a (q + j)) (rdW a (r + i)) (rdW a (r + j)) := by
  simp only [erSlAtB, ← hj, UInt64.add_assoc]

/-- A slice stored at words `i`, `i + 1` of a record, compared. -/
theorem slAt_ok {kk : IdxKind} {a : Array Word} (hsz : a.size < 2 ^ 64) {q r i j : Word} {kn : Nat}
    {xs ys : List (Idx kk)} (hi : i.toNat = kn) (hj : j.toNat = kn + 1) (hij : i + 1 = j)
    (hx : hlist? (aread a) (q.toNat + kn) = some xs) (hy : hlist? (aread a) (r.toNat + kn) = some ys) :
    erSlAtB a q r i = decide (xs = ys) := by
  obtain ⟨o, l, e1, e2, hs⟩ := hlistW_ (q := q) (k := i) (k1 := j) (kn := kn) hsz hi hj hx
  obtain ⟨o', l', e1', e2', hs'⟩ := hlistW_ (q := r) (k := i) (k1 := j) (kn := kn) hsz hi hj hy
  rw [erSlAtB_lit hij, e1, e2, e1', e2']
  exact erSlEqB_ok hsz hs hs'

theorem capsEqAll_ok {a : Array Word} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hsz : a.size < 2 ^ 64) {q r : Word} {x y : IIndCaps}
    (hx : decCaps (aread a) q.toNat = some x) (hy : decCaps (aread a) r.toNat = some y) :
    capsEqAll a q r = decide (x = y) := by
  sorry

/-! ## Recursor rules -/

theorem ruleFields {a : Array Word} {q : Word} {x : IRecRule} (hsz : a.size < 2 ^ 64)
    (h : decRule (aread a) q.toNat = some x) :
    ∃ w0 w1 w3 w8 : Word, rdW a q = w0 ∧ rdW a (q + 1) = w1 ∧
      rdW a (q + 3) = w3 ∧ rdW a (q + 8) = w8 ∧
      w0.toNat < 2 ^ 32 ∧ w8.toNat < 2 ^ 32 ∧ x.ctor = decI w0 ∧ x.nfields = w1.toNat ∧
      x.rhs = decI w8 ∧
      ((w3.toNat = 0 ∧ x.fire = .plain) ∨
       (w3.toNat = 1 ∧ ∃ (ls : List LIdx) (es : List EIdx), hlist? (aread a) (q.toNat + 4) = some ls ∧
          hlist? (aread a) (q.toNat + 6) = some es ∧ x.fire = .nested ls es) ∨
       (w3.toNat = 2 ∧ ∃ (ls : List LIdx), hlist? (aread a) (q.toNat + 4) = some ls ∧
          x.fire = .levels ls)) ∧
      q.toNat + 11 < 2 ^ 64 := by
  sorry

theorem ruleEqButRhsB_ok {a : Array Word} (hsz : a.size < 2 ^ 64) {q r : Word} {x y : IRecRule}
    (hx : decRule (aread a) q.toNat = some x) (hy : decRule (aread a) r.toNat = some y) :
    ruleEqButRhsB a q r = decide ({ x with rhs := default } = { y with rhs := default }) := by
  sorry

theorem decRules_succ (a : Array Word) (o n : Nat) :
    decRules (aread a) o (n + 1) = (do
      let r ← decRule (aread a) o
      let rs ← decRules (aread a) (o + 11) n
      pure (r :: rs)) := by
  simp only [decRules, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

theorem rule_eq_iff (x y : IRecRule) :
    ({ x with rhs := default } = { y with rhs := default } ∧ x.rhs = y.rhs) ↔ x = y := by
  sorry

theorem rulesEqN_ok {a : Array Word} (hsz : a.size < 2 ^ 64) :
    ∀ (c : Nat) (o1 o2 : Word) (xs ys : List IRecRule),
    decRules (aread a) o1.toNat c = some xs → decRules (aread a) o2.toNat c = some ys →
    rulesEqN a c o1 o2 = decide (xs = ys) := by
  sorry

theorem rulesEqB_ok {a : Array Word} (hsz : a.size < 2 ^ 64) {o1 l1 o2 l2 : Word}
    {xs ys : List IRecRule} (h1 : decRules (aread a) o1.toNat l1.toNat = some xs)
    (h2 : decRules (aread a) o2.toNat l2.toNat = some ys) :
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
    {cv cv' : IConstantVal} (hx : decCV (aread a) (p.toNat + kn) = some cv)
    (hy : decCV (aread a) (q.toNat + kn) = some cv') : cvEqB a (p + k) (q + k) = decide (cv = cv') := by
  obtain ⟨w, hw, -⟩ := decCV_name hx
  obtain ⟨w', hw', -⟩ := decCV_name hy
  exact cvEqB_ok hsz (by rw [toNat_add_of_get hsz hk hw]; exact hx)
    (by rw [toNat_add_of_get hsz hk hw']; exact hy)

theorem hintEqB_ok' {a : Array Word} (hsz : a.size < 2 ^ 64) {p q k : Word} {kn : Nat} (hk : k.toNat = kn)
    {x y : ConLeche.ReducibilityHint} (hx : decHint (aread a) (p.toNat + kn) = some x)
    (hy : decHint (aread a) (q.toNat + kn) = some y) : hintEqB a (p + k) (q + k) = decide (x = y) := by
  obtain ⟨w, hw, -⟩ := hintD hx
  obtain ⟨w', hw', -⟩ := hintD hy
  exact hintEqB_ok hsz (by rw [toNat_add_of_get hsz hk hw]; exact hx)
    (by rw [toNat_add_of_get hsz hk hw']; exact hy)

theorem capsEqAll_ok' {a : Array Word} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hsz : a.size < 2 ^ 64) {p q k : Word} {kn : Nat} (hk : k.toNat = kn) {x y : IIndCaps}
    (hx : decCaps (aread a) (p.toNat + kn) = some x) (hy : decCaps (aread a) (q.toNat + kn) = some y) :
    capsEqAll a (p + k) (q + k) = decide (x = y) := by
  sorry

theorem ciD {a : Array Word} {p : Nat} {x : IConstantInfo}
    (h : decCI (aread a) p = some x) :
    ∃ wk, a[p]? = some wk ∧
      ((wk.toNat = 0 ∧ ∃ cv, decCV (aread a) (p + 1) = some cv ∧ x = .axiomInfo cv) ∨
       (wk.toNat = 1 ∧ ∃ cv v hi, decCV (aread a) (p + 1) = some cv ∧ hd? (aread a) (p + 5) = some v ∧
          decHint (aread a) (p + 6) = some hi ∧ x = .defnInfo cv v hi) ∨
       (wk.toNat = 2 ∧ ∃ cv, decCV (aread a) (p + 1) = some cv ∧ x = .thmInfo cv) ∨
       (wk.toNat = 3 ∧ ∃ cv caps, decCV (aread a) (p + 1) = some cv ∧ decCaps (aread a) (p + 5) = some caps ∧
          x = .indInfo cv caps) ∨
       (wk.toNat = 4 ∧ ∃ cv np nf, decCV (aread a) (p + 1) = some cv ∧ nat? (aread a) (p + 5) = some np ∧
          nat? (aread a) (p + 6) = some nf ∧ x = .ctorInfo cv np nf) ∨
       (wk.toNat = 5 ∧ ∃ cv mi rp o c k rules, decCV (aread a) (p + 1) = some cv ∧
          nat? (aread a) (p + 5) = some mi ∧ nat? (aread a) (p + 6) = some rp ∧
          nat? (aread a) (p + 7) = some o ∧ nat? (aread a) (p + 8) = some c ∧
          bool? (aread a) (p + 9) = some k ∧
          decRules (aread a) o c = some rules ∧ x = .recInfo cv mi rp k rules)) := by
  sorry

/-- **A decoded record's constant value sits at `p + 1`** (every kind holds it inline, the twin's
pure `toConstantVal`). -/
theorem ciD_cv {a : Array Word} {p : Nat} {x : IConstantInfo}
    (h : decCI (aread a) p = some x) : decCV (aread a) (p + 1) = some x.toConstantVal := by
  sorry

theorem ciEqB_ok {a : Array Word} {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hsz : a.size < 2 ^ 64) {p q : Word} {x y : IConstantInfo}
    (hx : decCI (aread a) p.toNat = some x) (hy : decCI (aread a) q.toNat = some y) :
    ciEqB a p q = decide (x = y) := by
  sorry

end L.Ind

namespace L.Arena

open L.Ind

/- ronsync2 stage 2: commented out (stale program / l_model / removed twin)
theorem rowPW_eq (m : Mem) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : tagW w ≤ 2) :
    rowPW m w = rowP m w := by
  sorry

-/

/- ronsync2 stage 2: commented out (stale program / l_model / removed twin)
/-- **A hit of `env_find` is a hit of `find?`**: the record pointer is the row's, and the lookup
decodes there. -/
theorem envFindW_hit {vis : Word} {fe : IFEnv} {m m1 : Mem}
    {w : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) (hE : EnvR m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : r.headD 0 ≠ 0) :
    m1 = m ∧ r.tail.headD 0 = rowP m w ∧ fe.find? (decI w) = decCI (erecP m) (rowP m w).toNat ∧
      rowTag w ≤ 2 ∧ rowC m w ≠ 0 := by
  sorry

-/

end L.Arena
