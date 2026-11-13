module

public import ConAgua.Arena.Handle
public import ConAgua.Arena.RecLayout.CI
public import ConRon.Arena.Env

@[expose] public section

/-!
# Environment records in a word pool, and their decoders

The twin's environment values (`IConstantVal`, `IConstantInfo`, `IProjTable`) are nested: lists
of handles, lists of recursor rules (each with lists of its own), an `IIndCaps` with two lists, an
`IProjTable` with an `Array`. In L they are **records in a word pool**: a record is a run of
words at an address `p`, every list is a slice `(off, cnt)` of the same pool (two words of the
record), and a list of records is a slice of fixed-size records (recursor rules, 11 words). The
decoders below are the value relations (`decE`'s analogue): `decCI a p = some ci` says that the
record at `p` of the pool read by `a` denotes `ci`. A pool is read through a **reader**
`a : Nat → Option Word` (`aread` of an array; `erecP`, `Tiers.lean`, for `EREC`, whose two tiers
are one address space: tier 1 at `2^40 + i`), and only through it, so a pool that only grows
above its tops keeps every decoding below them (`ArrExt`).

Handle words must be below `2^32` (`hd?` refuses others), so a decoded handle is the word itself
and L may compare words where the twin compares handles.

## The layouts (offsets from the record address `p`)

`IConstantVal`: `RecLayout/CV.lean` (`CV.size` words at `q`: `name`, the lps slice, `type`).

`IConstantInfo`: `RecLayout/CI.lean` (word `p + CI.kind` is the kind; the value is at `p + CI.cv`,
so **word `p + CI.cv` is always the index key** `ci.name`):

| kind | constructor | fields (offsets `CI.…`) |
|---:|---|---|
| 0 | `axiomInfo cv` | `cv`; size `axiomSize` |
| 1 | `defnInfo cv value hint` | `cv`; `defnValue`; the hint at `defnHint` (`Hint.kind`: 0 opaque, 1 abbrev, 2 regular; `Hint.height`); size `defnSize` |
| 2 | `thmInfo cv` | `cv`; size `thmSize` |
| 3 | `indInfo cv caps` | `cv`; caps at `indCaps` (`decCaps`); size `indSize` |
| 4 | `ctorInfo cv np nf induct` | `cv`; `ctorNparams`, `ctorNfields`, the family `ctorInduct`; size `ctorSize` |
| 5 | `recInfo cv major pre isK rules` | `cv`; `recMajor`, `recPrefix`; rules slice `recRulesOff`, `recRulesLen` (11-word records); `recIsK`; size `recSize` |

A recursor rule (11 words at `q`): `ctor` `q`, `nfields` `q+1`, the fire's kind `q+3` (0
`plain`, 1 `nested`, 2 `levels`), its level slice `q+4`, `q+5`, its pin slice `q+6`, `q+7`
(`nested` only), `rhs` `q+8`; words `q+2`, `q+9`, `q+10` are not read (they held the
install-computed `ctorParams`, `k`, `eta`, which con-leche's task #480 removed; the offsets of
the rest are kept).

`IIndCaps`: `RecLayout/Caps.lean` (`Caps.size` words at `q`, the field offsets named there).

`IProjTable` (13 words, at `p`; not a constant: the environment's table component): word `p` is
`6` and word `p+1` is `0` (the kind and name words of the constant records' layout, kept so that
the fields keep their offsets), `structName` `p+2`, lps `p+3`,`p+4`, `numParams` `p+5`, `ctor`
`p+6`, `numFields` `p+7`, bodies `p+9`,`p+10`; words `p+8`, `p+11`, `p+12` are not read (the
removed `structSort` and `guards`).

The declarations themselves are the front's records (`DECL`/`DLP`, `Front/StateDR.lean`'s
`DeclsF`); an inductive block's constants are a slice of constant records in `DLP`.
-/

namespace L.Arena

open ConRon.Arena

section dec
variable (a : Nat → Option Word)

/-- Word `i`, a natural number. -/
def nat? (i : Nat) : Option Nat := (a i).map (·.toNat)

/-- Word `i`, a `Bool` (`0` is `false`). -/
def bool? (i : Nat) : Option Bool := (a i).map (· != 0)

/-- Word `i`, a handle (a word below `2^32`). -/
def hd? {k : IdxKind} (i : Nat) : Option (Idx k) := do
  let w ← a i
  if w.toNat < 2 ^ 32 then some (decI w) else none

/-- The handles at `off`, …, `off + len - 1`. -/
def hslice? {k : IdxKind} (off cnt : Nat) : Option (List (Idx k)) :=
  (List.range cnt).mapM fun j => hd? a (off + j)

/-- The handle list whose slice `(off, cnt)` is at words `i`, `i + 1`. -/
def hlist? {k : IdxKind} (i : Nat) : Option (List (Idx k)) := do
  hslice? a (← nat? a i) (← nat? a (i + 1))

/-- `IConstantVal` at `q`, laid out by `RecLayout/CV.lean` (the name, at offset 0, is word `q`). -/
def decCV (q : Nat) : Option IConstantVal := do
  pure ⟨← hd? a q, ← hlist? a (q + CV.lpsOff.toNat), ← hd? a (q + CV.type.toNat)⟩

/-- A reducibility hint at `q`: its kind (word `q`, `Hint.kind` = 0) and height (`Hint.height`). -/
def decHint (q : Nat) : Option ConLeche.ReducibilityHint := do
  match ← nat? a q with
  | 0 => pure .opaque
  | 1 => pure .abbrev
  | 2 => pure (.regular (← nat? a (q + Hint.height.toNat)))
  | _ => none

/-- A recursor rule: an 11-word record at `q` (`ctor`, `nfields`, the fire's kind (0 plain, 1
nested, 2 levels) at `q + 3`, its level slice, its pin slice, `rhs` at `q + 8`). -/
def decRule (q : Nat) : Option IRecRule := do
  let fire ← match ← nat? a (q + 3) with
    | 0 => some IRecRuleFire.plain
    | 1 => some (IRecRuleFire.nested (← hlist? a (q + 4)) (← hlist? a (q + 6)))
    | 2 => some (IRecRuleFire.levels (← hlist? a (q + 4)))
    | _ => none
  pure { ctor := ← hd? a q, nfields := ← nat? a (q + 1), fire, rhs := ← hd? a (q + 8) }

/-- The rules of the slice `(off, cnt)` of 11-word records. -/
def decRules (off cnt : Nat) : Option (List IRecRule) :=
  (List.range cnt).mapM fun j => decRule a (off + 11 * j)

/-- `IIndCaps`: `Caps.size` words at `q`, laid out by `RecLayout/Caps.lean`. -/
def decCaps (q : Nat) : Option IIndCaps := do
  pure { eta := ← bool? a (q + Caps.eta.toNat), nIdx := ← nat? a (q + Caps.nIdx.toNat),
         all := ← hlist? a (q + Caps.allOff.toNat), nparams := ← nat? a (q + Caps.nparams.toNat),
         ctors := ← hlist? a (q + Caps.ctorsOff.toNat),
         neverZero := ← bool? a (q + Caps.neverZero.toNat) }

/-- `IProjTable` at `p` (a table record). -/
def decTbl (p : Nat) : Option IProjTable := do
  pure { structName := ← hd? a (p + 2),
         levelParams := ← hlist? a (p + 3), numParams := ← nat? a (p + 5), ctor := ← hd? a (p + 6),
         numFields := ← nat? a (p + 7), bodies := (← hlist? a (p + 9)).toArray }

/-- **The constant record at `p`**, laid out by `RecLayout/CI.lean` (the kind, at offset 0, is word
`p`). -/
def decCI (p : Nat) : Option IConstantInfo := do
  match ← nat? a p with
  | 0 => pure (.axiomInfo (← decCV a (p + CI.cv.toNat)))
  | 1 => pure (.defnInfo (← decCV a (p + CI.cv.toNat)) (← hd? a (p + CI.defnValue.toNat))
      (← decHint a (p + CI.defnHint.toNat)))
  | 2 => pure (.thmInfo (← decCV a (p + CI.cv.toNat)))
  | 3 => pure (.indInfo (← decCV a (p + CI.cv.toNat)) (← decCaps a (p + CI.indCaps.toNat)))
  | 4 => pure (.ctorInfo (← decCV a (p + CI.cv.toNat)) (← nat? a (p + CI.ctorNparams.toNat))
      (← nat? a (p + CI.ctorNfields.toNat)) (← hd? a (p + CI.ctorInduct.toNat)))
  | 5 => pure (.recInfo (← decCV a (p + CI.cv.toNat)) (← nat? a (p + CI.recMajor.toNat))
      (← nat? a (p + CI.recPrefix.toNat)) (← bool? a (p + CI.recIsK.toNat))
      (← decRules a (← nat? a (p + CI.recRulesOff.toNat)) (← nat? a (p + CI.recRulesLen.toNat))))
  | _ => none

end dec

end L.Arena

/-! ## Decoding is stable under extension

A decoder reads its reader only; a successful decoding read only words that exist, so it decodes
the same under any reader that agrees there (`ArrExt`). This is how a record pool that only grows
above its tops (`erecP`, `Tiers.lean`) keeps every decoding below them. -/

namespace L.Arena

open ConRon.Arena

/-- The reader of an array. -/
def aread (a : Array Word) : Nat → Option Word := fun i => a[i]?

@[simp] theorem aread_apply (a : Array Word) (i : Nat) : aread a i = a[i]? := rfl

/-- `b` extends `a`: every word `a` reads, `b` reads too. -/
def ArrExt (a b : Nat → Option Word) : Prop := ∀ (i : Nat) (v : Word), a i = some v → b i = some v

section ext
variable {a b : Nat → Option Word} (h : ArrExt a b)
include h

theorem ArrExt.nat? {i : Nat} {x : Nat} (hx : nat? a i = some x) : nat? b i = some x := by
  simp only [L.Arena.nat?, Option.map_eq_some_iff] at hx ⊢
  obtain ⟨v, hv, rfl⟩ := hx; exact ⟨v, h i v hv, rfl⟩

theorem ArrExt.bool? {i : Nat} {x : Bool} (hx : bool? a i = some x) : bool? b i = some x := by
  simp only [L.Arena.bool?, Option.map_eq_some_iff] at hx ⊢
  obtain ⟨v, hv, rfl⟩ := hx; exact ⟨v, h i v hv, rfl⟩

theorem ArrExt.hd? {k : IdxKind} {i : Nat} {x : Idx k} (hx : hd? a i = some x) : hd? b i = some x := by
  simp only [L.Arena.hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨v, hv, hx⟩ := hx; exact ⟨v, h i v hv, hx⟩

omit h in
theorem ArrExt.mapM {α : Type} {f g : Nat → Option α} (hfg : ∀ j x, f j = some x → g j = some x) :
    ∀ (l : List Nat) (xs : List α), l.mapM f = some xs → l.mapM g = some xs
  | [], xs, hx => by simpa using hx
  | j :: js, xs, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx ⊢
    obtain ⟨y, hy, ys, hys, rfl⟩ := hx
    exact ⟨y, hfg j y hy, ys, ArrExt.mapM hfg js ys hys, rfl⟩

theorem ArrExt.hslice? {k : IdxKind} {o c : Nat} {xs : List (Idx k)} (hx : hslice? a o c = some xs) :
    hslice? b o c = some xs :=
  ArrExt.mapM (f := fun j => L.Arena.hd? a (o + j)) (g := fun j => L.Arena.hd? b (o + j))
    (fun _ _ hy => h.hd? hy) _ _ hx

theorem ArrExt.hlist? {k : IdxKind} {i : Nat} {xs : List (Idx k)} (hx : hlist? a i = some xs) :
    hlist? b i = some xs := by
  simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨o, ho, c, hc, hs⟩ := hx
  exact ⟨o, h.nat? ho, c, h.nat? hc, h.hslice? hs⟩

theorem ArrExt.decCV {q : Nat} {x : IConstantVal} (hx : decCV a q = some x) : decCV b q = some x := by
  simp only [L.Arena.decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
  obtain ⟨n, hn, l, hl, t, ht, e⟩ := hx
  exact ⟨n, h.hd? hn, l, h.hlist? hl, t, h.hd? ht, e⟩

theorem ArrExt.decHint {q : Nat} {x : ConLeche.ReducibilityHint} (hx : decHint a q = some x) :
    decHint b q = some x := by
  simp only [L.Arena.decHint, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨k, hk, e⟩ := hx
  refine ⟨k, h.nat? hk, ?_⟩
  split at e
  · exact e
  · exact e
  · simp only [Option.bind_eq_some_iff, Option.pure_def] at e ⊢
    obtain ⟨y, hy, e⟩ := e; exact ⟨y, h.nat? hy, e⟩
  · exact e

theorem ArrExt.decRule {q : Nat} {x : IRecRule} (hx : decRule a q = some x) : decRule b q = some x := by
  unfold L.Arena.decRule at hx ⊢
  cases h3 : L.Arena.nat? a (q + 3) with
  | none => simp [h3] at hx
  | some t =>
    rw [h.nat? h3]; rw [h3] at hx
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some] at hx ⊢
    have tail : ∀ (f : IRecRuleFire), (do
        let ctor ← L.Arena.hd? a q
        let nfields ← L.Arena.nat? a (q + 1)
        let rhs ← L.Arena.hd? a (q + 8)
        pure ({ ctor, nfields, fire := f, rhs } : IRecRule)) = some x →
        (do
        let ctor ← L.Arena.hd? b q
        let nfields ← L.Arena.nat? b (q + 1)
        let rhs ← L.Arena.hd? b (q + 8)
        pure ({ ctor, nfields, fire := f, rhs } : IRecRule)) = some x := by
      intro f hf
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hf ⊢
      obtain ⟨c, hc, nf, hnf, r, hr, e'⟩ := hf
      exact ⟨c, h.hd? hc, nf, h.nat? hnf, r, h.hd? hr, e'⟩
    match t, hx with
    | 0, hx => simp only at hx ⊢; exact tail _ hx
    | 1, hx =>
      cases hy : L.Arena.hlist? (k := .level) a (q + 4) with
      | none => simp [hy] at hx
      | some y =>
        cases hz : L.Arena.hlist? (k := .expr) a (q + 6) with
        | none => simp [hy, hz] at hx
        | some z =>
          rw [hy, hz] at hx; rw [h.hlist? hy, h.hlist? hz]
          simp only [Option.bind_some] at hx ⊢
          exact tail _ hx
    | 2, hx =>
      cases hy : L.Arena.hlist? (k := .level) a (q + 4) with
      | none => simp [hy] at hx
      | some y =>
        rw [hy] at hx; rw [h.hlist? hy]
        simp only [Option.bind_some] at hx ⊢
        exact tail _ hx
    | t + 3, hx => simp at hx

theorem ArrExt.decRules {o c : Nat} {xs : List IRecRule} (hx : decRules a o c = some xs) :
    decRules b o c = some xs :=
  ArrExt.mapM (f := fun j => L.Arena.decRule a (o + 11 * j)) (g := fun j => L.Arena.decRule b (o + 11 * j))
    (fun _ _ hy => h.decRule hy) _ _ hx

theorem ArrExt.decCaps {q : Nat} {x : IIndCaps} (hx : decCaps a q = some x) : decCaps b q = some x := by
  simp only [L.Arena.decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
  obtain ⟨e1, h1, e7, h7, e9, h9, e10, h10, e11, h11, e12, h12, e⟩ := hx
  exact ⟨e1, h.bool? h1, e7, h.nat? h7, e9, h.hlist? h9, e10, h.nat? h10, e11, h.hlist? h11,
    e12, h.bool? h12, e⟩

theorem ArrExt.decTbl {p : Nat} {x : IProjTable} (hx : decTbl a p = some x) : decTbl b p = some x := by
  simp only [L.Arena.decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
  obtain ⟨e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e8, h8, e⟩ := hx
  exact ⟨e2, h.hd? h2, e3, h.hlist? h3, e4, h.nat? h4, e5, h.hd? h5, e6, h.nat? h6,
    e8, h.hlist? h8, e⟩

theorem ArrExt.decCI {p : Nat} {x : IConstantInfo} (hx : decCI a p = some x) : decCI b p = some x := by
  unfold L.Arena.decCI at hx ⊢
  cases hk : L.Arena.nat? a p with
  | none => simp [hk] at hx
  | some k =>
    rw [h.nat? hk]; rw [hk] at hx
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some] at hx ⊢
    match k, hx with
    | 0, hx =>
      simp only [Option.bind_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, e⟩ := hx; exact ⟨y, h.decCV hy, e⟩
    | 1, hx =>
      simp only [Option.bind_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, z, hz, w, hw, e⟩ := hx
      exact ⟨y, h.decCV hy, z, h.hd? hz, w, h.decHint hw, e⟩
    | 2, hx =>
      simp only [Option.bind_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, e⟩ := hx; exact ⟨y, h.decCV hy, e⟩
    | 3, hx =>
      simp only [Option.bind_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, z, hz, e⟩ := hx; exact ⟨y, h.decCV hy, z, h.decCaps hz, e⟩
    | 4, hx =>
      simp only [Option.bind_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, z, hz, w, hw, i, hi, e⟩ := hx
      exact ⟨y, h.decCV hy, z, h.nat? hz, w, h.nat? hw, i, h.hd? hi, e⟩
    | 5, hx =>
      simp only [Option.bind_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, z, hz, w, hw, kk, hkk, o, ho, c, hc, r, hr, e⟩ := hx
      exact ⟨y, h.decCV hy, z, h.nat? hz, w, h.nat? hw, kk, h.bool? hkk, o, h.nat? ho, c, h.nat? hc,
        r, h.decRules hr, e⟩
    | k + 6, hx => simp at hx

end ext

theorem ArrExt.refl (a : Nat → Option Word) : ArrExt a a := fun _ _ h => h

theorem ArrExt.trans {a b c : Nat → Option Word} (h₁ : ArrExt a b) (h₂ : ArrExt b c) : ArrExt a c :=
  fun i v h => h₂ i v (h₁ i v h)

end L.Arena
