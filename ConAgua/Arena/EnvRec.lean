import ConAgua.Arena.StoreRel
import ConRon.Arena.CheckerSplit

/-!
# Environment records in a word pool, and their decoders

The twin's environment values (`IConstantVal`, `IConstantInfo`, `ValueGroup`) are nested: lists
of handles, lists of recursor rules (each with two lists of its own), an `IIndCaps` with four
lists, an `IProjTable` with an `Array`. In L they are **records in a word pool**: a record is a
run of words at a pointer `p`, every list is a slice `(off, cnt)` of the same pool (two words of
the record), and a list of records is a slice of fixed-size records (recursor rules, 11 words). The
decoders below are the value relations (`decE`'s analogue): `decCI dn a p = some ci` says that
the record at `p` in the pool `a` denotes `ci`. They read only the pool, so a pool that only grows
above a top keeps every decoding below it (`PoolSlice`'s `Agree`).

Handle words must be below `2^32` (`hd?` refuses others), so a decoded handle is the word itself
and L may compare words where the twin compares handles. `PropWhen`'s names are con-leche `Name`
values in the twin; in L they are name handles, read back by `dn` (the store's `denoteN`, a
parameter here: the consumers relate it to the store).

## The layouts (offsets from the record pointer `p`)

`IConstantVal` (4 words, at `q`): `name`, `lps.off`, `lps.len`, `type`.

`IConstantInfo` (word `p` is the kind; **word `p + 1` is always the index key** `ci.name`):

| kind | constructor | words |
|---:|---|---|
| 0 | `axiomInfo cv` | cv at `p+1` |
| 1 | `defnInfo cv value hint` | cv at `p+1`; `value` `p+5`; hint `p+6` (0 opaque, 1 abbrev, 2 regular), height `p+7` |
| 2 | `thmInfo cv` | cv at `p+1` |
| 3 | `indInfo cv caps` | cv at `p+1`; caps at `p+5` (15 words, `decCaps`) |
| 4 | `ctorInfo cv np nf` | cv at `p+1`; `p+5`, `p+6` |
| 5 | `recInfo cv major pre rules` | cv at `p+1`; `p+5`, `p+6`; rules slice `p+7`, `p+8` (11-word records) |

`IProjTable` (13 words, at `p`; not a constant: the environment's table component, `Tiers.lean`'s
`EnvR.tbls`/`EnvR.tables`): word `p` is `6` (the kind word of the constant records, which a table
record shares so that the fields keep their offsets), `p+1` the **next table** of the tables list
(`IEnv.tables`, newest first: the next record's pointer plus one, `0` at the end), `structName`
`p+2`, lps `p+3`,`p+4`, `numParams` `p+5`, `ctor` `p+6`, `numFields` `p+7`, `structSort` `p+8`,
bodies `p+9`,`p+10`, guards `p+11`,`p+12`.

The declarations themselves are the front's records (`DECL`/`DLP`, `Front/StateDR.lean`'s
`DeclsF`); an inductive block will need a slice of constant records (not yet).

`ValueGroup` (6 words): `kind` (0 defn, 1 thm, 2 opaque), cv (4 words), `jv`. A `PendingCheck`
is three words of `PEND` (`Checker.lean`): the value group's record pointer, `pos`, `vis`.
-/

namespace L.Arena

open ConRon.Arena

section dec
variable (a : Array Word)

/-- Word `i`, a natural number. -/
def nat? (i : Nat) : Option Nat := (a[i]?).map (·.toNat)

/-- Word `i`, a `Bool` (`0` is `false`). -/
def bool? (i : Nat) : Option Bool := (a[i]?).map (· != 0)

/-- Word `i`, a handle (a word below `2^32`). -/
def hd? {k : IdxKind} (i : Nat) : Option (Idx k) := do
  let w ← a[i]?
  if w.toNat < 2 ^ 32 then some (decI w) else none

/-- The handles at `off`, …, `off + len - 1`. -/
def hslice? {k : IdxKind} (off cnt : Nat) : Option (List (Idx k)) :=
  (List.range cnt).mapM fun j => hd? a (off + j)

/-- The handle list whose slice `(off, cnt)` is at words `i`, `i + 1`. -/
def hlist? {k : IdxKind} (i : Nat) : Option (List (Idx k)) := do
  hslice? a (← nat? a i) (← nat? a (i + 1))

/-- `IConstantVal` at `q`. -/
def decCV (q : Nat) : Option IConstantVal := do
  pure ⟨← hd? a q, ← hlist? a (q + 1), ← hd? a (q + 3)⟩

/-- A reducibility hint at `q` (kind) and `q + 1` (height). -/
def decHint (q : Nat) : Option ConLeche.ReducibilityHint := do
  match ← nat? a q with
  | 0 => pure .opaque
  | 1 => pure .abbrev
  | 2 => pure (.regular (← nat? a (q + 1)))
  | _ => none

/-- A recursor rule: an 11-word record at `q` (`ctor`, `nfields`, `ctorParams`, fire kind (0 plain,
1 nested), the fire's level slice, its pin slice, `rhs`, `k`, `eta`). -/
def decRule (q : Nat) : Option IRecRule := do
  let fire ← match ← nat? a (q + 3) with
    | 0 => some IRecRuleFire.plain
    | 1 => some (IRecRuleFire.nested (← hlist? a (q + 4)) (← hlist? a (q + 6)))
    | _ => none
  pure { ctor := ← hd? a q, nfields := ← nat? a (q + 1), ctorParams := ← nat? a (q + 2), fire,
         rhs := ← hd? a (q + 8), k := ← bool? a (q + 9), eta := ← bool? a (q + 10) }

/-- The rules of the slice `(off, cnt)` of 11-word records. -/
def decRules (off cnt : Nat) : Option (List IRecRule) :=
  (List.range cnt).mapM fun j => decRule a (off + 11 * j)

variable (dn : NIdx → Option ConLeche.Name)

/-- `PropWhen` at `q` (0 `never`, 1 `ifAllZero` with the name slice at `q + 1`, `q + 2`). -/
def decPW (q : Nat) : Option ConLeche.PropWhen := do
  match ← nat? a q with
  | 0 => pure .never
  | 1 => pure (.ifAllZero (← (← hlist? a (q + 1) : List NIdx).mapM dn))
  | _ => none

/-- `IIndCaps`: 15 words at `q` (`eta`, `etaCtor`, `etaParams`, `etaFields`, `unitlike`,
`unitParams`, `ruleK`, `sortZ` (3), `all` (2), `nparams`, `ctors` (2)). -/
def decCaps (q : Nat) : Option IIndCaps := do
  pure { eta := ← bool? a q, etaCtor := ← hd? a (q + 1), etaParams := ← nat? a (q + 2),
         etaFields := ← nat? a (q + 3), unitlike := ← bool? a (q + 4),
         unitParams := ← nat? a (q + 5), ruleK := ← bool? a (q + 6), sortZ := ← decPW a dn (q + 7),
         all := ← hlist? a (q + 10), nparams := ← nat? a (q + 12), ctors := ← hlist? a (q + 13) }

/-- `IProjTable` at `p` (a table record; word `p + 1`, the list link, is not part of it). -/
def decTbl (p : Nat) : Option IProjTable := do
  pure { structName := ← hd? a (p + 2),
         levelParams := ← hlist? a (p + 3), numParams := ← nat? a (p + 5), ctor := ← hd? a (p + 6),
         numFields := ← nat? a (p + 7), structSort := ← hd? a (p + 8),
         bodies := (← hlist? a (p + 9)).toArray, guards := ← hlist? a (p + 11) }

/-- **The tables list** (`IEnv.tables`, newest first): `k` table records linked from `h` (a
record pointer plus one; word `p + 1` of each record links the next). -/
def tblList : Nat → Nat → Option (List IProjTable)
  | 0, _ => some []
  | k + 1, h => if h = 0 then none else do
      let t ← decTbl a (h - 1)
      let ts ← tblList k (← nat? a (h - 1 + 1))
      pure (t :: ts)

/-- **The constant record at `p`.** -/
def decCI (p : Nat) : Option IConstantInfo := do
  match ← nat? a p with
  | 0 => pure (.axiomInfo (← decCV a (p + 1)))
  | 1 => pure (.defnInfo (← decCV a (p + 1)) (← hd? a (p + 5)) (← decHint a (p + 6)))
  | 2 => pure (.thmInfo (← decCV a (p + 1)))
  | 3 => pure (.indInfo (← decCV a (p + 1)) (← decCaps a dn (p + 5)))
  | 4 => pure (.ctorInfo (← decCV a (p + 1)) (← nat? a (p + 5)) (← nat? a (p + 6)))
  | 5 => pure (.recInfo (← decCV a (p + 1)) (← nat? a (p + 5)) (← nat? a (p + 6))
      (← decRules a (← nat? a (p + 7)) (← nat? a (p + 8))))
  | _ => none

/-- A value kind (0 defn, 1 thm, 2 opaque). -/
def decVK : Nat → Option ValueKind
  | 0 => some .defn | 1 => some .thm | 2 => some .opaque
  | _ => none

/-- A value group: 6 words at `q`. -/
def decVG (q : Nat) : Option ValueGroup := do
  pure ⟨← decVK (← nat? a q), ← decCV a (q + 1), ← hd? a (q + 5)⟩

end dec

end L.Arena

/-! ## Decoding is stable under extension

A decoder reads `a[i]?` only; a successful decoding read only words that exist, so it decodes
the same in any array that agrees there (`ArrExt`). This is how a record pool that only grows
above its top (`erecP`, `Tiers.lean`) keeps every decoding below it. -/

namespace L.Arena

open ConRon.Arena

/-- `b` extends `a`: every word of `a` is in `b`. -/
def ArrExt (a b : Array Word) : Prop := ∀ (i : Nat) (v : Word), a[i]? = some v → b[i]? = some v

section ext
variable {a b : Array Word} (h : ArrExt a b)
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
        let ctorParams ← L.Arena.nat? a (q + 2)
        let rhs ← L.Arena.hd? a (q + 8)
        let k ← L.Arena.bool? a (q + 9)
        let eta ← L.Arena.bool? a (q + 10)
        pure ({ ctor, nfields, ctorParams, fire := f, rhs, k, eta } : IRecRule)) = some x →
        (do
        let ctor ← L.Arena.hd? b q
        let nfields ← L.Arena.nat? b (q + 1)
        let ctorParams ← L.Arena.nat? b (q + 2)
        let rhs ← L.Arena.hd? b (q + 8)
        let k ← L.Arena.bool? b (q + 9)
        let eta ← L.Arena.bool? b (q + 10)
        pure ({ ctor, nfields, ctorParams, fire := f, rhs, k, eta } : IRecRule)) = some x := by
      intro f hf
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hf ⊢
      obtain ⟨c, hc, nf, hnf, cp, hcp, r, hr, k, hk, e, he, e'⟩ := hf
      exact ⟨c, h.hd? hc, nf, h.nat? hnf, cp, h.nat? hcp, r, h.hd? hr, k, h.bool? hk, e, h.bool? he, e'⟩
    match t, hx with
    | 0, hx => simp only [Option.bind_some] at hx ⊢; exact tail _ hx
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
    | t + 2, hx => simp at hx

theorem ArrExt.decRules {o c : Nat} {xs : List IRecRule} (hx : decRules a o c = some xs) :
    decRules b o c = some xs :=
  ArrExt.mapM (f := fun j => L.Arena.decRule a (o + 11 * j)) (g := fun j => L.Arena.decRule b (o + 11 * j))
    (fun _ _ hy => h.decRule hy) _ _ hx

theorem ArrExt.decPW {dn : NIdx → Option ConLeche.Name} {q : Nat} {x : ConLeche.PropWhen}
    (hx : decPW a dn q = some x) : decPW b dn q = some x := by
  simp only [L.Arena.decPW, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
  obtain ⟨k, hk, e⟩ := hx
  refine ⟨k, h.nat? hk, ?_⟩
  split at e
  · exact e
  · simp only [Option.bind_eq_some_iff, Option.pure_def] at e ⊢
    obtain ⟨y, hy, z, hz, e⟩ := e; exact ⟨y, h.hlist? hy, z, hz, e⟩
  · exact e

theorem ArrExt.decCaps {dn : NIdx → Option ConLeche.Name} {q : Nat} {x : IIndCaps}
    (hx : decCaps a dn q = some x) : decCaps b dn q = some x := by
  simp only [L.Arena.decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
  obtain ⟨e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, e10, h10, e11, h11, e⟩ := hx
  exact ⟨e1, h.bool? h1, e2, h.hd? h2, e3, h.nat? h3, e4, h.nat? h4, e5, h.bool? h5, e6, h.nat? h6,
    e7, h.bool? h7, e8, h.decPW h8, e9, h.hlist? h9, e10, h.nat? h10, e11, h.hlist? h11, e⟩

theorem ArrExt.decTbl {p : Nat} {x : IProjTable} (hx : decTbl a p = some x) : decTbl b p = some x := by
  simp only [L.Arena.decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
  obtain ⟨e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, e⟩ := hx
  exact ⟨e2, h.hd? h2, e3, h.hlist? h3, e4, h.nat? h4, e5, h.hd? h5, e6, h.nat? h6,
    e7, h.hd? h7, e8, h.hlist? h8, e9, h.hlist? h9, e⟩

theorem ArrExt.tblList : ∀ {k h : Nat} {x : List IProjTable}, tblList a k h = some x →
    tblList b k h = some x
  | 0, _, _, hx => hx
  | k + 1, h', x, hx => by
    unfold L.Arena.tblList at hx ⊢
    by_cases h0 : h' = 0
    · simp [h0] at hx
    · simp only [h0, ite_false, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
      obtain ⟨t, ht, n, hn, ts, hts, e⟩ := hx
      exact ⟨t, h.decTbl ht, n, h.nat? hn, ts, ArrExt.tblList hts, e⟩

theorem ArrExt.decCI {dn : NIdx → Option ConLeche.Name} {p : Nat} {x : IConstantInfo}
    (hx : decCI a dn p = some x) : decCI b dn p = some x := by
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
      obtain ⟨y, hy, z, hz, w, hw, e⟩ := hx
      exact ⟨y, h.decCV hy, z, h.nat? hz, w, h.nat? hw, e⟩
    | 5, hx =>
      simp only [Option.bind_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, z, hz, w, hw, o, ho, c, hc, r, hr, e⟩ := hx
      exact ⟨y, h.decCV hy, z, h.nat? hz, w, h.nat? hw, o, h.nat? ho, c, h.nat? hc, r, h.decRules hr, e⟩
    | k + 6, hx => simp at hx

theorem ArrExt.decVG {q : Nat} {x : ValueGroup} (hx : decVG a q = some x) : decVG b q = some x := by
  simp only [L.Arena.decVG, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx ⊢
  obtain ⟨n, hn, c, hc, cv, hcv, j, hj, e⟩ := hx
  exact ⟨n, h.nat? hn, c, hc, cv, h.decCV hcv, j, h.hd? hj, e⟩

end ext

theorem ArrExt.refl (a : Array Word) : ArrExt a a := fun _ _ h => h

theorem ArrExt.trans {a b c : Array Word} (h₁ : ArrExt a b) (h₂ : ArrExt b c) : ArrExt a c :=
  fun i v h => h₂ i v (h₁ i v h)

end L.Arena
