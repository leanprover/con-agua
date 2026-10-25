module

public import ConLeche.Kernel.Checker
public import ConLeche.Verify.Level
public import ConLeche.Verify.EnvWF
public import ConLeche.Term.Const

public section

/-!
# Denotation of kernel expressions into the term language

`denote cval env φ d e` maps a kernel `Expr` to a `ConLeche.Term.Term`:
the semantics tier's reading of a stored term.

The clauses in one line each:

| `Expr` node | `denote` |
|---|---|
| `.sort u` | `some (.sort (u.eval φ))` |
| `.fvar idx` | `some (.bvar (d - 1 - idx))` |
| `.const n us` | the valuation, `cval n (Level.substFn φ ps us)` |
| `.forallE ty body` | `.pi ⟦ty⟧ ⟦body opened⟧` |
| `.lam ty body` | `.lam ⟦ty⟧ ⟦body opened⟧` |
| `.app f a` | `.app ⟦f⟧ ⟦a⟧` |
| `.proj` | `.fst ⟦e⟧` / `.snd ⟦e⟧` |
| `.lit (.natVal n)` | `natLitT ⟦zero⟧ ⟦succ⟧ n` |
| `.letE ty v b` | `.letE ⟦v⟧ ⟦b opened⟧` — the type must read, and is dropped |

Four properties of that reading are worth stating rather than reading
off the table.

## There is no free-variable valuation

A free variable's term is determined by its own `fvar` index together
with the current depth: `fvar d` opened at depth `d` is de Bruijn index
`0` under one binder, `1` under two, i.e. `.bvar (d' - 1 - d)` at depth
`d'`.  So `denote` takes no environment of variable values — the leaf
clause computes what such an environment would have stored — and the
predicate that constrains the free variables is `CtxOk`, over the de
Bruijn context `Δ`.

## Delta is `rfl`, because `denote` never delta-reduces

`denote` does *not* unfold a constant: it reads the constant's value out
of the valuation `cval`, and the environment invariant records that a
definition's valuation is the denotation of its body.  A delta step in
the checker is therefore an *equation between denotations that already
holds*, not a rule of the type theory — which is the concrete sense in
which the reduction strategy drops out of the consistency argument.
The recursion over the environment lives in the *incremental
construction of the valuation* as declarations install, which is
`EnvModel`'s own induction and needs no separate termination argument.

## A `let` is a former, not a substitution

**Every clause maps a constructor to a constructor.**  That is not
cosmetic.  The principle to preserve, if any clause is ever tempted to
compute:

> **A structural `denote` is what keeps the substitution
> metatheory small.**

A `denote` that performed a substitution — emitting `b.inst ⟦value⟧`
for a `letE` — would force this layer's metatheory to prove that
lifting commutes with instantiation, and then that lifting commutes
with lifting, and the swamp `ConLeche/Term/Subst.lean` is proud of
avoiding (lean4lean's 123 syntactic lemmas) would reappear one layer
down.  So a stored `let` (terms keep their `let`s as Lean writes them)
denotes the `letE` former: the value, and the body opened at a fresh
variable, exactly as a binder's body.  The type must read (its
constants resolve) and is dropped.  ζ is a theorem about the
interpretation (`interp_zeta`), not a clause here.

## Projections, and why the layer grew a former for them

A `.proj` node carries an index and a subject, and nothing else: the
pair's type arguments `A` and `B` are not in it — the checker recovers
them at *use* time, by whnf-ing the subject's inferred type
(`ConLeche/Kernel/Core.lean`, the `.proj` clause of `inferBody`).  A
denotation that is a function of the expression alone therefore cannot
emit a constant applied to `A` and `B`, and a *relational* denotation is
not an option either: the defeq claim of the fuel induction needs both
sides denoted by the *same* function, or the two existentials do not
meet.

So the term language has untyped projection formers
(`ConLeche/Term/Syntax.lean`: `fst`/`snd`), carrying exactly what the
checker's node carries beyond the index, and typed by reading `A` and
`B` off the premise.  This clause reads field `i` of a structure (one
with a projection table) as the iterated spelling `projNV (i + 1)`,
behind the constructor's tag; a projection from anything without a
table has no image.  The alphabet comes out *smaller* for it: the
projections are derivable from the formers and are not `BConst`s.
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

/-- The term of a `Nat` literal: the `Nat.succ` valuation iterated on
the `Nat.zero` valuation.

Note that this is *unary and never evaluated*: nothing computes it, and the literal fast paths are discharged by lemma
families proved by meta-level induction on the literal (task #119, the
`Nat` interface), never by exhibiting a derivation of the size of the
numeral. -/
@[expose] def natLitT (zv sv : Term) : Nat → Term
  | 0 => zv
  | n + 1 => .app sv (natLitT zv sv n)

/-- The character-list part of a string literal's constructor form. -/
@[expose] def charListT (nilV consV ofNatV zv sv : Term) : List Char → Term
  | [] => nilV
  | c :: cs =>
    .app (.app consV (.app ofNatV (natLitT zv sv c.toNat)))
      (charListT nilV consV ofNatV zv sv cs)

/-- The stored level-parameter list of a constant (`[]` when absent). -/
@[expose] def levelParamsAt (env : Env) (n : Name) : List Name :=
  match env.find? n with
  | some ci => ci.toConstantVal.levelParams
  | none => []

/-- The tower projection's `Term` spelling (task #175 wiring W3):
`.fst ∘ .snd^i`, interpreting to `projS i` on the tuple
tier's carriers.  Depends only on the index. -/
@[expose] def projNV : Nat → Term → Term
  | 0, e => .fst e
  | i + 1, e => projNV i (.snd e)

/-- `projNV` commutes with lifting (it introduces no binders). -/
theorem projNV_liftN :
    ∀ (i : Nat) (e : Term) (n k : Nat),
      (projNV i e).liftN n k = projNV i (e.liftN n k)
  | 0, _, _, _ => rfl
  | i + 1, e, n, k => projNV_liftN i (.snd e) n k

/-- `projNV` commutes with instantiation. -/
theorem projNV_inst :
    ∀ (i : Nat) (e a : Term) (k : Nat),
      (projNV i e).inst a k = projNV i (e.inst a k)
  | 0, _, _, _ => rfl
  | i + 1, e, a, k => projNV_inst i (.snd e) a k

/-- Denote an expression under constant valuation `cval` (each
constant's term, level-polymorphically: a function of the
level-parameter assignment), level assignment `φ` and binder depth
`d`.  See the module docstring, in particular for the absent
free-variable valuation, for `letE`, and for the `.proj` clause. -/
@[expose] def denote (cval : Name → (Name → Nat) → Term) (env : Env)
    (φ : Name → Nat) : (d : Nat) → Expr → Option Term
  | _, .sort u => some (.sort (u.eval φ))
  | d, .fvar idx _ => some (.bvar (d - 1 - idx))
  | _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, .forallE ty body => do
    let A ← denote cval env φ d ty
    let B ← denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty))
    some (.pi A B)
  | d, .lam ty body => do
    let A ← denote cval env φ d ty
    let b ← denote cval env φ (d + 1) (body.instantiate1 (.fvar d ty))
    some (.lam A b)
  | d, .app f a => do
    let vf ← denote cval env φ d f
    let va ← denote cval env φ d a
    some (.app vf va)
  | d, .letE ty v b => do
    -- the type must read (its constants resolve, as everywhere in a
    -- stored term), but the reading drops it: nothing reads a `let`'s
    -- type.  The body is opened at a fresh variable, as a binder's
    -- (see "A `let` is a former" above).
    let _ ← denote cval env φ d ty
    let vv ← denote cval env φ d v
    let B ← denote cval env φ (d + 1) (b.instantiate1 (.fvar d ty))
    some (.letE vv B)
  | d, .proj sn i e => do
    -- a structure's field `i` behind the constructor's tag (task #175
    -- wiring W3; the tag is always there, task #362): the entry key
    -- consumed at the reading, never carried in the syntax
    let ve ← denote cval env φ d e
    match env.findProj? sn i with
    | some _ => some (projNV (i + 1) ve)
    | none => none
  | _, .lit (.natVal n) =>
    -- guarded exactly like the checker's literal paths
    if natLitSupported env then
      some (natLitT (cval natZeroName (Level.substFn φ [] []))
        (cval natSuccName (Level.substFn φ [] [])) n)
    else none
  | _, .lit (.strVal s) =>
    -- the denotation of the constructor form (`strLitToConstructor`),
    -- written out: each constant valued exactly as the `.const`
    -- clause values it on that form
    if strLitSupported env then
      some (.app (cval stringOfListName (Level.substFn φ [] []))
        (charListT
          (.app (cval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (cval charName (Level.substFn φ [] [])))
          (.app (cval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (cval charName (Level.substFn φ [] [])))
          (cval charOfNatName (Level.substFn φ [] []))
          (cval natZeroName (Level.substFn φ [] []))
          (cval natSuccName (Level.substFn φ [] []))
          s.toList))
    else none
  | _, _ => none
termination_by _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Denotation of a closed expression (as they appear in declarations). -/
@[expose] def denoteClosed (cval : Name → (Name → Nat) → Term) (env : Env) (φ : Name → Nat)
    (e : Expr) : Option Term :=
  denote cval env φ 0 e

/-! ## Clause equations

`denote` is defined by well-founded recursion on `Expr.sizeB`, so its
clauses are not definitional; these are the rewrite rules every
consumer uses. -/

section
variable {env : Env} {φ : Name → Nat}

theorem denote_sort (acval : Name → (Name → Nat) → Term)
    (d : Nat) (u : Level) :
    denote acval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denote]

theorem denote_fvar (acval : Name → (Name → Nat) → Term)
    (d idx : Nat) (ty : Expr) :
    denote acval env φ d (.fvar idx ty)
      = some (.bvar (d - 1 - idx)) := by
  rw [denote]

@[simp] theorem denote_bvar (acval : Name → (Name → Nat) → Term)
    (d i : Nat) : denote acval env φ d (.bvar i) = none := by
  rw [denote] <;> simp

theorem denote_const {acval : Name → (Name → Nat) → Term}
    {d : Nat} {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    denote acval env φ d (.const n us)
      = some (acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) := by
  rw [denote, hf]
  simp [hlen]

theorem denote_app (acval : Name → (Name → Nat) → Term)
    (d : Nat) (f a : Expr) :
    denote acval env φ d (.app f a)
      = (do
        let fa ← denote acval env φ d f
        let aa ← denote acval env φ d a
        some (.app fa aa)) := by
  rw [denote]

theorem denote_proj (acval : Name → (Name → Nat) → Term)
    (d : Nat) (s : Name) (i : Nat) (e : Expr) :
    denote acval env φ d (.proj s i e)
      = (do
        let ea ← denote acval env φ d e
        match env.findProj? s i with
        | some _ => some (projNV (i + 1) ea)
        | none => none) := by
  rw [denote]

theorem denote_forallE (acval : Name → (Name → Nat) → Term)
    (d : Nat) (ty body : Expr) :
    denote acval env φ d (.forallE ty body)
      = (do
        let ta ← denote acval env φ d ty
        let ba ← denote acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.pi ta ba)) := by
  rw [denote]

theorem denote_lam (acval : Name → (Name → Nat) → Term)
    (d : Nat) (ty body : Expr) :
    denote acval env φ d (.lam ty body)
      = (do
        let ta ← denote acval env φ d ty
        let ba ← denote acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.lam ta ba)) := by
  rw [denote]

theorem denote_letE (acval : Name → (Name → Nat) → Term)
    (d : Nat) (ty v body : Expr) :
    denote acval env φ d (.letE ty v body)
      = (do
        let _ ← denote acval env φ d ty
        let va ← denote acval env φ d v
        let ba ← denote acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.letE va ba)) := by
  rw [denote]

theorem denote_natLit {acval : Name → (Name → Nat) → Term}
    {d n : Nat} (hg : natLitSupported env = true) :
    denote acval env φ d (.lit (.natVal n))
      = some (natLitT (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] [])) n) := by
  rw [denote, ite_eq_left hg]

theorem denote_strLit {acval : Name → (Name → Nat) → Term}
    {d : Nat} {s : String} (hg : strLitSupported env = true) :
    denote acval env φ d (.lit (.strVal s))
      = some (.app (acval stringOfListName (Level.substFn φ [] []))
        (charListT
          (.app (acval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (.app (acval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (acval charOfNatName (Level.substFn φ [] []))
          (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] []))
          s.toList)) := by
  rw [denote, ite_eq_left hg]

end

end ConLeche.Verify
