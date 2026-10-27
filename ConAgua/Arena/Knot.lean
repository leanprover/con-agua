import ConAgua.Arena.WhnfBase

/-!
# The knot's `infer`, `infer_io`, `defeq` and eager slots, and the fueled entry points (lane `defeq`)

con-ron's `coreKnot` (`Arena/Core.lean:3532-3640`) ties the bodies together; in L the record is
the program and each slot is an L function (`WhnfBase.lean`, "The knot's slots"). Lane `whnf`
wrote the two `whnf` slots (`whnf_core`, `whnf`); this file has the other four:

| L | twin slot | memo (`CoreCaches.lean`) |
|---|---|---|
| `infer(mode, vis, d, e)` | `infer`: `inferC`, `inferBody` | `in` (array 99), key `(e, genW 0 eb)` |
| `infer_io(mode, vis, d, e)` | `inferIO`: `inferIOC`, `inferBodyIO` at the io view | `io` (array 100) |
| `defeq(mode, vis, d, a, b)` | `defeq`: `defeqC`, `defeqBody` | `de` (array 101), key `(a, genW b eb)`, value `Bool` |
| `defeq_e(mode, vis, d, a, b)` | `defeqE`: the eager tower | `defeq` at `mode ∣ 2` |

`eb` is the mode's eager bit `(mode >> 1) & 1` (`SlotPre.eb_mode`). A miss runs the body, probes
again (the body may have changed the table) and inserts, as `whnf`/`whnf_core` do.

**The eager slot.** The twin's `defeqE` at knot level `F + 1` swaps the eager tower's memos into
the six fields (`enterEager`, from a plain mode), probes `defeqC`, runs `defeqBody mode.toEager`
at the knot `coreKnot mode.toEager fe id F`, inserts, and swaps back (`leaveEager`). That is the
`defeq` slot of the knot at `mode.toEager` one level up, run on the eager set; in L each memo
holds both sets keyed by the eager bit (lane `whnf`'s design), so `defeq_e` is `defeq` at the mode
word with bit 1 set (`toEager`: `0 ↦ 2`, `1 ↦ 3`, eager modes fixed) and moves nothing.

**The entry points** (`Core.lean:3649-3675`, at `checkFuel`, uncounted): the conventions of lane
`induct`'s and lane `decls`' call sites (`IndIface.lean`'s `stubFns`, `DeclStep.lean`), at the
verified mode: `infer_type_core(vis, dep, e)`, `is_def_eq_core(vis, dep, a, b)`,
`ensure_sort_core(vis, dep, t)`. These replace the stubs of the same names in a whole program.

**Callees** (`DefeqCallees`): `has_fvar`, `abs_entry`, `ar_entry` are the phase-4 walks under
`CoreS` at exactly `coreWalkFuel` (`CoreWalks.lean`); `field_sort_zero` is `InferFieldSort.lean`;
`not_proof_fast`/`is_proof_fast` (`PropRead`) are `KnotCallees` fields until their proofs land.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The slots -/

/-- con-ron: ConRon/Arena/Core.lean:3528-3618 ConRon.Arena.coreKnot
con-ron: ConRon/Arena/Core.lean:3469-3475 ConRon.Arena.inferSet -/
@[l_impl ConRon.Arena.coreKnot ConRon.Arena.inferSet]
def inferSlotL : FunDecl := lfn (mode, vis, d, e) locals (k, fd, j, dd, x, z) {
  k := ((mode >> 1) & 1) << 32;
  (fd, j, dd) := call in_find(e, k);
  if fd != 0 { return inSch.arr.u64[j * 4 + 3] };
  x := call infer_body(mode, vis, d, e);
  (fd, j, dd) := call in_find(e, k);
  z := call in_put(e, k, x, fd, j);
  return x
}

/-- con-ron: ConRon/Arena/Core.lean:3528-3618 ConRon.Arena.coreKnot
con-ron: ConRon/Arena/Core.lean:3477-3484 ConRon.Arena.inferIOSet
con-ron: ConRon/Arena/Core.lean:266-271 ConRon.Arena.CoreFnsA.ioView -/
@[l_impl ConRon.Arena.coreKnot ConRon.Arena.inferIOSet ConRon.Arena.CoreFnsA.ioView]
def inferIOSlotL : FunDecl := lfn (mode, vis, d, e) locals (k, fd, j, dd, x, z) {
  k := ((mode >> 1) & 1) << 32;
  (fd, j, dd) := call io_find(e, k);
  if fd != 0 { return ioSch.arr.u64[j * 4 + 3] };
  x := call infer_body_io(mode, vis, d, e);
  (fd, j, dd) := call io_find(e, k);
  z := call io_put(e, k, x, fd, j);
  return x
}

/-- con-ron: ConRon/Arena/Core.lean:3528-3618 ConRon.Arena.coreKnot
con-ron: ConRon/Arena/Core.lean:3486-3493 ConRon.Arena.defeqSet -/
@[l_impl ConRon.Arena.coreKnot ConRon.Arena.defeqSet]
def defeqSlotL : FunDecl := lfn (mode, vis, d, a, b) locals (k, fd, j, dd, x, z) {
  k := b | (((mode >> 1) & 1) << 32);
  (fd, j, dd) := call de_find(a, k);
  if fd != 0 { return u64(deSch.arr.u64[j * 4 + 3] != 0) };
  x := call defeq_body(mode, vis, d, a, b);
  (fd, j, dd) := call de_find(a, k);
  z := call de_put(a, k, x, fd, j);
  return x
}

/-- con-ron: ConRon/Arena/Core.lean:3528-3618 ConRon.Arena.coreKnot
con-ron: ConRon/Arena/Core.lean:3495-3510 ConRon.Arena.enterEager
con-ron: ConRon/Arena/Core.lean:3512-3526 ConRon.Arena.leaveEager -/
@[l_impl ConRon.Arena.coreKnot ConRon.Arena.enterEager ConRon.Arena.leaveEager]
def defeqESlotL : FunDecl := lfn (mode, vis, d, a, b) locals (r) {
  r := call defeq(mode | 2, vis, d, a, b);
  return r
}

/-! ## The entry points (the verified mode, `checkFuel`) -/

/-- con-ron: ConRon/Arena/Core.lean:3650-3654 ConRon.Arena.inferTypeCore
con-ron: ConRon/Arena/Core.lean:3636-3642 ConRon.Arena.pureFnsA -/
@[l_impl ConRon.Arena.inferTypeCore ConRon.Arena.pureFnsA]
def inferTypeCoreL : FunDecl := lfn (vis, dep, e) locals (r) {
  r := call infer(0, vis, dep, e);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3656-3660 ConRon.Arena.isDefEqCore -/
@[l_impl ConRon.Arena.isDefEqCore]
def isDefEqCoreL : FunDecl := lfn (vis, dep, a, b) locals (r) {
  r := call defeq(0, vis, dep, a, b);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3662-3666 ConRon.Arena.ensureSortCore -/
@[l_impl ConRon.Arena.ensureSortCore]
def ensureSortCoreL : FunDecl := lfn (vis, dep, t) locals (r) {
  r := call ensure_sort(0, vis, dep, t);
  return r
}

end L.Arena

/-! ## The callees' specs

Each is a named L function with the spec of its twin (`CoreSpec`, `WhnfBase.lean`); `DefeqCallees p`
bundles them. `DefEqKnot.lean` builds it: the walks from `CoreWalks.lean`, `field_sort_zero` from
`InferFieldSort.lean`, the `PropRead` readers from `KnotCallees`. The callees lane `whnf` specifies
(`inst_list`, `inst_lp`, `str_lit_*`: `WhnfCallees`; `inst1`, `find_proj`: `CoreCallees`) are not
repeated. -/

namespace L.Arena

/-- `inferProj`'s propositional-structure test on the readbacks: the field's sort, at the
subject's levels, is equivalent to `Prop` (`none` is "not `some true`"). -/
def fieldSortZeroT (lps : List NIdx) (us : LsIdx) (fs : LIdx) : AM Bool := do
  let ks ← readNamesM lps
  let vs ← readLevelsM us
  let f ← readLevelM fs
  pure (ConLeche.Level.isEquiv (ConLeche.Level.subst ks vs f) .zero == some true)

/-- `has_fvar(e)` refines `hasFvarFast coreWalkFuel e` (phase 4: `fvarB` with the counter). -/
def HasFvarOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
    CoreSpec p n "has_fvar" [e] (hasFvarFast coreWalkFuel (decE e)) decBool s₀ a₀ dn vis fe M eb

/-- `not_proof_fast(vis, a)` refines `notProofFast fe coreWalkFuel a` (`PropRead.lean`, phase 2). -/
def NotProofFastOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb x : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW x →
    CoreSpec p n "not_proof_fast" [vis, x] (notProofFast fe coreWalkFuel (decE x)) decBool s₀ a₀
      dn vis fe M eb

/-- `is_proof_fast(vis, a)` refines `isProofFast fe coreWalkFuel a` (`PropRead.lean`, phase 2). -/
def IsProofFastOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb x : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW x →
    CoreSpec p n "is_proof_fast" [vis, x] (isProofFast fe coreWalkFuel (decE x)) decBool s₀ a₀
      dn vis fe M eb

/-- `abs_entry(e, d, k)` refines `abstract1Fast coreWalkFuel e d k` (phase 4). -/
def Abstract1OK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e d k : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
    CoreSpec p n "abs_entry" [e, d, k] (abstract1Fast coreWalkFuel (decE e) d.toNat k.toNat) decH
      s₀ a₀ dn vis fe M eb

/-- `ar_entry(e, d, k, c)` refines `abstractRangeFast coreWalkFuel e d k c` (phase 4). -/
def AbstractRangeOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e d k c : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
    CoreSpec p n "ar_entry" [e, d, k, c]
      (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat) decH s₀ a₀ dn vis fe M eb

/-- `field_sort_zero(po, pl, us, fs)` refines `fieldSortZeroT` (the level parameters an `EREC`
slice; `InferFieldSort.lean`). The twin's three readbacks fail on a dangling handle, which L
cannot see: the caller supplies that they succeed (and that the name cache holds readbacks). -/
def FieldSortZeroOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb po pl us fs : Word) (lps : List NIdx), CoreS dn s₀.mem a₀ vis fe M eb →
    HW us → HW fs → hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps →
    ReadNCOK a₀ → (∃ ks, lps.mapM (denoteN a₀.store.ns) = some ks) →
    (∃ ls, denoteLs a₀.store.lss (decI us) = some ls) →
    (∃ l, denoteL a₀.store.ls (decI fs) = some l) →
    CoreSpec p n "field_sort_zero" [po, pl, us, fs] (fieldSortZeroT lps (decI us) (decI fs)) decBool
      s₀ a₀ dn vis fe M eb

/-- **The leaf callees of phases 6 and 7.** -/
structure DefeqCallees (p : Prog) : Prop where
  hasFvar : HasFvarOK p
  notProofFast : NotProofFastOK p
  isProofFast : IsProofFastOK p
  abstract1 : Abstract1OK p
  abstractRange : AbstractRangeOK p
  fieldSortZero : FieldSortZeroOK p

end L.Arena
