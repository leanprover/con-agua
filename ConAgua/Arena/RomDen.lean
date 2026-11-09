module

public import ConAgua.Arena.IndDecStab
public import ConRon.Arena.Checker

@[expose] public section

/-!
# The ROM cache's denotation (`RomDen`, lane `ronsync2`)

The checks read the structured ROM constants from the startup cache (`ROMC`, filled by `rom_fill`;
`ConAgua/Rom/CIRead.lean`): words `2 k`, `2 k + 1` the `EREC` slice of record addresses of block
`k` (`0‥4` the basis blocks, `5` the pinned `And`), `12 + id` the `rom_ci` record, `19 + id` the
`rom_cv` record, `29 + id` the `rom_expr_pin` handle. The twin interns each constant at each use.
`RomDen m a` is what makes a cached read a refinement of that intern:

* **the values** `R : RomVals`, one per cached constant;
* **the memory** (`RomMem R m`): the cache's words decode to `R` in the tier-0 records (`er0A`:
  below the tops, and independent of tier 1, which every job empties), the blocks as `EREC`
  slices of record addresses (`erPL`), which `er_to_iw` copies into `IW`;
* **the twin** (`RomTw R (persKey a)`): at every state with `a`'s persistent tables, each intern
  is a no-op hit returning `R`'s value. Every ROM constant is interned into the persistent tier
  at startup (`internAllPins`, the scratch tier off) and the persistent tables only change when a
  step interns with the scratch tier off, so the twin half is carried by `persKey a' = persKey a`.

`RomDen` is a field of `TwinOK` (`DeclLvlStage.lean`): the cached readers' refinements
(`ConAgua/Rom/CIReadSpec.lean`) are stated under `StageT`.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## The twin's values by the readers' ids -/

/-- `rom_ci(id)`'s constant. -/
def romCiT : Nat → AM IConstantInfo
  | 0 => natA | 1 => iffA | 2 => iffIntroA | 3 => iffRecA | 4 => nonemptyA
  | 5 => nonemptyIntroA | _ => nonemptyRecA

/-- `rom_cv(id)`'s constant value. -/
def romCvT : Nat → AM IConstantVal
  | 0 => propextA | 1 => choiceA | 2 => trueCvA | 3 => trueIntroCvA | 4 => trustCompilerA
  | 5 => boolCvA | 6 => reduceNatCvA | 7 => reduceBoolCvA | 8 => ofReduceNatA | _ => ofReduceBoolA

/-- `rom_expr_pin(id)`'s expression. -/
def romExprT : Nat → AM EIdx
  | 0 => reduceNatDeclPin | _ => reduceBoolDeclPin

/-- The basis block of `rom_basis_decls(kind)`'s word. -/
def basisOfW : Nat → ConLeche.BasisKind
  | 0 => .eqK | 1 => .natK | 2 => .emptyK | 3 => .falseK | _ => .quotK

/-- The cached block `k`'s twin: the basis blocks `0‥4`, the pinned `And` at `5`. -/
def romBlkT (k : Nat) : AM (List IConstantInfo) :=
  if k < 5 then ConRon.Arena.BasisKind.decls (basisOfW k) else andPinDecls

end L.Ind

namespace L.Arena

open L.Ind

/-! ## The cache -/

/-- Word `i` of the cache `ROMC`. -/
def romcW (m : Mem) (i : Nat) : Word := rdW (m.arr64 L.Rom.ROMC) (UInt64.ofNat i)

/-- The tier-0 records: `erA` at the addresses below `2 ^ 40` (the cache's records are tier-0
records, written with the scratch tier off; reading them does not depend on tier 1). -/
def er0A (m : Mem) : Nat → Option Word := fun i => if i < 2 ^ 40 then erA m i else none

/-- An `EREC` slice of tier-0 record addresses `(q, l)`, each decoded by `f`. -/
def erPL {α : Type} (m : Mem) (f : Nat → Option α) (q l : Nat) : Option (List α) :=
  (List.range l).mapM fun j => do f (← nat? (er0A m) (q + j))

/-- The cached values: the `rom_ci` constants (`0‥6`), the `rom_cv` values (`0‥9`), the
`rom_expr_pin` handles (`0‥1`), the blocks (`0‥5`). -/
structure RomVals where
  ci : Nat → IConstantInfo
  cv : Nat → IConstantVal
  ex : Nat → EIdx
  blk : Nat → List IConstantInfo

/-- **The cache's memory**: its words decode to `R` in the tier-0 records. -/
structure RomMem (R : RomVals) (m : Mem) : Prop where
  size : 31 ≤ (m.arr64 L.Rom.ROMC).size
  ci : ∀ id, id < 7 → decCI (er0A m) (romcW m (12 + id)).toNat = some (R.ci id)
  cv : ∀ id, id < 10 → decCV (er0A m) (romcW m (19 + id)).toNat = some (R.cv id)
  ex : ∀ id, id < 2 → (romcW m (29 + id)).toNat < 2 ^ 32 ∧ decI (romcW m (29 + id)) = R.ex id
  blk : ∀ k, k < 6 →
    erPL m (decCI (er0A m)) (romcW m (2 * k)).toNat (romcW m (2 * k + 1)).toNat = some (R.blk k)

/-- The twin's persistent tables (all four stores). -/
def persKey (a : AState) : ETables × LsTables × LTables × NTables :=
  (a.store.pers, a.store.lss.pers, a.store.lss.ls.pers, a.store.lss.ls.ns.pers)

/-- **The twin's half**: at every state with the persistent tables `P`, each cached constant's
intern is a no-op hit returning `R`'s value. -/
structure RomTw (R : RomVals) (P : ETables × LsTables × LTables × NTables) : Prop where
  ci : ∀ id, id < 7 → ∀ a, persKey a = P → (romCiT id).run a = .ok (R.ci id, a)
  cv : ∀ id, id < 10 → ∀ a, persKey a = P → (romCvT id).run a = .ok (R.cv id, a)
  ex : ∀ id, id < 2 → ∀ a, persKey a = P → (romExprT id).run a = .ok (R.ex id, a)
  blk : ∀ k, k < 6 → ∀ a, persKey a = P → (romBlkT k).run a = .ok (R.blk k, a)

/-- **The ROM cache's denotation.** -/
def RomDen (m : Mem) (a : AState) : Prop := ∃ R, RomMem R m ∧ RomTw R (persKey a)

/-! ## The tier-0 records -/

/-- The tier-0 records are records. -/
theorem er0A_sub (m : Mem) : ArrExt (er0A m) (erA m) := fun i v h => by
  unfold er0A at h; split at h
  · exact h
  · cases h

/-- They grow with the records. -/
theorem er0A_ext {m m' : Mem} (h : ArrExt (erA m) (erA m')) : ArrExt (er0A m) (er0A m') :=
  fun i v hv => by
    unfold er0A at hv ⊢; split at hv
    · rw [if_pos (by assumption)]; exact h i v hv
    · cases hv

/-- They read tier 0 of `EREC` and its top only. -/
theorem er0A_congr {m m' : Mem} (h1 : m'.arr64 EREC = m.arr64 EREC)
    (h3 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129) : er0A m' = er0A m := by
  funext i
  unfold er0A
  split
  · rename_i hi
    have h0 : i / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt hi]
    simp only [erA, erecP, erecTop, h0, h1, h3, ↓reduceIte]; rfl
  · rfl

/-! ## Transport -/

/-- The cache's memory across a step that leaves `ROMC` alone and only grows the pools. -/
theorem RomMem.ext {R : RomVals} {m m' : Mem} (h : RomMem R m)
    (hR : m'.arr64 L.Rom.ROMC = m.arr64 L.Rom.ROMC) (hx : ArrExt (er0A m) (er0A m')) :
    RomMem R m' := by
  have hw : romcW m' = romcW m := by funext i; simp only [romcW, hR]
  refine ⟨hR ▸ h.size, fun id hid => ?_, fun id hid => ?_, fun id hid => hw ▸ h.ex id hid,
    fun k hk => ?_⟩
  · rw [hw]; exact hx.decCI (h.ci id hid)
  · rw [hw]; exact hx.decCV (h.cv id hid)
  · rw [hw]
    have hb := h.blk k hk
    simp only [erPL] at hb ⊢
    refine ArrExt.mapM (fun j x hj => ?_) _ _ hb
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hj ⊢
    obtain ⟨p, hp, hc⟩ := hj
    exact ⟨p, hx.nat? hp, hx.decCI hc⟩

/-- `RomDen` across a memory step that leaves `ROMC` alone and only grows the pools (the twin
unchanged). -/
theorem RomDen.grow {m m' : Mem} {a : AState} (h : RomDen m a)
    (hR : m'.arr64 L.Rom.ROMC = m.arr64 L.Rom.ROMC) (hg : IWGrow m m') : RomDen m' a :=
  let ⟨R, hm, ht⟩ := h; ⟨R, hm.ext hR (er0A_ext hg.erExt), ht⟩

/-- `RomDen` across a step that keeps `ROMC`, tier 0 of `EREC` and its top (`IW` and tier 1 of
`EREC` may change). -/
theorem RomDen.frame0 {m m' : Mem} {a : AState} (h : RomDen m a)
    (hR : m'.arr64 L.Rom.ROMC = m.arr64 L.Rom.ROMC) (h1 : m'.arr64 EREC = m.arr64 EREC)
    (h3 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129) : RomDen m' a :=
  let ⟨R, hm, ht⟩ := h
  ⟨R, hm.ext hR (by rw [er0A_congr h1 h3]; exact fun _ _ h => h), ht⟩

/-- `RomDen` across a twin step that keeps the persistent tables (the memory unchanged). -/
theorem RomDen.pers {m : Mem} {a a' : AState} (h : RomDen m a) (hp : persKey a' = persKey a) :
    RomDen m a' := by
  obtain ⟨R, hm, ht⟩ := h; exact ⟨R, hm, hp ▸ ht⟩

/-- `RomDen` across a twin step that keeps the store. -/
theorem RomDen.store {m : Mem} {a a' : AState} (h : RomDen m a) (hs : a'.store = a.store) :
    RomDen m a' := h.pers (by simp only [persKey, hs])

end L.Arena
