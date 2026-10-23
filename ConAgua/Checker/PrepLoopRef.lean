import ConAgua.Checker.PrepLeafRef

/-!
# `prepare_prelude`'s loops: `prep_front` refines `frontOf`, `prep_rest` its rest (lane `front4`)

The stream not yet picked is the list of stream positions `x ∈ [np, n)` not marked in `mk`
(`unm`): the twin's array after `pick`'s erasures is that list mapped through the records. Each
prelude record `a` is replaced by the first such record declaring its key (marked: it leaves the
stream), or kept; `ord[a]` is the position chosen.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- The positions `x ∈ [lo, hi)` not marked in `IW[mk ..]`. -/
def unm (m : Mem) (mk : Word) (lo hi : Nat) : List Nat :=
  (List.range' lo (hi - lo)).filter fun x => rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0

/-- The records at the positions of a list. -/
def recsAt (dsAll : Array IDeclaration) (xs : List Nat) : Array IDeclaration :=
  (xs.map fun x => dsAll[x]!).toArray

/-- **The prepare stage's setting**: the `n` records of `DECL` represent `dsAll` (each with
`RecOK`), `n < 2 ^ 59`, the prelude's `np ≤ n`; the slices `ord` and `mk` of `n` words each,
consecutive, below the pool top; the store relation. -/
structure PEnv (m : Mem) (a : AState) (dsAll : Array IDeclaration) (np nw ord mk : Word) : Prop where
  recs : ∀ x (h : x < dsAll.size), DeclAtF (m.arr64 DECL) (m.arr64 DLP) x dsAll[x] ∧
    RecOK (m.arr64 DECL) (m.arr64 DLP) x
  size : nw.toNat = dsAll.size
  n59 : nw.toNat < 2 ^ 59
  np : np.toNat ≤ nw.toNat
  rg1 : ord.toNat + nw.toNat ≤ mk.toNat
  rg2 : mk.toNat + nw.toNat ≤ iwTop m
  iwok : IWOK m
  arena : ArenaR m a

/-- What `prep_front`/`prep_rest` keep: arrays and `CTL` words from `64` on but `IW`, every
size, and the `IW` words outside `[ord, mk + n)`. -/
def PFr (ord mk nw : Word) (m m' : Mem) : Prop :=
  (∀ b : ArrId, 64 ≤ b → b ≠ IW → m'.arr64 b = m.arr64 b) ∧
    (∀ x : Word, 64 ≤ x.toNat → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) ∧
    (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size ∧
    ∀ x : Nat, (x < ord.toNat ∨ mk.toNat + nw.toNat ≤ x) → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?

/-- **`prep_front` is `frontOf`** from the prelude record `aw` on (`acc` the front so far, the
twin's stream the unmarked records). -/
theorem pFront_ok (dsAll : Array IDeclaration) (np nw ord mk : Word) :
    ∀ (fuel : Nat) (m m' : Mem) (a : AState) (aw r : Word) (acc : Array IDeclaration),
    PEnv m a dsAll np nw ord mk → aw.toNat ≤ np.toNat → acc.size = aw.toNat →
    (∀ k (hk : k < aw.toNat), (rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat < nw.toNat ∧
      acc[k]! = dsAll[(rdW (m.arr64 IW) (ord + UInt64.ofNat k)).toNat]!) →
    pFrontW fuel m np nw ord mk aw = some (r, m') →
    ∃ (front rest : Array IDeclaration) (a' : AState),
      (frontOf acc ((dsAll.toList.take np.toNat).drop aw.toNat)
        (recsAt dsAll (unm m mk np.toNat nw.toNat))).run a = .ok ((front, rest), a') ∧
      front.size = np.toNat ∧
      (∀ k (hk : k < np.toNat), (rdW (m'.arr64 IW) (ord + UInt64.ofNat k)).toNat < nw.toNat ∧
        front[k]! = dsAll[(rdW (m'.arr64 IW) (ord + UInt64.ofNat k)).toNat]!) ∧
      rest = recsAt dsAll (unm m' mk np.toNat nw.toNat) ∧
      PEnv m' a' dsAll np nw ord mk ∧ a'.pins = a.pins ∧ PFr ord mk nw m m' := by
  sorry

/-- **`prep_rest` writes the unmarked records `[j, n)` to `ord[c ..]`.** -/
theorem pRest_ok (nw ord mk : Word) :
    ∀ (fuel : Nat) (m m' : Mem) (c j r : Word),
    ord.toNat + nw.toNat ≤ mk.toNat → mk.toNat + nw.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 → c.toNat ≤ j.toNat → j.toNat ≤ nw.toNat →
    pRestW fuel m nw ord mk c j = some (r, m') →
    r.toNat = c.toNat + (unm m mk j.toNat nw.toNat).length ∧
      (∀ k (hk : k < (unm m mk j.toNat nw.toNat).length),
        rdW (m'.arr64 IW) (ord + UInt64.ofNat (c.toNat + k)) =
          UInt64.ofNat ((unm m mk j.toNat nw.toNat)[k]'hk)) ∧
      MemFrame [IW] [] m m' ∧
      ∀ x : Nat, (x < ord.toNat + c.toNat ∨ ord.toNat + nw.toNat ≤ x) →
        (m'.arr64 IW)[x]? = (m.arr64 IW)[x]? := by
  sorry

end L.Checker
