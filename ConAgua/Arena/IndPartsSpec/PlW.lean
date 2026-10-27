import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndPartsSpec.BsoK2
import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.Arena.IndRealAbs
import ConAgua.Arena.IndSumSpec.Row

/-!
# PlW

`plW_sim`, `ShapeSl`, `ShapeR`, `partsFreshGet`, `LvlHyp`, `LvlHyp.mono` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `paramLevels` as a `Sim` (from lane `indproofs`' `plgW_ok`, through `intern_ls_iw`). -/
theorem plW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {k : Nat} {m : Mem}
    {a : AState} {o l : Word} {lps : List NIdx} (hS : StageR dn vis fe m a)
    (hd : decHL m o.toNat l.toNat = some lps) (ht : o.toNat + l.toNat ≤ iwTop m) :
    Sim (plW k m o l) (paramLevels lps) a
      (fun r x m' a' => H (r.headD 0) ∧ decI (r.headD 0) = x ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro r m' hm
  cases k with
  | zero => cases hm
  | succ k =>
  rw [plW_succ] at hm
  rcases h1 : plgW k m o l with _ | ⟨r1, m1⟩ <;> rw [h1] at hm
  · cases hm
  simp only [plW.plK4] at hm
  rcases h2 : ilF m1 [r1.headD 0, r1.tail.headD 0] with _ | ⟨r2, m2⟩ <;> rw [h2] at hm
  · cases hm
  simp only [plW.plK5, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨us, a1, hrun1, hS1, hg1, hd1, -⟩ := plgW_ok dn vis fe k _ _ _ _ _ _ _ h1 hS hd (by omega) ht
  obtain ⟨x, a2, hrun2, hS2, hg2, hH, hx⟩ :=
    ilF_ok dn vis fe (r1.headD 0) (r1.tail.headD 0) us m1 _ a1 r2 h2 ⟨hS1, hd1⟩
  refine ⟨x, a2, ?_, by simpa using hH, by simpa using hx, hS2, hg1.trans hg2⟩
  simp only [paramLevels, StateT.run_bind, hrun1]
  exact hrun2

/-! ## `block_shape_seal` -/

/-- The shape record's two slices (members at words `0, 1`, recursors at `2, 3`) lie below the
top (lane `indproofs4`: `ShapeSrc` and `RecsB` for `check_block`). -/
def ShapeSl (m : Mem) (q : Word) : Prop :=
  (∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m) ∧
  (∀ o l, iwN m (q.toNat + 2) = some o → iwN m (q.toNat + 3) = some l → o + l ≤ iwTop m)

/-- `block_shape`'s result `(ok, q)` against the twin's `Option BlockShape`. -/
def ShapeR (x : Option BlockShape) (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some bs => r.headD 0 = 1 ∧ DecB (fun m => decBS m (r.tail.headD 0).toNat) m bs ∧ ShapeSl m (r.tail.headD 0)

/-- A fresh record's words, in the cut pool. -/
theorem partsFreshGet {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m'))
    (hS : StageR dn vis fe m a) (hl : ws.length < 2 ^ 64) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ q.toNat + ws.length = iwTop m' ∧
      ∀ j (hj : j < ws.length), (iwA (truncM m'))[q.toNat + j]? = some ws[j] := by
  obtain ⟨hS', hg, hq, htop, hget⟩ := posRecW_stage h hS hl
  refine ⟨hS', hg, by omega, fun j hj => ?_⟩
  rw [truncM_iw_eq (by omega)]
  simp only [iwA, hget j hj, List.getElem?_eq_getElem hj]

/-! ## `block_shape_tail` -/

/-- **What the sims need of the `lvl_eq_c` call** (at fuel `n + 2`, through `c`): its `Sim` at every
twin state `a1` the twin's prefix reaches with the sort `sv` (`T sv a1`) and every memory `m1` the
model's prefix reaches from `m` (`AFr m m1`). -/
def LvlHyp (c : CallM) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (m : Mem) (T : LIdx → AState → Prop) : Prop :=
  ∀ (sv : LIdx) (a1 : AState) (s z : Word) (m1 : Mem), T sv a1 → AFr m m1 → StageR dn vis fe m1 a1 →
    H s → decI s = sv → pinWordV m1 53 = some z →
    Sim (c (n + 2) "lvl_eq_c" [s, z] m1) (lvlEq? sv (decI z)) a1
      (fun r x m' a' => KeepPost dn vis fe decLvlEq m1 m' a' r x)

theorem LvlHyp.mono {c : CallM} {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m m' : Mem} {T T' : LIdx → AState → Prop} (h : LvlHyp c n dn vis fe m T) (hf : AFr m m')
    (hT : ∀ sv a1, T' sv a1 → T sv a1) : LvlHyp c n dn vis fe m' T' :=
  fun sv a1 s z m1 hT' hf1 hS hs hsv hz => h sv a1 s z m1 (hT _ _ hT') (hf.trans hf1) hS hs hsv hz

/-- The twin's prefix of `buildTwin` up to `lvlEq?`: the counts, the reserved names, the result sort
`sv` (`LvlHyp`'s `T`). -/
def TbbT (nP : Nat) (cvT0 : IConstantVal) (cvTs : List IConstantVal) (cs : List (IConstantVal × Nat × Nat))
    (rs : List (IConstantVal × Nat × Nat × List IRecRule)) (a : AState) (sv : LIdx) (a1 : AState) : Prop :=
  ∃ nIdxs a2 R a3,
    (ConRon.Arena.blockMemberCounts? nP cvTs.length cs.length (cvTs.map (·.name)) rs 0 cvTs).run a =
      .ok (some nIdxs, a2) ∧
    (reservedBasisNames : AM (List NIdx)).run a2 = .ok (R, a3) ∧
    (bsoTwin nP nIdxs cvT0.type).run a3 = .ok (sv, a1)

/-- The twin's prefix of `blockShape?` up to `lvlEq?`: the split, then `TbbT`. -/
def TshT (nP : Nat) (blk : List IConstantInfo) (a : AState) (sv : LIdx) (a1 : AState) : Prop :=
  ∃ cvT0 cvTs cs r0 rs, ConRon.Arena.blockSplit blk = some (cvT0 :: cvTs, cs, r0 :: rs) ∧
    TbbT nP cvT0 (cvT0 :: cvTs) cs (r0 :: rs) a sv a1

end L.Ind

end
