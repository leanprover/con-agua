import ConAgua.Arena.IndPosSpec.P2sfW
import ConAgua.Arena.IndPosSpec.Pos2RdGrow

/-!
# NestSeeds: `ConRon.Arena.nestSeeds` (the seed's fuel fold (nest_seeds_fuel))

The refinement theorems `nestSeedsFuel_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem wfWf_afr {n : Nat} {m m' : Mem} {e : Word} {r : List Word} (h : wfWf n m e = some (r, m')) :
    AFr m m' := by
  obtain ⟨n', w, -, hw, -⟩ := pos2_wfWf_some h
  exact wfW_afr hw

theorem p2sfW_afr : ∀ (n : Nat) (m m' : Mem) (dO dL k f : Word) (r : List Word),
    p2sfW n m dO dL k f = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [p2sfW] at h
  | n + 1, m, m', dO, dL, k, f, r, h => by
    simp only [p2sfW, p2sfK.eq_def] at h
    afr_auto h [wfWf_afr, p2sfW_afr n _ _ _ _ _ _ _]

theorem pos2_rootOuts_mono : ∀ q, OMono (fun m => decAt m (fun o l => decPL m (decKE m) o l) q) :=
  fun q => OMono.decAt (fun o l => OMono.decPL decKE_mono o l) q

theorem RootOutsB.grow {m m' : Mem} {o l : Nat} {outss : List (List (List NestFieldKind × EIdx))}
    (h : RootOutsB m o l outss) (hg : IWGrow m m') : RootOutsB m' o l outss :=
  DecB.grow (OMono.decPL pos2_rootOuts_mono o l) hg h

/-- An `(off, len)` record (`rec2`) of a `(kinds, closed)` slice. -/
theorem pos2_outs_rec {m' : Mem} {q o l : Word} {xs : List (List NestFieldKind × EIdx)}
    (hq : q.toNat + 2 ≤ iwTop m')
    (hget : ∀ j < [o, l].length, (m'.arr64 IW)[q.toNat + j]? = [o, l][j]?) (hx : OutsB m' o.toNat l.toNat xs) :
    DecB (fun m => decAt m (fun o l => decPL m (decKE m) o l) q.toNat) m' xs := by
  have g : ∀ j < 2, (iwA (truncM m'))[q.toNat + j]? = [o, l][j]? := fun j hj => by
    rw [truncM_iw_eq (by omega)]; exact hget j (by simpa using hj)
  have n0 : iwN (truncM m') q.toNat = some o.toNat := by
    simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 0 (by omega))
  have n1 : iwN (truncM m') (q.toNat + 1) = some l.toNat := by
    simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 1 (by omega))
  have hx' : decPL (truncM m') (decKE (truncM m')) o.toNat l.toNat = some xs := hx
  show decAt (truncM m') _ q.toNat = some xs
  simp only [decAt, n0, n1, Option.bind_eq_bind, Option.bind_some]
  exact hx'

/-! ## The seeds -/

/-- The seeds: word `o + i` points at a `(key, nPc)` record, the key a `NestKey` decoded below the
tops with its parameter slice below the top. -/
def SeedsAt (m : Mem) (o : Nat) (seeds : List (NestKey × Nat)) : Prop :=
  ∀ i (hi : i < seeds.length), ∃ sp key nPc : Word, (m.arr64 IW)[o + i]? = some sp ∧ o + i < iwTop m ∧
    sp.toNat + 1 < iwTop m ∧ (m.arr64 IW)[sp.toNat]? = some key ∧ (m.arr64 IW)[sp.toNat + 1]? = some nPc ∧
    DecB (fun m => decNK m key.toNat) m seeds[i].1 ∧ NKSl m key ∧ nPc.toNat = seeds[i].2

theorem pos2_key_rd {m m' : Mem} (hg : IWGrow m m') (htop : iwTop m < 2 ^ 64) {key : Word}
    (hk : key.toNat + 4 ≤ iwTop m) {j : Nat} (hj : j < 4) : rdW (m'.arr64 IW) (key + UInt64.ofNat j) = rdW (m.arr64 IW) (key + UInt64.ofNat j) := by
  apply pos2_rd_grow hg
  have : (UInt64.ofNat j).toNat = j := by simp; omega
  rw [word_add_toNat (by rw [this]; omega), this]; omega

theorem SeedsAt.grow {m m' : Mem} {o : Nat} {seeds : List (NestKey × Nat)} (h : SeedsAt m o seeds)
    (hg : IWGrow m m') (htop : iwTop m < 2 ^ 64) : SeedsAt m' o seeds := fun i hi => by
  obtain ⟨sp, key, nPc, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h i hi
  have hk4 := (pos2_nk_fields h6 htop).2.2.2.2.2.2
  refine ⟨sp, key, nPc, by rw [hg.2.2.1 _ h2]; exact h1, by have := hg.1; omega, by have := hg.1; omega,
    by rw [hg.2.2.1 _ (by omega)]; exact h4, by rw [hg.2.2.1 _ h3]; exact h5, h6.grow (decNK_mono _) hg, ?_, h8⟩
  have e2 := pos2_key_rd hg htop hk4 (j := 2) (by omega)
  have e3 := pos2_key_rd hg htop hk4 (j := 3) (by omega)
  simp only [NKSl] at h7 ⊢
  have := hg.1
  rw [show (key + 2 : Word) = key + UInt64.ofNat 2 from rfl, show (key + 3 : Word) = key + UInt64.ofNat 3 from rfl,
    e2, e3]
  exact Nat.le_trans h7 hg.1

theorem SeedsAt.tail {m : Mem} {o : Nat} {x : NestKey × Nat} {seeds : List (NestKey × Nat)}
    (h : SeedsAt m o (x :: seeds)) : SeedsAt m (o + 1) seeds := fun i hi => by
  obtain ⟨sp, key, nPc, h1, h2, rest⟩ := h (i + 1) (by simp; omega)
  exact ⟨sp, key, nPc, by rw [show o + 1 + i = o + (i + 1) by omega]; exact h1, by omega, by simpa using rest⟩

/-! ## Census -/

section census
variable {p : Prog} (L : RsLook p) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

include L in
@[refines_part ConRon.Arena.nestSeeds "the seed's fuel fold (nest_seeds_fuel)"]
theorem nestSeedsFuel_refines (s₀ : St) (a₀ : AState) (dO dL k f : Word) (ds : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hlen : ds.length = dL.toNat)
    (hel : ∀ j < dL.toNat, ∃ w, (s₀.mem.arr64 IW)[dO.toNat + j]? = some w ∧ H w ∧ ds[j]? = some (decI w))
    (hb : dO.toNat + dL.toNat ≤ iwTop s₀.mem) (hk : k.toNat ≤ dL.toNat) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_seeds_fuel" [dO, dL, k, f]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ a', ((ds.drop k.toNat).foldlM pos2FuelF f.toNat).run a₀ =
      .ok ((r.headD 0).toNat, a') ∧ StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (nestSeedsFuel_spec L n s₀ dO dL k f) ?_
  rintro r s' ⟨hlc, hm⟩
  have := p2sfW_ok dn vis fe dO dL ds s₀.mem hlen hel hb n s₀.mem s'.mem a₀ k f _ hm hS (IWGrow.refl _) hk hP
  exact ⟨hlc, by simpa using this⟩

end census

end L.Ind

end
