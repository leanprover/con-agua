module

public import ConAgua.Arena.RecCheckSpec.RpLook
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndPartsSpec.BlockRecNameSetOk
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# TpnB

`rpShape9`, `soa_spec`, `soaW`, `wan_spec`, `wanW`, `wantAuxFrom` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_rec_lps_ok`, below the tops -/

/-- The shape record's nine words lie below the top. -/
theorem rpShape9 {m : Mem} {q : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m q.toNat) m bs) :
    q.toNat + 9 ≤ iwTop m := by
  obtain ⟨-, -, -, -, -, -, hpr⟩ := decBS_some (show decBS (truncM m) q.toNat = some bs from hq)
  simp only [iwB, bool?, Option.map_eq_some_iff] at hpr
  obtain ⟨w, hw, -⟩ := hpr
  have := (truncM_iw_get hw).1
  omega

/-! ## `block_rec_split_own_aux` -/

l_model soa_spec (p : Prog) (hP : IndPartsProg p)
    (hp : p.lookup "block_rec_split_own_aux" = some blockRecSplitOwnAux)
  fns [hp ↦ soaW]
  specs [slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind]

/-! ## `block_rec_want_aux_names` -/

l_model wan_spec (p : Prog) (hP : IndPartsProg p) (hNri : NriF p)
    (hp : p.lookup "block_rec_want_aux_names" = some blockRecWantAuxNames)
  fns [hp ↦ wanW]
  specs [nriF_spec p hNri n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind]

/-- The wanted auxiliary names from index `j` on. -/
def wantAuxFrom (n0 : NIdx) (j k : Nat) : AM (List NIdx) :=
  (List.range k).mapM fun i => internNNode (.str n0 s!"rec_{j + i + 1}")

theorem wantAuxFrom_succ (n0 : NIdx) (j k : Nat) :
    wantAuxFrom n0 j (k + 1) = (do
      let x ← internNNode (.str n0 s!"rec_{j + 1}")
      let xs ← wantAuxFrom n0 (j + 1) k
      pure (x :: xs)) := by
  unfold wantAuxFrom
  rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
  congr 1
  funext x
  congr 1
  congr 1
  funext i
  simp only [Function.comp, Nat.succ_eq_add_one]
  rw [show j + (i + 1) + 1 = j + 1 + i + 1 by omega]

/-- **`block_rec_want_aux_names`' model refines the twin's `mapM` of `name_rec_i`** (the real
`name_rec_i`, `nriF_ok`). -/
theorem wanW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m : Mem) (a : AState) (n0 j auxl : Word), H n0 → StageR vis fe m a →
    j.toNat + auxl.toNat < 2 ^ 64 →
    Sim (wanW n m n0 j auxl) (wantAuxFrom (decI n0) j.toNat auxl.toNat) a
      (fun r xs m' a' => decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  sorry

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decRS_cv (m : Mem) (pp : Nat) (x : RecShape) (h : decRS m pp = some x) :
    ∃ a, iwN m pp = some a ∧ decCVp m a = some x.cvR := (decRS_some h).1

theorem decRS_lt (m : Mem) (pp : Nat) (x : RecShape) (h : decRS (truncM m) pp = some x) : pp < iwTop m := by
  obtain ⟨⟨a, ha, -⟩, -⟩ := decRS_some h; exact partsIwLt ha

/-- From `n₀` on: the wanted names, the stream's, the set test, the duplicate test. -/
theorem tpnB_sim (p : Prog) (L : RpLook p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (bs : BlockShape) (reco recl auxo auxl n0 : Word) (x : NIdx) (hn0 : H n0)
    (hx : decI n0 = x) :
    ∀ (m : Mem) (a : AState), StageR vis fe m a → PSlR0 decRS bs.recs reco recl m →
    PSlR decRS (rpAux bs) auxo auxl m →
    Sim (tpnB p (n + 1) reco recl auxo auxl n0 m)
      (do
        let wantAux ← (List.range (rpAux bs).length).mapM fun i => internNNode (.str x s!"rec_{i + 1}")
        if rpSetOk ((rpAux bs).map (·.cvR.name)) wantAux then pure (nameNodup (bs.recs.map (·.cvR.name)))
        else pure false)
      a (fun r b m' a' => r.headD 0 = (if b then 1 else 0) ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  sorry

/-- **`target_rec_pins_names`' model refines the twin's name pins** (through the stubs
`intern_nanon`, `name_rec_i`): the members' and recursors' slices of the shape and the auxiliary
recursors' slice decoded below the tops. -/
theorem tpnW_sim (p : Prog) (L : RpLook p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (m : Mem) (a : AState) (mo k reco recl auxo auxl : Word) (bs : BlockShape)
    (hS : StageR vis fe m a) (hms : PSlR0 decMS bs.members mo k m)
    (hrs : PSlR0 decRS bs.recs reco recl m) (haux : PSlR decRS (rpAux bs) auxo auxl m) :
    Sim (tpnW p (n + 1) m mo k reco recl auxo auxl) (namesTwin bs) a
      (fun r b m' a' => r.headD 0 = (if b then 1 else 0) ∧ StageR vis fe m' a' ∧ IWGrow m m') := by
  sorry

end L.Ind

end

end
