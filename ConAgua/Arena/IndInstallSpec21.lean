import ConAgua.Arena.IndInstallSpec20
import ConAgua.Arena.RecGenSpec10

/-!
# Refinements of `IndInstall`, part 21 (lane `indproofs2`, helper `install`): `checkBlockRec`

A wrapper reordering its arguments to `gen_rec_check`'s (helper `rec`'s `RecGen`, not proved yet:
a pending contract below).
-/


noncomputable section

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Pending callee contract (`sorry` until the owner's refinement lands) -/

/-- `gen_rec_check(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
cvTas.off, cvTas.len, block.off, block.len)` (lane `indproofs2`'s `RecGen`, pending): the generated
recursors checked; the environment with them at the returned view, the recursors' records
(`[cv, M, rhss.off, rhss.len]`) a slice decoded below the tops. -/
theorem genRecCheck_pending (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (pp nested pO pL tO tL rd mO mL cO cL bO bL : Word) (bs : BlockShape) (params : List EIdx)
    (tbl : List NestCtorNf) (rdv : ClassRead) (ms : List TargetMajor) (cvTas : List IConstantVal)
    (block : List IConstantInfo) :
    RelAM "gen_rec_check" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL]
      (fun m a => StageR dn vis fe m a ∧ DecB (fun m => decBS m pp.toNat) m bs ∧
        decHL m pO.toNat pL.toNat = some params ∧ pO.toNat + pL.toNat ≤ iwTop m ∧
        PSlR decNCN tbl tO tL m ∧ DecB (fun m => decCR m rd.toNat) m rdv ∧ PSlR decTM ms mO mL m ∧
        PSlR decCVp cvTas cO cL m ∧ DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
      (genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block)
      (fun m m' a' r x => StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow m m' ∧ decRRS m' r.tail x.2) := sorry

/-! ## `check_block_rec` -/

def icrK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m)

/-- **The model of `check_block_rec`** (body fuel `n`). -/
def icrW (p : Prog) (n : Nat) (m : Mem) (vis pp nested pO pL tO tL rd mO mL bO bL cO cL : Word) :
    Option (List Word × Mem) :=
  icrK (callW p n "gen_rec_check" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] m)

theorem icrK_some (r : List Word) (m : Mem) : icrK (some (r, m)) =
    some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m) := rfl
attribute [ind_grind] icrK_some

theorem icr_spec (p : Prog) (hp : p.lookup "check_block_rec" = some checkBlockRec) (n : Nat) (s₀ : St)
    (vis pp nested pO pL tO tL rd mO mL bO bL cO cL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_rec"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, bO, bL, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧ icrW p n s₀.mem vis pp nested pO pL tO tL rd mO mL bO bL cO cL =
      some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockRec]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "gen_rec_check"] <;>
    finish (gen := 40) (instances := 20000) [icrW]

/-- **`check_block_rec` refines `checkBlockRec`** (through `gen_rec_check`'s pending contract). -/
@[refines ConRon.Arena.checkBlockRec]
theorem checkBlockRec_refines (p : Prog) (hp : p.lookup "check_block_rec" = some checkBlockRec)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (pp nested pO pL tO tL rd mO mL bO bL cO cL : Word) (bs : BlockShape) (params : List EIdx)
    (tbl : List NestCtorNf) (rdv : ClassRead) (ms : List TargetMajor) (cvTas : List IConstantVal)
    (block : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hpre : DecB (fun m => decBS m pp.toNat) s₀.mem bs ∧
        decHL s₀.mem pO.toNat pL.toNat = some params ∧ pO.toNat + pL.toNat ≤ iwTop s₀.mem ∧
        PSlR decNCN tbl tO tL s₀.mem ∧ DecB (fun m => decCR m rd.toNat) s₀.mem rdv ∧
        PSlR decTM ms mO mL s₀.mem ∧ PSlR decCVp cvTas cO cL s₀.mem ∧
        DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_rec"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, bO, bL, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀ ∧
      StageR dn (r.headD 0)
        (AM.res (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀).1
        s'.mem (AM.st (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decRRS s'.mem r.tail
        (AM.res (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀).2; ⊤⦄ := by
  refine triple_post (icr_spec p hp n s₀ vis pp nested pO pL tO tL rd mO mL bO bL cO cL) ?_
  rintro r s' ⟨hl, hm⟩
  have hsim : Sim (icrW p n s₀.mem vis pp nested pO pL tO tL rd mO mL bO bL cO cL)
      (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀
      (fun r x m' a' => StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow s₀.mem m' ∧ decRRS m' r.tail x.2) := by
    unfold icrW ConRon.Arena.checkBlockRec
    refine Sim.post (K := icrK) rfl (fun _ _ => rfl)
      (installSimStub (p := p) (n := n) (genRecCheck_pending dn vis fe pp nested pO pL tO tL rd mO mL cO cL
        bO bL bs params tbl rdv ms cvTas block) ⟨hS, hpre⟩) ?_
    rintro r x m a ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  obtain ⟨hok, hQ⟩ := Sim.run hsim hm
  exact ⟨hl, hok, hQ⟩

end L.Ind
