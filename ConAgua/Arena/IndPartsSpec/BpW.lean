import ConAgua.Arena.IndPartsSpec.Bf
import ConAgua.Arena.IndPartsSpec.BrsW
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# BpW

`PartsR`, `bpa_spec`, `bpW_sim`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `block_parts`' result against the twin's `Option BlockParts`. -/
def PartsR (x : Option BlockParts) (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some bp => r.headD 0 = 1 ∧ DecB (fun m => decBP m (r.tail.headD 0).toNat) m bp ∧
      ShapeSl m (r.tail.headD 0)

theorem bpa_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St) (nPd off l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 6)) "block_parts" [nPd, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ bgoK3 (bshW c n s₀.mem nPd off l) = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.parts]
  simp only [callFn, blockParts]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, bsh_spec p hP c hc n] <;>
    finish (gen := 20) [bgoK3_some]

/-- **`block_parts`' model refines `blockParts?`** (`bshW_sim`). -/
theorem bpW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (c : CallM) (n : Nat) {m : Mem}
    {a : AState} {nPd off l : Word} {blk : List IConstantInfo} (hS : StageR dn vis fe m a)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) m blk)
    (hc : LvlHyp c n dn vis fe m (TshT nPd.toNat blk a)) :
    Sim (bgoK3 (bshW c n m nPd off l)) (ConRon.Arena.blockParts? nPd.toNat blk) a
      (fun r x m' a' => PartsR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  unfold ConRon.Arena.blockParts?
  intro r m' e
  rcases h1 : bshW c n m nPd off l with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  rw [bgoK3_some] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨x, a', hrun, hR, hS', hg'⟩ := bshW_sim c n hS hblk hc r1 m1 h1
  cases x with
  | none =>
    exact ⟨none, a', by simp only [StateT.run_bind, hrun]; rfl, hR, hS', hg'⟩
  | some bs =>
    obtain ⟨h1', hd, hsl⟩ := hR
    refine ⟨some ⟨bs⟩, a', by simp only [StateT.run_bind, hrun]; rfl, ⟨h1', ?_, hsl⟩, hS', hg'⟩
    show decBP (truncM m1) _ = _
    simp only [decBP, show decBS (truncM m1) (r1.tail.headD 0).toNat = some bs from hd, bind, pure,
      Option.bind_some, List.headD_cons, List.tail_cons]

end L.Ind

end
