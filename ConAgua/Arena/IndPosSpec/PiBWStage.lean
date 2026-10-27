import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndPartsSpec.RecTW

/-!
# PiBWStage

`piBW_stage`, `piBW_cwf`, `naK2`, `NaLook`, `nhiW`, `nestCtxHiAt_specE` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `pi_binders` under the stage relation -/

/-- **`pi_binders` keeps the stage relation** (it only conses into the pool). -/
theorem piBW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (fuel h : Word) (rs : List Word),
    piBW n m fuel h = some (rs, m') → StageR dn vis fe m a → H h → StageR dn vis fe m' a := by
  induction n with
  | zero => intro m m' a fuel h rs hh; simp [piBW] at hh
  | succ n ih =>
    intro m m' a fuel h rs hpb hS hh
    have hR := hS.1.arena.1
    by_cases hf : fuel = 0
    · rw [piBW_fuel0 n m fuel h hf] at hpb; simp at hpb
    by_cases hg : h >>> 28 ≠ 6
    · rw [piBW_leaf n m fuel h hf hg] at hpb
      simp only [Option.some.injEq, Prod.mk.injEq] at hpb
      obtain ⟨-, rfl⟩ := hpb; exact hS
    rw [piBW_node n m fuel h hf hg] at hpb
    have hg6 : h >>> 28 = 6 := by simpa using hg
    by_cases hr : eViewW m h = []
    · rw [hr, piBK1_nil] at hpb; simp at hpb
    obtain ⟨hvok, hew⟩ := eViewW_forall m h hg6 hr
    rw [piBK1_ne n m fuel _ hr] at hpb
    rcases hrec : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with _ | ⟨rs1, m1⟩ <;> rw [hrec] at hpb; · simp [piBK2] at hpb
    rw [piBK2_some] at hpb
    rcases hcons : consW n m1 ((eViewW m h).getD 1 0) (rs1.headD 0) (rs1.getD 1 0) with _ | ⟨r2, m2⟩ <;> rw [hcons] at hpb; · simp [piBK3] at hpb
    rw [piBK3_some] at hpb
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hpb)
    obtain ⟨-, hty, hb⟩ := view_forall m a hR h hh hvok hg6
    have hty2 : ((eViewW m h).getD 1 0).toNat < 2 ^ 32 := by rw [hew]; exact hty
    have hb2 : ((eViewW m h).getD 2 0).toNat < 2 ^ 32 := by rw [hew]; exact hb
    have hS1 := ih m m1 a (fuel - 1) _ rs1 hrec hS hb2
    obtain ⟨bs1, e1, -, -, hdec1, -, -, -, -, hle1⟩ :=
      piBW_ok n m m1 a (fuel - 1) _ rs1 hR hrec hb2 hS.2.2.2.1 hS.2.2.2.2.2
    exact (consW_stage hcons hS1 hle1 hty2 hdec1).1

/-- `pi_binders` at `CWF` from the stage relation: the twin's run, the stage relation kept. -/
theorem piBW_cwf {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {n : Nat} {m m' : Mem}
    {a : AState} {h : Word} {rs : List Word} (hpb : piBW n m CWF h = some (rs, m'))
    (hS : StageR dn vis fe m a) (hh : H h) :
    ∃ bs e, (ConRon.Arena.piBinders coreWalkFuel (decI h)).run a = .ok ((bs, e), a) ∧
      decHL m' (rs.headD 0).toNat (rs.getD 1 0).toNat = some bs ∧
      (rs.getD 2 0).toNat < 2 ^ 32 ∧ decE (rs.getD 2 0) = e ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ (rs.headD 0).toNat + (rs.getD 1 0).toNat ≤ iwTop m' := by
  obtain ⟨bs, e, hrun, -, hdec, hb1, hb2, hg, -, hle⟩ :=
    piBW_ok n m m' a CWF h rs hS.1.arena.1 hpb hh hS.2.2.2.1 hS.2.2.2.2.2
  rw [CWF_eq] at hrun
  exact ⟨bs, e, hrun, hdec, hb1, hb2, piBW_stage n m m' a CWF h rs hpb hS hh, hg, hle⟩

/-! ## `nest_arity` refines `nestArity` -/

def naK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m2) => some ([rs.getD 1 0], m2)
/-- The lookups of `nest_arity`. -/
structure NaLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hv : p.lookup "e_view" = some eView
  hs : p.lookup "sl_cons" = some slCons
  hpb : p.lookup "pi_binders" = some piBinders
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hp : p.lookup "nest_arity" = some nestArityL

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_ctx_hi_at` as a word model -/

/-- The model of `nest_ctx_hi_at(ctx, nf)`. -/
def nhiW (m : Mem) (ctx nf : Word) : Word := rdW (m.arr64 IW) (ctx + 4) + rdW (m.arr64 IW) (ctx + 1) + nf

theorem nestCtxHiAt_specE (p : Prog) (hp : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt) (n : Nat)
    (s₀ : St) (ctx nf : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctx_hi_at" [ctx, nf]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = nhiW s₀.mem ctx nf; ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtxHiAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [nhiW, rdW_eq]

/-- A decoded handle at `o`, as the word L reads there. -/
theorem rd_iwH0E {k : IdxKind} {m : Mem} {o : Word} {x : Idx k} (h : iwH m o.toNat = some x) :
    H (rdW (m.arr64 IW) o) ∧ decI (rdW (m.arr64 IW) o) = x := by
  obtain ⟨w, hw, hl, hx⟩ := hd?_some h
  simp only [iwA] at hw
  simp only [rdW, hw, Option.getD_some]
  exact ⟨hl, hx.symm⟩

/-! ## `nest_ds_closed(_go)`: `ds.allM (fvarB · ≤ hi)` -/

/-- The twin's per-parameter test. -/
def dsF (hi : Nat) (x : EIdx) : AM Bool := do
  let b ← fvarB coreWalkFuel x
  pure (decide (b ≤ hi))

mutual
def dcGoW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, hi, off, l =>
    if l = 0 then some ([1], m)
    else dcK n hi off l (fvbF m [CWF, rdW (m.arr64 IW) off])
def dcK (n : Nat) (hi off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if hi < r.headD 0 then some ([0], m1) else dcGoW n m1 hi (off + 1) (l - 1)
end

/-- The model of `nest_ds_closed(ctx, off, l)` at exec fuel `n + 1`. -/
def dcW (n : Nat) (m : Mem) (ctx off l : Word) : Option (List Word × Mem) := dcGoW n m (nhiW m ctx 0) off l

/-- `nest_ds_closed` at any exec fuel. -/
def dcWf : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, ctx, off, l => dcW n m ctx off l

/-- The lookups of `nest_ds_closed`. -/
structure DcLook (p : Prog) : Prop where
  hf : HfF p
  hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  hg : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL
  hp : p.lookup "nest_ds_closed" = some nestDsClosedL

/-- The lookups of `nest_occ`. -/
structure NoLook (p : Prog) : Prop where
  hv : p.lookup "e_view" = some eView
  hc : p.lookup "sl_contains" = some slContains
  hf : p.lookup "no_find" = some (memoFindG noSch)
  hput : p.lookup "no_put" = some (memoPutG noSch)
  hgo : p.lookup "nest_occ_go" = some nestOccGo
  hnode : p.lookup "nest_occ_node" = some nestOccNode
  hcl : p.lookup "no_clear" = some (memoClearG noSch)
  hp : p.lookup "nest_occ" = some nestOcc

end L.Ind

end
