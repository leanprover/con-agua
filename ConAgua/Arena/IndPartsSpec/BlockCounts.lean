import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# BlockCounts: `ConRon.Arena.blockCounts`, `ConRon.Arena.piBinders`, `ConRon.Arena.recTargetOf`

The refinement theorems `piBinders_refines`, `recTargetOf_refines`, `blockCounts_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
  (hs : p.lookup "sl_cons" = some slCons)
  (hp : p.lookup "pi_binders" = some piBinders)
include ha hc hv hs hp

theorem piBinders_spec (n : Nat) : ∀ (s₀ : St) (fuel h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_binders" [fuel, h]
    ⦃fun r s' => LocEq s' s₀ ∧ piBW n s₀.mem fuel h = some (r, s'.mem) ∧
      r = [r.headD 0, r.getD 1 0, r.getD 2 0]; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ fuel h; rw [invoke_eq _ hp]; simp only [callFn, piBinders]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ fuel h
    rw [invoke_eq _ hp]
    simp only [callFn, piBinders]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        eViewSpec4 p hv n, slConsSpec2 p ha hc hs n, ih] <;>
      finish (gen := 20) [List.getD_cons_zero, List.getD_cons_succ, Sig.retVal]

theorem piBinders_spec' (n : Nat) (s₀ : St) (fuel h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_binders" [fuel, h]
    ⦃fun r s' => LocEq s' s₀ ∧ piBW n s₀.mem fuel h = some (r, s'.mem); ⊤⦄ :=
  triple_post (piBinders_spec p ha hc hv hs hp n s₀ fuel h) (fun _r _s' ⟨h1, h2, _⟩ => ⟨h1, h2⟩)

end spec

/-- **`pi_binders` is `piBinders`**: under `ArenaR`, a returning run is a successful twin run
(no state change) whose binders are the new `IW` slice and whose body is the third result. -/
@[refines ConRon.Arena.piBinders]
theorem piBinders_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
    (hs : p.lookup "sl_cons" = some slCons) (hp : p.lookup "pi_binders" = some piBinders)
    (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (fuel h : Word)
    (hh : h.toNat < 2 ^ 32) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hcl : 200 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_binders" [fuel, h]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [r.headD 0, r.getD 1 0, r.getD 2 0] ∧
      (∃ bs e, (ConRon.Arena.piBinders fuel.toNat (decE h)).run a₀ = .ok ((bs, e), a₀) ∧
        decHL s'.mem (r.headD 0).toNat (r.getD 1 0).toNat = some bs ∧
        (r.getD 2 0).toNat < 2 ^ 32 ∧ decE (r.getD 2 0) = e) ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem ∧
      (r.headD 0).toNat + (r.getD 1 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (piBinders_spec' p ha hc hv hs hp n s₀ fuel h) ?_
  intro r s' ⟨hl, hm⟩
  obtain ⟨bs, e, hrun, hsh, hdec, hb1, hb2, hg, hf, hle⟩ :=
    piBW_ok n s₀.mem s'.mem a₀ fuel h r hR hm hh hsz hcl
  exact ⟨hl, hsh, ⟨bs, e, hrun, hdec, hb1, hb2⟩, hg, hf, hle⟩

/-- **`rec_target_of` refines `recTargetOf`** (through the stub `get_app_fn`). -/
@[refines ConRon.Arena.recTargetOf]
theorem recTargetOf_refines (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "rec_target_of" = some recTargetOf)
    (hst : StripProg p) (had : AdF p) (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis no nl mI ty : Word) (names : List NIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hnames : decHL s₀.mem no.toNat nl.toNat = some names)
    (hb : no.toNat + nl.toNat < 2 ^ 64) (hbt : no.toNat + nl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_target_of" [no, nl, mI, ty]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀ ∧
      r = [UInt64.ofNat (AM.res (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀)] ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (recTargetOf_spec p hv hf hp hst had n s₀ no nl mI ty) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hr, hS', hg⟩ := recTW_ok n dn fe vis s₀.mem s'.mem a₀ no nl mI ty r names hm
    hS hty hnames hb hbt
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hr, by rw [hst]; exact hS', hg⟩

theorem bcPure_three (nPd k nC nR bl g rOk rMI rRP : Word) :
    bcPure nPd k nC nR bl g rOk rMI rRP = [(bcPure nPd k nC nR bl g rOk rMI rRP).headD 0,
      (bcPure nPd k nC nR bl g rOk rMI rRP).getD 1 0, (bcPure nPd k nC nR bl g rOk rMI rRP).getD 2 0] := by
  unfold bcPure
  repeat' split
  all_goals rfl

section specp
local grind_pattern [ind_grind] bcPure_sort_lt => bcPure nPd k nC nR bl g rOk rMI rRP
local grind_pattern [ind_grind] bcPure_sort_ge => bcPure nPd k nC nR bl g rOk rMI rRP
local grind_pattern [ind_grind] bcPure_norec => bcPure nPd k nC nR bl g rOk rMI rRP
local grind_pattern [ind_grind] bcPure_badrp => bcPure nPd k nC nR bl g rOk rMI rRP
local grind_pattern [ind_grind] bcPure_eq1 => bcPure nPd k nC nR bl g rOk rMI rRP
local grind_pattern [ind_grind] bcPure_eq2 => bcPure nPd k nC nR bl g rOk rMI rRP
local grind_pattern [ind_grind] bcPure_none => bcPure nPd k nC nR bl g rOk rMI rRP
variable (p : Prog) (hpp : p.lookup "block_counts_pure" = some blockCountsPure)
include hpp

theorem blockCountsPure_spec (n : Nat) (s₀ : St) (nPd k nC nR bl g rOk rMI rRP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_counts_pure" [nPd, k, nC, nR, bl, g, rOk, rMI, rRP]
    ⦃fun r s' => s' = s₀ ∧ r = bcPure nPd k nC nR bl g rOk rMI rRP; ⊤⦄ := by
  rw [invoke_eq _ hpp]
  simp only [callFn, blockCountsPure]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      finish (gen := 20)

theorem blockCountsPure_spec' (n : Nat) (s₀ : St) (nPd k nC nR bl g rOk rMI rRP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_counts_pure" [nPd, k, nC, nR, bl, g, rOk, rMI, rRP]
    ⦃fun r s' => s' = s₀ ∧ r = bcPure nPd k nC nR bl g rOk rMI rRP ∧
      r = [r.headD 0, r.getD 1 0, r.getD 2 0]; ⊤⦄ :=
  triple_post (blockCountsPure_spec p hpp n s₀ nPd k nC nR bl g rOk rMI rRP)
    (fun r s' ⟨h1, h2⟩ => ⟨h1, h2, by rw [h2]; exact bcPure_three _ _ _ _ _ _ _ _ _⟩)

end specp

theorem bchW_two {n : Nat} {m m' : Mem} {cvT : Word} {r : List Word}
    (h : bchW n m cvT = some (r, m')) : r = [r.headD 0, r.getD 1 0] := by
  cases n with
  | zero => simp [bchW] at h
  | succ n =>
    rw [bchW_step] at h
    obtain ⟨rs, m1, hp, h⟩ := ipK_inv h (by simp [bchW.bchK1])
    rw [bchK1_some] at h
    by_cases hr : eViewW m1 (rs.getD 2 0) = []
    · rw [hr] at h; simp [bchW.bchK2] at h
    rw [bchK2_ne _ _ _ hr] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
  (hs : p.lookup "sl_cons" = some slCons) (hpb : p.lookup "pi_binders" = some piBinders)
  (hh : p.lookup "block_counts_head" = some blockCountsHead)
include ha hc hv hs hpb hh

theorem blockCountsHead_spec (n : Nat) (s₀ : St) (cvT : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_counts_head" [cvT]
    ⦃fun r s' => LocEq s' s₀ ∧ bchW n s₀.mem cvT = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hh]
  simp only [callFn, blockCountsHead]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        piBinders_spec p ha hc hv hs hpb n, eViewSpec4 p hv n] <;>
      finish (gen := 20) [rdW_eq, CWF, List.getD_cons_zero, List.getD_cons_succ, List.tail_cons]

theorem blockCountsHead_spec' (n : Nat) (s₀ : St) (cvT : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_counts_head" [cvT]
    ⦃fun r s' => LocEq s' s₀ ∧ bchW n s₀.mem cvT = some (r, s'.mem) ∧
      r = [r.headD 0, r.getD 1 0]; ⊤⦄ :=
  triple_post (blockCountsHead_spec p ha hc hv hs hpb hh n s₀ cvT)
    (fun _r _s' ⟨h1, h2⟩ => ⟨h1, h2, bchW_two h2⟩)

end spec

section spec2
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
  (hs : p.lookup "sl_cons" = some slCons) (hpb : p.lookup "pi_binders" = some piBinders)
  (hh : p.lookup "block_counts_head" = some blockCountsHead)
  (hpp : p.lookup "block_counts_pure" = some blockCountsPure)
  (hp : p.lookup "block_counts" = some blockCounts)
include ha hc hv hs hpb hh hpp hp

theorem blockCounts_spec (n : Nat) (s₀ : St) (nPd k nC nR cvT rOk rMI rRP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_counts" [nPd, k, nC, nR, cvT, rOk, rMI, rRP]
    ⦃fun r s' => LocEq s' s₀ ∧ bcW n s₀.mem nPd k nC nR cvT rOk rMI rRP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockCounts]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        blockCountsHead_spec' p ha hc hv hs hpb hh n, blockCountsPure_spec' p hpp n] <;>
      finish (gen := 20)

end spec2

/-- **`block_counts` refines `blockCounts?`** (the recursor datum `r` as `(rOk, rMI, rRP)`). -/
@[refines ConRon.Arena.blockCounts?]
theorem blockCounts_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
    (hs : p.lookup "sl_cons" = some slCons) (hpb : p.lookup "pi_binders" = some piBinders)
    (hh : p.lookup "block_counts_head" = some blockCountsHead)
    (hpp : p.lookup "block_counts_pure" = some blockCountsPure)
    (hp : p.lookup "block_counts" = some blockCounts) (n : Nat) (s₀ : St) (a₀ : AState)
    (nPd k nC nR cvT rOk rMI rRP : Word) (cv : IConstantVal) (rr : Option (Nat × Nat))
    (hR : ArenaR s₀.mem a₀) (hcv : decCVp s₀.mem cvT.toNat = some cv) (hb : cvT.toNat + 3 < 2 ^ 64)
    (hrr : rr = if rOk = 0 then none else some (rMI.toNat, rRP.toNat))
    (h1 : nPd.toNat < 2 ^ 32) (h2 : k.toNat < 2 ^ 32) (h3 : nC.toNat < 2 ^ 32)
    (h4 : nR.toNat < 2 ^ 32) (h5 : rMI.toNat < 2 ^ 32) (h6 : rRP.toNat < 2 ^ 32)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hcl : 200 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_counts" [nPd, k, nC, nR, cvT, rOk, rMI, rRP]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.blockCounts? nPd.toNat k.toNat nC.toNat nR.toNat cv rr) a₀ ∧
      AM.st (ConRon.Arena.blockCounts? nPd.toNat k.toNat nC.toNat nR.toNat cv rr) a₀ = a₀ ∧
      r = encONN (AM.res (ConRon.Arena.blockCounts? nPd.toNat k.toNat nC.toNat nR.toNat cv rr) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (blockCounts_spec p ha hc hv hs hpb hh hpp hp n s₀ nPd k nC nR cvT rOk rMI rRP) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, hrun, hr, -, hg, hf⟩ := bcW_ok n s₀.mem s'.mem a₀ nPd k nC nR cvT rOk rMI rRP r cv rr
    hR hm hcv hb hrr h1 h2 h3 h4 h5 h6 hsz hcl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hr, hg, hf⟩

end L.Ind

end
