module

public import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndParts
import ConAgua.L.ModelGen
import ConAgua.L.WordOff

@[expose] public section

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

/-! ## `block_counts` -/

section piB
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
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        eViewSpec4 p hv n, slConsSpec2 p ha hc hs n, ih] <;>
      finish (gen := 20) [List.getD_cons_zero, List.getD_cons_succ, Sig.retVal]

end piB

/-- **`block_counts_pure` is its model `bcPure`** (generated): the arithmetic tail of
`block_counts`, from the binder count `bl`, the result's tag `g` and the recursor data. -/
l_model blockCountsPure_spec (p : Prog) (hpp : p.lookup "block_counts_pure" = some blockCountsPure)
  fns [hpp ↦ bcPure ro list]
  grind [arena_grind] finish []

/-- **`block_counts_head` is its model `bchW`** (generated): `(bl, g)` and the memory. -/
l_model blockCountsHead_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
    (hs : p.lookup "sl_cons" = some slCons) (hpb : p.lookup "pi_binders" = some piBinders)
    (hh : p.lookup "block_counts_head" = some blockCountsHead)
  fns [hh ↦ bchW list]
  specs [piBinders_spec p ha hc hv hs hpb n, eViewSpec4 p hv n]
  grind [arena_grind] fold [CWF] finish [CWF]

/-- **`block_counts` is its model `bcW`** (generated). -/
l_model blockCounts_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hv : p.lookup "e_view" = some eView)
    (hs : p.lookup "sl_cons" = some slCons) (hpb : p.lookup "pi_binders" = some piBinders)
    (hh : p.lookup "block_counts_head" = some blockCountsHead)
    (hpp : p.lookup "block_counts_pure" = some blockCountsPure)
    (hp : p.lookup "block_counts" = some blockCounts)
  fns [hp ↦ bcW list]
  specs [blockCountsHead_spec p ha hc hv hs hpb hh n, blockCountsPure_spec p hpp n]
  grind [arena_grind]

theorem arenaR_frame_iw {m m' : Mem} {a : AState} (hf : MemFrame [IW] [200] m m')
    (h : ArenaR m a) : ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; decide)
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf h

theorem bchW_ok (n : Nat) (m m1 : Mem) (a : AState) (cvT : Word) (r1 : List Word)
    (hR : ArenaR m a) (h : bchW n m cvT = some (r1, m1))
    (hty : (erRd m (cvT + 3)).toNat < 2 ^ 32)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size) :
    ∃ bs res v, (ConRon.Arena.piBinders coreWalkFuel (decE (erRd m (cvT + 3)))).run a
        = .ok ((bs, res), a) ∧ r1 = [r1.headD 0, r1.getD 1 0] ∧ (r1.headD 0).toNat = bs.length ∧
      a.store.view res = some v ∧ ((r1.getD 1 0 = 2) ↔ ∃ u, v = .sort u) ∧
      IWGrow m m1 ∧ MemFrame [IW] [200] m m1 := by
  cases n with
  | zero => simp [bchW] at h
  | succ n =>
    rw [bchW.arm1, erRd_foldN] at h
    obtain ⟨rs, m1', hp, h⟩ := ipK_inv h (bchW.k_pi_binders.none)
    obtain ⟨bs, e, hrun, hsh, hdec, hb1, hb2, hg, hf, -⟩ :=
      piBW_ok n m m1' a CWF _ rs hR hp hty hsz hc
    have e1 : rs.tail.headD 0 = rs.getD 1 0 := by rw [hsh]; rfl
    have e2 : rs.tail.tail.headD 0 = rs.getD 2 0 := by rw [hsh]; rfl
    by_cases hr : eViewW m1' (rs.tail.tail.headD 0) = []
    · simp only [bchW.k_pi_binders, hr, ite_true, reduceCtorEq] at h
    rw [bchW.k_pi_binders.arm1 _ _ hr, e1, e2] at h
    rw [e2] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hR1 : ArenaR m1' a := arenaR_frame_iw hf hR
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m1' a hR1 _ hr
    have hlen := decHL_length m1' hdec
    refine ⟨bs, e, v, ?_, rfl, ?_, ?_, ?_, hg, hf⟩
    · rw [← CWF_eq]; exact hrun
    · simp only [List.headD_cons]; exact hlen.symm
    · rw [← hb2]; exact hv
    · simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact sort_head_iff _ _ _ hvr

/-- `Option (Nat × Nat)` as the words `(ok, a, b)`. -/
def encONN : Option (Nat × Nat) → List Word
  | none => [0, 0, 0]
  | some (p, q) => [1, UInt64.ofNat p, UInt64.ofNat q]

/-- The Nat-level tail of `blockCounts?` past the sort test. -/
def bcTail (nPd k nC nR : Nat) : Option (Nat × Nat) → Option (Nat × Nat)
  | none => none
  | some (mI, rP) =>
    if rP < nC + k || mI < rP then none
    else if rP - (nC + k) == nPd then some (nPd, mI - rP)
    else if k < nR && nPd + nR + nC ≤ rP then some (nPd, mI - rP)
    else none

theorem bcTail_snd {nPd k nC nR p q : Nat} {rr : Option (Nat × Nat)}
    (e : bcTail nPd k nC nR rr = some (p, q)) (hb : ∀ x y, rr = some (x, y) → x < 2 ^ 64) :
    q < 2 ^ 64 := by
  cases rr with
  | none => cases e
  | some xy =>
    obtain ⟨x, y⟩ := xy
    have := hb x y rfl
    simp only [bcTail] at e
    repeat' (split at e)
    all_goals (try simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at e)
    all_goals omega

theorem bcTail_run (nPd k nC nR : Nat) (rr : Option (Nat × Nat)) (a : AState) :
    (match rr with
      | none => (pure none : AM (Option (Nat × Nat)))
      | some (mI, rP) =>
        if rP < nC + k || mI < rP then pure none
        else if rP - (nC + k) == nPd then pure (some (nPd, mI - rP))
        else if k < nR && nPd + nR + nC ≤ rP then pure (some (nPd, mI - rP))
        else pure none).run a = .ok (bcTail nPd k nC nR rr, a) := by
  cases rr with
  | none => rfl
  | some q =>
    obtain ⟨mI, rP⟩ := q
    simp only [bcTail]
    repeat' split
    all_goals rfl

theorem bcPure_nonsort (m : Mem) (nPd k nC nR bl g rOk rMI rRP : Word) (hg : g ≠ 2)
    (h1 : nPd.toNat < 2 ^ 32) (h2 : k.toNat < 2 ^ 32) (h3 : nC.toNat < 2 ^ 32)
    (h4 : nR.toNat < 2 ^ 32) (h5 : rMI.toNat < 2 ^ 32) (h6 : rRP.toNat < 2 ^ 32) :
    bcPure m nPd k nC nR bl g rOk rMI rRP = some (encONN (bcTail nPd.toNat k.toNat nC.toNat nR.toNat
      (if rOk = 0 then none else some (rMI.toNat, rRP.toNat)))) := by
  by_cases h0 : rOk = 0
  · rw [bcPure.arm3 m _ _ _ _ _ _ _ _ _ hg h0, ite_eq_left h0]; rfl
  rw [ite_eq_right h0]
  simp only [bcTail]
  have e1 : (nC + k).toNat = nC.toNat + k.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have e2 : (nPd + nR + nC).toNat = nPd.toNat + nR.toNat + nC.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
  by_cases c1 : rRP < nC + k ∨ rMI < rRP
  · rw [bcPure.arm4 m _ _ _ _ _ _ _ _ _ hg h0 c1]
    have : (rRP.toNat < nC.toNat + k.toNat || rMI.toNat < rRP.toNat) = true := by
      rcases c1 with c | c
      · have := UInt64.lt_iff_toNat_lt.mp c; rw [e1] at this; simp [this]
      · have := UInt64.lt_iff_toNat_lt.mp c; simp [this]
    rw [ite_eq_left this]; rfl
  · have c1' : (rRP.toNat < nC.toNat + k.toNat || rMI.toNat < rRP.toNat) = false := by
      have a1 : ¬ rRP < nC + k := fun h => c1 (Or.inl h)
      have a2 : ¬ rMI < rRP := fun h => c1 (Or.inr h)
      have b1 := (not_congr UInt64.lt_iff_toNat_lt).mp a1
      have b2 := (not_congr UInt64.lt_iff_toNat_lt).mp a2
      rw [e1] at b1
      simp [b1, b2]
    rw [ite_eq_right (by simp [c1'])]
    have hle : (nC + k).toNat ≤ rRP.toNat := by
      have a1 : ¬ rRP < nC + k := fun h => c1 (Or.inl h)
      have b1 := (not_congr UInt64.lt_iff_toNat_lt).mp a1; omega
    have hle2 : nC + k ≤ rRP := UInt64.le_iff_toNat_le.mpr hle
    have hsub : (rRP - (nC + k)).toNat = rRP.toNat - (nC.toNat + k.toNat) := by
      rw [UInt64.toNat_sub_of_le _ _ hle2, e1]
    have hrm : rRP ≤ rMI := by
      have a2 : ¬ rMI < rRP := fun h => c1 (Or.inr h)
      exact UInt64.not_lt.mp a2
    have hsub2 : UInt64.ofNat (rMI.toNat - rRP.toNat) = rMI - rRP := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ hrm, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
    by_cases c2 : rRP - (nC + k) = nPd
    · rw [bcPure.arm5 m _ _ _ _ _ _ _ _ _ hg h0 c1 c2]
      have : (rRP.toNat - (nC.toNat + k.toNat) == nPd.toNat) = true := by
        rw [← hsub, c2]; simp
      rw [ite_eq_left this]
      simp only [encONN, hsub2, L.ofNat_toNat]
    · have c2' : (rRP.toNat - (nC.toNat + k.toNat) == nPd.toNat) = false := by
        rw [← hsub]; simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => c2 (UInt64.toNat_inj.mp h)
      rw [ite_eq_right (by simp [c2'])]
      by_cases c3 : k < nR ∧ nPd + nR + nC ≤ rRP
      · rw [bcPure.arm6 m _ _ _ _ _ _ _ _ _ hg h0 c1 c2 c3]
        have : (k.toNat < nR.toNat && nPd.toNat + nR.toNat + nC.toNat ≤ rRP.toNat) = true := by
          have a := UInt64.lt_iff_toNat_lt.mp c3.1
          have b := UInt64.le_iff_toNat_le.mp c3.2
          rw [e2] at b
          simp [a, b]
        rw [ite_eq_left this]
        simp only [encONN, hsub2, L.ofNat_toNat]
      · rw [bcPure.arm7 m _ _ _ _ _ _ _ _ _ hg h0 c1 c2 c3]
        have : (k.toNat < nR.toNat && nPd.toNat + nR.toNat + nC.toNat ≤ rRP.toNat) = false := by
          by_cases a : k < nR
          · have b : ¬ nPd + nR + nC ≤ rRP := fun h => c3 ⟨a, h⟩
            have b' := (not_congr UInt64.le_iff_toNat_le).mp b
            rw [e2] at b'
            simp [b']
          · have a' := (not_congr UInt64.lt_iff_toNat_lt).mp a
            simp [a']
        rw [ite_eq_right (by simp [this])]; rfl

theorem encONN_three (x : Option (Nat × Nat)) :
    [(encONN x).headD 0, (encONN x).tail.headD 0, (encONN x).tail.tail.headD 0] = encONN x := by
  rcases x with _ | ⟨_, _⟩ <;> rfl

theorem bcW_ok (n : Nat) (m m' : Mem) (a : AState) (nPd k nC nR cvT rOk rMI rRP : Word)
    (r : List Word) (cv : IConstantVal) (rr : Option (Nat × Nat))
    (hR : ArenaR m a) (h : bcW n m nPd k nC nR cvT rOk rMI rRP = some (r, m'))
    (hcv : decCVp m cvT.toNat = some cv) (hb : cvT.toNat + 3 < 2 ^ 64)
    (hrr : rr = if rOk = 0 then none else some (rMI.toNat, rRP.toNat))
    (h1 : nPd.toNat < 2 ^ 32) (h2 : k.toNat < 2 ^ 32) (h3 : nC.toNat < 2 ^ 32)
    (h4 : nR.toNat < 2 ^ 32) (h5 : rMI.toNat < 2 ^ 32) (h6 : rRP.toNat < 2 ^ 32)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size) :
    ∃ x, (ConRon.Arena.blockCounts? nPd.toNat k.toNat nC.toNat nR.toNat cv rr).run a = .ok (x, a) ∧
      r = encONN x ∧ (∀ p q, x = some (p, q) → q < 2 ^ 64) ∧ IWGrow m m' ∧
      MemFrame [IW] [200] m m' := by
  cases n with
  | zero => simp [bcW] at h
  | succ n =>
  rw [bcW.arm1] at h
  obtain ⟨r1, m1, hh, h⟩ := ipK_inv h (bcW.k_block_counts_head.none ..)
  rw [bcW.k_block_counts_head.arm1] at h
  obtain ⟨r0, hr0, h⟩ := L.Arena.of_K h (bcW.k_block_counts_pure.none _)
  rw [bcW.k_block_counts_pure.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hty32, hty⟩ := decCVp_type hcv hb
  obtain ⟨bs, res, v, hrun, hsh, hlen, hview, hiff, hg, hf⟩ :=
    bchW_ok n m m1 a cvT r1 hR hh hty32 hsz hc
  rw [show r1.tail.headD 0 = r1.getD 1 0 by rw [hsh]; rfl] at hr0
  have hvr := view_run res a v hview
  have hl32 : (r1.headD 0).toNat = bs.length := hlen
  by_cases hs : r1.getD 1 0 = 2
  · obtain ⟨u, rfl⟩ := hiff.mp hs
    by_cases hl : r1.headD 0 < nPd
    · have hlt : ¬ nPd.toNat ≤ bs.length := by
        have := UInt64.lt_iff_toNat_lt.mp hl; omega
      refine ⟨none, ?_, ?_, by simp, hg, hf⟩
      · unfold ConRon.Arena.blockCounts?
        rw [← hty]
        simp only [StateT.run_bind, hrun, except_ok_bind, hvr]
        rw [ite_eq_right hlt]; rfl
      · rw [bcPure.arm1 _ _ _ _ _ _ _ _ _ _ hs hl] at hr0; obtain rfl := Option.some.inj hr0; rfl
    · have hge : nPd.toNat ≤ bs.length := by
        have := (not_congr UInt64.lt_iff_toNat_lt).mp hl; omega
      refine ⟨some (nPd.toNat, bs.length - nPd.toNat), ?_, ?_, fun p q e => by
        simp only [Option.some.injEq, Prod.mk.injEq] at e; have := (r1.headD 0).toNat_lt; omega, hg, hf⟩
      · unfold ConRon.Arena.blockCounts?
        rw [← hty]
        simp only [StateT.run_bind, hrun, except_ok_bind, hvr]
        rw [ite_eq_left hge]; rfl
      · rw [bcPure.arm2 _ _ _ _ _ _ _ _ _ _ hs hl] at hr0; obtain rfl := Option.some.inj hr0
        simp only [encONN, List.headD_cons, List.tail_cons]
        have e1 : UInt64.ofNat nPd.toNat = nPd := L.ofNat_toNat nPd
        have e2 : UInt64.ofNat (bs.length - nPd.toNat) = r1.headD 0 - nPd := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
          have := (r1.headD 0).toNat_lt
          rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; omega
        rw [e1, e2]
  · have hns : ∀ u, v ≠ ENodeView.sort u := fun u hu => hs (hiff.mpr ⟨u, hu⟩)
    refine ⟨bcTail nPd.toNat k.toNat nC.toNat nR.toNat rr, ?_, ?_, fun p q e => ?_, hg, hf⟩
    rotate_left 2
    · subst hrr
      split at e
      · cases e
      · refine bcTail_snd e fun x y hxy => ?_
        simp only [Option.some.injEq, Prod.mk.injEq] at hxy; omega
    · unfold ConRon.Arena.blockCounts?
      rw [← hty]
      simp only [StateT.run_bind, hrun, except_ok_bind, hvr]
      cases v with
      | sort u => exact absurd rfl (hns u)
      | _ => exact bcTail_run _ _ _ _ rr a
    · rw [bcPure_nonsort _ _ _ _ _ _ _ _ _ _ hs h1 h2 h3 h4 h5 h6, ← hrr] at hr0
      obtain rfl := Option.some.inj hr0; exact encONN_three _

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
  refine triple_post (piBinders_spec p ha hc hv hs hp n s₀ fuel h) ?_
  intro r s' ⟨hl, hm, _⟩
  obtain ⟨bs, e, hrun, hsh, hdec, hb1, hb2, hg, hf, hle⟩ :=
    piBW_ok n s₀.mem s'.mem a₀ fuel h r hR hm hh hsz hcl
  exact ⟨hl, hsh, ⟨bs, e, hrun, hdec, hb1, hb2⟩, hg, hf, hle⟩

/-- **`rec_target_of` refines `recTargetOf`** (through the stub `get_app_fn`). -/
@[refines ConRon.Arena.recTargetOf]
theorem recTargetOf_refines (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "rec_target_of" = some recTargetOf)
    (hst : StripProg p) (had : AdF p) (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis no nl mI ty : Word) (names : List NIdx) (hS : StageR vis fe s₀.mem a₀)
    (hty : ty.toNat < 2 ^ 32) (hnames : decHL s₀.mem no.toNat nl.toNat = some names)
    (hb : no.toNat + nl.toNat < 2 ^ 64) (hbt : no.toNat + nl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec_target_of" [no, nl, mI, ty]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀ ∧
      r = [UInt64.ofNat (AM.res (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀)] ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.recTargetOf names mI.toNat (decI ty)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (recTargetOf_spec p hv hf hp hst had n s₀ no nl mI ty) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hr, hS', hg⟩ := recTW_ok n dn fe vis s₀.mem s'.mem a₀ no nl mI ty r names hm
    hS hty hnames hb hbt
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hr, by rw [hst]; exact hS', hg⟩

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
