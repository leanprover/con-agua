module

public import ConAgua.Arena.IWFrame
public import ConAgua.Arena.IndCopy
public import ConAgua.Arena.IndSum
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.Env
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndSum
import ConAgua.L.ModelGen

@[expose] public section

/-!
# StructElimLevel: `ConRon.Arena.structElimLevel`, `ConRon.Arena.structPsAt.go`

The refinement theorems `structElimLevel_refines`, `structPsAtGo_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `struct_elim_level` -/

/-- **`struct_elim_level` refines `structElimLevel`** under `ArenaR`: the fresh parameter at the
large eliminator, `zero` at the small one. -/
@[refines ConRon.Arena.structElimLevel]
theorem structElimLevel_refines (p : Prog) (hpf1 : p.lookup "param_find" = some paramFind)
    (hpp1 : p.lookup "param_push" = some paramPush)
    (hp1 : p.lookup "intern_param" = some internParam)
    (hpf2 : p.lookup "zero_find" = some zeroFind) (hpp2 : p.lookup "zero_push" = some zeroPush)
    (hp2 : p.lookup "intern_zero" = some internZero)
    (hp : p.lookup "struct_elim_level" = some structElimLevelL)
    (a₀ : AState) (n : Nat) (s₀ : St) (elim large : Word) (hR : ArenaR s₀.mem a₀)
    (helim : elim.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "struct_elim_level" [elim, large]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structElimLevel (decI elim) (large != 0)) a₀ ∧
      ArenaR s'.mem (AM.st (structElimLevel (decI elim) (large != 0)) a₀) ∧
      AM.res (structElimLevel (decI elim) (large != 0)) a₀ = decI (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structElimLevelL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        internParam_refinesA p hpf1 hpp1 hp1 a₀ n,
        internZero_refinesA p hpf2 hpp2 hp2 a₀ n] <;>
      finish [structElimLevel]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_ps_at_go`: a recursive refinement through callee models (the lane's template)

The recipe (lane `levels`' shape, made explicit for a recursion that interns and allocates):
1. a **word model** of the L function that calls the callees' word models (`binternW`, `consW`)
   and itself at the L fuel, one guarded equation per arm;
2. its `vcgen` spec, with the callees' **model** specs (no twin values in their hypotheses);
3. a **relational lemma** by induction on the L fuel: a model run from a memory related to `a`
   gives a twin run (`.run a = .ok (xs, a')`) and the relation after;
4. the census theorem: 2 and 3 composed by `triple_post`. -/

/-- **`struct_ps_at_go(o, nP, N, k)`'s model `psGoW`** (generated). -/
l_model structPsAtGo_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hp : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  fns [hp ↦ psGoW list]
  specs [iwAlloc_specW p ha n, slCons_specW p ha hc hsc n, internBVar_spec p hpf hpp hib n]
  grind [arena_grind]

end L.Ind

namespace L.Ind

open L.Arena

/-- **The model of `struct_ps_at_go` refines `structPsAt.go`** from a memory related to `a` by
`ArenaR`. -/
theorem psGoW_ok (n : Nat) : ∀ (m m' : Mem) (a : AState) (o nP N k : Word) (r : List Word),
    psGoW n m o nP N k = some (r, m') → ArenaR m a → (m.arr64 IW).size < 2 ^ 64 →
    200 < (m.arr64 CTL).size → o.toNat + nP.toNat < 2 ^ 64 → k.toNat + N.toNat ≤ nP.toNat →
    ∃ xs a', (structPsAt.go o.toNat nP.toNat N.toNat k.toNat).run a = .ok (xs, a') ∧
      ArenaR m' a' ∧ IWGrow m m' ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  induction n with
  | zero => intro m m' a o nP N k r h; simp [psGoW] at h
  | succ n ih =>
    intro m m' a o nP N k r h hR hsz hc hon hkN
    by_cases hN : N = 0
    · subst hN
      rw [psGoW.arm1 n m o nP 0 k rfl] at h
      simp only [allocW] at h
      by_cases h1 : m.len64 IW < rdW (m.arr64 CTL) 200
      · simp [h1, psGoW.k_iw_alloc] at h
      by_cases h2 : m.len64 IW - rdW (m.arr64 CTL) 200 < 0
      · simp at h2
      simp only [h1, h2, ite_false, psGoW.k_iw_alloc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hf := allocMem_frame m 0
      have hlen : (m.len64 IW).toNat = (m.arr64 IW).size := by simp [Mem.len64]; omega
      have htop : iwTop m ≤ (m.arr64 IW).size := by
        have : ¬ (m.len64 IW).toNat < (rdW (m.arr64 CTL) 200).toNat := h1
        simp only [iwTop]; omega
      refine ⟨[], a, by simp [structPsAt.go]; rfl, ArenaR.frame
        (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR,
        allocMem_grow m 0 (by simp; omega) hc, hf.size, by simp [decHL, hslice?], ?_⟩
      simp [iwTop, allocMem, rdW_set64, hc]
    · rw [psGoW.arm2 (hc1 := hN)] at h
      rcases hI : binternW m (o + nP - 1 - k) with _ | ⟨b, m1⟩
      · rw [hI] at h; simp [psGoW.k_intern_bvar] at h
      rw [hI] at h
      by_cases hb : 4294967296 ≤ b
      · rw [psGoW.k_intern_bvar.abort1 (hc1 := hb)] at h; simp at h
      rw [psGoW.k_intern_bvar.arm1 (hc1 := hb)] at h
      rcases hr : psGoW n m1 o nP (N - 1) (k + 1) with _ | ⟨r2, m2⟩
      · rw [hr] at h; simp [psGoW.k_struct_ps_at_go] at h
      rw [hr] at h
      simp only [psGoW.k_struct_ps_at_go] at h
      rcases hcw : consW n m2 b (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩
      · rw [hcw] at h; simp [psGoW.k_sl_cons] at h
      rw [hcw] at h
      simp only [psGoW.k_sl_cons, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- the interning
      have hN1 : 1 ≤ N.toNat := by
        have : N.toNat ≠ 0 := fun h0 => hN (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hb32 : b.toNat < 2 ^ 32 := by
        have : ¬ (4294967296 : Nat) ≤ b.toNat := hb
        omega
      obtain ⟨hok, hX, hres⟩ := bintern_correct m a hR.bvar _ _ _ hI
      have hI' := hI
      have hfr := consInternM_frame bvarCS_wf hI'
      have hR1 := hR.lift_bvar _ _ _ _ hX hfr
        (AM.st_proto bvarLens _ _ _ _ _ _ _ a (internE_bvar_run _ a) hok)
      have hg1 := IWGrow.of_keep hfr (by decide) (by decide)
      have hs1 : ∀ b, (m1.arr64 b).size = (m.arr64 b).size := hfr.size
      have hiw1 : m1.arr64 IW = m.arr64 IW := hfr.arr IW (by decide) (by decide)
      -- the recursion
      have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hN1' : (N - 1).toNat = N.toNat - 1 := by rw [UInt64.toNat_sub]; simp; omega
      obtain ⟨xs, a2, hrun2, hR2, hg2, hs2, hd2, ht2⟩ := ih m1 m2 _ o nP (N - 1) (k + 1) r2 hr hR1
        (by rw [hs1]; exact hsz) (by rw [hs1]; exact hc) hon (by rw [hk1, hN1']; omega)
      -- the cons
      obtain ⟨hr3, hd3, hg3, hf3, -, ht3⟩ := consW_dec hcw (by rw [hs2, hs1]; exact hsz)
        (by rw [hs2, hs1]; exact hc) (by omega) hb32 hd2
      subst hr3
      refine ⟨decE b :: xs, a2, ?_, ArenaR.frame
        (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf3 hR2,
        (hg1.trans hg2).trans hg3, fun b => by rw [hf3.size, hs2, hs1], ?_, by simpa using ht3⟩
      · have hu : (o + nP - 1 - k).toNat = o.toNat + nP.toNat - 1 - k.toNat := by
          rw [UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_add]; simp; omega
        have hNs : N.toNat = (N.toNat - 1) + 1 := by omega
        rw [hNs]
        simp only [structPsAt.go]
        rw [StateT.run_bind, ← hu, AM.run_of_ok _ _ hok, hres]
        simp only [bind, Except.bind]
        rw [← hk1, ← hN1']
        simp only [StateT.run] at hrun2
        simp only [StateT.bind, StateT.run, hrun2]
        rfl
      · simpa [decE_eq] using hd3

end L.Ind

namespace L.Ind

open L.Arena

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hp : p.lookup "struct_ps_at_go" = some structPsAtGoL)
include ha hc hsc hpf hpp hib hp

/-- **`struct_ps_at_go` refines `structPsAt.go`** under `ArenaR`: the twin's run succeeds, the
arena relation holds after it, the pool only grew, and the result slice decodes the twin's
list. -/
@[refines ConRon.Arena.structPsAt.go]
theorem structPsAtGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (o nP N k : Word)
    (hR : ArenaR s₀.mem a₀) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hc2 : 200 < (s₀.mem.arr64 CTL).size)
    (hon : o.toNat + nP.toNat < 2 ^ 64) (hkN : k.toNat + N.toNat ≤ nP.toNat) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_ps_at_go" [o, nP, N, k]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (structPsAt.go o.toNat nP.toNat N.toNat k.toNat) a₀ ∧
      ArenaR s'.mem (AM.st (structPsAt.go o.toNat nP.toNat N.toNat k.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structPsAt.go o.toNat nP.toNat N.toNat k.toNat) a₀); ⊤⦄ := by
  refine triple_post (structPsAtGo_spec p ha hc hsc hpf hpp hib hp n s₀ o nP N k) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', hrun, hR', hg, -, hd, -⟩ := psGoW_ok n _ _ _ _ _ _ _ _ hm hR hsz hc2 hon hkN
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hR', hg, by rw [hres]; exact hd⟩

end census

end L.Ind

end
