module

public import ConAgua.Arena.IndRealOpf
import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.StageInst1
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.WhnfEntry
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarStore
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.ProjStore

@[expose] public section

/-!
# `open_pis_at_fvars_f` only grows the pool, at any arguments

`open_pis_at_fvars_f` is a leaf of the core stage's write-set check (`IndTwin.lean`: the core
reaches it through `infer_proj`'s `proj_guard_rows`): it writes the pool `IW`, which the core's
write set leaves out. What it does to the pool, at any arguments and memory:

* the walks `opf_go`/`opa_go` and their callees (`opgFns`) do not write the pool or its top
  (`opgP_closed`, decided);
* the tail allocates a fresh slice and copies the stack slice into it (`allocW`, `s2iW_wr`,
  `recMem_post`);
* so `IWOK` is kept and the pools only grow (`opfF_grow`).

`iwKeep`: a frame that misses the pools and their tops keeps `IWOK` and is an `IWGrow`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **A frame that misses the pools and their tops** keeps `IWOK`, and the pools stay. -/
theorem iwKeep {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (IW : TieredArray) ∉ A ∧ (EREC : TieredArray) ∉ A ∧ tier1 EREC ∉ A)
    (hC : (129 : Word) ∉ C ∧ (130 : Word) ∉ C ∧ (200 : Word) ∉ C) (hI : IWOK m) :
    IWOK m' ∧ IWGrow m m' := by
  have hW := hf.arr IW hA.1 (by decide)
  have hE := hf.arr EREC hA.2.1 (by decide)
  have hE1 := hf.arr (tier1 EREC) hA.2.2 (by decide)
  have h129 := hf.ctl 129 hC.1
  have h130 := hf.ctl 130 hC.2.1
  have h200 := hf.ctl 200 hC.2.2
  exact ⟨IWOK.of_keep hf hA hC hI,
    ⟨by simp [iwTop, h200], by simp [erTop, h129], fun i _ => by rw [hW], fun i _ => by rw [hE],
      by simp [erecTop1, h130], fun i _ => by rw [hE1]⟩⟩

/-- A write of `CTL[c]`, `c` none of the tops, keeps `IWOK`, and the pools stay. -/
theorem iwKeep_ctl {m : Mem} {c : Word} (v : Word) (hc : c ≠ 129 ∧ c ≠ 130 ∧ c ≠ 200) (hI : IWOK m) :
    IWOK (m.set64 CTL c v) ∧ IWGrow m (m.set64 CTL c v) :=
  iwKeep (MemFrame.setCtl m c v) (by simp) (by simp only [List.mem_singleton]; grind) hI

/-! ## The walks leave the pool alone -/

/-- `opf_go`'s and `opa_go`'s call closure. -/
def opgFns : List FnName :=
  ["opf_go", "opa_go", "spn_push", "e_view", "fvar_find", "fvar_push", "intern_fvar"] ++
    instListFns ++ instFns

/-- What the walks write: `opfA` without the pool. -/
def opgA : List TieredArray := [(SPN : TieredArray), (FVREC : TieredArray), (FVSLOT : TieredArray),
  (FVLP : TieredArray), tier1 FVREC, tier1 FVSLOT, tier1 FVLP] ++ instListA ++ instA
/-- `opfC` without the pool's top. -/
def opgC : List Word := [136, 26, 27] ++ instListC ++ instC

theorem opgP_closed : closedA opfP opgA opgC opgFns = true := by decide +kernel

theorem opgA_not : (IW : TieredArray) ∉ opgA ∧ (EREC : TieredArray) ∉ opgA ∧ tier1 EREC ∉ opgA := by
  decide
theorem opgC_not : (129 : Word) ∉ opgC ∧ (130 : Word) ∉ opgC ∧ (200 : Word) ∉ opgC := by decide

/-! ## The entry at any arguments -/

theorem opfTopK_specV (p : Prog) (hp : p.lookup "open_pis_at_fvars_f" = some L.Stubs.openPisAtFvarsFL)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hs : p.lookup "spn_to_iw" = some spnToIwL)
    (k : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "open_pis_at_fvars_f" vs
    ⦃fun r s' => LocEq s' s₀ ∧
      opfTopK p k s₀.mem (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Stubs.openPisAtFvarsFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, callW_spec p k "opf_go",
      callW_spec p k "opa_go",
      iwAlloc_specW p ha k, s2i_spec p hs k] <;>
    finish (gen := 20) [opfTopK, opfK2, opfK3, opfTail_some, ntBW, Locals.init]

/-! ## The pool only grows -/

/-- The tail: a fresh slice, the stack slice copied into it, the stack top put back. -/
theorem opfTail_grow {k : Nat} {n co b : Word} {m2 m' : Mem} {r : List Word}
    (h : opfTail k n co b (allocW m2 n) = some (r, m')) (hI : IWOK m2) :
    IWOK m' ∧ IWGrow m2 m' := by
  rcases ha : allocW m2 n with _ | ⟨q, m3⟩
  · rw [ha] at h; cases h
  rw [ha, opfTail_some] at h
  obtain ⟨r4, m4, h4, h⟩ := kSome_inv (K := (ntBW · _)) h rfl (fun _ _ => rfl)
  simp only [bW_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨rfl, rfl, hroom⟩ := allocW_facts ha hI.iwSize
  rw [s2iW_wr _ _ _ _ _ _ _ h4]
  have hlen := spnWs_length (allocMem m2 n) co n.toNat
  obtain ⟨-, hg, hf, htop⟩ := recMem_post m2 (spnWs (allocMem m2 n) co n.toNat) n hlen.symm
    (by simpa using hI.ctl) (by rw [hlen]; exact hroom) hI.iwSize
  have hsz := hI.iwSize
  have hI4 : IWOK (wrIW (allocMem m2 n) (rdW (m2.arr64 CTL) 200) (spnWs (allocMem m2 n) co n.toNat)) := by
    refine IWOK.of_iw hf hI ?_
    simp only [iwTop, htop, hf.size IW]
    rw [UInt64.toNat_add]; omega
  obtain ⟨hI5, hg5⟩ := iwKeep_ctl (c := 136) co (by decide) hI4
  exact ⟨hI5, hg.trans hg5⟩

/-- **`open_pis_at_fvars_f`'s body keeps `IWOK` and only grows the pools**, given its walks'
write set. -/
theorem opfTopK_grow {p : Prog} (hcl : closedA p opgA opgC opgFns = true) {k : Nat} {m m' : Mem}
    {n e i : Word} {r : List Word} (h : opfTopK p k m n e i = some (r, m')) (hI : IWOK m) :
    IWOK m' ∧ IWGrow m m' := by
  unfold opfTopK at h
  obtain ⟨-, h⟩ := of_ite_none h
  obtain ⟨-, h⟩ := of_ite_none h
  obtain ⟨r1, m1, h1, h⟩ := kSome_inv (K := (ntBW · _)) h rfl (fun _ _ => rfl)
  simp only [bW_some] at h
  obtain ⟨hI1, hg1⟩ := iwKeep (run_memFrame hcl (f := "opf_go") (by decide) (run_of_callW h1)).1 opgA_not opgC_not hI
  unfold opfK2 at h
  by_cases hz : r1.headD 0 = 0
  · rw [ite_eq_left hz] at h
    obtain ⟨hI2, hg2⟩ := iwKeep_ctl (c := 136) (rdW (m.arr64 CTL) 136) (by decide) hI1
    obtain ⟨r2, m2, h2, h⟩ := kSome_inv (K := (ntBW · _)) h rfl (fun _ _ => rfl)
    simp only [bW_some] at h
    obtain ⟨hI3, hg3⟩ := iwKeep (run_memFrame hcl (f := "opa_go") (by decide) (run_of_callW h2)).1 opgA_not opgC_not hI2
    unfold opfK3 at h
    by_cases hz2 : r2.headD 0 = 0
    · rw [ite_eq_left hz2] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hI4, hg4⟩ := iwKeep_ctl (c := 136) (rdW (m.arr64 CTL) 136) (by decide) hI3
      exact ⟨hI4, ((hg1.trans hg2).trans hg3).trans hg4⟩
    · rw [ite_eq_right hz2] at h
      obtain ⟨hI4, hg4⟩ := opfTail_grow h hI3
      exact ⟨hI4, ((hg1.trans hg2).trans hg3).trans hg4⟩
  · rw [ite_eq_right hz] at h
    obtain ⟨hI2, hg2⟩ := opfTail_grow h hI1
    exact ⟨hI2, hg1.trans hg2⟩

/-- **`open_pis_at_fvars_f`'s model keeps `IWOK` and only grows the pools**, at any arguments. -/
theorem opfF_grow {m m' : Mem} {args r : List Word} (h : opfF m args = some (r, m')) (hI : IWOK m) :
    IWOK m' ∧ IWGrow m m' := by
  obtain ⟨N, hc⟩ := callF_run h
  rcases N with _ | k
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hk⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (opfTopK_specV opfP ((ProgHas.refl opfP).get _) ((ProgHas.refl opfP).get _)
      ((ProgHas.refl opfP).get _) k _ args) hc
  rw [hs'] at hk
  exact opfTopK_grow opgP_closed hk hI

end L.Ind

end
