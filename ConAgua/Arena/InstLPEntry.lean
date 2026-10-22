import ConAgua.Arena.InstLPWalkRef3
import ConAgua.Arena.InstLPKeys
import ConAgua.Arena.PropReadRefine

/-!
# `inst_lp` refines `instLPFast coreWalkFuel` under `CoreS` (`InstLPOK`)

`inst_lp_core(ko, kc, us, e)`: the cut-off on `e`'s level-parameter bit (`der_b`, `derLW_ok`),
else the values' slice (`ls_node(us)`: a stored list, which reads back by `StoreDen.lsAll`), the
keys checked to be stored names (`keys_ok`: they read back, `keysOkW_names`), the three memo
clears (`ilw_clears`: the twin's `instLPClear`), the walk at `coreWalkFuel` (`ilwGo_ok`), the clears
again. `inst_lp(po, pl, us, e)`: the keys copied from the record pool onto the spine stack
(`keys_push`), the core, the stack top put back.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The walk's program and its entries'. -/
structure ILWEntryProg (p : Prog) : Prop where
  all : ILWAllProg p
  keys : p.lookup "keys_ok" = some keysOk

theorem ilw_coreRef {T : AM EIdx} {a a' : AState} {v : EIdx} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
    (hrun : T.run a = .ok (v, a')) (hA : CoreAfter dn m m' a' vis fe M eb) (hv : v = decH r)
    (hr : ResH r) : CoreRef T a decH dn m vis fe M eb r m' := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hok, hst ▸ hA, hres.trans hv, hr⟩

/-- One walk-memo clear through `callW`: the stamp check and the cleared memory. -/
theorem ilw_clearCall {p : Prog} {k : Nat} {f : FnName} (S : MemoSch) (hf : p.lookup f = some (memoClearG S))
    {m m' : Mem} {r : List Word} (h : callW p k f [] m = some (r, m')) :
    rdW (m.arr64 CTL) S.cs + 2 ≠ 0 ∧ m' = mclearG S m := by
  obtain ⟨s', hs', -, hw, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (memoClearG_spec S p f hf k _) h
  exact ⟨hw, hs'.symm.trans hm⟩

/-- **The three clears before (or after) the walk** keep `CoreS`: the memo stamps only. -/
theorem ilw_clears_core {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hLP : LPMemos (mclearG lplsSch (mclearG lplSch (mclearG lpSch m)))) :
    CoreS dn (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) a vis fe M eb ∧
      StackKept m (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) := by
  have f1 := mclearG_frame lpSch m
  have f2 := mclearG_frame lplSch (mclearG lpSch m)
  have f3 := mclearG_frame lplsSch (mclearG lplSch (mclearG lpSch m))
  have hf : MemFrame [] [lpSch.cs, lpSch.cs + 1, lplSch.cs, lplSch.cs + 1, lplsSch.cs, lplsSch.cs + 1] m
      (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) :=
    ((f1.mono (by simp) (by simp)).trans (f2.mono (by simp) (by simp))).trans (f3.mono (by simp) (by simp))
  have hD : ArenaD (mclearG lplsSch (mclearG lplSch (mclearG lpSch m))) a :=
    ⟨hS.arena.1.frame (by simp) (by simp [arenaCtl, storeCtl, memoCtl, lpSch, lplSch, lplsSch]) hf,
      DerR.frameM _ _ _ _ hf (by simp) a hS.arena.2⟩
  exact hS.of_walk hD rfl hf (by simp) (by simp [lpSch, lplSch, lplsSch])
    (hS.memos.frameLP hf hLP (by simp) (by simp [lpSch, lplSch, lplsSch])) (by simp)
    (by simp [lpSch, lplSch, lplsSch]) (by simp) (by simp [lpSch, lplSch, lplsSch])

section core
variable {p : Prog} (hp : ILWEntryProg p)
include hp

/-- **`inst_lp_core(ko, kc, us, e)` refines `instLPFast coreWalkFuel lps us e`**, the keys `lps` a
slice of the spine stack below its top. -/
theorem ilwCore_ok (k : Nat) {m m' : Mem} {a : AState} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb ko kc us e : Word} {lps : List NIdx} {rs : List Word}
    (hS : CoreS dn m a vis fe M eb) (hh : HW e) (hus : HW us)
    (hks : hslice? (m.arr64 SPN) ko.toNat kc.toNat = some lps) (hkt : ko.toNat + kc.toNat ≤ (spTop m).toNat)
    (hc : callW p (k + 1) "inst_lp_core" [ko, kc, us, e] m = some (rs, m')) :
    CoreRef (instLPFast coreWalkFuel lps (decI us) (decE e)) a decH dn m vis fe M eb rs m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (instLPCore_spec p hp.all.lev.ilw k _ ko kc us e) hc
  rw [hs'] at hW
  change ilwCoreW p k m ko kc us e = some (rs.headD 0, m') at hW
  unfold ilwCoreW at hW
  -- `der_b`: the cut-off
  cases h1 : callW p k "der_b" [e] m with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨d, m₁⟩ := q
  rw [h1, ilwCoreD_some] at hW
  obtain ⟨s1, hs1, -, hm1, -, -, hlp⟩ :=
    triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (derB_spec p hp.all.mkp.spine.derb k _ e) h1
  have hm₁ : m₁ = m := hs1.symm.trans hm1
  subst hm₁
  rw [hlp] at hW
  have hd := derLW_ok m₁ a hS.arena.1 hS.arena.2 e hh
  by_cases h0 : exprLPW m₁ e = 0
  · rw [if_pos h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, rfl⟩ := hW
    rw [hd, lpW_zero_iff] at h0
    refine ilw_coreRef (v := decE e) (a' := a) ?_ ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
      (by simp only [decH, ← hr, decE_and32]) (by unfold ResH HW; rw [← hr]; exact and32_lt e)
    unfold instLPFast
    rw [StateT.run_bind, derivedE_run]
    simp only [except_ok_bind, h0, Bool.not_false, ↓reduceIte]; rfl
  rw [if_neg h0] at hW
  have hlp' : lpOfData (a.store.derived (decE e)) = true := by
    rw [hd, lpW_zero_iff] at h0; simpa using h0
  -- `ls_node(us)`: the values
  by_cases hne : lsNodeW m₁ us = []
  · rw [if_pos hne] at hW; cases hW
  rw [if_neg hne] at hW
  obtain ⟨ids, hvw, -, -⟩ := lsNodeW_view hS.arena.1 hus hne
  obtain ⟨hln, hvt, hsl⟩ := lsNodeW_store hS.arena.1 hus hvw
  obtain ⟨vs, hvs⟩ := hS.den.lsAll (decI us) (by rw [hvw]; rfl)
  have hvsl : denoteLList a.store.ls ids = some vs := by
    unfold denoteLs at hvs; rw [hvw] at hvs; exact hvs
  rw [hln] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  generalize lsO m₁ (tierW us) (idxW us) = vo at hW hvt hsl
  generalize lsL m₁ (tierW us) (idxW us) = vc at hW hvt hsl
  -- `keys_ok`: the keys read back
  cases h2 : callW p k "keys_ok" [ko, kc] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨r2, m₂⟩ := q
  rw [h2, ilwC0_some] at hW
  obtain ⟨s2, hs2, -, hm2, hk2⟩ :=
    triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩) (keysOk_spec p hp.keys k _ ko kc) h2
  have hm₂ : m₂ = m₁ := hs2.symm.trans hm2
  subst hm₂
  obtain ⟨ks, hksd, hnms⟩ := keysOkW_names hS.arena.1 hS.nwf k ko kc lps hk2 hks
    (by have := (spTop m₂).toNat_lt; omega)
  -- the clears
  cases h3 : callW p k "ilp_clear" [] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q =>
  obtain ⟨r3, m₃⟩ := q
  rw [h3, ilwC1_some] at hW
  obtain ⟨hw3, rfl⟩ := ilw_clearCall lpSch hp.all.lev.ilw.ilpc h3
  cases h4 : callW p k "ilpl_clear" [] (mclearG lpSch m₂) with
  | none => rw [h4] at hW; cases hW
  | some q =>
  obtain ⟨r4, m₄⟩ := q
  rw [h4, ilwC2_some] at hW
  obtain ⟨hw4, rfl⟩ := ilw_clearCall lplSch hp.all.lev.ilw.ilplc h4
  cases h5 : callW p k "ilpls_clear" [] (mclearG lplSch (mclearG lpSch m₂)) with
  | none => rw [h5] at hW; cases hW
  | some q =>
  obtain ⟨r5, m₅⟩ := q
  rw [h5, ilwC3_some] at hW
  obtain ⟨hw5, rfl⟩ := ilw_clearCall lplsSch hp.all.lev.ilw.ilplsc h5
  -- the twin's readbacks and clear
  obtain ⟨c1, hrn, hrc1, e1L, e1Ls, e1⟩ := readNamesM_run a hS.den.readN lps ks hksd
  have hrls : ReadLsCOK { a with caches := c1 } := by
    intro h' l' e'; rw [e1Ls] at e'; exact hS.readLs h' l' e'
  obtain ⟨c2, hrl, hrc2, e2L, e2N, e2⟩ := lp_readLevelsM_run { a with caches := c1 } (decI us) vs hvs hrls
  have hS₂ : CoreS dn m₂ { a with caches := c2 } vis fe M eb := by
    have := hS.readCaches c1.readNC c2.readLsC
      (by rw [show ({ a.caches with readNC := c1.readNC, readLsC := c2.readLsC } : Caches) = c2 by
            rw [e2, e1]]; exact hrc2)
      (by rw [show ({ a.caches with readNC := c1.readNC } : Caches) = c1 by rw [e1]]; exact hrc1)
    rwa [show ({ a.caches with readNC := c1.readNC, readLsC := c2.readLsC } : Caches) = c2 by
      rw [e2, e1]] at this
  have hM₃ := ilw_clears hS₂.memos.2.2.2.2.2 hw3 hw4 hw5 { a with caches := c2 }
  obtain ⟨hS₃', hSt₃⟩ := ilw_clears_core hS₂ hM₃.lpMemos
  have hS₃ := hS₃'.lpMemos ∅ ∅ ∅
  have hE₂ : ILWEnv m₂ a ko kc vo vc ks ids vs := ⟨hnms, hkt, hsl, hvt, hvsl⟩
  have hE₃ := hE₂.keep hSt₃ (a' := { ({ a with caches := c2 } : AState) with memos :=
    { a.memos with instLPC := ∅, instLPLC := ∅, instLPLsC := ∅ } }) (ILWGrow.of_lss rfl)
  -- the walk
  cases h6 : callW p k "lp_go" [e, ko, kc, vo, vc, 4000000000] (mclearG lplsSch (mclearG lplSch (mclearG lpSch m₂))) with
  | none => rw [h6] at hW; cases hW
  | some q =>
  obtain ⟨r6, m₆⟩ := q
  rw [h6, ilwCoreK_some] at hW
  obtain ⟨a₄, r4, ⟨M₄, hS₄, hK₄, hSt₄⟩, hM₄, -, hr6⟩ :=
    ilwGo_ok hp.all k _ m₆ _ dn vis fe M eb e ko kc vo vc 4000000000 ks ids vs r6 hS₃ hM₃ hE₃ hh h6
  -- the clears after it
  cases h7 : callW p k "ilp_clear" [] m₆ with
  | none => rw [h7] at hW; cases hW
  | some q =>
  obtain ⟨r7, m₇⟩ := q
  rw [h7, ilwE1_some] at hW
  obtain ⟨hw7, rfl⟩ := ilw_clearCall lpSch hp.all.lev.ilw.ilpc h7
  cases h8 : callW p k "ilpl_clear" [] (mclearG lpSch m₆) with
  | none => rw [h8] at hW; cases hW
  | some q =>
  obtain ⟨r8, m₈⟩ := q
  rw [h8, ilwE2_some] at hW
  obtain ⟨hw8, rfl⟩ := ilw_clearCall lplSch hp.all.lev.ilw.ilplc h8
  cases h9 : callW p k "ilpls_clear" [] (mclearG lplSch (mclearG lpSch m₆)) with
  | none => rw [h9] at hW; cases hW
  | some q =>
  obtain ⟨r9, m₉⟩ := q
  rw [h9, ilwE3_some] at hW
  obtain ⟨hw9, rfl⟩ := ilw_clearCall lplsSch hp.all.lev.ilw.ilplsc h9
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  have hM₉ := ilw_clears hM₄.lpMemos hw7 hw8 hw9 a₄
  obtain ⟨hS₉, hSt₉⟩ := ilw_clears_core hS₄ hM₉.lpMemos
  refine ilw_coreRef (v := decE (r6.headD 0)) ?_
    ⟨M₄, hS₉.lpMemos ∅ ∅ ∅, hK₄, hSt₃.trans (hSt₄.trans hSt₉)⟩
    (by simp only [decH, ← hr, decE_and32]) (by unfold ResH HW; rw [← hr]; exact and32_lt _)
  have hfu : (4000000000 : Word).toNat = coreWalkFuel := rfl
  rw [hfu] at r4
  unfold instLPFast
  rw [StateT.run_bind, derivedE_run]
  simp only [except_ok_bind, hlp', Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hrn, hrl,
    instLPClear_run, r4]
  rfl

end core

end L.Arena
