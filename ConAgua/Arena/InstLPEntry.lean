import ConAgua.Arena.InstLPWalkRef3
import ConAgua.Arena.InstLPKeys
import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.RecFireCore

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
    ⟨hS.arena.1.frame (by simp) (by simp [arenaCtl, storeCtl, memoCtl]) hf,
      DerR.frameM _ _ _ _ hf (by simp) a hS.arena.2⟩
  exact hS.of_walk hD rfl hf (by simp) (by simp)
    (hS.memos.frameLP hf hLP (by simp) (by simp)) (by simp)
    (by simp) (by simp) (by simp)

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
  · rw [ite_eq_left h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, rfl⟩ := hW
    rw [hd, lpW_zero_iff] at h0
    refine ilw_coreRef (v := decE e) (a' := a) ?_ ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
      (by simp only [decH, ← hr, decE_and32]) (by unfold ResH HW; rw [← hr]; exact and32_lt e)
    unfold instLPFast
    rw [StateT.run_bind, derivedE_run]
    simp only [except_ok_bind, h0, Bool.not_false, ↓reduceIte]; rfl
  rw [ite_eq_right h0] at hW
  have hlp' : lpOfData (a.store.derived (decE e)) = true := by
    rw [hd, lpW_zero_iff] at h0; simpa using h0
  -- `ls_node(us)`: the values
  by_cases hne : lsNodeW m₁ us = []
  · rw [ite_eq_left hne] at hW; cases hW
  rw [ite_eq_right hne] at hW
  obtain ⟨ids, hvw, -, -⟩ := lsNodeW_view hS.arena.1 hus hne
  obtain ⟨hln, hvt, hsl⟩ := lsNodeW_store hS.arena.1 hus hvw
  obtain ⟨vs, hvs⟩ := hS.den.lsAll (decI us) (by rw [hvw]; rfl)
  have hvsl : denoteLList a.store.ls ids = some vs := by
    unfold denoteLs at hvs; rw [hvw] at hvs; exact hvs
  rw [hln] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  generalize tfld m₁ LVLS (tierW us) (idxW us) 0 = vo at hW hvt hsl
  generalize tfld m₁ LVLS (tierW us) (idxW us) 1 = vc at hW hvt hsl
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

/-! ## `inst_lp`: the keys from the record pool -/

/-- **`ek_copy` copies a handle slice**: the record pool's slice `(s, l)` lands on the stack at `d`,
below `d` nothing changes. -/
theorem ekCopyW_slice : ∀ (lps : List NIdx) (n : Nat) (m m' : Mem) (s d l : Word),
    hslice? (m.arr64 EREC) s.toNat l.toNat = some lps → d.toNat + l.toNat ≤ (m.arr64 SPN).size →
    (m.arr64 SPN).size < 2 ^ 63 → s.toNat + l.toNat < 2 ^ 64 → ekCopyW n m s d l = some m' →
    hslice? (m'.arr64 SPN) d.toNat l.toNat = some lps ∧ MemFrame [SPN] [] m m' ∧
      ∀ i : Word, i.toNat < d.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i := by
  intro lps
  induction lps with
  | nil =>
    intro n m m' s d l hs hb hsz hsl hW
    have hl : l.toNat = 0 := by
      rcases hk' : l.toNat with _ | j
      · rfl
      · rw [hk', lp_hslice_succ] at hs
        simp only [Option.bind_eq_bind] at hs
        cases e : (hd? (m.arr64 EREC) s.toNat : Option NIdx) with
        | none => simp [e] at hs
        | some x =>
          cases e' : (hslice? (m.arr64 EREC) (s.toNat + 1) j : Option (List NIdx)) with
          | none | some xs => simp [e, e'] at hs
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by simpa using hl)
    subst hl0
    cases n with
    | zero => simp [ekCopyW] at hW
    | succ n =>
    rw [ekCopyW_zero n m s d 0 rfl] at hW; cases hW
    exact ⟨by simp [hslice?], MemFrame.refl _ _ _, fun _ _ => rfl⟩
  | cons x xs ih =>
    intro n m m' s d l hs hb hsz hsl hW
    rcases hk' : l.toNat with _ | j
    · rw [hk'] at hs; simp [hslice?] at hs
    rw [hk', lp_hslice_succ] at hs
    simp only [Option.bind_eq_bind] at hs
    cases e : (hd? (m.arr64 EREC) s.toNat : Option NIdx) with
    | none => simp [e] at hs
    | some x' =>
    cases e' : (hslice? (m.arr64 EREC) (s.toNat + 1) j : Option (List NIdx)) with
    | none => simp [e, e'] at hs
    | some xs' =>
    simp only [e, e', Option.bind_some, Option.pure_def, Option.some.injEq, List.cons.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hl0 : l ≠ 0 := fun h0 => by subst h0; simp at hk'
    cases n with
    | zero => simp [ekCopyW] at hW
    | succ n =>
    rw [ekCopyW_succ n m s d l hl0] at hW
    have hd1 : (d + 1).toNat = d.toNat + 1 := toNat_succ_lt (by omega)
    have hs1 : (s + 1).toNat = s.toNat + 1 := toNat_succ_lt (by omega)
    have hlm : (l - 1).toNat = j := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have hsz₁ : ((m.set64 SPN d (rdW (m.arr64 EREC) s)).arr64 SPN).size = (m.arr64 SPN).size :=
      Mem.size_arr64_set64 _ _ _ _
    have herec : (m.set64 SPN d (rdW (m.arr64 EREC) s)).arr64 EREC = m.arr64 EREC :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    obtain ⟨hk', hf', hb'⟩ := ih n _ m' (s + 1) (d + 1) (l - 1) (by rw [herec, hs1, hlm]; exact e')
      (by rw [hsz₁, hd1, hlm]; omega) (by rw [hsz₁]; exact hsz) (by rw [hs1, hlm]; omega) hW
    have hdl : d.toNat < (m.arr64 SPN).size := by omega
    have hd : rdW (m'.arr64 SPN) d = rdW (m.arr64 EREC) s := by
      rw [hb' d (by rw [hd1]; omega), rdW_set64]; simp [hdl]
    refine ⟨?_, (MemFrame.set64 _ _ (by decide) _ _).trans hf', ?_⟩
    · rw [lp_hslice_succ]
      have hsize : d.toNat < (m'.arr64 SPN).size := by rw [hf'.2.2.1 SPN, hsz₁]; exact hdl
      have hd' : (hd? (m'.arr64 SPN) d.toNat : Option NIdx) = some x' := by
        rw [← e]; simp only [hd?]
        have h1 : (m'.arr64 SPN)[d.toNat]? = some (rdW (m'.arr64 SPN) d) := by simp [rdW, hsize]
        have h2 : (m.arr64 EREC)[s.toNat]? = some (rdW (m.arr64 EREC) s) := by
          cases ee : (m.arr64 EREC)[s.toNat]? with
          | none => simp [hd?, ee] at e
          | some v => simp [rdW, ee]
        rw [h1, h2, hd]
      rw [hd1, hlm] at hk'
      simp [hd', hk']
    · intro i hi
      rw [hb' i (by rw [hd1]; omega), rdW_set64]
      have : ¬ d = i := fun e => by subst e; omega
      simp [this]

/-- **`inst_lp(po, pl, us, e)` refines `instLPFast coreWalkFuel lps us e`** under `CoreS`, the keys
`lps` a slice of the record pool (`InstLPOK`). -/
@[refines ConRon.Arena.instLPFast]
theorem instLP_refines (p : Prog) (hp : ILWEntryProg p) : InstLPOK p := by
  intro n s₀ a₀ dn vis fe M eb po pl us e lps hS he hus hlps
  apply CoreSpec.of_call
  intro rs m' hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ k =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (instLP_spec p hp.all.lev.ilw k _ po pl us e) hc
  rw [hs'] at hW
  change ilwLPW p k s₀.mem po pl us e = some (rs.headD 0, m') at hW
  unfold ilwLPW at hW
  generalize s₀.mem = m at hS hlps hW
  -- `keys_push`
  cases h1 : callW p k "keys_push" [po, pl] m with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨bs, m₁⟩ := q
  rw [h1, ilwLPK₁_some] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (keysPush_spec p hp.all.lev.ls.toLvSubProg k _ po pl) h1
  rw [hs1] at hW1
  change keysPushW k m po pl = some (bs.headD 0, m₁) at hW1
  cases k with
  | zero => simp [keysPushW] at hW1
  | succ k =>
  simp only [keysPushW] at hW1
  have hsz := hS.spn
  have hlen : (m.len64 SPN).toNat = (m.arr64 SPN).size := L.Front.toNat_ofNat_size _ (by omega)
  by_cases t1 : m.len64 SPN < spTop m
  · simp [t1] at hW1
  by_cases t2 : m.len64 SPN - spTop m < pl
  · simp [t1, t2] at hW1
  simp only [t1, t2, ↓reduceIte] at hW1
  have t1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t1)
  have t2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp t2)
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp t1), hlen] at t2'
  rw [hlen] at t1'
  cases hcp : ekCopyW k m po (spTop m) pl with
  | none => rw [hcp] at hW1; simp [kpK] at hW1
  | some mc =>
  rw [hcp, kpK_some] at hW1
  simp only [Option.some.injEq, Prod.mk.injEq] at hW1
  obtain ⟨hb, rfl⟩ := hW1
  have hnw : po.toNat + pl.toNat < 2 ^ 64 := by
    rcases hslice?_bound_fsz _ _ _ _ hlps with h0 | h0
    · have := po.toNat_lt; omega
    · have := hS.erec; omega
  obtain ⟨hsl, hfc, hbc⟩ := ekCopyW_slice lps k m mc po (spTop m) pl hlps (by omega) hsz hnw hcp
  have hctl := hS.ctl136
  have hfm : MemFrame [SPN] [136] m (mc.set64 CTL 136 (spTop m + pl)) :=
    (hfc.mono (by simp) (by simp)).trans ((MemFrame.setCtl _ _ _).mono (by simp) (by simp))
  have hS₁ : CoreS dn (mc.set64 CTL 136 (spTop m + pl)) a₀ vis fe M eb :=
    hS.frame_stk hfm (by simp) (by simp)
  have hspn₁ : (mc.set64 CTL 136 (spTop m + pl)).arr64 SPN = mc.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have htop₁ : (spTop (mc.set64 CTL 136 (spTop m + pl))).toNat = (spTop m).toNat + pl.toNat := by
    have hc' : (136 : Word).toNat < (mc.arr64 CTL).size := by rw [hfc.2.2.1 CTL]; simpa using hctl
    simp only [spTop]; rw [rdW_set64]; simp only [hc', and_self, ↓reduceIte]
    rw [UInt64.toNat_add]; simp only [spTop] at t1' t2' ⊢; omega
  -- the core
  rw [← hb] at hW
  cases h2 : callW p (k + 1) "inst_lp_core" [spTop m, pl, us, e] (mc.set64 CTL 136 (spTop m + pl)) with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨r2, m₂⟩ := q
  rw [h2, ilwLPK₂_some] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  obtain ⟨hok, ⟨M', hS₂, hK₂, hSt₂⟩, hres, hw⟩ := ilwCore_ok hp k hS₁ he hus (by rw [hspn₁]; exact hsl)
    (Nat.le_of_eq htop₁.symm) h2
  -- the stack top put back
  have hfb : MemFrame [] [136] m₂ (m₂.set64 CTL 136 (spTop m)) := MemFrame.setCtl _ _ _
  have hS₃ := hS₂.frame_stk hfb (by simp) (by simp)
  refine ⟨hok, ⟨M', hS₃, hK₂, ?_⟩, by rw [hres]; simp only [decH, hr], by unfold ResH; rw [← hr]; exact hw⟩
  have hc₂ : (136 : Word).toNat < (m₂.arr64 CTL).size := by simpa using hS₂.ctl136
  have hspn₃ : (m₂.set64 CTL 136 (spTop m)).arr64 SPN = m₂.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨?_, ?_, fun i hi => ?_, (BKept.of_frame hfm (by decide) (by decide)).trans
      (hSt₂.bstk.trans (BKept.of_frame hfb (by decide) (by decide))),
    (PoolGrew.of_frame hfm (by decide) (by decide)).trans
      (hSt₂.pool.trans (PoolGrew.of_frame hfb (by decide) (by decide)))⟩
  · simp only [spTop]; rw [rdW_set64]; simp only [hc₂, and_self, ↓reduceIte]
  · rw [hspn₃, hSt₂.size, hspn₁, hfc.2.2.1 SPN]
  · have hi' : i.toNat < (spTop m).toNat := UInt64.lt_iff_toNat_lt.mp hi
    simp only [spW]
    rw [hspn₃]
    have := hSt₂.below i (UInt64.lt_iff_toNat_lt.mpr (by rw [htop₁]; omega))
    simp only [spW] at this
    rw [this, hspn₁, hbc i hi']

end L.Arena
