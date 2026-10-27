import ConAgua.Arena.DeclNatSub
import ConAgua.Arena.RecGenSpec.ClassFeR

/-!
# Refinements of `IndInstall`, part 39 (lane `indproofs4`, helper `grc`): the pop, the elimination level, the large-eliminator contract

* `blockLargeElimAllowed_spec`: the stub contract for `block_large_elim_allowed` (`sorry`; under
  `StageR` the twin's read-back of the result sort is not available).
* `structElimLevel_stage`: `struct_elim_level(elim, large)` under the stage relation, its result a
  handle (`internParam_stage`/`internZero_stage`, the bound `consInternM_lt`).
* `genRecCheckPopAll_refines`: `gen_rec_check_pop_all(vis, prevs.off, prevs.len)` undoes the
  temporary pushes in reverse order (`envPopTemp_refines` per row; the frame of `env_pop_temp`
  from its call-closed program `popProg`, so the other tiers and the pool stay).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `block_large_elim_allowed`: a stub contract -/

/-! ## `struct_elim_level` under the stage relation -/

/-- The lookups of `struct_elim_level`. -/
structure SelProg (p : Prog) : Prop where
  pf1 : p.lookup "param_find" = some paramFind
  pp1 : p.lookup "param_push" = some paramPush
  ip : p.lookup "intern_param" = some internParam
  pf2 : p.lookup "zero_find" = some zeroFind
  pp2 : p.lookup "zero_push" = some zeroPush
  iz : p.lookup "intern_zero" = some internZero
  sel : p.lookup "struct_elim_level" = some structElimLevelL

/-- The model of `struct_elim_level(elim, large)` (body fuel `n`). -/
def selmW (p : Prog) (n : Nat) (m : Mem) (elim large : Word) : Option (List Word × Mem) :=
  if large ≠ 0 then
    match callW p n "intern_param" [elim] m with
    | none => none
    | some (r, m') => some ([r.headD 0], m')
  else
    match callW p n "intern_zero" [] m with
    | none => none
    | some (r, m') => some ([r.headD 0], m')

theorem selm_spec (p : Prog) (hp : p.lookup "struct_elim_level" = some structElimLevelL) (n : Nat)
    (s₀ : St) (elim large : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "struct_elim_level" [elim, large]
    ⦃fun r s' => LocEq s' s₀ ∧ selmW p n s₀.mem elim large = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structElimLevelL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "intern_param", callW_spec p n "intern_zero"] <;>
    finish (gen := 20) [selmW]

/-- **`struct_elim_level(elim, large)` refines `structElimLevel` under the stage relation**, its
result a handle. -/
theorem structElimLevel_stage {p : Prog} (P : SelProg p) (n : Nat) (s₀ : St) (a : AState)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (elim large : Word)
    (hS : StageR dn vis fe s₀.mem a) (he : elim.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_elim_level" [elim, large]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ a', (ConRon.Arena.structElimLevel (decI elim) (large != 0)).run a =
        .ok (decI (r.headD 0), a') ∧ StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      (r.headD 0).toNat < 2 ^ 32; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (selm_spec p P.sel n s₀ elim large) ?_
  rintro r s' ⟨hl, hm⟩
  refine ⟨hl, ?_⟩
  have hR := hS.1.arena.1
  unfold selmW at hm
  by_cases hlg : large ≠ 0
  · rw [ite_eq_left hlg] at hm
    rcases c : callW p n "intern_param" [elim] s₀.mem with _ | ⟨r1, m1⟩
    · rw [c] at hm; cases hm
    rw [c] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    obtain ⟨s1, hs1, -, hI⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (internParam_spec p P.pf1 P.pp1 P.ip n _ elim) c
    simp only at hs1 hI; rw [hs1] at hI
    obtain ⟨a', hrun, hS', hg⟩ := internParam_stage hS elim he hI
    have hI₂ := hI
    have hw := consInternM_lt paramCS_wf hR.param hI₂
    have hb : (large != 0) = true := by simpa using hlg
    refine ⟨a', ?_, hS', hg, by simpa using hw⟩
    simp only [List.headD_cons, ConRon.Arena.structElimLevel, hb, ite_true]
    exact hrun
  · rw [ite_eq_right hlg] at hm
    rcases c : callW p n "intern_zero" [] s₀.mem with _ | ⟨r1, m1⟩
    · rw [c] at hm; cases hm
    rw [c] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    obtain ⟨s1, hs1, -, hI⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (internZero_spec p P.pf2 P.pp2 P.iz n _) c
    simp only at hs1 hI; rw [hs1] at hI
    obtain ⟨a', hrun, hS', hg⟩ := internZero_stage hS hI
    have hI₂ := hI
    have hw := consInternM_lt zeroCS_wf hR.zero hI₂
    have hb : (large != 0) = false := by simpa using hlg
    refine ⟨a', ?_, hS', hg, by simpa using hw⟩
    simp only [List.headD_cons, ConRon.Arena.structElimLevel, hb]
    exact hrun

/-! ## The stage relation across an environment-index write -/

/-- **A run that writes only the environment's rows, `ECON` and `CTL[128]`**, relating its
memory to an environment `fe'` at view `vis'`, keeps the stage relation (at `fe'`) and the pool. -/
theorem StageR.of_envFrame {dn : NIdx → Option ConLeche.Name} {vis vis' : Word} {fe fe' : IFEnv}
    {a : AState} {m m' : Mem} (hS : StageR dn vis fe m a)
    (hfr : MemFrame [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1, ECON] [128] m m') (hE : EnvR dn m' vis' fe') :
    StageR dn vis' fe' m' a ∧ IWGrow m m' := by
  have hC : CheckR dn m' a vis' fe' :=
    ⟨⟨ArenaR.frame (fun b hb => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arenaArrs, storeArrs, memoArrs, EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1, ECON])
        (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hfr
        hS.1.arena.1,
      DerR.frameM _ _ m _ hfr (by decide) a hS.1.arena.2⟩,
     hS.1.core.frame (by decide) (fun x hx => by simp at hx; subst hx; decide) hfr,
     hS.1.pins.frame (by decide) hfr, hE, hS.1.mode.frame hfr (by decide) (by decide)⟩
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  have hI : m'.arr64 IW = m.arr64 IW := hfr.1 IW (by decide) (by decide)
  have hER : m'.arr64 EREC = m.arr64 EREC := hfr.1 EREC (by decide) (by decide)
  have h200 : iwTop m' = iwTop m := by simp only [iwTop, hfr.2.1 200 (by decide)]
  have h129 : erTop m' = erTop m := by simp only [erTop, hfr.2.1 129 (by decide)]
  refine ⟨⟨hC, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [h200, hI]; exact hI1
  · rw [h129, hER]; exact hE1
  · rw [hI]; exact hsz
  · rw [hER]; exact hEs
  · rw [hfr.2.2.1 CTL]; exact hc
  · exact ⟨by omega, by omega, fun i _ => by rw [hI], fun i _ => by rw [hER]⟩

/-! ## `env_pop_temp`'s write set -/

/-- `env_pop_temp` and its callees. -/
def popProg : Prog :=
  [("env_pop_temp", envPopTempL), ("env_row_set", envRowSetL), ("env_ix", envIxL)]

def popFns : List FnName := popProg.map (·.1)

theorem popProg_closed : closedA popProg [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1, ECON] [128] popFns = true := by
  decide +kernel

theorem popTemp_frame {p : Prog} (hx : p.lookup "env_ix" = some envIxL)
    (hs : p.lookup "env_row_set" = some envRowSetL) (hpt : p.lookup "env_pop_temp" = some envPopTempL)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n "env_pop_temp" vs m = some (r, m')) :
    MemFrame [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1, ECON] [128] m m' := by
  have hag : ∀ f ∈ popFns, p.lookup f = popProg.lookup f := by
    intro f hf
    simp only [popFns, popProg, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp only [hx, hs, hpt] <;> rfl
  rw [callW_agree popProg_closed hag n (by simp [popFns, popProg])] at h
  exact (run_memFrame popProg_closed (by simp [popFns, popProg]) (L.Arena.run_of_callW h)).1

/-! ## `gen_rec_check_pop_all` -/

/-- **`gen_rec_check_pop_all` is its model `papW`** (generated; its loop `papW.loop1`). -/
l_model pap_spec (p : Prog) (hp : p.lookup "gen_rec_check_pop_all" = some genRecCheckPopAll)
  fns [hp ↦ papW]
  specs [callW_spec p n "env_pop_temp"]
  grind [ind_grind] finish [rdW_eq] gen 40 instances 20000

theorem FA2.getElem {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, FA2 R as bs → ∀ (i : Nat) (h1 : i < as.length) (h2 : i < bs.length),
      R as[i] bs[i]
  | _, _, .nil, i, h1, _ => by simp at h1
  | _, _, .cons h hs, 0, _, _ => h
  | _, _, .cons _ hs, i + 1, h1, h2 => FA2.getElem hs i (by simpa using h1) (by simpa using h2)

theorem papW_ok {p : Prog} (hx : p.lookup "env_ix" = some envIxL)
    (hs : p.lookup "env_row_set" = some envRowSetL) (hpt : p.lookup "env_pop_temp" = some envPopTempL)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (a : AState) (po pl : Word)
    (prevs : List (NIdx × Option (Nat × IConstantInfo))) (k : Nat) :
    ∀ (m m' : Mem) (vis v' j : Word), papW.loop1 p k m vis po j = some (v', m') →
    StageR dn vis ((prevs.drop j.toNat).foldr (fun x acc => acc.popTemp x.1 x.2) fe) m a →
    j.toNat ≤ pl.toNat → SPL (decPrev dn) m po.toNat pl.toNat prevs →
    StageR dn v' (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) fe) m' a ∧ IWGrow m m' := by
  induction k with
  | zero => intro m m' vis v' j h; simp [papW.loop1.eq_1] at h
  | succ k ih =>
  intro m m' vis v' j h hS hj hsp
  by_cases h0 : ¬ 0 < j
  · rw [papW.loop1.arm2 (hc1 := h0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : j.toNat = 0 := by
      have : ¬ 0 < j.toNat := fun e => h0 (UInt64.lt_iff_toNat_lt.mpr (by simpa using e))
      omega
    rw [this, List.drop_zero] at hS
    exact ⟨hS, IWGrow.refl _⟩
  simp only [Decidable.not_not] at h0
  have hj0 : 0 < j.toNat := by simpa using UInt64.lt_iff_toNat_lt.mp h0
  obtain ⟨hb, ps, hps, hfa⟩ := hsp
  have hlen := decNL_length m hps
  have hplen : prevs.length = pl.toNat := by rw [← hfa.length_eq, hlen]
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz := hS.2.2.2.1
  obtain ⟨i, hi⟩ : ∃ i, i = j.toNat - 1 := ⟨_, rfl⟩
  have hil : i < ps.length := by omega
  have hj1 : (j - 1).toNat = i := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hpoi : (po + (j - 1)).toNat = po.toNat + i := by
    rw [UInt64.toNat_add, hj1]; simp; omega
  obtain ⟨-, hget⟩ := decNL_getW m pl.toNat po.toNat ps hps
  obtain ⟨w, hw, hwv⟩ := hget i hil
  have hrd1 : rdW (m.arr64 IW) (po + (j - 1)) = w := by
    simp only [rdW, hpoi]; simp only [iwA] at hw; rw [hw]; rfl
  have hst := FA2.getElem hfa i hil (by omega)
  have hdp : decPrev dn m ps[i] = some prevs[i] := hst.get
  simp only [decPrev, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdp
  obtain ⟨nm, hnm, c, hc, q, hq, pv, hpv, hxe⟩ := hdp
  simp only [iwH, hd?, bind, Option.bind_eq_some_iff] at hnm
  obtain ⟨wn, hwn, hnm⟩ := hnm
  split at hnm
  rotate_left
  · cases hnm
  rename_i hwn32
  simp only [Option.some.injEq] at hnm
  have hq0 : ps[i] < (m.arr64 IW).size := by
    have := (Array.getElem?_eq_some_iff.mp (by simpa [iwA] using hwn)).1; exact this
  have hq2 : ps[i] + 2 < (m.arr64 IW).size := by
    have := (Array.getElem?_eq_some_iff.mp (by simpa [iwA] using hq)).1; exact this
  have e0 : w.toNat = ps[i] := hwv
  have e1 : (w + 1).toNat = ps[i] + 1 := by rw [UInt64.toNat_add, e0]; simp; omega
  have e2 : (w + 2).toNat = ps[i] + 2 := by rw [UInt64.toNat_add, e0]; simp; omega
  have r0 : rdW (m.arr64 IW) w = wn := by simp only [rdW, e0]; simp only [iwA] at hwn; rw [hwn]; rfl
  have r1 : rdW (m.arr64 IW) (w + 1) = c := by simp only [rdW, e1]; simp only [iwA] at hc; rw [hc]; rfl
  have r2 : rdW (m.arr64 IW) (w + 2) = q := by simp only [rdW, e2]; simp only [iwA] at hq; rw [hq]; rfl
  rw [papW.loop1.arm1 (hc1 := h0), hrd1, r0, r1, r2] at h
  cases c1 : callW p k "env_pop_temp" [vis, wn, c, q] m with
  | none => rw [c1, papW.k_env_pop_temp.none] at h; cases h
  | some x =>
  obtain ⟨r1', m1⟩ := x
  rw [c1, papW.k_env_pop_temp.arm1] at h
  obtain ⟨s1, hs1, -, hE1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPopTemp_refines p hx hs hpt k _ vis wn c q pv hS.1.env (by simpa using hwn32) hpv) c1
  subst hs1
  have hfr := popTemp_frame hx hs hpt c1
  obtain ⟨hS1, hg1⟩ := StageR.of_envFrame hS hfr hE1
  have hdrop : ((prevs.drop j.toNat).foldr (fun x acc => acc.popTemp x.1 x.2) fe).popTemp (decI wn) pv =
      (prevs.drop (j - 1).toNat).foldr (fun x acc => acc.popTemp x.1 x.2) fe := by
    rw [hj1, List.drop_eq_getElem_cons (i := i) (show i < prevs.length by omega), ← hxe,
      show i + 1 = j.toNat by omega, hnm]
    rfl
  rw [hdrop] at hS1
  obtain ⟨hS', hg'⟩ := ih s1.mem m' (r1'.headD 0) v' (j - 1) h hS1 (by omega)
    (SPL.grow ⟨hb, ps, hps, hfa⟩ hg1)
  exact ⟨hS', hg1.trans hg'⟩

/-- **`gen_rec_check_pop_all(vis, prevs.off, prevs.len)` undoes the temporary pushes**, last first:
the stage relation at the returned view of `prevs.foldr popTemp fe`, the pool unchanged. -/
theorem genRecCheckPopAll_refines {p : Prog} (hx : p.lookup "env_ix" = some envIxL)
    (hs : p.lookup "env_row_set" = some envRowSetL) (hpt : p.lookup "env_pop_temp" = some envPopTempL)
    (hp : p.lookup "gen_rec_check_pop_all" = some genRecCheckPopAll) (n : Nat) (s₀ : St) (a : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (po pl : Word)
    (prevs : List (NIdx × Option (Nat × IConstantInfo))) (hS : StageR dn vis fe s₀.mem a)
    (hpv : SPL (decPrev dn) s₀.mem po.toNat pl.toNat prevs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_pop_all" [vis, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧
      StageR dn (r.headD 0) (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) fe) s'.mem a ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (pap_spec p hp (n + 1) s₀ vis po pl) ?_
  rintro r s' ⟨hl, hm⟩
  rw [papW.arm1] at hm
  obtain ⟨⟨v, m1⟩, h1, hm⟩ := of_K hm rfl
  rw [papW.k_loop1.arm1] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  have hlen := hpv.length
  have hd : (prevs.drop pl.toNat) = [] := List.drop_eq_nil_of_le (by omega)
  exact ⟨hl, papW_ok hx hs hpt dn fe a po pl prevs (n + 1) s₀.mem _ vis _ pl h1
    (by rw [hd]; exact hS) (Nat.le_refl _) hpv⟩

end L.Ind
