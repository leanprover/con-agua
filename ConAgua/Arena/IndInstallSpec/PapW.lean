module

public import ConAgua.Arena.IndInstallSpec.SelProg
import ConAgua.Arena.DeclNatSub
public import ConAgua.Arena.RecGenSpec.ClassFeR
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.Env

@[expose] public section

/-!
# PapW

`selmW`, `selm_spec`, `structElimLevel_stage`, `papW_ok`, `genRecCheckPopAll_refines` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

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
    {vis : Word} {fe : IFEnv} (elim large : Word)
    (hS : StageR vis fe s₀.mem a) (he : elim.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_elim_level" [elim, large]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ a', (ConRon.Arena.structElimLevel (decI elim) (large != 0)).run a =
        .ok (decI (r.headD 0), a') ∧ StageR vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      (r.headD 0).toNat < 2 ^ 32; ⊤⦄ := by
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  refine triple_post (selm_spec p P.sel n s₀ elim large) ?_
  rintro r s' ⟨hl, hm⟩
  refine ⟨hl, ?_⟩
  have hR := hS.check.arena.base
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

/-- The prev value `env_pop_temp` puts back is the decoded displaced row. -/
theorem prevD_eq {m : Mem} {c q : Word} {pv : Option IConstantInfo} (h : prevD m c q = some pv) :
    (if c = 0 then none else decCI (erecP m) q.toNat) = pv ∧
      (c ≠ 0 → ∃ ci, decCI (erecP m) q.toNat = some ci) := by
  unfold prevD at h
  by_cases hc : c = 0
  · simp only [hc, ite_true, Option.some.injEq] at h ⊢; exact ⟨h, fun h => absurd rfl h⟩
  · simp only [hc, ite_false] at h ⊢
    obtain ⟨ci, hci, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hci, fun _ => ⟨ci, hci⟩⟩

/-- **The pop loop**: from the `j`-th displaced row down, each `env_pop_temp` undoes the newest push
(`PopOK` of the first `j` rows, newest first, gives `env_pop_temp`'s preconditions). -/
theorem papW_ok {p : Prog} (hs : p.lookup "env_row_set" = some envRowSetL)
    (hpt : p.lookup "env_pop_temp" = some envPopTempL)
    (fe : IFEnv) (a : AState) (po pl : Word)
    (prevs : List (NIdx × Option IConstantInfo)) (cs : List (NIdx × Word)) (k : Nat) :
    ∀ (m m' : Mem) (vis v' j : Word), papW.loop1 p k m vis po j = some (v', m') →
    StageR vis ((prevs.drop j.toNat).foldr (fun x acc => acc.popTemp x.1 x.2) fe) m a →
    j.toNat ≤ pl.toNat → SPL decPrev m po.toNat pl.toNat prevs → SPL decPrevC m po.toNat pl.toNat cs →
    PopOK (ownC m) vis (cs.take j.toNat).reverse →
    StageR v' (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) fe) m' a ∧ IWGrow m m' := by
  induction k with
  | zero => intro m m' vis v' j h; simp [papW.loop1.eq_1] at h
  | succ k ih =>
  intro m m' vis v' j h hS hj hsp hspC hPop
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
  obtain ⟨hb, ps, hps, hfa⟩ := id hsp
  obtain ⟨-, psC, hpsC, hfaC⟩ := id hspC
  have hpsE : psC = ps := by rw [hps] at hpsC; exact (Option.some.inj hpsC).symm
  subst hpsE
  have hlen := decNL_length m hps
  have hplen : prevs.length = pl.toNat := by rw [← hfa.length_eq, hlen]
  have hclen : cs.length = pl.toNat := by rw [← hfaC.length_eq, hlen]
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz := hS.iw.iwSize
  obtain ⟨i, hi⟩ : ∃ i, i = j.toNat - 1 := ⟨_, rfl⟩
  have hil : i < psC.length := by omega
  have hj1 : (j - 1).toNat = i := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hpoi : (po + (j - 1)).toNat = po.toNat + i := by
    rw [UInt64.toNat_add, hj1]; simp; omega
  obtain ⟨-, hget⟩ := decNL_getW m pl.toNat po.toNat psC hps
  obtain ⟨w, hw, hwv⟩ := hget i hil
  have hrd1 : rdW (m.arr64 IW) (po + (j - 1)) = w := by
    simp only [rdW, hpoi]; simp only [iwA, aread_apply, aread_apply] at hw; rw [hw]; rfl
  have hdp : decPrev m psC[i] = some prevs[i] := (FA2.getElem hfa i hil (by omega)).get
  have hdc : decPrevC m psC[i] = some cs[i] := (FA2.getElem hfaC i hil (by omega)).get
  simp only [decPrev, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdp
  obtain ⟨nm, hnm, c, hc, q, hq, pv, hpv, hxe⟩ := hdp
  simp only [decPrevC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, hnm, hc] at hdc
  obtain ⟨_, ⟨rfl⟩, _, ⟨rfl⟩, hxc⟩ := hdc
  simp only [iwH, hd?, bind, Option.bind_eq_some_iff] at hnm
  obtain ⟨wn, hwn, hnm⟩ := hnm
  split at hnm
  rotate_left
  · cases hnm
  rename_i hwn32
  simp only [Option.some.injEq] at hnm
  have e0 : w.toNat = psC[i] := hwv
  have e1 : (w + 1).toNat = psC[i] + 1 := by
    have := (Array.getElem?_eq_some_iff.mp (by simpa [iwA, aread_apply, aread_apply] using hc)).1
    rw [UInt64.toNat_add, e0]; simp; omega
  have e2 : (w + 2).toNat = psC[i] + 2 := by
    have := (Array.getElem?_eq_some_iff.mp (by simpa [iwA, aread_apply, aread_apply] using hq)).1
    rw [UInt64.toNat_add, e0]; simp; omega
  have r0 : rdW (m.arr64 IW) w = wn := by simp only [rdW, e0]; simp only [iwA, aread_apply, aread_apply] at hwn; rw [hwn]; rfl
  have r1 : rdW (m.arr64 IW) (w + 1) = c := by simp only [rdW, e1]; simp only [iwA, aread_apply, aread_apply] at hc; rw [hc]; rfl
  have r2 : rdW (m.arr64 IW) (w + 2) = q := by simp only [rdW, e2]; simp only [iwA, aread_apply, aread_apply] at hq; rw [hq]; rfl
  rw [papW.loop1.arm1 (hc1 := h0), hrd1, r0, r1, r2] at h
  -- the stack's top
  have hwnW : nm.word.toUInt64 = wn := by rw [← hnm]; exact decI_word_self wn hwn32
  rw [show j.toNat = i + 1 by omega, List.take_succ_eq_append_getElem (by omega), List.reverse_append,
    ← hxc] at hPop
  obtain ⟨htop, hv, hc32, hcv, hfree, hrest⟩ := hPop
  obtain ⟨hpvE, hcd⟩ := prevD_eq hpv
  cases c1 : callW p k "env_pop_temp" [vis, wn, c, q] m with
  | none => rw [c1, papW.k_env_pop_temp.none] at h; cases h
  | some x =>
  obtain ⟨r1', m1⟩ := x
  rw [c1, papW.k_env_pop_temp.arm1] at h
  have hE := hS.check.env
  obtain ⟨s1, hs1, -, hr1, hE1, hm1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPopTemp_refines p hs hpt k _ vis wn c q hE (by simpa using hwn32) hv
      (by rw [← hwnW]; exact htop) hc32 hcv hcd
      (fun hc0 n hn => hfree hc0 n fun e => hn (by rw [e, hwnW]))) c1
  obtain ⟨s1', hs1', hm1', -, -, ht, hbd⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPopTemp_spec p hs hpt k _ vis wn c q) c1
  rw [hm1, hpvE] at hE1
  have hmm : m1 = ownSet m wn c q := by rw [← hs1, hm1]
  subst hmm
  simp only at ht hbd
  obtain ⟨hS1, hg1⟩ := StageR.of_own hS hE1
  have hO1 : ownC (ownSet m wn c q) = updC (ownC m) nm c := by
    funext n'
    simp only [ownC, updC]
    split
    · rename_i e; subst e; rw [hwnW]; exact (ownRaw_ownSet_self ht hbd hc32 hE.stamp).1
    · rename_i hne
      rw [ownRaw_ownSet_other (by simpa using hwn32) (L.Arena.nidx_word_lt32 n') ht
        fun e => hne (nidx_word_inj (by rw [e, hwnW]))]
  have hdrop : ((prevs.drop j.toNat).foldr (fun x acc => acc.popTemp x.1 x.2) fe).popTemp (decI wn) pv =
      (prevs.drop (j - 1).toNat).foldr (fun x acc => acc.popTemp x.1 x.2) fe := by
    rw [hj1, List.drop_eq_getElem_cons (i := i) (show i < prevs.length by omega), ← hxe,
      show i + 1 = j.toNat by omega, hnm]
    rfl
  rw [hdrop] at hS1
  simp only [hr1, List.headD_cons] at h
  obtain ⟨hS', hg'⟩ := ih _ m' (vis - 1) v' (j - 1) h hS1 (by omega) (hsp.grow hg1) (hspC.grow hg1)
    (by rw [hO1, hj1]; exact hrest)
  exact ⟨hS', hg1.trans hg'⟩

/-- **`gen_rec_check_pop_all(vis, prevs.off, prevs.len)` undoes the temporary pushes**, last first:
the stage relation at the returned view of `prevs.foldr popTemp fe`, the pool unchanged, given
the displaced rows' names and counters `cs` pop as a stack (`PopOK`, `classFeR_refines`' post). -/
theorem genRecCheckPopAll_refines {p : Prog} (hs : p.lookup "env_row_set" = some envRowSetL)
    (hpt : p.lookup "env_pop_temp" = some envPopTempL)
    (hp : p.lookup "gen_rec_check_pop_all" = some genRecCheckPopAll) (n : Nat) (s₀ : St) (a : AState)
    (vis : Word) (fe : IFEnv) (po pl : Word)
    (prevs : List (NIdx × Option IConstantInfo)) (cs : List (NIdx × Word)) (hS : StageR vis fe s₀.mem a)
    (hpv : SPL decPrev s₀.mem po.toNat pl.toNat prevs) (hcs : SPL decPrevC s₀.mem po.toNat pl.toNat cs)
    (hpop : PopOK (ownC s₀.mem) vis cs.reverse) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_pop_all" [vis, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧
      StageR (r.headD 0) (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) fe) s'.mem a ∧
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
  have hclen := hcs.length
  have hd : (prevs.drop pl.toNat) = [] := List.drop_eq_nil_of_le (by omega)
  exact ⟨hl, papW_ok hs hpt fe a po pl prevs cs (n + 1) s₀.mem _ vis _ pl h1
    (by rw [hd]; exact hS) (Nat.le_refl _) hpv hcs (by rw [List.take_of_length_le (by omega)]; exact hpop)⟩

end L.Ind
