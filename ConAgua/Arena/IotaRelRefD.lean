module

public import ConAgua.Arena.IotaRelRefL
public import ConAgua.Arena.IotaFrameIface
public import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Checker.Basis

@[expose] public section

/-!
# The ι reading rule, part 2: the driver (lane ronsync8)

`rule_reads`, `rules_read`, `rec_reads`, `recs_read` against the twin's `ruleReads`, `rulesRead`,
`recReads`, `recsRead`. They run at the index `feR` with the block's constants pushed, so the
invariant `RInv` carries the stage at `feR`, con-ron's `CheckOK` at the entry index, con-ron's
`IFEnvOK E feR` (the pushed environment `E`), the walk memos (`AbsOK`) and the record decoder's
names; `RInv.stageT` rebuilds `StageT` at `feR` for `iota_parts_at`.
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-! ## `TwinOK` at an index the environment invariant is known for -/

/-- `TwinOK.of_check` with the index's invariant `IFEnvOK E feR` given apart from `CheckOK`. -/
theorem twinOK_of_ienv {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe feR : IFEnv}
    {env E : ConLeche.Env} (hok : ConRon.Bridge.CheckOK false env fe a)
    (hi : ConRon.Bridge.IFEnvOK E feR a) (hm : TwinMem dn m a) :
    TwinOK dn m a feR := by
  have hwf := hok.state.wf
  obtain ⟨rk, hw⟩ := hwf
  have hLs : LsStoreWF a.store.lss := hw.lss
  have hL : LStoreWF a.store.ls := hLs.ls
  have hc := hok.caches
  have hp := hok.pins
  refine ⟨hc.readL, hc.readLs, hw.nsWF, hm.erec, hm.spn, hm.memos, hm.bstk, ?_⟩
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, hp.zeroLevel, ⟨_, hp.emptyLevels⟩, hc.readN,
    fun c ci hf => ?_, fun c tbl hf => ?_, fun u hu => denoteL_of_viewW hL hu,
    fun us hus => ?_, hm.dnN, fun c cv mI rP isK rules hf r hr lvls pins hfi u hu => ?_,
    fun c cv mI rP isK rules hf r hr lvls hfi u hu => ?_⟩
  · exact denoteL_of_viewW hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c ci hf
    obtain ⟨y, hy⟩ := denoteCI_cv hd
    exact denoteCV_lps hy
  · obtain ⟨-, pt, -, hpt, -⟩ := hi.tblHit c tbl hf
    obtain ⟨ks, hks⟩ := denoteProjTable_lps hpt
    exact ⟨ks, denoteNList_mapM hks⟩
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c _ hf
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases h2 : ConRon.Arena.Frontend.denoteRules a.store rules with
    | none => rw [h2] at hd; split at hd <;> simp_all
    | some ys => exact denoteRules_mem h2 r hr lvls pins hfi u hu
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c _ hf
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases h2 : ConRon.Arena.Frontend.denoteRules a.store rules with
    | none => rw [h2] at hd; split at hd <;> simp_all
    | some ys => exact denoteRules_memL h2 r hr lvls hfi u hu

/-! ## The invariant of the driver -/

/-- **The driver's invariant** at the pushed index `feR` (environment `E`), con-ron's `CheckOK` at
the entry index `fe` (environment `env`). -/
structure RInv (dn : NIdx → Option ConLeche.Name) (vis : Word) (feR : IFEnv) (env : ConLeche.Env)
    (fe : IFEnv) (E : ConLeche.Env) (m : Mem) (a : AState) : Prop where
  stage : StageR vis feR m a
  check : ConRon.Bridge.CheckOK false env fe a
  ienv : ConRon.Bridge.IFEnvOK E feR a
  abs : AbsOK m
  dnN : ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN a.store.ns k = some x

section inv
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {feR : IFEnv} {env : ConLeche.Env}
  {fe : IFEnv} {E : ConLeche.Env}

theorem RInv.stageT {m : Mem} {a : AState} (h : RInv dn vis feR env fe E m a) : StageT dn vis feR m a :=
  ⟨h.stage, twinOK_of_ienv h.check h.ienv
    ⟨h.abs.wk.2.1, h.abs.wk.2.2.1, h.abs.wk.2.2.2.1, h.abs.coreMemos, h.dnN⟩, h.abs.wk.2.2.2.2⟩

theorem RInv.step {m m' : Mem} {a a' : AState} (h : RInv dn vis feR env fe E m a)
    (hS : StageR vis feR m' a') (hA : AbsOK m') (hs : ConRon.Bridge.CoreStep env fe a a') :
    RInv dn vis feR env fe E m' a' :=
  ⟨hS, hs.ok, h.ienv.mono hs.ext, hA, fun k x e => hs.ext.lss.ls.ns k x (h.dnN k x e)⟩

end inv

/-! ## Words of a result list -/

theorem irHeadD (r : List Word) : r.headD 0 = r.getD 0 0 := by cases r <;> rfl

theorem irTailGetD (r : List Word) (k : Nat) : r.tail.getD k 0 = r.getD (k + 1) 0 := by
  cases r <;> simp

theorem decIPAt_lit {m : Mem} {r : List Word} {x : IIotaParts} (h : decIPAt 1 m r x) :
    decIPAt 0 m [r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.tail.tail.headD 0] x := by
  simp only [decIPAt, decRL] at h ⊢
  simp only [irHeadD, irTailGetD, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add]
  simpa using h

theorem decIRAt_lit {m : Mem} {w0 w1 w2 w3 w4 w5 w6 w7 : Word} {x : IotaRec}
    (h : decIRAt 1 m [w0, w1, w2, w3, w4, w5, w6, w7] x) : decIRAt 0 m [w1, w2, w3, w4, w5, w6, w7] x :=
  decIRAt_drop h

section rule
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {feR : IFEnv}
  {env : ConLeche.Env} {fe : IFEnv} {E : ConLeche.Env}

/-- **`rule_reads(vis, q, ok, IotaRec, mI, rP, i, r)` refines `ruleReads feR cv rr mI rP i rl`**,
under the driver's invariant. -/
@[refines ConRon.Arena.ruleReads]
theorem ruleReads_rel (P : IotaRelProg p) (PF : IotaFrameProg p)
    (hf : p.lookup "rule_reads" = some ruleReadsL) (hAk : AbsKeep p "iota_parts_rel") {n : Nat}
    {m m' : Mem} {a : AState} {q rok r1 r2 r3 r4 r5 r6 r7 mI rP i rw : Word} {r : List Word}
    {cv : IConstantVal} {cvP : ConLeche.ConstantVal} {rr : Option IotaRec} {rl : IRecRule}
    {rlP : ConLeche.RecRule}
    (hc : callW p n "rule_reads" [vis, q, rok, r1, r2, r3, r4, r5, r6, r7, mI, rP, i, rw] m = some (r, m'))
    (hI : RInv dn vis feR env fe E m a)
    (hcv : decCV (erecP m) q.toNat = some cv)
    (hrr : decOIR m [rok, r1, r2, r3, r4, r5, r6, r7] rr)
    (hrrP : ∀ r0, rr = some r0 →
      ∃ x, ConRon.Bridge.Inductives.iotaRecP cvP mI.toNat rP.toNat = some x ∧
        ConRon.Bridge.Inductives.RecRel a.store r0 x)
    (hrl : decRule (erecP m) rw.toNat = some rl) (hrlP : Frontend.denoteRule a.store rl = some rlP) :
    ∃ b a', (ruleReads feR cv rr mI.toNat rP.toNat i.toNat rl).run a = .ok (b, a') ∧
      RInv dn vis feR env fe E m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧
      ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ruleReads_specW p hf n _ vis q rok r1 r2 r3 r4 r5 r6 r7 mI rP i rw) hc
  rcases n with _ | n
  · rw [ruleReadsW.eq_1] at hW; cases hW
  have z0 : ∀ {mm : Mem} {b : Bool}, b = false → decW0B mm [0] b := fun h => by subst h; simp [decW0B]
  have hok := hI.check
  simp only [ruleReads]
  rcases rr with _ | rr
  · simp only [decOIR, List.headD_cons] at hrr
    rw [ruleReadsW.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrr] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨false, a, rfl, hI, IWGrow.refl _, z0 rfl, ConRon.Bridge.CoreStep.refl hok⟩
  obtain ⟨hrok, hrrd⟩ := hrr
  simp only [List.headD_cons] at hrok
  have hrok0 : rok ≠ 0 := by rw [hrok]; decide
  obtain ⟨xr, hxr, hrel⟩ := hrrP rr rfl
  -- `nIdx`
  have hnI : ∃ nI : Word, nI.toNat = mI.toNat - rP.toNat ∧
      ruleReadsW p (n + 1) m vis q rok r1 r2 r3 r4 r5 r6 r7 mI rP i rw =
        ruleReadsW.j1 p n vis q r1 r2 r3 r4 r5 r6 r7 mI rP i rw nI m := by
    by_cases hlt : mI < rP
    · refine ⟨0, ?_, ruleReadsW.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrok0 hlt⟩
      have := UInt64.lt_iff_toNat_lt.mp hlt; simp; omega
    · refine ⟨mI - rP, ?_, ruleReadsW.arm3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrok0 hlt⟩
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp hlt)]
  obtain ⟨nI, hnI, hj⟩ := hnI
  rw [hj, ruleReadsW.j1.arm1] at hW
  dsimp only
  -- the minor's parts off the recursor's type
  rcases c1 : callW p n "iota_parts_of_at" [r1, r2, r3, r4, r5, r6, r7, rP, nI, i, rw] m with
    _ | ⟨q1, m1⟩
  · rw [c1, ruleReadsW.k_iota_parts_of_at.none] at hW; cases hW
  obtain ⟨x1, a1, h1, ⟨hS1, hg1, hd1⟩, hA1⟩ := iotaPartsOfAt_rel PF n vis feR r1 r2 r3 r4 r5 r6 r7 rP
    nI i rw rr rl m m1 a q1 c1 ⟨hI.stage, hI.abs, decIRAt_lit hrrd, hrl⟩
  rw [hnI] at h1
  obtain ⟨k1, hpo⟩ := ConRon.Bridge.Inductives.iotaPartsOfAt_run (env := env) (fe := fe) hok hrel h1
  have hI1 := hI.step hS1 hA1 k1
  rw [StateT.run_bind, h1, except_ok_bind]
  rcases x1 with _ | p'
  · simp only [decOIP] at hd1
    rw [c1, ruleReadsW.k_iota_parts_of_at.arm1 _ _ _ _ _ _ _ _ _ hd1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨false, a1, rfl, hI1, hg1, z0 rfl, k1⟩
  obtain ⟨hq1, hp'd⟩ := hd1
  obtain ⟨p'P, -, hp'rel⟩ := hpo p' rfl
  rw [c1, ruleReadsW.k_iota_parts_of_at.arm2 _ _ _ _ _ _ _ _ _ (by rw [hq1]; decide)] at hW
  dsimp only
  -- the constructor, by the rule's name
  have hrl1 : decRule (erecP m1) rw.toNat = some rl := ArrExt.decRule hg1.ext hrl
  have hctw : rl.ctor = decI (erRd m1 rw) ∧ HW (erRd m1 rw) := by
    obtain ⟨e1, e2⟩ := hd?_rd (erRdOK m1) (q := rw) (f := 0) (by simpa using decRule_ctor hrl1)
    exact ⟨by simpa using e1, by simpa [HW] using e2⟩
  rcases c2 : callW p n "env_find" [erRd m1 rw, vis] m1 with _ | ⟨q2, m2⟩
  · rw [c2, ruleReadsW.k_env_find.none] at hW; cases hW
  obtain ⟨hm2, hq2⟩ := irEnvFind P c2
  subst m2; subst hq2
  have hE1 := hS1.check.env
  rw [hctw.1]
  by_cases hf0 : (findRes m1 vis (erRd m1 rw)).headD 0 = 0
  · rw [c2, ruleReadsW.k_env_find.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf0] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a1, ?_, hI1, hg1, z0 rfl, k1⟩
    rw [findRes_miss hE1 hctw.2 hf0]; rfl
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hE1 hctw.2 hf0
  rw [hfind, hci]
  have hcs := decCI_ctorR (erRdOK m1) hci
  by_cases hk4 : erRd m1 ((findRes m1 vis (erRd m1 rw)).tail.headD 0) ≠ 4
  · rw [c2, ruleReadsW.k_env_find.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf0 hk4] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    refine ⟨false, a1, ?_, hI1, hg1, z0 rfl, k1⟩
    have hnc := hcs.2 hk4
    cases ci with
    | ctorInfo cv' np nf fam => exact absurd rfl (hnc cv' np nf fam)
    | _ => rfl
  have hk4 : erRd m1 ((findRes m1 vis (erRd m1 rw)).tail.headD 0) = 4 := Classical.not_not.mp hk4
  rw [c2, ruleReadsW.k_env_find.arm3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf0 hk4] at hW
  obtain ⟨cvj, rfl, -⟩ := hcs.1 hk4
  dsimp only
  generalize hqj : (findRes m1 vis (erRd m1 rw)).tail.headD 0 = qj at hW hci
  have hcvj : decCV (erecP m1) (qj + CI.cv).toNat = some cvj := decCI_cv_rd (erRdOK m1) hci
  -- the twin's constructor denotes
  have hfP : feR.find? rl.ctor = some (.ctorInfo cvj (erRd m1 (qj + CI.ctorNparams)).toNat
      (erRd m1 (qj + CI.ctorNfields)).toNat (decI (erRd m1 (qj + CI.ctorInduct)))) := by
    rw [hctw.1, hfind, hqj, hci]
  obtain ⟨-, d, -, hd, -⟩ := hI1.ienv.hit _ _ hfP
  obtain ⟨cvjP, hcvjP⟩ := denoteCI_cv hd
  -- the parts through the constructor
  rcases c3 : callW p n "iota_parts_at" [qj + CI.cv, erRd m1 (qj + CI.ctorNparams), mI, rP, rw] m1 with
    _ | ⟨q3, m3⟩
  · rw [c3, ruleReadsW.k_iota_parts_at.none] at hW; cases hW
  obtain ⟨x3, a3, h3, ⟨hS3, hg3, hd3⟩, hA3⟩ := iotaPartsAt_rel PF n dn vis feR (qj + CI.cv)
    (erRd m1 (qj + CI.ctorNparams)) mI rP rw cvj rl m1 m3 a1 q3 c3
    ⟨hI1.stageT, hA1, k1.ok.state, hcvj, hrl1, ⟨_, hcvjP⟩, ⟨_, ConRon.Bridge.denoteRule_ext hrlP k1.ext⟩⟩
  obtain ⟨k3, hpa⟩ := ConRon.Bridge.Inductives.iotaPartsAt_run (env := env) (fe := fe) k1.ok hcvjP
    (ConRon.Bridge.denoteRule_ext hrlP k1.ext) h3
  have hI3 := hI1.step hS3 hA3 k3
  rw [StateT.run_bind, h3, except_ok_bind]
  rcases x3 with _ | ⟨pp, pd⟩
  · simp only [decOIPD] at hd3
    rw [c3, ruleReadsW.k_iota_parts_at.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨false, a3, rfl, hI3, hg1.trans hg3, z0 rfl, k1.trans k3⟩
  obtain ⟨hq3, hppd, hpdd, hpdb⟩ := hd3
  rw [c3, ruleReadsW.k_iota_parts_at.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hq3]; decide)] at hW
  dsimp only
  rcases c4 : callW p n "iota_parts_rel" [vis, erRd m1 (qj + CI.ctorNparams), q, rw,
      q1.tail.headD 0, q1.tail.tail.headD 0, q1.tail.tail.tail.headD 0, q1.tail.tail.tail.tail.headD 0,
      q1.tail.tail.tail.tail.tail.headD 0, q1.tail.tail.tail.tail.tail.tail.headD 0,
      q1.tail.tail.tail.tail.tail.tail.tail.headD 0, q3.tail.headD 0, q3.tail.tail.headD 0,
      q3.tail.tail.tail.headD 0, q3.tail.tail.tail.tail.headD 0, q3.tail.tail.tail.tail.tail.headD 0,
      q3.tail.tail.tail.tail.tail.tail.headD 0, q3.tail.tail.tail.tail.tail.tail.tail.headD 0,
      q3.tail.tail.tail.tail.tail.tail.tail.tail.headD 0,
      q3.tail.tail.tail.tail.tail.tail.tail.tail.tail.headD 0] m3 with _ | ⟨q4, m4⟩
  · rw [c4, ruleReadsW.k_iota_parts_rel.none] at hW; cases hW
  rw [c4, ruleReadsW.k_iota_parts_rel.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have hpd' : decHL m3 (q3.tail.tail.tail.tail.tail.tail.tail.tail.headD 0).toNat
      (q3.tail.tail.tail.tail.tail.tail.tail.tail.tail.headD 0).toNat = some pd := by
    simpa only [irHeadD, irTailGetD] using hpdd
  have hpdb' : (q3.tail.tail.tail.tail.tail.tail.tail.tail.headD 0).toNat +
      (q3.tail.tail.tail.tail.tail.tail.tail.tail.tail.headD 0).toNat ≤ iwTop m3 := by
    simpa only [irHeadD, irTailGetD] using hpdb
  have g13 := hg1.trans hg3
  obtain ⟨b4, a4, h4, hS4, hg4, hd4, k4⟩ := iotaPartsRel_rel P c4 hI3.stage hI3.check
    (decIPAt_grow hg3 (decIPAt_lit hp'd)) (decIPAt_lit hppd)
    (ArrExt.decCV g13.ext hcv) (ArrExt.decRule hg3.ext hrl1) hpd' hpdb'
  exact ⟨b4, a4, h4, hI3.step hS4 (hAk _ _ _ _ _ c4 hA3) k4, g13.trans hg4, hd4,
    k1.trans (k3.trans k4)⟩

/-- The `j`-th rule of a decoded rule run, at L's address `ro + Rule.size * j`. -/
theorem irRuleAt {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {ro rl j : Word}
    {rules : List IRecRule} (h : decRules R ro.toNat rl.toNat = some rules) (hj : j < rl) :
    ∃ x, decRule R (ro + Rule.size * j).toNat = some x ∧
      rules.drop j.toNat = x :: rules.drop (j + 1).toNat := by
  obtain ⟨hlen, hget⟩ := decRules_get h
  have hj' : j.toNat < rl.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have hx := hget j.toNat hj'
  rw [List.getElem?_eq_getElem (by omega)] at hx
  obtain ⟨w, hw⟩ : ∃ w, R (ro.toNat + Rule.size.toNat * j.toNat) = some w := by
    have := decRule_ctor hx
    try simp only [ctor_add] at this
    cases e : R (ro.toNat + Rule.size.toNat * j.toNat) with
    | none => simp [hd?, e] at this
    | some w => exact ⟨w, rfl⟩
  have hlt := hR.lt _ _ hw
  have e : (ro + Rule.size * j).toNat = ro.toNat + Rule.size.toNat * j.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    have : Rule.size.toNat * j.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt hlt]
  have hj1 : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := rl.toNat_lt; omega
  refine ⟨_, by rw [e]; exact hx, ?_⟩
  rw [hj1, List.drop_eq_getElem_cons (by omega)]

/-- **`rules_read`'s loop from rule `i`** refines `rulesRead` on the rules from `i` on. -/
theorem rulesRead_loop (P : IotaRelProg p) (PF : IotaFrameProg p)
    (hrr' : p.lookup "rule_reads" = some ruleReadsL) (hAk : AbsKeep p "iota_parts_rel")
    {q rok r1 r2 r3 r4 r5 r6 r7 mI rP ro rl : Word} {cv : IConstantVal} {cvP : ConLeche.ConstantVal}
    {rr : Option IotaRec} {rules : List IRecRule} :
    ∀ (k : Nat) (m m' : Mem) (a : AState) (i : Word) (r : List Word) (rulesP : List ConLeche.RecRule),
      rulesReadW.loop1 p k m vis q rok r1 r2 r3 r4 r5 r6 r7 mI rP ro rl i = some (r, m') →
      RInv dn vis feR env fe E m a → decCV (erecP m) q.toNat = some cv →
      decOIR m [rok, r1, r2, r3, r4, r5, r6, r7] rr →
      (∀ r0, rr = some r0 →
        ∃ x, ConRon.Bridge.Inductives.iotaRecP cvP mI.toNat rP.toNat = some x ∧
          ConRon.Bridge.Inductives.RecRel a.store r0 x) →
      decRules (erecP m) ro.toNat rl.toNat = some rules →
      Frontend.denoteRules a.store (rules.drop i.toNat) = some rulesP → i ≤ rl →
      ∃ b a', (rulesRead feR cv rr mI.toNat rP.toNat (rules.drop i.toNat) i.toNat).run a = .ok (b, a') ∧
        RInv dn vis feR env fe E m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧
        ConRon.Bridge.CoreStep env fe a a'
  | 0, m, m', a, i, r, _, hW, _, _, _, _, _, _, _ => by rw [rulesReadW.loop1.eq_1] at hW; cases hW
  | k + 1, m, m', a, i, r, rulesP, hW, hI, hcv, hrr, hrrP, hrs, hrsP, hi => by
    by_cases hc : i < rl
    · rw [rulesReadW.loop1.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc] at hW
      obtain ⟨x, hx, hdrop⟩ := irRuleAt (erRdOK m) hrs hc
      rw [hdrop] at hrsP ⊢
      simp only [Frontend.denoteRules] at hrsP
      obtain ⟨xP, hxP⟩ : ∃ xP, Frontend.denoteRule a.store x = some xP := by
        cases e : Frontend.denoteRule a.store x with
        | none => rw [e] at hrsP; simp at hrsP
        | some y => exact ⟨y, rfl⟩
      obtain ⟨restP, hrestP⟩ : ∃ restP, Frontend.denoteRules a.store (rules.drop (i + 1).toNat) = some restP := by
        cases e : Frontend.denoteRules a.store (rules.drop (i + 1).toNat) with
        | none => rw [hxP, e] at hrsP; simp at hrsP
        | some y => exact ⟨y, rfl⟩
      rcases c1 : callW p k "rule_reads" [vis, q, rok, r1, r2, r3, r4, r5, r6, r7, mI, rP, i,
          ro + Rule.size * i] m with _ | ⟨r1', m1⟩
      · rw [c1, rulesReadW.k_rule_reads.eq_1] at hW; cases hW
      obtain ⟨b1, a1, h1, hI1, hg1, hd1, k1⟩ := ruleReads_rel P PF hrr' hAk c1 hI hcv hrr hrrP hx hxP
      simp only [rulesRead]
      rw [StateT.run_bind, h1, except_ok_bind]
      by_cases hz : r1'.headD 0 = 0
      · rw [c1, rulesReadW.k_rule_reads.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hb1 : b1 = false := by have := hd1.1; rw [hz] at this; simpa using this.symm
        subst hb1
        exact ⟨false, a1, rfl, hI1, hg1, by simp [decW0B], k1⟩
      rw [c1, rulesReadW.k_rule_reads.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz] at hW
      have hb1 : b1 = true := by rw [← hd1.1]; exact bne_iff_ne.mpr hz
      subst hb1
      simp only [ite_true]
      have hi1 : i + 1 ≤ rl := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; have := UInt64.lt_iff_toNat_lt.mp hc
        simp; have := rl.toNat_lt; omega
      have hj1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := UInt64.lt_iff_toNat_lt.mp hc; have := rl.toNat_lt; omega
      obtain ⟨b2, a2, h2, hI2, hg2, hd2, k2⟩ := rulesRead_loop P PF hrr' hAk k m1 m' a1 (i + 1) r restP hW hI1
        (ArrExt.decCV hg1.ext hcv) (decOIR_grow hg1 hrr)
        (fun r0 e => by
          obtain ⟨x0, h0, h0'⟩ := hrrP r0 e
          exact ⟨x0, h0, h0'.mono k1.ext⟩)
        (ArrExt.decRules hg1.ext hrs) (ConRon.Bridge.denoteRules_ext k1.ext _ _ hrestP) hi1
      rw [hj1] at h2
      rw [hj1]
      exact ⟨b2, a2, h2, hI2, hg1.trans hg2, hd2, k1.trans k2⟩
    rw [rulesReadW.loop1.arm2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hi' : i = rl := UInt64.le_antisymm hi (UInt64.not_lt.mp hc)
    subst hi'
    rw [List.drop_eq_nil_of_le (by rw [decRules_length hrs]; exact Nat.le_refl _)]
    exact ⟨true, a, rfl, hI, IWGrow.refl _, by simp [decW0B], ConRon.Bridge.CoreStep.refl hI.check⟩

/-- **`rules_read(vis, q, ok, IotaRec, mI, rP, ro, rl)` refines `rulesRead … rules 0`**. -/
@[refines ConRon.Arena.rulesRead]
theorem rulesRead_rel (P : IotaRelProg p) (PF : IotaFrameProg p)
    (hf : p.lookup "rules_read" = some rulesReadL)
    (hrr' : p.lookup "rule_reads" = some ruleReadsL) (hAk : AbsKeep p "iota_parts_rel") {n : Nat}
    {m m' : Mem} {a : AState} {q rok r1 r2 r3 r4 r5 r6 r7 mI rP ro rl : Word} {r : List Word}
    {cv : IConstantVal} {cvP : ConLeche.ConstantVal} {rr : Option IotaRec} {rules : List IRecRule}
    {rulesP : List ConLeche.RecRule}
    (hc : callW p n "rules_read" [vis, q, rok, r1, r2, r3, r4, r5, r6, r7, mI, rP, ro, rl] m = some (r, m'))
    (hI : RInv dn vis feR env fe E m a) (hcv : decCV (erecP m) q.toNat = some cv)
    (hrr : decOIR m [rok, r1, r2, r3, r4, r5, r6, r7] rr)
    (hrrP : ∀ r0, rr = some r0 →
      ∃ x, ConRon.Bridge.Inductives.iotaRecP cvP mI.toNat rP.toNat = some x ∧
        ConRon.Bridge.Inductives.RecRel a.store r0 x)
    (hrs : decRules (erecP m) ro.toNat rl.toNat = some rules)
    (hrsP : Frontend.denoteRules a.store rules = some rulesP) :
    ∃ b a', (rulesRead feR cv rr mI.toNat rP.toNat rules 0).run a = .ok (b, a') ∧
      RInv dn vis feR env fe E m' a' ∧ IWGrow m m' ∧ decW0B m' r b ∧ ConRon.Bridge.CoreStep env fe a a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rulesRead_specW p hf n _ vis q rok r1 r2 r3 r4 r5 r6 r7 mI rP ro rl) hc
  rcases n with _ | n
  · rw [rulesReadW.eq_1] at hW; cases hW
  rw [rulesReadW.arm1] at hW
  simpa using rulesRead_loop P PF hrr' hAk (n + 1) m _ a 0 r rulesP hW hI hcv hrr hrrP hrs
    (by simpa using hrsP) UInt64.zero_le

end rule

end L.Ind
