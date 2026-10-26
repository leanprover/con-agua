import ConAgua.Arena.DeclValT
import ConAgua.Arena.DeclArmLoop
import ConAgua.Arena.DeclStepGo

/-!
# The declaration arms under `StageT` (lane `loopt2`)

`DeclArm*.lean`'s arms run from the stage relation, the core's entry points read through their
stubs. Here they run from `StageT`, reading the program's own calls (`realCall p`), through the
`StageT` versions of the value checks (`DeclValT.lean`). An arm's post is the stage relation at its
environment and the core's memos well formed (`CoreMemos`): after an arm no core call follows in
the step, and the loop re-derives the twin's invariants at the next declaration.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.deprecated false

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- **`erec_ci` writes the record pool and its top** (`EREC`, `CTL[129]`). -/
theorem erecCiW_frame {n : Nat} {m m' : Mem} {i k : Word} {r : List Word}
    (h : erecCiW n m i k = some (r, m')) : MemFrame [EREC] [129] m m' := by
  cases n with
  | zero => simp [erecCiW] at h
  | succ n =>
  rw [erecCiW_step] at h
  cases h1 : L.Ind.erAllocW m (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => rw [h1] at h; cases h
  | some q1 =>
  obtain ⟨s, m1⟩ := q1
  rw [h1, eciK1_some] at h
  cases h2 : dlpCopyW n m1 s (1 + rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)) with
  | none => rw [h2] at h; cases h
  | some m2 =>
  rw [h2, eciK2_some] at h
  cases h3 : L.Ind.erAllocW m2 8 with
  | none => rw [h3] at h; cases h
  | some q3 =>
  obtain ⟨p, m3⟩ := q3
  rw [h3, eciK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have fA : ∀ {x y : Mem} {k : Word} {o : Word}, L.Ind.erAllocW x k = some (o, y) →
      MemFrame [EREC] [129] x y := by
    intro x y k o hx
    rw [erAllocW_mem hx]
    exact (MemFrame.setCtl x 129 _).mono (by simp) (by simp)
  have f2 : MemFrame [EREC] [129] m1 m2 := by
    rw [dlpCopyW_eq n m1 m2 _ _ _ h2]; exact (wrER_frame _ _ _).mono (by simp) (by simp)
  have f4 : MemFrame [EREC] [129] m3 (eciMem m3 p i k s (rdW (m.arr64 DECL) (4 + 8 * i))) := by
    rw [eciMem_eq]; exact (wrER_frame _ _ _).mono (by simp) (by simp)
  exact (((fA h1).trans f2).trans (fA h3)).trans f4

/-- `StageT` across `erec_ci` (an `EREC` writer: `TwinOK.frame`). -/
theorem erecCiW_okT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word} {ds : Array IDeclaration}
    {ci : IConstantInfo}
    (h : erecCiW n m i ck = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hci : stepCI ck.toNat ds[i.toNat] = some ci) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧ decCI (erecP m') dn (r.headD 0).toNat = some ci ∧
      decCV (erecP m') ((r.headD 0).toNat + 1) = some (stepCV ds[i.toNat]) ∧
      hd? (erecP m') ((r.headD 0).toNat + 5) = some (stepVal ds[i.toNat]) ∧
      (r.headD 0).toNat + 8 ≤ erTop m' := by
  obtain ⟨hS', hg, h1, h2, h3, h4⟩ := erecCiW_ok h hS.stage hD hi hci
  have hf := erecCiW_frame h
  refine ⟨⟨hS', hS.twin.frame hf ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
    by simp only [pinW, hf.1 PINS (by decide) (by decide)]; exact hS.flag⟩, hg, h1, h2, h3, h4⟩

/-- `lvl_eq_c` at its text (`FireProg.lvlText`). -/
theorem _root_.L.Ind.KnotStageProg.lvlEqC {p : Prog} (hq : KnotStageProg p) :
    p.lookup "lvl_eq_c" = some lvlEqCL :=
  (hq.knot.fire.lvlText _ (by decide)).trans rfl

/-- **`check_constant_val` refines `checkConstantVal .verified`** under `StageT`, at the call (the
census link since lane `indstaget`). -/
@[refines ConRon.Arena.checkConstantVal]
theorem checkConstantVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis q : Word) (cv : IConstantVal) (hS : StageT dn vis fe s₀.mem a₀)
    (hqd : decCV (erecP s₀.mem) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks) (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_constant_val" [vis, q]
    ⦃fun _r s' => LocEq s' s₀ ∧ AM.ok (checkConstantVal V fe cv) a₀ ∧
      StageT dn vis fe s'.mem (AM.st (checkConstantVal V fe cv) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      L.Stubs.CrOK s'.mem; ⊤⦄ := by
  refine triple_post (ccv_specW p hp (realCall p) (realCall_spec p) n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg, hCr'⟩ := ccvW_okT hq hap hkp hn hm hS hqd hqb hlps hCr
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, hCr'⟩

/-- **`check_constant_val` keeps the walk memos** (`AbsOK`), under `checkConstantVal_refinesT`'s
preconditions (lane `indstaget`: replaces the `AbsKeep` premise of the inductive stage). -/
theorem checkConstantVal_absOK (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {r : List Word} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis q : Word} {cv : IConstantVal}
    (hS : StageT dn vis fe m a₀) (hqd : decCV (erecP m) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks) (hCr : L.Stubs.CrOK m)
    (h : callW p n "check_constant_val" [vis, q] m = some (r, m')) (hA : AbsOK m) : AbsOK m' := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ccv_specW p hp (realCall p) (realCall_spec p) n _ vis q) h
  exact ccvW_okTA hq hap hkp hn hm hS hqd hqb hlps hCr hA
/-- **`check_thm_val` refines `checkThmVal .verified`** under `StageT`, at the call: the stage
relation at the extended environment and the core's memos after it (the census link since lane
`indstaget`). -/
@[refines ConRon.Arena.checkThmVal]
theorem checkThmVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.thmInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a₀ ∧
      Frontend.denoteCV a₀.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_thm_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkThmVal V fe cv v) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkThmVal V fe cv v) a₀) s'.mem
        (AM.st (checkThmVal V fe cv v) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (tv_specW p hp (realCall p) (realCall_spec p) n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  have hcv := decCI_cvTA hc (.inl rfl)
  obtain ⟨a', hrun, hS', hM', hg⟩ :=
    tvW_okT hq hp.rcp hq.knot.lvc hq.lvlEqC hap hkp hn hm hS hc hcv hv hpre hCr
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hM', hg⟩

/-- **`check_defn_val` refines `checkDefnVal .verified`** under `StageT`, at the arm's record
(lane `indstaget`; `dvW_okT`). -/
@[refines ConRon.Arena.checkDefnVal]
theorem checkDefnVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hh : ConLeche.ReducibilityHint)
    (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.defnInfo cv v hh))
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_defn_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDefnVal V fe cv v hh) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkDefnVal V fe cv v hh) a₀) s'.mem
        (AM.st (checkDefnVal V fe cv v hh) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (dv_specW p hp (realCall p) (realCall_spec p) n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hcv, hv⟩ := decls_decCI_defn hc
  obtain ⟨a', hrun, hS', hM', hg⟩ :=
    dvW_okT hq hp.rcp hap hkp hn "type mismatch in definition" hm hS hc hcv hv hlps hCr
  rw [← checkDefnVal_dvT] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hM', hg⟩

/-- **`check_opaque_val` refines `checkOpaqueVal .verified`** under `StageT`, at the arm's record
(lane `indstaget`; `dvW_okT`). -/
@[refines ConRon.Arena.checkOpaqueVal]
theorem checkOpaqueVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.axiomInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v)
    (hlps : ∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks)
    (hCr : L.Stubs.CrOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_opaque_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkOpaqueVal V fe cv v) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkOpaqueVal V fe cv v) a₀) s'.mem
        (AM.st (checkOpaqueVal V fe cv v) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (ov_specW p hp (realCall p) (realCall_spec p) n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  have hcv := decCI_cvTA hc (.inr rfl)
  obtain ⟨a', hrun, hS', hM', hg⟩ :=
    dvW_okT hq hp.rcp hap hkp hn "type mismatch in opaque" hm hS hc hcv hv hlps hCr
  rw [← checkOpaqueVal_dvT] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hM', hg⟩

/-- **The theorem arm under `StageT`** (`cdtW_ok`'s). -/
theorem cdtW_okT {p : Prog} (hV : ValProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {env : ConLeche.Env} {c : ConLeche.ConstantVal}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {i : Word} {r : List Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal} {v : EIdx}
    (h : cdtW p n m i vis = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .thmDecl cv v) (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hCr : L.Stubs.CrOK m) :
    ∃ fe' a', (checkDecl V pins fe (.thmDecl cv v)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' := by
  cases n with
  | zero => simp [cdtW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [cdtW_step] at h
  cases h1 : erecCiW n m i 2 with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdtK1_some] at h
  have hCr1 := CrOK.frame hCr (erecCiW_frame h1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .thmInfo cv) h1 hS hD hi (by rw [hd]; rfl)
  rw [hd] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at h hci1 hcv1 hval1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.2.2.1; have := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  cases h2 : callW p n "check_constant_val" [vis, q + 1] m1 with
  | none => rw [h2] at h; cases h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cdtK2_some] at h
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (checkConstantVal_refinesT p hV hq hap hkp n hn' ⟨m1, Locals.init []⟩ a dn fe vis (q + 1) cv hS1
      (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcvd) hCr1) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  -- the twin's constant check: `FoldOK` and the constant's denotation after it
  obtain ⟨hstep1, _F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (ConRon.Bridge.CoreSpec.of_core rfl) hfold hcvd hrun2
  have hok1 := hfold.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hwsT : ConLeche.Expr.WScoped 0 c.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkConstantVal_typeWF hpure1).fvar
  cases h3 : callW p n "check_thm_val" [vis, q] s2.mem with
  | none => rw [h3] at h; cases h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, cdtK3_some] at h
  have hx2 : ArrExt (erecP m1) (erecP s2.mem) := IWGrow.erecPExt hg2
  obtain ⟨s3, hs3, -, hok3, hS3, hM3, hg3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (checkThmVal_refinesT p hV hq hap hkp n hn' ⟨s2.mem, Locals.init []⟩ _ dn fe vis q cv v hS2
      (ArrExt.decCI hx2 hci1) (ArrExt.hd? hx2 hval1)
      ⟨env, c, hok1.envWF, hok1.check, hcA, hwsT⟩ hCr2) h3
  subst hs3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hrun3 := AM.run_of_ok _ _ hok3
  refine ⟨_, _, ?_, by simpa using hS3, hM3, hg1.trans (hg2.trans hg3)⟩
  show (do checkConstantVal V fe cv; checkThmVal V fe cv v).run a = _
  simp only [StateT.run_bind, hrun2, exc_ok_bind']
  exact hrun3

/-- **`erec_vg` writes the record pool and its top.** -/
theorem erecVgW_frame {m m' : Mem} {q vk : Word} {r : List Word} (h : erecVgW m q vk = some (r, m')) :
    MemFrame [EREC] [129] m m' := by
  unfold erecVgW at h
  split at h
  · cases h
  rename_i g m1 h1
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have f1 : MemFrame [EREC] [129] m m1 := by
    rw [erAllocW_mem h1]; exact (MemFrame.setCtl m 129 _).mono (by simp) (by simp)
  have fs : ∀ (x : Mem) (j : Word), MemFrame [EREC] [129] x (vgSet x g q j) := fun x j =>
    (MemFrame.set64 x EREC (by decide) _ _).mono (by simp) (by simp)
  have f0 : MemFrame [EREC] [129] m1 (m1.set64 EREC g vk) :=
    (MemFrame.set64 m1 EREC (by decide) g vk).mono (by simp) (by simp)
  exact (((((f1.trans f0).trans (fs _ 1)).trans (fs _ 2)).trans (fs _ 3)).trans (fs _ 4)).trans
    (fs _ 5)

/-- **`install_value` under `StageT`** (`ivW_gen`'s): the header and the value's guards under
`StageT`; after the push the stage relation at the extended environment and `CoreMemos`. -/
theorem ivW_genT {p : Prog} (hRp : RecProg p) (hI : IhProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {i ck vk : Word} {r : List Word}
    {ds : Array IDeclaration} {ci : IConstantInfo} {k : ValueKind} {env : ConLeche.Env}
    {c : ConLeche.ConstantVal}
    (h : ivW p n m i vis ck vk = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hci : stepCI ck.toNat ds[i.toNat] = some ci) (hk : decVK vk.toNat = some k)
    (hfold : ConRon.Bridge.FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store (stepCV ds[i.toNat]) = some c) (hCr : L.Stubs.CrOK m) :
    ∃ a2 a3, (installHeader fe (stepCV ds[i.toNat])).run a = .ok ((), a2) ∧
      (vk ≠ 1 → (installValueGuards fe (stepCV ds[i.toNat]) (stepVal ds[i.toNat])).run a2 =
        .ok ((), a3)) ∧ (vk = 1 → a3 = a2) ∧
      StageR dn (r.headD 0) (fe.push ci) m' a3 ∧ CoreMemos m' ∧ IWGrow m m' ∧
      decVG (erecP m') (r.tail.headD 0).toNat = some ⟨k, stepCV ds[i.toNat], stepVal ds[i.toNat]⟩ := by
  cases n with
  | zero => simp [ivW] at h
  | succ n =>
  rw [ivW_step] at h
  cases h1 : erecCiW n m i ck with
  | none => rw [h1] at h; simp [ivK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ivK1_some] at h
  have hCr1 := CrOK.frame hCr (erecCiW_frame h1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ := erecCiW_okT h1 hS hD hi hci
  generalize hq : r1.headD 0 = q at h hci1 hcv1 hval1 htop1
  have hb : q.toNat + 8 < 2 ^ 64 := by
    have h1 := hS1.stage.2.2.1; have h2 := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  cases h2 : callW p n "install_header" [vis, q + 1] m1 with
  | none => rw [h2] at h; simp [ivK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, ivK2_some] at h
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (ih_specW p hI (realCall p) (realCall_spec p) n ⟨m1, Locals.init []⟩ vis (q + 1)) h2
  rw [hs2] at hW2
  obtain ⟨a2, hrun2, hS2, hg2, -, -⟩ :=
    ihW_okT hap hkp.crf hW2 hS1 (by rw [hq1]; exact hcv1) (by rw [hq1]; omega) (denoteCV_lps hcvd) hCr1
  -- the parameters' names read back after the header: con-ron's `installHeader_bridge`
  have hlps2 : ∃ ks, (stepCV ds[i.toNat]).levelParams.mapM (denoteN a2.store.ns) = some ks := by
    obtain ⟨hstep, -⟩ := ConRon.Bridge.installHeader_bridge hfold hcvd hrun2
    exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hstep.ext)
  have tail : ∀ (m3 : Mem) (a3 : AState), StageT dn vis fe m3 a3 → IWGrow m1 m3 →
      ivK4 p vis vk q (callW p n "env_push" [vis, q] m3) = some (r, m') →
      StageR dn (r.headD 0) (fe.push ci) m' a3 ∧ CoreMemos m' ∧ IWGrow m1 m' ∧
      decVG (erecP m') (r.tail.headD 0).toNat = some ⟨k, stepCV ds[i.toNat], stepVal ds[i.toNat]⟩ := by
    intro m3 a3 hS3 hg3 h
    have hx3 : ArrExt (erecP m1) (erecP m3) := IWGrow.erecPExt hg3
    have hci3 := ArrExt.decCI hx3 hci1
    obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci3
    have hw : (rdW (m3.arr64 EREC) (q + 1)).toNat < 2 ^ 32 := by
      rw [rdW_of_get? hq1.symm (erecP_get hw1)]; exact hwl
    cases h4 : callW p n "env_push" [vis, q] m3 with
    | none => rw [h4] at h; simp [ivK4] at h
    | some rm4 =>
    obtain ⟨r4, m4⟩ := rm4
    rw [h4, ivK4_some] at h
    obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (envPush_specW p hRp n ⟨m3, Locals.init []⟩ vis q hw) h4
    subst hs4
    obtain ⟨hS4, hg4⟩ := envPushW_ok hW4 hS3.stage hci3
    have hM4 : CoreMemos s4.mem := hS3.twin.memos.frame (envPushW_frame hW4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    cases h5 : erecVgW s4.mem q vk with
    | none => rw [h5] at h; simp [ivK5] at h
    | some rm5 =>
    obtain ⟨r5, m5⟩ := rm5
    rw [h5, ivK5_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hx4 : ArrExt (erecP m1) (erecP s4.mem) := IWGrow.erecPExt (hg3.trans hg4)
    have htop4 : q.toNat + 8 ≤ erTop s4.mem := by
      have := (hg3.trans hg4).2.1; omega
    obtain ⟨hS5, hg5, hvg⟩ := erecVgW_ok h5 hS4 (ArrExt.decCV hx4 hcv1) (ArrExt.hd? hx4 hval1)
      htop4 hk
    have hM5 : CoreMemos m5 := hM4.frame (erecVgW_frame h5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨by simpa using hS5, hM5, hg3.trans (hg4.trans hg5), by simpa using hvg⟩
  by_cases hv1 : vk ≠ 1
  · rw [if_pos hv1] at h
    have hval2 : hd? (erecP m2) (q.toNat + 5) = some (stepVal ds[i.toNat]) :=
      ArrExt.hd? (IWGrow.erecPExt hg2) hval1
    obtain ⟨wv, hwv, hwvl, hwvd⟩ := hd?_some hval2
    have hq5 : (q + 5).toNat = q.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
    have ev : rdW (m2.arr64 EREC) (q + 5) = wv := rdW_of_get? hq5.symm (erecP_get hwv)
    rw [ev] at h
    cases h3 : ivgW (realCall p) n m2 vis (q + 1) wv with
    | none => rw [h3] at h; simp [ivK3] at h
    | some rm3 =>
    obtain ⟨r3, m3⟩ := rm3
    rw [h3, ivK3_some] at h
    have hcv2 : decCV (erA m2) (q + 1).toNat = some (stepCV ds[i.toNat]) := by
      rw [hq1]; exact ArrExt.decCV (IWGrow.erecExt (hg2)) hcv1
    obtain ⟨a3, hrun3, hS3, hg3, -⟩ := ivgW_okT hap hkp h3 hS2 hcv2 (by rw [hq1]; omega) hwvl hlps2 hCr2
    obtain ⟨hS', hM', hg', hvg'⟩ := tail m3 a3 hS3 (hg2.trans hg3) h
    refine ⟨a2, a3, hrun2, fun _ => by rw [hwvd]; exact hrun3, fun h' => absurd h' hv1, hS', hM',
      hg1.trans hg', hvg'⟩
  · rw [if_neg hv1] at h
    obtain ⟨hS', hM', hg', hvg'⟩ := tail m2 a2 hS2 hg2 h
    exact ⟨a2, a2, hrun2, fun h' => absurd h' hv1, fun _ => rfl, hS', hM', hg1.trans hg', hvg'⟩

end L.Arena
