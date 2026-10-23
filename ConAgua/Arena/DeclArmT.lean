import ConAgua.Arena.DeclValT
import ConAgua.Arena.DeclArmLoop

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
open L.Front (DECL DLP DeclsR)

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
    (hD : DeclsR (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
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

/-- **`check_constant_val` under `StageT`**, at the call. -/
theorem checkConstantVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis q : Word) (cv : IConstantVal) (hS : StageT dn vis fe s₀.mem a₀)
    (hqd : decCV (erecP s₀.mem) q.toNat = some cv) (hqb : q.toNat + 3 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_constant_val" [vis, q]
    ⦃fun _r s' => LocEq s' s₀ ∧ AM.ok (checkConstantVal V fe cv) a₀ ∧
      StageT dn vis fe s'.mem (AM.st (checkConstantVal V fe cv) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (ccv_specW p hp (realCall p) (realCall_spec p) n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg⟩ := ccvW_okT hq hn hm hS hqd hqb
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg⟩

/-- **`check_thm_val` under `StageT`**, at the call: the stage relation at the extended
environment and the core's memos after it. -/
theorem checkThmVal_refinesT (p : Prog) (hp : ValProg p) (hq : KnotStageProg p) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis c : Word) (cv : IConstantVal) (v : EIdx) (hS : StageT dn vis fe s₀.mem a₀)
    (hc : decCI (erecP s₀.mem) dn c.toNat = some (.thmInfo cv))
    (hv : hd? (erecP s₀.mem) (c.toNat + 5) = some v) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_thm_val" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkThmVal V fe cv v) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkThmVal V fe cv v) a₀) s'.mem
        (AM.st (checkThmVal V fe cv v) a₀) ∧ CoreMemos s'.mem ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (tv_specW p hp (realCall p) (realCall_spec p) n s₀ vis c) ?_
  rintro r s' ⟨hl, hm⟩
  have hcv := decCI_cv hc (.inl rfl)
  obtain ⟨a', hrun, hS', hM', hg⟩ :=
    tvW_okT hq hp.rcp hq.knot.lvc hq.lvlEqC hn hm hS hc hcv hv
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hS', hM', hg⟩

/-- **The theorem arm under `StageT`** (`cdtW_ok`'s). -/
theorem cdtW_okT {p : Prog} (hV : ValProg p) (hq : KnotStageProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {i : Word} {r : List Word}
    {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal} {v : EIdx}
    (h : cdtW p n m i vis = some (r, m')) (hS : StageT dn vis fe m a)
    (hD : DeclsR (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .thmDecl cv v) :
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
  obtain ⟨s2, hs2, -, hok2, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (checkConstantVal_refinesT p hV hq n hn' ⟨m1, Locals.init []⟩ a dn fe vis (q + 1) cv hS1
      (by rw [hq1]; exact hcv1) (by omega)) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  cases h3 : callW p n "check_thm_val" [vis, q] s2.mem with
  | none => rw [h3] at h; cases h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, cdtK3_some] at h
  have hx2 : ArrExt (erecP m1) (erecP s2.mem) := IWGrow.erecPExt hg2
  obtain ⟨s3, hs3, -, hok3, hS3, hM3, hg3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (checkThmVal_refinesT p hV hq n hn' ⟨s2.mem, Locals.init []⟩ _ dn fe vis q cv v hS2
      (ArrExt.decCI hx2 hci1) (ArrExt.hd? hx2 hval1)) h3
  subst hs3
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hrun3 := AM.run_of_ok _ _ hok3
  refine ⟨_, _, ?_, by simpa using hS3, hM3, hg1.trans (hg2.trans hg3)⟩
  show (do checkConstantVal V fe cv; checkThmVal V fe cv v).run a = _
  simp only [StateT.run_bind, hrun2, exc_ok_bind']
  exact hrun3

end L.Arena
