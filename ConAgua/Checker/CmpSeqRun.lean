module

public import ConAgua.Checker.ParDriverL
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CmpSeqEntry
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Checker.CmpSeqCheck
public import ConAgua.Checker.PhaseBReads

@[expose] public section

/-!
# Modes `8` and `9` as runs of `check` in place (lane compare2, the sJ variant)

The sequential compared run's entry 2 runs `check` in place on the driver region with the mode
word `8` (the solution's jobs: `check_bs`) and then `9` (the challenge's: `check_bc`). The region
differs from the frozen memory in `OUT`, `HDRF`, `CTLF` and the byte arrays, which the two modes'
call closures never read (`CqSeqProg.reads`), so each run is the run on the frozen memory with
the region's globals (`L.invoke_agree_ok`): `cq_check8`, `cq_check9` give the switch's facts and the
jobs' `check_jobs` call on the frozen side.

`CqSeqProg p`: what the two modes need of the program (the lookups, the callees' triples with
their error classes, the read set); proved at the checker's program once it holds the modes'
functions.
-/

namespace L.Checker

open L L.Arena L.Front
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true

/-- **What modes `8` and `9` need of the program.** -/
structure CqSeqProg (p : Prog) : Prop where
  check : p.lookup "check" = some checkL
  bs : p.lookup "check_bs" = some checkBSL
  bc : p.lookup "check_bc" = some checkBCL
  bankS : ∀ n (s₀ : St), ⦃fun s => s = s₀⦄ invoke p (exec p n) "cq_bank_s" []
    ⦃fun _ s' => LocEq s' s₀ ∧ CqRowsSOK s₀.mem ∧ CqTailSOK (cqRowsS s₀.mem) ∧ s'.mem = cqBankSM s₀.mem;
     fun e => e.cls = 0⦄
  ctlS : ∀ n (s₀ : St), ⦃fun s => s = s₀⦄ invoke p (exec p n) "cq_ctl_s" []
    ⦃fun _ s' => LocEq s' s₀ ∧ CqCtlSOK s₀.mem ∧ s'.mem = cqCtlSM s₀.mem; fun e => e.cls = 0⦄
  bankC : ∀ n (s₀ : St), ⦃fun s => s = s₀⦄ invoke p (exec p n) "cq_bank_c" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = cqBankCM s₀.mem; fun e => e.cls = 0⦄
  ctlC : ∀ n (s₀ : St), ⦃fun s => s = s₀⦄ invoke p (exec p n) "cq_ctl_c" []
    ⦃fun _ s' => LocEq s' s₀ ∧ CqCtlCOK s₀.mem ∧ s'.mem = cqCtlCM s₀.mem; fun e => e.cls = 0⦄
  flush : ∀ n (s₀ : St), ⦃fun s => s = s₀⦄ invoke p (exec p n) "flush_caches" []
    ⦃fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧ s'.mem = flushMem s₀.mem; fun e => e.cls = 0⦄
  reads : ∃ fs, "check_bs" ∈ fs ∧ "check_bc" ∈ fs ∧ readsIn p phaseBPa (fun _ => false) fs = true

/-- An ok run meets a triple's post, whatever its error post. -/
theorem cq_of_run {α : Type} {prog : M α} {s s' : St} {a : α} {P : St → Prop}
    {Q : α → St → Prop} {E : Err → Prop} (hp : P s) (h : prog.run s = .ok (a, s'))
    (hwp : ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; E⦄) : Q a s' := by
  have hs := hwp.le_wp s hp
  rw [Std.WP.StateT.wp_apply_eq, h] at hs
  exact hs

/-- **`check`'s dispatch to modes `8` and `9`**: with the mode word `8` (resp. `9`), `check` is
`check_bs()` (resp. `check_bc()`). -/
theorem check_dispatch89 {p : Prog} (hp : p.lookup "check" = some checkL) (n : Nat) (s₀ : St)
    (md : Word) (f : FnName) (hmf : (md = 8 ∧ f = "check_bs") ∨ (md = 9 ∧ f = "check_bc"))
    (P : Word → Mem → Prop)
    (hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) f []
      ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check" []
    ⦃fun r s' => s₀.mem.glob MODE = md → P (r.headD 0) s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkL]
  rcases hmf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hC ·),
      (L.invoke_loc p (exec p n) "check_a" [·] ·), (L.invoke_loc p (exec p n) "check_bc" [] ·),
      (L.invoke_loc p (exec p n) "check_b" [] ·),
      (L.invoke_loc p (exec p n) "check_c1" [] ·), (L.invoke_loc p (exec p n) "check_c2" [] ·),
      (L.invoke_loc p (exec p n) "check_c3" [·] ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc] at *)
    all_goals grind [lang_grind]
  · vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hC ·),
      (L.invoke_loc p (exec p n) "check_a" [·] ·), (L.invoke_loc p (exec p n) "check_bs" [] ·),
      (L.invoke_loc p (exec p n) "check_b" [] ·),
      (L.invoke_loc p (exec p n) "check_c1" [] ·), (L.invoke_loc p (exec p n) "check_c2" [] ·),
      (L.invoke_loc p (exec p n) "check_c3" [·] ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc] at *)
    all_goals grind [lang_grind]


/-- **Mode `8` in place**: a returning run of `check` with the mode word `8` on a region `W` that
agrees with `N` but in `OUT`, `HDRF`, `CTLF` and the bytes ran `check_bs` on `N`'s side: the
switch's checks, the guards, and a returning `check_jobs(PLO, PHI)` call on `cqSM N` whose final
memory agrees with the region's. -/
theorem cq_check8 {p : Prog} (hQ : CqSeqProg p) {W N : Mem}
    (hAg : Agree phaseBPa (fun _ => false) W N) (hmode : W.glob MODE = 8)
    {n : Nat} (hN : n ≤ 2 ^ 62) {rs : List Word} {W' : Mem} (hrun : L.run p n "check" [] W = .ok (rs, W')) :
    ∃ k r' N', k ≤ 2 ^ 62 ∧ Agree phaseBPa (fun _ => false) W' N' ∧ rs.headD 0 = 71757147230292 ∧
      CqRowsSOK N ∧ CqTailSOK (cqRowsS N) ∧ CqCtlSOK (cqBankSM N) ∧ FlushOK (cqCtlSM (cqBankSM N)) ∧
      ¬ rdW ((cqSM N).arr64 DECL) 0 < (cqSM N).glob PHI ∧ ¬ (cqSM N).glob PHI < (cqSM N).glob PLO ∧
      callE p k "check_jobs" [(cqSM N).glob PLO, (cqSM N).glob PHI] (cqSM N) = .ok (r', N') := by
  obtain ⟨fs, hfs, -, hrd⟩ := hQ.reads
  let P : Word → Mem → Prop := fun x W'' => ∃ k r' N', k ≤ 2 ^ 62 ∧ Agree phaseBPa (fun _ => false) W'' N' ∧
      x = 71757147230292 ∧
      CqRowsSOK N ∧ CqTailSOK (cqRowsS N) ∧ CqCtlSOK (cqBankSM N) ∧ FlushOK (cqCtlSM (cqBankSM N)) ∧
      ¬ rdW ((cqSM N).arr64 DECL) 0 < (cqSM N).glob PHI ∧ ¬ (cqSM N).glob PHI < (cqSM N).glob PLO ∧
      callE p k "check_jobs" [(cqSM N).glob PLO, (cqSM N).glob PHI] (cqSM N) = .ok (r', N')
  let s₀ : St := { mem := W, loc := Locals.init [] }
  cases n with
  | zero =>
    exfalso
    obtain ⟨e, he, -⟩ := callE_zero p "check" [] W
    simp only [L.run, callE] at hrun he
    cases h : (invoke p (exec p 0) "check" []).run { mem := W, loc := Locals.init [] } <;>
      simp_all [Except.map]
  | succ n =>
  have hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_bs" []
      ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄ := by
    intro s₁
    apply M.triple_of_run
    rintro s r s' rfl h1 e1
    have hAg1 : Agree phaseBPa (fun _ => false) s.mem N := by rw [e1]; exact hAg
    obtain ⟨s₂', h2, hAg2, -⟩ := invoke_agree_ok (s₂ := ⟨N, s.loc⟩) hrd hfs hAg1 rfl h1
    cases n with
    | zero =>
      exfalso
      obtain ⟨e, he, -⟩ := callE_zero p "check_bs" [] N
      rw [callE_of_run h2] at he; cases he
    | succ k =>
      have H := cq_of_run (P := fun x => x = ⟨N, s.loc⟩) rfl h2
        (checkBS_spec hQ.bs k (hQ.bankS k) (hQ.ctlS k) (hQ.flush k) ⟨N, s.loc⟩)
      dsimp only at H
      obtain ⟨-, hr, h3, h4, h5, h6, h7, h8, r', hj⟩ := H
      refine ⟨k, r', s₂'.mem, by omega, ?_, ?_, ?_⟩
      · exact hAg2
      · subst hr; rfl
      · exact ⟨h3, h4, h5, h6, h7, h8, hj⟩
  simp only [L.run] at hrun
  cases h : (invoke p (exec p (n + 1)) "check" []).run s₀ with
  | error e => simp [s₀, h, Except.map] at hrun
  | ok x =>
    obtain ⟨r, s'⟩ := x
    simp only [s₀] at h
    rw [h] at hrun
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact M.of_run (P := fun x => x = s₀) rfl h
      (check_dispatch89 hQ.check n s₀ 8 "check_bs" (.inl ⟨rfl, rfl⟩) P hC) hmode

/-- **Mode `9` in place**: a returning run of `check` with the mode word `9` on a region `W` that
agrees with `N` but in `OUT`, `HDRF`, `CTLF` and the bytes ran `check_bc` on `N`'s side: the
switch's checks, the guards, and a returning `check_jobs(PLO, PHI)` call on `cqCM N` whose final
memory agrees with the region's. -/
theorem cq_check9 {p : Prog} (hQ : CqSeqProg p) {W N : Mem}
    (hAg : Agree phaseBPa (fun _ => false) W N) (hmode : W.glob MODE = 9)
    {n : Nat} (hN : n ≤ 2 ^ 62) {rs : List Word} {W' : Mem} (hrun : L.run p n "check" [] W = .ok (rs, W')) :
    ∃ k r' N', k ≤ 2 ^ 62 ∧ Agree phaseBPa (fun _ => false) W' N' ∧ rs.headD 0 = 71757147230292 ∧
      CqCtlCOK (cqBankCM N) ∧ FlushOK (cqCtlCM (cqBankCM N)) ∧
      ¬ rdW ((cqCM N).arr64 DECL) 0 < (cqCM N).glob PHI ∧ ¬ (cqCM N).glob PHI < (cqCM N).glob PLO ∧
      callE p k "check_jobs" [(cqCM N).glob PLO, (cqCM N).glob PHI] (cqCM N) = .ok (r', N') := by
  obtain ⟨fs, -, hfs, hrd⟩ := hQ.reads
  let P : Word → Mem → Prop := fun x W'' => ∃ k r' N', k ≤ 2 ^ 62 ∧ Agree phaseBPa (fun _ => false) W'' N' ∧
      x = 71757147230292 ∧
      CqCtlCOK (cqBankCM N) ∧ FlushOK (cqCtlCM (cqBankCM N)) ∧
      ¬ rdW ((cqCM N).arr64 DECL) 0 < (cqCM N).glob PHI ∧ ¬ (cqCM N).glob PHI < (cqCM N).glob PLO ∧
      callE p k "check_jobs" [(cqCM N).glob PLO, (cqCM N).glob PHI] (cqCM N) = .ok (r', N')
  let s₀ : St := { mem := W, loc := Locals.init [] }
  cases n with
  | zero =>
    exfalso
    obtain ⟨e, he, -⟩ := callE_zero p "check" [] W
    simp only [L.run, callE] at hrun he
    cases h : (invoke p (exec p 0) "check" []).run { mem := W, loc := Locals.init [] } <;>
      simp_all [Except.map]
  | succ n =>
  have hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_bc" []
      ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄ := by
    intro s₁
    apply M.triple_of_run
    rintro s r s' rfl h1 e1
    have hAg1 : Agree phaseBPa (fun _ => false) s.mem N := by rw [e1]; exact hAg
    obtain ⟨s₂', h2, hAg2, -⟩ := invoke_agree_ok (s₂ := ⟨N, s.loc⟩) hrd hfs hAg1 rfl h1
    cases n with
    | zero =>
      exfalso
      obtain ⟨e, he, -⟩ := callE_zero p "check_bc" [] N
      rw [callE_of_run h2] at he; cases he
    | succ k =>
      have H := cq_of_run (P := fun x => x = ⟨N, s.loc⟩) rfl h2
        (checkBC_spec hQ.bc k (hQ.bankC k) (hQ.ctlC k) (hQ.flush k) ⟨N, s.loc⟩)
      dsimp only at H
      obtain ⟨-, hr, h5, h6, h7, h8, r', hj⟩ := H
      refine ⟨k, r', s₂'.mem, by omega, hAg2, ?_, h5, h6, h7, h8, hj⟩
      subst hr; rfl
  simp only [L.run] at hrun
  cases h : (invoke p (exec p (n + 1)) "check" []).run s₀ with
  | error e => simp [s₀, h, Except.map] at hrun
  | ok x =>
    obtain ⟨r, s'⟩ := x
    simp only [s₀] at h
    rw [h] at hrun
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact M.of_run (P := fun x => x = s₀) rfl h
      (check_dispatch89 hQ.check n s₀ 9 "check_bc" (.inr ⟨rfl, rfl⟩) P hC) hmode

end L.Checker
