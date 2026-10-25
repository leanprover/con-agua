import ConAgua.Arena.LoopStart
import ConAgua.Arena.FreezeRel

/-!
# Phase A as entry 1 runs it: `install_fold_go(0, cnt, 0)` ending in `PhaseBStart` (lane parmode)

docs/design/parmode.md, "Step 4" (a). Entry 1 (`check_a`, `Checker/Entry.lean`) runs phase A's
fold directly, `install_fold_go(0, DECL[0], 0)`, then `par_compact`. Here the fold's run, from the
loop's start facts (as `installThenCheck_refines`, `CheckerT.lean`; ported from lane parallel's
`phaseA_refines`, which had a `phase_a` function around the fold):

* `installFoldGo_phaseA`: a returning `install_fold_go(0, cnt, 0)` (`cnt` the number of records)
  means the twin's phase A accepts (`installFold … = .ok (.ok (ds.size, fe, pend), a')`), and the
  memory is `PhaseBStart … a' v` at the fold's result `v` (the final view), with con-ron's phase-B
  invariant from `TwinPend.startAM`.
* `installFoldGo_start`: the same from the memory facts the stages before the loop leave
  (`loop_start`, `LoopStart.lean`), at the start store's name decoder `dnOf`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- **Phase A's fold, from record `0`, refines the twin's phase A and ends in `PhaseBStart`.** -/
theorem installFoldGo_phaseA (mode : ConLeche.CheckMode) (pins : List INatOpPinSet)
    (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration) (p : Prog)
    (hm : mode = .verified) (hb : BracketProg p) (hdc : LoopCallees dn p)
    (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds)
    (hpp : p.lookup "pend_push" = some pendPushL)
    (hpn : p.lookup "is_none" = some isNoneL) (hps : p.lookup "is_some" = some isSomeL)
    (hpi : p.lookup "install_step" = some installStepL)
    (hpd : p.lookup "install_decl_step" = some installDeclStepL)
    (hpg : p.lookup "install_fold_go" = some installFoldGoL)
    (hpx : p.lookup "install_fold_next" = some installFoldNextL) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (cnt : Word) (hcnt : cnt.toNat = ds.size)
    (hT : TwinFold pins ds (mkIFEnv IEnv.empty) #[] a₀)
    (hR : LoopR pins dn s₀.mem a₀ 0 (mkIFEnv IEnv.empty) #[] ds)
    (hM : LoopMem dn s₀.mem a₀) (hc : CoreMemos s₀.mem) (hIM : IndMemos s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_go" [0, cnt, 0]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ (fe : IFEnv) (pend : Array PendingCheck) (a' : AState),
      installFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList a₀ = .ok (.ok (ds.size, fe, pend), a') ∧
      PhaseBStart pins dn ds fe pend s'.mem a' (r.headD 0); ⊤⦄ := by
  have hsz : ds.size < 2 ^ 63 := by have := hR.decls.dsize; have := hR.decls.room; omega
  refine triple_post ((installFoldGo_refines mode pins dn ds p hpp hpn hps hpi hpd hpg hpx hsz hb hdc
    hm hFD hLD n hn).1 s₀ a₀ 0 cnt 0 (mkIFEnv IEnv.empty) #[] (by simp) hcnt hT hR hM hc hIM) ?_
  intro r s' ⟨hl, h⟩
  simp only [FoldPost, UInt64.toNat_zero, List.drop_zero] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨e, hL⟩ := FoldOut.eq h2
  have hrun := AM.run_of_ok _ _ h1
  rw [e] at hrun
  refine ⟨hl, _, _, _, hrun, hL, h3, h4, ?_, h5.cr⟩
  subst hm
  exact TwinPend.startAM hT h1 e

/-- **Phase A's fold from the loop's start**: from the memory facts the stages before it leave and
the twin's fold invariant at its start state `a`, a returning `install_fold_go(0, cnt, 0)` is an
accepting phase A ending in `PhaseBStart` at its result (the final view). The name decoder is the
start store's (`dnOf`). -/
theorem installFoldGo_start {p : Prog} {pins : List INatOpPinSet} {ds : Array IDeclaration}
    {a : AState} (hP : LoopTopProg p) (hdc : LoopCallees (dnOf a.store) p) (hFD : FrontDecls ds)
    (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (cnt : Word) (hcnt : cnt.toNat = ds.size)
    (hT : TwinFold pins ds (mkIFEnv IEnv.empty) #[] a)
    (hA : ArenaD s₀.mem a) (hcore : CoreR s₀.mem a.caches) (hpf : PinsFull s₀.mem a.pins)
    (hD : DeclsF (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) ds) (hPS : L.Rom.PinSetsR s₀.mem pins)
    (hiw : L.Ind.IWOK s₀.mem) (hz : LoopZero s₀.mem) (hpin : pinW s₀.mem 0 ≠ 0)
    (hE : (s₀.mem.arr64 EREC).size < 2 ^ 63) (hS : (s₀.mem.arr64 SPN).size < 2 ^ 63)
    (hB : (s₀.mem.arr64 145).size < 2 ^ 63) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_go" [0, cnt, 0]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ (fe : IFEnv) (pend : Array PendingCheck) (a' : AState),
      installFold .verified pins (0, mkIFEnv IEnv.empty, #[]) ds.toList a = .ok (.ok (ds.size, fe, pend), a') ∧
      PhaseBStart pins (dnOf a.store) ds fe pend s'.mem a' (r.headD 0); ⊤⦄ := by
  obtain ⟨hR, hM, hc, hIM⟩ := loop_start (pins := pins) hA hcore hpf hD hPS hiw hz hpin hE hS hB hmode
  exact installFoldGo_phaseA .verified pins (dnOf a.store) ds p rfl hP.bracket hdc hFD
    (declsLpsDn_dnOf hT.pd hT.den) hP.pp hP.pn hP.ps hP.pi hP.pd hP.pg hP.px n hn s₀ a cnt hcnt hT hR
    hM hc hIM

/-- The number of records at the loop's start is `DECL[0]` (`DeclsF`). -/
theorem declCount_eq {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {v : Word} {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (hR : LoopR pins dn m a v fe pend ds) (h : 0 < (m.arr64 DECL).size) :
    ((m.arr64 DECL)[0]).toNat = ds.size := by
  have := hR.decls.count; simpa [h] using this

/-- The number of pending groups is `CTL[130]` (`PendR`). -/
theorem pendCount_eq {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {v : Word} {fe : IFEnv} {pend : Array PendingCheck} {ds : Array IDeclaration}
    (hR : LoopR pins dn m a v fe pend ds) (h : 130 < (m.arr64 CTL).size) :
    ((m.arr64 CTL)[130]).toNat = pend.size := by
  have := hR.pend.count; simp only [pendCount] at this
  rwa [rdW_eq _ _ 130 rfl h] at this

end L.Arena
