module

public import ConAgua.Arena.JustifyRef5
import ConAgua.Arena.RecLayout.CIDec
import ConRon.Bridge.Pers
public import ConAgua.Arena.CmpVCone
import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Compare.Justify
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# `justify_why` refines `justifyWhy` (lane compare, helper compare-cone)

The solution's constant of the statement's name (`sol_find`), the statements compared
(`same_cv_up_to_levels`), the type's names (`needs_reset`, `needs_expr`), then the cone from an
empty memo (`cs_clear`) over those names (`cone_push`, `cone_go` at the fuel `CTL[225] + 1`).

`0` is the twin's `none`, an accept. A nonzero result is a twin `some`, and the twin runs: its
message reads a name back (`readNameM`), the statement's (it denotes) or the cone's culprit (it
denotes by `coneGo_den`, `Arena/CmpVCone.lean`, given the solution's mates denoting,
`CvMatesDen`).
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind L.Stubs

/-- A message built from a name read back: an `ok` run is a `some`. -/
theorem some_of_msg {α : Type} {x : AM α} {g : α → String} {a a' : AState} {y : Option String}
    (h : (x >>= fun s => pure (some (g s)) : AM (Option String)).run a = .ok (y, a')) :
    y.isSome := by
  obtain ⟨s, a1, -, h2⟩ := ConRon.Bridge.AM.bind_ok h
  cases h2; rfl

/-- A message built from a denoting name read back runs, the store kept. -/
theorem msg_ok {β : Type} {g : ConLeche.Name → β} {a0 a : AState} {h : NIdx} {nm : ConLeche.Name}
    (hx : Ext a0.store a.store) (hd : denoteN a.store.ns h = some nm) :
    ∃ y a', (readNameM h >>= fun s => pure (g s) : AM β).run a = .ok (y, a') ∧
      Ext a0.store a'.store := by
  obtain ⟨x, s', hr, hs⟩ := ConRon.Bridge.CmpV.readNameM_ok hd
  refine ⟨g x, s', ?_, hs ▸ hx⟩
  simp only [StateT.run_bind, show (readNameM h).run a = _ from hr, except_ok_bind]
  rfl

/-- **The walks' memory from the walks' states.** -/
theorem WalkMem.of_walks {m : Mem} (hN : ∃ x, NdR m x) (hW : ∃ s w, CnR m s w) : WalkMem m := by
  obtain ⟨x, hx⟩ := hN
  obtain ⟨s, w, hw⟩ := hW
  exact ⟨⟨_, hx.rel.seen⟩, ⟨_, hw.rel.seen⟩, hx.ctl, hw.ctl⟩

section jw
variable {p : Prog} (P : ConeProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

/-- **`justify_why(vis, x + CI.cv)` refines `justifyWhy`** of the record `x`'s statement: `0`
exactly when the twin answers `none` (an accept, the context and the walks' memory kept); a
nonzero result is a twin `some` whenever the twin's run succeeds. -/
@[refines ConRon.Arena.justifyWhy]
theorem justifyWhy_ok {J : ISolution} {n : Nat} {m m' : Mem} {a : AState} {x : Word}
    {r : List Word} {ci : IConstantInfo}
    (h : callW p n "justify_why" [vis, x + CI.cv] m = some (r, m'))
    (hC : ConeT dn vis fe J m a) (hx : decCI (erecP m) x.toNat = some ci)
    (hden : ∃ C, Frontend.denoteCI a.store ci = some C) (hWM : WalkMem m)
    (hnx : J.idx.next + 1 < 2 ^ 64) :
    ∃ a', ConeT dn vis fe J m' a' ∧ IWGrow m m' ∧ WalkMem m' ∧
      (r.headD 0 = 0 → (ConRon.Arena.justifyWhy J fe ci.toConstantVal).run a = .ok (none, a')) ∧
      (r.headD 0 ≠ 0 → ∀ y a'', (ConRon.Arena.justifyWhy J fe ci.toConstantVal).run a = .ok (y, a'') →
        y.isSome) ∧
      (r.headD 0 ≠ 0 → ∀ {env envS : ConLeche.Env}
        {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)},
        ConRon.Bridge.CheckOK false env fe a → ConRon.Bridge.IFEnvOK envS (ConRon.Bridge.SolView J) a →
        ConRon.Bridge.MatesDen a.store J.mates matesU → ConRon.Bridge.CvMatesDen a.store J.mates →
        ∃ y a'', (ConRon.Arena.justifyWhy J fe ci.toConstantVal).run a = .ok (y, a'') ∧
          Ext a.store a''.store) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (justifyWhy_specW p P.jw n _ vis (x + CI.cv)) h
  rcases n with _ | n
  · rw [justifyWhyW.eq_1] at hW; cases hW
  rw [justifyWhyW.arm1] at hW
  have hcv := decCI_cv hx
  obtain ⟨hwn, hname, -, -, hwt, htype⟩ := decCV_rd_ci (erRdOK m) hcv
  have hq0 : x + (CI.cv + CV.name) = x + CI.cv := by
    rw [show (CI.cv + CV.name : Word) = CI.cv by decide]
  rw [hq0] at hwn hname
  generalize hwn' : erRd m (x + CI.cv) = wn at hW hwn hname
  -- `sol_find`
  replace hW := opt_some hW (justifyWhyW.k_sol_find.eq_1 ..)
  obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  obtain ⟨s1, rfl, hm1, -, hs1n, hs1s⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (solFind_refines p P.srg P.sf n _ wn hC.sol hwn) c1
  simp only at hm1 hs1n hs1s
  rw [hm1] at hW
  rw [← hname] at hs1n hs1s
  by_cases e1 : r1.headD 0 = 0
  · rw [justifyWhyW.k_sol_find.arm1 _ _ _ _ _ _ e1] at hW
    obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
    subst e
    refine ⟨a, hC, IWGrow.refl _, hWM, fun h => absurd h (by decide), fun _ y a'' hy => ?_,
      fun _ env envS matesU _ _ _ _ => ?_⟩
    · simp only [ConRon.Arena.justifyWhy, hs1n.mpr e1] at hy
      exact some_of_msg hy
    · simp only [ConRon.Arena.justifyWhy, hs1n.mpr e1]
      obtain ⟨C, hdc⟩ := hden
      exact msg_ok (Ext.refl _) (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hdc)).1
  rw [justifyWhyW.k_sol_find.arm2 _ _ _ _ _ _ e1] at hW
  obtain ⟨ci', hci'⟩ := Option.ne_none_iff_exists'.mp (fun h => e1 (hs1n.mp h))
  obtain ⟨-, hd⟩ := (hs1s ci').mp hci'
  -- `same_cv_up_to_levels`
  replace hW := opt_some hW (justifyWhyW.k_same_cv_up_to_levels.eq_1 ..)
  obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
  obtain ⟨C, hdc⟩ := hden
  obtain ⟨C', hdd⟩ := hC.sden _ _ hci'
  obtain ⟨b2, a2, hrun2, hT2, hg2, hok2, hr2, hx2, hb2⟩ :=
    sameCv_sim P.cmp n hC.T hC.ok hC.rd hx hd hdc hdd r2 m2 c2
  have hf2 : MemFrame coneA coneC m m2 := cmp_frame P (by simp [cmpFns]) c2
  have hf2c : MemFrame cmpA cmpC m m2 :=
    (run_memFrame P.cmpClosed (by simp [cmpFns]) (run_of_callW c2)).1
  have hJ2 : SolR m2 J := hC.sol.growF hf2 coneA_sol coneC_sol hg2.erecGrow
  have hC2 : ConeT dn vis fe J m2 a2 :=
    ⟨hT2, hok2, hr2, hJ2, hC.fden.ext hx2, hC.sden.ext hx2⟩
  have hWM2 : WalkMem m2 := hWM.frame hf2c (not_mem_cmpA (by decide)) (not_mem_cmpA (by decide))
    (not_mem_cmpC (by decide)) (not_mem_cmpC (by decide))
  have hrun2' : (ConRon.Arena.justifyWhy J fe ci.toConstantVal).run a =
      (if !b2 then
        (do let s ← readNameM ci.toConstantVal.name
            pure (some s!"the solution's {s} has another type") : AM (Option String))
      else do
        let y ← NeedsSt.empty.expr ci.toConstantVal.type
        let q ← ConRon.Arena.coneGo J fe (J.idx.next + 1) ∅ y.acc
        match q.1 with
        | none => pure none
        | some n => do
          let s ← readNameM n
          pure (some s!"its type reads {s}, which the solution does not declare alike")).run a2 := by
    simp only [ConRon.Arena.justifyWhy, hci', StateT.run_bind, hrun2, except_ok_bind, NeedsSt.expr,
      NeedsSt.empty, bind_assoc, pure_bind]
    rfl
  by_cases e2 : r2.headD 0 = 0
  · rw [justifyWhyW.k_same_cv_up_to_levels.arm1 _ _ _ _ _ _ e2] at hW
    obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
    subst e
    have hb : b2 = false := by
      cases hq : b2; rfl; exact absurd (hb2.mpr hq) (by simpa using e2)
    refine ⟨a2, hC2, hg2, hWM2, fun h => absurd h (by decide), fun _ y a'' hy => ?_,
      fun _ env envS matesU _ _ _ _ => ?_⟩
    · rw [hrun2', hb] at hy
      exact some_of_msg hy
    · rw [hrun2', hb]
      exact msg_ok hx2 (ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv
        (ConRon.Bridge.denoteCI_toConstantVal hdc)).1 hx2)
  rw [justifyWhyW.k_same_cv_up_to_levels.arm2 _ _ _ _ _ _ e2] at hW
  have hb : b2 = true := hb2.mp e2
  rw [hb] at hrun2'
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun2'
  -- `needs_reset`, `needs_expr`
  replace hW := opt_some hW (justifyWhyW.k_needs_reset.eq_1 ..)
  obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
  obtain ⟨mp, hmp⟩ := hWM2.nd
  obtain ⟨hy3, hf3⟩ := needsReset_ref P.nd.toNeedsProg c3 hmp hWM2.ntop
  have hS3 := (hT2.stage.ndFrame hf3)
  rw [justifyWhyW.k_needs_reset.arm1] at hW
  replace hW := opt_some hW (justifyWhyW.k_needs_expr.eq_1 ..)
  obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
  have hx2' : decCI (erecP m2) x.toNat = some ci := ArrExt.decCI hg2.ext hx
  obtain ⟨-, -, -, -, hwt2, htype2⟩ := decCV_rd_ci (erRdOK m2) (decCI_cv hx2')
  have hqt : x + CI.cv + CV.type = x + (CI.cv + CV.type) := UInt64.add_assoc _ _ _
  rw [erRd_nd hf3, hqt] at c4
  obtain ⟨y4, e4, hy4, hS4, hf4⟩ := needsExpr_ref P.nd.toNeedsProg c4 hS3.1 hy3 hwt2
  replace e4 : (NeedsSt.empty.expr ci.toConstantVal.type).run a2 = .ok (y4, a2) := by
    rw [htype2]; exact e4
  have hf34 : MemFrame ndA ndC m2 m4 := hf3.trans hf4
  have hT4 : StageT dn vis fe m4 a2 := L.Arena.StageT.of_ndw hT2 hS4 (ndFrame_w hf34)
  have hJ4 : SolR m4 J := hJ2.growF hf34 (by decide) (fun x hx => ndC_sol x hx)
    (iwGrow_frame hf34 (by decide) (by decide)).erecGrow
  -- `cs_clear`, the empty stack, `cone_push`
  rw [justifyWhyW.k_needs_expr.arm1] at hW
  replace hW := opt_some hW (justifyWhyW.k_cs_clear.eq_1 ..)
  obtain ⟨⟨r5, m5⟩, c5, hW⟩ := hW
  obtain ⟨s5, rfl, -, hw5, hm5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (memoClearG_spec csSch p "cs_clear" P.csc n _) c5
  simp only at hw5 hm5
  obtain ⟨mq, hmq0⟩ := hWM2.cs
  have hmq := memoRG_frame csSch csSch_wf nmKey _ ndA ndC (by decide) (by decide) _ _ hf34 _ hmq0
  have hcl := memoRG_clear csSch csSch_wf nmKey (fun w : Word => w != 0) m4 mq hmq hw5
  rw [← hm5] at hcl
  have hfc : MemFrame [CSM] [222, 223] m4 s5.mem := by
    rw [hm5]; exact (mclearG_frame csSch m4).mono (by simp) (by simp [csSch])
  rw [justifyWhyW.k_cs_clear.arm1] at hW
  replace hW := opt_some hW (justifyWhyW.k_cone_push.eq_1 ..)
  obtain ⟨⟨r6, m6⟩, c6, hW⟩ := hW
  have hctop : CTOPC.toNat < (s5.mem.arr64 CTL).size := by
    rw [hfc.size, hf34.size]; exact hWM2.ctop
  have hC0 : CnR (s5.mem.set64 CTL CTOPC 0) ∅ [] := by
    have hT0 : ctlW (s5.mem.set64 CTL CTOPC 0) CTOPC = 0 := by
      simp only [ctlW, rdW_set64, hctop, and_self, ite_true]
    refine ⟨⟨memoRG_frame csSch csSch_wf nmKey _ [] [CTOPC] (by simp) (by decide) _ _
      (MemFrame.setCtl _ _ _) _ hcl, by simp [cwkList, hT0], fun i hi => by rw [hT0] at hi; simp at hi,
      by rw [hT0]; simp⟩, by rw [Mem.size64_set64]; exact hctop⟩
  have hy5 : NdR (s5.mem.set64 CTL CTOPC 0) y4 :=
    (hy4.frame hfc (by decide) (by decide)).frame (MemFrame.setCtl _ _ _) (by simp) (by simp; decide)
  obtain ⟨hW6, hf6⟩ := conePush_ok P.cp c6 hC0 hy5
  rw [List.append_nil] at hW6
  have hfm6 : MemFrame [CSM, CWK] [222, 223, CTOPC] m4 m6 :=
    ((hfc.mono (by simp) (by simp)).trans ((MemFrame.setCtl s5.mem CTOPC 0).mono (by simp) (by simp))).trans
      (hf6.mono (by simp) (by simp))
  have hg46 : IWGrow m4 m6 := iwGrow_frame hfm6 (by decide) (by decide)
  have hC6 : ConeT dn vis fe J m6 a2 :=
    ⟨hT4.of_fr (hT4.stage.frame_hi hfm6 (by decide)
      (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl <;> simp [CTOPC]) (by decide) (by decide)).1 hfm6 (by decide)
      (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl <;> simp [CTOPC]), hok2, hr2,
      hJ4.growF hfm6 (by decide) (by intro y hy; exact not_solCtl (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl <;> simp [CTOPC])) hg46.erecGrow,
      hC2.fden, hC2.sden⟩
  have hN6 : ∃ x, NdR m6 x := ⟨_, hy5.frame hf6 (by decide) (by decide)⟩
  -- `cone_go(CTL[225] + 1, vis)`
  rw [justifyWhyW.k_cone_push.arm1] at hW
  replace hW := opt_some hW (justifyWhyW.k_cone_go.none ..)
  obtain ⟨⟨r7, m7⟩, c7, hW⟩ := hW
  obtain ⟨y7, a7, hrun7, hC7, hg7, hN7, hW7, hr7⟩ := coneGo_ok P c7 hC6 hW6 hN6
  have hfuel : (rdW (m6.arr64 CTL) SNEXTC + 1).toNat = J.idx.next + 1 := by
    have := hC6.sol.next
    simp only [ctlW] at this
    rw [UInt64.toNat_add, this]; simp; omega
  rw [hfuel] at hrun7
  have hg := hg2.trans ((iwGrow_frame hf34 (by decide) (by decide)).trans (hg46.trans hg7))
  have hm7 : m7 = s'.mem := by
    by_cases e7 : r7.headD 0 = 0
    · rw [justifyWhyW.k_cone_go.arm1 _ _ _ e7] at hW; exact (Prod.mk.inj (Option.some.inj hW)).2
    · rw [justifyWhyW.k_cone_go.arm2 _ _ _ e7] at hW; exact (Prod.mk.inj (Option.some.inj hW)).2
  subst hm7
  refine ⟨a7, hC7, hg, WalkMem.of_walks hN7 hW7, fun h0 => ?_, fun h0 y a'' hy => ?_,
    fun h0 env envS matesU hck hsol hm hcm => ?_⟩
  · by_cases e7 : r7.headD 0 = 0
    · rw [hrun2', StateT.run_bind, e4, except_ok_bind, StateT.run_bind, hrun7,
        except_ok_bind]
      simp only [hr7.mp e7]
      rfl
    · rw [justifyWhyW.k_cone_go.arm2 _ _ _ e7] at hW
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hW)
      exact absurd h0 (by simp)
  · by_cases e7 : r7.headD 0 = 0
    · rw [justifyWhyW.k_cone_go.arm1 _ _ _ e7] at hW
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hW)
      exact absurd rfl h0
    · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp (fun e => e7 (hr7.mpr e))
      rw [hrun2', StateT.run_bind, e4, except_ok_bind, StateT.run_bind, hrun7,
        except_ok_bind] at hy
      simp only [hk] at hy
      exact some_of_msg hy
  · by_cases e7 : r7.headD 0 = 0
    · rw [justifyWhyW.k_cone_go.arm1 _ _ _ e7] at hW
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hW)
      exact absurd rfl h0
    · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp (fun e => e7 (hr7.mpr e))
      -- the twin's walk from the statements' comparison: a renaming step, the type's names denote
      obtain ⟨hst2, -⟩ := ConRon.Bridge.sameCvUpToLevels_run hck.state hck.readOK
        (ConRon.Bridge.denoteCI_toConstantVal hdc) (ConRon.Bridge.denoteCI_toConstantVal hdd) hrun2
      have hck2 := hst2.checkOK hck
      have hty2 := ConRon.Bridge.denote_ext (ConRon.Bridge.denoteCV_inv (ConRon.Bridge.denoteCI_toConstantVal hdc)).2.2
        hst2.ext
      obtain ⟨-, hx4⟩ := ConRon.Bridge.CmpV.expr_exact hck2.state hck2.pins
        (ConRon.Bridge.CmpV.XRel.empty a2.store) hty2 e4
      obtain ⟨hst7, hd7⟩ := ConRon.Bridge.CmpV.coneGo_den _ _ _ a2 a7 y7 hck2 (hsol.mono hst2.ext)
        (hm.mono hst2.ok.wf hst2.ext) (hcm.ext hst2.ext)
        (ConRon.Bridge.CmpV.allDen_of_denoteNList hx4.2) hrun7
      obtain ⟨nm, hnm⟩ := hd7 k hk
      rw [hrun2', StateT.run_bind, e4, except_ok_bind, StateT.run_bind, hrun7, except_ok_bind]
      simp only [hk]
      exact msg_ok (hst2.ext.trans hst7.ext) hnm

end jw

end L.Arena
