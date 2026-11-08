module

import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NestGroupCtors
public import ConAgua.Arena.IndPosSpec.UnW
public import ConAgua.Arena.IlpRd
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all Init.Data.List.Control
import ConAgua.Arena.IndPosSpec.SnocWStage
import ConAgua.Arena.RecClassSpec.CloseLams
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.IndPosSpec.UCtx
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# NuW

`nestRootCanon_spec`, `nrcW_ok`, `nestUniformOk_spec`, `nuW_ok`, `cvLps_exec1`, `rootCanon_small` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem nestRootCanon_spec (p : Prog) (hl : PccLook p) (hc : p.lookup "er_copy" = some erCopy)
    (he : p.lookup "er_to_iw" = some erToIw) (hcv : p.lookup "cv_lps" = some cvLps)
    (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St) (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 3)) "nest_root_canon" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nrcW cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem nrcW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : IlpRd cR dn vis fe (IlpBase m a))
    (h : nrcW cR k m ctx cv = some (r, m')) (hS : StageR vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv)
    (hnn : c.nP + c.names.length < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestRootCanon c cvv).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x ∧ PosMR m' ∧ (PccAfr → AFr m m') := by
  sorry

theorem nestUniformOk_spec (p : Prog) (hl : NuLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 4)) "nest_uniform_ok" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nuW cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem nuW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : ∀ (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (h : nuW cR k m ctx cv = some (r, m')) (hS : StageR vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv) (hhi : c.hiAt 0 < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ r = [if x then 1 else 0] ∧ PosMR m' ∧ (NuAfr → AFr m m') := by
  sorry

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena

theorem cvLps_exec1 (p : Prog) (hcv : p.lookup "cv_lps" = some cvLps) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p 1) "cv_lps" [q] ⦃fun _ _ => False; ⊤⦄ := by
  rw [invoke_eq _ hcv]; simp only [callFn, cvLps]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish

theorem rootCanon_small (p : Prog) (hcv : p.lookup "cv_lps" = some cvLps)
    (hp : p.lookup "nest_root_canon" = some nestRootCanonL) (k : Nat) (hk : k ≤ 2) (s₀ : St) (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_root_canon" [ctx, cv] ⦃fun _ _ => False; ⊤⦄ := by
  match k, hk with
  | 0, _ => exact invoke_exec0 p _ _ s₀
  | 1, _ =>
    rw [invoke_eq _ hp]; simp only [callFn, nestRootCanonL]
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish
  | 2, _ =>
    rw [invoke_eq _ hp]; simp only [callFn, nestRootCanonL]
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, cvLps_exec1 p hcv] <;> finish
  | _ + 3, h => exact absurd h (by omega)

theorem nestUniformOk_spec' (p : Prog) (hl : NuLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform_ok" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nuWf cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  match k with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | 1 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish
  | 2 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtxHiAt_specE p hl.hh 1, piDomsOcc_spec p hl.no hl.hpd 1,
        rootCanon_small p hl.hcv hl.pcc.hp' 1 (by omega)] <;> finish [pdoW, pdoK1, noConstWf]
  | 3 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtxHiAt_specE p hl.hh 2, piDomsOcc_spec p hl.no hl.hpd 2,
        rootCanon_small p hl.hcv hl.pcc.hp' 2 (by omega)] <;>
      finish [pdoW, pdoK1, noConstWf, noConstW, noClrK, noGoW]
  | k + 4 => exact nestUniformOk_spec p hl cR hcR k s₀ ctx cv

theorem nestUniformCs_spec (p : Prog) (hl : NuLook p) (hp : p.lookup "nest_uniform_cs" = some nestUniformCsL)
    (cR : CallM) (hcR : CallSpec p cR) (k : Nat) : ∀ (s₀ : St) (ctx o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform_cs" [ctx, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ucW cR k s₀.mem ctx o l = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ ctx o l
    rw [invoke_eq _ hp]; simp only [callFn, nestUniformCsL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ ctx o l
    simp only [invoke_eq _ hp, callFn, nestUniformCsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestUniformOk_spec' p hl cR hcR k, ih] <;>
      finish (gen := 20) [rdW_eq]

/-! ### `nest_uniform`: the relational side -/

theorem nuWf_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (h : nuWf cR k m ctx cv = some (r, m')) (hS : StageR vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv) (hhi : c.hiAt 0 < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ r = [if x then 1 else 0] ∧ PosMR m' ∧ (NuAfr → AFr m m') := by
  match k, h with
  | k + 4, h => exact nuW_ok k dn fe vis m m' a ctx cv c cvv r cR (hI k) h hS hc hin hsl hcv hhi hP

theorem ucW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word) (c : NestCtx)
    (hhi : c.hiAt 0 < 2 ^ 64) (cR : CallM) (J : Mem → AState → Prop) (Pcv : IConstantVal → Prop)
    (hJI : ∀ (m : Mem) (a : AState) (cv : Word) (cvv : IConstantVal), J m a → Pcv cvv →
      decCV (erecP m) cv.toNat = some cvv → ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (hJnu : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (cv : Word) (cvv : IConstantVal) (r : List Word) (x : Bool),
      J m a → Pcv cvv → nuWf cR k m ctx cv = some (r, m') →
      (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') → StageR vis fe m' a' → (NuAfr → AFr m m') →
      J m' a') (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (o l : Word) (cs : List (IConstantVal × Nat)) (r : List Word),
    ucW cR k m ctx o l = some (r, m') → StageR vis fe m a → J m a → (∀ x ∈ cs, Pcv x.1) →
    UCtx dn vis fe m ctx c →
    l.toNat = cs.length → o.toNat + cs.length ≤ iwTop m → CsAt m o.toNat cs (· < iwTop m) → PosMR m →
    ∃ b a', (cs.allM (fun x => ConRon.Arena.nestUniformOk c x.1)).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' ∧ J m' a' := by
  induction k with
  | zero => intro m m' a o l cs r h; simp [ucW] at h
  | succ k ih =>
    intro m m' a o l cs r h hS hJ hPc hU hl hob hcs hP
    by_cases hl0 : l = 0
    · rw [ucW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : cs = [] := List.eq_nil_of_length_eq_zero (by rw [← hl]; rfl)
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl _, rfl, hP, hJ⟩
    rw [ucW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨x, cs', rfl⟩ := List.exists_cons_of_ne_nil (show cs ≠ [] from fun e => by rw [e] at hl; exact hlz hl)
    obtain ⟨w, hw, h0, h1, qn, hqn, hcvv, -⟩ := hcs 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hw hcvv
    have hrw : rdW (m.arr64 IW) o = w := by simp [rdW, hw]
    obtain ⟨q, hq, rfl⟩ : ∃ q : Word, (m.arr64 IW)[w.toNat]? = some q ∧ q.toNat = qn := by
      simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at hqn; exact hqn
    have hrq : rdW (m.arr64 IW) w = q := by simp [rdW, hq]
    rw [hrw, hrq] at h
    rcases hnu : nuWf cR k m ctx q with _ | ⟨r1, m1⟩ <;> rw [hnu] at h; · simp [ucK] at h
    have hPx := hPc x List.mem_cons_self
    obtain ⟨b1, a1, hrun1, hS1, hg1, hr1, hP1, hA1⟩ := nuWf_ok k dn fe vis m m1 a ctx q c x.1 r1 cR
      (hJI m a q x.1 hJ hPx hcvv) hnu hS hU.dec hU.inn hU.sl hcvv hhi hP
    have hJ1 := hJnu k m m1 a a1 q x.1 r1 b1 hJ hPx hnu hrun1 hS1 hA1
    rw [List.allM_cons]
    cases b1 with
    | false =>
      subst hr1
      rw [ucK_no (h := rfl)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, a1, ?_, hS1, hg1, rfl, hP1, hJ1⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind]; rfl
    | true =>
      subst hr1
      rw [ucK_yes (h := by simp)] at h
      have ho1 : (o + 1).toNat = o.toNat + 1 := word_add_toNat (by
        have := hS.iw.iw; have := hS.iw.iwSize; simp at hob; simp; omega)
      have hl1 : (l - 1).toNat = l.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      have hcs1 := hcs.tail
      have hb1 : o.toNat + 1 + cs'.length ≤ iwTop m := by simp at hob; omega
      obtain ⟨b, a', hrun, hS', hg', hr, hP', hJ'⟩ := ih m1 m' a1 (o + 1) (l - 1) cs' r h hS1 hJ1
        (fun y hy => hPc y (List.mem_cons_of_mem _ hy)) (hU.grow hg1)
        (by rw [hl1, hl]; simp) (by rw [ho1]; have := hg1.iw; omega)
        (by rw [ho1]; exact hcs1.grow hb1 hg1) hP1
      refine ⟨b, a', ?_, hS', hg1.trans hg', hr, hP', hJ'⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, ite_true]
      exact hrun

end L.Ind

end

end
