import ConAgua.Arena.IndPos2SpecF
import ConAgua.Arena.IndPosSpec5

/-! # `nestSeedOf` (lane `indproofs2`, helper `pos`): a resolved class's parameters, each through
`replaceApps` then `replaceFVars (.keyMap params holes)`, written into a fresh slice. -/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `replace_apps` at any exec fuel. -/
def posRpW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, us, b, nn, e => rpConstW k m no nl us b nn e

mutual
def sgGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, ctx, f, dO, dL, q, j =>
    if dL ≤ j then some m
    else sgK1 k ctx f dO dL q j (posRpW k m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (rdW (m.arr64 IW) (ctx + 10)) 0 (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 IW) (dO + j)))
def sgK1 (k : Nat) (ctx f dO dL q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (y, m1) => if 4294967296 ≤ y then none else sgK2 k ctx f dO dL q j (rxW k m1 f y)
def sgK2 (k : Nat) (ctx f dO dL q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (z, m2) => sgGoW k (m2.set64 IW (q + j) z) ctx f dO dL q (j + 1)
end

section arms
variable (k : Nat) (m m1 m2 : Mem) (ctx f dO dL q j y z : Word)
theorem sgGoW_done (h : dL ≤ j) : sgGoW (k + 1) m ctx f dO dL q j = some m := by simp [sgGoW, h]
theorem sgGoW_step (h : ¬ dL ≤ j) : sgGoW (k + 1) m ctx f dO dL q j =
    sgK1 k ctx f dO dL q j (posRpW k m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
      (rdW (m.arr64 IW) (ctx + 10)) 0 (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 IW) (dO + j))) := by
  simp [sgGoW, h]
theorem sgK1_big (h : 4294967296 ≤ y) : sgK1 k ctx f dO dL q j (some (y, m1)) = none := by simp [sgK1, h]
theorem sgK1_ok (h : ¬ 4294967296 ≤ y) : sgK1 k ctx f dO dL q j (some (y, m1)) =
    sgK2 k ctx f dO dL q j (rxW k m1 f y) := by rw [sgK1, ite_eq_right h]
theorem sgK2_some : sgK2 k ctx f dO dL q j (some (z, m2)) =
    sgGoW k (m2.set64 IW (q + j) z) ctx f dO dL q (j + 1) := by rw [sgK2]
end arms
attribute [ind_grind] sgGoW_done sgGoW_step sgK1_big sgK1_ok sgK2_some

def sgC (nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m4) => some ([key, nPc], m4)
def sgB (k : Nat) (ctx f ind us dO dL nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m2) => match sgGoW k m2 ctx f dO dL q 0 with
    | none => none
    | some m3 => sgC nPc (posRecW m3 [ind, us, q, dL])
def sgA (k : Nat) (ctx ind us dO dL nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (f, m1) => sgB k ctx f ind us dO dL nPc (allocW m1 dL)
/-- The model of `nest_seed_of` at exec fuel `k + 1`. -/
def sgW (k : Nat) (m : Mem) (ctx hO hL ind us dO dL nPc : Word) : Option (List Word × Mem) :=
  sgA k ctx ind us dO dL nPc (posRecW m [1, rdW (m.arr64 IW) (ctx + 7), rdW (m.arr64 IW) (ctx + 8), hO, hL])

/-- The lookups of `nest_seed_of`. -/
structure SgLook (p : Prog) : Prop where
  cr : CrLook p
  go : p.lookup "nest_seed_of_go" = some nestSeedOfGoL
  so : p.lookup "nest_seed_of" = some nestSeedOfL

section spec
variable (p : Prog) (L : SgLook p)

include L in
theorem posRp_spec (k : Nat) (s₀ : St) (no nl us b nn e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "replace_apps" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧ posRpW k s₀.mem no nl us b nn e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have C := L.cr
  cases k with
  | zero => rw [invoke_eq _ C.ra]; simp only [callFn, replaceApps]; vcgen [exec] <;> grind
  | succ k => exact replaceApps_spec p C.rx.hl C.rx.hk C.raf C.rap C.rgo C.rnd C.rcl C.ra k s₀ no nl us b nn e

include L in
theorem sgGo_spec (k : Nat) : ∀ (s₀ : St) (ctx f dO dL q j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_seed_of_go" [ctx, f, dO, dL, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ sgGoW k s₀.mem ctx f dO dL q j = some s'.mem; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ ctx f dO dL q j
    rw [invoke_eq _ L.go]; simp only [callFn, nestSeedOfGoL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ ctx f dO dL q j
    have hrx := (rxSpec_all p L.cr.rx k).2.2.2.2.2.2.2
    simp only [invoke_eq _ L.go, callFn, nestSeedOfGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        posRp_spec p L k, hrx, ih] <;>
      finish (gen := 20) [rdW_eq]

include L in
theorem nestSeedOf_spec (k : Nat) (s₀ : St) (ctx hO hL ind us dO dL nPc : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_seed_of" [ctx, hO, hL, ind, us, dO, dL, nPc]
    ⦃fun r s' => LocEq s' s₀ ∧ sgW k s₀.mem ctx hO hL ind us dO dL nPc = some (r, s'.mem); ⊤⦄ := by
  have R := L.cr.rx
  simp only [invoke_eq _ L.so, callFn, nestSeedOfL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      posRec5_specW p R.ha R.h5 k, posRec4_specW p R.ha R.h4 k, iwAlloc_specW p R.ha k, sgGo_spec p L k] <;>
    finish (gen := 20) [sgW, sgA, sgB, sgC, rdW_eq]

end spec


/-! ### The relational side -/

/-- The twin's per-parameter step of `nestSeedOf`. -/
def sgF (c : NestCtx) (holes : List EIdx) (x : EIdx) : AM EIdx := do
  let y ← ConRon.Arena.replaceApps c.names c.lvls 0 c.nP x
  ConRon.Arena.replaceFVars (.keyMap c.params holes) y

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem sgGoW_ok (k : Nat) :
    ∀ (m0 m m' : Mem) (a : AState) (ctx f dO dL q j : Word) (c : NestCtx) (holes ds acc : List EIdx)
      (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word),
    sgGoW k m ctx f dO dL q j = some m' → StageR dn vis fe m a → IWGrow m0 m → iwTop m0 ≤ q.toNat →
    q.toNat + dL.toNat ≤ iwTop m → decCtx m0 ctx.toNat = some c → CtxIn m0 ctx.toNat (· < iwTop m0) →
    CtxSl m0 ctx.toNat → c.nP + c.names.length < 2 ^ 64 → FMOk m0 f.toNat (.keyMap c.params holes) →
    decHL m0 dO.toNat dL.toNat = some ds → (∀ j < dL.toNat, dO.toNat + j < iwTop m0) → j.toNat ≤ dL.toNat →
    decHL m q.toNat j.toNat = some acc → RfInv m M G g → PosMR m →
    ∃ ys a', ((ds.drop j.toNat).mapM (sgF c holes)).run a = .ok (ys, a') ∧
      decHL m' q.toNat dL.toNat = some (acc ++ ys) ∧ StageR dn vis fe m' a' ∧ IWGrow m0 m' ∧
      iwTop m ≤ iwTop m' ∧ (∃ M' G', RfInv m' M' G' g ∧ GKeep M M' G ∧ G ≤ G') ∧ PosMR m' := by
  induction k with
  | zero => intro m0 m m' a ctx f dO dL q j c holes ds acc M G g h; simp [sgGoW] at h
  | succ k ih =>
  intro m0 m m' a ctx f dO dL q j c holes ds acc M G g h hS hg0 hq0 hql hc hin hsl hb hfm hds hdsb hj hacc hR hP
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hxl := decHL_length m0 hds
  have hal := decHL_length m hacc
  by_cases hd : dL ≤ j
  · rw [sgGoW_done (h := hd)] at h
    cases h
    have hjl : j.toNat = dL.toNat := by have := UInt64.le_iff_toNat_le.mp hd; omega
    refine ⟨[], a, ?_, by rw [← hjl]; simpa using hacc, hS, hg0, Nat.le_refl _, ⟨M, G, hR, GKeep.refl _ _,
      UInt64.le_refl _⟩, hP⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  rw [sgGoW_step (h := hd)] at h
  have hjl : j.toNat < dL.toNat := by
    have : ¬ dL.toNat ≤ j.toNat := fun e => hd (UInt64.le_iff_toNat_le.mpr e)
    omega
  -- the context's fields, in `m`
  obtain ⟨ec, hcin⟩ := hin.grow hg0
  have hcm : decCtx m ctx.toNat = some c := by rw [ec]; exact hc
  obtain ⟨hn, hn', -, -, hnP, hlvH, hlv, -, -, h11⟩ := ctx_fields hcm hcin htop
  have hnsum : (rdW (m.arr64 IW) ctx).toNat + (rdW (m.arr64 IW) (ctx + 1)).toNat ≤ iwTop m := by
    have hsl' := hsl.grow hin hg0
    obtain ⟨hnm, -⟩ := decCtx_some hcm
    obtain ⟨o, l, ho, hl, -⟩ := decAt_some hnm
    have r0 : (rdW (m.arr64 IW) ctx).toNat = o := by
      have := rd_iwN (m := m) (p := ctx) (i := 0) (by simpa using ho) (by simp; omega); simpa using this
    have r1 : (rdW (m.arr64 IW) (ctx + 1)).toNat = l := rd_iwN (by simpa using hl) (by simp; omega)
    rw [r0, r1]; exact hsl' 0 (by omega) o l (by simpa using ho) (by simpa using hl)
  -- the parameter
  have hoj := hdsb j.toNat hjl
  obtain ⟨hxH, hxd⟩ := rd_iwH (m := m) (p := dO) (i := j)
    (by rw [iwH_agree (RdS.of_grow hg0) hoj]; exact decHL_getI hds _ hjl) (by omega)
  generalize rdW (m.arr64 IW) (dO + j) = x at h hxH hxd
  cases k with
  | zero => simp [posRpW, sgK1] at h
  | succ k' =>
  simp only [posRpW] at h
  rcases hra : rpConstW k' m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 10)) 0
      (rdW (m.arr64 IW) (ctx + 4)) x with _ | ⟨y, m1⟩; · rw [hra] at h; simp [sgK1] at h
  rw [hra] at h
  obtain ⟨mp0, hM⟩ := hP.rp
  obtain ⟨a1, hr1, hM1, hS1, hg1⟩ := rpConstW_ok k' dn fe vis m m1 a _ _ _ 0 _ x y c.nP c.names mp0 hra hS hxH hlvH hn
    (by omega) hnsum hnP (by rw [hnP]; omega) (by simp; omega) hM
  have hR1 := hR.frame (rpConstW_fr hra)
  by_cases hyb : 4294967296 ≤ y
  · rw [sgK1_big (h := hyb)] at h; simp at h
  rw [sgK1_ok (h := hyb)] at h
  rcases hrf : rxW (k' + 1) m1 f y with _ | ⟨z, m2⟩ <;> rw [hrf] at h; · simp [sgK2] at h
  rw [sgK2_some] at h
  have hg01 := hg0.trans hg1
  obtain ⟨a2, hr2, hzH, M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := (rxOK_all dn fe vis (k' + 1)).2.2.2.2.2.2 m1 m2 a1 f y
    _ z M G g hrf hS1 (hfm.grow hg01) (lt_of_notbig hyb) hR1
  have hqj : (q + j).toNat = q.toNat + j.toNat := word_add_toNat (by omega)
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (show j.toNat + 1 < 2 ^ 64 by have := dL.toNat_lt; omega)
  have hg12 := hg1.trans hg2
  have hacc2 : decHL m2 q.toNat j.toNat = some acc := by rw [decHL_grow hg12 (by omega)]; exact hacc
  have hdec3 := decHL_write m2 q j z acc hzH hS2.2.2.2.1 (by have := hS2.2.1; have := hg12.1; omega) hacc2
  have hS3 := hS2.set_iw (q + j) z
  have hg03 : IWGrow m0 (m2.set64 IW (q + j) z) := (hg0.trans hg12).set_iw (q + j) z (by omega)
  have ht3 : iwTop (m2.set64 IW (q + j) z) = iwTop m2 := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hP3 : PosMR (m2.set64 IW (q + j) z) :=
    ((hP.setRp (rpConstW_mfr hra) ⟨∅, hM1⟩).setRf (rxW_mfr hrf) ⟨M2, G2, g, hR2⟩).fr (MFr.set_iw _ _ _)
  obtain ⟨ys, a', hrun, hdec', hS', hg', ht', ⟨M', G', hR', hk', hG'⟩, hP'⟩ := ih m0 _ m' a2 ctx f dO dL q (j + 1) c
    holes ds (acc ++ [decE z]) M2 G2 g h hS3 hg03 hq0 (by rw [ht3]; have := hg12.1; omega) hc hin hsl hb hfm hds hdsb
    (by rw [hj1]; omega) (by rw [hj1]; exact hdec3) (hR2.frame (RfFr.set_iw _ _ _)) hP3
  refine ⟨decE z :: ys, a', ?_, by simpa using hdec', hS', hg', by have := hg12.1; omega, ⟨M', G', hR',
    hk2.trans hk' hG2, UInt64.le_trans hG2 hG'⟩, hP'⟩
  simp only [List.drop_eq_getElem_cons (show j.toNat < ds.length by omega), List.mapM_cons, StateT.run_bind, sgF, ← hxd, show (decI x : EIdx) = decE x from rfl, ← hlv]
  simp only [show ((0 : Word).toNat) = 0 from rfl] at hr1
  simp only [hr1, except_ok_bind, hr2]
  rw [hj1] at hrun
  rw [hrun]
  rfl

theorem sgW_ok (k : Nat)
    (m m' : Mem) (a : AState) (ctx hO hL ind us dO dL nPc : Word) (r : List Word) (c : NestCtx)
    (holes ds : List EIdx) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (h : sgW k m ctx hO hL ind us dO dL nPc = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hb : c.nP + c.names.length < 2 ^ 64) (hho : decHL m hO.toNat hL.toNat = some holes)
    (hhob : hO.toNat + hL.toNat ≤ iwTop m) (hds : decHL m dO.toNat dL.toNat = some ds)
    (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop m) (hind : H ind) (hus : H us) (hR : RfInv m M G g)
    (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestSeedOf c holes (decI ind) (decI us) ds nPc.toNat).run a = .ok (x, a') ∧
      decNK m' (r.headD 0).toNat = some x.1 ∧ (r.tail.headD 0).toNat = x.2 ∧
      NKIn m' (r.headD 0).toNat (· < iwTop m') ∧ RxPost dn fe vis m m' a' M G g ∧ PosMR m' := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, -, hpa, hpa', -, -, -, -, -, h11⟩ := ctx_fields hc hin htop
  have hpsum : (rdW (m.arr64 IW) (ctx + 7)).toNat + (rdW (m.arr64 IW) (ctx + 8)).toNat ≤ iwTop m := by
    obtain ⟨-, -, -, -, hpm, -⟩ := decCtx_some hc
    obtain ⟨o, l, ho, hl, -⟩ := decAt_some hpm
    rw [rd_iwN (m := m) (p := ctx) (i := 7) (by simpa using ho) (by simp; omega),
      rd_iwN (m := m) (p := ctx) (i := 8) (by simpa using hl) (by simp; omega)]
    exact hsl 7 (by omega) o l ho hl
  unfold sgW at h
  rcases hr1 : posRecW m [1, rdW (m.arr64 IW) (ctx + 7), rdW (m.arr64 IW) (ctx + 8), hO, hL] with _ | ⟨f, m1⟩ <;> rw [hr1] at h; · simp [sgA] at h
  simp only [sgA] at h
  obtain ⟨hS1, hg1, hf1, ht1, hget1⟩ := posRecW_stage hr1 hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht1
  have g0 := iwN_of_get (by simpa using hget1 0 (by simp))
  have g1 := iwN_of_get (by simpa using hget1 1 (by simp))
  have g2 := iwN_of_get (by simpa using hget1 2 (by simp))
  have g3 := iwN_of_get (by simpa using hget1 3 (by simp))
  have g4 := iwN_of_get (by simpa using hget1 4 (by simp))
  have hfm : FMOk m1 f.toNat (.keyMap c.params holes) :=
    ⟨by simpa using g0, by omega, ⟨_, _, g1, g2, by rw [decHL_grow hg1 hpsum]; exact hpa, by have := hg1.1; omega⟩,
      ⟨_, _, g3, g4, by rw [decHL_grow hg1 hhob]; exact hho, by have := hg1.1; omega⟩⟩
  obtain ⟨ec1, hci1⟩ := hin.grow hg1
  have hsl1 := hsl.grow hin hg1
  have hR1 := hR.frame (posRecW_fr hr1)
  rcases hal : allocW m1 dL with _ | ⟨q, m2⟩ <;> rw [hal] at h; · simp [sgB] at h
  simp only [sgB] at h
  obtain ⟨hS2, hg2, hqd, hroom, htop2⟩ := hS1.alloc hal
  have hqt : q.toNat = iwTop m1 := by simp only [iwTop, hqd]
  rcases hgo : sgGoW k m2 ctx f dO dL q 0 with _ | m3 <;> rw [hgo] at h; · simp at h
  simp only at h
  obtain ⟨ys, a3, hrun, hdec3, hS3, hg13, ht3, ⟨M3, G3, hR3, hk3, hG3⟩, hP3⟩ := sgGoW_ok dn fe vis k m1 m2 m3 a ctx f
    dO dL q 0 c holes ds [] M G g hgo hS2 hg2 (by omega) (by omega) (by rw [ec1]; exact hc) hci1 hsl1 hb hfm
    (by rw [decHL_agree (RdS.of_grow hg1) hdsb]; exact hds) (fun j hj => Nat.lt_of_lt_of_le (hdsb j hj) hg1.1)
    (by simp) (by simp [decHL, hslice?]) (hR1.frame (allocW_fr hal))
    ((hP.fr (posRecW_mfr hr1)).fr (allocW_mfr hal))
  rcases hr4 : posRecW m3 [ind, us, q, dL] with _ | ⟨key, m4⟩ <;> rw [hr4] at h; · simp [sgC] at h
  simp only [sgC, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS4, hg4, hk4, ht4, hget4⟩ := posRecW_stage hr4 hS3 (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have hqb : q.toNat + dL.toNat ≤ iwTop m3 := by have := hg13.1; omega
  have hdk : decNK m4 key.toNat = some ⟨decI ind, decI us, ys⟩ :=
    decNK_of_words (by simpa using hget4 0 (by simp)) hind (hget4 1 (by simp)) hus (hget4 2 (by simp))
      (hget4 3 (by simp)) (by rw [decHL_grow hg4 hqb]; simpa using hdec3)
  refine ⟨(⟨decI ind, decI us, ys⟩, nPc.toNat), a3, ?_, hdk, rfl, ?_, ?_, hP3.fr (posRecW_mfr hr4)⟩
  · simp only [ConRon.Arena.nestSeedOf, StateT.run_bind]
    have : (ds.mapM fun x => do
        let y ← ConRon.Arena.replaceApps c.names c.lvls 0 c.nP x
        ConRon.Arena.replaceFVars (.keyMap c.params holes) y) = ds.mapM (sgF c holes) := rfl
    rw [this, show ds = ds.drop (0 : Word).toNat from rfl, hrun]
    rfl
  · simp only [List.headD_cons]
    refine ⟨fun j hj => by omega, fun o l ho hl j hj => ?_⟩
    have e2 := iwN_of_get (m := m4) (by simpa using hget4 2 (by simp))
    have e3 := iwN_of_get (m := m4) (by simpa using hget4 3 (by simp))
    rw [e2] at ho; rw [e3] at hl
    cases ho; cases hl
    have := hg4.1; omega
  · exact ⟨M3, G3, hS4, (hg1.trans hg13).trans hg4, hR3.frame (posRecW_fr hr4), hk3, hG3⟩

end rel


section census
variable (p : Prog) (L : SgLook p)
include L

/-- **`nest_seed_of` refines `nestSeedOf`** (through the stubs below `replace_apps` and `replace_fvars`;
the walk memos well formed in the memory at hand, `PosMR`, and again after). -/
@[refines ConRon.Arena.nestSeedOf]
theorem nestSeedOf_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis ctx hO hL ind us dO dL nPc : Word) (c : NestCtx) (holes ds : List EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) (hP : PosMR s₀.mem)
    (hS : StageR dn vis fe s₀.mem a₀) (hc : decCtx s₀.mem ctx.toNat = some c)
    (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) (hsl : CtxSl s₀.mem ctx.toNat)
    (hb : c.nP + c.names.length < 2 ^ 64) (hho : decHL s₀.mem hO.toNat hL.toNat = some holes)
    (hhob : hO.toNat + hL.toNat ≤ iwTop s₀.mem) (hds : decHL s₀.mem dO.toNat dL.toNat = some ds)
    (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop s₀.mem) (hind : H ind) (hus : H us)
    (hR : RfInv s₀.mem M G g) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_seed_of" [ctx, hO, hL, ind, us, dO, dL, nPc]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestSeedOf c holes (decI ind) (decI us) ds nPc.toNat) a₀ ∧
      decNK s'.mem (r.headD 0).toNat =
        some (AM.res (ConRon.Arena.nestSeedOf c holes (decI ind) (decI us) ds nPc.toNat) a₀).1 ∧
      (r.tail.headD 0).toNat = (AM.res (ConRon.Arena.nestSeedOf c holes (decI ind) (decI us) ds nPc.toNat) a₀).2 ∧
      NKIn s'.mem (r.headD 0).toNat (· < iwTop s'.mem) ∧
      RxPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.nestSeedOf c holes (decI ind) (decI us) ds nPc.toNat) a₀)
        M G g ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (nestSeedOf_spec p L k s₀ ctx hO hL ind us dO dL nPc) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, h1, h2, h3, h4, hP'⟩ := sgW_ok dn fe vis k _ _ a₀ ctx hO hL ind us dO dL nPc r c holes ds
    M G g hm hS hc hin hsl hb hho hhob hds hdsb hind hus hR hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact h1, by rw [hres]; exact h2, h3, by rw [hst]; exact h4, hP'⟩

end census
end L.Ind
