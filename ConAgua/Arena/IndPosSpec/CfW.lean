module

import ConAgua.Arena.IndPosSpec.NestAcceptGroup
import ConAgua.Arena.IndPosSpec.NestCrest2
public import ConAgua.Arena.IndPosSpec.NestGroupCtors
public import ConAgua.Arena.IndPosSpec.P2ctK1
public import ConAgua.Arena.IndPosSpec.UCtx
import ConAgua.Arena.IndPosSpec.UnW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPosSpec.NestKeyMap
public import ConAgua.Arena.IndPosSpec.GrpAt
import all ConAgua.Arena.IndPos

@[expose] public section

/-!
# CfW

`NfsB.grow`, `pos2_rd_get`, `nsb_words`, `NSB.grow`, `nsb_rec6`, `cfK3_some` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem NfsB.grow {m m' : Mem} {o l : Nat} {xs : List NestCtorNf} (h : NfsB m o l xs) (hg : IWGrow m m') :
    NfsB m' o l xs := DecB.grow (OMono.decPL decNCN_mono o l) hg h

/-- A word read at `p + i`, with no wrap. -/
theorem pos2_rd_get {m : Mem} {p i v : Word} (h : (m.arr64 IW)[p.toNat + i.toNat]? = some v)
    (hb : p.toNat + i.toNat < 2 ^ 64) : rdW (m.arr64 IW) (p + i) = v := by
  have : (p + i).toNat = p.toNat + i.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hb
  simp [rdW, this, h]

/-- The words of a decoded `NestState` record lie below the top. -/
theorem nsb_words {m : Mem} {p : Word} {NS : NestState} (h : NSB m p NS) (htop : iwTop m < 2 ^ 64) :
    p.toNat + 6 ≤ iwTop m ∧
    KsB m (rdW (m.arr64 IW) p).toNat (rdW (m.arr64 IW) (p + 1)).toNat NS.keys.toList ∧
    KsB m (rdW (m.arr64 IW) (p + 2)).toNat (rdW (m.arr64 IW) (p + 3)).toNat NS.active ∧
    NfsB m (rdW (m.arr64 IW) (p + 4)).toNat (rdW (m.arr64 IW) (p + 5)).toNat NS.ctorNfs.toList := by
  have h' : decNS (truncM m) p.toNat = some NS := h.dec
  simp only [decNS, decAt, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h'
  obtain ⟨ks, ⟨o0, ho0, l0, hl0, hks⟩, act, ⟨o2, ho2, l2, hl2, hact⟩, nfs, ⟨o4, ho4, l4, hl4, hnfs⟩, hNS⟩ := h'
  cases hNS
  obtain ⟨i0, e0⟩ := pos2_iwN_trunc ho0
  obtain ⟨i1, e1⟩ := pos2_iwN_trunc hl0
  obtain ⟨i2, e2⟩ := pos2_iwN_trunc ho2
  obtain ⟨i3, e3⟩ := pos2_iwN_trunc hl2
  obtain ⟨i4, e4⟩ := pos2_iwN_trunc ho4
  obtain ⟨i5, e5⟩ := pos2_iwN_trunc hl4
  have r0 : (rdW (m.arr64 IW) p).toNat = o0 := by
    have := rd_iwN (m := m) (p := p) (i := 0) (by simpa using e0) (by simp; omega); simpa using this
  rw [r0, rd_iwN (i := 1) (by simpa using e1) (by simp; omega), rd_iwN (i := 2) (by simpa using e2) (by simp; omega),
    rd_iwN (i := 3) (by simpa using e3) (by simp; omega), rd_iwN (i := 4) (by simpa using e4) (by simp; omega),
    rd_iwN (i := 5) (by simpa using e5) (by simp; omega)]
  exact ⟨by omega, by simpa [KsB, DecB] using hks, hact, by simpa [NfsB, DecB] using hnfs⟩

theorem NSB.grow {m m' : Mem} {p : Word} {NS : NestState} (h : NSB m p NS) (hg : IWGrow m m')
    (htop : iwTop m < 2 ^ 64) : NSB m' p NS := by
  have hp := (nsb_words h htop).1
  have e : ∀ i : Word, i.toNat < 6 → rdW (m'.arr64 IW) (p + i) = rdW (m.arr64 IW) (p + i) := by
    intro i hi
    have : (p + i).toNat = p.toNat + i.toNat := word_add_toNat (by omega)
    simp only [rdW, this]; rw [hg.iwGet _ (by omega)]
  have e0 : rdW (m'.arr64 IW) p = rdW (m.arr64 IW) p := by simpa using e 0 (by decide)
  refine ⟨DecB.grow (decNS_mono _) hg h.dec, ?_, ?_, ?_⟩
  · rw [e0, e 1 (by decide)]; have := h.b0; have := hg.iw; omega
  · rw [e 2 (by decide), e 3 (by decide)]; have := h.b2; have := hg.iw; omega
  · rw [e 4 (by decide), e 5 (by decide)]; have := h.b4; have := hg.iw; omega

/-- **A fresh `NestState` record** (`rec6` of three slices decoded below the tops). -/
theorem nsb_rec6 {m' : Mem} {q kO kL aO aL nO nL : Word} {keys act : List NestKey} {nfs : List NestCtorNf}
    (hq : q.toNat + 6 ≤ iwTop m') (htop : iwTop m' < 2 ^ 64)
    (hget : ∀ j < [kO, kL, aO, aL, nO, nL].length, (m'.arr64 IW)[q.toNat + j]? = [kO, kL, aO, aL, nO, nL][j]?)
    (hk : KsB m' kO.toNat kL.toNat keys) (hkb : kO.toNat + kL.toNat ≤ iwTop m')
    (ha : KsB m' aO.toNat aL.toNat act) (hab : aO.toNat + aL.toNat ≤ iwTop m')
    (hn : NfsB m' nO.toNat nL.toNat nfs) (hnb : nO.toNat + nL.toNat ≤ iwTop m') :
    NSB m' q ⟨keys.toArray, act, nfs.toArray⟩ := by
  sorry

end L.Ind

namespace L.Ind

open L.Arena

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (us dO dL gO gL ns2 aO aL kb q : Word) (r : List Word)
theorem cfK3_some : cfK3 kb (some (q, m3)) = some ([nestedW kb, q], m3) := rfl
theorem cfK2_some : cfK2 ns2 aO aL kb (some (r, m2)) = cfK3 kb (posRecW m2 [r.headD 0, r.tail.headD 0, aO, aL,
    rdW (m2.arr64 IW) (ns2 + 4), rdW (m2.arr64 IW) (ns2 + 5)]) := rfl
theorem cfK1_acc (h : r.headD 0 ≠ 0) : cfK1 k us dO dL gO gL ns2 aO aL kb (some (r, m1)) =
    cfK2 ns2 aO aL kb (nagW k m1 us dO dL gO gL (rdW (m1.arr64 IW) ns2) (rdW (m1.arr64 IW) (ns2 + 1))) := by
  rw [cfK1, ite_eq_left h]
theorem cfK1_open (h : ¬ r.headD 0 ≠ 0) : cfK1 k us dO dL gO gL ns2 aO aL kb (some (r, m1)) =
    cfK2 ns2 aO aL kb (some ([rdW (m1.arr64 IW) ns2, rdW (m1.arr64 IW) (ns2 + 1)], m1)) := by
  rw [cfK1, ite_eq_right h]
end arms
attribute [ind_grind] cfK3_some cfK2_some cfK1_acc cfK1_open

end L.Ind

namespace L.Ind

open L.Arena

/-- The twin's tail of `nestContNew`. -/
def cfT (c : NestCtx) (us : LsIdx) (ds : List EIdx) (grp : List (NIdx × EIdx)) (ns2 : NestState)
    (act : List NestKey) (kb : Nat) : AM (NestFieldKind × NestState) := do
  let closed ← ds.allM (dsF (c.hiAt 0))
  let keys := if closed then nestAcceptGroup us ds grp ns2.keys else ns2.keys
  pure (.nested (kb != 0), { keys, active := act, ctorNfs := ns2.ctorNfs })

/-- `decNFK` of a `.nested` kind word. -/
theorem decNFK_nestedW (kb : Word) : decNFK (nestedW kb) = some (.nested (kb.toNat != 0)) := by
  by_cases h : kb = 0
  · subst h; decide
  · have : kb.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
    simp only [nestedW, h, ne_eq, not_false_eq_true, ite_true]
    simp [decNFK, this]

theorem cfW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {k : Nat} {m m' : Mem} {a : AState}
    {ctx us dO dL gO gL ns2 aO aL kb : Word} {c : NestCtx} {ds : List EIdx} {grp : List (NIdx × EIdx)}
    {NS2 : NestState} {act : List NestKey} {r : List Word}
    (h : cfW k m ctx us dO dL gO gL ns2 aO aL kb = some (r, m')) (hS : StageR vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hhi : c.hiAt 0 < 2 ^ 64) (hus : H us)
    (hds : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds)
    (hdsb : dO.toNat + dL.toNat ≤ iwTop m)
    (hgl : gL.toNat = grp.length) (hgb : gO.toNat + grp.length ≤ iwTop m) (hgrp : GrpAt m gO.toNat grp)
    (hns : NSB m ns2 NS2) (hact : KsB m aO.toNat aL.toNat act) (hab : aO.toNat + aL.toNat ≤ iwTop m) :
    ∃ x a', (cfT c (decI us) ds grp NS2 act kb.toNat).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ r.headD 0 = nestedW kb ∧ decNFK (r.headD 0) = some x.1 ∧ NSB m' (r.tail.headD 0) x.2 := by
  cases k with
  | zero => simp [cfW] at h
  | succ k =>
  simp only [cfW] at h
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  have hdsD := hds.get (OMono.decHL _ _)
  rcases hdc : dcWf k m ctx dO dL with _ | ⟨r1, m1⟩ <;> rw [hdc] at h; · simp [cfK1] at h
  obtain ⟨b, a1, hrun1, hS1, hg1, hr1⟩ := dcWf_ok dn fe vis k m m1 a ctx dO dL c ds r1 hdc hS hU.dec hU.inn hhi hdsD
    (fun j hj => by omega)
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
  have hns1 := hns.grow hg1 htop
  obtain ⟨hp6, hk1, -, hn1⟩ := nsb_words hns1 htop1
  have hkb1 := hns1.b0
  -- the keys, cached or not
  have hkeys : ∃ (rk : List Word) (mk : Mem), cfK1 k us dO dL gO gL ns2 aO aL kb (some (r1, m1)) =
      cfK2 ns2 aO aL kb (some (rk, mk)) ∧ StageR vis fe mk a1 ∧ IWGrow m1 mk ∧
      KsB mk (rk.headD 0).toNat (rk.tail.headD 0).toNat
        (if b then nestAcceptGroup (decI us) ds grp NS2.keys else NS2.keys).toList ∧
      (rk.headD 0).toNat + (rk.tail.headD 0).toNat ≤ iwTop mk := by
    cases b with
    | true =>
      rw [cfK1_acc (h := by rw [hr1]; decide)]
      rcases hag : nagW k m1 us dO dL gO gL (rdW (m1.arr64 IW) ns2) (rdW (m1.arr64 IW) (ns2 + 1)) with _ | ⟨rk, mk⟩; · rw [cfK1_acc (h := by rw [hr1]; decide), hag] at h; simp [cfK2] at h
      obtain ⟨h1, h2, h3, h4⟩ := nagW_ok dn vis fe us dO dL ds hus k m1 mk a1 gO gL _ _ grp NS2.keys rk hag hS1
        (DecB.grow (OMono.decHL _ _) hg1 hds) hgl (by have := hg1.iw; omega) (hgrp.grow hgb hg1) hk1 hkb1
      exact ⟨rk, mk, rfl, h1, h2, by simpa using h3, h4⟩
    | false =>
      rw [cfK1_open (h := by rw [hr1]; decide)]
      exact ⟨_, m1, rfl, hS1, IWGrow.refl _, by simpa using hk1, by simpa using hkb1⟩
  obtain ⟨rk, mk, hk, hSk, hgk, hksk, hkbk⟩ := hkeys
  rw [hk, cfK2_some] at h
  rcases hq : posRecW mk [rk.headD 0, rk.tail.headD 0, aO, aL, rdW (mk.arr64 IW) (ns2 + 4),
      rdW (mk.arr64 IW) (ns2 + 5)] with _ | ⟨q, m3⟩; · rw [hq] at h; simp [cfK3] at h
  rw [hq, cfK3_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS3, hg3, hqq, ht3, hget3⟩ := posRecW_stage hq hSk (by simp)
  simp only [List.length_cons, List.length_nil] at ht3
  have hg13 := hg1.trans (hgk.trans hg3)
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.iw.iw hS3.iw.iwSize
  have hnk := (hns1.grow hgk htop1)
  obtain ⟨-, -, -, hnk'⟩ := nsb_words hnk (Nat.lt_of_le_of_lt hSk.iw.iw hSk.iw.iwSize)
  refine ⟨(.nested (kb.toNat != 0), (NestState.mk (if b then nestAcceptGroup (decI us) ds grp NS2.keys
    else NS2.keys) act NS2.ctorNfs)), a1, ?_, hS3, hg13, rfl, by simpa using decNFK_nestedW kb, ?_⟩
  · simp only [cfT, StateT.run_bind, hrun1, except_ok_bind]; rfl
  · have := nsb_rec6 (m' := m3) (q := q) (keys := (if b then nestAcceptGroup (decI us) ds grp NS2.keys
        else NS2.keys).toList) (act := act) (nfs := NS2.ctorNfs.toList) (by omega) htop3 hget3
      (hksk.grow hg3) (by have := hg3.iw; omega) ((hact.grow hg1).grow (hgk.trans hg3))
      (by have := hg13.iw; omega) (hnk'.grow hg3) (by have := hnk.b4; have := hg3.iw; omega)
    simpa using this

end L.Ind

namespace L.Ind

open L.Arena

/- ronsync2 stage 2: commented out (statement at the old twin/L)
def naWf : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, vis, c => naW k m vis c
-/


end L.Ind

namespace L.Ind

open L.Arena

section arms
variable (n : Nat) (m m1 : Mem) (ko nF cl i su : Word)
theorem u4W_done (h : nF ≤ i) : u4W (n + 1) m ko nF cl i = some ([0], m) := by simp [u4W, h]
theorem u4W_kind (h : ¬ nF ≤ i) (hk : rdW (m.arr64 IW) (ko + i) ≠ 0) :
    u4W (n + 1) m ko nF cl i = u4K n ko nF cl i (ustWf n m cl 0 i) := by simp [u4W, h, hk]
theorem u4W_ord (h : ¬ nF ≤ i) (hk : ¬ rdW (m.arr64 IW) (ko + i) ≠ 0) :
    u4W (n + 1) m ko nF cl i = u4W n m ko nF cl (i + 1) := by simp only [u4W]; rw [ite_eq_right h, ite_eq_right hk]
theorem u4K_hit (h : su ≠ 0) : u4K n ko nF cl i (some (su, m1)) = some ([1], m1) := by rw [u4K, ite_eq_left h]
theorem u4K_miss (h : ¬ su ≠ 0) : u4K n ko nF cl i (some (su, m1)) = u4W n m1 ko nF cl (i + 1) := by
  rw [u4K, ite_eq_right h]
end arms
attribute [ind_grind] u4W_done u4W_kind u4W_ord u4K_hit u4K_miss

end L.Ind

namespace L.Ind

open L.Arena

theorem decKL_get {m : Mem} {o l : Nat} {ks : List NestFieldKind} (h : decKL m o l = some ks) :
    ks.length = l ∧ ∀ j (_hj : j < l), ∃ w, iwA m (o + j) = some w ∧ decNFK w = ks[j]? := by
  induction l generalizing o ks with
  | zero => simp [decKL] at h; subst h; simp
  | succ l ih =>
    simp only [decKL_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, hw, x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hxs
    refine ⟨by simp [h1], fun j _hj => ?_⟩
    cases j with
    | zero => exact ⟨w, by simpa using hw, by simpa using hx⟩
    | succ j =>
      obtain ⟨w', hw', hx'⟩ := h2 j (by omega)
      exact ⟨w', by rw [show o + (j + 1) = o + 1 + j by omega]; exact hw', by simpa using hx'⟩

end L.Ind

namespace L.Ind

open L.Arena

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (ctx hi cur : Word) (r : List Word)
theorem roK2_some : roK2 (some (r, m3)) = some ([if r.headD 0 = 0 then 1 else 0], m3) := rfl
theorem roK1_some : roK1 k ctx hi (some (r, m2)) = roK2 (noaW k m2 (rdW (m2.arr64 IW) ctx)
    (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi (r.headD 0) (r.tail.headD 0)) := rfl
theorem roK0_eq : roK0 k ctx hi cur (some (r, m1)) =
    if r.headD 0 = 0 then some ([0], m1) else roK1 k ctx hi (gaaF m1 [CWF, cur]) := rfl
end arms
attribute [ind_grind] roK2_some roK1_some

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Callees at small exec fuel, and their models at any exec fuel -/

theorem canonCrest_exec1 (p : Prog) (hp : p.lookup "nest_canon_crest" = some nestCanonCrest) (s₀ : St)
    (no nl us nn cty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p 1) "nest_canon_crest" [no, nl, us, nn, cty] ⦃fun _ _ => False; ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, nestCanonCrest]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> finish

theorem nestCrest_spec' (p : Prog) (L : CrLook p) (k : Nat) (s₀ : St) (no nl us dO dL hO hL cty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_crest" [no, nl, us, dO, dL, hO, hL, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ pcrWf k s₀.mem no nl us dO dL hO hL cty = some (r, s'.mem); ⊤⦄ := by
  match k with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | 1 =>
    rw [invoke_eq _ L.cr]; simp only [callFn, nestCrest]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> finish
  | 2 =>
    rw [invoke_eq _ L.cr]; simp only [callFn, nestCrest]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, canonCrest_exec1 p L.cc] <;> finish
  | k + 3 => exact nestCrest_spec p L k s₀ no nl us dO dL hO hL cty

end L.Ind

end
