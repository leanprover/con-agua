import ConAgua.Arena.IndPos2SpecL

/-! # `IndPos2`, the `nestPos` block's leaves, continued (lane `indproofs2`, helper `pos2`): the
walk's state record (`NestState`, decoded below the tops), `nest_cont_new_finish`. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The walk's state, below the tops -/

/-- A `NestState` record at `p`: decoded below the tops, its three slices below the top. -/
structure NSB (m : Mem) (p : Word) (NS : NestState) : Prop where
  dec : DecB (fun m => decNS m p.toNat) m NS
  b0 : (rdW (m.arr64 IW) p).toNat + (rdW (m.arr64 IW) (p + 1)).toNat ≤ iwTop m
  b2 : (rdW (m.arr64 IW) (p + 2)).toNat + (rdW (m.arr64 IW) (p + 3)).toNat ≤ iwTop m
  b4 : (rdW (m.arr64 IW) (p + 4)).toNat + (rdW (m.arr64 IW) (p + 5)).toNat ≤ iwTop m

/-- A `NestCtorNf` slice decoded below the tops. -/
def NfsB (m : Mem) (o l : Nat) (xs : List NestCtorNf) : Prop := DecB (fun m => decPL m (decNCN m) o l) m xs

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
    simp only [rdW, this]; rw [hg.2.2.1 _ (by omega)]
  have e0 : rdW (m'.arr64 IW) p = rdW (m.arr64 IW) p := by simpa using e 0 (by decide)
  refine ⟨DecB.grow (decNS_mono _) hg h.dec, ?_, ?_, ?_⟩
  · rw [e0, e 1 (by decide)]; have := h.b0; have := hg.1; omega
  · rw [e 2 (by decide), e 3 (by decide)]; have := h.b2; have := hg.1; omega
  · rw [e 4 (by decide), e 5 (by decide)]; have := h.b4; have := hg.1; omega

/-- **A fresh `NestState` record** (`rec6` of three slices decoded below the tops). -/
theorem nsb_rec6 {m' : Mem} {q kO kL aO aL nO nL : Word} {keys act : List NestKey} {nfs : List NestCtorNf}
    (hq : q.toNat + 6 ≤ iwTop m') (htop : iwTop m' < 2 ^ 64)
    (hget : ∀ j < [kO, kL, aO, aL, nO, nL].length, (m'.arr64 IW)[q.toNat + j]? = [kO, kL, aO, aL, nO, nL][j]?)
    (hk : KsB m' kO.toNat kL.toNat keys) (hkb : kO.toNat + kL.toNat ≤ iwTop m')
    (ha : KsB m' aO.toNat aL.toNat act) (hab : aO.toNat + aL.toNat ≤ iwTop m')
    (hn : NfsB m' nO.toNat nL.toNat nfs) (hnb : nO.toNat + nL.toNat ≤ iwTop m') :
    NSB m' q ⟨keys.toArray, act, nfs.toArray⟩ := by
  have g : ∀ j < 6, (iwA (truncM m'))[q.toNat + j]? = [kO, kL, aO, aL, nO, nL][j]? := fun j hj => by
    rw [truncM_iw_eq (by omega)]; exact hget j (by simpa using hj)
  have n0 : iwN (truncM m') q.toNat = some kO.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 0 (by omega))
  have n1 : iwN (truncM m') (q.toNat + 1) = some kL.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 1 (by omega))
  have n2 : iwN (truncM m') (q.toNat + 2) = some aO.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 2 (by omega))
  have n3 : iwN (truncM m') (q.toNat + 2 + 1) = some aL.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 3 (by omega))
  have n4 : iwN (truncM m') (q.toNat + 4) = some nO.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 4 (by omega))
  have n5 : iwN (truncM m') (q.toNat + 4 + 1) = some nL.toNat := by simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 5 (by omega))
  have rq : ∀ i : Word, i.toNat < 6 → rdW (m'.arr64 IW) (q + i) = [kO, kL, aO, aL, nO, nL][i.toNat]?.getD 0 := by
    intro i hi
    have : (q + i).toNat = q.toNat + i.toNat := word_add_toNat (by omega)
    simp only [rdW, this]; rw [hget _ (by simpa using hi)]
  have r0 : rdW (m'.arr64 IW) q = kO := by simpa using rq 0 (by decide)
  have r1 : rdW (m'.arr64 IW) (q + 1) = kL := by simpa using rq 1 (by decide)
  have r2 : rdW (m'.arr64 IW) (q + 2) = aO := by simpa using rq 2 (by decide)
  have r3 : rdW (m'.arr64 IW) (q + 3) = aL := by simpa using rq 3 (by decide)
  have r4 : rdW (m'.arr64 IW) (q + 4) = nO := by simpa using rq 4 (by decide)
  have r5 : rdW (m'.arr64 IW) (q + 5) = nL := by simpa using rq 5 (by decide)
  refine ⟨?_, by rw [r0, r1]; exact hkb, by rw [r2, r3]; exact hab, by rw [r4, r5]; exact hnb⟩
  show decNS (truncM m') q.toNat = _
  have hk' : decPL (truncM m') (decNK (truncM m')) kO.toNat kL.toNat = some keys := hk
  have ha' : decPL (truncM m') (decNK (truncM m')) aO.toNat aL.toNat = some act := ha
  have hn' : decPL (truncM m') (decNCN (truncM m')) nO.toNat nL.toNat = some nfs := hn
  simp only [decNS, decAt, n0, n1, n2, n3, n4, n5, hk', ha', hn', Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_cont_new_finish`: the group cached when closed, the active list restored -/

/-- The kind word of `.nested (kb != 0)`. -/
def nestedW (kb : Word) : Word := 4 + 8 * (if kb ≠ 0 then 1 else 0)

def cfK3 (kb : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m3) => some ([nestedW kb, q], m3)
def cfK2 (ns2 aO aL kb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => cfK3 kb (posRecW m2 [r.headD 0, r.tail.headD 0, aO, aL, rdW (m2.arr64 IW) (ns2 + 4),
      rdW (m2.arr64 IW) (ns2 + 5)])
def cfK1 (k : Nat) (us dO dL gO gL ns2 aO aL kb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 ≠ 0 then
      cfK2 ns2 aO aL kb (nagW k m1 us dO dL gO gL (rdW (m1.arr64 IW) ns2) (rdW (m1.arr64 IW) (ns2 + 1)))
    else cfK2 ns2 aO aL kb (some ([rdW (m1.arr64 IW) ns2, rdW (m1.arr64 IW) (ns2 + 1)], m1))
/-- The model of `nest_cont_new_finish(ctx, us, dsOff, dsLen, grpOff, grpLen, ns2, actOff, actLen, kb)`. -/
def cfW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, ctx, us, dO, dL, gO, gL, ns2, aO, aL, kb => cfK1 k us dO dL gO gL ns2 aO aL kb (dcWf k m ctx dO dL)

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

theorem nestContNewFinish_spec (p : Prog) (L : NagLook p) (hd : DcLook p) (h6 : p.lookup "rec6" = some rec6)
    (hp : p.lookup "nest_cont_new_finish" = some nestContNewFinishL) (n : Nat) (s₀ : St)
    (ctx us dO dL gO gL ns2 aO aL kb : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new_finish" [ctx, us, dO, dL, gO, gL, ns2, aO, aL, kb]
    ⦃fun r s' => LocEq s' s₀ ∧
      cfW n s₀.mem ctx us dO dL gO gL ns2 aO aL kb = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestContNewFinishL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        dc_spec' p hd.hf hd.hh hd.hg hd.hp n, nestAcceptGroup_spec p L n, rec6_specW p L.ha h6 n] <;>
      finish (gen := 20) (instances := 5000) [cfW, nestedW, rdW_eq]

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

theorem cfW_mfr {k : Nat} {m m' : Mem} {ctx us dO dL gO gL ns2 aO aL kb : Word} {r : List Word}
    (h : cfW k m ctx us dO dL gO gL ns2 aO aL kb = some (r, m')) : MFr [] [] m m' := by
  cases k with
  | zero => simp [cfW] at h
  | succ k =>
  simp only [cfW] at h
  rcases h1 : dcWf k m ctx dO dL with _ | ⟨r1, m1⟩ <;> rw [h1] at h; · simp [cfK1] at h
  refine (dcWf_mfr h1).trans ?_
  simp only [cfK1] at h
  split at h
  · unfold cfK2 cfK3 at h
    mfr_auto h [nagW_mfr _ _ _ _ _ _ _ _ _ _ _, posRecW_mfr]
  · simp only [cfK2] at h
    unfold cfK3 at h
    mfr_auto h [posRecW_mfr]

theorem cfW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {k : Nat} {m m' : Mem} {a : AState}
    {ctx us dO dL gO gL ns2 aO aL kb : Word} {c : NestCtx} {ds : List EIdx} {grp : List (NIdx × EIdx)}
    {NS2 : NestState} {act : List NestKey} {r : List Word}
    (h : cfW k m ctx us dO dL gO gL ns2 aO aL kb = some (r, m')) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hhi : c.hiAt 0 < 2 ^ 64) (hus : H us)
    (hds : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds)
    (hdsb : dO.toNat + dL.toNat ≤ iwTop m)
    (hgl : gL.toNat = grp.length) (hgb : gO.toNat + grp.length ≤ iwTop m) (hgrp : GrpAt m gO.toNat grp)
    (hns : NSB m ns2 NS2) (hact : KsB m aO.toNat aL.toNat act) (hab : aO.toNat + aL.toNat ≤ iwTop m) :
    ∃ x a', (cfT c (decI us) ds grp NS2 act kb.toNat).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ r.headD 0 = nestedW kb ∧ decNFK (r.headD 0) = some x.1 ∧ NSB m' (r.tail.headD 0) x.2 := by
  cases k with
  | zero => simp [cfW] at h
  | succ k =>
  simp only [cfW] at h
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hdsD := hds.get (OMono.decHL _ _)
  rcases hdc : dcWf k m ctx dO dL with _ | ⟨r1, m1⟩ <;> rw [hdc] at h; · simp [cfK1] at h
  obtain ⟨b, a1, hrun1, hS1, hg1, hr1⟩ := dcWf_ok dn fe vis k m m1 a ctx dO dL c ds r1 hdc hS hU.dec hU.inn hhi hdsD
    (fun j hj => by omega)
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  have hns1 := hns.grow hg1 htop
  obtain ⟨hp6, hk1, -, hn1⟩ := nsb_words hns1 htop1
  have hkb1 := hns1.b0
  -- the keys, cached or not
  have hkeys : ∃ (rk : List Word) (mk : Mem), cfK1 k us dO dL gO gL ns2 aO aL kb (some (r1, m1)) =
      cfK2 ns2 aO aL kb (some (rk, mk)) ∧ StageR dn vis fe mk a1 ∧ IWGrow m1 mk ∧
      KsB mk (rk.headD 0).toNat (rk.tail.headD 0).toNat
        (if b then nestAcceptGroup (decI us) ds grp NS2.keys else NS2.keys).toList ∧
      (rk.headD 0).toNat + (rk.tail.headD 0).toNat ≤ iwTop mk := by
    cases b with
    | true =>
      rw [cfK1_acc (h := by rw [hr1]; decide)]
      rcases hag : nagW k m1 us dO dL gO gL (rdW (m1.arr64 IW) ns2) (rdW (m1.arr64 IW) (ns2 + 1)) with _ | ⟨rk, mk⟩; · rw [cfK1_acc (h := by rw [hr1]; decide), hag] at h; simp [cfK2] at h
      obtain ⟨h1, h2, h3, h4⟩ := nagW_ok dn vis fe us dO dL ds hus k m1 mk a1 gO gL _ _ grp NS2.keys rk hag hS1
        (DecB.grow (OMono.decHL _ _) hg1 hds) hgl (by have := hg1.1; omega) (hgrp.grow hgb hg1) hk1 hkb1
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
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have hnk := (hns1.grow hgk htop1)
  obtain ⟨-, -, -, hnk'⟩ := nsb_words hnk (Nat.lt_of_le_of_lt hSk.2.1 hSk.2.2.2.1)
  refine ⟨(.nested (kb.toNat != 0), (NestState.mk (if b then nestAcceptGroup (decI us) ds grp NS2.keys
    else NS2.keys) act NS2.ctorNfs)), a1, ?_, hS3, hg13, rfl, by simpa using decNFK_nestedW kb, ?_⟩
  · simp only [cfT, StateT.run_bind, hrun1, except_ok_bind]; rfl
  · have := nsb_rec6 (m' := m3) (q := q) (keys := (if b then nestAcceptGroup (decI us) ds grp NS2.keys
        else NS2.keys).toList) (act := act) (nfs := NS2.ctorNfs.toList) (by omega) htop3 hget3
      (hksk.grow hg3) (by have := hg3.1; omega) ((hact.grow hg1).grow (hgk.trans hg3))
      (by have := hg13.1; omega) (hnk'.grow hg3) (by have := hnk.b4; have := hg3.1; omega)
    simpa using this

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_pos_hole_kind`, `nest_pos_fvar` -/

/-- The model of `nest_pos_hole_kind(ctx, kb, i)` (memory unchanged). -/
def hkW (m : Mem) (ctx kb i : Word) : Option Word :=
  if i < nhiW m ctx 0 then
    (if 1152921504606846976 ≤ i - rdW (m.arr64 IW) (ctx + 4) then none
     else if kb = 0 then some (1 + 8 * (i - rdW (m.arr64 IW) (ctx + 4)))
     else some (2 + 8 * (i - rdW (m.arr64 IW) (ctx + 4))))
  else some 3

def hkWf : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | _ + 1, m, ctx, kb, i => hkW m ctx kb i

theorem nestPosHoleKind_spec (p : Prog) (hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt)
    (hp : p.lookup "nest_pos_hole_kind" = some nestPosHoleKindL) (n : Nat) (s₀ : St) (ctx kb i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_hole_kind" [ctx, kb, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ hkWf n s₀.mem ctx kb i = some (r.headD 0); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestPosHoleKindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nestCtxHiAt_specE p hh n] <;>
      finish (gen := 20) [hkWf, hkW, rdW_eq, LocEq]

/-- The twin's field kind of a hole `i`. -/
def holeKind (c : NestCtx) (kb i : Nat) : NestFieldKind :=
  if i < c.hiAt 0 then (if kb == 0 then .recursive (i - c.nP) else .reflexive (i - c.nP)) else .inProgress

theorem hkW_ok {m : Mem} {ctx kb i r : Word} {c : NestCtx} (h : hkW m ctx kb i = some r)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (htop : iwTop m < 2 ^ 64)
    (hhi : c.hiAt 0 < 2 ^ 64) (hnP : c.nP ≤ i.toNat) :
    decNFK r = some (holeKind c kb.toNat i.toNat) := by
  have hhw := nhiW_toNat (nf := 0) hc hin htop (by simpa using hhi)
  obtain ⟨-, -, -, -, hP, -⟩ := ctx_fields hc hin htop
  simp only [UInt64.toNat_zero] at hhw
  unfold hkW at h
  have ht : (i - rdW (m.arr64 IW) (ctx + 4)).toNat = i.toNat - c.nP := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hP]
  by_cases hlt : i < nhiW m ctx 0
  · rw [ite_eq_left hlt] at h
    have hlt' : i.toNat < c.hiAt 0 := by have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    by_cases hbig : 1152921504606846976 ≤ i - rdW (m.arr64 IW) (ctx + 4)
    · rw [ite_eq_left hbig] at h; cases h
    rw [ite_eq_right hbig] at h
    have hsmall : i.toNat - c.nP < 1152921504606846976 := by
      have : ¬ (1152921504606846976 : Word).toNat ≤ (i - rdW (m.arr64 IW) (ctx + 4)).toNat :=
        fun e => hbig (UInt64.le_iff_toNat_le.mpr e)
      simp at this; omega
    simp only [holeKind, hlt', ite_true]
    by_cases hkb : kb = 0
    · rw [ite_eq_left hkb] at h; cases h; subst hkb
      have e : (1 + 8 * (i - rdW (m.arr64 IW) (ctx + 4))).toNat = 1 + 8 * (i.toNat - c.nP) := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, ht]; simp; omega
      simp only [decNFK, e]
      have h1 : (1 + 8 * (i.toNat - c.nP)) % 8 = 1 := by omega
      have h2 : (1 + 8 * (i.toNat - c.nP)) / 8 = i.toNat - c.nP := by omega
      simp [h1, h2]
    · rw [ite_eq_right hkb] at h; cases h
      have hkb' : (kb.toNat == 0) = false := by
        simp; intro e; exact hkb (UInt64.toNat_inj.mp (by simpa using e))
      have e : (2 + 8 * (i - rdW (m.arr64 IW) (ctx + 4))).toNat = 2 + 8 * (i.toNat - c.nP) := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, ht]; simp; omega
      simp only [decNFK, e, hkb']
      have h1 : (2 + 8 * (i.toNat - c.nP)) % 8 = 2 := by omega
      have h2 : (2 + 8 * (i.toNat - c.nP)) / 8 = i.toNat - c.nP := by omega
      simp [h1, h2]
  · rw [ite_eq_right hlt] at h; cases h
    have : ¬ i.toNat < c.hiAt 0 := fun e => hlt (UInt64.lt_iff_toNat_lt.mpr (by omega))
    simp [holeKind, this, decNFK]

end L.Ind

namespace L.Ind

open L.Arena

def haWf : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, ctx, po, pl, i => haW k m ctx po pl i

def naWf : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, vis, c => naW k m vis c

def p2pfK3 (k : Nat) (ctx kb i aL dL2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) =>
    if aL + dL2 < aL then none
    else if aL + dL2 ≠ r.headD 0 then none
    else match hkWf k m3 ctx kb i with
      | none => none
      | some w => some ([w], m3)
def p2pfK2 (k : Nat) (vis ctx kb i aL hp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) =>
    if r.headD 0 ≠ 0 then none
    else p2pfK3 k ctx kb i aL (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) hp + 3))
      (naWf k m2 vis (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) hp)))
def p2pfK1 (k : Nat) (vis ctx kb hi i aO aL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then none
    else p2pfK2 k vis ctx kb i aL (r.tail.headD 0) (noaW k m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1))
      (rdW (m1.arr64 IW) (ctx + 4)) hi aO aL)
/-- The model of `nest_pos_fvar(vis, ctx, progOff, progLen, kb, hi, i, argsOff, argsLen)`. -/
def pfW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, po, pl, kb, hi, i, aO, aL => p2pfK1 k vis ctx kb hi i aO aL (haWf k m ctx po pl i)

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (vis ctx kb hi i aO aL hp dL2 : Word) (r : List Word)
theorem p2pfK1_eq : p2pfK1 k vis ctx kb hi i aO aL (some (r, m1)) =
    if r.headD 0 = 0 then none
    else p2pfK2 k vis ctx kb i aL (r.tail.headD 0) (noaW k m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1))
      (rdW (m1.arr64 IW) (ctx + 4)) hi aO aL) := rfl
theorem p2pfK2_eq : p2pfK2 k vis ctx kb i aL hp (some (r, m2)) =
    if r.headD 0 ≠ 0 then none
    else p2pfK3 k ctx kb i aL (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) hp + 3))
      (naWf k m2 vis (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) hp))) := rfl
theorem p2pfK3_eq : p2pfK3 k ctx kb i aL dL2 (some (r, m3)) =
    if aL + dL2 < aL then none
    else if aL + dL2 ≠ r.headD 0 then none
    else match hkWf k m3 ctx kb i with
      | none => none
      | some w => some ([w], m3) := rfl
end arms

/-- The lookups of `nest_pos_fvar`. -/
structure PfLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  h2 : p.lookup "rec2" = some rec2
  h4 : p.lookup "rec4" = some rec4
  hrg : p.lookup "nest_ctx_root_holes_go" = some nestCtxRootHolesGo
  hr : p.lookup "nest_ctx_root_holes" = some nestCtxRootHoles
  hc : p.lookup "iw_copy" = some iwCopy
  hap : p.lookup "sl_append" = some slAppend
  hha : p.lookup "nest_hole_at" = some nestHoleAt
  no : NoLook p
  hoa : p.lookup "nest_occ_any" = some nestOccAnyL
  na : NaLook p
  hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  hk : p.lookup "nest_pos_hole_kind" = some nestPosHoleKindL
  hp : p.lookup "nest_pos_fvar" = some nestPosFvarL

theorem nestHoleAt_spec' (p : Prog) (L : PfLook p) (k : Nat) (s₀ : St) (ctx po pl i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_hole_at" [ctx, po, pl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ haWf k s₀.mem ctx po pl i = some (r, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ L.hha]; simp only [callFn, nestHoleAt]; vcgen [exec] <;> grind
  | succ k => exact nestHoleAt_spec p L.ha L.h2 L.h4 L.hrg L.hr L.hc L.hap L.hha k s₀ ctx po pl i

theorem nestArity_spec' (p : Prog) (hl : NaLook p) (k : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_arity" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ naWf k s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ hl.hp]; simp only [callFn, nestArityL]; vcgen [exec] <;> grind
  | succ k => exact nestArity_spec p hl k s₀ vis c

theorem nestPosFvar_spec (p : Prog) (L : PfLook p) (n : Nat) (s₀ : St) (vis ctx po pl kb hi i aO aL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_fvar" [vis, ctx, po, pl, kb, hi, i, aO, aL]
    ⦃fun r s' => LocEq s' s₀ ∧ pfW n s₀.mem vis ctx po pl kb hi i aO aL = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ L.hp, callFn, nestPosFvarL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestHoleAt_spec' p L n, nestOccAny_spec p L.no L.hoa n, nestArity_spec' p L.na n,
        nestPosHoleKind_spec p L.hh L.hk n] <;>
      finish (gen := 20) (instances := 5000) [pfW, p2pfK1_eq, p2pfK2_eq, p2pfK3_eq, rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

/-- The `.fvar` arm of `nestPos`, its result kind to `K` (the twin's text). -/
def pfK {β : Type} (fe : IFEnv) (ctx : NestCtx) (prog : List NestHole) (kb hi i : Nat) (args : List EIdx)
    (K : NestFieldKind → AM β) : AM β :=
  match ConRon.Arena.nestHoleAt ctx prog i with
  | none => fail nestNonValid
  | some h => do
    if ← args.anyM (fun x => ConRon.Arena.nestOcc ctx.names ctx.nP hi x) then fail nestNonValid
    else do
      let ar ← ConRon.Arena.nestArity fe h.key.cname
      if args.length + h.key.ds.length == ar then K (holeKind ctx kb i) else fail nestNonValid

theorem nestHoleAt_nP {c : NestCtx} {prog : List NestHole} {i : Nat} {h : NestHole}
    (e : ConRon.Arena.nestHoleAt c prog i = some h) : c.nP ≤ i := by
  unfold ConRon.Arena.nestHoleAt at e; split at e
  · assumption
  · cases e

/-- A hole decoded below the top: its key's name and `ds` length as the words L reads. -/
theorem nh_key_words {m : Mem} {p : Word} {hl : NestHole} (hd : decNH m p.toNat = some hl)
    (hin : NHIn m p.toNat (· < iwTop m)) (htop : iwTop m < 2 ^ 64) :
    H (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) ∧ decI (rdW (m.arr64 IW) (rdW (m.arr64 IW) p)) = hl.key.cname ∧
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) p + 3)).toNat = hl.key.ds.length := by
  obtain ⟨k, hk, hK⟩ := decNH_fields hd
  have hkin := hin.2.2 k hk
  have hp0 := hin.1
  have hk0 := hkin.1 0 (by omega)
  have hklt : k < 2 ^ 64 := by omega
  have hk' : (UInt64.ofNat k : Word).toNat = k := UInt64.toNat_ofNat_of_lt' hklt
  have hrd : rdW (m.arr64 IW) p = UInt64.ofNat k := by
    have := rd_iwN (m := m) (p := p) (i := 0) (by simpa using hk) (by simp; omega)
    apply UInt64.toNat_inj.mp; rw [hk']
    simpa using this
  rw [hrd]
  obtain ⟨h0, h1, -, -, h4, -, -⟩ := nk_fields (key := UInt64.ofNat k) (by rw [hk']; exact hK) (by rw [hk']; exact hkin) htop
  exact ⟨h0, h1, by rw [← decHL_length m h4]⟩

theorem pfW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m m' : Mem} {a : AState} {ctx po pl kb hi i aO aL : Word} {c : NestCtx}
    {prog : List NestHole} {args : List EIdx} {r : List Word}
    (h : pfW k m vis ctx po pl kb hi i aO aL = some (r, m')) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hpr : HSl m po.toNat pl.toNat prog) (hhi : c.hiAt 0 < 2 ^ 64)
    (hargs : decHL m aO.toNat aL.toNat = some args) (hab : aO.toNat + aL.toNat ≤ iwTop m) (hP : PosMR m) :
    ∃ x a', (∀ {β : Type} (K : NestFieldKind → AM β),
      (pfK fe c prog kb.toNat hi.toNat i.toNat args K).run a = (K x).run a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decNFK (r.headD 0) = some x ∧ PosMR m' := by
  cases k with
  | zero => simp [pfW] at h
  | succ k =>
  simp only [pfW] at h
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  cases k with
  | zero => simp [haWf, p2pfK1] at h
  | succ k =>
  rcases hha : haWf (k + 1) m ctx po pl i with _ | ⟨r1, m1⟩ <;> rw [hha] at h; · simp [p2pfK1] at h
  rw [p2pfK1_eq] at h
  obtain ⟨hS1, hg1, hon⟩ := haW_ok k dn fe vis a m m1 ctx po pl i r1 c prog (by simpa [haWf] using hha) hS hU.dec
    hU.inn hpr
  cases hnh : ConRon.Arena.nestHoleAt c prog i.toNat with
  | none =>
    rw [hnh] at hon; simp only [decONH] at hon
    rw [ite_eq_left hon] at h; cases h
  | some hl =>
  rw [hnh] at hon
  obtain ⟨hon1, hdec, hnin⟩ := hon
  rw [ite_eq_right (by rw [hon1]; decide)] at h
  have hU1 := hU.grow hg1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨hn1, -, -, -, hnP1, -⟩ := ctx_fields hU1.dec hU1.inn htop1
  have hne1 := ctx_names_end hU1.dec hU1.inn hU1.sl htop1
  rcases hoa : noaW (k + 1) m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1)) (rdW (m1.arr64 IW) (ctx + 4))
      hi aO aL with _ | ⟨r2, m2⟩; · rw [hoa] at h; simp [p2pfK2] at h
  rw [hoa, p2pfK2_eq] at h
  obtain ⟨b, hrunoa, hS2, hg2, hr2, hP2⟩ := noaW_ok dn fe vis _ _ _ _ c.names (k + 1) m1 m2 a _ _ args r2 hoa hS1
    hn1 hne1 (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hargs)
    (fun j hj => by have := hg1.1; omega) (hP.fr (haW_mfr (by simpa [haWf] using hha)))
  rw [hnP1] at hrunoa
  cases b with
  | true => rw [ite_eq_left (by rw [hr2]; decide)] at h; cases h
  | false =>
  rw [ite_eq_right (by rw [hr2]; decide)] at h
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hd2, hnin2⟩ := hnin.grow hg2
  rw [← hd2] at hdec
  obtain ⟨hcH, hcd, hdl⟩ := nh_key_words hdec hnin2 htop2
  rcases hna : naWf (k + 1) m2 vis (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0))) with _ | ⟨r3, m3⟩ <;> rw [hna] at h; · simp [p2pfK3] at h
  rw [p2pfK3_eq] at h
  obtain ⟨ar, a3, hrun3, hS3, hg3, hr3⟩ := naW_ok dn fe vis _ hcH k m2 m3 a r3 (by simpa [naWf] using hna) hS2
  rw [hcd] at hrun3
  have hal := decHL_length m hargs
  by_cases hov : aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3) < aL
  · rw [ite_eq_left hov] at h; cases h
  rw [ite_eq_right hov] at h
  have hsum : (aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat =
      aL.toNat + hl.key.ds.length := by
    rw [← hdl]
    rcases Nat.lt_or_ge (aL.toNat + (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat) (2 ^ 64)
      with hl' | hl'
    · exact word_add_toNat hl'
    · exfalso; apply hov; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
      have := aL.toNat_lt; have := (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat_lt; omega
  by_cases hne : aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3) ≠ r3.headD 0
  · rw [ite_eq_left hne] at h; cases h
  rw [ite_eq_right hne] at h
  have heq : args.length + hl.key.ds.length = ar := by
    rw [hal, ← hsum, ← hr3]; simp only [ne_eq, Decidable.not_not] at hne; rw [hne]
  rcases hk : hkWf (k + 1) m3 ctx kb i with _ | w <;> rw [hk] at h; · cases h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hU3 := (hU1.grow hg2).grow hg3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have hw := hkW_ok (by simpa [hkWf] using hk) hU3.dec hU3.inn htop3 hhi (nestHoleAt_nP hnh)
  refine ⟨holeKind c kb.toNat i.toNat, a3, fun K => ?_, hS3, (hg1.trans hg2).trans hg3, by simpa using hw,
    hP2.fr (naW_mfr (by simpa [naWf] using hna))⟩
  simp only [pfK, hnh, StateT.run_bind, hrunoa, except_ok_bind, Bool.false_eq_true, ite_false, hrun3, heq,
    beq_self_eq_true, ite_true]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_ctors_u4`: a non-ordinary field read later -/

def ustWf : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | n + 2, m, cty, nP, j => ustW n m cty nP j
  | _, _, _, _, _ => none

mutual
def u4W : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, ko, nF, cl, i =>
    if nF ≤ i then some ([0], m)
    else if rdW (m.arr64 IW) (ko + i) ≠ 0 then u4K n ko nF cl i (ustWf n m cl 0 i)
    else u4W n m ko nF cl (i + 1)
def u4K (n : Nat) (ko nF cl i : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (su, m1) => if su ≠ 0 then some ([1], m1) else u4W n m1 ko nF cl (i + 1)
end

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

/-- The lookups of `struct_used_later`. -/
structure UslLook (p : Prog) : Prop where
  hv : p.lookup "e_view" = some eView
  hf : p.lookup "hb_find" = some (memoFindG hbSch)
  hput : p.lookup "hb_put" = some (memoPutG hbSch)
  hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL
  hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL
  hbp : BvbProg p
  hst : StripProg p
  hcl : p.lookup "hb_clear" = some (memoClearG hbSch)
  hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL
  hp : p.lookup "struct_used_later" = some structUsedLaterL

theorem structUsedLater_spec' (p : Prog) (L : UslLook p) (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ ustWf n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  match n with
  | 0 => rw [invoke_eq _ L.hp]; simp only [callFn, structUsedLaterL]; vcgen [exec] <;> grind
  | 1 =>
    rw [invoke_eq _ L.hp]; simp only [callFn, structUsedLaterL]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> grind
  | n + 2 => exact structUsedLater_spec p L.hv L.hf L.hput L.hins L.hgo L.hbp L.hst L.hcl L.hfast L.hp n s₀ cty nP j

theorem nestCtorsU4_spec (p : Prog) (L : UslLook p) (hp : p.lookup "nest_ctors_u4" = some nestCtorsU4L)
    (n : Nat) : ∀ (s₀ : St) (ko nF cl i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_u4" [ko, nF, cl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ u4W n s₀.mem ko nF cl i = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ko nF cl i
    rw [invoke_eq _ hp]; simp only [callFn, nestCtorsU4L]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ko nF cl i
    simp only [invoke_eq _ hp, callFn, nestCtorsU4L]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, structUsedLater_spec' p L n, ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

/-- The twin's U4 test at field `i`. -/
def u4F (ks : List NestFieldKind) (closed : EIdx) (i : Nat) : AM Bool :=
  if (ks[i]?.map (· == .ordinary)).getD true then pure false else structUsedLater closed 0 i

theorem decKL_get {m : Mem} {o l : Nat} {ks : List NestFieldKind} (h : decKL m o l = some ks) :
    ks.length = l ∧ ∀ j (_hj : j < l), ∃ w, (iwA m)[o + j]? = some w ∧ decNFK w = ks[j]? := by
  induction l generalizing o ks with
  | zero => simp [decKL] at h; subst h; simp
  | succ l ih =>
    simp only [decKL_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, hw, x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hxs
    refine ⟨by simp [h1], fun j hj => ?_⟩
    cases j with
    | zero => exact ⟨w, by simpa using hw, by simpa using hx⟩
    | succ j =>
      obtain ⟨w', hw', hx'⟩ := h2 j (by omega)
      exact ⟨w', by rw [show o + (j + 1) = o + 1 + j by omega]; exact hw', by simpa using hx'⟩

theorem decNFK_ordinary {w : Word} {x : NestFieldKind} (h : decNFK w = some x) :
    (x == .ordinary) = (w == 0) := by
  by_cases hw : w = 0
  · subst hw; simp [decNFK] at h; subst h; rfl
  · have hw' : (w == 0) = false := by simpa using hw
    rw [hw']
    simp only [decNFK] at h
    split at h <;> rename_i ht
    · split at h
      · exfalso; apply hw; apply UInt64.toNat_inj.mp; simp; omega
      · cases h
    all_goals first
      | (simp only [Option.some.injEq] at h; subst h; exact beq_eq_false_iff_ne.mpr (by intro e; cases e))
      | (split at h
         · simp only [Option.some.injEq] at h; subst h; exact beq_eq_false_iff_ne.mpr (by intro e; cases e)
         · cases h)
      | (cases h; done)

theorem u4W_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {m0 : Mem} (ko nF cl : Word) (ks : List NestFieldKind) (hcl : H cl)
    (hks : decKL (truncM m0) ko.toNat nF.toNat = some ks) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (i : Word) (r : List Word),
    u4W n m ko nF cl i = some (r, m') → StageR dn vis fe m a → IWGrow m0 m → i.toNat ≤ nF.toNat → PosMR m →
    ∃ b a', ((List.range' i.toNat (nF.toNat - i.toNat)).anyM (u4F ks (decI cl))).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' := by
  intro n
  obtain ⟨hkl, hkw⟩ := decKL_get hks
  induction n with
  | zero => intro m m' a i r h; simp [u4W] at h
  | succ n ih =>
    intro m m' a i r h hS hg0 hi hP
    by_cases hd : nF ≤ i
    · rw [u4W_done (h := hd)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : nF.toNat - i.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hd; omega
      rw [this]; exact ⟨false, a, rfl, hS, IWGrow.refl _, rfl, hP⟩
    have hlt : i.toNat < nF.toNat := by
      have : ¬ nF.toNat ≤ i.toNat := fun e => hd (UInt64.le_iff_toNat_le.mpr e); omega
    obtain ⟨w, hw, hx⟩ := hkw i.toNat hlt
    obtain ⟨hwi, hw'⟩ := truncM_iw_get hw
    have hrd : rdW (m.arr64 IW) (ko + i) = w := by
      have e : (ko + i).toNat = ko.toNat + i.toNat := word_add_toNat (by
        have := hS.2.1; have := hS.2.2.2.1; have := hg0.1; omega)
      simp only [rdW, e]; simp only [iwA] at hw'; rw [hg0.2.2.1 _ hwi, hw']; rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := word_add_toNat (by have := nF.toNat_lt; simp; omega)
    have hrange : List.range' i.toNat (nF.toNat - i.toNat) =
        i.toNat :: List.range' (i + 1).toNat (nF.toNat - (i + 1).toNat) := by
      rw [hi1, show nF.toNat - i.toNat = (nF.toNat - (i.toNat + 1)) + 1 by omega, List.range'_succ]
    rw [hrange, List.anyM_cons]
    have hord : ((ks[i.toNat]?.map (· == .ordinary)).getD true) = (w == 0) := by
      rw [List.getElem?_eq_getElem (by omega)] at hx ⊢
      simp only [Option.map_some, Option.getD_some]
      exact decNFK_ordinary hx
    by_cases hk : rdW (m.arr64 IW) (ko + i) ≠ 0
    · rw [u4W_kind (h := hd) (hk := hk)] at h
      have hw0 : (w == 0) = false := by rw [← hrd]; simpa using hk
      cases n with
      | zero => simp [ustWf, u4K] at h
      | succ n =>
      cases n with
      | zero => simp [ustWf, u4K] at h
      | succ n =>
      rcases hu : ustW n m cl 0 i with _ | ⟨su, m1⟩; · simp only [ustWf] at h; rw [hu] at h; simp [u4K] at h
      simp only [ustWf] at h; rw [hu] at h
      obtain ⟨mp, hmp⟩ := hP.hb
      obtain ⟨b1, a1, hrun1, hsu, hM1, hS1, hg1⟩ := ustW_ok n m m1 a cl 0 i su mp
        (by have := nF.toNat_lt; simp; omega) hcl hS hmp hu
      have hP1 := hP.setHb (ustW_mfr hu) hM1
      by_cases hs : su ≠ 0
      · rw [u4K_hit (h := hs)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hb1 : b1 = true := by cases b1 <;> simp_all
        subst hb1
        refine ⟨true, a1, ?_, hS1, hg1, rfl, hP1⟩
        simp only [u4F, hord, hw0, Bool.false_eq_true, ite_false, StateT.run_bind]
        simp only [UInt64.toNat_zero] at hrun1
        rw [hrun1]; rfl
      · rw [u4K_miss (h := hs)] at h
        have hb1 : b1 = false := by cases b1 <;> simp_all
        subst hb1
        obtain ⟨b, a', hrun, hS', hg', hr, hP'⟩ := ih m1 m' a1 (i + 1) r h hS1 (hg0.trans hg1)
          (by rw [hi1]; omega) hP1
        refine ⟨b, a', ?_, hS', hg1.trans hg', hr, hP'⟩
        simp only [u4F, hord, hw0, Bool.false_eq_true, ite_false, StateT.run_bind]
        simp only [UInt64.toNat_zero] at hrun1
        rw [hrun1, except_ok_bind]; simpa using hrun
    · rw [u4W_ord (h := hd) (hk := hk)] at h
      have hw0 : (w == 0) = true := by rw [← hrd]; simpa using hk
      obtain ⟨b, a', hrun, hS', hg', hr, hP'⟩ := ih m m' a (i + 1) r h hS hg0 (by rw [hi1]; omega) hP
      refine ⟨b, a', ?_, hS', hg', hr, hP'⟩
      simp only [u4F, hord, hw0, ite_true, StateT.run_bind]
      simpa using hrun

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_ctors_res_ok`: the result headed by a hole, hole-free indices -/

def roK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([if r.headD 0 = 0 then 1 else 0], m3)
def roK1 (k : Nat) (ctx hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => roK2 (noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      (rdW (m2.arr64 IW) (ctx + 4)) hi (r.headD 0) (r.tail.headD 0))
def roK0 (k : Nat) (ctx hi cur : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then some ([0], m1) else roK1 k ctx hi (gaaF m1 [CWF, cur])
/-- The model of `nest_ctors_res_ok(ctx, hi, cur)`. -/
def roW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, ctx, hi, cur => roK0 k ctx hi cur (resHeadW m cur)

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (ctx hi cur : Word) (r : List Word)
theorem roK2_some : roK2 (some (r, m3)) = some ([if r.headD 0 = 0 then 1 else 0], m3) := rfl
theorem roK1_some : roK1 k ctx hi (some (r, m2)) = roK2 (noaW k m2 (rdW (m2.arr64 IW) ctx)
    (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi (r.headD 0) (r.tail.headD 0)) := rfl
theorem roK0_eq : roK0 k ctx hi cur (some (r, m1)) =
    if r.headD 0 = 0 then some ([0], m1) else roK1 k ctx hi (gaaF m1 [CWF, cur]) := rfl
end arms
attribute [ind_grind] roK2_some roK1_some

theorem nestCtorsResOk_spec (p : Prog) (hl : NoLook p) (hoa : p.lookup "nest_occ_any" = some nestOccAnyL)
    (hrh : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p)
    (hp : p.lookup "nest_ctors_res_ok" = some nestCtorsResOkL) (n : Nat) (s₀ : St) (ctx hi cur : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_res_ok" [ctx, hi, cur]
    ⦃fun r s' => LocEq s' s₀ ∧ roW n s₀.mem ctx hi cur = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorsResOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestResHead_spec p hrh had n, gaaF_spec p had n, nestOccAny_spec p hl hoa n] <;>
      finish (gen := 20) [roW, roK0_eq, rdW_eq]

/-- The twin's result check of `nestCtors`, the rest to `K` (the twin's text). -/
def roK {β : Type} (c : NestCtx) (hi : Nat) (cur : EIdx) (K : Bool → AM β) : AM β := do
  let resOk ← do
    if ← nestResHead cur then do
      let args ← getAppArgs coreWalkFuel cur
      let occ ← args.anyM fun x => ConRon.Arena.nestOcc c.names c.nP hi x
      pure !occ
    else pure false
  K resOk

theorem roW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m m' : Mem} {a : AState} {ctx hi cur : Word} {c : NestCtx} {r : List Word}
    (h : roW k m ctx hi cur = some (r, m')) (hS : StageR dn vis fe m a) (hU : UCtx dn vis fe m ctx c)
    (hcur : H cur) (hP : PosMR m) :
    ∃ b a', (∀ {β : Type} (K : Bool → AM β), (roK c hi.toNat (decI cur) K).run a = (K b).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' := by
  cases k with
  | zero => simp [roW] at h
  | succ k =>
  simp only [roW] at h
  rcases hrh : resHeadW m cur with _ | ⟨r1, m1⟩ <;> rw [hrh] at h; · simp [roK0] at h
  rw [roK0_eq] at h
  obtain ⟨a1, hrun1, hS1, hg1⟩ := resHeadW_ok dn fe vis m m1 a cur r1 hcur hrh hS
  by_cases h0 : r1.headD 0 = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨false, a1, fun K => ?_, hS1, hg1, rfl, hP.fr (resHeadW_mfr hrh)⟩
    simp only [roK, StateT.run_bind, hrun1, except_ok_bind, h0, bne_self_eq_false, Bool.false_eq_true, ite_false]
    rfl
  rw [ite_eq_right h0] at h
  have hne : (r1.headD 0 != 0) = true := by simpa using h0
  rcases hga : gaaF m1 [CWF, cur] with _ | ⟨r2, m2⟩ <;> rw [hga] at h; · simp [roK1] at h
  rw [roK1_some] at h
  obtain ⟨args, a2, hrun2, hS2, hg2, hargs⟩ := gaaF_ok dn vis fe CWF cur hcur m1 m2 a1 r2 hga hS1
  rw [CWF_eq] at hrun2
  have hU2 := (hU.grow hg1).grow hg2
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hU2.dec hU2.inn htop2
  have hne2 := ctx_names_end hU2.dec hU2.inn hU2.sl htop2
  obtain ⟨hdA, hbA⟩ := hargs
  have e0 : r2.getD 0 0 = r2.headD 0 := by cases r2 <;> rfl
  have e1 : r2.getD 1 0 = r2.tail.headD 0 := by rcases r2 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  rw [e0, e1] at hdA hbA
  rcases hoa : noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
      (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩; · rw [hoa] at h; simp [roK2] at h
  rw [hoa, roK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨b, hrunoa, hS3, hg3, hr3, hP3⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m2 m3 a2 _ _ args r3 hoa hS2
    hn2 hne2 hdA (fun j hj => by omega) ((hP.fr (resHeadW_mfr hrh)).fr (MFr.ofGaaF hga))
  rw [hnP2] at hrunoa
  refine ⟨!b, a2, ?_, hS3, (hg1.trans hg2).trans hg3, ?_, hP3⟩
  · intro β K; simp only [roK, StateT.run_bind, hrun1, except_ok_bind, hne, ite_true, hrun2, hrunoa]; rfl
  · rw [hr3]; cases b <;> rfl

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

/-- `nest_crest` at any exec fuel (below `3` it never returns). -/
def pcrWf : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | k + 3, m, no, nl, us, dO, dL, hO, hL, cty => pcrW k m no nl us dO dL hO hL cty
  | _, _, _, _, _, _, _, _, _, _ => none

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

/-! ## `nest_ctors_crest`: the group abstracted, typed at the frame's context -/

def p2ctK4 (cR : CallM) (k : Nat) (vis hi : Word) (crest : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) => match cR k "ensure_sort_core" [vis, hi, r.headD 0] m4 with
    | none => none
    | some (_, m5) => some ([crest], m5)
def p2ctK3 (cR : CallM) (k : Nat) (vis hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) =>
    if r.headD 0 = 0 then none
    else p2ctK4 cR k vis hi (r.tail.headD 0) (cR k "infer_type_core" [vis, hi, r.tail.headD 0] m3)
def p2ctK2 (cR : CallM) (k : Nat) (vis no nl us dO dL hO hL hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => p2ctK3 cR k vis hi (pcrWf k m2 no nl us dO dL hO hL (r.headD 0))
def p2ctK1 (cR : CallM) (k : Nat) (vis no nl us dO dL hO hL cv hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    match nodupW k m1 (r.headD 0) (r.tail.headD 0) with
    | none => none
    | some b => if b = 0 then none
      else p2ctK2 cR k vis no nl us dO dL hO hL hi (cR k "inst_lp_fast" [CWF, r.headD 0, r.tail.headD 0, us,
        rdW (m1.arr64 EREC) (cv + 3)] m1)
/-- The model of `nest_ctors_crest(vis, namesOff, namesLen, us, dsOff, dsLen, holesOff, holesLen, cv, hi)`. -/
def p2ctW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, no, nl, us, dO, dL, hO, hL, cv, hi => p2ctK1 cR k vis no nl us dO dL hO hL cv hi (cvLpsW k m cv)

section arms
variable (cR : CallM) (k : Nat) (m1 m2 m3 m4 : Mem) (vis no nl us dO dL hO hL cv hi crest : Word) (r : List Word)
theorem p2ctK4_eq : p2ctK4 cR k vis hi crest (some (r, m4)) = match cR k "ensure_sort_core" [vis, hi, r.headD 0] m4 with
    | none => none
    | some (_, m5) => some ([crest], m5) := rfl
theorem p2ctK3_eq : p2ctK3 cR k vis hi (some (r, m3)) = if r.headD 0 = 0 then none
    else p2ctK4 cR k vis hi (r.tail.headD 0) (cR k "infer_type_core" [vis, hi, r.tail.headD 0] m3) := rfl
theorem p2ctK2_some : p2ctK2 cR k vis no nl us dO dL hO hL hi (some (r, m2)) =
    p2ctK3 cR k vis hi (pcrWf k m2 no nl us dO dL hO hL (r.headD 0)) := rfl
theorem p2ctK1_eq : p2ctK1 cR k vis no nl us dO dL hO hL cv hi (some (r, m1)) =
    match nodupW k m1 (r.headD 0) (r.tail.headD 0) with
    | none => none
    | some b => if b = 0 then none
      else p2ctK2 cR k vis no nl us dO dL hO hL hi (cR k "inst_lp_fast" [CWF, r.headD 0, r.tail.headD 0, us,
        rdW (m1.arr64 EREC) (cv + 3)] m1) := rfl
end arms
attribute [ind_grind] p2ctK2_some

/-- The lookups of `nest_ctors_crest`. -/
structure CtLook (p : Prog) : Prop where
  cr : CrLook p
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "er_copy" = some erCopy
  he : p.lookup "er_to_iw" = some erToIw
  hcv : p.lookup "cv_lps" = some cvLps
  hsc : p.lookup "sl_contains" = some slContains
  hnd : p.lookup "sl_nodup" = some slNodup
  hp : p.lookup "nest_ctors_crest" = some nestCtorsCrestL

theorem nestCtorsCrest_spec (p : Prog) (L : CtLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis no nl us dO dL hO hL cv hi : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_crest" [vis, no, nl, us, dO, dL, hO, hL, cv, hi]
    ⦃fun r s' => LocEq s' s₀ ∧ p2ctW cR n s₀.mem vis no nl us dO dL hO hL cv hi = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ L.hp, callFn, nestCtorsCrestL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        cvLps_spec p L.ha L.hc L.he L.hcv n, slNodup_spec p L.hsc L.hnd n, hcR n "inst_lp_fast",
        nestCrest_spec' p L.cr n, hcR n "infer_type_core", hcR n "ensure_sort_core"] <;>
      finish (gen := 20) (instances := 5000) [p2ctW, p2ctK1_eq, p2ctK3_eq, p2ctK4_eq, rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

end L.Ind
