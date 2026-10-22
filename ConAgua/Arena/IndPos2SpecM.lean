import ConAgua.Arena.IndPos2SpecL

/-! # `IndPos2`, the `nestPos` block's leaves, continued (lane `indproofs2`, helper `pos2`): the
walk's state record (`NestState`, decoded below the tops), `nest_cont_new_finish`. -/

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
  rw [cfK1, if_pos h]
theorem cfK1_open (h : ¬ r.headD 0 ≠ 0) : cfK1 k us dO dL gO gL ns2 aO aL kb (some (r, m1)) =
    cfK2 ns2 aO aL kb (some ([rdW (m1.arr64 IW) ns2, rdW (m1.arr64 IW) (ns2 + 1)], m1)) := by
  rw [cfK1, if_neg h]
end arms
attribute [ind_grind] cfK3_some cfK2_some cfK1_acc cfK1_open

theorem nestContNewFinish_spec (p : Prog) (L : NagLook p) (hd : DcLook p) (h6 : p.lookup "rec6" = some rec6)
    (hp : p.lookup "nest_cont_new_finish" = some nestContNewFinishL) (n : Nat) (s₀ : St)
    (ctx us dO dL gO gL ns2 aO aL kb : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new_finish" [ctx, us, dO, dL, gO, gL, ns2, aO, aL, kb]
    ⦃fun r s' => LocEq s' s₀ ∧
      cfW n s₀.mem ctx us dO dL gO gL ns2 aO aL kb = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestContNewFinishL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        dc_spec' p hd.hh hd.hg hd.hp n, nestAcceptGroup_spec p L n, rec6_specW p L.ha h6 n] <;>
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
    simp only [nestedW, h, ne_eq, not_false_eq_true, if_true]
    simp [decNFK, this]

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
  cases hdc : dcWf k m ctx dO dL with
  | none => rw [hdc] at h; simp [cfK1] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  rw [hdc] at h
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
      cases hag : nagW k m1 us dO dL gO gL (rdW (m1.arr64 IW) ns2) (rdW (m1.arr64 IW) (ns2 + 1)) with
      | none => rw [cfK1_acc (h := by rw [hr1]; decide), hag] at h; simp [cfK2] at h
      | some pr2 =>
      obtain ⟨rk, mk⟩ := pr2
      obtain ⟨h1, h2, h3, h4⟩ := nagW_ok dn vis fe us dO dL ds hus k m1 mk a1 gO gL _ _ grp NS2.keys rk hag hS1
        (DecB.grow (OMono.decHL _ _) hg1 hds) hgl (by have := hg1.1; omega) (hgrp.grow hgb hg1) hk1 hkb1
      exact ⟨rk, mk, rfl, h1, h2, by simpa using h3, h4⟩
    | false =>
      rw [cfK1_open (h := by rw [hr1]; decide)]
      exact ⟨_, m1, rfl, hS1, IWGrow.refl _, by simpa using hk1, by simpa using hkb1⟩
  obtain ⟨rk, mk, hk, hSk, hgk, hksk, hkbk⟩ := hkeys
  rw [hk, cfK2_some] at h
  cases hq : posRecW mk [rk.headD 0, rk.tail.headD 0, aO, aL, rdW (mk.arr64 IW) (ns2 + 4),
      rdW (mk.arr64 IW) (ns2 + 5)] with
  | none => rw [hq] at h; simp [cfK3] at h
  | some pr3 =>
  obtain ⟨q, m3⟩ := pr3
  rw [hq, cfK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
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
