import ConAgua.Arena.RecCheckSpec15

/-!
# `RecCheck`: `targetK53`, the relational side (lane `indproofs3`, helper `rec`)

The twin split at the L functions' boundaries (`tkTele`, `tkHeads`, `tkArgs`, verbatim pieces of
`targetK53`; `tk53_eq` puts them back together), each simulated by its word model.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The twin's pieces -/

/-- `targetK53`'s argument check. -/
def tkArgs (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx) (Mc : TargetMajor) (I' : NIdx)
    (us' : LsIdx) (la ma : List EIdx) : AM Bool := do
  let le ← (la.drop Mc.nPc).mapM ConRon.Arena.eraseFVarTys
  let me ← (ma.drop Mc.nPc).mapM ConRon.Arena.eraseFVarTys
  if le != me then pure false
  else
    let lp := la.take Mc.nPc
    let hd ← ConRon.Arena.internConstE I' us'
    let app ← ConRon.Arena.mkAppN hd lp
    if ← ConRon.Arena.nestOcc p.memberNames 0 0 app then
      ConRon.Arena.targetClassMatch V fe p formerTys Mc.pfvs Mc.lvls Mc.ds us' lp
    else pure false

/-- `targetK53`'s head check. -/
def tkHeads (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx) (Mc : TargetMajor) (leafW majDom : EIdx) :
    AM Bool := do
  let lh ← ConRon.Arena.getAppFn coreWalkFuel leafW
  let mh ← ConRon.Arena.getAppFn coreWalkFuel majDom
  if lh.tag == ETag.const && mh.tag == ETag.const then
    match ← ConRon.Arena.viewConst lh with
    | none => failDanglingE
    | some (I', us') =>
      match ← ConRon.Arena.viewConst mh with
      | none => failDanglingE
      | some (I, _) => do
        let la ← ConRon.Arena.getAppArgs coreWalkFuel leafW
        let ma ← ConRon.Arena.getAppArgs coreWalkFuel majDom
        if !(I' == I && la.length == ma.length) then pure false
        else tkArgs fe p formerTys Mc I' us' la ma
  else pure false

/-- `targetK53`'s telescope check. -/
def tkTele (teleW tele : List EIdx) : AM Bool := do
  let ew ← teleW.mapM fun b => ConRon.Arena.eraseFVarTys b
  let et ← tele.mapM fun b => ConRon.Arena.eraseFVarTys b
  pure (ew == et)

theorem tk53_eq (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx) (Mc : TargetMajor)
    (tele : List EIdx) (majDom f : EIdx) :
    ConRon.Arena.targetK53 V fe p formerTys Mc tele majDom f = (do
      match ← ConRon.Arena.stripPis tele.length f with
      | none => pure false
      | some (teleW, leafW) => do
        let c ← tkTele teleW tele
        if c then tkHeads fe p formerTys Mc leafW majDom else pure false) := by
  rw [ConRon.Arena.targetK53]
  apply bind_congr; intro o
  rcases o with _ | ⟨teleW, leafW⟩
  · rfl
  · simp only [tkTele, bind_assoc, pure_bind]
    apply bind_congr; intro ew; apply bind_congr; intro et
    by_cases h : ew = et
    · subst h; simp only [bne_self_eq_false, beq_self_eq_true, Bool.false_eq_true, if_false, if_true]; rfl
    · have h1 : (ew != et) = true := by simpa using h
      have h2 : (ew == et) = false := by simpa using h
      simp only [h1, h2, if_true, Bool.false_eq_true, if_false]

/-! ## `erase_each`, `target_k53_tele` simulated -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem eftF_ok (n : Nat) {m m' : Mem} {a : AState} {e : Word} {r : List Word}
    (h : eftF n m e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.eraseFVarTys (decE e)).run a = .ok (decE (r.headD 0), a') ∧ H (r.headD 0) ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => simp [eftF] at h
  | succ n => exact eftW_ok dn fe vis n h hS he hP

theorem eeW_ok (n : Nat) : ∀ {m m' : Mem} {a : AState} {o l : Word} {r : List Word} {xs : List EIdx},
    eeW n m o l = some (r, m') → StageR dn vis fe m a → HSl0 m o l xs → RcMR m →
    ∃ ys a', (xs.mapM fun b => ConRon.Arena.eraseFVarTys b).run a = .ok (ys, a') ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ys ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  induction n with
  | zero => intro m m' a o l r xs h; simp [eeW] at h
  | succ n ih =>
  intro m m' a o l r xs h hS hxs hP
  by_cases hl : l = 0
  · rw [eeW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : xs = [] := by have := hxs.len; simpa using this
    subst this
    exact ⟨[], a, rfl, by simp [decHL, hslice?], by simp, hS, IWGrow.refl _, hP⟩
  rw [eeW_cons (h := hl)] at h
  have hb : o.toNat + l.toNat ≤ iwTop m := hxs.2.resolve_left hl
  obtain ⟨w, xs', rfl, ew, hw, hxs'⟩ := decHL_cons hxs.1 hl (hS.lt64 hb)
  obtain ⟨eo, el, hl0⟩ := slice_step hl (hS.lt64 hb)
  rw [ew] at h
  cases h1 : eftF n m w with
  | none => rw [h1] at h; simp [eeK0] at h
  | some x =>
  obtain ⟨rv, m1⟩ := x
  rw [h1, eeK0_some] at h
  obtain ⟨a1, run1, hv, hS1, hg1, hP1⟩ := eftF_ok dn fe vis n h1 hS hw hP
  cases h2 : eeW n m1 (o + 1) (l - 1) with
  | none => rw [h2] at h; simp [eeK1] at h
  | some x =>
  obtain ⟨rr, m2⟩ := x
  rw [h2, eeK1_some] at h
  obtain ⟨ys, a2, run2, hd2, hb2, hS2, hg2, hP2⟩ := ih h2 hS1
    (HSl0.of (by rw [decHL_grow hg1 (by rw [eo, el]; omega)]; exact hxs') (by rw [eo, el]; have := hg1.1; omega)) hP1
  cases h3 : consW n m2 (rv.headD 0) (rr.headD 0) (rr.tail.headD 0) with
  | none => rw [h3] at h; simp [eeK2] at h
  | some x =>
  obtain ⟨rc, m3⟩ := x
  rw [h3, eeK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hv hd2
  have hf3 := (consW_dec h3 hS2.2.2.2.1 hS2.2.2.2.2.2 hb2 hv hd2).2.2.2.1
  refine ⟨decE (rv.headD 0) :: ys, a2, ?_, by rw [decE_eq]; simpa using hd3, Nat.le_of_eq ht3, hS3, (hg1.trans hg2).trans hg3,
    hP2.fr (MFr.of_iw hf3)⟩
  rw [List.mapM_cons]
  simp only [StateT.run_bind, ← decE_eq, run1, except_ok_bind, run2]
  rfl

/-- Word-slice equality of two decoded handle slices is the lists' equality. -/
theorem eqW_dec {n : Nat} {m : Mem} {o1 l1 o2 l2 e : Word} {xs1 xs2 : List EIdx}
    (h : eqW n m o1 l1 o2 l2 = some e)
    (h1 : decHL m o1.toNat l1.toNat = some xs1) (hb1 : o1.toNat + l1.toNat < 2 ^ 64)
    (h2 : decHL m o2.toNat l2.toNat = some xs2) (hb2 : o2.toNat + l2.toNat < 2 ^ 64) :
    e = if xs1 = xs2 then 1 else 0 := by
  obtain ⟨ws1, s1, e1, hw1⟩ := slR_of_decHL m _ _ _ h1 hb1
  obtain ⟨ws2, s2, e2, hw2⟩ := slR_of_decHL m _ _ _ h2 hb2
  simp only [UInt64.ofNat_toNat] at s1 s2
  rw [eqW_ok n m o1 l1 o2 l2 e ws1 ws2 s1 s2 h, e1, e2]
  have : ws1 = ws2 ↔ ws1.map (fun w => (decI w : EIdx)) = ws2.map decI := by
    constructor
    · intro h; rw [h]
    · intro h
      apply List.ext_getElem
      · simpa using congrArg List.length h
      · intro i hi1 hi2
        have := congrArg (·[i]?) h
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2,
          Option.map_some, Option.some.injEq] at this
        exact decE_inj _ _ (hw1 _ (List.getElem_mem hi1)) (hw2 _ (List.getElem_mem hi2)) this
  by_cases hq : ws1 = ws2
  · simp [hq]
  · rw [if_neg hq, if_neg (fun h => hq (this.mpr h))]

theorem tteW_ok (n : Nat) {m m' : Mem} {a : AState} {bso bsl teo tel : Word} {r : List Word}
    {bs tele : List EIdx} (h : tteW n m bso bsl teo tel = some (r, m')) (hS : StageR dn vis fe m a)
    (hbs : HSl0 m bso bsl bs) (htl : HSl0 m teo tel tele) (hP : RcMR m) :
    ∃ c a', (tkTele bs tele).run a = .ok (c, a') ∧ (r.headD 0 != 0) = c ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => simp [tteW] at h
  | succ n =>
  rw [tteW_succ] at h
  cases h1 : eeW n m bso bsl with
  | none => rw [h1] at h; simp [tteK1] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1, tteK1_some] at h
  obtain ⟨ys1, a1, run1, hd1, hb1, hS1, hg1, hP1⟩ := eeW_ok dn fe vis n h1 hS hbs hP
  cases h2 : eeW n m1 teo tel with
  | none => rw [h2] at h; simp [tteK2] at h
  | some x =>
  obtain ⟨r2, m2⟩ := x
  rw [h2, tteK2_some] at h
  obtain ⟨ys2, a2, run2, hd2, hb2, hS2, hg2, hP2⟩ := eeW_ok dn fe vis n h2 hS1 (htl.grow hg1) hP1
  cases h3 : eqW n m2 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) with
  | none => rw [h3] at h; simp [tteK3] at h
  | some e =>
  rw [h3, tteK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have he := eqW_dec h3 (by rw [decHL_grow hg2 hb1]; exact hd1) (hS2.lt64 (by have := hg2.1; omega))
    hd2 (hS2.lt64 hb2)
  refine ⟨ys1 == ys2, a2, ?_, ?_, hS2, hg1.trans hg2, hP2⟩
  · simp only [tkTele, StateT.run_bind, run1, except_ok_bind, run2]; rfl
  · rw [he]; by_cases hq : ys1 = ys2 <;> simp [hq]

end rel

/-! ## Slices: `drop`, `take`; a `TargetMajor`'s fields -/

theorem HSl0.drop {k' : IdxKind} {m : Mem} {o l k : Word} {xs : List (Idx k')} (h : HSl0 m o l xs) :
    HSl0 m (if l < k then o else o + k) (if l < k then 0 else l - k) (xs.drop k.toNat) := by
  have hlen := h.len
  by_cases hlk : l < k
  · simp only [hlk, if_true]
    have : xs.drop k.toNat = [] := List.drop_eq_nil_of_le (by rw [hlen]; exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlk))
    rw [this]; exact ⟨by simp [decHL, hslice?], .inl rfl⟩
  · simp only [hlk, if_false]
    have hkl : k.toNat ≤ l.toNat := by
      have := UInt64.lt_iff_toNat_lt (a := l) (b := k); simp only [hlk, false_iff] at this; omega
    have hsub : (l - k).toNat = l.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hkl)
    by_cases h0 : l - k = 0
    · have : xs.drop k.toNat = [] := List.drop_eq_nil_of_le (by
        have := congrArg UInt64.toNat h0; rw [hsub] at this; simp at this; omega)
      rw [this, h0]; exact ⟨by simp [decHL, hslice?], .inl rfl⟩
    · have hl0 : l ≠ 0 := by intro e; apply h0; apply UInt64.toNat_inj.mp; rw [hsub]; subst e; simp
      have hb := h.2.resolve_left hl0
      have hok : (o + k).toNat = o.toNat + k.toNat := by
        rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt
        have ht : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
        omega
      refine HSl0.of ?_ (by rw [hok, hsub]; omega)
      rw [hok, hsub]; exact decHL_drop k.toNat h.1 hkl

theorem HSl0.take {k' : IdxKind} {m : Mem} {o l k : Word} {xs : List (Idx k')} (h : HSl0 m o l xs) :
    HSl0 m o (if l < k then l else k) (xs.take k.toNat) := by
  have hlen := h.len
  by_cases hlk : l < k
  · simp only [hlk, if_true]
    rw [List.take_of_length_le (by rw [hlen]; exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlk))]; exact h
  · simp only [hlk, if_false]
    have hkl : k.toNat ≤ l.toNat := by
      have := UInt64.lt_iff_toNat_lt (a := l) (b := k); simp only [hlk, false_iff] at this; omega
    refine ⟨decHL_take h.1 _ hkl, ?_⟩
    by_cases hk0 : k = 0
    · exact .inl hk0
    · have hl0 : l ≠ 0 := by intro e; subst e; apply hk0; apply UInt64.toNat_inj.mp; simp at hkl; simp [hkl]
      exact .inr (Nat.le_trans (by omega) (h.2.resolve_left hl0))

/-- The fields of a `TargetMajor` record decoded below the tops that `target_k53_args` reads. -/
theorem tmFields {m : Mem} {w : Word} {TM : TargetMajor} (h : DecB (fun m => decTM m w.toNat) m TM)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (w + 1)) ∧ decI (rdW (m.arr64 IW) (w + 1)) = TM.lvls ∧
    HSl0 m (rdW (m.arr64 IW) (w + 2)) (rdW (m.arr64 IW) (w + 3)) TM.ds ∧
    (rdW (m.arr64 IW) (w + 4)).toNat = TM.nPc ∧
    HSl0 m (rdW (m.arr64 IW) (w + 11)) (rdW (m.arr64 IW) (w + 12)) TM.pfvs ∧ w.toNat + 12 < iwTop m := by
  have h' : decTM (truncM m) w.toNat = some TM := h
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨i0, hi0, lv, hlv, ds, hds, nP, hnP, nI, -, cs, -, mb, -, nfs, -, pf, hpf, rfl⟩ := h'
  obtain ⟨hl1, hl2⟩ := truncH (i := 1) hlv hsz
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hds
  have hsl := truncSl (w := w) (i := 2) ho (by simpa [Nat.add_assoc] using hl) hd hsz
  obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some hpf
  have hsl' := truncSl (w := w) (i := 11) ho' (by simpa [Nat.add_assoc] using hl') hd' hsz
  obtain ⟨-, hnm⟩ := rec2IwN_trunc hnP
  obtain ⟨e4, t4⟩ := rec2RdN (w := w) (k := 4) hnm hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat (2 + 1) = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl,
    show UInt64.ofNat 11 = (11 : Word) from rfl, show UInt64.ofNat (11 + 1) = (12 : Word) from rfl] at hl1 hl2 hsl hsl' e4
  exact ⟨hl1, hl2, hsl, by rw [e4, t4], hsl', by have := (rec2IwN_trunc hl').1; omega⟩

section rel2
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem noF_ok (n : Nat) {m m' : Mem} {a : AState} {no nl e r : Word} {names : List NIdx}
    (h : noF n m no nl 0 0 e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e)
    (hno : decHL m no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop m) (hP : RcMR m) :
    ∃ b, (ConRon.Arena.nestOcc names 0 0 (decE e)).run a = .ok (b, a) ∧ (r != 0) = b ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => simp [noF] at h
  | succ n =>
  obtain ⟨ws, hws, hwm, hwl⟩ := slR_of_decHL m _ _ _ hno (hS.lt64 hnob)
  simp only [UInt64.ofNat_toNat] at hws
  obtain ⟨mp, hM⟩ := hP.pos.no
  obtain ⟨b, run, hb, hM', hS', hg, hf⟩ := noConstW_ok n dn fe vis m m' a no nl 0 0 e r ws mp h hS he hws hwl hM
  rw [hwm]
  exact ⟨b, by simpa using run, hb, hS', hg, hP.setNo hf ⟨∅, hM'⟩⟩

theorem tkaW_ok (n : Nat) {m m' : Mem} {a : AState} {q fto ftl Mc ip usp lao lal mao mal : Word}
    {r : List Word} {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor} {la ma : List EIdx}
    (h : tkaW n m vis q fto ftl Mc ip usp lao lal mao mal = some (r, m')) (hS : StageR dn vis fe m a)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (hip : H ip) (hus : H usp) (hla : HSl0 m lao lal la) (hma : HSl0 m mao mal ma) (hP : RcMR m) :
    ∃ c a', (tkArgs fe bs formerTys TM (decI ip) (decI usp) la ma).run a = .ok (c, a') ∧
      (r.headD 0 != 0) = c ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases n with
  | zero => simp [tkaW] at h
  | succ n =>
  rw [tkaW_succ] at h
  have hsz := hS.2.2.2.1
  obtain ⟨hlvH, hlvD, hdsS, hnP, hpfS, hMt⟩ := tmFields hMc hsz
  have hMk : ∀ k : Nat, k ≤ 12 → (Mc + UInt64.ofNat k).toNat < iwTop m := fun k hk => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by
      have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hMt; omega)]; omega
  generalize hK : rdW (m.arr64 IW) (Mc + 4) = K at h hnP
  cases h1 : eeW n m (if lal < K then lao else lao + K) (if lal < K then 0 else lal - K) with
  | none => rw [h1] at h; simp [tkaK1] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1, tkaK1_some] at h
  obtain ⟨le, a1, run1, hd1, hb1, hS1, hg1, hP1⟩ := eeW_ok dn fe vis n h1 hS hla.drop hP
  cases h2 : eeW n m1 (if mal < K then mao else mao + K) (if mal < K then 0 else mal - K) with
  | none => rw [h2] at h; simp [tkaK2] at h
  | some x =>
  obtain ⟨r2, m2⟩ := x
  rw [h2, tkaK2_some] at h
  obtain ⟨me, a2, run2, hd2, hb2, hS2, hg2, hP2⟩ := eeW_ok dn fe vis n h2 hS1 (hma.grow hg1).drop hP1
  cases h3 : eqW n m2 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) with
  | none => rw [h3] at h; simp [tkaK3] at h
  | some e =>
  rw [h3] at h
  have he := eqW_dec h3 (by rw [decHL_grow hg2 hb1]; exact hd1) (hS2.lt64 (by have := hg2.1; omega)) hd2
    (hS2.lt64 hb2)
  have hg12 := hg1.trans hg2
  rw [hnP] at run1 run2
  by_cases he0 : e = 0
  · rw [tkaK3_no (h := he0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hne : le ≠ me := by intro hq; rw [hq] at he; simp at he; exact absurd he (by rw [he0]; decide)
    refine ⟨false, a2, ?_, rfl, hS2, hg12, hP2⟩
    have : (le != me) = true := by simpa using hne
    simp only [tkArgs, StateT.run_bind, run1, except_ok_bind, run2, this, if_true]; rfl
  rw [tkaK3_yes (h := he0)] at h
  have heq : le = me := by
    by_cases hq : le = me
    · exact hq
    · rw [if_neg hq] at he; exact absurd he he0
  subst heq
  -- the leaf's class
  cases h4 : ceinternW m2 ip usp with
  | none => rw [h4] at h; simp [tkaK4] at h
  | some x =>
  obtain ⟨hd, m3⟩ := x
  rw [h4] at h
  obtain ⟨a3, run3, hS3, hg3⟩ := internConst_stage hS2 ip usp hip hus h4
  by_cases hb4 : 4294967296 ≤ hd
  · rw [tkaK4_big (h := hb4)] at h; cases h
  rw [tkaK4_ok (h := hb4)] at h
  have hhd : H hd := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb4; simp at hb4; omega
  have hP3 : RcMR m3 := hP2.fr (ceinternW_mfr h4)
  have hg03 := hg12.trans hg3
  have hlp := (hla.grow hg03).take (k := K)
  rw [hnP] at hlp
  generalize hL : (if lal < K then lal else K) = lpl at h hlp
  cases h5 : stubM "mk_app_n_f" m3 [hd, lao, lpl] with
  | none => rw [h5] at h; simp [tkaK5] at h
  | some x =>
  obtain ⟨ra, m4⟩ := x
  rw [h5, tkaK5_some] at h
  obtain ⟨app, a4, run4, hS4, hg4, happH, happD⟩ := mkAppN_spec dn vis fe hd lao lpl hhd _ m3 m4 a3 ra h5
    ⟨hS3, hlp.1⟩
  have hP4 : RcMR m4 := hP3.stub (by decide) h5
  have hg04 := hg03.trans hg4
  cases h6 : memberNamesW n m4 q with
  | none => rw [h6] at h; simp [tkaK6] at h
  | some x =>
  obtain ⟨rn, m5⟩ := x
  rw [h6, tkaK6_some] at h
  have hbs4 := hbs.grow hg04
  obtain ⟨hS5, hg5, -, hdn, htn⟩ := memberNamesW_stage h6 hS4 hbs4
  have hf5 := (memberNamesW_dec h6 hS4.2.2.2.1 hS4.2.2.2.2.2 hbs4.dec
    (by have := hbs4.ptop; have := hS4.lt64 (Nat.le_refl _); omega) hbs4.2.1 hbs4.2.2).2.2.2.1
  have hP5 : RcMR m5 := hP4.fr (MFr.of_iw hf5)
  cases h7 : noF n m5 (rn.headD 0) (rn.tail.headD 0) 0 0 (ra.headD 0) with
  | none => rw [h7] at h; simp [tkaK7] at h
  | some x =>
  obtain ⟨occ, m6⟩ := x
  rw [h7] at h
  obtain ⟨b, run6, hb6, hS6, hg6, hP6⟩ := noF_ok dn fe vis n h7 hS5 happH hdn (Nat.le_of_eq htn) hP5
  have hg06 := (hg04.trans hg5).trans hg6
  have hdecApp : decE (ra.headD 0) = app := happD
  have hrun4 : (mkAppN (decE hd) (la.take TM.nPc)).run a3 = .ok (decE (ra.headD 0), a4) := by
    rw [hdecApp]; exact run4
  by_cases ho : occ = 0
  · rw [tkaK7_no (h := ho)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have : b = false := by rw [← hb6, ho]; rfl
    subst this
    refine ⟨false, a4, ?_, rfl, hS6, hg06, hP6⟩
    simp only [tkArgs, StateT.run_bind, run1, except_ok_bind, run2, bne_self_eq_false, Bool.false_eq_true,
      if_false, ConRon.Arena.internConstE, run3, hrun4, run6]
    rfl
  rw [tkaK7_yes (h := ho)] at h
  have hb1 : b = true := by rw [← hb6]; simpa using ho
  subst hb1
  have hMk6 : ∀ k : Nat, k ≤ 12 → rdW (m6.arr64 IW) (Mc + UInt64.ofNat k) = rdW (m.arr64 IW) (Mc + UInt64.ofNat k) :=
    fun k hk => rdW_grow hg06 (hMk k hk)
  have e11 := hMk6 11 (by omega); have e12 := hMk6 12 (by omega); have e1 := hMk6 1 (by omega)
  have e2 := hMk6 2 (by omega); have e3 := hMk6 3 (by omega)
  simp only [show UInt64.ofNat 11 = (11 : Word) from rfl, show UInt64.ofNat 12 = (12 : Word) from rfl,
    show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl] at e11 e12 e1 e2 e3
  rw [e11, e12, e1, e2, e3] at h
  cases h8 : tcmF n m6 vis q fto ftl (rdW (m.arr64 IW) (Mc + 11)) (rdW (m.arr64 IW) (Mc + 12))
      (rdW (m.arr64 IW) (Mc + 1)) (rdW (m.arr64 IW) (Mc + 2)) (rdW (m.arr64 IW) (Mc + 3)) usp lao lpl with
  | none => rw [h8] at h; simp [tkaK8] at h
  | some x =>
  obtain ⟨r8, m8⟩ := x
  rw [h8, tkaK8_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨c, a8, run8, hc, hS8, hg8, hP8⟩ := tcmF_ok dn fe vis n h8 hS6 (hbs.grow hg06) hlvH hus
    (by rw [decHL_grow hg06 hftb]; exact hft) (by have := hg06.1; omega) (hpfS.grow hg06) (hdsS.grow hg06)
    (hlp.grow ((hg4.trans hg5).trans hg6)) hP6
  rw [hlvD] at run8
  refine ⟨c, a8, ?_, by simpa using hc, hS8, hg06.trans hg8, hP8⟩
  simp only [tkArgs, StateT.run_bind, run1, except_ok_bind, run2, bne_self_eq_false, Bool.false_eq_true,
    if_false, ConRon.Arena.internConstE, run3, hrun4, run6, if_true]
  exact run8
end rel2

end L.Ind
