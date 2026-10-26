import ConAgua.Arena.ConstsResolveFRefine
import ConAgua.Arena.IndPos2SpecB
import ConAgua.Arena.FVarRangeRefine
import ConAgua.Census.Attr

/-!
# `consts_resolve_ffast` refines `constsResolveFFast`: the walk (lane `tails`)

The relational half of `ConstsResolveFRefine.lean`: the leaves (`cr_leaf` is the twin's
`constsResolve` at one node), the memoized walk `crf_go` by induction on L's fuel, the entry.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Stubs

open L.Arena L.Ind

/-- **`e_view` answers tag `8` only at a `lit` handle**, below `2^32`, past the view checks. -/
theorem eViewW_lit (m : Mem) (h : Word) (hne : eViewW m h ≠ []) (h8 : (eViewW m h).headD 0 = 8) :
    h >>> 28 = 8 ∧ h.toNat < 2 ^ 32 ∧ ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) ∧
      ¬ tcnt m LIT (tierW h) ≤ idxW h := by
  unfold eViewW at hne h8
  by_cases c : (4294967295 : Word) < h
  · simp [c] at hne
  have hh : h.toNat < 2 ^ 32 := by
    have : ¬ (4294967295 : Nat) < h.toNat := c
    omega
  simp only [c, ite_false] at hne h8
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, ite_false] at hne h8
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, ite_true] at hne h8
    by_cases cc : tcnt m BVAR (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g0, ite_false] at hne h8
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, ite_true] at hne h8
    by_cases cc : tcnt m FVAR (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g1, ite_false] at hne h8
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, ite_true] at hne h8
    by_cases cc : tcnt m SORT (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g2, ite_false] at hne h8
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, ite_true] at hne h8
    by_cases cc : tcnt m CONST (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g3, ite_false] at hne h8
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ite_true] at hne h8
    by_cases cc : tcnt m APP (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g4, ite_false] at hne h8
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, ite_true] at hne h8
    by_cases cc : tcnt m LAM (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g5, ite_false] at hne h8
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, ite_true] at hne h8
    by_cases cc : tcnt m FORALL (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g6, ite_false] at hne h8
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ite_true] at hne h8
    by_cases cc : tcnt m LET (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g7, ite_false] at hne h8
  by_cases g8 : h >>> 28 = 8
  · simp only [g8, ite_true] at hne
    by_cases cc : tcnt m LIT (tierW h) ≤ idxW h
    · simp [cc] at hne
    · exact ⟨g8, hh, hs, cc⟩
  simp only [g8, ite_false] at hne h8
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, ite_true] at hne h8
    by_cases cc : tcnt m PROJ (tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp [g9] at hne

theorem getD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> rfl

theorem pinsFound_nat (fe : IFEnv) (m : Mem) :
    pinsFound fe m [1, 2, 3] = ((fe.find? (decI (pinW m 2))).isSome &&
      (fe.find? (decI (pinW m 3))).isSome && (fe.find? (decI (pinW m 4))).isSome) := by
  simp [pinsFound, Bool.and_assoc]

theorem pinsFound_str (fe : IFEnv) (m : Mem) :
    pinsFound fe m [1, 2, 3, 5, 6, 7, 8, 9, 10, 12] = ((fe.find? (decI (pinW m 2))).isSome &&
      (fe.find? (decI (pinW m 3))).isSome && (fe.find? (decI (pinW m 4))).isSome &&
      (fe.find? (decI (pinW m 6))).isSome && (fe.find? (decI (pinW m 7))).isSome &&
      (fe.find? (decI (pinW m 8))).isSome && (fe.find? (decI (pinW m 9))).isSome &&
      (fe.find? (decI (pinW m 10))).isSome && (fe.find? (decI (pinW m 11))).isSome &&
      (fe.find? (decI (pinW m 13))).isSome) := by
  simp [pinsFound, Bool.and_assoc]

theorem ite_not (b : Bool) : (if (!b) = true then (0 : Word) else 1) = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem getD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> rfl

theorem getD3 (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩ <;> rfl

/-! ## The memo -/

theorem crSch_wf : crSch.WF := ⟨by decide, by decide⟩

/-- A memo slot's value word and the twin's Bool. -/
def CrV (_ : Mem) (w : Word) (b : Bool) : Prop := w = if b then 1 else 0

/-- **The walk memo**: `CRM` against the twin's threaded `Std.HashMap EIdx Bool`. -/
def CrR (m : Mem) (memo : Std.HashMap EIdx Bool) : Prop := MemoRV crSch bmKey CrV m memo

/-- The walk's write set. -/
abbrev CrFrame (m m' : Mem) : Prop := MemFrame [CRM] [158, 159] m m'

theorem crV_stable : VStable crSch CrV := fun _ _ _ _ _ h => h

theorem StageR.crf {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} (hS : StageR dn vis fe m a) (hf : CrFrame m m') :
    StageR dn vis fe m' a ∧ IWGrow m m' :=
  StageR.frame_hi hS hf (by simp [CRM]) (by simp) (by simp [IW, CRM]) (by simp)


/-- What the walk's call at L fuel `n` says: the twin's walk at the counter's fuel, from the
related memo, reads only and answers the word, with the memo related after. -/
def CrfOK (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    Prop :=
  ∀ (m m' : Mem) (a : AState) (memo : Std.HashMap EIdx Bool) (f h : Word) (r : List Word),
    StageR dn vis fe m a → CrR m memo → h.toNat < 2 ^ 32 →
    callW p n "crf_go" [vis, f, h] m = some (r, m') →
    ∃ b memo', (constsResolveFGo fe memo f.toNat (decE h)).run a = .ok ((b, memo'), a) ∧
      CrR m' memo' ∧ CrFrame m m' ∧ r.headD 0 = if b then 1 else 0

theorem ite_and (b c : Bool) :
    (if (if b then (1 : Word) else 0) ≠ 0 ∧ (if c then (1 : Word) else 0) ≠ 0 then (1 : Word) else 0) =
      if (b && c) then 1 else 0 := by
  cases b <;> cases c <;> rfl

theorem ite_and3 (b c d : Bool) :
    (if (if b then (1 : Word) else 0) ≠ 0 ∧ (if c then (1 : Word) else 0) ≠ 0 ∧
      (if d then (1 : Word) else 0) ≠ 0 then (1 : Word) else 0) = if (b && c && d) then 1 else 0 := by
  cases b <;> cases c <;> cases d <;> rfl

section rel
variable {p : Prog} (hp : CrfProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include hp

/-- **`cr_lit_pins(vis, s)` as a call**: memory unchanged, the flag set, the word the twin's
literal guard (`s = 0`: `Nat`'s three pins, else `String`'s ten). -/
theorem clp_callW {n : Nat} {m m' : Mem} {a : AState} {s : Word} {r : List Word}
    (hS : StageR dn vis fe m a) (hc : callW p n "cr_lit_pins" [vis, s] m = some (r, m')) :
    m' = m ∧ pinW m 0 ≠ 0 ∧
      r.headD 0 = if (if s = 0 then pinsFound fe m [1, 2, 3]
        else pinsFound fe m [1, 2, 3, 5, 6, 7, 8, 9, 10, 12]) then 1 else 0 := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hW := callW_model (M := fun mm => clpW p n mm vis s) (clp_spec p hp n · vis s) hc
  unfold clpW at hW
  by_cases h0 : s = 0
  · rw [ite_eq_left h0] at hW
    obtain ⟨rfl, hf, rfl⟩ := clpL_callW hp hS _ _ _ _ _ hW
    refine ⟨rfl, hf, ?_⟩
    simp only [ite_eq_left h0, Bool.false_or, List.headD_cons]
    exact ite_not _
  · rw [ite_eq_right h0] at hW
    obtain ⟨rfl, hf, rfl⟩ := clpL_callW hp hS _ _ _ _ _ hW
    refine ⟨rfl, hf, ?_⟩
    simp only [ite_eq_right h0, Bool.false_or, List.headD_cons]
    exact ite_not _

/-- **`cr_leaf` at a leaf's view is `constsResolve`**: memory unchanged, the twin's walk at the
node reads only, and the word is its answer. -/
theorem cl_callW {n : Nat} {m m' : Mem} {a : AState} {h : Word} {r : List Word} {v : ENodeView}
    (hS : StageR dn vis fe m a) (hh : h.toNat < 2 ^ 32) (hne : eViewW m h ≠ [])
    (hv : a.store.view (decE h) = some v) (hR : ViewR (eViewW m h) v)
    (hleaf : (eViewW m h).headD 0 = 0 ∨ (eViewW m h).headD 0 = 2 ∨ (eViewW m h).headD 0 = 3 ∨
      (eViewW m h).headD 0 = 8)
    (hc : callW p n "cr_leaf" [vis, (eViewW m h).headD 0, (eViewW m h).tail.headD 0, h] m =
      some (r, m')) :
    m' = m ∧ ∃ b, (constsResolve fe coreWalkFuel (decE h)).run a = .ok (b, a) ∧
      r.headD 0 = if b then 1 else 0 := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hW := callW_model (M := fun mm => clW p n mm vis ((eViewW m h).headD 0)
    ((eViewW m h).tail.headD 0) h) (cl_spec p hp n · vis _ _ h) hc
  rw [show coreWalkFuel = 3999999999 + 1 from rfl, constsResolve, StateT.run_bind,
    view_run (decE h) a v hv, except_ok_bind]
  cases v with
  | bvar i =>
    have hg : (eViewW m h).headD 0 = 0 := hR.1
    rw [hg] at hW
    simp only [clW, show (0 : Word) ≠ 8 by decide, show (0 : Word) ≠ 3 by decide, ite_false,
      Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨rfl, true, rfl, rfl⟩
  | sort u =>
    have hg : (eViewW m h).headD 0 = 2 := hR.1
    rw [hg] at hW
    simp only [clW, show (2 : Word) ≠ 8 by decide, show (2 : Word) ≠ 3 by decide, ite_false,
      Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨rfl, true, rfl, rfl⟩
  | const nn us =>
    obtain ⟨hg, hx, hxn, -, -⟩ := hR
    rw [hg] at hW
    simp only [clW, show (3 : Word) ≠ 8 by decide, ite_false, ite_true] at hW
    rw [getD1] at hx hxn
    cases he : callW p n "env_find" [(eViewW m h).tail.headD 0, vis] m with
    | none => rw [he] at hW; cases hW
    | some q =>
    obtain ⟨re, me⟩ := q
    rw [he, bW_some, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨rfl, hval⟩ := envFind_callW hp hS.1.env hx he
    rw [hxn] at hval
    exact ⟨rfl, _, rfl, hval⟩
  | lit l =>
    have hg : (eViewW m h).headD 0 = 8 := hR
    obtain ⟨h8, -, hs, hcc⟩ := eViewW_lit m h hne hg
    obtain ⟨k, hk, hrel⟩ := view_lit_f m a hS.1.arena.1 h hh ⟨hs, UInt64.not_le.mp hcc⟩ h8
    rw [hv] at hk
    cases Option.some.inj hk
    rw [hg] at hW
    simp only [clW, ite_true] at hW
    cases hi : callW p n "is_str_lit" [h] m with
    | none => rw [hi] at hW; cases hW
    | some q =>
    obtain ⟨rs, ms⟩ := q
    rw [hi, bW_some] at hW
    obtain ⟨s', rfl, -, hms, hisl⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (isStrLit_spec p hp.isl n _ h) hi
    simp only at hms hisl
    rw [hms] at hW
    unfold islW at hisl
    simp only [h8, ne_eq, not_true_eq_false, ite_false, hs, hcc, Option.some.injEq] at hisl
    cases hl : callW p n "cr_lit_pins" [vis, rs.headD 0] m with
    | none => rw [hl] at hW; cases hW
    | some q =>
    obtain ⟨rl, ml⟩ := q
    rw [hl, bW_some, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨rfl, h0, hval⟩ := clp_callW hp hS hl
    have hF := hS.1.pins.full h0
    refine ⟨rfl, ?_⟩
    obtain ⟨⟨N⟩ | ⟨str⟩⟩ := k
    · have hrec : tfld ml LIT (tierW h) (idxW h) 0 = 0 := hrel.1
      rw [hrec] at hisl
      rw [← hisl] at hval
      simp only [show (0 : Word) ≠ 1 by decide, ite_false, ite_true] at hval
      refine ⟨_, ?_, by rw [List.headD_cons]; exact hval.trans (by rw [pinsFound_nat])⟩
      simp [pinNat, pinNatZero, pinNatSucc, PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC,
        StateT.run_bind, pinAt_run hF, except_ok_bind]
      rfl
    · have hrec : tfld ml LIT (tierW h) (idxW h) 0 = 1 := hrel.1
      rw [hrec] at hisl
      rw [← hisl] at hval
      simp only [ite_true, show (1 : Word) ≠ 0 by decide, ite_false] at hval
      refine ⟨_, ?_, by rw [List.headD_cons]; exact hval.trans (by rw [pinsFound_str])⟩
      simp [pinNat, pinNatZero, pinNatSucc, pinString, pinStringOfList, pinList, pinListNil,
        pinListCons, pinChar, pinCharOfNat, PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC, PIN_STRING,
        PIN_STRING_OF_LIST, PIN_LIST, PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR, PIN_CHAR_OF_NAT,
        StateT.run_bind, pinAt_run hF, except_ok_bind]
      rfl
  | fvar i ty => have := hR.1; rw [this] at hleaf; simp at hleaf
  | app f x => have := hR.1; rw [this] at hleaf; simp at hleaf
  | lam t b => have := hR.1; rw [this] at hleaf; simp at hleaf
  | forallE t b => have := hR.1; rw [this] at hleaf; simp at hleaf
  | letE t x b => have := hR.1; rw [this] at hleaf; simp at hleaf
  | proj s i e => have := hR.1; rw [this] at hleaf; simp at hleaf

/-- **The tail**: probe, record `w` (the twin's `b`), return it. -/
theorem crfT_callW {n : Nat} {m m' : Mem} {memo : Std.HashMap EIdx Bool} {h w : Word}
    {b : Bool} {r : List Word} (hM : CrR m memo) (hh : h.toNat < 2 ^ 32) (hw : w = if b then 1 else 0)
    (hc : crfT p n m h w = some (r, m')) :
    r = [w] ∧ CrR m' (memo.insert (decE h) b) ∧ CrFrame m m' := by
  unfold crfT at hc
  rcases hf : callW p n "crm_find" [h, 0] m with _ | ⟨rf, mf⟩
    <;> simp only [hf, reduceCtorEq, crfT1] at hc
  obtain ⟨s', hmf, hs', hne, hrf⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoFindG_spec crSch p "crm_find" hp.find n _ h 0) hf
  subst hs'
  simp only at hmf hrf
  subst hmf hrf
  cases hp' : callW p n "crm_put" [h, 0, w, (mfindG crSch m h 0).headD 0,
      (mfindG crSch m h 0).tail.headD 0] m with
  | none => rw [hp'] at hc; cases hc
  | some q =>
  obtain ⟨rp, mp⟩ := q
  rw [hp', crfT2, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨s'', hmp, -, hput⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoPutG_spec crSch p "crm_put" hp.put n _ h 0 w _ _) hp'
  simp only at hput
  subst hmp
  have hr : ¬ mfindG crSch m h 0 = [] := hne
  have hs : msetG crSch m h 0 w = some s''.mem := by
    rw [msetG, ite_eq_right hr]; exact hput
  refine ⟨rfl, ?_, ?_⟩
  · exact memoRV_set crSch crSch_wf bmKey CrV crV_stable m memo hM h 0 w ⟨hh, rfl⟩ b hw _ hs
  · exact (msetG_frame crSch crSch_wf m _ h 0 w hs).mono (by simp [CRM]) (by simp)

theorem crf_step (n : Nat) (ih : CrfOK p dn vis fe n) : CrfOK p dn vis fe (n + 1) := by
  intro m m' a memo f h r hS hM hh hc
  have hW := callW_model (M := fun mm => crfW p n mm vis f h) (crf_spec p hp n · vis f h) hc
  unfold crfW at hW
  by_cases hf : f = 0
  · rw [ite_eq_left hf] at hW; cases hW
  rw [ite_eq_right hf] at hW
  rcases hv : callW p n "e_view" [h] m with _ | ⟨rv, mv⟩
    <;> simp only [hv, reduceCtorEq, crfV] at hW
  obtain ⟨s', hmv, hs', hne, hrv⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (eView_spec p hp.view n _ h) hv
  subst hs'
  simp only at hmv hrv
  subst hmv hrv
  obtain ⟨v, hview, hR⟩ := eViewW_ok m a hS.1.arena.1 h hne
  rw [ctrW_toNat f hf, constsResolveFGo, StateT.run_bind, view_run (decE h) a v hview,
    except_ok_bind]
  cases v with
  | bvar _ | sort _ | const _ _ | lit _ =>
    have hg := (by first | exact hR.1 | exact hR : (eViewW m h).headD 0 = _)
    rw [ite_eq_left (by rw [hg]; decide)] at hW
    rcases hl : callW p n "cr_leaf" [vis, (eViewW m h).headD 0, (eViewW m h).tail.headD 0, h] m with _ | ⟨rl, ml⟩
      <;> simp only [hl, reduceCtorEq, crfLf, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    obtain ⟨rfl, b, hb, hres⟩ := cl_callW hp hS hh hne hview hR (by rw [hg]; decide) hl
    refine ⟨b, memo, ?_, hM, MemFrame.refl _ _ _, hres⟩
    simp only [StateT.run_bind, hb, except_ok_bind]; rfl
  | fvar i ty =>
    obtain ⟨hg, -, hb1, hd1⟩ := hR
    rw [getD2] at hb1 hd1
    rw [ite_eq_right (by rw [hg]; decide)] at hW
    rcases hfd : callW p n "crm_find" [h, 0] m with _ | ⟨rf, mf⟩
      <;> simp only [hfd, reduceCtorEq, crfM] at hW
    obtain ⟨s', hmf, hs', hne', hrf⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (memoFindG_spec crSch p "crm_find" hp.find n _ h 0) hfd
    subst hs'
    simp only at hmf hrf
    subst hmf hrf
    by_cases hhit : (mfindG crSch m h 0).headD 0 ≠ 0
    · rw [ite_eq_left hhit, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      obtain ⟨bv, hbv, hw⟩ := memoRV_hit crSch bmKey CrV m memo hM h 0 hne' hhit ⟨hh, rfl⟩
      refine ⟨bv, memo, ?_, hM, MemFrame.refl _ _ _, hw⟩
      change memo[decE h]? = some bv at hbv
      simp only [hbv]; rfl
    rw [ite_eq_right hhit] at hW
    have hmiss : memo[decE h]? = none :=
      memoRV_miss crSch bmKey CrV m memo hM h 0 ⟨hh, rfl⟩ hne' (by simpa using hhit)
    rw [crfN, ite_eq_left hg] at hW
    rcases h1 : callW p n "crf_go" [vis, f - 1, (eViewW m h).tail.tail.headD 0] m with _ | ⟨ra, ma⟩
      <;> simp only [h1, reduceCtorEq, crfFv] at hW
    obtain ⟨b1, memo1, hr1, hM1, hF1, hres1⟩ := ih m ma a memo (f - 1) _ ra hS hM hb1 h1
    obtain ⟨rfl, hM2, hF2⟩ := crfT_callW hp hM1 hh hres1 hW
    refine ⟨b1, memo1.insert (decE h) b1, ?_, hM2, hF1.trans hF2, hres1⟩
    rw [← hd1]
    simp only [hmiss, StateT.run_bind, hr1, except_ok_bind]; rfl
  | app _ _ | lam _ _ | forallE _ _ =>
    obtain ⟨hg, hb1, hd1, hb2, hd2⟩ := hR
    rw [getD1] at hb1 hd1
    rw [getD2] at hb2 hd2
    rw [ite_eq_right (by rw [hg]; decide)] at hW
    rcases hfd : callW p n "crm_find" [h, 0] m with _ | ⟨rf, mf⟩
      <;> simp only [hfd, reduceCtorEq, crfM] at hW
    obtain ⟨s', hmf, hs', hne', hrf⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (memoFindG_spec crSch p "crm_find" hp.find n _ h 0) hfd
    subst hs'
    simp only at hmf hrf
    subst hmf hrf
    by_cases hhit : (mfindG crSch m h 0).headD 0 ≠ 0
    · rw [ite_eq_left hhit, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      obtain ⟨bv, hbv, hw⟩ := memoRV_hit crSch bmKey CrV m memo hM h 0 hne' hhit ⟨hh, rfl⟩
      refine ⟨bv, memo, ?_, hM, MemFrame.refl _ _ _, hw⟩
      change memo[decE h]? = some bv at hbv
      simp only [hbv]; rfl
    rw [ite_eq_right hhit] at hW
    have hmiss : memo[decE h]? = none :=
      memoRV_miss crSch bmKey CrV m memo hM h 0 ⟨hh, rfl⟩ hne' (by simpa using hhit)
    rw [crfN, ite_eq_right (by rw [hg]; decide), ite_eq_left (by rw [hg]; decide)] at hW
    rcases h1 : callW p n "crf_go" [vis, f - 1, (eViewW m h).tail.headD 0] m with _ | ⟨ra, ma⟩
      <;> simp only [h1, reduceCtorEq, crfB1] at hW
    obtain ⟨b1, memo1, hr1, hM1, hF1, hres1⟩ := ih m ma a memo (f - 1) _ ra hS hM hb1 h1
    have hS1 := (StageR.crf hS hF1).1
    rcases h2 : callW p n "crf_go" [vis, f - 1, (eViewW m h).tail.tail.headD 0] ma with _ | ⟨rb, mb⟩
      <;> simp only [h2, reduceCtorEq, crfB2] at hW
    obtain ⟨b2, memo2, hr2, hM2, hF2, hres2⟩ := ih ma mb a memo1 (f - 1) _ rb hS1 hM1 hb2 h2
    rw [hres1, hres2, ite_and] at hW
    obtain ⟨rfl, hM3, hF3⟩ := crfT_callW hp hM2 hh rfl hW
    refine ⟨b1 && b2, memo2.insert (decE h) (b1 && b2), ?_, hM3, (hF1.trans hF2).trans hF3, rfl⟩
    rw [← hd1, ← hd2]
    simp only [hmiss, StateT.run_bind, hr1, hr2, except_ok_bind]; rfl
  | letE t x bd =>
    obtain ⟨hg, hb1, hd1, hb2, hd2, hb3, hd3⟩ := hR
    rw [getD1] at hb1 hd1
    rw [getD2] at hb2 hd2
    rw [getD3] at hb3 hd3
    rw [ite_eq_right (by rw [hg]; decide)] at hW
    rcases hfd : callW p n "crm_find" [h, 0] m with _ | ⟨rf, mf⟩
      <;> simp only [hfd, reduceCtorEq, crfM] at hW
    obtain ⟨s', hmf, hs', hne', hrf⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (memoFindG_spec crSch p "crm_find" hp.find n _ h 0) hfd
    subst hs'
    simp only at hmf hrf
    subst hmf hrf
    by_cases hhit : (mfindG crSch m h 0).headD 0 ≠ 0
    · rw [ite_eq_left hhit, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      obtain ⟨bv, hbv, hw⟩ := memoRV_hit crSch bmKey CrV m memo hM h 0 hne' hhit ⟨hh, rfl⟩
      refine ⟨bv, memo, ?_, hM, MemFrame.refl _ _ _, hw⟩
      change memo[decE h]? = some bv at hbv
      simp only [hbv]; rfl
    rw [ite_eq_right hhit] at hW
    have hmiss : memo[decE h]? = none :=
      memoRV_miss crSch bmKey CrV m memo hM h 0 ⟨hh, rfl⟩ hne' (by simpa using hhit)
    rw [crfN, ite_eq_right (by rw [hg]; decide), ite_eq_right (by rw [hg]; decide),
            ite_eq_left (by rw [hg])] at hW
    rcases h1 : callW p n "crf_go" [vis, f - 1, (eViewW m h).tail.headD 0] m with _ | ⟨ra, ma⟩
      <;> simp only [h1, reduceCtorEq, crfL1] at hW
    obtain ⟨b1, memo1, hr1, hM1, hF1, hres1⟩ := ih m ma a memo (f - 1) _ ra hS hM hb1 h1
    have hS1 := (StageR.crf hS hF1).1
    rcases h2 : callW p n "crf_go" [vis, f - 1, (eViewW m h).tail.tail.headD 0] ma with _ | ⟨rb, mb⟩
      <;> simp only [h2, reduceCtorEq, crfL2] at hW
    obtain ⟨b2, memo2, hr2, hM2, hF2, hres2⟩ := ih ma mb a memo1 (f - 1) _ rb hS1 hM1 hb2 h2
    have hS2 := (StageR.crf hS1 hF2).1
    rcases h3 : callW p n "crf_go" [vis, f - 1, (eViewW m h).tail.tail.tail.headD 0] mb with _ | ⟨rc, mc⟩
      <;> simp only [h3, reduceCtorEq, crfL3] at hW
    obtain ⟨b3, memo3, hr3, hM3, hF3, hres3⟩ := ih mb mc a memo2 (f - 1) _ rc hS2 hM2 hb3 h3
    rw [hres1, hres2, hres3, ite_and3] at hW
    obtain ⟨rfl, hM4, hF4⟩ := crfT_callW hp hM3 hh rfl hW
    refine ⟨b1 && b2 && b3, memo3.insert (decE h) (b1 && b2 && b3), ?_, hM4,
      ((hF1.trans hF2).trans hF3).trans hF4, rfl⟩
    rw [← hd1, ← hd2, ← hd3]
    simp only [hmiss, StateT.run_bind, hr1, hr2, hr3, except_ok_bind]
    cases b1 <;> cases b2 <;> rfl
  | proj sn i e =>
    obtain ⟨hg, hb1, hd1, -, hb3, hd3⟩ := hR
    rw [getD1] at hb1 hd1
    rw [getD3] at hb3 hd3
    rw [ite_eq_right (by rw [hg]; decide)] at hW
    rcases hfd : callW p n "crm_find" [h, 0] m with _ | ⟨rf, mf⟩
      <;> simp only [hfd, reduceCtorEq, crfM] at hW
    obtain ⟨s', hmf, hs', hne', hrf⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (memoFindG_spec crSch p "crm_find" hp.find n _ h 0) hfd
    subst hs'
    simp only at hmf hrf
    subst hmf hrf
    by_cases hhit : (mfindG crSch m h 0).headD 0 ≠ 0
    · rw [ite_eq_left hhit, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      obtain ⟨bv, hbv, hw⟩ := memoRV_hit crSch bmKey CrV m memo hM h 0 hne' hhit ⟨hh, rfl⟩
      refine ⟨bv, memo, ?_, hM, MemFrame.refl _ _ _, hw⟩
      change memo[decE h]? = some bv at hbv
      simp only [hbv]; rfl
    rw [ite_eq_right hhit] at hW
    have hmiss : memo[decE h]? = none :=
      memoRV_miss crSch bmKey CrV m memo hM h 0 ⟨hh, rfl⟩ hne' (by simpa using hhit)
    rw [crfN, ite_eq_right (by rw [hg]; decide), ite_eq_right (by rw [hg]; decide),
            ite_eq_right (by rw [hg]; decide)] at hW
    rcases h1 : callW p n "crf_go" [vis, f - 1, (eViewW m h).tail.tail.tail.headD 0] m with _ | ⟨ra, ma⟩
      <;> simp only [h1, reduceCtorEq, crfP1] at hW
    obtain ⟨b1, memo1, hr1, hM1, hF1, hres1⟩ := ih m ma a memo (f - 1) _ ra hS hM hb3 h1
    have hS1 := (StageR.crf hS hF1).1
    rcases h2 : callW p n "env_find" [(eViewW m h).tail.headD 0, vis] ma with _ | ⟨re, me⟩
      <;> simp only [h2, reduceCtorEq, crfP2] at hW
    obtain ⟨rfl, hval⟩ := envFind_callW hp hS1.1.env hb1 h2
    rw [hval, hres1, ite_and] at hW
    obtain ⟨rfl, hM2, hF2⟩ := crfT_callW hp hM1 hh rfl hW
    refine ⟨(fe.find? (decI ((eViewW m h).tail.headD 0))).isSome && b1,
      memo1.insert (decE h) ((fe.find? (decI ((eViewW m h).tail.headD 0))).isSome && b1), ?_, hM2,
      hF1.trans hF2, rfl⟩
    rw [← hd1, ← hd3]
    simp only [hmiss, StateT.run_bind, hr1, except_ok_bind]; rfl


/-- **The model of `crf_go` refines `constsResolveFGo`** at every L fuel: from a memory in the
stage relation with the memo table related to the twin's threaded memo, a returning call is the
twin's walk at the counter's fuel, reading only, answering the word, the memo related after. -/
@[refines ConRon.Arena.constsResolveFGo]
theorem crf_refines (n : Nat) : CrfOK p dn vis fe n := by
  induction n with
  | zero => intro m m' a memo f h r _ _ _ hc; rw [callW_zero] at hc; cases hc
  | succ n ih => exact crf_step hp n ih

/-- A memory whose walk-memo table `CRM` is related to some memo (its stamps are not ahead of
the epoch): what the entry's clear turns into the empty memo. -/
def CrOK (m : Mem) : Prop := ∃ memo, CrR m memo

/-- **`consts_resolve_ffast(vis, e)` refines `constsResolveFFast fe e`** under the stage relation
(with a related walk-memo table), in the `RefAM` shape of `IndStubs.lean`'s
`constsResolveFFast_spec`; the memo table stays related after. -/
theorem constsResolveFFast_ref (e : Word) (he : H e) :
    CallRef p "consts_resolve_ffast" [vis, e] (fun m a => StageR dn vis fe m a ∧ CrOK m)
      (constsResolveFFast fe (decI e))
      (fun m m' a r x => KeepPost dn vis fe decW0B m m' a r x ∧ CrOK m') := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, memo0, hM0⟩ hc => ?_
  have hW := callW_model (M := fun mm => crffW p k mm vis e) (crff_spec p hp k · vis e) hc
  unfold crffW at hW
  cases h1 : callW p k "crm_clear" [] m with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨rc, mc⟩ := q
  rw [h1, bW_some] at hW
  obtain ⟨s', hmc, -, hw, hclr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoClearG_spec crSch p "crm_clear" hp.clear k _) h1
  simp only at hw hclr
  subst hmc
  rw [hclr] at hW
  cases h2 : callW p k "crf_go" [vis, 4000000000, e] (mclearG crSch m) with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨rg, mg⟩ := q
  rw [h2, bW_some, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  have hfc : CrFrame m (mclearG crSch m) :=
    (mclearG_frame crSch m).mono (by simp) (by simp)
  have hSc := (StageR.crf hS hfc).1
  have hMc : CrR (mclearG crSch m) ∅ := memoRV_clear crSch crSch_wf bmKey CrV m memo0 hM0 hw
  obtain ⟨b, memo', hr, hM', hF, hres⟩ := crf_refines hp k _ _ a ∅ _ e rg hSc hMc he h2
  rw [coreWalkFuel_toNat] at hr
  obtain ⟨hS', hG⟩ := StageR.crf hS (hfc.trans hF)
  refine ⟨b, a, ?_, ⟨hS', hG, ?_, ?_⟩, memo', hM'⟩
  · simp only [constsResolveFFast, StateT.run_bind, ← decE_eq, hr, except_ok_bind]; rfl
  · simp only [List.headD_cons, hres]; cases b <;> rfl
  · simp only [List.headD_cons, hres]; cases b <;> decide

/-- **`consts_resolve_ffast(vis, e)` refines `constsResolveFFast fe e`**, as a Hoare triple
(`RefAM`): the census link. -/
@[refines ConRon.Arena.constsResolveFFast]
theorem constsResolveFFast_refines (e : Word) (he : H e) :
    RefAM p "consts_resolve_ffast" [vis, e] (fun m a => StageR dn vis fe m a ∧ CrOK m)
      (constsResolveFFast fe (decI e))
      (fun m m' a r x => KeepPost dn vis fe decW0B m m' a r x ∧ CrOK m') :=
  (constsResolveFFast_ref hp e he).refAM

end rel

end L.Stubs
