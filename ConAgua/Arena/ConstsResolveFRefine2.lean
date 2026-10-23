import ConAgua.Arena.ConstsResolveFRefine
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
      ¬ rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h := by
  unfold eViewW at hne h8
  by_cases c : (4294967295 : Word) < h
  · simp [c] at hne
  have hh : h.toNat < 2 ^ 32 := by
    have : ¬ (4294967295 : Nat) < h.toNat := c
    omega
  simp only [c, if_false] at hne h8
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, if_false] at hne h8
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g0, if_false] at hne h8
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g1, if_false] at hne h8
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g2, if_false] at hne h8
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g3, if_false] at hne h8
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g4, if_false] at hne h8
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g5, if_false] at hne h8
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g6, if_false] at hne h8
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · simp [cc] at h8
  simp only [g7, if_false] at hne h8
  by_cases g8 : h >>> 28 = 8
  · simp only [g8, if_true] at hne
    by_cases cc : rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h
    · simp [cc] at hne
    · exact ⟨g8, hh, hs, cc⟩
  simp only [g8, if_false] at hne h8
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, if_true] at hne h8
    by_cases cc : rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h
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
  · rw [if_pos h0] at hW
    obtain ⟨rfl, hf, rfl⟩ := clpL_callW hp hS _ _ _ _ _ hW
    refine ⟨rfl, hf, ?_⟩
    simp only [if_pos h0, Bool.false_or, List.headD_cons]
    exact ite_not _
  · rw [if_neg h0] at hW
    obtain ⟨rfl, hf, rfl⟩ := clpL_callW hp hS _ _ _ _ _ hW
    refine ⟨rfl, hf, ?_⟩
    simp only [if_neg h0, Bool.false_or, List.headD_cons]
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
    simp only [clW, show (0 : Word) ≠ 8 by decide, show (0 : Word) ≠ 3 by decide, if_false,
      Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨rfl, true, rfl, rfl⟩
  | sort u =>
    have hg : (eViewW m h).headD 0 = 2 := hR.1
    rw [hg] at hW
    simp only [clW, show (2 : Word) ≠ 8 by decide, show (2 : Word) ≠ 3 by decide, if_false,
      Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨rfl, true, rfl, rfl⟩
  | const nn us =>
    obtain ⟨hg, hx, hxn, -, -⟩ := hR
    rw [hg] at hW
    simp only [clW, show (3 : Word) ≠ 8 by decide, if_false, if_true] at hW
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
    simp only [clW, if_true] at hW
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
    simp only [h8, ne_eq, not_true_eq_false, if_false, hs, hcc, Option.some.injEq] at hisl
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
    · have hrec : rdW (ml.arr64 REC) (idxW h * 8 + tierW h * 4) = 0 := hrel.1
      rw [hrec] at hisl
      rw [← hisl] at hval
      simp only [show (0 : Word) ≠ 1 by decide, if_false, if_true] at hval
      refine ⟨_, ?_, by rw [List.headD_cons]; exact hval.trans (by rw [pinsFound_nat])⟩
      simp [pinNat, pinNatZero, pinNatSucc, PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC,
        StateT.run_bind, pinAt_run hF, except_ok_bind]
      rfl
    · have hrec : rdW (ml.arr64 REC) (idxW h * 8 + tierW h * 4) = 1 := hrel.1
      rw [hrec] at hisl
      rw [← hisl] at hval
      simp only [if_true, show (1 : Word) ≠ 0 by decide, if_false] at hval
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

end rel

end L.Stubs
