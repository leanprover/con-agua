module

import ConAgua.L.ModelGen
import ConAgua.Arena.WhnfDeltaRefine
import all ConAgua.Arena.Pins
import ConAgua.Arena.StrLitChar
import ConAgua.Arena.StrLitList
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DefEqMid
import ConAgua.Arena.InferBodyLet
import ConAgua.L.LocNF
import Std.Tactic.BVDecide.Normalize.Bool
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.StrLitBase
import all ConAgua.Arena.StrLit

@[expose] public section

/-!
# `str_lit_stored` under `CoreS`

`str_lit_stored(vis)` is `nat_lit_stored` and the presence of the seven string-support names
(con-leche task #480: what they are is the declarations' own check, `lit_shape_ok`). The proof of
the retired `str_lit_supported` chain went with it; this one is owed (lane ronsync2, stage 3).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The model of `str_lit_stored`. -/
l_model strLitStored_spec (p : Prog) (hp : p.lookup "str_lit_stored" = some strLitStoredL)
  fns [hp ↦ strLitStoredW]
  specs [callW_spec p n "nat_lit_stored", callW_spec p n "pin_at", callW_spec p n "env_find"]
  grind [arena_grind]
  gen 40

theorem bit_and (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then (1 : Word) else 0) &&& if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem bit_ne (P : Prop) [Decidable P] : ((if P then (1 : Word) else 0) != 0) = decide P := by
  by_cases hP : P <;> simp [hP]

theorem CRef.of_run {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (b : α) (hrun : T.run a₀ = .ok (b, a₀))
    (hC : CoreS dn m a₀ vis fe M eb)
    (hfr : MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m₀ m)
    (hres : dec r = b) (hok : ok r) : CRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨h1, h2, h3⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨h1, by rw [h2]; exact hC, by rw [h3, hres], hfr, hok⟩

section calls
variable (p : Prog) (hp : StrLitProg p)
include hp

theorem callW_strLitStored (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (r : List Word) (m' : Mem)
    (h : callW p n "str_lit_stored" [vis] s₀.mem = some (r, m')) :
    CRef (strLitStored fe) a₀ decBool dn s₀.mem vis fe MM eb r m' ResH := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (strLitStored_spec p hp.strLitStored (n + 1) s₀ vis) h
  rw [strLitStoredW.eq_2] at hW
  rcases h0 : callW p n "nat_lit_stored" [vis] s₀.mem with _ | ⟨r₀, m₀⟩
    <;> simp only [h0, strLitStoredW.k_nat_lit_stored, reduceCtorEq] at hW
  obtain ⟨-, hC₀, hres₀, hfr₀, -⟩ := callW_natLitStored p hp.toWhnfDeltaProg' n s₀ a₀ dn vis fe MM eb hC r₀ m₀ h0
  have hrun₀ := natLitStored_run hC.pins fe
  have hst₀ : AM.st (natLitStored fe) a₀ = a₀ := by simp only [AM.st, hrun₀]
  have hv₀ : AM.res (natLitStored fe) a₀ = ((fe.find? (decI (pinW s₀.mem 2))).isSome &&
      (fe.find? (decI (pinW s₀.mem 3))).isSome && (fe.find? (decI (pinW s₀.mem 4))).isSome) := by
    simp only [AM.res, hrun₀]
  rw [hst₀] at hC₀
  rw [hres₀] at hv₀
  have hpin : ∀ k, pinW m₀ k = pinW s₀.mem k := fun k => by
    unfold pinW; rw [hfr₀.arr _ (by simp [CREC, CSLOT, CLP, PINS]) (by decide)]
  by_cases hb : r₀.headD 0 = 0
  · simp only [hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hf : ((fe.find? (decI (pinW s₀.mem 2))).isSome &&
      (fe.find? (decI (pinW s₀.mem 3))).isSome && (fe.find? (decI (pinW s₀.mem 4))).isSome) = false := by
      rw [← hv₀]; unfold decBool; rw [hb]; rfl
    rw [hf] at hrun₀
    have hsF : (strLitStored fe).run a₀ = .ok (false, a₀) := by
      simp only [strLitStored, StateT.run_bind, hrun₀, except_ok_bind]; rfl
    refine CRef.of_run false hsF (by rw [← hm]; exact hC₀) (by rw [← hm]; exact hfr₀) ?_ ?_
    · show (r.headD 0 != 0) = false; rw [← hr]; rfl
    · unfold ResH; rw [← hr]; unfold HW; decide
  simp only [hb, ↓reduceIte] at hW
  have ht : ((fe.find? (decI (pinW s₀.mem 2))).isSome &&
      (fe.find? (decI (pinW s₀.mem 3))).isSome && (fe.find? (decI (pinW s₀.mem 4))).isSome) = true := by
    rw [← hv₀]; unfold decBool; exact bne_iff_ne.mpr hb
  have hn : ∀ (k : Nat), k < 51 → HW (pinW m₀ (1 + k)) := fun k hk => hC₀.pins.names_lt k hk
  rcases hp0 : callW p n "pin_at" [5] m₀ with _ | ⟨a0, m0p⟩
    <;> simp only [hp0, strLitStoredW.k_pin_at, reduceCtorEq] at hW
  obtain ⟨hmp0, -, -, hrp0⟩ := callW_pinAt p hp.pinAt n _ 5 a0 m0p hp0
  subst m0p
  rcases hp1 : callW p n "pin_at" [6] m₀ with _ | ⟨a1, m1p⟩
    <;> simp only [hp1, strLitStoredW.k_pin_at_2, reduceCtorEq] at hW
  obtain ⟨hmp1, -, -, hrp1⟩ := callW_pinAt p hp.pinAt n _ 6 a1 m1p hp1
  subst m1p
  rcases hp2 : callW p n "pin_at" [7] m₀ with _ | ⟨a2, m2p⟩
    <;> simp only [hp2, strLitStoredW.k_pin_at_3, reduceCtorEq] at hW
  obtain ⟨hmp2, -, -, hrp2⟩ := callW_pinAt p hp.pinAt n _ 7 a2 m2p hp2
  subst m2p
  rcases hp3 : callW p n "pin_at" [8] m₀ with _ | ⟨a3, m3p⟩
    <;> simp only [hp3, strLitStoredW.k_pin_at_4, reduceCtorEq] at hW
  obtain ⟨hmp3, -, -, hrp3⟩ := callW_pinAt p hp.pinAt n _ 8 a3 m3p hp3
  subst m3p
  rcases hp4 : callW p n "pin_at" [9] m₀ with _ | ⟨a4, m4p⟩
    <;> simp only [hp4, strLitStoredW.k_pin_at_5, reduceCtorEq] at hW
  obtain ⟨hmp4, -, -, hrp4⟩ := callW_pinAt p hp.pinAt n _ 9 a4 m4p hp4
  subst m4p
  rcases hp5 : callW p n "pin_at" [10] m₀ with _ | ⟨a5, m5p⟩
    <;> simp only [hp5, strLitStoredW.k_pin_at_6, reduceCtorEq] at hW
  obtain ⟨hmp5, -, -, hrp5⟩ := callW_pinAt p hp.pinAt n _ 10 a5 m5p hp5
  subst m5p
  rcases hp6 : callW p n "pin_at" [12] m₀ with _ | ⟨a6, m6p⟩
    <;> simp only [hp6, strLitStoredW.k_pin_at_7, reduceCtorEq] at hW
  obtain ⟨hmp6, -, -, hrp6⟩ := callW_pinAt p hp.pinAt n _ 12 a6 m6p hp6
  subst m6p
  rcases hf0 : callW p n "env_find" [a0.headD 0, vis] m₀ with _ | ⟨b0, m0f⟩
    <;> simp only [hf0, strLitStoredW.k_env_find, reduceCtorEq] at hW
  obtain ⟨hmf0, hq0, hd0⟩ := callW_envFind p hp.toWhnfDeltaProg' n ⟨m₀, Locals.init []⟩ vis _ hC₀.env
    (by rw [hrp0]; exact hn 5 (by decide)) b0 m0f hf0
  subst m0f
  rcases hf1 : callW p n "env_find" [a1.headD 0, vis] m₀ with _ | ⟨b1, m1f⟩
    <;> simp only [hf1, strLitStoredW.k_env_find_2, reduceCtorEq] at hW
  obtain ⟨hmf1, hq1, hd1⟩ := callW_envFind p hp.toWhnfDeltaProg' n ⟨m₀, Locals.init []⟩ vis _ hC₀.env
    (by rw [hrp1]; exact hn 6 (by decide)) b1 m1f hf1
  subst m1f
  rcases hf2 : callW p n "env_find" [a2.headD 0, vis] m₀ with _ | ⟨b2, m2f⟩
    <;> simp only [hf2, strLitStoredW.k_env_find_3, reduceCtorEq] at hW
  obtain ⟨hmf2, hq2, hd2⟩ := callW_envFind p hp.toWhnfDeltaProg' n ⟨m₀, Locals.init []⟩ vis _ hC₀.env
    (by rw [hrp2]; exact hn 7 (by decide)) b2 m2f hf2
  subst m2f
  rcases hf3 : callW p n "env_find" [a3.headD 0, vis] m₀ with _ | ⟨b3, m3f⟩
    <;> simp only [hf3, strLitStoredW.k_env_find_4, reduceCtorEq] at hW
  obtain ⟨hmf3, hq3, hd3⟩ := callW_envFind p hp.toWhnfDeltaProg' n ⟨m₀, Locals.init []⟩ vis _ hC₀.env
    (by rw [hrp3]; exact hn 8 (by decide)) b3 m3f hf3
  subst m3f
  rcases hf4 : callW p n "env_find" [a4.headD 0, vis] m₀ with _ | ⟨b4, m4f⟩
    <;> simp only [hf4, strLitStoredW.k_env_find_5, reduceCtorEq] at hW
  obtain ⟨hmf4, hq4, hd4⟩ := callW_envFind p hp.toWhnfDeltaProg' n ⟨m₀, Locals.init []⟩ vis _ hC₀.env
    (by rw [hrp4]; exact hn 9 (by decide)) b4 m4f hf4
  subst m4f
  rcases hf5 : callW p n "env_find" [a5.headD 0, vis] m₀ with _ | ⟨b5, m5f⟩
    <;> simp only [hf5, strLitStoredW.k_env_find_6, reduceCtorEq] at hW
  obtain ⟨hmf5, hq5, hd5⟩ := callW_envFind p hp.toWhnfDeltaProg' n ⟨m₀, Locals.init []⟩ vis _ hC₀.env
    (by rw [hrp5]; exact hn 10 (by decide)) b5 m5f hf5
  subst m5f
  rcases hf6 : callW p n "env_find" [a6.headD 0, vis] m₀ with _ | ⟨b6, m6f⟩
    <;> simp only [hf6, strLitStoredW.k_env_find_7, reduceCtorEq] at hW
  obtain ⟨hmf6, hq6, hd6⟩ := callW_envFind p hp.toWhnfDeltaProg' n ⟨m₀, Locals.init []⟩ vis _ hC₀.env
    (by rw [hrp6]; exact hn 12 (by decide)) b6 m6f hf6
  subst m6f
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hval : (strLitStored fe).run a₀ = .ok ((fe.find? (decI (pinW s₀.mem 6))).isSome && (fe.find? (decI (pinW s₀.mem 7))).isSome && (fe.find? (decI (pinW s₀.mem 8))).isSome && (fe.find? (decI (pinW s₀.mem 9))).isSome && (fe.find? (decI (pinW s₀.mem 10))).isSome && (fe.find? (decI (pinW s₀.mem 11))).isSome && (fe.find? (decI (pinW s₀.mem 13))).isSome, a₀) := by
    simp only [strLitStored, StateT.run_bind, hrun₀, except_ok_bind, ht, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, pinString, pinStringOfList, pinList, pinListNil, pinListCons, pinChar, pinCharOfNat,
      PIN_STRING, PIN_STRING_OF_LIST, PIN_LIST, PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR, PIN_CHAR_OF_NAT,
      pinAt_run hC.pins 5 (by decide), pinAt_run hC.pins 6 (by decide), pinAt_run hC.pins 7 (by decide), pinAt_run hC.pins 8 (by decide), pinAt_run hC.pins 9 (by decide), pinAt_run hC.pins 10 (by decide), pinAt_run hC.pins 12 (by decide)]
    rfl
  have e0 : fe.find? (decI (pinW s₀.mem 6)) = envFound m₀ (b0.headD 0) (b0.tail.headD 0) := by
    rw [← hq0, hrp0, hpin]; rfl
  have e1 : fe.find? (decI (pinW s₀.mem 7)) = envFound m₀ (b1.headD 0) (b1.tail.headD 0) := by
    rw [← hq1, hrp1, hpin]; rfl
  have e2 : fe.find? (decI (pinW s₀.mem 8)) = envFound m₀ (b2.headD 0) (b2.tail.headD 0) := by
    rw [← hq2, hrp2, hpin]; rfl
  have e3 : fe.find? (decI (pinW s₀.mem 9)) = envFound m₀ (b3.headD 0) (b3.tail.headD 0) := by
    rw [← hq3, hrp3, hpin]; rfl
  have e4 : fe.find? (decI (pinW s₀.mem 10)) = envFound m₀ (b4.headD 0) (b4.tail.headD 0) := by
    rw [← hq4, hrp4, hpin]; rfl
  have e5 : fe.find? (decI (pinW s₀.mem 11)) = envFound m₀ (b5.headD 0) (b5.tail.headD 0) := by
    rw [← hq5, hrp5, hpin]; rfl
  have e6 : fe.find? (decI (pinW s₀.mem 13)) = envFound m₀ (b6.headD 0) (b6.tail.headD 0) := by
    rw [← hq6, hrp6, hpin]; rfl
  rw [e0, e1, e2, e3, e4, e5, e6] at hval
  refine CRef.of_run _ hval (by rw [← hm]; exact hC₀) (by rw [← hm]; exact hfr₀) ?_ ?_
  · show (r.headD 0 != 0) = _
    rw [envFound_isSome hd0, envFound_isSome hd1, envFound_isSome hd2, envFound_isSome hd3, envFound_isSome hd4, envFound_isSome hd5, envFound_isSome hd6, ← hr]
    simp only [bit_and, bit_ne]
    simp only [Bool.decide_and, ne_eq, decide_not]
    rfl
  · unfold ResH; rw [← hr]; unfold HW
    simp only [bit_and]
    split <;> decide

/-- **`str_lit_stored(vis)` refines `strLitStored fe`.** -/
@[refines ConRon.Arena.strLitStored]
theorem strLitStored_core : StrLitStoredOK p := fun n s₀ a₀ dn vis fe MM eb hC =>
  CoreSpec.of_callC fun r m' h => callW_strLitStored p hp n s₀ a₀ dn vis fe MM eb hC r m' h

end calls

end L.Arena
