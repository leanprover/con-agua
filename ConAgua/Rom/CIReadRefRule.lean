module

import ConAgua.Rom.CIReadRefCaps
import ConAgua.L.WordOff
import ConAgua.Rom.CIReadRefCV
import ConAgua.Rom.CIReadRefNames
public import ConAgua.Rom.CIReadRefBase
public import ConAgua.Rom.CIReadSpec

@[expose] public section

/-!
# The ROM constant readers: recursor rules (helper `decls4-rom`)

`rci_rule(q, r)` refines `Frontend.internRule` for a plain rule (no pinned constant ROM rule is
nested), into the 11-word record at `r` (`decRule`); `rci_rules_to(q, o, k)` refines
`Frontend.internRules` into consecutive records (`decRules`).
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- A list decoded index by index. -/
theorem holds_mapM_range {α : Type} [Inhabited α] {SE SI : Nat → Prop} {g : Mem → Nat → Option α} {m : Mem}
    (xs : List α) (h : ∀ j (hj : j < xs.length), Holds SE SI (fun m => g m j) m xs[j]) :
    Holds SE SI (fun m => (List.range xs.length).mapM (g m)) m xs := by
  intro m' h1 h2
  show List.mapM (g m') (List.range xs.length) = some xs
  rw [rmapM_some_of _ (fun j => xs.getD j default) _ (fun j hj => by
    have hj' := List.mem_range.mp hj
    have := h j hj' m' h1 h2
    simp only at this
    rw [this]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'])]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `decRule` of a plain rule from its words. -/
theorem holds_decRule {m : Mem} {q : Nat} (irl : IRecRule) (wc wnf wcp wf wrhs wk weta : Word)
    (h0 : erA m q = some wc) (h1 : erA m (q + 1) = some wnf) (h2 : erA m (q + 2) = some wcp)
    (h3 : erA m (q + 3) = some wf) (h8 : erA m (q + 8) = some wrhs)
    (h9 : erA m (q + 9) = some wk) (h10 : erA m (q + 10) = some weta)
    (hc : wc.toNat < 2 ^ 32) (hr : wrhs.toNat < 2 ^ 32) (hf : wf.toNat = 0)
    (ec : irl.ctor = decI wc) (enf : irl.nfields = wnf.toNat) (ecp : irl.ctorParams = wcp.toNat)
    (efi : irl.fire = .plain) (er : irl.rhs = decI wrhs) (ek : irl.k = (wk != 0))
    (eeta : irl.eta = (weta != 0)) :
    Holds (fun i => q ≤ i ∧ i < q + 11) (fun _ => False) (fun m => decRule (erA m) q) m irl := by
  intro m' hE _
  have g : ∀ i, i < 11 → erA m' (q + i) = erA m (q + i) := fun i hi => hE _ ⟨by omega, by omega⟩
  have e0 := (g 0 (by omega)).trans h0
  have e1 := (g 1 (by omega)).trans h1
  have e2 := (g 2 (by omega)).trans h2
  have e3 := (g 3 (by omega)).trans h3
  have e8 := (g 8 (by omega)).trans h8
  have e9 := (g 9 (by omega)).trans h9
  have e10 := (g 10 (by omega)).trans h10
  simp only [Nat.add_zero] at e0
  have : irl = ⟨decI wc, wnf.toNat, wcp.toNat, .plain, decI wrhs, wk != 0, weta != 0⟩ := by
    cases irl; simp_all
  rw [this]
  simp [decRule, nat?_of e3, hf, hd?, e0, hc, nat?_of e1, nat?_of e2, e8, hr, bool?_of e9,
    bool?_of e10]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A plain rule that fits its encoding. -/
def ruleFits (rl : ConLeche.RecRule) : Bool :=
  nameFits rl.ctor && decide (rl.nfields < 2 ^ 64) && decide (rl.ctorParams < 2 ^ 64) &&
    (match rl.fire with | .plain => true | .nested _ _ => false) && exprFits rl.rhs
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem encRule_eq (seen : List ConLeche.Expr) (rl : ConLeche.RecRule) (hp : rl.fire = .plain)
    (rest : List UInt8) :
    (encRule seen rl).1 ++ rest = encName rl.ctor ++ (u64B rl.nfields ++ (u64B rl.ctorParams ++
      (u64B (if rl.k then 1 else 0) ++ (u64B (if rl.eta then 1 else 0) ++ (u64B 0 ++
      ((encExprM seen rl.rhs).1 ++ rest)))))) ∧ (encRule seen rl).2 = (encExprM seen rl.rhs).2 := by
  simp [encRule, hp, bw, List.append_assoc]
-/

section rule
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_rule` refines `Frontend.internRule`** for a plain rule, into the 11 words at `rr`. -/
@[refines_part ConRon.Arena.Frontend.internRule "plain rules"]
theorem rule_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (rl : ConLeche.RecRule) (hfit : ruleFits rl = true) (k : Nat) (m : Mem) (a : AState)
    (q rr : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hst : stkTop m = 0) (hd : rom.drop q.toNat = (encRule seen rl).1 ++ rest)
    (hc0 : erTop m₀ ≤ rr.toNat) (hc11 : rr.toNat + 11 ≤ erTop m)
    (hc : callW p (k + 1) "rci_rule" [q, rr] m = some (r, m')) :
    ∃ (memo' : EMemo) (irl : IRecRule) (a' : AState),
      (Frontend.internRule memo rl).run a = .ok ((memo', irl), a') ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' (encRule seen rl).2 memo' ∧ stkTop m' = 0 ∧
      (r.headD 0).toNat = q.toNat + (encRule seen rl).1.length ∧
      EKeep (fun i => rr.toNat ≤ i ∧ i < rr.toNat + 11) m m' ∧ erTop m' = erTop m ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => rr.toNat ≤ i ∧ i < rr.toNat + 11) (fun _ => False)
        (fun m => decRule (erA m) rr.toNat) m' irl := by
  sorry

end rule

section rules
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_rules_to` refines `Frontend.internRules`**, into the 11-word records at `o`, `o + 11`, …. -/
@[refines_part ConRon.Arena.Frontend.internRules "plain rules"]
theorem rulesTo_rel {m₀ : Mem} {a₀ : AState} {T : Nat} :
    ∀ (rs : List ConLeche.RecRule), rs.all ruleFits = true → ∀ (seen : List ConLeche.Expr) (memo : EMemo)
      (k : Nat) (m : Mem) (a : AState) (q o kw : Word) (rest : List UInt8) (r : List Word) (m' : Mem),
      RInv m₀ a₀ T m a → MemoR m seen memo → stkTop m = 0 →
      rom.drop q.toNat = (encRules seen rs).1 ++ rest → kw.toNat = rs.length →
      erTop m₀ ≤ o.toNat → o.toNat + 11 * rs.length ≤ erTop m →
      callW p k "rci_rules_to" [q, o, kw] m = some (r, m') →
      ∃ (memo' : EMemo) (irs : List IRecRule) (a' : AState),
        (Frontend.internRules memo rs).run a = .ok ((memo', irs), a') ∧ irs.length = rs.length ∧
        RInv m₀ a₀ T m' a' ∧ MemoR m' (encRules seen rs).2 memo' ∧ stkTop m' = 0 ∧
        (r.headD 0).toNat = q.toNat + (encRules seen rs).1.length ∧
        EKeep (fun i => o.toNat ≤ i ∧ i < o.toNat + 11 * rs.length) m m' ∧ erTop m' = erTop m ∧
        m'.arr64 IW = m.arr64 IW ∧
        ∀ j (hj : j < irs.length), Holds (fun i => o.toNat + 11 * j ≤ i ∧ i < o.toNat + 11 * j + 11)
          (fun _ => False) (fun m => decRule (erA m) (o.toNat + 11 * j)) m' irs[j] := by
  intro rs
  induction rs with
  | nil =>
    intro _ seen memo k m a q o kw rest r m' hI hM hst hd hk ho hot hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mq => rulesToW p k mq q o kw) (rulesTo_specW rom p hL k · q o kw) hc
    have hk0 : kw = 0 := by apply UInt64.toNat_inj.mp; simpa using hk
    simp only [rulesToW, hk0, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨memo, [], a, rfl, rfl, hI, hM, hst, by simp [encRules], EKeep.refl _ _, rfl, rfl,
      fun j hj => by simp at hj⟩
  | cons rl rs ih =>
    intro hfit seen memo k m a q o kw rest r m' hI hM hst hd hk ho hot hc
    simp only [List.all_cons, Bool.and_eq_true] at hfit
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mq => rulesToW p k mq q o kw) (rulesTo_specW rom p hL k · q o kw) hc
    have hk0 : kw ≠ 0 := fun h => by subst h; simp at hk
    simp only [rulesToW, hk0, ite_false] at hw
    cases k with
    | zero => rw [callW_zero] at hw; simp at hw
    | succ k =>
    obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
    simp only [List.length_cons] at hot hk
    have hd0 : rom.drop q.toNat = (encRule seen rl).1 ++ ((encRules (encRule seen rl).2 rs).1 ++ rest) := by
      rw [hd]; simp [encRules, List.append_assoc]
    obtain ⟨memo1, irl, a1, hrun1, hI1, hM1, hs1, hq1, hek1, ht1, hIW1, hH1⟩ :=
      rule_rel hL hr seen memo rl hfit.1 k m a q o _ _ m1 hI hM hst hd0 ho (by omega) h1
    have hlt := hI.er_lt
    have ho11 : (o + 11).toNat = o.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
    have hk1' : (kw - 1).toNat = rs.length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    obtain ⟨r2, m2, h2, hw⟩ := ntBW_inv hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hd1 : rom.drop (r1.headD 0).toNat = (encRules (encRule seen rl).2 rs).1 ++ rest :=
      drop_shift rom q _ _ _ (by rw [hd0, List.append_assoc]) _ hq1
    obtain ⟨memo2, irs, a2, hrun2, hlen2, hI2, hM2, hs2, hq2, hek2, ht2, hIW2, hH2⟩ :=
      ih hfit.2 _ memo1 (k + 1) m1 a1 _ (o + 11) (kw - 1) rest r2 m2 hI1 hM1 hs1 hd1 hk1'
        (by omega) (by omega) h2
    refine ⟨memo2, irl :: irs, a2, ?_, by simp [hlen2], hI2, ?_, hs2, ?_, ?_, by rw [ht2, ht1],
      by rw [hIW2, hIW1], ?_⟩
    · simp only [Frontend.internRules]
      rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun2]
      rfl
    · simpa [encRules] using hM2
    · simp only [List.headD_cons]; rw [hq2, hq1]; simp [encRules]; omega
    · rw [ho11] at hek2
      exact (hek1.mono fun i hi => ⟨by omega, by simp; omega⟩).trans
        (hek2.mono fun i hi => ⟨by omega, by simp; omega⟩)
    · intro j hj
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]
        exact hH1.ekeep hek2 (fun i hi => ⟨by omega, by omega⟩) hIW2
      | succ j =>
        simp only [List.getElem_cons_succ]
        have := hH2 j (by simp at hj; omega)
        rw [ho11] at this
        have e : o.toNat + 11 + 11 * j = o.toNat + 11 * (j + 1) := by omega
        rw [e] at this
        exact this

end rules

end L.Rom
