module

public import ConAgua.Rom.CIReadRefRule
import ConAgua.L.WordOff
import ConAgua.Rom.CIReadRefNames
public import ConAgua.Rom.CIReadRefCV
public import ConAgua.Rom.CIReadRefCaps
import ConAgua.Arena.DeclNatCv
import ConAgua.Rom.ReadScr

@[expose] public section

/-!
# The ROM constant readers: constants (helper `decls4-rom`)

`rci_ci(q)` refines `Frontend.internCI` into a fresh `EREC` record (`decCI`), for the kinds the
pinned constants have (axioms, theorems, inductives without `sortZ` names, constructors,
recursors with plain rules: `ciFits`).
-/


open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- The constants the readers handle, fitting their encodings. -/
def ciFits : ConLeche.ConstantInfo → Bool
  | .axiomInfo v => cvFits v
  | .thmInfo v => cvFits v
  | .indInfo v c => cvFits v && capsFits c
  | .ctorInfo v nP nF T => cvFits v && decide (nP < 2 ^ 64) && decide (nF < 2 ^ 64) && nameFits T
  | .recInfo v mI rP _ rs => cvFits v && decide (mI < 2 ^ 64) && decide (rP < 2 ^ 64) &&
      decide (rs.length < 2 ^ 59) && rs.all ruleFits
  | _ => false

section ci
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_ci`'s dispatch**: the kind word read, the record of its size (the generated model's
join point `ciW.j1`). -/
theorem ciHead (kn : Nat) (sz : Word) (hsz : ciSize (UInt64.ofNat kn) = some sz) (hkn : kn < 2 ^ 64)
    (tail : List UInt8) (k : Nat) (m : Mem) (q : Word) (r : List Word) (m' : Mem)
    (hd : rom.drop q.toNat = u64B kn ++ tail)
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) :
    ciW.j1 p k (q + 8) (UInt64.ofNat kn) sz m = some (r, m') := by
  have hw := callW_model (M := fun mq => ciW p k mq q) (ci_specW rom p hL k · q) hc
  unfold ciW at hw
  replace hw := u64_some hL hw
  have e0 := u64_at hr q 0 [] kn _ (by rw [hd]; rfl) (by simp) hkn
  simp only [UInt64.add_zero] at e0
  rw [e0] at hw
  simp only [List.headD_cons] at hw
  unfold ciSize at hsz
  by_cases h0 : UInt64.ofNat kn = 0
  · rw [ite_eq_left h0] at hsz; simp only [h0, ↓reduceIte] at hw; cases hsz; rw [h0]; exact hw
  rw [ite_eq_right h0] at hsz; simp only [h0, ↓reduceIte] at hw
  by_cases h2 : UInt64.ofNat kn = 2
  · rw [ite_eq_left h2] at hsz; simp only [h2, ↓reduceIte] at hw; cases hsz; rw [h2]; exact hw
  rw [ite_eq_right h2] at hsz; simp only [h2, ↓reduceIte] at hw
  by_cases h1 : UInt64.ofNat kn = 1
  · rw [ite_eq_left h1] at hsz; simp only [h1, ↓reduceIte] at hw; cases hsz; rw [h1]; exact hw
  rw [ite_eq_right h1] at hsz; simp only [h1, ↓reduceIte] at hw
  by_cases h3 : UInt64.ofNat kn = 3
  · rw [ite_eq_left h3] at hsz; simp only [h3, ↓reduceIte] at hw; cases hsz; rw [h3]; exact hw
  rw [ite_eq_right h3] at hsz; simp only [h3, ↓reduceIte] at hw
  by_cases h4 : UInt64.ofNat kn = 4
  · rw [ite_eq_left h4] at hsz; simp only [h4, ↓reduceIte] at hw; cases hsz; rw [h4]; exact hw
  rw [ite_eq_right h4] at hsz; simp only [h4, ↓reduceIte] at hw
  by_cases h5 : UInt64.ofNat kn = 5
  · rw [ite_eq_left h5] at hsz; simp only [h5, ↓reduceIte] at hw; cases hsz; rw [h5]; exact hw
  rw [ite_eq_right h5] at hsz; simp only [h5, ↓reduceIte] at hw
  cases hsz

set_option maxHeartbeats 4000000 in
/-- **`rci_ci`'s common part**: the record allocated (`rA`), its kind word, its constant value; the
rest of the chain `K` (the kind's part, from `ciHead`'s join point unfolded) at the record and
the position after the value (`r2`). -/
theorem ciPre {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (v : ConLeche.ConstantVal) (hv : cvFits v = true) (kn : Nat) (sz : Word)
    (h5 : 5 ≤ sz.toNat)
    (tail : List UInt8) (k : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8)
    (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = u64B kn ++ ((encCV seen v).1 ++ (tail ++ rest)))
    {K : List Word → List Word → Mem → Option (List Word × Mem)}
    (hw : ntBW (callW p k "erec_alloc" [sz] m) (fun ρ₂ μ₂ =>
      ntBW (callW p k "erec_put" [ρ₂.headD 0, UInt64.ofNat kn] μ₂) fun _ μ₃ =>
        ntBW (callW p k "rci_cv" [q + 8, ρ₂.headD 0 + 1] μ₃) (K ρ₂)) = some (r, m')) :
    ∃ (rA r2 : List Word) (pp q2 : Word) (memo1 : EMemo) (icv : IConstantVal) (a1 : AState) (m2 : Mem)
      (k' : Nat), rA.headD 0 = pp ∧ r2.headD 0 = q2 ∧
      k = k' + 1 ∧ pp.toNat = erT m ∧ erT m + sz.toNat ≤ erT m2 ∧
      (Frontend.internCV memo v).run a = .ok ((memo1, icv), a1) ∧
      RInv m₀ a₀ T m2 a1 ∧ MemoR m2 (encCV seen v).2 memo1 ∧ stkTop m2 = 0 ∧
      rom.drop q2.toNat = tail ++ rest ∧ q2.toNat = q.toNat + 8 + (encCV seen v).1.length ∧
      EKeep (fun _ => False) m m2 ∧ m2.arr64 IW = m.arr64 IW ∧
      erA m2 (pp.toNat) = some (UInt64.ofNat kn) ∧
      Holds (fun i => (pp.toNat + 1 ≤ i ∧ i < pp.toNat + 5) ∨ (erT m + sz.toNat ≤ i ∧ i < erT m2))
        (fun _ => False) (fun m => decCV (erA m) (pp.toNat + CI.cv.toNat)) m2 icv ∧
      K rA r2 m2 = some (r, m') := by
  have hlt := hI.er_lt
  have hgo := hI.erT_mono
  have hrom := hr; simp only [RomOK] at hrom
  obtain ⟨r1, m1, h1, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨hI1, ho1, ht1, -, -, hIW1, -, -, hk1⟩ := hI.erAlloc (erAllocCall hL h1)
  have hf1 : MemFrame [] [129, 130] m m1 := (erAllocW_spec (erAllocCall hL h1) hI.ok).2.1
  have hM1 := hM.frameG hf1 (by simp) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.ctl 131 (by decide)
  have hlt1 := hI1.er_lt
  obtain ⟨ra, ma, ha, hw⟩ := L.Ind.ntBW_some hw
  rw [putCall hL ha] at hw
  obtain ⟨hI2, hM2, hs2, ht2, hIW2, hg2, hn2⟩ :=
    putER_facts hI1 hM1 (r1.headD 0) (UInt64.ofNat kn) (by omega) (by omega)
  cases k with
  | zero => rw [callW_zero] at hw; simp at hw
  | succ k =>
  obtain ⟨r2, m2, h2, hw⟩ := L.Ind.ntBW_some hw
  have hlen := drop_len rom _ (u64B kn) _ hd (by simp [u64B])
  simp only [u64B, List.length_cons, List.length_nil] at hlen
  have hq8 : (q + 8).toNat = q.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have hp1 : (r1.headD 0 + 1).toNat = (r1.headD 0).toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have hd8 : rom.drop (q + 8).toNat = (encCV seen v).1 ++ (tail ++ rest) := by
    rw [hq8, ← List.drop_drop, hd]; simp [u64B]
  obtain ⟨memo1, icv, a2, hrun2, hI3, hM3, hs3, hq3, hek3, ht3, hIW3, hH3⟩ :=
    cv_rel hL hr seen memo v hv k _ a _ (r1.headD 0 + 1) _ _ m2 hI2 hM2 (by rw [hs2, hs1, hst]) hd8
      (by omega) (by omega) h2
  refine ⟨r1, r2, r1.headD 0, r2.headD 0, memo1, icv, a2, m2, k, rfl, rfl, rfl, ho1, by omega, hrun2, hI3, hM3, hs3,
    ?_, ?_, ⟨by omega, fun i hi _ => ?_⟩, by rw [hIW3, hIW2, hIW1], ?_, ?_, hw⟩
  · exact drop_shift rom _ _ _ _ (by rw [hd8, List.append_assoc]) _ hq3
  · rw [hq3, hq8]
  · rw [hek3.2 i (by omega) (by omega), hn2 i (by omega) (by omega), hk1 i hi]
  · rw [hek3.2 _ (by omega) (by omega)]
    exact hg2
  · rw [hp1] at hH3
    exact hH3.mono (fun i hi => by omega) (fun _ h => h)

end ci

/-- What `rci_ci` gives, for the constant `c` at the memo `memo` (`seen`). -/
def CIPost (m₀ : Mem) (a₀ : AState) (T : Nat) (seen : List ConLeche.Expr)
    (memo : EMemo) (c : ConLeche.ConstantInfo) (m : Mem) (a : AState) (q : Word) (r : List Word)
    (m' : Mem) : Prop :=
  ∃ (memo' : EMemo) (ici : IConstantInfo) (a' : AState),
    (Frontend.internCI memo c).run a = .ok ((memo', ici), a') ∧
    RInv m₀ a₀ T m' a' ∧ MemoR m' (encCI seen c).2 memo' ∧ stkTop m' = 0 ∧
    (r.tail.headD 0).toNat = q.toNat + (encCI seen c).1.length ∧
    EKeep (fun _ => False) m m' ∧ (r.headD 0).toNat = erT m ∧ m'.arr64 IW = m.arr64 IW ∧
    Holds (fun i => erT m ≤ i ∧ i < erT m') (fun _ => False)
      (fun m => decCI (erA m) (r.headD 0).toNat) m' ici

section kinds
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- An axiom or a theorem: the constant value only. -/
theorem ci_cvOnly {m₀ : Mem} {a₀ : AState} {T : Nat}
    (seen : List ConLeche.Expr) (memo : EMemo) (v : ConLeche.ConstantVal) (hv : cvFits v = true)
    (kn : Nat) (hkn : kn = 0 ∨ kn = 2) (c : ConLeche.ConstantInfo)
    (hcE : encCI seen c = (u64B kn ++ (encCV seen v).1, (encCV seen v).2))
    (k : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8) (r : List Word) (m' : Mem)
    (hrun : ∀ memo1 icv a1, (Frontend.internCV memo v).run a = .ok ((memo1, icv), a1) →
      (Frontend.internCI memo c).run a = .ok ((memo1, if kn = 0 then .axiomInfo icv else .thmInfo icv), a1))
    (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = (encCI seen c).1 ++ rest)
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) : CIPost m₀ a₀ T seen memo c m a q r m' := by
  unfold CIPost; rw [hcE] at hd ⊢; simp only at hd ⊢
  have hsz : ciSize (UInt64.ofNat kn) = some 5 := by rcases hkn with rfl | rfl <;> rfl
  have hj := ciHead hL hr kn 5 hsz (by omega) ((encCV seen v).1 ++ ([] ++ rest)) _ m q r m'
    (by rw [hd]; simp [List.append_assoc]) hc
  unfold ciW.j1 at hj
  obtain ⟨rA, r2, pp, q2, memo1, icv, a1, m2, k', hrA, hr2, rfl, hpp, ht2, hrun2, hI2, hM2, hs2, -, hq2,
    hek2, hIW2, hw0, hH2, hw⟩ := ciPre hL hr seen memo v hv kn 5 (by decide) []
      _ m a q rest r m' hI hM hst (by rw [hd]; simp [List.append_assoc]) hj
  simp only [hrA, hr2] at hw
  replace ht2 : erT m + 5 ≤ erT m2 := ht2
  have hk1 : UInt64.ofNat kn ≠ 1 := by rcases hkn with rfl | rfl <;> decide
  have hk3 : UInt64.ofNat kn ≠ 3 := by rcases hkn with rfl | rfl <;> decide
  have hk4 : UInt64.ofNat kn ≠ 4 := by rcases hkn with rfl | rfl <;> decide
  have hk5 : UInt64.ofNat kn ≠ 5 := by rcases hkn with rfl | rfl <;> decide
  simp only [hk1, hk3, hk4, hk5, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨memo1, _, a1, hrun memo1 icv a1 hrun2, hI2, hM2, hs2, by simp [hq2, u64B]; omega, hek2,
    by simp [hpp], hIW2, ?_⟩
  intro m'' h1 h2
  simp only [List.headD_cons]
  have e0 := (h1 pp.toNat ⟨by omega, by omega⟩).trans hw0
  have ecv := hH2 m'' (fun i hi => h1 i (by omega)) (fun _ h => h.elim)
  rcases hkn with rfl | rfl
  · simp [decCI, nat?_of e0, ecv]
  · simp [decCI, nat?_of e0, ecv]

/-- A constructor: the constant value, the two counts, the family's name. -/
theorem ci_ctor {m₀ : Mem} {a₀ : AState} {T : Nat}
    (seen : List ConLeche.Expr) (memo : EMemo) (v : ConLeche.ConstantVal) (hv : cvFits v = true)
    (nP nF : Nat) (fam : ConLeche.Name) (hnP : nP < 2 ^ 64) (hnF : nF < 2 ^ 64) (hfam : nameFits fam = true)
    (k : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8) (r : List Word) (m' : Mem)
    (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = (encCI seen (.ctorInfo v nP nF fam)).1 ++ rest)
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) :
    CIPost m₀ a₀ T seen memo (.ctorInfo v nP nF fam) m a q r m' := by
  unfold CIPost
  simp only [encCI] at hd ⊢
  have hj := ciHead hL hr 4 8 rfl (by omega) ((encCV seen v).1 ++ ((u64B nP ++ u64B nF ++ encName fam) ++ rest))
    _ m q r m' (by rw [hd]; simp [List.append_assoc]) hc
  unfold ciW.j1 at hj
  obtain ⟨rA, r2, pp, q2, memo1, icv, a1, m2, k', hrA, hr2, rfl, hpp, ht2, hrun2, hI2, hM2, hs2, hd2, hq2,
    hek2, hIW2, hw0, hH2, hw⟩ := ciPre hL hr seen memo v hv 4 8 (by decide) (u64B nP ++ u64B nF ++ encName fam)
      _ m a q rest r m' hI hM hst (by rw [hd]; simp [List.append_assoc]) hj
  simp only [hrA, hr2] at hw
  replace ht2 : erT m + 8 ≤ erT m2 := ht2
  rw [show (8 : Word).toNat = 8 from rfl] at hH2
  have i1 : (UInt64.ofNat 4 = 1) = False := by decide
  have i3 : (UInt64.ofNat 4 = 3) = False := by decide
  have i4 : (UInt64.ofNat 4 = 4) = True := by decide
  simp only [i1, i3, i4, ite_false, ite_true] at hw
  replace hw := putE_some hL (u64_some hL hw)
  replace hw := putE_some hL (u64_some hL hw)
  have e1 := u64_at hr q2 0 [] nP (u64B nF ++ encName fam ++ rest)
    (by rw [hd2, List.append_assoc, List.append_assoc]; rfl) (by simp) hnP
  simp only [UInt64.add_zero] at e1
  have e2 := u64_at hr q2 8 (u64B nP) nF (encName fam ++ rest)
    (by rw [hd2, List.append_assoc, List.append_assoc]) (by simp [u64B]) hnF
  rw [e1, e2] at hw
  simp only [List.headD_cons] at hw
  have hlt := hI2.er_lt
  have hgo := hI.erT_mono
  obtain ⟨hI3, hM3, hs3, ht3, hIW3, hg3, hn3⟩ := putER_facts hI2 hM2 (pp + 5) (UInt64.ofNat nP) (by off_omega)
    (by off_omega)
  obtain ⟨hI4, hM4, hs4, ht4, hIW4, hg4, hn4⟩ := putER_facts hI3 hM3 (pp + 6) (UInt64.ofNat nF) (by off_omega)
    (by off_omega)
  have hlen := drop_len rom _ (u64B nP ++ u64B nF) _ (by rw [hd2, List.append_assoc]) (by simp [u64B])
  simp only [List.length_append, u64B, List.length_cons, List.length_nil] at hlen
  have hrom := hr; simp only [RomOK] at hrom
  -- the family's name
  generalize hm4 : erecPutMem (erecPutMem m2 (pp + 5) (UInt64.ofNat nP)) (pp + 6) (UInt64.ofNat nF) = m4
    at hw hI4 hM4 hs4 ht4 hIW4 hg4 hn4
  have hq16 : (q2 + 16).toNat = q2.toNat + 16 := by rw [UInt64.toNat_add]; simp; omega
  have hdn : rom.drop (q2 + 16).toNat = encName fam ++ rest := by
    rw [hq16, ← List.drop_drop, hd2]; simp [u64B]
  obtain ⟨r5, m5, h5, hw⟩ := L.Ind.ntBW_some hw
  obtain ⟨a5, hrun5, hA5, hk5, hlt5, hq5, hf5, hmo5⟩ := nameCall hL hr fam hfam hI4.arena hI4.mode hdn h5
  obtain ⟨hI5, -, -, hIW5, ht5, -, hE5⟩ := hI4.expr hA5 hmo5 (hf5.mono (fun b hb => by simp [ExprA, RomA, hb])
    (fun x hx => by simp [ExprC, RomC, hx])) hk5 (L.Arena.internName_ks _ _ _ _ hrun5)
  have hM5 := hM4.frameG hf5 (by decide) (by decide)
  have hs5 : stkTop m5 = stkTop m4 := hf5.ctl 131 (by decide)
  obtain ⟨rb, m6, hb, hw⟩ := L.Ind.ntBW_some hw
  rw [putCall hL hb] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hp7lt : (pp + 7).toNat < erT m5 := by rw [ht5, ht4, ht3]; off_omega
  obtain ⟨hI6, hM6, hs6, ht6, hIW6, hg6, hn6⟩ := putER_facts hI5 hM5 (pp + 7) (r5.headD 0) (by off_omega) hp7lt
  refine ⟨memo1, .ctorInfo icv nP nF (decI (r5.headD 0)), a5, ?_, hI6, hM6,
    by rw [hs6, hs5, hs4, hs3, hs2], ?_,
    ⟨by omega, fun i hi _ => ?_⟩, by simp [hpp], by rw [hIW6, hIW5, hIW4, hIW3, hIW2], ?_⟩
  · simp only [Frontend.internCI]; rw [run_bind_of _ _ _ _ _ hrun2]
    simp only [StateT.run_bind, hrun5, except_ok_bind]; rfl
  · simp only [List.tail_cons, List.headD_cons]
    rw [hq5, hq16, hq2]
    simp [u64B]; omega
  · rw [hn6 _ (by off_omega) (by omega), hE5, hn4 _ (by off_omega) (by omega),
      hn3 _ (by off_omega) (by omega)]
    exact hek2.2 i hi id
  · intro m'' h1 h2
    simp only [List.headD_cons]
    have g : ∀ i, pp.toNat ≤ i → i < pp.toNat + 8 →
        erA m'' i = erA (erecPutMem m5 (pp + 7) (r5.headD 0)) i := fun i h h' => h1 i ⟨by omega, by
          rw [ht6, ht5, ht4, ht3]; omega⟩
    have e0 : erA m'' pp.toNat = some (UInt64.ofNat 4) := by
      rw [g _ (by omega) (by omega), hn6 _ (by off_omega) (by omega), hE5,
        hn4 _ (by off_omega) (by omega), hn3 _ (by off_omega) (by omega)]
      exact hw0
    have e5 : erA m'' (pp.toNat + 5) = some (UInt64.ofNat nP) := by
      rw [g _ (by omega) (by omega), hn6 _ (by off_omega) (by omega), hE5,
        hn4 _ (by off_omega) (by omega), ← off_toNat (by omega)]
      exact hg3
    have e6 : erA m'' (pp.toNat + 6) = some (UInt64.ofNat nF) := by
      rw [g _ (by omega) (by omega), hn6 _ (by off_omega) (by omega), hE5, ← off_toNat (by omega)]
      exact hg4
    have e7 : erA m'' (pp.toNat + 7) = some (r5.headD 0) := by
      rw [g _ (by omega) (by omega), ← off_toNat (by omega)]
      exact hg6
    have ecv := ((((hH2.putER (pp + 5) (UInt64.ofNat nP) (fun i hi => ⟨by off_omega, by omega⟩) (by off_omega)).putER (pp + 6)
      (UInt64.ofNat nF) (fun i hi => ⟨by off_omega, by omega⟩) (by off_omega)).keep
        (m' := m5) (fun i _ => by rw [hE5, ← hm4]) (fun _ h => h.elim)).putER (pp + 7) (r5.headD 0)
          (fun i hi => ⟨by off_omega, by omega⟩) (by off_omega)) m'' (fun i hi => h1 i (by omega)) (fun _ h => h.elim)
    have hlt5' : (r5.head?.getD 0).toNat < 2 ^ 32 := by simpa using hlt5
    simp [decCI, nat?_of e0, ecv, nat?_of e5, nat?_of e6, hd?, e7, hlt5', L.toNat_ofNat_of_lt hnP,
      L.toNat_ofNat_of_lt hnF]

/-- An inductive. -/
theorem ci_ind {m₀ : Mem} {a₀ : AState} {T : Nat}
    (seen : List ConLeche.Expr) (memo : EMemo) (v : ConLeche.ConstantVal) (hv : cvFits v = true)
    (caps : ConLeche.IndCaps) (hcaps : capsFits caps = true)
    (k : Nat) (a : AState) (m : Mem) (q : Word) (rest : List UInt8) (r : List Word) (m' : Mem)
    (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = (encCI seen (.indInfo v caps)).1 ++ rest)
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) :
    CIPost m₀ a₀ T seen memo (.indInfo v caps) m a q r m' := by
  unfold CIPost
  simp only [encCI] at hd ⊢
  have hj := ciHead hL hr 3 20 rfl (by omega) ((encCV seen v).1 ++ ((encCaps caps) ++ rest)) _ m q r m'
    (by rw [hd]; simp [List.append_assoc]) hc
  unfold ciW.j1 at hj
  obtain ⟨rA, r2, pp, q2, memo1, icv, a1, m2, k', hrA, hr2, rfl, hpp, ht2, hrun2, hI2, hM2, hs2, hd2, hq2,
    hek2, hIW2, hw0, hH2, hw⟩ := ciPre hL hr seen memo v hv 3 20 (by decide) (encCaps caps)
      _ m a q rest r m' hI hM hst (by rw [hd]; simp [List.append_assoc]) hj
  simp only [hrA, hr2] at hw
  replace ht2 : erT m + 20 ≤ erT m2 := ht2
  rw [show (20 : Word).toNat = 20 from rfl] at hH2
  have i1 : (UInt64.ofNat 3 = 1) = False := by decide
  have i3 : (UInt64.ofNat 3 = 3) = True := by decide
  simp only [i1, i3, ite_false, ite_true] at hw
  obtain ⟨r3, m3, h3, hw⟩ := L.Ind.ntBW_some hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hlt := hI2.er_lt
  have hgo := hI.erT_mono
  have hp5 : (pp + 5).toNat = pp.toNat + 5 := by
    rw [UInt64.toNat_add, show (5 : Word).toNat = 5 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨ic, a3, hrun3, hI3, hM3, hs3, hq3, hek3, ht3, hIW3, hH3⟩ :=
    caps_rel hL hr _ memo1 caps hcaps k' m2 a1 q2 (pp + 5) rest r3 m3 hI2 hM2 hs2 hd2
      (by omega) (by omega) h3
  rw [hp5] at hek3 hH3
  refine ⟨memo1, .indInfo icv ic, a3, ?_, hI3, hM3, hs3, ?_,
    ⟨by omega, fun i hi _ => ?_⟩, by simp [hpp], by rw [hIW3, hIW2], ?_⟩
  · simp only [Frontend.internCI]; rw [run_bind_of _ _ _ _ _ hrun2, run_bind_of _ _ _ _ _ hrun3]; rfl
  · simp only [List.tail_cons, List.headD_cons]; rw [hq3, hq2]; simp [u64B]; omega
  · rw [hek3.2 i (by omega) (by omega)]; exact hek2.2 i hi id
  · intro m'' h1 h2
    simp only [List.headD_cons]
    have e0 : erA m'' pp.toNat = some (UInt64.ofNat 3) := by
      rw [h1 _ ⟨by omega, by omega⟩, hek3.2 _ (by omega) (by omega)]; exact hw0
    have ecv := (hH2.ekeep hek3 (fun i hi => ⟨by omega, by omega⟩) hIW3) m''
      (fun i hi => h1 i (by omega)) (fun _ h => h.elim)
    have ecaps := hH3 m'' (fun i hi => h1 i (by omega)) (fun _ h => h.elim)
    have : pp.toNat + 1 + 4 = pp.toNat + 5 := by omega
    simp [decCI, CI.indCaps, nat?_of e0, ecv, ecaps]

set_option maxHeartbeats 1000000 in
/-- A recursor (plain rules). -/
theorem ci_rec {m₀ : Mem} {a₀ : AState} {T : Nat}
    (seen : List ConLeche.Expr) (memo : EMemo) (v : ConLeche.ConstantVal) (hv : cvFits v = true)
    (mI rP : Nat) (isK : Bool) (rs : List ConLeche.RecRule) (hmI : mI < 2 ^ 64) (hrP : rP < 2 ^ 64)
    (hlen : rs.length < 2 ^ 59) (hrs : rs.all ruleFits = true)
    (k : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8) (r : List Word) (m' : Mem)
    (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = (encCI seen (.recInfo v mI rP isK rs)).1 ++ rest)
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) :
    CIPost m₀ a₀ T seen memo (.recInfo v mI rP isK rs) m a q r m' := by
  unfold CIPost
  simp only [encCI, bw] at hd ⊢
  have hj := ciHead hL hr 5 10 rfl (by omega) ((encCV seen v).1 ++ ((u64B mI ++ (u64B rP ++ (u64B (if isK then 1 else 0) ++ (u64B rs.length ++ (encRules (encCV seen v).2 rs).1)))) ++ rest)) _ m q r m'
    (by rw [hd]; simp [List.append_assoc]) hc
  unfold ciW.j1 at hj
  obtain ⟨rA, r2, pp, q2, memo1, icv, a1, m2, k', hrA, hr2, rfl, hpp, ht2, hrun2, hI2, hM2, hs2, hd2, hq2,
    hek2, hIW2, hw0, hH2, hw⟩ := ciPre hL hr seen memo v hv 5 10 (by decide) (u64B mI ++ (u64B rP ++ (u64B (if isK then 1 else 0) ++ (u64B rs.length ++ (encRules (encCV seen v).2 rs).1))))
      _ m a q rest r m' hI hM hst (by rw [hd]; simp [List.append_assoc]) hj
  simp only [hrA, hr2] at hw
  replace ht2 : erT m + 10 ≤ erT m2 := ht2
  rw [show (10 : Word).toNat = 10 from rfl] at hH2
  have i1 : (UInt64.ofNat 5 = 1) = False := by decide
  have i3 : (UInt64.ofNat 5 = 3) = False := by decide
  have i4 : (UInt64.ofNat 5 = 4) = False := by decide
  have i5 : (UInt64.ofNat 5 = 5) = True := by decide
  simp only [i1, i3, i4, i5, ite_false, ite_true] at hw
  replace hw := putE_some hL (u64_some hL hw)
  replace hw := putE_some hL (u64_some hL hw)
  replace hw := putE_some hL (u64_some hL hw)
  replace hw := u64_some hL hw
  have hb : (if isK then 1 else 0) < 2 ^ 64 := by cases isK <;> decide
  have e1 := u64_at hr q2 0 [] mI _ (by rw [hd2]; rfl) (by simp) hmI
  simp only [UInt64.add_zero] at e1
  have e2 := u64_at hr q2 8 (u64B mI) rP _ (by rw [hd2]; rfl) (by simp [u64B]) hrP
  have e3 := u64_at hr q2 16 (u64B mI ++ u64B rP) (if isK then 1 else 0) _
    (by rw [hd2]; repeat rw [List.append_assoc]) (by simp [u64B]) hb
  have e4 := u64_at hr q2 24 (u64B mI ++ u64B rP ++ u64B (if isK then 1 else 0)) rs.length _
    (by rw [hd2]; repeat rw [List.append_assoc]) (by simp [u64B]) (by omega)
  rw [e1, e2, e3, e4] at hw
  simp only [List.headD_cons] at hw
  generalize hkw : UInt64.ofNat (if isK then 1 else 0) = kw at hw
  have hlt := hI2.er_lt
  have hgo := hI.erT_mono
  have hrom := hr; simp only [RomOK] at hrom
  change ntBW (callW p (k' + 1) "erec_alloc" [11 * UInt64.ofNat rs.length]
    (putERs m2 [(pp + 5, UInt64.ofNat mI), (pp + 6, UInt64.ofNat rP), (pp + 9, kw)])) _ = _ at hw
  generalize hws : [(pp + 5, UInt64.ofNat mI), (pp + 6, UInt64.ofNat rP), (pp + 9, kw)] = ws at hw
  have hwsB : ∀ jw ∈ ws, erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT m2 := by
    intro jw hjw; rw [← hws] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl | rfl <;> constructor <;> off_omega
  have hws41 : ∀ jw ∈ ws, jw.1.toNat < 2 ^ 41 := fun jw h => by have := (hwsB jw h).2; omega
  obtain ⟨hI4, hM4, hs4, ht4, hIW4⟩ := putERs_facts ws m2 hI2 hM2 hwsB
  have hget4 : ∀ j w, (j, w) ∈ ws → erA (putERs m2 ws) j.toNat = some w := by
    intro j w hjw
    refine putERs_get ws m2 j w hI2 hwsB ?_ hjw
    rw [← hws]; simp (disch := omega) only [off_toNat, List.map_cons, List.map_nil]; simp
  have hne4 : ∀ i, i < erT m2 → i ≠ pp.toNat + 5 → i ≠ pp.toNat + 6 → i ≠ pp.toNat + 9 →
      erA (putERs m2 ws) i = erA m2 i := fun i hi h5 h6 h9 =>
    putERs_ne ws m2 i (by
      intro jw hjw; rw [← hws] at hjw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
      rcases hjw with rfl | rfl | rfl <;> off_omega) (by omega) hws41
  have h11 : (11 * UInt64.ofNat rs.length).toNat = 11 * rs.length := by
    rw [UInt64.toNat_mul, L.toNat_ofNat_of_lt (by omega)]; simp; omega
  cases h4 : callW p (k' + 1) "erec_alloc" [11 * UInt64.ofNat rs.length] (putERs m2 ws) with
  | none => rw [h4] at hw; simp at hw
  | some t4 =>
  obtain ⟨r4, m5⟩ := t4
  rw [h4, bW_some] at hw
  obtain ⟨hI5, ho5, ht5, -, -, hIW5, -, -, hk5⟩ := hI4.erAlloc (erAllocCall hL h4)
  rw [h11] at ht5
  have hf5 : MemFrame [] [129, 130] (putERs m2 ws) m5 := (erAllocW_spec (erAllocCall hL h4) hI4.ok).2.1
  have hM5 := hM4.frameG hf5 (by simp) (by decide)
  have hs5 : stkTop m5 = stkTop (putERs m2 ws) := hf5.ctl 131 (by decide)
  replace hw := putE_some hL (putE_some hL hw)
  change ntBW (callW p (k' + 1) "rci_rules_to" [q2 + 32, r4.headD 0, UInt64.ofNat rs.length]
    (putERs m5 [(pp + 7, r4.headD 0), (pp + 8, UInt64.ofNat rs.length)])) _ = _ at hw
  generalize hws' : [(pp + 7, r4.headD 0), (pp + 8, UInt64.ofNat rs.length)] = ws' at hw
  have hwsB' : ∀ jw ∈ ws', erT m₀ ≤ jw.1.toNat ∧ jw.1.toNat < erT m5 := by
    intro jw hjw; rw [← hws'] at hjw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
    rcases hjw with rfl | rfl <;> constructor <;> off_omega
  have hws41' : ∀ jw ∈ ws', jw.1.toNat < 2 ^ 41 := fun jw h => by have := (hwsB' jw h).2; have := hI5.er_lt; omega
  obtain ⟨hI7, hM7, hs7, ht7, hIW7⟩ := putERs_facts ws' m5 hI5 hM5 hwsB'
  have hget7 : ∀ j w, (j, w) ∈ ws' → erA (putERs m5 ws') j.toNat = some w := by
    intro j w hjw
    refine putERs_get ws' m5 j w hI5 hwsB' ?_ hjw
    rw [← hws']; simp (disch := omega) only [off_toNat, List.map_cons, List.map_nil]; simp
  have hne7 : ∀ i, i < erT m2 → i ≠ pp.toNat + 7 → i ≠ pp.toNat + 8 →
      erA (putERs m5 ws') i = erA (putERs m2 ws) i := fun i hi h7 h8 => by
    rw [putERs_ne ws' m5 i (by
      intro jw hjw; rw [← hws'] at hjw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hjw
      rcases hjw with rfl | rfl <;> off_omega) (by omega) hws41', hk5 i (by omega)]
  obtain ⟨r5, m6, h5, hw⟩ := L.Ind.ntBW_some hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hlenR := drop_len rom _ (u64B mI ++ u64B rP ++ u64B (if isK then 1 else 0) ++ u64B rs.length) _
    (by rw [hd2]; repeat rw [List.append_assoc]) (by simp [u64B])
  simp only [List.length_append, u64B, List.length_cons, List.length_nil] at hlenR
  have hq32 : (q2 + 32).toNat = q2.toNat + 32 := by
    rw [UInt64.toNat_add, show (32 : Word).toNat = 32 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have hd32 : rom.drop (q2 + 32).toNat = (encRules (encCV seen v).2 rs).1 ++ rest := by
    rw [hq32, ← List.drop_drop, hd2]; simp [u64B]
  obtain ⟨memo2, irs, a3, hrun3, hlen3, hI8, hM8, hs8, hq8, hek8, ht8, hIW8, hH8⟩ :=
    rulesTo_rel hL hr rs hrs _ memo1 (k' + 1) _ a1 _ (r4.headD 0) _ rest r5 m6 hI7 hM7
      (by rw [hs7, hs5, hs4, hs2]) hd32 (L.toNat_ofNat_of_lt (by omega)) (by omega) (by omega) h5
  -- the earlier words through the rules
  have hk8 : ∀ i, i < erT m2 → erA m6 i = erA (putERs m5 ws') i := fun i hi =>
    hek8.2 i (by omega) (by omega)
  have hkey : ∀ i, i < erT m2 → i ≠ pp.toNat + 5 → i ≠ pp.toNat + 6 → i ≠ pp.toNat + 7 →
      i ≠ pp.toNat + 8 → i ≠ pp.toNat + 9 → erA m6 i = erA m2 i := fun i hi h5 h6 h7 h8 h9 => by
    rw [hk8 i hi, hne7 i hi h7 h8, hne4 i hi h5 h6 h9]
  refine ⟨memo2, .recInfo icv mI rP isK irs, a3, ?_, hI8, hM8, hs8, ?_,
    ⟨by omega, fun i hi _ => ?_⟩, by simp [hpp], by rw [hIW8, hIW7, hIW5, hIW4, hIW2], ?_⟩
  · simp only [Frontend.internCI]; rw [run_bind_of _ _ _ _ _ hrun2, run_bind_of _ _ _ _ _ hrun3]; rfl
  · simp only [List.tail_cons, List.headD_cons]; rw [hq8, hq32, hq2]; simp [u64B]; omega
  · rw [hkey i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hek2.2 i hi id
  · intro m'' h1 h2
    simp only [List.headD_cons]
    have g : ∀ i, pp.toNat ≤ i → i < pp.toNat + 10 → erA m'' i = erA m6 i := fun i h h' =>
      h1 i ⟨by omega, by omega⟩
    have e0 : erA m'' pp.toNat = some (UInt64.ofNat 5) := by
      rw [g _ (by omega) (by omega), hkey _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hw0
    have w5 := hget4 (pp + 5) (UInt64.ofNat mI) (by rw [← hws]; simp)
    have w6 := hget4 (pp + 6) (UInt64.ofNat rP) (by rw [← hws]; simp)
    have w9 := hget4 (pp + 9) kw (by rw [← hws]; simp)
    have w7 := hget7 (pp + 7) (r4.headD 0) (by rw [← hws']; simp)
    have w8 := hget7 (pp + 8) (UInt64.ofNat rs.length) (by rw [← hws']; simp)
    rw [off_toNat (by omega)] at w5 w6 w7 w8 w9
    have e5 : erA m'' (pp.toNat + 5) = some (UInt64.ofNat mI) := by
      rw [g _ (by omega) (by omega), hk8 _ (by omega), hne7 _ (by omega) (by omega) (by omega)]; exact w5
    have e6 : erA m'' (pp.toNat + 6) = some (UInt64.ofNat rP) := by
      rw [g _ (by omega) (by omega), hk8 _ (by omega), hne7 _ (by omega) (by omega) (by omega)]; exact w6
    have e9 : erA m'' (pp.toNat + 9) = some kw := by
      rw [g _ (by omega) (by omega), hk8 _ (by omega), hne7 _ (by omega) (by omega) (by omega)]; exact w9
    have e7 : erA m'' (pp.toNat + 7) = some (r4.headD 0) := by
      rw [g _ (by omega) (by omega), hk8 _ (by omega)]; exact w7
    have e8 : erA m'' (pp.toNat + 8) = some (UInt64.ofNat rs.length) := by
      rw [g _ (by omega) (by omega), hk8 _ (by omega)]; exact w8
    have ecv : decCV (erA m'') (pp.toNat + CI.cv.toNat) = some icv := by
      refine hH2 m'' (fun i hi => ?_) (fun _ h => h.elim)
      rw [h1 i (by omega), hkey i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    have erules : decRules (erA m'') (r4.headD 0).toNat rs.length = some irs := by
      rw [← hlen3]
      exact holds_mapM_range (g := fun m j => decRule (erA m) ((r4.headD 0).toNat + 11 * j))
        (SE := fun i => ((r4.headD 0).toNat ≤ i ∧ i < (r4.headD 0).toNat + 11 * rs.length) ∨
          (erT (putERs m5 ws') ≤ i ∧ i < erT m6))
        (SI := fun _ => False) irs
        (fun j hj => (hH8 j hj).mono (fun i hi => by
          rcases hi with hi | hi
          · left; omega
          · right; exact hi) (fun _ h => h)) m''
        (fun i hi => h1 i (by rcases hi with hi | hi <;> omega)) (fun _ h => h.elim)
    rw [← hkw] at e9
    simp [decCI, nat?_of e0, ecv, nat?_of e5, nat?_of e6, bool?_of e9, nat?_of e7, nat?_of e8,
      L.toNat_ofNat_of_lt hmI, L.toNat_ofNat_of_lt hrP, L.toNat_ofNat_of_lt (show rs.length < 2 ^ 64 by omega), bw_ne]
    simp at erules; simp [erules]

/-- **`rci_ci` refines `Frontend.internCI`** for the constants `ciFits` admits. -/
@[refines_part ConRon.Arena.Frontend.internCI "the pinned constants' kinds"]
theorem ci_rel {m₀ : Mem} {a₀ : AState} {T : Nat}
    (seen : List ConLeche.Expr) (memo : EMemo) (c : ConLeche.ConstantInfo) (hfit : ciFits c = true)
    (k : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8) (r : List Word) (m' : Mem)
    (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = (encCI seen c).1 ++ rest)
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) :
    CIPost m₀ a₀ T seen memo c m a q r m' := by
  cases c with
  | axiomInfo v =>
    exact ci_cvOnly hL hr seen memo v hfit 0 (.inl rfl) _ rfl k m a q rest r m'
      (fun memo1 icv a1 h => by
        simp only [Frontend.internCI]; rw [run_bind_of _ _ _ _ _ h]; rfl) hI hM hst hd hc
  | thmInfo v =>
    exact ci_cvOnly hL hr seen memo v hfit 2 (.inr rfl) _ rfl k m a q rest r m'
      (fun memo1 icv a1 h => by
        simp only [Frontend.internCI]; rw [run_bind_of _ _ _ _ _ h]; rfl) hI hM hst hd hc
  | indInfo v caps =>
    simp only [ciFits, Bool.and_eq_true] at hfit
    exact ci_ind hL hr seen memo v hfit.1 caps hfit.2 k a m q rest r m' hI hM hst hd hc
  | ctorInfo v nP nF fam =>
    simp only [ciFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
    exact ci_ctor hL hr seen memo v hfit.1.1.1 nP nF fam hfit.1.1.2 hfit.1.2 hfit.2 k m a q rest r m' hI hM hst hd hc
  | recInfo v mI rP isK rs =>
    simp only [ciFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
    exact ci_rec hL hr seen memo v hfit.1.1.1.1 mI rP isK rs hfit.1.1.1.2 hfit.1.1.2 hfit.1.2 hfit.2
      k m a q rest r m' hI hM hst hd hc
  | defnInfo v e h => simp [ciFits] at hfit

end kinds

end L.Rom
