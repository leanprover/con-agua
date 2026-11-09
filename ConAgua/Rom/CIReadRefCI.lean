module

public import ConAgua.Rom.CIReadRefRule
import ConAgua.L.WordOff
import ConAgua.Rom.CIReadRefNames
public import ConAgua.Rom.CIReadRefCV
public import ConAgua.Rom.CIReadRefCaps

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
  | .ctorInfo v nP nF => cvFits v && decide (nP < 2 ^ 64) && decide (nF < 2 ^ 64)
  | .recInfo v mI rP _ rs => cvFits v && decide (mI < 2 ^ 64) && decide (rP < 2 ^ 64) &&
      decide (rs.length < 2 ^ 59) && rs.all ruleFits
  | _ => false

theorem rdU_ntBW {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m : Mem} {i : Word}
    {k : Word → Mem → Option (List Word × Mem)} {f : List Word → Mem → Option (List Word × Mem)}
    {v : List Word × Mem} (h : ntBW (rdU p n m i k) f = some v) : ntBW (k (u64W rom i) m) f = some v := by
  change ntBW (ntBW (callW p n "rom_u64_c" [i] m) (fun r m' => k (r.headD 0) m')) f = some v at h
  cases hc : callW p n "rom_u64_c" [i] m with
  | none => rw [hc] at h; simp at h
  | some t =>
    obtain ⟨r, m'⟩ := t
    rw [hc, bW_some] at h
    obtain ⟨rfl, rfl⟩ := u64Call hL hc
    exact h

theorem putE_ntBW {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m : Mem} {i w : Word}
    {k : Mem → Option (List Word × Mem)} {f : List Word → Mem → Option (List Word × Mem)}
    {v : List Word × Mem} (h : ntBW (putE p n m i w k) f = some v) :
    ntBW (k (erecPutMem m i w)) f = some v := by
  change ntBW (ntBW (callW p n "erec_put" [i, w] m) (fun _ m' => k m')) f = some v at h
  cases hc : callW p n "erec_put" [i, w] m with
  | none => rw [hc] at h; simp at h
  | some t =>
    obtain ⟨r, m'⟩ := t
    rw [hc, bW_some] at h
    rw [← putCall hL hc]; exact h

section ci
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

set_option maxHeartbeats 4000000 in
/-- **`rci_ci`'s common part**: the kind word, the record allocated, its constant value. -/
theorem ciPre {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (v : ConLeche.ConstantVal) (hv : cvFits v = true) (kn : Nat) (sz : Word)
    (hsz : ciSize (UInt64.ofNat kn) = some sz) (h5 : 5 ≤ sz.toNat) (hkn : kn < 2 ^ 64)
    (tail : List UInt8) (k : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8)
    (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = u64B kn ++ ((encCV seen v).1 ++ (tail ++ rest)))
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) :
    ∃ (pp : Word) (memo1 : EMemo) (icv : IConstantVal) (a1 : AState) (m2 : Mem) (q2 : Word) (k' : Nat),
      k = k' + 1 ∧ pp.toNat = erT m ∧ erT m + sz.toNat ≤ erT m2 ∧
      (Frontend.internCV memo v).run a = .ok ((memo1, icv), a1) ∧
      RInv m₀ a₀ T m2 a1 ∧ MemoR m2 (encCV seen v).2 memo1 ∧ stkTop m2 = 0 ∧
      rom.drop q2.toNat = tail ++ rest ∧ q2.toNat = q.toNat + 8 + (encCV seen v).1.length ∧
      EKeep (fun _ => False) m m2 ∧ m2.arr64 IW = m.arr64 IW ∧
      erA m2 (pp.toNat) = some (UInt64.ofNat kn) ∧
      Holds (fun i => (pp.toNat + 1 ≤ i ∧ i < pp.toNat + 5) ∨ (erT m + sz.toNat ≤ i ∧ i < erT m2))
        (fun _ => False) (fun m => decCV (erA m) (pp.toNat + 1)) m2 icv ∧
      ntBW (ciTailW p k m2 (UInt64.ofNat kn) pp q2) (fun r3 m3 => some ([pp, r3.headD 0], m3)) =
        some (r, m') := by
  have hw := callW_model (M := fun mq => ciW p k mq q) (ci_specW rom p hL k · q) hc
  unfold ciW at hw
  replace hw := rdU_some hL hw
  have e0 := u64_at hr q 0 [] kn _ (by rw [hd]; rfl) (by simp) hkn
  simp only [UInt64.add_zero] at e0
  rw [e0, hsz] at hw
  simp only at hw
  have hlt := hI.er_lt
  have hgo := hI.erT_mono
  have hrom := hr; simp only [RomOK] at hrom
  obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
  obtain ⟨hI1, ho1, ht1, -, -, hIW1, -, -, hk1⟩ := hI.erAlloc (erAllocCall hL h1)
  have hf1 : MemFrame [] [129, 130] m m1 := (erAllocW_spec (erAllocCall hL h1) hI.ok).2.1
  have hM1 := hM.frameG hf1 (by simp) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.ctl 131 (by decide)
  have hlt1 := hI1.er_lt
  obtain ⟨ra, ma, ha, hw⟩ := ntBW_inv hw
  rw [putCall hL ha] at hw
  obtain ⟨hI2, hM2, hs2, ht2, hIW2, hg2, hn2⟩ :=
    putER_facts hI1 hM1 (r1.headD 0) (UInt64.ofNat kn) (by omega) (by omega)
  cases k with
  | zero => dsimp only at hw; rw [callW_zero] at hw; simp at hw
  | succ k =>
  obtain ⟨r2, m2, h2, hw⟩ := ntBW_inv hw
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
  refine ⟨r1.headD 0, memo1, icv, a2, m2, r2.headD 0, k, rfl, ho1, by omega, hrun2, hI3, hM3, hs3,
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
  obtain ⟨pp, memo1, icv, a1, m2, q2, k', rfl, hpp, ht2, hrun2, hI2, hM2, hs2, -, hq2, hek2, hIW2,
    hw0, hH2, hw⟩ := ciPre hL hr seen memo v hv kn 5 hsz (by decide) (by omega) [] _ m a q rest r m'
      hI hM hst (by rw [hd]; simp [List.append_assoc]) hc
  replace ht2 : erT m + 5 ≤ erT m2 := ht2
  have hk1 : UInt64.ofNat kn ≠ 1 := by rcases hkn with rfl | rfl <;> decide
  have hk3 : UInt64.ofNat kn ≠ 3 := by rcases hkn with rfl | rfl <;> decide
  have hk4 : UInt64.ofNat kn ≠ 4 := by rcases hkn with rfl | rfl <;> decide
  have hk5 : UInt64.ofNat kn ≠ 5 := by rcases hkn with rfl | rfl <;> decide
  simp only [ciTailW, hk1, hk3, hk4, hk5, ite_false, bW_some, Option.some.injEq, Prod.mk.injEq] at hw
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

/-- A constructor. -/
theorem ci_ctor {m₀ : Mem} {a₀ : AState} {T : Nat}
    (seen : List ConLeche.Expr) (memo : EMemo) (v : ConLeche.ConstantVal) (hv : cvFits v = true)
    (nP nF : Nat) (hnP : nP < 2 ^ 64) (hnF : nF < 2 ^ 64)
    (k : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8) (r : List Word) (m' : Mem)
    (hI : RInv m₀ a₀ T m a) (hM : MemoR m seen memo) (hst : stkTop m = 0)
    (hd : rom.drop q.toNat = (encCI seen (.ctorInfo v nP nF)).1 ++ rest)
    (hc : callW p (k + 1) "rci_ci" [q] m = some (r, m')) :
    CIPost m₀ a₀ T seen memo (.ctorInfo v nP nF) m a q r m' := by
  unfold CIPost
  simp only [encCI] at hd ⊢
  obtain ⟨pp, memo1, icv, a1, m2, q2, k', rfl, hpp, ht2, hrun2, hI2, hM2, hs2, hd2, hq2, hek2, hIW2,
    hw0, hH2, hw⟩ := ciPre hL hr seen memo v hv 4 7 rfl (by decide) (by omega) (u64B nP ++ u64B nF)
      _ m a q rest r m' hI hM hst (by rw [hd]; simp [List.append_assoc]) hc
  replace ht2 : erT m + 7 ≤ erT m2 := ht2
  rw [show (7 : Word).toNat = 7 from rfl] at hH2
  have i1 : (UInt64.ofNat 4 = 1) = False := by decide
  have i3 : (UInt64.ofNat 4 = 3) = False := by decide
  have i4 : (UInt64.ofNat 4 = 4) = True := by decide
  simp only [ciTailW, ciCtorW, i1, i3, i4, ite_false, ite_true] at hw
  replace hw := putE_ntBW hL (rdU_ntBW hL hw)
  replace hw := putE_ntBW hL (rdU_ntBW hL hw)
  have e1 := u64_at hr q2 0 [] nP (u64B nF ++ rest) (by rw [hd2, List.append_assoc]; rfl) (by simp) hnP
  simp only [UInt64.add_zero] at e1
  have e2 := u64_at hr q2 8 (u64B nP) nF rest (by rw [hd2, List.append_assoc]) (by simp [u64B]) hnF
  rw [e1, e2] at hw
  simp only [bW_some, Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hlt := hI2.er_lt
  have hgo := hI.erT_mono
  obtain ⟨hI3, hM3, hs3, ht3, hIW3, hg3, hn3⟩ := putER_facts hI2 hM2 (pp + 5) (UInt64.ofNat nP) (by off_omega)
    (by off_omega)
  obtain ⟨hI4, hM4, hs4, ht4, hIW4, hg4, hn4⟩ := putER_facts hI3 hM3 (pp + 6) (UInt64.ofNat nF) (by off_omega)
    (by off_omega)
  have hlen := drop_len rom _ (u64B nP ++ u64B nF) _ (by rw [hd2]) (by simp [u64B])
  simp only [List.length_append, u64B, List.length_cons, List.length_nil] at hlen
  have hrom := hr; simp only [RomOK] at hrom
  refine ⟨memo1, .ctorInfo icv nP nF, a1, ?_, hI4, hM4, by rw [hs4, hs3, hs2], ?_,
    ⟨by omega, fun i hi _ => ?_⟩, by simp [hpp], by rw [hIW4, hIW3, hIW2], ?_⟩
  · simp only [Frontend.internCI]; rw [run_bind_of _ _ _ _ _ hrun2]; rfl
  · simp only [List.tail_cons, List.headD_cons]
    rw [off_toNat (by omega), hq2]
    simp [u64B]; omega
  · rw [hn4 _ (by off_omega) (by omega), hn3 _ (by off_omega) (by omega)]
    exact hek2.2 i hi id
  · intro m'' h1 h2
    simp only [List.headD_cons]
    have g : ∀ i, pp.toNat ≤ i → i < pp.toNat + 7 →
        erA m'' i = erA (erecPutMem (erecPutMem m2 (pp + 5) (UInt64.ofNat nP)) (pp + 6)
          (UInt64.ofNat nF)) i := fun i h h' => h1 i ⟨by omega, by omega⟩
    have e0 : erA m'' pp.toNat = some (UInt64.ofNat 4) := by
      rw [g _ (by omega) (by omega), hn4 _ (by off_omega) (by omega), hn3 _ (by off_omega) (by omega)]
      exact hw0
    have e5 : erA m'' (pp.toNat + 5) = some (UInt64.ofNat nP) := by
      rw [g _ (by omega) (by omega), hn4 _ (by off_omega) (by omega), ← off_toNat (by omega)]
      exact hg3
    have e6 : erA m'' (pp.toNat + 6) = some (UInt64.ofNat nF) := by
      rw [g _ (by omega) (by omega), ← off_toNat (by omega)]
      exact hg4
    have ecv := ((hH2.putER (pp + 5) (UInt64.ofNat nP) (fun i hi => ⟨by off_omega, by omega⟩) (by off_omega)).putER (pp + 6)
      (UInt64.ofNat nF) (fun i hi => ⟨by off_omega, by omega⟩) (by off_omega)) m'' (fun i hi => h1 i (by omega)) (fun _ h => h.elim)
    simp [decCI, nat?_of e0, ecv, nat?_of e5, nat?_of e6, ofNat_toNat_lt hnP, ofNat_toNat_lt hnF]

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
  obtain ⟨pp, memo1, icv, a1, m2, q2, k', rfl, hpp, ht2, hrun2, hI2, hM2, hs2, hd2, hq2, hek2, hIW2,
    hw0, hH2, hw⟩ := ciPre hL hr seen memo v hv 3 20 rfl (by decide) (by omega) (encCaps caps)
      _ m a q rest r m' hI hM hst (by rw [hd]; simp [List.append_assoc]) hc
  replace ht2 : erT m + 20 ≤ erT m2 := ht2
  rw [show (20 : Word).toNat = 20 from rfl] at hH2
  have i1 : (UInt64.ofNat 3 = 1) = False := by decide
  have i3 : (UInt64.ofNat 3 = 3) = True := by decide
  simp only [ciTailW, i1, i3, ite_false, ite_true] at hw
  obtain ⟨r3, m3, h3, hw⟩ := ntBW_inv hw
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
    simp [decCI, nat?_of e0, ecv, ecaps]

end kinds

end L.Rom
