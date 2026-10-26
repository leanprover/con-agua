import ConAgua.Arena.PromoteCIRef14

/-!
# `pci_mk`, the constant-value decoder from words, the `decCI` arms
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem cvStore_eq (m : Mem) (d a b c e : Word) :
    cvStore m d a b c e = stP d m [((0 : Word), a), ((1 : Word), b), ((2 : Word), c), ((3 : Word), e)] := by
  simp only [cvStore, stP, size_set64, UInt64.add_zero]
  by_cases h0 : (m.arr64 EREC).size ≤ d.toNat <;> by_cases h1 : (m.arr64 EREC).size ≤ (d + 1).toNat <;>
    by_cases h2 : (m.arr64 EREC).size ≤ (d + 2).toNat <;>
    by_cases h3 : (m.arr64 EREC).size ≤ (d + 3).toNat <;> simp only [h0, h1, h2, h3, or_true, or_false, ↓reduceIte]

theorem decCV_mk {A : Array Word} {d : Nat} {nm qq l t : Word} {lps : List NIdx}
    (h1 : A[d + 1]? = some nm) (h2 : A[d + 2]? = some qq) (h3 : A[d + 3]? = some l)
    (h4 : A[d + 4]? = some t) (hnm : nm.toNat < 2 ^ 32) (ht : t.toNat < 2 ^ 32)
    (hs : hslice? A qq.toNat l.toNat = some lps) :
    decCV A (d + 1) = some ⟨decI nm, lps, decI t⟩ := by
  unfold decCV
  have a1 : (hd? A (d + 1) : Option NIdx) = some (decI nm) := by simp [L.Arena.hd?, h1, hnm]
  have a2 : (hlist? A (d + 1 + 1) : Option (List NIdx)) = some lps := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    exact ⟨qq.toNat, by simp [L.Arena.nat?, show d + 1 + 1 = d + 2 from rfl, h2],
      l.toNat, by simp [L.Arena.nat?, show d + 1 + 1 + 1 = d + 3 from rfl, h3], hs⟩
  have a3 : (hd? A (d + 1 + 3) : Option EIdx) = some (decI t) := by
    simp [L.Arena.hd?, show d + 1 + 3 = d + 4 from rfl, h4, ht]
  simp [a1, a2, a3]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem cvWr_rel {n : Nat} {d a b c e : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 4 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "cv_wr" [d, a, b, c, e] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 4 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧ (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c ∧ (m'.arr64 EREC)[d.toNat + 3]? = some e := by
  obtain ⟨s', hs', -, hW⟩ := callW_triple (cvWr_spec p hp n ⟨m, Locals.init []⟩ d a b c e) hc
  simp only at hW
  rw [hs', cvStore_eq] at hW
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) hW
  refine ⟨h1, h2, fun i hi => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      show (((0 : Word)).toNat = 0) from rfl, show (((1 : Word)).toNat = 1) from rfl,
      show (((2 : Word)).toNat = 2) from rfl, show (((3 : Word)).toNat = 3) from rfl]
    omega
  · simpa using h5

/-- **`pci_mk`**: a fresh record with the kind word of `q` and the constant value words. -/
theorem pciMk_rel {n : Nat} {q k nm qq l t kw : Word} {m m' : Mem} {r : List Word}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (hk5 : 5 ≤ k.toNat)
    (hc : callW p (n + 1) "pci_mk" [q, k, nm, qq, l, t] m = some (r, m')) :
    (r.headD 0).toNat = erecTop m ∧ erecTop m' = erecTop m + k.toNat ∧ ErecGrow m m' ∧
    MemFrame [EREC] [129] m m' ∧ erecTop m + k.toNat ≤ (m'.arr64 EREC).size ∧
    (m'.arr64 EREC)[erecTop m]? = some kw ∧ (m'.arr64 EREC)[erecTop m + 1]? = some nm ∧
    (m'.arr64 EREC)[erecTop m + 2]? = some qq ∧ (m'.arr64 EREC)[erecTop m + 3]? = some l ∧
    (m'.arr64 EREC)[erecTop m + 4]? = some t := by
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciMk_spec p hp n ⟨m, Locals.init []⟩ q k nm qq l t) hc
  simp only at hW
  rw [hs'] at hW
  simp only [pciMkW] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  obtain ⟨⟨r5, ma⟩, hal, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hd5, hTa, hroom, hfa, hEa⟩ := alloc_rel p hp hal
  obtain ⟨⟨rk, mk⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm1, hr1, -⟩ := rd1_call p hp hrd
  obtain rfl := hm1.symm
  have hqa : (ma.arr64 EREC)[q.toNat]? = some kw := by rw [hEa]; exact hkw
  have hq : q.toNat < (ma.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hqa).1
  rw [rd1W_of (by rw [hEa]; exact hsz) (by simpa using hqa)] at hr1
  subst hr1
  simp only [g0, List.headD_cons] at hW
  obtain ⟨⟨rw1, mw⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  have hTa' : erecTop ma = erecTop m + k.toNat := hTa
  have hdn : (r5.headD 0).toNat = erecTop m := hd5
  obtain ⟨u1, u2, u3, u4⟩ := wr1_rel p hp (d := r5.headD 0) (by rw [hEa]; omega) (by rw [hEa]; exact hsz) hwr
  obtain ⟨⟨rw2, mc⟩, hcw, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  have e1 : (r5.headD 0 + 1).toNat = (r5.headD 0).toNat + 1 :=
    toNat_add1 _ (by have h := hroom; omega)
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := cvWr_rel p hp (d := r5.headD 0 + 1)
    (by rw [e1, u1, hEa]; omega) (by rw [u1, hEa]; exact hsz) hcw
  rw [e1] at v3 v4 v5 v6 v7
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm
  have hfr : MemFrame [EREC] [129] m mc :=
    ((hfa.mono (by simp) (by simp)).trans (u2.mono (by simp) (by simp))).trans
      (v2.mono (by simp) (by simp))
  have hTc : erecTop mc = erecTop m + k.toNat := by
    simp only [erecTop]
    rw [v2.2.1 129 (by simp), u2.2.1 129 (by simp)]
    exact hTa'
  have hszc : (mc.arr64 EREC).size = (m.arr64 EREC).size := by rw [v1, u1, hEa]
  refine ⟨by rw [← hr]; exact hdn, hTc, ⟨by omega, fun i hi => ?_, hszc⟩, hfr, by rw [hszc]; omega,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [v3 i (by omega), u3 i (by omega), hEa]
  · rw [← hdn, v3 _ (Or.inl (by omega))]; simpa using u4
  · rw [← hdn]; simpa using v4
  · rw [← hdn]; simpa using v5
  · rw [← hdn]; simpa using v6
  · rw [← hdn]; simpa using v7

end rel

end L.Arena
