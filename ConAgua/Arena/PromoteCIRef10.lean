import ConAgua.Arena.PromoteCIRef9

/-!
# `promote_caps` refines `promoteCaps`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem decCaps_words {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {caps : IIndCaps} (h : decCaps a dn q = some caps) :
    hd? a (q + 1) = some caps.etaCtor ∧ hlist? a (q + 10) = some caps.all ∧
      hlist? a (q + 13) = some caps.ctors := by
  unfold decCaps at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, e8, h8, e9, h9, e10, h10,
    e11, h11, rfl⟩ := h
  exact ⟨h2, h9, h11⟩

theorem promoteCaps_eq (pm : PMemo) (fuel : Nat) (c : IIndCaps) :
    promoteCaps pm fuel c = (do
      let (m, ct) ← promoteN pm fuel c.etaCtor
      let (m, al) ← promoteNList m fuel c.all
      let (m, cs) ← promoteNList m fuel c.ctors
      pure (m, { c with etaCtor := ct, all := al, ctors := cs })) := rfl

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem capsWr_rel' {n : Nat} {d c a k : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 14 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "caps_wr" [d, c, a, k] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, i ≠ d.toNat + 1 → i ≠ d.toNat + 10 → i ≠ d.toNat + 13 →
      (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some c ∧ (m'.arr64 EREC)[d.toNat + 10]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 13]? = some k := by
  have h := capsWr_call p hp hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi1 hi2 hi3 => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      show (((1 : Word)).toNat = 1) from rfl, show (((10 : Word)).toNat = 10) from rfl,
      show (((13 : Word)).toNat = 13) from rfl]
    omega
  · simpa using h5

theorem projWr_rel' {n : Nat} {d tn sn lp c ss bs gs : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 12 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "proj_wr" [d, tn, sn, lp, c, ss, bs, gs] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, i ≠ d.toNat + 1 → i ≠ d.toNat + 2 → i ≠ d.toNat + 3 → i ≠ d.toNat + 6 →
      i ≠ d.toNat + 8 → i ≠ d.toNat + 9 → i ≠ d.toNat + 11 →
      (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some tn ∧ (m'.arr64 EREC)[d.toNat + 2]? = some sn ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some lp ∧ (m'.arr64 EREC)[d.toNat + 6]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 8]? = some ss ∧ (m'.arr64 EREC)[d.toNat + 9]? = some bs ∧
    (m'.arr64 EREC)[d.toNat + 11]? = some gs := by
  have h := projWr_call p hp hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := stP_nat d _ (by simp; omega) (by simp) h
  refine ⟨h1, h2, fun i hi1 hi2 hi3 hi4 hi5 hi6 hi7 => h3 i ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      show (((1 : Word)).toNat = 1) from rfl, show (((2 : Word)).toNat = 2) from rfl,
      show (((3 : Word)).toNat = 3) from rfl, show (((6 : Word)).toNat = 6) from rfl,
      show (((8 : Word)).toNat = 8) from rfl, show (((9 : Word)).toNat = 9) from rfl,
      show (((11 : Word)).toNat = 11) from rfl]
    omega
  · simpa using h5

theorem caps_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f s d : Word) (D : Nat)
    (dn : NIdx → Option ConLeche.Name) (caps : IIndCaps) (r : List Word) (m' : Mem)
    (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcaps : decCaps (preE m D) dn s.toNat = some caps) (hsD : s.toNat + 15 ≤ D)
    (hDt : D ≤ erecTop m) (hdD : D ≤ d.toNat) (hdT : d.toNat + 15 ≤ erecTop m)
    (hc : callW p n "promote_caps" [f, s, d] m = some (r, m')) :
    ∃ a' pm' caps', (promoteCaps pm f.toNat caps).run a = .ok ((pm', caps'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ SlotGrow m m' d.toNat (d.toNat + 15) ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧ decCaps (erecP m') dn d.toNat = some caps' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteCaps_spec p hp n ⟨m, Locals.init []⟩ f s d) hc
  simp only at hW
  rw [hs'] at hW
  simp only [capsW] at hW
  obtain ⟨hec, hall, hcts⟩ := decCaps_words hcaps
  -- the parts
  cases hca : callW p n "caps_parts" [f, s] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨cr, m₃⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := callW_triple (capsParts_spec p hp n ⟨m, Locals.init []⟩ f s) hca
  rw [hs1] at hW1
  simp only [capsPW] at hW1
  have e1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e10 : (s + 10).toNat = s.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have e13 : (s + 13).toNat = s.toNat + 13 := by rw [UInt64.toNat_add]; simp; omega
  -- name
  have hd1 : hd? (erecP m) (s + 1).toNat = some caps.etaCtor := by
    rw [e1]; exact (preE_mono m hDt).hd? hec
  cases hcb : callW p n "pn_at" [f, s + 1] m with
  | none => rw [hcb] at hW1; cases hW1
  | some x =>
  obtain ⟨c, m₁⟩ := x
  rw [hcb] at hW1
  simp only [Option.bind_some] at hW1
  obtain ⟨a1, pm1, hrun1, hD1, hP1, hpw1, hcp1, hfr1⟩ :=
    pnAt_rel p hp n m a pm f (s + 1) caps.etaCtor c m₁ hD hP hsz hd1 hcb
  obtain ⟨hE1, hT1⟩ := eFrame_erec hfr1
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hE1]; exact hsz
  have hP1' : erecP m₁ = erecP m := by rw [erecP_eq_preE, erecP_eq_preE, hT1]; exact preE_congr hE1 _
  -- all
  have hl10 : hlist? (erecP m₁) (s + 10).toNat = some caps.all := by
    rw [hP1', e10]; exact (preE_mono m hDt).hlist? hall
  cases hcc : callW p n "ps_at" [0, f, s + 10] m₁ with
  | none => rw [hcc] at hW1; cases hW1
  | some x =>
  obtain ⟨x1, m₂⟩ := x
  rw [hcc] at hW1
  simp only [Option.bind_some] at hW1
  obtain ⟨wo1, wl1, hn1, hn1', hsl1, a2, pm2, al', hrun2, hD2, hP2, hcp2, hfr2, hq2, hg2, hT2, hts2,
    hsl2⟩ := psAt0_rel p hp n m₁ a1 pm1 f (s + 10) caps.all x1 m₂ hD1 hP1 hsz1 hl10 hcc
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hg2.2.2]; exact hsz1
  -- ctors
  have hl13 : hlist? (erecP m₂) (s + 13).toNat = some caps.ctors := by
    rw [e13]
    exact hg2.ext.hlist? (by rw [hP1']; exact (preE_mono m hDt).hlist? hcts)
  cases hcd : callW p n "ps_at" [0, f, s + 13] m₂ with
  | none => rw [hcd] at hW1; cases hW1
  | some x =>
  obtain ⟨x2, m₃'⟩ := x
  rw [hcd] at hW1
  simp only [Option.bind_some] at hW1
  obtain ⟨wo2, wl2, hn2, hn2', hsl2', a3, pm3, cs', hrun3, hD3, hP3, hcp3, hfr3, hq3, hg3, hT3, hts3,
    hsl3⟩ := psAt0_rel p hp n m₂ a2 pm2 f (s + 13) caps.ctors x2 m₃' hD2 hP2 hsz2 hl13 hcd
  obtain ⟨hlist, hm3⟩ := Prod.mk.inj (Option.some.inj hW1)
  subst hm3
  sorry

end rel

end L.Arena
