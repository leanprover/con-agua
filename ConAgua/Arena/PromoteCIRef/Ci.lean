import ConAgua.Arena.PromoteCIRef.Caps
import ConAgua.Arena.PromoteCIRef.PreESizeLe
import ConAgua.Arena.PromoteCIRef.Rules
import ConAgua.Arena.PromoteCIRef.Of

/-!
# Ci

`wr1_call`, `wr2_call`, `wr4_call`, `wr1_rel`, `wr2_rel`, `wr4_rel` and the lemmas only they use.
-/

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem wr1_call {n : Nat} {d a : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr1" [d, a] m = some (r, m')) :
    stP d m [((0 : Word), a)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr1_spec p hp n ⟨m, Locals.init []⟩ d a) hc; exact hW

theorem wr2_call {n : Nat} {d a b : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr2" [d, a, b] m = some (r, m')) :
    stP d m [((0 : Word), a), ((1 : Word), b)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr2_spec p hp n ⟨m, Locals.init []⟩ d a b) hc; exact hW

theorem wr4_call {n : Nat} {d a b c e : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr4" [d, a, b, c, e] m = some (r, m')) :
    stP d m [((0 : Word), a), ((1 : Word), b), ((2 : Word), c), ((3 : Word), e)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr4_spec p hp n ⟨m, Locals.init []⟩ d a b c e) hc; exact hW

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem wr1_rel {n : Nat} {d a : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 1 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr1" [d, a] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 1 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr1_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

theorem wr2_rel {n : Nat} {d a b : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 2 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr2" [d, a, b] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 2 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr2_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

theorem wr4_rel {n : Nat} {d a b c e : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 4 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr4" [d, a, b, c, e] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 4 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some e := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr4_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

end rel

end L.Arena

end

section

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

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The result of a `pci_*` arm** (`α`: what the twin returns besides the memo; `P` its run;
`Q` the decoding of the new record at `d`): a fresh record `d` of `K` words at or above the old
top, whose kind word is `kw`. -/
def ArmOk {α : Type} (m : Mem) (a : AState) (r : List Word) (m' : Mem) (K : Nat) (kw : Word)
    (P : α → AState → PMemo → Prop) (Q : α → Mem → Nat → Prop) : Prop :=
  ∃ (a' : AState) (pm' : PMemo) (x : α), P x a' pm' ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧
    cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
    erecTop m' ≤ (m'.arr64 EREC).size ∧
    ∃ d : Nat, (r.headD 0).toNat = d ∧ erecTop m ≤ d ∧ d + K ≤ erecTop m' ∧
      (m'.arr64 EREC)[d]? = some kw ∧ Q x m' d

theorem arenaD_erec129 {m m' : Mem} {a : AState} {pm : PMemo} (hD : ArenaD m a) (hP : PMemoR m pm)
    (hf : MemFrame [EREC] [129] m m') : ArenaD m' a ∧ PMemoR m' pm :=
  ⟨⟨ArenaR.frame_ext _ _ (by simp [EREC]) (by simp) m _ hf a hD.1,
    DerR.frameM _ _ m _ hf (by simp [EREC]) a hD.2⟩,
    hP.frame (by simp [EREC]) (by simp) hf⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- The record's constant value decodes at `d`, and keeps doing so when later writes land in
`[d + 5, hi)`. -/
def CvStable (M : Mem) (d : Nat) (cv : IConstantVal) : Prop :=
  decCV (erecP M) (d + 1) = some cv ∧
    ∀ (M' : Mem) (hi : Nat), SlotGrow M M' (d + 5) hi → erecTop M ≤ (M.arr64 EREC).size →
      erecTop M' ≤ (M'.arr64 EREC).size → decCV (erecP M') (d + 1) = some cv

/-- **The constant value, then `pci_mk`**: the words of the promoted value land in the new
record, which then decodes. -/
theorem mk_decode {n : Nat} {M0 M1 M2 : Mem} {c r : List Word} {q k kw : Word}
    {cv' : IConstantVal} (hCV : CVWords M0 c cv') (hext : ArrExt (erecP M0) (erecP M1))
    (hT01 : erecTop M0 ≤ erecTop M1)
    (_hts1 : erecTop M1 ≤ (M1.arr64 EREC).size) (hsz : (M1.arr64 EREC).size < 2 ^ 64)
    (hkw : (M1.arr64 EREC)[q.toNat]? = some kw) (hk5 : 5 ≤ k.toNat)
    (hmk : callW p (n + 1) "pci_mk" [q, k, g0 c, g1 c, g2 c, g3 c] M1 = some (r, M2)) :
    (r.headD 0).toNat = erecTop M1 ∧ erecTop M2 = erecTop M1 + k.toNat ∧ ErecGrow M1 M2 ∧
    MemFrame [EREC] [129] M1 M2 ∧ erecTop M2 ≤ (M2.arr64 EREC).size ∧
    (M2.arr64 EREC)[erecTop M1]? = some kw ∧ CvStable M2 (erecTop M1) cv' := by
  obtain ⟨hr, hT, hg, hfr, hroom, w0, w1, w2, w3, w4⟩ := pciMk_rel p hp hsz hkw hk5 hmk
  obtain ⟨-, hpw0, hn0, hsl, hpw3, ht3⟩ := hCV
  have hts2 : erecTop M2 ≤ (M2.arr64 EREC).size := by rw [hT]; exact hroom
  have P : ∀ {i : Nat} {w : Word}, i < erecTop M2 → (M2.arr64 EREC)[i]? = some w →
      (erecP M2)[i]? = some w := fun hi h => preE_of_get hi h
  have hs' : hslice? (erecP M2) (c.tail.headD 0).toNat (c.tail.tail.headD 0).toNat =
      some cv'.levelParams := hg.ext.hslice? (hext.hslice? hsl)
  have hbd : (c.tail.tail.headD 0).toNat = 0 ∨
      (c.tail.headD 0).toNat + (c.tail.tail.headD 0).toNat ≤ erecTop M1 := by
    rcases hslice?_bound hsl with h0 | h0
    · exact .inl h0
    · right; have := erecP_size_le M0; omega
  have hn0' : decI (g0 c) = cv'.name := hn0
  have ht3' : decI (g3 c) = cv'.type := ht3
  have hdcv := decCV_mk (A := erecP M2) (d := erecTop M1) (nm := g0 c) (qq := g1 c) (l := g2 c)
    (t := g3 c) (P (by omega) w1) (P (by omega) w2) (P (by omega) w3) (P (by omega) w4) hpw0.1
    hpw3.1 hs'
  have hdec : decCV (erecP M2) (erecTop M1 + 1) = some cv' := by
    rw [hdcv, hn0', ht3']
  refine ⟨hr, hT, hg, hfr, hts2, w0, hdec, ?_⟩
  intro M' hi hgs hts hts'
  have Q : ∀ (i : Nat) {w : Word}, erecTop M1 ≤ i → i < erecTop M1 + 5 →
      (M2.arr64 EREC)[i]? = some w → (erecP M')[i]? = some w := fun i w hi1 hi2 h => by
    have : (M'.arr64 EREC)[i]? = (M2.arr64 EREC)[i]? := hgs.2.1 i (by omega) (by omega)
    exact preE_of_get (by have := hgs.1; omega) (by rw [this]; exact h)
  have hs'' := hgs.hslice? hts hts' hs' (by omega)
  have h2 := decCV_mk (A := erecP M') (d := erecTop M1) (nm := g0 c) (qq := g1 c) (l := g2 c)
    (t := g3 c) (Q _ (by omega) (by omega) w1) (Q _ (by omega) (by omega) w2)
    (Q _ (by omega) (by omega) w3) (Q _ (by omega) (by omega) w4) hpw0.1 hpw3.1 hs''
  rw [hn0', ht3'] at h2
  exact h2

theorem plain_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (cv : IConstantVal) (kw : Word) (r : List Word) (m' : Mem) (hD : ArenaD m a)
    (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (hqD : q.toNat + 5 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_plain" [f, q] m = some (r, m')) :
    ArmOk m a r m' 5 kw
      (fun (cv' : IConstantVal) a' pm' => (promoteCV pm f.toNat cv).run a = .ok ((pm', cv'), a'))
      (fun cv' M d => CvStable M d cv') := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciPlain_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [plainW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  cases hmk : callW p (n + 1) "pci_mk" [q, 5, g0 c, g1 c, g2 c, g3 c] m₁ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₂⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨hr, hm2⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm2
  have hkw1 : (m₁.arr64 EREC)[q.toNat]? = some kw := by
    rw [hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (ArrExt.refl _) (Nat.le_refl _) hts1 hsz1 hkw1
    (by simp only [show ((5 : Word)).toNat = 5 from rfl]; omega) hmk
  simp only [show ((5 : Word)).toNat = 5 from rfl] at b2
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD1 hP1 b4
  refine ⟨a1, pm1, cv', hrun1, hDf, hPf, hcp1, ?_, htk1.trans (TierKeep.of_frame b4 (by simp)), hg1.trans b3, b5, erecTop m₁, ?_, hg1.1, ?_, b6,
    b7⟩
  · exact (hfr1.trans (b4.mono (by simp) (by simp)))
  · rw [← hr]; exact b1
  · rw [b2]; omega

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem toNat_add5 (x : Word) (h : x.toNat + 5 < 2 ^ 64) : (x + 5).toNat = x.toNat + 5 := by
  rw [UInt64.toNat_add, show (5 : Word).toNat = 5 from rfl]; exact Nat.mod_eq_of_lt h

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem ctor_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (cv : IConstantVal) (kw w5 w6 : Word) (r : List Word) (m' : Mem) (hD : ArenaD m a)
    (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (h5 : (m.arr64 EREC)[q.toNat + 5]? = some w5) (h6 : (m.arr64 EREC)[q.toNat + 6]? = some w6)
    (hqD : q.toNat + 7 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_ctor" [f, q] m = some (r, m')) :
    ArmOk m a r m' 7 kw
      (fun (cv' : IConstantVal) a' pm' => (promoteCV pm f.toNat cv).run a = .ok ((pm', cv'), a'))
      (fun cv' M d => decCV (erecP M) (d + 1) = some cv' ∧ (erecP M)[d + 5]? = some w5 ∧
        (erecP M)[d + 6]? = some w6) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciCtor_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ctorW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  have e5 : (q + 5).toNat = q.toNat + 5 := toNat_add5 _ (by omega)
  obtain ⟨⟨ra, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm0, hr0, -⟩ := rd2_call p hp hrd
  obtain rfl := hm0.symm
  rw [rd2W_of hsz (by rw [e5]; simpa using h5) (by rw [e5]; simpa using h6)] at hr0
  subst hr0
  simp only [g0, g1, List.headD_cons, List.tail_cons] at hW
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  cases hmk : callW p (n + 1) "pci_mk" [q, 7, g0 c, g1 c, g2 c, g3 c] m₁ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₂⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  have hkw1 : (m₁.arr64 EREC)[q.toNat]? = some kw := by
    rw [hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (ArrExt.refl _) (Nat.le_refl _)
    hts1 hsz1 hkw1 (by simp only [show ((7 : Word)).toNat = 7 from rfl]; omega) hmk
  simp only [show ((7 : Word)).toNat = 7 from rfl] at b2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [b3.2.2]; exact hsz1
  have e5d : (dl.headD 0 + 5).toNat = erecTop m₁ + 5 := by
    rw [toNat_add5 _ (by omega)]; omega
  obtain ⟨⟨z, m₃⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨t1, t2, t3, t4, t5⟩ := wr2_rel p hp (d := dl.headD 0 + 5)
    (by rw [e5d]; omega) hsz2 hwr
  rw [e5d] at t3 t4 t5
  obtain ⟨hr, hm3⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm3
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD1 hP1 b4
  obtain ⟨hDg, hPg⟩ := arenaD_erecFrame hDf hPf t2
  have hT3 : erecTop m₃ = erecTop m₂ := by simp only [erecTop]; rw [t2.2.1 129 (by simp)]
  have hsz3 : (m₃.arr64 EREC).size = (m₂.arr64 EREC).size := t1
  have hgs : SlotGrow m₂ m₃ (erecTop m₁ + 5) (erecTop m₁ + 7) :=
    ⟨by rw [hT3]; exact Nat.le_refl _, fun i hi hout => t3 i (by omega), hsz3⟩
  have hts3 : erecTop m₃ ≤ (m₃.arr64 EREC).size := by rw [hT3, hsz3]; exact b5
  have hg23 : ErecGrow m₁ m₃ :=
    ((SlotGrow.of_grow b3 (erecTop m₁ + 5) (erecTop m₁ + 7)).trans hgs (Nat.le_refl _)
      (Nat.le_refl _)).toGrow (by omega)
  refine ⟨a1, pm1, cv', hrun1, hDg, hPg, hcp1, ?_,
    htk1.trans ((TierKeep.of_frame b4 (by simp)).trans (TierKeep.of_frame t2 (by simp))), hg1.trans hg23, hts3, erecTop m₁, ?_, hg1.1, ?_, ?_, ?_⟩
  · exact (hfr1.trans (b4.mono (by simp) (by simp))).trans (t2.mono (by simp) (by simp))
  · rw [← hr]; exact b1
  · rw [hT3, b2]; omega
  · rw [t3 _ (Or.inl (by omega))]; exact b6
  · refine ⟨b7.2 m₃ (erecTop m₁ + 7) hgs b5 hts3, ?_, ?_⟩
    · exact preE_of_get (m := m₃) (T := erecTop m₃) (by rw [hT3, b2]; omega) (by simpa using t4)
    · exact preE_of_get (m := m₃) (T := erecTop m₃) (by rw [hT3, b2]; omega) (by simpa using t5)

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem rd3W_ne {m : Mem} {s : Word} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hne : rd3W m s ≠ []) :
    ∃ a b c : Word, rd3W m s = [a, b, c] ∧ (m.arr64 EREC)[s.toNat]? = some a ∧
      (m.arr64 EREC)[s.toNat + 1]? = some b ∧ (m.arr64 EREC)[s.toNat + 2]? = some c := by
  unfold rd3W at hne ⊢
  by_cases hc : (m.arr64 EREC).size ≤ s.toNat ∨ (m.arr64 EREC).size ≤ (s + 1).toNat ∨
      (m.arr64 EREC).size ≤ (s + 2).toNat
  · rw [ite_eq_left hc] at hne; exact absurd rfl hne
  rw [ite_eq_right hc]
  simp only [not_or, Nat.not_le] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  have e1 : (s + 1).toNat = s.toNat + 1 := toNat_add1 _ (by omega)
  have e2 : (s + 2).toNat = s.toNat + 2 := by
    rw [UInt64.toNat_add, show (2 : Word).toNat = 2 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e1] at h1; rw [e2] at h2
  refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩
  · simp [rdW, Array.getElem?_eq_getElem h0]
  · rw [rdW, e1]; simp [Array.getElem?_eq_getElem h1]
  · rw [rdW, e2]; simp [Array.getElem?_eq_getElem h2]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem defn_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (cv : IConstantVal) (kw wv : Word) (r : List Word) (m' : Mem) (hD : ArenaD m a)
    (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (h5 : (m.arr64 EREC)[q.toNat + 5]? = some wv) (hwv : wv.toNat < 2 ^ 32)
    (hqD : q.toNat + 7 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_defn" [f, q] m = some (r, m')) :
    ArmOk m a r m' 8 kw
      (fun (x : IConstantVal × EIdx) a' pm' => ∃ (a1 : AState) (pm1 : PMemo),
        (promoteCV pm f.toNat cv).run a = .ok ((pm1, x.1), a1) ∧
        (promoteE pm1 f.toNat (decE wv)).run a1 = .ok ((pm', x.2), a'))
      (fun x M d => decCV (erecP M) (d + 1) = some x.1 ∧
        (hd? (erecP M) (d + 5) : Option EIdx) = some x.2 ∧ ∃ w6 w7 : Word,
          (erecP M)[d + 6]? = some w6 ∧ (erecP M)[d + 7]? = some w7 ∧
          (m.arr64 EREC)[q.toNat + 6]? = some w6 ∧ (m.arr64 EREC)[q.toNat + 7]? = some w7) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciDefn_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [defnW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  have e5 : (q + 5).toNat = q.toNat + 5 := toNat_add5 _ (by omega)
  obtain ⟨⟨ra, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm0, hr0, hne⟩ := rd3_call p hp hrd
  obtain rfl := hm0.symm
  rw [hr0] at hne
  obtain ⟨wa, w6, w7, hr3, hwa, hw6, hw7⟩ := rd3W_ne hsz hne
  rw [e5] at hwa hw6 hw7
  have hwav : wv = wa := (Option.some.inj (hwa.symm.trans (by simpa using h5))).symm
  subst hwav
  rw [hr3] at hr0
  subst hr0
  simp only [g0, g1, g2, List.headD_cons, List.tail_cons] at hW
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  obtain ⟨⟨rx, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a2, pm2, hrun2, hD2, hP2, hpw2, hcp2, hfr2, htk2⟩ :=
    (pe_rel p hp (n + 1)).1 m₁ a1 pm1 f wv rx m₂ hD1 hP1 hwv hcb
  obtain ⟨hE2, hT2⟩ := eFrame_erec hfr2
  have hg12 : ErecGrow m₁ m₂ := ErecGrow.of_eq hE2 hT2
  have hP2e : erecP m₂ = erecP m₁ := by
    rw [erecP_eq_preE, erecP_eq_preE, hT2]; exact preE_congr hE2 _
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [hE2]; exact hsz1
  have hts2 : erecTop m₂ ≤ (m₂.arr64 EREC).size := by rw [hE2, hT2]; exact hts1
  cases hmk : callW p (n + 1) "pci_mk" [q, 8, g0 c, g1 c, g2 c, g3 c] m₂ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₃⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  have hkw2 : (m₂.arr64 EREC)[q.toNat]? = some kw := by
    rw [hE2, hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (by rw [hP2e]; exact ArrExt.refl _)
    (by rw [hT2]; exact Nat.le_refl _) hts2 hsz2 hkw2 (by simp only [show ((8 : Word)).toNat = 8 from rfl]; omega) hmk
  simp only [show ((8 : Word)).toNat = 8 from rfl] at b2
  have hsz3 : (m₃.arr64 EREC).size < 2 ^ 64 := by rw [b3.2.2]; exact hsz2
  have e5d : (dl.headD 0 + 5).toNat = erecTop m₂ + 5 := by
    rw [toNat_add5 _ (by omega)]; omega
  obtain ⟨⟨z, m₄⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := wr3_rel p hp (d := dl.headD 0 + 5)
    (by rw [e5d]; omega) hsz3 hwr
  rw [e5d] at t3 t4 t5 t6
  obtain ⟨hr, hm4⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm4
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD2 hP2 b4
  obtain ⟨hDg, hPg⟩ := arenaD_erecFrame hDf hPf t2
  have hT4 : erecTop m₄ = erecTop m₃ := by simp only [erecTop]; rw [t2.2.1 129 (by simp)]
  have hsz4 : (m₄.arr64 EREC).size = (m₃.arr64 EREC).size := t1
  have hgs : SlotGrow m₃ m₄ (erecTop m₂ + 5) (erecTop m₂ + 8) :=
    ⟨by rw [hT4]; exact Nat.le_refl _, fun i hi hout => t3 i (by omega), hsz4⟩
  have hts4 : erecTop m₄ ≤ (m₄.arr64 EREC).size := by rw [hT4, hsz4]; exact b5
  have hg34 : ErecGrow m₂ m₄ :=
    ((SlotGrow.of_grow b3 (erecTop m₂ + 5) (erecTop m₂ + 8)).trans hgs (Nat.le_refl _)
      (Nat.le_refl _)).toGrow (by omega)
  refine ⟨a2, pm2, (cv', decE (rx.headD 0)), ⟨a1, pm1, hrun1, hrun2⟩, hDg, hPg,
    hcp2.trans hcp1, ?_,
    htk1.trans (htk2.trans ((TierKeep.of_frame b4 (by simp)).trans (TierKeep.of_frame t2 (by simp)))),
    hg1.trans (hg12.trans hg34), hts4, erecTop m₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hfr1.trans (eFrame_cons hfr2)).trans (b4.mono (by simp) (by simp))).trans
      (t2.mono (by simp) (by simp))
  · rw [← hr]; exact b1
  · rw [hT2]; exact hg1.1
  · rw [hT4, b2]; omega
  · rw [t3 _ (Or.inl (by omega))]; exact b6
  · refine ⟨b7.2 m₄ (erecTop m₂ + 8) hgs b5 hts4, ?_, w6, w7, ?_, ?_, hw6, hw7⟩
    · exact hd?_of_pre (m := m₄) (T := erecTop m₄) (by rw [hT4, b2]; omega) (by simpa using t4) hpw2.1
    · exact preE_of_get (m := m₄) (T := erecTop m₄) (by rw [hT4, b2]; omega) (by simpa using t5)
    · exact preE_of_get (m := m₄) (T := erecTop m₄) (by rw [hT4, b2]; omega) (by simpa using t6)

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem decRules_bound : ∀ (c : Nat) (a : Array Word) (off : Nat) (rls : List IRecRule),
    decRules a off c = some rls → c = 0 ∨ off + 11 * c ≤ a.size := by
  intro c
  induction c with
  | zero => intro a off rls _; exact .inl rfl
  | succ c ih =>
    intro a off rls h
    right
    rw [decRules_succ] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨r0, hr0, rs, hrs, -⟩ := h
    obtain ⟨w0, w1, w2, w8, w9, w10, -, -, -, -, -, -, -, -, -, -, -, -, e10, -⟩ := pmDecRule_words hr0
    have := (Array.getElem?_eq_some_iff.mp e10).1
    rcases ih a (off + 11) rs hrs with h0 | h0
    · subst h0; omega
    · omega

theorem toNat_mul11 (l : Word) (h : l.toNat < 2 ^ 60) : (11 * l).toNat = 11 * l.toNat := by
  rw [UInt64.toNat_mul, show (11 : Word).toNat = 11 from rfl]
  exact Nat.mod_eq_of_lt (by omega)

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem ind_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (dn : NIdx → Option ConLeche.Name) (cv : IConstantVal) (caps : IIndCaps) (kw : Word)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv)
    (hcaps : decCaps (preE m D) dn (q.toNat + 5) = some caps)
    (hkw : (m.arr64 EREC)[q.toNat]? = some kw) (hqD : q.toNat + 20 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_ind" [f, q] m = some (r, m')) :
    ArmOk m a r m' 20 kw
      (fun (x : IConstantVal × IIndCaps) a' pm' => ∃ (a1 : AState) (pm1 : PMemo),
        (promoteCV pm f.toNat cv).run a = .ok ((pm1, x.1), a1) ∧
        (promoteCaps pm1 f.toNat caps).run a1 = .ok ((pm', x.2), a'))
      (fun x M d => decCV (erecP M) (d + 1) = some x.1 ∧ decCaps (erecP M) dn (d + 5) = some x.2) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciInd_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [indW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  have e5 : (q + 5).toNat = q.toNat + 5 := toNat_add5 _ (by omega)
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  cases hmk : callW p (n + 1) "pci_mk" [q, 20, g0 c, g1 c, g2 c, g3 c] m₁ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₂⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  have hkw1 : (m₁.arr64 EREC)[q.toNat]? = some kw := by
    rw [hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (ArrExt.refl _) (Nat.le_refl _)
    hts1 hsz1 hkw1 (by simp only [show ((20 : Word)).toNat = 20 from rfl]; omega) hmk
  simp only [show ((20 : Word)).toNat = 20 from rfl] at b2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [b3.2.2]; exact hsz1
  have e5d : (dl.headD 0 + 5).toNat = erecTop m₁ + 5 := by
    rw [toNat_add5 _ (by omega)]; omega
  obtain ⟨⟨z, m₃⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD1 hP1 b4
  have hg02 : ErecGrow m m₂ := hg1.trans b3
  have hlow : ArrExt (preE m D) (preE m₂ D) := preE_ext (fun i hi => hg02.2.1 i (by omega))
  obtain ⟨a3, pm3, caps', hrun3, hD3, hP3, hcp3, hfr3, htk3, hgs, hts3, hdc⟩ :=
    caps_rel p hp (n + 1) m₂ a1 pm1 f (q + 5) (dl.headD 0 + 5) D dn caps z m₃ hDf hPf hsz2 b5
      (by rw [e5]; exact hlow.decCaps hcaps) (by rw [e5]; omega) (by have := hg02.1; omega)
      (by rw [e5d]; have := hg1.1; omega) (by rw [e5d, b2]; omega) hcc
  rw [e5d] at hgs hdc
  obtain ⟨hr, hm3⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm3
  have hg3 : ErecGrow m₁ m₃ :=
    ((SlotGrow.of_grow b3 (erecTop m₁ + 5) (erecTop m₁ + 5 + 15)).trans hgs (Nat.le_refl _)
      (Nat.le_refl _)).toGrow (by omega)
  refine ⟨a3, pm3, (cv', caps'), ⟨a1, pm1, hrun1, hrun3⟩, hD3, hP3, hcp3.trans hcp1, ?_,
    htk1.trans ((TierKeep.of_frame b4 (by simp)).trans htk3), hg1.trans hg3, hts3, erecTop m₁, ?_, hg1.1, ?_, ?_, ?_⟩
  · exact (hfr1.trans (b4.mono (by simp) (by simp))).trans hfr3
  · rw [← hr]; exact b1
  · have := hgs.1; omega
  · have h1 : (m₃.arr64 EREC)[erecTop m₁]? = (m₂.arr64 EREC)[erecTop m₁]? := hgs.2.1 _ (by omega) (Or.inl (by omega))
    rw [h1]; exact b6
  · exact ⟨b7.2 m₃ _ hgs b5 hts3, hdc⟩

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem SlotGrow.widen {m m' : Mem} {lo hi lo' hi' : Nat} (h : SlotGrow m m' lo hi)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : SlotGrow m m' lo' hi' :=
  ⟨h.1, fun i hi1 hout => h.2.1 i hi1 (by omega), h.2.2⟩

theorem rules_zero_gen {n : Nat} {f s l d : Word} {m m' : Mem} {r : List Word} (p : Prog)
    (hp : PromoteProg p) (hl : l = 0)
    (hc : callW p n "promote_rules" [f, s, l, d] m = some (r, m')) : m' = m := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteRules_spec p hp n ⟨m, Locals.init []⟩ f s l d) hc
  simp only at hW
  rw [hs'] at hW
  simp only [rulesW, hl, ↓reduceIte, Option.some.injEq] at hW
  exact hW.symm

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

/-- **`rec_block`**: a fresh block of `11 l` words, the four record words written at `d5`. -/
theorem recBlock_rel {n : Nat} {d5 w5 w6 l : Word} {m m' : Mem} {r : List Word}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hbd : d5.toNat + 4 ≤ erecTop m)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hc : callW p n "rec_block" [d5, w5, w6, l] m = some (r, m')) :
    l.toNat < 1152921504606846976 ∧ (r.headD 0).toNat = erecTop m ∧
    erecTop m' = erecTop m + 11 * l.toNat ∧ SlotGrow m m' d5.toNat (d5.toNat + 4) ∧
    MemFrame [EREC] [129] m m' ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
    (m'.arr64 EREC)[d5.toNat]? = some w5 ∧ (m'.arr64 EREC)[d5.toNat + 1]? = some w6 ∧
    (m'.arr64 EREC)[d5.toNat + 2]? = some (r.headD 0) ∧ (m'.arr64 EREC)[d5.toNat + 3]? = some l := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (recBlock_spec p hp n ⟨m, Locals.init []⟩ d5 w5 w6 l) hc
  simp only at hW
  rw [hs'] at hW
  simp only [recBlockW] at hW
  cases n with
  | zero => simp only [callW_zero'] at hW; split at hW <;> simp at hW
  | succ n =>
  by_cases hbig : 1152921504606846976 ≤ l
  · rw [ite_eq_left hbig] at hW; cases hW
  rw [ite_eq_right hbig] at hW
  have h60 : l.toNat < 1152921504606846976 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hbig)
    simpa using this
  have h11 : (11 * l).toNat = 11 * l.toNat := toNat_mul11 l (by omega)
  obtain ⟨⟨r5, ma⟩, hal, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hd5, hTa, hroom, hfa, hEa⟩ := alloc_rel p hp hal
  rw [h11] at hTa hroom
  obtain ⟨⟨z, mb⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := wr4_rel p hp (d := d5) (by rw [hEa]; omega)
    (by rw [hEa]; exact hsz) hwr
  have hT : erecTop mb = erecTop m + 11 * l.toNat := by
    simp only [erecTop]; rw [t2.2.1 129 (by simp)]; exact hTa
  have hsz' : (mb.arr64 EREC).size = (m.arr64 EREC).size := by rw [t1, hEa]
  refine ⟨h60, by rw [← hr]; exact hd5, hT, ⟨by omega, fun i hi hout => ?_, hsz'⟩,
    (hfa.mono (by simp) (by simp)).trans (t2.mono (by simp) (by simp)), by rw [hT, hsz']; omega,
    by simpa using t4, by simpa using t5, by rw [← hr]; simpa using t6, by simpa using t7⟩
  · rw [t3 i (by omega), hEa]

theorem rec_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (cv : IConstantVal) (rls : List IRecRule) (kw w5 w6 w7 w8 : Word) (r : List Word) (m' : Mem)
    (hD : ArenaD m a) (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (h5 : (m.arr64 EREC)[q.toNat + 5]? = some w5) (h6 : (m.arr64 EREC)[q.toNat + 6]? = some w6)
    (h7 : (m.arr64 EREC)[q.toNat + 7]? = some w7) (h8 : (m.arr64 EREC)[q.toNat + 8]? = some w8)
    (hrls : decRules (preE m D) w7.toNat w8.toNat = some rls)
    (hqD : q.toNat + 9 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_rec" [f, q] m = some (r, m')) :
    ArmOk m a r m' 9 kw
      (fun (x : IConstantVal × List IRecRule) a' pm' => ∃ (a1 : AState) (pm1 : PMemo),
        (promoteCV pm f.toNat cv).run a = .ok ((pm1, x.1), a1) ∧
        (promoteRules pm1 f.toNat rls).run a1 = .ok ((pm', x.2), a'))
      (fun x M d => decCV (erecP M) (d + 1) = some x.1 ∧ nat? (erecP M) (d + 5) = some w5.toNat ∧
        nat? (erecP M) (d + 6) = some w6.toNat ∧ nat? (erecP M) (d + 8) = some w8.toNat ∧
        ∃ pw : Nat, nat? (erecP M) (d + 7) = some pw ∧ decRules (erecP M) pw w8.toNat = some x.2) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (pciRec_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [recW, pciMkC] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  have e1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 _ (by omega)
  have e5 : (q + 5).toNat = q.toNat + 5 := toNat_add5 _ (by omega)
  obtain ⟨⟨ra, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm0, hr0, -⟩ := rd4_call p hp hrd
  obtain rfl := hm0.symm
  rw [rd4W_of hsz (by rw [e5]; simpa using h5) (by rw [e5]; simpa using h6)
    (by rw [e5]; simpa using h7) (by rw [e5]; simpa using h8)] at hr0
  subst hr0
  simp only [g0, g1, g2, g3, List.headD_cons, List.tail_cons] at hW
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1, htk1⟩ :=
    cv_rel p hp (n + 1) m a pm f (q + 1) cv c m₁ hD hP
      (by rw [e1]; exact (preE_mono m hDt).decCV hcv) hsz hca
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hg1.2.2]; exact hsz
  cases hmk : callW p (n + 1) "pci_mk" [q, 9, g0 c, g1 c, g2 c, g3 c] m₁ with
  | none => rw [hmk] at hW; cases hW
  | some x =>
  obtain ⟨dl, m₂⟩ := x
  rw [hmk] at hW
  simp only [Option.bind_some] at hW
  have hkw1 : (m₁.arr64 EREC)[q.toNat]? = some kw := by
    rw [hg1.2.1 _ (by omega)]; exact hkw
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (ArrExt.refl _) (Nat.le_refl _)
    hts1 hsz1 hkw1 (by simp only [show ((9 : Word)).toNat = 9 from rfl]; omega) hmk
  simp only [show ((9 : Word)).toNat = 9 from rfl] at b2
  have hsz2 : (m₂.arr64 EREC).size < 2 ^ 64 := by rw [b3.2.2]; exact hsz1
  have e5d : (dl.headD 0 + 5).toNat = erecTop m₁ + 5 := by
    rw [toNat_add5 _ (by omega)]; omega
  obtain ⟨⟨bl, m₃⟩, hbl, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨c60, u1, u2, u3, u4, u5, u6, u7, u8, u9⟩ := recBlock_rel p hp (d5 := dl.headD 0 + 5)
    hsz2 (by rw [e5d, b2]; omega) b5 hbl
  rw [e5d] at u3 u6 u7 u8 u9
  have hsz3 : (m₃.arr64 EREC).size < 2 ^ 64 := by rw [u3.2.2]; exact hsz2
  obtain ⟨⟨z, m₄⟩, hpr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, hm4⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hm4
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD1 hP1 b4
  obtain ⟨hDg, hPg⟩ := arenaD_erec129 hDf hPf u4
  have hg02 : ErecGrow m m₂ := hg1.trans b3
  have h01 : erecTop m ≤ erecTop m₁ := hg1.1
  have hlow : ArrExt (preE m D) (preE m₃ D) := preE_ext (fun i hi => by
    rw [u3.2.1 i (by omega) (by omega)]; exact hg02.2.1 i (by omega))
  have hgb : SlotGrow m₂ m₃ (erecTop m₁ + 5) (erecTop m₁ + 5 + 4) := u3
  by_cases hl0 : w8 = 0
  · have hm : m₃ = m₄ := (rules_zero_gen p hp hl0 hpr).symm
    subst hm
    have hl0' : w8.toNat = 0 := by rw [hl0]; rfl
    rw [hl0'] at hrls
    simp only [decRules, List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at hrls
    subst hrls
    have hg3 : ErecGrow m₁ m₃ :=
      ((SlotGrow.of_grow b3 (erecTop m₁ + 5) (erecTop m₁ + 5 + 4)).trans hgb (Nat.le_refl _)
        (Nat.le_refl _)).toGrow (by omega)
    refine ⟨a1, pm1, (cv', []), ⟨a1, pm1, hrun1, ?_⟩, hDg, hPg, hcp1, ?_,
      htk1.trans ((TierKeep.of_frame b4 (by simp)).trans (TierKeep.of_frame u4 (by simp))), hg1.trans hg3, u5,
      erecTop m₁, ?_, hg1.1, ?_, ?_, ?_⟩
    · rw [promoteRules_nil]; rfl
    · exact (hfr1.trans (b4.mono (by simp) (by simp))).trans (u4.mono (by simp) (by simp))
    · rw [← hr]; exact b1
    · rw [u2, b2]; omega
    · have h1 : (m₃.arr64 EREC)[erecTop m₁]? = (m₂.arr64 EREC)[erecTop m₁]? :=
        hgb.2.1 _ (by omega) (Or.inl (by omega))
      rw [h1]; exact b6
    · have hts3 : erecTop m₃ ≤ (m₃.arr64 EREC).size := u5
      have N : ∀ {i : Nat} {w : Word}, i < erecTop m₃ → (m₃.arr64 EREC)[i]? = some w →
          nat? (erecP m₃) i = some w.toNat := fun hi h => nat?_of_pre hi h
      refine ⟨b7.2 m₃ _ hgb b5 hts3, N (by omega) (by simpa using u6), N (by omega) (by simpa using u7),
        N (by omega) (by simpa using u9), (bl.headD 0).toNat, N (by omega) (by simpa using u8), ?_⟩
      rw [hl0']; simp [decRules]
  · have hbnd := decRules_bound _ _ _ _ hrls
    have hsD : w7.toNat + 11 * w8.toNat ≤ D := by
      rcases hbnd with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl0
      · have := preE_size_le m D; omega
    obtain ⟨a3, pm3, rls', hrun3, hD3, hP3, hcp3, hfr3, htk3, hgs3, hts3, hdr3⟩ :=
      rules_rel p hp (n + 1) m₃ a1 pm1 f w7 w8 (bl.headD 0) D rls z m₄ hDg hPg hsz3 u5
        (hlow.decRules hrls) hsD (by omega) (by omega) (by omega) hpr
    have hjoin : SlotGrow m₂ m₄ (erecTop m₁ + 5) ((bl.headD 0).toNat + 11 * w8.toNat) :=
      (hgb.widen (Nat.le_refl _) (show erecTop m₁ + 5 + 4 ≤ (bl.headD 0).toNat by omega)).join hgs3
        (by omega) (by omega)
    have hg4 : ErecGrow m m₄ :=
      ((SlotGrow.of_grow hg02 (erecTop m₁ + 5) ((bl.headD 0).toNat + 11 * w8.toNat)).trans hjoin
        (Nat.le_refl _) (Nat.le_refl _)).toGrow (by omega)
    have hts2' : erecTop m₂ ≤ (m₂.arr64 EREC).size := b5
    have N : ∀ {i : Nat} {w : Word}, i < erecTop m₄ → (m₄.arr64 EREC)[i]? = some w →
        nat? (erecP m₄) i = some w.toNat := fun hi h => nat?_of_pre hi h
    have key : ∀ j, j < 4 → (m₄.arr64 EREC)[erecTop m₁ + 5 + j]? = (m₃.arr64 EREC)[erecTop m₁ + 5 + j]? :=
      fun j hj => hgs3.2.1 _ (by omega) (Or.inl (by omega))
    have hT3 : erecTop m₃ = erecTop m₂ + 11 * w8.toNat := by rw [u2]
    refine ⟨a3, pm3, (cv', rls'), ⟨a1, pm1, hrun1, hrun3⟩, hD3, hP3, hcp3.trans hcp1, ?_,
      htk1.trans ((TierKeep.of_frame b4 (by simp)).trans ((TierKeep.of_frame u4 (by simp)).trans htk3)), hg4, hts3,
      erecTop m₁, ?_, hg1.1, ?_, ?_, ?_⟩
    · exact ((hfr1.trans (b4.mono (by simp) (by simp))).trans (u4.mono (by simp) (by simp))).trans hfr3
    · rw [← hr]; exact b1
    · have := hgs3.1; omega
    · rw [hjoin.2.1 _ (by omega) (Or.inl (by omega))]; exact b6
    · refine ⟨b7.2 m₄ _ hjoin b5 hts3, N (by have := hgs3.1; omega) ?_, N (by have := hgs3.1; omega) ?_,
        N (by have := hgs3.1; omega) ?_, (bl.headD 0).toNat, N (by have := hgs3.1; omega) ?_, ?_⟩
      · have := key 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; simpa using u6
      · have := key 1 (by omega); rw [show erecTop m₁ + 5 + 1 = erecTop m₁ + 6 from rfl] at this
        rw [show erecTop m₁ + 6 = erecTop m₁ + 5 + 1 from rfl, this]; simpa using u7
      · have := key 3 (by omega); rw [show erecTop m₁ + 5 + 3 = erecTop m₁ + 8 from rfl] at this
        rw [this]; simpa using u9
      · have := key 2 (by omega); rw [show erecTop m₁ + 5 + 2 = erecTop m₁ + 7 from rfl] at this
        rw [this]; simpa using u8
      · exact hdr3

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section mk
variable {A : Array Word} {dn : NIdx → Option ConLeche.Name} {d : Nat} {cv : IConstantVal}

theorem decCI_ax (hk : nat? A d = some 0) (hcv : decCV A (d + 1) = some cv) :
    decCI A dn d = some (.axiomInfo cv) := by
  unfold decCI; simp [hk, hcv]

theorem decCI_df {e : EIdx} {h : ConLeche.ReducibilityHint} (hk : nat? A d = some 1)
    (hcv : decCV A (d + 1) = some cv) (he : hd? A (d + 5) = some e)
    (hh : decHint A (d + 6) = some h) : decCI A dn d = some (.defnInfo cv e h) := by
  unfold decCI; simp [hk, hcv, he, hh]

theorem decCI_th (hk : nat? A d = some 2) (hcv : decCV A (d + 1) = some cv) :
    decCI A dn d = some (.thmInfo cv) := by
  unfold decCI; simp [hk, hcv]

theorem decCI_in {caps : IIndCaps} (hk : nat? A d = some 3) (hcv : decCV A (d + 1) = some cv)
    (hc : decCaps A dn (d + 5) = some caps) : decCI A dn d = some (.indInfo cv caps) := by
  unfold decCI; simp [hk, hcv, hc]

theorem decCI_ct {np nf : Nat} (hk : nat? A d = some 4) (hcv : decCV A (d + 1) = some cv)
    (h5 : nat? A (d + 5) = some np) (h6 : nat? A (d + 6) = some nf) :
    decCI A dn d = some (.ctorInfo cv np nf) := by
  unfold decCI; simp [hk, hcv, h5, h6]

theorem decCI_rc {mi rp ro rc : Nat} {rls : List IRecRule} (hk : nat? A d = some 5)
    (hcv : decCV A (d + 1) = some cv) (h5 : nat? A (d + 5) = some mi)
    (h6 : nat? A (d + 6) = some rp) (h7 : nat? A (d + 7) = some ro)
    (h8 : nat? A (d + 8) = some rc) (hr : decRules A ro rc = some rls) :
    decCI A dn d = some (.recInfo cv mi rp rls) := by
  unfold decCI; simp [hk, hcv, h5, h6, h7, h8, hr]

end mk

/-- The shapes of a decoded constant record. -/
theorem decCI_cases {A : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {ci : IConstantInfo} (h : decCI A dn q = some ci) :
    (∃ cv, nat? A q = some 0 ∧ decCV A (q + 1) = some cv ∧ ci = .axiomInfo cv) ∨
    (∃ cv e hh, nat? A q = some 1 ∧ decCV A (q + 1) = some cv ∧ hd? A (q + 5) = some e ∧
      decHint A (q + 6) = some hh ∧ ci = .defnInfo cv e hh) ∨
    (∃ cv, nat? A q = some 2 ∧ decCV A (q + 1) = some cv ∧ ci = .thmInfo cv) ∨
    (∃ cv caps, nat? A q = some 3 ∧ decCV A (q + 1) = some cv ∧ decCaps A dn (q + 5) = some caps ∧
      ci = .indInfo cv caps) ∨
    (∃ cv np nf, nat? A q = some 4 ∧ decCV A (q + 1) = some cv ∧ nat? A (q + 5) = some np ∧
      nat? A (q + 6) = some nf ∧ ci = .ctorInfo cv np nf) ∨
    (∃ cv mi rp ro rc rls, nat? A q = some 5 ∧ decCV A (q + 1) = some cv ∧
      nat? A (q + 5) = some mi ∧ nat? A (q + 6) = some rp ∧ nat? A (q + 7) = some ro ∧
      nat? A (q + 8) = some rc ∧ decRules A ro rc = some rls ∧ ci = .recInfo cv mi rp rls) := by
  unfold decCI at h
  cases hk : nat? A q with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.bind_eq_bind, Option.bind_some] at h
    rcases k with _ | _ | _ | _ | _ | _ | k
    · left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, rfl⟩ := h
      exact ⟨cv, rfl, hcv, rfl⟩
    · right; left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, e, he, hh, hhh, rfl⟩ := h
      exact ⟨cv, e, hh, rfl, hcv, he, hhh, rfl⟩
    · right; right; left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, rfl⟩ := h
      exact ⟨cv, rfl, hcv, rfl⟩
    · right; right; right; left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, caps, hc, rfl⟩ := h
      exact ⟨cv, caps, rfl, hcv, hc, rfl⟩
    · right; right; right; right; left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, np, hnp, nf, hnf, rfl⟩ := h
      exact ⟨cv, np, nf, rfl, hcv, hnp, hnf, rfl⟩
    · right; right; right; right; right
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, mi, hmi, rp, hrp, ro, hro, rc, hrc, rls, hr, rfl⟩ := h
      exact ⟨cv, mi, rp, ro, rc, rls, rfl, hcv, hmi, hrp, hro, hrc, hr, rfl⟩
    · simp at h

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem decCV_bound {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    q + 3 < a.size := by
  unfold decCV at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨n, hn, l, hl, t, ht, -⟩ := h
  obtain ⟨w, hw, -⟩ := hd?_some ht
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem decCaps_bound {a : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {caps : IIndCaps} (h : decCaps a dn q = some caps) : q + 14 < a.size := by
  obtain ⟨-, -, hc, -⟩ := decCaps_words h
  obtain ⟨o, c, -, hc1, -⟩ := hlist?_unfold hc
  obtain ⟨w, hw, -⟩ := nat?_get hc1
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem decHint_move' {a b : Array Word} {i j : Nat} {h : ConLeche.ReducibilityHint}
    (hw0 : b[j]? = a[i]?) (hw1 : a[i + 1]? = none ∨ b[j + 1]? = a[i + 1]?)
    (hd : decHint a i = some h) : decHint b j = some h := by
  unfold decHint at hd ⊢
  cases hk : nat? a i with
  | none => simp [hk] at hd
  | some t =>
    have hk' : nat? b j = some t := nat?_move hw0 hk
    simp only [hk, hk', Option.bind_eq_bind, Option.bind_some] at hd ⊢
    rcases t with _ | _ | _ | t
    · exact hd
    · exact hd
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hd ⊢
      obtain ⟨x, hx, rfl⟩ := hd
      rcases hw1 with h1 | h1
      · obtain ⟨w, hw, -⟩ := nat?_get hx; rw [h1] at hw; cases hw
      · exact ⟨x, nat?_move h1 hx, rfl⟩
    · simp at hd

/-- The word of a decoded `nat?`, read in the pool `m` (below `D`). -/
theorem nat_word_pre {m : Mem} {D i k : Nat} (h : nat? (preE m D) i = some k) :
    ∃ w, (m.arr64 EREC)[i]? = some w ∧ w.toNat = k ∧ i < D := by
  obtain ⟨w, hw, hk, hi⟩ := nat?_pre h
  exact ⟨w, hw, hk, hi⟩

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem nat?_erecP {m : Mem} {i : Nat} {w : Word} (h : i < erecTop m)
    (hw : (m.arr64 EREC)[i]? = some w) : nat? (erecP m) i = some w.toNat := nat?_of_pre h hw

theorem decHint_bound {a : Array Word} {q : Nat} {h : ConLeche.ReducibilityHint}
    (hd : decHint a q = some h) : q < a.size := by
  unfold decHint at hd
  cases hk : nat? a q with
  | none => simp [hk] at hd
  | some t =>
    obtain ⟨w, hw, -⟩ := nat?_get hk
    exact (Array.getElem?_eq_some_iff.mp hw).1

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem ci_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (dn : NIdx → Option ConLeche.Name) (ci : IConstantInfo) (r : List Word) (m' : Mem)
    (hD : ArenaD m a) (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hci : decCI (preE m D) dn q.toNat = some ci) (hDt : D ≤ erecTop m)
    (hc : callW p n "promote_ci" [f, q] m = some (r, m')) :
    ∃ a' pm' ci', (promoteCI pm f.toNat ci).run a = .ok ((pm', ci'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧
      ErecGrow m m' ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧ erecTop m ≤ (r.headD 0).toNat ∧
      (r.headD 0).toNat < erecTop m' ∧ decCI (erecP m') dn (r.headD 0).toNat = some ci' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteCI_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ciW] at hW
  have hkk : ∃ k, nat? (preE m D) q.toNat = some k := by
    unfold decCI at hci
    cases hk : nat? (preE m D) q.toNat with
    | none => simp [hk] at hci
    | some k => exact ⟨k, rfl⟩
  obtain ⟨kk, hkk⟩ := hkk
  obtain ⟨kw, hkwm, hkwk, hqD0⟩ := nat_word_pre hkk
  obtain ⟨⟨rr, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm0, hr0, -⟩ := rd1_call p hp hrd
  obtain rfl := hm0.symm
  rw [rd1W_of hsz (by simpa using hkwm)] at hr0
  subst hr0
  simp only [g0, List.headD_cons] at hW
  have hPG : ∀ {i : Nat} {w : Word} {m'' : Mem}, i < erecTop m'' → (m''.arr64 EREC)[i]? = some w →
      nat? (erecP m'') i = some w.toNat := fun hi h => nat?_of_pre hi h
  rcases decCI_cases hci with ⟨cv, hk, hcv, rfl⟩ | ⟨cv, e, hh, hk, hcv, he, hhh, rfl⟩ |
    ⟨cv, hk, hcv, rfl⟩ | ⟨cv, caps, hk, hcv, hcp, rfl⟩ | ⟨cv, np, nf, hk, hcv, hnp, hnf, rfl⟩ |
    ⟨cv, mi, rp, ro, rc, rls, hk, hcv, hmi, hrp, hro, hrc, hrl, rfl⟩
  · -- axiom
    have hK : kk = 0 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 0 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [ show ¬((0:Word) = 1) by decide, show ¬((0:Word) = 3) by decide, show ¬((0:Word) = 4) by decide, show ¬((0:Word) = 5) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    have hb := decCV_bound hcv
    obtain ⟨a', pm1, cv', hrun, hDf, hPf, hcp, hfr, htk, hg, hts', d, hdr, hdlo, hdhi, hkind, hQ⟩ :=
      plain_rel p hp n m a pm f q D cv 0 dl m1 hD hP hsz hts hcv hkwm (by omega) hDt hcl
    refine ⟨a', pm1, .axiomInfo cv', ?_, hDf, hPf, hcp, hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_ax (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hQ.1
  · -- defn
    have hK : kk = 1 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 1 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ¬((1:Word) = 0 ∨ (1:Word) = 2) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some he
    obtain ⟨hlt5, hm5⟩ := preE_get_lt hwv
    have hb6 := decHint_bound hhh
    obtain ⟨a', pm1, x, ⟨aA, pmA, hrun1, hrun2⟩, hDf, hPf, hcp, hfr, htk, hg, hts', d, hdr, hdlo, hdhi,
      hkind, hdcv, hd5, w6, w7, e6, e7, s6, s7⟩ :=
      defn_rel p hp n m a pm f q D cv 1 wv dl m1 hD hP hsz hts hcv hkwm hm5 hwvl (by omega) hDt hcl
    have hrun2' : (promoteE pmA f.toNat (decI wv)).run aA = .ok ((pm1, x.2), a') := hrun2
    have hhint : decHint (erecP m1) (d + 6) = some hh := by
      refine decHint_move' (a := preE m D) (b := erecP m1) (i := q.toNat + 6) (j := d + 6) ?_ ?_ hhh
      · rw [e6, preE_get, ite_eq_left (by omega)]; exact s6.symm
      · by_cases h : q.toNat + 6 + 1 < D
        · right
          have e7' : (erecP m1)[d + 6 + 1]? = some w7 := e7
          rw [e7', preE_get, ite_eq_left h]; exact s7.symm
        · left; rw [preE_get, ite_eq_right h]
    refine ⟨a', pm1, .defnInfo x.1 x.2 hh, ?_, hDf, hPf, hcp, hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun1]; simp only; rw [run_bind_ok hrun2']; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_df (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hdcv hd5 hhint
  · -- thm
    have hK : kk = 2 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 2 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [ show ¬((2:Word) = 1) by decide, show ¬((2:Word) = 3) by decide, show ¬((2:Word) = 4) by decide, show ¬((2:Word) = 5) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    have hb := decCV_bound hcv
    obtain ⟨a', pm1, cv', hrun, hDf, hPf, hcp, hfr, htk, hg, hts', d, hdr, hdlo, hdhi, hkind, hQ⟩ :=
      plain_rel p hp n m a pm f q D cv 2 dl m1 hD hP hsz hts hcv hkwm (by omega) hDt hcl
    refine ⟨a', pm1, .thmInfo cv', ?_, hDf, hPf, hcp, hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_th (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hQ.1
  · -- ind
    have hK : kk = 3 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 3 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ¬((3:Word) = 0 ∨ (3:Word) = 2) by decide, show ¬((3:Word) = 1) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    have hb := decCaps_bound hcp
    obtain ⟨a', pm1, x, ⟨aA, pmA, hrun1, hrun2⟩, hDf, hPf, hcp', hfr, htk, hg, hts', d, hdr, hdlo, hdhi,
      hkind, hdcv, hdcaps⟩ :=
      ind_rel p hp n m a pm f q D dn cv caps 3 dl m1 hD hP hsz hts hcv hcp hkwm (by omega) hDt hcl
    refine ⟨a', pm1, .indInfo x.1 x.2, ?_, hDf, hPf, hcp', hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun1]; simp only; rw [run_bind_ok hrun2]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_in (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hdcv hdcaps
  · -- ctor
    have hK : kk = 4 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 4 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ¬((4:Word) = 0 ∨ (4:Word) = 2) by decide, show ¬((4:Word) = 1) by decide, show ¬((4:Word) = 3) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    obtain ⟨w5, hw5, rfl, hlt5⟩ := nat_word_pre hnp
    obtain ⟨w6, hw6, rfl, hlt6⟩ := nat_word_pre hnf
    obtain ⟨a', pm1, cv', hrun, hDf, hPf, hcp', hfr, htk, hg, hts', d, hdr, hdlo, hdhi,
      hkind, hdcv, hn5, hn6⟩ :=
      ctor_rel p hp n m a pm f q D cv 4 w5 w6 dl m1 hD hP hsz hts hcv hkwm hw5 hw6 (by omega) hDt hcl
    refine ⟨a', pm1, .ctorInfo cv' w5.toNat w6.toNat, ?_, hDf, hPf, hcp', hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_ct (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hdcv (by simp [nat?, hn5]) (by simp [nat?, hn6])
  · -- rec
    have hK : kk = 5 := (Option.some.inj (hkk.symm.trans hk))
    have hkw0 : kw = 5 := UInt64.toNat_inj.mp (by rw [hkwk, hK]; rfl)
    subst hkw0
    simp only [show ¬((5:Word) = 0 ∨ (5:Word) = 2) by decide, show ¬((5:Word) = 1) by decide, show ¬((5:Word) = 3) by decide, show ¬((5:Word) = 4) by decide, ↓reduceIte] at hW
    simp only [promoteArmK] at hW
    obtain ⟨⟨dl, m1⟩, hcl, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hr, hm1⟩ := Prod.mk.inj (Option.some.inj hW)
    subst hm1
    have hr' : dl.headD 0 = r.headD 0 := hr
    have hpre := preE_size_le m D
    obtain ⟨w5, hw5, rfl, hlt5⟩ := nat_word_pre hmi
    obtain ⟨w6, hw6, rfl, hlt6⟩ := nat_word_pre hrp
    obtain ⟨w7, hw7, rfl, hlt7⟩ := nat_word_pre hro
    obtain ⟨w8, hw8, rfl, hlt8⟩ := nat_word_pre hrc
    obtain ⟨a', pm1, x, ⟨aA, pmA, hrun1, hrun2⟩, hDf, hPf, hcp', hfr, htk, hg, hts', d, hdr, hdlo, hdhi,
      hkind, hdcv, hn5, hn6, hn8, pw, hn7, hdr7⟩ :=
      rec_rel p hp n m a pm f q D cv rls 5 w5 w6 w7 w8 dl m1 hD hP hsz hts hcv hkwm hw5 hw6 hw7 hw8
        hrl (by omega) hDt hcl
    refine ⟨a', pm1, .recInfo x.1 w5.toNat w6.toNat x.2, ?_, hDf, hPf, hcp', hfr, htk, hg, hts', ?_, ?_, ?_⟩
    · simp only [promoteCI]; rw [run_bind_ok hrun1]; simp only; rw [run_bind_ok hrun2]; rfl
    · rw [← hr', hdr]; exact hdlo
    · rw [← hr', hdr]; omega
    · rw [← hr', hdr]
      exact decCI_rc (by have h := nat?_erecP (m := m1) (i := d) (by omega) hkind; simpa using h) hdcv hn5 hn6 hn7 hn8 hdr7

end rel

end L.Arena

end
