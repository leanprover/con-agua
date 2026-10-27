import ConAgua.Arena.PromoteCIRef.Fire
import ConAgua.Arena.PromoteCIRef.Proj

/-!
# Rule

`wr3_call`, `wr5_call`, `wr_core`, `wr3_rel`, `wr5_rel`, `ruleWr_rel` and the lemmas only they use.
-/

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem wr3_call {n : Nat} {d a b c : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr3" [d, a, b, c] m = some (r, m')) :
    stP d m [((0 : Word), a), ((1 : Word), b), ((2 : Word), c)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr3_spec p hp n ⟨m, Locals.init []⟩ d a b c) hc; exact hW

theorem wr5_call {n : Nat} {d a b c e g : Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "erec_wr5" [d, a, b, c, e, g] m = some (r, m')) :
    stP d m [((0 : Word), a), ((1 : Word), b), ((2 : Word), c), ((3 : Word), e), ((4 : Word), g)] = some m' := by
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (erecWr5_spec p hp n ⟨m, Locals.init []⟩ d a b c e g) hc; exact hW

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **A store of the words `ps` at offsets below `N` from `d`**, as a relation on the pool. -/
theorem wr_core {N : Nat} {d : Word} {ps : List (Word × Word)} {m m' : Mem}
    (hbd : d.toNat + N ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hN : ∀ q ∈ ps, q.1.toNat < N) (hnd : (ps.map (fun q => q.1.toNat)).Nodup)
    (h : stP d m ps = some m') :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + N ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (∀ q ∈ ps, (m'.arr64 EREC)[d.toNat + q.1.toNat]? = some q.2) := by
  obtain ⟨h1, h2, h3, -, h5⟩ := stP_nat d ps (fun q hq => by have := hN q hq; omega) hnd h
  exact ⟨h1, h2, fun i hi => h3 i fun q hq => by have := hN q hq; omega, h5⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem wr3_rel {n : Nat} {d a b c : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 3 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr3" [d, a, b, c] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 3 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr3_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

theorem wr5_rel {n : Nat} {d a b c e g : Word} {m m' : Mem} {r : List Word}
    (hbd : d.toNat + 5 ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hc : callW p n "erec_wr5" [d, a, b, c, e, g] m = some (r, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 5 ≤ i) → (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat + 0]? = some a ∧
    (m'.arr64 EREC)[d.toNat + 1]? = some b ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some c ∧
    (m'.arr64 EREC)[d.toNat + 3]? = some e ∧
    (m'.arr64 EREC)[d.toNat + 4]? = some g := by
  obtain ⟨h1, h2, h3, h5⟩ := wr_core hbd hsz
    (by simp only [List.forall_mem_cons]; decide) (by simp) (wr5_call p hp hc)
  exact ⟨h1, h2, h3, by simpa using h5⟩

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

/-- **`rule_wr`**: the constructor and right-hand side written, three words copied twice. -/
theorem ruleWr_rel {n : Nat} {d s c r w1 w2 w9 w10 : Word} {m m' : Mem} {rr : List Word}
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hsd : s.toNat + 11 ≤ d.toNat)
    (hdb : d.toNat + 11 ≤ (m.arr64 EREC).size)
    (h1 : (m.arr64 EREC)[s.toNat + 1]? = some w1) (h2 : (m.arr64 EREC)[s.toNat + 2]? = some w2)
    (h9 : (m.arr64 EREC)[s.toNat + 9]? = some w9) (h10 : (m.arr64 EREC)[s.toNat + 10]? = some w10)
    (hc : callW p n "rule_wr" [d, s, c, r] m = some (rr, m')) :
    (m'.arr64 EREC).size = (m.arr64 EREC).size ∧ MemFrame [EREC] [] m m' ∧
    (∀ i, (i < d.toNat ∨ d.toNat + 11 ≤ i ∨ (d.toNat + 3 ≤ i ∧ i < d.toNat + 8)) →
      (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) ∧
    (m'.arr64 EREC)[d.toNat]? = some c ∧ (m'.arr64 EREC)[d.toNat + 1]? = some w1 ∧
    (m'.arr64 EREC)[d.toNat + 2]? = some w2 ∧ (m'.arr64 EREC)[d.toNat + 8]? = some r ∧
    (m'.arr64 EREC)[d.toNat + 9]? = some w9 ∧ (m'.arr64 EREC)[d.toNat + 10]? = some w10 := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (ruleWr_spec p hp n ⟨m, Locals.init []⟩ d s c r) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ruleWrW] at hW
  have e1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e9 : (s + 9).toNat = s.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have e8 : (d + 8).toNat = d.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨ra, ma⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm1, hr1, -⟩ := rd2_call p hp hca
  obtain rfl := hm1.symm
  rw [rd2W_of hsz (by rw [e1]; simpa using h1) (by rw [e1]; simpa using h2)] at hr1
  subst hr1
  obtain ⟨⟨rb, mb⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm2, hr2, -⟩ := rd2_call p hp hcb
  obtain rfl := hm2.symm
  rw [rd2W_of hsz (by rw [e9]; simpa using h9) (by rw [e9]; simpa using h10)] at hr2
  subst hr2
  simp only [g0, g1, List.headD_cons, List.tail_cons] at hW
  obtain ⟨⟨rc, mc⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := wr3_rel p hp (by omega) hsz hcc
  cases hcd : callW p n "erec_wr3" [d + 8, r, w9, w10] mc with
  | none => rw [hcd] at hW; cases hW
  | some x =>
  obtain ⟨rd, md⟩ := x
  rw [hcd, memK_some] at hW
  have hm : md = m' := Option.some.inj hW
  subst hm
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := wr3_rel p hp (d := d + 8) (by rw [e8, a1]; omega) (by rw [a1]; exact hsz) hcd
  rw [e8] at b3 b4 b5 b6
  refine ⟨by rw [b1, a1], a2.trans b2, fun i hi => ?_, ?_, ?_, ?_, b4, b5, b6⟩
  · rw [b3 i (by omega), a3 i (by omega)]
  · rw [b3 d.toNat (by omega)]; simpa using a4
  · rw [b3 (d.toNat + 1) (by omega)]; exact a5
  · rw [b3 (d.toNat + 2) (by omega)]; exact a6

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem decFire_of_words {A : Array Word} {d : Nat} {k q b r y : Word} {fire : IRecRuleFire}
    (h3 : A[d + 3]? = some k) (h4 : A[d + 4]? = some q) (h5 : A[d + 5]? = some b)
    (h6 : A[d + 6]? = some r) (h7 : A[d + 7]? = some y) (hf : FireWords A k q b r y fire) :
    decFire A d = some fire := by
  unfold decFire
  have n3 : nat? A (d + 3) = some k.toNat := by simp [nat?, h3]
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, lv, ps, rfl, h1, h2⟩
  · simp [n3]
  · have n3' : nat? A (d + 3) = some 1 := by simpa using n3
    have l1 : hlist? A (d + 4) = some lv := by
      simp [hlist?, nat?, h4, h5, h1]
    have l2 : hlist? A (d + 6) = some ps := by
      simp [hlist?, nat?, h6, h7, h2]
    simp [n3', l1, l2]

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem peAt_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f addr : Word) (u : EIdx)
    (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hu : hd? (erecP m) addr.toNat = some u) (hc : callW p n "pe_at" [f, addr] m = some (r, m')) :
    AtOk (promoteE pm f.toNat u) decE m a (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (peAt_spec p hp n ⟨m, Locals.init []⟩ f addr) hc
  simp only at hW
  rw [hs'] at hW
  obtain ⟨w, hw, hwl, rfl⟩ := hd?_some hu
  have hw' := erecP_get hw
  simp only [peAtW] at hW
  obtain ⟨⟨r₁, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hm1, hr1, -⟩ := rd1_call p hp hca
  rw [rd1W_of hsz (by simpa using hw')] at hr1
  subst hr1
  obtain rfl := hm1.symm
  obtain ⟨⟨r₂, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  have key : PEOk (promoteE pm f.toNat (decE w)) m a pm (r₂.headD 0) m₂ :=
    (pe_rel p hp n).1 m a pm f w r₂ m₂ hD hP hwl hcb
  obtain ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr, htk⟩ := key
  rw [← hr]
  exact ⟨a', pm', hrun, hD', hP', hpw, hcp, hfr, htk⟩

end rel

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem FireWords.slot {m m' : Mem} {lo hi : Nat} (hg : SlotGrow m m' lo hi)
    (hts : erecTop m ≤ (m.arr64 EREC).size) (hts' : erecTop m' ≤ (m'.arr64 EREC).size)
    {k q b r y : Word} {fire : IRecRuleFire}
    (hf : FireWords (erecP m) k q b r y fire) (hq : k = 1 → hi ≤ q.toNat ∧ hi ≤ r.toNat) :
    FireWords (erecP m') k q b r y fire := by
  rcases hf with hf | ⟨hk, lv, ps, rfl, h1, h2⟩
  · exact Or.inl hf
  · obtain ⟨o1, o2⟩ := hq hk
    exact Or.inr ⟨hk, lv, ps, rfl, hg.hslice? hts hts' h1 (Or.inr (Or.inl o1)),
      hg.hslice? hts hts' h2 (Or.inr (Or.inl o2))⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem rule_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f s d : Word) (D : Nat)
    (rl : IRecRule) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hrl : decRule (preE m D) s.toNat = some rl) (hsD : s.toNat + 11 ≤ D) (hDt : D ≤ erecTop m)
    (hdD : D ≤ d.toNat) (hdT : d.toNat + 11 ≤ erecTop m)
    (hc : callW p n "promote_rule" [f, s, d] m = some (r, m')) :
    ∃ a' pm' rl', (promoteRule pm f.toNat rl).run a = .ok ((pm', rl'), a') ∧ ArenaD m' a' ∧
      PMemoR m' pm' ∧ cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧
      SlotGrow m m' d.toNat (d.toNat + 11) ∧ erecTop m' ≤ (m'.arr64 EREC).size ∧
      decRule (erecP m') d.toNat = some rl' ∧ FireHi (erecP m') d.toNat (erecTop m) := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteRule_spec p hp n ⟨m, Locals.init []⟩ f s d) hc
  simp only at hW
  rw [hs'] at hW
  simp only [ruleW] at hW
  obtain ⟨w0, w1, w2, w8, w9, w10, e0, l0, hctor, e1, hnf, e2, hcpr, e8, l8, hrhs, e9, hk, e10,
    he⟩ := pmDecRule_words hrl
  obtain ⟨-, M0⟩ := preE_get_lt e0
  obtain ⟨-, M1⟩ := preE_get_lt e1
  obtain ⟨-, M2⟩ := preE_get_lt e2
  obtain ⟨-, M8⟩ := preE_get_lt e8
  obtain ⟨-, M9⟩ := preE_get_lt e9
  obtain ⟨-, M10⟩ := preE_get_lt e10
  have hd0 : hd? (erecP m) s.toNat = some rl.ctor := by
    rw [hctor, erecP_eq_preE]; exact hd?_of_pre (by omega) M0 l0
  -- the name
  obtain ⟨⟨c, m₁⟩, hca, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, hrun1, hD1, hP1, hpw1, hcp1, hfr1, htk1⟩ :=
    pnAt_rel p hp n m a pm f s rl.ctor c m₁ hD hP hsz hd0 hca
  obtain ⟨hE1, hT1⟩ := eFrame_erec hfr1
  have hsz1 : (m₁.arr64 EREC).size < 2 ^ 64 := by rw [hE1]; exact hsz
  have hts1 : erecTop m₁ ≤ (m₁.arr64 EREC).size := by rw [hE1, hT1]; exact hts
  -- the firing mode
  have hsrc : decFire (preE m₁ D) s.toNat = some rl.fire := by
    rw [preE_congr hE1]; exact decRule_fire hrl
  obtain ⟨⟨u, m₂⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a2, pm2, fire', hrun2, hD2, hP2, hcp2, hfr2, htk2, hg2, hts2, hfw, hlo⟩ :=
    fire_rel p hp n m₁ a1 pm1 f s D rl.fire u m₂ hD1 hP1 hsz1 hts1 hsrc hsD (by rw [hT1]; exact hDt) hcb
  rw [hT1] at hlo
  have hsz2 : (m₂.arr64 EREC).size = (m.arr64 EREC).size := by rw [hg2.2.2, hE1]
  have hT12 : erecTop m ≤ erecTop m₂ := by rw [← hT1]; exact hg2.1
  have key2 : ∀ i < erecTop m, (m₂.arr64 EREC)[i]? = (m.arr64 EREC)[i]? := fun i hi => by
    rw [hg2.2.1 i (by rw [hT1]; exact hi), hE1]
  -- the right-hand side
  have hd8 : hd? (erecP m₂) (s + 8).toNat = some rl.rhs := by
    have e8' : (s + 8).toNat = s.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
    rw [e8', hrhs, erecP_eq_preE]
    exact hd?_of_pre (by omega) (by rw [key2 _ (by omega)]; exact M8) l8
  obtain ⟨⟨rr, m₃⟩, hcc, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a3, pm3, hrun3, hD3, hP3, hpw3, hcp3, hfr3, htk3⟩ :=
    peAt_rel p hp n m₂ a2 pm2 f (s + 8) rl.rhs rr m₃ hD2 hP2 (by rw [hsz2]; exact hsz) hd8 hcc
  obtain ⟨hE3, hT3⟩ := eFrame_erec hfr3
  have hsz3 : (m₃.arr64 EREC).size = (m.arr64 EREC).size := by
    have := hfr3.2.2.1 EREC; rw [this, hsz2]
  have key3 : ∀ i < erecTop m, (m₃.arr64 EREC)[i]? = (m.arr64 EREC)[i]? := fun i hi => by
    rw [hE3, key2 i hi]
  have hg03 : ErecGrow m m₃ :=
    ⟨by rw [hT3]; exact hT12, fun i hi => key3 i hi, hsz3⟩
  -- the record
  obtain ⟨⟨z, m₄⟩, hcd, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := ruleWr_rel p hp (by rw [hsz3]; exact hsz)
    (by omega) (by rw [hsz3]; omega)
    (by rw [key3 _ (by omega)]; exact M1) (by rw [key3 _ (by omega)]; exact M2)
    (by rw [key3 _ (by omega)]; exact M9) (by rw [key3 _ (by omega)]; exact M10) hcd
  have e3 : (d + 3).toNat = d.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  cases hce : callW p n "erec_wr5" [d + 3, u.headD 0, u.tail.headD 0, u.tail.tail.headD 0,
      u.tail.tail.tail.headD 0, u.tail.tail.tail.tail.headD 0] m₄ with
  | none => rw [hce] at hW; cases hW
  | some x =>
  obtain ⟨z2, m₅⟩ := x
  rw [hce, memK_some] at hW
  have hm : m₅ = m' := Option.some.inj hW
  subst hm
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := wr5_rel p hp (d := d + 3)
    (by rw [e3, q1, hsz3]; omega) (by rw [q1, hsz3]; exact hsz) hce
  rw [e3] at t3 t4 t5 t6 t7 t8
  have hsz5 : (m₅.arr64 EREC).size = (m.arr64 EREC).size := by rw [t1, q1, hsz3]
  have hT5 : erecTop m₅ = erecTop m₃ := by
    simp only [erecTop]
    rw [t2.2.1 129 (by simp), q2.2.1 129 (by simp)]
  have hfr45 : MemFrame [EREC] [] m₃ m₅ := q2.trans t2
  have hgr : SlotGrow m₃ m₅ d.toNat (d.toNat + 11) :=
    ⟨by rw [hT5]; exact Nat.le_refl _, fun i hi hout => by
      rw [t3 i (by omega), q3 i (by omega)], hsz5.trans hsz3.symm⟩
  have hgrm : SlotGrow m m₅ d.toNat (d.toNat + 11) :=
    (SlotGrow.of_grow hg03 _ _).trans hgr (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨hDf, hPf⟩ := arenaD_erecFrame hD3 hP3 hfr45
  have hts5 : erecTop m₅ ≤ (m₅.arr64 EREC).size := by rw [hT5, hT3, hsz5]; omega
  have hT53 : erecTop m ≤ erecTop m₅ := by rw [hT5, hT3]; exact hT12
  refine ⟨a3, pm3, ⟨decI (c.headD 0), rl.nfields, rl.ctorParams, fire', decE (rr.headD 0), rl.k, rl.eta⟩,
    ?_, hDf, hPf, hcp3.trans (hcp2.trans hcp1), ?_,
    htk1.trans (htk2.trans (htk3.trans (TierKeep.of_frame hfr45 (by simp)))), hgrm, hts5, ?_⟩
  · rw [promoteRule, run_bind_ok hrun1]
    simp only
    rw [run_bind_ok hrun2]
    simp only
    rw [run_bind_ok hrun3]; rfl
  · refine ((eFrame_cons hfr1).trans (hfr2)).trans ((eFrame_cons hfr3).trans
      ((hfr45).mono (by simp) (by simp)))
  · have hu5 : ∀ i, (i < d.toNat + 3 ∨ d.toNat + 8 ≤ i) →
        (m₅.arr64 EREC)[i]? = (m₄.arr64 EREC)[i]? := fun i hi => t3 i (by omega)
    have f0 : (m₅.arr64 EREC)[d.toNat]? = some (c.headD 0) := by rw [hu5 _ (by omega)]; exact q4
    have f1 : (m₅.arr64 EREC)[d.toNat + 1]? = some w1 := by rw [hu5 _ (by omega)]; exact q5
    have f2 : (m₅.arr64 EREC)[d.toNat + 2]? = some w2 := by rw [hu5 _ (by omega)]; exact q6
    have f8 : (m₅.arr64 EREC)[d.toNat + 8]? = some (rr.headD 0) := by
      rw [hu5 _ (by omega)]; exact q7
    have f9 : (m₅.arr64 EREC)[d.toNat + 9]? = some w9 := by rw [hu5 _ (by omega)]; exact q8
    have f10 : (m₅.arr64 EREC)[d.toNat + 10]? = some w10 := by rw [hu5 _ (by omega)]; exact q9
    have P : ∀ {i : Nat} {w : Word}, i < erecTop m₅ → (m₅.arr64 EREC)[i]? = some w →
        (erecP m₅)[i]? = some w := fun hi h => preE_of_get hi h
    have hfw5 : FireWords (erecP m₅) (g0 u) (g1 u) (g2 u) (g3 u) (g4 u) fire' := by
      have hEP : erecP m₃ = erecP m₂ := by
        rw [erecP_eq_preE, erecP_eq_preE, hT3]
        exact preE_congr hE3 _
      have hts3 : erecTop m₃ ≤ (m₃.arr64 EREC).size := by rw [hT3, hsz3]; omega
      have := FireWords.slot hgr hts3 hts5 (by rw [hEP]; exact hfw)
        (fun h1 => by have := hlo h1; omega)
      exact this
    have hc0 : (hd? (erecP m₅) d.toNat : Option NIdx) = some (decI (c.headD 0)) := by
      rw [erecP_eq_preE]; exact hd?_of_pre (by omega) f0 hpw1.1
    have hn1 : nat? (erecP m₅) (d.toNat + 1) = some rl.nfields := by
      rw [erecP_eq_preE, ← hnf]; exact nat?_of_pre (by omega) f1
    have hn2 : nat? (erecP m₅) (d.toNat + 2) = some rl.ctorParams := by
      rw [erecP_eq_preE, ← hcpr]; exact nat?_of_pre (by omega) f2
    have hfi : decFire (erecP m₅) d.toNat = some fire' :=
      decFire_of_words (P (by omega) (by simpa using t4)) (P (by omega) (by simpa using t5))
        (P (by omega) (by simpa using t6)) (P (by omega) (by simpa using t7))
        (P (by omega) (by simpa using t8)) hfw5
    have hr8 : (hd? (erecP m₅) (d.toNat + 8) : Option EIdx) = some (decE (rr.headD 0)) := by
      rw [erecP_eq_preE]; exact hd?_of_pre (by omega) f8 hpw3.1
    have hb9 : bool? (erecP m₅) (d.toNat + 9) = some rl.k := by
      simp [bool?, P (by omega) f9, hk]
    have hb10 : bool? (erecP m₅) (d.toNat + 10) = some rl.eta := by
      simp [bool?, P (by omega) f10, he]
    refine ⟨decRule_mk hc0 hn1 hn2 hfi hr8 hb9 hb10, ?_⟩
    intro h3
    obtain ⟨w, hw, hw1⟩ := nat?_get h3
    have g3 : (erecP m₅)[d.toNat + 3]? = some (u.headD 0) :=
      P (i := d.toNat + 3) (by omega) (by simpa using t4)
    have hwu : w = u.headD 0 := Option.some.inj (hw.symm.trans g3)
    have hu1 : u.headD 0 = 1 := UInt64.toNat_inj.mp (by rw [← hwu]; simpa using hw1)
    obtain ⟨hl1, hl2⟩ := hlo hu1
    have N : ∀ {i : Nat} {w : Word}, i < erecTop m₅ → (m₅.arr64 EREC)[i]? = some w →
        nat? (erecP m₅) i = some w.toNat := fun hi h => nat?_of_pre hi h
    exact ⟨(u.tail.headD 0).toNat, (u.tail.tail.headD 0).toNat, (u.tail.tail.tail.headD 0).toNat,
      (u.tail.tail.tail.tail.headD 0).toNat, N (by omega) (by simpa using t5),
      N (by omega) (by simpa using t6), N (by omega) (by simpa using t7),
      N (by omega) (by simpa using t8), hl1, hl2⟩

end rel

end L.Arena

end
