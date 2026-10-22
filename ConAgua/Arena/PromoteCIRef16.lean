import ConAgua.Arena.PromoteCIRef15

/-!
# The constant arms: common vocabulary, `pci_plain`, `pci_ctor`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- **The result of a `pci_*` arm** (`α`: what the twin returns besides the memo; `P` its run;
`Q` the decoding of the new record at `d`): a fresh record `d` of `K` words at or above the old
top, whose kind word is `kw`. -/
def ArmOk {α : Type} (m : Mem) (a : AState) (r : List Word) (m' : Mem) (K : Nat) (kw : Word)
    (P : α → AState → PMemo → Prop) (Q : α → Mem → Nat → Prop) : Prop :=
  ∃ (a' : AState) (pm' : PMemo) (x : α), P x a' pm' ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧
    cp a' = cp a ∧ MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ ErecGrow m m' ∧
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

/-- **The constant value, then `pci_mk`**: the words of the promoted value land in the new
record, which then decodes. -/
theorem mk_decode {n : Nat} {M0 M1 M2 : Mem} {c r : List Word} {q k kw : Word}
    {cv' : IConstantVal} (hCV : CVWords M0 c cv') (hext : ArrExt (erecP M0) (erecP M1))
    (hts1 : erecTop M1 ≤ (M1.arr64 EREC).size) (hsz : (M1.arr64 EREC).size < 2 ^ 64)
    (hkw : (M1.arr64 EREC)[q.toNat]? = some kw) (hk5 : 5 ≤ k.toNat)
    (hmk : callW p (n + 1) "pci_mk" [q, k, g0 c, g1 c, g2 c, g3 c] M1 = some (r, M2)) :
    (r.headD 0).toNat = erecTop M1 ∧ erecTop M2 = erecTop M1 + k.toNat ∧ ErecGrow M1 M2 ∧
    MemFrame [EREC] [129] M1 M2 ∧ erecTop M2 ≤ (M2.arr64 EREC).size ∧
    (M2.arr64 EREC)[erecTop M1]? = some kw ∧ decCV (erecP M2) (erecTop M1 + 1) = some cv' := by
  obtain ⟨hr, hT, hg, hfr, hroom, w0, w1, w2, w3, w4⟩ := pciMk_rel p hp hsz hkw hk5 hmk
  obtain ⟨-, hpw0, hn0, hsl, hpw3, ht3⟩ := hCV
  have hts2 : erecTop M2 ≤ (M2.arr64 EREC).size := by rw [hT]; exact hroom
  have P : ∀ {i : Nat} {w : Word}, i < erecTop M2 → (M2.arr64 EREC)[i]? = some w →
      (erecP M2)[i]? = some w := fun hi h => preE_of_get hi h
  have hs' : hslice? (erecP M2) (g1 c).toNat (g2 c).toNat = some cv'.levelParams :=
    hg.ext.hslice? (hext.hslice? hsl)
  have hdcv := decCV_mk (A := erecP M2) (d := erecTop M1) (nm := g0 c) (qq := g1 c) (l := g2 c)
    (t := g3 c) (P (by omega) w1) (P (by omega) w2) (P (by omega) w3) (P (by omega) w4) hpw0.1
    hpw3.1 hs'
  refine ⟨hr, hT, hg, hfr, hts2, w0, ?_⟩
  rw [hdcv, hn0, ht3]

theorem plain_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (cv : IConstantVal) (kw : Word) (r : List Word) (m' : Mem) (hD : ArenaD m a)
    (hP : PMemoR m pm) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hts : erecTop m ≤ (m.arr64 EREC).size)
    (hcv : decCV (preE m D) (q.toNat + 1) = some cv) (hkw : (m.arr64 EREC)[q.toNat]? = some kw)
    (hqD : q.toNat + 5 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "pci_plain" [f, q] m = some (r, m')) :
    ArmOk m a r m' 5 kw
      (fun (cv' : IConstantVal) a' pm' => (promoteCV pm f.toNat cv).run a = .ok ((pm', cv'), a'))
      (fun cv' M d => decCV (erecP M) (d + 1) = some cv') := by
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
  cases hca : callW p (n + 1) "promote_cv" [f, q + 1] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨c, m₁⟩ := x
  rw [hca] at hW
  simp only [Option.bind_some] at hW
  obtain ⟨a1, pm1, cv', hrun1, hD1, hP1, hCV, hg1, hts1, hcp1, hfr1⟩ :=
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
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := mk_decode p hp (n := n) hCV (ArrExt.refl _) hts1 hsz1 hkw1
    (by simp only [show ((5 : Word)).toNat = 5 from rfl]; omega) hmk
  simp only [show ((5 : Word)).toNat = 5 from rfl] at b2
  obtain ⟨hDf, hPf⟩ := arenaD_erec129 hD1 hP1 b4
  refine ⟨a1, pm1, cv', hrun1, hDf, hPf, hcp1, ?_, hg1.trans b3, b5, erecTop m₁, ?_, hg1.1, ?_, b6,
    b7⟩
  · exact (hfr1.trans (b4.mono (by simp) (by simp)))
  · rw [← hr]; exact b1
  · rw [b2]; omega

end rel

end L.Arena
