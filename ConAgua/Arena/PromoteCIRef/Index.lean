import ConAgua.Arena.PromoteCIInfra
import ConAgua.Arena.PromoteCIRef.ConstsAt
import ConAgua.Arena.PromoteCIRef.Promoted
import Std.Tactic.BVDecide.Normalize.Prop
import ConRon.Bridge.Grind

/-!
# Index

`index_rel`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem index_rel (dn : NIdx → Option ConLeche.Name) : ∀ (n : Nat) (m : Mem) (vis c j k : Word)
    (fe : IFEnv) (installed : List IConstantInfo) (r : List Word) (m' : Mem),
    EnvR dn m vis fe → (m.arr64 EREC).size < 2 ^ 64 → k.toNat = installed.length →
    installed.length ≤ j.toNat + 1 → installed.length ≤ c.toNat →
    ConstsAt dn (erecP m) (m.arr64 ECON) j.toNat installed →
    callW p n "index_promoted" [c, j, k] m = some (r, m') →
    EnvR dn m' vis ⟨fe.env, indexPromoted fe.idx c.toNat installed, fe.visibleBelow, fe.tbls⟩ ∧
      MemFrame [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1] [] m m' := by
  intro n
  induction n with
  | zero => intro m vis c j k fe installed r m' _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m vis c j k fe installed r m' hE hsz hk hj hcc hcon hc
  obtain ⟨s', hs', -, hW⟩ := callW_triple (indexPromoted_spec p hp n ⟨m, Locals.init []⟩ c j k) hc
  simp only at hW
  rw [hs'] at hW
  simp only [indexW] at hW
  cases installed with
  | nil =>
    have hk0 : k = 0 := UInt64.toNat_inj.mp (by simpa using hk)
    rw [ite_eq_left hk0] at hW
    have hm : m = m' := Option.some.inj hW
    subst hm
    exact ⟨hE, MemFrame.refl _ _ _⟩
  | cons ci cs =>
    have hk0 : k ≠ 0 := by
      intro h; rw [h] at hk; simp at hk
    have hc0 : c ≠ 0 := by
      intro h; rw [h] at hcc; simp at hcc
    rw [ite_eq_right hk0] at hW
    obtain ⟨⟨ptr, hptr, hdec⟩, hrest⟩ := hcon
    have hbd : j.toNat < (m.arr64 ECON).size := (Array.getElem?_eq_some_iff.mp hptr).1
    rw [ite_eq_right (by omega)] at hW
    have hrdp : rdW (m.arr64 ECON) j = ptr := by
      rw [pci_rdW_of_get? _ j (by simpa using hptr)]
    rw [hrdp] at hW
    obtain ⟨w, hwA, hwl, hname⟩ := decCI_name hdec
    have hwm := erecP_get hwA
    have hlt : ptr.toNat + 1 < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hwm).1
    have e1 : (ptr + 1).toNat = ptr.toNat + 1 := toNat_add1 _ (by omega)
    obtain ⟨⟨rr, m0⟩, hrd, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨hm0, hr0, -⟩ := rd1_call p hp hrd
    obtain rfl := hm0.symm
    rw [rd1W_of hsz (by rw [e1]; simpa using hwm)] at hr0
    subst hr0
    simp only [g0, List.headD_cons] at hW
    obtain ⟨⟨z, m1⟩, hcb, hW⟩ := Option.bind_eq_some_iff.mp hW
    dsimp only at hW
    obtain ⟨s2, hs2, hmem, -, hrt, hrb⟩ := callW_triple
      (envRowSet_spec p (hp.get "env_ix") (hp.get "env_row_set") n ⟨m, Locals.init []⟩ w c ptr hwl) hcb
    have hm1 : m1 = rowSet m w c ptr := by rw [← hs2]; exact hmem
    subst hm1
    have hfr : MemFrame [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1] [] m (rowSet m w c ptr) := rowSet_frame _ _ _ _ hrt
    have hE1 : EnvR dn (rowSet m w c ptr) vis
        ⟨fe.env, fe.idx.insert (decI w) (c.toNat - 1, ci), fe.visibleBelow, fe.tbls⟩ := by
      refine hE.setRow w c ptr hwl hrt hrb _ (some (c.toNat - 1, ci)) ?_ ?_ ?_
      · intro nn
        rw [Std.HashMap.getElem?_insert]
        by_cases e : nn.word.toUInt64 = w
        · have : decI w = nn := (decI_eq_iff w hwl nn).mpr e.symm
          simp [e, this]
        · have : ¬ decI w = nn := fun h => e ((decI_eq_iff w hwl nn).mp h).symm
          simp [e, this]
      · simp [hc0]
      · intro _; simp [hdec]
    have hEE : (rowSet m w c ptr).arr64 EREC = m.arr64 EREC := hfr.1 EREC (by decide) (by decide)
    have hEC : (rowSet m w c ptr).arr64 ECON = m.arr64 ECON := hfr.1 ECON (by decide) (by decide)
    have hP1 : erecP (rowSet m w c ptr) = erecP m := erecP_congr hEE (hfr.2.1 129 (by simp))
    have hszz : ((rowSet m w c ptr).arr64 EREC).size < 2 ^ 64 := by rw [hEE]; exact hsz
    have hlenk : (k - 1).toNat = cs.length := by
      rw [toNat_sub1 k hk0]; simp at hk; omega
    have hjn : cs = [] ∨ j ≠ 0 := by
      by_cases h : j = 0
      · left
        cases cs with
        | nil => rfl
        | cons c0 cs0 => simp only [List.length_cons] at hj; rw [h] at hj; simp at hj
      · exact .inr h
    have hj1 : cs.length ≤ (j - 1).toNat + 1 := by
      rcases hjn with h | h
      · subst h; simp
      · rw [toNat_sub1 j h]; simp only [List.length_cons] at hj; have := toNat_pred j h; omega
    have hcn : (c - 1).toNat = c.toNat - 1 := toNat_sub1 c hc0
    have hcc1 : cs.length ≤ (c - 1).toNat := by
      rw [hcn]; simp only [List.length_cons] at hcc; omega
    have hcon' : ConstsAt dn (erecP (rowSet m w c ptr)) ((rowSet m w c ptr).arr64 ECON) (j - 1).toNat cs := by
      rcases hjn with h | h
      · subst h; trivial
      · rw [toNat_sub1 j h, hP1, hEC]; exact hrest
    cases hcc' : callW p n "index_promoted" [c - 1, j - 1, k - 1] (rowSet m w c ptr) with
    | none => rw [hcc'] at hW; cases hW
    | some y =>
    obtain ⟨z2, m3⟩ := y
    rw [hcc', memK_some] at hW
    have hm3 : m3 = m' := Option.some.inj hW
    subst hm3
    obtain ⟨hEf, hfr2⟩ := ih (rowSet m w c ptr) vis (c - 1) (j - 1) (k - 1) _ cs z2 m3 hE1 hszz hlenk hj1 hcc1 hcon' hcc'
    refine ⟨?_, hfr.trans hfr2⟩
    rw [hcn] at hEf
    simp only [indexPromoted]
    rw [hname]
    exact hEf

end rel

end L.Arena
