import ConAgua.Arena.PromoteCIInfra
import ConAgua.Arena.PromoteCIRef.ConstsAt
import ConAgua.Arena.PromoteCIRef.Promoted
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic

/-!
# Erase

`envErase_mem`, `erase_rel`.
-/

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena
set_option experimental.vcgen true

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem envErase_mem (n : Nat) (s₀ : St) (w : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "env_erase" [w]
    ⦃fun _ s' => s'.mem = rowSet s₀.mem w 0 0 ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧
      rowIx w + 1 < (s₀.mem.arr64 (rowArr w)).size; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "env_erase")]
  simp only [callFn, envEraseL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        envRowSet_spec p (hp.get "env_ix") (hp.get "env_row_set") n] <;>
      finish

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

theorem erase_rel (dn : NIdx → Option ConLeche.Name) : ∀ (n : Nat) (m : Mem) (vis j k : Word)
    (fe : IFEnv) (installed : List IConstantInfo) (r : List Word) (m' : Mem),
    EnvR dn m vis fe → (m.arr64 EREC).size < 2 ^ 64 → k.toNat = installed.length →
    installed.length ≤ j.toNat + 1 →
    ConstsAt dn (erecP m) (m.arr64 ECON) j.toNat installed →
    callW p n "erase_installed" [j, k] m = some (r, m') →
    EnvR dn m' vis ⟨fe.env, eraseInstalled fe.idx installed, fe.visibleBelow, fe.tbls⟩ ∧
      MemFrame [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1] [] m m' := by
  intro n
  induction n with
  | zero => intro m vis j k fe installed r m' _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m vis j k fe installed r m' hE hsz hk hj hcon hc
  obtain ⟨s', hs', -, hW⟩ := callW_triple (eraseInstalled_spec p hp n ⟨m, Locals.init []⟩ j k) hc
  simp only at hW
  rw [hs'] at hW
  simp only [eraseW] at hW
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
    obtain ⟨s1, hs1, -, hE1⟩ := callW_triple
      (envErase_spec p (hp.get "env_ix") (hp.get "env_row_set") (hp.get "env_erase") n ⟨m, Locals.init []⟩ (fe := fe) vis w hE hwl) hcb
    obtain ⟨s2, hs2, hmem, -, hrt, -⟩ := callW_triple
      (envErase_mem p hp n ⟨m, Locals.init []⟩ w hwl) hcb
    have hfr : MemFrame [EIXA, EIXS, EIXN, EIXA1, EIXS1, EIXN1] [] m m1 := by
      rw [← hs2, hmem]; exact rowSet_frame _ _ _ _ hrt
    rw [hs1] at hE1
    have hEE : m1.arr64 EREC = m.arr64 EREC := hfr.1 EREC (by decide) (by decide)
    have hEC : m1.arr64 ECON = m.arr64 ECON := hfr.1 ECON (by decide) (by decide)
    have hP1 : erecP m1 = erecP m := erecP_congr hEE (hfr.2.1 129 (by simp))
    have hszz : (m1.arr64 EREC).size < 2 ^ 64 := by rw [hEE]; exact hsz
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
    have hcon' : ConstsAt dn (erecP m1) (m1.arr64 ECON) (j - 1).toNat cs := by
      rcases hjn with h | h
      · subst h; trivial
      · rw [toNat_sub1 j h, hP1, hEC]; exact hrest
    cases hcc : callW p n "erase_installed" [j - 1, k - 1] m1 with
    | none => rw [hcc] at hW; cases hW
    | some y =>
    obtain ⟨z2, m3⟩ := y
    rw [hcc, memK_some] at hW
    have hm3 : m3 = m' := Option.some.inj hW
    subst hm3
    obtain ⟨hEf, hfr2⟩ := ih m1 vis (j - 1) (k - 1) _ cs z2 m3 hE1 hszz hlenk hj1 hcon' hcc
    refine ⟨?_, hfr.trans hfr2⟩
    simp only [eraseInstalled]
    rw [hname]
    exact hEf

end rel

end L.Arena

end
