import ConAgua.Arena.DeclDivModSpec.PureRun
import ConAgua.Arena.DeclNatBase

/-!
# Cons

`dmGgW`, `dmTpgW`, `rdW_iw_of`, `StmtL.cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

section guards
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

def dmGgW (_p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs pe : Word) : Option (List Word × Mem) :=
  ntBW (lbbF m [4000000000, 0, pe]) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  ntBW (hffF m2 [4000000000, pe]) fun r3 m3 =>
  if r3.headD 0 ≠ 0 then some ([0], m3) else
  ntBW (cl n "all_level_params_defined" [0, 0, pe] m3) fun r4 m4 =>
  if r4.headD 0 = 0 then some ([0], m4) else
  ntBW (cl n "consts_resolve_ffast" [vs, pe] m4) fun r5 m5 => some ([r5.headD 0], m5)

def dmTpgW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs nm ty : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "env_find" [nm, vs] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  ntBW (callW p n "type_pin_stored" [vs, nm] m1) fun r2 m2 =>
  ntBW (hffF m2 [4000000000, r2.headD 0]) fun r3 m3 =>
  if r3.headD 0 ≠ 0 then some ([0], m3) else
  ntBW (lbbF m3 [4000000000, 0, ty]) fun r4 m4 =>
  if r4.headD 0 = 0 then some ([0], m4) else
  ntBW (hffF m4 [4000000000, ty]) fun r5 m5 =>
  if r5.headD 0 ≠ 0 then some ([0], m5) else
  ntBW (cl n "consts_resolve_ffast" [vs, ty] m5) fun r6 m6 => some ([r6.headD 0], m6)

/-! ## `div_mod_certs_guard_go` -/

theorem rdW_iw_of {m : Mem} {x : Word} {i : Nat} {w : Word} (h : (iwA m)[i]? = some w)
    (hx : x.toNat = i) : rdW (m.arr64 IW) x = w := by
  simp only [iwA] at h; simp [rdW, hx, h]

theorem StmtL.cons {m : Mem} {so sl : Word} {s : List EIdx × EIdx} {ss : List (List EIdx × EIdx)}
    (hI : IWOK m) (h : StmtL m so.toNat sl.toNat (s :: ss)) :
    sl ≠ 0 ∧ ∃ q : Word, rdW (m.arr64 IW) so = q ∧ StmtAt m q s ∧
      StmtL m (so + 1).toNat (sl - 1).toNat ss := by
  obtain ⟨hb, hl, hj⟩ := h
  have hl0 : sl ≠ 0 := fun e => by rw [e] at hl; simp at hl
  have hlen : sl.toNat = ss.length + 1 := by simpa using hl
  have ho : (so + 1).toNat = so.toNat + 1 := by
    have h1 := hI.1; have h2 := hI.2.2.1
    rw [UInt64.toNat_add]; simp; omega
  have hl1 : (sl - 1).toNat = ss.length := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  obtain ⟨q, hq, hs⟩ := hj 0 (by simp)
  refine ⟨hl0, q, rdW_iw_of (by simpa using hq) rfl, by simpa using hs, ?_⟩
  rw [ho, hl1]
  refine ⟨by omega, rfl, fun j hj' => ?_⟩
  obtain ⟨q2, hq2, hs2⟩ := hj (j + 1) (by simpa using hj')
  exact ⟨q2, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hq2, by simpa using hs2⟩

end guards

end L.Ind

end
