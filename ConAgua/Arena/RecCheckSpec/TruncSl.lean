import ConAgua.Arena.RecCheckSpec.TcmF
import ConAgua.Arena.RecCheckSpec.Tpd
import ConAgua.Arena.RecGenSpec.Rec3IwSlice
import ConAgua.Arena.IndSumSpec.Row

/-!
# TruncSl

`tcmK6_some`, `tcmK5_some`, `tcmK4_ok`, `tcmK3_some`, `tcmK2_some`, `tcmK1_no` and the lemmas only they use.
-/

section

noncomputable section

/-!
# `RecCheck`: `targetClassMatch` (lane `indproofs3`, helper `rec`)

Levels by `lvls_eq_c` (the cached `lvlsEq?`; a master callee without a stage-level model, entered
through the stub contract `lvlsEqStub_spec` below, as `lvl_eq_c` is through `lvlEqStub_spec`), then
`block_shape_member_names`, `block_shape_lps` (L: called instead of the inlined copy of member 0's
level parameters, which it is), `param_levels`, `target_holes` and `target_params_def_eq`
(`RecCheckSpec/PdsC`). L: the depth `pfl + ftl` aborts on a wrap before `target_holes` (a capacity
abort; the twin's `Nat` sum cannot wrap). Write sets of the callees (`MFr`), so the walk memos
(`RcMR`) are carried.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis p fto ftl pfo pfl dso dsl edso edsl d : Word) (r rn rb rh rl : List Word)
theorem tcmK6_some : tcmK6 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem tcmK5_some : tcmK5 cR n vis pfo pfl dso dsl edso edsl d rn rb (some (rh, m)) =
    tcmK6 (pdeW cR n m vis d (rn.headD 0) (rn.tail.headD 0) (rb.headD 0) (rh.headD 0) (rh.tail.headD 0) pfo pfl
      dso dsl edso edsl) := rfl
theorem tcmK4_ok (h : ¬ pfl + ftl < pfl) : tcmK4 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (some (rb, m)) =
    tcmK5 cR n vis pfo pfl dso dsl edso edsl (pfl + ftl) rn rb (thW n m fto ftl pfl) := by
  simp only [tcmK4]; rw [ite_eq_right h]
theorem tcmK3_some : tcmK3 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (some (rl, m)) =
    tcmK4 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (plW n m (rl.headD 0) (rl.tail.headD 0)) := rfl
theorem tcmK2_some : tcmK2 cR n vis p fto ftl pfo pfl dso dsl edso edsl (some (rn, m)) =
    tcmK3 cR n vis fto ftl pfo pfl dso dsl edso edsl rn (lpsW n m p) := rfl
theorem tcmK1_no (h : r.headD 0 ≠ 2) : tcmK1 cR n vis p fto ftl pfo pfl dso dsl edso edsl (some (r, m)) =
    some ([0], m) := by simp only [tcmK1]; rw [ite_eq_left h]
theorem tcmK1_yes (h : ¬ r.headD 0 ≠ 2) : tcmK1 cR n vis p fto ftl pfo pfl dso dsl edso edsl (some (r, m)) =
    tcmK2 cR n vis p fto ftl pfo pfl dso dsl edso edsl (memberNamesW n m p) := by
  simp only [tcmK1]; rw [ite_eq_right h]
end arms
attribute [ind_grind] tcmK6_some tcmK5_some tcmK4_ok tcmK3_some tcmK2_some tcmK1_no tcmK1_yes

theorem targetClassMatch_spec (p : Prog) (L : TcmLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis q fto ftl pfo pfl us dso dsl lvls edso edsl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "target_class_match"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
    ⦃fun r s' => LocEq s' s₀ ∧
      tcmW cR n s₀.mem vis q fto ftl pfo pfl us dso dsl lvls edso edsl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.tcm]
  simp only [callFn, targetClassMatch]
  sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      hcR n "lvls_eq_c", blockShapeMemberNames_spec p L.ha L.mnc L.mn n,
      blockShapeLps_spec p L.ha L.erc L.eri L.lps n,
      plW_spec p L.ha L.ic L.sc L.sg L.pf L.pp L.ip L.plg L.pl L.il n,
      targetHoles_spec p L.ff L.fp L.iff L.ic L.ha L.sc L.th n, tpd_spec p L.tp cR hcR n] <;>
    finish (gen := 40) (instances := 20000) [tcmW, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
      loc_init9, loc_init10, loc_init11]

end L.Ind

end
end

end

section

noncomputable section

/-!
# `RecCheck`: `targetMajorNfs` (lane `indproofs3`, helper `rec`)

The walk's recorded constructor normal forms of a class. L (D18): the loop became the twin's list
recursion (the tail first, so the class-match calls fire from the last entry to the first), each
kept entry `sl_cons`ed onto the kept tail (a copy, so the result is a pointer slice decoded below
the tops). Callees: `ctors_have_name` (helper `recb`'s `chnW`), `target_class_match`
(`RecCheckSpec/TcmLook`), `sl_cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Reading records decoded below the tops -/

/-- A handle field of a record decoded in the cut pools, read at its word address. -/
theorem truncH {k : IdxKind} {m : Mem} {w : Word} {i : Nat} {x : Idx k}
    (h : iwH (truncM m) (w.toNat + i) = some x) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (w + UInt64.ofNat i)) ∧ decI (rdW (m.arr64 IW) (w + UInt64.ofNat i)) = x := by
  have hi : w.toNat + i < iwTop m := by
    simp only [iwH, hd?] at h
    cases hw : (iwA (truncM m))[w.toNat + i]? with
    | none => simp [hw] at h
    | some v => exact (truncM_iw_get hw).1
  rw [iwH_truncM hi] at h
  obtain ⟨v, e, hv, hd⟩ := iwH_rdW_at h hsz
  rw [e]; exact ⟨hv, hd⟩

/-- A slice field `(off, len)` of a record decoded in the cut pools, read at its word addresses. -/
theorem truncSl {k : IdxKind} {m : Mem} {w : Word} {i o l : Nat} {xs : List (Idx k)}
    (ho : iwN (truncM m) (w.toNat + i) = some o) (hl : iwN (truncM m) (w.toNat + i + 1) = some l)
    (hd : decHL (truncM m) o l = some xs) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    HSl0 m (rdW (m.arr64 IW) (w + UInt64.ofNat i)) (rdW (m.arr64 IW) (w + UInt64.ofNat (i + 1))) xs := by
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨-, hlm⟩ := rec2IwN_trunc hl
  obtain ⟨eo, to⟩ := rec2RdN (w := w) (k := i) hom hsz
  obtain ⟨el, tl⟩ := rec2RdN (w := w) (k := i + 1) (by simpa [Nat.add_assoc] using hlm) hsz
  rw [eo, el]
  rcases rec3IwSlice hd with hb | h0
  · refine HSl0.of ?_ (by rw [to, tl]; exact hb)
    rw [to, tl, ← decHL_truncM hb]; exact hd
  · subst h0
    have hx : xs = [] := by have := decHL_length _ hd; simpa using this
    subst hx
    exact ⟨by rw [tl]; simp [decHL, hslice?], .inl (UInt64.toNat_inj.mp (by rw [tl]; rfl))⟩

theorem tcmF_spec (p : Prog) (L : TcmLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St)
    (vis q fto ftl pfo pfl us dso dsl lvls edso edsl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_class_match"
      [vis, q, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl]
    ⦃fun r s' => LocEq s' s₀ ∧
      tcmF cR n s₀.mem vis q fto ftl pfo pfl us dso dsl lvls edso edsl = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetClassMatch_spec p L cR hcR n s₀ vis q fto ftl pfo pfl us dso dsl lvls edso edsl

end L.Ind

end
end

end
