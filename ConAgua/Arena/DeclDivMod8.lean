import ConAgua.Arena.DeclDivMod7

/-!
# The `Nat.div` family's pin gate, bottom up: the certificates (lane `decls3`, `decls3-divmod`)

Part 8: `check_div_mod_certs`, `check_type_pins`, `check_div_mod_pin_value`,
`check_div_mod_pin_at`. The inference and the definitional equality are the stubs'
(`inferTypeCore_spec`, `isDefEqCore_spec`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

structure DmProg8 (p : Prog) : Prop extends DmProg7 p where
  lCheckDivModCerts : p.lookup "check_div_mod_certs" = some checkDivModCertsL
  lCheckDivModPinAt : p.lookup "check_div_mod_pin_at" = some checkDivModPinAtL
  lCheckTypePins : p.lookup "check_type_pins" = some checkTypePinsL
  lCheckDivModPinValue : p.lookup "check_div_mod_pin_value" = some checkDivModPinValueL
  lCheckDivModPinLoop : p.lookup "check_div_mod_pin_loop" = some checkDivModPinLoopL
  lCheckDivModPin : p.lookup "check_div_mod_pin" = some checkDivModPinL

section certs
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

def cmW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs c annVal so sl po pl : Word) : Option (List Word × Mem) :=
  if sl = 0 ∧ pl = 0 then some ([1], m) else
  if sl = 0 ∨ pl = 0 then some ([0], m) else
  ntBW (callW p n "div_mod_cert_guard" [vs, c, annVal, rdW (m.arr64 IW) (rdW (m.arr64 IW) so),
    rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 2),
    rdW (m.arr64 IW) po] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  ntBW (callW p n "subst_const_all" [c, annVal, 4000000000, rdW (m1.arr64 IW) po] m1) fun r2 m2 =>
  ntBW (callW p n "subst_const0_list" [c, annVal, rdW (m2.arr64 IW) (rdW (m.arr64 IW) so),
    rdW (m2.arr64 IW) (rdW (m.arr64 IW) so + 1)] m2) fun r3 m3 =>
  ntBW (callW p n "div_mod_cert_applied" [r2.headD 0, r3.headD 0, r3.tail.headD 0] m3) fun r4 m4 =>
  ntBW (cl n "infer_type_core" [vs, 4, r4.headD 0] m4) fun r5 m5 =>
  ntBW (callW p n "subst_const0" [c, annVal, 4000000000,
    rdW (m5.arr64 IW) (rdW (m.arr64 IW) so + 2)] m5) fun r6 m6 =>
  ntBW (cl n "is_def_eq_core" [vs, 4, r5.headD 0, r6.headD 0] m6) fun r7 m7 =>
  if r7.headD 0 = 0 then some ([0], m7) else
  ntBW (callW p n "check_div_mod_certs" [vs, c, annVal, so + 1, sl - 1, po + 1, pl - 1] m7) fun r8 m8 =>
    some ([r8.headD 0], m8)

set_option maxHeartbeats 3200000 in
theorem cm_specW (p : Prog) (hp : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
    (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St) (vs c annVal so sl po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_div_mod_certs" [vs, c, annVal, so, sl, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ cmW p cl n s₀.mem vs c annVal so sl po pl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDivModCertsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_cert_guard", callW_spec p n "subst_const_all",
      callW_spec p n "subst_const0_list", callW_spec p n "div_mod_cert_applied",
      hc n "infer_type_core", callW_spec p n "subst_const0",
      hc n "is_def_eq_core", callW_spec p n "check_div_mod_certs"] <;>
    finish (gen := 30) (instances := 10000) [cmW, ntBW, rdW_eq]

/-! ## `check_type_pins` -/

def dmCtpW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs o l : Word) : Option (List Word × Mem) :=
  if l = 0 then some ([1], m) else
  ntBW (callW p n "type_pin_stored" [vs, rdW (m.arr64 EREC) o] m) fun r1 m1 =>
  ntBW (cl n "is_def_eq_core" [vs, 0, r1.headD 0, rdW (m1.arr64 EREC) (o + 1)] m1) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  ntBW (callW p n "check_type_pins" [vs, o + 2, l - 1] m2) fun r3 m3 => some ([r3.headD 0], m3)

set_option maxHeartbeats 3200000 in
theorem ctp_specW (p : Prog) (hp : p.lookup "check_type_pins" = some checkTypePinsL)
    (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St) (vs o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_type_pins" [vs, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ dmCtpW p cl n s₀.mem vs o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkTypePinsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "type_pin_stored", hc n "is_def_eq_core", callW_spec p n "check_type_pins"] <;>
    finish (gen := 30) (instances := 10000) [dmCtpW, ntBW, rdW_eq]

/-! ## `check_div_mod_pin_value` -/

def dmCpvW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs c value ps : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "div_mod_decl_pin" [ps, c] m) fun r1 m1 =>
  ntBW (cl n "is_def_eq_core" [vs, 0, value, r1.headD 0] m1) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  ntBW (callW p n "div_mod_cert_stmts" [c] m2) fun r3 m3 =>
  ntBW (callW p n "div_mod_cert_proofs" [ps, c] m3) fun r4 m4 =>
  ntBW (callW p n "check_div_mod_certs" [vs, c, value, r3.headD 0, r3.tail.headD 0, r4.headD 0,
    r4.tail.headD 0] m4) fun r5 m5 => some ([r5.headD 0], m5)

set_option maxHeartbeats 3200000 in
theorem cpv_specW (p : Prog) (hp : p.lookup "check_div_mod_pin_value" = some checkDivModPinValueL)
    (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St) (vs c value ps : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_div_mod_pin_value" [vs, c, value, ps]
    ⦃fun r s' => LocEq s' s₀ ∧ dmCpvW p cl n s₀.mem vs c value ps = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDivModPinValueL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_decl_pin", hc n "is_def_eq_core",
      callW_spec p n "div_mod_cert_stmts", callW_spec p n "div_mod_cert_proofs",
      callW_spec p n "check_div_mod_certs"] <;>
    finish (gen := 30) (instances := 10000) [dmCpvW, ntBW]

/-! ## `check_div_mod_pin_at` -/

/-- **`check_div_mod_pin_at` is its model `cpaW`** (generated). -/
l_model cpa_specW (p : Prog) (hp : p.lookup "check_div_mod_pin_at" = some checkDivModPinAtL)
  fns [hp ↦ cpaW list]
  specs [callW_spec p n "div_mod_type_pins", callW_spec p n "check_type_pins",
    callW_spec p n "check_div_mod_pin_value"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW]

end certs

end L.Ind
