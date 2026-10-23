import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.IndRealApdT

/-!
# `check_reduce_pin(vis, vis2, c, v)` refines `checkReducePin` (lane `decls3`)

The `Lean.reduceNat`/`Lean.reduceBool` install gate, after the opaque's push: the stored constant
at the pushed view `vis2` (`reduce_stored_ok`), then at the pre-insertion view `vis` the element
inductive, the pin's guards, the value against the pin, and the identity certificate. The stage
relation at `vis2` gives it at `vis` (`fe2.restrictTo vis`: the same index, `EnvR.restrictTo`) and
back. L change: a handle guard after `reduce_cert_var` (`is_def_eq_core`'s spec needs it).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind

/-- The stage relation at another view of the same environment. -/
theorem StageR.restrict {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR dn vis fe m a) (k : Word) :
    StageR dn k (fe.restrictTo k.toNat) m a :=
  ⟨⟨h.1.arena, h.1.core, h.1.pins, h.1.env.restrictTo k⟩, h.2⟩

theorem IFEnv.restrictTo_restrictTo (fe : IFEnv) (j k : Nat) :
    (fe.restrictTo j).restrictTo k = fe.restrictTo k := rfl

theorem IFEnv.restrictTo_self (fe : IFEnv) : fe.restrictTo fe.visibleBelow = fe := rfl

/-! ## The model -/

section model
variable (p : Prog)

/-- After the second comparison. -/
def crpK8 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m8) => if r8.headD 0 = 0 then none else some ([0], m8)

/-- After `mk_app`: the identity certificate. -/
def crpK7 (cl : CallM) (n : Nat) (vis x : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ax, m7) => crpK8 (cl n "is_def_eq_core" [vis, 1, ax, x] m7)

/-- After `reduce_cert_var`: the handle guard, the application. -/
def crpK6 (cl : CallM) (n : Nat) (vis v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    if 4294967296 ≤ r6.headD 0 then none else crpK7 cl n vis (r6.headD 0) (mkAppW m6 v (r6.headD 0))

/-- After the comparison with the pin. -/
def crpK5 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if r5.headD 0 = 0 then none else crpK6 cl n vis v (callW p n "reduce_cert_var" [c] m5)

/-- After `reduce_decl_pin`. -/
def crpK4 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => crpK5 p cl n vis c v (cl n "is_def_eq_core" [vis, 0, v, r4.headD 0] m4)

/-- After `reduce_pin_guard`. -/
def crpK3 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then none else crpK4 p cl n vis c v (callW p n "reduce_decl_pin" [c] m3)

/-- After `reduce_elem_ok`. -/
def crpK2 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none else crpK3 p cl n vis c v (callW p n "reduce_pin_guard" [vis, c] m2)

/-- After `reduce_stored_ok`. -/
def crpK1 (cl : CallM) (n : Nat) (vis c v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then none else crpK2 p cl n vis c v (callW p n "reduce_elem_ok" [vis, c] m1)

/-- **The model of `check_reduce_pin(vis, vis2, c, v)`.** -/
def crpW (cl : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, vis, vis2, c, v => crpK1 p cl n vis c v (callW p n "reduce_stored_ok" [vis2, c] m)

section arms
variable (cl : CallM) (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 m8 : Mem) (vis vis2 c v x ax : Word)
  (r1 r2 r3 r4 r5 r6 r8 : List Word)
theorem crpW_step : crpW p cl (n + 1) m vis vis2 c v =
    crpK1 p cl n vis c v (callW p n "reduce_stored_ok" [vis2, c] m) := rfl
theorem crpK1_some : crpK1 p cl n vis c v (some (r1, m1)) =
    if r1.headD 0 = 0 then none else crpK2 p cl n vis c v (callW p n "reduce_elem_ok" [vis, c] m1) :=
  rfl
theorem crpK2_some : crpK2 p cl n vis c v (some (r2, m2)) =
    if r2.headD 0 = 0 then none
    else crpK3 p cl n vis c v (callW p n "reduce_pin_guard" [vis, c] m2) := rfl
theorem crpK3_some : crpK3 p cl n vis c v (some (r3, m3)) =
    if r3.headD 0 = 0 then none else crpK4 p cl n vis c v (callW p n "reduce_decl_pin" [c] m3) := rfl
theorem crpK4_some : crpK4 p cl n vis c v (some (r4, m4)) =
    crpK5 p cl n vis c v (cl n "is_def_eq_core" [vis, 0, v, r4.headD 0] m4) := rfl
theorem crpK5_some : crpK5 p cl n vis c v (some (r5, m5)) =
    if r5.headD 0 = 0 then none else crpK6 cl n vis v (callW p n "reduce_cert_var" [c] m5) := rfl
theorem crpK6_some : crpK6 cl n vis v (some (r6, m6)) =
    if 4294967296 ≤ r6.headD 0 then none else crpK7 cl n vis (r6.headD 0) (mkAppW m6 v (r6.headD 0)) :=
  rfl
theorem crpK7_some : crpK7 cl n vis x (some (ax, m7)) =
    crpK8 (cl n "is_def_eq_core" [vis, 1, ax, x] m7) := rfl
theorem crpK8_some : crpK8 (some (r8, m8)) = if r8.headD 0 = 0 then none else some ([0], m8) := rfl
end arms

grind_pattern [ind_grind] crpW_step => crpW p cl (n + 1) m vis vis2 c v
grind_pattern [ind_grind] crpK1_some => crpK1 p cl n vis c v (some (r1, m1))
grind_pattern [ind_grind] crpK2_some => crpK2 p cl n vis c v (some (r2, m2))
grind_pattern [ind_grind] crpK3_some => crpK3 p cl n vis c v (some (r3, m3))
grind_pattern [ind_grind] crpK4_some => crpK4 p cl n vis c v (some (r4, m4))
grind_pattern [ind_grind] crpK5_some => crpK5 p cl n vis c v (some (r5, m5))
grind_pattern [ind_grind] crpK6_some => crpK6 cl n vis v (some (r6, m6))
grind_pattern [ind_grind] crpK7_some => crpK7 cl n vis x (some (ax, m7))
grind_pattern [ind_grind] crpK8_some => crpK8 (some (r8, m8))

/-- The lookups of `check_reduce_pin`. -/
structure CrpProg (p : Prog) : Prop where
  red : RedProg p
  rcv : RcvProg p
  crp : p.lookup "check_reduce_pin" = some checkReducePinL
  rpg : p.lookup "reduce_pin_guard" = some reducePinGuardL
  rdp : p.lookup "reduce_decl_pin" = some reduceDeclPinL
  db : p.lookup "der_b" = some derB
  af : p.lookup "app_find" = some appFind
  ap : p.lookup "app_push" = some appPush
  ia : p.lookup "intern_app" = some internApp
  ma : p.lookup "mk_app" = some mkApp
  bvb : BvbProg p
  hf : HfF p
  /-- `all_level_params_defined`'s program (`reduce_pin_guard` under `StageT`, `DeclCrpT.lean`). -/
  apd : L.Ind.ApdF p

set_option maxHeartbeats 1600000 in
theorem crp_specW (h : CrpProg p) (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St) (vis vis2 c v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_reduce_pin" [vis, vis2, c, v]
    ⦃fun r s' => LocEq s' s₀ ∧ crpW p cl n s₀.mem vis vis2 c v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.crp]
  simp only [callFn, checkReducePinL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        callW_spec p n "reduce_stored_ok", callW_spec p n "reduce_elem_ok",
        callW_spec p n "reduce_pin_guard", callW_spec p n "reduce_decl_pin",
        hc n "is_def_eq_core", callW_spec p n "reduce_cert_var",
        mkApp_spec p h.db h.af h.ap h.ia h.ma n] <;>
      finish (gen := 20)

end model

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_reduce_pin` refines `checkReducePin`** at the model level: from the stage relation at
the pushed view `vis2`, the gate at `vis` and back. -/
theorem crpW_ok {p : Prog} (h : CrpProg p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis vis2 : Word} {fe2 : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {c v : Word}
    {r : List Word} (hW : crpW p stubCall n m vis vis2 c v = some (r, m')) (hS : StageR dn vis2 fe2 m a)
    (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32) :
    ∃ a', (checkReducePin V (fe2.restrictTo vis.toNat) fe2 (decI c) (decI v)).run a = .ok ((), a') ∧
      StageR dn vis2 fe2 m' a' ∧ IWGrow m m' := by
  cases n with
  | zero => simp [crpW] at hW
  | succ n =>
  rw [crpW_step] at hW
  -- the stored constant, at `vis2`
  cases h1 : callW p n "reduce_stored_ok" [vis2, c] m with
  | none => rw [h1] at hW; cases hW
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, crpK1_some] at hW
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hb1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceStoredOk_refines p h.red dn vis2 fe2 c hc n ⟨m, Locals.init []⟩ a hS) h1
  subst hs1
  have hrun1 := AM.run_of_ok _ _ hok1
  by_cases e1 : r1.headD 0 = 0
  · rw [if_pos e1] at hW; cases hW
  rw [if_neg e1] at hW
  have t1 : AM.res (reduceStoredOk fe2 (decI c)) a = true := by rw [← hb1]; simpa using e1
  rw [t1] at hrun1
  generalize AM.st (reduceStoredOk fe2 (decI c)) a = a1 at hrun1 hS1
  -- at the pre-insertion view
  have hS1' := StageR.restrict hS1 vis
  generalize hfe : fe2.restrictTo vis.toNat = fe at hS1' ⊢
  -- the element inductive
  cases h2 : callW p n "reduce_elem_ok" [vis, c] s1.mem with
  | none => rw [h2] at hW; cases hW
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, crpK2_some] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hb2, -⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (reduceElemOk_refines p h.red dn hdn vis fe c hc n ⟨s1.mem, Locals.init []⟩ a1 hS1') h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  by_cases e2 : r2.headD 0 = 0
  · rw [if_pos e2] at hW; cases hW
  rw [if_neg e2] at hW
  have t2 : AM.res (reduceElemOk fe (decI c)) a1 = true := by rw [← hb2]; simpa using e2
  rw [t2] at hrun2
  generalize AM.st (reduceElemOk fe (decI c)) a1 = a2 at hrun2 hS2
  -- the pin's guards
  cases h3 : callW p n "reduce_pin_guard" [vis, c] s2.mem with
  | none => rw [h3] at hW; cases hW
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, crpK3_some] at hW
  obtain ⟨s3, hs3, -, hok3, hS3, hg3, hb3, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (reducePinGuard_refines p h.red.pa h.bvb h.hf h.rdp h.rpg n ⟨s2.mem, Locals.init []⟩ a2 dn fe vis c hS2 hc h.red.rom)
    h3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  by_cases e3 : r3.headD 0 = 0
  · rw [if_pos e3] at hW; cases hW
  rw [if_neg e3] at hW
  have t3 : AM.res (reducePinGuard fe (decI c)) a2 = true := by rw [← hb3]; simpa using e3
  rw [t3] at hrun3
  generalize AM.st (reducePinGuard fe (decI c)) a2 = a3 at hrun3 hS3
  -- the pin
  cases h4 : callW p n "reduce_decl_pin" [c] s3.mem with
  | none => rw [h4] at hW; cases hW
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, crpK4_some] at hW
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hpl, hpe⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (reduceDeclPin_refines p h.red.pa n ⟨s3.mem, Locals.init []⟩ a3 dn fe vis c hS3 hc h.red.rom h.rdp) h4
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  rw [← hpe] at hrun4
  generalize AM.st (reduceDeclPin (decI c)) a3 = a4 at hrun4 hS4
  -- the value against the pin
  cases h5 : stubCall n "is_def_eq_core" [vis, 0, v, r4.headD 0] s4.mem with
  | none => rw [h5] at hW; simp [crpK5] at hW
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, crpK5_some] at hW
  obtain ⟨x5, a5, hrun5, hS5, hg5, hx5, -⟩ :=
    L.Ind.isDefEqCore_spec dn vis fe 0 v (r4.headD 0) hv hpl s4.mem m5 a4 r5 h5 hS4
  by_cases e5 : r5.headD 0 = 0
  · rw [if_pos e5] at hW; cases hW
  rw [if_neg e5] at hW
  have t5 : x5 = true := by rw [← hx5]; simpa using e5
  -- the certificate's variable
  cases h6 : callW p n "reduce_cert_var" [c] m5 with
  | none => rw [h6] at hW; simp [crpK6] at hW
  | some rm6 =>
  obtain ⟨r6, m6⟩ := rm6
  rw [h6, crpK6_some] at hW
  obtain ⟨s6, hs6, -, hok6, hS6, hg6, hx6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (reduceCertVar_refines p h.rcv n ⟨m5, Locals.init []⟩ a5 dn fe vis c hS5 hc) h6
  subst hs6
  have hrun6 := AM.run_of_ok _ _ hok6
  rw [hx6] at hrun6
  generalize AM.st (reduceCertVar (decI c)) a5 = a6 at hrun6 hS6
  by_cases e6 : 4294967296 ≤ r6.headD 0
  · rw [if_pos e6] at hW; cases hW
  rw [if_neg e6] at hW
  have hxl : (r6.headD 0).toNat < 2 ^ 32 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp e6); simpa using this
  -- the application
  cases h7 : mkAppW s6.mem v (r6.headD 0) with
  | none => rw [h7] at hW; cases hW
  | some rm7 =>
  obtain ⟨ax, m7⟩ := rm7
  rw [h7, crpK7_some] at hW
  obtain ⟨a7, hrun7, hS7, hg7⟩ := mkApp_stage hS6 v (r6.headD 0) h7
  have haxl := mkAppW_hw s6.mem a6 hS6.1.arena v (r6.headD 0) ax m7 h7
  -- the identity certificate
  cases h8 : stubCall n "is_def_eq_core" [vis, 1, ax, r6.headD 0] m7 with
  | none => rw [h8] at hW; simp [crpK8] at hW
  | some rm8 =>
  obtain ⟨r8, m8⟩ := rm8
  rw [h8, crpK8_some] at hW
  obtain ⟨x8, a8, hrun8, hS8, hg8, hx8, -⟩ :=
    L.Ind.isDefEqCore_spec dn vis fe 1 ax (r6.headD 0) haxl hxl m7 m8 a7 r8 h8 hS7
  by_cases e8 : r8.headD 0 = 0
  · rw [if_pos e8] at hW; cases hW
  rw [if_neg e8] at hW
  have t8 : x8 = true := by rw [← hx8]; simpa using e8
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  refine ⟨a8, ?_, ?_, hg1.trans (hg2.trans (hg3.trans (hg4.trans (hg5.trans (hg6.trans
    (hg7.trans hg8))))))⟩
  · have h00 : (0 : Word).toNat = 0 := rfl
    have h01 : (1 : Word).toNat = 1 := rfl
    rw [h00] at hrun5
    rw [h01] at hrun8
    simp only [checkReducePin, StateT.run_bind, hrun1, exc_ok_bind', if_true]
    simp only [hrun2, exc_ok_bind', if_true, StateT.run_bind, hrun3, hrun4, hrun5, t5, hrun6]
    have e7 : (internE (.app (decI v) (decE (r6.headD 0)))).run a6 = .ok (decE ax, a7) := hrun7
    simp only [e7, exc_ok_bind', StateT.run_bind]
    have e8 : (isDefEqCore V fe checkFuel 1 (decE ax) (decE (r6.headD 0))).run a7 =
        .ok (x8, a8) := hrun8
    simp only [e8, t8, if_true, StateT.run_bind]
    rfl
  · have hvb : fe2.visibleBelow = vis2.toNat := hS.1.env.vis
    have := StageR.restrict hS8 vis2
    rw [← hfe, IFEnv.restrictTo_restrictTo, ← hvb, IFEnv.restrictTo_self] at this
    exact this

/-- **`check_reduce_pin(vis, vis2, c, v)` refines `checkReducePin`** (through the core's, the
walks' and the ROM stubs; the census link is `crpW_okT`, `DeclCrpT.lean`). -/
theorem checkReducePin_refines (p : Prog) (h : CrpProg p) (dn : NIdx → Option ConLeche.Name)
    (hdn : DnInj dn) (vis vis2 : Word) (fe2 : IFEnv) (c v : Word) (hc : c.toNat < 2 ^ 32)
    (hv : v.toNat < 2 ^ 32) :
    RefAM p "check_reduce_pin" [vis, vis2, c, v] (StageR dn vis2 fe2)
      (checkReducePin V (fe2.restrictTo vis.toNat) fe2 (decI c) (decI v))
      (KeepPost dn vis2 fe2 decUnit) := by
  intro n s₀ a₀ hS
  refine triple_post (crp_specW p h stubCall (stubCall_spec p) n s₀ vis vis2 c v) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg⟩ := crpW_ok h hdn hm hS hc hv
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact ⟨hS', hg, trivial⟩⟩

end L.Arena
