import ConAgua.Arena.RecClassSpecI
import ConAgua.Arena.IndPos2SpecF

/-!
# `RecClass`: `classGenRecTy` (lane `indproofs2`, helper `rec2`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Pieces -/

theorem rec2CG_get {m : Mem} {g : Nat} {G : ClassGen} (h : decCG m g = some G) :
    iwN m g = some G.nP ∧ decAt m (decPL m (decCS m)) (g + 7) = some G.slots := by
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, rfl⟩ := h
  exact ⟨hnP, hsl⟩

/-- `class_gen_mot_var` at every fuel. -/
def rec2MotVarF (n : Nat) (m : Mem) (g c : Word) : Option (List Word × Mem) :=
  fuelW n (motVarW (n - 1) m g c)

theorem rec2MotVar_specF (p : Prog) (h : MtProg p) (hff : p.lookup "fvar_find" = some fvarFind)
    (hfp : p.lookup "fvar_push" = some fvarPush) (hif : p.lookup "intern_fvar" = some internFVar)
    (hsv : p.lookup "class_gen_slot_var" = some classGenSlotVar)
    (hms : p.lookup "class_read_motive_slot" = some classReadMotiveSlot)
    (hp : p.lookup "class_gen_mot_var" = some classGenMotVar) (n : Nat) (s₀ : St) (g c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_mot_var" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rec2MotVarF n s₀.mem g c = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact motVar_spec p h.pw h.sf h.sp h.isort hff hfp hif hsv hms hp n s₀ g c

theorem rec2SimMotVar {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (n : Nat) (hS : StageR dn vis fe m a) {g : Word} (c : Word) {G : ClassGen}
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64) :
    RSim (rec2MotVarF n m g c) (ConRon.Arena.ClassGen.motVar G c.toNat) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ H (b.1.headD 0) ∧ decE (b.1.headD 0) = x) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rintro ⟨r, m'⟩ h
  obtain ⟨-, hgt, -⟩ := rec2CG_parts hG
  obtain ⟨hg, hsl⟩ := rec2CG_get (hG.get (decCG_mono _))
  have := hS.2.1; have := hS.2.2.2.1
  obtain ⟨x, a', hrun, hS', hg', h1, h2⟩ := motVarW_ok dn vis fe n m m' a g c G r hS hg (by omega) hsl
    hns (by omega) hS.2.2.2.1 h
  exact ⟨x, a', hrun, hS', hg', h1, h2⟩

/-! ## `class_gen_rec_ty_tail` -/

def rtK7 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) => some ([1, r7.headD 0], m7)

def rtK6 (n : Nat) (b2o b2l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => rtK7 (closeW n m6 b2o b2l 0 (r6.headD 0))

def rtK5 (n : Nat) (b2o b2l mv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => rtK6 n b2o b2l (stubM "mk_app_n_f" m5 [mv, r5.headD 0, r5.tail.headD 0])

def rtK4 (n : Nat) (fo fl t b2o b2l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => rtK5 n b2o b2l (r4.headD 0) (snocW n m4 fo fl t)

def rtK3 (n : Nat) (g c fo fl t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => rtK4 n fo fl t (r3.headD 0) (r3.tail.headD 0) (rec2MotVarF n m3 g c)

def rtK2 (n : Nat) (g c fo fl maj t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => rtK3 n g c fo fl t (snocW n m2 (r2.headD 0) (r2.tail.headD 0) maj)

def rtK1 (n : Nat) (g c rP fo fl maj t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    rtK2 n g c fo fl maj t (appendW n m1 (rdW (m1.arr64 IW) (g + 12)) rP (r1.headD 0) (r1.tail.headD 0))

/-- **The model of `class_gen_rec_ty_tail`.** -/
def rtW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, g, c, rP, fo, fl, maj, t => rtK1 n g c rP fo fl maj t (stubM "fvar_type_ds" m [fo, fl])

def gtK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def gtK1 (n : Nat) (g c rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else if rP + r1.tail.tail.headD 0 < rP then none
    else match fvinternW m1 (rP + r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) with
      | none => none
      | some (t, m2) =>
        if 4294967296 ≤ t then none
        else gtK2 (rtW n m2 g c rP (r1.tail.headD 0) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) t)

/-- **The model of `class_gen_rec_ty`.** -/
def gtW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, g, c => gtK1 n g c (rdW (m.arr64 IW) (g + 13)) (mjW n m g c (rdW (m.arr64 IW) (g + 13)))

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 : Mem) (g c rP fo fl maj t b2o b2l mv : Word)
  (r r1 r2 r3 r4 r5 r6 r7 : List Word)
theorem rtW_eq : rtW (n + 1) m g c rP fo fl maj t = rtK1 n g c rP fo fl maj t (stubM "fvar_type_ds" m [fo, fl]) := rfl
theorem rtK1_some : rtK1 n g c rP fo fl maj t (some (r1, m1)) =
    rtK2 n g c fo fl maj t (appendW n m1 (rdW (m1.arr64 IW) (g + 12)) rP (r1.headD 0) (r1.tail.headD 0)) := rfl
theorem rtK2_some : rtK2 n g c fo fl maj t (some (r2, m2)) =
    rtK3 n g c fo fl t (snocW n m2 (r2.headD 0) (r2.tail.headD 0) maj) := rfl
theorem rtK3_some : rtK3 n g c fo fl t (some (r3, m3)) =
    rtK4 n fo fl t (r3.headD 0) (r3.tail.headD 0) (rec2MotVarF n m3 g c) := rfl
theorem rtK4_some : rtK4 n fo fl t b2o b2l (some (r4, m4)) = rtK5 n b2o b2l (r4.headD 0) (snocW n m4 fo fl t) := rfl
theorem rtK5_some : rtK5 n b2o b2l mv (some (r5, m5)) =
    rtK6 n b2o b2l (stubM "mk_app_n_f" m5 [mv, r5.headD 0, r5.tail.headD 0]) := rfl
theorem rtK6_some : rtK6 n b2o b2l (some (r6, m6)) = rtK7 (closeW n m6 b2o b2l 0 (r6.headD 0)) := rfl
theorem rtK7_some : rtK7 (some (r7, m7)) = some ([1, r7.headD 0], m7) := rfl
theorem gtW_eq : gtW (n + 1) m g c =
    gtK1 n g c (rdW (m.arr64 IW) (g + 13)) (mjW n m g c (rdW (m.arr64 IW) (g + 13))) := rfl
theorem gtK2_some : gtK2 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] rtW_eq => rtW (n + 1) m g c rP fo fl maj t
grind_pattern [ind_grind] rtK1_some => rtK1 n g c rP fo fl maj t (some (r1, m1))
grind_pattern [ind_grind] rtK2_some => rtK2 n g c fo fl maj t (some (r2, m2))
grind_pattern [ind_grind] rtK3_some => rtK3 n g c fo fl t (some (r3, m3))
grind_pattern [ind_grind] rtK4_some => rtK4 n fo fl t b2o b2l (some (r4, m4))
grind_pattern [ind_grind] rtK5_some => rtK5 n b2o b2l mv (some (r5, m5))
grind_pattern [ind_grind] rtK6_some => rtK6 n b2o b2l (some (r6, m6))
grind_pattern [ind_grind] rtK7_some => rtK7 (some (r7, m7))
grind_pattern [ind_grind] gtW_eq => gtW (n + 1) m g c
grind_pattern [ind_grind] gtK2_some => gtK2 (some (r, m))

/-- The lookups `class_gen_rec_ty` needs. -/
structure GtProg (p : Prog) extends MtProg p : Prop where
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  ifv : p.lookup "intern_fvar" = some internFVar
  sv : p.lookup "class_gen_slot_var" = some classGenSlotVar
  ms : p.lookup "class_read_motive_slot" = some classReadMotiveSlot
  mv : p.lookup "class_gen_mot_var" = some classGenMotVar
  snoc : p.lookup "sl_snoc" = some slSnoc
  rtt : p.lookup "class_gen_rec_ty_tail" = some classGenRecTyTail
  rt : p.lookup "class_gen_rec_ty" = some classGenRecTy

theorem classGenRecTyTail_spec (p : Prog) (h : GtProg p) (n : Nat) (s₀ : St) (g c rP fo fl maj t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rec_ty_tail" [g, c, rP, fo, fl, maj, t]
    ⦃fun r s' => LocEq s' s₀ ∧ rtW n s₀.mem g c rP fo fl maj t = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rtt]
  simp only [callFn, classGenRecTyTail]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "fvar_type_ds" n, slAppend_specW p h.alloc h.copy h.app n,
        slSnoc_specW p h.alloc h.copy h.snoc n,
        rec2MotVar_specF p h.toMtProg h.fvf h.fvp h.ifv h.sv h.ms h.mv n,
        stubM_spec p "mk_app_n_f" n, closeTelescope_spec p h.db h.ff h.fp h.ifa h.mkf h.ct n] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6]

theorem classGenRecTy_spec (p : Prog) (h : GtProg p) (n : Nat) (s₀ : St) (g c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rec_ty" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ gtW n s₀.mem g c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rt]
  simp only [callFn, classGenRecTy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classGenMajor_spec p h.toMjProg n, internFVar_spec p h.fvf h.fvp h.ifv n,
        classGenRecTyTail_spec p h n] <;>
      finish (gen := 20) [rdW_eq, gtK1]

end L.Ind
