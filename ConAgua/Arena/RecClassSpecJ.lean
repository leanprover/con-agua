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

def gtK3 (n : Nat) (g c rP fo fl maj : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (t, m2) => if 4294967296 ≤ t then none else gtK2 (rtW n m2 g c rP fo fl maj t)

def gtK1 (n : Nat) (g c rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else if rP + r1.tail.tail.headD 0 < rP then none
    else gtK3 n g c rP (r1.tail.headD 0) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0)
      (fvinternW m1 (rP + r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0))

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
theorem gtK1_fail (h : r1.headD 0 = 0) : gtK1 n g c rP (some (r1, m1)) = some ([0, 0], m1) := by
  rw [gtK1, if_pos h]
theorem gtK1_ov (h : r1.headD 0 ≠ 0) (h2 : rP + r1.tail.tail.headD 0 < rP) : gtK1 n g c rP (some (r1, m1)) = none := by
  rw [gtK1, if_neg h, if_pos h2]
theorem gtK1_ok (h : r1.headD 0 ≠ 0) (h2 : ¬ rP + r1.tail.tail.headD 0 < rP) : gtK1 n g c rP (some (r1, m1)) =
    gtK3 n g c rP (r1.tail.headD 0) (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0)
      (fvinternW m1 (rP + r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0)) := by
  rw [gtK1, if_neg h, if_neg h2]
theorem gtK3_big (h : 4294967296 ≤ t) : gtK3 n g c rP fo fl maj (some (t, m2)) = none := by
  rw [gtK3, if_pos h]
theorem gtK3_ok (h : ¬ 4294967296 ≤ t) : gtK3 n g c rP fo fl maj (some (t, m2)) =
    gtK2 (rtW n m2 g c rP fo fl maj t) := by
  rw [gtK3, if_neg h]
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
grind_pattern [ind_grind] gtK1_fail => gtK1 n g c rP (some (r1, m1))
grind_pattern [ind_grind] gtK1_ov => gtK1 n g c rP (some (r1, m1))
grind_pattern [ind_grind] gtK1_ok => gtK1 n g c rP (some (r1, m1))
grind_pattern [ind_grind] gtK3_big => gtK3 n g c rP fo fl maj (some (t, m2))
grind_pattern [ind_grind] gtK3_ok => gtK3 n g c rP fo fl maj (some (t, m2))

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
      finish (gen := 20) [rdW_eq]

/-! ## `class_gen_rec_ty` refines `classGenRecTy` -/

/-- The twin's `classGenRecTy` after the major variable. -/
def rec2RecTyTail (G : ClassGen) (c : Nat) (ifs : List EIdx) (maj t : EIdx) : AM (Option EIdx) := do
  let ibs ← ifs.mapM G.binder
  let mv ← G.motVar c
  let body ← mkAppN mv (ifs ++ [t])
  let r ← ConRon.Arena.closeTelescope (G.pre ++ ibs ++ [maj]) 0 body
  pure (some r)

theorem rec2RecTy_eq (G : ClassGen) (c : Nat) : ConRon.Arena.classGenRecTy G c = (do
    match ← G.major c G.pre.length with
    | none => pure none
    | some (ifs, maj) => do
      let t ← internE (.fvar (G.pre.length + ifs.length) maj)
      rec2RecTyTail G c ifs maj t) := rfl

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem rtW_sim (n : Nat) (m : Mem) (a : AState) (g c rP fo fl maj t : Word) (G : ClassGen)
    (ifs : List EIdx) (po : Nat) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hpo : iwN m (g.toNat + 12) = some po)
    (hpre : DecB (fun m => (decHL m po rP.toNat : Option (List EIdx))) m G.pre)
    (hifs : decHL m fo.toNat fl.toNat = some ifs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hmaj : H maj) (ht : H t) :
    RSim (rtW n m g c rP fo fl maj t) (rec2RecTyTail G c.toNat ifs (decI maj) (decI t)) a
      (KP dn vis fe m decOE) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [rtW_eq]
  unfold rec2RecTyTail
  rw [rec2MapM_genBinder]
  obtain ⟨-, hgt, -⟩ := rec2CG_parts hG
  refine RSim.bind (K := rtK1 n g c rP fo fl maj t) rfl ((fvarTypeDs_spec dn vis fe fo fl ifs).sim ⟨hS, hifs⟩) ?_
  rintro ⟨r1, m1⟩ ibs a1 - ⟨hS1, hg1, hibs, hib⟩
  dsimp only at hS1 hg1 hibs hib
  simp only [getD_zero, Nat.zero_add, getD_one] at hibs hib
  rw [rtK1_some]
  have hpo1 : iwN m1 (g.toNat + 12) = some po := by rw [iwN_grow hg1 (by omega)]; exact hpo
  obtain ⟨e12, t12⟩ := rec2RdN (w := g) (k := 12) hpo1 hS1.2.2.2.1
  simp only [show UInt64.ofNat 12 = (12 : Word) from rfl] at e12
  rw [e12]
  refine RSim.lstep (K := rtK2 n g c fo fl maj t) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hS2, hg2, hd2, hb2⟩ := rec2AppendW_dec h2 hS1 (by rw [t12]; exact hpre.grow (OMono.decHL _ _) hg1) hibs hib
  rw [rtK2_some]
  refine RSim.lstep (K := rtK3 n g c fo fl t) rfl fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hr3, hd3, hg3, -, -, ht3⟩ := snocW_dec h3 hS2.2.2.2.1 hS2.2.2.2.2.2 hb2 hmaj hd2
  have hS3 := snocW_stage h3 hS2
  rw [rtK3_some]
  have hg13 := hg1.trans (hg2.trans hg3)
  refine RSim.bind (K := rtK4 n fo fl t (r3.headD 0) (r3.tail.headD 0)) rfl
    (rec2SimMotVar n hS3 c (hG.grow (decCG_mono _) hg13) hns) ?_
  rintro ⟨r4, m4⟩ mv a4 - ⟨hS4, hg4, hmvH, hmvd⟩
  dsimp only at hS4 hg4 hmvH hmvd
  subst hmvd
  rw [rtK4_some]
  have hg14 := hg13.trans hg4
  refine RSim.lstep (K := rtK5 n (r3.headD 0) (r3.tail.headD 0) (r4.headD 0)) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hr5, hd5, hg5, -, -, ht5⟩ := snocW_dec h5 hS4.2.2.2.1 hS4.2.2.2.2.2 (Nat.le_trans hfb hg14.1) ht
    (by rw [decHL_grow hg14 hfb]; exact hifs)
  have hS5 := snocW_stage h5 hS4
  rw [rtK5_some]
  rw [hr5] at ⊢
  simp only [List.headD_cons, List.tail_cons]
  refine RSim.bind (K := rtK6 n (r3.headD 0) (r3.tail.headD 0)) rfl
    ((mkAppN_spec dn vis fe _ _ _ hmvH (ifs ++ [decI t])).sim ⟨hS5, hd5⟩) ?_
  rintro ⟨r6, m6⟩ body a6 - ⟨hS6, hg6, hbH, hbd⟩
  dsimp only at hS6 hg6 hbH hbd
  rw [rtK6_some]
  have hg36 := hg4.trans (hg5.trans hg6)
  have hb3 : (r3.headD 0).toNat + (r3.tail.headD 0).toNat ≤ iwTop m3 := by rw [hr3]; simp only [List.headD_cons, List.tail_cons]; omega
  have hd3' : decHL m6 (r3.headD 0).toNat (r3.tail.headD 0).toNat = some (G.pre ++ ibs ++ [decI maj]) := by
    rw [decHL_grow hg36 hb3, hr3]; exact hd3
  refine RSim.bind (K := rtK7) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m6 b.2 ∧
    decW0E b.2 b.1 x) ?_ ?_
  · rintro ⟨r7, m7⟩ h7
    obtain ⟨x, a', hrun, hS', hg, hx⟩ := closeW_ok n dn fe vis m6 m7 a6 _ _ 0 _ _ r7 h7 hS6 hbH hd3'
      (hS6.lt64 (Nat.le_trans hb3 hg36.1)) (Nat.le_trans hb3 hg36.1) (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact UInt64.toNat_lt _)
    refine ⟨x, a', ?_, hS', hg, hx⟩
    rw [← hbd]; simpa using hrun
  rintro ⟨r7, m7⟩ x a7 - ⟨hS7, hg7, hx⟩
  rw [rtK7_some]
  exact RSim.pure_some ⟨hS7, hg14.trans (hg5.trans (hg6.trans hg7)), rfl, by simpa [decW0E] using hx⟩

end sims

theorem gtW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c : Word) (G : ClassGen) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64) :
    RSim (gtW n m g c) (ConRon.Arena.classGenRecTy G c.toNat) a (KP dn vis fe m decOE) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [gtW_eq, rec2RecTy_eq]
  obtain ⟨-, hgt, -, -, -, ⟨o12, l12, h12, h13, hpre⟩⟩ := rec2CG_parts hG
  obtain ⟨e13, t13⟩ := rec2RdN (w := g) (k := 13) h13 hS.2.2.2.1
  simp only [show UInt64.ofNat 13 = (13 : Word) from rfl] at e13
  rw [e13]
  have hlen : G.pre.length = l12 := decHL_length _ (hpre.get (OMono.decHL _ _))
  have hm := mjW_sim dn vis fe n m a g c (UInt64.ofNat l12) G hS hG
  have hd13 : (UInt64.ofNat l12 : Word).toNat = G.pre.length := by rw [t13, hlen]
  rw [hd13] at hm
  refine RSim.bind (K := gtK1 n g c (UInt64.ofNat l12)) rfl hm ?_
  rintro ⟨r1, m1⟩ o1 a1 - ⟨hS1, hg1, ho1⟩
  dsimp only at hS1 hg1 ho1
  cases o1 with
  | none =>
    rw [gtK1_fail (h := ho1)]
    exact RSim.pure_some ⟨hS1, hg1, rfl⟩
  | some p1 =>
  obtain ⟨ifs, maj⟩ := p1
  obtain ⟨h11, ⟨hifs, hfb⟩, hmH, hmd⟩ := ho1
  simp only [getD_one, getD_two, Nat.reduceAdd] at hifs hfb
  simp only [drop3_headD] at hmH hmd
  have h10 : r1.headD 0 ≠ 0 := by rw [h11]; decide
  by_cases hov : UInt64.ofNat l12 + r1.tail.tail.headD 0 < UInt64.ofNat l12
  · rw [gtK1_ov (h := h10) (h2 := hov)]; exact RSim.none
  rw [gtK1_ok (h := h10) (h2 := hov)]
  have hu : (UInt64.ofNat l12 + r1.tail.tail.headD 0).toNat = G.pre.length + ifs.length := by
    have : ¬ (UInt64.ofNat l12 + r1.tail.tail.headD 0).toNat < (UInt64.ofNat l12 : Word).toNat :=
      fun x => hov (UInt64.lt_iff_toNat_lt.mpr x)
    rw [UInt64.toNat_add] at this ⊢
    have h1 : l12 < 2 ^ 64 := by have := (UInt64.ofNat l12 : Word).toNat_lt; rw [t13] at this; exact this
    have h2 := (r1.tail.tail.headD 0).toNat_lt
    rw [decHL_length _ hifs, hlen]
    rw [t13] at this ⊢
    omega
  have hi := simInternFVar hS1 (UInt64.ofNat l12 + r1.tail.tail.headD 0) hmH
  rw [hu, hmd] at hi
  refine RSim.bind (K := gtK3 n g c _ _ _ _) rfl hi ?_
  rintro ⟨t, m2⟩ x a2 - ⟨hS2, hg2, rfl⟩
  dsimp only at hS2 hg2
  by_cases hbig : 4294967296 ≤ t
  · rw [gtK3_big (h := hbig)]; exact RSim.none
  rw [gtK3_ok (h := hbig)]
  have htH : H t := by
    have : ¬ (4294967296 : Word).toNat ≤ t.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg12 := hg1.trans hg2
  have hr := rtW_sim (dn := dn) (vis := vis) (fe := fe) n m2 a2 g c (UInt64.ofNat l12) _ _ _ t G ifs o12 hS2
    (hG.grow (decCG_mono _) hg12) hns (by rw [iwN_grow hg12 (by omega)]; exact h12)
    (by rw [t13]; exact hpre.grow (OMono.decHL _ _) hg12) (by rw [decHL_grow hg2 hfb]; exact hifs)
    (Nat.le_trans hfb hg2.1) hmH htH
  rw [hmd] at hr
  refine RSim.bindPure (K := gtK2) rfl hr ?_
  rintro ⟨r5, m5⟩ y a5 - ⟨hS5, hg5, hy⟩
  rw [gtK2_some]
  refine RSim.pure_some ⟨hS5, hg12.trans hg5, ?_⟩
  cases y with
  | none => exact hy
  | some e => obtain ⟨h1, h2⟩ := hy; exact ⟨by simpa using h1, by simpa [decW0E] using h2⟩

/-- **`class_gen_rec_ty` refines `classGenRecTy`** (through the stubs of `class_gen_major`,
`fvar_type_ds`, `mk_app_n_f` and `close_telescope`'s `abstract1_fast`; the generator decoded below
the tops). -/
@[refines ConRon.Arena.classGenRecTy]
theorem classGenRecTy_refines (p : Prog) (hp : GtProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rec_ty" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classGenRecTy G c.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.classGenRecTy G c.toNat) a₀)
        (AM.res (ConRon.Arena.classGenRecTy G c.toNat) a₀); ⊤⦄ :=
  triple_post (classGenRecTy_spec p hp n s₀ g c) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (gtW_sim dn vis fe n _ a₀ g c G hS hG hns).am hw⟩

end L.Ind
