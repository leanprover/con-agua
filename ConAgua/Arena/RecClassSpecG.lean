import ConAgua.Arena.RecClassSpecF

/-!
# `RecClass`: `classReadSlots` (lane `indproofs2`, helper `rec`)
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Model -/

l_model classReadSlotsSnoc_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "class_read_slots_snoc" = some classReadSlotsSnoc)
  fns [hp ↦ motSnocW list]
  specs [slSnoc_specW p ha hc hsn n]
  grind [arena_grind] simp []

theorem snocW_room {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word}
    (h : snocW n m o l x = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m) {xs : List Nat}
    (hxs : decNL m o.toNat l.toNat = some xs) : iwTop m' ≤ (m'.arr64 IW).size := by
  obtain ⟨-, -, -, hf, -, htop⟩ := snocW_decN h hsz hc hsrc hxs
  rw [hf.2.2.1 IW]
  simp only [snocW] at h
  have h0 : l + 1 ≠ 0 := by intro e0; simp [e0] at h
  simp only [h0, ite_false] at h
  rcases hal : allocW m (l + 1) with _ | qm
  · simp [hal] at h
  obtain ⟨hq, -, hroom⟩ := allocW_facts hal hsz
  rw [← htop, ← hq]; exact hroom

/-- `class_read_slots_snoc` under the stage relation. -/
theorem motSnocW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {N : Nat} {m m' : Mem} {mo ml np d : Word} {r : List Word} {xs : List Nat}
    (h : motSnocW N m mo ml np d = some (r, m')) (hS : StageR dn vis fe m a)
    (hsrc : mo.toNat + ml.toNat ≤ iwTop m) (hxs : decNL m mo.toNat ml.toNat = some xs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ [d.toNat - np.toNat]) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  rcases N with _ | N
  · simp [motSnocW] at h
  have key : ∀ x, x.toNat = d.toNat - np.toNat → motSnocW.k_sl_snoc (snocW N m mo ml x) = some (r, m') →
      StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ [d.toNat - np.toNat]) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := fun x hx h2 => by
    obtain ⟨⟨r3, m3⟩, h3, h2⟩ := of_K h2 rfl
    rw [motSnocW.k_sl_snoc.arm1] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
    obtain ⟨hr, hdn, hg, hf, -, htop⟩ := snocW_decN h3 hS.2.2.2.1 hS.2.2.2.2.2 hsrc hxs
    have hroom := snocW_room h3 hS.2.2.2.1 hS.2.2.2.2.2 hsrc hxs
    refine ⟨stage_frame_iw hS hf (by rw [← hf.2.2.1 IW]; exact hroom), hg, ?_, ?_⟩
    · rw [hr]; simpa [hx] using hdn
    · rw [hr]; simpa using htop
  by_cases hle : np ≤ d
  · rw [motSnocW.arm1 (hc1 := hle)] at h
    exact key _ (UInt64.toNat_sub_of_le _ _ hle) h
  · rw [motSnocW.arm2 (hc1 := hle)] at h
    exact key 0 (by have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle); simp; omega) h

mutual
/-- **The model of `class_read_slots`.** -/
def slotsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | N + 1, m, p, vis, np, n, mo, ml, d, e =>
    if n = 0 then some ([1, 0, 0], m)
    else if e >>> 28 ≠ 6 then some ([0, 0, 0], m)
    else if eViewW m e = [] then none
    else ssK1 cR N p vis np n mo ml d ((eViewW m e).tail.headD 0) ((eViewW m e).tail.tail.headD 0)
      (slotW cR N m p vis np mo ml d ((eViewW m e).tail.headD 0))

/-- After `class_read_slot`. -/
def ssK1 (cR : CallM) (N : Nat) (p vis np n mo ml d dom body : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0, 0], m1)
    else ssK1b (nextW cR N m1 p vis np n mo ml d dom body (r1.tail.headD 0))

/-- After `class_read_slots_next`. -/
def ssK1b : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m)

/-- **The model of `class_read_slots_next`.** -/
def nextW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | N + 1, m, p, vis, np, n, mo, ml, d, dom, body, slot =>
    if rdW (m.arr64 IW) slot = 0 then
      ssK2 cR N p vis np n d dom body slot (motSnocW N m mo ml np d)
    else ssK3 cR N p vis np n d dom body slot mo ml m

/-- After `sl_snoc`. -/
def ssK2 (cR : CallM) (N : Nat) (p vis np n d dom body slot : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ssK3 cR N p vis np n d dom body slot (r2.headD 0) (r2.tail.headD 0) m2

/-- `intern_fvar`. -/
def ssK3 (cR : CallM) (N : Nat) (p vis np n d dom body slot mo2 ml2 : Word) (m2 : Mem) : Option (List Word × Mem) :=
  ssK4 cR N p vis np n d body slot mo2 ml2 (fvinternW m2 d dom)

/-- After `intern_fvar`. -/
def ssK4 (cR : CallM) (N : Nat) (p vis np n d body slot mo2 ml2 : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (fv, m3) =>
    if 4294967296 ≤ fv then none
    else ssK5 cR N p vis np n d slot mo2 ml2 (i1F m3 [CWF, body, fv, 0])

/-- After `instantiate1_fast`. -/
def ssK5 (cR : CallM) (N : Nat) (p vis np n d slot mo2 ml2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ssK6 N slot (slotsW cR N m4 p vis np (n - 1) mo2 ml2 (d + 1) (r4.headD 0))

/-- After the recursive call. -/
def ssK6 (N : Nat) (slot : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if r5.headD 0 = 0 then some ([0, 0, 0], m5)
    else ssK7 (consW N m5 slot (r5.tail.headD 0) (r5.tail.tail.headD 0))

/-- After `sl_cons`. -/
def ssK7 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => some ([1, r6.headD 0, r6.tail.headD 0], m6)
end

section arms
variable (N : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (p vis np n mo ml d e dom body slot mo2 ml2 fv : Word)
  (r1 r2 r4 r5 r6 : List Word) (cR : CallM)
theorem slotsW_zero (h : n = 0) : slotsW cR (N + 1) m p vis np n mo ml d e = some ([1, 0, 0], m) := by
  rw [slotsW, ite_eq_left h]
theorem slotsW_tag (h : n ≠ 0) (h2 : e >>> 28 ≠ 6) :
    slotsW cR (N + 1) m p vis np n mo ml d e = some ([0, 0, 0], m) := by
  rw [slotsW, ite_eq_right h, ite_eq_left h2]
theorem slotsW_nil (h : n ≠ 0) (h2 : ¬ e >>> 28 ≠ 6) (h3 : eViewW m e = []) :
    slotsW cR (N + 1) m p vis np n mo ml d e = none := by
  rw [slotsW, ite_eq_right h, ite_eq_right h2, ite_eq_left h3]
theorem slotsW_ok (h : n ≠ 0) (h2 : ¬ e >>> 28 ≠ 6) (h3 : eViewW m e ≠ []) :
    slotsW cR (N + 1) m p vis np n mo ml d e =
      ssK1 cR N p vis np n mo ml d ((eViewW m e).tail.headD 0) ((eViewW m e).tail.tail.headD 0)
        (slotW cR N m p vis np mo ml d ((eViewW m e).tail.headD 0)) := by
  rw [slotsW, ite_eq_right h, ite_eq_right h2, ite_eq_right h3]
theorem ssK1_fail (h : r1.headD 0 = 0) : ssK1 cR N p vis np n mo ml d dom body (some (r1, m1)) =
    some ([0, 0, 0], m1) := by rw [ssK1, ite_eq_left h]
theorem ssK1_ok (h : r1.headD 0 ≠ 0) : ssK1 cR N p vis np n mo ml d dom body (some (r1, m1)) =
    ssK1b (nextW cR N m1 p vis np n mo ml d dom body (r1.tail.headD 0)) := by rw [ssK1, ite_eq_right h]
theorem ssK1b_some : ssK1b (some (r1, m1)) =
    some ([r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0], m1) := by rw [ssK1b]
theorem nextW_mot (h : rdW (m.arr64 IW) slot = 0) : nextW cR (N + 1) m p vis np n mo ml d dom body slot =
    ssK2 cR N p vis np n d dom body slot (motSnocW N m mo ml np d) := by
  rw [nextW, ite_eq_left h]
theorem nextW_min (h : rdW (m.arr64 IW) slot ≠ 0) : nextW cR (N + 1) m p vis np n mo ml d dom body slot =
    ssK3 cR N p vis np n d dom body slot mo ml m := by
  rw [nextW, ite_eq_right h]
theorem ssK2_some : ssK2 cR N p vis np n d dom body slot (some (r2, m2)) =
    ssK3 cR N p vis np n d dom body slot (r2.headD 0) (r2.tail.headD 0) m2 := by rw [ssK2]
theorem ssK3_eq : ssK3 cR N p vis np n d dom body slot mo2 ml2 m2 =
    ssK4 cR N p vis np n d body slot mo2 ml2 (fvinternW m2 d dom) := by rw [ssK3]
theorem ssK4_big (h : 4294967296 ≤ fv) : ssK4 cR N p vis np n d body slot mo2 ml2 (some (fv, m3)) = none := by
  rw [ssK4, ite_eq_left h]
theorem ssK4_ok (h : ¬ 4294967296 ≤ fv) : ssK4 cR N p vis np n d body slot mo2 ml2 (some (fv, m3)) =
    ssK5 cR N p vis np n d slot mo2 ml2 (i1F m3 [CWF, body, fv, 0]) := by
  rw [ssK4, ite_eq_right h]
theorem ssK5_some : ssK5 cR N p vis np n d slot mo2 ml2 (some (r4, m4)) =
    ssK6 N slot (slotsW cR N m4 p vis np (n - 1) mo2 ml2 (d + 1) (r4.headD 0)) := by rw [ssK5]
theorem ssK6_fail (h : r5.headD 0 = 0) : ssK6 N slot (some (r5, m5)) = some ([0, 0, 0], m5) := by
  rw [ssK6, ite_eq_left h]
theorem ssK6_ok (h : r5.headD 0 ≠ 0) : ssK6 N slot (some (r5, m5)) =
    ssK7 (consW N m5 slot (r5.tail.headD 0) (r5.tail.tail.headD 0)) := by rw [ssK6, ite_eq_right h]
theorem ssK7_some : ssK7 (some (r6, m6)) = some ([1, r6.headD 0, r6.tail.headD 0], m6) := by rw [ssK7]
end arms

grind_pattern [ind_grind] slotsW_zero => slotsW cR (N + 1) m p vis np n mo ml d e
grind_pattern [ind_grind] slotsW_tag => slotsW cR (N + 1) m p vis np n mo ml d e
grind_pattern [ind_grind] slotsW_nil => slotsW cR (N + 1) m p vis np n mo ml d e
grind_pattern [ind_grind] slotsW_ok => slotsW cR (N + 1) m p vis np n mo ml d e
grind_pattern [ind_grind] ssK1_fail => ssK1 cR N p vis np n mo ml d dom body (some (r1, m1))
grind_pattern [ind_grind] ssK1_ok => ssK1 cR N p vis np n mo ml d dom body (some (r1, m1))
grind_pattern [ind_grind] ssK1b_some => ssK1b (some (r1, m1))
grind_pattern [ind_grind] nextW_mot => nextW cR (N + 1) m p vis np n mo ml d dom body slot
grind_pattern [ind_grind] nextW_min => nextW cR (N + 1) m p vis np n mo ml d dom body slot
grind_pattern [ind_grind] ssK2_some => ssK2 cR N p vis np n d dom body slot (some (r2, m2))
grind_pattern [ind_grind] ssK3_eq => ssK3 cR N p vis np n d dom body slot mo2 ml2 m2
grind_pattern [ind_grind] ssK4_big => ssK4 cR N p vis np n d body slot mo2 ml2 (some (fv, m3))
grind_pattern [ind_grind] ssK4_ok => ssK4 cR N p vis np n d body slot mo2 ml2 (some (fv, m3))
grind_pattern [ind_grind] ssK5_some => ssK5 cR N p vis np n d slot mo2 ml2 (some (r4, m4))
grind_pattern [ind_grind] ssK6_fail => ssK6 N slot (some (r5, m5))
grind_pattern [ind_grind] ssK6_ok => ssK6 N slot (some (r5, m5))
grind_pattern [ind_grind] ssK7_some => ssK7 (some (r6, m6))

/-- The lookups `class_read_slots` needs. -/
structure SlotsProg (p : Prog) : Prop extends SlotProg p where
  sn : p.lookup "sl_snoc" = some slSnoc
  ff : p.lookup "fvar_find" = some fvarFind
  fp : p.lookup "fvar_push" = some fvarPush
  ifv : p.lookup "intern_fvar" = some internFVar
  slots : p.lookup "class_read_slots" = some classReadSlots
  next : p.lookup "class_read_slots_next" = some classReadSlotsNext
  msn : p.lookup "class_read_slots_snoc" = some classReadSlotsSnoc
  hi1 : I1Prog p

set_option maxHeartbeats 1000000 in
theorem classReadSlots_specs (p : Prog) (hP : SlotsProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat) :
    (∀ (s₀ : St) (q vis np n mo ml d e : Word),
      ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read_slots" [q, vis, np, n, mo, ml, d, e]
      ⦃fun r s' => LocEq s' s₀ ∧ slotsW cR N s₀.mem q vis np n mo ml d e = some (r, s'.mem); ⊤⦄) ∧
    (∀ (s₀ : St) (q vis np n mo ml d dom body slot : Word),
      ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read_slots_next"
        [q, vis, np, n, mo, ml, d, dom, body, slot]
      ⦃fun r s' => LocEq s' s₀ ∧ nextW cR N s₀.mem q vis np n mo ml d dom body slot = some (r, s'.mem);
        ⊤⦄) := by
  induction N with
  | zero =>
    refine ⟨fun s₀ q vis np n mo ml d e => ?_, fun s₀ q vis np n mo ml d dom body slot => ?_⟩
    · rw [invoke_eq _ hP.slots]; simp only [callFn, classReadSlots]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hP.next]; simp only [callFn, classReadSlotsNext]; vcgen [exec] <;> grind
  | succ N ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun s₀ q vis np n mo ml d e => ?_, fun s₀ q vis np n mo ml d dom body slot => ?_⟩
    · rw [invoke_eq _ hP.slots]; simp only [callFn, classReadSlots]
      sym only [lang_grind, arena_grind, ind_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
          eView_spec p hP.v N, classReadSlot_spec p hP.toSlotProg cR hcR N, ih2] <;>
        finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]
    · rw [invoke_eq _ hP.next]; simp only [callFn, classReadSlotsNext]
      sym only [lang_grind, arena_grind, ind_grind] =>
        vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
          classReadSlotsSnoc_spec p hP.a hP.c hP.sn hP.msn N, internFVar_spec p hP.ff hP.fp hP.ifv N,
          i1F_spec p hP.hi1 N, slCons_specW p hP.a hP.c hP.sc N, ih1] <;>
        finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9]

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Relational lemma -/

theorem viewBindW {m : Mem} {a : AState} (hR : ArenaR m a) {w : Word} (hH : H w)
    (hne : eViewW m w ≠ []) (hg : w >>> 28 = 6) :
    (viewBind (decE w)).run a = .ok (some (decE ((eViewW m w).tail.headD 0),
      decE ((eViewW m w).tail.tail.headD 0)), a) ∧
      H ((eViewW m w).tail.headD 0) ∧ H ((eViewW m w).tail.tail.headD 0) := by
  obtain ⟨hvok, hew⟩ := eViewW_forall m w hg hne
  obtain ⟨-, h1, h2⟩ := view_forall m a hR w hH hvok hg
  have hvb := viewBind_forall m a hR w hH hvok hg
  rw [hew]
  simp only [List.tail_cons, List.headD_cons]
  exact ⟨by rw [viewBind_run', hvb], h1, h2⟩

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

theorem simInternFVar (hS : StageR dn vis fe m a) (u : Word) {ty : Word} (hty : H ty) :
    RSim (fvinternW m u ty) (internFVarE u.toNat (decI ty)) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ x = decE b.1) := by
  rintro ⟨r, m'⟩ h
  obtain ⟨a', hrun, hS', hg⟩ := internFVar_stage hS u ty hty h
  exact ⟨decE r, a', hrun, hS', hg, rfl⟩

theorem simInst1 (hS : StageR dn vis fe m a) {e v : Word} (he : H e) :
    RSim (i1F m [CWF, e, v, 0]) (instantiate1Fast coreWalkFuel (decI e) (decI v) 0)
      a (KP dn vis fe m decW0E) := by
  rintro ⟨r, m'⟩ hb
  have h := i1F_ok dn vis fe e v 0 he m m' a r hb hS
  rw [CWF_eq] at h; exact h

end sims

theorem motSnocW_afr {N : Nat} {m m' : Mem} {mo ml np d : Word} {r : List Word}
    (h : motSnocW N m mo ml np d = some (r, m')) : AFr m m' := by
  rcases N with _ | N
  · simp [motSnocW] at h
  simp only [motSnocW, motSnocW.k_sl_snoc.eq_def] at h
  afr_auto h [snocW_afr]

/-- `class_read_slots`'s result. -/
def decSlots (m' : Mem) (r : List Word) : Option (List ClassSlot) → Prop
  | none => r.headD 0 = 0
  | some sl => r.headD 0 = 1 ∧ SPL decCS m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat sl

/-- The twin's `classReadSlots` after the slot and the motive positions. -/
def slotsRest (bs : BlockShape) (fe : IFEnv) (np k : Nat) (motPos' : List Nat) (d : Nat)
    (dom body : EIdx) (slot : ClassSlot) : AM (Option (List ClassSlot)) := do
  let fv ← internFVarE d dom
  let b2 ← instantiate1Fast coreWalkFuel body fv 0
  match ← ConRon.Arena.classReadSlots bs fe np k motPos' (d + 1) b2 with
  | none => pure none
  | some rest => pure (some (slot :: rest))

theorem slotsRest_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (p np : Word)
    (bs : BlockShape) (N : Nat)
    (ih : ∀ (m : Mem) (a : AState) (n mo ml d e : Word) (motPos : List Nat),
      StageR dn vis fe m a → J m → H e → BSOK m p.toNat bs → decNL m mo.toNat ml.toNat = some motPos →
      mo.toNat + ml.toNat ≤ iwTop m → d.toNat + n.toNat < 2 ^ 64 →
      RSim (slotsW cR N m p vis np n mo ml d e)
        (ConRon.Arena.classReadSlots bs fe np.toNat n.toNat motPos d.toNat (decI e)) a
        (fun b a' x => KP dn vis fe m decSlots b a' x ∧ J b.2))
    (m0 m2 : Mem) (a2 : AState) (n d dom body slotw mo2 ml2 : Word) (k : Nat) (motPos' : List Nat)
    (slot : ClassSlot) (hS : StageR dn vis fe m2 a2) (hJ : J m2) (hg : IWGrow m0 m2) (hdom : H dom)
    (hbody : H body)
    (hb : BSOK m2 p.toNat bs) (hmot : decNL m2 mo2.toNat ml2.toNat = some motPos')
    (hmt : mo2.toNat + ml2.toNat ≤ iwTop m2) (hn : n.toNat = k + 1) (hd : d.toNat + n.toNat < 2 ^ 64)
    (hsl : StabD (fun m => decCS m slotw.toNat) m2 slot) :
    RSim (ssK3 cR N p vis np n d dom body slotw mo2 ml2 m2)
      (slotsRest bs fe np.toNat k motPos' d.toNat (decI dom) (decI body) slot) a2
      (fun b a' x => KP dn vis fe m0 decSlots b a' x ∧ J b.2) := by
  rw [ssK3_eq]
  refine RSim.bind (K := ssK4 cR N p vis np n d body slotw mo2 ml2) (by rw [ssK4])
    (RSim.withJ hO.1 (simInternFVar hS d hdom) (fun _ _ hb => fvinternW_afr hb) hJ) ?_
  rintro ⟨fv, m3⟩ x a3 - ⟨⟨hS3, hg3, rfl⟩, hJ3⟩
  dsimp only at hS3 hg3 hJ3
  by_cases hbig : 4294967296 ≤ fv
  · rw [ssK4_big (h := hbig)]; exact RSim.none
  rw [ssK4_ok (h := hbig)]
  have hfv : H fv := by
    have : ¬ (4294967296 : Word).toNat ≤ fv.toNat := fun e => hbig (UInt64.le_iff_toNat_le.mpr e)
    simp at this; exact this
  refine RSim.bind (K := ssK5 cR N p vis np n d slotw mo2 ml2) (by rw [ssK5])
    (RSim.withJ hO.1 (simInst1 hS3 hbody) (fun _ _ hb => i1F_afr hb) hJ3) ?_
  rintro ⟨r4, m4⟩ b2 a4 - ⟨⟨hS4, hg4, hb4, rfl⟩, hJ4⟩
  dsimp only at hS4 hg4 hb4 hJ4
  rw [ssK5_some]
  have hg24 := hg3.trans hg4
  have hn1 : (n - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have h := ih m4 a4 (n - 1) mo2 ml2 (d + 1) (r4.headD 0) motPos' hS4 hJ4 hb4 (hb.grow hg24)
    (by rw [decNL_grow hg24 hmt]; exact hmot) (Nat.le_trans hmt hg24.1) (by rw [hn1, hd1]; omega)
  rw [hn1, hd1] at h
  refine RSim.bind (K := ssK6 N slotw) (by rw [ssK6]) h ?_
  rintro ⟨r5, m5⟩ o a5 - ⟨⟨hS5, hg5, hd5⟩, hJ5⟩
  dsimp only at hS5 hg5 hd5 hJ5
  have hg25 := hg24.trans hg5
  rcases o with _ | rest
  · rw [ssK6_fail (h := hd5)]; exact RSim.pure_some ⟨⟨hS5, hg.trans hg25, rfl⟩, hJ5⟩
  obtain ⟨h51, hsp⟩ := hd5
  rw [ssK6_ok (h := by rw [h51]; decide)]
  refine RSim.lstep (K := ssK7) (by rw [ssK7]) ?_
  rintro ⟨r6, m6⟩ h6
  obtain ⟨hS6, hg6, hsp6⟩ := SPL.cons h6 hS5 hsp (hsl.grow hg25)
  rw [ssK7_some]
  exact RSim.pure_some ⟨⟨hS6, (hg.trans hg25).trans hg6, rfl, hsp6⟩, hO.1 _ _ (consW_afr h6) hJ5⟩

/-- The twin's `classReadSlots` after the slot. -/
def slotsNext (bs : BlockShape) (fe : IFEnv) (np k : Nat) (motPos : List Nat) (d : Nat)
    (dom body : EIdx) (slot : ClassSlot) : AM (Option (List ClassSlot)) :=
  slotsRest bs fe np k (match slot with
    | .motive _ => motPos ++ [d - np]
    | .minor _ _ _ => motPos) d dom body slot

theorem slots_sims (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (p np : Word)
    (bs : BlockShape) (N : Nat) :
    (∀ (m : Mem) (a : AState) (n mo ml d e : Word) (motPos : List Nat),
      StageR dn vis fe m a → J m → H e → BSOK m p.toNat bs → decNL m mo.toNat ml.toNat = some motPos →
      mo.toNat + ml.toNat ≤ iwTop m → d.toNat + n.toNat < 2 ^ 64 →
      RSim (slotsW cR N m p vis np n mo ml d e)
        (ConRon.Arena.classReadSlots bs fe np.toNat n.toNat motPos d.toNat (decI e)) a
        (fun b a' x => KP dn vis fe m decSlots b a' x ∧ J b.2)) ∧
    (∀ (m : Mem) (a : AState) (n mo ml d dom body slotw : Word) (motPos : List Nat) (k : Nat)
      (slot : ClassSlot),
      StageR dn vis fe m a → J m → H dom → H body → BSOK m p.toNat bs →
      decNL m mo.toNat ml.toNat = some motPos → mo.toNat + ml.toNat ≤ iwTop m →
      n.toNat = k + 1 → d.toNat + n.toNat < 2 ^ 64 → StabD (fun m => decCS m slotw.toNat) m slot →
      RSim (nextW cR N m p vis np n mo ml d dom body slotw)
        (slotsNext bs fe np.toNat k motPos d.toNat (decI dom) (decI body) slot) a
        (fun b a' x => KP dn vis fe m decSlots b a' x ∧ J b.2)) := by
  induction N with
  | zero =>
    exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => RSim.of_none (by rw [slotsW]),
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => RSim.of_none (by rw [nextW])⟩
  | succ N ih =>
  obtain ⟨ih1, ih2⟩ := ih
  refine ⟨fun m a n mo ml d e motPos hS hJ hH hb hmot hmt hd => ?_,
    fun m a n mo ml d dom body slotw motPos k slot hS hJ hdomH hbodyH hb hmot hmt hk hd hsl => ?_⟩
  · by_cases hn : n = 0
    · rw [slotsW_zero (h := hn)]
      have hz : n.toNat = 0 := by rw [hn]; rfl
      rw [hz]
      exact RSim.pure_some ⟨⟨hS, IWGrow.refl m, rfl, SPL.nil 0 (Nat.zero_le _)⟩, hJ⟩
    obtain ⟨k, hk⟩ : ∃ k, n.toNat = k + 1 :=
      ⟨n.toNat - 1, by have : n.toNat ≠ 0 := fun e => hn (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
    rw [hk, ConRon.Arena.classReadSlots]
    by_cases hg : e >>> 28 ≠ 6
    · rw [slotsW_tag (h := hn) (h2 := hg)]
      have ht : ¬ (((decI e : EIdx)).tag == ETag.forallE) = true :=
        fun h => hg ((tag_beq _ hH _ 6 (by decide) rfl).mp h)
      rw [ite_eq_right ht]
      exact RSim.pure_some ⟨⟨hS, IWGrow.refl m, rfl⟩, hJ⟩
    by_cases hne : eViewW m e = []
    · rw [slotsW_nil (h := hn) (h2 := hg) (h3 := hne)]; exact RSim.none
    rw [slotsW_ok (h := hn) (h2 := hg) (h3 := hne)]
    have hg6 : e >>> 28 = 6 := by simpa using hg
    have ht : (((decI e : EIdx)).tag == ETag.forallE) = true := (tag_beq _ hH _ 6 (by decide) rfl).mpr hg6
    rw [ite_eq_left ht]
    obtain ⟨hvb, hdomH, hbodyH⟩ := viewBindW hS.1.arena.1 hH hne hg6
    refine RSim.tstep hvb ?_
    refine RSim.bind (K := ssK1 cR N p vis np n mo ml d ((eViewW m e).tail.headD 0)
      ((eViewW m e).tail.tail.headD 0)) (by rw [ssK1])
      (slotW_sim dn vis fe cR J hO N m a p np mo ml d ((eViewW m e).tail.headD 0) bs motPos hS hJ hdomH hb
        hmot hmt) ?_
    rintro ⟨r1, m1⟩ o a1 - ⟨⟨hS1, hg1, hd1⟩, hJ1⟩
    dsimp only at hS1 hg1 hd1 hJ1
    rcases o with _ | slot
    · rw [ssK1_fail (h := hd1)]; exact RSim.pure_some ⟨⟨hS1, hg1, rfl⟩, hJ1⟩
    obtain ⟨h11, hsl⟩ := hd1
    rw [ssK1_ok (h := by rw [h11]; decide)]
    refine RSim.bindPure (K := ssK1b) (by rw [ssK1b])
      (ih2 m1 a1 n mo ml d _ _ _ motPos k slot hS1 hJ1 hdomH hbodyH (hb.grow hg1)
        (by rw [decNL_grow hg1 hmt]; exact hmot) (Nat.le_trans hmt hg1.1) hk hd hsl) ?_
    rintro ⟨r2, m2⟩ x a2 - ⟨⟨hS2, hg2, hd2⟩, hJ2⟩
    rw [ssK1b_some]
    refine RSim.pure_some ⟨⟨hS2, hg1.trans hg2, ?_⟩, hJ2⟩
    cases x <;> exact hd2
  · have htag := decCS_tag hsl.get
    have hsz := hS.2.2.2.1
    have hrd := iwN_rdW htag (by have := iwN_lt htag; omega)
    rw [UInt64.ofNat_toNat] at hrd
    cases slot with
    | motive key =>
      rw [nextW_mot (h := by rw [hrd.1]; rfl)]
      refine RSim.lstep (K := ssK2 cR N p vis np n d dom body slotw) (by rw [ssK2]) ?_
      rintro ⟨r2, m2⟩ h2
      obtain ⟨hS2, hg2, hdn2, htop2⟩ := motSnocW_stage h2 hS hmt hmot
      rw [ssK2_some]
      exact slotsRest_sim dn vis fe cR J hO p np bs N ih1 m m2 a n d _ _ _ _ _ k
        (motPos ++ [d.toNat - np.toNat]) (.motive key) hS2 (hO.1 _ _ (motSnocW_afr h2) hJ) hg2 hdomH hbodyH
        (hb.grow hg2) hdn2 (by omega) hk hd (hsl.grow hg2)
    | minor c cn ihs =>
      rw [nextW_min (h := by rw [hrd.1]; simp [ClassSlot.isMinor])]
      exact slotsRest_sim dn vis fe cR J hO p np bs N ih1 m m a n d _ _ _ mo ml k motPos
        (.minor c cn ihs) hS hJ (IWGrow.refl m) hdomH hbodyH hb hmot hmt hk hd hsl

end L.Ind
