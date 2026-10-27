import ConAgua.Arena.IndPartsSpec9
import ConAgua.Arena.IndPartsSpec5

/-!
# Refinements of `IndParts`, part 10 (lane `indproofs2`, helper `parts`): the recursor name set

`blockRecNameSetOk`: `block_rec_want` (`name_rec` per member, in order), `block_rec_got` (the
recursors' names), `sl_set_eq` (with `sl_all_in`, library functions without a model before).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `sl_all_in`, `sl_set_eq` -/

/-- **`sl_all_in` is its model `allInW`** (generated). -/
l_model slAllIn_spec (p : Prog) (hc : p.lookup "sl_contains" = some slContains)
    (hp : p.lookup "sl_all_in" = some slAllIn)
  fns [hp ↦ allInW ro]
  specs [slContains_spec p hc n]
  grind [arena_grind]

theorem allInW_ok (n : Nat) : ∀ (m : Mem) (o1 l1 o2 l2 r : Word) (ws1 ws2 : List Word),
    SlR m o1 l1 ws1 → SlR m o2 l2 ws2 → allInW n m o1 l1 o2 l2 = some r →
    r = if ws1.all (fun w => ws2.contains w) then 1 else 0 := by
  induction n with
  | zero => intro m o1 l1 o2 l2 r ws1 ws2 _ _ h; simp [allInW] at h
  | succ n ih =>
    intro m o1 l1 o2 l2 r ws1 ws2 h1 h2 h
    cases h1 with
    | nil => rw [allInW.arm1 n m _ 0 o2 l2 rfl] at h; simp at h; simp [h]
    | @cons _ _ ws hl hs =>
      rw [allInW.arm2 n m _ _ o2 l2 hl] at h
      obtain ⟨b, hb, h⟩ := ipK_inv1 h (by simp [allInW.k_sl_contains])
      have := containsW_ok n m o2 l2 _ b ws2 h2 hb
      by_cases b0 : b = 0
      · rw [allInW.k_sl_contains.arm1 _ _ _ _ _ _ _ b0] at h; simp at h; subst h
        subst b0
        split at this <;> simp_all
      · rw [allInW.k_sl_contains.arm2 _ _ _ _ _ _ _ b0] at h
        rw [ih _ _ _ _ _ _ _ _ hs h2 h]
        split at this <;> simp_all

/-- The model of `sl_set_eq`. -/
def setEqW (n : Nat) (m : Mem) (o1 l1 o2 l2 : Word) : Option Word :=
  if l1 ≠ l2 then some 0
  else match allInW n m o1 l1 o2 l2 with
    | none => none
    | some b => if b = 0 then some 0 else allInW n m o2 l2 o1 l1

theorem slSetEq_spec (p : Prog) (hc : p.lookup "sl_contains" = some slContains)
    (ha : p.lookup "sl_all_in" = some slAllIn) (hp : p.lookup "sl_set_eq" = some slSetEq) (n : Nat)
    (s₀ : St) (o1 l1 o2 l2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "sl_set_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ setEqW n s₀.mem o1 l1 o2 l2 = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, slSetEq]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, slAllIn_spec p hc ha n] <;>
    finish (gen := 20) [setEqW]

theorem setEqW_ok {n : Nat} {m : Mem} {o1 l1 o2 l2 r : Word} {ws1 ws2 : List Word}
    (h1 : SlR m o1 l1 ws1) (h2 : SlR m o2 l2 ws2) (h : setEqW n m o1 l1 o2 l2 = some r) :
    r = if (ws1.length == ws2.length && ws2.all (fun w => ws1.contains w) &&
      ws1.all (fun w => ws2.contains w)) then 1 else 0 := by
  have e1 := slR_length h1; have e2 := slR_length h2
  unfold setEqW at h
  by_cases hl : l1 ≠ l2
  · rw [ite_eq_left hl] at h; simp at h; subst h
    have : ws1.length ≠ ws2.length := fun e => hl (UInt64.toNat_inj.mp (by omega))
    simp [this]
  · rw [ite_eq_right hl] at h
    have hl' : l1 = l2 := by simpa using hl
    have hlen : ws1.length = ws2.length := by rw [e1, e2, hl']
    rcases ha : allInW n m o1 l1 o2 l2 with _ | b <;> rw [ha] at h
    · simp at h
    simp only at h
    have hb := allInW_ok n m o1 l1 o2 l2 b ws1 ws2 h1 h2 ha
    by_cases b0 : b = 0
    · rw [ite_eq_left b0] at h; simp at h; subst h
      subst b0
      split at hb <;> simp_all
    · rw [ite_eq_right b0] at h
      have hb2 := allInW_ok n m o2 l2 o1 l1 r ws2 ws1 h2 h1 h
      split at hb <;> simp_all

/-! ## `block_rec_want`, `block_rec_got` -/

mutual
/-- **The model of `block_rec_want`.** -/
def brwW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, mo, ml =>
    if ml = 0 then some ([0, 0], m)
    else brwK1 n mo ml (nrF m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) mo))])
/-- After `name_rec`. -/
def brwK1 (n : Nat) (mo ml : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => bggK3 n (r1.headD 0) (brwW n m1 (mo + 1) (ml - 1))
end

/-- **The model of `block_rec_got`.** -/
def brgW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, ro, rl =>
    if rl = 0 then some ([0, 0], m)
    else brgK n (rdW (m.arr64 IW) ro) (brgW n m (ro + 1) (rl - 1))
where
  /-- After the recursive call. -/
  brgK (n : Nat) (rc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) => bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) rc)) (r.headD 0) (r.tail.headD 0))

section arms
variable (n : Nat) (m m1 : Mem) (mo ml ro rl rc : Word) (r1 : List Word)
theorem brwW_nil (h : ml = 0) : brwW (n + 1) m mo ml = some ([0, 0], m) := by simp [brwW, h]
theorem brwW_cons (h : ml ≠ 0) : brwW (n + 1) m mo ml = brwK1 n mo ml
    (nrF m [rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) mo))]) := by
  simp [brwW, h]
theorem brwK1_some : brwK1 n mo ml (some (r1, m1)) = bggK3 n (r1.headD 0) (brwW n m1 (mo + 1) (ml - 1)) := by
  simp [brwK1]
theorem brgW_nil (h : rl = 0) : brgW (n + 1) m ro rl = some ([0, 0], m) := by simp [brgW, h]
theorem brgW_cons (h : rl ≠ 0) : brgW (n + 1) m ro rl =
    brgW.brgK n (rdW (m.arr64 IW) ro) (brgW n m (ro + 1) (rl - 1)) := by simp [brgW, h]
theorem brgK_some : brgW.brgK n rc (some (r1, m1)) =
    bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) rc)) (r1.headD 0) (r1.tail.headD 0)) := rfl
end arms
attribute [ind_grind] brwW_nil brwW_cons brwK1_some brgW_nil brgW_cons brgK_some

section spec
variable (p : Prog) (hP : IndPartsProg p)
include hP

theorem brw_spec (hp : p.lookup "block_rec_want" = some blockRecWant) (n : Nat) :
    ∀ (s₀ : St) (mo ml : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_want" [mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ brwW n s₀.mem mo ml = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ mo ml; rw [invoke_eq _ hp]; simp only [callFn, blockRecWant]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ mo ml
    rw [invoke_eq _ hp]
    simp only [callFn, blockRecWant]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nrF_spec p hP.nr n,
        slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem brg_spec (hp : p.lookup "block_rec_got" = some blockRecGot) (n : Nat) :
    ∀ (s₀ : St) (ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_got" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ brgW n s₀.mem ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ ro rl; rw [invoke_eq _ hp]; simp only [callFn, blockRecGot]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ro rl
    rw [invoke_eq _ hp]
    simp only [callFn, blockRecGot]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

/-- A pointer slice's head and tail, below the tops. -/
theorem partsPSl_cons {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) (hl : l ≠ 0) :
    ∃ p x xs', xs = x :: xs' ∧ rdW (m.arr64 IW) o = UInt64.ofNat p ∧ p < 2 ^ 64 ∧
      DecB (fun m => f m p) m x ∧ PSlR f xs' (o + 1) (l - 1) m := by
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 :=
    ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hd := h.1; simp only [DecB, hL] at hd
  obtain ⟨p, x, xs', rfl, hp, hx, hxs'⟩ := decPL_cons hd
  obtain ⟨hw, hpb, holt⟩ := partsIwRd hp rfl
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨p, x, xs', rfl, hw, hpb, hx, ⟨?_, ?_⟩⟩
  · show decPL _ _ _ _ = _; rw [ho1, partsPred_of hL]; exact hxs'
  · rw [ho1, partsPred_of hL]; have := h.2; omega

theorem partsPSl_nil {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o : Word} {m : Mem}
    (h : PSlR f xs o 0 m) : xs = [] := by
  have := decPL_length _ h.1; simpa using this

/-- A constant decoded below the tops: its name word, in any memory grown into. -/
theorem partsCVName {m m' : Mem} (hg : IWGrow m m') {q : Nat} {cv : IConstantVal}
    (h : DecB (fun m => decCVp m q) m cv) (hq : q < 2 ^ 64) :
    (rdW (m'.arr64 EREC) (UInt64.ofNat q)).toNat < 2 ^ 32 ∧
      decI (rdW (m'.arr64 EREC) (UInt64.ofNat q)) = cv.name :=
  decCVp_name_p (h.stab (OMono.decCVp _) m' hg) hq

/-- **`block_rec_got`'s model**: the recursors' names. -/
theorem brgW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (ro rl : Word) (recs : List RecShape) (r : List Word),
    brgW n m ro rl = some (r, m') → StageR dn vis fe m a → PSlR decRS recs ro rl m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (recs.map (·.cvR.name)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a ro rl recs r h; simp [brgW] at h
  | succ n ih =>
    intro m m' a ro rl recs r h hS hrs
    by_cases hl : rl = 0
    · rw [brgW_nil n m ro rl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hrs]
      exact ⟨hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
    rw [brgW_cons n m ro rl hl] at h
    obtain ⟨pc, rs0, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hl
    rw [hw] at h
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [brgW.brgK])
    rw [brgK_some] at h
    obtain ⟨hS1, hg1, hd1, hb1⟩ := ih m m1 a (ro + 1) (rl - 1) rs' r1 h1 hS hrs'
    obtain ⟨⟨ca, hca, hcv⟩, -⟩ := decRS_some (show decRS (truncM m) pc = some rs0 from hrs0)
    obtain ⟨hcw, hcab, -⟩ := partsIwRd hca (UInt64.toNat_ofNat_of_lt' hpb)
    have hpclt : pc < iwTop m := partsIwLt hca
    rw [partsRdIW_grow hg1 (by rw [UInt64.toNat_ofNat_of_lt' hpb]; exact hpclt), hcw] at h
    obtain ⟨hnl, hne⟩ := partsCVName hg1 (show DecB (fun m => decCVp m ca) m rs0.cvR from hcv) hcab
    rcases h2 : consW n m1 (rdW (m1.arr64 EREC) (UInt64.ofNat ca)) (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [bgoK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hd2, ht2⟩ := consW_stage h2 hS1 hb1 hnl hd1
    refine ⟨hS2, hg1.trans hg2, ?_, by simp only [List.headD_cons, List.tail_cons]; omega⟩
    simp only [List.headD_cons, List.tail_cons, List.map_cons]
    rw [← hne]; exact hd2

/-- **`block_rec_want`'s model refines the twin's `mapM` of `name_rec`.** -/
theorem brwW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml : Word) (ms : List MemberShape),
    StageR dn vis fe m a →
    DecB (fun m => decPL m (decMS m) mo.toNat ml.toNat) m ms ∧ (ml = 0 ∨ mo.toNat + ml.toNat ≤ iwTop m) →
    Sim (brwW n m mo ml) (ms.mapM fun ms => internNNode (.str ms.cvT.name "rec")) a
      (fun r xs m' a' => decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  induction n with
  | zero => intro m a mo ml ms _ _ r m' e; simp [brwW] at e
  | succ n ih =>
    intro m a mo ml ms hS hms
    by_cases hl : ml = 0
    · rw [brwW_nil n m mo ml hl]
      have : ms = [] := by
        have := decPL_length _ (show decPL _ _ _ _ = _ from hms.1); subst hl; simpa using this
      subst this
      exact Sim.ret ⟨by simp [decHL, hslice?], by simp, hS, IWGrow.refl _⟩
    rw [brwW_cons n m mo ml hl]
    obtain ⟨pc, ms0, ms', rfl, hw, hpb, hms0, hms'⟩ := partsPSl_cons ⟨hms.1, hms.2.resolve_left hl⟩ hl
    obtain ⟨⟨ca, hca, hcv⟩, -⟩ := decMS_some (show decMS (truncM m) pc = some ms0 from hms0)
    obtain ⟨hcw, hcab, -⟩ := partsIwRd hca (UInt64.toNat_ofNat_of_lt' hpb)
    rw [hw, hcw]
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) (show DecB (fun m => decCVp m ca) m ms0.cvT from hcv) hcab
    rw [List.mapM_cons]
    have h1 := partsSimW (nrF_ok dn vis fe _ hnl) hS
    rw [hne] at h1
    refine Sim.bindK (by simp [brwK1]) (fun _ _ => by rw [brwK1]) h1 ?_
    rintro r1 x1 m1 a1 ⟨hS1, hg1, hx1l, hx1⟩
    refine Sim.bindK (by simp [bggK3]) (fun _ _ => by rw [bggK3]) (ih m1 a1 (mo + 1) (ml - 1) ms' hS1 ⟨(hms'.grow decMS_mono hg1).1, Or.inr (hms'.grow decMS_mono hg1).2⟩) ?_
    rintro r2 xs m2 a2 ⟨hd2, hb2, hS2, hg2⟩
    intro r m' e
    rcases h3 : consW n m2 (r1.headD 0) (r2.headD 0) (r2.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at e
    · cases e
    rw [bgoK3_some] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 hb2 hx1l hd2
    refine ⟨x1 :: xs, a2, rfl, ?_, by simp only [List.headD_cons, List.tail_cons]; omega, hS3,
      (hg1.trans hg2).trans hg3⟩
    simp only [List.headD_cons, List.tail_cons]; rw [← hx1]; exact hd3

/-! ## `block_rec_name_set_ok` -/

theorem partsContains_decI (ws : List Word) (x : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) : (ws.map (decI : Word → NIdx)).contains (decI x) = ws.contains x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.contains_cons]
    rw [ih (fun w' h' => hws w' (List.mem_cons_of_mem _ h')),
      L.Arena.decI_beq x w hx (hws w (List.mem_cons_self ..))]
    by_cases h : x = w <;> simp [h]

theorem partsAll_decI (ws vs : List Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hvs : ∀ w ∈ vs, w.toNat < 2 ^ 32) :
    (ws.map (decI : Word → NIdx)).all (fun n => (vs.map (decI : Word → NIdx)).contains n) =
      ws.all (fun w => vs.contains w) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.all_cons]
    rw [ih (fun w' h' => hws w' (List.mem_cons_of_mem _ h')),
      partsContains_decI vs w hvs (hws w (List.mem_cons_self ..))]

/-- **The model of `block_rec_name_set_ok`** (at exec fuel `n + 2`). -/
def brnW (n : Nat) (m : Mem) (mo ml ro rl : Word) : Option (List Word × Mem) :=
  match brwW (n + 1) m mo ml with
  | none => none
  | some (r1, m1) =>
    match brgW (n + 1) m1 ro rl with
    | none => none
    | some (r2, m2) =>
      match setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with
      | none => none
      | some b => some ([b], m2)

theorem brn_spec (p : Prog) (hP : IndPartsProg p) (hw : p.lookup "block_rec_want" = some blockRecWant)
    (hg : p.lookup "block_rec_got" = some blockRecGot) (hc : p.lookup "sl_contains" = some slContains)
    (ha : p.lookup "sl_all_in" = some slAllIn) (hs : p.lookup "sl_set_eq" = some slSetEq)
    (hp : p.lookup "block_rec_name_set_ok" = some blockRecNameSetOk) (n : Nat) (s₀ : St)
    (mo ml ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "block_rec_name_set_ok" [mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ brnW n s₀.mem mo ml ro rl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockRecNameSetOk]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, brw_spec p hP hw (n + 1),
      brg_spec p hP hg (n + 1), slSetEq_spec p hc ha hs n] <;>
    finish (gen := 20) [brnW]

/-- The program bundle of the name set. -/
structure IndPartsProg3 (p : Prog) : Prop extends IndPartsProg2 p where
  want : p.lookup "block_rec_want" = some blockRecWant
  got : p.lookup "block_rec_got" = some blockRecGot
  contains : p.lookup "sl_contains" = some slContains
  allIn : p.lookup "sl_all_in" = some slAllIn
  setEq : p.lookup "sl_set_eq" = some slSetEq
  nameSet : p.lookup "block_rec_name_set_ok" = some blockRecNameSetOk

/-- **`block_rec_name_set_ok` refines `blockRecNameSetOk`** (through the stub `name_rec`): the
members and recursors slices of records decoded below the tops (the members' below the top unless
empty: an empty slice's offset is whatever its record holds). -/
@[refines ConRon.Arena.blockRecNameSetOk]
theorem blockRecNameSetOk_refines (p : Prog) (hP : IndPartsProg3 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mo ml ro rl : Word)
    (ms : List MemberShape) (recs : List RecShape) (hS : StageR dn vis fe s₀.mem a₀)
    (hms : DecB (fun m => decPL m (decMS m) mo.toNat ml.toNat) s₀.mem ms ∧
      (ml = 0 ∨ mo.toNat + ml.toNat ≤ iwTop s₀.mem))
    (hrs : PSlR decRS recs ro rl s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "block_rec_name_set_ok" [mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.blockRecNameSetOk ms recs) a₀ ∧
      r = [if AM.res (ConRon.Arena.blockRecNameSetOk ms recs) a₀ then 1 else 0] ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.blockRecNameSetOk ms recs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (brn_spec p hP.toIndPartsProg hP.want hP.got hP.contains hP.allIn hP.setEq hP.nameSet
    n s₀ mo ml ro rl) ?_
  rintro r s' ⟨hl, hm⟩
  have hsim : Sim (brnW n s₀.mem mo ml ro rl) (ConRon.Arena.blockRecNameSetOk ms recs) a₀
      (fun r b m' a' => r = [if b then 1 else 0] ∧ StageR dn vis fe m' a' ∧ IWGrow s₀.mem m') := by
    unfold brnW ConRon.Arena.blockRecNameSetOk
    refine Sim.bindK (K := fun x => match x with
      | none => none
      | some (r1, m1) =>
        match brgW (n + 1) m1 ro rl with
        | none => none
        | some (r2, m2) =>
          match setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with
          | none => none
          | some b => some ([b], m2))
      (body := fun r1 m1 => match brgW (n + 1) m1 ro rl with
        | none => none
        | some (r2, m2) =>
          match setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with
          | none => none
          | some b => some ([b], m2)) rfl (fun _ _ => rfl) (brwW_sim (n + 1) _ a₀ mo ml ms hS hms) ?_
    rintro r1 want m1 a1 ⟨hd1, hb1, hS1, hg1⟩
    intro r m' e
    rcases h2 : brgW (n + 1) m1 ro rl with _ | ⟨r2, m2⟩ <;> rw [h2] at e
    · cases e
    simp only at e
    obtain ⟨hS2, hg2, hd2, hb2⟩ := brgW_ok (n + 1) m1 m2 a1 ro rl recs r2 h2 hS1 (hrs.grow decRS_mono hg1)
    rcases h3 : setEqW n m2 (r2.headD 0) (r2.tail.headD 0) (r1.headD 0) (r1.tail.headD 0) with _ | b <;> rw [h3] at e
    · cases e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    have hT : iwTop m2 < 2 ^ 64 := (rdW (m2.arr64 CTL) 200).toNat_lt
    have hd1' : decHL m2 (r1.headD 0).toNat (r1.tail.headD 0).toNat = some want := by
      rw [decHL_grow3 hg2 hb1]; exact hd1
    obtain ⟨gws, hgs, hgm, hgl⟩ := slR_of_decHL m2 _ _ _ hd2 (by omega)
    obtain ⟨wws, hws, hwm, hwl⟩ := slR_of_decHL m2 _ _ _ hd1' (by have := hg2.1; omega)
    rw [ofNat_toNat_word, ofNat_toNat_word] at hgs hws
    have hb := setEqW_ok hgs hws h3
    refine ⟨_, a1, rfl, ?_, hS2, hg1.trans hg2⟩
    rw [hb, hgm, hwm, partsAll_decI wws gws hwl hgl, partsAll_decI gws wws hgl hwl]
    simp only [List.length_map]
  obtain ⟨hok, hr, hS', hg⟩ := Sim.run hsim hm
  exact ⟨hl, hok, hr, hS', hg⟩

end L.Ind
