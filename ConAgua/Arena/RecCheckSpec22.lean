import ConAgua.Arena.RecCheckSpec21
import ConAgua.Arena.IndInstallSpec20
import ConAgua.Arena.IndInstallSpec9

/-!
# `RecCheck`: `targetRecPins`' name pins (lane `indproofs3`, helper `rec2`)

`ptr_list_names` under the stage relation at any slice decoded below the tops (an empty slice's
offset is whatever its record holds), and `target_rec_pins_names`: the auxiliary names wanted
(`n₀.rec_1 …`) against the ones the stream has, as sets, and no two recursors sharing a name.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The lookups -/

/-- The program bundle of `target_rec_pins` and its callees. -/
structure RpLook (p : Prog) : Prop extends IndPartsProg3 p where
  erCopy : p.lookup "er_copy" = some erCopy
  rna : NaF p
  erToIw : p.lookup "er_to_iw" = some erToIw
  slEq : p.lookup "sl_eq" = some slEq
  lpsOne : p.lookup "block_rec_lps_one" = some blockRecLpsOne
  lpsGo : p.lookup "block_rec_lps_ok_go" = some blockRecLpsOkGo
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  lpsOk : p.lookup "block_rec_lps_ok" = some blockRecLpsOk
  unres : p.lookup "block_rec_names_unreserved" = some blockRecNamesUnreserved
  rrn : RrnF p
  soa : p.lookup "block_rec_split_own_aux" = some blockRecSplitOwnAux
  wan : p.lookup "block_rec_want_aux_names" = some blockRecWantAuxNames
  nri : NriF p
  pnc : p.lookup "ptr_names_copy" = some ptrNamesCopy
  pln : p.lookup "ptr_list_names" = some ptrListNames
  nodup : p.lookup "sl_nodup" = some slNodup
  nco : p.lookup "num_ctors_of" = some numCtorsOf
  acc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy
  acg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo
  ac : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors
  names : p.lookup "target_rec_pins_names" = some targetRecPinsNames
  psplit : p.lookup "target_rec_pins_split" = some targetRecPinsSplit
  pins : p.lookup "target_rec_pins" = some targetRecPins

/-! ## `ptr_list_names` under the stage relation -/

theorem nameCopyW_src0 (n : Nat) (m : Mem) (d s : Word) : nameCopyW n m d s 0 = nameCopyW n m d 0 0 := by
  cases n <;> simp [nameCopyW]

theorem ptrNamesW_src0 {n : Nat} {m : Mem} {o l : Word} (hl : l = 0) : ptrNamesW n m o l = ptrNamesW n m 0 l := by
  subst hl; simp only [ptrNamesW, nameCopyW_src0]

theorem ptrNamesW_room {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : ptrNamesW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (rdW (m.arr64 CTL) 200).toNat + l.toNat ≤ (m.arr64 IW).size := by
  simp only [ptrNamesW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
    obtain ⟨q, m1⟩ := qm
    obtain ⟨hq, -, hroom⟩ := allocW_facts hal hsz
    rw [← hq]; exact hroom

/-- **`ptr_list_names` under the stage relation**: the names of a slice of records decoded below
the tops whose word `0` is a constant pointer. -/
theorem plnW_stage {α : Type} {f : Mem → Nat → Option α} (cvOf : α → IConstantVal)
    (hf : ∀ q, OMono (fun m => f m q))
    (hcv : ∀ m pp x, f m pp = some x → ∃ a, iwN m pp = some a ∧ decCVp m a = some (cvOf x))
    (hfb : ∀ m pp x, f (truncM m) pp = some x → pp < iwTop m)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (h : ptrNamesW n m o l = some (r, m')) (hS : StageR dn vis fe m a) (hx : PSlR0 f xs o l m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200, l] ∧
      decHL m' (rdW (m.arr64 CTL) 200).toNat l.toNat = some (xs.map fun x => (cvOf x).name) ∧
      (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' := by
  obtain ⟨-, -, hsz, -, hc⟩ := hS.2
  have hroom := ptrNamesW_room h hsz
  have hlen : xs.length = l.toNat := decPL_length _ hx.1
  by_cases hl : l = 0
  · have hxs := hx.nil hl
    subst hxs
    rw [ptrNamesW_src0 hl] at h
    obtain ⟨hr, hd, hg, hfr, ht⟩ := ptrNamesW_dec [] h hsz hc (by simp [hl]) (by simp [hl])
      (fun j hj => absurd hj (by simp))
    exact ⟨stage_frame_iw hS hfr (by rw [← ht]; exact hroom), hg, hr, by simpa using hd, ht⟩
  · have hP := hx.pslr hl
    obtain ⟨-, hel⟩ := pos2_decPL_trunc hx.1
    obtain ⟨hr, hd, hg, hfr, ht⟩ := ptrNamesW_dec (xs.map cvOf) h hsz hc (by simp [hlen]) hP.2
      (fun j hj => by
        have hj' : j < xs.length := by simpa using hj
        obtain ⟨v, -, hv, hj2, hfv⟩ := hel j (by omega)
        have hvt : v < iwTop m := hfb m v _ hfv
        have hfm : f m v = some xs[j] := (show DecB (fun m => f m v) m xs[j] from hfv).get (hf v)
        obtain ⟨a, ha, hca⟩ := hcv m v _ hfm
        exact ⟨v, a, hv, hvt, ha, by simpa using hca⟩)
    exact ⟨stage_frame_iw hS hfr (by rw [← ht]; exact hroom), hg, hr, by simpa [List.map_map, Function.comp_def] using hd, ht⟩

theorem decRS_cv (m : Mem) (pp : Nat) (x : RecShape) (h : decRS m pp = some x) :
    ∃ a, iwN m pp = some a ∧ decCVp m a = some x.cvR := (decRS_some h).1

theorem decRS_lt (m : Mem) (pp : Nat) (x : RecShape) (h : decRS (truncM m) pp = some x) : pp < iwTop m := by
  obtain ⟨⟨a, ha, -⟩, -⟩ := decRS_some h; exact partsIwLt ha

/-! ## Guards: the L code aborts where the twin fails -/

/-! ## The twin's name pins, as one test -/

/-- `n₀`: member 0's name, `.anonymous` (interned) at no member. -/
def rpN0 (p : BlockShape) : AM NIdx :=
  match p.members with
  | [] => internNNode .anonymous
  | ms :: _ => pure ms.cvT.name

/-- The auxiliary recursors. -/
def rpAux (p : BlockShape) : List RecShape := p.recs.filter fun rc => !(rc.tgt < p.k)

/-- The set test of the auxiliary names. -/
def rpSetOk (gotAux wantAux : List NIdx) : Bool :=
  gotAux.length == wantAux.length && wantAux.all (gotAux.contains ·) && gotAux.all (wantAux.contains ·)

/-- **The twin's name pins** (`targetRecPins` between the member name set and the split): the
auxiliary names as a set, then no two recursors sharing a name. -/
def namesTwin (p : BlockShape) : AM Bool := do
  let n₀ ← rpN0 p
  let wantAux ← (List.range (rpAux p).length).mapM fun i => internNNode (.str n₀ s!"rec_{i + 1}")
  if rpSetOk ((rpAux p).map (·.cvR.name)) wantAux then pure (nameNodup (p.recs.map (·.cvR.name)))
  else pure false

/-! ## `target_rec_pins_names` -/

def tpnK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def tpnK4 (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rn, m) => tpnK5 (callW p n "sl_nodup" [rn.headD 0, rn.tail.headD 0] m)
def tpnK3 (p : Prog) (n : Nat) (reco recl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ro, m) => if ro.headD 0 = 0 then some ([0], m)
    else tpnK4 p n (callW p n "ptr_list_names" [reco, recl] m)
def tpnK2 (p : Prog) (n : Nat) (reco recl : Word) (rw : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rg, m) => tpnK3 p n reco recl
      (callW p n "sl_set_eq" [rw.headD 0, rw.tail.headD 0, rg.headD 0, rg.tail.headD 0] m)
def tpnK1 (p : Prog) (n : Nat) (reco recl auxo auxl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rw, m) => tpnK2 p n reco recl rw (callW p n "ptr_list_names" [auxo, auxl] m)
/-- From `n₀` on. -/
def tpnB (p : Prog) (n : Nat) (reco recl auxo auxl n0 : Word) (m : Mem) : Option (List Word × Mem) :=
  tpnK1 p n reco recl auxo auxl (callW p n "block_rec_want_aux_names" [n0, 0, auxl] m)
def tpnK0 (p : Prog) (n : Nat) (reco recl auxo auxl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tpnB p n reco recl auxo auxl (r.headD 0) m

/-- **The model of `target_rec_pins_names`** (body fuel `n`). -/
def tpnW (p : Prog) (n : Nat) (m : Mem) (mo k reco recl auxo auxl : Word) : Option (List Word × Mem) :=
  if k = 0 then tpnK0 p n reco recl auxo auxl (callW p n "intern_nanon" [] m)
  else tpnB p n reco recl auxo auxl (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) mo))) m

section arms
variable (p : Prog) (n : Nat) (m : Mem) (reco recl auxo auxl : Word) (r rw : List Word)
theorem tpnK5_some : tpnK5 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem tpnK4_some : tpnK4 p n (some (r, m)) = tpnK5 (callW p n "sl_nodup" [r.headD 0, r.tail.headD 0] m) := rfl
theorem tpnK3_zero (h : r.headD 0 = 0) : tpnK3 p n reco recl (some (r, m)) = some ([0], m) := by
  simp only [tpnK3]; rw [ite_eq_left h]
theorem tpnK3_ok (h : ¬ r.headD 0 = 0) : tpnK3 p n reco recl (some (r, m)) =
    tpnK4 p n (callW p n "ptr_list_names" [reco, recl] m) := by simp only [tpnK3]; rw [ite_eq_right h]
theorem tpnK2_some : tpnK2 p n reco recl rw (some (r, m)) = tpnK3 p n reco recl
    (callW p n "sl_set_eq" [rw.headD 0, rw.tail.headD 0, r.headD 0, r.tail.headD 0] m) := rfl
theorem tpnK1_some : tpnK1 p n reco recl auxo auxl (some (r, m)) =
    tpnK2 p n reco recl r (callW p n "ptr_list_names" [auxo, auxl] m) := rfl
theorem tpnK0_some : tpnK0 p n reco recl auxo auxl (some (r, m)) = tpnB p n reco recl auxo auxl (r.headD 0) m := rfl
end arms
attribute [ind_grind] tpnK5_some tpnK4_some tpnK3_zero tpnK3_ok tpnK2_some tpnK1_some tpnK0_some

set_option maxHeartbeats 1600000 in
theorem tpn_spec (p : Prog) (hp : p.lookup "target_rec_pins_names" = some targetRecPinsNames) (n : Nat)
    (s₀ : St) (mo k reco recl auxo auxl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_rec_pins_names" [mo, k, reco, recl, auxo, auxl]
    ⦃fun r s' => LocEq s' s₀ ∧ tpnW p n s₀.mem mo k reco recl auxo auxl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetRecPinsNames]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "intern_nanon", callW_spec p n "block_rec_want_aux_names",
      callW_spec p n "ptr_list_names", callW_spec p n "sl_set_eq", callW_spec p n "sl_nodup"] <;>
    finish (gen := 40) (instances := 20000) [tpnW, tpnB, rdW_eq]

/-- From `n₀` on: the wanted names, the stream's, the set test, the duplicate test. -/
theorem tpnB_sim (p : Prog) (L : RpLook p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (bs : BlockShape) (reco recl auxo auxl n0 : Word) (x : NIdx) (hn0 : H n0)
    (hx : decI n0 = x) :
    ∀ (m : Mem) (a : AState), StageR dn vis fe m a → PSlR0 decRS bs.recs reco recl m →
    PSlR decRS (rpAux bs) auxo auxl m →
    Sim (tpnB p (n + 1) reco recl auxo auxl n0 m)
      (do
        let wantAux ← (List.range (rpAux bs).length).mapM fun i => internNNode (.str x s!"rec_{i + 1}")
        if rpSetOk ((rpAux bs).map (·.cvR.name)) wantAux then pure (nameNodup (bs.recs.map (·.cvR.name)))
        else pure false)
      a (fun r b m' a' => r.headD 0 = (if b then 1 else 0) ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro m a hS hrs haux
  have hl : auxl.toNat = (rpAux bs).length := (decPL_length _ haux.1).symm
  have hT : ∀ m : Mem, iwTop m < 2 ^ 64 := fun m => (rdW (m.arr64 CTL) 200).toNat_lt
  have hwant : Sim (callW p (n + 1) "block_rec_want_aux_names" [n0, 0, auxl] m)
      ((List.range (rpAux bs).length).mapM fun i => internNNode (.str x s!"rec_{i + 1}")) a
      (fun r xs m' a' => decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
    intro r m' e
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (wan_spec p L.toIndPartsProg L.nri L.wan (n + 1) _ n0 0 auxl) e
    have h := wanW_sim (dn := dn) (vis := vis) (fe := fe) (n + 1) m a n0 0 auxl hn0 hS
      (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact auxl.toNat_lt) r s'.mem hW
    have heq : wantAuxFrom (decI n0) (0 : Word).toNat auxl.toNat =
        (List.range (rpAux bs).length).mapM fun i => internNNode (.str x s!"rec_{i + 1}") := by
      unfold wantAuxFrom; rw [hx, hl]; simp only [UInt64.toNat_zero, Nat.zero_add]
    rw [heq] at h; exact h
  refine Sim.bindK (K := tpnK1 p (n + 1) reco recl auxo auxl) rfl (fun _ _ => rfl) hwant ?_
  rintro rw want m1 a1 ⟨hd1, hb1, hS1, hg1⟩
  refine Sim.mstep (K := tpnK2 p (n + 1) reco recl rw) rfl (fun _ _ => rfl) fun rg m2 h2 => ?_
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (ptrListNames_spec p L.alloc L.pnc L.pln (n + 1) _ auxo auxl) h2
  dsimp only at hW2
  have haux1 := haux.grow (fun q => decRS_mono q) hg1
  obtain ⟨hS2, hg2, hr2, hd2, ht2⟩ := plnW_stage (·.cvR) (fun q => decRS_mono q) decRS_cv decRS_lt hW2 hS1
    ⟨haux1.1, Or.inr haux1.2⟩
  subst hr2
  refine Sim.mstep (K := tpnK3 p (n + 1) reco recl) rfl (fun _ _ => rfl) fun ro m3 h3 => ?_
  obtain ⟨s3, rfl, -, hm3, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (slSetEq_spec p L.contains L.allIn L.setEq n _ _ _ _ _) h3
  simp only [List.headD_cons, List.tail_cons] at hW3 hm3
  rw [hm3]
  have hd1' : decHL s2.mem (rw.headD 0).toNat (rw.tail.headD 0).toNat = some want := by
    rw [decHL_grow3 hg2 hb1]; exact hd1
  obtain ⟨wws, hws, hwm, hwl⟩ := slR_of_decHL s2.mem _ _ _ hd1' (by have := hg2.1; have := hT s2.mem; omega)
  obtain ⟨gws, hgs, hgm, hgl⟩ := slR_of_decHL s2.mem _ _ _ hd2 (by rw [ht2]; exact hT _)
  rw [ofNat_toNat_word, ofNat_toNat_word] at hws hgs
  have hset := setEqW_ok hws hgs hW3
  have hcond : (wws.length == gws.length && gws.all (fun w => wws.contains w) &&
      wws.all (fun w => gws.contains w)) = rpSetOk ((rpAux bs).map (·.cvR.name)) want := by
    unfold rpSetOk
    rw [hgm, hwm, partsAll_decI wws gws hwl hgl, partsAll_decI gws wws hgl hwl, List.length_map,
      List.length_map]
    cases gws.all (fun w => wws.contains w) <;> cases wws.all (fun w => gws.contains w) <;>
      simp [Bool.and_comm, BEq.comm]
  by_cases hok : rpSetOk ((rpAux bs).map (·.cvR.name)) want = true
  · have hro : ro.headD 0 = 1 := by rw [hset, hcond, ite_eq_left hok]
    rw [tpnK3_ok _ _ _ _ _ _ (by rw [hro]; decide), ite_eq_left hok]
    refine Sim.mstep (K := tpnK4 p (n + 1)) rfl (fun _ _ => rfl) fun rn m4 h4 => ?_
    obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (ptrListNames_spec p L.alloc L.pnc L.pln (n + 1) _ reco recl) h4
    dsimp only at hW4
    have hrs2 := PSlR0.grow (fun q => decRS_mono q) hrs (hg1.trans hg2)
    obtain ⟨hS4, hg4, hr4, hd4, ht4⟩ := plnW_stage (·.cvR) (fun q => decRS_mono q) decRS_cv decRS_lt hW4 hS2 hrs2
    subst hr4
    refine Sim.mstep (K := tpnK5) rfl (fun _ _ => rfl) fun rd m5 h5 => ?_
    obtain ⟨s5, rfl, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
      (slNodup_spec p L.contains L.nodup (n + 1) _ _ _) h5
    simp only [List.headD_cons, List.tail_cons] at hW5 hm5
    obtain ⟨nws, hns, hnm, hnl⟩ := slR_of_decHL s4.mem _ _ _ hd4 (by rw [ht4]; exact hT _)
    rw [ofNat_toNat_word, ofNat_toNat_word] at hns
    have hnd := nodupW_ok _ _ _ _ _ _ hns hW5
    rw [tpnK5_some, hm5]
    refine Sim.ret ⟨?_, hS4, hg1.trans (hg2.trans hg4)⟩
    simp only [List.headD_cons]
    rw [hnd, hnm, nameNodup_map nws hnl]
    by_cases h : nws.Nodup <;> simp [h]
  · have hro : ro.headD 0 = 0 := by rw [hset, hcond, ite_eq_right hok]
    rw [tpnK3_zero _ _ _ _ _ _ hro, ite_eq_right hok]
    exact Sim.ret ⟨by simp, hS2, hg1.trans hg2⟩

/-- **`target_rec_pins_names`' model refines the twin's name pins** (through the stubs
`intern_nanon`, `name_rec_i`): the members' and recursors' slices of the shape and the auxiliary
recursors' slice decoded below the tops. -/
theorem tpnW_sim (p : Prog) (L : RpLook p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (m : Mem) (a : AState) (mo k reco recl auxo auxl : Word) (bs : BlockShape)
    (hS : StageR dn vis fe m a) (hms : PSlR0 decMS bs.members mo k m)
    (hrs : PSlR0 decRS bs.recs reco recl m) (haux : PSlR decRS (rpAux bs) auxo auxl m) :
    Sim (tpnW p (n + 1) m mo k reco recl auxo auxl) (namesTwin bs) a
      (fun r b m' a' => r.headD 0 = (if b then 1 else 0) ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  unfold tpnW namesTwin
  by_cases hk : k = 0
  · rw [ite_eq_left hk]
    have hm : bs.members = [] := hms.nil hk
    have h0 : rpN0 bs = internNNode .anonymous := by unfold rpN0; rw [hm]
    rw [h0]
    refine Sim.bindK (K := tpnK0 p (n + 1) reco recl auxo auxl) rfl (fun _ _ => rfl)
      (show Sim (callW p (n + 1) "intern_nanon" [] m) (internNNode .anonymous) a
        (fun r x m' a' => KeepPost dn vis fe decW0N m m' a' r x) from fun r m' e => by
        obtain ⟨s', rfl, -, hs⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (naF_spec p L.rna (n + 1) _ []) e
        exact naF_ok dn vis fe m s'.mem a r hs hS) ?_
    rintro r0 x0 m0 a0 ⟨hS0, hg0, hx0b, hx0⟩
    refine (tpnB_sim p L n bs reco recl auxo auxl (r0.headD 0) x0 hx0b hx0 m0 a0 hS0
      (hrs.grow (fun q => decRS_mono q) hg0) (haux.grow (fun q => decRS_mono q) hg0)).mono ?_
    rintro r b m' a' ⟨h1, h2, h3⟩
    exact ⟨h1, h2, hg0.trans h3⟩
  · rw [ite_eq_right hk]
    obtain ⟨pc, ms0, ms', hmeq, hw, hpb, hms0, -⟩ := partsPSl_cons (hms.pslr hk) hk
    obtain ⟨⟨ca, hca, hcv⟩, -⟩ := decMS_some (show decMS (truncM m) pc = some ms0 from hms0)
    obtain ⟨hcw, hcab, -⟩ := partsIwRd hca (UInt64.toNat_ofNat_of_lt' hpb)
    obtain ⟨hnl, hne⟩ := partsCVName (IWGrow.refl m) (show DecB (fun m => decCVp m ca) m ms0.cvT from hcv) hcab
    have h0 : rpN0 bs = pure ms0.cvT.name := by unfold rpN0; rw [hmeq]
    rw [h0, hw, hcw]
    refine Sim.bind_twin (x := ms0.cvT.name) rfl ?_
    exact tpnB_sim p L n bs reco recl auxo auxl _ _ hnl hne m a hS hrs haux

end L.Ind
