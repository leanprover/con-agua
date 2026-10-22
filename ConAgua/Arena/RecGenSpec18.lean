import ConAgua.Arena.RecGenSpec17

/-!
# `targetMajorOf` (lane `indproofs3`, helper `indproofs3-pos-cls`)

The major's head and arguments (the `get_app_fn`/`get_app_args` stubs), its `const` view, its
position among the members (`sl_find` over the members' names), then the member or the outside
branch.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

def tmfK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
def tmcK2 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) (r4 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 ≠ 0 then
      tmfK6 (callW p n "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y, r.tail.headD 0] m)
    else tmfK6 (callW p n "target_major_of_outside" [vis, pp, pfo, pfl, x, y, ao, al, r4.headD 0, r4.tail.headD 0] m)
def tmcK1 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmcK2 p n vis pp cao cal pfo pfl fvo fvl ao al x y r
      (callW p n "sl_find" [r.headD 0, r.tail.headD 0, x] m)

/-- **The model of `target_major_of_const`** at exec fuel `n + 1`. -/
def tmcW (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) :
    Option (List Word × Mem) :=
  tmcK1 p n vis pp cao cal pfo pfl fvo fvl ao al x y (callW p n "block_shape_member_names" [pp] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) (r r4 : List Word)
theorem tmcK1_some : tmcK1 p n vis pp cao cal pfo pfl fvo fvl ao al x y (some (r, m)) =
    tmcK2 p n vis pp cao cal pfo pfl fvo fvl ao al x y r (callW p n "sl_find" [r.headD 0, r.tail.headD 0, x] m) := rfl
theorem tmcK2_some : tmcK2 p n vis pp cao cal pfo pfl fvo fvl ao al x y r4 (some (r, m)) =
    if r.headD 0 ≠ 0 then
      tmfK6 (callW p n "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y, r.tail.headD 0] m)
    else tmfK6 (callW p n "target_major_of_outside" [vis, pp, pfo, pfl, x, y, ao, al, r4.headD 0, r4.tail.headD 0] m) :=
  rfl
theorem tmfK6_some : tmfK6 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] tmcK1_some tmcK2_some tmfK6_some

set_option maxHeartbeats 1600000 in
theorem tmc_spec (p : Prog) (hp : p.lookup "target_major_of_const" = some targetMajorOfConst) (n : Nat)
    (s₀ : St) (vis pp cao cal pfo pfl fvo fvl ao al x y : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ tmcW p n s₀.mem vis pp cao cal pfo pfl fvo fvl ao al x y = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorOfConst]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "block_shape_member_names", callW_spec p n "sl_find",
      callW_spec p n "target_major_of_member", callW_spec p n "target_major_of_outside"] <;>
    finish (gen := 40) (instances := 20000) [tmcW, rdW_eq]

def tmfK3 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmfK6 (callW p n "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, r1.headD 0,
      r1.tail.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m)
def tmfK2 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 >>> 28 ≠ 3 then none
      else tmfK3 p n vis pp cao cal pfo pfl fvo fvl r1 (callW p n "e_view" [r.headD 0] m)
def tmfK1 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl fvo fvl mty : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => tmfK2 p n vis pp cao cal pfo pfl fvo fvl r (callW p n "get_app_fn_f" [CWF, mty] m)

/-- **The model of `target_major_of`** at exec fuel `n + 1`. -/
def tmfW (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl fvo fvl mty : Word) : Option (List Word × Mem) :=
  tmfK1 p n vis pp cao cal pfo pfl fvo fvl mty (callW p n "get_app_args_f" [CWF, mty] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl fvo fvl mty : Word) (r r1 : List Word)
theorem tmfK1_some : tmfK1 p n vis pp cao cal pfo pfl fvo fvl mty (some (r, m)) =
    tmfK2 p n vis pp cao cal pfo pfl fvo fvl r (callW p n "get_app_fn_f" [CWF, mty] m) := rfl
theorem tmfK2_some : tmfK2 p n vis pp cao cal pfo pfl fvo fvl r1 (some (r, m)) =
    if r.headD 0 >>> 28 ≠ 3 then none
      else tmfK3 p n vis pp cao cal pfo pfl fvo fvl r1 (callW p n "e_view" [r.headD 0] m) := rfl
theorem tmfK3_some : tmfK3 p n vis pp cao cal pfo pfl fvo fvl r1 (some (r, m)) =
    tmfK6 (callW p n "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, r1.headD 0,
      r1.tail.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m) := rfl
end arms
attribute [ind_grind] tmfK1_some tmfK2_some tmfK3_some

set_option maxHeartbeats 1600000 in
theorem tmf_spec (p : Prog) (hp : p.lookup "target_major_of" = some targetMajorOf) (n : Nat)
    (s₀ : St) (vis pp cao cal pfo pfl fvo fvl mty : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "target_major_of" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, mty]
    ⦃fun r s' => LocEq s' s₀ ∧ tmfW p n s₀.mem vis pp cao cal pfo pfl fvo fvl mty = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorOf]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "get_app_args_f", callW_spec p n "get_app_fn_f", callW_spec p n "e_view",
      callW_spec p n "target_major_of_const"] <;>
    finish (gen := 40) (instances := 20000) [tmfW, rdW_eq]

/-- The lookups of `target_major_of`. -/
structure TmfProg (p : Prog) : Prop where
  tmm : TmmProg p
  tmo : TmoOProg p
  mnc : p.lookup "member_names_copy" = some memberNamesCopy
  bsmn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  find : p.lookup "sl_find" = some slFind
  ev : p.lookup "e_view" = some eView
  tmc : p.lookup "target_major_of_const" = some targetMajorOfConst
  tmf : p.lookup "target_major_of" = some targetMajorOf

/-- **`target_major_of_const`'s model simulates `targetMajorOf` after the head's view.** -/
theorem tmcW_sim {p : Prog} (hP : TmfProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (hcs : CtorSums fe) (n : Nat) (hn : 2 ^ 31 + n ≤ coreWalkFuel) {m : Mem} {a : AState}
    {pp cao cal pfo pfl fvo fvl ao al x y : Word} {bs : BlockShape}
    {css : List (List (IConstantVal × Nat))} {pfvs fvs args : List EIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcss : PSlR decCNS css cao cal m) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) m fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hagb : ao.toNat + al.toNat ≤ iwTop m)
    (hx : H x) (hy : H y) (hPm : PosMR m) :
    Sim (tmcW p n m vis pp cao cal pfo pfl fvo fvl ao al x y)
      (match bs.memberNames.findIdx? (· == (decI x : NIdx)) with
        | some t => tmoMemT bs css pfvs fvs args (decI x) (decI y) t
        | none => tmoOutT fe bs pfvs args (decI x) (decI y)) a
      (fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ PosMR m') := by
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hqd, hq9, hptr⟩ := partsShapeFacts hq hsrc
  unfold tmcW
  refine Sim.mstep (K := tmcK1 p n vis pp cao cal pfo pfl fvo fvl ao al x y) rfl (fun _ _ => rfl) fun r4 m4 e4 => ?_
  obtain ⟨s4, rfl, hr4, hdn, hg4, hf4, ht4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.tmm.alloc hP.mnc hP.bsmn n _ pp bs hqd (by omega) hS.2.2.2.1 hS.2.2.2.2.2
      hsrc (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr o l j v h1 h2 h3 h4))) e4
  obtain ⟨s4', hs4', -, hW4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.tmm.alloc hP.mnc hP.bsmn n _ pp) e4
  have hroom := memberNamesW_room hW4 hS.2.2.2.1
  rw [partsShapeK hqd hq9] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  simp only at hr4 hdn hg4 hf4 ht4
  have hS4 : StageR dn vis fe s4.mem a := stage_frame_iw hS hf4 (by
    rw [← ht4]; simp only [iwTop] at hroom ⊢; omega)
  have hT4 : iwTop s4.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  have hP4 : PosMR s4.mem := hPm.fr (MFr.of_iw hf4)
  rw [tmcK1_some, hr4]
  simp only [List.headD_cons, List.tail_cons]
  obtain ⟨ws, hsl, hws, hwlt⟩ := slR_of_decHL s4.mem _ _ _ hdn (by omega)
  rw [UInt64.ofNat_toNat] at hsl
  refine Sim.mstep (K := tmcK2 p n vis pp cao cal pfo pfl fvo fvl ao al x y _) rfl (fun _ _ => rfl)
    fun r5 m5 e5 => ?_
  obtain ⟨s5, rfl, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (slFind_spec p hP.find n _ _ _ x) e5
  simp only at hm5
  have hlen : ws.length < 2 ^ 64 := by rw [slR_length hsl]; exact UInt64.toNat_lt _
  have hr5 := findW_ok n s4.mem _ _ x r5 ws hsl hW5 hlen
  rw [hm5] at *
  rw [hws, findIdx_decIP ws x hwlt hx, tmcK2_some]
  have hT4' : (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop s4.mem := ht4
  cases hfi : ws.findIdx? (· == x) with
  | some i =>
    rw [hfi] at hr5
    subst hr5
    simp only [List.headD_cons, List.tail_cons, ne_eq, show (1 : Word) ≠ 0 by decide, not_false_eq_true, if_true]
    obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hie : (UInt64.ofNat i : Word).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
    refine Sim.post (K := tmfK6) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
      (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow s4.mem m' ∧ PosMR m') ?_ ?_
    · intro r6 m6 e6
      cases n with
      | zero => rw [callW_zero] at e6; cases e6
      | succ k =>
      obtain ⟨s6, rfl, -, hW6⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
        (tmm_spec p hP.tmm.mem k _ pp cao cal pfo pfl fvo fvl ao al x y (UInt64.ofNat i)) e6
      have := tmmW_sim hP.tmm k (t := UInt64.ofNat i) (bs := bs) (css := css) hS4 (hq.grow (decBS_mono _) hg4)
        (partsHsrc_grow hg4 hq9 hsrc) (hcss.grow decCNS_mono hg4) (hpf.grow (OMono.decHL _ _) hg4)
        (hfv.grow (OMono.decHL _ _) hg4) (Nat.le_trans hfvb hg4.1) (hag.grow (OMono.decHL _ _) hg4)
        (Nat.le_trans hagb hg4.1) hx hy hP4 r6 s6.mem hW6
      rw [hie] at this
      exact this
    rintro r x' m' a' ⟨h1, h2, h3, h4⟩
    exact ⟨by simpa using h1, h2, hg4.trans h3, h4⟩
  | none =>
    rw [hfi] at hr5
    subst hr5
    simp only [List.headD_cons, List.tail_cons, ne_eq, not_true_eq_false, if_false]
    refine Sim.post (K := tmfK6) (f := fun r => [r.headD 0]) rfl (fun _ _ => rfl)
      (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
        IWGrow s4.mem m' ∧ PosMR m') ?_ ?_
    · intro r6 m6 e6
      cases n with
      | zero => rw [callW_zero] at e6; cases e6
      | succ k =>
      obtain ⟨s6, rfl, -, hW6⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
        (tmo_spec p hP.tmo.out k _ vis pp pfo pfl x y ao al _ _) e6
      exact tmoW_sim hP.tmo hcs k (by omega) hS4 (hq.grow (decBS_mono _) hg4) (by have := hg4.1; omega) hsl hwlt
        (fun j hj => by rw [UInt64.toNat_ofNat_of_lt' hkb] at hj; omega) hws.symm
        (hag.grow (OMono.decHL _ _) hg4) (Nat.le_trans hagb hg4.1) (hpf.grow (OMono.decHL _ _) hg4) hx hy hP4
        r6 s6.mem hW6
    rintro r x' m' a' ⟨h1, h2, h3, h4⟩
    exact ⟨by simpa using h1, h2, hg4.trans h3, h4⟩

end L.Ind
