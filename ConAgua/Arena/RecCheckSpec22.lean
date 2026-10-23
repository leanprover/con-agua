import ConAgua.Arena.RecCheckSpec21

/-!
# `RecCheck`: `targetRecPins`' name pins (lane `indproofs3`, helper `rec2`)

`ptr_list_names` under the stage relation at any slice decoded below the tops (an empty slice's
offset is whatever its record holds), and `target_rec_pins_names`: the auxiliary names wanted
(`n₀.rec_1 …`) against the ones the stream has, as sets, and no two recursors sharing a name.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The lookups -/

/-- The program bundle of `target_rec_pins` and its callees. -/
structure RpLook (p : Prog) : Prop extends IndPartsProg3 p where
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  slEq : p.lookup "sl_eq" = some slEq
  lpsOne : p.lookup "block_rec_lps_one" = some blockRecLpsOne
  lpsGo : p.lookup "block_rec_lps_ok_go" = some blockRecLpsOkGo
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  lpsOk : p.lookup "block_rec_lps_ok" = some blockRecLpsOk
  unres : p.lookup "block_rec_names_unreserved" = some blockRecNamesUnreserved
  soa : p.lookup "block_rec_split_own_aux" = some blockRecSplitOwnAux
  wan : p.lookup "block_rec_want_aux_names" = some blockRecWantAuxNames
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

/-- A guard on a pure test: the model aborts when the callee returned `0`, the twin passes
`unless c do fail e` when `c`. -/
theorem Sim.guardPure {γ δ : Type} {K : Option (List Word × Mem) → Option (γ × Mem)}
    {body : Mem → Option (γ × Mem)} {mo : Option (List Word × Mem)} {c : Bool} {e : CheckError}
    {g : PUnit → AM δ} {a : AState} {Q : Mem → Prop} {R : γ → δ → Mem → AState → Prop}
    (hn : K none = none) (hs : ∀ r m₁, K (some (r, m₁)) = if r.headD 0 = 0 then none else body m₁)
    (h1 : ∀ r m₁, mo = some (r, m₁) → r.headD 0 = (if c then 1 else 0) ∧ Q m₁)
    (h2 : ∀ m₁, Q m₁ → Sim (body m₁) (g PUnit.unit) a R) :
    Sim (K mo) ((unless c do fail e) >>= g) a R := by
  intro r m' e'
  cases hmo : mo with
  | none => rw [hmo, hn] at e'; cases e'
  | some x =>
    obtain ⟨r₁, m₁⟩ := x
    rw [hmo, hs] at e'
    obtain ⟨hr, hQ⟩ := h1 r₁ m₁ hmo
    cases c with
    | false => rw [if_neg (by decide)] at hr; rw [if_pos hr] at e'; cases e'
    | true =>
      rw [if_pos rfl] at hr
      rw [if_neg (by rw [hr]; decide)] at e'
      obtain ⟨y, a₂, h2r, hR⟩ := h2 m₁ hQ r m' e'
      exact ⟨y, a₂, by simpa [StateT.run_bind] using h2r, hR⟩

/-- A guard on a twin test `op`: `unless ← op do fail e`. -/
theorem Sim.guardRun {γ δ : Type} {K : Option (List Word × Mem) → Option (γ × Mem)}
    {body : Mem → Option (γ × Mem)} {mo : Option (List Word × Mem)} {op : AM Bool} {e : CheckError}
    {g : PUnit → AM δ} {a : AState} {Q : Mem → AState → Prop} {R : γ → δ → Mem → AState → Prop}
    (hn : K none = none) (hs : ∀ r m₁, K (some (r, m₁)) = if r.headD 0 = 0 then none else body m₁)
    (h1 : Sim mo op a (fun r b m₁ a₁ => r.headD 0 = (if b then 1 else 0) ∧ Q m₁ a₁))
    (h2 : ∀ m₁ a₁, Q m₁ a₁ → Sim (body m₁) (g PUnit.unit) a₁ R) :
    Sim (K mo) (op >>= fun b => (unless b do fail e) >>= g) a R := by
  intro r m' e'
  cases hmo : mo with
  | none => rw [hmo, hn] at e'; cases e'
  | some x =>
    obtain ⟨r₁, m₁⟩ := x
    rw [hmo, hs] at e'
    obtain ⟨b, a₁, hrun, hr, hQ⟩ := h1 r₁ m₁ hmo
    cases b with
    | false => rw [if_neg (by decide)] at hr; rw [if_pos hr] at e'; cases e'
    | true =>
      rw [if_pos rfl] at hr
      rw [if_neg (by rw [hr]; decide)] at e'
      obtain ⟨y, a₂, h2r, hR⟩ := h2 m₁ a₁ hQ r m' e'
      exact ⟨y, a₂, by rw [StateT.run_bind, hrun]; simpa [StateT.run_bind, except_ok_bind] using h2r, hR⟩

/-- A guard whose twin side is any computation that passes on to `g` when `op` returns `true`. -/
theorem Sim.guardPass {γ δ : Type} {K : Option (List Word × Mem) → Option (γ × Mem)}
    {body : Mem → Option (γ × Mem)} {mo : Option (List Word × Mem)} {op : AM Bool}
    {g whole : AM δ} {a : AState} {Q : Mem → AState → Prop} {R : γ → δ → Mem → AState → Prop}
    (hn : K none = none) (hs : ∀ r m₁, K (some (r, m₁)) = if r.headD 0 = 0 then none else body m₁)
    (h1 : Sim mo op a (fun r b m₁ a₁ => r.headD 0 = (if b then 1 else 0) ∧ Q m₁ a₁))
    (hpass : ∀ a₁, op.run a = .ok (true, a₁) → whole.run a = g.run a₁)
    (h2 : ∀ m₁ a₁, Q m₁ a₁ → Sim (body m₁) g a₁ R) :
    Sim (K mo) whole a R := by
  intro r m' e'
  cases hmo : mo with
  | none => rw [hmo, hn] at e'; cases e'
  | some x =>
    obtain ⟨r₁, m₁⟩ := x
    rw [hmo, hs] at e'
    obtain ⟨b, a₁, hrun, hr, hQ⟩ := h1 r₁ m₁ hmo
    cases b with
    | false => rw [if_neg (by decide)] at hr; rw [if_pos hr] at e'; cases e'
    | true =>
      rw [if_pos rfl] at hr
      rw [if_neg (by rw [hr]; decide)] at e'
      obtain ⟨y, a₂, h2r, hR⟩ := h2 m₁ a₁ hQ r m' e'
      exact ⟨y, a₂, by rw [hpass a₁ hrun]; exact h2r, hR⟩

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
  simp only [tpnK3]; rw [if_pos h]
theorem tpnK3_ok (h : ¬ r.headD 0 = 0) : tpnK3 p n reco recl (some (r, m)) =
    tpnK4 p n (callW p n "ptr_list_names" [reco, recl] m) := by simp only [tpnK3]; rw [if_neg h]
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

end L.Ind
