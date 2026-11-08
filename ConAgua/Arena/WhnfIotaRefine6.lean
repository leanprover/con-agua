module

public import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.WordOff
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreRefine
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 6 (`iota_ctor_never_prop`, `iota_case3`)

The L function is split into small ones (`e_rec_get`, `const_name_of`, `ind_caps_check`) and the
`caps_never_zero` stub's statement is corrected (see `CapsNeverZeroOK`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The small L functions -/

/-- Model of `e_rec_get`. -/
def eRecGetW (m : Mem) (k : Word) : Option Word :=
  if k.toNat < (m.arr64 EREC).size then some (rdW (m.arr64 EREC) k) else none

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem eRecGet_spec (p : Prog) (hp : p.lookup "e_rec_get" = some eRecGetL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "e_rec_get" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ eRecGetW s₀.mem k = some (r.headD 0); ⊤⦄ := by
  sorry

-/

/-- Model of `const_name_of`. -/
def cnoW (m : Mem) (hh : Word) : Option Word :=
  if tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m CONST (tierW hh) ≤ idxW hh then none
  else some (tfld m CONST (tierW hh) (idxW hh) 0)

theorem constNameOf_spec (p : Prog) (hp : p.lookup "const_name_of" = some constNameOfL) (n : Nat)
    (s₀ : St) (hh : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "const_name_of" [hh]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ cnoW s₀.mem hh = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, constNameOfL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] <;>
    finish [cnoW, tierW, idxW]

/-- Model of `ind_caps_check` (callees at fuel `n`). -/
def iccW (p : Prog) (n : Nat) (m : Mem) (indP us : Word) : Option (Word × Mem) :=
  match callW p n "e_rec_get" [indP] m with
  | none => none
  | some (k, m0) =>
  if k.headD 0 ≠ 3 then some (0, m0) else
  match callW p n "ls_node" [us] m0 with
  | none => none
  | some (r1, m1) =>
  match callW p n "e_rec_get" [indP + 3] m1 with
  | none => none
  | some (lp, m2) =>
  if lp.headD 0 ≠ r1.tail.headD 0 then some (0, m2) else
  match callW p n "e_rec_get" [indP + 2] m2 with
  | none => none
  | some (po, m3) =>
  match callW p n "e_rec_get" [indP + 12] m3 with
  | none => none
  | some (swd, m4) =>
  match callW p n "e_rec_get" [indP + 13] m4 with
  | none => none
  | some (so, m5) =>
  match callW p n "e_rec_get" [indP + 14] m5 with
  | none => none
  | some (sc, m6) =>
  match callW p n "caps_never_zero"
      [po.headD 0, lp.headD 0, us, swd.headD 0, so.headD 0, sc.headD 0] m6 with
  | none => none
  | some (nz, m7) => some (nz.headD 0, m7)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem indCapsCheck_spec (p : Prog) (hp : p.lookup "ind_caps_check" = some indCapsCheckL)
    (n : Nat) (s₀ : St) (indP us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "ind_caps_check" [indP, us]
    ⦃fun r s' => LocEq s' s₀ ∧ iccW p n s₀.mem indP us = some (r.headD 0, s'.mem); ⊤⦄ := by
  sorry

-/

/-- Model of `iota_ctor_never_prop` (callees at fuel `n`). -/
def inpW (p : Prog) (n : Nat) (m : Mem) (vis ctorP us : Word) : Option (Word × Mem) :=
  match callW p n "e_rec_get" [ctorP + 4] m with
  | none => none
  | some (ty, m0) =>
  match callW p n "pi_result" [ty.headD 0] m0 with
  | none => none
  | some (r1, m1) =>
  match callW p n "get_app_fn" [r1.headD 0] m1 with
  | none => none
  | some (r2, m2) =>
  if tagW (r2.headD 0) ≠ 3 then some (0, m2) else
  match callW p n "const_name_of" [r2.headD 0] m2 with
  | none => none
  | some (r3, m3) =>
  match callW p n "env_find" [r3.headD 0, vis] m3 with
  | none => none
  | some (r4, m4) =>
  if r4.headD 0 = 0 then some (0, m4) else
  match callW p n "ind_caps_check" [r4.tail.headD 0, us] m4 with
  | none => none
  | some (r5, m5) => some (r5.headD 0, m5)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem iotaCtorNeverProp_spec (p : Prog)
    (hp : p.lookup "iota_ctor_never_prop" = some iotaCtorNeverPropL) (n : Nat) (s₀ : St)
    (vis ctorP us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "iota_ctor_never_prop" [vis, ctorP, us]
    ⦃fun r s' => LocEq s' s₀ ∧ inpW p n s₀.mem vis ctorP us = some (r.headD 0, s'.mem); ⊤⦄ := by
  sorry

-/


/-! ## The record of an inductive -/

theorem nat?_some {a : Array Word} {i k : Nat} (h : nat? (aread a) i = some k) :
    ∃ w, a[i]? = some w ∧ w.toNat = k := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, hk⟩ := h
  exact ⟨w, hw, hk⟩

theorem nat?_of {a : Array Word} {i : Nat} {w : Word} (h : a[i]? = some w) : nat? (aread a) i = some w.toNat := by
  simp [nat?, h]

theorem hlist?_slice {a : Array Word} {i : Nat} {l : List NIdx} (h : hlist? (aread a) i = some l) :
    ∃ o c : Word, a[i]? = some o ∧ a[i+1]? = some c ∧ hslice? (aread a) o.toNat c.toNat = some l := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, c, hc, hs⟩ := h
  obtain ⟨wo, hwo, rfl⟩ := nat?_some ho
  obtain ⟨wc, hwc, rfl⟩ := nat?_some hc
  exact ⟨wo, wc, hwo, hwc, hs⟩

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem decPW_ww {b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {pw : ConLeche.PropWhen} {swd so sc : Word} (h : decPW b dn q = some pw)
    (h0 : b[q]? = some swd) (h1 : b[q+1]? = some so) (h2 : b[q+2]? = some sc) :
    decPWw b dn swd so sc = some pw := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem decCI_ind_fields (b : Array Word) (dn : NIdx → Option ConLeche.Name) (q : Nat)
    (cv : IConstantVal) (caps : IIndCaps) (h : decCI (aread b) q = some (.indInfo cv caps)) :
    ∃ po pc swd so sc : Word, b[q+2]? = some po ∧ b[q+3]? = some pc ∧
      hslice? (aread b) po.toNat pc.toNat = some cv.levelParams ∧ b[q+12]? = some swd ∧
      b[q+13]? = some so ∧ b[q+14]? = some sc ∧ decPWw b dn swd so sc = some caps.sortZ := by
  sorry

-/

/-! ## The head name of a `const` handle -/

theorem viewConstName_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) (_hg : tagW h = 3) :
    a.store.viewConstName (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  have hfl := ConsR.flag hR.app
  have e : a.store.viewConstName (decE h) =
      ((if tierW h = 0 then a.store.pers else a.store.scr).consts.node? (idxW h).toNat).map
        (fun r => r.n) := by
    unfold EStore.viewConstName EStore.persGetConstName
    rw [decE_pers h hh]
    by_cases ht : tierW h = 0
    · simp [ht, ETables.getConstName, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
    · have hon : a.store.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hv.1 ⟨ht, h1⟩
      simp [ht, hon, ETables.getConstName, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
  rw [e, Tbl.node?, hk]
  simp [hn, decI_word]


/-! ## The family test -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The twin's tail of `iotaCtorNeverProp` at an inductive's record. -/
def inpTail (cvT : IConstantVal) (caps : IIndCaps) (us : LsIdx) : AM Bool := do
  match ← viewLsLen us with
  | none => failDanglingLs
  | some usl =>
    if cvT.levelParams.length == usl then capsNeverZero cvT.levelParams us caps else pure false
-/

theorem rdW_get (b : Array Word) (x v : Word) (hx : b[x.toNat]? = some v) : rdW b x = v := by
  simp [rdW, hx]

theorem eRec_val {m : Mem} {k v : Word} (h : eRecGetW m k = some v) :
    rdW (m.arr64 EREC) k = v := by
  simp only [eRecGetW] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h
  · cases h

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem inpTail_short (cvT : IConstantVal) (caps : IIndCaps) (us : LsIdx) (a : AState) (usl : Nat)
    (hv : a.store.lss.viewLen us = some usl) (hne : cvT.levelParams.length ≠ usl) :
    (inpTail cvT caps us).run a = .ok (false, a) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem inpTail_full (cvT : IConstantVal) (caps : IIndCaps) (us : LsIdx) (a a' : AState) (usl : Nat)
    (b : Bool) (hv : a.store.lss.viewLen us = some usl) (heq : cvT.levelParams.length = usl)
    (hc : (capsNeverZero cvT.levelParams us caps).run a = .ok (b, a')) :
    (inpTail cvT caps us).run a = .ok (b, a') := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem iccW_ok (p : Prog) (hp : IotaProg4 p) (hcn : CapsNeverZeroOK p) (n : Nat)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb : Word) (indP us : Word)
    (hus : HW us) (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (cvT : IConstantVal) (caps : IIndCaps)
    (hci : decCI (erecP m) indP.toNat = some (.indInfo cvT caps))
    (hfe : ∃ c, fe.find? c = some (.indInfo cvT caps)) (w : Word) (mF : Mem)
    (h : iccW p n m indP us = some (w, mF)) :
    ∃ (b : Bool) (a' : AState), (inpTail cvT caps (decI us)).run a = .ok (b, a') ∧
      (w != 0) = b ∧ CoreAfter dn m mF a' vis fe M eb ∧ HW w := by
  sorry

-/


section inpRun
variable (fe : IFEnv) (cvj : IConstantVal) (us : LsIdx) (a : AState) (pr hh : EIdx)
  (hpr : (piResult coreWalkFuel cvj.type).run a = .ok (pr, a))
  (hga : (getAppFn coreWalkFuel pr).run a = .ok (hh, a))

theorem viewConstName_run (a : AState) (h : EIdx) :
    (viewConstName h).run a = .ok (a.store.viewConstName h, a) := rfl

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hpr hga in
theorem inp_run_not (ht : hh.tag ≠ ETag.const) :
    (iotaCtorNeverProp fe cvj us).run a = .ok (false, a) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hpr hga in
theorem inp_run_other (T : NIdx) (hv : a.store.viewConstName hh = some T)
    (ht : hh.tag = ETag.const) (hf : ∀ cvT caps, fe.find? T ≠ some (.indInfo cvT caps)) :
    (iotaCtorNeverProp fe cvj us).run a = .ok (false, a) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
include hpr hga in
theorem inp_run_ind (T : NIdx) (hv : a.store.viewConstName hh = some T)
    (ht : hh.tag = ETag.const) (cvT : IConstantVal) (caps : IIndCaps)
    (hf : fe.find? T = some (.indInfo cvT caps)) (b : Bool) (a' : AState)
    (htl : (inpTail cvT caps us).run a = .ok (b, a')) :
    (iotaCtorNeverProp fe cvj us).run a = .ok (b, a') := by
  sorry

-/

end inpRun


theorem rdW_eq_three {b : Array Word} {x : Word} (h : rdW b x = 3) : b[x.toNat]? = some 3 := by
  cases hx : b[x.toNat]? with
  | none => simp [rdW, hx] at h
  | some w => simp only [rdW, hx, Option.getD_some] at h; rw [h]

theorem iccW_kind (p : Prog) (hp : IotaProg4 p) (n : Nat) (m : Mem) (indP us w : Word) (mF : Mem)
    (hk : rdW (m.arr64 EREC) indP ≠ 3) (h : iccW p n m indP us = some (w, mF)) :
    w = 0 ∧ mF = m := by
  sorry

/-! ## `iota_case3(rlk, vis, ctorP, us)` -/

/-- Model of `iota_case3` (callee at fuel `n`). -/
def icW (p : Prog) (n : Nat) (m : Mem) (rlk vis ctorP us : Word) : Option (Word × Mem) :=
  if rlk ≠ 0 then some (0, m)
  else match callW p n "iota_ctor_never_prop" [vis, ctorP, us] m with
    | none => none
    | some (r, m') => some (if r.headD 0 = 0 then 1 else 0, m')

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem iotaCase3_spec (p : Prog) (hp : p.lookup "iota_case3" = some iotaCase3L) (n : Nat)
    (s₀ : St) (rlk vis ctorP us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "iota_case3" [rlk, vis, ctorP, us]
    ⦃fun r s' => LocEq s' s₀ ∧ icW p n s₀.mem rlk vis ctorP us = some (r.headD 0, s'.mem); ⊤⦄ := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem iotaCase3_run_k (fe : IFEnv) (rl : IRecRule) (cvj : IConstantVal) (us : LsIdx) (a : AState)
    (hk : rl.k = true) : (iotaCase3 fe rl cvj us).run a = .ok (false, a) := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem iotaCase3_run_nk (fe : IFEnv) (rl : IRecRule) (cvj : IConstantVal) (us : LsIdx) (a a' : AState)
    (np : Bool) (hk : rl.k = false) (h : (iotaCtorNeverProp fe cvj us).run a = .ok (np, a')) :
    (iotaCase3 fe rl cvj us).run a = .ok (!np, a') := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`iota_case3` refines `iotaCase3`.** -/
@[refines ConRon.Arena.iotaCase3]
theorem iotaCase3_refines (p : Prog) (hp : IotaProg4 p) (hcn : CapsNeverZeroOK p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb rlk ctorP us : Word) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us → rl.k = (rlk != 0) →
    decCI (erecP s₀.mem) ctorP.toNat = some (.ctorInfo cvj cnP cnF) →
    CoreSpec p n "iota_case3" [rlk, vis, ctorP, us] (iotaCase3 fe rl cvj (decI us)) decBool s₀ a₀ dn
      vis fe MM eb := by
  sorry

-/

end L.Arena
