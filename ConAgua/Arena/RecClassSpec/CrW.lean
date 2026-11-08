module

import ConAgua.Arena.LdRd
import ConAgua.Arena.IndSumSpec.DecHLTake
public import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecClassSpec.PiBWRoom
public import ConAgua.Arena.RecClassSpec.ReadProg
import ConAgua.Arena.IndPartsSpec.BlockCounts
import ConAgua.Arena.IndRealAbsSim
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.IndRealOpf3
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.IndPartsSpec.RecTW
public import ConAgua.Arena.IndRealOpf
public import ConAgua.Arena.RecClassSpec.Classes
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.RecClass

@[expose] public section

/-!
# CrW

`OpfJ`, `opfJ_real`, `fvarHeadW_afr`, `crW_nil`, `crW_big`, `crW_cons` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## How `class_read`'s models read `open_pis_at_fvars_f`

The models of `class_read` and its callees read their `open_pis_at_fvars_f` calls through a
`cR : CallM` (`IndCallM.lean`): `stubCall` (the stub contract, for the `StageR` proofs) or
`realCall p` (the program's own call, for `AbsOK` across `class_read`). Their relational lemmas
take `OpfJ cR J`: the reading refines the twin and keeps an invariant `J` of the memory, which
every `AFr` step keeps as well (`J := True` for the stubs, `J := AbsOK` for the real call). -/

/-- **`cR`'s `open_pis_at_fvars_f` refines `openPisAtFvarsF`, keeping `J`**; `J` is kept by every
step that keeps `AbsOK`. -/
def OpfJ (cR : CallM) (J : Mem → Prop) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    Prop :=
  (∀ m m', AFr m m' → J m → J m') ∧
  ∀ (N : Nat) (k e i : Word), H e → ∀ (m m' : Mem) (a : AState) (r : List Word),
    cR N "open_pis_at_fvars_f" [k, e, i] m = some (r, m') → StageR vis fe m a → J m →
    ∃ x a', (openPisAtFvarsF k.toNat (decI e) i.toNat).run a = .ok (x, a') ∧
      KeepPost vis fe decOLE m m' a' r x ∧ J m'

/-- The program's own reading keeps `AbsOK` (`opfF_ok`). -/
theorem opfJ_real {p : Prog} (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) : OpfJ (realCall p) AbsOK dn vis fe := by
  sorry

theorem fvarHeadW_afr {m m' : Mem} {e : Word} {r : List Word} (h : fvarHeadW m e = some (r, m')) :
    AFr m m' := by
  unfold fvarHeadW at h
  afr_auto h [gafF_afr]

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m4 m5 : Mem) (nP mo ml ro rl c : Word) (r r1 r2 r4 r5 : List Word)
theorem crW_nil (h : rl = 0) : crW cR (n + 1) m nP mo ml ro rl = some ([1, 0, 0], m) := by simp [crW, h]
theorem crW_big (h : rl ≠ 0) (h1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 2) + 1 = 0) :
    crW cR (n + 1) m nP mo ml ro rl = none := by
  simp [crW, h, h1]
theorem crW_cons (h : rl ≠ 0) (h1 : rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 2) + 1 ≠ 0) :
    crW cR (n + 1) m nP mo ml ro rl = crK1 cR n nP mo ml ro rl
      (cR n "open_pis_at_fvars_f"
        [rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 2) + 1,
         rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0] m) := by
  simp [crW, h, h1]
theorem crK1_fail (h : r1.headD 0 = 0) : crK1 cR n nP mo ml ro rl (some (r1, m1)) = some ([0, 0, 0], m1) := by
  rw [crK1, ite_eq_left h]
theorem crK1_ok (h : r1.headD 0 ≠ 0) : crK1 cR n nP mo ml ro rl (some (r1, m1)) =
    crK2 cR n nP mo ml ro rl m1 (fvarHeadW m1 (r1.tail.tail.tail.headD 0)) := by
  rw [crK1, ite_eq_right h]
theorem crK2_fail (h : r2.headD 0 = 0) : crK2 cR n nP mo ml ro rl m1 (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [crK2, ite_eq_left h]
theorem crK2_ok (h : r2.headD 0 ≠ 0) : crK2 cR n nP mo ml ro rl m1 (some (r2, m2)) =
    crK3 cR n nP mo ml ro rl m2 (cmvW (n - 1) m2 nP mo ml (r2.tail.headD 0)) := by
  rw [crK2, ite_eq_right h]
theorem crK3_fail (r3 : List Word) (h : r3.headD 0 = 0) : crK3 cR n nP mo ml ro rl m2 (some r3) = some ([0, 0, 0], m2) := by
  rw [crK3, ite_eq_left h]
theorem crK3_ok (r3 : List Word) (h : r3.headD 0 ≠ 0) : crK3 cR n nP mo ml ro rl m2 (some r3) =
    crK4 n (r3.tail.headD 0) (crW cR n m2 nP mo ml (ro + 1) (rl - 1)) := by
  rw [crK3, ite_eq_right h]
theorem crK4_fail (h : r4.headD 0 = 0) : crK4 n c (some (r4, m4)) = some ([0, 0, 0], m4) := by
  rw [crK4, ite_eq_left h]
theorem crK4_ok (h : r4.headD 0 ≠ 0) : crK4 n c (some (r4, m4)) =
    crK5 (consW n m4 c (r4.tail.headD 0) (r4.tail.tail.headD 0)) := by
  rw [crK4, ite_eq_right h]
theorem crK5_some : crK5 (some (r5, m5)) = some ([1, r5.headD 0, r5.tail.headD 0], m5) := by rw [crK5]
end arms

grind_pattern [ind_grind] crW_nil => crW cR (n + 1) m nP mo ml ro rl
grind_pattern [ind_grind] crW_big => crW cR (n + 1) m nP mo ml ro rl
grind_pattern [ind_grind] crW_cons => crW cR (n + 1) m nP mo ml ro rl
grind_pattern [ind_grind] crK1_fail => crK1 cR n nP mo ml ro rl (some (r1, m1))
grind_pattern [ind_grind] crK1_ok => crK1 cR n nP mo ml ro rl (some (r1, m1))
grind_pattern [ind_grind] crK2_fail => crK2 cR n nP mo ml ro rl m1 (some (r2, m2))
grind_pattern [ind_grind] crK2_ok => crK2 cR n nP mo ml ro rl m1 (some (r2, m2))
grind_pattern [ind_grind] crK3_fail => crK3 cR n nP mo ml ro rl m2 (some r3)
grind_pattern [ind_grind] crK3_ok => crK3 cR n nP mo ml ro rl m2 (some r3)
grind_pattern [ind_grind] crK4_fail => crK4 n c (some (r4, m4))
grind_pattern [ind_grind] crK4_ok => crK4 n c (some (r4, m4))
grind_pattern [ind_grind] crK5_some => crK5 (some (r5, m5))

theorem classReadRecCls_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_read_rec_cls" = some classReadRecCls) (had : AdF p) (cR : CallM)
    (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (nP mo ml ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_rec_cls" [nP, mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ crW cR n s₀.mem nP mo ml ro rl = some (r, s'.mem); ⊤⦄ := by
  sorry

theorem findIdx_lt (p : Nat) : ∀ (l : List Nat) (i : Nat), l.findIdx? (· == p) = some i → i < l.length := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons a t ih =>
    intro i h
    simp only [List.findIdx?_cons] at h
    by_cases hb : (a == p) = true
    · simp [hb] at h; subst h; simp
    · simp only [hb, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      have := ih j hj
      simp; omega

theorem cmv_lt (nP : Nat) (ms : List Nat) (pv i : Nat)
    (h : ConRon.Arena.classOfMotiveVar nP ms pv = some i) : i < ms.length := by
  simp only [ConRon.Arena.classOfMotiveVar] at h
  split at h
  · exact findIdx_lt _ ms i h
  · simp at h

theorem decRS_fields {m : Mem} {p : Nat} {R : RecShape} (h : decRS m p = some R) :
    ∃ q, iwN m p = some q ∧ decCVp m q = some R.cvR ∧ iwN m (p + 2) = some R.mI := by
  sorry

section crsteps
variable (nP : Nat) (motPos : List Nat) (rc : RecShape) (rest : List RecShape) (a a1 a2 a4 : AState)

theorem cr_fail1 (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (none, a1)) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (none, a1) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, Except.bind]
  rfl

theorem cr_fail2 (xs : List EIdx) (concl : EIdx)
    (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (some (xs, concl), a1))
    (hrun2 : (ConRon.Arena.fvarHead concl) a1 = .ok (none, a2)) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (none, a2) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, hrun2, Except.bind]
  rfl

theorem cr_fail3 (xs : List EIdx) (concl : EIdx) (i : Nat)
    (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (some (xs, concl), a1))
    (hrun2 : (ConRon.Arena.fvarHead concl) a1 = .ok (some i, a2))
    (hc : ConRon.Arena.classOfMotiveVar nP motPos i = none) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (none, a2) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, hrun2, hc, Except.bind]
  rfl

theorem cr_fail4 (xs : List EIdx) (concl : EIdx) (i c : Nat)
    (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (some (xs, concl), a1))
    (hrun2 : (ConRon.Arena.fvarHead concl) a1 = .ok (some i, a2))
    (hc : ConRon.Arena.classOfMotiveVar nP motPos i = some c)
    (hrun4 : (ConRon.Arena.classReadRecCls nP motPos rest) a2 = .ok (none, a4)) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (none, a4) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, hrun2, hc, hrun4, Except.bind]
  rfl

theorem cr_ok (xs : List EIdx) (concl : EIdx) (i c : Nat) (cs : List Nat)
    (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (some (xs, concl), a1))
    (hrun2 : (ConRon.Arena.fvarHead concl) a1 = .ok (some i, a2))
    (hc : ConRon.Arena.classOfMotiveVar nP motPos i = some c)
    (hrun4 : (ConRon.Arena.classReadRecCls nP motPos rest) a2 = .ok (some cs, a4)) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (some (c :: cs), a4) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, hrun2, hc, hrun4, Except.bind]
  rfl
end crsteps

/-- `class_read_rec_cls`'s result against the twin's `Option (List Nat)`. -/
def CrRes (m' : Mem) (r : List Word) : Option (List Nat) → Prop
  | none => r.headD 0 = 0
  | some cs => r.headD 0 = 1 ∧
      decNL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some cs ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m'

theorem crW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (nP mo ml ro rl : Word) (r : List Word) (recs : List RecShape)
      (motPos : List Nat),
    crW cR n m nP mo ml ro rl = some (r, m') → StageR vis fe m a → J m →
    decPL m (decRS m) ro.toNat rl.toNat = some recs →
    (∀ m1, IWGrow m m1 → decPL m1 (decRS m1) ro.toNat rl.toNat = some recs) →
    decNL m mo.toNat ml.toNat = some motPos → mo.toNat + ml.toNat ≤ iwTop m →
    ro.toNat + rl.toNat < 2 ^ 64 →
    ∃ res a', (ConRon.Arena.classReadRecCls nP.toNat motPos recs).run a = .ok (res, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ CrRes m' r res ∧ J m' := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem mapM_decCVp_grow {m m' : Mem} (hg : IWGrow m m') :
    ∀ (ps : List Nat), (∀ q ∈ ps, CVExt m q) → ps.mapM (decCVp m') = ps.mapM (decCVp m)
  | [], _ => rfl
  | q :: ps, h => by
    simp only [List.mapM_cons]
    rw [decCVp_grow_r hg (h q (List.mem_cons_self ..)),
      mapM_decCVp_grow hg ps (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]
-/

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

l_model classReadMinorIh1_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1) (had : AdF p)
  fns [hi1 ↦ ih1W list]
  specs [ftdF_spec p had n, pirF_spec p had n, gaaF_spec p had n,
    fvarHead_spec p hfh hv had n, classOfMotiveVar_spec p hf hcm n]
  grind [arena_grind]

l_model classReadMinorIhs_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
    (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs) (had : AdF p)
  fns [his ↦ ihsW list]
  specs [classReadMinorIh1_spec p hfh hv hf hcm hi1 had n, rec2_specW p ha n h2,
    slCons_specW p ha hc hsc n]
  grind [arena_grind]

l_model classReadMinorFinish_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
    (h5 : p.lookup "rec5" = some rec5)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
    (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs)
    (hfin : p.lookup "class_read_minor_finish" = some classReadMinorFinish) (had : AdF p)
  fns [hfin ↦ finW list]
  specs [eView_spec p hv n, classReadMinorIhs_spec p hfh hv hf hcm hc ha hsc h2 hi1 his had n,
    rec5_specW p ha n h5]
  grind [arena_grind]

l_model classReadMinorTail_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
    (h5 : p.lookup "rec5" = some rec5)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
    (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs)
    (hfin : p.lookup "class_read_minor_finish" = some classReadMinorFinish)
    (htl : p.lookup "class_read_minor_tail" = some classReadMinorTail) (had : AdF p)
  fns [htl ↦ tailW list]
  specs [gaaF_spec p had n, gafF_spec p had n,
    classReadMinorFinish_spec p hfh hv hf hcm hc ha hsc h2 h5 hi1 his hfin had n]
  grind [arena_grind] extra [ld64_rd_spec]

l_model classReadMinor_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
    (h5 : p.lookup "rec5" = some rec5)
    (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
    (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs)
    (hfin : p.lookup "class_read_minor_finish" = some classReadMinorFinish)
    (hpb : p.lookup "pi_binders" = some piBinders)
    (hmin : p.lookup "class_read_minor" = some classReadMinor)
    (htl : p.lookup "class_read_minor_tail" = some classReadMinorTail) (had : AdF p)
    (cR : CallM) (hcR : CallSpec p cR)
  fns [hmin ↦ minorW list]
  specs [piBinders_spec p ha hc hv hsc hpb n, hcR n "open_pis_at_fvars_f",
    fvarHead_spec p hfh hv had n, classOfMotiveVar_spec p hf hcm n,
    classReadMinorTail_spec p hfh hv hf hcm hc ha hsc h2 h5 hi1 his hfin htl had n]
  grind [arena_grind] extra [ld64_rd_spec]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

theorem simPiResult (hS : StageR vis fe m a) {e : Word} (he : H e) :
    RSim (pirF m [CWF, e]) (piResult coreWalkFuel (decI e)) a (KP dn vis fe m decW0E) := by
  have h := (pirF_ok dn vis fe CWF e he).sim hS; rw [CWF_eq] at h; exact h

theorem simGetAppFn (hS : StageR vis fe m a) {e : Word} (he : H e) :
    RSim (gafF m [CWF, e]) (getAppFn coreWalkFuel (decI e)) a (KP dn vis fe m decW0E) := by
  have h := (gafF_ok dn vis fe CWF e he).sim hS; rw [CWF_eq] at h; exact h

/-- A reading `cR` of `open_pis_at_fvars_f` with `OpfJ` as a `RSim`: the stub contract's post and
the invariant `J` after. -/
theorem OpfJ.sim {cR : CallM} {J : Mem → Prop} (hO : OpfJ cR J dn vis fe) (N : Nat)
    (hS : StageR vis fe m a) (hJ : J m) {k e i : Word} (he : H e) :
    RSim (cR N "open_pis_at_fvars_f" [k, e, i] m) (openPisAtFvarsF k.toNat (decI e) i.toNat) a
      (fun b a' x => KP dn vis fe m decOLE b a' x ∧ J b.2) := by
  rintro ⟨r, m'⟩ h
  obtain ⟨x, a', hrun, hK, hJ'⟩ := hO.2 N k e i he m m' a r h hS hJ
  exact ⟨x, a', hrun, hK, hJ'⟩

/-- `J` added to a model chain's post across a step that keeps `AbsOK`. -/
theorem RSim.withJ {β α : Type} {o : Option (β × Mem)} {op : AM α} {Q : β × Mem → AState → α → Prop}
    {J : Mem → Prop} (hJk : ∀ m m', AFr m m' → J m → J m') (h : RSim o op a Q)
    (hf : ∀ r m', o = some (r, m') → AFr m m') (hJ : J m) :
    RSim o op a (fun b a' x => Q b a' x ∧ J b.2) :=
  RSim.withF h fun ⟨r, m'⟩ hb => hJk _ _ (hf r m' hb) hJ

/-- `fvar_head`'s result. -/
def decFH (r : List Word) : Option Nat → Prop
  | none => r = [0, 0]
  | some i => r = [1, UInt64.ofNat i] ∧ i < 2 ^ 64

theorem simFvarHead (hS : StageR vis fe m a) {e : Word} (he : H e) :
    RSim (fvarHeadW m e) (ConRon.Arena.fvarHead (decI e)) a
      (fun b a' x => StageR vis fe b.2 a' ∧ IWGrow m b.2 ∧ decFH b.1 x) := by
  sorry

end sims

/-! ## Reading the last element of a decoded slice -/

theorem decHL_last {k : IdxKind} {m : Mem} {wo wl : Word} {xs : List (Idx k)}
    (h : decHL m wo.toNat wl.toNat = some xs) (hl : wl ≠ 0) (hb : wo.toNat + wl.toNat < 2 ^ 64) :
    ∃ w, rdW (m.arr64 IW) (wo + wl - 1) = w ∧ H w ∧ xs.getLast? = some (decI w) := by
  have hl0 : wl.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hlen := decHL_length m h
  obtain ⟨w, h1, h2, h3⟩ := decHL_get' h (wl.toNat - 1) (by omega) (by omega)
  have he : UInt64.ofNat (wo.toNat + (wl.toNat - 1)) = wo + wl - 1 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega), UInt64.toNat_sub_of_le _ _ ?_, UInt64.toNat_add]
    · simp; omega
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; simp; omega
  rw [he] at h1
  refine ⟨w, h1, h2, ?_⟩
  rw [List.getLast?_eq_getElem?, hlen, ← h3]
  exact List.getElem?_eq_getElem _

/-! ## `class_read_minor_ih1` -/

/-- The twin's `filterMapM` body in `classReadMinor`. -/
def ihStep (nP : Nat) (motPos : List Nat) (d : Nat) (x : EIdx) : AM (Option (Nat × Nat)) := do
  let ty ← fvarTypeD x
  let r ← piResult coreWalkFuel ty
  match ← ConRon.Arena.fvarHead r with
  | none => pure none
  | some p2 =>
    match ConRon.Arena.classOfMotiveVar nP motPos p2 with
    | none => pure none
    | some t => do
      let rargs ← getAppArgs coreWalkFuel r
      match rargs.getLast? with
      | none => pure none
      | some a =>
        match ← ConRon.Arena.fvarHead a with
        | none => pure none
        | some f => pure (if d ≤ f then some (f - d, t) else none)

/-- `class_read_minor_ih1`'s result. -/
def decIH (_m : Mem) (r : List Word) : Option (Nat × Nat) → Prop
  | none => r.headD 0 = 0
  | some (f, t) => r = [1, UInt64.ofNat f, UInt64.ofNat t] ∧ f < 2 ^ 64 ∧ t < 2 ^ 64

theorem ofNat_sub_word (f : Nat) (d : Word) (hf : f < 2 ^ 64) (hd : d.toNat ≤ f) :
    UInt64.ofNat f - d = UInt64.ofNat (f - d.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hf]; exact hd),
    UInt64.toNat_ofNat_of_lt' hf, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]

theorem ih1W_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d x : Word) (motPos : List Nat) (hS : StageR vis fe m a) (hx : H x)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (ih1W n m nP mo ml d x) (ihStep nP.toNat motPos d.toNat (decI x)) a (KP dn vis fe m decIH) := by
  sorry

/-- A word of a fresh record, read stably. -/
theorem rec_iwN_stab {m m' : Mem} {ws : List Word} {q : Word} (hq : q = rdW (m.arr64 CTL) 200)
    (hget : ∀ j < ws.length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = ws[j]?)
    (htop : iwTop m' = iwTop m + ws.length) (j : Nat) (hj : j < ws.length) :
    StabD (fun m => iwN m (q.toNat + j)) m' (ws[j]'hj).toNat := by
  sorry

theorem decNN_stab {m : Mem} {q x y : Nat} (h1 : StabD (fun m => iwN m q) m x)
    (h2 : StabD (fun m => iwN m (q + 1)) m y) : StabD (fun m => decNN m q) m (x, y) := by
  intro m' hg
  simp only [decNN, h1 m' hg, h2 m' hg]; rfl

/-- The stable record `[a, b]` built by `rec2`. -/
theorem rec2_decNN {m m' : Mem} {a b q : Word} (hq : q = rdW (m.arr64 CTL) 200)
    (hget : ∀ j < [a, b].length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = [a, b][j]?)
    (htop : iwTop m' = iwTop m + [a, b].length) :
    StabD (fun m => decNN m q.toNat) m' (a.toNat, b.toNat) :=
  decNN_stab (by simpa using rec_iwN_stab hq hget htop 0 (by simp))
    (by simpa using rec_iwN_stab hq hget htop 1 (by simp))

/-! ## `class_read_minor_ihs` -/

/-- `class_read_minor_ihs`'s result: a stable slice of `[field, class]` records. -/
def decIHS (m' : Mem) (r : List Word) (ihs : List (Nat × Nat)) : Prop :=
  SPL decNN m' (r.headD 0).toNat (r.tail.headD 0).toNat ihs

theorem ihsW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nP mo ml d : Word)
    (motPos : List Nat) (n : Nat) : ∀ (m : Mem) (a : AState) (fo fl : Word) (fvs : List EIdx),
    StageR vis fe m a → decHL m fo.toNat fl.toNat = some fvs → fo.toNat + fl.toNat ≤ iwTop m →
    decNL m mo.toNat ml.toNat = some motPos → mo.toNat + ml.toNat ≤ iwTop m →
    RSim (ihsW n m nP mo ml d fo fl) (fvs.filterMapM (ihStep nP.toNat motPos d.toNat)) a
      (KP dn vis fe m decIHS) := by
  sorry

/-! ## `class_read_minor_finish` -/

/-- A `const` handle's view, through `e_view`'s words. -/
theorem viewConstW {m : Mem} {a : AState} (hR : ArenaR m a) {w : Word} (hne : eViewW m w ≠ [])
    (hg : tagW w = 3) :
    (ConRon.Arena.viewConst (decE w)).run a = .ok (some (decI ((eViewW m w).tail.headD 0),
      decI ((eViewW m w).tail.tail.headD 0)), a) ∧ H ((eViewW m w).tail.headD 0) ∧
      H ((eViewW m w).tail.tail.headD 0) := by
  obtain ⟨v, hv, hR'⟩ := eViewW_ok m a hR w hne
  have hhead := eViewW_head3 m w hne hg
  cases v with
  | const nn us =>
    simp only [ViewR, getD_one, getD_two] at hR'
    obtain ⟨-, hn1, hn2, hu1, hu2⟩ := hR'
    refine ⟨?_, hn1, hu1⟩
    show Except.ok (a.store.viewConst (decE w), a) = _
    rw [EStore.viewConst_of_view_r _ _ _ _ hv, hn2, hu2]
  | bvar i => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | fvar i ty => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | sort u => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | app f x => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | lam f x => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | forallE f x => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | letE f x y => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)
  | lit l => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR') (by decide)
  | proj f x y => simp only [ViewR] at hR'; exact absurd (hhead.symm.trans hR'.1) (by decide)

/-- A handle word of a fresh record, read stably. -/
theorem rec_iwH_stab {kk : IdxKind} {m m' : Mem} {ws : List Word} {q : Word} (hq : q = rdW (m.arr64 CTL) 200)
    (hget : ∀ j < ws.length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = ws[j]?)
    (htop : iwTop m' = iwTop m + ws.length) (j : Nat) (hj : j < ws.length) (hw : H (ws[j]'hj)) :
    StabD (fun m => (iwH m (q.toNat + j) : Option (Idx kk))) m' (decI (ws[j]'hj)) := by
  subst hq
  have hlt : (rdW (m.arr64 CTL) 200).toNat + j < iwTop m' := by rw [htop]; simp [iwTop]; omega
  refine StabD.of_eq (fun m'' hg => iwH_grow hg hlt) ?_
  simp [iwH, hd?, iwA, hget j hj, List.getElem?_eq_getElem hj, hw]

theorem decCS_minor_stab {m : Mem} {q c o l : Nat} {cn : NIdx} {ihs : List (Nat × Nat)}
    (h0 : StabD (fun m => iwN m q) m 1) (h1 : StabD (fun m => iwN m (q + 1)) m c)
    (h2 : StabD (fun m => (iwH m (q + 2) : Option NIdx)) m cn)
    (h3 : StabD (fun m => iwN m (q + 3)) m o) (h4 : StabD (fun m => iwN m (q + 4)) m l)
    (hs : SPL decNN m o l ihs) : StabD (fun m => decCS m q) m (.minor c cn ihs) := by
  intro m' hg
  have e4 : iwN m' (q + 3 + 1) = some l := h4 m' hg
  simp [decCS, decAt, h0 m' hg, h1 m' hg, h2 m' hg, h3 m' hg, e4, (hs.grow hg).decPL]

/-- The twin's `classReadMinor` from the conclusion's head on. -/
def minorFin (nP : Nat) (motPos : List Nat) (d c : Nat) (fvs : List EIdx) (hd : EIdx) :
    AM (Option ClassSlot) :=
  if (hd.tag == ETag.const) = true then do
    match ← viewConst hd with
    | none => failDanglingE
    | some (cn, _) => do
      let ihs ← fvs.filterMapM (ihStep nP motPos d)
      pure (some (.minor c cn ihs))
  else pure none

/-- A slot read off a binder: `none`, or a stably decoding slot record. -/
def decSlot (m' : Mem) (r : List Word) : Option ClassSlot → Prop
  | none => r.headD 0 = 0
  | some s => r.headD 0 = 1 ∧ StabD (fun m => decCS m (r.tail.headD 0).toNat) m' s

theorem finW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d fo fl hd c : Word) (motPos : List Nat) (fvs : List EIdx)
    (hS : StageR vis fe m a) (hH : H hd) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hft : fo.toNat + fl.toNat ≤ iwTop m) (hmot : decNL m mo.toNat ml.toNat = some motPos)
    (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (finW n m nP mo ml d fo fl hd c) (minorFin nP.toNat motPos d.toNat c.toNat fvs (decI hd)) a
      (KP dn vis fe m decSlot) := by
  sorry

/-! ## The callees that keep `AbsOK` -/

theorem pirF_afrR {m m' : Mem} {args r : List Word} (h : pirF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (pirF_frame h)

/-- (`IndRealAbsPos`' `piBW_afr`, here for the `class_read` chain.) -/
theorem piBW_afrR : ∀ (n : Nat) (m m' : Mem) (fuel h : Word) (r : List Word), piBW n m fuel h = some (r, m') →
    AFr m m'
  | 0, _, _, _, _, _, hh => by simp [piBW] at hh
  | n + 1, m, m', fuel, h, r, hh => by
    simp only [piBW, piBK1, piBK2.eq_def, piBK3.eq_def] at hh
    afr_auto hh [piBW_afrR n _ _ _ _ _, consW_afr]

theorem ih1W_afr {n : Nat} {m m' : Mem} {nP mo ml d x : Word} {r : List Word}
    (h : ih1W n m nP mo ml d x = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [ih1W] at h
  simp only [ih1W, ih1W.k_fvar_type_d.eq_def, ih1W.k_pi_result_f.eq_def, ih1W.k_fvar_head.eq_def,
    ih1W.k_class_of_motive_var.eq_def, ih1W.k_get_app_args_f.eq_def, ih1W.k_fvar_head_2.eq_def] at h
  afr_auto h [ftdF_afr, pirF_afrR, fvarHeadW_afr, gaaF_afr]

theorem ihsW_afr : ∀ (n : Nat) (m m' : Mem) (nP mo ml d fo fl : Word) (r : List Word),
    ihsW n m nP mo ml d fo fl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [ihsW] at h
  | n + 1, m, m', nP, mo, ml, d, fo, fl, r, h => by
    simp only [ihsW, ihsW.k_class_read_minor_ih1.eq_def, ihsW.k_class_read_minor_ihs.eq_def, ihsW.k_rec2.eq_def, ihsW.k_sl_cons.eq_def] at h
    afr_auto h [ih1W_afr, ihsW_afr n _ _ _ _ _ _ _ _ _, recW_afr, consW_afr]

theorem finW_afr {n : Nat} {m m' : Mem} {nP mo ml d fo fl hd c : Word} {r : List Word}
    (h : finW n m nP mo ml d fo fl hd c = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [finW] at h
  simp only [finW, finW.k_class_read_minor_ihs.eq_def, finW.k_rec5.eq_def] at h
  afr_auto h [ihsW_afr n _ _ _ _ _ _ _ _ _, recW_afr]

theorem tailW_afr {n : Nat} {m m' : Mem} {nP mo ml d fo fl concl c : Word} {r : List Word}
    (h : tailW n m nP mo ml d fo fl concl c = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [tailW] at h
  simp only [tailW, tailW.k_get_app_args_f.eq_def, tailW.k_get_app_fn_f.eq_def,
    tailW.k_class_read_minor_finish.eq_def] at h
  afr_auto h [gaaF_afr, gafF_afr, finW_afr]

/-! ## `class_read_minor_tail`, `class_read_minor` -/

/-- The twin's `classReadMinor` from the class on. -/
def minorTail (nP : Nat) (motPos : List Nat) (d c : Nat) (fvs : List EIdx) (concl : EIdx) :
    AM (Option ClassSlot) := do
  let args ← getAppArgs coreWalkFuel concl
  match args.getLast? with
  | none => pure none
  | some last => do
    let hd ← getAppFn coreWalkFuel last
    minorFin nP motPos d c fvs hd

theorem decSlot_pair {m : Mem} {r : List Word} {x : Option ClassSlot} (h : decSlot m r x) :
    decSlot m [r.headD 0, r.tail.headD 0] x := by
  cases x with
  | none => exact h
  | some s => exact h

theorem tailW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d fo fl concl c : Word) (motPos : List Nat) (fvs : List EIdx)
    (hS : StageR vis fe m a) (hH : H concl) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hft : fo.toNat + fl.toNat ≤ iwTop m) (hmot : decNL m mo.toNat ml.toNat = some motPos)
    (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (tailW n m nP mo ml d fo fl concl c)
      (minorTail nP.toNat motPos d.toNat c.toNat fvs (decI concl)) a (KP dn vis fe m decSlot) := by
  sorry

theorem minorW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d dom : Word) (motPos : List Nat) (hS : StageR vis fe m a) (hJ : J m)
    (hH : H dom)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (minorW cR n m nP mo ml d dom) (ConRon.Arena.classReadMinor nP.toNat motPos d.toNat (decI dom)) a
      (fun b a' x => KP dn vis fe m decSlot b a' x ∧ J b.2) := by
  sorry

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/- ronsync2 stage 2: commented out (statement at the old twin/L)
l_model classReadSlotMotive_spec (p : Prog) (hP : SlotProg p)
  fns [hP.smot ↦ slotMotW list]
  specs [piBinders_spec p hP.a hP.c hP.v hP.sc hP.pb n, gafF_spec p hP.ad n,
    gaaF_spec p hP.ad n, eView_spec p hP.v n,
    classNPcOf_spec p hP.a hP.mc hP.mn hP.ct hP.x hP.g hP.ef hP.npc n,
    rec4_specW p hP.a n hP.r4, rec2_specW p hP.a n hP.r2]
  grind [arena_grind]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- After `class_n_pc_of`: the join point of `cnt := min n al`. -/
theorem slotMotW_npc_some (iName us ao al : Word) (r : List Word) (m : Mem) :
    slotMotW.k_class_n_pc_of iName us ao al (some (r, m)) =
      slotMotW.k_rec4 (recW m 4 [iName, us, ao, if r.headD 0 < al then r.headD 0 else al]) := by
  by_cases h : r.headD 0 < al
  · rw [slotMotW.k_class_n_pc_of.arm1 (hc1 := h), slotMotW.j1, ite_eq_left h]
  · rw [slotMotW.k_class_n_pc_of.arm2 (hc1 := h), slotMotW.j1, ite_eq_right h]
-/

def slK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
def slK1 (cR : CallM) (n : Nat) (p vis np mo ml d dom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if tagW (r1.headD 0) = 2 then slK2 (slotMotW n m1 p vis dom)
    else slK2 (minorW cR n m1 np mo ml d dom)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `class_read_slot`.** -/
def slotW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, p, vis, np, mo, ml, d, dom => slK1 cR n p vis np mo ml d dom (pirF m [CWF, dom])
-/

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (p vis np mo ml d dom mdom iName us ao al : Word)
  (r r1 r2 r3 r4 r5 r6 : List Word) (cR : CallM)
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotW_eq : slotW cR (n + 1) m p vis np mo ml d dom =
    slK1 cR n p vis np mo ml d dom (pirF m [CWF, dom]) := rfl
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slK1_mot (h : tagW (r1.headD 0) = 2) : slK1 cR n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (slotMotW n m1 p vis dom) := by rw [slK1, ite_eq_left h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slK1_min (h : ¬ tagW (r1.headD 0) = 2) : slK1 cR n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (minorW cR n m1 np mo ml d dom) := by rw [slK1, ite_eq_right h]
-/
theorem slK2_some : slK2 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms

-- ronsync2 stage 2: grind_pattern [ind_grind] slotW_eq => slotW cR (n + 1) m p vis np mo ml d dom
-- ronsync2 stage 2: grind_pattern [ind_grind] slK1_mot => slK1 cR n p vis np mo ml d dom (some (r1, m1))
-- ronsync2 stage 2: grind_pattern [ind_grind] slK1_min => slK1 cR n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK2_some => slK2 (some (r, m))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem classReadSlot_spec (p : Prog) (hP : SlotProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat)
    (s₀ : St) (q vis np mo ml d dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_slot" [q, vis, np, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ slotW cR n s₀.mem q vis np mo ml d dom = some (r, s'.mem); ⊤⦄ := by
  sorry
-/

/-! ## Relational lemmas -/

theorem tag_beq (e : Word) (hh : H e) (t : UInt32) (k : Nat) (hk : k < 16) (ht : t = UInt32.ofNat k) :
    (((decI e : EIdx).tag == t) = true) ↔ tagW e = UInt64.ofNat k := by
  subst ht
  have := decE_tag_eq e hh k hk
  simp only [beq_iff_eq]; exact this

theorem decCS_motive_stab {m : Mem} {q kp : Nat} {key : ClassKey}
    (h0 : StabD (fun m => iwN m q) m 0) (h1 : StabD (fun m => iwN m (q + 1)) m kp)
    (hk : StabD (fun m => decCK m kp) m key) : StabD (fun m => decCS m q) m (.motive key) := by
  intro m' hg
  simp [decCS, h0 m' hg, h1 m' hg, hk m' hg]

/-- The twin's `classReadSlot` motive arm. -/
def slotMot (bs : BlockShape) (fe : IFEnv) (dom : EIdx) : AM (Option ClassSlot) := do
  let (bss, _) ← ConRon.Arena.piBinders coreWalkFuel dom
  match bss.getLast? with
  | none => pure none
  | some mdom => do
    let hd ← getAppFn coreWalkFuel mdom
    if hd.tag == ETag.const then
      match ← viewConst hd with
      | none => failDanglingE
      | some (iName, us) => do
        let args ← getAppArgs coreWalkFuel mdom
        let n := ConRon.Arena.classNPcOf bs fe iName
        pure (some (.motive ⟨iName, us, args.take n⟩))
    else pure none

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotMotW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (p dom : Word) (bs : BlockShape) (hS : StageR vis fe m a) (hH : H dom)
    (hb : BSOK m p.toNat bs) :
    RSim (slotMotW n m p vis dom) (slotMot bs fe (decI dom)) a (KP dn vis fe m decSlot) := by
  rcases n with _ | n
  · exact RSim.none
  rw [slotMotW.arm1]
  refine RSim.bind (K := slotMotW.k_pi_binders n p vis) rfl (simPiBinders n hS hH) ?_
  rintro ⟨r1, m1⟩ ⟨bss, e⟩ a1 - ⟨hS1, hg1, hd1, ht1⟩
  dsimp only at hS1 hg1 hd1 ht1
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m1 ≤ (m1.arr64 IW).size := hS1.iw.iw
    have h2 : (m1.arr64 IW).size < 2 ^ 64 := hS1.iw.iwSize
    omega
  by_cases hz : r1.tail.headD 0 = 0
  · rw [slotMotW.k_pi_binders.arm1 (hc1 := hz)]
    have hnil : bss = [] := by
      have := decHL_length m1 hd1; rw [hz] at this; exact List.eq_nil_of_length_eq_zero this
    subst hnil
    exact RSim.pure_some ⟨hS1, hg1, rfl⟩
  obtain ⟨w, hw, hwH, hlast⟩ := decHL_last hd1 hz hb1
  rw [slotMotW.k_pi_binders.arm2 (hc1 := hz), hw]
  simp only []
  rw [hlast]
  refine RSim.bind (K := slotMotW.k_get_app_fn_f n p vis w) rfl (simGetAppFn hS1 hwH) ?_
  rintro ⟨r2, m2⟩ hd a2 - ⟨hS2, hg2, hb2, rfl⟩
  dsimp only at hS2 hg2 hb2
  have hg12 := hg1.trans hg2
  by_cases hg : tagW (r2.headD 0) ≠ 3
  · rw [slotMotW.k_get_app_fn_f.arm1 (hc1 := hg)]
    have ht : ¬ (((decI (r2.headD 0) : EIdx)).tag == ETag.const) = true :=
      fun e => hg ((tag_beq _ hb2 _ 3 (by decide) rfl).mp e)
    rw [ite_eq_right ht]
    exact RSim.pure_some ⟨hS2, hg12, rfl⟩
  by_cases hne : eViewW m2 (r2.headD 0) = []
  · rw [slotMotW.k_get_app_fn_f.abort1 (hc1 := Decidable.of_not_not hg) (hc2 := hne)]; exact RSim.none
  rw [slotMotW.k_get_app_fn_f.arm2 (hc1 := Decidable.of_not_not hg) (hc2 := hne)]
  have hg3 : tagW (r2.headD 0) = 3 := by simpa using hg
  have ht : (((decI (r2.headD 0) : EIdx)).tag == ETag.const) = true :=
    (tag_beq _ hb2 _ 3 (by decide) rfl).mpr hg3
  obtain ⟨hvc, hnH, huH⟩ := viewConstW hS2.check.arena.base hne hg3
  rw [ite_eq_left ht]
  refine RSim.tstep hvc ?_
  refine RSim.bind (K := slotMotW.k_get_app_args_f n p vis ((eViewW m2 (r2.headD 0)).tail.headD 0)
    ((eViewW m2 (r2.headD 0)).tail.tail.headD 0)) rfl (simGetAppArgs hS2 hwH) ?_
  rintro ⟨r3, m3⟩ args a3 - ⟨hS3, hg3', hd3, ht3⟩
  dsimp only at hS3 hg3' hd3 ht3
  simp only [Nat.zero_add, getD_zero, getD_one] at hd3 ht3
  have hg13 := hg12.trans hg3'
  rw [slotMotW.k_get_app_args_f.arm1]
  refine RSim.lstep (K := slotMotW.k_class_n_pc_of _ _ (r3.headD 0) (r3.tail.headD 0)) rfl ?_
  rintro ⟨r4, m4⟩ h4
  obtain ⟨hS4, hg4, rfl, hN⟩ := npcW_ok h4 hS3 (hb.grow hg13) hnH
  rw [slotMotW_npc_some]
  simp only [List.headD_cons]
  generalize hNd : ConRon.Arena.classNPcOf bs fe (decI ((eViewW m2 (r2.headD 0)).tail.headD 0)) = N at hN ⊢
  refine RSim.lstep (K := slotMotW.k_rec4) rfl ?_
  rintro ⟨r5, m5⟩ h5
  obtain ⟨hS5, hg5, hr5, hget5, htop5⟩ := recW_stage h5 hS4 rfl
  rw [slotMotW.k_rec4.arm1, hr5]
  simp only [List.headD_cons]
  refine RSim.lstep (K := slotMotW.k_rec2) rfl ?_
  rintro ⟨r6, m6⟩ h6
  obtain ⟨hS6, hg6, hr6, hget6, htop6⟩ := recW_stage h6 hS5 rfl
  rw [slotMotW.k_rec2.arm1, hr6]
  refine RSim.pure_some ⟨hS6, ((hg13.trans hg4).trans hg5).trans hg6, rfl, ?_⟩
  simp only [List.headD_cons, List.tail_cons]
  have hlen3 := decHL_length m3 hd3
  have hds : decHL m3 (r3.headD 0).toNat (min N (r3.tail.headD 0).toNat) = some (args.take N) := by
    rw [decHL_take hd3 _ (Nat.min_le_right _ _)]
    congr 1; rw [List.take_eq_take_iff]; simp [hlen3]
  have hq5 : rdW (m4.arr64 CTL) 200 = rdW (m4.arr64 CTL) 200 := rfl
  have k0 := rec_iwH_stab (kk := IdxKind.name) hq5 hget5 htop5 0 (by simp) hnH
  have k1 := rec_iwH_stab (kk := IdxKind.levels) hq5 hget5 htop5 1 (by simp) huH
  have k2 := rec_iwN_stab hq5 hget5 htop5 2 (by simp)
  have k3 := rec_iwN_stab hq5 hget5 htop5 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at k0 k1 k2 k3
  replace k3 : StabD (fun m => iwN m ((rdW (m4.arr64 CTL) 200).toNat + 3)) m5
      (min N (r3.tail.headD 0).toNat) := by
    refine fun m' hg => (k3 m' hg).trans (congrArg some ?_)
    by_cases h : UInt64.ofNat N < r3.tail.headD 0
    · simp only [h, ite_true]
      have := UInt64.lt_iff_toNat_lt.mp h
      rw [UInt64.toNat_ofNat_of_lt' hN] at this ⊢; omega
    · simp only [h, ite_false]
      have : ¬ N < (r3.tail.headD 0).toNat := fun e => h (UInt64.lt_iff_toNat_lt.mpr
        (by rw [UInt64.toNat_ofNat_of_lt' hN]; exact e))
      omega
  have hdsS : StabD (fun m => (decHL m (r3.headD 0).toNat (min N (r3.tail.headD 0).toNat) :
      Option (List EIdx))) m5 (args.take N) := by
    refine StabD.of_eq (fun m'' hg => decHL_grow hg ?_) ?_
    · have := Nat.min_le_right N (r3.tail.headD 0).toNat
      have := Nat.le_trans ht3 ((hg4.trans hg5).1); omega
    · rw [decHL_grow (hg4.trans hg5) (by have := Nat.min_le_right N (r3.tail.headD 0).toNat; omega)]
      exact hds
  have hkey : StabD (fun m => decCK m (rdW (m4.arr64 CTL) 200).toNat) m5
      ⟨decI ((eViewW m2 (r2.headD 0)).tail.headD 0), decI ((eViewW m2 (r2.headD 0)).tail.tail.headD 0),
        args.take N⟩ := by
    intro m' hg
    have e3 : iwN m' ((rdW (m4.arr64 CTL) 200).toNat + 2 + 1) = some (min N (r3.tail.headD 0).toNat) :=
      k3 m' hg
    simp only [decCK, decAt, k0 m' hg, k1 m' hg, k2 m' hg, e3, Option.bind_eq_bind, Option.bind_some, hdsS m' hg]; rfl
  have hq6 : rdW (m5.arr64 CTL) 200 = rdW (m5.arr64 CTL) 200 := rfl
  have j0 := rec_iwN_stab hq6 hget6 htop6 0 (by simp)
  have j1 := rec_iwN_stab hq6 hget6 htop6 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at j0 j1
  exact decCS_motive_stab j0 j1 (hkey.grow hg6)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem envFindW_afrR {m m' : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m')) :
    AFr m m' := by
  unfold envFindW at h
  afr_auto h []
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem npcW_afr {n : Nat} {m m' : Mem} {p vis i : Word} {r : List Word}
    (h : npcW n m p vis i = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [npcW] at h
  simp only [npcW, npcK1.eq_def, npcK2.eq_def, npcK3.eq_def] at h
  afr_auto h [memberNamesW_afr, envFindW_afrR]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotMotW_afr {n : Nat} {m m' : Mem} {p vis dom : Word} {r : List Word}
    (h : slotMotW n m p vis dom = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [slotMotW] at h
  simp only [slotMotW, slotMotW.k_pi_binders.eq_def, slotMotW.k_get_app_fn_f.eq_def,
    slotMotW.k_get_app_args_f.eq_def, slotMotW.k_class_n_pc_of.eq_def, slotMotW.j1, slotMotW.k_rec4.eq_def,
    slotMotW.k_rec2.eq_def] at h
  afr_auto h [piBW_afrR _ _ _ _ _ _, gafF_afr, gaaF_afr, npcW_afr, recW_afr]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (n : Nat) (m : Mem)
    (a : AState) (p np mo ml d dom : Word) (bs : BlockShape) (motPos : List Nat)
    (hS : StageR vis fe m a) (hJ : J m) (hH : H dom) (hb : BSOK m p.toNat bs)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (slotW cR n m p vis np mo ml d dom)
      (ConRon.Arena.classReadSlot bs fe np.toNat motPos d.toNat (decI dom)) a
      (fun b a' x => KP dn vis fe m decSlot b a' x ∧ J b.2) := by
  sorry
-/

end L.Ind

end

end

section

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
  grind [arena_grind]

theorem snocW_room {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word}
    (h : snocW n m o l x = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m) {xs : List Nat}
    (hxs : decNL m o.toNat l.toNat = some xs) : iwTop m' ≤ (m'.arr64 IW).size := by
  obtain ⟨-, -, -, hf, -, htop⟩ := snocW_decN h hsz hc hsrc hxs
  rw [hf.size IW]
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
    (h : motSnocW N m mo ml np d = some (r, m')) (hS : StageR vis fe m a)
    (hsrc : mo.toNat + ml.toNat ≤ iwTop m) (hxs : decNL m mo.toNat ml.toNat = some xs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ [d.toNat - np.toNat]) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  sorry

mutual
/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `class_read_slots`.** -/
def slotsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | N + 1, m, p, vis, np, n, mo, ml, d, e =>
    if n = 0 then some ([1, 0, 0], m)
    else if tagW e ≠ 6 then some ([0, 0, 0], m)
    else if eViewW m e = [] then none
    else ssK1 cR N p vis np n mo ml d ((eViewW m e).tail.headD 0) ((eViewW m e).tail.tail.headD 0)
      (slotW cR N m p vis np mo ml d ((eViewW m e).tail.headD 0))
-/

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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `class_read_slots_next`.** -/
def nextW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | N + 1, m, p, vis, np, n, mo, ml, d, dom, body, slot =>
    if rdW (m.arr64 IW) slot = 0 then
      ssK2 cR N p vis np n d dom body slot (motSnocW N m mo ml np d)
    else ssK3 cR N p vis np n d dom body slot mo ml m
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- After `sl_snoc`. -/
def ssK2 (cR : CallM) (N : Nat) (p vis np n d dom body slot : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ssK3 cR N p vis np n d dom body slot (r2.headD 0) (r2.tail.headD 0) m2
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `intern_fvar`. -/
def ssK3 (cR : CallM) (N : Nat) (p vis np n d dom body slot mo2 ml2 : Word) (m2 : Mem) : Option (List Word × Mem) :=
  ssK4 cR N p vis np n d body slot mo2 ml2 (fvinternW m2 d dom)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- After `intern_fvar`. -/
def ssK4 (cR : CallM) (N : Nat) (p vis np n d body slot mo2 ml2 : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (fv, m3) =>
    if 4294967296 ≤ fv then none
    else ssK5 cR N p vis np n d slot mo2 ml2 (i1F m3 [CWF, body, fv, 0])
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- After `instantiate1_fast`. -/
def ssK5 (cR : CallM) (N : Nat) (p vis np n d slot mo2 ml2 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ssK6 N slot (slotsW cR N m4 p vis np (n - 1) mo2 ml2 (d + 1) (r4.headD 0))
-/

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
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotsW_zero (h : n = 0) : slotsW cR (N + 1) m p vis np n mo ml d e = some ([1, 0, 0], m) := by
  rw [slotsW, ite_eq_left h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotsW_tag (h : n ≠ 0) (h2 : tagW e ≠ 6) :
    slotsW cR (N + 1) m p vis np n mo ml d e = some ([0, 0, 0], m) := by
  rw [slotsW, ite_eq_right h, ite_eq_left h2]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotsW_nil (h : n ≠ 0) (h2 : ¬ tagW e ≠ 6) (h3 : eViewW m e = []) :
    slotsW cR (N + 1) m p vis np n mo ml d e = none := by
  rw [slotsW, ite_eq_right h, ite_eq_right h2, ite_eq_left h3]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotsW_ok (h : n ≠ 0) (h2 : ¬ tagW e ≠ 6) (h3 : eViewW m e ≠ []) :
    slotsW cR (N + 1) m p vis np n mo ml d e =
      ssK1 cR N p vis np n mo ml d ((eViewW m e).tail.headD 0) ((eViewW m e).tail.tail.headD 0)
        (slotW cR N m p vis np mo ml d ((eViewW m e).tail.headD 0)) := by
  rw [slotsW, ite_eq_right h, ite_eq_right h2, ite_eq_right h3]
-/
theorem ssK1_fail (h : r1.headD 0 = 0) : ssK1 cR N p vis np n mo ml d dom body (some (r1, m1)) =
    some ([0, 0, 0], m1) := by rw [ssK1, ite_eq_left h]
theorem ssK1_ok (h : r1.headD 0 ≠ 0) : ssK1 cR N p vis np n mo ml d dom body (some (r1, m1)) =
    ssK1b (nextW cR N m1 p vis np n mo ml d dom body (r1.tail.headD 0)) := by rw [ssK1, ite_eq_right h]
theorem ssK1b_some : ssK1b (some (r1, m1)) =
    some ([r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0], m1) := by rw [ssK1b]
theorem nextW_mot (h : rdW (m.arr64 IW) slot = 0) : nextW cR (N + 1) m p vis np n mo ml d dom body slot =
    ssK2 cR N p vis np n d dom body slot (motSnocW N m mo ml np d) := by
  rw [nextW, ite_eq_left h]
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nextW_min (h : rdW (m.arr64 IW) slot ≠ 0) : nextW cR (N + 1) m p vis np n mo ml d dom body slot =
    ssK3 cR N p vis np n d dom body slot mo ml m := by
  rw [nextW, ite_eq_right h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem ssK2_some : ssK2 cR N p vis np n d dom body slot (some (r2, m2)) =
    ssK3 cR N p vis np n d dom body slot (r2.headD 0) (r2.tail.headD 0) m2 := by rw [ssK2]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem ssK3_eq : ssK3 cR N p vis np n d dom body slot mo2 ml2 m2 =
    ssK4 cR N p vis np n d body slot mo2 ml2 (fvinternW m2 d dom) := by rw [ssK3]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem ssK4_big (h : 4294967296 ≤ fv) : ssK4 cR N p vis np n d body slot mo2 ml2 (some (fv, m3)) = none := by
  rw [ssK4, ite_eq_left h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem ssK4_ok (h : ¬ 4294967296 ≤ fv) : ssK4 cR N p vis np n d body slot mo2 ml2 (some (fv, m3)) =
    ssK5 cR N p vis np n d slot mo2 ml2 (i1F m3 [CWF, body, fv, 0]) := by
  rw [ssK4, ite_eq_right h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem ssK5_some : ssK5 cR N p vis np n d slot mo2 ml2 (some (r4, m4)) =
    ssK6 N slot (slotsW cR N m4 p vis np (n - 1) mo2 ml2 (d + 1) (r4.headD 0)) := by rw [ssK5]
-/
theorem ssK6_fail (h : r5.headD 0 = 0) : ssK6 N slot (some (r5, m5)) = some ([0, 0, 0], m5) := by
  rw [ssK6, ite_eq_left h]
theorem ssK6_ok (h : r5.headD 0 ≠ 0) : ssK6 N slot (some (r5, m5)) =
    ssK7 (consW N m5 slot (r5.tail.headD 0) (r5.tail.tail.headD 0)) := by rw [ssK6, ite_eq_right h]
theorem ssK7_some : ssK7 (some (r6, m6)) = some ([1, r6.headD 0, r6.tail.headD 0], m6) := by rw [ssK7]
end arms

-- ronsync2 stage 2: grind_pattern [ind_grind] slotsW_zero => slotsW cR (N + 1) m p vis np n mo ml d e
-- ronsync2 stage 2: grind_pattern [ind_grind] slotsW_tag => slotsW cR (N + 1) m p vis np n mo ml d e
-- ronsync2 stage 2: grind_pattern [ind_grind] slotsW_nil => slotsW cR (N + 1) m p vis np n mo ml d e
-- ronsync2 stage 2: grind_pattern [ind_grind] slotsW_ok => slotsW cR (N + 1) m p vis np n mo ml d e
grind_pattern [ind_grind] ssK1_fail => ssK1 cR N p vis np n mo ml d dom body (some (r1, m1))
grind_pattern [ind_grind] ssK1_ok => ssK1 cR N p vis np n mo ml d dom body (some (r1, m1))
grind_pattern [ind_grind] ssK1b_some => ssK1b (some (r1, m1))
grind_pattern [ind_grind] nextW_mot => nextW cR (N + 1) m p vis np n mo ml d dom body slot
grind_pattern [ind_grind] nextW_min => nextW cR (N + 1) m p vis np n mo ml d dom body slot
grind_pattern [ind_grind] ssK2_some => ssK2 cR N p vis np n d dom body slot (some (r2, m2))
-- ronsync2 stage 2: grind_pattern [ind_grind] ssK3_eq => ssK3 cR N p vis np n d dom body slot mo2 ml2 m2
-- ronsync2 stage 2: grind_pattern [ind_grind] ssK4_big => ssK4 cR N p vis np n d body slot mo2 ml2 (some (fv, m3))
-- ronsync2 stage 2: grind_pattern [ind_grind] ssK4_ok => ssK4 cR N p vis np n d body slot mo2 ml2 (some (fv, m3))
-- ronsync2 stage 2: grind_pattern [ind_grind] ssK5_some => ssK5 cR N p vis np n d slot mo2 ml2 (some (r4, m4))
grind_pattern [ind_grind] ssK6_fail => ssK6 N slot (some (r5, m5))
grind_pattern [ind_grind] ssK6_ok => ssK6 N slot (some (r5, m5))
grind_pattern [ind_grind] ssK7_some => ssK7 (some (r6, m6))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, eView_spec p hP.v N,
        classReadSlot_spec p hP.toSlotProg cR hcR N, ih2]
      all_goals subst_vars
      all_goals (try simp only [LocEq] at *)
      all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, Nat.reduceEqDiff,
        reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
      all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5, loc_init6,
        loc_init7]
    · rw [invoke_eq _ hP.next]; simp only [callFn, classReadSlotsNext]
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec,
        classReadSlotsSnoc_spec p hP.a hP.c hP.sn hP.msn N, internFVar_spec p hP.ff hP.fp hP.ifv N,
        i1F_spec p hP.hi1 N, slCons_specW p hP.a hP.c hP.sc N, ih1]
      all_goals subst_vars
      all_goals (try simp only [LocEq] at *)
      all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
        reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
      all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5, loc_init6,
        loc_init7, loc_init8, loc_init9]
-/

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Relational lemma -/

theorem viewBindW {m : Mem} {a : AState} (hR : ArenaR m a) {w : Word} (hH : H w)
    (hne : eViewW m w ≠ []) (hg : tagW w = 6) :
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

theorem simInst1 (hS : StageR vis fe m a) {e v : Word} (he : H e) :
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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slotsRest_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (p np : Word)
    (bs : BlockShape) (N : Nat)
    (ih : ∀ (m : Mem) (a : AState) (n mo ml d e : Word) (motPos : List Nat),
      StageR vis fe m a → J m → H e → BSOK m p.toNat bs → decNL m mo.toNat ml.toNat = some motPos →
      mo.toNat + ml.toNat ≤ iwTop m → d.toNat + n.toNat < 2 ^ 64 →
      RSim (slotsW cR N m p vis np n mo ml d e)
        (ConRon.Arena.classReadSlots bs fe np.toNat n.toNat motPos d.toNat (decI e)) a
        (fun b a' x => KP dn vis fe m decSlots b a' x ∧ J b.2))
    (m0 m2 : Mem) (a2 : AState) (n d dom body slotw mo2 ml2 : Word) (k : Nat) (motPos' : List Nat)
    (slot : ClassSlot) (hS : StageR vis fe m2 a2) (hJ : J m2) (hg : IWGrow m0 m2) (hdom : H dom)
    (hbody : H body)
    (hb : BSOK m2 p.toNat bs) (hmot : decNL m2 mo2.toNat ml2.toNat = some motPos')
    (hmt : mo2.toNat + ml2.toNat ≤ iwTop m2) (hn : n.toNat = k + 1) (hd : d.toNat + n.toNat < 2 ^ 64)
    (hsl : StabD (fun m => decCS m slotw.toNat) m2 slot) :
    RSim (ssK3 cR N p vis np n d dom body slotw mo2 ml2 m2)
      (slotsRest bs fe np.toNat k motPos' d.toNat (decI dom) (decI body) slot) a2
      (fun b a' x => KP dn vis fe m0 decSlots b a' x ∧ J b.2) := by
  sorry
-/

/-- The twin's `classReadSlots` after the slot. -/
def slotsNext (bs : BlockShape) (fe : IFEnv) (np k : Nat) (motPos : List Nat) (d : Nat)
    (dom body : EIdx) (slot : ClassSlot) : AM (Option (List ClassSlot)) :=
  slotsRest bs fe np k (match slot with
    | .motive _ => motPos ++ [d - np]
    | .minor _ _ _ => motPos) d dom body slot

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem slots_sims (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (p np : Word)
    (bs : BlockShape) (N : Nat) :
    (∀ (m : Mem) (a : AState) (n mo ml d e : Word) (motPos : List Nat),
      StageR vis fe m a → J m → H e → BSOK m p.toNat bs → decNL m mo.toNat ml.toNat = some motPos →
      mo.toNat + ml.toNat ≤ iwTop m → d.toNat + n.toNat < 2 ^ 64 →
      RSim (slotsW cR N m p vis np n mo ml d e)
        (ConRon.Arena.classReadSlots bs fe np.toNat n.toNat motPos d.toNat (decI e)) a
        (fun b a' x => KP dn vis fe m decSlots b a' x ∧ J b.2)) ∧
    (∀ (m : Mem) (a : AState) (n mo ml d dom body slotw : Word) (motPos : List Nat) (k : Nat)
      (slot : ClassSlot),
      StageR vis fe m a → J m → H dom → H body → BSOK m p.toNat bs →
      decNL m mo.toNat ml.toNat = some motPos → mo.toNat + ml.toNat ≤ iwTop m →
      n.toNat = k + 1 → d.toNat + n.toNat < 2 ^ 64 → StabD (fun m => decCS m slotw.toNat) m slot →
      RSim (nextW cR N m p vis np n mo ml d dom body slotw)
        (slotsNext bs fe np.toNat k motPos d.toNat (decI dom) (decI body) slot) a
        (fun b a' x => KP dn vis fe m decSlots b a' x ∧ J b.2)) := by
  sorry
-/

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

l_model classReadMotPos_spec (p : Prog) (hP : ReadProg p)
  fns [hP.mp ↦ motPosW list]
  specs [slCons_specW p hP.a hP.c hP.sc n]
  grind [arena_grind]

def frK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([1, r3.headD 0], m3)

def frK2 (so sl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else frK3 (recW m2 4 [so, sl, r2.tail.headD 0, r2.tail.tail.headD 0])

def frK1 (cR : CallM) (N : Nat) (nP so sl ro rl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => frK2 so sl (crW cR N m1 nP (r1.headD 0) (r1.tail.headD 0) ro rl)

/-- **The model of `class_read_finish`.** -/
def readFinW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | N + 1, m, nP, so, sl, ro, rl => frK1 cR N nP so sl ro rl (motPosW N m so sl 0)

/-- **The model of `class_read_n_slots`**: `rP - nP`, truncated. -/
def tsubW (a b : Word) : Word := if b ≤ a then a - b else 0

def rdK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0, r3.tail.headD 0], m3)

def rdK2 (cR : CallM) (N : Nat) (nP ro rl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else rdK3 (readFinW cR N m2 nP (r2.tail.headD 0) (r2.tail.tail.headD 0) ro rl)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
def rdK1 (cR : CallM) (N : Nat) (p vis nP ro rl rc0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else rdK2 cR N nP ro rl (slotsW cR N m1 p vis nP (tsubW (rdW (m1.arr64 IW) (rc0 + 1)) nP) 0 0 nP
      (r1.tail.tail.tail.headD 0))
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `class_read`.** -/
def readW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | N + 1, m, p, vis, nP, ro, rl =>
    if rl = 0 then some ([0, 0], m)
    else rdK1 cR N p vis nP ro rl (rdW (m.arr64 IW) ro)
      (cR N "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0] m)
-/

/-! ## Arms -/

section arms
variable (N : Nat) (m m1 m2 m3 : Mem) (so sl j nP ro rl p vis rc0 a b : Word) (r r1 r2 r3 : List Word)
  (cR : CallM)
theorem readFinW_eq : readFinW cR (N + 1) m nP so sl ro rl = frK1 cR N nP so sl ro rl (motPosW N m so sl 0) := rfl
theorem frK1_some : frK1 cR N nP so sl ro rl (some (r1, m1)) =
    frK2 so sl (crW cR N m1 nP (r1.headD 0) (r1.tail.headD 0) ro rl) := rfl
theorem frK2_fail (h : r2.headD 0 = 0) : frK2 so sl (some (r2, m2)) = some ([0, 0], m2) := by
  rw [frK2, ite_eq_left h]
theorem frK2_ok (h : r2.headD 0 ≠ 0) : frK2 so sl (some (r2, m2)) =
    frK3 (recW m2 4 [so, sl, r2.tail.headD 0, r2.tail.tail.headD 0]) := by rw [frK2, ite_eq_right h]
theorem frK3_some : frK3 (some (r3, m3)) = some ([1, r3.headD 0], m3) := rfl
theorem tsubW_le (h : b ≤ a) : tsubW a b = a - b := by simp [tsubW, h]
theorem tsubW_gt (h : ¬ b ≤ a) : tsubW a b = 0 := by simp [tsubW, h]
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem readW_nil (h : rl = 0) : readW cR (N + 1) m p vis nP ro rl = some ([0, 0], m) := by
  simp [readW, h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem readW_ok (h : rl ≠ 0) : readW cR (N + 1) m p vis nP ro rl =
    rdK1 cR N p vis nP ro rl (rdW (m.arr64 IW) ro)
      (cR N "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0] m) := by
  simp [readW, h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem rdK1_fail (h : r1.headD 0 = 0) : rdK1 cR N p vis nP ro rl rc0 (some (r1, m1)) = some ([0, 0], m1) := by
  rw [rdK1, ite_eq_left h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem rdK1_ok (h : r1.headD 0 ≠ 0) : rdK1 cR N p vis nP ro rl rc0 (some (r1, m1)) =
    rdK2 cR N nP ro rl (slotsW cR N m1 p vis nP (tsubW (rdW (m1.arr64 IW) (rc0 + 1)) nP) 0 0 nP
      (r1.tail.tail.tail.headD 0)) := by rw [rdK1, ite_eq_right h]
-/
theorem rdK2_fail (h : r2.headD 0 = 0) : rdK2 cR N nP ro rl (some (r2, m2)) = some ([0, 0], m2) := by
  rw [rdK2, ite_eq_left h]
theorem rdK2_ok (h : r2.headD 0 ≠ 0) : rdK2 cR N nP ro rl (some (r2, m2)) =
    rdK3 (readFinW cR N m2 nP (r2.tail.headD 0) (r2.tail.tail.headD 0) ro rl) := by rw [rdK2, ite_eq_right h]
theorem rdK3_some : rdK3 (some (r3, m3)) = some ([r3.headD 0, r3.tail.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] readFinW_eq => readFinW cR (N + 1) m nP so sl ro rl
grind_pattern [ind_grind] frK1_some => frK1 cR N nP so sl ro rl (some (r1, m1))
grind_pattern [ind_grind] frK2_fail => frK2 so sl (some (r2, m2))
grind_pattern [ind_grind] frK2_ok => frK2 so sl (some (r2, m2))
grind_pattern [ind_grind] frK3_some => frK3 (some (r3, m3))
grind_pattern [ind_grind] tsubW_le => tsubW a b
grind_pattern [ind_grind] tsubW_gt => tsubW a b
-- ronsync2 stage 2: grind_pattern [ind_grind] readW_nil => readW cR (N + 1) m p vis nP ro rl
-- ronsync2 stage 2: grind_pattern [ind_grind] readW_ok => readW cR (N + 1) m p vis nP ro rl
-- ronsync2 stage 2: grind_pattern [ind_grind] rdK1_fail => rdK1 cR N p vis nP ro rl rc0 (some (r1, m1))
-- ronsync2 stage 2: grind_pattern [ind_grind] rdK1_ok => rdK1 cR N p vis nP ro rl rc0 (some (r1, m1))
grind_pattern [ind_grind] rdK2_fail => rdK2 cR N nP ro rl (some (r2, m2))
grind_pattern [ind_grind] rdK2_ok => rdK2 cR N nP ro rl (some (r2, m2))
grind_pattern [ind_grind] rdK3_some => rdK3 (some (r3, m3))

/-! ## Specs -/

theorem classReadFinish_spec (p : Prog) (hP : ReadProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat)
    (s₀ : St) (nP so sl ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read_finish" [nP, so, sl, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ readFinW cR N s₀.mem nP so sl ro rl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.rfin]; simp only [callFn, classReadFinish]
  rcases N with _ | N
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      classReadMotPos_spec p hP N,
      classReadRecCls_spec p hP.fh hP.v hP.f hP.cm hP.c hP.a hP.sc hP.rcl hP.ad cR hcR N,
      rec4_specW p hP.a N hP.r4] <;>
    finish (gen := 20) [rdW_eq]

theorem classReadNSlots_spec (p : Prog) (hP : ReadProg p) (N : Nat) (s₀ : St) (a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read_n_slots" [a, b]
    ⦃fun r s' => s' = s₀ ∧ r = [tsubW a b]; ⊤⦄ := by
  rw [invoke_eq _ hP.ns]; simp only [callFn, classReadNSlots]
  rcases N with _ | N
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
    finish (gen := 20)

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem classRead_spec (p : Prog) (hP : ReadProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat) (s₀ : St)
    (q vis nP ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read" [q, vis, nP, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ readW cR N s₀.mem q vis nP ro rl = some (r, s'.mem); ⊤⦄ := by
  sorry
-/

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Relational lemmas -/

/-- The motive test `classRead` filters the prefix positions by. -/
def motF (slots : List ClassSlot) (s : Nat) : Bool :=
  match slots[s]? with
  | some (.motive _) => true
  | _ => false

theorem SPL.get {α : Type} {dec : Mem → Nat → Option α} {m : Mem} {o l : Nat} {xs : List α}
    (h : SPL dec m o l xs) (j : Nat) (hj : j < l) :
    ∃ q, iwN m (o + j) = some q ∧ StabD (fun m => dec m q) m (xs[j]'(by rw [h.length]; exact hj)) := by
  obtain ⟨-, ps, hps, hf⟩ := h
  have hpl := decNL_length m hps
  have hq := mapM_opt_get (fun j => iwN m (o + j)) (List.range l) ps hps j (by simpa using hj)
  simp only [List.getElem_range] at hq
  exact ⟨ps[j]'(by omega), hq, FA2.get hf j (by omega) _⟩

theorem range'_filter_step (f : Nat → Bool) (j k : Nat) :
    (List.range' j (k + 1)).filter f = if f j then j :: (List.range' (j + 1) k).filter f
      else (List.range' (j + 1) k).filter f := by
  simp only [List.range'_succ, List.filter_cons]
  try (split <;> rfl)

theorem motPosW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (a : AState)
    (so sl : Word) (slots : List ClassSlot) (N : Nat) : ∀ (m m' : Mem) (j : Word) (r : List Word),
    motPosW N m so sl j = some (r, m') → StageR vis fe m a → SPL decCS m so.toNat sl.toNat slots →
    j.toNat ≤ sl.toNat →
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat =
        some ((List.range' j.toNat (sl.toNat - j.toNat)).filter (motF slots)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  sorry

/-- The twin's `classRead` after the slots. -/
def readFinTw (nP : Nat) (slots : List ClassSlot) (recs : List RecShape) : AM (Option ClassRead) := do
  match ← ConRon.Arena.classReadRecCls nP ((List.range slots.length).filter (motF slots)) recs with
  | none => pure none
  | some recCls => pure (some ⟨slots, recCls⟩)

theorem RecsDec.dec {m m' : Mem} {ro rl : Word} {recs : List RecShape} (h : RecsDec m ro rl recs)
    (hg : IWGrow m m') : decPL m' (decRS m') ro.toNat rl.toNat = some recs :=
  h.1.stab (OMono.decPL decRS_mono _ _) m' hg

theorem RecsDec.grow {m m' : Mem} {ro rl : Word} {recs : List RecShape} (h : RecsDec m ro rl recs)
    (hg : IWGrow m m') : RecsDec m' ro rl recs :=
  ⟨h.1.grow (OMono.decPL decRS_mono _ _) hg, h.2⟩

theorem motPosW_afr : ∀ (N : Nat) (m m' : Mem) (so sl j : Word) (r : List Word),
    motPosW N m so sl j = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [motPosW] at h
  | N + 1, m, m', so, sl, j, r, h => by
    simp only [motPosW, motPosW.k_class_read_mot_pos.eq_def, motPosW.k_sl_cons.eq_def] at h
    afr_auto h [motPosW_afr N _ _ _ _ _ _, consW_afr]

theorem readFinW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (N : Nat) (m : Mem)
    (a : AState) (nP so sl ro rl : Word) (slots : List ClassSlot) (recs : List RecShape)
    (hS : StageR vis fe m a) (hJ : J m) (hsp : SPL decCS m so.toNat sl.toNat slots)
    (hrecs : RecsDec m ro rl recs) :
    RSim (readFinW cR N m nP so sl ro rl) (readFinTw nP.toNat slots recs) a
      (fun b a' x => KP dn vis fe m decRead b a' x ∧ J b.2) := by
  sorry

theorem decRS_rP {m : Mem} {p : Nat} {R : RecShape} (h : decRS m p = some R) :
    ∃ q, iwN m p = some q ∧ decCVp m q = some R.cvR ∧ iwN m (p + 1) = some R.rP := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem readW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (N : Nat) (m : Mem)
    (a : AState) (p nP ro rl : Word) (bs : BlockShape) (recs : List RecShape)
    (hS : StageR vis fe m a) (hJ : J m) (hb : BSOK m p.toNat bs) (hrecs : RecsDec m ro rl recs) :
    RSim (readW cR N m p vis nP ro rl) (ConRon.Arena.classRead bs fe nP.toNat recs) a
      (fun b a' x => KP dn vis fe m decRead b a' x ∧ J b.2) := by
  sorry
-/

end L.Ind

namespace L.Ind

open L.Arena

/-- **`class_read` refines `classRead` and keeps `AbsOK`**: `classRead_refines` with the program's
own `open_pis_at_fvars_f` (`opfF_ok`), so the walk memos are well formed after (no `AbsKeep`
premise). -/
theorem classRead_refinesA (p : Prog) (hP : ReadProg p) (hOpf : OpfF p) (N : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q nP ro rl : Word)
    (bs : BlockShape) (recs : List RecShape) (hS : StageR vis fe s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hb : BSOK s₀.mem q.toNat bs) (hrecs : RecsDec s₀.mem ro rl recs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read" [q, vis, nP, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRead bs fe nP.toNat recs) a₀ ∧
      KP dn vis fe s₀.mem decRead (r, s'.mem) (AM.st (ConRon.Arena.classRead bs fe nP.toNat recs) a₀)
        (AM.res (ConRon.Arena.classRead bs fe nP.toNat recs) a₀) ∧ AbsOK s'.mem; ⊤⦄ := by
  sorry

end L.Ind

end

end
