import ConAgua.Arena.LdRd
import ConAgua.Arena.IndSumSpec.DecHLTake
import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RecClassSpec.ReadProg
import ConAgua.Arena.IndPartsSpec.BlockCounts
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

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
    cR N "open_pis_at_fvars_f" [k, e, i] m = some (r, m') → StageR dn vis fe m a → J m →
    ∃ x a', (openPisAtFvarsF k.toNat (decI e) i.toNat).run a = .ok (x, a') ∧
      KeepPost dn vis fe decOLE m m' a' r x ∧ J m'

/-- The program's own reading keeps `AbsOK` (`opfF_ok`). -/
theorem opfJ_real {p : Prog} (hOpf : OpfF p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) : OpfJ (realCall p) AbsOK dn vis fe :=
  ⟨fun _ _ h hA => h hA, fun N k e i he m m' a r h hS hA => by
    obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (opfF_spec p hOpf N _ [k, e, i]) h
    rw [hs] at hW
    exact opfF_ok dn vis fe k e i he m m' a r hW ⟨hS, hA⟩⟩

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
  induction n with
  | zero =>
    intro s₀ nP mo ml ro rl; rw [invoke_eq _ hp]; simp only [callFn, classReadRecCls]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP mo ml ro rl
    rw [invoke_eq _ hp]
    simp only [callFn, classReadRecCls]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hcR n "open_pis_at_fvars_f", fvarHead_spec p hfh hv had n,
        classOfMotiveVar_spec p hf hcm n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20) [rdW_eq]

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
  simp only [decRS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, rP, hrP, mI, hmI, tg, htg, rh, hrh, rfl⟩ := h
  exact ⟨q, hq, hcv, hmI⟩

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
    crW cR n m nP mo ml ro rl = some (r, m') → StageR dn vis fe m a → J m →
    decPL m (decRS m) ro.toNat rl.toNat = some recs →
    (∀ m1, IWGrow m m1 → decPL m1 (decRS m1) ro.toNat rl.toNat = some recs) →
    decNL m mo.toNat ml.toNat = some motPos → mo.toNat + ml.toNat ≤ iwTop m →
    ro.toNat + rl.toNat < 2 ^ 64 →
    ∃ res a', (ConRon.Arena.classReadRecCls nP.toNat motPos recs).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ CrRes m' r res ∧ J m' := by
  induction n with
  | zero => intro m m' a nP mo ml ro rl r recs motPos h; simp [crW] at h
  | succ n ih =>
    intro m m' a nP mo ml ro rl r recs motPos h hS hJ hrecs hstab hmot hmt hb
    by_cases hrl : rl = 0
    · rw [crW_nil cR n m nP mo ml ro rl hrl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hz : rl.toNat = 0 := by rw [hrl]; rfl
      rw [hz] at hrecs
      simp [decPL] at hrecs
      subst hrecs
      refine ⟨some [], a, rfl, hS, IWGrow.refl m, ?_, hJ⟩
      simp [CrRes, decNL]
    · obtain ⟨r1, hr1, hrl1⟩ := wordSucc_of_ne hrl
      rw [hr1] at hrecs
      obtain ⟨p0, rc, rest, rfl, hp0, hrc, hrest⟩ := decPL_cons hrecs
      obtain ⟨q, hq, hcv, hmIq⟩ := decRS_fields hrc
      have hro64 : ro.toNat < 2 ^ 64 := ro.toNat_lt
      have e0 : UInt64.ofNat ro.toNat = ro := UInt64.ofNat_toNat
      have hrd0 := iwN_rdW hp0 (by omega)
      rw [e0] at hrd0
      have hp0b : p0 < 2 ^ 64 := hrd0.2
      have hrdq := iwN_rdW hq (by omega)
      have hIW64 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
      have hrdm := iwN_off (k := 2) hmIq (by have := iwN_lt hmIq; omega)
      simp only [show UInt64.ofNat 2 = 2 from rfl] at hrdm
      obtain ⟨-, -, htyp⟩ := decCV_some (a := erA m) (q := q) hcv
      have hqb : q < 2 ^ 64 := hrdq.2
      have hE64 : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
      have hq3 : q + 3 < 2 ^ 64 := by
        rcases hw : (m.arr64 EREC)[q + 3]? with _ | w
        · simp [hd?, erA, hw] at htyp
        · have := (Array.getElem?_eq_some_iff.mp hw).1; omega
      obtain ⟨wt, hwt, hwtlt, hwtd⟩ := erH_rdW htyp hq3
      have hq3w : UInt64.ofNat q + 3 = UInt64.ofNat (q + 3) := by simp [UInt64.ofNat_add]
      have hguard : rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 2) + 1 ≠ 0 := by
        intro h0; rw [crW_big cR n m nP mo ml ro rl hrl h0] at h; cases h
      have hmIw : (UInt64.ofNat rc.mI + 1).toNat = rc.mI + 1 := by
        have h1 : rc.mI + 1 < 2 ^ 64 := by
          rw [hrd0.1, hrdm.2] at hguard
          have hlt : rc.mI < 2 ^ 64 := (iwN_rdW hmIq (by have := iwN_lt hmIq; omega)).2
          refine Nat.lt_of_not_ge fun hc => hguard ?_
          rw [show rc.mI = 2 ^ 64 - 1 by omega]; decide
        have hh : (UInt64.ofNat rc.mI).toNat = rc.mI := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
        rw [UInt64.toNat_add, hh]
        show (rc.mI + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt h1
      simp only [crW_cons cR n m nP mo ml ro rl hrl hguard, hrd0.1, hrdm.2, hrdq.1, hq3w, hwt] at h
      obtain ⟨⟨r1', m1⟩, hs, h⟩ := of_K h (by simp only [crK1])
      obtain ⟨res1, a1, hrun1, ⟨hS1, hg1, hdec1⟩, hJ1⟩ :=
        hO.2 n (UInt64.ofNat rc.mI + 1) wt 0 hwtlt m m1 a r1' hs hS hJ
      have hrun1' : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (res1, a1) := by
        rw [hmIw, hwtd] at hrun1; exact hrun1
      cases res1 with
      | none =>
        have h0 : r1'.headD 0 = 0 := hdec1
        rw [crK1, ite_eq_left h0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨none, a1, cr_fail1 nP.toNat motPos rc rest a a1 hrun1', hS1, hg1, rfl, hJ1⟩
      | some xl =>
        obtain ⟨xs, concl⟩ := xl
        obtain ⟨h1, -, hleaf⟩ := hdec1
        have h0 : r1'.headD 0 ≠ 0 := by rw [h1]; decide
        rw [crK1, ite_eq_right h0] at h
        have hleaf3 : r1'.tail.tail.tail.headD 0 = (r1'.drop 3).headD 0 := by
          rcases r1' with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
        rw [hleaf3] at h
        obtain ⟨hl1, hl2⟩ := hleaf
        obtain ⟨⟨r2, m2⟩, hf, h⟩ := of_K h (by simp only [crK2])
        obtain ⟨x, a2, hrun2, hS2, hg2, hr2, hxb⟩ :=
          fvarHeadW_ok dn vis fe m1 m2 a1 ((r1'.drop 3).headD 0) hl1 r2 hf hS1
        have hJ2 : J m2 := hO.1 _ _ (fvarHeadW_afr hf) hJ1
        have hrun2' : (ConRon.Arena.fvarHead concl) a1 = .ok (x, a2) := by rw [← hl2]; exact hrun2
        cases x with
        | none =>
          have hr20 : r2.headD 0 = 0 := by rw [hr2]; rfl
          rw [crK2, ite_eq_left hr20] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨none, a2, cr_fail2 nP.toNat motPos rc rest a a1 a2 xs concl hrun1' hrun2',
            hS2, hg1.trans hg2, rfl, hJ2⟩
        | some i =>
          have hi64 : i < 2 ^ 64 := hxb i rfl
          have hr20 : r2.headD 0 ≠ 0 := by rw [hr2]; show (1 : Word) ≠ 0; decide
          have hr2t : r2.tail.headD 0 = UInt64.ofNat i := by rw [hr2]; rfl
          rw [crK2, ite_eq_right hr20, hr2t] at h
          have hmot2 : decNL m2 mo.toNat ml.toNat = some motPos := by
            rw [decNL_grow (hg1.trans hg2) hmt]; exact hmot
          have hmlb : mo.toNat + ml.toNat < 2 ^ 64 := by
            have := hS2.2; have := hS.2.2.2.1; have := hS.2.1; omega
          obtain ⟨r3, hc, h⟩ := of_K h (by simp only [crK3])
          have hcm := cmvW_ok (n - 1) m2 nP mo ml (UInt64.ofNat i) r3 motPos hmot2 hmlb hc
          rw [UInt64.toNat_ofNat_of_lt' hi64] at hcm
          cases co : ConRon.Arena.classOfMotiveVar nP.toNat motPos i with
          | none =>
            rw [co] at hcm
            have hr30 : r3.headD 0 = 0 := by rw [hcm]; rfl
            rw [crK3, ite_eq_left hr30] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            exact ⟨none, a2, cr_fail3 nP.toNat motPos rc rest a a1 a2 xs concl i hrun1' hrun2' co,
              hS2, hg1.trans hg2, rfl, hJ2⟩
          | some cc =>
            rw [co] at hcm
            have hr30 : r3.headD 0 ≠ 0 := by rw [hcm]; show (1 : Word) ≠ 0; decide
            have hr3t : r3.tail.headD 0 = UInt64.ofNat cc := by rw [hcm]; rfl
            have hcc64 : cc < 2 ^ 64 := by
              have := cmv_lt _ _ _ _ co; have := decNL_length m2 hmot2; have := ml.toNat_lt; omega
            rw [crK3, ite_eq_right hr30, hr3t] at h
            obtain ⟨⟨r4, m4⟩, hr, h⟩ := of_K h rfl
            have hro1 : (ro + 1).toNat = ro.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
            have hrest' : ∀ m3, IWGrow m2 m3 → decPL m3 (decRS m3) (ro + 1).toNat (rl - 1).toNat = some rest := by
              intro m3 hg3
              have := hstab m3 ((hg1.trans hg2).trans hg3)
              rw [hr1] at this
              obtain ⟨p0', x', ys', heq, -, -, hrest''⟩ := decPL_cons this
              rw [hro1, hrl1, (List.cons.inj heq).2]; exact hrest''
            have hmt2 : mo.toNat + ml.toNat ≤ iwTop m2 := Nat.le_trans hmt (hg1.trans hg2).1
            have hb' : (ro + 1).toNat + (rl - 1).toNat < 2 ^ 64 := by rw [hro1, hrl1]; omega
            have hrest2 := hrest' m2 (IWGrow.refl m2)
            obtain ⟨res4, a4, hrun4, hS4, hg4, hres4, hJ4⟩ := ih m2 m4 a2 nP mo ml (ro + 1) (rl - 1) r4 rest
              motPos hr hS2 hJ2 hrest2 hrest' hmot2 hmt2 hb'
            have hg14 := (hg1.trans hg2).trans hg4
            cases res4 with
            | none =>
              have hr40 : r4.headD 0 = 0 := hres4
              rw [crK4, ite_eq_left hr40] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
              exact ⟨none, a4, cr_fail4 nP.toNat motPos rc rest a a1 a2 a4 xs concl i cc hrun1' hrun2' co hrun4,
                hS4, hg14, rfl, hJ4⟩
            | some cs =>
              obtain ⟨hr41, hdn4, hle4⟩ := hres4
              have hr40 : r4.headD 0 ≠ 0 := by rw [hr41]; decide
              rw [crK4, ite_eq_right hr40] at h
              obtain ⟨⟨r5, m5⟩, hcw, h⟩ := of_K h rfl
              rw [crK5_some] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
              obtain ⟨hS5, hg5, hdn5, htop5⟩ := consW_stageN hcw hS4 hle4 hdn4
              refine ⟨some (cc :: cs), a4, cr_ok nP.toNat motPos rc rest a a1 a2 a4 xs concl i cc cs
                hrun1' hrun2' co hrun4, hS5, hg14.trans hg5, ?_, hO.1 _ _ (consW_afr hcw) hJ4⟩
              refine ⟨rfl, ?_, ?_⟩
              · simpa [UInt64.toNat_ofNat_of_lt' hcc64] using hdn5
              · simpa using Nat.le_of_eq htop5

theorem mapM_decCVp_grow {m m' : Mem} (hg : IWGrow m m') :
    ∀ (ps : List Nat), (∀ q ∈ ps, CVExt m q) → ps.mapM (decCVp m') = ps.mapM (decCVp m)
  | [], _ => rfl
  | q :: ps, h => by
    simp only [List.mapM_cons]
    rw [decCVp_grow_r hg (h q (List.mem_cons_self ..)),
      mapM_decCVp_grow hg ps (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]

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
  grind [arena_grind] simp [rdW_eq, getElem_rdW']

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
  grind [arena_grind] simp [rdW_eq, getElem_rdW']

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
  grind [arena_grind] simp [rdW_eq]

section models2
variable (n : Nat) (nP mo ml d : Word)

def tK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) => some ([r7.headD 0, r7.tail.headD 0], m7)

def tK2 (fo fl c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => tK3 (finW n m6 nP mo ml d fo fl (r6.headD 0) c)

def tK1 (fo fl c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if r5.tail.headD 0 = 0 then some ([0, 0], m5)
    else tK2 n nP mo ml d fo fl c
      (gafF m5 [CWF, rdW (m5.arr64 IW) (r5.headD 0 + r5.tail.headD 0 - 1)])

end models2

/-- **The model of `class_read_minor_tail`.** -/
def tailW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, d, fo, fl, concl, c =>
    tK1 n nP mo ml d fo fl c (gaaF m [CWF, concl])

section models3
variable (n : Nat) (nP mo ml d : Word)

def mK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([r5.headD 0, r5.tail.headD 0], m5)

def mK4 (fo fl concl : Word) (m3 : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r4 =>
    if r4.headD 0 = 0 then some ([0, 0], m3)
    else mK5 (tailW n m3 nP mo ml d fo fl concl (r4.tail.headD 0))

def mK3 (fo fl concl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0, 0], m3)
    else mK4 n nP mo ml d fo fl concl m3 (cmvW (n - 1) m3 nP mo ml (r3.tail.headD 0))

def mK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0], m2)
    else mK3 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0)
      (fvarHeadW m2 (r2.tail.tail.tail.headD 0))

def mK1 (cR : CallM) (dom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => mK2 n nP mo ml d (cR n "open_pis_at_fvars_f" [r1.tail.headD 0, dom, d] m1)

end models3

/-- **The model of `class_read_minor`.** -/
def minorW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, d, dom => mK1 n nP mo ml d cR dom (piBW n m CWF dom)

/-! ## Arms (for `finish`) -/

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 : Mem) (nP mo ml d x fo fl hd c cn t rr dom concl : Word)
  (cR : CallM)
  (r1 r2 r3 r4 r5 r6 r7 : List Word)

theorem minorW_eq : minorW cR (n + 1) m nP mo ml d dom = mK1 n nP mo ml d cR dom (piBW n m CWF dom) := rfl
theorem mK1_some : mK1 n nP mo ml d cR dom (some (r1, m1)) =
    mK2 n nP mo ml d (cR n "open_pis_at_fvars_f" [r1.tail.headD 0, dom, d] m1) := rfl
theorem mK2_fail (h : r2.headD 0 = 0) : mK2 n nP mo ml d (some (r2, m2)) = some ([0, 0], m2) := by
  rw [mK2, ite_eq_left h]
theorem mK2_ok (h : r2.headD 0 ≠ 0) : mK2 n nP mo ml d (some (r2, m2)) =
    mK3 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0) (r2.tail.tail.tail.headD 0) (fvarHeadW m2 (r2.tail.tail.tail.headD 0)) := by
  rw [mK2, ite_eq_right h]
theorem mK3_fail (h : r3.headD 0 = 0) : mK3 n nP mo ml d fo fl concl (some (r3, m3)) = some ([0, 0], m3) := by
  rw [mK3, ite_eq_left h]
theorem mK3_ok (h : r3.headD 0 ≠ 0) : mK3 n nP mo ml d fo fl concl (some (r3, m3)) =
    mK4 n nP mo ml d fo fl concl m3 (cmvW (n - 1) m3 nP mo ml (r3.tail.headD 0)) := by rw [mK3, ite_eq_right h]
theorem mK4_fail (h : r4.headD 0 = 0) : mK4 n nP mo ml d fo fl concl m3 (some r4) = some ([0, 0], m3) := by
  rw [mK4, ite_eq_left h]
theorem mK4_ok (h : r4.headD 0 ≠ 0) : mK4 n nP mo ml d fo fl concl m3 (some r4) =
    mK5 (tailW n m3 nP mo ml d fo fl concl (r4.tail.headD 0)) := by rw [mK4, ite_eq_right h]
theorem mK5_some : mK5 (some (r5, m5)) = some ([r5.headD 0, r5.tail.headD 0], m5) := rfl
theorem tailW_eq : tailW (n + 1) m nP mo ml d fo fl concl c =
    tK1 n nP mo ml d fo fl c (gaaF m [CWF, concl]) := rfl
theorem tK1_fail (h : r5.tail.headD 0 = 0) : tK1 n nP mo ml d fo fl c (some (r5, m5)) = some ([0, 0], m5) := by
  rw [tK1, ite_eq_left h]
theorem tK1_ok (h : r5.tail.headD 0 ≠ 0) : tK1 n nP mo ml d fo fl c (some (r5, m5)) =
    tK2 n nP mo ml d fo fl c (gafF m5 [CWF, rdW (m5.arr64 IW) (r5.headD 0 + r5.tail.headD 0 - 1)]) := by
  rw [tK1, ite_eq_right h]
theorem tK2_some : tK2 n nP mo ml d fo fl c (some (r6, m6)) =
    tK3 (finW n m6 nP mo ml d fo fl (r6.headD 0) c) := rfl
theorem tK3_some : tK3 (some (r7, m7)) = some ([r7.headD 0, r7.tail.headD 0], m7) := rfl
end arms

grind_pattern [ind_grind] minorW_eq => minorW cR (n + 1) m nP mo ml d dom
grind_pattern [ind_grind] mK1_some => mK1 n nP mo ml d cR dom (some (r1, m1))
grind_pattern [ind_grind] mK2_fail => mK2 n nP mo ml d (some (r2, m2))
grind_pattern [ind_grind] mK2_ok => mK2 n nP mo ml d (some (r2, m2))
grind_pattern [ind_grind] mK3_fail => mK3 n nP mo ml d fo fl concl (some (r3, m3))
grind_pattern [ind_grind] mK3_ok => mK3 n nP mo ml d fo fl concl (some (r3, m3))
grind_pattern [ind_grind] mK4_fail => mK4 n nP mo ml d fo fl concl m3 (some r4)
grind_pattern [ind_grind] mK4_ok => mK4 n nP mo ml d fo fl concl m3 (some r4)
grind_pattern [ind_grind] mK5_some => mK5 (some (r5, m5))
grind_pattern [ind_grind] tailW_eq => tailW (n + 1) m nP mo ml d fo fl concl c
grind_pattern [ind_grind] tK1_fail => tK1 n nP mo ml d fo fl c (some (r5, m5))
grind_pattern [ind_grind] tK1_ok => tK1 n nP mo ml d fo fl c (some (r5, m5))
grind_pattern [ind_grind] tK2_some => tK2 n nP mo ml d fo fl c (some (r6, m6))
grind_pattern [ind_grind] tK3_some => tK3 (some (r7, m7))

/-! ## Specs -/

section specs
variable (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "sl_find" = some slFind) (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
  (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hsc : p.lookup "sl_cons" = some slCons) (h2 : p.lookup "rec2" = some rec2)
  (h5 : p.lookup "rec5" = some rec5)
  (hi1 : p.lookup "class_read_minor_ih1" = some classReadMinorIh1)
  (his : p.lookup "class_read_minor_ihs" = some classReadMinorIhs)
  (hfin : p.lookup "class_read_minor_finish" = some classReadMinorFinish)
  (hpb : p.lookup "pi_binders" = some piBinders)
  (hmin : p.lookup "class_read_minor" = some classReadMinor)
  (htl : p.lookup "class_read_minor_tail" = some classReadMinorTail) (had : AdF p)

include hfh hv hf hcm hi1 hc ha hsc h2 his h5 hfin htl had in
theorem classReadMinorTail_spec (n : Nat) (s₀ : St) (nP mo ml d fo fl concl c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_minor_tail" [nP, mo, ml, d, fo, fl, concl, c]
    ⦃fun r s' => LocEq s' s₀ ∧ tailW n s₀.mem nP mo ml d fo fl concl c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ htl]; simp only [callFn, classReadMinorTail]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      gaaF_spec p had n, gafF_spec p had n,
      classReadMinorFinish_spec p hfh hv hf hcm hc ha hsc h2 h5 hi1 his hfin had n] <;>
    finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

include hfh hv hf hcm hi1 hc ha hsc h2 his h5 hfin htl hpb hmin had in
theorem classReadMinor_spec (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (nP mo ml d dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_minor" [nP, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ minorW cR n s₀.mem nP mo ml d dom = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hmin]; simp only [callFn, classReadMinor]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      piBinders_spec' p ha hc hv hsc hpb n, hcR n "open_pis_at_fvars_f",
      fvarHead_spec p hfh hv had n, classOfMotiveVar_spec p hf hcm n,
      classReadMinorTail_spec p hfh hv hf hcm hc ha hsc h2 h5 hi1 his hfin htl had n] <;>
    finish (gen := 20) [rdW_eq, loc_init4]

end specs

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

theorem simPiResult (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (pirF m [CWF, e]) (piResult coreWalkFuel (decI e)) a (KP dn vis fe m decW0E) := by
  have h := (pirF_ok dn vis fe CWF e he).sim hS; rw [CWF_eq] at h; exact h

theorem simGetAppFn (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (gafF m [CWF, e]) (getAppFn coreWalkFuel (decI e)) a (KP dn vis fe m decW0E) := by
  have h := (gafF_ok dn vis fe CWF e he).sim hS; rw [CWF_eq] at h; exact h

/-- A reading `cR` of `open_pis_at_fvars_f` with `OpfJ` as a `RSim`: the stub contract's post and
the invariant `J` after. -/
theorem OpfJ.sim {cR : CallM} {J : Mem → Prop} (hO : OpfJ cR J dn vis fe) (N : Nat)
    (hS : StageR dn vis fe m a) (hJ : J m) {k e i : Word} (he : H e) :
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

theorem simFvarHead (hS : StageR dn vis fe m a) {e : Word} (he : H e) :
    RSim (fvarHeadW m e) (ConRon.Arena.fvarHead (decI e)) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ decFH b.1 x) := by
  rintro ⟨r, m'⟩ h
  obtain ⟨x, a', hrun, hS', hg, hr, hb⟩ := fvarHeadW_ok dn vis fe m m' a e he r h hS
  refine ⟨x, a', hrun, hS', hg, ?_⟩
  cases x with
  | none => exact hr
  | some i => exact ⟨hr, hb i rfl⟩

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
    (a : AState) (nP mo ml d x : Word) (motPos : List Nat) (hS : StageR dn vis fe m a) (hx : H x)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (ih1W n m nP mo ml d x) (ihStep nP.toNat motPos d.toNat (decI x)) a (KP dn vis fe m decIH) := by
  rcases n with _ | n
  · exact RSim.none
  have hmb : mo.toNat + ml.toNat < 2 ^ 64 := by
    have := hS.2.1; have := hS.2.2.2.1; omega
  refine RSim.bind (K := ih1W.k_fvar_type_d n nP mo ml d) rfl (simFvarTypeD hS hx) ?_
  rintro ⟨r1, m1⟩ ty a1 - ⟨hS1, hg1, hb1, rfl⟩
  refine RSim.bind (K := ih1W.k_pi_result_f n nP mo ml d) rfl (simPiResult hS1 hb1) ?_
  rintro ⟨r2, m2⟩ ty2 a2 - ⟨hS2, hg2, hb2, rfl⟩
  refine RSim.bind (K := ih1W.k_fvar_head n nP mo ml d (r2.headD 0)) rfl (simFvarHead hS2 hb2) ?_
  rintro ⟨r3, m3⟩ x3 a3 - ⟨hS3, hg3, hx3⟩
  have hg13 := (hg1.trans hg2).trans hg3
  rcases x3 with _ | p2
  · simp only [decFH] at hx3; subst hx3; rw [ih1W.k_fvar_head.arm1 (hc1 := rfl)]; exact RSim.pure_some ⟨hS3, hg13, rfl⟩
  obtain ⟨rfl, hp2⟩ := hx3
  rw [ih1W.k_fvar_head.arm2 (hc1 := by simp)]
  refine RSim.lstep (K := ih1W.k_class_of_motive_var d (r2.headD 0) m3) rfl fun r4 h4 => ?_
  have hmot3 : decNL m3 mo.toNat ml.toNat = some motPos := by rw [decNL_grow hg13 hmt]; exact hmot
  have hc := cmvW_ok (n - 1) m3 nP mo ml _ r4 motPos hmot3 hmb h4
  simp only [List.tail_cons, List.headD_cons, UInt64.toNat_ofNat_of_lt' hp2] at hc
  show RSim _ (match ConRon.Arena.classOfMotiveVar nP.toNat motPos p2 with
    | none => pure none
    | some t => _) a3 _
  rcases hcm : ConRon.Arena.classOfMotiveVar nP.toNat motPos p2 with _ | t
  · rw [hcm] at hc; subst hc; rw [ih1W.k_class_of_motive_var.arm1 (hc1 := rfl)]; exact RSim.pure_some ⟨hS3, hg13, rfl⟩
  rw [hcm] at hc; subst hc
  have ht : t < 2 ^ 64 := by
    have := cmv_lt _ _ _ _ hcm; have := decNL_length m3 hmot3; omega
  rw [ih1W.k_class_of_motive_var.arm2 (hc1 := by simp)]
  simp only [List.tail_cons, List.headD_cons]
  refine RSim.bind (K := ih1W.k_get_app_args_f d (UInt64.ofNat t)) rfl (simGetAppArgs hS3 hb2) ?_
  rintro ⟨r5, m5⟩ rargs a5 - ⟨hS5, hg5, hd5, ht5⟩
  simp only [Nat.zero_add, getD_zero, getD_one] at hd5 ht5
  have hg15 := hg13.trans hg5
  have hb5 : (r5.headD 0).toNat + (r5.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m5 ≤ (m5.arr64 IW).size := hS5.2.1
    have h2 : (m5.arr64 IW).size < 2 ^ 64 := hS5.2.2.2.1
    omega
  by_cases hz : r5.tail.headD 0 = 0
  · rw [ih1W.k_get_app_args_f.arm1 (hc1 := hz)]
    have hnil : rargs = [] := by
      have := decHL_length m5 hd5; rw [hz] at this; exact List.eq_nil_of_length_eq_zero this
    subst hnil
    exact RSim.pure_some ⟨hS5, hg15, rfl⟩
  obtain ⟨w, hw, hH, hlast⟩ := decHL_last hd5 hz hb5
  rw [ih1W.k_get_app_args_f.arm2 (hc1 := hz), hw, hlast]
  refine RSim.bind (K := ih1W.k_fvar_head_2 d (UInt64.ofNat t)) rfl (simFvarHead hS5 hH) ?_
  rintro ⟨r6, m6⟩ x6 a6 - ⟨hS6, hg6, hx6⟩
  have hg16 := hg15.trans hg6
  rcases x6 with _ | f
  · simp only [decFH] at hx6; subst hx6; rw [ih1W.k_fvar_head_2.arm1 (hc1 := rfl)]; exact RSim.pure_some ⟨hS6, hg16, rfl⟩
  obtain ⟨rfl, hf⟩ := hx6
  by_cases hlt : UInt64.ofNat f < d
  · rw [ih1W.k_fvar_head_2.arm2 (hc1 := by simp) (hc2 := hlt)]
    have hlt' : ¬ d.toNat ≤ f := by
      have := UInt64.lt_iff_toNat_lt.mp hlt; rw [UInt64.toNat_ofNat_of_lt' hf] at this; omega
    refine RSim.pure_some ⟨hS6, hg16, ?_⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false hlt')]; rfl
  · rw [ih1W.k_fvar_head_2.arm3 (hc1 := by simp) (hc2 := hlt)]
    have hle : d.toNat ≤ f := by
      have := (UInt64.not_lt).mp hlt; rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hf] at this
      exact this
    refine RSim.pure_some ⟨hS6, hg16, ?_⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hle)]
    refine ⟨?_, by omega, ht⟩
    simp only [List.tail_cons, List.headD_cons, ofNat_sub_word f d hf hle]

/-- A word of a fresh record, read stably. -/
theorem rec_iwN_stab {m m' : Mem} {ws : List Word} {q : Word} (hq : q = rdW (m.arr64 CTL) 200)
    (hget : ∀ j < ws.length, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + j]? = ws[j]?)
    (htop : iwTop m' = iwTop m + ws.length) (j : Nat) (hj : j < ws.length) :
    StabD (fun m => iwN m (q.toNat + j)) m' (ws[j]'hj).toNat := by
  subst hq
  have hlt : (rdW (m.arr64 CTL) 200).toNat + j < iwTop m' := by rw [htop]; simp [iwTop]; omega
  refine StabD.of_eq (fun m'' hg => iwN_grow hg hlt) ?_
  simp only [iwN, nat?, iwA, hget j hj, List.getElem?_eq_getElem hj, Option.map_some]

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
    StageR dn vis fe m a → decHL m fo.toNat fl.toNat = some fvs → fo.toNat + fl.toNat ≤ iwTop m →
    decNL m mo.toNat ml.toNat = some motPos → mo.toNat + ml.toNat ≤ iwTop m →
    RSim (ihsW n m nP mo ml d fo fl) (fvs.filterMapM (ihStep nP.toNat motPos d.toNat)) a
      (KP dn vis fe m decIHS) := by
  induction n with
  | zero => intro m a fo fl fvs _ _ _ _ _; exact RSim.of_none (by rw [ihsW])
  | succ n ih =>
  intro m a fo fl fvs hS hfvs hft hmot hmt
  have hfb : fo.toNat + fl.toNat < 2 ^ 64 := by
    have h1 : iwTop m ≤ (m.arr64 IW).size := hS.2.1
    have h2 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
    omega
  by_cases hfl : fl = 0
  · rw [ihsW.arm1 (hc1 := hfl)]
    have hnil : fvs = [] := by
      have := decHL_length m hfvs; rw [hfl] at this; exact List.eq_nil_of_length_eq_zero this
    subst hnil
    rw [List.filterMapM_nil]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, SPL.nil 0 (Nat.zero_le _)⟩
  obtain ⟨hfo1, hfl1, hfl0⟩ := slice_step hfl hfb
  obtain ⟨k, hk⟩ : ∃ k, fl.toNat = k + 1 := ⟨fl.toNat - 1, by omega⟩
  rw [hk] at hfvs
  obtain ⟨x, xs, rfl, hxs, hx⟩ := decHL_cons_r hfvs
  obtain ⟨w, hw, hH, rfl⟩ := iwH_rdW hx (by omega)
  rw [UInt64.ofNat_toNat] at hw
  rw [ihsW.arm2 (hc1 := hfl), hw, List.filterMapM_cons]
  refine RSim.bind (K := ihsW.k_class_read_minor_ih1 n nP mo ml d fo fl) (by rw [ihsW.k_class_read_minor_ih1.none])
    (ih1W_sim dn vis fe n m a nP mo ml d w motPos hS hH hmot hmt) ?_
  rintro ⟨r1, m1⟩ o a1 - ⟨hS1, hg1, ho⟩
  dsimp only at hS1 hg1 ho
  rw [ihsW.k_class_read_minor_ih1.arm1]
  have hxs1 : decHL m1 (fo + 1).toNat (fl - 1).toNat = some xs := by
    rw [hfo1, hfl1, decHL_grow hg1 (by omega)]; rw [show fl.toNat - 1 = k by omega]; exact hxs
  have hft1 : (fo + 1).toNat + (fl - 1).toNat ≤ iwTop m1 := by have := hg1.1; omega
  have hmot1 : decNL m1 mo.toNat ml.toNat = some motPos := by rw [decNL_grow hg1 hmt]; exact hmot
  have hmt1 : mo.toNat + ml.toNat ≤ iwTop m1 := Nat.le_trans hmt hg1.1
  rcases o with _ | ft
  · refine RSim.bindPure (K := ihsW.k_class_read_minor_ihs n (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0)) rfl (ih m1 a1 (fo + 1) (fl - 1) xs hS1 hxs1 hft1 hmot1 hmt1) ?_
    rintro ⟨r2, m2⟩ rest a2 - ⟨hS2, hg2, hsp⟩
    have ho' : r1.headD 0 ≠ 1 := by simp only [decIH] at ho; rw [ho]; decide
    rw [ihsW.k_class_read_minor_ihs.arm2 (hc1 := ho')]
    exact RSim.pure_some ⟨hS2, hg1.trans hg2, hsp⟩
  obtain ⟨f, t⟩ := ft
  obtain ⟨rfl, hf, ht⟩ := ho
  refine RSim.bind (K := ihsW.k_class_read_minor_ihs n 1 (UInt64.ofNat f) (UInt64.ofNat t)) rfl
    (ih m1 a1 (fo + 1) (fl - 1) xs hS1 hxs1 hft1 hmot1 hmt1) ?_
  rintro ⟨r2, m2⟩ rest a2 - ⟨hS2, hg2, hsp⟩
  rw [ihsW.k_class_read_minor_ihs.arm1 (hc1 := rfl)]
  refine RSim.lstep (K := ihsW.k_rec2 n (r2.headD 0) (r2.tail.headD 0)) rfl ?_
  rintro ⟨r3, m3⟩ h3
  obtain ⟨hS3, hg3, hr3, hget, htop⟩ := recW_stage h3 hS2 rfl
  rw [ihsW.k_rec2.arm1]
  refine RSim.lstep (K := ihsW.k_sl_cons) rfl ?_
  rintro ⟨r4, m4⟩ h4
  have hst := rec2_decNN (a := UInt64.ofNat f) (b := UInt64.ofNat t) rfl hget htop
  rw [hr3] at h4
  simp only [List.headD_cons] at h4
  obtain ⟨hS4, hg4, hsp4⟩ := SPL.cons h4 hS3 (hsp.grow hg3) hst
  rw [ihsW.k_sl_cons.arm1]
  refine RSim.pure_some ⟨hS4, ((hg1.trans hg2).trans hg3).trans hg4, ?_⟩
  simp only [decIHS, List.headD_cons, List.tail_cons]
  rwa [UInt64.toNat_ofNat_of_lt' hf, UInt64.toNat_ofNat_of_lt' ht] at hsp4

/-! ## `class_read_minor_finish` -/

/-- A `const` handle's view, through `e_view`'s words. -/
theorem viewConstW {m : Mem} {a : AState} (hR : ArenaR m a) {w : Word} (hne : eViewW m w ≠ [])
    (hg : w >>> 28 = 3) :
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
    (hS : StageR dn vis fe m a) (hH : H hd) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hft : fo.toNat + fl.toNat ≤ iwTop m) (hmot : decNL m mo.toNat ml.toNat = some motPos)
    (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (finW n m nP mo ml d fo fl hd c) (minorFin nP.toNat motPos d.toNat c.toNat fvs (decI hd)) a
      (KP dn vis fe m decSlot) := by
  rcases n with _ | n
  · exact RSim.none
  by_cases hg : hd >>> 28 ≠ 3
  · rw [finW.arm1 (hc1 := hg)]
    have ht : ¬ (((decI hd : EIdx)).tag == ETag.const) = true := by
      have : ¬ (decE hd).tag = ETag.const := fun h => hg ((decE_tag_const hd hH).mp h)
      simp only [beq_iff_eq]; exact this
    simp only [minorFin]
    rw [ite_eq_right ht]
    exact RSim.pure_some ⟨hS, IWGrow.refl m, rfl⟩
  by_cases hne : eViewW m hd = []
  · rw [finW.abort1 (hc1 := Decidable.of_not_not hg) (hc2 := hne)]; exact RSim.none
  rw [finW.arm2 (hc1 := Decidable.of_not_not hg) (hc2 := hne)]
  have hg3 : hd >>> 28 = 3 := by simpa using hg
  have ht : (((decI hd : EIdx)).tag == ETag.const) = true := by
    have : (decE hd).tag = ETag.const := (decE_tag_const hd hH).mpr hg3
    simp only [beq_iff_eq]; exact this
  obtain ⟨hvc, hcn, -⟩ := viewConstW hS.1.arena.1 hne hg3
  simp only [minorFin]
  rw [ite_eq_left ht]
  refine RSim.tstep hvc ?_
  refine RSim.bind (K := finW.k_class_read_minor_ihs c ((eViewW m hd).tail.headD 0)) rfl
    (ihsW_sim dn vis fe nP mo ml d motPos n m a fo fl fvs hS hfvs hft hmot hmt) ?_
  rintro ⟨r1, m1⟩ ihs a1 - ⟨hS1, hg1, hsp⟩
  dsimp only at hS1 hg1 hsp
  refine RSim.lstep (K := finW.k_rec5) rfl ?_
  rintro ⟨r2, m2⟩ h2
  obtain ⟨hS2, hg2, hr2, hget, htop⟩ := recW_stage h2 hS1 rfl
  rw [finW.k_rec5.arm1]
  refine RSim.pure_some ⟨hS2, hg1.trans hg2, rfl, ?_⟩
  rw [hr2]
  simp only [List.headD_cons, List.tail_cons]
  have hq : rdW (m1.arr64 CTL) 200 = rdW (m1.arr64 CTL) 200 := rfl
  have e0 := rec_iwN_stab hq hget htop 0 (by simp)
  have e1 := rec_iwN_stab hq hget htop 1 (by simp)
  have e2 := rec_iwH_stab (kk := IdxKind.name) hq hget htop 2 (by simp) hcn
  have e3 := rec_iwN_stab hq hget htop 3 (by simp)
  have e4 := rec_iwN_stab hq hget htop 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4
  exact decCS_minor_stab e0 e1 e2 e3 e4 (hsp.grow hg2)

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
  simp only [tailW, tK1.eq_def, tK2.eq_def, tK3.eq_def] at h
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
    (hS : StageR dn vis fe m a) (hH : H concl) (hfvs : decHL m fo.toNat fl.toNat = some fvs)
    (hft : fo.toNat + fl.toNat ≤ iwTop m) (hmot : decNL m mo.toNat ml.toNat = some motPos)
    (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (tailW n m nP mo ml d fo fl concl c)
      (minorTail nP.toNat motPos d.toNat c.toNat fvs (decI concl)) a (KP dn vis fe m decSlot) := by
  rcases n with _ | n
  · exact RSim.none
  rw [tailW_eq]
  refine RSim.bind (K := tK1 n nP mo ml d fo fl c) rfl (simGetAppArgs hS hH) ?_
  rintro ⟨r5, m5⟩ rargs a5 - ⟨hS5, hg5, hd5, ht5⟩
  dsimp only at hS5 hg5 hd5 ht5
  simp only [Nat.zero_add, getD_zero, getD_one] at hd5 ht5
  have hb5 : (r5.headD 0).toNat + (r5.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m5 ≤ (m5.arr64 IW).size := hS5.2.1
    have h2 : (m5.arr64 IW).size < 2 ^ 64 := hS5.2.2.2.1
    omega
  by_cases hz : r5.tail.headD 0 = 0
  · rw [tK1_fail (h := hz)]
    have hnil : rargs = [] := by
      have := decHL_length m5 hd5; rw [hz] at this; exact List.eq_nil_of_length_eq_zero this
    subst hnil
    exact RSim.pure_some ⟨hS5, hg5, rfl⟩
  obtain ⟨w, hw, hwH, hlast⟩ := decHL_last hd5 hz hb5
  rw [tK1_ok (h := hz), hw, hlast]
  refine RSim.bind (K := tK2 n nP mo ml d fo fl c) rfl (simGetAppFn hS5 hwH) ?_
  rintro ⟨r6, m6⟩ hd a6 - ⟨hS6, hg6, hb6, rfl⟩
  dsimp only at hS6 hg6 hb6
  rw [tK2_some]
  have hg56 := hg5.trans hg6
  refine RSim.bindPure (K := tK3) rfl (finW_sim dn vis fe n m6 a6 nP mo ml d fo fl (r6.headD 0) c motPos
    fvs hS6 hb6 (by rw [decHL_grow hg56 hft]; exact hfvs) (Nat.le_trans hft hg56.1)
    (by rw [decNL_grow hg56 hmt]; exact hmot) (Nat.le_trans hmt hg56.1)) ?_
  rintro ⟨r7, m7⟩ x a7 - ⟨hS7, hg7, hd7⟩
  rw [tK3_some]
  exact RSim.pure_some ⟨hS7, hg56.trans hg7, decSlot_pair hd7⟩

theorem minorW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (n : Nat) (m : Mem)
    (a : AState) (nP mo ml d dom : Word) (motPos : List Nat) (hS : StageR dn vis fe m a) (hJ : J m)
    (hH : H dom)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (minorW cR n m nP mo ml d dom) (ConRon.Arena.classReadMinor nP.toNat motPos d.toNat (decI dom)) a
      (fun b a' x => KP dn vis fe m decSlot b a' x ∧ J b.2) := by
  rcases n with _ | n
  · exact RSim.none
  have hmb : mo.toNat + ml.toNat < 2 ^ 64 := by
    have h1 : iwTop m ≤ (m.arr64 IW).size := hS.2.1
    have h2 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
    omega
  rw [minorW_eq]
  refine RSim.bind (K := mK1 n nP mo ml d cR dom) rfl
    (RSim.withJ hO.1 (simPiBinders n hS hH) (fun _ _ hb => piBW_afrR _ _ _ _ _ _ hb) hJ) ?_
  rintro ⟨r1, m1⟩ ⟨bs, e⟩ a1 - ⟨⟨hS1, hg1, hd1, ht1⟩, hJ1⟩
  dsimp only at hS1 hg1 hd1 ht1 hJ1
  rw [mK1_some]
  have hlen : bs.length = (r1.tail.headD 0).toNat := decHL_length _ hd1
  simp only []
  rw [hlen]
  refine RSim.bind (K := mK2 n nP mo ml d) rfl (hO.sim n hS1 hJ1 hH) ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨⟨hS2, hg2, ho⟩, hJ2⟩
  dsimp only at hS2 hg2 ho hJ2
  have hg12 := hg1.trans hg2
  rcases o with _ | fc
  · rw [mK2_fail (h := ho)]; exact RSim.pure_some ⟨⟨hS2, hg12, rfl⟩, hJ2⟩
  obtain ⟨fvs, concl⟩ := fc
  obtain ⟨h21, ⟨hfvs, hft⟩, hcH, rfl⟩ := ho
  simp only [getD_one, getD_two, Nat.reduceAdd] at hfvs hft
  rw [drop3_headD] at hcH ⊢
  rw [mK2_ok (h := by rw [h21]; decide)]
  refine RSim.bind (K := mK3 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0)
    (r2.tail.tail.tail.headD 0)) rfl
    (RSim.withJ hO.1 (simFvarHead hS2 hcH) (fun _ _ hb => fvarHeadW_afr hb) hJ2) ?_
  rintro ⟨r3, m3⟩ x3 a3 - ⟨⟨hS3, hg3, hx3⟩, hJ3⟩
  dsimp only at hS3 hg3 hx3 hJ3
  have hg13 := hg12.trans hg3
  rcases x3 with _ | p2
  · simp only [decFH] at hx3; subst hx3
    rw [mK3_fail (h := rfl)]
    exact RSim.pure_some ⟨⟨hS3, hg13, rfl⟩, hJ3⟩
  obtain ⟨rfl, hp2⟩ := hx3
  rw [mK3_ok (h := by simp)]
  refine RSim.lstep (K := mK4 n nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0)
    (r2.tail.tail.tail.headD 0) m3) rfl fun r4 h4 => ?_
  have hmot3 : decNL m3 mo.toNat ml.toNat = some motPos := by rw [decNL_grow hg13 hmt]; exact hmot
  have hc := cmvW_ok (n - 1) m3 nP mo ml _ r4 motPos hmot3 hmb h4
  simp only [List.tail_cons, List.headD_cons, UInt64.toNat_ofNat_of_lt' hp2] at hc
  rcases hcm : ConRon.Arena.classOfMotiveVar nP.toNat motPos p2 with _ | c
  · rw [hcm] at hc; subst hc
    simp only [hcm]
    rw [mK4_fail (h := rfl)]
    exact RSim.pure_some ⟨⟨hS3, hg13, rfl⟩, hJ3⟩
  rw [hcm] at hc; subst hc
  simp only [hcm]
  have hc64 : c < 2 ^ 64 := by
    have := cmv_lt _ _ _ _ hcm; have := decNL_length m3 hmot3; omega
  rw [mK4_ok (h := by simp)]
  simp only [List.tail_cons, List.headD_cons]
  have ht := tailW_sim dn vis fe n m3 a3 nP mo ml d (r2.tail.headD 0) (r2.tail.tail.headD 0)
    (r2.tail.tail.tail.headD 0) (UInt64.ofNat c) motPos fvs hS3 hcH
    (by rw [decHL_grow hg3 hft]; exact hfvs) (Nat.le_trans hft hg3.1) hmot3 (Nat.le_trans hmt hg13.1)
  rw [UInt64.toNat_ofNat_of_lt' hc64] at ht
  refine RSim.bindPure (K := mK5) rfl (RSim.withJ hO.1 ht (fun _ _ hb => tailW_afr hb) hJ3) ?_
  rintro ⟨r5, m5⟩ x a5 - ⟨⟨hS5, hg5, hd5⟩, hJ5⟩
  rw [mK5_some]
  exact RSim.pure_some ⟨⟨hS5, hg13.trans hg5, decSlot_pair hd5⟩, hJ5⟩

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

l_model classReadSlotMotive_spec (p : Prog) (hP : SlotProg p)
  fns [hP.smot ↦ slotMotW list]
  specs [piBinders_spec' p hP.a hP.c hP.v hP.sc hP.pb n, gafF_spec p hP.ad n,
    gaaF_spec p hP.ad n, eView_spec p hP.v n,
    classNPcOf_spec p hP.a hP.mc hP.mn hP.ct hP.x hP.g hP.ef hP.npc n,
    rec4_specW p hP.a n hP.r4, rec2_specW p hP.a n hP.r2]
  grind [arena_grind] simp [rdW_eq, getElem_rdW']

/-- After `class_n_pc_of`: the join point of `cnt := min n al`. -/
theorem slotMotW_npc_some (iName us ao al : Word) (r : List Word) (m : Mem) :
    slotMotW.k_class_n_pc_of iName us ao al (some (r, m)) =
      slotMotW.k_rec4 (recW m 4 [iName, us, ao, if r.headD 0 < al then r.headD 0 else al]) := by
  by_cases h : r.headD 0 < al
  · rw [slotMotW.k_class_n_pc_of.arm1 (hc1 := h), slotMotW.j1, ite_eq_left h]
  · rw [slotMotW.k_class_n_pc_of.arm2 (hc1 := h), slotMotW.j1, ite_eq_right h]

def slK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

def slK1 (cR : CallM) (n : Nat) (p vis np mo ml d dom : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 >>> 28 = 2 then slK2 (slotMotW n m1 p vis dom)
    else slK2 (minorW cR n m1 np mo ml d dom)

/-- **The model of `class_read_slot`.** -/
def slotW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, p, vis, np, mo, ml, d, dom => slK1 cR n p vis np mo ml d dom (pirF m [CWF, dom])

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 : Mem) (p vis np mo ml d dom mdom iName us ao al : Word)
  (r r1 r2 r3 r4 r5 r6 : List Word) (cR : CallM)
theorem slotW_eq : slotW cR (n + 1) m p vis np mo ml d dom =
    slK1 cR n p vis np mo ml d dom (pirF m [CWF, dom]) := rfl
theorem slK1_mot (h : r1.headD 0 >>> 28 = 2) : slK1 cR n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (slotMotW n m1 p vis dom) := by rw [slK1, ite_eq_left h]
theorem slK1_min (h : ¬ r1.headD 0 >>> 28 = 2) : slK1 cR n p vis np mo ml d dom (some (r1, m1)) =
    slK2 (minorW cR n m1 np mo ml d dom) := by rw [slK1, ite_eq_right h]
theorem slK2_some : slK2 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] slotW_eq => slotW cR (n + 1) m p vis np mo ml d dom
grind_pattern [ind_grind] slK1_mot => slK1 cR n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK1_min => slK1 cR n p vis np mo ml d dom (some (r1, m1))
grind_pattern [ind_grind] slK2_some => slK2 (some (r, m))

theorem classReadSlot_spec (p : Prog) (hP : SlotProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat)
    (s₀ : St) (q vis np mo ml d dom : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_slot" [q, vis, np, mo, ml, d, dom]
    ⦃fun r s' => LocEq s' s₀ ∧ slotW cR n s₀.mem q vis np mo ml d dom = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.slot]; simp only [callFn, classReadSlot]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      pirF_spec p hP.ad n, classReadSlotMotive_spec p hP n,
      classReadMinor_spec p hP.fh hP.v hP.f hP.cm hP.c hP.a hP.sc hP.r2 hP.r5 hP.i1 hP.is hP.fin
        hP.pb hP.min hP.tl hP.ad cR hcR n] <;>
    finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6]

/-! ## Relational lemmas -/

theorem tag_beq (e : Word) (hh : H e) (t : UInt32) (k : Nat) (hk : k < 16) (ht : t = UInt32.ofNat k) :
    (((decI e : EIdx).tag == t) = true) ↔ e >>> 28 = UInt64.ofNat k := by
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

theorem slotMotW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (p dom : Word) (bs : BlockShape) (hS : StageR dn vis fe m a) (hH : H dom)
    (hb : BSOK m p.toNat bs) :
    RSim (slotMotW n m p vis dom) (slotMot bs fe (decI dom)) a (KP dn vis fe m decSlot) := by
  rcases n with _ | n
  · exact RSim.none
  rw [slotMotW.arm1]
  refine RSim.bind (K := slotMotW.k_pi_binders n p vis) rfl (simPiBinders n hS hH) ?_
  rintro ⟨r1, m1⟩ ⟨bss, e⟩ a1 - ⟨hS1, hg1, hd1, ht1⟩
  dsimp only at hS1 hg1 hd1 ht1
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m1 ≤ (m1.arr64 IW).size := hS1.2.1
    have h2 : (m1.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
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
  by_cases hg : r2.headD 0 >>> 28 ≠ 3
  · rw [slotMotW.k_get_app_fn_f.arm1 (hc1 := hg)]
    have ht : ¬ (((decI (r2.headD 0) : EIdx)).tag == ETag.const) = true :=
      fun e => hg ((tag_beq _ hb2 _ 3 (by decide) rfl).mp e)
    rw [ite_eq_right ht]
    exact RSim.pure_some ⟨hS2, hg12, rfl⟩
  by_cases hne : eViewW m2 (r2.headD 0) = []
  · rw [slotMotW.k_get_app_fn_f.abort1 (hc1 := Decidable.of_not_not hg) (hc2 := hne)]; exact RSim.none
  rw [slotMotW.k_get_app_fn_f.arm2 (hc1 := Decidable.of_not_not hg) (hc2 := hne)]
  have hg3 : r2.headD 0 >>> 28 = 3 := by simpa using hg
  have ht : (((decI (r2.headD 0) : EIdx)).tag == ETag.const) = true :=
    (tag_beq _ hb2 _ 3 (by decide) rfl).mpr hg3
  obtain ⟨hvc, hnH, huH⟩ := viewConstW hS2.1.arena.1 hne hg3
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

theorem envFindW_afrR {m m' : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m')) :
    AFr m m' := by
  unfold envFindW at h
  afr_auto h []

theorem npcW_afr {n : Nat} {m m' : Mem} {p vis i : Word} {r : List Word}
    (h : npcW n m p vis i = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [npcW] at h
  simp only [npcW, npcK1.eq_def, npcK2.eq_def, npcK3.eq_def] at h
  afr_auto h [memberNamesW_afr, envFindW_afrR]

theorem slotMotW_afr {n : Nat} {m m' : Mem} {p vis dom : Word} {r : List Word}
    (h : slotMotW n m p vis dom = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [slotMotW] at h
  simp only [slotMotW, slotMotW.k_pi_binders.eq_def, slotMotW.k_get_app_fn_f.eq_def,
    slotMotW.k_get_app_args_f.eq_def, slotMotW.k_class_n_pc_of.eq_def, slotMotW.j1, slotMotW.k_rec4.eq_def,
    slotMotW.k_rec2.eq_def] at h
  afr_auto h [piBW_afrR _ _ _ _ _ _, gafF_afr, gaaF_afr, npcW_afr, recW_afr]

theorem slotW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (n : Nat) (m : Mem)
    (a : AState) (p np mo ml d dom : Word) (bs : BlockShape) (motPos : List Nat)
    (hS : StageR dn vis fe m a) (hJ : J m) (hH : H dom) (hb : BSOK m p.toNat bs)
    (hmot : decNL m mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop m) :
    RSim (slotW cR n m p vis np mo ml d dom)
      (ConRon.Arena.classReadSlot bs fe np.toNat motPos d.toNat (decI dom)) a
      (fun b a' x => KP dn vis fe m decSlot b a' x ∧ J b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [slotW_eq]
  refine RSim.bind (K := slK1 cR n p vis np mo ml d dom) rfl
    (RSim.withJ hO.1 (simPiResult hS hH) (fun _ _ hb => pirF_afrR hb) hJ) ?_
  rintro ⟨r1, m1⟩ r a1 - ⟨⟨hS1, hg1, hb1, rfl⟩, hJ1⟩
  dsimp only at hS1 hg1 hb1 hJ1
  by_cases ht : r1.headD 0 >>> 28 = 2
  · rw [slK1_mot (h := ht)]
    have ht' : (((decI (r1.headD 0) : EIdx)).tag == ETag.sort) = true :=
      (tag_beq _ hb1 _ 2 (by decide) rfl).mpr ht
    rw [ite_eq_left ht']
    refine RSim.bindPure (K := slK2) rfl (RSim.withJ hO.1
      (slotMotW_sim dn vis fe n m1 a1 p dom bs hS1 hH (hb.grow hg1)) (fun _ _ hb => slotMotW_afr hb) hJ1) ?_
    rintro ⟨r2, m2⟩ x a2 - ⟨⟨hS2, hg2, hd2⟩, hJ2⟩
    rw [slK2_some]
    exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, decSlot_pair hd2⟩, hJ2⟩
  · rw [slK1_min (h := ht)]
    have ht' : ¬ (((decI (r1.headD 0) : EIdx)).tag == ETag.sort) = true :=
      fun e => ht ((tag_beq _ hb1 _ 2 (by decide) rfl).mp e)
    rw [ite_eq_right ht']
    refine RSim.bindPure (K := slK2) rfl (minorW_sim dn vis fe cR J hO n m1 a1 np mo ml d dom motPos hS1
      hJ1 hH (by rw [decNL_grow hg1 hmt]; exact hmot) (Nat.le_trans hmt hg1.1)) ?_
    rintro ⟨r2, m2⟩ x a2 - ⟨⟨hS2, hg2, hd2⟩, hJ2⟩
    rw [slK2_some]
    exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, decSlot_pair hd2⟩, hJ2⟩

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec, eView_spec p hP.v N,
        classReadSlot_spec p hP.toSlotProg cR hcR N, ih2]
      all_goals subst_vars
      all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
        reduceIte, beq_iff_eq, bne_iff_ne, ne_eq] at *)
      all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5, loc_init6,
        loc_init7]
    · rw [invoke_eq _ hP.next]; simp only [callFn, classReadSlotsNext]
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rd_spec,
        classReadSlotsSnoc_spec p hP.a hP.c hP.sn hP.msn N, internFVar_spec p hP.ff hP.fp hP.ifv N,
        i1F_spec p hP.hi1 N, slCons_specW p hP.a hP.c hP.sc N, ih1]
      all_goals subst_vars
      all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        Locals.init_nil, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
        reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
      all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind, rdW_eq, loc_init4, loc_init5, loc_init6,
        loc_init7, loc_init8, loc_init9]

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
  grind [arena_grind] simp [rdW_eq, getElem_rdW']

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

def rdK1 (cR : CallM) (N : Nat) (p vis nP ro rl rc0 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else rdK2 cR N nP ro rl (slotsW cR N m1 p vis nP (tsubW (rdW (m1.arr64 IW) (rc0 + 1)) nP) 0 0 nP
      (r1.tail.tail.tail.headD 0))

/-- **The model of `class_read`.** -/
def readW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | N + 1, m, p, vis, nP, ro, rl =>
    if rl = 0 then some ([0, 0], m)
    else rdK1 cR N p vis nP ro rl (rdW (m.arr64 IW) ro)
      (cR N "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0] m)

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
theorem readW_nil (h : rl = 0) : readW cR (N + 1) m p vis nP ro rl = some ([0, 0], m) := by
  simp [readW, h]
theorem readW_ok (h : rl ≠ 0) : readW cR (N + 1) m p vis nP ro rl =
    rdK1 cR N p vis nP ro rl (rdW (m.arr64 IW) ro)
      (cR N "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0] m) := by
  simp [readW, h]
theorem rdK1_fail (h : r1.headD 0 = 0) : rdK1 cR N p vis nP ro rl rc0 (some (r1, m1)) = some ([0, 0], m1) := by
  rw [rdK1, ite_eq_left h]
theorem rdK1_ok (h : r1.headD 0 ≠ 0) : rdK1 cR N p vis nP ro rl rc0 (some (r1, m1)) =
    rdK2 cR N nP ro rl (slotsW cR N m1 p vis nP (tsubW (rdW (m1.arr64 IW) (rc0 + 1)) nP) 0 0 nP
      (r1.tail.tail.tail.headD 0)) := by rw [rdK1, ite_eq_right h]
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
grind_pattern [ind_grind] readW_nil => readW cR (N + 1) m p vis nP ro rl
grind_pattern [ind_grind] readW_ok => readW cR (N + 1) m p vis nP ro rl
grind_pattern [ind_grind] rdK1_fail => rdK1 cR N p vis nP ro rl rc0 (some (r1, m1))
grind_pattern [ind_grind] rdK1_ok => rdK1 cR N p vis nP ro rl rc0 (some (r1, m1))
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
    finish (gen := 20)

theorem classRead_spec (p : Prog) (hP : ReadProg p) (cR : CallM) (hcR : CallSpec p cR) (N : Nat) (s₀ : St)
    (q vis nP ro rl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read" [q, vis, nP, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ readW cR N s₀.mem q vis nP ro rl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.rd]; simp only [callFn, classRead]
  rcases N with _ | N
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      hcR N "open_pis_at_fvars_f", classReadNSlots_spec p hP N,
      (classReadSlots_specs p hP.toSlotsProg cR hcR N).1, classReadFinish_spec p hP cR hcR N] <;>
    finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7]

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
    motPosW N m so sl j = some (r, m') → StageR dn vis fe m a → SPL decCS m so.toNat sl.toNat slots →
    j.toNat ≤ sl.toNat →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat =
        some ((List.range' j.toNat (sl.toNat - j.toNat)).filter (motF slots)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction N with
  | zero => intro m m' j r h; simp [motPosW] at h
  | succ N ih =>
  intro m m' j r h hS hsp hj
  by_cases he : sl ≤ j
  · rw [motPosW.arm1 (hc1 := he)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : sl.toNat - j.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp he; omega
    refine ⟨hS, IWGrow.refl m, ?_, by simp⟩
    simp [this, decNL]
  rw [motPosW.arm2 (hc1 := he)] at h
  have hjl : j.toNat < sl.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp he)
  have := sl.toNat_lt
  have hlen : j.toNat < slots.length := by rw [hsp.length]; exact hjl
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  obtain ⟨hS1, hg1, hd1, ht1⟩ := ih m m1 (j + 1) r1 h1 hS hsp (by rw [hj1]; omega)
  rw [hj1] at hd1
  obtain ⟨q, hq, hst⟩ := hsp.get j.toNat hjl
  have hsz := hS.2.2.2.1
  have hb := hsp.1
  have hrd := iwN_rdW_at (w := so) (k := j.toNat) hq hsz
  rw [show so + UInt64.ofNat j.toNat = so + j by simp] at hrd
  have hrd1 : rdW (m1.arr64 IW) (so + j) = UInt64.ofNat q := by
    rw [← hrd.1]; simp only [rdW]
    rw [show (so + j).toNat = so.toNat + j.toNat by
      rw [UInt64.toNat_add]; have := hS.2.1; exact Nat.mod_eq_of_lt (by omega), hg1.2.2.1 _ (by omega)]
  have htag := decCS_tag (hst.grow hg1).get
  have hrq := iwN_rdW htag (by have := iwN_lt htag; omega)
  rw [show UInt64.ofNat q = UInt64.ofNat q from rfl] at hrq
  have hsplit : sl.toNat - j.toNat = (sl.toNat - (j.toNat + 1)) + 1 := by omega
  by_cases hm : (slots[j.toNat]'hlen).isMinor = true
  · rw [motPosW.k_class_read_mot_pos.arm2 (hc1 := by rw [hrd1, hrq.1]; simp [hm])] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hf : motF slots j.toNat = false := by
      simp only [motF, List.getElem?_eq_getElem hlen]
      revert hm; generalize slots[j.toNat] = x; cases x <;> simp [ClassSlot.isMinor]
    refine ⟨hS1, hg1, ?_, by simpa using ht1⟩
    simp only [List.headD_cons, List.tail_cons]
    rw [hsplit, range'_filter_step, hf]; simpa using hd1
  · rw [motPosW.k_class_read_mot_pos.arm1 (hc1 := by rw [hrd1, hrq.1]; simp at hm; simp [hm])] at h
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
    rw [motPosW.k_sl_cons.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hd2, ht2⟩ := consW_stageN h2 hS1 ht1 hd1
    have hf : motF slots j.toNat = true := by
      simp only [motF, List.getElem?_eq_getElem hlen]
      revert hm; generalize slots[j.toNat] = x; cases x <;> simp [ClassSlot.isMinor]
    refine ⟨hS2, hg1.trans hg2, ?_, by simpa using Nat.le_of_eq ht2⟩
    simp only [List.headD_cons, List.tail_cons]
    rw [hsplit, range'_filter_step, hf]; simpa using hd2

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
    (hS : StageR dn vis fe m a) (hJ : J m) (hsp : SPL decCS m so.toNat sl.toNat slots)
    (hrecs : RecsDec m ro rl recs) :
    RSim (readFinW cR N m nP so sl ro rl) (readFinTw nP.toNat slots recs) a
      (fun b a' x => KP dn vis fe m decRead b a' x ∧ J b.2) := by
  rcases N with _ | N
  · exact RSim.none
  rw [readFinW_eq]
  refine RSim.lstep (K := frK1 cR N nP so sl ro rl) rfl ?_
  rintro ⟨r1, m1⟩ h1
  obtain ⟨hS1, hg1, hd1, ht1⟩ := motPosW_ok dn vis fe a so sl slots N m m1 0 r1 h1 hS hsp (by simp)
  have hJ1 := hO.1 _ _ (motPosW_afr _ _ _ _ _ _ _ h1) hJ
  simp only [UInt64.toNat_zero, Nat.sub_zero] at hd1
  rw [← hsp.length, ← List.range_eq_range'] at hd1
  rw [frK1_some]
  have hcr : RSim (crW cR N m1 nP (r1.headD 0) (r1.tail.headD 0) ro rl)
      (ConRon.Arena.classReadRecCls nP.toNat ((List.range slots.length).filter (motF slots)) recs) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m1 b.2 ∧ CrRes b.2 b.1 x ∧ J b.2) := by
    rintro ⟨r, m'⟩ h
    exact crW_ok dn vis fe cR J hO N m1 m' a nP _ _ ro rl r recs _ h hS1 hJ1 (hrecs.dec hg1)
      (fun m3 hg3 => hrecs.dec (hg1.trans hg3)) hd1 ht1 hrecs.2
  refine RSim.bind (K := frK2 so sl) rfl hcr ?_
  rintro ⟨r2, m2⟩ x a2 - ⟨hS2, hg2, hc2, hJ2⟩
  dsimp only at hS2 hg2 hc2 hJ2
  have hg12 := hg1.trans hg2
  rcases x with _ | cs
  · rw [frK2_fail (h := hc2)]; exact RSim.pure_some ⟨⟨hS2, hg12, rfl⟩, hJ2⟩
  obtain ⟨h21, hdn2, ht2⟩ := hc2
  rw [frK2_ok (h := by rw [h21]; decide)]
  refine RSim.lstep (K := frK3) rfl ?_
  rintro ⟨r3, m3⟩ h3
  obtain ⟨hS3, hg3, hr3, hget, htop⟩ := recW_stage h3 hS2 rfl
  have hJ3 := hO.1 _ _ (recW_afr h3) hJ2
  rw [frK3_some, hr3]
  have hq : rdW (m2.arr64 CTL) 200 = rdW (m2.arr64 CTL) 200 := rfl
  have k0 := rec_iwN_stab hq hget htop 0 (by simp)
  have k1 := rec_iwN_stab hq hget htop 1 (by simp)
  have k2 := rec_iwN_stab hq hget htop 2 (by simp)
  have k3 := rec_iwN_stab hq hget htop 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at k0 k1 k2 k3
  have hsp3 := hsp.grow (hg12.trans hg3)
  refine RSim.pure_some ⟨⟨hS3, hg12.trans hg3, rfl, ?_, so.toNat, sl.toNat, ?_, ?_, ?_⟩, hJ3⟩
  all_goals simp only [List.headD_cons, List.tail_cons]
  · intro m' hg
    have e1 : iwN m' ((rdW (m2.arr64 CTL) 200).toNat + 0 + 1) = some sl.toNat := by simpa using k1 m' hg
    have e3 : iwN m' ((rdW (m2.arr64 CTL) 200).toNat + 2 + 1) = some (r2.tail.tail.headD 0).toNat :=
      k3 m' hg
    have hdn' : decNL m' (r2.tail.headD 0).toNat (r2.tail.tail.headD 0).toNat = some cs := by
      rw [decNL_grow (hg3.trans hg) ht2]; exact hdn2
    simp only [decCR, decAt, Nat.add_zero] at e1 ⊢
    simp only [k0 m' hg, e1, k2 m' hg, e3, (hsp3.grow hg).decPL, hdn', Option.bind_eq_bind,
      Option.bind_some]
    rfl
  · simpa using k0 _ (IWGrow.refl _)
  · simpa using k1 _ (IWGrow.refl _)
  · exact hsp3

theorem decRS_rP {m : Mem} {p : Nat} {R : RecShape} (h : decRS m p = some R) :
    ∃ q, iwN m p = some q ∧ decCVp m q = some R.cvR ∧ iwN m (p + 1) = some R.rP := by
  simp only [decRS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, rP, hrP, mI, hmI, tg, htg, rh, hrh, rfl⟩ := h
  exact ⟨q, hq, hcv, hrP⟩

theorem readW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (cR : CallM)
    (J : Mem → Prop) (hO : OpfJ cR J dn vis fe) (N : Nat) (m : Mem)
    (a : AState) (p nP ro rl : Word) (bs : BlockShape) (recs : List RecShape)
    (hS : StageR dn vis fe m a) (hJ : J m) (hb : BSOK m p.toNat bs) (hrecs : RecsDec m ro rl recs) :
    RSim (readW cR N m p vis nP ro rl) (ConRon.Arena.classRead bs fe nP.toNat recs) a
      (fun b a' x => KP dn vis fe m decRead b a' x ∧ J b.2) := by
  rcases N with _ | N
  · exact RSim.none
  have hdp := hrecs.dec (IWGrow.refl m)
  have hsz := hS.2.2.2.1
  have hts : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  by_cases hrl : rl = 0
  · rw [readW_nil (h := hrl)]
    have : recs = [] := by
      have := decPL_length m hdp; rw [hrl] at this; exact List.eq_nil_of_length_eq_zero this
    subst this
    rw [ConRon.Arena.classRead]
    exact RSim.pure_some ⟨⟨hS, IWGrow.refl m, rfl⟩, hJ⟩
  obtain ⟨k, hk⟩ : ∃ k, rl.toNat = k + 1 :=
    ⟨rl.toNat - 1, by have : rl.toNat ≠ 0 := fun e => hrl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hdpT := hrecs.1
  simp only [DecB] at hdpT
  rw [hk] at hdpT hdp
  obtain ⟨p0, rc0, rest, rfl, hp0T, hrcT, -⟩ := decPL_cons hdpT
  obtain ⟨hro, hp0⟩ := iwN_truncM_get hp0T
  obtain ⟨q, hqT, hcvT, hrPT⟩ := decRS_rP hrcT
  obtain ⟨hp0lt, hq⟩ := iwN_truncM_get hqT
  obtain ⟨hp1lt, hrP⟩ := iwN_truncM_get hrPT
  have hcv : decCVp m q = some rc0.cvR := (OMono.decCVp q).mono _ _ _ (IWGrow.refl m).truncExt hcvT
  rw [readW_ok (h := hrl)]
  rw [ConRon.Arena.classRead]
  have hrd0 := (iwN_rdW hp0 (by omega)).1
  rw [UInt64.ofNat_toNat] at hrd0
  have hrdq := iwN_rdW hq (by omega)
  have hqb : q < 2 ^ 64 := hrdq.2
  have hq3 : (UInt64.ofNat q).toNat + 3 < 2 ^ 64 := by
    rw [UInt64.toNat_ofNat_of_lt' hqb]
    have := hS.2.2.2.2.1
    obtain ⟨w, hw, -⟩ := hd?_some (decCV_type hcv)
    have := (Array.getElem?_eq_some_iff.mp hw).1
    simp only [erA] at this; omega
  obtain ⟨htyH, htyE⟩ := decCVp_type (q := UInt64.ofNat q)
    (by rw [UInt64.toNat_ofNat_of_lt' hqb]; exact hcv) hq3
  rw [hrd0, hrdq.1]
  rw [← htyE]
  refine RSim.bind (K := rdK1 cR N p vis nP ro rl (UInt64.ofNat p0)) rfl (hO.sim N hS hJ htyH) ?_
  rintro ⟨r1, m1⟩ o a1 - ⟨⟨hS1, hg1, ho⟩, hJ1⟩
  dsimp only at hS1 hg1 ho hJ1
  rcases o with _ | fb
  · rw [rdK1_fail (h := ho)]; exact RSim.pure_some ⟨⟨hS1, hg1, rfl⟩, hJ1⟩
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨h11, -, hbH, rfl⟩ := ho
  rw [drop3_headD] at hbH ⊢
  rw [rdK1_ok (h := by rw [h11]; decide)]
  have hrP1 : rdW (m1.arr64 IW) (UInt64.ofNat p0 + 1) = UInt64.ofNat rc0.rP := by
    have h := iwN_rdW_at (w := UInt64.ofNat p0) (k := 1) (m := m)
      (by rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; exact hrP) hsz
    rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at h
    rw [← h.1]; simp only [rdW]
    rw [show (UInt64.ofNat p0 + 1).toNat = p0 + 1 by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]; simp; omega,
      hg1.2.2.1 _ hp1lt]
  have hrPb : rc0.rP < 2 ^ 64 := (iwN_rdW hrP (by omega)).2
  rw [hrP1]
  have hts1 : (tsubW (UInt64.ofNat rc0.rP) nP).toNat = rc0.rP - nP.toNat := by
    by_cases hle : nP ≤ UInt64.ofNat rc0.rP
    · rw [tsubW_le _ _ hle, UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_ofNat_of_lt' hrPb]
    · rw [tsubW_gt _ _ hle]
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
      rw [UInt64.toNat_ofNat_of_lt' hrPb] at this; simp; omega
  have hsl := (slots_sims dn vis fe cR J hO p nP bs N).1 m1 a1 (tsubW (UInt64.ofNat rc0.rP) nP) 0 0 nP
    (r1.tail.tail.tail.headD 0) [] hS1 hJ1 hbH (hb.grow hg1) (by simp [decNL]) (by simp)
    (by rw [hts1]; have := nP.toNat_lt; omega)
  rw [hts1] at hsl
  try simp only [UInt64.toNat_zero] at hsl
  refine RSim.bind (K := rdK2 cR N nP ro rl) rfl hsl ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨⟨hS2, hg2, ho2⟩, hJ2⟩
  dsimp only at hS2 hg2 ho2 hJ2
  have hg12 := hg1.trans hg2
  rcases o with _ | slots
  · rw [rdK2_fail (h := ho2)]; exact RSim.pure_some ⟨⟨hS2, hg12, rfl⟩, hJ2⟩
  obtain ⟨h21, hsp⟩ := ho2
  rw [rdK2_ok (h := by rw [h21]; decide)]
  refine RSim.bindPure (K := rdK3) rfl (readFinW_sim dn vis fe cR J hO N m2 a2 nP _ _ ro rl slots _ hS2
    hJ2 hsp (hrecs.grow hg12)) ?_
  rintro ⟨r3, m3⟩ x a3 - ⟨⟨hS3, hg3, hd3⟩, hJ3⟩
  rw [rdK3_some]
  refine RSim.pure_some ⟨⟨hS3, hg12.trans hg3, ?_⟩, hJ3⟩
  cases x <;> exact hd3

end L.Ind

namespace L.Ind

open L.Arena

/-- **`class_read` refines `classRead` and keeps `AbsOK`**: `classRead_refines` with the program's
own `open_pis_at_fvars_f` (`opfF_ok`), so the walk memos are well formed after (no `AbsKeep`
premise). -/
theorem classRead_refinesA (p : Prog) (hP : ReadProg p) (hOpf : OpfF p) (N : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q nP ro rl : Word)
    (bs : BlockShape) (recs : List RecShape) (hS : StageR dn vis fe s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hb : BSOK s₀.mem q.toNat bs) (hrecs : RecsDec s₀.mem ro rl recs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_read" [q, vis, nP, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRead bs fe nP.toNat recs) a₀ ∧
      KP dn vis fe s₀.mem decRead (r, s'.mem) (AM.st (ConRon.Arena.classRead bs fe nP.toNat recs) a₀)
        (AM.res (ConRon.Arena.classRead bs fe nP.toNat recs) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classRead_spec p hP (realCall p) (realCall_spec p) N s₀ q vis nP ro rl) fun _ _ ⟨hl, hw⟩ =>
    let ⟨hok, hK, hA'⟩ := (readW_sim dn vis fe (realCall p) AbsOK (opfJ_real hOpf dn vis fe) N _ a₀ q nP
      ro rl bs recs hS hA hb hrecs).am hw
    ⟨hl, hok, hK, hA'⟩

end L.Ind

end

end
