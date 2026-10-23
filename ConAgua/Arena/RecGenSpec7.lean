import ConAgua.Arena.RecClassSpecJ
import ConAgua.Arena.RecGenSpec3
import ConAgua.Arena.IndRealAbsPos

/-!
# `RecGen`: `classRecTyOk` (lane `indproofs2`, helper `rec2`)
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Constants below the record top -/

theorem rec2DecCV_agree {a b : Array Word} {q T : Nat} (hag : ∀ i, i < T → b[i]? = a[i]?) (hq4 : q + 4 ≤ T)
    (hl : ∀ o l, nat? a (q + 1) = some o → nat? a (q + 2) = some l → o + l ≤ T ∨ l = 0) :
    decCV b q = decCV a q := by
  have hn : ∀ i, i < T → nat? b i = nat? a i := fun i hi => by simp only [nat?, hag i hi]
  have hh : ∀ {k : IdxKind} i, i < T → (hd? b i : Option (Idx k)) = hd? a i :=
    fun i hi => by simp only [hd?, hag i hi]
  simp only [decCV]
  rw [hh q (by omega), hh (q + 3) (by omega)]
  have hlist : (hlist? b (q + 1) : Option (List (Idx IdxKind.name))) = hlist? a (q + 1) := by
    simp only [hlist?]
    rw [hn (q + 1) (by omega), hn (q + 1 + 1) (by omega)]
    cases ho : nat? a (q + 1) with
    | none => simp
    | some o =>
      cases hl' : nat? a (q + 1 + 1) with
      | none => simp
      | some l =>
        try simp only [Option.bind_some]
        apply hslice?_congr
        intro j hj
        have := hl o l ho hl'
        exact hag (o + j) (by omega)
  rw [hlist]

/-- A constant record below the top decodes in the record pool in use. -/
theorem rec2DecCV_erecP {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv) (hq : CVExt m q) :
    decCV (erecP m) q = some cv := by
  rw [rec2DecCV_agree (a := erA m) (T := erTop m) (fun i hi => ?_) hq.1 hq.2]
  · exact h
  · simp only [erecP, erA, Array.getElem?_extract, erecTop, erTop] at hi ⊢
    simp only [Nat.zero_add, Array.getElem?_eq_none_iff, Array.size_extract]
    split <;> simp_all <;> omega

/-! ## `class_rec_ty_ok_guards` -/

def rgK (g k rc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if rdW (m1.arr64 IW) (rc + 3) ≠ (if rdW (m1.arr64 IW) (r1.headD 0 + 8) ≠ 0
        then rdW (m1.arr64 IW) (r1.headD 0 + 8) - 1 else k) then none
    else if rdW (m1.arr64 IW) (rc + 1) ≠ rdW (m1.arr64 IW) g + rdW (m1.arr64 IW) (g + 8) then none
    else if rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5) < rdW (m1.arr64 IW) (rc + 1)
      then none
    else if rdW (m1.arr64 IW) (rc + 2) ≠ rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5)
      then none
    else some ([0], m1)

/-- **The model of `class_rec_ty_ok_guards`.** -/
def rgW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, g, k, rc, c => rgK g k rc (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c)

theorem rgW_eq (n : Nat) (m : Mem) (g k rc c : Word) :
    rgW (n + 1) m g k rc c = rgK g k rc (tmaW n m (rdW (m.arr64 IW) (g + 3)) (rdW (m.arr64 IW) (g + 4)) c) := rfl

grind_pattern [ind_grind] rgW_eq => rgW (n + 1) m g k rc c

/-! ## `class_rec_ty_ok` -/

def rtoK5 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => if r5.headD 0 = 0 then none else some ([q], m5)

def rtoK4 (cR : CallM) (n : Nat) (vis cvRi gty q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => rtoK5 q (cR n "is_def_eq_core" [vis, 0, rdW (m4.arr64 EREC) (cvRi + 3), gty] m4)

def rtoK3 (cR : CallM) (n : Nat) (vis cvRi gty : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m3) => rtoK4 cR n vis cvRi gty q (ccoW cR n m3 vis q)

def rtoK2 (cR : CallM) (n : Nat) (vis rc cvRi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then none
    else rtoK3 cR n vis cvRi (r2.tail.headD 0)
      (cvNewW m2 (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc))
        (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 1)) (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 2))
        (r2.tail.headD 0))

def rtoK1 (cR : CallM) (n : Nat) (vis g rc cvRi c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => rtoK2 cR n vis rc cvRi (gtW n m1 g c)

/-- **The model of `class_rec_ty_ok`.** -/
def rtoW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, g, k, rc, cvRi, c => rtoK1 cR n vis g rc cvRi c (rgW n m g k rc c)

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis g k rc cvRi c gty q : Word) (r1 r2 r4 r5 : List Word)
theorem rtoW_eq : rtoW cR (n + 1) m vis g k rc cvRi c = rtoK1 cR n vis g rc cvRi c (rgW n m g k rc c) := rfl
theorem rtoK1_some : rtoK1 cR n vis g rc cvRi c (some (r1, m1)) = rtoK2 cR n vis rc cvRi (gtW n m1 g c) := rfl
theorem rtoK2_fail (h : r2.headD 0 = 0) : rtoK2 cR n vis rc cvRi (some (r2, m2)) = none := by
  rw [rtoK2, if_pos h]
theorem rtoK2_ok (h : r2.headD 0 ≠ 0) : rtoK2 cR n vis rc cvRi (some (r2, m2)) =
    rtoK3 cR n vis cvRi (r2.tail.headD 0)
      (cvNewW m2 (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc))
        (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 1)) (rdW (m2.arr64 EREC) (rdW (m2.arr64 IW) rc + 2))
        (r2.tail.headD 0)) := by
  rw [rtoK2, if_neg h]
theorem rtoK3_some : rtoK3 cR n vis cvRi gty (some (q, m3)) = rtoK4 cR n vis cvRi gty q (ccoW cR n m3 vis q) := rfl
theorem rtoK4_some : rtoK4 cR n vis cvRi gty q (some (r4, m4)) =
    rtoK5 q (cR n "is_def_eq_core" [vis, 0, rdW (m4.arr64 EREC) (cvRi + 3), gty] m4) := rfl
theorem rtoK5_fail (h : r5.headD 0 = 0) : rtoK5 q (some (r5, m5)) = none := by rw [rtoK5, if_pos h]
theorem rtoK5_ok (h : r5.headD 0 ≠ 0) : rtoK5 q (some (r5, m5)) = some ([q], m5) := by rw [rtoK5, if_neg h]
end arms

grind_pattern [ind_grind] rtoW_eq => rtoW cR (n + 1) m vis g k rc cvRi c
grind_pattern [ind_grind] rtoK1_some => rtoK1 cR n vis g rc cvRi c (some (r1, m1))
grind_pattern [ind_grind] rtoK2_fail => rtoK2 cR n vis rc cvRi (some (r2, m2))
grind_pattern [ind_grind] rtoK2_ok => rtoK2 cR n vis rc cvRi (some (r2, m2))
grind_pattern [ind_grind] rtoK3_some => rtoK3 cR n vis cvRi gty (some (q, m3))
grind_pattern [ind_grind] rtoK4_some => rtoK4 cR n vis cvRi gty q (some (r4, m4))
grind_pattern [ind_grind] rtoK5_fail => rtoK5 q (some (r5, m5))
grind_pattern [ind_grind] rtoK5_ok => rtoK5 q (some (r5, m5))

/-- The lookups `class_rec_ty_ok` needs. -/
structure RtoProg (p : Prog) extends GtProg p : Prop where
  ih : IhProg p
  ccoh : p.lookup "class_const_ok_header" = some classConstOkHeader
  cco : p.lookup "class_const_ok" = some classConstOkL
  era : p.lookup "erec_alloc" = some erecAlloc
  cvn : p.lookup "cv_new" = some cvNew
  rg : p.lookup "class_rec_ty_ok_guards" = some classRecTyOkGuards
  rto : p.lookup "class_rec_ty_ok" = some classRecTyOkL

theorem classRecTyOkGuards_spec (p : Prog) (h : RtoProg p) (n : Nat) (s₀ : St) (g k rc c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_ty_ok_guards" [g, k, rc, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rgW n s₀.mem g k rc c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rg]
  simp only [callFn, classRecTyOkGuards]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma h.na n] <;>
      finish (gen := 20) [rdW_eq, rgK]

theorem classRecTyOk_spec (p : Prog) (h : RtoProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (s₀ : St) (vis g k rc cvRi c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_ty_ok" [vis, g, k, rc, cvRi, c]
    ⦃fun r s' => LocEq s' s₀ ∧ rtoW cR n s₀.mem vis g k rc cvRi c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.rto]
  simp only [callFn, classRecTyOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRecTyOkGuards_spec p h n, classGenRecTy_spec p h.toGtProg n, cvNew_specW p h.era h.cvn n,
        classConstOk_spec p h.ih h.ccoh h.cco cR hcR n, hcR n "is_def_eq_core"] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5]

/-! ## Relational lemmas -/

theorem rec2DecRS_parts {m : Mem} {p : Nat} {RS : RecShape} (h : decRS m p = some RS) :
    ∃ q, iwN m p = some q ∧ decCVp m q = some RS.cvR ∧ iwN m (p + 1) = some RS.rP ∧
      iwN m (p + 2) = some RS.mI ∧ iwN m (p + 3) = some RS.tgt := by
  simp only [decRS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, rP, hrP, mI, hmI, tgt, htgt, rh, hrh, rfl⟩ := h
  exact ⟨q, hq, hcv, hrP, hmI, htgt⟩

theorem rec2W_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : (UInt64.ofNat a : Word) = UInt64.ofNat b) : a = b := by
  have := congrArg UInt64.toNat h
  rwa [UInt64.toNat_ofNat_of_lt' ha, UInt64.toNat_ofNat_of_lt' hb] at this

theorem rec2W_add (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((UInt64.ofNat a + UInt64.ofNat b : Word)).toNat = (a + b) % 2 ^ 64 := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' ha, UInt64.toNat_ofNat_of_lt' hb]

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-! ## The `abstract1` memo across `class_const_ok` -/

/-- `install_header` keeps the `abstract1` memo. -/
theorem ihHdrW_afr {n : Nat} {m m' : Mem} {vis q : Word} {r : List Word}
    (h : L.Arena.ihW n m vis q = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [L.Arena.ihW] at h
  | succ n =>
  simp only [L.Arena.ihW, L.Arena.ihK1.eq_def, L.Arena.ihK2.eq_def, L.Arena.ihK3.eq_def, L.Arena.ihK4.eq_def,
    L.Arena.ihK5.eq_def, L.Arena.ihK6.eq_def, L.Arena.ihK7.eq_def, L.Arena.ihK8.eq_def, L.Arena.ihK9.eq_def] at h
  afr_auto h [envFindW_afr, ipfF_afr, cvLpsA_afr, lbbF_afr, hffF_afr, stub_afr]

theorem ccoW_afr {n : Nat} {m m' : Mem} {vis q : Word} {r : List Word} (h : ccoW stubCall n m vis q = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [ccoW] at h
  | succ n =>
  simp only [ccoW, ccoK1.eq_def, ccoK2.eq_def, ccoK3.eq_def, stubCall] at h
  afr_auto h [ihHdrW_afr, stub_afr]

theorem rgW_sim {β γ : Type} (n : Nat) (m : Mem) (a : AState) (g k rc c : Word) (G : ClassGen)
    (RS : RecShape) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) m RS) (hA : AbsOK m)
    (K : Option (List Word × Mem) → Option β) (hK : K none = none) (rest : AM γ)
    (Q : β → AState → γ → Prop)
    (hrest : ∀ m1 a1, StageR dn vis fe m1 a1 → IWGrow m m1 → AbsOK m1 → RSim (K (some ([0], m1))) rest a1 Q) :
    RSim (K (rgW (n + 1) m g k rc c)) (do
      let ci ← ConRon.Arena.targetMajorAt G.cls c.toNat
      unless RS.tgt == ci.member.getD k.toNat do
        fail (.invalid "generated recursor: the recursor record's member is not its class's")
      unless RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + ci.nIdx do
        fail (.invalid "generated recursor: the recursor record's rule prefix or major index is \
          not the generated one")
      rest) a Q := by
  rw [rgW_eq]
  have hsz := hS.2.2.2.1
  have htop := hS.2.1
  obtain ⟨-, hgt, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4]
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by omega); omega
    · have := rec2DecB_PL_top hcls hl; omega
  refine RSim.bind (K := fun o => K (rgK g k rc o)) hK (RSim.withF (rec2SimTMA dn vis fe n m a _ _ c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)) (fun _ hb => tmaW_afr hb)) ?_
  rintro ⟨r1, m1⟩ tm a1 - ⟨⟨hS1, hg1, hTM, -⟩, hf1⟩
  dsimp only at hS1 hg1 hTM
  cases hr : rgK g k rc (some (r1, m1)) with
  | none => rw [hK]; exact RSim.none
  | some b =>
  have hb := hr
  simp only [rgK] at hb
  by_cases c1 : rdW (m1.arr64 IW) (rc + 3) ≠ (if rdW (m1.arr64 IW) (r1.headD 0 + 8) ≠ 0
      then rdW (m1.arr64 IW) (r1.headD 0 + 8) - 1 else k)
  · rw [if_pos c1] at hb; cases hb
  rw [if_neg c1] at hb
  by_cases c2 : rdW (m1.arr64 IW) (rc + 1) ≠ rdW (m1.arr64 IW) g + rdW (m1.arr64 IW) (g + 8)
  · rw [if_pos c2] at hb; cases hb
  rw [if_neg c2] at hb
  by_cases c3 : rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5) < rdW (m1.arr64 IW) (rc + 1)
  · rw [if_pos c3] at hb; cases hb
  rw [if_neg c3] at hb
  by_cases c4 : rdW (m1.arr64 IW) (rc + 2) ≠ rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5)
  · rw [if_pos c4] at hb; cases hb
  rw [if_neg c4] at hb
  cases hb
  have hsz1 := hS1.2.2.2.1
  obtain ⟨k8, hk8, hmem⟩ := decTM_member hTM
  obtain ⟨-, -, -, -, hni⟩ := rec2DecTM_parts hTM
  obtain ⟨e8, -⟩ := rec2RdN (w := r1.headD 0) (k := 8) hk8 hsz1
  obtain ⟨e5, -⟩ := rec2RdN (w := r1.headD 0) (k := 5) hni hsz1
  have k8lt := (iwN_rdW_at (w := r1.headD 0) (k := 8) hk8 hsz1).2
  have nilt := (iwN_rdW_at (w := r1.headD 0) (k := 5) hni hsz1).2
  simp only [show UInt64.ofNat 8 = (8 : Word) from rfl, show UInt64.ofNat 5 = (5 : Word) from rfl] at e8 e5
  obtain ⟨-, -, -, hrP, hmI, htgt⟩ := rec2DecRS_parts (hrc.stab (decRS_mono _) m1 hg1)
  obtain ⟨eP, -⟩ := rec2RdN (w := rc) (k := 1) hrP hsz1
  obtain ⟨eI, -⟩ := rec2RdN (w := rc) (k := 2) hmI hsz1
  obtain ⟨eT, -⟩ := rec2RdN (w := rc) (k := 3) htgt hsz1
  have rPlt := (iwN_rdW_at (w := rc) (k := 1) hrP hsz1).2
  have mIlt := (iwN_rdW_at (w := rc) (k := 2) hmI hsz1).2
  have tglt := (iwN_rdW_at (w := rc) (k := 3) htgt hsz1).2
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl] at eP eI eT
  obtain ⟨hnP, hsl⟩ := rec2CG_get (hG.stab (decCG_mono _) m1 hg1)
  obtain ⟨so, sl, hso, hsl', hsls⟩ := decAt_some hsl
  have hlen := decPL_length m1 hsls
  obtain ⟨eg, -⟩ := rec2RdN (w := g) (k := 0) (by simpa using hnP) hsz1
  obtain ⟨eg8, -⟩ := rec2RdN (w := g) (k := 8) (by simpa [Nat.add_assoc] using hsl') hsz1
  have nPlt := (iwN_rdW_at (w := g) (k := 0) (by simpa using hnP) hsz1).2
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
    show UInt64.ofNat 8 = (8 : Word) from rfl] at eg eg8
  rw [eT, e8] at c1
  rw [eP, eg, eg8] at c2
  rw [eP, e5] at c3
  rw [eI, eP, e5] at c4
  have sllt := (iwN_rdW_at (w := g) (k := 8) (by simpa [Nat.add_assoc] using hsl') hsz1).2
  -- the member guard
  have g1 : (RS.tgt == tm.member.getD k.toNat) = true := by
    rw [hmem]; simp only [decON]
    by_cases hz : k8 = 0
    · subst hz
      simp only [show (UInt64.ofNat 0 : Word) = 0 from rfl, ne_eq, not_true_eq_false, if_false,
        Decidable.not_not] at c1
      have : RS.tgt = k.toNat := by
        have := congrArg UInt64.toNat c1
        rwa [UInt64.toNat_ofNat_of_lt' tglt] at this
      simp [this]
    · have hz' : (UInt64.ofNat k8 : Word) ≠ 0 := fun e => hz (rec2W_inj k8lt (by decide) e)
      simp only [hz', ne_eq, not_false_eq_true, if_true, Decidable.not_not] at c1
      have e1 : (UInt64.ofNat k8 - 1 : Word) = UInt64.ofNat (k8 - 1) := by
        obtain ⟨j, rfl⟩ : ∃ j, k8 = j + 1 := ⟨k8 - 1, by omega⟩
        simp [UInt64.ofNat_add]
      rw [e1] at c1
      have := rec2W_inj tglt (by omega) c1
      simp [hz, this]
  -- the prefix and major index guards
  have hsl8 : sl = G.slots.length := hlen.symm
  have c2' := Decidable.of_not_not c2
  have hrPe : RS.rP = G.nP + G.slots.length := by
    have := congrArg UInt64.toNat c2'
    rw [UInt64.toNat_ofNat_of_lt' rPlt, rec2W_add _ _ nPlt sllt, hsl8] at this
    rw [this, Nat.mod_eq_of_lt hns]
  have hno : RS.rP + tm.nIdx < 2 ^ 64 := by
    have : ¬ (UInt64.ofNat RS.rP + UInt64.ofNat tm.nIdx : Word).toNat < (UInt64.ofNat RS.rP : Word).toNat :=
      fun x => c3 (UInt64.lt_iff_toNat_lt.mpr x)
    rw [rec2W_add _ _ rPlt nilt, UInt64.toNat_ofNat_of_lt' rPlt] at this
    omega
  have hmIe : RS.mI = RS.rP + tm.nIdx := by
    have := congrArg UInt64.toNat (Decidable.of_not_not c4)
    rw [UInt64.toNat_ofNat_of_lt' mIlt, rec2W_add _ _ rPlt nilt, Nat.mod_eq_of_lt hno] at this
    exact this
  have g2 : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx) = true := by
    simp [hrPe, hmIe]
  simp only [g1, g2, if_true, ite_true, pure_bind]
  exact hrest m1 a1 hS1 hg1 (hf1 hA)

/-- `class_rec_ty_ok`'s result: a constant record below the record top. -/
def decCVR (m' : Mem) (r : List Word) (cv : IConstantVal) : Prop :=
  decCVp m' (r.headD 0).toNat = some cv ∧ CVExt m' (r.headD 0).toNat

theorem rtoW_sim (n : Nat) (m : Mem) (a : AState) (g k rc cvRi c : Word) (G : ClassGen) (RS : RecShape)
    (CVRi : IConstantVal) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) m RS)
    (hcvR : ∀ q, iwN m rc.toNat = some q → CVExt m q)
    (hcvRi : DecB (fun m => decCVp m cvRi.toNat) m CVRi) (hA : AbsOK m) :
    RSim (rtoW stubCall n m vis g k rc cvRi c) (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a
      (fun b a' x => KP dn vis fe m decCVR b a' x ∧ AbsOK b.2) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [rtoW_eq]
  unfold ConRon.Arena.classRecTyOk
  cases n with
  | zero => exact RSim.none
  | succ n =>
  refine rgW_sim n m a g k rc c G RS hS hG hns hrc hA (rtoK1 stubCall (n + 1) vis g rc cvRi c) rfl _ _ ?_
  intro m1 a1 hS1 hg1 hA1
  rw [rtoK1_some]
  refine RSim.bind (K := rtoK2 stubCall (n + 1) vis rc cvRi) rfl
    (gtW_sim dn vis fe (n + 1) m1 a1 g c G hS1 (hG.grow (decCG_mono _) hg1) hns hA1) ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨⟨hS2, hg2, ho⟩, hA2⟩
  dsimp only at hS2 hg2 ho
  cases o with
  | none => rw [rtoK2_fail (h := ho)]; exact RSim.none
  | some gty =>
  obtain ⟨h21, hgH, hgd⟩ := ho
  rw [rtoK2_ok (h := by rw [h21]; decide)]
  subst hgd
  have hg12 := hg1.trans hg2
  obtain ⟨q0, hq0, -⟩ := rec2DecRS_parts (show decRS (truncM m) rc.toNat = some RS from hrc)
  obtain ⟨hrct, hq0m⟩ := rec2IwN_trunc hq0
  have hq2 : iwN m2 rc.toNat = some q0 := by rw [iwN_grow hg12 hrct]; exact hq0m
  obtain ⟨q0', hq0', hcv2, -⟩ := rec2DecRS_parts (hrc.stab (decRS_mono _) m2 hg12)
  rw [hq2] at hq0'; cases hq0'
  have hext2 := CVExt_grow hg12 (hcvR q0 hq0m)
  obtain ⟨erc, trc⟩ := rec2RdN (w := rc) (k := 0) (by simpa using hq2) hS2.2.2.2.1
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at erc
  rw [erc]
  refine RSim.lstep (K := rtoK3 stubCall (n + 1) vis cvRi (r2.tail.headD 0)) rfl fun ⟨q, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hq, htop3, hsl3, hdec3⟩ := cvNew_stage (cq := UInt64.ofNat q0) h3 hS2
    (by rw [trc]; exact hcv2) (by rw [trc]; exact hext2.1) (by rw [trc]; exact hext2.2) hgH
  rw [rtoK3_some]
  have hext3 : CVExt m3 q.toNat := ⟨by omega, fun o l ho hl => (hsl3 o l ho hl).imp_left fun h => Nat.le_trans h hg3.2.1⟩
  have hqb : q.toNat + 3 < 2 ^ 64 := by
    obtain ⟨-, hE1, -, hEs, -⟩ := hS3.2
    omega
  have hA3 := cvNewW_afr h3 hA2
  refine RSim.bind (K := rtoK4 stubCall (n + 1) vis cvRi (r2.tail.headD 0) q) rfl
    (RSim.withF (ccoW_sim dn vis fe (n + 1) m3 a2 q _ hS3 (rec2DecCV_erecP hdec3 hext3) hqb)
      (fun _ hb => ccoW_afr hb)) ?_
  rintro ⟨r4, m4⟩ u a4 - ⟨⟨hS4, hg4, -⟩, hf4⟩
  dsimp only at hS4 hg4
  rw [rtoK4_some]
  have hg14 := hg12.trans (hg3.trans hg4)
  have hri := hcvRi.stab (OMono.decCVp _) m4 hg14
  obtain ⟨wt, hwt, hwtH, hwtE⟩ := decCV_typeW hri
  have hEi := (Array.getElem?_eq_some_iff.mp hwt).1
  have hE64 := hS4.2.2.2.2.1
  have et : rdW (m4.arr64 EREC) (cvRi + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hEi ⊢; omega) hwt
  rw [et]
  have hi := (isDefEqCore_spec dn vis fe 0 wt (r2.tail.headD 0) hwtH hgH).sim hS4
  rw [show (0 : Word).toNat = 0 from rfl, ← hwtE] at hi
  refine RSim.bind (K := rtoK5 q) rfl (RSim.withF hi (fun _ hb => stub_afr hb)) ?_
  rintro ⟨r5, m5⟩ bb a5 - ⟨⟨hS5, hg5, hbb, -⟩, hf5⟩
  dsimp only at hS5 hg5 hbb
  by_cases h50 : r5.headD 0 = 0
  · rw [rtoK5_fail (h := h50)]; exact RSim.none
  rw [rtoK5_ok (h := h50)]
  have hbt : bb = true := by rw [← hbb]; simpa using h50
  subst hbt
  simp only [if_true]
  have hg35 := hg4.trans hg5
  refine RSim.pure_some ⟨⟨hS5, hg14.trans hg5, ?_, CVExt_grow hg35 hext3⟩, hf5 (hf4 hA3)⟩
  show decCVp m5 q.toNat = _
  rw [decCVp_grow_r hg35 hext3, hdec3]

/-- **`class_rec_ty_ok` refines `classRecTyOk`** (the generated type through `class_gen_rec_ty`'s
stubs, `class_const_ok`'s and `is_def_eq_core`): the result is the generated constant, a fresh record
below the record top. -/
@[refines ConRon.Arena.classRecTyOk]
theorem classRecTyOk_refines (p : Prog) (hp : RtoProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g k rc cvRi c : Word) (G : ClassGen)
    (RS : RecShape) (CVRi : IConstantVal) (hS : StageR dn vis fe s₀.mem a₀)
    (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrc : DecB (fun m => decRS m rc.toNat) s₀.mem RS)
    (hcvR : ∀ q, iwN s₀.mem rc.toNat = some q → CVExt s₀.mem q)
    (hcvRi : DecB (fun m => decCVp m cvRi.toNat) s₀.mem CVRi) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_ty_ok" [vis, g, k, rc, cvRi, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀ ∧
      KP dn vis fe s₀.mem decCVR (r, s'.mem)
        (AM.st (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀)
        (AM.res (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classRecTyOk_spec p hp stubCall (stubCall_spec p) n s₀ vis g k rc cvRi c) fun _ _ ⟨hl, hw⟩ =>
    let h := (rtoW_sim (dn := dn) (vis := vis) (fe := fe) n _ a₀ g k rc cvRi c G RS CVRi hS hG hns hrc
      hcvR hcvRi hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end sims

end L.Ind
