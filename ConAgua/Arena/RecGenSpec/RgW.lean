import ConAgua.Arena.RecClassSpec.GtProg
import ConAgua.Arena.RecClassSpec.MkTMWAfr
import ConAgua.Arena.RecClassSpec.Rec2SimTMA
import ConAgua.Arena.RecGenSpec.CkcW
import ConAgua.Arena.RecGenSpec.ClassConstOkHeader

/-!
# RgW

`rec2DecCV_agree`, `rgK`, `rgW`, `rgW_eq`, `rtoK5`, `rtoK4` and the lemmas only they use.
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

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis g k rc cvRi c gty q : Word) (r1 r2 r4 r5 : List Word)
theorem rtoK2_fail (h : r2.headD 0 = 0) : rtoK2 cR n vis rc cvRi (some (r2, m2)) = none := by
  rw [rtoK2, ite_eq_left h]
theorem rtoK5_fail (h : r5.headD 0 = 0) : rtoK5 q (some (r5, m5)) = none := by rw [rtoK5, ite_eq_left h]
end arms

grind_pattern [ind_grind] rtoK2_fail => rtoK2 cR n vis rc cvRi (some (r2, m2))
grind_pattern [ind_grind] rtoK5_fail => rtoK5 q (some (r5, m5))
/-- The lookups `class_rec_ty_ok` needs. -/
structure RtoProg (p : Prog) : Prop extends GtProg p where
  ih : IhProg p
  ccoh : p.lookup "class_const_ok_header" = some classConstOkHeader
  cco : p.lookup "class_const_ok" = some classConstOkL
  era : p.lookup "erec_alloc" = some erecAlloc
  cvn : p.lookup "cv_new" = some cvNew
  rg : p.lookup "class_rec_ty_ok_guards" = some classRecTyOkGuards
  rto : p.lookup "class_rec_ty_ok" = some classRecTyOkL

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

/-- A `RSim` whose post also records the twin's run. -/
theorem RSim.withRun {β α : Type} {o : Option β} {op : AM α} {a : AState}
    {Q : β → AState → α → Prop} (h : RSim o op a Q) :
    RSim o op a (fun b a' x => Q b a' x ∧ op.run a = .ok (x, a')) := by
  intro b hb
  obtain ⟨x, a', hr, hq⟩ := h b hb
  exact ⟨x, a', hr, hq, hr⟩

/-- `class_rec_ty_ok_guards` (the continuation gets the twin's run of `targetMajorAt`, from which a
caller carrying con-ron's invariant gets it across: lane `indstaget`). -/
theorem rgW_sim {β γ : Type} (n : Nat) (m : Mem) (a : AState) (g k rc c : Word) (G : ClassGen)
    (RS : RecShape) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) m RS) (hA : AbsOK m)
    (K : Option (List Word × Mem) → Option β) (hK : K none = none) (rest : AM γ)
    (Q : β → AState → γ → Prop)
    (hrest : ∀ m1 a1 tm, (ConRon.Arena.targetMajorAt G.cls c.toNat).run a = .ok (tm, a1) →
      StageR dn vis fe m1 a1 → IWGrow m m1 → AbsOK m1 → RSim (K (some ([0], m1))) rest a1 Q) :
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
  refine RSim.bind (K := fun o => K (rgK g k rc o)) hK (RSim.withRun (RSim.withF (rec2SimTMA dn vis fe n m a _ _ c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)) (fun _ hb => tmaW_afr hb))) ?_
  rintro ⟨r1, m1⟩ tm a1 - ⟨⟨⟨hS1, hg1, hTM, -⟩, hf1⟩, hrun1⟩
  dsimp only at hS1 hg1 hTM
  cases hr : rgK g k rc (some (r1, m1)) with
  | none => rw [hK]; exact RSim.none
  | some b =>
  have hb := hr
  simp only [rgK] at hb
  obtain ⟨c1, hb⟩ := of_ite_none hb
  obtain ⟨c2, hb⟩ := of_ite_none hb
  obtain ⟨c3, hb⟩ := of_ite_none hb
  obtain ⟨c4, hb⟩ := of_ite_none hb
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
      simp only [show (UInt64.ofNat 0 : Word) = 0 from rfl, ne_eq, not_true_eq_false, ite_false,
        Decidable.not_not] at c1
      have := congrArg UInt64.toNat c1
      rw [UInt64.toNat_ofNat_of_lt' tglt] at this
      simp [this]
    · have hz' : (UInt64.ofNat k8 : Word) ≠ 0 := fun e => hz (rec2W_inj k8lt (by decide) e)
      simp only [hz', ne_eq, not_false_eq_true, ite_true, Decidable.not_not] at c1
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
  simp only [g1, g2, ite_true]
  exact hrest m1 a1 tm hrun1 hS1 hg1 (hf1 hA)

/-- `class_rec_ty_ok`'s result: a constant record below the record top. -/
def decCVR (m' : Mem) (r : List Word) (cv : IConstantVal) : Prop :=
  decCVp m' (r.headD 0).toNat = some cv ∧ CVExt m' (r.headD 0).toNat

end sims

end L.Ind

end
