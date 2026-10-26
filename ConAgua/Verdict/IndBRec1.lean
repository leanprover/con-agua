import ConAgua.Arena.IndT.CheckIndDecl
import ConAgua.Verdict.IndE

/-!
# Error refinements of the recursor generation's leaves (lane `verdicts-b`, helper `ib`)

`class_key_of`, ... : a failing call of class `1`/`2` claims that the twin fails with that class.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model classKeyOfE_spec (p : Prog) (hf : p.lookup "class_key_of" = some classKeyOfL)
  fns [hf ↦ classKeyOfE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] heartbeats 400000 errors

section kof
variable {p : Prog} (L : KofProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
include L

/-- **`class_key_of`'s error refinement** (the hypotheses of `classKeyOf_refines`): a failing call of
class `1`/`2` (the one reject site, the major's parameters mentioning more than the recursor's;
the callees `class_key_canon`, `class_key_of_closed` are outside the verdict closure) claims the
twin's `classKeyOf` fails. -/
theorem classKeyOf_claim (hnv : closedNV p _root_.L.Checker.nvFns = true) (k : Nat) (s₀ : St)
    (a₀ : AState) (nP po pl key : Word) (pfvs : List EIdx) (ck : ClassKey)
    (hS : StageR dn vis fe s₀.mem a₀) (hpf : decHL s₀.mem po.toNat pl.toNat = some pfvs)
    (hpb : po.toNat + pl.toNat ≤ iwTop s₀.mem) (hk : DecB (fun m => decCK m key.toNat) s₀.mem ck)
    (hP : PosMR s₀.mem) :
    CoreSpecE p (k + 2) "class_key_of" [nP, po, pl, key] (ConRon.Arena.classKeyOf nP.toNat pfvs ck)
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (classKeyOfE_spec p L.kof (k + 2) ⟨s₀.mem, Locals.init []⟩ nP po pl key)
    hc (Err.code_ne_of_cls hk0)
  rw [classKeyOfE.arm1] at hW
  cases h1 : callE p (k + 1) "class_key_canon" [po, pl, key] s₀.mem with
  | error e1 =>
    rw [h1, classKeyOfE.k_class_key_canon.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  obtain ⟨s1, hs1, -, hm1⟩ := triple_of_callW (kc_spec L k ⟨s₀.mem, Locals.init []⟩ po pl key)
    (callW_of_callE h1)
  subst hs1
  obtain ⟨x1, a1, hrun1, hd1, hb1, hds1, hS1, hg1, hP1⟩ :=
    kcW_ok dn fe vis k s₀.mem _ a₀ po pl key r1 pfvs ck hm1 hS hpf hpb hk hP
  have htop1 : iwTop s1.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hd1
  obtain ⟨-, -, -, -, hds, -, -⟩ := pos2_nk_fields hnk htop1
  rw [h1, classKeyOfE.k_class_key_canon.eq_2] at hW
  refine ErrClaim.bind_right hrun1 ?_
  cases h2 : callE p (k + 1) "class_key_of_closed"
      [nP, rdW (s1.mem.arr64 IW) (r1.headD 0 + 2), rdW (s1.mem.arr64 IW) (r1.headD 0 + 3)] s1.mem with
  | error e2 =>
    rw [h2, classKeyOfE.k_class_key_of_closed.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hm2⟩ := triple_of_callW (ckc2_spec L (k + 1) ⟨s1.mem, Locals.init []⟩ nP _ _)
    (callW_of_callE h2)
  subst hs2
  obtain ⟨b, a2, hrun2, hS2, hg2, hb2, -⟩ := ckc2W_ok dn fe vis (k + 1) s1.mem _ a1 nP _ _ nk.ds r2 hm2 hS1 hds
    (by omega) hds1
  by_cases h0 : r2.headD 0 = 0
  · rw [h2, classKeyOfE.k_class_key_of_closed.abort1 p _ r2 _ h0] at hW
    cases hW
    have hbf : b = false := by
      rw [← hb2, h0]; rfl
    subst hbf
    refine ErrClaim.bind_right hrun2 ?_
    exact ErrClaim.fail _ _ rfl
  · rw [h2, classKeyOfE.k_class_key_of_closed.arm1 p _ r2 _ h0] at hW
    cases hW
end kof


l_model classMinorSlotE_spec (p : Prog) (hf : p.lookup "class_minor_slot" = some classMinorSlotL)
  fns [hf ↦ classMinorSlotE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`class_minor_slot`'s error refinement** (the hypotheses of `classMinorSlot_refines`): the
scan `class_minor_slot_go` is outside the verdict closure; the one reject site (not exactly one
minor premise) means the twin's hit list is not a singleton. -/
theorem classMinorSlot_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hgo : p.lookup "class_minor_slot_go" = some classMinorSlotGo)
    (hp : p.lookup "class_minor_slot" = some classMinorSlotL) (n : Nat) (s₀ : St) (a₀ : AState)
    (rd c cc : Word) (R : ClassRead) (hR : decCR s₀.mem rd.toNat = some R) (hcc : cc.toNat < 2 ^ 32)
    (hsz : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) :
    CoreSpecE p (n + 1) "class_minor_slot" [rd, c, cc]
      (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (classMinorSlotE_spec p hp (n + 1) ⟨s₀.mem, Locals.init []⟩ rd c cc)
    hc (Err.code_ne_of_cls hk0)
  simp only [classMinorSlotE] at hW
  cases h1 : callE p n "class_minor_slot_go"
      [rdW (s₀.mem.arr64 IW) rd, rdW (s₀.mem.arr64 IW) (rd + 1), 0, c, cc, 0, 0, 0, 0] s₀.mem with
  | error e1 =>
    rw [h1, classMinorSlotE.k_class_minor_slot_go.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q =>
  obtain ⟨r, m1⟩ := q
  by_cases hx : r.headD 0 ≠ 1
  · rw [h1, classMinorSlotE.k_class_minor_slot_go.abort1 p r m1 hx] at hW
    cases hW
    obtain ⟨s', -, -, -, x, y, z, w, hg, rfl⟩ := triple_of_callW
      (classMinorSlotGo_spec p hgo n ⟨s₀.mem, Locals.init []⟩ _ _ 0 c cc 0 0 0 0) (callW_of_callE h1)
    simp only [List.headD_cons] at hx
    have hR' := hR
    simp only [decCR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hR'
    obtain ⟨slots, hsl, rcs, -, hRe⟩ := hR'
    have hRs : R.slots = slots := by rw [← hRe]
    obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hsl
    have hrd64 : rd.toNat < 2 ^ 64 := rd.toNat_lt
    have ho' := iwN_rdW ho hrd64
    rw [UInt64.ofNat_toNat] at ho'
    have hl' := iwN_off (k := 1) hl (by have := iwN_lt hl; omega)
    rw [show UInt64.ofNat 1 = 1 from rfl, UInt64.ofNat_toNat] at hl'
    have hl1 : rdW (s₀.mem.arr64 IW) (rd + 1) = UInt64.ofNat l := hl'.2
    simp only at hg
    rw [ho'.1, hl1] at hg
    have hol : o + l < 2 ^ 64 := by
      rcases decPL_le hdec with h0 | h0
      · have : o < 2 ^ 64 := ho'.2
        omega
      · omega
    have hlz : l < 2 ^ 64 := (iwN_rdW hl (by have := iwN_lt hl; omega)).2
    have hos : o < 2 ^ 64 := ho'.2
    have hg2 := classMinorSlotGoW_ok n s₀.mem (UInt64.ofNat o) (UInt64.ofNat l) 0 c cc 0 0 0 0 x y z w
      slots hg
      (by simpa [UInt64.toNat_ofNat_of_lt' hos, UInt64.toNat_ofNat_of_lt' hlz] using hdec) hcc hsz
      (by simp [UInt64.toNat_ofNat_of_lt' hos, UInt64.toNat_ofNat_of_lt' hlz]; omega)
      (by simp [UInt64.toNat_ofNat_of_lt' hlz]; omega) (by simp [UInt64.toNat_ofNat_of_lt' hlz]; omega)
    obtain ⟨g1, -, -⟩ := hg2
    simp only [UInt64.toNat_zero, Nat.zero_add] at g1
    rw [← hRs] at g1
    have hlen : (hitsFrom c.toNat (decI cc) 0 R.slots).length ≠ 1 := by
      intro h1'
      apply hx
      have : x.toNat = (1 : Word).toNat := by rw [g1, h1']; rfl
      exact UInt64.toNat_inj.mp this
    have hits := hitsFrom_eq c.toNat (decI cc) 0 R.slots
    simp only [Nat.zero_add] at hits
    show ErrClaim (ConRon.Arena.classMinorSlot R c.toNat (decI cc)) a₀ _
    simp only [ConRon.Arena.classMinorSlot]
    erw [hits]
    match hh : hitsFrom c.toNat (decI cc) 0 R.slots, hlen with
    | [], _ => exact ErrClaim.fail _ _ (by decide)
    | _ :: _ :: _, _ => exact ErrClaim.fail _ _ (by decide)
  · rw [h1, classMinorSlotE.k_class_minor_slot_go.arm1 p r m1 (by simpa using hx)] at hW
    cases hW


l_model classRecTyOkGuardsE_spec (p : Prog) (hf : p.lookup "class_rec_ty_ok_guards" = some classRecTyOkGuards)
  fns [hf ↦ classRecTyOkGuardsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem memGuard_iff (tgt k8 : Nat) (k : Word) (ht : tgt < 2 ^ 64) (hk8 : k8 < 2 ^ 64) :
    (UInt64.ofNat tgt = (if (UInt64.ofNat k8 : Word) ≠ 0 then (UInt64.ofNat k8 : Word) - 1 else k)) ↔
      (tgt == (decON k8).getD k.toNat) = true := by
  by_cases hz : k8 = 0
  · subst hz
    simp only [show (UInt64.ofNat 0 : Word) = 0 from rfl, ne_eq, not_true_eq_false, ite_false, decON,
      ite_true, Option.getD_none, beq_iff_eq]
    constructor
    · intro h; have := congrArg UInt64.toNat h; rwa [UInt64.toNat_ofNat_of_lt' ht] at this
    · intro h; rw [h]; exact UInt64.ofNat_toNat
  · have hz' : (UInt64.ofNat k8 : Word) ≠ 0 := fun e => hz (rec2W_inj hk8 (by decide) e)
    have e1 : (UInt64.ofNat k8 - 1 : Word) = UInt64.ofNat (k8 - 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k8 = j + 1 := ⟨k8 - 1, by omega⟩
      simp [UInt64.ofNat_add]
    simp only [hz', ne_eq, not_false_eq_true, ite_true, e1, decON, hz, ite_false, Option.getD_some, beq_iff_eq]
    constructor
    · intro h; exact rec2W_inj ht (by omega) h
    · intro h; rw [h]

section rg
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **A passing guard run** (`rgW_sim`'s facts, for the error claims of the steps after the guards):
the twin's `targetMajorAt` ran ok, and both of its guards hold. -/
theorem rgW_pass (n : Nat) (m : Mem) (a : AState) (g k rc c : Word) (G : ClassGen)
    (RS : RecShape) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) m RS) (hA : AbsOK m)
    (rg : List Word) (mg : Mem) (h : rgW (n + 1) m g k rc c = some (rg, mg)) :
    ∃ tm a1, (ConRon.Arena.targetMajorAt G.cls c.toNat).run a = .ok (tm, a1) ∧
      StageR dn vis fe mg a1 ∧ IWGrow m mg ∧ AbsOK mg ∧
      (RS.tgt == tm.member.getD k.toNat) = true ∧
      (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx) = true := by
  rw [rgW_eq] at h
  have hsz := hS.2.2.2.1
  have htop := hS.2.1
  obtain ⟨-, hgt, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4] at h
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by omega); omega
    · have := rec2DecB_PL_top hcls hl; omega
  obtain ⟨⟨r1, m1⟩, hT, h⟩ := of_K h rfl
  obtain ⟨tm, a1, hrun1, hS1, hg1, hTM, -⟩ := rec2SimTMA dn vis fe n m a (UInt64.ofNat o3) (UInt64.ofNat l3) c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3) (r1, m1) hT
  dsimp only at hS1 hg1 hTM
  have hb := h
  simp only [rgK] at hb
  obtain ⟨c1, hb⟩ := of_ite_none hb
  obtain ⟨c2, hb⟩ := of_ite_none hb
  obtain ⟨c3, hb⟩ := of_ite_none hb
  obtain ⟨c4, hb⟩ := of_ite_none hb
  obtain ⟨-, hmg⟩ := Prod.mk.inj (Option.some.inj hb)
  subst hmg
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
  exact ⟨tm, a1, hrun1, hS1, hg1, tmaW_afr hT hA, g1, g2⟩


/-- **`class_rec_ty_ok_guards`' error claim**, in the shape of `rgW_sim`: a failing guard run of class
`1`/`2` claims that the twin's `classRecTyOk` prefix (the member and the rule prefix guards, then
the `rest`) fails. -/
theorem rgE_claim {γ : Type} {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (h : RtoProg p)
    (n : Nat) (m : Mem) (a : AState) (g k rc c : Word) (G : ClassGen)
    (RS : RecShape) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (_hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) m RS) (_hA : AbsOK m)
    (rest : AM γ) (e : Err)
    (he : classRecTyOkGuardsE p (n + 1) m g k rc c = .error e) :
    ErrClaim (do
      let ci ← ConRon.Arena.targetMajorAt G.cls c.toNat
      unless RS.tgt == ci.member.getD k.toNat do
        fail (.invalid "generated recursor: the recursor record's member is not its class's")
      unless RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + ci.nIdx do
        fail (.invalid "generated recursor: the recursor record's rule prefix or major index is \
          not the generated one")
      rest) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hsz := hS.2.2.2.1
  have htop := hS.2.1
  obtain ⟨-, hgt, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by omega); omega
    · have := rec2DecB_PL_top hcls hl; omega
  rw [classRecTyOkGuardsE.arm1, e3, e4] at he
  cases h1 : callE p n "target_major_at" [UInt64.ofNat o3, UInt64.ofNat l3, c] m with
  | error e1 =>
    rw [h1, classRecTyOkGuardsE.k_target_major_at.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  obtain ⟨s1, hs1, -, hmod⟩ := triple_of_callW
    (targetMajorAt_spec p h.alloc h.pw h.mtm h.tmd h.tma h.na n ⟨m, Locals.init []⟩ _ _ c)
    (callW_of_callE h1)
  obtain ⟨tm, a1, hrun1, hS1, hg1, hTM, -⟩ := rec2SimTMA dn vis fe n m a (UInt64.ofNat o3) (UInt64.ofNat l3) c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3) (r1, m1) (by rw [← hs1]; exact hmod)
  dsimp only at hS1 hg1 hTM
  refine ErrClaim.bind_right hrun1 ?_
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
  have sllt := (iwN_rdW_at (w := g) (k := 8) (by simpa [Nat.add_assoc] using hsl') hsz1).2
  have hsl8 : sl = G.slots.length := hlen.symm
  have hmg := memGuard_iff RS.tgt k8 k tglt k8lt
  rw [← hmem] at hmg
  rw [h1] at he
  have key : ∀ memv : Word, memv = (if (UInt64.ofNat k8 : Word) ≠ 0 then (UInt64.ofNat k8 : Word) - 1 else k) →
      classRecTyOkGuardsE.j1 p g rc (r1.headD 0) memv m1 = .error e → ErrClaim (do
      unless RS.tgt == tm.member.getD k.toNat do
        fail (.invalid "generated recursor: the recursor record's member is not its class's")
      unless RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx do
        fail (.invalid "generated recursor: the recursor record's rule prefix or major index is \
          not the generated one")
      rest) a1 e := by
    intro memv hmv hj
    by_cases c1 : rdW (m1.arr64 IW) (rc + 3) = memv
    · by_cases c2 : rdW (m1.arr64 IW) (rc + 1) = rdW (m1.arr64 IW) g + rdW (m1.arr64 IW) (g + 8)
      · by_cases c3 : rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5) <
            rdW (m1.arr64 IW) (rc + 1)
        · rw [classRecTyOkGuardsE.j1.abort3 p g rc _ memv m1 c1 c2 c3] at hj
          cases hj
          exact ErrClaim.of_cls0 rfl
        · by_cases c4 : rdW (m1.arr64 IW) (rc + 2) = rdW (m1.arr64 IW) (rc + 1) + rdW (m1.arr64 IW) (r1.headD 0 + 5)
          · rw [classRecTyOkGuardsE.j1.arm1 p g rc _ memv m1 c1 c2 c3 c4] at hj
            cases hj
          · rw [classRecTyOkGuardsE.j1.abort4 p g rc _ memv m1 c1 c2 c3 c4] at hj
            cases hj
            have g1t : (RS.tgt == tm.member.getD k.toNat) = true := by
              apply hmg.mp; rw [← hmv, ← eT]; exact c1
            have g2f : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx) = false := by
              cases hh : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx)
              · rfl
              · exfalso
                simp only [Bool.and_eq_true, beq_iff_eq] at hh
                apply c4
                rw [eI, eP, e5, hh.2, UInt64.ofNat_add]
            simp only [g1t, g2f, Bool.false_eq_true, ite_true, ite_false]
            exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
      · rw [classRecTyOkGuardsE.j1.abort2 p g rc _ memv m1 c1 c2] at hj
        cases hj
        have g1t : (RS.tgt == tm.member.getD k.toNat) = true := by
          apply hmg.mp; rw [← hmv, ← eT]; exact c1
        have g2f : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx) = false := by
          cases hh : (RS.rP == G.nP + G.slots.length && RS.mI == RS.rP + tm.nIdx)
          · rfl
          · exfalso
            simp only [Bool.and_eq_true, beq_iff_eq] at hh
            apply c2
            rw [eP, eg, eg8, hh.1, ← hsl8, UInt64.ofNat_add]
        simp only [g1t, g2f, Bool.false_eq_true, ite_true, ite_false]
        exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
    · rw [classRecTyOkGuardsE.j1.abort1 p g rc _ memv m1 c1] at hj
      cases hj
      rw [eT, hmv] at c1
      have g1f : (RS.tgt == tm.member.getD k.toNat) = false := by
        cases hh : (RS.tgt == tm.member.getD k.toNat)
        · rfl
        · exact absurd (hmg.mpr hh) c1
      simp only [g1f, Bool.false_eq_true, ite_false]
      exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
  by_cases hmz : rdW (m1.arr64 IW) (r1.headD 0 + 8) ≠ 0
  · rw [classRecTyOkGuardsE.k_target_major_at.arm1 p g k rc r1 m1 hmz] at he
    refine key _ ?_ he
    rw [e8] at hmz ⊢
    simp [hmz]
  · rw [classRecTyOkGuardsE.k_target_major_at.arm2 p g k rc r1 m1 (by simpa using hmz)] at he
    refine key _ ?_ he
    rw [e8] at hmz
    simp [hmz]

end rg

end L.Ind
