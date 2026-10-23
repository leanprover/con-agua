import ConAgua.Arena.RecGenSpec7

/-!
# `RecGen`: `classRecTysOk` (lane `indproofs2`, helper `rec2`)
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The model -/

def rtsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0, r3.tail.headD 0], m3)

def rtsK2 (n : Nat) (x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => rtsK3 (consW n m2 x (r2.headD 0) (r2.tail.headD 0))

mutual
/-- **The model of `class_rec_tys_ok`.** -/
def rtsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, g, k, ro, rl, vo, vl, co, cl =>
    if rl = 0 then some ([0, 0], m)
    else if vl = 0 ∨ cl = 0 then none
    else rtsK1 cR n vis g k ro rl vo vl co cl
      (rtoW cR n m vis g k (rdW (m.arr64 IW) ro) (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co))
def rtsK1 (cR : CallM) (n : Nat) (vis g k ro rl vo vl co cl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    rtsK2 n (r1.headD 0) (rtsW cR n m1 vis g k (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1))
end

section arms
variable (cR : CallM) (n : Nat) (m m1 m2 m3 : Mem) (vis g k ro rl vo vl co cl x : Word) (r1 r2 r3 : List Word)
theorem rtsW_nil (h : rl = 0) : rtsW cR (n + 1) m vis g k ro rl vo vl co cl = some ([0, 0], m) := by
  simp [rtsW, h]
theorem rtsW_short (h : ¬ rl = 0) (h2 : vl = 0 ∨ cl = 0) : rtsW cR (n + 1) m vis g k ro rl vo vl co cl = none := by
  simp only [rtsW]; rw [if_neg h, if_pos h2]
theorem rtsW_cons (h : ¬ rl = 0) (h2 : ¬ (vl = 0 ∨ cl = 0)) : rtsW cR (n + 1) m vis g k ro rl vo vl co cl =
    rtsK1 cR n vis g k ro rl vo vl co cl
      (rtoW cR n m vis g k (rdW (m.arr64 IW) ro) (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)) := by
  simp only [rtsW]; rw [if_neg h, if_neg h2]
theorem rtsK1_some : rtsK1 cR n vis g k ro rl vo vl co cl (some (r1, m1)) =
    rtsK2 n (r1.headD 0) (rtsW cR n m1 vis g k (ro + 1) (rl - 1) (vo + 1) (vl - 1) (co + 1) (cl - 1)) := by
  rw [rtsK1]
theorem rtsK2_some : rtsK2 n x (some (r2, m2)) = rtsK3 (consW n m2 x (r2.headD 0) (r2.tail.headD 0)) := rfl
theorem rtsK3_some : rtsK3 (some (r3, m3)) = some ([r3.headD 0, r3.tail.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] rtsW_nil => rtsW cR (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsW_short => rtsW cR (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsW_cons => rtsW cR (n + 1) m vis g k ro rl vo vl co cl
grind_pattern [ind_grind] rtsK1_some => rtsK1 cR n vis g k ro rl vo vl co cl (some (r1, m1))
grind_pattern [ind_grind] rtsK2_some => rtsK2 n x (some (r2, m2))
grind_pattern [ind_grind] rtsK3_some => rtsK3 (some (r3, m3))

/-- The lookups `class_rec_tys_ok` needs. -/
structure RtsProg (p : Prog) extends RtoProg p : Prop where
  cons : p.lookup "sl_cons" = some slCons
  rts : p.lookup "class_rec_tys_ok" = some classRecTysOkL

theorem classRecTysOk_spec (p : Prog) (h : RtsProg p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) :
    ∀ (s₀ : St) (vis g k ro rl vo vl co cl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_tys_ok" [vis, g, k, ro, rl, vo, vl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ rtsW cR n s₀.mem vis g k ro rl vo vl co cl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis g k ro rl vo vl co cl
    rw [invoke_eq _ h.rts]; simp only [callFn, classRecTysOkL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis g k ro rl vo vl co cl
    rw [invoke_eq _ h.rts]
    simp only [callFn, classRecTysOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRecTyOk_spec p h.toRtoProg cR hcR n, slCons_specW p h.alloc h.copy h.cons n, ih] <;>
      finish (gen := 20) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8]

/-! ## Relational lemma -/

open Classical in
/-- A constant record below the record top, decoded. -/
noncomputable def decCVX (m : Mem) (p : Nat) : Option IConstantVal :=
  if CVExt m p then decCVp m p else none

theorem decCVX_stab {m : Mem} {p : Nat} {cv : IConstantVal} (h1 : decCVp m p = some cv)
    (h2 : CVExt m p) : StabD (fun m => decCVX m p) m cv := by
  intro m'' hg
  simp only [decCVX, if_pos (CVExt_grow hg h2)]
  rw [decCVp_grow_r hg h2, h1]

theorem RecsOK_tail {m : Mem} {ro rl : Nat} {cv : IConstantVal} {cvs : List IConstantVal}
    (h : RecsOK m ro (rl + 1) (cv :: cvs)) : RecsOK m (ro + 1) rl cvs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by simpa using h2, fun j hj => ?_⟩
  obtain ⟨p0, q, cv', hp0, hp1, hq, hcv, hext, hcvs⟩ := h3 (j + 1) (by omega)
  exact ⟨p0, q, cv', by rw [show ro + 1 + j = ro + (j + 1) by omega]; exact hp0, hp1, hq, hcv, hext,
    by simpa using hcvs⟩

/-- `class_rec_tys_ok`'s result: a stable slice of constant records below the record top. -/
def decCVS (m' : Mem) (r : List Word) (xs : List IConstantVal) : Prop :=
  SPL decCVX m' (r.headD 0).toNat (r.tail.headD 0).toNat xs

theorem rec2ToNat_succ {o : Word} {i : Nat} (h : o.toNat ≤ i) (hi : i < 2 ^ 64 - 1) :
    (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega

theorem rec2ToNat_pred {l : Word} (h : l ≠ 0) : (l - 1).toNat = l.toNat - 1 := by
  have : l.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp

theorem rtsW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g k : Word) (G : ClassGen)
    (hns : G.nP + G.slots.length < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (ro rl vo vl co cl : Word) (rcs : List RecShape) (cvs : List IConstantVal)
      (cs : List Nat), StageR dn vis fe m a → DecB (fun m => decCG m g.toNat) m G →
    DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) m rcs →
    RecsOK m ro.toNat rl.toNat (rcs.map (·.cvR)) →
    DecB (fun m => decPL m (decCVp m) vo.toNat vl.toNat) m cvs →
    DecB (fun m => decNL m co.toNat cl.toNat) m cs → AbsOK m →
    RSim (rtsW stubCall n m vis g k ro rl vo vl co cl) (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a
      (fun b a' x => KP dn vis fe m decCVS b a' x ∧ AbsOK b.2) := by
  induction n with
  | zero => intros; intro b hb; simp [rtsW] at hb
  | succ n ih =>
  intro m a ro rl vo vl co cl rcs cvs cs hS hG hrcs hok hcvs hcs hA
  have hsz := hS.2.2.2.1
  have htop := hS.2.1
  by_cases hrl : rl = 0
  · rw [rtsW_nil (h := hrl)]
    have : rcs = [] := by
      have := decPL_length _ (hrcs.get (OMono.decPL (fun q => decRS_mono q) _ _))
      rw [hrl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRecTysOk
    exact RSim.pure_some ⟨⟨hS, IWGrow.refl m, by simpa [decCVS] using SPL.nil (dec := decCVX) (m := m) 0 (by omega)⟩,
      hA⟩
  by_cases hsh : vl = 0 ∨ cl = 0
  · rw [rtsW_short (h := hrl) (h2 := hsh)]; exact RSim.none
  rw [rtsW_cons (h := hrl) (h2 := hsh)]
  have hvl : vl ≠ 0 := fun e => hsh (.inl e)
  have hcl : cl ≠ 0 := fun e => hsh (.inr e)
  have hl0 : ∀ w : Word, w ≠ 0 → ∃ j, w.toNat = j + 1 := fun w hw =>
    ⟨w.toNat - 1, by have : w.toNat ≠ 0 := fun e => hw (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨jr, hjr⟩ := hl0 rl hrl
  obtain ⟨jv, hjv⟩ := hl0 vl hvl
  obtain ⟨jc, hjc⟩ := hl0 cl hcl
  have hrcs' : decPL (truncM m) (decRS (truncM m)) ro.toNat (jr + 1) = some rcs := by rw [← hjr]; exact hrcs
  obtain ⟨p, RS, rcs', rfl, hp, hRS, hrcsT⟩ := decPL_cons hrcs'
  have hcvs' : decPL (truncM m) (decCVp (truncM m)) vo.toNat (jv + 1) = some cvs := by rw [← hjv]; exact hcvs
  obtain ⟨pv, CV, cvs', rfl, hpv, hCV, hcvsT⟩ := decPL_cons hcvs'
  have hcs' : decNL (truncM m) co.toNat (jc + 1) = some cs := by rw [← hjc]; exact hcs
  rw [decNL_succ] at hcs'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcs'
  obtain ⟨c0, hc0, cs', hcsT, rfl⟩ := hcs'
  obtain ⟨hpt, hpm⟩ := rec2IwN_trunc hp
  obtain ⟨hpvt, hpvm⟩ := rec2IwN_trunc hpv
  obtain ⟨hc0t, hc0m⟩ := rec2IwN_trunc hc0
  obtain ⟨ep, tp⟩ := rec2RdN (w := ro) (k := 0) (by simpa using hpm) hsz
  obtain ⟨ev, tv⟩ := rec2RdN (w := vo) (k := 0) (by simpa using hpvm) hsz
  obtain ⟨ec, tc⟩ := rec2RdN (w := co) (k := 0) (by simpa using hc0m) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at ep ev ec
  rw [ep, ev, ec]
  have hokj := hok.2.2 0 (by omega)
  obtain ⟨p0, q, cv, hp0, -, hq, -, hext, -⟩ := hokj
  rw [Nat.add_zero, hpm] at hp0; cases hp0
  have hcvR : ∀ q', iwN m p = some q' → CVExt m q' := fun q' h' => by rw [hq] at h'; cases h'; exact hext
  have hro1 := rec2ToNat_succ (o := ro) (i := ro.toNat) (Nat.le_refl _) (by omega)
  have hvo1 := rec2ToNat_succ (o := vo) (i := vo.toNat) (Nat.le_refl _) (by omega)
  have hco1 := rec2ToNat_succ (o := co) (i := co.toNat) (Nat.le_refl _) (by omega)
  have hrl1 := rec2ToNat_pred hrl
  have hvl1 := rec2ToNat_pred hvl
  have hcl1 := rec2ToNat_pred hcl
  unfold ConRon.Arena.classRecTysOk
  have hr := rtoW_sim (dn := dn) (vis := vis) (fe := fe) n m a g k (UInt64.ofNat p) (UInt64.ofNat pv)
    (UInt64.ofNat c0) G RS CV hS hG hns (by rw [tp]; exact hRS) (by rw [tp]; exact hcvR) (by rw [tv]; exact hCV) hA
  rw [tc] at hr
  refine RSim.bind (K := rtsK1 stubCall n vis g k ro rl vo vl co cl) (by simp [rtsK1]) hr ?_
  rintro ⟨r1, m1⟩ x a1 - ⟨⟨hS1, hg1, hx⟩, hA1⟩
  dsimp only at hS1 hg1 hx
  rw [rtsK1_some]
  have hok' := RecsOK_tail (by rw [← hjr]; simpa using hok)
  refine RSim.bind (K := rtsK2 n (r1.headD 0)) rfl (ih m1 a1 _ _ _ _ _ _ rcs' cvs' cs' hS1
    (hG.grow (decCG_mono _) hg1)
    (by rw [hro1, hrl1, hjr]; exact (show DecB (fun m => decPL m (decRS m) (ro.toNat + 1) jr) m rcs' from
      hrcsT).grow (OMono.decPL (fun q => decRS_mono q) _ _) hg1)
    (by rw [hro1, hrl1, hjr]; exact RecsOK_grow hg1 (by simpa using hok'))
    (by rw [hvo1, hvl1, hjv]; exact (show DecB (fun m => decPL m (decCVp m) (vo.toNat + 1) jv) m cvs' from
      hcvsT).grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg1)
    (by rw [hco1, hcl1, hjc]; exact (show DecB (fun m => decNL m (co.toNat + 1) jc) m cs' from
      hcsT).grow (OMono.decNL _ _) hg1) hA1) ?_
  rintro ⟨r2, m2⟩ xs a2 - ⟨⟨hS2, hg2, hxs⟩, hA2⟩
  dsimp only at hS2 hg2 hxs
  rw [rtsK2_some]
  refine RSim.lstep (K := rtsK3) rfl fun ⟨r3, m3⟩ h3 => ?_
  have hy : StabD (fun m => decCVX m (r1.headD 0).toNat) m1 x := decCVX_stab hx.1 hx.2
  obtain ⟨hS3, hg3, hsp3⟩ := SPL.cons h3 hS2 hxs (hy.grow hg2)
  rw [rtsK3_some]
  exact RSim.pure_some ⟨⟨hS3, hg1.trans (hg2.trans hg3), by simpa [decCVS] using hsp3⟩, consW_afr h3 hA2⟩

/-- **`class_rec_tys_ok` refines `classRecTysOk`** (through `class_rec_ty_ok`'s stubs): the
generated constants, a stable slice of records below the record top. -/
@[refines ConRon.Arena.classRecTysOk]
theorem classRecTysOk_refines (p : Prog) (hp : RtsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g k ro rl vo vl co cl : Word)
    (G : ClassGen) (rcs : List RecShape) (cvs : List IConstantVal) (cs : List Nat)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrcs : DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) s₀.mem rcs)
    (hok : RecsOK s₀.mem ro.toNat rl.toNat (rcs.map (·.cvR)))
    (hcvs : DecB (fun m => decPL m (decCVp m) vo.toNat vl.toNat) s₀.mem cvs)
    (hcs : DecB (fun m => decNL m co.toNat cl.toNat) s₀.mem cs) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_tys_ok" [vis, g, k, ro, rl, vo, vl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a₀ ∧
      KP dn vis fe s₀.mem decCVS (r, s'.mem)
        (AM.st (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a₀)
        (AM.res (ConRon.Arena.classRecTysOk V fe G k.toNat rcs cvs cs) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classRecTysOk_spec p hp stubCall (stubCall_spec p) n s₀ vis g k ro rl vo vl co cl) fun _ _ ⟨hl, hw⟩ =>
    let h := (rtsW_sim dn vis fe g k G hns n _ a₀ ro rl vo vl co cl rcs cvs cs hS hG hrcs hok hcvs hcs hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind
