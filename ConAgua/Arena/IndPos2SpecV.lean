import ConAgua.Arena.IndPos2SpecU

/-! # `IndPos2`, the root frame and the seeds (lane `indproofs2`, helper `pos2`): the models
simulated by the twin (`nestRoot`, `nestSeeds`, the seeds' fuel fold), and the census theorems. -/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The seeds' fuel -/

theorem pos2_wfWf_some {n : Nat} {m m1 : Mem} {e : Word} {r : List Word} (h : wfWf n m e = some (r, m1)) :
    ∃ n' w, n = n' + 2 ∧ wfW n' m e = some (w, m1) ∧ r = [w] := by
  match n, h with
  | n' + 2, h =>
    simp only [wfWf] at h
    cases hc : wfW n' m e with
    | none => rw [hc] at h; cases h
    | some pr =>
      obtain ⟨w, m2⟩ := pr
      rw [hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨n', w, rfl, hc, rfl⟩

/-- The twin's fold of the seed's fuel. -/
def pos2FuelF (acc : Nat) (d : EIdx) : AM Nat := do
  let w ← ConRon.Arena.whnfWalkFuel d
  pure (max acc w)

theorem p2sfW_afr : ∀ (n : Nat) (m m' : Mem) (dO dL k f : Word) (r : List Word),
    p2sfW n m dO dL k f = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [p2sfW] at h
  | n + 1, m, m', dO, dL, k, f, r, h => by
    simp only [p2sfW, p2sfK.eq_def] at h
    afr_auto h [(fun h => by
        obtain ⟨n', w, -, hw, -⟩ := pos2_wfWf_some h
        exact wfW_afr hw), p2sfW_afr n _ _ _ _ _ _ _]

theorem p2sfW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (dO dL : Word) (ds : List EIdx) (m0 : Mem) (hlen : ds.length = dL.toNat)
    (hel : ∀ j < dL.toNat, ∃ w, (m0.arr64 IW)[dO.toNat + j]? = some w ∧ H w ∧ ds[j]? = some (decI w))
    (hb : dO.toNat + dL.toNat ≤ iwTop m0) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (k f : Word) (r : List Word),
    p2sfW n m dO dL k f = some (r, m') → StageR dn vis fe m a → IWGrow m0 m → k.toNat ≤ dL.toNat → PosMR m →
    ∃ a', ((ds.drop k.toNat).foldlM pos2FuelF f.toNat).run a = .ok ((r.headD 0).toNat, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m'
  | 0, m, m', a, k, f, r, h, _, _, _, _ => by simp [p2sfW] at h
  | n + 1, m, m', a, k, f, r, h, hS, hg0, hk, hP => by
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hd : dL ≤ k
    · rw [p2sfW_done (h := hd)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : k.toNat = dL.toNat := Nat.le_antisymm hk (UInt64.le_iff_toNat_le.mp hd)
      rw [this, ← hlen, List.drop_length]
      exact ⟨a, rfl, hS, IWGrow.refl _, hP⟩
    rw [p2sfW_step (h := hd)] at h
    have hkl : k.toNat < dL.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hd); omega
    obtain ⟨w, hw, hH, hdj⟩ := hel k.toNat hkl
    have hg0t := hg0.1
    have hrd : rdW (m.arr64 IW) (dO + k) = w := by
      have e : (dO + k).toNat = dO.toNat + k.toNat := word_add_toNat (by omega)
      simp only [rdW, e]; rw [hg0.2.2.1 _ (by omega), hw]; rfl
    rw [hrd] at h
    cases hwf : wfWf n m w with
    | none => rw [hwf] at h; simp [p2sfK] at h
    | some pr =>
    obtain ⟨rw, m1⟩ := pr
    rw [hwf, p2sfK_some] at h
    obtain ⟨n', wv, hn, hwW, rfl⟩ := pos2_wfWf_some hwf
    obtain ⟨mp, hmp⟩ := hP.dp
    obtain ⟨d, hrunw, hwd, hM1, hS1, hg1, hf1⟩ := wfW_ok n' dn fe vis m m1 a w wv mp hwW hS hH hmp
    have hk1 : (k + 1).toNat = k.toNat + 1 := word_add_toNat (by simp; omega)
    obtain ⟨a', hrun, hS', hg', hP'⟩ := p2sfW_ok dn vis fe dO dL ds m0 hlen hel hb n m1 m' a (k + 1) _ r h hS1
      (hg0.trans hg1) (by omega) (hP.setDp hf1 ⟨∅, hM1⟩)
    refine ⟨a', ?_, hS', hg1.trans hg', hP'⟩
    have hdk : ds[k.toNat]'(by omega) = decI w := by
      have := hdj; rw [List.getElem?_eq_getElem (by omega)] at this; exact Option.some.inj this
    have hmax : (if f < [wv].headD 0 then [wv].headD 0 else f).toNat = max f.toNat d := by
      have e1 := @UInt64.lt_iff_toNat_lt f wv
      by_cases hlt : f < wv
      · simp only [List.headD_cons, hlt, ite_true]; have := e1.mp hlt; omega
      · simp only [List.headD_cons, hlt, ite_false]; have : ¬ f.toNat < wv.toNat := fun x => hlt (e1.mpr x); omega
    rw [hmax, hk1] at hrun
    rw [List.drop_eq_getElem_cons (by omega), List.foldlM_cons, hdk]
    simp only [pos2FuelF, StateT.run_bind, ← decE_eq, hrunw, except_ok_bind] at hrun ⊢
    exact hrun

/-! ## The root frame -/

/-- The root frame's outputs: a slice of `(off, len)` records of `(kinds, closed)` slices. -/
def RootOutsB (m : Mem) (o l : Nat) (outss : List (List (List NestFieldKind × EIdx))) : Prop :=
  DecB (fun m => decPL m (decAt m (fun o l => decPL m (decKE m) o l)) o l) m outss

theorem pos2_rootOuts_mono : ∀ q, OMono (fun m => decAt m (fun o l => decPL m (decKE m) o l) q) :=
  fun q => OMono.decAt (fun o l => OMono.decPL decKE_mono o l) q

theorem RootOutsB.grow {m m' : Mem} {o l : Nat} {outss : List (List (List NestFieldKind × EIdx))}
    (h : RootOutsB m o l outss) (hg : IWGrow m m') : RootOutsB m' o l outss :=
  DecB.grow (OMono.decPL pos2_rootOuts_mono o l) hg h

/-- An `(off, len)` record (`rec2`) of a `(kinds, closed)` slice. -/
theorem pos2_outs_rec {m' : Mem} {q o l : Word} {xs : List (List NestFieldKind × EIdx)}
    (hq : q.toNat + 2 ≤ iwTop m')
    (hget : ∀ j < [o, l].length, (m'.arr64 IW)[q.toNat + j]? = [o, l][j]?) (hx : OutsB m' o.toNat l.toNat xs) :
    DecB (fun m => decAt m (fun o l => decPL m (decKE m) o l) q.toNat) m' xs := by
  have g : ∀ j < 2, (iwA (truncM m'))[q.toNat + j]? = [o, l][j]? := fun j hj => by
    rw [truncM_iw_eq (by omega)]; exact hget j (by simpa using hj)
  have n0 : iwN (truncM m') q.toNat = some o.toNat := by
    simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 0 (by omega))
  have n1 : iwN (truncM m') (q.toNat + 1) = some l.toNat := by
    simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 1 (by omega))
  have hx' : decPL (truncM m') (decKE (truncM m')) o.toNat l.toNat = some xs := hx
  show decAt (truncM m') _ q.toNat = some xs
  simp only [decAt, n0, n1, Option.bind_eq_bind, Option.bind_some]
  exact hx'

section root
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  (hcs : CtorSums fe) (ctx hO hL : Word) (c : NestCtx) (holes : List EIdx)

include hcs in
/-- **`nest_root`** simulated by `nestRoot`. -/
theorem p2rtW_ok : ∀ (n : Nat), 2 ^ 31 + n ≤ coreWalkFuel → ∀ (m m' : Mem) (a : AState) (cO cL ns oO oL : Word)
    (css : List (List (IConstantVal × Nat))) (NS : NestState) (outss : List (List (List NestFieldKind × EIdx)))
    (r : List Word),
    p2rtW n m vis ctx hO hL cO cL ns oO oL = some (r, m') → StageR dn vis fe m a → UCtx dn vis fe m ctx c →
    c.hiAt 0 < 2 ^ 64 → c.params.length + c.names.length < 2 ^ 64 →
    decHL m hO.toNat hL.toNat = some holes → hO.toNat + hL.toNat ≤ iwTop m →
    cL.toNat = css.length → cO.toNat + css.length ≤ iwTop m → CssAt m cO.toNat css → NSB m ns NS →
    RootOutsB m oO.toNat oL.toNat outss → oO.toNat + oL.toNat ≤ iwTop m → PosMR m → AbsOK m →
    ∃ x a', (nestRoot V fe c holes css NS outss).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      RootOutsB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ NSB m' (r.tail.tail.headD 0) x.2 ∧ PosMR m' ∧
      AbsOK m'
  | 0, _, m, m', a, cO, cL, ns, oO, oL, css, NS, outss, r, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp [p2rtW] at h
  | n + 1, hn, m, m', a, cO, cL, ns, oO, oL, css, NS, outss, r, h, hS, hU, hhi, hpn, hho, hhob, hcl, hcb, hcss,
      hns, hout, houtb, hP, hA => by
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    rw [p2rtW_succ] at h
    by_cases h0 : cL = 0
    · rw [if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst h0
      have : css = [] := List.eq_nil_of_length_eq_zero (by simpa using hcl.symm)
      subst this
      exact ⟨(outss, NS), a, by rw [ConRon.Arena.nestRoot.eq_def]; rfl, hS, IWGrow.refl _, by simpa using hout,
        by simpa using houtb, by simpa using hns, hP, hA⟩
    rw [if_neg h0] at h
    obtain ⟨cs, css', rfl⟩ : ∃ x css', css = x :: css' := by
      cases css with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hcl)) h0
      | cons x css' => exact ⟨x, css', rfl⟩
    simp only [List.length_cons] at hcl hcb
    obtain ⟨hdr, cO', cL', h0w, h1w, h2w, -, hhdr, hcl', hcb', hcsAt⟩ := hcss 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0w hcl' hcb' hcsAt
    rw [hcl'] at hcb'
    have rd0 : rdW (m.arr64 IW) cO = hdr := by simp [rdW, h0w]
    have rd1 : rdW (m.arr64 IW) hdr = cO' := by simp [rdW, h1w]
    have hdr1 : (hdr + 1).toNat = hdr.toNat + 1 := word_add_toNat (by simp; omega)
    have rd2 : rdW (m.arr64 IW) (hdr + 1) = cL' := by simp [rdW, hdr1, h2w]
    rw [rd0, rd1, rd2] at h
    -- the context's words
    obtain ⟨hn0, -, hpa0, -, -, hus0, husd0, -, -, -⟩ := ctx_fields hU.dec hU.inn htop
    have hne0 := ctx_names_end hU.dec hU.inn hU.sl htop
    have hpe0 := ctx_params_end hU.dec hU.inn hU.sl htop
    have hW : WCtx dn vis fe m ctx 0 0 c [] := ⟨hU, by simp [HSl, HolesAt], by simpa using hhi⟩
    have hhi0 : (nhiW m ctx 0).toNat = c.hiAt 0 := by simpa using hW.hi htop
    have hpl : (rdW (m.arr64 IW) (ctx + 8)).toNat = c.params.length := (pos2_hslice_get hpa0).1.symm
    have hC : CtorsCtx m (rdW (m.arr64 IW) (ctx + 10)) (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8))
        (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) hO hL c.params c.names holes :=
      ⟨hus0, by show decHL (truncM m) _ _ = _; rw [decHL_truncM hpe0]; exact hpa0, hpe0, hn0, hne0,
        by rw [hpl]; exact hpn, hho, hhob⟩
    have hCt := (nbOK_all dn vis fe hcs n (by omega)).2.2.2.2.2.2.2.1
    cases hc : nbCtorsW n m vis ctx 1 0 0 0 (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 10))
        (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8)) (rdW (m.arr64 IW) ctx)
        (rdW (m.arr64 IW) (ctx + 1)) hO hL cO' cL' ns 0 0 with
    | none => rw [hc] at h; simp [p2rtK1] at h
    | some pr =>
    obtain ⟨r1, m1⟩ := pr
    rw [hc, p2rtK1_some] at h
    obtain ⟨x1, a1, hrun1, hS1, hg1, hO1, hOb1, hns1, hP1, hA1⟩ := hCt m m1 a ctx 1 0 0 0 (nhiW m ctx 0) _ _ _ _ _ hO hL
      cO' cL' ns 0 0 c [] c.params c.names holes cs NS [] r1 hc hS hW hC hcl' hcb' hcsAt hns
      (by simpa using OutsB.nil m 0) (by simp) hP hA
    rw [hhi0, husd0] at hrun1
    have hrun1' : (nestCtors V fe c true 0 [] (c.hiAt 0) c.lvls c.params c.names holes cs NS []).run a =
        .ok (x1, a1) := by simpa using hrun1
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    -- its record, appended
    cases hr2 : posRecW m1 [r1.headD 0, r1.tail.headD 0] with
    | none => rw [hr2] at h; simp [p2rtK2] at h
    | some pr2 =>
    obtain ⟨q, m2⟩ := pr2
    rw [hr2, p2rtK2_some] at h
    obtain ⟨hS2, hg2, hq2, ht2, hget2⟩ := posRecW_stage hr2 hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht2
    have hrec := pos2_outs_rec (q := q) (by omega) hget2 (hO1.grow hg2)
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
    cases hsn : snocW n m2 oO oL q with
    | none => rw [hsn] at h; simp [p2rtK3] at h
    | some pr3 =>
    obtain ⟨ro, m3⟩ := pr3
    rw [hsn, p2rtK3_some] at h
    have hg12 := hg1.trans hg2
    obtain ⟨hS3, hg3, h30, h31, ht3, hw3, hx3⟩ := snocW_words hsn hS2 (by have := hg12.1; omega)
    have hout3 : RootOutsB m3 (ro.headD 0).toNat (ro.tail.headD 0).toNat (outss ++ [x1.1]) := by
      rw [h30, h31]
      exact pos2_decB_snoc pos2_rootOuts_mono (hout.grow hg12) hg3 (by omega) hw3 hx3
        (DecB.grow (pos2_rootOuts_mono _) hg3 hrec)
    have hg13 := hg12.trans hg3
    have hcO1 : (cO + 1).toNat = cO.toNat + 1 := word_add_toNat (by simp; omega)
    have hcL1 : (cL - 1).toNat = css'.length := by rw [pos2_word_pred h0]; omega
    obtain ⟨x, a', hrun, hS', hg', hO', hOb', hns', hP', hA'⟩ := p2rtW_ok n (by omega) m3 m' a1 (cO + 1) (cL - 1)
      (r1.tail.tail.headD 0) (ro.headD 0) (ro.tail.headD 0) css' x1.2 (outss ++ [x1.1]) r h hS3 (hU.grow hg13) hhi
      hpn (by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by omega)]; exact hho)
      (by have := hg13.1; omega) hcL1 (by rw [hcO1]; have := hg13.1; omega)
      (by rw [hcO1]; exact (hcss.grow hg13).tail)
      ((hns1.grow hg2 htop1).grow hg3 htop2) hout3 (by rw [h30, h31]; omega)
      ((hP1.fr (posRecW_mfr hr2)).fr (snocW_mfr hsn)) (snocW_afr hsn (posRecW_afr hr2 hA1))
    refine ⟨x, a', ?_, hS', hg13.trans hg', hO', hOb', hns', hP', hA'⟩
    simp only [ConRon.Arena.nestRoot, StateT.run_bind]
    rw [hrun1']
    exact hrun

end root

/-! ## The seeds -/

/-- The seeds: word `o + i` points at a `(key, nPc)` record, the key a `NestKey` decoded below the
tops with its parameter slice below the top. -/
def SeedsAt (m : Mem) (o : Nat) (seeds : List (NestKey × Nat)) : Prop :=
  ∀ i (hi : i < seeds.length), ∃ sp key nPc : Word, (m.arr64 IW)[o + i]? = some sp ∧ o + i < iwTop m ∧
    sp.toNat + 1 < iwTop m ∧ (m.arr64 IW)[sp.toNat]? = some key ∧ (m.arr64 IW)[sp.toNat + 1]? = some nPc ∧
    DecB (fun m => decNK m key.toNat) m seeds[i].1 ∧ NKSl m key ∧ nPc.toNat = seeds[i].2

theorem pos2_key_rd {m m' : Mem} (hg : IWGrow m m') (htop : iwTop m < 2 ^ 64) {key : Word}
    (hk : key.toNat + 4 ≤ iwTop m) {j : Nat} (hj : j < 4) : rdW (m'.arr64 IW) (key + UInt64.ofNat j) = rdW (m.arr64 IW) (key + UInt64.ofNat j) := by
  apply pos2_rd_grow hg
  have : (UInt64.ofNat j).toNat = j := by simp; omega
  rw [word_add_toNat (by rw [this]; omega), this]; omega

theorem SeedsAt.grow {m m' : Mem} {o : Nat} {seeds : List (NestKey × Nat)} (h : SeedsAt m o seeds)
    (hg : IWGrow m m') (htop : iwTop m < 2 ^ 64) : SeedsAt m' o seeds := fun i hi => by
  obtain ⟨sp, key, nPc, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h i hi
  have hk4 := (pos2_nk_fields h6 htop).2.2.2.2.2.2
  refine ⟨sp, key, nPc, by rw [hg.2.2.1 _ h2]; exact h1, by have := hg.1; omega, by have := hg.1; omega,
    by rw [hg.2.2.1 _ (by omega)]; exact h4, by rw [hg.2.2.1 _ h3]; exact h5, h6.grow (decNK_mono _) hg, ?_, h8⟩
  have e2 := pos2_key_rd hg htop hk4 (j := 2) (by omega)
  have e3 := pos2_key_rd hg htop hk4 (j := 3) (by omega)
  simp only [NKSl] at h7 ⊢
  have := hg.1
  rw [show (key + 2 : Word) = key + UInt64.ofNat 2 from rfl, show (key + 3 : Word) = key + UInt64.ofNat 3 from rfl,
    e2, e3]
  exact Nat.le_trans h7 hg.1

theorem SeedsAt.tail {m : Mem} {o : Nat} {x : NestKey × Nat} {seeds : List (NestKey × Nat)}
    (h : SeedsAt m o (x :: seeds)) : SeedsAt m (o + 1) seeds := fun i hi => by
  obtain ⟨sp, key, nPc, h1, h2, rest⟩ := h (i + 1) (by simp; omega)
  exact ⟨sp, key, nPc, by rw [show o + 1 + i = o + (i + 1) by omega]; exact h1, by omega, by simpa using rest⟩

section seeds
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  (hcs : CtorSums fe) (ctx : Word) (c : NestCtx)

include hcs in
/-- **`nest_seeds`** simulated by `nestSeeds`. -/
theorem p2sdW_ok : ∀ (n : Nat), 2 ^ 31 + n ≤ coreWalkFuel → ∀ (m m' : Mem) (a : AState) (sO sL ns : Word)
    (seeds : List (NestKey × Nat)) (NS : NestState) (r : List Word),
    p2sdW n m vis ctx sO sL ns = some (r, m') → StageR dn vis fe m a → UCtx dn vis fe m ctx c →
    c.hiAt 0 < 2 ^ 64 → sL.toNat = seeds.length → SeedsAt m sO.toNat seeds → NSB m ns NS → PosMR m → AbsOK m →
    ∃ x a', (nestSeeds V fe c seeds NS).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      NSB m' (r.headD 0) x ∧ PosMR m' ∧ AbsOK m'
  | 0, _, m, m', a, sO, sL, ns, seeds, NS, r, h, _, _, _, _, _, _, _, _ => by simp [p2sdW] at h
  | n + 1, hn, m, m', a, sO, sL, ns, seeds, NS, r, h, hS, hU, hhi, hsl, hsd, hns, hP, hA => by
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    rw [p2sdW_succ] at h
    by_cases h0 : sL = 0
    · rw [if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst h0
      have : seeds = [] := List.eq_nil_of_length_eq_zero (by simpa using hsl.symm)
      subst this
      exact ⟨NS, a, by rw [ConRon.Arena.nestSeeds.eq_def]; rfl, hS, IWGrow.refl _, by simpa using hns, hP, hA⟩
    rw [if_neg h0] at h
    obtain ⟨⟨kk, nPcN⟩, seeds', rfl⟩ : ∃ x seeds', seeds = x :: seeds' := by
      cases seeds with
      | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hsl)) h0
      | cons x seeds' => exact ⟨x, seeds', rfl⟩
    simp only [List.length_cons] at hsl
    obtain ⟨sp, key, nPc, h0w, hsO, hsp1, h1w, h2w, hkd, hksl, hnpc⟩ := hsd 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0w hkd hnpc
    have rd0 : rdW (m.arr64 IW) sO = sp := by simp [rdW, h0w]
    have rd1 : rdW (m.arr64 IW) sp = key := by simp [rdW, h1w]
    have hsp1' : (sp + 1).toNat = sp.toNat + 1 := word_add_toNat (by simp; omega)
    have rd2 : rdW (m.arr64 IW) (sp + 1) = nPc := by simp [rdW, hsp1', h2w]
    rw [rd0, rd1, rd2] at h
    obtain ⟨hnnH, hnnd, husH, husd, hdsd, hdsb, hk4⟩ := pos2_nk_fields hkd htop
    obtain ⟨hk, hkin⟩ := pos2_nk_in hkd
    obtain ⟨hdl, hdel⟩ := pos2_hslice_get hdsd
    -- the fuel
    cases hf : p2sfW n m (rdW (m.arr64 IW) (key + 2)) (rdW (m.arr64 IW) (key + 3)) 0 SLACK with
    | none => rw [hf] at h; simp [p2sdK1] at h
    | some pr =>
    obtain ⟨rf, m1⟩ := pr
    rw [hf, p2sdK1_some] at h
    obtain ⟨a1, hfold, hS1, hg1, hP1⟩ := p2sfW_ok dn vis fe _ _ kk.ds m hdl hdel hksl n m m1 a 0 SLACK rf hf hS
      (IWGrow.refl _) (by simp) hP
    have hA1 := p2sfW_afr _ _ _ _ _ _ _ _ hf hA
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    -- the instance's type
    cases n with
    | zero => simp [nitWf, p2sdK2] at h
    | succ n' =>
    cases hni : nitW n' m1 vis ctx (nhiW m ctx 0) key with
    | none => simp only [nitWf] at h; rw [hni] at h; simp [p2sdK2] at h
    | some pr2 =>
    obtain ⟨r2, m2⟩ := pr2
    simp only [nitWf] at h
    rw [hni, p2sdK2_some] at h
    have hW : WCtx dn vis fe m ctx 0 0 c [] := ⟨hU, by simp [HSl, HolesAt], by simpa using hhi⟩
    have hhi0 : (nhiW m ctx 0).toNat = c.hiAt 0 := by simpa using hW.hi htop
    obtain ⟨x2, a2, hrun2, hS2, hg2, -, hctyH, hctyd, hP2⟩ := nitW_ok n' dn fe vis ctx _ (c.hiAt 0) hhi0 c m1 m2 a1 key kk
      r2 hni hS1 (hU.grow hg1) (hkd.get (decNK_mono _) |>.symm ▸ (hkd.stab (decNK_mono _) m1 hg1))
      (pos2_nk_in (hkd.grow (decNK_mono _) hg1)).2 ((hsd.grow hg1 htop) 0 (by simp) |>.elim fun _ h' => by
        obtain ⟨key', nPc', h0', -, -, h1', -, -, hksl', -⟩ := h'
        have : (m1.arr64 IW)[sO.toNat]? = some sp := by rw [hg1.2.2.1 _ (by omega)]; exact h0w
        simp only [Nat.add_zero] at h0'
        rw [this] at h0'; cases h0'
        rw [hg1.2.2.1 _ (by omega), h1w] at h1'; cases h1'
        exact hksl') hP1
    have hA2 := nitW_afr hni hA1
    have hg12 := hg1.trans hg2
    have hksl2 : (rdW (m.arr64 IW) (key + 2)).toNat + (rdW (m.arr64 IW) (key + 3)).toNat ≤ iwTop m2 :=
      Nat.le_trans hksl hg12.1
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
    -- the container instance
    have e0 : rdW (m2.arr64 IW) key = rdW (m.arr64 IW) key := pos2_rd_grow hg12 (by omega)
    have e1 := pos2_key_rd hg12 htop hk4 (j := 1) (by omega)
    have e2 := pos2_key_rd hg12 htop hk4 (j := 2) (by omega)
    have e3 := pos2_key_rd hg12 htop hk4 (j := 3) (by omega)
    rw [show (key + 1 : Word) = key + UInt64.ofNat 1 from rfl, show (key + 2 : Word) = key + UInt64.ofNat 2 from rfl,
      show (key + 3 : Word) = key + UInt64.ofNat 3 from rfl, e0, e1, e2, e3] at h
    have hKey := (nbOK_all dn vis fe hcs (n' + 1) (by omega)).2.2.2.2.1
    cases hk3 : nbKeyW (n' + 1) m2 vis ctx (rf.headD 0) 0 0 0 (rdW (m.arr64 IW) key)
        (rdW (m.arr64 IW) (key + UInt64.ofNat 1)) (rdW (m.arr64 IW) (key + UInt64.ofNat 2))
        (rdW (m.arr64 IW) (key + UInt64.ofNat 3)) nPc (r2.tail.headD 0) ns with
    | none => rw [hk3] at h; simp [p2sdK3] at h
    | some pr3 =>
    obtain ⟨r3, m3⟩ := pr3
    rw [hk3, p2sdK3_some] at h
    obtain ⟨x3, a3, hrun3, hS3, hg3, -, hns3, hP3, hA3⟩ := hKey m2 m3 a2 ctx (rf.headD 0) 0 0 0 _ _ _ _ nPc _ ns c [] kk.ds NS r3
      hk3 hS2 (hW.grow hg12) hnnH husH
      (by show decHL (truncM m2) _ _ = _; rw [decHL_truncM (by simpa using hksl2)]
          rw [decHL_agree (RdS.of_grow hg12) (fun j hj => by simpa using hdsb j hj)]; simpa using hdsd)
      (by simpa using hksl2) hctyH (hns.grow hg12 htop) hP2 hA2
    have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
    have hg13 := hg12.trans hg3
    have hsO1 : (sO + 1).toNat = sO.toNat + 1 := word_add_toNat (by simp; omega)
    have hsL1 : (sL - 1).toNat = seeds'.length := by rw [pos2_word_pred h0]; omega
    obtain ⟨x, a', hrun, hS', hg', hns', hP', hA'⟩ := p2sdW_ok (n' + 1) (by omega) m3 m' a3 (sO + 1) (sL - 1)
      (r3.tail.headD 0) seeds' x3.2 r h hS3 (hU.grow hg13) hhi hsL1
      (by rw [hsO1]; exact (hsd.grow hg13 htop).tail) hns3 hP3 hA3
    refine ⟨x, a', ?_, hS', hg13.trans hg', hns', hP', hA'⟩
    have hfold' : (kk.ds.foldlM (fun a d => do
        let w ← ConRon.Arena.whnfWalkFuel d
        pure (max a w)) fuelSlack).run a = .ok ((rf.headD 0).toNat, a1) := by
      simp only [UInt64.toNat_zero, List.drop_zero] at hfold
      exact hfold
    have hrun3' : (nestContKey V fe c (rf.headD 0).toNat [] 0 kk.cname kk.lvls kk.ds nPcN x2.2 NS).run a2 =
        .ok (x3, a3) := by
      have e1 : decI (rdW (m.arr64 IW) (key + UInt64.ofNat 1)) = kk.lvls := husd
      rw [← hnnd, ← e1, ← hctyd, ← hnpc]
      exact hrun3
    simp only [ConRon.Arena.nestSeeds, StateT.run_bind]
    rw [hfold']
    simp only [except_ok_bind]
    rw [hrun2]
    simp only [except_ok_bind]
    rw [hrun3']
    simp only [except_ok_bind]
    exact hrun

end seeds

/-! ## Census -/

section census
variable {p : Prog} (L : RsLook p) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

include L in
@[refines_part ConRon.Arena.nestSeeds "the seed's fuel fold (nest_seeds_fuel)"]
theorem nestSeedsFuel_refines (s₀ : St) (a₀ : AState) (dO dL k f : Word) (ds : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hlen : ds.length = dL.toNat)
    (hel : ∀ j < dL.toNat, ∃ w, (s₀.mem.arr64 IW)[dO.toNat + j]? = some w ∧ H w ∧ ds[j]? = some (decI w))
    (hb : dO.toNat + dL.toNat ≤ iwTop s₀.mem) (hk : k.toNat ≤ dL.toNat) (hP : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_seeds_fuel" [dO, dL, k, f]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ a', ((ds.drop k.toNat).foldlM pos2FuelF f.toNat).run a₀ =
      .ok ((r.headD 0).toNat, a') ∧ StageR dn vis fe s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ PosMR s'.mem; ⊤⦄ := by
  refine triple_post (nestSeedsFuel_spec L n s₀ dO dL k f) ?_
  rintro r s' ⟨hlc, hm⟩
  have := p2sfW_ok dn vis fe dO dL ds s₀.mem hlen hel hb n s₀.mem s'.mem a₀ k f _ hm hS (IWGrow.refl _) hk hP
  exact ⟨hlc, by simpa using this⟩

variable (hcs : CtorSums fe)
include L hcs

@[refines ConRon.Arena.nestRoot]
theorem nestRoot_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx hO hL cO cL ns oO oL : Word)
    (c : NestCtx) (holes : List EIdx) (css : List (List (IConstantVal × Nat))) (NS : NestState)
    (outss : List (List (List NestFieldKind × EIdx))) (hS : StageR dn vis fe s₀.mem a₀)
    (hU : UCtx dn vis fe s₀.mem ctx c) (hhi : c.hiAt 0 < 2 ^ 64) (hpn : c.params.length + c.names.length < 2 ^ 64)
    (hho : decHL s₀.mem hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop s₀.mem)
    (hcl : cL.toNat = css.length) (hcb : cO.toNat + css.length ≤ iwTop s₀.mem) (hcss : CssAt s₀.mem cO.toNat css)
    (hns : NSB s₀.mem ns NS) (hout : RootOutsB s₀.mem oO.toNat oL.toNat outss)
    (houtb : oO.toNat + oL.toNat ≤ iwTop s₀.mem) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_root" [vis, ctx, hO, hL, cO, cL, ns, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestRoot V fe c holes css NS outss).run a₀ = .ok (x, a') ∧ StageR dn vis fe s'.mem a' ∧
      IWGrow s₀.mem s'.mem ∧ RootOutsB s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ NSB s'.mem (r.tail.tail.headD 0) x.2 ∧
      PosMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (nestRoot_spec L n s₀ vis ctx hO hL cO cL ns oO oL) ?_
  rintro r s' ⟨hlc, hm⟩
  have := p2rtW_ok dn vis fe hcs ctx hO hL c holes n hn s₀.mem s'.mem a₀ cO cL ns oO oL css NS outss _ hm hS hU
    hhi hpn hho hhob hcl hcb hcss hns hout houtb hP hA
  exact ⟨hlc, by simpa using this⟩

@[refines ConRon.Arena.nestSeeds]
theorem nestSeeds_refines (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) (ctx sO sL ns : Word)
    (c : NestCtx) (seeds : List (NestKey × Nat)) (NS : NestState) (hS : StageR dn vis fe s₀.mem a₀)
    (hU : UCtx dn vis fe s₀.mem ctx c) (hhi : c.hiAt 0 < 2 ^ 64) (hsl : sL.toNat = seeds.length)
    (hsd : SeedsAt s₀.mem sO.toNat seeds) (hns : NSB s₀.mem ns NS) (hP : PosMR s₀.mem) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_seeds" [vis, ctx, sO, sL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ x a', (nestSeeds V fe c seeds NS).run a₀ = .ok (x, a') ∧ StageR dn vis fe s'.mem a' ∧
      IWGrow s₀.mem s'.mem ∧ NSB s'.mem (r.headD 0) x ∧ PosMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (nestSeeds_spec L n s₀ vis ctx sO sL ns) ?_
  rintro r s' ⟨hlc, hm⟩
  have := p2sdW_ok dn vis fe hcs ctx c n hn s₀.mem s'.mem a₀ sO sL ns seeds NS _ hm hS hU hhi hsl hsd hns hP hA
  exact ⟨hlc, by simpa using this⟩

end census

end L.Ind
