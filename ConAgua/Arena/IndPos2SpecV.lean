import ConAgua.Arena.IndPos2SpecU

/-! # `IndPos2`, the root frame and the seeds (lane `indproofs2`, helper `pos2`): the models
simulated by the twin (`nestRoot`, `nestSeeds`, the seeds' fuel fold), and the census theorems. -/

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

theorem p2sfW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (hM : PosMemo dn vis fe)
    (dO dL : Word) (ds : List EIdx) (m0 : Mem) (hlen : ds.length = dL.toNat)
    (hel : ∀ j < dL.toNat, ∃ w, (m0.arr64 IW)[dO.toNat + j]? = some w ∧ H w ∧ ds[j]? = some (decI w))
    (hb : dO.toNat + dL.toNat ≤ iwTop m0) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (k f : Word) (r : List Word),
    p2sfW n m dO dL k f = some (r, m') → StageR dn vis fe m a → IWGrow m0 m → k.toNat ≤ dL.toNat →
    ∃ a', ((ds.drop k.toNat).foldlM pos2FuelF f.toNat).run a = .ok ((r.headD 0).toNat, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m'
  | 0, m, m', a, k, f, r, h, _, _, _ => by simp [p2sfW] at h
  | n + 1, m, m', a, k, f, r, h, hS, hg0, hk => by
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hd : dL ≤ k
    · rw [p2sfW_done (h := hd)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : k.toNat = dL.toNat := Nat.le_antisymm hk (UInt64.le_iff_toNat_le.mp hd)
      rw [this, ← hlen, List.drop_length]
      exact ⟨a, rfl, hS, IWGrow.refl _⟩
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
    obtain ⟨mp, hmp⟩ := hM.dp m a hS
    obtain ⟨d, hrunw, hwd, -, hS1, hg1⟩ := wfW_ok n' dn fe vis m m1 a w wv mp hwW hS hH hmp
    have hk1 : (k + 1).toNat = k.toNat + 1 := word_add_toNat (by simp; omega)
    obtain ⟨a', hrun, hS', hg'⟩ := p2sfW_ok dn vis fe hM dO dL ds m0 hlen hel hb n m1 m' a (k + 1) _ r h hS1
      (hg0.trans hg1) (by omega)
    refine ⟨a', ?_, hS', hg1.trans hg'⟩
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
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (hM : PosMemo dn vis fe)
  (hcs : CtorSums fe) (ctx hO hL : Word) (c : NestCtx) (holes : List EIdx)

include hM hcs in
/-- **`nest_root`** simulated by `nestRoot`. -/
theorem p2rtW_ok : ∀ (n : Nat), 2 ^ 31 + n ≤ coreWalkFuel → ∀ (m m' : Mem) (a : AState) (cO cL ns oO oL : Word)
    (css : List (List (IConstantVal × Nat))) (NS : NestState) (outss : List (List (List NestFieldKind × EIdx)))
    (r : List Word),
    p2rtW n m vis ctx hO hL cO cL ns oO oL = some (r, m') → StageR dn vis fe m a → UCtx dn vis fe m ctx c →
    c.hiAt 0 < 2 ^ 64 → c.params.length + c.names.length < 2 ^ 64 →
    decHL m hO.toNat hL.toNat = some holes → hO.toNat + hL.toNat ≤ iwTop m →
    cL.toNat = css.length → cO.toNat + css.length ≤ iwTop m → CssAt m cO.toNat css → NSB m ns NS →
    RootOutsB m oO.toNat oL.toNat outss → oO.toNat + oL.toNat ≤ iwTop m →
    ∃ x a', (nestRoot V fe c holes css NS outss).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      RootOutsB m' (r.headD 0).toNat (r.tail.headD 0).toNat x.1 ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ NSB m' (r.tail.tail.headD 0) x.2
  | 0, _, m, m', a, cO, cL, ns, oO, oL, css, NS, outss, r, h, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp [p2rtW] at h
  | n + 1, hn, m, m', a, cO, cL, ns, oO, oL, css, NS, outss, r, h, hS, hU, hhi, hpn, hho, hhob, hcl, hcb, hcss,
      hns, hout, houtb => by
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
        by simpa using houtb, by simpa using hns⟩
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
    have hCt := (nbOK_all dn vis fe hM hcs n (by omega)).2.2.2.2.2.2.2.1
    cases hc : nbCtorsW n m vis ctx 1 0 0 0 (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 10))
        (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8)) (rdW (m.arr64 IW) ctx)
        (rdW (m.arr64 IW) (ctx + 1)) hO hL cO' cL' ns 0 0 with
    | none => rw [hc] at h; simp [p2rtK1] at h
    | some pr =>
    obtain ⟨r1, m1⟩ := pr
    rw [hc, p2rtK1_some] at h
    obtain ⟨x1, a1, hrun1, hS1, hg1, hO1, hOb1, hns1⟩ := hCt m m1 a ctx 1 0 0 0 (nhiW m ctx 0) _ _ _ _ _ hO hL cO'
      cL' ns 0 0 c [] c.params c.names holes cs NS [] r1 hc hS hW hC hcl' hcb' hcsAt hns (by simpa using OutsB.nil m 0)
      (by simp)
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
    obtain ⟨x, a', hrun, hS', hg', hO', hOb', hns'⟩ := p2rtW_ok n (by omega) m3 m' a1 (cO + 1) (cL - 1)
      (r1.tail.tail.headD 0) (ro.headD 0) (ro.tail.headD 0) css' x1.2 (outss ++ [x1.1]) r h hS3 (hU.grow hg13) hhi
      hpn (by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by omega)]; exact hho)
      (by have := hg13.1; omega) hcL1 (by rw [hcO1]; have := hg13.1; omega)
      (by rw [hcO1]; exact (hcss.grow hg13).tail)
      ((hns1.grow hg2 htop1).grow hg3 htop2) hout3 (by rw [h30, h31]; omega)
    refine ⟨x, a', ?_, hS', hg13.trans hg', hO', hOb', hns'⟩
    simp only [ConRon.Arena.nestRoot, StateT.run_bind]
    rw [hrun1']
    exact hrun

end root

end L.Ind
