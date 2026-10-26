import ConAgua.Verdict.IndA2
import ConAgua.Arena.DeclArmT

/-!
# `check_shapeless_formers` and `check_shapeless`: ok run and error claims (lane `verdicts-b`, helper `ia`)

`check_shapeless_formers` has no ok refinement elsewhere (`check_ind_decl`'s ok proof only needs
that `check_shapeless` never returns). The verdict claim of `check_shapeless` needs more: when the
formers all run ok on the L side, the twin's `checkShapelessFormers` runs ok too (else it would
reject, class `1`, where `check_shapeless` declines, class `2`). `csfE_claim` proves both halves by
induction on the block, from the claim of `check_constant_val` (`CheckConstantValE`) and its ok
refinement `checkConstantVal_refinesT`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model csfE_spec (p : Prog) (hf : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
  fns [hf ↦ csfE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model cslE_spec (p : Prog) (hf : p.lookup "check_shapeless" = some checkShapeless)
  fns [hf ↦ cslE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

-- `check_constant_val`'s error claim, in the shape of `checkConstantVal_refinesT`
err_stmt CheckConstantValE := checkConstantVal_refinesT fuel n

theorem erA_truncM_a5 (m : Mem) : erA (truncM m) = erecP m := by
  apply Array.ext_getElem?
  intro i
  rw [truncM_er_get?]
  simp only [erecP, erecTop, erTop, Array.getElem?_extract, erA]
  by_cases h : i < (rdW (m.arr64 CTL) 129).toNat
  · simp only [h, ↓reduceIte]
    by_cases h2 : i < (m.arr64 EREC).size
    · simp [h2]; omega
    · simp [h2]
  · simp [h]; omega

/-- The head of a decoded block slice. -/
theorem decEBlk_head {dn : NIdx → Option ConLeche.Name} {m : Mem} {off cnt : Word}
    {ci : IConstantInfo} {rest : List IConstantInfo}
    (hd : DecB (fun m => decEBlk dn m off.toNat cnt.toNat) m (ci :: rest))
    (hlen : cnt.toNat = rest.length + 1) (hb : off.toNat + cnt.toNat ≤ erTop m) :
    ∃ w : Word, rdW (m.arr64 EREC) off = w ∧ decCI (erecP m) dn w.toNat = some ci ∧
      (off + 1).toNat = off.toNat + 1 ∧ (cnt - 1).toNat = rest.length ∧
      DecB (fun m => decEBlk dn m (off + 1).toNat (cnt - 1).toNat) m rest := by
  have hoff : (off + 1).toNat = off.toNat + 1 := by
    have : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
    rw [UInt64.toNat_add]; simp; omega
  have hcnt : (cnt - 1).toNat = rest.length := by
    have h1 : 1 ≤ cnt.toNat := by omega
    have := cnt.toNat_lt
    rw [UInt64.toNat_sub]
    simp
    omega
  have hd' : decEBlk dn (truncM m) off.toNat (rest.length + 1) = some (ci :: rest) := by
    rw [← hlen]; exact hd
  rw [decEBlk_succ] at hd'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd'
  obtain ⟨q, hq, x, hx, xs, hxs, heq⟩ := hd'
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  simp only [nat?, Option.map_eq_some_iff] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  obtain ⟨-, hw'⟩ := truncM_er_get hw
  refine ⟨w, ?_, ?_, hoff, hcnt, ?_⟩
  · show ((m.arr64 EREC)[off.toNat]?).getD 0 = w
    rw [show (m.arr64 EREC)[off.toNat]? = some w from hw']; rfl
  · rw [erA_truncM_a5] at hx; exact hx
  · show decEBlk dn (truncM m) (off + 1).toNat (cnt - 1).toNat = some xs
    rw [hoff, hcnt]; exact hxs

theorem mapM_denoteN_of {dn : NIdx → Option ConLeche.Name} {ns : ConRon.Arena.NStore}
    (hd : ∀ k x, dn k = some x → denoteN ns k = some x) :
    ∀ l : List NIdx, (∀ k ∈ l, (dn k).isSome) → ∃ ks, l.mapM (denoteN ns) = some ks
  | [], _ => ⟨[], rfl⟩
  | k :: l, h => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (h k (List.mem_cons_self ..))
    obtain ⟨ks, hks⟩ := mapM_denoteN_of hd l (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    exact ⟨x :: ks, by simp [List.mapM_cons, hd k x hx, hks]⟩

theorem erecP_get_lt {m : Mem} {i : Nat} {v : Word} (h : (erecP m)[i]? = some v) : i < erTop m := by
  rw [← erA_truncM_a5] at h
  exact (truncM_er_get h).1

theorem decCV_bound {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ v, a[q + 3]? = some v := by
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, hnm, lv, hlv, ty, hty, -⟩ := h
  simp only [hd?, bind, Option.bind_eq_some_iff] at hty
  obtain ⟨v, hv, -⟩ := hty
  exact ⟨v, hv⟩

section
variable {p : Prog}

/-- **`check_shapeless_formers`, both halves by induction on the block**: its model's error is
the twin's `checkShapelessFormers` failing with that class; its ok run is a twin ok run, with the
stage relation, the pools' growth and the `Cr` memo kept. -/
theorem csfE_claim (hq : KnotStageProg p) (hV : ValProg p) (hap : ApdF p) (hkp : CrKeep p)
    (eCcv : CheckConstantValE p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} :
    ∀ (block : List IConstantInfo) (F : Nat), F ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (off cnt : Word),
      StageT dn vis fe m a → L.Stubs.CrOK m →
      DecB (fun m => decEBlk dn m off.toNat cnt.toNat) m block → cnt.toNat = block.length →
      off.toNat + cnt.toNat ≤ erTop m → BlockLpsDn dn block →
      (∀ e, csfE p F m vis off cnt = .error e →
        ErrClaim (ConRon.Arena.checkShapelessFormers V fe block) a e) ∧
      (∀ r m', csfE p F m vis off cnt = .ok (r, m') →
        ∃ a', (ConRon.Arena.checkShapelessFormers V fe block).run a = .ok ((), a') ∧ StageT dn vis fe m' a' ∧
          IWGrow m m' ∧ L.Stubs.CrOK m') := by
  intro block
  induction block with
  | nil =>
    intro F hF m a off cnt hT hCr hd hlen hb hlps
    cases F with
    | zero =>
      refine ⟨fun e he => ?_, fun r m' he => ?_⟩
      · rw [csfE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
      · rw [csfE.eq_1] at he; cases he
    | succ F =>
      have hc0 : cnt = 0 := UInt64.toNat_inj.1 (by simpa using hlen)
      rw [csfE.arm1 p F m vis off cnt hc0]
      refine ⟨fun e he => (by cases he), fun r m' he => ?_⟩
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact ⟨a, rfl, hT, IWGrow.refl _, hCr⟩
  | cons ci rest ih =>
    intro F hF m a off cnt hT hCr hd hlen hb hlps
    cases F with
    | zero =>
      refine ⟨fun e he => ?_, fun r m' he => ?_⟩
      · rw [csfE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
      · rw [csfE.eq_1] at he; cases he
    | succ F =>
      obtain ⟨w, hw, hci, hoff, hcnt, hrest⟩ := decEBlk_head hd (by simpa using hlen) hb
      have hc0 : cnt ≠ 0 := fun h => by simp [h] at hlen
      have hlenr : (cnt - 1).toNat = rest.length := hcnt
      have hlen' : cnt.toNat = rest.length + 1 := by simpa using hlen
      have hlpsr : BlockLpsDn dn rest := fun cv caps hm => hlps cv caps (List.mem_cons_of_mem _ hm)
      have hF' : F ≤ 2 ^ 62 := by omega
      -- the tag word of the head
      obtain ⟨wt, hwt, hwtn⟩ := decCI_tag hci
      have hwt' : rdW (m.arr64 EREC) w = wt := by
        show ((m.arr64 EREC)[w.toNat]?).getD 0 = wt
        rw [erecP_get hwt]; rfl
      -- the rest of the block, from any state after the head
      have tail : ∀ (m1 : Mem) (a1 : AState), StageT dn vis fe m1 a1 → IWGrow m m1 → L.Stubs.CrOK m1 →
          (∀ e, csfE p F m1 vis (off + 1) (cnt - 1) = .error e →
            ErrClaim (ConRon.Arena.checkShapelessFormers V fe rest) a1 e) ∧
          (∀ r m', csfE p F m1 vis (off + 1) (cnt - 1) = .ok (r, m') →
            ∃ a', (ConRon.Arena.checkShapelessFormers V fe rest).run a1 = .ok ((), a') ∧
              StageT dn vis fe m' a' ∧ IWGrow m1 m' ∧ L.Stubs.CrOK m') :=
        fun m1 a1 hT1 hg1 hCr1 => ih F hF' m1 a1 (off + 1) (cnt - 1) hT1 hCr1
          (hrest.grow (decEBlk_mono _ _ _) hg1) hlenr
          (by rw [hoff, hlenr]; have := hg1.2.1; omega) hlpsr
      by_cases h3 : ∃ cv caps, ci = IConstantInfo.indInfo cv caps
      · obtain ⟨cv, caps, rfl⟩ := h3
        have hwt3 : wt = 3 := UInt64.toNat_inj.1 (by simpa [ciTag] using hwtn)
        have htag : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) = 3 := by rw [hw, hwt', hwt3]
        obtain ⟨cv', caps', hcvd, hc⟩ := (L.Arena.decCI_kind3 hci hwt).1 hwt3
        injection hc with h1 h2
        subst h1
        have hlt : w.toNat + 1 + 3 < 2 ^ 64 := by
          obtain ⟨v, hv⟩ := decCV_bound hcvd
          have := erecP_get_lt hv
          have : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
          omega
        have hw1 : (w + 1).toNat = w.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        have hlpsd : ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks :=
          mapM_denoteN_of (fun k x hk => hT.twin.mem.dnN k x hk) _ (hlps cv caps (List.mem_cons_self ..))
        have htw : ConRon.Arena.checkShapelessFormers V fe (IConstantInfo.indInfo cv caps :: rest) =
            (checkConstantVal V fe cv >>= fun _ => ConRon.Arena.checkShapelessFormers V fe rest) := rfl
        rw [htw]
        have hqd : decCV (erecP m) (w + 1).toNat = some cv := by rw [hw1]; exact hcvd
        have hqb : (w + 1).toNat + 3 < 2 ^ 64 := by omega
        refine ⟨fun e he => ?_, fun r m' he => ?_⟩
        · rw [csfE.arm2 p F m vis off cnt hc0 htag, hw] at he
          cases c1 : callE p F "check_constant_val" [vis, w + 1] m with
          | error e1 =>
            rw [c1, csfE.k_check_constant_val.none] at he; cases he
            exact ErrClaim.bind_left (eCcv hV hq hap hkp ⟨m, Locals.init []⟩ a dn fe vis (w + 1) cv hT hqd hqb
              hlpsd hCr F hF' _ c1)
          | ok q1 =>
            obtain ⟨r1, m1⟩ := q1
            rw [c1, csfE.k_check_constant_val.arm1, csfE.j1.arm1] at he
            have d1 := callW_of_callE c1
            obtain ⟨s1, hs1, -, hok, hT1, hg1, hCr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
              (checkConstantVal_refinesT p hV hq hap hkp F hF' ⟨m, Locals.init []⟩ a dn fe vis (w + 1) cv hT hqd
                hqb hlpsd hCr) d1
            subst hs1
            refine ErrClaim.bind_right (partsRunOfOk hok) ?_
            obtain ⟨t1, t2⟩ := tail _ _ hT1 hg1 hCr1
            cases hx : csfE p F _ vis (off + 1) (cnt - 1) with
            | error ε => rw [hx, csfE.k_check_shapeless_formers.none] at he; cases he; exact t1 _ hx
            | ok q => obtain ⟨r0, m0⟩ := q; rw [hx, csfE.k_check_shapeless_formers.eq_2] at he; cases he
        · rw [csfE.arm2 p F m vis off cnt hc0 htag, hw] at he
          cases c1 : callE p F "check_constant_val" [vis, w + 1] m with
          | error e1 => rw [c1, csfE.k_check_constant_val.none] at he; cases he
          | ok q1 =>
            obtain ⟨r1, m1⟩ := q1
            rw [c1, csfE.k_check_constant_val.arm1, csfE.j1.arm1] at he
            have d1 := callW_of_callE c1
            obtain ⟨s1, hs1, -, hok, hT1, hg1, hCr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
              (checkConstantVal_refinesT p hV hq hap hkp F hF' ⟨m, Locals.init []⟩ a dn fe vis (w + 1) cv hT hqd
                hqb hlpsd hCr) d1
            subst hs1
            obtain ⟨t1, t2⟩ := tail _ _ hT1 hg1 hCr1
            cases hx : csfE p F _ vis (off + 1) (cnt - 1) with
            | error ε => rw [hx, csfE.k_check_shapeless_formers.none] at he; cases he
            | ok q =>
              obtain ⟨r0, m0⟩ := q
              rw [hx, csfE.k_check_shapeless_formers.eq_2] at he
              simp only [Except.ok.injEq, Prod.mk.injEq] at he
              obtain ⟨-, rfl⟩ := he
              obtain ⟨a', hrun, hT', hg, hCr'⟩ := t2 r0 m0 hx
              refine ⟨a', ?_, hT', IWGrow.trans (by simpa using hg1) hg, hCr'⟩
              simp only [StateT.run_bind, partsRunOfOk hok, exc_ok_bind']
              exact hrun
      · have hne : wt ≠ 3 := by
          intro h
          have := (L.Arena.decCI_kind3 hci hwt).1 h
          obtain ⟨cv, caps, -, hc⟩ := this
          exact h3 ⟨cv, caps, hc⟩
        have htag : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 3 := by rw [hw, hwt']; exact hne
        have htw : ConRon.Arena.checkShapelessFormers V fe (ci :: rest) =
            ConRon.Arena.checkShapelessFormers V fe rest := by
          cases ci with
          | indInfo cv caps => exact absurd ⟨cv, caps, rfl⟩ h3
          | _ => rfl
        obtain ⟨t1, t2⟩ := tail m a hT (IWGrow.refl m) hCr
        refine ⟨fun e he => ?_, fun r m' he => ?_⟩
        · rw [csfE.arm3 p F m vis off cnt hc0 htag, csfE.j1.arm1] at he
          rw [htw]
          cases hx : csfE p F m vis (off + 1) (cnt - 1) with
          | error ε => rw [hx, csfE.k_check_shapeless_formers.none] at he; cases he; exact t1 _ hx
          | ok q => obtain ⟨r0, m0⟩ := q; rw [hx, csfE.k_check_shapeless_formers.eq_2] at he; cases he
        · rw [csfE.arm3 p F m vis off cnt hc0 htag, csfE.j1.arm1] at he
          cases hx : csfE p F m vis (off + 1) (cnt - 1) with
          | error ε => rw [hx, csfE.k_check_shapeless_formers.none] at he; cases he
          | ok q =>
            obtain ⟨r0, m0⟩ := q
            rw [hx, csfE.k_check_shapeless_formers.eq_2] at he
            simp only [Except.ok.injEq, Prod.mk.injEq] at he
            obtain ⟨-, rfl⟩ := he
            obtain ⟨a', hrun, hT', hg, hCr'⟩ := t2 r0 m0 hx
            exact ⟨a', by rw [htw]; exact hrun, hT', hg, hCr'⟩
theorem decEBlk_length (dn : NIdx → Option ConLeche.Name) (m : Mem) :
    ∀ (cnt off : Nat) (block : List IConstantInfo), decEBlk dn m off cnt = some block → block.length = cnt
  | 0, off, block, h => by
    simp only [decEBlk, List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | n + 1, off, block, h => by
    rw [decEBlk_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨q, -, x, -, xs, hxs, rfl⟩ := h
    simp [decEBlk_length dn m n (off + 1) xs hxs]

theorem checkShapelessE_claim (eCcv : CheckConstantValE p) : CheckShapelessE p := by
  intro hq hV hap hkp hcsf hcsl F hF m a dn vis fe o l block hT hd hCr hlps hb er he
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (cslE_spec p hcsl F ⟨m, Locals.init []⟩ vis o l) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  cases F with
  | zero => rw [cslE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ F =>
  rw [cslE.arm1] at he
  have hF' : F ≤ 2 ^ 62 := by omega
  have hlen : l.toNat = block.length :=
    (decEBlk_length dn m _ _ block (hd.get (decEBlk_mono _ _ _))).symm
  have hcl := csfE_claim hq hV hap hkp eCcv (dn := dn) (vis := vis) (fe := fe) block F hF' m a o l hT hCr hd hlen hb hlps
  unfold ConRon.Arena.checkShapeless
  cases c1 : callE p F "check_shapeless_formers" [vis, o, l] m with
  | error e1 =>
    rw [c1, cslE.k_check_shapeless_formers.none] at he
    cases he
    have h1 := triple_of_callE_err (csfE_spec p hcsf F ⟨m, Locals.init []⟩ vis o l) c1 (Err.code_ne_of_cls hk0)
    simp only at h1
    exact ErrClaim.bind_left (hcl.1 _ h1)
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [c1, cslE.k_check_shapeless_formers.eq_2] at he
    cases he
    obtain ⟨s', hs, -, h1⟩ := triple_of_callE (csfE_spec p hcsf F ⟨m, Locals.init []⟩ vis o l) c1
    simp only at hs h1
    subst hs
    obtain ⟨a', hrun, -⟩ := hcl.2 _ _ h1
    exact ErrClaim.bind_right hrun (ErrClaim.fail _ _ (by decide))

end

end L.Ind
