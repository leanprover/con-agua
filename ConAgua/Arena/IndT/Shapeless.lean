module

public import ConAgua.Arena.IndArmLps
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.DeclNatLit
import ConAgua.Arena.DeclReduceSpec2
public import ConAgua.Verdict.DeclValsE
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved

@[expose] public section

/-!
# `check_shapeless_formers` and `check_shapeless`: one model and one refinement each

`check_shapeless_formers` checks the block's formers as constants (`check_constant_val` by its
unified model, `ccv_ref`); `check_shapeless` runs it and declines. So `check_shapeless` never
returns: the ok case of `csl_ref` is empty. Its error is the formers' (`csf_ref`, by induction on
the block) or the decline, where the twin's `checkShapelessFormers` ran ok (else it would reject,
class `1`, where `check_shapeless` declines, class `2`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **The model of `check_shapeless_formers`, both outcomes**: `check_constant_val` by its unified
model. -/
l_model csfE_spec (p : Prog) (hV : ValProg p)
    (hf : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
  fns [hf ↦ csfE] specs [checkConstantVal_specE p hV n] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The model of `check_shapeless`, both outcomes** (only errors): the formers by their unified
model. -/
l_model cslE_spec (p : Prog) (hV : ValProg p)
    (hcsf : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
    (hf : p.lookup "check_shapeless" = some checkShapeless)
  fns [hf ↦ cslE] specs [csfE_spec p hV hcsf n] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

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

section
variable {p : Prog}

/-- What `check_shapeless_formers` gives besides the twin's run (from `m`): the stage relation,
the pools' growth, the `Cr` memo. -/
structure CsfPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  crOK : L.Stubs.CrOK m'

/-- **`check_shapeless_formers` refines `checkShapelessFormers .verified`, both outcomes**, by
induction on the block: each former by `ccv_ref`. -/
theorem csf_ref (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} :
    ∀ (block : List IConstantInfo) (F : Nat), F ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (off cnt : Word),
      StageT dn vis fe m a → L.Stubs.CrOK m →
      DecB (fun m => decEBlk dn m off.toNat cnt.toNat) m block → cnt.toNat = block.length →
      off.toNat + cnt.toNat ≤ erTop m → BlockLpsDn dn block →
      RefE (VerdictCtxU p) (csfE p F m vis off cnt) (ConRon.Arena.checkShapelessFormers V fe block) a
        (fun v _ a' => CsfPost dn vis fe m v.2 a') := by
  intro block
  induction block with
  | nil =>
    intro F hF m a off cnt hT hCr hd hlen hb hlps
    cases F with
    | zero => rw [csfE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
    | succ F =>
      have hc0 : cnt = 0 := UInt64.toNat_inj.1 (by simpa using hlen)
      rw [csfE.arm1 p F m vis off cnt hc0]
      exact RefE.ret rfl ⟨hT, IWGrow.refl _, hCr⟩
  | cons ci rest ih =>
    intro F hF m a off cnt hT hCr hd hlen hb hlps
    cases F with
    | zero => rw [csfE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
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
          RefE (VerdictCtxU p) (csfE p F m1 vis (off + 1) (cnt - 1))
            (ConRon.Arena.checkShapelessFormers V fe rest) a1
            (fun v _ a' => CsfPost dn vis fe m v.2 a') := fun m1 a1 hT1 hg1 hCr1 =>
        (ih F hF' m1 a1 (off + 1) (cnt - 1) hT1 hCr1 (hrest.grow (decEBlk_mono _ _ _) hg1) hlenr
          (by rw [hoff, hlenr]; have := hg1.er; omega) hlpsr).mono
          fun _ _ _ h => ⟨h.stage, hg1.trans h.grow, h.crOK⟩
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
        rw [csfE.arm2 p F m vis off cnt hc0 htag, hw]
        refine RefE.bindE (fun _ => csfE.k_check_constant_val.none ..) id
          (ccv_ref hq hap hkp hF' hT hqd hqb hlpsd hCr) fun ⟨_, m1⟩ _ a1 _ hP1 => ?_
        rw [csfE.k_check_constant_val.arm1, csfE.j1.arm1]
        exact RefE.lastE (f := fun v => (0, v.2)) (fun _ => csfE.k_check_shapeless_formers.none ..)
          (fun _ => csfE.k_check_shapeless_formers.arm1 ..) id (tail _ _ hP1.stage hP1.grow hP1.crOK)
          fun _ _ _ _ h => h
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
        rw [csfE.arm3 p F m vis off cnt hc0 htag, csfE.j1.arm1, htw]
        exact RefE.lastE (f := fun v => (0, v.2)) (fun _ => csfE.k_check_shapeless_formers.none ..)
          (fun _ => csfE.k_check_shapeless_formers.arm1 ..) id (tail m a hT (IWGrow.refl m) hCr)
          fun _ _ _ _ h => h

/-- **`check_shapeless` refines `checkShapeless .verified`, both outcomes**: it never returns
(the ok case is empty); its error is the formers' (`csf_ref`) or its decline, after the twin's
formers ran ok. -/
theorem csl_ref (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p) (F : Nat) (hF : F ≤ 2 ^ 62)
    (m : Mem) (a : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {o l : Word} {block : List IConstantInfo}
    (hT : StageT dn vis fe m a) (hd : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block)
    (hCr : L.Stubs.CrOK m) (hlps : BlockLpsDn dn block) (hb : o.toNat + l.toNat ≤ erTop m) :
    RefE (VerdictCtxU p) (cslE p F m vis o l) (ConRon.Arena.checkShapeless V fe block) a
      (fun _ _ _ => False) := by
  cases F with
  | zero => rw [cslE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ F =>
  rw [cslE.arm1]
  have hF' : F ≤ 2 ^ 62 := by omega
  have hlen : l.toNat = block.length :=
    (decEBlk_length dn m _ _ block (hd.get (decEBlk_mono _ _ _))).symm
  unfold ConRon.Arena.checkShapeless
  refine RefE.bindE (fun _ => cslE.k_check_shapeless_formers.none ..) id
    (csf_ref hq hap hkp (dn := dn) (vis := vis) (fe := fe) block F hF' m a o l hT hCr hd hlen hb hlps)
    fun ⟨_, _⟩ _ _ _ _ => ?_
  rw [cslE.k_check_shapeless_formers.eq_2]
  exact fun _ => ErrClaim.fail _ _ (by decide)

end

end L.Ind
