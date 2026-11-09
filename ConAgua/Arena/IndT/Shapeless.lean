module

public import ConAgua.Arena.IndArmLps
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
import ConAgua.Arena.DeclNatLit
import ConRon.Bridge.Checker.Base
import ConAgua.Arena.DeclReduceSpec2
public import ConAgua.Verdict.DeclValsE
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import all ConAgua.Arena.IndParts

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
l_model csfE_spec (p : Prog) (hV : CcvProg p)
    (hf : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
  fns [hf ↦ csfE] specs [checkConstantVal_specE p hV n] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The model of `check_shapeless`, both outcomes** (only errors): the formers by their unified
model. -/
l_model cslE_spec (p : Prog) (hV : CcvProg p)
    (hcsf : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
    (hf : p.lookup "check_shapeless" = some checkShapeless)
  fns [hf ↦ cslE] specs [csfE_spec p hV hcsf n] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


theorem erA_truncM_a5 (m : Mem) : erA (truncM m) = erecP m := truncM_erA m

/-- The head of a decoded block slice (the record word `EREC⦃off⦄` reads, over both tiers). -/
theorem decEBlk_head {dn : NIdx → Option ConLeche.Name} {m : Mem} {off cnt : Word}
    {ci : IConstantInfo} {rest : List IConstantInfo}
    (hd : DecB (fun m => decEBlk dn m off.toNat cnt.toNat) m (ci :: rest))
    (hlen : cnt.toNat = rest.length + 1) (hb : off.toNat + cnt.toNat < 2 ^ 64) :
    ∃ w : Word, erRd m off = w ∧ decCI (erA m) w.toNat = some ci ∧
      (off + 1).toNat = off.toNat + 1 ∧ (cnt - 1).toNat = rest.length ∧
      DecB (fun m => decEBlk dn m (off + 1).toNat (cnt - 1).toNat) m rest := by
  have hoff : (off + 1).toNat = off.toNat + 1 := by
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
  simp only [nat?, Option.map_eq_some_iff, truncM_erA] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  refine ⟨w, erRd_of_erA hw, ?_, hoff, hcnt, ?_⟩
  · rw [truncM_erA] at hx; exact hx
  · show decEBlk dn (truncM m) (off + 1).toNat (cnt - 1).toNat = some xs
    rw [hoff, hcnt]; exact hxs

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

/-- A decoded record's kind word, over any reader: `3` exactly for an `indInfo`. -/
theorem decCI_tag3 {R : Nat → Option Word} {q : Nat} {ci : IConstantInfo} (h : decCI R q = some ci) :
    ∃ w, R q = some w ∧ (w = 3 ↔ ∃ cv caps, ci = .indInfo cv caps) := by
  have h' := h
  simp only [decCI, Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
  obtain ⟨k, hk, -⟩ := h'
  have hk' := hk
  simp only [nat?, Option.map_eq_some_iff] at hk'
  obtain ⟨w, hw, rfl⟩ := hk'
  refine ⟨w, hw, fun h3 => ?_, fun ⟨cv, caps, hc⟩ => ?_⟩
  · subst h3
    obtain ⟨cv, caps, hc, -⟩ := decCI_kind3 h hk
    exact ⟨cv, caps, hc⟩
  · subst hc
    have := decCI_indInfo_kind h
    rw [hk] at this
    exact UInt64.toNat_inj.1 (by simpa using this)

/-- An `indInfo` record's constant value decodes at `q + 1`. -/
theorem decCI_ind_cv {R : Nat → Option Word} {q : Nat} {cv : IConstantVal} {caps : IIndCaps}
    (h : decCI R q = some (.indInfo cv caps)) : decCV R (q + 1) = some cv := by
  have hk := decCI_indInfo_kind h
  simp only [decCI, hk, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.bind_some, Option.some.injEq] at h
  obtain ⟨cv', hcv, caps', -, he⟩ := h
  cases he; exact hcv

theorem denoteCIList_cons_inv {st : ConRon.Arena.EStore} {ci : IConstantInfo}
    {rest : List IConstantInfo} {bP : List ConLeche.ConstantInfo}
    (h : Frontend.denoteCIList st (ci :: rest) = some bP) :
    (∃ x, Frontend.denoteCI st ci = some x) ∧ ∃ xs, Frontend.denoteCIList st rest = some xs := by
  unfold Frontend.denoteCIList at h
  rcases h1 : Frontend.denoteCI st ci with _ | x <;>
    rcases h2 : Frontend.denoteCIList st rest with _ | xs <;> simp [h1, h2] at h
  exact ⟨⟨x, rfl⟩, xs, rfl⟩

theorem denoteCI_ind_cv {st : ConRon.Arena.EStore} {cv : IConstantVal} {caps : IIndCaps}
    {x : ConLeche.ConstantInfo} (h : Frontend.denoteCI st (.indInfo cv caps) = some x) :
    ∃ c, Frontend.denoteCV st cv = some c := by
  rcases h1 : Frontend.denoteCV st cv with _ | c
  · simp [Frontend.denoteCI, h1] at h
  · exact ⟨c, rfl⟩

/-- **`check_shapeless_formers` refines `checkShapelessFormers .verified`, both outcomes**, by
induction on the block: each former by `ccv_ref` (con-ron's `checkConstantVal_bridge`: a core
step, so the rest of the block still denotes). -/
theorem csf_ref (hP : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcrf : CrfF p) {dn : NIdx → Option ConLeche.Name} (hCS : CcvSims p dn) {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) :
    ∀ (block : List IConstantInfo) (F : Nat), F ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (off cnt : Word),
      StageT dn vis fe m a → ConRon.Bridge.CheckOK false env fe a → L.Stubs.CrOK m →
      DecB (fun m => decEBlk dn m off.toNat cnt.toNat) m block → cnt.toNat = block.length →
      off.toNat + cnt.toNat < 2 ^ 64 → (∃ bP, Frontend.denoteCIList a.store block = some bP) →
      RefE (VerdictCtxU p) (csfE p F m vis off cnt) (ConRon.Arena.checkShapelessFormers V fe block) a
        (fun v _ a' => CsfPost dn vis fe m v.2 a') := by
  intro block
  induction block with
  | nil =>
    intro F hF m a off cnt hT _ hCr hd hlen hb _
    cases F with
    | zero => rw [csfE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
    | succ F =>
      have hc0 : cnt = 0 := UInt64.toNat_inj.1 (by simpa using hlen)
      rw [csfE.arm1 p F m vis off cnt hc0]
      exact RefE.ret rfl ⟨hT, IWGrow.refl _, hCr⟩
  | cons ci rest ih =>
    intro F hF m a off cnt hT hck hCr hd hlen hb ⟨bP, hbP⟩
    cases F with
    | zero => rw [csfE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
    | succ F =>
      obtain ⟨w, hw, hci, hoff, hcnt, hrest⟩ := decEBlk_head hd (by simpa using hlen) hb
      have hc0 : cnt ≠ 0 := fun h => by simp [h] at hlen
      have hlenr : (cnt - 1).toNat = rest.length := hcnt
      have hF' : F ≤ 2 ^ 62 := by omega
      obtain ⟨⟨ciP, hciP⟩, xs, hxs⟩ := denoteCIList_cons_inv hbP
      -- the tag word of the head
      obtain ⟨wt, hwt, hwtn⟩ := decCI_tag3 hci
      have hwt' : erRd m w = wt := erRd_of_erA hwt
      -- the rest of the block, from any state after the head
      have tail : ∀ (m1 : Mem) (a1 : AState), StageT dn vis fe m1 a1 →
          ConRon.Bridge.CheckOK false env fe a1 → ConRon.Arena.Ext a.store a1.store → IWGrow m m1 →
          L.Stubs.CrOK m1 →
          RefE (VerdictCtxU p) (csfE p F m1 vis (off + 1) (cnt - 1))
            (ConRon.Arena.checkShapelessFormers V fe rest) a1
            (fun v _ a' => CsfPost dn vis fe m v.2 a') := fun m1 a1 hT1 hck1 hx1 hg1 hCr1 =>
        (ih F hF' m1 a1 (off + 1) (cnt - 1) hT1 hck1 hCr1 (hrest.grow (decEBlk_mono _ _ _) hg1) hlenr
          (by rw [hlenr]; have := hg1.er; have := hoff; simp only [List.length_cons] at hlen; omega)
          ⟨xs, ConRon.Bridge.denoteCIList_mono hx1 _ _ hxs⟩).mono
          fun _ _ _ h => ⟨h.stage, hg1.trans h.grow, h.crOK⟩
      by_cases h3 : ∃ cv caps, ci = IConstantInfo.indInfo cv caps
      · obtain ⟨cv, caps, rfl⟩ := h3
        have hwt3 : wt = 3 := hwtn.2 ⟨cv, caps, rfl⟩
        have htag : erRd m (erRd m off) = 3 := by rw [hw, hwt', hwt3]
        have hcvd : decCV (erA m) (w.toNat + 1) = some cv := decCI_ind_cv hci
        obtain ⟨c, hc⟩ := denoteCI_ind_cv hciP
        have hlt : w.toNat + 1 + 3 < 2 ^ 64 := by
          obtain ⟨v, hv, -⟩ := (decCV_words hcvd).2.2
          exact erecP_lt64 hv
        have hw1 : (w + 1).toNat = w.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        have htw : ConRon.Arena.checkShapelessFormers V fe (IConstantInfo.indInfo cv caps :: rest) =
            (checkConstantVal V fe cv ((0 : Word) != 0) >>= fun _ =>
              ConRon.Arena.checkShapelessFormers V fe rest) := rfl
        rw [htw]
        have hqd : decCV (erecP m) (w + 1).toNat = some cv := by rw [hw1]; exact hcvd
        have hqb : (w + 1).toNat + 3 < 2 ^ 64 := by omega
        rw [csfE.arm2 p F m vis off cnt hc0 htag]
        rw [show rdW (m.arr64 (tierA EREC (off >>> 40))) (off &&& 1099511627775) = w from hw]
        refine RefE.bindE (fun _ => csfE.k_check_constant_val.none ..) id
          (ccv_ref hP hq hap hkp hcrf hCS hF' hT hqd hqb hc hCr) fun ⟨_, m1⟩ _ a1 hrun1 hP1 => ?_
        rw [csfE.k_check_constant_val.arm1, csfE.j1.arm1]
        obtain ⟨c1, -⟩ := ConRon.Bridge.checkConstantVal_bridge ConRon.Bridge.CoreSpec.of_core hck henv hc
          hrun1
        exact RefE.lastE (f := fun v => (0, v.2)) (fun _ => csfE.k_check_shapeless_formers.none ..)
          (fun _ => csfE.k_check_shapeless_formers.arm1 ..) id
          (tail _ _ hP1.stage c1.ok c1.ext hP1.grow hP1.crOK) fun _ _ _ _ h => h
      · have hne : wt ≠ 3 := fun h => h3 (hwtn.1 h)
        have htag : erRd m (erRd m off) ≠ 3 := by rw [hw, hwt']; exact hne
        have htw : ConRon.Arena.checkShapelessFormers V fe (ci :: rest) =
            ConRon.Arena.checkShapelessFormers V fe rest := by
          cases ci with
          | indInfo cv caps => exact absurd ⟨cv, caps, rfl⟩ h3
          | _ => rfl
        rw [csfE.arm3 p F m vis off cnt hc0 htag, csfE.j1.arm1, htw]
        exact RefE.lastE (f := fun v => (0, v.2)) (fun _ => csfE.k_check_shapeless_formers.none ..)
          (fun _ => csfE.k_check_shapeless_formers.arm1 ..) id
          (tail m a hT hck (ConRon.Arena.Ext.refl _) (IWGrow.refl m) hCr) fun _ _ _ _ h => h

/-- **`check_shapeless` refines `checkShapeless .verified`, both outcomes**: it never returns
(the ok case is empty); its error is the formers' (`csf_ref`) or its decline, after the twin's
formers ran ok. -/
theorem csl_ref (hP : CcvProg p) (hq : KnotStageProg p) (hap : ApdF p) (hkp : CrKeep p)
    (hcrf : CrfF p) {dn : NIdx → Option ConLeche.Name} (hCS : CcvSims p dn) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (F : Nat) (hF : F ≤ 2 ^ 62)
    (m : Mem) (a : AState) {vis : Word} {fe : IFEnv}
    {o l : Word} {block : List IConstantInfo}
    (hT : StageT dn vis fe m a) (hck : ConRon.Bridge.CheckOK false env fe a)
    (hd : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block)
    (hCr : L.Stubs.CrOK m) (hbd : ∃ bP, Frontend.denoteCIList a.store block = some bP)
    (hb : o.toNat + l.toNat < 2 ^ 64) :
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
    (csf_ref hP hq hap hkp hcrf hCS (vis := vis) (fe := fe) henv block F hF' m a o l hT hck hCr hd hlen hb
      hbd)
    fun ⟨_, _⟩ _ _ _ _ => ?_
  rw [cslE.k_check_shapeless_formers.eq_2]
  exact fun _ => ErrClaim.fail _ _ (by decide)

end

end L.Ind
