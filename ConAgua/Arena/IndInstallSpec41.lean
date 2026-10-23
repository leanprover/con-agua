import ConAgua.Arena.IndInstallSpec40
import ConAgua.Arena.IndInstallSpec30
import ConAgua.Arena.IndInstallSpec38
import ConAgua.Arena.RecCheckSpec24
import ConAgua.Arena.RecGenSpec11
import ConAgua.Arena.RecGenSpec12
import ConAgua.Arena.RecClassSpecM
import ConAgua.Arena.IndSumSpec
import ConAgua.Arena.IndRealNames


/-!
# Refinements of `IndInstall`, part 41 (lane `indproofs4`, helper `grc`): `genRecCheck`

`gen_rec_check` (`RecGen.lean`) refines the twin's `genRecCheck` (`genRecCheck_refines`), and with
it `check_block_rec` refines `checkBlockRec` (`checkBlockRec_refines`, formerly through the pending
contract `genRecCheck_pending`).

* The twin is cut into continuation-passing parts (`grcTwinA` … `grcTwinR`; `genRecCheck_split`
  by `rfl`), one per part of the L code: `gen_rec_check_prep`'s pins, stream and guards
  (`grpAW_ok`), its classes, constructors, count, formers and level (`grpBW_ok`), its generator
  record, prefix and recursor types (`grpCW_ok`), then `gen_rec_check`'s pushes, rules, pops and
  flushes (`gckW_sim`).
* Glue: stable slices decoded below the tops (`spl_decB`, `csRes_decB`), the class reading's words
  (`crWords`), a fresh `ClassGen` record (`cgRec_decB`), the classes' constructor level-parameter
  slices through `classes_nfs` (`classesNfs_refinesLp`, from `CnsRec`'s source pointer), the
  prefix's slice fresh (`gpbW_simF`), the walk memos across `target_rec_pins` and
  `class_stream_recs` by their program text (`RcMR.ofClosed`).
* `block_large_elim_allowed` enters through its stub contract (`IndInstallSpec39`).

Hypotheses beyond the stage relation and the decodings: `RecsB` (the shape's recursor slice below
the top, also when empty), `ClassesLp` (the classes' constructors' level-parameter slices in
`EREC`, `classes_ctors`' own hypothesis), `RcMR`, `AbsOK`, and the program facts `GrcProg p`,
`closedA p rcFreeA rcFreeC fsR`, `AbsKeep` of `grcKeepCallees`. The word bounds `classes_ctors` and
the generator need (the pool's size `+ 5`, `nP + k`, `nP + slots`) come from `gen_rec_check_prep`'s
capacity guards.
-/

noncomputable section
set_option experimental.vcgen true
set_option linter.deprecated false
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena
local notation "V" => ConLeche.CheckMode.verified

-- ==== Tw2.lean


section twin
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (nestedBit : Bool)
    (params : List EIdx) (tbl : List NestCtorNf) (rd : ClassRead) (ms : List TargetMajor)
    (cvTas : List IConstantVal) (block : List IConstantInfo) {β : Type}

/-- The twin's `genRecCheck`, part A: the pins, the stream's recursor types, the guards. -/
def grcTwinA (k : List IConstantVal → AM β) : AM β := do
  ConRon.Arena.targetRecPins p block
  let cvRis ← ConRon.Arena.classStreamRecs mode fe p.recs
  if p.k == 0 then
    ConRon.Arena.fail (.invalid "generated recursor: the block declares no family")
  if p.large then
    let nb := nestedBit || ms.any (·.member.isNone)
    unless ← ConRon.Arena.blockLargeElimAllowed p nb do
      ConRon.Arena.fail (.invalid "generated recursor: large eliminator on a block whose sort may be Prop \
        (official: elim_only_at_universe_zero)")
  k cvRis

/-- Part B: the classes' entries and constructors, the count, the formers, the level. -/
def grcTwinB (k : List TargetMajor → List (List ConRon.Arena.ClassCtor) → List EIdx → LIdx → AM β) :
    AM β := do
  let formerTys := cvTas.map (·.type)
  let ms2 ← ConRon.Arena.classesNfs mode fe p formerTys tbl ms
  let ctors ← ConRon.Arena.classesCtors mode fe p formerTys rd ms2 0 ms2
  unless (rd.slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum do
    ConRon.Arena.fail (.invalid "generated recursor: the recursors' prefix has a minor premise for no \
      constructor of a class (official: invalid recursor)")
  let formerTysC ← ms2.mapM (ConRon.Arena.classFormerTy fe cvTas)
  let elim ← ConRon.Arena.structElimLevel p.elim p.large
  k ms2 ctors formerTysC elim

/-- Part C: the generator, its prefix, the recursor types. -/
def grcTwinC (cvRis : List IConstantVal) (ms2 : List TargetMajor)
    (ctors : List (List ConRon.Arena.ClassCtor)) (formerTysC : List EIdx) (elim : LIdx)
    (k : ConRon.Arena.ClassGen → List IConstantVal → AM β) : AM β := do
  let g0 : ConRon.Arena.ClassGen := ⟨p.nP, params, ms2, formerTysC, rd.slots, ctors, elim, []⟩
  match ← g0.prefixBinders with
  | none => ConRon.Arena.fail (.internal "generated recursor: recursor prefix")
  | some pre => do
    let g := { g0 with pre := pre }
    let cvGs ← ConRon.Arena.classRecTysOk mode fe g p.k p.recs cvRis rd.recCls
    k g cvGs

/-- The rest: the pushes, the rules, the pops. -/
def grcTwinR (g : ConRon.Arena.ClassGen) (cvGs : List IConstantVal) :
    AM (IFEnv × List (IConstantVal × TargetMajor × List EIdx)) := do
  let visT := fe.visibleBelow
  let (feR, prevs) := ConRon.Arena.classFeR p cvGs rd.recCls fe
  ConRon.Arena.flushCaches
  let out ← ConRon.Arena.classRecsRulesOk mode visT feR g rd.recCls cvGs cvGs rd.recCls
  let fe2 := prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feR
  ConRon.Arena.flushCaches
  pure (fe2, out)

end twin

theorem genRecCheck_split (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (nestedBit : Bool)
    (params : List EIdx) (tbl : List NestCtorNf) (rd : ClassRead) (ms : List TargetMajor)
    (cvTas : List IConstantVal) (block : List IConstantInfo) :
    ConRon.Arena.genRecCheck mode fe p nestedBit params tbl rd ms cvTas block =
      grcTwinA mode fe p nestedBit ms block (fun cvRis =>
        grcTwinB mode fe p tbl rd ms cvTas (fun ms2 ctors ftc elim =>
          grcTwinC mode fe p params rd cvRis ms2 ctors ftc elim (grcTwinR mode fe p rd))) := rfl


-- ==== G1.lean





/-! ## Decodings -/

theorem iwGrow_truncM (m : Mem) : IWGrow m (truncM m) := by
  have hc : (truncM m).arr64 CTL = m.arr64 CTL := by
    simp only [truncM, Mem.arr64, Array.getD_eq_getD_getElem?]
    simp [Array.set!_eq_setIfInBounds, CTL, IW, EREC]
  refine ⟨by simp only [iwTop, hc]; exact Nat.le_refl _, by simp only [erTop, hc]; exact Nat.le_refl _,
    fun i hi => ?_, fun i hi => ?_⟩
  · have := truncM_iw_eq (m := m) hi; simpa [iwA] using this
  · have := truncM_er_eq (m := m) hi; simpa [erA] using this

theorem StabD.decB {α : Type} {f : Mem → Option α} {m : Mem} {x : α} (h : StabD f m x) : DecB f m x :=
  h _ (iwGrow_truncM m)

theorem mapM_of_stab {α : Type} {dec : Mem → Nat → Option α} {m : Mem} :
    ∀ {ps : List Nat} {xs : List α}, FA2 (fun q x => StabD (fun m => dec m q) m x) ps xs →
      ps.mapM (dec (truncM m)) = some xs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h1 h2 => by
    have e := h1.decB
    simp only [DecB] at e
    simp only [List.mapM_cons, e, mapM_of_stab h2]; rfl

/-- A stable pointer slice is decoded below the tops. -/
theorem spl_decB {α : Type} {dec : Mem → Nat → Option α} {m : Mem} {o l : Nat} {xs : List α}
    (h : SPL dec m o l xs) : DecB (fun m => decPL m (dec m) o l) m xs := by
  obtain ⟨hb, ps, hps, hf⟩ := h
  show decPL (truncM m) (dec (truncM m)) o l = some xs
  rw [decPL_eq_bind, show decNL (truncM m) o l = some ps from decNL_decB hps hb]
  exact mapM_of_stab hf

/-! ## `ClassesLp` through `classes_nfs` -/

theorem classesLp_of_cnsRec {mb mF : Mem} {mo ml qr : Word} {hi : Nat} {ws : List Nat}
    {xs : List TargetMajor} (hlp : ClassesLp mb mo ml) (hg : IWGrow mb mF) (hk : KeepW mb mF)
    (hsz : (mb.arr64 IW).size < 2 ^ 64)
    (hws : decNL mF qr.toNat ml.toNat = some ws) (hacc : FA2 (CnsRec mb (CnsSrc mb mo ml) hi mF) ws xs) :
    ClassesLp mF qr ml := by
  intro c hc v o l hv ho hl
  have hpl := decNL_length mF hws
  have hq := mapM_opt_get (fun j => iwN mF (qr.toNat + j)) (List.range ml.toNat) ws hws c (by simpa using hc)
  simp only [List.getElem_range] at hq
  rw [hv] at hq
  have hlen := FA2.length_eq hacc
  have hR := FA2.get hacc c (by omega) (by omega)
  simp only [Option.some.injEq] at hq
  rw [← hq] at hR
  obtain ⟨p0, src, eo, el, ps, hsrc, ⟨c', hc', hp0⟩, hw, htop, hwords, -⟩ := hR
  have w6 := hwords 6 (by omega) (by omega) (by omega)
  have w7 := hwords 7 (by omega) (by omega) (by omega)
  have ho' : iwN (truncM mb) (p0 + 6) = some o := by
    simp only [iwN, nat?] at ho ⊢; rw [← w6]; simpa [iwA] using ho
  have hl' : iwN (truncM mb) (p0 + 7) = some l := by
    simp only [iwN, nat?] at hl ⊢; rw [← w7]; simpa [iwA] using hl
  have hs : decTM (truncM mb) p0 = some src := hsrc
  simp only [decTM, bind, Option.bind_eq_some_iff, pure] at hs
  obtain ⟨_, -, _, -, _, -, _, -, _, -, cts, hct, -⟩ := hs
  obtain ⟨o', l', ho'', hl'', hdct⟩ := decAt_some hct
  rw [ho'] at ho''; rw [show p0 + 6 + 1 = p0 + 7 by omega, hl'] at hl''
  cases ho''; cases hl''
  have hol : o < 2 ^ 64 ∧ l < 2 ^ 64 := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at ho' hl'
    obtain ⟨w1, -, rfl⟩ := ho'; obtain ⟨w2, -, rfl⟩ := hl'
    exact ⟨w1.toNat_lt, w2.toNat_lt⟩
  have h1 := (rec2IwN_trunc ho').2
  have h2 := (rec2IwN_trunc hl').2
  have hL := hlp c' hc' p0 o l hp0 h1 h2
  refine hL.grow (cAs := cts) ?_ hsz hg hk
  show decPL (truncM mb) (decCN (truncM mb)) _ _ = some cts
  rw [UInt64.toNat_ofNat_of_lt' hol.1, UInt64.toNat_ofNat_of_lt' hol.2]
  exact hdct

/-- **`classes_nfs` refines `classesNfs`**, with the classes' constructor records' level-parameter
slices (`ClassesLp`) carried to the result. -/
theorem classesNfs_refinesLp {p : Prog} (P : CnsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl tblo tbll mo ml : Word)
    (bs : BlockShape) (formerTys : List EIdx) (tbl : List NestCtorNf) (ms : List TargetMajor)
    (hS : StageR dn vis fe s₀.mem a₀) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tblo tbll s₀.mem) (hms : PSlR decTM ms mo ml s₀.mem) (hP : RcMR s₀.mem)
    (hlp : ClassesLp s₀.mem mo ml) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_nfs" [vis, q, fto, ftl, tblo, tbll, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀ ∧
      PSlR decTM (AM.res (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) (r.headD 0) (r.tail.headD 0) s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classesNfs V fe bs formerTys tbl ms) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧
      (KeepW s₀.mem s'.mem → ClassesLp s'.mem (r.headD 0) (r.tail.headD 0)); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
  refine triple_post (cnfs_spec p P.cns n s₀ vis q fto ftl tblo tbll mo ml) ?_
  rintro r s' ⟨hl, hm⟩
  rw [cnfsW_eq] at hm
  cases c0 : callW p n "iw_alloc" [ml] s₀.mem with
  | none => rw [c0] at hm; cases hm
  | some x0 =>
  obtain ⟨r0, m0⟩ := x0
  rw [c0, cnfsK1_some] at hm
  cases c1 : cnsW p (n + 1) m0 vis q fto ftl tblo tbll mo ml (r0.headD 0) 0 with
  | none => rw [c1] at hm; cases hm
  | some mF =>
  rw [c1, cnfsK2_some] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, hmF⟩ := hm
  obtain ⟨s0, hs0, -, hw0⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩) (iwAlloc_specW p P.ha n _ ml) c0
  simp only at hs0 hw0; subst hs0
  obtain ⟨hS0, hg0, hq0, ht0⟩ := allocW_stage hw0 hS
  obtain ⟨rest, a', run, hSF, hgF, htF, hPF, ws', hws', hacc'⟩ := cnsW_ok P dn fe vis q fto ftl tblo tbll mo ml
    (r0.headD 0) bs formerTys tbl ms s₀.mem hq0 hms htbl hbs hft hftb (n + 1) s0.mem mF a₀ 0 [] [] c1 hS0 hg0
    (by omega) (hP.fr (allocW_mfr hw0)) UInt64.zero_le (by simp [decNL]) FA2.nil
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hacc'
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  rw [← hmF]
  refine ⟨hl, hok, ?_, by rw [hst]; exact hSF, hgF, hPF, fun hk => ?_⟩
  · rw [hres]
    refine ⟨?_, by simpa using htF⟩
    show decPL (truncM mF) (decTM (truncM mF)) _ _ = some rest
    simp only [List.headD_cons, List.tail_cons]
    rw [decPL_eq_bind, show decNL (truncM mF) (r0.headD 0).toNat ml.toNat = some ws' from decNL_decB hws' htF]
    exact cnsRec_mapM hgF hacc'
  · simp only [List.headD_cons, List.tail_cons]
    exact classesLp_of_cnsRec hlp hgF hk hS.2.2.2.1 hws' hacc'

/-! ## Memo frames from the program text -/

/-- Every word array below 256 but the recursor check's walk memos. -/
def rcFreeA : List ArrId := (List.range 256).filter (fun b => b ∉ [NOM, DPM, RAM, HBM, RFM, TAM])
/-- Every `CTL` word below 256 but those memos' control words. -/
def rcFreeC : List Word :=
  ((List.range 256).filter (fun c => c ∉ [204, 206, 208, 210, 212, 213, 214, 218, 219])).map Nat.toUInt64

theorem rcFree_mfr {m m' : Mem} (h : MemFrame rcFreeA rcFreeC m m') :
    MFr [MAM, MCM] [202, 203, 205, 207, 209, 211, 215, 216, 217] m m' := by
  refine ⟨rcFreeA, rcFreeC, h, fun b hb => ?_, fun x hx => ?_⟩
  · simp only [rcFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    simp only [NOM, DPM, RAM, HBM, RFM, TAM, MAM, MCM, ArrId] at hb ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · simp only [rcFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    obtain ⟨c, ⟨hc, h2⟩, rfl⟩ := hx
    have : (Nat.toUInt64 c).toNat = c := by simp; omega
    rw [this]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_cases h1 : c < 202
    · exact .inl h1
    by_cases h2' : 219 < c
    · exact .inr (.inl h2')
    right; right
    have : c = 202 ∨ c = 203 ∨ c = 205 ∨ c = 207 ∨ c = 209 ∨ c = 211 ∨ c = 215 ∨ c = 216 ∨ c = 217 := by
      omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A callee of a program whose text writes outside the recursor check's walk memos keeps `RcMR`. -/
theorem RcMR.ofClosed {p : Prog} {fs : List FnName} (hcl : closedA p rcFreeA rcFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : RcMR m) : RcMR m' := by
  have hfr := rcFree_mfr (run_memFrame hcl hf (run_of_callW h)).1
  exact ⟨hM.pos.mfr hfr (by simp [PosAv, NOM, DPM, RAM, HBM, RFM, MAM, MCM]),
    let ⟨mp, hm⟩ := hM.ta; ⟨mp, taMR_mfr hfr (by decide) (by decide) hm⟩⟩


-- ==== S41A.lean
/-! ## The program bundle -/

/-- The lookups of `gen_rec_check` and its callees. -/
structure GrcProg (p : Prog) : Prop where
  rp : RpLook p
  cpy : p.lookup "iw_copy" = some iwCopy
  ia : p.lookup "iw_alloc" = some iwAlloc
  slc : p.lookup "sl_cons" = some slCons
  csr : p.lookup "class_stream_recs" = some classStreamRecsL
  anm : p.lookup "gen_rec_check_any_no_member" = some genRecCheckAnyNoMember
  gft : p.lookup "gen_rec_check_former_tys" = some genRecCheckFormerTys
  cns : CnsProg p
  ccs : CcsProg p
  csm : p.lookup "class_slot_is_minor" = some classSlotIsMinor
  gmo : p.lookup "gen_rec_check_minor_ok" = some genRecCheckMinorOk
  cft : CftProg p
  gftc : p.lookup "gen_rec_check_former_tys_c" = some genRecCheckFormerTysC
  sel : SelProg p
  pb : PbProg p
  rts : RtsProg p
  cfr : CfrProg p
  flush : FlushProg p
  crr : CrrProg p
  eix : p.lookup "env_ix" = some envIxL
  ers : p.lookup "env_row_set" = some envRowSetL
  ept : p.lookup "env_pop_temp" = some envPopTempL
  gpa : p.lookup "gen_rec_check_pop_all" = some genRecCheckPopAll
  prep : p.lookup "gen_rec_check_prep" = some genRecCheckPrep
  grc : p.lookup "gen_rec_check" = some genRecCheckL

/-- The callees of `gen_rec_check_prep` that keep the recursor check's walk memos by their program
text. -/
def grcMemoCallees : List FnName := ["target_rec_pins", "class_stream_recs"]

/-- The callees of `gen_rec_check` outside the `abstract1` cascade, which keep its memo (`AbsKeep`,
a program fact). -/
def grcKeepCallees : List FnName :=
  ["target_rec_pins", "class_stream_recs", "gen_rec_check_former_tys", "classes_nfs", "classes_ctors",
    "gen_rec_check_former_tys_c", "struct_elim_level", "class_fe_r", "gen_rec_check_pop_all"]

/-- The recursor shapes' slice of the shape at `pp` lies below the top. -/
def RecsB (m : Mem) (pp : Word) : Prop :=
  ∀ o l, iwN m (pp.toNat + 2) = some o → iwN m (pp.toNat + 3) = some l → o + l ≤ iwTop m

theorem RecsB.grow {m m' : Mem} {pp : Word} (h : RecsB m pp) (hg : IWGrow m m') (h3 : pp.toNat + 3 < iwTop m) :
    RecsB m' pp := by
  intro o l ho hl
  rw [iwN_grow hg (by omega)] at ho
  rw [iwN_grow hg h3] at hl
  exact Nat.le_trans (h o l ho hl) hg.1

/-- A number slice decoded in the cut pool is below the top (or empty). -/
theorem decNL_trunc_slice {m : Mem} {o l : Nat} {xs : List Nat} (h : decNL (truncM m) o l = some xs) :
    l = 0 ∨ o + l ≤ iwTop m := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact .inl h0
  right
  have hg := mapM_opt_get (fun j => iwN (truncM m) (o + j)) (List.range l) xs h (l - 1) (by simp; omega)
  simp only [List.getElem_range] at hg
  have := (rec2IwN_trunc hg).1
  omega

/-- **A class reading's words**: its slots' and its recursor classes' slices. -/
theorem crWords {m : Mem} {rd : Word} {R : ConRon.Arena.ClassRead} (h : DecB (fun m => decCR m rd.toNat) m R) :
    rd.toNat + 3 < iwTop m ∧
    DecB (fun m' => decPL m' (decCS m') (rdW (m.arr64 IW) rd).toNat (rdW (m.arr64 IW) (rd + 1)).toNat) m R.slots ∧
    DecB (fun m' => decNL m' (rdW (m.arr64 IW) (rd + 2)).toNat (rdW (m.arr64 IW) (rd + 3)).toNat) m R.recCls ∧
    (rdW (m.arr64 IW) (rd + 2)).toNat + (rdW (m.arr64 IW) (rd + 3)).toNat < 2 ^ 64 ∧
    (rdW (m.arr64 IW) rd).toNat + (rdW (m.arr64 IW) (rd + 1)).toNat < 2 ^ 64 := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have h' : decCR (truncM m) rd.toNat = some R := h
  simp only [decCR, bind, Option.bind_eq_some_iff, pure] at h'
  obtain ⟨sl, hsl, rc, hrc, hR⟩ := h'
  have hRs : R = ⟨sl, rc⟩ := by rw [← Option.some.inj hR]
  subst hRs
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hsl
  obtain ⟨o2, l2, ho2, hl2, hd2⟩ := decAt_some hrc
  have t3 := (rec2IwN_trunc hl2).1
  have e0 : rd.toNat = rd.toNat := rfl
  have e1 : (rd + 1).toNat = rd.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (rd + 2).toNat = rd.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (rd + 3).toNat = rd.toNat + 2 + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨w0, b0⟩ := bpWord ho e0
  obtain ⟨w1, b1⟩ := bpWord hl e1
  obtain ⟨w2, b2⟩ := bpWord ho2 e2
  obtain ⟨w3, b3⟩ := bpWord hl2 e3
  rw [w0, w1, w2, w3, UInt64.toNat_ofNat_of_lt' b0, UInt64.toNat_ofNat_of_lt' b1, UInt64.toNat_ofNat_of_lt' b2,
    UInt64.toNat_ofNat_of_lt' b3]
  refine ⟨by omega, hd, hd2, ?_, ?_⟩
  · rcases decNL_trunc_slice hd2 with h0 | h0 <;> omega
  · rcases Nat.eq_zero_or_pos l with h0 | h0
    · omega
    · have hg := mapM_opt_get (fun j => do (decCS (truncM m)) (← iwN (truncM m) (o + j))) (List.range l) sl hd
        (l - 1) (by simp; omega)
      simp only [List.getElem_range, Option.bind_eq_bind, Option.bind_eq_some_iff] at hg
      obtain ⟨v, hv, -⟩ := hg
      have := (rec2IwN_trunc hv).1
      omega


/-! ## Part A: the capacity guards, the pins, the stream, the guards -/

theorem word_add_noWrap {x y : Word} (h : ¬ x + y < x) : x.toNat + y.toNat < 2 ^ 64 := by
  have h' : ¬ (x + y).toNat < x.toNat := fun e => h (UInt64.lt_iff_toNat_lt.mpr e)
  rw [UInt64.toNat_add] at h'
  have := y.toNat_lt
  have hx := x.toNat_lt
  omega

theorem grpAW_ok {p : Prog} (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp nested rd mO mL bO bL : Word} {bs : BlockShape}
    {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {block : List IConstantInfo} {r : List Word} {m' : Mem}
    (h : grpAW p n m vis pp nested rd mO mL bO bL = some (r, m'))
    (hS : StageR dn vis fe m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hP : RcMR m) (hA : AbsOK m) (hkeep : ∀ f ∈ grcKeepCallees, AbsKeep p f) :
    ((m.arr64 IW).size + 5 < 2 ^ 64 ∧ bs.nP + bs.k < 2 ^ 64 ∧ bs.nP + rdv.slots.length < 2 ^ 64) ∧
    ∃ cvRis a', (∀ {β : Type} (k : List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block k).run a = (k cvRis).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ KeepW m m' ∧ CsRes m' r cvRis ∧ AbsOK m' := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hp8 := hbs.ptop
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hbsD : decBS (truncM m) pp.toNat = some bs := hbs.1
  obtain ⟨-, hrecs, -, -, -, hlarge, -⟩ := decBS_some hbsD
  unfold grpAW at h
  -- the capacity guards
  by_cases g1 : m.len64 IW + 5 < 5
  · rw [if_pos g1] at h; cases h
  rw [if_neg g1] at h
  by_cases g2 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (pp + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [if_pos g2] at h; cases h
  rw [if_neg g2] at h
  by_cases g3 : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (rd + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [if_pos g3] at h; cases h
  rw [if_neg g3] at h
  have hcap : (m.arr64 IW).size + 5 < 2 ^ 64 ∧ bs.nP + bs.k < 2 ^ 64 ∧ bs.nP + rdv.slots.length < 2 ^ 64 := by
    obtain ⟨e4, hnP64, -, -⟩ := partsShapeWords (IWGrow.refl m) hbs.1 (by omega)
    have hkb : bs.k < 2 ^ 64 := by
      obtain ⟨o', l', -, hl', hg'⟩ := decAt_some (decBS_some hbsD).1
      have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
    have e1 : rdW (m.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := partsShapeK hbs.dec (by omega)
    obtain ⟨-, hslD, -, -, -⟩ := crWords hrd
    have hsl := decPL_length _ (show decPL (truncM m) (decCS (truncM m)) _ _ = some rdv.slots from hslD)
    refine ⟨?_, ?_, ?_⟩
    · have g1' : ¬ (m.len64 IW + 5).toNat < (5 : Word).toNat := fun e => g1 (UInt64.lt_iff_toNat_lt.mpr e)
      rw [UInt64.toNat_add] at g1'
      simp only [Mem.len64] at g1'
      rw [UInt64.toNat_ofNat_of_lt' (by omega)] at g1'
      simp at g1'
      omega
    · have := word_add_noWrap g2
      rw [e4, e1, UInt64.toNat_ofNat_of_lt' hnP64, UInt64.toNat_ofNat_of_lt' hkb] at this
      exact this
    · have := word_add_noWrap g3
      rw [e4, UInt64.toNat_ofNat_of_lt' hnP64, ← hsl] at this
      exact this
  refine ⟨hcap, ?_⟩
  -- `target_rec_pins`
  cases c1 : callW p n "target_rec_pins" [pp, bO, bL] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, grpK1_some] at h
  obtain ⟨s1, hs1, -, hok1, hS1, hg1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetRecPins_refines p P.rp n _ a dn vis fe pp bO bL bs block hS hbs.1 hblk)
    (callW_mono c1 (Nat.le_add_right n 3))
  simp only at hs1 hS1 hg1; subst hs1
  have hrun1 := AM.run_of_ok _ a hok1
  generalize AM.st (ConRon.Arena.targetRecPins bs block) a = a1 at hrun1 hS1
  have hP1 := RcMR.ofClosed hclR (hfR _ (by decide)) c1 hP
  have hA1 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c1 hA
  have hk1 := callW_keepW c1
  -- `class_stream_recs`
  have hrecsP : PSlR decRS bs.recs (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) m :=
    bpPSl decRS_mono hrecs hrb (by rw [UInt64.toNat_add]; simp; omega) (by rw [UInt64.toNat_add]; simp; omega)
  have hw2 : rdW (s1.mem.arr64 IW) (pp + 2) = rdW (m.arr64 IW) (pp + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have hw3 : rdW (s1.mem.arr64 IW) (pp + 3) = rdW (m.arr64 IW) (pp + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [hw2, hw3] at h
  have hrecs1 := hrecsP.grow (fun q => decRS_mono q) hg1
  cases c2 : callW p n "class_stream_recs" [vis, rdW (m.arr64 IW) (pp + 2), rdW (m.arr64 IW) (pp + 3)] s1.mem with
  | none => rw [c2] at h; cases h
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2] at h
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hcs2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classStreamRecs_refines_decB p P.cpy P.ia P.slc P.csr n _ a1 dn fe vis _ _ bs.recs hS1 hrecs1.1 hrecs1.2) c2
  simp only at hs2 hS2 hg2 hcs2; subst hs2
  have hrun2 := AM.run_of_ok _ a1 hok2
  generalize AM.res (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = cvRis at hrun2 hcs2
  generalize AM.st (ConRon.Arena.classStreamRecs V fe bs.recs) a1 = a2 at hrun2 hS2
  have hP2 := RcMR.ofClosed hclR (hfR _ (by decide)) c2 hP1
  have hA2 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c2 hA1
  have hk2 := callW_keepW c2
  have hg12 := hg1.trans hg2
  -- the family guard
  have hk : rdW (s2.mem.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := by
    rw [partsRdIW_grow hg12 (by rw [UInt64.toNat_add]; simp; omega)]
    exact partsShapeK (hbs.dec) (by omega)
  by_cases hk0 : rdW (s2.mem.arr64 IW) (pp + 1) = 0
  · rw [grpK2_fam (h := hk0)] at h; cases h
  have hkb : (bs.k == 0) = false := by
    cases e : bs.k with
    | zero => rw [e] at hk; exact absurd hk hk0
    | succ _ => rfl
  -- the elimination guard
  have hL : (rdW (s2.mem.arr64 IW) (pp + 7) != 0) = bs.large := by
    rw [partsRdIW_grow hg12 (by rw [UInt64.toNat_add]; simp; omega)]
    exact installIwB (k := 7) hlarge hsz
  have hgoal : ∀ (m4 : Mem) (a4 : AState), StageR dn vis fe m4 a4 → IWGrow m m4 → RcMR m4 → KeepW m m4 → AbsOK m4 →
      CsRes m4 r2 cvRis →
      (∀ {β : Type} (k : List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block k).run a = (k cvRis).run a4) →
      some ([r2.headD 0, r2.tail.headD 0], m4) = some (r, m') →
      ∃ cvRis a', (∀ {β : Type} (k : List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block k).run a = (k cvRis).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ KeepW m m' ∧ CsRes m' r cvRis ∧ AbsOK m' := by
    intro m4 a4 hS4 hg4 hP4 hk4 hA4 hcs4 hrun e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨cvRis, a4, hrun, hS4, hg4, hP4, hk4, ?_, hA4⟩
    obtain ⟨ptrs, h1, h2, h3, h4⟩ := hcs4
    exact ⟨ptrs, h1, h2, h3, h4⟩
  by_cases h7 : rdW (s2.mem.arr64 IW) (pp + 7) = 0
  · rw [grpK2_small (h1 := hk0) (h := h7)] at h
    have hl : bs.large = false := by rw [← hL, h7]; rfl
    refine hgoal s2.mem a2 hS2 hg12 hP2 (hk1.trans hk2) hA2 hcs2 (fun k => ?_) h
    simp only [grcTwinA, StateT.run_bind, hrun1, except_ok_bind, hrun2, hkb, hl, Bool.false_eq_true, ite_false]
  have hl : bs.large = true := by rw [← hL]; simpa using h7
  -- the twin's large branch, from `blockLargeElimAllowed`'s run
  have hlarge_run : ∀ (nb : Bool) (a3 a4 : AState) (allowed : Bool),
      nb = ((nested != 0) || ms.any (·.member.isNone)) →
      (ConRon.Arena.blockLargeElimAllowed bs nb).run a3 = .ok (allowed, a4) → allowed = true → a3 = a2 →
      ∀ {β : Type} (k : List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block k).run a = (k cvRis).run a4 := by
    intro nb a3 a4 allowed hnb hr hal ha3 β k
    subst hnb ha3 hal
    simp only [grcTwinA, StateT.run_bind, hrun1, except_ok_bind, hrun2, hkb, hl, hr, Bool.false_eq_true,
      ite_false, ite_true]
  have hmsD : decPL s2.mem (decTM s2.mem) mO.toNat mL.toNat = some ms :=
    (hms.1.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg12).get (OMono.decPL (fun q => decTM_mono q) _ _)
  have hmsb : mO.toNat + mL.toNat < 2 ^ 64 := hS.lt64 hms.2
  by_cases hn : nested = 0
  · rw [grpK2_any (h1 := hk0) (h := h7) (hn := hn)] at h
    cases c3 : callW p n "gen_rec_check_any_no_member" [mO, mL] s2.mem with
    | none => rw [c3] at h; cases h
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [c3, grpK3_some] at h
    obtain ⟨s3, hs3, -, hm3, hany, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (genRecCheckAnyNoMember_refines p P.anm n _ mO mL ms hmsD hmsb hS2.2.2.2.1) c3
    simp only at hs3 hm3 hany; subst hs3
    rw [hm3] at h
    cases c4 : callW p n "block_large_elim_allowed" [pp, r3.headD 0] s2.mem with
    | none => rw [c4] at h; cases h
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [c4] at h
    obtain ⟨s4, hs4, -, hst⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (stubM_spec p "block_large_elim_allowed" n _ [pp, r3.headD 0]) c4
    simp only at hs4 hst; subst hs4
    obtain ⟨al, a4, hr4, hS4, hm4, hd4⟩ := blockLargeElimAllowed_spec dn vis fe pp (r3.headD 0) bs _ _ a2 _ hst
      ⟨hS2, hbs.1.grow (decBS_mono _) hg12⟩
    by_cases h0 : r4.headD 0 = 0
    · rw [grpK4_bad (h := h0)] at h; cases h
    rw [grpK4_ok (h := h0), hm4] at h
    have hal : al = true := by rw [← hd4.1]; simpa using h0
    refine hgoal s2.mem a4 (by rw [← hm4]; exact hS4) hg12 hP2 (hk1.trans hk2) hA2 hcs2
      (hlarge_run _ a2 a4 al (by rw [hany, hn]; rfl) hr4 hal rfl) h
  · rw [grpK2_nested (h1 := hk0) (h := h7) (hn := hn)] at h
    cases c4 : callW p n "block_large_elim_allowed" [pp, nested] s2.mem with
    | none => rw [c4] at h; cases h
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [c4] at h
    obtain ⟨s4, hs4, -, hst⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
      (stubM_spec p "block_large_elim_allowed" n _ [pp, nested]) c4
    simp only at hs4 hst; subst hs4
    obtain ⟨al, a4, hr4, hS4, hm4, hd4⟩ := blockLargeElimAllowed_spec dn vis fe pp nested bs _ _ a2 _ hst
      ⟨hS2, hbs.1.grow (decBS_mono _) hg12⟩
    by_cases h0 : r4.headD 0 = 0
    · rw [grpK4_bad (h := h0)] at h; cases h
    rw [grpK4_ok (h := h0), hm4] at h
    have hal : al = true := by rw [← hd4.1]; simpa using h0
    have hnb : (nested != 0) = ((nested != 0) || ms.any (·.member.isNone)) := by
      have : (nested != 0) = true := by simpa using hn
      rw [this]; rfl
    refine hgoal s2.mem a4 (by rw [← hm4]; exact hS4) hg12 hP2 (hk1.trans hk2) hA2 hcs2
      (hlarge_run _ a2 a4 al hnb hr4 hal rfl) h

-- ==== S41C.lean
/-! ## The generator record -/

/-- **A fresh `ClassGen` record of parts decoded below the tops is decoded below the tops.** -/
theorem cgRec_decB {m : Mem} {g : Word}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : Word}
    (hget : ∀ j (hj : j < 14), (m.arr64 IW)[g.toNat + j]? =
      [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13][j]?)
    (hq : g.toNat + 14 ≤ iwTop m) {nP : Nat} {params : List EIdx} {cls : List TargetMajor}
    {ftc : List EIdx} {slots : List ConRon.Arena.ClassSlot} {ctors : List (List ConRon.Arena.ClassCtor)}
    {elim : LIdx} {pre : List EIdx}
    (h0 : w0.toNat = nP)
    (hpar : DecB (fun m => (decHL m w1.toNat w2.toNat : Option (List EIdx))) m params)
    (hcls : DecB (fun m => decPL m (decTM m) w3.toNat w4.toNat) m cls)
    (hft : DecB (fun m => (decHL m w5.toNat w6.toNat : Option (List EIdx))) m ftc)
    (hsl : DecB (fun m => decPL m (decCS m) w7.toNat w8.toNat) m slots)
    (hct : DecB (fun m => decPL m (decLH m (decPL m (decCC m))) w9.toNat w10.toNat) m ctors)
    (hel : w11.toNat < 2 ^ 32) (hel' : (decI w11 : LIdx) = elim)
    (hpre : DecB (fun m => (decHL m w12.toNat w13.toNat : Option (List EIdx))) m pre) :
    DecB (fun m => decCG m g.toNat) m (⟨nP, params, cls, ftc, slots, ctors, elim, pre⟩ : ConRon.Arena.ClassGen) := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hgw : ∀ j (hj : j < 14), (iwA (truncM m))[g.toNat + j]? =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13][j]'(by simpa using hj)) := by
    intro j hj
    rw [truncM_iw_eq (by omega)]
    simp only [iwA, hget j hj]
    rw [List.getElem?_eq_getElem (by simp; omega)]
  have hw : ∀ j (hj : j < 14), iwN (truncM m) (g.toNat + j) =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13][j]'(by simpa using hj)).toNat := by
    intro j hj; simp only [iwN, nat?, hgw j hj]; rfl
  have h0' := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega)
  have h4 := hw 4 (by omega)
  have h5 := hw 5 (by omega)
  have h6 := hw 6 (by omega)
  have h7 := hw 7 (by omega)
  have h8 := hw 8 (by omega)
  have h9 := hw 9 (by omega)
  have h10 := hw 10 (by omega)
  have h12 := hw 12 (by omega)
  have h13 := hw 13 (by omega)
  have h11 : (iwH (truncM m) (g.toNat + 11) : Option LIdx) = some elim := by
    simp only [iwH, hd?, hgw 11 (by omega)]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    simp [hel, hel']
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13
  have e1 : (decHL (truncM m) w1.toNat w2.toNat : Option (List EIdx)) = some params := hpar
  have e3 : decPL (truncM m) (decTM (truncM m)) w3.toNat w4.toNat = some cls := hcls
  have e5 : (decHL (truncM m) w5.toNat w6.toNat : Option (List EIdx)) = some ftc := hft
  have e7 : decPL (truncM m) (decCS (truncM m)) w7.toNat w8.toNat = some slots := hsl
  have e9 : decPL (truncM m) (decLH (truncM m) (decPL (truncM m) (decCC (truncM m)))) w9.toNat w10.toNat =
    some ctors := hct
  have e12 : (decHL (truncM m) w12.toNat w13.toNat : Option (List EIdx)) = some pre := hpre
  show decCG (truncM m) g.toNat = _
  simp only [decCG, decAt, Nat.add_assoc, Nat.reduceAdd, h0', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, Option.bind_eq_bind, Option.bind_some, e1, e3, e5, e7, e9, e12, h0]
  rfl

-- ==== S41P.lean
/-! ## The prefix, fresh -/

theorem gpbW_simF (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem) (a : AState)
    (g : Word) (G : ClassGen) (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hA : AbsOK m) :
    RSim (gpbW n m g) (ConRon.Arena.ClassGen.prefixBinders G) a
      (fun b a' x => (KP dn vis fe m decIHO b a' x ∧ AbsOK b.2) ∧
        (∀ pre, x = some pre → iwTop m ≤ (b.1.tail.headD 0).toNat)) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [gpbW_eq]
  unfold ConRon.Arena.ClassGen.prefixBinders
  rw [rec2MapM_genBinder]
  have hsz := hS.2.2.2.1
  have hG' : decCG (truncM m) g.toNat = some G := hG
  simp only [decCG, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hG'
  obtain ⟨nP, hnP, ps, hps, cls, hcls, ft, hft, sl, hsl, cts, hcts, el, hel, pre, hpre, hGe⟩ := hG'
  obtain ⟨o1, l1, h1, h2, hpd⟩ := decAt_some hps
  obtain ⟨-, h1m⟩ := rec2IwN_trunc h1
  obtain ⟨-, h2m⟩ := rec2IwN_trunc h2
  obtain ⟨e1, t1⟩ := rec2RdN (w := g) (k := 1) h1m hsz
  obtain ⟨e2, t2⟩ := rec2RdN (w := g) (k := 2) (by simpa [Nat.add_assoc] using h2m) hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at e1 e2
  rw [e1, e2]
  have hpar : decHL m o1 l1 = some G.params := by
    rw [← hGe]; exact (show DecB (fun m => (decHL m o1 l1 : Option (List EIdx))) m ps from hpd).get (OMono.decHL _ _)
  have hpb : 0 < l1 → o1 + l1 ≤ iwTop m := by
    intro hl
    have hpd' : decHL (truncM m) o1 l1 = some ps := hpd
    have hs : (iwA (truncM m)).size ≤ iwTop m := by
      apply Nat.le_of_not_lt
      intro h
      have := truncM_iw_get? m (iwTop m)
      rw [if_neg (Nat.lt_irrefl _), Array.getElem?_eq_getElem h] at this
      cases this
    rcases decHL_le hpd' with h0 | h0
    · omega
    · exact Nat.le_trans h0 hs
  refine RSim.bind (K := gpbK1 n g) rfl (RSim.withF ((ftdsF_ok dn vis fe _ _ G.params).sim
      ⟨hS, by rw [t1, t2]; exact hpar, by rw [t1, t2]; exact hpb⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r1, m1⟩ pbs a1 - ⟨⟨hS1, hg1, hpbs, hpbb⟩, hf1⟩
  dsimp only at hS1 hg1 hpbs hpbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hpbs hpbb
  rw [gpbK1_some]
  have hps := psW_sim dn vis fe G g hns n m1 a1 0 0 hS1 (hG.grow (decCG_mono _) hg1) (by simp) (by simp)
    (hf1 hA)
  simp only [UInt64.toNat_zero, List.drop_zero] at hps
  refine RSim.bind (K := gpbK2 n (r1.headD 0) (r1.tail.headD 0)) rfl hps ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho, hA2⟩
  dsimp only at hS2 hg2 ho
  cases o with
  | none =>
    rw [gpbK2_fail (h := ho)]
    exact RSim.pure_some ⟨⟨⟨hS2, hg1.trans hg2, rfl⟩, hA2⟩, fun _ h => by cases h⟩
  | some sbs =>
  obtain ⟨h21, hsb, hsbb⟩ := ho
  rw [gpbK2_ok (h := by rw [h21]; decide)]
  refine RSim.lstep (K := gpbK3) rfl fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hd3, hb3⟩ := rec2AppendW_dec h3 hS2 ((decHL_decB hpbs hpbb).grow (OMono.decHL _ _) hg2) hsb hsbb
  obtain ⟨hr3, -⟩ := appendW_dec h3 hS2.2.2.2.1 hS2.2.2.2.2.2 (Nat.le_trans hpbb hg2.1) hsbb
    ((decHL_decB hpbs hpbb).get (OMono.decHL _ _) |> fun h => by rw [decHL_grow hg2 hpbb]; exact h) hsb
  rw [gpbK3_some]
  refine RSim.pure_some ⟨⟨⟨hS3, hg1.trans (hg2.trans hg3), rfl, by simpa using hd3, by simpa using hb3⟩,
    appendW_afr h3 hA2⟩, fun _ _ => ?_⟩
  rw [hr3]
  simp only [List.tail_cons, List.headD_cons]
  exact Nat.le_trans (hg1.trans hg2).1 (Nat.le_refl _)


/-! ## The record's stores, as one write -/

theorem grpGs_eq (m1 : Mem) (g pp pO pL m2o m2l fo fl rd co cl el : Word) (hrd : rd.toNat + 1 < g.toNat)
    (hg : g.toNat + 14 < 2 ^ 64) :
    grpG3 (grpG2b (grpG2 (grpG1 m1 g pp pO pL m2o m2l) g fo fl rd) g rd co) g cl el =
      wrIW m1 g [rdW (m1.arr64 IW) (pp + 4), pO, pL, m2o, m2l, fo, fl, rdW (m1.arr64 IW) rd,
        rdW (m1.arr64 IW) (rd + 1), co, cl, el, 0, 0] := by
  have hr1 : (rd + 1).toNat = rd.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  simp only [grpG1, grpG2, grpG2b, grpG3]
  simp (disch := (first | omega | (simp only [UInt64.toNat_add, hr1]; simp; omega))) only [rdW_set_ne]
  simp only [wrIW, UInt64.add_assoc, UInt64.reduceAdd]

-- ==== S41E.lean
/-! ## Small tools -/

theorem decHL_set_out {k : IdxKind} {m : Mem} {x v : Word} {o l : Nat} (h : o + l ≤ x.toNat ∨ x.toNat < o) :
    (decHL (m.set64 IW x v) o l : Option (List (Idx k))) = decHL m o l := by
  simp only [decHL, hslice?]
  apply mapM_opt_congr
  intro j hj
  have : j < l := List.mem_range.mp hj
  simp only [hd?, iwA]
  rw [set64IW_get, if_neg (by omega)]

-- ==== S41F.lean
/-! ## Part C: the generator record, its prefix, the recursor types -/

theorem decCC_lh_mono : ∀ q, OMono (fun m => decLH m (decPL m (decCC m)) q) :=
  fun q => OMono.decAt (fun o l => OMono.decPL decCC_mono o l) q

theorem grpCW_ok {p : Prog} (P : GrcProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp pO pL rd cRo cRl m2o m2l fo fl co cl el : Word}
    {bs : BlockShape} {params : List EIdx} {rdv : ConRon.Arena.ClassRead} {ms2 : List TargetMajor}
    {ctors : List (List ConRon.Arena.ClassCtor)} {ftc : List EIdx} {elim : LIdx} {cvRis : List IConstantVal}
    {r : List Word} {m' : Mem}
    (h : grpCW p n m vis pp pO pL rd cRo cRl m2o m2l fo fl co cl el = some (r, m'))
    (hS : StageR dn vis fe m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (hrd : DecB (fun m => decCR m rd.toNat) m rdv) (hms2 : PSlR decTM ms2 m2o m2l m)
    (hct : DecB (fun m => decPL m (decLH m (decPL m (decCC m))) co.toNat cl.toNat) m ctors)
    (hft : decHL m fo.toNat fl.toNat = some ftc) (hftb : fo.toNat + fl.toNat ≤ iwTop m)
    (hel : el.toNat < 2 ^ 32) (hel' : (decI el : LIdx) = elim)
    (hcv : DecB (fun m => decPL m (decCVp m) cRo.toNat cRl.toNat) m cvRis)
    (hns : bs.nP + rdv.slots.length < 2 ^ 64) (hA : AbsOK m) :
    ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        (grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k).run a = (k G cvGs).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ DecB (fun m => decCG m (r.headD 0).toNat) m' G ∧
      G.nP + G.slots.length < 2 ^ 64 ∧ G.slots = rdv.slots ∧ decCVS m' r.tail cvGs ∧ AbsOK m' := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hc : 200 < (m.arr64 CTL).size := hS.2.2.2.2.2
  have hp8 := hbs.ptop
  obtain ⟨hrd3, hslD, hrcD, hrcb, -⟩ := crWords hrd
  unfold grpCW at h
  -- `iw_alloc(14)`
  cases c1 : callW p n "iw_alloc" [14] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, grpC1_some] at h
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p P.ia n _ 14) c1
  simp only at hs1 hal; subst hs1
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  obtain ⟨hS1, -, hqtop, -⟩ := allocW_stage hal hS
  generalize hgq : r1.headD 0 = g at h hq hqtop hroom
  have h14 : (14 : Word).toNat = 14 := rfl
  rw [h14] at hroom
  unfold grpC2W grpC2bW grpC3W at h
  rw [grpGs_eq s1.mem g pp pO pL m2o m2l fo fl rd co cl el (by omega) (by omega)] at h
  have e4 : rdW (s1.mem.arr64 IW) (pp + 4) = UInt64.ofNat bs.nP := by
    rw [hm1, allocMem_IW]; exact (partsShapeWords (IWGrow.refl m) hbs.1 (by omega)).1
  have er0 : rdW (s1.mem.arr64 IW) rd = rdW (m.arr64 IW) rd := by rw [hm1, allocMem_IW]
  have er1 : rdW (s1.mem.arr64 IW) (rd + 1) = rdW (m.arr64 IW) (rd + 1) := by rw [hm1, allocMem_IW]
  rw [e4, er0, er1] at h
  generalize hws : [UInt64.ofNat bs.nP, pO, pL, m2o, m2l, fo, fl, rdW (m.arr64 IW) rd,
    rdW (m.arr64 IW) (rd + 1), co, cl, el, (0 : Word), 0] = ws at h
  have hS1G : StageR dn vis fe (wrIW s1.mem g ws) a := StageR.wrIW hS1 g ws
  have hwl : ws.length = 14 := by rw [← hws]; rfl
  obtain ⟨hget, hgG, hfG, htopG⟩ := recMem_post m ws 14 (by rw [hwl]; rfl) hc (by rw [hwl, ← hq]; omega) hsz
  rw [← hm1, ← hq] at hget hgG htopG hfG
  have hAG := AFr.iw hfG hA
  have hgt : g.toNat = iwTop m := hqtop
  have htG : iwTop (wrIW s1.mem g ws) = iwTop m + 14 := by
    simp only [iwTop]; rw [htopG, UInt64.toNat_add, h14, Nat.mod_eq_of_lt (by omega)]
    simp only [iwTop] at hgt; omega
  -- the generator record, decoded
  have hnP : bs.nP < 2 ^ 64 := (partsShapeWords (IWGrow.refl m) hbs.1 (by omega)).2.1
  have hparD := decHL_decB hpar hparb
  have hftD := decHL_decB hft hftb
  have hrecsP : PSlR decRS bs.recs (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) m := by
    obtain ⟨-, hrecs, -, -, -, -, -⟩ := decBS_some (show decBS (truncM m) pp.toNat = some bs from hbs.1)
    exact bpPSl decRS_mono hrecs hrb (by rw [UInt64.toNat_add]; simp; omega) (by rw [UInt64.toNat_add]; simp; omega)
  have hcomp : ∀ m'', IWGrow m m'' →
      DecB (fun x => (decHL x pO.toNat pL.toNat : Option (List EIdx))) m'' params ∧
      DecB (fun x => decPL x (decTM x) m2o.toNat m2l.toNat) m'' ms2 ∧
      DecB (fun x => (decHL x fo.toNat fl.toNat : Option (List EIdx))) m'' ftc ∧
      DecB (fun x => decPL x (decCS x) (rdW (m.arr64 IW) rd).toNat (rdW (m.arr64 IW) (rd + 1)).toNat) m'' rdv.slots ∧
      DecB (fun x => decPL x (decLH x (decPL x (decCC x))) co.toNat cl.toNat) m'' ctors := by
    intro m'' hg
    exact ⟨hparD.grow (OMono.decHL _ _) hg, hms2.1.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg,
      hftD.grow (OMono.decHL _ _) hg, hslD.grow (OMono.decPL decCS_mono _ _) hg,
      hct.grow (OMono.decPL decCC_lh_mono _ _) hg⟩
  generalize hmG : wrIW s1.mem g ws = mG at hS1G hget hgG htopG htG h hAG
  obtain ⟨cP, cM, cF, cS, cC⟩ := hcomp mG hgG
  have hsl1 : rd.toNat + 1 < iwTop m := by omega
  have hG0 : DecB (fun x => decCG x g.toNat) mG
      (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, []⟩ : ConRon.Arena.ClassGen) := by
    subst hws
    exact cgRec_decB (fun j hj => hget j (by simpa using hj)) (by omega) (UInt64.toNat_ofNat_of_lt' hnP) cP cM cF
      cS cC hel hel' (by show decHL (truncM mG) (0 : Word).toNat (0 : Word).toNat = some []; simp [decHL, hslice?])
  -- the prefix
  unfold grpDW at h
  cases c2 : callW p n "class_gen_prefix_binders" [g] mG with
  | none => rw [c2] at h; cases h
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2] at h
  obtain ⟨s2, hs2, -, hgp⟩ := triple_of_callW (s₀ := ⟨mG, Locals.init []⟩) (prefixBinders_spec p P.pb n _ g) c2
  simp only at hs2 hgp; subst hs2
  obtain ⟨x2, a2, hrun2, ⟨⟨hS2, hg2, hd2⟩, hA2⟩, hfr2⟩ :=
    gpbW_simF dn vis fe n mG a g _ hS1G hG0 hns hAG (r2, s2.mem) hgp
  dsimp only at hS2 hg2 hd2 hfr2 hA2
  have hk2 := callW_keepW c2
  by_cases h0 : r2.headD 0 = 0
  · rw [grpC3_bad (h := h0)] at h; cases h
  rw [grpC3_ok (h := h0)] at h
  cases x2 with
  | none => exact absurd hd2 h0
  | some pre =>
  obtain ⟨-, hpreD, hpreb⟩ := hd2
  have hfr := hfr2 pre rfl
  generalize ho : r2.tail.headD 0 = o at h hpreD hpreb hfr
  generalize hl : r2.tail.tail.headD 0 = l at h hpreD hpreb
  have hgs : g.toNat + 14 ≤ (s2.mem.arr64 IW).size := by
    rw [hk2 IW, ← hmG, wrIW_size, hm1, allocMem_IW]; omega
  have e12 : (g + 12).toNat = g.toNat + 12 := by rw [UInt64.toNat_add]; simp; omega
  have e13 : (g + 13).toNat = g.toNat + 13 := by rw [UInt64.toNat_add]; simp; omega
  have hgP : IWGrow m (grpPMem s2.mem g o l) :=
    ((hgG.trans hg2).set_iw _ _ (by rw [e12]; omega)).set_iw _ _ (by rw [e13]; omega)
  have hSP : StageR dn vis fe (grpPMem s2.mem g o l) a2 := (hS2.set_iw _ _).set_iw _ _
  have hAP : AbsOK (grpPMem s2.mem g o l) :=
    AFr.set64 _ IW (by decide) (by decide) _ _ (AFr.set64 _ IW (by decide) (by decide) _ _ hA2)
  have htP : iwTop (grpPMem s2.mem g o l) = iwTop s2.mem := by simp only [grpPMem, iwTop_set_iw]
  have hgetP : ∀ j (hj : j < 14), ((grpPMem s2.mem g o l).arr64 IW)[g.toNat + j]? =
      [UInt64.ofNat bs.nP, pO, pL, m2o, m2l, fo, fl, rdW (m.arr64 IW) rd, rdW (m.arr64 IW) (rd + 1), co, cl, el,
        o, l][j]? := by
    intro j hj
    simp only [grpPMem]
    rw [set64IW_get, set64IW_get]
    by_cases j13 : j = 13
    · subst j13; rw [if_pos ⟨e13.symm, by rw [size_set64]; omega⟩]; rfl
    rw [if_neg (by omega)]
    by_cases j12 : j = 12
    · subst j12; rw [if_pos ⟨e12.symm, by omega⟩]; rfl
    rw [if_neg (by omega), hg2.2.2.1 _ (by omega), hget j (by rw [hwl]; omega), ← hws]
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega
  have hpreP : DecB (fun x => (decHL x o.toNat l.toNat : Option (List EIdx))) (grpPMem s2.mem g o l) pre := by
    refine decHL_decB ?_ (by rw [htP]; exact hpreb)
    simp only [grpPMem]
    rw [decHL_set_out (by rw [e13]; omega), decHL_set_out (by rw [e12]; omega)]
    exact hpreD
  obtain ⟨dP, dM, dF, dS, dC⟩ := hcomp _ hgP
  have hG : DecB (fun x => decCG x g.toNat) (grpPMem s2.mem g o l)
      (⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩ : ConRon.Arena.ClassGen) :=
    cgRec_decB hgetP (by rw [htP]; have := hg2.1; rw [htG] at this; omega) (UInt64.toNat_ofNat_of_lt' hnP) dP dM dF dS dC hel hel'
      hpreP
  -- `class_rec_tys_ok`
  have rP : ∀ k, k < 9 → rdW ((grpPMem s2.mem g o l).arr64 IW) (pp + UInt64.ofNat k) =
      rdW (m.arr64 IW) (pp + UInt64.ofNat k) := fun k hk =>
    partsRdIW_grow hgP (by rw [UInt64.toNat_add]; simp; omega)
  have rR : ∀ k, k < 4 → rdW ((grpPMem s2.mem g o l).arr64 IW) (rd + UInt64.ofNat k) =
      rdW (m.arr64 IW) (rd + UInt64.ofNat k) := fun k hk =>
    partsRdIW_grow hgP (by rw [UInt64.toNat_add]; simp; omega)
  rw [show (pp + 1 : Word) = pp + UInt64.ofNat 1 from rfl, show (pp + 2 : Word) = pp + UInt64.ofNat 2 from rfl,
    show (pp + 3 : Word) = pp + UInt64.ofNat 3 from rfl, show (rd + 2 : Word) = rd + UInt64.ofNat 2 from rfl,
    show (rd + 3 : Word) = rd + UInt64.ofNat 3 from rfl, rP 1 (by omega), rP 2 (by omega), rP 3 (by omega),
    rR 2 (by omega), rR 3 (by omega)] at h
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o', l', -, hl', hg'⟩ := decAt_some (decBS_some (show decBS (truncM m) pp.toNat = some bs from hbs.1)).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  have hkw : rdW (m.arr64 IW) (pp + UInt64.ofNat 1) = UInt64.ofNat bs.k := partsShapeK hbs.dec (by omega)
  rw [hkw] at h
  have hrcs := hrecsP.1.grow (OMono.decPL decRS_mono _ _) hgP
  cases c3 : callW p n "class_rec_tys_ok" [vis, g, UInt64.ofNat bs.k, rdW (m.arr64 IW) (pp + UInt64.ofNat 2),
      rdW (m.arr64 IW) (pp + UInt64.ofNat 3), cRo, cRl, rdW (m.arr64 IW) (rd + UInt64.ofNat 2),
      rdW (m.arr64 IW) (rd + UInt64.ofNat 3)] (grpPMem s2.mem g o l) with
  | none => rw [c3] at h; cases h
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, grpC4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s3, hs3, -, hok3, ⟨hS3, hg3, hd3⟩, hA3⟩ := triple_of_callW (s₀ := ⟨grpPMem s2.mem g o l, Locals.init []⟩)
    (classRecTysOk_refines p P.rts n _ a2 dn vis fe g (UInt64.ofNat bs.k) _ _ cRo cRl _ _ _ bs.recs cvRis rdv.recCls
      hSP hG hns hrcs (rec3RecsOK_of_decB hrcs (Nat.le_trans hrecsP.2 hgP.1)) (hcv.grow (OMono.decPL
        (fun q => OMono.decCVp q) _ _) hgP) (hrcD.grow (OMono.decNL _ _) hgP) hAP) c3
  simp only at hs3 hS3 hg3 hd3 hA3; subst hs3
  have hrun3 := AM.run_of_ok _ a2 hok3
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hrun3 hS3 hd3
  refine ⟨⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩,
    AM.res (ConRon.Arena.classRecTysOk V fe ⟨bs.nP, params, ms2, ftc, rdv.slots, ctors, elim, pre⟩ bs.k bs.recs
      cvRis rdv.recCls) a2, _, fun {β} k => ?_, hS3, hgP.trans hg3, hG.grow (decCG_mono _) hg3, hns, rfl, ?_, hA3⟩
  · simp only [grcTwinC, StateT.run_bind, hrun2, except_ok_bind, hrun3]
  · simpa [decCVS] using hd3

-- ==== S41G.lean
/-! ## Part B: the classes, their constructors, the count, the formers, the level -/

theorem ClassesLp.grow {m m' : Mem} {mo ml : Word} {ms : List TargetMajor} (h : ClassesLp m mo ml)
    (hms : PSlR decTM ms mo ml m) (hg : IWGrow m m') (hk : KeepW m m') (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ClassesLp m' mo ml := by
  intro c hc v o l hv ho hl
  have hms0 : decPL (truncM m) (decTM (truncM m)) mo.toNat ml.toNat = some ms := hms.1
  obtain ⟨v', hv', hsrc⟩ := decPL_getH (truncM m) hms0 c hc
  obtain ⟨hvt, hvm⟩ := rec2IwN_trunc hv'
  rw [iwN_grow hg hvt, hvm] at hv
  have e := Option.some.inj hv
  subst e
  have hs := hsrc
  simp only [decTM, bind, Option.bind_eq_some_iff, pure] at hs
  obtain ⟨_, -, _, -, _, -, _, -, _, -, cts, hct, -⟩ := hs
  obtain ⟨o', l', ho'', hl'', hdct⟩ := decAt_some hct
  obtain ⟨h6t, h6⟩ := rec2IwN_trunc ho''
  obtain ⟨h7t, h7⟩ := rec2IwN_trunc hl''
  rw [iwN_grow hg h6t, h6] at ho
  rw [show v' + 6 + 1 = v' + 7 by omega] at h7t h7
  rw [iwN_grow hg h7t, h7] at hl
  have e1 := Option.some.inj ho
  have e2 := Option.some.inj hl
  subst e1 e2
  have hol : o' < 2 ^ 64 ∧ l' < 2 ^ 64 := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at h6 h7
    obtain ⟨w1, -, rfl⟩ := h6; obtain ⟨w2, -, rfl⟩ := h7
    exact ⟨w1.toNat_lt, w2.toNat_lt⟩
  refine (h c hc v' o' l' hvm h6 h7).grow (cAs := cts) ?_ hsz hg hk
  show decPL (truncM m) (decCN (truncM m)) _ _ = some cts
  rw [UInt64.toNat_ofNat_of_lt' hol.1, UInt64.toNat_ofNat_of_lt' hol.2]
  exact hdct

/-- A handle word of a record decoded below the tops, read at its word address. -/
theorem installIwH {k : IdxKind} {m : Mem} {w : Word} {i : Nat} {x : Idx k}
    (h : iwH (truncM m) (w.toNat + i) = some x) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (rdW (m.arr64 IW) (w + UInt64.ofNat i)).toNat < 2 ^ 32 ∧ decI (rdW (m.arr64 IW) (w + UInt64.ofNat i)) = x := by
  simp only [iwH, hd?, bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, hx⟩ := h
  obtain ⟨hi, hv'⟩ := truncM_iw_get hv
  simp only [iwA] at hv'
  have hlt : w.toNat + i < (m.arr64 IW).size := (Array.getElem?_eq_some_iff.mp hv').1
  have he : (w + UInt64.ofNat i).toNat = w.toNat + i := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)]; exact Nat.mod_eq_of_lt (by omega)
  have hr : rdW (m.arr64 IW) (w + UInt64.ofNat i) = v := by simp only [rdW, he, hv']; rfl
  rw [hr]
  split at hx
  · exact ⟨by assumption, Option.some.inj hx⟩
  · cases hx

theorem grpBW_ok {p : Prog} (P : GrcProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp pO pL tO tL rd mO mL cO cL cRo cRl : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {cvRis : List IConstantVal}
    {r : List Word} {m' : Mem}
    (h : grpBW p n m vis pp pO pL tO tL rd mO mL cO cL cRo cRl = some (r, m'))
    (hS : StageR dn vis fe m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp cvTas cO cL m) (hlp : ClassesLp m mO mL)
    (hcvR : DecB (fun m => decPL m (decCVp m) cRo.toNat cRl.toNat) m cvRis)
    (hns : bs.nP + rdv.slots.length < 2 ^ 64) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ grcKeepCallees, AbsKeep p f) :
    ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        (grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
          grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k)).run a = (k G cvGs).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ DecB (fun m => decCG m (r.headD 0).toNat) m' G ∧
      G.nP + G.slots.length < 2 ^ 64 ∧ G.slots = rdv.slots ∧ decCVS m' r.tail cvGs ∧ AbsOK m' := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hp8 := hbs.ptop
  obtain ⟨hrd3, hslD, -, -, hslb⟩ := crWords hrd
  unfold grpBW at h
  -- the formers' types
  cases c1 : callW p n "gen_rec_check_former_tys" [cO, cL] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, grpB1_some] at h
  obtain ⟨s1, hs1, -, hS1, hg1, hf1, hft1, hftb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (genRecCheckFormerTys_refines P.ia P.gft n _ a cO cL cvTas hS hcv) c1
  simp only at hs1 hS1 hg1 hf1 hft1 hftb1; subst hs1
  have hP1 := hP.fr hf1
  have hk1 := callW_keepW c1
  have hA1 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c1 hA
  -- `classes_nfs`
  cases c2 : callW p n "classes_nfs" [vis, pp, r1.headD 0, r1.tail.headD 0, tO, tL, mO, mL] s1.mem with
  | none => rw [c2] at h; cases h
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, grpB2_some] at h
  obtain ⟨s2, hs2, -, hok2, hms2, hS2, hg2, hP2, hlp2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classesNfs_refinesLp P.cns n _ a dn fe vis pp _ _ tO tL mO mL bs (cvTas.map (·.type)) tbl ms hS1
      (hbs.grow hg1) hft1 hftb1 (htbl.grow (fun q => decNCN_mono q) hg1) (hms.grow (fun q => decTM_mono q) hg1) hP1
      (hlp.grow hms hg1 hk1 hsz)) c2
  simp only at hs2 hms2 hS2 hg2 hP2 hlp2; subst hs2
  have hk2 := callW_keepW c2
  have hA2 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c2 hA1
  have hrun2 := AM.run_of_ok _ a hok2
  generalize AM.res (ConRon.Arena.classesNfs V fe bs (cvTas.map (·.type)) tbl ms) a = ms2 at hrun2 hms2
  generalize AM.st (ConRon.Arena.classesNfs V fe bs (cvTas.map (·.type)) tbl ms) a = a2 at hrun2 hS2
  have hg12 := hg1.trans hg2
  -- `classes_ctors`
  have hsz2 : (s2.mem.arr64 IW).size = (m.arr64 IW).size := by rw [hk2 IW, hk1 IW]
  cases c3 : callW p n "classes_ctors" [vis, pp, r1.headD 0, r1.tail.headD 0, rd, r2.headD 0, r2.tail.headD 0]
      s2.mem with
  | none => rw [c3] at h; cases h
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, grpB3_some] at h
  obtain ⟨s3, hs3, -, hok3, hS3, hg3, hsp3, -⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (classesCtors_refines P.ccs n _ a2 dn fe vis pp _ _ rd _ _ bs (cvTas.map (·.type)) rdv ms2 hS2
      (hbs.grow hg12) (by rw [decHL_grow3 hg2 hftb1]; exact hft1) (Nat.le_trans hftb1 hg2.1)
      (hrd.grow (decCR_mono _) hg12) hms2.1 (hS2.lt64 hms2.2) (hlp2 hk2) hnpk (by rw [hsz2]; exact hsz5) hP2) c3
  simp only at hs3 hS3 hg3 hsp3; subst hs3
  have hrun3 := AM.run_of_ok _ a2 hok3
  generalize AM.res (ConRon.Arena.classesCtors V fe bs (cvTas.map (·.type)) rdv ms2 0 ms2) a2 = ctors at hrun3 hsp3
  generalize AM.st (ConRon.Arena.classesCtors V fe bs (cvTas.map (·.type)) rdv ms2 0 ms2) a2 = a3 at hrun3 hS3
  have hg13 := hg12.trans hg3
  have hA3 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c3 hA2
  have hctD := spl_decB hsp3.toSPL
  -- the count
  have er0 : rdW (s3.mem.arr64 IW) rd = rdW (m.arr64 IW) rd := partsRdIW_grow hg13 (by omega)
  have er1 : rdW (s3.mem.arr64 IW) (rd + 1) = rdW (m.arr64 IW) (rd + 1) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  rw [er0, er1] at h
  cases c4 : callW p n "gen_rec_check_minor_ok" [rdW (m.arr64 IW) rd, rdW (m.arr64 IW) (rd + 1), r3.headD 0,
      r3.tail.headD 0] s3.mem with
  | none => rw [c4] at h; cases h
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4] at h
  obtain ⟨s4, hs4, -, hm4, hmo⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (genRecCheckMinorOk_refines P.csm P.gmo n _ _ _ _ _ rdv.slots ctors
      ((hslD.grow (OMono.decPL decCS_mono _ _) hg13).get (OMono.decPL decCS_mono _ _)) hslb
      (hctD.get (OMono.decPL decCC_lh_mono _ _)) (hS3.lt64 hsp3.2.1) hS3.2.2.2.1) c4
  simp only at hs4 hm4 hmo; subst hs4
  by_cases h0 : r4.headD 0 = 0
  · rw [grpB4_bad (h := h0)] at h; cases h
  rw [grpB4_ok (h := h0), hm4] at h
  have hcount : ((rdv.slots.filter ConRon.Arena.ClassSlot.isMinor).length == (ctors.map List.length).sum) = true := by
    rw [← hmo]; simpa using h0
  -- the classes' formers
  cases c5 : callW p n "gen_rec_check_former_tys_c" [vis, cO, cL, r2.headD 0, r2.tail.headD 0] s3.mem with
  | none => rw [c5] at h; cases h
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, grpB5_some] at h
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hftc5, hftcb5⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (genRecCheckFormerTysC_refines P.cft P.gftc n _ a3 dn vis fe cO cL _ _ cvTas ms2 hS3
      (hcv.grow (fun q => OMono.decCVp q) hg13) (hms2.grow (fun q => decTM_mono q) hg3)) c5
  simp only at hs5 hS5 hg5 hftc5 hftcb5; subst hs5
  have hrun5 := AM.run_of_ok _ a3 hok5
  generalize AM.res (ms2.mapM (ConRon.Arena.classFormerTy fe cvTas)) a3 = ftc at hrun5 hftc5
  generalize AM.st (ms2.mapM (ConRon.Arena.classFormerTy fe cvTas)) a3 = a5 at hrun5 hS5
  have hg15 := hg13.trans hg5
  have hA5 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c5 (by rw [hm4] at c4; exact hA3)
  -- the elimination level
  have hbsD : decBS (truncM m) pp.toNat = some bs := hbs.1
  obtain ⟨-, -, -, helim, -, hlarge, -⟩ := decBS_some hbsD
  obtain ⟨hel5, hel5'⟩ := installIwH (i := 5) helim hsz
  have hL := installIwB (k := 7) hlarge hsz
  have ew5 : rdW (s5.mem.arr64 IW) (pp + 5) = rdW (m.arr64 IW) (pp + UInt64.ofNat 5) :=
    partsRdIW_grow hg15 (by rw [UInt64.toNat_add]; simp; omega)
  have ew7 : rdW (s5.mem.arr64 IW) (pp + 7) = rdW (m.arr64 IW) (pp + UInt64.ofNat 7) :=
    partsRdIW_grow hg15 (by rw [UInt64.toNat_add]; simp; omega)
  rw [ew5, ew7] at h
  cases c6 : callW p n "struct_elim_level" [rdW (m.arr64 IW) (pp + UInt64.ofNat 5),
      rdW (m.arr64 IW) (pp + UInt64.ofNat 7)] s5.mem with
  | none => rw [c6] at h; cases h
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, grpB6_some] at h
  obtain ⟨s6, hs6, -, a6, hrun6, hS6, hg6, hel6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (structElimLevel_stage P.sel n _ a5 _ _ hS5 hel5) c6
  simp only at hs6 hrun6 hS6 hg6 hel6; subst hs6
  rw [hel5', hL] at hrun6
  have hg16 := hg15.trans hg6
  have hA6 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c6 hA5
  -- part C
  obtain ⟨G, cvGs, a', hrunC, hS', hg', hG', hns', hsl', hcg', hA'⟩ := grpCW_ok P n h hS6 (hbs.grow hg16)
    (hrb.grow hg16 (by omega)) (decHL_grow' hg16 hparb hpar) (Nat.le_trans hparb hg16.1)
    (hrd.grow (decCR_mono _) hg16) (hms2.grow (fun q => decTM_mono q) (hg3.trans (hg5.trans hg6)))
    (hctD.grow (OMono.decPL decCC_lh_mono _ _) (hg5.trans hg6))
    (decHL_grow' hg6 hftcb5 hftc5) (Nat.le_trans hftcb5 hg6.1) hel6 rfl
    (hcvR.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg16) hns hA6
  refine ⟨G, cvGs, a', fun {β} k => ?_, hS', hg16.trans hg', hG', hns', hsl', hcg', hA'⟩
  rw [← hrunC k]
  simp only [grcTwinB, StateT.run_bind, hrun2, except_ok_bind, hrun3, hcount, hrun5, hrun6, ite_true]

-- ==== S41H.lean
/-! ## The whole prep -/

/-- `class_stream_recs`' result, decoded below the tops. -/
theorem csRes_decB {m : Mem} {r : List Word} {cvs : List IConstantVal} (h : CsRes m r cvs) :
    DecB (fun x => decPL x (decCVp x) (r.headD 0).toNat (r.tail.headD 0).toNat) m cvs := by
  obtain ⟨ptrs, hp, hd, hx, hb⟩ := h
  show decPL (truncM m) (decCVp (truncM m)) _ _ = some cvs
  rw [decPL_eq_bind, show decNL (truncM m) (r.headD 0).toNat (r.tail.headD 0).toNat = some ptrs from
    decNL_decB hp hb]
  rw [decPL_eq_bind, hp] at hd
  simp only [Option.bind_eq_bind, Option.bind_some] at hd
  have : ∀ (qs : List Nat) (xs : List IConstantVal), qs.mapM (decCVp m) = some xs → (∀ q ∈ qs, CVExt m q) →
      qs.mapM (decCVp (truncM m)) = some xs := by
    intro qs
    induction qs with
    | nil => intro xs h _; simpa using h
    | cons q qs ih =>
      intro xs h hq
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx1, ys, hys, rfl⟩ := h
      have e : decCVp (truncM m) q = some x := installCvDecB hx1 (hq q (by simp))
      simp only [List.mapM_cons, e, ih ys hys (fun q' hq' => hq q' (by simp [hq'])), Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
  exact this ptrs cvs hd hx

theorem decPL_trunc_len {α : Type} {m : Mem} {f : Nat → Option α} {o l : Nat} {xs : List α}
    (h : decPL (truncM m) f o l = some xs) : xs.length ≤ iwTop m := by
  rw [decPL_length _ h]
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · omega
  · have hg := mapM_opt_get (fun j => do f (← iwN (truncM m) (o + j))) (List.range l) xs h (l - 1)
      (by simp; omega)
    simp only [List.getElem_range, Option.bind_eq_bind, Option.bind_eq_some_iff] at hg
    obtain ⟨v, hv, -⟩ := hg
    have := (rec2IwN_trunc hv).1
    omega

/-- **`gen_rec_check_prep`'s model refines the twin's `genRecCheck` up to the checked recursor
types.** -/
theorem grpW_ok {p : Prog} (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {block : List IConstantInfo} {r : List Word} {m' : Mem}
    (h : grpW p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL = some (r, m'))
    (hS : StageR dn vis fe m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp cvTas cO cL m)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hlp : ClassesLp m mO mL)
    (hP : RcMR m) (hA : AbsOK m) (hkeep : ∀ f ∈ grcKeepCallees, AbsKeep p f) :
    ∃ G cvGs a', (∀ {β : Type} (k : ConRon.Arena.ClassGen → List IConstantVal → AM β),
        (grcTwinA V fe bs (nested != 0) ms block (fun cvRis =>
          grcTwinB V fe bs tbl rdv ms cvTas (fun ms2 ctors ftc elim =>
            grcTwinC V fe bs params rdv cvRis ms2 ctors ftc elim k))).run a = (k G cvGs).run a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ DecB (fun m => decCG m (r.headD 0).toNat) m' G ∧
      G.nP + G.slots.length < 2 ^ 64 ∧ G.slots = rdv.slots ∧ decCVS m' r.tail cvGs ∧ AbsOK m' := by
  have hT : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  unfold grpW at h
  cases cA : grpAW p n m vis pp nested rd mO mL bO bL with
  | none => rw [cA] at h; cases h
  | some qA =>
  obtain ⟨rA, mA⟩ := qA
  rw [cA, grpKA_some] at h
  obtain ⟨⟨hsz5, hnpk, hns⟩, cvRis, aA, hrunA, hSA, hgA, hPA, hkA, hcsA, hAA⟩ :=
    grpAW_ok P hclR hfR n cA hS hbs hrb hrd hms hblk hP hA hkeep
  have hszA : (mA.arr64 IW).size = (m.arr64 IW).size := hkA IW
  obtain ⟨G, cvGs, a', hrunB, hS', hg', hG', hns', hsl', hcg', hA'⟩ := grpBW_ok P n h hSA (hbs.grow hgA)
    (hrb.grow hgA (by have := hbs.ptop; omega)) (decHL_grow' hgA hparb hpar) (Nat.le_trans hparb hgA.1)
    (htbl.grow (fun q => decNCN_mono q) hgA) (hrd.grow (decCR_mono _) hgA) (hms.grow (fun q => decTM_mono q) hgA)
    (hcv.grow (fun q => OMono.decCVp q) hgA) (hlp.grow hms hgA hkA hS.2.2.2.1) (csRes_decB hcsA) hns hnpk
    (by rw [hszA]; exact hsz5) hPA hAA hkeep
  exact ⟨G, cvGs, a', fun {β} k => by rw [hrunA]; exact hrunB k, hS', hgA.trans hg', hG', hns', hsl', hcg', hA'⟩

-- ==== S41a2.lean
/-! ## `gen_rec_check`'s model -/

section model
variable (p : Prog) (n : Nat)

/-- After the second flush: `(fe2, out.off, out.len)`. -/
def gckK6 (v oo ol : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([v, oo, ol], m)

/-- After the pop: the flush. -/
def gckK5 (oo ol : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => gckK6 (r.headD 0) oo ol (callW p n "flush_caches" [] m)

/-- After `class_recs_rules_ok`: the pop. -/
def gckK4 (fR po pl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => gckK5 p n (r.headD 0) (r.tail.headD 0)
      (callW p n "gen_rec_check_pop_all" [fR, po, pl] m)

/-- After the flush: `class_recs_rules_ok`. -/
def gckK3 (vis rd g cgo cgl fR po pl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => gckK4 p n fR po pl (callW p n "class_recs_rules_ok"
      [vis, fR, g, rdW (m.arr64 IW) (rd + 2), rdW (m.arr64 IW) (rd + 3), cgo, cgl] m)

/-- After `class_fe_r`: the flush. -/
def gckK2 (vis rd g cgo cgl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => gckK3 p n vis rd g cgo cgl (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0)
      (callW p n "flush_caches" [] m)

/-- After the prep: `class_fe_r`. -/
def gckK1 (vis pp rd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => gckK2 p n vis rd (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0)
      (callW p n "class_fe_r" [pp, r.tail.headD 0, r.tail.tail.headD 0, rdW (m.arr64 IW) (rd + 2),
        rdW (m.arr64 IW) (rd + 3), vis] m)

/-- **The model of `gen_rec_check`** (body fuel `n`). -/
def gckW (m : Mem) (vis pp nested pO pL tO tL rd mO mL cO cL bO bL : Word) : Option (List Word × Mem) :=
  gckK1 p n vis pp rd (callW p n "gen_rec_check_prep" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL,
    bO, bL] m)

end model

section arms
variable (p : Prog) (n : Nat) (m : Mem) (r : List Word) (vis pp rd g cgo cgl fR po pl v oo ol : Word)
theorem gckK6_some : gckK6 v oo ol (some (r, m)) = some ([v, oo, ol], m) := rfl
theorem gckK5_some : gckK5 p n oo ol (some (r, m)) = gckK6 (r.headD 0) oo ol (callW p n "flush_caches" [] m) := rfl
theorem gckK4_some : gckK4 p n fR po pl (some (r, m)) = gckK5 p n (r.headD 0) (r.tail.headD 0)
    (callW p n "gen_rec_check_pop_all" [fR, po, pl] m) := rfl
theorem gckK3_some : gckK3 p n vis rd g cgo cgl fR po pl (some (r, m)) = gckK4 p n fR po pl
    (callW p n "class_recs_rules_ok" [vis, fR, g, rdW (m.arr64 IW) (rd + 2), rdW (m.arr64 IW) (rd + 3), cgo, cgl] m) :=
  rfl
theorem gckK2_some : gckK2 p n vis rd g cgo cgl (some (r, m)) = gckK3 p n vis rd g cgo cgl (r.headD 0)
    (r.tail.headD 0) (r.tail.tail.headD 0) (callW p n "flush_caches" [] m) := rfl
theorem gckK1_some : gckK1 p n vis pp rd (some (r, m)) = gckK2 p n vis rd (r.headD 0) (r.tail.headD 0)
    (r.tail.tail.headD 0) (callW p n "class_fe_r" [pp, r.tail.headD 0, r.tail.tail.headD 0,
      rdW (m.arr64 IW) (rd + 2), rdW (m.arr64 IW) (rd + 3), vis] m) := rfl
end arms

attribute [ind_grind] gckK6_some gckK5_some gckK4_some gckK3_some gckK2_some gckK1_some

set_option maxHeartbeats 1600000 in
theorem gck_spec (p : Prog) (hp : p.lookup "gen_rec_check" = some genRecCheckL) (n : Nat)
    (s₀ : St) (vis pp nested pO pL tO tL rd mO mL cO cL bO bL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "gen_rec_check"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧
      gckW p n s₀.mem vis pp nested pO pL tO tL rd mO mL cO cL bO bL = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, genRecCheckL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "gen_rec_check_prep", callW_spec p n "class_fe_r", callW_spec p n "flush_caches",
      callW_spec p n "class_recs_rules_ok", callW_spec p n "gen_rec_check_pop_all"] <;>
    finish (gen := 40) (instances := 20000) [gckW, rdW_eq]

-- ==== S41I.lean
/-! ## `gen_rec_check` -/

theorem decRRS.grow {m m' : Mem} {r : List Word} {xs : List (IConstantVal × TargetMajor × List EIdx)}
    (h : decRRS m r xs) (hg : IWGrow m m') : decRRS m' r xs :=
  ⟨h.1.grow (OMono.decPL decRR_mono _ _) hg, Nat.le_trans h.2 hg.1⟩

/-- **`gen_rec_check`'s model refines `genRecCheck`.** -/
theorem gckW_sim {p : Prog} (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word}
    {bs : BlockShape} {params : List EIdx} {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead}
    {ms : List TargetMajor} {cvTas : List IConstantVal} {block : List IConstantInfo}
    (hS : StageR dn vis fe m a) (hbs : BSOK m pp.toNat bs) (hrb : RecsB m pp)
    (hpar : decHL m pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop m)
    (htbl : PSlR decNCN tbl tO tL m) (hrd : DecB (fun m => decCR m rd.toNat) m rdv)
    (hms : PSlR decTM ms mO mL m) (hcv : PSlR decCVp cvTas cO cL m)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hlp : ClassesLp m mO mL)
    (hP : RcMR m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ grcKeepCallees, AbsKeep p f) :
    Sim (gckW p n m vis pp nested pO pL tO tL rd mO mL cO cL bO bL)
      (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block) a
      (fun r x m' a' => StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow m m' ∧ decRRS m' r.tail x.2 ∧ AbsOK m') := by
  intro r m' h
  unfold gckW at h
  obtain ⟨hrd3, -, hrcD, hrcb, -⟩ := crWords hrd
  -- the prep
  cases c1 : callW p n "gen_rec_check_prep" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, gckK1_some] at h
  cases n with
  | zero => rw [callW_zero] at c1; cases c1
  | succ n =>
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (grp_spec p P.prep n _ vis pp nested pO pL tO tL rd mO mL cO cL bO bL) c1
  simp only at hs1 hw1; subst hs1
  obtain ⟨G, cvGs, a1, hrunP, hS1, hg1, hG1, hns1, -, hcg1, hA1⟩ := grpW_ok P hclR hfR n hw1 hS hbs hrb hpar
    hparb htbl hrd hms hcv hblk hlp hP hA hkeep
  have e2 : rdW (s1.mem.arr64 IW) (rd + 2) = rdW (m.arr64 IW) (rd + 2) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  have e3 : rdW (s1.mem.arr64 IW) (rd + 3) = rdW (m.arr64 IW) (rd + 3) :=
    partsRdIW_grow hg1 (by rw [UInt64.toNat_add]; simp; omega)
  rw [e2, e3] at h
  -- the pushes
  cases c2 : callW p (n + 1) "class_fe_r" [pp, r1.tail.headD 0, r1.tail.tail.headD 0,
      rdW (m.arr64 IW) (rd + 2), rdW (m.arr64 IW) (rd + 3), vis] s1.mem with
  | none => rw [c2] at h; cases h
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, gckK2_some] at h
  obtain ⟨s2, hs2, -, hS2, hg2, hpv2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classFeR_refines p P.cfr (n + 1) _ a1 dn vis fe pp _ _ _ _ bs cvGs rdv.recCls hS1 (hbs.1.grow (decBS_mono _) hg1)
      hcg1 (hrcD.grow (OMono.decNL _ _) hg1)) c2
  simp only at hs2 hS2 hg2 hpv2; subst hs2
  have hA2 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c2 hA1
  generalize hfrr : ConRon.Arena.classFeR bs cvGs rdv.recCls fe = FR at hS2 hpv2
  obtain ⟨feR, prevs⟩ := FR
  simp only at hS2 hpv2
  -- the flush
  cases c3 : callW p (n + 1) "flush_caches" [] s2.mem with
  | none => rw [c3] at h; cases h
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, gckK3_some] at h
  obtain ⟨s3, hs3, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (flushCaches_spec p P.flush (n + 1) _) c3
  simp only at hs3 hfok hfm; subst hs3
  obtain ⟨hS3, hg3⟩ := flush_stage hS2 hfok
  rw [← hfm] at hS3 hg3
  have hg23 := hg2.trans hg3
  have hA3 : AbsOK s3.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2
  have hg13 := hg1.trans hg23
  -- the rules
  have e2' : rdW (s3.mem.arr64 IW) (rd + 2) = rdW (m.arr64 IW) (rd + 2) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  have e3' : rdW (s3.mem.arr64 IW) (rd + 3) = rdW (m.arr64 IW) (rd + 3) :=
    partsRdIW_grow hg13 (by rw [UInt64.toNat_add]; simp; omega)
  rw [e2', e3'] at h
  have hcg3 := hcg1.grow hg23
  cases c4 : callW p (n + 1) "class_recs_rules_ok" [vis, r2.headD 0, r1.headD 0, rdW (m.arr64 IW) (rd + 2),
      rdW (m.arr64 IW) (rd + 3), r1.tail.headD 0, r1.tail.tail.headD 0] s3.mem with
  | none => rw [c4] at h; cases h
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, gckK4_some] at h
  obtain ⟨s4, hs4, -, hok4, ⟨hS4, hg4, hd4⟩, hA4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (classRecsRulesOk_refines p P.crr (n + 1) _ _ dn vis (r2.headD 0) feR (r1.headD 0) _ _ _ _ G rdv.recCls cvGs
      hS3 (hG1.grow (decCG_mono _) hg23) hns1 (hrcD.grow (OMono.decNL _ _) hg13) hrcb hcg3
      (hS3.lt64 hcg3.1) hA3) c4
  simp only at hs4 hS4 hg4 hd4; subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  generalize AM.res (ConRon.Arena.classRecsRulesOk V vis.toNat feR G rdv.recCls cvGs cvGs rdv.recCls)
    { a1 with caches := Caches.empty } = out at hrun4 hd4
  generalize AM.st (ConRon.Arena.classRecsRulesOk V vis.toNat feR G rdv.recCls cvGs cvGs rdv.recCls)
    { a1 with caches := Caches.empty } = a4 at hrun4 hS4
  -- the pops
  cases c5 : callW p (n + 1) "gen_rec_check_pop_all" [r2.headD 0, r2.tail.headD 0, r2.tail.tail.headD 0]
      s4.mem with
  | none => rw [c5] at h; cases h
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, gckK5_some] at h
  obtain ⟨s5, hs5, -, hS5, hg5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (genRecCheckPopAll_refines P.eix P.ers P.ept P.gpa (n + 1) _ a4 dn (r2.headD 0) feR _ _ prevs hS4
      (hpv2.grow (hg3.trans hg4))) c5
  simp only at hs5 hS5 hg5; subst hs5
  have hA5 := hkeep _ (by simp [grcKeepCallees]) _ _ _ _ _ c5 hA4
  -- the flush
  cases c6 : callW p (n + 1) "flush_caches" [] s5.mem with
  | none => rw [c6] at h; cases h
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, gckK6_some] at h
  obtain ⟨s6, hs6, -, hfok6, hfm6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (flushCaches_spec p P.flush (n + 1) _) c6
  simp only at hs6 hfok6 hfm6; subst hs6
  obtain ⟨hS6, hg6⟩ := flush_stage hS5 hfok6
  have hA6 : AbsOK s6.mem := by rw [hfm6]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA5
  rw [← hfm6] at hS6 hg6
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨(prevs.foldr (fun x acc => acc.popTemp x.1 x.2) feR, out), { a4 with caches := Caches.empty }, ?_,
    by simpa using hS6, hg1.trans (hg23.trans (hg4.trans (hg5.trans hg6))),
    by have := hd4.grow (hg5.trans hg6); simp only [decRRS] at this ⊢; simpa using this, hA6⟩
  have hvis : fe.visibleBelow = vis.toNat := hS.1.env.vis
  rw [genRecCheck_split, hrunP]
  simp only [grcTwinR, hfrr, StateT.run_bind, flushCaches_run, except_ok_bind, hvis, hrun4]
  rfl

-- ==== S41J.lean
/-- **`gen_rec_check(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
cvTas.off, cvTas.len, block.off, block.len)` refines `genRecCheck`**: from the stage relation, the
block's shape (`BSOK`, its recursor shapes' slice below the top: `RecsB`), the parameters, the
positivity table, the class reading, the classes (their constructors' level-parameter slices in
`EREC`: `ClassesLp`), the formers and the raw block decoded below the tops, and the recursor check's
and `abstract1`'s memos well formed (`RcMR`, `AbsOK`): the
environment with the generated recursors at the returned view, the recursors' records `r.tail`
decoded below the tops. Program facts: the lookups (`GrcProg`) and the write set of the callees
that keep the walk memos by their text (`hclR`), those that keep `abstract1`'s (`AbsKeep`). The word
bounds come from `gen_rec_check_prep`'s capacity guards. Through `block_large_elim_allowed`'s contract
(`IndInstallSpec39`). -/
@[refines ConRon.Arena.genRecCheck]
theorem genRecCheck_refines {p : Prog} (P : GrcProg p) {fsR : List FnName}
    (hclR : closedA p rcFreeA rcFreeC fsR = true) (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR) (n : Nat) (s₀ : St)
    (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {pp nested pO pL tO tL rd mO mL cO cL bO bL : Word} {bs : BlockShape} {params : List EIdx}
    {tbl : List NestCtorNf} {rdv : ConRon.Arena.ClassRead} {ms : List TargetMajor}
    {cvTas : List IConstantVal} {block : List IConstantInfo}
    (hS : StageR dn vis fe s₀.mem a₀) (hbs : BSOK s₀.mem pp.toNat bs) (hrb : RecsB s₀.mem pp)
    (hpar : decHL s₀.mem pO.toNat pL.toNat = some params) (hparb : pO.toNat + pL.toNat ≤ iwTop s₀.mem)
    (htbl : PSlR decNCN tbl tO tL s₀.mem) (hrd : DecB (fun m => decCR m rd.toNat) s₀.mem rdv)
    (hms : PSlR decTM ms mO mL s₀.mem) (hcv : PSlR decCVp cvTas cO cL s₀.mem)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block) (hlp : ClassesLp s₀.mem mO mL)
    (hP : RcMR s₀.mem) (hA : AbsOK s₀.mem)
    (hkeep : ∀ f ∈ grcKeepCallees, AbsKeep p f) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas block) a₀ ∧
      StageR dn (r.headD 0) (AM.res (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas
        block) a₀).1 s'.mem (AM.st (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas
        block) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decRRS s'.mem r.tail (AM.res (ConRon.Arena.genRecCheck V fe bs (nested != 0) params tbl rdv ms cvTas
        block) a₀).2 ∧ AbsOK s'.mem; ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
  refine triple_post (gck_spec p P.grc n s₀ vis pp nested pO pL tO tL rd mO mL cO cL bO bL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hQ⟩ := Sim.run (gckW_sim P hclR hfR n hS hbs hrb hpar hparb htbl hrd hms hcv hblk hlp hP hA hkeep) hm
  exact ⟨hl, hok, hQ⟩

/-! ## `check_block_rec` -/

/-- **`check_block_rec` refines `checkBlockRec`** (through `genRecCheck_refines`). -/
@[refines ConRon.Arena.checkBlockRec]
theorem checkBlockRec_refines (p : Prog) (hp : p.lookup "check_block_rec" = some checkBlockRec)
    (P : GrcProg p) {fsR : List FnName} (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ grcMemoCallees, f ∈ fsR)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (pp nested pO pL tO tL rd mO mL bO bL cO cL : Word) (bs : BlockShape) (params : List EIdx)
    (tbl : List NestCtorNf) (rdv : ClassRead) (ms : List TargetMajor) (cvTas : List IConstantVal)
    (block : List IConstantInfo) (hS : StageR dn vis fe s₀.mem a₀)
    (hpre : BSOK s₀.mem pp.toNat bs ∧
        decHL s₀.mem pO.toNat pL.toNat = some params ∧ pO.toNat + pL.toNat ≤ iwTop s₀.mem ∧
        PSlR decNCN tbl tO tL s₀.mem ∧ DecB (fun m => decCR m rd.toNat) s₀.mem rdv ∧
        PSlR decTM ms mO mL s₀.mem ∧ PSlR decCVp cvTas cO cL s₀.mem ∧
        DecB (fun m => decEBlk dn m bO.toNat bL.toNat) s₀.mem block)
    (hrb : RecsB s₀.mem pp) (hlp : ClassesLp s₀.mem mO mL) (hP : RcMR s₀.mem) (hA : AbsOK s₀.mem)
    (hkeep : ∀ f ∈ grcKeepCallees, AbsKeep p f) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_rec"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, bO, bL, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀ ∧
      StageR dn (r.headD 0)
        (AM.res (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀).1
        s'.mem (AM.st (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decRRS s'.mem r.tail
        (AM.res (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀).2 ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (icr_spec p hp n s₀ vis pp nested pO pL tO tL rd mO mL bO bL cO cL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hbs, hpar, hparb, htbl, hrd, hms, hcv, hblk⟩ := hpre
  have hsim : Sim (icrW p n s₀.mem vis pp nested pO pL tO tL rd mO mL bO bL cO cL)
      (ConRon.Arena.checkBlockRec V fe ⟨bs⟩ (nested != 0) params tbl rdv ms block cvTas) a₀
      (fun r x m' a' => StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow s₀.mem m' ∧ decRRS m' r.tail x.2 ∧
        AbsOK m') := by
    unfold icrW ConRon.Arena.checkBlockRec
    refine Sim.post (K := icrK) rfl (fun _ _ => rfl)
      (installSimCall (Q := fun r x m' a' => StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow s₀.mem m' ∧
        decRRS m' r.tail x.2 ∧ AbsOK m') (genRecCheck_refines P hclR hfR n ⟨s₀.mem, Locals.init []⟩ a₀ hS hbs hrb hpar hparb htbl
        hrd hms hcv hblk hlp hP hA hkeep) (fun r s' h => by obtain ⟨-, hok, hQ⟩ := h; exact ⟨hok, hQ⟩)) ?_
    rintro r x m a ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by simp only [decRRS] at h3 ⊢; simpa using h3, h4⟩
  obtain ⟨hok, hQ⟩ := Sim.run hsim hm
  exact ⟨hl, hok, hQ⟩

end L.Ind
