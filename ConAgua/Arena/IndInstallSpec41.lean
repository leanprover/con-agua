import ConAgua.Arena.IndInstallSpec40
import ConAgua.Arena.IndInstallSpec30
import ConAgua.Arena.IndRealBle
import ConAgua.Arena.IndInstallSpec39
import ConAgua.Arena.RecCheckSpec22
import ConAgua.Arena.RecGenSpec27
import ConAgua.Arena.RecGenSpec28

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

/-! ## Memo frames from the program text -/

/-- Every word array below 320 (both tiers) but the recursor check's walk memos. -/
def rcFreeA : List ArrId := (List.range 388).filter (fun b => b ∉ [NOM, DPM, RAM, HBM, RFM, TAM])
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
  ble : BleProg p
  opf : OpfF p

/-- The callees of `gen_rec_check_prep` that keep the recursor check's walk memos by their program
text. -/
def grcMemoCallees : List FnName := ["target_rec_pins", "class_stream_recs"]

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

-- ==== S41C.lean
/-! ## The generator record -/

/-- **A fresh `ClassGen` record of parts decoded below the tops is decoded below the tops.** -/
theorem cgRec_decB {m : Mem} {g : Word}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : Word}
    (hget : ∀ j (_hj : j < 14), (m.arr64 IW)[g.toNat + j]? =
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
  have hgw : ∀ j (_hj : j < 14), (iwA (truncM m))[g.toNat + j]? =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13][j]'(by simpa using _hj)) := by
    intro j _hj
    rw [truncM_iw_eq (by omega)]
    simp only [iwA, hget j _hj]
    rw [List.getElem?_eq_getElem (by simp; omega)]
  have hw : ∀ j (_hj : j < 14), iwN (truncM m) (g.toNat + j) =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13][j]'(by simpa using _hj)).toNat := by
    intro j _hj; simp only [iwN, nat?, hgw j _hj]; rfl
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
  rcases n with _ | n
  · exact RSim.none
  rw [gpbW.arm1]
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
      rw [ite_eq_right (Nat.lt_irrefl _), Array.getElem?_eq_getElem h] at this
      cases this
    rcases decHL_le hpd' with h0 | h0
    · omega
    · exact Nat.le_trans h0 hs
  refine RSim.bind (K := gpbW.k_fvar_type_ds n g) rfl (RSim.withF ((ftdsF_ok dn vis fe _ _ G.params).sim
      ⟨hS, by rw [t1, t2]; exact hpar, by rw [t1, t2]; exact hpb⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r1, m1⟩ pbs a1 - ⟨⟨hS1, hg1, hpbs, hpbb⟩, hf1⟩
  dsimp only at hS1 hg1 hpbs hpbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hpbs hpbb
  rw [gpbW.k_fvar_type_ds.arm1]
  have hps := psW_sim dn vis fe G g hns n m1 a1 0 0 hS1 (hG.grow (decCG_mono _) hg1) (by simp) (by simp)
    (hf1 hA)
  simp only [UInt64.toNat_zero, List.drop_zero] at hps
  refine RSim.bind (K := gpbW.k_class_gen_prefix_binders_slots_go n (r1.headD 0) (r1.tail.headD 0)) rfl hps ?_
  rintro ⟨r2, m2⟩ o a2 - ⟨hS2, hg2, ho, hA2⟩
  dsimp only at hS2 hg2 ho
  cases o with
  | none =>
    rw [gpbW.k_class_gen_prefix_binders_slots_go.arm1 (hc1 := ho)]
    exact RSim.pure_some ⟨⟨⟨hS2, hg1.trans hg2, rfl⟩, hA2⟩, fun _ h => by cases h⟩
  | some sbs =>
  obtain ⟨h21, hsb, hsbb⟩ := ho
  rw [gpbW.k_class_gen_prefix_binders_slots_go.arm2 (hc1 := by rw [h21]; decide)]
  refine RSim.lstep (K := gpbW.k_sl_append) rfl fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hd3, hb3⟩ := rec2AppendW_dec h3 hS2 ((decHL_decB hpbs hpbb).grow (OMono.decHL _ _) hg2) hsb hsbb
  obtain ⟨hr3, -⟩ := appendW_dec h3 hS2.2.2.2.1 hS2.2.2.2.2.2 (Nat.le_trans hpbb hg2.1) hsbb
    ((decHL_decB hpbs hpbb).get (OMono.decHL _ _) |> fun h => by rw [decHL_grow hg2 hpbb]; exact h) hsb
  rw [gpbW.k_sl_append.arm1]
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
  rw [set64IW_get, ite_eq_right (by omega)]

-- ==== S41F.lean
/-! ## Part C: the generator record, its prefix, the recursor types -/

theorem decCC_lh_mono : ∀ q, OMono (fun m => decLH m (decPL m (decCC m)) q) :=
  fun q => OMono.decAt (fun o l => OMono.decPL decCC_mono o l) q

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
  simp only [Option.bind_some] at hd
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

-- ==== S41J.lean

/-! ## `check_block_rec` -/

end L.Ind
