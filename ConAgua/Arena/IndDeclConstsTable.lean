module

public import ConAgua.Arena.IndDeclConstsBlock
public import ConAgua.Arena.IndSumSpec.StructProjBodies
import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndDeclConsts
import ConAgua.Arena.IndPartsSpec.RulePrefixAt

@[expose] public section

/-!
# A declaration's tables (lane `ronsync2`, stage 3)

`block_table(p, ms)` refines one member of con-ron's `blockTables` (`Arena/Install.lean`): a
structure-like member's constructor (`MemberShape.structCtor?`), its projection bodies
(`struct_proj_bodies`, `spbW_ok`), the block's level parameters (`block_shape_lps`, `lpsW_dec`)
and the bodies copied into `EREC` (`er_from_iw`, `efF_stage`), the 13-word table record
(`erec_alloc`, `erec_put`s: `btMem_eq`, `erRec_stage`). `block_tables(p, mo, ml)` refines
`blockTables p ms`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `block_table(s)`. -/
structure TablesProg (p : Prog) : Prop extends BlockProg p where
  tErCopy : p.lookup "er_copy" = some L.Ind.erCopy
  tErToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  sView : p.lookup "e_view" = some eView
  sDerB : p.lookup "der_b" = some derB
  sBvarFind : p.lookup "bvar_find" = some bvarFind
  sBvarPush : p.lookup "bvar_push" = some bvarPush
  sInternBVar : p.lookup "intern_bvar" = some internBVar
  sProjFind : p.lookup "proj_find" = some projFind
  sProjPush : p.lookup "proj_push" = some projPush
  sInternProj : p.lookup "intern_proj" = some internProj
  sMkProj : p.lookup "mk_proj" = some mkProj
  sArgP : p.lookup "struct_proj_arg_p" = some structProjArgPL
  sGo : p.lookup "struct_proj_bodies_go" = some structProjBodiesGoL
  sPsAtGo : p.lookup "struct_ps_at_go" = some structPsAtGoL
  sPsAt : p.lookup "struct_ps_at" = some structPsAtL
  sProjPs : p.lookup "struct_proj_ps" = some structProjPsL
  spb : p.lookup "struct_proj_bodies" = some structProjBodiesL
  i1l : I1lF p
  sn : p.lookup "sl_snoc" = some slSnoc
  st : StripProg p
  bt : p.lookup "block_table" = some blockTable
  bts : p.lookup "block_tables" = some blockTables

/-! ## The twin, one member at a time -/

/-- One member's table (`blockTables`' step): `some none` at a member that is not structure-like,
`some (some t)` its table, `none` where its constructor's type is too short for the bodies. -/
def tblOne (bs : BlockShape) (ms : MemberShape) : AM (Option (Option IProjTable)) :=
  match ms.structCtor? with
  | some c => do
    match ← structProjBodies ms.declared.name bs.nP c.2 c.1.type with
    | some bodies => pure (some (some ⟨ms.declared.name, bs.lps, bs.nP, c.1.name, c.2, bodies⟩))
    | none => pure none
  | none => pure (some none)

/-- The rest of `blockTables` after one member's step. -/
def tblRest (bs : BlockShape) (rest : List MemberShape) : Option (Option IProjTable) →
    AM (Option (List IProjTable))
  | none => pure none
  | some o => do
    let ts ← ConRon.Arena.blockTables bs rest
    pure (ts.map (o.toList ++ ·))

theorem blockTables_cons (bs : BlockShape) (ms : MemberShape) (rest : List MemberShape) :
    ConRon.Arena.blockTables bs (ms :: rest) = (tblOne bs ms >>= tblRest bs rest) := by
  cases h : ms.structCtor? with
  | none => simp [ConRon.Arena.blockTables, tblOne, tblRest, h]
  | some c =>
    simp only [ConRon.Arena.blockTables, tblOne, h, bind_assoc]
    congr 1; funext x
    cases x <;> simp [tblRest]

/-! ## `block_table`: the model -/

/-- The memory after the table record's thirteen `erec_put`s (each argument read at its time). -/
def btMem (m1 : Mem) (q pp c cv T elo ell ebo ebl : Word) : Mem :=
  let m6 := erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m1 q 6) (q + 1) 0) (q + 2) T)
    (q + 3) elo) (q + 4) ell
  let m7 := erecPutMem m6 (q + 5) (rdW (m6.arr64 IW) (pp + 4))
  let m8 := erecPutMem m7 (q + 6) (erRd m7 cv)
  let m9 := erecPutMem m8 (q + 7) (rdW (m8.arr64 IW) (c + 1))
  erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m9 (q + 8) 0) (q + 9) ebo) (q + 10) ebl)
    (q + 11) 0) (q + 12) 0

/-- **The model of `block_table(p, ms)`** at exec fuel `n`. -/
l_model dbt_spec {p : Prog} (hP : TablesProg p)
  fns [hP.bt ↦ dbtW list]
  specs [spbW_spec p hP.alloc hP.iwCopy hP.slCons hP.sView hP.sDerB hP.sBvarFind hP.sBvarPush hP.sInternBVar
      hP.sProjFind hP.sProjPush hP.sInternProj hP.sMkProj hP.sArgP hP.sn hP.sGo hP.sPsAtGo hP.sPsAt hP.sProjPs
      hP.spb hP.i1l hP.st n,
    blockShapeLps_spec p hP.alloc hP.tErCopy hP.tErToIw hP.lps n, efF_spec p hP.cbr.tsr hP.erPut n,
    erecAlloc_specW p hP.erAlloc n, erecPut_specM p hP.erPut n]
  grind [arena_grind]

/-! ## `block_table`: the record -/

theorem btMem_eq {m1 : Mem} {q pp c cv T elo ell ebo ebl : Word} (hfr : ErApart q 13 cv) :
    btMem m1 q pp c cv T elo ell ebo ebl = wrER m1 q [6, 0, T, elo, ell, rdW (m1.arr64 IW) (pp + 4),
      erRd m1 cv, rdW (m1.arr64 IW) (c + 1), 0, ebo, ebl, 0, 0] := by
  have f : ∀ j < 6, erTier cv ≠ erTier (q + UInt64.ofNat j) ∨ erOff cv ≠ erOff (q + UInt64.ofNat j) :=
    fun j hj => hfr j (by omega)
  have f0 : erTier cv ≠ erTier q ∨ erOff cv ≠ erOff q := by simpa using f 0 (by decide)
  have f1 := f 1 (by decide)
  have f2 := f 2 (by decide)
  have f3 := f 3 (by decide)
  have f4 := f 4 (by decide)
  have f5 := f 5 (by decide)
  simp only [show (UInt64.ofNat 1 : Word) = 1 from rfl, show (UInt64.ofNat 2 : Word) = 2 from rfl,
    show (UInt64.ofNat 3 : Word) = 3 from rfl, show (UInt64.ofNat 4 : Word) = 4 from rfl,
    show (UInt64.ofNat 5 : Word) = 5 from rfl] at f1 f2 f3 f4 f5
  simp only [btMem, wrER, erecPutMem_iw]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl,
    show q + 9 + 1 = q + 10 by ac_rfl, show q + 10 + 1 = q + 11 by ac_rfl,
    show q + 11 + 1 = q + 12 by ac_rfl]
  rw [erRd_erecPutMem_ne f5, erRd_erecPutMem_ne f4, erRd_erecPutMem_ne f3, erRd_erecPutMem_ne f2,
    erRd_erecPutMem_ne f1, erRd_erecPutMem_ne f0]

/-- One member's table result: `(0, _)` no table, `(1, q)` the table record at `q`, `(2, _)` the
twin's `none`. -/
def DcTblR (m : Mem) (r : List Word) : Option (Option IProjTable) → Prop
  | none => r.headD 0 = 2
  | some none => r.headD 0 = 0
  | some (some t) => r.headD 0 = 1 ∧ decTbl (erecP m) (r.tail.headD 0).toNat = some t

theorem structCtor?_none {ms : MemberShape} (h : ms.ctors.length ≠ 1 ∨ ms.nIdx ≠ 0) :
    ms.structCtor? = none := by
  unfold MemberShape.structCtor?
  split
  · rename_i c hc
    rw [hc] at h
    simp at h
    simp [h]
  · rfl

theorem efF_afr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : efF n m o l = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [efF] at h
  | succ n => exact efW_afr h

/-- **`block_table` refines one member of `blockTables`** (`tblOne`). -/
theorem btW_ok {vis : Word} {fe : IFEnv} {n : Nat} {m m' : Mem}
    {a : AState} {pp ms : Word} {bs : BlockShape} {mS : MemberShape} {r : List Word}
    (hS : StageR vis fe m a) (hA : AbsOK m) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hms : DecB (fun m => decMS m ms.toNat) m mS) (hnP : 1 + bs.nP < 2 ^ 64)
    (h : dbtW n m pp ms = some (r, m')) :
    ∃ x a', (tblOne bs mS).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
      DcTblR m' r x := by
  rcases n with _ | n
  · simp [dbtW] at h
  have hms0 : decMS (truncM m) ms.toNat = some mS := hms
  obtain ⟨-, ⟨da, hda, hdecl⟩, hnI, hct⟩ := decMS_some hms0
  obtain ⟨co, cl, hco, hcl, hcs⟩ := decAt_some hct
  have hlen := decPL_length (truncM m) hcs
  obtain ⟨hclW, -⟩ := iwRd (o := ms) (w := 3) (by simpa using hcl)
  obtain ⟨hnIW, -⟩ := iwRd (o := ms) (w := 1) (by simpa using hnI)
  -- the declines
  by_cases h3 : rdW (m.arr64 IW) (ms + 3) ≠ 1
  · rw [dbtW.arm1 (hc1 := h3)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : mS.structCtor? = none := structCtor?_none (.inl (by
      rw [hlen, ← hclW]; intro e; exact h3 (UInt64.toNat_inj.mp (by simpa using e))))
    exact ⟨some none, a, by simp [tblOne, this]; rfl, hS, IWGrow.refl m, hA, rfl⟩
  by_cases h1 : rdW (m.arr64 IW) (ms + 1) ≠ 0
  · rw [dbtW.arm2 (hc1 := Decidable.of_not_not h3) (hc2 := h1)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : mS.structCtor? = none := structCtor?_none (.inr (by
      rw [← hnIW]; intro e; exact h1 (UInt64.toNat_inj.mp (by simpa using e))))
    exact ⟨some none, a, by simp [tblOne, this]; rfl, hS, IWGrow.refl m, hA, rfl⟩
  rw [dbtW.arm3 (hc1 := Decidable.of_not_not h3) (hc2 := Decidable.of_not_not h1)] at h
  simp only [erRd_foldN] at h
  have hcl1 : cl = 1 := by rw [← hclW]; simp at h3; rw [h3]; rfl
  have hnI0 : mS.nIdx = 0 := by rw [← hnIW]; simp at h1; rw [h1]; rfl
  -- the constructor
  obtain ⟨v, y, hv, hy, hget⟩ := decPL_get cl co mS.ctors hcs 0 (by omega)
  have hctors : mS.ctors = [y] := by
    cases hc : mS.ctors with
    | nil => rw [hc] at hlen; simp at hlen; omega
    | cons y0 ys =>
      rw [hc] at hlen hget
      simp at hget
      subst hget
      have : ys = [] := List.eq_nil_of_length_eq_zero (by simp at hlen; omega)
      rw [this]
  have hsc : mS.structCtor? = some y := by simp [MemberShape.structCtor?, hctors, hnI0]
  simp only [decCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hy
  obtain ⟨cva, hcva, cv0, hcv0, nF, hnF, rfl⟩ := hy
  obtain ⟨hcoW, -⟩ := iwRd (o := ms) (w := 2) (by simpa using hco)
  obtain ⟨cw, hcw, hcwv, hcwlt⟩ := rdW_of_iwN_truncM (o := rdW (m.arr64 IW) (ms + 2))
    (by rw [hcoW]; simpa using hv)
  obtain ⟨cvw, hcvw, hcvwv, -⟩ := rdW_of_iwN_truncM (o := cw) (by rw [hcwv]; exact hcva)
  obtain ⟨hnFW, -⟩ := iwRd (o := cw) (w := 1) (by rw [hcwv]; simpa using hnF)
  obtain ⟨daw, hdaw, hdawv, -⟩ := rdW_of_iwN_truncM (o := ms + 4)
    (by have e : (ms + 4).toNat = ms.toNat + 4 := by
          have := (iwRd (o := ms) (w := 4) (by simpa using hda)).2
          have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
          rw [UInt64.toNat_add]; simp at this ⊢; omega
        rw [e]; exact hda)
  rw [hcw, hcvw, hdaw] at h
  -- the declared name and the constructor's type
  have hdecl' := decCVp_truncM (by rw [← hdawv] at hdecl; exact hdecl)
  obtain ⟨w0, hw0, hw0lt, hname⟩ := decCV_name hdecl'
  have hT : erRd m daw = w0 := (erRd_of_erecP hw0).1
  have hcv0' := decCVp_truncM (by rw [← hcvwv] at hcv0; exact hcv0)
  have hcv0c := hcv0'
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hcv0c
  obtain ⟨nm, hnm, lps0, -, ty, hty, hcvE⟩ := hcv0c
  obtain ⟨w3, hw3, hw3lt, hty'⟩ := hd?_some hty
  have hty0 : cv0.type = decI w3 := by rw [← Option.some.inj hcvE]; exact hty'
  have hnm0 : cv0.name = nm := by rw [← Option.some.inj hcvE]
  obtain ⟨wn, hwn, hwnlt, hnm'⟩ := hd?_some hnm
  obtain ⟨r3e, -⟩ := erRd_add (cq := cvw) (j := 3) (m := m) hw3 (by decide)
  rw [show (UInt64.ofNat 3 : Word) = 3 from rfl] at r3e
  rw [hT, r3e] at h
  -- the parameters' word
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨-, -, hnPi, -, -, -, h8⟩ := decBS_some hqt
  obtain ⟨hnPW, -⟩ := iwRd (o := pp) (w := 4) (by simpa using hnPi)
  have hpp9 : pp.toNat + 9 < 2 ^ 64 := by
    simp only [iwB, bool?, Option.map_eq_some_iff] at h8
    obtain ⟨x, hx, -⟩ := h8
    have := (truncM_iw_get hx).1
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    omega
  -- `struct_proj_bodies`
  obtain ⟨⟨r1, m1⟩, hW1, h⟩ := of_K h (by simp [dbtW.k_struct_proj_bodies.none])
  obtain ⟨x, a1, hrun1, hS1, hg1, hdec1, hA1⟩ := spbW_ok (fun _ => none) vis fe n m m1 a _ _ _ _ r1
    hW1 hS hw3lt (by rw [hnPW]; omega) (UInt64.toNat_lt _) hA
  rw [hnPW, hnFW, ← hname, ← hty0] at hrun1
  cases x with
  | none =>
    have h0 : r1.headD 0 = 0 := hdec1
    rw [dbtW.k_struct_proj_bodies.arm1 (hc1 := h0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a1, ?_, hS1, hg1, hA1, rfl⟩
    simp only [tblOne, hsc, StateT.run_bind, hrun1, except_ok_bind]
    rfl
  | some bodies =>
  obtain ⟨h01, hdb, hbb⟩ := hdec1
  rw [dbtW.k_struct_proj_bodies.arm2 (hc1 := by rw [h01]; decide)] at h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  -- `block_shape_lps`
  obtain ⟨⟨r2, m2⟩, hW2, h⟩ := of_K h (by simp [dbtW.k_block_shape_lps.none])
  rw [dbtW.k_block_shape_lps.arm1] at h
  have hq1 : decBS m1 pp.toNat = some bs := hq.stab (decBS_mono _) _ hg1
  obtain ⟨-, hdl2, hg2, hf2, hlb2, hroom2⟩ :=
    lpsW_dec hW2 hS1.iw.iwSize hS1.iw.ctl hS1.iw.erSize hq1 hpp9
  have hS2 : StageR vis fe m2 a1 :=
    ⟨CheckR.frame_iw hf2 hS1.check, IWOK.of_iw hf2 hS1.iw (hroom2 hS1.iw.iw)⟩
  have hA2 : AbsOK m2 := hA1.iw hf2
  -- the level parameters' copy
  obtain ⟨⟨r3, m3⟩, hW3, h⟩ := of_K h (by simp [dbtW.k_er_from_iw.none])
  rw [dbtW.k_er_from_iw.arm1] at h
  obtain ⟨hS3, hg3, hl3, hsl3⟩ := efF_stage hW3 hS2 hdl2 hlb2
  have hA3 := efF_afr hW3 hA2
  -- the bodies' copy
  obtain ⟨⟨r4, m4⟩, hW4, h⟩ := of_K h (by simp [dbtW.k_er_from_iw_2.none])
  rw [dbtW.k_er_from_iw_2.arm1] at h
  have hg13 := hg2.trans hg3
  have hdb3 := decHL_grow' hg13 hbb hdb
  obtain ⟨hS4, hg4, hl4, hsl4⟩ := efF_stage hW4 hS3 hdb3 (Nat.le_trans hbb hg13.iw)
  have hA4 := efF_afr hW4 hA3
  have hg04 : IWGrow m m4 := hg1.trans (hg13.trans hg4)
  -- the record
  obtain ⟨⟨q, m5⟩, hW5, h⟩ := of_K h (by simp [dbtW.k_erec_alloc.none])
  rw [dbtW.k_erec_alloc.arm1] at h
  replace h : some ([1, q], btMem m5 q pp cw cvw w0 (r3.headD 0) (r3.tail.headD 0) (r4.headD 0)
    (r4.tail.headD 0)) = some (r, m') := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hwn4 : erecP m4 cvw.toNat = some wn := by
    exact IWGrow.ext hg04 _ _ hwn
  have hfr : ErApart q 13 cvw := fun j hj => erFresh hW5 hS4.iw hwn4 hj
  rw [btMem_eq hfr]
  obtain ⟨-, hf5, -⟩ := erAllocW_spec hW5 hS4.iw
  have hr5 : ∀ x, erRd m5 x = erRd m4 x := fun x => by
    unfold erRd; rw [hf5.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  have hI5 : m5.arr64 IW = m4.arr64 IW := hf5.arr IW (by simp) (by decide)
  have l4 : (pp + 4).toNat < iwTop m := by
    have := (iwRd (o := pp) (w := 4) (by simpa using hnPi)).2
    rw [UInt64.toNat_add]; simp at this ⊢; omega
  have l1 : (cw + 1).toNat < iwTop m := by
    have := (iwRd (o := cw) (w := 1) (by rw [hcwv]; simpa using hnF)).2
    rw [UInt64.toNat_add]; simp at this ⊢; omega
  rw [hr5, (erRd_of_erecP hwn4).1, hI5, rdW_iw_grow hg04 l4, rdW_iw_grow hg04 l1]
  obtain ⟨hS6, hg6, -, -, -, -, hget⟩ := erRec_stage hW5 hS4 [6, 0, w0, r3.headD 0, r3.tail.headD 0,
    rdW (m.arr64 IW) (pp + 4), wn, rdW (m.arr64 IW) (cw + 1), 0, r4.headD 0, r4.tail.headD 0, 0, 0] rfl
  have hA6 : AbsOK (wrER m5 q [6, 0, w0, r3.headD 0, r3.tail.headD 0,
      rdW (m.arr64 IW) (pp + 4), wn, rdW (m.arr64 IW) (cw + 1), 0, r4.headD 0, r4.tail.headD 0, 0, 0]) :=
    (show AFr _ _ from AFr.of_frame (wrER_frame _ _ _)) (erAllocW_afr hW5 hA4)
  refine ⟨some (some ⟨mS.declared.name, bs.lps, bs.nP, cv0.name, nF, bodies⟩), a1, ?_, hS6, hg04.trans hg6, hA6,
    rfl, ?_⟩
  · simp only [tblOne, hsc, StateT.run_bind, hrun1, except_ok_bind]
    rfl
  · generalize wrER m5 q _ = M at hg6 hget
    have hgM : IWGrow m3 M := hg4.trans hg6
    have e2 := hget 2 (by simp)
    have e3 := hget 3 (by simp)
    have e4 := hget 4 (by simp)
    have e5 := hget 5 (by simp)
    have e6 := hget 6 (by simp)
    have e7 := hget 7 (by simp)
    have e9 := hget 9 (by simp)
    have e10 := hget 10 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at e2 e3 e4 e5 e6 e7 e9 e10
    have hsl3' := (IWGrow.ext hgM).hslice? hsl3
    have hsl4' := (IWGrow.ext hg6).hslice? hsl4
    rw [← hl3] at hsl3'
    rw [← hl4] at hsl4'
    simp only [List.headD_cons, List.tail_cons]
    -- `block_table` writes the record word by word: its offsets as numbers
    simp only [decTbl, show ProjTbl.structName.toNat = 2 from rfl, show ProjTbl.lpsOff.toNat = 3 from rfl,
      show ProjTbl.numParams.toNat = 5 from rfl, show ProjTbl.ctor.toNat = 6 from rfl,
      show ProjTbl.numFields.toNat = 7 from rfl, show ProjTbl.bodiesOff.toNat = 9 from rfl,
      Option.bind_eq_bind, hd?, hlist?, nat?, e2, e3, e4, e5, e6, e7, e9, e10,
      show q.toNat + 9 + 1 = q.toNat + 10 from rfl,
      Option.map_some, Option.bind_some, hw0lt, hwnlt, ite_true, hsl3', hsl4', hnPW, hnFW,
      Option.pure_def, ← hname, Array.toArray_toList]
    rw [hnm0, hnm']

/-! ## `block_tables` -/

/-- **The model of `block_tables(p, mo, ml)`** at exec fuel `n`. -/
l_model bts_spec {p : Prog} (hP : TablesProg p)
  fns [hP.bts ↦ btsW list]
  specs [dbt_spec hP n, slCons_specW p hP.alloc hP.iwCopy hP.slCons n]
  grind [arena_grind]

/-- A table record pointer consed onto a slice of `EREC` table records (`sl_cons`). -/
theorem consW_tbl {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {ts : List IProjTable} {t : IProjTable}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a) (hb : o.toNat + l.toNat ≤ iwTop m)
    (hd : decPL m (decTbl (erecP m)) o.toNat l.toNat = some ts) (hx : decTbl (erecP m) x.toNat = some t) :
    decPL m' (decTbl (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some (t :: ts) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  rw [decPL_eq_bind] at hd
  rcases hps : decNL m o.toNat l.toNat with _ | ps <;> rw [hps] at hd
  · cases hd
  simp only [Option.bind_some] at hd
  obtain ⟨hS', hg, hd', ht'⟩ := consW_stageN h hS hb hps
  have hext := IWGrow.ext hg
  refine ⟨?_, ht', hS', hg⟩
  rw [decPL_eq_bind, hd']
  simp only [Option.bind_some, List.mapM_cons]
  rw [show decTbl (erecP m') x.toNat = some t from hext.decTbl hx,
    ArrExt.mapM (f := decTbl (erecP m)) (g := decTbl (erecP m')) (fun _ _ hy => hext.decTbl hy) _ _ hd]
  rfl

/-- A slice of `EREC` table records below the `IW` top, across pool growth. -/
theorem decPL_tbl_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} {ts : List IProjTable}
    (hb : o + l ≤ iwTop m) (hd : decPL m (decTbl (erecP m)) o l = some ts) :
    decPL m' (decTbl (erecP m')) o l = some ts := by
  rw [decPL_eq_bind] at hd ⊢
  rcases hps : decNL m o l with _ | ps <;> rw [hps] at hd
  · cases hd
  have hps' : decNL m' o l = some ps := by
    rw [← hps]; simp only [decNL]; apply L.Ind.mapM_congr_of; intro j hj
    simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet _ (by simp at hj; omega)]
  rw [hps']
  simp only [Option.bind_some] at hd ⊢
  exact ArrExt.mapM (fun _ _ hy => (IWGrow.ext hg).decTbl hy) _ _ hd

/-- What `block_tables` returns: `(0, _, _)` the twin's `none`, `(1, off, len)` an `IW` slice of
`EREC` table records below the pool's top. -/
def BtsR (m : Mem) (r : List Word) : Option (List IProjTable) → Prop
  | none => r.headD 0 = 0
  | some ts => r.headD 0 = 1 ∧
      decPL m (decTbl (erecP m)) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some ts ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m

/-- **`block_tables` refines `blockTables`**: `(1, off, len)` an `IW` slice of `EREC` table
records below the pool's top, `(0, _, _)` the twin's `none`. -/
theorem btsW_ok {p : Prog} (_hP : TablesProg p) (pp : Word) (bs : BlockShape) (vis : Word) (fe : IFEnv)
    (hnP : 1 + bs.nP < 2 ^ 64) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (mo ml : Word) (mss : List MemberShape) (r : List Word),
    StageR vis fe m a → AbsOK m → DecB (fun m => decBS m pp.toNat) m bs → PSlR0 decMS mss mo ml m →
    btsW n m pp mo ml = some (r, m') →
    ∃ ts a', (ConRon.Arena.blockTables bs mss).run a = .ok (ts, a') ∧ BtsR m' r ts ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a mo ml mss r _ _ _ _ h; simp [btsW] at h
  | succ n ih =>
  intro m m' a mo ml mss r hS hA hq hmss h
  by_cases hl : ml = 0
  · rw [btsW.arm1 n m pp mo ml hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : mss = [] := by
      have h := hmss.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨some [], a, rfl, ⟨rfl, by simp [decPL], by simp⟩, hS, IWGrow.refl m, hA⟩
  obtain ⟨q, ms, rest, rfl, hw, hqb, hdms, hrest⟩ := partsPSl_cons ⟨hmss.1, hmss.2.resolve_left hl⟩ hl
  rw [btsW.arm2 n m pp mo ml hl, hw] at h
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [btsW.k_block_table.none])
  obtain ⟨x, a1, hrun1, hS1, hg1, hA1, hx⟩ := btW_ok hS hA hq (by rw [hq']; exact hdms) hnP h1
  rcases x with _ | _ | t
  · have h2 : r1.headD 0 = 2 := hx
    rw [btsW.k_block_table.arm1 (hc1 := h2)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a1, ?_, rfl, hS1, hg1, hA1⟩
    simp only [blockTables_cons, StateT.run_bind, hrun1, except_ok_bind]; rfl
  all_goals rw [btsW.k_block_table.arm2 (hc1 := by rw [show r1.headD 0 = _ from by first | exact hx | exact hx.1]; decide)] at h
  all_goals obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [btsW.k_block_tables.none])
  all_goals obtain ⟨ts, a3, hrun3, hd3, hS3, hg3, hA3⟩ := ih m1 m3 a1 (mo + 1) (ml - 1) rest r3 hS1 hA1 (hq.grow (decBS_mono _) hg1) (PSlR0.grow decMS_mono ⟨hrest.dec, Or.inr hrest.bound⟩ hg1) h3
  · have h0 : r1.headD 0 = 0 := hx
    rw [btsW.k_block_tables.arm1 (hc1 := h0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨ts, a3, ?_, by cases ts <;> simpa [BtsR] using hd3, hS3, hg1.trans hg3, hA3⟩
    simp only [blockTables_cons, StateT.run_bind, hrun1, except_ok_bind, tblRest, hrun3]
    cases ts <;> rfl
  · obtain ⟨h01, hdt⟩ := hx
    rcases ts with _ | ts
    · have hz : r3.headD 0 = 0 := hd3
      rw [btsW.k_block_tables.arm2 (hc1 := by rw [h01]; decide) (hc2 := hz)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨none, a3, ?_, rfl, hS3, hg1.trans hg3, hA3⟩
      simp only [blockTables_cons, StateT.run_bind, hrun1, except_ok_bind, tblRest, hrun3]; rfl
    obtain ⟨h31, hd3, hb3⟩ := hd3
    rw [btsW.k_block_tables.arm3 (hc1 := by rw [h01]; decide) (hc2 := by rw [h31]; decide)] at h
    obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [btsW.k_sl_cons.none])
    rw [btsW.k_sl_cons.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hd5, hb5, hS5, hg5⟩ := consW_tbl h4 hS3 hb3 hd3
      (hg3.ext.decTbl hdt)
    refine ⟨some (t :: ts), a3, ?_, ⟨rfl, by simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega⟩, hS5,
      hg1.trans (hg3.trans hg5), hA3.consW h4⟩
    simp only [blockTables_cons, StateT.run_bind, hrun1, except_ok_bind, tblRest, hrun3]
    rfl

/-- What the tables' checks need of each table: its level parameters' names read back and its
parameter count bounded. -/
def TblsOK (st : EStore) (Q : List IProjTable) : Prop :=
  ∀ t ∈ Q, (∃ ks, t.levelParams.mapM (denoteN st.lss.ls.ns) = some ks) ∧ t.numParams + 1 < 2 ^ 64

/-- **The tables `blockTables` builds** carry the block's level parameters and parameter count. -/
theorem blockTables_tbls (bs : BlockShape) : ∀ (mss : List MemberShape) (a a' : AState)
    (ts : List IProjTable), (ConRon.Arena.blockTables bs mss).run a = .ok (some ts, a') →
    ∀ t ∈ ts, t.levelParams = bs.lps ∧ t.numParams = bs.nP
  | [], a, a', ts, h => by
    simp only [ConRon.Arena.blockTables] at h
    cases h; intro t ht; cases ht
  | ms :: rest, a, a', ts, h => by
    rw [blockTables_cons, StateT.run_bind] at h
    rcases h1 : (tblOne bs ms).run a with e | ⟨o, a1⟩
    · rw [h1] at h; cases h
    rw [h1, except_ok_bind] at h
    rcases o with _ | o
    · cases h
    simp only [tblRest, StateT.run_bind] at h
    rcases h2 : (ConRon.Arena.blockTables bs rest).run a1 with e | ⟨r, a2⟩
    · rw [h2] at h; cases h
    rw [h2, except_ok_bind] at h
    rcases r with _ | ts'
    · cases h
    have hts : ts = o.toList ++ ts' := by cases h; rfl
    subst hts
    have ih := blockTables_tbls bs rest a1 a2 ts' h2
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases o with _ | t0
      · cases ht
      have ht0 : t = t0 := by simpa using ht
      subst ht0
      unfold tblOne at h1
      split at h1
      · simp only [StateT.run_bind] at h1
        rcases h3 : (structProjBodies _ _ _ _).run a with e | ⟨x, a3⟩
        · rw [h3] at h1; cases h1
        rw [h3, except_ok_bind] at h1
        rcases x with _ | bodies
        · cases h1
        cases h1; exact ⟨rfl, rfl⟩
      · cases h1
    · exact ih t ht

end L.Ind

end
