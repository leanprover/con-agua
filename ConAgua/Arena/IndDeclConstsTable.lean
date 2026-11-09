module

public import ConAgua.Arena.IndDeclConstsBlock
public import ConAgua.Arena.IndSumSpec.StructProjBodies
public import ConAgua.Arena.IndPartsSpec.MemberNames
public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.IndSumSpec.TsrW
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

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
  ipal : IpalF p
  bt : p.lookup "block_table" = some blockTable
  bts : p.lookup "block_tables" = some blockTables

/-! ## The twin, one member at a time -/

/-- One member's table, if any (`blockTables`' step). -/
def tblOne (bs : BlockShape) (ms : MemberShape) : AM (Option IProjTable) :=
  match ms.structCtor? with
  | some c => do
    match ← structProjBodies ms.declared.name bs.nP c.2 c.1.type with
    | some bodies => pure (some ⟨ms.declared.name, bs.lps, bs.nP, c.1.name, c.2, bodies⟩)
    | none => pure none
  | none => pure none

theorem blockTables_cons (bs : BlockShape) (ms : MemberShape) (rest : List MemberShape) :
    ConRon.Arena.blockTables bs (ms :: rest) =
      (do let o ← tblOne bs ms; let ts ← ConRon.Arena.blockTables bs rest; pure (o.toList ++ ts)) := by
  cases h : ms.structCtor? with
  | none => simp [ConRon.Arena.blockTables, tblOne, h]
  | some c =>
    simp only [ConRon.Arena.blockTables, tblOne, h, bind_assoc]
    congr 1; funext x
    cases x <;> simp

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

/-- After `erec_alloc`: the puts. -/
def btK5 (pp c cv T elo ell ebo ebl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([1, r.headD 0], btMem m (r.headD 0) pp c cv T elo ell ebo ebl)

/-- After the bodies' copy: the record. -/
def btK4 (p : Prog) (n : Nat) (pp c cv T elo ell : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => btK5 pp c cv T elo ell (r.headD 0) (r.tail.headD 0) (callW p n "erec_alloc" [13] m)

/-- After the level parameters' copy: the bodies'. -/
def btK3 (p : Prog) (n : Nat) (pp c cv T bo bl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => btK4 p n pp c cv T (r.headD 0) (r.tail.headD 0) (callW p n "er_from_iw" [bo, bl] m)

/-- After `block_shape_lps`: their copy. -/
def btK2 (p : Prog) (n : Nat) (pp c cv T bo bl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => btK3 p n pp c cv T bo bl (callW p n "er_from_iw" [r.headD 0, r.tail.headD 0] m)

/-- After `struct_proj_bodies`. -/
def btK1 (p : Prog) (n : Nat) (pp c cv T : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else btK2 p n pp c cv T (r.tail.headD 0) (r.tail.tail.headD 0) (callW p n "block_shape_lps" [pp] m)

/-- **The model of `block_table(p, ms)`** at exec fuel `n`. -/
def btW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, pp, ms =>
    if rdW (m.arr64 IW) (ms + 3) ≠ 1 then some ([0, 0], m)
    else if rdW (m.arr64 IW) (ms + 1) ≠ 0 then some ([0, 0], m)
    else
      let c := rdW (m.arr64 IW) (rdW (m.arr64 IW) (ms + 2))
      let cv := rdW (m.arr64 IW) c
      let T := erRd m (rdW (m.arr64 IW) (ms + 4))
      btK1 p n pp c cv T (callW p n "struct_proj_bodies"
        [T, rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (c + 1), erRd m (cv + 3)] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp c cv T bo bl elo ell ebo ebl : Word) (r : List Word)
theorem btK5_some : btK5 pp c cv T elo ell ebo ebl (some (r, m)) =
    some ([1, r.headD 0], btMem m (r.headD 0) pp c cv T elo ell ebo ebl) := rfl
theorem btK4_some : btK4 p n pp c cv T elo ell (some (r, m)) =
    btK5 pp c cv T elo ell (r.headD 0) (r.tail.headD 0) (callW p n "erec_alloc" [13] m) := rfl
theorem btK3_some : btK3 p n pp c cv T bo bl (some (r, m)) =
    btK4 p n pp c cv T (r.headD 0) (r.tail.headD 0) (callW p n "er_from_iw" [bo, bl] m) := rfl
theorem btK2_some : btK2 p n pp c cv T bo bl (some (r, m)) =
    btK3 p n pp c cv T bo bl (callW p n "er_from_iw" [r.headD 0, r.tail.headD 0] m) := rfl
theorem btK1_some : btK1 p n pp c cv T (some (r, m)) =
    if r.headD 0 = 0 then some ([0, 0], m)
    else btK2 p n pp c cv T (r.tail.headD 0) (r.tail.tail.headD 0) (callW p n "block_shape_lps" [pp] m) := rfl
end arms
attribute [ind_grind] btK5_some btK4_some btK3_some btK2_some btK1_some

theorem bt_spec {p : Prog} (hP : TablesProg p) (n : Nat) (s₀ : St) (pp ms : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_table" [pp, ms]
    ⦃fun r s' => LocEq s' s₀ ∧ btW p n s₀.mem pp ms = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.bt]
  simp only [callFn, blockTable]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "struct_proj_bodies", callW_spec p n "block_shape_lps",
        callW_spec p n "er_from_iw", callW_spec p n "erec_alloc", erecPut_specW p hP.erPut n] <;>
      finish (gen := 40) (instances := 20000) [btW, btMem, erRd, rdW_eq]

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

/-- One member's table result: `(0, _)` none, `(1, q)` the table record at `q`. -/
def TblR (m : Mem) (r : List Word) : Option IProjTable → Prop
  | none => r.headD 0 = 0
  | some t => r.headD 0 = 1 ∧ decTbl (erecP m) (r.tail.headD 0).toNat = some t

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
theorem btW_ok {p : Prog} (hP : TablesProg p) {vis : Word} {fe : IFEnv} {n : Nat} {m m' : Mem}
    {a : AState} {pp ms : Word} {bs : BlockShape} {mS : MemberShape} {r : List Word}
    (hS : StageR vis fe m a) (hA : AbsOK m) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hms : DecB (fun m => decMS m ms.toNat) m mS) (hnP : 1 + bs.nP < 2 ^ 64)
    (h : btW p n m pp ms = some (r, m')) :
    ∃ x a', (tblOne bs mS).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
      TblR m' r x := by
  rcases n with _ | n
  · simp [btW] at h
  have hms0 : decMS (truncM m) ms.toNat = some mS := hms
  obtain ⟨-, ⟨da, hda, hdecl⟩, hnI, hct⟩ := decMS_some hms0
  obtain ⟨co, cl, hco, hcl, hcs⟩ := decAt_some hct
  have hlen := decPL_length (truncM m) hcs
  obtain ⟨hclW, -⟩ := iwRd (o := ms) (w := 3) (by simpa using hcl)
  obtain ⟨hnIW, -⟩ := iwRd (o := ms) (w := 1) (by simpa using hnI)
  simp only [btW] at h
  -- the declines
  by_cases h3 : rdW (m.arr64 IW) (ms + 3) ≠ 1
  · rw [ite_eq_left h3] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : mS.structCtor? = none := structCtor?_none (.inl (by
      rw [hlen, ← hclW]; intro e; exact h3 (UInt64.toNat_inj.mp (by simpa using e))))
    exact ⟨none, a, by simp [tblOne, this]; rfl, hS, IWGrow.refl m, hA, rfl⟩
  rw [ite_eq_right h3] at h
  by_cases h1 : rdW (m.arr64 IW) (ms + 1) ≠ 0
  · rw [ite_eq_left h1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : mS.structCtor? = none := structCtor?_none (.inr (by
      rw [← hnIW]; intro e; exact h1 (UInt64.toNat_inj.mp (by simpa using e))))
    exact ⟨none, a, by simp [tblOne, this]; rfl, hS, IWGrow.refl m, hA, rfl⟩
  rw [ite_eq_right h1] at h
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
  obtain ⟨⟨r1, m1⟩, hc1, h⟩ := of_K h (by simp [btK1])
  rcases n with _ | n
  · exact (callW_zero_false hc1).elim
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (spbW_spec p hP.alloc hP.iwCopy hP.slCons hP.sView hP.sDerB hP.sBvarFind hP.sBvarPush hP.sInternBVar
      hP.sProjFind hP.sProjPush hP.sInternProj hP.sMkProj hP.sArgP hP.sGo hP.sPsAtGo hP.sPsAt hP.sProjPs
      hP.spb hP.i1l hP.ipal (n + 1) _ _ _ _ _) hc1
  obtain ⟨x, a1, hrun1, hS1, hg1, hdec1, hA1⟩ := spbW_ok (fun _ => none) vis fe (n + 1) m s1.mem a _ _ _ _ r1
    hW1 hS hw3lt (by rw [hnPW]; omega) (UInt64.toNat_lt _) hA
  rw [hnPW, hnFW, ← hname, ← hty0] at hrun1
  rw [btK1_some] at h
  cases x with
  | none =>
    have h0 : r1.headD 0 = 0 := hdec1
    rw [ite_eq_left h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a1, ?_, hS1, hg1, hA1, rfl⟩
    simp only [tblOne, hsc, StateT.run_bind, hrun1, except_ok_bind]
    rfl
  | some bodies =>
  obtain ⟨h01, hdb, hbb⟩ := hdec1
  rw [ite_eq_right (by rw [h01]; decide)] at h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  -- `block_shape_lps`
  obtain ⟨⟨r2, m2⟩, hc2, h⟩ := of_K h (by simp [btK2])
  rw [btK2_some] at h
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockShapeLps_spec p hP.alloc hP.tErCopy hP.tErToIw hP.lps (n + 1) _ pp) hc2
  have hq1 : decBS s1.mem pp.toNat = some bs := hq.stab (decBS_mono _) _ hg1
  obtain ⟨-, hdl2, hg2, hf2, hlb2, hroom2⟩ :=
    lpsW_dec hW2 hS1.iw.iwSize hS1.iw.ctl hS1.iw.erSize hq1 hpp9
  have hS2 : StageR vis fe s2.mem a1 :=
    ⟨CheckR.frame_iw hf2 hS1.check, IWOK.of_iw hf2 hS1.iw (hroom2 hS1.iw.iw)⟩
  have hA2 : AbsOK s2.mem := hA1.iw hf2
  -- the level parameters' copy
  obtain ⟨⟨r3, m3⟩, hc3, h⟩ := of_K h (by simp [btK3])
  rw [btK3_some] at h
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (efF_spec p hP.cbr.tsr hP.erPut (n + 1) _ _ _) hc3
  obtain ⟨hS3, hg3, hl3, hsl3⟩ := efF_stage hW3 hS2 hdl2 hlb2
  have hA3 := efF_afr hW3 hA2
  -- the bodies' copy
  obtain ⟨⟨r4, m4⟩, hc4, h⟩ := of_K h (by simp [btK4])
  rw [btK4_some] at h
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (efF_spec p hP.cbr.tsr hP.erPut (n + 1) _ _ _) hc4
  have hg13 := hg2.trans hg3
  have hdb3 := decHL_grow' hg13 hbb hdb
  obtain ⟨hS4, hg4, hl4, hsl4⟩ := efF_stage hW4 hS3 hdb3 (Nat.le_trans hbb hg13.iw)
  have hA4 := efF_afr hW4 hA3
  have hg04 : IWGrow m s4.mem := hg1.trans (hg13.trans hg4)
  -- the record
  obtain ⟨⟨r5, m5⟩, hc5, h⟩ := of_K h (by simp [btK5])
  rw [btK5_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s5, rfl, -, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (erecAlloc_specW p hP.erAlloc (n + 1) _ 13) hc5
  generalize hqq : r5.headD 0 = q at hW5 ⊢
  have hwn4 : erecP s4.mem cvw.toNat = some wn := by
    exact IWGrow.ext hg04 _ _ hwn
  have hfr : ErApart q 13 cvw := fun j hj => erFresh hW5 hS4.iw hwn4 hj
  rw [btMem_eq hfr]
  obtain ⟨-, hf5, -⟩ := erAllocW_spec hW5 hS4.iw
  have hr5 : ∀ x, erRd s5.mem x = erRd s4.mem x := fun x => by
    unfold erRd; rw [hf5.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  have hI5 : s5.mem.arr64 IW = s4.mem.arr64 IW := hf5.arr IW (by simp) (by decide)
  have l4 : (pp + 4).toNat < iwTop m := by
    have := (iwRd (o := pp) (w := 4) (by simpa using hnPi)).2
    rw [UInt64.toNat_add]; simp at this ⊢; omega
  have l1 : (cw + 1).toNat < iwTop m := by
    have := (iwRd (o := cw) (w := 1) (by rw [hcwv]; simpa using hnF)).2
    rw [UInt64.toNat_add]; simp at this ⊢; omega
  rw [hr5, (erRd_of_erecP hwn4).1, hI5, rdWIW_grow hg04 l4, rdWIW_grow hg04 l1]
  obtain ⟨hS6, hg6, -, -, -, -, hget⟩ := erRec_stage hW5 hS4 [6, 0, w0, r3.headD 0, r3.tail.headD 0,
    rdW (m.arr64 IW) (pp + 4), wn, rdW (m.arr64 IW) (cw + 1), 0, r4.headD 0, r4.tail.headD 0, 0, 0] rfl
  have hA6 : AbsOK (wrER s5.mem q [6, 0, w0, r3.headD 0, r3.tail.headD 0,
      rdW (m.arr64 IW) (pp + 4), wn, rdW (m.arr64 IW) (cw + 1), 0, r4.headD 0, r4.tail.headD 0, 0, 0]) :=
    (show AFr _ _ from AFr.of_frame (wrER_frame _ _ _)) (erAllocW_afr hW5 hA4)
  refine ⟨some ⟨mS.declared.name, bs.lps, bs.nP, cv0.name, nF, bodies⟩, a1, ?_, hS6, hg04.trans hg6, hA6,
    rfl, ?_⟩
  · simp only [tblOne, hsc, StateT.run_bind, hrun1, except_ok_bind]
    rfl
  · generalize wrER s5.mem q _ = M at hg6 hget
    have hgM : IWGrow s3.mem M := hg4.trans hg6
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
    simp only [decTbl, Option.bind_eq_bind, hd?, hlist?, nat?, e2, e3, e4, e5, e6, e7, e9, e10,
      show q.toNat + 9 + 1 = q.toNat + 10 from rfl,
      Option.map_some, Option.bind_some, hw0lt, hwnlt, ite_true, hsl3', hsl4', hnPW, hnFW,
      Option.pure_def, ← hname, Array.toArray_toList]
    rw [hnm0, hnm']

end L.Ind

end
