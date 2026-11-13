module

public import ConAgua.Arena.IndDeclConstsDeclared
public import ConAgua.Arena.IndInstallSpec.IcaW
public import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.RecClassSpec.CloseLams
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

import ConAgua.L.ModelGen

@[expose] public section

/-!
# A declaration's constants: the formers (lane `ronsync2`, stage 3)

`block_formers_go(p, isRec, d.off, d.len, i)` and `block_formers(p, isRec)` refine con-ron's
`blockFormers` (`Arena/Install.lean`, pure): each member's former as declared (`block_shape_declared`,
`declW_dec`), an `.indInfo` record with its capability record `blockCapsAt p i isRec`
(`block_caps_at`, `ind_info_rec`: `blockCapsAt_ok`, `iirW_stage`), consed into an `IW` slice of
`EREC` constant records (`sl_cons`, `consW_ci`). Models in the continuation style of `icbiW`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `block_formers`. -/
structure FormersProg (p : Prog) : Prop extends ConsIndsProg p where
  iwCopy : p.lookup "iw_copy" = some iwCopy
  slCons : p.lookup "sl_cons" = some slCons
  fieldCopy : p.lookup "member_field_copy" = some memberFieldCopy
  declared : p.lookup "block_shape_declared" = some blockShapeDeclared
  bfg : p.lookup "block_formers_go" = some blockFormersGo
  bf : p.lookup "block_formers" = some blockFormers

/-- The twin's formers from member `i` on (each capability record a twin run: its never-zero read). -/
def formersFrom (bs : BlockShape) (b : Bool) (cvs : List IConstantVal) (i : Nat) : AM (List IConstantInfo) :=
  (cvs.zipIdx i).mapM fun (cv, j) => do pure (IConstantInfo.indInfo cv (← ConRon.Arena.blockCapsAt bs j b))

theorem formersFrom_nil (bs : BlockShape) (b : Bool) (i : Nat) : formersFrom bs b [] i = pure [] := by
  simp [formersFrom]

theorem formersFrom_cons (bs : BlockShape) (b : Bool) (cv : IConstantVal) (cvs : List IConstantVal)
    (i : Nat) : formersFrom bs b (cv :: cvs) i = (do
      let c ← ConRon.Arena.blockCapsAt bs i b
      let r ← formersFrom bs b cvs (i + 1)
      pure (IConstantInfo.indInfo cv c :: r)) := by
  simp [formersFrom, List.zipIdx_cons, List.mapM_cons, bind_assoc]

theorem blockFormers_eq (bs : BlockShape) (b : Bool) :
    ConRon.Arena.blockFormers bs b = formersFrom bs b (bs.members.map (·.declared)) 0 := rfl

/-! ## `block_formers_go` -/

/-- **The model of `block_formers_go(p, isRec, dO, dL, i)`** at exec fuel `n`. -/
l_model bfg_spec (p : Prog) (hp : p.lookup "block_formers_go" = some blockFormersGo)
  fns [hp ↦ bfgW list]
  specs [callW_spec p n "block_caps_at", callW_spec p n "ind_info_rec", callW_spec p n "sl_cons"]
  grind [arena_grind]

/-- `sl_cons`' run, as its model. -/
theorem consCall {p : Prog} (hP : FormersProg p) {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) : consW n m x o l = some (r, m') := by
  obtain ⟨s', rfl, -, hK⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.iwCopy hP.slCons n _ x o l) h
  exact hK

/-- **`block_formers_go` refines the formers from member `i` on**: an `IW` slice of `EREC`
constant records below the pool's top. -/
theorem bfgW_ok {p : Prog} (hP : FormersProg p) (pp isRec : Word) (bs : BlockShape) (b : Bool)
    (hb : (isRec != 0) = b) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (a : AState) (m m' : Mem) (dO dL i : Word) (cvs : List IConstantVal) (r : List Word),
    StageR vis fe m a → ReadLCOK a → SortsDen a → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    PSlR decCVp cvs dO dL m → i.toNat + dL.toNat < 2 ^ 64 →
    bfgW p n m pp isRec dO dL i = some (r, m') →
    ∃ L a', (formersFrom bs b cvs i.toNat).run a = .ok (L, a') ∧
      decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some L ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      a'.store = a.store ∧ ReadLCOK a' := by
  induction n with
  | zero => intro a m m' dO dL i cvs r _ _ _ _ _ _ _ h; simp [bfgW] at h
  | succ n ih =>
  intro a m m' dO dL i cvs r hS hrl hsd hq hsrc hcvs hil h
  by_cases hl : dL = 0
  · rw [bfgW.arm1 p n m pp isRec dO dL i hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨[], a, by rw [formersFrom_nil]; rfl, by simp [decPL], by simp, hS, IWGrow.refl m, rfl, hrl⟩
  obtain ⟨q, cv, rest, rfl, hw, hqb, hdcv, hrest⟩ := partsPSl_cons hcvs hl
  rw [bfgW.arm2 p n m pp isRec dO dL i hl] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [bfgW.k_block_caps_at.none])
  rw [bfgW.k_block_caps_at.arm1] at h
  obtain ⟨caps, a1, hrun1, hS1, hg1, hca, hst1, hrl1⟩ := blockCapsAt_ok hP.toCapsProg n hq hsrc hb h1 hS hrl hsd
  have hsd1 : SortsDen a1 := by unfold SortsDen; rw [hst1]; exact hsd
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [bfgW.k_ind_info_rec.none])
  rw [bfgW.k_ind_info_rec.arm1] at h
  have hlpos : 0 < dL.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hol : dO.toNat < iwTop m := by have := hcvs.2; omega
  have hw1 : rdW (m1.arr64 IW) dO = UInt64.ofNat q := by
    rw [← hw]; simp only [rdW]; rw [hg1.iwGet _ hol]
  rw [hw1] at h2
  obtain ⟨q2, rfl, hW2⟩ := installIirRun hP.toConsIndsProg h2
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨hS2, hg2, hci⟩ := iirW_stage hW2 hS1 (by rw [hq']; exact hdcv.grow (OMono.decCVp _) hg1) hca
  have hg12 := hg1.trans hg2
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bfgW.k_block_formers_go.none])
  simp only [List.headD_cons] at h
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (dL - 1).toNat = dL.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  obtain ⟨L3, a3, hrun3, hd3, hb3, hS3, hg3, hst3, hrl3⟩ := ih a1 m2 m3 (dO + 1) (dL - 1) (i + 1) rest r3 hS2
    hrl1 hsd1 (hq.grow (decBS_mono _) hg12) (partsHsrc_grow hg12 hq9 hsrc)
    (hrest.grow (fun q => OMono.decCVp q) hg12) (by omega) h3
  rw [hi1] at hrun3
  rw [bfgW.k_block_formers_go.arm1] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bfgW.k_sl_cons.none])
  rw [bfgW.k_sl_cons.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hd5, hb5, hS5, hg5⟩ := consW_ci (consCall hP h4) hS3 hb3 hd3
    (hg3.ext.decCI hci)
  refine ⟨_, a3, ?_, by simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega, hS5,
    hg12.trans (hg3.trans hg5), hst3.trans hst1, hrl3⟩
  rw [formersFrom_cons]
  simp only [StateT.run_bind, hrun1, except_ok_bind, hrun3]
  rfl

/-! ## `block_formers` -/

/-- `partsShapeFacts` with the member records' word `4` (`declared`) below the top. -/
theorem shapeFacts4 {m : Mem} {q : Word} {bs : BlockShape}
    (hq : DecB (fun m => decBS m q.toNat) m bs) :
    ∀ o l j v, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v + 4 < iwTop m := by
  have hqt : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, -⟩ := partsAt decMS_mono hmem
  have hq1 : q.toNat + 1 < iwTop m := partsIwLt hl
  have hoN : iwN m q.toNat = some o.toNat := by rw [← iwN_truncM (by omega)]; exact ho
  have hlN : iwN m (q.toNat + 1) = some l.toNat := by rw [← iwN_truncM (by omega)]; exact hl
  intro o' l' j v h1 h2 hj hv
  rw [hoN] at h1; rw [hlN] at h2
  simp only [Option.some.injEq] at h1 h2; subst h1 h2
  obtain ⟨v', hv', hms⟩ := decPL_getH (truncM m) (show decPL _ _ _ _ = _ from hdm) j hj
  have hlt := partsIwLt hv'
  rw [iwN_truncM hlt, hv] at hv'
  simp only [Option.some.injEq] at hv'; subst hv'
  obtain ⟨-, ⟨a, ha, -⟩, -⟩ := decMS_some hms
  exact partsIwLt ha

/-- **The model of `block_formers(p, isRec)`** at exec fuel `n`. -/
l_model dbf_spec (p : Prog) (hp : p.lookup "block_formers" = some blockFormers)
  fns [hp ↦ dbfW list]
  specs [callW_spec p n "block_shape_declared", callW_spec p n "block_formers_go"]
  grind [arena_grind]

/-- **`block_formers` refines `blockFormers`** (pure in the twin): an `IW` slice of `EREC`
constant records below the pool's top. -/
theorem bfW_ok {p : Prog} (hP : FormersProg p) {n : Nat} {m m' : Mem} {pp isRec : Word}
    {bs : BlockShape} {b : Bool} {r : List Word} {a : AState} {vis : Word} {fe : IFEnv}
    (hb : (isRec != 0) = b) (hS : StageR vis fe m a) (hrl : ReadLCOK a) (hsd : SortsDen a)
    (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hsrc : ShapeSrc m pp) (h : dbfW p n m pp isRec = some (r, m')) :
    ∃ L a', (ConRon.Arena.blockFormers bs b).run a = .ok (L, a') ∧
      decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some L ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      a'.store = a.store ∧ ReadLCOK a' := by
  rcases n with _ | n
  · simp [dbfW] at h
  rw [dbfW.arm1] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [dbfW.k_block_shape_declared.none])
  rw [dbfW.k_block_shape_declared.arm1] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [dbfW.k_block_formers_go.none])
  rw [dbfW.k_block_formers_go.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeDeclared_spec p hP.alloc hP.fieldCopy hP.declared n _ pp) h1
  obtain ⟨hqd, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨er, hdd, hg1, hf1, htop1, hroom1⟩ := declW_dec hW1 hS.iw.iwSize hS.iw.ctl hqd hq9 hsrc
    (shapeFacts4 hq)
  dsimp only at hdd htop1 hroom1 hf1 hg1
  have hS1 : StageR vis fe s1.mem a :=
    ⟨CheckR.frame_iw hf1 hS.check, IWOK.of_iw hf1 hS.iw (by rw [hf1.size IW]; exact hroom1)⟩
  subst er
  have hk : bs.k < 2 ^ 64 := by
    have := (rdW (s1.mem.arr64 CTL) 200).toNat_lt; have h' := htop1; simp only [iwTop] at h'; omega
  have hkk : (UInt64.ofNat bs.k : Word).toNat = bs.k := UInt64.toNat_ofNat_of_lt' hk
  simp only [List.headD_cons, List.tail_cons] at h2
  have hcvs : PSlR decCVp (bs.members.map (·.declared)) (rdW (m.arr64 CTL) 200) (UInt64.ofNat bs.k) s1.mem :=
    ⟨by rw [hkk]; exact decPLcv_decB hdd (by omega), by have := hkk; omega⟩
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (bfg_spec p hP.bfg n _ pp isRec _ _ 0) h2
  obtain ⟨L, a', hrun, hd, hbd, hS2, hg2, hst, hrl'⟩ := bfgW_ok hP pp isRec bs b hb vis fe n a _ _ _ _ 0 _ _ hS1
    hrl hsd (hq.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hcvs
    (by rw [hkk]; simp; omega) hW2
  exact ⟨L, a', by rw [blockFormers_eq]; simpa using hrun, by simpa using hd, by simpa using hbd, hS2,
    hg1.trans hg2, hst, hrl'⟩

end L.Ind

end
