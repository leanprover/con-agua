module

public import ConAgua.Arena.IndDeclConstsRefire
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
public import ConAgua.Arena.IndInstallSpec.InstallCtxWord9
import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# A declaration's constants: the recursors (lane `ronsync2`, stage 3)

`block_rec(p, rc)` refines one step of con-ron's `blockRecs` (`Arena/Install.lean`): the fire
(`rec_fire`, `rfW_ok`), its slices copied into `EREC` (`er_from_iw`, `efW_stage`), the rules refired
into a fresh run (`rules_refire`, `rrW_ok`), the `.recInfo` record (`rec_info_rec`, `riRec_stage`).
`block_recs(p, recs.off, recs.len)` refines `blockRecs p recs`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `block_rec(s)`. -/
structure RecsProg (p : Prog) : Prop extends FireProg p where
  cbr : CbrLook p
  rr : p.lookup "rules_refire" = some rulesRefire
  br : p.lookup "block_rec" = some blockRec
  brs : p.lookup "block_recs" = some blockRecs

l_model br_spec (p : Prog) (hP : RecsProg p)
  fns [hP.br ↦ brW]
  specs [rf_spec p hP.toFireProg n, efF_spec p hP.cbr.tsr hP.erPut n, erecAlloc_specW p hP.erAlloc n,
    rr_spec p hP.erPut hP.rr n, ri_spec p hP.cbr hP.erPut n]
  grind [arena_grind]

/-- `er_from_iw` at the fuel-shifted model. -/
theorem efF_stage {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {o l : Word} {r : List Word} {kk : IdxKind} {xs : List (Idx kk)}
    (h : efF n m o l = some (r, m'))
    (hS : StageR vis fe m a) (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = l ∧
      hslice? (erecP m') (r.headD 0).toNat l.toNat = some xs := by
  cases n with
  | zero => simp [efF] at h
  | succ n => exact efW_stage n h hS hd hb

theorem getD4_eq (r : List Word) : r.getD 4 0 = r.tail.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> rfl

/-- A `Bool` word of `IW` below the top, as the model reads it. -/
theorem rdW_of_iwB {m : Mem} {o w : Word} {b : Bool} (h : iwB (truncM m) (o.toNat + w.toNat) = some b) :
    (rdW (m.arr64 IW) (o + w) != 0) = b := by
  simp only [iwB, bool?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hlt, hx'⟩ := truncM_iw_get hx
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have e : (o + w).toNat = o.toNat + w.toNat := by rw [UInt64.toNat_add]; omega
  simp only [iwA, aread_apply] at hx'
  rw [rdW_of_get? e.symm hx']

/-- **`block_rec` refines one recursor of `blockRecs`**: the `.recInfo` record with its rules
refired at `recFire`'s fire. -/
theorem brW_ok {p : Prog} (hP : RecsProg p) {vis : Word} {fe : IFEnv} {n : Nat} {m m' : Mem}
    {a : AState} {pp rc q : Word} {bs : BlockShape} {rs : RecShape}
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hrs : DecB (fun m => decRS m rc.toNat) m rs) (h : brW p n m pp rc = some (q, m')) :
    ∃ f a', (ConRon.Arena.recFire bs rs).run a = .ok (f, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat =
        some (.recInfo rs.cvR rs.mI rs.rP rs.isK (rs.rules.map fun rl => { rl with fire := f })) := by
  rcases n with _ | n
  · simp [brW] at h
  simp only [brW] at h
  rcases h1 : rfW p n m pp rc with _ | ⟨r1, m1⟩ <;> rw [h1] at h
  · simp [brW.k_rec_fire] at h
  obtain ⟨f, a1, hrun1, hS1, hg1, hdf⟩ := rfW_ok hP.toFireProg hS hq hrs h1
  simp only [brW.k_rec_fire] at h
  -- the fire's two slices, as `IW` handle slices of `m1`
  obtain ⟨lvH, psH, hlv, hps, hFire⟩ : ∃ (lvH : List LIdx) (psH : List EIdx),
      (decHL m1 (r1.tail.headD 0).toNat (r1.tail.tail.headD 0).toNat = some lvH ∧
        (r1.tail.headD 0).toNat + (r1.tail.tail.headD 0).toNat ≤ iwTop m1) ∧
      (decHL m1 (r1.tail.tail.tail.headD 0).toNat (r1.tail.tail.tail.tail.headD 0).toNat = some psH ∧
        (r1.tail.tail.tail.headD 0).toNat + (r1.tail.tail.tail.tail.headD 0).toNat ≤ iwTop m1) ∧
      ∀ R : Nat → Option Word, ∀ elo epo : Word, hslice? R elo.toNat (r1.tail.tail.headD 0).toNat = some lvH →
        hslice? R epo.toNat (r1.tail.tail.tail.tail.headD 0).toNat = some psH →
        FireAt R (r1.headD 0) elo (r1.tail.tail.headD 0) epo (r1.tail.tail.tail.tail.headD 0) f := by
    cases f with
    | plain =>
      have hr : r1 = [0, 0, 0, 0, 0] := hdf
      subst hr
      exact ⟨[], [], ⟨by simp [decHL, hslice?], by simp⟩, ⟨by simp [decHL, hslice?], by simp⟩,
        fun _ _ _ _ _ => rfl⟩
    | nested lv ps =>
      obtain ⟨h0, ⟨hl1, hl2⟩, ⟨hp1, hp2⟩⟩ := hdf
      simp only [Nat.reduceAdd, getD1_eq, getD2_eq, getD3_eq, getD4_eq] at hl1 hl2 hp1 hp2
      exact ⟨lv, ps, ⟨hl1, hl2⟩, ⟨hp1, hp2⟩, fun R elo epo h1 h2 => ⟨h0, h1, h2⟩⟩
    | levels _ => exact hdf.elim
  rcases h2 : efF n m1 (r1.tail.headD 0) (r1.tail.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [h2] at h
  · simp [brW.k_er_from_iw] at h
  obtain ⟨hS2, hg2, hl2, hsl2⟩ := efF_stage h2 hS1 hlv.1 hlv.2
  simp only [brW.k_er_from_iw] at h
  rcases h3 : efF n m2 (r1.tail.tail.tail.headD 0) (r1.tail.tail.tail.tail.headD 0) with _ | ⟨r3, m3⟩ <;>
    rw [h3] at h
  · simp [brW.k_er_from_iw_2] at h
  obtain ⟨hS3, hg3, hl3, hsl3⟩ := efF_stage h3 hS2 (by rw [decHL_grow hg2 hps.2]; exact hps.1)
    (by have := hg2.iw; omega)
  simp only [brW.k_er_from_iw_2] at h
  have hg03 : IWGrow m m3 := hg1.trans (hg2.trans hg3)
  -- the recursor's words
  have hrs0 : decRS (truncM m) rc.toNat = some rs := hrs
  obtain ⟨⟨aw, haw, hcv⟩, hrP, hmI, -, ⟨o, c, ho, hc, hru⟩, hisK⟩ := decRS_some hrs0
  obtain ⟨hcW, hc5⟩ := iwRd (o := rc) (w := 5) (by simpa using hc)
  obtain ⟨hoW, ho4⟩ := iwRd (o := rc) (w := 4) (by simpa using ho)
  obtain ⟨hmIW, hm2⟩ := iwRd (o := rc) (w := 2) (by simpa using hmI)
  obtain ⟨hrPW, hr1⟩ := iwRd (o := rc) (w := 1) (by simpa using hrP)
  have hisKW := rdW_of_iwB (o := rc) (w := 6) (by simpa using hisK)
  obtain ⟨cw, hcw, hcwv, hcwlt⟩ := rdW_of_iwN_truncM haw
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have l5 : (rc + 5).toNat < iwTop m := by rw [UInt64.toNat_add]; simp at hc5 ⊢; omega
  rw [rdWIW_grow hg03 l5] at h
  by_cases hbig : 4294967296 ≤ rdW (m.arr64 IW) (rc + 5)
  · rw [ite_eq_left hbig] at h; cases h
  rw [ite_eq_right hbig] at h
  have hc32 : (rdW (m.arr64 IW) (rc + 5)).toNat < 2 ^ 32 := by
    have : ¬ _ := fun c => hbig (UInt64.le_iff_toNat_le.mpr c); simp at this; omega
  rcases h4 : erAllocW m3 (11 * rdW (m.arr64 IW) (rc + 5)) with _ | ⟨run, m4⟩ <;> rw [h4] at h
  · simp [brW.k_erec_alloc] at h
  simp only [brW.k_erec_alloc] at h
  obtain ⟨-, hf4, -⟩ := erAllocW_spec h4 hS3.iw
  have hI4 : m4.arr64 IW = m3.arr64 IW := hf4.arr IW (by simp) (by decide)
  have l4 : (rc + 4).toNat < iwTop m := by rw [UInt64.toNat_add]; simp at ho4 ⊢; omega
  rw [hI4, rdWIW_grow hg03 l4] at h
  rcases h5 : rrW n m4 run (rdW (m.arr64 IW) (rc + 4)) (rdW (m.arr64 IW) (rc + 5)) (r1.headD 0) (r2.headD 0)
    (r2.tail.headD 0) (r3.headD 0) (r3.tail.headD 0) with _ | ⟨r5, m5⟩ <;> rw [h5] at h
  · simp [brW.k_rules_refire] at h
  simp only [brW.k_rules_refire] at h
  have hru' : decRules (erecP m3) (rdW (m.arr64 IW) (rc + 4)).toNat (rdW (m.arr64 IW) (rc + 5)).toNat =
      some rs.rules := by
    rw [hoW, hcW]
    have e : decRules (erA (truncM m)) o c = some rs.rules := hru
    rw [truncM_erA] at e
    exact (IWGrow.ext hg03).decRules e
  rw [hl2, hl3] at h5
  obtain ⟨hS5, hg5, hdr5⟩ := rrW_ok h4 hS3 hc32 hru'
    (hFire _ _ _ ((IWGrow.ext hg3).hslice? hsl2) hsl3) h5
  have hg05 : IWGrow m m5 := hg03.trans hg5
  have l6 : (rc + 6).toNat < iwTop m := by
    have := (decRS_some hrs0).2.2.2.2.2
    simp only [iwB, bool?, Option.map_eq_some_iff] at this
    obtain ⟨x, hx, -⟩ := this
    have := (truncM_iw_get hx).1
    rw [UInt64.toNat_add]; simp; omega
  have l2 : (rc + 2).toNat < iwTop m := by rw [UInt64.toNat_add]; simp at hm2 ⊢; omega
  have l1 : (rc + 1).toNat < iwTop m := by rw [UInt64.toNat_add]; simp at hr1 ⊢; omega
  rw [rdWIW_grow hg05 hcwlt, rdWIW_grow hg05 l2, rdWIW_grow hg05 l1, rdWIW_grow hg05 l6, hcw] at h
  have hcv5 : decCV (erecP m5) cw.toNat = some rs.cvR := by
    rw [hcwv]; exact (IWGrow.ext hg05).decCV (decCVp_truncM hcv)
  obtain ⟨hS6, hg6, hci⟩ := riRec_stage h hS5 hcv5 hdr5
  refine ⟨f, a1, hrun1, hS6, hg05.trans hg6, ?_⟩
  rw [hci, hmIW, hrPW, hisKW]

/-! ## `block_recs` -/

mutual
/-- **The model of `block_recs(p, ro, rl)`** at exec fuel `n`. -/
def dbrsW (p : Prog) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, pp, ro, rl =>
    if rl = 0 then some ([0, 0], m)
    else brsK1 p n pp ro rl (callW p n "block_rec" [pp, rdW (m.arr64 IW) ro] m)
/-- After the record: the rest, then the consing. -/
def brsK1 (p : Prog) (n : Nat) (pp ro rl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bfgK3 p n (r.headD 0) (dbrsW p n m pp (ro + 1) (rl - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp ro rl : Word) (r : List Word)
theorem brsW_nil (h : rl = 0) : dbrsW p (n + 1) m pp ro rl = some ([0, 0], m) := by simp [dbrsW, h]
theorem brsW_cons (h : rl ≠ 0) : dbrsW p (n + 1) m pp ro rl =
    brsK1 p n pp ro rl (callW p n "block_rec" [pp, rdW (m.arr64 IW) ro] m) := by simp [dbrsW, h]
theorem brsK1_some : brsK1 p n pp ro rl (some (r, m)) =
    bfgK3 p n (r.headD 0) (dbrsW p n m pp (ro + 1) (rl - 1)) := by simp [brsK1]
end arms
attribute [ind_grind] brsW_nil brsW_cons brsK1_some

theorem dbrs_spec {p : Prog} (hP : RecsProg p) (n : Nat) :
    ∀ (s₀ : St) (pp ro rl : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_recs" [pp, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ dbrsW p n s₀.mem pp ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ pp ro rl; rw [invoke_eq _ hP.brs]; simp only [callFn, blockRecs]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ pp ro rl
    rw [invoke_eq _ hP.brs]
    simp only [callFn, blockRecs]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "block_rec", callW_spec p n "sl_cons", ih] <;>
      finish (gen := 20) [rdW_eq]

/-- `block_rec`'s run, as its model. -/
theorem brCall {p : Prog} (hP : RecsProg p) {n : Nat} {m m' : Mem} {pp rc : Word} {r : List Word}
    (h : callW p n "block_rec" [pp, rc] m = some (r, m')) : brW p n m pp rc = some (r.headD 0, m') := by
  obtain ⟨s', rfl, -, hK⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (br_spec p hP n _ pp rc) h
  exact hK

/-- **`block_recs` refines `blockRecs`**: an `IW` slice of `EREC` constant records below the
pool's top. -/
theorem brsW_ok {p : Prog} (hP : RecsProg p) (pp : Word) (bs : BlockShape) (vis : Word) (fe : IFEnv)
    (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (ro rl : Word) (rcs : List RecShape) (r : List Word),
    StageR vis fe m a → DecB (fun m => decBS m pp.toNat) m bs → PSlR0 decRS rcs ro rl m →
    dbrsW p n m pp ro rl = some (r, m') →
    ∃ cis a', (ConRon.Arena.blockRecs bs rcs).run a = .ok (cis, a') ∧
      decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some cis ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' a ro rl rcs r _ _ _ h; simp [dbrsW] at h
  | succ n ih =>
  intro m m' a ro rl rcs r hS hq hrcs h
  by_cases hl : rl = 0
  · rw [brsW_nil p n m pp ro rl hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : rcs = [] := by
      have h := hrcs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨[], a, rfl, by simp [decPL], by simp, hS, IWGrow.refl m⟩
  obtain ⟨q, rc, rest, rfl, hw, hqb, hdrc, hrest⟩ := partsPSl_cons ⟨hrcs.1, hrcs.2.resolve_left hl⟩ hl
  rw [brsW_cons p n m pp ro rl hl, hw] at h
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [brsK1])
  rw [brsK1_some] at h
  obtain ⟨f, a1, hrun1, hS1, hg1, hci⟩ := brW_ok hP hS hq (by rw [hq']; exact hdrc) (brCall hP h1)
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bfgK3])
  obtain ⟨cis, a3, hrun3, hd3, hb3, hS3, hg3⟩ := ih m1 m3 a1 (ro + 1) (rl - 1) rest r3 hS1
    (hq.grow (decBS_mono _) hg1) (PSlR0.grow decRS_mono ⟨hrest.dec, Or.inr hrest.bound⟩ hg1) h3
  rw [bfgK3_some] at h
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bfgK4])
  rw [bfgK4_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hd5, hb5, hS5, hg5⟩ := consW_ci (consCall hP.toFormersProg h4) hS3 hb3 hd3 (hg3.ext.decCI hci)
  refine ⟨_ :: cis, a3, ?_, by simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega, hS5,
    hg1.trans (hg3.trans hg5)⟩
  simp only [ConRon.Arena.blockRecs, StateT.run_bind, hrun1, except_ok_bind, hrun3]
  rfl

end L.Ind

end
