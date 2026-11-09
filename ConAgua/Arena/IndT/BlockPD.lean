module

public import ConAgua.Arena.IndT.BlockC
public import ConAgua.Arena.IndMaster
public import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndDeclConstsTable
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndDeclConsts

@[expose] public section

/-!
# `ifenv_push_delta`'s contract (lane `ronsync2`, stage 3)

`ifenv_push_delta(vis, L.off, L.len, Q.off, Q.len)` (`IndDeclConsts.lean`): `ifenv_push_all`
(`env_push` per record: `envPush_stage`) then `ifenv_push_tables` (`env_push_table` per table:
`envPushTable_stageE`, the stage relation by the frame of `tblSet` as `StageR.of_own`'s by
`ownSet`'s). The memories' facts by the environment rows' frame (arrays `140‥148`, `BkMem.ofEnv`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true

namespace L.Ind

open L.Arena

/-! ## The environment rows' frame -/

/-- **`BkMem` across a writer of the environment's rows only** (arrays `140‥148`). -/
theorem BkMem.ofEnv {A : List TieredArray} {m m' : Mem} (h : BkMem m) (hf : MemFrame A [] m m')
    (hA : ∀ b ∈ A, 140 ≤ b.arr ∧ b.arr ≤ 148) : BkMem m' := by
  have nm : ∀ (x : TieredArray), (x.arr < 140 ∨ 148 < x.arr) → x ∉ A := fun x hx h' => by
    have := hA x h'; omega
  refine ⟨h.ind.frame hf (fun b hb => ⟨fun e => ?_, fun e => ?_, by have := hA b hb; omega⟩)
      (fun x hx => by simp at hx),
    CoreMemos.frame hf ⟨nm _ (by decide), nm _ (by decide)⟩ (by simp) h.core
      ⟨nm _ (by decide), nm _ (by decide), nm _ (by decide)⟩ (by simp)
      ⟨nm _ (by decide), nm _ (by decide), nm _ (by decide)⟩ (by simp),
    AFr.of_frame hf ?_ (by decide) h.abs⟩
  · subst e; have := hA _ hb; revert this; decide
  · subst e; have := hA _ hb; revert this; decide
  · simp only [memoFreeA, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    intro b hb
    have := hA b hb
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      (intro e; subst e; revert this; decide)

/-- **The stage relation across a writer of the environment's rows**, at the environment its
`EnvR` gives (`StageR.of_own`'s, for any such frame). -/
theorem StageR.of_envFrame {vis vis' : Word} {fe fe' : IFEnv} {a : AState} {m m' : Mem}
    {A : List TieredArray} (hS : StageR vis fe m a) (hf : MemFrame A [] m m')
    (hA : ∀ b ∈ A, 140 ≤ b.arr ∧ b.arr ≤ 148) (hE : EnvR m' vis' fe') :
    StageR vis' fe' m' a ∧ IWGrow m m' := by
  have hlow : ∀ y ∈ arenaArrs, y.arr < 64 := by decide
  have hA3 : (IW : TieredArray) ∉ A ∧ (EREC : TieredArray) ∉ A ∧ tier1 EREC ∉ A :=
    ⟨fun h => by have := hA _ h; revert this; decide, fun h => by have := hA _ h; revert this; decide,
      fun h => by have := hA _ h; revert this; decide⟩
  have hC3 : (129 : Word) ∉ ([] : List Word) ∧ (130 : Word) ∉ ([] : List Word) ∧
      (200 : Word) ∉ ([] : List Word) := by simp
  refine ⟨⟨⟨⟨ArenaR.frame (fun b hb hm => by have := hlow b hm; have := hA b hb; omega)
      (fun x hx => by simp at hx) hf hS.check.arena.base,
      DerR.frameM _ _ m _ hf (fun b hb => by have := hA b hb; omega) a hS.check.arena.der⟩,
    hS.check.core.frame (fun b hb => .inr (by have := hA b hb; omega)) (fun x hx => by simp at hx) hf,
    hS.check.pins.frame (fun b hb => .inr (by have := hA b hb; omega)) hf, hE,
    hS.check.mode.frame hf (by simp) (by simp)⟩, IWOK.of_keep hf hA3 hC3 hS.iw⟩,
    IWGrow.of_keep hf hA3 hC3⟩

theorem tblSet_frame (m : Mem) (w v : Word) : MemFrame [otxArrT w] [] m (tblSet m w v) := by
  have hne : otxArrT w ≠ CTL := fun e => by have := otxArrT_arr w; rw [e] at this; revert this; decide
  unfold tblSet
  exact (MemFrame.set64 _ _ hne _ _).trans (MemFrame.set64 _ _ hne _ _)

theorem otx_rng (w : Word) : ∀ b ∈ [otxArrT w], 140 ≤ b.arr ∧ b.arr ≤ 148 := by
  intro b hb; simp only [List.mem_singleton] at hb; subst hb; have := otxArrT_arr w; omega

theorem own_rng (w : Word) : ∀ b ∈ [ownArr w], 140 ≤ b.arr ∧ b.arr ≤ 148 := by
  intro b hb; simp only [List.mem_singleton] at hb; subst hb; have := ownArr_arr w; omega

/-- **`env_push_table` under the stage relation.** -/
theorem envPushTable_stageE {p : Prog} (hs : p.lookup "tbl_own_set" = some tblOwnSetL)
    (hpu : p.lookup "env_push_table" = some envPushTableL) {n : Nat} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {q : Word} {r : List Word} {t : IProjTable}
    (hc : callW p n "env_push_table" [q] m = some (r, m')) (hS : StageR vis fe m a)
    (ht : decTbl (erecP m) q.toNat = some t) :
    StageR vis (fe.pushTable t) m' a ∧ IWGrow m m' ∧
      ∃ w v, m' = tblSet m w v := by
  obtain ⟨s', hs', -, hE, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPushTable_refines p hs hpu n ⟨m, Locals.init []⟩ vis q hS.check.env ht) hc
  simp only at hs' hE hm
  subst hs'
  rw [hm] at hE ⊢
  exact ⟨(StageR.of_envFrame hS (tblSet_frame _ _ _) (otx_rng _) hE).1,
    (StageR.of_envFrame hS (tblSet_frame _ _ _) (otx_rng _) hE).2, _, _, rfl⟩

/-- **`env_push` under the stage relation**, its memory an `ownSet`. -/
theorem envPush_stageE {p : Prog} (hrs : p.lookup "env_row_set" = some envRowSetL)
    (hpu : p.lookup "env_push" = some envPushL) {n : Nat} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {c : Word} {r : List Word} {ci : IConstantInfo}
    (hc : callW p n "env_push" [vis, c] m = some (r, m'))
    (hS : StageR vis fe m a) (hci : decCI (erecP m) c.toNat = some ci) :
    StageR (r.headD 0) (fe.push ci) m' a ∧ IWGrow m m' ∧ ∃ w c' q, m' = ownSet m w c' q := by
  obtain ⟨s', hs', -, hr, hE, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPush_refines p hrs hpu n ⟨m, Locals.init []⟩ vis c hS.check.env hci) hc
  subst hs' hr
  simp only [List.headD_cons]
  rw [hm] at hE ⊢
  exact ⟨(StageR.of_own hS hE).1, (StageR.of_own hS hE).2, _, _, _, rfl⟩

/-! ## The models -/

mutual
/-- **The model of `ifenv_push_all(vis, o, l)`** at exec fuel `n`. -/
def paW (p : Prog) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, vis, o, l =>
    if l = 0 then some ([vis], m)
    else paK1 p n o l (callW p n "env_push" [vis, rdW (m.arr64 IW) o] m)
def paK1 (p : Prog) (n : Nat) (o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (v, m) => paK2 (paW p n m (v.headD 0) (o + 1) (l - 1))
def paK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

mutual
/-- **The model of `ifenv_push_tables(o, l)`** at exec fuel `n`. -/
def ptW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if l = 0 then some ([0], m)
    else ptK1 p n o l (callW p n "env_push_table" [rdW (m.arr64 IW) o] m)
def ptK1 (p : Prog) (n : Nat) (o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ptK2 (ptW p n m (o + 1) (l - 1))
def ptK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)
end

def ipdK2 (v : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([v.headD 0], m)

def ipdK1 (p : Prog) (n : Nat) (qo ql : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (v, m) => ipdK2 v (callW p n "ifenv_push_tables" [qo, ql] m)

/-- **The model of `ifenv_push_delta(vis, lo, ll, qo, ql)`.** -/
def ipdW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, vis, lo, ll, qo, ql => ipdK1 p n qo ql (callW p n "ifenv_push_all" [vis, lo, ll] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis o l qo ql : Word) (r : List Word)
theorem paW_nil (h : l = 0) : paW p (n + 1) m vis o l = some ([vis], m) := by simp [paW, h]
theorem paW_cons (h : l ≠ 0) : paW p (n + 1) m vis o l =
    paK1 p n o l (callW p n "env_push" [vis, rdW (m.arr64 IW) o] m) := by simp [paW, h]
theorem paK1_some : paK1 p n o l (some (r, m)) = paK2 (paW p n m (r.headD 0) (o + 1) (l - 1)) := by
  simp [paK1]
theorem paK2_some : paK2 (some (r, m)) = some ([r.headD 0], m) := rfl
theorem ptW_nil (h : l = 0) : ptW p (n + 1) m o l = some ([0], m) := by simp [ptW, h]
theorem ptW_cons (h : l ≠ 0) : ptW p (n + 1) m o l =
    ptK1 p n o l (callW p n "env_push_table" [rdW (m.arr64 IW) o] m) := by simp [ptW, h]
theorem ptK1_some : ptK1 p n o l (some (r, m)) = ptK2 (ptW p n m (o + 1) (l - 1)) := by simp [ptK1]
theorem ptK2_some : ptK2 (some (r, m)) = some ([0], m) := rfl
theorem ipdW_succ : ipdW p (n + 1) m vis o l qo ql =
    ipdK1 p n qo ql (callW p n "ifenv_push_all" [vis, o, l] m) := rfl
theorem ipdK1_some : ipdK1 p n qo ql (some (r, m)) =
    ipdK2 r (callW p n "ifenv_push_tables" [qo, ql] m) := rfl
theorem ipdK2_some (v : List Word) : ipdK2 v (some (r, m)) = some ([v.headD 0], m) := rfl
end arms
attribute [ind_grind] paW_nil paW_cons paK1_some paK2_some ptW_nil ptW_cons ptK1_some ptK2_some ipdW_succ
  ipdK1_some ipdK2_some

/-- The lookups the pushes take. -/
structure PdProg (p : Prog) : Prop where
  rs : p.lookup "env_row_set" = some envRowSetL
  push : p.lookup "env_push" = some envPushL
  tos : p.lookup "tbl_own_set" = some tblOwnSetL
  pt : p.lookup "env_push_table" = some envPushTableL
  pa : p.lookup "ifenv_push_all" = some ifenvPushAll
  pts : p.lookup "ifenv_push_tables" = some ifenvPushTables
  pd : p.lookup "ifenv_push_delta" = some ifenvPushDelta

theorem pa_spec {p : Prog} (hP : PdProg p) (n : Nat) :
    ∀ (s₀ : St) (vis o l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ifenv_push_all" [vis, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ paW p n s₀.mem vis o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis o l; rw [invoke_eq _ hP.pa]; simp only [callFn, ifenvPushAll]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis o l
    rw [invoke_eq _ hP.pa]
    simp only [callFn, ifenvPushAll]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "env_push", ih] <;>
      finish (gen := 20) [rdW_eq]

theorem pt_spec {p : Prog} (hP : PdProg p) (n : Nat) :
    ∀ (s₀ : St) (o l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ifenv_push_tables" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ptW p n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o l; rw [invoke_eq _ hP.pts]; simp only [callFn, ifenvPushTables]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l
    rw [invoke_eq _ hP.pts]
    simp only [callFn, ifenvPushTables]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "env_push_table", ih] <;>
      finish (gen := 20) [rdW_eq]

theorem pd_spec {p : Prog} (hP : PdProg p) (n : Nat) (s₀ : St) (vis lo ll qo ql : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "ifenv_push_delta" [vis, lo, ll, qo, ql]
    ⦃fun r s' => LocEq s' s₀ ∧ ipdW p n s₀.mem vis lo ll qo ql = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.pd]
  simp only [callFn, ifenvPushDelta]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        callW_spec p n "ifenv_push_all", callW_spec p n "ifenv_push_tables"] <;>
      finish (gen := 20) [rdW_eq]

/-! ## The models against the twin -/

theorem pa_ok {p : Prog} (hP : PdProg p) {a : AState} (n : Nat) :
    ∀ (m m' : Mem) (vis o l : Word) (fe : IFEnv) (cis : List IConstantInfo) (r : List Word),
    paW p n m vis o l = some (r, m') → StageR vis fe m a → BkMem m →
    decPL m (decCI (erecP m)) o.toNat l.toNat = some cis → o.toNat + l.toNat ≤ iwTop m →
    StageR (r.headD 0) (IFEnv.pushAll cis fe) m' a ∧ BkMem m' ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' vis o l fe cis r h; simp [paW] at h
  | succ n ih =>
  intro m m' vis o l fe cis r h hS hM hd hb
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases hl : l = 0
  · rw [paW_nil p n m vis o l hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : cis = [] := by subst hl; simpa [decPL] using hd.symm
    subst this
    exact ⟨hS, hM, IWGrow.refl m⟩
  rw [paW_cons p n m vis o l hl] at h
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 :=
    ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  rw [hL] at hd
  cases cis with
  | nil => have := decPL_length _ hd; simp at this
  | cons ci cis =>
  obtain ⟨pv, hpv, hci⟩ := decPL_head hd
  have htl := decPL_tail hd
  have hrd : (rdW (m.arr64 IW) o).toNat = pv := by
    simp only [iwN, nat?, iwA, aread_apply, Option.map_eq_some_iff] at hpv
    obtain ⟨w, hw, rfl⟩ := hpv
    simp only [rdW, hw, Option.getD_some]
  rcases h1 : callW p n "env_push" [vis, rdW (m.arr64 IW) o] m with _ | ⟨v, m1⟩
  · rw [h1] at h; simp [paK1] at h
  rw [h1, paK1_some] at h
  obtain ⟨hS1, hg1, w, c, q, hm1⟩ := envPush_stageE hP.rs hP.push h1 hS (by rw [hrd]; exact hci)
  have hM1 : BkMem m1 := by rw [hm1]; exact hM.ofEnv (ownSet_frame _ _ _ _) (own_rng _)
  rcases h2 : paW p n m1 (v.headD 0) (o + 1) (l - 1) with _ | ⟨r2, m2⟩
  · rw [h2] at h; simp [paK2] at h
  rw [h2, paK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = L := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  have htl' : decPL m1 (decCI (erecP m1)) (o + 1).toNat (l - 1).toNat = some cis := by
    rw [ho1, hl1]; exact decPL_ci_grow hg1 (by omega) htl
  obtain ⟨hS2, hM2, hg2⟩ := ih m1 m2 (v.headD 0) (o + 1) (l - 1) _ cis r2 h2 hS1 hM1 htl'
    (by rw [ho1, hl1]; have := hg1.iw; omega)
  exact ⟨by simpa [IFEnv.pushAll] using hS2, hM2, hg1.trans hg2⟩

theorem pt_ok {p : Prog} (hP : PdProg p) {a : AState} {vis : Word} (n : Nat) :
    ∀ (m m' : Mem) (o l : Word) (fe : IFEnv) (ts : List IProjTable) (r : List Word),
    ptW p n m o l = some (r, m') → StageR vis fe m a → BkMem m →
    decPL m (decTbl (erecP m)) o.toNat l.toNat = some ts → o.toNat + l.toNat ≤ iwTop m →
    StageR vis (IFEnv.pushTables ts fe) m' a ∧ BkMem m' ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' o l fe ts r h; simp [ptW] at h
  | succ n ih =>
  intro m m' o l fe ts r h hS hM hd hb
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  by_cases hl : l = 0
  · rw [ptW_nil p n m o l hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : ts = [] := by subst hl; simpa [decPL] using hd.symm
    subst this
    exact ⟨hS, hM, IWGrow.refl m⟩
  rw [ptW_cons p n m o l hl] at h
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 :=
    ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  rw [hL] at hd
  cases ts with
  | nil => have := decPL_length _ hd; simp at this
  | cons t ts =>
  obtain ⟨pv, hpv, hti⟩ := decPL_head hd
  have htl := decPL_tail hd
  have hrd : (rdW (m.arr64 IW) o).toNat = pv := by
    simp only [iwN, nat?, iwA, aread_apply, Option.map_eq_some_iff] at hpv
    obtain ⟨w, hw, rfl⟩ := hpv
    simp only [rdW, hw, Option.getD_some]
  rcases h1 : callW p n "env_push_table" [rdW (m.arr64 IW) o] m with _ | ⟨v, m1⟩
  · rw [h1] at h; simp [ptK1] at h
  rw [h1, ptK1_some] at h
  obtain ⟨hS1, hg1, w, c, hm1⟩ := envPushTable_stageE hP.tos hP.pt h1 hS (by rw [hrd]; exact hti)
  have hM1 : BkMem m1 := by rw [hm1]; exact hM.ofEnv (tblSet_frame _ _ _) (otx_rng _)
  rcases h2 : ptW p n m1 (o + 1) (l - 1) with _ | ⟨r2, m2⟩
  · rw [h2] at h; simp [ptK2] at h
  rw [h2, ptK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = L := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  have htl' : decPL m1 (decTbl (erecP m1)) (o + 1).toNat (l - 1).toNat = some ts := by
    rw [ho1, hl1]; exact decPL_tbl_grow hg1 (by omega) htl
  obtain ⟨hS2, hM2, hg2⟩ := ih m1 m2 (o + 1) (l - 1) _ ts r2 h2 hS1 hM1 htl'
    (by rw [ho1, hl1]; have := hg1.iw; omega)
  exact ⟨by simpa [IFEnv.pushTables] using hS2, hM2, hg1.trans hg2⟩

/-- **`ifenv_push_delta`'s contract.** -/
theorem pdRefS_of {G : Prop} {p : Prog} (hP : PdProg p)
    (hGnv : G → closedNV p _root_.L.Checker.nvFns = true) : PdRefS G p := by
  intro n vis fe m a lo ll qo ql cis ts hS hM hdc hbc hdt hbt
  rcases c : callE p n "ifenv_push_delta" [vis, lo, ll, qo, ql] m with e | ⟨r, m'⟩
  · exact fun hG => ErrClaim.of_callE_nv (hGnv hG) (_root_.L.Checker.nv_mem (by decide +kernel)) c
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pd_spec hP n _ vis lo ll qo ql) (callW_of_callE c)
  rcases n with _ | n
  · simp [ipdW] at hW
  rw [ipdW_succ] at hW
  rcases h1 : callW p n "ifenv_push_all" [vis, lo, ll] m with _ | ⟨v, m1⟩
  · rw [h1] at hW; simp [ipdK1] at hW
  rw [h1, ipdK1_some] at hW
  rcases h2 : callW p n "ifenv_push_tables" [qo, ql] m1 with _ | ⟨u, m2⟩
  · rw [h2] at hW; simp [ipdK2] at hW
  rw [h2, ipdK2_some] at hW
  obtain ⟨rfl, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (pa_spec hP n _ vis lo ll) h1
  obtain ⟨hS1, hM1, hg1⟩ := pa_ok hP n _ _ _ _ _ fe cis v hW1 hS hM hdc hbc
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩) (pt_spec hP n _ qo ql) h2
  obtain ⟨hS2, hM2, hg2⟩ := pt_ok hP (vis := v.headD 0) n _ _ _ _ _ ts u hW2 hS1 hM1
    (decPL_tbl_grow hg1 hbt hdt) (Nat.le_trans hbt hg1.iw)
  rw [← hm]
  exact ⟨(), a, rfl, rfl, by simpa [IFEnv.pushDelta] using hS2, hM2, hg1.trans hg2⟩

end L.Ind

end
