import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.KnotEntry
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.CrOKFrame
import ConRon.Bridge.Checker.Hyp

/-!
# `check_value_group` under `StageT` (lane `loopt2`)

`check_value_group`'s pieces under `StageT` (its refinement, `cvg_ref`, is in
`Verdict/DeclValE.lean`): the theorem test's prefix, `iw_reset`, and `install_value_guards`
(`ivgW_okT`) with the program's own calls (`realCall p`): the pool writers by their frames
(`StageT.of_iw`), the value guards' walks by their real refinements (`apdF_okT`, `crfF_okT`;
helper `indproofs4-sw2`).
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- `loose_bvars_bounded_fast`'s twin run keeps the store (it changes the per-call memos only). -/
theorem lbbF_store {f k : Nat} {e : EIdx} {a a' : AState} {x : Bool}
    (h : (looseBVarsBoundedFast f k e).run a = .ok (x, a')) : a'.store = a.store := by
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_bvarB_sp _ _) fun _ => Keeps.pure _) x a' h
  rfl

/-- `has_fvar_fast`'s twin run keeps the store. -/
theorem hffF_store {f : Nat} {e : EIdx} {a a' : AState} {x : Bool}
    (h : (hasFvarFast f e).run a = .ok (x, a')) : a'.store = a.store := by
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_fvarB_sp _ _) fun _ => Keeps.pure _) x a' h
  rfl

/-- **`install_value_guards` under `StageT`** (the statement `ivgW_okT` proves). -/
def IvgT (p : Prog) : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q v : Word} {r : List Word} {cv : IConstantVal},
    ivgW (realCall p) n m vis q v = some (r, m') → StageT dn vis fe m a →
    decCV (erA m) q.toNat = some cv → q.toNat + 3 < 2 ^ 64 → v.toNat < 2 ^ 32 →
    (∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) → L.Stubs.CrOK m →
    ∃ a', (installValueGuards fe cv (decI v)).run a = .ok ((), a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ L.Stubs.CrOK m'

/-- **`install_value_guards` under `StageT`** (`ivgW_ok`'s): the copy by its frame
(`StageT.of_iw`), the four walks by their `StageT` refinements: `all_level_params_defined` by
`apdF_okT` (the parameters' names read back at the entry, the walks before it keeping the twin's
store), `consts_resolve_ffast` by `crfF_okT` (its memo `CrOK` carried across the copy and the walks
by their frames). -/
theorem ivgW_okT {p : Prog} (hap : ApdF p) (hkp : CrKeep p) : IvgT p := by
  intro dn vis fe a n m m' q v r cv h hS hq hqb hv hlps hCr
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq
  have e1 : rdW (m.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (L.Ind.hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => simp [ivgW] at h
  | succ n =>
  cases n with
  | zero => simp [ivgW, cvLpsW, ivgK1] at h
  | succ n =>
  rw [ivgW_step, cvLpsW_step, e1, e2] at h
  cases h1 : erToIwW n m w1 w2 with
  | none => rw [h1] at h; simp [ivgK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ivgK1_some] at h
  obtain ⟨-, hr1t, hdec1, hS1R, hg1, htop1⟩ := erToIwW_stage h1 hS.stage hsrc
  have hS1 := StageT.of_iw hS hS1R (erToIwW_frame h1 hS.stage hsrc)
  have hCr1 := CrOK.frame hCr (erToIwW_frame h1 hS.stage hsrc) (by decide) (by decide)
  cases h2 : lbbF m1 [4000000000, 0, v] with
  | none => rw [h2] at h; simp [ivgK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, ivgK2_some] at h
  have hCr2 := CrOK.frame hCr1 (lbbF_frame h2) (by decide) (by decide)
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ :=
    lbbF_okT dn vis fe 4000000000 0 v hv m1 m2 a r2 h2 hS1
  by_cases hb2 : r2.headD 0 = 0
  · rw [ite_eq_left hb2] at h; simp at h
  rw [ite_eq_right hb2] at h
  cases h3 : hffF m2 [4000000000, v] with
  | none => rw [h3] at h; simp [ivgK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, ivgK3_some] at h
  have hCr3 := CrOK.frame hCr2 (hffF_frame h3) (by decide) (by decide)
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    hffF_okT dn vis fe 4000000000 v hv m2 m3 a2 r3 h3 hS2
  by_cases hb3 : r3.headD 0 ≠ 0
  · rw [ite_eq_left hb3] at h; simp at h
  rw [ite_eq_right hb3] at h
  rw [hr1t] at h
  cases h4 : realCall p (n + 1) "all_level_params_defined" [r1.headD 0, w2, v] m3 with
  | none => rw [h4] at h; simp [ivgK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, ivgK4_some] at h
  have hdec3 : decHL m3 (r1.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg2.trans hg3) (by omega), hdec1]; exact hsl
  have hst3 : a3.store = a.store := (hffF_store hrun3).trans (lbbF_store hrun2)
  have hCr4 := CrOK.frame hCr3 (apdF_frame (apdF_of_callW hap h4)) (by decide) (by decide)
  obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
    apdF_okT dn vis fe (r1.headD 0) w2 v hv cv.levelParams m3 m4 a3 r4 (apdF_of_callW hap h4)
      ⟨hS3, hdec3, by rw [hst3]; exact hlps⟩
  by_cases hb4 : r4.headD 0 = 0
  · rw [ite_eq_left hb4] at h; simp at h
  rw [ite_eq_right hb4] at h
  cases h5 : realCall p (n + 1) "consts_resolve_ffast" [vis, v] m4 with
  | none => rw [h5] at h; simp [ivgK5] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, ivgK5_some] at h
  obtain ⟨x5, a5, hrun5, ⟨hS5, hg5, hx5, -⟩, hCr5⟩ :=
    crfF_okT dn vis fe v hv m4 m5 a4 r5 (crfF_of_callW hkp.crf h5) ⟨hS4, hCr4.crMemo⟩
  by_cases hb5 : r5.headD 0 = 0
  · rw [ite_eq_left hb5] at h; simp at h
  rw [ite_eq_right hb5] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have ex2 : x2 = true := by rw [← hx2]; simpa using hb2
  have ex3 : x3 = false := by rw [← hx3]; simpa using hb3
  have ex4 : x4 = true := by rw [← hx4]; simpa using hb4
  have ex5 : x5 = true := by rw [← hx5]; simpa using hb5
  rw [fuelW] at hrun2 hrun3
  refine ⟨a5, ?_, hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hCr5.crOK⟩
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun2
  simp only [installValueGuards, StateT.run_bind, hrun2, exc_ok_bind', ex2, hrun3, ex3, hrun4,
    ex4, hrun5, ex5, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure]
  rfl

/-- The memory after `iw_reset` keeps `StageT`. -/
theorem iwReset_stageT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hT : StageT dn vis fe m a) : StageT dn vis fe (m.set64 CTL 200 0) a :=
  StageT.of_iw hT (iwReset_stage hT.stage).1
    (MemFrame.mono (MemFrame.setCtl m 200 0) (by simp) (by simp))

/-- **The theorem test's prefix extends the twin's store** (con-ron's `KnotSpec.infer` and
`EnsureSortSpec`, as in `checkValueGroup_bridge`): from `CheckOK` and the constant's type denoting
in scope. -/
theorem thmPrefix_ext {env : ConLeche.Env} {fe : IFEnv} {a a1 a2 : AState} {cv : IConstantVal}
    {cP : ConLeche.ConstantVal} {x1 : EIdx} {x2 : LIdx} (henv : ConLeche.EnvWF env)
    (hck : ConRon.Bridge.CheckOK V env fe a) (hcv : Frontend.denoteCV a.store cv = some cP)
    (hws : ConLeche.Expr.WScoped 0 cP.type)
    (h1 : (inferTypeCore V fe checkFuel 0 cv.type).run a = .ok (x1, a1))
    (h2 : (ensureSortCore V fe checkFuel 0 x1).run a1 = .ok (x2, a2)) :
    ConRon.Bridge.CheckOK V env fe a2 ∧ Ext a.store a2.store := by
  obtain ⟨-, -, hty0⟩ := ConRon.Bridge.Core.denoteCV_inv hcv
  obtain ⟨hcka, hxa, -, sty, hsty, hwssty, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a) rfl h1
    (((ConRon.Bridge.CoreSpec.of_core rfl).knot env fe henv).infer a 0 cv.type cP.type hck hty0 hws)
  obtain ⟨hckb, hxb, -, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a1) rfl h2
    (((ConRon.Bridge.CoreSpec.of_core rfl).sort env fe henv) a1 0 x1 sty hcka hsty hwssty)
  exact ⟨hckb, hxa.trans hxb⟩

end L.Arena
