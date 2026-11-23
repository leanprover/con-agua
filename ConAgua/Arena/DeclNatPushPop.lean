module

public import ConAgua.Arena.IndInstallSpec.PapW
public import ConAgua.Arena.StageFlags
import all ConAgua.Arena.Env

@[expose] public section

/-!
# A temporary push, popped (lane `ronsync2`, stage 3)

The definition arm's two gates (`check_structural_nat_pin`, `check_div_mod_pin`) read the
environment with the checked record pushed and pop it again: `env_row_get(n)` reads the own row
the push displaces, `env_push(vis, p)` pushes, the reads run at the pushed view, and
`env_pop_temp(w, n, c, q)` puts the row back (the twin's `fe.push ci`, then
`(fe.push ci).popTemp ci.name fe.idx[ci.name]?`, `IFEnv.popTemp`). `pushPop_stage` is the stage
relation across the pair, at any memory in between that kept the own rows.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **A push popped**: from the stage relation at `vis` before the push of record `pw` (name `nw`),
and the stage relation at the pushed view after reads that kept the own rows, `env_pop_temp` with
the own row read before the push gives the stage relation at `vis` of the twin's popped index. -/
theorem pushPop_stage {p : Prog} (hP : EnvFlagsProg p)
    (hpt : p.lookup "env_pop_temp" = some envPopTempL)
    {k k' : Nat} {vis pw nw : Word} {fe : IFEnv} {a a2 : AState} {m m1 m2 m3 : Mem}
    {ci : IConstantInfo} {r1 r3 : List Word}
    (hS : StageR vis fe m a) (hci : decCI (erecP m) pw.toNat = some ci) (hnm : ci.name = decI nw)
    (hn : nw.toNat < 2 ^ 32)
    (h1 : callW p k "env_push" [vis, pw] m = some (r1, m1))
    (hS2 : StageR (r1.headD 0) (fe.push ci) m2 a2) (hg : IWGrow m m2) (hO : ownC m2 = ownC m1)
    (h3 : callW p k' "env_pop_temp" [r1.headD 0, nw, (ownRaw m nw).1, (ownRaw m nw).2] m2 =
      some (r3, m3)) :
    StageR (r3.headD 0) ((fe.push ci).popTemp ci.name fe.idx[ci.name]?) m3 a2 ∧ IWGrow m2 m3 ∧
      r3.headD 0 = vis := by
  have hE := hS.check.env
  have hwn : (decI nw : NIdx).word.toUInt64 = nw := decI_word_self nw hn
  obtain ⟨hO1, hr1, hv1⟩ := envPush_ownC hP h1 hE hci (by have := hS.iw.ctl; omega)
  have hvis1 : (vis + 1).toNat = vis.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hprev := rec3PrevD_grow hg (rec3PrevD hE hn)
  obtain ⟨hpvE, hcd⟩ := prevD_eq hprev
  have hown : ∀ n' : NIdx, (ownRaw m2 n'.word.toUInt64).1 = updC (ownC m) ci.name (vis + 1) n' := by
    intro n'; rw [← hO1, ← hO]; rfl
  have hcC : (ownRaw m nw).1 = ownC m ci.name := by rw [hnm]; simp only [ownC, hwn]
  rw [hr1, List.headD_cons] at h3 hS2
  obtain ⟨s3, hs3, -, hr3, hE3, hm3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (envPopTemp_refines p hP.rowSet hpt k' _ (vis + 1) nw (ownRaw m nw).1 (ownRaw m nw).2 hS2.check.env hn
      (fun e => by have := congrArg UInt64.toNat e; rw [hvis1] at this; simp at this)
      (by have := hown ci.name; rw [hnm, hwn] at this; rw [this]; simp [updC])
      (ownRaw_fst_lt m nw)
      (fun hc0 => by
        have := hE.fresh (decI nw) (by rw [hwn]; exact hc0)
        rw [hwn] at this; rw [hvis1]; omega)
      hcd
      (fun hc0 n' hn' e => by
        rw [hown n'] at e
        have hne : n' ≠ ci.name := fun h => hn' (by rw [h, hnm, hwn])
        simp only [updC, ite_eq_right hne] at e
        exact hne (hE.uniq n' ci.name (by simp only [ownC] at e; rw [e]; exact hc0)
          (by simp only [ownC] at e; rw [e, hcC]; rfl))))
    h3
  rw [hpvE, ← hnm, hm3] at hE3
  have hm3' : m3 = ownSet m2 nw (ownRaw m nw).1 (ownRaw m nw).2 := by rw [← hs3, hm3]
  subst hm3'
  obtain ⟨hS3, hg3⟩ := StageR.of_own hS2 hE3
  rw [hr3, List.headD_cons, show vis + 1 - 1 = vis by simp] at *
  exact ⟨hS3, hg3, rfl⟩

/-- **The flags set back after the pop** (`env_set_flags(fn, fs)`, the twin's
`.setFlags fe.natLit fe.strLit`): `fn`, `fs` the words `CTL[160]`, `CTL[161]` the gate saved
before its push, which are `fe`'s flags. -/
theorem setFlags_stage {p : Prog} (hP : EnvFlagsProg p) {k : Nat} {vis x y : Word} {fe fe' : IFEnv}
    {a : AState} {m m' : Mem} {r : List Word}
    (hS : StageR vis fe' m a) (hx : fe.natLit = (x != 0)) (hy : fe.strLit = (y != 0))
    (h : callW p k "env_set_flags" [x, y] m = some (r, m')) :
    StageR vis (fe'.setFlags fe.natLit fe.strLit) m' a ∧ IWGrow m m' ∧ m' = flagsSet m x y := by
  obtain ⟨s', hs', -, hm', hE'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envSetFlags_refines hP.setFlags k _ vis x y hS.check.env
      (show 161 < (m.arr64 CTL).size by have := hS.iw.ctl; omega)) h
  rw [← hx, ← hy] at hE'
  have e : m' = flagsSet m x y := by rw [← hs', hm']
  rw [hm'] at hE'
  subst e
  obtain ⟨h1, h2⟩ := StageR.of_flags hS hE'
  exact ⟨h1, h2, rfl⟩

/-! ## The reads at the pushed view keep the own rows -/

/-- The call closure of the two gates' reads at the pushed view (`check_structural_nat_pin_at_fe2`,
`check_div_mod_pin_at_fe2`) in the checker's program: lookups, pin reads, interning, `IW` slices. -/
def fe2Fns : List FnName :=
  ["check_div_mod_pin_at_fe2", "env_find", "base_row_get", "env_row_get", "div_mod_env_guard",
   "bool_ctor_typed", "const_e", "intern_const", "const_push", "const_find", "pin_word", "pin_at",
   "ci_to_cv", "eq_stored", "nat_op_stored_ok", "nat_op_ty_pinned",
   "nat_op_cod", "e_view", "nat_op_deps", "iw_alloc", "nat_op_pins", "nat_op_pins_c",
   "nat_op_pins_b", "nat_op_pins_a", "nat_op_guard", "nat_op_bool_ctors", "bool_ctor_ok",
   "sl_contains", "nat_div_mod_names", "nat_op_deps_stored", "nat_lit_supported", "nat_succ_ok",
   "nat_zero_ok", "nat_ind_ok", "check_structural_nat_pin_at_fe2"]

/-- The arrays `fe2Fns` may write: all but the own layer's row arrays. -/
def fe2A : List TieredArray := checkerWordArrays.filter fun b => b.arr < 140 ∨ 142 < b.arr

/-- The `CTL` words `fe2Fns` may write: all but the stamp (`CTL[133]`). -/
def fe2C : List Word := ((List.range 1024).filter fun x => x ≠ 133).map UInt64.ofNat

/-- **The program hypothesis**: the reads at the pushed view write no own row. -/
def Fe2Closed (p : Prog) : Prop := closedA p fe2A fe2C fe2Fns = true

theorem oix_arr (g : Nat) (t : UInt64) :
    140 ≤ (tierA (oixArr g) t).arr ∧ (tierA (oixArr g) t).arr ≤ 142 := by
  unfold tierA oixArr; generalize (t &&& 1 != 0) = b
  cases b <;> split <;> (try split) <;> decide

/-- A call of `fe2Fns` keeps the own rows' counters. -/
theorem callW_fe2_ownC {p : Prog} (hcl : Fe2Closed p) {f : FnName} (hf : f ∈ fe2Fns) {n : Nat}
    {args : List Word} {m m' : Mem} {r : List Word} (h : callW p n f args m = some (r, m')) :
    ownC m' = ownC m := by
  have hfr := (run_memFrame hcl hf (run_of_callW h)).1
  refine ownC_frame hfr ?_ (by
    simp only [fe2C, List.mem_map, List.mem_filter, List.mem_range, not_exists, not_and]
    intro x hx e
    have := congrArg UInt64.toNat e
    simp only [decide_eq_true_eq] at hx
    simp only [UInt64.toNat_ofNat] at this; simp at this; omega)
  intro b hb g t e
  subst e
  simp only [fe2A, List.mem_filter, decide_eq_true_eq] at hb
  have := oix_arr g t
  omega

end L.Ind
