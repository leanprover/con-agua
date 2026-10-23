import ConAgua.Arena.IndInstallSpec2

/-!
# Refinements of `IndInstall`, part 3 (lane `indproofs`, helper `install`)

`lvl_eq_fueled` (through the `lvl_eq` stub) and `check_block_agree_one`.
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

/-! ## `lvl_eq_fueled` -/

/-- The model of `lvl_eq_fueled(u, v)`: the stub `lvl_eq`, `none` (word `0`) aborts. -/
def lveW (m : Mem) (u v : Word) : Option (List Word × Mem) :=
  match stubM "lvl_eq_c" m [u, v] with
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then none else some ([if r.headD 0 = 2 then 1 else 0], m1)

theorem lvlEqFueled_spec (p : Prog) (hp : p.lookup "lvl_eq_fueled" = some lvlEqFueled) (n : Nat)
    (s₀ : St) (u v : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "lvl_eq_fueled" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ lveW s₀.mem u v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvlEqFueled]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        stubM_spec p "lvl_eq_c" n] <;>
      finish (gen := 20) [lveW]

/-- **`lvl_eq_fueled` is `liftFueled (← lvlEq? u v)`**, through the `lvl_eq` stub. -/
theorem lveW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (u v : Word) (hu : H u) (hv : H v) (r : List Word)
    (h : lveW m u v = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ b a', (lvlEq? (decI u) (decI v)).run a = .ok (some b, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) := by
  simp only [lveW] at h
  cases hs : stubM "lvl_eq_c" m [u, v] with
  | none => simp [hs] at h
  | some rm1 =>
    obtain ⟨r1, m1⟩ := rm1
    simp only [hs] at h
    by_cases h0 : r1.headD 0 = 0
    · rw [if_pos h0] at h; exact absurd h (by simp)
    · rw [if_neg h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨x, a1, hrun, hSt, hg, hdec⟩ := lvlEqStub_spec dn vis fe u v hu hv m m1 a r1 hs hS
      simp only [decLvlEq] at hdec
      cases x with
      | none => exact absurd hdec h0
      | some b =>
        refine ⟨b, a1, hrun, hSt, hg, ?_⟩
        · cases b <;> simp at hdec ⊢ <;> simp [hdec]

/-! ## `check_block_agree_one` -/

mutual
/-- **The model of `check_block_agree_one`**: the opened telescope, the member 0 domains, the
doms comparison, the universe comparison. -/
def agW (n : Nat) (m : Mem) (vis nP fvs0O fvs0L s0 cvTa s : Word) : Option (List Word × Mem) :=
  agK1 (n - 1) vis nP fvs0O fvs0L s0 s
    (stubM "open_pis_at_fvars_f" m [nP, rdW (m.arr64 EREC) (cvTa + 3), 0])

/-- After `open_pis_at_fvars_f`: `ok = 0` and a length mismatch abort, then `fvar_type_ds`. -/
def agK1 (n : Nat) (vis nP fvs0O fvs0L s0 s : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then none
    else if r.tail.tail.headD 0 ≠ fvs0L then none
    else agK2 n vis nP fvs0L s0 s r (ftdsF m1 [fvs0O, fvs0L])

/-- After `fvar_type_ds`: the doms comparison. -/
def agK2 (n : Nat) (vis nP fvs0L s0 s : Word) (r : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rd, m2) =>
    agK3 s0 s (domsW n m2 vis 0 (r.tail.headD 0) (r.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP)

/-- After `check_block_doms_at`: `lvl_eq_fueled`. -/
def agK3 (s0 s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => agK4 (lveW m3 s s0)

/-- After `lvl_eq_fueled`: `eq = 0` aborts. -/
def agK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (re, m4) => if re.headD 0 = 0 then none else some ([], m4)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (vis nP fvs0O fvs0L s0 s : Word) (r rd re : List Word)
theorem agK1_abort0 (h : r.headD 0 = 0) : agK1 n vis nP fvs0O fvs0L s0 s (some (r, m1)) = none := by
  rw [agK1, if_pos h]
theorem agK1_abortL (h0 : r.headD 0 ≠ 0) (h : r.tail.tail.headD 0 ≠ fvs0L) :
    agK1 n vis nP fvs0O fvs0L s0 s (some (r, m1)) = none := by
  rw [agK1, if_neg h0, if_pos h]
theorem agK1_ok (h0 : r.headD 0 ≠ 0) (h : r.tail.tail.headD 0 = fvs0L) :
    agK1 n vis nP fvs0O fvs0L s0 s (some (r, m1)) =
      agK2 n vis nP fvs0L s0 s r (ftdsF m1 [fvs0O, fvs0L]) := by
  rw [agK1, if_neg h0, if_neg (by simpa using h)]
theorem agK2_some : agK2 n vis nP fvs0L s0 s r (some (rd, m2)) =
    agK3 s0 s (domsW n m2 vis 0 (r.tail.headD 0) (r.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP) := rfl
theorem agK3_some (r' : List Word) : agK3 s0 s (some (r', m3)) = agK4 (lveW m3 s s0) := rfl
theorem agK4_ok (h : re.headD 0 ≠ 0) : agK4 (some (re, m1)) = some ([], m1) := by
  rw [agK4, if_neg h]
theorem agK4_abort (h : re.headD 0 = 0) : agK4 (some (re, m1)) = none := by
  rw [agK4, if_pos h]
end arms

grind_pattern [ind_grind] agK1_abort0 => agK1 n vis nP fvs0O fvs0L s0 s (some (r, m1))
grind_pattern [ind_grind] agK1_abortL => agK1 n vis nP fvs0O fvs0L s0 s (some (r, m1))
grind_pattern [ind_grind] agK1_ok => agK1 n vis nP fvs0O fvs0L s0 s (some (r, m1))
grind_pattern [ind_grind] agK2_some => agK2 n vis nP fvs0L s0 s r (some (rd, m2))
grind_pattern [ind_grind] agK3_some => agK3 s0 s (some (r', m3))
grind_pattern [ind_grind] agK4_ok => agK4 (some (re, m1))
grind_pattern [ind_grind] agK4_abort => agK4 (some (re, m1))

theorem checkBlockAgreeOne_spec (p : Prog)
    (hd : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
    (hl : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
    (hp : p.lookup "check_block_agree_one" = some checkBlockAgreeOne) (had : AdF p) (n : Nat) (s₀ : St)
    (vis nP fvs0O fvs0L s0 cvTa s : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_agree_one"
      [vis, nP, fvs0O, fvs0L, s0, cvTa, s]
    ⦃fun r s' => LocEq s' s₀ ∧ agW n s₀.mem vis nP fvs0O fvs0L s0 cvTa s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockAgreeOne]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        stubM_spec p "open_pis_at_fvars_f" n, ftdsF_spec p had n,
        domsW_spec p hd had.ftd n, lvlEqFueled_spec p hl n] <;>
      finish (gen := 20) [agW, lveW]

/-- A successful `domsW` has `j` within both lists. -/
theorem domsW_le {n : Nat} {m : Mem} {vis off fo fl dO dl j : Word} {r : List Word} {m' : Mem}
    (h : domsW n m vis off fo fl dO dl j = some (r, m')) :
    j.toNat ≤ fl.toNat ∧ j.toNat ≤ dl.toNat := by
  cases n with
  | zero => simp [domsW] at h
  | succ n =>
    by_cases hj : j = 0
    · subst hj; simp
    · have hjpos : 1 ≤ j.toNat := by
        rcases Nat.eq_zero_or_pos j.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hj
        · omega
      have hj1 : (j - 1).toNat = j.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hjpos))]
        simp
      by_cases hfl : fl ≤ j - 1
      · rw [domsW_abortF n m vis off fo fl dO dl j hj hfl] at h; simp at h
      by_cases hdl : dl ≤ j - 1
      · rw [domsW_abortD n m vis off fo fl dO dl j hj hfl hdl] at h; simp at h
      have h1 : ¬ fl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hfl
      have h2 : ¬ dl.toNat ≤ (j - 1).toNat := by rw [← UInt64.le_iff_toNat_le]; exact hdl
      omega

/-- The per-member body of `checkBlockAgree` after member 0's telescope `fvs0` is opened. -/
def agreeBodyAM (fe : IFEnv) (nP : Nat) (fvs0 : List EIdx) (cvTa : IConstantVal) (s s₀ : LIdx) :
    AM Unit := do
  let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
    (.invalid "parameters of all inductive datatypes must match")
  unless tq.1.length == fvs0.length do
    fail (.invalid "parameters of all inductive datatypes must match")
  let doms ← fvarTypeDs fvs0
  ConRon.Arena.checkBlockDomsAt V fe 0 tq.1 doms nP
  unless ← liftFueled "level comparison" (← lvlEq? s s₀) do
    fail (.invalid "mutually inductive types must live in the same universe")

theorem agGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, c⟩⟩ <;> rfl
theorem agGetD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, d⟩⟩⟩ <;> rfl
theorem agGetD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by
  rcases r with _ | ⟨a, b⟩ <;> rfl

theorem exc_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

/-- **The relational lemma of `check_block_agree_one`.** -/
theorem agW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (m m' : Mem)
    (a : AState) (vis nP fvs0O fvs0L s0 cvTa s : Word) (r : List Word) (cv : IConstantVal)
    (fvs0 : List EIdx)
    (h : agW (n + 1) m vis nP fvs0O fvs0L s0 cvTa s = some (r, m'))
    (hStage : StageR dn vis fe m a)
    (hty : (rdW (m.arr64 EREC) (cvTa + 3)).toNat < 2 ^ 32 ∧ decI (rdW (m.arr64 EREC) (cvTa + 3)) = cv.type)
    (hfvs0 : decHL m fvs0O.toNat fvs0L.toNat = some fvs0)
    (hfot : fvs0O.toNat + fvs0L.toNat ≤ iwTop m) (hs : H s) (hs0 : H s0) :
    ∃ a', (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)).run a = .ok ((), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  simp only [agW, Nat.add_sub_cancel] at h
  cases hra : stubM "open_pis_at_fvars_f" m [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] with
  | none => rw [hra] at h; simp [agK1] at h
  | some ram1 =>
  obtain ⟨ra, m1⟩ := ram1
  rw [hra] at h
  by_cases h0 : ra.headD 0 = 0
  · rw [agK1_abort0 n m1 _ _ _ _ _ _ ra h0] at h; simp at h
  by_cases hL : ra.tail.tail.headD 0 = fvs0L
  case neg => rw [agK1_abortL n m1 _ _ _ _ _ _ ra h0 hL] at h; simp at h
  rw [agK1_ok n m1 _ _ _ _ _ _ ra h0 hL] at h
  obtain ⟨x1, a1, hrun1, hSt1, hg1, hdec1⟩ :=
    openPisAtFvarsF_spec dn vis fe nP (rdW (m.arr64 EREC) (cvTa + 3)) 0 hty.1 m m1 a ra hra hStage
  cases x1 with
  | none => exact absurd hdec1 h0
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨-, hrl1, -⟩ := hdec1
  simp only [decRL, show (1:Nat) + 1 = 2 from rfl, agGetD1, agGetD2] at hrl1
  obtain ⟨hfv1, hfvb1⟩ := hrl1
  have hlen1 := decHL_length m1 hfv1
  have hlen0 := decHL_length m hfvs0
  rw [hL] at hlen1
  cases hrb : ftdsF m1 [fvs0O, fvs0L] with
  | none => rw [hrb] at h; simp [agK2] at h
  | some rdm2 =>
  obtain ⟨rd, m2⟩ := rdm2
  rw [hrb, agK2_some] at h
  have hbound1 : fvs0O.toNat + fvs0L.toNat ≤ iwTop m1 := by have := hg1.1; omega
  obtain ⟨x2, a2, hrun2, hSt2, hg2, hdec2⟩ :=
    ftdsF_ok dn vis fe fvs0O fvs0L fvs0 m1 m2 a1 rd hrb
      ⟨hSt1, by rw [decHL_grow hg1 (by omega)]; exact hfvs0⟩
  simp only [decRL, show (0:Nat) + 1 = 1 from rfl, agGetD0, agGetD1] at hdec2
  obtain ⟨hdm2, hdb2⟩ := hdec2
  cases hw : domsW n m2 vis 0 (ra.tail.headD 0) (ra.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP with
  | none => rw [hw] at h; simp [agK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [hw, agK3_some] at h
  obtain ⟨hjf, hjd⟩ := domsW_le hw
  have hlt1 := UInt64.toNat_lt (ra.tail.headD 0)
  have hlt2 := UInt64.toNat_lt (ra.tail.tail.headD 0)
  have hlt3 := UInt64.toNat_lt (rd.headD 0)
  have hlt4 := UInt64.toNat_lt (rd.tail.headD 0)
  have hltt : iwTop m2 < 2 ^ 64 := UInt64.toNat_lt _
  have hltt1 : iwTop m1 < 2 ^ 64 := UInt64.toNat_lt _
  obtain ⟨a3, hrun3, hSt3, hg3⟩ := domsW_ok n dn fe m2 m3 a2 vis 0 (ra.tail.headD 0)
    (ra.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP fvs x2 r3 hw hSt2
    (by rw [decHL_grow hg2 hfvb1]; exact hfv1) hdm2 (by omega) (by omega)
    (by have := hg2.1; omega) (by omega) (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hlt2) hjf hjd
  cases hl : lveW m3 s s0 with
  | none => rw [hl] at h; simp [agK4] at h
  | some rem4 =>
  obtain ⟨re, m4⟩ := rem4
  rw [hl] at h
  by_cases hre : re.headD 0 = 0
  · rw [agK4_abort (m1 := m4) (re := re) hre] at h; simp at h
  rw [agK4_ok (m1 := m4) (re := re) hre] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨b, a4, hrun4, hSt4, hg4, hbre⟩ := lveW_ok dn vis fe m3 m4 a3 s s0 hs hs0 re hl hSt3
  have hb : b = true := by
    cases b
    · exact absurd (by rw [hbre]; rfl) hre
    · rfl
  subst hb
  refine ⟨a4, ?_, hSt4, (hg1.trans hg2).trans (hg3.trans hg4)⟩
  have hty' : cv.type = decI (rdW (m.arr64 EREC) (cvTa + 3)) := hty.2.symm
  simp only [agreeBodyAM, unwrapOr, hty', StateT.run_bind, pure_bind]
  have hz : UInt64.toNat 0 = 0 := rfl
  simp only [hz] at hrun1 hrun3
  have heq : (fvs.length == fvs0.length) = true := by
    simp only [beq_iff_eq]; omega
  have hlenE : fvs.length = fvs0.length := by omega
  simp [StateT.run_bind, hrun1, hrun2, hrun3, hrun4, heq, hlenE, liftFueled, exc_ok_bind]
  rfl

/-- **`check_block_agree_one` is one step of `checkBlockAgree`** (member 0's telescope `fvs0`
opened by the caller): the parameter telescopes agree in length and domains, and the result
sorts are equivalent; the L code aborts nowhere the twin does not fail. -/
@[refines_part ConRon.Arena.checkBlockAgree "one member's two agreements"]
theorem checkBlockAgreeOne_refines (p : Prog)
    (hd : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
    (hl : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
    (hp : p.lookup "check_block_agree_one" = some checkBlockAgreeOne) (had : AdF p) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis nP fvs0O fvs0L s0 cvTa s : Word) (cv : IConstantVal) (fvs0 : List EIdx)
    (hStage : StageR dn vis fe s₀.mem a₀)
    (hty : (rdW (s₀.mem.arr64 EREC) (cvTa + 3)).toNat < 2 ^ 32 ∧
      decI (rdW (s₀.mem.arr64 EREC) (cvTa + 3)) = cv.type)
    (hfvs0 : decHL s₀.mem fvs0O.toNat fvs0L.toNat = some fvs0)
    (hfot : fvs0O.toNat + fvs0L.toNat ≤ iwTop s₀.mem) (hs : H s) (hs0 : H s0) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_agree_one"
      [vis, nP, fvs0O, fvs0L, s0, cvTa, s]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (checkBlockAgreeOne_spec p hd hl hp had (n + 1) s₀ vis nP fvs0O fvs0L s0 cvTa s) ?_
  rintro r s' ⟨hlq, hm⟩
  obtain ⟨a', hrun, hSt', hg⟩ := agW_ok n dn fe s₀.mem s'.mem a₀ vis nP fvs0O fvs0L s0 cvTa s r cv
    fvs0 hm hStage hty hfvs0 hfot hs hs0
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlq, hok, by rw [hst]; exact hSt', hg⟩

end L.Ind
