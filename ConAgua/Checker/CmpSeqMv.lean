module

public import ConAgua.Checker.CmpSeqEntry
import all ConAgua.Checker.CmpSeqEntry
import ConAgua.Arena.FreezeCmpSpec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.Checker.CmpSeqView
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# Modes `8` and `9`'s index words (lane compare2, the sJ variant)

`cq_ctl_s` and `cq_ctl_c` (`Checker/CmpSeqEntry.lean`) are straight-line word moves
`d[i] := s[j]` (constant indices). One move list runs as `cqMvs` (`cqMvs_run`: each move reads the
memory the previous ones left); the specs `cqCtlS_spec`/`cqCtlC_spec` end there. (vcgen over the
whole body builds a term whose unshared size doubles with every store.)
-/

namespace L.Checker

open L L.Arena L.Front
open Std.WP
open scoped Lean.Order

/-- A word move `d[i] := s[j]`. -/
abbrev CqMv := ArrId × Word × ArrId × Word

/-- The move's statement. -/
def cqMvS (x : CqMv) : Stmt := .st64 x.1 (.const x.2.1) (.ld64 x.2.2.1 (.const x.2.2.2))

/-- The memory after one move. -/
def cqMv (m : Mem) (x : CqMv) : Mem := m.set64 x.1 x.2.1 (rdW (m.arr64 x.2.2.1) x.2.2.2)

/-- The memory after the moves `l`, in order. -/
def cqMvs (l : List CqMv) (m : Mem) : Mem := l.foldl cqMv m

/-- Every move of `l` in bounds (sizes never change). -/
def CqMvsOK (l : List CqMv) (m : Mem) : Prop :=
  ∀ x ∈ l, x.2.1.toNat < (m.arr64 x.1).size ∧ x.2.2.2.toNat < (m.arr64 x.2.2.1).size

instance (l : List CqMv) (m : Mem) : Decidable (CqMvsOK l m) := by
  unfold CqMvsOK; infer_instance

theorem cqMvs_size (l : List CqMv) : ∀ (m : Mem) (b : TieredArray), ((cqMvs l m).arr64 b).size = (m.arr64 b).size := by
  induction l with
  | nil => intro m b; rfl
  | cons x l ih => intro m b; simp only [cqMvs, List.foldl_cons] at *; rw [ih]; simp [cqMv, L.Mem.size64_set64]

theorem cq_evalE_ld (a : ArrId) (j : Word) (s : St) :
    (evalE (.ld64 a (.const j))).run s =
      if j.toNat < (s.mem.arr64 a).size then .ok (rdW (s.mem.arr64 a) j, s) else .error .oob := by
  by_cases h : j.toNat < (s.mem.arr64 a).size
  · simp [evalE, ld64, h, rdW]; rfl
  · simp [evalE, ld64, h]

/-- **A move list runs as `cqMvs`**, or ends out of bounds. -/
theorem cqMvs_run {p : Prog} {f : Stmt → M Sig} (R : Stmt) :
    ∀ (l : List CqMv) (s : St), (step p f (l.foldr (fun x t => .seq (cqMvS x) t) R)).run s =
      if CqMvsOK l s.mem then (step p f R).run { s with mem := cqMvs l s.mem } else .error .oob
  | [], s => by simp [CqMvsOK, cqMvs]
  | x :: l, s => by
    rw [List.foldr_cons, show cqMvS x = .st64 x.1 (.const x.2.1) (.ld64 x.2.2.1 (.const x.2.2.2)) from rfl]
    rw [step_st64_seq _ _ _ _ s x.2.1 (rdW (s.mem.arr64 x.2.2.1) x.2.2.2)
      (x.2.2.2.toNat < (s.mem.arr64 x.2.2.1).size) rfl (by rw [cq_evalE_ld])]
    by_cases h : x.2.2.2.toNat < (s.mem.arr64 x.2.2.1).size ∧ x.2.1.toNat < (s.mem.arr64 x.1).size
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), cqMvs_run R l]
      have e : ∀ (m : Mem), CqMvsOK (x :: l) m ↔
          (x.2.1.toNat < (m.arr64 x.1).size ∧ x.2.2.2.toNat < (m.arr64 x.2.2.1).size) ∧ CqMvsOK l m := by
        intro m; simp [CqMvsOK]
      have e2 : CqMvsOK l (s.mem.set64 x.1 x.2.1 (rdW (s.mem.arr64 x.2.2.1) x.2.2.2)) ↔ CqMvsOK l s.mem := by
        simp [CqMvsOK, L.Mem.size64_set64]
      simp only [e, e2, h, and_self, true_and]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false ?_)]
      simp only [CqMvsOK, List.mem_cons, forall_eq_or_imp]
      grind

/-! ## `cq_ctl_s` -/

/-- `cq_ctl_s`'s moves: the challenge's index words to `CCTL[16‥29]`, the solution's in. -/
def cqCtlSMvs : List CqMv :=
  [(CCTL, 16, CTL, 128), (CTL, 128, CTL, 225),
   (CCTL, 17, CTL, 162), (CTL, 162, SCTL, 162), (CCTL, 18, CTL, 163), (CTL, 163, SCTL, 163),
   (CCTL, 19, CTL, 164), (CTL, 164, SCTL, 164), (CCTL, 20, CTL, 165), (CTL, 165, SCTL, 165),
   (CCTL, 21, CTL, 166), (CTL, 166, SCTL, 166), (CCTL, 22, CTL, 167), (CTL, 167, SCTL, 167),
   (CCTL, 23, CTL, 168), (CTL, 168, SCTL, 168), (CCTL, 24, CTL, 169), (CTL, 169, SCTL, 169),
   (CCTL, 25, CTL, 170), (CTL, 170, SCTL, 170), (CCTL, 26, CTL, 171), (CTL, 171, SCTL, 171),
   (CCTL, 27, CTL, 172), (CTL, 172, SCTL, 172), (CCTL, 28, CTL, 173), (CTL, 173, SCTL, 173),
   (CCTL, 29, CTL, 224)]

/-- **The memory after `cq_ctl_s()`**. -/
def cqCtlSM (m : Mem) : Mem := (cqMvs cqCtlSMvs m).set64 CTL 224 0

/-- `cq_ctl_s`'s bounds. -/
def CqCtlSOK (m : Mem) : Prop :=
  30 ≤ (m.arr64 CCTL).size ∧ 226 ≤ (m.arr64 CTL).size ∧ 174 ≤ (m.arr64 SCTL).size

theorem cqCtlSL_eq : cqCtlSL = { nparams := 0, nlocals := 0, body :=
    (cqCtlSMvs.foldr (fun x t => .seq (cqMvS x) t) (.seq (.st64 CTL (.const 224) (.const 0)) (.ret [.const 0]))) } := by
  unfold cqCtlSL; rfl

/-- **`cq_ctl_s()` as a triple** (any fuel). -/
theorem cqCtlS_spec (p : Prog) (hp : p.lookup "cq_ctl_s" = some cqCtlSL) (n : Nat) (s₀ : St) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "cq_ctl_s" []
    ⦃fun _ s' => LocEq s' s₀ ∧ CqCtlSOK s₀.mem ∧ s'.mem = cqCtlSM s₀.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs0 hrun
  subst hs0
  rw [invoke_eq _ hp] at hrun
  unfold callFn at hrun
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, StateT.run_modify] at hrun
  generalize hB : (exec p n cqCtlSL.body).run ({ mem := s.mem, loc := Locals.init [] } : St) = B at hrun
  cases B with
  | error e => cases hrun
  | ok v =>
    obtain ⟨sig, s2⟩ := v
    simp only [StateT.run_pure] at hrun
    have hrun' : (sig.retVal, ({ mem := s2.mem, loc := s.loc } : St)) = (r, s') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at hrun'
    obtain ⟨rfl, rfl⟩ := hrun'
    match n with
    | 0 => cases hB
    | n + 1 =>
      change (step p (exec p n) cqCtlSL.body).run _ = _ at hB
      rw [cqCtlSL_eq] at hB
      simp only at hB
      rw [cqMvs_run] at hB
      split at hB
      · rename_i hok
        rw [step_st64_seq (P := True) _ _ _ _ _ 224 0 rfl rfl] at hB
        have hc : 226 ≤ (s.mem.arr64 CTL).size := by
          have := (hok (CTL, 128, CTL, 225) (by simp [cqCtlSMvs])).2; simp at this; omega
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨trivial, by rw [cqMvs_size]; simp; omega⟩)] at hB
        simp [step] at hB
        simp only [evalArgs, evalE] at hB
        cases hB
        have h1 := (hok (CCTL, 29, CTL, 224) (by simp [cqCtlSMvs])).1
        have h2 := (hok (CTL, 173, SCTL, 173) (by simp [cqCtlSMvs])).2
        simp only at h1 h2
        exact ⟨rfl, ⟨by simp at h1; omega, hc, by simp at h2; omega⟩, rfl⟩
      · cases hB

/-! ## `cq_ctl_c` -/

/-- `cq_ctl_c`'s moves: the challenge's index words back from `CCTL[16‥29]`. -/
def cqCtlCMvs : List CqMv :=
  [(CTL, 128, CCTL, 16), (CTL, 162, CCTL, 17), (CTL, 163, CCTL, 18), (CTL, 164, CCTL, 19),
   (CTL, 165, CCTL, 20), (CTL, 166, CCTL, 21), (CTL, 167, CCTL, 22), (CTL, 168, CCTL, 23),
   (CTL, 169, CCTL, 24), (CTL, 170, CCTL, 25), (CTL, 171, CCTL, 26), (CTL, 172, CCTL, 27),
   (CTL, 173, CCTL, 28), (CTL, 224, CCTL, 29)]

/-- **The memory after `cq_ctl_c()`**. -/
def cqCtlCM (m : Mem) : Mem := cqMvs cqCtlCMvs m

/-- `cq_ctl_c`'s bounds. -/
def CqCtlCOK (m : Mem) : Prop := 30 ≤ (m.arr64 CCTL).size ∧ 225 ≤ (m.arr64 CTL).size

theorem cqCtlCL_eq : cqCtlCL = { nparams := 0, nlocals := 0, body :=
    (cqCtlCMvs.foldr (fun x t => .seq (cqMvS x) t) (.ret [.const 0])) } := by
  unfold cqCtlCL; rfl

/-- **`cq_ctl_c()` as a triple** (any fuel). -/
theorem cqCtlC_spec (p : Prog) (hp : p.lookup "cq_ctl_c" = some cqCtlCL) (n : Nat) (s₀ : St) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "cq_ctl_c" []
    ⦃fun _ s' => LocEq s' s₀ ∧ CqCtlCOK s₀.mem ∧ s'.mem = cqCtlCM s₀.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs0 hrun
  subst hs0
  rw [invoke_eq _ hp] at hrun
  unfold callFn at hrun
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, StateT.run_modify] at hrun
  generalize hB : (exec p n cqCtlCL.body).run ({ mem := s.mem, loc := Locals.init [] } : St) = B at hrun
  cases B with
  | error e => cases hrun
  | ok v =>
    obtain ⟨sig, s2⟩ := v
    simp only [StateT.run_pure] at hrun
    have hrun' : (sig.retVal, ({ mem := s2.mem, loc := s.loc } : St)) = (r, s') := Except.ok.inj hrun
    simp only [Prod.mk.injEq] at hrun'
    obtain ⟨rfl, rfl⟩ := hrun'
    match n with
    | 0 => cases hB
    | n + 1 =>
      change (step p (exec p n) cqCtlCL.body).run _ = _ at hB
      rw [cqCtlCL_eq] at hB
      simp only at hB
      rw [cqMvs_run] at hB
      split at hB
      · rename_i hok
        simp only [step, evalArgs, evalE] at hB
        cases hB
        have h1 := (hok (CTL, 224, CCTL, 29) (by simp [cqCtlCMvs]))
        simp only at h1
        exact ⟨rfl, ⟨by simp at h1; omega, by simp at h1; omega⟩, rfl⟩
      · cases hB

/-! ## What the moves change -/

theorem cq_rdW_arr {m : Mem} {a b : TieredArray} {k v x : Word} (h : b ≠ a) :
    rdW ((m.set64 a k v).arr64 b) x = rdW (m.arr64 b) x := by
  rw [Mem.arr64_set64_ne _ _ _ _ _ h]

theorem cq_rdW_idx {m : Mem} {a b : TieredArray} {k v x : Word} (h : k ≠ x) :
    rdW ((m.set64 a k v).arr64 b) x = rdW (m.arr64 b) x := by
  rw [rdW_set64]; simp [h]

theorem cq_rdW_hit {m : Mem} {a : TieredArray} {k v : Word} (h : k.toNat < (m.arr64 a).size) :
    rdW ((m.set64 a k v).arr64 a) k = v := by
  rw [rdW_set64]; simp [h]

/-- The `CCTL` slot keeping the challenge's index word `x ∈ csC`. -/
def cqSlot (x : Word) : Word := if x = 128 then 16 else if x = 224 then 29 else x - 145

theorem cqCtlSM_frame (m : Mem) : MemFrame [CCTL] csC m (cqCtlSM m) := by
  refine ⟨fun b hb hc => ?_, fun x hx => ?_, fun b => ?_⟩
  · have hb' : b ≠ CCTL := fun e => hb (by simp [e])
    simp only [cqCtlSM, cqMvs, cqCtlSMvs, List.foldl, cqMv, Mem.arr64_set64_ne _ _ _ _ _ hb',
      Mem.arr64_set64_ne _ _ _ _ _ hc]
  · simp only [csC, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hx
    simp only [cqCtlSM, cqMvs, cqCtlSMvs, List.foldl, cqMv, rdW_set64]
    simp (config := { decide := true }) [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5,
      Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12,
      Ne.symm h13, Ne.symm h14]
  · simp only [cqCtlSM, L.Mem.size64_set64, cqMvs_size]

/-- `cq_ctl_s` keeps the challenge's index words in their slots. -/
theorem cqCtlSM_cctl {m : Mem} (h : CqCtlSOK m) :
    ∀ x ∈ csC, rdW ((cqCtlSM m).arr64 CCTL) (cqSlot x) = rdW (m.arr64 CTL) x := by
  obtain ⟨h1, h2, h3⟩ := h
  intro x hx
  simp only [csC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [cqSlot, ite_true, ite_false, UInt64.reduceSub]
    simp only [cqCtlSM, cqMvs, cqCtlSMvs, List.foldl, cqMv]
    simp (disch := first | decide | ((try simp only [L.Mem.size64_set64]); (try simp); omega)) only
      [cq_rdW_arr, cq_rdW_idx, cq_rdW_hit]

/-- `cq_ctl_s` keeps `CCTL` outside the slots. -/
theorem cqCtlSM_cctl_keep (m : Mem) (k : Word) (hk : k.toNat < 16 ∨ 29 < k.toNat) :
    rdW ((cqCtlSM m).arr64 CCTL) k = rdW (m.arr64 CCTL) k := by
  have hne : ∀ j : Word, 16 ≤ j.toNat → j.toNat ≤ 29 → j ≠ k := by
    intro j h1 h2 e; subst e; omega
  simp only [cqCtlSM, cqMvs, cqCtlSMvs, List.foldl, cqMv, rdW_set64]
  simp (config := { decide := true }) [hne 16 (by decide) (by decide), hne 17 (by decide) (by decide),
    hne 18 (by decide) (by decide), hne 19 (by decide) (by decide), hne 20 (by decide) (by decide),
    hne 21 (by decide) (by decide), hne 22 (by decide) (by decide), hne 23 (by decide) (by decide),
    hne 24 (by decide) (by decide), hne 25 (by decide) (by decide), hne 26 (by decide) (by decide),
    hne 27 (by decide) (by decide), hne 28 (by decide) (by decide), hne 29 (by decide) (by decide)]

/-- **The solution's index words after `cq_ctl_s`**: the counter from `CTL[225]`, the frozen
words from `SCTL`, the flag `0`. -/
theorem cqCtlSM_ctl {m : Mem} (h : CqCtlSOK m) :
    rdW ((cqCtlSM m).arr64 CTL) 128 = rdW (m.arr64 CTL) 225 ∧
    (∀ x : Word, 162 ≤ x.toNat → x.toNat ≤ 173 → rdW ((cqCtlSM m).arr64 CTL) x = rdW (m.arr64 SCTL) x) ∧
    rdW ((cqCtlSM m).arr64 CTL) 224 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun x hx1 hx2 => ?_, ?_⟩
  · simp only [cqCtlSM, cqMvs, cqCtlSMvs, List.foldl, cqMv]
    simp (disch := first | decide | ((try simp only [L.Mem.size64_set64]); (try simp); omega)) only
      [cq_rdW_arr, cq_rdW_idx, cq_rdW_hit]
  · have e : ∃ k : Nat, k < 12 ∧ x = (162 + k).toUInt64 := ⟨x.toNat - 162, by omega, by
      apply UInt64.toNat_inj.mp; simp; omega⟩
    obtain ⟨k, hk, rfl⟩ := e
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by
      omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Nat.reduceAdd, Nat.toUInt64_eq, UInt64.reduceOfNat]
      simp only [cqCtlSM, cqMvs, cqCtlSMvs, List.foldl, cqMv]
      simp (disch := first | decide | ((try simp only [L.Mem.size64_set64]); (try simp); omega)) only
      [cq_rdW_arr, cq_rdW_idx, cq_rdW_hit]
  · simp only [cqCtlSM, cqMvs, cqCtlSMvs, List.foldl, cqMv]
    simp (disch := first | decide | ((try simp only [L.Mem.size64_set64]); (try simp); omega)) only
      [cq_rdW_arr, cq_rdW_idx, cq_rdW_hit]

theorem cqCtlCM_frame (m : Mem) : MemFrame [] csC m (cqCtlCM m) := by
  refine ⟨fun b _ hc => ?_, fun x hx => ?_, fun b => ?_⟩
  · simp only [cqCtlCM, cqMvs, cqCtlCMvs, List.foldl, cqMv, Mem.arr64_set64_ne _ _ _ _ _ hc]
  · simp only [csC, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hx
    simp only [cqCtlCM, cqMvs, cqCtlCMvs, List.foldl, cqMv, rdW_set64]
    simp (config := { decide := true }) [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5,
      Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12,
      Ne.symm h13, Ne.symm h14]
  · simp only [cqCtlCM, cqMvs_size]

/-- **`cq_ctl_c` restores the challenge's index words** from their slots. -/
theorem cqCtlCM_ctl {m : Mem} (h : CqCtlCOK m) :
    ∀ x ∈ csC, rdW ((cqCtlCM m).arr64 CTL) x = rdW (m.arr64 CCTL) (cqSlot x) := by
  obtain ⟨h1, h2⟩ := h
  intro x hx
  simp only [csC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [cqSlot, ite_true, ite_false, UInt64.reduceSub]
    simp only [cqCtlCM, cqMvs, cqCtlCMvs, List.foldl, cqMv]
    simp (disch := first | decide | ((try simp only [L.Mem.size64_set64]); (try simp); omega)) only
      [cq_rdW_arr, cq_rdW_idx, cq_rdW_hit]

/-- `cq_ctl_c` keeps every array but `CTL`. -/
theorem cqCtlCM_arr (m : Mem) (b : TieredArray) (hb : b ≠ CTL) : (cqCtlCM m).arr64 b = m.arr64 b :=
  (cqCtlCM_frame m).arr b (by simp) hb

end L.Checker
