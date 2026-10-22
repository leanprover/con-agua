import ConAgua.Arena.IndPartsSpec10

/-!
# Refinements of `IndParts`, part 11 (lane `indproofs2`, helper `parts`): the member counts

`blockMemberCounts?`: `block_member_counts_find` (the `findM?` over the recursors, through
`rec_target_of`), `block_member_counts_go` (one `block_counts` per former, then the rest). The pool
stays below its top across `block_counts` (`PTop`, so the stage relation is kept: lane
`indproofs`' `blockCounts_refines` gives only the frame).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The pool top stays in the array -/

/-- The pool's top is in the array, whose length is a word. -/
def PTop (m : Mem) : Prop :=
  iwTop m ≤ (m.arr64 IW).size ∧ (m.arr64 IW).size < 2 ^ 64 ∧ 200 < (m.arr64 CTL).size

theorem copyW_ctl (n : Nat) : ∀ (m m' : Mem) (d s l : Word), copyW n m d s l = some m' →
    m'.arr64 CTL = m.arr64 CTL ∧ (m'.arr64 IW).size = (m.arr64 IW).size := by
  induction n with
  | zero => intro m m' d s l h; simp [copyW] at h
  | succ n ih =>
    intro m m' d s l h
    by_cases hl : l = 0
    · rw [copyW_nil n m d s l hl] at h; cases h; exact ⟨rfl, rfl⟩
    rw [copyW_step n m d s l hl] at h
    obtain ⟨h1, h2⟩ := ih _ _ _ _ _ h
    exact ⟨h1.trans (Mem.arr64_set64_ne _ _ _ _ _ (by decide)), h2.trans (size_set64 _ _ _ _ _)⟩

theorem consW_ptop {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) (hP : PTop m) : PTop m' := by
  obtain ⟨-, hsz, hc⟩ := hP
  simp only [consW] at h
  split at h
  · cases h
  cases hal : allocW m (l + 1) with
  | none => rw [hal] at h; cases h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  rw [hal] at h
  simp only at h
  cases hcp : copyW (n - 1) (m1.set64 IW q x) (q + 1) o l with
  | none => rw [hcp] at h; cases h
  | some m2 =>
  rw [hcp] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨rfl, rfl, hroom⟩ := allocW_facts hal hsz
  obtain ⟨hC, hI⟩ := copyW_ctl _ _ _ _ _ _ hcp
  rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)] at hC
  rw [size_set64, allocMem_IW] at hI
  refine ⟨?_, by rw [hI]; exact hsz, by rw [hC]; simp only [allocMem]; rw [size_set64]; exact hc⟩
  simp only [iwTop]
  rw [hC, allocMem_top m _ hc, hI, UInt64.toNat_add]
  have := (rdW (m.arr64 CTL) 200).toNat_lt
  omega

theorem piBW_ptop (n : Nat) : ∀ (m m' : Mem) (fuel h : Word) (rs : List Word),
    piBW n m fuel h = some (rs, m') → PTop m → PTop m' := by
  induction n with
  | zero => intro m m' fuel h rs hh; simp [piBW] at hh
  | succ n ih =>
    intro m m' fuel h rs hh hP
    by_cases hf : fuel = 0
    · rw [piBW_fuel0 n m fuel h hf] at hh; cases hh
    by_cases hg : h >>> 28 ≠ 6
    · rw [piBW_leaf n m fuel h hf hg] at hh; simp at hh; rw [← hh.2]; exact hP
    rw [piBW_node n m fuel h hf hg] at hh
    by_cases hr : eViewW m h = []
    · rw [hr, piBK1_nil] at hh; cases hh
    rw [piBK1_ne n m fuel _ hr] at hh
    cases hrec : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with
    | none => rw [hrec] at hh; simp [piBK2] at hh
    | some rm =>
      obtain ⟨rs1, m1⟩ := rm
      rw [hrec, piBK2_some] at hh
      cases hcons : consW n m1 ((eViewW m h).getD 1 0) (rs1.headD 0) (rs1.getD 1 0) with
      | none => rw [hcons] at hh; simp [piBK3] at hh
      | some rm2 =>
        obtain ⟨r2, m2⟩ := rm2
        rw [hcons, piBK3_some] at hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨-, rfl⟩ := hh
        exact consW_ptop hcons (ih _ _ _ _ _ hrec hP)

theorem bcW_ptop {n : Nat} {m m' : Mem} {nPd k nC nR cvT rOk rMI rRP : Word} {r : List Word}
    (h : bcW n m nPd k nC nR cvT rOk rMI rRP = some (r, m')) (hP : PTop m) : PTop m' := by
  cases n with
  | zero => simp [bcW] at h
  | succ n =>
  rw [bcW_def] at h
  cases n with
  | zero => simp [bchW, bcK] at h
  | succ n =>
  rw [bchW_step] at h
  cases hp : piBW n m CWF (rdW (m.arr64 EREC) (cvT + 3)) with
  | none => rw [hp] at h; simp [bchW.bchK1, bcK] at h
  | some rm =>
    obtain ⟨rs, m1⟩ := rm
    rw [hp, bchK1_some] at h
    by_cases hr : eViewW m1 (rs.getD 2 0) = []
    · rw [hr] at h; simp [bchW.bchK2, bcK] at h
    rw [bchK2_ne _ _ _ hr, bcK_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact piBW_ptop n _ _ _ _ _ hp hP

/-! ## The program bundle -/

/-- The program bundle of the counts. -/
structure IndPartsProg4 (p : Prog) : Prop extends IndPartsProg3 p where
  target : p.lookup "rec_target_of" = some recTargetOf
  piB : p.lookup "pi_binders" = some piBinders
  bcHead : p.lookup "block_counts_head" = some blockCountsHead
  bcPure : p.lookup "block_counts_pure" = some blockCountsPure
  counts : p.lookup "block_counts" = some blockCounts
  mcFind : p.lookup "block_member_counts_find" = some blockMemberCountsFind
  mcGo : p.lookup "block_member_counts_go" = some blockMemberCountsGo
  mc : p.lookup "block_member_counts" = some blockMemberCounts

/-! ## `block_member_counts_find` -/

theorem partsFindM_cons {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (p : α → m Bool)
    (a : α) (as : List α) :
    List.findM? p (a :: as) = (do let b ← p a; if b then pure (some a) else List.findM? p as) := by
  simp only [List.findM?]
  congr 1; funext b; cases b <;> rfl

/-- After the recursive call. -/
def bmfK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m)

mutual
/-- **The model of `block_member_counts_find`.** -/
def bmfW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, ro, rl, mm =>
    if rl = 0 then some ([0, 0, 0], m)
    else bmfK1 n no nl ro rl mm (rdW (m.arr64 IW) ro)
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 1))
      (recTW n m no nl (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 1))
        (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3)))
/-- After `rec_target_of`. -/
def bmfK1 (n : Nat) (no nl ro rl mm e mI : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = mm then some ([1, mI, rdW (m1.arr64 IW) (e + 2)], m1)
    else bmfK2 (bmfW n m1 no nl (ro + 1) (rl - 1) mm)
end

section arms
variable (n : Nat) (m m1 : Mem) (no nl ro rl mm e mI : Word) (r1 : List Word)
theorem bmfW_nil (h : rl = 0) : bmfW (n + 1) m no nl ro rl mm = some ([0, 0, 0], m) := by
  simp [bmfW, h]
theorem bmfW_cons (h : rl ≠ 0) : bmfW (n + 1) m no nl ro rl mm =
    bmfK1 n no nl ro rl mm (rdW (m.arr64 IW) ro) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 1))
      (recTW n m no nl (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 1))
        (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3))) := by simp [bmfW, h]
theorem bmfK1_hit (h : r1.headD 0 = mm) : bmfK1 n no nl ro rl mm e mI (some (r1, m1)) =
    some ([1, mI, rdW (m1.arr64 IW) (e + 2)], m1) := by simp only [bmfK1]; exact if_pos h
theorem bmfK1_miss (h : r1.headD 0 ≠ mm) : bmfK1 n no nl ro rl mm e mI (some (r1, m1)) =
    bmfK2 (bmfW n m1 no nl (ro + 1) (rl - 1) mm) := by simp only [bmfK1]; exact if_neg h
theorem bmfK2_some : bmfK2 (some (r1, m1)) =
    some ([r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0], m1) := rfl
end arms
attribute [ind_grind] bmfW_nil bmfW_cons bmfK1_hit bmfK1_miss bmfK2_some

theorem bmf_spec (p : Prog) (hP : IndPartsProg4 p) (n : Nat) : ∀ (s₀ : St) (no nl ro rl mm : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_member_counts_find" [no, nl, ro, rl, mm]
    ⦃fun r s' => LocEq s' s₀ ∧ bmfW n s₀.mem no nl ro rl mm = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ no nl ro rl mm; rw [invoke_eq _ hP.mcFind]; simp only [callFn, blockMemberCountsFind]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ no nl ro rl mm
    rw [invoke_eq _ hP.mcFind]
    simp only [callFn, blockMemberCountsFind]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        recTargetOf_spec p hP.view hP.find hP.target n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem decSR_fields {m : Mem} {p : Nat} {cv : IConstantVal} {mI rP : Nat} {rules : List IRecRule}
    (h : decSR m p = some (cv, mI, rP, rules)) :
    (∃ cvp, iwN m p = some cvp ∧ decCVp m cvp = some cv) ∧ iwN m (p + 1) = some mI ∧
      iwN m (p + 2) = some rP := by
  simp only [decSR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, g, hg, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  exact ⟨⟨a, ha, hb⟩, hc, hd⟩

/-! ### Twin-side facts -/

theorem partsExBind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β} (h : x >>= f = .ok v) :
    ∃ y, x = .ok y ∧ f y = .ok v := by
  cases x with
  | error e => cases h
  | ok y => exact ⟨y, rfl, h⟩

theorem partsFailNe {α : Type} {e : CheckError} {a a' : AState} {v : α}
    (h : (fail e : AM α).run a = .ok (v, a')) : False := by
  revert h; unfold fail
  simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind, bind, StateT.run]

theorem partsPureRun {α : Type} {c v : α} {a a' : AState} (h : (pure c : AM α).run a = .ok (v, a')) :
    v = c := by
  simp [StateT.run, pure, StateT.pure, Except.pure] at h; exact h.1.symm

theorem partsRecTarget_le {names : List NIdx} {mI : Nat} {ty : EIdx} {a a' : AState} {t : Nat}
    (h : (ConRon.Arena.recTargetOf names mI ty).run a = .ok (t, a')) : t ≤ names.length := by
  unfold ConRon.Arena.recTargetOf at h
  simp only [StateT.run_bind] at h
  obtain ⟨⟨p1, a1⟩, -, h⟩ := partsExBind h
  rcases p1 with _ | ⟨l, e⟩
  · exact Nat.le_of_eq (partsPureRun h)
  simp only at h
  split at h
  · simp only [StateT.run_bind] at h
    obtain ⟨⟨v, a2⟩, -, h⟩ := partsExBind h
    rcases v with _ | ⟨dom, b⟩
    · exact (partsFailNe h).elim
    simp only [StateT.run_bind] at h
    obtain ⟨⟨hd, a3⟩, -, h⟩ := partsExBind h
    split at h
    · simp only [StateT.run_bind] at h
      obtain ⟨⟨w, a4⟩, -, h⟩ := partsExBind h
      rcases w with _ | ⟨nn, us⟩
      · exact (partsFailNe h).elim
      simp only at h
      split at h
      · rename_i t' ht'
        rw [partsPureRun h]
        rw [List.findIdx?_eq_some_iff_getElem] at ht'
        exact Nat.le_of_lt ht'.1
      · exact Nat.le_of_eq (partsPureRun h)
    · exact Nat.le_of_eq (partsPureRun h)
  · exact Nat.le_of_eq (partsPureRun h)

/-- The `findM?` predicate of `blockMemberCounts?`. -/
def bmfPred (names : List NIdx) (mm : Nat) (q : IConstantVal × Nat × Nat × List IRecRule) : AM Bool := do
  pure ((← ConRon.Arena.recTargetOf names q.2.1 q.1.type) == mm)

/-- **`block_member_counts_find`'s model refines the twin's `findM?`.** -/
theorem bmfW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl mm : Word}
    {names : List NIdx} (n : Nat) :
    ∀ (m : Mem) (a : AState) (ro rl : Word) (rs : List (IConstantVal × Nat × Nat × List IRecRule)),
    StageR dn vis fe m a → PSlR decSR rs ro rl m →
    DecB (fun m => decHL m no.toNat nl.toNat) m names → no.toNat + nl.toNat ≤ iwTop m →
    Sim (bmfW n m no nl ro rl mm) (rs.findM? (bmfPred names mm.toNat)) a
      (fun r x m' a' => r = encONN (x.map fun q => (q.2.1, q.2.2.1)) ∧ StageR dn vis fe m' a' ∧
        IWGrow m m') := by
  induction n with
  | zero => intro m a ro rl rs _ _ _ _ r m' e; simp [bmfW] at e
  | succ n ih =>
    intro m a ro rl rs hS hrs hnm hnb
    by_cases hl : rl = 0
    · rw [bmfW_nil n m no nl ro rl mm hl]
      subst hl; rw [partsPSl_nil hrs]
      exact Sim.ret ⟨rfl, hS, IWGrow.refl _⟩
    rw [bmfW_cons n m no nl ro rl mm hl]
    obtain ⟨pc, ⟨cv, mI, rP, rules⟩, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hl
    obtain ⟨⟨cvp, hcvp, hcv⟩, hmI, hrP⟩ := decSR_fields (show decSR (truncM m) pc = _ from hrs0)
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hp1 : (UInt64.ofNat pc + 1).toNat = pc + 1 := by
      have := partsIwLt hmI; rw [UInt64.toNat_add, hpw]; simp; omega
    have hp2 : (UInt64.ofNat pc + 2).toNat = pc + 2 := by
      have := partsIwLt hrP; rw [UInt64.toNat_add, hpw]; simp; omega
    obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp hpw
    obtain ⟨hmw, hmb, -⟩ := partsIwRd hmI hp1
    obtain ⟨hrw, hrb, hrlt⟩ := partsIwRd hrP hp2
    obtain ⟨htyl, htye⟩ := partsCVType hcv (UInt64.toNat_ofNat_of_lt' hcvb)
    rw [hw, hcw, hmw]
    rw [partsFindM_cons]
    simp only [bmfPred, bind_assoc, pure_bind]
    have hnames : decHL m no.toNat nl.toNat = some names := hnm.get (OMono.decHL _ _)
    refine Sim.bindK (K := bmfK1 n no nl ro rl mm (UInt64.ofNat pc) (UInt64.ofNat mI))
      (body := fun r1 m1 => if r1.headD 0 = mm then some ([1, UInt64.ofNat mI,
          rdW (m1.arr64 IW) (UInt64.ofNat pc + 2)], m1)
        else bmfK2 (bmfW n m1 no nl (ro + 1) (rl - 1) mm)) (by simp [bmfK1])
      (fun _ _ => by simp only [bmfK1])
      (Q := fun r t m1 a1 => r = [UInt64.ofNat t] ∧ t ≤ names.length ∧ StageR dn vis fe m1 a1 ∧ IWGrow m m1)
      ?_ ?_
    · intro r1 m1 e
      obtain ⟨t, a1, hrun, hr, hS1, hg1⟩ := recTW_ok n dn fe vis m m1 a no nl _ _ r1 names e hS htyl
        hnames (by omega) hnb
      rw [UInt64.toNat_ofNat_of_lt' hmb, htye] at hrun
      exact ⟨t, a1, hrun, hr, partsRecTarget_le hrun, hS1, hg1⟩
    rintro r1 t m1 a1 ⟨rfl, htl, hS1, hg1⟩
    have hnlen : names.length < 2 ^ 64 := by
      rw [decHL_length _ hnames]; omega
    have hcond : (UInt64.ofNat t = mm) ↔ (t == mm.toNat) = true := by
      simp only [beq_iff_eq]
      constructor
      · intro e; rw [← e, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
      · intro e; rw [e, ofNat_toNat_word]
    simp only [List.headD_cons]
    by_cases hc : UInt64.ofNat t = mm
    · have hb : (t == mm.toNat) = true := hcond.mp hc
      simp only [hc, hb, if_true]
      rw [partsRdIW_grow hg1 (by rw [hp2]; exact hrlt), hrw]
      exact Sim.ret ⟨rfl, hS1, hg1⟩
    · have hb : (t == mm.toNat) = false := by simpa using (fun e => hc (hcond.mpr e))
      simp only [hc, hb, if_false, Bool.false_eq_true]
      refine Sim.congr (op := List.findM? (bmfPred names mm.toNat) rs' >>= pure) ?_ (bind_pure _)
      refine Sim.bindK (K := bmfK2) (body := fun r m' => some ([r.headD 0, r.tail.headD 0,
          r.tail.tail.headD 0], m')) rfl (fun _ _ => rfl)
        (ih m1 a1 (ro + 1) (rl - 1) rs' hS1 (hrs'.grow decSR_mono hg1) (hnm.grow (OMono.decHL _ _) hg1)
          (Nat.le_trans hnb hg1.1)) ?_
      rintro r x m' a' ⟨rfl, hS', hg'⟩
      refine Sim.ret ⟨?_, hS', hg1.trans hg'⟩
      cases x <;> rfl

end L.Ind
