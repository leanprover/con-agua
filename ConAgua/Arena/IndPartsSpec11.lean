import ConAgua.Arena.IndPartsSpec10

/-!
# Refinements of `IndParts`, part 11 (lane `indproofs2`, helper `parts`): the member counts

`blockMemberCounts?`: `block_member_counts_find` (the `findM?` over the recursors, through
`rec_target_of`), `block_member_counts_go` (one `block_counts` per former, then the rest). The pool
stays below its top across `block_counts` (`PTop`, so the stage relation is kept: lane
`indproofs`' `blockCounts_refines` gives only the frame).
-/

noncomputable section

set_option experimental.vcgen true

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
  rcases hal : allocW m (l + 1) with _ | ⟨q, m1⟩ <;> rw [hal] at h
  · cases h
  simp only at h
  rcases hcp : copyW (n - 1) (m1.set64 IW q x) (q + 1) o l with _ | m2 <;> rw [hcp] at h
  · cases h
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
    obtain ⟨rs1, m1, hrec, hh⟩ := ipK_inv hh (by simp [piBK2])
    rw [piBK2_some] at hh
    obtain ⟨r2, m2, hcons, hh⟩ := ipK_inv hh (by simp [piBK3])
    rw [piBK3_some] at hh
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
  rcases hp : piBW n m CWF (rdW (m.arr64 EREC) (cvT + 3)) with _ | ⟨rs, m1⟩ <;> rw [hp] at h
  · simp [bchW.bchK1, bcK] at h
  rw [bchK1_some] at h
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

theorem bmfK2_some (m1 : Mem) (r1 : List Word) : bmfK2 (some (r1, m1)) =
    some ([r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0], m1) := rfl
attribute [ind_grind] bmfK2_some

/-- **`block_member_counts_find` is its model `bmfW`** (generated). -/
l_model bmf_spec (p : Prog) (hP : IndPartsProg4 p)
  fns [hP.mcFind ↦ bmfW]
  specs [recTargetOf_spec p hP.view hP.find hP.target hP.strip hP.ad n]
  grind [ind_grind] finish [rdW_eq] gen 20

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
      (fun r x m' a' => r = encONN (x.map fun q => (q.2.1, q.2.2.1)) ∧
        (∀ q, x = some q → q.2.1 < 2 ^ 64 ∧ q.2.2.1 < 2 ^ 64) ∧ StageR dn vis fe m' a' ∧
        IWGrow m m') := by
  induction n with
  | zero => intro m a ro rl rs _ _ _ _ r m' e; rw [bmfW.eq_1] at e; cases e
  | succ n ih =>
    intro m a ro rl rs hS hrs hnm hnb
    by_cases hl : rl = 0
    · rw [bmfW.arm1 n m no nl ro rl mm hl]
      subst hl; rw [partsPSl_nil hrs]
      exact Sim.ret ⟨rfl, by simp, hS, IWGrow.refl _⟩
    rw [bmfW.arm2 n m no nl ro rl mm hl]
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
    refine Sim.bindK (bmfW.k_rec_target_of.none ..) (fun _ _ => by rw [bmfW.k_rec_target_of.eq_2])
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
      exact Sim.ret ⟨rfl, fun q e => by simp only [Option.some.injEq] at e; subst e; exact ⟨hmb, hrb⟩,
        hS1, hg1⟩
    · have hb : (t == mm.toNat) = false := by simpa using (fun e => hc (hcond.mpr e))
      simp only [hc, hb, if_false, Bool.false_eq_true]
      refine Sim.congr (op := List.findM? (bmfPred names mm.toNat) rs' >>= pure) ?_ (bind_pure _)
      refine Sim.bindK rfl (fun _ _ => by rw [bmfW.k_block_member_counts_find])
        (ih m1 a1 (ro + 1) (rl - 1) rs' hS1 (hrs'.grow decSR_mono hg1) (hnm.grow (OMono.decHL _ _) hg1)
          (Nat.le_trans hnb hg1.1)) ?_
      rintro r x m' a' ⟨rfl, hxb, hS', hg'⟩
      refine Sim.ret ⟨?_, hxb, hS', hg1.trans hg'⟩
      cases x <;> rfl

/-! ## `block_member_counts_go`, `block_member_counts` -/

mutual
/-- **The model of `block_member_counts_go`.** -/
def bmgW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, nPd, k, nC, no, nl, ro, rl, cto, ctl, idx =>
    if ctl = 0 then some ([1, 0, 0], m)
    else bmgK1 n nPd k nC no nl ro rl cto ctl idx (rdW (m.arr64 IW) cto) (bmfW n m no nl ro rl idx)
/-- After `block_member_counts_find`. -/
def bmgK1 (n : Nat) (nPd k nC no nl ro rl cto ctl idx cv : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if 4294967296 ≤ r1.tail.headD 0 ∨ 4294967296 ≤ r1.tail.tail.headD 0 then none
    else bmgK2 n nPd k nC no nl ro rl cto ctl idx
      (bcW n m1 nPd k nC rl cv (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0))
/-- After `block_counts`. -/
def bmgK2 (n : Nat) (nPd k nC no nl ro rl cto ctl idx : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else bmgK3 n (r2.tail.tail.headD 0) (bmgW n m2 nPd k nC no nl ro rl (cto + 1) (ctl - 1) (idx + 1))
/-- After the recursive call. -/
def bmgK3 (n : Nat) (cb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0, 0, 0], m3)
    else bsK3 (consW n m3 cb (r3.tail.headD 0) (r3.tail.tail.headD 0))
end

section arms
variable (n : Nat) (m m1 : Mem) (nPd k nC no nl ro rl cto ctl idx cv cb : Word) (r1 : List Word)
theorem bmgW_nil (h : ctl = 0) : bmgW (n + 1) m nPd k nC no nl ro rl cto ctl idx = some ([1, 0, 0], m) := by
  simp [bmgW, h]
theorem bmgW_cons (h : ctl ≠ 0) : bmgW (n + 1) m nPd k nC no nl ro rl cto ctl idx =
    bmgK1 n nPd k nC no nl ro rl cto ctl idx (rdW (m.arr64 IW) cto) (bmfW n m no nl ro rl idx) := by
  simp [bmgW, h]
theorem bmgK1_ok (h : ¬ (4294967296 ≤ r1.tail.headD 0 ∨ 4294967296 ≤ r1.tail.tail.headD 0)) :
    bmgK1 n nPd k nC no nl ro rl cto ctl idx cv (some (r1, m1)) = bmgK2 n nPd k nC no nl ro rl cto ctl idx
      (bcW n m1 nPd k nC rl cv (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0)) := by
  simp only [bmgK1]; exact if_neg h
theorem bmgK2_fail (h : r1.headD 0 = 0) :
    bmgK2 n nPd k nC no nl ro rl cto ctl idx (some (r1, m1)) = some ([0, 0, 0], m1) := by
  simp only [bmgK2]; exact if_pos h
theorem bmgK2_ok (h : r1.headD 0 ≠ 0) :
    bmgK2 n nPd k nC no nl ro rl cto ctl idx (some (r1, m1)) =
      bmgK3 n (r1.tail.tail.headD 0) (bmgW n m1 nPd k nC no nl ro rl (cto + 1) (ctl - 1) (idx + 1)) := by
  simp only [bmgK2]; exact if_neg h
theorem bmgK3_fail (h : r1.headD 0 = 0) : bmgK3 n cb (some (r1, m1)) = some ([0, 0, 0], m1) := by
  simp only [bmgK3]; exact if_pos h
theorem bmgK3_ok (h : r1.headD 0 ≠ 0) : bmgK3 n cb (some (r1, m1)) =
    bsK3 (consW n m1 cb (r1.tail.headD 0) (r1.tail.tail.headD 0)) := by
  simp only [bmgK3]; exact if_neg h
end arms
attribute [ind_grind] bmgW_nil bmgW_cons bmgK1_ok bmgK2_fail bmgK2_ok bmgK3_fail bmgK3_ok

theorem bmg_spec (p : Prog) (hP : IndPartsProg4 p) (n : Nat) :
    ∀ (s₀ : St) (nPd k nC no nl ro rl cto ctl idx : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_member_counts_go" [nPd, k, nC, no, nl, ro, rl, cto, ctl, idx]
    ⦃fun r s' => LocEq s' s₀ ∧ bmgW n s₀.mem nPd k nC no nl ro rl cto ctl idx = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ nPd k nC no nl ro rl cto ctl idx; rw [invoke_eq _ hP.mcGo]
    simp only [callFn, blockMemberCountsGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nPd k nC no nl ro rl cto ctl idx
    rw [invoke_eq _ hP.mcGo]
    simp only [callFn, blockMemberCountsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        bmf_spec p hP n, blockCounts_spec p hP.alloc hP.copy hP.view hP.cons hP.piB hP.bcHead hP.bcPure
          hP.counts n, slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- `block_member_counts`' result `(ok, off, len)` against the twin's `Option (List Nat)`. -/
def NsR (x : Option (List Nat)) (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some ns => r.headD 0 = 1 ∧ DecB (fun m => decNL m (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat) m ns ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m

theorem NsR_three {x : Option (List Nat)} {r : List Word} {m : Mem} (h : NsR x r m) :
    NsR x [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0] m := by cases x <;> exact h

theorem stageR_ptop {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR dn vis fe m a) : PTop m := ⟨hS.2.1, hS.2.2.2.1, hS.2.2.2.2.2⟩

/-- **`block_member_counts_go`'s model refines `blockMemberCounts?` from member `idx`.** -/
theorem bmgW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {nPd k nC no nl ro rl : Word}
    {names : List NIdx} {rs : List (IConstantVal × Nat × Nat × List IRecRule)}
    (h1 : nPd.toNat < 2 ^ 32) (h2 : k.toNat < 2 ^ 32) (h3 : nC.toNat < 2 ^ 32) (h4 : rl.toNat < 2 ^ 32)
    (n : Nat) :
    ∀ (m : Mem) (a : AState) (cto ctl idx : Word) (cvTs : List IConstantVal),
    StageR dn vis fe m a → PSlR decCVp cvTs cto ctl m → PSlR decSR rs ro rl m →
    DecB (fun m => decHL m no.toNat nl.toNat) m names → no.toNat + nl.toNat ≤ iwTop m →
    idx.toNat + ctl.toNat ≤ iwTop m →
    Sim (bmgW n m nPd k nC no nl ro rl cto ctl idx)
      (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs idx.toNat cvTs) a
      (fun r x m' a' => NsR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  induction n with
  | zero => intro m a cto ctl idx cvTs _ _ _ _ _ _ r m' e; simp [bmgW] at e
  | succ n ih =>
    intro m a cto ctl idx cvTs hS hts hrs hnm hnb hix
    by_cases hl : ctl = 0
    · rw [bmgW_nil n m nPd k nC no nl ro rl cto ctl idx hl]
      subst hl; rw [partsPSl_nil hts]
      exact Sim.ret ⟨⟨rfl, by show decNL _ _ _ = _; simp [decNL], by simp⟩, hS, IWGrow.refl _⟩
    rw [bmgW_cons n m nPd k nC no nl ro rl cto ctl idx hl]
    obtain ⟨pc, cv0, ts', rfl, hw, hpb, hcv0, hts'⟩ := partsPSl_cons hts hl
    rw [hw]
    simp only [ConRon.Arena.blockMemberCounts?]
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hrl : rs.length = rl.toNat := (decPL_length _ hrs.1)
    refine Sim.bindK (by simp [bmgK1]) (fun _ _ => by rw [bmgK1]) (bmfW_sim n m a ro rl rs hS hrs hnm hnb) ?_
    rintro r1 x m1 a1 ⟨rfl, hxb, hS1, hg1⟩
    by_cases hbig : 4294967296 ≤ (encONN (x.map fun q => (q.2.1, q.2.2.1))).tail.headD 0 ∨
        4294967296 ≤ (encONN (x.map fun q => (q.2.1, q.2.2.1))).tail.tail.headD 0
    · rw [if_pos hbig]; exact Sim.of_none
    rw [if_neg hbig]
    have h5 : ((encONN (x.map fun q => (q.2.1, q.2.2.1))).tail.headD 0).toNat < 2 ^ 32 := by
      have := mt Or.inl hbig; rw [UInt64.le_iff_toNat_le] at this; simpa using this
    have h6 : ((encONN (x.map fun q => (q.2.1, q.2.2.1))).tail.tail.headD 0).toNat < 2 ^ 32 := by
      have := mt Or.inr hbig; rw [UInt64.le_iff_toNat_le] at this; simpa using this
    rw [hrl]
    have hcv1 : decCVp m1 (UInt64.ofNat pc).toNat = some cv0 := by
      rw [hpw]; exact hcv0.stab (OMono.decCVp _) m1 hg1
    have hb3 : (UInt64.ofNat pc).toNat + 3 < 2 ^ 64 := by
      rw [hpw]
      obtain ⟨w, hw3, -, -⟩ := hd?_some (decCV_type (show decCV (erA (truncM m)) pc = some cv0 from hcv0))
      have := (truncM_er_get hw3).1
      have : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
      omega
    generalize hE : encONN (x.map fun q => (q.2.1, q.2.2.1)) = E at h5 h6
    refine Sim.bindK (by simp [bmgK2]) (fun _ _ => by rw [bmgK2])
      (Q := fun r2 x2 m2 a2 => a2 = a1 ∧ r2 = encONN x2 ∧ (∀ p q, x2 = some (p, q) → q < 2 ^ 64) ∧
        StageR dn vis fe m2 a1 ∧ IWGrow m1 m2) ?_ ?_
    · revert hE
      cases x with
      | none =>
        intro hE; dsimp only; intro r2 m2 e
        obtain ⟨x2, hrun, hr2, hq2, hg2, hf2⟩ := bcW_ok n m1 m2 a1 nPd k nC rl (UInt64.ofNat pc) _ _ _ r2
          cv0 none hS1.1.arena.1 e hcv1 hb3 (by subst hE; rfl) h1 h2 h3 h4 h5 h6 hS1.2.2.2.1 hS1.2.2.2.2.2
        have hP2 := bcW_ptop e (stageR_ptop hS1)
        exact ⟨x2, a1, hrun, rfl, hr2, hq2, stage_frame_iw hS1 hf2 (by rw [← hf2.2.2.1 IW]; exact hP2.1), hg2⟩
      | some q =>
        intro hE; dsimp only; intro r2 m2 e
        obtain ⟨b1, b2⟩ := hxb q rfl
        obtain ⟨x2, hrun, hr2, hq2, hg2, hf2⟩ := bcW_ok n m1 m2 a1 nPd k nC rl (UInt64.ofNat pc) _ _ _ r2
          cv0 (some (q.2.1, q.2.2.1)) hS1.1.arena.1 e hcv1 hb3
          (by subst hE; simp [encONN, UInt64.toNat_ofNat_of_lt' b1, UInt64.toNat_ofNat_of_lt' b2])
          h1 h2 h3 h4 h5 h6 hS1.2.2.2.1 hS1.2.2.2.2.2
        have hP2 := bcW_ptop e (stageR_ptop hS1)
        exact ⟨x2, a1, hrun, rfl, hr2, hq2, stage_frame_iw hS1 hf2 (by rw [← hf2.2.2.1 IW]; exact hP2.1), hg2⟩
    rintro r2 x2 m2 a2 ⟨rfl, rfl, hq2, hS2, hg2⟩
    have hg02 := hg1.trans hg2
    cases x2 with
    | none =>
      simp only [encONN, List.headD_cons, if_true]
      exact Sim.ret ⟨rfl, hS2, hg02⟩
    | some c =>
    obtain ⟨c1, c2⟩ := c
    have hc2 := hq2 c1 c2 rfl
    rw [if_neg (show (encONN (some (c1, c2))).headD 0 ≠ 0 by simp [encONN])]
    have hcl1 : ctl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
    have hcto1 : (cto + 1).toNat = cto.toNat + 1 := by
      have := hts.2; rw [UInt64.toNat_add]; simp; omega
    have hidx1 : (idx + 1).toNat = idx.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hctl1 : (ctl - 1).toNat = ctl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hrec := ih m2 _ (cto + 1) (ctl - 1) (idx + 1) ts' hS2 (hts'.grow (fun _ => OMono.decCVp _) hg02)
      (hrs.grow decSR_mono hg02) (hnm.grow (OMono.decHL _ _) hg02) (Nat.le_trans hnb hg02.1)
      (by rw [hidx1, hctl1]; have := hg02.1; omega)
    rw [hidx1] at hrec
    refine Sim.bindK (by simp [bmgK3]) (fun _ _ => by rw [bmgK3]) hrec ?_
    rintro r3 x3 m3 a3 ⟨hR3, hS3, hg3⟩
    cases x3 with
    | none =>
      have h0 : r3.headD 0 = 0 := hR3
      rw [if_pos h0]
      exact Sim.ret ⟨rfl, hS3, hg02.trans hg3⟩
    | some ns =>
    obtain ⟨h1', hd3, hb3'⟩ := hR3
    rw [if_neg (by rw [h1']; decide)]
    intro r m' e
    rcases h4 : consW n m3 ((encONN (some (c1, c2))).tail.tail.headD 0) (r3.tail.headD 0) (r3.tail.tail.headD 0) with _ | ⟨r4, m4⟩ <;> rw [h4] at e
    · cases e
    rw [bsK3_some] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS4, hg4, hd4, ht4⟩ := consW_stageN h4 hS3 hb3' (hd3.get (OMono.decNL _ _))
    refine ⟨some (c2 :: ns), a3, rfl, ⟨rfl, ?_, by simp only [List.headD_cons, List.tail_cons]; omega⟩, hS4,
      (hg02.trans hg3).trans hg4⟩
    have hc2' : ((encONN (some (c1, c2))).tail.tail.headD 0).toNat = c2 := by
      simp [encONN, UInt64.toNat_ofNat_of_lt' hc2]
    rw [hc2'] at hd4
    exact decNL_decB hd4 (Nat.le_of_eq ht4)

/-- **The model of `block_member_counts`** (at exec fuel `n + 1`). -/
def bmcW (n : Nat) (m : Mem) (nPd k nC no nl ro rl cto ctl : Word) : Option (List Word × Mem) :=
  if 4294967296 ≤ nPd ∨ 4294967296 ≤ k ∨ 4294967296 ≤ nC ∨ 4294967296 ≤ rl then none
  else bmfK2 (bmgW n m nPd k nC no nl ro rl cto ctl 0)

theorem bmc_spec (p : Prog) (hP : IndPartsProg4 p) (n : Nat) (s₀ : St) (nPd k nC no nl ro rl cto ctl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_member_counts" [nPd, k, nC, no, nl, ro, rl, cto, ctl]
    ⦃fun r s' => LocEq s' s₀ ∧ bmcW n s₀.mem nPd k nC no nl ro rl cto ctl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.mc]
  simp only [callFn, blockMemberCounts]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, bmg_spec p hP n] <;>
    finish (gen := 20) [bmcW]

/-- **`block_member_counts` refines `blockMemberCounts?`** from member `0` (through
`rec_target_of`'s and `block_counts`' stubs; the counts and the recursor records' words past
`2^32` a capacity abort): the formers a slice of constants, the recursors the split's records,
both decoded below the tops; the result a number slice decoded below the tops (`NsR`). -/
@[refines ConRon.Arena.blockMemberCounts?]
theorem blockMemberCounts_refines (p : Prog) (hP : IndPartsProg4 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nPd k nC no nl ro rl cto ctl : Word)
    (names : List NIdx) (cvTs : List IConstantVal) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (hS : StageR dn vis fe s₀.mem a₀) (hts : PSlR decCVp cvTs cto ctl s₀.mem)
    (hrs : PSlR decSR rs ro rl s₀.mem) (hnm : DecB (fun m => decHL m no.toNat nl.toNat) s₀.mem names)
    (hnb : no.toNat + nl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_member_counts" [nPd, k, nC, no, nl, ro, rl, cto, ctl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs 0 cvTs) a₀ ∧
      NsR (AM.res (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs 0 cvTs) a₀) r s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs 0 cvTs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (bmc_spec p hP n s₀ nPd k nC no nl ro rl cto ctl) ?_
  rintro r s' ⟨hl, hm⟩
  unfold bmcW at hm
  split at hm
  · cases hm
  rename_i hg
  have b : ∀ w : Word, ¬ 4294967296 ≤ w → w.toNat < 2 ^ 32 := fun w h => by
    rw [UInt64.le_iff_toNat_le] at h; simpa using h
  have hsim := bmgW_sim (b nPd (fun h => hg (Or.inl h))) (b k (fun h => hg (Or.inr (Or.inl h))))
    (b nC (fun h => hg (Or.inr (Or.inr (Or.inl h))))) (b rl (fun h => hg (Or.inr (Or.inr (Or.inr h))))) n
    s₀.mem a₀ cto ctl 0 cvTs hS hts hrs hnm hnb (by simp; have := hts.2; omega)
  rcases hb : bmgW n s₀.mem nPd k nC no nl ro rl cto ctl 0 with _ | ⟨r1, m1⟩ <;> rw [hb] at hm
  · cases hm
  rw [bmfK2_some] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨hok, hR, hS', hg'⟩ := Sim.run hsim hb
  exact ⟨hl, hok, NsR_three hR, hS', hg'⟩

end L.Ind
