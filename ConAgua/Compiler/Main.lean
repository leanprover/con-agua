module

public import ConAgua.Compiler.Correct

@[expose] public section

/-!
# The end-to-end compiler theorem

`compile_correct`: run from `ca_enter` on a machine state that holds L's memory `m` in the
layout `G`, the entry arguments in the table and `N` units of fuel in `rsi`, every run of the
compiled program returns to the caller with the callee-saved registers restored, and either
reports `exhausted` (`rdx = 1`) or reports exactly what `L.run p N entry args m` says:
`rdx = 0`, the results in the result registers (`rax`, `rdi`, `r8`, …; see `resReg`) and, past
the sixth, in the table's result area (`Layout.resAddr`), and the final memory in the layout, or `rdx = 2` for an error
(never for running out of fuel, which only `rdx = 1` reports).
-/

namespace L.Compiler

open L

/-- What the harness sees after `ca_enter` returns, against L's result. -/
def OutcomeRel (G : Layout) : Except Err (List Word × Mem) → MachineData → Prop
  | .ok (rs, m'), s => s.regs.rdx = 0 ∧ ResOut G G.tab.nres rs s ∧ MemRel G m' s.dmem
  | .error .outOfFuel, _ => False
  | .error _, s => s.regs.rdx = 2

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14 Reg64s.set64_r15 Reg64s.set64_rbp

theorem mem_of_lookup {p : Prog} {f : FnName} {fd : FunDecl} (h : p.lookup f = some fd) : (f, fd) ∈ p := by
  induction p with
  | nil => simp at h
  | cons q p ih =>
    obtain ⟨f', fd'⟩ := q
    simp only [List.lookup_cons] at h
    split at h
    · rename_i heq; cases h; have : f = f' := by simpa using heq
      subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem toBitVec_eq_A (x : UInt64) : x.toBitVec = A x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [A]

theorem A_toNat (b : BitVec 64) : A b.toNat = b := by simp [A]

theorem A_add8 (x : Nat) : A x + 8 = A (x + 8) := A_add x 8

theorem A_sub8 (x : Nat) (h : 8 ≤ x) (hx : x < 2 ^ 64) : A x - 8 = A (x - 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [A, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  omega

/-- Normal form of machine addresses: `A n` for a natural number `n`. -/
macro "addr_simp" : tactic => `(tactic| simp only [Reg64s.set64_rsp, Reg64s.set64_r15, Reg64s.set64_r14,
  Reg64s.set64_rbp, Reg64s.get64_rbp, Reg64s.get64_rsp, UInt64.toBitVec_ofBitVec, toBitVec_eq_A,
  UInt64.toNat_mk', A_toNat, A_add, A_add8])

theorem compile_correct [Host] (p : Prog) (entry : FnName) (G : Layout) (hG : G.Ok)
    (hwf : Prog.wf G.tab p = true) (k0 : Nat) (hcode : Code (compileProg G.tab p entry) k0)
    (fd : FunDecl) (hentry : p.lookup entry = some fd)
    (args : List Word) (hargs : args.length = fd.nparams) (hnargs : G.nargs = args.length)
    (m : Mem) (N : Nat) (d : MachineData) (ra : Word)
    (hT : d.regs.rdi.toNat = G.T) (hN : d.regs.rsi.toNat = N)
    (hmem : MemRel G m d.dmem) (hroom : G.lo + 8 ≤ G.hi)
    (htop : rdW d.dmem (A G.T) = some (UInt64.ofNat G.hi))
    (hargv : ∀ i (h : i < args.length), rdW d.dmem (A (G.T + G.tab.args.toNat + 8 * i)) = some args[i])
    (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra)
    (hcs : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 →
      (d.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x)
    (hcs24 : 24 ≤ d.regs.rsp.toNat) (hcs8 : d.regs.rsp.toNat + 8 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data))
      d (label enterL) := by
  simp only [Prog.wf_eq, Prog.wfSpec, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hfds, _⟩, hTab⟩ := hwf
  have hwfp : ∀ f fd, p.lookup f = some fd → FunDecl.wf p G.tab fd = true :=
    fun f fd hl => hfds (f, fd) (mem_of_lookup hl)
  have hProg : ∀ f fd, p.lookup f = some fd → ∃ kf, Code (compileFn G.tab f fd) kf :=
    fun f fd hl => code_of_lookup p _ hcode.right hl
  obtain ⟨_, hFun⟩ := execSim_all hG hTab p hwfp hProg N
  obtain ⟨kf, hkf⟩ := hProg entry fd hentry
  have hlF : label (fnL entry) = at_ kf := by rw [Code.label (i := 0) hkf rfl]; rfl
  have ht := hcode.left
  simp only [trampoline, burnFuel, List.cons_append, List.nil_append] at ht
  have hlEnter : label enterL = at_ (k0 + 0) := Code.label (i := 0) ht rfl
  have hlExh : label exhaustedL = at_ (k0 + 14) := Code.label (i := 14) ht rfl
  have hlErr : label errorL = at_ (k0 + 17) := Code.label (i := 17) ht rfl
  have hlFin : label finishL = at_ (k0 + 19) := Code.label (i := 19) ht rfl
  rw [hlEnter]
  -- the common exit `ca_finish`: restore the caller's stack and registers, return
  have hfin : ∀ s : MachineData, s.regs.rbp.toNat = d.regs.rsp.toNat - 24 →
      rdW s.dmem (A (d.regs.rsp.toNat - 24)) = some d.regs.r15 →
      rdW s.dmem (A (d.regs.rsp.toNat - 24 + 8)) = some d.regs.r14 →
      rdW s.dmem (A (d.regs.rsp.toNat - 24 + 8 + 8)) = some d.regs.rbp →
      rdW s.dmem (A (d.regs.rsp.toNat - 24 + 8 + 8 + 8)) = some ra →
      (s.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) s) →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s (at_ (k0 + 19)) := by
    intro s hbp h15 h14 hbp' hra' hout
    refine ev_label (Code.get (i := 19) ht rfl) ?_
    refine ev_movRR (Code.get (i := 20) ht rfl) ?_
    refine ev_pop (Code.get (i := 21) ht rfl) (v := d.regs.r15) ?_ ?_
    · addr_simp; rw [hbp]; exact h15
    refine ev_pop (Code.get (i := 22) ht rfl) (v := d.regs.r14) ?_ ?_
    · addr_simp; rw [hbp]; exact h14
    refine ev_pop (Code.get (i := 23) ht rfl) (v := d.regs.rbp) ?_ ?_
    · addr_simp; rw [hbp]; exact hbp'
    refine ev_ret (Code.get (i := 24) ht rfl) (ra := ra) ?_ ?_
    · addr_simp; rw [hbp]; exact hra'
    refine Eventually.done _ ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · addr_simp; rw [hbp]; simp only [A, BitVec.toNat_ofNat]; omega
    · simp
    · simp
    · simp
    · rcases hout with h | h
      · exact Or.inl (by simpa using h)
      · right
        revert h
        generalize run p N entry args m = res
        rcases res with e | ⟨r, m'⟩
        · cases e <;> simp [OutcomeRel]
        · simp only [OutcomeRel, Reg64s.set64_rsp, Reg64s.set64_r15, Reg64s.set64_r14, Reg64s.set64_rbp]
          rintro ⟨h1, ⟨h2, h4⟩, h3⟩
          exact ⟨h1, ⟨h2.congr rfl rfl rfl rfl rfl rfl, h4⟩, h3⟩
  have hsp0 := hcs24
  -- the three pushes
  have hmap : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat → (rdW d.dmem (A x)).isSome → True :=
    fun _ _ _ _ => trivial
  suffices H : ∀ s3 : MachineData, s3.regs.rsp.toNat = d.regs.rsp.toNat - 24 →
      s3.regs.rdi = d.regs.rdi → s3.regs.rsi = d.regs.rsi →
      Only (d.regs.rsp.toNat - 24) d.regs.rsp.toNat d.dmem s3.dmem →
      rdW s3.dmem (A (d.regs.rsp.toNat - 24)) = some d.regs.r15 →
      rdW s3.dmem (A (d.regs.rsp.toNat - 24 + 8)) = some d.regs.r14 →
      rdW s3.dmem (A (d.regs.rsp.toNat - 24 + 8 + 8)) = some d.regs.rbp →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s3 (at_ (k0 + 0 + 1 + 1 + 1 + 1)) by
    have hm : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x + 8 ≤ d.regs.rsp.toNat → (rdW d.dmem (A x)).isSome :=
      fun x h1 h2 => isSome_rdW fun j hj => by rw [A_add]; exact (hcs _ (by omega) (by omega)).1
    have e1 : d.regs.rsp.toBitVec - 8 = A (d.regs.rsp.toNat - 8) := by
      rw [toBitVec_eq_A, A_sub8 _ (by omega) (by omega)]
    refine ev_label (Code.get (i := 0) ht rfl) ?_
    refine ev_push (Code.get (i := 1) ht rfl) ?_ ?_
    · rw [e1]; exact hm _ (by omega) (by omega)
    have e2 : (UInt64.ofBitVec (d.regs.rsp.toBitVec - 8)).toBitVec - 8 = A (d.regs.rsp.toNat - 16) := by
      rw [UInt64.toBitVec_ofBitVec, e1, A_sub8 _ (by omega) (by omega)]; congr 1
    refine ev_push (Code.get (i := 2) ht rfl) ?_ ?_
    · simp only [Reg64s.set64_rsp]; rw [e2, e1, rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hm _ (by omega) (by omega)
    have e3 : (UInt64.ofBitVec (A (d.regs.rsp.toNat - 16))).toBitVec - 8 = A (d.regs.rsp.toNat - 24) := by
      rw [UInt64.toBitVec_ofBitVec, A_sub8 _ (by omega) (by omega)]; congr 1
    simp only [Reg64s.set64_rsp]
    rw [e2, e1]
    refine ev_push (Code.get (i := 3) ht rfl) ?_ ?_
    · simp only [Reg64s.set64_rsp]; rw [e3, rdW_wrW_A (by omega) (by omega) (by omega),
        rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hm _ (by omega) (by omega)
    simp only [Reg64s.set64_rsp]
    rw [e3]
    refine H _ ?_ (by simp) (by simp) ?_ ?_ ?_ ?_
    · simp only [UInt64.toNat_ofBitVec, A, BitVec.toNat_ofNat]; omega
    · exact (Only.wrW (by omega)).union (a := d.regs.rsp.toNat - 24) (b := d.regs.rsp.toNat)
        ((Only.wrW (by omega)).union (a := d.regs.rsp.toNat - 24) (b := d.regs.rsp.toNat - 8)
          (Only.wrW (by omega)) (by omega) (by omega) (by omega) (by omega))
        (by omega) (by omega) (by omega) (by omega)
    · simp [rdW_wrW_same]
    · rw [rdW_wrW_A (by omega) (by omega) (by omega), show d.regs.rsp.toNat - 24 + 8 = d.regs.rsp.toNat - 16 by omega]
      simp [rdW_wrW_same]
    · rw [rdW_wrW_A (by omega) (by omega) (by omega), rdW_wrW_A (by omega) (by omega) (by omega),
        show d.regs.rsp.toNat - 24 + 8 + 8 = d.regs.rsp.toNat - 8 by omega]
      simp [rdW_wrW_same]
  intro s3 h3sp h3di h3si h3O h3r15 h3r14 h3bp
  have hTabArgs : G.T + G.tab.args.toNat + 8 * args.length = G.tabEnd := by
    simp [Layout.tabEnd, Tab.args, hnargs]; omega
  have hTe := hG.tab_end
  -- the table cell `[T]` is outside the caller's stack
  have htop3 : rdW s3.dmem (A G.T) = some (UInt64.ofNat G.hi) := by
    rw [← htop]
    refine rdW_congr fun j hj => ?_
    rw [A_add]
    refine h3O.same _ (by simp [Layout.tabEnd] at hTe; omega) ?_
    refine Classical.byContradiction fun hc => ?_
    simp only [not_or, Nat.not_lt] at hc
    exact (hcs (G.T + j) (by omega) (by omega)).2.2.2 ⟨by omega, by simp [Layout.tabEnd]; omega⟩
  suffices H : ∀ s8 : MachineData, s8.regs.rsp.toNat = G.hi → s8.regs.rbp.toNat = d.regs.rsp.toNat - 24 →
      s8.regs.r15.toNat = G.T → s8.regs.r14.toNat = N → s8.regs.rsi.toNat = G.T + G.tab.args.toNat →
      s8.dmem = s3.dmem →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s8
        (at_ (k0 + 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) by
    refine ev_movRR (Code.get (i := 4) ht rfl) ?_
    refine ev_movRR (Code.get (i := 5) ht rfl) ?_
    refine ev_movRR (Code.get (i := 6) ht rfl) ?_
    refine ev_movRM (Code.get (i := 7) ht rfl) ⟨by simp [Tab.stackTop], by simp [Tab.stackTop]⟩
      (v := UInt64.ofNat G.hi) ?_ ?_
    · simp [Tab.stackTop, h3di, hT]; exact htop3
    refine ev_lea (Code.get (i := 8) ht rfl) ⟨by simp [Tab.args]; omega, by simp [Tab.args]; simp [maxOff] at hTab; omega⟩ ?_
    refine H _ ?_ ?_ ?_ ?_ ?_ rfl
    · simp [UInt64.toNat_ofNat_of_lt' (show G.hi < UInt64.size by simp [UInt64.size]; exact hG.hi_le)]
    · simp [h3sp]
    · simp [h3di, hT]
    · simp [h3si, hN]
    · simp only [Reg64s.set64_rsi, Reg64s.set64_rsp, Reg64s.set64_r14, Reg64s.set64_r15, Reg64s.set64_rbp,
        Reg64s.get64_r15, Reg64s.get64_rdi, UInt64.toNat_ofBitVec, UInt64.toNat_toBitVec, A, BitVec.toNat_ofNat, h3di, hT]
      have : G.T + G.tab.args.toNat < 2 ^ 64 := by omega
      omega
  intro s8 h8sp h8bp h815 h814 h8si h8m
  have hhi := hG.hi_le
  -- the caller's stack survives any change outside it
  have hcsw : ∀ dm : DataMem, (∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 →
      dm.get? (A x) = s3.dmem.get? (A x)) →
      rdW dm (A (d.regs.rsp.toNat - 24)) = some d.regs.r15 ∧
      rdW dm (A (d.regs.rsp.toNat - 24 + 8)) = some d.regs.r14 ∧
      rdW dm (A (d.regs.rsp.toNat - 24 + 8 + 8)) = some d.regs.rbp ∧
      rdW dm (A (d.regs.rsp.toNat - 24 + 8 + 8 + 8)) = some ra := by
    intro dm hdm
    have hc : ∀ y, d.regs.rsp.toNat - 24 ≤ y → y + 8 ≤ d.regs.rsp.toNat + 8 → rdW dm (A y) = rdW s3.dmem (A y) :=
      fun y h1 h2 => rdW_congr fun j hj => by rw [A_add]; exact hdm _ (by omega) (by omega)
    refine ⟨by rw [hc _ (by omega) (by omega)]; exact h3r15, by rw [hc _ (by omega) (by omega)]; exact h3r14,
      by rw [hc _ (by omega) (by omega)]; exact h3bp, ?_⟩
    rw [hc _ (by omega) (by omega), h3O.rdW_eq (by omega) (by omega),
      show d.regs.rsp.toNat - 24 + 8 + 8 + 8 = d.regs.rsp.toNat by omega]
    exact hra
  have hexit : ∀ s : MachineData, s.regs.rbp.toNat = d.regs.rsp.toNat - 24 →
      (∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 → s.dmem.get? (A x) = s3.dmem.get? (A x)) →
      (s.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) s) →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s (label finishL) := by
    intro s hbp hdm hout
    obtain ⟨w1, w2, w3, w4⟩ := hcsw s.dmem hdm
    rw [hlFin]; exact hfin s hbp w1 w2 w3 w4 hout
  -- the exhausted exit: `rdx := 1`
  have hexh : ∀ s : MachineData, s.regs.rbp.toNat = d.regs.rsp.toNat - 24 →
      (∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 → s.dmem.get? (A x) = s3.dmem.get? (A x)) →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s (label exhaustedL) := by
    intro s hbp hdm
    rw [hlExh]
    refine ev_label (Code.get (i := 14) ht rfl) ?_
    refine ev_movRI (Code.get (i := 15) ht rfl) ?_
    refine ev_jmp (Code.get (i := 16) ht rfl) ?_
    exact hexit _ (by simp [hbp]) hdm (Or.inl (by simp))
  have hs8 : 8 ≤ G.hi := by omega
  refine ev_sub1 (Code.get (i := 9) ht rfl) fun st hst => ?_
  refine ev_jcc (Code.get (i := 10) ht rfl) (fun hcc => ?_) (fun hcc => ?_)
  · exact hexh _ (by simp [h8bp]) (fun x _ _ => by simp [h8m])
  · simp only [CondCode.interp] at hcc
    rw [hst] at hcc
    have hN0 : s8.regs.r14 ≠ 0 := by intro h; simp [h] at hcc
    have hpos : 0 < s8.regs.r14.toNat := by
      rcases Nat.eq_zero_or_pos s8.regs.r14.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hN0
      · exact h
    have hcall8 : (UInt64.ofBitVec (s8.regs.get64 .r14 - 1)).toNat = N - 1 := by
      have := u64_sub_one_toNat hpos; simp only [Reg64s.get64_r14]; rw [← h814]; exact this
    have e1 : s8.regs.rsp.toBitVec - 8 = A (G.hi - 8) := by
      rw [toBitVec_eq_A, h8sp, A_sub8 _ hs8 hhi]
    refine ev_call (Code.get (i := 11) ht rfl) ?_ ?_
    · simp only [Reg64s.set64_r14]; rw [e1]
      exact isSome_rdW fun j hj => by
        rw [A_add, h8m]; exact h3O.grows _ (hmem.stack _ ⟨by omega, by omega⟩)
    rw [hlF]
    simp only [Reg64s.set64_r14, Reg64s.set64_rsp]
    rw [e1]
    -- facts about the argument cells (in the table, so outside both stacks)
    have hcell : ∀ i, i < args.length → ∀ j < 8, G.InTab (G.T + G.tab.args.toNat + 8 * i + j) := by
      intro i hi j hj
      exact ⟨by omega, by omega⟩
    have hcellS : ∀ i, i < args.length → G.T + G.tab.args.toNat + 8 * i + 8 ≤ G.lo ∨
        G.hi ≤ G.T + G.tab.args.toNat + 8 * i := by
      intro i hi
      have h0 := hG.notStack_of_tab (hcell i hi 0 (by omega))
      simp only [Layout.InStack, not_and, Nat.not_lt] at h0
      by_cases hlo : G.T + G.tab.args.toNat + 8 * i < G.lo
      · left
        refine Classical.byContradiction fun hc => ?_
        exact hG.notStack_of_tab (hcell i hi (G.lo - (G.T + G.tab.args.toNat + 8 * i)) (by omega))
          ⟨by omega, by omega⟩
      · right; exact h0 (by omega)
    have hm3 : MemRel G m s3.dmem := hmem.only' hG h3O fun x h1 h2 =>
      ⟨(hcs x (by omega) (by omega)).2.2.2, (hcs x (by omega) (by omega)).2.2.1⟩
    refine hFun entry fd kf hentry hkf args ⟨m, Locals.init []⟩ _
      (UInt64.ofBitVec (at_ (k0 + 11 + 1)).toBitVec) _ hargs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [UInt64.toNat_mk', A_toNat]
      rw [rdW_wrW_same]
    · intro i hi
      simp only [h8si]
      have hc := hcellS i hi
      rw [rdW_wrW_A (by omega) (by omega) (by omega), h8m, ← hargv i hi, h3O.rdW_eq (by omega) ?_]
      refine Classical.byContradiction fun hc' => ?_
      simp only [not_or, Nat.not_le, Nat.not_lt] at hc'
      by_cases hb : G.T + G.tab.args.toNat + 8 * i ≤ d.regs.rsp.toNat - 24
      · exact (hcs (d.regs.rsp.toNat - 24) (Nat.le_refl _) (by omega)).2.2.2
          (by have := hcell i hi (d.regs.rsp.toNat - 24 - (G.T + G.tab.args.toNat + 8 * i)) (by omega)
              rw [show G.T + G.tab.args.toNat + 8 * i + (d.regs.rsp.toNat - 24 - (G.T + G.tab.args.toNat + 8 * i))
                = d.regs.rsp.toNat - 24 by omega] at this
              exact this)
      · exact (hcs (G.T + G.tab.args.toNat + 8 * i) (by omega) (by omega)).2.2.2
          (by have := hcell i hi 0 (by omega); simpa using this)
    · simp only [UInt64.toNat_mk', A_toNat, h8si]
      rcases Nat.eq_zero_or_pos args.length with h0 | hpos
      · exact Or.inl h0
      · have hc := hcellS 0 hpos
        rcases hc with hc | hc
        · right; right
          refine Classical.byContradiction fun hc' => ?_
          exact hG.notStack_of_tab (x := G.lo) ⟨by omega, by omega⟩ ⟨Nat.le_refl _, by omega⟩
        · right; left; simp only [A, BitVec.toNat_ofNat]; omega
    · simp only [h8si]; omega
    · simp only [UInt64.toNat_mk', A_toNat, A, BitVec.toNat_ofNat]; omega
    · simp only [UInt64.toNat_mk', A_toNat, A, BitVec.toNat_ofNat]; omega
    · exact h815
    · rw [h8m]
      exact hm3.only hG (Only.wrW (x := G.hi - 8) (by omega)) fun x h1 h2 => ⟨by omega, by omega⟩
    · simp only [UInt64.toNat_mk']
      have := u64_sub_one_toNat hpos
      simp only [Reg64s.get64_r14] at hcall8 ⊢
      rw [show (s8.regs.r14.toBitVec - 1) = (s8.regs.r14 - 1).toBitVec from rfl]
      simp only [UInt64.toNat_toBitVec]
      omega
    all_goals
      have hcsS : ∀ dm : DataMem, Pres G (G.hi - 8) (wrW s8.dmem (A (G.hi - 8))
          (at_ (k0 + 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)).toBitVec) dm →
          ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 → dm.get? (A x) = s3.dmem.get? (A x) := by
        intro dm hP x h1 h2
        have hx := hcs x (by omega) (by omega)
        have hxs : x < G.lo ∨ G.hi ≤ x := by
          simp only [Layout.InStack, not_and, Nat.not_lt] at hx
          by_cases h : G.lo ≤ x
          · exact Or.inr (hx.2.1 h)
          · exact Or.inl (by omega)
        rw [hP.same x (by omega) (by omega) hx.2.2.1 (fun hr => hx.2.2.2 hr.tab) (fun hg => hx.2.2.2 hg.tab), get?_wrW_A (by omega) (by omega) (by omega), h8m]
    · -- the entry function returned
      intro r σ' d' hinv hm' hloc hrsp' hrbp' hr15' hr14' hrax' hpres'
      simp only [UInt64.toBitVec_ofBitVec, Int64.ofBitVec_toBitVec]
      refine ev_movRI (Code.get (i := 12) ht rfl) ?_
      refine ev_jmp (Code.get (i := 13) ht rfl) ?_
      simp only [UInt64.toNat_mk', A_toNat] at hpres'
      have hsz : (A (G.hi - 8)).toNat = G.hi - 8 := by simp only [A, BitVec.toNat_ofNat]; omega
      rw [hsz] at hpres'
      refine hexit _ (by simp [hrbp', h8bp]) (fun x h1 h2 => hcsS _ hpres' x h1 h2) (Or.inr ?_)
      have hrun : run p N entry args m = .ok (r, σ'.mem) := by simp [run, hinv, Except.map]
      rw [hrun]
      exact ⟨by simp, ⟨hrax'.1.congr rfl rfl rfl rfl rfl rfl, hrax'.2⟩, hm'⟩
    · -- an error
      intro d' ⟨x, hx, hne⟩ hG'
      simp only [UInt64.toNat_mk', A_toNat] at hG'
      have hsz : (A (G.hi - 8)).toNat = G.hi - 8 := by simp only [A, BitVec.toNat_ofNat]; omega
      rw [hsz] at hG'
      rw [hlErr]
      refine ev_label (Code.get (i := 17) ht rfl) ?_
      refine ev_movRI (Code.get (i := 18) ht rfl) ?_
      obtain ⟨w1, w2, w3, w4⟩ := hcsw _ (fun y h1 h2 => hcsS _ hG'.mem y h1 h2)
      refine hfin _ (by simp [hG'.rbp, h8bp]) w1 w2 w3 w4 (Or.inr ?_)
      have hrun : run p N entry args m = .error x := by simp [run, hx, Except.map]
      rw [hrun]
      cases x <;> simp_all [OutcomeRel]
    · -- out of fuel or stack
      intro d' hG'
      simp only [UInt64.toNat_mk', A_toNat] at hG'
      have hsz : (A (G.hi - 8)).toNat = G.hi - 8 := by simp only [A, BitVec.toNat_ofNat]; omega
      rw [hsz] at hG'
      exact hexh _ (by simp [hG'.rbp, h8bp]) (fun y h1 h2 => hcsS _ hG'.mem y h1 h2)
  

end L.Compiler
