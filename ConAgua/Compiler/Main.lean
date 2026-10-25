module

public import ConAgua.Compiler.Correct
public import ConAgua.Compiler.WFFast

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
  | .error e, s => s.regs.rdx = 2 ∧ s.regs.rax = e.code

theorem OutcomeRel.error {G : Layout} {e : Err} (he : e ≠ .outOfFuel) {s : MachineData}
    (h2 : s.regs.rdx = 2) (hr : s.regs.rax = e.code) : OutcomeRel G (.error e) s := by
  cases e
  · exact absurd rfl he
  all_goals exact ⟨h2, hr⟩

/-- `d'` agrees with `d` outside the layout's stack, arrays and table and outside the 24 bytes
below `sp`, and has every byte `d` has (inside the trampoline, after its stores). -/
structure MemFrameT (G : Layout) (sp : Nat) (d d' : DataMem) : Prop where
  grows : ∀ y, (d.get? y).isSome → (d'.get? y).isSome
  same : ∀ x < 2 ^ 64, ¬ G.InStack x → ¬ G.InArr x → ¬ G.InTab x → (x < sp - 24 ∨ sp ≤ x) →
    d'.get? (A x) = d.get? (A x)

/-- `d'` agrees with `d` outside the layout's stack, arrays and table, outside the 24 bytes below
`sp` (the trampoline's saved `rbp`, `r14`, `T`) and outside the 32 bytes past the table (its saved
`r15`, `rbx`, `r12`, `r13`), and has every byte `d` has. -/
structure MemFrame (G : Layout) (sp : Nat) (d d' : DataMem) : Prop where
  grows : ∀ y, (d.get? y).isSome → (d'.get? y).isSome
  same : ∀ x < 2 ^ 64, ¬ G.InStack x → ¬ G.InArr x → ¬ G.InTab x → (x < sp - 24 ∨ sp ≤ x) →
    (x < G.tabEnd ∨ G.tabEnd + 32 ≤ x) → d'.get? (A x) = d.get? (A x)

/-- The registers the trampoline keeps in its save area besides `r15`: `rbx`, `r12`, `r13` hold
their values from `r0`. -/
def CalleeKept (r0 r : Reg64s) : Prop := r.rbx = r0.rbx ∧ r.r12 = r0.r12 ∧ r.r13 = r0.r13

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

theorem loadArgs_length (tab : Tab) : ∀ (i : Nat) (rs : List Reg64), (loadArgs tab i rs).length = rs.length
  | _, [] => rfl
  | i, _ :: rs => by simp [loadArgs, loadArgs_length tab (i + 1) rs]

/-- The entry's arguments from the table into the registers `rs` (`loadArgs`). -/
theorem sim_loadArgs [Host] {G : Layout} (tab : Tab) (hT : tab = G.tab) (vs : List Word)
    (Q : MachineState → Prop) :
    ∀ (rs : List Reg64) (i k : Nat) (s : MachineData), Code (loadArgs tab i rs) k → s.regs.r15.toNat = G.T →
    (∀ r ∈ rs, r ∈ allocRegs) → rs.Nodup → i + rs.length ≤ vs.length →
    tab.args.toNat + 8 * (i + rs.length) < 2 ^ 31 →
    (∀ j (h : j < vs.length), rdW s.dmem (A (G.T + tab.args.toNat + 8 * j)) = some vs[j]) →
    (∀ s', s'.dmem = s.dmem → (∀ r, r ∉ rs → s'.regs.get64 r = s.regs.get64 r) →
      (∀ j, j < rs.length → s'.regs.get64 (rs.getD j .rax) = (vs.getD (i + j) 0).toBitVec) →
      Ev Q s' (at_ (k + rs.length))) →
    Ev Q s (at_ k) := by
  intro rs
  induction rs with
  | nil =>
    exact fun i k s _ _ _ _ _ _ _ hK => hK s rfl (fun _ _ => rfl) (fun j h => absurd h (by simp))
  | cons r rs ih =>
    intro i k s hc h15 hrs hnd hlen hoff hv hK
    simp only [loadArgs] at hc
    simp only [List.length_cons] at hlen hoff
    have hr := hrs r List.mem_cons_self
    have hnr : r ∉ rs := (List.nodup_cons.mp hnd).1
    have harg : 0 ≤ tab.args := by simp only [Tab.args]; omega
    refine ev_movRM hc.head ⟨by omega, by omega⟩ (v := vs[i]) ?_ ?_
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, h15, ← hv i (by omega)]
      congr 2; omega
    obtain ⟨h1, h2, h3, h4⟩ := set64_alloc_fields (R := s.regs) hr vs[i].toBitVec
    refine ih (i + 1) (k + 1) _ hc.tail (by simp only [h4]; exact h15)
      (fun r' h => hrs r' (List.mem_cons_of_mem _ h)) (List.nodup_cons.mp hnd).2 (by omega) (by omega) hv ?_
    intro s' hd hk hreg
    refine ev_congr (hK s' hd (fun r' hr' => ?_) (fun j hj => ?_)) (by simp; omega)
    · rw [hk r' (fun h => hr' (List.mem_cons_of_mem _ h)), rget_set, if_neg (fun (e : r' = r) => hr' (e ▸ List.mem_cons_self))]
    · cases j with
      | zero =>
        simp only [List.getD_cons_zero, Nat.add_zero]
        rw [hk r hnr, rget_set, if_pos rfl]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < vs.length by omega)]
      | succ j =>
        have := hreg j (by simpa using hj)
        simpa [show i + 1 + j = i + (j + 1) by omega] using this

/-- The frames in `Prog.skt` fit the frame bound of well-formed functions. -/
theorem skOf_skt_lt {p : Prog} {tab : Tab} (entry : FnName)
    (hwf : ∀ f fd, (f, fd) ∈ p → FunDecl.wf p tab fd = true) (g : FnName) :
    8 * skOf (Prog.skt p entry) g + 8 < maxOff := by
  unfold skOf
  cases h : (Prog.skt p entry).find (nameCode g) with
  | none => simp [maxOff]
  | some v =>
    obtain ⟨f, fd, hm, -, -, rfl⟩ := Prog.skt_spec h
    have hw := hwf f fd hm
    simp only [FunDecl.wf_eq, FunDecl.wfSpec, Bool.and_eq_true, decide_eq_true_eq] at hw
    have := tempsS_le (fnAlloc fd) (Stmt.nret fd.body) fd.body
    simp only [Option.getD_some, fnFrame]
    simp only [frameWords] at hw
    omega

theorem enter_core [Host] (p : Prog) (entry : FnName) (G : Layout) (hG : G.Ok)
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
    (hcs24 : 24 ≤ d.regs.rsp.toNat) (hcs8 : d.regs.rsp.toNat + 8 < 2 ^ 64)
    (hsv : ∀ x, G.tabEnd ≤ x → x < G.tabEnd + 32 → ¬ G.InStack x ∧ ¬ G.InArr x ∧
      (x < d.regs.rsp.toNat - 24 ∨ d.regs.rsp.toNat + 8 ≤ x))
    (hsv64 : G.tabEnd + 32 < 2 ^ 64) (v15 vbx v12 v13 : Word)
    (hv15 : rdW d.dmem (A G.tabEnd) = some v15) (hvbx : rdW d.dmem (A (G.tabEnd + 8)) = some vbx)
    (hv12 : rdW d.dmem (A (G.tabEnd + 16)) = some v12) (hv13 : rdW d.dmem (A (G.tabEnd + 24)) = some v13) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = v15 ∧
        (st.data.regs.rbx = vbx ∧ st.data.regs.r12 = v12 ∧ st.data.regs.r13 = v13) ∧
        MemFrameT G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data))
      d (at_ (k0 + 5)) := by
  simp only [Prog.wf_eq, Prog.wfSpec, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hfds, hnd⟩, hTab⟩ := hwf
  have hwfp : ∀ f fd, p.lookup f = some fd → FunDecl.wf p G.tab fd = true :=
    fun f fd hl => hfds (f, fd) (mem_of_lookup hl)
  have hcode' : Code (trampoline G.tab entry (nrOf (Prog.nrt p) G.tab entry) (entryNp p entry) ++
      compileFns G.tab (Prog.nrt p) (Prog.skt p entry) p) k0 := hcode
  have hProg : ∀ f fd, p.lookup f = some fd →
      ∃ kf, Code (compileFn G.tab (Prog.nrt p) (Prog.skt p entry) f fd) kf :=
    fun f fd hl => code_of_lookup p _ hcode'.right hl
  have hTree : ∀ g fd, p.lookup g = some fd → nrOf (Prog.nrt p) G.tab g = Stmt.nret fd.body :=
    fun g fd hl => nrOf_nrt hnd G.tab hl
  have hsk := skOf_skt_lt entry (tab := G.tab) fun f fd hm => hfds (f, fd) hm
  obtain ⟨_, hFun⟩ := execSim_all hG hTab p hwfp (Prog.nrt p) hTree hsk hProg N
  obtain ⟨kf, hkf⟩ := hProg entry fd hentry
  have hlF : label (fnL entry) = at_ kf := by rw [Code.label (i := 0) hkf (compileFn_head _ _ _ _ _)]; rfl
  -- the entry's result count
  have hc0 : nrOf (Prog.nrt p) G.tab entry = Stmt.nret fd.body := hTree entry fd hentry
  have hnr : Stmt.nret fd.body ≤ G.tab.nres := by
    have := hwfp entry fd hentry
    simp only [FunDecl.wf_eq, FunDecl.wfSpec, Bool.and_eq_true] at this
    exact Stmt.nret_le_of_wf this.1.2
  have ht0 := hcode'.left
  have hnp : entryNp p entry = fd.nparams := by simp [entryNp, hentry]
  rw [hc0, hnp] at ht0
  have ht := ht0
  simp only [trampoline, burnFuel, List.append_assoc, List.cons_append, List.nil_append] at ht
  have htR := ht.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail
  have htArg := htR.left
  obtain ⟨K, hK⟩ : ∃ K, K = k0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      (if fd.nparams ≤ argRegs.length then loadArgs G.tab 0 (argRegs.take fd.nparams) else []).length :=
    ⟨_, rfl⟩
  have htP := htR.right
  rw [← hK] at htP
  have htZ := htP.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail.tail
  have hz := htZ.left
  have hz2 := htZ.right
  have hlExh : label exhaustedL = at_ (K + 4) := Code.label (i := 4) htP rfl
  have hlErr : label errorL = at_ (K + 7) := Code.label (i := 7) htP rfl
  have hlAbort : label abortL = at_ (K + 9) := Code.label (i := 9) htP rfl
  have hlFin : label finishL = at_ (K + 12) := Code.label (i := 12) htP rfl
  have hlOk : label okL = at_ (K + 22) := Code.label (i := 22) htP rfl
  -- the save area: the four words past the table
  have hfw := hwfp entry fd hentry
  simp only [FunDecl.wf_eq, FunDecl.wfSpec, Bool.and_eq_true, decide_eq_true_eq] at hfw
  have hfw2 : fd.nparams < 2 ^ 26 := by simp only [frameWords, maxOff] at hfw; omega
  have hTab0 := hTab
  simp only [maxOff] at hTab0
  have hsave0 : 0 ≤ G.tab.save fd.nparams := by simp only [Tab.save, Tab.args]; omega
  have hsaveS : G.tab.save fd.nparams + 32 < 2 ^ 31 := by simp only [Tab.save, Tab.args]; omega
  have hsaveE : G.T + (G.tab.save fd.nparams).toNat = G.tabEnd := by
    simp only [Tab.save, Tab.args, Layout.tabEnd]; omega
  have hsvOut : ∀ x, G.tabEnd ≤ x → x < G.tabEnd + 32 → ¬ G.InTab x := fun x h1 _ h => by
    simp only [Layout.InTab] at h; omega
  -- the common exit `ca_finish`: restore the caller's stack and registers, return
  have hfin : ∀ s : MachineData, s.regs.rbp.toNat = d.regs.rsp.toNat - 24 →
      rdW s.dmem (A (d.regs.rsp.toNat - 24)) = some d.regs.rdi →
      rdW s.dmem (A (d.regs.rsp.toNat - 24 + 8)) = some d.regs.r14 →
      rdW s.dmem (A (d.regs.rsp.toNat - 24 + 8 + 8)) = some d.regs.rbp →
      rdW s.dmem (A (d.regs.rsp.toNat - 24 + 8 + 8 + 8)) = some ra →
      MemFrameT G d.regs.rsp.toNat d.dmem s.dmem →
      (s.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) s) →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = v15 ∧
        (st.data.regs.rbx = vbx ∧ st.data.regs.r12 = v12 ∧ st.data.regs.r13 = v13) ∧
        MemFrameT G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s (at_ (K + 12)) := by
    intro s hbp h15 h14 hbp' hra' hfr hout
    have hsvs : ∀ y, G.tabEnd ≤ y → y + 8 ≤ G.tabEnd + 32 → rdW s.dmem (A y) = rdW d.dmem (A y) :=
      fun y h1 h2 => rdW_congr fun j hj => by
        rw [A_add]; obtain ⟨q1, q2, q3⟩ := hsv (y + j) (by omega) (by omega)
        exact hfr.same _ (by omega) q1 q2 (hsvOut _ (by omega) (by omega)) (by rcases q3 with h | h <;> omega)
    have hs0 : rdW s.dmem (A G.tabEnd) = some v15 := by rw [hsvs _ (by omega) (by omega)]; exact hv15
    have hs1 : rdW s.dmem (A (G.tabEnd + 8)) = some vbx := by rw [hsvs _ (by omega) (by omega)]; exact hvbx
    have hs2 : rdW s.dmem (A (G.tabEnd + 16)) = some v12 := by rw [hsvs _ (by omega) (by omega)]; exact hv12
    have hs3 : rdW s.dmem (A (G.tabEnd + 24)) = some v13 := by rw [hsvs _ (by omega) (by omega)]; exact hv13
    refine ev_label (Code.get (i := 12) htP rfl) ?_
    refine ev_movRR (Code.get (i := 13) htP rfl) ?_
    refine ev_pop (Code.get (i := 14) htP rfl) (v := d.regs.rdi) ?_ ?_
    · addr_simp; rw [hbp]; exact h15
    have hT' : (UInt64.ofBitVec d.regs.rdi.toBitVec).toNat = G.T := by simpa using hT
    refine ev_movRM (Code.get (i := 15) htP rfl) ⟨by omega, by omega⟩ (v := vbx) ?_ ?_
    · simp only [Reg64s.get64_r15, Reg64s.set64_r15, Reg64s.set64_rsp, UInt64.toNat_toBitVec, Reg64s.r15_mk]
      rw [hT', show (G.tab.save fd.nparams + 8).toNat = (G.tab.save fd.nparams).toNat + 8 by omega,
        ← Nat.add_assoc, hsaveE]; exact hs1
    refine ev_movRM (Code.get (i := 16) htP rfl) ⟨by omega, by omega⟩ (v := v12) ?_ ?_
    · simp only [Reg64s.get64_r15, Reg64s.set64_r15, Reg64s.set64_rsp, Reg64s.set64_rbx, UInt64.toNat_toBitVec,
        Reg64s.r15_mk]
      rw [hT', show (G.tab.save fd.nparams + 16).toNat = (G.tab.save fd.nparams).toNat + 16 by omega,
        ← Nat.add_assoc, hsaveE]; exact hs2
    refine ev_movRM (Code.get (i := 17) htP rfl) ⟨by omega, by omega⟩ (v := v13) ?_ ?_
    · simp only [Reg64s.get64_r15, Reg64s.set64_r15, Reg64s.set64_rsp, Reg64s.set64_rbx, Reg64s.set64_r12,
        UInt64.toNat_toBitVec, Reg64s.r15_mk]
      rw [hT', show (G.tab.save fd.nparams + 24).toNat = (G.tab.save fd.nparams).toNat + 24 by omega,
        ← Nat.add_assoc, hsaveE]; exact hs3
    refine ev_movRM (Code.get (i := 18) htP rfl) ⟨by omega, by omega⟩ (v := v15) ?_ ?_
    · simp only [Reg64s.get64_r15, Reg64s.set64_r15, Reg64s.set64_rsp, Reg64s.set64_rbx, Reg64s.set64_r12,
        Reg64s.set64_r13, UInt64.toNat_toBitVec, Reg64s.r15_mk]
      rw [hT', hsaveE]; exact hs0
    refine ev_pop (Code.get (i := 19) htP rfl) (v := d.regs.r14) ?_ ?_
    · simp only [Reg64s.set64_rbx, Reg64s.set64_r12, Reg64s.set64_r13]; addr_simp; rw [hbp]; exact h14
    refine ev_pop (Code.get (i := 20) htP rfl) (v := d.regs.rbp) ?_ ?_
    · simp only [Reg64s.set64_rbx, Reg64s.set64_r12, Reg64s.set64_r13]; addr_simp; rw [hbp]; exact hbp'
    refine ev_ret (Code.get (i := 21) htP rfl) (ra := ra) ?_ ?_
    · simp only [Reg64s.set64_rbx, Reg64s.set64_r12, Reg64s.set64_r13]; addr_simp; rw [hbp]; exact hra'
    refine Eventually.done _ ⟨rfl, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, hfr, ?_⟩
    · simp only [Reg64s.set64_rbx, Reg64s.set64_r12, Reg64s.set64_r13]; addr_simp; rw [hbp]
      simp only [A, BitVec.toNat_ofNat]; omega
    all_goals try simp [Reg64s.set64_rbx, Reg64s.set64_r12, Reg64s.set64_r13]
    · rcases hout with h | h
      · exact Or.inl (by simpa using h)
      · right
        revert h
        generalize run p N entry args m = res
        rcases res with e | ⟨r, m'⟩
        · cases e <;> simp [OutcomeRel]
        · simp only [OutcomeRel, Reg64s.set64_rsp, Reg64s.set64_r15, Reg64s.set64_r14, Reg64s.set64_rbp,
            Reg64s.set64_rbx, Reg64s.set64_r12, Reg64s.set64_r13]
          rintro ⟨h1, ⟨h2, h4⟩, h3⟩
          exact ⟨h1, ⟨h2.congr rfl rfl rfl rfl rfl rfl, h4⟩, h3⟩
  have hsp0 := hcs24
  -- the three pushes
  have hmap : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat → (rdW d.dmem (A x)).isSome → True :=
    fun _ _ _ _ => trivial
  suffices H : ∀ s3 : MachineData, s3.regs.rsp.toNat = d.regs.rsp.toNat - 24 →
      s3.regs.rdi = d.regs.rdi → s3.regs.rsi = d.regs.rsi →
      Only (d.regs.rsp.toNat - 24) d.regs.rsp.toNat d.dmem s3.dmem →
      rdW s3.dmem (A (d.regs.rsp.toNat - 24)) = some d.regs.rdi →
      rdW s3.dmem (A (d.regs.rsp.toNat - 24 + 8)) = some d.regs.r14 →
      rdW s3.dmem (A (d.regs.rsp.toNat - 24 + 8 + 8)) = some d.regs.rbp →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = v15 ∧
        (st.data.regs.rbx = vbx ∧ st.data.regs.r12 = v12 ∧ st.data.regs.r13 = v13) ∧
        MemFrameT G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s3 (at_ (k0 + 5 + 1 + 1 + 1)) by
    have hm : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x + 8 ≤ d.regs.rsp.toNat → (rdW d.dmem (A x)).isSome :=
      fun x h1 h2 => isSome_rdW fun j hj => by rw [A_add]; exact (hcs _ (by omega) (by omega)).1
    have e1 : d.regs.rsp.toBitVec - 8 = A (d.regs.rsp.toNat - 8) := by
      rw [toBitVec_eq_A, A_sub8 _ (by omega) (by omega)]
    refine ev_push (Code.get (i := 5) ht rfl) ?_ ?_
    · rw [e1]; exact hm _ (by omega) (by omega)
    have e2 : (UInt64.ofBitVec (d.regs.rsp.toBitVec - 8)).toBitVec - 8 = A (d.regs.rsp.toNat - 16) := by
      rw [UInt64.toBitVec_ofBitVec, e1, A_sub8 _ (by omega) (by omega)]; congr 1
    refine ev_push (Code.get (i := 6) ht rfl) ?_ ?_
    · simp only [Reg64s.set64_rsp]; rw [e2, e1, rdW_wrW_A (by omega) (by omega) (by omega)]
      exact hm _ (by omega) (by omega)
    have e3 : (UInt64.ofBitVec (A (d.regs.rsp.toNat - 16))).toBitVec - 8 = A (d.regs.rsp.toNat - 24) := by
      rw [UInt64.toBitVec_ofBitVec, A_sub8 _ (by omega) (by omega)]; congr 1
    simp only [Reg64s.set64_rsp]
    rw [e2, e1]
    refine ev_push (Code.get (i := 7) ht rfl) ?_ ?_
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
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = v15 ∧
        (st.data.regs.rbx = vbx ∧ st.data.regs.r12 = v12 ∧ st.data.regs.r13 = v13) ∧
        MemFrameT G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s8
        (at_ (k0 + 5 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) by
    refine ev_movRR (Code.get (i := 8) ht rfl) ?_
    refine ev_movRR (Code.get (i := 9) ht rfl) ?_
    refine ev_movRR (Code.get (i := 10) ht rfl) ?_
    refine ev_movRM (Code.get (i := 11) ht rfl) ⟨by simp [Tab.stackTop], by simp [Tab.stackTop]⟩
      (v := UInt64.ofNat G.hi) ?_ ?_
    · simp [Tab.stackTop, h3di, hT]; exact htop3
    refine ev_lea (Code.get (i := 12) ht rfl) ⟨by simp [Tab.args]; omega, by simp [Tab.args]; simp [maxOff] at hTab; omega⟩ ?_
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
  -- facts about the argument cells (in the table, so outside both stacks)
  have hcell : ∀ i, i < args.length → ∀ j < 8, G.InTab (G.T + G.tab.args.toNat + 8 * i + j) := by
    exact fun i hi j hj => ⟨by omega, by omega⟩
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
  have hargs8 : ∀ i (hi : i < args.length),
      rdW s8.dmem (A (G.T + G.tab.args.toNat + 8 * i)) = some args[i] := by
    intro i hi
    have hc := hcellS i hi
    rw [h8m, ← hargv i hi, h3O.rdW_eq (by omega) ?_]
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
  -- the entry's arguments in place (at most 6 in registers): the state `s9`
  suffices H9 : ∀ s9 : MachineData, s9.regs.rsp = s8.regs.rsp → s9.regs.rbp = s8.regs.rbp →
      s9.regs.r15 = s8.regs.r15 → s9.regs.r14 = s8.regs.r14 → s9.dmem = s8.dmem →
      (args.length ≤ argRegs.length → ∀ i (h : i < args.length),
        s9.regs.get64 (argRegs.getD i .rax) = args[i].toBitVec) →
      (argRegs.length < args.length → s9.regs.rsi = s8.regs.rsi) →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = v15 ∧
        (st.data.regs.rbx = vbx ∧ st.data.regs.r12 = v12 ∧ st.data.regs.r13 = v13) ∧
        MemFrameT G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s9 (at_ K) by
    by_cases hnp6 : fd.nparams ≤ argRegs.length
    · rw [if_pos hnp6] at htArg hK
      have hnp6' : fd.nparams ≤ 6 := by simpa [argRegs] using hnp6
      have hlen : (argRegs.take fd.nparams).length = fd.nparams := by simp; omega
      refine ev_congr (sim_loadArgs G.tab rfl args _ (argRegs.take fd.nparams) 0 _ s8 htArg
        (by rw [h815]) (fun r h => argRegs_sub (List.mem_of_mem_take h)) ((by decide : argRegs.Nodup).sublist (List.take_sublist _ _))
        (by rw [hlen]; omega) (by rw [hlen]; simp only [Tab.args, maxOff] at hTab ⊢; omega)
        (fun j hj => hargs8 j hj) ?_) (by omega)
      intro s9 hd9 hk9 hr9
      have hkeep : ∀ r, r ∉ allocRegs → s9.regs.get64 r = s8.regs.get64 r := fun r hr =>
        hk9 r fun h => hr (argRegs_sub (List.mem_of_mem_take h))
      refine ev_congr (H9 s9 (UInt64.toBitVec_inj.mp (hkeep .rsp (by decide)))
        (UInt64.toBitVec_inj.mp (hkeep .rbp (by decide))) (UInt64.toBitVec_inj.mp (hkeep .r15 (by decide)))
        (UInt64.toBitVec_inj.mp (hkeep .r14 (by decide))) hd9 (fun _ i hi => ?_) (fun h => by omega)) ?_
      · have := hr9 i (by rw [hlen]; omega)
        have htk : (argRegs.take fd.nparams).getD i .rax = argRegs.getD i .rax := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_take, show i < fd.nparams by omega]
        rw [htk] at this
        rw [this]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      · rw [hK, loadArgs_length, hlen]
    · rw [if_neg hnp6] at htArg hK
      exact ev_congr (H9 s8 rfl rfl rfl rfl rfl (fun h => absurd h (by omega)) (fun _ => rfl))
        (by rw [hK]; simp)
  intro s9 h9sp h9bp h915 h914 h9m hreg9 hrsi9
  replace h8sp : s9.regs.rsp.toNat = G.hi := by rw [h9sp]; exact h8sp
  replace h8bp : s9.regs.rbp.toNat = d.regs.rsp.toNat - 24 := by rw [h9bp]; exact h8bp
  replace h815 : s9.regs.r15.toNat = G.T := by rw [h915]; exact h815
  replace h814 : s9.regs.r14.toNat = N := by rw [h914]; exact h814
  replace hargs8 : ∀ i (hi : i < args.length),
      rdW s9.dmem (A (G.T + G.tab.args.toNat + 8 * i)) = some args[i] := by rw [h9m]; exact hargs8
  replace h8m : s9.dmem = s3.dmem := by rw [h9m]; exact h8m
  have h8si' : argRegs.length < args.length → s9.regs.rsi.toNat = G.T + G.tab.args.toNat := fun h => by
    rw [hrsi9 h]; exact h8si
  clear h9sp h9bp h915 h914 h9m h8si
  have hhi := hG.hi_le
  -- the caller's stack survives any change outside it
  have hcsw : ∀ dm : DataMem, (∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 →
      dm.get? (A x) = s3.dmem.get? (A x)) →
      rdW dm (A (d.regs.rsp.toNat - 24)) = some d.regs.rdi ∧
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
      MemFrameT G d.regs.rsp.toNat d.dmem s.dmem →
      (s.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) s) →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = v15 ∧
        (st.data.regs.rbx = vbx ∧ st.data.regs.r12 = v12 ∧ st.data.regs.r13 = v13) ∧
        MemFrameT G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s (label finishL) := by
    intro s hbp hdm hfr hout
    obtain ⟨w1, w2, w3, w4⟩ := hcsw s.dmem hdm
    rw [hlFin]; exact hfin s hbp w1 w2 w3 w4 hfr hout
  -- the exhausted exit: `rdx := 1`
  have hexh : ∀ s : MachineData, s.regs.rbp.toNat = d.regs.rsp.toNat - 24 →
      (∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 → s.dmem.get? (A x) = s3.dmem.get? (A x)) →
      MemFrameT G d.regs.rsp.toNat d.dmem s.dmem →
      Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = v15 ∧
        (st.data.regs.rbx = vbx ∧ st.data.regs.r12 = v12 ∧ st.data.regs.r13 = v13) ∧
        MemFrameT G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data)) s (label exhaustedL) := by
    intro s hbp hdm hfr
    rw [hlExh]
    refine ev_label (Code.get (i := 4) htP rfl) ?_
    refine ev_movRI (Code.get (i := 5) htP rfl) ?_
    refine ev_jmp (Code.get (i := 6) htP rfl) ?_
    exact hexit _ (by simp [hbp]) hdm hfr (Or.inl (by simp))
  have hs9 : 8 ≤ G.hi := by omega
  have hF9 : MemFrameT G d.regs.rsp.toNat d.dmem s9.dmem :=
    ⟨fun y hy => by rw [h8m]; exact h3O.grows y hy, fun x hx _ _ _ hsp => by
      rw [h8m]; exact h3O.same x hx hsp⟩
  refine ev_sub1 (Code.get (i := 0) htP rfl) fun st hst => ?_
  refine ev_jcc (Code.get (i := 1) htP rfl) (fun hcc => ?_) (fun hcc => ?_)
  · exact hexh _ (by simp [h8bp]) (fun x _ _ => by simp [h8m]) hF9
  · simp only [CondCode.interp] at hcc
    rw [hst] at hcc
    have hN0 : s9.regs.r14 ≠ 0 := by intro h; simp [h] at hcc
    have hpos : 0 < s9.regs.r14.toNat := by
      rcases Nat.eq_zero_or_pos s9.regs.r14.toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hN0
      · exact h
    have hcall8 : (UInt64.ofBitVec (s9.regs.get64 .r14 - 1)).toNat = N - 1 := by
      have := u64_sub_one_toNat hpos; simp only [Reg64s.get64_r14]; rw [← h814]; exact this
    have e1 : s9.regs.rsp.toBitVec - 8 = A (G.hi - 8) := by
      rw [toBitVec_eq_A, h8sp, A_sub8 _ hs9 hhi]
    refine ev_call (Code.get (i := 2) htP rfl) ?_ ?_
    · simp only [Reg64s.set64_r14]; rw [e1]
      exact isSome_rdW fun j hj => by
        rw [A_add, h8m]; exact h3O.grows _ (hmem.stack _ ⟨by omega, by omega⟩)
    rw [hlF]
    simp only [Reg64s.set64_r14, Reg64s.set64_rsp]
    rw [e1]
    have hm3 : MemRel G m s3.dmem := hmem.only' hG h3O fun x h1 h2 =>
      ⟨(hcs x (by omega) (by omega)).2.2.2, (hcs x (by omega) (by omega)).2.2.1⟩
    refine hFun entry fd kf hentry hkf args ⟨m, Locals.init []⟩ _
      (UInt64.ofBitVec (at_ (K + 2 + 1)).toBitVec) _ hargs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [UInt64.toNat_mk', A_toNat]
      rw [rdW_wrW_same]
    · refine ⟨fun hl i hi => ?_, fun hl => ⟨fun i hi => ?_, ?_, ?_⟩⟩
      · have hr := argRegs_getD_mem i (by omega)
        rw [← hreg9 hl i hi]
        generalize argRegs.getD i .rax = r at hr
        obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := allocRegs_ne hr
        cases r <;> (first | exact absurd rfl n4 | exact absurd rfl n6 | rfl)
      · have hc := hcellS i hi
        simp only [h8si' hl]
        rw [rdW_wrW_A (by omega) (by omega) (by omega), hargs8 i hi]
      · simp only [UInt64.toNat_mk', A_toNat, h8si' hl]
        have hc := hcellS 0 (by omega)
        rcases hc with hc | hc
        · right
          refine Classical.byContradiction fun hc' => ?_
          exact hG.notStack_of_tab (x := G.lo) ⟨by omega, by omega⟩ ⟨Nat.le_refl _, by omega⟩
        · left; simp only [A, BitVec.toNat_ofNat]; omega
      · simp only [h8si' hl]; omega
    · simp only [UInt64.toNat_mk', A_toNat, A, BitVec.toNat_ofNat, skOf_skt_entry]; omega
    · simp only [UInt64.toNat_mk', A_toNat, A, BitVec.toNat_ofNat]; omega
    · exact h815
    · rw [h8m]
      exact hm3.only hG (Only.wrW (x := G.hi - 8) (by omega)) fun x h1 h2 => ⟨by omega, by omega⟩
    · simp only [UInt64.toNat_mk']
      have := u64_sub_one_toNat hpos
      simp only [Reg64s.get64_r14] at hcall8 ⊢
      rw [show (s9.regs.r14.toBitVec - 1) = (s9.regs.r14 - 1).toBitVec from rfl]
      simp only [UInt64.toNat_toBitVec]
      omega
    all_goals
      have hcsS : ∀ dm : DataMem, Pres G (G.hi - 8) (wrW s9.dmem (A (G.hi - 8))
          (at_ (K + 2 + 1)).toBitVec) dm →
          ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 → dm.get? (A x) = s3.dmem.get? (A x) := by
        intro dm hP x h1 h2
        have hx := hcs x (by omega) (by omega)
        have hxs : x < G.lo ∨ G.hi ≤ x := by
          simp only [Layout.InStack, not_and, Nat.not_lt] at hx
          by_cases h : G.lo ≤ x
          · exact Or.inr (hx.2.1 h)
          · exact Or.inl (by omega)
        rw [hP.same x (by omega) (by omega) hx.2.2.1 (fun hr => hx.2.2.2 hr.tab) (fun hg => hx.2.2.2 hg.tab), get?_wrW_A (by omega) (by omega) (by omega), h8m]
      have hfrS : ∀ dm : DataMem, Pres G (G.hi - 8) (wrW s9.dmem (A (G.hi - 8))
          (at_ (K + 2 + 1)).toBitVec) dm → MemFrameT G d.regs.rsp.toNat d.dmem dm := by
        intro dm hP
        refine ⟨fun y hy => hP.grows y (isSome_get?_storeInt (hF9.grows y hy)), fun x hx hs ha ht hsp => ?_⟩
        have hxs : x < G.lo ∨ G.hi ≤ x := by
          simp only [Layout.InStack, not_and, Nat.not_lt] at hs
          by_cases h : G.lo ≤ x
          · exact Or.inr (hs h)
          · exact Or.inl (by omega)
        rw [hP.same x hx (by omega) ha (fun hr => ht hr.tab) (fun hg => ht hg.tab),
          get?_wrW_A (by omega) hx (by omega)]
        exact hF9.same x hx hs ha ht hsp
    · -- the entry function returned
      intro r σ' d' hinv hm' hloc hrsp' hrbp' hr15' hr14' hrax' hpres'
      simp only [UInt64.toBitVec_ofBitVec, Int64.ofBitVec_toBitVec]
      refine ev_jmp (Code.get (i := 3) htP rfl) ?_
      rw [hlOk]
      refine ev_label (Code.get (i := 22) htP rfl) ?_
      simp only [UInt64.toNat_mk', A_toNat] at hpres' hrsp'
      have hsz : (A (G.hi - 8)).toNat = G.hi - 8 := by simp only [A, BitVec.toNat_ofNat]; omega
      rw [hsz] at hpres' hrsp'
      have hTab' := hTab; simp only [maxOff] at hTab'
      have hlen := hrax'.2.2
      -- zero the results past the entry's
      refine sim_loadRes hG _ rfl [] r _ (by omega) (G.tab.nres - Stmt.nret fd.body) (Stmt.nret fd.body) _ d'
        hz (by omega) (by simp) (by rw [hr15']; simpa using h815) (by have := hG.lo_le; omega) (by simp)
        (fun x hx => hm'.res x hx) (fun j hj => absurd hj (by simp))
        (fun j hj hm => hrax'.1 j hj hm) (fun j h1 h2 => hrax'.2.1 j h1 h2)
        (fun j hj => by simp only [List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none,
          List.getElem?_eq_none (show r.length ≤ j by omega)]) ?_
      intro s' q1 q2 q3 q4 hO hR hM
      refine ev_movRI hz2.head ?_
      refine ev_jmp hz2.tail.head ?_
      have hres' : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 →
          s'.dmem.get? (A x) = d'.dmem.get? (A x) := by
        intro x h1 h2
        refine hO.same x (by omega) (Classical.byContradiction fun hc => ?_)
        simp only [not_or, Nat.not_lt, Nat.not_le] at hc
        exact (hcs x (by omega) (by omega)).2.2.2 (Layout.inRes_of hc.1 hc.2).tab
      refine hexit _ (by simp [q2, hrbp', h8bp]) (fun x h1 h2 => by
          rw [show ({ s' with regs := s'.regs.set64 .rdx (Int64.ofInt 0).toBitVec } : MachineData).dmem = s'.dmem
            from rfl, hres' x h1 h2]
          exact hcsS _ hpres' x h1 h2) ⟨fun y hy => hO.grows y ((hfrS _ hpres').grows y hy),
          fun x hx hs ha ht hsp => by
          rw [show ({ s' with regs := s'.regs.set64 .rdx (Int64.ofInt 0).toBitVec } : MachineData).dmem = s'.dmem
            from rfl, hO.same x hx (Classical.byContradiction fun hc => by
              simp only [not_or, Nat.not_lt, Nat.not_le] at hc
              exact ht (Layout.inRes_of hc.1 hc.2).tab)]
          exact (hfrS _ hpres').same x hx hs ha ht hsp⟩ (Or.inr ?_)
      have hrun : run p N entry args m = .ok (r, σ'.mem) := by simp [run, hinv, Except.map]
      rw [hrun]
      refine ⟨by simp, ⟨?_, fun j h1 h2 => by simpa using hM j h1 (by omega), by omega⟩,
        hm'.only_res hG hO fun x a b => Layout.inRes_of a b⟩
      exact ResRel.set64 (n := G.tab.nres) (fun j hj hm => hR j (by omega) hm) (Or.inr (Or.inl rfl)) _
    · -- an error with code `0`: `rax := 0`, `rdx := 2`
      intro d' ⟨x, hx, hne⟩ hG'
      simp only [UInt64.toNat_mk', A_toNat] at hG'
      have hsz : (A (G.hi - 8)).toNat = G.hi - 8 := by simp only [A, BitVec.toNat_ofNat]; omega
      rw [hsz] at hG'
      rw [hlErr]
      refine ev_label (Code.get (i := 7) htP rfl) ?_
      refine ev_movRI (Code.get (i := 8) htP rfl) ?_
      refine ev_label (Code.get (i := 9) htP rfl) ?_
      refine ev_movRR (Code.get (i := 10) htP rfl) ?_
      refine ev_movRI (Code.get (i := 11) htP rfl) ?_
      obtain ⟨w1, w2, w3, w4⟩ := hcsw _ (fun y h1 h2 => hcsS _ hG'.mem y h1 h2)
      refine hfin _ (by simp [hG'.rbp, h8bp, Reg64s.set64]) w1 w2 w3 w4 (hfrS _ hG'.mem) (Or.inr ?_)
      have hrun : run p N entry args m = .error x := by simp [run, hx, Except.map]
      rw [hrun]
      refine OutcomeRel.error hne.1 ?_ ?_
      · simp only [Reg64s.set64_rdx]
      · rw [hne.2]; simp [Reg64s.set64, Reg64s.get64]
    · -- an abort, its code in `rax`: `rdx := 2`
      intro d' k hx hG' hrax
      simp only [UInt64.toNat_mk', A_toNat] at hG'
      have hsz : (A (G.hi - 8)).toNat = G.hi - 8 := by simp only [A, BitVec.toNat_ofNat]; omega
      rw [hsz] at hG'
      rw [hlAbort]
      refine ev_label (Code.get (i := 9) htP rfl) ?_
      refine ev_movRR (Code.get (i := 10) htP rfl) ?_
      refine ev_movRI (Code.get (i := 11) htP rfl) ?_
      obtain ⟨w1, w2, w3, w4⟩ := hcsw _ (fun y h1 h2 => hcsS _ hG'.mem y h1 h2)
      refine hfin _ (by simp [hG'.rbp, h8bp, Reg64s.set64]) w1 w2 w3 w4 (hfrS _ hG'.mem) (Or.inr ?_)
      have hrun : run p N entry args m = .error (.abort k) := by simp [run, hx, Except.map]
      rw [hrun]
      refine OutcomeRel.error (e := .abort k) nofun ?_ ?_
      · simp only [Reg64s.set64_rdx]
      · simp [Reg64s.set64, Reg64s.get64, Err.code, hrax]
    · -- out of fuel or stack
      intro d' hG'
      simp only [UInt64.toNat_mk', A_toNat] at hG'
      have hsz : (A (G.hi - 8)).toNat = G.hi - 8 := by simp only [A, BitVec.toNat_ofNat]; omega
      rw [hsz] at hG'
      exact hexh _ (by simp [hG'.rbp, h8bp]) (fun y h1 h2 => hcsS _ hG'.mem y h1 h2) (hfrS _ hG'.mem)
  

/-- **The trampoline from its entry**: it stores the caller's `r15`, `rbx`, `r12`, `r13` in the 32
bytes past the table and runs as `enter_core`, which puts them back; the memory outside the layout,
the 24 bytes below `rsp` and those 32 bytes is the caller's (`MemFrame`). Besides
`compile_correct`'s premises, the 32 bytes past the table must be mapped and apart from the L stack,
the arrays and the caller's 32 bytes of machine stack. -/
theorem compile_correct_frame [Host] (p : Prog) (entry : FnName) (G : Layout) (hG : G.Ok)
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
    (hcs24 : 24 ≤ d.regs.rsp.toNat) (hcs8 : d.regs.rsp.toNat + 8 < 2 ^ 64)
    (hsv : ∀ x, G.tabEnd ≤ x → x < G.tabEnd + 32 → (d.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧
      ¬ G.InArr x ∧ (x < d.regs.rsp.toNat - 24 ∨ d.regs.rsp.toNat + 8 ≤ x))
    (hsv64 : G.tabEnd + 32 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        CalleeKept d.regs st.data.regs ∧ MemFrame G d.regs.rsp.toNat d.dmem st.data.dmem ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data))
      d (label enterL) := by
  have hwf' := hwf
  simp only [Prog.wf_eq, Prog.wfSpec, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf'
  obtain ⟨⟨hfds, -⟩, hTab⟩ := hwf'
  have hfw := hfds (entry, fd) (mem_of_lookup hentry)
  simp only [FunDecl.wf_eq, FunDecl.wfSpec, Bool.and_eq_true, decide_eq_true_eq] at hfw
  have hfw2 : fd.nparams < 2 ^ 26 := by simp only [frameWords, maxOff] at hfw; omega
  simp only [maxOff] at hTab
  have hnp : entryNp p entry = fd.nparams := by simp [entryNp, hentry]
  have ht : Code (trampoline G.tab entry (nrOf (Prog.nrt p) G.tab entry) fd.nparams) k0 := by
    have h := (show Code (trampoline G.tab entry (nrOf (Prog.nrt p) G.tab entry) (entryNp p entry) ++
      compileFns G.tab (Prog.nrt p) (Prog.skt p entry) p) k0 from hcode).left
    rwa [hnp] at h
  have hsave0 : 0 ≤ G.tab.save fd.nparams := by simp only [Tab.save, Tab.args]; omega
  have hsaveS : G.tab.save fd.nparams + 32 < 2 ^ 31 := by simp only [Tab.save, Tab.args]; omega
  have hsaveE : G.T + (G.tab.save fd.nparams).toNat = G.tabEnd := by
    simp only [Tab.save, Tab.args, Layout.tabEnd]; omega
  have hTe : G.T ≤ G.tabEnd := by simp only [Layout.tabEnd]; omega
  have hdi : (d.regs.get64 .rdi).toNat = G.T := by simpa using hT
  have e0 : (d.regs.get64 .rdi).toNat + (G.tab.save fd.nparams).toNat = G.tabEnd := by rw [hdi, hsaveE]
  have e1 : (d.regs.get64 .rdi).toNat + (G.tab.save fd.nparams + 8).toNat = G.tabEnd + 8 := by
    rw [hdi, show (G.tab.save fd.nparams + 8).toNat = (G.tab.save fd.nparams).toNat + 8 by omega]; omega
  have e2 : (d.regs.get64 .rdi).toNat + (G.tab.save fd.nparams + 16).toNat = G.tabEnd + 16 := by
    rw [hdi, show (G.tab.save fd.nparams + 16).toNat = (G.tab.save fd.nparams).toNat + 16 by omega]; omega
  have e3 : (d.regs.get64 .rdi).toNat + (G.tab.save fd.nparams + 24).toNat = G.tabEnd + 24 := by
    rw [hdi, show (G.tab.save fd.nparams + 24).toNat = (G.tab.save fd.nparams).toNat + 24 by omega]; omega
  have hmap : ∀ y, G.tabEnd ≤ y → y + 8 ≤ G.tabEnd + 32 → ∀ dm : DataMem,
      (∀ z, (d.dmem.get? z).isSome → (dm.get? z).isSome) → (rdW dm (A y)).isSome :=
    fun y h1 h2 dm hg => isSome_rdW fun j hj => by rw [A_add]; exact hg _ (hsv _ (by omega) (by omega)).1
  rw [Code.label (i := 0) ht rfl]
  refine ev_label (Code.get (i := 0) ht rfl) ?_
  refine ev_movMR (Code.get (i := 1) ht rfl) ⟨by omega, by omega⟩ ?_ ?_
  · rw [e0]; exact hmap _ (Nat.le_refl _) (by omega) _ fun _ h => h
  refine ev_movMR (Code.get (i := 2) ht rfl) ⟨by omega, by omega⟩ ?_ ?_
  · rw [e1, e0]; exact hmap _ (by omega) (by omega) _ fun _ h => isSome_get?_storeInt h
  refine ev_movMR (Code.get (i := 3) ht rfl) ⟨by omega, by omega⟩ ?_ ?_
  · rw [e2, e1, e0]; exact hmap _ (by omega) (by omega) _ fun _ h => isSome_get?_storeInt (isSome_get?_storeInt h)
  refine ev_movMR (Code.get (i := 4) ht rfl) ⟨by omega, by omega⟩ ?_ ?_
  · rw [e3, e2, e1, e0]
    exact hmap _ (by omega) (by omega) _ fun _ h => isSome_get?_storeInt (isSome_get?_storeInt (isSome_get?_storeInt h))
  simp only [e0, e1, e2, e3]
  generalize hdm1 : wrW (wrW (wrW (wrW d.dmem (A G.tabEnd) (d.regs.get64 .r15)) (A (G.tabEnd + 8))
    (d.regs.get64 .rbx)) (A (G.tabEnd + 16)) (d.regs.get64 .r12)) (A (G.tabEnd + 24)) (d.regs.get64 .r13) = dm1
  -- the stores change only the save area
  have hO : Only G.tabEnd (G.tabEnd + 32) d.dmem dm1 := by
    rw [← hdm1]
    exact ((((Only.wrW (by omega)).union (Only.wrW (by omega)) (Nat.le_refl _) (by omega) (by omega) (by omega)
      : Only G.tabEnd (G.tabEnd + 32) _ _).union (Only.wrW (by omega)) (Nat.le_refl _) (by omega) (Nat.le_refl _)
        (by omega) : Only G.tabEnd (G.tabEnd + 32) _ _).union (Only.wrW (by omega)) (Nat.le_refl _) (by omega)
          (Nat.le_refl _) (by omega))
  have hwin : ∀ x, d.regs.rsp.toNat - 24 ≤ x → x < d.regs.rsp.toNat + 8 → dm1.get? (A x) = d.dmem.get? (A x) := by
    intro x h1 h2
    refine hO.same x (by omega) (Classical.byContradiction fun hc => ?_)
    simp only [not_or, Nat.not_lt, Nat.not_le] at hc
    rcases (hsv x hc.1 hc.2).2.2.2 with h | h <;> omega
  have hv : rdW dm1 (A G.tabEnd) = some d.regs.r15 ∧ rdW dm1 (A (G.tabEnd + 8)) = some d.regs.rbx ∧
      rdW dm1 (A (G.tabEnd + 16)) = some d.regs.r12 ∧ rdW dm1 (A (G.tabEnd + 24)) = some d.regs.r13 := by
    rw [← hdm1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rdW_wrW_A (by omega) (by omega) (by omega), rdW_wrW_A (by omega) (by omega) (by omega),
        rdW_wrW_A (by omega) (by omega) (by omega), rdW_wrW_same]; simp
    · rw [rdW_wrW_A (by omega) (by omega) (by omega), rdW_wrW_A (by omega) (by omega) (by omega),
        rdW_wrW_same]; simp
    · rw [rdW_wrW_A (by omega) (by omega) (by omega), rdW_wrW_same]; simp
    · rw [rdW_wrW_same]; simp
  have hout : ∀ x, G.T ≤ x → x < G.tabEnd → dm1.get? (A x) = d.dmem.get? (A x) := fun x h1 h2 =>
    hO.same x (by omega) (Or.inl h2)
  refine ev_congr (j := k0 + 5) ?_ (by omega)
  refine eventually_weaken _ _ _ _ ?_ (enter_core p entry G hG hwf k0 hcode fd hentry args hargs hnargs m N
    { d with dmem := dm1 } ra hT hN (hmem.only' hG hO fun x h1 h2 => ⟨fun h => by
      simp only [Layout.InTab] at h; omega, (hsv x h1 h2).2.2.1⟩)
    hroom (by rw [← htop]; exact rdW_congr fun j hj => by rw [A_add]; exact hout _ (by omega) (by
      simp only [Layout.tabEnd] at hTe ⊢; omega))
    (fun i h => by
      rw [← hargv i h]; refine rdW_congr fun j hj => ?_
      rw [A_add]; refine hout _ (by omega) ?_
      simp only [Layout.tabEnd, Tab.args, hnargs] at hTe ⊢; omega)
    (by show rdW dm1 (A d.regs.rsp.toNat) = some ra
        rw [← hra]; exact rdW_congr fun j hj => by rw [A_add]; exact hwin _ (by omega) (by omega))
    (fun x h1 h2 => by rw [hwin x h1 h2]; exact hcs x h1 h2)
    hcs24 hcs8 (fun x h1 h2 => (hsv x h1 h2).2) hsv64 _ _ _ _ hv.1 hv.2.1 hv.2.2.1 hv.2.2.2)
  intro st ⟨hpc, hsp, hbp, h14, h15, hkept, hfr, hres⟩
  refine ⟨hpc, hsp, hbp, h14, h15, hkept, ⟨fun y hy => hfr.grows y (hO.grows y hy),
    fun x hx hs ha ht' hsp' hsv' => ?_⟩, hres⟩
  rw [hfr.same x hx hs ha ht' hsp']
  exact hO.same x hx hsv'

/-- **The end-to-end compiler theorem** (`compile_correct_frame` without the memory frame): the
caller's `rsp`, `rbp`, `r14`, `r15`, `rbx`, `r12`, `r13` are restored on every path, whatever
registers the compiled functions use. -/
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
    (hcs24 : 24 ≤ d.regs.rsp.toNat) (hcs8 : d.regs.rsp.toNat + 8 < 2 ^ 64)
    (hsv : ∀ x, G.tabEnd ≤ x → x < G.tabEnd + 32 → (d.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧
      ¬ G.InArr x ∧ (x < d.regs.rsp.toNat - 24 ∨ d.regs.rsp.toNat + 8 ≤ x))
    (hsv64 : G.tabEnd + 32 < 2 ^ 64) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rsp.toNat = d.regs.rsp.toNat + 8 ∧
        st.data.regs.rbp = d.regs.rbp ∧ st.data.regs.r14 = d.regs.r14 ∧ st.data.regs.r15 = d.regs.r15 ∧
        CalleeKept d.regs st.data.regs ∧
        (st.data.regs.rdx = 1 ∨ OutcomeRel G (run p N entry args m) st.data))
      d (label enterL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨h1, h2, h3, h4, h5, h6, _, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩)
    (compile_correct_frame p entry G hG hwf k0 hcode fd hentry args hargs hnargs m N d ra hT hN hmem
      hroom htop hargv hra hcs hcs24 hcs8 hsv hsv64)

end L.Compiler
