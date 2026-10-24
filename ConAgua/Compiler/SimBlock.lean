module

public import ConAgua.Compiler.SimStore
public import ConAgua.L.Blocks

@[expose] public section

/-!
# Blocks: `copy64`, `copy8w`, `scan8` (lane blkcopy, docs/design/blkcopy.md)

Each block is a machine loop with no L loop around it: the simulation is an induction on the
iterations inside one statement (`scan_loop`, `copy64_loop`, `copy8w_loop`), with the memory
relation (`Inv`) carried through the stores of the copies (`Inv.store64`).
-/

namespace L.Compiler

open L

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

/-- The registers but `rax`, `rcx`, `rdx` agree. -/
def KeepR (s s0 : MachineData) : Prop :=
  ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s.regs.get64 r = s0.regs.get64 r

theorem KeepR.refl (s : MachineData) : KeepR s s := fun _ _ _ _ => rfl

theorem KeepR.trans {s s1 s0 : MachineData} (h : KeepR s s1) (h1 : KeepR s1 s0) : KeepR s s0 :=
  fun r a b c => (h r a b c).trans (h1 r a b c)

theorem KeepR.set {s s0 : MachineData} (h : KeepR s s0) {r : Reg64} (hr : r = .rax ∨ r = .rcx ∨ r = .rdx)
    (v : BitVec 64) (st : StatusFlags) : KeepR { s with regs := s.regs.set64 r v, status := st } s0 :=
  fun r' a b c => by
    rw [← h r' a b c]
    exact get64_set64_scratch hr v r' a b c

theorem KeepR.ofEq {s' s s0 : MachineData} (h : KeepR s s0)
    (h' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.regs.get64 r = s.regs.get64 r) : KeepR s' s0 :=
  fun r a b c => (h' r a b c).trans (h r a b c)

theorem add_swap (x y z : BitVec 64) : x + y + z = x + z + y := by
  rw [BitVec.add_assoc, BitVec.add_comm y, ← BitVec.add_assoc]

theorem KeepR.flags {s s0 : MachineData} (h : KeepR s s0) (st : StatusFlags) :
    KeepR { s with status := st } s0 := h

theorem KeepR.r15 {s s0 : MachineData} (h : KeepR s s0) : s.regs.r15 = s0.regs.r15 := by
  have := h .r15 (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_r15] at this
  exact UInt64.toBitVec_inj.mp this

theorem KeepR.rsp {s s0 : MachineData} (h : KeepR s s0) : s.regs.rsp = s0.regs.rsp := by
  have := h .rsp (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_rsp] at this
  exact UInt64.toBitVec_inj.mp this

theorem KeepR.rbp {s s0 : MachineData} (h : KeepR s s0) : s.regs.rbp = s0.regs.rbp := by
  have := h .rbp (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_rbp] at this
  exact UInt64.toBitVec_inj.mp this

theorem KeepR.r14 {s s0 : MachineData} (h : KeepR s s0) : s.regs.r14 = s0.regs.r14 := by
  have := h .r14 (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_r14] at this
  exact UInt64.toBitVec_inj.mp this

theorem KeepR.rsi {s s0 : MachineData} (h : KeepR s s0) : s.regs.rsi = s0.regs.rsi := by
  have := h .rsi (by decide) (by decide) (by decide)
  simp only [Reg64s.get64_rsi] at this
  exact UInt64.toBitVec_inj.mp this

/-- `Inv` with the same memory and the registers but the scratch ones. -/
theorem Inv.keepR {G : Layout} {ctx : Ctx} {F : Nat} {σ : St} {s s0 : MachineData} (hI : Inv G ctx F σ s0)
    (hd : s.dmem = s0.dmem) (hK : KeepR s s0) : Inv G ctx F σ s :=
  hI.of_regs hd hK.rsp hK.r15 fun r hr =>
    hK r (allocRegs_ne hr).1 (allocRegs_ne hr).2.1 (allocRegs_ne hr).2.2.1

theorem one_toBitVec : (Int64.ofInt 1).toBitVec = (1 : Word).toBitVec := rfl
theorem eight_toBitVec : (Int64.ofInt 8).toBitVec = (8 : Word).toBitVec := rfl

section
variable [Host]

/-- **The scan loop**: from `rax = j < e`, with the source at `rcx`, every iteration reads a
byte and its class; the loop leaves at `X` with `rax = scanN b c j e`. -/
theorem scan_loop {G : Layout} {b : Array UInt8} {c : List UInt8} {B TT : Nat} {off : Int}
    {eo : Operand .W64} {ve : Word} {kL : Nat} {Lb Xb : Label} {Q : MachineState → Prop}
    {D : DataMem} {s0 : MachineData}
    (hcode : Code (scanLoop Lb Xb off eo) kL)
    (hL : label Lb = at_ kL) (hX : label Xb = at_ (kL + 8))
    (hsrc : SrcAt G b D B) (hve : ve.toNat ≤ b.size)
    (hTT : s0.regs.get64 .r15 + BitVec.ofInt 64 (Int64.ofInt off).toInt = A TT)
    (htbl : ∀ y < 256, D.get? (A (TT + y)) = some c[y]!) (hTT2 : TT + 256 < 2 ^ 64)
    (he : ∀ s, s.dmem = D → KeepR s s0 → OpReads s eo ve) :
    ∀ n (jj : Word) (s : MachineData), s.dmem = D → KeepR s s0 → s.regs.get64 .rcx = A B →
      s.regs.get64 .rax = jj.toBitVec → jj < ve → ve.toNat - jj.toNat = n →
      (∀ s', s'.dmem = D → KeepR s' s0 →
        s'.regs.get64 .rax = (UInt64.ofNat (scanN b c jj.toNat ve.toNat)).toBitVec → Ev Q s' (at_ (kL + 8))) →
      Ev Q s (at_ kL) := by
  simp only [scanLoop] at hcode
  intro n
  induction n with
  | zero =>
    intro jj s _ _ _ _ hlt hn _
    have := UInt64.lt_iff_toNat_lt.mp hlt; omega
  | succ n ih =>
    intro jj s hD hK hrcx hrax hlt hn hexit
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    have hjb : jj.toNat < b.size := by omega
    have hfit := hsrc.fit
    refine ev_label hcode.head ?_
    refine ev_movzxR (d := .rdx) hcode.tail.head (b := b[jj.toNat]!) ?_ ?_
    · rw [hD, show s.regs.rcx.toBitVec + s.regs.rax.toBitVec = A (B + jj.toNat) by
        rw [← Reg64s.get64_rcx, ← Reg64s.get64_rax, hrcx, hrax]
        apply BitVec.eq_of_toNat_eq; simp [A, BitVec.toNat_add]]
      exact hsrc.get _ hjb
    have hy : (b[jj.toNat]!).toNat < 256 := (b[jj.toNat]!).toNat_lt
    refine ev_movzxS hcode.tail.tail.head (v := c[(b[jj.toNat]!).toNat]!) ?_ ?_
    · rw [hD]
      have h15 : (s.regs.set64 .rdx (b[jj.toNat]!).toUInt64.toBitVec).get64 .r15 = s0.regs.get64 .r15 := by
        rw [rget_set]; simp only [reduceCtorEq, ↓reduceIte]; exact hK .r15 (by decide) (by decide) (by decide)
      rw [h15, rget_set, if_pos rfl, add_swap, hTT]
      rw [show A TT + (b[jj.toNat]!).toUInt64.toBitVec = A (TT + (b[jj.toNat]!).toNat) by
        apply BitVec.eq_of_toNat_eq; simp [A, BitVec.toNat_add]]
      exact htbl _ hy
    refine ev_cmpRO (v := 0) hcode.tail.tail.tail.head (.inl rfl) ?_
    simp only [rget_set, ↓reduceIte]
    refine ev_jcc hcode.tail.tail.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · rw [interp_nz] at hcc
      have hc0 : c[(b[jj.toNat]!).toNat]! ≠ 0 := by
        intro h0; simp [h0] at hcc
      rw [hX]
      refine hexit _ hD (hK.ofEq (by keep_tac)) ?_
      rw [scanN_hit b c _ _ hlt' hc0]
      simp only [rget_set, reduceCtorEq, ↓reduceIte, hrax, UInt64.ofNat_toNat]
    · rw [interp_nz] at hcc
      have hc0 : c[(b[jj.toNat]!).toNat]! = 0 := by
        have h1 : (c[(b[jj.toNat]!).toNat]!).toUInt64 = 0 := by simpa using hcc
        have h2 := congrArg UInt64.toNat h1
        simp only [UInt8.toNat_toUInt64, UInt64.toNat_zero] at h2
        exact UInt8.toNat_inj.mp (by simpa using h2)
      have hj1 : (jj + 1).toNat = jj.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := ve.toNat_lt; omega
      refine ev_addRI hcode.tail.tail.tail.tail.tail.head fun st => ?_
      have hrax2 : ∀ (R : Reg64s), R = (s.regs.set64 .rdx (b[jj.toNat]!).toUInt64.toBitVec).set64 .rdx
          (c[(b[jj.toNat]!).toNat]!).toUInt64.toBitVec → R.get64 .rax = jj.toBitVec := by
        intro R hR; subst hR; simp only [rget_set, reduceCtorEq, ↓reduceIte, hrax]
      rw [hrax2 _ rfl, one_toBitVec, ← UInt64.toBitVec_add]
      refine ev_cmpRO (v := ve) hcode.tail.tail.tail.tail.tail.tail.head
        (he _ hD (hK.ofEq (by keep_tac))) ?_
      simp only [rget_set, ↓reduceIte]
      refine ev_jcc hcode.tail.tail.tail.tail.tail.tail.tail.head (fun hcc2 => ?_) (fun hcc2 => ?_)
      · rw [interp_c] at hcc2
        have hlt2 : jj + 1 < ve := by simpa using hcc2
        rw [hL]
        refine ih (jj + 1) _ hD (hK.ofEq (by keep_tac)) (by simp only [rget_set, reduceCtorEq, ↓reduceIte, hrcx])
          (by simp only [rget_set, ↓reduceIte]) hlt2 (by rw [hj1]; omega) fun s' h1 h2 h3 => hexit s' h1 h2 ?_
        rw [h3, scanN_miss b c _ _ hlt' hc0, hj1]
      · rw [interp_c] at hcc2
        have hge : ¬ (jj + 1 < ve) := by simpa using hcc2
        have hge' : ¬ (jj + 1).toNat < ve.toNat := fun h => hge (UInt64.lt_iff_toNat_lt.mpr h)
        refine ev_congr (hexit _ hD (hK.ofEq (by keep_tac)) ?_) (by omega)
        rw [scanN_miss b c _ _ hlt' hc0, scanN_end b c _ _ (by rw [hj1] at hge'; omega)]
        simp only [rget_set, ↓reduceIte]
        congr 1
end

section
variable [Host] {G : Layout} (hG : G.Ok)
  (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
  (p : Prog) (K : Stmt → M Sig) (P : Nat → Prop)
include hG hTab

/-- A block operand reads its value. -/
theorem opnd_reads {ctx : Ctx} (hT : ctx.tab = G.tab) {F : Nat} (hF : 8 * F + 8 < maxOff) {σ : St}
    {s : MachineData} (hI : Inv G ctx F σ s) {e : Expr} (hw : Expr.opndWf ctx.nl G.tab e = true) {v : Word}
    (hv : evalP σ e = .ok v) : OpReads s (opnd ctx e) v := by
  simp only [Expr.opndWf, Bool.and_eq_true] at hw
  have hsome : (simpleOp ctx e).isSome := by
    cases e <;> simp_all [Expr.isOpnd, simpleOp] <;> split <;> rfl
  have hs : simpleOp ctx e = some (opnd ctx e) := by
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome; simp [opnd, ho]
  obtain ⟨v', hv', hr⟩ := simpleOp_reads hT hTab hF hI hw.2 hs
  rw [hv] at hv'; cases hv'; exact hr

omit hG hTab in
theorem opnd_ok {σ : St} {nl : Nat} {e : Expr} (hw : Expr.opndWf nl G.tab e = true) :
    ∃ v, evalP σ e = .ok v := by
  simp only [Expr.opndWf, Bool.and_eq_true] at hw
  cases e <;> simp_all [Expr.isOpnd, evalP]

/-- An exit through `ca_error` with the memory unchanged. -/
theorem gpost_mem {top : Nat} {d s : MachineData} (hd : s.dmem = d.dmem) (hr : s.regs.rbp = d.regs.rbp) :
    GPost G top d s := ⟨hr, hd ▸ Pres.refl _ _⟩

/-- `x := rax`, the end of a scan. -/
theorem sim_storeRax {ctx : Ctx} {F : Nat} (hF : 8 * F + 8 < maxOff) {x : Var} (hx : x < ctx.nl) {σ : St}
    {s d : MachineData} {k : Nat} {Q : MachineState → Prop} (hId : Inv G ctx F σ d) (hKR : KeepR s d)
    (hd : s.dmem = d.dmem) {v : Word} (hrax : s.regs.get64 .rax = v.toBitVec)
    (hc : Host.prog[k]? = some (storeRax ctx x))
    (hnorm : ∀ d', Inv G ctx F (σ.setLoc x v) d' → SPost G F d d' → Ev Q d' (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  have hF' := hF; simp only [maxOff] at hF'
  have hI := hId.keepR hd hKR
  simp only [storeRax] at hc
  cases hl : ctx.alloc.lookup x with
  | some r =>
    rw [hl] at hc
    refine ev_movRR hc ?_
    rw [hrax]
    obtain ⟨h1, h2, h3, h4⟩ := set64_alloc_fields (R := s.regs) (hI.al.reg x r hl) v.toBitVec
    refine hnorm _ (hI.setLocR hx hl v s.status) ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [h1]; exact hKR.rsp
    · simp only [h2]; exact hKR.rbp
    · simp only [h4]; exact hKR.r15
    · simp only [h3, hKR.r14]; exact Nat.le_refl _
    · exact hd ▸ Pres.refl _ _
  | none =>
    rw [hl] at hc
    have := hI.slot x hx hl
    refine ev_movMR hc ⟨by lomega, by lomega⟩ ?_ ?_
    · rw [slot_addr _ x _ (by omega)]; exact hI.mapped (by lomega)
    rw [slot_addr _ x _ (by omega), hrax]
    refine hnorm _ (hI.setLoc hG hx hl v) ⟨hKR.rsp, hKR.rbp, hKR.r15, by rw [hKR.r14]; exact Nat.le_refl _, ?_⟩
    rw [← hd]
    refine Pres.of_only (Only.wrW ?_) ?_ ?_
    · have := hI.hi; have := hG.hi_le; omega
    · have := hI.lo; omega
    · have := hI.hi; simp only [top, hKR.rsp]; lomega

theorem sim_scan8 (x : Var) (s : BSrc) (i e : Expr) (c : List UInt8) :
    SimS p G (stepRun p K) P (.scan8 x s i e c) := by
  intro ctx F path k hT hF hc hwf hN htmp σ d Q hI hP hK
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  obtain ⟨⟨⟨⟨⟨hx, hws⟩, hwi⟩, hwe⟩, hc256⟩, hcpre⟩ := hwf
  simp only [compileS] at hc hK
  have hF' := hF; simp only [maxOff] at hF'
  have hTab' := hTab; simp only [maxOff] at hTab'
  obtain ⟨vi, hvi⟩ := opnd_ok (σ := σ) hwi
  obtain ⟨ve, hve⟩ := opnd_ok (σ := σ) hwe
  have hrun := step_scan8_run p K σ x s i e c hvi hve
  have hLlt := src8_size_lt hG hI.mem hws
  have hcS := hc.left
  have hcT := hc.right
  simp only [scan8Code] at hcS
  have hpre := hcS.left.left
  have hloop := hcS.left.right
  have hXh : Host.prog[k + 18]? = some (.label (ctx.lbl path "X")) := by
    have := hcS.right.head; simpa [scanLoop] using this
  have hst : Host.prog[k + 19]? = some (storeRax ctx x) := by
    have := hcT.head; simpa [scan8Code, scanLoop] using this
  have hXl : label (ctx.lbl path "X") = at_ (k + 18) := by
    have := Code.label hcS.right (i := 0) rfl; simpa [scanLoop] using this
  have hLl : label (ctx.lbl path "L") = at_ (k + 10) := by
    have := Code.label hloop (i := 0) rfl; simpa using this
  have hlen : k + (scan8Code ctx path s i e c ++ [storeRax ctx x]).length = k + 19 + 1 := by
    simp [scan8Code, scanLoop]
  -- the end: `x := rax`, from a state with the memory and the registers but the scratch ones of `d`
  have fin : ∀ s' (v : Word), s'.dmem = d.dmem → KeepR s' d → s'.regs.get64 .rax = v.toBitVec →
      stepRun p K (.scan8 x s i e c) σ = .ok (.normal, σ.setLoc x v) → Ev Q s' (at_ (k + 18)) := by
    intro s' v hd hk hr hrun'
    refine ev_label hXh ?_
    exact sim_storeRax hG hTab hF hx hI hk hd hr hst fun d' hI' hS =>
      ev_congr (hK.normal _ d' hrun' hI' hS) hlen
  have hInv : ∀ s', s'.dmem = d.dmem → KeepR s' d → Inv G ctx F σ s' := fun s' hd hk => hI.keepR hd hk
  have herr : ∀ s', s'.dmem = d.dmem → KeepR s' d → ¬ (vi ≤ ve ∧ ve.toNat ≤ (σ.mem.src8 s).size) →
      Ev Q s' (label errorL) := fun s' hd hk hn =>
    hK.err s' ⟨.oob, by rw [hrun, if_neg hn], by simp⟩ (gpost_mem hG hTab hd hk.rbp)
  refine sim_srcLen hG hT hTab hI hws (r := .rdx) hpre.head ?_
  refine ev_movRO hpre.tail.head (opnd_reads hG hTab hT hF (hInv _ (by rfl) ((KeepR.refl d).ofEq (by keep_tac))) hwe hve) ?_
  refine ev_cmpRO (v := UInt64.ofNat (σ.mem.src8 s).size) hpre.tail.tail.head
    (.inr (.inr ⟨.rdx, rfl, by simp [rget_set]⟩)) ?_
  simp only [rget_set, reduceCtorEq, ↓reduceIte]
  refine ev_jcc hpre.tail.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · rw [interp_a] at hcc
    refine herr _ (by rfl) ((KeepR.refl d).ofEq (by keep_tac)) fun ⟨_, h⟩ => ?_
    simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hLlt] at hcc
    omega
  rw [interp_a] at hcc
  have hveL : ve.toNat ≤ (σ.mem.src8 s).size := by
    simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hLlt] at hcc
    omega
  refine ev_movRO hpre.tail.tail.tail.tail.head
    (opnd_reads hG hTab hT hF (hInv _ (by rfl) ((KeepR.refl d).ofEq (by keep_tac))) hwi hvi) ?_
  refine ev_cmpRO (v := ve) hpre.tail.tail.tail.tail.tail.head
    (opnd_reads hG hTab hT hF (hInv _ (by rfl) ((KeepR.refl d).ofEq (by keep_tac))) hwe hve) ?_
  simp only [rget_set, reduceCtorEq, ↓reduceIte]
  refine ev_jcc hpre.tail.tail.tail.tail.tail.tail.head (fun hcc2 => ?_) (fun hcc2 => ?_)
  · rw [interp_a] at hcc2
    refine herr _ (by rfl) ((KeepR.refl d).ofEq (by keep_tac)) fun ⟨h, _⟩ => ?_
    simp only [decide_eq_true_eq] at hcc2
    exact absurd h (UInt64.not_le.mpr hcc2)
  rw [interp_a] at hcc2
  have hij : vi ≤ ve := by simpa using hcc2
  have hok : stepRun p K (.scan8 x s i e c) σ =
      .ok (.normal, σ.setLoc x (UInt64.ofNat (scanN (σ.mem.src8 s) c vi.toNat ve.toNat))) := by
    rw [hrun, if_pos ⟨hij, hveL⟩]
  refine sim_srcBase (σ := σ) (F := F) hG hT hTab ?_ hws hpre.tail.tail.tail.tail.tail.tail.tail.head fun B hB => ?_
  · exact hInv _ (by rfl) ((KeepR.refl d).ofEq (by keep_tac))
  refine ev_cmpRO (v := ve) hpre.tail.tail.tail.tail.tail.tail.tail.tail.head
    (opnd_reads hG hTab hT hF (hInv _ (by rfl) ((KeepR.refl d).ofEq (by keep_tac))) hwe hve) ?_
  simp only [rget_set, reduceCtorEq, ↓reduceIte]
  refine ev_jcc hpre.tail.tail.tail.tail.tail.tail.tail.tail.tail.head (fun hcc3 => ?_) (fun hcc3 => ?_)
  · rw [interp_nc] at hcc3
    have heq : vi = ve := UInt64.le_antisymm hij (by simpa using hcc3)
    rw [hXl]
    refine fin _ vi (by rfl) ((KeepR.refl d).ofEq (by keep_tac)) (by simp [rget_set]) ?_
    rw [hok, scanN_end _ _ _ _ (by rw [heq]; omega), UInt64.ofNat_toNat]
  rw [interp_nc] at hcc3
  have hlt : vi < ve := by simpa using hcc3
  -- the class table
  have hcp := List.isPrefixOf_iff_prefix.mp hcpre
  have hidx : romIdx c G.tab.rom + c.length ≤ G.tab.rom.length := by
    have h1 := congrArg List.length (List.prefix_iff_eq_take.mp hcp)
    have := romIdx_le c G.tab.rom; simp at h1; omega
  have hw8 : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
  have hTE := hG.tab_end
  simp only [Layout.tabEnd] at hTE
  have htbl : ∀ y < 256, d.dmem.get? (A (G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + romIdx c G.tab.rom + y)) =
      some c[y]! := fun y hy => by
    have hb := hI.mem.rom (romIdx c G.tab.rom + y) (by omega)
    have hd : G.tab.rom[romIdx c G.tab.rom + y]'(by omega) = c[y]'(by omega) := by
      rw [hcp.getElem (by omega), List.getElem_drop]
    rw [hd] at hb
    rw [show G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + romIdx c G.tab.rom + y =
      G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + (romIdx c G.tab.rom + y) by omega, hb]
    simp [show y < c.length by omega]
  have hTT : d.regs.get64 .r15 + BitVec.ofInt 64 (Int64.ofInt (ctx.tab.romBase + romIdx c ctx.tab.rom)).toInt =
      A (G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + romIdx c G.tab.rom) := by
    rw [hT]
    have hof : (Int64.ofInt (G.tab.romBase + (romIdx c G.tab.rom : Int))).toInt =
        G.tab.romBase + (romIdx c G.tab.rom : Int) := by
      simp only [Int64.toInt_ofInt, Tab.romBase]; rw [Int.bmod_eq_of_le] <;> simp [Int64.size] <;> omega
    rw [hof]
    apply BitVec.eq_of_toNat_eq
    simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec, BitVec.toNat_add, BitVec.toNat_ofInt, A,
      BitVec.toNat_ofNat, hI.r15, Tab.romBase]
    omega
  have hloop' : Code (scanLoop (ctx.lbl path "L") (ctx.lbl path "X") (ctx.tab.romBase + romIdx c ctx.tab.rom)
      (opnd ctx e)) (k + 10) := by simpa using hloop
  refine ev_congr (scan_loop hloop' hLl (by rw [hXl]) hB hveL hTT htbl (by omega)
    (fun s' hd hk => opnd_reads hG hTab hT hF (hInv s' hd hk) hwe hve) _ vi _ (by rfl)
    ((KeepR.refl d).ofEq (by keep_tac)) (by simp [rget_set]) (by simp [rget_set]) hlt rfl
    fun s' hd hk hr => ev_congr (fin s' _ hd hk hr hok) (by omega)) (by simp)
end

end L.Compiler
