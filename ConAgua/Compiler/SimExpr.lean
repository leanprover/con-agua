module

public import ConAgua.Compiler.Rel

@[expose] public section

/-!
# Expressions and conditions

`evalE` never changes the state, so its run is a pure function `evalP` of the state.
`sim_expr`: the code of `e` leaves `evalP σ e` in `rax`, or jumps to `ca_error` exactly when
`evalP σ e` fails; it changes only the temporaries from `t` on.
-/

namespace L.Compiler

open L

/-- `evalE`, without the state. -/
def evalP (σ : St) : Expr → Except Err Word
  | .const w => .ok w
  | .var x => .ok (σ.loc x)
  | .bin op a b => do
    let x ← evalP σ a
    let y ← evalP σ b
    return op.eval x y
  | .ld8 a i => do
    let j ← evalP σ i
    if h : j.toNat < (σ.mem.arr8 a).size then .ok (σ.mem.arr8 a)[j.toNat].toUInt64 else .error .oob
  | .ld64 a i => do
    let j ← evalP σ i
    if h : j.toNat < (σ.mem.arr64 a).size then .ok (σ.mem.arr64 a)[j.toNat] else .error .oob
  | .len8 a => .ok (σ.mem.len8 a)
  | .len64 a => .ok (σ.mem.len64 a)
  | .cmpw c a b => do
    let x ← evalP σ a
    let y ← evalP σ b
    return c.evalW x y
  | .ldc d i => do
    let j ← evalP σ i
    if h : j.toNat < d.length then .ok d[j.toNat].toUInt64 else .error .oob
  | .glob g => .ok (σ.mem.glob g)
  | .ld64t a t i => do
    let u ← evalP σ t
    let j ← evalP σ i
    if h : j.toNat < (σ.mem.arr64 (tierA a u)).size then .ok (σ.mem.arr64 (tierA a u))[j.toNat]
    else .error .oob
  | .len64t a t => do
    let u ← evalP σ t
    .ok (σ.mem.len64 (tierA a u))
  | .ld8x8 b i => do
    let j ← evalP σ i
    if j.toNat + 8 ≤ (σ.mem.src8 b).size then .ok (le64 (σ.mem.src8 b) j.toNat) else .error .oob

theorem evalE_run (σ : St) (e : Expr) : (evalE e).run σ = (evalP σ e).map (·, σ) := by
  induction e with
  | const => rfl
  | var => rfl
  | bin op a b iha ihb =>
    simp only [evalE, evalP, StateT.run_bind] at *
    rw [iha]
    cases evalP σ a <;> simp [Except.map, bind, Except.bind, ihb]
    · cases evalP σ b <;> rfl
  | ld8 a i ih =>
    simp only [evalE, evalP, StateT.run_bind, ih]
    cases evalP σ i with
    | error => rfl
    | ok j =>
      simp only [Except.map, bind, Except.bind, L.ld8, pure]
      by_cases hj : j.toNat < (σ.mem.arr8 a).size
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj, StateT.pure]; rfl
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj]; rfl
  | ld64 a i ih =>
    simp only [evalE, evalP, StateT.run_bind, ih]
    cases evalP σ i with
    | error => rfl
    | ok j =>
      simp only [Except.map, bind, Except.bind, L.ld64, pure]
      by_cases hj : j.toNat < (σ.mem.arr64 a).size
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj, StateT.pure]; rfl
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj]; rfl
  | len8 => rfl
  | len64 => rfl
  | glob => rfl
  | cmpw op a b iha ihb =>
    simp only [evalE, evalP, StateT.run_bind] at *
    rw [iha]
    cases evalP σ a <;> simp [Except.map, bind, Except.bind, ihb]
    · cases evalP σ b <;> rfl
  | ldc d i ih =>
    simp only [evalE, evalP, StateT.run_bind, ih]
    cases evalP σ i with
    | error => rfl
    | ok j =>
      simp only [Except.map, bind, Except.bind, L.ldc, pure]
      by_cases hj : j.toNat < d.length
      · simp [hj]; rfl
      · simp [hj]; rfl
  | ld64t a t i iht ihi =>
    simp only [evalE, evalP, StateT.run_bind, iht]
    cases evalP σ t with
    | error => rfl
    | ok u =>
      simp only [Except.map, bind, Except.bind, ihi]
      cases evalP σ i with
      | error => rfl
      | ok j =>
        simp only [L.ld64, pure]
        by_cases hj : j.toNat < (σ.mem.arr64 (tierA a u)).size
        · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj, StateT.pure,
            bind, Except.bind, Except.pure, pure]
        · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj, bind,
            Except.bind, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure]
  | len64t a t ih =>
    simp only [evalE, evalP, StateT.run_bind, ih]
    cases evalP σ t <;> rfl
  | ld8x8 b i ih =>
    simp only [evalE, evalP, StateT.run_bind, ih]
    cases evalP σ i with
    | error => rfl
    | ok j =>
      simp only [Except.map, bind, Except.bind, L.ld8x8, pure]
      by_cases hj : j.toNat + 8 ≤ (σ.mem.src8 b).size
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj, StateT.pure]; rfl
      · simp [StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, hj]; rfl


theorem romIdx_le (d rom : List UInt8) : romIdx d rom ≤ rom.length := by
  induction rom with
  | nil => simp [romIdx]
  | cons b rom ih => simp only [romIdx]; split <;> simp; omega


/-! ## Blocks: condition codes, byte sources, 8-byte loads (lane blkcopy) -/

theorem interp_c (a b : UInt64) : CondCode.c.interp (cmpFlags a.toBitVec b.toBitVec) = decide (a < b) := by
  have := cmpCC_interp .ult a b; simpa [cmpCC, Cmp.eval] using this

theorem interp_nc (a b : UInt64) : CondCode.nc.interp (cmpFlags a.toBitVec b.toBitVec) = decide (b ≤ a) := by
  have := neg_interp .c (cmpFlags a.toBitVec b.toBitVec)
  simp only [CondCode.neg] at this
  rw [this, interp_c]
  simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

theorem interp_a (a b : UInt64) : CondCode.a.interp (cmpFlags a.toBitVec b.toBitVec) = decide (b < a) := by
  have := neg_interp .be (cmpFlags a.toBitVec b.toBitVec)
  simp only [CondCode.neg] at this
  have h2 := cmpCC_interp .ule a b
  simp only [cmpCC] at h2
  rw [this, h2]
  simp only [Cmp.eval, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
  by_cases h : a.toNat ≤ b.toNat <;> simp [h] <;> omega

theorem interp_nz (a b : UInt64) : CondCode.nz.interp (cmpFlags a.toBitVec b.toBitVec) = (a != b) := by
  have := cmpCC_interp .ne a b; simpa [cmpCC, Cmp.eval] using this

/-- **An 8-byte load reads `le64`.** -/
theorem rdW_le64 {d : DataMem} {X : Nat} {b : Array UInt8} {k : Nat}
    (h : ∀ j < 8, d.get? (A (X + j)) = some b[k + j]!) : rdW d (A X) = some (le64 b k) :=
  rdW_bytes h

/-- What a byte source is on the machine: its bytes at `B`, below `2^64`. -/
structure SrcAt (G : Layout) (b : Array UInt8) (d : DataMem) (B : Nat) : Prop where
  fit : B + b.size < 2 ^ 64
  get : ∀ x < b.size, d.get? (A (B + x)) = some b[x]!
  out64 : ∀ x < b.size, ∀ a < G.tab.nw, ¬ G.In64 a (B + x)
  outSt : ∀ x < b.size, ¬ G.InStack (B + x)

/-! ## Evaluating an expression on the machine -/

/-- What evaluating an expression with temporaries from `t` may change: `rax`, `rcx`, `rdx`,
the flags and the temporaries `t, t+1, …` of the frame. -/
structure EPost (nl F t : Nat) (s s' : MachineData) : Prop where
  rsp : s'.regs.rsp = s.regs.rsp
  rbp : s'.regs.rbp = s.regs.rbp
  r14 : s'.regs.r14 = s.regs.r14
  r15 : s'.regs.r15 = s.regs.r15
  rsi : s'.regs.rsi = s.regs.rsi
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.regs.get64 r = s.regs.get64 r
  mem : Only (s.regs.rsp.toNat + 8 * (nl + t)) (s.regs.rsp.toNat + 8 * F) s.dmem s'.dmem

theorem EPost.refl (nl F t : Nat) (s : MachineData) : EPost nl F t s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, Only.refl _ _ _⟩

theorem EPost.trans {nl F t t' : Nat} {s s' s'' : MachineData} (h : EPost nl F t s s')
    (h' : EPost nl F t' s' s'') (ht : t ≤ t') : EPost nl F t s s'' := by
  have hm := h'.mem
  rw [h.rsp] at hm
  exact ⟨h'.rsp.trans h.rsp, h'.rbp.trans h.rbp, h'.r14.trans h.r14, h'.r15.trans h.r15,
    h'.rsi.trans h.rsi, fun r h1 h2 h3 => (h'.keep r h1 h2 h3).trans (h.keep r h1 h2 h3),
    h.mem.trans hm (by omega) (Nat.le_refl _)⟩

/-- The registers of an expression step: only `rax`, `rcx`, `rdx` and the flags change. -/
theorem EPost.regs {nl F t : Nat} {s : MachineData} {r : Reg64} (hr : r = .rax ∨ r = .rcx ∨ r = .rdx)
    (v : BitVec 64) (st : StatusFlags) :
    EPost nl F t s { s with regs := s.regs.set64 r v, status := st } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r' h1 h2 h3 => get64_set64_scratch hr v r' h1 h2 h3, Only.refl _ _ _⟩ <;>
    rcases hr with rfl | rfl | rfl <;> rfl

theorem EPost.regs' {nl F t : Nat} {s : MachineData} {r : Reg64} (hr : r = .rax ∨ r = .rcx ∨ r = .rdx)
    (v : BitVec 64) : EPost nl F t s { s with regs := s.regs.set64 r v } :=
  EPost.regs (st := s.status) hr v

theorem EPost.flags {nl F t : Nat} {s : MachineData} (st : StatusFlags) :
    EPost nl F t s { s with status := st } :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, Only.refl _ _ _⟩


theorem EPost.store {nl F t j : Nat} {s : MachineData} {v : BitVec 64} (hj : nl + t ≤ j) (hjF : j + 1 ≤ F)
    (hov : s.regs.rsp.toNat + 8 * F ≤ 2 ^ 64) :
    EPost nl F t s { s with dmem := wrW s.dmem (A (s.regs.rsp.toNat + 8 * j)) v } :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, (Only.wrW (by omega)).mono (by omega) (by omega)⟩

theorem EPost.of_eq {nl F t : Nat} {s s' s'' : MachineData} (h : EPost nl F t s s')
    (hd : s''.dmem = s'.dmem) (h1 : s''.regs.rsp = s'.regs.rsp) (h2 : s''.regs.rbp = s'.regs.rbp)
    (h3 : s''.regs.r14 = s'.regs.r14) (h4 : s''.regs.r15 = s'.regs.r15) (h5 : s''.regs.rsi = s'.regs.rsi)
    (h6 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s''.regs.get64 r = s'.regs.get64 r) :
    EPost nl F t s s'' :=
  ⟨h1.trans h.rsp, h2.trans h.rbp, h3.trans h.r14, h4.trans h.r15, h5.trans h.rsi,
    fun r a b c => (h6 r a b c).trans (h.keep r a b c), hd ▸ h.mem⟩

/-- `Inv` after an expression step. -/
theorem Inv.ofE {G : Layout} (hG : G.Ok) {ctx : Ctx} {F t : Nat} {σ : St} {s s' : MachineData}
    (hI : Inv G ctx F σ s) (hE : EPost ctx.nl F t s s') : Inv G ctx F σ s' :=
  hI.only hG (hE.mem.mono (by omega) (Nat.le_refl _)) hE.rsp hE.r15 (fun r hr =>
    hE.keep r (allocRegs_ne hr).1 (allocRegs_ne hr).2.1 (allocRegs_ne hr).2.2.1)
    fun _ => rsi_of_get64 (hE.keep .rsi (by decide) (by decide) (by decide))

theorem slot_addr (s : MachineData) (j : Nat) (off : Int) (h : off = 8 * (j : Int)) :
    A ((s.regs.get64 .rsp).toNat + off.toNat) = A (s.regs.rsp.toNat + 8 * j) := by
  subst h; simp only [Reg64s.get64_rsp, UInt64.toNat_toBitVec]; congr 1; (try omega)

theorem Inv.mapped {G : Layout} {ctx : Ctx} {F : Nat} {σ : St} {s : MachineData} (hI : Inv G ctx F σ s) {j : Nat}
    (hj : j ≤ F) : (rdW s.dmem (A (s.regs.rsp.toNat + 8 * j))).isSome :=
  isSome_rdW fun i hi => by
    rw [A_add]
    exact hI.mem.stack _ ⟨by have := hI.lo; omega, by have := hI.hi; omega⟩

theorem toNat_eight_mul (x : Nat) : (8 * (x : Int)).toNat = 8 * x := by omega

/-- `omega`, after unfolding L's `Nat` synonyms (see docs/gaps/omega-nat-synonym-hyp.lean). -/
macro "lomega" : tactic => `(tactic| (try simp only [L.Var, L.ArrId] at *) <;> omega)

/-- The registers but `rax`, `rcx`, `rdx` agree (`EPost.keep`), for states built by register
writes. -/
macro "keep_tac" : tactic => `(tactic| (intro r h1 h2 h3; cases r <;>
  first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | rfl))

attribute [local simp] Reg64s.set64_rax Reg64s.set64_rcx Reg64s.set64_rdx Reg64s.set64_rsi
  Reg64s.set64_rsp Reg64s.set64_r14

section
variable [Host] {G : Layout} (hG : G.Ok)
include hG

/-- `r := len(s)`. -/
theorem sim_srcLen {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff) {F : Nat} {σ : St} {s : MachineData}
    (hI : Inv G ctx F σ s) {b : BSrc} (hw : BSrc.wf G.tab b = true) {r : Reg64} {k : Nat}
    (hc : Host.prog[k]? = some (srcLen ctx r b)) {Q : MachineState → Prop}
    (h : Ev Q { s with regs := s.regs.set64 r (UInt64.ofNat (σ.mem.src8 b).size).toBitVec } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  simp only [maxOff] at hTab
  cases b with
  | arr a =>
    simp only [BSrc.wf, decide_eq_true_eq] at hw
    simp only [srcLen] at hc
    refine ev_movRM hc ⟨by simp [Tab.len8]; lomega, by simp [Tab.len8]; lomega⟩
      (v := UInt64.ofNat (G.s8 a)) ?_ ?_
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len8 a hw
    · simpa [Mem.src8, hI.mem.size8 a hw] using h
  | rom d =>
    simp only [srcLen] at hc
    exact ev_movRI hc (by simpa [Mem.src8] using h)

/-- `rcx :=` the address of the source's byte `0`. -/
theorem sim_srcBase {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff) {F : Nat} {σ : St} {s : MachineData}
    (hI : Inv G ctx F σ s) {b : BSrc} (hw : BSrc.wf G.tab b = true) {k : Nat}
    (hc : Host.prog[k]? = some (srcBase ctx b)) {Q : MachineState → Prop}
    (h : ∀ B, SrcAt G (σ.mem.src8 b) s.dmem B →
      Ev Q { s with regs := s.regs.set64 .rcx (A B) } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  have hTE := hG.tab_end
  simp only [Layout.tabEnd] at hTE
  simp only [maxOff] at hTab
  cases b with
  | arr a =>
    simp only [BSrc.wf, decide_eq_true_eq] at hw
    simp only [srcBase] at hc
    have hsz := hI.mem.size8 a hw
    have hend := hG.end8 a hw
    refine ev_movRM hc ⟨by simp [Tab.base8]; lomega, by simp [Tab.base8]; lomega⟩
      (v := UInt64.ofNat (G.b8 a)) ?_ ?_
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.base8 a hw
    have := h (G.b8 a) ⟨by simp only [Mem.src8]; omega, fun x hx => by
      simp only [Mem.src8] at hx ⊢
      rw [hI.mem.get8 a hw x hx]; simp [hx], fun x hx b hb => by
      simp only [Mem.src8] at hx
      exact hG.arr8_64 a hw b hb _ ⟨by omega, by omega⟩, fun x hx hst => by
      simp only [Mem.src8] at hx
      exact hG.stack_arr _ hst (Or.inl ⟨a, hw, by omega, by omega⟩)⟩
    have e : (UInt64.ofNat (G.b8 a)).toBitVec = A (G.b8 a) := by
      apply BitVec.eq_of_toNat_eq; simp [A]
    rw [e]; exact this
  | rom d =>
    simp only [BSrc.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [srcBase] at hc
    have hpre := List.prefix_iff_eq_take.mp (List.isPrefixOf_iff_prefix.mp hw.1)
    have hidx : romIdx d G.tab.rom + d.length ≤ G.tab.rom.length := by
      have h1 := congrArg List.length hpre; have := romIdx_le d G.tab.rom; simp at h1; omega
    have hw8 : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
    have hoff : SmallOff (G.tab.romBase + (romIdx d G.tab.rom : Int)) := by
      simp only [Tab.romBase] at *; omega
    rw [hT] at hc
    refine ev_lea hc hoff ?_
    have := h (G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + romIdx d G.tab.rom)
      ⟨by simp only [Mem.src8, List.size_toArray]; omega, fun x hx => by
        simp only [Mem.src8, List.size_toArray] at hx ⊢
        have hb := hI.mem.rom (romIdx d G.tab.rom + x) (by omega)
        have hd : G.tab.rom[romIdx d G.tab.rom + x]'(by omega) = d[x] := by
          rw [(List.isPrefixOf_iff_prefix.mp hw.1).getElem hx, List.getElem_drop]
        rw [hd] at hb
        rw [show G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + romIdx d G.tab.rom + x =
          G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + (romIdx d G.tab.rom + x) by omega, hb]
        simp [hx], fun x hx b hb h64 => by
        simp only [Mem.src8, List.size_toArray] at hx
        exact hG.tab_arr _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩ (Or.inr ⟨b, hb, h64⟩),
        fun x hx hst => by
        simp only [Mem.src8, List.size_toArray] at hx
        exact hG.tab_stack _ ⟨by omega, by simp only [Layout.tabEnd]; omega⟩ hst⟩
    have e : (s.regs.get64 .r15).toNat + (G.tab.romBase + (romIdx d G.tab.rom : Int)).toNat =
        G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + romIdx d G.tab.rom := by
      simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, Tab.romBase]; omega
    rw [e]; exact this

end

theorem src8_size_lt {G : Layout} (hG : G.Ok) {σ : St} {d : DataMem} (hm : MemRel G σ.mem d) {b : BSrc}
    (hw : BSrc.wf G.tab b = true) : (σ.mem.src8 b).size < 2 ^ 64 := by
  cases b with
  | arr a =>
    simp only [BSrc.wf, decide_eq_true_eq] at hw
    have := hG.end8 a hw; have := hm.size8 a hw
    simp only [Mem.src8]; omega
  | rom d =>
    simp only [BSrc.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [Mem.src8, List.size_toArray]; omega

/-! ## Simple operands -/

section
variable [Host] {G : Layout}

/-- A simple operand reads the value of its expression. -/
theorem simpleOp_reads {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    {F : Nat} (hF : 8 * F + 8 < maxOff) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    {b : Expr} (hwf : Expr.wf ctx.nl G.tab b = true) {o : Operand .W64} (h : simpleOp ctx b = some o) :
    ∃ v, evalP σ b = .ok v ∧ OpReads s o v := by
  simp only [maxOff] at hF hTab
  cases b with
  | const w =>
    simp only [simpleOp] at h
    split at h
    · cases h; exact ⟨w, rfl, .inl rfl⟩
    · cases h
  | var x =>
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    simp only [simpleOp] at h
    cases hl : ctx.alloc.lookup x with
    | some r =>
      simp only [hl, Option.some.injEq] at h; subst h
      exact ⟨σ.loc x, rfl, .inr (.inr ⟨r, rfl, hI.reg x hwf r hl⟩)⟩
    | none =>
      simp only [hl, Option.some.injEq] at h; subst h
      have := hI.slot x hwf hl
      refine ⟨σ.loc x, rfl, .inr (.inl ⟨_, _, rfl, ⟨by lomega, by lomega⟩, ?_⟩)⟩
      rw [Reg64s.get64_rsp, UInt64.toNat_toBitVec, toNat_eight_mul]; exact hI.frame x hwf hl
  | len8 a =>
    simp only [simpleOp, Option.some.injEq] at h; subst h
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    refine ⟨UInt64.ofNat (G.s8 a), by simp [evalP, Mem.len8, hI.mem.size8 a hwf],
      .inr (.inl ⟨_, _, rfl, ⟨by simp [Tab.len8]; lomega, by simp [Tab.len8]; lomega⟩, ?_⟩)⟩
    rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len8 a hwf
  | len64 a =>
    simp only [simpleOp, Option.some.injEq] at h; subst h
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    have hw64 := G.tab.wpos_lt hwf
    refine ⟨UInt64.ofNat (G.s64 a), by simp [evalP, Mem.len64, hI.mem.size64 a hwf],
      .inr (.inl ⟨_, _, rfl, ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩, ?_⟩)⟩
    rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len64 a hwf
  | glob g =>
    simp only [simpleOp, Option.some.injEq] at h; subst h
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    refine ⟨σ.mem.glob g, rfl, .inr (.inl ⟨_, _, rfl, ⟨by simp [Tab.globOff, Tab.globBase]; lomega,
        by simp [hT, Tab.globOff, Tab.globBase]; lomega⟩, ?_⟩)⟩
    rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT, Layout.globAddr_toNat]
    exact hI.mem.glob g hwf
  | _ => simp [simpleOp] at h

/-- `r := b` in one instruction, for a simple `b`. -/
theorem sim_loadInto {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    {F : Nat} (hF : 8 * F + 8 < maxOff) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    {r : Reg64} {b : Expr} (hwf : Expr.wf ctx.nl G.tab b = true) {code : Program} {k : Nat}
    (h : loadInto ctx r b = some code) (hc : Code code k) :
    ∃ v, evalP σ b = .ok v ∧ code.length = 1 ∧ ∀ Q,
      Ev Q { s with regs := s.regs.set64 r v.toBitVec } (at_ (k + 1)) → Ev Q s (at_ k) := by
  unfold loadInto at h
  split at h
  · cases h; exact ⟨_, rfl, rfl, fun Q hq => ev_movRI hc.head hq⟩
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v, hv, hr⟩ := simpleOp_reads hT hTab hF hI hwf ho
    exact ⟨v, hv, rfl, fun Q hq => ev_movRO hc.head hr hq⟩

omit [Host] in
theorem shl_mod64 (x k : UInt64) : x <<< UInt64.ofNat (k.toNat % 64) = x <<< k := by
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_shiftLeft]

omit [Host] in
theorem shr_mod64 (x k : UInt64) : x >>> UInt64.ofNat (k.toNat % 64) = x >>> k := by
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_shiftRight]

omit [Host] in
theorem log2_lt64 (k : UInt64) (h : k.toNat = 2 ^ Nat.log2 k.toNat) : Nat.log2 k.toNat < 64 := by
  rw [Nat.log2_lt (by intro h0; rw [h0] at h; simp at h)]; exact k.toNat_lt

omit [Host] in
/-- Multiplying by a power of two is a shift. -/
theorem shl_log2 (x k : UInt64) (h : k.toNat = 2 ^ Nat.log2 k.toNat) :
    x <<< UInt64.ofNat (Nat.log2 k.toNat) = x * k := by
  have hl := log2_lt64 k h
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_mul, BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have : (2:Nat) ^ Nat.log2 k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hl
  simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt hl]
  omega

/-- `rax := rax op rcx` (`binCode`), as a continuation. -/
theorem sim_binCode {op : BinOp} {k : Nat} (hc : Code (binCode op) k) {nl F t : Nat} {s : MachineData}
    {Q : MachineState → Prop}
    (hq : ∀ s', s'.regs.rax = op.eval s.regs.rax s.regs.rcx → EPost nl F t s s' →
      Ev Q s' (at_ (k + (binCode op).length))) : Ev Q s (at_ k) := by
  by_cases hop : op = .mulhi
  · subst hop
    simp only [binCode] at hc hq
    refine ev_mul hc.head fun st => ?_
    refine ev_movRR hc.tail.head ?_
    refine ev_congr (hq _ (by simp) ?_) rfl
    exact EPost.of_eq (s' := s) (EPost.refl _ _ _ _) rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
  · have hb : binCode op = [binInstr op] := by cases op <;> simp_all [binCode]
    rw [hb] at hc hq
    refine ev_bin hop hc.head fun st => ?_
    refine ev_congr (hq _ (by simp) ?_) rfl
    exact EPost.of_eq (s' := s) (EPost.refl _ _ _ _) rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)

/-- `rax := rax op b` for a simple `b` (`binSimple`). -/
theorem sim_binSimple {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    {F : Nat} (hF : 8 * F + 8 < maxOff) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    {op : BinOp} {b : Expr} (hwf : Expr.wf ctx.nl G.tab b = true) {code : Program} {k : Nat}
    (h : binSimple ctx op b = some code) (hc : Code code k) :
    ∃ vb, evalP σ b = .ok vb ∧ ∀ t Q,
      (∀ s', s'.regs.rax = op.eval s.regs.rax vb → EPost ctx.nl F t s s' →
        Ev Q s' (at_ (k + code.length))) → Ev Q s (at_ k) := by
  unfold binSimple at h
  split at h
  · cases h
    refine ⟨_, rfl, fun t Q hq => ?_⟩
    refine ev_shiftI (op := .shl) (Nat.mod_lt _ (by decide)) (Or.inl rfl) hc.head fun st => ?_
    exact hq _ (by simp [BinOp.eval, shl_mod64]) (EPost.regs (by simp) _ _)
  · cases h
    refine ⟨_, rfl, fun t Q hq => ?_⟩
    refine ev_shiftI (op := .shr) (Nat.mod_lt _ (by decide)) (Or.inr rfl) hc.head fun st => ?_
    exact hq _ (by simp [BinOp.eval, shr_mod64]) (EPost.regs (by simp) _ _)
  · rename_i kk
    split at h
    · rename_i hp
      cases h
      have hp' : kk.toNat = 2 ^ Nat.log2 kk.toNat := by simpa using hp
      refine ⟨_, rfl, fun t Q hq => ?_⟩
      refine ev_shiftI (op := .shl) (log2_lt64 kk hp') (Or.inl rfl) hc.head fun st => ?_
      exact hq _ (by simp [BinOp.eval, shl_log2 _ _ hp']) (EPost.regs (by simp) _ _)
    · simp only [loadInto, Option.map_some, Option.some.injEq] at h
      subst h
      refine ⟨_, rfl, fun t Q hq => ?_⟩
      refine ev_movRI hc.head ?_
      refine sim_binCode (op := .mul) (nl := ctx.nl) (F := F) (t := t) hc.tail fun s' hr hE => ?_
      refine ev_congr (hq s' (by simpa using hr) ((EPost.regs' (by simp) _).trans hE (Nat.le_refl _))) ?_
      simp [binCode]
  · split at h
    · rename_i d hd
      cases h
      obtain ⟨o, ho, hdo⟩ := Option.bind_eq_some_iff.mp hd
      obtain ⟨v, hv, hr⟩ := simpleOp_reads hT hTab hF hI hwf ho
      refine ⟨v, hv, fun t Q hq => ?_⟩
      exact ev_binO hdo hc.head hr fun st => hq _ (by simp) (EPost.regs (by simp) _ _)
    · obtain ⟨lc, hl, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨v, hv, hlen, hld⟩ := sim_loadInto (r := .rcx) hT hTab hF hI hwf hl hc.left
      refine ⟨v, hv, fun t Q hq => hld Q ?_⟩
      rw [← hlen]
      refine sim_binCode (nl := ctx.nl) (F := F) (t := t) hc.right fun s' hr hE => ?_
      refine ev_congr (hq s' (by simpa using hr) ((EPost.regs' (by simp) _).trans hE (Nat.le_refl _))) ?_
      simp only [List.length_append]; omega

/-- `cmp rax, b` for a simple `b` (`cmpSimple`). -/
theorem sim_cmpSimple {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    {F : Nat} (hF : 8 * F + 8 < maxOff) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    {b : Expr} (hwf : Expr.wf ctx.nl G.tab b = true) {code : Program} {k : Nat}
    (h : cmpSimple ctx b = some code) (hc : Code code k) :
    ∃ vb, evalP σ b = .ok vb ∧ ∀ t Q,
      (∀ s', s'.status = cmpFlags s.regs.rax.toBitVec vb.toBitVec → EPost ctx.nl F t s s' →
        Ev Q s' (at_ (k + code.length))) → Ev Q s (at_ k) := by
  unfold cmpSimple at h
  split at h
  · rename_i o ho
    cases h
    obtain ⟨v, hv, hr⟩ := simpleOp_reads hT hTab hF hI hwf ho
    exact ⟨v, hv, fun t Q hq => ev_cmpO hc.head hr (hq _ rfl (EPost.flags _))⟩
  · obtain ⟨lc, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨v, hv, hlen, hld⟩ := sim_loadInto (r := .rcx) hT hTab hF hI hwf hl hc.left
    refine ⟨v, hv, fun t Q hq => hld Q ?_⟩
    have hcR := hc.right
    rw [hlen] at hcR
    refine ev_cmpRR hcR.head ?_
    refine ev_congr (hq _ rfl ((EPost.regs' (by simp) _).trans (EPost.flags _) (Nat.le_refl _))) ?_
    simp [hlen]

end

section
variable [Host] {G : Layout}

/-- The temporaries `t, …, t + n - 1` fit the frame, or there are none. -/
def TmpFit (nl F t n : Nat) : Prop := n = 0 ∨ nl + t + n ≤ F

omit [Host] in
theorem TmpFit.mono {nl F t n m : Nat} (h : TmpFit nl F t n) (hm : m ≤ n) : TmpFit nl F t m := by
  rcases h with h | h
  · exact .inl (by omega)
  · by_cases m = 0
    · exact .inl ‹_›
    · exact .inr (by omega)

omit [Host] in
theorem TmpFit.le {nl F t n : Nat} (h : TmpFit nl F t n) (hn : 0 < n) : nl + t + n ≤ F := by
  rcases h with h | h <;> omega

omit [Host] in
theorem loadInto_isSome {ctx : Ctx} {r : Reg64} {b : Expr} (h : Expr.isSimple b = true) :
    (loadInto ctx r b).isSome := by
  cases b <;> simp only [Expr.isSimple, reduceCtorEq] at h <;> simp only [loadInto, simpleOp] <;>
    (try split) <;> simp

omit [Host] in
theorem binSimple_none {ctx : Ctx} {op : BinOp} {b : Expr} (h : binSimple ctx op b = none) :
    Expr.isSimple b = false := by
  cases hs : Expr.isSimple b
  · rfl
  have hl := loadInto_isSome (ctx := ctx) (r := .rcx) hs
  unfold binSimple at h
  split at h
  · cases h
  · cases h
  · split at h
    · cases h
    · simp [loadInto] at h
  · split at h
    · cases h
    · cases hl' : loadInto ctx .rcx b <;> simp_all

omit [Host] in
theorem cmpSimple_none {ctx : Ctx} {b : Expr} (h : cmpSimple ctx b = none) :
    Expr.isSimple b = false := by
  cases hs : Expr.isSimple b
  · rfl
  have hl := loadInto_isSome (ctx := ctx) (r := .rcx) hs
  unfold cmpSimple at h
  split at h
  · cases h
  · cases hl' : loadInto ctx .rcx b <;> simp_all

omit [Host] in
theorem tempsE_bin_left (_op : BinOp) (a b : Expr) :
    tempsE a ≤ (if Expr.isSimple b then tempsE a else max (tempsE a) (1 + tempsE b)) := by
  split <;> omega

/-- `a op b` compared in place (`cmpIn`): the flags make `cc` the comparison. -/
theorem sim_cmpIn {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    {F : Nat} (hF : 8 * F + 8 < maxOff) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    {op : Cmp} {a b : Expr} (hwa : Expr.wf ctx.nl G.tab a = true) (hwb : Expr.wf ctx.nl G.tab b = true)
    {cc : CondCode} {d : Directive} (h : cmpIn ctx op a b = some (cc, d)) {k : Nat}
    (hk : Host.prog[k]? = some d) :
    ∃ va vb, evalP σ a = .ok va ∧ evalP σ b = .ok vb ∧ ∀ Q,
      (∀ st, cc.interp st = op.eval va vb → Ev Q { s with status := st } (at_ (k + 1))) →
        Ev Q s (at_ k) := by
  unfold cmpIn at h
  split at h
  next m o hm ho =>
    split at h
    · cases h
      obtain ⟨va, hva, hra⟩ := simpleOp_reads hT hTab hF hI hwa hm
      obtain ⟨vb, hvb, hrb⟩ := simpleOp_reads hT hTab hF hI hwb ho
      exact ⟨va, vb, hva, hvb, fun Q hq => ev_cmpG hk hra hrb (hq _ (cmpCC_interp op va vb))⟩
    · cases h
  next o m _ ho hm =>
    split at h
    · cases h
      obtain ⟨va, hva, hra⟩ := simpleOp_reads hT hTab hF hI hwa ho
      obtain ⟨vb, hvb, hrb⟩ := simpleOp_reads hT hTab hF hI hwb hm
      exact ⟨va, vb, hva, hvb, fun Q hq => ev_cmpG hk hrb hra (hq _ (swapCC_interp op va vb))⟩
    · cases h
  next => cases h


/-! ### Tiered accesses (lane tierarr)

`tierDesc r` turns a tier word in `r` into the address of the tier's descriptor block,
`T + 4096 (u & 1)`: tier `1` of array `a` is array `a + tierOff`, whose descriptor is
`16 · tierOff = 4096` bytes after `a`'s. -/

omit [Host] in
theorem set64_set64 (R : Reg64s) (r : Reg64) (a b : BitVec 64) : (R.set64 r a).set64 r b = R.set64 r b := by
  cases r <;> rfl

omit [Host] in
theorem tier_bit (u : Word) : (u &&& 1).toNat ≤ 1 := by
  rw [UInt64.toNat_and]; exact Nat.le_trans Nat.and_le_right (by decide)

omit [Host] in
/-- The tier's array is below `a + tierOff + 1`. -/
theorem tierA_le (a : ArrId) (u : Word) : tierA a u ≤ a + tierOff := by
  have := tier_bit u; simp only [tierA, tierOff]; lomega

omit [Host] in
/-- The descriptor words of tier `u`'s array, from the tier-0 offsets: `8 (u & 1)` further. -/
theorem tier_off (tab : Tab) {a : ArrId} (ha : a < tab.wK) (u : Word) :
    (tab.len64 (tierA a u)).toNat = (tab.len64 a).toNat + 8 * (u &&& 1).toNat ∧
    (tab.base64 (tierA a u)).toNat = (tab.base64 a).toNat + 8 * (u &&& 1).toNat := by
  have := tier_bit u
  simp only [Tab.len64, Tab.base64, tierA]
  rw [tab.wpos_tier ha _ this]; omega

theorem sim_tierDesc {r : Reg64} {k : Nat} {s : MachineData}
    {Q : MachineState → Prop} (hc : Code (tierDesc r) k) {u : Word} (hu : s.regs.get64 r = u.toBitVec)
    (h : ∀ st, Ev Q { s with regs := s.regs.set64 r (u &&& 1).toBitVec, status := st } (at_ (k + 1))) :
    Ev Q s (at_ k) := by
  simp only [tierDesc] at hc
  refine ev_aluRI (op := .and) (w := 1) rfl hc.head fun st1 => ?_
  have := h st1
  simp only [hu, UInt64.ofBitVec_toBitVec, BinOp.eval] at this ⊢
  exact this

omit [Host] in
theorem loadInto_simple {ctx : Ctx} {r : Reg64} {b : Expr} {c : Program} (h : loadInto ctx r b = some c) :
    Expr.isSimple b = true := by
  cases b <;> simp_all [loadInto, simpleOp, Expr.isSimple]

end

section
variable [Host] {G : Layout} (hG : G.Ok)
include hG

/-- The descriptor block's address does not wrap: the table has `a + tierOff + 1` word arrays. -/
theorem tier_T {a : ArrId} (ha : a + tierOff < G.tab.nw) : G.T + 4096 + 16 + 16 * G.tab.nb < 2 ^ 64 := by
  have := hG.tab_end
  simp only [Layout.tabEnd, tierOff] at *; lomega

/-- From `R` = the tier `u & 1` and `rax` = the index `j`: the bounds check and the load of
`a⟨u⟩.u64[j]`. -/
theorem sim_ld64t_core {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    {F t : Nat} {a : ArrId} (ha : a < G.tab.wK) {σ : St} {s : MachineData}
    (hI : Inv G ctx F σ s) {R : Reg64} (_hRc : R ≠ .rcx) {u j : Word} {k : Nat} {Q : MachineState → Prop}
    (hc : Code [i64 (.cmp (.reg (rr .rax)) (oM (tdesc R (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (tdesc R (ctx.tab.base64 a)), movRM .rax (mbi .rcx .rax .W64)] k)
    (hR : s.regs.get64 R = (u &&& 1).toBitVec) (hrax : s.regs.rax = j)
    (hok : ∀ (h : j.toNat < (σ.mem.arr64 (tierA a u)).size) s',
      s'.regs.rax = (σ.mem.arr64 (tierA a u))[j.toNat] → EPost ctx.nl F t s s' → Ev Q s' (at_ (k + 4)))
    (herr : ∀ s', ¬ j.toNat < (σ.mem.arr64 (tierA a u)).size → EPost ctx.nl F t s s' →
      Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  simp only [maxOff] at hTab
  have ha' := (G.tab.wK_spec ha).2
  have hta : tierA a u < G.tab.nw := Nat.lt_of_le_of_lt (tierA_le a u) ha'
  have hw := G.tab.wpos_lt (Nat.lt_of_le_of_lt (Nat.le_add_right a tierOff) ha')
  have hb := tier_bit u
  have hr15 := hI.r15
  have hoff := tier_off G.tab ha u
  have hD : ∀ d : Int, s.regs.r15.toNat + 8 * (s.regs.get64 R).toNat + d.toNat =
      G.T + 8 * (u &&& 1).toNat + d.toNat := by
    intro d; rw [hR, UInt64.toNat_toBitVec, hr15]
  have hsz := hI.mem.size64 _ hta
  have hend := hG.end64 _ hta
  have hlt : G.s64 (tierA a u) < UInt64.size := by simp [UInt64.size]; omega
  refine ev_cmpRMt hc.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
    (v := UInt64.ofNat (G.s64 (tierA a u))) ?_ ?_
  · rw [hD, show G.T + 8 * (u &&& 1).toNat + (ctx.tab.len64 a).toNat =
      G.T + (G.tab.len64 (tierA a u)).toNat by rw [hT]; omega]
    exact hI.mem.len64 _ hta
  refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · refine herr _ ?_ (EPost.flags _)
    simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true', decide_eq_false_iff_not,
      UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax] at hcc
    rw [hsz]; simpa using hcc
  · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false', decide_eq_true_eq,
      UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax] at hcc
    have hj : j.toNat < (σ.mem.arr64 (tierA a u)).size := by rw [hsz]; simpa using hcc
    refine ev_movRMt hc.tail.tail.head ⟨by simp [Tab.base64]; lomega, by simp [hT, Tab.base64]; lomega⟩
      (v := UInt64.ofNat (G.b64 (tierA a u))) ?_ ?_
    · rw [show ∀ st, ({ s with status := st } : MachineData).regs = s.regs from fun _ => rfl, hD,
        show G.T + 8 * (u &&& 1).toNat + (ctx.tab.base64 a).toNat =
        G.T + (G.tab.base64 (tierA a u)).toNat by rw [hT]; omega]
      exact hI.mem.base64 _ hta
    refine ev_ld64 hc.tail.tail.tail.head (v := (σ.mem.arr64 (tierA a u))[j.toNat]) ?_ ?_
    · simp only [Reg64s.set64_rcx, hrax]
      have := hI.mem.get64 _ hta j.toNat hj
      rw [← this]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [A]
      (try omega)
    refine ev_congr (hok hj _ (by simp) ?_) (by omega)
    exact ((EPost.flags _).trans (EPost.regs' (r := .rcx) (by simp) _) (Nat.le_refl _)).trans
      (EPost.regs' (r := .rax) (by simp) _) (Nat.le_refl _)

/-- From `rdx` = the tier word `u` and `rax` = the index `j`: the tier, the bounds check and the
load of `a⟨u⟩.u64[j]`. -/
theorem sim_ld64t_tail {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    {F t : Nat} {a : ArrId} (ha : a < G.tab.wK) {σ : St} {s : MachineData}
    (hI : Inv G ctx F σ s) {u j : Word} {k : Nat} {Q : MachineState → Prop}
    (hc : Code (tierDesc .rdx ++ [i64 (.cmp (.reg (rr .rax)) (oM (tdesc .rdx (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (tdesc .rdx (ctx.tab.base64 a)), movRM .rax (mbi .rcx .rax .W64)]) k)
    (hrdx : s.regs.get64 .rdx = u.toBitVec) (hrax : s.regs.rax = j)
    (hok : ∀ (h : j.toNat < (σ.mem.arr64 (tierA a u)).size) s',
      s'.regs.rax = (σ.mem.arr64 (tierA a u))[j.toNat] → EPost ctx.nl F t s s' → Ev Q s' (at_ (k + 5)))
    (herr : ∀ s', ¬ j.toNat < (σ.mem.arr64 (tierA a u)).size → EPost ctx.nl F t s s' →
      Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  refine sim_tierDesc (r := .rdx) hc.left hrdx fun st => ?_
  have hE1 : EPost ctx.nl F t s { s with regs := s.regs.set64 .rdx (u &&& 1).toBitVec, status := st } :=
    EPost.regs (by simp) _ _
  refine sim_ld64t_core hG hT hTab ha (hI.ofE hG hE1) (R := .rdx) (by decide) hc.right
    (by rw [rget_set, ite_eq_left rfl]) (by rw [← hrax]; rfl)
    (fun hj s' hv hE => ev_congr (hok hj s' hv (hE1.trans hE (Nat.le_refl _))) (by simp))
    (fun s' hj hE => herr s' hj (hE1.trans hE (Nat.le_refl _)))

theorem sim_expr (ctx : Ctx) (hT : ctx.tab = G.tab) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    (F : Nat) (hF : 8 * F + 8 < maxOff) :
    ∀ (e : Expr) (t k : Nat), Code (compileE ctx e t) k → Expr.wf ctx.nl G.tab e = true →
    TmpFit ctx.nl F t (tempsE e) →
    ∀ (σ : St) (s : MachineData) (Q : MachineState → Prop), Inv G ctx F σ s →
    (∀ v s', evalP σ e = .ok v → s'.regs.rax = v → EPost ctx.nl F t s s' →
      Ev Q s' (at_ (k + (compileE ctx e t).length))) →
    (∀ s', (∃ x, evalP σ e = .error x) → EPost ctx.nl F t s s' → Ev Q s' (label errorL)) →
    Ev Q s (at_ k) := by
  have hF0 := hF
  have hTab0 := hTab
  simp only [maxOff] at hF hTab
  intro e
  induction e with
  | const w =>
    intro t k hc _ _ σ s Q hI hok _
    exact ev_movRI hc.head (hok w _ rfl (by simp) (EPost.regs' (by simp) _))
  | var x =>
    intro t k hc hwf _ σ s Q hI hok _
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    simp only [compileE] at hc hok
    cases hl : ctx.alloc.lookup x with
    | some r =>
      simp only [hl] at hc hok
      refine ev_movRR hc.head (hok _ _ rfl ?_ (EPost.regs' (by simp) _))
      simp [hI.reg x hwf r hl]
    | none =>
      simp only [hl] at hc hok
      have := hI.slot x hwf hl
      refine ev_movRM hc.head ⟨by lomega, by lomega⟩ (v := σ.loc x) ?_
        (hok _ _ rfl (by simp) (EPost.regs' (by simp) _))
      rw [Reg64s.get64_rsp, UInt64.toNat_toBitVec, toNat_eight_mul]; exact hI.frame x hwf hl
  | len8 a =>
    intro t k hc hwf _ σ s Q hI hok _
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    refine ev_movRM hc.head ⟨by simp [Tab.len8]; lomega, by simp [Tab.len8]; lomega⟩
      (v := UInt64.ofNat (G.s8 a)) ?_
      (hok _ _ rfl ?_ (EPost.regs' (by simp) _))
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len8 a hwf
    · simp [Mem.len8, hI.mem.size8 a hwf]
  | len64 a =>
    intro t k hc hwf _ σ s Q hI hok _
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    have hw64 := G.tab.wpos_lt hwf
    refine ev_movRM hc.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
      (v := UInt64.ofNat (G.s64 a)) ?_
      (hok _ _ rfl ?_ (EPost.regs' (by simp) _))
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len64 a hwf
    · simp [Mem.len64, hI.mem.size64 a hwf]
  | glob g =>
    intro t k hc hwf _ σ s Q hI hok _
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    refine ev_movRM hc.head ⟨by simp [Tab.globOff, Tab.globBase]; lomega,
        by simp [hT, Tab.globOff, Tab.globBase]; lomega⟩
      (v := σ.mem.glob g) ?_ (hok _ _ rfl (by simp) (EPost.regs' (by simp) _))
    rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT, Layout.globAddr_toNat]
    exact hI.mem.glob g hwf
  | bin op a b iha ihb =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true] at hwf
    simp only [tempsE] at htmp
    simp only [compileE, List.append_assoc, List.singleton_append] at hc hok
    cases hbs : binSimple ctx op b
    case some code =>
      simp only [hbs] at hc hok
      refine iha t k hc.left hwf.1 (htmp.mono (tempsE_bin_left op a b)) σ s Q hI ?_ ?_
      · intro va s1 hva hrax1 hE1
        have hI1 : Inv G ctx F σ s1 :=
          hI.ofE hG hE1
        obtain ⟨vb, hvb, hsim⟩ := sim_binSimple hT hTab0 hF0 hI1 hwf.2 hbs hc.right
        refine hsim t Q fun s' hr hE' => ?_
        have hev : evalP σ (.bin op a b) = .ok (op.eval va vb) := by simp [evalP, hva, hvb]; rfl
        refine ev_congr (hok _ s' hev (by rw [hr, hrax1]) (hE1.trans hE' (Nat.le_refl _))) ?_
        simp only [List.length_append]; omega
      · intro s1 herra hE1
        refine herr s1 ?_ hE1
        obtain ⟨x, hx⟩ := herra
        exact ⟨x, by simp [evalP, hx]; rfl⟩
    simp only [hbs] at hc hok
    have hc1 := hc.right
    have hsp := hI.hi
    have hhi := hG.hi_le
    simp only [binSimple_none hbs, Bool.false_eq_true, ite_false] at htmp
    replace htmp := htmp.le (by omega)
    refine iha t k hc.left hwf.1 (.inr (by omega)) σ s Q hI ?_ ?_
    · intro va s1 hva hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      have hoff : SmallOff (8 * ((ctx.nl : Int) + (t : Int))) := ⟨by omega, by omega⟩
      refine ev_movMR hc1.head hoff ?_ ?_
      · rw [slot_addr _ (ctx.nl + t) _ (by omega)]; exact hI1.mapped (by omega)
      rw [slot_addr _ (ctx.nl + t) _ (by omega)]
      have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + t) (s := s1)
        (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
      have hI2 := hI.ofE hG hE2
      have hc2 := hc1.tail
      refine ihb (t + 1) _ hc2.left hwf.2 (.inr (by omega)) σ _ Q hI2 ?_ ?_
      · intro vb s3 hvb hrax3 hE3
        have h1rsp := congrArg UInt64.toNat hE1.rsp
        have h2rsp := congrArg UInt64.toNat hE2.rsp
        have h3rsp := congrArg UInt64.toNat hE3.rsp
        have hcR := hc2.right
        refine ev_movRR hcR.head ?_
        refine ev_movRM hcR.tail.head hoff (v := va) ?_ ?_
        · rw [slot_addr _ (ctx.nl + t) _ (by omega)]
          simp only [Reg64s.set64_rcx]
          rw [hE3.rsp, hE3.mem.rdW_eq (by omega) (by omega)]
          simp only [hE1.rsp, rdW_wrW_same, Reg64s.get64_rax, hrax1, UInt64.ofBitVec_toBitVec]
        have hcB := hcR.tail.tail
        have hev : evalP σ (.bin op a b) = .ok (op.eval va vb) := by simp [evalP, hva, hvb]; rfl
        by_cases hop : op = .mulhi
        · subst hop
          simp only [binCode] at hcB hok
          refine ev_mul hcB.head fun st => ?_
          refine ev_movRR hcB.tail.head ?_
          refine ev_congr (hok (BinOp.mulhi.eval va vb) _ hev (by simp [hrax3]) ?_) ?_
          · exact (hE2.trans hE3 (by omega)).of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · have hb : binCode op = [binInstr op] := by cases op <;> simp_all [binCode]
          rw [hb] at hcB hok
          refine ev_bin hop hcB.head fun st => ?_
          refine ev_congr (hok (op.eval va vb) _ hev (by simp [hrax3]) ?_) ?_
          · exact (hE2.trans hE3 (by omega)).of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro s3 herrb hE3
        refine herr s3 ?_ (hE2.trans hE3 (by omega))
        obtain ⟨x, hx⟩ := herrb
        exact ⟨x, by simp [evalP, hva, hx]; rfl⟩
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩
  | cmpw op a b iha ihb =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true] at hwf
    simp only [tempsE] at htmp
    simp only [compileE, List.append_assoc, List.singleton_append] at hc hok
    cases hcr : cmpIn ctx op a b
    case some p =>
      obtain ⟨cc, d⟩ := p
      simp only [hcr] at hc hok
      obtain ⟨va, vb, hva, hvb, hsim⟩ := sim_cmpIn hT hTab0 hF0 hI hwf.1 hwf.2 hcr hc.head
      refine hsim Q fun st hst => ?_
      have hE2 : EPost ctx.nl F t s { s with status := st } := EPost.flags _
      have hcT := hc.tail
      refine ev_movRI hcT.head ?_
      refine ev_movRI hcT.tail.head ?_
      refine ev_cmov hcT.tail.tail.head ?_
      have hev : evalP σ (.cmpw op a b) = .ok (op.evalW va vb) := by simp [evalP, hva, hvb]; rfl
      refine ev_congr (hok (op.evalW va vb) _ hev ?_ ?_) ?_
      · simp only [Reg64s.set64_rax, Reg64s.set64_rdx, hst, UInt64.ofBitVec_toBitVec, Cmp.evalW]
      · exact hE2.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
      · simp
    simp only [hcr] at hc hok
    cases hcs : cmpSimple ctx b
    case some code =>
      simp only [hcs] at hc hok
      refine iha t k hc.left hwf.1 (htmp.mono (tempsE_bin_left .add a b)) σ s Q hI ?_ ?_
      · intro va s1 hva hrax1 hE1
        have hI1 : Inv G ctx F σ s1 :=
          hI.ofE hG hE1
        have hcR := hc.right
        obtain ⟨vb, hvb, hsim⟩ := sim_cmpSimple hT hTab0 hF0 hI1 hwf.2 hcs hcR.left
        refine hsim t Q fun s2 hst hE2 => ?_
        have hcT := hcR.right
        refine ev_movRI hcT.head ?_
        refine ev_movRI hcT.tail.head ?_
        refine ev_cmov hcT.tail.tail.head ?_
        have hev : evalP σ (.cmpw op a b) = .ok (op.evalW va vb) := by simp [evalP, hva, hvb]; rfl
        rw [hrax1] at hst
        refine ev_congr (hok (op.evalW va vb) _ hev ?_ ?_) ?_
        · simp only [Reg64s.set64_rax, Reg64s.set64_rdx, hst, UInt64.ofBitVec_toBitVec, cmpCC_interp, Cmp.evalW]
        · exact (hE1.trans hE2 (Nat.le_refl _)).of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro s1 herra hE1
        refine herr s1 ?_ hE1
        obtain ⟨x, hx⟩ := herra
        exact ⟨x, by simp [evalP, hx]; rfl⟩
    simp only [hcs] at hc hok
    have hc1 := hc.right
    have hsp := hI.hi
    have hhi := hG.hi_le
    simp only [cmpSimple_none hcs, Bool.false_eq_true, ite_false] at htmp
    replace htmp := htmp.le (by omega)
    refine iha t k hc.left hwf.1 (.inr (by omega)) σ s Q hI ?_ ?_
    · intro va s1 hva hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      have hoff : SmallOff (8 * ((ctx.nl : Int) + (t : Int))) := ⟨by omega, by omega⟩
      refine ev_movMR hc1.head hoff ?_ ?_
      · rw [slot_addr _ (ctx.nl + t) _ (by omega)]; exact hI1.mapped (by omega)
      rw [slot_addr _ (ctx.nl + t) _ (by omega)]
      have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + t) (s := s1)
        (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
      have hI2 := hI.ofE hG hE2
      have hc2 := hc1.tail
      refine ihb (t + 1) _ hc2.left hwf.2 (.inr (by omega)) σ _ Q hI2 ?_ ?_
      · intro vb s3 hvb hrax3 hE3
        have h1rsp := congrArg UInt64.toNat hE1.rsp
        have h2rsp := congrArg UInt64.toNat hE2.rsp
        have h3rsp := congrArg UInt64.toNat hE3.rsp
        have hcR := hc2.right
        refine ev_movRR hcR.head ?_
        refine ev_movRM hcR.tail.head hoff (v := va) ?_ ?_
        · rw [slot_addr _ (ctx.nl + t) _ (by omega)]
          simp only [Reg64s.set64_rcx]
          rw [hE3.rsp, hE3.mem.rdW_eq (by omega) (by omega)]
          simp only [hE1.rsp, rdW_wrW_same, Reg64s.get64_rax, hrax1, UInt64.ofBitVec_toBitVec]
        refine ev_cmpRR hcR.tail.tail.head ?_
        refine ev_movRI hcR.tail.tail.tail.head ?_
        refine ev_movRI hcR.tail.tail.tail.tail.head ?_
        refine ev_cmov hcR.tail.tail.tail.tail.tail.head ?_
        have hev : evalP σ (.cmpw op a b) = .ok (op.evalW va vb) := by simp [evalP, hva, hvb]; rfl
        refine ev_congr (hok (op.evalW va vb) _ hev ?_ ?_) ?_
        · simp only [Reg64s.set64_rcx, Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.get64_rax, hrax3, UInt64.ofBitVec_toBitVec, cmpCC_interp, Cmp.evalW]
        · exact (hE2.trans hE3 (by omega)).of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro s3 herrb hE3
        refine herr s3 ?_ (hE2.trans hE3 (by omega))
        obtain ⟨x, hx⟩ := herrb
        exact ⟨x, by simp [evalP, hva, hx]; rfl⟩
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩
  | ldc d i ih =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true] at hwf
    simp only [tempsE] at htmp
    simp only [compileE] at hc hok
    have hcR := hc.right
    have hpre := List.prefix_iff_eq_take.mp (List.isPrefixOf_iff_prefix.mp hwf.1)
    have hdl : d.length ≤ G.tab.rom.length := by
      have := congrArg List.length hpre; simp at this; omega
    have hidx : romIdx d G.tab.rom + d.length ≤ G.tab.rom.length := by
      have h1 := congrArg List.length hpre; have := romIdx_le d G.tab.rom; simp at h1; omega
    have hw : G.tab.rom.length ≤ 8 * G.tab.romWords := G.tab.rom_length_le
    have htabEnd := hG.tab_end
    simp only [Layout.tabEnd] at htabEnd
    refine ih t k hc.left hwf.2 htmp σ s Q hI ?_ ?_
    · intro j s1 hj hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      refine ev_cmpRI hcR.head ?_
      have hdl' : (Int64.ofInt (d.length : Int)).toBitVec.toNat = d.length := by
        simp [Int64.toBitVec_ofInt]; omega
      refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ ⟨.oob, ?_⟩ ((hE1.trans (EPost.flags _) (Nat.le_refl _)))
        simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true', decide_eq_false_iff_not,
          UInt64.toNat_toBitVec, hdl', hrax1] at hcc
        simp only [evalP, hj, bind, Except.bind]
        rw [dite_eq_right (by exact hcc)]
      · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false', decide_eq_true_eq,
          UInt64.toNat_toBitVec, hdl', hrax1] at hcc
        have hoff : SmallOff (G.tab.romBase + (romIdx d G.tab.rom : Int)) := by
          simp only [Tab.romBase]; omega
        rw [hT] at hcR
        refine ev_lea hcR.tail.tail.head hoff ?_
        have hb := hI1.mem.rom (romIdx d G.tab.rom + j.toNat) (by omega)
        have hd : G.tab.rom[romIdx d G.tab.rom + j.toNat]'(by omega) = d[j.toNat] := by
          rw [(List.isPrefixOf_iff_prefix.mp hwf.1).getElem hcc, List.getElem_drop]
        rw [hd] at hb
        refine ev_movzx hcR.tail.tail.tail.head (b := d[j.toNat]) ?_ ?_
        · simp only [Reg64s.set64_rcx, Reg64s.get64_r15, UInt64.toNat_toBitVec, hI1.r15]
          rw [show A (G.T + (G.tab.romBase + (romIdx d G.tab.rom : Int)).toNat) + s1.regs.rax.toBitVec =
              A (G.T + 16 + 16 * (G.tab.nb + G.tab.nw) + (romIdx d G.tab.rom + j.toNat)) from ?_]
          · exact hb
          apply BitVec.eq_of_toNat_eq
          simp only [Tab.romBase, A, BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec, hrax1]
          omega
        refine ev_congr (hok d[j.toNat].toUInt64 _ ?_ (by simp) ?_) ?_
        · simp only [evalP, hj, bind, Except.bind]
          rw [dite_eq_left hcc]
        · exact hE1.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩
  | ld8 a i ih =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [tempsE] at htmp
    simp only [compileE] at hc hok
    have hcR := hc.right
    refine ih t k hc.left hwf.2 htmp σ s Q hI ?_ ?_
    · intro j s1 hj hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      have hsz := hI1.mem.size8 a hwf.1
      have hend := hG.end8 a hwf.1
      refine ev_cmpRM hcR.head ⟨by simp [Tab.len8]; lomega, by simp [Tab.len8]; lomega⟩
        (v := UInt64.ofNat (G.s8 a)) ?_ ?_
      · rw [hI1.r15, hT]; exact hI1.mem.len8 a hwf.1
      refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ ⟨.oob, ?_⟩ ((hE1.trans (EPost.flags _) (Nat.le_refl _)))
        simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true', decide_eq_false_iff_not,
          UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (show G.s8 a < UInt64.size by
            simp [UInt64.size]; omega), hrax1] at hcc
        simp only [evalP, hj, bind, Except.bind]
        rw [dite_eq_right (by rw [hsz]; exact hcc)]
      · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false', decide_eq_true_eq,
          UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' (show G.s8 a < UInt64.size by
            simp [UInt64.size]; omega), hrax1] at hcc
        refine ev_movRM hcR.tail.tail.head ⟨by simp [Tab.base8]; lomega, by simp [Tab.base8]; lomega⟩
          (v := UInt64.ofNat (G.b8 a)) ?_ ?_
        · simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec]
          rw [hI1.r15, hT]; exact hI1.mem.base8 a hwf.1
        refine ev_movzx hcR.tail.tail.tail.head (b := (σ.mem.arr8 a)[j.toNat]'(by omega)) ?_ ?_
        · simp only [Reg64s.set64_rcx, hrax1]
          have := hI1.mem.get8 a hwf.1 j.toNat (by omega)
          rw [← this]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [A]
          (try omega)
        refine ev_congr (hok ((σ.mem.arr8 a)[j.toNat]'(by omega)).toUInt64 _ ?_ (by simp) ?_) ?_
        · simp only [evalP, hj, bind, Except.bind]
          rw [dite_eq_left (by omega)]
        · exact hE1.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩
  | ld64 a i ih =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [tempsE] at htmp
    simp only [compileE] at hc hok
    have hcR := hc.right
    refine ih t k hc.left hwf.2 htmp σ s Q hI ?_ ?_
    · intro j s1 hj hrax1 hE1
      have hI1 : Inv G ctx F σ s1 :=
        hI.ofE hG hE1
      have hsz := hI1.mem.size64 a hwf.1
      have hend := hG.end64 a hwf.1
      have hlt : G.s64 a < UInt64.size := by simp [UInt64.size]; omega
      have hw64 := G.tab.wpos_lt hwf.1
      refine ev_cmpRM hcR.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
        (v := UInt64.ofNat (G.s64 a)) ?_ ?_
      · rw [hI1.r15, hT]; exact hI1.mem.len64 a hwf.1
      refine ev_jcc hcR.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ ⟨.oob, ?_⟩ ((hE1.trans (EPost.flags _) (Nat.le_refl _)))
        simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_true', decide_eq_false_iff_not,
          UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax1] at hcc
        simp only [evalP, hj, bind, Except.bind]
        rw [dite_eq_right (by rw [hsz]; exact hcc)]
      · simp only [CondCode.interp, cmpFlags_cf, Bool.not_eq_false', decide_eq_true_eq,
          UInt64.toNat_toBitVec, UInt64.toNat_ofNat_of_lt' hlt, hrax1] at hcc
        refine ev_movRM hcR.tail.tail.head ⟨by simp [Tab.base64]; lomega, by simp [hT, Tab.base64]; lomega⟩
          (v := UInt64.ofNat (G.b64 a)) ?_ ?_
        · simp only [Reg64s.get64_r15, UInt64.toNat_toBitVec]
          rw [hI1.r15, hT]; exact hI1.mem.base64 a hwf.1
        refine ev_ld64 hcR.tail.tail.tail.head (v := (σ.mem.arr64 a)[j.toNat]'(by omega)) ?_ ?_
        · simp only [Reg64s.set64_rcx, hrax1]
          have := hI1.mem.get64 a hwf.1 j.toNat (by omega)
          rw [← this]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [A]
          (try omega)
        refine ev_congr (hok ((σ.mem.arr64 a)[j.toNat]'(by omega)) _ ?_ (by simp) ?_) ?_
        · simp only [evalP, hj, bind, Except.bind]
          rw [dite_eq_left (by omega)]
        · exact hE1.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩

  | ld64t a tt i iht ihi =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨ha, hwt⟩, hwi⟩ := hwf
    simp only [tempsE] at htmp
    simp only [compileE] at hc hok
    by_cases hTt : ctx.isT tt = true
    · -- the tier local: its tier is in `rsi`
      simp only [hTt, ite_true] at hc hok
      cases tt with
      | var x =>
        have hx : ctx.treg = some x := by simpa [Ctx.isT] using hTt
        have hu : evalP σ (.var x) = .ok (σ.loc x) := rfl
        simp only [Expr.isSimple, ite_true] at htmp
        refine ihi t k hc.left hwi htmp σ s Q hI ?_ ?_
        · intro j s1 hj hrax1 hE1
          have hI1 : Inv G ctx F σ s1 := hI.ofE hG hE1
          refine sim_ld64t_core hG hT hTab0 ha hI1 (R := .rsi) (u := σ.loc x) (j := j) (t := t) (by decide)
            hc.right (by simp [Reg64s.get64, hI1.tr x hx]) hrax1 (fun hjb s' hv hE3 => ?_) (fun s' hjb hE3 => ?_)
          · refine ev_congr (hok _ s' ?_ hv (hE1.trans hE3 (Nat.le_refl _))) ?_
            · simp only [evalP, hj, bind, Except.bind]
              rw [dite_eq_left hjb]
            · simp only [List.length_append, List.length_cons, List.length_nil]; omega
          · refine herr s' ⟨.oob, ?_⟩ (hE1.trans hE3 (Nat.le_refl _))
            simp only [evalP, hj, bind, Except.bind]
            rw [dite_eq_right hjb]
        · intro s1 herri hE1
          refine herr s1 ?_ hE1
          obtain ⟨y, hy⟩ := herri
          exact ⟨y, by simp [evalP, hy]; rfl⟩
      | _ => simp [Ctx.isT] at hTt
    simp only [hTt, Bool.false_eq_true, ite_false] at hc hok
    cases hl : loadInto ctx .rdx tt
    case some ld =>
      simp only [hl, List.append_assoc] at hc hok
      have hs := loadInto_simple hl
      simp only [hs, ite_true] at htmp
      refine ihi t k hc.left hwi htmp σ s Q hI ?_ ?_
      · intro j s1 hj hrax1 hE1
        have hI1 : Inv G ctx F σ s1 := hI.ofE hG hE1
        have hc1 := hc.right
        obtain ⟨u, hu, hlen, hld⟩ := sim_loadInto (r := .rdx) hT hTab hF hI1 hwt hl hc1.left
        refine hld Q ?_
        have hcT := hc1.right
        rw [hlen] at hcT
        have hE2 := hE1.trans (EPost.regs' (s := s1) (r := .rdx) (by simp) u.toBitVec) (Nat.le_refl _)
        refine sim_ld64t_tail hG hT hTab0 ha (u := u) (j := j) (hI.ofE hG hE2) hcT (by rw [rget_set, ite_eq_left rfl]) (by rw [← hrax1]; rfl)
          (t := t) (fun hjb s' hv hE3 => ?_) (fun s' hjb hE3 => ?_)
        · refine ev_congr (hok _ s' ?_ hv (hE2.trans hE3 (Nat.le_refl _))) ?_
          · simp only [evalP, hu, hj, bind, Except.bind]
            rw [dite_eq_left hjb]
          · simp only [List.length_append, List.length_cons, List.length_nil, tierDesc]; omega
        · refine herr s' ⟨.oob, ?_⟩ (hE2.trans hE3 (Nat.le_refl _))
          simp only [evalP, hu, hj, bind, Except.bind]
          rw [dite_eq_right hjb]
      · intro s1 herri hE1
        refine herr s1 ?_ hE1
        obtain ⟨x, hx⟩ := herri
        obtain ⟨u, hu, -, -⟩ := sim_loadInto (r := .rdx) hT hTab hF hI hwt hl hc.right.left
        exact ⟨x, by simp [evalP, hu, hx]; rfl⟩
    simp only [hl, List.append_assoc, List.cons_append, List.nil_append] at hc hok
    have hns : Expr.isSimple tt = false := by
      cases hs : Expr.isSimple tt
      · rfl
      · have := loadInto_isSome (ctx := ctx) (r := .rdx) hs; simp [hl] at this
    simp only [hns, Bool.false_eq_true, ite_false] at htmp
    have hsp := hI.hi
    have hhi := hG.hi_le
    replace htmp := htmp.le (by omega)
    have hc1 := hc.right
    refine iht t k hc.left hwt (.inr (by omega)) σ s Q hI ?_ ?_
    · intro u s1 hu hrax1 hE1
      have hI1 : Inv G ctx F σ s1 := hI.ofE hG hE1
      have hoff : SmallOff (8 * ((ctx.nl : Int) + (t : Int))) := ⟨by omega, by omega⟩
      refine ev_movMR hc1.head hoff ?_ ?_
      · rw [slot_addr _ (ctx.nl + t) _ (by omega)]; exact hI1.mapped (by omega)
      rw [slot_addr _ (ctx.nl + t) _ (by omega)]
      have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + t) (s := s1)
        (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
      have hI2 := hI.ofE hG hE2
      have hc2 := hc1.tail
      refine ihi (t + 1) _ hc2.left hwi (.inr (by omega)) σ _ Q hI2 ?_ ?_
      · intro j s3 hj hrax3 hE3
        have h1rsp := congrArg UInt64.toNat hE1.rsp
        have h2rsp := congrArg UInt64.toNat hE2.rsp
        have h3rsp := congrArg UInt64.toNat hE3.rsp
        have hcR := hc2.right
        refine ev_movRM hcR.head hoff (v := u) ?_ ?_
        · rw [slot_addr _ (ctx.nl + t) _ (by omega)]
          rw [hE3.rsp, hE3.mem.rdW_eq (by omega) (by omega)]
          simp only [hE1.rsp, rdW_wrW_same, Reg64s.get64_rax, hrax1, UInt64.ofBitVec_toBitVec]
        have hE4 := (hE2.trans hE3 (by omega)).trans (EPost.regs' (s := s3) (r := .rdx) (by simp) u.toBitVec) (Nat.le_refl _)
        refine sim_ld64t_tail hG hT hTab0 ha (u := u) (j := j) (hI.ofE hG hE4) hcR.tail (by rw [rget_set, ite_eq_left rfl])
          (by rw [← hrax3]; rfl) (t := t) (fun hjb s' hv hE5 => ?_) (fun s' hjb hE5 => ?_)
        · refine ev_congr (hok _ s' ?_ hv (hE4.trans hE5 (Nat.le_refl _))) ?_
          · simp only [evalP, hu, hj, bind, Except.bind]
            rw [dite_eq_left hjb]
          · simp only [List.length_append, List.length_cons, List.length_nil, tierDesc]; omega
        · refine herr s' ⟨.oob, ?_⟩ (hE4.trans hE5 (Nat.le_refl _))
          simp only [evalP, hu, hj, bind, Except.bind]
          rw [dite_eq_right hjb]
      · intro s3 herri hE3
        refine herr s3 ?_ (hE2.trans hE3 (by omega))
        obtain ⟨x, hx⟩ := herri
        exact ⟨x, by simp [evalP, hu, hx]; rfl⟩
    · intro s1 herrt hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herrt
      exact ⟨x, by simp [evalP, hx]; rfl⟩
  | ld8x8 b i ih =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true] at hwf
    simp only [tempsE] at htmp
    simp only [compileE] at hc hok
    have hcR := hc.right
    refine ih t k hc.left hwf.2 htmp σ s Q hI ?_ ?_
    · intro j s1 hj hrax1 hE1
      have hI1 : Inv G ctx F σ s1 := hI.ofE hG hE1
      have hLlt := src8_size_lt hG hI1.mem hwf.1
      have h8 : (8 : UInt64).toNat = 8 := rfl
      refine sim_srcLen hG hT hTab0 hI1 hwf.1 (r := .rdx) hcR.head ?_
      refine ev_cmpRO (v := 8) hcR.tail.head (.inl rfl) ?_
      refine ev_jcc hcR.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
      · refine herr _ ⟨.oob, ?_⟩ (hE1.trans (EPost.of_eq (EPost.refl _ _ _ _) rfl (by simp) (by simp)
          (by simp) (by simp) (by simp) (by keep_tac)) (Nat.le_refl _))
        simp only [rget_set, ↓reduceIte] at hcc
        rw [interp_c] at hcc
        simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hLlt, h8] at hcc
        simp only [evalP, hj, bind, Except.bind]
        rw [ite_eq_right (by omega)]
      · simp only [rget_set, ↓reduceIte] at hcc
        rw [interp_c] at hcc
        simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hLlt, h8] at hcc
        refine ev_subRI hcR.tail.tail.tail.head fun st => ?_
        simp only [rget_set, ↓reduceIte]
        refine ev_cmpRO (v := UInt64.ofNat (σ.mem.src8 b).size - 8) hcR.tail.tail.tail.tail.head
          (.inr (.inr ⟨.rdx, rfl, by simp⟩)) ?_
        refine ev_jcc hcR.tail.tail.tail.tail.tail.head (fun hcc2 => ?_) (fun hcc2 => ?_)
        · refine herr _ ⟨.oob, ?_⟩ (hE1.trans (EPost.of_eq (EPost.refl _ _ _ _) rfl (by simp) (by simp)
            (by simp) (by simp) (by simp) (by keep_tac)) (Nat.le_refl _))
          simp only [Reg64s.get64_rax, Reg64s.set64_rdx, hrax1] at hcc2
          rw [interp_a] at hcc2
          have hv : (UInt64.ofNat (σ.mem.src8 b).size - 8).toNat = (σ.mem.src8 b).size - 8 := by
            rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hLlt, h8]; omega),
              UInt64.toNat_ofNat_of_lt' hLlt, h8]
          simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hv] at hcc2
          simp only [evalP, hj, bind, Except.bind]
          rw [ite_eq_right (by omega)]
        · simp only [Reg64s.get64_rax, Reg64s.set64_rdx, hrax1] at hcc2
          rw [interp_a] at hcc2
          have hv : (UInt64.ofNat (σ.mem.src8 b).size - 8).toNat = (σ.mem.src8 b).size - 8 := by
            rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hLlt, h8]; omega),
              UInt64.toNat_ofNat_of_lt' hLlt, h8]
          simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, hv, Nat.not_lt] at hcc2
          refine sim_srcBase (σ := σ) (F := F) hG hT hTab0 ?_ hwf.1 hcR.tail.tail.tail.tail.tail.tail.head fun B hB => ?_
          · exact hI1.of_regs rfl (by simp) (by simp) (by alloc_keep) (fun _ => rfl)
          have hbytes : ∀ jj < 8, s1.dmem.get? (A (B + j.toNat + jj)) = some (σ.mem.src8 b)[j.toNat + jj]! :=
            fun jj hjj => by rw [show B + j.toNat + jj = B + (j.toNat + jj) by omega]; exact hB.get _ (by omega)
          refine ev_ld64b hcR.tail.tail.tail.tail.tail.tail.tail.head (v := le64 (σ.mem.src8 b) j.toNat) ?_ ?_
          · simp only [Reg64s.set64_rcx, Reg64s.set64_rdx]
            rw [show (A B) + s1.regs.rax.toBitVec = A (B + j.toNat) by
              apply BitVec.eq_of_toNat_eq; simp [A, BitVec.toNat_add, hrax1]]
            exact rdW_le64 hbytes
          refine ev_congr (hok (le64 (σ.mem.src8 b) j.toNat) _ ?_ (by simp) ?_) ?_
          · simp only [evalP, hj, bind, Except.bind]
            rw [ite_eq_left (by omega)]
          · exact hE1.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro s1 herra hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herra
      exact ⟨x, by simp [evalP, hx]; rfl⟩
  | len64t a tt iht =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨ha, hwt⟩ := hwf
    simp only [tempsE] at htmp
    simp only [compileE, List.append_assoc] at hc hok
    by_cases hTt : ctx.isT tt = true
    · simp only [hTt, ite_true] at hc hok
      cases tt with
      | var x =>
        have hx : ctx.treg = some x := by simpa [Ctx.isT] using hTt
        have ha' := (G.tab.wK_spec ha).2
        have hta : tierA a (σ.loc x) < G.tab.nw := Nat.lt_of_le_of_lt (tierA_le a _) ha'
        have hw := G.tab.wpos_lt (Nat.lt_of_le_of_lt (Nat.le_add_right a tierOff) ha')
        have hb := tier_bit (σ.loc x)
        have hr15 := hI.r15
        have hoff := tier_off G.tab ha (σ.loc x)
        refine ev_movRMt hc.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
          (v := UInt64.ofNat (G.s64 (tierA a (σ.loc x)))) ?_ ?_
        · rw [show s.regs.get64 .rsi = (σ.loc x &&& 1).toBitVec by simp [Reg64s.get64, hI.tr x hx],
            UInt64.toNat_toBitVec, hr15,
            show G.T + 8 * (σ.loc x &&& 1).toNat + (ctx.tab.len64 a).toNat =
            G.T + (G.tab.len64 (tierA a (σ.loc x))).toNat by rw [hT]; omega]
          exact hI.mem.len64 _ hta
        refine ev_congr (hok (UInt64.ofNat (G.s64 (tierA a (σ.loc x)))) _ ?_ (by simp) (EPost.regs' (by simp) _)) ?_
        · simp only [evalP, Mem.len64, hI.mem.size64 _ hta, bind, Except.bind]
        · simp
      | _ => simp [Ctx.isT] at hTt
    simp only [hTt, Bool.false_eq_true, ite_false] at hc hok
    refine iht t k hc.left hwt htmp σ s Q hI ?_ ?_
    · intro u s1 hu hrax1 hE1
      have hI1 : Inv G ctx F σ s1 := hI.ofE hG hE1
      have hc1 := hc.right
      have ha' := (G.tab.wK_spec ha).2
      have hta : tierA a u < G.tab.nw := Nat.lt_of_le_of_lt (tierA_le a u) ha'
      have hw := G.tab.wpos_lt (Nat.lt_of_le_of_lt (Nat.le_add_right a tierOff) ha')
      have hb := tier_bit u
      have hr15 := hI1.r15
      have hoff := tier_off G.tab ha u
      refine sim_tierDesc (r := .rax) hc1.left (u := u) (by simp [hrax1]) fun st => ?_
      have hcR := hc1.right
      refine ev_movRMt hcR.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
        (v := UInt64.ofNat (G.s64 (tierA a u))) ?_ ?_
      · simp only [rget_set, ↓reduceIte, UInt64.toNat_toBitVec]
        rw [show (s1.regs.set64 .rax (u &&& 1).toBitVec).r15 = s1.regs.r15 from rfl, hr15,
          show G.T + 8 * (u &&& 1).toNat + (ctx.tab.len64 a).toNat =
          G.T + (G.tab.len64 (tierA a u)).toNat by rw [hT]; omega]
        exact hI1.mem.len64 _ hta
      refine ev_congr (hok (UInt64.ofNat (G.s64 (tierA a u))) _ ?_ (by simp) ?_) ?_
      · simp only [evalP, hu, Mem.len64, hI1.mem.size64 _ hta, bind, Except.bind]
      · exact hE1.trans ((EPost.regs (by simp) _ _).trans (EPost.regs' (by simp) _) (Nat.le_refl _))
          (Nat.le_refl _)
      · simp only [List.length_append, List.length_cons, List.length_nil, tierDesc]; omega
    · intro s1 herrt hE1
      refine herr s1 ?_ hE1
      obtain ⟨x, hx⟩ := herrt
      exact ⟨x, by simp [evalP, hx]; rfl⟩
end

/-! ## Conditions -/

/-- `evalC`, without the state. -/
def evalCP (σ : St) : Cond → Except Err Bool
  | .cmp c a b => do
    let x ← evalP σ a
    let y ← evalP σ b
    return c.eval x y
  | .and p q => do if (← evalCP σ p) then evalCP σ q else return false
  | .or p q => do if (← evalCP σ p) then return true else evalCP σ q
  | .not p => do return !(← evalCP σ p)

theorem evalC_run (σ : St) (c : Cond) : (evalC c).run σ = (evalCP σ c).map (·, σ) := by
  induction c with
  | cmp op a b =>
    simp only [evalC, evalCP, StateT.run_bind, evalE_run]
    cases evalP σ a <;> simp [Except.map, bind, Except.bind]
    · cases evalP σ b <;> rfl
  | and p q ihp ihq =>
    simp only [evalC, evalCP, StateT.run_bind, ihp]
    cases evalCP σ p with
    | error => rfl
    | ok b => cases b <;> simp [Except.map, bind, Except.bind, ihq] <;> rfl
  | or p q ihp ihq =>
    simp only [evalC, evalCP, StateT.run_bind, ihp]
    cases evalCP σ p with
    | error => rfl
    | ok b => cases b <;> simp [Except.map, bind, Except.bind, ihq] <;> rfl
  | not p ih =>
    simp only [evalC, evalCP, StateT.run_bind, ih]
    cases evalCP σ p <;> rfl


end L.Compiler
