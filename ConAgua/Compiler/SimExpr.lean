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
      · simp [hj, StateT.pure]; rfl
      · simp [hj]; rfl


theorem romIdx_le (d rom : List UInt8) : romIdx d rom ≤ rom.length := by
  induction rom with
  | nil => simp [romIdx]
  | cons b rom ih => simp only [romIdx]; split <;> simp; omega

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
  hI.only hG (hE.mem.mono (by omega) (Nat.le_refl _)) hE.rsp hE.r15 fun r hr =>
    hE.keep r (allocRegs_ne hr).1 (allocRegs_ne hr).2.1 (allocRegs_ne hr).2.2.1

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
      .inr (.inl ⟨_, _, rfl, ⟨by simp [Tab.len8]; lomega, by simp [hT, Tab.len8]; lomega⟩, ?_⟩)⟩
    rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len8 a hwf
  | len64 a =>
    simp only [simpleOp, Option.some.injEq] at h; subst h
    simp only [Expr.wf, decide_eq_true_eq] at hwf
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
theorem tempsE_bin_left (op : BinOp) (a b : Expr) :
    tempsE a ≤ (if Expr.isSimple b then tempsE a else max (tempsE a) (1 + tempsE b)) := by
  split <;> omega

/-- `cmp r, b` for a local in register `r` (`cmpReg`). -/
theorem sim_cmpReg {ctx : Ctx} (hT : ctx.tab = G.tab)
    (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    {F : Nat} (hF : 8 * F + 8 < maxOff) {σ : St} {s : MachineData} (hI : Inv G ctx F σ s)
    {a b : Expr} (hwa : Expr.wf ctx.nl G.tab a = true) (hwb : Expr.wf ctx.nl G.tab b = true)
    {code : Program} {k : Nat} (h : cmpReg ctx a b = some code) (hc : Code code k) :
    ∃ va vb, evalP σ a = .ok va ∧ evalP σ b = .ok vb ∧ code.length = 1 ∧ ∀ t Q,
      (∀ s', s'.status = cmpFlags va.toBitVec vb.toBitVec → EPost ctx.nl F t s s' →
        Ev Q s' (at_ (k + 1))) → Ev Q s (at_ k) := by
  unfold cmpReg at h
  split at h
  · rename_i x
    split at h
    · rename_i r o hr ho
      cases h
      simp only [Expr.wf, decide_eq_true_eq] at hwa
      obtain ⟨vb, hvb, hrd⟩ := simpleOp_reads hT hTab hF hI hwb ho
      refine ⟨σ.loc x, vb, rfl, hvb, rfl, fun t Q hq => ev_cmpRO hc.head hrd ?_⟩
      rw [hI.reg x hwa r hr]
      exact hq _ rfl (EPost.flags _)
    · cases h
  · cases h

/-- The simulation of one expression, as `sim_expr` states it (its induction hypotheses). -/
def SimE (G : Layout) (ctx : Ctx) (F : Nat) (e : Expr) : Prop :=
  ∀ (t k : Nat), Code (compileE ctx e t) k → Expr.wf ctx.nl G.tab e = true →
    TmpFit ctx.nl F t (tempsE e) →
    ∀ (σ : St) (s : MachineData) (Q : MachineState → Prop), Inv G ctx F σ s →
    (∀ v s', evalP σ e = .ok v → s'.regs.rax = v → EPost ctx.nl F t s s' →
      Ev Q s' (at_ (k + (compileE ctx e t).length))) →
    (∀ s', (∃ x, evalP σ e = .error x) → EPost ctx.nl F t s s' → Ev Q s' (label errorL)) →
    Ev Q s (at_ k)

end

section
variable [Host] {G : Layout} (hG : G.Ok)
include hG

/-- Two operands through the temporary `t`: `a` into `rax`, spilled; `b` into `rax`, moved to
`r`; `a` reloaded into `rax`. -/
theorem sim_pair {ctx : Ctx} {F : Nat} (hF : 8 * F + 8 < maxOff) {a b : Expr}
    (iha : SimE G ctx F a) (ihb : SimE G ctx F b) {r : Reg64} (hr : r = .rcx ∨ r = .rdx)
    {t k : Nat} {rest : Program}
    (hc : Code (compileE ctx a t ++ movMR (ctx.tmp t) .rax ::
      (compileE ctx b (t + 1) ++ movRR r .rax :: movRM .rax (ctx.tmp t) :: rest)) k)
    (hwa : Expr.wf ctx.nl G.tab a = true) (hwb : Expr.wf ctx.nl G.tab b = true)
    (htmp : ctx.nl + t + max (tempsE a) (1 + tempsE b) ≤ F)
    {σ : St} {s : MachineData} {Q : MachineState → Prop} (hI : Inv G ctx F σ s)
    (hok : ∀ va vb s3, evalP σ a = .ok va → evalP σ b = .ok vb → s3.regs.rax = vb →
      EPost ctx.nl F t s s3 →
      Code rest (k + (compileE ctx a t).length + 1 + (compileE ctx b (t + 1)).length + 1 + 1) →
      Ev Q { s3 with regs := (s3.regs.set64 r (s3.regs.get64 .rax)).set64 .rax va.toBitVec }
        (at_ (k + (compileE ctx a t).length + 1 + (compileE ctx b (t + 1)).length + 1 + 1)))
    (herra : ∀ s' x, evalP σ a = .error x → EPost ctx.nl F t s s' → Ev Q s' (label errorL))
    (herrb : ∀ s' va x, evalP σ a = .ok va → evalP σ b = .error x → EPost ctx.nl F t s s' →
      Ev Q s' (label errorL)) :
    Ev Q s (at_ k) := by
  have hF' := hF; simp only [maxOff] at hF'
  have hsp := hI.hi
  have hhi := hG.hi_le
  refine iha t k hc.left hwa (.inr (by omega)) σ s Q hI ?_ fun s1 ⟨x, hx⟩ hE1 => herra s1 x hx hE1
  intro va s1 hva hrax1 hE1
  have hI1 := hI.ofE hG hE1
  have hoff : SmallOff (8 * ((ctx.nl : Int) + (t : Int))) := ⟨by omega, by omega⟩
  have hc1 := hc.right
  refine ev_movMR hc1.head hoff ?_ ?_
  · rw [slot_addr _ (ctx.nl + t) _ (by omega)]; exact hI1.mapped (by omega)
  rw [slot_addr _ (ctx.nl + t) _ (by omega)]
  have hE2 := hE1.trans (EPost.store (v := s1.regs.get64 .rax) (j := ctx.nl + t) (s := s1)
    (by omega) (by omega) (by rw [hE1.rsp]; omega)) (Nat.le_refl _)
  have hc2 := hc1.tail
  refine ihb (t + 1) _ hc2.left hwb (.inr (by omega)) σ _ Q (hI.ofE hG hE2) ?_
    fun s3 ⟨x, hx⟩ hE3 => herrb s3 va x hva hx (hE2.trans hE3 (by omega))
  intro vb s3 hvb hrax3 hE3
  have h1rsp := congrArg UInt64.toNat hE1.rsp
  have h2rsp := congrArg UInt64.toNat hE2.rsp
  have h3rsp := congrArg UInt64.toNat hE3.rsp
  have hcR := hc2.right
  refine ev_movRR hcR.head (ev_movRM hcR.tail.head hoff (v := va) ?_
    (hok va vb s3 hva hvb hrax3 (hE2.trans hE3 (by omega)) hcR.tail.tail))
  rw [slot_addr _ (ctx.nl + t) _ (by omega)]
  rcases hr with rfl | rfl <;> simp only [Reg64s.set64_rcx, Reg64s.set64_rdx] <;>
    rw [hE3.rsp, hE3.mem.rdW_eq (by omega) (by omega)] <;>
    simp only [hE1.rsp, rdW_wrW_same, Reg64s.get64_rax, hrax1, UInt64.ofBitVec_toBitVec]

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
    exact fun t k hc _ _ σ s Q hI hok _ => ev_movRI hc.head (hok w _ rfl (by simp) (EPost.regs' (by simp) _))
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
    refine ev_movRM hc.head ⟨by simp [Tab.len8]; lomega, by simp [hT, Tab.len8]; lomega⟩
      (v := UInt64.ofNat (G.s8 a)) ?_
      (hok _ _ rfl ?_ (EPost.regs' (by simp) _))
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len8 a hwf
    · simp [evalP, Mem.len8, hI.mem.size8 a hwf]
  | len64 a =>
    intro t k hc hwf _ σ s Q hI hok _
    simp only [Expr.wf, decide_eq_true_eq] at hwf
    refine ev_movRM hc.head ⟨by simp [Tab.len64]; lomega, by simp [hT, Tab.len64]; lomega⟩
      (v := UInt64.ofNat (G.s64 a)) ?_
      (hok _ _ rfl ?_ (EPost.regs' (by simp) _))
    · rw [Reg64s.get64_r15, UInt64.toNat_toBitVec, hI.r15, hT]; exact hI.mem.len64 a hwf
    · simp [evalP, Mem.len64, hI.mem.size64 a hwf]
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
      · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalP, hx]; rfl⟩ hE1
    simp only [hbs] at hc hok
    simp only [binSimple_none hbs, Bool.false_eq_true, ite_false] at htmp
    refine sim_pair hG hF0 iha ihb (.inl rfl) hc hwf.1 hwf.2 (htmp.le (by omega)) hI
      (fun va vb s3 hva hvb hrax3 hE13 hcB => ?_) (fun s1 x hx hE1 => herr s1 ⟨x, by simp [evalP, hx]; rfl⟩ hE1)
      fun s3 va x hva hx hE => herr s3 ⟨x, by simp [evalP, hva, hx]; rfl⟩ hE
    have hev : evalP σ (.bin op a b) = .ok (op.eval va vb) := by simp [evalP, hva, hvb]; rfl
    by_cases hop : op = .mulhi
    · subst hop
      simp only [binCode] at hcB hok
      refine ev_mul hcB.head fun st => ?_
      refine ev_movRR hcB.tail.head ?_
      refine ev_congr (hok (BinOp.mulhi.eval va vb) _ hev (by simp [hrax3]) ?_) ?_
      · exact hE13.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · have hb : binCode op = [binInstr op] := by cases op <;> simp_all [binCode]
      rw [hb] at hcB hok
      refine ev_bin hop hcB.head fun st => ?_
      refine ev_congr (hok (op.eval va vb) _ hev (by simp [hrax3]) ?_) ?_
      · exact hE13.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  | cmpw op a b iha ihb =>
    intro t k hc hwf htmp σ s Q hI hok herr
    simp only [Expr.wf, Bool.and_eq_true] at hwf
    simp only [tempsE] at htmp
    simp only [compileE, List.append_assoc, List.singleton_append] at hc hok
    cases hcr : cmpReg ctx a b
    case some code =>
      simp only [hcr] at hc hok
      obtain ⟨va, vb, hva, hvb, hlen, hsim⟩ := sim_cmpReg hT hTab0 hF0 hI hwf.1 hwf.2 hcr hc.left
      refine hsim t Q fun s2 hst hE2 => ?_
      have hcT := hc.right
      rw [hlen] at hcT
      refine ev_movRI hcT.head ?_
      refine ev_movRI hcT.tail.head ?_
      refine ev_cmov hcT.tail.tail.head ?_
      have hev : evalP σ (.cmpw op a b) = .ok (op.evalW va vb) := by simp [evalP, hva, hvb]; rfl
      refine ev_congr (hok (op.evalW va vb) _ hev ?_ ?_) ?_
      · simp only [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.get64_rax, hst,
          UInt64.toBitVec_ofBitVec, UInt64.ofBitVec_toBitVec, cmpCC_interp, Cmp.evalW]
      · exact hE2.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
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
        · simp only [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.get64_rax, hst,
            UInt64.toBitVec_ofBitVec, UInt64.ofBitVec_toBitVec, cmpCC_interp, Cmp.evalW]
        · exact (hE1.trans hE2 (Nat.le_refl _)).of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalP, hx]; rfl⟩ hE1
    simp only [hcs] at hc hok
    simp only [cmpSimple_none hcs, Bool.false_eq_true, ite_false] at htmp
    refine sim_pair hG hF0 iha ihb (.inl rfl) hc hwf.1 hwf.2 (htmp.le (by omega)) hI
      (fun va vb s3 hva hvb hrax3 hE13 hcB => ?_) (fun s1 x hx hE1 => herr s1 ⟨x, by simp [evalP, hx]; rfl⟩ hE1)
      fun s3 va x hva hx hE => herr s3 ⟨x, by simp [evalP, hva, hx]; rfl⟩ hE
    refine ev_cmpRR hcB.head ?_
    refine ev_movRI hcB.tail.head ?_
    refine ev_movRI hcB.tail.tail.head ?_
    refine ev_cmov hcB.tail.tail.tail.head ?_
    have hev : evalP σ (.cmpw op a b) = .ok (op.evalW va vb) := by simp [evalP, hva, hvb]; rfl
    refine ev_congr (hok (op.evalW va vb) _ hev ?_ ?_) ?_
    · simp only [Reg64s.set64_rcx, Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.get64_rax, hrax3,
        UInt64.toBitVec_ofBitVec, UInt64.ofBitVec_toBitVec, cmpCC_interp, Cmp.evalW]
    · exact hE13.of_eq rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
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
    · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalP, hx]; rfl⟩ hE1
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
      refine ev_cmpRM hcR.head ⟨by simp [Tab.len8]; lomega, by simp [hT, Tab.len8]; lomega⟩
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
        refine ev_movRM hcR.tail.tail.head ⟨by simp [Tab.base8]; lomega, by simp [hT, Tab.base8]; lomega⟩
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
    · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalP, hx]; rfl⟩ hE1
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
    · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalP, hx]; rfl⟩ hE1

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

section
variable [Host] {G : Layout} (hG : G.Ok)
include hG

theorem sim_cond (ctx : Ctx) (hT : ctx.tab = G.tab) (hTab : 16 + 16 * (G.tab.nb + G.tab.nw) + 8 * G.tab.romWords + 8 * G.tab.nxres + 8 * G.tab.ng < maxOff)
    (F : Nat) (hF : 8 * F + 8 < maxOff) :
    ∀ (c : Cond) (path : Path) (pol : Bool) (l : Label) (t k : Nat),
    Code (compileC ctx path c pol l t) k → Cond.wf ctx.nl G.tab c = true →
    TmpFit ctx.nl F t (tempsC c) →
    ∀ (σ : St) (s : MachineData) (Q : MachineState → Prop), Inv G ctx F σ s →
    (∀ s', evalCP σ c = .ok pol → EPost ctx.nl F t s s' → Ev Q s' (label l)) →
    (∀ s', evalCP σ c = .ok (!pol) → EPost ctx.nl F t s s' →
      Ev Q s' (at_ (k + (compileC ctx path c pol l t).length))) →
    (∀ s', (∃ x, evalCP σ c = .error x) → EPost ctx.nl F t s s' → Ev Q s' (label errorL)) →
    Ev Q s (at_ k) := by
  intro c
  induction c with
  | cmp op a b =>
    intro path pol l t k hc hwf htmp σ s Q hI hjmp hfall herr
    have hF' := hF
    simp only [maxOff] at hF'
    simp only [Cond.wf, Bool.and_eq_true] at hwf
    simp only [tempsC] at htmp
    simp only [compileC, List.append_assoc, List.singleton_append] at hc hfall
    cases hcr : cmpReg ctx a b
    case some code =>
      simp only [hcr] at hc hfall
      obtain ⟨va, vb, hva, hvb, hlen, hsim⟩ := sim_cmpReg hT hTab hF hI hwf.1 hwf.2 hcr hc.left
      refine hsim t Q fun s2 hst hE2 => ?_
      have hcR := hc.right
      rw [hlen] at hcR
      have hev : evalCP σ (.cmp op a b) = .ok (op.eval va vb) := by simp [evalCP, hva, hvb]; rfl
      refine ev_jcc hcR.head (fun hcc => ?_) (fun hcc => ?_)
      · rw [hst] at hcc
        have : op.eval va vb = pol := by
          cases pol <;> simp_all [neg_interp, cmpCC_interp]
        exact hjmp _ (hev.trans (by rw [this])) hE2
      · rw [hst] at hcc
        have : op.eval va vb = !pol := by
          cases pol <;> simp_all [neg_interp, cmpCC_interp]
        refine ev_congr (hfall _ (hev.trans (by rw [this])) hE2) ?_
        simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    simp only [hcr] at hc hfall
    cases hcs : cmpSimple ctx b
    case some code =>
      simp only [hcs] at hc hfall
      refine sim_expr hG ctx hT hTab F hF a t k hc.left hwf.1 (htmp.mono (tempsE_bin_left .add a b)) σ s Q hI ?_ ?_
      · intro va s1 hva hrax1 hE1
        have hI1 : Inv G ctx F σ s1 :=
          hI.ofE hG hE1
        have hcR := hc.right
        obtain ⟨vb, hvb, hsim⟩ := sim_cmpSimple hT hTab hF hI1 hwf.2 hcs hcR.left
        refine hsim t Q fun s2 hst hE2 => ?_
        have hE4 := hE1.trans hE2 (Nat.le_refl _)
        have hev : evalCP σ (.cmp op a b) = .ok (op.eval va vb) := by simp [evalCP, hva, hvb]; rfl
        rw [hrax1] at hst
        refine ev_jcc hcR.right.head (fun hcc => ?_) (fun hcc => ?_)
        · rw [hst] at hcc
          have : op.eval va vb = pol := by
            cases pol <;> simp_all [neg_interp, cmpCC_interp]
          exact hjmp _ (hev.trans (by rw [this])) hE4
        · rw [hst] at hcc
          have : op.eval va vb = !pol := by
            cases pol <;> simp_all [neg_interp, cmpCC_interp]
          refine ev_congr (hfall _ (hev.trans (by rw [this])) hE4) ?_
          simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalCP, hx]; rfl⟩ hE1
    simp only [hcs] at hc hfall
    simp only [cmpSimple_none hcs, Bool.false_eq_true, ite_false] at htmp
    refine sim_pair hG hF (sim_expr hG ctx hT hTab F hF a) (sim_expr hG ctx hT hTab F hF b) (.inl rfl) hc
      hwf.1 hwf.2 (htmp.le (by omega)) hI (fun va vb s3 hva hvb hrax3 hE13 hcB => ?_)
      (fun s1 x hx hE1 => herr s1 ⟨x, by simp [evalCP, hx]; rfl⟩ hE1)
      fun s3 va x hva hx hE => herr s3 ⟨x, by simp [evalCP, hva, hx]; rfl⟩ hE
    refine ev_cmpRR hcB.head ?_
    have hE4 : EPost ctx.nl F t s _ := hE13.of_eq (s'' := { s3 with
      regs := (s3.regs.set64 .rcx (s3.regs.get64 .rax)).set64 .rax va.toBitVec,
      status := cmpFlags va.toBitVec vb.toBitVec }) rfl (by simp) (by simp) (by simp) (by simp) (by simp) (by keep_tac)
    have hev : evalCP σ (.cmp op a b) = .ok (op.eval va vb) := by simp [evalCP, hva, hvb]; rfl
    refine ev_jcc hcB.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · simp only [Reg64s.set64_rcx, Reg64s.set64_rax, Reg64s.get64_rax, hrax3, UInt64.toBitVec_ofBitVec,
        UInt64.ofBitVec_toBitVec] at hcc hE4 ⊢
      have : op.eval va vb = pol := by
        cases pol <;> simp_all [neg_interp, cmpCC_interp]
      exact hjmp _ (hev.trans (by rw [this])) hE4
    · simp only [Reg64s.set64_rcx, Reg64s.set64_rax, Reg64s.get64_rax, hrax3, UInt64.toBitVec_ofBitVec,
        UInt64.ofBitVec_toBitVec] at hcc hE4 ⊢
      have : op.eval va vb = !pol := by
        cases pol <;> simp_all [neg_interp, cmpCC_interp]
      refine ev_congr (hfall _ (hev.trans (by rw [this])) hE4) ?_
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
  | and p q ihp ihq | or p q ihp ihq =>
    intro path pol l t k hc hwf htmp σ s Q hI hjmp hfall herr
    simp only [Cond.wf, Bool.and_eq_true] at hwf
    simp only [tempsC] at htmp
    -- `and` with `false` and `or` with `true` jump straight to `l`; the other two through a label
    cases pol <;> first
    | (simp only [compileC] at hc hfall
       refine ihp _ _ l t k hc.left hwf.1 (htmp.mono (by omega)) σ s Q hI ?_ ?_ ?_
       · intro s1 hp hE1; exact hjmp s1 (by simp [evalCP, hp]; rfl) hE1
       · intro s1 hp hE1
         have hI1 := hI.ofE hG hE1
         refine ihq _ _ l t _ hc.right hwf.2 (htmp.mono (by omega)) σ s1 Q hI1 ?_ ?_ ?_
         · intro s2 hq hE2; exact hjmp s2 (by simp [evalCP, hp, hq]; rfl) (hE1.trans hE2 (Nat.le_refl _))
         · intro s2 hq hE2
           refine ev_congr (hfall s2 (by simp [evalCP, hp, hq]; rfl) (hE1.trans hE2 (Nat.le_refl _))) ?_
           simp only [List.length_append]; omega
         · exact fun s2 ⟨x, hx⟩ hE2 => herr s2 ⟨x, by simp [evalCP, hp, hx]; rfl⟩ (hE1.trans hE2 (Nat.le_refl _))
       · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalCP, hx]; rfl⟩ hE1)
    | (simp only [compileC, List.append_assoc] at hc hfall
       have hS := hc.right.right
       have hlS := Code.label (i := 0) hS rfl
       refine ihp _ _ _ t k hc.left hwf.1 (htmp.mono (by omega)) σ s Q hI ?_ ?_ ?_
       · intro s1 hp hE1
         rw [hlS]
         refine ev_label hS.head ?_
         refine ev_congr (hfall s1 (by simp [evalCP, hp]; rfl) hE1) ?_
         simp only [List.length_append, List.length_cons, List.length_nil]; omega
       · intro s1 hp hE1
         have hI1 := hI.ofE hG hE1
         refine ihq _ _ l t _ hc.right.left hwf.2 (htmp.mono (by omega)) σ s1 Q hI1 ?_ ?_ ?_
         · intro s2 hq hE2; exact hjmp s2 (by simp [evalCP, hp, hq]; rfl) (hE1.trans hE2 (Nat.le_refl _))
         · intro s2 hq hE2
           refine ev_label hS.head ?_
           refine ev_congr (hfall s2 (by simp [evalCP, hp, hq]; rfl) (hE1.trans hE2 (Nat.le_refl _))) ?_
           simp only [List.length_append, List.length_cons, List.length_nil]; omega
         · exact fun s2 ⟨x, hx⟩ hE2 => herr s2 ⟨x, by simp [evalCP, hp, hx]; rfl⟩ (hE1.trans hE2 (Nat.le_refl _))
       · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalCP, hx]; rfl⟩ hE1)
  | not p ih =>
    intro path pol l t k hc hwf htmp σ s Q hI hjmp hfall herr
    simp only [Cond.wf] at hwf
    simp only [tempsC] at htmp
    simp only [compileC] at hc hfall
    refine ih _ (!pol) l t k hc hwf htmp σ s Q hI ?_ ?_ ?_
    · intro s1 hp hE1; exact hjmp s1 (by rw [evalCP, hp]; cases pol <;> rfl) hE1
    · intro s1 hp hE1; exact hfall s1 (by rw [evalCP, hp]; cases pol <;> rfl) hE1
    · exact fun s1 ⟨x, hx⟩ hE1 => herr s1 ⟨x, by simp [evalCP, hx]; rfl⟩ hE1

end

end L.Compiler
