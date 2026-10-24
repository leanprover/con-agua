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

/-- From `rax = L`: `n ≤ L` and `o ≤ L - n`, else `ca_error`. -/
theorem sim_lenChk {ctx : Ctx} {o n : Expr} {k : Nat} (hc : Code (lenChk ctx o n) k) {s : MachineData}
    {L vo vn : Word} {Q : MachineState → Prop} (hrax : s.regs.get64 .rax = L.toBitVec)
    (hro : ∀ s', s'.dmem = s.dmem → KeepR s' s → OpReads s' (opnd ctx o) vo)
    (hrn : ∀ s', s'.dmem = s.dmem → KeepR s' s → OpReads s' (opnd ctx n) vn)
    (herr : ∀ s', s'.dmem = s.dmem → KeepR s' s → ¬ vo.toNat + vn.toNat ≤ L.toNat → Ev Q s' (label errorL))
    (hok : ∀ s', s'.dmem = s.dmem → KeepR s' s → vo.toNat + vn.toNat ≤ L.toNat → Ev Q s' (at_ (k + 5))) :
    Ev Q s (at_ k) := by
  simp only [lenChk] at hc
  have hrax' : s.regs.rax = L := by
    apply UInt64.toBitVec_inj.mp; simpa using hrax
  refine ev_cmpRO (v := vn) hc.head (hrn _ rfl (KeepR.refl s)) ?_
  rw [hrax]
  refine ev_jcc hc.tail.head (fun hcc => ?_) (fun hcc => ?_)
  · rw [interp_c] at hcc
    refine herr _ rfl ((KeepR.refl s).ofEq (by keep_tac)) ?_
    simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt] at hcc; omega
  rw [interp_c] at hcc
  have h1 : vn.toNat ≤ L.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hcc
  refine ev_binO (op := .sub) rfl hc.tail.tail.head (hrn _ rfl ((KeepR.refl s).ofEq (by keep_tac))) fun st => ?_
  simp only [hrax, hrax', UInt64.ofBitVec_toBitVec, BinOp.eval]
  refine ev_cmpRO (v := vo) hc.tail.tail.tail.head (hro _ rfl ((KeepR.refl s).ofEq (by keep_tac))) ?_
  simp only [rget_set, ↓reduceIte]
  refine ev_jcc hc.tail.tail.tail.tail.head (fun hcc2 => ?_) (fun hcc2 => ?_)
  · rw [interp_c] at hcc2
    refine herr _ rfl ((KeepR.refl s).ofEq (by keep_tac)) ?_
    simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr h1)] at hcc2
    omega
  · rw [interp_c] at hcc2
    simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr h1)] at hcc2
    exact ev_congr (hok _ rfl ((KeepR.refl s).ofEq (by keep_tac)) (by omega)) (by omega)

/-- Where a block operand's descriptor block is: `R`. -/
structure DescAt (G : Layout) (ctx : Ctx) (D : DataMem) (R : Nat) (wa aw : ArrId) : Prop where
  arr : aw < G.tab.nw
  len : rdW D (A (R + (ctx.tab.len64 wa).toNat)) = some (UInt64.ofNat (G.s64 aw))
  base : rdW D (A (R + (ctx.tab.base64 wa).toNat)) = some (UInt64.ofNat (G.b64 aw))
  offl : SmallOff (ctx.tab.len64 wa)
  offb : SmallOff (ctx.tab.base64 wa)
  rlt : R < 2 ^ 64

/-- The descriptor block of a block operand: none for a plain array (`r15`), `tierDesc` into `r`
for a tiered one. -/
theorem sim_warrDesc {ctx : Ctx} (hT : ctx.tab = G.tab) {F : Nat} (hF : 8 * F + 8 < maxOff) {σ : St}
    {s : MachineData} (hI : Inv G ctx F σ s) {w : WArr} (hw : WArr.wf ctx.nl G.tab w = true) {r : Reg64}
    (hr : r = .rcx ∨ r = .rdx) {k : Nat} (hc : Code (warrDesc ctx r w).1 k) {aw : ArrId}
    (hwp : warrP σ w = .ok aw) {Q : MachineState → Prop}
    (h : ∀ s' (R : Nat), s'.dmem = s.dmem → KeepR s' s → s'.regs.get64 (warrDesc ctx r w).2 = A R →
      DescAt G ctx s.dmem R w.arr aw → Ev Q s' (at_ (k + (warrDesc ctx r w).1.length))) :
    Ev Q s (at_ k) := by
  have hTab' := hTab; simp only [maxOff] at hTab'
  have hTE := hG.tab_end
  simp only [Layout.tabEnd] at hTE
  cases w with
  | plain a =>
    simp only [WArr.wf, decide_eq_true_eq] at hw
    simp only [warrP, Except.ok.injEq] at hwp
    subst hwp
    simp only [warrDesc, List.length_nil, Nat.add_zero] at h ⊢
    refine h s G.T rfl (KeepR.refl s) ?_ ⟨hw, ?_, ?_, ?_, ?_, by omega⟩
    · apply BitVec.eq_of_toNat_eq; simp [A, hI.r15]; omega
    · simpa [WArr.arr, hT] using hI.mem.len64 a hw
    · simpa [WArr.arr, hT] using hI.mem.base64 a hw
    · rw [hT]; simp [Tab.len64, WArr.arr]; lomega
    · rw [hT]; simp [Tab.base64, WArr.arr]; lomega
  | tier a t =>
    simp only [WArr.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨ha, hto⟩, hwt⟩ := hw
    obtain ⟨u, hu⟩ := opnd_ok (σ := σ) (nl := ctx.nl) (G := G) (e := t) (by simp [Expr.opndWf, hto, hwt])
    simp only [warrP, hu, Except.map, Except.ok.injEq] at hwp
    subst hwp
    simp only [warrDesc] at hc h ⊢
    refine ev_movRO hc.head (opnd_reads hG hTab hT hF hI (by simp [Expr.opndWf, hto, hwt]) hu) ?_
    refine sim_tierDesc (r := r) (u := u) (by rcases hr with rfl | rfl <;> simp) hc.tail (by simp [rget_set]) fun st => ?_
    have hta : tierA a u < G.tab.nw := Nat.lt_of_le_of_lt (tierA_le a u) ha
    have hTT := tier_T hG ha
    have hb := tier_bit u
    have hoff := tier_off G.tab a u
    refine ev_congr (h _ (G.T + 4096 * (u &&& 1).toNat) rfl ((KeepR.refl s).ofEq ?_) ?_
      ⟨hta, ?_, ?_, ?_, ?_, by omega⟩) ?_
    · rcases hr with rfl | rfl <;> keep_tac
    · simp only [rget_set, ↓reduceIte]
      rw [show (s.regs.set64 r u.toBitVec).r15 = s.regs.r15 by rcases hr with rfl | rfl <;> rfl]
      apply BitVec.eq_of_toNat_eq; simp [A, hI.r15]
    · simp only [WArr.arr]
      rw [hT, show G.T + 4096 * (u &&& 1).toNat + (G.tab.len64 a).toNat = G.T + (G.tab.len64 (tierA a u)).toNat by
        omega]
      exact hI.mem.len64 _ hta
    · simp only [WArr.arr]
      rw [hT, show G.T + 4096 * (u &&& 1).toNat + (G.tab.base64 a).toNat = G.T + (G.tab.base64 (tierA a u)).toNat by
        omega]
      exact hI.mem.base64 _ hta
    · rw [hT]; simp [Tab.len64, WArr.arr]; lomega
    · rw [hT]; simp [Tab.base64, WArr.arr]; lomega
    · simp [tierDesc]

/-- `r := base + 8 o` for the block operand whose descriptor block is at `R`. -/
theorem sim_wordPtr {ctx : Ctx} {r R : Reg64} (hr : r = .rcx ∨ r = .rdx) (hR : R ≠ .rax) {a aw : ArrId}
    {o : Expr} {k : Nat} (hc : Code (wordPtr ctx r R a o) k) {s : MachineData} {RV : Nat} {D : DataMem}
    {Q : MachineState → Prop} {vo : Word} (hd : s.dmem = D) (hRV : s.regs.get64 R = A RV)
    (hdesc : DescAt G ctx D RV a aw) (hvo : vo.toNat ≤ G.s64 aw)
    (hro : ∀ s', s'.dmem = D → KeepR s' s → OpReads s' (opnd ctx o) vo)
    (h : ∀ s', s'.dmem = D → KeepR s' s → s'.regs.get64 r = A (G.b64 aw + 8 * vo.toNat) →
      Ev Q s' (at_ (k + 5))) :
    Ev Q s (at_ k) := by
  simp only [wordPtr] at hc
  have hend := hG.end64 aw hdesc.arr
  have hRlt := hdesc.rlt
  refine ev_movRM hc.head hdesc.offb (v := UInt64.ofNat (G.b64 aw)) ?_ ?_
  · rw [hRV, hd]
    simpa [A, Nat.mod_eq_of_lt hRlt] using hdesc.base
  refine ev_movRO hc.tail.head (hro _ hd ((KeepR.refl s).ofEq (by rcases hr with rfl | rfl <;> keep_tac))) ?_
  refine ev_shlRI (n := 3) (by decide) hc.tail.tail.head fun st => ?_
  refine ev_binO (op := .add) rfl hc.tail.tail.tail.head (v := UInt64.ofNat (G.b64 aw))
    (.inr (.inr ⟨r, rfl, by rcases hr with rfl | rfl <;> simp [rget_set]⟩)) fun st2 => ?_
  refine ev_movRR hc.tail.tail.tail.tail.head ?_
  refine h _ hd ((KeepR.refl s).ofEq (by rcases hr with rfl | rfl <;> keep_tac)) ?_
  rcases hr with rfl | rfl <;>
  · simp only [rget_set, ↓reduceIte, reduceCtorEq, UInt64.ofBitVec_toBitVec, BinOp.eval]
    apply BitVec.eq_of_toNat_eq
    simp [UInt64.toNat_add, UInt64.toNat_shiftLeft, A, Nat.shiftLeft_eq]
    congr 1; omega

omit hG hTab in
theorem arr64_size_set64 (m : Mem) (a : ArrId) (i v : Word) (b : ArrId) :
    ((m.set64 a i v).arr64 b).size = (m.arr64 b).size := by
  simp only [Mem.set64, Mem.arr64]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases hb : a = b
  · subst hb
    by_cases ha : a < m.words.size <;> simp [ha]
  · simp [hb]

/-- An 8-byte stack cell survives a store into a word array. -/
theorem rdW_slot_store64 {d : DataMem} {X : Nat} (hX1 : G.lo ≤ X) (hX2 : X + 8 ≤ G.hi) {a : ArrId}
    (ha : a < G.tab.nw) {j : Nat} (hj : j < G.s64 a) (v : BitVec 64) :
    rdW (wrW d (A (G.b64 a + 8 * j)) v) (A X) = rdW d (A X) := by
  have hend := hG.end64 a ha
  have := hG.hi_le
  rw [rdW_wrW_A (by omega) (by omega) ?_]
  exact cell_disj (P := G.In64 a) (Q := G.InStack) (fun k hk => ⟨by omega, by omega⟩)
    (fun k hk => ⟨by omega, by omega⟩) fun t h1 h2 => hG.stack_arr t h2 (Or.inr ⟨a, ha, h1⟩)

/-- **The copy loop of `copy64`**: from `rcx` = word `u` of `sa`, `rdx` = word `w` of `da`, the end
of the source in the stack cell `[rsp + eoff]`; `n > 0` words left. It leaves at `X` with the
memory of `m.copy64 da w sa u n`. -/
theorem copy64_loop {ctx : Ctx} {F : Nat} {Lb : Label} {eoff : Int} {kL : Nat} {Q : MachineState → Prop}
    (hcode : Code (copy64Loop Lb (mb .rsp eoff)) kL) (hL : label Lb = at_ kL)
    {da sa : ArrId} (hda : da < G.tab.nw) (hsa : sa < G.tab.nw) (hEoff : SmallOff eoff)
    {σ : St} {s0 : MachineData} {top : Nat}
    (hX1 : G.lo ≤ s0.regs.rsp.toNat + eoff.toNat) (hX2 : s0.regs.rsp.toNat + eoff.toNat + 8 ≤ G.hi) :
    ∀ n (m : Mem) (w u : Word) (s : MachineData), Inv G ctx F { σ with mem := m } s → KeepR s s0 →
      s.regs.get64 .rcx = A (G.b64 sa + 8 * u.toNat) → s.regs.get64 .rdx = A (G.b64 da + 8 * w.toNat) →
      rdW s.dmem (A (s0.regs.rsp.toNat + eoff.toNat)) = some (UInt64.ofNat (G.b64 sa + 8 * (u.toNat + n))) →
      0 < n → w.toNat + n ≤ (m.arr64 da).size → u.toNat + n ≤ (m.arr64 sa).size →
      (∀ s', Inv G ctx F { σ with mem := m.copy64 da w sa u n } s' → KeepR s' s0 →
        Pres G top s.dmem s'.dmem → Ev Q s' (at_ (kL + 7))) →
      Ev Q s (at_ kL) := by
  simp only [copy64Loop] at hcode
  have hends := hG.end64 sa hsa
  have hendd := hG.end64 da hda
  intro n
  induction n with
  | zero => intro m w u s _ _ _ _ _ h0; omega
  | succ n ih =>
    intro m w u s hI hK hrcx hrdx hE _ hwd hus hexit
    have hszd := hI.mem.size64 da hda
    have hszs := hI.mem.size64 sa hsa
    simp only at hszd hszs
    have hrsp := hK.rsp
    refine ev_label hcode.head ?_
    -- the source word
    have hut : u.toNat < (m.arr64 sa).size := by omega
    have hwt : w.toNat < (m.arr64 da).size := by omega
    refine ev_movRM hcode.tail.head ⟨Int.le_refl _, by decide⟩ (v := (m.arr64 sa)[u.toNat]!) ?_ ?_
    · rw [hrcx]
      have := hI.mem.get64 sa hsa u.toNat hut
      simp only [getElem!_pos (m.arr64 sa) u.toNat hut]
      simpa [A, Nat.mod_eq_of_lt (show G.b64 sa + 8 * u.toNat < 2 ^ 64 by omega)] using this
    -- the store into the destination
    refine ev_movMR hcode.tail.tail.head ⟨Int.le_refl _, by decide⟩ ?_ ?_
    · simp only [rget_set, reduceCtorEq, ↓reduceIte, hrdx]
      have := hI.mem.get64 da hda w.toNat hwt
      simp [A, Nat.mod_eq_of_lt (show G.b64 da + 8 * w.toNat < 2 ^ 64 by omega), this]
    simp only [rget_set, reduceCtorEq, ↓reduceIte, hrdx]
    rw [show A ((A (G.b64 da + 8 * w.toNat)).toNat + (0 : Int).toNat) = A (G.b64 da + 8 * w.toNat) by
      simp [A, Nat.mod_eq_of_lt (show G.b64 da + 8 * w.toNat < 2 ^ 64 by omega)]]
    have hIs := (hI.keepR (s := { s with regs := s.regs.set64 .rax ((m.arr64 sa)[u.toNat]!).toBitVec })
      rfl ((KeepR.refl s).ofEq (by keep_tac))).store64 hG hda hwt ((m.arr64 sa)[u.toNat]!)
    simp only at hIs
    refine ev_addRI hcode.tail.tail.tail.head fun st1 => ?_
    refine ev_addRI hcode.tail.tail.tail.tail.head fun st2 => ?_
    have hu1 : (u + 1).toNat = u.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hw1 : (w + 1).toNat = w.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hE' := hE
    rw [← rdW_slot_store64 hG hTab hX1 hX2 hda (j := w.toNat) (by omega) ((m.arr64 sa)[u.toNat]!).toBitVec] at hE'
    refine ev_cmpRO (r := .rcx) (v := UInt64.ofNat (G.b64 sa + 8 * (u.toNat + (n + 1)))) hcode.tail.tail.tail.tail.tail.head
      (.inr (.inl ⟨.rsp, eoff, rfl, hEoff, by simpa [hrsp] using hE'⟩)) ?_
    have hrc : (A (G.b64 sa + 8 * u.toNat) + (Int64.ofInt 8).toBitVec) =
        (UInt64.ofNat (G.b64 sa + 8 * (u.toNat + 1))).toBitVec := by
      apply BitVec.eq_of_toNat_eq
      simp [A, BitVec.toNat_add, eight_toBitVec]; omega
    simp only [rget_set, reduceCtorEq, ↓reduceIte, hrcx, hrc]
    refine ev_jcc hcode.tail.tail.tail.tail.tail.tail.head (fun hcc => ?_) (fun hcc => ?_)
    · rw [interp_c] at hcc
      simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
        UInt64.toNat_ofNat_of_lt' (show G.b64 sa + 8 * (u.toNat + 1) < 2 ^ 64 by omega),
        UInt64.toNat_ofNat_of_lt' (show G.b64 sa + 8 * (u.toNat + (n + 1)) < 2 ^ 64 by omega)] at hcc
      rw [hL]
      have hdw : G.b64 da + 8 * (w.toNat + 1) < 2 ^ 64 := by omega
      have hrd : A (G.b64 da + 8 * w.toNat) + (Int64.ofInt 8).toBitVec = A (G.b64 da + 8 * (w.toNat + 1)) := by
        apply BitVec.eq_of_toNat_eq
        simp [A, BitVec.toNat_add, eight_toBitVec]; omega
      refine ih (m.set64 da w ((m.arr64 sa)[u.toNat]!)) (w + 1) (u + 1) _
        (hIs.keepR rfl ((KeepR.refl _).ofEq (by keep_tac))) (by exact hK.ofEq (by keep_tac))
        (by simp only [rget_set, reduceCtorEq, ↓reduceIte, hu1]; apply BitVec.eq_of_toNat_eq; simp [A])
        (by simp only [rget_set, ↓reduceIte, hw1, hrdx, hrd])
        (by rw [hu1]; simpa [Nat.add_assoc, Nat.add_comm 1 n] using hE') (by omega)
        (by rw [arr64_size_set64]; omega) (by rw [arr64_size_set64]; omega) ?_
      intro s' hI' hK' hP
      refine hexit s' (by rw [Mem.copy64_succ]; exact hI') hK' ((Pres.store64 hG hda (j := w.toNat) (by omega) _).trans hP)
    · rw [interp_c] at hcc
      simp only [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt,
        UInt64.toNat_ofNat_of_lt' (show G.b64 sa + 8 * (u.toNat + 1) < 2 ^ 64 by omega),
        UInt64.toNat_ofNat_of_lt' (show G.b64 sa + 8 * (u.toNat + (n + 1)) < 2 ^ 64 by omega)] at hcc
      have hn0 : n = 0 := by omega
      subst hn0
      refine ev_congr (hexit _ (hIs.keepR rfl ((KeepR.refl _).ofEq (by keep_tac))) (by exact hK.ofEq (by keep_tac))
        (Pres.store64 hG hda (j := w.toNat) (by omega) _)) (by omega)

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
