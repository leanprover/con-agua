module

public import ConAguaX86.AsmEsc.Chain2
public import ConAguaX86.AsmEsc.LitHashL
import Kraken.X64.Registers

@[expose] public section

/-!
# Hand-written `lit_hash` and its simulation contract

`litHashAsm tab` is a hand-written body for `lit_hash(o, l)` (`L.Arena.litHash`, the FNV-1a hash of
a literal's limbs). `l = 0` returns the offset basis at once. Otherwise, up front: the window inside
its tier and below `2^40`, and fuel for the loop, else `ca_exhausted`. The loop is 5 instructions
per limb: `xor` from memory, `imul`, the pointer step, `dec`, `jnz`. `litHashAsm_sim` proves the
per-function contract (`FnSimAt`) against `litHash_run` (`LitHashL.lean`).

Registers: `rdi o`, `r8 l` on entry; `rax` the hash; in the loop `rdi` the address of the next limb,
`r8` the limbs left, `rsi` the FNV prime.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- A local label of the hand-written `lit_hash`. -/
abbrev lhL (m : String) : Label := ".Lasm_lit_hash_" ++ m

/-- The hand-written `lit_hash`, for the table `tab` (the descriptor offsets of `POOL` = 0). -/
def litHashAsm (tab : Tab) : Program :=
  [ .label (fnL "lit_hash"),                                           -- 0
    movRI .rax fnvBasis,                                               -- 1  h
    i64 (.cmp (.reg (rr .r8)) (.imm (.int64 (0 : Word).toInt64))),     -- 2
    jccL .z (lhL "Z"),                                                 -- 3  l = 0
    movRI .rdx idxMask,                                                -- 4
    movRR .rcx .rdi,                                                   -- 5
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 6
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 7  tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rdx)),                             -- 8  x
    movRR .r11 .rdx,                                                   -- 9
    i64 (.sub (.reg (rr .r11)) (oR .rdi)),                             -- 10
    i64 (.cmp (.reg (rr .r11)) (oR .r8)),                              -- 11
    jccL .c exhaustedL,                                                -- 12 x + l ≥ 2^40
    movRM .rdx (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 13
    i64 (.sub (.reg (rr .rdx)) (oR .rdi)),                             -- 14
    jccL .c exhaustedL,                                                -- 15
    i64 (.cmp (.reg (rr .rdx)) (oR .r8)),                              -- 16
    jccL .c exhaustedL,                                                -- 17 len - x < l
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 18
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 19 rdi := &A[x]
    i64 (.sub (.reg (rr .r14)) (oR .r8)),                              -- 20
    jccL .c exhaustedL,                                                -- 21 fuel < l
    movRI .rsi fnvPrime,                                               -- 22
    .label (lhL "L"),                                                  -- 23
    i64 (.xor (.reg (rr .rax)) (oM (mb .rdi 0))),                      -- 24 h ^= A[x + i]
    i64 (.imul none (.reg (rr .rax)) (oR .rsi)),                       -- 25 h *= prime
    i64 (.add (.reg (rr .rdi)) (oI 8)),                                -- 26
    i64 (.dec (.reg (rr .r8))),                                        -- 27
    jccL .nz (lhL "L"),                                                -- 28
    .label (lhL "Z"),                                                  -- 29
    i64 .ret ]                                                         -- 30

section
variable [Host] {kf : Nat} {tab : Tab}

theorem lh_code (hc : Code (litHashAsm tab) kf) {i : Nat} {x : Directive}
    (hi : (litHashAsm tab)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

theorem lh_rdi_step (B j : Nat) (h : B + 8 * (j + 1) < 2 ^ 64) :
    ({ toBitVec := (UInt64.ofNat (B + 8 * j)).toBitVec + (Int64.ofInt 8).toBitVec } : UInt64) =
      UInt64.ofNat (B + 8 * (j + 1)) := by
  apply UInt64.toNat_inj.mp
  show ((UInt64.ofNat (B + 8 * j)).toBitVec + (Int64.ofInt 8).toBitVec).toNat = _
  rw [BitVec.toNat_add, UInt64.toNat_toBitVec, L.toNat_ofNat_of_lt (by omega),
    L.toNat_ofNat_of_lt (by omega), show (Int64.ofInt 8).toBitVec.toNat = 8 from rfl]
  omega

theorem lh_r8_step (w : Word) (r : Nat) (h : w.toNat = r + 1) :
    ({ toBitVec := w.toBitVec - 1 } : UInt64).toNat = r := by
  show (w.toBitVec - 1).toNat = r
  have h' : w.toBitVec.toNat = r + 1 := h
  rw [BitVec.toNat_sub, h', show (1 : BitVec 64).toNat = 1 from rfl]
  omega

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} (hc : Code (litHashAsm G.tab) kf)
  {d : MachineData} {Q : MachineState → Prop}
include hG hc

/-- One step of the loop (`.L`): the next step (`hnext`, while limbs are left) or `.Z` (`hlast`). -/
theorem lh_step (TR : TieredArray) (hTR : G.tab.dom64 TR = true) (M : Mem) (R14 : UInt64)
    (s : MachineData) (j r : Nat) (hF : MrFr G d s) (hm : MemRel G M s.dmem)
    (hj : j < (M.arr64 TR).size)
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * j))
    (hr8 : s.regs.r8.toNat = r + 1) (hrsi : s.regs.rsi = fnvPrime) (hr14 : s.regs.r14 = R14)
    (hnext : r ≠ 0 → ∀ s', MrFr G d s' → MemRel G M s'.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * (j + 1)) → s'.regs.r8.toNat = r →
      s'.regs.rsi = fnvPrime → s'.regs.r14 = R14 →
      s'.regs.rax = (s.regs.rax ^^^ (M.arr64 TR)[j]!) * fnvPrime → Ev Q s' (at_ (kf + 23)))
    (hlast : r = 0 → ∀ s', MrFr G d s' → MemRel G M s'.dmem →
      s'.regs.rax = (s.regs.rax ^^^ (M.arr64 TR)[j]!) * fnvPrime → Ev Q s' (at_ (kf + 29))) :
    Ev Q s (at_ (kf + 23)) := by
  have hpA := G.tab.pos64_lt hTR
  have heA := hG.end64 _ hpA
  have hszA := hm.size64 TR hTR
  have hrd : rdW s.dmem (A ((s.regs.get64 .rdi).toNat + (0 : Int).toNat)) = some (M.arr64 TR)[j] := by
    have := hm.get64 TR hTR j hj
    rs [hrdi]
    rw [UInt64.toNat_toBitVec, L.toNat_ofNat_of_lt (by omega)]
    exact this
  refine ev_label (lh_code hc (i := 23) rfl) ?_
  refine ev_aluOp (op := .xor) (v := (M.arr64 TR)[j]) rfl (lh_code hc (i := 24) rfl)
    (Or.inr (Or.inl ⟨.rdi, 0, rfl, by decide, hrd⟩)) fun st1 => ?_
  refine ev_aluOp (op := .mul) (v := fnvPrime) rfl (lh_code hc (i := 25) rfl)
    (Or.inr (Or.inr ⟨.rsi, rfl, by rs [hrsi]⟩)) fun st2 => ?_
  refine ev_addRI (lh_code hc (i := 26) rfl) fun st3 => ?_
  refine ev_decR (lh_code hc (i := 27) rfl) fun st4 _ hzf => ?_
  have hstep : (M.arr64 TR)[j]! = (M.arr64 TR)[j] := getElem!_pos (M.arr64 TR) j hj
  refine ev_jcc (lh_code hc (i := 28) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, Bool.not_eq_eq_eq_not, Bool.not_true] at hcc
    rw [hcc] at hzf
    rs [hr8] at hzf
    have hr0 : r ≠ 0 := by
      intro h0; subst h0
      have e : s.regs.r8 = 1 := UInt64.toNat_inj.mp (by rw [hr8]; rfl)
      rw [e] at hzf; exact absurd hzf (by decide)
    refine ev_lbl (Code.label hc (i := 23) rfl) ?_
    refine hnext hr0 _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hrsi, hr14, BinOp.eval, hstep]
    · rw [← hr14]; exact hF.r14
    · exact hF.pres
    · exact hm
    · exact lh_rdi_step _ _ (by omega)
    · exact lh_r8_step _ _ hr8
  · simp only [CondCode.interp, Bool.not_eq_eq_eq_not, Bool.not_false] at hcc
    rw [hcc] at hzf
    rs [hr8] at hzf
    have hr0 : r = 0 := by
      have e := of_decide_eq_true hzf.symm
      have := lh_r8_step _ r hr8
      rw [show ({ toBitVec := s.regs.r8.toBitVec - 1 } : UInt64) = 0 from UInt64.toBitVec_inj.mp e] at this
      simp at this; omega
    refine hlast hr0 _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
    all_goals try rs [hF.rsp, hF.rbp, hF.r15, hrdi, hrsi, hr14, BinOp.eval, hstep]
    · rw [← hr14]; exact hF.r14
    · exact hF.pres
    · exact hm

/-- The loop from `.L` with `r + 1` limbs to go, by induction on `r`; after the last, `.Z`. -/
theorem lh_loop (TR : TieredArray) (hTR : G.tab.dom64 TR = true) (M : Mem) (rb : Word) (H : Word)
    (R14 : UInt64) (hT : ∀ s', MrFr G d s' → MemRel G M s'.dmem → s'.regs.rax = H →
      Ev Q s' (at_ (kf + 29))) :
    ∀ (r i : Nat) (s : MachineData), MrFr G d s → MemRel G M s.dmem →
      rb.toNat + i + r + 1 ≤ (M.arr64 TR).size →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TR) + 8 * (rb.toNat + i)) →
      s.regs.r8.toNat = r + 1 → s.regs.rsi = fnvPrime → s.regs.r14 = R14 →
      H = lhRows (M.arr64 TR) (rb + UInt64.ofNat i) s.regs.rax (r + 1) →
      Ev Q s (at_ (kf + 23)) := by
  have hpA := G.tab.pos64_lt hTR
  have heA := hG.end64 _ hpA
  intro r
  induction r with
  | zero =>
    intro i s hF hm hb hrdi hr8 hrsi hr14 hH
    have hszA := hm.size64 TR hTR
    have hy : (rb + UInt64.ofNat i).toNat = rb.toNat + i := by
      rw [UInt64.toNat_add, L.toNat_ofNat_of_lt (by omega)]; omega
    refine lh_step hG hc TR hTR M R14 s (rb.toNat + i) 0 hF hm (by omega) hrdi hr8 hrsi hr14
      (fun h => absurd rfl h) fun _ s' hF' hm' hrax => hT s' hF' hm' ?_
    rw [hrax, hH, lhRows, lhRows, hy]
  | succ r ih =>
    intro i s hF hm hb hrdi hr8 hrsi hr14 hH
    have hszA := hm.size64 TR hTR
    have hy : (rb + UInt64.ofNat i).toNat = rb.toNat + i := by
      rw [UInt64.toNat_add, L.toNat_ofNat_of_lt (by omega)]; omega
    refine lh_step hG hc TR hTR M R14 s (rb.toNat + i) (r + 1) hF hm (by omega) hrdi hr8 hrsi hr14
      (fun _ s' hF' hm' hrdi' hr8' hrsi' hr14' hrax => ?_) (fun h => absurd h (by omega))
    refine ih (i + 1) s' hF' hm' (by omega) (by rw [hrdi']; congr 2) hr8' hrsi' hr14' ?_
    rw [hrax, hH, lhRows, hy, UInt64.add_assoc, UInt64.ofNat_add, UInt64.ofNat_one]

/-- `.Z`: the return. -/
theorem lh_tail {ra : Word} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra) (hlo : G.lo ≤ d.regs.rsp.toNat)
    (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (s : MachineData) (M : Mem) (c : Word) (hF : MrFr G d s)
    (hm : MemRel G M s.dmem) (hrax : s.regs.rax = c)
    (hok : ∀ s', MemRel G M s'.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = c → Pres G d.regs.rsp.toNat d.dmem s'.dmem → Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + 29)) := by
  refine ev_label (lh_code hc (i := 29) rfl) ?_
  refine frame_ret hG hra hlo hhi hF (lh_code hc (i := 30) rfl) fun s' e1 e2 e3 e4 e5 e6 => ?_
  exact hok s' (by rw [e1]; exact hm) e2 e3 e4 (by rw [e5]; exact hF.r14) (by rw [e6]; exact hrax)
    (by rw [e1]; exact hF.pres)

end

theorem litHash_nret : Stmt.nret litHash.body = 1 := by
  rw [litHash_body]; rfl

/-- **The hand-written `lit_hash` meets the compiler's per-function contract**, for any table in
which `POOL` (0) is a tiered word array with small descriptor offsets, at every fuel. -/
theorem litHashAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok)
    (hp : p.lookup "lit_hash" = some litHash) (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (litHashAsm G.tab) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n "lit_hash" litHash kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [litHash_nparams] at hlen
  obtain ⟨o, l, rfl⟩ : ∃ o l, vs = [o, l] := by
    match vs, hlen with
    | [o, l], _ => exact ⟨o, l, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = o := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = l := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hh := hG.hi_le
  have hfin : ∀ c : Word, (invoke p (exec p n) "lit_hash" [o, l]).run σ = .ok ([c], σ) →
      ∀ s, MrFr G d s → MemRel G σ.mem s.dmem → s.regs.rax = c → Ev Q s (at_ (kf + 29)) := by
    intro c hrun s hF hm hcx
    refine lh_tail hG hc hra hlo hhi s σ.mem c hF hm hcx fun s' e1 e2 e3 e4 e5 e6 e7 => ?_
    refine hok _ _ s' hrun e1 rfl e2 e3 e4 e5 ?_ e7
    rw [litHash_nret]; exact resOut_zero' e6
  refine ev_label (lh_code hc (i := 0) rfl) ?_
  refine ev_movRI (lh_code hc (i := 1) rfl) ?_
  refine ev_cmpRO (lh_code hc (i := 2) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (lh_code hc (i := 3) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcc
    rs [hr8] at hcc
    have hl0 : l = 0 := UInt64.toBitVec_inj.mp hcc
    subst hl0
    have hrun := litHash_run p hp σ o 0 n (by simp; omega) (Or.inl rfl)
    simp only [UInt64.toNat_zero, lhRows] at hrun
    refine ev_lbl (Code.label hc (i := 29) rfl) ?_
    refine hfin fnvBasis hrun _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
    all_goals try rs
    · exact Nat.le_refl _
    · exact Pres.refl _ _
    · exact hmem
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcc
  rs [hr8] at hcc
  have hnz : l ≠ 0 := fun h => hcc (by rw [h])
  refine ev_movRI (lh_code hc (i := 4) rfl) ?_
  refine ev_movRR (lh_code hc (i := 5) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (lh_code hc (i := 6) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (lh_code hc (i := 7) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (lh_code hc (i := 8) rfl)
    (Or.inr (Or.inr ⟨.rdx, rfl, by rs⟩)) fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (o >>> 40) &&& 1 ∧ s1.regs.rdi = o &&& idxMask ∧
      s1.regs.rdx = idxMask ∧ s1.regs.r8 = l ∧ s1.regs.rax = fnvBasis ∧
      s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g5, g6, g7, g9, g10, g11, g12, g13⟩ => ?_
  have hTR := G.tab.dom64_tierA hdom (o >>> 40)
  have heA := hG.end64 _ (G.tab.pos64_lt hTR)
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdA := pool_desc hm1 hdom (o >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hszA := hmem.size64 _ hTR
  generalize hSA : G.s (G.tab.pos64 (tierA 0 (o >>> 40))) = SA at *
  generalize hBA : G.b (G.tab.pos64 (tierA 0 (o >>> 40))) = BA at *
  have hSAn : (UInt64.ofNat SA).toNat = SA := L.toNat_ofNat_of_lt (by omega)
  have hsub : ∀ (S : Nat) (w : Word), S < 2 ^ 64 → w.toNat ≤ S →
      ((UInt64.ofNat S).toBitVec - w.toBitVec).toNat = S - w.toNat := by
    intro S w h1 h2
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat S).toBitVec.toNat = S from
      L.toNat_ofNat_of_lt h1]
    have := w.toNat_lt; omega
  have hrb : (o &&& idxMask).toNat < 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hmask : (idxMask : Word).toNat = 2 ^ 40 - 1 := rfl
  have hX : ∀ s', s'.regs.rbp = d.regs.rbp → s'.dmem = s1.dmem → Ev Q s' (label exhaustedL) :=
    fun s' e1 e2 => hexh _ ⟨e1, by rw [e2, g13]; exact Pres.refl _ _⟩
  -- the indices stay below `2^40`
  refine ev_movRR (lh_code hc (i := 9) rfl) ?_
  refine ev_subRR (lh_code hc (i := 10) rfl) fun _ _ => ?_
  refine ev_cmpRO (lh_code hc (i := 11) rfl) (v := l) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (lh_code hc (i := 12) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc1 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc1
  rs [g2, g5] at hcc1
  rw [BitVec.toNat_sub] at hcc1
  simp only [UInt64.toNat_toBitVec, hmask] at hcc1
  have hr40 : (o &&& idxMask).toNat + l.toNat < 2 ^ 40 := by omega
  -- the window
  refine ev_movRMt (lh_code hc (i := 13) rfl) hoffL (v := UInt64.ofNat SA) (by rs; exact hdA.1) ?_
  refine ev_subRR (lh_code hc (i := 14) rfl) fun st hcf => ?_
  rs [g2, hSAn] at hcf
  refine ev_jcc (lh_code hc (i := 15) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc3 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSAn] at hcc3
  refine ev_cmpRO (lh_code hc (i := 16) rfl) (v := l) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (lh_code hc (i := 17) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc4 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc4
  rs [g2] at hcc4
  rw [hsub SA _ (by omega) (by omega)] at hcc4
  simp only [UInt64.toNat_toBitVec] at hcc4
  have hqa : (o &&& idxMask).toNat + l.toNat ≤ SA := by omega
  refine ev_movRMt (lh_code hc (i := 18) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (lh_code hc (i := 19) rfl) ?_
  -- the fuel
  refine ev_subRR (lh_code hc (i := 20) rfl) fun st hcf => ?_
  rs [g6, g9] at hcf
  refine ev_jcc (lh_code hc (i := 21) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  refine ev_movRI (lh_code hc (i := 22) rfl) ?_
  have hl14 : l.toNat ≤ d.regs.r14.toNat := by omega
  have hlF : l.toNat < n := by omega
  have hrun := litHash_run p hp σ o l n hlF (Or.inr ⟨hr40, by rw [hszA]; exact hqa⟩)
  rw [← hSA] at hqa
  have hrdi0 : (UInt64.ofNat BA).toBitVec + (o &&& idxMask).toBitVec * 8 =
      (UInt64.ofNat (BA + 8 * ((o &&& idxMask).toNat + 0))).toBitVec := by
    have := addr_idx BA 0 (o &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  have hl1 : l.toNat = (l.toNat - 1) + 1 := by have := L.toNat_ne_zero_of_ne _ hnz; omega
  refine lh_loop hG hc _ hTR σ.mem (o &&& idxMask) _ (d.regs.r14 - l)
    (fun s' fr hm' h' => hfin _ hrun s' fr hm' h') (l.toNat - 1) 0 _ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try rs [g1, g2, g5, g6, g7, g9, g10, g11, g12, g13]
  · show (d.regs.r14 - l).toNat ≤ _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl14)]; omega
  · exact Pres.refl _ _
  · exact hmem
  · omega
  · apply UInt64.toBitVec_inj.mp; rw [hBA]; exact hrdi0
  · exact hl1
  · rfl
  · rw [← hl1, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]

end L.AsmEsc
