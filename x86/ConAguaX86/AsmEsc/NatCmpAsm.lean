module

public import ConAguaX86.AsmEsc.Chain2
public import ConAguaX86.AsmEsc.NatCmpL
import Kraken.X64.Registers

@[expose] public section

/-!
# Hand-written `nat_cmp` and its simulation contract

`natCmpAsm tab` is a hand-written body for `nat_cmp(oa, la, ob, lb)` (`L.Arena.natCmp`): `0`, `1`
or `2` as the number at `oa` (`la` limbs) is below, equal to or above the one at `ob` (`lb`
limbs). Different lengths decide; equal lengths compare from the top limb down. Up front (for
`la = lb > 0`): both windows inside their tiers and below `2^40` and fuel for the loop, else
`ca_exhausted`. The loop is 8 instructions per limb.

Registers: `rdi oa`, `r8 la`, `r9 ob`, `r10 lb`; in the loop `rdi`, `r9` the addresses of the
limbs 0 and `r8` the index.
-/

namespace L.AsmEsc

open L L.Arena L.Compiler

/-- A local label of the hand-written `nat_cmp`. -/
abbrev ncL (m : String) : Label := ".Lasm_nat_cmp_" ++ m

/-- The hand-written `nat_cmp`, for the table `tab` (the descriptor offsets of `POOL` = 0). -/
def natCmpAsm (tab : Tab) : Program :=
  [ .label (fnL "nat_cmp"),                                            -- 0
    i64 (.cmp (.reg (rr .r8)) (oR .r10)),                              -- 1
    jccL .c (ncL "Z0"),                                                -- 2  la < lb
    jccL .a (ncL "Z2"),                                                -- 3  la > lb
    i64 (.cmp (.reg (rr .r8)) (.imm (.int64 (0 : Word).toInt64))),     -- 4
    jccL .z (ncL "Z1"),                                                -- 5  la = lb = 0
    movRI .rax idxMask,                                                -- 6
    movRR .rcx .rdi,                                                   -- 7
    i64 (.shr (.reg (rr .rcx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 8
    i64 (.and (.reg (rr .rcx)) (.imm (.int64 (1 : Word).toInt64))),    -- 9  A's tier bit
    i64 (.and (.reg (rr .rdi)) (oR .rax)),                             -- 10 qa
    movRR .rdx .r9,                                                    -- 11
    i64 (.shr (.reg (rr .rdx)) (.imm8 (.int64 (Int64.ofInt 40)))),    -- 12
    i64 (.and (.reg (rr .rdx)) (.imm (.int64 (1 : Word).toInt64))),    -- 13 B's tier bit
    i64 (.and (.reg (rr .r9)) (oR .rax)),                              -- 14 qb
    movRR .r11 .rax,                                                   -- 15
    i64 (.sub (.reg (rr .r11)) (oR .rdi)),                             -- 16
    i64 (.cmp (.reg (rr .r11)) (oR .r8)),                              -- 17
    jccL .c exhaustedL,                                                -- 18 qa + la ≥ 2^40
    movRR .r11 .rax,                                                   -- 19
    i64 (.sub (.reg (rr .r11)) (oR .r9)),                              -- 20
    i64 (.cmp (.reg (rr .r11)) (oR .r8)),                              -- 21
    jccL .c exhaustedL,                                                -- 22 qb + la ≥ 2^40
    movRM .rax (tdesc .rcx (tab.len64 (0 : ArrId))),                   -- 23
    i64 (.sub (.reg (rr .rax)) (oR .rdi)),                             -- 24
    jccL .c exhaustedL,                                                -- 25
    i64 (.cmp (.reg (rr .rax)) (oR .r8)),                              -- 26
    jccL .c exhaustedL,                                                -- 27 len - qa < la
    movRM .rcx (tdesc .rcx (tab.base64 (0 : ArrId))),                  -- 28
    i64 (.lea (rr .rdi) (mbi .rcx .rdi .W64)),                         -- 29 rdi := &A[0]
    movRM .rax (tdesc .rdx (tab.len64 (0 : ArrId))),                   -- 30
    i64 (.sub (.reg (rr .rax)) (oR .r9)),                              -- 31
    jccL .c exhaustedL,                                                -- 32
    i64 (.cmp (.reg (rr .rax)) (oR .r8)),                              -- 33
    jccL .c exhaustedL,                                                -- 34 len - qb < la
    movRM .rdx (tdesc .rdx (tab.base64 (0 : ArrId))),                  -- 35
    i64 (.lea (rr .r9) (mbi .rdx .r9 .W64)),                           -- 36 r9 := &B[0]
    i64 (.sub (.reg (rr .r14)) (oR .r8)),                              -- 37
    jccL .c exhaustedL,                                                -- 38 fuel < la
    .label (ncL "L"),                                                  -- 39
    i64 (.sub (.reg (rr .r8)) (oI 1)),                                 -- 40 k := k - 1
    movRM .rax (mbi .rdi .r8 .W64),                                    -- 41
    movRM .rdx (mbi .r9 .r8 .W64),                                     -- 42
    i64 (.cmp (.reg (rr .rax)) (oR .rdx)),                             -- 43
    jccL .c (ncL "Z0"),                                                -- 44
    jccL .a (ncL "Z2"),                                                -- 45
    i64 (.cmp (.reg (rr .r8)) (.imm (.int64 (0 : Word).toInt64))),     -- 46
    jccL .nz (ncL "L"),                                                -- 47
    .label (ncL "Z1"),                                                 -- 48
    movRI .rax 1,                                                      -- 49
    i64 .ret,                                                          -- 50
    .label (ncL "Z0"),                                                 -- 51
    movRI .rax 0,                                                      -- 52
    i64 .ret,                                                          -- 53
    .label (ncL "Z2"),                                                 -- 54
    movRI .rax 2,                                                      -- 55
    i64 .ret ]                                                         -- 56

section
variable [Host] {kf : Nat} {tab : Tab}

theorem nc_code (hc : Code (natCmpAsm tab) kf) {i : Nat} {x : Directive}
    (hi : (natCmpAsm tab)[i]? = some x) : Host.prog[kf + i]? = some x := Code.get hc hi

end

section
variable [Host] {G : L.Compiler.Layout} (hG : G.Ok) {kf : Nat} (hc : Code (natCmpAsm G.tab) kf)
  {d : MachineData} {Q : MachineState → Prop}
include hG hc

/-- An exit (`.Z0`, `.Z1`, `.Z2` at `i`): `rax := c`, the return. -/
theorem nc_exit {i : Nat} {c : Word} {l : Label} (h0 : (natCmpAsm G.tab)[i]? = some (.label l))
    (h1 : (natCmpAsm G.tab)[i + 1]? = some (movRI .rax c)) (h2 : (natCmpAsm G.tab)[i + 2]? = some (i64 .ret))
    {ra : Word} (hra : rdW d.dmem (A d.regs.rsp.toNat) = some ra) (hlo : G.lo ≤ d.regs.rsp.toNat)
    (hhi : d.regs.rsp.toNat + 8 ≤ G.hi) (s : MachineData) (hF : MrFr G d s)
    (hok : ∀ s', s'.dmem = s.dmem → s'.regs.rsp.toNat = d.regs.rsp.toNat + 8 →
      s'.regs.rbp = d.regs.rbp → s'.regs.r15 = d.regs.r15 → s'.regs.r14.toNat ≤ d.regs.r14.toNat →
      s'.regs.rax = c → Ev Q s' (Int64.ofBitVec ra.toBitVec)) :
    Ev Q s (at_ (kf + i)) := by
  refine ev_label (nc_code hc h0) ?_
  refine ev_movRI (nc_code hc h1) ?_
  refine frame_ret hG hra hlo hhi ⟨?_, ?_, ?_, ?_, ?_⟩ (nc_code hc h2) fun s' e1 e2 e3 e4 e5 e6 => ?_
  all_goals try rs [hF.rsp, hF.rbp, hF.r15]
  · exact hF.r14
  · exact hF.pres
  · exact hok s' e1 e2 e3 e4 (by rw [e5]; rs; exact hF.r14) (by rw [e6]; rs)

/-- One step of the loop (`.L`), comparing limb `j`. -/
theorem nc_step (TA TB : TieredArray) (hTA : G.tab.dom64 TA = true) (hTB : G.tab.dom64 TB = true)
    (qa qb : Word) (M : Mem) (hm : MemRel G M d.dmem) (j : Nat) (s : MachineData) (hF : MrFr G d s)
    (hd : s.dmem = d.dmem)
    (hrdi : s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat))
    (hr9 : s.regs.r9 = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat)) (hr8 : s.regs.r8.toNat = j + 1)
    (hqa : qa.toNat + (j + 1) ≤ G.s (G.tab.pos64 TA)) (hqb : qb.toNat + (j + 1) ≤ G.s (G.tab.pos64 TB))
    (hnext : (M.arr64 TA)[(qa + UInt64.ofNat j).toNat]! = (M.arr64 TB)[(qb + UInt64.ofNat j).toNat]! → j ≠ 0 →
      ∀ s', MrFr G d s' → s'.dmem = d.dmem →
      s'.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s'.regs.r9 = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat) → s'.regs.r8.toNat = j →
      Ev Q s' (at_ (kf + 39)))
    (hZ0 : ncRes TA TB qa qb M (j + 1) = 0 → ∀ s', MrFr G d s' → s'.dmem = d.dmem → Ev Q s' (at_ (kf + 51)))
    (hZ1 : j = 0 → ncRes TA TB qa qb M (j + 1) = 1 → ∀ s', MrFr G d s' → s'.dmem = d.dmem →
      Ev Q s' (at_ (kf + 48)))
    (hZ2 : ncRes TA TB qa qb M (j + 1) = 2 → ∀ s', MrFr G d s' → s'.dmem = d.dmem → Ev Q s' (at_ (kf + 54))) :
    Ev Q s (at_ (kf + 39)) := by
  have hpA := G.tab.pos64_lt hTA
  have hpB := G.tab.pos64_lt hTB
  have heA := hG.end64 _ hpA
  have heB := hG.end64 _ hpB
  have hszA := hm.size64 TA hTA
  have hszB := hm.size64 TB hTB
  have hr8n := s.regs.r8.toNat_lt
  have hj : (UInt64.ofNat j).toNat = j := L.toNat_ofNat_of_lt (by omega)
  have hsub : s.regs.r8.toBitVec - (Int64.ofInt 1).toBitVec = (UInt64.ofNat j).toBitVec := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat j).toBitVec.toNat = j from hj]
    show (2 ^ 64 - 1 + s.regs.r8.toNat) % 2 ^ 64 = j
    omega
  generalize hBA : G.b (G.tab.pos64 TA) = BA at *
  generalize hBB : G.b (G.tab.pos64 TB) = BB at *
  have hqj : (qa + UInt64.ofNat j).toNat = qa.toNat + j := by rw [L.toNat_add_of_lt _ _ (by omega), hj]
  have hbj : (qb + UInt64.ofNat j).toNat = qb.toNat + j := by rw [L.toNat_add_of_lt _ _ (by omega), hj]
  have hinA : (qa + UInt64.ofNat j).toNat < (M.arr64 TA).size := by rw [hqj, hszA]; omega
  have hinB : (qb + UInt64.ofNat j).toNat < (M.arr64 TB).size := by rw [hbj, hszB]; omega
  have haA : (UInt64.ofNat (BA + 8 * qa.toNat)).toBitVec + (UInt64.ofNat j).toBitVec * 8 =
      A (BA + 8 * (qa + UInt64.ofNat j).toNat) := by
    rw [addr_idx BA qa.toNat (UInt64.ofNat j) (by omega), hqj, hj]
  have haB : (UInt64.ofNat (BB + 8 * qb.toNat)).toBitVec + (UInt64.ofNat j).toBitVec * 8 =
      A (BB + 8 * (qb + UInt64.ofNat j).toNat) := by
    rw [addr_idx BB qb.toNat (UInt64.ofNat j) (by omega), hbj, hj]
  have hrA : rdW s.dmem (A (BA + 8 * (qa + UInt64.ofNat j).toNat)) =
      some (M.arr64 TA)[(qa + UInt64.ofNat j).toNat] := by
    have := hm.get64 TA hTA _ hinA; rw [hBA] at this; rw [hd]; exact this
  have hrB : rdW s.dmem (A (BB + 8 * (qb + UInt64.ofNat j).toNat)) =
      some (M.arr64 TB)[(qb + UInt64.ofNat j).toNat] := by
    have := hm.get64 TB hTB _ hinB; rw [hBB] at this; rw [hd]; exact this
  have hR : ncRes TA TB qa qb M (j + 1) =
      if (M.arr64 TA)[(qa + UInt64.ofNat j).toNat] < (M.arr64 TB)[(qb + UInt64.ofNat j).toNat] then 0
      else if (M.arr64 TB)[(qb + UInt64.ofNat j).toNat] < (M.arr64 TA)[(qa + UInt64.ofNat j).toNat] then 2
      else ncRes TA TB qa qb M j := by
    simp only [ncRes, getElem!_pos, hinA, hinB]
  have hx' : (M.arr64 TA)[(qa + UInt64.ofNat j).toNat]! = (M.arr64 TA)[(qa + UInt64.ofNat j).toNat] := by
    simp only [getElem!_pos, hinA]
  have hy' : (M.arr64 TB)[(qb + UInt64.ofNat j).toNat]! = (M.arr64 TB)[(qb + UInt64.ofNat j).toNat] := by
    simp only [getElem!_pos, hinB]
  rw [hx', hy'] at hnext
  generalize (M.arr64 TA)[(qa + UInt64.ofNat j).toNat] = x at hrA hR hnext
  generalize (M.arr64 TB)[(qb + UInt64.ofNat j).toNat] = y at hrB hR hnext
  have hF' : ∀ s' : MachineData, s'.regs.rsp = s.regs.rsp → s'.regs.rbp = s.regs.rbp →
      s'.regs.r15 = s.regs.r15 → s'.regs.r14 = s.regs.r14 → s'.dmem = s.dmem → MrFr G d s' :=
    fun s' a b c e f => ⟨a.trans hF.rsp, b.trans hF.rbp, c.trans hF.r15, by rw [e]; exact hF.r14,
      by rw [f]; exact hF.pres⟩
  refine ev_label (nc_code hc (i := 39) rfl) ?_
  refine ev_subRI (nc_code hc (i := 40) rfl) fun st1 => ?_
  refine ev_ldX (nc_code hc (i := 41) rfl) (v := x) (by rs [hrdi]; rw [hsub, haA]; exact hrA) ?_
  refine ev_ldX (nc_code hc (i := 42) rfl) (v := y) (by rs [hr9]; rw [hsub, haB]; exact hrB) ?_
  refine ev_cmpRO (nc_code hc (i := 43) rfl) (v := y) (Or.inr (Or.inr ⟨.rdx, rfl, by rs⟩)) ?_
  refine ev_jcc (nc_code hc (i := 44) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hcc
    rs at hcc
    have hlt : x < y := UInt64.lt_iff_toNat_lt.mpr hcc
    refine ev_lbl (Code.label hc (i := 51) rfl) ?_
    exact hZ0 (by rw [hR]; simp only [hlt, reduceIte]) _ (hF' _ (by rs) (by rs) (by rs) (by rs) rfl) (by rw [← hd])
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc
  rs at hcc
  have hnlt : ¬ x < y := fun h => hcc (UInt64.lt_iff_toNat_lt.mp h)
  refine ev_jcc (nc_code hc (i := 45) rfl) (fun hca => ?_) (fun hca => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, beq_eq_false_iff_ne] at hca
    rs at hca
    have hgt : y < x := by
      rw [UInt64.lt_iff_toNat_lt]
      have h2 : x ≠ y := fun e => hca.2 (by rw [e])
      have h3 : x.toNat ≠ y.toNat := fun e => h2 (UInt64.toNat_inj.mp e)
      have e1 : x.toBitVec.toNat = x.toNat := rfl
      have e2 : y.toBitVec.toNat = y.toNat := rfl
      omega
    refine ev_lbl (Code.label hc (i := 54) rfl) ?_
    exact hZ2 (by rw [hR]; simp only [hnlt, hgt, reduceIte]) _ (hF' _ (by rs) (by rs) (by rs) (by rs) rfl) (by rw [← hd])
  have heq : x = y := by
    simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Bool.and_eq_false_iff, Bool.not_eq_false',
      decide_eq_true_eq, beq_iff_eq] at hca
    rs at hca
    rcases hca with h | h
    · exact absurd h hcc
    · exact UInt64.toBitVec_inj.mp h
  have hngt : ¬ y < x := by rw [heq]; exact UInt64.lt_irrefl _
  refine ev_cmpRO (nc_code hc (i := 46) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (nc_code hc (i := 47) rfl) (fun hcz => ?_) (fun hcz => ?_)
  · simp only [CondCode.interp, cmpFlags_zf, Bool.not_eq_true', beq_eq_false_iff_ne] at hcz
    rs at hcz
    rw [hsub] at hcz
    have hj0 : j ≠ 0 := by intro h; subst h; exact hcz rfl
    refine ev_lbl (Code.label hc (i := 39) rfl) ?_
    refine hnext heq hj0 _ (hF' _ (by rs) (by rs) (by rs) (by rs) rfl) (by rw [← hd]) (by rs [hrdi])
      (by rs [hr9]) ?_
    rs; rw [hsub]; exact hj
  · simp only [CondCode.interp, cmpFlags_zf, Bool.not_eq_false', beq_iff_eq] at hcz
    rs at hcz
    rw [hsub] at hcz
    have hj0 : j = 0 := by
      have := congrArg BitVec.toNat hcz
      rw [show (UInt64.ofNat j).toBitVec.toNat = j from hj] at this
      simpa using this
    subst hj0
    exact hZ1 rfl (by rw [hR]; simp only [hnlt, hngt, reduceIte]; rfl) _ (hF' _ (by rs) (by rs) (by rs) (by rs) rfl)
      (by rw [← hd])

/-- The loop from `.L` with `j + 1` limbs left (memory `M`, never written): to the exit of
`ncRes` (`.Z0`, `.Z1` or `.Z2`). -/
theorem nc_loop (TA TB : TieredArray) (hTA : G.tab.dom64 TA = true) (hTB : G.tab.dom64 TB = true)
    (qa qb : Word) (M : Mem) (hm : MemRel G M d.dmem) :
    ∀ (j : Nat) (s : MachineData), MrFr G d s → s.dmem = d.dmem →
      s.regs.rdi = UInt64.ofNat (G.b (G.tab.pos64 TA) + 8 * qa.toNat) →
      s.regs.r9 = UInt64.ofNat (G.b (G.tab.pos64 TB) + 8 * qb.toNat) → s.regs.r8.toNat = j + 1 →
      qa.toNat + (j + 1) ≤ G.s (G.tab.pos64 TA) → qb.toNat + (j + 1) ≤ G.s (G.tab.pos64 TB) →
      (ncRes TA TB qa qb M (j + 1) = 0 → ∀ s', MrFr G d s' → s'.dmem = d.dmem → Ev Q s' (at_ (kf + 51))) →
      (ncRes TA TB qa qb M (j + 1) = 1 → ∀ s', MrFr G d s' → s'.dmem = d.dmem → Ev Q s' (at_ (kf + 48))) →
      (ncRes TA TB qa qb M (j + 1) = 2 → ∀ s', MrFr G d s' → s'.dmem = d.dmem → Ev Q s' (at_ (kf + 54))) →
      Ev Q s (at_ (kf + 39)) := by
  intro j
  induction j with
  | zero =>
    intro s hF hd h1 h2 h3 h4 h5 hZ0 hZ1 hZ2
    exact nc_step hG hc TA TB hTA hTB qa qb M hm 0 s hF hd h1 h2 h3 h4 h5 (fun _ h => absurd rfl h)
      hZ0 (fun _ => hZ1) hZ2
  | succ j ih =>
    intro s hF hd h1 h2 h3 h4 h5 hZ0 hZ1 hZ2
    refine nc_step hG hc TA TB hTA hTB qa qb M hm (j + 1) s hF hd h1 h2 h3 h4 h5 ?_ hZ0
      (fun h => absurd h (by omega)) hZ2
    intro heq _ s' g1 g2 g3 g4 g5
    rw [ncRes_eq TA TB qa qb M (j + 1) heq] at hZ0 hZ1 hZ2
    exact ih s' g1 g2 g3 g4 g5 (by omega) (by omega) hZ0 hZ1 hZ2

end

/-- **The hand-written `nat_cmp` meets the compiler's per-function contract**, for any table in
which `POOL` (0) is a tiered word array with small descriptor offsets, at every fuel. -/
theorem natCmpAsm_sim [Host] (p : Prog) (G : L.Compiler.Layout) (hG : G.Ok)
    (hp : p.lookup "nat_cmp" = some natCmp) (hdom : G.tab.dom64 (tier1 0) = true)
    (hoffL : SmallOff (G.tab.len64 (0 : ArrId))) (hoffB : SmallOff (G.tab.base64 (0 : ArrId)))
    (kf : Nat) (hc : Code (natCmpAsm G.tab) kf) (sk : NTree) (n : Nat) :
    FnSimAt p G sk n "nat_cmp" natCmp kf := by
  intro vs σ d ra Q hlen hra hargs hlo8 hhi h15 hmem h14 hok herr habrt hexh
  have hlo : G.lo ≤ d.regs.rsp.toNat := by omega
  rw [natCmp_nparams] at hlen
  obtain ⟨oa, la, ob, lb, rfl⟩ : ∃ oa la ob lb, vs = [oa, la, ob, lb] := by
    match vs, hlen with
    | [oa, la, ob, lb], _ => exact ⟨oa, la, ob, lb, rfl⟩
  have hA := hargs.1 (by simp [argRegs])
  have hrdi : d.regs.rdi = oa := UInt64.toBitVec_inj.mp (hA 0 (by simp))
  have hr8 : d.regs.r8 = la := UInt64.toBitVec_inj.mp (hA 1 (by simp))
  have hr9 : d.regs.r9 = ob := UInt64.toBitVec_inj.mp (hA 2 (by simp))
  have hr10 : d.regs.r10 = lb := UInt64.toBitVec_inj.mp (hA 3 (by simp))
  have hh := hG.hi_le
  have hnr : Stmt.nret natCmp.body = 1 := by rw [natCmp_body]; rfl
  have hn0 : 0 < n := by omega
  -- every exit: the result `c` of the run, `rax := c`, the return
  have hfin : ∀ (c : Word), (invoke p (exec p n) "nat_cmp" [oa, la, ob, lb]).run σ = .ok ([c], σ) →
      ∀ (i : Nat) (l : Label), (natCmpAsm G.tab)[i]? = some (.label l) →
      (natCmpAsm G.tab)[i + 1]? = some (movRI .rax c) → (natCmpAsm G.tab)[i + 2]? = some (i64 .ret) →
      ∀ s, MrFr G d s → s.dmem = d.dmem → Ev Q s (at_ (kf + i)) := by
    intro c hrun i l h0 h1 h2 s hF hd
    refine nc_exit hG hc h0 h1 h2 hra hlo hhi s hF fun s' e1 e2 e3 e4 e5 e6 => ?_
    refine hok _ _ s' hrun (by rw [e1, hd]; exact hmem) rfl e2 e3 e4 e5 ?_ (by rw [e1, hd]; exact Pres.refl _ _)
    rw [hnr]; exact resOut_zero' e6
  have hFd : ∀ s : MachineData, s.regs.rsp = d.regs.rsp → s.regs.rbp = d.regs.rbp → s.regs.r15 = d.regs.r15 →
      s.regs.r14.toNat ≤ d.regs.r14.toNat → s.dmem = d.dmem → MrFr G d s :=
    fun s a b c e f => ⟨a, b, c, e, by rw [f]; exact Pres.refl _ _⟩
  refine ev_label (nc_code hc (i := 0) rfl) ?_
  refine ev_cmpRO (nc_code hc (i := 1) rfl) (v := lb) (Or.inr (Or.inr ⟨.r10, rfl, by rs [hr10]⟩)) ?_
  refine ev_jcc (nc_code hc (i := 2) rfl) (fun hcc => ?_) (fun hcc => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, decide_eq_true_eq] at hcc
    rs [hr8] at hcc
    have hlt : la < lb := UInt64.lt_iff_toNat_lt.mpr hcc
    have hne : la ≠ lb := fun e => by rw [e] at hlt; exact UInt64.lt_irrefl _ hlt
    have hrun := natCmp_run p hp σ oa la ob lb n hn0 (fun e => absurd e hne) (fun e => absurd e hne)
    simp only [hlt, reduceIte] at hrun
    refine ev_lbl (Code.label hc (i := 51) rfl) ?_
    exact hfin 0 hrun 51 _ rfl rfl rfl _ (hFd _ rfl rfl rfl (Nat.le_refl _) rfl) rfl
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc
  rs [hr8] at hcc
  have hnlt : ¬ la < lb := fun h => hcc (UInt64.lt_iff_toNat_lt.mp h)
  refine ev_jcc (nc_code hc (i := 3) rfl) (fun hca => ?_) (fun hca => ?_)
  · simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, beq_eq_false_iff_ne] at hca
    rs [hr8, hr10] at hca
    have hgt : lb < la := by
      rw [UInt64.lt_iff_toNat_lt]
      have h2 : la ≠ lb := fun e => hca.2 (by rw [e])
      have h3 : la.toNat ≠ lb.toNat := fun e => h2 (UInt64.toNat_inj.mp e)
      have e1 : la.toBitVec.toNat = la.toNat := rfl
      have e2 : lb.toBitVec.toNat = lb.toNat := rfl
      omega
    have hne : la ≠ lb := fun e => by rw [e] at hgt; exact UInt64.lt_irrefl _ hgt
    have hrun := natCmp_run p hp σ oa la ob lb n hn0 (fun e => absurd e hne) (fun e => absurd e hne)
    simp only [hnlt, hgt, reduceIte] at hrun
    refine ev_lbl (Code.label hc (i := 54) rfl) ?_
    exact hfin 2 hrun 54 _ rfl rfl rfl _ (hFd _ rfl rfl rfl (Nat.le_refl _) rfl) rfl
  have heq : la = lb := by
    simp only [CondCode.interp, cmpFlags_cf, cmpFlags_zf, Bool.and_eq_false_iff, Bool.not_eq_false',
      decide_eq_true_eq, beq_iff_eq] at hca
    rs [hr8, hr10] at hca
    rcases hca with h | h
    · exact absurd h hcc
    · exact UInt64.toBitVec_inj.mp h
  subst heq
  have hngt : ¬ la < la := UInt64.lt_irrefl _
  refine ev_cmpRO (nc_code hc (i := 4) rfl) (v := 0) (Or.inl rfl) ?_
  refine ev_jcc (nc_code hc (i := 5) rfl) (fun hcz => ?_) (fun hcz => ?_)
  · simp only [CondCode.interp, cmpFlags_zf, beq_iff_eq] at hcz
    rs [hr8] at hcz
    have hl0 : la = 0 := UInt64.toBitVec_inj.mp hcz
    subst hl0
    have hrun := natCmp_run p hp σ oa 0 ob 0 n hn0 (fun _ => by simpa using hn0) (fun _ => Or.inl rfl)
    simp only [hngt, reduceIte, UInt64.toNat_zero, ncRes] at hrun
    refine ev_lbl (Code.label hc (i := 48) rfl) ?_
    exact hfin 1 hrun 48 _ rfl rfl rfl _ (hFd _ rfl rfl rfl (Nat.le_refl _) rfl) rfl
  simp only [CondCode.interp, cmpFlags_zf, beq_eq_false_iff_ne] at hcz
  rs [hr8] at hcz
  have hnz : la ≠ 0 := fun h => hcz (by rw [h])
  refine ev_movRI (nc_code hc (i := 6) rfl) ?_
  refine ev_movRR (nc_code hc (i := 7) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (nc_code hc (i := 8) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (nc_code hc (i := 9) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (nc_code hc (i := 10) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_movRR (nc_code hc (i := 11) rfl) ?_
  refine ev_shiftR (n := 40) (op := .shr) (by decide) (Or.inr rfl) (nc_code hc (i := 12) rfl) fun st => ?_
  refine ev_aluRI (op := .and) (w := 1) rfl (nc_code hc (i := 13) rfl) fun st => ?_
  refine ev_aluOp (op := .and) (v := idxMask) rfl (nc_code hc (i := 14) rfl) (Or.inr (Or.inr ⟨.rax, rfl, by rs⟩))
    fun st => ?_
  refine ev_gen (fun s1 => s1.regs.rcx = (oa >>> 40) &&& 1 ∧ s1.regs.rdi = oa &&& idxMask ∧
      s1.regs.rdx = (ob >>> 40) &&& 1 ∧ s1.regs.r9 = ob &&& idxMask ∧ s1.regs.rax = idxMask ∧
      s1.regs.r8 = la ∧ s1.regs.r14 = d.regs.r14 ∧ s1.regs.r15 = d.regs.r15 ∧
      s1.regs.rsp = d.regs.rsp ∧ s1.regs.rbp = d.regs.rbp ∧ s1.dmem = d.dmem)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rs [hrdi, hr8, hr9, hr10, BinOp.eval]
        all_goals rfl)
    fun s1 ⟨g1, g2, g3, g4, g5, g6, g9, g10, g11, g12, g13⟩ => ?_
  have hTA := G.tab.dom64_tierA hdom (oa >>> 40)
  have hTB := G.tab.dom64_tierA hdom (ob >>> 40)
  have heA := hG.end64 _ (G.tab.pos64_lt hTA)
  have heB := hG.end64 _ (G.tab.pos64_lt hTB)
  have hm1 : MemRel G σ.mem s1.dmem := by rw [g13]; exact hmem
  have h15' : s1.regs.r15.toNat = G.T := by rw [g10]; exact h15
  have hdA := pool_desc hm1 hdom (oa >>> 40) (r := .rcx) (by rs [g1]) h15'
  have hdB := pool_desc hm1 hdom (ob >>> 40) (r := .rdx) (by rs [g3]) h15'
  have hszA := hmem.size64 _ hTA
  have hszB := hmem.size64 _ hTB
  generalize hSA : G.s (G.tab.pos64 (tierA 0 (oa >>> 40))) = SA at *
  generalize hSB : G.s (G.tab.pos64 (tierA 0 (ob >>> 40))) = SB at *
  generalize hBA : G.b (G.tab.pos64 (tierA 0 (oa >>> 40))) = BA at *
  generalize hBB : G.b (G.tab.pos64 (tierA 0 (ob >>> 40))) = BB at *
  have hSAn : (UInt64.ofNat SA).toNat = SA := L.toNat_ofNat_of_lt (by omega)
  have hSBn : (UInt64.ofNat SB).toNat = SB := L.toNat_ofNat_of_lt (by omega)
  have hsub : ∀ (S : Nat) (w : Word), S < 2 ^ 64 → w.toNat ≤ S →
      ((UInt64.ofNat S).toBitVec - w.toBitVec).toNat = S - w.toNat := by
    intro S w h1 h2
    rw [BitVec.toNat_sub, UInt64.toNat_toBitVec, show (UInt64.ofNat S).toBitVec.toNat = S from
      L.toNat_ofNat_of_lt h1]
    have := w.toNat_lt; omega
  have hra' : (oa &&& idxMask).toNat < 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hrb' : (ob &&& idxMask).toNat < 2 ^ 40 := by
    rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hmask : (idxMask : Word).toNat = 2 ^ 40 - 1 := rfl
  have hX : ∀ s', s'.regs.rbp = d.regs.rbp → s'.dmem = s1.dmem → Ev Q s' (label exhaustedL) :=
    fun s' e1 e2 => hexh _ ⟨e1, by rw [e2, g13]; exact Pres.refl _ _⟩
  -- the indices stay below `2^40`
  refine ev_movRR (nc_code hc (i := 15) rfl) ?_
  refine ev_subRR (nc_code hc (i := 16) rfl) fun _ _ => ?_
  refine ev_cmpRO (nc_code hc (i := 17) rfl) (v := la) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (nc_code hc (i := 18) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc1 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc1
  rs [g2, g5] at hcc1
  rw [BitVec.toNat_sub] at hcc1
  simp only [UInt64.toNat_toBitVec, hmask] at hcc1
  have ha40 : (oa &&& idxMask).toNat + la.toNat ≤ 2 ^ 40 := by omega
  refine ev_movRR (nc_code hc (i := 19) rfl) ?_
  refine ev_subRR (nc_code hc (i := 20) rfl) fun _ _ => ?_
  refine ev_cmpRO (nc_code hc (i := 21) rfl) (v := la) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (nc_code hc (i := 22) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc2 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc2
  rs [g4, g5] at hcc2
  rw [BitVec.toNat_sub] at hcc2
  simp only [UInt64.toNat_toBitVec, hmask] at hcc2
  have hb40 : (ob &&& idxMask).toNat + la.toNat ≤ 2 ^ 40 := by omega
  -- the window of `A`
  refine ev_movRMt (nc_code hc (i := 23) rfl) hoffL (v := UInt64.ofNat SA) (by rs; exact hdA.1) ?_
  refine ev_subRR (nc_code hc (i := 24) rfl) fun st hcf => ?_
  rs [g2, hSAn] at hcf
  refine ev_jcc (nc_code hc (i := 25) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc3 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSAn] at hcc3
  refine ev_cmpRO (nc_code hc (i := 26) rfl) (v := la) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (nc_code hc (i := 27) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc4 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc4
  rs [g2] at hcc4
  rw [hsub SA _ (by omega) (by omega)] at hcc4
  simp only [UInt64.toNat_toBitVec] at hcc4
  have hqa : (oa &&& idxMask).toNat + la.toNat ≤ SA := by omega
  refine ev_movRMt (nc_code hc (i := 28) rfl) hoffB (v := UInt64.ofNat BA) (by rs; exact hdA.2) ?_
  refine ev_leaX (nc_code hc (i := 29) rfl) ?_
  -- the window of `B`
  refine ev_movRMt (nc_code hc (i := 30) rfl) hoffL (v := UInt64.ofNat SB) (by rs; exact hdB.1) ?_
  refine ev_subRR (nc_code hc (i := 31) rfl) fun st hcf => ?_
  rs [g4, hSBn] at hcf
  refine ev_jcc (nc_code hc (i := 32) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc5 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec, hSBn] at hcc5
  refine ev_cmpRO (nc_code hc (i := 33) rfl) (v := la) (Or.inr (Or.inr ⟨.r8, rfl, by rs [g6]⟩)) ?_
  refine ev_jcc (nc_code hc (i := 34) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc6 => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not] at hcc6
  rs [g4] at hcc6
  rw [hsub SB _ (by omega) (by omega)] at hcc6
  simp only [UInt64.toNat_toBitVec] at hcc6
  have hqb : (ob &&& idxMask).toNat + la.toNat ≤ SB := by omega
  refine ev_movRMt (nc_code hc (i := 35) rfl) hoffB (v := UInt64.ofNat BB) (by rs; exact hdB.2) ?_
  refine ev_leaX (nc_code hc (i := 36) rfl) ?_
  -- the fuel
  refine ev_subRR (nc_code hc (i := 37) rfl) fun st hcf => ?_
  rs [g6, g9] at hcf
  refine ev_jcc (nc_code hc (i := 38) rfl) (fun _ => hX _ (by rs [g12]) rfl) (fun hcc7 => ?_)
  simp only [CondCode.interp, hcf, decide_eq_false_iff_not, UInt64.toNat_toBitVec] at hcc7
  have hl14 : la.toNat ≤ d.regs.r14.toNat := by omega
  have hlF : la.toNat < n := by omega
  have hrun := natCmp_run p hp σ oa la ob la n hn0 (fun _ => hlF)
    (fun _ => Or.inr ⟨ha40, hb40, by rw [hszA]; exact hqa, by rw [hszB]; exact hqb⟩)
  simp only [hngt, reduceIte] at hrun
  rw [← hSA] at hqa
  rw [← hSB] at hqb
  have hrdi0 : (UInt64.ofNat BA).toBitVec + (oa &&& idxMask).toBitVec * 8 =
      (UInt64.ofNat (BA + 8 * (oa &&& idxMask).toNat)).toBitVec := by
    have := addr_idx BA 0 (oa &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  have hr90 : (UInt64.ofNat BB).toBitVec + (ob &&& idxMask).toBitVec * 8 =
      (UInt64.ofNat (BB + 8 * (ob &&& idxMask).toNat)).toBitVec := by
    have := addr_idx BB 0 (ob &&& idxMask) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at this
    rw [this]; rfl
  have hpos : la.toNat ≠ 0 := fun h => hnz (UInt64.toNat_inj.mp (by rw [h]; rfl))
  have hj : la.toNat = (la.toNat - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos)).symm
  rw [hj] at hrun
  refine nc_loop (d := d) hG hc _ _ hTA hTB (oa &&& idxMask) (ob &&& idxMask) σ.mem hmem (la.toNat - 1) _
    (hFd _ (by rs [g11]) (by rs [g12]) (by rs [g10]) ?_ (by rs [g13])) (by rs [g13])
    (by apply UInt64.toBitVec_inj.mp; rs [g1, g2]; rw [hBA]; exact hrdi0)
    (by apply UInt64.toBitVec_inj.mp; rs [g3, g4]; rw [hBB]; exact hr90)
    (by rs [g6]; exact hj) (by omega) (by omega)
    (fun h s' fr hd => hfin 0 (by rw [hrun, h]) 51 _ rfl rfl rfl s' fr hd)
    (fun h s' fr hd => hfin 1 (by rw [hrun, h]) 48 _ rfl rfl rfl s' fr hd)
    (fun h s' fr hd => hfin 2 (by rw [hrun, h]) 54 _ rfl rfl rfl s' fr hd)
  rs [g6, g9]
  show (d.regs.r14 - la).toNat ≤ _
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl14)]; omega

end L.AsmEsc
