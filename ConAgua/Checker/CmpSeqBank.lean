module

public import ConAgua.Checker.CmpSeqMv
import all ConAgua.Checker.CmpSeqEntry
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.FreezeSpec
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Modes `8` and `9`'s bank switches (lane compare2, the sJ variant)

`cq_bank_s()` (`Checker/CmpSeqEntry.lean`) runs as `cqBankSM`: the six row swaps (`cqRowsS`, each
`cqRowStep`: `cqRowsM` and the extent in `CCTL[k]`), then the records, firsts and declaration pool
kept and swapped at the larger extent (`cqTailS`); `CqRowsSOK`/`CqTailSOK` are its checks.
`cq_bank_c()` runs as `cqBankCM`: the nine copies back from the stash at the extents `CCTL[0‥8]`.
-/

namespace L.Checker
open L L.Arena L.Front
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true

theorem cq_getElem_rdW (a : Array Word) (x : Word) (h : x.toNat < a.size) : a[x.toNat] = rdW a x := by
  simp [rdW, h]

theorem cq_getElem_rdW0 (a : Array Word) (h : 0 < a.size) : a[0] = rdW a 0 := by
  simp [rdW, h]

theorem cq_toNat_18 {a : Word} (h : ¬ 576460752303423488 ≤ a) :
    (1 + 8 * a).toNat = 1 + 8 * a.toNat ∧ a.toNat < 2 ^ 59 := by
  have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
  simp at this
  refine ⟨?_, by omega⟩
  simp [UInt64.toNat_add, UInt64.toNat_mul]; omega

theorem cq_toNat_1 {a : Word} (h : ¬ 576460752303423488 ≤ a) : (1 + a).toNat = 1 + a.toNat ∧ a.toNat < 2 ^ 59 := by
  have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
  simp at this
  refine ⟨?_, by omega⟩
  simp [UInt64.toNat_add]; omega

/-- The lookups `cq_bank_s` needs. -/
structure CqBankSProg (p : Prog) : Prop where
  ea : p.lookup "cq_swap_eixa" = some (cqSwapRowsG CEIXA EIXA SIXA 34)
  ta : p.lookup "cq_swap_tixa" = some (cqSwapRowsG CTIXA TIXA STXA 34)
  es : p.lookup "cq_swap_eixs" = some (cqSwapRowsG CEIXS EIXS SIXS 36)
  ts : p.lookup "cq_swap_tixs" = some (cqSwapRowsG CTIXS TIXS STXS 36)
  en : p.lookup "cq_swap_eixn" = some (cqSwapRowsG CEIXN EIXN SIXN 38)
  tn : p.lookup "cq_swap_tixn" = some (cqSwapRowsG CTIXN TIXN STXN 38)

/-- `if a < b then b else a`. -/
def cqMax (a b : Word) : Word := if a < b then b else a

/-- One row swap of `cq_bank_s` and its extent's store `CCTL[k]`. -/
def cqRowStep (c d s : ArrId) (ca k : Word) (m : Mem) : Mem :=
  (cqRowsM c d s ca m).set64 CCTL k (cqRowsN m ca)

/-- The memory after `cq_bank_s`'s six row swaps. -/
def cqRowsS (m0 : Mem) : Mem :=
  cqRowStep CTIXN TIXN STXN 38 5 <| cqRowStep CEIXN EIXN SIXN 38 4 <| cqRowStep CTIXS TIXS STXS 36 3 <|
    cqRowStep CEIXS EIXS SIXS 36 2 <| cqRowStep CTIXA TIXA STXA 34 1 <| cqRowStep CEIXA EIXA SIXA 34 0 m0

/-- The row swaps' checks. -/
def CqRowsSOK (m0 : Mem) : Prop :=
  let m1 := cqRowStep CEIXA EIXA SIXA 34 0 m0
  let m2 := cqRowStep CTIXA TIXA STXA 34 1 m1
  let m3 := cqRowStep CEIXS EIXS SIXS 36 2 m2
  let m4 := cqRowStep CTIXS TIXS STXS 36 3 m3
  let m5 := cqRowStep CEIXN EIXN SIXN 38 4 m4
  CqRowsOK CEIXA EIXA SIXA 34 m0 ∧ CqRowsOK CTIXA TIXA STXA 34 m1 ∧ CqRowsOK CEIXS EIXS SIXS 36 m2 ∧
    CqRowsOK CTIXS TIXS STXS 36 m3 ∧ CqRowsOK CEIXN EIXN SIXN 38 m4 ∧ CqRowsOK CTIXN TIXN STXN 38 m5 ∧
    9 ≤ (m0.arr64 CCTL).size

/-- The records' extent `cq_bank_s` copies (the larger count). -/
def cqDeclA (m : Mem) : Word := cqMax (rdW (m.arr64 DECL) 0) (rdW (m.arr64 SDECL) 0)

/-- The declaration pools' extent (the larger). -/
def cqDlpA (m : Mem) : Word := cqMax (rdW (m.arr64 DLP) 0) (rdW (m.arr64 SDLP) 0)

/-- `cq_bank_s`'s copies after the row swaps. -/
def cqTailS (m6 : Mem) : Mem :=
  let a := cqDeclA m6
  let n := 1 + 8 * a
  let m7 := ((m6.set64 CCTL 6 n).copy64 CDECL 0 DECL 0 n.toNat).copy64 DECL 0 SDECL 0 n.toNat
  let m8 := ((m7.set64 CCTL 7 a).copy64 CFIRSTS 0 FIRSTS 0 a.toNat).copy64 FIRSTS 0 SFIRSTS 0 a.toNat
  let n2 := 1 + cqDlpA m8
  ((m8.set64 CCTL 8 n2).copy64 CDLP 0 DLP 0 n2.toNat).copy64 DLP 0 SDLP 0 n2.toNat

/-- The copies' checks. -/
def CqTailSOK (m6 : Mem) : Prop :=
  0 < (m6.arr64 DECL).size ∧ 0 < (m6.arr64 SDECL).size ∧ 0 < (m6.arr64 DLP).size ∧
    0 < (m6.arr64 SDLP).size ∧
    (cqDeclA m6).toNat < 2 ^ 59 ∧ (cqDlpA m6).toNat < 2 ^ 59 ∧
    1 + 8 * (cqDeclA m6).toNat ≤ (m6.arr64 CDECL).size ∧ 1 + 8 * (cqDeclA m6).toNat ≤ (m6.arr64 DECL).size ∧
    1 + 8 * (cqDeclA m6).toNat ≤ (m6.arr64 SDECL).size ∧
    (cqDeclA m6).toNat ≤ (m6.arr64 CFIRSTS).size ∧ (cqDeclA m6).toNat ≤ (m6.arr64 FIRSTS).size ∧
    (cqDeclA m6).toNat ≤ (m6.arr64 SFIRSTS).size ∧
    1 + (cqDlpA m6).toNat ≤ (m6.arr64 CDLP).size ∧ 1 + (cqDlpA m6).toNat ≤ (m6.arr64 DLP).size ∧
    1 + (cqDlpA m6).toNat ≤ (m6.arr64 SDLP).size

theorem cqTailSOK_intro {M : Mem} {a b : Word} (ha : cqDeclA M = a) (hb : cqDlpA M = b)
    (d0 : 0 < (M.arr64 DECL).size) (d1 : 0 < (M.arr64 SDECL).size) (l0 : 0 < (M.arr64 DLP).size)
    (l1 : 0 < (M.arr64 SDLP).size) (hA : a.toNat < 2 ^ 59) (hB : b.toNat < 2 ^ 59)
    (k1 : 1 + 8 * a.toNat ≤ (M.arr64 CDECL).size ∧ 1 + 8 * a.toNat ≤ (M.arr64 DECL).size)
    (k2 : 1 + 8 * a.toNat ≤ (M.arr64 DECL).size ∧ 1 + 8 * a.toNat ≤ (M.arr64 SDECL).size)
    (k3 : a.toNat ≤ (M.arr64 CFIRSTS).size ∧ a.toNat ≤ (M.arr64 FIRSTS).size)
    (k4 : a.toNat ≤ (M.arr64 FIRSTS).size ∧ a.toNat ≤ (M.arr64 SFIRSTS).size)
    (k5 : 1 + b.toNat ≤ (M.arr64 CDLP).size ∧ 1 + b.toNat ≤ (M.arr64 DLP).size)
    (k6 : 1 + b.toNat ≤ (M.arr64 DLP).size ∧ 1 + b.toNat ≤ (M.arr64 SDLP).size) : CqTailSOK M := by
  subst ha hb
  exact ⟨d0, d1, l0, l1, hA, hB, k1.1, k1.2, k2.2, k3.1, k3.2, k4.2, k5.1, k5.2, k6.2⟩

/-- **The memory after `cq_bank_s()`**. -/
def cqBankSM (m0 : Mem) : Mem := cqTailS (cqRowsS m0)

theorem cqBankS_spec (p : Prog) (hp : p.lookup "cq_bank_s" = some cqBankSL) (hP : CqBankSProg p) (n : Nat) (s₀ : St) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "cq_bank_s" []
    ⦃fun _ s' => LocEq s' s₀ ∧ CqRowsSOK s₀.mem ∧ CqTailSOK (cqRowsS s₀.mem) ∧ s'.mem = cqBankSM s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cqBankSL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have h1 := cqSwapRows_spec p hP.ea n
    have h2 := cqSwapRows_spec p hP.ta n
    have h3 := cqSwapRows_spec p hP.es n
    have h4 := cqSwapRows_spec p hP.ts n
    have h5 := cqSwapRows_spec p hP.en n
    have h6 := cqSwapRows_spec p hP.tn n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr,
      (h1 ·), (h2 ·), (h3 ·), (h4 ·), (h5 ·), (h6 ·)]
    all_goals clear h1 h2 h3 h4 h5 h6
    all_goals rename_i s0 e0 rs1 t1 a1 c1 rs2 t2 a2 c2 rs3 t3 a3 c3 rs4 t4 a4 c4 rs5 t5 a5 c5 t6 a6 c6 d0 d1 q1 q2 d2 k1 k2 d3 k3 k4 l0 l1 q3 q4 d4 k5 k6
    all_goals subst e0
    all_goals simp only [L.reduceLoc, L.St.setLocs_mem] at a1 a2 a3 a4 a5 a6
    all_goals obtain ⟨-, o1, e1, r1⟩ := a1
    all_goals obtain ⟨-, o2, e2, r2⟩ := a2
    all_goals obtain ⟨-, o3, e3, r3⟩ := a3
    all_goals obtain ⟨-, o4, e4, r4⟩ := a4
    all_goals obtain ⟨-, o5, e5, r5⟩ := a5
    all_goals obtain ⟨-, o6, e6, r6⟩ := a6
    all_goals have H1 : t1.mem.set64 CCTL 0 (rs1.headD 0) = cqRowStep CEIXA EIXA SIXA 34 0 s0.mem := by simp only [cqRowStep, e1, r1]
    all_goals have H2 : t2.mem.set64 CCTL 1 (rs2.headD 0) = cqRowStep CTIXA TIXA STXA 34 1 (cqRowStep CEIXA EIXA SIXA 34 0 s0.mem) := by simp only [e2, r2, H1, cqRowStep]
    all_goals have H3 : t3.mem.set64 CCTL 2 (rs3.headD 0) = cqRowStep CEIXS EIXS SIXS 36 2 (cqRowStep CTIXA TIXA STXA 34 1 (cqRowStep CEIXA EIXA SIXA 34 0 s0.mem)) := by simp only [e3, r3, H2, cqRowStep]
    all_goals have H4 : t4.mem.set64 CCTL 3 (rs4.headD 0) = cqRowStep CTIXS TIXS STXS 36 3 (cqRowStep CEIXS EIXS SIXS 36 2 (cqRowStep CTIXA TIXA STXA 34 1 (cqRowStep CEIXA EIXA SIXA 34 0 s0.mem))) := by simp only [e4, r4, H3, cqRowStep]
    all_goals have H5 : t5.mem.set64 CCTL 4 (rs5.headD 0) = cqRowStep CEIXN EIXN SIXN 38 4 (cqRowStep CTIXS TIXS STXS 36 3 (cqRowStep CEIXS EIXS SIXS 36 2 (cqRowStep CTIXA TIXA STXA 34 1 (cqRowStep CEIXA EIXA SIXA 34 0 s0.mem)))) := by simp only [e5, r5, H4, cqRowStep]
    all_goals have HM : t6.mem.set64 CCTL 5 (rs.headD 0) = cqRowsS s0.mem := by simp only [e6, r6, H5, cqRowStep, cqRowsS]
    all_goals have hsz : ∀ b, ((cqRowsS s0.mem).arr64 b).size = (s0.mem.arr64 b).size := by intro b; simp only [cqRowsS, cqRowStep, cqRowsM, size_copy64, L.Mem.size64_set64]
    all_goals simp only [L.reduceLoc, L.St.setLoc_mem, L.St.setLocs_mem, Cmp.eval, BinOp.eval, UInt64.toNat_zero, Nat.zero_add, decide_eq_true_eq] at d0 d1 q1 q2 d2 k1 k2 d3 k3 k4 l0 l1 q3 q4 d4 k5 k6 ⊢
    all_goals simp only [HM] at d0 d1 q1 q2 d2 k1 k2 d3 k3 k4 l0 l1 q3 q4 d4 k5 k6 ⊢
    all_goals simp only [size_copy64, L.Mem.size64_set64, cq_getElem_rdW0, cqBankSM] at d0 d1 q1 q2 d2 k1 k2 d3 k3 k4 l0 l1 q3 q4 d4 k5 k6 ⊢
    all_goals simp (disch := decide) only [arr64_copy64_ne, Mem.arr64_set64_ne] at d0 d1 q1 q2 d2 k1 k2 d3 k3 k4 l0 l1 q3 q4 d4 k5 k6 ⊢
    case vc1 | vc5 | vc9 | vc13 => simp only [LocEq]
    case vc2 | vc6 | vc10 | vc14 =>
      simp only [CqRowsSOK]
      rw [← H5, ← H4, ← H3, ← H2, ← H1]
      refine ⟨o1, o2, o3, o4, o5, o6, ?_⟩
      have := hsz CCTL
      rw [this] at d4; simp at d4; omega
    all_goals generalize cqRowsS s0.mem = M at d0 d1 q1 q2 d2 k1 k2 d3 k3 k4 l0 l1 q3 q4 d4 k5 k6 ⊢
    case vc4 | vc8 | vc12 | vc16 =>
      simp (disch := decide) only [cqTailS, cqDeclA, cqDlpA, cqMax, q1, q3, ite_true, ite_false,
        arr64_copy64_ne, Mem.arr64_set64_ne]
    all_goals obtain ⟨e8, hA⟩ := cq_toNat_18 q2
    all_goals obtain ⟨e9, hB⟩ := cq_toNat_1 q4
    all_goals simp only [e8, e9] at k1 k2 k5 k6
    all_goals exact cqTailSOK_intro (by simp only [cqDeclA, cqMax, q1, ite_true, ite_false]) (by simp only [cqDlpA, cqMax, q3, ite_true, ite_false]) d0 d1 l0 l1 hA hB k1 k2 k3 k4 k5 k6

/-- **The memory after `cq_bank_c()`**: the challenge's rows, records, firsts and pool back from
the stash at the extents `CCTL[0‥8]`. -/
def cqBankCM (m : Mem) : Mem :=
  let c := m.arr64 CCTL
  ((((((((m.copy64 EIXA 0 CEIXA 0 (rdW c 0).toNat).copy64 TIXA 0 CTIXA 0 (rdW c 1).toNat).copy64
    EIXS 0 CEIXS 0 (rdW c 2).toNat).copy64 TIXS 0 CTIXS 0 (rdW c 3).toNat).copy64
    EIXN 0 CEIXN 0 (rdW c 4).toNat).copy64 TIXN 0 CTIXN 0 (rdW c 5).toNat).copy64
    DECL 0 CDECL 0 (rdW c 6).toNat).copy64 FIRSTS 0 CFIRSTS 0 (rdW c 7).toNat).copy64
    DLP 0 CDLP 0 (rdW c 8).toNat

/-- The lookups `cq_bank_c` needs. -/
structure CqBankCProg (p : Prog) : Prop where
  ea : p.lookup "cq_back_eixa" = some (cqBackG CEIXA EIXA)
  ta : p.lookup "cq_back_tixa" = some (cqBackG CTIXA TIXA)
  es : p.lookup "cq_back_eixs" = some (cqBackG CEIXS EIXS)
  ts : p.lookup "cq_back_tixs" = some (cqBackG CTIXS TIXS)
  en : p.lookup "cq_back_eixn" = some (cqBackG CEIXN EIXN)
  tn : p.lookup "cq_back_tixn" = some (cqBackG CTIXN TIXN)

theorem cqBankC_spec (p : Prog) (hp : p.lookup "cq_bank_c" = some cqBankCL) (hP : CqBankCProg p) (n : Nat) (s₀ : St) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "cq_bank_c" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = cqBankCM s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cqBankCL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have h1 := cqBack_spec p hP.ea n
    have h2 := cqBack_spec p hP.ta n
    have h3 := cqBack_spec p hP.es n
    have h4 := cqBack_spec p hP.ts n
    have h5 := cqBack_spec p hP.en n
    have h6 := cqBack_spec p hP.tn n
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, warr,
      (h1 · ·), (h2 · ·), (h3 · ·), (h4 · ·), (h5 · ·), (h6 · ·)]
    all_goals clear h1 h2 h3 h4 h5 h6
    all_goals rename_i s0 e0 g0 rs1 t1 a1 c1 rs2 t2 a2 c2 rs3 t3 a3 c3 rs4 t4 a4 c4 rs5 t5 a5 c5 t6 a6 c6 j1 j2 j3 j4 j5
    all_goals subst e0
    case vc1 => simp only [LocEq]
    simp only [L.reduceLoc, L.St.setLoc_mem, L.St.setLocs_mem] at a1 a2 a3 a4 a5 a6 ⊢
    obtain ⟨-, -, -, e1⟩ := a1
    obtain ⟨-, -, -, e2⟩ := a2
    obtain ⟨-, -, -, e3⟩ := a3
    obtain ⟨-, -, -, e4⟩ := a4
    obtain ⟨-, -, -, e5⟩ := a5
    obtain ⟨-, -, -, e6⟩ := a6
    simp only [e6, e5, e4, e3, e2, e1, cq_getElem_rdW]
    simp (disch := decide) only [arr64_copy64_ne, cqBankCM]

end L.Checker
