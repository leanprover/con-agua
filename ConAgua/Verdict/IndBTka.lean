import ConAgua.Verdict.IndBK53
import ConAgua.Verdict.IndBTmn

/-!
# `target_k53_args`' error claim (lane `verdicts-b`, helper `fin`, fork `tka`)

`TkaE` (IndBK53.lean) proved: the error model of `target_k53_args`, its claim along `tkaW_okC`'s case
chain; the callees outside the verdict closure claim nothing, `target_class_match` is `tcm_claimA`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The error model (by hand: the generator's step `grind` fails) -/

def tkaE.k8 : Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r, m) => .ok ([r.headD 0], m)

def tkaE.k7 (p : Prog) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r, m) =>
    if r.headD 0 = 0 then .ok ([0], m)
    else tkaE.k8 (callE p n "target_class_match" [vis, q, fto, ftl, rdW (m.arr64 IW) (Mc + 11),
      rdW (m.arr64 IW) (Mc + 12), rdW (m.arr64 IW) (Mc + 1), rdW (m.arr64 IW) (Mc + 2),
      rdW (m.arr64 IW) (Mc + 3), usp, lao, lpl] m)

def tkaE.k6 (p : Prog) (n : Nat) (vis q fto ftl Mc usp lao lpl app : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (rn, m) => tkaE.k7 p n vis q fto ftl Mc usp lao lpl
      (callE p n "nest_occ" [rn.headD 0, rn.tail.headD 0, 0, 0, app] m)

def tkaE.k5 (p : Prog) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (ra, m) => tkaE.k6 p n vis q fto ftl Mc usp lao lpl (ra.headD 0)
      (callE p n "block_shape_member_names" [q] m)

def tkaE.k4 (p : Prog) (n : Nat) (vis q fto ftl Mc usp lao lpl : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r, m) =>
    if 4294967296 ≤ r.headD 0 then .error (.abort 0)
    else tkaE.k5 p n vis q fto ftl Mc usp lao lpl (callE p n "mk_app_n_f" [r.headD 0, lao, lpl] m)

def tkaE.k3 (p : Prog) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r, m) =>
    if r.headD 0 = 0 then .ok ([0], m)
    else tkaE.k4 p n vis q fto ftl Mc usp lao (if lal < K then lal else K)
      (callE p n "intern_const" [ip, usp] m)

def tkaE.k2 (p : Prog) (n : Nat) (vis q fto ftl Mc ip usp lao lal K : Word) (r1 : List Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r2, m) => tkaE.k3 p n vis q fto ftl Mc ip usp lao lal K
      (callE p n "sl_eq" [r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0] m)

def tkaE.k1 (p : Prog) (n : Nat) (vis q fto ftl Mc ip usp lao lal mao mal K : Word) :
    Except Err (List Word × Mem) → Except Err (List Word × Mem)
  | .error ε => .error ε
  | .ok (r1, m) => tkaE.k2 p n vis q fto ftl Mc ip usp lao lal K r1
      (callE p n "erase_each" [if mal < K then mao else mao + K, if mal < K then 0 else mal - K] m)

/-- **The error model of `target_k53_args`** (`tkaW`'s shape, every callee through `callE`). -/
def tkaE (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Except Err (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => .error .outOfFuel
  | n + 1, m, vis, q, fto, ftl, Mc, ip, usp, lao, lal, mao, mal =>
    tkaE.k1 p n vis q fto ftl Mc ip usp lao lal mao mal (rdW (m.arr64 IW) (Mc + 4))
      (callE p n "erase_each" [if lal < rdW (m.arr64 IW) (Mc + 4) then lao else lao + rdW (m.arr64 IW) (Mc + 4),
        if lal < rdW (m.arr64 IW) (Mc + 4) then 0 else lal - rdW (m.arr64 IW) (Mc + 4)] m)

theorem tka_ite_neg {α : Sort _} {x K : Word} {a b : α} (h : K ≤ x) : (if x < K then a else b) = b :=
  if_neg (UInt64.not_lt.mpr h)

theorem tka_ite_pos {α : Sort _} {x K : Word} {a b : α} (h : x < K) : (if x < K then a else b) = a :=
  if_pos h

set_option maxHeartbeats 8000000 in
theorem tkaE_spec (p : Prog) (hf : p.lookup "target_k53_args" = some targetK53Args) (n : Nat) (s₀ : St)
    (vis q fto ftl Mc ip usp lao lal mao mal : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53_args" [vis, q, fto, ftl, Mc, ip, usp, lao, lal, mao, mal]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      tkaE p n s₀.mem vis q fto ftl Mc ip usp lao lal mao mal = .error ε⦄ := by
  cases n with
  | zero =>
    rw [invoke_eq _ hf]; simp only [callFn, targetK53Args]
    vcgen [exec] <;> grind
  | succ n =>
    rw [invoke_eq _ hf]
    simp only [callFn, targetK53Args]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_specE,
      callE_spec p n "erase_each", callE_spec p n "sl_eq", callE_spec p n "intern_const",
      callE_spec p n "mk_app_n_f", callE_spec p n "block_shape_member_names", callE_spec p n "nest_occ",
      callE_spec p n "target_class_match"]
    all_goals (try simp only [LocEq] at *)
    all_goals (try simp only [*, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
        List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, Locals.init_nil,
        Locals.init_cons_zero, Locals.init_cons_succ, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
        loc_init9, loc_init10, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
        reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals (try simp_all [tka_ite_neg, tka_ite_pos, tkaE, tkaE.k1, tkaE.k2, tkaE.k3, tkaE.k4, tkaE.k5, tkaE.k6, tkaE.k7, tkaE.k8])
    all_goals grind [lang_grind, arena_grind, tkaE, tkaE.k1, tkaE.k2, tkaE.k3, tkaE.k4, tkaE.k5, tkaE.k6,
      tkaE.k7, tkaE.k8]

/-! ## The claim -/

section sims
variable {p : Prog} (hq : KnotStageProg p) {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hnv hcE in
/-- **`target_k53_args`' error claim** (`TkaE`, every `dn vis fe`; `tkaW_okC`'s case chain): the
callees outside the verdict closure claim nothing, the capacity abort is class `0`, a failing
`target_class_match` is `tcm_claimA`'s. -/
theorem tkaE_of (L : K53Look p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    TkaE p dn vis fe env := by
  intro n hn s₀ a q fto ftl Mc ip usp lao lal mao mal bs formerTys TM la ma pP formerTysP laP maP McP
    I'P us'P hC hA hbs hft hftb hMc hip hus hla hma hP hsh hftP hMcP hipP husP hlaP hmaP hformer hMs
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (tkaE_spec p L.tka n s₀ vis q fto ftl Mc ip usp lao lal mao mal) hc
    (Err.code_ne_of_cls hk0)
  have hS := hC.stage
  obtain ⟨-, hMlv, hMds, hMnpc, -, -, -, -, hMpf⟩ := ConRon.Bridge.Inductives.dMajor_inv hMcP
  obtain _ | n := n
  · simp only [tkaE] at hW; cases hW; exact absurd rfl hk0
  simp only [tkaE] at hW
  have hsz := hS.2.2.2.1
  obtain ⟨hlvH, hlvD, hdsS, hnP, hpfS, hMt⟩ := tmFields hMc hsz
  have hMk : ∀ k : Nat, k ≤ 12 → (Mc + UInt64.ofNat k).toNat < iwTop s₀.mem := fun k hk => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by
      have := (rdW (s₀.mem.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hMt; omega)]; omega
  generalize hK : rdW (s₀.mem.arr64 IW) (Mc + 4) = K at hW hnP
  -- `erase_each` of the leaf's indices
  cases h1 : callE p n "erase_each" [if lal < K then lao else lao + K, if lal < K then 0 else lal - K]
      s₀.mem with
  | error e1 =>
    rw [h1] at hW; simp only [tkaE.k1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1] at hW; simp only [tkaE.k1] at hW
  obtain ⟨s1, hs1, -, h1'⟩ := triple_of_callE (ee_spec p L n ⟨s₀.mem, Locals.init []⟩ _ _) h1
  rw [hs1] at h1'
  dsimp only at h1'
  obtain ⟨le, a1, run1, hd1, hb1, hS1, hg1, hP1⟩ := eeW_ok dn fe vis n h1' hS hla.drop hP
  have hA1 := eeW_afr n h1' hA
  -- `erase_each` of the major's indices
  cases h2 : callE p n "erase_each" [if mal < K then mao else mao + K, if mal < K then 0 else mal - K]
      m1 with
  | error e2 =>
    rw [h2] at hW; simp only [tkaE.k2] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW; simp only [tkaE.k2] at hW
  obtain ⟨s2, hs2, -, h2'⟩ := triple_of_callE (ee_spec p L n ⟨m1, Locals.init []⟩ _ _) h2
  rw [hs2] at h2'
  dsimp only at h2'
  obtain ⟨me, a2, run2, hd2, hb2, hS2, hg2, hP2⟩ := eeW_ok dn fe vis n h2' hS1 (hma.grow hg1).drop hP1
  have hA2 := eeW_afr n h2' hA1
  -- `sl_eq`
  cases h3 : callE p n "sl_eq" [r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0] m2 with
  | error e3 =>
    rw [h3] at hW; simp only [tkaE.k3] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3'⟩ := q3
  rw [h3] at hW; simp only [tkaE.k3] at hW
  obtain ⟨s3, hs3, -, hm3, h3'⟩ := triple_of_callE (slEq_spec p L.eq n ⟨m2, Locals.init []⟩ _ _ _ _) h3
  have hm3' : m3' = m2 := by rw [← hs3]; exact hm3
  rw [hm3'] at hW h3
  dsimp only at h3'
  have he := eqW_dec h3' (by rw [decHL_grow hg2 hb1]; exact hd1) (hS2.lt64 (by have := hg2.1; omega)) hd2
    (hS2.lt64 hb2)
  have hg12 := hg1.trans hg2
  rw [hnP] at run1 run2
  obtain ⟨q1, -⟩ := eraseAll_spec (la.drop TM.nPc) (laP.drop TM.nPc) a a1 le hC.check.state
    hC.check.pins ⟨trivial, ConRon.Bridge.Inductives.denoteEList_drop hlaP TM.nPc⟩ run1
  have hC1 := hC.of_pstep hS1 hA1 q1
  obtain ⟨q2, -⟩ := eraseAll_spec (ma.drop TM.nPc) (maP.drop TM.nPc) a1 a2 me hC1.check.state
    hC1.check.pins ⟨trivial, ConRon.Bridge.Inductives.denoteEList_drop
      (denoteEList_ext q1.ext _ _ hmaP) TM.nPc⟩ run2
  have hC2 := hC1.of_pstep hS2 hA2 q2
  have q12 := q1.trans q2
  by_cases he0 : r3.headD 0 = 0
  · rw [if_pos he0] at hW; cases hW
  rw [if_neg he0] at hW
  have heq : le = me := by
    by_cases hq' : le = me
    · exact hq'
    · rw [if_neg hq'] at he; exact absurd he he0
  subst heq
  -- `intern_const`
  cases h4 : callE p n "intern_const" [ip, usp] m2 with
  | error e4 =>
    rw [h4] at hW; simp only [tkaE.k4] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m3⟩ := q4
  rw [h4] at hW; simp only [tkaE.k4] at hW
  obtain ⟨s4, hs4, -, h4'⟩ := triple_of_callE
    (internConst_spec (p := p) L.cf L.cp L.ic n ⟨m2, Locals.init []⟩ ip usp) h4
  rw [hs4] at h4'
  dsimp only at h4'
  generalize hhd' : r4.headD 0 = hd at hW h4'
  obtain ⟨a3, run3, hS3, hg3⟩ := internConst_stage hS2 ip usp hip hus h4'
  have hA3 := ceinternW_afr h4' hA2
  obtain ⟨q3, hhdP⟩ := ConRon.Bridge.Inductives.internConstE_run hC2.check.state
    (ConRon.Bridge.denoteN_ext hipP q12.ext) (ConRon.Bridge.denoteLs_ext husP q12.ext) run3
  have hC3 := hC2.of_pstep hS3 hA3 q3
  have q13 := q12.trans q3
  by_cases hb4 : 4294967296 ≤ hd
  · rw [if_pos hb4] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hb4] at hW
  have hhd : H hd := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb4; simp at hb4; omega
  have hP3 : RcMR m3 := hP2.fr (ceinternW_mfr h4')
  have hg03 := hg12.trans hg3
  have hlp := (hla.grow hg03).take (k := K)
  rw [hnP] at hlp
  generalize hL : (if lal < K then lal else K) = lpl at hW hlp
  -- `mk_app_n_f`
  cases h5 : callE p n "mk_app_n_f" [hd, lao, lpl] m3 with
  | error e5 =>
    rw [h5] at hW; simp only [tkaE.k5] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨ra, m4⟩ := q5
  rw [h5] at hW; simp only [tkaE.k5] at hW
  obtain ⟨s5, hs5, -, h5'⟩ := triple_of_callE (mknF_spec p L.ad n ⟨m3, Locals.init []⟩ _) h5
  rw [hs5] at h5'
  dsimp only at h5'
  obtain ⟨app, a4, run4, hS4, hg4, happH, happD⟩ := mknF_ok dn vis fe hd lao lpl hhd _ m3 m4 a3 ra h5'
    ⟨hS3, hlp.1⟩
  have hA4 := mknF_afr h5' hA3
  have hlpP := denoteEList_ext q13.ext _ _ (ConRon.Bridge.Inductives.denoteEList_take hlaP TM.nPc)
  obtain ⟨q4, -⟩ := ConRon.Bridge.Inductives.mkAppN_run (la.take TM.nPc) (laP.take TM.nPc)
    hC3.check.state hhdP hlpP run4
  have hC4 := hC3.of_pstep hS4 hA4 q4
  have q14 := q13.trans q4
  have hP4 : RcMR m4 := hP3.fr (MFr.ofMknF h5')
  have hg04 := hg03.trans hg4
  -- `block_shape_member_names`
  cases h6 : callE p n "block_shape_member_names" [q] m4 with
  | error e6 =>
    rw [h6] at hW; simp only [tkaE.k6] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6
  | ok q6 =>
  obtain ⟨rn, m5⟩ := q6
  rw [h6] at hW; simp only [tkaE.k6] at hW
  obtain ⟨s6, hs6, -, h6'⟩ := triple_of_callE (blockShapeMemberNames_spec p L.tmn.tcm.ha L.tmn.tcm.mnc
    L.tmn.tcm.mn n ⟨m4, Locals.init []⟩ q) h6
  rw [hs6] at h6'
  dsimp only at h6'
  have hbs4 := hbs.grow hg04
  obtain ⟨hS5, hg5, -, hdn, htn⟩ := memberNamesW_stage h6' hS4 hbs4
  have hf5 := (memberNamesW_dec h6' hS4.2.2.2.1 hS4.2.2.2.2.2 hbs4.dec
    (by have := hbs4.ptop; have := hS4.lt64 (Nat.le_refl _); omega) hbs4.2.1 hbs4.2.2).2.2.2.1
  have hP5 : RcMR m5 := hP4.fr (MFr.of_iw hf5)
  have hA5 := AFr.iw hf5 hA4
  have hC5 := hC4.of_pstep hS5 hA5 (PStep.refl hC4.check.state)
  -- `nest_occ`
  cases h7 : callE p n "nest_occ" [rn.headD 0, rn.tail.headD 0, 0, 0, ra.headD 0] m5 with
  | error e7 =>
    rw [h7] at hW; simp only [tkaE.k7] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h7
  | ok q7 =>
  obtain ⟨r7, m6⟩ := q7
  rw [h7] at hW; simp only [tkaE.k7] at hW
  obtain ⟨s7, hs7, -, h7'⟩ := triple_of_callE (noF_spec p L n ⟨m5, Locals.init []⟩ _ _ _ _ _) h7
  rw [hs7] at h7'
  dsimp only at h7'
  generalize hocc : r7.headD 0 = occ at hW h7'
  obtain ⟨b, run6, hb6, hS6, hg6, hP6⟩ := noF_ok dn fe vis n h7' hS5 happH hdn (Nat.le_of_eq htn) hP5
  have hA6 := noF_afr h7' hA5
  have hC6 := hC5.of_pstep hS6 hA6 (PStep.refl hC5.check.state)
  have hg06 := (hg04.trans hg5).trans hg6
  have hdecApp : decE (ra.headD 0) = app := happD
  have hrun4 : (mkAppN (decE hd) (la.take TM.nPc)).run a3 = .ok (decE (ra.headD 0), a4) := by
    rw [hdecApp]; exact run4
  by_cases ho : occ = 0
  · rw [if_pos ho] at hW; cases hW
  rw [if_neg ho] at hW
  have hb1 : b = true := by rw [← hb6]; simpa using ho
  subst hb1
  have hMk6 : ∀ k : Nat, k ≤ 12 → rdW (m6.arr64 IW) (Mc + UInt64.ofNat k) =
      rdW (s₀.mem.arr64 IW) (Mc + UInt64.ofNat k) :=
    fun k hk => rdW_grow hg06 (hMk k hk)
  have e11 := hMk6 11 (by omega); have e12 := hMk6 12 (by omega); have e1 := hMk6 1 (by omega)
  have e2 := hMk6 2 (by omega); have e3 := hMk6 3 (by omega)
  simp only [show UInt64.ofNat 11 = (11 : Word) from rfl, show UInt64.ofNat 12 = (12 : Word) from rfl,
    show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl] at e11 e12 e1 e2 e3
  rw [e11, e12, e1, e2, e3] at hW
  -- `target_class_match`
  cases h8 : callE p n "target_class_match" [vis, q, fto, ftl, rdW (s₀.mem.arr64 IW) (Mc + 11),
      rdW (s₀.mem.arr64 IW) (Mc + 12), rdW (s₀.mem.arr64 IW) (Mc + 1), rdW (s₀.mem.arr64 IW) (Mc + 2),
      rdW (s₀.mem.arr64 IW) (Mc + 3), usp, lao, lpl] m6 with
  | ok q8 =>
    rw [h8] at hW; simp only [tkaE.k8] at hW; cases hW
  | error e8 =>
  rw [h8] at hW; simp only [tkaE.k8] at hW; cases hW
  have hcl := CoreSpecE.of_callE (tcm_claimA hq henv hnv hcE L.tmn.tcm n (by omega) ⟨m6, Locals.init []⟩ a4
    q fto ftl _ _ _ _ _ usp lao lpl bs formerTys _ _ _ hC6 hA6
    (hbs.grow hg06) hlvH hus
    (by rw [decHL_grow hg06 hftb]; exact hft) (by have := hg06.1; dsimp only; omega) (hpfS.grow hg06) (hdsS.grow hg06)
    (hlp.grow ((hg4.trans hg5).trans hg6)) hP6
    (ConRon.Bridge.Inductives.dShape_ext q14.ext _ _ hsh) (denoteEList_ext q14.ext _ _ hftP)
    (denoteEList_ext q14.ext _ _ hMpf) (by rw [hlvD]; exact ConRon.Bridge.denoteLs_ext hMlv q14.ext)
    (denoteEList_ext q14.ext _ _ hMds) (ConRon.Bridge.denoteLs_ext husP q14.ext)
    (denoteEList_ext q4.ext _ _ hlpP) hformer hMs.1) h8
  rw [hlvD] at hcl
  intro hk
  obtain ⟨ce, hce, hcls⟩ := hcl hk
  refine ⟨ce, ?_, hcls⟩
  simp only [tkArgs, StateT.run_bind, run1, except_ok_bind, run2, bne_self_eq_false, Bool.false_eq_true,
    if_false, ConRon.Arena.internConstE, run3, hrun4, run6, if_true]
  exact hce

end sims

end L.Ind
