import ConAgua.Arena.IndInstallSpec33

/-!
# Refinements of `IndInstall`, part 34 (lane `indproofs3`, helper `pos`): `checkBlockPositivity`

`check_block_positivity(vis, p, cvTas, ctorsAs)`: the walk's context (`block_nest_ctx`),
`nest_uniform`, the root frame from the empty state (`check_block_positivity_init`, `nest_root`),
the propositional bit (`pin_word(53)`, `lvl_eq_true`), the fields' universes at the holes
(`check_abs_ctor_sorts_all`), then the kinds (`outs` itself, `decKSS`) and the normal forms
(`check_block_positivity_nfs`).

Hypotheses beyond the stage relation and the inputs' decodings, and who discharges them:
* `PosMR s₀.mem` (the walk memos well formed now): the caller (`check_block_pass`), from its own
  pre; it is returned for the memory after, for `nest_seeds`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of `check_block_positivity`. -/
structure PosBlkProg (p : Prog) : Prop where
  nck : NckProg p
  nh : NhLook p
  bnc : p.lookup "block_nest_ctx" = some blockNestCtx
  nu : NuLook p
  nuCs : p.lookup "nest_uniform_cs" = some nestUniformCsL
  nuP : p.lookup "nest_uniform" = some nestUniformL
  init : p.lookup "check_block_positivity_init" = some checkBlockPositivityInit
  rs : RsLook p
  pin : p.lookup "pin_word" = some pinWordL
  eqt : p.lookup "lvl_eq_true" = some lvlEqTrue
  abs : AbsProg p
  nfs : NfsProg p
  cbp : p.lookup "check_block_positivity" = some checkBlockPositivity

/-! ## The model -/

def cbpK8 (oO oL ns : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([oO, oL, r.headD 0, r.tail.headD 0, ns], m)
def cbpK7 (p : Prog) (n : Nat) (oO oL ns : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => cbpK8 oO oL ns (callW p n "check_block_positivity_nfs" [oO, oL] m)
def cbpK6 (p : Prog) (n : Nat) (vis ctx caO caL oO oL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbpK7 p n oO oL ns
      (callW p n "check_abs_ctor_sorts_all" [vis, ctx, r.headD 0, caO, caL, oO, oL] m)
def cbpK5 (p : Prog) (n : Nat) (vis ctx caO caL oO oL ns : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbpK6 p n vis ctx caO caL oO oL ns
      (callW p n "lvl_eq_true" [rdW (m.arr64 IW) (ctx + 9), r.headD 0] m)
def cbpK4 (p : Prog) (n : Nat) (vis ctx caO caL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbpK5 p n vis ctx caO caL (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0)
      (callW p n "pin_word" [53] m)
def cbposK3 (p : Prog) (n : Nat) (vis ctx hO hL caO caL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbpK4 p n vis ctx caO caL
      (callW p n "nest_root" [vis, ctx, hO, hL, caO, caL, r.headD 0, 0, 0] m)
def cbposK2 (p : Prog) (n : Nat) (vis ctx hO hL caO caL : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => cbposK3 p n vis ctx hO hL caO caL (callW p n "check_block_positivity_init" [] m)
def cbposK1 (p : Prog) (n : Nat) (vis caO caL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbposK2 p n vis (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) caO caL
      (callW p n "nest_uniform" [r.headD 0, caO, caL] m)

/-- **The model of `check_block_positivity(vis, p, cvO, cvL, caO, caL)`** (body fuel `n`). -/
def cbposW (p : Prog) (n : Nat) (m : Mem) (vis q cvO cvL caO caL : Word) : Option (List Word × Mem) :=
  cbposK1 p n vis caO caL (callW p n "block_nest_ctx" [vis, q, cvO, cvL] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis q ctx hO hL caO caL oO oL ns : Word) (r : List Word)
theorem cbpK8_some : cbpK8 oO oL ns (some (r, m)) = some ([oO, oL, r.headD 0, r.tail.headD 0, ns], m) := rfl
theorem cbpK7_some : cbpK7 p n oO oL ns (some (r, m)) =
    cbpK8 oO oL ns (callW p n "check_block_positivity_nfs" [oO, oL] m) := rfl
theorem cbpK6_some : cbpK6 p n vis ctx caO caL oO oL ns (some (r, m)) = cbpK7 p n oO oL ns
    (callW p n "check_abs_ctor_sorts_all" [vis, ctx, r.headD 0, caO, caL, oO, oL] m) := rfl
theorem cbpK5_some : cbpK5 p n vis ctx caO caL oO oL ns (some (r, m)) = cbpK6 p n vis ctx caO caL oO oL ns
    (callW p n "lvl_eq_true" [rdW (m.arr64 IW) (ctx + 9), r.headD 0] m) := rfl
theorem cbpK4_some : cbpK4 p n vis ctx caO caL (some (r, m)) = cbpK5 p n vis ctx caO caL (r.headD 0)
    (r.tail.headD 0) (r.tail.tail.headD 0) (callW p n "pin_word" [53] m) := rfl
theorem cbposK3_some : cbposK3 p n vis ctx hO hL caO caL (some (r, m)) = cbpK4 p n vis ctx caO caL
    (callW p n "nest_root" [vis, ctx, hO, hL, caO, caL, r.headD 0, 0, 0] m) := rfl
theorem cbposK2_some : cbposK2 p n vis ctx hO hL caO caL (some (r, m)) =
    cbposK3 p n vis ctx hO hL caO caL (callW p n "check_block_positivity_init" [] m) := rfl
theorem cbposK1_some : cbposK1 p n vis caO caL (some (r, m)) = cbposK2 p n vis (r.headD 0) (r.tail.headD 0)
    (r.tail.tail.headD 0) caO caL (callW p n "nest_uniform" [r.headD 0, caO, caL] m) := rfl
end arms
attribute [ind_grind] cbpK8_some cbpK7_some cbpK6_some cbpK5_some cbpK4_some cbposK3_some cbposK2_some cbposK1_some

set_option maxHeartbeats 1600000 in
theorem cbpos_spec (p : Prog) (hp : p.lookup "check_block_positivity" = some checkBlockPositivity) (n : Nat)
    (s₀ : St) (vis q cvO cvL caO caL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_positivity" [vis, q, cvO, cvL, caO, caL]
    ⦃fun r s' => LocEq s' s₀ ∧ cbposW p n s₀.mem vis q cvO cvL caO caL = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockPositivity]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "block_nest_ctx", callW_spec p n "nest_uniform",
      callW_spec p n "check_block_positivity_init", callW_spec p n "nest_root", callW_spec p n "pin_word",
      callW_spec p n "lvl_eq_true", callW_spec p n "check_abs_ctor_sorts_all",
      callW_spec p n "check_block_positivity_nfs"] <;>
    finish (gen := 40) (instances := 20000) [cbposW, rdW_eq]

/-! ## The fresh `NestState` -/

theorem pos3_init {p : Prog} (hP : PosBlkProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {m m' : Mem} {r : List Word}
    (h : callW p n "check_block_positivity_init" [] m = some (r, m')) (hS : StageR dn vis fe m a) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧ NSB m' (r.headD 0) {} := by
  obtain ⟨s', rfl, -, hm, hr, hroom⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkBlockPositivityInit_spec p hP.nfs.alloc hP.init n _ hS.2.2.2.1) h
  simp only at hm hr hroom
  obtain ⟨hget, hg, hf, htop⟩ := rec6Mem_post m 0 0 0 0 0 0 hS.2.2.2.2.2 hroom hS.2.2.2.1
  rw [← hm] at hget hg hf htop
  have hT' : iwTop s'.mem = iwTop m + 6 := by
    have hl : (rdW (m.arr64 CTL) 200).toNat + 6 < 2 ^ 64 := Nat.lt_of_le_of_lt hroom hS.2.2.2.1
    simp only [iwTop, htop, UInt64.toNat_add]; simp; omega
  have hroom' : iwTop m + 6 ≤ (m.arr64 IW).size := hroom
  refine ⟨stage_frame_iw hS hf (by omega), hg, MFr.of_iw hf, ?_⟩
  rw [hr]
  have hsz' : iwTop s'.mem < 2 ^ 64 := Nat.lt_of_le_of_lt (stage_frame_iw hS hf (by omega)).2.1
    (stage_frame_iw hS hf (by omega)).2.2.2.1
  have := nsb_rec6 (m' := s'.mem) (q := rdW (m.arr64 CTL) 200) (kO := 0) (kL := 0) (aO := 0) (aL := 0)
    (nO := 0) (nL := 0) (keys := []) (act := []) (nfs := []) (by simp only [iwTop] at *; omega) hsz'
    (fun j hj => hget j hj) (by simp [KsB, DecB, decPL]) (by simp) (by simp [KsB, DecB, decPL]) (by simp)
    (by simp [NfsB, DecB, decPL]) (by simp)
  exact this

/-! ## The relation -/

/-- The callees of `check_block_positivity` outside the `abstract1` cascade, which keep its memo
(`AbsKeep`, a program fact). -/
def posKeepCallees : List FnName :=
  ["block_nest_ctx", "nest_uniform", "check_block_positivity_init", "check_abs_ctor_sorts_all",
    "check_block_positivity_nfs"]

/-- **`check_block_positivity`'s model refines `checkBlockPositivity`.** -/
theorem cbposW_ok {p : Prog} (hP : PosBlkProg p) (n : Nat)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {q cvO cvL caO caL : Word} {P : BlockParts} {cvTas : List IConstantVal}
    {css : List (List (IConstantVal × Nat))} {r : List Word}
    (h : cbposW p (n + 2) m vis q cvO cvL caO caL = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : DecB (fun m => decBS m q.toNat) m P.shape) (hsrc : ShapeSrc m q)
    (hcv : PSlR decCVp cvTas cvO cvL m) (hcss : PSlR decCNSB css caO caL m) (hPM : PosMR m) (hA : AbsOK m)
    (hk : ∀ f ∈ posKeepCallees, AbsKeep p f) :
    ∃ x a', (ConRon.Arena.checkBlockPositivity V fe P cvTas css).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m' ∧ AbsOK m' ∧
      PSlR decKSS x.1 (r.headD 0) (r.tail.headD 0) m' ∧
      PSlR decNFS x.2.1 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m' ∧
      NSB m' ((r.drop 4).headD 0) x.2.2 := by
  unfold cbposW at h
  -- the walk's context
  cases h1 : callW p (n + 2) "block_nest_ctx" [vis, q, cvO, cvL] m with
  | none => rw [h1] at h; simp [cbposK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1, cbposK1_some] at h
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (bnc_spec p hP.nck hP.nh hP.bnc n _ vis q cvO cvL) h1
  obtain ⟨⟨c, holes⟩, a1, hrun1, hc1, hho1, hhob1, hS1, hg1, hin1, hsl1, hhi1, hpn1⟩ :=
    bncW_sim n hS hq hsrc hcv r1 s1.mem hW1
  have hP1 : PosMR s1.mem := hPM.fr (bncW_mfr hW1)
  have hA1 : AbsOK s1.mem := hk _ (by simp [posKeepCallees]) _ _ _ _ _ h1 hA
  have hU1 : UCtx dn vis fe s1.mem (r1.headD 0) c := ⟨hc1.get (decCtx_mono _), hin1, hsl1⟩
  obtain ⟨hlen, hcb1, hcss1⟩ := pos3_cssAt (hcss.grow decCNSB_mono hg1)
  -- `nest_uniform`
  cases h2 : callW p (n + 2) "nest_uniform" [r1.headD 0, caO, caL] s1.mem with
  | none => rw [h2] at h; simp [cbposK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, cbposK2_some] at h
  obtain ⟨s2, rfl, -, hok2, hS2, hg2, hP2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (nestUniform_refines p hP.nu hP.nuCs hP.nuP (n + 2) _ a1 dn fe vis (r1.headD 0) caO caL c css hS1 hU1
      hhi1 hlen hcss1 hP1) h2
  have hrun2 := partsRunOfOk hok2
  have hA2 : AbsOK s2.mem := hk _ (by simp [posKeepCallees]) _ _ _ _ _ h2 hA1
  -- the empty state
  cases h3 : callW p (n + 2) "check_block_positivity_init" [] s2.mem with
  | none => rw [h3] at h; simp [cbposK3] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3, cbposK3_some] at h
  obtain ⟨hS3, hg3, hf3, hns3⟩ := pos3_init hP h3 hS2
  have hA3 : AbsOK m3 := hk _ (by simp [posKeepCallees]) _ _ _ _ _ h3 hA2
  have hg13 := hg2.trans hg3
  -- the root frame
  cases h4 : callW p (n + 2) "nest_root" [vis, r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, caO, caL,
      r3.headD 0, 0, 0] m3 with
  | none => rw [h4] at h; simp [cbpK4] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4, cbpK4_some] at h
  obtain ⟨s4, rfl, -, ⟨outs, ns⟩, a4, hrun4, hS4, hg4, hO4, hOb4, hns4, hP4, hA4⟩ :=
    triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (nestRoot_refines hP.rs (n + 2) dn vis fe _ _ (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0)
      caO caL (r3.headD 0) 0 0 c holes css {} [] hS3 (hU1.grow hg13) hhi1 hpn1
      (by rw [decHL_grow3 hg13 hhob1]; exact hho1) (Nat.le_trans hhob1 hg13.1) hlen
      (Nat.le_trans hcb1 hg13.1) (hcss1.grow hg13) hns3 (by simp [RootOutsB, DecB, decPL]) (by simp)
      (hP2.fr hf3) hA3) h4
  have hg14 := hg13.trans hg4
  -- `pin_word(53)`
  cases h5 : callW p (n + 2) "pin_word" [53] s4.mem with
  | none => rw [h5] at h; simp [cbpK5] at h
  | some x5 =>
  obtain ⟨r5, m5⟩ := x5
  rw [h5, cbpK5_some] at h
  obtain ⟨s5, rfl, -, hm5, hz5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (pinWord_specV p hP.pin (n + 2) _ 53) h5
  simp only at hm5 hz5
  rw [hm5] at h
  obtain ⟨hrunz, hzH⟩ := pinZero_stage hS4 hz5
  -- `lvl_eq_true`
  obtain ⟨huH, hue⟩ := installCtxWord9 (hc1.grow (decCtx_mono _) hg14) hS4.2.2.2.1
  cases h6 : callW p (n + 2) "lvl_eq_true" [rdW (s4.mem.arr64 IW) (r1.headD 0 + 9), r5.headD 0] s4.mem with
  | none => rw [h6] at h; simp [cbpK6] at h
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6, cbpK6_some] at h
  obtain ⟨s6, rfl, -, he6⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (eqTrue_specW p hP.eqt (n + 2) _ _ _) h6
  simp only at he6
  unfold eqTrueW at he6
  cases hs6 : stubM "lvl_eq_c" s4.mem [rdW (s4.mem.arr64 IW) (r1.headD 0 + 9), r5.headD 0] with
  | none => rw [hs6] at he6; simp [eqTrueK] at he6
  | some y6 =>
  obtain ⟨r6', m6'⟩ := y6
  rw [hs6, eqTrueK_some] at he6
  simp only [Option.some.injEq, Prod.mk.injEq] at he6
  obtain ⟨hr6, hm6⟩ := he6
  subst hm6
  obtain ⟨y, a6, hrun6, hS6, hg6, hy6⟩ := lvlEqStub_spec dn vis fe _ _ huH hzH s4.mem s6.mem a4 r6' hs6 hS4
  have hP6 : PosMR s6.mem := hP4.fr (MFr.ofStub hs6)
  have hA6 : AbsOK s6.mem := stub_afr hs6 (by decide) hA4
  have hb6 : (r6.headD 0 != 0) = (y == some true) := by
    rw [← hr6]
    simp only [decLvlEq] at hy6
    rcases y with _ | _ | _ <;> simp_all
  -- the fields' universes at the holes
  have hg16 := hg14.trans hg6
  cases h7 : callW p (n + 2) "check_abs_ctor_sorts_all" [vis, r1.headD 0, r6.headD 0, caO, caL, r4.headD 0,
      r4.tail.headD 0] s6.mem with
  | none => rw [h7] at h; simp [cbpK7] at h
  | some x7 =>
  obtain ⟨r7, m7⟩ := x7
  rw [h7, cbpK7_some] at h
  obtain ⟨s7, rfl, -, hW7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (iaa_spec p hP.abs.all (n + 2) _ _ _ _ _ _ _ _) h7
  have hP7 : PosMR s7.mem := hP6.fr (iaaW_mfr hP.abs _ hW7)
  have hA7 : AbsOK s7.mem := hk _ (by simp [posKeepCallees]) _ _ _ _ _ h7 hA6
  have hOb6 : (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop s6.mem := Nat.le_trans hOb4 hg6.1
  obtain ⟨u7, a7, hrun7, hS7, hg7⟩ := iaaW_sim hP.abs dn vis fe (r1.headD 0) (r6.headD 0) c (y == some true) hb6
    hhi1 (n + 2) s6.mem a6 caO caL (r4.headD 0) (r4.tail.headD 0) css outs hS6 (hc1.grow (decCtx_mono _) hg16)
    ((pos3_cns hcss).grow decCNS_mono (hg1.trans hg16)) ⟨hO4.grow hg6, Or.inr hOb6⟩ r7 s7.mem hW7
  -- the normal forms
  cases h8 : callW p (n + 2) "check_block_positivity_nfs" [r4.headD 0, r4.tail.headD 0] s7.mem with
  | none => rw [h8] at h; simp [cbpK8] at h
  | some x8 =>
  obtain ⟨r8, m8⟩ := x8
  rw [h8, cbpK8_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s8, rfl, -, hW8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (pnf_spec p hP.nfs.nfs (n + 2) _ _ _) h8
  have hOb7 : (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop s7.mem := Nat.le_trans hOb6 hg7.1
  obtain ⟨hS8, hg8, hf8, hd8⟩ := pnfW_ok hP.nfs (n + 2) _ _ a7 _ _ outs r8 hW8 hS7
    ⟨(hO4.grow (hg6.trans hg7)), hOb7⟩
  have hg48 := (hg6.trans hg7).trans hg8
  refine ⟨(outs.map (·.map (·.1)), outs.map (·.map (·.2)), ns), a7, ?_, hS8, (hg1.trans hg14).trans hg48,
    hP7.fr hf8, hk _ (by simp [posKeepCallees]) _ _ _ _ _ h8 hA7, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [ConRon.Arena.checkBlockPositivity, StateT.run_bind, hrun1, except_ok_bind]
    rw [hrun2]; simp only [except_ok_bind]
    rw [hrun4]; simp only [except_ok_bind]
    rw [hrunz]; simp only [except_ok_bind]
    rw [← hue, hrun6]; simp only [except_ok_bind]
    rw [hrun7]; simp only [except_ok_bind]
    rfl
  · exact pos3_kinds (hO4.grow hg48)
  · simp only [List.headD_cons, List.tail_cons]; exact Nat.le_trans hOb7 hg8.1
  · simpa using hd8
  · simpa using hns4.grow hg48 (Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1)

/-! ## Census -/

/-- **`check_block_positivity` refines `checkBlockPositivity`** (through the stubs of its callees:
`open_pis_at_fvars_f`, `intern_ls_iw`, `inst_pis_with`'s, `lvl_eq_c`, `all_level_params_defined`, the
fields' sorts' core stubs, and `nest_root`'s). The shape record and the formers decoded below the tops,
the members' constructors with their slices' bounds (`decCNSB`, from `checkBlockCtors_refines`), the
walk memos well formed (`PosMR`). After: the stage relation at the twin's state, the pools grown, the walk memos
still well formed, the kinds (`decKSS`, the `outs` slice itself), the normal forms (`decNFS`, fresh)
and the walk's state (`NSB`, `nest_root`'s). -/
@[refines ConRon.Arena.checkBlockPositivity]
theorem checkBlockPositivity_refines (p : Prog) (hP : PosBlkProg p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (q cvO cvL caO caL : Word) (P : BlockParts)
    (cvTas : List IConstantVal) (css : List (List (IConstantVal × Nat)))
    (hS : StageR dn vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m q.toNat) s₀.mem P.shape)
    (hsrc : ShapeSrc s₀.mem q) (hcv : PSlR decCVp cvTas cvO cvL s₀.mem)
    (hcss : PSlR decCNSB css caO caL s₀.mem) (hPM : PosMR s₀.mem) (hA : AbsOK s₀.mem)
    (hk : ∀ f ∈ posKeepCallees, AbsKeep p f) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 3)) "check_block_positivity" [vis, q, cvO, cvL, caO, caL]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧
      PSlR decKSS (AM.res (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀).1 (r.headD 0)
        (r.tail.headD 0) s'.mem ∧
      PSlR decNFS (AM.res (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀).2.1 (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) s'.mem ∧
      NSB s'.mem ((r.drop 4).headD 0) (AM.res (ConRon.Arena.checkBlockPositivity V fe P cvTas css) a₀).2.2;
      ⊤⦄ := by
  refine triple_post (cbpos_spec p hP.cbp (n + 2) s₀ vis q cvO cvL caO caL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hQ⟩ := cbposW_ok hP n hm hS hq hsrc hcv hcss hPM hA hk
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact hQ

end L.Ind
