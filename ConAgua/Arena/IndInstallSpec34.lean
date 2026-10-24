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

/-! ## Census -/

end L.Ind
