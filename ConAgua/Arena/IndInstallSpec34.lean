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

/-- **`check_block_positivity` is its model `cbposW`** (generated). -/
l_model cbpos_spec (p : Prog) (hp : p.lookup "check_block_positivity" = some checkBlockPositivity)
  fns [hp ↦ cbposW]
  specs [callW_spec p n "block_nest_ctx", callW_spec p n "nest_uniform",
    callW_spec p n "check_block_positivity_init", callW_spec p n "nest_root", callW_spec p n "pin_word",
    callW_spec p n "lvl_eq_true", callW_spec p n "check_abs_ctor_sorts_all",
    callW_spec p n "check_block_positivity_nfs"]
  grind [ind_grind] finish [rdW_eq] gen 40 heartbeats 1600000 instances 20000

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

/-! ## Census -/

end L.Ind
