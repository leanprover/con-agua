module

public import ConAgua.Arena.IndInstallSpec.InstallCtxWord9
public import ConAgua.Arena.IndInstallSpec.NfsProg
public import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
public import ConAgua.Arena.IndPosSpec.CfW
public import ConAgua.Arena.IndPosSpec.RsLook
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# Pos3Init

`PosBlkProg`, `pos3_init`.
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

/-! ## The fresh `NestState` -/

theorem pos3_init {p : Prog} (hP : PosBlkProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {m m' : Mem} {r : List Word}
    (h : callW p n "check_block_positivity_init" [] m = some (r, m')) (hS : StageR dn vis fe m a) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧ NSB m' (r.headD 0) {} := by
  obtain ⟨s', rfl, -, hm, hr, hroom⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkBlockPositivityInit_spec p hP.nfs.alloc hP.init n _ hS.iw.iwSize) h
  simp only at hm hr hroom
  obtain ⟨hget, hg, hf, htop⟩ := rec6Mem_post m 0 0 0 0 0 0 hS.iw.ctl hroom hS.iw.iwSize
  rw [← hm] at hget hg hf htop
  have hT' : iwTop s'.mem = iwTop m + 6 := by
    have hl : (rdW (m.arr64 CTL) 200).toNat + 6 < 2 ^ 64 := Nat.lt_of_le_of_lt hroom hS.iw.iwSize
    simp only [iwTop, htop, UInt64.toNat_add]; simp; omega
  have hroom' : iwTop m + 6 ≤ (m.arr64 IW).size := hroom
  refine ⟨stage_frame_iw hS hf (by omega), hg, MFr.of_iw hf, ?_⟩
  rw [hr]
  have hsz' : iwTop s'.mem < 2 ^ 64 := Nat.lt_of_le_of_lt (stage_frame_iw hS hf (by omega)).2.1
    (stage_frame_iw hS hf (by omega)).iw.iwSize
  have := nsb_rec6 (m' := s'.mem) (q := rdW (m.arr64 CTL) 200) (kO := 0) (kL := 0) (aO := 0) (aL := 0)
    (nO := 0) (nL := 0) (keys := []) (act := []) (nfs := []) (by simp only [iwTop] at *; omega) hsz'
    (fun j hj => hget j hj) (by simp [KsB, DecB, decPL]) (by simp) (by simp [KsB, DecB, decPL]) (by simp)
    (by simp [NfsB, DecB, decPL]) (by simp)
  exact this

/-! ## The relation -/

/-! ## Census -/

end L.Ind
