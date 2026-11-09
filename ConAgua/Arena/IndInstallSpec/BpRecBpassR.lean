module

public import ConAgua.Arena.IndInstallSpec.DecCNS
public import ConAgua.Arena.IndInstallSpec.DecISS
public import ConAgua.Arena.IndInstallSpec.HbFreeMfr
public import ConAgua.Arena.IndInstallSpec.Icp
public import ConAgua.Arena.IndInstallSpec.Pos3MapMProj
import ConAgua.Arena.RecGenSpec.Classes
import ConAgua.Arena.IndPosSpec.FgW

@[expose] public section

/-!
# BpRecBpassR

`decBPass`, `BPassR` (the 11-word `BlockPass` record), `bpMem_eq`, `icprW_ok`, `bpRec_bpassR`,
`ctorsLp_of_decPL` and the lemmas only they use.
-/

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The `BlockPass` record -/

/-- **`BlockPass`**, `[env1, p, kinds.off, kinds.len, params.off, params.len, rd, cls.off, cls.len,
tbl.off, tbl.len]` (`check_block_pass_rec`), at the environment `fe` (word 0 is its view). The
element decoders are the producers': `check_block_positivity`'s outputs read as their kinds
(`nest_out_kinds`: a member's list of an output's field kinds), `block_nest_ctx` (handles),
`check_block_classes` (`decCR`, `decTM`), `nest_seeds` (`decNCN`). -/
def decBPass (fe : IFEnv) (m : Mem) (q : Nat) : Option BlockPass := do
  pure { env1 := fe,
         p := ← decBS m (← iwN m (q + 1)),
         kinds := ← decAt m (decPL m (decLH m (decPL m (decLH m (decKL m))))) (q + 2),
         params := ← decAt m (decHL m) (q + 4),
         rd := ← decCR m (← iwN m (q + 6)),
         cls := ← decAt m (decPL m (decTM m)) (q + 7),
         tbl := ← decAt m (decPL m (decNCN m)) (q + 9) }

end L.Ind

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **The pass's record at `q`**: decoded below the tops at `fe` (whose view `vis` is word 0), its
slices and the shape's members below the top. -/
def BPassR (vis : Word) (fe : IFEnv) (m : Mem) (q : Word) (bp : BlockPass) : Prop :=
  DecB (fun m => decBPass fe m q.toNat) m bp ∧ BPassB m q.toNat ∧ rdW (m.arr64 IW) q = vis ∧
    ShapeSrc m (rdW (m.arr64 IW) (q + 1))

end L.Ind

end

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The record -/

theorem bpMem_eq (m : Mem) (q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : Word) :
    bpMem m q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 = wrIW m q [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10] := by
  simp only [bpMem, wrIW, UInt64.add_assoc]
  rfl

/-- **`check_block_pass_rec`'s run**: a fresh 11-word record at the old top, the stage relation
and the walk memos kept, the pool grown. -/
theorem icprW_ok {p : Prog} (ha : p.lookup "iw_alloc" = some iwAlloc) {n : Nat}
    {vis : Word} {fe : IFEnv} {a : AState} {m m' : Mem}
    {r : List Word} {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : Word}
    (h : icprW p n m w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 = some (r, m'))
    (hS : StageR vis fe m a) (hP : PosMR m) :
    ∃ q : Word, r = [q] ∧ StageR vis fe m' a ∧ IWGrow m m' ∧ PosMR m' ∧ q.toNat = iwTop m ∧
      q.toNat + 11 ≤ iwTop m' ∧
      ∀ j (_hj : j < 11), (m'.arr64 IW)[q.toNat + j]? = [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10][j]? := by
  unfold icprW at h
  rcases c1 : callW p n "iw_alloc" [11] m with _ | ⟨rq, m1⟩
  · rw [c1] at h; cases h
  rw [c1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p ha n _ 11) c1
  simp only at hs1 hal
  subst hs1
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hS.iw.iwSize
  have hc : 200 < (m.arr64 CTL).size := hS.iw.ctl
  rw [bpMem_eq, hm1, hq]
  have hk : (11 : Word).toNat = [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10].length := rfl
  obtain ⟨hget, hg, hf, htopW⟩ := recMem_post m [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10] 11 hk hc (by rw [← hq]; simpa using hroom) hS.iw.iwSize
  have hqi : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
  refine ⟨rdW (m.arr64 CTL) 200, rfl, ?_, hg, hP.fr (MFr.of_iw hf), hqi, ?_, fun j _hj => hget j _hj⟩
  · have hS1 := (StageR.alloc hS hal).1
    rw [hm1] at hS1
    exact StageR.wrIW hS1 (rdW (m.arr64 CTL) 200) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10]
  · simp only [iwTop]
    rw [htopW, UInt64.toNat_add]
    have h11 : (11 : Word).toNat = 11 := rfl
    rw [hq] at hroom
    have hsz := hS.iw.iwSize
    rw [h11] at hroom ⊢
    rw [Nat.mod_eq_of_lt (by have : UInt64.size = 2 ^ 64 := rfl; omega)]; exact Nat.le_refl _

/-- **A fresh `BlockPass` record of parts decoded below the tops is decoded below the tops**, its
slices below the top (`BPassR`). -/
theorem bpRec_bpassR {m : Mem} {q : Word} {fe : IFEnv}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : Word}
    (hget : ∀ j (_hj : j < 11), (m.arr64 IW)[q.toNat + j]? = [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10][j]?)
    (hq : q.toNat + 11 ≤ iwTop m)
    {bs : BlockShape} {kinds : List (List (List NestFieldKind))}
    {params : List EIdx} {rd : ClassRead} {cls : List TargetMajor} {tbl : List NestCtorNf}
    (hbs : DecB (fun m => decBS m w1.toNat) m bs) (hsrc : ShapeSrc m w1)
    (hk : PSlR decKSS kinds w2 w3 m)
    (hpa : DecB (fun m => (decHL m w4.toNat w5.toNat : Option (List EIdx))) m params)
    (hpb : w4.toNat + w5.toNat ≤ iwTop m) (hrd : DecB (fun m => decCR m w6.toNat) m rd)
    (hcl : PSlR decTM cls w7 w8 m) (htb : PSlR decNCN tbl w9 w10 m) :
    BPassR w0 fe m q (⟨fe, bs, kinds, params, rd, cls, tbl⟩ : BlockPass) := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hw : ∀ j (_hj : j < 11), iwN (truncM m) (q.toNat + j) =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10][j]'(by simpa using _hj)).toNat := fun j _hj => by
    rw [iwN_truncM (by omega)]
    simp only [iwN, nat?, iwA, aread_apply, hget j _hj]
    rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have hwm : ∀ j (_hj : j < 11), iwN m (q.toNat + j) =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10][j]'(by simpa using _hj)).toNat := fun j _hj => by
    rw [← iwN_truncM (show q.toNat + j < iwTop m by omega)]; exact hw j _hj
  have h1 := hw 1 (by omega)
  have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega)
  have h4 := hw 4 (by omega)
  have h5 := hw 5 (by omega)
  have h6 := hw 6 (by omega)
  have h7 := hw 7 (by omega)
  have h8 := hw 8 (by omega)
  have h9 := hw 9 (by omega)
  have h10 := hw 10 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  refine ⟨?_, ⟨hq, ?_⟩, ?_, ?_⟩
  · show decBPass fe (truncM m) q.toNat = _
    have e1 : decBS (truncM m) w1.toNat = some bs := hbs
    have e2 : decPL (truncM m) (decKSS (truncM m)) w2.toNat w3.toNat = some kinds := hk.dec
    have e4 : (decHL (truncM m) w4.toNat w5.toNat : Option (List EIdx)) = some params := hpa
    have e6 : decCR (truncM m) w6.toNat = some rd := hrd
    have e7 : decPL (truncM m) (decTM (truncM m)) w7.toNat w8.toNat = some cls := hcl.dec
    have e9 : decPL (truncM m) (decNCN (truncM m)) w9.toNat w10.toNat = some tbl := htb.dec
    simp only [decBPass, decAt, Nat.add_assoc, Nat.reduceAdd, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10, Option.bind_eq_bind, Option.bind_some, e1, e4, e6, e7, e9]
    have e2' : decPL (truncM m) (decLH (truncM m) (decPL (truncM m) (decLH (truncM m) (decKL (truncM m)))))
        w2.toNat w3.toNat = some kinds := e2
    simp only [e2']
    rfl
  · intro i hi o l ho hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · rw [hwm 2 (by omega)] at ho; rw [hwm 3 (by omega)] at hl; cases ho; cases hl; exact hk.bound
    · rw [hwm 4 (by omega)] at ho; rw [hwm 5 (by omega)] at hl; cases ho; cases hl; exact hpb
    · rw [hwm 7 (by omega)] at ho; rw [hwm 8 (by omega)] at hl; cases ho; cases hl; exact hcl.bound
    · rw [hwm 9 (by omega)] at ho; rw [hwm 10 (by omega)] at hl; cases ho; cases hl; exact htb.bound
  · have := hget 0 (by omega)
    simp only [Nat.add_zero] at this
    simp only [rdW, this]; rfl
  · have e1 := hget 1 (by omega)
    have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hr : rdW (m.arr64 IW) (q + 1) = w1 := by simp only [rdW, hq1, e1]; rfl
    rw [hr]; exact hsrc

/-! ## The classes' constructors' level-parameter slices -/

/-- **A constructor slice decoded below the tops has its constants' level-parameter slices in
`EREC` or empty** (`CtorsLp`): each constructor's constant record is decoded below the tops
(`CVExt`). -/
theorem ctorsLp_of_decPL {m : Mem} {co cl : Nat} {cts : List (IConstantVal × Nat)}
    (hdc : decPL (truncM m) (decCN (truncM m)) co cl = some cts) (hcob : co < 2 ^ 64) (hclb : cl < 2 ^ 64)
    (hE : erTop m ≤ (m.arr64 EREC).size) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    CtorsLp m (UInt64.ofNat co) (UInt64.ofNat cl) := by
  sorry

theorem iwN_trunc_lt {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) : v < 2 ^ 64 := by
  have h6 := (rec2IwN_trunc h).2
  simp only [iwN, nat?, Option.map_eq_some_iff] at h6
  obtain ⟨w, -, rfl⟩ := h6; exact w.toNat_lt

/-- **A class slice decoded below the tops has its constructors' level-parameter slices in `EREC`
or empty** (`ClassesLp`). -/
theorem classesLp_of_decPL {m : Mem} {mo ml : Word} {ms : List TargetMajor}
    (h : decPL (truncM m) (decTM (truncM m)) mo.toNat ml.toNat = some ms)
    (hE : erTop m ≤ (m.arr64 EREC).size) (hsz : (m.arr64 IW).size < 2 ^ 64) : ClassesLp m mo ml := by
  intro c hc v o l hv ho hl
  obtain ⟨v', hv', htm⟩ := decPL_getH (truncM m) h c hc
  rw [(rec2IwN_trunc hv').2] at hv
  cases Option.some.inj hv
  simp only [decTM, bind, Option.bind_eq_some_iff, pure] at htm
  obtain ⟨_, -, _, -, _, -, _, -, _, -, cts, hcts, -⟩ := htm
  obtain ⟨co, cl, hco, hcl, hdc⟩ := decAt_some hcts
  rw [(rec2IwN_trunc hco).2] at ho
  rw [show v + 6 + 1 = v + 7 by omega] at hcl
  rw [(rec2IwN_trunc hcl).2] at hl
  cases Option.some.inj ho
  cases Option.some.inj hl
  exact ctorsLp_of_decPL hdc (iwN_trunc_lt hco) (iwN_trunc_lt hcl) hE hsz

/-- The pass's callees without a walk-memo lemma (and positivity's `check_abs_ctor_sorts_all`). -/
def passCallees : List FnName :=
  ["check_block_inds", "check_block_ctors", "block_nest_ctx", "class_read", "class_read_classes",
    "check_abs_ctor_sorts_all"]

end L.Ind

end
