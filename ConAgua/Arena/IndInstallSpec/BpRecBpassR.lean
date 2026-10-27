import ConAgua.Arena.IndInstallSpec.DecCNS
import ConAgua.Arena.IndInstallSpec.DecISS
import ConAgua.Arena.IndInstallSpec.HbFreeMfr
import ConAgua.Arena.IndInstallSpec.Icp
import ConAgua.Arena.IndInstallSpec.Pos3MapMProj
import ConAgua.Arena.RecGenSpec.Classes

/-!
# BpRecBpassR

`decBPass`, `BPassR`, `bpMem_eq`, `icprW_ok`, `bpRec_bpassR`, `ctorsLp_of_decPL` and the lemmas only they use.
-/

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The `BlockPass` record -/

/-- **`BlockPass`**, `[env1, cvTas.off, cvTas.len, p, ctorsAs.off, ctorsAs.len, sortsss.off,
sortsss.len, kinds.off, kinds.len, nfs.off, nfs.len, params.off, params.len, rd, cls.off, cls.len,
tbl.off, tbl.len]`, at the environment `fe` (word 0 is its view). The element decoders are the
producers': `check_block_inds` (`decCVp`), `check_block_ctors` (`decCNS`, `decISS`),
`check_block_positivity` (kinds: a member's list of a constructor's list of field kinds; normal forms:
a member's list of handles), `block_nest_ctx` (handles), `check_block_classes` (`decCR`, `decTM`),
`nest_seeds` (`decNCN`). -/
def decBPass (fe : IFEnv) (m : Mem) (q : Nat) : Option BlockPass := do
  pure { env1 := fe,
         cvTas := ← decAt m (decPL m (decCVp m)) (q + 1),
         p := ⟨← decBS m (← iwN m (q + 3))⟩,
         ctorsAs := ← decAt m (decPL m (decCNS m)) (q + 4),
         sortsss := ← decAt m (decPL m (decISS m)) (q + 6),
         kinds := ← decAt m (decPL m (decLH m (decPL m (decLH m (decKL m))))) (q + 8),
         nfs := ← decAt m (decPL m (decLH m (decHL m))) (q + 10),
         params := ← decAt m (decHL m) (q + 12),
         rd := ← decCR m (← iwN m (q + 14)),
         cls := ← decAt m (decPL m (decTM m)) (q + 15),
         tbl := ← decAt m (decPL m (decNCN m)) (q + 17) }

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
    ShapeSrc m (rdW (m.arr64 IW) (q + 3))

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

theorem bpMem_eq (m : Mem) (q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : Word) :
    bpMem m q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 =
      wrIW m q [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18] := by
  simp only [bpMem, wrIW, UInt64.add_assoc]
  rfl

/-- **`check_block_pass_rec`'s run**: a fresh 19-word record at the old top, the stage relation
and the walk memos kept, the pool grown. -/
theorem icprW_ok {p : Prog} (ha : p.lookup "iw_alloc" = some iwAlloc) {n : Nat}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {m m' : Mem}
    {r : List Word} {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : Word}
    (h : icprW p n m w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 = some (r, m'))
    (hS : StageR dn vis fe m a) (hP : PosMR m) :
    ∃ q : Word, r = [q] ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧ PosMR m' ∧ q.toNat = iwTop m ∧
      q.toNat + 19 ≤ iwTop m' ∧
      ∀ j (_hj : j < 19), (m'.arr64 IW)[q.toNat + j]? =
        [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18][j]? := by
  unfold icprW at h
  rcases c1 : callW p n "iw_alloc" [19] m with _ | ⟨rq, m1⟩
  · rw [c1] at h; cases h
  rw [c1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s1, hs1, -, hal⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iwAlloc_specW p ha n _ 19) c1
  simp only at hs1 hal
  subst hs1
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hS.2.2.2.1
  obtain ⟨-, -, hqtop, -, htop1⟩ := StageR.alloc hS hal
  have hc : 200 < (m.arr64 CTL).size := hS.2.2.2.2.2
  rw [bpMem_eq, hm1, hq]
  have hk : (19 : Word).toNat = [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16,
      w17, w18].length := rfl
  obtain ⟨hget, hg, hf, htopW⟩ := recMem_post m [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
    w14, w15, w16, w17, w18] 19 hk hc (by rw [← hq]; simpa using hroom) hS.2.2.2.1
  have hqi : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
  refine ⟨rdW (m.arr64 CTL) 200, rfl, ?_, hg, hP.fr (MFr.of_iw hf), hqi, ?_, fun j _hj => hget j _hj⟩
  · have hS1 := (StageR.alloc hS hal).1
    rw [hm1] at hS1
    exact StageR.wrIW hS1 (rdW (m.arr64 CTL) 200)
      [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18]
  · simp only [iwTop]
    rw [htopW, UInt64.toNat_add]
    have h19 : (19 : Word).toNat = 19 := rfl
    rw [hq] at hroom
    have hsz := hS.2.2.2.1
    rw [h19] at hroom ⊢
    rw [Nat.mod_eq_of_lt (by have : UInt64.size = 2 ^ 64 := rfl; omega)]; exact Nat.le_refl _

/-- **A fresh `BlockPass` record of parts decoded below the tops is decoded below the tops**, its
slices below the top (`BPassR`). -/
theorem bpRec_bpassR {m : Mem} {q : Word} {fe : IFEnv}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : Word}
    (hget : ∀ j (_hj : j < 19), (m.arr64 IW)[q.toNat + j]? =
      [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18][j]?)
    (hq : q.toNat + 19 ≤ iwTop m)
    {cvTas : List IConstantVal} {bs : BlockShape} {ctorsAs : List (List (IConstantVal × Nat))}
    {sss : List (List (List LIdx))} {kinds : List (List (List NestFieldKind))} {nfs : List (List EIdx)}
    {params : List EIdx} {rd : ClassRead} {cls : List TargetMajor} {tbl : List NestCtorNf}
    (hcv : PSlR decCVp cvTas w1 w2 m) (hbs : DecB (fun m => decBS m w3.toNat) m bs)
    (hsrc : ShapeSrc m w3) (hca : PSlR decCNS ctorsAs w4 w5 m) (hss : PSlR decISS sss w6 w7 m)
    (hk : PSlR decKSS kinds w8 w9 m) (hn : PSlR decNFS nfs w10 w11 m)
    (hpa : DecB (fun m => (decHL m w12.toNat w13.toNat : Option (List EIdx))) m params)
    (hpb : w12.toNat + w13.toNat ≤ iwTop m) (hrd : DecB (fun m => decCR m w14.toNat) m rd)
    (hcl : PSlR decTM cls w15 w16 m) (htb : PSlR decNCN tbl w17 w18 m) :
    BPassR w0 fe m q (⟨fe, cvTas, ⟨bs⟩, ctorsAs, sss, kinds, nfs, params, rd, cls, tbl⟩ : BlockPass) := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hw : ∀ j (_hj : j < 19), iwN (truncM m) (q.toNat + j) =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
        w18][j]'(by simpa using _hj)).toNat := fun j _hj => by
    rw [iwN_truncM (by omega)]
    simp only [iwN, nat?, iwA, hget j _hj]
    rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have hwm : ∀ j (_hj : j < 19), iwN m (q.toNat + j) =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
        w18][j]'(by simpa using _hj)).toNat := fun j _hj => by
    rw [← iwN_truncM (show q.toNat + j < iwTop m by omega)]; exact hw j _hj
  have h0 := hw 0 (by omega)
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
  have h11 := hw 11 (by omega)
  have h12 := hw 12 (by omega)
  have h13 := hw 13 (by omega)
  have h14 := hw 14 (by omega)
  have h15 := hw 15 (by omega)
  have h16 := hw 16 (by omega)
  have h17 := hw 17 (by omega)
  have h18 := hw 18 (by omega)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  refine ⟨?_, ⟨hq, ?_⟩, ?_, ?_⟩
  · show decBPass fe (truncM m) q.toNat = _
    have e1 : decPL (truncM m) (decCVp (truncM m)) w1.toNat w2.toNat = some cvTas := hcv.1
    have e3 : decBS (truncM m) w3.toNat = some bs := hbs
    have e4 : decPL (truncM m) (decCNS (truncM m)) w4.toNat w5.toNat = some ctorsAs := hca.1
    have e6 : decPL (truncM m) (decISS (truncM m)) w6.toNat w7.toNat = some sss := hss.1
    have e8 : decPL (truncM m) (decKSS (truncM m)) w8.toNat w9.toNat = some kinds := hk.1
    have e10 : decPL (truncM m) (decNFS (truncM m)) w10.toNat w11.toNat = some nfs := hn.1
    have e12 : (decHL (truncM m) w12.toNat w13.toNat : Option (List EIdx)) = some params := hpa
    have e14 : decCR (truncM m) w14.toNat = some rd := hrd
    have e15 : decPL (truncM m) (decTM (truncM m)) w15.toNat w16.toNat = some cls := hcl.1
    have e17 : decPL (truncM m) (decNCN (truncM m)) w17.toNat w18.toNat = some tbl := htb.1
    simp only [decBPass, decAt, Nat.add_assoc, Nat.reduceAdd, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, Option.bind_eq_bind, Option.bind_some, e1, e3, e4,
      e6, e12, e14, e15, e17]
    have e8' : decPL (truncM m) (decLH (truncM m) (decPL (truncM m) (decLH (truncM m) (decKL (truncM m)))))
        w8.toNat w9.toNat = some kinds := e8
    have e10' : decPL (truncM m) (decLH (truncM m) (decHL (truncM m))) w10.toNat w11.toNat = some nfs := e10
    simp only [e8', e10']
    rfl
  · intro i hi o l ho hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hwm 1 (by omega)] at ho; rw [hwm 2 (by omega)] at hl; cases ho; cases hl; exact hcv.2
    · rw [hwm 4 (by omega)] at ho; rw [hwm 5 (by omega)] at hl; cases ho; cases hl; exact hca.2
    · rw [hwm 6 (by omega)] at ho; rw [hwm 7 (by omega)] at hl; cases ho; cases hl; exact hss.2
    · rw [hwm 8 (by omega)] at ho; rw [hwm 9 (by omega)] at hl; cases ho; cases hl; exact hk.2
    · rw [hwm 10 (by omega)] at ho; rw [hwm 11 (by omega)] at hl; cases ho; cases hl; exact hn.2
    · rw [hwm 12 (by omega)] at ho; rw [hwm 13 (by omega)] at hl; cases ho; cases hl; exact hpb
    · rw [hwm 15 (by omega)] at ho; rw [hwm 16 (by omega)] at hl; cases ho; cases hl; exact hcl.2
    · rw [hwm 17 (by omega)] at ho; rw [hwm 18 (by omega)] at hl; cases ho; cases hl; exact htb.2
  · have := hget 0 (by omega)
    simp only [Nat.add_zero] at this
    simp only [rdW, this]; rfl
  · have e3 := hget 3 (by omega)
    have hq3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
    have hr : rdW (m.arr64 IW) (q + 3) = w3 := by simp only [rdW, hq3, e3]; rfl
    rw [hr]; exact hsrc

/-! ## The classes' constructors' level-parameter slices -/

/-- **A constructor slice decoded below the tops has its constants' level-parameter slices in
`EREC` or empty** (`CtorsLp`): each constructor's constant record is decoded below the tops
(`CVExt`). -/
theorem ctorsLp_of_decPL {m : Mem} {co cl : Nat} {cts : List (IConstantVal × Nat)}
    (hdc : decPL (truncM m) (decCN (truncM m)) co cl = some cts) (hcob : co < 2 ^ 64) (hclb : cl < 2 ^ 64)
    (hE : erTop m ≤ (m.arr64 EREC).size) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    CtorsLp m (UInt64.ofNat co) (UInt64.ofNat cl) := by
  intro k hk
  rw [UInt64.toNat_ofNat_of_lt' hclb] at hk
  obtain ⟨v, hv, hcn⟩ := decPL_getH (truncM m) hdc k hk
  have hv0 := (rec2IwN_trunc hv).2
  rw [← UInt64.toNat_ofNat_of_lt' hcob] at hv0
  obtain ⟨hrdv, hvb⟩ := iwN_rdW_at (w := UInt64.ofNat co) (k := k) hv0 hsz
  simp only [CtorLp]
  rw [hrdv]
  have hcnD : DecB (fun m => decCN m (UInt64.ofNat v : Word).toNat) m
      (cts[k]'(by rw [decPL_length _ hdc]; exact hk)) := by
    show decCN (truncM m) _ = _
    rw [UInt64.toNat_ofNat_of_lt' hvb]; exact hcn
  obtain ⟨a, ha, ha3, hcv, -⟩ := decCN_words hcnD hsz
  rw [ha]
  obtain ⟨⟨-, hx⟩, -⟩ := rec3CVExt_of_trunc (show decCVp (truncM m) a = _ from hcv)
  have ha64 : a + 3 < 2 ^ 64 := by have := (rdW (m.arr64 CTL) 129).toNat_lt; simp only [erTop] at ha3; omega
  have e1 : (UInt64.ofNat a + 1 : Word).toNat = a + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  have e2 : (UInt64.ofNat a + 2 : Word).toNat = a + 2 := by rw [UInt64.toNat_add]; simp <;> omega
  obtain ⟨w1, hw1⟩ : ∃ w, (m.arr64 EREC)[a + 1]? = some w :=
    ⟨_, Array.getElem?_eq_getElem (show a + 1 < (m.arr64 EREC).size by omega)⟩
  obtain ⟨w2, hw2⟩ : ∃ w, (m.arr64 EREC)[a + 2]? = some w :=
    ⟨_, Array.getElem?_eq_getElem (show a + 2 < (m.arr64 EREC).size by omega)⟩
  rw [rdW_of_get? e1.symm hw1, rdW_of_get? e2.symm hw2]
  rcases hx w1.toNat w2.toNat (by simp [nat?, erA, hw1]) (by simp [nat?, erA, hw2])
    with h | h
  · right; omega
  · left; exact h

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

/-! ## The constructors' sums across the formers' environment -/

/-- Every index row is visible (an unrestricted environment). -/
def AllVis (fe : IFEnv) : Prop := ∀ (n : NIdx) (e : Nat × IConstantInfo), fe.idx[n]? = some e → e.1 < fe.visibleBelow

theorem AllVis.push {fe : IFEnv} (hv : AllVis fe) (ci : IConstantInfo) : AllVis (fe.push ci) := by
  intro n e he
  simp only [IFEnv.push, Std.HashMap.getElem?_insert] at he ⊢
  split at he
  · cases he; simp
  · have := hv n e he; omega

/-- The pass's callees without a walk-memo lemma (and positivity's `check_abs_ctor_sorts_all`). -/
def passCallees : List FnName :=
  ["check_block_inds", "check_block_ctors", "block_nest_ctx", "class_read", "class_read_classes",
    "check_abs_ctor_sorts_all"]

end L.Ind

end
