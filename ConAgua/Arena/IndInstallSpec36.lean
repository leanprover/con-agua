import ConAgua.Arena.IndInstallSpec35
import ConAgua.Arena.RecGenSpec21
import ConAgua.Arena.IndInstallSpec34

/-!
# Refinements of `IndInstall`, part 36 (lane `indproofs4`): `checkBlockPass`

`check_block_pass(vis, p0, isRec)` (`icpW`, `IndInstallSpec28`): the formers (`checkBlockInds`),
the flush, the constructors, the positivity context, the classes (`RecGenSpec21`), the positivity
check, the classes' seeds and the nested seeds, then the 19-word `BlockPass` record
(`check_block_pass_rec`), decoded below the tops (`BPassR`, what `checkBlockTail` takes), with what
the recursor stage takes of it: its shape's recursor slice below the top (`RecsB`, the shape a copy
of the input's by `block_shape_with_sort`) and its classes' constructors' level-parameter slices in
`EREC` (`ClassesLp`, from the classes' decoding: `classesLp_of_decPL`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

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
      ∀ j (hj : j < 19), (m'.arr64 IW)[q.toNat + j]? =
        [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18][j]? := by
  unfold icprW at h
  cases c1 : callW p n "iw_alloc" [19] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨rq, m1⟩ := q1
  rw [c1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
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
  refine ⟨rdW (m.arr64 CTL) 200, rfl, ?_, hg, hP.fr (MFr.of_iw hf), hqi, ?_, fun j hj => hget j hj⟩
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
    (hget : ∀ j (hj : j < 19), (m.arr64 IW)[q.toNat + j]? =
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
  have hw : ∀ j (hj : j < 19), iwN (truncM m) (q.toNat + j) =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
        w18][j]'(by simpa using hj)).toNat := fun j hj => by
    rw [iwN_truncM (by omega)]
    simp only [iwN, nat?, iwA, hget j hj]
    rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have hwm : ∀ j (hj : j < 19), iwN m (q.toNat + j) =
      some ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17,
        w18][j]'(by simpa using hj)).toNat := fun j hj => by
    rw [← iwN_truncM (show q.toNat + j < iwTop m by omega)]; exact hw j hj
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
    simp only [decBPass, decAt, decLH, Nat.add_assoc, Nat.reduceAdd, h1, h2, h3, h4, h5, h6, h7, h8,
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

theorem am_bind_ok {α β : Type} {x : AM α} {f : α → AM β} {a a' : AState} {y : β}
    (h : (x >>= f).run a = .ok (y, a')) : ∃ v a₁, x.run a = .ok (v, a₁) ∧ (f v).run a₁ = .ok (y, a') := by
  simp only [StateT.run_bind] at h
  cases hx : x.run a with
  | error e => rw [hx] at h; cases h
  | ok va => obtain ⟨v, a₁⟩ := va; rw [hx] at h; exact ⟨v, a₁, rfl, h⟩

theorem exc_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ v, x = .ok v ∧ f v = .ok y := by
  cases x with
  | error e => cases h
  | ok v => exact ⟨v, rfl, h⟩

/-- Every index row is visible (an unrestricted environment). -/
def AllVis (fe : IFEnv) : Prop := ∀ (n : NIdx) (e : Nat × IConstantInfo), fe.idx[n]? = some e → e.1 < fe.visibleBelow

theorem AllVis.push {fe : IFEnv} (hv : AllVis fe) (ci : IConstantInfo) : AllVis (fe.push ci) := by
  intro n e he
  simp only [IFEnv.push, Std.HashMap.getElem?_insert] at he ⊢
  split at he
  · cases he; simp
  · have := hv n e he; omega

theorem find?_push_allVis {fe : IFEnv} {ci : IConstantInfo} (hv : AllVis fe) (n : NIdx) :
    (fe.push ci).find? n = if ci.name = n then some ci else fe.find? n := by
  simp only [IFEnv.find?, IFEnv.push, Std.HashMap.getElem?_insert]
  by_cases h : ci.name = n
  · subst h; simp
  · have h' : (ci.name == n) = false := by simpa using h
    simp only [h', Bool.false_eq_true, ite_false, h]
    cases e : fe.idx[n]? with
    | none => rfl
    | some r =>
      have := hv n r e
      simp only [show r.1 < fe.visibleBelow + 1 by omega, this, ite_true]

/-! ## `check_block_pass` -/

/-- The lookups of `check_block_pass`. -/
structure PassProg (p : Prog) : Prop where
  inds : IndsProg p
  flush : FlushProg p
  ctors : CtorsProg p
  nck : NckProg p
  nhl : NhLook p
  bnc : p.lookup "block_nest_ctx" = some blockNestCtx
  cbc : CbcProg p
  pos : PosBlkProg p
  sds : SdProg p
  rs : RsLook p
  ha : p.lookup "iw_alloc" = some iwAlloc
  prec : p.lookup "check_block_pass_rec" = some checkBlockPassRec
  pass : p.lookup "check_block_pass" = some checkBlockPass

/-- The pass's callees without a walk-memo lemma. -/
def passCallees : List FnName :=
  ["check_block_inds", "check_block_ctors", "block_nest_ctx", "class_read", "class_read_classes"]

/-- The pass's callees outside the `abstract1` cascade, which keep its memo (`AbsKeep`, a program
fact), with those of `check_block_inds` and `check_block_positivity`. -/
def passKeepCallees : List FnName :=
  ["check_block_ctors", "block_nest_ctx", "check_block_classes", "class_seeds", "check_block_pass_rec"] ++
    indsKeepCallees ++ posKeepCallees

/-- **`check_block_pass`' model refines `checkBlockPass`.** -/
theorem icpW_sim {p : Prog} (hP : PassProg p) {fs : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs) (n : Nat)
    (hn : 2 ^ 31 + (n + 4) ≤ coreWalkFuel) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState} {p0 isRec : Word} {bs : BlockShape} {b : Bool}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m p0.toNat) m bs) (hsrc : ShapeSrc m p0)
    (hcx : ShapeCV m p0) (hb : (isRec != 0) = b) (hv : AllVis fe) (hPm : PosMR m) (hA : AbsOK m) (hk : ∀ f ∈ passKeepCallees, AbsKeep p f) :
    Sim (icpW p (n + 3) m vis p0 isRec) (ConRon.Arena.checkBlockPass V fe ⟨bs⟩ b) a
      (fun r x m' a' => StageR dn (rdW (m'.arr64 IW) (r.headD 0)) x.env1 m' a' ∧ IWGrow m m' ∧
        BPassR (rdW (m'.arr64 IW) (r.headD 0)) x.env1 m' (r.headD 0) x ∧ PosMR m' ∧ AbsOK m' ∧
        (RecsB m p0 → RecsB m' (rdW (m'.arr64 IW) (r.headD 0 + 3))) ∧
        ClassesLp m' (rdW (m'.arr64 IW) (r.headD 0 + 15)) (rdW (m'.arr64 IW) (r.headD 0 + 16))) := by
  have hk' : ∀ f, f ∈ passKeepCallees → AbsKeep p f := hk
  intro r m' h
  unfold icpW at h
  -- the formers
  cases c1 : callW p (n + 3) "check_block_inds" [vis, p0, isRec] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, icpK1_some] at h
  obtain ⟨s1, hs1, -, hok1, hout, hA1, hrb1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (checkBlockInds_refines p hP.inds (n + 2) _ a dn vis fe p0 isRec bs b hS hq hsrc hcx hb hA
      (fun f hf => hk' f (by simp [passKeepCallees, hf]))) c1
  simp only at hs1 hout
  subst hs1
  have hrun1 := AM.run_of_ok _ a hok1
  generalize AM.res (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a = x1 at hrun1 hout
  generalize AM.st (ConRon.Arena.checkBlockInds V fe ⟨bs⟩ b) a = a1 at hrun1 hout
  obtain ⟨fe1, cvTas, bs1⟩ := x1
  obtain ⟨hS1, hg1, hcv1, hbs1, hsrc1⟩ := hout
  have hP1 := PosMR.ofClosed hcl (hfs _ (by decide)) c1 hPm
  simp only at hS1 hcv1 hbs1
  have hT1 : iwTop s1.mem < 2 ^ 64 := (rdW (s1.mem.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, hmemv⟩ := partsShapeFacts hbs1 hsrc1
  -- the flush
  cases c2 : callW p (n + 3) "flush_caches" [] s1.mem with
  | none => rw [c2] at h; cases h
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, icpK2_some] at h
  obtain ⟨s2, hs2, -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (flushCaches_spec p hP.flush (n + 3) _) c2
  simp only at hs2 hfok hfm
  subst hs2
  obtain ⟨hS2, hg2⟩ := flush_stage hS1 hfok
  rw [← hfm] at hS2 hg2
  have hP2 : PosMR s2.mem := by
    rw [hfm]; exact hP1.fr (MFr.of_frame (flushMem_frame s1.mem) (by simp) (by
      intro x hx; left; have := flushCtl_lt x hx; omega))
  have hA2 : AbsOK s2.mem := by rw [hfm]; exact AFr.of_frame (flushMem_frame s1.mem) (by decide) (by decide) hA1
  generalize ha2 : ({ a1 with caches := Caches.empty } : AState) = a2 at hS2
  have hg12 := hg2
  -- the constructors
  have hbs2 := hbs1.grow (decBS_mono _) hg12
  have hsrc2 := partsHsrc_grow hg12 hq9 hsrc1
  obtain ⟨hmemb, -, -, -, -, -, -⟩ := decBS_some (show decBS (truncM s2.mem) _ = _ from hbs2)
  have hq1 : (r1.tail.tail.tail.headD 0 + 1).toNat = (r1.tail.tail.tail.headD 0).toNat + 1 := by
    have h9 := hq9
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hmss := bpPSl decMS_mono hmemb hsrc2 (w := r1.tail.tail.tail.headD 0)
    (w1 := r1.tail.tail.tail.headD 0 + 1) rfl hq1
  have hcv2 := hcv1.grow (fun q => OMono.decCVp q) hg12
  cases c3 : callW p (n + 3) "check_block_ctors" [r1.headD 0, r1.headD 0, r1.tail.tail.tail.headD 0,
      rdW (s2.mem.arr64 IW) (r1.tail.tail.tail.headD 0),
      rdW (s2.mem.arr64 IW) (r1.tail.tail.tail.headD 0 + 1), r1.tail.headD 0, r1.tail.tail.headD 0]
      s2.mem with
  | none => rw [c3] at h; cases h
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, icpK3_some] at h
  obtain ⟨s3, hs3, -, hok3, hS3, hg3, hca3, hss3, hcb3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (checkBlockCtors_refines p hP.ctors (n + 2) _ a2 dn (r1.headD 0) fe1 _ _ _ _ _ bs1 bs1.members cvTas
      hS2 hbs2 hsrc2 hmss hcv2 hA2) c3
  simp only at hs3 hS3 hg3 hca3 hss3 hcb3
  subst hs3
  have hrun3 := AM.run_of_ok _ a2 hok3
  generalize AM.res (ConRon.Arena.checkBlockCtors V fe1 fe1 bs1 bs1.members cvTas) a2 = x3
    at hrun3 hca3 hss3 hcb3
  generalize AM.st (ConRon.Arena.checkBlockCtors V fe1 fe1 bs1 bs1.members cvTas) a2 = a3 at hrun3 hS3
  obtain ⟨ctorsAs, sss⟩ := x3
  have hP3 := PosMR.ofClosed hcl (hfs _ (by decide)) c3 hP2
  have hA3 : AbsOK s3.mem := hk' _ (by simp [passKeepCallees]) _ _ _ _ _ c3 hA2
  have hg13 := hg12.trans hg3
  -- the positivity context
  have hbs3 := hbs1.grow (decBS_mono _) hg13
  have hsrc3 := partsHsrc_grow hg13 hq9 hsrc1
  have hcv3 := hcv1.grow (fun q => OMono.decCVp q) hg13
  cases c4 : callW p (n + 3) "block_nest_ctx" [r1.headD 0, r1.tail.tail.tail.headD 0, r1.tail.headD 0,
      r1.tail.tail.headD 0] s3.mem with
  | none => rw [c4] at h; cases h
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, icpK4_some] at h
  obtain ⟨s4, hs4, -, hok4, hctx4, hho4, hhob4, hS4, hg4, hin4, hsl4, hhi4, hpn4⟩ :=
    triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (blockNestCtx_refines p hP.nck hP.nhl hP.bnc (n + 1) _ a3 dn (r1.headD 0) fe1 _ _ _ bs1 cvTas
      hS3 hbs3 hsrc3 hcv3) c4
  simp only at hs4 hctx4 hho4 hhob4 hS4 hg4 hin4 hsl4 hhi4 hpn4
  subst hs4
  have hrun4 := AM.run_of_ok _ a3 hok4
  generalize AM.res (ConRon.Arena.blockNestCtx fe1 bs1 cvTas) a3 = x4 at hrun4 hctx4 hho4 hhi4 hpn4
  generalize AM.st (ConRon.Arena.blockNestCtx fe1 bs1 cvTas) a3 = a4 at hrun4 hS4
  obtain ⟨c, holes⟩ := x4
  have hP4 := PosMR.ofClosed hcl (hfs _ (by decide)) c4 hP3
  have hA4 : AbsOK s4.mem := hk' _ (by simp [passKeepCallees]) _ _ _ _ _ c4 hA3
  have hg14 := hg13.trans hg4
  -- the classes
  have hT4 : iwTop s4.mem < 2 ^ 64 := (rdW (s4.mem.arr64 CTL) 200).toNat_lt
  have hbs4 := hbs1.grow (decBS_mono _) hg14
  have hsrc4 := partsHsrc_grow hg14 hq9 hsrc1
  obtain ⟨-, hq94, hmemv4⟩ := partsShapeFacts hbs4 hsrc4
  have hBS : BSOK s4.mem (r1.tail.tail.tail.headD 0).toNat bs1 :=
    ⟨hbs4, hsrc4, fun o l j v ho hl hj hv => by have := hmemv4 o l j v ho hl hj hv; omega⟩
  obtain ⟨-, hrcs, -, -, -, -, -⟩ := decBS_some (show decBS (truncM s4.mem) _ = _ from hbs4)
  obtain ⟨ro, rl, hro, hrl, hrd, hrb⟩ := partsAt decRS_mono hrcs
  have hp2 : (r1.tail.tail.tail.headD 0 + 2).toNat = (r1.tail.tail.tail.headD 0).toNat + 2 := by
    have h9 := hq94
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hp3 : (r1.tail.tail.tail.headD 0 + 3).toNat = (r1.tail.tail.tail.headD 0).toNat + 2 + 1 := by
    have h9 := hq94
    generalize r1.tail.tail.tail.headD 0 = w at h9 ⊢
    rw [UInt64.toNat_add]; simp; omega
  obtain ⟨wro, -⟩ := bpWord hro hp2
  obtain ⟨wrl, -⟩ := bpWord hrl hp3
  have hRD : RecsDec s4.mem (rdW (s4.mem.arr64 IW) (r1.tail.tail.tail.headD 0 + 2))
      (rdW (s4.mem.arr64 IW) (r1.tail.tail.tail.headD 0 + 3)) bs1.recs := by
    rw [wro, wrl, UInt64.ofNat_toNat, UInt64.ofNat_toNat]
    refine ⟨hrd, ?_⟩
    rcases hrb with h0 | hb
    · subst h0; simpa using ro.toNat_lt
    · omega
  have hcdec : decCtx (truncM s4.mem) (r4.headD 0).toNat = some c := hctx4
  obtain ⟨-, -, -, -, hpar, -, -⟩ := decCtx_some hcdec
  obtain ⟨po, pl, hpo, hpl, hpd⟩ := decAt_some hpar
  have hc10 : (r4.headD 0).toNat + 10 < iwTop s4.mem := hin4.1 10 (by omega)
  have hc7 : (r4.headD 0 + 7).toNat = (r4.headD 0).toNat + 7 := by
    have h10 := hc10
    generalize r4.headD 0 = w at h10 ⊢
    rw [UInt64.toNat_add]; simp; omega
  have hc8 : (r4.headD 0 + 8).toNat = (r4.headD 0).toNat + 7 + 1 := by
    have h10 := hc10
    generalize r4.headD 0 = w at h10 ⊢
    rw [UInt64.toNat_add]; simp; omega
  obtain ⟨wpo, hpob⟩ := bpWord hpo hc7
  obtain ⟨wpl, hplb⟩ := bpWord hpl hc8
  have hpoT : (UInt64.ofNat po : Word).toNat = po := UInt64.toNat_ofNat_of_lt' hpob
  have hplT : (UInt64.ofNat pl : Word).toNat = pl := UInt64.toNat_ofNat_of_lt' hplb
  have hpfD : DecB (fun m => (decHL m (rdW (s4.mem.arr64 IW) (r4.headD 0 + 7)).toNat
      (rdW (s4.mem.arr64 IW) (r4.headD 0 + 8)).toNat : Option (List EIdx))) s4.mem c.params := by
    rw [wpo, wpl, hpoT, hplT]; exact hpd
  have hpfb : (rdW (s4.mem.arr64 IW) (r4.headD 0 + 7)).toNat +
      (rdW (s4.mem.arr64 IW) (r4.headD 0 + 8)).toNat ≤ iwTop s4.mem := by
    rw [wpo, wpl, hpoT, hplT]
    rw [iwN_truncM (by omega)] at hpo
    rw [iwN_truncM (by omega)] at hpl
    exact hsl4 7 (by omega) po pl hpo hpl
  have hca4 := hca3.grow decCNS_mono hg4
  cases c5 : callW p (n + 3) "check_block_classes" [r1.headD 0, r1.tail.tail.tail.headD 0,
      rdW (s4.mem.arr64 IW) (r4.headD 0 + 7), rdW (s4.mem.arr64 IW) (r4.headD 0 + 8), r3.headD 0,
      r3.tail.headD 0] s4.mem with
  | none => rw [c5] at h; cases h
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, icpK5_some] at h
  have hA5 : AbsOK m5 := hk' _ (by simp [passKeepCallees]) _ _ _ _ _ c5 hA4
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hrd5, hms5, hP5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (checkBlockClasses_refines hP.cbc hcl (hfs _ (by decide)) (hfs _ (by decide)) dn (r1.headD 0) fe1
      (n + 2) _ a4 _ _ _ _ _ bs1 ctorsAs c.params hS4 hBS hsrc4 hRD hca4 hpfD hpfb hP4) c5
  simp only at hs5 hS5 hg5 hrd5 hms5 hP5
  subst hs5
  have hrun5 := AM.run_of_ok _ a4 hok5
  generalize AM.res (ConRon.Arena.checkBlockClasses V fe1 bs1 c.params ctorsAs) a4 = x5 at hrun5 hrd5 hms5
  generalize AM.st (ConRon.Arena.checkBlockClasses V fe1 bs1 c.params ctorsAs) a4 = a5 at hrun5 hS5
  obtain ⟨rd, ms⟩ := x5
  have hg15 := hg14.trans hg5
  -- the positivity check
  have hbs5 := hbs1.grow (decBS_mono _) hg15
  have hsrc5 := partsHsrc_grow hg15 hq9 hsrc1
  have hcv5 := hcv1.grow (fun q => OMono.decCVp q) hg15
  have hcb5 := hcb3.grow decCNSB_mono (hg4.trans hg5)
  cases c6 : callW p (n + 3) "check_block_positivity" [r1.headD 0, r1.tail.tail.tail.headD 0,
      r1.tail.headD 0, r1.tail.tail.headD 0, r3.headD 0, r3.tail.headD 0] s5.mem with
  | none => rw [c6] at h; cases h
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [c6, icpK6_some] at h
  obtain ⟨s6, hs6, -, hok6, hS6, hg6, hP6, hA6, hks6, hnf6, hns6⟩ := triple_of_callW
    (s₀ := ⟨s5.mem, Locals.init []⟩)
    (checkBlockPositivity_refines p hP.pos n (by omega) _ a5 dn (r1.headD 0) fe1 _ _ _ _ _ ⟨bs1⟩
      cvTas ctorsAs hS5 hbs5 hsrc5 hcv5 hcb5 hP5 hA5 (fun f hf => hk' f (by simp [passKeepCallees, hf]))) c6
  simp only at hs6 hS6 hg6 hP6 hA6 hks6 hnf6 hns6
  subst hs6
  have hrun6 := AM.run_of_ok _ a5 hok6
  generalize AM.res (ConRon.Arena.checkBlockPositivity V fe1 ⟨bs1⟩ cvTas ctorsAs) a5 = x6 at hrun6 hks6 hnf6 hns6
  generalize AM.st (ConRon.Arena.checkBlockPositivity V fe1 ⟨bs1⟩ cvTas ctorsAs) a5 = a6 at hrun6 hS6
  obtain ⟨kinds, nfs, NS⟩ := x6
  have hg16 := hg15.trans hg6
  have hT6 : iwTop s6.mem < 2 ^ 64 := (rdW (s6.mem.arr64 CTL) 200).toNat_lt
  -- the classes' seeds
  have hU4 : UCtx dn (r1.headD 0) fe1 s4.mem (r4.headD 0) c :=
    ⟨hctx4.get (decCtx_mono _), hin4, hsl4⟩
  have hg46 := hg5.trans hg6
  have hU6 := hU4.grow hg46
  have hho6 : (decHL s6.mem (r4.tail.headD 0).toNat (r4.tail.tail.headD 0).toNat : Option (List EIdx)) =
      some holes := by rw [decHL_grow3 hg46 hhob4]; exact hho4
  have hms6 := hms5.grow (fun q => decTM_mono q) hg6
  cases c7 : callW p (n + 3) "class_seeds" [r4.headD 0, r4.tail.headD 0, r4.tail.tail.headD 0,
      r5.tail.headD 0, r5.tail.tail.headD 0] s6.mem with
  | none => rw [c7] at h; cases h
  | some q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [c7, icpK7_some] at h
  obtain ⟨s7, hs7, -, hok7, hS7, hg7, hsd7, hP7⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (classSeeds_refines hP.sds (n + 3) _ a6 dn (r1.headD 0) fe1 _ _ _ _ _ c holes ms hS6 hU6 hhi4 hho6
      (Nat.le_trans hhob4 hg46.1) hms6 hP6) c7
  simp only at hs7 hS7 hg7 hsd7 hP7
  subst hs7
  have hA7 : AbsOK s7.mem := hk' _ (by simp [passKeepCallees]) _ _ _ _ _ c7 hA6
  have hrun7 := AM.run_of_ok _ a6 hok7
  generalize AM.res (ConRon.Arena.classSeeds c holes ms) a6 = seeds at hrun7 hsd7
  generalize AM.st (ConRon.Arena.classSeeds c holes ms) a6 = a7 at hrun7 hS7
  -- the nested seeds
  have hg67 := hg7
  have hU7 := hU6.grow hg67
  have hns7 := hns6.grow hg67 hT6
  have hdrop : (r6.drop 4).headD 0 = r6.tail.tail.tail.tail.headD 0 := by
    rcases r6 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
  rw [hdrop] at hns7
  cases c8 : callW p (n + 3) "nest_seeds" [r1.headD 0, r4.headD 0, r7.headD 0, r7.tail.headD 0,
      r6.tail.tail.tail.tail.headD 0] s7.mem with
  | none => rw [c8] at h; cases h
  | some q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [c8, icpK8_some] at h
  obtain ⟨s8, hs8, -, ns, a8, hrun8, hS8, hg8, hns8, hP8, hA8⟩ := triple_of_callW (s₀ := ⟨s7.mem, Locals.init []⟩)
    (nestSeeds_refines hP.rs (n + 3) dn (r1.headD 0) fe1 (by omega) _ a7 _ _ _ _ c seeds NS hS7 hU7
      hhi4 hsd7.2.1 hsd7.2.2.2 hns7 hP7 hA7) c8
  simp only at hs8 hS8 hg8 hns8 hP8 hA8
  subst hs8
  have hT8 : iwTop s8.mem < 2 ^ 64 := (rdW (s8.mem.arr64 CTL) 200).toNat_lt
  obtain ⟨-, -, -, hnfsB⟩ := nsb_words hns8 hT8
  have htbl8 : PSlR decNCN ns.ctorNfs.toList (rdW (s8.mem.arr64 IW) (r8.headD 0 + 4))
      (rdW (s8.mem.arr64 IW) (r8.headD 0 + 5)) s8.mem := ⟨hnfsB, hns8.b4⟩
  have hg48 := (hg5.trans hg6).trans (hg7.trans hg8)
  have hw7 : rdW (s8.mem.arr64 IW) (r4.headD 0 + 7) = rdW (s4.mem.arr64 IW) (r4.headD 0 + 7) :=
    partsRdIW_grow hg48 (by rw [hc7]; omega)
  have hw8 : rdW (s8.mem.arr64 IW) (r4.headD 0 + 8) = rdW (s4.mem.arr64 IW) (r4.headD 0 + 8) :=
    partsRdIW_grow hg48 (by rw [hc8]; omega)
  -- the record
  cases c9 : callW p (n + 3) "check_block_pass_rec" [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0,
      r1.tail.tail.tail.headD 0, r3.headD 0, r3.tail.headD 0, r3.tail.tail.headD 0,
      r3.tail.tail.tail.headD 0, r6.headD 0, r6.tail.headD 0, r6.tail.tail.headD 0,
      r6.tail.tail.tail.headD 0, rdW (s8.mem.arr64 IW) (r4.headD 0 + 7),
      rdW (s8.mem.arr64 IW) (r4.headD 0 + 8), r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0,
      rdW (s8.mem.arr64 IW) (r8.headD 0 + 4), rdW (s8.mem.arr64 IW) (r8.headD 0 + 5)] s8.mem with
  | none => rw [c9] at h; cases h
  | some q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [c9, icprK_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hA9 : AbsOK m9 := hk' _ (by simp [passKeepCallees]) _ _ _ _ _ c9 hA8
  obtain ⟨s9, hs9, -, hW9⟩ := triple_of_callW (s₀ := ⟨s8.mem, Locals.init []⟩)
    (icpr_spec p hP.prec (n + 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) c9
  simp only at hs9 hW9
  subst hs9
  obtain ⟨q, hr9, hS9, hg9, hP9, hqt, hq19, hget⟩ := icprW_ok hP.ha hW9 hS8 hP8
  subst hr9
  have hg89 := hg9
  have hgA := hg1.trans (hg12.trans (hg3.trans (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9)))))))
  have hw0 : rdW (s9.mem.arr64 IW) q = r1.headD 0 := by
    have := hget 0 (by omega)
    simp only [Nat.add_zero, List.getElem?_cons_zero] at this
    simp only [rdW, this]; rfl
  have hBP := bpRec_bpassR (fe := fe1) hget hq19
    (hcv1.grow (fun q => OMono.decCVp q) (hg12.trans (hg3.trans (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9))))))))
    (hbs1.grow (decBS_mono _) (hg12.trans (hg3.trans (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9))))))))
    (partsHsrc_grow (hg12.trans (hg3.trans (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9))))))) hq9 hsrc1)
    (hca3.grow decCNS_mono (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9))))))
    (hss3.grow decISS_mono (hg4.trans (hg5.trans (hg6.trans (hg7.trans (hg8.trans hg9))))))
    (hks6.grow decKSS_mono (hg7.trans (hg8.trans hg9)))
    (hnf6.grow decNFS_mono (hg7.trans (hg8.trans hg9)))
    (by rw [hw7, hw8]; exact hpfD.grow (OMono.decHL _ _) (hg48.trans hg9))
    (by rw [hw7, hw8]; exact Nat.le_trans hpfb (hg48.trans hg9).1)
    (hrd5.grow (decCR_mono _) (hg6.trans (hg7.trans (hg8.trans hg9))))
    (hms6.grow (fun q => decTM_mono q) (hg7.trans (hg8.trans hg9)))
    (htbl8.grow (fun q => decNCN_mono q) hg9)
  have hT9 : iwTop s9.mem < 2 ^ 64 := (rdW (s9.mem.arr64 CTL) 200).toNat_lt
  have hrw : ∀ j (hj : j < 19), rdW (s9.mem.arr64 IW) (q + UInt64.ofNat j) =
      [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0, r3.headD 0,
        r3.tail.headD 0, r3.tail.tail.headD 0, r3.tail.tail.tail.headD 0, r6.headD 0, r6.tail.headD 0,
        r6.tail.tail.headD 0, r6.tail.tail.tail.headD 0, rdW (s8.mem.arr64 IW) (r4.headD 0 + 7),
        rdW (s8.mem.arr64 IW) (r4.headD 0 + 8), r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0,
        rdW (s8.mem.arr64 IW) (r8.headD 0 + 4), rdW (s8.mem.arr64 IW) (r8.headD 0 + 5)][j]'(by simpa using hj) := by
    intro j hj
    have e := hget j hj
    have hqj : (q + UInt64.ofNat j).toNat = q.toNat + j := tailToNat (by omega)
    rw [List.getElem?_eq_getElem (by simpa using hj)] at e
    simp only [rdW, hqj, e]; rfl
  have hr3 : rdW (s9.mem.arr64 IW) (q + 3) = r1.tail.tail.tail.headD 0 := hrw 3 (by omega)
  have hr15 : rdW (s9.mem.arr64 IW) (q + 15) = r5.tail.headD 0 := hrw 15 (by omega)
  have hr16 : rdW (s9.mem.arr64 IW) (q + 16) = r5.tail.tail.headD 0 := hrw 16 (by omega)
  have hms9 := hms6.grow (fun q => decTM_mono q) (hg7.trans (hg8.trans hg9))
  refine ⟨⟨fe1, cvTas, ⟨bs1⟩, ctorsAs, sss, kinds, nfs, c.params, rd, ms, ns.ctorNfs.toList⟩, a8, ?_,
    ?_, hgA, ?_, hP9, hA9, fun hrb => ?_, ?_⟩
  · rw [← ha2] at hrun3
    simp only [ConRon.Arena.checkBlockPass, StateT.run_bind, hrun1, except_ok_bind, BlockParts.complete,
      flushCaches_run, hrun3, hrun4, hrun5, hrun6, hrun7, hrun8]
    rfl
  · simp only [List.headD_cons]; rw [hw0]; exact hS9
  · simp only [List.headD_cons]; rw [hw0]; exact hBP
  · simp only [List.headD_cons]; rw [hr3]
    exact (hrb1 hrb).grow (hg12.trans (hg3.trans (hg4.trans (hg5.trans (hg6.trans (hg7.trans
      (hg8.trans hg9))))))) (by omega)
  · simp only [List.headD_cons]; rw [hr15, hr16]
    exact classesLp_of_decPL hms9.1 hS9.2.2.1 hS9.2.2.2.1

/-- **`check_block_pass(vis, p0, isRec)` refines `checkBlockPass`**: from the stage relation, the
block's shape decoded below the tops (with its member slice's bound and constant records), an
unrestricted environment (`AllVis`) and the walk
memos well formed, the pass's record at `r[0]` decoded below the tops (`BPassR`, at its word 0, the
formers' view), the stage relation at that view of the formers' environment, the memos kept, the
record's shape's recursor slice below the top if the input's is (`RecsB`), its classes'
constructors' level-parameter slices in `EREC` (`ClassesLp`). Program facts: the lookups (`PassProg`) and the write set of the callees without a memo lemma
(`hcl`). -/
@[refines ConRon.Arena.checkBlockPass]
theorem checkBlockPass_refines {p : Prog} (hP : PassProg p) {fs : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs) (n : Nat)
    (hn : 2 ^ 31 + (n + 4) ≤ coreWalkFuel) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {p0 isRec : Word} {bs : BlockShape} {b : Bool}
    (hS : StageR dn vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m p0.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem p0) (hcx : ShapeCV s₀.mem p0) (hb : (isRec != 0) = b) (hv : AllVis fe)
    (hPm : PosMR s₀.mem) (hA : AbsOK s₀.mem) (hk : ∀ f ∈ passKeepCallees, AbsKeep p f) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 4)) "check_block_pass" [vis, p0, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ x a', (ConRon.Arena.checkBlockPass V fe ⟨bs⟩ b).run a₀ = .ok (x, a') ∧
      StageR dn (rdW (s'.mem.arr64 IW) (r.headD 0)) x.env1 s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧
      BPassR (rdW (s'.mem.arr64 IW) (r.headD 0)) x.env1 s'.mem (r.headD 0) x ∧ PosMR s'.mem ∧ AbsOK s'.mem ∧
      (RecsB s₀.mem p0 → RecsB s'.mem (rdW (s'.mem.arr64 IW) (r.headD 0 + 3))) ∧
      ClassesLp s'.mem (rdW (s'.mem.arr64 IW) (r.headD 0 + 15)) (rdW (s'.mem.arr64 IW) (r.headD 0 + 16)); ⊤⦄ :=
  triple_post (icp_spec p hP.pass (n + 3) s₀ vis p0 isRec) fun r s' ⟨hl, hm⟩ =>
    ⟨hl, icpW_sim hP hcl hfs n hn hS hq hsrc hcx hb hv hPm hA hk r s'.mem hm⟩

end L.Ind
