import ConAgua.Arena.IndPartsSpec11

/-!
# Refinements of `IndParts`, part 12 (lane `indproofs2`, helper `parts`): `blockShape?`'s maps

The pieces of `blockShape?` that build lists: the former names (`block_shape_names_of`), the
constructors without their own `nP` (`block_shape_ctors_of`), the members (`block_shape_members_of`,
the twin's `zip`s), the rules' right-hand sides (`block_shape_rhss_of`) and the recursor shapes
(`block_shape_recs_of`, through `rec_target_of`). Each recurses as the twin's list function (the
rest first, then `sl_cons`; `recs_of` calls `rec_target_of` on this element first).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The models -/

/-- **The model of `block_shape_names_of`.** -/
def bsnW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, cto, ctl =>
    if ctl = 0 then some ([0, 0], m)
    else bsnK n cto (bsnW n m (cto + 1) (ctl - 1))
where
  /-- After the recursive call. -/
  bsnK (n : Nat) (cto : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) => bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) cto)) (r.headD 0)
        (r.tail.headD 0))

/-- **The model of `block_shape_ctors_of`.** -/
def bctW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, cso, csl =>
    if csl = 0 then some ([0, 0], m)
    else bctK n (rdW (m.arr64 IW) cso) (bctW n m (cso + 1) (csl - 1))
where
  /-- After the recursive call: the `[cv, nF]` record, consed on. -/
  bctK (n : Nat) (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) =>
      match posRecW m1 [rdW (m1.arr64 IW) c, rdW (m1.arr64 IW) (c + 2)] with
      | none => none
      | some (e, m2) => bgoK3 (consW n m2 e (r.headD 0) (r.tail.headD 0))

/-- **The model of `block_shape_members_of`.** -/
def bmoW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, cto, ctl, io, go =>
    if ctl = 0 then some ([0, 0], m)
    else bmoK n cto io go (bmoW n m (cto + 1) (ctl - 1) (io + 1) (go + 1))
where
  /-- After the recursive call: the member record, consed on. -/
  bmoK (n : Nat) (cto io go : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) =>
      match posRecW m1 [rdW (m1.arr64 IW) cto, rdW (m1.arr64 IW) io,
          rdW (m1.arr64 IW) (rdW (m1.arr64 IW) go), rdW (m1.arr64 IW) (rdW (m1.arr64 IW) go + 1)] with
      | none => none
      | some (e, m2) => bgoK3 (consW n m2 e (r.headD 0) (r.tail.headD 0))

section arms
variable (n : Nat) (m m1 : Mem) (cto ctl cso csl io go ro rl c : Word) (r : List Word)
theorem bsnW_nil (h : ctl = 0) : bsnW (n + 1) m cto ctl = some ([0, 0], m) := by simp [bsnW, h]
theorem bsnW_cons (h : ctl ≠ 0) : bsnW (n + 1) m cto ctl = bsnW.bsnK n cto (bsnW n m (cto + 1) (ctl - 1)) := by
  simp [bsnW, h]
theorem bsnK_some : bsnW.bsnK n cto (some (r, m1)) = bgoK3 (consW n m1
    (rdW (m1.arr64 EREC) (rdW (m1.arr64 IW) cto)) (r.headD 0) (r.tail.headD 0)) := rfl
theorem bctW_nil (h : csl = 0) : bctW (n + 1) m cso csl = some ([0, 0], m) := by simp [bctW, h]
theorem bctW_cons (h : csl ≠ 0) : bctW (n + 1) m cso csl =
    bctW.bctK n (rdW (m.arr64 IW) cso) (bctW n m (cso + 1) (csl - 1)) := by simp [bctW, h]
theorem bctK_some : bctW.bctK n c (some (r, m1)) =
    (match posRecW m1 [rdW (m1.arr64 IW) c, rdW (m1.arr64 IW) (c + 2)] with
      | none => none
      | some (e, m2) => bgoK3 (consW n m2 e (r.headD 0) (r.tail.headD 0))) := rfl
theorem bmoW_nil (h : ctl = 0) : bmoW (n + 1) m cto ctl io go = some ([0, 0], m) := by simp [bmoW, h]
theorem bmoW_cons (h : ctl ≠ 0) : bmoW (n + 1) m cto ctl io go =
    bmoW.bmoK n cto io go (bmoW n m (cto + 1) (ctl - 1) (io + 1) (go + 1)) := by simp [bmoW, h]
theorem bmoK_some : bmoW.bmoK n cto io go (some (r, m1)) =
    (match posRecW m1 [rdW (m1.arr64 IW) cto, rdW (m1.arr64 IW) io,
          rdW (m1.arr64 IW) (rdW (m1.arr64 IW) go), rdW (m1.arr64 IW) (rdW (m1.arr64 IW) go + 1)] with
      | none => none
      | some (e, m2) => bgoK3 (consW n m2 e (r.headD 0) (r.tail.headD 0))) := rfl
end arms
attribute [ind_grind] bsnW_nil bsnW_cons bsnK_some bctW_nil bctW_cons bctK_some bmoW_nil bmoW_cons
  bmoK_some

/-! ## The `vcgen` specs -/

section spec
variable (p : Prog) (hP : IndPartsProg4 p)
include hP

theorem bsn_spec (hp : p.lookup "block_shape_names_of" = some blockShapeNamesOf) (n : Nat) :
    ∀ (s₀ : St) (cto ctl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_names_of" [cto, ctl]
    ⦃fun r s' => LocEq s' s₀ ∧ bsnW n s₀.mem cto ctl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ cto ctl; rw [invoke_eq _ hp]; simp only [callFn, blockShapeNamesOf]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cto ctl
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeNamesOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem bct_spec (hp : p.lookup "block_shape_ctors_of" = some blockShapeCtorsOf) (n : Nat) :
    ∀ (s₀ : St) (cso csl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_ctors_of" [cso, csl]
    ⦃fun r s' => LocEq s' s₀ ∧ bctW n s₀.mem cso csl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ cso csl; rw [invoke_eq _ hp]; simp only [callFn, blockShapeCtorsOf]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cso csl
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeCtorsOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec2_specW p hP.alloc hP.rec2 n, slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem bmo_spec (h4 : p.lookup "rec4" = some rec4)
    (hp : p.lookup "block_shape_members_of" = some blockShapeMembersOf) (n : Nat) :
    ∀ (s₀ : St) (cto ctl io go : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_members_of" [cto, ctl, io, go]
    ⦃fun r s' => LocEq s' s₀ ∧ bmoW n s₀.mem cto ctl io go = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ cto ctl io go; rw [invoke_eq _ hp]; simp only [callFn, blockShapeMembersOf]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ cto ctl io go
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeMembersOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p hP.alloc h4 n, slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

/-- **`block_shape_rhss_of` is its model `brhW`** (generated). -/
l_model brh_spec (p : Prog) (hP : IndPartsProg4 p)
    (hp : p.lookup "block_shape_rhss_of" = some blockShapeRhssOf)
  fns [hp ↦ brhW]
  specs [slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

/-! ## The relations -/

/-- **`block_shape_names_of`**: the formers' names. -/
theorem bsnW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (cto ctl : Word) (cvTs : List IConstantVal) (r : List Word),
    bsnW n m cto ctl = some (r, m') → StageR dn vis fe m a → PSlR decCVp cvTs cto ctl m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (cvTs.map (·.name)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a cto ctl cvTs r h; simp [bsnW] at h
  | succ n ih =>
    intro m m' a cto ctl cvTs r h hS hts
    by_cases hl : ctl = 0
    · rw [bsnW_nil n m cto ctl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hts]
      exact ⟨hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
    rw [bsnW_cons n m cto ctl hl] at h
    obtain ⟨pc, cv0, ts', rfl, hw, hpb, hcv0, hts'⟩ := partsPSl_cons hts hl
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bsnW.bsnK])
    rw [bsnK_some] at h
    obtain ⟨hS1, hg1, hd1, hb1⟩ := ih m m1 a (cto + 1) (ctl - 1) ts' r1 h1 hS hts'
    have hctolt : cto.toNat < iwTop m := by have := hts.2; have : ctl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega
    rw [partsRdIW_grow hg1 hctolt, hw] at h
    obtain ⟨hnl, hne⟩ := partsCVName hg1 hcv0 hpb
    rcases h2 : consW n m1 (rdW (m1.arr64 EREC) (UInt64.ofNat pc)) (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [bgoK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hd2, ht2⟩ := consW_stage h2 hS1 hb1 hnl hd1
    refine ⟨hS2, hg1.trans hg2, ?_, by simp only [List.headD_cons, List.tail_cons]; omega⟩
    simp only [List.headD_cons, List.tail_cons, List.map_cons]
    rw [← hne]; exact hd2

theorem partsDecRules_succ (a : Array Word) (o L : Nat) :
    decRules a o (L + 1) = (do
      let x ← decRule a o
      let xs ← decRules a (o + 11) L
      pure (x :: xs)) := by
  simp only [decRules, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.mul_zero, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range L))
  funext j; simp only [Function.comp]; congr 1; omega

theorem partsRule_rhs {a : Array Word} {q : Nat} {x : IRecRule} (h : decRule a q = some x) :
    hd? a (q + 8) = some x.rhs ∧ ∃ w, a[q + 10]? = some w := by
  unfold decRule at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨kd, -, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Option.pure_def, Option.bind_some] at h
    obtain ⟨c, -, nf, -, cp, -, rhs, hrhs, k, -, e, he, rfl⟩ := h
    simp only [bool?, Option.map_eq_some_iff] at he; obtain ⟨w, hw, -⟩ := he; exact ⟨hrhs, w, hw⟩
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Option.pure_def, Option.bind_some] at h
    obtain ⟨l1, -, l2, -, c, -, nf, -, cp, -, rhs, hrhs, k, -, e, he, rfl⟩ := h
    simp only [bool?, Option.map_eq_some_iff] at he; obtain ⟨w, hw, -⟩ := he; exact ⟨hrhs, w, hw⟩
  · simp at h

/-- **`block_shape_rhss_of`**: the rules' right-hand sides (`EREC` 11-word records). -/
theorem brhW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (ro rl : Word) (rules : List IRecRule) (r : List Word),
    brhW n m ro rl = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => decRules (erA m) ro.toNat rl.toNat) m rules →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (rules.map (·.rhs)) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a ro rl rules r h; rw [brhW.eq_1] at h; cases h
  | succ n ih =>
    intro m m' a ro rl rules r h hS hru
    by_cases hl : rl = 0
    · rw [brhW.arm1 n m ro rl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl
      have : rules = [] := by
        have h0 : decRules (erA (truncM m)) ro.toNat 0 = some rules := hru
        simpa [decRules] using h0.symm
      subst this
      exact ⟨hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
    obtain ⟨L, hL⟩ : ∃ L, rl.toNat = L + 1 :=
      ⟨rl.toNat - 1, by have : rl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
    rw [brhW.arm2 n m ro rl hl] at h
    have hd : decRules (erA (truncM m)) ro.toNat (L + 1) = some rules := by
      have := hru; simp only [DecB, hL] at this; exact this
    rw [partsDecRules_succ] at hd
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
    obtain ⟨x0, hx0, rs', hrs', rfl⟩ := hd
    obtain ⟨hrh, w10, hw10⟩ := partsRule_rhs hx0
    obtain ⟨w, hw, hwl, hwe⟩ := hd?_some hrh
    obtain ⟨hwlt, hw'⟩ := truncM_er_get hw
    have h10 := (truncM_er_get hw10).1
    have hE : erTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 129).toNat_lt
    have hro11 : (ro + 11).toNat = ro.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
    have hro8 : (ro + 8).toNat = ro.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
    have hrest : DecB (fun m => decRules (erA m) (ro + 11).toNat (rl - 1).toNat) m rs' := by
      show decRules _ _ _ = _; rw [hro11, partsPred_of hL]; exact hrs'
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (brhW.k_block_shape_rhss_of.none ..)
    rw [brhW.k_block_shape_rhss_of.arm1] at h
    obtain ⟨hS1, hg1, hd1, hb1⟩ := ih m m1 a (ro + 11) (rl - 1) rs' r1 h1 hS hrest
    have hrd : rdW (m1.arr64 EREC) (ro + 8) = w := by
      refine rdW_of_get? hro8.symm ?_
      rw [hg1.2.2.2 _ hwlt]; exact hw'
    rw [hrd] at h
    rcases h2 : consW n m1 w (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [h2] at h
    · cases h
    rw [brhW.k_sl_cons.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨hS2, hg2, hd2, ht2⟩ := consW_stage h2 hS1 hb1 hwl hd1
    refine ⟨hS2, hg1.trans hg2, ?_, by simp only [List.headD_cons, List.tail_cons]; omega⟩
    simp only [List.headD_cons, List.tail_cons, List.map_cons]
    rw [hwe]; exact hd2

/-- A fresh record's `IW` word `j`, decoded below the new top. -/
theorem partsFreshN {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m'))
    (hS : StageR dn vis fe m a) (hl : ws.length < 2 ^ 64) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      ∀ j (hj : j < ws.length), iwN (truncM m') (q.toNat + j) = some (ws[j]).toNat := by
  obtain ⟨h1, h2, -, -, h5⟩ := partsFresh h hS hl
  exact ⟨h1, h2, h5⟩

/-- **`block_shape_ctors_of`**: the constructors as `[cv, nF]`. -/
theorem bctW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (cso csl : Word) (cs : List (IConstantVal × Nat × Nat)) (r : List Word),
    bctW n m cso csl = some (r, m') → StageR dn vis fe m a → PSlR decSC cs cso csl m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      PSlR decCN (cs.map fun c => (c.1, c.2.2)) (r.headD 0) (r.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' a cso csl cs r h; simp [bctW] at h
  | succ n ih =>
    intro m m' a cso csl cs r h hS hcs
    by_cases hl : csl = 0
    · rw [bctW_nil n m cso csl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hcs]
      exact ⟨hS, IWGrow.refl _, PSlR.nil _ _⟩
    rw [bctW_cons n m cso csl hl] at h
    obtain ⟨pc, ⟨cv0, nP0, nF0⟩, cs', rfl, hw, hpb, hc0, hcs'⟩ := partsPSl_cons hcs hl
    rw [hw] at h
    have hd0 : decSC (truncM m) pc = some (cv0, nP0, nF0) := hc0
    simp only [decSC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hd0
    obtain ⟨cvp, hcvp, cv, hcv, nP, hnP, nF, hnF, e1, e2, e3⟩ := hd0
    subst e1 e2 e3
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hp2 : (UInt64.ofNat pc + 2).toNat = pc + 2 := by
      have := partsIwLt hnF; rw [UInt64.toNat_add, hpw]; simp; omega
    obtain ⟨hcw, hcvb, hclt⟩ := partsIwRd hcvp hpw
    obtain ⟨hfw, hfb, hflt⟩ := partsIwRd hnF hp2
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bctW.bctK])
    rw [bctK_some] at h
    obtain ⟨hS1, hg1, hR1⟩ := ih m m1 a (cso + 1) (csl - 1) cs' r1 h1 hS hcs'
    rw [partsRdIW_grow hg1 (by rw [hpw]; exact hclt), hcw, partsRdIW_grow hg1 (by rw [hp2]; exact hflt),
      hfw] at h
    rcases h2 : posRecW m1 [UInt64.ofNat cvp, UInt64.ofNat nF] with _ | ⟨e, m2⟩ <;> rw [h2] at h
    · cases h
    simp only at h
    obtain ⟨hS2, hg2, hget⟩ := partsFreshN h2 hS1 (by simp)
    have g0 := hget 0 (by simp); have g1 := hget 1 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ,
      UInt64.toNat_ofNat_of_lt' hcvb, UInt64.toNat_ofNat_of_lt' hfb] at g0 g1
    have hg02 := hg1.trans hg2
    have hdec : DecB (fun m => decCN m e.toNat) m2 (cv, nF) := by
      show decCN (truncM m2) e.toNat = _
      have hcv2 : decCVp (truncM m2) cvp = some cv :=
        (show DecB (fun m => decCVp m cvp) m cv from hcv).grow (OMono.decCVp _) hg02
      simp only [decCN, g0, g1, hcv2, bind, Option.bind_some, pure]
    rcases h3 : consW n m2 e (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at h
    · cases h
    rw [bgoK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hR2 := hR1.grow decCN_mono hg2
    obtain ⟨hS3, hg3, hd3, ht3⟩ := partsConsPL decCN_mono h3 hS2 hR2.2 hR2.1 hdec
    exact ⟨hS3, hg02.trans hg3, hd3, Nat.le_of_eq ht3⟩

/-- A number slice's head and tail, below the tops. -/
theorem partsNL_cons {ns : List Nat} {o l : Word} {m : Mem} (h : DecB (fun m => decNL m o.toNat l.toNat) m ns)
    (hb : o.toNat + l.toNat ≤ iwTop m) (hl : l ≠ 0) :
    ∃ x xs, ns = x :: xs ∧ rdW (m.arr64 IW) o = UInt64.ofNat x ∧ x < 2 ^ 64 ∧
      DecB (fun m => decNL m (o + 1).toNat (l - 1).toNat) m xs ∧ (o + 1).toNat + (l - 1).toNat ≤ iwTop m := by
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 :=
    ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hd : decNL (truncM m) o.toNat (L + 1) = some ns := by have := h; simp only [DecB, hL] at this; exact this
  rw [decNL_succ] at hd
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
  obtain ⟨x, hx, xs, hxs, rfl⟩ := hd
  obtain ⟨hw, hxb, holt⟩ := partsIwRd hx rfl
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨x, xs, rfl, hw, hxb, ?_, by rw [ho1, partsPred_of hL]; omega⟩
  show decNL _ _ _ = _; rw [ho1, partsPred_of hL]; exact hxs

/-- **`block_shape_members_of`**: the members, the twin's `zip`s. -/
theorem bmoW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (cto ctl io go : Word) (cvTs : List IConstantVal) (ns : List Nat)
      (gss : List (List (IConstantVal × Nat))) (r : List Word),
    bmoW n m cto ctl io go = some (r, m') → StageR dn vis fe m a → PSlR decCVp cvTs cto ctl m →
    DecB (fun m => decNL m io.toNat ctl.toNat) m ns → io.toNat + ctl.toNat ≤ iwTop m →
    PSlR decGH gss go ctl m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      PSlR decMS (((cvTs.zip ns).zip gss).map fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape))
        (r.headD 0) (r.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' a cto ctl io go cvTs ns gss r h; simp [bmoW] at h
  | succ n ih =>
    intro m m' a cto ctl io go cvTs ns gss r h hS hts hns hnb hgs
    by_cases hl : ctl = 0
    · rw [bmoW_nil n m cto ctl io go hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rw [partsPSl_nil hts]
      exact ⟨hS, IWGrow.refl _, PSlR.nil _ _⟩
    rw [bmoW_cons n m cto ctl io go hl] at h
    obtain ⟨pc, cv, ts', rfl, hw, hpb, hcv, hts'⟩ := partsPSl_cons hts hl
    obtain ⟨n0, ns', rfl, hnw, hn0b, hns', hnb'⟩ := partsNL_cons hns hnb hl
    obtain ⟨gp, g, gss', rfl, hgw, hgpb, hg0, hgs'⟩ := partsPSl_cons hgs hl
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hcl0 : ctl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
    have hd0 : decGH (truncM m) gp = some g := hg0
    simp only [decGH, decAt, bind, Option.bind_eq_some_iff] at hd0
    obtain ⟨goff, hgoff, glen, hglen, hgd⟩ := hd0
    have hgpw : (UInt64.ofNat gp).toNat = gp := UInt64.toNat_ofNat_of_lt' hgpb
    have hgp1 : (UInt64.ofNat gp + 1).toNat = gp + 1 := by
      have := partsIwLt hglen; rw [UInt64.toNat_add, hgpw]; simp; omega
    obtain ⟨hgow, hgob, hgolt⟩ := partsIwRd hgoff hgpw
    obtain ⟨hglw, hglb, hgllt⟩ := partsIwRd hglen hgp1
    obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [bmoW.bmoK])
    rw [bmoK_some] at h
    obtain ⟨hS1, hg1, hR1⟩ := ih m m1 a (cto + 1) (ctl - 1) (io + 1) (go + 1) ts' ns' gss' r1 h1 hS hts'
      hns' hnb' hgs'
    have l1 : cto.toNat < iwTop m := by have := hts.2; omega
    have l2 : io.toNat < iwTop m := by omega
    have l3 : go.toNat < iwTop m := by have := hgs.2; omega
    rw [partsRdIW_grow hg1 l1, hw, partsRdIW_grow hg1 l2, hnw, partsRdIW_grow hg1 l3, hgw,
      partsRdIW_grow hg1 (by rw [hgpw]; exact hgolt), hgow, partsRdIW_grow hg1 (by rw [hgp1]; exact hgllt),
      hglw] at h
    rcases h2 : posRecW m1 [UInt64.ofNat pc, UInt64.ofNat n0, UInt64.ofNat goff, UInt64.ofNat glen] with _ | ⟨e, m2⟩ <;> rw [h2] at h
    · cases h
    simp only at h
    obtain ⟨hS2, hg2, hget⟩ := partsFreshN h2 hS1 (by simp)
    have g0 := hget 0 (by simp); have g1 := hget 1 (by simp); have g2 := hget 2 (by simp)
    have g3 := hget 3 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ, UInt64.toNat_ofNat_of_lt' hpb,
      UInt64.toNat_ofNat_of_lt' hn0b, UInt64.toNat_ofNat_of_lt' hgob, UInt64.toNat_ofNat_of_lt' hglb] at g0 g1 g2 g3
    have hg02 := hg1.trans hg2
    have hdec : DecB (fun m => decMS m e.toNat) m2 ⟨cv, n0, g⟩ := by
      show decMS (truncM m2) e.toNat = _
      have hcv2 : decCVp (truncM m2) pc = some cv := hcv.grow (OMono.decCVp _) hg02
      have hgd2 : decPL (truncM m2) (decCN (truncM m2)) goff glen = some g :=
        (show DecB (fun m => decPL m (decCN m) goff glen) m g from hgd).grow (OMono.decPL decCN_mono _ _) hg02
      simp only [decMS, decAt, g0, g1, hcv2, bind, Option.bind_some, pure, Nat.add_assoc,
        show 2 + 1 = 3 from rfl, g2, g3, hgd2]
    rcases h3 : consW n m2 e (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r3, m3⟩ <;> rw [h3] at h
    · cases h
    rw [bgoK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hR2 := hR1.grow decMS_mono hg2
    obtain ⟨hS3, hg3, hd3, ht3⟩ := partsConsPL decMS_mono h3 hS2 hR2.2 hR2.1 hdec
    exact ⟨hS3, hg02.trans hg3, hd3, Nat.le_of_eq ht3⟩

/-! ## `block_shape_recs_of` -/

/-- **`block_shape_recs_of` is its model `brsW`** (generated). -/
l_model brs_spec (p : Prog) (hP : IndPartsProg4 p) (h6 : p.lookup "rec6" = some rec6)
    (hr : p.lookup "block_shape_rhss_of" = some blockShapeRhssOf)
    (hp : p.lookup "block_shape_recs_of" = some blockShapeRecsOf)
  fns [hp ↦ brsW]
  specs [recTargetOf_spec p hP.view hP.find hP.target hP.strip hP.ad n, brh_spec p hP hr n,
    rec6_specW p hP.alloc h6 n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [ind_grind] finish [rdW_eq] gen 20

theorem decSR_fields2 {m : Mem} {p : Nat} {cv : IConstantVal} {mI rP : Nat} {rules : List IRecRule}
    (h : decSR m p = some (cv, mI, rP, rules)) :
    ∃ o l, iwN m (p + 3) = some o ∧ iwN m (p + 4) = some l ∧ decRules (erA m) o l = some rules := by
  simp only [decSR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, g, hg, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  exact ⟨e, f, he, hf, hg⟩

/-- The recursor shape of a split recursor (the twin's `rs.mapM` body). -/
def brsF (names : List NIdx) (r : IConstantVal × Nat × Nat × List IRecRule) : AM RecShape := do
  let tgt ← ConRon.Arena.recTargetOf names r.2.1 r.1.type
  pure ⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩

/-- **`block_shape_recs_of`'s model refines the twin's `rs.mapM`.** -/
theorem brsW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {no nl : Word}
    {names : List NIdx} (n : Nat) :
    ∀ (m : Mem) (a : AState) (ro rl : Word) (rs : List (IConstantVal × Nat × Nat × List IRecRule)),
    StageR dn vis fe m a → PSlR decSR rs ro rl m →
    DecB (fun m => decHL m no.toNat nl.toNat) m names → no.toNat + nl.toNat ≤ iwTop m →
    Sim (brsW n m no nl ro rl) (rs.mapM (brsF names)) a
      (fun r xs m' a' => PSlR decRS xs (r.headD 0) (r.tail.headD 0) m' ∧ StageR dn vis fe m' a' ∧
        IWGrow m m') := by
  induction n with
  | zero => intro m a ro rl rs _ _ _ _ r m' e; rw [brsW.eq_1] at e; cases e
  | succ n ih =>
    intro m a ro rl rs hS hrs hnm hnb
    by_cases hl : rl = 0
    · rw [brsW.arm1 n m no nl ro rl hl]
      subst hl; rw [partsPSl_nil hrs]
      exact Sim.ret ⟨PSlR.nil _ _, hS, IWGrow.refl _⟩
    rw [brsW.arm2 n m no nl ro rl hl]
    obtain ⟨pc, ⟨cv, mI, rP, rules⟩, rs', rfl, hw, hpb, hrs0, hrs'⟩ := partsPSl_cons hrs hl
    obtain ⟨⟨cvp, hcvp, hcv⟩, hmI, hrP⟩ := decSR_fields (show decSR (truncM m) pc = _ from hrs0)
    obtain ⟨ro', rl', hro', hrl', hru⟩ := decSR_fields2 (show decSR (truncM m) pc = _ from hrs0)
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have hpw : (UInt64.ofNat pc).toNat = pc := UInt64.toNat_ofNat_of_lt' hpb
    have hpk : ∀ k : Nat, k ≤ 4 → pc + k < iwTop m → (UInt64.ofNat pc + UInt64.ofNat k).toNat = pc + k := by
      intro k hk hlt; rw [UInt64.toNat_add, hpw, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; omega
    have hp1 : (UInt64.ofNat pc + 1).toNat = pc + 1 := hpk 1 (by omega) (partsIwLt hmI)
    have hp2 : (UInt64.ofNat pc + 2).toNat = pc + 2 := hpk 2 (by omega) (partsIwLt hrP)
    have hp3 : (UInt64.ofNat pc + 3).toNat = pc + 3 := hpk 3 (by omega) (partsIwLt hro')
    have hp4 : (UInt64.ofNat pc + 4).toNat = pc + 4 := hpk 4 (by omega) (partsIwLt hrl')
    obtain ⟨hcw, hcvb, hclt⟩ := partsIwRd hcvp hpw
    obtain ⟨hmw, hmb, hmlt⟩ := partsIwRd hmI hp1
    obtain ⟨hrw, hrb, hrlt⟩ := partsIwRd hrP hp2
    obtain ⟨how, hob, holt⟩ := partsIwRd hro' hp3
    obtain ⟨hlw, hlb, hllt⟩ := partsIwRd hrl' hp4
    obtain ⟨htyl, htye⟩ := partsCVType hcv (UInt64.toNat_ofNat_of_lt' hcvb)
    rw [hw, hcw, hmw]
    rw [List.mapM_cons]
    simp only [brsF, bind_assoc, pure_bind]
    have hnames : decHL m no.toNat nl.toNat = some names := hnm.get (OMono.decHL _ _)
    refine Sim.bindK (brsW.k_rec_target_of.none ..) (fun _ _ => brsW.k_rec_target_of.arm1 ..)
      (Q := fun r t m1 a1 => r = [UInt64.ofNat t] ∧ t ≤ names.length ∧ StageR dn vis fe m1 a1 ∧ IWGrow m m1)
      ?_ ?_
    · intro r1 m1 e
      obtain ⟨t, a1, hrun, hr, hS1, hg1⟩ := recTW_ok n dn fe vis m m1 a no nl _ _ r1 names e hS htyl
        hnames (by omega) hnb
      rw [UInt64.toNat_ofNat_of_lt' hmb, htye] at hrun
      exact ⟨t, a1, hrun, hr, partsRecTarget_le hrun, hS1, hg1⟩
    rintro r1 t m1 a1 ⟨rfl, htl, hS1, hg1⟩
    simp only [List.headD_cons]
    rw [partsRdIW_grow hg1 (by rw [hp3]; exact holt), how, partsRdIW_grow hg1 (by rw [hp4]; exact hllt), hlw]
    intro r m' e
    rcases h2 : brhW n m1 (UInt64.ofNat ro') (UInt64.ofNat rl') with _ | ⟨r2, m2⟩ <;> rw [h2] at e
    · rw [brsW.k_block_shape_rhss_of.none] at e; cases e
    rw [brsW.k_block_shape_rhss_of.arm1] at e
    have hru1 : DecB (fun m => decRules (erA m) (UInt64.ofNat ro').toNat (UInt64.ofNat rl').toNat) m1 rules := by
      rw [UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb]
      exact (show DecB (fun m => decRules (erA m) ro' rl') m rules from hru).grow (partsDecRules_mono _ _) hg1
    obtain ⟨hS2, hg2, hd2, hb2⟩ := brhW_ok n m1 m2 a1 _ _ rules r2 h2 hS1 hru1
    have hg12 := hg1.trans hg2
    rw [partsRdIW_grow hg12 (by rw [hpw]; exact hclt), hcw, partsRdIW_grow hg12 (by rw [hp2]; exact hrlt), hrw,
      partsRdIW_grow hg12 (by rw [hp1]; exact hmlt), hmw] at e
    rcases h3 : posRecW m2 [UInt64.ofNat cvp, UInt64.ofNat rP, UInt64.ofNat mI, UInt64.ofNat t,
        r2.headD 0, r2.tail.headD 0] with _ | ⟨rc, m3⟩ <;> rw [h3] at e
    · rw [brsW.k_rec6.none] at e; cases e
    rw [brsW.k_rec6.arm1] at e
    obtain ⟨hS3, hg3, hget⟩ := partsFreshN h3 hS2 (by simp)
    have hnlen : names.length < 2 ^ 64 := by rw [decHL_length _ hnames]; omega
    have g0 := hget 0 (by simp); have g1 := hget 1 (by simp); have g2 := hget 2 (by simp)
    have g3 := hget 3 (by simp); have g4 := hget 4 (by simp); have g5 := hget 5 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ, UInt64.toNat_ofNat_of_lt' hcvb,
      UInt64.toNat_ofNat_of_lt' hrb, UInt64.toNat_ofNat_of_lt' hmb,
      UInt64.toNat_ofNat_of_lt' (show t < 2 ^ 64 by omega)] at g0 g1 g2 g3 g4 g5
    have hg03 := hg12.trans hg3
    have hdec : DecB (fun m => decRS m rc.toNat) m3 ⟨cv, rP, mI, t, rules.map (·.rhs)⟩ := by
      show decRS (truncM m3) rc.toNat = _
      have hcv3 : decCVp (truncM m3) cvp = some cv :=
        (show DecB (fun m => decCVp m cvp) m cv from hcv).grow (OMono.decCVp _) hg03
      have hrh3 : decHL (truncM m3) (r2.headD 0).toNat (r2.tail.headD 0).toNat = some (rules.map (·.rhs)) :=
        (decHL_decB hd2 hb2).grow (OMono.decHL _ _) hg3
      simp only [decRS, decAt, g0, g1, g2, g3, hcv3, bind, Option.bind_some, pure, Nat.add_assoc,
        show 4 + 1 = 5 from rfl, g4, g5, hrh3]
    revert r m' e
    refine Sim.bindK (brsW.k_block_shape_recs_of.none ..) (fun _ _ => brsW.k_block_shape_recs_of.arm1 ..)
      (ih m3 a1 (ro + 1) (rl - 1) rs' hS3 (hrs'.grow decSR_mono hg03) (hnm.grow (OMono.decHL _ _) hg03)
        (Nat.le_trans hnb hg03.1)) ?_
    rintro r4 xs m4 a4 ⟨hR4, hS4, hg4⟩
    intro r m' e
    rcases h5 : consW n m4 rc (r4.headD 0) (r4.tail.headD 0) with _ | ⟨r5, m5⟩ <;> rw [h5] at e
    · cases e
    rw [brsW.k_sl_cons.arm1] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS5, hg5, hd5, ht5⟩ := partsConsPL decRS_mono h5 hS4 hR4.2 hR4.1 (hdec.grow (decRS_mono _) hg4)
    exact ⟨_, a4, rfl, ⟨hd5, Nat.le_of_eq ht5⟩, hS5, ((hg03.trans hg4).trans hg5)⟩

end L.Ind
