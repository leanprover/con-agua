import ConAgua.Arena.IndPartsSpec11

/-!
# Refinements of `IndParts`, part 12 (lane `indproofs2`, helper `parts`): `blockShape?`'s maps

The pieces of `blockShape?` that build lists: the former names (`block_shape_names_of`), the
constructors without their own `nP` (`block_shape_ctors_of`), the members (`block_shape_members_of`,
the twin's `zip`s), the rules' right-hand sides (`block_shape_rhss_of`) and the recursor shapes
(`block_shape_recs_of`, through `rec_target_of`). Each recurses as the twin's list function (the
rest first, then `sl_cons`; `recs_of` calls `rec_target_of` on this element first).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

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

/-- **The model of `block_shape_rhss_of`.** -/
def brhW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, ro, rl =>
    if rl = 0 then some ([0, 0], m)
    else brhK n ro (brhW n m (ro + 11) (rl - 1))
where
  /-- After the recursive call. -/
  brhK (n : Nat) (ro : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (r, m1) => bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (ro + 8)) (r.headD 0) (r.tail.headD 0))

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
theorem brhW_nil (h : rl = 0) : brhW (n + 1) m ro rl = some ([0, 0], m) := by simp [brhW, h]
theorem brhW_cons (h : rl ≠ 0) : brhW (n + 1) m ro rl = brhW.brhK n ro (brhW n m (ro + 11) (rl - 1)) := by
  simp [brhW, h]
theorem brhK_some : brhW.brhK n ro (some (r, m1)) =
    bgoK3 (consW n m1 (rdW (m1.arr64 EREC) (ro + 8)) (r.headD 0) (r.tail.headD 0)) := rfl
end arms
attribute [ind_grind] bsnW_nil bsnW_cons bsnK_some bctW_nil bctW_cons bctK_some bmoW_nil bmoW_cons
  bmoK_some brhW_nil brhW_cons brhK_some

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

theorem brh_spec (hp : p.lookup "block_shape_rhss_of" = some blockShapeRhssOf) (n : Nat) :
    ∀ (s₀ : St) (ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_rhss_of" [ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ brhW n s₀.mem ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ ro rl; rw [invoke_eq _ hp]; simp only [callFn, blockShapeRhssOf]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ro rl
    rw [invoke_eq _ hp]
    simp only [callFn, blockShapeRhssOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slCons_specW p hP.alloc hP.copy hP.cons n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

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
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hl; rw [partsPSl_nil hts]
      exact ⟨hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
    rw [bsnW_cons n m cto ctl hl] at h
    obtain ⟨pc, cv0, ts', rfl, hw, hpb, hcv0, hts'⟩ := partsPSl_cons hts hl
    cases h1 : bsnW n m (cto + 1) (ctl - 1) with
    | none => rw [h1] at h; simp [bsnW.bsnK] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, bsnK_some] at h
    obtain ⟨hS1, hg1, hd1, hb1⟩ := ih m m1 a (cto + 1) (ctl - 1) ts' r1 h1 hS hts'
    have hctolt : cto.toNat < iwTop m := by have := hts.2; have : ctl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega
    rw [partsRdIW_grow hg1 hctolt, hw] at h
    obtain ⟨hnl, hne⟩ := partsCVName hg1 hcv0 hpb
    cases h2 : consW n m1 (rdW (m1.arr64 EREC) (UInt64.ofNat pc)) (r1.headD 0) (r1.tail.headD 0) with
    | none => rw [h2] at h; cases h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, bgoK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
  | zero => intro m m' a ro rl rules r h; simp [brhW] at h
  | succ n ih =>
    intro m m' a ro rl rules r h hS hru
    by_cases hl : rl = 0
    · rw [brhW_nil n m ro rl hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hl
      have : rules = [] := by
        have h0 : decRules (erA (truncM m)) ro.toNat 0 = some rules := hru
        simpa [decRules] using h0.symm
      subst this
      exact ⟨hS, IWGrow.refl _, by simp [decHL, hslice?], by simp⟩
    obtain ⟨L, hL⟩ : ∃ L, rl.toNat = L + 1 :=
      ⟨rl.toNat - 1, by have : rl.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
    rw [brhW_cons n m ro rl hl] at h
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
    cases h1 : brhW n m (ro + 11) (rl - 1) with
    | none => rw [h1] at h; simp [brhW.brhK] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, brhK_some] at h
    obtain ⟨hS1, hg1, hd1, hb1⟩ := ih m m1 a (ro + 11) (rl - 1) rs' r1 h1 hS hrest
    have hrd : rdW (m1.arr64 EREC) (ro + 8) = w := by
      refine rdW_of_get? hro8.symm ?_
      rw [hg1.2.2.2 _ hwlt]; exact hw'
    rw [hrd] at h
    cases h2 : consW n m1 w (r1.headD 0) (r1.tail.headD 0) with
    | none => rw [h2] at h; cases h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, bgoK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hS2, hg2, hd2, ht2⟩ := consW_stage h2 hS1 hb1 hwl hd1
    refine ⟨hS2, hg1.trans hg2, ?_, by simp only [List.headD_cons, List.tail_cons]; omega⟩
    simp only [List.headD_cons, List.tail_cons, List.map_cons]
    rw [hwe]; exact hd2

end L.Ind
