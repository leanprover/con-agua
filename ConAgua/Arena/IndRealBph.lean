import ConAgua.Arena.DeclAndPinIndRef

/-!
# `basis_pin_hit(off, len)`: the loops and their models (lane `indproofs4`, helper `bph`)

`L.Checker.basisPinHitL` (`Checker/Entry.lean`) tries the kinds `0`‥`3` (`eqK`, `natK`, `emptyK`,
`falseK`): the pinned block (`rom_basis_decls(k)`, an `IW` slice), the name pre-filter (the
member names, word `1` of each constant record, compared pointwise: the inner loop), then the block
copied to `IW` (`er_to_iw`) and compared (`canon_eq_list`). Both loops are named blocks
(`bphNLoop`, `bphLoop`; `basisPinHitL_eq : … := rfl`) with recursive models (`bphNW`, `bphGoW`).
The refinement is `IndRealBph2.lean`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The loops as named blocks -/

/-- The name pre-filter of `basisPinHitL`, named for its spec. -/
-- con-ron: none — `basisPinHitL`'s inner loop (`rfl`), a named block for the proof
def bphNLoop : Stmt := lblk (bo, bl, k, o, l, j, e, q, ql) {
  while j < l {
    if EREC.u64[IW.u64[o + j] + 1] != EREC.u64[EREC.u64[bo + j] + 1] { break };
    j += 1
  }
}

/-- The loop over the kinds of `basisPinHitL`, named for its spec. -/
-- con-ron: none — `basisPinHitL`'s outer loop (`rfl`), a named block for the proof
def bphLoop : Stmt := lblk (bo, bl, k, o, l, j, e, q, ql) {
  while k < 4 {
    (o, l) := call rom_basis_decls(k);
    if l == bl {
      j := 0;
      ⟪bphNLoop⟫;
      if j == l {
        (q, ql) := call er_to_iw(bo, bl);
        e := call canon_eq_list(q, ql, o, l);
        if e != 0 { return (1, k) };
        return (0, 0)
      }
    };
    k += 1
  }
}

/-- `basisPinHitL`, with its loops spliced from `bphLoop`. -/
-- con-ron: none — `basisPinHitL` itself (`rfl`), its loops named blocks for the proof
def basisPinHitL' : FunDecl := lfn (bo, bl) locals (k, o, l, j, e, q, ql) {
  k := 0;
  ⟪bphLoop⟫;
  return (0, 0)
}

theorem basisPinHitL_eq : L.Checker.basisPinHitL = basisPinHitL' := rfl

/-! ## The models -/

/-- **The model of the name pre-filter** at L fuel `f`, from member `j`: the first member whose
name words differ, or `l`. -/
def bphNW : Nat → Mem → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _ => none
  | f + 1, m, bo, o, l, j =>
    if j < l then
      if rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + j) + 1) ≠
          rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (bo + j) + 1) then some j
      else bphNW f m bo o l (j + 1)
    else some j

section arms
variable (f : Nat) (m : Mem) (bo o l j : Word)
theorem bphNW_exit (h : ¬ j < l) : bphNW (f + 1) m bo o l j = some j := by
  simp only [bphNW]; rw [ite_eq_right h]
theorem bphNW_brk (h : j < l) (h2 : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + j) + 1) ≠
    rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (bo + j) + 1)) : bphNW (f + 1) m bo o l j = some j := by
  simp only [bphNW]; rw [ite_eq_left h, ite_eq_left h2]
theorem bphNW_next (h : j < l) (h2 : rdW (m.arr64 EREC) (rdW (m.arr64 IW) (o + j) + 1) =
    rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (bo + j) + 1)) :
    bphNW (f + 1) m bo o l j = bphNW f m bo o l (j + 1) := by
  simp only [bphNW]; rw [ite_eq_left h, ite_eq_right (by simpa using h2)]
end arms

theorem bphNLoop_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f bphNLoop
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧
      bphNW f s₀.mem (s₀.loc 0) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) = some (s'.loc 5); ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := bphNLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, ih] <;>
      finish [bphNW_exit, bphNW_brk, bphNW_next]

theorem bphNLoop_step_spec (p : Prog) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ step p (exec p f) bphNLoop
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧
      s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧ s'.loc 4 = s₀.loc 4 ∧
      bphNW (f + 1) s₀.mem (s₀.loc 0) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) = some (s'.loc 5); ⊤⦄ :=
  Triple.step_exec (bphNLoop_spec p (f + 1) s₀)

section model
variable (p : Prog)

/-- After the comparison. -/
def bphK4 (k : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => if r3.headD 0 ≠ 0 then some ([1, k], m3) else some ([0, 0], m3)

/-- After `er_to_iw`. -/
def bphK3 (f : Nat) (k o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => bphK4 k (callW p f "canon_eq_list" [r2.headD 0, r2.tail.headD 0, o, l] m2)

/-- After the name pre-filter; `rest` is the next kind. -/
def bphK2 (f : Nat) (bo bl k o l : Word) (m1 : Mem) (rest : Option (List Word × Mem)) :
    Option Word → Option (List Word × Mem)
  | none => none
  | some j => if j = l then bphK3 p f k o l (callW p f "er_to_iw" [bo, bl] m1) else rest

/-- **The model of the loop over the kinds** at L fuel `f`, from kind `k`: the function's result
(`(0, 0)` when the loop falls through) and the memory. -/
def bphGoW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | f + 1, m, bo, bl, k =>
    if k < 4 then
      match callW p f "rom_basis_decls" [k] m with
      | none => none
      | some (r1, m1) =>
        if r1.tail.headD 0 = bl then
          bphK2 p f bo bl k (r1.headD 0) (r1.tail.headD 0) m1 (bphGoW f m1 bo bl (k + 1))
            (bphNW (f + 1) m1 bo (r1.headD 0) (r1.tail.headD 0) 0)
        else bphGoW f m1 bo bl (k + 1)
    else some ([0, 0], m)

section arms
variable (f : Nat) (m m1 m2 m3 : Mem) (bo bl k o l j : Word) (r1 r2 r3 : List Word)
  (rest : Option (List Word × Mem))
theorem bphK4_some : bphK4 k (some (r3, m3)) =
    if r3.headD 0 ≠ 0 then some ([1, k], m3) else some ([0, 0], m3) := rfl
theorem bphK3_some : bphK3 p f k o l (some (r2, m2)) =
    bphK4 k (callW p f "canon_eq_list" [r2.headD 0, r2.tail.headD 0, o, l] m2) := rfl
theorem bphK2_some : bphK2 p f bo bl k o l m1 rest (some j) =
    if j = l then bphK3 p f k o l (callW p f "er_to_iw" [bo, bl] m1) else rest := rfl
theorem bphGoW_exit (h : ¬ k < 4) : bphGoW p (f + 1) m bo bl k = some ([0, 0], m) := by
  simp only [bphGoW]; rw [ite_eq_right h]
theorem bphGoW_none1 (h : k < 4) (h1 : callW p f "rom_basis_decls" [k] m = none) :
    bphGoW p (f + 1) m bo bl k = none := by
  simp only [bphGoW]; rw [ite_eq_left h, h1]
theorem bphGoW_step (h : k < 4) (h1 : callW p f "rom_basis_decls" [k] m = some (r1, m1)) :
    bphGoW p (f + 1) m bo bl k =
      if r1.tail.headD 0 = bl then
        bphK2 p f bo bl k (r1.headD 0) (r1.tail.headD 0) m1 (bphGoW p f m1 bo bl (k + 1))
          (bphNW (f + 1) m1 bo (r1.headD 0) (r1.tail.headD 0) 0)
      else bphGoW p f m1 bo bl (k + 1) := by
  simp only [bphGoW]; rw [ite_eq_left h, h1]
end arms

grind_pattern [ind_grind] bphK4_some => bphK4 k (some (r3, m3))
grind_pattern [ind_grind] bphK3_some => bphK3 p f k o l (some (r2, m2))
grind_pattern [ind_grind] bphK2_some => bphK2 p f bo bl k o l m1 rest (some j)
grind_pattern [ind_grind] bphGoW_step => bphGoW p (f + 1) m bo bl k, callW p f "rom_basis_decls" [k] m, some (r1, m1)
grind_pattern [ind_grind] bphGoW_none1 => bphGoW p (f + 1) m bo bl k, callW p f "rom_basis_decls" [k] m

theorem bphLoop_spec (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f bphLoop
    ⦃fun r s' => r ≠ .brk ∧
      bphGoW p f s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) = some (r.retOr [0, 0], s'.mem); ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := bphLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, bphNLoop_step_spec p f,
        callW_spec p f "rom_basis_decls", callW_spec p f "er_to_iw",
        callW_spec p f "canon_eq_list"] <;>
      finish [bphGoW_exit]

theorem bph_specW (hp : p.lookup "basis_pin_hit" = some L.Checker.basisPinHitL) (n : Nat) (s₀ : St)
    (bo bl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "basis_pin_hit" [bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧ bphGoW p (n + 1) s₀.mem bo bl 0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, basisPinHitL_eq]
  simp only [callFn, basisPinHitL']
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (bphLoop_spec p (n + 1) s)] <;>
    finish [Sig.retVal, Sig.retOr]

end model

end L.Ind
