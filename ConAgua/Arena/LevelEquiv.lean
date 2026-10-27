module

import ConAgua.Census.Attr
public import ConAgua.Arena.LevelLeq
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.Arena.LevelLeqSpec
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `leq`, `isEquiv`, `isEquivList`: the entries of the level comparison

con-leche's `Level.leq` (`leqCore defaultFuel (simplify l) (simplify r) 0`), `Level.isEquiv`
(structural equality, then equality of the simplified forms, then `leq` both ways, short-circuit)
and `Level.isEquivList` (pairwise, `false` on a length mismatch only after the common prefix
compared equal), Rust `kernel/level.rs:453-500`. `defaultFuel = 10^4` is the literal fuel word
`10000`, the bias of `diff = 0` the literal `2^32`.

* `lv_leq_top(l, r)`: `leq`;
* `lv_equiv(l, r)`: `isEquiv` (it simplifies each side once; con-leche's `leq` simplifies again,
  to the same levels);
* `lv_equivs(a, n, b, k)`: `isEquivList` on two lists of level pointers, the words
  `POOL[a .. a + n)` and `POOL[b .. b + k)` (a level list's slice, `LsStore.lean`), recursive in
  the list.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `lv_leq_top(l, r)`: `leq` -/

/-- After simplifying `l`, then `r`. -/
def ltK₁ (n : Nat) (r : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ltK₂ n x (simpW n m₁ r)
where
  ltK₂ (n : Nat) (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => leqW n m₂ 10000 x y 4294967296

/-- **The model of `lv_leq_top`.** -/
def leqTopW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, l, r => ltK₁ n r (simpW n m l)

section ltArms
variable (n : Nat) (m m₁ : Mem) (l r x y : Word)
theorem leqTopW_succ : leqTopW (n + 1) m l r = ltK₁ n r (simpW n m l) := rfl
theorem ltK₁_some : ltK₁ n r (some (x, m₁)) = ltK₁.ltK₂ n x (simpW n m₁ r) := rfl
theorem ltK₂_some : ltK₁.ltK₂ n x (some (y, m₁)) = leqW n m₁ 10000 x y 4294967296 := rfl
end ltArms

grind_pattern [level_grind] leqTopW_succ => leqTopW (n + 1) m l r
grind_pattern [level_grind] ltK₁_some => ltK₁ n r (some (x, m₁))
grind_pattern [level_grind] ltK₂_some => ltK₁.ltK₂ n x (some (y, m₁))

/-- con-leche: ConLeche/Kernel/Level.lean:144-146 ConLeche.Level.leq
con-leche: ConLeche/Kernel/Level.lean:139-142 ConLeche.Level.defaultFuel -/
@[l_impl ConLeche.Level.leq ConLeche.Level.defaultFuel]
def lvLeqTop : FunDecl := lfn (l, r) locals (x, y) {
  x := call lv_simp(l);
  y := call lv_simp(r);
  x := call lv_leq(10000, x, y, 4294967296);
  return x
}

/-! ## `lv_equiv(l, r)`: `isEquiv` -/

/-- After `lv_eq(l, r)`. -/
def evK₁ (n : Nat) (m : Mem) (l r : Word) : Option Word → Option (Word × Mem)
  | none => none
  | some z => if z ≠ 0 then some (2, m) else evK₂ n r (simpW n m l)
where
  /-- After simplifying `l`. -/
  evK₂ (n : Nat) (r : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (x, m₁) => evK₃ n x (simpW n m₁ r)
  /-- After simplifying `r`. -/
  evK₃ (n : Nat) (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => evK₄ n m₂ x y (lvEqW n m₂ x y)
  /-- After comparing the simplified forms. -/
  evK₄ (n : Nat) (m₂ : Mem) (x y : Word) : Option Word → Option (Word × Mem)
    | none => none
    | some z => if z ≠ 0 then some (2, m₂) else evK₅ n x y (leqW n m₂ 10000 x y 4294967296)
  /-- After `leq l r`. -/
  evK₅ (n : Nat) (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => if z ≠ 2 then some (z, m₃) else leqW n m₃ 10000 y x 4294967296

/-- **The model of `lv_equiv`.** -/
def equivW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, l, r => evK₁ n m l r (lvEqW n m l r)

section evArms
variable (n : Nat) (m m₁ : Mem) (l r x y z : Word)
theorem equivW_succ : equivW (n + 1) m l r = evK₁ n m l r (lvEqW n m l r) := rfl
theorem evK₁_ne (hz : z ≠ 0) : evK₁ n m l r (some z) = some (2, m) := by simp [evK₁, hz]
theorem evK₁_zero : evK₁ n m l r (some 0) = evK₁.evK₂ n r (simpW n m l) := by simp [evK₁]
theorem evK₂_some : evK₁.evK₂ n r (some (x, m₁)) = evK₁.evK₃ n x (simpW n m₁ r) := rfl
theorem evK₃_some : evK₁.evK₃ n x (some (y, m₁)) = evK₁.evK₄ n m₁ x y (lvEqW n m₁ x y) := rfl
theorem evK₄_ne (hz : z ≠ 0) : evK₁.evK₄ n m₁ x y (some z) = some (2, m₁) := by
  simp [evK₁.evK₄, hz]
theorem evK₄_zero : evK₁.evK₄ n m₁ x y (some 0) =
    evK₁.evK₅ n x y (leqW n m₁ 10000 x y 4294967296) := by simp [evK₁.evK₄]
theorem evK₅_stop (hz : z ≠ 2) : evK₁.evK₅ n x y (some (z, m₁)) = some (z, m₁) := by
  simp [evK₁.evK₅, hz]
theorem evK₅_go : evK₁.evK₅ n x y (some (2, m₁)) = leqW n m₁ 10000 y x 4294967296 := by
  simp [evK₁.evK₅]
end evArms

grind_pattern [level_grind] equivW_succ => equivW (n + 1) m l r
grind_pattern [level_grind] evK₁_ne => evK₁ n m l r (some z)
grind_pattern [level_grind] evK₁_zero => evK₁ n m l r (some 0)
grind_pattern [level_grind] evK₂_some => evK₁.evK₂ n r (some (x, m₁))
grind_pattern [level_grind] evK₃_some => evK₁.evK₃ n x (some (y, m₁))
grind_pattern [level_grind] evK₄_ne => evK₁.evK₄ n m₁ x y (some z)
grind_pattern [level_grind] evK₄_zero => evK₁.evK₄ n m₁ x y (some 0)
grind_pattern [level_grind] evK₅_stop => evK₁.evK₅ n x y (some (z, m₁))
grind_pattern [level_grind] evK₅_go => evK₁.evK₅ n x y (some (2, m₁))

/-- con-leche: ConLeche/Kernel/Level.lean:148-167 ConLeche.Level.isEquiv -/
@[l_impl ConLeche.Level.isEquiv]
def lvEquiv : FunDecl := lfn (l, r) locals (x, y, z) {
  z := call lv_eq(l, r);
  if z != 0 { return 2 };
  x := call lv_simp(l);
  y := call lv_simp(r);
  z := call lv_eq(x, y);
  if z != 0 { return 2 };
  z := call lv_leq(10000, x, y, 4294967296);
  if z != 2 { return z };
  z := call lv_leq(10000, y, x, 4294967296);
  return z
}

/-! ## `lv_equivs(a, n, b, k)`: `isEquivList` -/

mutual
/-- **The model of `lv_equivs`.** -/
def equivsW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, a, ln, b, k =>
    if ln = 0 ∨ k = 0 then some (if ln = k then 2 else 1, m)
    else esK n a ln b k (equivW n m (prd m a) (prd m b))
termination_by n _ _ _ _ _ => (n, 0)

/-- After comparing the heads. -/
def esK (n : Nat) (a ln b k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m₁) => if z ≠ 2 then some (z, m₁) else equivsW n m₁ (a + 1) (ln - 1) (b + 1) (k - 1)
termination_by _ => (n, 1)
end

section esArms
variable (n : Nat) (m m₁ : Mem) (a ln b k z : Word)
theorem equivsW_end (h : ln = 0 ∨ k = 0) :
    equivsW (n + 1) m a ln b k = some (if ln = k then 2 else 1, m) := by
  rw [equivsW]; simp [h]
theorem equivsW_cons (h : ¬ (ln = 0 ∨ k = 0)) :
    equivsW (n + 1) m a ln b k =
      esK n a ln b k (equivW n m (prd m a) (prd m b)) := by
  rw [equivsW]; simp only [h, ↓reduceIte]
theorem esK_stop (hz : z ≠ 2) : esK n a ln b k (some (z, m₁)) = some (z, m₁) := by
  rw [esK]; simp [hz]
theorem esK_go : esK n a ln b k (some (2, m₁)) =
    equivsW n m₁ (a + 1) (ln - 1) (b + 1) (k - 1) := by rw [esK]; simp
end esArms

grind_pattern [level_grind] equivsW_end => equivsW (n + 1) m a ln b k
grind_pattern [level_grind] equivsW_cons => equivsW (n + 1) m a ln b k
grind_pattern [level_grind] esK_stop => esK n a ln b k (some (z, m₁))
grind_pattern [level_grind] esK_go => esK n a ln b k (some (2, m₁))

/-- con-leche: ConLeche/Kernel/Level.lean:169-175 ConLeche.Level.isEquivList -/
@[l_impl ConLeche.Level.isEquivList]
def lvEquivs : FunDecl := lfn (a, n, b, k) locals (z) {
  if n == 0 || k == 0 { if n == k { return 2 }; return 1 };
  z := call lv_equiv(POOL⦃a⦄, POOL⦃b⦄);
  if z != 2 { return z };
  z := call lv_equivs(a + 1, n - 1, b + 1, k - 1);
  return z
}

/-! ## The specs -/

section specs
variable (p : Prog) (hp : LevelProg p)

include hp in
theorem lvLeqTop_spec (hpt : p.lookup "lv_leq_top" = some lvLeqTop) (n : Nat) (s₀ : St)
    (l r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_leq_top" [l, r]
    ⦃fun res s' => LocEq s' s₀ ∧ leqTopW n s₀.mem l r = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpt]
  simp only [callFn, lvLeqTop]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        lvSimp_spec p hp.node hp.alloc hp.comb hp.simp n, (leqSpecs p hp n).1] <;>
      finish (gen := 20)

include hp in
theorem lvEquiv_spec (hpe : p.lookup "lv_equiv" = some lvEquiv) (n : Nat) (s₀ : St) (l r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_equiv" [l, r]
    ⦃fun res s' => LocEq s' s₀ ∧ equivW n s₀.mem l r = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpe]
  simp only [callFn, lvEquiv]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvEq_spec p hp.node hp.eq n,
        lvSimp_spec p hp.node hp.alloc hp.comb hp.simp n, (leqSpecs p hp n).1] <;>
      finish (gen := 20)

include hp in
theorem lvEquivs_spec (hpe : p.lookup "lv_equiv" = some lvEquiv)
    (hps : p.lookup "lv_equivs" = some lvEquivs) (n : Nat) : ∀ (s₀ : St) (a ln b k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_equivs" [a, ln, b, k]
    ⦃fun res s' => LocEq s' s₀ ∧ equivsW n s₀.mem a ln b k = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ a ln b k; rw [invoke_eq _ hps]; simp only [callFn, lvEquivs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ a ln b k
    rw [invoke_eq _ hps]
    simp only [callFn, lvEquivs]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lvEquiv_spec p hp hpe n, ih] <;>
      finish (gen := 20)

/-! ## `lvl_eq(u, v)`: the twin's `lvlEq?`, without its cache -/

/-- **The model of `lvl_eq`**: reset the heap, then `lv_equiv`. -/
def lvlEqW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, u, v => equivW n (m.set64 CTL 192 0) u v

/-- con-ron's `lvlEq?` (`Arena/Core.lean:129`) on two level handles: the level algorithm on a
fresh heap (the top reset to `0`). The verdict cache `lvlEqC` is `lvl_eq_c`'s, in front of this
function (`CoreLevels.lean`); this is the uncached computation (`LevelArena.lean`,
`lvlEq_refines`). -/
-- con-ron: ConRon/Arena/Core.lean:132-149 ConRon.Arena.lvlEq?
@[l_impl ConRon.Arena.lvlEq?]
def lvlEqL : FunDecl := lfn (u, v) locals (z) {
  CTL.u64[192] := 0;
  z := call lv_equiv(u, v);
  return z
}

include hp in
theorem lvlEq_spec (hpe : p.lookup "lv_equiv" = some lvEquiv) (hpl : p.lookup "lvl_eq" = some lvlEqL)
    (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lvl_eq" [u, v]
    ⦃fun res s' => LocEq s' s₀ ∧ lvlEqW n s₀.mem u v = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpl]
  simp only [callFn, lvlEqL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, lvEquiv_spec p hp hpe n] <;>
      finish (gen := 20) [lvlEqW]

end specs

/-! ## `lvls_eq(us, vs)`: the twin's `lvlsEq?`, without its cache -/

/-- **The model of `ls_node`**: the slice `[offset, length]` of a level-list handle, `[]` where the
L code aborts (a tag other than `0`, a closed scratch tier, an index past the count). -/
def lsNodeW (m : Mem) (h : Word) : List Word :=
  if h >>> 28 ≠ 0 then []
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then []
  else if tcnt m LVLS (tierW h) ≤ idxW h then []
  else [tfld m LVLS (tierW h) (idxW h) 0, tfld m LVLS (tierW h) (idxW h) 1]

/-- con-ron: ConRon/Arena/Monad.lean:491-497 ConRon.Arena.viewLs -/
def lsNode : FunDecl := lfn (h) locals (t, i) {
  if h >> 28 != 0 { abort };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LVLS⟨t⟩.count <= i { abort };
  return (LVLS⟨t, i⟩.o, LVLS⟨t, i⟩.l)
}

theorem lsNode_spec (p : Prog) (hp : p.lookup "ls_node" = some lsNode) (n : Nat) (s₀ : St)
    (q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_node" [q]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = lsNodeW s₀.mem q; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lsNode]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld,
        evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
      finish [lsNodeW, tierW, idxW]

/-- **The model of `lvls_eq`**: the two slices (none on a handle `ls_node` aborts on), the heap
reset, `lv_equivs`. -/
def lvlsEqW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, us, vs =>
    if lsNodeW m us = [] ∨ lsNodeW m vs = [] then none else
    equivsW n (m.set64 CTL 192 0) ((lsNodeW m us).headD 0) ((lsNodeW m us).tail.headD 0)
      ((lsNodeW m vs).headD 0) ((lsNodeW m vs).tail.headD 0)

/-- con-ron's `lvlsEq?` (`Arena/Core.lean:155`) on two level-list handles: `isEquivList` on their
slices, on a fresh heap; the verdict cache `lvlsEqC` is not represented (as for `lvl_eq`). -/
-- con-ron: ConRon/Arena/Core.lean:151-168 ConRon.Arena.lvlsEq?
@[l_impl ConRon.Arena.lvlsEq?]
def lvlsEqL : FunDecl := lfn (us, vs) locals (a, n, b, k, z) {
  (a, n) := call ls_node(us);
  (b, k) := call ls_node(vs);
  CTL.u64[192] := 0;
  z := call lv_equivs(a, n, b, k);
  return z
}

section lists
variable (p : Prog) (hp : LevelProg p)

include hp in
theorem lvlsEq_spec (hpe : p.lookup "lv_equiv" = some lvEquiv)
    (hps : p.lookup "lv_equivs" = some lvEquivs) (hpn : p.lookup "ls_node" = some lsNode)
    (hpl : p.lookup "lvls_eq" = some lvlsEqL) (n : Nat) (s₀ : St) (us vs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lvls_eq" [us, vs]
    ⦃fun res s' => LocEq s' s₀ ∧ lvlsEqW n s₀.mem us vs = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpl]
  simp only [callFn, lvlsEqL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, lsNode_spec p hpn n,
        lvEquivs_spec p hp hpe hps n] <;>
      finish (gen := 20) [lvlsEqW]

end lists

/-! ## The program -/

/-- The level functions, as one program. -/
def levelProg : Prog :=
  [("lv_node", lvNode), ("lh_mk", lhMk), ("lv_eq", lvEq), ("lv_comb", lvComb), ("lv_simp", lvSimp),
    ("lv_nz", lvNz), ("lv_subst", lvSubst), ("lv_subsimp", lvSubsimp), ("lv_dist1", lvDist1),
    ("lv_dist2", lvDist2), ("lv_leq", lvLeq), ("lv_rest", lvRest), ("lv_imax", lvImax),
    ("lv_imax_l", lvImaxL), ("lv_imax_r", lvImaxR), ("lv_cases", lvCases),
    ("lv_cases_at", lvCasesAt), ("lv_leq_top", lvLeqTop), ("lv_equiv", lvEquiv),
    ("lv_equivs", lvEquivs), ("lvl_eq", lvlEqL), ("ls_node", lsNode), ("lvls_eq", lvlsEqL)]

end L.Arena
