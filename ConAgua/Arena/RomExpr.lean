import ConAgua.Arena.RomLevels
import ConLeche.Verify.Cached.Erase
import ConAgua.Census.Attr

/-!
# The ROM's expressions: `rom_expr(pos)` refines `internExprGo`, its memo mirrored

`internExprGo m e` (`Arena/Frontend/Readback.lean`) interns a con-leche expression tree,
memoised at the compound nodes (`fvar`, `app`, `lam`, `forallE`, `letE`, `proj`) on the subterms
already interned in the same call (`EMemo`, keyed by value). L mirrors the memo **exactly** without
comparing trees: the encoder (`encExprM`) threads the list `seen` of the compound subterms the
twin's memo holds at each point, and where the twin's memo hits it emits a **back reference** (tag
`9`, the index in `seen`) instead of the subtree; L keeps the handle of the `k`-th memo entry in
`RMEMO[k]` (array 139, count `CTL[132]`, reset per call by the caller). The relation (`MemoR`:
the count is `seen.length`, `RMEMO[k]` decodes to the twin's `m[seen[k]]`, and every key of `m` is
in `seen`) is all the proof needs; the ROM's contents are never evaluated.

Tags: `0` bvar (index), `1` sort (level), `2` const (name, levels), `4` fvar (index, type), `5`
app, `6` lam, `7` forallE, `8` letE, `9` back reference, `10` proj (name, index, structure). A
literal has no encoding (`exprFits`): no constant datum of the checker contains one.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Rom

open L.Arena

/-- The memo of the expression interner. -/
abbrev RMEMO : ArrId := 139

/-- Its count, `CTL[132]`. -/
def memoCnt (m : Mem) : Word := rdW (m.arr64 CTL) 132

/-! ## The encoding -/

/-- **An expression, with the twin's memo**: `seen` the compound subterms interned so far in the
call (in insertion order); returns the bytes and the list after. -/
def encExprM (seen : List ConLeche.Expr) : ConLeche.Expr → List UInt8 × List ConLeche.Expr
  | .bvar i => (0 :: u64B i, seen)
  | .sort u => (1 :: encLevel u, seen)
  | .const n us => (2 :: (encName n ++ encLevels us), seen)
  | .lit _ => ([3], seen)
  | e@(.fvar i ty) =>
    if e ∈ seen then (9 :: u64B (seen.idxOf e), seen) else
      let r := encExprM seen ty
      (4 :: (u64B i ++ r.1), r.2 ++ [e])
  | e@(.app f a) =>
    if e ∈ seen then (9 :: u64B (seen.idxOf e), seen) else
      let r₁ := encExprM seen f
      let r₂ := encExprM r₁.2 a
      (5 :: (r₁.1 ++ r₂.1), r₂.2 ++ [e])
  | e@(.lam ty b) =>
    if e ∈ seen then (9 :: u64B (seen.idxOf e), seen) else
      let r₁ := encExprM seen ty
      let r₂ := encExprM r₁.2 b
      (6 :: (r₁.1 ++ r₂.1), r₂.2 ++ [e])
  | e@(.forallE ty b) =>
    if e ∈ seen then (9 :: u64B (seen.idxOf e), seen) else
      let r₁ := encExprM seen ty
      let r₂ := encExprM r₁.2 b
      (7 :: (r₁.1 ++ r₂.1), r₂.2 ++ [e])
  | e@(.letE ty v b) =>
    if e ∈ seen then (9 :: u64B (seen.idxOf e), seen) else
      let r₁ := encExprM seen ty
      let r₂ := encExprM r₁.2 v
      let r₃ := encExprM r₂.2 b
      (8 :: (r₁.1 ++ r₂.1 ++ r₃.1), r₃.2 ++ [e])
  | e@(.proj n i sub) =>
    if e ∈ seen then (9 :: u64B (seen.idxOf e), seen) else
      let r := encExprM seen sub
      (10 :: (encName n ++ u64B i ++ r.1), r.2 ++ [e])

/-! ## `memo_push(h)`, `rom_expr(pos)` -/

/-- con-ron: none — the L memo of the ROM expression interner (the twin's `EMemo` insert). -/
def memoPush : FunDecl := lfn (h) locals (o) {
  o := CTL.u64[132];
  if len(RMEMO.u64) <= o { abort };
  RMEMO.u64[o] := h;
  CTL.u64[132] := o + 1;
  return 0
}

/-- The memory after recording `h`. -/
def mpushMem (m : Mem) (h : Word) : Mem := (m.set64 RMEMO (memoCnt m) h).set64 CTL 132 (memoCnt m + 1)

theorem memoPush_spec (p : Prog) (hp : p.lookup "memo_push" = some memoPush) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "memo_push" [h]
    ⦃fun _ s' => LocEq s' s₀ ∧ memoCnt s₀.mem < s₀.mem.len64 RMEMO ∧
      s'.mem = mpushMem s₀.mem h; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [mpushMem, memoCnt]

/-- The back reference `k` is to an entry of the memo. -/
def memoOk (m : Mem) (k : Word) : Prop := k < memoCnt m

instance (m : Mem) (k : Word) : Decidable (memoOk m k) := by unfold memoOk; infer_instance


/-- `memo_get(k)`: memo entry `k` (abort past the count).
con-ron: none — the L memo's lookup (the twin's `EMemo` hit). -/
def memoGet : FunDecl := lfn (k) locals () {
  if CTL.u64[132] <= k { abort };
  return RMEMO.u64[k]
}

theorem memoGet_spec (p : Prog) (hp : p.lookup "memo_get" = some memoGet) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "memo_get" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ memoOk s₀.mem k ∧ r = [rdW (s₀.mem.arr64 RMEMO) k]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoGet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [memoOk, memoCnt]

section prog
variable (rom : List UInt8)

/-- `rom_ex_ref(pos)`: a back reference: memo entry `u64 at pos + 1`. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:189-251 ConRon.Arena.Frontend.internExprGo
@[l_impl ConRon.Arena.Frontend.internExprGo]
def romExRef : FunDecl := lfn (pos) locals (k, h) {
  k := call rom_u64(pos + 1);
  h := call memo_get(k);
  return (h, pos + 9)
}

/-- The model of `rom_ex_ref`. -/
def romRefW (m : Mem) (pos : Word) : Option (Word × Word × Mem) :=
  if memoOk m (u64W rom (pos + 1)) then some (rdW (m.arr64 RMEMO) (u64W rom (pos + 1)), pos + 9, m)
  else none

/-- `rom_ex_leaf(pos, t)`: a `bvar` (`t = 0`), `sort` (`1`) or `const` (`2`) node. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:189-251 ConRon.Arena.Frontend.internExprGo
@[l_impl ConRon.Arena.Frontend.internExprGo]
def romExLeaf : FunDecl := lfn (pos, t) locals (h, q, a, b, k) {
  if t == 0 {
    k := call rom_u64(pos + 1);
    h := call intern_bvar(k);
    if h >= 4294967296 { abort };
    return (h, pos + 9)
  };
  if t == 1 {
    (a, q) := call rom_level(pos + 1);
    h := call intern_sort(a);
    if h >= 4294967296 { abort };
    return (h, q)
  };
  if t != 2 { abort };
  (a, q) := call rom_name(pos + 1);
  (b, q) := call rom_levels(q);
  h := call intern_const(a, b);
  if h >= 4294967296 { abort };
  return (h, q)
}

/-- con-ron: ConRon/Arena/Frontend/Readback.lean:189-251 ConRon.Arena.Frontend.internExprGo -/
@[l_impl ConRon.Arena.Frontend.internExprGo]
def romExpr : FunDecl := lfn (pos) locals (t, h, q, k) {
  t := rom.c8[pos];
  if t == 9 {
    (h, q) := call rom_ex_ref(pos);
    return (h, q)
  };
  if t == 0 || t == 1 || t == 2 {
    (h, q) := call rom_ex_leaf(pos, t);
    return (h, q)
  };
  if t == 4 || t == 10 {
    (h, q) := call rom_ex_one(pos, t);
    return (h, q)
  };
  (h, q) := call rom_ex_two(pos, t);
  return (h, q)
}

/-- `rom_ex_one(pos, t)`: an `fvar` (`t = 4`) or a `proj` (`t = 10`) node. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:189-251 ConRon.Arena.Frontend.internExprGo
@[l_impl ConRon.Arena.Frontend.internExprGo]
def romExOne : FunDecl := lfn (pos, t) locals (h, q, a, b, k, z) {
  if t == 4 {
    k := call rom_u64(pos + 1);
    (a, q) := call rom_expr(pos + 9);
    h := call intern_fvar(k, a);
    if h >= 4294967296 { abort };
    z := call memo_push(h);
    return (h, q)
  };
  if t != 10 { abort };
  (a, q) := call rom_name(pos + 1);
  k := call rom_u64(q);
  (b, q) := call rom_expr(q + 8);
  h := call mk_proj(a, k, b);
  if h >= 4294967296 { abort };
  z := call memo_push(h);
  return (h, q)
}

/-- `rom_ex_two(pos, t)`: an `app`/`lam`/`forallE` (`t` = 5, 6, 7) or `letE` (`8`) node. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:189-251 ConRon.Arena.Frontend.internExprGo
@[l_impl ConRon.Arena.Frontend.internExprGo]
def romExTwo : FunDecl := lfn (pos, t) locals (h, q, a, b, c, z) {
  (a, q) := call rom_expr(pos + 1);
  (b, q) := call rom_expr(q);
  if t == 5 {
    h := call mk_app(a, b);
    if h >= 4294967296 { abort };
    z := call memo_push(h);
    return (h, q)
  };
  if t == 6 {
    h := call mk_lam(a, b);
    if h >= 4294967296 { abort };
    z := call memo_push(h);
    return (h, q)
  };
  if t == 7 {
    h := call mk_forall(a, b);
    if h >= 4294967296 { abort };
    z := call memo_push(h);
    return (h, q)
  };
  if t != 8 { abort };
  (c, q) := call rom_expr(q);
  h := call mk_let(a, b, c);
  if h >= 4294967296 { abort };
  z := call memo_push(h);
  return (h, q)
}

/-- A leaf interned: the handle checked. -/
def exLeafK (q : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h, m') => if 4294967296 ≤ h then none else some (h, q, m')

/-- A compound node interned: the handle checked, then recorded in the memo. -/
def exNodeK (q : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h, m') =>
    if 4294967296 ≤ h then none
    else if memoCnt m' < m'.len64 RMEMO then some (h, q, mpushMem m' h) else none

/-- After a sort's level. -/
def exSortK : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (a, q, m₁) => exLeafK q (sointernW m₁ a)

/-- After a constant's levels. -/
def exConst2K (a : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (b, q, m₂) => exLeafK q (ceinternW m₂ a b)

/-- After a constant's name. -/
def exConst2KN (n : Nat) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (a, q, m₁) => exConst2K a (romLevelsW rom n m₁ q)

/-- After the second operand. -/
def exTwoK (t a : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (b, q, m₂) =>
    if t = 5 then exNodeK q (mkAppW m₂ a b)
    else if t = 6 then exNodeK q (mkLamW m₂ a b)
    else if t = 7 then exNodeK q (mkForallW m₂ a b)
    else none

/-- The model of `rom_ex_leaf`. -/
def romLeafW : Nat → Mem → Word → Word → Option (Word × Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, pos, t =>
    if t = 0 then exLeafK (pos + 9) (binternW m (u64W rom (pos + 1)))
    else if t = 1 then exSortK (romLevelW rom n m (pos + 1))
    else if t = 2 then exConst2KN rom n (romNameW rom n m (pos + 1))
    else none

mutual
/-- **The model of `rom_expr`** at L fuel `n`. -/
def romExprW : Nat → Mem → Word → Option (Word × Word × Mem)
  | 0, _, _ => none
  | n + 1, m, pos =>
    if romB rom pos = 9 then romRefW rom m pos
    else if romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2 then romLeafW rom n m pos (romB rom pos)
    else if romB rom pos = 4 ∨ romB rom pos = 10 then romOneW n m pos (romB rom pos)
    else romTwoW n m pos (romB rom pos)

/-- The model of `rom_ex_one`. -/
def romOneW : Nat → Mem → Word → Word → Option (Word × Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, pos, t =>
    if t = 4 then exFvarK (u64W rom (pos + 1)) (romExprW n m (pos + 9))
    else if t = 10 then exProjK n (romNameW rom n m (pos + 1))
    else none

/-- The model of `rom_ex_two`. -/
def romTwoW : Nat → Mem → Word → Word → Option (Word × Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, pos, t => exOneK n t (romExprW n m (pos + 1))

/-- After an fvar's type. -/
def exFvarK (k : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (a, q, m₁) => exNodeK q (fvinternW m₁ k a)

/-- After a projection's name. -/
def exProjK (n : Nat) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (a, q, m₁) => exProj2K a (u64W rom q) (romExprW n m₁ (q + 8))

/-- After a projection's structure. -/
def exProj2K (a k : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (b, q, m₂) => exNodeK q (mkProjW m₂ a k b)

/-- After the first operand. -/
def exOneK (n : Nat) (t : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (a, q, m₁) =>
    if t = 8 then exLet2K n a (romExprW n m₁ q) else exTwoK t a (romExprW n m₁ q)

/-- A `letE` after its type. -/
def exLet2K (n : Nat) (a : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (b, q, m₂) => exLet3K a b (romExprW n m₂ q)

/-- A `letE` after its value. -/
def exLet3K (a b : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (c, q, m₃) => exNodeK q (mkLetW m₃ a b c)
end

end prog

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ m₂ m₃ : Mem) (pos q t a b c k h : Word)

theorem exLeafK_some (hh : ¬ 4294967296 ≤ h) : exLeafK q (some (h, m)) = some (h, q, m) := by
  simp [exLeafK, hh]
theorem exNodeK_some (hh : ¬ 4294967296 ≤ h) (hc : memoCnt m < m.len64 RMEMO) :
    exNodeK q (some (h, m)) = some (h, q, mpushMem m h) := by simp [exNodeK, hh, hc]
theorem exSortK_some : exSortK (some (a, q, m)) = exLeafK q (sointernW m a) := rfl
theorem exConst2K_some : exConst2K a (some (b, q, m)) = exLeafK q (ceinternW m a b) := rfl
theorem exTwoK_app (ht : t = 5) : exTwoK t a (some (b, q, m)) = exNodeK q (mkAppW m a b) := by
  simp [exTwoK, ht]
theorem exTwoK_lam (ht : t = 6) : exTwoK t a (some (b, q, m)) = exNodeK q (mkLamW m a b) := by
  simp [exTwoK, ht]
theorem exTwoK_forall (ht : t = 7) : exTwoK t a (some (b, q, m)) = exNodeK q (mkForallW m a b) := by
  simp [exTwoK, ht]
theorem exConst2KN_some : exConst2KN rom n (some (a, q, m)) = exConst2K a (romLevelsW rom n m q) := by
  simp [exConst2KN]
theorem romLeafW_bvar (ht : t = 0) :
    romLeafW rom (n + 1) m pos t = exLeafK (pos + 9) (binternW m (u64W rom (pos + 1))) := by
  simp [romLeafW, ht]
theorem romLeafW_sort (ht0 : t ≠ 0) (ht : t = 1) :
    romLeafW rom (n + 1) m pos t = exSortK (romLevelW rom n m (pos + 1)) := by simp [romLeafW, ht0, ht]
theorem romLeafW_const (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht : t = 2) :
    romLeafW rom (n + 1) m pos t = exConst2KN rom n (romNameW rom n m (pos + 1)) := by
  simp [romLeafW, ht0, ht1, ht]
theorem exFvarK_some : exFvarK rom k (some (a, q, m)) = exNodeK q (fvinternW m k a) := by simp [exFvarK]
theorem exProjK_some : exProjK rom n (some (a, q, m)) = exProj2K rom a (u64W rom q) (romExprW rom n m (q + 8)) := by
  simp [exProjK]
theorem exProj2K_some : exProj2K rom a k (some (b, q, m)) = exNodeK q (mkProjW m a k b) := by simp [exProj2K]
theorem exOneK_let (ht : t = 8) : exOneK rom n t (some (a, q, m)) = exLet2K rom n a (romExprW rom n m q) := by
  simp [exOneK, ht]
theorem exOneK_two (ht : t ≠ 8) : exOneK rom n t (some (a, q, m)) = exTwoK t a (romExprW rom n m q) := by
  simp [exOneK, ht]
theorem exLet2K_some : exLet2K rom n a (some (b, q, m)) = exLet3K rom a b (romExprW rom n m q) := by
  simp [exLet2K]
theorem exLet3K_some : exLet3K rom a b (some (c, q, m)) = exNodeK q (mkLetW m a b c) := by simp [exLet3K]

theorem romExprW_ref (h9 : romB rom pos = 9) :
    romExprW rom (n + 1) m pos = romRefW rom m pos := by
  simp [romExprW, h9]
theorem romExprW_leaf (h9 : romB rom pos ≠ 9) (h2 : romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2) :
    romExprW rom (n + 1) m pos = romLeafW rom n m pos (romB rom pos) := by
  simp [romExprW, h9, h2]
theorem romExprW_one (h9 : romB rom pos ≠ 9) (h2 : ¬ (romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2))
    (h4 : romB rom pos = 4 ∨ romB rom pos = 10) :
    romExprW rom (n + 1) m pos = romOneW rom n m pos (romB rom pos) := by
  simp only [romExprW, h9, h2, h4, ite_false, ite_true]
theorem romExprW_two (h9 : romB rom pos ≠ 9) (h2 : ¬ (romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2))
    (h4 : ¬ (romB rom pos = 4 ∨ romB rom pos = 10)) :
    romExprW rom (n + 1) m pos = romTwoW rom n m pos (romB rom pos) := by
  simp only [romExprW, h9, h2, h4, ite_false]
theorem romOneW_fvar (ht : t = 4) :
    romOneW rom (n + 1) m pos t = exFvarK rom (u64W rom (pos + 1)) (romExprW rom n m (pos + 9)) := by
  simp [romOneW, ht]
theorem romOneW_proj (ht4 : t ≠ 4) (ht : t = 10) :
    romOneW rom (n + 1) m pos t = exProjK rom n (romNameW rom n m (pos + 1)) := by
  simp [romOneW, ht4, ht]
theorem romTwoW_eq : romTwoW rom (n + 1) m pos t = exOneK rom n t (romExprW rom n m (pos + 1)) := by
  simp [romTwoW]
end arms

attribute [arena_grind =] exLeafK_some exSortK_some exConst2K_some exTwoK_app exTwoK_lam exTwoK_forall
  exConst2KN_some exFvarK_some exProjK_some exProj2K_some exOneK_let exOneK_two exLet2K_some exLet3K_some
grind_pattern [arena_grind] exNodeK_some => exNodeK q (some (h, m))
grind_pattern [arena_grind] romExprW_ref => romExprW rom (n + 1) m pos
grind_pattern [arena_grind] romExprW_leaf => romExprW rom (n + 1) m pos
grind_pattern [arena_grind] romLeafW_bvar => romLeafW rom (n + 1) m pos t
grind_pattern [arena_grind] romLeafW_sort => romLeafW rom (n + 1) m pos t
grind_pattern [arena_grind] romLeafW_const => romLeafW rom (n + 1) m pos t
grind_pattern [arena_grind] romExprW_one => romExprW rom (n + 1) m pos
grind_pattern [arena_grind] romExprW_two => romExprW rom (n + 1) m pos
grind_pattern [arena_grind] romOneW_fvar => romOneW rom (n + 1) m pos t
grind_pattern [arena_grind] romOneW_proj => romOneW rom (n + 1) m pos t
attribute [arena_grind =] romTwoW_eq

/-- The functions `rom_expr` calls. -/
structure ExprProg (rom : List UInt8) (p : Prog) : Prop extends LevelsProg rom p where
  rom_expr : p.lookup "rom_expr" = some (romExpr rom)
  rom_ex_leaf : p.lookup "rom_ex_leaf" = some romExLeaf
  memo_get : p.lookup "memo_get" = some memoGet
  rom_ex_ref : p.lookup "rom_ex_ref" = some romExRef
  rom_ex_one : p.lookup "rom_ex_one" = some romExOne
  rom_ex_two : p.lookup "rom_ex_two" = some romExTwo
  memo_push : p.lookup "memo_push" = some memoPush
  bvar_find : p.lookup "bvar_find" = some bvarFind
  bvar_push : p.lookup "bvar_push" = some bvarPush
  intern_bvar : p.lookup "intern_bvar" = some internBVar
  sort_find : p.lookup "sort_find" = some sortFind
  sort_push : p.lookup "sort_push" = some sortPush
  intern_sort : p.lookup "intern_sort" = some internSort
  const_find : p.lookup "const_find" = some constFind
  const_push : p.lookup "const_push" = some constPush
  intern_const : p.lookup "intern_const" = some internConst
  fvar_find : p.lookup "fvar_find" = some fvarFind
  fvar_push : p.lookup "fvar_push" = some fvarPush
  intern_fvar : p.lookup "intern_fvar" = some internFVar
  der_b : p.lookup "der_b" = some derB
  app_find : p.lookup "app_find" = some appFind
  app_push : p.lookup "app_push" = some appPush
  intern_app : p.lookup "intern_app" = some internApp
  mk_app : p.lookup "mk_app" = some mkApp
  lam_find : p.lookup "lam_find" = some lamFind
  lam_push : p.lookup "lam_push" = some lamPush
  intern_lam : p.lookup "intern_lam" = some internLamL
  mk_lam : p.lookup "mk_lam" = some mkLam
  forall_find : p.lookup "forall_find" = some forallFind
  forall_push : p.lookup "forall_push" = some forallPush
  intern_forall : p.lookup "intern_forall" = some internForallL
  mk_forall : p.lookup "mk_forall" = some mkForall
  letE_find : p.lookup "letE_find" = some letFind
  letE_push : p.lookup "letE_push" = some letPush
  intern_letE : p.lookup "intern_letE" = some internLet
  mk_let : p.lookup "mk_let" = some mkLet
  proj_find : p.lookup "proj_find" = some projFind
  proj_push : p.lookup "proj_push" = some projPush
  intern_proj : p.lookup "intern_proj" = some internProj
  mk_proj : p.lookup "mk_proj" = some mkProj

section spec
variable (rom : List UInt8) (p : Prog) (hL : ExprProg rom p)
include hL

/-- `rom_expr`'s spec at L fuel `n`. -/
def SpecE (rom : List UInt8) (p : Prog) (n : Nat) : Prop :=
  ∀ (s₀ : St) (pos : Word), (s₀.mem.arr64 POOL).size < 2 ^ 63 →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rom_expr" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ romExprW rom n s₀.mem pos = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄
/-- `rom_ex_one`'s. -/
def SpecO (rom : List UInt8) (p : Prog) (n : Nat) : Prop :=
  ∀ (s₀ : St) (pos t : Word), (s₀.mem.arr64 POOL).size < 2 ^ 63 →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rom_ex_one" [pos, t]
    ⦃fun r s' => LocEq s' s₀ ∧ romOneW rom n s₀.mem pos t = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄
/-- `rom_ex_two`'s. -/
def SpecT (rom : List UInt8) (p : Prog) (n : Nat) : Prop :=
  ∀ (s₀ : St) (pos t : Word), (s₀.mem.arr64 POOL).size < 2 ^ 63 →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rom_ex_two" [pos, t]
    ⦃fun r s' => LocEq s' s₀ ∧ romTwoW rom n s₀.mem pos t = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄
/-- The three specs at L fuel `n`. -/
def ExprSpecs (rom : List UInt8) (p : Prog) (n : Nat) : Prop :=
  SpecE rom p n ∧ SpecO rom p n ∧ SpecT rom p n

theorem romExLeaf_specW (n : Nat) (s₀ : St) (pos t : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rom_ex_leaf" [pos, t]
    ⦃fun r s' => LocEq s' s₀ ∧ romLeafW rom n s₀.mem pos t = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.rom_ex_leaf]
  simp only [callFn, romExLeaf]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hn' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (romName_specW rom p hL.toNameProg n s₁ pos₁ h₁)
    have hl' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (romLevel_specW rom p hL.toLevelProg n s₁ pos₁ h₁)
    have hls' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8
      (romLevels_specW rom p hL.toLevelsProg n s₁ pos₁ h₁)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hn', hl', hls',
        romU64_spec rom p hL.rom_u64 n,
        internBVar_spec p hL.bvar_find hL.bvar_push hL.intern_bvar n,
        internSort_spec p hL.sort_find hL.sort_push hL.intern_sort n,
        internConst_spec p hL.const_find hL.const_push hL.intern_const n] <;>
      finish [Keep.size]

theorem romRefW_ok (m : Mem) (pos : Word) (h : memoOk m (u64W rom (pos + 1))) :
    romRefW rom m pos = some (rdW (m.arr64 RMEMO) (u64W rom (pos + 1)), pos + 9, m) := by
  simp only [romRefW]; rw [if_pos h]

attribute [local irreducible] u64W memoOk in
theorem romExRef_specW (n : Nat) (s₀ : St) (pos : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rom_ex_ref" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ romRefW rom s₀.mem pos = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.rom_ex_ref]
  simp only [callFn, romExRef]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, romU64_spec rom p hL.rom_u64 n,
        memoGet_spec p hL.memo_get n] <;>
      finish [romRefW]

theorem romExpr_stepE (n : Nat) (ih : ExprSpecs rom p n) : SpecE rom p (n + 1) := by
  obtain ⟨_, ihO, ihT⟩ := ih
  unfold SpecO at ihO; unfold SpecT at ihT
  intro s₀ pos hs
  have hO := fun s₁ pos₁ t₁ h₁ => Triple.keep hL.no_st8 (ihO s₁ pos₁ t₁ h₁)
  have hT := fun s₁ pos₁ t₁ h₁ => Triple.keep hL.no_st8 (ihT s₁ pos₁ t₁ h₁)
  have hLf := fun s₁ pos₁ t₁ h₁ => Triple.keep hL.no_st8 (romExLeaf_specW rom p hL n s₁ pos₁ t₁ h₁)
  rw [invoke_eq _ hL.rom_expr]
  simp only [callFn, romExpr]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ldc, hLf, hO, hT,
      romExRef_specW rom p hL n] <;>
    finish [Keep.size]

theorem romExpr_stepO (n : Nat) (ih : ExprSpecs rom p n) : SpecO rom p (n + 1) := by
  obtain ⟨ihE, _, _⟩ := ih
  unfold SpecE at ihE
  intro s₀ pos t hs
  have hE := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (ihE s₁ pos₁ h₁)
  have hn' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (romName_specW rom p hL.toNameProg n s₁ pos₁ h₁)
  have hmp := fun s₁ h₁ => Triple.keep hL.no_st8 (memoPush_spec p hL.memo_push n s₁ h₁)
  rw [invoke_eq _ hL.rom_ex_one]
  simp only [callFn, romExOne]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hn', hE, hmp,
      romU64_spec rom p hL.rom_u64 n,
      internFVar_spec p hL.fvar_find hL.fvar_push hL.intern_fvar n,
      mkProj_spec p hL.der_b hL.proj_find hL.proj_push hL.intern_proj hL.mk_proj n] <;>
    finish [Keep.size, memoCnt]

theorem romExpr_stepT (n : Nat) (ih : ExprSpecs rom p n) : SpecT rom p (n + 1) := by
  obtain ⟨ihE, _, _⟩ := ih
  unfold SpecE at ihE
  intro s₀ pos t hs
  have hE := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (ihE s₁ pos₁ h₁)
  have hmp := fun s₁ h₁ => Triple.keep hL.no_st8 (memoPush_spec p hL.memo_push n s₁ h₁)
  rw [invoke_eq _ hL.rom_ex_two]
  simp only [callFn, romExTwo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hE, hmp,
      mkApp_spec p hL.der_b hL.app_find hL.app_push hL.intern_app hL.mk_app n,
      mkLam_spec p hL.der_b hL.lam_find hL.lam_push hL.intern_lam hL.mk_lam n,
      mkForall_spec p hL.der_b hL.forall_find hL.forall_push hL.intern_forall hL.mk_forall n,
      mkLet_spec p hL.der_b hL.letE_find hL.letE_push hL.intern_letE hL.mk_let n] <;>
    finish (gen := 16) [Keep.size, memoCnt]

/-- **`rom_expr`, `rom_ex_one`, `rom_ex_two` compute their models.** -/
theorem romExpr_specsW (n : Nat) : ExprSpecs rom p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ pos _ => ?_, fun s₀ pos t _ => ?_, fun s₀ pos t _ => ?_⟩
    · rw [invoke_eq _ hL.rom_expr]; simp only [callFn, romExpr]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hL.rom_ex_one]; simp only [callFn, romExOne]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hL.rom_ex_two]; simp only [callFn, romExTwo]; vcgen [exec] <;> grind
  | succ n ih =>
    exact ⟨romExpr_stepE rom p hL n ih, romExpr_stepO rom p hL n ih, romExpr_stepT rom p hL n ih⟩

end spec

end L.Rom
