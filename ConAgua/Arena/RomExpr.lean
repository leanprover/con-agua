import ConAgua.Arena.RomLevels
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

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

Tags: `0` bvar (index), `1` sort (level), `2` const (name, levels), `3` a `natVal` literal below
`2^64` (its value), `4` fvar (index, type), `5` app, `6` lam, `7` forallE, `8` letE, `9` back
reference, `10` proj (name, index, structure). A string literal (`11`) has no reader: no datum of the
checker contains one.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

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
  | .lit (.natVal n) => (3 :: u64B n, seen)
  | .lit (.strVal _) => ([11], seen)
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

/-- **The handles of the memo's entries, as a set** (the memo library's schema: array `150`,
`CTL[148]`, `CTL[149]`). `memo_push` aborts when the handle is already there: an explicitly encoded
compound subterm the twin's memo would have hit. The canonical encoding never does that; on
untrusted bytes (the pin data) the check is what makes the twin's memo miss wherever L interns
(DESIGN.md, "The pin data as an input"). -/
abbrev RSET : ArrId := 150

/-- The schema of `RSET`. -/
def rsetSch : MemoSch := ⟨RSET, 148⟩

/-- `memo_push(h)`'s checks on the set: the probe returned, and `h` is not in the set. -/
def rsetOK (m : Mem) (h : Word) : Prop :=
  mfindG rsetSch m h 0 ≠ [] ∧ (mfindG rsetSch m h 0).headD 0 = 0

/-- con-ron: none — the L memo of the ROM expression interner (the twin's `EMemo` insert), with the
canonical-encoding check. -/
def memoPush : FunDecl := lfn (h) locals (o, f, j, d, z) {
  (f, j, d) := call rset_find(h, 0);
  if f != 0 { abort };
  z := call rset_put(h, 0, 1, f, j);
  o := CTL.u64[132];
  if len(RMEMO.u64) <= o { abort };
  RMEMO.u64[o] := h;
  CTL.u64[132] := o + 1;
  return 0
}

/-- The memory after recording `h` in the set (`m` itself where the put aborts). -/
def mpushPut (m : Mem) (h : Word) : Mem :=
  (mputG rsetSch m h 0 1 0 ((mfindG rsetSch m h 0).tail.headD 0)).getD m

/-- The memory after recording `h`: in the set, then at the memo's end. -/
def mpushMem (m : Mem) (h : Word) : Mem :=
  ((mpushPut m h).set64 RMEMO (memoCnt (mpushPut m h)) h).set64 CTL 132
    (memoCnt (mpushPut m h) + 1)

/-- **The model of `memo_push`**: `none` where it aborts. -/
def mpushW (m : Mem) (h : Word) : Option Mem :=
  if mfindG rsetSch m h 0 = [] then none
  else if (mfindG rsetSch m h 0).headD 0 ≠ 0 then none
  else match mputG rsetSch m h 0 1 0 ((mfindG rsetSch m h 0).tail.headD 0) with
    | none => none
    | some m₁ =>
      if memoCnt m₁ < m₁.len64 RMEMO then
        some ((m₁.set64 RMEMO (memoCnt m₁) h).set64 CTL 132 (memoCnt m₁ + 1))
      else none

theorem memoPush_spec (p : Prog) (hp : p.lookup "memo_push" = some memoPush)
    (hf : p.lookup "rset_find" = some (memoFindG rsetSch))
    (hu : p.lookup "rset_put" = some (memoPutG rsetSch)) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "memo_push" [h]
    ⦃fun _ s' => LocEq s' s₀ ∧ mpushW s₀.mem h = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        memoFindG_spec rsetSch p "rset_find" hf n, memoPutG_spec rsetSch p "rset_put" hu n] <;>
      finish [mpushW, memoCnt]

theorem mpushPut_frame (m : Mem) (h : Word) : MemFrame [RSET] [149] m (mpushPut m h) := by
  unfold mpushPut
  cases hp : mputG rsetSch m h 0 1 0 ((mfindG rsetSch m h 0).tail.headD 0) with
  | none => exact MemFrame.refl _ _ _
  | some m₁ => exact mputG_frame rsetSch ⟨by decide, by decide⟩ m m₁ _ _ _ _ _ hp

theorem mpushPut_memo (m : Mem) (h : Word) :
    memoCnt (mpushPut m h) = memoCnt m ∧ (mpushPut m h).len64 RMEMO = m.len64 RMEMO ∧
      (mpushPut m h).arr64 RMEMO = m.arr64 RMEMO := by
  have hf := mpushPut_frame m h
  have hR := hf.1 RMEMO (by simp [RSET, RMEMO]) (by decide)
  refine ⟨hf.2.1 132 (by simp), ?_, hR⟩
  simp only [Mem.len64, hR]

/-- What `memo_push` checked, and its memory. -/
theorem mpushW_eq {m m' : Mem} {h : Word} (hW : mpushW m h = some m') :
    memoCnt m < m.len64 RMEMO ∧ rsetOK m h ∧ m' = mpushMem m h := by
  unfold mpushW at hW
  split at hW; · cases hW
  rename_i h1
  split at hW; · cases hW
  rename_i h2
  split at hW; · cases hW
  rename_i m₁ hput
  have hpp : mpushPut m h = m₁ := by simp only [mpushPut, hput, Option.getD_some]
  obtain ⟨hc, hl, -⟩ := mpushPut_memo m h
  rw [hpp] at hc hl
  split at hW
  · rename_i h4
    cases hW
    rw [hc, hl] at h4
    exact ⟨h4, ⟨h1, by simpa using h2⟩, by simp only [mpushMem, hpp]⟩
  · cases hW

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
-- con-ron: ConRon/Arena/Frontend/Readback.lean:194-256 ConRon.Arena.Frontend.internExprGo
def romExRef : FunDecl := lfn (pos) locals (k, h) {
  k := call rom_u64(pos + 1);
  h := call memo_get(k);
  return (h, pos + 9)
}

/-- The model of `rom_ex_ref`. -/
def romRefW (m : Mem) (pos : Word) : Option (Word × Word × Mem) :=
  if u64OK rom (pos + 1) ∧ memoOk m (u64W rom (pos + 1)) then
    some (rdW (m.arr64 RMEMO) (u64W rom (pos + 1)), pos + 9, m)
  else none

/-- The memory after the limb `k` went to the pool top. -/
def litWordMem (m : Mem) (k : Word) : Mem :=
  (m.set64 (tierA 0 (m.top >>> 40)) (m.top &&& 1099511627775) k).set64 CTL 0 (m.top + 1)

/-- The model of `rom_lit`. -/
def romLitW (m : Mem) (k : Word) : Option (Word × Mem) :=
  if m.len64 (tierA 0 (m.top >>> 40)) ≤ (m.top &&& 1099511627775) then none
  else if k = 0 then internW m m.top 0 else internW (litWordMem m k) m.top 1

/-- `rom_lit(k)`: intern the `natVal` literal `k` (its one limb at the pool top, none for `0`). -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:194-256 ConRon.Arena.Frontend.internExprGo
def romLit : FunDecl := lfn (k) locals (o, h, pt, pb) {
  o := CTL.u64[0];
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  if len(POOL⟨pt⟩) <= pb { abort };
  if k == 0 {
    h := call intern_lit(o, 0);
    return h
  };
  POOL⟨pt⟩[pb] := k;
  CTL.u64[0] := o + 1;
  h := call intern_lit(o, 1);
  return h
}

/-- `rom_lit`'s length check bounds its one-limb slice by the pool's capacity. -/
theorem romLit_cap (m : Mem) (h : ¬ m.len64 (tierA 0 (m.top >>> 40)) ≤ (m.top &&& 1099511627775))
    (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) : m.top.toNat + 1 ≤ pcap m := by
  have hsz := pcap_tier m (m.top >>> 40) hc
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top ht
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact L.Front.toNat_ofNat_size _ (by omega)
  have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
  rw [hlen] at this
  rw [pcap_eq m hc]
  omega
grind_pattern [arena_grind] romLit_cap => m.len64 (tierA 0 (m.top >>> 40)), pcap m

/-- **`rom_lit`'s pool write**: the limb at the old top, the pool grew by one word. -/
theorem litWordMem_facts (m : Mem) (k : Word) (hpool : PoolOK m)
    (h : ¬ m.len64 (tierA 0 (m.top >>> 40)) ≤ (m.top &&& 1099511627775)) :
    Grows m (litWordMem m k) ∧ SliceOK (litWordMem m k) m.top 1 ∧
    (vpool (litWordMem m k))[m.top.toNat]? = some k := by
  have hsm := hpool.small
  have h41 := hpool.top41
  have hsz := hsm.tier (m.top >>> 40)
  have hc : pcap m < 2 ^ 64 := by have := hpool.2.2.1; omega
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact L.Front.toNat_ofNat_size _ (by omega)
  have hi := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
  rw [hlen] at hi
  have hv : vpool (m.set64 (tierA 0 (m.top >>> 40)) (m.top &&& 1099511627775) k) =
      (vpool m).set! m.top.toNat k := vpool_stidx0 m m.top k h41 hi (by omega)
  have hg : Grows m (litWordMem m k) :=
    Grows.write m _ 1 hpool (PFrame.set64 _ _ _ (PFrame.refl _))
      (by rw [hv]; exact Agree.set _ _ _ _ _ (Agree.refl _ _) (Nat.le_refl _))
      (by have : (1 : Word).toNat = 1 := rfl; omega)
  have hctl : 0 < ((m.set64 (tierA 0 (m.top >>> 40)) (m.top &&& 1099511627775) k).arr64 CTL).size := by
    rw [arr64_set64_tier_ne _ _ _ _ _ ⟨by decide, by decide⟩]; exact hpool.2.1
  refine ⟨hg, SliceOK.fresh hg (Mem.top_set64 _ _ hctl), ?_⟩
  rw [litWordMem, vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, hv, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  simp [vpool_size, h41]

theorem romLit_spec (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hpi : p.lookup "intern_lit" = some internLit) (hp : p.lookup "rom_lit" = some romLit)
    (n : Nat) (s₀ : St) (k : Word) (hs : pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_lit" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ romLitW s₀.mem k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, romLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        internLit_spec p hph hpe hpm hpf hpp hpi n] <;>
      finish [romLitW, litWordMem]

/-- `rom_ex_leaf(pos, t)`: a `bvar` (`t = 0`), `sort` (`1`), `const` (`2`) or literal (`3`) node. -/
-- con-ron: ConRon/Arena/Frontend/Readback.lean:194-256 ConRon.Arena.Frontend.internExprGo
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
  if t == 3 {
    k := call rom_u64(pos + 1);
    h := call rom_lit(k);
    if h >= 4294967296 { abort };
    return (h, pos + 9)
  };
  if t != 2 { abort };
  (a, q) := call rom_name(pos + 1);
  (b, q) := call rom_levels(q);
  h := call intern_const(a, b);
  if h >= 4294967296 { abort };
  return (h, q)
}

/-- con-ron: ConRon/Arena/Frontend/Readback.lean:194-256 ConRon.Arena.Frontend.internExprGo -/
def romExpr : FunDecl := lfn (pos) locals (t, h, q, k) {
  t := rom.c8[pos];
  if t == 9 {
    (h, q) := call rom_ex_ref(pos);
    return (h, q)
  };
  if t == 0 || t == 1 || t == 2 || t == 3 {
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
-- con-ron: ConRon/Arena/Frontend/Readback.lean:194-256 ConRon.Arena.Frontend.internExprGo
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
-- con-ron: ConRon/Arena/Frontend/Readback.lean:194-256 ConRon.Arena.Frontend.internExprGo
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
    else match mpushW m' h with
      | none => none
      | some m'' => some (h, q, m'')

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
    if (t = 0 ∨ t = 3) ∧ ¬ u64OK rom (pos + 1) then none
    else if t = 0 then exLeafK (pos + 9) (binternW m (u64W rom (pos + 1)))
    else if t = 1 then exSortK (romLevelW rom n m (pos + 1))
    else if t = 2 then exConst2KN rom n (romNameW rom n m (pos + 1))
    else if t = 3 then exLeafK (pos + 9) (romLitW m (u64W rom (pos + 1)))
    else none

mutual
/-- **The model of `rom_expr`** at L fuel `n`. -/
def romExprW : Nat → Mem → Word → Option (Word × Word × Mem)
  | 0, _, _ => none
  | n + 1, m, pos =>
    if romB rom pos = 9 then romRefW rom m pos
    else if romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2 ∨ romB rom pos = 3 then
      romLeafW rom n m pos (romB rom pos)
    else if romB rom pos = 4 ∨ romB rom pos = 10 then romOneW n m pos (romB rom pos)
    else romTwoW n m pos (romB rom pos)

/-- The model of `rom_ex_one`. -/
def romOneW : Nat → Mem → Word → Word → Option (Word × Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, pos, t =>
    if t = 4 then (if u64OK rom (pos + 1) then exFvarK (u64W rom (pos + 1)) (romExprW n m (pos + 9)) else none)
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
  | some (a, q, m₁) => if u64OK rom q then exProj2K a (u64W rom q) (romExprW n m₁ (q + 8)) else none

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
theorem exNodeK_some (hh : ¬ 4294967296 ≤ h) :
    exNodeK q (some (h, m)) = (mpushW m h).map (fun m' => (h, q, m')) := by
  simp only [exNodeK, hh, ite_false]; cases mpushW m h <;> rfl
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
theorem romLeafW_bvar (ht : t = 0) (hu : u64OK rom (pos + 1)) :
    romLeafW rom (n + 1) m pos t = exLeafK (pos + 9) (binternW m (u64W rom (pos + 1))) := by
  simp [romLeafW, ht, hu]
theorem romLeafW_sort (_ht0 : t ≠ 0) (ht : t = 1) :
    romLeafW rom (n + 1) m pos t = exSortK (romLevelW rom n m (pos + 1)) := by simp [romLeafW, ht]
theorem romLeafW_u64 (ht : t = 0 ∨ t = 3) (hu : ¬ u64OK rom (pos + 1)) :
    romLeafW rom (n + 1) m pos t = none := by simp [romLeafW, ht, hu]
theorem romLeafW_const (_ht0 : t ≠ 0) (_ht1 : t ≠ 1) (ht : t = 2) :
    romLeafW rom (n + 1) m pos t = exConst2KN rom n (romNameW rom n m (pos + 1)) := by
  simp [romLeafW, ht]
theorem romLeafW_lit (_ht0 : t ≠ 0) (_ht1 : t ≠ 1) (_ht2 : t ≠ 2) (ht : t = 3) (hu : u64OK rom (pos + 1)) :
    romLeafW rom (n + 1) m pos t = exLeafK (pos + 9) (romLitW m (u64W rom (pos + 1))) := by
  simp [romLeafW, ht, hu]
theorem exFvarK_some : exFvarK rom k (some (a, q, m)) = exNodeK q (fvinternW m k a) := by simp [exFvarK]
theorem exProjK_some (hu : u64OK rom q) :
    exProjK rom n (some (a, q, m)) = exProj2K rom a (u64W rom q) (romExprW rom n m (q + 8)) := by
  simp [exProjK, hu]
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
theorem romExprW_leaf (h9 : romB rom pos ≠ 9)
    (h2 : romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2 ∨ romB rom pos = 3) :
    romExprW rom (n + 1) m pos = romLeafW rom n m pos (romB rom pos) := by
  simp [romExprW, h9, h2]
theorem romExprW_one (h9 : romB rom pos ≠ 9) (h2 : ¬ (romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2 ∨ romB rom pos = 3))
    (h4 : romB rom pos = 4 ∨ romB rom pos = 10) :
    romExprW rom (n + 1) m pos = romOneW rom n m pos (romB rom pos) := by
  simp only [romExprW, h9, h2, h4, ite_false, ite_true]
theorem romExprW_two (h9 : romB rom pos ≠ 9) (h2 : ¬ (romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2 ∨ romB rom pos = 3))
    (h4 : ¬ (romB rom pos = 4 ∨ romB rom pos = 10)) :
    romExprW rom (n + 1) m pos = romTwoW rom n m pos (romB rom pos) := by
  simp only [romExprW, h9, h2, h4, ite_false]
theorem romOneW_fvar (ht : t = 4) (hu : u64OK rom (pos + 1)) :
    romOneW rom (n + 1) m pos t = exFvarK rom (u64W rom (pos + 1)) (romExprW rom n m (pos + 9)) := by
  simp [romOneW, ht, hu]
theorem romOneW_proj (_ht4 : t ≠ 4) (ht : t = 10) :
    romOneW rom (n + 1) m pos t = exProjK rom n (romNameW rom n m (pos + 1)) := by
  simp [romOneW, ht]
theorem romTwoW_eq : romTwoW rom (n + 1) m pos t = exOneK rom n t (romExprW rom n m (pos + 1)) := by
  simp [romTwoW]
end arms

attribute [arena_grind =] exLeafK_some exSortK_some exConst2K_some exTwoK_app exTwoK_lam exTwoK_forall
  exConst2KN_some exFvarK_some exProj2K_some exOneK_let exOneK_two exLet2K_some exLet3K_some
grind_pattern [arena_grind] exNodeK_some => exNodeK q (some (h, m))
grind_pattern [arena_grind] exProjK_some => exProjK rom n (some (a, q, m))
grind_pattern [arena_grind] romExprW_ref => romExprW rom (n + 1) m pos
grind_pattern [arena_grind] romExprW_leaf => romExprW rom (n + 1) m pos
grind_pattern [arena_grind] romLeafW_bvar => romLeafW rom (n + 1) m pos t
grind_pattern [arena_grind] romLeafW_sort => romLeafW rom (n + 1) m pos t
grind_pattern [arena_grind] romLeafW_const => romLeafW rom (n + 1) m pos t
grind_pattern [arena_grind] romLeafW_lit => romLeafW rom (n + 1) m pos t
grind_pattern [arena_grind] romExprW_one => romExprW rom (n + 1) m pos
grind_pattern [arena_grind] romExprW_two => romExprW rom (n + 1) m pos
grind_pattern [arena_grind] romOneW_fvar => romOneW rom (n + 1) m pos t
grind_pattern [arena_grind] romOneW_proj => romOneW rom (n + 1) m pos t
attribute [arena_grind =] romTwoW_eq

/-! ## The models keep the top in a tier -/

theorem mpushW_topK {m m' : Mem} {h : Word} (hW : mpushW m h = some m') : TopK m m' := by
  obtain ⟨-, -, rfl⟩ := mpushW_eq hW
  refine (memFrame_top (mpushPut_frame m h) (by decide)).trans (TopK.of_eq ?_ ?_ ?_)
  · simp only [mpushMem]
    rw [top_set64_ne _ _ _ (by decide)]
    simp only [Mem.top, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ RMEMO by decide)]
  · simp only [mpushMem, pcap_set64]
  · simp only [mpushMem]
    rw [flag_set64_ctl _ _ _ (by decide), Mem.flag_set64_ne _ _ _ _ (by decide)]

theorem mkAppW_topK {m m' : Mem} {f a r : Word} (h : mkAppW m f a = some (r, m')) : TopK m m' := by
  unfold mkAppW at h; split at h; · cases h
  exact memFrame_top (mkK_frame appCS_wf (by decide) h) (by decide)
theorem mkLamW_topK {m m' : Mem} {f a r : Word} (h : mkLamW m f a = some (r, m')) : TopK m m' := by
  unfold mkLamW at h; split at h; · cases h
  exact memFrame_top (mkK_frame lamCS_wf (by decide) h) (by decide)
theorem mkForallW_topK {m m' : Mem} {f a r : Word} (h : mkForallW m f a = some (r, m')) : TopK m m' := by
  unfold mkForallW at h; split at h; · cases h
  exact memFrame_top (mkK_frame forallCS_wf (by decide) h) (by decide)
theorem mkLetW_topK {m m' : Mem} {t v b r : Word} (h : mkLetW m t v b = some (r, m')) : TopK m m' := by
  unfold mkLetW at h; split at h; · cases h
  exact memFrame_top (mkK_frame letCS_wf (by decide) h) (by decide)
theorem mkProjW_topK {m m' : Mem} {n i e r : Word} (h : mkProjW m n i e = some (r, m')) : TopK m m' := by
  unfold mkProjW at h; split at h; · cases h
  exact memFrame_top (mkK_frame projCS_wf (by decide) h) (by decide)

theorem romLitW_topK {m m' : Mem} {k r : Word} (h : romLitW m k = some (r, m')) : TopK m m' := by
  unfold romLitW at h
  split at h; · cases h
  rename_i hl
  split at h
  · exact cons_topK litCS_wf (by decide) (by decide) h
  · refine TopK.trans (fun hc ht => ⟨?_, ?_, fun hm => ?_⟩) (cons_topK litCS_wf (by decide) (by decide) h)
    · have := romLit_cap m hl hc ht
      rw [pcap_eq m hc] at this
      apply top_set64_lt
      rw [UInt64.toNat_add]; simp; omega
    · simp only [litWordMem, pcap_set64]
    · have hsz := pcap_tier m (m.top >>> 40) hc
      have hsplit := tag_split m.top
      have htier := tag_tier_le m.top ht
      have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
        simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
      have hi := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl)
      rw [hlen] at hi
      have htop0 : (m.set64 (tierA 0 (m.top >>> 40)) (m.top &&& 1099511627775) k).top = m.top :=
        top_set64_arr _ _ _ _ (Ne.symm (tierA_pool_ne _ _ (by decide) (by decide)))
      have hflag : (litWordMem m k).flag = m.flag := by
        rw [litWordMem, Mem.flag_set64_top, Mem.flag_set64_ne _ _ _ _ (Ne.symm (tierA_pool_ne _ _ (by decide) (by decide)))]
      rcases hm with hf | h0
      · exact .inl (by rw [hflag]; exact hf)
      · right
        have hT : (m.top + 1).toNat = m.top.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        rcases top_set64_cases (m.set64 (tierA 0 (m.top >>> 40)) (m.top &&& 1099511627775) k) (m.top + 1) with e | e
        · show (litWordMem m k).top.toNat < _
          rw [litWordMem, e, hT]; omega
        · show (litWordMem m k).top.toNat < _
          rw [litWordMem, e, htop0]; exact h0

theorem exLeafK_eq {q h q' : Word} {r : Option (Word × Mem)} {m' : Mem}
    (hW : exLeafK q r = some (h, q', m')) : r = some (h, m') := by
  cases r with
  | none => simp [exLeafK] at hW
  | some r =>
    obtain ⟨w, m₁⟩ := r
    simp only [exLeafK] at hW
    split at hW
    · simp at hW
    · simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, -, rfl⟩ := hW; rfl

theorem exNodeK_topK {q h q' : Word} {r : Option (Word × Mem)} {m m' : Mem}
    (hr : ∀ w m₁, r = some (w, m₁) → TopK m m₁) (hW : exNodeK q r = some (h, q', m')) : TopK m m' := by
  cases r with
  | none => simp [exNodeK] at hW
  | some r =>
    obtain ⟨w, m₁⟩ := r
    simp only [exNodeK] at hW
    split at hW
    · simp at hW
    split at hW
    · simp at hW
    rename_i m₂ hp
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨-, -, rfl⟩ := hW
    exact (hr w m₁ rfl).trans (mpushW_topK hp)


theorem romLeafW_topK (rom : List UInt8) (n : Nat) (m : Mem) (pos t h q : Word) (m' : Mem)
    (hW : romLeafW rom n m pos t = some (h, q, m')) : TopK m m' := by
  cases n with
  | zero => simp [romLeafW] at hW
  | succ n =>
    by_cases hu : (t = 0 ∨ t = 3) ∧ ¬ u64OK rom (pos + 1)
    · simp [romLeafW, hu] at hW
    by_cases h0 : t = 0
    · rw [romLeafW_bvar rom n m pos t h0 (Classical.byContradiction fun hh => hu ⟨Or.inl h0, hh⟩)] at hW
      exact cons_topK bvarCS_wf (by decide) (by decide) (exLeafK_eq hW)
    by_cases h1 : t = 1
    · rw [romLeafW_sort rom n m pos t h0 h1] at hW
      cases hP : romLevelW rom n m (pos + 1) with
      | none => rw [hP] at hW; simp [exSortK] at hW
      | some r =>
        obtain ⟨a, q₁, m₁⟩ := r
        rw [hP, exSortK_some] at hW
        exact (romLevelW_topK hP).trans
          (cons_topK sortCS_wf (by decide) (by decide) (exLeafK_eq hW))
    by_cases h2 : t = 2
    · rw [romLeafW_const rom n m pos t h0 h1 h2] at hW
      cases hP : romNameW rom n m (pos + 1) with
      | none => rw [hP] at hW; simp [exConst2KN] at hW
      | some r =>
        obtain ⟨a, q₁, m₁⟩ := r
        rw [hP, exConst2KN_some] at hW
        cases hQ : romLevelsW rom n m₁ q₁ with
        | none => rw [hQ] at hW; simp [exConst2K] at hW
        | some r =>
          obtain ⟨b, q₂, m₂⟩ := r
          rw [hQ, exConst2K_some] at hW
          exact ((romNameW_topK hP).trans
            (romLevelsW_topK hQ)).trans
            (cons_topK constCS_wf (by decide) (by decide) (exLeafK_eq hW))
    by_cases h3 : t = 3
    · rw [romLeafW_lit rom n m pos t h0 h1 h2 h3 (Classical.byContradiction fun hh => hu ⟨Or.inr h3, hh⟩)] at hW
      exact romLitW_topK (exLeafK_eq hW)
    simp [romLeafW, h0, h1, h2, h3] at hW

/-- **`rom_expr`'s models keep the top in a tier.** -/
theorem romExprW_topK (rom : List UInt8) (n : Nat) :
    (∀ m pos h q m', romExprW rom n m pos = some (h, q, m') → TopK m m') ∧
    (∀ m pos t h q m', romOneW rom n m pos t = some (h, q, m') → TopK m m') ∧
    (∀ m pos t h q m', romTwoW rom n m pos t = some (h, q, m') → TopK m m') := by
  induction n with
  | zero =>
    refine ⟨fun m pos h q m' hW => ?_, fun m pos t h q m' hW => ?_, fun m pos t h q m' hW => ?_⟩ <;>
      simp [romExprW, romOneW, romTwoW] at hW
  | succ n ih =>
    obtain ⟨ihE, ihO, ihT⟩ := ih
    refine ⟨fun m pos h q m' hW => ?_, fun m pos t h q m' hW => ?_, fun m pos t h q m' hW => ?_⟩
    · by_cases h9 : romB rom pos = 9
      · rw [romExprW_ref rom n m pos h9] at hW
        simp only [romRefW] at hW
        split at hW
        · simp only [Option.some.injEq, Prod.mk.injEq] at hW
          obtain ⟨-, -, rfl⟩ := hW; exact TopK.refl _
        · simp at hW
      by_cases h2 : romB rom pos = 0 ∨ romB rom pos = 1 ∨ romB rom pos = 2 ∨ romB rom pos = 3
      · rw [romExprW_leaf rom n m pos h9 h2] at hW
        exact romLeafW_topK rom n m pos _ h q m' hW
      by_cases h4 : romB rom pos = 4 ∨ romB rom pos = 10
      · rw [romExprW_one rom n m pos h9 h2 h4] at hW
        exact ihO m pos _ h q m' hW
      · rw [romExprW_two rom n m pos h9 h2 h4] at hW
        exact ihT m pos _ h q m' hW
    · by_cases h4 : t = 4
      · by_cases hu : u64OK rom (pos + 1)
        · rw [romOneW_fvar rom n m pos t h4 hu] at hW
          cases hP : romExprW rom n m (pos + 9) with
          | none => rw [hP] at hW; simp [exFvarK] at hW
          | some r =>
            obtain ⟨a, q₁, m₁⟩ := r
            rw [hP, exFvarK_some] at hW
            exact (ihE m (pos + 9) a q₁ m₁ hP).trans (exNodeK_topK (fun w m₂ hI =>
              cons_topK fvarCS_wf (by decide) (by decide) hI) hW)
        · simp [romOneW, h4, hu] at hW
      by_cases h10 : t = 10
      · rw [romOneW_proj rom n m pos t h4 h10] at hW
        cases hP : romNameW rom n m (pos + 1) with
        | none => rw [hP] at hW; simp [exProjK] at hW
        | some r =>
          obtain ⟨a, q₁, m₁⟩ := r
          rw [hP] at hW
          by_cases hu : u64OK rom q₁
          case neg => simp [exProjK, hu] at hW
          rw [exProjK_some rom n m₁ q₁ a hu] at hW
          cases hQ : romExprW rom n m₁ (q₁ + 8) with
          | none => rw [hQ] at hW; simp [exProj2K] at hW
          | some r =>
            obtain ⟨b, q₂, m₂⟩ := r
            rw [hQ, exProj2K_some] at hW
            exact ((romNameW_topK hP).trans (ihE m₁ (q₁ + 8) b q₂ m₂ hQ)).trans
              (exNodeK_topK (fun w m₃ hI => mkProjW_topK hI) hW)
      · simp [romOneW, h4, h10] at hW
    · rw [romTwoW_eq] at hW
      cases hP : romExprW rom n m (pos + 1) with
      | none => rw [hP] at hW; simp [exOneK] at hW
      | some r =>
        obtain ⟨a, q₁, m₁⟩ := r
        have k1 := ihE m (pos + 1) a q₁ m₁ hP
        rw [hP] at hW
        by_cases h8 : t = 8
        · rw [exOneK_let rom n m₁ q₁ t a h8] at hW
          cases hQ : romExprW rom n m₁ q₁ with
          | none => rw [hQ] at hW; simp [exLet2K] at hW
          | some r =>
            obtain ⟨b, q₂, m₂⟩ := r
            rw [hQ, exLet2K_some] at hW
            cases hR : romExprW rom n m₂ q₂ with
            | none => rw [hR] at hW; simp [exLet3K] at hW
            | some r =>
              obtain ⟨c, q₃, m₃⟩ := r
              rw [hR, exLet3K_some] at hW
              exact ((k1.trans (ihE m₁ q₁ b q₂ m₂ hQ)).trans (ihE m₂ q₂ c q₃ m₃ hR)).trans
                (exNodeK_topK (fun w m₄ hI => mkLetW_topK hI) hW)
        · rw [exOneK_two rom n m₁ q₁ t a h8] at hW
          cases hQ : romExprW rom n m₁ q₁ with
          | none => rw [hQ] at hW; simp [exTwoK] at hW
          | some r =>
            obtain ⟨b, q₂, m₂⟩ := r
            have k2 := k1.trans (ihE m₁ q₁ b q₂ m₂ hQ)
            rw [hQ] at hW
            by_cases h5 : t = 5
            · rw [exTwoK_app m₂ q₂ t a b h5] at hW
              exact k2.trans (exNodeK_topK (fun w m₄ hI => mkAppW_topK hI) hW)
            by_cases h6 : t = 6
            · rw [exTwoK_lam m₂ q₂ t a b h6] at hW
              exact k2.trans (exNodeK_topK (fun w m₄ hI => mkLamW_topK hI) hW)
            by_cases h7 : t = 7
            · rw [exTwoK_forall m₂ q₂ t a b h7] at hW
              exact k2.trans (exNodeK_topK (fun w m₄ hI => mkForallW_topK hI) hW)
            simp [exTwoK, h5, h6, h7] at hW

theorem romExprW_top' (rom : List UInt8) (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem)
    (hW : romExprW rom n m pos = some (h, q, m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := ((romExprW_topK rom n).1 m pos h q m' hW hc ht).1
grind_pattern [arena_grind] romExprW_top' => romExprW rom n m pos, some (h, q, m')

/-- The functions `rom_expr` calls. -/
structure ExprProg (rom : List UInt8) (p : Prog) : Prop extends LevelsProg rom p where
  rom_expr : p.lookup "rom_expr" = some (romExpr rom)
  rom_ex_leaf : p.lookup "rom_ex_leaf" = some romExLeaf
  memo_get : p.lookup "memo_get" = some memoGet
  rom_ex_ref : p.lookup "rom_ex_ref" = some romExRef
  rom_ex_one : p.lookup "rom_ex_one" = some romExOne
  rom_ex_two : p.lookup "rom_ex_two" = some romExTwo
  memo_push : p.lookup "memo_push" = some memoPush
  rset_find : p.lookup "rset_find" = some (memoFindG rsetSch)
  rset_put : p.lookup "rset_put" = some (memoPutG rsetSch)
  lit_match : p.lookup "lit_match" = some litMatch
  lit_find : p.lookup "lit_find" = some litFind
  lit_push : p.lookup "lit_push" = some litPush
  intern_lit : p.lookup "intern_lit" = some internLit
  rom_lit : p.lookup "rom_lit" = some romLit
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
  ∀ (s₀ : St) (pos : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rom_expr" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ romExprW rom n s₀.mem pos = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄
/-- `rom_ex_one`'s. -/
def SpecO (rom : List UInt8) (p : Prog) (n : Nat) : Prop :=
  ∀ (s₀ : St) (pos t : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rom_ex_one" [pos, t]
    ⦃fun r s' => LocEq s' s₀ ∧ romOneW rom n s₀.mem pos t = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄
/-- `rom_ex_two`'s. -/
def SpecT (rom : List UInt8) (p : Prog) (n : Nat) : Prop :=
  ∀ (s₀ : St) (pos t : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rom_ex_two" [pos, t]
    ⦃fun r s' => LocEq s' s₀ ∧ romTwoW rom n s₀.mem pos t = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄
/-- The three specs at L fuel `n`. -/
def ExprSpecs (rom : List UInt8) (p : Prog) (n : Nat) : Prop :=
  SpecE rom p n ∧ SpecO rom p n ∧ SpecT rom p n

theorem romExLeaf_specW (n : Nat) (s₀ : St) (pos t : Word)
    (hs : pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41) :
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
        internConst_spec p hL.const_find hL.const_push hL.intern_const n,
        romLit_spec p hL.lit_hash hL.limbs_eq hL.lit_match hL.lit_find hL.lit_push hL.intern_lit
          hL.rom_lit n] <;>
      finish [Keep.size, Keep.pcap]

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
    finish [Keep.size, Keep.pcap]

theorem romExpr_stepO (n : Nat) (ih : ExprSpecs rom p n) : SpecO rom p (n + 1) := by
  obtain ⟨ihE, _, _⟩ := ih
  unfold SpecE at ihE
  intro s₀ pos t hs
  have hE := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (ihE s₁ pos₁ h₁)
  have hn' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (romName_specW rom p hL.toNameProg n s₁ pos₁ h₁)
  have hmp := fun s₁ h₁ => Triple.keep hL.no_st8 (memoPush_spec p hL.memo_push hL.rset_find hL.rset_put n s₁ h₁)
  rw [invoke_eq _ hL.rom_ex_one]
  simp only [callFn, romExOne]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hn', hE, hmp,
      romU64_spec rom p hL.rom_u64 n,
      internFVar_spec p hL.fvar_find hL.fvar_push hL.intern_fvar n,
      mkProj_spec p hL.der_b hL.proj_find hL.proj_push hL.intern_proj hL.mk_proj n] <;>
    finish [Keep.size, Keep.pcap, memoCnt, Option.map_some]

theorem romExpr_stepT (n : Nat) (ih : ExprSpecs rom p n) : SpecT rom p (n + 1) := by
  obtain ⟨ihE, _, _⟩ := ih
  unfold SpecE at ihE
  intro s₀ pos t hs
  have hE := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (ihE s₁ pos₁ h₁)
  have hmp := fun s₁ h₁ => Triple.keep hL.no_st8 (memoPush_spec p hL.memo_push hL.rset_find hL.rset_put n s₁ h₁)
  rw [invoke_eq _ hL.rom_ex_two]
  simp only [callFn, romExTwo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hE, hmp,
      mkApp_spec p hL.der_b hL.app_find hL.app_push hL.intern_app hL.mk_app n,
      mkLam_spec p hL.der_b hL.lam_find hL.lam_push hL.intern_lam hL.mk_lam n,
      mkForall_spec p hL.der_b hL.forall_find hL.forall_push hL.intern_forall hL.mk_forall n,
      mkLet_spec p hL.der_b hL.letE_find hL.letE_push hL.intern_letE hL.mk_let n] <;>
    finish (gen := 16) [Keep.size, Keep.pcap, memoCnt, Option.map_some]

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
