module

public import ConAgua.Arena.FreezeRel
import ConAgua.L.Blocks
import all ConAgua.Arena.Freeze
import ConAgua.Arena.Checker

@[expose] public section

/-!
# The frozen buffer's spec: `fz_i` and `par_compact` (lane parmode, entry 1)

docs/design/parmode.md, "Redesign" and "Step 4" (a). `par_compact(c)` (`Arena/Freeze.lean`)
writes the frozen buffer into `OUT`. Here its run, as a function of the memory:

* `fzStep m c i z o`: what `fz_i(o, c)` does for the prefix image `z` (`fzPreG z.src z.e i`): if
  `c ≠ 0` the prefix `z.src[0‥e)` copied to `OUT[o‥o+e)`, then the header entry `(o, e)` at
  `OUT[10+2i]`, `OUT[11+2i]` (`e = fzEv m z.e`, the extent); `fzPreG_run`: the run is that memory
  with the result `o + e`, or `oob` (`fzOK`: the extent's loads, the copy and the two header words
  in bounds).
* `parCompactMem m c`: the 64 images in header order from offset `hdrW`, then the header's
  words `0`‥`4`, `8`, `9`; `parCompact_run`: the run of `par_compact(c)` (fuel `≥ 2`) is
  that memory with the result `fzOff m 64` (the buffer's length), or `oob` (`parCompactOK`).
* What the memory holds: nothing but `OUT` changes (`parCompactMem_frame`, `MemFrame [OUT] []`);
  the header words (`parCompactMem_hdr*`); for `c ≠ 0` each image
  `OUT[fzOff m i ‥ fzOff m i + fzExt m zᵢ) = zᵢ.src[0 ‥ fzExt m zᵢ)` (`parCompactMem_img`).

The extents read only arrays other than `OUT` (`Expr.fzOk`, checked for `frozen`), so every
`fz_i` computes its extent as in the memory before `par_compact` (`fzExt m z`).
-/


namespace L.Arena

open L
open Std.WP
open scoped Lean.Order

/-! ## Extents: expressions of constants and loads from arrays other than `OUT` -/

/-- An extent expression: constants, binary operations and loads (`ld64`) from word arrays other
than `OUT`. -/
def _root_.L.Expr.fzOk : Expr → Bool
  | .const _ => true
  | .bin _ a b => a.fzOk && b.fzOk
  | .ld64 a i => a != OUT && i.fzOk
  | _ => false

/-- An extent's value in memory `m` (no locals). -/
def fzEv (m : Mem) (e : Expr) : Word := Expr.pval ⟨m, fun _ => 0⟩ e

/-- The extent's loads are in bounds in `m`. -/
def _root_.L.Expr.ldOk (m : Mem) : Expr → Bool
  | .const _ => true
  | .bin _ a b => a.ldOk m && b.ldOk m
  | .ld64 a i => i.ldOk m && decide ((fzEv m i).toNat < (m.arr64 a).size)
  | _ => false

theorem fzEv_bin (m : Mem) (op : BinOp) (a b : Expr) :
    fzEv m (.bin op a b) = op.eval (fzEv m a) (fzEv m b) := rfl

theorem fzEv_ld64 (m : Mem) (a : ArrId) (i : Expr) : fzEv m (.ld64 a i) = rd64 m a (fzEv m i) := rfl

/-- Locals do not matter. -/
theorem pval_fz : ∀ (e : Expr), e.fzOk = true → ∀ s : St, Expr.pval s e = fzEv s.mem e
  | .const _, _, _ => rfl
  | .bin op a b, h, s => by
    simp only [Expr.fzOk, Bool.and_eq_true] at h
    simp only [Expr.pval, fzEv_bin, pval_fz a h.1 s, pval_fz b h.2 s]
  | .ld64 a i, h, s => by
    simp only [Expr.fzOk, Bool.and_eq_true] at h
    simp only [Expr.pval, fzEv_ld64, pval_fz i h.2 s]
  | .var _, h, _ | .ld8 _ _, h, _ | .len8 _, h, _ | .len64 _, h, _ | .cmpw _ _ _, h, _
  | .ldc _ _, h, _ | .glob _, h, _ | .ld64t _ _ _, h, _ | .len64t _ _, h, _ | .ld8x8 _ _, h, _ | .ld32t _ _ _, h, _ | .ld32h _ _ _ _, h, _ =>
    by simp [Expr.fzOk] at h

/-- Memories that agree on every array but `OUT` give extents the same values. -/
theorem fzEv_congr {m m' : Mem} (h : ∀ a : TieredArray, a ≠ OUT → m'.arr64 a = m.arr64 a) :
    ∀ (e : Expr), e.fzOk = true → fzEv m' e = fzEv m e ∧ e.ldOk m' = e.ldOk m
  | .const _, _ => ⟨rfl, rfl⟩
  | .bin op a b, he => by
    simp only [Expr.fzOk, Bool.and_eq_true] at he
    obtain ⟨h1, h2⟩ := fzEv_congr h a he.1
    obtain ⟨h3, h4⟩ := fzEv_congr h b he.2
    simp [fzEv_bin, Expr.ldOk, h1, h2, h3, h4]
  | .ld64 a i, he => by
    simp only [Expr.fzOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at he
    obtain ⟨h1, h2⟩ := fzEv_congr h i he.2
    simp [fzEv_ld64, Expr.ldOk, rd64, h1, h2, h a (TieredArray.t0_ne he.1)]
  | .var _, h | .ld8 _ _, h | .len8 _, h | .len64 _, h | .cmpw _ _ _, h
  | .ldc _ _, h | .glob _, h | .ld64t _ _ _, h | .len64t _ _, h | .ld8x8 _ _, h | .ld32t _ _ _, h | .ld32h _ _ _ _, h =>
    by simp [Expr.fzOk] at h

/-- **Evaluating an extent**: its value, or `oob` (a load out of bounds). -/
theorem evalE_fz : ∀ (e : Expr), e.fzOk = true → ∀ s : St,
    (evalE e).run s = if e.ldOk s.mem then .ok (fzEv s.mem e, s) else .error .oob
  | .const _, _, s => by simp [evalE, Expr.ldOk, fzEv, Expr.pval]; rfl
  | .bin op a b, he, s => by
    simp only [Expr.fzOk, Bool.and_eq_true] at he
    have ha := evalE_fz a he.1 s
    have hb := evalE_fz b he.2 s
    simp only [evalE, StateT.run_bind, ha, Expr.ldOk, Bool.and_eq_true]
    by_cases h1 : a.ldOk s.mem = true
    · simp only [h1, ite_true]
      by_cases h2 : b.ldOk s.mem = true
      · simp [h2, hb, fzEv_bin]; rfl
      · simp [h2, hb]; rfl
    · simp [h1]; rfl
  | .ld64 a i, he, s => by
    simp only [Expr.fzOk, Bool.and_eq_true] at he
    have hi := evalE_fz i he.2 s
    simp only [evalE, StateT.run_bind, hi, Expr.ldOk, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h1 : i.ldOk s.mem = true
    · simp only [h1, ite_true, true_and]
      by_cases h2 : (fzEv s.mem i).toNat < (s.mem.arr64 a).size
      · simp [ld64, h2, fzEv_ld64, rd64, Array.getD]; rfl
      · simp [ld64, h2]; rfl
    · simp [h1]; rfl
  | .var _, h, _ | .ld8 _ _, h, _ | .len8 _, h, _ | .len64 _, h, _ | .cmpw _ _ _, h, _
  | .ldc _ _, h, _ | .glob _, h, _ | .ld64t _ _ _, h, _ | .len64t _ _, h, _ | .ld8x8 _ _, h, _ | .ld32t _ _ _, h, _ | .ld32h _ _ _ _, h, _ =>
    by simp [Expr.fzOk] at h

/-! ## Stores and copies -/

attribute [local simp] L.Mem.size64_set64 L.St.setLoc_mem L.St.setLoc_loc

@[simp] theorem size_copy64 (m : Mem) (d : TieredArray) (di : Word) (s : TieredArray) (si : Word) (n : Nat)
    (b : TieredArray) : ((m.copy64 d di s si n).arr64 b).size = (m.arr64 b).size := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy64]; rw [ih, L.Mem.size64_set64]

theorem arr64_copy64_ne (m : Mem) (d : TieredArray) (di : Word) (s : TieredArray) (si : Word) (n : Nat)
    {b : TieredArray} (h : b ≠ d) : (m.copy64 d di s si n).arr64 b = m.arr64 b := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy64]; rw [ih, Mem.arr64_set64_ne _ _ _ _ _ h]

/-! ## `fz_i`: one prefix image -/

/-- The memory after `fz_i(o, c)` for the prefix image `z` in header entry `i` (no bounds: an
out-of-bounds store writes nothing, but then the run is `oob`, `fzOK`). -/
def fzCopy (m : Mem) (c : Word) (z : Fz) (o : Word) (b : Word := 0) : Mem :=
  if c ≠ 0 then m.copy64 OUT (b + o) z.src 0 (fzEv m z.e).toNat else m

def fzStep (m : Mem) (c : Word) (i : Nat) (z : Fz) (o : Word) (b : Word := 0) : Mem :=
  (((fzCopy m c z o b).set64 OUT
    (b + (10 + 2 * i).toUInt64) o).set64 OUT (b + (11 + 2 * i).toUInt64) (fzEv m z.e))

/-- `fz_i(o, c, b)` stays in bounds: the extent's loads, the copy (if `c ≠ 0`), the two header words. -/
def fzOK (m : Mem) (c : Word) (i : Nat) (z : Fz) (o : Word) (b : Word := 0) : Bool :=
  z.e.ldOk m &&
    (c == 0 || decide ((b + o).toNat + (fzEv m z.e).toNat ≤ (m.arr64 OUT).size ∧
      (fzEv m z.e).toNat ≤ (m.arr64 z.src).size)) &&
    decide ((b + (10 + 2 * i).toUInt64).toNat < (m.arr64 OUT).size) &&
    decide ((b + (11 + 2 * i).toUInt64).toNat < (m.arr64 OUT).size)

/-- **`fz_i`'s run**: from any state, with fuel, `fz_i(o, c)` returns `o + e` (`e` the extent)
with the memory `fzStep` and the caller's locals, or fails with `oob`. -/
theorem fzPreG_run {p : Prog} {f : FnName} {z : Fz} {i : Nat}
    (hl : p.lookup f = some (fzPreG z.src z.e i)) (he : z.e.fzOk = true) (n : Nat) (s : St)
    (o c b : Word) :
    (invoke p (exec p (n + 1)) f [o, c, b]).run s =
      if fzOK s.mem c i z o b then
        .ok ([o + fzEv s.mem z.e], { s with mem := fzStep s.mem c i z o b })
      else .error .oob := by
  simp only [invoke, lookupFn, hl, callFn, exec, step, fzPreG, StateT.run_bind, StateT.run_get,
    StateT.run_set, pure_bind, evalE_fz z.e he]
  by_cases h1 : z.e.ldOk s.mem = true
  · by_cases h3 : (b.toNat + (10 + 2 * i)) % 18446744073709551616 < (s.mem.arr64 OUT).size <;>
    by_cases h4 : (b.toNat + (11 + 2 * i)) % 18446744073709551616 < (s.mem.arr64 OUT).size <;>
    by_cases hc : c = 0
    all_goals try by_cases h2 : (b.toNat + o.toNat) % 18446744073709551616 + UInt64.toNat (fzEv s.mem z.e) ≤ (s.mem.arr64 OUT).size ∧
                  UInt64.toNat (fzEv s.mem z.e) ≤ (s.mem.arr64 z.src).size
    all_goals simp [*, fzOK, fzStep, fzCopy, setLoc, St.setLoc, evalC, evalE, warr, st64,
        Cmp.eval, fzC, evalArgs, Sig.retVal, Sig.retOr, Locals.init, BinOp.eval, StateT.run_bind]
    all_goals first | rfl | done
  · simp [h1, fzOK]; rfl

/-! ## The frozen entries -/

/-- Frozen entry `i`'s image. -/
def fzAt (i : Nat) : Fz := (frozen[i]?.map (·.2)).getD ⟨OUT, .const 0⟩

theorem fzF_eq {i : Nat} (h : i < frozen.length) : fzF i = fzPreG (fzAt i).src (fzAt i).e i := by
  simp only [fzF, fzAt, List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

theorem frozen_fzOk_all : frozen.all (fun x => x.2.e.fzOk && x.2.src != OUT) = true := by
  decide +kernel

/-- Every frozen extent is an extent expression, and no image's source is `OUT`. -/
theorem fzAt_ok {i : Nat} (h : i < frozen.length) : (fzAt i).e.fzOk = true ∧ (fzAt i).src ≠ OUT := by
  have := List.all_eq_true.mp frozen_fzOk_all frozen[i] (List.getElem_mem h)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  simpa [fzAt, List.getElem?_eq_getElem h] using this

/-! ## The calls `o := fz_i(o, c)` in sequence -/

/-- The memory and the offset after the images of the entries `is`, from memory `m` and offset
`o`. -/
def pcGo (c b : Word) : List Nat → Mem → Word → Mem × Word
  | [], m, o => (m, o)
  | i :: is, m, o => pcGo c b is (fzStep m c i (fzAt i) o b) (o + fzEv m (fzAt i).e)

/-- Every `fz_i` of the entries `is` stays in bounds. -/
def pcOK (c b : Word) : List Nat → Mem → Word → Bool
  | [], _, _ => true
  | i :: is, m, o => fzOK m c i (fzAt i) o b && pcOK c b is (fzStep m c i (fzAt i) o b) (o + fzEv m (fzAt i).e)

/-- The call `o := fz_i(o, c)`. -/
def fzCall (i : Nat) : Stmt := .call [2] (fzName i) [.var 2, .var 0, .var 1]

theorem fzCalls_eq : fzCalls = (List.range frozen.length).map fzCall := by rfl

@[simp] theorem St.setLoc_loc_same (M : Mem) (s : St) (x : Var) (a b : Word) :
    ({ mem := M, loc := (s.setLoc x a).loc } : St).setLoc x b = ({ mem := M, loc := s.loc } : St).setLoc x b := by
  simp only [St.setLoc]; congr 1; funext y; by_cases h : y = x <;> simp [h]

/-- **The calls in sequence**: from a state with offset `o` in local `1` and the flag `c` in
local `0`, the calls of the entries `is` run as `pcGo`, or fail with `oob`. -/
theorem fzCalls_run {p : Prog} (n : Nat) (rest : Stmt) :
    ∀ (is : List Nat), (∀ i ∈ is, i < frozen.length ∧ p.lookup (fzName i) = some (fzF i)) →
    ∀ (s : St),
    (step p (exec p (n + 1)) ((is.map fzCall).foldr .seq rest)).run s =
      if pcOK (s.loc 0) (s.loc 1) is s.mem (s.loc 2) then
        (step p (exec p (n + 1)) rest).run
          ({ s with mem := (pcGo (s.loc 0) (s.loc 1) is s.mem (s.loc 2)).1 }.setLoc 2
            (pcGo (s.loc 0) (s.loc 1) is s.mem (s.loc 2)).2)
      else .error .oob
  | [], _, s => by
    have : ({ s with mem := s.mem } : St).setLoc 2 (s.loc 2) = s := by
      cases s; simp only [St.setLoc]; congr 1; funext y; split <;> simp_all
    simp [pcOK, pcGo, this]
  | i :: is, h, s => by
    have hi := h i (by simp)
    have hrest := fzCalls_run n rest is (fun j hj => h j (by simp [hj]))
    have hz := fzAt_ok hi.1
    have hrun := fzPreG_run (p := p) (f := fzName i) (z := fzAt i) (i := i)
      (by rw [hi.2, fzF_eq hi.1]) hz.1 n
    simp only [List.map_cons, List.foldr_cons, fzCall, step, StateT.run_bind, evalArgs, evalE,
      StateT.run_get, pure_bind, StateT.run_pure, hrun, pcOK, pcGo, Bool.and_eq_true]
    by_cases h1 : fzOK s.mem (s.loc 0) i (fzAt i) (s.loc 2) (s.loc 1) = true
    · simp [h1, setLocs, St.setLocs, hrest, L.St.setLoc_mem, St.setLoc_loc_same]
      rfl
    · simp [h1]; rfl

/-! ## What the images and stores leave alone -/

/-- What a memory step that writes only `OUT` keeps. -/
structure OutFrame (m m' : Mem) : Prop where
  arr : ∀ a : TieredArray, a ≠ OUT → m'.arr64 a = m.arr64 a
  size : ∀ a : TieredArray, (m'.arr64 a).size = (m.arr64 a).size
  bytes : m'.bytes = m.bytes
  glob : m'.glob = m.glob

theorem OutFrame.refl (m : Mem) : OutFrame m m := ⟨fun _ _ => rfl, fun _ => rfl, rfl, rfl⟩

theorem OutFrame.trans {m₁ m₂ m₃ : Mem} (h₁ : OutFrame m₁ m₂) (h₂ : OutFrame m₂ m₃) :
    OutFrame m₁ m₃ :=
  ⟨fun a ha => (h₂.arr a ha).trans (h₁.arr a ha), fun a => (h₂.size a).trans (h₁.size a),
    h₂.bytes.trans h₁.bytes, h₂.glob.trans h₁.glob⟩

theorem OutFrame.set64 (m : Mem) (i v : Word) : OutFrame m (m.set64 OUT i v) :=
  ⟨fun _ ha => Mem.arr64_set64_ne _ _ _ _ _ ha, fun _ => L.Mem.size64_set64 _ _ _ _ _,
    rfl, rfl⟩

theorem OutFrame.copy64 (m : Mem) (di : Word) (s : ArrId) (si : Word) (n : Nat) :
    OutFrame m (m.copy64 OUT di s si n) :=
  ⟨fun _ ha => arr64_copy64_ne _ _ _ _ _ _ ha, fun _ => size_copy64 _ _ _ _ _ _ _,
    Mem.copy64_bytes _ _ _ _ _ _, Mem.copy64_glob _ _ _ _ _ _⟩

theorem OutFrame.fzStep (m : Mem) (c : Word) (i : Nat) (z : Fz) (o b : Word) :
    OutFrame m (fzStep m c i z o b) := by
  unfold L.Arena.fzStep
  refine OutFrame.trans ?_ (OutFrame.trans (OutFrame.set64 _ _ _) (OutFrame.set64 _ _ _))
  unfold fzCopy
  split
  · exact OutFrame.copy64 _ _ _ _ _
  · exact OutFrame.refl _

theorem OutFrame.pcGo (c b : Word) : ∀ (is : List Nat) (m : Mem) (o : Word),
    OutFrame m (pcGo c b is m o).1
  | [], m, _ => OutFrame.refl m
  | i :: is, m, o => (OutFrame.fzStep m c i (fzAt i) o b).trans (OutFrame.pcGo c b is _ _)

/-! ## `par_compact` -/

theorem getElem_set64_out (M : Mem) (a : TieredArray) (ha : a ≠ OUT) (i v : Word) (k : Nat)
    (h : k < ((M.set64 OUT i v).arr64 a).size) :
    ((M.set64 OUT i v).arr64 a)[k]'h = (M.arr64 a)[k]'(by rwa [L.Mem.size64_set64] at h) := by
  simp only [Mem.arr64_set64_ne _ _ _ _ _ ha]

theorem getElem_set64_out_ctl (M : Mem) (i v : Word) (k : Nat)
    (h : k < ((M.set64 OUT i v).arr64 CTL).size) :
    ((M.set64 OUT i v).arr64 CTL)[k]'h = (M.arr64 CTL)[k]'(by rwa [L.Mem.size64_set64] at h) :=
  getElem_set64_out M CTL (by decide) i v k h

theorem getElem_set64_out_decl (M : Mem) (i v : Word) (k : Nat)
    (h : k < ((M.set64 OUT i v).arr64 L.Front.DECL).size) :
    ((M.set64 OUT i v).arr64 L.Front.DECL)[k]'h = (M.arr64 L.Front.DECL)[k]'(by rwa [L.Mem.size64_set64] at h) :=
  getElem_set64_out M L.Front.DECL (by decide) i v k h

attribute [simp] L.run_throw

attribute [simp] L.except_error_bind

attribute [simp] L.except_error_map

theorem dite_getElem_pure (A : Array Word) (i : Nat) (e : Err) :
    (if h : i < A.size then (pure A[i] : M Word) else throw e) =
      if i < A.size then pure (A.getD i 0) else throw e := by
  by_cases h : i < A.size <;> simp [h, Array.getD]

/-- The header's words `0`‥`5`, `8`, `9` (the tail of `par_compact`) at `OUT[b‥)`, after the images. -/
def pcTail (m : Mem) (o : Word) (b : Word := 0) : Mem :=
  (((((((m.set64 OUT (b + Nat.toUInt64 0) fzMagic).set64 OUT (b + Nat.toUInt64 1) o).set64 OUT
    (b + Nat.toUInt64 2) (rd64 m L.Front.DECL (Nat.toUInt64 0))).set64 OUT
    (b + Nat.toUInt64 3) (rd64 m CTL (Nat.toUInt64 128))).set64
    OUT (b + Nat.toUInt64 4) frozen.length.toUInt64).set64 OUT (b + Nat.toUInt64 5) (Nat.toUInt64 0)).set64 OUT
    (b + Nat.toUInt64 8) (Nat.toUInt64 0)).set64 OUT (b + Nat.toUInt64 9) hdrW.toUInt64

/-- The images' memory and the buffer's length (the offset after the last image, relative to `b`). -/
def pcImages (m : Mem) (c : Word) (b : Word := 0) : Mem × Word :=
  pcGo c b (List.range frozen.length) m (UInt64.ofNat hdrW)

/-- **The memory after `par_compact(c, b)`**: the images (`c ≠ 0`) and the header entries in
header order from offset `b + hdrW`, then the header's words `0`‥`5`, `8`, `9` at `OUT[b‥)`. -/
def parCompactMem (m : Mem) (c : Word) (b : Word := 0) : Mem :=
  pcTail (pcImages m c b).1 (pcImages m c b).2 b

/-- The header's words `b + 0`‥`b + 5`, `b + 8`, `b + 9` in bounds. -/
def pcHdrOK (sz : Nat) (b : Word) : Prop :=
  (b + Nat.toUInt64 0).toNat < sz ∧ (b + Nat.toUInt64 1).toNat < sz ∧ (b + Nat.toUInt64 2).toNat < sz ∧
    (b + Nat.toUInt64 3).toNat < sz ∧ (b + Nat.toUInt64 4).toNat < sz ∧ (b + Nat.toUInt64 5).toNat < sz ∧
    (b + Nat.toUInt64 8).toNat < sz ∧ (b + Nat.toUInt64 9).toNat < sz

instance (sz : Nat) (b : Word) : Decidable (pcHdrOK sz b) := by unfold pcHdrOK; infer_instance

theorem pcHdrOK_zero (sz : Nat) : pcHdrOK sz 0 ↔ 9 < sz := by
  simp only [pcHdrOK]; constructor
  · intro h; have := h.2.2.2.2.2.2.2; simp at this; omega
  · intro h; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> omega

/-- `par_compact(c, b)` stays in bounds: every `fz_i`, the header's words, `DECL[0]`, `CTL[128]`. -/
def parCompactOK (m : Mem) (c : Word) (b : Word := 0) : Bool :=
  pcOK c b (List.range frozen.length) m (UInt64.ofNat hdrW) && decide (pcHdrOK (m.arr64 OUT).size b) &&
    decide (0 < (m.arr64 L.Front.DECL).size) && decide (128 < (m.arr64 CTL).size)

/-- `par_compact`'s tail: the header's words, then the length. -/
def pcTailS : Stmt :=
    .seq (fzSt 0 (.const fzMagic)) <|
    .seq (fzSt 1 (.var 2)) <|
    .seq (fzSt 2 fzDecl) <|
    .seq (fzSt 3 (fzCtl 128)) <|
    .seq (fzSt 4 (fzC frozen.length)) <|
    .seq (fzSt 5 (fzC 0)) <|
    .seq (fzSt 8 (fzC 0)) <|
    .seq (fzSt 9 (fzC hdrW)) <|
    .ret [.var 2]

theorem parCompactL_eq : parCompactL =
    { nparams := 2, nlocals := 3, body := .seq (.set 2 (fzC hdrW)) (fzCalls.foldr .seq pcTailS) } := by rfl

theorem fzCalls_lookup {p : Prog} (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i)) :
    ∀ i ∈ List.range frozen.length, i < frozen.length ∧ p.lookup (fzName i) = some (fzF i) :=
  fun i hi => ⟨List.mem_range.mp hi, hfz i (List.mem_range.mp hi)⟩

/-- A store to `OUT[b + k]` (`b` local `1`) of a value that evaluates to `w` if `P`, else fails
with `oob`, then `rest`. -/
theorem step_fzSt {p : Prog} {f : Stmt → M Sig} (k : Nat) (v : Expr) (rest : Stmt) (s : St) (w : Word)
    (P : Prop) [Decidable P] (hv : (evalE v).run s = if P then .ok (w, s) else .error .oob) :
    (step p f (.seq (fzSt k v) rest)).run s =
      if P ∧ (s.loc 1 + k.toUInt64).toNat < (s.mem.arr64 OUT).size then
        (step p f rest).run { s with mem := s.mem.set64 OUT (s.loc 1 + k.toUInt64) w }
      else .error .oob := by
  simp only [fzSt, step, StateT.run_bind, evalE, StateT.run_get, pure_bind, fzC, BinOp.eval]
  by_cases hP : P
  · by_cases h : ((s.loc 1).toNat + k) % 18446744073709551616 < (s.mem.arr64 OUT).size
    · simp [h, hv, hP, L.st64]
    · simp [h, hv, hP, L.st64]
  · simp [hv, hP]

theorem rd64_set64_out (m : Mem) (a : ArrId) (ha : (a : TieredArray) ≠ OUT) (i v j : Word) :
    rd64 (m.set64 OUT i v) a j = rd64 m a j := by
  simp only [rd64, Mem.arr64_set64_ne _ _ _ _ _ ha]

theorem evalE_const_run (w : Word) (s : St) :
    (evalE (.const w)).run s = if True then .ok (w, s) else .error .oob := by simp [evalE]; rfl

theorem evalE_var_run (x : Var) (s : St) :
    (evalE (.var x)).run s = if True then .ok (s.loc x, s) else .error .oob := by simp [evalE]; rfl

theorem evalE_ld_run (a : ArrId) (j : Nat) (s : St) :
    (evalE (.ld64 a (.const j.toUInt64))).run s =
      if j.toUInt64.toNat < (s.mem.arr64 a).size then .ok (rd64 s.mem a j.toUInt64, s) else .error .oob := by
  by_cases h : j % 18446744073709551616 < (s.mem.arr64 a).size
  · simp [evalE, ld64, h, rd64, Array.getD]; rfl
  · simp [evalE, ld64, h]

set_option maxHeartbeats 1000000 in
/-- **`par_compact`'s run**: from any state, with fuel `≥ 2`, `par_compact(c, b)` returns the
buffer's length with the memory `parCompactMem` and the caller's locals, or fails with `oob`. -/
theorem parCompact_run {p : Prog} (hp : p.lookup "par_compact" = some parCompactL)
    (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i)) (n : Nat) (s : St) (c b : Word) :
    (invoke p (exec p (n + 2)) "par_compact" [c, b]).run s =
      if parCompactOK s.mem c b then
        .ok ([(pcImages s.mem c b).2], { s with mem := parCompactMem s.mem c b })
      else .error .oob := by
  have hF := OutFrame.pcGo c b (List.range frozen.length) s.mem (UInt64.ofNat hdrW)
  have hx : ∀ st, exec p (n + 2) st = step p (exec p (n + 1)) st := fun _ => rfl
  have hc := fzCalls_run (p := p) n pcTailS _ (fzCalls_lookup hfz)
  rw [← fzCalls_eq] at hc
  simp only [invoke, lookupFn, hp, callFn, hx, parCompactL_eq, step, StateT.run_bind, StateT.run_get,
    StateT.run_set, pure_bind, StateT.run_pure, setLoc, StateT.run_modify]
  simp only [fzC, evalE, StateT.run_pure, pure_bind, hc, L.St.setLoc_loc, Locals.init]
  simp only [parCompactOK, pcImages, Bool.and_eq_true]
  by_cases h1 : pcOK c b (List.range frozen.length) s.mem (UInt64.ofNat hdrW) = true
  · simp only [h1, ite_true, decide_eq_true_eq, true_and]
    generalize hG : pcGo c b (List.range frozen.length) s.mem (UInt64.ofNat hdrW) = G at *
    obtain ⟨M, o⟩ := G
    simp only at hF ⊢
    have e0 : (if (0:Nat) = 2 then hdrW.toUInt64 else [c, b].getD 0 0) = c := rfl
    have e1 : (if (1:Nat) = 2 then hdrW.toUInt64 else [c, b].getD 1 0) = b := rfl
    have eW : hdrW.toUInt64 = UInt64.ofNat hdrW := rfl
    simp only [e0, e1, eW, L.St.setLoc_mem, h1, hG, ite_true]
    generalize hS : ({ mem := M, loc := (({ mem := s.mem, loc := Locals.init [c, b] } : St).setLoc 2
      (UInt64.ofNat hdrW)).loc } : St).setLoc 2 o = S
    have hS1 : S.loc 1 = b := by rw [← hS]; rfl
    have hS2 : S.loc 2 = o := by rw [← hS]; rfl
    have hSm : S.mem = M := by rw [← hS]; rfl
    simp only [pcTailS, fzDecl, fzCtl, fzC]
    simp only [step_fzSt _ _ _ _ _ _ (evalE_const_run _ _), step_fzSt _ _ _ _ _ _ (evalE_var_run _ _),
      step_fzSt _ _ _ _ _ _ (evalE_ld_run _ _ _)]
    simp only [L.Mem.size64_set64, rd64_set64_out _ L.Front.DECL (by decide), rd64_set64_out _ CTL (by decide),
      Mem.arr64_set64_ne _ _ _ _ _ (show (L.Front.DECL : TieredArray) ≠ OUT by decide),
      Mem.arr64_set64_ne _ _ _ _ _ (show (CTL : TieredArray) ≠ OUT by decide), hS1, hS2, hSm, true_and,
      hF.size]
    by_cases hok : (pcHdrOK (s.mem.arr64 OUT).size b ∧ 0 < (s.mem.arr64 L.Front.DECL).size) ∧
        128 < (s.mem.arr64 CTL).size
    · rw [ite_eq_left hok]
      obtain ⟨⟨⟨h0, h1, h2, h3, h4, h5, h8, h9⟩, hd⟩, hc⟩ := hok
      have hd' : (Nat.toUInt64 0).toNat < (s.mem.arr64 L.Front.DECL).size := by simpa using hd
      have hc' : (Nat.toUInt64 128).toNat < (s.mem.arr64 CTL).size := by simpa using hc
      simp only [h0, h1, h2, h3, h4, h5, h8, h9, hd', hc', and_self, ite_true]
      simp [step, evalArgs, evalE, Sig.retVal, Sig.retOr, parCompactMem, pcImages, hG, pcTail, hS2]
      rfl
    · rw [ite_eq_right hok]
      (repeat' split) <;> first | rfl |
        (exfalso; refine hok ⟨⟨?_, ?_⟩, ?_⟩ <;> simp_all [pcHdrOK])
  · simp [h1]

/-! ## What a copy and a store leave in the destination -/

theorem getD_set64_same (m : Mem) (a : ArrId) (i v : Word) (k : Nat) :
    ((m.set64 a i v).arr64 a).getD k 0 =
      if k = i.toNat ∧ k < (m.arr64 a).size then v else (m.arr64 a).getD k 0 := by
  rw [Mem.arr64_set64_same]
  simp only [Array.getD_eq_getD_getElem?]
  by_cases h1 : i.toNat = k <;> by_cases h2 : k < (m.arr64 a).size <;> simp_all <;> omega

theorem getD_copy64 {d s : ArrId} (hds : d ≠ s) : ∀ (n : Nat) (m : Mem) (di si : Word),
    di.toNat + n ≤ 2 ^ 64 → si.toNat + n ≤ 2 ^ 64 → ∀ k : Nat,
    ((m.copy64 d di s si n).arr64 d).getD k 0 =
      if di.toNat ≤ k ∧ k < di.toNat + n ∧ k < (m.arr64 d).size then
        (m.arr64 s).getD (si.toNat + (k - di.toNat)) 0
      else (m.arr64 d).getD k 0
  | 0, m, di, si, _, _, k => by simp [Mem.copy64]; omega
  | n + 1, m, di, si, hd, hs, k => by
    simp only [Mem.copy64]
    have hsd : s ≠ d := fun e => hds e.symm
    cases n with
    | zero =>
      simp only [Mem.copy64, getD_set64_same, getElem!_def]
      by_cases h1 : k = di.toNat <;> by_cases h2 : k < (m.arr64 d).size
      · subst h1; simp [h2, Array.getD_eq_getD_getElem?]; cases (m.arr64 s)[si.toNat]? <;> rfl
      · subst h1; simp [h2]
      · simp only [h1, false_and, ite_false]; split <;> first | rfl | omega
      · simp only [h1, false_and, ite_false]; split <;> first | rfl | omega
    | succ n =>
      have hd1 : (di + 1).toNat = di.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (si + 1).toNat = si.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [getD_copy64 hds (n + 1) _ (di + 1) (si + 1) (by omega) (by omega) k, hd1, hs1,
        Mem.arr64_set64_ne _ _ _ _ _ (TieredArray.t0_ne hsd), L.Mem.size64_set64, getD_set64_same]
      by_cases h1 : k = di.toNat
      · subst h1
        have : ¬ (di.toNat + 1 ≤ di.toNat) := by omega
        simp only [this, false_and, ite_false, true_and, Nat.sub_self, Nat.add_zero, Nat.le_refl]
        by_cases h2 : di.toNat < (m.arr64 d).size
        · simp [h2, getElem!_def, Array.getD_eq_getD_getElem?]; cases (m.arr64 s)[si.toNat]? <;> rfl
        · simp [h2]
      · simp only [h1, false_and, ite_false]
        by_cases h3 : di.toNat + 1 ≤ k ∧ k < di.toNat + 1 + (n + 1) ∧ k < (m.arr64 d).size
        · rw [ite_eq_left h3, ite_eq_left (by omega)]; congr 1; omega
        · rw [ite_eq_right h3, ite_eq_right (by omega)]

/-! ## Offsets -/

/-- The offset of frozen entry `i`'s image: `hdrW` plus the extents before it (as words). -/
def fzOff (m : Mem) (i : Nat) : Word :=
  (List.range i).foldl (fun o j => o + fzEv m (fzAt j).e) (UInt64.ofNat hdrW)

/-- The extents before entry `i`, as a number. -/
def fzSum (m : Mem) (i : Nat) : Nat :=
  (List.range i).foldl (fun s j => s + (fzEv m (fzAt j).e).toNat) 0

theorem fzOff_succ (m : Mem) (i : Nat) : fzOff m (i + 1) = fzOff m i + fzEv m (fzAt i).e := by
  simp [fzOff, List.range_succ, List.foldl_append]

theorem fzSum_succ (m : Mem) (i : Nat) : fzSum m (i + 1) = fzSum m i + (fzEv m (fzAt i).e).toNat := by
  simp [fzSum, List.range_succ, List.foldl_append]

theorem fzExt_eq (m : Mem) (z : Fz) : fzExt m z = (fzEv m z.e).toNat := rfl

theorem pcGo_append (c b : Word) : ∀ (l₁ l₂ : List Nat) (m : Mem) (o : Word),
    pcGo c b (l₁ ++ l₂) m o = pcGo c b l₂ (pcGo c b l₁ m o).1 (pcGo c b l₁ m o).2
  | [], _, _, _ => rfl
  | _ :: l₁, l₂, _, _ => pcGo_append c b l₁ l₂ _ _

theorem pcOK_append (c b : Word) : ∀ (l₁ l₂ : List Nat) (m : Mem) (o : Word),
    pcOK c b (l₁ ++ l₂) m o = (pcOK c b l₁ m o && pcOK c b l₂ (pcGo c b l₁ m o).1 (pcGo c b l₁ m o).2)
  | [], _, _, _ => by simp [pcOK, pcGo]
  | i :: l₁, l₂, m, o => by simp [pcOK, pcGo, pcOK_append c b l₁ l₂, Bool.and_assoc]

theorem pcGo_range_succ (c b : Word) (m : Mem) (n : Nat) :
    pcGo c b (List.range (n + 1)) m (UInt64.ofNat hdrW) =
      ((fzStep (pcGo c b (List.range n) m (UInt64.ofNat hdrW)).1 c n (fzAt n)
          (pcGo c b (List.range n) m (UInt64.ofNat hdrW)).2 b),
        (pcGo c b (List.range n) m (UInt64.ofNat hdrW)).2 +
          fzEv (pcGo c b (List.range n) m (UInt64.ofNat hdrW)).1 (fzAt n).e) := by
  rw [List.range_succ, pcGo_append]; rfl

theorem pcOK_range_succ (c b : Word) (m : Mem) (n : Nat) :
    pcOK c b (List.range (n + 1)) m (UInt64.ofNat hdrW) =
      (pcOK c b (List.range n) m (UInt64.ofNat hdrW) &&
        fzOK (pcGo c b (List.range n) m (UInt64.ofNat hdrW)).1 c n (fzAt n)
          (pcGo c b (List.range n) m (UInt64.ofNat hdrW)).2 b) := by
  rw [List.range_succ, pcOK_append]; simp [pcOK]

/-- The images' offsets (relative to the header) are `fzOff`, and the extents are read as in the
memory before. -/
theorem pcGo_off (c b : Word) (m : Mem) : ∀ n, n ≤ frozen.length →
    (pcGo c b (List.range n) m (UInt64.ofNat hdrW)).2 = fzOff m n
  | 0, _ => rfl
  | n + 1, h => by
    rw [pcGo_range_succ, pcGo_off c b m n (by omega), fzOff_succ,
      (fzEv_congr (OutFrame.pcGo c b (List.range n) m _).arr _ (fzAt_ok (by omega)).1).1]

theorem pcImages_snd (m : Mem) (c : Word) (b : Word := 0) : (pcImages m c b).2 = fzOff m frozen.length :=
  pcGo_off c b m _ (Nat.le_refl _)

theorem fzSum_mono (m : Mem) {j n : Nat} (h : j ≤ n) : fzSum m j ≤ fzSum m n := by
  induction n with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge j (n + 1) with h' | h'
    · rw [fzSum_succ]; have := ih (by omega); omega
    · have : j = n + 1 := by omega
      subst this; exact Nat.le_refl _

theorem toNat_hdr (k : Nat) (h : k < 2 ^ 64) : (k.toUInt64).toNat = k := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' h]

/-- A word plus a small number, without wrapping. -/
theorem toNat_badd (b : Word) (k : Nat) (h : b.toNat + k < 2 ^ 64) : (b + k.toUInt64).toNat = b.toNat + k := by
  rw [UInt64.toNat_add, toNat_hdr k (by omega)]; exact Nat.mod_eq_of_lt h

theorem toNat_add_lt (b o : Word) (h : b.toNat + o.toNat < 2 ^ 64) : (b + o).toNat = b.toNat + o.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-- **The images and header entries after a run that stayed in bounds**, the header at `OUT[b‥)`:
from offset `hdrW` (relative), the header entries of the entries before `n` hold their offsets and
extents, and (if `c ≠ 0`) each image holds its source's prefix; the offsets do not wrap; the
words below `b` are as before. -/
theorem pcGo_good (m : Mem) (c b : Word) (hW : b.toNat + hdrW ≤ (m.arr64 OUT).size)
    (hb : b.toNat + hdrW < 2 ^ 64)
    (hlt : c ≠ 0 → (m.arr64 OUT).size < 2 ^ 64) : ∀ n, n ≤ frozen.length →
    pcOK c b (List.range n) m (UInt64.ofNat hdrW) = true →
    (c ≠ 0 → (∀ j ≤ n, (fzOff m j).toNat = hdrW + fzSum m j) ∧
      b.toNat + hdrW + fzSum m n ≤ (m.arr64 OUT).size) ∧
    (∀ j < n,
      ((pcGo c b (List.range n) m (UInt64.ofNat hdrW)).1.arr64 OUT).getD (b.toNat + (10 + 2 * j)) 0 = fzOff m j ∧
      ((pcGo c b (List.range n) m (UInt64.ofNat hdrW)).1.arr64 OUT).getD (b.toNat + (11 + 2 * j)) 0 =
        fzEv m (fzAt j).e) ∧
    (c ≠ 0 → ∀ j < n, ∀ t < (fzEv m (fzAt j).e).toNat,
      ((pcGo c b (List.range n) m (UInt64.ofNat hdrW)).1.arr64 OUT).getD (b.toNat + hdrW + fzSum m j + t) 0 =
        (m.arr64 (fzAt j).src).getD t 0) ∧
    (∀ k < b.toNat, ((pcGo c b (List.range n) m (UInt64.ofNat hdrW)).1.arr64 OUT).getD k 0 =
      (m.arr64 OUT).getD k 0)
  | 0, _, _ => ⟨fun _ => ⟨fun j hj => by
      have : j = 0 := by omega
      subst this; simp [fzOff, fzSum, hdrW]; decide, by simp [fzSum]; omega⟩,
      fun j hj => absurd hj (by omega), fun _ j hj => absurd hj (by omega), fun _ _ => rfl⟩
  | n + 1, hn, hok => by
    rw [pcOK_range_succ, Bool.and_eq_true] at hok
    obtain ⟨ih1, ih2, ih3, ih4⟩ := pcGo_good m c b hW hb hlt n (by omega) hok.1
    have hF := OutFrame.pcGo c b (List.range n) m (UInt64.ofNat hdrW)
    have hoff := pcGo_off c b m n (by omega)
    have hz := fzAt_ok (i := n) (by omega)
    have he := (fzEv_congr hF.arr _ hz.1)
    have hk := hok.2
    rw [pcGo_range_succ]
    generalize hM : (pcGo c b (List.range n) m (UInt64.ofNat hdrW)).1 = M at *
    rw [hoff] at hk ⊢
    simp only [fzOK, he.1, he.2, hF.size, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hk
    obtain ⟨⟨⟨hld, hcp⟩, h10⟩, h11⟩ := hk
    have hfl := frozen_length
    have hW' := hdrW_eq
    rw [toNat_badd _ _ (by omega)] at h10 h11
    -- the offsets
    have hO : c ≠ 0 → (fzOff m n).toNat = hdrW + fzSum m n ∧
        (b + fzOff m n).toNat = b.toNat + (fzOff m n).toNat ∧
        b.toNat + (fzOff m n).toNat + (fzEv m (fzAt n).e).toNat ≤ (m.arr64 OUT).size ∧
        (fzEv m (fzAt n).e).toNat ≤ (m.arr64 (fzAt n).src).size := fun hc => by
      have h1 := (ih1 hc).1 n (Nat.le_refl _)
      have h2 := (ih1 hc).2
      have h3 := hlt hc
      have e : (b + fzOff m n).toNat = b.toNat + (fzOff m n).toNat := toNat_add_lt _ _ (by omega)
      rcases hcp with h | h
      · exact absurd h hc
      · rw [e] at h; exact ⟨h1, e, h⟩
    refine ⟨fun hc => ?_, fun j hj => ?_, fun hc j hj t ht => ?_, fun k hk => ?_⟩
    · obtain ⟨hO1, -, hO2, -⟩ := hO hc
      have hlt' := hlt hc
      have hS : (fzOff m (n + 1)).toNat = hdrW + fzSum m (n + 1) := by
        rw [fzOff_succ, UInt64.toNat_add, fzSum_succ, hO1]; omega
      refine ⟨fun j hj => ?_, by rw [fzSum_succ]; omega⟩
      rcases Nat.lt_or_ge j (n + 1) with h' | h'
      · exact (ih1 hc).1 j (by omega)
      · have : j = n + 1 := by omega
        subst this; exact hS
    all_goals simp only [fzStep]
    all_goals generalize hM1 : fzCopy M c (fzAt n) (fzOff m n) b = M1
    all_goals have hM1s : (M1.arr64 OUT).size = (M.arr64 OUT).size := by
                rw [← hM1, fzCopy]; split <;> simp
    all_goals have hM1i : c ≠ 0 → ∀ k, (M1.arr64 OUT).getD k 0 =
          if b.toNat + (fzOff m n).toNat ≤ k ∧ k < b.toNat + (fzOff m n).toNat + (fzEv m (fzAt n).e).toNat ∧
            k < (M.arr64 OUT).size then
            (m.arr64 (fzAt n).src).getD (k - (b.toNat + (fzOff m n).toNat)) 0
          else (M.arr64 OUT).getD k 0 := by
                intro hc k
                obtain ⟨hO1, hO2, hO3, hO4⟩ := hO hc
                have := (fzEv m (fzAt n).e).toNat_lt
                have := hlt hc
                rw [← hM1, fzCopy, ite_eq_left hc, he.1, getD_copy64 (Ne.symm hz.2) _ _ _ _ (by omega) (by simp; omega),
                  hF.arr _ (TieredArray.t0_ne hz.2), hO2]
                simp
    all_goals have hM1h : ∀ k, k < b.toNat + hdrW → (M1.arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 := by
                intro k hk
                by_cases hc : c = 0
                · rw [← hM1, fzCopy, ite_eq_right (by simpa using hc)]
                · rw [hM1i hc, ite_eq_right]
                  have := (hO hc).1
                  omega
    all_goals simp only [getD_set64_same, L.Mem.size64_set64, hM1s, he.1,
        toNat_badd b (10 + 2 * n) (by omega), toNat_badd b (11 + 2 * n) (by omega)]
    · rcases (by omega : j < n ∨ j = n) with hj' | rfl
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          hM1h _ (by omega), hM1h _ (by omega)]
        exact ih2 j hj'
      · rw [hF.size] at *
        rw [ite_eq_right (by omega), ite_eq_left ⟨rfl, by omega⟩, ite_eq_left ⟨rfl, by omega⟩]
        exact ⟨rfl, rfl⟩
    · obtain ⟨hO1, hO2, hO3, hO4⟩ := hO hc
      have hsj := fzSum_mono m (j := j) (n := n) (by omega)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), hM1i hc]
      rcases (by omega : j < n ∨ j = n) with hj' | rfl
      · have hsj' := fzSum_mono m (j := j + 1) (n := n) (by omega)
        rw [fzSum_succ] at hsj'
        rw [ite_eq_right (by omega)]
        exact ih3 hc j hj' t ht
      · rw [ite_eq_left (by rw [hF.size]; omega)]
        congr 1; omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hM1h _ (by omega)]
      exact ih4 k hk

/-! ## The memory after `par_compact`

The general forms (`_b`) for the header at `OUT[b‥)`, `b + hdrW` below `2^64`; the flat forms
(`b = 0`) keep their statements. -/

theorem OutFrame.pcTail (M : Mem) (o b : Word) : OutFrame M (pcTail M o b) :=
  (((((((OutFrame.set64 _ _ _).trans (OutFrame.set64 _ _ _)).trans (OutFrame.set64 _ _ _)).trans
    (OutFrame.set64 _ _ _)).trans (OutFrame.set64 _ _ _)).trans (OutFrame.set64 _ _ _)).trans
    (OutFrame.set64 _ _ _)).trans (OutFrame.set64 _ _ _)

/-- **`par_compact` writes only `OUT`.** -/
theorem parCompactMem_out_b (m : Mem) (c b : Word) : OutFrame m (parCompactMem m c b) :=
  (OutFrame.pcGo c b (List.range frozen.length) m (UInt64.ofNat hdrW)).trans (OutFrame.pcTail _ _ _)

theorem parCompactMem_out (m : Mem) (c : Word) : OutFrame m (parCompactMem m c) :=
  parCompactMem_out_b m c 0

/-- **`par_compact`'s write set**, as a `MemFrame`: only `OUT`. -/
theorem parCompactMem_frame (m : Mem) (c : Word) (b : Word := 0) : MemFrame [OUT] [] m (parCompactMem m c b) := by
  have h := parCompactMem_out_b m c b
  refine ⟨fun b hb _ => h.arr b (by simpa using hb), fun x _ => ?_, h.size⟩
  rw [h.arr CTL (by decide)]

/-- A run that stayed in bounds had room for the header. -/
theorem parCompactOK_hdr_b {m : Mem} {c b : Word} (h : parCompactOK m c b = true)
    (hb : b.toNat + hdrW < 2 ^ 64) : b.toNat + hdrW ≤ (m.arr64 OUT).size := by
  simp only [parCompactOK, Bool.and_eq_true] at h
  have h1 := h.1.1.1
  obtain ⟨k, hk⟩ : ∃ k, frozen.length = k + 1 := ⟨_, frozen_length⟩
  have hfl := frozen_length
  rw [hk, pcOK_range_succ, Bool.and_eq_true] at h1
  have h2 := h1.2
  simp only [fzOK, Bool.and_eq_true, decide_eq_true_eq] at h2
  have h3 := h2.2
  have  := hdrW_eq
  rw [toNat_badd _ _ (by omega), (OutFrame.pcGo c b _ m _).size] at h3
  omega

theorem parCompactOK_hdr {m : Mem} {c : Word} (h : parCompactOK m c = true) :
    hdrW ≤ (m.arr64 OUT).size := by
  have := parCompactOK_hdr_b h (by simp; have := hdrW_eq; omega)
  simpa using this

theorem getD_pcTail_lo_b (M : Mem) (o b : Word) (h : pcHdrOK (M.arr64 OUT).size b)
    (hb : b.toNat + 10 < 2 ^ 64) :
    ((pcTail M o b).arr64 OUT).getD (b.toNat + 0) 0 = fzMagic ∧
    ((pcTail M o b).arr64 OUT).getD (b.toNat + 1) 0 = o ∧
    ((pcTail M o b).arr64 OUT).getD (b.toNat + 2) 0 = rd64 M L.Front.DECL 0 ∧
    ((pcTail M o b).arr64 OUT).getD (b.toNat + 3) 0 = rd64 M CTL 128 ∧
    ((pcTail M o b).arr64 OUT).getD (b.toNat + 4) 0 = UInt64.ofNat frozen.length ∧
    ((pcTail M o b).arr64 OUT).getD (b.toNat + 5) 0 = 0 ∧
    ((pcTail M o b).arr64 OUT).getD (b.toNat + 8) 0 = 0 ∧
    ((pcTail M o b).arr64 OUT).getD (b.toNat + 9) 0 = UInt64.ofNat hdrW := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h8, h9⟩ := h
  rw [toNat_badd _ _ (by omega)] at h0 h1 h2 h3 h4 h5 h8 h9
  simp only [pcTail, getD_set64_same, L.Mem.size64_set64, toNat_badd _ _ (by omega : b.toNat + 0 < 2 ^ 64),
    toNat_badd _ _ (by omega : b.toNat + 1 < 2 ^ 64), toNat_badd _ _ (by omega : b.toNat + 2 < 2 ^ 64),
    toNat_badd _ _ (by omega : b.toNat + 3 < 2 ^ 64), toNat_badd _ _ (by omega : b.toNat + 4 < 2 ^ 64),
    toNat_badd _ _ (by omega : b.toNat + 5 < 2 ^ 64), toNat_badd _ _ (by omega : b.toNat + 8 < 2 ^ 64),
    toNat_badd _ _ (by omega : b.toNat + 9 < 2 ^ 64)]
  simp (config := { decide := true }) [h1, h2, h3, h4, h5, h8, h9]
  exact fun h => absurd h (by omega)

theorem getD_pcTail_hi_b (M : Mem) (o b : Word) (k : Nat) (hk : k < b.toNat ∨ b.toNat + 10 ≤ k)
    (hb : b.toNat + 10 < 2 ^ 64) :
    ((pcTail M o b).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 := by
  simp only [pcTail, getD_set64_same, L.Mem.size64_set64, toNat_badd _ _ (by omega : b.toNat + 0 < 2 ^ 64),
    toNat_badd _ _ (by omega : b.toNat + 1 < 2 ^ 64), toNat_badd _ _ (by omega : b.toNat + 2 < 2 ^ 64),
    toNat_badd _ _ (by omega : b.toNat + 3 < 2 ^ 64), toNat_badd _ _ (by omega : b.toNat + 4 < 2 ^ 64),
    toNat_badd _ _ (by omega : b.toNat + 5 < 2 ^ 64), toNat_badd _ _ (by omega : b.toNat + 8 < 2 ^ 64),
    toNat_badd _ _ (by omega : b.toNat + 9 < 2 ^ 64)]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem getD_pcTail_hi (M : Mem) (o : Word) (k : Nat) (hk : 10 ≤ k) :
    ((pcTail M o).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 :=
  getD_pcTail_hi_b M o 0 k (by simp; omega) (by simp)

/-- **The header's words** `0`‥`5`, `8`, `9` at `OUT[b‥)`: the magic, the buffer's length, the
number of records (`DECL[0]`), the stream index's next counter (`CTL[128]`), the number of frozen
entries, no next phase, the header's own entry. -/
theorem parCompactMem_hdr_b {m : Mem} {c b : Word} (h : parCompactOK m c b = true)
    (hb : b.toNat + hdrW < 2 ^ 64) :
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + 0) 0 = fzMagic ∧
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + 1) 0 = fzOff m frozen.length ∧
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + 2) 0 = rd64 m L.Front.DECL 0 ∧
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + 3) 0 = rd64 m CTL 128 ∧
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + 4) 0 = UInt64.ofNat frozen.length ∧
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + 5) 0 = 0 ∧
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + 8) 0 = 0 ∧
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + 9) 0 = UInt64.ofNat hdrW := by
  have hF := OutFrame.pcGo c b (List.range frozen.length) m (UInt64.ofNat hdrW)
  have hH : pcHdrOK ((pcImages m c b).1.arr64 OUT).size b := by
    simp only [parCompactOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [pcImages, hF.size]; exact h.1.1.2
  have := getD_pcTail_lo_b (pcImages m c b).1 (pcImages m c b).2 b hH (by have := hdrW_eq; omega)
  rw [pcImages_snd m c b] at this
  simp only [parCompactMem, pcImages_snd m c b]
  refine ⟨this.1, this.2.1, ?_, ?_, this.2.2.2.2⟩
  · rw [this.2.2.1]
    simp only [rd64, pcImages, hF.arr L.Front.DECL (by decide)]
  · rw [this.2.2.2.1]
    simp only [rd64, pcImages, hF.arr CTL (by decide)]

theorem parCompactMem_hdr {m : Mem} {c : Word} (h : parCompactOK m c = true) :
    ((parCompactMem m c).arr64 OUT).getD 0 0 = fzMagic ∧
    ((parCompactMem m c).arr64 OUT).getD 1 0 = fzOff m frozen.length ∧
    ((parCompactMem m c).arr64 OUT).getD 2 0 = rd64 m L.Front.DECL 0 ∧
    ((parCompactMem m c).arr64 OUT).getD 3 0 = rd64 m CTL 128 ∧
    ((parCompactMem m c).arr64 OUT).getD 4 0 = UInt64.ofNat frozen.length ∧
    ((parCompactMem m c).arr64 OUT).getD 8 0 = 0 ∧
    ((parCompactMem m c).arr64 OUT).getD 9 0 = UInt64.ofNat hdrW := by
  have := parCompactMem_hdr_b h (by simp; have := hdrW_eq; omega)
  simp only [UInt64.toNat_zero, Nat.zero_add] at this
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.2⟩

/-- Word `5` of the header (no next phase). -/
theorem parCompactMem_w5 {m : Mem} {c : Word} (h : parCompactOK m c = true) :
    ((parCompactMem m c).arr64 OUT).getD 5 0 = 0 := by
  have := parCompactMem_hdr_b h (by simp; have := hdrW_eq; omega)
  simp only [UInt64.toNat_zero, Nat.zero_add] at this
  exact this.2.2.2.2.2.1

/-- **The header entries**: entry `i` holds its image's offset `fzOff m i` (relative to the
header) and extent `fzExt m (fzAt i)` (for `c ≠ 0` the offsets must not wrap: `OUT` below `2^64`
words). -/
theorem parCompactMem_entry_b {m : Mem} {c b : Word} (h : parCompactOK m c b = true)
    (hb : b.toNat + hdrW < 2 ^ 64)
    (hlt : c ≠ 0 → (m.arr64 OUT).size < 2 ^ 64) {i : Nat} (hi : i < frozen.length) :
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + (10 + 2 * i)) 0 = fzOff m i ∧
    ((parCompactMem m c b).arr64 OUT).getD (b.toNat + (11 + 2 * i)) 0 = UInt64.ofNat (fzExt m (fzAt i)) := by
  have hW := parCompactOK_hdr_b h hb
  simp only [parCompactOK, Bool.and_eq_true] at h
  have hg := (pcGo_good m c b hW hb hlt frozen.length (Nat.le_refl _) h.1.1.1).2.1 i hi
  have := hdrW_eq
  simp only [parCompactMem, getD_pcTail_hi_b _ _ _ _ (Or.inr (by omega : b.toNat + 10 ≤ b.toNat + (10 + 2 * i)))
    (by omega), getD_pcTail_hi_b _ _ _ _ (Or.inr (by omega : b.toNat + 10 ≤ b.toNat + (11 + 2 * i))) (by omega),
    pcImages, fzExt_eq, UInt64.ofNat_toNat]
  exact hg

theorem parCompactMem_entry {m : Mem} {c : Word} (h : parCompactOK m c = true)
    (hlt : c ≠ 0 → (m.arr64 OUT).size < 2 ^ 64) {i : Nat} (hi : i < frozen.length) :
    ((parCompactMem m c).arr64 OUT).getD (10 + 2 * i) 0 = fzOff m i ∧
    ((parCompactMem m c).arr64 OUT).getD (11 + 2 * i) 0 = UInt64.ofNat (fzExt m (fzAt i)) := by
  have := parCompactMem_entry_b h (by simp; have := hdrW_eq; omega) hlt hi
  simpa using this

/-- **The images** (`c ≠ 0`): image `i` sits at `OUT[b + fzOff m i ‥ b + fzOff m i + fzExt m (fzAt i))`
(the offset `hdrW` plus the extents before it, no wrap) and holds the prefix
`(fzAt i).src[0 ‥ fzExt m (fzAt i))` of the memory before `par_compact`. -/
theorem parCompactMem_img_b {m : Mem} {c b : Word} (h : parCompactOK m c b = true) (hc : c ≠ 0)
    (hb : b.toNat + hdrW < 2 ^ 64)
    (hlt : (m.arr64 OUT).size < 2 ^ 64) {i : Nat} (hi : i < frozen.length) :
    (fzOff m i).toNat = hdrW + fzSum m i ∧
    ∀ t < fzExt m (fzAt i),
      ((parCompactMem m c b).arr64 OUT).getD (b.toNat + (fzOff m i).toNat + t) 0 =
        (m.arr64 (fzAt i).src).getD t 0 := by
  have hW := parCompactOK_hdr_b h hb
  simp only [parCompactOK, Bool.and_eq_true] at h
  have hg := pcGo_good m c b hW hb (fun _ => hlt) frozen.length (Nat.le_refl _) h.1.1.1
  have ho := hg.1 hc |>.1 i (by omega)
  refine ⟨ho, fun t ht => ?_⟩
  have  := hdrW_eq
  rw [parCompactMem, getD_pcTail_hi_b _ _ _ _ (Or.inr (by omega)) (by omega), ho, ← Nat.add_assoc]
  exact hg.2.2.1 hc i hi t ht

theorem parCompactMem_img {m : Mem} {c : Word} (h : parCompactOK m c = true) (hc : c ≠ 0)
    (hlt : (m.arr64 OUT).size < 2 ^ 64) {i : Nat} (hi : i < frozen.length) :
    (fzOff m i).toNat = hdrW + fzSum m i ∧
    ∀ t < fzExt m (fzAt i),
      ((parCompactMem m c).arr64 OUT).getD ((fzOff m i).toNat + t) 0 =
        (m.arr64 (fzAt i).src).getD t 0 := by
  have := parCompactMem_img_b h hc (by simp; have := hdrW_eq; omega) hlt hi
  simpa using this

/-- **The words below the header** are as before. -/
theorem parCompactMem_low_b {m : Mem} {c b : Word} (h : parCompactOK m c b = true)
    (hb : b.toNat + hdrW < 2 ^ 64) (hlt : c ≠ 0 → (m.arr64 OUT).size < 2 ^ 64) {k : Nat} (hk : k < b.toNat) :
    ((parCompactMem m c b).arr64 OUT).getD k 0 = (m.arr64 OUT).getD k 0 := by
  have hW := parCompactOK_hdr_b h hb
  simp only [parCompactOK, Bool.and_eq_true] at h
  have hg := pcGo_good m c b hW hb hlt frozen.length (Nat.le_refl _) h.1.1.1
  have  := hdrW_eq
  rw [parCompactMem, getD_pcTail_hi_b _ _ _ _ (Or.inl hk) (by omega)]
  exact hg.2.2.2 k hk

/-- **`par_compact` as a triple** (any fuel): a returning call stayed in bounds, keeps the caller's
locals, ends in `parCompactMem` and returns the buffer's length. -/
theorem parCompact_spec {p : Prog} (hp : p.lookup "par_compact" = some parCompactL)
    (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i)) (n : Nat) (s₀ : St)
    (c b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "par_compact" [c, b]
    ⦃fun r s' => LocEq s' s₀ ∧ parCompactOK s₀.mem c b = true ∧
      s'.mem = parCompactMem s₀.mem c b ∧ r = [fzOff s₀.mem frozen.length]; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  match n with
  | 0 => simp [invoke, lookupFn, hp, callFn, exec] at hrun
  | 1 =>
    have h0 := hfz 0 (by decide)
    simp only [invoke, lookupFn, hp, callFn, exec, parCompactL_eq, fzCalls_eq] at hrun
    rw [frozen_length, List.range_succ_eq_map] at hrun
    simp only [List.map_cons, List.foldr_cons, fzCall] at hrun
    simp [h0, evalArgs, evalE, setLoc, fzC, step, invoke, lookupFn, callFn] at hrun
  | n + 2 =>
    rw [parCompact_run hp hfz n] at hrun
    split at hrun
    · rename_i h
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨rfl, h, rfl, by rw [pcImages_snd _ _ b]⟩
    · cases hrun

end L.Arena
