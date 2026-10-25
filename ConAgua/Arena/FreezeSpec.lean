import ConAgua.Arena.FreezeRel

/-!
# The frozen buffer's spec: `fz_i` and `par_compact` (lane parmode, entry 1)

docs/design/parmode.md, "Redesign" and "Step 4" (a). `par_compact(vis, c)` (`Arena/Freeze.lean`)
writes the frozen buffer into `OUT`. Here its run, as a function of the memory:

* `fzStep m c i z o`: what `fz_i(o, c)` does for the prefix image `z` (`fzPreG z.src z.e i`): if
  `c ≠ 0` the prefix `z.src[0‥e)` copied to `OUT[o‥o+e)`, then the header entry `(o, e)` at
  `OUT[10+2i]`, `OUT[11+2i]` (`e = fzEv m z.e`, the extent); `fzPreG_run`: the run is that memory
  with the result `o + e`, or `oob` (`fzOK`: the extent's loads, the copy and the two header words
  in bounds).
* `parCompactMem m vis c`: the 58 images in header order from offset `hdrW`, then the header's
  words `0`‥`4`, `8`, `9`; `parCompact_run`: the run of `par_compact(vis, c)` (fuel `≥ 2`) is
  that memory with the result `fzOff m 58` (the buffer's length), or `oob` (`parCompactOK`).
* What the memory holds: nothing but `OUT` changes (`parCompactMem_frame`, `MemFrame [OUT] []`);
  the header words (`parCompactMem_hdr*`); for `c ≠ 0` each image
  `OUT[fzOff m i ‥ fzOff m i + fzExt m zᵢ) = zᵢ.src[0 ‥ fzExt m zᵢ)` (`parCompactMem_img`).

The extents read only arrays other than `OUT` (`Expr.fzOk`, checked for `frozen`), so every
`fz_i` computes its extent as in the memory before `par_compact` (`fzExt m z`).
-/

set_option linter.unusedSimpArgs false

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
  | .ldc _ _, h, _ | .glob _, h, _ | .ld64t _ _ _, h, _ | .len64t _ _, h, _ | .ld8x8 _ _, h, _ =>
    by simp [Expr.fzOk] at h

/-- Memories that agree on every array but `OUT` give extents the same values. -/
theorem fzEv_congr {m m' : Mem} (h : ∀ a, a ≠ OUT → m'.arr64 a = m.arr64 a) :
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
    simp [fzEv_ld64, Expr.ldOk, rd64, h1, h2, h a he.1]
  | .var _, h | .ld8 _ _, h | .len8 _, h | .len64 _, h | .cmpw _ _ _, h
  | .ldc _ _, h | .glob _, h | .ld64t _ _ _, h | .len64t _ _, h | .ld8x8 _ _, h =>
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
      · simp [ld64, h2, fzEv_ld64, rd64, Array.getD, Array.getElem?_eq_getElem h2]; rfl
      · simp [ld64, h2]; rfl
    · simp [h1]; rfl
  | .var _, h, _ | .ld8 _ _, h, _ | .len8 _, h, _ | .len64 _, h, _ | .cmpw _ _ _, h, _
  | .ldc _ _, h, _ | .glob _, h, _ | .ld64t _ _ _, h, _ | .len64t _ _, h, _ | .ld8x8 _ _, h, _ =>
    by simp [Expr.fzOk] at h

/-! ## Stores and copies -/

attribute [local simp] size_set64

@[simp] theorem size_copy64 (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) (n : Nat)
    (b : ArrId) : ((m.copy64 d di s si n).arr64 b).size = (m.arr64 b).size := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy64]; rw [ih, size_set64]

theorem arr64_copy64_ne (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) (n : Nat)
    {b : ArrId} (h : b ≠ d) : (m.copy64 d di s si n).arr64 b = m.arr64 b := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy64]; rw [ih, Mem.arr64_set64_ne _ _ _ _ _ h]

/-! ## `fz_i`: one prefix image -/

/-- The memory after `fz_i(o, c)` for the prefix image `z` in header entry `i` (no bounds: an
out-of-bounds store writes nothing, but then the run is `oob`, `fzOK`). -/
def fzStep (m : Mem) (c : Word) (i : Nat) (z : Fz) (o : Word) : Mem :=
  (((if c ≠ 0 then m.copy64 OUT o z.src 0 (fzEv m z.e).toNat else m).set64 OUT
    (10 + 2 * i).toUInt64 o).set64 OUT (11 + 2 * i).toUInt64 (fzEv m z.e))

/-- `fz_i(o, c)` stays in bounds: the extent's loads, the copy (if `c ≠ 0`), the two header words. -/
def fzOK (m : Mem) (c : Word) (i : Nat) (z : Fz) (o : Word) : Bool :=
  z.e.ldOk m &&
    (c == 0 || decide (o.toNat + (fzEv m z.e).toNat ≤ (m.arr64 OUT).size ∧
      (fzEv m z.e).toNat ≤ (m.arr64 z.src).size)) &&
    decide ((10 + 2 * i).toUInt64.toNat < (m.arr64 OUT).size) &&
    decide ((11 + 2 * i).toUInt64.toNat < (m.arr64 OUT).size)

/-- **`fz_i`'s run**: from any state, with fuel, `fz_i(o, c)` returns `o + e` (`e` the extent)
with the memory `fzStep` and the caller's locals, or fails with `oob`. -/
theorem fzPreG_run {p : Prog} {f : FnName} {z : Fz} {i : Nat}
    (hl : p.lookup f = some (fzPreG z.src z.e i)) (he : z.e.fzOk = true) (n : Nat) (s : St)
    (o c : Word) :
    (invoke p (exec p (n + 1)) f [o, c]).run s =
      if fzOK s.mem c i z o then
        .ok ([o + fzEv s.mem z.e], { s with mem := fzStep s.mem c i z o })
      else .error .oob := by
  simp only [invoke, lookupFn, hl, callFn, exec, step, fzPreG, StateT.run_bind, StateT.run_get,
    StateT.run_set, pure_bind, evalE_fz z.e he]
  by_cases h1 : z.e.ldOk s.mem = true
  · by_cases h3 : (10 + 2 * i) % 18446744073709551616 < (s.mem.arr64 OUT).size <;>
    by_cases h4 : (11 + 2 * i) % 18446744073709551616 < (s.mem.arr64 OUT).size <;>
    by_cases hc : c = 0
    all_goals try by_cases h2 : UInt64.toNat o + UInt64.toNat (fzEv s.mem z.e) ≤ (s.mem.arr64 OUT).size ∧
                  UInt64.toNat (fzEv s.mem z.e) ≤ (s.mem.arr64 z.src).size
    all_goals simp [h1, hc, h3, h4, *, fzOK, fzStep, setLoc, St.setLoc, evalC, evalE, warr, st64,
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
def pcGo (c : Word) : List Nat → Mem → Word → Mem × Word
  | [], m, o => (m, o)
  | i :: is, m, o => pcGo c is (fzStep m c i (fzAt i) o) (o + fzEv m (fzAt i).e)

/-- Every `fz_i` of the entries `is` stays in bounds. -/
def pcOK (c : Word) : List Nat → Mem → Word → Bool
  | [], _, _ => true
  | i :: is, m, o => fzOK m c i (fzAt i) o && pcOK c is (fzStep m c i (fzAt i) o) (o + fzEv m (fzAt i).e)

/-- The call `o := fz_i(o, c)`. -/
def fzCall (i : Nat) : Stmt := .call [2] (fzName i) [.var 2, .var 1]

theorem fzCalls_eq : fzCalls = (List.range frozen.length).map fzCall := rfl

theorem St.setLoc_setLoc_same (s : St) (x : Var) (a b : Word) :
    (s.setLoc x a).setLoc x b = s.setLoc x b := by
  simp only [St.setLoc]; congr 1; funext y; split <;> rfl

@[simp] theorem St.setLoc_mem (s : St) (x : Var) (a : Word) : (s.setLoc x a).mem = s.mem := rfl

@[simp] theorem St.setLoc_loc_app (s : St) (x : Var) (a : Word) (y : Var) :
    (s.setLoc x a).loc y = if y = x then a else s.loc y := rfl

@[simp] theorem St.setLoc_loc_same (M : Mem) (s : St) (x : Var) (a b : Word) :
    ({ mem := M, loc := (s.setLoc x a).loc } : St).setLoc x b = ({ mem := M, loc := s.loc } : St).setLoc x b := by
  simp only [St.setLoc]; congr 1; funext y; by_cases h : y = x <;> simp [h]

/-- **The calls in sequence**: from a state with offset `o` in local `2` and the flag `c` in
local `1`, the calls of the entries `is` run as `pcGo`, or fail with `oob`. -/
theorem fzCalls_run {p : Prog} (n : Nat) (rest : Stmt) :
    ∀ (is : List Nat), (∀ i ∈ is, i < frozen.length ∧ p.lookup (fzName i) = some (fzF i)) →
    ∀ (s : St),
    (step p (exec p (n + 1)) ((is.map fzCall).foldr .seq rest)).run s =
      if pcOK (s.loc 1) is s.mem (s.loc 2) then
        (step p (exec p (n + 1)) rest).run
          ({ s with mem := (pcGo (s.loc 1) is s.mem (s.loc 2)).1 }.setLoc 2
            (pcGo (s.loc 1) is s.mem (s.loc 2)).2)
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
    by_cases h1 : fzOK s.mem (s.loc 1) i (fzAt i) (s.loc 2) = true
    · simp [h1, setLocs, St.setLocs, hrest, St.setLoc_mem, St.setLoc_loc_same]
      rfl
    · simp [h1]; rfl

/-! ## What the images and stores leave alone -/

theorem words_size_set64 (m : Mem) (a : ArrId) (i v : Word) :
    (m.set64 a i v).words.size = m.words.size := by simp [Mem.set64]

theorem words_size_copy64 (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) (n : Nat) :
    (m.copy64 d di s si n).words.size = m.words.size := by
  induction n generalizing m di si with
  | zero => rfl
  | succ n ih => simp only [Mem.copy64]; rw [ih, words_size_set64]

/-- What a memory step that writes only `OUT` keeps. -/
structure OutFrame (m m' : Mem) : Prop where
  arr : ∀ a, a ≠ OUT → m'.arr64 a = m.arr64 a
  size : ∀ a, (m'.arr64 a).size = (m.arr64 a).size
  words : m'.words.size = m.words.size
  bytes : m'.bytes = m.bytes
  glob : m'.glob = m.glob

theorem OutFrame.refl (m : Mem) : OutFrame m m := ⟨fun _ _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem OutFrame.trans {m₁ m₂ m₃ : Mem} (h₁ : OutFrame m₁ m₂) (h₂ : OutFrame m₂ m₃) :
    OutFrame m₁ m₃ :=
  ⟨fun a ha => (h₂.arr a ha).trans (h₁.arr a ha), fun a => (h₂.size a).trans (h₁.size a),
    h₂.words.trans h₁.words, h₂.bytes.trans h₁.bytes, h₂.glob.trans h₁.glob⟩

theorem OutFrame.set64 (m : Mem) (i v : Word) : OutFrame m (m.set64 OUT i v) :=
  ⟨fun _ ha => Mem.arr64_set64_ne _ _ _ _ _ ha, fun _ => size_set64 _ _ _ _ _,
    words_size_set64 _ _ _ _, rfl, rfl⟩

theorem OutFrame.copy64 (m : Mem) (di : Word) (s : ArrId) (si : Word) (n : Nat) :
    OutFrame m (m.copy64 OUT di s si n) :=
  ⟨fun _ ha => arr64_copy64_ne _ _ _ _ _ _ ha, fun _ => size_copy64 _ _ _ _ _ _ _,
    words_size_copy64 _ _ _ _ _ _, Mem.copy64_bytes _ _ _ _ _ _, Mem.copy64_glob _ _ _ _ _ _⟩

theorem OutFrame.fzStep (m : Mem) (c : Word) (i : Nat) (z : Fz) (o : Word) :
    OutFrame m (fzStep m c i z o) := by
  unfold L.Arena.fzStep
  refine OutFrame.trans ?_ (OutFrame.trans (OutFrame.set64 _ _ _) (OutFrame.set64 _ _ _))
  split
  · exact OutFrame.copy64 _ _ _ _ _
  · exact OutFrame.refl _

theorem OutFrame.pcGo (c : Word) : ∀ (is : List Nat) (m : Mem) (o : Word),
    OutFrame m (pcGo c is m o).1
  | [], m, _ => OutFrame.refl m
  | i :: is, m, o => (OutFrame.fzStep m c i (fzAt i) o).trans (OutFrame.pcGo c is _ _)

/-! ## `par_compact` -/

theorem getElem_set64_out (M : Mem) (a : ArrId) (ha : a ≠ OUT) (i v : Word) (k : Nat)
    (h : k < ((M.set64 OUT i v).arr64 a).size) :
    ((M.set64 OUT i v).arr64 a)[k]'h = (M.arr64 a)[k]'(by rwa [size_set64] at h) := by
  simp only [Mem.arr64_set64_ne _ _ _ _ _ ha]

theorem getElem_set64_out_ctl (M : Mem) (i v : Word) (k : Nat)
    (h : k < ((M.set64 OUT i v).arr64 CTL).size) :
    ((M.set64 OUT i v).arr64 CTL)[k]'h = (M.arr64 CTL)[k]'(by rwa [size_set64] at h) :=
  getElem_set64_out M CTL (by decide) i v k h

@[simp] theorem run_throw_M {α : Type} (e : Err) (s : St) :
    StateT.run (throw e : M α) s = Except.error e := rfl

@[simp] theorem except_bind_error {α β : Type} (e : Err) (f : α → Except Err β) :
    (Except.error e >>= f) = Except.error e := rfl

@[simp] theorem except_map_error {α β : Type} (e : Err) (f : α → β) :
    (f <$> (Except.error e : Except Err α)) = Except.error e := rfl

theorem dite_getElem_pure (A : Array Word) (i : Nat) (e : Err) :
    (if h : i < A.size then (pure A[i] : M Word) else throw e) =
      if i < A.size then pure (A.getD i 0) else throw e := by
  by_cases h : i < A.size <;> simp [h, Array.getD]

/-- The header's words `0`‥`4`, `8`, `9` (the tail of `par_compact`), after the images. -/
def pcTail (m : Mem) (vis o : Word) : Mem :=
  ((((((m.set64 OUT 0 fzMagic).set64 OUT 1 o).set64 OUT 2 (rd64 m CTL 130)).set64 OUT 3 vis).set64
    OUT 4 (UInt64.ofNat frozen.length)).set64 OUT 8 0).set64 OUT 9 (UInt64.ofNat hdrW)

/-- The images' memory and the buffer's length (the offset after the last image). -/
def pcImages (m : Mem) (c : Word) : Mem × Word :=
  pcGo c (List.range frozen.length) m (UInt64.ofNat hdrW)

/-- **The memory after `par_compact(vis, c)`**: the images (`c ≠ 0`) and the header entries in
header order from offset `hdrW`, then the header's words `0`‥`4`, `8`, `9`. -/
def parCompactMem (m : Mem) (vis c : Word) : Mem :=
  pcTail (pcImages m c).1 vis (pcImages m c).2

/-- `par_compact(vis, c)` stays in bounds: every `fz_i`, the header's words, `CTL[130]`. -/
def parCompactOK (m : Mem) (c : Word) : Bool :=
  pcOK c (List.range frozen.length) m (UInt64.ofNat hdrW) && decide (9 < (m.arr64 OUT).size) &&
    decide (130 < (m.arr64 CTL).size)

/-- `par_compact`'s tail: the header's words, then the length. -/
def pcTailS : Stmt :=
    .seq (.st64 OUT (fzC 0) (.const fzMagic)) <|
    .seq (.st64 OUT (fzC 1) (.var 2)) <|
    .seq (.st64 OUT (fzC 2) (fzCtl 130)) <|
    .seq (.st64 OUT (fzC 3) (.var 0)) <|
    .seq (.st64 OUT (fzC 4) (fzC frozen.length)) <|
    .seq (.st64 OUT (fzC 8) (fzC 0)) <|
    .seq (.st64 OUT (fzC 9) (fzC hdrW)) <|
    .ret [.var 2]

theorem parCompactL_eq : parCompactL =
    { nparams := 2, nlocals := 3, body := .seq (.set 2 (fzC hdrW)) (fzCalls.foldr .seq pcTailS) } := rfl

theorem fzCalls_lookup {p : Prog} (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i)) :
    ∀ i ∈ List.range frozen.length, i < frozen.length ∧ p.lookup (fzName i) = some (fzF i) :=
  fun i hi => ⟨List.mem_range.mp hi, hfz i (List.mem_range.mp hi)⟩

/-- **`par_compact`'s run**: from any state, with fuel `≥ 2`, `par_compact(vis, c)` returns the
buffer's length with the memory `parCompactMem` and the caller's locals, or fails with `oob`. -/
theorem parCompact_run {p : Prog} (hp : p.lookup "par_compact" = some parCompactL)
    (hfz : ∀ i < frozen.length, p.lookup (fzName i) = some (fzF i)) (n : Nat) (s : St) (vis c : Word) :
    (invoke p (exec p (n + 2)) "par_compact" [vis, c]).run s =
      if parCompactOK s.mem c then
        .ok ([(pcImages s.mem c).2], { s with mem := parCompactMem s.mem vis c })
      else .error .oob := by
  have hF := OutFrame.pcGo c (List.range frozen.length) s.mem (UInt64.ofNat hdrW)
  have hx : ∀ st, exec p (n + 2) st = step p (exec p (n + 1)) st := fun _ => rfl
  have hc := fzCalls_run (p := p) n pcTailS _ (fzCalls_lookup hfz)
  rw [← fzCalls_eq] at hc
  simp only [invoke, lookupFn, hp, callFn, hx, parCompactL_eq, step, StateT.run_bind, StateT.run_get,
    StateT.run_set, pure_bind, evalE, StateT.run_pure, setLoc, StateT.run_modify]
  simp only [fzC, evalE, StateT.run_pure, pure_bind, hc, St.setLoc_loc_app, Locals.init]
  simp only [parCompactOK, pcImages, Bool.and_eq_true]
  by_cases h1 : pcOK c (List.range frozen.length) s.mem (UInt64.ofNat hdrW) = true
  · simp only [h1, pcTailS, step, fzC, fzCtl, ite_true]
    by_cases h2 : 9 < (s.mem.arr64 OUT).size
    · have h0 : 0 < (s.mem.arr64 OUT).size := by omega
      have h1' : 1 < (s.mem.arr64 OUT).size := by omega
      have h2' : 2 < (s.mem.arr64 OUT).size := by omega
      have h3' : 3 < (s.mem.arr64 OUT).size := by omega
      have h4' : 4 < (s.mem.arr64 OUT).size := by omega
      have h8' : 8 < (s.mem.arr64 OUT).size := by omega
      by_cases h3 : 130 < (s.mem.arr64 CTL).size
      · simp [h1, h0, h1', h2', h3', h4', h8', h2, h3, getElem_set64_out_ctl, st64, evalE, ld64,
          StateT.run_bind, hF.size, parCompactMem, pcTail, pcImages, evalArgs, rd64,
          Mem.arr64_set64_ne, Locals.init, Sig.retVal, Sig.retOr]
        rfl
      · simp [h1, h0, h1', h2', h3', h4', h8', h2, h3, st64, evalE, ld64,
          StateT.run_bind, hF.size]
    · obtain h | h | h | h | h | h | h | h | h | h : (s.mem.arr64 OUT).size = 0 ∨
        (s.mem.arr64 OUT).size = 1 ∨ (s.mem.arr64 OUT).size = 2 ∨ (s.mem.arr64 OUT).size = 3 ∨
        (s.mem.arr64 OUT).size = 4 ∨ (s.mem.arr64 OUT).size = 5 ∨ (s.mem.arr64 OUT).size = 6 ∨
        (s.mem.arr64 OUT).size = 7 ∨ (s.mem.arr64 OUT).size = 8 ∨ (s.mem.arr64 OUT).size = 9 := by omega
      all_goals by_cases h3 : 130 < (s.mem.arr64 CTL).size <;> simp [h1, h, h2, h3, st64, evalE, ld64, StateT.run_bind, hF.size, dite_getElem_pure]
  · simp [h1]

end L.Arena
