import ConAgua.Front.Apply
import ConAgua.Front.ExprIface
import ConAgua.Arena.ExprMk
import ConAgua.Front.NatDec
import ConAgua.Front.Preserve

/-!
# Expression lines into the stores: `apply_expr`

con-ron's `parseExprEntryD` (`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:211`) interns one
expression record and binds its export id. Here the expression id table is the dense word array
`EID` (66, `Apply.lean`: entry `i` is the handle word `+ 1`, `0` unset), and

* `expr_get(i)`, `expr_fresh(i)`: `StateD.expr` / `StateD.freshExpr` (abort where the twin fails);
* `ls_put(v)`: the universe list whose `[` is at `v`, read again from the input (the traversal of
  `itemsN`), each item a level id looked up in `LID`, the handle words appended to the pool; returns
  the slice `(top, count)`;
* `node_bin(k, a, c)` (`app`/`lam`/`forallE`), `node_let`, `node_proj`, `node_const`, `node_lit`:
  one node from its fields (`ExprIface.lean`'s table), through the derived-range constructors
  `mk_*` (`ConAgua/Arena/ExprMk.lean`) for compound nodes, `intern_*` for leaves;
* `expr_node(pl, a, c, d)`: the dispatch on the kind `pl`; `strVal` (`17`) aborts (the `lit` store
  does not represent string contents yet), a `natVal` past 18 digits aborts;
* `apply_expr(pl, idx, a, c, d)`: `expr_fresh(idx)`, `expr_node`, the handle `< 2^32`,
  `EID[idx] := h + 1`.

Each spec is an equation about a named `Option` model, as in `Apply.lean`; the refinement is in
`ApplyExprRefine.lean`.
-/

set_option experimental.vcgen true
set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (numEndN)
open L.Front.Fields (rdNatN NONE itemsN itemsN_end itemsN_close itemsN_digit itemsN_noprog
  itemsN_other)

namespace L.Front

/-! ## `expr_get`, `expr_fresh` -/

def exprGet : FunDecl := lfn (i) locals (e) {
  if len(EID.u64) <= i { abort };
  e := EID.u64[i];
  if e == 0 { abort };
  return e - 1
}

def exprFresh : FunDecl := lfn (i) {
  if len(EID.u64) <= i { abort };
  if EID.u64[i] != 0 { abort };
  return 0
}

/-! ## `ls_put(v)` -/

def lsLoop : Stmt := lblk (v, i, top, cnt, c, e, x, h) {
  while 0 == 0 {
    if len(IN.u8) <= i { CTL.u64[0] := top + cnt; return (top, cnt) };
    c := IN.u8[i];
    if c == 93 { CTL.u64[0] := top + cnt; return (top, cnt) };
    if 48 <= c && c <= 57 {
      e := call num_end(i);
      if e <= i { CTL.u64[0] := top + cnt; return (top, cnt) };
      x := call read_nat(i, e);
      if x == 18446744073709551615 { abort };
      h := call level_get(x);
      if len(POOL.u64) <= top + cnt { abort };
      POOL.u64[top + cnt] := h;
      cnt += 1;
      i := e
    } else {
      i += 1
    }
  }
}

def lsPut : FunDecl := lfn (v) locals (i, top, cnt, c, e, x, h) {
  top := CTL.u64[0];
  if len(POOL.u64) < top { abort };
  i := v + 1;
  ⟪lsLoop⟫;
  return (0, 0)
}

/-- The number of items `ls_put` writes, from `i` with `cnt` written. -/
def lsCntN (b : Array UInt8) (i cnt : Word) : Word :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 93 then cnt
    else if 48 ≤ byteW b i ∧ byteW b i ≤ 57 then
      if hj : i < UInt64.ofNat (numEndN b i.toNat) then
        lsCntN b (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1)
      else cnt
    else lsCntN b (i + 1) cnt
  else cnt
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    first
      | (rw [UInt64.lt_iff_toNat_lt] at hj; omega)
      | (have := L.Scan.toNat_add_one_of_lt_ofNat h; omega)

/-- The memory after the copy loop of `ls_put`, from `i` with `cnt` written above `top`; `none`
where it aborts (an item past 18 digits, an unbound level id, a full pool). -/
def lsLoopM (b : Array UInt8) (m : Mem) (top i cnt : Word) : Option Mem :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 93 then some (m.set64 CTL 0 (top + cnt))
    else if 48 ≤ byteW b i ∧ byteW b i ≤ 57 then
      if hj : i < UInt64.ofNat (numEndN b i.toNat) then
        if rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) = NONE then none
        else if tblOK m LID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))) = true ∧
            top + cnt < m.len64 POOL then
          lsLoopM b (m.set64 POOL (top + cnt)
            (tblW m LID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))))) top
            (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1)
        else none
      else some (m.set64 CTL 0 (top + cnt))
    else lsLoopM b m top (i + 1) cnt
  else some (m.set64 CTL 0 (top + cnt))
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    first
      | (rw [UInt64.lt_iff_toNat_lt] at hj; omega)
      | (have := L.Scan.toNat_add_one_of_lt_ofNat h; omega)

section lsArms
variable (b : Array UInt8) (m : Mem) (top i cnt : Word)

theorem lsCntN_end (h : ¬ i < UInt64.ofNat b.size) : lsCntN b i cnt = cnt := by
  rw [lsCntN, dif_neg h]
theorem lsCntN_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) : lsCntN b i cnt = cnt := by
  rw [lsCntN, dif_pos h, if_pos hc]
theorem lsCntN_digit (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : i < UInt64.ofNat (numEndN b i.toNat)) :
    lsCntN b i cnt = lsCntN b (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1) := by
  rw [lsCntN, dif_pos h, if_neg hc, if_pos hd, dif_pos he]
theorem lsCntN_noprog (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : ¬ i < UInt64.ofNat (numEndN b i.toNat)) :
    lsCntN b i cnt = cnt := by
  rw [lsCntN, dif_pos h, if_neg hc, if_pos hd, dif_neg he]
theorem lsCntN_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) : lsCntN b i cnt = lsCntN b (i + 1) cnt := by
  rw [lsCntN, dif_pos h, if_neg hc, if_neg hd]

theorem lsLoopM_end (h : ¬ i < UInt64.ofNat b.size) :
    lsLoopM b m top i cnt = some (m.set64 CTL 0 (top + cnt)) := by
  rw [lsLoopM, dif_neg h]
theorem lsLoopM_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) :
    lsLoopM b m top i cnt = some (m.set64 CTL 0 (top + cnt)) := by
  rw [lsLoopM, dif_pos h, if_pos hc]
theorem lsLoopM_digit (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : i < UInt64.ofNat (numEndN b i.toNat)) :
    lsLoopM b m top i cnt =
      if rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) = NONE then none
      else if tblOK m LID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))) = true ∧
          top + cnt < m.len64 POOL then
        lsLoopM b (m.set64 POOL (top + cnt)
          (tblW m LID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))))) top
          (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1)
      else none := by
  rw [lsLoopM, dif_pos h, if_neg hc, if_pos hd, dif_pos he]
theorem lsLoopM_noprog (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : ¬ i < UInt64.ofNat (numEndN b i.toNat)) :
    lsLoopM b m top i cnt = some (m.set64 CTL 0 (top + cnt)) := by
  rw [lsLoopM, dif_pos h, if_neg hc, if_pos hd, dif_neg he]
theorem lsLoopM_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) : lsLoopM b m top i cnt = lsLoopM b m top (i + 1) cnt := by
  rw [lsLoopM, dif_pos h, if_neg hc, if_neg hd]
end lsArms

grind_pattern [lang_grind] lsCntN_end => lsCntN b i cnt
grind_pattern [lang_grind] lsCntN_close => lsCntN b i cnt, b[i.toNat]
grind_pattern [lang_grind] lsCntN_digit => lsCntN b i cnt, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] lsCntN_noprog => lsCntN b i cnt, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] lsCntN_other => lsCntN b i cnt, b[i.toNat]
grind_pattern [lang_grind] lsLoopM_end => lsLoopM b m top i cnt
grind_pattern [lang_grind] lsLoopM_close => lsLoopM b m top i cnt, b[i.toNat]
grind_pattern [lang_grind] lsLoopM_digit => lsLoopM b m top i cnt, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] lsLoopM_noprog => lsLoopM b m top i cnt, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] lsLoopM_other => lsLoopM b m top i cnt, b[i.toNat]

/-- The model of `ls_put(v)`: the memory after. -/
def lsPutW (b : Array UInt8) (m : Mem) (v : Word) : Option Mem :=
  if m.len64 POOL < m.top then none else lsLoopM b m m.top (v + 1) 0

/-- The length of the slice `ls_put(v)` returns. -/
def lsPutL (b : Array UInt8) (v : Word) : Word := lsCntN b (v + 1) 0

/-! ## What `ls_put` writes -/

theorem tblOK_congr {m m' : Mem} {b : ArrId} (h : m'.arr64 b = m.arr64 b) (i : Word) :
    tblOK m' b i = tblOK m b i := by unfold tblOK Mem.len64; rw [h]
theorem tblW_congr {m m' : Mem} {b : ArrId} (h : m'.arr64 b = m.arr64 b) (i : Word) :
    tblW m' b i = tblW m b i := by simp only [tblW, h]

/-- **The copy loop of `ls_put`**: it appends the handles of the items to the pool above
`top + cnt`, leaves the pool below alone, sets the top after them, and changes nothing else. -/
theorem lsLoopM_facts (b : Array UInt8) (top : Word) : ∀ (m : Mem) (i cnt : Word) (m' : Mem),
    lsLoopM b m top i cnt = some m' →
    top.toNat + cnt.toNat ≤ (m.arr64 POOL).size → (m.arr64 POOL).size < 2 ^ 63 →
    (lsCntN b i cnt).toNat = cnt.toNat + (itemsN b i).length ∧
    (m'.arr64 POOL).size = (m.arr64 POOL).size ∧
    top.toNat + (lsCntN b i cnt).toNat ≤ (m'.arr64 POOL).size ∧
    (∀ j, j < top.toNat + cnt.toNat → (m'.arr64 POOL)[j]? = (m.arr64 POOL)[j]?) ∧
    (∀ k (hk : k < (itemsN b i).length), (m'.arr64 POOL)[top.toNat + cnt.toNat + k]? =
        some (tblW m LID (itemsN b i)[k])) ∧
    (∀ x ∈ itemsN b i, tblOK m LID x = true) ∧
    (0 < (m.arr64 CTL).size → m'.top = top + lsCntN b i cnt ∧
      Frame POOL (m.set64 CTL 0 m'.top) m') := by
  intro m i cnt
  fun_induction lsLoopM b m top i cnt with
  | case1 m i cnt h1 h2 =>
    intro m' h hr hs
    cases h
    rw [lsCntN_close _ _ _ h1 h2, itemsN_close _ _ h1 h2]
    refine ⟨by simp, size_set64 _ _ _ _ _, by rw [size_set64]; omega, fun j _ => by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)], fun k hk => by simp at hk, by simp,
      fun hc => ⟨Mem.top_set64 _ _ hc, by rw [Mem.top_set64 _ _ hc]; exact Frame.refl _ _⟩⟩
  | case2 m i cnt h1 h2 h3 h4 h5 => intro m' h; cases h
  | case3 m i cnt h1 h2 h3 h4 h5 h6 ih =>
    intro m' h hr hs
    obtain ⟨hok, hlt⟩ := h6
    have hlen : (m.len64 POOL).toNat = (m.arr64 POOL).size := by
      simp only [Mem.len64]; exact toNat_ofNat_size _ hs
    have htc : (top + cnt).toNat = top.toNat + cnt.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    rw [hlen, htc] at hlt'
    have hc1 : (cnt + 1).toNat = cnt.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hP : ∀ B, B ≠ POOL →
        (m.set64 POOL (top + cnt) (tblW m LID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))))).arr64 B =
          m.arr64 B := fun B hB => Mem.arr64_set64_ne _ _ _ _ _ hB
    obtain ⟨i1, i3, i4, i5, i6, i7, i8⟩ := ih m' h
      (by rw [size_set64, hc1]; omega) (by rw [size_set64]; exact hs)
    rw [lsCntN_digit _ _ _ h1 h2 h3 h4, itemsN_digit _ _ h1 h2 h3 h4]
    rw [size_set64] at i3
    refine ⟨by rw [i1, hc1]; simp; omega, i3, i4, fun j hj => ?_, fun k hk => ?_, ?_, fun hc => ?_⟩
    · rw [i5 j (by rw [hc1]; omega), Mem.arr64_set64_same, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds, htc]
      simp [show top.toNat + cnt.toNat ≠ j by omega]
    · cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [i5 _ (by rw [hc1]; omega), Mem.arr64_set64_same, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds, htc]
        simp; omega
      | succ k =>
        simp only [List.getElem_cons_succ]
        have := i6 k (by simpa using hk)
        rw [hc1, tblW_congr (hP LID (by decide))] at this
        rw [← this]; congr 1; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hok
      · rw [← tblOK_congr (hP LID (by decide))]; exact i7 x hx
    · obtain ⟨i2, i8⟩ := i8 (by rw [hP CTL (by decide)]; exact hc)
      refine ⟨i2, Frame.trans _ _ _ _ ?_ i8⟩
      exact Frame.set64_both _ _ _ _ _ _ (Frame.set64 _ _ _ _ _ (Frame.refl _ _)) (by decide)
  | case4 m i cnt h1 h2 h3 h4 h5 h6 => intro m' h; cases h
  | case5 m i cnt h1 h2 h3 h4 =>
    intro m' h hr hs
    cases h
    rw [lsCntN_noprog _ _ _ h1 h2 h3 h4, itemsN_noprog _ _ h1 h2 h3 h4]
    refine ⟨by simp, size_set64 _ _ _ _ _, by rw [size_set64]; omega, fun j _ => by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)], fun k hk => by simp at hk, by simp,
      fun hc => ⟨Mem.top_set64 _ _ hc, by rw [Mem.top_set64 _ _ hc]; exact Frame.refl _ _⟩⟩
  | case6 m i cnt h1 h2 h3 ih =>
    intro m' h hr hs
    rw [lsCntN_other _ _ _ h1 h2 h3, itemsN_other _ _ h1 h2 h3]
    exact ih m' h hr hs
  | case7 m i cnt h1 =>
    intro m' h hr hs
    cases h
    rw [lsCntN_end _ _ _ h1, itemsN_end _ _ h1]
    refine ⟨by simp, size_set64 _ _ _ _ _, by rw [size_set64]; omega, fun j _ => by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)], fun k hk => by simp at hk, by simp,
      fun hc => ⟨Mem.top_set64 _ _ hc, by rw [Mem.top_set64 _ _ hc]; exact Frame.refl _ _⟩⟩

/-- `ls_put`'s slice fits in the pool after it (what `intern_ls` needs). -/
theorem lsPut_room (b : Array UInt8) (m m' : Mem) (v : Word) (h : lsPutW b m v = some m')
    (hs : (m.arr64 POOL).size < 2 ^ 63) :
    (m'.arr64 POOL).size < 2 ^ 64 ∧ m.top.toNat + (lsPutL b v).toNat ≤ (m'.arr64 POOL).size := by
  unfold lsPutW at h
  split at h
  · cases h
  rename_i ht
  have hlen : (m.len64 POOL).toNat = (m.arr64 POOL).size := by
    simp only [Mem.len64]; exact toNat_ofNat_size _ hs
  have ht' : m.top.toNat ≤ (m.arr64 POOL).size := by
    have := UInt64.not_lt.mp ht; rw [UInt64.le_iff_toNat_le, hlen] at this; exact this
  obtain ⟨-, h3, h4, -⟩ := lsLoopM_facts b m.top m _ 0 m' h (by simpa using ht') hs
  exact ⟨by omega, h4⟩

/-! ## The nodes -/

def nodeBin : FunDecl := lfn (k, a, c) locals (f, x, h) {
  f := call expr_get(a);
  x := call expr_get(c);
  if k == 10 {
    h := call mk_app(f, x)
  } else if k == 11 {
    h := call mk_lam(f, x)
  } else {
    h := call mk_forall(f, x)
  };
  return h
}

/-- The model of `node_bin(k, a, c)`. -/
def binW (m : Mem) (k a c : Word) : Option (Word × Mem) :=
  if tblOK m EID a = true ∧ tblOK m EID c = true then
    if k = 10 then mkAppW m (tblW m EID a) (tblW m EID c)
    else if k = 11 then mkLamW m (tblW m EID a) (tblW m EID c)
    else mkForallW m (tblW m EID a) (tblW m EID c)
  else none

def nodeLet : FunDecl := lfn (a, c, d) locals (t, v, x, h) {
  t := call expr_get(a);
  v := call expr_get(c);
  x := call expr_get(d);
  h := call mk_let(t, v, x);
  return h
}

/-- The model of `node_let(a, c, d)`. -/
def letW (m : Mem) (a c d : Word) : Option (Word × Mem) :=
  if tblOK m EID a = true ∧ tblOK m EID c = true ∧ tblOK m EID d = true then
    mkLetW m (tblW m EID a) (tblW m EID c) (tblW m EID d)
  else none

def nodeProj : FunDecl := lfn (a, c, d) locals (n, e, h) {
  if c == 18446744073709551615 { abort };
  n := call name_get(a);
  e := call expr_get(d);
  h := call mk_proj(n, c, e);
  return h
}

/-- The model of `node_proj(a, c, d)`. -/
def projW (m : Mem) (a c d : Word) : Option (Word × Mem) :=
  if c ≠ NONE ∧ tblOK m NID a = true ∧ tblOK m EID d = true then
    mkProjW m (tblW m NID a) c (tblW m EID d)
  else none

def nodeConst : FunDecl := lfn (a, c) locals (n, o, l, g, h) {
  n := call name_get(a);
  (o, l) := call ls_put(c);
  g := call intern_ls(o, l);
  if g >= 4294967296 { abort };
  h := call intern_const(n, g);
  return h
}

/-- The tail of `node_const` after `intern_ls`. -/
def constK2 (n : Word) : Option (Word × Mem) → Option (Word × Mem)
  | some (g, m₂) => if g < 0x100000000 then ceinternW m₂ n g else none
  | none => none

/-- The tail of `node_const` after `ls_put`. -/
def constK (n o l : Word) : Option Mem → Option (Word × Mem)
  | some m₁ => constK2 n (lsinternW m₁ o l)
  | none => none

@[arena_grind =] theorem constK2_none (n : Word) : constK2 n none = none := rfl
@[arena_grind =] theorem constK2_some (n g : Word) (m₂ : Mem) :
    constK2 n (some (g, m₂)) = if g < 0x100000000 then ceinternW m₂ n g else none := rfl
@[arena_grind =] theorem constK_none (n o l : Word) : constK n o l none = none := rfl
@[arena_grind =] theorem constK_some (n o l : Word) (m₁ : Mem) :
    constK n o l (some m₁) = constK2 n (lsinternW m₁ o l) := rfl

/-- The model of `node_const(a, c)`. -/
def constW (b : Array UInt8) (m : Mem) (a c : Word) : Option (Word × Mem) :=
  if tblOK m NID a = true then constK (tblW m NID a) m.top (lsPutL b c) (lsPutW b m c) else none

def nodeLit : FunDecl := lfn (c, d) locals (o, l, h) {
  (o, l) := call nat_dec(c, d);
  if len(POOL.u64) < o { abort };
  if len(POOL.u64) - o < l { abort };
  h := call intern_lit(o, l);
  return h
}

/-- After `nat_dec`: its result `(o, l)` and memory (`none`: it aborted), then `intern_lit(o, l)`. -/
def litK : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    if m₁.len64 POOL < r.headD 0 then none
    else if m₁.len64 POOL - r.headD 0 < r.tail.headD 0 then none
    else internW m₁ (r.headD 0) (r.tail.headD 0)

@[arena_grind =] theorem litK_none : litK none = none := rfl
@[arena_grind =] theorem litK_some (r : List Word) (m₁ : Mem) : litK (some (r, m₁)) =
    if m₁.len64 POOL < r.headD 0 then none
    else if m₁.len64 POOL - r.headD 0 < r.tail.headD 0 then none
    else internW m₁ (r.headD 0) (r.tail.headD 0) := rfl

/-- The model of `node_lit(c, d)`: the decimal digits `[c, d)` into the pool, interned. -/
def litW (b : Array UInt8) (m : Mem) (c d : Word) : Option (Word × Mem) := litK (natDecW b m c d)

/-! ## `expr_node`, `apply_expr` -/

def exprNode : FunDecl := lfn (pl, a, c, d) locals (u, h) {
  if pl == 8 {
    if a == 18446744073709551615 { abort };
    h := call intern_bvar(a);
    return h
  };
  if pl == 9 {
    u := call level_get(a);
    h := call intern_sort(u);
    return h
  };
  if pl == 10 || pl == 11 || pl == 12 {
    h := call node_bin(pl, a, c);
    return h
  };
  if pl == 13 { h := call node_let(a, c, d); return h };
  if pl == 14 { h := call node_proj(a, c, d); return h };
  if pl == 15 { h := call node_const(a, c); return h };
  if pl == 16 { h := call node_lit(c, d); return h };
  abort
}

/-- The model of `expr_node(pl, a, c, d)`: the node's handle and the memory after. -/
def nodeW (b : Array UInt8) (m : Mem) (pl a c d : Word) : Option (Word × Mem) :=
  if pl = 8 then (if a = NONE then none else binternW m a)
  else if pl = 9 then (if tblOK m LID a = true then sointernW m (tblW m LID a) else none)
  else if pl = 10 ∨ pl = 11 ∨ pl = 12 then binW m pl a c
  else if pl = 13 then letW m a c d
  else if pl = 14 then projW m a c d
  else if pl = 15 then constW b m a c
  else if pl = 16 then litW b m c d
  else none

def applyExpr : FunDecl := lfn (pl, idx, a, c, d) locals (z, h) {
  z := call expr_fresh(idx);
  h := call expr_node(pl, a, c, d);
  if h >= 4294967296 { abort };
  EID.u64[idx] := h + 1;
  return 0
}

/-- **The model of `apply_expr(pl, idx, a, c, d)`.** -/
def applyExprW (b : Array UInt8) (m : Mem) (pl idx a c d : Word) : Option Mem :=
  if tblFresh m EID idx = true then putK EID idx (nodeW b m pl a c d) else none

/-! ## The program -/

/-- The expression functions with everything they call, on top of `frontProg`. -/
def exprProg : Prog := frontProg ++
  [("skip_digits", L.Scan.Leaves.skipDigits), ("num_end", L.Scan.Leaves.numEnd),
   ("read_nat", L.Front.Fields.readNat), ("der_b", derB),
   ("app_find", appFind), ("app_push", appPush), ("intern_app", internApp), ("mk_app", mkApp),
   ("lam_find", lamFind), ("lam_push", lamPush), ("intern_lam", internLamL), ("mk_lam", mkLam),
   ("forall_find", forallFind), ("forall_push", forallPush), ("intern_forall", internForallL),
   ("mk_forall", mkForall),
   ("letE_find", letFind), ("letE_push", letPush), ("intern_letE", internLet), ("mk_let", mkLet),
   ("proj_find", projFind), ("proj_push", projPush), ("intern_proj", internProj),
   ("mk_proj", mkProj),
   ("bvar_find", bvarFind), ("bvar_push", bvarPush), ("intern_bvar", internBVar),
   ("sort_find", sortFind), ("sort_push", sortPush), ("intern_sort", internSort),
   ("const_find", constFind), ("const_push", constPush), ("intern_const", internConst),
   ("ls_match", lsMatch), ("ls_find", lsFind), ("ls_push", lsPush), ("intern_ls", internLs),
   ("lit_match", litMatch), ("lit_find", litFind), ("lit_push", litPush), ("intern_lit", internLit),
   ("expr_get", exprGet), ("expr_fresh", exprFresh), ("ls_put", lsPut), ("node_bin", nodeBin),
   ("node_let", nodeLet), ("node_proj", nodeProj), ("node_const", nodeConst),
   ("node_lit", nodeLit), ("expr_node", exprNode), ("apply_expr", applyExpr),
   ("dec_chunk", decChunk), ("nat_mad", natMad), ("nat_dec", natDec)]

/-- Every word array 64 words (all zero), the input `[0, 1]`. -/
def exprMem : Mem :=
  { bytes := #["[0, 1]5".toUTF8.data], words := Array.replicate 67 (Array.replicate 64 0) }

/-- Run the calls in turn; the results. -/
def exprRuns (m : Mem) : List (FnName × List Word) → Option (List (List Word))
  | [] => some []
  | (f, vs) :: xs => match run exprProg 400 f vs m with
    | .ok (r, m') => (exprRuns m' xs).map (r :: ·)
    | .error _ => none

/- Level 1 = `succ zero`; expressions `sort 0` (0), `bvar 0` (1), `app 1 0` (2), `lam 0 1` (3),
`forallE 0 1` (4), `letE 0 2 1` (5), `proj 0 7 1` (6), `const 0 [0, 1]` (7), `natVal 5` (8),
`natVal 0` (9), `app 1 0` again (10, the same node as 2); then the handles of 0‥10. -/
#guard exprRuns exprMem
  [("front_init", []), ("apply_level", [1, 1, 0, 0]),
   ("apply_expr", [9, 0, 0, 0, 0]), ("apply_expr", [8, 1, 0, 0, 0]),
   ("apply_expr", [10, 2, 1, 0, 0]), ("apply_expr", [11, 3, 0, 1, 0]),
   ("apply_expr", [12, 4, 0, 1, 0]), ("apply_expr", [13, 5, 0, 2, 1]),
   ("apply_expr", [14, 6, 0, 7, 1]), ("apply_expr", [15, 7, 0, 0, 0]),
   ("apply_expr", [16, 8, 0, 6, 7]), ("apply_expr", [16, 9, 0, 1, 2]),
   ("apply_expr", [10, 10, 1, 0, 0]),
   ("expr_get", [0]), ("expr_get", [1]), ("expr_get", [2]), ("expr_get", [3]),
   ("expr_get", [4]), ("expr_get", [5]), ("expr_get", [6]), ("expr_get", [7]),
   ("expr_get", [8]), ("expr_get", [9]), ("expr_get", [10])] ==
  some [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0],
    [0x20000000], [0], [0x40000000], [0x50000000], [0x60000000], [0x70000000], [0x90000000],
    [0x30000000], [0x80000000], [0x80000001], [0x40000000]]

/- A rebound id aborts; an unbound child aborts; a `strVal` aborts. -/
#guard (exprRuns exprMem [("front_init", []), ("apply_expr", [8, 0, 0, 0, 0]),
  ("apply_expr", [8, 0, 1, 0, 0])]).isNone
#guard (exprRuns exprMem [("front_init", []), ("apply_expr", [10, 0, 1, 2, 0])]).isNone
#guard (exprRuns exprMem [("front_init", []), ("apply_expr", [17, 0, 0, 0, 0])]).isNone

/-! ## The specs -/

/-- Every function the expression functions call, at its name in `p`. -/
structure ExprLookups (p : Prog) : Prop where
  front : FrontLookups p
  skip_digits : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits
  num_end : p.lookup "num_end" = some L.Scan.Leaves.numEnd
  read_nat : p.lookup "read_nat" = some L.Front.Fields.readNat
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
  bvar_find : p.lookup "bvar_find" = some bvarFind
  bvar_push : p.lookup "bvar_push" = some bvarPush
  intern_bvar : p.lookup "intern_bvar" = some internBVar
  sort_find : p.lookup "sort_find" = some sortFind
  sort_push : p.lookup "sort_push" = some sortPush
  intern_sort : p.lookup "intern_sort" = some internSort
  const_find : p.lookup "const_find" = some constFind
  const_push : p.lookup "const_push" = some constPush
  intern_const : p.lookup "intern_const" = some internConst
  ls_match : p.lookup "ls_match" = some lsMatch
  ls_find : p.lookup "ls_find" = some lsFind
  ls_push : p.lookup "ls_push" = some lsPush
  intern_ls : p.lookup "intern_ls" = some internLs
  lit_match : p.lookup "lit_match" = some litMatch
  lit_find : p.lookup "lit_find" = some litFind
  lit_push : p.lookup "lit_push" = some litPush
  intern_lit : p.lookup "intern_lit" = some internLit
  expr_get : p.lookup "expr_get" = some exprGet
  expr_fresh : p.lookup "expr_fresh" = some exprFresh
  ls_put : p.lookup "ls_put" = some lsPut
  node_bin : p.lookup "node_bin" = some nodeBin
  node_let : p.lookup "node_let" = some nodeLet
  node_proj : p.lookup "node_proj" = some nodeProj
  node_const : p.lookup "node_const" = some nodeConst
  node_lit : p.lookup "node_lit" = some nodeLit
  expr_node : p.lookup "expr_node" = some exprNode
  apply_expr : p.lookup "apply_expr" = some applyExpr
  dec_chunk : p.lookup "dec_chunk" = some decChunk
  nat_mad : p.lookup "nat_mad" = some natMad
  nat_dec : p.lookup "nat_dec" = some natDec
  no_st8 : p.noSt8 = true

theorem exprProg_lookups : ExprLookups exprProg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> rfl
  all_goals rfl

section specs
variable (p : Prog) (hE : ExprLookups p)
include hE

theorem exprGet_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "expr_get" [i]
    ⦃fun r s' => s' = s₀ ∧ tblOK s₀.mem EID i = true ∧ r = [tblW s₀.mem EID i]; ⊤⦄ := by
  rw [invoke_eq _ hE.expr_get]
  simp only [callFn, exprGet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;> finish [tblOK, tblW]

theorem exprFresh_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "expr_fresh" [i]
    ⦃fun _ s' => s' = s₀ ∧ tblFresh s₀.mem EID i = true; ⊤⦄ := by
  rw [invoke_eq _ hE.expr_fresh]
  simp only [callFn, exprFresh]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;> finish [tblFresh]

theorem lsLoop_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n lsLoop
    ⦃fun r s' => r ≠ .brk ∧ r.retOr [0, 0] = [s₀.loc 2, lsCntN b (s₀.loc 1) (s₀.loc 3)] ∧
      lsLoopM b s₀.mem (s₀.loc 2) (s₀.loc 1) (s₀.loc 3) = some s'.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lsLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ld64, st64, ih,
        L.Scan.Leaves.numEnd_spec p hE.skip_digits hE.num_end b hb64 n,
        L.Front.Fields.readNat_spec p b hb hE.read_nat n,
        levelGet_spec p hE.front n] <;> finish [NONE]

theorem lsLoop_step_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) lsLoop
    ⦃fun r s' => r ≠ .brk ∧ r.retOr [0, 0] = [s₀.loc 2, lsCntN b (s₀.loc 1) (s₀.loc 3)] ∧
      lsLoopM b s₀.mem (s₀.loc 2) (s₀.loc 1) (s₀.loc 3) = some s'.mem; ⊤⦄ :=
  Triple.step_exec (lsLoop_spec p hE b hb (n + 1) s₀)

theorem lsPut_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_put" [v]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [s₀.mem.top, lsPutL b v] ∧ lsPutW b s₀.mem v = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hE.ls_put]
  simp only [callFn, lsPut]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lsLoop_step_spec p hE b hb n] <;> finish [lsPutW, lsPutL, top_rdW]

theorem nodeBin_spec (n : Nat) (s₀ : St) (k a c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "node_bin" [k, a, c]
    ⦃fun r s' => LocEq s' s₀ ∧ binW s₀.mem k a c = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hE.node_bin]
  simp only [callFn, nodeBin]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, exprGet_spec p hE n,
        mkApp_spec p hE.der_b hE.app_find hE.app_push hE.intern_app hE.mk_app n,
        mkLam_spec p hE.der_b hE.lam_find hE.lam_push hE.intern_lam hE.mk_lam n,
        mkForall_spec p hE.der_b hE.forall_find hE.forall_push hE.intern_forall hE.mk_forall n] <;>
      finish [binW]

theorem nodeLet_spec (n : Nat) (s₀ : St) (a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "node_let" [a, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ letW s₀.mem a c d = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hE.node_let]
  simp only [callFn, nodeLet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, exprGet_spec p hE n,
        mkLet_spec p hE.der_b hE.letE_find hE.letE_push hE.intern_letE hE.mk_let n] <;>
      finish [letW]

theorem nodeProj_spec (n : Nat) (s₀ : St) (a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "node_proj" [a, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ projW s₀.mem a c d = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hE.node_proj]
  simp only [callFn, nodeProj]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, exprGet_spec p hE n,
        nameGet_spec p hE.front n,
        mkProj_spec p hE.der_b hE.proj_find hE.proj_push hE.intern_proj hE.mk_proj n] <;>
      finish [projW, NONE]

theorem nodeLit_spec (b : Array UInt8) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hps : (s₀.mem.arr64 POOL).size < 2 ^ 63) (c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "node_lit" [c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ litW b s₀.mem c d = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hE.node_lit]
  simp only [callFn, nodeLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hdec : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ c d : Word,
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "nat_dec" [c, d]
        ⦃fun r s' => (LocEq s' s₁ ∧ natDecW b s₁.mem c d = some (r, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ := fun s₁ hm₁ c d =>
      Triple.keep hE.no_st8 (natDec_specW p b hE.dec_chunk hE.nat_mad hE.nat_dec n s₁ hm₁ c d)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hdec,
        internLit_spec p hE.front.lit_hash hE.front.limbs_eq hE.lit_match hE.lit_find hE.lit_push
          hE.intern_lit n] <;>
      finish [litW, Keep.size]

theorem nodeConst_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (hps : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "node_const" [a, c]
    ⦃fun r s' => LocEq s' s₀ ∧ constW b s₀.mem a c = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hE.node_const]
  simp only [callFn, nodeConst]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hroom := fun m' h => lsPut_room b s₀.mem m' c h hps
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, nameGet_spec p hE.front n,
        lsPut_spec p hE b hb n,
        internLs_spec p hE.front.lit_hash hE.front.limbs_eq hE.ls_match hE.ls_find hE.ls_push
          hE.intern_ls n,
        internConst_spec p hE.const_find hE.const_push hE.intern_const n] <;>
      finish [constW]

theorem exprNode_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (hps : (s₀.mem.arr64 POOL).size < 2 ^ 63) (pl a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "expr_node" [pl, a, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ nodeW b s₀.mem pl a c d = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hE.expr_node]
  simp only [callFn, exprNode]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, levelGet_spec p hE.front n,
        internBVar_spec p hE.bvar_find hE.bvar_push hE.intern_bvar n,
        internSort_spec p hE.sort_find hE.sort_push hE.intern_sort n,
        nodeBin_spec p hE n, nodeLet_spec p hE n, nodeProj_spec p hE n,
        nodeConst_spec p hE b hb n, nodeLit_spec p hE b n] <;>
      finish [nodeW, NONE]

theorem applyExpr_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (hps : (s₀.mem.arr64 POOL).size < 2 ^ 63) (pl idx a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_expr" [pl, idx, a, c, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ applyExprW b s₀.mem pl idx a c d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hE.apply_expr]
  simp only [callFn, applyExpr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64,
        exprFresh_spec p hE n, exprNode_spec p hE b hb n] <;>
      finish [applyExprW]

end specs

end L.Front
