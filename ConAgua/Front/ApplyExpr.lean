import ConAgua.Front.Apply
import ConAgua.Front.ExprIface
import ConAgua.Arena.ExprMk
import ConAgua.Front.NatDec
import ConAgua.Front.Preserve
import ConAgua.Front.Unescape
import ConAgua.Arena.BVarStore
import ConAgua.Arena.ConstStore
import ConAgua.Arena.LsStore
import ConAgua.Arena.SortStore
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# Expression lines into the stores: `apply_expr`

con-ron's `parseExprEntryD` (`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:211`) interns one
expression record and binds its export id. Here the expression id table is `IdTable.lean`'s table
`EID` (66, its sparse overflow array 74), and

* `expr_get(i)`, `expr_fresh(i)`, `expr_put(i, h)`: `StateD.expr` / `StateD.freshExpr` (abort where
  the twin fails) / `IdTable.insert`;
* `ls_put(v)`: the universe list whose `[` is at `v`, read again from the input (the traversal of
  `itemsN`), each item a level id looked up in `LID`, the handle words appended to the pool; returns
  the slice `(top, count)`;
* `node_bin(k, a, c)` (`app`/`lam`/`forallE`), `node_let`, `node_proj`, `node_const`, `node_lit`:
  one node from its fields (`ExprIface.lean`'s table), through the derived-range constructors
  `mk_*` (`ConAgua/Arena/ExprMk.lean`) for compound nodes, `intern_*` for leaves;
* `expr_node(pl, a, c, d)`: the dispatch on the kind `pl` (`natVal` through `nat_dec`, `strVal`
  through `str_put_esc`);
* `apply_expr(pl, idx, a, c, d)`: `expr_fresh(idx)`, `expr_node`, the handle `< 2^32`,
  `expr_put(idx, h)`.

Each spec is an equation about a named `Option` model, as in `Apply.lean`; the refinement is in
`ApplyExprRefine.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (numEndN)
open L.Front.Fields (rdNatN NONE itemsN itemsN_end itemsN_close itemsN_digit itemsN_noprog
  itemsN_other)
open L.Front.Unescape (strPutEsc strPutEscW strPutEsc_specW)

namespace L.Front

/-! ## `expr_get`, `expr_fresh`, `expr_put` -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:127-132 ConRon.Arena.Frontend.StateD.expr
con-leche: ConLeche/Frontend/Scan/Types.lean:334-336 ConLeche.Frontend.IdTable.get? -/
def exprGet : FunDecl := tblGetG EID "esp_find"

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:159-162 ConRon.Arena.Frontend.StateD.freshExpr
con-leche: ConLeche/Frontend/Scan/Types.lean:351-360 ConLeche.Frontend.IdTable.bound -/
def exprFresh : FunDecl := tblFreshG EID "esp_find"

/-- con-leche: ConLeche/Frontend/Scan/Types.lean:338-345 ConLeche.Frontend.IdTable.insert -/
def exprPut : FunDecl := tblPutG EID "esp_find" "esp_put"

/-! ## `ls_put(v)` -/

def lsLoop : Stmt := lblk (v, i, top, cnt, c, e, x, h, pt, pb) {
  while 0 == 0 {
    if len(IN.u8) <= i { CTL.u64[0] := top + cnt; return (top, cnt) };
    c := IN.u8[i];
    if c == 93 { CTL.u64[0] := top + cnt; return (top, cnt) };
    if 48 <= c && c <= 57 {
      e := call num_end(i);
      if e <= i { CTL.u64[0] := top + cnt; return (top, cnt) };
      x := call read_nat(i, e);
      if x == 18446744073709551615 { abort R_LONG_NUMBER };
      h := call level_get(x);
      if len(POOL⟨pt⟩) <= pb + cnt { abort };
      POOL⟨pt⟩[pb + cnt] := h;
      cnt += 1;
      i := e
    } else {
      i += 1
    }
  }
}

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
def lsPut : FunDecl := lfn (v) locals (i, top, cnt, c, e, x, h, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) < pb { abort };
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
            (top &&& (1099511627775 : Word)) + cnt < m.len64 (tierA POOL (top >>> 40)) then
          lsLoopM b (m.set64 (tierA POOL (top >>> 40)) ((top &&& 1099511627775) + cnt)
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
  rw [lsCntN, dite_eq_right h]
theorem lsCntN_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) : lsCntN b i cnt = cnt := by
  rw [lsCntN, dite_eq_left h, ite_eq_left hc]
theorem lsCntN_digit (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : i < UInt64.ofNat (numEndN b i.toNat)) :
    lsCntN b i cnt = lsCntN b (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1) := by
  rw [lsCntN, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_left he]
theorem lsCntN_noprog (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : ¬ i < UInt64.ofNat (numEndN b i.toNat)) :
    lsCntN b i cnt = cnt := by
  rw [lsCntN, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_right he]
theorem lsCntN_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) : lsCntN b i cnt = lsCntN b (i + 1) cnt := by
  rw [lsCntN, dite_eq_left h, ite_eq_right hc, ite_eq_right hd]

theorem lsLoopM_end (h : ¬ i < UInt64.ofNat b.size) :
    lsLoopM b m top i cnt = some (m.set64 CTL 0 (top + cnt)) := by
  rw [lsLoopM, dite_eq_right h]
theorem lsLoopM_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) :
    lsLoopM b m top i cnt = some (m.set64 CTL 0 (top + cnt)) := by
  rw [lsLoopM, dite_eq_left h, ite_eq_left hc]
theorem lsLoopM_digit (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : i < UInt64.ofNat (numEndN b i.toNat)) :
    lsLoopM b m top i cnt =
      if rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) = NONE then none
      else if tblOK m LID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))) = true ∧
          (top &&& (1099511627775 : Word)) + cnt < m.len64 (tierA POOL (top >>> 40)) then
        lsLoopM b (m.set64 (tierA POOL (top >>> 40)) ((top &&& 1099511627775) + cnt)
          (tblW m LID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))))) top
          (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1)
      else none := by
  rw [lsLoopM, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_left he]
theorem lsLoopM_noprog (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : ¬ i < UInt64.ofNat (numEndN b i.toNat)) :
    lsLoopM b m top i cnt = some (m.set64 CTL 0 (top + cnt)) := by
  rw [lsLoopM, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_right he]
theorem lsLoopM_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) : lsLoopM b m top i cnt = lsLoopM b m top (i + 1) cnt := by
  rw [lsLoopM, dite_eq_left h, ite_eq_right hc, ite_eq_right hd]
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
  if m.len64 (tierA POOL (m.top >>> 40)) < (m.top &&& 1099511627775) then none
  else lsLoopM b m m.top (v + 1) 0

/-- The length of the slice `ls_put(v)` returns. -/
def lsPutL (b : Array UInt8) (v : Word) : Word := lsCntN b (v + 1) 0

/-! ## What `ls_put` writes -/

/-- **The copy loop of `ls_put`**: it appends the handles of the items to the pool above
`top + cnt` (in the top's tier, inside its array), leaves the pool below alone, sets the top after
them, and changes nothing else. -/
theorem lsLoopM_facts (b : Array UInt8) (top : Word) (ht : top.toNat < 2 ^ 41) :
    ∀ (m : Mem) (i cnt : Word) (m' : Mem),
    lsLoopM b m top i cnt = some m' →
    (top &&& 1099511627775).toNat + cnt.toNat ≤ (m.arr64 (tierA POOL (top >>> 40))).size →
    (m.arr64 (tierA POOL (top >>> 40))).size < 2 ^ 40 →
    (lsCntN b i cnt).toNat = cnt.toNat + (itemsN b i).length ∧ pcap m' = pcap m ∧
    (top &&& 1099511627775).toNat + (lsCntN b i cnt).toNat ≤ (m.arr64 (tierA POOL (top >>> 40))).size ∧
    (∀ j, j < top.toNat + cnt.toNat → (vpool m')[j]? = (vpool m)[j]?) ∧
    (∀ k (hk : k < (itemsN b i).length), (vpool m')[top.toNat + cnt.toNat + k]? =
        some (tblW m LID (itemsN b i)[k])) ∧
    (∀ x ∈ itemsN b i, tblOK m LID x = true) ∧
    (0 < (m.arr64 CTL).size → m'.top = top + lsCntN b i cnt ∧
      PFrame (m.set64 CTL 0 m'.top) m') := by
  have hI := tag_idx_lt top
  have hsp := tag_split top
  have htr := tag_tier_le top ht
  intro m i cnt
  fun_induction lsLoopM b m top i cnt with
  | case1 m i cnt h1 h2 =>
    intro m' h hr hs
    cases h
    rw [lsCntN_close _ _ _ h1 h2, itemsN_close _ _ h1 h2]
    refine ⟨by simp, pcap_set64 _ _ _ _, hr, fun j _ => by
      rw [vpool_set64_ne _ _ _ _ (by decide)], fun k hk => by simp at hk, by simp,
      fun hc => ⟨Mem.top_set64 _ _ hc, by rw [Mem.top_set64 _ _ hc]; exact PFrame.refl _⟩⟩
  | case2 m i cnt h1 h2 h3 h4 h5 => intro m' h; cases h
  | case3 m i cnt h1 h2 h3 h4 h5 h6 ih =>
    intro m' h hr hs
    obtain ⟨hok, hlt⟩ := h6
    have hlen : (m.len64 (tierA POOL (top >>> 40))).toNat = (m.arr64 (tierA POOL (top >>> 40))).size := by
      simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    have hIc : ((top &&& 1099511627775) + cnt).toNat = (top &&& 1099511627775).toNat + cnt.toNat := by
      rw [UInt64.toNat_add]; omega
    have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
    rw [hlen, hIc] at hlt'
    have htc : (top + cnt).toNat = top.toNat + cnt.toNat := by
      rw [UInt64.toNat_add]; omega
    have hc1 : (cnt + 1).toNat = cnt.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hP : ∀ B, B ≠ POOL ∧ B ≠ POOL1 →
        (m.set64 (tierA POOL (top >>> 40)) ((top &&& 1099511627775) + cnt)
          (tblW m LID (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))))).arr64 B =
          m.arr64 B := fun B hB => arr64_set64_tier_ne _ _ _ _ _ hB
    have hst : ∀ v, vpool (m.set64 (tierA POOL (top >>> 40)) ((top &&& 1099511627775) + cnt) v) =
        (vpool m).set! (top.toNat + cnt.toNat) v := fun v => by
      rw [vpool_stidx m top cnt v ht (by rw [hIc]; exact hlt') (by omega) (by omega), htc]
    obtain ⟨i1, i3, i4, i5, i6, i7, i8⟩ := ih m' h
      (by rw [Mem.size_arr64_set64, hc1]; omega) (by rw [Mem.size_arr64_set64]; exact hs)
    rw [lsCntN_digit _ _ _ h1 h2 h3 h4, itemsN_digit _ _ h1 h2 h3 h4]
    rw [Mem.size_arr64_set64] at i4
    rw [pcap_set64] at i3
    refine ⟨by rw [i1, hc1]; simp; omega, i3, i4, fun j hj => ?_, fun k hk => ?_, ?_, fun hc => ?_⟩
    · rw [i5 j (by rw [hc1]; omega), hst, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds]
      simp [show top.toNat + cnt.toNat ≠ j by omega]
    · cases k with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [i5 _ (by rw [hc1]; omega), hst, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds]
        have : top.toNat + cnt.toNat < 2 ^ 41 := by omega
        simp [vpool_size, this]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have := i6 k (by simpa using hk)
        rw [hc1, tblW_congr (TblSame.of_eq (hP LID (by decide)) (hP _ (by decide)) (hP CTL (by decide)))] at this
        rw [← this]; congr 1; omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hok
      · rw [← tblOK_congr (TblSame.of_eq (hP LID (by decide)) (hP _ (by decide)) (hP CTL (by decide)))]; exact i7 x hx
    · obtain ⟨i2, i8⟩ := i8 (by rw [hP CTL (by decide)]; exact hc)
      refine ⟨i2, PFrame.trans ?_ i8⟩
      exact PFrame.set64_both _ _ _ (PFrame.set64 _ _ _ (PFrame.refl _)) (by decide) (by decide)
  | case4 m i cnt h1 h2 h3 h4 h5 h6 => intro m' h; cases h
  | case5 m i cnt h1 h2 h3 h4 =>
    intro m' h hr hs
    cases h
    rw [lsCntN_noprog _ _ _ h1 h2 h3 h4, itemsN_noprog _ _ h1 h2 h3 h4]
    refine ⟨by simp, pcap_set64 _ _ _ _, hr, fun j _ => by
      rw [vpool_set64_ne _ _ _ _ (by decide)], fun k hk => by simp at hk, by simp,
      fun hc => ⟨Mem.top_set64 _ _ hc, by rw [Mem.top_set64 _ _ hc]; exact PFrame.refl _⟩⟩
  | case6 m i cnt h1 h2 h3 ih =>
    intro m' h hr hs
    rw [lsCntN_other _ _ _ h1 h2 h3, itemsN_other _ _ h1 h2 h3]
    exact ih m' h hr hs
  | case7 m i cnt h1 =>
    intro m' h hr hs
    cases h
    rw [lsCntN_end _ _ _ h1, itemsN_end _ _ h1]
    refine ⟨by simp, pcap_set64 _ _ _ _, hr, fun j _ => by
      rw [vpool_set64_ne _ _ _ _ (by decide)], fun k hk => by simp at hk, by simp,
      fun hc => ⟨Mem.top_set64 _ _ hc, by rw [Mem.top_set64 _ _ hc]; exact PFrame.refl _⟩⟩

/-- `ls_put`'s slice fits in the pool after it (what `intern_ls` needs). -/
theorem lsPut_room (b : Array UInt8) (m m' : Mem) (v : Word) (h : lsPutW b m v = some m')
    (hs : pcap m < 2 ^ 63) (ht : m.top.toNat ≤ pcap m) :
    pcap m' < 2 ^ 64 ∧ m.top.toNat + (lsPutL b v).toNat ≤ pcap m' := by
  unfold lsPutW at h
  split at h
  · cases h
  rename_i hle
  have hp := pcap_eq m (by omega)
  have ht41 : m.top.toNat < 2 ^ 41 := by omega
  have hsz := pcap_tier m (m.top >>> 40) (by omega)
  have hsp := tag_split m.top
  have htr := tag_tier_le m.top ht41
  have hlen : (m.len64 (tierA POOL (m.top >>> 40))).toNat = (m.arr64 (tierA POOL (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have ht' : (m.top &&& 1099511627775).toNat ≤ (m.arr64 (tierA POOL (m.top >>> 40))).size := by
    have := UInt64.not_lt.mp hle; rw [UInt64.le_iff_toNat_le, hlen] at this; exact this
  obtain ⟨-, h3, h4, -⟩ := lsLoopM_facts b m.top ht41 m _ 0 m' h (by simpa using ht') hsz
  refine ⟨by omega, ?_⟩
  simp only [lsPutL]
  omega

/-- The length checks of `node_lit`/`node_lit_str`/`apply_str` on a slice `(o, l)` at an address
of a tier: the slice lies below `pcap` (what the stores' `intern_*` need). -/
theorem slice_room (m : Mem) (o l : Word) (hs : pcap m < 2 ^ 64) (ho : o.toNat ≤ pcap m)
    (h1 : ¬ m.len64 (tierA POOL (o >>> 40)) < o - (o >>> 40) <<< 40)
    (h2 : ¬ m.len64 (tierA POOL (o >>> 40)) - (o - (o >>> 40) <<< 40) < l) :
    o.toNat + l.toNat ≤ pcap m := by
  have hp := pcap_eq m hs
  have hsz := pcap_tier m (o >>> 40) hs
  have hsp := tag_split o
  have htr := tag_tier_le o (by omega)
  have hb : (o - (o >>> 40) <<< 40).toNat = (o &&& 1099511627775).toNat := by
    rw [tag_off_toNat, tag_idx_toNat]
  have hlen : (m.len64 (tierA POOL (o >>> 40))).toNat = (m.arr64 (tierA POOL (o >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  rw [UInt64.not_lt, UInt64.le_iff_toNat_le, hlen, hb] at h1
  rw [UInt64.not_lt, UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _
    (UInt64.le_iff_toNat_le.mpr (by rw [hlen, hb]; exact h1)), hlen, hb] at h2
  omega
grind_pattern [arena_grind] slice_room =>
  m.len64 (tierA POOL (o >>> 40)) - (o - (o >>> 40) <<< 40) < l, pcap m

theorem Keep.pcap {m m' : Mem} (h : Keep m m') : pcap m' = pcap m := pcap_congr (h.2 _) (h.2 _)
grind_pattern [arena_grind] Keep.pcap => Keep m m', pcap m'

theorem natDecW_top (b : Array UInt8) (m m' : Mem) (c d : Word) (r : List Word)
    (h : natDecW b m c d = some (r, m')) : r.headD 0 = m.top := by
  unfold natDecW at h
  split at h
  · cases h
  cases hD : decW b m (rdW (m.arr64 CTL) 0) 0 c d with
  | none => rw [hD] at h; cases h
  | some x =>
    rw [hD, finK_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; simp [rdW, Mem.top]
grind_pattern [arena_grind] natDecW_top => natDecW b m c d, some (r, m')

/-! ## The nodes -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
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

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
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

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
def nodeProj : FunDecl := lfn (a, c, d) locals (n, e, h) {
  if c == 18446744073709551615 { abort R_LONG_NUMBER };
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

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
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

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
def nodeLit : FunDecl := lfn (c, d) locals (o, l, h) {
  (o, l) := call nat_dec(c, d);
  if len(POOL⟨⦃o⦄.tier⟩) < o - ⦃o⦄.base { abort };
  if len(POOL⟨⦃o⦄.tier⟩) - (o - ⦃o⦄.base) < l { abort };
  h := call intern_lit(o, l);
  return h
}

/-- After `nat_dec`: its result `(o, l)` and memory (`none`: it aborted), then `intern_lit(o, l)`. -/
def litK : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    if m₁.len64 (tierA POOL (r.headD 0 >>> 40)) < r.headD 0 - (r.headD 0 >>> 40) <<< 40 then none
    else if m₁.len64 (tierA POOL (r.headD 0 >>> 40)) - (r.headD 0 - (r.headD 0 >>> 40) <<< 40) < r.tail.headD 0 then none
    else internW m₁ (r.headD 0) (r.tail.headD 0)

@[arena_grind =] theorem litK_none : litK none = none := rfl
@[arena_grind =] theorem litK_some (r : List Word) (m₁ : Mem) : litK (some (r, m₁)) =
    if m₁.len64 (tierA POOL (r.headD 0 >>> 40)) < r.headD 0 - (r.headD 0 >>> 40) <<< 40 then none
    else if m₁.len64 (tierA POOL (r.headD 0 >>> 40)) - (r.headD 0 - (r.headD 0 >>> 40) <<< 40) < r.tail.headD 0 then none
    else internW m₁ (r.headD 0) (r.tail.headD 0) := rfl

theorem litK_intern {r : List Word} {m₁ m' : Mem} {w : Word} (h : litK (some (r, m₁)) = some (w, m')) :
    internW m₁ (r.headD 0) (r.tail.headD 0) = some (w, m') := by
  rw [litK_some] at h
  split at h
  · cases h
  split at h
  · cases h
  exact h

/-- The model of `node_lit(c, d)`: the decimal digits `[c, d)` into the pool, interned. -/
def litW (b : Array UInt8) (m : Mem) (c d : Word) : Option (Word × Mem) := litK (natDecW b m c d)

/-! ## `node_lit_str`: a string literal's body, unescaped into the pool and interned

Shares the pattern of a `str` name line (`apply_str`, `Line.lean`): `str_put_esc` decodes the
body `[c, d)` into the pool at the old top, then `intern_lit_str` hash-conses the slice. A `c`
of `0` aborts (as `apply_str`'s), the sentinel for "no body". -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
def nodeLitStr : FunDecl := lfn (c, d) locals (o, l, h) {
  if c == 0 { abort };
  (o, l) := call str_put_esc(c, d);
  if len(POOL⟨⦃o⦄.tier⟩) < o - ⦃o⦄.base { abort };
  if len(POOL⟨⦃o⦄.tier⟩) - (o - ⦃o⦄.base) < l { abort };
  h := call intern_lit_str(o, l);
  return h
}

/-- After `str_put_esc`: its length result `l` and memory (`none`: it aborted, at the slice
`(o, l)`), then `intern_lit_str(o, l)`. -/
def litStrK (o : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (l, m₁) =>
    if m₁.len64 (tierA POOL (o >>> 40)) < o - (o >>> 40) <<< 40 then none
    else if m₁.len64 (tierA POOL (o >>> 40)) - (o - (o >>> 40) <<< 40) < l then none
    else internWStr m₁ o l

@[arena_grind =] theorem litStrK_none (o : Word) : litStrK o none = none := rfl
@[arena_grind =] theorem litStrK_some (o l : Word) (m₁ : Mem) : litStrK o (some (l, m₁)) =
    if m₁.len64 (tierA POOL (o >>> 40)) < o - (o >>> 40) <<< 40 then none
    else if m₁.len64 (tierA POOL (o >>> 40)) - (o - (o >>> 40) <<< 40) < l then none
    else internWStr m₁ o l := rfl

theorem litStrK_intern {o l : Word} {m₁ m' : Mem} {w : Word}
    (h : litStrK o (some (l, m₁)) = some (w, m')) : internWStr m₁ o l = some (w, m') := by
  rw [litStrK_some] at h
  split at h
  · cases h
  split at h
  · cases h
  exact h

/-- The model of `node_lit_str(c, d)`: the string body `[c, d)`, unescaped into the pool and
interned. -/
def litStrW (b : Array UInt8) (m : Mem) (c d : Word) : Option (Word × Mem) :=
  if c = 0 then none else litStrK m.top (strPutEscW b m c d)

/-! ## `expr_node`, `apply_expr` -/

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
def exprNode : FunDecl := lfn (pl, a, c, d) locals (u, h) {
  if pl == 8 {
    if a == 18446744073709551615 { abort R_LONG_NUMBER };
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
  if pl == 17 { h := call node_lit_str(c, d); return h };
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
  else if pl = 17 then litStrW b m c d
  else none

/-- con-ron: ConRon/Arena/Frontend/ExportC.lean:191-222 ConRon.Arena.Frontend.parseExprEntryD -/
@[l_impl ConRon.Arena.Frontend.parseExprEntryD]
def applyExpr : FunDecl := lfn (pl, idx, a, c, d) locals (z, h) {
  z := call expr_fresh(idx);
  h := call expr_node(pl, a, c, d);
  if h >= 4294967296 { abort };
  z := call expr_put(idx, h);
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
   ("lit_match_str", litMatchStr), ("lit_find_str", litFindStr), ("lit_push_str", litPushStr),
   ("intern_lit_str", internLitStr),
   ("esp_find", memoFindG (spS EID)), ("esp_put", memoPutG (spS EID)),
   ("expr_get", exprGet), ("expr_fresh", exprFresh), ("expr_put", exprPut), ("ls_put", lsPut), ("node_bin", nodeBin),
   ("node_let", nodeLet), ("node_proj", nodeProj), ("node_const", nodeConst),
   ("node_lit", nodeLit), ("node_lit_str", nodeLitStr), ("expr_node", exprNode),
   ("apply_expr", applyExpr), ("dec_chunk", decChunk), ("nat_mad", natMad), ("nat_dec", natDec),
   ("byte_in", L.Scan.Str.byteIn), ("hex_val", L.Scan.Str.hexVal), ("hex4", L.Scan.Str.hex4),
   ("hex3", L.Scan.Str.hex3), ("esc_sur", L.Front.Unescape.escSur),
   ("esc_one", L.Front.Unescape.escOne), ("utf8_put", L.Front.Unescape.utf8Put),
   ("str_put_esc", L.Front.Unescape.strPutEsc)]

/-- Every word array 128 words (all zero), the input `[0, 1]`. -/
def exprMem : Mem :=
  { bytes := #["[0, 1]5".toUTF8.data], words := Array.replicate 75 (Array.replicate 128 0) }

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

/-- Input `"ab""cd"`: two quoted strings, no escapes. -/
def exprStrMem : Mem :=
  { bytes := #["\"ab\"\"cd\"".toUTF8.data], words := Array.replicate 75 (Array.replicate 128 0) }

/- `"ab"` interned twice (the same handle, `0x80000000`), `"cd"` a different one (`0x80000001`). -/
#guard exprRuns exprStrMem
  [("front_init", []), ("apply_expr", [17, 0, 0, 1, 3]), ("apply_expr", [17, 1, 0, 1, 3]),
   ("apply_expr", [17, 2, 0, 5, 7]),
   ("expr_get", [0]), ("expr_get", [1]), ("expr_get", [2])] ==
  some [[0], [0], [0], [0], [0x80000000], [0x80000000], [0x80000001]]

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
  lit_match_str : p.lookup "lit_match_str" = some litMatchStr
  lit_find_str : p.lookup "lit_find_str" = some litFindStr
  lit_push_str : p.lookup "lit_push_str" = some litPushStr
  intern_lit_str : p.lookup "intern_lit_str" = some internLitStr
  expr_get : p.lookup "expr_get" = some exprGet
  expr_fresh : p.lookup "expr_fresh" = some exprFresh
  esp_find : p.lookup "esp_find" = some (memoFindG (spS EID))
  esp_put : p.lookup "esp_put" = some (memoPutG (spS EID))
  expr_put : p.lookup "expr_put" = some exprPut
  ls_put : p.lookup "ls_put" = some lsPut
  node_bin : p.lookup "node_bin" = some nodeBin
  node_let : p.lookup "node_let" = some nodeLet
  node_proj : p.lookup "node_proj" = some nodeProj
  node_const : p.lookup "node_const" = some nodeConst
  node_lit : p.lookup "node_lit" = some nodeLit
  node_lit_str : p.lookup "node_lit_str" = some nodeLitStr
  expr_node : p.lookup "expr_node" = some exprNode
  apply_expr : p.lookup "apply_expr" = some applyExpr
  dec_chunk : p.lookup "dec_chunk" = some decChunk
  nat_mad : p.lookup "nat_mad" = some natMad
  nat_dec : p.lookup "nat_dec" = some natDec
  no_st8 : p.noSt8 = true

section specs
variable (p : Prog) (hE : ExprLookups p)
include hE

theorem exprGet_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "expr_get" [i]
    ⦃fun r s' => s' = s₀ ∧ tblOK s₀.mem EID i = true ∧ r = [tblW s₀.mem EID i]; ⊤⦄ :=
  tblGetG_spec p EID "esp_find" hE.esp_find _ hE.expr_get n s₀ i

theorem exprFresh_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "expr_fresh" [i]
    ⦃fun _ s' => s' = s₀ ∧ tblFresh s₀.mem EID i = true; ⊤⦄ :=
  tblFreshG_spec p EID "esp_find" hE.esp_find _ hE.expr_fresh n s₀ i

theorem exprPut_spec (n : Nat) (s₀ : St) (i h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "expr_put" [i, h]
    ⦃fun _ s' => LocEq s' s₀ ∧ tblPutW s₀.mem EID i h = some s'.mem; ⊤⦄ :=
  tblPutG_spec p EID "esp_find" "esp_put" hE.esp_find hE.esp_put _ hE.expr_put n s₀ i h

theorem lsLoop_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b ∧ s.loc 8 = s.loc 2 >>> 40 ∧
      s.loc 9 = s.loc 2 &&& 1099511627775⦄
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
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b ∧ s.loc 8 = s.loc 2 >>> 40 ∧
      s.loc 9 = s.loc 2 &&& 1099511627775⦄
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
    (hps : pcap s₀.mem < 2 ^ 63) (htop : s₀.mem.top.toNat ≤ pcap s₀.mem) (c d : Word) :
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

theorem nodeLitStr_spec (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpb : p.lookup "byte_in" = some L.Scan.Str.byteIn)
    (hph : p.lookup "hex_val" = some L.Scan.Str.hexVal)
    (hp4 : p.lookup "hex4" = some L.Scan.Str.hex4) (hp3 : p.lookup "hex3" = some L.Scan.Str.hex3)
    (hpsu : p.lookup "esc_sur" = some L.Front.Unescape.escSur)
    (hpo : p.lookup "esc_one" = some L.Front.Unescape.escOne)
    (hpu : p.lookup "utf8_put" = some L.Front.Unescape.utf8Put)
    (hpe : p.lookup "str_put_esc" = some strPutEsc) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hps : pcap s₀.mem < 2 ^ 63) (htop : s₀.mem.top.toNat ≤ pcap s₀.mem) (c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "node_lit_str" [c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ litStrW b s₀.mem c d = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hE.node_lit_str]
  simp only [callFn, nodeLitStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hesc : ∀ (s₁ : St), s₁.mem.arr8 IN = b → ∀ c d : Word,
        ⦃fun s => s = s₁⦄ invoke p (exec p n) "str_put_esc" [c, d]
        ⦃fun r s' => (LocEq s' s₁ ∧ r.headD 0 = s₁.mem.top ∧
          strPutEscW b s₁.mem c d = some (r.tail.headD 0, s'.mem)) ∧
          Keep s₁.mem s'.mem ∧ LocEq s' s₁; ⊤⦄ := fun s₁ hm₁ c d =>
      Triple.keep hE.no_st8 (strPutEsc_specW p b hb hpb hph hp4 hp3 hpsu hpo hpu hpe n s₁ hm₁ c d)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hesc,
        internLitStr_spec p hE.front.lit_hash hE.front.limbs_eq hE.lit_match_str hE.lit_find_str
          hE.lit_push_str hE.intern_lit_str n] <;>
      finish [litStrW, Keep.size]

theorem nodeConst_spec (b : Array UInt8) (hb : b.size < 2 ^ 63) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (hps : pcap s₀.mem < 2 ^ 63) (htop : s₀.mem.top.toNat ≤ pcap s₀.mem) (a c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "node_const" [a, c]
    ⦃fun r s' => LocEq s' s₀ ∧ constW b s₀.mem a c = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hE.node_const]
  simp only [callFn, nodeConst]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hroom := fun m' h => lsPut_room b s₀.mem m' c h hps htop
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, nameGet_spec p hE.front n,
        lsPut_spec p hE b hb n,
        internLs_spec p hE.front.lit_hash hE.front.limbs_eq hE.ls_match hE.ls_find hE.ls_push
          hE.intern_ls n,
        internConst_spec p hE.const_find hE.const_push hE.intern_const n] <;>
      finish [constW]

theorem exprNode_spec (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpb : p.lookup "byte_in" = some L.Scan.Str.byteIn)
    (hph : p.lookup "hex_val" = some L.Scan.Str.hexVal)
    (hp4 : p.lookup "hex4" = some L.Scan.Str.hex4) (hp3 : p.lookup "hex3" = some L.Scan.Str.hex3)
    (hpsu : p.lookup "esc_sur" = some L.Front.Unescape.escSur)
    (hpo : p.lookup "esc_one" = some L.Front.Unescape.escOne)
    (hpu : p.lookup "utf8_put" = some L.Front.Unescape.utf8Put)
    (hpe : p.lookup "str_put_esc" = some strPutEsc) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (hps : pcap s₀.mem < 2 ^ 63) (htop : s₀.mem.top.toNat ≤ pcap s₀.mem) (pl a c d : Word) :
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
        nodeConst_spec p hE b hb n, nodeLit_spec p hE b n,
        nodeLitStr_spec p hE b hb hpb hph hp4 hp3 hpsu hpo hpu hpe n] <;>
      finish [nodeW, NONE]

theorem applyExpr_spec (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpb : p.lookup "byte_in" = some L.Scan.Str.byteIn)
    (hph : p.lookup "hex_val" = some L.Scan.Str.hexVal)
    (hp4 : p.lookup "hex4" = some L.Scan.Str.hex4) (hp3 : p.lookup "hex3" = some L.Scan.Str.hex3)
    (hpsu : p.lookup "esc_sur" = some L.Front.Unescape.escSur)
    (hpo : p.lookup "esc_one" = some L.Front.Unescape.escOne)
    (hpu : p.lookup "utf8_put" = some L.Front.Unescape.utf8Put)
    (hpe : p.lookup "str_put_esc" = some strPutEsc) (n : Nat) (s₀ : St)
    (hm : s₀.mem.arr8 IN = b) (hps : pcap s₀.mem < 2 ^ 63) (htop : s₀.mem.top.toNat ≤ pcap s₀.mem) (pl idx a c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "apply_expr" [pl, idx, a, c, d]
    ⦃fun _ s' => LocEq s' s₀ ∧ applyExprW b s₀.mem pl idx a c d = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hE.apply_expr]
  simp only [callFn, applyExpr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        exprFresh_spec p hE n, exprPut_spec p hE n, exprNode_spec p hE b hb hpb hph hp4 hp3 hpsu hpo hpu hpe n] <;>
      finish [applyExprW]

end specs

end L.Front
