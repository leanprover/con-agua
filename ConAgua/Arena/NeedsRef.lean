module

public import ConAgua.Arena.NeedsModels
public import ConAgua.Arena.IndRealFvt
public import ConAgua.Arena.Frame
import ConAgua.Arena.DefEqMidQuick
import ConAgua.Arena.CoreErec
import ConAgua.Arena.WhnfCoreProj
import all ConAgua.Arena.Needs

@[expose] public section

/-!
# What a record reads, in L: the refinements, part 1 (lane compare, helper H1)

The walk's state and its frame, `needs_name` (the push), the name loops, `lit_needs` and
`needs_go` against the twin's `Arena/Needs.lean`. A run is from the stage relation `StageR vis fe`
and the walk's state `NeedsR` (`JustifyIface.lean`) at the twin state `a`, which no function of the
walk changes: a returning L run is the twin's `.ok` run, the state after related by `NeedsR`, and
the run writes only the walk's arrays and control words (`ndA`, `ndC`), so the stage is kept.
-/

open ConRon.Arena
open Std.WP

namespace L.Arena

open L.Ind L.Stubs

/-! ## The walk's write set -/

/-- The arrays the walk writes: the memo and the stack. -/
def ndA : List TieredArray := [NDM, NACC]

/-- The control words the walk writes: the memo's stamp and count, the stack's top. -/
def ndC : List Word := [220, 221, NTOPC]

/-- **The walk's state with room for its top word**: `NeedsR` and the control word `CTL[227]`
inside `CTL`. -/
structure NdR (m : Mem) (x : NeedsSt) : Prop where
  rel : NeedsR m x
  ctl : NTOPC.toNat < (m.arr64 CTL).size

theorem ndA_stage : ∀ b ∈ ndA, b.hi = false ∧ 137 ≤ b.arr ∧ (b.arr < 140 ∨ 144 ≤ b.arr) ∧
    (b.arr < 146 ∨ 149 ≤ b.arr) := by decide

theorem ndC_stage : ∀ x ∈ ndC, 131 ≤ x.toNat ∧ x.toNat ≠ 133 ∧ x.toNat ≠ 134 ∧ x.toNat ≠ 135 ∧
    (x.toNat < 160 ∨ 172 ≤ x.toNat) := by
  intro x hx; simp only [ndC, NTOPC, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> simp

/-- **The stage across the walk's writes.** -/
theorem StageR.ndFrame {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} (hS : StageR vis fe m a)
    (hf : MemFrame ndA ndC m m') : StageR vis fe m' a ∧ IWGrow m m' :=
  hS.frame_hi hf ndA_stage ndC_stage (by simp [ndA]; decide) (by simp [ndC, NTOPC])

/-- **The walk's state across a frame that writes none of it.** -/
theorem NdR.frame {A : List TieredArray} {C : List Word} {m m' : Mem} {x : NeedsSt}
    (hf : MemFrame A C m m') (hA : (NDM : TieredArray) ∉ A ∧ (NACC : TieredArray) ∉ A)
    (hC : (220 : Word) ∉ C ∧ NTOPC ∉ C) (h : NdR m x) : NdR m' x := by
  have hN : m'.arr64 NACC = m.arr64 NACC := hf.arr _ hA.2 (by decide)
  have hT : ctlW m' NTOPC = ctlW m NTOPC := hf.ctl _ hC.2
  refine ⟨⟨memoRG_frame ndSch ndSch_wf bmKey _ A C hA.1 hC.1 m m' hf _ h.rel.seen, ?_, ?_, ?_⟩, ?_⟩
  · rw [← h.rel.acc]; simp only [naccList, hN, hT]
  · intro i hi; rw [hN]; exact h.rel.words i (by rw [← hT]; exact hi)
  · rw [hN, hT]; exact h.rel.room
  · rw [hf.size]; exact h.ctl

/-! ## The program -/

/-- The functions the walk's calls reach (the write set `ndA`, `ndC` is decided on the concrete
program; `nat_op_deps` writes the work pool besides, `ndFns` does not hold it). -/
def ndFns : List FnName :=
  ["needs_reset", "needs_name", "needs_names", "needs_names_iw", "lit_needs", "needs_go",
   "needs_expr", "needs_exprs", "needs_rule", "needs_rules", "pin_footprint_reduce",
   "pin_at", "e_view", "nd_find", "nd_put", "nd_clear", "nat_op_name", "pin_range_has"]

/-- **What the refinements need of a program.** -/
structure NeedsProg (p : Prog) : Prop where
  reset : p.lookup "needs_reset" = some needsResetL
  name : p.lookup "needs_name" = some needsNameL
  names : p.lookup "needs_names" = some needsNamesL
  names_iw : p.lookup "needs_names_iw" = some needsNamesIwL
  lit : p.lookup "lit_needs" = some litNeedsL
  go : p.lookup "needs_go" = some needsGoL
  expr : p.lookup "needs_expr" = some needsExprL
  exprs : p.lookup "needs_exprs" = some needsExprsL
  rule : p.lookup "needs_rule" = some needsRuleL
  rules : p.lookup "needs_rules" = some needsRulesL
  pfr : p.lookup "pin_footprint_reduce" = some pinFootprintReduceL
  pfn : p.lookup "pin_footprint_nat" = some pinFootprintNatL
  pf : p.lookup "pin_footprint" = some pinFootprintL
  const : p.lookup "needs_const" = some needsConstL
  table : p.lookup "needs_table" = some needsTableL
  e_view : p.lookup "e_view" = some eView
  pin_at : p.lookup "pin_at" = some pinAtL
  nd_find : p.lookup "nd_find" = some (memoFindG ndSch)
  nd_put : p.lookup "nd_put" = some (memoPutG ndSch)
  nd_clear : p.lookup "nd_clear" = some (memoClearG ndSch)
  nat_op_name : p.lookup "nat_op_name" = some natOpNameL
  pin_range_has : p.lookup "pin_range_has" = some pinRangeHas
  /-- The walk writes only its own arrays and control words (decided on the concrete program). -/
  closed : closedA p ndA ndC ndFns = true

section steps
variable {p : Prog} (P : NeedsProg p) {vis : Word} {fe : IFEnv} {a : AState}
include P

/-- A call of a walk function writes only the walk's state. -/
theorem nd_frame {f : FnName} (hf : f ∈ ndFns) {n : Nat} {args r : List Word} {m m' : Mem}
    (hc : callW p n f args m = some (r, m')) : MemFrame ndA ndC m m' :=
  (run_memFrame P.closed hf (run_of_callW hc)).1

/-! ## `needs_name` -/

/-- The memory after a push of `w` at the top `t`. -/
abbrev pushM (m : Mem) (t w : Word) : Mem := (m.set64 NACC t w).set64 CTL NTOPC (t + 1)

omit P in
theorem push_frame (m : Mem) (t w : Word) : MemFrame [NACC] [NTOPC] m (pushM m t w) :=
  ((MemFrame.set64 m NACC (by decide) t w).mono (by simp) (by simp)).trans
    ((MemFrame.setCtl _ NTOPC (t + 1)).mono (by simp) (by simp))

omit P in
/-- **A push is `NeedsSt.name`.** -/
theorem NdR.push {m : Mem} {x : NeedsSt} (h : NdR m x) {w : Word} (hw : HW w)
    (hlt : ¬ m.len64 NACC ≤ ctlW m NTOPC) :
    NdR (pushM m (ctlW m NTOPC) w) (x.name (decI w)) := by
  obtain ⟨t, ht⟩ : ∃ t, ctlW m NTOPC = t := ⟨_, rfl⟩
  rw [ht] at hlt ⊢
  have hl : t.toNat < (m.arr64 NACC).size % 2 ^ 64 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    simpa [len64_eq] using this
  have hl' : t.toNat < (m.arr64 NACC).size := Nat.lt_of_lt_of_le hl (Nat.mod_le _ _)
  have ht1 : (t + 1).toNat = t.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
  have hN : (pushM m t w).arr64 NACC = (m.arr64 NACC).set! t.toNat w := by
    simp only [pushM]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_same]
  have hT : ctlW (pushM m t w) NTOPC = t + 1 := by
    simp only [ctlW, pushM, rdW_set64, Mem.size64_set64, h.ctl, and_self, ite_true]
  have hrd : ∀ i, rdN ((m.arr64 NACC).set! t.toNat w) i = if i = t.toNat then w else rdN (m.arr64 NACC) i := by
    intro i
    simp only [rdN, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases e : t.toNat = i
    · subst e; simp [hl']
    · simp [e, Ne.symm e]
  have hx := h.rel
  have hseen := memoRG_frame ndSch ndSch_wf bmKey _ [NACC] [NTOPC] (by decide) (by decide) m _
    (push_frame m t w) _ hx.seen
  refine ⟨⟨hseen, ?_, ?_, ?_⟩, ?_⟩
  · simp only [NeedsSt.name, ← hx.acc, naccList, hN, hT, ht1, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, hrd, ite_true, ht]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have : i ≠ t.toNat := by have := List.mem_range.mp hi; omega
    simp only [this, ite_false]
  · intro i hi
    rw [hN, hrd]
    rw [hT, ht1] at hi
    split
    · exact hw
    · exact hx.words i (by rw [ht]; omega)
  · have := hx.room; rw [ht] at this; rw [hN, hT, ht1, Array.size_set!]; omega
  · simp only [pushM, Mem.size64_set64]; exact h.ctl

/-- **`needs_name(w)` refines `NeedsSt.name`**: the name pushed. -/
theorem needsName_step {n : Nat} {m m' : Mem} {w : Word} {r : List Word} {x : NeedsSt}
    (hc : callW p n "needs_name" [w] m = some (r, m')) (hx : NdR m x) (hw : HW w) :
    NdR m' (x.name (decI w)) ∧ MemFrame ndA ndC m m' := by
  refine ⟨?_, nd_frame P (by decide) hc⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (needsName_specW p P.name n _ w) hc
  simp only [needsNameW] at hW
  split at hW
  · cases hW
  · obtain ⟨-, e⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [← e]; exact hx.push hw ‹_›

omit P in
/-- The record pool across the walk's writes. -/
theorem erecP_nd {m m' : Mem} (hf : MemFrame ndA ndC m m') : erecP m' = erecP m := by
  have h0 : m'.arr64 EREC = m.arr64 EREC := hf.arr _ (by decide) (by decide)
  have h1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr _ (by decide) (by decide)
  have t0 : erTop m' = erTop m := by simp only [erTop]; rw [hf.ctl _ (by simp [ndC, NTOPC])]
  have t1 : erecTop1 m' = erecTop1 m := by simp only [erecTop1]; rw [hf.ctl _ (by simp [ndC, NTOPC])]
  funext i; simp only [erecP, h0, h1, t0, t1]

omit P in
/-- The work pool across the walk's writes. -/
theorem iwA_nd {m m' : Mem} (hf : MemFrame ndA ndC m m') : iwA m' = iwA m := by
  simp only [iwA]; rw [hf.arr _ (by decide) (by decide)]

/-- **`needs_names`' loop**: from cursor `i`, the names of the slice pushed in order. -/
theorem needsNamesLoop : ∀ (n : Nat) (m m' : Mem) (o l i : Word) (x : NeedsSt) (ns : List NIdx),
    needsNamesW.loop1 p n m o l i = some m' → NdR m x → i ≤ l →
    hslice? (erecP m) (o.toNat + i.toNat) (l.toNat - i.toNat) = some ns →
    NdR m' ⟨x.seen, x.acc ++ ns⟩ ∧ MemFrame ndA ndC m m'
  | 0, _, _, _, _, _, _, _, hW, _, _, _ => by rw [needsNamesW.loop1.eq_1] at hW; cases hW
  | n + 1, m, m', o, l, i, x, ns, hW, hx, hil, hns => by
    by_cases hlt : i < l
    · rw [needsNamesW.loop1.arm1 _ _ _ _ _ _ hlt] at hW
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        have := UInt64.lt_iff_toNat_lt.mp hlt; have := l.toNat_lt
        rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
      have hk : l.toNat - i.toNat = (l.toNat - (i + 1).toNat) + 1 := by
        have := UInt64.lt_iff_toNat_lt.mp hlt; omega
      rw [hk, hslice?_succ] at hns
      cases e1 : (hd? (erecP m) (o.toNat + i.toNat) : Option NIdx) with
      | none => rw [e1] at hns; cases hns
      | some w =>
      cases e2 : (hslice? (erecP m) (o.toNat + i.toNat + 1) (l.toNat - (i + 1).toNat) : Option (List NIdx)) with
      | none => rw [e1, e2] at hns; cases hns
      | some ns' =>
      rw [e1, e2] at hns
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hns
      subst hns
      obtain ⟨wd, hwd, hwlt, rfl⟩ := hd?_some e1
      have hoi : (o + i).toNat = o.toNat + i.toNat := by
        have : o.toNat + i.toNat < 2 ^ 64 := by
          rcases Nat.lt_or_ge (o.toNat + i.toNat) (2 ^ 64) with h | h
          · exact h
          · simp [erecP, show ¬ o.toNat + i.toNat < 2 ^ 64 by omega] at hwd
        rw [UInt64.toNat_add]; omega
      have hrd : erRd m (o + i) = wd := (erRd_of_erecP (by rw [hoi]; exact hwd)).1
      rw [hrd] at hW
      rcases c1 : callW p n "needs_name" [wd] m with _ | ⟨r1, m1⟩
      · rw [c1, needsNamesW.k_needs_name.eq_1] at hW; cases hW
      rw [c1, needsNamesW.k_needs_name.arm1] at hW
      obtain ⟨hx1, hf1⟩ := needsName_step P c1 hx hwlt
      have hs1 : hslice? (erecP m1) (o.toNat + (i + 1).toNat) (l.toNat - (i + 1).toNat) =
          some ns' := by rw [erecP_nd hf1, hi1, ← Nat.add_assoc, ← hi1]; exact e2
      obtain ⟨hx2, hf2⟩ := needsNamesLoop n m1 m' o l (i + 1) _ ns' hW hx1
        (by rw [UInt64.le_iff_toNat_le, hi1]; have := UInt64.lt_iff_toNat_lt.mp hlt; omega) hs1
      refine ⟨?_, hf1.trans hf2⟩
      simpa [NeedsSt.name] using hx2
    · rw [needsNamesW.loop1.arm2 _ _ _ _ _ _ hlt] at hW
      cases hW
      have hle : l.toNat - i.toNat = 0 := by
        have := UInt64.le_iff_toNat_le.mp hil; have := UInt64.not_lt.mp hlt
        have := UInt64.le_iff_toNat_le.mp this; omega
      rw [hle] at hns
      simp only [hslice?, List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at hns
      subst hns
      exact ⟨by simpa using hx, MemFrame.refl _ _ _⟩

/-- **`needs_names_iw`' loop**: from cursor `i`, the names of the slice pushed in order. -/
theorem needsNamesIwLoop : ∀ (n : Nat) (m m' : Mem) (o l i : Word) (x : NeedsSt) (ns : List NIdx),
    needsNamesIwW.loop1 p n m o l i = some m' → NdR m x → (m.arr64 IW).size < 2 ^ 64 → i ≤ l →
    hslice? (iwA m) (o.toNat + i.toNat) (l.toNat - i.toNat) = some ns →
    NdR m' ⟨x.seen, x.acc ++ ns⟩ ∧ MemFrame ndA ndC m m'
  | 0, _, _, _, _, _, _, _, hW, _, _, _, _ => by rw [needsNamesIwW.loop1.eq_1] at hW; cases hW
  | n + 1, m, m', o, l, i, x, ns, hW, hx, hsz, hil, hns => by
    by_cases hlt : i < l
    · rw [needsNamesIwW.loop1.arm1 _ _ _ _ _ _ hlt] at hW
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        have := UInt64.lt_iff_toNat_lt.mp hlt; have := l.toNat_lt
        rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
      have hk : l.toNat - i.toNat = (l.toNat - (i + 1).toNat) + 1 := by
        have := UInt64.lt_iff_toNat_lt.mp hlt; omega
      rw [hk, hslice?_succ] at hns
      cases e1 : (hd? (iwA m) (o.toNat + i.toNat) : Option NIdx) with
      | none => rw [e1] at hns; cases hns
      | some w =>
      cases e2 : (hslice? (iwA m) (o.toNat + i.toNat + 1) (l.toNat - (i + 1).toNat) : Option (List NIdx)) with
      | none => rw [e1, e2] at hns; cases hns
      | some ns' =>
      rw [e1, e2] at hns
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hns
      subst hns
      obtain ⟨wd, hwd, hwlt, rfl⟩ := hd?_some e1
      have hoi : (o + i).toNat = o.toNat + i.toNat := by
        have : o.toNat + i.toNat < 2 ^ 64 := by
          rcases Nat.lt_or_ge (o.toNat + i.toNat) (2 ^ 64) with h | h
          · exact h
          · have := (Array.getElem?_eq_some_iff.mp (show (m.arr64 IW)[o.toNat + i.toNat]? = some wd from hwd)).1
            omega
        rw [UInt64.toNat_add]; omega
      have hrd : rdW (m.arr64 IW) (o + i) = wd := by
        simp only [iwA, aread] at hwd; simp only [rdW, hoi, hwd, Option.getD_some]
      rw [hrd] at hW
      rcases c1 : callW p n "needs_name" [wd] m with _ | ⟨r1, m1⟩
      · rw [c1, needsNamesIwW.k_needs_name.eq_1] at hW; cases hW
      rw [c1, needsNamesIwW.k_needs_name.arm1] at hW
      obtain ⟨hx1, hf1⟩ := needsName_step P c1 hx hwlt
      have hs1 : hslice? (iwA m1) (o.toNat + (i + 1).toNat) (l.toNat - (i + 1).toNat) =
          some ns' := by rw [iwA_nd hf1, hi1, ← Nat.add_assoc, ← hi1]; exact e2
      obtain ⟨hx2, hf2⟩ := needsNamesIwLoop n m1 m' o l (i + 1) _ ns' hW hx1 (by rw [hf1.size]; exact hsz)
        (by rw [UInt64.le_iff_toNat_le, hi1]; have := UInt64.lt_iff_toNat_lt.mp hlt; omega) hs1
      refine ⟨?_, hf1.trans hf2⟩
      simpa [NeedsSt.name] using hx2
    · rw [needsNamesIwW.loop1.arm2 _ _ _ _ _ _ hlt] at hW
      cases hW
      have hle : l.toNat - i.toNat = 0 := by
        have := UInt64.le_iff_toNat_le.mp hil; have := UInt64.not_lt.mp hlt
        have := UInt64.le_iff_toNat_le.mp this; omega
      rw [hle] at hns
      simp only [hslice?, List.range_zero, List.mapM_nil, Option.pure_def, Option.some.injEq] at hns
      subst hns
      exact ⟨by simpa using hx, MemFrame.refl _ _ _⟩

omit P in
theorem names_eq (x : NeedsSt) (ns : List NIdx) : x.names ns = ⟨x.seen, x.acc ++ ns⟩ := by
  simp [NeedsSt.names, nidxAppend]

/-- **`needs_names(o, l)` refines `NeedsSt.names`** over the `EREC` slice's names. -/
theorem needsNames_step {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} {x : NeedsSt}
    {ns : List NIdx} (hc : callW p n "needs_names" [o, l] m = some (r, m')) (hx : NdR m x)
    (hns : hslice? (erecP m) o.toNat l.toNat = some ns) :
    NdR m' (x.names ns) ∧ MemFrame ndA ndC m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (needsNames_specW p P.names n _ o l) hc
  rcases n with _ | n
  · rw [needsNamesW.eq_1] at hW; cases hW
  rw [needsNamesW.arm1] at hW
  rcases e : needsNamesW.loop1 p (n + 1) m o l 0 with _ | m1
  · rw [e, needsNamesW.k_loop1.eq_1] at hW; cases hW
  rw [e, needsNamesW.k_loop1.arm1] at hW
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [names_eq]
  exact needsNamesLoop P (n + 1) m _ o l 0 x ns e hx (by rw [UInt64.le_iff_toNat_le]; simp) (by simpa using hns)

/-- **`needs_names_iw(o, l)` pushes the `IW` slice's names** (`nidxAppend` at the slice). -/
theorem needsNamesIw_step {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} {x : NeedsSt}
    {ns : List NIdx} (hc : callW p n "needs_names_iw" [o, l] m = some (r, m')) (hx : NdR m x)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hns : hslice? (iwA m) o.toNat l.toNat = some ns) :
    NdR m' ⟨x.seen, nidxAppend x.acc ns 0 ns.length⟩ ∧ MemFrame ndA ndC m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (needsNamesIw_specW p P.names_iw n _ o l) hc
  rcases n with _ | n
  · rw [needsNamesIwW.eq_1] at hW; cases hW
  rw [needsNamesIwW.arm1] at hW
  rcases e : needsNamesIwW.loop1 p (n + 1) m o l 0 with _ | m1
  · rw [e, needsNamesIwW.k_loop1.eq_1] at hW; cases hW
  rw [e, needsNamesIwW.k_loop1.arm1] at hW
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  simp only [nidxAppend, List.drop_zero, Nat.sub_zero, List.take_length]
  exact needsNamesIwLoop P (n + 1) m _ o l 0 x ns e hx hsz (by rw [UInt64.le_iff_toNat_le]; simp)
    (by simpa using hns)

end steps

end L.Arena
