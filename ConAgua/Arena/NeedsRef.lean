module

public import ConAgua.Arena.NeedsModels
public import ConAgua.Arena.IndRealFvt
public import ConAgua.Arena.Frame
import ConAgua.Arena.DefEqMidQuick
import ConAgua.Arena.CoreErec
import ConAgua.Arena.InferBodyDisp
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
theorem _root_.L.Ind.StageR.ndFrame {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} (hS : StageR vis fe m a)
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

/-! ## Continuations -/

/-- A continuation that passes `none` on returned `some`: its argument was `some`. -/
theorem opt_some {α β : Type} {K : Option α → Option β} {x : Option α} {y : β} (h : K x = some y)
    (hK : K none = none) : ∃ q, x = some q ∧ K (some q) = some y := by
  cases x with
  | none => rw [hK] at h; cases h
  | some q => exact ⟨q, rfl, h⟩

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

/-! ## `lit_needs` -/

/-- A `pin_at(k)` call under the stage: the memory kept, a handle, the twin's `pinAt k`. -/
theorem pinCall {n : Nat} {m m' : Mem} {k : Word} {r : List Word}
    (hc : callW p n "pin_at" [k] m = some (r, m')) (hS : StageR vis fe m a) :
    m = m' ∧ HW (r.headD 0) ∧ (pinAt k.toNat).run a = .ok (decI (r.headD 0), a) := by
  obtain ⟨s', rfl, hm, -, hlt, hrun⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pinAt_refines p P.pin_at n _ a hS.check.pins k) hc
  exact ⟨hm.symm, hlt, hrun⟩

omit P in
/-- A literal `e_view` returned for: the view checks passed. -/
theorem viewOK_lit {m : Mem} {h : Word} (hne : eViewW m h ≠ []) (hg : tagW h = 8) :
    viewOK m h LIT := by
  unfold eViewW at hne
  simp only [hg] at hne
  refine ⟨fun hc => hne (by simp [hc]), UInt64.not_le.mp fun hle => hne (by simp [hle])⟩

omit P in
/-- The literal's kind word across the walk's writes. -/
theorem tfld_nd {m m' : Mem} (hf : MemFrame ndA ndC m m') (t i f : Word) :
    tfld m' LIT t i f = tfld m LIT t i f := by
  simp only [tfld]; rw [hf.tier _ (by decide) (by decide) (by decide)]

/-- **`lit_needs(h)` refines `litNeeds`** at the literal `h` views as (`e_view` returned its
words, tag `8`). -/
theorem litNeeds_step {n : Nat} {m m' : Mem} {h : Word} {r : List Word} {x : NeedsSt}
    {l : ConLeche.Literal} (hc : callW p n "lit_needs" [h] m = some (r, m'))
    (hS : StageR vis fe m a) (hx : NdR m x) (hh : HW h) (hne : eViewW m h ≠ []) (hg : tagW h = 8)
    (hv : a.store.view (decE h) = some (.lit l)) :
    ∃ acc, (litNeeds l x.acc).run a = .ok (acc, a) ∧ NdR m' ⟨x.seen, acc⟩ ∧
      MemFrame ndA ndC m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (litNeeds_specW p P.lit n _ h) hc
  rcases n with _ | n
  · rw [litNeedsW.eq_1] at hW; cases hW
  rw [litNeedsW.arm1] at hW
  replace hW := opt_some hW rfl; obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW; rw [litNeedsW.k_pin_at.arm1] at hW
  obtain ⟨rfl, w1, e1⟩ := pinCall P c1 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW; rw [litNeedsW.k_pin_at_2.arm1] at hW
  obtain ⟨rfl, w2, e2⟩ := pinCall P c2 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW; rw [litNeedsW.k_pin_at_3.arm1] at hW
  obtain ⟨rfl, w3, e3⟩ := pinCall P c3 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW; rw [litNeedsW.k_pin_at_4.arm1] at hW
  obtain ⟨rfl, w4, e4⟩ := pinCall P c4 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r5, m5⟩, c5, hW⟩ := hW; rw [litNeedsW.k_pin_at_5.arm1] at hW
  obtain ⟨rfl, w5, e5⟩ := pinCall P c5 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r6, m6⟩, c6, hW⟩ := hW; rw [litNeedsW.k_pin_at_6.arm1] at hW
  obtain ⟨rfl, w6, e6⟩ := pinCall P c6 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r7, m7⟩, c7, hW⟩ := hW; rw [litNeedsW.k_pin_at_7.arm1] at hW
  obtain ⟨rfl, w7, e7⟩ := pinCall P c7 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r8, m8⟩, c8, hW⟩ := hW; rw [litNeedsW.k_pin_at_8.arm1] at hW
  obtain ⟨rfl, w8, e8⟩ := pinCall P c8 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r9, m9⟩, c9, hW⟩ := hW; rw [litNeedsW.k_pin_at_9.arm1] at hW
  obtain ⟨rfl, w9, e9⟩ := pinCall P c9 hS
  replace hW := opt_some hW rfl; obtain ⟨⟨r10, m10⟩, c10, hW⟩ := hW; rw [litNeedsW.k_pin_at_10.arm1] at hW
  obtain ⟨rfl, w10, e10⟩ := pinCall P c10 hS
  have hG : litGuardNames.run a = .ok ([decI (r1.headD 0), decI (r2.headD 0), decI (r3.headD 0),
      decI (r4.headD 0), decI (r5.headD 0), decI (r6.headD 0), decI (r7.headD 0),
      decI (r8.headD 0), decI (r9.headD 0), decI (r10.headD 0)], a) := by
    simp only [litGuardNames, pinNat, pinNatZero, pinNatSucc, pinString, pinStringOfList, pinList,
      pinListNil, pinListCons, pinChar, pinCharOfNat, StateT.run_bind]
    simp only [PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC, PIN_STRING, PIN_STRING_OF_LIST, PIN_LIST,
      PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR, PIN_CHAR_OF_NAT] at *
    simp only [UInt64.reduceToNat] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, except_ok_bind]; rfl
  replace hW := opt_some hW rfl; obtain ⟨⟨q1, n1⟩, d1, hW⟩ := hW; rw [litNeedsW.k_needs_name.arm1] at hW
  obtain ⟨hx1, f1⟩ := needsName_step P d1 hx w1
  replace hW := opt_some hW rfl; obtain ⟨⟨q2, n2⟩, d2, hW⟩ := hW; rw [litNeedsW.k_needs_name_2.arm1] at hW
  obtain ⟨hx2, f2⟩ := needsName_step P d2 hx1 w2
  replace hW := opt_some hW rfl; obtain ⟨⟨q3, n3⟩, d3, hW⟩ := hW
  obtain ⟨hx3, f3⟩ := needsName_step P d3 hx2 w3
  have hf3 := f1.trans (f2.trans f3)
  have hR := hS.check.arena.base
  obtain ⟨hstr, hnat⟩ := view_lit_kind m a hR h hh (viewOK_lit hne hg) hg
  rw [← tfld_nd hf3] at hstr hnat
  by_cases hk : tfld n3 LIT (tierW h) (idxW h) 0 = 1
  · obtain ⟨str, hs⟩ := hstr hk
    rw [hv] at hs; cases hs
    rw [litNeedsW.k_needs_name_3.arm2 _ _ _ _ _ _ _ _ _ _ _ _ hk] at hW
    replace hW := opt_some hW rfl; obtain ⟨⟨q4, n4⟩, d4, hW⟩ := hW; rw [litNeedsW.k_needs_name_4.arm1] at hW
    obtain ⟨hx4, f4⟩ := needsName_step P d4 hx3 w4
    replace hW := opt_some hW rfl; obtain ⟨⟨q5, n5⟩, d5, hW⟩ := hW; rw [litNeedsW.k_needs_name_5.arm1] at hW
    obtain ⟨hx5, f5⟩ := needsName_step P d5 hx4 w5
    replace hW := opt_some hW rfl; obtain ⟨⟨q6, n6⟩, d6, hW⟩ := hW; rw [litNeedsW.k_needs_name_6.arm1] at hW
    obtain ⟨hx6, f6⟩ := needsName_step P d6 hx5 w6
    replace hW := opt_some hW rfl; obtain ⟨⟨q7, n7⟩, d7, hW⟩ := hW; rw [litNeedsW.k_needs_name_7.arm1] at hW
    obtain ⟨hx7, f7⟩ := needsName_step P d7 hx6 w7
    replace hW := opt_some hW rfl; obtain ⟨⟨q8, n8⟩, d8, hW⟩ := hW; rw [litNeedsW.k_needs_name_8.arm1] at hW
    obtain ⟨hx8, f8⟩ := needsName_step P d8 hx7 w8
    replace hW := opt_some hW rfl; obtain ⟨⟨q9, n9⟩, d9, hW⟩ := hW; rw [litNeedsW.k_needs_name_9.arm1] at hW
    obtain ⟨hx9, f9⟩ := needsName_step P d9 hx8 w9
    replace hW := opt_some hW rfl; obtain ⟨⟨q10, n10⟩, d10, hW⟩ := hW
    rw [litNeedsW.k_needs_name_10.arm1] at hW
    obtain ⟨hx10, f10⟩ := needsName_step P d10 hx9 w10
    obtain ⟨-, e⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [← e]
    refine ⟨x.acc ++ [decI (r1.headD 0), decI (r2.headD 0), decI (r3.headD 0),
      decI (r4.headD 0), decI (r5.headD 0), decI (r6.headD 0), decI (r7.headD 0),
      decI (r8.headD 0), decI (r9.headD 0), decI (r10.headD 0)], ?_, ?_, hf3.trans (f4.trans (f5.trans (f6.trans (f7.trans (f8.trans (f9.trans f10))))))⟩
    · simp only [litNeeds, StateT.run_bind, hG, except_ok_bind]; rfl
    · simpa [NeedsSt.name, nidxAppend] using hx10
  · rw [litNeedsW.k_needs_name_3.arm1 _ _ _ _ _ _ _ _ _ _ _ _ hk] at hW
    obtain ⟨-, e⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [← e]
    obtain ⟨l', hl', hns⟩ := hnat hk
    rw [hv] at hl'; cases hl'
    cases l with
    | strVal str => exact absurd rfl (hns str)
    | natVal N =>
    refine ⟨x.acc ++ [decI (r1.headD 0), decI (r2.headD 0), decI (r3.headD 0)], ?_, ?_, hf3⟩
    · simp only [litNeeds, StateT.run_bind, hG, except_ok_bind]; rfl
    · simpa [NeedsSt.name, nidxAppend] using hx3

/-! ## The memo -/

/-- An `nd_find(h, 0)` call: the probe, the memory kept. -/
theorem ndFind_call {n : Nat} {m m' : Mem} {h : Word} {r : List Word}
    (hc : callW p n "nd_find" [h, 0] m = some (r, m')) :
    m = m' ∧ r ≠ [] ∧ r = mfindG ndSch m h 0 := by
  obtain ⟨s', rfl, hs, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoFindG_spec ndSch p "nd_find" P.nd_find n _ h 0) hc
  subst hs
  exact ⟨rfl, hne, hr⟩

omit P in
/-- **The memo's insert** (`s.insert h true`): the stack kept. -/
theorem NdR.memoSet {m m' : Mem} {x : NeedsSt} (hx : NdR m x) {h : Word} (hh : HW h)
    (hs : msetG ndSch m h 0 1 = some m') :
    NdR m' ⟨x.seen.insert (decE h) true, x.acc⟩ ∧ MemFrame ndA ndC m m' := by
  have hf := msetG_frame ndSch ndSch_wf m m' h 0 1 hs
  have hseen := memoRG_set ndSch ndSch_wf bmKey (fun w : Word => w != 0) m x.seen hx.rel.seen h 0 1
    ⟨hh, rfl⟩ m' hs
  have hN : m'.arr64 NACC = m.arr64 NACC := hf.arr _ (by decide) (by decide)
  have hT : ctlW m' NTOPC = ctlW m NTOPC := hf.ctl _ (by decide)
  refine ⟨⟨⟨hseen, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [← hx.rel.acc]; simp only [naccList, hN, hT]
  · intro i hi; rw [hN]; exact hx.rel.words i (by rw [← hT]; exact hi)
  · rw [hN, hT]; exact hx.rel.room
  · rw [hf.size]; exact hx.ctl
  exact hf.mono (by simp [ndA, ndSch]) (by simp [ndC, ndSch])

/-- **The walk's last steps** (`j1`: probe again, insert): the node into the memo. -/
theorem ndJoin {n : Nat} {m m' : Mem} {h : Word} {r : List Word} {x : NeedsSt}
    (hW : needsGoW.j1 p n h m = some (r, m')) (hx : NdR m x) (hh : HW h) :
    NdR m' ⟨x.seen.insert (decE h) true, x.acc⟩ ∧ MemFrame ndA ndC m m' := by
  rw [needsGoW.j1.arm1] at hW
  replace hW := opt_some hW (needsGoW.k_nd_find_2.none _ _ _); obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  rw [needsGoW.k_nd_find_2.arm1] at hW
  obtain ⟨rfl, hne, rfl⟩ := ndFind_call P c1
  replace hW := opt_some hW (needsGoW.k_lit_needs.none _); obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
  rw [needsGoW.k_lit_needs.arm1] at hW
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨s', rfl, -, hput⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoPutG_spec ndSch p "nd_put" P.nd_put n _ h 0 1 _ _) c2
  rw [← msetG_eq ndSch m h 0 1 hne] at hput
  exact hx.memoSet hh hput

/-! ## `needs_go` -/

omit P in
theorem ndFuel_pred {f : Word} (hf0 : f ≠ 0) : ∃ k, f.toNat = k + 1 ∧ (f - 1).toNat = k := by
  have h0 : f.toNat ≠ 0 := fun h => hf0 (UInt64.toNat_inj.mp (by simpa using h))
  refine ⟨f.toNat - 1, by omega, ?_⟩
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp

/-- A view the walk records in its memo (not a leaf, not a constant). -/
def ndCompound : ENodeView → Prop
  | .bvar _ | .sort _ | .lit _ | .const _ _ => False
  | _ => True

omit P in
theorem needsGo_hit {seen : Std.HashMap EIdx Bool} {acc : List NIdx} {k : Nat} {h : EIdx}
    {v : ENodeView} (hv : a.store.view h = some v) (hc : ndCompound v) {b : Bool}
    (hs : seen[h]? = some b) : (needsGo seen acc (k + 1) h).run a = .ok ((seen, acc), a) := by
  cases v <;> simp only [ndCompound] at hc <;>
    simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs] <;> rfl

/-- The twin's walk state as a pair. -/
abbrev NdP (m : Mem) (y : Std.HashMap EIdx Bool × List NIdx) : Prop := NdR m ⟨y.1, y.2⟩

/-- **`needs_go(f, h)` refines `needsGo`** (its model at every fuel): from the stage and the walk's
state `x`, a returning run is the twin's `.ok` run from `x`, the state after related, the run
writing only the walk's state. -/
theorem needsGo_run : ∀ (n : Nat) (m m' : Mem) (f h : Word) (r : List Word) (x : NeedsSt),
    needsGoW p n m f h = some (r, m') → StageR vis fe m a → NdR m x → HW h →
    ∃ y, (needsGo x.seen x.acc f.toNat (decE h)).run a = .ok (y, a) ∧ NdP m' y ∧
      MemFrame ndA ndC m m'
  | 0, _, _, _, _, _, _, hW, _, _, _ => by rw [needsGoW.eq_1] at hW; cases hW
  | n + 1, m, m', f, h, r, x, hW, hS, hx, hh => by
    by_cases hf0 : f = 0
    · rw [needsGoW.abort1 _ _ _ _ _ hf0] at hW; cases hW
    obtain ⟨k, hk, hk1⟩ := ndFuel_pred hf0
    rw [hk]
    rw [needsGoW.arm1 _ _ _ _ _ hf0] at hW
    replace hW := opt_some hW (needsGoW.k_e_view.none _ _ _ _); obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
    obtain ⟨s1, rfl, hs1, hne, rfl⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (eView_spec p P.e_view n _ h) c1
    subst hs1
    dsimp only at hW c1 hne
    have hR := hS.check.arena.base
    obtain ⟨v, hv, hr⟩ := eViewW_ok m a hR h hne
    have hg := eViewW_head m h hne
    cases v with
    | fvar i ty =>
      obtain ⟨g1, -, hy, ety⟩ := hr
      rw [L.getD_two] at hy ety
      rw [needsGoW.k_e_view.arm4 _ _ _ _ _ _ (by rw [g1]; decide) (by rw [g1]; decide)
        (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_nd_find.eq_1 _ _ _ _ _ _ _ _)
      obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
      obtain ⟨rfl, hne2, rfl⟩ := ndFind_call P c2
      by_cases hhit : (mfindG ndSch m h 0).headD 0 ≠ 0
      · rw [needsGoW.k_nd_find.arm1 _ _ _ _ _ _ _ _ _ _ hhit] at hW
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hs := memoRG_hit ndSch bmKey _ m x.seen hx.rel.seen h 0 hne2 hhit ⟨hh, rfl⟩
        exact ⟨(x.seen, x.acc), needsGo_hit hv trivial hs, hx, MemFrame.refl _ _ _⟩
      have hmiss := memoRG_miss ndSch bmKey (fun w : Word => w != 0) m x.seen hx.rel.seen h 0
        ⟨hh, rfl⟩ hne2 (Classical.not_not.mp hhit)
      rw [needsGoW.k_nd_find.arm2 _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hhit) g1] at hW
      replace hW := opt_some hW (needsGoW.k_needs_go.none _ _ _)
      obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
      rw [needsGoW.k_needs_go.arm1] at hW
      obtain ⟨y1, e1, hy1, f1⟩ := needsGo_run n m m3 (f - 1) _ r3 x c3 hS hx hy
      obtain ⟨hz, fz⟩ := ndJoin P hW hy1 hh
      refine ⟨(y1.1.insert (decE h) true, y1.2), ?_, hz, f1.trans fz⟩
      rw [hk1, ety] at e1
      simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
      simp only [bmKey] at hmiss
      simp only [hmiss, StateT.run_bind, e1, except_ok_bind]
      rfl
    | bvar i =>
      rw [needsGoW.k_e_view.arm1 _ _ _ _ _ _ (Or.inl hr.1)] at hW
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      exact ⟨(x.seen, x.acc), by
        simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind] <;> rfl,
        hx, MemFrame.refl _ _ _⟩
    | sort u =>
      rw [needsGoW.k_e_view.arm1 _ _ _ _ _ _ (Or.inr hr.1)] at hW
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      exact ⟨(x.seen, x.acc), by
        simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind] <;> rfl,
        hx, MemFrame.refl _ _ _⟩
    | lit l =>
      have g1 : (eViewW m h).headD 0 = 8 := hr
      rw [needsGoW.k_e_view.arm2 _ _ _ _ _ _ (by rw [g1]; decide) g1] at hW
      replace hW := opt_some hW (needsGoW.k_lit_needs.none _)
      obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
      rw [needsGoW.k_lit_needs.arm1] at hW
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨acc, e1, hy, f1⟩ := litNeeds_step P c2 hS hx hh hne (by rw [← hg, g1]) hv
      refine ⟨(x.seen, acc), ?_, hy, f1⟩
      simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, e1]
      rfl
    | const c us =>
      obtain ⟨g1, hc, ec, -, -⟩ := hr
      rw [L.getD_one] at hc ec
      rw [needsGoW.k_e_view.arm3 _ _ _ _ _ _ (by rw [g1]; decide) (by rw [g1]; decide) g1] at hW
      replace hW := opt_some hW (needsGoW.k_lit_needs.none _)
      obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
      rw [needsGoW.k_lit_needs.arm1] at hW
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨hy, f1⟩ := needsName_step P c2 hx hc
      refine ⟨(x.seen, x.acc ++ [c]), ?_, by rw [← ec]; exact hy, f1⟩
      simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind] <;> rfl
    | app t b =>
      obtain ⟨g1, ht, et, hb, eb⟩ := hr
      rw [L.getD_one] at ht et; rw [L.getD_two] at hb eb
      rw [needsGoW.k_e_view.arm4 _ _ _ _ _ _ (by rw [g1]; decide) (by rw [g1]; decide)
        (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_nd_find.eq_1 _ _ _ _ _ _ _ _)
      obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
      obtain ⟨rfl, hne2, rfl⟩ := ndFind_call P c2
      by_cases hhit : (mfindG ndSch m h 0).headD 0 ≠ 0
      · rw [needsGoW.k_nd_find.arm1 _ _ _ _ _ _ _ _ _ _ hhit] at hW
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hs := memoRG_hit ndSch bmKey _ m x.seen hx.rel.seen h 0 hne2 hhit ⟨hh, rfl⟩
        exact ⟨(x.seen, x.acc), needsGo_hit hv trivial hs, hx, MemFrame.refl _ _ _⟩
      have hmiss := memoRG_miss ndSch bmKey (fun w : Word => w != 0) m x.seen hx.rel.seen h 0
        ⟨hh, rfl⟩ hne2 (Classical.not_not.mp hhit)
      simp only [bmKey] at hmiss
      rw [needsGoW.k_nd_find.arm3 _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hhit)
        (by rw [g1]; decide) (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_needs_go_2.none _ _ _ _ _)
      obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
      rw [needsGoW.k_needs_go_2.arm1] at hW
      obtain ⟨y1, e1, hy1, f1⟩ := needsGo_run n m m3 (f - 1) _ r3 x c3 hS hx ht
      have hS1 := (hS.ndFrame f1).1
      replace hW := opt_some hW (needsGoW.k_needs_go.none _ _ _)
      obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
      rw [needsGoW.k_needs_go.arm1] at hW
      obtain ⟨y2, e2, hy2, f2⟩ := needsGo_run n m3 m4 (f - 1) _ r4 ⟨y1.1, y1.2⟩ c4 hS1 hy1 hb
      obtain ⟨hz, fz⟩ := ndJoin P hW hy2 hh
      refine ⟨(y2.1.insert (decE h) true, y2.2), ?_, hz, f1.trans (f2.trans fz)⟩
      rw [hk1, et] at e1; rw [hk1, eb] at e2
      simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
      simp only [hmiss, StateT.run_bind, e1, except_ok_bind]
      simp only [e2, except_ok_bind]
      rfl
    | lam t b =>
      obtain ⟨g1, ht, et, hb, eb⟩ := hr
      rw [L.getD_one] at ht et; rw [L.getD_two] at hb eb
      rw [needsGoW.k_e_view.arm4 _ _ _ _ _ _ (by rw [g1]; decide) (by rw [g1]; decide)
        (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_nd_find.eq_1 _ _ _ _ _ _ _ _)
      obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
      obtain ⟨rfl, hne2, rfl⟩ := ndFind_call P c2
      by_cases hhit : (mfindG ndSch m h 0).headD 0 ≠ 0
      · rw [needsGoW.k_nd_find.arm1 _ _ _ _ _ _ _ _ _ _ hhit] at hW
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hs := memoRG_hit ndSch bmKey _ m x.seen hx.rel.seen h 0 hne2 hhit ⟨hh, rfl⟩
        exact ⟨(x.seen, x.acc), needsGo_hit hv trivial hs, hx, MemFrame.refl _ _ _⟩
      have hmiss := memoRG_miss ndSch bmKey (fun w : Word => w != 0) m x.seen hx.rel.seen h 0
        ⟨hh, rfl⟩ hne2 (Classical.not_not.mp hhit)
      simp only [bmKey] at hmiss
      rw [needsGoW.k_nd_find.arm3 _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hhit)
        (by rw [g1]; decide) (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_needs_go_2.none _ _ _ _ _)
      obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
      rw [needsGoW.k_needs_go_2.arm1] at hW
      obtain ⟨y1, e1, hy1, f1⟩ := needsGo_run n m m3 (f - 1) _ r3 x c3 hS hx ht
      have hS1 := (hS.ndFrame f1).1
      replace hW := opt_some hW (needsGoW.k_needs_go.none _ _ _)
      obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
      rw [needsGoW.k_needs_go.arm1] at hW
      obtain ⟨y2, e2, hy2, f2⟩ := needsGo_run n m3 m4 (f - 1) _ r4 ⟨y1.1, y1.2⟩ c4 hS1 hy1 hb
      obtain ⟨hz, fz⟩ := ndJoin P hW hy2 hh
      refine ⟨(y2.1.insert (decE h) true, y2.2), ?_, hz, f1.trans (f2.trans fz)⟩
      rw [hk1, et] at e1; rw [hk1, eb] at e2
      simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
      simp only [hmiss, StateT.run_bind, e1, except_ok_bind]
      simp only [e2, except_ok_bind]
      rfl
    | forallE t b =>
      obtain ⟨g1, ht, et, hb, eb⟩ := hr
      rw [L.getD_one] at ht et; rw [L.getD_two] at hb eb
      rw [needsGoW.k_e_view.arm4 _ _ _ _ _ _ (by rw [g1]; decide) (by rw [g1]; decide)
        (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_nd_find.eq_1 _ _ _ _ _ _ _ _)
      obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
      obtain ⟨rfl, hne2, rfl⟩ := ndFind_call P c2
      by_cases hhit : (mfindG ndSch m h 0).headD 0 ≠ 0
      · rw [needsGoW.k_nd_find.arm1 _ _ _ _ _ _ _ _ _ _ hhit] at hW
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hs := memoRG_hit ndSch bmKey _ m x.seen hx.rel.seen h 0 hne2 hhit ⟨hh, rfl⟩
        exact ⟨(x.seen, x.acc), needsGo_hit hv trivial hs, hx, MemFrame.refl _ _ _⟩
      have hmiss := memoRG_miss ndSch bmKey (fun w : Word => w != 0) m x.seen hx.rel.seen h 0
        ⟨hh, rfl⟩ hne2 (Classical.not_not.mp hhit)
      simp only [bmKey] at hmiss
      rw [needsGoW.k_nd_find.arm3 _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hhit)
        (by rw [g1]; decide) (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_needs_go_2.none _ _ _ _ _)
      obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
      rw [needsGoW.k_needs_go_2.arm1] at hW
      obtain ⟨y1, e1, hy1, f1⟩ := needsGo_run n m m3 (f - 1) _ r3 x c3 hS hx ht
      have hS1 := (hS.ndFrame f1).1
      replace hW := opt_some hW (needsGoW.k_needs_go.none _ _ _)
      obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
      rw [needsGoW.k_needs_go.arm1] at hW
      obtain ⟨y2, e2, hy2, f2⟩ := needsGo_run n m3 m4 (f - 1) _ r4 ⟨y1.1, y1.2⟩ c4 hS1 hy1 hb
      obtain ⟨hz, fz⟩ := ndJoin P hW hy2 hh
      refine ⟨(y2.1.insert (decE h) true, y2.2), ?_, hz, f1.trans (f2.trans fz)⟩
      rw [hk1, et] at e1; rw [hk1, eb] at e2
      simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
      simp only [hmiss, StateT.run_bind, e1, except_ok_bind]
      simp only [e2, except_ok_bind]
      rfl
    | letE t v b =>
      obtain ⟨g1, ht, et, hv2, ev, hb, eb⟩ := hr
      rw [L.getD_one] at ht et; rw [L.getD_two] at hv2 ev; rw [L.getD_three] at hb eb
      rw [needsGoW.k_e_view.arm4 _ _ _ _ _ _ (by rw [g1]; decide) (by rw [g1]; decide)
        (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_nd_find.eq_1 _ _ _ _ _ _ _ _)
      obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
      obtain ⟨rfl, hne2, rfl⟩ := ndFind_call P c2
      by_cases hhit : (mfindG ndSch m h 0).headD 0 ≠ 0
      · rw [needsGoW.k_nd_find.arm1 _ _ _ _ _ _ _ _ _ _ hhit] at hW
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hs := memoRG_hit ndSch bmKey _ m x.seen hx.rel.seen h 0 hne2 hhit ⟨hh, rfl⟩
        exact ⟨(x.seen, x.acc), needsGo_hit hv trivial hs, hx, MemFrame.refl _ _ _⟩
      have hmiss := memoRG_miss ndSch bmKey (fun w : Word => w != 0) m x.seen hx.rel.seen h 0
        ⟨hh, rfl⟩ hne2 (Classical.not_not.mp hhit)
      simp only [bmKey] at hmiss
      rw [needsGoW.k_nd_find.arm4 _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hhit)
        (by rw [g1]; decide) (by rw [g1]; decide) g1] at hW
      replace hW := opt_some hW (needsGoW.k_needs_go_3.none _ _ _ _ _ _)
      obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
      rw [needsGoW.k_needs_go_3.arm1] at hW
      obtain ⟨y1, e1, hy1, f1⟩ := needsGo_run n m m3 (f - 1) _ r3 x c3 hS hx ht
      have hS1 := (hS.ndFrame f1).1
      replace hW := opt_some hW (needsGoW.k_needs_go_4.none _ _ _ _ _)
      obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
      rw [needsGoW.k_needs_go_4.arm1] at hW
      obtain ⟨y2, e2, hy2, f2⟩ := needsGo_run n m3 m4 (f - 1) _ r4 ⟨y1.1, y1.2⟩ c4 hS1 hy1 hv2
      have hS2 := (hS1.ndFrame f2).1
      replace hW := opt_some hW (needsGoW.k_needs_go.none _ _ _)
      obtain ⟨⟨r5, m5⟩, c5, hW⟩ := hW
      rw [needsGoW.k_needs_go.arm1] at hW
      obtain ⟨y3, e3, hy3, f3⟩ := needsGo_run n m4 m5 (f - 1) _ r5 ⟨y2.1, y2.2⟩ c5 hS2 hy2 hb
      obtain ⟨hz, fz⟩ := ndJoin P hW hy3 hh
      refine ⟨(y3.1.insert (decE h) true, y3.2), ?_, hz, f1.trans (f2.trans (f3.trans fz))⟩
      rw [hk1, et] at e1; rw [hk1, ev] at e2; rw [hk1, eb] at e3
      simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
      simp only [hmiss, StateT.run_bind, e1, except_ok_bind]
      simp only [e2, except_ok_bind, e3]
      rfl
    | proj sn i e =>
      obtain ⟨g1, hsn, esn, -, he, ee⟩ := hr
      rw [L.getD_one] at hsn esn; rw [L.getD_three] at he ee
      rw [needsGoW.k_e_view.arm4 _ _ _ _ _ _ (by rw [g1]; decide) (by rw [g1]; decide)
        (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_nd_find.eq_1 _ _ _ _ _ _ _ _)
      obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
      obtain ⟨rfl, hne2, rfl⟩ := ndFind_call P c2
      by_cases hhit : (mfindG ndSch m h 0).headD 0 ≠ 0
      · rw [needsGoW.k_nd_find.arm1 _ _ _ _ _ _ _ _ _ _ hhit] at hW
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        have hs := memoRG_hit ndSch bmKey _ m x.seen hx.rel.seen h 0 hne2 hhit ⟨hh, rfl⟩
        exact ⟨(x.seen, x.acc), needsGo_hit hv trivial hs, hx, MemFrame.refl _ _ _⟩
      have hmiss := memoRG_miss ndSch bmKey (fun w : Word => w != 0) m x.seen hx.rel.seen h 0
        ⟨hh, rfl⟩ hne2 (Classical.not_not.mp hhit)
      simp only [bmKey] at hmiss
      rw [needsGoW.k_nd_find.arm5 _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hhit)
        (by rw [g1]; decide) (by rw [g1]; decide) (by rw [g1]; decide)] at hW
      replace hW := opt_some hW (needsGoW.k_needs_go_4.none _ _ _ _ _)
      obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
      rw [needsGoW.k_needs_go_4.arm1] at hW
      obtain ⟨hy1, f1⟩ := needsName_step P c3 hx hsn
      have hS1 := (hS.ndFrame f1).1
      replace hW := opt_some hW (needsGoW.k_needs_go.none _ _ _)
      obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
      rw [needsGoW.k_needs_go.arm1] at hW
      obtain ⟨y2, e2, hy2, f2⟩ := needsGo_run n m3 m4 (f - 1) _ r4 _ c4 hS1 hy1 he
      obtain ⟨hz, fz⟩ := ndJoin P hW hy2 hh
      refine ⟨(y2.1.insert (decE h) true, y2.2), ?_, hz, f1.trans (f2.trans fz)⟩
      rw [hk1, ee] at e2
      simp only [NeedsSt.name, esn] at e2
      simp only [needsGo, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
      simp only [hmiss, StateT.run_bind, e2, except_ok_bind]
      rfl

end steps

end L.Arena
