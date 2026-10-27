import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.IndSim
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# SumRules: `ConRon.Arena.sumRules`

The refinement theorems `sumRules_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Shared pieces -/

/-- **A real callee's `RelW` fact as a `Sim`** of its model run. -/
theorem sumSim_of_relW {α : Type} {W : Mem → List Word → Option (List Word × Mem)} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    {m : Mem} {a : AState} (h : RelW W args pre op post) (hp : pre m a) :
    Sim (W m args) op a (fun r x m' a' => post m m' a' r x) :=
  fun r m' e => h m m' a r e hp

/-- **A pointer written right after a decoded prefix** extends it by the pointer's record. -/
theorem sumDecPL_write {α : Type} (m : Mem) (f : Nat → Option α) (o j : Nat) (w v : Word)
    (acc : List α) (x : α) (hw : w.toNat = o + j) (hsz : o + j < (m.arr64 IW).size)
    (h : decPL m f o j = some acc) (hx : f v.toNat = some x) :
    decPL (m.set64 IW w v) f o (j + 1) = some (acc ++ [x]) := by
  unfold decPL at h ⊢
  rw [List.range_succ, List.mapM_append]
  have e1 : (List.range j).mapM (fun i => do f (← iwN (m.set64 IW w v) (o + i))) =
      (List.range j).mapM (fun i => do f (← iwN m (o + i))) := by
    apply mapM_congr_of
    intro i hi
    have hi' : i < j := List.mem_range.mp hi
    simp only [iwN, nat?, iwA, set64IW_get]
    rw [ite_eq_right (by omega)]
  rw [e1, h]
  simp [iwN, nat?, iwA, set64IW_get, hw, hsz, hx]

/-- **A model step that only reshapes the result words** (`K (some (r, m)) = some (f r, m)`). -/
theorem sumSim_map {β γ α : Type} {K : Option (β × Mem) → Option (γ × Mem)} {f : β → γ}
    {mo : Option (β × Mem)} {op : AM α} {a : AState} {Q : β → α → Mem → AState → Prop}
    {R : γ → α → Mem → AState → Prop} (hn : K none = none) (hs : ∀ r m, K (some (r, m)) = some (f r, m))
    (h : Sim mo op a Q) (hq : ∀ r x m a', Q r x m a' → R (f r) x m a') : Sim (K mo) op a R := by
  intro r m' e
  rcases hmo : mo with _ | ⟨r1, m1⟩
  · rw [hmo, hn] at e; cases e
  rw [hmo, hs] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨x, a', h1, h2⟩ := h r1 m1 hmo
  exact ⟨x, a', h1, hq _ _ _ _ h2⟩

/-- A pointer slice stays decoded when the pool grows (below its top) and the record decoder
only gains (as lane `decls3`'s `decPL_grow`). -/
theorem sumDecPL_grow {α : Type} {m m' : Mem} {f f' : Nat → Option α} (hg : IWGrow m m')
    (hf : ∀ q x, f q = some x → f' q = some x) :
    ∀ (c o : Nat) (xs : List α), o + c ≤ iwTop m → decPL m f o c = some xs →
    decPL m' f' o c = some xs := by
  intro c
  induction c with
  | zero => intro o xs _ h; simpa [decPL] using h
  | succ c ih =>
    intro o xs hb h
    rw [decPL_succ] at h ⊢
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨v, hv, x, hfx, xs', hxs, rfl⟩ := h
    refine ⟨v, ?_, x, hf v x hfx, xs', ih (o + 1) xs' (by omega) hxs, rfl⟩
    simp only [iwN, nat?, iwA] at hv ⊢
    rw [hg.2.2.1 o (by omega)]; exact hv

/-- A handle at the head of a slice decoded below the top, as the model reads it. -/
theorem sumRd_of_decHL_truncM {m : Mem} {o l : Word} {x : EIdx} {xs : List EIdx}
    (h : decHL (truncM m) o.toNat l.toNat = some (x :: xs)) :
    ∃ w, rdW (m.arr64 IW) o = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x ∧ o.toNat < iwTop m := by
  have hl : l.toNat = (l.toNat - 1) + 1 := by
    have := decHL_length (truncM m) h; simp at this; omega
  rw [hl] at h
  simp only [decHL, hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, List.cons.injEq] at h
  obtain ⟨y, hy, ys, -, rfl, -⟩ := h
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  split at hy
  · cases hy
    exact ⟨w, rdW_of_get? rfl hw', by assumption, rfl, hi⟩
  · cases hy

theorem sumDecHL_tail {m : Mem} {o l : Nat} {x : EIdx} {xs : List EIdx}
    (h : decHL m o (l + 1) = some (x :: xs)) : decHL m (o + 1) l = some xs := by
  simp only [decHL, hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, List.cons.injEq] at h
  obtain ⟨y, -, ys, hys, -, rfl⟩ := h
  exact hys

/-! ## `sum_rules_go`: the word model -/

/-- The memory after the rule record's eleven writes. -/
def ruleMem (m : Mem) (q ctorN nF nP rhs k eta : Word) : Mem :=
  ((((((((((m.set64 EREC q ctorN).set64 EREC (q + 1) nF).set64 EREC (q + 2) nP).set64 EREC (q + 3) 0
    ).set64 EREC (q + 4) 0).set64 EREC (q + 5) 0).set64 EREC (q + 6) 0).set64 EREC (q + 7) 0
    ).set64 EREC (q + 8) rhs).set64 EREC (q + 9) k).set64 EREC (q + 10) eta

theorem ruleMem_eq (m : Mem) (q ctorN nF nP rhs k eta : Word) :
    ruleMem m q ctorN nF nP rhs k eta = wrER m q [ctorN, nF, nP, 0, 0, 0, 0, 0, rhs, k, eta] := by
  simp only [ruleMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl,
    show q + 9 + 1 = q + 10 by ac_rfl]

/-- After the rest. -/
def rgoK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => some ([0], m3)
/-- After `erec_alloc`: the writes, then the rest (`rest`, at the written memory). -/
def rgoK2 (rest : Mem → Option (List Word × Mem)) (nP o ctorN nF rhs k eta : Word) :
    Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m2) => rgoK3 (rest ((ruleMem m2 q ctorN nF nP rhs k eta).set64 IW o q))
/-- After `rec_rule_bits`: the record. -/
def rgoK1 (rest : Mem → Option (List Word × Mem)) (nP o ctorN nF rhs : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (kr, m1) => rgoK2 rest nP o ctorN nF rhs (kr.headD 0) (kr.tail.headD 0) (erAllocW m1 11)

/-- **The model of `sum_rules_go(vis, nP, cO, cL, rO, rL, o)`** at exec fuel `n`. -/
def rgoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nP, cO, cL, rO, rL, o =>
    if cL = 0 ∨ rL = 0 then some ([0], m)
    else
      rgoK1 (fun m' => rgoW n m' vis nP (cO + 1) (cL - 1) (rO + 1) (rL - 1) (o + 1)) nP o
        (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO)))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) (rdW (m.arr64 IW) rO)
        (rrbF m [vis, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO))])

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (vis nP cO cL rO rL o ctorN nF rhs k eta q : Word)
  (kr r : List Word) (rest : Mem → Option (List Word × Mem))
theorem rgoW_nil (h : cL = 0 ∨ rL = 0) : rgoW (n + 1) m vis nP cO cL rO rL o = some ([0], m) := by
  simp [rgoW, h]
theorem rgoW_cons (h : ¬ (cL = 0 ∨ rL = 0)) : rgoW (n + 1) m vis nP cO cL rO rL o =
    rgoK1 (fun m' => rgoW n m' vis nP (cO + 1) (cL - 1) (rO + 1) (rL - 1) (o + 1)) nP o
      (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO)))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1)) (rdW (m.arr64 IW) rO)
      (rrbF m [vis, rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) cO))]) := by
  rw [rgoW, ite_eq_right h]
theorem rgoK1_some : rgoK1 rest nP o ctorN nF rhs (some (kr, m1)) =
    rgoK2 rest nP o ctorN nF rhs (kr.headD 0) (kr.tail.headD 0) (erAllocW m1 11) := rfl
theorem rgoK2_some : rgoK2 rest nP o ctorN nF rhs k eta (some (q, m2)) =
    rgoK3 (rest ((ruleMem m2 q ctorN nF nP rhs k eta).set64 IW o q)) := rfl
theorem rgoK3_some : rgoK3 (some (r, m3)) = some ([0], m3) := rfl
end arms
attribute [ind_grind] rgoW_nil rgoW_cons rgoK1_some rgoK2_some rgoK3_some

section spec
variable (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
  (hp : p.lookup "sum_rules_go" = some sumRulesGoL) (hrrb : RrbF p)
include ha hp hrrb

theorem rgoW_spec (n : Nat) : ∀ (s₀ : St) (vis nP cO cL rO rL o : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sum_rules_go" [vis, nP, cO, cL, rO, rL, o]
    ⦃fun r s' => LocEq s' s₀ ∧ rgoW n s₀.mem vis nP cO cL rO rL o = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis nP cO cL rO rL o; rw [invoke_eq _ hp]; simp only [callFn, sumRulesGoL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis nP cO cL rO rL o
    rw [invoke_eq _ hp]
    simp only [callFn, sumRulesGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        rrbF_spec p hrrb n, erecAlloc_specW p ha n, ih] <;>
      finish (gen := 20) [ruleMem, rdW_eq]

end spec

/-! ## `sum_rules`: the word model -/

/-- After the rules. -/
def rulesK2 (o k : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => some ([o, k], m2)
/-- After the allocation: the rules. -/
def rulesK1 (n : Nat) (vis nP cO cL rO rL k : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (o, m1) => rulesK2 o k (rgoW n m1 vis nP cO cL rO rL o)

/-- **The model of `sum_rules(vis, recName, nP, cO, cL, rO, rL)`** at callee fuel `n`. -/
def rulesW (n : Nat) (m : Mem) (vis nP cO cL rO rL : Word) : Option (List Word × Mem) :=
  rulesK1 n vis nP cO cL rO rL (if rL < cL then rL else cL) (allocW m (if rL < cL then rL else cL))

theorem rulesK1_some (n : Nat) (vis nP cO cL rO rL k o : Word) (m1 : Mem) :
    rulesK1 n vis nP cO cL rO rL k (some (o, m1)) = rulesK2 o k (rgoW n m1 vis nP cO cL rO rL o) := rfl
theorem rulesK2_some (o k : Word) (r : List Word) (m2 : Mem) :
    rulesK2 o k (some (r, m2)) = some ([o, k], m2) := rfl
attribute [ind_grind] rulesK1_some rulesK2_some

section spec2
variable (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
  (hg : p.lookup "sum_rules_go" = some sumRulesGoL) (hia : p.lookup "iw_alloc" = some iwAlloc)
  (hp : p.lookup "sum_rules" = some sumRulesL) (hrrb : RrbF p)
include ha hg hia hp hrrb

theorem rulesW_spec (n : Nat) (s₀ : St) (vis recName nP cO cL rO rL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "sum_rules" [vis, recName, nP, cO, cL, rO, rL]
    ⦃fun r s' => LocEq s' s₀ ∧ rulesW n s₀.mem vis nP cO cL rO rL = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, sumRulesL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      iwAlloc_specW p hia n, rgoW_spec p ha hg hrrb n] <;>
    finish (gen := 20) [rulesW]

end spec2

/-! ## The relation to the twin -/

/-- The rules' decoder: an `EREC` pointer to an 11-word rule record, below the record pool's top. -/
abbrev rlDec (m : Mem) (q : Nat) : Option IRecRule := decRule (erecP m) q

theorem sumDecRule_words {a : Array Word} {q : Nat} {c nF nP rhs k e : Word}
    (h0 : a[q]? = some c) (h1 : a[q + 1]? = some nF) (h2 : a[q + 2]? = some nP)
    (h3 : a[q + 3]? = some 0) (h8 : a[q + 8]? = some rhs) (h9 : a[q + 9]? = some k)
    (h10 : a[q + 10]? = some e) (hc : H c) (hr : H rhs) :
    decRule a q = some
      { ctor := decI c, nfields := nF.toNat, ctorParams := nP.toNat,
        fire := .plain, rhs := decI rhs, k := k != 0, eta := e != 0 } := by
  simp [decRule, nat?, hd?, bool?, h0, h1, h2, h3, h8, h9, h10, hc, hr]

theorem rlDec_set_iw (m : Mem) (o v : Word) : rlDec (m.set64 IW o v) = rlDec m := by
  have hf := set64IW_frame m o v
  unfold rlDec erecP erecTop
  rw [hf.1 EREC (by decide) (by decide), hf.2.1 129 (by decide)]

theorem sumToNat_succ {w : Word} (h : w.toNat < 2 ^ 64 - 1) : (w + 1).toNat = w.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

theorem sumToNat_pred {w : Word} (h : w ≠ 0) : (w - 1).toNat = w.toNat - 1 := by
  have : w.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp

/-- **`sum_rules_go`'s model refines `sumRules`**: the rules written after the decoded prefix
`acc` of the result slice at `q0` (its next slot `o = q0 + j`), the slots allocated above `m0`'s
top. -/
theorem rgoW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (recName : NIdx)
    (n : Nat) : ∀ (m : Mem) (a : AState) (nP cO cL rO rL o : Word) (m0 : Mem) (q0 : Word) (j : Nat)
    (acc : List IRecRule) (cs : List (IConstantVal × Nat)) (rhss : List EIdx),
    StageR dn vis fe m a → IWGrow m0 m → iwTop m0 ≤ q0.toNat → o.toNat = q0.toNat + j →
    o.toNat + min cL.toNat rL.toNat ≤ iwTop m →
    decPL m (rlDec m) q0.toNat j = some acc →
    DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m0 cs →
    DecB (fun m => decHL m rO.toNat rL.toNat) m0 rhss →
    Sim (rgoW n m vis nP cO cL rO rL o) (sumRules fe recName nP.toNat cs rhss) a
      (fun _ rules m' a' => StageR dn vis fe m' a' ∧ IWGrow m0 m' ∧
        decPL m' (rlDec m') q0.toNat (j + rules.length) = some (acc ++ rules) ∧
        rules.length = min cL.toNat rL.toNat ∧ q0.toNat + j + rules.length ≤ iwTop m') := by
  induction n with
  | zero => intro m a nP cO cL rO rL o m0 q0 j acc cs rhss _ _ _ _ _ _ _ _; exact Sim.of_none
  | succ n ih =>
  intro m a nP cO cL rO rL o m0 q0 j acc cs rhss hS hg0 hq0 ho hroom hacc hcs0 hrh0
  have hcs := DecB.grow (OMono.decPL decCN_mono _ _) hg0 hcs0
  have hrh := DecB.grow (OMono.decHL _ _) hg0 hrh0
  have hcl := decPL_length (m := truncM m) hcs
  have hrl := decHL_length (truncM m) hrh
  by_cases hz : cL = 0 ∨ rL = 0
  · rw [rgoW_nil n m vis nP cO cL rO rL o hz]
    have e : sumRules fe recName nP.toNat cs rhss = pure [] := by
      rcases hz with h | h
      · subst h; cases cs with | nil => simp [sumRules] | cons _ _ => simp at hcl
      · subst h; cases cs <;> cases rhss <;> simp_all [sumRules]
    rw [e]
    refine Sim.ret ⟨hS, hg0, by simpa using hacc, ?_, by simp; omega⟩
    rcases hz with h | h <;> simp [h]
  rw [rgoW_cons n m vis nP cO cL rO rL o hz]
  have hcL : cL ≠ 0 := fun h => hz (.inl h)
  have hrL : rL ≠ 0 := fun h => hz (.inr h)
  obtain ⟨L, hL⟩ : ∃ L, cL.toNat = L + 1 :=
    ⟨cL.toNat - 1, by have : cL.toNat ≠ 0 := fun e => hcL (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨R, hR⟩ : ∃ R, rL.toNat = R + 1 :=
    ⟨rL.toNat - 1, by have : rL.toNat ≠ 0 := fun e => hrL (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  -- the heads
  have hcs' : decPL (truncM m) (decCN (truncM m)) cO.toNat (L + 1) = some cs := by
    have := hcs; simp only [DecB, hL] at this; exact this
  cases cs with
  | nil => simp at hcl; omega
  | cons c cs =>
  cases rhss with
  | nil => simp at hrl; omega
  | cons rhs rhss =>
  obtain ⟨cv, nF⟩ := c
  obtain ⟨pv, hpv, hc⟩ := decPL_head hcs'
  have htail : DecB (fun m => decPL m (decCN m) (cO.toNat + 1) L) m0 cs := by
    have := hcs0; simp only [DecB, hL] at this; exact decPL_tail this
  obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hc
  obtain ⟨w, hw, hwv, hcO⟩ := rdW_of_iwN_truncM hpv
  obtain ⟨hI1, hE1, hIsz, -, -⟩ := hS.2
  have hcq' : iwN (truncM m) w.toNat = some cqN := by rw [hwv]; exact hcq
  obtain ⟨w2, hw2, hw2v, hpvlt⟩ := rdW_of_iwN_truncM hcq'
  have hw1 : (w + 1).toNat = pv + 1 := by rw [UInt64.toNat_add, hwv]; simp; omega
  have hnF' : iwN (truncM m) (w + 1).toNat = some nF := by rw [hw1]; exact hnF
  obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
  have hcvE : decCV (erecP m) w2.toNat = some cv := by rw [hw2v]; exact decCVp_truncM hcv
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hcvE
  have hwn' : rdW (m.arr64 EREC) w2 = wn := rdW_of_get? rfl (erecP_get hwn)
  have hrh' : decHL (truncM m) rO.toNat (R + 1) = some (rhs :: rhss) := by
    have := hrh; simp only [DecB, hR] at this; exact this
  have hrtail : DecB (fun m => decHL m (rO.toNat + 1) R) m0 rhss := by
    have := hrh0; simp only [DecB, hR] at this; exact sumDecHL_tail this
  obtain ⟨wr, hwr, hwrl, hwrd, hrO⟩ := sumRd_of_decHL_truncM (o := rO) (l := rL) (by rw [hR]; exact hrh')
  rw [hw, hw2, hw3, hwn', hwr]
  -- the twin's rule before the bits
  have hrule : ({ ctor := cv.name, nfields := nF, ctorParams := nP.toNat, fire := .plain,
                   rhs := rhs } : IRecRule).ctor = decI wn := hname
  simp only [sumRules]
  refine Sim.bindK (K := rgoK1 _ nP o wn w3 wr) rfl (fun _ _ => rfl)
    (sumSim_of_relW (rrbF_ok dn vis fe wn hwnl _ hrule) hS) fun kr x m1 a1 hQ => ?_
  obtain ⟨hS1, hg1, hx⟩ := hQ
  subst hx
  rw [rgoK1_some]
  rcases hal : erAllocW m1 11 with _ | ⟨q, m2⟩
  · exact Sim.of_none
  rw [rgoK2_some, ruleMem_eq]
  obtain ⟨hSM, hgM, hqt, htM, hget⟩ := erRec_stage hal hS1 [wn, w3, nP, 0, 0, 0, 0, 0, wr, kr.headD 0, kr.tail.headD 0] rfl
  generalize hM : wrER m2 q _ = M at hSM hgM htM hget
  -- the record decodes
  have hP : ∀ i, i < 11 → (erecP M)[q.toNat + i]? = (M.arr64 EREC)[q.toNat + i]? :=
    fun i hi => erecP_getE (by simp at htM; omega)
  have hrec : rlDec M q.toNat = some
      { ctor := decI wn, nfields := w3.toNat, ctorParams := nP.toNat,
        fire := .plain, rhs := decI wr, k := kr.headD 0 != 0, eta := kr.tail.headD 0 != 0 } := by
    have hw : ∀ i, i < 11 → (erecP M)[q.toNat + i]? =
        [wn, w3, nP, 0, 0, 0, 0, 0, wr, kr.headD 0, kr.tail.headD 0][i]? :=
      fun i hi => by rw [hP i hi, hget i (by simpa using hi)]
    exact sumDecRule_words (by simpa using hw 0 (by decide)) (hw 1 (by decide)) (hw 2 (by decide))
      (hw 3 (by decide)) (hw 8 (by decide)) (hw 9 (by decide)) (hw 10 (by decide)) hwnl hwrl
  -- the pointer written
  have hgm1M := hg1.trans hgM
  have hoT : o.toNat < iwTop m := by simp only [Nat.min_def] at hroom; split at hroom <;> omega
  have hoS : o.toNat < (M.arr64 IW).size := by
    obtain ⟨h1, -, -, -, -⟩ := hSM.2; have := hgm1M.1; omega
  have haccM : decPL M (rlDec M) q0.toNat j = some acc :=
    sumDecPL_grow hgm1M (fun q x h => ArrExt.decRule (IWGrow.erecPExtR hgm1M) h) _ _ _
      (by omega) hacc
  have hacc' := sumDecPL_write M (rlDec M) q0.toNat j o q acc _ ho (by omega) haccM hrec
  rw [← rlDec_set_iw M o q] at hacc'
  have hS' := hSM.set_iw o q
  have hg0' : IWGrow m0 (M.set64 IW o q) := (hg0.trans hgm1M).set_iw o q (by omega)
  have htop' : iwTop (M.set64 IW o q) = iwTop M := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hlt : o.toNat < 2 ^ 64 - 1 := by have := hS.lt64 (x := iwTop m) (Nat.le_refl _); omega
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := sumToNat_succ (by have := hS.lt64 (x := iwTop m) (Nat.le_refl _); omega)
  have hrO1 : (rO + 1).toNat = rO.toNat + 1 := sumToNat_succ (by have := hS.lt64 (x := iwTop m) (Nat.le_refl _); omega)
  have hcL1 : (cL - 1).toNat = L := by rw [sumToNat_pred hcL]; omega
  have hrL1 : (rL - 1).toNat = R := by rw [sumToNat_pred hrL]; omega
  refine Sim.bindK (K := rgoK3) rfl (fun _ _ => rfl)
    (ih (M.set64 IW o q) a1 nP (cO + 1) (cL - 1) (rO + 1) (rL - 1) (o + 1) m0 q0 (j + 1) _ cs rhss hS' hg0'
      hq0 (by rw [sumToNat_succ hlt]; omega)
      (by rw [sumToNat_succ hlt, hcL1, hrL1, htop']; have := hgm1M.1; simp only [Nat.min_def] at hroom ⊢
          split at hroom <;> split <;> omega)
      hacc'
      (by rw [hcO1, hcL1]; exact htail) (by rw [hrO1, hrL1]; exact hrtail))
    fun _ rules m3 a3 hQ => ?_
  obtain ⟨hS3, hg3, hd3, hl3, ht3⟩ := hQ
  refine Sim.ret ⟨hS3, hg3, ?_, ?_, ?_⟩
  · rw [← hname, hw3v, hwrd] at hd3
    simpa [Nat.add_assoc, Nat.add_comm 1] using hd3
  · simp only [List.length_cons, hl3, hcL1, hrL1, hL, hR]; omega
  · simp only [List.length_cons]; omega

/-- **`sum_rules`' model refines `sumRules`**: the rules in a fresh `IW` slice of `EREC` rule
pointers. -/
theorem rulesW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (recName : NIdx)
    (n : Nat) (m : Mem) (a : AState) (nP cO cL rO rL : Word) (cs : List (IConstantVal × Nat))
    (rhss : List EIdx) (hS : StageR dn vis fe m a)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m cs)
    (hrh : DecB (fun m => decHL m rO.toNat rL.toNat) m rhss) :
    Sim (rulesW n m vis nP cO cL rO rL) (sumRules fe recName nP.toNat cs rhss) a
      (fun r rules m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        decPL m' (rlDec m') (r.headD 0).toNat (r.tail.headD 0).toNat = some rules ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m') := by
  unfold rulesW
  generalize hk : (if rL < cL then rL else cL) = k
  have hkm : k.toNat = min cL.toNat rL.toNat := by
    subst hk; split
    · rename_i h; have := UInt64.lt_iff_toNat_lt.mp h; omega
    · rename_i h; have : ¬ rL.toNat < cL.toNat := fun e => h (UInt64.lt_iff_toNat_lt.mpr e); omega
  rcases hal : allocW m k with _ | ⟨o, m1⟩
  · exact Sim.of_none
  rw [rulesK1_some]
  obtain ⟨hS1, hg1, hot, ht1⟩ := allocW_stage hal hS
  refine sumSim_map (K := rulesK2 o k) rfl (fun _ _ => rfl)
    (rgoW_ok recName n m1 a nP cO cL rO rL o m o 0 [] cs rhss hS1 hg1 (by omega) (by simp)
      (by omega) (by simp [decPL]) hcs hrh) fun _ rules m' a' hQ => ?_
  obtain ⟨hS', hg', hd', hl', ht'⟩ := hQ
  refine ⟨hS', hg', ?_, ?_⟩
  · simpa [hkm, hl'] using hd'
  · simp only [List.headD_cons, List.tail_cons]; omega

section census
variable (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
  (hg : p.lookup "sum_rules_go" = some sumRulesGoL) (hia : p.lookup "iw_alloc" = some iwAlloc)
  (hp : p.lookup "sum_rules" = some sumRulesL) (hrrb : RrbF p)
include ha hg hia hp hrrb

/-- **`sum_rules` refines `sumRules`** (through `rec_rule_bits`' refinement, `rrbF_ok`): from the stage relation and
the constructor and right-hand-side lists decoded below the tops, the rules in a fresh `IW` slice of
pointers to `EREC` rule records (`decRule`, below the record pool's top). -/
@[refines ConRon.Arena.sumRules]
theorem sumRules_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis recName nP cO cL rO rL : Word) (cs : List (IConstantVal × Nat)) (rhss : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) s₀.mem cs)
    (hrh : DecB (fun m => decHL m rO.toNat rL.toNat) s₀.mem rhss) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "sum_rules" [vis, recName, nP, cO, cL, rO, rL]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (sumRules fe (decI recName) nP.toNat cs rhss) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (sumRules fe (decI recName) nP.toNat cs rhss) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decPL s'.mem (rlDec s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (sumRules fe (decI recName) nP.toNat cs rhss) a₀); ⊤⦄ := by
  refine triple_post (rulesW_spec p ha hg hia hp hrrb n s₀ vis recName nP cO cL rO rL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hok, hS', hg', hd, -⟩ := (rulesW_ok (decI recName) n _ a₀ nP cO cL rO rL cs rhss hS hcs hrh).run hm
  exact ⟨hl, hok, hS', hg', hd⟩

end census

end L.Ind

end
