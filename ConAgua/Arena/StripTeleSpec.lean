import ConAgua.Arena.IndView
import ConAgua.Arena.IndMaster
import ConAgua.Arena.StripTele
import ConAgua.L.ProgHas
import ConAgua.Arena.IndStubs
import ConAgua.Front.Preserve
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `strip_pis`, `strip_lams` refine `stripPis`, `stripLams` (lane `indproofs3`, helper `stubs`)

The two strippers (`StripTele.lean`, lane `whnf3`) under the stage relation, replacing the stub
contracts `stripPis_spec`/`stripLams_spec` of `IndStubs.lean`.

* **The word model** `stripTW tg n m [k, e]` (`tg` = `6` for `strip_pis`, `5` for `strip_lams`; `n`
  the L fuel of the call): the loop's model `stripGoW` at the loop's fuel, its callees by their
  models (`eViewW`, `allocW`). It does not depend on the program, so a caller's model calls it in
  place of the old `stubM "strip_pis"`, and only the caller's `vcgen` spec needs the lookups
  (`StripProg p`).
* **The relational lemma** `stripTW_pis_ok`/`stripTW_lams_ok`: a returning model run from the stage
  relation is a twin run of `stripPis k (decI e)` (`stripLams`) that keeps the twin state, with
  `KeepPost … decOLE` after — the stub contract's statement, with `stripTW` for `stubM` and no
  further hypothesis. The domains are consecutive `IW` words from the old top; on `none` the top
  is put back.
* **The write set**: `stripW_frame` (`IW` and `CTL[200]` only), for the memo frames of callers.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `e_view` of a binder -/

/-- A returning `e_view` of a `forallE` handle: the view checks hold and the words are the
binder's. -/
theorem eViewW_forall (m : Mem) (h : Word) (hg : h >>> 28 = 6) (hne : eViewW m h ≠ []) :
    viewOK m h FORALL ∧ eViewW m h = [6, tfld m FORALL (tierW h) (idxW h) 0,
      tfld m FORALL (tierW h) (idxW h) 1, 0] := by
  unfold eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, ite_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, ite_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  have n3 : ¬ h >>> 28 = 3 := by rw [hg]; decide
  have n4 : ¬ h >>> 28 = 4 := by rw [hg]; decide
  have n5 : ¬ h >>> 28 = 5 := by rw [hg]; decide
  simp only [hg, ite_true] at hne ⊢
  by_cases c : tcnt m FORALL (tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, ite_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-- A returning `e_view` of a `lam` handle. -/
theorem eViewW_lamS (m : Mem) (h : Word) (hg : h >>> 28 = 5) (hne : eViewW m h ≠ []) :
    viewOK m h LAM ∧ eViewW m h = [5, tfld m LAM (tierW h) (idxW h) 0,
      tfld m LAM (tierW h) (idxW h) 1, 0] := by
  unfold eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, ite_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, ite_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  have n3 : ¬ h >>> 28 = 3 := by rw [hg]; decide
  have n4 : ¬ h >>> 28 = 4 := by rw [hg]; decide
  simp only [hg, ite_true] at hne ⊢
  by_cases c : tcnt m LAM (tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, ite_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-! ## The word model -/

/-- **The model of the strippers' loop** (`tg` the binder tag: `6` `strip_pis`, `5` `strip_lams`)
at the loop's fuel, from count `n` and handle `h`; `k` the count wanted, `o` the pool's top at
entry. -/
def stripGoW (tg k o : Word) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | f + 1, m, n, h =>
    if n < k then
      if h >>> 28 ≠ tg then some ([0, 0, 0, 0], m.set64 CTL 200 o)
      else match eViewW m h with
        | [] => none
        | v => match allocW m 1 with
          | none => none
          | some (q, m1) =>
            stripGoW tg k o f (m1.set64 IW q (v.tail.headD 0)) (n + 1) (v.tail.tail.headD 0)
    else some ([1, o, k, h], m)

/-- **The model of `strip_pis(k, e)` (`tg = 6`) and `strip_lams(k, e)` (`tg = 5`)** at the call's
L fuel. -/
def stripTW (tg : Word) : Nat → Mem → List Word → Option (List Word × Mem)
  | 0, _, _ => none
  | f + 1, m, args => stripGoW tg (args.headD 0) (rdW (m.arr64 CTL) 200) (f + 1) m 0 (args.tail.headD 0)

section arms
variable (tg k o : Word) (f : Nat) (m m1 : Mem) (n h q : Word)

theorem stripGoW_ge (hn : ¬ n < k) : stripGoW tg k o (f + 1) m n h = some ([1, o, k, h], m) := by
  simp only [stripGoW, hn, ite_false]

theorem stripGoW_tag (hn : n < k) (hg : h >>> 28 ≠ tg) :
    stripGoW tg k o (f + 1) m n h = some ([0, 0, 0, 0], m.set64 CTL 200 o) := by
  simp only [stripGoW, ite_eq_left hn, ite_eq_left hg]

theorem stripGoW_step (hn : n < k) (hg : ¬ h >>> 28 ≠ tg) (hv : eViewW m h ≠ [])
    (ha : allocW m 1 = some (q, m1)) :
    stripGoW tg k o (f + 1) m n h = stripGoW tg k o f (m1.set64 IW q ((eViewW m h).tail.headD 0))
      (n + 1) ((eViewW m h).tail.tail.headD 0) := by
  simp only [stripGoW, ite_eq_left hn, ite_eq_right hg]
  repeat' split
  all_goals simp_all

end arms

/-! ## The `vcgen` specs -/

/-- The strippers' program: the two functions and their callees. -/
def stripProg : Prog :=
  [("strip_pis", stripPisL), ("strip_lams", stripLamsL), ("e_view", eView), ("iw_alloc", iwAlloc)]

/-- The program bundle of the strippers. -/
def StripProg (p : Prog) : Prop := ProgHas p stripProg

theorem stripPisLoop_spec (p : Prog) (hp : StripProg p) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f stripPisLoop
    ⦃fun r s' => r ≠ .brk ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 2 = s₀.loc 2 ∧
      stripGoW 6 (s₀.loc 0) (s₀.loc 2) f s₀.mem (s₀.loc 3) (s₀.loc 4) =
        some (r.retOr [1, s'.loc 2, s'.loc 0, s'.loc 4], s'.mem); ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := stripPisLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih,
        eView_spec p (hp.get "e_view") f, iwAlloc_specW p (hp.get "iw_alloc") f] <;>
      finish [stripGoW_ge, stripGoW_tag, stripGoW_step]

theorem stripLamsLoop_spec (p : Prog) (hp : StripProg p) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f stripLamsLoop
    ⦃fun r s' => r ≠ .brk ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 2 = s₀.loc 2 ∧
      stripGoW 5 (s₀.loc 0) (s₀.loc 2) f s₀.mem (s₀.loc 3) (s₀.loc 4) =
        some (r.retOr [1, s'.loc 2, s'.loc 0, s'.loc 4], s'.mem); ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := stripLamsLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih,
        eView_spec p (hp.get "e_view") f, iwAlloc_specW p (hp.get "iw_alloc") f] <;>
      finish [stripGoW_ge, stripGoW_tag, stripGoW_step]

theorem stripTW_succ (tg : Word) (f : Nat) (m : Mem) (k e : Word) :
    stripTW tg (f + 1) m [k, e] = stripGoW tg k (rdW (m.arr64 CTL) 200) (f + 1) m 0 e := rfl

/-- **`strip_pis(k, e)` returns its model's words.** -/
theorem stripPis_specW (p : Prog) (hp : StripProg p) (n : Nat) (s₀ : St) (k e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "strip_pis" [k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ stripTW 6 n s₀.mem [k, e] = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "strip_pis")]
  simp only [callFn, stripPisL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        fun s => Triple.step_exec (stripPisLoop_spec p hp (n + 1) s)] <;>
      finish [stripTW_succ]

/-- **`strip_lams(k, e)` returns its model's words.** -/
theorem stripLams_specW (p : Prog) (hp : StripProg p) (n : Nat) (s₀ : St) (k e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "strip_lams" [k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ stripTW 5 n s₀.mem [k, e] = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "strip_lams")]
  simp only [callFn, stripLamsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        fun s => Triple.step_exec (stripLamsLoop_spec p hp (n + 1) s)] <;>
      finish [stripTW_succ]

/-! ## The relational lemmas -/

theorem viewBind_run_s (h : EIdx) (a : AState) :
    (viewBind h).run a = .ok (a.store.viewBind h, a) := rfl


theorem StageR.set_iw {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR dn vis fe m a) (p x : Word) : StageR dn vis fe (m.set64 IW p x) a := by
  have hf := set64IW_frame m p x
  have hC : (m.set64 IW p x).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hE : (m.set64 IW p x).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨CheckR.frame_iw hf hS.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.2
  have hI := hf.2.2.1 IW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [iwTop, hC, hI]; exact h1
  · simp only [erTop, hC, hE]; exact h2
  · rw [hI]; exact h3
  · rw [hE]; exact h4
  · rw [hC]; exact h5
/-- Putting the pool's top back to `o ≤` the top keeps the stage relation. -/
theorem StageR.set_top {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hS : StageR dn vis fe m a) (o : Word) (ho : o.toNat ≤ iwTop m) :
    StageR dn vis fe (m.set64 CTL 200 o) a ∧ iwTop (m.set64 CTL 200 o) = o.toNat := by
  have hf : MemFrame [IW] [200] m (m.set64 CTL 200 o) :=
    MemFrame.mono (MemFrame.setCtl m 200 o) (by simp) (by simp)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.2
  have ht : iwTop (m.set64 CTL 200 o) = o.toNat := by
    simp only [iwTop, rdW_set64]
    have h200 : UInt64.toNat 200 < (m.arr64 CTL).size := by simpa using h5
    rw [ite_eq_left ⟨trivial, trivial, h200⟩]
  have h129 : rdW ((m.set64 CTL 200 o).arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : (m.set64 CTL 200 o).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  refine ⟨⟨CheckR.frame_iw hf hS.1, ?_, ?_, ?_, ?_, ?_⟩, ht⟩
  · rw [ht, hf.2.2.1 IW]; omega
  · simp only [erTop, h129, hE]; exact h2
  · rw [hf.2.2.1 IW]; exact h3
  · rw [hE]; exact h4
  · rw [hf.2.2.1 CTL]; exact h5

/-- One step of the twin's strippers (`stripPis`/`stripLams` at `k + 1`, tag `T`, the rest `rec`). -/
def stripStepT (T : UInt32) (rec : EIdx → AM (Option (List EIdx × EIdx))) (h : EIdx) :
    AM (Option (List EIdx × EIdx)) := do
  if h.tag == T then
    match ← viewBind h with
    | none => failDanglingE
    | some (ty, b) => do
      match ← rec b with
      | some p => pure (some (ty :: p.1, p.2))
      | none => pure none
  else pure none

theorem stripPis_succ (k : Nat) (h : EIdx) : stripPis (k + 1) h = stripStepT ETag.forallE (stripPis k) h := rfl
theorem stripLams_succ (k : Nat) (h : EIdx) : stripLams (k + 1) h = stripStepT ETag.lam (stripLams k) h := rfl

/-- What the loop's result words say: `none` puts the top back to `o`; `some (l, b)` is the slice
`(o, k)`, read from count `n` on, and the body. -/
def StripRes (o k n : Word) (m' : Mem) (r : List Word) : Option (List EIdx × EIdx) → Prop
  | none => r.headD 0 = 0 ∧ iwTop m' = o.toNat
  | some (l, b) => r = [1, o, k, r.getD 3 0] ∧
      decHL m' (o.toNat + n.toNat) (k.toNat - n.toNat) = some l ∧ H (r.getD 3 0) ∧
      decE (r.getD 3 0) = b ∧ iwTop m' = o.toNat + k.toNat

theorem tag_beq_iff (w : Word) (hw : H w) (t : Word) (ht : t.toNat < 16) :
    ((decE w).tag == t.toUInt32) = decide (w >>> 28 = t) := by
  rw [decE_tag w hw]
  have key : (w >>> 28).toNat = w.toNat / 268435456 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have hlt : (w >>> 28).toNat < 16 := by simp only [H] at hw; rw [key]; omega
  by_cases h : w >>> 28 = t
  · simp [h]
  · simp only [h, decide_false]
    apply beq_false_of_ne
    intro h2
    apply h
    apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat h2
    rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32] at this
    omega

section loop
variable (tg : Word) (T : UInt32)
  (tw : Nat → EIdx → AM (Option (List EIdx × EIdx)))
  (h0 : ∀ h, tw 0 h = pure (some ([], h)))
  (hs : ∀ j h, tw (j + 1) h = stripStepT T (tw j) h)
  (hT : ∀ w : Word, H w → ((decE w).tag == T) = decide (w >>> 28 = tg))
  (hvb : ∀ (m : Mem) (a : AState) (w : Word), ArenaR m a → H w → eViewW m w ≠ [] → w >>> 28 = tg →
    (viewBind (decE w)).run a = .ok (some (decE ((eViewW m w).tail.headD 0),
      decE ((eViewW m w).tail.tail.headD 0)), a) ∧
    H ((eViewW m w).tail.headD 0) ∧ H ((eViewW m w).tail.tail.headD 0))
  (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k o : Word) (a : AState)
include h0 hs hT hvb

/-- **The loop's model refines the twin's stripper** from count `n`: the twin keeps its state,
the stage relation holds after, only `IW` and `CTL[200]` are written, the pool below the current
top is kept, and the words say the twin's result (`StripRes`). -/
theorem stripGoW_ok : ∀ (f : Nat) (m m' : Mem) (n h : Word) (r : List Word),
    stripGoW tg k o f m n h = some (r, m') → StageR dn vis fe m a → H h → n ≤ k →
    iwTop m = o.toNat + n.toNat →
    ∃ x, (tw (k.toNat - n.toNat) (decE h)).run a = .ok (x, a) ∧ StageR dn vis fe m' a ∧
      MemFrame [IW] [200] m m' ∧ (∀ i < iwTop m, (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?) ∧
      StripRes o k n m' r x := by
  intro f
  induction f with
  | zero => intro m m' n h r hm; simp [stripGoW] at hm
  | succ f ih =>
  intro m m' n h r hm hS hh hnk htop
  by_cases hn' : ¬ n < k
  · have hn := hn'
    rw [stripGoW_ge tg k o f m n h hn] at hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    have hk : n = k := by
      have := UInt64.le_iff_toNat_le.mp hnk
      have : ¬ n.toNat < k.toNat := fun h => hn (UInt64.lt_iff_toNat_lt.mpr h)
      exact UInt64.toNat_inj.mp (by omega)
    subst hk
    refine ⟨some ([], decE h), by rw [Nat.sub_self, h0]; rfl, hS, MemFrame.refl _ _ _,
      fun _ _ => rfl, rfl, ?_, hh, rfl, by omega⟩
    simp [decHL, hslice?]
  have hn : n < k := Classical.not_not.mp hn'
  have hnk' : n.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp hn
  have hj : k.toNat - n.toNat = (k.toNat - (n + 1).toNat) + 1 := by
    rw [UInt64.toNat_add]; simp; rw [Nat.mod_eq_of_lt (by have := k.toNat_lt; omega)]; omega
  rw [hj, hs]
  by_cases hg : h >>> 28 ≠ tg
  · rw [stripGoW_tag tg k o f m n h hn hg] at hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨hS', ht'⟩ := hS.set_top o (by omega)
    have hf : MemFrame [IW] [200] m (m.set64 CTL 200 o) :=
      MemFrame.mono (MemFrame.setCtl m 200 o) (by simp) (by simp)
    refine ⟨none, ?_, hS', hf, fun i _ => by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)], rfl, ht'⟩
    simp only [stripStepT, hT h hh, decide_eq_true_iff, hg, ite_false]; rfl
  have hg' : h >>> 28 = tg := Classical.not_not.mp hg
  by_cases hv : eViewW m h = []
  · simp [stripGoW, hn, hg, hv] at hm
  cases ha : allocW m 1 with
  | none => simp [stripGoW, hn, hg, ha] at hm
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  rw [stripGoW_step tg k o f m m1 n h q hn hg hv ha] at hm
  obtain ⟨hvr, hty, hb⟩ := hvb m a h hS.1.arena.1 hh hv hg'
  obtain ⟨hS1, hgr1, hq, ht1⟩ := allocW_stage ha hS
  obtain ⟨-, rfl, hroom⟩ := allocW_facts ha hS.2.2.2.1
  have hS2 := hS1.set_iw q ((eViewW m h).tail.headD 0)
  have ht2 : iwTop ((allocMem m 1).set64 IW q ((eViewW m h).tail.headD 0)) = iwTop m + 1 := by
    have e : iwTop ((allocMem m 1).set64 IW q ((eViewW m h).tail.headD 0)) = iwTop (allocMem m 1) := by
      simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    rw [e, ht1]; rfl
  have hn1 : (n + 1).toNat = n.toNat + 1 := by
    have := k.toNat_lt
    rw [UInt64.toNat_add]; simp; first | omega | rw [Nat.mod_eq_of_lt (by omega)]
  obtain ⟨x', hrun', hS', hf', hlow', hres'⟩ := ih _ m' (n + 1) ((eViewW m h).tail.tail.headD 0) r hm hS2 hb
    (UInt64.le_iff_toNat_le.mpr (by omega)) (by rw [ht2, htop, hn1]; omega)
  have hfr : MemFrame [IW] [200] m m' :=
    ((allocMem_frame m 1).trans (set64IW_frame _ q ((eViewW m h).tail.headD 0))).trans hf'
  have hq' : q.toNat = iwTop m := hq
  have hlowm : ∀ i < iwTop m, (m'.arr64 IW)[i]? = (m.arr64 IW)[i]? := by
    intro i hi
    rw [hlow' i (by omega), set64IW_get, ite_eq_right (by omega), allocMem_IW]
  have hat : (m'.arr64 IW)[q.toNat]? = some ((eViewW m h).tail.headD 0) := by
    rw [hlow' _ (by omega), set64IW_get, ite_eq_left ⟨rfl, by rw [allocMem_IW]; have := hroom; simp at this; omega⟩]
  refine ⟨match x' with | some p => some (decE ((eViewW m h).tail.headD 0) :: p.1, p.2) | none => none, ?_, hS', hfr, hlowm, ?_⟩
  · simp only [stripStepT, hT h hh, decide_eq_true_iff, hg', ite_true, StateT.run_bind, hvr,
      except_ok_bind]
    simp only [hrun']
    cases x' <;> rfl
  · cases x' with
    | none => exact hres'
    | some p =>
      obtain ⟨l, bb⟩ := p
      obtain ⟨hr, hdec, hH, hbd, htop'⟩ := hres'
      refine ⟨hr, ?_, hH, hbd, htop'⟩
      have hkn : k.toNat - n.toNat = (k.toNat - (n.toNat + 1)) + 1 := by omega
      rw [hkn, decHL, hslice?_succ]
      rw [hn1] at hdec
      simp only [decHL] at hdec
      have hon : o.toNat + n.toNat = q.toNat := by omega
      rw [hon, show q.toNat + 1 = o.toNat + (n.toNat + 1) by omega, hdec]
      simp only [hd?, iwA, hat, Option.bind_eq_bind, Option.bind]
      rw [ite_eq_left hty]; rfl

end loop

/-- **A model run as a twin run**: a returning run of the model `W` on `args` from a memory with
`pre` is a successful run of `op` with `post` after (the shape of `IndStubs`' `RelAM`, for a real
function's word model). -/
def RelW {α : Type} (W : Mem → List Word → Option (List Word × Mem)) (args : List Word)
    (pre : Mem → AState → Prop) (op : AM α)
    (post : Mem → Mem → AState → List Word → α → Prop) : Prop :=
  ∀ (m m' : Mem) (a : AState) (r : List Word), W m args = some (r, m') → pre m a →
    ∃ x a', op.run a = .ok (x, a') ∧ post m m' a' r x

theorem stripTW_ok (tg : Word) (T : UInt32)
    (tw : Nat → EIdx → AM (Option (List EIdx × EIdx)))
    (h0 : ∀ h, tw 0 h = pure (some ([], h)))
    (hs : ∀ j h, tw (j + 1) h = stripStepT T (tw j) h)
    (hT : ∀ w : Word, H w → ((decE w).tag == T) = decide (w >>> 28 = tg))
    (hvb : ∀ (m : Mem) (a : AState) (w : Word), ArenaR m a → H w → eViewW m w ≠ [] → w >>> 28 = tg →
      (viewBind (decE w)).run a = .ok (some (decE ((eViewW m w).tail.headD 0),
        decE ((eViewW m w).tail.tail.headD 0)), a) ∧
      H ((eViewW m w).tail.headD 0) ∧ H ((eViewW m w).tail.tail.headD 0))
    (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k e : Word) (he : H e) :
    RelW (stripTW tg n) [k, e] (StageR dn vis fe) (tw k.toNat (decI e)) (KeepPost dn vis fe decOLE) := by
  intro m m' a r hw hS
  match n, hw with
  | f + 1, hw =>
  rw [stripTW_succ] at hw
  obtain ⟨x, hrun, hS', hf, hlow, hres⟩ := stripGoW_ok tg T tw h0 hs hT hvb dn vis fe k _ a (f + 1)
    m m' 0 e r hw hS he (UInt64.le_iff_toNat_le.mpr (by simp)) (by simp [iwTop])
  have ht0 : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
  have h129 : erTop m' = erTop m := by simp only [erTop]; rw [hf.2.1 129 (by simp)]
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  have hgrow : iwTop m ≤ iwTop m' → IWGrow m m' := fun h =>
    ⟨h, by rw [h129]; exact Nat.le_refl _, hlow, fun i _ => by rw [hE]⟩
  simp only [UInt64.toNat_zero, Nat.sub_zero] at hrun
  refine ⟨x, a, hrun, hS', ?_⟩
  cases x with
  | none =>
    obtain ⟨h0', ht⟩ := hres
    exact ⟨hgrow (by omega), h0'⟩
  | some p =>
    obtain ⟨l, b⟩ := p
    obtain ⟨hr, hdec, hH, hb, ht⟩ := hres
    refine ⟨hgrow (by omega), ?_⟩
    rw [hr]
    refine ⟨rfl, ⟨?_, ?_⟩, ?_, ?_⟩
    · simpa using hdec
    · simp only [List.getD_cons_succ, List.getD_cons_zero, ht]; omega
    · exact hH
    · exact hb

/-- **`strip_pis` refines `stripPis`** (the model; the census theorem is `stripPis_refines`). -/
theorem stripTW_pis_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (k e : Word) (he : H e) :
    RelW (stripTW 6 n) [k, e] (StageR dn vis fe) (stripPis k.toNat (decI e))
      (KeepPost dn vis fe decOLE) :=
  stripTW_ok 6 ETag.forallE stripPis (fun _ => rfl) stripPis_succ
    (fun w hw => tag_beq_iff w hw 6 (by decide))
    (fun m a w hR hw hne hg => by
      obtain ⟨hvok, hew⟩ := eViewW_forall m w hg hne
      obtain ⟨-, h1, h2⟩ := view_forall m a hR w hw hvok hg
      have hvb := viewBind_forall m a hR w hw hvok hg
      rw [hew]
      exact ⟨by rw [viewBind_run_s, hvb]; rfl, h1, h2⟩)
    n dn vis fe k e he

/-- **`strip_lams` refines `stripLams`** (the model). -/
theorem stripTW_lams_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (k e : Word) (he : H e) :
    RelW (stripTW 5 n) [k, e] (StageR dn vis fe) (stripLams k.toNat (decI e))
      (KeepPost dn vis fe decOLE) :=
  stripTW_ok 5 ETag.lam stripLams (fun _ => rfl) stripLams_succ
    (fun w hw => tag_beq_iff w hw 5 (by decide))
    (fun m a w hR hw hne hg => by
      obtain ⟨hvok, hew⟩ := eViewW_lamS m w hg hne
      obtain ⟨-, h1, h2⟩ := view_lam m a hR w hw hvok hg
      have hvb := viewBind_lam m a hR w hw hvok hg
      rw [hew]
      exact ⟨by rw [viewBind_run_s, hvb]; rfl, h1, h2⟩)
    n dn vis fe k e he

/-! ## The fuel-free model

A returning loop ran at most `k` iterations, so its result does not depend on the fuel beyond
that: `stripF tg m [k, e]` is the model at fuel `k + 2`, and it is what every call returns,
whatever its fuel. Callers' models call `stripF` (no fuel, no program). -/

theorem stripGoW_fuel (tg k o : Word) : ∀ (f : Nat) (m : Mem) (n h : Word) (x : List Word × Mem),
    stripGoW tg k o f m n h = some x → n ≤ k → ∀ f', k.toNat - n.toNat < f' →
    stripGoW tg k o f' m n h = some x := by
  intro f
  induction f with
  | zero => intro m n h x hm; simp [stripGoW] at hm
  | succ f ih =>
  intro m n h x hm hnk f' hf'
  match f', hf' with
  | f'' + 1, hf' =>
  by_cases hn : n < k
  · have hnk' : n.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp hn
    by_cases hg : h >>> 28 ≠ tg
    · rw [stripGoW_tag tg k o f m n h hn hg] at hm; rw [stripGoW_tag tg k o f'' m n h hn hg, hm]
    by_cases hv : eViewW m h = []
    · simp [stripGoW, hn, hg, hv] at hm
    cases ha : allocW m 1 with
    | none => simp [stripGoW, hn, hg, ha] at hm
    | some qm =>
      obtain ⟨q, m1⟩ := qm
      rw [stripGoW_step tg k o f m m1 n h q hn hg hv ha] at hm
      rw [stripGoW_step tg k o f'' m m1 n h q hn hg hv ha]
      have hn1 : (n + 1).toNat = n.toNat + 1 := by
        have := k.toNat_lt
        rw [UInt64.toNat_add]; simp; first | omega | rw [Nat.mod_eq_of_lt (by omega)]
      exact ih _ _ _ _ hm (UInt64.le_iff_toNat_le.mpr (by omega)) _ (by omega)
  · rw [stripGoW_ge tg k o f m n h hn] at hm; rw [stripGoW_ge tg k o f'' m n h hn, hm]

/-- **The fuel-free model of the strippers.** -/
def stripF (tg : Word) (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  stripTW tg ((args.headD 0).toNat + 2) m args

theorem stripF_of_TW {tg : Word} {n : Nat} {m : Mem} {k e : Word} {x : List Word × Mem}
    (h : stripTW tg n m [k, e] = some x) : stripF tg m [k, e] = some x := by
  match n, h with
  | f + 1, h =>
    rw [stripTW_succ] at h
    exact stripGoW_fuel tg k _ (f + 1) m 0 e x h (UInt64.le_iff_toNat_le.mpr (by simp)) _ (by simp; omega)

/-- `strip_pis(k, e)` returns `stripF 6`. -/
theorem stripPis_specF (p : Prog) (hp : StripProg p) (n : Nat) (s₀ : St) (k e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "strip_pis" [k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ stripF 6 s₀.mem [k, e] = some (r, s'.mem); ⊤⦄ :=
  triple_post (stripPis_specW p hp n s₀ k e) fun _ _ h => ⟨h.1, stripF_of_TW h.2⟩

/-- `strip_lams(k, e)` returns `stripF 5`. -/
theorem stripLams_specF (p : Prog) (hp : StripProg p) (n : Nat) (s₀ : St) (k e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "strip_lams" [k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ stripF 5 s₀.mem [k, e] = some (r, s'.mem); ⊤⦄ :=
  triple_post (stripLams_specW p hp n s₀ k e) fun _ _ h => ⟨h.1, stripF_of_TW h.2⟩

/-- **`strip_pis` refines `stripPis`**, the fuel-free model (replaces `IndStubs.stripPis_spec`). -/
theorem stripF_pis_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (k e : Word) (he : H e) :
    RelW (stripF 6) [k, e] (StageR dn vis fe) (stripPis k.toNat (decI e))
      (KeepPost dn vis fe decOLE) :=
  stripTW_pis_ok _ dn vis fe k e he

/-- **`strip_lams` refines `stripLams`**, the fuel-free model (replaces `IndStubs.stripLams_spec`). -/
theorem stripF_lams_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (k e : Word) (he : H e) :
    RelW (stripF 5) [k, e] (StageR dn vis fe) (stripLams k.toNat (decI e))
      (KeepPost dn vis fe decOLE) :=
  stripTW_lams_ok _ dn vis fe k e he

/-! ## The census theorems -/

/-- **`strip_pis` refines `stripPis`** under the stage relation, at every L fuel. -/
@[refines ConRon.Arena.stripPis]
theorem stripPis_refines (p : Prog) (hp : StripProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (k e : Word) (he : H e) :
    RefAM p "strip_pis" [k, e] (StageR dn vis fe) (stripPis k.toNat (decI e))
      (KeepPost dn vis fe decOLE) := by
  intro n s₀ a₀ hS
  refine triple_post (stripPis_specW p hp n s₀ k e) ?_
  rintro r s' ⟨hloc, hw⟩
  obtain ⟨x, a', hrun, hpost⟩ := stripTW_pis_ok n dn vis fe k e he _ _ _ _ hw hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hloc, hok, by rw [hst, hres]; exact hpost⟩

/-- **`strip_lams` refines `stripLams`** under the stage relation, at every L fuel. -/
@[refines ConRon.Arena.stripLams]
theorem stripLams_refines (p : Prog) (hp : StripProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (k e : Word) (he : H e) :
    RefAM p "strip_lams" [k, e] (StageR dn vis fe) (stripLams k.toNat (decI e))
      (KeepPost dn vis fe decOLE) := by
  intro n s₀ a₀ hS
  refine triple_post (stripLams_specW p hp n s₀ k e) ?_
  rintro r s' ⟨hloc, hw⟩
  obtain ⟨x, a', hrun, hpost⟩ := stripTW_lams_ok n dn vis fe k e he _ _ _ _ hw hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hloc, hok, by rw [hst, hres]; exact hpost⟩

/-- A call of `strip_pis` meets its model (for callers whose models use `callW`). -/
theorem stripF_of_callW {p : Prog} (hp : StripProg p) {n : Nat} {k e : Word} {m m' : Mem}
    {r : List Word} (hc : callW p n "strip_pis" [k, e] m = some (r, m')) :
    stripF 6 m [k, e] = some (r, m') := by
  obtain ⟨s', rfl, -, hs⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (stripPis_specF p hp n _ k e) hc
  exact hs

/-! ## The write set -/

theorem stripGoW_frame (tg k o : Word) : ∀ (f : Nat) (m m' : Mem) (n h : Word) (r : List Word),
    stripGoW tg k o f m n h = some (r, m') → MemFrame [IW] [200] m m' := by
  intro f
  induction f with
  | zero => intro m m' n h r hm; simp [stripGoW] at hm
  | succ f ih =>
  intro m m' n h r hm
  by_cases hn : n < k
  · by_cases hg : h >>> 28 ≠ tg
    · rw [stripGoW_tag tg k o f m n h hn hg] at hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨-, rfl⟩ := hm
      exact MemFrame.mono (MemFrame.setCtl m 200 o) (by simp) (by simp)
    by_cases hv : eViewW m h = []
    · simp [stripGoW, hn, hg, hv] at hm
    cases ha : allocW m 1 with
    | none => simp [stripGoW, hn, hg, ha] at hm
    | some qm =>
      obtain ⟨q, m1⟩ := qm
      rw [stripGoW_step tg k o f m m1 n h q hn hg hv ha] at hm
      have hm1 : MemFrame [IW] [200] m m1 := by
        simp only [allocW] at ha
        split at ha
        · cases ha
        split at ha
        · cases ha
        simp only [Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨-, rfl⟩ := ha
        exact allocMem_frame m 1
      exact (hm1.trans (set64IW_frame _ _ _)).trans (ih _ _ _ _ _ hm)
  · rw [stripGoW_ge tg k o f m n h hn] at hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨-, rfl⟩ := hm
    exact MemFrame.refl _ _ _

/-- **The strippers write `IW` and `CTL[200]` only.** -/
theorem stripF_frame {tg : Word} {m m' : Mem} {args r : List Word}
    (h : stripF tg m args = some (r, m')) : MemFrame [IW] [200] m m' :=
  stripGoW_frame _ _ _ _ _ _ _ _ _ h

end L.Ind
