module

import ConAgua.Front.IndApplyRefine
import ConAgua.Arena.IndPartsSpec.BlockSplitRecs
public import ConAgua.Arena.RecSim
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.RecClassSpec.CloseLams
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Checker.Entry
public import ConAgua.Front.IndApplySpec
import all ConAgua.Front.IndApply
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# `ind_params_ok(nP, off, len)` refines `indParamsOk` (lane `indproofs4`)

`L.Checker.indParamsOkL` (`Checker/Entry.lean`) walks the block's `EREC` slice of constant records
(`decEBlk`): a type former's telescope to a sort (`pi_sort_tele_len`, the front's `sortTeleW`,
refining `piSortTeleLen?`: `sortTeleW_ok`) has at least `nP` binders, a constructor declares
exactly `nP` parameters. The loop is a named block (`ipoLoop`) with a recursive model (`ipoW`);
everything reads only, so the memory and the twin's state are unchanged.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The loop as a named block -/

/-- The loop of `indParamsOkL`, named for its spec. -/
-- con-ron: none — `indParamsOkL`'s own loop (`rfl`), a named block for the proof
def ipoLoop : Stmt := lblk (np, o, l, j, p, k, ok, n) {
  for j < l {
    p := EREC⦃o + j⦄;
    k := EREC⦃p⦄;
    if k == 3 {
      (ok, n) := call pi_sort_tele_len(⟪CWF⟫, EREC⦃p + 4⦄);
      if ok != 0 && n < np { return 0 }
    };
    if k == 4 {
      if EREC⦃p + 5⦄ != np { return 0 }
    }
  }
}

/-- `indParamsOkL`, with its loop spliced from `ipoLoop`. -/
-- con-ron: none — `indParamsOkL` itself (`rfl`), its loop a named block for the proof
@[no_expose] def indParamsOkL' : FunDecl := lfn (np, o, l) locals (j, p, k, ok, n) {
  j := 0;
  ⟪ipoLoop⟫;
  return 1
}

theorem indParamsOkL_eq : L.Checker.indParamsOkL = indParamsOkL' := by rfl

/-! ## The model -/

/-- The constructor check, then the next record. -/
def ipoK (m : Mem) (np pw : Word) (rest : Option Sig) : Option Sig :=
  if rdW (m.arr64 EREC) pw = 4 ∧ rdW (m.arr64 EREC) (pw + 5) ≠ np then some (.ret [0]) else rest

/-- After `pi_sort_tele_len`. -/
def ipoT (m : Mem) (np pw : Word) (rest : Option Sig) : Option (Word × Word) → Option Sig
  | none => none
  | some (ok, n) => if ok ≠ 0 ∧ n < np then some (.ret [0]) else ipoK m np pw rest

/-- **The model of `ind_params_ok`' loop** at L fuel `k`, from record `j`: its signal. -/
def ipoW : Nat → Mem → Word → Word → Word → Word → Option Sig
  | 0, _, _, _, _, _ => none
  | k + 1, m, np, o, l, j =>
    if j < l then
      if rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j)) = 3 then
        ipoT m np (rdW (m.arr64 EREC) (o + j)) (ipoW k m np o l (j + 1))
          (L.Front.Ind.sortTeleW k m CWF (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j) + 4)))
      else ipoK m np (rdW (m.arr64 EREC) (o + j)) (ipoW k m np o l (j + 1))
    else some .normal

section arms
variable (k : Nat) (m : Mem) (np o l j pw ok n : Word) (rest : Option Sig)
theorem ipoK_bad (h : rdW (m.arr64 EREC) pw = 4 ∧ rdW (m.arr64 EREC) (pw + 5) ≠ np) :
    ipoK m np pw rest = some (.ret [0]) := by simp only [ipoK]; rw [ite_eq_left h]
theorem ipoK_ok (h : ¬ (rdW (m.arr64 EREC) pw = 4 ∧ rdW (m.arr64 EREC) (pw + 5) ≠ np)) :
    ipoK m np pw rest = rest := by simp only [ipoK]; rw [ite_eq_right h]
theorem ipoT_none : ipoT m np pw rest none = none := rfl
theorem ipoT_bad (h : ok ≠ 0 ∧ n < np) : ipoT m np pw rest (some (ok, n)) = some (.ret [0]) := by
  simp only [ipoT]; rw [ite_eq_left h]
theorem ipoT_ok (h : ¬ (ok ≠ 0 ∧ n < np)) : ipoT m np pw rest (some (ok, n)) = ipoK m np pw rest := by
  simp only [ipoT]; rw [ite_eq_right h]
theorem ipoW_exit (h : ¬ j < l) : ipoW (k + 1) m np o l j = some .normal := by
  simp only [ipoW]; rw [ite_eq_right h]
theorem ipoW_ind (h : j < l) (h3 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j)) = 3) :
    ipoW (k + 1) m np o l j = ipoT m np (rdW (m.arr64 EREC) (o + j)) (ipoW k m np o l (j + 1))
      (L.Front.Ind.sortTeleW k m CWF (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j) + 4))) := by
  simp only [ipoW]; rw [ite_eq_left h, ite_eq_left h3]
theorem ipoW_other (h : j < l) (h3 : ¬ rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (o + j)) = 3) :
    ipoW (k + 1) m np o l j = ipoK m np (rdW (m.arr64 EREC) (o + j)) (ipoW k m np o l (j + 1)) := by
  simp only [ipoW]; rw [ite_eq_left h, ite_eq_right h3]
end arms

attribute [ind_grind] ipoK_bad ipoK_ok ipoT_none ipoT_bad ipoT_ok ipoW_exit ipoW_ind ipoW_other

/-- `pi_sort_tele_len` with its two lookups only (the front's `sortTele_spec`). -/
theorem sortTele_specI (p : Prog) (hps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen)
    (hev : p.lookup "e_view" = some eView) (n : Nat) : ∀ (s₀ : St) (f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_sort_tele_len" [f, h]
    ⦃fun r s' => s' = s₀ ∧ L.Front.Ind.sortTeleW n s₀.mem f h = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ f h; rw [invoke_eq _ hps]; simp only [callFn, L.Front.Ind.piSortTeleLen]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ f h
    rw [invoke_eq _ hps]
    simp only [callFn, L.Front.Ind.piSortTeleLen]
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        eView_spec p hev n] <;> finish [L.Front.Ind.sortTeleW]

theorem ipoLoop_spec (p : Prog) (hps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen)
    (hev : p.lookup "e_view" = some eView) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k ipoLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧
      ipoW k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) = some r; ⊤⦄ := by
  sorry

theorem ipoW_ne_brk : ∀ (k : Nat) (m : Mem) (np o l j : Word), ipoW k m np o l j ≠ some .brk := by
  intro k
  induction k with
  | zero => intro m np o l j h; simp [ipoW] at h
  | succ k ih =>
    intro m np o l j h
    simp only [ipoW] at h
    split at h
    · split at h
      · simp only [ipoT] at h
        split at h
        · cases h
        · split at h
          · cases h
          · simp only [ipoK] at h; split at h
            · cases h
            · exact ih _ _ _ _ _ h
      · simp only [ipoK] at h; split at h
        · cases h
        · exact ih _ _ _ _ _ h
    · cases h

/-- The function's result from its loop's signal. -/
def ipoR : Option Sig → Option Word
  | some .normal => some 1
  | some (.ret vs) => some (vs.headD 0)
  | _ => none

theorem ipoR_normal : ipoR (some .normal) = some 1 := rfl
theorem ipoR_ret (vs : List Word) : ipoR (some (.ret vs)) = some (vs.headD 0) := rfl

theorem ipo_spec (p : Prog) (hps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen)
    (hev : p.lookup "e_view" = some eView) (hp : p.lookup "ind_params_ok" = some L.Checker.indParamsOkL)
    (k : Nat) (s₀ : St) (np o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "ind_params_ok" [np, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ ipoR (ipoW (k + 1) s₀.mem np o l 0) = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp, indParamsOkL_eq]
  simp only [callFn, indParamsOkL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (ipoLoop_spec p hps hev (k + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [ipoR_normal, ipoR_ret, loc_init4, ipoW_ne_brk]

/-! ## The relation to the twin -/

theorem decEBlk_get {dn : NIdx → Option ConLeche.Name} {m : Mem} {o l : Nat} {blk : List IConstantInfo}
    (h : decEBlk dn m o l = some blk) (j : Nat) (hj : j < l) :
    ∃ q, nat? (erA m) (o + j) = some q ∧
      decCI (erA m) q = some (blk[j]'(by rw [mapM_opt_length _ _ _ h]; simpa using hj)) := by
  have := mapM_opt_get _ (List.range l) blk h j (by simpa using hj)
  simp only [List.getElem_range, Option.bind_eq_bind, Option.bind_eq_some_iff] at this
  exact this

theorem rdW_of_nat? {a : Array Word} {i q : Nat} (h : nat? (aread a) i = some q) (hi : i < 2 ^ 64) :
    rdW a (UInt64.ofNat i) = UInt64.ofNat q ∧ q < 2 ^ 64 := by
  sorry

theorem ipo_twin_other (nP : Nat) (ci : IConstantInfo) (rest : List IConstantInfo) (a : AState)
    (h1 : ∀ cv caps, ci ≠ .indInfo cv caps) (h2 : ∀ cv x y, ci ≠ .ctorInfo cv x y) :
    (indParamsOk nP (ci :: rest)).run a = (indParamsOk nP rest).run a := by
  cases ci with
  | indInfo cv caps => exact absurd rfl (h1 cv caps)
  | ctorInfo cv x y => exact absurd rfl (h2 cv x y)
  | _ => rfl

/-- **`ind_params_ok`' loop refines `indParamsOk`** on the records from `j`: reading only, the
verdict `true` exactly when the loop falls through. -/
theorem ipoW_ok (dn : NIdx → Option ConLeche.Name) {m : Mem} {a : AState} (hR : ArenaR m a)
    (np o l : Word) (blk : List IConstantInfo) (hdec : decEBlk dn m o.toNat l.toNat = some blk)
    (hb : o.toNat + l.toNat < 2 ^ 64) (hEs : (m.arr64 EREC).size < 2 ^ 64) :
    ∀ (k : Nat) (j : Word) (r : Sig), ipoW k m np o l j = some r → j ≤ l →
      (indParamsOk np.toNat (blk.drop j.toNat)).run a = .ok (decide (r = .normal), a) := by
  sorry

theorem ipoW_sig : ∀ (k : Nat) (m : Mem) (np o l j : Word) (sg : Sig), ipoW k m np o l j = some sg →
    sg = .normal ∨ sg = .ret [0] := by
  intro k
  induction k with
  | zero => intro m np o l j sg h; simp [ipoW] at h
  | succ k ih =>
    intro m np o l j sg h
    simp only [ipoW] at h
    split at h
    · split at h
      · simp only [ipoT] at h
        split at h
        · cases h
        · split at h
          · cases h; exact .inr rfl
          · simp only [ipoK] at h; split at h
            · cases h; exact .inr rfl
            · exact ih _ _ _ _ _ _ h
      · simp only [ipoK] at h; split at h
        · cases h; exact .inr rfl
        · exact ih _ _ _ _ _ _ h
    · cases h; exact .inl rfl

/-- **`ind_params_ok(nP, off, len)` refines `indParamsOk`** under the stage relation, the block's
`EREC` slice decoded: reading only (memory and twin state unchanged), the word `1` exactly when the
twin answers `true`. -/
@[refines ConRon.Arena.indParamsOk]
theorem indParamsOk_refines (p : Prog)
    (hps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen)
    (hev : p.lookup "e_view" = some eView) (hp : p.lookup "ind_params_ok" = some L.Checker.indParamsOkL)
    (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (np o l : Word) (blk : List IConstantInfo) (hS : StageR vis fe s₀.mem a₀)
    (hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) s₀.mem blk) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "ind_params_ok" [np, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ AM.ok (indParamsOk np.toNat blk) a₀ ∧
      AM.st (indParamsOk np.toNat blk) a₀ = a₀ ∧
      (r.headD 0 != 0) = AM.res (indParamsOk np.toNat blk) a₀ ∧ (r.headD 0).toNat ≤ 1; ⊤⦄ := by
  refine triple_post (ipo_spec p hps hev hp k s₀ np o l) ?_
  rintro r s' ⟨hl, hm, hR⟩
  have hdec : decEBlk dn s₀.mem o.toNat l.toNat = some blk := hblk.get (decEBlk_mono _ _ _)
  cases hw : ipoW (k + 1) s₀.mem np o l 0 with
  | none => rw [hw] at hR; cases hR
  | some sg =>
  rw [hw] at hR
  have hrun := ipoW_ok dn hS.check.arena.base np o l blk hdec hb hS.iw.erSize (k + 1) 0 sg hw (by simp)
  simp only [UInt64.toNat_zero, List.drop_zero] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hl, hm, hok, hst, ?_⟩
  rw [hres]
  rcases ipoW_sig _ _ _ _ _ _ _ hw with rfl | rfl
  · simp only [ipoR, Option.some.injEq] at hR; rw [← hR]; decide
  · simp only [ipoR, Option.some.injEq, List.headD_cons] at hR; rw [← hR]; decide

end L.Ind
