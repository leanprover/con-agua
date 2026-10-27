import ConAgua.Arena.IndInstallSpec7
import ConAgua.Arena.RecStab

/-!
# Refinements of `IndInstall`, part 8 (lane `indproofs2`, helper `install`): `checkBlockTele`

The round-3 template for this module's parents: every callee enters the word model as its run
`callW p n f args m` (so the `vcgen` spec needs no callee spec but `callW_spec`), and the
relational lemma turns each run into the twin's through the callee's own refinement triple
(`installSimCall`) or its stub contract (`installSimStub`), composed by `Sim.bindK`.

A former's constant record carries `CVExt` (rec lane's: the record and its level-parameter slice
below the record pool's top), a precondition on the member records (the twin's decoding of an
empty slice ignores its offset, so `DecB` alone does not give it); `check_sum_tele` now returns it
for its result.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Callees as runs -/

/-- **A callee's refinement triple, as a `Sim` on its run.** -/
theorem installSimCall {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName} {args : List Word}
    {m : Mem} {op : AM α} {a : AState} {Q : List Word → α → Mem → AState → Prop}
    {P : List Word → St → Prop}
    (h : ⦃fun s => s = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p n) f args ⦃fun r s' => P r s'; ⊤⦄)
    (hP : ∀ r s', P r s' → AM.ok op a ∧ Q r (AM.res op a) s'.mem (AM.st op a)) :
    Sim (callW p n f args m) op a Q := by
  intro r m' e
  obtain ⟨s', rfl, hp⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) h e
  obtain ⟨hok, hq⟩ := hP r s' hp
  exact ⟨_, _, partsRunOfOk hok, hq⟩

/-! ## Constant records below the tops -/

/-- A constant decoded in a memory whose record lies below the tops (`CVExt`) is decoded below
the tops. -/
theorem installCvDecB {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv)
    (hx : CVExt m q) : DecB (fun m => decCVp m q) m cv := by
  obtain ⟨hq, hsl⟩ := hx
  have e : ∀ i, i < erTop m → (erA (truncM m))[i]? = (erA m)[i]? := fun i hi => truncM_er_eq hi
  show decCVp (truncM m) q = some cv
  simp only [decCVp] at h ⊢
  simp only [decCV, bind, Option.bind, pure, hlist?] at h ⊢
  have e0 : (hd? (erA (truncM m)) q : Option NIdx) = hd? (erA m) q := by simp only [hd?, e q (by omega)]
  have e1 : nat? (erA (truncM m)) (q + 1) = nat? (erA m) (q + 1) := by simp only [nat?, e (q + 1) (by omega)]
  have e2 : nat? (erA (truncM m)) (q + 1 + 1) = nat? (erA m) (q + 1 + 1) := by
    simp only [nat?, e (q + 1 + 1) (by omega)]
  have e3 : (hd? (erA (truncM m)) (q + 3) : Option EIdx) = hd? (erA m) (q + 3) := by
    simp only [hd?, e (q + 3) (by omega)]
  rw [e0, e1, e2, e3]
  cases h1 : nat? (erA m) (q + 1) with
  | none => rw [h1] at h; revert h; cases (hd? (erA m) q : Option NIdx) <;> simp
  | some lo =>
  cases h2 : nat? (erA m) (q + 1 + 1) with
  | none => rw [h1, h2] at h; revert h; cases (hd? (erA m) q : Option NIdx) <;> simp
  | some ll =>
  have hN := hsl lo ll h1 (by simpa using h2)
  have hs : (hslice? (erA (truncM m)) lo ll : Option (List NIdx)) = hslice? (erA m) lo ll := by
    simp only [hslice?]
    exact mapM_congr_of _ _ _ (fun j hj => by
      have := List.mem_range.mp hj
      simp only [hd?, e (lo + j) (by omega)])
  rw [h1, h2] at h
  simp only [hs]
  exact h

/-! ## The lookups of `check_sum_tele` -/

/-- The lookups `check_sum_tele`'s refinement takes. -/
structure CstProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  view : p.lookup "e_view" = some eView
  fvarFind : p.lookup "fvar_find" = some fvarFind
  fvarPush : p.lookup "fvar_push" = some fvarPush
  internFVar : p.lookup "intern_fvar" = some internFVar
  wt : p.lookup "whnf_telescope" = some whnfTelescopeL
  sortFind : p.lookup "sort_find" = some sortFind
  sortPush : p.lookup "sort_push" = some sortPush
  internSort : p.lookup "intern_sort" = some internSort
  derB : p.lookup "der_b" = some derB
  forallFind : p.lookup "forall_find" = some forallFind
  forallPush : p.lookup "forall_push" = some forallPush
  internForall : p.lookup "intern_forall" = some internForallL
  mkForall : p.lookup "mk_forall" = some mkForall
  closeTele : p.lookup "close_telescope" = some closeTelescope
  erAlloc : p.lookup "erec_alloc" = some erecAlloc
  cvNew : p.lookup "cv_new" = some cvNew
  slow : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL
  tele : p.lookup "check_sum_tele" = some checkSumTeleL
  strip : StripProg p
  i1 : I1Prog p
  ab : AbF p

/-- `intern_sort` as a `Sim` (master's, through its stage lemma). -/
theorem installSortSim {p : Prog} (hP : CstProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {u : Word} (hS : StageR dn vis fe m a) (hu : H u) :
    Sim (callW p n "intern_sort" [u] m) (internSortE (decI u)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decE (r.headD 0) = x ∧ AFr m m') := by
  intro r m' e
  obtain ⟨s', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSort_spec p hP.sortFind hP.sortPush hP.internSort n _ u) e
  obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS u hu hI
  exact ⟨_, a', hrun, hS', hg, rfl, sointernW_afr hI⟩

/-! ## `check_block_tele` -/

/-- **`check_block_tele` is its model `ibtW`** (generated). -/
l_model ibt_spec (p : Prog) (hp : p.lookup "check_block_tele" = some checkBlockTele)
  fns [hp ↦ ibtW]
  specs [callW_spec p n "check_constant_val", callW_spec p n "check_sum_tele",
    callW_spec p n "strip_pis", callW_spec p n "intern_sort"]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- The post of `check_block_tele`: the checked former below the tops, its result sort a handle. -/
def TeleOut (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (x : IConstantVal × LIdx) (m' : Mem) (a' : AState) : Prop :=
  StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some x.1 ∧
    CVExt m' (r.headD 0).toNat ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2

/-- What a member record must satisfy: decoded below the tops, its former's constant record
below the tops (`CVExt`). -/
def MemOK (m : Mem) (q : Nat) (ms : MemberShape) : Prop :=
  DecB (fun m => decMS m q) m ms ∧ ∀ c, iwN m q = some c → CVExt m c

theorem MemOK.grow {m m' : Mem} {q : Nat} {ms : MemberShape} (h : MemOK m q ms) (hg : IWGrow m m') :
    MemOK m' q ms := by
  refine ⟨h.1.grow (decMS_mono _) hg, fun c hc => ?_⟩
  have hq : q < iwTop m := by
    have := h.1; simp only [DecB, decMS, bind, Option.bind_eq_some_iff] at this
    obtain ⟨c', hc', -⟩ := this; exact partsIwLt hc'
  rw [iwN_grow hg hq] at hc
  exact CVExt_grow hg (h.2 c hc)

/-- A callee proved at every positive fuel is simulated at every fuel (`callW` at `0` fails). -/
theorem _root_.L.Arena.Sim.callW_pos {α : Type} {p : Prog} {f : FnName} {args : List Word} {m : Mem} {op : AM α}
    {a : AState} {Q : List Word → α → Mem → AState → Prop}
    (h : ∀ k, Sim (callW p (k + 1) f args m) op a Q) (n : Nat) : Sim (callW p n f args m) op a Q := by
  cases n with
  | zero => rw [callW_zero]; exact Sim.of_none
  | succ k => exact h k

end L.Ind
