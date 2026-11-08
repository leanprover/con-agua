module

public import ConAgua.Arena.DeclStep
public import ConAgua.Arena.IndRealWalk
public import ConAgua.Arena.CoreLevels
import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndMaster
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndCopy2
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.Pins

@[expose] public section

/-!
# Phase B's check, `check_value_group`: its write set from the text

The declaration loop's relation `LoopR` has, beside the stage relation (`StageR = CheckR ∧ IWOK`,
what every callee keeps), the pending checks (`PEND`, `CTL[130]`) and the front's declaration
records (`DECL`, `DLP`). No callee spec mentions them (a stub's `RelAM` post is `KeepPost`), so
they come from the program text (`closedA`, DESIGN "The relation's architecture"): every function
`check_value_group` reaches writes only arrays other than `PEND`/`DECL`/`DLP` and `CTL` words
other than `130`.

The text is a concrete program `cvgProg`: this lane's functions, lane `induct`'s library and stubs,
and the real master callees (`pin_word`, lane `whnf`'s `lvl_eq_c` with lane `levels`'
`lvl_eq`). A program `p` with that text (`CvgProg p`, a `TextProg`) agrees with it on the reached
functions but `openFns` (the core's entry points and the walks: real code in the checker, stubs
here) and has the write set on a call-closed superset (`StepIn`; for the checker's program,
`ConAgua/Checker/LoopDecl.lean`).
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP)

/-- The arrays a step may write: all but the pending checks and the declaration records. -/
def stepA : List TieredArray :=
  checkerWordArrays.filter fun b => b ≠ DECL ∧ b ≠ DLP ∧ (b.arr < 146 ∨ 149 < b.arr)

/-- The `CTL` words a step may write: all but the pending checks' count, the promotion memos'
words and the pin variant list's header (`CTL[150]`, `CTL[151]`, lane `romload`). -/
def stepC : List Word :=
  ((List.range 1024).filter fun x => x ≠ 130 ∧ x ≠ 150 ∧ x ≠ 151 ∧ (x < 140 ∨ 147 < x)).map
    UInt64.ofNat

/-- `check_value_group`'s text: this lane's functions, lane `induct`'s library and stubs, and the
real master callees it reaches. -/
def cvgProg : Prog :=
  declStepFns ++ L.Ind.libFns ++ L.Ind.stubFns ++ [("pin_word", pinWordL)] ++
    [("lvl_eq_c", lvlEqCL), ("lvl_eq_rec", lvlEqRecL), ("lq_find", memoFindG lqSch),
     ("lq_put", memoPutG lqSch)] ++ levelProg

/-- The functions `check_value_group` reaches. -/
def cvgFns : List FnName :=
  ["iw_reset", "infer_type_core", "ensure_sort_core", "pin_word", "lvl_eq_c",
   "lq_find", "lvl_eq_rec", "lvl_eq", "lv_equiv", "lv_eq", "lv_node", "lv_simp", "lh_mk", "lv_comb",
   "lv_leq", "lv_rest", "lv_imax", "lv_cases", "lv_cases_at", "lv_subsimp", "lv_subst", "lv_imax_l",
   "lv_dist1", "lv_dist2", "lv_imax_r", "lq_put", "cv_lps", "er_to_iw",
   "iw_alloc", "er_copy", "loose_bvars_bounded_fast", "has_fvar_fast", "all_level_params_defined",
   "consts_resolve_ffast", "is_def_eq_core"]

/-- **The callees the declaration texts do not fix** (lane `loopt2`): real code in the checker's
program, stubs in the texts (`cvgProg`, `ivProg`, `armText`): the core's entry points, the walks,
the ROM readers and the gates' leaves. Their specs come from their own refinements (or
`stubM_spec`), never from the texts' lookups; their write set is the checker's (`StepIn`). -/
def openFns : List FnName :=
  ["infer_type_core", "ensure_sort_core", "is_def_eq_core", "loose_bvars_bounded_fast",
   "has_fvar_fast", "all_level_params_defined", "nat_lit_supported", "rom_cv",
   "rom_ci", "rom_expr_pin", "rom_basis_decls", "rom_pin_sets",
   "consts_resolve_ffast"]

/-- **`fs` lies in a call-closed function set with a step's write set** (`stepA`, `stepC`). -/
def StepIn (p : Prog) (fs : List FnName) : Prop :=
  ∃ F : List FnName, (∀ f ∈ fs, f ∈ F) ∧ closedA p stepA stepC F = true

open Std.WP in
open scoped Lean.Order in
/-- A function of `fs` keeps the memory outside a step's write set (`invoke_memFrame`). -/
theorem StepIn.memFrame {p : Prog} {fs : List FnName} (h : StepIn p fs) (n : Nat) {f : FnName}
    (hf : f ∈ fs) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun _ s => MemFrame stepA stepC s₀.mem s.mem ∧ s.mem.bytes = s₀.mem.bytes; ⊤⦄ :=
  by obtain ⟨_, hF, hc⟩ := h; exact invoke_memFrame hc n (hF f hf) vs s₀

/-- **A program with a text `q` on the functions `fs`**: it agrees with `q` on `fs` but
`openFns`, and `fs` has a step's write set in it. -/
structure TextProg (p q : Prog) (fs : List FnName) : Prop where
  agree : ∀ f ∈ fs, f ∉ openFns → p.lookup f = q.lookup f
  closed : StepIn p fs

/-- A program with `check_value_group`'s text. -/
structure CvgProg (p : Prog) : Prop extends TextProg p cvgProg cvgFns where
  bvb : BvbProg p
  hf : L.Ind.HfF p

section lookups
variable {p : Prog} (h : CvgProg p)
include h
theorem CvgProg.reset : p.lookup "iw_reset" = some L.Ind.iwReset :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.pin : p.lookup "pin_word" = some pinWordL :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.lps : p.lookup "cv_lps" = some L.Ind.cvLps :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.eti : p.lookup "er_to_iw" = some L.Ind.erToIw :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.alloc : p.lookup "iw_alloc" = some L.Ind.iwAlloc :=
  (h.agree _ (by decide) (by decide)).trans rfl
theorem CvgProg.copy : p.lookup "er_copy" = some L.Ind.erCopy :=
  (h.agree _ (by decide) (by decide)).trans rfl
end lookups

end L.Arena

/-! ## Word models and their `vcgen` specs (no twin values) -/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-- The model of `pin_word(k)`. -/
def pinWordW (m : Mem) (k : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else some ([rdW (m.arr64 PINS) k], m)

theorem pinWord_specW (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ pinWordW s₀.mem k = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinWordW, pinW_eq, rdW_eq]

/-- The model of `iw_reset()`. -/
def iwResetW (m : Mem) : Option (List Word × Mem) := some ([], m.set64 CTL 200 0)

theorem iwReset_specW (p : Prog) (hp : p.lookup "iw_reset" = some iwReset) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "iw_reset" []
    ⦃fun r s' => LocEq s' s₀ ∧ iwResetW s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iwReset]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [iwResetW]

/-- The model of `cv_lps(q)` (its copy runs at `n - 1`). -/
def cvLpsW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, q => erToIwW n m (rdW (m.arr64 EREC) (q + 1)) (rdW (m.arr64 EREC) (q + 2))

theorem cvLpsW_step (n : Nat) (m : Mem) (q : Word) :
    cvLpsW (n + 1) m q = erToIwW n m (rdW (m.arr64 EREC) (q + 1)) (rdW (m.arr64 EREC) (q + 2)) :=
  rfl

grind_pattern [ind_grind] cvLpsW_step => cvLpsW (n + 1) m q

theorem cvLps_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "cv_lps" = some cvLps) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_lps" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ cvLpsW n s₀.mem q = some (r, s'.mem) ∧
      r = [r.headD 0, r.tail.headD 0]; ⊤⦄ := by
  sorry

end L.Arena

/-! ## The relational lemmas: a model run from the stage relation is a twin run -/

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **`er_to_iw` under the stage relation**: the copy decodes as the `EREC` slice, the stage
relation holds after it, the pool only grew. A zero-length copy needs no source bound. -/
theorem erToIwW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : erToIwW n m o l = some (r, m'))
    (hS : StageR vis fe m a) (hsrc : l.toNat = 0 ∨ o.toNat + l.toNat ≤ (m.arr64 EREC).size) :
    r = [r.headD 0, r.tail.headD 0] ∧ r.tail.headD 0 = l ∧
    (∀ {k : IdxKind}, (decHL m' (r.headD 0).toNat l.toNat : Option (List (Idx k))) =
      hslice? (erA m) o.toNat l.toNat) ∧
    StageR vis fe m' a ∧ IWGrow m m' ∧ (r.headD 0).toNat + l.toNat ≤ iwTop m' := by
  sorry

/-- **`er_to_iw` writes only the pool and its top** (`IW`, `CTL[200]`). -/
theorem erToIwW_frame {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : erToIwW n m o l = some (r, m'))
    (hS : StageR vis fe m a) (hsrc : l.toNat = 0 ∨ o.toNat + l.toNat ≤ (m.arr64 EREC).size) :
    MemFrame [IW] [200] m m' := by
  sorry

/-- Destructuring a constant value: its name, its universe-parameter slice, its type. -/
theorem decCV_slice {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV (aread a) q = some cv) :
    ∃ w1 w2, a[q + 1]? = some w1 ∧ a[q + 2]? = some w2 ∧
      hslice? (aread a) w1.toNat w2.toNat = some cv.levelParams := by
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, -, lv, hlv, ty, -, rfl⟩ := h
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho2, l', hl2, hsl⟩ := hlv
  simp only [nat?, Option.map_eq_some_iff] at ho2 hl2
  obtain ⟨w1, hw1, rfl⟩ := ho2
  obtain ⟨w2, hw2, rfl⟩ := hl2
  exact ⟨w1, w2, hw1, hw2, hsl⟩

theorem rdW_of_get? {a : Array Word} {x w : Word} {k : Nat} (hk : k = x.toNat) (h : a[k]? = some w) :
    rdW a x = w := by
  subst hk; simp [rdW, h]

theorem exc_ok_bind' {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

theorem fuelW : (4000000000 : Word).toNat = coreWalkFuel := rfl

theorem decCV_typeW {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV (aread a) q = some cv) :
    ∃ w, a[q + 3]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.type = decI w := by
  simp only [decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, ty, hty, rfl⟩ := h
  exact hd?_some hty

/-- A grown pool keeps every record of the old one. -/
theorem IWGrow.erecExt {m m' : Mem} (h : IWGrow m m') : ArrExt (erecP m) (erA m') := by
  sorry

/-- The memory after `iw_reset` is in the stage relation. -/
theorem iwReset_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hS : StageR vis fe m a) :
    StageR vis fe (m.set64 CTL 200 0) a ∧ m.set64 CTL 200 0 = m.set64 CTL 200 0 ∧
      (m.set64 CTL 200 0).arr64 EREC = m.arr64 EREC ∧ erTop (m.set64 CTL 200 0) = erTop m := by
  sorry

theorem erecP_reset (m : Mem) : erecP (m.set64 CTL 200 0) = erecP m := by
  sorry

theorem word_add_toNat (g : Word) (k : Nat) (h : g.toNat + k < 2 ^ 64) :
    (g + UInt64.ofNat k).toNat = g.toNat + k := by
  rw [UInt64.toNat_add]; simp; omega

end L.Arena
