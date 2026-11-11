module

public import ConAgua.Arena.ConstsResolveF
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatSpec
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.DeclNatBase
public import ConAgua.Arena.WhnfIota
import all ConAgua.Arena.ConstsResolveF

@[expose] public section

/-!
# `consts_resolve_ffast` refines `constsResolveFFast` (lane `tails`)

`ConstsResolveF.lean`'s L code (lane `stubs`) under the inductive stage's relation `StageR`, in the
`RefAM` shape of `IndStubs.lean`'s contract `constsResolveFFast_spec`.

* **Models from the calls.** Every function's word model is written over `callW` of its callees
  (`DeclNatBase.lean`'s style), so each `vcgen` spec only matches the text; the callees' meaning
  enters in the relational lemmas (`pin_at`: `pinAt_model`; `env_find`: `envFindW_found`; `e_view`:
  `eViewW_ok`; `is_str_lit`: `islW`, `viewLit_ok`).
* **The memo.** The twin threads its memo (`Std.HashMap EIdx Bool`) through the walk; the L table
  `CRM` (`crSch`) is related to it by the memo library's `MemoRV` at key `(h, 0)` (`bmKey`) and the
  value relation `CrV` (the word is `0` or `1`, and decodes to the Bool). The twin's walk changes
  no state; the L walk writes only `CRM` and `CTL[158‥159]`, which `StageR` does not read
  (`StageR.frame_hi`).
* **Fuel.** The counter word `f` is the twin's fuel (`4000000000` = `coreWalkFuel` at the entry);
  the induction is on L's fuel.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Stubs

open L.Arena L.Ind

/-- What the specs need of the program. -/
structure CrfProg (p : Prog) : Prop where
  entry : p.lookup "consts_resolve_ffast" = some constsResolveFFastL
  go : p.lookup "crf_go" = some crfGo
  leaf : p.lookup "cr_leaf" = some crLeaf
  lit : p.lookup "cr_lit_pins" = some crLitPins
  pf : p.lookup "pin_found" = some pinFound
  find : p.lookup "crm_find" = some (memoFindG crSch)
  put : p.lookup "crm_put" = some (memoPutG crSch)
  clear : p.lookup "crm_clear" = some (memoClearG crSch)
  view : p.lookup "e_view" = some eView
  isl : p.lookup "is_str_lit" = some isStrLitL
  ef : p.lookup "env_find" = some envFindL
  erg : p.lookup "env_row_get" = some envRowGetL
  brg : p.lookup "base_row_get" = some baseRowGetL
  pin : p.lookup "pin_at" = some pinAtL

/-! ## The models over the calls, and their specs -/

section models
variable (p : Prog) (k : Nat)

/-- `consts_resolve_ffast(vis, e)`. -/
def crffW (m : Mem) (vis e : Word) : Option (List Word × Mem) :=
  ntBW (callW p k "crm_clear" [] m) fun _ mc =>
  ntBW (callW p k "crf_go" [vis, 4000000000, e] mc) fun r mr => some ([r.headD 0], mr)

end models

l_model pf_spec (p : Prog) (hp : CrfProg p)
  fns [hp.pf ↦ pfW list]
  specs [callW_spec p n "pin_at", callW_spec p n "env_find"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model clp_spec (p : Prog) (hp : CrfProg p)
  fns [hp.lit ↦ clpW list]
  specs [callW_spec p n "pin_found"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model cl_spec (p : Prog) (hp : CrfProg p)
  fns [hp.leaf ↦ clW list]
  specs [callW_spec p n "is_str_lit", callW_spec p n "cr_lit_pins", callW_spec p n "env_find"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

l_model crf_spec (p : Prog) (hp : CrfProg p)
  fns [hp.go ↦ crfW list]
  specs [callW_spec p n "e_view", callW_spec p n "cr_leaf", callW_spec p n "crm_find",
    callW_spec p n "crm_put", callW_spec p n "crf_go", callW_spec p n "env_find"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW pfuel

theorem crff_spec (p : Prog) (hp : CrfProg p) (k : Nat) (s₀ : St) (vis e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "consts_resolve_ffast" [vis, e]
    ⦃fun r s' => LocEq s' s₀ ∧ crffW p k s₀.mem vis e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.entry]
  simp only [callFn, constsResolveFFastL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p k "crm_clear",
      callW_spec p k "crf_go"] <;>
    finish (gen := 20) [crffW, ntBW]

/-! ## The callees' meaning -/

section rel
variable {p : Prog} (hp : CrfProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include hp

/-- **`env_find(w, vis)` as a call**: memory unchanged, and the word says whether `w` has a row in
the environment. -/
theorem envFind_callW {n : Nat} {m m' : Mem} {w : Word} {r : List Word}
    (hE : EnvR m vis fe) (hw : w.toNat < 2 ^ 32)
    (hc : callW p n "env_find" [w, vis] m = some (r, m')) :
    m' = m ∧ r.headD 0 = if (fe.find? (decI w)).isSome then 1 else 0 := by
  obtain ⟨s', hs', h1, -, hR⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_spec p hp.erg hp.brg hp.ef n _ vis w) hc
  refine ⟨hs'.symm.trans h1, ?_⟩
  subst hR
  obtain ⟨hf, hd⟩ := hE.find_res hw
  rw [hf]
  by_cases h0 : (findRes m vis w).headD 0 = 0
  · rw [h0]; simp [envFound]
  · obtain ⟨ci, hci⟩ := hd h0
    have h1 : (findRes m vis w).headD 0 = 1 := by
      unfold findRes at h0 ⊢
      by_cases a1 : ownHit m vis w <;> by_cases a2 : baseHit m w <;> simp_all
    have e : envFound m 1 ((findRes m vis w).tail.headD 0) = some ci := by
      unfold envFound; rw [ite_eq_right (show (1 : Word) ≠ 0 by decide)]; exact hci
    rw [h1, e]; rfl

/-- **`pin_found(vis, i)`**: memory unchanged, the flag set, `i < 51`, and the word says whether
pin `i`'s name has a row. -/
theorem pf_callW {n : Nat} {m m' : Mem} {i : Word} {r : List Word} {a : AState}
    (hS : StageR vis fe m a) (hc : callW p n "pin_found" [vis, i] m = some (r, m'))
    (h51 : i ≠ 51) :
    m' = m ∧ pinW m 0 ≠ 0 ∧ i.toNat < 51 ∧
      r.headD 0 = (if (fe.find? (decI (pinW m (1 + i.toNat)))).isSome then 1 else 0) := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hW := callW_model (M := fun mm => pfW p n mm vis i) (pf_spec p hp n · vis i) hc
  unfold pfW at hW
  cases h1 : callW p n "pin_at" [i] m with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨r1, m1⟩ := q
  rw [h1, bW_some] at hW
  obtain ⟨rfl, h0, hi, hr1⟩ := pinAt_model hp.pin h1 rfl h51
  cases h2 : callW p n "env_find" [r1.headD 0, vis] m1 with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨r2, m2⟩ := q
  rw [h2, bW_some, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  have hF := hS.check.pins.full h0
  have hlt := hF.names_lt _ hi
  rw [hr1] at h2
  obtain ⟨rfl, hv⟩ := envFind_callW hp hS.check.env hlt h2
  exact ⟨rfl, h0, hi, hv⟩

/-- Whether every pin of `ks` has a row (the twin's `&&` of `isSome`s). -/
def pinsFound (fe : IFEnv) (m : Mem) (ks : List Word) : Bool :=
  ks.all fun k => (fe.find? (decI (pinW m (1 + k.toNat)))).isSome

/-- **A `pin_found` call in `cr_lit_pins`' chain**: the memory unchanged, the flag set, and the
word says whether pin `i`'s name has a row. -/
theorem pf_bind {n : Nat} {m : Mem} {a : AState} {i : Word} {r : List Word} {m' : Mem}
    {K : List Word → Mem → Option (List Word × Mem)} (hS : StageR vis fe m a) (h51 : i ≠ 51)
    (h : ntBW (callW p n "pin_found" [vis, i] m) K = some (r, m')) :
    ∃ r₀, K r₀ m = some (r, m') ∧ pinW m 0 ≠ 0 ∧
      r₀.headD 0 = if (fe.find? (decI (pinW m (1 + i.toNat)))).isSome then 1 else 0 := by
  rcases hc : callW p n "pin_found" [vis, i] m with _ | ⟨r₀, m₀⟩ <;> rw [hc] at h
  · cases h
  obtain ⟨rfl, h0, -, hv⟩ := pf_callW hp hS hc h51
  exact ⟨r₀, h, h0, hv⟩

end rel

end L.Stubs
