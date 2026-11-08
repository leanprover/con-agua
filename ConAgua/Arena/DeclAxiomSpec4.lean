module

public import ConAgua.Arena.DeclAxiomSpec3
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclBasisSpec2
import ConAgua.Arena.WhnfDeltaRefine
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# `std_axiom_ok(vis, q)` refines `stdAxiomOk` (lane `decls3`)

The model runs the three clauses of a family (`famK*`: pin, `find_pinned`, abort-free `0` on a
miss) for `propext` (after the pinned `Eq` test) or `Classical.choice`; the relational lemma runs
`stdAxiomOk_eq`'s flattened twin. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The lookups of `std_axiom_ok`. -/
structure StdProg2 (p : Prog) : Prop where
  std : StdProg p
  fam : p.lookup "std_ax_family" = some stdAxFamily

l_model fam_specW (p : Prog) (h : StdProg2 p)
  fns [h.fam ↦ famW list]
  specs [pinAt_specW p h.std.red.pa n, callW_spec p n "find_pinned", callW_spec p n "rom_cv",
    callW_spec p n "eq_stored",
    mp_specW p h.std.red.canon h.std.red.mp n]
  grind [arena_grind] extra [ld64_rd_spec]

l_model std_specW (p : Prog) (h : StdProg2 p)
  fns [h.std.std ↦ stdW list]
  specs [pinAt_specW p h.std.red.pa n, callW_spec p n "rom_ci", callW_spec p n "find_is",
    callW_spec p n "std_ax_family", callW_spec p n "eq_stored"]
  grind [arena_grind] extra [ld64_rd_spec]

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A `find_pinned` call's run, against its clause. -/
theorem fp_call {p : Prog} (h : StdProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k ca cb id : Word} {r : List Word}
    (hc : callW p n "find_pinned" [vis, nm, k, ca, cb, id] m = some (r, m'))
    (hS : StageR vis fe m a) (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4 ∨ k = 5)
    (hid : id.toNat < 8) :
    ∃ b a', (clausePT fe (decI nm) k ca cb (romPinT id.toNat)).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A family of `stdAxiomOk`, flattened (`stdAxiomOk_eq`). -/
def famT (fe : IFEnv) (cv : IConstantVal) (s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word) : AM Bool := do
  let x1 ← pinAt s1.toNat
  let b1 ← clausePT fe x1 3 0 0 (romPinT i1.toNat)
  if !b1 then pure false else do
    let x2 ← pinAt s2.toNat
    let b2 ← clausePT fe x2 4 c2 c2 (romPinT i2.toNat)
    if !b2 then pure false else do
      let x3 ← pinAt s3.toNat
      let b3 ← clausePT fe x3 5 c3 c3 (romPinT i3.toNat)
      if !b3 then pure false else cv.matchesPin (← romCvT cvid.toNat)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`std_ax_family` refines a family of `stdAxiomOk`** at the model level. -/
theorem famW_ok {p : Prog} (h : StdProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word}
    {r : List Word} {cv : IConstantVal}
    (hW : famW p n m vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid = some (r, m'))
    (hS : StageR vis fe m a) (hq : decCV (erecP m) q.toNat = some cv)
    (h1 : i1.toNat < 8) (h2 : i2.toNat < 8) (h3 : i3.toNat < 8) (hcv : cvid.toNat < 10) :
    ∃ b a', (famT fe cv s1 s2 s3 i1 i2 i3 c2 c3 cvid).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- A family call's run. -/
theorem fam_call {p : Prog} (h : StdProg2 p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word}
    {r : List Word} {cv : IConstantVal}
    (hc : callW p n "std_ax_family" [vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid] m = some (r, m'))
    (hS : StageR vis fe m a) (hq : decCV (erecP m) q.toNat = some cv)
    (h1 : i1.toNat < 8) (h2 : i2.toNat < 8) (h3 : i3.toNat < 8) (hcv : cvid.toNat < 10) :
    ∃ b a', (famT fe cv s1 s2 s3 i1 i2 i3 c2 c3 cvid).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  sorry
-/

/-- **`std_axiom_ok(vis, q)` refines `stdAxiomOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.stdAxiomOk]
theorem stdAxiomOk_refines (p : Prog) (h : StdProg2 p) (dn : NIdx → Option ConLeche.Name)
    (hdn : DnInj dn) (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "std_axiom_ok" [vis, q]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (stdAxiomOk fe cv) (KeepPost vis fe decW0B) := by
  sorry

end L.Arena
