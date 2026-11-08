module

public import ConAgua.Arena.DeclNatSpec
import ConAgua.Arena.DeclCanonSpec2
public import ConAgua.Arena.DeclCanonSpec

@[expose] public section

/-!
# `ci_to_cv` refines `IConstantInfo.toConstantVal` (lane `decls3`, helper `decls3-nat`)

The stored record's inline constant value (the twin's pure projection). The result decodes in the
record prefix `erecP` of the memory after (`decCV (erecP m') q`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A returning `ntBW`: its callee returned. -/
theorem ntBW_some {β : Type} {mo : Option (List Word × Mem)} {k : List Word → Mem → Option β} {res : β}
    (hw : ntBW mo k = some res) : ∃ r m, mo = some (r, m) ∧ k r m = some res := by
  cases mo with
  | none => cases hw
  | some q => exact ⟨q.1, q.2, rfl, hw⟩

section cvref
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatCvProg (p : Prog) : Prop extends NatGateProg p where
  lCanon : CanonProg p

theorem IWGrow.erec_get {m m' : Mem} (h : IWGrow m m') {i : Nat} {v : Word}
    (hv : erecP m i = some v) : (m'.arr64 EREC)[i]? = some v := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem erecP_size_le' (m : Mem) : (erecP m).size ≤ erTop m := by
  simp only [erecP, Array.size_extract, erecTop, erTop]; omega
-/

theorem rdW_erec_of {m : Mem} {q : Word} {w : Word} (_hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h : erecP m (q.toNat) = some w) : rdW (m.arr64 EREC) q = w := by
  sorry

theorem ciToCv_ref (hN : NatCvProg p) (q : Word) (ci : IConstantInfo) :
    CallRef p "ci_to_cv" [q]
      (fun m a => StageR vis fe m a ∧ decCI (erecP m) q.toNat = some ci)
      (pure ci.toConstantVal)
      (KeepPost vis fe (fun m r (cv : IConstantVal) => decCV (erecP m) (r.headD 0).toNat = some cv)) := by
  sorry

end cvref

end L.Ind
