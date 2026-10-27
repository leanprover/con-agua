import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndPosSpec.RxMapW

/-!
# KofProg

`KofProg`, `ckOfNk`, `decCK_eq`, `decCK_decB_nk`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `class_key_of`. -/
structure KofProg (p : Prog) : Prop where
  rx : RxLook p
  h3 : p.lookup "rec3" = some rec3
  tcp : p.lookup "target_canon_params" = some targetCanonParams
  go : p.lookup "class_key_canon_go" = some classKeyCanonGo
  kc : p.lookup "class_key_canon" = some classKeyCanonL
  kcl : p.lookup "class_key_of_closed" = some classKeyOfClosed
  kof : p.lookup "class_key_of" = some classKeyOfL
  bvb : BvbProg p
  hf : HfF p

/-! ## Class keys as nest keys (the same layout) -/

/-- A `NestKey` read as a `ClassKey`. -/
def ckOfNk (n : NestKey) : ClassKey := ⟨n.cname, n.lvls, n.ds⟩

theorem decCK_eq (m : Mem) (k : Nat) : decCK m k = (decNK m k).map ckOfNk := by
  simp only [decCK, decNK, Option.bind_eq_bind, Option.pure_def]
  cases (iwH m k : Option NIdx) <;> simp
  cases (iwH m (k + 1) : Option LsIdx) <;> simp
  cases (decAt m (decHL m) (k + 2) : Option (List EIdx)) <;> simp [ckOfNk]

theorem decCK_decB_nk {m : Mem} {k : Nat} {ck : ClassKey} (h : DecB (fun m => decCK m k) m ck) :
    ∃ nk, DecB (fun m => decNK m k) m nk ∧ ckOfNk nk = ck := by
  have h' : decCK (truncM m) k = some ck := h
  rw [decCK_eq, Option.map_eq_some_iff] at h'
  obtain ⟨nk, h1, h2⟩ := h'
  exact ⟨nk, h1, h2⟩

end L.Ind

end
