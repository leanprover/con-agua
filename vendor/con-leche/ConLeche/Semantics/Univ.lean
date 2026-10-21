module

public import ConLeche.Semantics.Kit

@[expose] public section

/-!
# The sorts' placement along the universes

`⟦Sort n⟧` is a member of `⟦Sort (n+1)⟧` (`interp_sort_mem`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe w

theorem interp_sort_mem (V : Type w) [SetTheory V] (ρ : Nat → V) (n : Nat) :
    interp V ρ (.sort n) ∈ˢ interp V ρ (.sort (n + 1)) := univ_mem_univ n

end ConLeche.Semantics
