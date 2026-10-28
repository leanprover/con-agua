import ConAgua.Arena.IndT.Pass
/-!
# `check_block_classes`' error claim

`checkBlockClassesE_claim`: the error half of `check_block_classes`' refinement (`cbc_ref`,
`RecGen21`), in the shape the block pass's claim reads.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_classes`' error claim** (`CheckBlockClassesE`, the `err_stmt` of
`checkBlockClasses_refinesC`): `cbc_ref`'s error half. -/
theorem checkBlockClassesE_claim {p : Prog} (hG : VerdictCtx p) : CheckBlockClassesE p := by
  intro dn vis fe env hq hIlpf hLC henv hP fs hcl hfr hfc s₀ a pp po pl co cl bs css pfvs hC hb hsrc hrecs
    hcss hpf hpfb hPm hA hOpf hk2 hk3 pP pfvsP cssP hpl hpw hshP hpfP hcssP F hF e he
  cases F with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "check_block_classes" [vis, pp, po, pl, co, cl] s₀.mem
    rw [he] at he'; cases he'; exact ErrClaim.of_cls0 h0
  | succ n =>
  exact RefE.run_err (cbcE_spec p hP (n + 1) ⟨s₀.mem, Locals.init []⟩ vis pp po pl co cl) hG.nv hG
    (cbc_ref hq hIlpf hLC henv hP hcl hfr hfc n (by omega) s₀.mem a pp po pl co cl bs css pfvs hC hb hsrc
      hrecs hcss hpf hpfb hPm hA hOpf hk2 hk3 hpl hpw hshP hpfP hcssP) he

end L.Ind
