import ConAgua.Arena.RecCheckSpec.K53Look
import ConAgua.Arena.RecCheckSpec.TruncSl
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# PdWMfr

What `class_nodes_agree`'s refinement reads: `decNCN_ty`, `pdW_mfr`, `CnaProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The relational side -/

/-- The type field of a `NestCtorNf` record decoded below the tops. -/
theorem decNCN_ty {m : Mem} {e : Word} {nf : NestCtorNf} (h : DecB (fun m => decNCN m e.toNat) m nf)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (e + 4)) ∧ decI (rdW (m.arr64 IW) (e + 4)) = nf.ty := by
  have h' : decNCN (truncM m) e.toNat = some nf := h
  simp only [decNCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨c, -, lv, -, ds, -, x4, h4, rfl⟩ := h'
  exact truncH (i := 4) h4 hsz

/-- `target_pi_doms_with` writes no walk memo. -/
theorem pdW_mfr : ∀ (n : Nat) (m m' : Mem) (xo xl e : Word) (r : List Word),
    pdW n m xo xl e = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [pdW] at h
  | n + 1, m, m', xo, xl, e, r, h => by
    by_cases h0 : xl = 0
    · rw [pdW_nil (h := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    by_cases h6 : tagW e ≠ 6
    · rw [pdW_nf (h := h0) (h1 := h6)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    by_cases hv : eViewW m e = []
    · rw [pdW_ev (h := h0) (h1 := h6) (h2 := hv)] at h; cases h
    rw [pdW_cons (h := h0) (h1 := h6) (h2 := hv)] at h
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp only [pdK1])
    rw [pdK1_some] at h
    refine (MFr.ofI1F h1).trans ?_
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
    refine (pdW_mfr n _ _ _ _ _ _ h2).trans ?_
    by_cases h3 : r2.headD 0 = 0
    · rw [pdK2_none (h := h3)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [pdK2_ok (h := h3)] at h
    obtain ⟨⟨r3, m3⟩, h4, h⟩ := of_K h rfl
    rw [pdK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
    exact consW_mfr h4

/-- The lookups of `class_nodes_agree`. -/
structure CnaProg (p : Prog) : Prop where
  k53 : K53Look p
  hv : p.lookup "e_view" = some eView
  hc : p.lookup "iw_copy" = some iwCopy
  ha : p.lookup "iw_alloc" = some iwAlloc
  hsc : p.lookup "sl_cons" = some slCons
  pd : p.lookup "target_pi_doms_with" = some L.Ind.targetPiDomsWith
  hi1 : I1Prog p
  cna : p.lookup "class_nodes_agree" = some classNodesAgreeL

end L.Ind

end
