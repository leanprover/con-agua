import ConAgua.Arena.RecGenSpec.RgW
import ConAgua.Arena.RecGenSpec.DecCVX
import ConAgua.Arena.RecStab
import ConAgua.Arena.RecGenSpec.ClassMinorSlot
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# ClassRecTysOk

`RtsProg`, `decCVS` and the lemmas `class_rec_tys_ok`'s refinement uses.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `class_rec_tys_ok` needs. -/
structure RtsProg (p : Prog) : Prop extends RtoProg p where
  cons : p.lookup "sl_cons" = some slCons
  rts : p.lookup "class_rec_tys_ok" = some classRecTysOkL

theorem decCVX_stab {m : Mem} {p : Nat} {cv : IConstantVal} (h1 : decCVp m p = some cv)
    (h2 : CVExt m p) : StabD (fun m => decCVX m p) m cv := by
  intro m'' hg
  simp only [decCVX, ite_eq_left (CVExt_grow hg h2)]
  rw [decCVp_grow_r hg h2, h1]

theorem RecsOK_tail {m : Mem} {ro rl : Nat} {cv : IConstantVal} {cvs : List IConstantVal}
    (h : RecsOK m ro (rl + 1) (cv :: cvs)) : RecsOK m (ro + 1) rl cvs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by simpa using h2, fun j hj => ?_⟩
  obtain ⟨p0, q, cv', hp0, hp1, hq, hcv, hext, hcvs⟩ := h3 (j + 1) (by omega)
  exact ⟨p0, q, cv', by rw [show ro + 1 + j = ro + (j + 1) by omega]; exact hp0, hp1, hq, hcv, hext,
    by simpa using hcvs⟩

/-- `class_rec_tys_ok`'s result: a stable slice of constant records below the record top. -/
def decCVS (m' : Mem) (r : List Word) (xs : List IConstantVal) : Prop :=
  SPL decCVX m' (r.headD 0).toNat (r.tail.headD 0).toNat xs

end L.Ind

end
