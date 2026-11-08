module

public import ConAgua.Arena.RecClassSpec.Classes
public import ConAgua.Arena.RecClassSpec.GtProg
public import ConAgua.Arena.IndGrindAttr
import ConRon.Bridge.Grind
public import ConAgua.Arena.RecSim

@[expose] public section

/-!
# RgW

`rec2DecCV_agree`, `RtoProg` (the lookups of `class_rec_ty_ok`) and the lemmas of its refinement.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Constants below the record top -/

theorem rec2DecCV_agree {a b : Array Word} {q T : Nat} (hag : ∀ i, i < T → b[i]? = a[i]?) (hq4 : q + 4 ≤ T)
    (hl : ∀ o l, nat? (aread a) (q + 1) = some o → nat? (aread a) (q + 2) = some l → o + l ≤ T ∨ l = 0) :
    decCV (aread b) q = decCV (aread a) q := by
  sorry

/-- The lookups `class_rec_ty_ok` needs. -/
structure RtoProg (p : Prog) : Prop extends GtProg p where
  ccoh : p.lookup "class_const_ok_header" = some classConstOkHeader
  cco : p.lookup "class_const_ok" = some classConstOkL
  era : p.lookup "erec_alloc" = some erecAlloc
  cvn : p.lookup "cv_new" = some cvNew
  rg : p.lookup "class_rec_ty_ok_guards" = some classRecTyOkGuards
  rto : p.lookup "class_rec_ty_ok" = some classRecTyOkL

/-! ## Relational lemmas -/

theorem rec2DecRS_parts {m : Mem} {p : Nat} {RS : RecShape} (h : decRS m p = some RS) :
    ∃ q, iwN m p = some q ∧ decCVp m q = some RS.cvR ∧ iwN m (p + 1) = some RS.rP ∧
      iwN m (p + 2) = some RS.mI ∧ iwN m (p + 3) = some RS.tgt := by
  sorry

theorem rec2W_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : (UInt64.ofNat a : Word) = UInt64.ofNat b) : a = b := by
  have := congrArg UInt64.toNat h
  rwa [UInt64.toNat_ofNat_of_lt' ha, UInt64.toNat_ofNat_of_lt' hb] at this

theorem rec2W_add (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((UInt64.ofNat a + UInt64.ofNat b : Word)).toNat = (a + b) % 2 ^ 64 := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' ha, UInt64.toNat_ofNat_of_lt' hb]

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-! ## The `abstract1` memo across `class_const_ok` -/

/-- A `RSim` whose post also records the twin's run. -/
theorem RSim.withRun {β α : Type} {o : Option β} {op : AM α} {a : AState}
    {Q : β → AState → α → Prop} (h : RSim o op a Q) :
    RSim o op a (fun b a' x => Q b a' x ∧ op.run a = .ok (x, a')) := by
  intro b hb
  obtain ⟨x, a', hr, hq⟩ := h b hb
  exact ⟨x, a', hr, hq, hr⟩

/-- `class_rec_ty_ok`'s result: a constant record below the record top. -/
def decCVR (m' : Mem) (r : List Word) (cv : IConstantVal) : Prop :=
  decCVp m' (r.headD 0).toNat = some cv ∧ CVExt m' (r.headD 0).toNat

end sims

end L.Ind

end
