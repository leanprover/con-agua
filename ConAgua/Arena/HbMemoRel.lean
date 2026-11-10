module

public import ConAgua.Arena.IWFrame
public import ConAgua.Arena.IndIface

@[expose] public section

/-!
# The `hasLooseBVarB` walk's memo relation, and the frames of the core's stage invariants

`hbVR`/`hbMR` (the memo of `has_loose_b_var_b`, array `HBM`, control words `CTL[214..215]`) and the
frame lemmas `IWOK.frameC`, `hbMR_frame`: below `WhnfBase`, whose `CoreS` carries both.
-/

noncomputable section

open ConRon.Arena

namespace L.Ind

open L.Arena

theorem hbSch_wf : hbSch.WF := ⟨by decide, by decide⟩

/-- A stored value word is exactly the answer's `0`/`1`. -/
def hbVR (_ : Mem) (w : Word) (v : Bool) : Prop := w = if v then 1 else 0

/-- The memo relation of the `hasLooseBVarB` walk (keys `(node, index)`). -/
abbrev hbMR (m : Mem) (mp : Std.HashMap (EIdx × Nat) Bool) : Prop := MemoRV hbSch lfKey hbVR m mp

theorem hbVR_stable : VStable hbSch hbVR := fun _ _ _ _ _ h => h

/-- The `hb` memo survives a frame away from `HBM` and `CTL[214]`. -/
theorem hbMR_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : (HBM : TieredArray) ∉ A) (hC : (214 : Word) ∉ C) {mp : Std.HashMap (EIdx × Nat) Bool}
    (h : hbMR m mp) : hbMR m' mp :=
  memoRV_frame hbSch hbSch_wf lfKey hbVR A C hA hC m m' hf (fun _ _ h => h) mp h

end L.Ind
