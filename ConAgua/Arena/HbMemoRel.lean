module

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

/-- `IWOK` survives a frame that keeps both `EREC` tiers and the tops `CTL[129]`, `CTL[130]`,
`CTL[200]` (it reads only the size of `IW`). -/
theorem IWOK.frameC {m m' : Mem} {A : List TieredArray} {C : List Word} (hf : MemFrame A C m m')
    (hE : (EREC : TieredArray) ∉ A) (hE1 : (tier1 EREC : TieredArray) ∉ A) (h129 : (129 : Word) ∉ C)
    (h130 : (130 : Word) ∉ C) (h200 : (200 : Word) ∉ C) (h : IWOK m) : IWOK m' := by
  have hR : m'.arr64 EREC = m.arr64 EREC := hf.arr _ hE (by decide)
  have hR1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := hf.arr _ hE1 (by decide)
  have := (IWOK_iff m).mp h
  simp only [IWOK_iff, iwTop, erTop, erecTop1, hR, hR1, hf.size, hf.ctl _ h129,
    hf.ctl _ h130, hf.ctl _ h200] at this ⊢
  exact this

end L.Ind
