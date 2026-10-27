import ConAgua.Arena.IndInstallSpec.PapW

/-!
# The inductive arm's block: the front's decoding is the stage's (lane `indproofs4`)

`IndArmSpec` hands the arm its block as the front decodes it (`decCIs (erecP m)`, the record pool
below its top); `cidW_ok` takes it as the stage decodes it below the tops (`DecB decEBlk`). The
cut memory's record pool is exactly the pool below its top (`erA_truncM`), so the two agree.
-/


open ConRon.Arena

namespace L.Ind
open L.Arena

/-- The cut memory's record pool is the pool below its top. -/
theorem erA_truncM (m : Mem) : erA (truncM m) = erecP m := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < erTop m
  · rw [truncM_er_eq hi, erecP_getE hi]; rfl
  · rw [truncM_er_get?, ite_eq_right hi]
    symm
    simp only [erecP, Array.getElem?_extract]
    split
    · rename_i h
      exact absurd (show i < erTop m by simp only [erTop, erecTop] at *; omega) hi
    · rfl

/-- **The front's block decoding is the stage's** (`IndArmSpec`'s premise to `cidW_ok`'s). -/
theorem decB_decEBlk_of_decCIs {dn : NIdx → Option ConLeche.Name} {m : Mem} {o l : Nat}
    {blk : List IConstantInfo} (h : L.Front.decCIs (erecP m) dn o l = some blk) :
    DecB (fun m => decEBlk dn m o l) m blk := by
  show decEBlk dn (truncM m) o l = some blk
  simp only [decEBlk, erA_truncM]
  exact h

end L.Ind
