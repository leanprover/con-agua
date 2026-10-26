import ConAgua.Arena.IndPartsSpec14
import ConAgua.Arena.IndRealAbsPos

/-!
# `blockShape?` under `StageC`, part 1: the walk memos across `block_shape`'s first callees
(lane `indproofs4`, helper `bpc`)

`AbsOK` across the models of the callees `block_shape` runs before `lvl_eq_c` (`block_split`,
`block_shape_names_of`, `block_member_counts`, `er_to_iw`, `block_shape_pins_ok`,
`block_shape_result_sort`): they write the record pool and `EREC` only (`afr_auto`). `lvl_eq_c`'s
real refinement (`lvlEqC_simC`) needs `StageC` at the call, whose memory half is `AbsOK`'s.
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## `block_split` -/

theorem bsrW_afr : ∀ (n : Nat) (m m' : Mem) (off l : Word) (r : List Word),
    bsrW n m off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [bsrW] at h
  | n + 1, m, m', off, l, r, h => by
    simp only [bsrW, bsrK1.eq_def, bsrK2.eq_def, bsK3.eq_def] at h
    afr_auto h [bsrW_afr n _ _ _ _ _, posRecW_afr, consW_afr]

theorem bscW_afr : ∀ (n : Nat) (m m' : Mem) (off l : Word) (r : List Word),
    bscW n m off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [bscW] at h
  | n + 1, m, m', off, l, r, h => by
    simp only [bscW, bscK1.eq_def, bscK2.eq_def, bscKR.eq_def] at h
    afr_auto h [bscW_afr n _ _ _ _ _, bsrW_afr n _ _ _ _ _, posRecW_afr, consW_afr]

theorem bsW_afr : ∀ (n : Nat) (m m' : Mem) (off l : Word) (r : List Word),
    bsW n m off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [bsW] at h
  | n + 1, m, m', off, l, r, h => by
    simp only [bsW, bsK1.eq_def, bsK2.eq_def, bsKC.eq_def] at h
    afr_auto h [bsW_afr n _ _ _ _ _, bscW_afr n _ _ _ _ _, posRecW_afr, consW_afr]

/-! ## `block_shape_names_of` -/

theorem bsnW_afr : ∀ (n : Nat) (m m' : Mem) (cto ctl : Word) (r : List Word),
    bsnW n m cto ctl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [bsnW] at h
  | n + 1, m, m', cto, ctl, r, h => by
    simp only [bsnW, bsnW.bsnK.eq_def, bgoK3.eq_def] at h
    afr_auto h [bsnW_afr n _ _ _ _ _, consW_afr]

/-! ## `block_member_counts` -/

theorem recTW_afr : ∀ (n : Nat) (m m' : Mem) (no nl mI ty : Word) (r : List Word),
    recTW n m no nl mI ty = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [recTW] at h
  | n + 1, m, m', no, nl, mI, ty, r, h => by
    simp only [recTW, recTK1.eq_def, recTK2.eq_def, recTK3.eq_def, recTK4.eq_def, recTK5.eq_def] at h
    afr_auto h [stripF_afr, gafF_afr]

theorem bchW_afr : ∀ {n : Nat} {m m' : Mem} {cvT : Word} {r : List Word},
    bchW n m cvT = some (r, m') → AFr m m'
  | 0, _, _, _, _, h => by simp [bchW] at h
  | n + 1, m, m', cvT, r, h => by
    simp only [bchW, bchW.bchK1.eq_def, bchW.bchK2.eq_def] at h
    afr_auto h [piBW_afr _ _ _ _ _ _]

theorem bcW_afr : ∀ {n : Nat} {m m' : Mem} {nPd k nC nR cvT rOk rMI rRP : Word} {r : List Word},
    bcW n m nPd k nC nR cvT rOk rMI rRP = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by simp [bcW] at h
  | n + 1, m, m', nPd, k, nC, nR, cvT, rOk, rMI, rRP, r, h => by
    simp only [bcW, bcK.eq_def] at h
    afr_auto h [bchW_afr]

theorem bmfW_afr : ∀ (n : Nat) (m m' : Mem) (no nl ro rl mm : Word) (r : List Word),
    bmfW n m no nl ro rl mm = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [bmfW.eq_1] at h
  | n + 1, m, m', no, nl, ro, rl, mm, r, h => by
    simp only [bmfW.eq_2, bmfW.k_rec_target_of.eq_def, bmfW.k_block_member_counts_find.eq_def] at h
    afr_auto h [bmfW_afr n _ _ _ _ _ _ _ _, recTW_afr n _ _ _ _ _ _ _]

theorem bmgW_afr : ∀ (n : Nat) (m m' : Mem) (nPd k nC no nl ro rl cto ctl idx : Word) (r : List Word),
    bmgW n m nPd k nC no nl ro rl cto ctl idx = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [bmgW] at h
  | n + 1, m, m', nPd, k, nC, no, nl, ro, rl, cto, ctl, idx, r, h => by
    simp only [bmgW, bmgK1.eq_def, bmgK2.eq_def, bmgK3.eq_def, bsK3.eq_def] at h
    afr_auto h [bmgW_afr n _ _ _ _ _ _ _ _ _ _ _ _ _, bmfW_afr n _ _ _ _ _ _ _ _, bcW_afr, consW_afr]

theorem bmcW_afr {n : Nat} {m m' : Mem} {nPd k nC no nl ro rl cto ctl : Word} {r : List Word}
    (h : bmcW n m nPd k nC no nl ro rl cto ctl = some (r, m')) : AFr m m' := by
  simp only [bmcW, bmfK2.eq_def] at h
  afr_auto h [bmgW_afr n _ _ _ _ _ _ _ _ _ _ _ _ _]

/-! ## `block_shape_pins_ok` -/

theorem bpfW_afr : ∀ (n : Nat) (m m' : Mem) (cto ctl lo ll : Word) (r : List Word),
    bpfW n m cto ctl lo ll = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [bpfW] at h
  | n + 1, m, m', cto, ctl, lo, ll, r, h => by
    simp only [bpfW, bpfK1.eq_def, bpfK2.eq_def, bpfK3.eq_def, pinK4.eq_def] at h
    afr_auto h [bpfW_afr n _ _ _ _ _ _ _, erToIwW_afr]

theorem bprW_afr : ∀ (n : Nat) (m m' : Mem) (ro rl : Word) (r : List Word),
    bprW n m ro rl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [bprW] at h
  | n + 1, m, m', ro, rl, r, h => by
    simp only [bprW, pinK4.eq_def] at h
    afr_auto h [bprW_afr n _ _ _ _ _]

theorem bpcW_afr : ∀ (n : Nat) (m m' : Mem) (nP cso csl lo ll : Word) (r : List Word),
    bpcW n m nP cso csl lo ll = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [bpcW] at h
  | n + 1, m, m', nP, cso, csl, lo, ll, r, h => by
    simp only [bpcW, bpcK1.eq_def, bpcK2.eq_def, bpcK3.eq_def, pinK4.eq_def] at h
    afr_auto h [bpcW_afr n _ _ _ _ _ _ _ _, erToIwW_afr]

theorem bpoW_afr {n : Nat} {m m' : Mem} {nP cto ctl lo ll ro rl cso csl : Word} {r : List Word}
    (h : bpoW n m nP cto ctl lo ll ro rl cso csl = some (r, m')) : AFr m m' := by
  simp only [bpoW] at h
  afr_auto h [bpfW_afr n _ _ _ _ _ _ _, bprW_afr n _ _ _ _ _, bpcW_afr n _ _ _ _ _ _ _ _]

/-! ## `block_shape_result_sort` -/

theorem bsoW_afr {m m' : Mem} {nP io il ty : Word} {r : List Word}
    (h : bsoW m nP io il ty = some (r, m')) : AFr m m' := by
  simp only [bsoW, bsoK1.eq_def, bsoK2] at h
  afr_auto h [stripF_afr]

end L.Ind
