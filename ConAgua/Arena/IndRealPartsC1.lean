module

import ConAgua.Arena.IndRealAbsPos
public import ConAgua.Arena.IndPartsSpec.BmgW
public import ConAgua.Arena.IndPartsSpec.BmoW
public import ConAgua.Arena.IndPartsSpec.BpcW
public import ConAgua.Arena.IndPartsSpec.BsoK2
import ConAgua.Arena.RecClassSpec.Classes

@[expose] public section

/-!
# `readBlock` under `StageC`, part 1: the walk memos across `read_block`'s first callees
(lane `indproofs4`, helper `bpc`)

`AbsOK` across the models of the callees `block_shape` runs before `lvl_eq_c` (`block_split`,
`block_shape_names_of`, `block_member_counts`, `er_to_iw`, the three tests,
`block_shape_result_sort`): they write the record pool and `EREC` only (`afr_auto`). `lvl_eq_c`'s
real refinement (`lvlEqC_simC`) needs `StageC` at the call, whose memory half is `AbsOK`'s.
-/


open ConRon.Arena

namespace L.Ind

open L.Arena

/-! ## `block_split` -/

theorem bsrW_afr : ∀ (n : Nat) (m m' : Mem) (off l : Word) (r : List Word),
    bsrW n m off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [bsrW.eq_1] at h
  | n + 1, m, m', off, l, r, h => by
    simp only [bsrW.eq_2, bsrW.k_block_split_recs.eq_def, bsrW.k_rec6.eq_def,
      bsrW.k_sl_cons.eq_def] at h
    afr_auto h [bsrW_afr n _ _ _ _ _, posRecW_afr, consW_afr]

theorem bscW_afr : ∀ (n : Nat) (m m' : Mem) (off l : Word) (r : List Word),
    bscW n m off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [bscW.eq_1] at h
  | n + 1, m, m', off, l, r, h => by
    simp only [bscW.eq_2, bscW.k_block_split_ctors.eq_def, bscW.k_rec3.eq_def, bscW.k_sl_cons.eq_def,
      bscW.k_block_split_recs.eq_def] at h
    afr_auto h [bscW_afr n _ _ _ _ _, bsrW_afr n _ _ _ _ _, posRecW_afr, consW_afr]

theorem bsW_afr : ∀ (n : Nat) (m m' : Mem) (off l : Word) (r : List Word),
    bsW n m off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, h => by simp [bsW.eq_1] at h
  | n + 1, m, m', off, l, r, h => by
    simp only [bsW.eq_2, bsW.k_block_split.eq_def, bsW.k_sl_cons.eq_def, bsW.k_rec6.eq_def,
      bsW.k_rec6_2.eq_def, bsW.k_block_split_ctors.eq_def] at h
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
    simp only [recTW, recTW.k_strip_pis.eq_def, recTW.k_get_app_fn_f.eq_def, recTW.k_sl_find.eq_def] at h
    afr_auto h [stripF_afr, gafF_afr]

theorem bchW_afr : ∀ {n : Nat} {m m' : Mem} {cvT : Word} {r : List Word},
    bchW n m cvT = some (r, m') → AFr m m'
  | 0, _, _, _, _, h => by simp [bchW] at h
  | n + 1, m, m', cvT, r, h => by
    simp only [bchW, bchW.k_pi_binders.eq_def] at h
    afr_auto h [piBW_afr _ _ _ _ _ _]

theorem bcW_afr : ∀ {n : Nat} {m m' : Mem} {nPd k nC nR cvT rOk rMI rRP : Word} {r : List Word},
    bcW n m nPd k nC nR cvT rOk rMI rRP = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by simp [bcW] at h
  | n + 1, m, m', nPd, k, nC, nR, cvT, rOk, rMI, rRP, r, h => by
    simp only [bcW, bcW.k_block_counts_head.eq_def, bcW.k_block_counts_pure.eq_def] at h
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
    simp only [bmgW, bmgW.k_block_member_counts_find.eq_def, bmgW.k_block_counts.eq_def,
      bmgW.k_block_member_counts_go.eq_def, bmgW.k_sl_cons.eq_def] at h
    afr_auto h [bmgW_afr n _ _ _ _ _ _ _ _ _ _ _ _ _, bmfW_afr n _ _ _ _ _ _ _ _, bcW_afr, consW_afr]

theorem bmcW_afr {n : Nat} {m m' : Mem} {nPd k nC no nl ro rl cto ctl : Word} {r : List Word}
    (h : bmcW n m nPd k nC no nl ro rl cto ctl = some (r, m')) : AFr m m' := by
  simp only [bmcW, bmcW.k_block_member_counts_go.eq_def] at h
  afr_auto h [bmgW_afr n _ _ _ _ _ _ _ _ _ _ _ _ _]

/-! ## `readBlock`'s three tests -/

theorem floW_afr : ∀ (n : Nat) (m m' : Mem) (cto ctl lo ll : Word) (r : List Word),
    floW n m cto ctl lo ll = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [floW] at h
  | n + 1, m, m', cto, ctl, lo, ll, r, h => by
    simp only [floW, floW.k_er_to_iw.eq_def, floW.k_sl_eq.eq_def, floW.k_formers_lps_ok.eq_def] at h
    afr_auto h [floW_afr n _ _ _ _ _ _ _, erToIwW_afr]

theorem cpoW_afr : ∀ (n : Nat) (m m' : Mem) (nP cso csl : Word) (r : List Word),
    cpoW n m nP cso csl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [cpoW] at h
  | n + 1, m, m', nP, cso, csl, r, h => by
    simp only [cpoW, cpoW.k_ctors_params_ok.eq_def] at h
    afr_auto h [cpoW_afr n _ _ _ _ _ _]

theorem cloW_afr : ∀ (n : Nat) (m m' : Mem) (cso csl lo ll : Word) (r : List Word),
    cloW n m cso csl lo ll = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [cloW] at h
  | n + 1, m, m', cso, csl, lo, ll, r, h => by
    simp only [cloW, cloW.k_er_to_iw.eq_def, cloW.k_sl_eq.eq_def, cloW.k_ctors_lps_ok.eq_def] at h
    afr_auto h [cloW_afr n _ _ _ _ _ _ _, erToIwW_afr]

/-! ## `block_shape_result_sort` -/

theorem bsoW_afr {m m' : Mem} {nP io il ty : Word} {r : List Word}
    (h : bsoW m nP io il ty = some (r, m')) : AFr m m' := by
  simp only [bsoW, bsoW.k_strip_pis.eq_def, bsoW.k_pin_word.eq_def] at h
  afr_auto h [stripF_afr]

end L.Ind
