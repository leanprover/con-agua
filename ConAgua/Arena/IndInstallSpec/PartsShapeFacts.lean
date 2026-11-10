module

import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
public import ConAgua.Arena.IndSumSpec.ColW
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.RecClassSpec.CloseLams
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.IndInstall
public import ConAgua.Arena.IndPartsSpec.MemberNames
public import ConAgua.Arena.IndPartsSpec.RulePrefixAt
public import ConAgua.Arena.IndPosSpec.CtxFields
import all ConAgua.Arena.IndParts
import ConAgua.Arena.LdRd
import ConAgua.L.ModelGen

@[expose] public section

/-!
# PartsShapeFacts

`nctxMem`, `nctxMem_eq`, `partsNctx_eq`, `nckRec`, `nckW`, `NckProg` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_shape_formers` (`BlockShape.formers`), through `member_field_copy` -/

/-- **`member_field_copy(d, s, l, k)`'s model `fieldCopyW`** (generated): `IW[d + j] := IW[IW[s + j] + k]`. -/
l_model memberFieldCopy_spec (p : Prog) (hp : p.lookup "member_field_copy" = some memberFieldCopy)
  fns [hp ↦ fieldCopyW void]
  grind [arena_grind] extra [ld64_rd_spec] simp []

/-- `fieldCopyW`'s copy step, the recursive call's memory passed on. -/
theorem fieldCopyW_step (n : Nat) (m : Mem) (d s l k : Word) (hl : l ≠ 0) :
    fieldCopyW (n + 1) m d s l k =
      fieldCopyW n (m.set64 IW d (rdW (m.arr64 IW) (rdW (m.arr64 IW) s + k))) (d + 1) (s + 1) (l - 1) k := by
  rw [fieldCopyW.arm2 (hc1 := hl)]; cases fieldCopyW n _ _ _ _ _ <;> rfl

/-- **What `member_field_copy` leaves**: word `k` of each member record, the records below `d`. -/
theorem fieldCopyW_get (n : Nat) (k : Word) : ∀ (m m' : Mem) (d s l : Word), fieldCopyW n m d s l k = some m' →
    s.toNat + l.toNat ≤ d.toNat → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ j < l.toNat, (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + j)) + k).toNat < d.toNat) →
    (∀ b : TieredArray, b ≠ ↑IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat
      then some (rdW (m.arr64 IW) (rdW (m.arr64 IW) (UInt64.ofNat (s.toNat + (i - d.toNat))) + k))
      else (m.arr64 IW)[i]? :=
  ipCopyW_get (fun n m d s l => fieldCopyW n m d s l k) (fun m x => rdW (m.arr64 IW) (x + k))
    (fun x d => (x + k).toNat < d)
    (fun _ _ _ _ => by simp [fieldCopyW]) (fieldCopyW.arm1 · · · · · k) (fieldCopyW_step · · · · · k)
    (fun m d v x hx => rdW_set64_IW_ne m d v (x + k) (by omega))
    (fun _ _ h => by omega) n

/-- The model of `block_shape_formers(p)` (its copy at `n - 1`). -/
def formersW (n : Nat) (m : Mem) (p : Word) : Option (List Word × Mem) :=
  match allocW m (rdW (m.arr64 IW) (p + 1)) with
  | none => none
  | some (q, m1) =>
    match fieldCopyW (n - 1) m1 q (rdW (m1.arr64 IW) p) (rdW (m1.arr64 IW) (p + 1)) 0 with
    | none => none
    | some m2 => some ([q, rdW (m2.arr64 IW) (p + 1)], m2)

theorem blockShapeFormers_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "member_field_copy" = some memberFieldCopy)
    (hp : p.lookup "block_shape_formers" = some blockShapeFormers) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_formers" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ formersW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeFormers]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hmod : ∀ a m1 m2, allocW s₀.mem (rdW (s₀.mem.arr64 IW) (q + 1)) = some (a, m1) →
        fieldCopyW n m1 a (rdW (m1.arr64 IW) q) (rdW (m1.arr64 IW) (q + 1)) 0 = some m2 →
        formersW (n + 1) s₀.mem q = some ([a, rdW (m2.arr64 IW) (q + 1)], m2) := by
      intro a m1 m2 h1 h2
      simp [formersW, h1, h2]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n, memberFieldCopy_spec p hc n] <;>
      finish (gen := 20)

/-- A slice of record pointers below the top is decoded below the tops. -/
theorem decPLcv_decB {m : Mem} {o l : Nat} {xs : List IConstantVal}
    (h : decPL m (decCVp m) o l = some xs) (hb : o + l ≤ iwTop m) :
    DecB (fun m => decPL m (decCVp m) o l) m xs := by
  show decPL (truncM m) (decCVp (truncM m)) o l = some xs
  have he : decCVp (truncM m) = decCVp m := by funext q; simp only [decCVp, truncM_erA]
  rw [he]
  unfold decPL at *
  rw [← h]
  refine mapM_congr_range _ fun j hj => ?_
  have : j < l := List.mem_range.mp hj
  rw [iwN_truncM (by omega)]

/-- **`block_shape_formers` is `BlockShape.formers`**: the new `IW` slice holds the members'
former pointers (word 0 of each member record). -/
theorem formersW_dec {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : formersW n m p = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hq : decBS m p.toNat = some bs)
    (hpt : p.toNat + 9 ≤ iwTop m)
    (hsrc : ∀ o l, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → o + l ≤ iwTop m)
    (hptr : ∀ o l j v, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v < iwTop m) :
    r = [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
    decPL m' (decCVp m') (rdW (m.arr64 CTL) 200).toNat bs.k = some bs.formers ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop m' ∧ iwTop m' ≤ (m.arr64 IW).size := by
  have htl : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).1
  have hlen := decPL_length m hg
  have hk : bs.k = l := by rw [BlockShape.k, hlen]
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (p.toNat + 1) = p + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have e1' : (p + 1).toNat = p.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [ofNat_toNat_word] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := by simp [hob]
  have hll : (UInt64.ofNat l).toNat = l := by simp [hlb]
  have hsrc' := hsrc o l ho hl
  unfold formersW at h
  rw [hl'] at h
  rcases hal : allocW m (UInt64.ofNat l) with _ | ⟨q, m1⟩
  · simp [hal] at h
  obtain ⟨hq', hm1, hroom⟩ := allocW_facts hal hsz
  rw [hll] at hroom
  simp only [hal] at h
  subst hq' hm1
  have hIW := allocMem_IW m (UInt64.ofNat l)
  rw [hIW, ho', hl'] at h
  rcases hcp : fieldCopyW (n - 1) (allocMem m (UInt64.ofNat l)) (rdW (m.arr64 CTL) 200)
      (UInt64.ofNat o) (UInt64.ofNat l) 0 with _ | m2
  · simp [hcp] at h
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hptr' : ∀ j < (UInt64.ofNat l).toNat,
      (rdW ((allocMem m (UInt64.ofNat l)).arr64 IW) (UInt64.ofNat ((UInt64.ofNat o).toNat + j)) + 0).toNat
        < q.toNat := by
    intro j hj
    rw [hll] at hj
    obtain ⟨v, y, hv, -, -⟩ := decPL_get l o bs.members hg j hj
    have hvb := hptr o l j v ho hl hj hv
    obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
    rw [hIW, hoo, hv', UInt64.add_zero]
    simp only [iwTop, hqq] at hvb
    rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]; exact hvb
  obtain ⟨hA, hS, hG⟩ := fieldCopyW_get (n - 1) 0 _ _ _ _ _ hcp
    (by rw [hoo, hll]; simp only [iwTop, hqq] at hsrc'; omega)
    (by rw [hIW, hll]; exact hroom) (by rw [hIW]; exact hsz) hptr'
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m _).trans (copy_frame hA (by rw [hS, hIW]))
  have htop : rdW (m2.arr64 CTL) 200 = q + UInt64.ofNat l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + UInt64.ofNat l).toNat = q.toNat + l := by
    rw [UInt64.toNat_add]; simp [hll]; omega
  have hER : erecP m2 = erecP m := erecP_frame hfr (by decide) (by decide) (by decide) (by decide)
  have hCV : decCVp m2 = decCVp m := by funext a; simp only [decCVp, erA, hER]
  have hqt : iwTop m = q.toNat := by simp only [iwTop, hqq]
  refine ⟨?_, ?_, ?_, hfr, ?_, ?_⟩
  · have : rdW (m2.arr64 IW) (p + 1) = UInt64.ofNat l := by
      rw [← hl']; simp only [rdW]; rw [hG, ite_eq_right (by rw [e1']; omega)]
    rw [this, hk]
  · rw [hk, hCV]
    have hxs : bs.formers.length = l := by simp [BlockShape.formers, hlen]
    have := decPL_of_get (m := m2) (decCVp m) bs.formers q.toNat (fun j hj => by
      have hj' : j < l := by omega
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get l o bs.members hg j hj'
      obtain ⟨⟨a, hva, hcv⟩, -, -⟩ := decMS_some hy
      have hGj := hG (q.toNat + j)
      rw [ite_eq_left (by rw [hll]; omega)] at hGj
      have e2 : q.toNat + j - q.toNat = j := by omega
      rw [e2, hoo] at hGj
      have hvb := hptr o l j v ho hl hj' hv
      obtain ⟨hv', -⟩ := iwN_rdW hv (by omega)
      rw [hv', UInt64.add_zero] at hGj
      obtain ⟨hva', hab⟩ := iwN_rdW hva (by omega)
      rw [hva'] at hGj
      have hy' : bs.members[j]'(by omega) = y := by
        simpa [List.getElem?_eq_getElem (show j < bs.members.length by omega)] using hget
      refine ⟨a, ?_, ?_⟩
      · simp only [iwN, nat?, iwA, aread_apply, hGj, Option.map_some]
        rw [UInt64.toNat_ofNat_of_lt' hab]
      · simp [BlockShape.formers, List.getElem_map, hy', hcv])
    rw [hxs] at this
    exact this
  · refine iwGrow_of_frame hfr (N := UInt64.ofNat l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq, hll]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  · simp only [iwTop, htop, hsum, hk]
  · simp only [iwTop, htop, hsum]; omega

/-- The memory after `block_shape_nest_ctx`'s thirteen writes. -/
def nctxMem (m : Mem) (a b c d e f g h i j k l o : Word) : Mem :=
  let q := rdW (m.arr64 CTL) 200
  (((((((((((((allocMem m 13).set64 IW q a).set64 IW (q + 1) b).set64 IW (q + 2) c).set64 IW (q + 3) d).set64
    IW (q + 4) e).set64 IW (q + 5) f).set64 IW (q + 6) g).set64 IW (q + 7) h).set64 IW (q + 8) i).set64
    IW (q + 9) j).set64 IW (q + 10) k).set64 IW (q + 11) l).set64 IW (q + 12) o

theorem nctxMem_eq (m : Mem) (a b c d e f g h i j k l o : Word) :
    nctxMem m a b c d e f g h i j k l o =
      wrIW (allocMem m 13) (rdW (m.arr64 CTL) 200) [a, b, c, d, e, f, g, h, i, j, k, l, o] := by
  simp [nctxMem, wrIW, UInt64.add_assoc]

theorem partsNctx_eq (m : Mem) (a b c d e f g h i j k l o : Word) :
    (match allocW m 13 with | none => none | some (q, _) => some (q, nctxMem m a b c d e f g h i j k l o)) =
      posRecW m [a, b, c, d, e, f, g, h, i, j, k, l, o] := by
  rw [posRecW_eq m _ 13 rfl, nctxMem_eq]; cases allocW m 13 <;> rfl

/-- After `param_levels`: the formers, then the record (`np`, `srt` read before the formers). -/
def nckRec (n : Nat) (p fo fl : Word) (r1 r2 r3 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    match formersW n m4 p with
    | none => none
    | some (r5, m5) =>
      match allocW m5 13 with
      | none => none
      | some (q, _) => some ([q], nctxMem m5 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)
          (rdW (m4.arr64 IW) (p + 4)) (r3.headD 0) (r3.tail.headD 0) fo fl (rdW (m4.arr64 IW) (p + 6)) (r4.headD 0)
          (r5.headD 0) (r5.tail.headD 0))

/-- **The model of `block_shape_nest_ctx`** (at exec fuel `n + 1`). -/
def nckW (n : Nat) (m : Mem) (p fo fl : Word) : Option (List Word × Mem) :=
  match memberNamesW n m p with
  | none => none
  | some (r1, m1) =>
    match lpsW n m1 p with
    | none => none
    | some (r2, m2) =>
      match nIdxsW n m2 p with
      | none => none
      | some (r3, m3) => nckRec n p fo fl r1 r2 r3 (plW n m3 (r2.headD 0) (r2.tail.headD 0))

/-- The lookups of `BlockShape.nestCtx` (and `param_levels`). -/
structure NckProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  slGet : p.lookup "sl_get" = some slGet
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  plGo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  namesCopy : p.lookup "member_names_copy" = some memberNamesCopy
  names : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  nIdxsCopy : p.lookup "n_idxs_copy" = some nIdxsCopy
  nIdxs : p.lookup "block_shape_n_idxs" = some blockShapeNIdxs
  nctx : p.lookup "block_shape_nest_ctx" = some blockShapeNestCtx
  fieldCopy : p.lookup "member_field_copy" = some memberFieldCopy
  formers : p.lookup "block_shape_formers" = some blockShapeFormers

/-! ## The shape record's members, below the tops -/

/-- What the projections' lemmas ask of a shape record decoded below the tops whose members' slice
lies below the top. -/
theorem partsShapeFacts {m : Mem} {q : Word} {bs : BlockShape}
    (hq : DecB (fun m => decBS m q.toNat) m bs)
    (_hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m) :
    decBS m q.toNat = some bs ∧ q.toNat + 9 ≤ iwTop m ∧
    (∀ o l j v, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v + 1 < iwTop m) := by
  have hqt : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, hpr⟩ := decBS_some hqt
  have hq8 : q.toNat + 8 < iwTop m := by
    simp only [iwB, bool?, Option.map_eq_some_iff] at hpr
    obtain ⟨w, hw, -⟩ := hpr
    exact (truncM_iw_get hw).1
  refine ⟨hq.get (decBS_mono _), by omega, ?_⟩
  obtain ⟨o, l, ho, hl, hdm, -⟩ := partsAt decMS_mono hmem
  have hoN : iwN m q.toNat = some o.toNat := by rw [← iwN_truncM (by omega)]; exact ho
  have hlN : iwN m (q.toNat + 1) = some l.toNat := by rw [← iwN_truncM (by omega)]; exact hl
  intro o' l' j v h1 h2 hj hv
  rw [hoN] at h1; rw [hlN] at h2
  simp only [Option.some.injEq] at h1 h2; subst h1 h2
  obtain ⟨v', hv', hms⟩ := decPL_getH (truncM m) (show decPL _ _ _ _ = _ from hdm) j hj
  have hlt := partsIwLt hv'
  rw [iwN_truncM hlt, hv] at hv'
  simp only [Option.some.injEq] at hv'; subst hv'
  obtain ⟨-, ⟨a, ha, -⟩, -⟩ := decMS_some hms
  have := partsIwLt ha; omega

/-- The members' count word of a decoded shape record. -/
theorem partsShapeK {m : Mem} {q : Word} {bs : BlockShape} (hq : decBS m q.toNat = some bs)
    (hb : q.toNat + 9 ≤ iwTop m) : rdW (m.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have := decBS_k hq (by omega)
  rwa [show UInt64.ofNat (q.toNat + 1) = q + 1 from by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp] at this

theorem partsHsrc_grow {m m' : Mem} (hg : IWGrow m m') {q : Word} (hq9 : q.toNat + 9 ≤ iwTop m)
    (hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m) :
    ∀ o l, iwN m' q.toNat = some o → iwN m' (q.toNat + 1) = some l → o + l ≤ iwTop m' := by
  intro o l h1 h2
  have e1 : iwN m' q.toNat = iwN m q.toNat := by simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet _ (by omega)]
  have e2 : iwN m' (q.toNat + 1) = iwN m (q.toNat + 1) := by simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet _ (by omega)]
  rw [e1] at h1; rw [e2] at h2
  exact Nat.le_trans (hsrc o l h1 h2) hg.iw

/-- The record's words read off a decoded shape (`nP`, `resSort`), in a grown memory. -/
theorem partsShapeWords {m m' : Mem} (hg : IWGrow m m') {q : Word} {bs : BlockShape}
    (hq : DecB (fun m => decBS m q.toNat) m bs) (hq9 : q.toNat + 9 ≤ iwTop m) :
    rdW (m'.arr64 IW) (q + 4) = UInt64.ofNat bs.nP ∧ bs.nP < 2 ^ 64 ∧
      H (rdW (m'.arr64 IW) (q + 6)) ∧ decI (rdW (m'.arr64 IW) (q + 6)) = bs.resSort := by
  have hqt : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨-, -, hnp, -, hsort, -, -⟩ := decBS_some hqt
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have h4 : (q + 4).toNat = q.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have h6 : (q + 6).toNat = q.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hw4, hnb, -⟩ := partsIwRd hnp h4
  rw [rdW_iw_grow hg (by omega)]
  refine ⟨hw4, hnb, ?_⟩
  obtain ⟨w, hw, hwl, hwe⟩ := hd?_some (show hd? (iwA (truncM m)) (q.toNat + 6) = some bs.resSort from hsort)
  obtain ⟨-, hw'⟩ := truncM_iw_get hw
  simp only [iwA, aread_apply, aread_apply] at hw'
  rw [rdW_iw_grow hg (by omega), rdW_of_get? h6.symm hw']
  exact ⟨hwl, hwe.symm⟩

end L.Ind

end
