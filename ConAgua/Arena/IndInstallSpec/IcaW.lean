module

public import ConAgua.Arena.IndInstallSpec.IcbiW
import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndSumSpec.ConsSumCtors
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.PartsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.RecClassSpec.MjProg
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndInstallSpec.BlockCapsAt
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConRon.Arena.Inductives.BlockInstall
public import ConRon.Bridge.Inductives.Install
import all ConAgua.Arena.IndInstall
import ConAgua.Arena.LdRd
public import ConAgua.Arena.RecLayout.CapsDec
import ConAgua.L.ModelGen
import ConAgua.Arena.RecClassSpec.CloseLams
public import ConAgua.Arena.IndInstallSpec.MemberNZ

@[expose] public section

/-!
# IcaW

The generated models of `block_caps_head`, `block_caps_one`, `block_caps_fin`, `block_caps_at`, `er_put_ci`
and `ind_info_rec`, and their refinements (`blockCapsAt_ok`, `iirW_stage`, `consBlockInds_refines`).
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The word models (generated) -/

l_model capsHead_spec (p : Prog) (hp : p.lookup "block_caps_head" = some blockCapsHead)
  fns [hp ↦ capsHead ro list]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model capsOne_spec (p : Prog) (hp : p.lookup "block_caps_one" = some blockCapsOne)
  fns [hp ↦ capsOne ro list]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model icf_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "block_caps_fin" = some blockCapsFin)
  fns [hp ↦ icfW list]
  specs [callW_spec p n "block_shape_member_names", callW_spec p n "block_caps_at_er_copy",
    callW_spec p n "block_caps_ctor_names", iwAlloc_specW p ha n]
  grind [arena_grind] extra [ld64_rd_spec] simp []

l_model ica_spec (p : Prog) (hp : p.lookup "block_caps_at" = some blockCapsAt)
  fns [hp ↦ icaW list]
  specs [callW_spec p n "member_never_zero", callW_spec p n "block_caps_head", callW_spec p n "block_caps_one",
    callW_spec p n "block_caps_fin"]
  grind [arena_grind] simp []

end L.Ind

end

end

section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A handle slice of the record pool in use (both tiers, below their tops: `erA`). -/
def ESl (m : Mem) (o l : Word) (xs : List NIdx) : Prop :=
  hslice? (erA m) o.toNat l.toNat = some xs

theorem ESl.grow {m m' : Mem} {o l : Word} {xs : List NIdx} (h : ESl m o l xs) (hg : IWGrow m m') :
    ESl m' o l xs := by
  exact hg.erecGrow.ext.hslice? h

theorem ctorNamesW_room {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : ctorNamesW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    iwTop m + l.toNat ≤ (m.arr64 IW).size := by
  unfold ctorNamesW at h
  cases hal : allocW m l with
  | none => rw [hal] at h; cases h
  | some x =>
    obtain ⟨hq, -, hr⟩ := allocW_facts hal hsz
    simp only [iwTop]; rw [hq] at hr; exact hr

/-- An `EREC` copy of an `IW` handle slice, under the stage relation. -/
theorem installErCopy {p : Prog} (hP : CapsProg p) {n : Nat}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {o l : Word} {r : List Word} {xs : List NIdx}
    (h : callW p n "block_caps_at_er_copy" [o, l] m = some (r, m')) (hS : StageR vis fe m a)
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ ESl m' (r.headD 0) (r.tail.headD 0) xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockCapsAtErCopy_spec p hP.erAlloc hP.erCopyGo hP.erPut hP.erCopy n _ o l) h
  simp only at hW
  obtain ⟨q, m1, ha, rfl, hm'⟩ := capsErCopyW_post hW
  rw [hm']
  obtain ⟨hS', hg, -, -, -, -, hW3⟩ := erRec_stage ha hS _ (ieWords_length _ _ _).symm
  refine ⟨hS', hg, ?_⟩
  simp only [List.headD_cons, List.tail_cons, ESl]
  have hI := hS.iw.iw
  rw [← (show hslice? (iwA m) o.toNat l.toNat = some xs from hd)]; unfold hslice?
  refine mapM_congr_range _ fun j hj => ?_
  have hj' : j < l.toNat := List.mem_range.mp hj
  have h3 := hW3 j (by rw [ieWords_length]; exact hj')
  rw [ieWords_get _ _ _ _ hj'] at h3
  have hin : o.toNat + j < (m.arr64 IW).size := by omega
  have hoj : (o + UInt64.ofNat j).toNat = o.toNat + j := by
    have := hS.iw.iwSize; simp [UInt64.toNat_add]; omega
  simp only [hd?, erA, h3, iwA, aread_apply, rdW, hoj, Array.getElem?_eq_getElem hin, Option.getD_some]

/-- **A capability record written field by field at a fresh `IW` allocation**
(`block_caps_fin`'s last statements): the stage relation kept, the pool grown, the record's words
(`CapsRecW`) at the old top. -/
theorem capsFin_rec {vis : Word} {fe : IFEnv} {a : AState} {m m5 : Mem}
    {q w0 w1 w2 w3 w4 w5 w6 w7 : Word} (ha : allocW m Caps.size = some (q, m5))
    (hS : StageR vis fe m a) :
    StageR vis fe ((((((((m5.set64 IW (q + Caps.eta) w0).set64 IW (q + Caps.nIdx) w1).set64 IW
      (q + Caps.neverZero) w2).set64 IW (q + Caps.allOff) w3).set64 IW (q + Caps.allLen) w4).set64 IW
      (q + Caps.nparams) w5).set64 IW (q + Caps.ctorsOff) w6).set64 IW (q + Caps.ctorsLen) w7) a ∧
    IWGrow m ((((((((m5.set64 IW (q + Caps.eta) w0).set64 IW (q + Caps.nIdx) w1).set64 IW
      (q + Caps.neverZero) w2).set64 IW (q + Caps.allOff) w3).set64 IW (q + Caps.allLen) w4).set64 IW
      (q + Caps.nparams) w5).set64 IW (q + Caps.ctorsOff) w6).set64 IW (q + Caps.ctorsLen) w7) ∧
    q.toNat = iwTop m ∧
    iwTop ((((((((m5.set64 IW (q + Caps.eta) w0).set64 IW (q + Caps.nIdx) w1).set64 IW
      (q + Caps.neverZero) w2).set64 IW (q + Caps.allOff) w3).set64 IW (q + Caps.allLen) w4).set64 IW
      (q + Caps.nparams) w5).set64 IW (q + Caps.ctorsOff) w6).set64 IW (q + Caps.ctorsLen) w7) =
      iwTop m + Caps.size.toNat ∧
    CapsRecW (iwA ((((((((m5.set64 IW (q + Caps.eta) w0).set64 IW (q + Caps.nIdx) w1).set64 IW
      (q + Caps.neverZero) w2).set64 IW (q + Caps.allOff) w3).set64 IW (q + Caps.allLen) w4).set64 IW
      (q + Caps.nparams) w5).set64 IW (q + Caps.ctorsOff) w6).set64 IW (q + Caps.ctorsLen) w7))
      q.toNat w0 w1 w2 w3 w4 w5 w6 w7 := by
  obtain ⟨hS5, hg5, hq, ht5⟩ := allocW_stage ha hS
  have hb := hS5.iw.iw
  have h64 := hS5.iw.iwSize
  have hsz5 : (m5.arr64 IW).size = (m.arr64 IW).size := (allocW_facts ha hS.iw.iwSize).2.1 ▸ by
    rw [allocMem_IW]
  have e : ∀ f : Word, f.toNat < Caps.size.toNat → (q + f).toNat = q.toNat + f.toNat := fun f hf => by
    rw [UInt64.toNat_add]; omega
  have hk : ∀ f : Word, f.toNat < Caps.size.toNat → iwTop m ≤ (q + f).toNat := fun f hf => by
    rw [e f hf]; omega
  have hf : MemFrame [IW] [200] m5 ((((((((m5.set64 IW (q + Caps.eta) w0).set64 IW (q + Caps.nIdx) w1).set64 IW
      (q + Caps.neverZero) w2).set64 IW (q + Caps.allOff) w3).set64 IW (q + Caps.allLen) w4).set64 IW
      (q + Caps.nparams) w5).set64 IW (q + Caps.ctorsOff) w6).set64 IW (q + Caps.ctorsLen) w7) := by
    refine MemFrame.mono (A := [IW]) (C := []) ?_ (by simp) (by simp)
    refine MemFrame.trans ?_ (MemFrame.set64 _ IW (by decide) _ _)
    refine MemFrame.trans ?_ (MemFrame.set64 _ IW (by decide) _ _)
    refine MemFrame.trans ?_ (MemFrame.set64 _ IW (by decide) _ _)
    refine MemFrame.trans ?_ (MemFrame.set64 _ IW (by decide) _ _)
    refine MemFrame.trans ?_ (MemFrame.set64 _ IW (by decide) _ _)
    refine MemFrame.trans ?_ (MemFrame.set64 _ IW (by decide) _ _)
    refine MemFrame.trans ?_ (MemFrame.set64 _ IW (by decide) _ _)
    exact MemFrame.set64 _ IW (by decide) _ _
  have htop : iwTop ((((((((m5.set64 IW (q + Caps.eta) w0).set64 IW (q + Caps.nIdx) w1).set64 IW
      (q + Caps.neverZero) w2).set64 IW (q + Caps.allOff) w3).set64 IW (q + Caps.allLen) w4).set64 IW
      (q + Caps.nparams) w5).set64 IW (q + Caps.ctorsOff) w6).set64 IW (q + Caps.ctorsLen) w7) =
      iwTop m5 := by
    simp [iwTop, rdW_set64, show (CTL : TieredArray) ≠ IW by decide]
  refine ⟨stage_frame_iw hS5 hf (by rw [htop]; exact hb), ?_, hq, by rw [htop, ht5], ?_⟩
  · exact ((((((((hg5.set_iw _ _ (hk _ Caps.eta_lt)).set_iw _ _ (hk _ Caps.nIdx_lt)).set_iw _ _
      (hk _ Caps.neverZero_lt)).set_iw _ _ (hk _ Caps.allOff_lt)).set_iw _ _
      (hk _ Caps.allLen_lt)).set_iw _ _ (hk _ Caps.nparams_lt)).set_iw _ _
      (hk _ Caps.ctorsOff_lt)).set_iw _ _ (hk _ Caps.ctorsLen_lt))
  · exact capsRecW_set64 (m := m5) (A := IW) (by omega) (by omega)

/-- **`block_caps_fin`'s record**: the stage relation kept, the record's words at the returned pointer,
the member names and the ctor names as `EREC` slices below the record pool's top. -/
theorem icfW_ok {p : Prog} (hP : CapsProg p) {n : Nat}
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
    {pp coff clen w0 nIdx nz : Word} {r : List Word} {bs : BlockShape}
    {cs : List (IConstantVal × Nat)}
    (h : icfW p (n + 1) m pp coff clen w0 nIdx nz = some (r, m'))
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcs : PSlR decCN cs coff clen m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ ∃ aq al cq cl : Word,
      (r.headD 0).toNat + Caps.size.toNat ≤ iwTop m' ∧
      CapsRecW (iwA m') (r.headD 0).toNat w0 nIdx nz aq al (UInt64.ofNat bs.nP) cq cl ∧
      ESl m' aq al bs.memberNames ∧ ESl m' cq cl (cs.map (·.1.name)) := by
  have hsz := hS.iw.iwSize
  have hcl := hS.iw.ctl
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, hptr1⟩ := partsShapeFacts hq hsrc
  have hptr0 : ∀ o l j v, iwN m pp.toNat = some o → iwN m (pp.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v < iwTop m :=
    fun o l j v h1 h2 h3 h4 => by have := hptr1 o l j v h1 h2 h3 h4; omega
  have hkw := partsShapeK hq' hq9
  have hkb : bs.k < 2 ^ 64 := by
    have : bs.k = (UInt64.ofNat bs.k).toNat := by
      obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hq').1
      have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']
      rw [UInt64.toNat_ofNat_of_lt' this.2]
    rw [this]; exact UInt64.toNat_lt _
  rw [icfW.arm1] at h
  -- the member names
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl; rw [icfW.k_block_shape_member_names.arm1] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.alloc hP.namesCopy hP.names n _ pp) h1
  simp only at hW1; subst hs1
  obtain ⟨hr1, hd1, hg1, hf1, ht1⟩ := memberNamesW_dec hW1 hsz hcl hq' (by omega) hsrc hptr0
  have hS1 : StageR vis fe s1.mem a := stage_frame_iw hS hf1 (by
    have := memberNamesW_room hW1 hsz; rw [hkw, UInt64.toNat_ofNat_of_lt' hkb] at this
    simp only [iwTop] at this ht1 ⊢; omega)
  subst hr1
  simp only [List.headD_cons, List.tail_cons] at h
  -- their `EREC` copy
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [icfW.k_block_caps_at_er_copy.arm1] at h
  obtain ⟨hS2, hg2, hE2⟩ := installErCopy hP h2 hS1
    (by rw [UInt64.toNat_ofNat_of_lt' hkb]; exact hd1)
    (by rw [UInt64.toNat_ofNat_of_lt' hkb]; omega)
  -- the ctor names
  have hcs2 := hcs.grow decCN_mono (hg1.trans hg2)
  have hsz2 := hS2.iw.iwSize
  have hcl2 := hS2.iw.ctl
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl; rw [icfW.k_block_caps_ctor_names.arm1] at h
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (blockCapsCtorNames_spec p hP.alloc hP.namesCopy hP.ctorNames n _ coff clen) h3
  simp only at hW3; subst hs3
  have hcsd : decPL (truncM m2) (decCN (truncM m2)) coff.toNat clen.toNat = some cs := hcs2.1
  have hlen := decPL_length _ hcsd
  obtain ⟨hr3, hd3, hg3, hf3, ht3⟩ := ctorNamesW_dec hW3 hsz2 hcl2 hcs2.2 (cs.map (·.1))
    (by simp [hlen]) (fun j hj => by
      obtain ⟨v, y, hv, hy, hget⟩ := decPL_get clen.toNat coff.toNat cs hcsd j hj
      obtain ⟨⟨a', hva, hcv⟩, -⟩ := decCN_some hy
      obtain ⟨hvlt, hv'⟩ := L.Ind.iwN_truncM_some hv
      obtain ⟨hvlt2, hva'⟩ := L.Ind.iwN_truncM_some hva
      have hj' : j < cs.length := by omega
      have hy' : cs[j] = y := by simpa [List.getElem?_eq_getElem hj'] using hget
      refine ⟨v, a', hv', by omega, hva', ?_⟩
      simp only [List.getElem_map, hy']
      exact DecB.get (f := fun m => decCVp m a') (OMono.decCVp _) hcv)
  have hS3 : StageR vis fe s3.mem a := stage_frame_iw hS2 hf3 (by
    have := ctorNamesW_room hW3 hsz2; simp only [iwTop] at this ht3 ⊢; omega)
  subst hr3
  simp only [List.headD_cons, List.tail_cons, List.map_map] at h hd3
  -- their `EREC` copy
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl; rw [icfW.k_block_caps_at_er_copy_2.arm1] at h
  obtain ⟨hS4, hg4, hE4⟩ := installErCopy hP h4 hS3 hd3 (by omega)
  have hg04 := ((hg1.trans hg2).trans hg3).trans hg4
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg04 hq hq9
  rw [hnpw] at h
  -- the record
  rcases ha : allocW m4 Caps.size with _ | ⟨q, m5⟩
  · rw [ha, icfW.k_iw_alloc.none] at h; cases h
  rw [ha, icfW.k_iw_alloc.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS7, hg47, hq, ht7, hw⟩ := capsFin_rec ha hS4
  refine ⟨hS7, hg04.trans hg47, r2.headD 0, r2.tail.headD 0, r4.headD 0, r4.tail.headD 0,
    by simp only [List.headD_cons]; omega, hw, (hE2.grow (hg3.trans hg4)).grow hg47, hE4.grow hg47⟩

/-! ## `block_caps_at`'s relation -/

theorem installEvalW3 (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    ((if a then (1 : Word) else 0) &&& (if b then 1 else 0) &&& (if c then 1 else 0) != 0) =
      (decide a && decide b && decide c) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp only [ha, hb, hc] <;> decide

theorem installEvalW2 (a b : Prop) [Decidable a] [Decidable b] :
    ((if a then (1 : Word) else 0) &&& (if b then 1 else 0) != 0) = (decide a && decide b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb] <;> decide

theorem installOfNatBeq {x c : Nat} (hx : x < 2 ^ 64) (hc : c < 2 ^ 64) :
    (UInt64.ofNat x == UInt64.ofNat c) = (x == c) := by
  by_cases h : x = c
  · subst h; simp
  · have : UInt64.ofNat x ≠ UInt64.ofNat c := fun e => h (by
      have := congrArg UInt64.toNat e
      rwa [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hc] at this)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

/-- A pure callee's run: the memory unchanged, the result its model. -/
theorem installPureCall {p : Prog} {n : Nat} {f : FnName} {args : List Word} {m m' : Mem}
    {R : Option (List Word)} {r : List Word}
    (h : ⦃fun st => st = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' ⟨m, Locals.init []⟩ ∧ s'.mem = m ∧ R = some r; ⊤⦄)
    (hc : callW p n f args m = some (r, m')) : R = some r ∧ m' = m := by
  obtain ⟨s', rfl, -, h1, h2⟩ := triple_of_callW h hc
  exact ⟨h2, h1⟩

/-- **`block_caps_fin`'s run: the record.** A capability record with the branch words, the index
count, the member names and the ctor names. -/
theorem installCapsTail {p : Prog} (hP : CapsProg p) (n : Nat)
    {vis : Word} {fe : IFEnv} {m m2 : Mem} {a : AState} {pp coff clen w0 nIdx nz : Word}
    {r2 : List Word} {bs : BlockShape} {cs : List (IConstantVal × Nat)}
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcs : PSlR decCN cs coff clen m)
    (h2 : callW p (n + 1) "block_caps_fin" [pp, coff, clen, w0, nIdx, nz] m = some (r2, m2)) :
    StageR vis fe m2 a ∧ IWGrow m m2 ∧ CapsAt m2 (r2.headD 0).toNat
      { eta := w0 != 0, all := bs.memberNames, nparams := bs.nP,
        nIdx := nIdx.toNat, ctors := cs.map (·.1.name), neverZero := nz != 0 } := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (icf_spec p hP.alloc hP.fin (n + 1) _ pp coff clen w0 nIdx nz) h2
  simp only at hW
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨-, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  obtain ⟨hS2, hg2, aq, al, cq, cl, htop, hcw, hEa, hEc⟩ := icfW_ok hP hW hS hq hsrc hcs
  refine ⟨hS2, hg2, htop, fun a e ha he => ?_⟩
  have hd := decCaps_of_words (hcw.shift ha) (he.hslice? hEa) (he.hslice? hEc)
  rw [hd, UInt64.toNat_ofNat_of_lt' hnpb]

/-- **`block_caps_at`'s model refines `blockCapsAt`** (pure in the twin): the stage relation kept,
the capability record at the returned pointer. -/
theorem icaHead_ok {p : Prog} (hP : CapsProg p) (n : Nat)
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {pp mi isRec nz : Word} {bs : BlockShape} {b : Bool}
    {r : List Word} (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hb : (isRec != 0) = b)
    (h : icaW.k_block_caps_head p n pp isRec nz (callW p n "block_caps_head" [pp, mi] m) = some (r, m'))
    (hS : StageR vis fe m a) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      CapsAt m' (r.headD 0).toNat
        (ConRon.Bridge.Inductives.blockCapsAtP bs mi.toNat b (nz != 0)) := by
  rcases n with _ | n
  · rw [callW_zero, icaW.k_block_caps_head.none] at h; cases h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hq hsrc
  have hkw := partsShapeK hq' hq9
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdm, hob⟩ := partsAt decMS_mono hmem
  have hdm' : decPL (truncM m) (decMS (truncM m)) o.toNat l.toNat = some bs.members := hdm
  have hlk : bs.k = l.toNat := decPL_length _ hdm'
  have hkb : bs.k < 2 ^ 64 := by rw [hlk]; exact l.toNat_lt
  obtain ⟨hw0, -, -⟩ := partsIwRd ho (w := pp) rfl
  rw [UInt64.ofNat_toNat] at hw0
  -- the record, shared by the branches
  have hfin : ∀ (w0 : Word) (cs : List (IConstantVal × Nat)) (coff clen nIdx : Word)
      (R : IIndCaps), PSlR decCN cs coff clen m →
      R =
        { eta := w0 != 0, all := bs.memberNames, nparams := bs.nP, nIdx := nIdx.toNat, ctors := cs.map (·.1.name),
          neverZero := nz != 0 } →
      icaW.j1 p (n + 1) pp nz coff clen nIdx w0 m = some (r, m') →
      StageR vis fe m' a ∧ IWGrow m m' ∧ CapsAt m' (r.headD 0).toNat R := by
    intro w0 cs coff clen nIdx R hcs hR hK
    rw [icaW.j1.arm1] at hK
    obtain ⟨⟨r2, m2⟩, h2, hK⟩ := of_K hK rfl
    rw [icaW.k_block_caps_fin.arm1] at hK
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hK)
    obtain ⟨hS2, hg2, hca⟩ := installCapsTail hP n hS hq hsrc hcs h2
    subst hR
    exact ⟨hS2, hg2, by simpa using hca⟩
  obtain ⟨⟨r0, m0⟩, h0, h⟩ := of_K h rfl
  obtain ⟨hr0, hm0⟩ := installPureCall (capsHead_spec p hP.head (n + 1) _ pp mi) h0
  subst m0
  unfold ConRon.Bridge.Inductives.blockCapsAtP
  rcases Nat.lt_or_ge mi.toNat bs.k with hmi | hmi
  case inr =>
    have hnone : bs.members[mi.toNat]? = none :=
        List.getElem?_eq_none (by unfold BlockShape.k at hmi; omega)
    rw [capsHead.arm1 (hc1 := by rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega)]
      at hr0
    cases hr0
    rw [icaW.k_block_caps_head.arm2 (hc1 := by decide)] at h
    simp only [List.headD_cons, List.tail_cons] at h
    simp only [hnone]
    exact hfin 0 [] 0 0 0 _ (PSlR.nil decCN m) rfl h
  -- member `mi`
  have hl0 : l.toNat ≠ 0 := by omega
  have hob' : o.toNat + l.toNat ≤ iwTop m := hob.resolve_left (fun h => hl0 (by rw [h]; rfl))
  obtain ⟨v, hv, hmsd⟩ := decPL_getH (truncM m) hdm' mi.toNat (by omega)
  generalize hmsh : bs.members[mi.toNat]'(by rw [decPL_length _ hdm']; omega) = msh at hmsd
  have hsome : bs.members[mi.toNat]? = some msh := by rw [← hmsh]; exact List.getElem?_eq_getElem _
  simp only [hsome]
  have hom : (o + mi).toNat = o.toNat + mi.toNat := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨hwv, hvb, hvlt⟩ := partsIwRd hv (w := o + mi) hom
  have hv' : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hvb
  obtain ⟨⟨cvp, hcvp, hcvT⟩, -, hni, hct⟩ := decMS_some hmsd
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono hct
  have hv3 : v + 3 < iwTop m := partsIwLt hcl
  obtain ⟨hw2, -, -⟩ := partsIwRd hco (w := UInt64.ofNat v + 2) (by rw [UInt64.toNat_add, hv']; simp; omega)
  obtain ⟨hw3, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat v + 3) (by rw [UInt64.toNat_add, hv']; simp; omega)
  obtain ⟨hw1n, hnb, -⟩ := partsIwRd hni (w := UInt64.ofNat v + 1) (by rw [UInt64.toNat_add, hv']; simp; omega)
  rw [UInt64.ofNat_toNat] at hw2 hw3
  have hnI : (UInt64.ofNat msh.nIdx : Word).toNat = msh.nIdx := UInt64.toNat_ofNat_of_lt' hnb
  have hcd' : decPL (truncM m) (decCN (truncM m)) co.toNat cl.toNat = some msh.ctors := hcd
  have hlenc : msh.ctors.length = cl.toNat := decPL_length _ hcd'
  have hhd : capsHead m pp mi = if cl = 0 then some [0, 0, 0, UInt64.ofNat v, UInt64.ofNat msh.nIdx]
      else some [co, cl, if cl = 1 then 1 else 0, UInt64.ofNat v, UInt64.ofNat msh.nIdx] := by
    unfold capsHead
    rw [ite_eq_right (by rw [hkw, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hkb]; omega)]
    simp only [hw0, hwv, hw2, hw3, hw1n]
  rcases hcs : msh.ctors with _ | ⟨c, _ | ⟨c2, cs⟩⟩
  · -- no constructor
    have hcl0 : cl = 0 := by
      apply UInt64.toNat_inj.mp; rw [← hlenc, hcs]; rfl
    rw [hhd, ite_eq_left hcl0] at hr0
    cases hr0
    rw [icaW.k_block_caps_head.arm2 (hc1 := by simp)] at h
    simp only [List.headD_cons, List.tail_cons] at h
    exact hfin 0 [] 0 0 (UInt64.ofNat msh.nIdx) _ (PSlR.nil decCN m) (by rw [hnI]; rfl) h
  · -- one constructor
    have hcl1 : cl = 1 := by apply UInt64.toNat_inj.mp; rw [← hlenc, hcs]; rfl
    subst hcl1
    rw [hhd, ite_eq_right (by decide)] at hr0
    cases hr0
    rw [icaW.k_block_caps_head.arm1 (hc1 := by simp)] at h
    simp only [List.headD_cons, List.tail_cons] at h
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
    obtain ⟨hr1, hm1⟩ := installPureCall (capsOne_spec p hP.one (n + 1) _ (UInt64.ofNat v) isRec) h1
    subst m1
    rw [capsOne.arm1] at hr1
    cases hr1
    rw [icaW.k_block_caps_one.arm1] at h
    simp only [List.headD_cons] at h
    have hcb1 : co.toNat + (1 : Word).toNat ≤ iwTop m := hcb.resolve_left (by decide)
    refine hfin _ [c] co 1 (UInt64.ofNat msh.nIdx) _
      ⟨by rw [← hcs]; exact hcd, hcb1⟩ ?_ h
    simp only [hw1n, installEvalW2]
    have e1 : decide (UInt64.ofNat msh.nIdx = (0 : Word)) = (msh.nIdx == 0) := by
      rw [← installOfNatBeq (c := 0) hnb (by decide)]; rfl
    have e4 : decide (isRec = 0) = !b := by rw [← hb, bne, Bool.not_not]; rfl
    simp only [e1, e4, hnI, List.map_cons, List.map_nil]
    by_cases h1 : msh.nIdx = 0 <;> cases b <;> simp [h1, bne]
  · -- two or more
    have hcl2 : 2 ≤ cl.toNat := by rw [← hlenc, hcs]; simp
    have hne0 : cl ≠ 0 := fun e => by rw [e] at hcl2; simp at hcl2
    have hne1 : (if cl = 1 then (1 : Word) else 0) ≠ 1 := by
      have : cl ≠ 1 := fun e => by rw [e] at hcl2; simp at hcl2
      simp [this]
    rw [hhd, ite_eq_right hne0] at hr0
    cases hr0
    rw [icaW.k_block_caps_head.arm2 (hc1 := by simpa using hne1)] at h
    simp only [List.headD_cons, List.tail_cons] at h
    have hbd : co.toNat + cl.toNat ≤ iwTop m := hcb.resolve_left hne0
    exact hfin 0 (c :: c2 :: cs) co cl (UInt64.ofNat msh.nIdx) _ ⟨by rw [← hcs]; exact hcd, hbd⟩
      (by rw [hnI]; rfl) h

/-- **`block_caps_at`'s model refines `blockCapsAt`**: the never-zero read (`mnzW_ok`, under
`ReadLCOK` and `SortsDen`), then the record (`icaHead_ok`, con-ron's `blockCapsAt_split`). -/
theorem icaW_ok {p : Prog} (hP : CapsProg p) (n : Nat)
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {pp mi isRec : Word} {bs : BlockShape} {b : Bool}
    {r : List Word} (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hb : (isRec != 0) = b) (h : icaW p n m pp mi isRec = some (r, m')) (hS : StageR vis fe m a)
    (hrl : ReadLCOK a) (hsd : SortsDen a) :
    ∃ caps a', (ConRon.Arena.blockCapsAt bs mi.toNat b).run a = .ok (caps, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ CapsAt m' (r.headD 0).toNat caps ∧ a'.store = a.store ∧
      ReadLCOK a' := by
  rcases n with _ | n
  · simp [icaW] at h
  rw [icaW.arm1] at h
  obtain ⟨⟨r0, m0⟩, h0, h⟩ := of_K h rfl
  rw [icaW.k_member_never_zero.arm1] at h
  obtain ⟨s0, hs0, -, hW0⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mnzW_spec p hP.mnz.mnz n _ pp mi) h0
  rw [hs0] at hW0
  obtain ⟨a1, hrun1, hS0, hg0, hst1, hrl1⟩ := mnzW_ok hP.mnz hq hsrc hS hrl hsd hW0
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hS2, hg2, hca⟩ := icaHead_ok hP n (hq.grow (decBS_mono _) hg0)
    (partsHsrc_grow hg0 hq9 hsrc) hb h hS0
  refine ⟨_, a1, ?_, hS2, hg0.trans hg2, hca, hst1, hrl1⟩
  rw [ConRon.Bridge.Inductives.blockCapsAt_split]
  simp only [StateT.run_bind, hrun1, except_ok_bind]
  rfl

/-- **`block_caps_at` refines `blockCapsAt`, as a call** (`icaW_ok`). -/
theorem blockCapsAt_ok {p : Prog} (hP : CapsProg p) (n : Nat)
    {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState} {pp mi isRec : Word} {bs : BlockShape} {b : Bool}
    {r : List Word} (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hb : (isRec != 0) = b) (h : callW p n "block_caps_at" [pp, mi, isRec] m = some (r, m'))
    (hS : StageR vis fe m a) (hrl : ReadLCOK a) (hsd : SortsDen a) :
    ∃ caps a', (ConRon.Arena.blockCapsAt bs mi.toNat b).run a = .ok (caps, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ CapsAt m' (r.headD 0).toNat caps ∧ a'.store = a.store ∧
      ReadLCOK a' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ica_spec p hP.caps n _ pp mi isRec) h
  exact icaW_ok hP n hq hsrc hb hW hS hrl hsd

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ind_info_rec` -/

/-- The record's image (`wrERo`), read in the memory before the allocation: the head (the kind
word and the constant's value, `CI.indHdImg`), then the capability record's `Caps.size` words. -/
def iirImg (m : Mem) (cv caps : Word) : List (Option Word) :=
  CI.indHdImg 3 (erRd m cv) (erRd m (cv + CV.lpsOff)) (erRd m (cv + CV.lpsLen)) (erRd m (cv + CV.type)) ++
    (ieWords (m.arr64 IW) Caps.size.toNat caps).map some

theorem iirImg_length (m : Mem) (cv caps : Word) : (iirImg m cv caps).length = CI.indSize.toNat := by
  rw [iirImg, List.length_append, CI.indHdImg_length, List.length_map, ieWords_length,
    CI.indSize_toNat]

l_model erPutCi_spec (p : Prog) (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "er_put_ci" = some erPutCi)
  fns [hp ↦ erPutCiW void]
  specs [erecPut_specW p hpu n]
  grind [arena_grind] simp []

/-- The model of `ind_info_rec(cv, caps)`. -/
def iirW (m : Mem) (cv caps : Word) : Option (Word × Mem) :=
  match erAllocW m CI.indSize with
  | none => none
  | some (q, m1) => some (q, wrERo m1 q (iirImg m cv caps))

l_model iir_specK (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hp : p.lookup "ind_info_rec" = some indInfoRec)
  fns [hp ↦ iirK list]
  specs [erecAlloc_specW p ha n, callW_spec p n "er_put_ci", callW_spec p n "block_caps_at_er_copy_go"]
  grind [arena_grind] finish [rdW_eq] gen 40 instances 20000

theorem wrER_IW (m : Mem) (q : Word) (ws : List Word) : (wrER m q ws).arr64 IW = m.arr64 IW :=
  (wrER_frame ws m q).1 IW (by simp [EREC, IW]) (by decide)

theorem erAllocW_arr {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) :
    m1.arr64 IW = m.arr64 IW ∧ ∀ x, erRd m1 x = erRd m x := by
  have hc : ∀ b : TieredArray, b ≠ CTL → m1.arr64 b = m.arr64 b := by
    intro b hb
    simp only [erAllocW] at h
    split at h
    · split at h; · cases h
      split at h; · cases h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      simp only [erAllocMem]; rw [ite_eq_left (by assumption)]; exact Mem.arr64_set64_ne _ _ _ _ _ hb
    · split at h; · cases h
      split at h; · cases h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      simp only [erAllocMem]; rw [ite_eq_right (by assumption)]; exact Mem.arr64_set64_ne _ _ _ _ _ hb
  refine ⟨hc _ (by decide), fun x => ?_⟩
  unfold erRd; rw [hc _ (by rw [tierA_EREC]; split <;> decide)]

/-- `er_put_ci`'s stores are the head's image. -/
theorem erPutCiW_wrERo {m m' : Mem} {q k cv : Word} (h : erPutCiW m q k cv = some m') :
    m' = wrERo m q (CI.indHdImg k (erRd m cv) (erRd m (cv + CV.lpsOff)) (erRd m (cv + CV.lpsLen))
      (erRd m (cv + CV.type))) := by
  unfold erPutCiW at h
  simp only [erRd_foldN] at h
  iterate 5 (split at h; · cases h)
  cases h
  -- the image's entries in order (the layout's numbers: a whole-record writer)
  simp [wrERo, CI.indHdImg, recImg, rec_unfold, UInt64.add_assoc]

/-- `ind_info_rec`'s writes are the record's image. -/
theorem iirK_eq {p : Prog} (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "er_put_ci" = some erPutCi)
    (hcg : p.lookup "block_caps_at_er_copy_go" = some blockCapsAtErCopyGo) {n : Nat} {m m' : Mem}
    {cv caps : Word} {r : List Word} (h : iirK p (n + 2) m cv caps = some (r, m')) :
    ∃ q, r = [q] ∧ iirW m cv caps = some (q, m') := by
  unfold iirW
  rw [iirK.arm1] at h
  rcases h1 : erAllocW m CI.indSize with _ | ⟨q, m1⟩
  · rw [h1] at h; cases h
  obtain ⟨hI1, hE1⟩ := erAllocW_arr h1
  rw [h1, iirK.k_erec_alloc.arm1] at h
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [iirK.k_er_put_ci.arm1] at h
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (erPutCi_spec p hpu hp (n + 1) _ q 3 cv) h2
  have e2 := erPutCiW_wrERo hW2
  have i2 : s2.mem.arr64 IW = m.arr64 IW := by
    rw [e2, (wrERo_frame _ _ _).1 IW (by simp [EREC, IW]) (by decide), hI1]
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h rfl; rw [iirK.k_block_caps_at_er_copy_go.arm1] at h
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (ieCopy_spec p hcg hpu (n + 1) _ _ _ _) h3
  simp only at hW3; subst hs3
  have e3 := ieCopyW_wrER _ _ _ _ _ _ hW3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  refine ⟨q, rfl, ?_⟩
  simp only [hE1] at e2
  dsimp only
  rw [iirImg, wrERo_append, CI.indHdImg_length, UInt64.ofNat_toNat, wrERo_map_some, e3, i2, e2]

/-- **`ind_info_rec` under the stage relation**: a fresh `.indInfo` record of the constant at `cv`
(decoded below the tops) and the capability record at `caps`. -/
theorem iirW_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cv caps q : Word} {cvv : IConstantVal} {c : IIndCaps}
    (h : iirW m cv caps = some (q, m')) (hS : StageR vis fe m a)
    (hcv : DecB (fun m => decCVp m cv.toNat) m cvv) (hcp : CapsAt m caps.toNat c) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat = some (.indInfo cvv c) := by
  unfold iirW at h
  rcases h1 : erAllocW m CI.indSize with _ | ⟨q1, m1⟩
  · rw [h1] at h; cases h
  rw [h1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS', hg, -, -, -, -, hget⟩ := erRecO_stage h1 hS (iirImg m cv caps)
    (iirImg_length m cv caps).symm
  generalize hM : wrERo m1 q1 (iirImg m cv caps) = M at hS' hg hget
  -- the head's words
  have hd : ∀ {o : Word} {x : Word}, o.toNat < CI.indCaps.toNat →
      (CI.indHdImg 3 (erRd m cv) (erRd m (cv + CV.lpsOff)) (erRd m (cv + CV.lpsLen))
        (erRd m (cv + CV.type)))[o.toNat]? = some (some x) → erecP M (q1.toNat + o.toNat) = some x :=
    fun ho e => hget _ _ (by rw [iirImg, List.getElem?_append_left (by rw [CI.indHdImg_length]; exact ho), e])
  have hcvE : decCV (erecP m) cv.toNat = some cvv := decCVp_truncM hcv
  obtain ⟨en, enl, hsl, -, et, etl⟩ := decCV_rd (erRdOK m) hcvE
  have cvb := CI.cv_le
  have hic := CI.indCaps_ge
  have o4 := CV.order
  have ho : ∀ f : Word, f.toNat < CV.size.toNat → (CI.cv + f).toNat < CI.indCaps.toNat := fun f hf => by
    rw [CI.cv_add_toNat (by have := CV.size_le; omega)]
    have : CI.cv.toNat + CV.size.toNat ≤ CI.indCaps.toNat := by simp [rec_layout, CI.cv, CV.size, CI.indCaps]
    omega
  have adj : ∀ f : Word, f.toNat ≤ 64 →
      q1.toNat + (CI.cv + f).toNat = q1.toNat + CI.cv.toNat + f.toNat := fun f hf => by
    rw [CI.cv_add_toNat hf, Nat.add_assoc]
  have hw : CVRecW (erecP M) (q1.toNat + CI.cv.toNat) (erRd m cv) (erRd m (cv + CV.lpsOff))
      (erRd m (cv + CV.lpsLen)) (erRd m (cv + CV.type)) :=
    ⟨by rw [← adj _ CV.name_le]; exact hd (ho _ CV.name_lt) (CI.indHdImg_name ..),
      by rw [← adj _ CV.lpsOff_le]; exact hd (ho _ CV.lpsOff_lt) (CI.indHdImg_lo ..),
      by rw [← adj _ CV.lpsLen_le]; exact hd (ho _ CV.lpsLen_lt) (CI.indHdImg_ll ..),
      by rw [← adj _ CV.type_le]; exact hd (ho _ CV.type_lt) (CI.indHdImg_ty ..)⟩
  have hcv' : decCV (erecP M) (q1.toNat + CI.cv.toNat) = some cvv := by
    rw [decCV_of_words hw enl etl (ArrExt.hslice? (IWGrow.ext hg) hsl), ← en, ← et]
  -- the capability record's words
  have hcaps : decCaps (erecP M) (q1.toNat + CI.indCaps.toNat) = some c := by
    refine hcp.2 (erecP M) _ (fun i hi => ?_) (IWGrow.ext hg)
    have hIsz : iwTop m ≤ (m.arr64 IW).size := hS.iw.iw
    have hsz := hS.iw.iwSize
    have hc15 := hcp.1
    rw [Nat.add_assoc, hget (CI.indCaps.toNat + i) (rdW (m.arr64 IW) (caps + UInt64.ofNat i))]
    · simp only [iwA, aread_apply, rdW]
      have e : (caps + UInt64.ofNat i).toNat = caps.toNat + i := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega
      rw [e, Array.getElem?_eq_getElem (by omega)]; simp
    · rw [iirImg, List.getElem?_append_right (by rw [CI.indHdImg_length]; omega), CI.indHdImg_length,
        show CI.indCaps.toNat + i - CI.indCaps.toNat = i by omega, List.getElem?_map,
        ieWords_get _ _ _ _ (by simpa using hi)]
      rfl
  have n0 : nat? (erecP M) q1.toNat = some 3 := by
    have := hd (o := CI.kind) (by simp [rec_layout, CI.kind, CI.indCaps]) (CI.indHdImg_kind ..)
    simp only [show CI.kind.toNat = 0 from rfl, Nat.add_zero] at this
    simp [nat?, this]
  exact ⟨hS', hg, decCI_indInfo_iff.mpr ⟨n0, hcv', hcaps⟩⟩

section arms
variable (p : Prog) (n : Nat) (m : Mem) (p1 isRec o l vis i : Word) (r : List Word)
theorem icbiW_zero : icbiW p 0 m p1 isRec o l vis i = none := by simp [icbiW]
end arms
/-- `ind_info_rec`'s run, at any fuel. -/
theorem installIirRun {p : Prog} (hP : ConsIndsProg p) {n : Nat} {m m' : Mem} {cv caps : Word}
    {r : List Word} (h : callW p n "ind_info_rec" [cv, caps] m = some (r, m')) :
    ∃ q, r = [q] ∧ iirW m cv caps = some (q, m') := by
  obtain ⟨s', rfl, -, hK⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iir_specK p hP.erAlloc hP.iir n _ cv caps) h
  rcases n with _ | _ | j
  · rw [iirK.eq_1] at hK; cases hK
  · exfalso
    rw [iirK.arm1] at hK
    cases h1 : erAllocW m CI.indSize with
    | none => simp only [h1, iirK.k_erec_alloc.none] at hK; cases hK
    | some x =>
      obtain ⟨q, m1⟩ := x
      simp only [h1, iirK.k_erec_alloc.arm1, callW_zero, iirK.k_er_put_ci.none] at hK; cases hK
  exact iirK_eq hP.recP.put hP.putCi hP.erCopyGo hK

/-- **`cons_block_inds`' model refines `consBlockInds`** (pure in the twin): each member's former
pushed with its capability record `blockCapsAt bs i isRec`, the stage relation at the returned view. -/
theorem icbiW_ok {p : Prog} (hP : ConsIndsProg p) (p1 isRec : Word) (bs : BlockShape) (b : Bool)
    (hb : (isRec != 0) = b) (n : Nat) :
    ∀ (a : AState) (m m' : Mem) (vis : Word) (fe : IFEnv) (o l i : Word) (cvs : List IConstantVal)
      (r : List Word),
    StageR vis fe m a → ReadLCOK a → SortsDen a → DecB (fun m => decBS m p1.toNat) m bs → ShapeSrc m p1 →
    PSlR decCVp cvs o l m → i.toNat + l.toNat < 2 ^ 64 →
    icbiW p n m p1 isRec o l vis i = some (r, m') →
    ∃ fe' a', (ConRon.Arena.consBlockInds bs b cvs i.toNat fe).run a = .ok (fe', a') ∧
      StageR (r.headD 0) fe' m' a' ∧ IWGrow m m' ∧ a'.store = a.store ∧ ReadLCOK a' := by
  induction n with
  | zero => intro a m m' vis fe o l i cvs r _ _ _ _ _ _ _ h; rw [icbiW_zero] at h; cases h
  | succ n ih =>
  intro a m m' vis fe o l i cvs r hS hrl hsd hq hsrc hcvs hil h
  by_cases hl : l = 0
  · rw [icbiW_nil p n m p1 isRec o l vis i hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨fe, a, rfl, hS, IWGrow.refl m, rfl, hrl⟩
  obtain ⟨q, cv, rest, rfl, hw, hqb, hdcv, hrest⟩ := partsPSl_cons hcvs hl
  rw [icbiW_cons p n m p1 isRec o l vis i hl] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [icbiK1])
  rw [icbiK1_some] at h
  obtain ⟨caps, a1, hrun1, hS1, hg1, hca, hst1, hrl1⟩ := blockCapsAt_ok hP.toCapsProg n hq hsrc hb h1 hS hrl hsd
  have hsd1 : SortsDen a1 := by unfold SortsDen; rw [hst1]; exact hsd
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [icbiK2])
  rw [icbiK2_some] at h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hol : o.toNat < iwTop m := by have := hcvs.2; omega
  have hw1 : rdW (m1.arr64 IW) o = UInt64.ofNat q := by
    rw [← hw]; simp only [rdW]; rw [hg1.iwGet _ hol]
  rw [hw1] at h2
  obtain ⟨q2, rfl, hW2⟩ := installIirRun hP h2
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  obtain ⟨hS2, hg2, hci⟩ := iirW_stage hW2 hS1 (by rw [hq']; exact hdcv.grow (OMono.decCVp _) hg1) hca
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [icbiK3])
  rw [icbiK3_some] at h
  simp only [List.headD_cons] at h3
  obtain ⟨hS3, hg3⟩ := envPush_stage hP.recP.ef h3 hS2 hci
  have hg13 := (hg1.trans hg2).trans hg3
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [icbiK4])
  rw [icbiK4_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨fe', a', hrun', hS', hg', hst', hrl'⟩ := ih a1 m3 m4 (r3.headD 0) _ (o + 1) (l - 1) (i + 1) rest r4 hS3
    hrl1 hsd1 (hq.grow (decBS_mono _) hg13) (partsHsrc_grow hg13 hq9 hsrc)
    (hrest.grow (fun q => OMono.decCVp q) hg13) (by omega) h4
  rw [hi1] at hrun'
  refine ⟨fe', a', ?_, by simpa using hS', hg13.trans hg', hst'.trans hst1, hrl'⟩
  unfold ConRon.Arena.consBlockInds
  simp only [StateT.run_bind, hrun1, except_ok_bind]
  exact hrun'

/-- **`cons_block_inds` refines `consBlockInds`**: the formers pushed, each with
its capability record (its never-zero read through the readback memo), the stage relation at the returned view; the twin's store unchanged. -/
@[refines ConRon.Arena.consBlockInds]
theorem consBlockInds_refines (p : Prog) (hP : ConsIndsProg p) (n : Nat) (s₀ : St) (a : AState)
    (vis : Word) (fe : IFEnv) (p1 isRec o l i : Word) (bs : BlockShape) (b : Bool)
    (cvs : List IConstantVal) (hb : (isRec != 0) = b) (hS : StageR vis fe s₀.mem a)
    (hrl : ReadLCOK a) (hsd : SortsDen a)
    (hq : DecB (fun m => decBS m p1.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem p1)
    (hcvs : PSlR decCVp cvs o l s₀.mem) (hil : i.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_block_inds" [p1, isRec, o, l, vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      ∃ fe' a', (ConRon.Arena.consBlockInds bs b cvs i.toNat fe).run a = .ok (fe', a') ∧
        StageR (r.headD 0) fe' s'.mem a' ∧ IWGrow s₀.mem s'.mem ∧ a'.store = a.store ∧ ReadLCOK a'; ⊤⦄ :=
  triple_post (icbi_spec p hP.cbi n s₀ p1 isRec o l vis i) fun r _s' ⟨hl, hm⟩ =>
    ⟨hl, icbiW_ok hP p1 isRec bs b hb n a _ _ vis fe o l i cvs r hS hrl hsd hq hsrc hcvs hil hm⟩

end L.Ind

end

end
