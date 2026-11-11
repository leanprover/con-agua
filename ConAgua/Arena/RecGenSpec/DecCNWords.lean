module

public import ConAgua.Arena.RecGenSpec.CfaFv
public import ConAgua.Arena.RecGenSpec.CfoProg
public import ConAgua.Arena.RecGenSpec.Set64
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Arena.RecClassSpec.MjProg

@[expose] public section

/-!
# DecCNWords

`CxoProg`, `AgreeA.set_iw`, `KeepW.of_mfr`, `FA2.snoc` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A `[cv, nF]` record decoded below the tops: the constant's pointer, its name word (`EREC⦃a⦄`,
over both tiers), `nF`. -/
theorem decCN_wordsE {m : Mem} {cA : Word} {x : IConstantVal × Nat} (h : DecB (fun m => decCN m cA.toNat) m x)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ a : Nat, rdW (m.arr64 IW) cA = UInt64.ofNat a ∧ a + 3 < 2 ^ 64 ∧
      DecB (fun m => decCVp m a) m x.1 ∧ H (erRd m (UInt64.ofNat a)) ∧
      decI (erRd m (UInt64.ofNat a)) = x.1.name ∧
      rdW (m.arr64 IW) (cA + 1) = UInt64.ofNat x.2 ∧ x.2 < 2 ^ 64 ∧ cA.toNat + 1 < iwTop m := by
  have h' : decCN (truncM m) cA.toNat = some x := h
  obtain ⟨⟨a, ha, hcv⟩, hn⟩ := decCN_some h'
  obtain ⟨-, ha'⟩ := L.Ind.iwN_truncM_some ha
  obtain ⟨hnt, hn'⟩ := L.Ind.iwN_truncM_some hn
  have ra := iwN_rdW_at (w := cA) (k := 0) (by simpa using ha') hsz
  have rn := iwN_rdW_at (w := cA) (k := 1) hn' hsz
  have hcv' : decCVp m a = some x.1 := (show DecB (fun m => decCVp m a) m x.1 from hcv).get (OMono.decCVp _)
  obtain ⟨hnm2, -, hty2⟩ := decCV_some (a := erA m) (q := a) hcv'
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hty2
  obtain ⟨w3, hw3, -⟩ := hty2
  have h3 : a + 3 < 2 ^ 64 := erecP_lt64 hw3
  obtain ⟨w, hw, hwH, hwD⟩ := erH_rdW hnm2 (by omega)
  refine ⟨a, by simpa using ra.1, h3, hcv, by rw [hw]; exact hwH, by rw [hw]; exact hwD, by simpa using rn.1, rn.2,
    hnt⟩

/-! ## The relational side -/

/-- The lookups of `class_ctor_of`. -/
structure CxoProg (p : Prog) : Prop extends CfaProg p where
  cnf : p.lookup "class_ctor_of_nfs" = some classCtorOfNfs
  cmsg : p.lookup "class_minor_slot_go" = some classMinorSlotGo
  cms : p.lookup "class_minor_slot" = some classMinorSlotL
  cfo : CfoProg p
  erc : p.lookup "er_copy" = some erCopy
  eri : p.lookup "er_to_iw" = some erToIw
  cvl : p.lookup "cv_lps" = some cvLps
  tca : p.lookup "target_ctor_at" = some targetCtorAt
  ipw : p.lookup "inst_pis_with" = some instPisWith
  r6 : p.lookup "rec6" = some rec6
  cxo : p.lookup "class_ctor_of" = some classCtorOfL

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

local notation "V" => ConLeche.CheckMode.verified

/-! ## Tools -/

theorem AgreeA.set_iw {b : Nat} (m : Mem) {i : Word} (v : Word) (hi : i.toNat < b) :
    AgreeA b m (m.set64 IW i v) := by
  have e0 : (m.set64 IW i v).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have e1 : (m.set64 IW i v).arr64 (tier1 EREC) = m.arr64 (tier1 EREC) :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have eC : (m.set64 IW i v).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨by rw [iwTop_set_iw]; exact Nat.le_refl _, fun j hj _ => ?_,
    ⟨by simp only [erTop, eC]; exact Nat.le_refl _, fun j _ => by rw [e0],
      by simp only [erecTop1, eC]; exact Nat.le_refl _, fun j _ => by rw [e1]⟩⟩
  rw [set64IW_get]; rw [ite_eq_right (by omega)]

theorem KeepW.of_mfr {S : List TieredArray} {T : List Word} {m m' : Mem} (h : MFr S T m m') : KeepW m m' := by
  obtain ⟨A, C, hf, -, -⟩ := h
  exact hf.size

theorem FA2.snoc {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β} {a : α} {b : β}, FA2 R as bs → R a b → FA2 R (as ++ [a]) (bs ++ [b])
  | _, _, _, _, .nil, h => .cons h .nil
  | _, _, _, _, .cons h1 h2, h => .cons h1 (FA2.snoc h2 h)

/-- A prefix of words written one after the other, the next one at its end. -/
theorem decNL_write (m : Mem) (o j : Nat) (w v : Word) (ps : List Nat) (hw : w.toNat = o + j)
    (hsz : o + j < (m.arr64 IW).size) (h : decNL m o j = some ps) :
    decNL (m.set64 IW w v) o (j + 1) = some (ps ++ [v.toNat]) := by
  rw [decNL_snoc]
  have e1 : decNL (m.set64 IW w v) o j = decNL m o j := by
    simp only [decNL]
    apply L.Ind.mapM_congr_of
    intro i hi
    have hi' : i < j := List.mem_range.mp hi
    simp only [iwN, nat?, iwA, aread_apply, set64IW_get]
    rw [ite_eq_right (by omega)]
  rw [e1, h]
  simp [iwN, nat?, iwA, aread_apply, set64IW_get, hw, hsz]

/-! ## `class_ctors_of`: the relational side -/

/-- The lookups of `class_ctors_of`. -/
structure CosProg (p : Prog) : Prop extends CxoProg p where
  cos : p.lookup "class_ctors_of" = some classCtorsOfL

/-! ## `classes_ctors`: the relational side -/

/-- A `TargetMajor` decoded below the tops: its constructors' slice (words 6, 7). -/
theorem decTM_ctors {m : Mem} {v : Nat} {M : TargetMajor} (h : DecB (fun m => decTM m v) m M) :
    ∃ o l : Nat, iwN m (v + 6) = some o ∧ iwN m (v + 7) = some l ∧ v + 7 < iwTop m ∧
      DecB (fun m => decPL m (decCN m) o l) m M.ctors := by
  have h' : decTM (truncM m) v = some M := h
  simp only [decTM, bind, Option.bind_eq_some_iff, pure] at h'
  obtain ⟨i, hi, lv, hlv, ds, hds, nPc, hnPc, nIdx, hnIdx, ctors, hctors, mem, hmem, nfs, hnfs, pf, hpf, hM⟩ := h'
  cases hM
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hctors
  obtain ⟨-, ho'⟩ := L.Ind.iwN_truncM_some ho
  obtain ⟨hlt, hl'⟩ := L.Ind.iwN_truncM_some hl
  exact ⟨o, l, ho', by simpa [Nat.add_assoc] using hl', by simpa [Nat.add_assoc] using hlt, hd⟩

/-- A fresh `[off, len]` header (at or above `b`) of a slice stable above `b`. -/
theorem stabA_decLH {α : Type} {dec : Mem → Nat → Option α} {m : Mem} {hq o l b : Nat} {xs : List α}
    (h0 : iwN m hq = some o) (h1 : iwN m (hq + 1) = some l) (hb : b ≤ hq) (ht : hq + 2 ≤ iwTop m)
    (hs : SPLA b dec m o l xs) : StabA b (fun m => decLH m (decPL m (dec m)) hq) m xs := by
  intro m' hA
  simp only [decLH, decAt]
  rw [hA.iwN hb (by omega), h0, hA.iwN (by omega) (by omega), h1]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact hs.stab m' hA

/-- The lookups of `classes_ctors`. -/
structure CcsProg (p : Prog) : Prop extends CosProg p where
  r2 : p.lookup "rec2" = some rec2
  ccs : p.lookup "classes_ctors" = some classesCtorsL

end L.Ind

end

end
