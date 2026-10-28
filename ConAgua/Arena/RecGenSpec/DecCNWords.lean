import ConAgua.Arena.RecGenSpec.CfaFv
import ConAgua.Arena.RecGenSpec.CtorLp
import ConAgua.Arena.RecGenSpec.CfoProg
import ConAgua.Arena.RecGenSpec.Set64
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# DecCNWords

`decCN_words`, `CxoProg`, `AgreeA.set_iw`, `KeepW.of_mfr`, `CtorLp.grow`, `FA2.snoc` and the lemmas only they use.
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

/-- A `[cv, nF]` record decoded below the tops: the constant's pointer, its name word, `nF`. -/
theorem decCN_words {m : Mem} {cA : Word} {x : IConstantVal × Nat} (h : DecB (fun m => decCN m cA.toNat) m x)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ a : Nat, rdW (m.arr64 IW) cA = UInt64.ofNat a ∧ a + 3 < erTop m ∧
      DecB (fun m => decCVp m a) m x.1 ∧ H (rdW (m.arr64 EREC) (UInt64.ofNat a)) ∧
      decI (rdW (m.arr64 EREC) (UInt64.ofNat a)) = x.1.name ∧
      rdW (m.arr64 IW) (cA + 1) = UInt64.ofNat x.2 ∧ x.2 < 2 ^ 64 ∧ cA.toNat + 1 < iwTop m := by
  have h' : decCN (truncM m) cA.toNat = some x := h
  obtain ⟨⟨a, ha, hcv⟩, hn⟩ := decCN_some h'
  obtain ⟨-, ha'⟩ := rec2IwN_trunc ha
  obtain ⟨hnt, hn'⟩ := rec2IwN_trunc hn
  have ra := iwN_rdW_at (w := cA) (k := 0) (by simpa using ha') hsz
  have rn := iwN_rdW_at (w := cA) (k := 1) hn' hsz
  obtain ⟨hnm, -, hty⟩ := decCV_some (a := erA (truncM m)) (q := a) hcv
  simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hnm hty
  obtain ⟨w0, hw0, -⟩ := hnm
  obtain ⟨w3, hw3, -⟩ := hty
  obtain ⟨-, hw0'⟩ := truncM_er_get hw0
  obtain ⟨h3t, -⟩ := truncM_er_get hw3
  have hcv' : decCVp m a = some x.1 := (show DecB (fun m => decCVp m a) m x.1 from hcv).get (OMono.decCVp _)
  obtain ⟨hnm2, -, -⟩ := decCV_some (a := erA m) (q := a) hcv'
  obtain ⟨w, hw, hwH, hwD⟩ := erH_rdW hnm2 (by have := ra.2; omega)
  refine ⟨a, by simpa using ra.1, h3t, hcv, by rw [hw]; exact hwH, by rw [hw]; exact hwD, by simpa using rn.1, rn.2,
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
  refine ⟨by rw [iwTop_set_iw]; exact Nat.le_refl _,
    by simp only [erTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact Nat.le_refl _,
    fun j hj _ => ?_, fun j _ => ?_⟩
  · rw [set64IW_get]; rw [ite_eq_right (by omega)]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

theorem KeepW.of_mfr {S : List TieredArray} {T : List Word} {m m' : Mem} (h : MFr S T m m') : KeepW m m' := by
  obtain ⟨A, C, hf, -, -⟩ := h
  exact hf.size

/-- `CtorLp` holds on as the pools grow and keep their sizes. -/
theorem CtorLp.grow {m m' : Mem} {cA : Word} {x : IConstantVal × Nat} (h : CtorLp m cA)
    (hcA : DecB (fun m => decCN m cA.toNat) m x) (hsz : (m.arr64 IW).size < 2 ^ 64) (hg : IWGrow m m')
    (hk : KeepW m m') : CtorLp m' cA := by
  obtain ⟨a, ha, ha3, -, -, -, -, -, hct⟩ := decCN_words hcA hsz
  have ha64 : a + 3 < 2 ^ 64 := by have := (rdW (m.arr64 CTL) 129).toNat_lt; simp only [erTop] at ha3; omega
  have e1 : (UInt64.ofNat a + 1 : Word).toNat = a + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  have e2 : (UInt64.ofNat a + 2 : Word).toNat = a + 2 := by rw [UInt64.toNat_add]; simp <;> omega
  simp only [CtorLp] at h ⊢
  rw [ha] at h
  rw [rdW_grow hg (by omega), ha]
  rw [rdW_er_grow hg (by rw [e2]; omega), rdW_er_grow hg (by rw [e1]; omega), hk EREC]
  exact h

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
    apply mapM_opt_congr
    intro i hi
    have hi' : i < j := List.mem_range.mp hi
    simp only [iwN, nat?, iwA, set64IW_get]
    rw [ite_eq_right (by omega)]
  rw [e1, h]
  simp [iwN, nat?, iwA, set64IW_get, hw, hsz]

/-! ## `class_ctors_of`: the relational side -/

/-- The lookups of `class_ctors_of`. -/
structure CosProg (p : Prog) : Prop extends CxoProg p where
  cos : p.lookup "class_ctors_of" = some classCtorsOfL

/-- `CtorLp` at every constructor record of a slice. -/
def CtorsLp (m : Mem) (ao al : Word) : Prop :=
  ∀ j < al.toNat, CtorLp m (rdW (m.arr64 IW) (ao + UInt64.ofNat j))

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
  obtain ⟨-, ho'⟩ := rec2IwN_trunc ho
  obtain ⟨hlt, hl'⟩ := rec2IwN_trunc hl
  exact ⟨o, l, ho', by simpa [Nat.add_assoc] using hl', by simpa [Nat.add_assoc] using hlt, hd⟩

/-- `CtorsLp` holds on as the pools grow and keep their sizes. -/
theorem CtorsLp.grow {m m' : Mem} {ao al : Word} {cAs : List (IConstantVal × Nat)} (h : CtorsLp m ao al)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m cAs) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hg : IWGrow m m') (hk : KeepW m m') : CtorsLp m' ao al := by
  intro j hj
  have hcAs0 : decPL (truncM m) (decCN (truncM m)) ao.toNat al.toNat = some cAs := hcAs
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hcAs0 j hj
  obtain ⟨hvt, hv0⟩ := rec2IwN_trunc hv
  have hrd := iwN_rdW_at (w := ao) (k := j) hv0 hsz
  have hgt : (ao + UInt64.ofNat j).toNat < iwTop m := by
    rw [UInt64.toNat_add]; simp; have := ao.toNat_lt; omega
  rw [rdW_grow hg hgt, hrd.1]
  have := h j hj
  rw [hrd.1] at this
  have hdv' : DecB (fun m => decCN m (UInt64.ofNat v : Word).toNat) m (cAs[j]'(by
      rw [decPL_length _ hcAs0]; exact hj)) := by
    rw [UInt64.toNat_ofNat_of_lt' hrd.2]; exact hdv
  exact this.grow hdv' hsz hg hk

/-- `CtorLp` at every constructor record of every class of `(ms.off, ms.len)`. -/
def ClassesLp (m : Mem) (mo ml : Word) : Prop :=
  ∀ c < ml.toNat, ∀ v o l, iwN m (mo.toNat + c) = some v → iwN m (v + 6) = some o → iwN m (v + 7) = some l →
    CtorsLp m (UInt64.ofNat o) (UInt64.ofNat l)

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
