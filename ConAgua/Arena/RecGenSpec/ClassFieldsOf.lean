import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RecGenSpec.CfoProg
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# ClassFieldsOf: `ConRon.Arena.classFieldsOf`

`class_fields_of_go`'s simulation lemmas (`rec2SimPiBinders`, `SPLA`, `CfoQ`) and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `class_fields_of_go` refines `classFieldsOf` -/

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

/-- `pi_binders` as a simulation, with its write set. -/
theorem rec2SimPiBinders (n : Nat) (hS : StageR dn vis fe m a) {h : Word} (hh : H h) :
    RSim (piBW n m CWF h) (ConRon.Arena.piBinders coreWalkFuel (decI h)) a
      (fun b a' x => a' = a ∧ StageR dn vis fe b.2 a ∧ IWGrow m b.2 ∧ MemFrame [IW] [200] m b.2 ∧
        decHL b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat = some x.1) := by
  intro b hb
  obtain ⟨x, a', hrun, hS', hg, hd, -⟩ := simPiBinders n hS hh b hb
  obtain ⟨rs, m'⟩ := b
  obtain ⟨bs, e, hrun2, -, -, -, -, -, hf, -⟩ :=
    piBW_ok n m m' a CWF h rs hS.check.arena.base hb hh hS.iw.2.2.1 hS.iw.2.2.2.2
  rw [CWF_eq, decE_eq] at hrun2
  have : (x, a') = ((bs, e), a) := by rw [hrun] at hrun2; injection hrun2
  cases this
  exact ⟨(bs, e), a, hrun, rfl, hS', hg, hf, hd⟩

end sims

theorem AgreeA.refl (b : Nat) (m : Mem) : AgreeA b m m :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem AgreeA.mono {b b' : Nat} {m m' : Mem} (hb : b ≤ b') (h : AgreeA b m m') : AgreeA b' m m' :=
  ⟨h.1, h.2.1, fun i hb' hi => h.2.2.1 i (Nat.le_trans hb hb') hi, h.2.2.2⟩

theorem AgreeA.iwH {k : IdxKind} {b : Nat} {m m' : Mem} (h : AgreeA b m m') {i : Nat} (hb : b ≤ i)
    (hi : i < iwTop m) : (iwH m' i : Option (Idx k)) = iwH m i := by
  simp only [L.Ind.iwH, hd?, iwA]; rw [h.2.2.1 i hb hi]

namespace StabA
variable {α : Type} {b : Nat} {f : Mem → Option α} {m m' : Mem} {x : α}
theorem get (h : StabA b f m x) : f m = some x := h m (AgreeA.refl b m)
theorem grow (h : StabA b f m x) (hg : AgreeA b m m') : StabA b f m' x := fun m'' h' => h m'' (hg.trans h')
theorem mono {b' : Nat} (hb : b ≤ b') (h : StabA b' f m x) : StabA b f m x := fun m' h' => h m' (h'.mono hb)
theorem stabD (h : StabA b f m x) : StabD f m x := fun m' hg => h m' (AgreeA.of_grow hg)
end StabA

/-- A constant decoded below the tops is stable above any bound (it lives in `EREC`). -/
theorem stabA_decCVp {m : Mem} {q : Nat} {x : IConstantVal} (h : DecB (fun m => decCVp m q) m x) (b : Nat) :
    StabA b (fun m => decCVp m q) m x := by
  intro m' hA
  have h' : decCV (erA (truncM m)) q = some x := h
  show decCV (erA m') q = some x
  refine ArrExt.decCV (fun i v hv => ?_) h'
  obtain ⟨hi, hv'⟩ := truncM_er_get hv
  simp only [erA] at hv' ⊢; rw [hA.2.2.2 i hi]; exact hv'

namespace SPLA
variable {α : Type} {b : Nat} {dec : Mem → Nat → Option α} {m m' : Mem} {o l : Nat} {xs : List α}

theorem nil (o : Nat) (ho : o ≤ iwTop m) : SPLA b dec m o 0 [] :=
  ⟨.inl rfl, by omega, [], by simp [decNL], FA2.nil⟩

theorem grow (h : SPLA b dec m o l xs) (hA : AgreeA b m m') : SPLA b dec m' o l xs := by
  obtain ⟨h1, h2, ps, hps, hf⟩ := h
  exact ⟨h1, Nat.le_trans h2 hA.1, ps, by rw [decNL_agree ⟨h1, h2, ps, hps, hf⟩ hA]; exact hps,
    FA2.imp (fun _ _ hq => hq.grow hA) hf⟩

theorem mono {b' : Nat} (hb : b ≤ b') (h : SPLA b' dec m o l xs) : SPLA b dec m o l xs := by
  obtain ⟨h1, h2, ps, hps, hf⟩ := h
  exact ⟨h1.imp id (Nat.le_trans hb), h2, ps, hps, FA2.imp (fun _ _ hq => hq.mono hb) hf⟩

theorem toSPL (h : SPLA b dec m o l xs) : SPL dec m o l xs := by
  obtain ⟨-, h2, ps, hps, hf⟩ := h
  exact ⟨h2, ps, hps, FA2.imp (fun _ _ hq => hq.stabD) hf⟩

/-- `sl_cons` of a pointer decoding stably above `b` onto a slice stable above `b`, at a top from
`b` on. -/
theorem cons {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {x ow lw : Word} {r : List Word} {y : α} (h : consW n m x ow lw = some (r, m'))
    (hS : StageR dn vis fe m a) (hl : SPLA b dec m ow.toNat lw.toNat xs) (hbt : b ≤ iwTop m)
    (hy : StabA b (fun m => dec m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      SPLA b dec m' (r.headD 0).toNat (r.tail.headD 0).toNat (y :: xs) := by
  obtain ⟨h1, h2, ps, hps, hf⟩ := hl
  obtain ⟨hr, -, -, -, -, -⟩ := consW_decN h hS.iw.2.2.1 hS.iw.2.2.2.2 h2 hps
  obtain ⟨hS', hg, hdn, htop⟩ := consW_stageN h hS h2 hps
  refine ⟨hS', hg, .inr ?_, by omega, x.toNat :: ps, hdn,
    FA2.cons (hy.grow (AgreeA.of_grow hg)) (FA2.imp (fun _ _ hq => hq.grow (AgreeA.of_grow hg)) hf)⟩
  rw [hr]; exact hbt

end SPLA

/-- A one- or three-word record at the top decodes stably above any bound up to that top. -/
theorem rec2RecW_decCF_A {m m' : Mem} {k : Word} {ws r : List Word} {y : ClassField} {b : Nat}
    (h : recW m k ws = some (r, m')) (hc : 200 < (m.arr64 CTL).size) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hk : k.toNat = ws.length) (hb : b ≤ iwTop m)
    (hy : ∀ m'', (∀ j (hj : j < ws.length), iwN m'' ((r.headD 0).toNat + j) = some (ws[j]'hj).toNat) →
      decCF m'' (r.headD 0).toNat = some y) :
    StabA b (fun m => decCF m (r.headD 0).toNat) m' y := by
  obtain ⟨hr, hget, -, -, htop, -⟩ := recW_post h hc hsz hk
  subst hr
  intro m'' hA
  refine hy m'' fun j hj => ?_
  have hlt : (rdW (m.arr64 CTL) 200).toNat + j < iwTop m' := by rw [htop]; simp [iwTop]; omega
  simp only [List.headD_cons]
  rw [hA.iwN (by simp only [iwTop] at hb; omega) hlt]
  simp only [L.Ind.iwN, nat?, iwA, hget j hj, List.getElem?_eq_getElem hj, Option.map_some]

/-- The post of `class_fields_of(_go)`: the stage relation, growth, the fields' kinds a stable slice,
`nest_occ`'s memo relation at some map, and the write set outside the other walk memos (lane
`indproofs4`, helper `cls`: `class_ctor_of` carries `RcMR` across the call); the kinds' slice and
records lie above the entry's top (`SPLA`, for `class_ctors_of`'s writes into its result slots). -/
def CfoQ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (b : List Word × Mem)
    (a' : AState) (ks : List ClassField) : Prop :=
  StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧
    SPLA (iwTop m) decCF b.2 (b.1.headD 0).toNat (b.1.tail.headD 0).toNat ks ∧
    (∃ mp, noMR b.2 mp) ∧ MFr [NOM] [204, 205] m b.2

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

/-- A fresh `rec6` record (at or above `b`) of parts stable above `b` decodes stably above `b` as a
`ClassCtor`. -/
theorem rec6_decCC {m m' : Mem} {q : Word} {cvw nFw ko kl tyD tyN : Word} {cv : IConstantVal}
    {kinds : List ClassField} {b : Nat}
    (hget : ∀ j < 6, (m'.arr64 IW)[q.toNat + j]? = [cvw, nFw, ko, kl, tyD, tyN][j]?)
    (hq : q.toNat + 6 ≤ iwTop m') (hb : b ≤ q.toNat) (hg : IWGrow m m')
    (hcv : DecB (fun m => decCVp m cvw.toNat) m cv)
    (hks : SPLA b decCF m ko.toNat kl.toNat kinds) (hD : H tyD) (hN : H tyN) :
    StabA b (fun m => decCC m q.toNat) m' ⟨cv, nFw.toNat, kinds, decI tyD, decI tyN⟩ := by
  intro m'' hA
  have hA0 : AgreeA b m m'' := (AgreeA.of_grow hg).trans hA
  have hw : ∀ j (hj : j < 6), iwN m'' (q.toNat + j) =
      some ([cvw, nFw, ko, kl, tyD, tyN][j]'(by simpa using hj)).toNat := fun j hj => by
    rw [hA.iwN (by omega) (by omega)]
    simp only [iwN, nat?, iwA]
    rw [hget j hj, List.getElem?_eq_getElem (by simp; omega)]; rfl
  have h0 := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega)
  have hhD : (iwH m'' (q.toNat + 4) : Option EIdx) = some (decI tyD) := by
    rw [hA.iwH (by omega) (by omega)]
    simp only [iwH, hd?, iwA]
    rw [hget 4 (by omega)]
    simp [hD]
  have hhN : (iwH m'' (q.toNat + 5) : Option EIdx) = some (decI tyN) := by
    rw [hA.iwH (by omega) (by omega)]
    simp only [iwH, hd?, iwA]
    rw [hget 5 (by omega)]
    simp [hN]
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  have e1 : decCVp m'' cvw.toNat = some cv := stabA_decCVp hcv b m'' hA0
  have e3 := hks.stab m'' hA0
  simp only [decCC, decAt, h0, Nat.add_assoc, Nat.reduceAdd, h1, h2, h3, Option.bind_eq_bind,
    Option.bind_some, e1, e3, hhD, hhN]
  rfl

end L.Ind

end

end
