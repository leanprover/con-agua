import ConAgua.Arena.IndPartsSpec.Bs
import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.RecClassSpec.Classes

/-!
# PartsConsPL

`partsConsPL`, `PSlR`, `PSlR.grow`, `PSlR.nil`, `SplitRec`, `SplitR` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`sl_cons` of a pointer onto a pointer slice decoded below the tops.** -/
theorem partsConsPL {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List α} {y : α}
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a)
    (hb : o.toNat + l.toNat ≤ iwTop m)
    (hxs : DecB (fun m => decPL m (f m) o.toNat l.toNat) m xs) (hy : DecB (fun m => f m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      DecB (fun m => decPL m (f m) (r.headD 0).toNat (r.tail.headD 0).toNat) m' (y :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  have hxs' : decPL (truncM m) (f (truncM m)) o.toNat l.toNat = some xs := hxs
  rw [decPL_eq_bind] at hxs'
  simp only [Option.bind_eq_some_iff] at hxs'
  obtain ⟨ps, hps, hmap⟩ := hxs'
  have hps' : decNL m o.toNat l.toNat = some ps :=
    (OMono.decNL _ _).mono _ _ _ (IWGrow.refl m).truncExt hps
  obtain ⟨hS', hg, hdn, htop⟩ := consW_stageN h hS hb hps'
  refine ⟨hS', hg, ?_, htop⟩
  show decPL (truncM m') (f (truncM m')) _ _ = some (y :: xs)
  have hdn' : decNL (truncM m') (r.headD 0).toNat (r.tail.headD 0).toNat = some (x.toNat :: ps) :=
    decNL_decB hdn (Nat.le_of_eq htop)
  rw [decPL_eq_bind, hdn']
  have hy' : f (truncM m') x.toNat = some y := hy.grow (hf _) hg
  have hm' : ps.mapM (f (truncM m')) = some xs :=
    (show DecB (fun m => ps.mapM (f m)) m xs from hmap).grow (OMono.mapM hf ps) hg
  simp [hy', hm']

/-- A slice result decoded below the tops (`(off, len)`, the slice below the top). -/
def PSlR {α : Type} (f : Mem → Nat → Option α) (xs : List α) (o l : Word) (m : Mem) : Prop :=
  DecB (fun m => decPL m (f m) o.toNat l.toNat) m xs ∧ o.toNat + l.toNat ≤ iwTop m

theorem PSlR.grow {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {xs : List α} {o l : Word} {m m' : Mem} (h : PSlR f xs o l m) (hg : IWGrow m m') : PSlR f xs o l m' :=
  ⟨h.1.grow (OMono.decPL hf _ _) hg, Nat.le_trans h.2 hg.1⟩

theorem PSlR.nil {α : Type} (f : Mem → Nat → Option α) (m : Mem) : PSlR f [] 0 0 m :=
  ⟨by show decPL _ _ _ _ = _; simp [decPL], by simp⟩

/-- **`blockSplit`'s record at `q`**: its three slices, decoded below the tops. -/
def SplitRec (x : List IConstantVal × List (IConstantVal × Nat × Nat) ×
    List (IConstantVal × Nat × Nat × List IRecRule)) (q : Word) (m : Mem) : Prop :=
  q.toNat + 6 ≤ iwTop m ∧
  PSlR decCVp x.1 (rdW (m.arr64 IW) q) (rdW (m.arr64 IW) (q + 1)) m ∧
  PSlR decSC x.2.1 (rdW (m.arr64 IW) (q + 2)) (rdW (m.arr64 IW) (q + 3)) m ∧
  PSlR decSR x.2.2 (rdW (m.arr64 IW) (q + 4)) (rdW (m.arr64 IW) (q + 5)) m

/-- `block_split`'s result `(ok, q)` against the twin. -/
def SplitR (x : Option (List IConstantVal × List (IConstantVal × Nat × Nat) ×
    List (IConstantVal × Nat × Nat × List IRecRule))) (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some t => r.headD 0 = 1 ∧ SplitRec t (r.tail.headD 0) m

/-- A word of the pool below the top reads the same after growth. -/
theorem partsRdIW_grow {m m' : Mem} (hg : IWGrow m m') {w : Word} (hw : w.toNat < iwTop m) :
    rdW (m'.arr64 IW) w = rdW (m.arr64 IW) w := by
  simp only [rdW]; rw [hg.2.2.1 _ hw]

/-! ## The census theorems -/

/-- **The program bundle of the split** (one field per lookup). -/
structure IndPartsProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  nr : NrF p
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  rec3 : p.lookup "rec3" = some rec3
  rec5 : p.lookup "rec5" = some rec5
  rec6 : p.lookup "rec6" = some rec6
  recs : p.lookup "block_split_recs" = some blockSplitRecs
  ctors : p.lookup "block_split_ctors" = some blockSplitCtors
  split : p.lookup "block_split" = some blockSplit
  strip : StripProg p
  ad : AdF p

end L.Ind

end
