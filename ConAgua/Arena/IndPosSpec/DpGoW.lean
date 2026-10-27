import ConAgua.Arena.IndPosSpec.MatesW
import ConAgua.Arena.IndView

/-!
# DpGoW

`dpFin`, `dpGoW`, `dpG1`, `dpG3`, `dpG4`, `dpG5` and the lemmas only they use.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `depth_go`, `depth_node`: word models -/

def dpFin (mx : Word) (m : Mem) : Option (Word × Mem) :=
  if 4294967295 ≤ mx then none else some (mx + 1, m)

mutual
def dpGoW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, f, h => if f = 0 then none else dpG1 n m f h (eViewW m h)
def dpG1 (n : Nat) (m : Mem) (f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8 then some (1, m)
  else dpG3 n m f h v (mfindG dpSch m h 0)
def dpG3 (n : Nat) (m : Mem) (f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 DPM) (fr.tail.headD 0 * 4 + 3), m)
  else dpG4 h (dpNodeW n m (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def dpG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => dpG5 r (msetG dpSch m1 h 0 r)
def dpG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def dpNodeW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, f1, g, x, y, z =>
    if g = 4 ∨ g = 5 ∨ g = 6 then dpB1 n f1 y (dpGoW n m f1 x)
    else if g = 7 then dpL1 n f1 y z (dpGoW n m f1 x)
    else dpP1 (dpGoW n m f1 z)
def dpB1 (n : Nat) (f1 y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d1, m1) => dpB2 d1 (dpGoW n m1 f1 y)
def dpB2 (d1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d2, m2) => dpFin (maxW d1 d2) m2
def dpL1 (n : Nat) (f1 y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d1, m1) => dpL2 n f1 z d1 (dpGoW n m1 f1 y)
def dpL2 (n : Nat) (f1 z d1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d2, m2) => dpL3 d1 d2 (dpGoW n m2 f1 z)
def dpL3 (d1 d2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d3, m3) => dpFin (maxW (maxW d1 d2) d3) m3
def dpP1 : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d1, m1) => dpFin d1 m1
end

theorem dpSch_wf : dpSch.WF := ⟨by decide, by decide⟩

abbrev dpMR (m : Mem) (mp : Std.HashMap EIdx Nat) : Prop :=
  MemoRG dpSch bmKey (fun w : Word => w.toNat) m mp

def dpClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if rdW (m1.arr64 CTL) dpSch.cs + 2 = 0 then none else some (r, mclearG dpSch m1)

/-! ## `nest_phs` -/

mutual
def phsGoW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | k + 1, m, q, n, i => if n ≤ i then some m else phsK1 k m q n i (pinWordV m 53)
def phsK1 (k : Nat) (m : Mem) (q n i : Word) : Option Word → Option Mem
  | none => none
  | some z => if 4294967296 ≤ z then none else phsK2 k q n i (sointernW m z)
def phsK2 (k : Nat) (q n i : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (s, m1) => if 4294967296 ≤ s then none else phsK3 k q n i (fvinternW m1 i s)
def phsK3 (k : Nat) (q n i : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (v, m2) => if 4294967296 ≤ v then none else phsGoW k (m2.set64 IW (q + i) v) q n (i + 1)
end

def phsB (q nn : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m2 => some ([q, nn], m2)
def phsA (k : Nat) (nn : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => phsB q nn (phsGoW k m1 q nn 0)
def phsW (k : Nat) (m : Mem) (nn : Word) : Option (List Word × Mem) := phsA k nn (allocW m nn)
theorem decHL_write {k : IdxKind} (m : Mem) (q i v : Word) (ws : List (Idx k))
    (hv : v.toNat < 2 ^ 32) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hb : q.toNat + i.toNat < (m.arr64 IW).size) (h : decHL m q.toNat i.toNat = some ws) :
    decHL (m.set64 IW (q + i) v) q.toNat (i.toNat + 1) = some (ws ++ [decI v]) := by
  have hqi : (q + i).toNat = q.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  simp only [decHL]
  rw [hslice?_add]
  have h1 : (hslice? (iwA (m.set64 IW (q + i) v)) q.toNat i.toNat : Option (List (Idx k))) = some ws := by
    rw [← h]; simp only [decHL]
    apply hslice?_congr
    intro j hj
    simp only [iwA, set64IW_get]
    rw [ite_eq_right (by omega)]
  have h2 : (hslice? (iwA (m.set64 IW (q + i) v)) (q.toNat + i.toNat) 1 : Option (List (Idx k))) =
      some [decI v] := by
    rw [hslice?_succ]
    have : (hd? (iwA (m.set64 IW (q + i) v)) (q.toNat + i.toNat) : Option (Idx k)) = some (decI v) := by
      simp [hd?, iwA, set64IW_get, hqi, hb, hv]
    rw [this]; simp [hslice?]
  rw [h1, h2]; simp

theorem StageR.alloc {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {k q : Word} (hS : StageR dn vis fe m a) (h : allocW m k = some (q, m1)) :
    StageR dn vis fe m1 a ∧ IWGrow m m1 ∧ q = rdW (m.arr64 CTL) 200 ∧ q.toNat + k.toNat ≤ (m.arr64 IW).size ∧
      iwTop m1 = q.toNat + k.toNat := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.2
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts h h3
  subst hm1
  have hf := allocMem_frame m k
  have hqi : q.toNat = iwTop m := by simp only [iwTop, hq]
  have htop : iwTop (allocMem m k) = q.toNat + k.toNat := by
    simp only [iwTop, allocMem_top m k h5, ← hq]
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have h129 : rdW ((allocMem m k).arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : (allocMem m k).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  refine ⟨⟨CheckR.frame_iw hf hS.1, ?_, ?_, ?_, ?_, ?_⟩, allocMem_grow m k (by omega) h5, hq, hroom, htop⟩
  · rw [htop, hf.2.2.1 IW]; exact hroom
  · simp only [erTop, h129, hE]; exact h2
  · rw [hf.2.2.1 IW]; exact h3
  · rw [hE]; exact h4
  · rw [hf.2.2.1 CTL]; exact h5

/-! ## `nest_canon_crest` -/

def pccC (_r3 : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => if 4294967296 ≤ r then none else some ([1, r], m3)

end L.Ind

end
