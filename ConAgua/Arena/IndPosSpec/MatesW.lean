import ConAgua.Arena.IndCopy2
import ConAgua.Arena.Pins
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# MatesW

`pinWordV`, `pinWord_specV`, `canonK3`, `canonK2`, `canonK1`, `canonK0` and the lemmas only they use.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `pin_word` as a word model -/

def pinWordV (m : Mem) (k : Word) : Option Word :=
  if rdW (m.arr64 PINS) 0 = 0 then none else some (rdW (m.arr64 PINS) k)

theorem pinWord_specV (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ pinWordV s₀.mem k = some (r.headD 0); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [pinWordV]

/-! ## `nest_canon_sub` -/

def canonK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => if 4294967296 ≤ r then none else some ([1, r], m2)
def canonK2 (nn mi : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (s, m1) => if 4294967296 ≤ s then none else canonK3 (fvinternW m1 (nn + mi) s)
def canonK1 (nn mi : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => if 4294967296 ≤ z then none else canonK2 nn mi (sointernW m z)
def canonK0 (nn : Word) (m : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some fr => if fr.headD 0 = 0 then some ([0, 0], m)
      else canonK1 nn (fr.tail.headD 0) m (pinWordV m 53)
def canonW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, us, nn, c, v =>
    if v ≠ us then some ([0, 0], m) else canonK0 nn m (findW n m no nl c)

theorem lt_of_notbig {z : Word} (h : ¬ 4294967296 ≤ z) : z.toNat < 2 ^ 32 := by
  have : ¬ (4294967296 : Word).toNat ≤ z.toNat := fun hh => h (UInt64.le_iff_toNat_le.mpr hh)
  have e : (4294967296 : Word).toNat = 4294967296 := by decide
  omega

/-! ## `nest_frame_mates_go` -/

mutual
def matesW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, c, off, l, oO, oL =>
    if l = 0 then some ([oO, oL], m)
    else matesK1 n m c off l oO oL (containsW n m oO oL (rdW (m.arr64 EREC) off))
def matesK1 (n : Nat) (m : Mem) (c off l oO oL : Word) : Option Word → Option (List Word × Mem)
  | none => none
  | some b =>
    if rdW (m.arr64 EREC) off = c ∨ b ≠ 0 then matesK3 (matesW n m c (off + 1) (l - 1) oO oL)
    else matesK2 n c off l (snocW n m oO oL (rdW (m.arr64 EREC) off))
def matesK2 (n : Nat) (c off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => matesK3 (matesW n m2 c (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0))
def matesK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0], m3)
end

theorem getD2_eq (vl : List Word) : vl.getD 2 0 = vl.tail.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl
theorem getD3_eq (vl : List Word) : vl.getD 3 0 = vl.tail.tail.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;> rfl
theorem getD1_eq' (vl : List Word) : vl.getD 1 0 = vl.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl

/-- The word-valued memo relation of the mentions walk. -/
abbrev maMR (m : Mem) (mp : Std.HashMap EIdx Bool) : Prop :=
  MemoRG maSch bmKey (fun w : Word => w != 0) m mp

theorem maSch_wf : maSch.WF := ⟨by decide, by decide⟩

/-- **The stage relation across a writer above array 136 and `CTL[129]`** (the per-call memos). -/
theorem StageR.frame_hi {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {A : List ArrId} {C : List Word} (hS : StageR dn vis fe m a) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 137 ≤ b ∧ b < 256 ∧ (b < 140 ∨ 144 ≤ b)) (hC : ∀ x ∈ C, 130 ≤ x.toNat ∧ x.toNat ≠ 133) (hA2 : IW ∉ A) (hC2 : (200 : Word) ∉ C) :
    StageR dn vis fe m' a ∧ IWGrow m m' := by
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW hA2 (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (fun h => by have := hA _ h; simp [EREC] at this)
    (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 200 hC2
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 :=
    hf.2.1 129 (fun h => by have := (hC _ h).1; simp at this)
  refine ⟨⟨CheckR.frame_hi hA hC hf hS.1, ?_⟩, ?_⟩
  · simp only [IWOK, iwTop, erTop, hI, hE, h200, h129, hf.2.2.1 CTL]; exact hS.2
  · refine ⟨?_, ?_, fun i _ => by rw [hI], fun i _ => by rw [hE]⟩
    · simp only [iwTop, h200]; exact Nat.le_refl _
    · simp only [erTop, h129]; exact Nat.le_refl _

end L.Ind

end
