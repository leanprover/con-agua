import ConAgua.Arena.RecCheckSpec.TaCW
import ConAgua.Arena.IndPosSpec.BvbWMfr

/-!
# RcLook

`taMR_mfr`, `RcMR`, `eftK2`, `HSl0`, `HSl0.of`, `HSl0.len` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The memos of the recursor check -/

theorem taMR_mfr {S : List ArrId} {T : List Word} {m m' : Mem} (hf : MFr S T m m') (hS : TAM ∉ S)
    (hT : (212 : Word) ∉ T) {mp : Std.HashMap EIdx EIdx} (h : taMR m mp) : taMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo TAM 212 (by decide) (by decide) hS hT
  exact memoRG_frame taSch taSch_wf bmKey (fun w : Word => decE w) A C hA hC m m' f mp h

/-- **The walk memos of the recursor check, well formed in `m`**: the positivity walks' (`PosMR`,
with `replace_fvars`' banked memo) and `target_abs`' (`ta`). Each walk clears its memo on entry,
so some well-formed memo suffices; carried across writers outside the memo region (`RcMR.fr`)
and across each walk by its own post (`RcMR.setRf`, …). -/
structure RcMR (m : Mem) : Prop where
  pos : PosMR m
  ta : ∃ mp, taMR m mp

/-! ## `erase_fvar_tys` -/

def eftK2 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r], m2)

/-! ## Slices decoded below the top unless empty -/

/-- A handle slice decoded at `(o, l)`, below the pool's top unless empty (an empty slice's offset
is whatever its record holds: a decoding below the tops says no more). -/
def HSl0 {k : IdxKind} (m : Mem) (o l : Word) (xs : List (Idx k)) : Prop :=
  decHL m o.toNat l.toNat = some xs ∧ (l = 0 ∨ o.toNat + l.toNat ≤ iwTop m)

theorem HSl0.of {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)} (hd : decHL m o.toNat l.toNat = some xs)
    (hb : o.toNat + l.toNat ≤ iwTop m) : HSl0 m o l xs := ⟨hd, .inr hb⟩

theorem HSl0.len {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)} (h : HSl0 m o l xs) :
    xs.length = l.toNat := decHL_length _ h.1

/-! ## `target_canon_params` -/

def tcpK1 (n : Nat) (e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => eftK2 (rxW n m1 (r1.headD 0) e)

/-- **The model of `target_canon_params`** (body fuel `n`). -/
def tcpW (n : Nat) (m : Mem) (pfo pfl e : Word) : Option (List Word × Mem) :=
  tcpK1 n e (recW m 3 [3, if pfl = 0 then 0 else pfo, pfl])

/-! ## The census theorems -/

/-- The lookups of this file. -/
structure RcLook (p : Prog) : Prop where
  rx : RxLook p
  nt : NtLook p
  r3 : p.lookup "rec3" = some rec3
  eft : p.lookup "erase_fvar_tys" = some eraseFVarTys
  tcp : p.lookup "target_canon_params" = some targetCanonParams
  tco : p.lookup "target_ctors_of" = some targetCtorsOf

end L.Ind

end
