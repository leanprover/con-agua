module

public import ConAgua.Arena.RecCheckSpec.EqWDec
import ConAgua.Arena.RecCheckSpec.TruncSl
import ConAgua.Arena.RecCheckSpec.EeW2
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSim
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.RecCheckSpec.EeW

@[expose] public section

/-!
# TmFields

`HSl0.grow`, `tkHeads`, `tk53_eq`, `tteW_ok`, `tmFields`, `noF_ok`.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem HSl0.grow {k : IdxKind} {m m' : Mem} {o l : Word} {xs : List (Idx k)} (h : HSl0 m o l xs)
    (hg : IWGrow m m') : HSl0 m' o l xs := by
  obtain ⟨hd, hb⟩ := h
  rcases hb with rfl | hb
  · have hx : xs = [] := by have := decHL_length _ hd; simpa using this
    subst hx
    exact ⟨by simp [decHL, hslice?], .inl rfl⟩
  · exact ⟨by rw [decHL_grow hg hb]; exact hd, .inr (Nat.le_trans hb hg.iw)⟩

end L.Ind

end

end

section

noncomputable section

/-!
# `RecCheck`: `targetK53`, the relational side (lane `indproofs3`, helper `rec`)

The twin split at the L functions' boundaries (`tkTele`, `tkHeads`, `tkArgs`, verbatim pieces of
`targetK53`; `tk53_eq` puts them back together), each simulated by its word model.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `targetK53`'s head check. -/
def tkHeads (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx) (Mc : TargetMajor) (leafW majDom : EIdx) :
    AM Bool := do
  let lh ← ConRon.Arena.getAppFn coreWalkFuel leafW
  let mh ← ConRon.Arena.getAppFn coreWalkFuel majDom
  if lh.tag == ETag.const && mh.tag == ETag.const then
    match ← ConRon.Arena.viewConst lh with
    | none => failDanglingE
    | some (I', us') =>
      match ← ConRon.Arena.viewConst mh with
      | none => failDanglingE
      | some (I, _) => do
        let la ← ConRon.Arena.getAppArgs coreWalkFuel leafW
        let ma ← ConRon.Arena.getAppArgs coreWalkFuel majDom
        if !(I' == I && la.length == ma.length) then pure false
        else tkArgs fe p formerTys Mc I' us' la ma
  else pure false

theorem tk53_eq (fe : IFEnv) (p : BlockShape) (formerTys : List EIdx) (Mc : TargetMajor)
    (tele : List EIdx) (majDom f : EIdx) :
    ConRon.Arena.targetK53 V fe p formerTys Mc tele majDom f = (do
      match ← ConRon.Arena.stripPis tele.length f with
      | none => pure false
      | some (teleW, leafW) => do
        let c ← tkTele teleW tele
        if c then tkHeads fe p formerTys Mc leafW majDom else pure false) := by
  rw [ConRon.Arena.targetK53]
  apply bind_congr; intro o
  rcases o with _ | ⟨teleW, leafW⟩
  · rfl
  · simp only [tkTele, bind_assoc, pure_bind]
    apply bind_congr; intro ew; apply bind_congr; intro et
    by_cases h : ew = et
    · subst h; simp only [bne_self_eq_false, beq_self_eq_true, Bool.false_eq_true, ite_false, ite_true]; rfl
    · have h1 : (ew != et) = true := by simpa using h
      have h2 : (ew == et) = false := by simpa using h
      simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false]

/-! ## `erase_each`, `target_k53_tele` simulated -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem tteW_ok (n : Nat) {m m' : Mem} {a : AState} {bso bsl teo tel : Word} {r : List Word}
    {bs tele : List EIdx} (h : tteW n m bso bsl teo tel = some (r, m')) (hS : StageR vis fe m a)
    (hbs : HSl0 m bso bsl bs) (htl : HSl0 m teo tel tele) (hP : RcMR m) :
    ∃ c a', (tkTele bs tele).run a = .ok (c, a') ∧ (r.headD 0 != 0) = c ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  sorry

end rel

/-- The fields of a `TargetMajor` record decoded below the tops that `target_k53_args` reads. -/
theorem tmFields {m : Mem} {w : Word} {TM : TargetMajor} (h : DecB (fun m => decTM m w.toNat) m TM)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (w + 1)) ∧ decI (rdW (m.arr64 IW) (w + 1)) = TM.lvls ∧
    HSl0 m (rdW (m.arr64 IW) (w + 2)) (rdW (m.arr64 IW) (w + 3)) TM.ds ∧
    (rdW (m.arr64 IW) (w + 4)).toNat = TM.nPc ∧
    HSl0 m (rdW (m.arr64 IW) (w + 11)) (rdW (m.arr64 IW) (w + 12)) TM.pfvs ∧ w.toNat + 12 < iwTop m := by
  have h' : decTM (truncM m) w.toNat = some TM := h
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨i0, hi0, lv, hlv, ds, hds, nP, hnP, nI, -, cs, -, mb, -, nfs, -, pf, hpf, rfl⟩ := h'
  obtain ⟨hl1, hl2⟩ := truncH (i := 1) hlv hsz
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hds
  have hsl := truncSl (w := w) (i := 2) ho (by simpa [Nat.add_assoc] using hl) hd hsz
  obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some hpf
  have hsl' := truncSl (w := w) (i := 11) ho' (by simpa [Nat.add_assoc] using hl') hd' hsz
  obtain ⟨-, hnm⟩ := rec2IwN_trunc hnP
  obtain ⟨e4, t4⟩ := rec2RdN (w := w) (k := 4) hnm hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat (2 + 1) = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl,
    show UInt64.ofNat 11 = (11 : Word) from rfl, show UInt64.ofNat (11 + 1) = (12 : Word) from rfl] at hl1 hl2 hsl hsl' e4
  exact ⟨hl1, hl2, hsl, by rw [e4, t4], hsl', by have := (rec2IwN_trunc hl').1; omega⟩

section rel2
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem noF_ok (n : Nat) {m m' : Mem} {a : AState} {no nl e r : Word} {names : List NIdx}
    (h : noF n m no nl 0 0 e = some (r, m')) (hS : StageR vis fe m a) (he : H e)
    (hno : decHL m no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop m) (hP : RcMR m) :
    ∃ b, (ConRon.Arena.nestOcc names 0 0 (decE e)).run a = .ok (b, a) ∧ (r != 0) = b ∧
      StageR vis fe m' a ∧ IWGrow m m' ∧ RcMR m' := by
  sorry

end rel2

end L.Ind

end
end

end
