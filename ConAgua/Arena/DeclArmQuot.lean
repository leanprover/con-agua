import ConAgua.Arena.DeclAxiomSpec4
import ConAgua.Arena.DeclCheckLoop

/-!
# The quotient pin: `quot_pin_hit(k, q)` (lane `decls3`)

`quotPinHit k cv`: the record is the pinned quotient block's constant at its own slot, compared at
`toConstantVal` up to the canonical form (`cv_canon_eq`, helper `decls3-canon`, taken here as the
hypothesis `CvCanonSpec` until it lands). Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind

/-- What `cv_canon_eq` must refine (helper `decls3-canon`'s statement shape). -/
def CvCanonSpec (p : Prog) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q r : Word)
    (cv cv' : IConstantVal),
    RefAM p "cv_canon_eq" [q, r]
      (fun m a => StageR dn vis fe m a ∧ decCV (erA m) q.toNat = some cv ∧
        decCV (erA m) r.toNat = some cv')
      (cv.canonEq cv') (KeepPost dn vis fe decW0B)

section model
variable (p : Prog)

/-- After the comparison. -/
def qphK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0], m3)

/-- After `ci_to_cv`. -/
def qphK2 (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => qphK3 (callW p n "cv_canon_eq" [q, r2.headD 0] m2)

/-- After the block's read. -/
def qphK1 (n : Nat) (k q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.tail.headD 0 ≤ k then some ([0], m1)
    else qphK2 p n q (callW p n "ci_to_cv" [rdW (m1.arr64 IW) (r1.headD 0 + k)] m1)

/-- **The model of `quot_pin_hit(k, q)`.** -/
def qphW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, k, q => qphK1 p n k q (stubM "rom_basis_decls" m [4])

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (k q : Word) (r1 r2 r3 : List Word)
theorem qphW_step : qphW p (n + 1) m k q = qphK1 p n k q (stubM "rom_basis_decls" m [4]) := rfl
theorem qphK1_some : qphK1 p n k q (some (r1, m1)) =
    if r1.tail.headD 0 ≤ k then some ([0], m1)
    else qphK2 p n q (callW p n "ci_to_cv" [rdW (m1.arr64 IW) (r1.headD 0 + k)] m1) := rfl
theorem qphK2_some : qphK2 p n q (some (r2, m2)) =
    qphK3 (callW p n "cv_canon_eq" [q, r2.headD 0] m2) := rfl
theorem qphK3_some : qphK3 (some (r3, m3)) = some ([r3.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] qphW_step => qphW p (n + 1) m k q
grind_pattern [ind_grind] qphK1_some => qphK1 p n k q (some (r1, m1))
grind_pattern [ind_grind] qphK2_some => qphK2 p n q (some (r2, m2))
grind_pattern [ind_grind] qphK3_some => qphK3 (some (r3, m3))

theorem qph_specW (hp : p.lookup "quot_pin_hit" = some quotPinHitL) (n : Nat) (s₀ : St)
    (k q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "quot_pin_hit" [k, q]
    ⦃fun r s' => LocEq s' s₀ ∧ qphW p n s₀.mem k q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, quotPinHitL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "rom_basis_decls" n, callW_spec p n "ci_to_cv",
        callW_spec p n "cv_canon_eq"] <;>
      finish (gen := 20) [rdW_eq]

end model

theorem slot_lt (k : ConLeche.QuotKind) : k.slot < 5 := by cases k <;> decide

/-- **`quot_pin_hit(k, q)` refines `quotPinHit`** at the model level. -/
theorem qphW_ok {p : Prog} (hC : CanonProg p) (hCV : CvCanonSpec p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal} {k : ConLeche.QuotKind}
    (hW : qphW p n m (UInt64.ofNat k.slot) q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    ∃ b a', (quotPinHit k cv).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decW0B m' r b := by
  have hks : (UInt64.ofNat k.slot).toNat = k.slot :=
    UInt64.toNat_ofNat_of_lt' (by have := slot_lt k; rw [UInt64_size_eq]; omega)
  cases n with
  | zero => simp [qphW] at hW
  | succ n =>
  rw [qphW_step] at hW
  cases h1 : stubM "rom_basis_decls" m [4] with
  | none => rw [h1] at hW; cases hW
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, qphK1_some] at hW
  obtain ⟨blk, a1, hrun1, hS1, hg1, hD1, hr1⟩ := romBasisDecls_spec dn vis fe 4 (by decide) m m1 a r1 h1 hS
  have hrun1' : (BasisKind.decls .quotK).run a = .ok (blk, a1) := hrun1
  have hlen : blk.length = (r1.tail.headD 0).toNat := decPL_length (truncM m1) hD1
  generalize r1.headD 0 = o at hW hD1 hlen
  generalize r1.tail.headD 0 = l at hW hD1 hlen
  by_cases hl : l ≤ UInt64.ofNat k.slot
  · rw [if_pos hl] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    have hn : blk[k.slot]? = none := by
      apply List.getElem?_eq_none; rw [hlen]
      have := UInt64.le_iff_toNat_le.mp hl; omega
    refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
    simp only [quotPinHit, StateT.run_bind, hrun1', exc_ok_bind', hn]
    rfl
  rw [if_neg hl] at hW
  have hlt : k.slot < (l).toNat := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl); omega
  obtain ⟨v, ci, hv, hci, hget⟩ := decPL_get _ _ _ hD1 k.slot hlt
  -- the pointer word
  have hvm : iwN m1 (o.toNat + k.slot) = some v :=
    (IWGrow.refl m1).truncExt.1.nat? hv
  obtain ⟨w, hw, rfl⟩ : ∃ w, (iwA m1)[o.toNat + k.slot]? = some w ∧ w.toNat = v := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
  have hob : o.toNat + k.slot < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hw).1; have := hS1.2.2.2.1; simp only [iwA] at *; omega
  have hidx : (o + UInt64.ofNat k.slot).toNat = o.toNat + k.slot := by
    rw [UInt64.toNat_add, hks]; simp; omega
  have ew : rdW (m1.arr64 IW) (o + UInt64.ofNat k.slot) = w := by
    simp only [rdW, hidx]; simp only [iwA] at hw; simp [hw]
  rw [ew] at hW
  have hciP : decCI (erecP m1) dn w.toNat = some ci := ArrExt.decCI (truncM_erecP m1) hci
  -- `ci_to_cv`
  cases h2 : callW p n "ci_to_cv" [w] m1 with
  | none => rw [h2] at hW; cases hW
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, qphK2_some] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hcv2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (ciToCv_refines p hC dn vis fe w ci n ⟨m1, Locals.init []⟩ a1 ⟨hS1, hciP⟩) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  generalize AM.res ci.toConstantVal a1 = pcv at hrun2 hcv2
  generalize AM.st ci.toConstantVal a1 = a2 at hrun2 hS2
  -- `cv_canon_eq`
  cases h3 : callW p n "cv_canon_eq" [q, r2.headD 0] s2.mem with
  | none => rw [h3] at hW; cases hW
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, qphK3_some] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  have hg12 := hg1.trans hg2
  obtain ⟨s3, hs3, -, hok3, hS3, hg3, hd3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (hCV dn vis fe q (r2.headD 0) cv pcv n ⟨s2.mem, Locals.init []⟩ a2
      ⟨hS2, ArrExt.decCV (IWGrow.erecExt hg12) hq, ArrExt.decCV (erecP_ext _) hcv2⟩) h3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  refine ⟨_, _, ?_, hS3, hg12.trans hg3, hd3⟩
  simp only [quotPinHit, StateT.run_bind, hrun1', exc_ok_bind', hget, hrun2]
  exact hrun3

end L.Arena
