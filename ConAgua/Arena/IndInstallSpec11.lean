import ConAgua.Arena.IndInstallSpec10

/-!
# Refinements of `IndInstall`, part 11 (lane `indproofs2`, helper `install`): `consBlockCtors`

The members' constructors pushed member by member (`cons_sum_ctors`, lead's), by recursion as the
twin's.
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A member's constructors: a pointer to `[off, len]` of `[cv, nF]` pointers. -/
def decCNS (m : Mem) (mp : Nat) : Option (List (IConstantVal × Nat)) := decAt m (decPL m (decCN m)) mp

theorem decCNS_mono (q : Nat) : OMono (fun m => decCNS m q) :=
  OMono.decAt (fun o l => OMono.decPL decCN_mono o l) q

mutual
/-- **The model of `cons_block_ctors(nP, o, l, vis)`** at exec fuel `n`. -/
def icbcW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, nP, o, l, vis =>
    if l = 0 then some ([vis], m)
    else icbcK1 p n nP o l (callW p n "cons_sum_ctors" [nP, rdW (m.arr64 IW) (rdW (m.arr64 IW) o),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1), vis] m)
/-- After a member's constructors: the rest. -/
def icbcK1 (p : Prog) (n : Nat) (nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icbcK2 (icbcW p n m nP (o + 1) (l - 1) (r.headD 0))
/-- The returned view. -/
def icbcK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (nP o l vis : Word) (r : List Word)
theorem icbcW_zero : icbcW p 0 m nP o l vis = none := by simp [icbcW]
theorem icbcW_nil (h : l = 0) : icbcW p (n + 1) m nP o l vis = some ([vis], m) := by simp [icbcW, h]
theorem icbcW_cons (h : l ≠ 0) : icbcW p (n + 1) m nP o l vis =
    icbcK1 p n nP o l (callW p n "cons_sum_ctors" [nP, rdW (m.arr64 IW) (rdW (m.arr64 IW) o),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1), vis] m) := by simp [icbcW, h]
theorem icbcK1_some : icbcK1 p n nP o l (some (r, m)) = icbcK2 (icbcW p n m nP (o + 1) (l - 1) (r.headD 0)) := by
  simp [icbcK1]
theorem icbcK2_some : icbcK2 (some (r, m)) = some ([r.headD 0], m) := by simp [icbcK2]
end arms
attribute [ind_grind] icbcW_nil icbcW_cons icbcK1_some icbcK2_some

theorem icbc_spec (p : Prog) (hp : p.lookup "cons_block_ctors" = some consBlockCtors) (n : Nat) :
    ∀ (s₀ : St) (nP o l vis : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "cons_block_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ icbcW p n s₀.mem nP o l vis = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ nP o l vis; rw [invoke_eq _ hp]; simp only [callFn, consBlockCtors]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP o l vis
    rw [invoke_eq _ hp]
    simp only [callFn, consBlockCtors]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "cons_sum_ctors", ih] <;>
      finish (gen := 20) [rdW_eq]

/-- **`cons_block_ctors`' model refines `consBlockCtors`.** -/
theorem icbcW_ok (p : Prog) (hRp : RecProg p) (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hcs : p.lookup "cons_sum_ctors" = some consSumCtorsL) (dn : NIdx → Option ConLeche.Name)
    (nP : Word) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (o l : Word)
      (css : List (List (IConstantVal × Nat))) (r : List Word),
    icbcW p n m nP o l vis = some (r, m') → StageR dn vis fe m a → PSlR decCNS css o l m →
    StageR dn (r.headD 0) (ConRon.Arena.consBlockCtors nP.toNat css fe) m' a ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' a vis fe o l css r h; rw [icbcW_zero] at h; cases h
  | succ n ih =>
  intro m m' a vis fe o l css r h hS hcss
  by_cases hl : l = 0
  · rw [icbcW_nil p n m nP o l vis hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : css = [] := by
      have h := hcss.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨hS, IWGrow.refl m⟩
  obtain ⟨q, cs, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hcss hl
  rw [icbcW_cons p n m nP o l vis hl, hw] at h
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  -- the member's `[off, len]` words
  have hdx' : decCNS (truncM m) q = some cs := hdx
  simp only [decCNS] at hdx'
  obtain ⟨co, cl, hco, hcl, hcsd⟩ := decAt_some hdx'
  obtain ⟨hwo, hcob, -⟩ := partsIwRd hco (w := UInt64.ofNat q) hq'
  obtain ⟨hwl, hclb, -⟩ := partsIwRd hcl (w := UInt64.ofNat q + 1) (by
    have := partsIwLt hcl; have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    rw [UInt64.toNat_add, hq']; simp; omega)
  rw [hwo, hwl] at h
  rcases h1 : callW p n "cons_sum_ctors" [nP, UInt64.ofNat co, UInt64.ofNat cl, vis] m with _ | ⟨r1, m1⟩
  · rw [h1] at h; simp [icbcK1] at h
  rw [h1, icbcK1_some] at h
  obtain ⟨s1, rfl, -, hS1, hg1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (consSumCtors_refines p hRp hci hcs n ⟨m, Locals.init []⟩ a dn fe vis nP _ _ cs hS
      (by rw [UInt64.toNat_ofNat_of_lt' hcob, UInt64.toNat_ofNat_of_lt' hclb]; exact hcsd)) h1
  rcases h2 : icbcW p n s1.mem nP (o + 1) (l - 1) (r1.headD 0) with _ | ⟨r2, m2⟩
  · rw [h2] at h; simp [icbcK2] at h
  rw [h2, icbcK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS2, hg2⟩ := ih s1.mem m2 a (r1.headD 0) _ (o + 1) (l - 1) rest r2 h2 hS1 (hrest.grow decCNS_mono hg1)
  refine ⟨?_, hg1.trans hg2⟩
  simpa [ConRon.Arena.consBlockCtors] using hS2

/-- **`cons_block_ctors` refines `consBlockCtors`**: from the stage relation at `vis` of `fe` and
the members' constructor lists decoded below the tops, a returning run returns the view of the
environment with every member's constructors pushed, member by member. -/
@[refines ConRon.Arena.consBlockCtors]
theorem consBlockCtors_refines (p : Prog) (hRp : RecProg p)
    (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hcs : p.lookup "cons_sum_ctors" = some consSumCtorsL)
    (hp : p.lookup "cons_block_ctors" = some consBlockCtors) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (nP o l vis : Word)
    (css : List (List (IConstantVal × Nat))) (hS : StageR dn vis fe s₀.mem a₀)
    (hcss : PSlR decCNS css o l s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_block_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn (r.headD 0) (ConRon.Arena.consBlockCtors nP.toNat css fe) s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (icbc_spec p hp n s₀ nP o l vis) fun r _ ⟨hl, hm⟩ =>
    ⟨hl, icbcW_ok p hRp hci hcs dn nP n _ _ a₀ vis fe o l css r hm hS hcss⟩

end L.Ind
