import ConAgua.Arena.DeclRomStubs
import ConAgua.Rom.CIReadSpec
import ConAgua.Arena.DeclCanonEq
import ConRon.Bridge.Checker.Basis

/-!
# `check_basis_decl(vis, kind)` refines `checkBasisDecl` (lane `decls3`)

The quotient block first requires the pinned `Eq` basis (`find_is` against `rom_ci(0)`, helper
`decls3-canon`'s `findIs_spec`), then the annotated block (`rom_basis_decls_a(kind)`) is installed
(`install_basis_decls`, `DeclBasisSpec.lean`). Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- A constant record decoded below the top decodes in the whole pool. -/
theorem decRCI_get {dn : NIdx → Option ConLeche.Name} {m : Mem} {r : List Word}
    {ci : IConstantInfo} (h : decRCI dn m r ci) : decCI (erA m) dn (r.headD 0).toNat = some ci :=
  DecB.get ⟨fun _ _ _ he h => he.2.decCI h⟩ h

section model
variable (p : Prog)

/-- After the install. -/
def cbdK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([r5.headD 0], m5)

/-- After the block's read: the install. -/
def cbdK4 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    cbdK5 (callW p n "install_basis_decls" [vis, r4.headD 0, r4.tail.headD 0] m4)

/-- After `find_is`: abort on a miss. -/
def cbdK3 (n : Nat) (vis k : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then none else cbdK4 p n vis (callW p n "rom_basis_decls_a" [k] m3)

/-- After `rom_ci(0)`. -/
def cbdK2 (n : Nat) (vis k en : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => cbdK3 p n vis k (callW p n "find_is" [vis, en, r2.headD 0] m2)

/-- After the `Eq` pin. -/
def cbdK1 (n : Nat) (vis k : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => cbdK2 p n vis k (r1.headD 0) (callW p n "rom_ci" [0] m1)

/-- **The model of `check_basis_decl(vis, kind)`.** -/
def cbdW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, k =>
    if k = 4 then cbdK1 p n vis k (pinAtW m 0) else cbdK4 p n vis (callW p n "rom_basis_decls_a" [k] m)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis k en : Word) (r1 r2 r3 r4 r5 : List Word)
theorem cbdW_step : cbdW p (n + 1) m vis k =
    if k = 4 then cbdK1 p n vis k (pinAtW m 0) else cbdK4 p n vis (callW p n "rom_basis_decls_a" [k] m) :=
  rfl
theorem cbdK1_some : cbdK1 p n vis k (some (r1, m1)) =
    cbdK2 p n vis k (r1.headD 0) (callW p n "rom_ci" [0] m1) := rfl
theorem cbdK2_some : cbdK2 p n vis k en (some (r2, m2)) =
    cbdK3 p n vis k (callW p n "find_is" [vis, en, r2.headD 0] m2) := rfl
theorem cbdK3_some : cbdK3 p n vis k (some (r3, m3)) =
    if r3.headD 0 = 0 then none else cbdK4 p n vis (callW p n "rom_basis_decls_a" [k] m3) := rfl
theorem cbdK4_some : cbdK4 p n vis (some (r4, m4)) =
    cbdK5 (callW p n "install_basis_decls" [vis, r4.headD 0, r4.tail.headD 0] m4) := rfl
theorem cbdK5_some : cbdK5 (some (r5, m5)) = some ([r5.headD 0], m5) := rfl
end arms

grind_pattern [ind_grind] cbdW_step => cbdW p (n + 1) m vis k
grind_pattern [ind_grind] cbdK1_some => cbdK1 p n vis k (some (r1, m1))
grind_pattern [ind_grind] cbdK2_some => cbdK2 p n vis k en (some (r2, m2))
grind_pattern [ind_grind] cbdK3_some => cbdK3 p n vis k (some (r3, m3))
grind_pattern [ind_grind] cbdK4_some => cbdK4 p n vis (some (r4, m4))
grind_pattern [ind_grind] cbdK5_some => cbdK5 (some (r5, m5))

theorem cbd_specW (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "check_basis_decl" = some checkBasisDeclL) (n : Nat) (s₀ : St) (vis k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_basis_decl" [vis, k]
    ⦃fun r s' => LocEq s' s₀ ∧ cbdW p n s₀.mem vis k = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBasisDeclL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p hpa n,
        callW_spec p n "rom_ci", callW_spec p n "find_is", callW_spec p n "rom_basis_decls_a",
        callW_spec p n "install_basis_decls"] <;>
      finish (gen := 20)

end model

local notation "V" => ConLeche.CheckMode.verified

/-- The block install after the read, at the model level. -/
theorem cbdK4_ok {p : Prog} (hB : BasisProg p) (hR : L.Rom.RomRefs p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {k : Word} {r : List Word} (hk : k.toNat < 5)
    (h : cbdK4 p n vis (callW p n "rom_basis_decls_a" [k] m) = some (r, m'))
    (hS : StageR dn vis fe m a)
    (hQ : k.toNat = 4 → ConRon.Bridge.StateOK a ∧ L.Rom.NamesDn dn a L.Rom.quotNames) :
    ∃ fe' a', (do installBasisDecls fe (← BasisKind.declsA (basisOfW k.toNat))).run a =
      .ok (fe', a') ∧ StageR dn (r.headD 0) fe' m' a' ∧ IWGrow m m' := by
  cases h4 : callW p n "rom_basis_decls_a" [k] m with
  | none => rw [h4] at h; cases h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, cbdK4_some] at h
  obtain ⟨cis, a4, hrun4, hS4, hg4, hD4, -⟩ :
      ∃ cis a4, (BasisKind.declsA (basisOfW k.toNat)).run a = .ok (cis, a4) ∧
        KeepPost dn vis fe (decRBlk dn) m m4 a4 r4 cis := by
    by_cases h4' : k.toNat < 4
    · exact hR.basisA dn vis fe k h4' n m a r4 m4 hS h4
    · have hk4 : k.toNat = 4 := by omega
      have : k = 4 := UInt64.toNat_inj.mp (by rw [hk4]; rfl)
      subst this
      obtain ⟨hok, hN⟩ := hQ hk4
      exact hR.quotA dn vis fe n m a r4 m4 ⟨hS, hok, hN⟩ h4
  cases h5 : callW p n "install_basis_decls" [vis, r4.headD 0, r4.tail.headD 0] m4 with
  | none => rw [h5] at h; cases h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, cbdK5_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s5, hs5, -, hok5, hS5, hg5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (installBasisDecls_refines p hB n ⟨m4, Locals.init []⟩ a4 dn fe vis _ _ cis hS4 hD4) h5
  subst hs5
  refine ⟨_, _, ?_, by simpa using hS5, hg4.trans hg5⟩
  simp only [StateT.run_bind, hrun4, exc_ok_bind']
  exact AM.run_of_ok _ _ hok5

/-- **`check_basis_decl(vis, kind)` refines `checkBasisDecl`** (through the ROM stubs). -/
@[refines ConRon.Arena.checkBasisDecl]
theorem checkBasisDecl_refines (p : Prog) (hB : BasisProg p) (hC : CanonProg p) (hR : L.Rom.RomRefs p)
    (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "check_basis_decl" = some checkBasisDeclL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (hdn : DnInj dn) (fe : IFEnv) (vis k : Word)
    (hk : k.toNat < 5) (hS : StageR dn vis fe s₀.mem a₀)
    (hQ : k = 4 → ConRon.Bridge.StateOK a₀ ∧ L.Rom.NamesDn dn a₀ L.Rom.quotNames) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_basis_decl" [vis, k]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkBasisDecl fe (basisOfW k.toNat)) a₀ ∧
      StageR dn (r.headD 0) (AM.res (checkBasisDecl fe (basisOfW k.toNat)) a₀) s'.mem
        (AM.st (checkBasisDecl fe (basisOfW k.toNat)) a₀) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (cbd_specW p hpa hp n s₀ vis k) ?_
  rintro r s' ⟨hl, h⟩
  refine ⟨hl, ?_⟩
  suffices ∃ fe' a', (checkBasisDecl fe (basisOfW k.toNat)).run a₀ = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' s'.mem a' ∧ IWGrow s₀.mem s'.mem by
    obtain ⟨fe', a', hrun, hS', hg⟩ := this
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    exact ⟨hok, by rw [hst, hres]; exact hS', hg⟩
  cases n with
  | zero => simp [cbdW] at h
  | succ n =>
  rw [cbdW_step] at h
  by_cases h4 : k = 4
  · rw [if_pos h4] at h
    subst h4
    -- the `Eq` pin
    cases h1 : pinAtW s₀.mem 0 with
    | none => rw [h1] at h; cases h
    | some rm1 =>
    obtain ⟨r1, m1⟩ := rm1
    rw [h1, cbdK1_some] at h
    obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.1.pins
    rw [hm1, hr1] at h
    simp only [List.headD_cons] at h
    -- `eqA`
    cases h2 : callW p n "rom_ci" [0] s₀.mem with
    | none => rw [h2] at h; cases h
    | some rm2 =>
    obtain ⟨r2, m2⟩ := rm2
    rw [h2, cbdK2_some] at h
    obtain ⟨ea, a2, hrun2, hS2, hg2, hea⟩ := hR.ci dn vis fe 0 (by decide) n s₀.mem a₀ r2 m2 hS h2
    -- `find_is`
    cases h3 : callW p n "find_is" [vis, pinW s₀.mem (1 + (0 : Word).toNat), r2.headD 0] m2 with
    | none => rw [h3] at h; cases h
    | some rm3 =>
    obtain ⟨r3, m3⟩ := rm3
    rw [h3, cbdK3_some] at h
    obtain ⟨s3, hs3, -, hok3, hS3, hg3, hb3, -⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (findIs_spec p hC dn vis fe hdn _ _ ea n ⟨m2, Locals.init []⟩ a2
        ⟨hS2, hl1, decRCI_get hea⟩) h3
    subst hs3
    have hrun3 := AM.run_of_ok _ _ hok3
    simp only [AM.st_pure, AM.res_pure] at hS3 hb3
    by_cases h0 : r3.headD 0 = 0
    · rw [if_pos h0] at h; cases h
    rw [if_neg h0] at h
    have hfind : (fe.find? (decI (pinW s₀.mem (1 + (0 : Word).toNat))) == some ea) = true := by
      rw [← hb3]; simpa using h0
    have hrun2' : eqA.run a₀ = .ok (ea, a2) := hrun2
    obtain ⟨hok0, hN0⟩ := hQ rfl
    have st2 := (ConRon.Bridge.internCI_fresh hok0 hrun2').1
    obtain ⟨fe', a', hrun', hS', hg'⟩ := cbdK4_ok hB hR (by decide) h hS3
      (fun _ => ⟨st2.ok, L.Rom.NamesDn.ext hN0 st2.ext⟩)
    refine ⟨fe', a', ?_, hS', hg2.trans (hg3.trans hg')⟩
    simp only [checkBasisDecl, basisOfW, show (4 : Word).toNat = 4 from rfl,
      show (ConLeche.BasisKind.quotK == ConLeche.BasisKind.quotK) = true from rfl, if_true,
      StateT.run_bind, pinEq, PIN_EQ, show (0 : Nat) = (0 : Word).toNat from rfl, hrun1,
      exc_ok_bind']
    have hrun2' : eqA.run a₀ = .ok (ea, a2) := hrun2
    rw [hrun2', exc_ok_bind']
    simp only [hfind, if_true]
    exact hrun'
  · rw [if_neg h4] at h
    obtain ⟨fe', a', hrun', hS', hg'⟩ := cbdK4_ok hB hR hk h hS (fun e => absurd
      (UInt64.toNat_inj.mp (by rw [e]; rfl)) h4)
    refine ⟨fe', a', ?_, hS', hg'⟩
    have hq : (basisOfW k.toNat == ConLeche.BasisKind.quotK) = false := by
      have : k.toNat ≠ 4 := fun e => h4 (UInt64.toNat_inj.mp (by simpa using e))
      unfold basisOfW
      split <;> simp_all <;> omega
    simp only [checkBasisDecl, hq, Bool.false_eq_true, if_false]
    exact hrun'

end L.Arena
