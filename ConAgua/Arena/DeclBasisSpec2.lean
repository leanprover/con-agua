import ConAgua.Rom.CIReadSpec
import ConRon.Bridge.Checker.Basis
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

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

/-- **The model of `check_basis_decl(vis, kind)`, both outcomes**: the ROM readers and `find_is`
(outside the verdict closure) lifted, `install_basis_decls` by its unified model. -/
l_model checkBasisDecl_specE (p : Prog) (hB : BasisProg p) (hpa : p.lookup "pin_at" = some pinAtL)
  (hp : p.lookup "check_basis_decl" = some checkBasisDeclL)
  fns [hp ↦ checkBasisDeclE]
  specs [pinAt_specW p hpa n, callW_spec p n "rom_ci", callW_spec p n "find_is",
    callW_spec p n "rom_basis_decls_a", installBasisDecls_specE p hB n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

local notation "V" => ConLeche.CheckMode.verified

/-- The block's read and install (`j1`), both outcomes. -/
theorem cbdJ_ref {p : Prog} (hB : BasisProg p) (hR : L.Rom.RomRefs p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m : Mem}
    {k : Word} (hk : k.toNat < 5) (hS : StageR dn vis fe m a)
    (hQ : k.toNat = 4 → ConRon.Bridge.StateOK a ∧ L.Rom.NamesDn dn a L.Rom.quotNames) :
    RefE True (checkBasisDeclE.j1 p n vis k m)
      (do installBasisDecls fe (← BasisKind.declsA (basisOfW k.toNat)) : AM IFEnv) a
      (fun v fe' a' => IbdPost dn m v.1 v.2 fe' a') := by
  rw [checkBasisDeclE.j1.arm1]
  rcases h4 : callW p n "rom_basis_decls_a" [k] m with _ | ⟨r4, m4⟩
  · rw [liftE_none, checkBasisDeclE.k_rom_basis_decls_a.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, checkBasisDeclE.k_rom_basis_decls_a.arm1]
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
  exact RefE.bind_right hrun4 ((ibds_ref hB dn n hS4 hD4).mono
    fun _ _ _ hR5 => ⟨hR5.stage, hg4.trans hR5.grow⟩)

/-- **`check_basis_decl(vis, kind)` refines `checkBasisDecl`, both outcomes** (through the ROM
stubs): the quotient block without the pinned `Eq` basis declines, then the install. -/
theorem cbd_ref {p : Prog} (hB : BasisProg p) (hC : CanonProg p) (hR : L.Rom.RomRefs p)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {a : AState}
    (n : Nat) {m : Mem} {k : Word} (hk : k.toNat < 5) (hS : StageR dn vis fe m a)
    (hQ : k = 4 → ConRon.Bridge.StateOK a ∧ L.Rom.NamesDn dn a L.Rom.quotNames) :
    RefE True (checkBasisDeclE p n m vis k) (checkBasisDecl fe (basisOfW k.toNat)) a
      (fun v fe' a' => IbdPost dn m v.1 v.2 fe' a') := by
  cases n with
  | zero => rw [checkBasisDeclE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  by_cases h4 : k = 4
  · rw [checkBasisDeclE.arm1 p n m vis k h4]
    subst h4
    obtain ⟨hok0, hN0⟩ := hQ rfl
    simp only [checkBasisDecl, basisOfW, show (4 : Word).toNat = 4 from rfl,
      show (ConLeche.BasisKind.quotK == ConLeche.BasisKind.quotK) = true from rfl, ite_true]
    -- the `Eq` pin
    rcases h1 : pinAtW m 0 with _ | ⟨r1, m1⟩
    · rw [liftE_none, checkBasisDeclE.k_pin_at.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, checkBasisDeclE.k_pin_at.arm1]
    obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.1.pins
    subst hm1
    have hpe : pinEq.run a = .ok (decI (pinW m1 (1 + (0 : Word).toNat)), a) := by
      simpa [pinEq, PIN_EQ] using hrun1
    refine RefE.bind_right hpe ?_
    rw [hr1]
    simp only [List.headD_cons]
    -- `eqA`
    rcases h2 : callW p n "rom_ci" [0] m1 with _ | ⟨r2, m2⟩
    · rw [liftE_none, checkBasisDeclE.k_rom_ci.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, checkBasisDeclE.k_rom_ci.arm1]
    obtain ⟨ea, a2, hrun2, hS2, hg2, hea⟩ := hR.ci dn vis fe 0 (by decide) n m1 a r2 m2 hS h2
    have hrun2' : eqA.run a = .ok (ea, a2) := hrun2
    refine RefE.bind_right hrun2' ?_
    -- `find_is`
    rcases h3 : callW p n "find_is" [vis, pinW m1 (1 + (0 : Word).toNat), r2.headD 0] m2 with
      _ | ⟨r3, m3⟩
    · rw [liftE_none, checkBasisDeclE.k_find_is.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨s3, hs3, -, hok3, hS3, hg3, hb3, -⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (findIs_spec p hC dn vis fe hdn _ _ ea n ⟨m2, Locals.init []⟩ a2
        ⟨hS2, hl1, decRCI_get hea⟩) h3
    subst hs3
    have hrun3 := AM.run_of_ok _ _ hok3
    simp only [AM.st_pure, AM.res_pure] at hS3 hb3
    by_cases h0 : r3.headD 0 = 0
    · rw [checkBasisDeclE.k_find_is.abort1 p _ _ _ _ _ h0]
      have hfind : (fe.find? (decI (pinW m1 (1 + (0 : Word).toNat))) == some ea) = false := by
        rw [← hb3]; simpa using h0
      simp only [hfind, Bool.false_eq_true, ite_false]
      exact RefE.bind_left fun _ => ErrClaim.fail _ _ rfl
    rw [checkBasisDeclE.k_find_is.arm1 p _ _ _ _ _ h0]
    have hfind : (fe.find? (decI (pinW m1 (1 + (0 : Word).toNat))) == some ea) = true := by
      rw [← hb3]; simpa using h0
    simp only [hfind, ite_true]
    have st2 := (ConRon.Bridge.internCI_fresh hok0 hrun2').1
    exact (cbdJ_ref (k := 4) hB hR (by decide) hS3
      (fun _ => ⟨st2.ok, L.Rom.NamesDn.ext hN0 st2.ext⟩)).mono
      fun _ _ _ hR' => ⟨hR'.stage, hg2.trans (hg3.trans hR'.grow)⟩
  · rw [checkBasisDeclE.arm2 p n m vis k h4]
    have hq : (basisOfW k.toNat == ConLeche.BasisKind.quotK) = false := by
      have : k.toNat ≠ 4 := fun e => h4 (UInt64.toNat_inj.mp (by simpa using e))
      unfold basisOfW
      split <;> simp_all <;> omega
    simp only [checkBasisDecl, hq, Bool.false_eq_true, ite_false]
    exact cbdJ_ref hB hR hk hS (fun e => absurd (UInt64.toNat_inj.mp (by rw [e]; rfl)) h4)

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
  refine triple_post (RefE.triple (checkBasisDecl_specE p hB hpa hp n s₀ vis k)
    (cbd_ref hB hC hR hdn n hk hS hQ)) ?_
  rintro r s' ⟨hl, fe', a', hrun, hR'⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact hR'.stage, hR'.grow⟩

end L.Arena
