import ConAgua.Verdict.DeclHdrE
import ConAgua.Arena.Checker

/-!
# The verdict claims of `install_basis_decl`, `install_basis_decls`, `check_basis_decl`
(lane `verdicts-b`, helper `d`)

A duplicate declaration rejects (`installBasisDecl`'s `fail (.invalid …)`), the quotient block
without the pinned `Eq` basis declines; `env_push`, the ROM readers and `find_is` claim nothing.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

l_model installBasisDecl_specE (p : Prog)
  (hf : p.lookup "install_basis_decl" = some installBasisDeclL)
  fns [hf ↦ installBasisDeclE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model installBasisDecls_specE (p : Prog)
  (hf : p.lookup "install_basis_decls" = some installBasisDeclsL)
  fns [hf ↦ installBasisDeclsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model checkBasisDecl_specE (p : Prog)
  (hf : p.lookup "check_basis_decl" = some checkBasisDeclL)
  fns [hf ↦ checkBasisDeclE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

/-- **`install_basis_decl`'s error claim** (a duplicate declaration rejects). -/
theorem ibdE_okT {p : Prog} (hB : BasisProg p) (hnv : closedNV p L.Checker.nvFns = true)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m : Mem} {c : Word} {ci : IConstantInfo} {e : Err}
    (hS : StageR dn vis fe m a) (hci : decCI (erecP m) dn c.toNat = some ci)
    (hc : callE p n "install_basis_decl" [vis, c] m = .error e) :
    ErrClaim (installBasisDecl fe ci) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (installBasisDecl_specE p hB.ibd n ⟨m, Locals.init []⟩ vis c) hc
    (Err.code_ne_of_cls hk0)
  obtain ⟨w, hw1, hwl, hname⟩ := decCI_name hci
  have hcb : c.toNat + 1 < 2 ^ 64 := erecP_bound hw1 hS.2
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 hcb
  have ew : rdW (m.arr64 EREC) (c + 1) = w := rdW_of_get? hc1.symm (erecP_get hw1)
  cases n with
  | zero => rw [installBasisDeclE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  rw [installBasisDeclE.arm1, ew] at hW
  cases h1 : callE p n "env_find" [w, vis] m with
  | error e1 =>
    rw [h1, installBasisDeclE.k_env_find.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE
    (envFind_specW p hB.ih.ix hB.ih.rowGet hB.ih.find n ⟨m, Locals.init []⟩ w vis) h1
  subst hs1
  by_cases hb : r1.headD 0 ≠ 0
  · rw [installBasisDeclE.k_env_find.abort1 p _ _ _ _ _ hb] at hW; cases hW
    have : (fe.find? ci.name).isSome = true := by
      rw [hname]; exact envFindW_hitSome hW1 hS.1.env hwl hb
    simp only [installBasisDecl, fail_bindAM]
    refine ErrClaim.ite_neg (by simp [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] at this ⊢; exact this) ?_
    exact ErrClaim.fail _ _ rfl
  rw [installBasisDeclE.k_env_find.arm1 p _ _ _ _ _ (by simpa using hb)] at hW
  cases h2 : callE p n "env_push" [vis, c] s1.mem with
  | error e2 =>
    rw [h2, installBasisDeclE.k_env_push.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h2
  | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, installBasisDeclE.k_env_push.arm1] at hW; cases hW

/-- **`install_basis_decls`' error claim**, on the model, by induction on the fuel (the recursion
is the model's). -/
theorem ibdsE_rel {p : Prog} (hB : BasisProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) :
    ∀ (n : Nat) (m : Mem) (vis : Word) (fe : IFEnv) (a : AState) (o l : Word)
      (cis : List IConstantInfo) (e : Err),
      installBasisDeclsE p n m vis o l = .error e → StageR dn vis fe m a →
      DecB (basisDec dn o.toNat l.toNat) m cis → ErrClaim (installBasisDecls fe cis) a e := by
  intro n
  induction n with
  | zero =>
    intro m vis fe a o l cis e h _ _
    rw [installBasisDeclsE.eq_1] at h; cases h
    exact fun hk => absurd rfl hk
  | succ n ih =>
  intro m vis fe a o l cis e h hS hD
  by_cases hl : l = 0
  · rw [installBasisDeclsE.arm1 p n m vis o l hl] at h; cases h
  rw [installBasisDeclsE.arm2 p n m vis o l hl] at h
  obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by
    have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hD' : basisDec dn o.toNat (k + 1) (truncM m) = some cis := by rw [← hk]; exact hD
  cases cis with
  | nil => have := decPL_length (truncM m) hD'; simp at this
  | cons ci cs =>
  obtain ⟨v, hv, hci⟩ := decPL_head hD'
  have hext := (IWGrow.refl m).truncExt
  have hvm : iwN m o.toNat = some v := hext.1.nat? hv
  have hci' : decCI (erecP m) dn v = some ci := ArrExt.decCI (truncM_erecP m) hci
  obtain ⟨w0, hw0, rfl⟩ : ∃ w0, (iwA m)[o.toNat]? = some w0 ∧ w0.toNat = v := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
  have ew : rdW (m.arr64 IW) o = w0 := by simp [rdW, iwA] at hw0 ⊢; simp [hw0]
  rw [ew] at h
  cases h1 : callE p n "install_basis_decl" [vis, w0] m with
  | error e1 =>
    rw [h1, installBasisDeclsE.k_install_basis_decl.none] at h; cases h
    exact ErrClaim.bind_left (ibdE_okT hB hnv hS hci' h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, installBasisDeclsE.k_install_basis_decl.arm1] at h
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (ibd_specW p hB n ⟨m, Locals.init []⟩ vis w0)
    (h1)
  subst hs1
  obtain ⟨hrun1, hS1, hg1⟩ := ibdW_ok hB.rcp hW1 hS hci'
  have hob : o.toNat + 1 < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hw0).1
    have := hS.2.2.2.1; simp only [iwA] at *; omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_add_small o 1 hob
  have hl1 : (l - 1).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hDt : DecB (basisDec dn (o + 1).toNat (l - 1).toNat) m cs := by
    rw [ho1, hl1]; exact decPL_tail hD'
  have := ih s1.mem (r1.headD 0) (fe.push ci) a (o + 1) (l - 1) cs e h hS1
    (DecB.grow (basisDec_mono dn _ _) hg1 hDt)
  simp only [installBasisDecls]
  exact ErrClaim.bind_right hrun1 this

/-- **The block's read and install, error half of `cbdK4_ok`.** -/
theorem cbdK4E {p : Prog} (hB : BasisProg p) (hR : L.Rom.RomRefs p)
    (hnv : closedNV p L.Checker.nvFns = true)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m : Mem}
    {k : Word} {e : Err} (hk : k.toNat < 5) (hS : StageR dn vis fe m a)
    (hQ : k.toNat = 4 → ConRon.Bridge.StateOK a ∧ L.Rom.NamesDn dn a L.Rom.quotNames)
    (h : checkBasisDeclE.k_rom_basis_decls_a p n vis (callE p n "rom_basis_decls_a" [k] m) = .error e) :
    ErrClaim (do installBasisDecls fe (← BasisKind.declsA (basisOfW k.toNat)) : AM IFEnv) a e := by
  cases h4 : callE p n "rom_basis_decls_a" [k] m with
  | error e4 =>
    rw [h4, checkBasisDeclE.k_rom_basis_decls_a.none] at h; cases h
    exact nvl hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, checkBasisDeclE.k_rom_basis_decls_a.arm1] at h
  have h4w := callW_of_callE h4
  obtain ⟨cis, a4, hrun4, hS4, hg4, hD4, -⟩ :
      ∃ cis a4, (BasisKind.declsA (basisOfW k.toNat)).run a = .ok (cis, a4) ∧
        KeepPost dn vis fe (decRBlk dn) m m4 a4 r4 cis := by
    by_cases h4' : k.toNat < 4
    · exact hR.basisA dn vis fe k h4' n m a r4 m4 hS h4w
    · have hk4 : k.toNat = 4 := by omega
      have : k = 4 := UInt64.toNat_inj.mp (by rw [hk4]; rfl)
      subst this
      obtain ⟨hok, hN⟩ := hQ hk4
      exact hR.quotA dn vis fe n m a r4 m4 ⟨hS, hok, hN⟩ h4w
  refine ErrClaim.bind_right hrun4 ?_
  cases h5 : callE p n "install_basis_decls" [vis, r4.headD 0, r4.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, checkBasisDeclE.k_install_basis_decls.none] at h; cases h
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have hW := triple_of_callE_err
      (installBasisDecls_specE p hB.ibds n ⟨m4, Locals.init []⟩ vis (r4.headD 0) (r4.tail.headD 0))
      h5 (Err.code_ne_of_cls hk0)
    exact ibdsE_rel hB hnv dn n m4 vis fe a4 _ _ cis e hW hS4 hD4
  | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, checkBasisDeclE.k_install_basis_decls.arm1] at h; cases h

/-- **`check_basis_decl`'s error claim**: the quotient block without the pinned `Eq` basis
declines; the install by `ibdsE_rel`. -/
theorem cbdE_okT {p : Prog} (hB : BasisProg p) (hC : CanonProg p) (hR : L.Rom.RomRefs p)
    (hnv : closedNV p L.Checker.nvFns = true) (hpa : p.lookup "pin_at" = some pinAtL)
    (hp : p.lookup "check_basis_decl" = some checkBasisDeclL)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m : Mem} {k : Word} {e : Err} (hk : k.toNat < 5) (hS : StageR dn vis fe m a)
    (hQ : k = 4 → ConRon.Bridge.StateOK a ∧ L.Rom.NamesDn dn a L.Rom.quotNames)
    (hc : callE p n "check_basis_decl" [vis, k] m = .error e) :
    ErrClaim (checkBasisDecl fe (basisOfW k.toNat)) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkBasisDecl_specE p hp n ⟨m, Locals.init []⟩ vis k) hc
    (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [checkBasisDeclE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  by_cases h4 : k = 4
  · rw [checkBasisDeclE.arm1 p n m vis k h4] at hW
    subst h4
    obtain ⟨hok0, hN0⟩ := hQ rfl
    simp only [checkBasisDecl, basisOfW, show (4 : Word).toNat = 4 from rfl,
      show (ConLeche.BasisKind.quotK == ConLeche.BasisKind.quotK) = true from rfl, ite_true]
    cases h1 : callE p n "pin_at" [0] m with
    | error e1 =>
      rw [h1, checkBasisDeclE.k_pin_at.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h1
    | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, checkBasisDeclE.k_pin_at.arm1] at hW
    obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (pinAt_specW p hpa n ⟨m, Locals.init []⟩ 0) h1
    obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok hW1 hS.1.pins
    have hm1' : m1 = m := hs1.symm.trans hm1
    subst hm1'
    have hpe : pinEq.run a = .ok (decI (pinW m1 (1 + (0 : Word).toNat)), a) := by
      simpa [pinEq, PIN_EQ] using hrun1
    refine ErrClaim.bind_right hpe ?_
    rw [hr1] at hW
    simp only [List.headD_cons] at hW
    -- `eqA`
    cases h2 : callE p n "rom_ci" [0] m1 with
    | error e2 =>
      rw [h2, checkBasisDeclE.k_rom_ci.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h2
    | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, checkBasisDeclE.k_rom_ci.arm1] at hW
    obtain ⟨ea, a2, hrun2, hS2, hg2, hea⟩ := hR.ci dn vis fe 0 (by decide) n m1 a r2 m2 hS
      (callW_of_callE h2)
    have hrun2' : eqA.run a = .ok (ea, a2) := hrun2
    refine ErrClaim.bind_right hrun2' ?_
    -- `find_is`
    cases h3 : callE p n "find_is" [vis, pinW m1 (1 + (0 : Word).toNat), r2.headD 0] m2 with
    | error e3 =>
      rw [h3, checkBasisDeclE.k_find_is.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h3
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3] at hW
    obtain ⟨s3, hs3, -, hok3, hS3, hg3, hb3, -⟩ := triple_of_callE
      (findIs_spec p hC dn vis fe hdn _ _ ea n ⟨m2, Locals.init []⟩ a2
        ⟨hS2, hl1, decRCI_get hea⟩) h3
    subst hs3
    have hrun3 := AM.run_of_ok _ _ hok3
    simp only [AM.st_pure, AM.res_pure] at hS3 hb3
    by_cases h0 : r3.headD 0 = 0
    · rw [checkBasisDeclE.k_find_is.abort1 p _ _ _ _ _ h0] at hW; cases hW
      have hfind : (fe.find? (decI (pinW m1 (1 + (0 : Word).toNat))) == some ea) = false := by
        rw [← hb3]; simpa using h0
      simp only [hfind, Bool.false_eq_true, ite_false]
      exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
    rw [checkBasisDeclE.k_find_is.arm1 p _ _ _ _ _ h0, checkBasisDeclE.j1.arm1] at hW
    have hfind : (fe.find? (decI (pinW m1 (1 + (0 : Word).toNat))) == some ea) = true := by
      rw [← hb3]; simpa using h0
    simp only [hfind, ite_true]
    have st2 := (ConRon.Bridge.internCI_fresh hok0 hrun2').1
    exact cbdK4E hB hR hnv (by decide) hS3
      (fun _ => ⟨st2.ok, L.Rom.NamesDn.ext hN0 st2.ext⟩) hW
  · rw [checkBasisDeclE.arm2 p n m vis k h4, checkBasisDeclE.j1.arm1] at hW
    have hq : (basisOfW k.toNat == ConLeche.BasisKind.quotK) = false := by
      have : k.toNat ≠ 4 := fun e => h4 (UInt64.toNat_inj.mp (by simpa using e))
      unfold basisOfW
      split <;> simp_all <;> omega
    simp only [checkBasisDecl, hq, Bool.false_eq_true, ite_false]
    exact cbdK4E hB hR hnv hk hS (fun e => absurd (UInt64.toNat_inj.mp (by rw [e]; rfl)) h4) hW

end L.Arena
