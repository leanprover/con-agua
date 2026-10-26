import ConAgua.Verdict.DeclArmsE

/-!
# The verdict claim of `check_decl` (lane `verdicts-b`, helper `d`)
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt DeclAtF IndDeclAt CVAt dw decCIs)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

l_model checkDecl_specE (p : Prog) (hf : p.lookup "check_decl" = some checkDeclL)
  fns [hf ↦ checkDeclE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors


section cd
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)
  (p : Prog)

/-- **`check_ind_decl`'s error claim** (the inductive arm's contract, error half of
`IndArmSpec`; a hypothesis here): a failing run claims the twin's `checkDecl` failure. -/
def IndArmSpecE (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (pins : List INatOpPinSet) (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (env : ConLeche.Env) (block : List IConstantInfo) (nP : Nat) (o l w : Word),
    l.toNat = block.length → w.toNat = nP →
    decCIs (erecP m) dn o.toNat l.toNat = some block → o.toNat + l.toNat ≤ erTop m →
    FrontBlock block → StageT dn vis fe m a → ConRon.Bridge.StateOK a → FoldOK V env fe a →
    (∃ x, Frontend.denoteDecl a.store (.indDecl block nP) = some x) → BlockLpsDnA dn block →
    IndMemos m → ∀ e, callE p n "check_ind_decl" [vis, o, l, w] m = .error e →
    ErrClaim (checkDecl V pins fe (.indDecl block nP)) a e

/-- The arms' error claims, for every record of the kind. -/
structure ArmsE (p : Prog) : Prop where
  axiom_ : ∀ cv, ArmSpecE pins dn ds p "check_decl_axiom" (.axiomDecl cv)
  defn : ∀ cv v hh, ArmSpecE pins dn ds p "check_decl_defn" (.defnDecl cv v hh)
  thm : ∀ cv v, ArmSpecE pins dn ds p "check_decl_thm" (.thmDecl cv v)
  opaque_ : ∀ cv v, ArmSpecE pins dn ds p "check_decl_opaque" (.opaqueDecl cv v)
  quot : ∀ k cv, ArmSpecE pins dn ds p "check_decl_quot" (.quotDecl k cv)

/-- **What `check_decl` claims on failure under `StageT`** (the error half of `CheckDeclSpecT`). -/
def CheckDeclSpecE : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ConRon.Bridge.StateOK a →
    LoopR pins dn m a vis fe pend ds → StageT dn vis fe m a →
    (∃ env, FoldOK V env fe a) → (∃ x, Frontend.denoteDecl a.store (dsAt ds i) = some x) →
    (∃ pinsP, PinsDenote a.store pins pinsP) → IndMemos m →
    ∀ e, callE p n "check_decl" [i, vis] m = .error e →
    ErrClaim (checkDecl V pins fe (dsAt ds i)) a e

/-- **`check_decl` fails only where `checkDecl` does** under `StageT`, for the front's record
kinds: each arm by its error claim, the inductive branch by `IndArmSpecE`. -/
theorem checkDecl_errT {p : Prog} (hcd : p.lookup "check_decl" = some checkDeclL) (hib : IbeProg p)
    (hnv : closedNV p L.Checker.nvFns = true)
    (harms : ArmsE pins dn ds p) (hia : IndArmSpecE p dn)
    (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) :
    CheckDeclSpecE pins dn ds p := by
  intro n hn m a vis fe pend i hi hok hR hS hF hden hPD hIM e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDecl_specE p hcd n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hdecl := hR.decls.recs i.toNat hi
  have hds : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hd : ds[i.toNat]? = some ds[i.toNat] := Array.getElem?_eq_getElem hi
  rw [hds] at hden ⊢
  have h1 := hR.decls.room
  have h2 := hR.decls.dsize
  have hw0 : rdW (m.arr64 DECL) (1 + 8 * i) = dw (m.arr64 DECL) i.toNat 0 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  cases n with
  | zero => rw [checkDeclE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  simp only [checkDeclE, hw0] at hW
  generalize hdi : ds[i.toNat] = d at hdecl hd hden
  have kerr : ∀ {x : Except Err (List Word × Mem)},
      checkDeclE.k_check_ind_decl p x = .error e → x = .error e := by
    intro x h
    cases x with
    | error e1 => rw [checkDeclE.k_check_ind_decl.none] at h; cases h; rfl
    | ok q =>
      obtain ⟨r, m1⟩ := q
      rw [checkDeclE.k_check_ind_decl.arm1] at h; cases h
  cases d with
  | axiomDecl cv =>
    rw [hdecl.1] at hW
    simp only [show (1 : Word) ≠ 6 by decide, if_false, if_true] at hW
    exact harms.axiom_ cv n hn' m a vis fe pend i hi hd hok hR hS hF hden hPD hIM.cr e (kerr hW)
  | defnDecl cv v hh =>
    rw [hdecl.1] at hW
    simp only [show (2 : Word) ≠ 6 by decide, show (2 : Word) ≠ 1 by decide, if_false,
      if_true] at hW
    exact harms.defn cv v hh n hn' m a vis fe pend i hi hd hok hR hS hF hden hPD hIM.cr e (kerr hW)
  | thmDecl cv v =>
    rw [hdecl.1] at hW
    simp only [show (3 : Word) ≠ 6 by decide, show (3 : Word) ≠ 1 by decide,
      show (3 : Word) ≠ 2 by decide, if_false, if_true] at hW
    exact harms.thm cv v n hn' m a vis fe pend i hi hd hok hR hS hF hden hPD hIM.cr e (kerr hW)
  | opaqueDecl cv v =>
    rw [hdecl.1] at hW
    simp only [show (4 : Word) ≠ 6 by decide, show (4 : Word) ≠ 1 by decide,
      show (4 : Word) ≠ 2 by decide, show (4 : Word) ≠ 3 by decide, if_false, if_true] at hW
    exact harms.opaque_ cv v n hn' m a vis fe pend i hi hd hok hR hS hF hden hPD hIM.cr e (kerr hW)
  | quotDecl k cv =>
    rw [hdecl.1] at hW
    simp only [show (5 : Word) ≠ 6 by decide, show (5 : Word) ≠ 1 by decide,
      show (5 : Word) ≠ 2 by decide, show (5 : Word) ≠ 3 by decide, show (5 : Word) ≠ 4 by decide,
      if_false, if_true] at hW
    exact harms.quot k cv n hn' m a vis fe pend i hi hd hok hR hS hF hden hPD hIM.cr e (kerr hW)
  | indDecl b nP =>
    rw [hdecl.1] at hW
    simp only [if_true] at hW
    have hdecl' : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat b nP := by
      have := hR.decls.recs i.toNat hi
      rw [hdi] at this; exact this
    have hFB := hFD _ hi _ _ hdi
    have hlpd := hLD _ hi _ _ hdi
    have hD : (m.arr64 DECL).size < 2 ^ 63 := hR.decls.dsize
    have hP : (m.arr64 DLP).size < 2 ^ 63 := hR.decls.psize
    cases h1 : callE p n "ind_block_to_erec" [i] m with
    | error e1 =>
      rw [h1, checkDeclE.k_ind_block_to_erec.none] at hW; cases hW
      exact nvl hnv (by decide +kernel) h1
    | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, checkDeclE.k_ind_block_to_erec.eq_2] at hW
    obtain ⟨s1, hs1, -, n', hW1⟩ := triple_of_callE
      (indBlockToErec_specW p hib.erec_alloc hib.dind_copy hib.ind_rec_copy hib.ind_copy_go
        hib.ind_block_to_erec n ⟨m, Locals.init []⟩ i) h1
    subst hs1
    obtain ⟨hS1, hg1, hf1, -, hl1, hdec1, htop1⟩ := ibeW_ok hW1 hS.stage hdecl' hFB hD hP
    have hT1 : StageT dn vis fe s1.mem a :=
      ⟨hS1, hS.twin.frame hf1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        by rw [pinW_frame hf1 (by decide)]; exact hS.flag⟩
    have hIM1 : IndMemos s1.mem :=
      hIM.frame hf1 (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide)
    have hw : (rdW (s1.mem.arr64 DECL) (5 + 8 * i)).toNat = nP := by
      rw [hf1.1 DECL (by decide) (by decide)]
      have h0 : dw (m.arr64 DECL) i.toNat 0 ≠ 0 := by rw [hdecl'.1]; decide
      rw [rdW_dwI hD h0 rfl (by decide)]
      exact hdecl'.2.1
    obtain ⟨env, hFo⟩ := hF
    exact hia pins n hn' s1.mem a vis fe env b nP _ _ _ hl1 hw hdec1 htop1 hFB hT1 hok hFo hden
      hlpd hIM1 e (kerr hW)
  | basisDecl _ => exact hdecl.elim

end cd

end L.Arena
