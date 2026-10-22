import ConAgua.Arena.DeclArmAxiom
import ConAgua.Arena.DeclArmDefn

/-!
# `check_decl` refines `checkDecl` at the loop's relation (lane `decls3`)

`check_decl(i, vis)` reads the record's kind word and calls one arm (`DeclStep.lean`). Under the
front's records (`DeclsR`: every record is an axiom, definition, theorem, opaque or quotient,
`DeclAt`) the kind is `1`‥`5`, so the inductive branch (kind `6`, lane `induct`'s
`check_ind_decl`) is never taken here; it becomes reachable with the front's inductive records
(lane `indproofs2`).

Each arm's spec at the loop's relation is a theorem, all five proved: the theorem arm
(`DeclArmLoop.lean`), the opaque arm (`DeclArmOpaque.lean`), and through specs that are fields of
`CheckDeclProg` (to be discharged by the callees' proofs): the quotient arm (`CvCanonSpec`), the
axiom arm (`CiCanonSpec`), the definition arm (`DefnProg`: the two gates' specs, `NatGateSpec`,
`DivGateSpec`). The callees' own stub specs (the ROM readers, `lvl_eq_c`) are `sorry`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsR DeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `check_decl`'s proof takes. -/
structure CheckDeclProg (p : Prog) : Prop where
  cd : p.lookup "check_decl" = some checkDeclL
  ax : p.lookup "check_decl_axiom" = some checkDeclAxiom
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  th : p.lookup "check_decl_thm" = some checkDeclThm
  op : p.lookup "check_decl_opaque" = some checkDeclOpaque
  qu : p.lookup "check_decl_quot" = some checkDeclQuot
  arm : ArmProg p
  val : ValProg p
  crp : CrpProg p
  quot : QuotProg p
  axp : AxProg p
  /-- The definition arm's two gates (`DeclArmDefn.lean`), at every variant list. -/
  defn : ∀ pins, DefnProg p pins

/-! ## The arms not proved yet -/

section pending
variable {p : Prog} (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration)

/-- The shape of an arm's spec at the loop's relation, for the record `d` at `i`. -/
def ArmSpec (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d → LoopR pins dn s₀.mem a₀ vis fe pend ds →
  ⦃fun s => s = s₀⦄ invoke p (exec p n) f [i, vis]
  ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkDecl V pins fe d) a₀ ∧
    LoopR pins dn s'.mem (AM.st (checkDecl V pins fe d) a₀) (r.headD 0)
      (AM.res (checkDecl V pins fe d) a₀) pend ds; ⊤⦄

/-- `check_decl_axiom` (`DeclArmAxiom.lean`; through `CiCanonSpec`, a field of `AxProg`). -/
theorem checkDeclAxiom_loop (hP : CheckDeclProg p) (hdn : DnInj dn) (cv : IConstantVal) :
    ArmSpec pins dn ds p "check_decl_axiom" (.axiomDecl cv) :=
  fun n s₀ a₀ vis fe pend i hi hd hR =>
    checkDeclAxiom_loop' hP.arm hP.axp pins dn hdn ds n s₀ a₀ vis fe pend i cv hi hd hR

/-- `check_decl_defn` (`DeclArmDefn.lean`; through the gates' specs, `DefnProg`, a field of
`CheckDeclProg`). -/
theorem checkDeclDefn_loop (hP : CheckDeclProg p) (cv : IConstantVal) (v : EIdx)
    (h : ConLeche.ReducibilityHint) :
    ArmSpec pins dn ds p "check_decl_defn" (.defnDecl cv v h) :=
  fun n s₀ a₀ vis fe pend i hi hd hR =>
    checkDeclDefn_loop' hP.arm hP.val pins (hP.defn pins) dn ds n s₀ a₀ vis fe pend i cv v h hi hd hR

/-- `check_decl_opaque` (`DeclArmOpaque.lean`). -/
theorem checkDeclOpaque_loop (hP : CheckDeclProg p) (hdn : DnInj dn) (cv : IConstantVal)
    (v : EIdx) : ArmSpec pins dn ds p "check_decl_opaque" (.opaqueDecl cv v) :=
  fun n s₀ a₀ vis fe pend i hi hd hR =>
    checkDeclOpaque_loop' hP.arm hP.val hP.crp hP.op pins dn hdn ds n s₀ a₀ vis fe pend i cv v hi hd hR

/-- `check_decl_quot` (`DeclArmQuot.lean`; through `CvCanonSpec`, a field of `QuotProg`). -/
theorem checkDeclQuot_loop (hP : CheckDeclProg p) (hdn : DnInj dn) (k : ConLeche.QuotKind)
    (cv : IConstantVal) : ArmSpec pins dn ds p "check_decl_quot" (.quotDecl k cv) :=
  fun n s₀ a₀ vis fe pend i hi hd hR =>
    checkDeclQuot_loop' hP.arm hP.val.rcp hP.quot pins dn hdn ds n s₀ a₀ vis fe pend i k cv hi hd hR

end pending

/-! ## The dispatcher -/

section model
variable (p : Prog)

/-- After an arm: its view word. -/
def cdRet : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- The inductive branch (kind `6`). -/
def cdInd (n : Nat) (i vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    cdRet (callW p n "check_ind_decl"
      [vis, r1.headD 0, r1.tail.headD 0, rdW (m1.arr64 DECL) (5 + 8 * i)] m1)

/-- The dispatch on the kind word `k`. -/
def cdSel (n : Nat) (m : Mem) (i vis k : Word) : Option (List Word × Mem) :=
  if k = 6 then cdInd p n i vis (callW p n "ind_block_to_erec" [i] m)
  else if k = 1 then cdRet (callW p n "check_decl_axiom" [i, vis] m)
  else if k = 2 then cdRet (callW p n "check_decl_defn" [i, vis] m)
  else if k = 3 then cdRet (callW p n "check_decl_thm" [i, vis] m)
  else if k = 4 then cdRet (callW p n "check_decl_opaque" [i, vis] m)
  else if k = 5 then cdRet (callW p n "check_decl_quot" [i, vis] m)
  else none

/-- **The model of `check_decl(i, vis)`.** -/
def cdW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, i, vis => cdSel p n m i vis (rdW (m.arr64 DECL) (1 + 8 * i))

section arms
variable (n : Nat) (m m1 : Mem) (i vis k : Word) (r r1 : List Word)
theorem cdW_step : cdW p (n + 1) m i vis = cdSel p n m i vis (rdW (m.arr64 DECL) (1 + 8 * i)) := rfl
theorem cdRet_some : cdRet (some (r, m)) = some ([r.headD 0], m) := rfl
theorem cdInd_some : cdInd p n i vis (some (r1, m1)) =
    cdRet (callW p n "check_ind_decl"
      [vis, r1.headD 0, r1.tail.headD 0, rdW (m1.arr64 DECL) (5 + 8 * i)] m1) := rfl
end arms

grind_pattern [ind_grind] cdW_step => cdW p (n + 1) m i vis
grind_pattern [ind_grind] cdRet_some => cdRet (some (r, m))
grind_pattern [ind_grind] cdInd_some => cdInd p n i vis (some (r1, m1))

theorem cd_specW (hp : p.lookup "check_decl" = some checkDeclL) (n : Nat) (s₀ : St) (i vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_decl" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cdW p n s₀.mem i vis = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDeclL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "ind_block_to_erec", callW_spec p n "check_ind_decl",
        callW_spec p n "check_decl_axiom", callW_spec p n "check_decl_defn",
        callW_spec p n "check_decl_thm", callW_spec p n "check_decl_opaque",
        callW_spec p n "check_decl_quot"] <;>
      finish (gen := 20) [cdSel, rdW_eq]

end model

/-- An arm's run through `callW`, at the loop's relation. -/
theorem arm_callW {p : Prog} {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {f : FnName} {d : IDeclaration} (hA : ArmSpec pins dn ds p f d)
    {n : Nat} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {pend : Array PendingCheck}
    {i : Word} {r : List Word} (hi : i.toNat < ds.size) (hd : ds[i.toNat]? = some d)
    (hR : LoopR pins dn m a vis fe pend ds) (h : cdRet (callW p n f [i, vis] m) = some (r, m')) :
    AM.ok (checkDecl V pins fe d) a ∧
      LoopR pins dn m' (AM.st (checkDecl V pins fe d) a) (r.headD 0) (AM.res (checkDecl V pins fe d) a)
        pend ds := by
  cases h1 : callW p n f [i, vis] m with
  | none => rw [h1] at h; cases h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cdRet_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s', hs', -, hok, hL⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hA n ⟨m, Locals.init []⟩ a vis fe pend i hi hd hR) h1
  subst hs'
  exact ⟨hok, by simpa using hL⟩

/-- **`check_decl` refines `checkDecl`** at the loop's relation, for the front's record kinds
(through the arms' specs: every arm's but the definition arm's is proved). -/
@[refines_part ConRon.Arena.checkDecl "one-constant records (the front's kinds 1-5)"]
theorem checkDecl_loop {p : Prog} (hP : CheckDeclProg p) (pins : List INatOpPinSet)
    (dn : NIdx → Option ConLeche.Name) (hdn : DnInj dn) (ds : Array IDeclaration) :
    CheckDeclSpec V pins dn ds p := by
  intro n s₀ a₀ vis fe pend i hi hR
  refine triple_post (cd_specW p hP.cd n s₀ i vis) ?_
  rintro r s' ⟨hl, h⟩
  refine ⟨hl, ?_⟩
  have hdecl := hR.decls.recs i.toNat hi
  have hds : dsAt ds i = ds[i.toNat] := by simp [dsAt, Array.getD, hi]
  have hd : ds[i.toNat]? = some ds[i.toNat] := Array.getElem?_eq_getElem hi
  rw [hds]
  have h1 := hR.decls.room
  have h2 := hR.decls.dsize
  have hw0 : rdW (s₀.mem.arr64 DECL) (1 + 8 * i) = dw (s₀.mem.arr64 DECL) i.toNat 0 :=
    rdW_dw _ (by omega) (by decide) (by decide)
  cases n with
  | zero => simp [cdW] at h
  | succ n =>
  rw [cdW_step, hw0] at h
  generalize hdi : ds[i.toNat] = d at hdecl hd
  cases d with
  | axiomDecl cv =>
    rw [hdecl.1] at h
    simp only [cdSel, show (1 : Word) ≠ 6 by decide, if_false, if_true] at h
    exact arm_callW (checkDeclAxiom_loop pins dn ds hP hdn cv) hi hd hR h
  | defnDecl cv v hh =>
    rw [hdecl.1] at h
    simp only [cdSel, show (2 : Word) ≠ 6 by decide, show (2 : Word) ≠ 1 by decide, if_false,
      if_true] at h
    exact arm_callW (checkDeclDefn_loop pins dn ds hP cv v hh) hi hd hR h
  | thmDecl cv v =>
    rw [hdecl.1] at h
    simp only [cdSel, show (3 : Word) ≠ 6 by decide, show (3 : Word) ≠ 1 by decide,
      show (3 : Word) ≠ 2 by decide, if_false, if_true] at h
    exact arm_callW (fun n s₀ a₀ vis fe pend i hi hd hR =>
      checkDeclThm_loop hP.arm hP.val hP.th pins dn ds n s₀ a₀ vis fe pend i cv v hi hd hR) hi hd hR h
  | opaqueDecl cv v =>
    rw [hdecl.1] at h
    simp only [cdSel, show (4 : Word) ≠ 6 by decide, show (4 : Word) ≠ 1 by decide,
      show (4 : Word) ≠ 2 by decide, show (4 : Word) ≠ 3 by decide, if_false, if_true] at h
    exact arm_callW (checkDeclOpaque_loop pins dn ds hP hdn cv v) hi hd hR h
  | quotDecl k cv =>
    rw [hdecl.1] at h
    simp only [cdSel, show (5 : Word) ≠ 6 by decide, show (5 : Word) ≠ 1 by decide,
      show (5 : Word) ≠ 2 by decide, show (5 : Word) ≠ 3 by decide, show (5 : Word) ≠ 4 by decide,
      if_false, if_true] at h
    exact arm_callW (checkDeclQuot_loop pins dn ds hP hdn k cv) hi hd hR h
  | indDecl _ _ => exact hdecl.elim
  | basisDecl _ => exact hdecl.elim

end L.Arena
