import ConAgua.Arena.InstLPWalkBase

/-!
# The `instLP` walk: the expression-interning steps and the memo write under `CoreS`

Each interning callee of the arms (`mk_app`, `mk_lam`, `mk_forall`, `mk_let`, `mk_proj`,
`intern_fvar`, `intern_sort`, `intern_const`), called through `callW`, refines the twin's
`internE` of the node and keeps the walk's invariants (`ILWStep`); the arms' memo write
(`find; put` of `instLPC`) is `instLPSet`.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- **What a step of the walk gives**: the twin's run of `T` from `a` succeeds with the result word's
handle, the relation holds after it (`CoreAfter`), with the walk memos and the twin's level stores
grown. -/
def ILWStep (T : AM EIdx) (a : AState) (dn : NIdx → Option ConLeche.Name) (m m' : Mem) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) (r : Word) : Prop :=
  ∃ a', T.run a = .ok (decE r, a') ∧ CoreAfter dn m m' a' vis fe M eb ∧ ILWMemo m' a' ∧ ILWGrow a a' ∧ HW r

/-- The program's interning callees. -/
structure ILWMkProg (p : Prog) : Prop where
  spine : SpineProg p
  lamf : p.lookup "lam_find" = some lamFind
  lamp : p.lookup "lam_push" = some lamPush
  lami : p.lookup "intern_lam" = some internLamL
  mklam : p.lookup "mk_lam" = some mkLam
  faf : p.lookup "forall_find" = some forallFind
  fap : p.lookup "forall_push" = some forallPush
  fai : p.lookup "intern_forall" = some internForallL
  mkfa : p.lookup "mk_forall" = some mkForall
  lef : p.lookup "letE_find" = some letFind
  lep : p.lookup "letE_push" = some letPush
  lei : p.lookup "intern_letE" = some internLet
  mklet : p.lookup "mk_let" = some mkLet
  pjf : p.lookup "proj_find" = some projFind
  pjp : p.lookup "proj_push" = some projPush
  pji : p.lookup "intern_proj" = some internProj
  mkpj : p.lookup "mk_proj" = some mkProj
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  fvi : p.lookup "intern_fvar" = some internFVar
  sof : p.lookup "sort_find" = some sortFind
  sop : p.lookup "sort_push" = some sortPush
  soi : p.lookup "intern_sort" = some internSort
  cof : p.lookup "const_find" = some constFind
  cop : p.lookup "const_push" = some constPush
  coi : p.lookup "intern_const" = some internConst

section steps
variable {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
  {M : ModeMaps} {eb : Word}

/-- **An expression interning that creates no `sort`/`const` view**, as a walk step. -/
theorem ilw_internE {v : ENodeView} {A : List ArrId} {C : List Word} (r : Word)
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hok : AM.ok (internE v) a) (hD : ArenaD m' (AM.st (internE v) a))
    (hres : AM.res (internE v) a = decE r) (hr : HW r) (hf : MemFrame A C m m')
    (h128 : ∀ b ∈ A, b < 96 ∨ 128 ≤ b := by decide) (hpins : (128 : ArrId) ∉ A := by decide)
    (henv : ∀ b ∈ A, b < 129 ∨ (144 ≤ b ∧ (b < 385 ∨ 388 ≤ b)) := by decide)
    (hC128 : ∀ x ∈ C, x.toNat < 96 ∨ 128 ≤ x.toNat := by simp)
    (hCenv : ∀ x ∈ C, x.toNat < 128 ∨ 136 ≤ x.toNat := by simp)
    (hmA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A := by decide) (hmC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C := by decide)
    (hmWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A := by decide)
    (hmWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C := by decide)
    (hscA : SOREC ∉ A ∧ CREC ∉ A ∧ tier1 SOREC ∉ A ∧ tier1 CREC ∉ A := by decide)
    (hscC : (1 : Word) ∉ C ∧ (16 : Word) ∉ C ∧ (17 : Word) ∉ C ∧ (18 : Word) ∉ C ∧ (19 : Word) ∉ C :=
      by decide)
    (hLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A := by decide)
    (hLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C := by decide)
    (hSA : SPN ∉ A ∧ BSTK ∉ A ∧ POOL ∉ A := by decide)
    (hSC : (136 : Word) ∉ C ∧ (137 : Word) ∉ C ∧ (0 : Word) ∉ C := by decide)
    (hL : LvlFree C := by lvl_free) (hP1 : POOL1 ∉ A := by decide) (hPT : PT0 ∉ A := by decide) :
    ILWStep (internE v) a dn m m' vis fe M eb r := by
  have hrun := AM.run_of_ok _ _ hok
  have hk := Keeps.run (keepsW_internE v) hrun
  have hS' := hS.arena_frame hD hk hf h128 hpins henv hC128 hCenv hmA hmC hmWA hmWC hLA hLC hscA hscC hSC.2.2
  obtain ⟨hM', hg⟩ := hM.of_internE hok hf hLA hLC
  refine ⟨_, ?_, ⟨M, hS', KeptAll.refl _ _, StackKept.of_frame hf hSA hSC hL hP1 hPT⟩, hM', hg, hr⟩
  rw [hrun, hres]

variable (p : Prog) (hp : ILWMkProg p) (n : Nat)
include hp

theorem ilw_mkApp (x y : Word) (rs : List Word) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hc : callW p n "mk_app" [x, y] m = some (rs, m')) :
    ILWStep (internE (.app (decE x) (decE y))) a dn m m' vis fe M eb (rs.headD 0) := by
  obtain ⟨hok, hD, hres, hf, hw⟩ := callW_mkApp p hp.spine n ⟨m, Locals.init []⟩ a hS.arena x y rs m' hc
  exact ilw_internE _ hS hM hok hD hres hw hf

theorem ilw_mkLam (x y : Word) (rs : List Word) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hc : callW p n "mk_lam" [x, y] m = some (rs, m')) (hw : HW (rs.headD 0)) :
    ILWStep (internE (.lam (decE x) (decE y))) a dn m m' vis fe M eb (rs.headD 0) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (mkLam_spec p hp.spine.derb hp.lamf hp.lamp hp.lami hp.mklam n
    ⟨m, Locals.init []⟩ x y) hc
  obtain ⟨hok, hD, hres⟩ := mkLam_ok m a hS.arena x y _ _ hm
  exact ilw_internE _ hS hM hok hD hres hw (mkLamW_frameA _ _ _ _ _ hm)

theorem ilw_mkForall (x y : Word) (rs : List Word) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hc : callW p n "mk_forall" [x, y] m = some (rs, m')) (hw : HW (rs.headD 0)) :
    ILWStep (internE (.forallE (decE x) (decE y))) a dn m m' vis fe M eb (rs.headD 0) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (mkForall_spec p hp.spine.derb hp.faf hp.fap hp.fai hp.mkfa n
    ⟨m, Locals.init []⟩ x y) hc
  obtain ⟨hok, hD, hres⟩ := mkForall_ok m a hS.arena x y _ _ hm
  exact ilw_internE _ hS hM hok hD hres hw (mkForallW_frameA _ _ _ _ _ hm)

theorem ilw_mkLet (x y z : Word) (rs : List Word) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hc : callW p n "mk_let" [x, y, z] m = some (rs, m')) (hw : HW (rs.headD 0)) :
    ILWStep (internE (.letE (decE x) (decE y) (decE z))) a dn m m' vis fe M eb (rs.headD 0) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (mkLet_spec p hp.spine.derb hp.lef hp.lep hp.lei hp.mklet n
    ⟨m, Locals.init []⟩ x y z) hc
  obtain ⟨hok, hD, hres⟩ := mkLet_ok m a hS.arena x y z _ _ hm
  exact ilw_internE _ hS hM hok hD hres hw (mkLetW_frameA _ _ _ _ _ _ hm)

theorem ilw_mkProj (nm ix x : Word) (rs : List Word) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hc : callW p n "mk_proj" [nm, ix, x] m = some (rs, m')) (hw : HW (rs.headD 0)) :
    ILWStep (internE (.proj (decI nm) ix.toNat (decE x))) a dn m m' vis fe M eb (rs.headD 0) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (mkProj_spec p hp.spine.derb hp.pjf hp.pjp hp.pji hp.mkpj n
    ⟨m, Locals.init []⟩ nm ix x) hc
  obtain ⟨hok, hD, hres⟩ := mkProj_ok m a hS.arena nm ix x _ _ hm
  exact ilw_internE _ hS hM hok hD hres hw (mkProjW_frameA _ _ _ _ _ _ hm)

theorem ilw_internFVar (ix x : Word) (rs : List Word) (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a)
    (hx : HW x) (hc : callW p n "intern_fvar" [ix, x] m = some (rs, m')) (hw : HW (rs.headD 0)) :
    ILWStep (internE (.fvar ix.toNat (decE x))) a dn m m' vis fe M eb (rs.headD 0) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (internFVar_spec p hp.fvf hp.fvp hp.fvi n
    ⟨m, Locals.init []⟩ ix x) hc
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.arena ix x _ hx _ hm
  exact ilw_internE _ hS hM hok hD hres hw (fvinternW_frame _ _ _ _ _ hm)

end steps

end L.Arena
