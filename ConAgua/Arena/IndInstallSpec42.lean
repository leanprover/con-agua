import ConAgua.Arena.IndInstallSpec37
import ConAgua.Arena.IndRealIpo
import ConAgua.Arena.IndPartsSpec15
import ConAgua.Arena.DeclBasisSpec2
import ConAgua.Arena.IndRealBph2
import ConAgua.Census.Attr

/-!
# `check_ind_decl(vis, boff, blen, nP)`: the inductive arm at `StageR` (lane `indproofs4`)

`checkIndDecl` (`IndParts.lean`) is the `.indDecl block nP` arm of `checkDecl`. It runs
`basis_pin_hit`, then `check_basis_decl`, `ind_params_ok`, `block_parts`, and either `check_block`
or `check_shapeless` (which never returns). Its model is `cidW`. `cidW_ok` composes the parts'
refinements:

* `checkBasisDecl_refines` (lane `decls`),
* `indParamsOk_refines` (`IndRealIpo`),
* `blockParts_refines` (`IndPartsSpec15`; its record's slices lie below the top, `ShapeSl`, which
  gives `check_block`'s `ShapeSrc` and `RecsB`),
* `checkBlock_refines` (`IndInstallSpec37`),
* `checkShapeless_refines` (`IndPartsSpec4`).

`ShapeCV` (the members' constant records within `EREC`) follows from the record's decoding below
the tops (`shapeCV_of_decB`).

`basis_pin_hit` refines `basisPinHit` by `basisPinHitL`'s proof (`IndRealBph2.basisPinHit_ok`).

**Pending program facts** (hypotheses here, to be discharged):

* `PartsOK p`: `block_parts`' record also satisfies what the recursor stage takes as input,
  `ShapeLp`, the fact `PassGrcOK` asks of the pass.

The walk memos (`PosMR`, the `mentions_any` and `target_abs` memos, `abstract1`'s memo) cross
`basis_pin_hit` and `block_parts` by their write set (`closedA … cidFreeA cidFreeC`: no array in
`201..208` or `49`, no `CTL` word in `202..219` or `48`; checked by `#eval` for `checkerProg`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The model -/

section model
variable (p : Prog)

/-- After `check_basis_decl` or `check_block`: the view. -/
def cidK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- After `block_parts`: the one route (the shapeless decline never returns). -/
def cidK4 (n : Nat) (vis o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then none
    else cidK2 (callW p n "check_block" [vis, o, l, r4.tail.headD 0] m4)

/-- After `ind_params_ok`. -/
def cidK3 (n : Nat) (vis o l w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then none else cidK4 p n vis o l (callW p n "block_parts" [w, o, l] m3)

/-- After `basis_pin_hit`. -/
def cidK1 (n : Nat) (vis o l w : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then cidK3 p n vis o l w (callW p n "ind_params_ok" [w, o, l] m1)
    else cidK2 (callW p n "check_basis_decl" [vis, r1.tail.headD 0] m1)

/-- **The model of `check_ind_decl(vis, boff, blen, nP)`.** -/
def cidW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, vis, o, l, w => cidK1 p n vis o l w (callW p n "basis_pin_hit" [o, l] m)

section arms
variable (n : Nat) (m m1 m3 m4 : Mem) (vis o l w : Word) (r r1 r3 r4 : List Word)
theorem cidW_step : cidW p (n + 1) m vis o l w =
    cidK1 p n vis o l w (callW p n "basis_pin_hit" [o, l] m) := rfl
theorem cidK1_some : cidK1 p n vis o l w (some (r1, m1)) =
    if r1.headD 0 = 0 then cidK3 p n vis o l w (callW p n "ind_params_ok" [w, o, l] m1)
    else cidK2 (callW p n "check_basis_decl" [vis, r1.tail.headD 0] m1) := rfl
theorem cidK3_some : cidK3 p n vis o l w (some (r3, m3)) =
    if r3.headD 0 = 0 then none else cidK4 p n vis o l (callW p n "block_parts" [w, o, l] m3) := rfl
theorem cidK4_some : cidK4 p n vis o l (some (r4, m4)) =
    if r4.headD 0 = 0 then none
    else cidK2 (callW p n "check_block" [vis, o, l, r4.tail.headD 0] m4) := rfl
theorem cidK2_some : cidK2 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] cidW_step => cidW p (n + 1) m vis o l w
grind_pattern [ind_grind] cidK1_some => cidK1 p n vis o l w (some (r1, m1))
grind_pattern [ind_grind] cidK3_some => cidK3 p n vis o l w (some (r3, m3))
grind_pattern [ind_grind] cidK4_some => cidK4 p n vis o l (some (r4, m4))
grind_pattern [ind_grind] cidK2_some => cidK2 (some (r, m))

theorem cid_specW (hp : p.lookup "check_ind_decl" = some checkIndDecl)
    (hsf : p.lookup "check_shapeless_formers" = some checkShapelessFormers)
    (hsl : p.lookup "check_shapeless" = some checkShapeless) (n : Nat) (s₀ : St) (vis o l w : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_ind_decl" [vis, o, l, w]
    ⦃fun r s' => LocEq s' s₀ ∧ cidW p n s₀.mem vis o l w = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkIndDecl]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        callW_spec p n "basis_pin_hit", callW_spec p n "check_basis_decl",
        callW_spec p n "ind_params_ok", callW_spec p n "block_parts", callW_spec p n "check_block",
        checkShapeless_refines p hsf hsl n] <;>
      finish (gen := 20)

end model

/-! ## The pending program facts -/

/-- **`block_parts`' record has its members' constructors' level-parameter slices in `EREC`**
(`ShapeLp`, pending), what the recursor stage takes of its input. -/
def PartsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (w o l : Word) (m m' : Mem) (r : List Word),
    callW p n "block_parts" [w, o, l] m = some (r, m') → r.headD 0 ≠ 0 →
    ShapeLp m' (r.tail.headD 0)

/-! ## The write set of `basis_pin_hit` and `block_parts` -/

/-- The arrays they may write: all below 256 but the stage memos' (`201..208`) and `abstract1`'s
memo (`49`). -/
def cidFreeA : List ArrId := (List.range 256).filter (fun b => (b < 201 ∨ 208 < b) ∧ b ≠ 49)

/-- The `CTL` words they may write: all below 256 but the stage memos' (`202..219`) and
`abstract1`'s (`48`). -/
def cidFreeC : List Word :=
  ((List.range 256).filter (fun c => (c < 202 ∨ 219 < c) ∧ c ≠ 48)).map Nat.toUInt64

/-- The callees of `check_ind_decl` that cross the walk memos by their write set. -/
def cidFrameCallees : List FnName := ["basis_pin_hit", "block_parts"]

/-- The memos the arm carries to `check_block`. -/
def CidMemos (m : Mem) : Prop :=
  PosMR m ∧ (∃ mp, maMR m mp) ∧ AbsOK m ∧ ∃ mp, taMR m mp

theorem CidMemos.frame {m m' : Mem} (h : CidMemos m) (hf : MemFrame cidFreeA cidFreeC m m') :
    CidMemos m' := by
  have hM : MFr [] [] m m' := MFr.of_frame hf
    (fun b hb => by
      simp only [cidFreeA, List.mem_filter, List.mem_range, decide_eq_true_eq] at hb
      exact hb.2.1)
    (fun x hx => by
      simp only [cidFreeC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
      obtain ⟨c, ⟨hc, h1, -⟩, rfl⟩ := hx
      have : (Nat.toUInt64 c).toNat = c := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
      rw [this]; exact h1)
  obtain ⟨hP, ⟨mp, hma⟩, hA, ⟨tp, hta⟩⟩ := h
  refine ⟨hP.fr hM, ⟨mp, maMR_mfr hM hma⟩, ?_, ⟨tp, taMR_mfr hM (by simp) (by simp) hta⟩⟩
  exact AFr.of_frame hf
    (by simp only [cidFreeA, List.all_eq_true, List.mem_filter, List.mem_range, decide_eq_true_eq, bne_iff_ne,
          ne_eq]; intro b hb; exact hb.2.2)
    (by simp only [cidFreeC, List.all_eq_true, List.mem_map, List.mem_filter, List.mem_range,
          decide_eq_true_eq, bne_iff_ne, ne_eq]
        rintro x ⟨c, ⟨hc, -, h48⟩, rfl⟩ e
        apply h48
        have := congrArg UInt64.toNat e
        rwa [UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)] at this) hA

theorem CidMemos.call {p : Prog} {fs : List FnName} (hcl : closedA p cidFreeA cidFreeC fs = true)
    {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem} {r : List Word} {m' : Mem}
    (h : callW p n f vs m = some (r, m')) (hM : CidMemos m) : CidMemos m' :=
  hM.frame (run_memFrame hcl hf (run_of_callW h)).1

/-! ## `ShapeCV` from the record's decoding -/

/-- A `BlockShape` record decoded below the tops has its members' constant records in `EREC`. -/
theorem shapeCV_of_decB {m : Mem} {q : Word} {bs : BlockShape}
    (h : DecB (fun m => decBS m q.toNat) m bs) : ShapeCV m q := by
  intro o l ho hl j hj c hc d hd
  obtain ⟨hmem, -⟩ := decBS_some (show decBS (truncM m) q.toNat = some bs from h)
  obtain ⟨o', l', ho', hl', hd'⟩ := decAt_some hmem
  rw [(rec2IwN_trunc ho').2] at ho
  rw [(rec2IwN_trunc hl').2] at hl
  obtain rfl := Option.some.inj ho
  obtain rfl := Option.some.inj hl
  obtain ⟨v, ms, hv, hms, -⟩ := decPL_get _ _ _ hd' j hj
  rw [(rec2IwN_trunc hv).2] at hc
  obtain rfl := Option.some.inj hc
  simp only [decMS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hms
  obtain ⟨d', hd'', cv, hcv, -⟩ := hms
  rw [(rec2IwN_trunc hd'').2] at hd
  obtain rfl := Option.some.inj hd
  exact (rec3CVExt_of_trunc hcv).1

/-! ## The arm -/

/-- The lookups of the inductive arm. -/
structure CidProg (p : Prog) : Prop where
  cid : p.lookup "check_ind_decl" = some checkIndDecl
  csf : p.lookup "check_shapeless_formers" = some checkShapelessFormers
  csl : p.lookup "check_shapeless" = some checkShapeless
  basis : BasisProg p
  canon : CanonProg p
  rom : L.Rom.RomRefs p
  pa : p.lookup "pin_at" = some pinAtL
  cbd : p.lookup "check_basis_decl" = some checkBasisDeclL
  ps : p.lookup "pi_sort_tele_len" = some L.Front.Ind.piSortTeleLen
  ev : p.lookup "e_view" = some eView
  ipo : p.lookup "ind_params_ok" = some L.Checker.indParamsOkL
  parts : IndPartsProg5 p
  cb : CbProg p
  bph : BphProg p

/-- **`check_ind_decl`'s model refines the `.indDecl` arm of `checkDecl`** at the stage relation.
Inputs: the block's `EREC` slice decoded below the tops, the twin state well formed (`StateOK`,
for the basis pin's canonical comparison), an
environment whose entries are visible and whose constructors' sums are words, and the walk
memos (`CidMemos`). Program facts: the lookups (`CidProg`), the write sets, `AbsKeep` of the
callees outside the `abstract1` cascade, and the pending `PassGrcOK` and `PartsOK`. -/
@[refines_part ConRon.Arena.checkDecl "the inductive arm (check_ind_decl), under StageR"]
theorem cidW_ok {p : Prog} (P : CidProg p) {fs fs2 fsR fsT fsC : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfs : ∀ f ∈ passCallees, f ∈ fs)
    (hfr : "block_raw_rec" ∈ fs) (hcl2 : closedA p hbFreeA hbFreeC fs2 = true)
    (hfs2 : ∀ f ∈ tailCallees, f ∈ fs2) (hclR : closedA p rcFreeA rcFreeC fsR = true)
    (hfR : ∀ f ∈ tailRcCallees, f ∈ fsR) (hclT : closedA p taFreeA taFreeC fsT = true)
    (hfT : ∀ f ∈ blockTaCallees, f ∈ fsT) (hclC : closedA p cidFreeA cidFreeC fsC = true)
    (hfC : ∀ f ∈ cidFrameCallees, f ∈ fsC)
    (hkp : ∀ f ∈ passKeepCallees, AbsKeep p f) (hkt : ∀ f ∈ tailKeepCallees, AbsKeep p f)
    (hkr : AbsKeep p "block_raw_rec") (hgp : PassGrcOK p) (hpo : PartsOK p)
    {n : Nat} (hn : 2 ^ 31 + (n + 4) ≤ coreWalkFuel)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {o l w : Word} {r : List Word} {block : List IConstantInfo}
    {pins : List INatOpPinSet}
    (h : cidW p n m vis o l w = some (r, m')) (hS : StageR dn vis fe m a)
    (hok : ConRon.Bridge.StateOK a)
    (hblk : DecB (fun m => decEBlk dn m o.toNat l.toNat) m block) (hb : o.toNat + l.toNat ≤ erTop m)
    (hv : AllVis fe) (hcs : CtorSums fe) (hM : CidMemos m) :
    ∃ fe' a', (checkDecl V pins fe (.indDecl block w.toNat)).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ IWGrow m m' := by
  cases n with
  | zero => simp [cidW] at h
  | succ n =>
  rw [cidW_step] at h
  -- `basis_pin_hit`
  cases c1 : callW p n "basis_pin_hit" [o, l] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1, cidK1_some] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, hx⟩ := basisPinHit_ok P.bph n dn vis fe m m1 a o l block r1 hS hok hblk c1
  have hM1 := hM.call hclC (hfC _ (by simp [cidFrameCallees])) c1
  have hblk1 := hblk.grow (decEBlk_mono _ _ _) hg1
  cases x with
  | some kind =>
    obtain ⟨hz, hk4, hkind⟩ := hx
    rw [if_neg hz] at h
    cases c2 : callW p n "check_basis_decl" [vis, r1.tail.headD 0] m1 with
    | none => rw [c2] at h; cases h
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [c2, cidK2_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨s2, hs2, -, hok2, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (checkBasisDecl_refines p P.basis P.canon P.rom P.pa P.cbd n ⟨m1, Locals.init []⟩ a1 dn hdn fe
        vis (r1.tail.headD 0) (by omega) hS1
        (fun e => absurd hk4 (by rw [e]; decide))) c2
    subst hs2
    have hrun2 := AM.run_of_ok _ _ hok2
    rw [hkind] at hrun2 hS2
    refine ⟨_, _, ?_, by simpa using hS2, hg1.trans hg2⟩
    simp only [checkDecl, StateT.run_bind, hrun1, exc_ok_bind']
    exact hrun2
  | none =>
  rw [if_pos hx] at h
  -- `ind_params_ok`
  have hbE : o.toNat + l.toNat < 2 ^ 64 := by
    have := hS.2.2.1; have := hS.2.2.2.2.1; omega
  cases c3 : callW p n "ind_params_ok" [w, o, l] m1 with
  | none => rw [c3] at h; cases h
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, cidK3_some] at h
  obtain ⟨s3, hs3, -, hm3, hok3, hst3, hres3, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (indParamsOk_refines p P.ps P.ev P.ipo n ⟨m1, Locals.init []⟩ a1 dn vis fe w o l block hS1 hblk1 hbE)
    (callW_mono c3 (Nat.le_succ n))
  simp only at hm3
  rw [hm3] at hs3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hst3] at hrun3
  by_cases z3 : r3.headD 0 = 0
  · rw [if_pos z3] at h; cases h
  rw [if_neg z3] at h
  have hpo3 : AM.res (indParamsOk w.toNat block) a1 = true := by
    rw [← hres3]; simpa using z3
  rw [hpo3] at hrun3
  -- `block_parts`
  cases c4 : callW p n "block_parts" [w, o, l] m1 with
  | none => rw [c4] at h; cases h
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, cidK4_some] at h
  obtain ⟨s4, hs4, -, hok4, hR4, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (blockParts_refines p P.parts n ⟨m1, Locals.init []⟩ a1 dn vis fe w o l block hS1 hblk1)
    (callW_mono c4 (by omega))
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  have hM4 := hM1.call hclC (hfC _ (by simp [cidFrameCallees])) c4
  by_cases z4 : r4.headD 0 = 0
  · rw [if_pos z4] at h; cases h
  rw [if_neg z4] at h
  have hlp4 := hpo n w o l m1 s4.mem r4 c4 z4
  generalize AM.res (blockParts? w.toNat block) a1 = bp at hrun4 hR4
  generalize AM.st (blockParts? w.toNat block) a1 = a4 at hrun4 hS4
  cases bp with
  | none => exact absurd hR4 z4
  | some bp =>
  obtain ⟨-, hd4, hsl4⟩ := hR4
  obtain ⟨bs⟩ := bp
  have hq4 : DecB (fun m => decBS m (r4.tail.headD 0).toNat) s4.mem bs := by
    have hd : decBP (truncM s4.mem) (r4.tail.headD 0).toNat = some ⟨bs⟩ := hd4
    simp only [decBP, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hd
    obtain ⟨bs', hbs', e⟩ := hd
    cases e
    exact hbs'
  obtain ⟨hP4, hma4, hA4, hta4⟩ := hM4
  -- `check_block`
  cases c5 : callW p n "check_block" [vis, o, l, r4.tail.headD 0] s4.mem with
  | none => rw [c5] at h; cases h
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5, cidK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, -⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (checkBlock_refines P.cb hcl hfs hfr hcl2 hfs2 hclR hfR hclT hfT hgp n (by omega) ⟨s4.mem, Locals.init []⟩
      a4 hS4 hq4 hsl4.1 (shapeCV_of_decB hq4) (hblk1.grow (decEBlk_mono _ _ _) hg4) hv hcs hP4 hma4 hA4
      hkp hkt hkr hta4 hsl4.2 hlp4) (callW_mono c5 (by omega))
  subst hs5
  have hrun5 := AM.run_of_ok _ _ hok5
  refine ⟨_, _, ?_, by simpa using hS5, hg1.trans (hg4.trans hg5)⟩
  simp only [checkDecl, StateT.run_bind, hrun1, exc_ok_bind', hrun3, Bool.not_true, Bool.false_eq_true, ite_false, hrun4]
  exact hrun5

end L.Ind
