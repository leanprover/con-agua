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
* `checkShapeless_never` (no callee contract: the function aborts).

`ShapeCV` (the members' constant records within `EREC`) follows from the record's decoding below
the tops (`shapeCV_of_decB`).

`basis_pin_hit` refines `basisPinHit` by `basisPinHitL`'s proof (`IndRealBph2.basisPinHit_ok`).

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

/-- **`check_shapeless` never returns**: it calls `check_shapeless_formers` (whatever that
does) and then aborts. Unlike `checkShapeless_refines` this needs no contract of the callee. -/
theorem checkShapeless_never (p : Prog)
    (hp : p.lookup "check_shapeless" = some checkShapeless) (n : Nat) (s₀ : St)
    (vis off cnt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_shapeless" [vis, off, cnt]
    ⦃fun _ _ => False; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkShapeless]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        callW_spec p n "check_shapeless_formers"] <;>
      finish

theorem cid_specW (hp : p.lookup "check_ind_decl" = some checkIndDecl)
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
        checkShapeless_never p hsl n] <;>
      finish (gen := 20)

end model

/-! ## The write set of `basis_pin_hit` and `block_parts` -/

/-- The arrays they may write: all below 320 (both tiers) but the stage memos' (`201..208`) and `abstract1`'s
memo (`49`), and since lane `indstaget` the pins and the core's walk memos. -/
def cidFreeA : List ArrId := (List.range 388).filter (fun b => (b < 201 ∨ 208 < b) ∧ b ≠ 49 ∧ b ≠ 50 ∧ b ≠ 51 ∧ b ≠ 155 ∧
  b ≠ PINS ∧ b ≠ 151 ∧ b ≠ 152 ∧ b ≠ 153 ∧ b ≠ 52 ∧ b ≠ 53 ∧ b ≠ 54)

/-- The `CTL` words they may write: all below 256 but the stage memos' (`202..219`) and
the walk memos' epoch words (`48`, `50`, `52`, `158`). -/
def cidFreeC : List Word :=
  ((List.range 256).filter (fun c => (c < 202 ∨ 219 < c) ∧ c ≠ 48 ∧ c ≠ 50 ∧ c ≠ 52 ∧ c ≠ 158 ∧
    c ≠ 152 ∧ c ≠ 154 ∧ c ≠ 156 ∧ c ≠ 54 ∧ c ≠ 56 ∧ c ≠ 58)).map Nat.toUInt64

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
  exact AFr.of_frame hf (by decide +kernel) (by decide +kernel) hA

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

end L.Ind
