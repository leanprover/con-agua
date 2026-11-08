module

public import ConAgua.Arena.DeclAndPinIndCopy2
import ConAgua.Arena.DeclCanonInfo
import ConAgua.Arena.DeclArmQuot
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.DeclTwin
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.SimLib
public import ConAgua.Arena.DeclAndPinInd
public import ConAgua.Arena.DeclCanonSpec
public import ConAgua.Rom.CIReadSpec
import all ConAgua.Arena.DeclAndPin

@[expose] public section

/-!
# The `And` pin's inductive arm, part 3: `and_pin_ok(i)` refines `andPinOk (.indDecl block nP)`

`and_pin_ok`'s whole model (`andpW`): the flag; for kind `6` the name test over the block
(`and_block_named`, `abnW_eq`), the parameter count, then the block copied (`ind_block_to_erec`,
`indBlockToErec_ok`; `er_to_iw`) and compared with the ROM's pinned `And` block (`rom_and_pin`,
a hypothesis: `RomAndPinRef`, helper `decls4-rom`) by `canon_eq_list` (`canonEqList_refines`,
which compares literals by handle: `LitInj`, from the twin state's `StateOK`). The one-constant
kinds are `andPinW` (`DeclAndPin.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

/-- The words `er_to_iw` leaves: the copy at the old top. -/
theorem erToIwW_wordsA {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (_hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64)
    (hsrc : o.toNat + l.toNat ≤ (m.arr64 EREC).size) :
    ∀ i < l.toNat, (m'.arr64 IW)[(rdW (m.arr64 CTL) 200).toNat + i]? = (m.arr64 EREC)[o.toNat + i]? := by
  sorry

end L.Ind

namespace L.Arena

open L.Front (DECL DLP trunc decCIs IndDeclAt dw)
open L.Ind (erTop iwTop StageR IWGrow decW0B erToIwW erToIw iwAlloc erCopy decRBlk decPL iwN iwA truncM erA truncM_iw_get)

/-! ## The model -/

section model
variable (p : Prog)

/-- After the comparison. -/
def andpK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0], m4)

/-- After `rom_and_pin`. -/
def andpK3 (n : Nat) (r2 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => andpK4 (callW p n "canon_eq_list"
      [r2.headD 0, r2.tail.headD 0, r3.headD 0, r3.tail.headD 0] m3)

/-- After `er_to_iw`. -/
def andpK2 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => andpK3 p n r2 (callW p n "rom_and_pin" [] m2)

/-- After `ind_block_to_erec`. -/
def andpK1 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => andpK2 p n (callW p n "er_to_iw" [r1.headD 0, r1.tail.headD 0] m1)

/-- **The model of `and_pin_ok(i)`**, every record kind. -/
def andpW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, i =>
    if rdW (m.arr64 PINS) 0 = 0 then none
    else if rdW (m.arr64 DECL) (1 + 8 * i) = 6 then
      if abnW m (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)).toNat = 0 then
        some ([1], m)
      else if rdW (m.arr64 DECL) (5 + 8 * i) ≠ 2 then some ([0], m)
      else andpK1 p n (callW p n "ind_block_to_erec" [i] m)
    else some ([andPinW m i], m)

section arms
variable (n : Nat) (m m1 m2 m3 m4 : Mem) (i : Word) (r1 r2 r3 r4 : List Word)
theorem andpK1_some : andpK1 p n (some (r1, m1)) =
    andpK2 p n (callW p n "er_to_iw" [r1.headD 0, r1.tail.headD 0] m1) := rfl
theorem andpK2_some : andpK2 p n (some (r2, m2)) = andpK3 p n r2 (callW p n "rom_and_pin" [] m2) := rfl
theorem andpK3_some : andpK3 p n r2 (some (r3, m3)) = andpK4 (callW p n "canon_eq_list"
    [r2.headD 0, r2.tail.headD 0, r3.headD 0, r3.tail.headD 0] m3) := rfl
theorem andpK4_some : andpK4 (some (r4, m4)) = some ([r4.headD 0], m4) := rfl
theorem andpW_step : andpW p (n + 1) m i =
    if rdW (m.arr64 PINS) 0 = 0 then none
    else if rdW (m.arr64 DECL) (1 + 8 * i) = 6 then
      if abnW m (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)).toNat = 0 then
        some ([1], m)
      else if rdW (m.arr64 DECL) (5 + 8 * i) ≠ 2 then some ([0], m)
      else andpK1 p n (callW p n "ind_block_to_erec" [i] m)
    else some ([andPinW m i], m) := rfl
end arms

grind_pattern [ind_grind] andpK1_some => andpK1 p n (some (r1, m1))
grind_pattern [ind_grind] andpK2_some => andpK2 p n (some (r2, m2))
grind_pattern [ind_grind] andpK3_some => andpK3 p n r2 (some (r3, m3))
grind_pattern [ind_grind] andpK4_some => andpK4 (some (r4, m4))
grind_pattern [ind_grind] andpW_step => andpW p (n + 1) m i

theorem andPinOk_specA (hp : p.lookup "and_pin_ok" = some andPinOkL)
    (hab : p.lookup "and_block_named" = some andBlockNamed) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "and_pin_ok" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ andpW p n s₀.mem i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, andPinOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        andBlockNamed_specW p hab n,
        callW_spec p n "ind_block_to_erec", callW_spec p n "er_to_iw", callW_spec p n "rom_and_pin",
        callW_spec p n "canon_eq_list"] <;>
      finish (gen := 20) [andPinW, lo32, rdW_eq]

end model

/-! ## Helpers -/

/-- A front block's slice does not start at the cut pool's word `0` (its pointer there reads `0`,
a record of kind `0`, which is no front constant). -/
theorem front_bo {P : Array Word} {t : Nat} {dn0 : NIdx → Option ConLeche.Name} {bo bl : Nat}
    {block : List IConstantInfo} (h : decCIs (trunc P t) bo bl = some block)
    (hFB : FrontBlock block) : 1 ≤ bo ∨ bl = 0 := by
  sorry

theorem denoteCIList_length {st : ConRon.Arena.EStore} :
    ∀ (cis : List IConstantInfo) (cs : List ConLeche.ConstantInfo),
      ConRon.Arena.Frontend.denoteCIList st cis = some cs → cis.length = cs.length
  | [], cs, h => by simp [ConRon.Arena.Frontend.denoteCIList] at h; subst h; rfl
  | c :: cis, cs, h => by
    simp only [ConRon.Arena.Frontend.denoteCIList] at h
    split at h
    · rename_i x xs _ hxs
      simp only [Option.some.injEq] at h; subst h
      simp [denoteCIList_length cis xs hxs]
    · cases h

/-- The pinned `And` block, interned: three constants, the state well formed after. -/
theorem andPinDecls_ok {a a1 : AState} {pinned : List IConstantInfo}
    (h : andPinDecls.run a = .ok (pinned, a1)) (hok : ConRon.Bridge.StateOK a) :
    ConRon.Bridge.StateOK a1 ∧ pinned.length = 3 := by
  have g2 : andPinDecls a = .ok (pinned, a1) := h
  simp only [ConRon.Arena.andPinDecls, ConRon.Arena.internCIList] at g2
  obtain ⟨p, s₃, hgo, hrest⟩ := ConRon.Bridge.AM.bind_ok g2
  obtain ⟨m1, cis⟩ := p
  obtain ⟨hv, hst⟩ := ConRon.Bridge.AM.pure_ok hrest
  subst hv; subst hst
  obtain ⟨hstep, hdp, -⟩ :=
    ConRon.Bridge.Frontend.internCIList_sstep ConLeche.andPin hok
      (ConRon.Bridge.Frontend.EMemoOK.empty _) hgo
  exact ⟨hstep.ok, by rw [denoteCIList_length _ _ hdp]; decide⟩

/-- A block decoded below the tops (`decRBlk`) is canon's slice premise. -/
theorem decRBlk_canon {dn : NIdx → Option ConLeche.Name} {m : Mem} {r : List Word}
    {cis : List IConstantInfo} (h : decRBlk dn m r cis) (hl : cis.length ≠ 0) :
    decPL m (fun q => decCI (erecP m) q) (r.headD 0).toNat (r.tail.headD 0).toNat = some cis ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m := by
  obtain ⟨hD, -⟩ := h
  have hD' : decPL (truncM m) (fun q => decCI (erA (truncM m)) q) (r.headD 0).toNat
      (r.tail.headD 0).toNat = some cis := hD
  have hlen := L.Ind.decPL_length (truncM m) hD'
  refine ⟨mapM_imp _ _ hD' fun j _ y hy => ?_, ?_⟩
  · simp only [bind, Option.bind_eq_some_iff] at hy ⊢
    obtain ⟨v, hv, hy⟩ := hy
    exact ⟨v, (IWGrow.refl m).truncExt.1.nat? hv, ArrExt.decCI (truncM_erecP m) hy⟩
  · obtain ⟨v, y, hv, -, -⟩ := L.Ind.decPL_get _ _ _ hD' ((r.tail.headD 0).toNat - 1) (by omega)
    simp only [iwN, nat?, Option.map_eq_some_iff] at hv
    obtain ⟨w, hw, -⟩ := hv
    have := (truncM_iw_get hw).1
    omega

/-- A pointer slice decoded in `IW` below its top, in `erecP`, stays decoded as the pools grow. -/
theorem decPL_growAP {m m' : Mem} {o l : Nat}
    {xs : List IConstantInfo} (h : decPL m (fun q => decCI (erecP m) q) o l = some xs)
    (hb : o + l ≤ iwTop m) (hg : IWGrow m m') :
    decPL m' (fun q => decCI (erecP m') q) o l = some xs := by
  sorry

/-- **`er_to_iw` of the copied block**: the `IW` slice decodes (in `erecP`) to the block. -/
theorem erToIw_blk {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} {block : List IConstantInfo}
    (h : erToIwW n m o l = some (r, m')) (hS : StageR vis fe m a)
    (hd : L.Front.decCIsR (erecP m) o.toNat l.toNat = some block) (hb : o.toNat + l.toNat ≤ erTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = l ∧
      decPL m' (fun q => decCI (erecP m') q) (r.headD 0).toNat l.toNat = some block ∧
      (r.headD 0).toNat + l.toNat ≤ iwTop m' := by
  sorry

/-! ## The refinement of the inductive arm -/

/-- The twin's arm at a filled pin table: the name test over `andHs`. -/
theorem andPinOk_ind_run {m : Mem} {a : AState} (hF : PinsFull m a.pins)
    (block : List IConstantInfo) (nP : Nat) :
    (andPinOk (.indDecl block nP)).run a =
      (if blockAndNamed (andHs m) block then
        (if nP == 2 then (do let pinned ← andPinDecls; canonEqList block pinned) else pure false)
      else pure true).run a := by
  simp only [andPinOk, StateT.run_bind, andPinNameHs_runW hF]
  rfl

/-- `and_pin_ok`'s inductive arm's lookups (beyond the canonical comparisons, `CanonProg`). -/
structure AndPinIndProg (p : Prog) : Prop extends IbeProg p where
  and_pin_ok : p.lookup "and_pin_ok" = some andPinOkL
  and_block_named : p.lookup "and_block_named" = some andBlockNamed
  iw_alloc : p.lookup "iw_alloc" = some iwAlloc
  er_copy : p.lookup "er_copy" = some erCopy
  er_to_iw : p.lookup "er_to_iw" = some erToIw
  canon : L.Ind.CanonProg p

/-- **`and_pin_ok`'s inductive arm refines `andPinOk (.indDecl block nP)`** (model level): from
the stage relation, the front's record `i` (`IndDeclAt`, a block of the front's shape) and a
well-formed twin state, the twin's test runs to `b`, the stage relation holds after it, the pools
only grew, and the result word is `b`. `rom_and_pin` by its refinement (`RomAndPinRef`). -/
theorem andpW_ind_ok {p : Prog} (hp : AndPinIndProg p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} (hR : L.Rom.RomAndPinRef p dn vis fe) {n : Nat} {m m' : Mem}
    {i : Word} {r : List Word} {block : List IConstantInfo} {nP : Nat} {a : AState}
    (h : andpW p n m i = some (r, m')) (hS : StageR vis fe m a)
    (hdecl : IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP) (hFB : FrontBlock block)
    (hok : ConRon.Bridge.StateOK a)
    (hD : (m.arr64 DECL).size < 2 ^ 63) (hP : (m.arr64 DLP).size < 2 ^ 63) :
    ∃ b a', (andPinOk (.indDecl block nP)).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  sorry

/-- **`and_pin_ok(i)` refines `andPinOk (.indDecl block nP)`** on the front's inductive record
`i` (`IndDeclAt`, of the front's shape `FrontBlock`), at a well-formed twin state (`StateOK`,
which gives canon's `LitInj`); `rom_and_pin` by its refinement (`RomAndPinRef`, helper
`decls4-rom`). -/
@[refines_part ConRon.Arena.andPinOk "the inductive arm (front blocks, FrontBlock)"]
theorem andPinOkInd_refines {p : Prog} (hp : AndPinIndProg p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} (hR : L.Rom.RomAndPinRef p dn vis fe) (i : Word)
    (block : List IConstantInfo) (nP : Nat) :
    L.Ind.RefAM p "and_pin_ok" [i]
      (fun m a => StageR vis fe m a ∧ IndDeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat block nP ∧
        FrontBlock block ∧ ConRon.Bridge.StateOK a ∧
        (m.arr64 DECL).size < 2 ^ 63 ∧ (m.arr64 DLP).size < 2 ^ 63)
      (andPinOk (.indDecl block nP)) (L.Ind.KeepPost vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hdecl, hFB, hok, hD, hP⟩
  refine triple_post (andPinOk_specA p hp.and_pin_ok hp.and_block_named n s₀ i) ?_
  rintro r s' ⟨hl, hW⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := andpW_ind_ok hp hR hW hS hdecl hFB hok hD hP
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok', by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

/-! ## Every record kind the front produces -/

/-- A one-constant record (kind word not `6`): the name test, memory unchanged. -/
theorem andpW_one {p : Prog} {n : Nat} {m m' : Mem} {i : Word} {r : List Word}
    (h : andpW p n m i = some (r, m')) (hk : rdW (m.arr64 DECL) (1 + 8 * i) ≠ 6) :
    rdW (m.arr64 PINS) 0 ≠ 0 ∧ m' = m ∧ r = [andPinW m i] := by
  cases n with
  | zero => simp [andpW] at h
  | succ n =>
  rw [andpW_step] at h
  have hfl : ¬ rdW (m.arr64 PINS) 0 = 0 := fun hfl => by rw [ite_eq_left hfl] at h; cases h
  rw [ite_eq_right hfl, ite_eq_right hk] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨hfl, h.2.symm, h.1.symm⟩

/-- A one-constant record: `and_pin_ok` is `andPinOk`'s name test, memory and twin state kept. -/
theorem andPinOkOne_ok {p : Prog} (hp : AndPinIndProg p)
    {vis : Word} {fe : IFEnv} (i : Word) (d : IDeclaration) :
    L.Ind.RefAM p "and_pin_ok" [i]
      (fun m a => StageR vis fe m a ∧ L.Front.DeclAt (m.arr64 DECL) (m.arr64 DLP) i.toNat d ∧
        (m.arr64 DECL).size < 2 ^ 63)
      (andPinOk d) (L.Ind.KeepPost vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hd, hD⟩
  refine triple_post (andPinOk_specA p hp.and_pin_ok hp.and_block_named n s₀ i) ?_
  rintro r s' ⟨hl, hW⟩
  have hk : dw (s₀.mem.arr64 DECL) i.toNat 0 ≠ 0 ∧ dw (s₀.mem.arr64 DECL) i.toNat 0 ≠ 6 := by
    cases d <;> simp only [L.Front.DeclAt] at hd <;> (try exact hd.elim) <;> rw [hd.1] <;> decide
  have e1 : rdW (s₀.mem.arr64 DECL) (1 + 8 * i) = dw (s₀.mem.arr64 DECL) i.toNat 0 :=
    rdW_dwI hD hk.1 rfl (by decide)
  have e2 : rdW (s₀.mem.arr64 DECL) (2 + 8 * i) = dw (s₀.mem.arr64 DECL) i.toNat 1 :=
    rdW_dwI hD hk.1 rfl (by decide)
  obtain ⟨hfl, hm, hr⟩ := andpW_one hW (by rw [e1]; exact hk.2)
  have hF : PinsFull s₀.mem a₀.pins := hS.check.pins.full hfl
  obtain ⟨hok', hst, hres⟩ := AM.of_run_ok _ _ _ _ (andPinOk_run hd hF)
  refine ⟨hl, hok', ?_⟩
  rw [hst, hres, hm, hr]
  refine ⟨hS, IWGrow.refl _, ?_, ?_⟩
  · have e12 : rdW (s₀.mem.arr64 PINS) 12 = pinW s₀.mem 12 := rfl
    have e49 : rdW (s₀.mem.arr64 PINS) 49 = pinW s₀.mem 49 := rfl
    have e50 : rdW (s₀.mem.arr64 PINS) 50 = pinW s₀.mem 50 := rfl
    simp only [andPinW, e2, e12, e49, e50, List.headD_cons]
    generalize lo32 (dw (s₀.mem.arr64 DECL) i.toNat 1) = x
    by_cases h1 : x = pinW s₀.mem 12 <;> by_cases h2 : x = pinW s₀.mem 49 <;>
      by_cases h3 : x = pinW s₀.mem 50 <;> simp [h1, h2, h3]
  · simp only [andPinW, List.headD_cons]; split <;> decide

/-- **`and_pin_ok(i)` refines `andPinOk d` for every record the front produces** (`DeclAtF`: the
one-constant kinds and inductive blocks; `basisDecl` has no front record, `DeclAtF` is `False`
there). An inductive block of the front's shape (`FrontBlock`, the constants `installIndD`
pushes); `rom_and_pin` by its refinement. -/
@[refines_part ConRon.Arena.andPinOk "the front's records (inductive blocks of the front's shape, FrontBlock)"]
theorem andPinOkF_refines {p : Prog} (hp : AndPinIndProg p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} (hR : L.Rom.RomAndPinRef p dn vis fe) (i : Word)
    (d : IDeclaration) :
    L.Ind.RefAM p "and_pin_ok" [i]
      (fun m a => StageR vis fe m a ∧ L.Front.DeclAtF (m.arr64 DECL) (m.arr64 DLP) i.toNat d ∧
        (∀ b nP, d = .indDecl b nP → FrontBlock b) ∧ ConRon.Bridge.StateOK a ∧
        (m.arr64 DECL).size < 2 ^ 63 ∧ (m.arr64 DLP).size < 2 ^ 63)
      (andPinOk d) (L.Ind.KeepPost vis fe decW0B) := by
  sorry

end L.Arena
