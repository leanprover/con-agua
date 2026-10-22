import ConAgua.Arena.DeclAndPinIndCopy2
import ConAgua.Arena.DeclCanonInfo
import ConAgua.Arena.DeclArmQuot
import ConAgua.Rom.CIReadSpec

/-!
# The `And` pin's inductive arm, part 3: `and_pin_ok(i)` refines `andPinOk (.indDecl block nP)`

`and_pin_ok`'s whole model (`apW`): the flag; for kind `6` the name test over the block
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
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Front (DECL DLP trunc decCIs IndDeclAt dw)
open L.Ind (erTop iwTop StageR IWGrow decW0B erToIwW erToIw iwAlloc erCopy decRBlk decPL iwN iwA truncM erA truncM_iw_get)

/-! ## The model -/

section model
variable (p : Prog)

/-- After the comparison. -/
def apK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => some ([r4.headD 0], m4)

/-- After `rom_and_pin`. -/
def apK3 (n : Nat) (r2 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => apK4 (callW p n "canon_eq_list"
      [r2.headD 0, r2.tail.headD 0, r3.headD 0, r3.tail.headD 0] m3)

/-- After `er_to_iw`. -/
def apK2 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => apK3 p n r2 (callW p n "rom_and_pin" [] m2)

/-- After `ind_block_to_erec`. -/
def apK1 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => apK2 p n (callW p n "er_to_iw" [r1.headD 0, r1.tail.headD 0] m1)

/-- **The model of `and_pin_ok(i)`**, every record kind. -/
def apW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, i =>
    if rdW (m.arr64 PINS) 0 = 0 then none
    else if rdW (m.arr64 DECL) (1 + 8 * i) = 6 then
      if abnW m (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)).toNat = 0 then
        some ([1], m)
      else if rdW (m.arr64 DECL) (5 + 8 * i) ≠ 2 then some ([0], m)
      else apK1 p n (callW p n "ind_block_to_erec" [i] m)
    else some ([andPinW m i], m)

section arms
variable (n : Nat) (m m1 m2 m3 m4 : Mem) (i : Word) (r1 r2 r3 r4 : List Word)
theorem apK1_some : apK1 p n (some (r1, m1)) =
    apK2 p n (callW p n "er_to_iw" [r1.headD 0, r1.tail.headD 0] m1) := rfl
theorem apK2_some : apK2 p n (some (r2, m2)) = apK3 p n r2 (callW p n "rom_and_pin" [] m2) := rfl
theorem apK3_some : apK3 p n r2 (some (r3, m3)) = apK4 (callW p n "canon_eq_list"
    [r2.headD 0, r2.tail.headD 0, r3.headD 0, r3.tail.headD 0] m3) := rfl
theorem apK4_some : apK4 (some (r4, m4)) = some ([r4.headD 0], m4) := rfl
theorem apW_step : apW p (n + 1) m i =
    if rdW (m.arr64 PINS) 0 = 0 then none
    else if rdW (m.arr64 DECL) (1 + 8 * i) = 6 then
      if abnW m (rdW (m.arr64 DECL) (3 + 8 * i)) (rdW (m.arr64 DECL) (4 + 8 * i)).toNat = 0 then
        some ([1], m)
      else if rdW (m.arr64 DECL) (5 + 8 * i) ≠ 2 then some ([0], m)
      else apK1 p n (callW p n "ind_block_to_erec" [i] m)
    else some ([andPinW m i], m) := rfl
end arms

grind_pattern [ind_grind] apK1_some => apK1 p n (some (r1, m1))
grind_pattern [ind_grind] apK2_some => apK2 p n (some (r2, m2))
grind_pattern [ind_grind] apK3_some => apK3 p n r2 (some (r3, m3))
grind_pattern [ind_grind] apK4_some => apK4 (some (r4, m4))
grind_pattern [ind_grind] apW_step => apW p (n + 1) m i

theorem andPinOk_specA (hp : p.lookup "and_pin_ok" = some andPinOkL)
    (hab : p.lookup "and_block_named" = some andBlockNamed) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "and_pin_ok" [i]
    ⦃fun r s' => LocEq s' s₀ ∧ apW p n s₀.mem i = some (r, s'.mem); ⊤⦄ := by
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
    {block : List IConstantInfo} (h : decCIs (trunc P t) dn0 bo bl = some block)
    (hFB : FrontBlock block) : 1 ≤ bo ∨ bl = 0 := by
  rcases bl with _ | k
  · right; rfl
  left
  refine Decidable.byContradiction fun hn => ?_
  have hb0 : bo = 0 := by omega
  subst hb0
  rw [decCIs_succ] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨c, ⟨v, hv, hc⟩, cs, -, rfl⟩ := h
  obtain ⟨w, hw, rfl⟩ : ∃ w, (trunc P t)[0]? = some w ∧ w.toNat = v := by simpa [nat?] using hv
  have := trunc_get_zero hw; subst this
  obtain ⟨kk, hkk, hk345⟩ := decCI_front_kind hc (hFB c (by simp))
  simp only [nat?, Option.map_eq_some_iff, UInt64.toNat_zero] at hkk
  obtain ⟨a, ha, rfl⟩ := hkk
  rw [hw] at ha; cases ha; simp at hk345

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
  obtain ⟨hstep, hdp, -, -⟩ :=
    ConRon.Bridge.Frontend.internCIList_sstep ConLeche.andPin hok
      (ConRon.Bridge.Frontend.EMemoOK.empty _) hgo
  exact ⟨hstep.ok, by rw [denoteCIList_length _ _ hdp]; decide⟩

/-- A block decoded below the tops (`decRBlk`) is canon's slice premise. -/
theorem decRBlk_canon {dn : NIdx → Option ConLeche.Name} {m : Mem} {r : List Word}
    {cis : List IConstantInfo} (h : decRBlk dn m r cis) (hl : cis.length ≠ 0) :
    decPL m (fun q => decCI (erecP m) dn q) (r.headD 0).toNat (r.tail.headD 0).toNat = some cis ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m := by
  obtain ⟨hD, -⟩ := h
  have hD' : decPL (truncM m) (fun q => decCI (erA (truncM m)) dn q) (r.headD 0).toNat
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
theorem decPL_grow {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {o l : Nat}
    {xs : List IConstantInfo} (h : decPL m (fun q => decCI (erecP m) dn q) o l = some xs)
    (hb : o + l ≤ iwTop m) (hg : IWGrow m m') :
    decPL m' (fun q => decCI (erecP m') dn q) o l = some xs := by
  unfold decPL at h ⊢
  refine mapM_imp _ _ h fun j hj y hy => ?_
  have hj' := List.mem_range.mp hj
  simp only [bind, Option.bind_eq_some_iff] at hy ⊢
  obtain ⟨v, hv, hy⟩ := hy
  refine ⟨v, ?_, ArrExt.decCI (IWGrow.erecPExt hg) hy⟩
  simp only [iwN, nat?, iwA] at hv ⊢
  rw [hg.2.2.1 _ (by omega)]; exact hv

end L.Arena
