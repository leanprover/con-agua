import ConAgua.Arena.IndRealCapsC
import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.LevelSimpRel
import ConAgua.Arena.IndInstallSpec23

/-!
# `block_large_elim_allowed` refines `blockLargeElimAllowed` (lane `indproofs4`, helper `lz`)

`block_large_elim_allowed(p, nested)` (`IndParts.lean`) is core-free: `lv_nz` of the shape's result
sort (`nzW_ok`: `isNeverZero` on the heap), then `block_shape_num_ctors` and two shape words; it
writes nothing. The twin reads the result sort back (`readLevelM`), so the refinement needs the
readback cache holding readbacks and the sort's readback (`StageR` alone does not give them; this
is why `IndInstallSpec39.blockLargeElimAllowed_spec` was a stub contract):

* `bleW_ok`: under `StageR`, `ReadLCOK` and the sort's readback, the twin's run, the memory
  unchanged, the verdict as a word, the twin's store unchanged and its cache holding readbacks;
* `blockLargeElimAllowed_simC`: under `StageC` and the shape's denotation (con-ron's
  `blockLargeElimAllowed_cspec`'s precondition), `StageC` after and the twin's step a `PStep`
  (`readLevelM_pstep`) — for lane `indstaget`'s `grpAW_okC`, in place of the stub contract.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The model -/

/-- The verdict after the constructor count: the large shape, one member, at most one
constructor. -/
def bleT (lg k nc : Word) : Word :=
  if lg = 0 then 0 else if k ≠ 1 then 0 else if nc = 0 then 1 else if nc = 1 then 1 else 0

/-- After `block_shape_num_ctors`. -/
def bleK2 (pp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([bleT (rdW (m.arr64 IW) (pp + 7)) (rdW (m.arr64 IW) (pp + 1)) (r.headD 0)], m)

/-- After `lv_nz`. -/
def bleK1 (p : Prog) (n : Nat) (pp nb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then some ([1], m)
    else if nb ≠ 0 then some ([0], m)
    else bleK2 pp (callW p n "block_shape_num_ctors" [pp] m)

/-- **The model of `block_large_elim_allowed(p, nested)`** (body fuel `n`). -/
def bleW (p : Prog) (n : Nat) (m : Mem) (pp nb : Word) : Option (List Word × Mem) :=
  bleK1 p n pp nb (callW p n "lv_nz" [rdW (m.arr64 IW) (pp + 6)] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (pp nb : Word) (r : List Word)
theorem bleK1_nz (h : r.headD 0 ≠ 0) : bleK1 p n pp nb (some (r, m)) = some ([1], m) := by
  simp only [bleK1]; rw [ite_eq_left h]
theorem bleK1_nb (h1 : r.headD 0 = 0) (h2 : nb ≠ 0) : bleK1 p n pp nb (some (r, m)) = some ([0], m) := by
  simp only [bleK1]; rw [ite_eq_right (by simpa using h1), ite_eq_left h2]
theorem bleK1_go (h1 : r.headD 0 = 0) (h2 : nb = 0) : bleK1 p n pp nb (some (r, m)) =
    bleK2 pp (callW p n "block_shape_num_ctors" [pp] m) := by
  simp only [bleK1]; rw [ite_eq_right (by simpa using h1), ite_eq_right (by simpa using h2)]
theorem bleK2_some : bleK2 pp (some (r, m)) =
    some ([bleT (rdW (m.arr64 IW) (pp + 7)) (rdW (m.arr64 IW) (pp + 1)) (r.headD 0)], m) := rfl
end arms

attribute [ind_grind] bleK1_nz bleK1_nb bleK1_go bleK2_some

theorem ble_spec (p : Prog) (hp : p.lookup "block_large_elim_allowed" = some blockLargeElimAllowed)
    (n : Nat) (s₀ : St) (pp nb : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "block_large_elim_allowed" [pp, nb]
    ⦃fun r s' => LocEq s' s₀ ∧ bleW p n s₀.mem pp nb = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockLargeElimAllowed]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "lv_nz", callW_spec p n "block_shape_num_ctors"] <;>
    finish (gen := 20) [bleW, bleT, rdW_eq]

/-! ## The refinement -/

/-- `blockShapeNumCtorsW_ok` with the count's bound. -/
theorem bsncW_ok (n : Nat) (m : Mem) (q r : Word) (bs : BlockShape)
    (hq : decBS m q.toNat = some bs) (hb : q.toNat + 9 < 2 ^ 64)
    (hol : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l < 2 ^ 64)
    (hsmall : (m.arr64 IW).size < 2 ^ 64)
    (h : numCtorsOfW n m (rdW (m.arr64 IW) q) (rdW (m.arr64 IW) (q + 1)) = some r) :
    r = UInt64.ofNat bs.numCtors ∧ bs.numCtors < 2 ^ 64 := by
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).1
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (q.toNat + 1) = q + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [ofNat_toNat_word] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := by simp [hob]
  have hll : (UInt64.ofNat l).toNat = l := by simp [hlb]
  have hd2 : decPL m (decMS m) (UInt64.ofNat o).toNat (UInt64.ofNat l).toNat =
      some bs.members := by rw [hoo, hll]; exact hg
  have hbnd2 : (UInt64.ofNat o).toNat + (UInt64.ofNat l).toNat < 2 ^ 64 := by
    rw [hoo, hll]; exact hol o l ho hl
  rw [ho', hl'] at h
  rw [BlockShape.numCtors]
  exact numCtorsOfW_ok n m (UInt64.ofNat o) (UInt64.ofNat l) r bs.members hsmall hbnd2 hd2 h

theorem ofNat_eq_small {k c : Nat} (hk : k < 2 ^ 64) (hc : c < 2 ^ 64) :
    (UInt64.ofNat k = UInt64.ofNat c) ↔ k = c :=
  ⟨fun h => by
    have := congrArg UInt64.toNat h
    rwa [UInt64.toNat_ofNat_of_lt' hk, UInt64.toNat_ofNat_of_lt' hc] at this, fun h => h ▸ rfl⟩

/-- `bleT`'s verdict, decoded. -/
theorem bleT_dec {m0 : Mem} {lg : Word} {k nc : Nat} {b : Bool} (hk : k < 2 ^ 64) (hn : nc < 2 ^ 64)
    (hL : (lg != 0) = b) :
    decW0B m0 [bleT lg (UInt64.ofNat k) (UInt64.ofNat nc)] (b && k == 1 && (nc == 0 || nc == 1)) := by
  have e1 : (UInt64.ofNat k = 1) ↔ k = 1 := ofNat_eq_small hk (c := 1) (by decide)
  have e0 : (UInt64.ofNat nc = 0) ↔ nc = 0 := ofNat_eq_small hn (c := 0) (by decide)
  have e1' : (UInt64.ofNat nc = 1) ↔ nc = 1 := ofNat_eq_small hn (c := 1) (by decide)
  subst hL
  simp only [decW0B, List.headD_cons, bleT]
  by_cases g1 : lg = 0 <;> by_cases g2 : k = 1 <;> by_cases g3 : nc = 0 <;> by_cases g4 : nc = 1 <;>
    simp [g1, g2, g3, g4, e1, e0, e1'] <;> omega

/-- The lookups of `block_large_elim_allowed`. -/
structure BleProg (p : Prog) : Prop where
  node : p.lookup "lv_node" = some lvNode
  nz : p.lookup "lv_nz" = some lvNz
  nco : p.lookup "num_ctors_of" = some numCtorsOf
  nc : p.lookup "block_shape_num_ctors" = some blockShapeNumCtors
  ble : p.lookup "block_large_elim_allowed" = some blockLargeElimAllowed

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`block_large_elim_allowed`'s model refines `blockLargeElimAllowed`** under `StageR`, the
readback cache holding readbacks and the result sort's readback: the memory unchanged, the
verdict a `0`/`1` word, the twin's store unchanged and its cache holding readbacks after. -/
theorem bleW_ok {p : Prog} (P : BleProg p) {n : Nat} {m m' : Mem} {a : AState} {pp nb : Word}
    {r : List Word} {bs : BlockShape} (h : bleW p n m pp nb = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hrl : ReadLCOK a) {lv : ConLeche.Level} (hd : denoteL a.store.ls bs.resSort = some lv) :
    ∃ x a', (ConRon.Arena.blockLargeElimAllowed bs (nb != 0)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ m' = m ∧ decW0B m' r x ∧ a'.store = a.store ∧ ReadLCOK a' := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hdec, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨-, -, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  unfold bleW at h
  obtain ⟨⟨r1, m1⟩, c1, h⟩ := of_K h rfl
  obtain ⟨s1, hs1, -, hm1, hnz⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvNz_spec p P.node P.nz n _ (rdW (m.arr64 IW) (pp + 6))) c1
  simp only at hs1 hm1 hnz
  rw [hm1] at hs1; subst hs1
  have hlv := denoteL_lvR hS.1.arena.1 (decI (rdW (m.arr64 IW) (pp + 6))) lv (by rw [hrse]; exact hd)
  rw [word_decI _ _ hrs32 |>.mpr rfl] at hlv
  have hx := nzW_ok n m _ _ lv hlv hnz
  obtain ⟨X, hrun, hcX⟩ := readLevelM_run' a bs.resSort lv hd hrl
  have hSX := hS.withReadLC X
  have htw : ∀ (y : Bool) (aY : AState),
      ((if ConLeche.Level.isNeverZero lv then pure true
        else if (nb != 0) then pure false
        else pure (bs.large && bs.k == 1 && (bs.numCtors == 0 || bs.numCtors == 1)) : AM Bool).run
          { a with caches := { a.caches with readLC := X } } = .ok (y, aY)) →
      (ConRon.Arena.blockLargeElimAllowed bs (nb != 0)).run a = .ok (y, aY) := by
    intro y aY e
    simp only [ConRon.Arena.blockLargeElimAllowed, StateT.run_bind, hrun, except_ok_bind]
    exact e
  cases hnv : ConLeche.Level.isNeverZero lv
  · rw [hnv] at hx
    simp only [Bool.false_eq_true, ite_false] at hx
    by_cases hnb : nb = 0
    · rw [bleK1_go (h1 := hx) (h2 := hnb)] at h
      rcases n with _ | k
      · rw [callW_zero] at h; cases h
      obtain ⟨⟨r2, m2⟩, c2, h⟩ := of_K h rfl; rw [bleK2_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨s2, hs2, hm2, hnc⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (blockShapeNumCtorsW_spec p P.nco P.nc k _ pp) c2
      subst hm2
      simp only at hs2 hnc
      subst hs2
      obtain ⟨hnc', hncb⟩ := bsncW_ok k _ pp _ bs hdec (by omega)
        (fun o l h1 h2 => by have := hsrc o l h1 h2; omega) hsz hnc
      obtain ⟨-, -, -, -, -, hlarge, -⟩ := decBS_some (show decBS (truncM _) pp.toNat = some bs from hq)
      have hL := installIwB (k := 7) hlarge hsz
      have hK := partsShapeK hdec hq9
      have hkb : bs.k < 2 ^ 64 := by
        obtain ⟨o, l, -, hl, hg⟩ := decAt_some (decBS_some hdec).1
        obtain ⟨-, hlb⟩ := iwN_rdW hl (by omega)
        rw [BlockShape.k, decPL_length _ hg]; exact hlb
      refine ⟨_, _, htw _ _ (by
        simp only [hnv, Bool.false_eq_true, ite_false, show (nb != 0) = false by simpa using hnb]; rfl),
        hSX, rfl, ?_, rfl, hcX⟩
      simp only [show pp + UInt64.ofNat 7 = pp + 7 from rfl] at hL
      simp only [hK, hnc']
      exact bleT_dec hkb hncb hL
    · rw [bleK1_nb (h1 := hx) (h2 := hnb)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, _, htw _ _ (by
        simp only [hnv, Bool.false_eq_true, ite_false, show (nb != 0) = true by simpa using hnb, ite_true]; rfl),
        hSX, rfl, ⟨rfl, by decide⟩, rfl, hcX⟩
  · rw [hnv] at hx
    simp only [ite_true] at hx
    rw [bleK1_nz (h := by rw [hx]; decide)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨true, _, htw _ _ (by simp only [hnv, ite_true]; rfl), hSX, rfl, ⟨rfl, by decide⟩, rfl, hcX⟩

/-- **`block_large_elim_allowed` refines `blockLargeElimAllowed`, as a call**, under `StageR`, the
readback cache holding readbacks and the result sort's readback. -/
theorem blockLargeElimAllowed_sim {p : Prog} (P : BleProg p) (n : Nat) {m : Mem} {a : AState}
    {pp nb : Word} {bs : BlockShape} (hS : StageR dn vis fe m a)
    (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp) (hrl : ReadLCOK a)
    {lv : ConLeche.Level} (hd : denoteL a.store.ls bs.resSort = some lv) :
    Sim (callW p n "block_large_elim_allowed" [pp, nb] m)
      (ConRon.Arena.blockLargeElimAllowed bs (nb != 0)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ m' = m ∧ decW0B m' r x ∧ a'.store = a.store ∧
        ReadLCOK a') := by
  intro r m' e
  rcases n with _ | k
  · rw [callW_zero] at e; cases e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ble_spec p P.ble k _ pp nb) e
  exact bleW_ok P hW hS hq hsrc hrl hd

/-- **`block_large_elim_allowed` refines `blockLargeElimAllowed` under `StageC`** (for lane
`indstaget`'s `grpAW_okC`, replacing `IndInstallSpec39.blockLargeElimAllowed_spec`): from the
shape's denotation (con-ron's `blockLargeElimAllowed_spec`'s precondition) and `AbsOK` (the memory
is unchanged), `StageC` after, the twin's step a `PStep`, the verdict con-leche's. -/
theorem blockLargeElimAllowed_simC {p : Prog} (P : BleProg p) (n : Nat) {env : ConLeche.Env}
    {m : Mem} {a : AState} {pp nb : Word} {bs : BlockShape} (hC : StageC dn vis fe env m a)
    (hA : AbsOK m) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    {pP : ConLeche.BlockShape} (hsh : ConRon.Bridge.Inductives.dShape a.store bs = some pP) :
    Sim (callW p n "block_large_elim_allowed" [pp, nb] m)
      (ConRon.Arena.blockLargeElimAllowed bs (nb != 0)) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ m' = m ∧ decW0B m' r x ∧
        ConRon.Bridge.Inductives.PStep a a' ∧ x = ConLeche.blockLargeElimAllowed pP (nb != 0)) := by
  intro r m' e
  obtain ⟨hrl, -, -⟩ := hC.lzFacts
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh
  obtain ⟨x, a', hrun, hS', rfl, hd, -, -⟩ :=
    blockLargeElimAllowed_sim P n hC.stage hq hsrc hrl hsP r m' e
  obtain ⟨hs, hx⟩ := ConRon.Bridge.Inductives.blockLargeElimAllowed_spec bs pP (nb != 0) a a' x
    hC.check.state hC.check.caches.readL hsh hrun
  exact ⟨x, a', hrun, hC.of_pstep hS' hA hs, rfl, hd, hs, hx⟩

end

end L.Ind
