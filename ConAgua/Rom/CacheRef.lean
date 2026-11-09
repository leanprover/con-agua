module

public import ConAgua.Rom.CIReadSpec
public import ConAgua.Rom.CIReadRefW
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Rom.CIRead

@[expose] public section

/-!
# The cached ROM readers refine the twin (lane `ronsync2`)

The five readers the checks call read the startup cache `ROMC` (`CIRead.lean`): `rom_ci`,
`rom_cv`, `rom_expr_pin` return a cache word, `rom_basis_decls(k)` and `rom_and_pin()` copy a
cached `EREC` slice of record addresses into a fresh `IW` slice (`er_to_iw`). Under `StageT`, the
cache's denotation (`TwinOK.rom`, `RomDen.lean`) gives the twin's value, a no-op hit of its intern,
and the cache's words decode to it; a copied block decodes in the copy. `romRefs_of`: a program
with the readers' lookups (`RomCacheProg`) has all five refinements (`RomRefs`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- Word `w` of the cache. -/
abbrev rcW (m : Mem) (w : Word) : Word := rdW (m.arr64 ROMC) w

/-! ## The word models -/

section models
variable (p : Prog) (n : Nat)

/-- `rom_ci(id)`. -/
def cCiW (m : Mem) (id : Word) : Option (List Word × Mem) :=
  if 7 ≤ id then none else some ([rcW m (12 + id)], m)

/-- `rom_cv(id)`. -/
def cCvW (m : Mem) (id : Word) : Option (List Word × Mem) :=
  if 10 ≤ id then none else some ([rcW m (19 + id)], m)

/-- `rom_expr_pin(id)`. -/
def cExW (m : Mem) (id : Word) : Option (List Word × Mem) :=
  if 2 ≤ id then none else some ([rcW m (29 + id)], m)

/-- `rom_basis_decls(k)`. -/
def cBasisW (m : Mem) (k : Word) : Option (List Word × Mem) :=
  if 5 ≤ k then none else
  ntBW (callW p n "er_to_iw" [rcW m (2 * k), rcW m (2 * k + 1)] m) fun r m1 =>
    some ([r.headD 0, r.tail.headD 0], m1)

/-- `rom_and_pin()`. -/
def cAndW (m : Mem) : Option (List Word × Mem) :=
  ntBW (callW p n "er_to_iw" [rcW m 10, rcW m 11] m) fun r m1 =>
    some ([r.headD 0, r.tail.headD 0], m1)

end models

/-! ## The specs -/

section specs
variable (p : Prog) (hL : RomCacheProg p) (n : Nat) (s₀ : St)
include hL

/-- The common preamble: unfold the call and the body. -/
local macro "rc_pre " fd:term : tactic => `(tactic| (
  rw [invoke_eq _ $fd]
  simp only [callFn, romBasisDeclsL, romCiL, romCvL, romExprPinL, romAndPinL]))

theorem cCi_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_ci" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ cCiW s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rc_pre hL.rom_ci
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
    finish (gen := 30) (instances := 10000) [cCiW]

theorem cCv_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_cv" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ cCvW s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rc_pre hL.rom_cv
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
    finish (gen := 30) (instances := 10000) [cCvW]

theorem cEx_specW (id : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_expr_pin" [id]
    ⦃fun r s' => LocEq s' s₀ ∧ cExW s₀.mem id = some (r, s'.mem); ⊤⦄ := by
  rc_pre hL.rom_expr_pin
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
    finish (gen := 30) (instances := 10000) [cExW]

theorem cBasis_specW (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_basis_decls" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ cBasisW p n s₀.mem k = some (r, s'.mem); ⊤⦄ := by
  rc_pre hL.rom_basis_decls
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "er_to_iw"] <;>
    finish (gen := 30) (instances := 10000) [cBasisW, ntBW]

theorem cAnd_specW :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "rom_and_pin" []
    ⦃fun r s' => LocEq s' s₀ ∧ cAndW p n s₀.mem = some (r, s'.mem); ⊤⦄ := by
  rc_pre hL.rom_and_pin
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "er_to_iw"] <;>
    finish (gen := 30) (instances := 10000) [cAndW, ntBW]

end specs

/-! ## `er_to_iw` word by word -/

/-- **`er_to_iw` copies an `EREC` slice word by word**: the new `IW` slice at the old top holds the
slice's words, the pool only grew, and the copy is below the new top. -/
theorem erToIwW_get {n : Nat} {m m' : Mem} {o l : Word} {r : List Word}
    (h : erToIwW n m o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hrd : ∀ j < l.toNat, ∃ v, erecP m (o.toNat + j) = some v) :
    r = [rdW (m.arr64 CTL) 200, l] ∧
    (∀ j < l.toNat, iwA m' ((rdW (m.arr64 CTL) 200).toNat + j) = erecP m (o.toNat + j)) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (rdW (m.arr64 CTL) 200).toNat + l.toNat = iwTop m' ∧ iwTop m' ≤ (m'.arr64 IW).size := by
  have hol : o.toNat + l.toNat ≤ 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | hpos
    · have := o.toNat_lt; omega
    · obtain ⟨v, hv⟩ := hrd (l.toNat - 1) (by omega)
      have : o.toNat + (l.toNat - 1) < 2 ^ 64 := by
        rcases Nat.lt_or_ge (o.toNat + (l.toNat - 1)) (2 ^ 64) with h' | h'
        · exact h'
        · unfold erecP at hv; rw [ite_eq_right (by omega)] at hv; cases hv
      omega
  simp only [erToIwW] at h
  cases hal : allocW m l with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  rcases hcp : erCopyW (n - 1) m1 q o l with _ | m2 <;> simp only [hcp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m l
  have hR : ∀ a, erRd (allocMem m l) a = erRd m a := fun a => by
    simp only [allocMem, erRd]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by rw [tierA_EREC]; split <;> decide)]
  obtain ⟨hA, hS, hG⟩ := erCopyW_get (n - 1) _ _ _ _ _ hcp hol
    (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz)
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m l).trans (copy_frame hA (by rw [hS, hIW]))
  have htop : rdW (m2.arr64 CTL) 200 = q + l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr, ?_, ?_⟩
  · intro j hj
    obtain ⟨v, hv⟩ := hrd j hj
    simp only [iwA, aread_apply, hG]
    rw [ite_eq_left (by omega), hR, show q.toNat + j - q.toNat = j by omega]
    have e : (UInt64.ofNat (o.toNat + j)).toNat = o.toNat + j := by simp; omega
    have hv' : erecP m (UInt64.ofNat (o.toNat + j)).toNat = some v := by rw [e]; exact hv
    rw [(erRd_of_erecP hv').1, hv]
  · refine iwGrow_of_frame hfr (N := l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  · simp only [iwTop, htop, hsum]
  · simp only [iwTop, htop, hsum, hS]; omega

/-! ## The refinements -/

theorem mapM_ext_mem {α : Type} {f g : Nat → Option α} :
    ∀ (l : List Nat) (xs : List α), (∀ j ∈ l, ∀ x, f j = some x → g j = some x) →
      l.mapM f = some xs → l.mapM g = some xs
  | [], xs, _, hx => by simpa using hx
  | j :: js, xs, hfg, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx ⊢
    obtain ⟨y, hy, ys, hys, rfl⟩ := hx
    exact ⟨y, hfg j (by simp) y hy, ys,
      mapM_ext_mem js ys (fun i hi => hfg i (by simp [hi])) hys, rfl⟩

theorem mapM_some_mem {α : Type} {f : Nat → Option α} :
    ∀ (l : List Nat) (xs : List α), l.mapM f = some xs → ∀ j ∈ l, ∃ x, f j = some x
  | [], _, _, j, hj => by simp at hj
  | i :: is, xs, hx, j, hj => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx
    obtain ⟨y, hy, ys, hys, rfl⟩ := hx
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ⟨y, hy⟩
    · exact mapM_some_mem is ys hys j hj

/-- Word `c + w` of the cache, at a natural index. -/
theorem romcW_add (m : Mem) (c : Nat) (w : Word) :
    romcW m (c + w.toNat) = rcW m (UInt64.ofNat c + w) := by
  simp only [romcW, rcW]; congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add]; simp

/-- A copied block decodes in the copy: the cached slice `(q, l)` of tier-0 record addresses,
copied into `IW` at `o`, decodes as `basisDec` there. -/
theorem blk_copy {m m' : Mem} {q l : Word} {o : Nat} {cis : List IConstantInfo}
    (hb : erPL m (decCI (er0A m)) q.toNat l.toNat = some cis)
    (hget : ∀ j < l.toNat, iwA m' (o + j) = erecP m (q.toNat + j))
    (hg : IWGrow m m') (htop : o + l.toNat = iwTop m') (dn : NIdx → Option ConLeche.Name) :
    DecB (basisDec dn o l.toNat) m' cis := by
  have hx : ArrExt (er0A m) (erA (truncM m')) := fun i v hv => by
    rw [truncM_erA]; exact hg.erExt i v (er0A_sub m i v hv)
  simp only [DecB, basisDec, decPL, erPL] at hb ⊢
  refine mapM_ext_mem _ _ (fun j hj x hx' => ?_) hb
  replace hj := List.mem_range.mp hj
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hx' ⊢
  obtain ⟨p, hp, hc⟩ := hx'
  refine ⟨p, ?_, hx.decCI hc⟩
  have hp' : nat? (erA m) (q.toNat + j) = some p := (er0A_sub m).nat? hp
  rw [show iwN (truncM m') (o + j) = nat? (erA m) (q.toNat + j) from by
    simp only [iwN, nat?]; rw [truncM_iw_eq (by omega), hget j hj]; rfl]
  exact hp'

section refs
variable (p : Prog) (hL : RomCacheProg p)
include hL

/-- **`rom_ci(id)` refines `romCiT id`.** -/
@[refines ConRon.Arena.natA ConRon.Arena.iffA ConRon.Arena.iffIntroA ConRon.Arena.iffRecA
  ConRon.Arena.nonemptyA ConRon.Arena.nonemptyIntroA ConRon.Arena.nonemptyRecA]
theorem romCiRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomCiRef p dn vis fe := by
  intro id hid n m a r m' hT hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => cCiW mq id) (cCi_specW p hL n · id) hc
  unfold cCiW at hw
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨R, hm, ht⟩ := hT.twin.rom
  refine ⟨R.ci id.toNat, a, ht.ci _ hid a rfl, hT, IWGrow.refl _, ?_⟩
  have hd := hm.ci _ hid
  rw [romcW_add m 12 id] at hd
  simp only [decRCI, DecB, List.headD_cons, truncM_erA]
  exact (er0A_sub m).decCI hd

/-- **`rom_cv(id)` refines `romCvT id`.** -/
@[refines ConRon.Arena.propextA ConRon.Arena.choiceA ConRon.Arena.trueCvA ConRon.Arena.trueIntroCvA
  ConRon.Arena.trustCompilerA ConRon.Arena.boolCvA ConRon.Arena.reduceNatCvA ConRon.Arena.reduceBoolCvA
  ConRon.Arena.ofReduceNatA ConRon.Arena.ofReduceBoolA]
theorem romCvRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomCvRef p dn vis fe := by
  intro id hid n m a r m' hT hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => cCvW mq id) (cCv_specW p hL n · id) hc
  unfold cCvW at hw
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨R, hm, ht⟩ := hT.twin.rom
  refine ⟨R.cv id.toNat, a, ht.cv _ hid a rfl, hT, IWGrow.refl _, ?_⟩
  have hd := hm.cv _ hid
  rw [romcW_add m 19 id] at hd
  simp only [decRCV, DecB, List.headD_cons, truncM_erA]
  exact (er0A_sub m).decCV hd

/-- **`rom_expr_pin(id)` refines `romExprT id`.** -/
@[refines ConRon.Arena.reduceNatDeclPin ConRon.Arena.reduceBoolDeclPin]
theorem romExprPinRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomExprPinRef p dn vis fe := by
  intro id hid n m a r m' hT hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => cExW mq id) (cEx_specW p hL n · id) hc
  unfold cExW at hw
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨R, hm, ht⟩ := hT.twin.rom
  refine ⟨R.ex id.toNat, a, ht.ex _ hid a rfl, hT, IWGrow.refl _, ?_⟩
  have hd := hm.ex _ hid
  rw [romcW_add m 29 id] at hd
  simpa [decW0E] using hd

/-- A cached block read: `er_to_iw` of cache words `(i, i + 1)` holding block `k`'s slice. -/
theorem blockRead {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {n : Nat}
    {m m' : Mem} {a : AState} {r : List Word} {R : RomVals} {k : Nat} {w0 w1 : Word}
    (hT : StageT dn vis fe m a) (hb : erPL m (decCI (er0A m)) w0.toNat w1.toNat = some (R.blk k))
    (hc : callW p n "er_to_iw" [w0, w1] m = some (r, m')) :
    StageT dn vis fe m' a ∧ IWGrow m m' ∧ decRBlk dn m' [r.headD 0, r.tail.headD 0] (R.blk k) := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => erToIwW (n + 1) mq w0 w1)
    (fun s₀ => erToIw_specW p hL.iw_alloc hL.er_copy hL.er_to_iw (n + 1) s₀ w0 w1) hc
  have hrd : ∀ j < w1.toNat, ∃ v, erecP m (w0.toNat + j) = some v := by
    intro j hj
    simp only [erPL] at hb
    obtain ⟨x, hx⟩ := mapM_some_mem _ _ hb j (List.mem_range.mpr hj)
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, nat?, Option.map_eq_some_iff] at hx
    obtain ⟨_, ⟨v, hv, -⟩, -⟩ := hx
    exact ⟨v, er0A_sub m _ _ hv⟩
  obtain ⟨hr, hget, hg, hfr, htop, hroom⟩ :=
    erToIwW_get hw hT.stage.iw.iwSize hT.stage.iw.ctl hrd
  subst hr
  have hS' : StageR vis fe m' a := ⟨CheckR.frame_iw hfr hT.stage.check, IWOK.of_iw hfr hT.stage.iw hroom⟩
  refine ⟨hT.of_iw hS' hfr, hg, ?_, rfl⟩
  simpa using blk_copy hb hget hg htop dn

/-- **`rom_basis_decls(k)` refines `BasisKind.decls`.** -/
@[refines_part ConRon.Arena.BasisKind.decls "the startup cache"]
theorem romBasisRef_of (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomBasisRef p dn vis fe := by
  intro k hk n m a r m' hT hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => cBasisW p n mq k) (cBasis_specW p hL n · k) hc
  unfold cBasisW at hw
  rw [ite_eq_right (by rw [UInt64.le_iff_toNat_le]; simp; omega)] at hw
  obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨R, hm, ht⟩ := hT.twin.rom
  have hb := hm.blk k.toNat (by omega)
  have e0 : romcW m (2 * k.toNat) = rcW m (2 * k) := by
    simp only [romcW, rcW]; congr 1
  have e1 : romcW m (2 * k.toNat + 1) = rcW m (2 * k + 1) := by
    simp only [romcW, rcW]; congr 1; apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat]; simp
  rw [e0, e1] at hb
  obtain ⟨hT', hg, hd⟩ := blockRead p hL hT hb h1
  have hrun := ht.blk k.toNat (by omega) a rfl
  simp only [romBlkT, hk, ↓reduceIte] at hrun
  exact ⟨R.blk k.toNat, a, hrun, hT', hg, hd⟩

/-- **`rom_and_pin()` refines `andPinDecls`.** -/
@[refines_part ConRon.Arena.andPinDecls "the startup cache"]
theorem romAndPinRef_of' (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) :
    RomAndPinRef p dn vis fe := by
  intro n m a r m' hT hc
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  have hw := callW_model (M := fun mq => cAndW p n mq) (cAnd_specW p hL n ·) hc
  unfold cAndW at hw
  obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨R, hm, ht⟩ := hT.twin.rom
  have hb := hm.blk 5 (by omega)
  obtain ⟨hT', hg, hd⟩ := blockRead p hL hT hb h1
  have hrun := ht.blk 5 (by omega) a rfl
  simp only [romBlkT, show ¬ (5 < 5) by omega, ↓reduceIte] at hrun
  exact ⟨R.blk 5, a, hrun, hT', hg, hd⟩

/-- **The cached readers refine the twin.** -/
theorem romRefs_of : RomRefs p :=
  ⟨romCiRef_of p hL, romCvRef_of p hL, romExprPinRef_of p hL, romBasisRef_of p hL,
    romAndPinRef_of' p hL⟩

end refs

end L.Rom
