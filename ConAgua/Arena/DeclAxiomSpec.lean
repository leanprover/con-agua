module

public import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclReduceSpec
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclAxiomSpec3
import all ConAgua.Arena.DeclArmsNat
import Std.Tactic.BVDecide.Normalize.Bool
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The `ofReduce*` axioms: `of_reduce_ax_ok(vis, q)` refines `ofReduceAxOk` (lane `decls3`)

The pinned `Eq` basis (`find_is` against `rom_ci(0)`), the element inductive and the stored reduce
opaque (`reduce_elem_ok`, `reduce_stored_ok`), the pin (`of_reduce_pin_a`, `matches_pin`). L
change: the axiom's name word loaded once into a local (it was loaded inside two call arguments).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The lookups of `of_reduce_ax_ok`. -/
structure OraProg (p : Prog) : Prop where
  red : RedProg p
  ora : p.lookup "of_reduce_ax_ok" = some ofReduceAxOkL
  oro : p.lookup "of_reduce_op" = some ofReduceOpL
  orp : p.lookup "of_reduce_pin_a" = some ofReducePinAL
  eqs : p.lookup "eq_stored" = some eqStoredL

/-- **The model of `of_reduce_ax_ok(vis, q)`.** -/
l_model ora_specW (p : Prog) (h : OraProg p)
  fns [h.ora ↦ oraW list]
  specs [oro_specW p h.red.pa h.oro n, callW_spec p n "eq_stored", callW_spec p n "reduce_elem_ok",
    callW_spec p n "reduce_stored_ok", callW_spec p n "of_reduce_pin_a",
    callW_spec p n "matches_pin"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **`of_reduce_ax_ok(vis, q)` refines `ofReduceAxOk`** at the model level. -/
theorem oraW_ok {p : Prog} (h : OraProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal} (hW : oraW p n m vis q = some (r, m')) (hS : StageR vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    ∃ b a', (ofReduceAxOk fe cv).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hq
  cases n with
  | zero => simp [oraW.eq_1] at hW
  | succ n =>
  rw [oraW.arm1, erecKind hwn] at hW
  simp only [ofReduceAxOk, hname]
  -- the operation
  rcases e1 : oroW m wn with _ | ⟨r1, m1⟩
  · rw [e1, oraW.k_of_reduce_op.none] at hW; cases hW
  obtain ⟨hm1, hl1, hrun1⟩ := oroW_ok e1 hS.check.pins hwnl
  subst m1
  rw [e1, oraW.k_of_reduce_op.arm1] at hW
  simp only [StateT.run_bind, hrun1, L.Arena.except_ok_bind]
  -- the pinned `Eq`
  rcases e2 : callW p n "eq_stored" [vis] m with _ | ⟨r2, m2⟩
  · rw [e2, oraW.k_eq_stored.none] at hW; cases hW
  obtain ⟨hm2, hrun2, -⟩ := eqs_call h.red h.eqs e2 hS
  subst m2
  rw [e2] at hW
  simp only [hrun2, L.Arena.except_ok_bind]
  by_cases z2 : r2.headD 0 = 0
  · rw [oraW.k_eq_stored.arm1 p n vis q _ _ r2 m z2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    simp only [z2, bne_self_eq_false, Bool.not_false, ↓reduceIte]
    exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  rw [oraW.k_eq_stored.arm2 p n vis q _ _ r2 m z2] at hW
  simp only [show (r2.headD 0 != 0) = true by simpa using z2, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  -- the element inductive
  rcases e3 : callW p n "reduce_elem_ok" [vis, r1.headD 0] m with _ | ⟨r3, m3⟩
  · rw [e3, oraW.k_reduce_elem_ok.none] at hW; cases hW
  obtain ⟨s3, hs3, -, hok3, hS3, hg3, hd3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (reduceElemOk_refines p h.red vis fe (r1.headD 0) hl1 n ⟨m, Locals.init []⟩ a hS) e3
  subst hs3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [e3] at hW
  simp only [StateT.run_bind, hrun3, L.Arena.except_ok_bind]
  generalize AM.res (reduceElemOk fe (decI (r1.headD 0))) a = b3 at hd3
  generalize AM.st (reduceElemOk fe (decI (r1.headD 0))) a = a3 at hS3
  by_cases z3 : r3.headD 0 = 0
  · rw [oraW.k_reduce_elem_ok.arm1 p n vis q _ _ r3 _ z3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : b3 = false := by rw [← hd3.1, z3]; rfl
    subst this
    exact ⟨false, a3, rfl, hS3, hg3, by simp [decW0B]⟩
  rw [oraW.k_reduce_elem_ok.arm2 p n vis q _ _ r3 _ z3] at hW
  have : b3 = true := by rw [← hd3.1]; simpa using z3
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  -- the stored reduce opaque
  rcases e4 : callW p n "reduce_stored_ok" [vis, r1.headD 0] s3.mem with _ | ⟨r4, m4⟩
  · rw [e4, oraW.k_reduce_stored_ok.none] at hW; cases hW
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hd4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (reduceStoredOk_refines p h.red vis fe (r1.headD 0) hl1 n ⟨s3.mem, Locals.init []⟩ a3 hS3) e4
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  rw [e4] at hW
  simp only [StateT.run_bind, hrun4, L.Arena.except_ok_bind]
  generalize AM.res (reduceStoredOk fe (decI (r1.headD 0))) a3 = b4 at hd4
  generalize AM.st (reduceStoredOk fe (decI (r1.headD 0))) a3 = a4 at hS4
  by_cases z4 : r4.headD 0 = 0
  · rw [oraW.k_reduce_stored_ok.arm1 p n q _ r4 _ z4] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : b4 = false := by rw [← hd4.1, z4]; rfl
    subst this
    exact ⟨false, a4, rfl, hS4, hg3.trans hg4, by simp [decW0B]⟩
  rw [oraW.k_reduce_stored_ok.arm2 p n q _ r4 _ z4] at hW
  have : b4 = true := by rw [← hd4.1]; simpa using z4
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  -- the pin
  rcases e5 : callW p n "of_reduce_pin_a" [wn] s4.mem with _ | ⟨r5, m5⟩
  · rw [e5, oraW.k_of_reduce_pin_a.none] at hW; cases hW
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hd5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (ofReducePinA_refines (p := p) (hpa := h.red.pa) (n := n) (s₀ := ⟨s4.mem, Locals.init []⟩)
      (a₀ := a4) (hS := hS4) (hc := hwnl) (hR := h.red.rom) (hp := h.orp)) e5
  subst hs5
  have hrun5 := AM.run_of_ok _ _ hok5
  rw [e5, oraW.k_of_reduce_pin_a.arm1] at hW
  have hg05 := hg3.trans (hg4.trans hg5)
  rcases e6 : callW p n "matches_pin" [q, r5.headD 0] s5.mem with _ | ⟨r6, m6⟩
  · rw [e6, oraW.k_matches_pin.none] at hW; cases hW
  rw [e6, oraW.k_matches_pin.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨rfl, hrun6, hd6⟩ := mpW_ok (a := AM.st (ofReducePinA (decI wn)) a4) (mp_callR h.red e6)
    hS5.iw.erSize (ArrExt.decCV (L.Ind.IWGrow.ext hg05) hq) (decRCV_get hd5)
  refine ⟨_, _, ?_, hS5, hg05, by simpa [decW0B] using hd6⟩
  simp only [StateT.run_bind, hrun5, L.Arena.except_ok_bind]
  exact hrun6

/-- **`of_reduce_ax_ok(vis, q)` refines `ofReduceAxOk`** (through the ROM readers' refinements). -/
@[refines ConRon.Arena.ofReduceAxOk]
theorem ofReduceAxOk_refines (p : Prog) (h : OraProg p) (dn : NIdx → Option ConLeche.Name)
    (_hdn : DnInj dn) (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "of_reduce_ax_ok" [vis, q]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (ofReduceAxOk fe cv) (KeepPost vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hq⟩
  refine triple_post (ora_specW p h n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := oraW_ok h hm hS hq
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

end L.Arena
