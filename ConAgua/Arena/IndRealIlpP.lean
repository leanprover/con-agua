module

public import ConAgua.Arena.IndRealMemo
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.TeleLift
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.TeleLift
import all ConAgua.Arena.Walk
import all ConAgua.Arena.WalkLift
import ConAgua.L.WordOff
import ConAgua.Arena.Inst1Refine

@[expose] public section

/-!
# `inst_pis_at_lift` under the stage relation and the walk memos (lane `indproofs4`, helper `ilp`)

`inst_pis_at_lift(f, off, len, e)` (lane `whnf3`'s `instPisAtLiftL`, `TeleLift.lean`): for each
argument of the `IW` slice, the tag test (`(0, 0)` at a non-`∀`), the binder view (`e_view`), and
`instantiate1_lift_fast(f, body, a, 0)`. The recipe of `IndReal.lean`:

* **The model** `ipalF := callF ipalP "inst_pis_at_lift"` over `ipalP` (the function, `e_view`,
  `IndRealMemo.lean`'s `i1lP`); write set `i1lA`/`i1lC` (the walk's only), so the `IW` pool and
  the slice's decoding are untouched.
* **The loop** a named block (`ipalLoop`) with a recursive model (`ipalGoW`), the walk's calls
  through `i1lF`.
* **`ipalF_ok`**: `RelW ipalF [f, o, l, e] (StageR ∧ AbsOK ∧ decHL) (instPisAtLift …)
  (KeepPost … decOE ∧ AbsOK)`, by `i1lF_ok` per step (replaced `IndStubs.instPisAtLift_spec`, deleted,
  whose `stubM` statement cannot carry the walk memos `AbsOK`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The program and the model -/

/-- The function and `e_view`. -/
def ipalHead : Prog := [("inst_pis_at_lift", instPisAtLiftL), ("e_view", eView)]

/-- The function, `e_view`, and `instantiate1_lift_fast`'s program. -/
def ipalP : Prog := ipalHead ++ i1lP

/-- The functions `inst_pis_at_lift` reaches. -/
def ipalPFns : List FnName := ["inst_pis_at_lift", "e_view"] ++ i1lPFns

theorem ipalP_closed : closedA ipalP i1lA i1lC ipalPFns = true := by decide +kernel

/-- The program bundle. -/
abbrev IpalF (p : Prog) : Prop := ProgHas p ipalP

theorem IpalF.i1l {p : Prog} (hp : IpalF p) : I1lF p := ProgHas.right (l₁ := ipalHead) hp

noncomputable section

l_model ipal_specW (p : Prog) (hp : IpalF p)
  fns [hp.get "inst_pis_at_lift" ↦ ipalW list]
  specs [eView_spec p (hp.get "e_view") n, i1lF_spec p (IpalF.i1l hp) n]
  grind [arena_grind]

end

/-- **The model of `inst_pis_at_lift`** (program- and fuel-free). -/
noncomputable def ipalF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ipalP "inst_pis_at_lift" m args

theorem ipalF_spec (p : Prog) (hp : IpalF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_pis_at_lift" args
    ⦃fun r s' => LocEq s' s₀ ∧ ipalF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ipalP_closed (hp.agree ipalPFns) (by decide) n s₀ args

/-- `inst_pis_at_lift` writes only `instantiate1_lift_fast`'s `i1lA`, `i1lC`. -/
theorem ipalF_frame {m m' : Mem} {args r : List Word} (h : ipalF m args = some (r, m')) :
    MemFrame i1lA i1lC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ipalP_closed (by decide) (run_of_callW hc)).1

/-- A model run is `ipalW` at some fuel. -/
theorem ipalF_W {m m' : Mem} {f o l e : Word} {r : List Word} (h : ipalF m [f, o, l, e] = some (r, m')) :
    ∃ n, ipalW n m f o l e = some (r, m') := by
  obtain ⟨n, hc⟩ := callF_run h
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (ipal_specW ipalP (ProgHas.refl _) n _ f o l e) hc
  rw [hs'] at hW
  exact ⟨n, hW⟩

/-! ## The relation to the twin -/

theorem i1lA_iw : (IW : TieredArray) ∉ i1lA := by decide

/-- **The loop refines `instPisAtLift` on the rest of the slice.** -/
theorem ipalGoW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f o l : Word)
    (xs : List EIdx) : ∀ (n : Nat) (m m' : Mem) (a : AState) (h k : Word) (r : List Word),
    ipalW.loop1 n m f o l h k = some (r, m') → StageR vis fe m a → AbsOK m → H h →
    k.toNat ≤ l.toNat → decHL m o.toNat l.toNat = some xs →
    ∃ x a', (instPisAtLift f.toNat (xs.drop k.toNat) (decI h)).run a = .ok (x, a') ∧
      KeepPost vis fe decOE m m' a' r x ∧ AbsOK m' := by
  have hxl : ∀ m, decHL m o.toNat l.toNat = some xs → xs.length = l.toNat := fun m h => decHL_length m h
  intro n
  induction n with
  | zero => intro m m' a h k r hW; simp [ipalW.loop1] at hW
  | succ n ih =>
    intro m m' a h k r hW hS hA hh hkl hdec
    have hlen := hxl m hdec
    by_cases hk : k < l
    · have hk' : k.toNat < l.toNat := UInt64.lt_iff_toNat_lt.mp hk
      obtain ⟨w, hw, hwlt, hwx⟩ := decHL_word hdec hS.iw.iwSize k.toNat hk'
      rw [L.toUInt64_toNat] at hw
      have hdrop : xs.drop k.toNat = xs[k.toNat] :: xs.drop (k.toNat + 1) :=
        List.drop_eq_getElem_cons (by omega)
      have hxk : xs[k.toNat] = decI w := by
        rw [List.getElem?_eq_getElem (by omega)] at hwx; exact Option.some.inj hwx
      by_cases h6 : tagW h ≠ 6
      · rw [ipalW.loop1.arm1 n m f o l h k hk h6] at hW
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
        refine ⟨none, a, ?_, ⟨hS, IWGrow.refl _, rfl⟩, hA⟩
        have ht : ¬ ((decI h : EIdx).tag == ETag.forallE) = true := by
          rw [decI_tag_forallE_beq h hh]; simpa using h6
        rw [hdrop]
        simp only [ConRon.Arena.instPisAtLift, ht, ite_false, Bool.false_eq_true]; rfl
      by_cases hv : eViewW m h = []
      · rw [ipalW.loop1.abort1 n m f o l h k hk (by simpa using h6) hv] at hW; cases hW
      have he6 : tagW h = 6 := by simpa using h6
      obtain ⟨v, hvw, hvr⟩ := eViewW_ok m a hS.check.arena.base h hv
      have ht : (decE h).tag = ETag.forallE := by
        have h1 : ((decI h : EIdx).tag == ETag.forallE) = true := by
          rw [decI_tag_forallE_beq h hh, he6]; decide
        exact beq_iff_eq.mp h1
      obtain ⟨ty, bd, rfl⟩ := EStore.view_forall a.store (decE h) ht v hvw
      obtain ⟨g, vt, hvl⟩ : ∃ g vt, eViewW m h = g :: vt := by
        cases e : eViewW m h with
        | nil => exact absurd e hv
        | cons g vt => exact ⟨g, vt, rfl⟩
      rw [hvl] at hvr
      simp only [ViewR, L.getD_one] at hvr
      obtain ⟨-, -, -, hy1, hy2⟩ := hvr
      have hy2' : (vt.tail.headD 0).toNat < 2 ^ 32 := by simpa using hy1
      have hy3 : decE (vt.tail.headD 0) = bd := by simpa using hy2
      have hbind : a.store.viewBind (decE h) = some (ty, bd) :=
        EStore.viewBind_of_view _ _ ht ty bd hvw
      rcases hst : i1lF m [f, (eViewW m h).tail.tail.headD 0, rdW (m.arr64 IW) (o + k), 0] with _ | ⟨rb, m1⟩
      · rw [ipalW.loop1.arm2 n m f o l h k hk he6 hv, hst, ipalW.k_instantiate1_lift_fast.none] at hW; cases hW
      rw [ipalW.loop1.arm2 n m f o l h k hk he6 hv, hst, ipalW.k_instantiate1_lift_fast.arm1] at hW
      rw [hvl, hw] at hst
      simp only [List.tail_cons] at hst
      obtain ⟨x1, a1, hrun1, ⟨hS1, hg1, hlt1, hdec1⟩, hA1⟩ :=
        i1lF_ok dn vis fe f (vt.tail.headD 0) w 0 hy2' hwlt m m1 a rb hst ⟨hS, hA⟩
      have hfr := i1lF_frame hst
      have hdec' : decHL m1 o.toNat l.toNat = some xs := by
        have hI : m1.arr64 IW = m.arr64 IW := hfr.arr IW i1lA_iw (by decide)
        simp only [decHL, iwA, hI]; exact hdec
      have hk1 : (k + 1).toNat = k.toNat + 1 := L.toNat_add_one_of_lt (by have := l.toNat_lt; omega)
      obtain ⟨x3, a3, hrun3, ⟨hS3, hg3, hout3⟩, hA3⟩ :=
        ih m1 m' a1 (rb.headD 0) (k + 1) r hW hS1 hA1 hlt1 (by omega) hdec'
      refine ⟨x3, a3, ?_, ⟨hS3, hg1.trans hg3, hout3⟩, hA3⟩
      have htag : ((decI h : EIdx).tag == ETag.forallE) = true := by
        rw [decI_tag_forallE_beq h hh, he6]; decide
      rw [hdrop, hxk]
      simp only [ConRon.Arena.instPisAtLift, htag, ite_true, StateT.run_bind]
      rw [show (decI h : EIdx) = decE h from rfl, L.Arena.viewBind_run, except_ok_bind, hbind]
      simp only [StateT.run_bind]
      rw [show (decI (vt.tail.headD 0) : EIdx) = bd from hy3, show (0 : Word).toNat = 0 from rfl] at hrun1
      rw [hrun1]
      simp only [except_ok_bind]
      rw [← hdec1, ← hk1]
      exact hrun3
    · rw [ipalW.loop1.arm3 n m f o l h k hk] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hkl' : k.toNat = l.toNat := by
        have := mt UInt64.lt_iff_toNat_lt.mpr hk; omega
      have hnil : xs.drop k.toNat = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨some (decI h), a, ?_, ⟨hS, IWGrow.refl _, rfl, hh, rfl⟩, hA⟩
      rw [hnil]; rfl

/-- **`inst_pis_at_lift` refines `instPisAtLift` under the stage relation and the walk memos**
(replaced the deleted `IndStubs.instPisAtLift_spec`); the memos are well formed after. -/
theorem ipalF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f o l e : Word)
    (he : H e) (xs : List EIdx) :
    RelW ipalF [f, o, l, e]
      (fun m a => StageR vis fe m a ∧ AbsOK m ∧ decHL m o.toNat l.toNat = some xs)
      (instPisAtLift f.toNat xs (decI e))
      (fun m m' a r x => KeepPost vis fe decOE m m' a r x ∧ AbsOK m') := by
  intro m m' a r h ⟨hS, hA, hdec⟩
  obtain ⟨n, hW⟩ := ipalF_W h
  rcases n with _ | n
  · simp [ipalW] at hW
  rw [ipalW.arm1] at hW
  have := ipalGoW_ok dn vis fe f o l xs (n + 1) m m' a e 0 r hW hS hA he (by simp) hdec
  simpa using this

end L.Ind
