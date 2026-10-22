import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.PinsNatOp

/-!
# `whnf_core_step` and its `app` arm refine `whnfCoreStep`

The step dispatches on the handle's tag after the view's checks; the `app` arm (`whnf_core_app`,
`WhnfCore.lean`) walks the spine (`get_app_spine`), normalises the head (the knot's `whnfCore`
slot), takes the reduct's own spine (`head_and_args`) and runs the batched β/ι walk (`whnf_app`),
then puts the stack top back. Twin: `whnfCoreStep` (`Arena/Core.lean:2351`), its `.app` clause
named `whnfCoreAppT` here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The `app` arm -/

/-- The twin's `.app` clause of `whnfCoreStep`. -/
def whnfCoreAppT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool) (depth : Nat)
    (e : EIdx) : AM WhnfStep := do
  let sp ← getAppSpine coreWalkFuel e
  let v ← r.whnfCore cheap depth sp.1
  let same := v == sp.1
  let hv ← headAndArgs v
  whnfApp mode r fe depth v hv.1 hv.2 same sp.2.1 sp.2.2 0

/-- The model of `whnf_core_app2`. -/
def coreApp2W (p : Prog) (n : Nat) (m : Mem) (mode vis d v h so sn : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "head_and_args" [v] m with
  | none => none
  | some (r₃, m₃) =>
    match callW p n "whnf_app" [mode, vis, d, v, r₃.headD 0, r₃.tail.headD 0, r₃.tail.tail.headD 0,
        Cmp.evalW .eq v h, so, sn, 0] m₃ with
    | none => none
    | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄.set64 CTL 136 (rdW (m.arr64 CTL) 136))

theorem coreApp2W_some (p : Prog) (n : Nat) (m m₃ m₄ : Mem) (mode vis d v h so sn : Word)
    (r₃ r₄ : List Word) (h₃ : callW p n "head_and_args" [v] m = some (r₃, m₃))
    (h₄ : callW p n "whnf_app" [mode, vis, d, v, r₃.headD 0, r₃.tail.headD 0, r₃.tail.tail.headD 0,
        Cmp.evalW .eq v h, so, sn, 0] m₃ = some (r₄, m₄)) :
    coreApp2W p n m mode vis d v h so sn =
      some (r₄.headD 0, r₄.tail.headD 0, m₄.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  simp only [coreApp2W, h₃, h₄]

theorem coreApp2_spec (p : Prog) (hp : p.lookup "whnf_core_app2" = some whnfCoreApp2L) (n : Nat)
    (s₀ : St) (mode vis d v h so sn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core_app2" [mode, vis, d, v, h, so, sn]
    ⦃fun r s' => LocEq s' s₀ ∧
      coreApp2W p n s₀.mem mode vis d v h so sn = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s'.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, whnfCoreApp2L]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "whnf_app", callW_spec p n "head_and_args"] <;>
  simp_all [coreApp2W, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, rdW, CTL, size_set64] <;>
  (congr 1; rw [Array.getElem?_eq_getElem]; rfl)

/-- The model of `whnf_core_app`. -/
def coreAppW (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "get_app_spine" [e] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "whnf_core" [mode, cheap, vis, d, r₁.headD 0] m₁ with
    | none => none
    | some (r₂, m₂) =>
      match callW p n "whnf_core_app2" [mode, vis, d, r₂.headD 0, r₁.headD 0, r₁.tail.headD 0,
          r₁.tail.tail.headD 0] m₂ with
      | none => none
      | some (r₄, m₄) =>
        some (r₄.headD 0, r₄.tail.headD 0, m₄.set64 CTL 136 (rdW (m.arr64 CTL) 136))

theorem coreAppW_some (p : Prog) (n : Nat) (m m₁ m₂ m₄ : Mem) (mode cheap vis d e : Word)
    (r₁ r₂ r₄ : List Word)
    (h₁ : callW p n "get_app_spine" [e] m = some (r₁, m₁))
    (h₂ : callW p n "whnf_core" [mode, cheap, vis, d, r₁.headD 0] m₁ = some (r₂, m₂))
    (h₄ : callW p n "whnf_core_app2" [mode, vis, d, r₂.headD 0, r₁.headD 0, r₁.tail.headD 0,
          r₁.tail.tail.headD 0] m₂ = some (r₄, m₄)) :
    coreAppW p n m mode cheap vis d e =
      some (r₄.headD 0, r₄.tail.headD 0, m₄.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  simp only [coreAppW, h₁, h₂, h₄]

theorem coreApp_spec (p : Prog) (hp : p.lookup "whnf_core_app" = some whnfCoreAppL) (n : Nat)
    (s₀ : St) (mode cheap vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core_app" [mode, cheap, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      coreAppW p n s₀.mem mode cheap vis d e = some (r.headD 0, r.tail.headD 0, s'.mem) ∧
      (136 : Word).toNat < (s'.mem.arr64 CTL).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, whnfCoreAppL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "get_app_spine", callW_spec p n "whnf_core", callW_spec p n "whnf_core_app2"] <;>
  simp_all [coreAppW, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, rdW, CTL, size_set64] <;>
  (congr 1; rw [Array.getElem?_eq_getElem]; rfl)


/-! ## Stack writers keep the relation; slices below the top survive -/

theorem CoreS.frame_stk {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b = SPN)
    (hC : ∀ x ∈ C, x = 136) : CoreS dn m' a vis fe M eb := by
  have aA : ∀ lo hi : Nat, hi ≤ 144 → AvoidA lo hi A := fun lo hi h b hb => by
    have := hA b hb; simp only [SPN, ArrId] at this ⊢; omega
  have aC : ∀ lo hi : Nat, hi ≤ 136 → AvoidC lo hi C := fun lo hi h x hx => by
    have := hA; rw [hC x hx]; right; simpa using h
  exact ⟨⟨ArenaR.frame_ext A C (fun b hb => by rw [hA b hb]; decide)
      (fun x hx => by rw [hC x hx]; decide) m m' hf a hS.arena.1,
      DerR.frameM A C m m' hf (fun b hb => .inr (by rw [hA b hb]; decide)) a hS.arena.2⟩,
    hS.core.frame (aA 96 128 (by decide)) (aC 96 128 (by decide)) hf,
    hS.pins.congr (hf.1 PINS (fun h => by have := hA _ h; simp [PINS, SPN] at this) (by decide)),
    hS.env.frame (aA 132 144 (by decide)) (aC 128 136 (by decide)) hf,
    hS.readL, hS.readLs, hS.nwf, hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn⟩

theorem SpineR.keep {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (hsz : (m'.arr64 SPN).size = (m.arr64 SPN).size)
    (hk : ∀ i : Word, i < spTop m → spW m' i = spW m i)
    (htop : off.toNat + cnt.toNat ≤ (spTop m).toNat) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m' off cnt xs := by
  have hb := h.bound
  have hlt : ∀ i : Nat, i < cnt.toNat → off + i.toUInt64 < spTop m := by
    intro i hi
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat']
    have : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨h.size, hsz ▸ hb, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hk _ (hlt i hi)]; exact h.lt i hi
  · rw [hk _ (hlt i (h.size ▸ hi))]; exact h.get i hi


/-! ## `whnf_core_app2` refines the reduct's spine and the β/ι walk -/

/-- The twin's second half of the `.app` clause. -/
def whnfCoreApp2T (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (v h : EIdx)
    (args nodes : Array EIdx) : AM WhnfStep := do
  let hv ← headAndArgs v
  whnfApp mode r fe depth v hv.1 hv.2 (v == h) args nodes 0

theorem evalW_eq_ne (v h : Word) (hv : HW v) (hh : HW h) :
    (Cmp.evalW .eq v h != 0) = (decE v == decE h) := by
  rw [decE_eq, decE_eq, decI_beq v h hv hh]
  by_cases e : v = h <;> simp [Cmp.evalW, Cmp.eval, e]

/-- The top restored after a run that kept everything below the old top. -/
theorem StackKept.restore {m m₁ : Mem} (hk : ∀ i : Word, i < spTop m → spW m₁ i = spW m i)
    (hsz : (m₁.arr64 SPN).size = (m.arr64 SPN).size)
    (h136 : (136 : Word).toNat < (m₁.arr64 CTL).size) :
    StackKept m (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)) := by
  have hspn : (m₁.set64 CTL 136 (rdW (m.arr64 CTL) 136)).arr64 SPN = m₁.arr64 SPN :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨?_, by rw [hspn, hsz], fun i hi => by simp only [spW, hspn]; exact hk i hi⟩
  simp only [spTop, rdW_set64]
  have : (136 : Word).toNat = 136 := rfl
  simp only [this] at h136
  simp; intro h; omega

section app2
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **`whnf_core_app2` refines the second half of the `.app` clause**, the spine's arguments and
nodes the slices `(so, sn)`, `(so + sn, sn)` below the top. -/
theorem coreApp2_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v h so sn : Word) (args nodes : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v) (hh : HW h)
    (har : SpineR s₀.mem so sn args) (hno : SpineR s₀.mem (so + sn) sn nodes)
    (hlo : so.toNat + sn.toNat + sn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 2) "whnf_core_app2" [mode, vis, d, v, h, so, sn]
      (whnfCoreApp2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE h)
        args nodes) decStep s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW, h136⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (coreApp2_spec p hp.capp2 (n + 1) s₀ mode vis d v h so sn)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  simp only [coreApp2W] at hW
  cases h3 : callW p (n + 1) "head_and_args" [v] s.mem with
  | none => simp [h3] at hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  simp only [h3] at hW
  cases h4 : callW p (n + 1) "whnf_app" [mode, vis, d, v, r₃.headD 0, r₃.tail.headD 0,
      r₃.tail.tail.headD 0, Cmp.evalW .eq v h, so, sn, 0] m₃ with
  | none => rw [h4] at hW; simp at hW
  | some q =>
  obtain ⟨r₄, m₄⟩ := q
  simp only [h4, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  obtain ⟨t₃, ht₃, -, hf₃, hg₃, hhw, ho3, htop3, xs, hha, hxs⟩ := triple_of_callW
    (headAndArgs_refines p (n + 1) s a₀ hS.arena.1 v hv) h3
  rw [ht₃] at hf₃ hg₃ htop3 hxs
  have hS₃ := hS.frame_stk hf₃ (by simp) (by simp)
  obtain ⟨hgt, hgsz, hgk⟩ := hg₃
  have har₃ := har.keep hgsz hgk (by omega) hS.spn
  have hno₃ := hno.keep hgsz hgk (by
    have hb := har.bound; have := hS.spn
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega) hS.spn
  have hvo : spTop m₃ = r₃.tail.headD 0 + r₃.tail.tail.headD 0 := by rw [htop3, ho3]
  have hwapp := whnfApp_refines p n hk F hF hn ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d v
    (r₃.headD 0) (r₃.tail.headD 0) (r₃.tail.tail.headD 0) (Cmp.evalW .eq v h) so sn 0 xs args nodes
    ⟨hS₃, hs.mode4, hs.eb_mode⟩ hv hhw hxs hvo har₃ hno₃ (by rw [ho3]; omega)
  obtain ⟨hok, ⟨M', hS₄, hK₄, hSt₄⟩, hres, hrw⟩ := CoreSpec.of_callW hwapp h4
  rw [evalW_eq_ne v h hv hh] at hok hres hS₄
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0] at hok hres hS₄
  have hrun₁ : (whnfCoreApp2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v)
      (decE h) args nodes).run a₀ = (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decE v) (decE (r₃.headD 0)) xs (decE v == decE h) args nodes 0).run a₀ := by
    simp only [whnfCoreApp2T, StateT.run_bind, hha, except_ok_bind]
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ (by rw [hrun₁]; exact AM.run_of_ok _ _ hok)
  have h136' : (136 : Word).toNat < (m₄.arr64 CTL).size := by
    rw [← hm, size_set64] at h136; exact h136
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    refine ⟨M', hS₄.frame_stk (MemFrame.setCtl m₄ 136 _) (by simp) (by simp), hK₄, ?_⟩
    apply StackKept.restore _ (by rw [hSt₄.2.1, hgsz]) h136'
    intro i hi
    rw [hSt₄.2.2 i (UInt64.lt_of_lt_of_le hi hgt)]; exact hgk i hi
  · rw [hres', hres]; simp only [decStep, hr0, hr1]
  · exact ⟨hr0 ▸ hrw.1, hr1 ▸ hrw.2⟩

end app2


/-! ## `whnf_core_app` refines the `.app` clause -/

theorem whnfCoreAppT_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) :
    whnfCoreAppT mode r fe cheap depth e = (do
      let sp ← getAppSpine coreWalkFuel e
      let v ← r.whnfCore cheap depth sp.1
      whnfCoreApp2T mode r fe depth v sp.1 sp.2.1 sp.2.2) := rfl

theorem coreApp2W_zero (p : Prog) (m : Mem) (mode vis d v h so sn : Word) :
    coreApp2W p 0 m mode vis d v h so sn = none := by
  simp [coreApp2W, callW_zero]

theorem addW (a b : Word) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

section app
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **`whnf_core_app` refines the `.app` clause of `whnfCoreStep`** (`whnfCoreAppT`). -/
theorem coreApp_refines (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hF : N ≤ F) (hn : N ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (N + 1) "whnf_core_app" [mode, cheap, vis, d, e]
      (whnfCoreAppT (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat (decE e))
      decStep s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW, h136⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (coreApp_spec p hp.capp N s₀ mode cheap vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  simp only [coreAppW] at hW
  cases h1 : callW p N "get_app_spine" [e] s.mem with
  | none => rw [h1] at hW; simp at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  simp only [h1] at hW
  cases h2 : callW p N "whnf_core" [mode, cheap, vis, d, r₁.headD 0] m₁ with
  | none => rw [h2] at hW; simp at hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  simp only [h2] at hW
  cases h4 : callW p N "whnf_core_app2" [mode, vis, d, r₂.headD 0, r₁.headD 0, r₁.tail.headD 0,
      r₁.tail.tail.headD 0] m₂ with
  | none => rw [h4] at hW; simp at hW
  | some q =>
  obtain ⟨r₄, m₄⟩ := q
  simp only [h4, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  -- the spine
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, ns, hsp, hxs, hns⟩ := triple_of_callW
    (getAppSpine_refines p N s a₀ hS.arena.1 e he) h1
  rw [ht₁] at hf₁ hg₁ htop1 hxs hns
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  obtain ⟨hgt, hgsz, hgk⟩ := hg₁
  -- the head
  have hslot := (hk N (Nat.le_refl _)).whnfCore F ⟨m₁, Locals.init []⟩ a₀ dn vis fe MM eb mode cheap
    d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw
  obtain ⟨hok₂, ⟨M', hS₂, hK₂, hSt₂⟩, hres₂, hrw₂⟩ := CoreSpec.of_callW hslot h2
  -- the second half
  cases N with
  | zero => simp [callW_zero] at h1
  | succ N =>
  cases N with
  | zero =>
    obtain ⟨t, -, -, hz, -⟩ := triple_of_callW (coreApp2_spec p hp.capp2 0 ⟨m₂, Locals.init []⟩
      mode vis d (r₂.headD 0) (r₁.headD 0) (r₁.tail.headD 0) (r₁.tail.tail.headD 0)) h4
    simp [coreApp2W_zero] at hz
  | succ n' =>
  have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hS₁.spn
  have hb1 := hxs.bound
  have hb2 := hns.bound
  have e1 : (r₁.tail.headD 0 + r₁.tail.tail.headD 0).toNat =
      (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := addW _ _ (by omega)
  rw [e1] at hb2
  have htopN : (spTop m₁).toNat = (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat +
      (r₁.tail.tail.headD 0).toNat := by
    rw [htop1, ← ho1, addW _ _ (by rw [e1]; omega), e1]
  have hxs₂ := hxs.keep hSt₂.2.1 hSt₂.2.2 (by omega) hspn₁
  have hns₂ := hns.keep hSt₂.2.1 hSt₂.2.2 (by rw [e1]; omega) hspn₁
  have happ := coreApp2_refines p hp n' (hk.mono (by omega)) F (by omega) (by omega)
    ⟨m₂, Locals.init []⟩ _ dn vis fe M' eb mode d (r₂.headD 0) (r₁.headD 0) (r₁.tail.headD 0)
    (r₁.tail.tail.headD 0) xs ns ⟨hS₂, hs.mode4, hs.eb_mode⟩ hrw₂ hhw hxs₂ hns₂
    (by have h22 := hSt₂.1; simp only at h22 ⊢; rw [h22]; omega)
  obtain ⟨hok₄, ⟨M'', hS₄, hK₄, hSt₄⟩, hres₄, hrw₄⟩ := CoreSpec.of_callW happ h4
  have hrun : (whnfCoreAppT (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
      (decE e)).run a₀ = .ok (AM.res (whnfCoreApp2T (decMode mode)
        (coreKnot (decMode mode) fe id F) fe d.toNat (decE (r₂.headD 0)) (decE (r₁.headD 0)) xs ns)
        (AM.st ((coreKnot (decMode mode) fe id F).whnfCore (cheap != 0) d.toNat (decE (r₁.headD 0)))
          a₀), AM.st (whnfCoreApp2T (decMode mode)
        (coreKnot (decMode mode) fe id F) fe d.toNat (decE (r₂.headD 0)) (decE (r₁.headD 0)) xs ns)
        (AM.st ((coreKnot (decMode mode) fe id F).whnfCore (cheap != 0) d.toNat (decE (r₁.headD 0)))
          a₀)) := by
    rw [whnfCoreAppT_eq]
    simp only [StateT.run_bind, hsp, except_ok_bind, AM.run_of_ok _ _ hok₂]
    rw [hres₂]
    exact AM.run_of_ok _ _ hok₄
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
  have h136' : (136 : Word).toNat < (m₄.arr64 CTL).size := by
    rw [← hm, size_set64] at h136; exact h136
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst', ← hm]
    refine ⟨M'', hS₄.frame_stk (MemFrame.setCtl m₄ 136 _) (by simp) (by simp), hK₂.trans hK₄, ?_⟩
    have h22 := hSt₂.1
    simp only at h22
    apply StackKept.restore _ (by rw [hSt₄.2.1, hSt₂.2.1, hgsz]) h136'
    intro i hi
    have hi1 : i < spTop m₁ := UInt64.lt_of_lt_of_le hi hgt
    rw [hSt₄.2.2 i (by rw [h22]; exact hi1), hSt₂.2.2 i hi1, hgk i hi]
  · rw [hres', hres₄]; simp only [decStep, hr0, hr1]
  · exact ⟨hr0 ▸ hrw₄.1, hr1 ▸ hrw₄.2⟩

end app


/-! ## The dispatcher -/

/-- The result of a stuck arm: `(0, e)` if the view check passes. -/
def stuckW (m : Mem) (c e : Word) : Option (Word × Word × Mem) :=
  if rdW (m.arr64 CTL) (c + tierW e) ≤ idxW e then none else some (0, e, m)

/-- The model of `whnf_core_step`. -/
def coreStepW (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word) :
    Option (Word × Word × Mem) :=
  let t := tierW e
  let i := idxW e
  if t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if e >>> 28 = 4 then
    if rdW (m.arr64 CTL) (4 + t) ≤ i then none else
    match callW p n "whnf_core_app" [mode, cheap, vis, d, e] m with
    | none => none
    | some (r, m') => some (r.headD 0, r.tail.headD 0, m')
  else if e >>> 28 = 9 then
    if rdW (m.arr64 CTL) (32 + t) ≤ i then none else
    match callW p n "whnf_core_step_proj" [mode, cheap, vis, d, e,
        rdW (m.arr64 PJREC) (i * 6 + t * 3), rdW (m.arr64 PJREC) (i * 6 + t * 3 + 1),
        rdW (m.arr64 PJREC) (i * 6 + t * 3 + 2)] m with
    | none => none
    | some (r, m') => some (r.headD 0, r.tail.headD 0, m')
  else if e >>> 28 = 7 then
    if rdW (m.arr64 CTL) (20 + t) ≤ i then none else
    match callW p n "inst1" [rdW (m.arr64 LEREC) (i * 6 + t * 3 + 2),
        rdW (m.arr64 LEREC) (i * 6 + t * 3 + 1), 0] m with
    | none => none
    | some (r, m') => some (1, r.headD 0, m')
  else if e >>> 28 = 0 then none
  else if e >>> 28 = 1 then stuckW m 26 e
  else if e >>> 28 = 2 then stuckW m 16 e
  else if e >>> 28 = 3 then stuckW m 18 e
  else if e >>> 28 = 5 then stuckW m 28 e
  else if e >>> 28 = 6 then stuckW m 30 e
  else if e >>> 28 = 8 then stuckW m 2 e
  else none

theorem coreStep_spec (p : Prog) (hp : p.lookup "whnf_core_step" = some whnfCoreStepL) (n : Nat)
    (s₀ : St) (mode cheap vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core_step" [mode, cheap, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      coreStepW p n s₀.mem mode cheap vis d e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, whnfCoreStepL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "whnf_core_app", callW_spec p n "whnf_core_step_proj", callW_spec p n "inst1"] <;>
    finish [coreStepW, stuckW, tierW, idxW]

/-! ## The dispatcher refines `whnfCoreStep` -/

theorem coreRef_congr {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {m : Mem} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₀)
    (h' : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  unfold CoreRef AM.ok AM.st AM.res at *; rw [h]; exact h'

/-- The views `whnfCoreStep` returns as they are. -/
def isDoneV : ENodeView → Bool
  | .sort _ | .fvar _ _ | .forallE _ _ | .lam _ _ | .const _ _ | .lit _ => true
  | _ => false

section stepRuns
variable {mode : ConLeche.CheckMode} {r : CoreFnsA} {fe : IFEnv} {cheap : Bool} {depth : Nat}
  {e : EIdx} {a : AState}

theorem step_run_done (v : ENodeView) (hv : a.store.view e = some v) (hd : isDoneV v = true) :
    (whnfCoreStep mode r fe cheap depth e).run a = .ok (.done e, a) := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases v <;> simp [isDoneV] at hd <;> rfl

theorem step_run_app (f x : EIdx) (hv : a.store.view e = some (.app f x)) :
    (whnfCoreStep mode r fe cheap depth e).run a = (whnfCoreAppT mode r fe cheap depth e).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_proj (sn : NIdx) (i : Nat) (pe : EIdx) (hv : a.store.view e = some (.proj sn i pe)) :
    (whnfCoreStep mode r fe cheap depth e).run a =
      (whnfCoreStepProj mode r fe cheap depth e sn i pe).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_let (t v b : EIdx) (hv : a.store.view e = some (.letE t v b)) :
    (whnfCoreStep mode r fe cheap depth e).run a =
      (do let e' ← instantiate1Fast coreWalkFuel b v 0; pure (WhnfStep.cont e') : AM WhnfStep).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

end stepRuns

theorem stepRef_done {T : AM WhnfStep} {a : AState} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb e : Word} {r : List Word}
    (hS : CoreS dn m a vis fe M eb) (hrun : T.run a = .ok (.done (decE e), a)) (he : HW e)
    (h0 : r.headD 0 = 0) (h1 : r.tail.headD 0 = e) :
    CoreRef T a decStep dn m vis fe M eb r m ResW := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
  · rw [hres]; simp only [decStep, h0, h1, ↓reduceIte]
  · exact ⟨by rw [h0]; unfold HW; decide, by rw [h1]; exact he⟩

section step
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **`whnf_core_step` refines `whnfCoreStep`.** -/
@[refines ConRon.Arena.whnfCoreStep]
theorem whnfCoreStep_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_step" [mode, cheap, vis, d, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) decStep s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (coreStep_spec p hp.step n s₀ mode cheap vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hR := hS.arena.1
  have hh : e.toNat < 2 ^ 32 := he
  simp only [coreStepW] at hW
  by_cases ht : tierW e ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0
  · simp [ht] at hW
  rw [if_neg ht] at hW
  -- the stuck arms
  have stuck : ∀ c : Word, stuckW s.mem c e = some (r.headD 0, r.tail.headD 0, s'.mem) →
      viewOK s.mem e c ∧ r.headD 0 = 0 ∧ r.tail.headD 0 = e ∧ s'.mem = s.mem := by
    intro c h
    simp only [stuckW] at h
    split at h
    · simp at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨⟨ht, by simpa using hle⟩, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  have done : ∀ c : Word, stuckW s.mem c e = some (r.headD 0, r.tail.headD 0, s'.mem) →
      (∀ v, a₀.store.view (decE e) = some v → isDoneV v = true → CoreRef (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe
          (cheap != 0) d.toNat (decE e)) a₀ decStep dn s.mem vis fe MM eb r s'.mem ResW) := by
    intro c h v hv hd
    obtain ⟨-, h0, h1, hm⟩ := stuck c h
    rw [hm]
    exact stepRef_done hS (step_run_done v hv hd) he h0 h1
  by_cases g4 : e >>> 28 = 4
  · rw [if_pos g4] at hW
    by_cases hc4 : rdW (s.mem.arr64 CTL) (4 + tierW e) ≤ idxW e
    · simp [hc4] at hW
    rw [if_neg hc4] at hW
    -- application
    cases hca : callW p n "whnf_core_app" [mode, cheap, vis, d, e] s.mem with
    | none => simp [hca] at hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    simp only [hca, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    cases n with
    | zero => simp [callW_zero] at hca
    | succ N =>
    have hv := (view_app s.mem a₀ hR e hh ⟨ht, by simpa using hc4⟩ g4).1
    have happ := coreApp_refines p hp N (hk.mono (by omega)) F (by omega) (by omega) s a₀ dn vis fe
      MM eb mode cheap d e hs he
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW happ hca
    refine coreRef_congr (step_run_app _ _ hv) ⟨hok, hm ▸ hA, ?_, ?_⟩
    · rw [hres]; simp only [decStep, h0, h1, ↓reduceIte]
    · unfold ResW; rw [← h0, ← h1]; exact hrw
  rw [if_neg g4] at hW
  by_cases g9 : e >>> 28 = 9
  · rw [if_pos g9] at hW
    by_cases hc9 : rdW (s.mem.arr64 CTL) (32 + tierW e) ≤ idxW e
    · simp [hc9] at hW
    rw [if_neg hc9] at hW
    -- projection
    cases hca : callW p n "whnf_core_step_proj" [mode, cheap, vis, d, e,
        rdW (s.mem.arr64 PJREC) (idxW e * 6 + tierW e * 3),
        rdW (s.mem.arr64 PJREC) (idxW e * 6 + tierW e * 3 + 1),
        rdW (s.mem.arr64 PJREC) (idxW e * 6 + tierW e * 3 + 2)] s.mem with
    | none => simp [hca] at hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    simp only [hca, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    cases n with
    | zero => simp [callW_zero] at hca
    | succ N =>
    obtain ⟨hv, hsn, hpe⟩ := view_proj s.mem a₀ hR e hh ⟨ht, by simpa using hc9⟩ g9
    have hpr := whnfCoreStepProj_refines p N (hk.mono (by omega)) F (by omega) (by omega) s a₀ dn
      vis fe MM eb mode cheap d e (rdW (s.mem.arr64 PJREC) (idxW e * 6 + tierW e * 3))
      (rdW (s.mem.arr64 PJREC) (idxW e * 6 + tierW e * 3 + 1))
      (rdW (s.mem.arr64 PJREC) (idxW e * 6 + tierW e * 3 + 2)) hs he hsn hpe
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hpr hca
    refine coreRef_congr (step_run_proj _ _ _ hv) ⟨hok, hm ▸ hA, ?_, ?_⟩
    · rw [hres]; simp only [decStep, h0, h1, ↓reduceIte]
    · unfold ResW; rw [← h0, ← h1]; exact hrw
  rw [if_neg g9] at hW
  by_cases g7 : e >>> 28 = 7
  · rw [if_pos g7] at hW
    by_cases hc7 : rdW (s.mem.arr64 CTL) (20 + tierW e) ≤ idxW e
    · simp [hc7] at hW
    rw [if_neg hc7] at hW
    -- let
    cases hca : callW p n "inst1" [rdW (s.mem.arr64 LEREC) (idxW e * 6 + tierW e * 3 + 2),
        rdW (s.mem.arr64 LEREC) (idxW e * 6 + tierW e * 3 + 1), 0] s.mem with
    | none => simp [hca] at hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    simp only [hca, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    obtain ⟨hv, -, hvv, hbb⟩ := view_let s.mem a₀ hR e hh ⟨ht, by simpa using hc7⟩ g7
    have hi := (coreCallees_stub p).inst1 n s a₀ dn vis fe MM eb _ _ 0 hS hbb hvv
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hi hca
    have hrun := AM.run_of_ok _ _ hok
    refine coreRef_congr (step_run_let _ _ _ hv) ?_
    have hrun' : (instantiate1Fast coreWalkFuel
        (decE (rdW (s.mem.arr64 LEREC) (idxW e * 6 + tierW e * 3 + 2)))
        (decE (rdW (s.mem.arr64 LEREC) (idxW e * 6 + tierW e * 3 + 1))) 0 >>=
        fun e' => pure (WhnfStep.cont e') : AM WhnfStep).run a₀ =
        .ok (.cont (decE (r₁.headD 0)), AM.st (instantiate1Fast coreWalkFuel
        (decE (rdW (s.mem.arr64 LEREC) (idxW e * 6 + tierW e * 3 + 2)))
        (decE (rdW (s.mem.arr64 LEREC) (idxW e * 6 + tierW e * 3 + 1))) 0) a₀) := by
      simp only [StateT.run_bind]
      rw [show ((0 : Word).toNat) = 0 from rfl] at hrun hres
      rw [hrun, hres]; rfl
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun'
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst', ← hm]; exact hA
    · rw [hres']; simp only [decStep, ← h0, ← h1]; rfl
    · exact ⟨by rw [← h0]; unfold HW; decide, by rw [← h1]; exact hrw⟩
  rw [if_neg g7] at hW
  by_cases g0 : e >>> 28 = 0
  · simp [g0] at hW
  rw [if_neg g0] at hW
  by_cases g1 : e >>> 28 = 1
  · rw [if_pos g1] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    obtain ⟨i, ty, hv'⟩ := view_fvar s.mem a₀ hR e hh hv g1
    exact done _ hW _ hv' rfl
  rw [if_neg g1] at hW
  by_cases g2 : e >>> 28 = 2
  · rw [if_pos g2] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    obtain ⟨u, hv'⟩ := view_sort s.mem a₀ hR e hh hv g2
    exact done _ hW _ hv' rfl
  rw [if_neg g2] at hW
  by_cases g3 : e >>> 28 = 3
  · rw [if_pos g3] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    obtain ⟨c, us, hv'⟩ := view_const s.mem a₀ hR e hh hv g3
    exact done _ hW _ hv' rfl
  rw [if_neg g3] at hW
  by_cases g5 : e >>> 28 = 5
  · rw [if_pos g5] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    exact done _ hW _ (view_lam s.mem a₀ hR e hh hv g5).1 rfl
  rw [if_neg g5] at hW
  by_cases g6 : e >>> 28 = 6
  · rw [if_pos g6] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    exact done _ hW _ (view_forall s.mem a₀ hR e hh hv g6).1 rfl
  rw [if_neg g6] at hW
  by_cases g8 : e >>> 28 = 8
  · rw [if_pos g8] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    obtain ⟨l, hv'⟩ := view_lit s.mem a₀ hR e hh hv g8
    exact done _ hW _ hv' rfl
  rw [if_neg g8] at hW
  simp at hW

end step

end L.Arena
