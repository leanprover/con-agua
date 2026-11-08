module

public import ConAgua.Arena.InferProj
public import ConAgua.Arena.InferBodyDisp
import ConAgua.Arena.ProjView
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.DefEqStuckCert
public import ConAgua.Arena.WhnfProjRefine
public import ConAgua.Arena.InferProj2Models
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConRon.Bridge.Grind

@[expose] public section

/-!
# `inferProj`: `infer_proj` (lane `defeq2`, helper `defeq2-proj`)

`infer_proj(mode, io, vis, d, sn, i, pe)` refines `inferProj` at both grades (`io = 0`: the knot;
`io = 1`: its io view, `CoreFnsA.ioView`), at L fuel `n + 1` from `KnotUpTo p n`, both outcomes
(`ip_ref`, over the unified model `ipE`): the subject's type (`infer`/`infer_io`, then `whnf`; their
errors are the slots'), its head constant `T.{us}` (read once, before `find_proj`; another head
rejects), the table lookup, then `infer_proj_at` (`ipa_ref`, `InferProj.lean`). A miss aborts in L
where the twin fails (`projMissError`'s verdict: out of range rejects, an indexed structure-like
declines, otherwise rejects).

**`inferProj_refines : InferProjProg p → ProjProg p → InferProjCallees p → InferProjOK p`**
(`ip_ref`'s ok half), closing `InferCallees.proj` (`InferBodyDisp.lean`).

Twin-side facts used here: `findProj?` is a pure lookup that answers only entries below the table's
field count (`findProj?_lt`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The model of `infer_proj` -/

/-! ## `infer_proj` refines `inferProj`, both outcomes -/

/-- **`getAppArgs` runs where `getAppFn` ran** (the same walk at the same fuel). -/
theorem getAppArgs_of_getAppFn : ∀ (fuel : Nat) (h : EIdx) (a : AState) (hh : EIdx) (a' : AState),
    (getAppFn fuel h).run a = .ok (hh, a') → ∃ xs, (getAppArgs fuel h).run a = .ok (xs, a)
  | 0, h, a, hh, a', hr => by simp [getAppFn, ConRon.Arena.fail] at hr; cases hr
  | fuel + 1, h, a, hh, a', hr => by
    by_cases ht : (h.tag == ETag.app) = true
    · cases hv : a.store.viewApp h with
      | none =>
        simp [getAppFn, ht, viewApp, hv, StateT.run_bind, failDanglingE, ConRon.Arena.fail] at hr
        cases hr
      | some fx =>
        obtain ⟨f, x⟩ := fx
        have hr' : (getAppFn fuel f).run a = .ok (hh, a') := by
          simpa [getAppFn, ht, viewApp, hv, StateT.run_bind] using hr
        obtain ⟨xs, hxs⟩ := getAppArgs_of_getAppFn fuel f a hh a' hr'
        refine ⟨xs ++ [x], ?_⟩
        simp [getAppArgs, ht, viewApp, hv, StateT.run_bind, hxs]; rfl
    · refine ⟨[], ?_⟩
      simp [getAppArgs, ht]; rfl

theorem inferProj_notConst (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ a₂ : AState) (it te hh : EIdx)
    (h1 : (r.infer d pe).run a = .ok (it, a₁)) (h2 : (r.whnf d it).run a₁ = .ok (te, a₂))
    (h3 : (getAppFn coreWalkFuel te).run a₂ = .ok (hh, a₂)) (ht : (hh.tag == ETag.const) = false) :
    (inferProj r fe d sn i pe).run a =
      .error (.invalid "invalid projection: not a structure-like type, or no such field") := by
  simp only [inferProj, StateT.run_bind, h1, except_ok_bind, h2, h3, ht]
  rfl

theorem inferProj_miss (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ a₂ : AState) (it te hh : EIdx) (T : NIdx) (us : LsIdx) (xs : List EIdx)
    (h1 : (r.infer d pe).run a = .ok (it, a₁)) (h2 : (r.whnf d it).run a₁ = .ok (te, a₂))
    (h3 : (getAppFn coreWalkFuel te).run a₂ = .ok (hh, a₂)) (ht : (hh.tag == ETag.const) = true)
    (hv : a₂.store.view hh = some (.const T us)) (h4 : fe.findProj? T i = none)
    (h5 : (getAppArgs coreWalkFuel te).run a₂ = .ok (xs, a₂)) :
    (inferProj r fe d sn i pe).run a =
      .error (projMissError fe (fe.findTable? T).isSome T sn i xs.length) := by
  simp only [inferProj, StateT.run_bind, h1, except_ok_bind, h2, h3, ht, ite_true,
    view_run _ _ _ hv, h4, h5]
  rfl

theorem rdW_ext' {a b : Array Word} (hab : ArrExt a b) (hsz : b.size < 2 ^ 63) {q : Word} {k : Nat}
    (hk : k < 64) {w : Word} (ha : a[q.toNat + k]? = some w) : rdW b (q + UInt64.ofNat k) = w := by
  have hb := hab _ _ ha
  have hlt : q.toNat + k < b.size := by
    rcases Nat.lt_or_ge (q.toNat + k) b.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hb
  have : (q + UInt64.ofNat k).toNat = q.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; rw [Nat.mod_eq_of_lt (a := k) (by omega)]; omega
  simp only [rdW, this, hb, Option.getD_some]

/-- **An inductive record's parameter count and constructors**: `nparams` at `q + 17`, the
constructor slice at `q + 18`, `q + 19`. -/
theorem decCI_indNC {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI (aread a) q.toNat = some (.indInfo cv caps))
    (hab : ArrExt a b) (hsz : b.size < 2 ^ 63) :
    caps.nparams = (rdW b (q + 17)).toNat ∧ caps.ctors.length = (rdW b (q + 19)).toNat ∧
    ∀ c, caps.ctors = [c] → c = decI (rdW b (rdW b (q + 18))) ∧ HW (rdW b (rdW b (q + 18))) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
  all_goals (rw [hk] at h)
  all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq,
    and_false, exists_false, Option.pure_def] at h
  obtain ⟨cv', -, caps', hcaps, hc⟩ := h
  cases hc
  simp only [decCaps, bool?, hd?, nat?, hlist?, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hcaps
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, np, ⟨wnp, hwnp, rfl⟩, cs,
    ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩, rfl⟩ := hcaps
  have h17 : rdW b (q + 17) = wnp := rdW_ext' hab hsz (k := 17) (by decide) (by simpa [Nat.add_assoc] using hwnp)
  have h18 : rdW b (q + 18) = wo := rdW_ext' hab hsz (k := 18) (by decide) (by simpa [Nat.add_assoc] using hwo)
  have h19 : rdW b (q + 19) = wc := rdW_ext' hab hsz (k := 19) (by decide) (by simpa [Nat.add_assoc] using hwc)
  refine ⟨by rw [h17], by rw [h19, hslice?_length hs], ?_⟩
  intro c' hc'
  simp only at hc'
  subst hc'
  have h1 : wc.toNat = 1 := by have := hslice?_length hs; simp at this; omega
  rw [h1] at hs
  simp only [hslice?, List.range_one, List.mapM_cons, List.mapM_nil, hd?, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Nat.add_zero] at hs
  obtain ⟨x, ⟨w', hw', hx⟩, _, rfl, hxs⟩ := hs
  simp only [List.cons.injEq, and_true] at hxs
  subst hxs
  have hrd : rdW b wo = w' := by simp only [rdW, hab _ _ hw', Option.getD_some]
  rw [h18, hrd]
  split at hx
  · rename_i hlt
    cases hx
    exact ⟨rfl, hlt⟩
  · cases hx

/-- **An ok `env_find` run**: the memory unchanged, the twin's `find?` decoded, a found record
decodes. -/
theorem envFind_callE {p : Prog} (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word} {fe : IFEnv} {w : Word}
    (hE : EnvR m vis fe) (hw : HW w) {r : List Word}
    (hc : callE p n "env_find" [w, vis] m = .ok (r, m')) :
    m' = m ∧ fe.find? (decI w) = decFound dn m (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨t₁, ht₁, hm₁, -, hfind⟩ := triple_of_callE
    (envFind_refines p hx hg hp n ⟨m, Locals.init []⟩ vis w hE hw) hc
  obtain ⟨t₂, ht₂, -, -, hfound⟩ := triple_of_callE
    (envFind_found p hx hg hp n ⟨m, Locals.init []⟩ vis w hw) hc
  refine ⟨ht₁ ▸ hm₁, hfind, fun h0 => ?_⟩
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  rw [hq]
  exact hE.found_some w hw htag hrow

/-- The constructor test of `projIndexedStructLike`: `c` a constructor with more than `i` fields. -/
def ctorFieldsGt (fe : IFEnv) (c : NIdx) (i : Nat) : Bool :=
  match fe.find? c with
  | some (.ctorInfo _ _ nF) => decide (i < nF)
  | _ => false

/-- **`projIndexedStructLike` at `T = sn` from `env_find(T)`'s record**: the L test `f ≠ 0`, kind
`3`, one constructor, fewer parameters than arguments; then the constructor test. -/
theorem pisl_first {fe : IFEnv} {dn : NIdx → Option ConLeche.Name} {m : Mem} {T : NIdx}
    {f q tn : Word} {i : Nat} (hsz : (m.arr64 EREC).size < 2 ^ 63)
    (hf : fe.find? T = decFound dn m f q)
    (hs : f ≠ 0 → ∃ ci, decCI (erecP m) q.toNat = some ci) :
    (¬ (f ≠ 0 ∧ rdW (m.arr64 EREC) q = 3 ∧ rdW (m.arr64 EREC) (q + 19) = 1 ∧
        rdW (m.arr64 EREC) (q + 17) < tn) →
      projIndexedStructLike fe T T i tn.toNat = false) ∧
    ((f ≠ 0 ∧ rdW (m.arr64 EREC) q = 3 ∧ rdW (m.arr64 EREC) (q + 19) = 1 ∧
        rdW (m.arr64 EREC) (q + 17) < tn) →
      HW (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 18))) ∧
      projIndexedStructLike fe T T i tn.toNat =
        ctorFieldsGt fe (decI (rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 18)))) i) := by
  by_cases f0 : f = 0
  · have hn : fe.find? T = none := by rw [hf]; simp [decFound, f0]
    refine ⟨fun _ => ?_, fun h => absurd h.1 (by simpa using f0)⟩
    simp [projIndexedStructLike, hn]
  obtain ⟨ci, hci⟩ := hs f0
  have hfind : fe.find? T = some ci := by rw [hf]; simp only [decFound, f0, ↓reduceIte]; exact hci
  have hK := decCI_indK hci (erecP_ext m) hsz
  by_cases h3 : rdW (m.arr64 EREC) q = 3
  · obtain ⟨cv, caps, rfl⟩ := hK.1 h3
    obtain ⟨hnp, hlen, hc⟩ := decCI_indNC hci (erecP_ext m) hsz
    by_cases h19 : rdW (m.arr64 EREC) (q + 19) = 1
    · have hl1 : caps.ctors.length = 1 := by rw [hlen, h19]; rfl
      obtain ⟨c, hc1⟩ := List.length_eq_one_iff.mp hl1
      obtain ⟨hcw, hhw⟩ := hc c hc1
      by_cases h17 : rdW (m.arr64 EREC) (q + 17) < tn
      · refine ⟨fun h => absurd ⟨f0, h3, h19, h17⟩ h, fun _ => ⟨hhw, ?_⟩⟩
        have hlt : caps.nparams < tn.toNat := by rw [hnp]; exact UInt64.lt_iff_toNat_lt.mp h17
        simp only [projIndexedStructLike, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfind,
          hc1, hlt, ← hcw, ctorFieldsGt]
        rcases fe.find? c with _ | ci
        · rfl
        · cases ci <;> rfl
      · refine ⟨fun _ => ?_, fun h => absurd h.2.2.2 h17⟩
        have hlt : ¬ caps.nparams < tn.toNat := by
          rw [hnp]; exact fun h => h17 (UInt64.lt_iff_toNat_lt.mpr h)
        simp only [projIndexedStructLike, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfind,
          hc1, hlt]
    · refine ⟨fun _ => ?_, fun h => absurd h.2.2.1 h19⟩
      have hl1 : caps.ctors.length ≠ 1 := by
        rw [hlen]; exact fun h => h19 (UInt64.toNat_inj.mp (by rw [h]; rfl))
      simp only [projIndexedStructLike, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfind]
      split
      · rename_i c hc'; rw [hc'] at hl1; simp at hl1
      · rfl
  · refine ⟨fun _ => ?_, fun h => absurd h.2.1 h3⟩
    have hni := hK.2 h3
    simp only [projIndexedStructLike, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hfind]
    split
    · rename_i cv caps hci'; cases hci'; exact absurd rfl (hni cv caps)
    · rfl

/-- **The constructor test from `env_find(c)`'s record**: `f ≠ 0`, kind `4`, `i` below the field
count at `q + 6`. -/
theorem ctorFieldsGt_eq {fe : IFEnv} {dn : NIdx → Option ConLeche.Name} {m : Mem} {c : NIdx}
    {f q iw : Word} (hsz : (m.arr64 EREC).size < 2 ^ 63)
    (hf : fe.find? c = decFound dn m f q)
    (hs : f ≠ 0 → ∃ ci, decCI (erecP m) q.toNat = some ci) :
    ctorFieldsGt fe c iw.toNat = decide (f ≠ 0 ∧ rdW (m.arr64 EREC) q = 4 ∧
      iw < rdW (m.arr64 EREC) (q + 6)) := by
  by_cases f0 : f = 0
  · have hn : fe.find? c = none := by rw [hf]; simp [decFound, f0]
    simp [ctorFieldsGt, hn, f0]
  obtain ⟨ci, hci⟩ := hs f0
  have hfind : fe.find? c = some ci := by rw [hf]; simp only [decFound, f0, ↓reduceIte]; exact hci
  have hK := decCI_ctorF hci (erecP_ext m) hsz
  by_cases h4 : rdW (m.arr64 EREC) q = 4
  · obtain ⟨cv, rfl⟩ := hK.1 h4
    simp only [ctorFieldsGt, hfind, f0, h4, ne_eq, not_false_eq_true, true_and, decide_eq_decide]
    exact UInt64.lt_iff_toNat_lt.symm
  · have hni := hK.2 h4
    have : ctorFieldsGt fe c iw.toNat = false := by
      simp only [ctorFieldsGt, hfind]
      split
      · rename_i cv np nf hci'; cases hci'; exact absurd rfl (hni cv np nf)
      · rfl
    rw [this]; simp [h4]

theorem inferProj_err1 (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a : AState) (ce : CheckError) (h1 : (r.infer d pe).run a = .error ce) :
    (inferProj r fe d sn i pe).run a = .error ce := by
  simp only [inferProj, StateT.run_bind, h1]; rfl

theorem inferProj_err2 (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ : AState) (it : EIdx) (ce : CheckError) (h1 : (r.infer d pe).run a = .ok (it, a₁))
    (h2 : (r.whnf d it).run a₁ = .error ce) :
    (inferProj r fe d sn i pe).run a = .error ce := by
  simp only [inferProj, StateT.run_bind, h1, except_ok_bind, h2]; rfl

/-- **`infer_proj` at the grade `io` refines `inferProj` at the record `R`**, both outcomes: its
`whnf` is the knot's, its `infer` the first call `f`'s (`hI`, `hIE`). The subject's type's and
`whnf`'s errors are the slots', a head that is no constant rejects, a miss is `projMissError`'s
verdict (out of range / indexed structure-like decline / reject), a hit is `infer_proj_at`'s. -/
theorem ip_grade (p : Prog) (hp : InferProjProg p) (hpj : ProjProg p) (hc : InferProjCallees p)
    (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode io d sn i pe : Word) (R : CoreFnsA)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn)
    (hpe : HW pe) (hWh : R.whnf = (coreKnot (decMode mode) (decEager mode) fe id F).whnf) (f : FnName)
    (hx : ipE p (n + 1) s₀.mem mode io vis d sn i pe =
      ipE.k_infer_io p n mode vis d sn i pe (callE p n f [mode, vis, d, pe] s₀.mem))
    (hI : CoreSpec p n f [mode, vis, d, pe] (R.infer d.toNat (decE pe)) decH s₀ a₀ dn vis fe M eb)
    (hIE : InferG p n → CoreSpecE p n f [mode, vis, d, pe] (R.infer d.toNat (decE pe)) s₀ a₀) :
    RefE (InferG p n) (ipE p (n + 1) s₀.mem mode io vis d sn i pe)
      (inferProj R fe d.toNat (decI sn) i.toNat (decE pe)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  rw [hx]
  have hK := hk n (Nat.le_refl _)
  -- the subject's type
  rcases hc1 : callE p n f [mode, vis, d, pe] s₀.mem with e1 | ⟨r₁, m₁⟩
  · exact fun hG => ErrClaim.of_run_err (fun ce h => inferProj_err1 _ _ _ _ _ _ _ ce h)
      (CoreSpecE.of_callE (hIE hG) hc1)
  simp only [ipE.k_infer_io, ipE.j1]
  have h₁ := CoreSpec.of_callW hI (callW_of_callE hc1)
  have hrun1 := ipRun_of_ref h₁
  obtain ⟨-, ⟨M₁, hS₁, hK₁, hSt₁⟩, -, hrw1⟩ := h₁
  -- `whnf`
  rcases hc2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
  · intro hG
    have hE2 := CoreSpecE.of_callE ((hG.knot n (Nat.le_refl _)).whnf F ⟨m₁, Locals.init []⟩ _ dn vis
      fe M₁ eb mode d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hrw1) hc2
    rw [← hWh] at hE2
    exact ErrClaim.of_run_err (fun ce h => inferProj_err2 _ _ _ _ _ _ _ _ _ ce hrun1 h) hE2
  simp only [ipE.k_whnf]
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hrw1) (callW_of_callE hc2)
  rw [← hWh] at h₂
  have hrun2 := ipRun_of_ref h₂
  obtain ⟨-, ⟨M₂, hS₂, hK₂, hSt₂⟩, -, hrw2⟩ := h₂
  -- `get_app_fn`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₃ m₃ hc3 => ?_
  dsimp only [ipE.k_get_app_fn]
  obtain ⟨rfl, hhw, hgaf⟩ := getAppFn_callW hp.leaf hS₂.arena.base hrw2 hc3
  by_cases g1 : tagW (r₃.headD 0) ≠ 3
  · have ht : ((decE (r₃.headD 0)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hhw]; simpa using g1
    exact RefE.abortAt g1 fun _ =>
      ErrClaim.of_error (inferProj_notConst _ _ _ _ _ _ _ _ _ _ _ _ hrun1 hrun2 hgaf ht) rfl
  refine RefE.pass g1 ?_
  have g1' : tagW (r₃.headD 0) = 3 := Classical.not_not.mp g1
  have ht : ((decE (r₃.headD 0)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hhw]; simpa using g1'
  refine RefE.abort0 (by rfl) fun g2 => ?_
  refine RefE.abort0 (by rfl) fun g3 => ?_
  have hvOK : viewOK m₃ (r₃.headD 0) CONST := ⟨g2, by simpa using g3⟩
  obtain ⟨cT, cu, hv, hcT, hcu, hcTw, hcuw⟩ :=
    view_const_words m₃ _ hS₂.arena.base (r₃.headD 0) hhw hvOK g1'
  generalize tfld m₃ CONST (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0 = wT at hcT hcTw ⊢
  generalize tfld m₃ CONST (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 1 = wu at hcu hcuw ⊢
  subst hcT hcu
  obtain ⟨lsu, hdu⟩ := (hc.den dn m₃ _ vis fe M₂ eb hS₂).constLs _ _ _ hv
  -- `find_proj`
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₄ m₄ hc4 => ?_
  dsimp only [ipE.k_find_proj]
  have h₄ := CoreSpec.of_callW (hc.findProj n ⟨m₃, Locals.init []⟩ _ dn vis fe M₂ eb wT i hS₂ hcTw) hc4
  have hrun4 : fe.findProj? (decI wT) i.toNat =
      decEntry (erecP m₃) (r₄.headD 0) (r₄.tail.headD 0) i.toNat := h₄.res
  obtain ⟨-, ⟨M₄, hS₄, hK₄, hSt₄⟩, -, -⟩ := h₄
  have hE₄ : m₄.arr64 EREC = m₃.arr64 EREC := hc.erec n "find_proj" _ m₃ r₄ m₄ (Or.inl rfl) hc4
  by_cases g4 : r₄.headD 0 = 0
  · -- a miss: `projMissError`
    rw [ite_eq_left g4]
    have hnone : fe.findProj? (decI wT) i.toNat = none := by
      rw [hrun4]; simp only [decEntry, g4, ↓reduceIte]
    obtain ⟨xs, hxs⟩ := getAppArgs_of_getAppFn _ _ _ _ _ hgaf
    have hT := inferProj_miss R fe d.toNat (decI sn) i.toNat (decE pe) a₀ _ _ _ _ _ _ _ xs hrun1
      hrun2 hgaf ht hv hnone hxs
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₅ m₅ hc5 => ?_
    dsimp only [ipE.k_find_table]
    obtain ⟨t₅, ht₅, hm₅, -, htbl, hsome⟩ := triple_of_callW (findTable_refines p
      hp.leaf.core.envix hp.leaf.core.envrow hpj.tblix hpj.tblrow hpj.findTable n
      ⟨m₄, Locals.init []⟩ vis wT hS₄.env hcTw) hc5
    have hm5 : m₅ = m₄ := ht₅ ▸ hm₅
    subst hm5
    by_cases g5 : r₅.headD 0 ≠ 0
    · have hts : (fe.findTable? (decI wT)).isSome = true := by rw [htbl]; exact hsome g5
      exact RefE.abortAt g5 fun _ => ErrClaim.of_error hT (by rw [hts]; rfl)
    refine RefE.pass g5 ?_
    have hts : (fe.findTable? (decI wT)).isSome = false := by
      rw [htbl]; simp only [tblOut, Classical.not_not.mp g5, ↓reduceIte, Option.isSome_none]
    by_cases g6 : wT = sn
    · subst g6
      rw [ite_eq_left rfl]
      refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₆ m₆ hc6 => ?_
      dsimp only [ipE.k_get_app_args]
      refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₇ m₇ hc7 => ?_
      dsimp only [ipE.k_env_find]
      obtain ⟨hf6, -, -, -, xs', hxs', hsp⟩ := getAppArgs_callW hp.leaf.core.spine hS₄ hrw2 hc6
      have hxx : xs' = xs := by
        have := hxs'.symm.trans hxs
        simp only [Except.ok.injEq, Prod.mk.injEq] at this
        exact this.1
      subst hxx
      have hlen : xs'.length = (r₆.tail.headD 0).toNat := by
        have := hsp.size; simpa using this
      have hS₆ := hS₄.frame_stk hf6 (by simp) (by simp)
      obtain ⟨rfl, hfind7, hfound7⟩ := envFind_callE hp.leaf.core.envix hp.leaf.core.envrow
        hp.leaf.core.envfind hS₆.env hcTw (callE_of_callW hc7)
      have hP := pisl_first (i := i.toNat) (tn := r₆.tail.headD 0) hS₆.erec hfind7 hfound7
      by_cases C1 : r₇.headD 0 ≠ 0 ∧ rdW (m₇.arr64 EREC) (r₇.tail.headD 0) = 3 ∧
          rdW (m₇.arr64 EREC) (r₇.tail.headD 0 + 19) = 1 ∧
          rdW (m₇.arr64 EREC) (r₇.tail.headD 0 + 17) < r₆.tail.headD 0
      · rw [ite_eq_left C1]
        obtain ⟨hwc, hpe1⟩ := hP.2 C1
        refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₈ m₈ hc8 => ?_
        dsimp only [ipE.k_env_find_2]
        obtain ⟨rfl, hfind8, hfound8⟩ := envFind_callE hp.leaf.core.envix hp.leaf.core.envrow
          hp.leaf.core.envfind hS₆.env hwc (callE_of_callW hc8)
        have hcf := ctorFieldsGt_eq (iw := i) hS₆.erec hfind8 hfound8
        by_cases C2 : r₈.headD 0 ≠ 0 ∧ rdW (m₈.arr64 EREC) (r₈.tail.headD 0) = 4 ∧
            i < rdW (m₈.arr64 EREC) (r₈.tail.headD 0 + 6)
        · rw [ite_eq_left C2]
          refine fun _ => ?_
          have hpt : projIndexedStructLike fe (decI wT) (decI wT) i.toNat xs'.length = true := by
            rw [hlen, hpe1, hcf]; simpa using C2
          exact ErrClaim.of_error hT (by
            rw [hts]; simp only [projMissError, Bool.false_eq_true, ↓reduceIte, hpt]; rfl)
        · rw [ite_eq_right C2]; simp only [ipE.j2]
          refine fun _ => ?_
          have hpt : projIndexedStructLike fe (decI wT) (decI wT) i.toNat xs'.length = false := by
            rw [hlen, hpe1, hcf]; simpa using C2
          exact ErrClaim.of_error hT (by
            rw [hts]; simp only [projMissError, Bool.false_eq_true, ↓reduceIte, hpt]; rfl)
      · rw [ite_eq_right C1]; simp only [ipE.j2]
        refine fun _ => ?_
        have hpt : projIndexedStructLike fe (decI wT) (decI wT) i.toNat xs'.length = false := by
          rw [hlen]; exact hP.1 C1
        exact ErrClaim.of_error hT (by
            rw [hts]; simp only [projMissError, Bool.false_eq_true, ↓reduceIte, hpt]; rfl)
    · rw [ite_eq_right g6]; simp only [ipE.j2]
      refine fun _ => ?_
      have hne : ((decI wT : NIdx) != decI sn) = true := by
        simp only [bne_iff_ne, ne_eq]; exact fun h => g6 (decI_inj hcTw hsn h)
      have hpt : projIndexedStructLike fe (decI wT) (decI sn) i.toNat xs.length = false := by
        simp [projIndexedStructLike, hne]
      exact ErrClaim.of_error hT (by
            rw [hts]; simp only [projMissError, Bool.false_eq_true, ↓reduceIte, hpt]; rfl)
  · -- a hit: `infer_proj_at`
    rw [ite_eq_right g4]
    obtain ⟨tbl, hdt, hfe⟩ := hc.projFound n m₃ _ dn vis fe M₂ eb wT i r₄ m₄ hS₂ hc4 g4
    have hde : decEntry (erecP m₃) (r₄.headD 0) (r₄.tail.headD 0) i.toNat =
        some (tbl.entry i.toNat) := by
      unfold decEntry; rw [ite_eq_right g4, hdt]; rfl
    rw [hde] at hrun4
    have hq₄ : decTbl (erecP m₄) (r₄.tail.headD 0).toNat = some tbl := by rw [hE₄]; exact hdt
    have hi : i.toNat < tbl.numFields := findProj?_lt hrun4
    cases n with
    | zero => exact RefE.of_cls0 (by simp)
    | succ N =>
    exact RefE.tail_eq (k := ipE.k_infer_proj_at p) (f := fun v => ([v.1.headD 0], v.2))
      (fun _ => rfl) (fun ⟨_, _⟩ => rfl) (fun hG => hG.nv)
      (inferProj_hit R fe d.toNat (decI sn) i.toNat (decE pe) a₀ _ _ _ _ _ _ _ _ hrun1 hrun2 hgaf
        ht hv hrun4)
      (fun _ _ _ h => ⟨CoreAfter.comp (hK₁.trans (hK₂.trans hK₄)) (hSt₁.trans (hSt₂.trans hSt₄))
        h.after, h.res, h.valid⟩)
      (ipa_ref p hp hc N ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb sn i pe (r₂.headD 0) wT wu
        (r₄.tail.headD 0) tbl hS₄ hq₄ hfe hi hcuw hrw2 hpe ⟨lsu, hdu⟩ hsn hcTw)

/-- **`infer_proj` refines `inferProj` at both grades, both outcomes**: the knot's record at
`io = 0`, its io view at `io = 1`. -/
theorem ip_ref (p : Prog) (hp : InferProjProg p) (hpj : ProjProg p) (hc : InferProjCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d sn i pe : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (hsn : HW sn) (hpe : HW pe) :
    RefE (InferG p n) (ipE p (n + 1) s₀.mem mode 0 vis d sn i pe)
      (inferProj (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI sn) i.toNat (decE pe)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) ∧
    RefE (InferG p n) (ipE p (n + 1) s₀.mem mode 1 vis d sn i pe)
      (inferProj (CoreFnsA.ioView (coreKnot (decMode mode) (decEager mode) fe id F)) fe d.toNat (decI sn) i.toNat
        (decE pe)) a₀ (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hK := hk n (Nat.le_refl _)
  exact ⟨ip_grade p hp hpj hc n hk F s₀ a₀ dn vis fe M eb mode 0 d sn i pe _ hF hn hs hsn hpe rfl
      "infer" (by simp [ipE]) (hK.infer F s₀ a₀ dn vis fe M eb mode d pe hF hn hs hpe)
      (fun hG => (hG.knot n (Nat.le_refl _)).infer F s₀ a₀ dn vis fe M eb mode d pe hF hn hs hpe),
    ip_grade p hp hpj hc n hk F s₀ a₀ dn vis fe M eb mode 1 d sn i pe _ hF hn hs hsn hpe rfl
      "infer_io" (by simp [ipE]) (hK.inferIO F s₀ a₀ dn vis fe M eb mode d pe hF hn hs hpe)
      (fun hG => (hG.knot n (Nat.le_refl _)).inferIO F s₀ a₀ dn vis fe M eb mode d pe hF hn hs hpe)⟩

/-- **`infer_proj` refines `inferProj` at both grades** (`InferProjOK`, `InferBodyDisp.lean`;
`ip_ref`'s ok half). -/
@[refines ConRon.Arena.inferProj]
theorem inferProj_refines (p : Prog) (hp : InferProjProg p) (hpj : ProjProg p)
    (hc : InferProjCallees p) : InferProjOK p :=
  fun n hk F s₀ a₀ dn vis fe M eb mode d sn i pe hF hn hs hsn hpe =>
    have h := ip_ref p hp hpj hc n hk F s₀ a₀ dn vis fe M eb mode d sn i pe hF hn hs hsn hpe
    ⟨RefE.coreSpec (ipE_spec p hp.ip hp.ipa (n + 1) s₀ mode 0 vis d sn i pe) h.1,
      RefE.coreSpec (ipE_spec p hp.ip hp.ipa (n + 1) s₀ mode 1 vis d sn i pe) h.2⟩

end L.Arena
