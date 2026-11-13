module

import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.WhnfBase
import all ConAgua.Arena.IndSum
import ConAgua.Arena.DeclCvg

@[expose] public section

/-!
# ConsSumCtors: `ConRon.Arena.consSumCtors`

The refinement theorems `consSumCtors_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ctor_info_rec` -/

/-- The memory after `ctor_info_rec`'s seven `erec_put`s (each copy reads the memory of its time). -/
def ciRecMem (m1 : Mem) (q cv nP nF : Word) : Mem :=
  let m2 := erecPutMem m1 q 4
  let m3 := erecPutMem m2 (q + 1) (erRd m2 cv)
  let m4 := erecPutMem m3 (q + 2) (erRd m3 (cv + 1))
  let m5 := erecPutMem m4 (q + 3) (erRd m4 (cv + 2))
  let m6 := erecPutMem m5 (q + 4) (erRd m5 (cv + 3))
  erecPutMem (erecPutMem m6 (q + 5) nP) (q + 6) nF

/-- The model of `ctor_info_rec(cv, nP, nF)`. -/
def ciRecW (m : Mem) (cv nP nF : Word) : Option (Word × Mem) :=
  match erAllocW m 7 with
  | none => none
  | some (q, m1) =>
    if 4294967296 ≤ erRd (ciRecMem m1 q cv nP nF) (q + 1) then none
    else some (q, ciRecMem m1 q cv nP nF)

theorem ciRec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "ctor_info_rec" = some ctorInfoRecL) (n : Nat) (s₀ : St) (cv nP nF : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctor_info_rec" [cv, nP, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ ciRecW s₀.mem cv nP nF = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, ctorInfoRecL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        erecAlloc_specW p ha n, erecPut_specW p hpu n] <;>
      finish [ciRecW, ciRecMem, erRd]

/-! ## `cons_sum_ctors`: the word model -/

l_model csc_spec (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut) (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL)
  fns [hp ↦ cscW list]
  specs [ciRec_specW p ha hpu hci n, callW_spec p n "env_push"]
  grind [arena_grind, ind_grind] finish [rdW_eq] gen 20

/-! ## `ctor_info_rec` under the stage relation -/

theorem rdW_set64_ne_er {m : Mem} {x y v : Word} (h : x.toNat ≠ y.toNat) :
    rdW ((m.set64 EREC x v).arr64 EREC) y = rdW (m.arr64 EREC) y := by
  simp only [rdW, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [h]

/-- The four copied words of a constant, decoded at a shifted place, decode the same. -/
theorem decCV_shift {a : Nat → Option Word} {q c : Nat} (h0 : a q = a c) (h1 : a (q + 1) = a (c + 1))
    (h2 : a (q + 2) = a (c + 2)) (h3 : a (q + 3) = a (c + 3)) : decCV a q = decCV a c := by
  simp only [decCV, hlist?, hd?, nat?, h0, h1, Nat.add_assoc, show 1 + 1 = 2 from rfl, h2, h3]

theorem ciRecMem_eq {m1 : Mem} {q cq nP nF : Word}
    (hfr : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], ∀ j < 7,
      erTier x ≠ erTier (q + UInt64.ofNat j) ∨ erOff x ≠ erOff (q + UInt64.ofNat j)) :
    ciRecMem m1 q cq nP nF = wrER m1 q [4, erRd m1 cq, erRd m1 (cq + 1), erRd m1 (cq + 2),
      erRd m1 (cq + 3), nP, nF] := by
  have f0 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier q ∨ erOff x ≠ erOff q :=
    fun x hx => by simpa using hfr x hx 0 (by decide)
  have f1 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 1) ∨ erOff x ≠ erOff (q + 1) :=
    fun x hx => hfr x hx 1 (by decide)
  have f2 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 2) ∨ erOff x ≠ erOff (q + 2) :=
    fun x hx => hfr x hx 2 (by decide)
  have f3 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 3) ∨ erOff x ≠ erOff (q + 3) :=
    fun x hx => hfr x hx 3 (by decide)
  simp only [ciRecMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl]
  simp (disch := first
    | exact f0 _ (by simp) | exact f1 _ (by simp) | exact f2 _ (by simp) | exact f3 _ (by simp))
    only [erRd_erecPutMem_ne]

/-- **`ctor_info_rec` under the stage relation**: a fresh `.ctorInfo` record of the constant at `cq`
(decoded in the record pool below its top), the stage relation kept. -/
theorem ciRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq nP nF q : Word} {cv : IConstantVal} (h : ciRecW m cq nP nF = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      ∃ T, decCI (erecP m') q.toNat = some (.ctorInfo cv nP.toNat nF.toNat T) := by
  sorry -- ronsync4-ind: the family word (`ctor_info_rec`'s new argument)

/-! ## `cons_sum_ctors`: the relation to the twin -/

theorem decCVp_truncM {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv) :
    decCV (erecP m) q = some cv := by
  rw [decCVp, truncM_erA] at h; exact h

/-- **`env_push` of a decoded record under the stage relation**: the new view relates the pushed
environment; the pools are kept. -/
theorem envPush_stage {p : Prog} (hrs : p.lookup "env_row_set" = some envRowSetL)
    (hpu : p.lookup "env_push" = some envPushL) {n : Nat} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {c : Word} {r : List Word} {ci : IConstantInfo}
    (hc : callW p n "env_push" [vis, c] m = some (r, m'))
    (hS : StageR vis fe m a) (hci : decCI (erecP m) c.toNat = some ci) :
    StageR (r.headD 0) (fe.push ci) m' a ∧ IWGrow m m' := by
  obtain ⟨s', hs', -, hr, hE, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPush_refines p hrs hpu n ⟨m, Locals.init []⟩ vis c hS.check.env hci) hc
  subst hs' hr
  simp only [List.headD_cons]
  rw [hm] at hE ⊢
  exact StageR.of_own hS hE

/-- A pointer word of the pool read below the top, as the model reads it. -/
theorem rdW_of_iwN_truncM {m : Mem} {o : Word} {v : Nat} (h : iwN (truncM m) o.toNat = some v) :
    ∃ w, rdW (m.arr64 IW) o = w ∧ w.toNat = v ∧ o.toNat < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨w, rdW_of_get? rfl hw', rfl, hi⟩

/-- **`cons_sum_ctors`' model refines `consSumCtors`**: the view returned relates the environment
with the constructors pushed. -/
theorem cscW_ok (p : Prog) (hRp : RecProg p) (k : Nat) (T : NIdx) :
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (nP o l : Word) (cs : List (IConstantVal × Nat))
      (r : List Word),
    cscW p k m nP o l vis = some (r, m') → StageR vis fe m a →
    DecB (fun m => decPL m (decCN m) o.toNat l.toNat) m cs →
    StageR (r.headD 0) (consSumCtors nP.toNat T cs fe) m' a ∧ IWGrow m m' := by
  sorry -- ronsync4-ind: the family word (`cons_sum_ctors`' new argument)

/-- **`cons_sum_ctors` refines `consSumCtors`**: from the stage relation at `vis` of `fe` and the
constructor list decoded below the tops, a returning run returns the view of the environment with
the constructors' `.ctorInfo` records pushed, in order. -/
@[refines ConRon.Arena.consSumCtors]
theorem consSumCtors_refines (p : Prog) (hRp : RecProg p)
    (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis nP o l : Word) (T : NIdx) (cs : List (IConstantVal × Nat))
    (hS : StageR vis fe s₀.mem a₀) (hcs : DecB (fun m => decPL m (decCN m) o.toNat l.toNat) s₀.mem cs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_sum_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR (r.headD 0) (consSumCtors nP.toNat T cs fe) s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (csc_spec p hRp.alloc hRp.put hci hp n s₀ nP o l vis) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, cscW_ok p hRp n T _ _ a₀ vis fe nP o l cs r hm hS hcs⟩

end L.Ind

end
