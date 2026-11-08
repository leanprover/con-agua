module

import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.L.WordOff
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.WhnfBase
import all ConAgua.Arena.IndSum

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

/-- The memory after `ctor_info_rec`'s seven writes (each copy reads the memory of its time). -/
def ciRecMem (m1 : Mem) (q cv nP nF : Word) : Mem :=
  let m2 := m1.set64 EREC q 4
  let m3 := m2.set64 EREC (q + 1) (rdW (m2.arr64 EREC) cv)
  let m4 := m3.set64 EREC (q + 2) (rdW (m3.arr64 EREC) (cv + 1))
  let m5 := m4.set64 EREC (q + 3) (rdW (m4.arr64 EREC) (cv + 2))
  let m6 := m5.set64 EREC (q + 4) (rdW (m5.arr64 EREC) (cv + 3))
  (m6.set64 EREC (q + 5) nP).set64 EREC (q + 6) nF

/-- The model of `ctor_info_rec(cv, nP, nF)`. -/
def ciRecW (m : Mem) (cv nP nF : Word) : Option (Word × Mem) :=
  match erAllocW m 7 with
  | none => none
  | some (q, m1) =>
    if 4294967296 ≤ rdW ((ciRecMem m1 q cv nP nF).arr64 EREC) (q + 1) then none
    else some (q, ciRecMem m1 q cv nP nF)

theorem ciRec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hp : p.lookup "ctor_info_rec" = some ctorInfoRecL) (n : Nat) (s₀ : St) (cv nP nF : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ctor_info_rec" [cv, nP, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ ciRecW s₀.mem cv nP nF = some (r.headD 0, s'.mem); ⊤⦄ := by
  sorry

/-! ## `cons_sum_ctors`: the word model -/

/-- The returned view. -/
def cscK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

mutual
/-- The model of `cons_sum_ctors(nP, o, l, vis)` at exec fuel `n`. -/
def cscW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, nP, o, l, vis =>
    if l = 0 then some ([vis], m)
    else cscK1 p n nP o l vis (ciRecW m (rdW (m.arr64 IW) (rdW (m.arr64 IW) o)) nP
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1)))
/-- After `ctor_info_rec`: the push. -/
def cscK1 (p : Prog) (n : Nat) (nP o l vis : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => cscK2 p n nP o l (callW p n "env_push" [vis, q] m1)
/-- After `env_push`: the rest. -/
def cscK2 (p : Prog) (n : Nat) (nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m2) => cscK3 (cscW p n m2 nP (o + 1) (l - 1) (rv.headD 0))
end

section arms
variable (p : Prog) (n : Nat) (m m1 m2 : Mem) (nP o l vis q : Word) (rv : List Word)
theorem cscW_nil (h : l = 0) : cscW p (n + 1) m nP o l vis = some ([vis], m) := by simp [cscW, h]
theorem cscW_cons (h : l ≠ 0) : cscW p (n + 1) m nP o l vis = cscK1 p n nP o l vis (ciRecW m
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) o)) nP (rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1))) := by
  simp [cscW, h]
theorem cscK1_some : cscK1 p n nP o l vis (some (q, m1)) =
    cscK2 p n nP o l (callW p n "env_push" [vis, q] m1) := by simp [cscK1]
theorem cscK2_some : cscK2 p n nP o l (some (rv, m2)) =
    cscK3 (cscW p n m2 nP (o + 1) (l - 1) (rv.headD 0)) := by simp [cscK2]
theorem cscK3_some : cscK3 (some (rv, m2)) = some ([rv.headD 0], m2) := rfl
end arms
attribute [ind_grind] cscW_nil cscW_cons cscK1_some cscK2_some cscK3_some

section spec
variable (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
  (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
  (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL)

include ha hci hp in
theorem csc_spec (n : Nat) : ∀ (s₀ : St) (nP o l vis : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_sum_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cscW p n s₀.mem nP o l vis = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ nP o l vis; rw [invoke_eq _ hp]; simp only [callFn, consSumCtorsL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP o l vis
    rw [invoke_eq _ hp]
    simp only [callFn, consSumCtorsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ciRec_specW p ha hci n, callW_spec p n "env_push", ih] <;> finish (gen := 20) [rdW_eq]

end spec

/-! ## `ctor_info_rec` under the stage relation -/

theorem rdW_set64_ne_er {m : Mem} {x y v : Word} (h : x.toNat ≠ y.toNat) :
    rdW ((m.set64 EREC x v).arr64 EREC) y = rdW (m.arr64 EREC) y := by
  simp only [rdW, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [h]

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The four copied words of a constant, decoded at a shifted place, decode the same. -/
theorem decCV_shift {a : Array Word} {q c : Nat} (h0 : a[q]? = a[c]?) (h1 : a[q + 1]? = a[c + 1]?)
    (h2 : a[q + 2]? = a[c + 2]?) (h3 : a[q + 3]? = a[c + 3]?) : decCV (aread a) q = decCV (aread a) c := by
  simp only [decCV, hlist?, hd?, nat?, h0, h1, h2, h3]
-/

theorem ciRecMem_eq {m1 : Mem} {q cq nP nF : Word} (hlt : cq.toNat + 4 ≤ q.toNat)
    (hq : q.toNat + 7 < 2 ^ 64) :
    ciRecMem m1 q cq nP nF = wrER m1 q [4, rdW (m1.arr64 EREC) cq, rdW (m1.arr64 EREC) (cq + 1),
      rdW (m1.arr64 EREC) (cq + 2), rdW (m1.arr64 EREC) (cq + 3), nP, nF] := by
  sorry

/-- **`ctor_info_rec` under the stage relation**: a fresh `.ctorInfo` record of the constant at `cq`
(decoded in the record pool below its top), the stage relation kept. -/
theorem ciRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq nP nF q : Word} {cv : IConstantVal} (h : ciRecW m cq nP nF = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat = some (.ctorInfo cv nP.toNat nF.toNat) := by
  sorry

/-! ## `cons_sum_ctors`: the relation to the twin -/

theorem decCVp_truncM {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp (truncM m) q = some cv) :
    decCV (erecP m) q = some cv := by
  sorry

/-- A pointer word of the pool read below the top, as the model reads it. -/
theorem rdW_of_iwN_truncM {m : Mem} {o : Word} {v : Nat} (h : iwN (truncM m) o.toNat = some v) :
    ∃ w, rdW (m.arr64 IW) o = w ∧ w.toNat = v ∧ o.toNat < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨w, rdW_of_get? rfl hw', rfl, hi⟩

/-- **`cons_sum_ctors`' model refines `consSumCtors`**: the view returned relates the environment
with the constructors pushed. -/
theorem cscW_ok (p : Prog) (hRp : RecProg p) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (nP o l : Word) (cs : List (IConstantVal × Nat))
      (r : List Word),
    cscW p k m nP o l vis = some (r, m') → StageR vis fe m a →
    DecB (fun m => decPL m (decCN m) o.toNat l.toNat) m cs →
    StageR (r.headD 0) (consSumCtors nP.toNat cs fe) m' a ∧ IWGrow m m' := by
  sorry

/-- **`cons_sum_ctors` refines `consSumCtors`**: from the stage relation at `vis` of `fe` and the
constructor list decoded below the tops, a returning run returns the view of the environment with
the constructors' `.ctorInfo` records pushed, in order. -/
@[refines ConRon.Arena.consSumCtors]
theorem consSumCtors_refines (p : Prog) (hRp : RecProg p)
    (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hp : p.lookup "cons_sum_ctors" = some consSumCtorsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis nP o l : Word) (cs : List (IConstantVal × Nat))
    (hS : StageR vis fe s₀.mem a₀) (hcs : DecB (fun m => decPL m (decCN m) o.toNat l.toNat) s₀.mem cs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_sum_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR (r.headD 0) (consSumCtors nP.toNat cs fe) s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (csc_spec p hRp.alloc hci hp n s₀ nP o l vis) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, cscW_ok p hRp n _ _ a₀ vis fe nP o l cs r hm hS hcs⟩

end L.Ind

end
