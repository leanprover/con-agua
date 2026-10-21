import ConAgua.Arena.RecCheck
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndPartsSpec

/-!
# Refinements of `RecCheck` (lane `induct`, round 2)

`target_major_at`'s HIT arm (`refines_part`: the default arm interns, left for a later round) and
`target_ctor_at`'s MEMBER arm (likewise `pure`). Both operations are `pure` on the hit/member
branch, so `AM.ok`/`AM.st`/`AM.res` collapse via `AM.ok_pure`/`AM.st_pure`/`AM.res_pure`
(`ConAgua/Arena/Refine.lean`) and no bind algebra is needed.

`decPL_getH`: a decoded `decPL` slice read back at one index (the general form of `decBS_k`'s
single-field read, `IndPartsSpec.lean`), needed here to read `ms[c]` off `target_major_at`'s `(mo,
ml)` slice of `TargetMajor` pointers. `decCV_some`/`erH_rdW`: the `IConstantVal` analogues of
`decBS_some`/`iwH_rdW`, over `EREC` rather than `IW`, needed to read `c.type` for
`target_ctor_at`.

`trivialTriple`: a `True`-postconditioned triple for any program, used to let `vcgen` step past a
callee on the branch this round leaves unproven (`target_major_default`'s interning, and
`target_ctor_at`'s `cv_lps`/`inst_lp_fast` outside-major path) without needing that callee's own
spec.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `decPL` read back at one index -/

/-- **A decoded `decPL` slice, read back at index `j`**: the pointer word at `o + j` decodes
(by `f`) to the twin's `xs[j]`. -/
theorem decPL_getH {α : Type} (m : Mem) {f : Nat → Option α} {o l : Nat} {xs : List α}
    (h : decPL m f o l = some xs) (j : Nat) (hj : j < l) :
    ∃ v, iwN m (o + j) = some v ∧
      f v = some (xs[j]'(by rw [decPL_length m h]; exact hj)) := by
  simp only [decPL] at h
  have hj' : j < (List.range l).length := by rw [List.length_range]; exact hj
  have hg := mapM_opt_get (fun j => do f (← iwN m (o + j))) (List.range l) xs h j hj'
  simp only [List.getElem_range, Option.bind_eq_bind, Option.bind_eq_some_iff] at hg
  obtain ⟨v, hv, hfv⟩ := hg
  exact ⟨v, hv, hfv⟩

/-- A trivially `True`-postconditioned triple, for the branch this theorem leaves to the default
arm (round 2's scope is the HIT arm only; the MISS arm interns and is left for a later round). -/
theorem trivialTriple {α : Type} (prog : M α) (P : St → Prop) :
    ⦃P⦄ prog ⦃fun _ _ => True; ⊤⦄ :=
  M.triple_of_run fun _ _ _ _ _ => trivial

/-! ## `target_major_at`'s HIT arm -/

/-- **`target_major_at` HIT arm refines `targetMajorAt`**: at an in-range class index, the
L function reads the stored pointer directly (no allocation), which decodes to the twin's
`ms[c]`, just as the twin's `pure m` does nothing to the state. -/
@[refines_part ConRon.Arena.targetMajorAt "hit"]
theorem targetMajorAt_refines_hit (p : Prog) (hp : p.lookup "target_major_at" = some targetMajorAt)
    (n : Nat) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (hR : StageR dn vis fe s₀.mem a₀) (mo ml c : Word) (ms : List TargetMajor)
    (bigM : TargetMajor) (hms : decPL s₀.mem (decTM s₀.mem) mo.toNat ml.toNat = some ms)
    (hc : c.toNat < ml.toNat) (hfound : ms[c.toNat]? = some bigM)
    (hbound : mo.toNat + ml.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "target_major_at" [mo, ml, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetMajorAt ms c.toNat) a₀ ∧
      KeepPost dn vis fe (fun m' r (x : TargetMajor) => decTM m' (r.headD 0).toNat = some x)
        s₀.mem s'.mem a₀ r (AM.res (ConRon.Arena.targetMajorAt ms c.toNat) a₀); ⊤⦄ := by
  obtain ⟨v, hv, hdec⟩ := decPL_getH s₀.mem hms c.toNat hc
  have hv' := iwN_rdW hv (by omega)
  have hget : ms[c.toNat]'(by rw [decPL_length s₀.mem hms]; exact hc) = bigM := by
    have heq := List.getElem?_eq_getElem (l := ms) (i := c.toNat)
      (by rw [decPL_length s₀.mem hms]; exact hc)
    rw [hfound] at heq
    exact (Option.some.injEq _ _).mp heq.symm
  have hdecBigM : decTM s₀.mem v = some bigM := hget ▸ hdec
  have hop : ConRon.Arena.targetMajorAt ms c.toNat = pure bigM := by
    simp [ConRon.Arena.targetMajorAt, hfound]
  have hcc : c < ml := UInt64.lt_iff_toNat_lt.mpr hc
  rw [invoke_eq _ hp]
  simp only [callFn, targetMajorAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        trivialTriple (invoke p (exec p n) "target_major_default" []) (fun s => s = s₀)] <;>
      finish [KeepPost, IWGrow.refl]

/-! ## `target_ctor_at`'s MEMBER arm -/

/-- `decCV`'s fields, read back (the `Env.lean` decoder, over an explicit array). -/
theorem decCV_some {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    hd? a q = some cv.name ∧ hlist? a (q + 1) = some cv.levelParams ∧
      hd? a (q + 3) = some cv.type := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨nm, hnm, l, hl, t, ht, heq⟩ := h
  obtain rfl := (Option.some.injEq _ _).mp heq.symm
  exact ⟨hnm, hl, ht⟩

/-- A decoded `EREC` handle, read back as a memory word (`iwH_rdW`'s analogue over `EREC`). -/
theorem erH_rdW {k : IdxKind} {m : Mem} {i : Nat} {x : Idx k} (h : hd? (erA m) i = some x)
    (hi : i < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (UInt64.ofNat i) = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x := by
  simp only [hd?, erA] at h
  cases hw : (m.arr64 EREC)[i]? with
  | none => simp [hw] at h
  | some w =>
    simp only [hw] at h
    by_cases hl : w.toNat < 2 ^ 32
    · simp [hl] at h
      have hiw : (UInt64.ofNat i).toNat = i := by simp; omega
      exact ⟨w, by simp [rdW, hiw, hw], hl, h⟩
    · simp [hl] at h

/-- **`target_ctor_at` MEMBER arm refines `targetCtorAt`**: at a member major, the L function
reads the constructor's stored type directly (no allocation), just as the twin's `pure c.type`
does nothing to the state. The major's `member` field is taken as a ghost hypothesis here
(`decTM`'s full destructuring is left for a later round; only the one word this arm reads,
`M + 8`, matters). -/
@[refines_part ConRon.Arena.targetCtorAt "member"]
theorem targetCtorAt_refines_member (p : Prog) (hp : p.lookup "target_ctor_at" = some targetCtorAt)
    (n : Nat) (s₀ : St) (a₀ : AState) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (hR : StageR dn vis fe s₀.mem a₀) (M c : Word) (bigM : TargetMajor) (cv : IConstantVal)
    (t0 : Nat) (hmemSome : bigM.member = some t0)
    (hmw : rdW (s₀.mem.arr64 IW) (M + 8) ≠ 0)
    (hcv : decCVp s₀.mem c.toNat = some cv) (hc3 : c.toNat + 3 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "target_ctor_at" [M, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetCtorAt bigM cv) a₀ ∧
      KeepPost dn vis fe decW0E s₀.mem s'.mem a₀ r (AM.res (ConRon.Arena.targetCtorAt bigM cv) a₀); ⊤⦄ := by
  obtain ⟨-, -, htyp⟩ := decCV_some (a := erA s₀.mem) (q := c.toNat) hcv
  obtain ⟨w, hw, hwlt, hwd⟩ := erH_rdW htyp (by omega)
  have hwc : UInt64.ofNat (c.toNat + 3) = c + 3 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add]
    simp
  rw [hwc] at hw
  have hop : ConRon.Arena.targetCtorAt bigM cv = pure cv.type := by
    simp [ConRon.Arena.targetCtorAt, hmemSome]
  rw [invoke_eq _ hp]
  simp only [callFn, targetCtorAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have htrivL : ∀ (args : List Word),
        ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_lp_fast" args ⦃fun _ _ => True; ⊤⦄ :=
      fun args => trivialTriple _ _
    have htrivC : ∀ (args : List Word),
        ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_lps" args ⦃fun _ _ => True; ⊤⦄ :=
      fun args => trivialTriple _ _
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, htrivL, htrivC] <;>
      finish [KeepPost, IWGrow.refl, decW0E]

end L.Ind
