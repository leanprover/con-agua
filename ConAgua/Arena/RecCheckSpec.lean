import ConAgua.Arena.RecCheck
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndPartsSpec
import ConAgua.Arena.RecClassSpec

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


/-! ## `abstract_prefix` (the round-1 `while` rewritten as a self-recursion) -/

mutual
/-- **The model of `abstract_prefix`.** -/
def apW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, k, c, e =>
    if k = 0 then some ([e], m)
    else apK1 n k c (stubM "abstract1_fast" m [CWF, e, k - 1, c])

/-- After `abstract1_fast`. -/
def apK1 (n : Nat) (k c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => apK2 (apW n m1 (k - 1) (c + 1) (r.headD 0))

/-- After the recursive call. -/
def apK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 : Mem) (k c e : Word) (r : List Word)
theorem apW_nil (h : k = 0) : apW (n + 1) m k c e = some ([e], m) := by simp [apW, h]
theorem apW_cons (h : k ≠ 0) :
    apW (n + 1) m k c e = apK1 n k c (stubM "abstract1_fast" m [CWF, e, k - 1, c]) := by
  simp [apW, h]
theorem apK1_some : apK1 n k c (some (r, m1)) = apK2 (apW n m1 (k - 1) (c + 1) (r.headD 0)) := by
  rw [apK1]
theorem apK2_some : apK2 (some (r, m)) = some ([r.headD 0], m) := by
  rw [apK2]
end arms

grind_pattern [ind_grind] apW_nil => apW (n + 1) m k c e
grind_pattern [ind_grind] apW_cons => apW (n + 1) m k c e
grind_pattern [ind_grind] apK1_some => apK1 n k c (some (r, m1))
grind_pattern [ind_grind] apK2_some => apK2 (some (r, m))

theorem abstractPrefix_spec (p : Prog) (hp : p.lookup "abstract_prefix" = some abstractPrefix) (n : Nat) :
    ∀ (s₀ : St) (k c e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abstract_prefix" [k, c, e]
    ⦃fun r s' => LocEq s' s₀ ∧ apW n s₀.mem k c e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ k c e; rw [invoke_eq _ hp]; simp only [callFn, abstractPrefix]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ k c e
    rw [invoke_eq _ hp]
    simp only [callFn, abstractPrefix]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "abstract1_fast" n, ih] <;>
      finish (gen := 20)


theorem apW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k c e : Word) (r : List Word),
    apW n m k c e = some (r, m') → StageR dn vis fe m a → H e → c.toNat + k.toNat < 2 ^ 64 →
    ∃ x a', (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x := by
  induction n with
  | zero => intro m m' a k c e r h; simp [apW] at h
  | succ n ih =>
    intro m m' a k c e r h hS he hb
    by_cases hk : k = 0
    · rw [apW_nil n m k c e hk] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hk0 : k.toNat = 0 := by rw [hk]; rfl
      rw [hk0]
      exact ⟨decI e, a, rfl, hS, IWGrow.refl m, by simpa using he, rfl⟩
    · rw [apW_cons n m k c e hk] at h
      have hpos : 1 ≤ k.toNat := by
        rcases Nat.eq_zero_or_pos k.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hk
        · omega
      have hk1 : (k - 1).toNat = k.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp
      have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      cases ha : stubM "abstract1_fast" m [CWF, e, k - 1, c] with
      | none => rw [ha] at h; simp [apK1] at h
      | some ram =>
        obtain ⟨ra, m1⟩ := ram
        rw [ha, apK1_some] at h
        obtain ⟨x1, a1, hrun1, hS1, hg1, hd1, hd2⟩ :=
          abstract1Fast_spec dn vis fe CWF e (k - 1) c he m m1 a ra ha hS
        cases hr : apW n m1 (k - 1) (c + 1) (ra.headD 0) with
        | none => rw [hr] at h; simp [apK2] at h
        | some rm =>
          obtain ⟨r2, m2⟩ := rm
          rw [hr, apK2_some] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨x2, a2, hrun2, hS2, hg2, hd21, hd22⟩ := ih m1 m2 a1 (k - 1) (c + 1) (ra.headD 0) r2 hr hS1 hd1
            (by rw [hk1, hc1]; omega)
          refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, by simpa using hd21, by simpa using hd22⟩
          rw [CWF_eq, hk1] at hrun1
          have hz : k.toNat = (k.toNat - 1) + 1 := by omega
          rw [hk1, hc1] at hrun2
          rw [hz]
          simp only [ConRon.Arena.abstractPrefix, StateT.run_bind]
          rw [hrun1]
          simp only [bind, Except.bind]
          rw [← hd2]
          exact hrun2

/-- **`abstract_prefix` refines `abstractPrefix`** (through the `abstract1_fast` stub). -/
@[refines ConRon.Arena.abstractPrefix]
theorem abstractPrefix_refines (p : Prog) (hp : p.lookup "abstract_prefix" = some abstractPrefix)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (k c e : Word) (hS : StageR dn vis fe s₀.mem a₀) (he : H e) (hb : c.toNat + k.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abstract_prefix" [k, c, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)) a₀; ⊤⦄ := by
  refine triple_post (abstractPrefix_spec p hp n s₀ k c e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, h1, h2⟩ := apW_ok dn vis fe n _ _ a₀ k c e r hm hS he hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.abstractPrefix k.toNat c.toNat (decI e)) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩


/-! ## `abstract_prefix_list` (the round-1 `while` rewritten as a self-recursion: first element,
then the rest, then `sl_cons`) -/

mutual
/-- **The model of `abstract_prefix_list`.** -/
def aplW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, rP, dso, dsl =>
    if dsl = 0 then some ([0, 0], m)
    else aplK1 n rP dso dsl (apW n m rP 0 (rdW (m.arr64 IW) dso))

/-- After the first element's abstraction. -/
def aplK1 (n : Nat) (rP dso dsl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => aplK2 n (r.headD 0) (aplW n m1 rP (dso + 1) (dsl - 1))

/-- After the recursive call: `sl_cons`. -/
def aplK2 (n : Nat) (x : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => aplK3 (consW n m2 x (r.headD 0) (r.tail.headD 0))

/-- After `sl_cons`. -/
def aplK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (rP dso dsl x : Word) (r : List Word)
theorem aplW_nil (h : dsl = 0) : aplW (n + 1) m rP dso dsl = some ([0, 0], m) := by simp [aplW, h]
theorem aplW_cons (h : dsl ≠ 0) :
    aplW (n + 1) m rP dso dsl = aplK1 n rP dso dsl (apW n m rP 0 (rdW (m.arr64 IW) dso)) := by
  simp [aplW, h]
theorem aplK1_some : aplK1 n rP dso dsl (some (r, m1)) =
    aplK2 n (r.headD 0) (aplW n m1 rP (dso + 1) (dsl - 1)) := by rw [aplK1]
theorem aplK2_some : aplK2 n x (some (r, m2)) =
    aplK3 (consW n m2 x (r.headD 0) (r.tail.headD 0)) := by rw [aplK2]
theorem aplK3_some : aplK3 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0], m3) := by rw [aplK3]
end arms

grind_pattern [ind_grind] aplW_nil => aplW (n + 1) m rP dso dsl
grind_pattern [ind_grind] aplW_cons => aplW (n + 1) m rP dso dsl
grind_pattern [ind_grind] aplK1_some => aplK1 n rP dso dsl (some (r, m1))
grind_pattern [ind_grind] aplK2_some => aplK2 n x (some (r, m2))
grind_pattern [ind_grind] aplK3_some => aplK3 (some (r, m3))

theorem abstractPrefixList_spec (p : Prog) (hap : p.lookup "abstract_prefix" = some abstractPrefix)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "abstract_prefix_list" = some abstractPrefixList) (n : Nat) :
    ∀ (s₀ : St) (rP dso dsl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abstract_prefix_list" [rP, dso, dsl]
    ⦃fun r s' => LocEq s' s₀ ∧ aplW n s₀.mem rP dso dsl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ rP dso dsl; rw [invoke_eq _ hp]; simp only [callFn, abstractPrefixList]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ rP dso dsl
    rw [invoke_eq _ hp]
    simp only [callFn, abstractPrefixList]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        abstractPrefix_spec p hap n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)


theorem aplW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (rP dso dsl : Word) (r : List Word) (ds : List EIdx),
    aplW n m rP dso dsl = some (r, m') → StageR dn vis fe m a →
    decHL m dso.toNat dsl.toNat = some ds → dso.toNat + dsl.toNat < 2 ^ 64 →
    dso.toNat + dsl.toNat ≤ iwTop m → rP.toNat < 2 ^ 64 →
    ∃ xs a', (ConRon.Arena.abstractPrefixList rP.toNat ds).run a = .ok (xs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a rP dso dsl r ds h; simp [aplW] at h
  | succ n ih =>
    intro m m' a rP dso dsl r ds h hS hds hb hbt hrP
    by_cases hdsl : dsl = 0
    · rw [aplW_nil n m rP dso dsl hdsl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : dsl.toNat = 0 := by rw [hdsl]; rfl
      rw [hz] at hds
      simp [decHL, hslice?] at hds
      subst hds
      refine ⟨[], a, rfl, hS, IWGrow.refl m, by simp [decHL, hslice?], by simp⟩
    · rw [aplW_cons n m rP dso dsl hdsl] at h
      have hpos : 1 ≤ dsl.toNat := by
        rcases Nat.eq_zero_or_pos dsl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hdsl
        · omega
      obtain ⟨c1, hc1⟩ : ∃ c1, dsl.toNat = c1 + 1 := ⟨dsl.toNat - 1, by omega⟩
      rw [hc1] at hds
      obtain ⟨d, ds', rfl, hds', hd⟩ := decHL_cons hds
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hd (by omega)
      rw [UInt64.ofNat_toNat] at hw1
      have hdsl1 : (dsl - 1).toNat = c1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
      have hdso1 : (dso + 1).toNat = dso.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [hw1] at h
      cases ha : apW n m rP 0 w with
      | none => rw [ha] at h; simp [aplK1] at h
      | some ram =>
        obtain ⟨ra, m1⟩ := ram
        rw [ha, aplK1_some] at h
        obtain ⟨x1, a1, hrun1, hS1, hg1, hd11, hd12⟩ := apW_ok dn vis fe n m m1 a rP 0 w ra ha hS hw2
          (by simpa using hrP)
        simp only [UInt64.toNat_zero] at hrun1
        cases hr : aplW n m1 rP (dso + 1) (dsl - 1) with
        | none => rw [hr] at h; simp [aplK2] at h
        | some rm =>
          obtain ⟨r2, m2⟩ := rm
          rw [hr, aplK2_some] at h
          have hds1 : decHL m1 (dso + 1).toNat (dsl - 1).toNat = some ds' := by
            rw [hdso1, hdsl1, decHL_grow hg1 (by omega)]; exact hds'
          obtain ⟨xs2, a2, hrun2, hS2, hg2, hd2, ht2⟩ := ih m1 m2 a1 rP (dso + 1) (dsl - 1) r2 ds' hr hS1 hds1
            (by rw [hdso1, hdsl1]; omega) (by rw [hdso1, hdsl1]; have := hg1.1; omega) hrP
          cases hc : consW n m2 (ra.headD 0) (r2.headD 0) (r2.tail.headD 0) with
          | none => rw [hc] at h; simp [aplK3] at h
          | some r3m =>
            obtain ⟨r3, m3⟩ := r3m
            rw [hc, aplK3_some] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hc hS2 ht2 hd11 hd2
            refine ⟨x1 :: xs2, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by rw [← hd12]; simpa using hd3, by simpa using Nat.le_of_eq ht3⟩
            simp only [ConRon.Arena.abstractPrefixList, StateT.run_bind]
            rw [← hw3, hrun1]
            simp only [bind, Except.bind]
            rw [hrun2]
            simp only [bind, Except.bind, pure, StateT.pure, Except.pure]
            rfl


/-- **`abstract_prefix_list` refines `abstractPrefixList`** (through the `abstract1_fast` stub). -/
@[refines ConRon.Arena.abstractPrefixList]
theorem abstractPrefixList_refines (p : Prog) (hap : p.lookup "abstract_prefix" = some abstractPrefix)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "abstract_prefix_list" = some abstractPrefixList) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (rP dso dsl : Word)
    (ds : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hds : decHL s₀.mem dso.toNat dsl.toNat = some ds)
    (hb : dso.toNat + dsl.toNat < 2 ^ 64) (hbt : dso.toNat + dsl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abstract_prefix_list" [rP, dso, dsl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.abstractPrefixList rP.toNat ds) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.abstractPrefixList rP.toNat ds) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (ConRon.Arena.abstractPrefixList rP.toNat ds) a₀); ⊤⦄ := by
  refine triple_post (abstractPrefixList_spec p hap hc ha hsc hp n s₀ rP dso dsl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', hrun, hS', hg, hd, -⟩ := aplW_ok dn vis fe n _ _ a₀ rP dso dsl r ds hm hS hds hb hbt
    rP.toNat_lt
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.abstractPrefixList rP.toNat ds) a₀ a' xs hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd⟩


/-! ## `target_holes` (loop rewritten as recursion: first hole, the rest, `sl_cons`) -/

mutual
/-- **The model of `target_holes`.** -/
def thW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, tyo, tyl, base =>
    if tyl = 0 then some ([0, 0], m)
    else thK1 n tyo tyl base (fvinternW m base (rdW (m.arr64 IW) tyo))

/-- After the first interning (guarded). -/
def thK1 (n : Nat) (tyo tyl base : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (v, m1) =>
    if 4294967296 ≤ v then none
    else thK2 n v (thW n m1 (tyo + 1) (tyl - 1) (base + 1))

/-- After the recursive call: `sl_cons`. -/
def thK2 (n : Nat) (v : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => thK3 (consW n m2 v (r.headD 0) (r.tail.headD 0))

/-- After `sl_cons`. -/
def thK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (tyo tyl base v : Word) (r : List Word)
theorem thW_nil (h : tyl = 0) : thW (n + 1) m tyo tyl base = some ([0, 0], m) := by simp [thW, h]
theorem thW_cons (h : tyl ≠ 0) :
    thW (n + 1) m tyo tyl base = thK1 n tyo tyl base (fvinternW m base (rdW (m.arr64 IW) tyo)) := by
  simp [thW, h]
theorem thK1_big (h : 4294967296 ≤ v) : thK1 n tyo tyl base (some (v, m1)) = none := by
  rw [thK1]; simp [h]
theorem thK1_ok (h : ¬ 4294967296 ≤ v) : thK1 n tyo tyl base (some (v, m1)) =
    thK2 n v (thW n m1 (tyo + 1) (tyl - 1) (base + 1)) := by
  rw [thK1]; simp [h]
theorem thK2_some : thK2 n v (some (r, m2)) = thK3 (consW n m2 v (r.headD 0) (r.tail.headD 0)) := by
  rw [thK2]
theorem thK3_some : thK3 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0], m3) := by rw [thK3]
end arms

grind_pattern [ind_grind] thW_nil => thW (n + 1) m tyo tyl base
grind_pattern [ind_grind] thW_cons => thW (n + 1) m tyo tyl base
grind_pattern [ind_grind] thK1_big => thK1 n tyo tyl base (some (v, m1))
grind_pattern [ind_grind] thK1_ok => thK1 n tyo tyl base (some (v, m1))
grind_pattern [ind_grind] thK2_some => thK2 n v (some (r, m2))
grind_pattern [ind_grind] thK3_some => thK3 (some (r, m3))

theorem targetHoles_spec (p : Prog) (hff : p.lookup "fvar_find" = some fvarFind)
    (hfp : p.lookup "fvar_push" = some fvarPush) (hif : p.lookup "intern_fvar" = some internFVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "target_holes" = some targetHoles) (n : Nat) :
    ∀ (s₀ : St) (tyo tyl base : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_holes" [tyo, tyl, base]
    ⦃fun r s' => LocEq s' s₀ ∧ thW n s₀.mem tyo tyl base = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ tyo tyl base; rw [invoke_eq _ hp]; simp only [callFn, targetHoles]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ tyo tyl base
    rw [invoke_eq _ hp]
    simp only [callFn, targetHoles]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internFVar_spec p hff hfp hif n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)


theorem thW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (tyo tyl base : Word) (r : List Word) (tys : List EIdx),
    thW n m tyo tyl base = some (r, m') → StageR dn vis fe m a →
    decHL m tyo.toNat tyl.toNat = some tys → tyo.toNat + tyl.toNat < 2 ^ 64 →
    tyo.toNat + tyl.toNat ≤ iwTop m → base.toNat + tyl.toNat < 2 ^ 64 →
    ∃ xs a', (ConRon.Arena.targetHoles tys base.toNat).run a = .ok (xs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' a tyo tyl base r tys h; simp [thW] at h
  | succ n ih =>
    intro m m' a tyo tyl base r tys h hS htys hb hbt hbase
    by_cases htyl : tyl = 0
    · rw [thW_nil n m tyo tyl base htyl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : tyl.toNat = 0 := by rw [htyl]; rfl
      rw [hz] at htys
      simp [decHL, hslice?] at htys
      subst htys
      refine ⟨[], a, rfl, hS, IWGrow.refl m, by simp [decHL, hslice?], by simp⟩
    · rw [thW_cons n m tyo tyl base htyl] at h
      have hpos : 1 ≤ tyl.toNat := by
        rcases Nat.eq_zero_or_pos tyl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) htyl
        · omega
      obtain ⟨c1, hc1⟩ : ∃ c1, tyl.toNat = c1 + 1 := ⟨tyl.toNat - 1, by omega⟩
      rw [hc1] at htys
      obtain ⟨ty, tys', rfl, htys', hty⟩ := decHL_cons htys
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hty (by omega)
      rw [UInt64.ofNat_toNat] at hw1
      have htyl1 : (tyl - 1).toNat = c1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
      have htyo1 : (tyo + 1).toNat = tyo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hbase1 : (base + 1).toNat = base.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [hw1] at h
      cases hf : fvinternW m base w with
      | none => rw [hf] at h; simp [thK1] at h
      | some vm1 =>
        obtain ⟨v, m1⟩ := vm1
        rw [hf] at h
        by_cases hv : 4294967296 ≤ v
        · rw [thK1_big n m1 tyo tyl base v hv] at h; simp at h
        rw [thK1_ok n m1 tyo tyl base v hv] at h
        have hv32 : v.toNat < 2 ^ 32 := by
          have : ¬ (4294967296 : Nat) ≤ v.toNat := hv
          omega
        obtain ⟨a1, hrun1, hS1, hg1⟩ := internFVar_stage hS base w hw2 hf
        cases hr : thW n m1 (tyo + 1) (tyl - 1) (base + 1) with
        | none => rw [hr] at h; simp [thK2] at h
        | some rm =>
          obtain ⟨r2, m2⟩ := rm
          rw [hr, thK2_some] at h
          have htys1 : decHL m1 (tyo + 1).toNat (tyl - 1).toNat = some tys' := by
            rw [htyo1, htyl1, decHL_grow hg1 (by omega)]; exact htys'
          obtain ⟨xs2, a2, hrun2, hS2, hg2, hd2, ht2⟩ := ih m1 m2 a1 (tyo + 1) (tyl - 1) (base + 1) r2 tys' hr hS1
            htys1 (by rw [htyo1, htyl1]; omega) (by rw [htyo1, htyl1]; have := hg1.1; omega)
            (by rw [hbase1, htyl1]; omega)
          cases hc : consW n m2 v (r2.headD 0) (r2.tail.headD 0) with
          | none => rw [hc] at h; simp [thK3] at h
          | some r3m =>
            obtain ⟨r3, m3⟩ := r3m
            rw [hc, thK3_some] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hc hS2 ht2 hv32 hd2
            refine ⟨decE v :: xs2, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa [decE_eq] using hd3, by simpa using Nat.le_of_eq ht3⟩
            rw [hbase1] at hrun2
            simp only [ConRon.Arena.targetHoles, ConRon.Arena.internFVarE, StateT.run_bind]
            rw [← hw3, show (decI w : EIdx) = decE w from rfl]
            rw [hrun1]
            simp only [bind, Except.bind]
            rw [hrun2]
            simp only [bind, Except.bind, pure, StateT.pure, Except.pure]
            rfl


/-- **`target_holes` refines `targetHoles`** (through master's `intern_fvar`). -/
@[refines ConRon.Arena.targetHoles]
theorem targetHoles_refines (p : Prog) (hff : p.lookup "fvar_find" = some fvarFind)
    (hfp : p.lookup "fvar_push" = some fvarPush) (hif : p.lookup "intern_fvar" = some internFVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "target_holes" = some targetHoles) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (tyo tyl base : Word)
    (tys : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (htys : decHL s₀.mem tyo.toNat tyl.toNat = some tys) (hb : tyo.toNat + tyl.toNat < 2 ^ 64)
    (hbt : tyo.toNat + tyl.toNat ≤ iwTop s₀.mem) (hbase : base.toNat + tyl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_holes" [tyo, tyl, base]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetHoles tys base.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetHoles tys base.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (ConRon.Arena.targetHoles tys base.toNat) a₀); ⊤⦄ := by
  refine triple_post (targetHoles_spec p hff hfp hif hc ha hsc hp n s₀ tyo tyl base) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', hrun, hS', hg, hd, -⟩ := thW_ok dn vis fe n _ _ a₀ tyo tyl base r tys hm hS htys hb hbt hbase
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.targetHoles tys base.toNat) a₀ a' xs hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd⟩


/-! ## `target_pin_tys` (loop rewritten as recursion) -/

mutual
/-- **The model of `target_pin_tys`.** -/
def tptW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, vis, d, xo, xl =>
    if xl = 0 then some ([], m)
    else tptK n vis d xo xl (stubM "infer_type_core" m [vis, d, rdW (m.arr64 IW) xo])

/-- After `infer_type_core`. -/
def tptK (n : Nat) (vis d xo xl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => tptK2 (tptW n m1 vis d (xo + 1) (xl - 1))

/-- After the recursive call: the function falls off its end. -/
def tptK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m2) => some ([], m2)
end

section arms
variable (n : Nat) (m m1 : Mem) (vis d xo xl : Word) (r : List Word)
theorem tptW_nil (h : xl = 0) : tptW (n + 1) m vis d xo xl = some ([], m) := by simp [tptW, h]
theorem tptW_cons (h : xl ≠ 0) :
    tptW (n + 1) m vis d xo xl = tptK n vis d xo xl (stubM "infer_type_core" m [vis, d, rdW (m.arr64 IW) xo]) := by
  simp [tptW, h]
theorem tptK_some : tptK n vis d xo xl (some (r, m1)) = tptK2 (tptW n m1 vis d (xo + 1) (xl - 1)) := by rw [tptK]
theorem tptK2_some : tptK2 (some (r, m1)) = some ([], m1) := by rw [tptK2]
end arms

grind_pattern [ind_grind] tptW_nil => tptW (n + 1) m vis d xo xl
grind_pattern [ind_grind] tptW_cons => tptW (n + 1) m vis d xo xl
grind_pattern [ind_grind] tptK_some => tptK n vis d xo xl (some (r, m1))
grind_pattern [ind_grind] tptK2_some => tptK2 (some (r, m1))

theorem targetPinTys_spec (p : Prog) (hp : p.lookup "target_pin_tys" = some targetPinTys) (n : Nat) :
    ∀ (s₀ : St) (vis d xo xl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pin_tys" [vis, d, xo, xl]
    ⦃fun r s' => LocEq s' s₀ ∧ tptW n s₀.mem vis d xo xl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis d xo xl; rw [invoke_eq _ hp]; simp only [callFn, targetPinTys]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis d xo xl
    rw [invoke_eq _ hp]
    simp only [callFn, targetPinTys]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "infer_type_core" n, ih] <;>
      finish (gen := 20)


local notation "V" => ConLeche.CheckMode.verified

theorem tptW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis d xo xl : Word) (r : List Word) (xs : List EIdx),
    tptW n m vis d xo xl = some (r, m') → StageR dn vis fe m a →
    decHL m xo.toNat xl.toNat = some xs → xo.toNat + xl.toNat < 2 ^ 64 →
    xo.toNat + xl.toNat ≤ iwTop m →
    ∃ a', (ConRon.Arena.targetPinTys V fe d.toNat xs).run a = .ok ((), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' a vis d xo xl r xs h; simp [tptW] at h
  | succ n ih =>
    intro m m' a vis d xo xl r xs h hS hxs hb hbt
    by_cases hxl : xl = 0
    · rw [tptW_nil n m vis d xo xl hxl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hz : xl.toNat = 0 := by rw [hxl]; rfl
      rw [hz] at hxs
      simp [decHL, hslice?] at hxs
      subst hxs
      exact ⟨a, rfl, hS, IWGrow.refl m⟩
    · rw [tptW_cons n m vis d xo xl hxl] at h
      have hpos : 1 ≤ xl.toNat := by
        rcases Nat.eq_zero_or_pos xl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hxl
        · omega
      obtain ⟨c1, hc1⟩ : ∃ c1, xl.toNat = c1 + 1 := ⟨xl.toNat - 1, by omega⟩
      rw [hc1] at hxs
      obtain ⟨x, xs', rfl, hxs', hx⟩ := decHL_cons hxs
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hx (by omega)
      rw [UInt64.ofNat_toNat] at hw1
      have hxl1 : (xl - 1).toNat = c1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
      have hxo1 : (xo + 1).toNat = xo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [hw1] at h
      cases hi : stubM "infer_type_core" m [vis, d, w] with
      | none => rw [hi] at h; simp [tptK] at h
      | some rm =>
        obtain ⟨ri, m1⟩ := rm
        rw [hi, tptK_some] at h
        obtain ⟨t1, a1, hrun1, hS1, hg1, -⟩ := inferTypeCore_spec dn vis fe d w hw2 m m1 a ri hi hS
        cases hr : tptW n m1 vis d (xo + 1) (xl - 1) with
        | none => rw [hr] at h; simp [tptK2] at h
        | some rm2 =>
          obtain ⟨r2, m2⟩ := rm2
          rw [hr, tptK2_some] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have hxs1 : decHL m1 (xo + 1).toNat (xl - 1).toNat = some xs' := by
            rw [hxo1, hxl1, decHL_grow hg1 (by omega)]; exact hxs'
          obtain ⟨a2, hrun2, hS2, hg2⟩ := ih m1 m2 a1 vis d (xo + 1) (xl - 1) r2 xs' hr hS1 hxs1
            (by rw [hxo1, hxl1]; omega) (by rw [hxo1, hxl1]; have := hg1.1; omega)
          refine ⟨a2, ?_, hS2, hg1.trans hg2⟩
          simp only [ConRon.Arena.targetPinTys, StateT.run_bind]
          rw [← hw3]
          have e : (decI w : EIdx) = decI w := rfl
          rw [hrun1]
          simp only [bind, Except.bind]
          exact hrun2


/-- **`target_pin_tys` refines `targetPinTys .verified`** (through the `infer_type_core` stub). -/
@[refines ConRon.Arena.targetPinTys]
theorem targetPinTys_refines (p : Prog) (hp : p.lookup "target_pin_tys" = some targetPinTys) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis d xo xl : Word)
    (xs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hxs : decHL s₀.mem xo.toNat xl.toNat = some xs) (hb : xo.toNat + xl.toNat < 2 ^ 64)
    (hbt : xo.toNat + xl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pin_tys" [vis, d, xo, xl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetPinTys V fe d.toNat xs) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetPinTys V fe d.toNat xs) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (targetPinTys_spec p hp n s₀ vis d xo xl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg⟩ := tptW_ok dn fe n _ _ a₀ vis d xo xl r xs hm hS hxs hb hbt
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ a₀ a' () hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg⟩


/-! ## `target_pi_doms_with` (loop rewritten as recursion on the binder telescope) -/

mutual
/-- **The model of `target_pi_doms_with`.** -/
def pdW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, xo, xl, e =>
    if xl = 0 then some ([1, 0, 0], m)
    else if e >>> 28 ≠ 6 then some ([0, 0, 0], m)
    else if eViewW m e = [] then none
    else pdK1 n xo xl ((eViewW m e).tail.headD 0)
      (stubM "instantiate1_fast" m [CWF, (eViewW m e).tail.tail.headD 0, rdW (m.arr64 IW) xo, 0])

/-- After `instantiate1_fast`. -/
def pdK1 (n : Nat) (xo xl d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => pdK2 n d (pdW n m1 (xo + 1) (xl - 1) (r.headD 0))

/-- After the recursive call: `sl_cons`. -/
def pdK2 (n : Nat) (d : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) =>
    if r.headD 0 = 0 then some ([0, 0, 0], m2)
    else pdK3 (consW n m2 d (r.tail.headD 0) (r.tail.tail.headD 0))

/-- After `sl_cons`. -/
def pdK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([1, r.headD 0, r.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (xo xl e d : Word) (r : List Word)
theorem pdW_nil (h : xl = 0) : pdW (n + 1) m xo xl e = some ([1, 0, 0], m) := by simp [pdW, h]
theorem pdW_nf (h : xl ≠ 0) (h1 : e >>> 28 ≠ 6) : pdW (n + 1) m xo xl e = some ([0, 0, 0], m) := by
  simp [pdW, h, h1]
theorem pdW_ev (h : xl ≠ 0) (h1 : ¬ e >>> 28 ≠ 6) (h2 : eViewW m e = []) :
    pdW (n + 1) m xo xl e = none := by
  simp only [pdW, h, h1, h2, if_false, if_true]
theorem pdW_cons (h : xl ≠ 0) (h1 : ¬ e >>> 28 ≠ 6) (h2 : eViewW m e ≠ []) : pdW (n + 1) m xo xl e =
    pdK1 n xo xl ((eViewW m e).tail.headD 0)
      (stubM "instantiate1_fast" m [CWF, (eViewW m e).tail.tail.headD 0, rdW (m.arr64 IW) xo, 0]) := by
  simp only [pdW, h, h1, h2, if_false]
theorem pdK1_some : pdK1 n xo xl d (some (r, m1)) = pdK2 n d (pdW n m1 (xo + 1) (xl - 1) (r.headD 0)) := by
  rw [pdK1]
theorem pdK2_none (h : r.headD 0 = 0) : pdK2 n d (some (r, m2)) = some ([0, 0, 0], m2) := by
  rw [pdK2, if_pos h]
theorem pdK2_ok (h : r.headD 0 ≠ 0) : pdK2 n d (some (r, m2)) =
    pdK3 (consW n m2 d (r.tail.headD 0) (r.tail.tail.headD 0)) := by
  rw [pdK2, if_neg h]
theorem pdK3_some : pdK3 (some (r, m3)) = some ([1, r.headD 0, r.tail.headD 0], m3) := by rw [pdK3]
end arms

grind_pattern [ind_grind] pdW_nil => pdW (n + 1) m xo xl e
grind_pattern [ind_grind] pdW_nf => pdW (n + 1) m xo xl e
grind_pattern [ind_grind] pdW_ev => pdW (n + 1) m xo xl e
grind_pattern [ind_grind] pdW_cons => pdW (n + 1) m xo xl e
grind_pattern [ind_grind] pdK1_some => pdK1 n xo xl d (some (r, m1))
grind_pattern [ind_grind] pdK2_none => pdK2 n d (some (r, m2))
grind_pattern [ind_grind] pdK2_ok => pdK2 n d (some (r, m2))
grind_pattern [ind_grind] pdK3_some => pdK3 (some (r, m3))

theorem targetPiDomsWith_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "target_pi_doms_with" = some targetPiDomsWith) (n : Nat) :
    ∀ (s₀ : St) (xo xl e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pi_doms_with" [xo, xl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pdW n s₀.mem xo xl e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ xo xl e; rw [invoke_eq _ hp]; simp only [callFn, targetPiDomsWith]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ xo xl e
    rw [invoke_eq _ hp]
    simp only [callFn, targetPiDomsWith]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        eView_spec p hv n, stubM_spec p "instantiate1_fast" n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20)


theorem tpd_step (x d b b' : EIdx) (e : Word) (xs : List EIdx) (a a1 a2 : AState) (res : Option (List EIdx))
    (htag : ((decE e).tag == ETag.forallE) = true) (hvb : a.store.viewBind (decE e) = some (d, b))
    (h1 : (instantiate1Fast coreWalkFuel b x 0) a = .ok (b', a1))
    (h2 : (ConRon.Arena.targetPiDomsWith xs b') a1 = .ok (res, a2)) :
    (ConRon.Arena.targetPiDomsWith (x :: xs) (decE e)) a =
      .ok ((match res with | some ds => some (d :: ds) | none => none), a2) := by
  simp only [ConRon.Arena.targetPiDomsWith, htag, ite_true]
  have e2 : (ConRon.Arena.viewBind (decE e)) a = .ok (a.store.viewBind (decE e), a) := rfl
  rw [hvb] at e2
  simp only [bind, StateT.bind, e2, Except.bind]
  simp only [h1, Except.bind, h2]
  cases res <;> rfl


theorem viewBind_run' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewBind h).run a = .ok (a.store.viewBind h, a) := rfl

/-- The result words of `target_pi_doms_with` against the twin's result. -/
def PdRes (m' : Mem) (r : List Word) : Option (List EIdx) → Prop
  | none => r.headD 0 = 0
  | some ds => r.headD 0 = 1 ∧ decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some ds ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m'

theorem pdW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (xo xl e : Word) (r : List Word) (xs : List EIdx),
    pdW n m xo xl e = some (r, m') → StageR dn vis fe m a → H e →
    decHL m xo.toNat xl.toNat = some xs → xo.toNat + xl.toNat < 2 ^ 64 →
    xo.toNat + xl.toNat ≤ iwTop m →
    ∃ res a', (ConRon.Arena.targetPiDomsWith xs (decI e)).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PdRes m' r res := by
  induction n with
  | zero => intro m m' a xo xl e r xs h; simp [pdW] at h
  | succ n ih =>
    intro m m' a xo xl e r xs h hS he hxs hb hbt
    by_cases hxl : xl = 0
    · rw [pdW_nil n m xo xl e hxl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : xl.toNat = 0 := by rw [hxl]; rfl
      rw [hz] at hxs
      simp [decHL, hslice?] at hxs
      subst hxs
      refine ⟨some [], a, rfl, hS, IWGrow.refl m, ?_⟩
      simp [PdRes, decHL, hslice?]
    · have hpos : 1 ≤ xl.toNat := by
        rcases Nat.eq_zero_or_pos xl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hxl
        · omega
      obtain ⟨c1, hc1⟩ : ∃ c1, xl.toNat = c1 + 1 := ⟨xl.toNat - 1, by omega⟩
      rw [hc1] at hxs
      obtain ⟨x, xs', rfl, hxs', hx⟩ := decHL_cons hxs
      have hftag : (decE e).tag = ETag.forallE ↔ e >>> 28 = 6 := ctag_iff e he 6 (by decide)
      by_cases hf : e >>> 28 ≠ 6
      · rw [pdW_nf n m xo xl e hxl hf] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨none, a, ?_, hS, IWGrow.refl m, rfl⟩
        have : ¬ (decE e).tag = ETag.forallE := fun hc => hf (hftag.mp hc)
        have htag' : ((decE e).tag == ETag.forallE) = false := by simpa using this
        have e1 : (decI e : EIdx) = decE e := rfl
        rw [e1]
        simp only [ConRon.Arena.targetPiDomsWith, htag', Bool.false_eq_true, ite_false]
        rfl
      have hf6 : e >>> 28 = 6 := by simpa using hf
      by_cases hev : eViewW m e = []
      · rw [pdW_ev n m xo xl e hxl (by simpa using hf) hev] at h; simp at h
      rw [pdW_cons n m xo xl e hxl (by simpa using hf) hev] at h
      obtain ⟨v, hv, hR⟩ := eViewW_ok m a hS.1.arena.1 e hev
      have hhead := eViewW_head6 m e hev hf6
      have hdec : ∃ ty b : EIdx, v = .forallE ty b ∧ (eViewW m e).tail.headD 0 = (eViewW m e).getD 1 0 ∧
          (eViewW m e).tail.tail.headD 0 = (eViewW m e).getD 2 0 ∧
          ((eViewW m e).getD 1 0).toNat < 2 ^ 32 ∧ decE ((eViewW m e).getD 1 0) = ty ∧
          ((eViewW m e).getD 2 0).toNat < 2 ^ 32 ∧ decE ((eViewW m e).getD 2 0) = b := by
        cases v with
        | forallE ty b =>
          simp only [ViewR] at hR
          refine ⟨ty, b, rfl, ?_, ?_, hR.2.1, hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2⟩ <;>
          · cases hh : eViewW m e with
            | nil => exact absurd hh hev
            | cons a1 t => cases t with
              | nil => simp
              | cons a2 t2 => cases t2 <;> simp
        | bvar i => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
        | fvar i ty => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
        | sort u => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
        | const n us => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
        | app f x => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
        | lam f x => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
        | letE f x y => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
        | lit l => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR) (by decide)
        | proj f x y => simp only [ViewR] at hR; exact absurd (hhead.symm.trans hR.1) (by decide)
      obtain ⟨ty, bb, rfl, ht1, ht2, hdlt, hdd, hblt, hbd⟩ := hdec
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hx (by omega)
      rw [UInt64.ofNat_toNat] at hw1
      rw [hw1, ht1, ht2] at h
      have hxl1 : (xl - 1).toNat = c1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
      have hxo1 : (xo + 1).toNat = xo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      cases hi : stubM "instantiate1_fast" m [CWF, (eViewW m e).getD 2 0, w, 0] with
      | none => rw [hi] at h; simp [pdK1] at h
      | some rim =>
        obtain ⟨ri, m1⟩ := rim
        rw [hi, pdK1_some] at h
        obtain ⟨t1, a1, hrun1, hS1, hg1, hd11, hd12⟩ :=
          instantiate1Fast_spec dn vis fe CWF ((eViewW m e).getD 2 0) w 0 hblt hw2 m m1 a ri hi hS
        cases hr : pdW n m1 (xo + 1) (xl - 1) (ri.headD 0) with
        | none => rw [hr] at h; simp [pdK2] at h
        | some rm =>
          obtain ⟨r2, m2⟩ := rm
          rw [hr] at h
          have hxs1 : decHL m1 (xo + 1).toNat (xl - 1).toNat = some xs' := by
            rw [hxo1, hxl1, decHL_grow hg1 (by omega)]; exact hxs'
          obtain ⟨res2, a2, hrun2, hS2, hg2, hres2⟩ := ih m1 m2 a1 (xo + 1) (xl - 1) (ri.headD 0) r2 xs' hr hS1 hd11
            hxs1 (by rw [hxo1, hxl1]; omega) (by rw [hxo1, hxl1]; have := hg1.1; omega)
          have htag : ((decE e).tag == ETag.forallE) = true := by simpa using hftag.mpr hf6
          have hvb := EStore.viewBind_of_view_forall _ _ _ _ hv
          have hrun1' : (instantiate1Fast coreWalkFuel bb (decI w) 0) a = .ok (t1, a1) := by
            have := hrun1
            have e3 : (decI ((eViewW m e).getD 2 0) : EIdx) = decE ((eViewW m e).getD 2 0) := rfl
            have h0 : (0 : Word).toNat = 0 := rfl
            rw [CWF_eq, e3, hbd, h0] at this
            exact this
          have hrun2' : (ConRon.Arena.targetPiDomsWith xs' t1) a1 = .ok (res2, a2) := by
            rw [← hd12]; exact hrun2
          have e1 : (decI e : EIdx) = decE e := rfl
          cases res2 with
          | none =>
            have hstep := tpd_step (decI w) ty bb t1 e xs' a a1 a2 none htag hvb hrun1' hrun2'
            have hr0 : r2.headD 0 = 0 := hres2
            rw [pdK2_none n m2 (r := r2) (d := (eViewW m e).getD 1 0) hr0] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl⟩
            rw [e1, ← hw3]; exact hstep
          | some ds =>
            have hstep := tpd_step (decI w) ty bb t1 e xs' a a1 a2 (some ds) htag hvb hrun1' hrun2'
            obtain ⟨hr1, hdd2, hle⟩ := hres2
            have hr1' : r2.headD 0 ≠ 0 := by rw [hr1]; decide
            rw [pdK2_ok n m2 (r := r2) (d := (eViewW m e).getD 1 0) hr1'] at h
            cases hc : consW n m2 ((eViewW m e).getD 1 0) (r2.tail.headD 0) (r2.tail.tail.headD 0) with
            | none => rw [hc] at h; simp [pdK3] at h
            | some r3m =>
              obtain ⟨r3, m3⟩ := r3m
              rw [hc, pdK3_some] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hc hS2 hle hdlt hdd2
              refine ⟨some (ty :: ds), a2, ?_, hS3, (hg1.trans hg2).trans hg3, ?_⟩
              · rw [e1, ← hw3]; exact hstep
              · refine ⟨rfl, ?_, ?_⟩
                · rw [← hdd]; simpa [decE_eq] using hd3
                · simpa using Nat.le_of_eq ht3


/-- **`target_pi_doms_with` refines `targetPiDomsWith`** (through `e_view`, the `instantiate1_fast`
stub and `sl_cons`). -/
@[refines ConRon.Arena.targetPiDomsWith]
theorem targetPiDomsWith_refines (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "target_pi_doms_with" = some targetPiDomsWith) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (xo xl e : Word) (xs : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (he : H e) (hxs : decHL s₀.mem xo.toNat xl.toNat = some xs)
    (hb : xo.toNat + xl.toNat < 2 ^ 64) (hbt : xo.toNat + xl.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pi_doms_with" [xo, xl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetPiDomsWith xs (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetPiDomsWith xs (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ PdRes s'.mem r (AM.res (ConRon.Arena.targetPiDomsWith xs (decI e)) a₀);
      ⊤⦄ := by
  refine triple_post (targetPiDomsWith_spec p hv hc ha hsc hp n s₀ xo xl e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hS', hg, hres⟩ := pdW_ok dn vis fe n _ _ a₀ xo xl e r xs hm hS he hxs hb hbt
  obtain ⟨hok, hst, hrs⟩ := AM.of_run_ok (ConRon.Arena.targetPiDomsWith xs (decI e)) a₀ a' res hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hrs]; exact hres⟩

end L.Ind
