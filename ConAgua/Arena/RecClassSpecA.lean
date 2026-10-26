import ConAgua.Arena.IndSumSpec
import ConAgua.Arena.RecClass
import ConAgua.Arena.IndInstallSpec
import ConAgua.Arena.IndView
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndRealSpine
import ConAgua.Arena.IndRealAbs

/-!
# Refinements of `RecClass` (lane `induct`)
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A nonzero length word: its `toNat` is a successor, the predecessor's `toNat` that. -/
theorem wordSucc_of_ne {w : Word} (h : w ≠ 0) : ∃ k, w.toNat = k + 1 ∧ (w - 1).toNat = k := by
  have hpos : 1 ≤ w.toNat := by
    rcases Nat.eq_zero_or_pos w.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) h
    · omega
  refine ⟨w.toNat - 1, by omega, ?_⟩
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp

theorem decNL_succ (m : Mem) (off n : Nat) :
    decNL m off (n + 1) = (do
      let x ← iwN m off
      let xs ← decNL m (off + 1) n
      pure (x :: xs)) := by
  simp only [decNL, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

/-- **A decoding `IW` number slice is an `SlR` slice** of the numbers' words. -/
theorem slR_of_decNL (m : Mem) : ∀ (n off : Nat) (ns : List Nat),
    decNL m off n = some ns → off + n < 2 ^ 64 →
    ∃ ws, SlR m (UInt64.ofNat off) (UInt64.ofNat n) ws ∧ ns = ws.map UInt64.toNat := by
  intro n
  induction n with
  | zero =>
    intro off ns h _
    simp [decNL] at h
    exact ⟨[], by simpa using (SlR.nil (m := m) (o := UInt64.ofNat off)), by simp [h]⟩
  | succ n ih =>
    intro off ns h hb
    rw [decNL_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨ws, hws, rfl⟩ := ih (off + 1) xs hxs (by omega)
    obtain ⟨e1, -⟩ := iwN_rdW hx (by omega)
    refine ⟨UInt64.ofNat x :: ws, ?_, ?_⟩
    · have e2 : UInt64.ofNat off + 1 = UInt64.ofNat (off + 1) := by simp [UInt64.ofNat_add]
      have e3 : UInt64.ofNat (n + 1) - 1 = UInt64.ofNat n := by simp [UInt64.ofNat_add]
      have hne : UInt64.ofNat (n + 1) ≠ 0 := by
        intro h0; have := congrArg UInt64.toNat h0; simp at this; omega
      rw [← e1]
      exact SlR.cons hne (by rw [e2, e3]; exact hws)
    · have := (iwN_rdW hx (by omega)).2
      simp; omega

theorem iwN_lt {m : Mem} {i v : Nat} (h : iwN m i = some v) : i < (m.arr64 IW).size := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem iwN_off {m : Mem} {p k v : Nat} (h : iwN m (p + k) = some v) (hb : p + k < 2 ^ 64) :
    (UInt64.ofNat p + UInt64.ofNat k).toNat < (m.arr64 IW).size ∧
    rdW (m.arr64 IW) (UInt64.ofNat p + UInt64.ofNat k) = UInt64.ofNat v := by
  have e : UInt64.ofNat p + UInt64.ofNat k = UInt64.ofNat (p + k) := by simp [UInt64.ofNat_add]
  have hl := iwN_lt h
  rw [e]
  refine ⟨?_, (iwN_rdW h hb).1⟩
  simp; omega

theorem iwH_off {m : Mem} {k' : IdxKind} {p k : Nat} {x : Idx k'} (h : iwH m (p + k) = some x) (hb : p + k < 2 ^ 64) :
    (UInt64.ofNat p + UInt64.ofNat k).toNat < (m.arr64 IW).size ∧
    ∃ w, rdW (m.arr64 IW) (UInt64.ofNat p + UInt64.ofNat k) = w ∧ w.toNat < 2 ^ 32 ∧ decI w = x := by
  have e : UInt64.ofNat p + UInt64.ofNat k = UInt64.ofNat (p + k) := by simp [UInt64.ofNat_add]
  have hl : p + k < (m.arr64 IW).size := by
    simp only [iwH, hd?, iwA] at h
    rcases hw : (m.arr64 IW)[p + k]? with _ | w
    · simp [hw] at h
    · exact (Array.getElem?_eq_some_iff.mp hw).1
  rw [e]
  refine ⟨by simp; omega, iwH_rdW h hb⟩


theorem decPL_succ_do {α : Type} (m : Mem) (f : Nat → Option α) (o l : Nat) :
    decPL m f o (l + 1) = (do
      let x ← (do let p ← iwN m o; f p)
      let ys ← decPL m f (o + 1) l
      pure (x :: ys)) := by
  simp only [decPL, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range l))
  funext j
  simp only [Function.comp]
  congr 2
  omega

theorem decPL_cons {α : Type} {m : Mem} {f : Nat → Option α} {o l : Nat} {xs : List α}
    (h : decPL m f o (l + 1) = some xs) :
    ∃ p x ys, xs = x :: ys ∧ iwN m o = some p ∧ f p = some x ∧ decPL m f (o + 1) l = some ys := by
  rw [decPL_succ_do] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨x, ⟨p, hp, hf⟩, ys, hr, rfl⟩ := h
  exact ⟨p, x, ys, rfl, hp, hf, hr⟩

theorem decPL_le {α : Type} {m : Mem} {f : Nat → Option α} : ∀ {o l : Nat} {xs : List α},
    decPL m f o l = some xs → l = 0 ∨ o + l ≤ (m.arr64 IW).size := by
  intro o l
  induction l generalizing o with
  | zero => intro xs _; exact Or.inl rfl
  | succ l ih =>
    intro xs h
    obtain ⟨p, x, ys, -, hp, -, hr⟩ := decPL_cons h
    have h1 := iwN_lt hp
    rcases ih hr with h0 | h0
    · right; omega
    · right; omega


/-- A decoded `ClassSlot`'s tag word is `1` exactly when it is `.isMinor`. -/
theorem decCS_tag {m : Mem} {p : Nat} {cs : ClassSlot} (h : decCS m p = some cs) :
    iwN m p = some (if cs.isMinor then 1 else 0) := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨q, -, h⟩ := h
    obtain ⟨k, -, rfl⟩ := h
    simp [ht, ClassSlot.isMinor]
  | 1, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, -, h⟩ := h
    obtain ⟨b, -, h⟩ := h
    obtain ⟨c2, -, rfl⟩ := h
    simp [ht, ClassSlot.isMinor]
  | (k + 2), h => simp at h

theorem decCS_motive {m : Mem} {p : Nat} {key : ClassKey} (h : decCS m p = some (.motive key)) :
    iwN m p = some 0 := by
  have := decCS_tag h
  simpa [ClassSlot.isMinor] using this

theorem decCS_minor {m : Mem} {p c' : Nat} {C' : NIdx} {ihs : List (Nat × Nat)}
    (h : decCS m p = some (.minor c' C' ihs)) :
    iwN m p = some 1 ∧ iwN m (p + 1) = some c' ∧ iwH m (p + 2) = some C' ∧
    ∃ o l, iwN m (p + 3) = some o ∧ iwN m (p + 4) = some l ∧ decPL m (decNN m) o l = some ihs := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, h => simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h; obtain ⟨_, _, h⟩ := h; obtain ⟨_, _, h⟩ := h; cases h
  | 1, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, ha, h⟩ := h
    obtain ⟨b, hb, h⟩ := h
    obtain ⟨c2, hc2, h⟩ := h
    cases h
    obtain ⟨o, l, ho, hl, hg⟩ := decAt_some hc2
    exact ⟨ht, ha, hb, o, l, ho, hl, hg⟩
  | (k + 2), h => simp at h

theorem decCS_ptr_lt {m : Mem} {p : Nat} {cs : ClassSlot} (h : decCS m p = some cs) :
    p < (m.arr64 IW).size := by
  have := decCS_tag h
  exact iwN_lt this


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


/-! ## `class_of_motive_var` -/

theorem findIdx_toNat (ws : List Word) (x : Word) :
    (ws.map UInt64.toNat).findIdx? (· == x.toNat) = ws.findIdx? (· == x) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.findIdx?_cons, beq_iff_eq]
    have : (w.toNat = x.toNat) ↔ w = x := ⟨fun h => UInt64.toNat_inj.mp h, fun h => h ▸ rfl⟩
    by_cases h : w = x
    · simp [h]
    · simp [h, this, ih]

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


/-! ## `class_of_motive_var`, model form (for callers) -/

/-- Normalise a two-word result. -/
def cmvK : Option (List Word) → Option (List Word)
  | none => none
  | some r => some [r.headD 0, r.tail.headD 0]

/-- **The model of `class_of_motive_var`** (its `sl_find` runs at the caller's fuel minus one). -/
def cmvW (n : Nat) (m : Mem) (nP o l pv : Word) : Option (List Word) :=
  if pv < nP then some [0, 0] else cmvK (findW n m o l (pv - nP))

theorem cmvW_lt (n : Nat) (m : Mem) (nP o l pv : Word) (h : pv < nP) : cmvW n m nP o l pv = some [0, 0] := by
  simp [cmvW, h]
theorem cmvW_ge (n : Nat) (m : Mem) (nP o l pv : Word) (h : ¬ pv < nP) :
    cmvW n m nP o l pv = cmvK (findW n m o l (pv - nP)) := by
  simp [cmvW, h]
theorem cmvK_some (r : List Word) : cmvK (some r) = some [r.headD 0, r.tail.headD 0] := rfl
grind_pattern [ind_grind] cmvW_lt => cmvW n m nP o l pv
grind_pattern [ind_grind] cmvW_ge => cmvW n m nP o l pv
grind_pattern [ind_grind] cmvK_some => cmvK (some r)

theorem classOfMotiveVar_spec (p : Prog) (hf : p.lookup "sl_find" = some slFind)
    (hp : p.lookup "class_of_motive_var" = some classOfMotiveVar) (n : Nat) (s₀ : St)
    (nP o l pv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_of_motive_var" [nP, o, l, pv]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ cmvW (n - 1) s₀.mem nP o l pv = some r; ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classOfMotiveVar]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, slFind_spec p hf n] <;>
      finish (gen := 20) [cmvW]

theorem cmvW_ok (n : Nat) (m : Mem) (nP o l pv : Word) (r : List Word) (ns : List Nat)
    (hd : decNL m o.toNat l.toNat = some ns) (hb : o.toNat + l.toNat < 2 ^ 64)
    (h : cmvW n m nP o l pv = some r) :
    r = match ConRon.Arena.classOfMotiveVar nP.toNat ns pv.toNat with
        | some i => [1, UInt64.ofNat i]
        | none => [0, 0] := by
  obtain ⟨ws, hws, rfl⟩ := slR_of_decNL m _ _ _ hd hb
  simp only [UInt64.ofNat_toNat] at hws
  have hlen : ws.length < 2 ^ 64 := by
    have := decNL_length m hd; simp at this; omega
  by_cases hlt : pv < nP
  · rw [cmvW_lt n m nP o l pv hlt] at h
    cases h
    have : ¬ nP.toNat ≤ pv.toNat := by have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    simp [ConRon.Arena.classOfMotiveVar, this]
  · rw [cmvW_ge n m nP o l pv hlt] at h
    obtain ⟨r0, hr, h⟩ := of_K h rfl
    rw [cmvK_some] at h
    simp only [Option.some.injEq] at h
    have hle' : nP.toNat ≤ pv.toNat := Nat.le_of_not_lt fun hh => hlt (UInt64.lt_iff_toNat_lt.mpr hh)
    have hle : nP ≤ pv := UInt64.le_iff_toNat_le.mpr hle'
    have hsub : (pv - nP).toNat = pv.toNat - nP.toNat := UInt64.toNat_sub_of_le _ _ hle
    have hk := findW_ok n _ _ _ _ _ _ hws hr hlen
    subst h
    rw [hk]
    simp only [ConRon.Arena.classOfMotiveVar, hle', ite_true, ← hsub, findIdx_toNat]
    cases List.findIdx? (fun x => x == pv - nP) ws <;> rfl

/-- **`class_of_motive_var` refines `classOfMotiveVar`**: `(1, i)` for `some i`, `(0, 0)` for
`none`; memory unchanged. -/
@[refines ConRon.Arena.classOfMotiveVar]
theorem classOfMotiveVar_refines (p : Prog) (hf : p.lookup "sl_find" = some slFind)
    (hp : p.lookup "class_of_motive_var" = some classOfMotiveVar) (n : Nat) (s₀ : St)
    (nP o l pv : Word) (ns : List Nat) (hd : decNL s₀.mem o.toNat l.toNat = some ns)
    (hb : o.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_of_motive_var" [nP, o, l, pv]
    ⦃fun r s' => s'.mem = s₀.mem ∧
      r = match ConRon.Arena.classOfMotiveVar nP.toNat ns pv.toNat with
        | some i => [1, UInt64.ofNat i]
        | none => [0, 0]; ⊤⦄ :=
  triple_post (classOfMotiveVar_spec p hf hp (n + 1) s₀ nP o l pv) fun r _ ⟨_, hm, hw⟩ =>
    ⟨hm, cmvW_ok n s₀.mem nP o l pv r ns hd hb hw⟩

/-! ## `class_binder`, `class_gen_binder`: one `fvar_type_d` call -/

/-- The word model of a one-call wrapper of `fvar_type_d`. -/
def fvarTypeDW1 (m : Mem) (x : Word) : Option (List Word × Mem) :=
  match ftdF m [x] with
  | none => none
  | some (r, m') => some ([r.headD 0], m')

theorem classBinder_spec (p : Prog) (hp : p.lookup "class_binder" = some classBinder) (had : AdF p)
    (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_binder" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarTypeDW1 s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classBinder]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ftdF_spec p had n] <;>
    finish [fvarTypeDW1]

theorem classGenBinder_spec (p : Prog) (hp : p.lookup "class_gen_binder" = some classGenBinder)
    (had : AdF p) (n : Nat) (s₀ : St) (g x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_binder" [g, x]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarTypeDW1 s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenBinder]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ftdF_spec p had n] <;>
    finish [fvarTypeDW1]

/-- The relational lemma of `fvarTypeDW1`. -/
theorem fvarTypeDW1_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (x : Word) (hx : H x) (r : List Word) (h : fvarTypeDW1 m x = some (r, m'))
    (hS : StageR dn vis fe m a) :
    ∃ t a', (fvarTypeD (decI x)).run a = .ok (t, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = t := by
  simp only [fvarTypeDW1] at h
  split at h
  · cases h
  rename_i r1 m1 hs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨t, a', hrun, hS', hg, hd1, hd2⟩ := ftdF_ok dn vis fe x hx m m1 a r1 hs hS
  exact ⟨t, a', hrun, hS', hg, hd1, by simpa using hd2⟩

/-- **`class_binder` refines `classBinder`** (through `fvar_type_d`). -/
@[refines ConRon.Arena.classBinder]
theorem classBinder_refines (p : Prog) (hp : p.lookup "class_binder" = some classBinder) (had : AdF p)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x : Word)
    (hx : H x) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_binder" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classBinder (decI x)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classBinder (decI x)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.classBinder (decI x)) a₀; ⊤⦄ := by
  refine triple_post (classBinder_spec p hp had n s₀ x) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hS', hg, h1, h2⟩ := fvarTypeDW1_ok dn vis fe _ _ a₀ x hx r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.classBinder (decI x)) a₀ a' t hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩

/-- **`class_gen_binder` refines `ClassGen.binder`** (through `fvar_type_d`). -/
@[refines ConRon.Arena.ClassGen.binder]
theorem classGenBinder_refines (p : Prog) (hp : p.lookup "class_gen_binder" = some classGenBinder)
    (had : AdF p) (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (G : ClassGen) (g x : Word) (hx : H x) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_binder" [g, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.binder G (decI x)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.binder G (decI x)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.ClassGen.binder G (decI x)) a₀; ⊤⦄ := by
  refine triple_post (classGenBinder_spec p hp had n s₀ g x) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hS', hg, h1, h2⟩ := fvarTypeDW1_ok dn vis fe _ _ a₀ x hx r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.ClassGen.binder G (decI x)) a₀ a' t hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩


/-! ## `expr_get_d` -/

/-- The word model of `expr_get_d`. -/
def exprGetDW (m : Mem) (o l i : Word) : Option (List Word × Mem) :=
  if i < l then
    (if (o + i).toNat < (m.arr64 IW).size then some ([rdW (m.arr64 IW) (o + i)], m) else none)
  else
    match binternW m 0 with
    | none => none
    | some (r, m') => if 4294967296 ≤ r then none else some ([r], m')

theorem exprGetD_spec (p : Prog) (hpf : p.lookup "bvar_find" = some bvarFind)
    (hpp : p.lookup "bvar_push" = some bvarPush) (hib : p.lookup "intern_bvar" = some internBVar)
    (hp : p.lookup "expr_get_d" = some exprGetD) (n : Nat) (s₀ : St)
    (o l i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "expr_get_d" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ exprGetDW s₀.mem o l i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, exprGetD]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      internBVar_spec p hpf hpp hib n] <;>
    finish [exprGetDW]

theorem exprGetDW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (o l i : Word) (xs : List EIdx) (r : List Word)
    (h : exprGetDW m o l i = some (r, m')) (hS : StageR dn vis fe m a)
    (hxs : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.exprGetD xs i.toNat).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x := by
  simp only [exprGetDW] at h
  by_cases hi : i < l
  · simp only [hi, ite_true] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hit : i.toNat < l.toNat := UInt64.lt_iff_toNat_lt.mp hi
      obtain ⟨w, hw1, hw2, hw3⟩ := decHL_get' hxs i.toNat hit hb
      have hoi : o + i = UInt64.ofNat (o.toNat + i.toNat) := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
      refine ⟨xs[i.toNat]'(by rw [decHL_length m hxs]; exact hit), a, ?_, hS, IWGrow.refl m, ?_, ?_⟩
      · simp [ConRon.Arena.exprGetD, hit, decHL_length m hxs]; rfl
      · simp only [List.headD_cons]; rw [hoi, hw1]; exact hw2
      · simp only [List.headD_cons]; rw [hoi, hw1]; exact hw3.symm
    · simp at h
  · simp only [hi, ite_false] at h
    split at h
    · cases h
    rename_i r1 m1 hs
    obtain ⟨hbig, h⟩ := of_ite_none h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨a', hrun, hS', hg⟩ := internBVar_stage hS 0 hs
    have hge : l.toNat ≤ i.toNat := Nat.le_of_not_lt fun h => hi (UInt64.lt_iff_toNat_lt.mpr h)
    have hlt : r1.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ r1.toNat := hbig; omega
    refine ⟨decE r1, a', ?_, hS', hg, by simpa using hlt, by simp [decE_eq]⟩
    have hn : xs[i.toNat]? = none := by
      rw [List.getElem?_eq_none_iff, decHL_length m hxs]; exact hge
    simp only [ConRon.Arena.exprGetD, hn]
    exact hrun

/-- **`expr_get_d` refines `exprGetD`** (through master's `intern_bvar`). -/
@[refines ConRon.Arena.exprGetD]
theorem exprGetD_refines (p : Prog) (hpf : p.lookup "bvar_find" = some bvarFind)
    (hpp : p.lookup "bvar_push" = some bvarPush) (hib : p.lookup "intern_bvar" = some internBVar)
    (hp : p.lookup "expr_get_d" = some exprGetD) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (o l i : Word) (xs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hxs : decHL s₀.mem o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "expr_get_d" [o, l, i]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.exprGetD xs i.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.exprGetD xs i.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.exprGetD xs i.toNat) a₀; ⊤⦄ := by
  refine triple_post (exprGetD_spec p hpf hpp hib hp n s₀ o l i) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, h1, h2⟩ := exprGetDW_ok dn vis fe _ _ a₀ o l i xs r hm hS hxs hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.exprGetD xs i.toNat) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩

theorem ETables.getFVarIdx_of_get (t : ETables) (i : EIdx) (k : Nat) (ty : EIdx)
    (h : t.get i = some (.fvar k ty)) : t.getFVarIdx i = some k := by
  unfold ETables.get at h
  unfold ETables.getFVarIdx
  split at h
  · simp at h
  split at h
  · cases hn : t.fvars.node? i.idxNat <;> simp [hn] at h ⊢
    exact h.1
  all_goals (repeat' (first | (simp at h; done) | split at h))

theorem EStore.viewFVarIdx_of_view (st : EStore) (i : EIdx) (k : Nat) (ty : EIdx)
    (h : st.view i = some (.fvar k ty)) : st.viewFVarIdx i = some k := by
  unfold EStore.view at h
  unfold EStore.viewFVarIdx EStore.persGetFVarIdx
  split at h
  · simp only [*, ite_true]; exact ETables.getFVarIdx_of_get _ _ _ _ h
  · split at h
    · simp only [*, ite_true]; split <;> simp_all [ETables.getFVarIdx_of_get _ _ _ _ h]
    · simp at h

/-! ## `fvar_head` -/

/-- The word model of `fvar_head`. -/
def fvarHeadW (m : Mem) (e : Word) : Option (List Word × Mem) :=
  match gafF m [CWF, e] with
  | none => none
  | some (r, m1) =>
    if r.headD 0 >>> 28 = 1 then
      (if eViewW m1 (r.headD 0) = [] then none
       else some ([1, (eViewW m1 (r.headD 0)).tail.headD 0], m1))
    else some ([0, 0], m1)

theorem fvarHead_spec (p : Prog) (hp : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (had : AdF p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarHeadW s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, fvarHead]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        gafF_spec p had n, eView_spec p hv n] <;>
      finish [fvarHeadW]

theorem viewFVarIdx_run' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewFVarIdx h).run a = .ok (a.store.viewFVarIdx h, a) := rfl

theorem fvarHeadW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (e : Word) (he : H e) (r : List Word) (h : fvarHeadW m e = some (r, m'))
    (hS : StageR dn vis fe m a) :
    ∃ x a', (ConRon.Arena.fvarHead (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ r = (match x with | some i => [1, UInt64.ofNat i] | none => [0, 0]) ∧
      (∀ i, x = some i → i < 2 ^ 64) := by
  simp only [fvarHeadW] at h
  split at h
  · cases h
  rename_i r1 m1 hs
  obtain ⟨t, a1, hrun1, hS1, hg1, hd1, hd2⟩ := gafF_ok dn vis fe CWF e he m m1 a r1 hs hS
  rw [CWF_eq] at hrun1
  generalize r1.headD 0 = w at hd1 hd2 h
  by_cases hf : w >>> 28 = 1
  · rw [ite_eq_left hf] at h
    obtain ⟨hne, h⟩ := of_ite_none h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨v, hv, hR⟩ := eViewW_ok m1 a1 hS1.1.arena.1 w hne
    have htag : (decE w).tag = ETag.fvar := by
      rw [decE_tag w hd1, hf]; rfl
    cases v
    case fvar k ty =>
      simp only [ViewR] at hR
      have hk := EStore.viewFVarIdx_of_view _ _ _ _ hv
      refine ⟨some k, a1, ?_, hS1, hg1, ?_, fun i hi => ?_⟩
      · simp only [ConRon.Arena.fvarHead]
        rw [StateT.run_bind, hrun1]
        simp only [bind, Except.bind]
        rw [← hd2, show (decI w : EIdx) = decE w from rfl]
        simp only [htag, beq_self_eq_true, ite_true]
        have e1 : (ConRon.Arena.viewFVarIdx (decE w)).run a1 = .ok (some k, a1) := by
          rw [viewFVarIdx_run', hk]
        simp only [StateT.run] at e1 ⊢
        simp only [StateT.bind, e1, bind, Except.bind]
        rfl
      · have e2 : (eViewW m1 w).tail.headD 0 = (eViewW m1 w).getD 1 0 := by
          rcases eViewW m1 w with _ | ⟨_, _ | _⟩ <;> simp
        simp only [e2, ← hR.2.1, UInt64.ofNat_toNat]
      · simp only [Option.some.injEq] at hi
        rw [← hi, ← hR.2.1]; exact UInt64.toNat_lt _
    all_goals (have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide))
  · rw [ite_eq_right hf] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have htag : ¬ (decE w).tag = ETag.fvar := by
      rw [decE_tag w hd1]
      intro hc
      apply hf
      have := congrArg UInt32.toNat hc
      simp [ETag.fvar] at this
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_shiftRight]
      simp
      omega
    refine ⟨none, a1, ?_, hS1, hg1, rfl, fun i hi => by simp at hi⟩
    simp only [ConRon.Arena.fvarHead]
    rw [StateT.run_bind, hrun1]
    simp only [bind, Except.bind]
    rw [← hd2, show (decI w : EIdx) = decE w from rfl]
    have htag' : ((decE w).tag == ETag.fvar) = false := by simpa using htag
    simp only [htag', Bool.false_eq_true, ite_false]
    rfl


/-- **`fvar_head` refines `fvarHead`** (through the `get_app_fn` stub and `e_view`). -/
@[refines ConRon.Arena.fvarHead]
theorem fvarHead_refines (p : Prog) (hp : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (had : AdF p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e : Word) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.fvarHead (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.fvarHead (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      r = (match AM.res (ConRon.Arena.fvarHead (decI e)) a₀ with
        | some i => [1, UInt64.ofNat i] | none => [0, 0]); ⊤⦄ := by
  refine triple_post (fvarHead_spec p hp hv had n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hr, -⟩ := fvarHeadW_ok dn vis fe _ _ a₀ e he r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.fvarHead (decI e)) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hr⟩


/-! ## `close_lams` -/

mutual
/-- **The model of `close_lams`.** -/
def closeLamsW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, bo, bl, i, body =>
    if bl = 0 then some ([body], m)
    else clK1 bo i (closeLamsW n m (bo + 1) (bl - 1) (i + 1) body)

/-- After the recursive call: `abstract1_fast`. -/
def clK1 (bo i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => clK2 bo (abF m1 [CWF, r.headD 0, i, 0])

/-- After `abstract1_fast`: read the binder domain, `mk_lam`. -/
def clK2 (bo : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ra, m2) =>
    if bo.toNat < (m2.arr64 IW).size then
      clK3 (mkLamW m2 (rdW (m2.arr64 IW) bo) (ra.headD 0))
    else none

/-- After `mk_lam`. -/
def clK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m3) => if 4294967296 ≤ rb then none else some ([rb], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (bo bl i body rb : Word) (r ra : List Word)
theorem closeLamsW_nil (h : bl = 0) : closeLamsW (n + 1) m bo bl i body = some ([body], m) := by
  simp [closeLamsW, h]
theorem closeLamsW_cons (h : bl ≠ 0) : closeLamsW (n + 1) m bo bl i body =
    clK1 bo i (closeLamsW n m (bo + 1) (bl - 1) (i + 1) body) := by
  simp [closeLamsW, h]
theorem clK1_some : clK1 bo i (some (r, m1)) =
    clK2 bo (abF m1 [CWF, r.headD 0, i, 0]) := rfl
theorem clK2_oob (h : ¬ bo.toNat < (m2.arr64 IW).size) : clK2 bo (some (ra, m2)) = none := by
  simp [clK2, h]
theorem clK2_ok (h : bo.toNat < (m2.arr64 IW).size) : clK2 bo (some (ra, m2)) =
    clK3 (mkLamW m2 (rdW (m2.arr64 IW) bo) (ra.headD 0)) := by
  simp [clK2, h]
theorem clK3_big (h : 4294967296 ≤ rb) : clK3 (some (rb, m3)) = none := by simp [clK3, h]
theorem clK3_ok (h : ¬ 4294967296 ≤ rb) : clK3 (some (rb, m3)) = some ([rb], m3) := by
  simp [clK3, h]
end arms

grind_pattern [ind_grind] closeLamsW_nil => closeLamsW (n + 1) m bo bl i body
grind_pattern [ind_grind] closeLamsW_cons => closeLamsW (n + 1) m bo bl i body
grind_pattern [ind_grind] clK1_some => clK1 bo i (some (r, m1))
grind_pattern [ind_grind] clK2_oob => clK2 bo (some (ra, m2))
grind_pattern [ind_grind] clK2_ok => clK2 bo (some (ra, m2))
grind_pattern [ind_grind] clK3_big => clK3 (some (rb, m3))
grind_pattern [ind_grind] clK3_ok => clK3 (some (rb, m3))

theorem closeLams_spec (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "lam_find" = some lamFind) (hpp : p.lookup "lam_push" = some lamPush)
    (hpi : p.lookup "intern_lam" = some internLamL) (hml : p.lookup "mk_lam" = some mkLam)
    (hp : p.lookup "close_lams" = some closeLams) (hab : AbF p) (n : Nat) :
    ∀ (s₀ : St) (bo bl i body : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_lams" [bo, bl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ closeLamsW n s₀.mem bo bl i body = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ bo bl i body; rw [invoke_eq _ hp]; simp only [callFn, closeLams]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ bo bl i body
    rw [invoke_eq _ hp]
    simp only [callFn, closeLams]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        abF_spec p hab n, mkLam_spec p hd hpf hpp hpi hml n, ih] <;>
      finish (gen := 20)


theorem decHL_cons_r {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o (l + 1) = some xs) :
    ∃ x ys, xs = x :: ys ∧ decHL m (o + 1) l = some ys ∧ iwH m o = some x := by
  simp only [decHL, hslice?_succ] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨x, hx, ys, hxs, rfl⟩ := h
  exact ⟨x, ys, rfl, hxs, hx⟩

theorem closeLamsW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (bo bl i body : Word) (bs : List EIdx) (r : List Word),
    closeLamsW n m bo bl i body = some (r, m') → StageR dn vis fe m a → H body →
    decHL m bo.toNat bl.toNat = some bs → bo.toNat + bl.toNat < 2 ^ 64 →
    bo.toNat + bl.toNat ≤ iwTop m → i.toNat + bl.toNat < 2 ^ 64 → AbsOK m →
    ∃ x a', (ConRon.Arena.closeLams bs i.toNat (decI body)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x ∧
      AbsOK m' := by
  induction n with
  | zero => intro m m' a bo bl i body bs r h; simp [closeLamsW] at h
  | succ n ih =>
    intro m m' a bo bl i body bs r h hS hb hbs hbo hbt hib hA
    by_cases hbl : bl = 0
    · rw [closeLamsW_nil n m bo bl i body hbl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hl0 : bl.toNat = 0 := by rw [hbl]; rfl
      rw [hl0] at hbs
      simp [decHL, hslice?] at hbs
      subst hbs
      exact ⟨decI body, a, rfl, hS, IWGrow.refl m, by simpa using hb, rfl, hA⟩
    · rw [closeLamsW_cons n m bo bl i body hbl] at h
      obtain ⟨l1, hl1, hbl1⟩ := wordSucc_of_ne hbl
      rw [hl1] at hbs
      obtain ⟨dom, rest, rfl, hrest, hdom⟩ := decHL_cons_r hbs
      have hbo1 : (bo + 1).toNat = bo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      obtain ⟨⟨r1, m1⟩, hr, h⟩ := of_K h rfl
      rw [clK1_some] at h
      obtain ⟨x1, a1, hrun1, hS1, hg1, hd11, hd12, hA1⟩ := ih m m1 a (bo + 1) (bl - 1) (i + 1) body rest r1 hr hS hb
        (by rw [hbo1, hbl1]; exact hrest) (by omega) (by omega) (by omega) hA
      obtain ⟨⟨ra, m2⟩, ha, h⟩ := of_K h rfl
      obtain ⟨x2, a2, hrun2, ⟨hS2, hg2, hd21, hd22⟩, hA2⟩ :=
        abF_ok dn vis fe (r1.headD 0) i 0 hd11 m1 m2 a1 ra ha ⟨hS1, hA1⟩
      by_cases hoob : bo.toNat < (m2.arr64 IW).size
      · rw [clK2_ok m2 bo ra hoob] at h
        obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hdom (by omega)
        rw [UInt64.ofNat_toNat] at hw1
        have hrd : rdW (m2.arr64 IW) bo = w := by
          have e : (m2.arr64 IW)[bo.toNat]? = (m.arr64 IW)[bo.toNat]? := (hg1.trans hg2).2.2.1 bo.toNat (by omega)
          simp only [rdW] at hw1 ⊢; rw [e]; exact hw1
        rw [hrd] at h
        obtain ⟨⟨rb, m3⟩, hm, h⟩ := of_K h rfl
        by_cases hbig : 4294967296 ≤ rb
        · rw [clK3_big m3 rb hbig] at h; simp at h
        rw [clK3_ok m3 rb hbig] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨a3, hrun3, hS3, hg3⟩ := mkLam_stage hS2 w (ra.headD 0) hm
        have hlt : rb.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ rb.toNat := hbig; omega
        refine ⟨decE rb, a3, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa using hlt, by simp [decE_eq],
          mkLamW_afr hm hA2⟩
        rw [CWF_eq, show (0 : Word).toNat = 0 from rfl] at hrun2
        rw [hi1] at hrun1
        simp only [ConRon.Arena.closeLams, StateT.run_bind]
        rw [hrun1]
        simp only [bind, Except.bind]
        rw [← hd12, hrun2]
        simp only
        rw [← hw3, ← hd22]
        exact hrun3
      · rw [clK2_oob m2 bo ra hoob] at h; simp at h


/-- **`close_lams` refines `closeLams`** (through the `abstract1_fast` and `mk_lam` stubs). -/
@[refines ConRon.Arena.closeLams]
theorem closeLams_refines (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "lam_find" = some lamFind) (hpp : p.lookup "lam_push" = some lamPush)
    (hpi : p.lookup "intern_lam" = some internLamL) (hml : p.lookup "mk_lam" = some mkLam)
    (hp : p.lookup "close_lams" = some closeLams) (hab : AbF p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (bo bl i body : Word) (bs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hb : H body)
    (hbs : decHL s₀.mem bo.toNat bl.toNat = some bs) (hbo : bo.toNat + bl.toNat < 2 ^ 64)
    (hbt : bo.toNat + bl.toNat ≤ iwTop s₀.mem) (hib : i.toNat + bl.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_lams" [bo, bl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀ ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (closeLams_spec p hd hpf hpp hpi hml hp hab n s₀ bo bl i body) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, h1, h2, hA'⟩ := closeLamsW_ok dn vis fe n _ _ a₀ bo bl i body bs r hm hS hb
    hbs hbo hbt hib hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2, hA'⟩


/-! ## `class_rec_of` (the round-1 `while` rewritten as a self-recursion on the shifted slices) -/

/-- After the recursive call. -/
def croK : Option (List Word) → Option (List Word)
  | none => none
  | some r => some [r.headD 0, r.tail.headD 0]

/-- **The model of `class_rec_of`.** -/
def classRecOfW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, rco, rcl, cgo, cgl, t =>
    if cgl = 0 then some [0, 0]
    else if rcl ≠ 0 ∧ ¬ rco.toNat < (m.arr64 IW).size then none
    else if (if rcl ≠ 0 then rdW (m.arr64 IW) rco else 0) = t then
      (if cgo.toNat < (m.arr64 IW).size ∧ (rdW (m.arr64 IW) cgo).toNat < (m.arr64 EREC).size
        then some [1, rdW (m.arr64 EREC) (rdW (m.arr64 IW) cgo)] else none)
    else croK (classRecOfW n m (rco + 1) (if rcl ≠ 0 then rcl - 1 else 0) (cgo + 1) (cgl - 1) t)

section arms
variable (n : Nat) (m : Mem) (rco rcl cgo cgl t : Word)
theorem classRecOfW_nil (h : cgl = 0) : classRecOfW (n + 1) m rco rcl cgo cgl t = some [0, 0] := by
  simp [classRecOfW, h]
theorem classRecOfW_oob (h : cgl ≠ 0) (h1 : rcl ≠ 0) (h2 : ¬ rco.toNat < (m.arr64 IW).size) :
    classRecOfW (n + 1) m rco rcl cgo cgl t = none := by
  simp [classRecOfW, h, h1, h2]
theorem classRecOfW_hit (h : cgl ≠ 0) (h1 : rcl ≠ 0 → rco.toNat < (m.arr64 IW).size)
    (h2 : (if rcl ≠ 0 then rdW (m.arr64 IW) rco else 0) = t) :
    classRecOfW (n + 1) m rco rcl cgo cgl t =
      (if cgo.toNat < (m.arr64 IW).size ∧ (rdW (m.arr64 IW) cgo).toNat < (m.arr64 EREC).size
        then some [1, rdW (m.arr64 EREC) (rdW (m.arr64 IW) cgo)] else none) := by
  have : ¬ (rcl ≠ 0 ∧ ¬ rco.toNat < (m.arr64 IW).size) := fun ⟨a, b⟩ => b (h1 a)
  simp only [classRecOfW, h, this, h2, ite_false, ite_true]
theorem classRecOfW_miss (h : cgl ≠ 0) (h1 : rcl ≠ 0 → rco.toNat < (m.arr64 IW).size)
    (h2 : ¬ (if rcl ≠ 0 then rdW (m.arr64 IW) rco else 0) = t) :
    classRecOfW (n + 1) m rco rcl cgo cgl t =
      croK (classRecOfW n m (rco + 1) (if rcl ≠ 0 then rcl - 1 else 0) (cgo + 1) (cgl - 1) t) := by
  have : ¬ (rcl ≠ 0 ∧ ¬ rco.toNat < (m.arr64 IW).size) := fun ⟨a, b⟩ => b (h1 a)
  simp only [classRecOfW, h, this, h2, ite_false]
end arms

end L.Ind
