import ConAgua.Arena.IndSumSpec
import ConAgua.Arena.RecClass
import ConAgua.Arena.IndInstallSpec
import ConAgua.Arena.IndView
import ConAgua.Arena.IndMaster

/-!
# Refinements of `RecClass` (lane `induct`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

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
    cases hx : iwN m off with
    | none => simp [hx] at h
    | some x =>
      cases hxs : decNL m (off + 1) n with
      | none => simp [hx, hxs] at h
      | some xs =>
        simp [hx, hxs] at h
        subst h
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
    cases hw : (m.arr64 IW)[p + k]? with
    | none => simp [hw] at h
    | some w => exact (Array.getElem?_eq_some_iff.mp hw).1
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
  cases hp : iwN m o with
  | none => simp [hp] at h
  | some p =>
    cases hf : f p with
    | none => simp [hp, hf] at h
    | some x =>
      cases hr : decPL m f (o + 1) l with
      | none => simp [hp, hf, hr] at h
      | some ys =>
        simp [hp, hf, hr] at h
        exact ⟨p, x, ys, h.symm, rfl, hf, rfl⟩

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
        | none => [0, 0]; ⊤⦄ := by
  obtain ⟨ws, hws, rfl⟩ := slR_of_decNL s₀.mem _ _ _ hd hb
  simp only [UInt64.ofNat_toNat] at hws
  have hlen : ws.length < 2 ^ 64 := by
    have := decNL_length s₀.mem hd; simp at this; omega
  have key : ∀ r, findW n s₀.mem o l (pv - nP) = some r → nP ≤ pv →
      r = match ConRon.Arena.classOfMotiveVar nP.toNat (ws.map UInt64.toNat) pv.toNat with
        | some i => [1, UInt64.ofNat i]
        | none => [0, 0] := by
    intro r hr hle
    have hle' : nP.toNat ≤ pv.toNat := UInt64.le_iff_toNat_le.mp hle
    have hsub : (pv - nP).toNat = pv.toNat - nP.toNat := UInt64.toNat_sub_of_le _ _ hle
    rw [findW_ok n _ _ _ _ _ _ hws hr hlen]
    simp only [ConRon.Arena.classOfMotiveVar, hle', ite_true, ← hsub, findIdx_toNat]
    cases List.findIdx? (fun x => x == pv - nP) ws <;> rfl
  have key2 : pv < nP →
      ConRon.Arena.classOfMotiveVar nP.toNat (ws.map UInt64.toNat) pv.toNat = none := by
    intro h
    have : ¬ nP.toNat ≤ pv.toNat := by have := UInt64.lt_iff_toNat_lt.mp h; omega
    simp [ConRon.Arena.classOfMotiveVar, this]
  rw [invoke_eq _ hp]
  simp only [callFn, classOfMotiveVar]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, slFind_spec p hf n] <;>
    finish


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
    simp only [Option.some.injEq] at h
    subst h
    have : ¬ nP.toNat ≤ pv.toNat := by have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    simp [ConRon.Arena.classOfMotiveVar, this]
  · rw [cmvW_ge n m nP o l pv hlt] at h
    cases hr : findW n m o l (pv - nP) with
    | none => rw [hr] at h; simp [cmvK] at h
    | some r0 =>
      rw [hr, cmvK_some] at h
      simp only [Option.some.injEq] at h
      have hle' : nP.toNat ≤ pv.toNat := by
        have : ¬ pv.toNat < nP.toNat := fun hh => hlt (UInt64.lt_iff_toNat_lt.mpr hh)
        omega
      have hle : nP ≤ pv := UInt64.le_iff_toNat_le.mpr hle'
      have hsub : (pv - nP).toNat = pv.toNat - nP.toNat := UInt64.toNat_sub_of_le _ _ hle
      have hk := findW_ok n _ _ _ _ _ _ hws hr hlen
      subst h
      rw [hk]
      simp only [ConRon.Arena.classOfMotiveVar, hle', ite_true, ← hsub, findIdx_toNat]
      cases List.findIdx? (fun x => x == pv - nP) ws <;> rfl

/-! ## `class_binder`, `class_gen_binder`: one `fvar_type_d` call (through the stub) -/

/-- The word model of a one-call wrapper of `fvar_type_d`. -/
def fvarTypeDW1 (m : Mem) (x : Word) : Option (List Word × Mem) :=
  match stubM "fvar_type_d" m [x] with
  | none => none
  | some (r, m') => some ([r.headD 0], m')

theorem classBinder_spec (p : Prog) (hp : p.lookup "class_binder" = some classBinder) (n : Nat)
    (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_binder" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarTypeDW1 s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classBinder]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stubM_spec p "fvar_type_d" n] <;>
    finish [fvarTypeDW1]

theorem classGenBinder_spec (p : Prog) (hp : p.lookup "class_gen_binder" = some classGenBinder)
    (n : Nat) (s₀ : St) (g x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_binder" [g, x]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarTypeDW1 s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenBinder]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, stubM_spec p "fvar_type_d" n] <;>
    finish [fvarTypeDW1]

/-- The relational lemma of `fvarTypeDW1`. -/
theorem fvarTypeDW1_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (x : Word) (hx : H x) (r : List Word) (h : fvarTypeDW1 m x = some (r, m'))
    (hS : StageR dn vis fe m a) :
    ∃ t a', (fvarTypeD (decI x)).run a = .ok (t, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = t := by
  simp only [fvarTypeDW1] at h
  cases hs : stubM "fvar_type_d" m [x] with
  | none => rw [hs] at h; simp at h
  | some rm =>
    obtain ⟨r1, m1⟩ := rm
    rw [hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨t, a', hrun, hS', hg, hd1, hd2⟩ := fvarTypeD_spec dn vis fe x hx m m1 a r1 hs hS
    exact ⟨t, a', hrun, hS', hg, hd1, by simpa using hd2⟩

/-- **`class_binder` refines `classBinder`** (through the `fvar_type_d` stub). -/
@[refines ConRon.Arena.classBinder]
theorem classBinder_refines (p : Prog) (hp : p.lookup "class_binder" = some classBinder) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (x : Word)
    (hx : H x) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_binder" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classBinder (decI x)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classBinder (decI x)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.classBinder (decI x)) a₀; ⊤⦄ := by
  refine triple_post (classBinder_spec p hp n s₀ x) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨t, a', hrun, hS', hg, h1, h2⟩ := fvarTypeDW1_ok dn vis fe _ _ a₀ x hx r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.classBinder (decI x)) a₀ a' t hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩

/-- **`class_gen_binder` refines `ClassGen.binder`** (through the `fvar_type_d` stub). -/
@[refines ConRon.Arena.ClassGen.binder]
theorem classGenBinder_refines (p : Prog) (hp : p.lookup "class_gen_binder" = some classGenBinder)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (G : ClassGen) (g x : Word) (hx : H x) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_binder" [g, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.binder G (decI x)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.binder G (decI x)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.ClassGen.binder G (decI x)) a₀; ⊤⦄ := by
  refine triple_post (classGenBinder_spec p hp n s₀ g x) ?_
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
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
    cases hs : binternW m 0 with
    | none => rw [hs] at h; simp at h
    | some rm =>
      obtain ⟨r1, m1⟩ := rm
      rw [hs] at h
      by_cases hbig : 4294967296 ≤ r1
      · simp [hbig] at h
      simp only [hbig, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨a', hrun, hS', hg⟩ := internBVar_stage hS 0 hs
      have hge : l.toNat ≤ i.toNat := by
        have : ¬ i.toNat < l.toNat := fun h => hi (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have hlt : r1.toNat < 2 ^ 32 := by
        have : ¬ (4294967296 : Nat) ≤ r1.toNat := hbig
        omega
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
  match stubM "get_app_fn" m [CWF, e] with
  | none => none
  | some (r, m1) =>
    if r.headD 0 >>> 28 = 1 then
      (if eViewW m1 (r.headD 0) = [] then none
       else some ([1, (eViewW m1 (r.headD 0)).tail.headD 0], m1))
    else some ([0, 0], m1)

theorem fvarHead_spec (p : Prog) (hp : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ fvarHeadW s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, fvarHead]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "get_app_fn" n, eView_spec p hv n] <;>
      finish [fvarHeadW]

theorem viewFVarIdx_run' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewFVarIdx h).run a = .ok (a.store.viewFVarIdx h, a) := rfl

theorem eViewW_head1 (m : Mem) (w : Word) (hne : eViewW m w ≠ []) (hg : w >>> 28 = 1) :
    (eViewW m w).headD 0 = 1 := by
  unfold eViewW at hne ⊢
  simp (config := {decide := true}) only [hg, ite_true, ite_false] at hne ⊢
  by_cases c1 : 4294967295 < w
  · simp [c1] at hne
  by_cases c2 : tierW w ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  by_cases c3 : rdW (m.arr64 CTL) (26 + tierW w) ≤ idxW w
  · simp [c1, c2, c3] at hne
  simp [c1, c2, c3]

theorem fvarHeadW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (e : Word) (he : H e) (r : List Word) (h : fvarHeadW m e = some (r, m'))
    (hS : StageR dn vis fe m a) :
    ∃ x a', (ConRon.Arena.fvarHead (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ r = (match x with | some i => [1, UInt64.ofNat i] | none => [0, 0]) ∧
      (∀ i, x = some i → i < 2 ^ 64) := by
  simp only [fvarHeadW] at h
  cases hs : stubM "get_app_fn" m [CWF, e] with
  | none => rw [hs] at h; simp at h
  | some rm =>
    obtain ⟨r1, m1⟩ := rm
    rw [hs] at h
    simp only at h
    obtain ⟨t, a1, hrun1, hS1, hg1, hd1, hd2⟩ := getAppFn_spec dn vis fe CWF e he m m1 a r1 hs hS
    rw [CWF_eq] at hrun1
    generalize r1.headD 0 = w at hd1 hd2 h
    by_cases hf : w >>> 28 = 1
    · rw [if_pos hf] at h
      by_cases hne : eViewW m1 w = []
      · rw [if_pos hne] at h; simp at h
      rw [if_neg hne] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨v, hv, hR⟩ := eViewW_ok m1 a1 hS1.1.arena.1 w hne
      have htag : (decE w).tag = ETag.fvar := by
        rw [decE_tag w hd1, hf]; rfl
      cases v with
      | fvar k ty =>
        simp only [ViewR] at hR
        have hk := EStore.viewFVarIdx_of_view _ _ _ _ hv
        refine ⟨some k, a1, ?_, hS1, hg1, ?_, fun i hi => ?_⟩
        · simp only [ConRon.Arena.fvarHead]
          rw [StateT.run_bind, hrun1]
          simp only [bind, Except.bind]
          rw [← hd2]
          have : (decI w : EIdx) = decE w := rfl
          rw [this]
          simp only [htag, beq_self_eq_true, ite_true]
          have e1 : (ConRon.Arena.viewFVarIdx (decE w)).run a1 = .ok (some k, a1) := by
            rw [viewFVarIdx_run', hk]
          simp only [StateT.run] at e1 ⊢
          simp only [StateT.bind, e1, bind, Except.bind]
          rfl
        · have e2 : (eViewW m1 w).tail.headD 0 = (eViewW m1 w).getD 1 0 := by
            cases eViewW m1 w with
            | nil => simp
            | cons x xs => cases xs <;> simp
          simp only [e2, ← hR.2.1, UInt64.ofNat_toNat]
        · simp only [Option.some.injEq] at hi
          rw [← hi, ← hR.2.1]; exact UInt64.toNat_lt _
      | bvar i => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | sort u => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | const n us => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | app f x => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | lam f x => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | forallE f x => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | letE f x y => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | lit l => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
      | proj f x y => have := eViewW_head1 m1 w hne hf; simp only [ViewR] at hR; first | exact absurd (this.symm.trans hR) (by decide) | exact absurd (this.symm.trans hR.1) (by decide)
    · rw [if_neg hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
      rw [← hd2]
      have : (decI w : EIdx) = decE w := rfl
      rw [this]
      have htag' : ((decE w).tag == ETag.fvar) = false := by simpa using htag
      simp only [htag', Bool.false_eq_true, ite_false]
      rfl


/-- **`fvar_head` refines `fvarHead`** (through the `get_app_fn` stub and `e_view`). -/
@[refines ConRon.Arena.fvarHead]
theorem fvarHead_refines (p : Prog) (hp : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e : Word) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.fvarHead (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.fvarHead (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      r = (match AM.res (ConRon.Arena.fvarHead (decI e)) a₀ with
        | some i => [1, UInt64.ofNat i] | none => [0, 0]); ⊤⦄ := by
  refine triple_post (fvarHead_spec p hp hv n s₀ e) ?_
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
  | some (r, m1) => clK2 bo (stubM "abstract1_fast" m1 [CWF, r.headD 0, i, 0])

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
    clK2 bo (stubM "abstract1_fast" m1 [CWF, r.headD 0, i, 0]) := rfl
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
    (hp : p.lookup "close_lams" = some closeLams) (n : Nat) :
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
        stubM_spec p "abstract1_fast" n, mkLam_spec p hd hpf hpp hpi hml n, ih] <;>
      finish (gen := 20)


theorem decHL_cons_r {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o (l + 1) = some xs) :
    ∃ x ys, xs = x :: ys ∧ decHL m (o + 1) l = some ys ∧ iwH m o = some x := by
  simp only [decHL, hslice?_succ] at h
  cases hx : (hd? (iwA m) o : Option (Idx k)) with
  | none => simp [hx] at h
  | some x =>
    cases hxs : (hslice? (iwA m) (o + 1) l : Option (List (Idx k))) with
    | none => simp [hx, hxs] at h
    | some ys =>
      simp [hx, hxs] at h
      exact ⟨x, ys, h.symm, hxs, hx⟩

theorem closeLamsW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (bo bl i body : Word) (bs : List EIdx) (r : List Word),
    closeLamsW n m bo bl i body = some (r, m') → StageR dn vis fe m a → H body →
    decHL m bo.toNat bl.toNat = some bs → bo.toNat + bl.toNat < 2 ^ 64 →
    bo.toNat + bl.toNat ≤ iwTop m → i.toNat + bl.toNat < 2 ^ 64 →
    ∃ x a', (ConRon.Arena.closeLams bs i.toNat (decI body)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decI (r.headD 0) = x := by
  induction n with
  | zero => intro m m' a bo bl i body bs r h; simp [closeLamsW] at h
  | succ n ih =>
    intro m m' a bo bl i body bs r h hS hb hbs hbo hbt hib
    by_cases hbl : bl = 0
    · rw [closeLamsW_nil n m bo bl i body hbl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl0 : bl.toNat = 0 := by rw [hbl]; rfl
      rw [hl0] at hbs
      simp [decHL, hslice?] at hbs
      subst hbs
      exact ⟨decI body, a, rfl, hS, IWGrow.refl m, by simpa using hb, rfl⟩
    · rw [closeLamsW_cons n m bo bl i body hbl] at h
      have hlpos : 1 ≤ bl.toNat := by
        rcases Nat.eq_zero_or_pos bl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hbl
        · omega
      obtain ⟨l1, hl1⟩ : ∃ l1, bl.toNat = l1 + 1 := ⟨bl.toNat - 1, by omega⟩
      rw [hl1] at hbs
      obtain ⟨dom, rest, rfl, hrest, hdom⟩ := decHL_cons_r hbs
      have hbl1 : (bl - 1).toNat = l1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hlpos))]; simp; omega
      have hbo1 : (bo + 1).toNat = bo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      cases hr : closeLamsW n m (bo + 1) (bl - 1) (i + 1) body with
      | none => rw [hr] at h; simp [clK1] at h
      | some rm =>
        obtain ⟨r1, m1⟩ := rm
        rw [hr, clK1_some] at h
        obtain ⟨x1, a1, hrun1, hS1, hg1, hd11, hd12⟩ := ih m m1 a (bo + 1) (bl - 1) (i + 1) body rest r1 hr hS hb
          (by rw [hbo1, hbl1]; exact hrest) (by omega) (by omega) (by omega)
        cases ha : stubM "abstract1_fast" m1 [CWF, r1.headD 0, i, 0] with
        | none => rw [ha] at h; simp [clK2] at h
        | some ram =>
          obtain ⟨ra, m2⟩ := ram
          rw [ha] at h
          obtain ⟨x2, a2, hrun2, hS2, hg2, hd21, hd22⟩ :=
            abstract1Fast_spec dn vis fe CWF (r1.headD 0) i 0 hd11 m1 m2 a1 ra ha hS1
          by_cases hoob : bo.toNat < (m2.arr64 IW).size
          · rw [clK2_ok m2 bo ra hoob] at h
            obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hdom (by omega)
            rw [UInt64.ofNat_toNat] at hw1
            have hrd : rdW (m2.arr64 IW) bo = w := by
              have hg := hg1.trans hg2
              have := hg.2.2.1 bo.toNat (by omega)
              simp only [rdW] at this hw1 ⊢
              have e : (m2.arr64 IW)[bo.toNat]? = (m.arr64 IW)[bo.toNat]? := this
              rw [e]; exact hw1
            rw [hrd] at h
            cases hm : mkLamW m2 w (ra.headD 0) with
            | none => rw [hm] at h; simp [clK3] at h
            | some rbm =>
              obtain ⟨rb, m3⟩ := rbm
              rw [hm] at h
              by_cases hbig : 4294967296 ≤ rb
              · rw [clK3_big m3 rb hbig] at h; simp at h
              rw [clK3_ok m3 rb hbig] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨a3, hrun3, hS3, hg3⟩ := mkLam_stage hS2 w (ra.headD 0) hm
              have hlt : rb.toNat < 2 ^ 32 := by
                have : ¬ (4294967296 : Nat) ≤ rb.toNat := hbig
                omega
              refine ⟨decE rb, a3, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa using hlt, by simp [decE_eq]⟩
              rw [CWF_eq] at hrun2
              have hz : (0 : Word).toNat = 0 := rfl
              rw [hz] at hrun2
              rw [hi1] at hrun1
              simp only [ConRon.Arena.closeLams, StateT.run_bind]
              rw [hrun1]
              simp only [bind, Except.bind]
              rw [← hd12, hrun2]
              simp only [bind, Except.bind]
              rw [← hw3, ← hd22]
              exact hrun3
          · rw [clK2_oob m2 bo ra hoob] at h; simp at h


/-- **`close_lams` refines `closeLams`** (through the `abstract1_fast` and `mk_lam` stubs). -/
@[refines ConRon.Arena.closeLams]
theorem closeLams_refines (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "lam_find" = some lamFind) (hpp : p.lookup "lam_push" = some lamPush)
    (hpi : p.lookup "intern_lam" = some internLamL) (hml : p.lookup "mk_lam" = some mkLam)
    (hp : p.lookup "close_lams" = some closeLams) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (bo bl i body : Word) (bs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hb : H body)
    (hbs : decHL s₀.mem bo.toNat bl.toNat = some bs) (hbo : bo.toNat + bl.toNat < 2 ^ 64)
    (hbt : bo.toNat + bl.toNat ≤ iwTop s₀.mem) (hib : i.toNat + bl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_lams" [bo, bl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = AM.res (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀; ⊤⦄ := by
  refine triple_post (closeLams_spec p hd hpf hpp hpi hml hp n s₀ bo bl i body) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, h1, h2⟩ := closeLamsW_ok dn vis fe n _ _ a₀ bo bl i body bs r hm hS hb
    hbs hbo hbt hib
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.closeLams bs i.toNat (decI body)) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, h1, by rw [hres]; exact h2⟩


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
  simp only [classRecOfW, h, this, h2, if_false, if_true]
theorem classRecOfW_miss (h : cgl ≠ 0) (h1 : rcl ≠ 0 → rco.toNat < (m.arr64 IW).size)
    (h2 : ¬ (if rcl ≠ 0 then rdW (m.arr64 IW) rco else 0) = t) :
    classRecOfW (n + 1) m rco rcl cgo cgl t =
      croK (classRecOfW n m (rco + 1) (if rcl ≠ 0 then rcl - 1 else 0) (cgo + 1) (cgl - 1) t) := by
  have : ¬ (rcl ≠ 0 ∧ ¬ rco.toNat < (m.arr64 IW).size) := fun ⟨a, b⟩ => b (h1 a)
  simp only [classRecOfW, h, this, h2, if_false, if_true]
end arms

grind_pattern [ind_grind] classRecOfW_nil => classRecOfW (n + 1) m rco rcl cgo cgl t
grind_pattern [ind_grind] classRecOfW_oob => classRecOfW (n + 1) m rco rcl cgo cgl t
grind_pattern [ind_grind] classRecOfW_hit => classRecOfW (n + 1) m rco rcl cgo cgl t
grind_pattern [ind_grind] classRecOfW_miss => classRecOfW (n + 1) m rco rcl cgo cgl t

theorem classRecOf_spec (p : Prog) (hp : p.lookup "class_rec_of" = some classRecOf) (n : Nat) :
    ∀ (s₀ : St) (rco rcl cgo cgl t : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_of" [rco, rcl, cgo, cgl, t]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ classRecOfW n s₀.mem rco rcl cgo cgl t = some r; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ rco rcl cgo cgl t; rw [invoke_eq _ hp]; simp only [callFn, classRecOf]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ rco rcl cgo cgl t
    rw [invoke_eq _ hp]
    simp only [callFn, classRecOf]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [croK]


/-- The twin's `classRecOf`, as a recursion on the shifted lists. -/
def crOf (t : Nat) : List Nat → List IConstantVal → Option NIdx
  | _, [] => none
  | rc, cv :: cs => if rc.headD 0 == t then some cv.name else crOf t rc.tail cs

theorem crOf_eq (t : Nat) : ∀ (cs : List IConstantVal) (rc : List Nat),
    ((List.range cs.length).find? fun r => rc.getD r 0 == t).map (fun r => (cs.getD r default).name) =
      crOf t rc cs := by
  intro cs
  induction cs with
  | nil => intro rc; simp [crOf]
  | cons cv cs ih =>
    intro rc
    have e0 : rc.getD 0 0 = rc.headD 0 := by cases rc <;> simp
    have e1 : ∀ r, rc.getD (r + 1) 0 = rc.tail.getD r 0 := by intro r; cases rc <;> simp
    rw [List.length_cons, List.range_succ_eq_map, List.find?_cons, e0]
    by_cases h : (rc.headD 0 == t) = true
    · simp only [h, crOf, ite_true, Option.map_some]; rfl
    · have h' : ¬ (rc.headD 0 == t) = true := h
      simp only [h', crOf, Bool.false_eq_true, if_false]
      rw [← ih rc.tail, List.find?_map]
      simp only [Option.map_map, Function.comp_def, e1, List.getD_cons_succ]


theorem decCVp_name {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv) :
    ∃ w, (m.arr64 EREC)[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = cv.name := by
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨nm, hnm, -, -, -, -, -, rfl⟩ := h
  simp only [hd?] at hnm
  cases hq : (erA m)[q]? with
  | none => simp [hq] at hnm
  | some w =>
    simp only [hq, Option.bind_some] at hnm
    by_cases hl : w.toNat < 2 ^ 32
    · simp [hl] at hnm
      exact ⟨w, by simpa [erA] using hq, hl, hnm⟩
    · simp [hl] at hnm

theorem classRecOfW_ok (n : Nat) : ∀ (m : Mem) (rco rcl cgo cgl t : Word) (r : List Word)
    (rc : List Nat) (cs : List IConstantVal),
    classRecOfW n m rco rcl cgo cgl t = some r → decNL m rco.toNat rcl.toNat = some rc →
    decPL m (decCVp m) cgo.toNat cgl.toNat = some cs → rco.toNat + rcl.toNat < 2 ^ 64 →
    cgo.toNat + cgl.toNat < 2 ^ 64 →
    (crOf t.toNat rc cs = none → r = [0, 0]) ∧
    ∀ nm, crOf t.toNat rc cs = some nm → r.headD 0 = 1 ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.headD 0) = nm := by
  induction n with
  | zero => intro m rco rcl cgo cgl t r rc cs h; simp [classRecOfW] at h
  | succ n ih =>
    intro m rco rcl cgo cgl t r rc cs h hrc hcs hb1 hb2
    by_cases hcgl : cgl = 0
    · rw [classRecOfW_nil n m rco rcl cgo cgl t hcgl] at h
      simp only [Option.some.injEq] at h
      subst h
      have : cgl.toNat = 0 := by rw [hcgl]; rfl
      rw [this] at hcs
      simp [decPL] at hcs
      subst hcs
      exact ⟨fun _ => rfl, fun nm hnm => by simp [crOf] at hnm⟩
    · have hpos : 1 ≤ cgl.toNat := by
        rcases Nat.eq_zero_or_pos cgl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hcgl
        · omega
      obtain ⟨c1, hc1⟩ : ∃ c1, cgl.toNat = c1 + 1 := ⟨cgl.toNat - 1, by omega⟩
      rw [hc1] at hcs
      obtain ⟨pn, cv, cs', rfl, hpn, hcv, hcs'⟩ := decPL_cons hcs
      have hgo : cgo.toNat < (m.arr64 IW).size := iwN_lt hpn
      have hpn' := iwN_rdW hpn (by omega)
      rw [UInt64.ofNat_toNat] at hpn'
      obtain ⟨wn, hwn1, hwn2, hwn3⟩ := decCVp_name hcv
      have hcgl1 : (cgl - 1).toNat = c1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
      have hcgo1 : (cgo + 1).toNat = cgo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      -- the first recursion-count entry and the shifted slice
      obtain ⟨v, rc', P1, P2, P3, P4, P5, P6⟩ : ∃ (v : Word) (rc' : List Nat),
          (if rcl ≠ 0 then rdW (m.arr64 IW) rco else 0) = v ∧
          (rcl ≠ 0 → rco.toNat < (m.arr64 IW).size) ∧ rc.headD 0 = v.toNat ∧ rc.tail = rc' ∧
          decNL m (rco + 1).toNat (if rcl ≠ 0 then rcl - 1 else 0).toNat = some rc' ∧
          (rco + 1).toNat + (if rcl ≠ 0 then rcl - 1 else 0).toNat < 2 ^ 64 := by
        by_cases hrcl : rcl = 0
        · have hr0 : rcl.toNat = 0 := by rw [hrcl]; rfl
          rw [hr0] at hrc
          simp [decNL] at hrc
          subst hrc
          refine ⟨0, [], by simp [hrcl], fun h => absurd hrcl h, by simp, by simp, ?_, ?_⟩
          · simp [hrcl, decNL]
          · simp [hrcl]; omega
        · have hpos' : 1 ≤ rcl.toNat := by
            rcases Nat.eq_zero_or_pos rcl.toNat with h0 | h0
            · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hrcl
            · omega
          obtain ⟨r1, hr1⟩ : ∃ r1, rcl.toNat = r1 + 1 := ⟨rcl.toNat - 1, by omega⟩
          rw [hr1, decNL_succ] at hrc
          cases hx : iwN m rco.toNat with
          | none => simp [hx] at hrc
          | some x =>
            cases hxs : decNL m (rco.toNat + 1) r1 with
            | none => simp [hx, hxs] at hrc
            | some xs =>
              simp [hx, hxs] at hrc
              subst hrc
              have hx' := iwN_rdW hx (by omega)
              rw [UInt64.ofNat_toNat] at hx'
              have hrcl1 : (rcl - 1).toNat = r1 := by
                rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos'))]; simp; omega
              have hrco1 : (rco + 1).toNat = rco.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
              refine ⟨UInt64.ofNat x, xs, by simp [hrcl, hx'.1], fun _ => iwN_lt hx, ?_, rfl, ?_, ?_⟩
              · rw [UInt64.toNat_ofNat_of_lt' hx'.2]; rfl
              · simp only [hrcl, ne_eq, not_false_eq_true, if_true, hrco1, hrcl1]; exact hxs
              · simp only [hrcl, ne_eq, not_false_eq_true, if_true, hrco1, hrcl1]; omega
      have hxv : (v = t) ↔ (rc.headD 0 == t.toNat) = true := by
        rw [P3]
        constructor
        · intro e; subst e; simp
        · intro e; simp at e; exact UInt64.toNat_inj.mp e
      have hcrOf : crOf t.toNat rc (cv :: cs') =
          if (rc.headD 0 == t.toNat) = true then some cv.name else crOf t.toNat rc' cs' := by
        simp only [crOf, P4]
      by_cases hvt : v = t
      · rw [classRecOfW_hit n m rco rcl cgo cgl t hcgl P2 (by rw [P1]; exact hvt)] at h
        have hpe : pn < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hwn1).1
        have hg : cgo.toNat < (m.arr64 IW).size ∧
            (rdW (m.arr64 IW) cgo).toNat < (m.arr64 EREC).size := by
          refine ⟨hgo, ?_⟩
          have e : (m.arr64 IW)[cgo.toNat]? = some (UInt64.ofNat pn) := by
            have := hpn'.1
            simpa [rdW, hgo] using this
          rw [hpn'.1, UInt64.toNat_ofNat_of_lt' hpn'.2]; exact hpe
        rw [if_pos hg] at h
        simp only [Option.some.injEq] at h
        subst h
        have hrd : rdW (m.arr64 EREC) (rdW (m.arr64 IW) cgo) = wn := by
          rw [hpn'.1]
          simp [rdW, UInt64.toNat_ofNat_of_lt' hpn'.2, hwn1]
        rw [hrd, hcrOf, if_pos (hxv.mp hvt)]
        refine ⟨fun e => by simp at e, fun nm hnm => ?_⟩
        simp only [Option.some.injEq] at hnm
        subst hnm
        exact ⟨rfl, by simpa using hwn2, by simpa using hwn3⟩
      · rw [classRecOfW_miss n m rco rcl cgo cgl t hcgl P2 (by rw [P1]; exact hvt)] at h
        cases hr : classRecOfW n m (rco + 1) (if rcl ≠ 0 then rcl - 1 else 0) (cgo + 1) (cgl - 1) t with
        | none => rw [hr] at h; simp [croK] at h
        | some r1 =>
          rw [hr] at h
          simp only [croK, Option.some.injEq] at h
          subst h
          have hcs'' : decPL m (decCVp m) (cgo + 1).toNat (cgl - 1).toNat = some cs' := by
            rw [hcgo1, hcgl1]; exact hcs'
          obtain ⟨g1, g2⟩ := ih m (rco + 1) _ (cgo + 1) (cgl - 1) t r1 rc' cs' hr P5 hcs'' P6
            (by rw [hcgo1, hcgl1]; omega)
          have hn : ¬ (rc.headD 0 == t.toNat) = true := fun e => hvt (hxv.mpr e)
          rw [hcrOf, if_neg hn]
          refine ⟨fun e => ?_, fun nm hnm => ?_⟩
          · have := g1 e; simp [this]
          · obtain ⟨a1, a2, a3⟩ := g2 nm hnm
            exact ⟨a1, a2, a3⟩


/-- **`class_rec_of` refines `classRecOf`**: `(1, name)` for `some name`, `(0, 0)` for `none`; the
memory is unchanged. -/
@[refines ConRon.Arena.classRecOf]
theorem classRecOf_refines (p : Prog) (hp : p.lookup "class_rec_of" = some classRecOf) (n : Nat)
    (s₀ : St) (rco rcl cgo cgl t : Word) (rc : List Nat) (cs : List IConstantVal)
    (hrc : decNL s₀.mem rco.toNat rcl.toNat = some rc)
    (hcs : decPL s₀.mem (decCVp s₀.mem) cgo.toNat cgl.toNat = some cs)
    (hb1 : rco.toNat + rcl.toNat < 2 ^ 64) (hb2 : cgo.toNat + cgl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_of" [rco, rcl, cgo, cgl, t]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (match ConRon.Arena.classRecOf rc cs t.toNat with
        | none => r = [0, 0]
        | some nm => r.headD 0 = 1 ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧ decI (r.tail.headD 0) = nm);
      ⊤⦄ := by
  refine triple_post (classRecOf_spec p hp n s₀ rco rcl cgo cgl t) ?_
  rintro r s' ⟨hl, hm, hw⟩
  obtain ⟨g1, g2⟩ := classRecOfW_ok n _ rco rcl cgo cgl t r rc cs hw hrc hcs hb1 hb2
  refine ⟨hl, hm, ?_⟩
  have e := crOf_eq t.toNat cs rc
  simp only [ConRon.Arena.classRecOf] at *
  rw [e]
  cases hc : crOf t.toNat rc cs with
  | none => exact g1 hc
  | some nm => exact g2 nm hc


/-! ## `class_read_motive_slot` (the `while` rewritten as a self-recursion on the shifted slice) -/

/-- After the recursive call: shift the position. -/
def msK : Option (List Word) → Option (List Word)
  | none => none
  | some r => if r.headD 0 = 0 then some [0, 0] else some [1, r.tail.headD 0 + 1]

/-- **The model of `class_read_motive_slot`.** -/
def msW : Nat → Mem → Word → Word → Word → Option (List Word)
  | 0, _, _, _, _ => none
  | n + 1, m, so, sl, c =>
    if sl = 0 then some [0, 0]
    else if ¬ so.toNat < (m.arr64 IW).size then none
    else if ¬ (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size then none
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = 0 then
      (if c = 0 then some [1, 0] else msK (msW n m (so + 1) (sl - 1) (c - 1)))
    else msK (msW n m (so + 1) (sl - 1) c)

section arms
variable (n : Nat) (m : Mem) (so sl c : Word)
theorem msW_nil (h : sl = 0) : msW (n + 1) m so sl c = some [0, 0] := by simp [msW, h]
theorem msW_oob1 (h : sl ≠ 0) (h1 : ¬ so.toNat < (m.arr64 IW).size) : msW (n + 1) m so sl c = none := by
  simp [msW, h, h1]
theorem msW_oob2 (h : sl ≠ 0) (h1 : so.toNat < (m.arr64 IW).size)
    (h2 : ¬ (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size) : msW (n + 1) m so sl c = none := by
  simp [msW, h, h1, h2]
theorem msW_hit (h : sl ≠ 0) (h1 : so.toNat < (m.arr64 IW).size)
    (h2 : (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size) (h3 : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = 0)
    (hc : c = 0) : msW (n + 1) m so sl c = some [1, 0] := by
  simp [msW, h, h1, h2, h3, hc]
theorem msW_mot (h : sl ≠ 0) (h1 : so.toNat < (m.arr64 IW).size)
    (h2 : (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size) (h3 : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = 0)
    (hc : c ≠ 0) : msW (n + 1) m so sl c = msK (msW n m (so + 1) (sl - 1) (c - 1)) := by
  simp [msW, h, h1, h2, h3, hc]
theorem msW_min (h : sl ≠ 0) (h1 : so.toNat < (m.arr64 IW).size)
    (h2 : (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size) (h3 : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) ≠ 0) :
    msW (n + 1) m so sl c = msK (msW n m (so + 1) (sl - 1) c) := by
  simp [msW, h, h1, h2, h3]
end arms

grind_pattern [ind_grind] msW_nil => msW (n + 1) m so sl c
grind_pattern [ind_grind] msW_oob1 => msW (n + 1) m so sl c
grind_pattern [ind_grind] msW_oob2 => msW (n + 1) m so sl c
grind_pattern [ind_grind] msW_hit => msW (n + 1) m so sl c
grind_pattern [ind_grind] msW_mot => msW (n + 1) m so sl c
grind_pattern [ind_grind] msW_min => msW (n + 1) m so sl c

theorem classReadMotiveSlot_spec (p : Prog) (hp : p.lookup "class_read_motive_slot" = some classReadMotiveSlot)
    (n : Nat) : ∀ (s₀ : St) (so sl c : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_motive_slot" [so, sl, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ msW n s₀.mem so sl c = some r; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ so sl c; rw [invoke_eq _ hp]; simp only [callFn, classReadMotiveSlot]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ so sl c
    rw [invoke_eq _ hp]
    simp only [callFn, classReadMotiveSlot]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [msK]


/-- The indices of the motive slots, counted from `j`. -/
def motIdx : Nat → List ClassSlot → List Nat
  | _, [] => []
  | j, .motive _ :: sls => j :: motIdx (j + 1) sls
  | j, .minor .. :: sls => motIdx (j + 1) sls

theorem motIdx_shift : ∀ (sls : List ClassSlot) (j : Nat), motIdx (j + 1) sls = (motIdx j sls).map (· + 1) := by
  intro sls
  induction sls with
  | nil => intro j; simp [motIdx]
  | cons sl sls ih =>
    intro j
    cases sl with
    | motive k => simp [motIdx, ih (j + 1)]
    | minor c C ihs => simp [motIdx, ih (j + 1)]

theorem motIdx_eq : ∀ (j : Nat) (sls : List ClassSlot),
    ((List.range sls.length).filter (fun s => match (sls[s]? : Option ClassSlot) with
      | some (.motive _) => true
      | _ => false)).map (j + ·) = motIdx j sls := by
  intro j sls
  induction sls generalizing j with
  | nil => simp [motIdx]
  | cons sl sls ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have e : (fun s : Nat => match ((sl :: sls)[s]? : Option ClassSlot) with
        | some (.motive _) => true | _ => false) ∘ Nat.succ =
        (fun s : Nat => match (sls[s]? : Option ClassSlot) with
        | some (.motive _) => true | _ => false) := by
      funext s; simp
    rw [e]
    have ih' := ih (j + 1)
    have e2 : ∀ L : List Nat, (L.map Nat.succ).map (j + ·) = L.map ((j + 1) + ·) := by
      intro L; simp [List.map_map, Function.comp_def]; intro x _; omega
    cases sl with
    | motive k => simp [motIdx, e2, ih']
    | minor c C ihs => simp [motIdx, e2, ih']


/-- The result words of a motive-position query. -/
def msRes : Option Nat → List Word
  | some i => [1, UInt64.ofNat i]
  | none => [0, 0]

theorem msK_of (o : Option Nat) (r1 : List Word) (h : r1 = msRes o) :
    msK (some r1) = some (msRes (o.map (· + 1))) := by
  subst h
  cases o <;> simp [msK, msRes, UInt64.ofNat_add]

theorem msW_ok (n : Nat) : ∀ (m : Mem) (so sl c : Word) (r : List Word) (sls : List ClassSlot),
    msW n m so sl c = some r → decPL m (decCS m) so.toNat sl.toNat = some sls →
    so.toNat + sl.toNat < 2 ^ 64 → r = msRes ((motIdx 0 sls)[c.toNat]?) := by
  induction n with
  | zero => intro m so sl c r sls h; simp [msW] at h
  | succ n ih =>
    intro m so sl c r sls h hdec hb
    by_cases hsl : sl = 0
    · rw [msW_nil n m so sl c hsl] at h
      simp only [Option.some.injEq] at h
      subst h
      have : sl.toNat = 0 := by rw [hsl]; rfl
      rw [this] at hdec
      simp [decPL] at hdec
      subst hdec
      simp [motIdx, msRes]
    · have hpos : 1 ≤ sl.toNat := by
        rcases Nat.eq_zero_or_pos sl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hsl
        · omega
      obtain ⟨s1, hs1⟩ : ∃ s1, sl.toNat = s1 + 1 := ⟨sl.toNat - 1, by omega⟩
      rw [hs1] at hdec
      obtain ⟨pn, sl', rest, rfl, hpn, hcs, hdec'⟩ := decPL_cons hdec
      have hso : so.toNat < (m.arr64 IW).size := iwN_lt hpn
      have hpn' := iwN_rdW hpn (by omega)
      rw [UInt64.ofNat_toNat] at hpn'
      have hpsz := decCS_ptr_lt hcs
      have htag := decCS_tag hcs
      have htag' := iwN_rdW htag (by have := hpn'.2; omega)
      have hpl : (rdW (m.arr64 IW) so).toNat < (m.arr64 IW).size := by
        rw [hpn'.1, UInt64.toNat_ofNat_of_lt' hpn'.2]; exact hpsz
      have hsl1 : (sl - 1).toNat = s1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
      have hso1 : (so + 1).toNat = so.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hdec1 : decPL m (decCS m) (so + 1).toNat (sl - 1).toNat = some rest := by
        rw [hso1, hsl1]; exact hdec'
      have hrd : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = UInt64.ofNat (if sl'.isMinor then 1 else 0) := by
        rw [hpn'.1]; exact htag'.1
      cases sl' with
      | motive k =>
        have hz : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) = 0 := by rw [hrd]; rfl
        by_cases hc : c = 0
        · rw [msW_hit n m so sl c hsl hso hpl hz hc] at h
          simp only [Option.some.injEq] at h
          subst h
          have : c.toNat = 0 := by rw [hc]; rfl
          simp [motIdx, this, msRes]
        · rw [msW_mot n m so sl c hsl hso hpl hz hc] at h
          cases hr : msW n m (so + 1) (sl - 1) (c - 1) with
          | none => rw [hr] at h; simp [msK] at h
          | some r1 =>
            rw [hr] at h
            have hc1 : (c - 1).toNat = c.toNat - 1 := by
              have : c.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
              rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
            have g := ih m (so + 1) (sl - 1) (c - 1) r1 rest hr hdec1 (by rw [hso1, hsl1]; omega)
            rw [msK_of _ r1 g] at h
            simp only [Option.some.injEq] at h
            subst h
            have hcne : c.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
            obtain ⟨c', hc'⟩ : ∃ c', c.toNat = c' + 1 := ⟨c.toNat - 1, by omega⟩
            rw [hc1, hc'] at *
            simp only [motIdx, motIdx_shift, List.getElem?_cons_succ, List.getElem?_map, Nat.add_sub_cancel]
      | minor c0 C0 ihs =>
        have hnz : rdW (m.arr64 IW) (rdW (m.arr64 IW) so) ≠ 0 := by
          rw [hrd]; simp [ClassSlot.isMinor]
        rw [msW_min n m so sl c hsl hso hpl hnz] at h
        cases hr : msW n m (so + 1) (sl - 1) c with
        | none => rw [hr] at h; simp [msK] at h
        | some r1 =>
          rw [hr] at h
          have g := ih m (so + 1) (sl - 1) c r1 rest hr hdec1 (by rw [hso1, hsl1]; omega)
          rw [msK_of _ r1 g] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [motIdx, motIdx_shift, List.getElem?_map]


/-- **`class_read_motive_slot` refines `ClassRead.motiveSlot`**: `(1, i)` for `some i`, `(0, 0)` for
`none`; memory unchanged. -/
@[refines ConRon.Arena.ClassRead.motiveSlot]
theorem classReadMotiveSlot_refines (p : Prog)
    (hp : p.lookup "class_read_motive_slot" = some classReadMotiveSlot) (n : Nat) (s₀ : St)
    (so sl c : Word) (sls : List ClassSlot) (hdec : decPL s₀.mem (decCS s₀.mem) so.toNat sl.toNat = some sls)
    (hb : so.toNat + sl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_motive_slot" [so, sl, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      r = msRes (ConRon.Arena.ClassRead.motiveSlot sls c.toNat); ⊤⦄ := by
  refine triple_post (classReadMotiveSlot_spec p hp n s₀ so sl c) ?_
  rintro r s' ⟨hl, hm, hw⟩
  refine ⟨hl, hm, ?_⟩
  rw [msW_ok n _ so sl c r sls hw hdec hb]
  have := motIdx_eq 0 sls
  simp only [Nat.zero_add, List.map_id'] at this
  simp only [ConRon.Arena.ClassRead.motiveSlot]
  erw [this]


/-! ## `class_gen_slot_var` (through `pin_word`, `intern_sort`, `intern_fvar`) -/

/-- The word model of `pin_word(k)`. -/
def pinWordW (m : Mem) (k : Word) : Option Word :=
  if 0 < (m.arr64 PINS).size ∧ rdW (m.arr64 PINS) 0 ≠ 0 then
    (if k.toNat < (m.arr64 PINS).size then some (rdW (m.arr64 PINS) k) else none)
  else none

theorem pinWord_specW (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ pinWordW s₀.mem k = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinWordW]

/-- After the sort interning. -/
def svK2 (m : Mem) (g s : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (z, m1) =>
    if 4294967296 ≤ z then none
    else if g.toNat < (m1.arr64 IW).size then
      (match fvinternW m1 (rdW (m1.arr64 IW) g + s) z with
       | none => none
       | some (fv, m2) => if 4294967296 ≤ fv then none else some ([fv], m2))
    else none

/-- **The model of `class_gen_slot_var`.** -/
def slotVarW (m : Mem) (g s : Word) : Option (List Word × Mem) :=
  match pinWordW m 53 with
  | none => none
  | some u => if 4294967296 ≤ u then none else svK2 m g s (sointernW m u)

theorem slotVar_spec (p : Prog) (hpin : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "class_gen_slot_var" = some classGenSlotVar) (n : Nat) (s₀ : St) (g s : Word) :
    ⦃fun s_ => s_ = s₀⦄ invoke p (exec p n) "class_gen_slot_var" [g, s]
    ⦃fun r s' => LocEq s' s₀ ∧ slotVarW s₀.mem g s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenSlotVar]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        pinWord_specW p hpin n, internSort_spec p hsf hsp his n, internFVar_spec p hff hfp hif n] <;>
      finish [slotVarW, svK2]


theorem slotVarW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (g s : Word) (G : ClassGen) (r : List Word) (hS : StageR dn vis fe m a)
    (hg : iwN m g.toNat = some G.nP) (hgt : g.toNat < iwTop m) (hns : G.nP + s.toNat < 2 ^ 64)
    (h : slotVarW m g s = some (r, m')) :
    ∃ x a', (ConRon.Arena.ClassGen.slotVar G s.toNat).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decE (r.headD 0) = x := by
  simp only [slotVarW] at h
  cases hpw : pinWordW m 53 with
  | none => rw [hpw] at h; simp at h
  | some u =>
    rw [hpw] at h
    by_cases hu : 4294967296 ≤ u
    · simp [hu] at h
    simp only [hu, if_false] at h
    have hu32 : u.toNat < 2 ^ 32 := by
      have : ¬ (4294967296 : Nat) ≤ u.toNat := hu
      omega
    cases hso : sointernW m u with
    | none => rw [hso] at h; simp [svK2] at h
    | some zm1 =>
      obtain ⟨z, m1⟩ := zm1
      rw [hso] at h
      simp only [svK2] at h
      by_cases hz : 4294967296 ≤ z
      · simp [hz] at h
      simp only [hz, if_false] at h
      have hz32 : z.toNat < 2 ^ 32 := by
        have : ¬ (4294967296 : Nat) ≤ z.toNat := hz
        omega
      -- pin
      have hpin : pinW m 0 ≠ 0 := by
        simp only [pinWordW] at hpw
        split at hpw
        · rename_i hh; exact hh.2
        · simp at hpw
      have hfull := hS.1.pins.full hpin
      have hzl : zeroLevel.run a = .ok (decI (pinW m 53), a) := pinZeroLevel_run hfull
      have hpu : u = pinW m 53 := by
        simp only [pinWordW] at hpw
        split at hpw
        · rename_i hh
          split at hpw
          · simp only [Option.some.injEq] at hpw
            rw [← hpw]; rfl
          · simp at hpw
        · simp at hpw
      obtain ⟨a1, hrun1, hS1, hg1⟩ := internSort_stage hS u hu32 hso
      obtain ⟨hg0, hmem⟩ : g.toNat < (m1.arr64 IW).size ∧ True := by
        by_cases hb : g.toNat < (m1.arr64 IW).size
        · exact ⟨hb, trivial⟩
        · simp [hb] at h
      simp only [hg0, if_true] at h
      -- IW[g] is unchanged
      have hrd : rdW (m1.arr64 IW) g = UInt64.ofNat G.nP := by
        have e1 := (iwN_rdW hg (by have := g.toNat_lt; omega))
        rw [UInt64.ofNat_toNat] at e1
        have e2 := hg1.2.2.1 g.toNat hgt
        simp only [rdW] at e1 ⊢
        have : (m1.arr64 IW)[g.toNat]? = (m.arr64 IW)[g.toNat]? := e2
        rw [this]; exact e1.1
      rw [hrd] at h
      cases hfv : fvinternW m1 (UInt64.ofNat G.nP + s) z with
      | none => rw [hfv] at h; simp at h
      | some fvm2 =>
        obtain ⟨fv, m2⟩ := fvm2
        rw [hfv] at h
        by_cases hf : 4294967296 ≤ fv
        · simp [hf] at h
        simp only [hf, if_false, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 (UInt64.ofNat G.nP + s) z hz32 hfv
        have hnP : G.nP < 2 ^ 64 := by omega
        have hsum : (UInt64.ofNat G.nP + s).toNat = G.nP + s.toNat := by
          rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hnP]; exact Nat.mod_eq_of_lt hns
        have hf32 : fv.toNat < 2 ^ 32 := by
          have : ¬ (4294967296 : Nat) ≤ fv.toNat := hf
          omega
        refine ⟨decE fv, a2, ?_, hS2, hg1.trans hg2, by simpa using hf32, rfl⟩
        rw [hsum] at hrun2
        simp only [ConRon.Arena.ClassGen.slotVar]
        have e0 : (zeroLevel : AM LIdx) a = .ok (decI (pinW m 53), a) := hzl
        rw [← hpu] at e0
        simp only [StateT.run] at hrun1 hrun2 ⊢
        simp only [StateT.bind, e0, bind, Except.bind, hrun1]
        exact hrun2


/-- **`class_gen_slot_var` refines `ClassGen.slotVar`** (through `pin_word` and master's interning). -/
@[refines ConRon.Arena.ClassGen.slotVar]
theorem classGenSlotVar_refines (p : Prog) (hpin : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "class_gen_slot_var" = some classGenSlotVar) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g s : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hg : iwN s₀.mem g.toNat = some G.nP)
    (hgt : g.toNat < iwTop s₀.mem) (hns : G.nP + s.toNat < 2 ^ 64) :
    ⦃fun s_ => s_ = s₀⦄ invoke p (exec p n) "class_gen_slot_var" [g, s]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.slotVar G s.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.slotVar G s.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.ClassGen.slotVar G s.toNat) a₀; ⊤⦄ := by
  refine triple_post (slotVar_spec p hpin hsf hsp his hff hfp hif hp n s₀ g s) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hgr, h1, h2⟩ := slotVarW_ok dn vis fe _ _ a₀ g s G r hS hg hgt hns hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.ClassGen.slotVar G s.toNat) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hgr, h1, by rw [hres]; exact h2⟩


/-! ## `class_gen_mot_var` -/

/-- The returned word. -/
def mvK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- After the motive-slot search. -/
def mvK (m : Mem) (g : Word) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r => mvK2 (slotVarW m g (if r.headD 0 = 0 then 0 else r.tail.headD 0))

/-- **The model of `class_gen_mot_var`.** -/
def motVarW (n : Nat) (m : Mem) (g c : Word) : Option (List Word × Mem) :=
  mvK m g (msW n m (rdW (m.arr64 IW) (g + 7)) (rdW (m.arr64 IW) (g + 8)) c)

section mvarms
variable (m : Mem) (g : Word) (r : List Word)
theorem mvK_some : mvK m g (some r) = mvK2 (slotVarW m g (if r.headD 0 = 0 then 0 else r.tail.headD 0)) := rfl
theorem mvK2_some (m' : Mem) : mvK2 (some (r, m')) = some ([r.headD 0], m') := rfl
end mvarms

grind_pattern [ind_grind] mvK_some => mvK m g (some r)
grind_pattern [ind_grind] mvK2_some => mvK2 (some (r, m'))

theorem motVar_spec (p : Prog) (hpin : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hsv : p.lookup "class_gen_slot_var" = some classGenSlotVar)
    (hms : p.lookup "class_read_motive_slot" = some classReadMotiveSlot)
    (hp : p.lookup "class_gen_mot_var" = some classGenMotVar) (n : Nat) (s₀ : St) (g c : Word) :
    ⦃fun s_ => s_ = s₀⦄ invoke p (exec p (n + 1)) "class_gen_mot_var" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ motVarW n s₀.mem g c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenMotVar]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      classReadMotiveSlot_spec p hms n, slotVar_spec p hpin hsf hsp his hff hfp hif hsv n] <;>
    finish (gen := 20) [motVarW]


theorem motIdx_lt : ∀ (sls : List ClassSlot) (j i : Nat), i ∈ motIdx j sls → j ≤ i ∧ i < j + sls.length := by
  intro sls
  induction sls with
  | nil => intro j i h; simp [motIdx] at h
  | cons sl sls ih =>
    intro j i h
    cases sl with
    | motive k =>
      simp only [motIdx, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := ih (j + 1) i h; simp; omega
    | minor c C ihs =>
      simp only [motIdx] at h
      have := ih (j + 1) i h; simp; omega

theorem motVarW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat)
    (m m' : Mem) (a : AState) (g c : Word) (G : ClassGen) (r : List Word) (hS : StageR dn vis fe m a)
    (hg : iwN m g.toNat = some G.nP) (hgt : g.toNat < iwTop m)
    (hsl : decAt m (decPL m (decCS m)) (g.toNat + 7) = some G.slots)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hgb : g.toNat + 9 < 2 ^ 64)
    (hsz : (m.arr64 IW).size + 5 < 2 ^ 64) (h : motVarW n m g c = some (r, m')) :
    ∃ x a', (ConRon.Arena.ClassGen.motVar G c.toNat).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 ∧ decE (r.headD 0) = x := by
  obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hsl
  have ho' := iwN_off (k := 7) ho (by omega)
  have hl' := iwN_off (k := 8) (by simpa [Nat.add_assoc] using hl) (by omega)
  have e : UInt64.ofNat g.toNat = g := UInt64.ofNat_toNat
  rw [e] at ho' hl'
  simp only [show UInt64.ofNat 7 = 7 from rfl, show UInt64.ofNat 8 = 8 from rfl] at ho' hl'
  simp only [motVarW, ho'.2, hl'.2] at h
  have hob : o < 2 ^ 64 := (iwN_rdW ho (by omega)).2
  have hlb : l < 2 ^ 64 := (iwN_rdW (by simpa [Nat.add_assoc] using hl) (by omega)).2
  have hol : o + l < 2 ^ 64 := by
    rcases decPL_le hdec with h0 | h0
    · omega
    · omega
  cases hms : msW n m (UInt64.ofNat o) (UInt64.ofNat l) c with
  | none => rw [hms] at h; simp [mvK] at h
  | some r1 =>
    rw [hms] at h
    have g1 := msW_ok n m _ _ c r1 G.slots hms (by simpa [UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb] using hdec)
      (by simp [UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb]; exact hol)
    have hmot : ConRon.Arena.ClassRead.motiveSlot G.slots c.toNat = (motIdx 0 G.slots)[c.toNat]? := by
      have := motIdx_eq 0 G.slots
      simp only [Nat.zero_add, List.map_id'] at this
      simp only [ConRon.Arena.ClassRead.motiveSlot]
      erw [this]
    obtain ⟨sv, hsv1, hsv2⟩ : ∃ sv : Word, sv.toNat = ((motIdx 0 G.slots)[c.toNat]?).getD 0 ∧
        (if r1.headD 0 = 0 then 0 else r1.tail.headD 0) = sv := by
      rw [g1]
      cases ho2 : (motIdx 0 G.slots)[c.toNat]? with
      | none => exact ⟨0, rfl, by simp [msRes]⟩
      | some i =>
        have hi : i ∈ motIdx 0 G.slots := List.mem_of_getElem? ho2
        have := (motIdx_lt G.slots 0 i hi).2
        exact ⟨UInt64.ofNat i, by simp; omega, by simp [msRes]⟩
    simp only [mvK, hsv2] at h
    cases hsw : slotVarW m g sv with
    | none => rw [hsw] at h; simp [mvK2] at h
    | some r2m =>
      obtain ⟨r2, m2⟩ := r2m
      rw [hsw] at h
      simp only [mvK2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hsvb : G.nP + sv.toNat < 2 ^ 64 := by
        rw [hsv1]
        cases ho2 : (motIdx 0 G.slots)[c.toNat]? with
        | none => simp; omega
        | some i =>
          have hi : i ∈ motIdx 0 G.slots := List.mem_of_getElem? ho2
          have := (motIdx_lt G.slots 0 i hi).2
          simp; omega
      obtain ⟨x, a', hrun, hS', hgr, h1, h2⟩ := slotVarW_ok dn vis fe _ _ a g sv G r2 hS hg hgt hsvb hsw
      refine ⟨x, a', ?_, hS', hgr, by simpa using h1, by simpa using h2⟩
      simp only [ConRon.Arena.ClassGen.motVar, hmot, ← hsv1]
      exact hrun


/-- **`class_gen_mot_var` refines `ClassGen.motVar`**. -/
@[refines ConRon.Arena.ClassGen.motVar]
theorem classGenMotVar_refines (p : Prog) (hpin : p.lookup "pin_word" = some pinWordL)
    (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
    (his : p.lookup "intern_sort" = some internSort)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hsv : p.lookup "class_gen_slot_var" = some classGenSlotVar)
    (hms : p.lookup "class_read_motive_slot" = some classReadMotiveSlot)
    (hp : p.lookup "class_gen_mot_var" = some classGenMotVar) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hg : iwN s₀.mem g.toNat = some G.nP)
    (hgt : g.toNat < iwTop s₀.mem)
    (hsl : decAt s₀.mem (decPL s₀.mem (decCS s₀.mem)) (g.toNat + 7) = some G.slots)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hgb : g.toNat + 9 < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) :
    ⦃fun s_ => s_ = s₀⦄ invoke p (exec p (n + 1)) "class_gen_mot_var" [g, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.motVar G c.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.motVar G c.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.ClassGen.motVar G c.toNat) a₀; ⊤⦄ := by
  refine triple_post (motVar_spec p hpin hsf hsp his hff hfp hif hsv hms hp n s₀ g c) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hgr, h1, h2⟩ := motVarW_ok dn vis fe n _ _ a₀ g c G r hS hg hgt hsl hns hgb hsz hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok (ConRon.Arena.ClassGen.motVar G c.toNat) a₀ a' x hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hgr, h1, by rw [hres]; exact h2⟩


theorem ctag_iff (w : Word) (hw : w.toNat < 2 ^ 32) (k : Nat) (hk : k < 16) :
    (decE w).tag = UInt32.ofNat k ↔ w >>> 28 = UInt64.ofNat k := by
  rw [decE_tag w hw]
  have h28 : (w >>> 28).toNat < 16 := by
    rw [UInt64.toNat_shiftRight]; simp; omega
  constructor
  · intro h
    have := congrArg UInt32.toNat h
    simp [UInt64.toNat_toUInt32] at this
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_ofNat_of_lt' (by omega : k < 2 ^ 64)]
    rw [UInt64.toNat_shiftRight] at *
    simp at *
    omega
  · intro h
    rw [h]; apply UInt32.toNat_inj.mp
    simp [UInt64.toNat_toUInt32]

theorem ETables.getConst_of_get_r (t : ETables) (i : EIdx) (n : NIdx) (us : LsIdx)
    (h : t.get i = some (.const n us)) : t.getConst i = some (n, us) := by
  unfold ETables.get at h
  unfold ETables.getConst
  repeat' (first | (simp at h; done) | split at h)
  cases hn : t.consts.node? i.idxNat <;> simp [hn] at h ⊢
  exact h

theorem EStore.viewConst_of_view_r (st : EStore) (i : EIdx) (n : NIdx) (us : LsIdx)
    (h : st.view i = some (.const n us)) : st.viewConst i = some (n, us) := by
  unfold EStore.view at h
  unfold EStore.viewConst EStore.persGetConst
  split at h
  · simp only [*, ite_true]; exact ETables.getConst_of_get_r _ _ _ _ h
  · split at h
    · simp only [*, ite_true]; split <;> simp_all [ETables.getConst_of_get_r _ _ _ _ h]
    · simp at h


theorem eViewW_head6 (m : Mem) (w : Word) (hne : eViewW m w ≠ []) (hg : w >>> 28 = 6) :
    (eViewW m w).headD 0 = 6 := by
  unfold eViewW at hne ⊢
  simp (config := {decide := true}) only [hg, ite_true, ite_false] at hne ⊢
  by_cases c1 : 4294967295 < w
  · simp [c1] at hne
  by_cases c2 : tierW w ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  by_cases c3 : rdW (m.arr64 CTL) (30 + tierW w) ≤ idxW w
  · simp [c1, c2, c3] at hne
  simp [c1, c2, c3]

theorem ETables.getBind_of_get_forall (t : ETables) (i : EIdx) (ty b : EIdx)
    (h : t.get i = some (.forallE ty b)) : t.getBind i = some (ty, b) := by
  unfold ETables.get at h
  unfold ETables.getBind
  repeat' (first | (simp at h; done) | split at h)
  rename_i h1 h2 h3 h4 h5 h6 h7
  have h7' : Idx.tag i = ETag.forallE := by simpa using h7
  have hne : ETag.forallE ≠ ETag.lam := by decide
  cases hn : t.foralls.node? i.idxNat <;> simp [hn, h7', hne] at h ⊢
  exact h

theorem EStore.viewBind_of_view_forall (st : EStore) (i : EIdx) (ty b : EIdx)
    (h : st.view i = some (.forallE ty b)) : st.viewBind i = some (ty, b) := by
  unfold EStore.view at h
  unfold EStore.viewBind EStore.persGetBind
  split at h
  · simp only [*, ite_true]; exact ETables.getBind_of_get_forall _ _ _ _ h
  · split at h
    · simp only [*, ite_true]; split <;> simp_all [ETables.getBind_of_get_forall _ _ _ _ h]
    · simp at h


/-! ## `class_gen_ih_parts` (through the `open_pis_at_fvars_f` and `get_app_args` stubs) -/

/-- After `get_app_args`. -/
def ihK2 (nPc xo xl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) =>
    if nPc < r.tail.headD 0 then some ([1, xo, xl, r.headD 0 + nPc, r.tail.headD 0 - nPc], m2)
    else some ([1, xo, xl, r.headD 0, 0], m2)

/-- After `open_pis_at_fvars_f`. -/
def ihK1 (nPc : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0, 0], m1)
    else ihK2 nPc (r.tail.headD 0) (r.tail.tail.headD 0)
      (stubM "get_app_args" m1 [CWF, r.tail.tail.tail.headD 0])

/-- **The model of `class_gen_ih_parts`.** -/
def ihW (m : Mem) (g t tele w d : Word) : Option (List Word × Mem) :=
  ihK1 (if t < rdW (m.arr64 IW) (g + 4) then rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 3) + t) + 4) else 0)
    (stubM "open_pis_at_fvars_f" m [tele, w, d])

section arms
variable (nPc xo xl : Word) (r : List Word) (m1 : Mem)
theorem ihK2_some : ihK2 nPc xo xl (some (r, m1)) =
    (if nPc < r.tail.headD 0 then some ([1, xo, xl, r.headD 0 + nPc, r.tail.headD 0 - nPc], m1)
    else some ([1, xo, xl, r.headD 0, 0], m1)) := rfl
theorem ihK1_some : ihK1 nPc (some (r, m1)) =
    (if r.headD 0 = 0 then some ([0, 0, 0, 0, 0], m1)
    else ihK2 nPc (r.tail.headD 0) (r.tail.tail.headD 0)
      (stubM "get_app_args" m1 [CWF, r.tail.tail.tail.headD 0])) := rfl
end arms
grind_pattern [ind_grind] ihK2_some => ihK2 nPc xo xl (some (r, m1))
grind_pattern [ind_grind] ihK1_some => ihK1 nPc (some (r, m1))

set_option maxHeartbeats 1600000 in
theorem classGenIhParts_spec (p : Prog) (hp : p.lookup "class_gen_ih_parts" = some classGenIhParts)
    (n : Nat) (s₀ : St) (g t tele w d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_ih_parts" [g, t, tele, w, d]
    ⦃fun r s' => LocEq s' s₀ ∧ ihW s₀.mem g t tele w d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classGenIhParts]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "open_pis_at_fvars_f" n, stubM_spec p "get_app_args" n] <;>
    finish (gen := 20) [ihW]


theorem decTM_nPc {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwN m (p + 4) = some M.nPc := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, a3, ha3, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  exact ha3


theorem decHL_drop {k' : IdxKind} {m : Mem} : ∀ (k : Nat) {o l : Nat} {xs : List (Idx k')},
    decHL m o l = some xs → k ≤ l → decHL m (o + k) (l - k) = some (xs.drop k) := by
  intro k
  induction k with
  | zero => intro o l xs h _; simpa using h
  | succ k ih =>
    intro o l xs h hk
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    obtain ⟨x, ys, rfl, hys, -⟩ := decHL_cons_r h
    have := ih hys (by omega)
    have e1 : o + 1 + k = o + (k + 1) := by omega
    have e2 : l' - k = l' + 1 - (k + 1) := by omega
    rw [e1, e2] at this
    simpa using this

/-- The `nPc` word `class_gen_ih_parts` reads, against the twin's `(g.cls[t]?).map nPc`. -/
theorem ihNPc_word {m : Mem} {g t : Word} {cls : List TargetMajor}
    (hcls : decAt m (decPL m (decTM m)) (g.toNat + 3) = some cls)
    (hsz : (m.arr64 IW).size + 5 < 2 ^ 64) :
    (if t < rdW (m.arr64 IW) (g + 4) then
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 3) + t) + 4) else 0) =
      UInt64.ofNat (match cls[t.toNat]? with | some M => M.nPc | none => 0) ∧
    (match cls[t.toNat]? with | some M => M.nPc | none => 0) < 2 ^ 64 := by
  obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hcls
  have hg64 : g.toNat + 4 < 2 ^ 64 := by have := iwN_lt hl; omega
  have e : UInt64.ofNat g.toNat = g := UInt64.ofNat_toNat
  have ho' := iwN_off (k := 3) ho (by omega)
  have hl' := iwN_off (k := 4) (by simpa [Nat.add_assoc] using hl) (by omega)
  rw [e] at ho' hl'
  simp only [show UInt64.ofNat 3 = 3 from rfl, show UInt64.ofNat 4 = 4 from rfl] at ho' hl'
  have hob : o < 2 ^ 64 := (iwN_rdW ho (by omega)).2
  have hlb : l < 2 ^ 64 := (iwN_rdW (by simpa [Nat.add_assoc] using hl) (by omega)).2
  rw [ho'.2, hl'.2]
  by_cases ht : t.toNat < l
  · have hlt : t < UInt64.ofNat l := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hlb]; exact ht
    obtain ⟨v, hv, hM⟩ := decPL_getH m hdec t.toNat ht
    have hsome : cls[t.toNat]? = some (cls[t.toNat]'(by rw [decPL_length m hdec]; exact ht)) :=
      List.getElem?_eq_getElem _
    rw [hsome]
    have hn4 := decTM_nPc hM
    have hvb : v < 2 ^ 64 := (iwN_rdW hv (by have := iwN_lt hv; omega)).2
    have hadd : UInt64.ofNat o + t = UInt64.ofNat (o + t.toNat) := by
      rw [UInt64.ofNat_add, UInt64.ofNat_toNat]
    have hrv := iwN_rdW hv (by have := iwN_lt hv; omega)
    have h4 := iwN_off (k := 4) hn4 (by have := iwN_lt hn4; omega)
    simp only [show UInt64.ofNat 4 = 4 from rfl] at h4
    refine ⟨?_, (iwN_rdW hn4 (by have := iwN_lt hn4; omega)).2⟩
    simp only [hlt, if_true, hadd, hrv.1, h4.2]
  · have hlt : ¬ t < UInt64.ofNat l := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hlb]; exact ht
    have hnone : cls[t.toNat]? = none := by
      rw [List.getElem?_eq_none_iff, decPL_length m hdec]; omega
    refine ⟨?_, by simp [hnone]⟩
    simp [hlt, hnone]


theorem iwH_lt {k : IdxKind} {m : Mem} {i : Nat} {x : Idx k} (h : iwH m i = some x) :
    i < (m.arr64 IW).size := by
  simp only [iwH, hd?, iwA] at h
  cases hw : (m.arr64 IW)[i]? with
  | none => simp [hw] at h
  | some w => exact (Array.getElem?_eq_some_iff.mp hw).1

theorem decHL_le {k : IdxKind} {m : Mem} : ∀ {o l : Nat} {xs : List (Idx k)},
    decHL m o l = some xs → l = 0 ∨ o + l ≤ (m.arr64 IW).size := by
  intro o l
  induction l generalizing o with
  | zero => intro xs _; exact Or.inl rfl
  | succ l ih =>
    intro xs h
    obtain ⟨x, ys, -, hys, hx⟩ := decHL_cons_r h
    have h1 := iwH_lt hx
    rcases ih hys with h0 | h0
    · right; omega
    · right; omega

/-- What `class_gen_ih_parts` returns against the twin's `Option (xs, args.drop nPc)`. -/
def IhRes (m' : Mem) (r : List Word) : Option (List EIdx × List EIdx) → Prop
  | none => r.headD 0 = 0
  | some (xs, ys) => r.headD 0 = 1 ∧
      decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some xs ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m' ∧
      decHL m' (r.tail.tail.tail.headD 0).toNat (r.tail.tail.tail.tail.headD 0).toNat = some ys ∧
      (r.tail.tail.tail.headD 0).toNat + (r.tail.tail.tail.tail.headD 0).toNat ≤ iwTop m'

theorem ihW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem)
    (a : AState) (g t tele w d : Word) (G : ClassGen) (r : List Word) (hS : StageR dn vis fe m a)
    (hw : H w) (hcls : decAt m (decPL m (decTM m)) (g.toNat + 3) = some G.cls)
    (hsz : (m.arr64 IW).size + 5 < 2 ^ 64)
    (h : ihW m g t tele w d = some (r, m')) :
    ∃ res a', (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ IhRes m' r res := by
  simp only [ihW] at h
  obtain ⟨hnp0, hnp64⟩ := ihNPc_word (t := t) hcls hsz
  rw [hnp0] at h
  cases hs : stubM "open_pis_at_fvars_f" m [tele, w, d] with
  | none => rw [hs] at h; simp [ihK1] at h
  | some r1m =>
    obtain ⟨r1, m1⟩ := r1m
    rw [hs] at h
    obtain ⟨res1, a1, hrun1, hS1, hg1, hdec1⟩ := openPisAtFvarsF_spec dn vis fe tele w d hw m m1 a r1 hs hS
    cases res1 with
    | none =>
      have h0 : r1.headD 0 = 0 := hdec1
      rw [ihK1_some, if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨none, a1, ?_, hS1, hg1, rfl⟩
      simp only [ConRon.Arena.ClassGen.ihParts, StateT.run_bind]
      rw [hrun1]
      rfl
    | some xl =>
      obtain ⟨xs, leaf⟩ := xl
      obtain ⟨h1, hxs, hleaf⟩ := hdec1
      have h0 : r1.headD 0 ≠ 0 := by rw [h1]; decide
      rw [ihK1_some, if_neg h0] at h
      have hleaf3 : r1.tail.tail.tail.headD 0 = (r1.drop 3).headD 0 := by
        cases r1 with
        | nil => rfl
        | cons a1 t1 => cases t1 with
          | nil => rfl
          | cons a2 t2 => cases t2 <;> rfl
      rw [hleaf3] at h
      obtain ⟨hl1, hl2⟩ := hleaf
      cases ha : stubM "get_app_args" m1 [CWF, (r1.drop 3).headD 0] with
      | none => rw [ha] at h; simp [ihK2] at h
      | some r2m =>
        obtain ⟨r2, m2⟩ := r2m
        rw [ha] at h
        obtain ⟨args, a2, hrun2, hS2, hg2, hdec2⟩ := getAppArgs_spec dn vis fe CWF ((r1.drop 3).headD 0) hl1 m1 m2 a1 r2 ha hS1
        generalize hN : (match G.cls[t.toNat]? with | some M => M.nPc | none => 0) = N at hnp64 h
        have gd : ∀ (l : List Word), l.getD 0 0 = l.headD 0 ∧ l.getD 1 0 = l.tail.headD 0 ∧
            l.getD 2 0 = l.tail.tail.headD 0 := by
          intro l; cases l with
          | nil => simp
          | cons a1 t1 => cases t1 with
            | nil => simp
            | cons a2 t2 => cases t2 <;> simp
        obtain ⟨hxs0, hxtop⟩ := hxs
        obtain ⟨hdec20, hatop⟩ := hdec2
        have hxs' : decHL m1 (r1.tail.headD 0).toNat (r1.tail.tail.headD 0).toNat = some xs := by
          rw [(gd r1).2.1, (gd r1).2.2] at hxs0
          exact hxs0
        have hxtop' : (r1.tail.headD 0).toNat + (r1.tail.tail.headD 0).toNat ≤ iwTop m1 := by
          rw [(gd r1).2.1, (gd r1).2.2] at hxtop
          exact hxtop
        have hdec2' : decHL m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat = some args := by
          simp only [show (0 : Nat) + 1 = 1 from rfl] at hdec20
          rw [(gd r2).1, (gd r2).2.1] at hdec20
          exact hdec20
        have hatop' : (r2.headD 0).toNat + (r2.tail.headD 0).toNat ≤ iwTop m2 := by
          simp only [show (0 : Nat) + 1 = 1 from rfl] at hatop
          rw [(gd r2).1, (gd r2).2.1] at hatop
          exact hatop
        have hxs2 : decHL m2 (r1.tail.headD 0).toNat (r1.tail.tail.headD 0).toNat = some xs := by
          rw [decHL_grow hg2 hxtop']; exact hxs'
        have hlen := decHL_length m2 hdec2'
        rw [ihK2_some] at h
        have hTW : (UInt64.ofNat N).toNat = N := UInt64.toNat_ofNat_of_lt' hnp64
        have htwin : (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat).run a =
            .ok (some (xs, args.drop N), a2) := by
          have hunf : ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat =
              (do match ← openPisAtFvarsF tele.toNat (decI w) d.toNat with
                  | none => pure none
                  | some (xs, leaf) => do
                    let args ← getAppArgs coreWalkFuel leaf
                    pure (some (xs, args.drop (match G.cls[t.toNat]? with | some M => M.nPc | none => 0)))) := rfl
          rw [hunf]
          simp only [StateT.run_bind]
          rw [hrun1]
          simp only [bind, Except.bind]
          have hrun2' : (getAppArgs coreWalkFuel leaf).run a1 = .ok (args, a2) := by
            have := hrun2
            rw [CWF_eq] at this
            have e3 : (decI ((r1.drop 3).headD 0) : EIdx) = leaf := hl2
            rw [e3] at this
            exact this
          rw [hN]
          simp only [StateT.run] at hrun2' ⊢
          simp only [bind, Except.bind, StateT.bind, hrun2']
          rfl
        have hao : (r2.headD 0).toNat + (r2.tail.headD 0).toNat < 2 ^ 64 ∨ (r2.tail.headD 0).toNat = 0 := by
          rcases decHL_le hdec2' with h0 | h0
          · right; exact h0
          · left; obtain ⟨-, -, hsz2, -, -⟩ := hS2.2; omega
        by_cases hlt : UInt64.ofNat N < r2.tail.headD 0
        · rw [if_pos hlt] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hNl : N < (r2.tail.headD 0).toNat := by
            have := UInt64.lt_iff_toNat_lt.mp hlt
            rwa [hTW] at this
          have hsum : (r2.headD 0 + UInt64.ofNat N).toNat = (r2.headD 0).toNat + N := by
            simp only [UInt64.toNat_add, hTW]
            apply Nat.mod_eq_of_lt
            rcases hao with h0 | h0 <;> omega
          have hsub : (r2.tail.headD 0 - UInt64.ofNat N).toNat = (r2.tail.headD 0).toNat - N := by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hTW]; omega)), hTW]
          have hdr := decHL_drop N hdec2' (by omega)
          refine ⟨some (xs, args.drop N), a2, htwin, hS2, hg1.trans hg2, ?_⟩
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · simpa using hxs2
          · have := hg2.1; simpa using Nat.le_trans hxtop' this
          · show decHL m2 (r2.headD 0 + UInt64.ofNat N).toNat (r2.tail.headD 0 - UInt64.ofNat N).toNat = _
            rw [hsum, hsub]; exact hdr
          · show (r2.headD 0 + UInt64.ofNat N).toNat + (r2.tail.headD 0 - UInt64.ofNat N).toNat ≤ iwTop m2
            rw [hsum, hsub]; omega
        · rw [if_neg hlt] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hNl : (r2.tail.headD 0).toNat ≤ N := by
            have : ¬ (UInt64.ofNat N).toNat < (r2.tail.headD 0).toNat := fun hh =>
              hlt (UInt64.lt_iff_toNat_lt.mpr hh)
            rw [hTW] at this; omega
          have hnil : args.drop N = [] := List.drop_eq_nil_of_le (by omega)
          refine ⟨some (xs, args.drop N), a2, htwin, hS2, hg1.trans hg2, ?_⟩
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · simpa using hxs2
          · have := hg2.1; simpa using Nat.le_trans hxtop' this
          · rw [hnil]; simp [decHL, hslice?]
          · show (r2.headD 0).toNat + (0 : Word).toNat ≤ iwTop m2
            simp only [UInt64.toNat_zero]; omega


/-- **`class_gen_ih_parts` refines `ClassGen.ihParts`** (through the `open_pis_at_fvars_f` and
`get_app_args` stubs). -/
@[refines ConRon.Arena.ClassGen.ihParts]
theorem classGenIhParts_refines (p : Prog) (hp : p.lookup "class_gen_ih_parts" = some classGenIhParts)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (g t tele w d : Word) (G : ClassGen) (hS : StageR dn vis fe s₀.mem a₀) (hw : H w)
    (hcls : decAt s₀.mem (decPL s₀.mem (decTM s₀.mem)) (g.toNat + 3) = some G.cls)
    (hsz : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_gen_ih_parts" [g, t, tele, w, d]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      IhRes s'.mem r (AM.res (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat) a₀);
      ⊤⦄ := by
  refine triple_post (classGenIhParts_spec p hp n s₀ g t tele w d) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hS', hg, hres⟩ := ihW_ok dn vis fe _ _ a₀ g t tele w d G r hS hw hcls hsz hm
  obtain ⟨hok, hst, hrs⟩ := AM.of_run_ok (ConRon.Arena.ClassGen.ihParts G t.toNat tele.toNat (decI w) d.toNat) a₀ a' res hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hrs]; exact hres⟩


theorem eViewW_head3 (m : Mem) (w : Word) (hne : eViewW m w ≠ []) (hg : w >>> 28 = 3) :
    (eViewW m w).headD 0 = 3 := by
  unfold eViewW at hne ⊢
  simp (config := {decide := true}) only [hg, ite_true, ite_false] at hne ⊢
  by_cases c1 : 4294967295 < w
  · simp [c1] at hne
  by_cases c2 : tierW w ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c1, c2] at hne
  by_cases c3 : rdW (m.arr64 CTL) (18 + tierW w) ≤ idxW w
  · simp [c1, c2, c3] at hne
  simp [c1, c2, c3]


theorem decTM_ind {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    iwH m p = some M.ind := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  exact h5


/-! ## `sl_cons` on a list of numbers (`IW` words read as `Nat`s) -/

/-- **`sl_cons` builds `x :: xs`**, the pool only grown, nothing else written. -/
theorem slCons_decN {m m' : Mem} {x o l : Word} {n : Nat} {xs : List Nat}
    (h : copyW n (consPre m x l) (rdW (m.arr64 CTL) 200 + 1) o l = some m')
    (hne : l + 1 ≠ 0)
    (hroom : (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size)
    (hsrc : o.toNat + l.toNat ≤ (rdW (m.arr64 CTL) 200).toNat)
    (hxs : decNL m o.toNat l.toNat = some xs) :
    decNL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (x.toNat :: xs) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + (l + 1) := by
  generalize hq : rdW (m.arr64 CTL) 200 = q at *
  have hlm : l.toNat ≠ 2 ^ 64 - 1 := fun h0 => hne (by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [h0])
  have hl1 : (l + 1).toNat = l.toNat + 1 := by
    rw [UInt64.toNat_add]; simp
    have : l.toNat < 2 ^ 64 := l.toNat_lt
    omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [hl1] at hroom
  -- the memory before the copy
  have hm1IW : (consPre m x l).arr64 IW = ((m.arr64 IW).set! q.toNat x) := by
    simp only [consPre, allocMem, hq]
    rw [Mem.arr64_set64_same, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hm1sz : ((consPre m x l).arr64 IW).size = (m.arr64 IW).size := by rw [hm1IW]; simp
  obtain ⟨hA, hS, hW, hG⟩ := copyW_get n _ _ _ _ _ h (by rw [hq1]; omega) (by rw [hq1, hm1sz]; omega)
    (by rw [hm1sz]; exact hsz)
  have hm1get : ∀ i, ((consPre m x l).arr64 IW)[i]? =
      if i = q.toNat then some x else (m.arr64 IW)[i]? := by
    intro i
    rw [hm1IW, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hi : q.toNat = i
    · subst hi; simp [show q.toNat < (m.arr64 IW).size by omega]
    · simp [hi, Ne.symm hi]
  have hget : ∀ i, (m'.arr64 IW)[i]? =
      if i = q.toNat then some x
      else if q.toNat + 1 ≤ i ∧ i < q.toNat + 1 + l.toNat then (m.arr64 IW)[o.toNat + (i - (q.toNat + 1))]?
      else (m.arr64 IW)[i]? := by
    intro i
    rw [hG i, hq1]
    by_cases hi : q.toNat + 1 ≤ i ∧ i < q.toNat + 1 + l.toNat
    · rw [if_pos hi, if_neg (by omega), if_pos hi, hm1get, if_neg (by omega)]
    · rw [if_neg hi, hm1get]
      by_cases hiq : i = q.toNat
      · simp [hiq]
      · rw [if_neg hiq, if_neg hiq, if_neg hi]
  -- the other arrays and CTL
  have hCTL : ∀ i, i ≠ (200 : Word) → rdW (m'.arr64 CTL) i = rdW (m.arr64 CTL) i := by
    intro i hi
    rw [hA CTL (by decide)]; exact consPre_ctl m x l i hi
  have hEREC : m'.arr64 EREC = m.arr64 EREC := by
    rw [hA EREC (by decide)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have htop : rdW (m'.arr64 CTL) 200 = q + (l + 1) := by
    rw [hA CTL (by decide)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), rdW_set64]; simp [hc, hq]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, htop⟩
  · rw [hl1, decNL_succ]
    have h0 : iwN m' q.toNat = some x.toNat := by
      simp [iwN, nat?, iwA, hget]
    rw [h0]
    have : decNL m' (q.toNat + 1) l.toNat = some xs := by
      rw [← hxs]
      simp only [decNL]
      apply mapM_opt_congr
      intro j hj
      have hj' : j < l.toNat := List.mem_range.mp hj
      simp only [iwN, nat?, iwA, hget]
      rw [if_neg (by omega), if_pos (by omega)]
      have : o.toNat + (q.toNat + 1 + j - (q.toNat + 1)) = o.toNat + j := by omega
      simp [this]
    simp [this]
  · have : (q + (l + 1)).toNat = q.toNat + (l.toNat + 1) := by
      rw [UInt64.toNat_add, hl1]; simp; omega
    simp only [iwTop, htop, this, hq]; omega
  · simp only [erTop, hCTL 129 (by decide)]; exact Nat.le_refl _
  · intro i hi
    simp only [iwTop, hq] at hi
    rw [hget, if_neg (by omega), if_neg (by omega)]
  · intro i _; rw [hEREC]
  · intro b hb hbc
    rw [hA b (by simpa using hb)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by simpa using hb), Mem.arr64_set64_ne _ _ _ _ _ hbc]
  · intro i hi; exact hCTL i (by simpa using hi)
  · intro b
    by_cases hb : b = IW
    · subst hb; rw [hS, hm1sz]
    · rw [hA b hb]; simp only [consPre, allocMem, size_set64]
  · rw [hW]; simp only [consPre, allocMem, Mem.words_size_set64]


/-- `consW` is the memory `slCons_dec` speaks about. -/
theorem consW_decN {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List Nat}
    (h : consW n m x o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hxs : decNL m o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l + 1] ∧
    decNL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (x.toNat :: xs) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ (l + 1).toNat = l.toNat + 1 ∧
    (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat = iwTop m' := by
  simp only [consW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  simp only [allocW] at h
  by_cases h1 : m.len64 IW < rdW (m.arr64 CTL) 200
  · simp [h1] at h
  by_cases h2 : m.len64 IW - rdW (m.arr64 CTL) 200 < l + 1
  · simp [h1, h2] at h
  simp only [h1, h2, if_false] at h
  cases hcp : copyW (n - 1) ((allocMem m (l + 1)).set64 IW (rdW (m.arr64 CTL) 200) x)
      (rdW (m.arr64 CTL) 200 + 1) o l with
  | none => simp [hcp] at h
  | some m2 =>
    simp [hcp] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlen : (m.len64 IW).toNat = (m.arr64 IW).size := by simp [Mem.len64]; omega
    have hq : (rdW (m.arr64 CTL) 200).toNat ≤ (m.arr64 IW).size := by
      have : ¬ (m.len64 IW).toNat < (rdW (m.arr64 CTL) 200).toNat := h1
      omega
    have hroom : (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat ≤ (m.arr64 IW).size := by
      have : ¬ (m.len64 IW - rdW (m.arr64 CTL) 200).toNat < (l + 1).toNat := h2
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
      omega
    have hlm : l.toNat ≠ 2 ^ 64 - 1 := fun e => h0 (by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [e])
    have hl1 : (l + 1).toNat = l.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := l.toNat_lt; omega
    obtain ⟨hd, hg, hf, ht⟩ := slCons_decN (n := n - 1) (xs := xs) hcp h0 hroom hsz hc
      (by simpa [iwTop] using hsrc) hxs
    refine ⟨rfl, hd, hg, hf, hl1, ?_⟩
    have e : (rdW (m.arr64 CTL) 200 + (l + 1)).toNat =
        (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat := by
      rw [UInt64.toNat_add]; omega
    simp only [iwTop, ht, e]



/-- The pool's top after a `sl_cons` stays within the array. -/
theorem consW_roomN {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    {xs : List Nat} (hxs : decNL m o.toNat l.toNat = some xs) :
    iwTop m' ≤ (m'.arr64 IW).size := by
  obtain ⟨-, -, -, hf, -, ht⟩ := consW_decN h hsz hc hsrc hxs
  rw [← ht, hf.2.2.1 IW]
  simp only [consW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  simp only [allocW] at h
  by_cases h1 : m.len64 IW < rdW (m.arr64 CTL) 200
  · simp [h1] at h
  by_cases h2 : m.len64 IW - rdW (m.arr64 CTL) 200 < l + 1
  · simp [h1, h2] at h
  have hlen : (m.len64 IW).toNat = (m.arr64 IW).size := by simp [Mem.len64]; omega
  have : ¬ (m.len64 IW).toNat < (rdW (m.arr64 CTL) 200).toNat := h1
  have h2' : ¬ (m.len64 IW - rdW (m.arr64 CTL) 200).toNat < (l + 1).toNat := h2
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at h2'
  omega

/-- **`sl_cons` keeps the stage relation**: the pool grew by the new slice, which decodes to
`x :: xs`. -/
theorem consW_stageN {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List Nat}
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hxs : decNL m o.toNat l.toNat = some xs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (x.toNat :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  obtain ⟨hr, hd, hg, hf, -, ht⟩ := consW_decN h hsz hc hsrc hxs
  have hroom := consW_roomN h hsz hc hsrc hxs
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  subst hr
  refine ⟨⟨CheckR.frame_iw hf hS.1, hroom, ?_, ?_, ?_, ?_⟩, hg, by simpa using hd, by simpa using ht⟩
  · simp only [erTop, h129, hE]; exact hE1
  · rw [hf.2.2.1 IW]; exact hsz
  · rw [hE]; exact hEs
  · rw [hf.2.2.1 CTL]; exact hc



/-! ## `class_read_rec_cls` -/

mutual
/-- **The model of `class_read_rec_cls`.** -/
def crW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, ro, rl =>
    if rl = 0 then some ([1, 0, 0], m)
    else crK1 n nP mo ml ro rl
      (stubM "open_pis_at_fvars_f" m
        [rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 2) + 1,
         rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0])

/-- After `open_pis_at_fvars_f`. -/
def crK1 (n : Nat) (nP mo ml ro rl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0, 0], m1)
    else crK2 n nP mo ml ro rl m1 (fvarHeadW m1 (r1.tail.tail.tail.headD 0))

/-- After `fvar_head`. -/
def crK2 (n : Nat) (nP mo ml ro rl : Word) (m1 : Mem) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else crK3 n nP mo ml ro rl m2 (cmvW (n - 1) m2 nP mo ml (r2.tail.headD 0))

/-- After `class_of_motive_var`. -/
def crK3 (n : Nat) (nP mo ml ro rl : Word) (m2 : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r3 =>
    if r3.headD 0 = 0 then some ([0, 0, 0], m2)
    else crK4 n (r3.tail.headD 0) (crW n m2 nP mo ml (ro + 1) (rl - 1))

/-- After the recursive call. -/
def crK4 (n : Nat) (c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then some ([0, 0, 0], m4)
    else crK5 (consW n m4 c (r4.tail.headD 0) (r4.tail.tail.headD 0))

/-- After `sl_cons`. -/
def crK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([1, r5.headD 0, r5.tail.headD 0], m5)
end


section arms
variable (n : Nat) (m m1 m2 m4 m5 : Mem) (nP mo ml ro rl c : Word) (r r1 r2 r4 r5 : List Word)
theorem crW_nil (h : rl = 0) : crW (n + 1) m nP mo ml ro rl = some ([1, 0, 0], m) := by simp [crW, h]
theorem crW_cons (h : rl ≠ 0) : crW (n + 1) m nP mo ml ro rl = crK1 n nP mo ml ro rl
      (stubM "open_pis_at_fvars_f" m
        [rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 2) + 1,
         rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0]) := by
  simp [crW, h]
theorem crK1_fail (h : r1.headD 0 = 0) : crK1 n nP mo ml ro rl (some (r1, m1)) = some ([0, 0, 0], m1) := by
  rw [crK1, if_pos h]
theorem crK1_ok (h : r1.headD 0 ≠ 0) : crK1 n nP mo ml ro rl (some (r1, m1)) =
    crK2 n nP mo ml ro rl m1 (fvarHeadW m1 (r1.tail.tail.tail.headD 0)) := by
  rw [crK1, if_neg h]
theorem crK2_fail (h : r2.headD 0 = 0) : crK2 n nP mo ml ro rl m1 (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [crK2, if_pos h]
theorem crK2_ok (h : r2.headD 0 ≠ 0) : crK2 n nP mo ml ro rl m1 (some (r2, m2)) =
    crK3 n nP mo ml ro rl m2 (cmvW (n - 1) m2 nP mo ml (r2.tail.headD 0)) := by
  rw [crK2, if_neg h]
theorem crK3_fail (r3 : List Word) (h : r3.headD 0 = 0) : crK3 n nP mo ml ro rl m2 (some r3) = some ([0, 0, 0], m2) := by
  rw [crK3, if_pos h]
theorem crK3_ok (r3 : List Word) (h : r3.headD 0 ≠ 0) : crK3 n nP mo ml ro rl m2 (some r3) =
    crK4 n (r3.tail.headD 0) (crW n m2 nP mo ml (ro + 1) (rl - 1)) := by
  rw [crK3, if_neg h]
theorem crK4_fail (h : r4.headD 0 = 0) : crK4 n c (some (r4, m4)) = some ([0, 0, 0], m4) := by
  rw [crK4, if_pos h]
theorem crK4_ok (h : r4.headD 0 ≠ 0) : crK4 n c (some (r4, m4)) =
    crK5 (consW n m4 c (r4.tail.headD 0) (r4.tail.tail.headD 0)) := by
  rw [crK4, if_neg h]
theorem crK5_some : crK5 (some (r5, m5)) = some ([1, r5.headD 0, r5.tail.headD 0], m5) := by rw [crK5]
end arms

grind_pattern [ind_grind] crW_nil => crW (n + 1) m nP mo ml ro rl
grind_pattern [ind_grind] crW_cons => crW (n + 1) m nP mo ml ro rl
grind_pattern [ind_grind] crK1_fail => crK1 n nP mo ml ro rl (some (r1, m1))
grind_pattern [ind_grind] crK1_ok => crK1 n nP mo ml ro rl (some (r1, m1))
grind_pattern [ind_grind] crK2_fail => crK2 n nP mo ml ro rl m1 (some (r2, m2))
grind_pattern [ind_grind] crK2_ok => crK2 n nP mo ml ro rl m1 (some (r2, m2))
grind_pattern [ind_grind] crK3_fail => crK3 n nP mo ml ro rl m2 (some r3)
grind_pattern [ind_grind] crK3_ok => crK3 n nP mo ml ro rl m2 (some r3)
grind_pattern [ind_grind] crK4_fail => crK4 n c (some (r4, m4))
grind_pattern [ind_grind] crK4_ok => crK4 n c (some (r4, m4))
grind_pattern [ind_grind] crK5_some => crK5 (some (r5, m5))

theorem classReadRecCls_spec (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_read_rec_cls" = some classReadRecCls) (n : Nat) :
    ∀ (s₀ : St) (nP mo ml ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_rec_cls" [nP, mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ crW n s₀.mem nP mo ml ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ nP mo ml ro rl; rw [invoke_eq _ hp]; simp only [callFn, classReadRecCls]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ nP mo ml ro rl
    rw [invoke_eq _ hp]
    simp only [callFn, classReadRecCls]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "open_pis_at_fvars_f" n, fvarHead_spec p hfh hv n,
        classOfMotiveVar_spec p hf hcm n, slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20) [rdW_eq]


theorem findIdx_lt (p : Nat) : ∀ (l : List Nat) (i : Nat), l.findIdx? (· == p) = some i → i < l.length := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons a t ih =>
    intro i h
    simp only [List.findIdx?_cons] at h
    by_cases hb : (a == p) = true
    · simp [hb] at h; subst h; simp
    · simp only [hb, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      have := ih j hj
      simp; omega

theorem cmv_lt (nP : Nat) (ms : List Nat) (pv i : Nat)
    (h : ConRon.Arena.classOfMotiveVar nP ms pv = some i) : i < ms.length := by
  simp only [ConRon.Arena.classOfMotiveVar] at h
  split at h
  · exact findIdx_lt _ ms i h
  · simp at h

theorem decNL_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} (h : o + l ≤ iwTop m) :
    decNL m' o l = decNL m o l := by
  simp only [decNL]
  apply mapM_opt_congr
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [iwN, nat?, iwA]
  rw [hg.2.2.1 (o + j) (by omega)]

theorem decRS_fields {m : Mem} {p : Nat} {R : RecShape} (h : decRS m p = some R) :
    ∃ q, iwN m p = some q ∧ decCVp m q = some R.cvR ∧ iwN m (p + 2) = some R.mI := by
  simp only [decRS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, rP, hrP, mI, hmI, tg, htg, rh, hrh, rfl⟩ := h
  exact ⟨q, hq, hcv, hmI⟩


section crsteps
variable (nP : Nat) (motPos : List Nat) (rc : RecShape) (rest : List RecShape) (a a1 a2 a4 : AState)

theorem cr_fail1 (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (none, a1)) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (none, a1) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, Except.bind]
  rfl

theorem cr_fail2 (xs : List EIdx) (concl : EIdx)
    (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (some (xs, concl), a1))
    (hrun2 : (ConRon.Arena.fvarHead concl) a1 = .ok (none, a2)) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (none, a2) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, hrun2, Except.bind]
  rfl

theorem cr_fail3 (xs : List EIdx) (concl : EIdx) (i : Nat)
    (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (some (xs, concl), a1))
    (hrun2 : (ConRon.Arena.fvarHead concl) a1 = .ok (some i, a2))
    (hc : ConRon.Arena.classOfMotiveVar nP motPos i = none) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (none, a2) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, hrun2, hc, Except.bind]
  rfl

theorem cr_fail4 (xs : List EIdx) (concl : EIdx) (i c : Nat)
    (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (some (xs, concl), a1))
    (hrun2 : (ConRon.Arena.fvarHead concl) a1 = .ok (some i, a2))
    (hc : ConRon.Arena.classOfMotiveVar nP motPos i = some c)
    (hrun4 : (ConRon.Arena.classReadRecCls nP motPos rest) a2 = .ok (none, a4)) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (none, a4) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, hrun2, hc, hrun4, Except.bind]
  rfl

theorem cr_ok (xs : List EIdx) (concl : EIdx) (i c : Nat) (cs : List Nat)
    (hrun1 : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (some (xs, concl), a1))
    (hrun2 : (ConRon.Arena.fvarHead concl) a1 = .ok (some i, a2))
    (hc : ConRon.Arena.classOfMotiveVar nP motPos i = some c)
    (hrun4 : (ConRon.Arena.classReadRecCls nP motPos rest) a2 = .ok (some cs, a4)) :
    (ConRon.Arena.classReadRecCls nP motPos (rc :: rest)) a = .ok (some (c :: cs), a4) := by
  simp only [ConRon.Arena.classReadRecCls, bind, StateT.bind, hrun1, hrun2, hc, hrun4, Except.bind]
  rfl
end crsteps

/-- `class_read_rec_cls`'s result against the twin's `Option (List Nat)`. -/
def CrRes (m' : Mem) (r : List Word) : Option (List Nat) → Prop
  | none => r.headD 0 = 0
  | some cs => r.headD 0 = 1 ∧
      decNL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some cs ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m'

theorem crW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (nP mo ml ro rl : Word) (r : List Word) (recs : List RecShape)
      (motPos : List Nat),
    crW n m nP mo ml ro rl = some (r, m') → StageR dn vis fe m a →
    decPL m (decRS m) ro.toNat rl.toNat = some recs →
    (∀ m1, IWGrow m m1 → decPL m1 (decRS m1) ro.toNat rl.toNat = some recs) →
    decNL m mo.toNat ml.toNat = some motPos → mo.toNat + ml.toNat ≤ iwTop m →
    ro.toNat + rl.toNat < 2 ^ 64 → (∀ R ∈ recs, R.mI + 1 < 2 ^ 64) →
    ∃ res a', (ConRon.Arena.classReadRecCls nP.toNat motPos recs).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ CrRes m' r res := by
  induction n with
  | zero => intro m m' a nP mo ml ro rl r recs motPos h; simp [crW] at h
  | succ n ih =>
    intro m m' a nP mo ml ro rl r recs motPos h hS hrecs hstab hmot hmt hb hmI
    by_cases hrl : rl = 0
    · rw [crW_nil n m nP mo ml ro rl hrl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : rl.toNat = 0 := by rw [hrl]; rfl
      rw [hz] at hrecs
      simp [decPL] at hrecs
      subst hrecs
      refine ⟨some [], a, rfl, hS, IWGrow.refl m, ?_⟩
      simp [CrRes, decNL]
    · have hpos : 1 ≤ rl.toNat := by
        rcases Nat.eq_zero_or_pos rl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hrl
        · omega
      obtain ⟨r1, hr1⟩ : ∃ r1, rl.toNat = r1 + 1 := ⟨rl.toNat - 1, by omega⟩
      rw [hr1] at hrecs
      obtain ⟨p0, rc, rest, rfl, hp0, hrc, hrest⟩ := decPL_cons hrecs
      obtain ⟨q, hq, hcv, hmIq⟩ := decRS_fields hrc
      have hro64 : ro.toNat < 2 ^ 64 := ro.toNat_lt
      have e0 : UInt64.ofNat ro.toNat = ro := UInt64.ofNat_toNat
      have hrd0 := iwN_rdW hp0 (by omega)
      rw [e0] at hrd0
      have hp0b : p0 < 2 ^ 64 := hrd0.2
      have hrdq := iwN_rdW hq (by omega)
      have hIW64 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
      have hrdm := iwN_off (k := 2) hmIq (by have := iwN_lt hmIq; omega)
      simp only [show UInt64.ofNat 2 = 2 from rfl] at hrdm
      obtain ⟨-, -, htyp⟩ := decCV_some (a := erA m) (q := q) hcv
      have hqb : q < 2 ^ 64 := hrdq.2
      have hE64 : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
      have hq3 : q + 3 < 2 ^ 64 := by
        cases hw : (m.arr64 EREC)[q + 3]? with
        | none => simp [hd?, erA, hw] at htyp
        | some w =>
          have := (Array.getElem?_eq_some_iff.mp hw).1
          omega
      obtain ⟨wt, hwt, hwtlt, hwtd⟩ := erH_rdW htyp hq3
      have hq3w : UInt64.ofNat q + 3 = UInt64.ofNat (q + 3) := by simp [UInt64.ofNat_add]
      have hmIw : (UInt64.ofNat rc.mI + 1).toNat = rc.mI + 1 := by
        have h1 := hmI rc (List.mem_cons_self ..)
        have hh : (UInt64.ofNat rc.mI).toNat = rc.mI := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
        rw [UInt64.toNat_add, hh]
        show (rc.mI + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt h1
      simp only [crW_cons n m nP mo ml ro rl hrl, hrd0.1, hrdm.2, hrdq.1, hq3w, hwt] at h
      cases hs : stubM "open_pis_at_fvars_f" m [UInt64.ofNat rc.mI + 1, wt, 0] with
      | none => rw [hs] at h; simp [crK1] at h
      | some r1m =>
        obtain ⟨r1', m1⟩ := r1m
        rw [hs] at h
        obtain ⟨res1, a1, hrun1, hS1, hg1, hdec1⟩ :=
          openPisAtFvarsF_spec dn vis fe (UInt64.ofNat rc.mI + 1) wt 0 hwtlt m m1 a r1' hs hS
        have hrun1' : (openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0) a = .ok (res1, a1) := by
          have := hrun1
          rw [hmIw, hwtd] at this
          have h0 : (0 : Word).toNat = 0 := rfl
          rw [h0] at this
          exact this
        cases res1 with
        | none =>
          have h0 : r1'.headD 0 = 0 := hdec1
          rw [crK1, if_pos h0] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨none, a1, cr_fail1 nP.toNat motPos rc rest a a1 hrun1', hS1, hg1, rfl⟩
        | some xl =>
          obtain ⟨xs, concl⟩ := xl
          obtain ⟨h1, -, hleaf⟩ := hdec1
          have h0 : r1'.headD 0 ≠ 0 := by rw [h1]; decide
          rw [crK1, if_neg h0] at h
          have hleaf3 : r1'.tail.tail.tail.headD 0 = (r1'.drop 3).headD 0 := by
            cases r1' with
            | nil => rfl
            | cons a1' t1 => cases t1 with
              | nil => rfl
              | cons a2' t2 => cases t2 <;> rfl
          rw [hleaf3] at h
          obtain ⟨hl1, hl2⟩ := hleaf
          cases hf : fvarHeadW m1 ((r1'.drop 3).headD 0) with
          | none => rw [hf] at h; simp [crK2] at h
          | some r2m =>
            obtain ⟨r2, m2⟩ := r2m
            rw [hf] at h
            obtain ⟨x, a2, hrun2, hS2, hg2, hr2, hxb⟩ :=
              fvarHeadW_ok dn vis fe m1 m2 a1 ((r1'.drop 3).headD 0) hl1 r2 hf hS1
            have hrun2' : (ConRon.Arena.fvarHead concl) a1 = .ok (x, a2) := by
              rw [← hl2]; exact hrun2
            cases x with
            | none =>
              have hr20 : r2.headD 0 = 0 := by rw [hr2]; rfl
              rw [crK2, if_pos hr20] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨none, a2, cr_fail2 nP.toNat motPos rc rest a a1 a2 xs concl hrun1' hrun2',
                hS2, hg1.trans hg2, rfl⟩
            | some i =>
              have hi64 : i < 2 ^ 64 := hxb i rfl
              have hr20 : r2.headD 0 ≠ 0 := by rw [hr2]; show (1 : Word) ≠ 0; decide
              have hr2t : r2.tail.headD 0 = UInt64.ofNat i := by rw [hr2]; rfl
              rw [crK2, if_neg hr20, hr2t] at h
              have hmot2 : decNL m2 mo.toNat ml.toNat = some motPos := by
                rw [decNL_grow (hg1.trans hg2) hmt]; exact hmot
              have hmlb : mo.toNat + ml.toNat < 2 ^ 64 := by
                have := hS2.2
                have := iwTop m
                have hh := hmt
                have h3 := hS.2.2.2.1
                have h4 := hS.2.1
                omega
              cases hc : cmvW (n - 1) m2 nP mo ml (UInt64.ofNat i) with
              | none => rw [hc] at h; simp [crK3] at h
              | some r3 =>
                rw [hc] at h
                have hcm := cmvW_ok (n - 1) m2 nP mo ml (UInt64.ofNat i) r3 motPos hmot2 hmlb hc
                rw [UInt64.toNat_ofNat_of_lt' hi64] at hcm
                cases co : ConRon.Arena.classOfMotiveVar nP.toNat motPos i with
                | none =>
                  rw [co] at hcm
                  have hr30 : r3.headD 0 = 0 := by rw [hcm]; rfl
                  rw [crK3, if_pos hr30] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨none, a2, cr_fail3 nP.toNat motPos rc rest a a1 a2 xs concl i hrun1' hrun2' co,
                    hS2, hg1.trans hg2, rfl⟩
                | some cc =>
                  rw [co] at hcm
                  have hr30 : r3.headD 0 ≠ 0 := by rw [hcm]; show (1 : Word) ≠ 0; decide
                  have hr3t : r3.tail.headD 0 = UInt64.ofNat cc := by rw [hcm]; rfl
                  have hcc64 : cc < 2 ^ 64 := by
                    have := cmv_lt _ _ _ _ co
                    have := decNL_length m2 hmot2
                    have := ml.toNat_lt
                    omega
                  rw [crK3, if_neg hr30, hr3t] at h
                  cases hr : crW n m2 nP mo ml (ro + 1) (rl - 1) with
                  | none => rw [hr] at h; simp [crK4] at h
                  | some r4m =>
                    obtain ⟨r4, m4⟩ := r4m
                    rw [hr] at h
                    have hro1 : (ro + 1).toNat = ro.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
                    have hrl1 : (rl - 1).toNat = r1 := by
                      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
                    have hrest' : ∀ m3, IWGrow m2 m3 → decPL m3 (decRS m3) (ro + 1).toNat (rl - 1).toNat = some rest := by
                      intro m3 hg3
                      have := hstab m3 ((hg1.trans hg2).trans hg3)
                      rw [hr1] at this
                      obtain ⟨p0', x', ys', heq, -, -, hrest''⟩ := decPL_cons this
                      rw [hro1, hrl1, (List.cons.inj heq).2]; exact hrest''
                    have hmt2 : mo.toNat + ml.toNat ≤ iwTop m2 := Nat.le_trans hmt (hg1.trans hg2).1
                    have hb' : (ro + 1).toNat + (rl - 1).toNat < 2 ^ 64 := by rw [hro1, hrl1]; omega
                    have hmI' : ∀ R ∈ rest, R.mI + 1 < 2 ^ 64 := fun R hR => hmI R (List.mem_cons_of_mem _ hR)
                    have hrest2 := hrest' m2 (IWGrow.refl m2)
                    obtain ⟨res4, a4, hrun4, hS4, hg4, hres4⟩ := ih m2 m4 a2 nP mo ml (ro + 1) (rl - 1) r4 rest
                      motPos hr hS2 hrest2 hrest' hmot2 hmt2 hb' hmI'
                    have hg14 := (hg1.trans hg2).trans hg4
                    cases res4 with
                    | none =>
                      have hr40 : r4.headD 0 = 0 := hres4
                      rw [crK4, if_pos hr40] at h
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ⟨none, a4, cr_fail4 nP.toNat motPos rc rest a a1 a2 a4 xs concl i cc hrun1' hrun2' co hrun4,
                        hS4, hg14, rfl⟩
                    | some cs =>
                      obtain ⟨hr41, hdn4, hle4⟩ := hres4
                      have hr40 : r4.headD 0 ≠ 0 := by rw [hr41]; decide
                      rw [crK4, if_neg hr40] at h
                      cases hcw : consW n m4 (UInt64.ofNat cc) (r4.tail.headD 0) (r4.tail.tail.headD 0) with
                      | none => rw [hcw] at h; simp [crK5] at h
                      | some r5m =>
                        obtain ⟨r5, m5⟩ := r5m
                        rw [hcw, crK5_some] at h
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        obtain ⟨hS5, hg5, hdn5, htop5⟩ := consW_stageN hcw hS4 hle4 hdn4
                        refine ⟨some (cc :: cs), a4, cr_ok nP.toNat motPos rc rest a a1 a2 a4 xs concl i cc cs
                          hrun1' hrun2' co hrun4, hS5, hg14.trans hg5, ?_⟩
                        refine ⟨rfl, ?_, ?_⟩
                        · simpa [UInt64.toNat_ofNat_of_lt' hcc64] using hdn5
                        · simpa using Nat.le_of_eq htop5


/-- **`class_read_rec_cls` refines `classReadRecCls`** (through the `open_pis_at_fvars_f` stub,
`fvar_head`, `class_of_motive_var` and `sl_cons`). The hypothesis `hstab` says that the recursor
records stay decodable across the pool's growth (they lie below the pool's top: `decRS` of a record
below the tops is stable under `IWGrow`; not proved here). -/
@[refines ConRon.Arena.classReadRecCls]
theorem classReadRecCls_refines (p : Prog) (hfh : p.lookup "fvar_head" = some fvarHead)
    (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
    (hcm : p.lookup "class_of_motive_var" = some classOfMotiveVar)
    (hc : p.lookup "iw_copy" = some iwCopy) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_read_rec_cls" = some classReadRecCls) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nP mo ml ro rl : Word)
    (recs : List RecShape) (motPos : List Nat) (hS : StageR dn vis fe s₀.mem a₀)
    (hrecs : decPL s₀.mem (decRS s₀.mem) ro.toNat rl.toNat = some recs)
    (hstab : ∀ m1, IWGrow s₀.mem m1 → decPL m1 (decRS m1) ro.toNat rl.toNat = some recs)
    (hmot : decNL s₀.mem mo.toNat ml.toNat = some motPos) (hmt : mo.toNat + ml.toNat ≤ iwTop s₀.mem)
    (hb : ro.toNat + rl.toNat < 2 ^ 64) (hmI : ∀ R ∈ recs, R.mI + 1 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_rec_cls" [nP, mo, ml, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classReadRecCls nP.toNat motPos recs) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classReadRecCls nP.toNat motPos recs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      CrRes s'.mem r (AM.res (ConRon.Arena.classReadRecCls nP.toNat motPos recs) a₀); ⊤⦄ := by
  refine triple_post (classReadRecCls_spec p hfh hv hf hcm hc ha hsc hp n s₀ nP mo ml ro rl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hS', hg, hres⟩ := crW_ok dn vis fe n _ _ a₀ nP mo ml ro rl r recs motPos hm hS
    hrecs hstab hmot hmt hb hmI
  obtain ⟨hok, hst, hrs⟩ := AM.of_run_ok (ConRon.Arena.classReadRecCls nP.toNat motPos recs) a₀ a' res hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hrs]; exact hres⟩


/-! ## Constant records are stable under the pool's growth -/

/-- `q`'s constant-value record lies below the `EREC` top (its four words and its level-parameter
slice). -/
def CVExt (m : Mem) (q : Nat) : Prop :=
  q + 4 ≤ erTop m ∧ ∀ o l, nat? (erA m) (q + 1) = some o → nat? (erA m) (q + 2) = some l →
    o + l ≤ erTop m

theorem decCVp_grow_r {m m' : Mem} (hg : IWGrow m m') {q : Nat} (hq : CVExt m q) :
    decCVp m' q = decCVp m q := by
  have hag : ∀ i, i < erTop m → (erA m')[i]? = (erA m)[i]? := fun i hi => by
    simp only [erA]; exact hg.2.2.2 i hi
  have hn : ∀ i, i < erTop m → nat? (erA m') i = nat? (erA m) i := fun i hi => by
    simp only [nat?, hag i hi]
  have hh : ∀ {k : IdxKind} i, i < erTop m → (hd? (erA m') i : Option (Idx k)) = hd? (erA m) i :=
    fun i hi => by simp only [hd?, hag i hi]
  obtain ⟨hq4, hl⟩ := hq
  simp only [decCVp, decCV]
  rw [hh q (by omega), hh (q + 3) (by omega)]
  have hlist : (hlist? (erA m') (q + 1) : Option (List (Idx IdxKind.name))) = hlist? (erA m) (q + 1) := by
    simp only [hlist?]
    rw [hn (q + 1) (by omega), hn (q + 1 + 1) (by omega)]
    cases ho : nat? (erA m) (q + 1) with
    | none => simp
    | some o =>
      cases hl' : nat? (erA m) (q + 1 + 1) with
      | none => simp
      | some l =>
        try simp only [Option.bind_some]
        apply hslice?_congr
        intro j hj
        have := hl o l ho hl'
        exact hag (o + j) (by omega)
  rw [hlist]


theorem decPL_eq_bind {α : Type} (m : Mem) (f : Nat → Option α) : ∀ (l o : Nat),
    decPL m f o l = (decNL m o l).bind (fun ps => ps.mapM f) := by
  intro l
  induction l with
  | zero => intro o; simp [decPL, decNL]
  | succ l ih =>
    intro o
    rw [decPL_succ_do, decNL_succ, ih (o + 1)]
    cases hp : iwN m o with
    | none => simp
    | some p =>
      cases hf : f p with
      | none => cases hr : decNL m (o + 1) l <;> simp [hf, hr]
      | some x =>
        cases hr : decNL m (o + 1) l with
        | none => simp
        | some ps => simp [hf]

theorem CVExt_grow {m m' : Mem} (hg : IWGrow m m') {q : Nat} (hq : CVExt m q) : CVExt m' q := by
  obtain ⟨h1, h2⟩ := hq
  have hn : ∀ i, i < erTop m → nat? (erA m') i = nat? (erA m) i := fun i hi => by
    simp only [nat?, erA]; rw [hg.2.2.2 i hi]
  refine ⟨Nat.le_trans h1 hg.2.1, fun o l ho hl => ?_⟩
  rw [hn (q + 1) (by omega)] at ho
  rw [hn (q + 2) (by omega)] at hl
  exact Nat.le_trans (h2 o l ho hl) hg.2.1

theorem mapM_decCVp_grow {m m' : Mem} (hg : IWGrow m m') :
    ∀ (ps : List Nat), (∀ q ∈ ps, CVExt m q) → ps.mapM (decCVp m') = ps.mapM (decCVp m)
  | [], _ => rfl
  | q :: ps, h => by
    simp only [List.mapM_cons]
    rw [decCVp_grow_r hg (h q (List.mem_cons_self ..)),
      mapM_decCVp_grow hg ps (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))]


/-! ## `class_read_classes` (loop rewritten as recursion: the rest, then `sl_cons` at a motive) -/

/-- A class-key record lies below the pool's top, with its datum slice. -/
def CKExt (m : Mem) (k : Nat) : Prop :=
  k + 4 ≤ iwTop m ∧ ∀ o l, iwN m (k + 2) = some o → iwN m (k + 3) = some l → o + l ≤ iwTop m

theorem decCK_grow {m m' : Mem} (hg : IWGrow m m') {k : Nat} (hk : CKExt m k) :
    decCK m' k = decCK m k := by
  obtain ⟨h1, h2⟩ := hk
  have hiw : ∀ i, i < iwTop m → iwN m' i = iwN m i := fun i hi => by
    simp only [iwN, nat?, iwA]; rw [hg.2.2.1 i hi]
  have hh : ∀ {kk : IdxKind} i, i < iwTop m → (iwH m' i : Option (Idx kk)) = iwH m i :=
    fun i hi => by simp only [iwH, hd?, iwA]; rw [hg.2.2.1 i hi]
  simp only [decCK]
  rw [hh k (by omega), hh (k + 1) (by omega)]
  have hat : decAt m' (decHL (k := IdxKind.expr) m') (k + 2) = decAt m (decHL (k := IdxKind.expr) m) (k + 2) := by
    simp only [decAt]
    rw [hiw (k + 2) (by omega), hiw (k + 2 + 1) (by omega)]
    cases ho : iwN m (k + 2) with
    | none => simp
    | some o =>
      cases hl : iwN m (k + 2 + 1) with
      | none => simp
      | some l =>
        show decHL m' o l = decHL m o l
        exact decHL_grow hg (h2 o l ho (by simpa using hl))
  rw [hat]

theorem mapM_decCK_grow {m m' : Mem} (hg : IWGrow m m') :
    ∀ (ps : List Nat), (∀ k ∈ ps, CKExt m k) → ps.mapM (decCK m') = ps.mapM (decCK m)
  | [], _ => rfl
  | k :: ps, h => by
    simp only [List.mapM_cons]
    rw [decCK_grow hg (h k (List.mem_cons_self ..)),
      mapM_decCK_grow hg ps (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]

theorem CKExt_grow {m m' : Mem} (hg : IWGrow m m') {k : Nat} (hk : CKExt m k) : CKExt m' k := by
  obtain ⟨h1, h2⟩ := hk
  have hiw : ∀ i, i < iwTop m → iwN m' i = iwN m i := fun i hi => by
    simp only [iwN, nat?, iwA]; rw [hg.2.2.1 i hi]
  refine ⟨Nat.le_trans h1 hg.1, fun o l ho hl => ?_⟩
  rw [hiw (k + 2) (by omega)] at ho
  rw [hiw (k + 3) (by omega)] at hl
  exact Nat.le_trans (h2 o l ho hl) hg.1


mutual
/-- **The model of `class_read_classes`.** -/
def rcW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, so, sl =>
    if sl = 0 then some ([0, 0], m)
    else rcK1 n (rdW (m.arr64 IW) so) (rcW n m (so + 1) (sl - 1))

/-- After the recursive call. -/
def rcK1 (n : Nat) (sp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if rdW (m1.arr64 IW) sp = 0 then
      rcK2 (consW n m1 (rdW (m1.arr64 IW) (sp + 1)) (r.headD 0) (r.tail.headD 0))
    else some ([r.headD 0, r.tail.headD 0], m1)

/-- After `sl_cons`. -/
def rcK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0, r.tail.headD 0], m2)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (so sl sp : Word) (r : List Word)
theorem rcW_nil (h : sl = 0) : rcW (n + 1) m so sl = some ([0, 0], m) := by simp [rcW, h]
theorem rcW_cons (h : sl ≠ 0) : rcW (n + 1) m so sl =
    rcK1 n (rdW (m.arr64 IW) so) (rcW n m (so + 1) (sl - 1)) := by simp [rcW, h]
theorem rcK1_mot (h : rdW (m1.arr64 IW) sp = 0) : rcK1 n sp (some (r, m1)) =
    rcK2 (consW n m1 (rdW (m1.arr64 IW) (sp + 1)) (r.headD 0) (r.tail.headD 0)) := by
  rw [rcK1, if_pos h]
theorem rcK1_min (h : rdW (m1.arr64 IW) sp ≠ 0) : rcK1 n sp (some (r, m1)) =
    some ([r.headD 0, r.tail.headD 0], m1) := by
  rw [rcK1, if_neg h]
theorem rcK2_some : rcK2 (some (r, m2)) = some ([r.headD 0, r.tail.headD 0], m2) := by rw [rcK2]
end arms

grind_pattern [ind_grind] rcW_nil => rcW (n + 1) m so sl
grind_pattern [ind_grind] rcW_cons => rcW (n + 1) m so sl
grind_pattern [ind_grind] rcK1_mot => rcK1 n sp (some (r, m1))
grind_pattern [ind_grind] rcK1_min => rcK1 n sp (some (r, m1))
grind_pattern [ind_grind] rcK2_some => rcK2 (some (r, m2))

theorem classReadClasses_spec (p : Prog) (hc : p.lookup "iw_copy" = some iwCopy)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_read_classes" = some classReadClasses) (n : Nat) :
    ∀ (s₀ : St) (so sl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_classes" [so, sl]
    ⦃fun r s' => LocEq s' s₀ ∧ rcW n s₀.mem so sl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ so sl; rw [invoke_eq _ hp]; simp only [callFn, classReadClasses]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ so sl
    rw [invoke_eq _ hp]
    simp only [callFn, classReadClasses]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slCons_specW p ha hc hsc n, ih] <;>
      finish (gen := 20) [rdW_eq]


theorem decCS_motive_key {m : Mem} {p : Nat} {key : ClassKey} (h : decCS m p = some (.motive key)) :
    ∃ kp, iwN m (p + 1) = some kp ∧ decCK m kp = some key := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨kp, hkp, k0, hk0, hk⟩ := h
    injection hk with hk
    subst hk
    exact ⟨kp, hkp, hk0⟩
  | 1, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, _, h⟩ := h; obtain ⟨_, _, h⟩ := h; obtain ⟨_, _, h⟩ := h; cases h
  | (k + 2), h => simp at h

/-- The slots' key records lie below the pool's top. -/
def SlotsExt (m : Mem) (so sl : Nat) : Prop :=
  so + sl ≤ iwTop m ∧ ∀ j, j < sl → ∀ sp, iwN m (so + j) = some sp →
    sp + 5 ≤ iwTop m ∧ ∀ kp, iwN m sp = some 0 → iwN m (sp + 1) = some kp → CKExt m kp

theorem SlotsExt_cons {m : Mem} {so sl : Nat} (h : SlotsExt m so (sl + 1)) :
    (∀ sp, iwN m so = some sp → sp + 5 ≤ iwTop m ∧
      ∀ kp, iwN m sp = some 0 → iwN m (sp + 1) = some kp → CKExt m kp) ∧ SlotsExt m (so + 1) sl := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun sp hsp => h2 0 (by omega) sp (by simpa using hsp), by omega, fun j hj sp hsp => ?_⟩
  exact h2 (j + 1) (by omega) sp (by rw [show so + (j + 1) = so + 1 + j by omega]; exact hsp)

theorem SlotsExt_grow {m m' : Mem} (hg : IWGrow m m') {so sl : Nat} (h : SlotsExt m so sl) :
    SlotsExt m' so sl := by
  obtain ⟨h1, h2⟩ := h
  have hiw : ∀ i, i < iwTop m → iwN m' i = iwN m i := fun i hi => by
    simp only [iwN, nat?, iwA]; rw [hg.2.2.1 i hi]
  refine ⟨Nat.le_trans h1 hg.1, fun j hj sp hsp => ?_⟩
  rw [hiw _ (by omega)] at hsp
  obtain ⟨hs5, hk⟩ := h2 j hj sp hsp
  refine ⟨Nat.le_trans hs5 hg.1, fun kp h0 h1' => ?_⟩
  rw [hiw _ (by omega)] at h0 h1'
  exact CKExt_grow hg (hk kp h0 h1')

/-- What `class_read_classes` returns: a slice of key pointers decoding to the keys. -/
def CcRes (m' : Mem) (r : List Word) (keys : List ClassKey) : Prop :=
  ∃ ptrs, decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ptrs ∧
    decPL m' (decCK m') (r.headD 0).toNat (r.tail.headD 0).toNat = some keys ∧
    (∀ k ∈ ptrs, CKExt m' k) ∧ (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'

theorem rcW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (a : AState) (n : Nat) :
    ∀ (m m' : Mem) (so sl : Word) (r : List Word) (slots : List ClassSlot),
    rcW n m so sl = some (r, m') → StageR dn vis fe m a →
    decPL m (decCS m) so.toNat sl.toNat = some slots → SlotsExt m so.toNat sl.toNat →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ CcRes m' r (ConRon.Arena.ClassRead.classes slots) := by
  induction n with
  | zero => intro m m' so sl r slots h; simp [rcW] at h
  | succ n ih =>
    intro m m' so sl r slots h hS hslots hext
    by_cases hsl : sl = 0
    · rw [rcW_nil n m so sl hsl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hz : sl.toNat = 0 := by rw [hsl]; rfl
      rw [hz] at hslots
      simp [decPL] at hslots
      subst hslots
      exact ⟨hS, IWGrow.refl m, [], by simp [decNL], by simp [decPL, ConRon.Arena.ClassRead.classes],
        by simp, by simp⟩
    · have hpos : 1 ≤ sl.toNat := by
        rcases Nat.eq_zero_or_pos sl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hsl
        · omega
      obtain ⟨l1, hl1⟩ : ∃ l1, sl.toNat = l1 + 1 := ⟨sl.toNat - 1, by omega⟩
      rw [hl1] at hslots hext
      obtain ⟨sp, cs, rest, rfl, hsp, hcs, hrest⟩ := decPL_cons hslots
      obtain ⟨hhead, hextt⟩ := SlotsExt_cons hext
      obtain ⟨hs5, hkext⟩ := hhead sp hsp
      have hso64 : so.toNat < 2 ^ 64 := so.toNat_lt
      have hIW64 : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
      have hso1 : (so + 1).toNat = so.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := iwN_lt hsp; omega
      have hsl1 : (sl - 1).toNat = l1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
      have e0 : UInt64.ofNat so.toNat = so := UInt64.ofNat_toNat
      have hrd0 := iwN_rdW hsp (by have := iwN_lt hsp; omega)
      rw [e0] at hrd0
      rw [rcW_cons n m so sl hsl, hrd0.1] at h
      cases hr : rcW n m (so + 1) (sl - 1) with
      | none => rw [hr] at h; simp [rcK1] at h
      | some r2m =>
        obtain ⟨r2, m1⟩ := r2m
        rw [hr] at h
        obtain ⟨hS1, hg1, ptrs, hdn1, hdp1, hext1, htop1⟩ :=
          ih m m1 (so + 1) (sl - 1) r2 rest hr hS (by rw [hso1, hsl1]; exact hrest)
            (by rw [hso1, hsl1]; exact hextt)
        have hsp64 : sp < 2 ^ 64 := hrd0.2
        have htag := decCS_tag hcs
        have htag' := iwN_rdW htag (by omega)
        have hiw1 : ∀ i, i < iwTop m → (m1.arr64 IW)[i]? = (m.arr64 IW)[i]? := hg1.2.2.1
        have hspw : rdW (m1.arr64 IW) (UInt64.ofNat sp) = UInt64.ofNat (if cs.isMinor then 1 else 0) := by
          rw [← htag'.1]
          simp only [rdW]
          rw [hiw1 _ (by simp [UInt64.toNat_ofNat_of_lt' hsp64]; omega)]
        cases cs with
        | minor c0 C0 ihs =>
          have hnz : rdW (m1.arr64 IW) (UInt64.ofNat sp) ≠ 0 := by
            rw [hspw]; simp [ClassSlot.isMinor]
          rw [rcK1_min n m1 (UInt64.ofNat sp) r2 hnz] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hS1, hg1, ptrs, ?_, ?_, hext1, ?_⟩
          · simpa using hdn1
          · simpa [ConRon.Arena.ClassRead.classes] using hdp1
          · simpa using htop1
        | motive key =>
          have hz : rdW (m1.arr64 IW) (UInt64.ofNat sp) = 0 := by
            rw [hspw]; simp [ClassSlot.isMinor]
          rw [rcK1_mot n m1 (UInt64.ofNat sp) r2 hz] at h
          obtain ⟨kp, hkp, hck⟩ := decCS_motive_key hcs
          have hk0 := hkext kp (by simpa [ClassSlot.isMinor] using htag) hkp
          have hrk := iwN_off (k := 1) hkp (by have := iwN_lt hkp; omega)
          simp only [show UInt64.ofNat 1 = 1 from rfl] at hrk
          have hsp1 : (UInt64.ofNat sp + 1).toNat = sp + 1 := by
            rw [UInt64.toNat_add]; simp [UInt64.toNat_ofNat_of_lt' hsp64]
            have := iwN_lt hkp; omega
          have hrk1 : rdW (m1.arr64 IW) (UInt64.ofNat sp + 1) = UInt64.ofNat kp := by
            have h2 := hrk.2
            simp only [rdW] at h2 ⊢
            rw [hsp1] at h2 ⊢
            rw [hiw1 _ (by omega)]
            exact h2
          rw [hrk1] at h
          cases hcw : consW n m1 (UInt64.ofNat kp) (r2.headD 0) (r2.tail.headD 0) with
          | none => rw [hcw] at h; simp [rcK2] at h
          | some r3m =>
            obtain ⟨r3, m2⟩ := r3m
            rw [hcw, rcK2_some] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hS2, hg2, hdn2, ht2⟩ := consW_stageN hcw hS1 htop1 hdn1
            have hg12 := hg1.trans hg2
            have hkb : (UInt64.ofNat kp).toNat = kp := UInt64.toNat_ofNat_of_lt' (by
              have := iwN_rdW hkp (by omega); exact this.2)
            have hdn2' : decNL m2 (r3.headD 0).toNat (r3.tail.headD 0).toNat = some (kp :: ptrs) := by
              simpa [hkb] using hdn2
            refine ⟨hS2, hg12, kp :: ptrs, by simpa using hdn2', ?_, ?_, by simpa using Nat.le_of_eq ht2⟩
            · simp only [List.headD_cons, List.tail_cons]
              rw [decPL_eq_bind, hdn2']
              simp only [Option.bind_some, List.mapM_cons]
              rw [decCK_grow hg12 hk0, hck]
              have h2 : ptrs.mapM (decCK m1) = some (ConRon.Arena.ClassRead.classes rest) := by
                rw [decPL_eq_bind, hdn1] at hdp1; simpa using hdp1
              rw [mapM_decCK_grow hg2 ptrs hext1, h2]
              simp [ConRon.Arena.ClassRead.classes]
            · intro k hk
              simp only [List.mem_cons] at hk
              rcases hk with rfl | hk
              · exact CKExt_grow hg12 hk0
              · exact CKExt_grow hg2 (hext1 k hk)


/-- **`class_read_classes` refines `ClassRead.classes`** (through `sl_cons`): the result slice holds
the motives' key records, in prefix order. `hext` says the slots' key records lie below the pool's
top (so they stay decodable as the pool grows). -/
@[refines ConRon.Arena.ClassRead.classes]
theorem classReadClasses_refines (p : Prog) (hc : p.lookup "iw_copy" = some iwCopy)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_read_classes" = some classReadClasses) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (so sl : Word) (slots : List ClassSlot)
    (hS : StageR dn vis fe s₀.mem a₀)
    (hslots : decPL s₀.mem (decCS s₀.mem) so.toNat sl.toNat = some slots)
    (hext : SlotsExt s₀.mem so.toNat sl.toNat) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_classes" [so, sl]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      CcRes s'.mem r (ConRon.Arena.ClassRead.classes slots); ⊤⦄ := by
  refine triple_post (classReadClasses_spec p hc ha hsc hp n s₀ so sl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hS', hg, hres⟩ := rcW_ok dn vis fe a₀ n _ _ so sl r slots hm hS hslots hext
  exact ⟨hl, hS', hg, hres⟩

end L.Ind
