module

public import ConAgua.Arena.RecClassSpec.CloseLams
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConRon.Bridge.Grind
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.RecClass

@[expose] public section

/-!
# Classes: `ConRon.Arena.ClassRead.classes`

The refinement theorems `classReadClasses_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

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
  obtain ⟨hA, hS, hG⟩ := copyW_get n _ _ _ _ _ h (by rw [hq1]; omega) (by rw [hq1, hm1sz]; omega)
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
    · rw [ite_eq_left hi, ite_eq_right (by omega), ite_eq_left hi, hm1get, ite_eq_right (by omega)]
    · rw [ite_eq_right hi, hm1get]
      by_cases hiq : i = q.toNat
      · simp [hiq]
      · rw [ite_eq_right hiq, ite_eq_right hiq, ite_eq_right hi]
  -- the other arrays and CTL
  have hCTL : ∀ i, i ≠ (200 : Word) → rdW (m'.arr64 CTL) i = rdW (m.arr64 CTL) i := by
    intro i hi
    rw [hA CTL (by decide)]; exact consPre_ctl m x l i hi
  have hEREC : m'.arr64 EREC = m.arr64 EREC := by
    rw [hA EREC (by decide)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hEREC1 : m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) := by
    rw [hA (tier1 EREC) (by decide)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have htop : rdW (m'.arr64 CTL) 200 = q + (l + 1) := by
    rw [hA CTL (by decide)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), rdW_set64]; simp [hc, hq]
  refine ⟨?_, { iw := ?_, er := ?_, iwGet := ?_, erGet := ?_, er1 := ?_, er1Get := ?_ }, ⟨?_, ?_, ?_⟩,
    htop⟩
  · rw [hl1, decNL_succ]
    have h0 : iwN m' q.toNat = some x.toNat := by
      simp [iwN, nat?, iwA, aread_apply, hget]
    rw [h0]
    have : decNL m' (q.toNat + 1) l.toNat = some xs := by
      rw [← hxs]
      simp only [decNL]
      apply mapM_opt_congr
      intro j hj
      have hj' : j < l.toNat := List.mem_range.mp hj
      simp only [iwN, nat?, iwA, aread_apply, hget]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      have : o.toNat + (q.toNat + 1 + j - (q.toNat + 1)) = o.toNat + j := by omega
      simp
    simp [this]
  · have : (q + (l + 1)).toNat = q.toNat + (l.toNat + 1) := by
      rw [UInt64.toNat_add, hl1]; simp; omega
    simp only [iwTop, htop, this, hq]; omega
  · simp only [erTop, hCTL 129 (by decide)]; exact Nat.le_refl _
  · intro i hi
    simp only [iwTop, hq] at hi
    rw [hget, ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro i _; rw [hEREC]
  · simp only [erecTop1, hCTL 130 (by decide)]; exact Nat.le_refl _
  · intro i _; rw [hEREC1]
  · intro b hb hbc
    rw [hA b (by simpa using hb)]; simp only [consPre, allocMem]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by simpa using hb), Mem.arr64_set64_ne _ _ _ _ _ hbc]
  · intro i hi; exact hCTL i (by simpa using hi)
  · intro b
    by_cases hb : b = IW
    · subst hb; rw [hS, hm1sz]
    · rw [hA b hb]; simp only [consPre, allocMem, size_set64]

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
  simp only [h0, ite_false] at h
  simp only [allocW] at h
  by_cases h1 : m.len64 IW < rdW (m.arr64 CTL) 200
  · simp [h1] at h
  by_cases h2 : m.len64 IW - rdW (m.arr64 CTL) 200 < l + 1
  · simp [h1, h2] at h
  simp only [h1, h2, ite_false] at h
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
  rw [← ht, hf.size IW]
  simp only [consW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, ite_false] at h
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
theorem consW_stageN {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List Nat}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hxs : decNL m o.toNat l.toNat = some xs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (x.toNat :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  have hsz := hS.iw.iwSize
  have hc := hS.iw.ctl
  obtain ⟨hr, hd, hg, hf, -, ht⟩ := consW_decN h hsz hc hsrc hxs
  have hroom := consW_roomN h hsz hc hsrc hxs
  subst hr
  exact ⟨⟨CheckR.frame_iw hf hS.check, IWOK.of_iw hf hS.iw hroom⟩, hg,
    by simpa using hd, by simpa using ht⟩

theorem gafF_afr {m m' : Mem} {args r : List Word} (h : gafF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (gafF_frame h)

/-! ## `class_read_rec_cls` -/

theorem decNL_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} (h : o + l ≤ iwTop m) :
    decNL m' o l = decNL m o l := by
  simp only [decNL]
  apply mapM_opt_congr
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [iwN, nat?, iwA, aread_apply, aread_apply]
  rw [hg.iwGet (o + j) (by omega)]

/-! ## Constant records are stable under the pool's growth -/

/-- `q`'s constant-value record decodes (its four words and its level-parameter slice are all
defined in the record pool, in either tier), so it stays decoded as the pool grows. -/
def CVExt (m : Mem) (q : Nat) : Prop := (decCVp m q).isSome

theorem CVExt.of_dec {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv) : CVExt m q := by
  simp [CVExt, h]

theorem decCVp_grow_r {m m' : Mem} (hg : IWGrow m m') {q : Nat} (hq : CVExt m q) :
    decCVp m' q = decCVp m q := by
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp hq
  rw [hcv]; exact ArrExt.decCV hg.ext hcv

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
      | none => cases hr : decNL m (o + 1) l <;> simp [hf]
      | some x =>
        cases hr : decNL m (o + 1) l with
        | none => simp
        | some ps => simp [hf]

theorem CVExt_grow {m m' : Mem} (hg : IWGrow m m') {q : Nat} (hq : CVExt m q) : CVExt m' q := by
  simp only [CVExt, decCVp_grow_r hg hq]; exact hq

/-! ## `class_read_classes` (loop rewritten as recursion: the rest, then `sl_cons` at a motive) -/

/-- A class-key record lies below the pool's top, with its datum slice. -/
def CKExt (m : Mem) (k : Nat) : Prop :=
  k + 4 ≤ iwTop m ∧ ∀ o l, iwN m (k + 2) = some o → iwN m (k + 3) = some l → o + l ≤ iwTop m ∨ l = 0

theorem decCK_grow {m m' : Mem} (hg : IWGrow m m') {k : Nat} (hk : CKExt m k) :
    decCK m' k = decCK m k := by
  obtain ⟨h1, h2⟩ := hk
  have hiw : ∀ i, i < iwTop m → iwN m' i = iwN m i := fun i hi => by
    simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet i hi]
  have hh : ∀ {kk : IdxKind} i, i < iwTop m → (iwH m' i : Option (Idx kk)) = iwH m i :=
    fun i hi => by simp only [iwH, hd?, iwA, aread_apply, aread_apply]; rw [hg.iwGet i hi]
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
        rcases h2 o l ho (by simpa using hl) with hb | rfl
        · exact decHL_grow hg hb
        · simp [decHL, hslice?]
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
    simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet i hi]
  refine ⟨Nat.le_trans h1 hg.iw, fun o l ho hl => ?_⟩
  rw [hiw (k + 2) (by omega)] at ho
  rw [hiw (k + 3) (by omega)] at hl
  exact (h2 o l ho hl).imp_left fun h => Nat.le_trans h hg.iw

l_model classReadClasses_spec (p : Prog) (hc : p.lookup "iw_copy" = some iwCopy)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hsc : p.lookup "sl_cons" = some slCons)
    (hp : p.lookup "class_read_classes" = some classReadClasses)
  fns [hp ↦ rcW list]
  specs [slCons_specW p ha hc hsc n]
  grind [arena_grind]

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
    sp + 2 ≤ iwTop m ∧ ∀ kp, iwN m sp = some 0 → iwN m (sp + 1) = some kp → CKExt m kp

theorem SlotsExt_cons {m : Mem} {so sl : Nat} (h : SlotsExt m so (sl + 1)) :
    (∀ sp, iwN m so = some sp → sp + 2 ≤ iwTop m ∧
      ∀ kp, iwN m sp = some 0 → iwN m (sp + 1) = some kp → CKExt m kp) ∧ SlotsExt m (so + 1) sl := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun sp hsp => h2 0 (by omega) sp (by simpa using hsp), by omega, fun j hj sp hsp => ?_⟩
  exact h2 (j + 1) (by omega) sp (by rw [show so + (j + 1) = so + 1 + j by omega]; exact hsp)

/-- What `class_read_classes` returns: a slice of key pointers decoding to the keys. -/
def CcRes (m' : Mem) (r : List Word) (keys : List ClassKey) : Prop :=
  ∃ ptrs, decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ptrs ∧
    decPL m' (decCK m') (r.headD 0).toNat (r.tail.headD 0).toNat = some keys ∧
    (∀ k ∈ ptrs, CKExt m' k) ∧ (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'

theorem rcW_ok (_dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (a : AState) (n : Nat) :
    ∀ (m m' : Mem) (so sl : Word) (r : List Word) (slots : List ClassSlot),
    rcW n m so sl = some (r, m') → StageR vis fe m a →
    decPL m (decCS m) so.toNat sl.toNat = some slots → SlotsExt m so.toNat sl.toNat →
    StageR vis fe m' a ∧ IWGrow m m' ∧ CcRes m' r (ConRon.Arena.ClassRead.classes slots) := by
  induction n with
  | zero => intro m m' so sl r slots h; simp [rcW] at h
  | succ n ih =>
    intro m m' so sl r slots h hS hslots hext
    by_cases hsl : sl = 0
    · rw [rcW.arm1 n m so sl hsl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hz : sl.toNat = 0 := by rw [hsl]; rfl
      rw [hz] at hslots
      simp [decPL] at hslots
      subst hslots
      exact ⟨hS, IWGrow.refl m, [], by simp [decNL], by simp [decPL, ConRon.Arena.ClassRead.classes],
        by simp, by simp⟩
    · obtain ⟨l1, hl1, hsl1⟩ := wordSucc_of_ne hsl
      rw [hl1] at hslots hext
      obtain ⟨sp, cs, rest, rfl, hsp, hcs, hrest⟩ := decPL_cons hslots
      obtain ⟨hhead, hextt⟩ := SlotsExt_cons hext
      obtain ⟨hs5, hkext⟩ := hhead sp hsp
      have hso64 : so.toNat < 2 ^ 64 := so.toNat_lt
      have hIW64 : (m.arr64 IW).size < 2 ^ 64 := hS.iw.iwSize
      have hso1 : (so + 1).toNat = so.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := iwN_lt hsp; omega
      have e0 : UInt64.ofNat so.toNat = so := UInt64.ofNat_toNat
      have hrd0 := iwN_rdW hsp (by have := iwN_lt hsp; omega)
      rw [e0] at hrd0
      rw [rcW.arm2 n m so sl hsl, hrd0.1] at h
      obtain ⟨⟨r2, m1⟩, hr, h⟩ := of_K h rfl
      obtain ⟨hS1, hg1, ptrs, hdn1, hdp1, hext1, htop1⟩ :=
        ih m m1 (so + 1) (sl - 1) r2 rest hr hS (by rw [hso1, hsl1]; exact hrest)
          (by rw [hso1, hsl1]; exact hextt)
      have hsp64 : sp < 2 ^ 64 := hrd0.2
      have htag := decCS_tag hcs
      have htag' := iwN_rdW htag (by omega)
      have hiw1 : ∀ i, i < iwTop m → (m1.arr64 IW)[i]? = (m.arr64 IW)[i]? := hg1.iwGet
      have hspw : rdW (m1.arr64 IW) (UInt64.ofNat sp) = UInt64.ofNat (if cs.isMinor then 1 else 0) := by
        rw [← htag'.1]
        simp only [rdW]
        rw [hiw1 _ (by simp [UInt64.toNat_ofNat_of_lt' hsp64]; omega)]
      cases cs with
      | minor c0 C0 ihs =>
        have hnz : rdW (m1.arr64 IW) (UInt64.ofNat sp) ≠ 0 := by
          rw [hspw]; simp [ClassSlot.isMinor]
        rw [rcW.k_class_read_classes.arm2 n (UInt64.ofNat sp) r2 m1 hnz] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨hS1, hg1, ptrs, ?_, ?_, hext1, ?_⟩
        · simpa using hdn1
        · simpa [ConRon.Arena.ClassRead.classes] using hdp1
        · simpa using htop1
      | motive key =>
        have hz : rdW (m1.arr64 IW) (UInt64.ofNat sp) = 0 := by
          rw [hspw]; simp [ClassSlot.isMinor]
        rw [rcW.k_class_read_classes.arm1 n (UInt64.ofNat sp) r2 m1 hz] at h
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
        obtain ⟨⟨r3, m2⟩, hcw, h⟩ := of_K h rfl
        rw [rcW.k_sl_cons.arm1] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
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
    (hS : StageR vis fe s₀.mem a₀)
    (hslots : decPL s₀.mem (decCS s₀.mem) so.toNat sl.toNat = some slots)
    (hext : SlotsExt s₀.mem so.toNat sl.toNat) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_read_classes" [so, sl]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      CcRes s'.mem r (ConRon.Arena.ClassRead.classes slots); ⊤⦄ := by
  refine triple_post (classReadClasses_spec p hc ha hsc hp n s₀ so sl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hS', hg, hres⟩ := rcW_ok dn vis fe a₀ n _ _ so sl r slots hm hS hslots hext
  exact ⟨hl, hS', hg, hres⟩

end L.Ind

end
