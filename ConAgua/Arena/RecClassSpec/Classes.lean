module

public import ConAgua.Arena.RecClassSpec.CloseLams
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndCallM
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
  sorry

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
theorem consW_stageN {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List Nat}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hxs : decNL m o.toNat l.toNat = some xs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decNL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (x.toNat :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  sorry

theorem gafF_afr {m m' : Mem} {args r : List Word} (h : gafF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (gafF_frame h)

/-! ## `class_read_rec_cls` -/

mutual
/-- **The model of `class_read_rec_cls`.** -/
def crW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, nP, mo, ml, ro, rl =>
    if rl = 0 then some ([1, 0, 0], m)
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 2) + 1 = 0 then none
    else crK1 cR n nP mo ml ro rl
      (cR n "open_pis_at_fvars_f"
        [rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 2) + 1,
         rdW (m.arr64 EREC) (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro) + 3), 0] m)

/-- After `open_pis_at_fvars_f`. -/
def crK1 (cR : CallM) (n : Nat) (nP mo ml ro rl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0, 0], m1)
    else crK2 cR n nP mo ml ro rl m1 (fvarHeadW m1 (r1.tail.tail.tail.headD 0))

/-- After `fvar_head`. -/
def crK2 (cR : CallM) (n : Nat) (nP mo ml ro rl : Word) (_m1 : Mem) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else crK3 cR n nP mo ml ro rl m2 (cmvW (n - 1) m2 nP mo ml (r2.tail.headD 0))

/-- After `class_of_motive_var`. -/
def crK3 (cR : CallM) (n : Nat) (nP mo ml ro rl : Word) (m2 : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r3 =>
    if r3.headD 0 = 0 then some ([0, 0, 0], m2)
    else crK4 n (r3.tail.headD 0) (crW cR n m2 nP mo ml (ro + 1) (rl - 1))

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

theorem decNL_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} (h : o + l ≤ iwTop m) :
    decNL m' o l = decNL m o l := by
  sorry

/-! ## Constant records are stable under the pool's growth -/

/-- `q`'s constant-value record lies below the `EREC` top (its four words and its level-parameter
slice). -/
def CVExt (m : Mem) (q : Nat) : Prop :=
  q + 4 ≤ erTop m ∧ ∀ o l, nat? (erA m) (q + 1) = some o → nat? (erA m) (q + 2) = some l →
    o + l ≤ erTop m ∨ l = 0

theorem decCVp_grow_r {m m' : Mem} (hg : IWGrow m m') {q : Nat} (hq : CVExt m q) :
    decCVp m' q = decCVp m q := by
  sorry

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
  sorry

/-! ## `class_read_classes` (loop rewritten as recursion: the rest, then `sl_cons` at a motive) -/

/-- A class-key record lies below the pool's top, with its datum slice. -/
def CKExt (m : Mem) (k : Nat) : Prop :=
  k + 4 ≤ iwTop m ∧ ∀ o l, iwN m (k + 2) = some o → iwN m (k + 3) = some l → o + l ≤ iwTop m ∨ l = 0

theorem decCK_grow {m m' : Mem} (hg : IWGrow m m') {k : Nat} (hk : CKExt m k) :
    decCK m' k = decCK m k := by
  sorry

theorem mapM_decCK_grow {m m' : Mem} (hg : IWGrow m m') :
    ∀ (ps : List Nat), (∀ k ∈ ps, CKExt m k) → ps.mapM (decCK m') = ps.mapM (decCK m)
  | [], _ => rfl
  | k :: ps, h => by
    simp only [List.mapM_cons]
    rw [decCK_grow hg (h k (List.mem_cons_self ..)),
      mapM_decCK_grow hg ps (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]

theorem CKExt_grow {m m' : Mem} (hg : IWGrow m m') {k : Nat} (hk : CKExt m k) : CKExt m' k := by
  sorry

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

theorem rcW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (a : AState) (n : Nat) :
    ∀ (m m' : Mem) (so sl : Word) (r : List Word) (slots : List ClassSlot),
    rcW n m so sl = some (r, m') → StageR vis fe m a →
    decPL m (decCS m) so.toNat sl.toNat = some slots → SlotsExt m so.toNat sl.toNat →
    StageR vis fe m' a ∧ IWGrow m m' ∧ CcRes m' r (ConRon.Arena.ClassRead.classes slots) := by
  sorry

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
