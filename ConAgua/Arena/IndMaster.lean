module

import ConAgua.Arena.IndCopy2
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.DerRel
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndCopy
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# The master callees of the inductive stage, under the stage relation (lane `indproofs`)

The stage calls master's expression constructors (`intern_bvar`, `intern_fvar`, `intern_sort`,
`intern_const`, `mk_app`, `mk_lam`, `mk_forall`, `mk_let`, `mk_proj`). Their L side is master's
word model and spec (`binternW`/`internBVar_spec`, `mkAppW`/`mkApp_spec`, …); this file gives the
twin side in the stage's shape, sorry-free: from `StageR` a model run is a successful
`internE` run, with `StageR` after (the writes are below array 64 and `CTL[64]`, the twin keeps
caches and pins: `StageR.of_walk`) and the pool only grown. A refinement through these callees
uses the master spec inside `vcgen` and the `_stage` lemma afterwards, as for a stub's `RelAM`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The frame of a `mk_*` tail: the interning's, plus the derived-range array. -/
theorem mkK_frame {A : ArrId} (hA : A ≠ CTL) {c s d : Word} {x : Option (Word × Mem)} {m m' : Mem}
    {r : Word} {A₀ : List TieredArray} {C₀ : List Word}
    (hx : ∀ r₁ m₁, x = some (r₁, m₁) → MemFrame A₀ C₀ m m₁) (h : mkK A c s d x = some (r, m')) :
    MemFrame (A :: (tier1 A) :: A₀) C₀ m m' := by
  match x, hx, h with
  | some (r₁, m₁), hx, h =>
    rw [mkK_some] at h
    split at h
    · cases h
    · rename_i m₂ hP
      cases h
      exact ((hx _ _ rfl).mono (fun b hb => by simp [hb]) (by simp)).trans
        ((derPutW_frame A hA _ _ _ _ _ _ hP).mono (by simp) (by simp))

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
  {r : Word}

/-- From the `AM.ok`/`ArenaD`/`AM.res` triple of a master `_ok`/`_D` lemma, a frame below 64
and `Keeps cp`: the stage relation after. -/
theorem stage_of_ok {op : AM EIdx} {A : List TieredArray} {C : List Word} (hS : StageR vis fe m a)
    (hok : AM.ok op a) (hD : ArenaD m' (AM.st op a)) (hres : AM.res op a = decE r)
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, InStoreTier b) (hC : ∀ x ∈ C, x.toNat < 64)
    (hk : Keeps cp op) (h01 : (0 : Word) ∉ C ∧ (1 : Word) ∉ C := by decide) :
    ∃ a', op.run a = .ok (decE r, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  have hrun := AM.run_of_ok op a hok
  rw [hres] at hrun
  obtain ⟨h1, h2⟩ := StageR.of_walk hS hD hf hA hC (hk.run hrun) h01
  exact ⟨_, hrun, h1, h2⟩

theorem internBVar_stage (hS : StageR vis fe m a) (u : Word) (hI : binternW m u = some (r, m')) :
    ∃ a', (internE (.bvar u.toNat)).run a = .ok (decE r, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hS.check.arena u r m' hI
  have hI₂ := hI
  exact stage_of_ok hS hok hD hres (consInternM_frame bvarCS_wf hI₂)
    (by simp [tier1, ConsSch.wset, bvarCS, BREC, BSLOT]) (by simp [bvarCS]) (keeps_internE _)

theorem internFVar_stage (hS : StageR vis fe m a) (u ty : Word) (hty : ty.toNat < 2 ^ 32)
    (hI : fvinternW m u ty = some (r, m')) :
    ∃ a', (internE (.fvar u.toNat (decE ty))).run a = .ok (decE r, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.check.arena u ty r hty m' hI
  exact stage_of_ok hS hok hD hres (fvinternW_frame m u ty _ _ hI)
    (by simp [tier1, FVREC, FVSLOT, FVLP]) (by simp) (keeps_internE _)

theorem internSort_stage (hS : StageR vis fe m a) (u : Word) (hu : u.toNat < 2 ^ 32)
    (hI : sointernW m u = some (r, m')) :
    ∃ a', (internE (.sort (decI u))).run a = .ok (decE r, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internSort_D m a hS.check.arena u r hu m' hI
  exact stage_of_ok hS hok hD hres (sointernW_frame m u _ _ hI)
    (by simp [tier1, SOREC, SOSLOT, SOLP]) (by simp) (keeps_internE _)

theorem internConst_stage (hS : StageR vis fe m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (hI : ceinternW m f x = some (r, m')) :
    ∃ a', (internE (.const (decI (k := .name) f) (decI (k := .levels) x))).run a = .ok (decE r, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internConst_D m a hS.check.arena f x r hf hx m' hI
  exact stage_of_ok hS hok hD hres (ceinternW_frame m f x _ _ hI)
    (by simp [tier1, CREC, CSLOT, CLP]) (by simp) (keeps_internE _)

theorem mkApp_stage (hS : StageR vis fe m a) (f x : Word) (hI : mkAppW m f x = some (r, m')) :
    ∃ a', (internE (.app (decE f) (decE x))).run a = .ok (decE r, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkApp_ok m a hS.check.arena f x r m' hI
  have hf : MemFrame [ADER, tier1 ADER, AREC, tier1 AREC, ASLOT, tier1 ASLOT] [4, 5] m m' := by
    unfold mkAppW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame appCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, ADER, AREC, ASLOT]) (by simp) (keeps_internE _)

theorem mkLam_stage (hS : StageR vis fe m a) (t b : Word) (hI : mkLamW m t b = some (r, m')) :
    ∃ a', (internE (.lam (decE t) (decE b))).run a = .ok (decE r, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkLam_ok m a hS.check.arena t b r m' hI
  have hf : MemFrame [LADER, tier1 LADER, LAREC, tier1 LAREC, LASLOT, tier1 LASLOT] [28, 29] m m' := by
    unfold mkLamW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame lamCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, LADER, LAREC, LASLOT]) (by simp) (keeps_internE _)

theorem mkForall_stage (hS : StageR vis fe m a) (t b : Word) (hI : mkForallW m t b = some (r, m')) :
    ∃ a', (internE (.forallE (decE t) (decE b))).run a = .ok (decE r, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkForall_ok m a hS.check.arena t b r m' hI
  have hf : MemFrame [FADER, tier1 FADER, FAREC, tier1 FAREC, FASLOT, tier1 FASLOT] [30, 31] m m' := by
    unfold mkForallW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame forallCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, FADER, FAREC, FASLOT]) (by simp) (keeps_internE _)

theorem mkLet_stage (hS : StageR vis fe m a) (t v b : Word) (hI : mkLetW m t v b = some (r, m')) :
    ∃ a', (internE (.letE (decE t) (decE v) (decE b))).run a = .ok (decE r, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkLet_ok m a hS.check.arena t v b r m' hI
  have hf : MemFrame [LEDER, tier1 LEDER, LEREC, tier1 LEREC, LESLOT, tier1 LESLOT] [20, 21] m m' := by
    unfold mkLetW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame letCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, LEDER, LEREC, LESLOT]) (by simp) (keeps_internE _)

theorem mkProj_stage (hS : StageR vis fe m a) (n i e : Word) (hI : mkProjW m n i e = some (r, m')) :
    ∃ a', (internE (.proj (decI n) i.toNat (decE e))).run a = .ok (decE r, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkProj_ok m a hS.check.arena n i e r m' hI
  have hf : MemFrame [PJDER, tier1 PJDER, PJREC, tier1 PJREC, PJSLOT, tier1 PJSLOT] [32, 33] m m' := by
    unfold mkProjW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame projCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, PJDER, PJREC, PJSLOT]) (by simp) (keeps_internE _)

end

/-! ## The pool's `sl_cons` under the stage relation -/

/-- The pool's top after a `sl_cons` stays within the array. -/
theorem consW_room {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hx : x.toNat < 2 ^ 32) {k : IdxKind} {xs : List (Idx k)} (hxs : decHL m o.toNat l.toNat = some xs) :
    iwTop m' ≤ (m'.arr64 IW).size := by
  obtain ⟨-, -, -, hf, -, ht⟩ := consW_dec h hsz hc hsrc hx hxs
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
theorem consW_stage {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {k : IdxKind} {xs : List (Idx k)}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m) (hx : x.toNat < 2 ^ 32)
    (hxs : decHL m o.toNat l.toNat = some xs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (decI x :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  have hsz := hS.iw.iwSize
  have hc := hS.iw.ctl
  obtain ⟨hr, hd, hg, hf, -, ht⟩ := consW_dec h hsz hc hsrc hx hxs
  have hroom := consW_room h hsz hc hsrc hx hxs
  subst hr
  exact ⟨⟨CheckR.frame_iw hf hS.check, IWOK.of_iw hf hS.iw hroom⟩, hg, by simpa using hd,
    by simpa using ht⟩

/-! ## Level interning under the stage relation -/

/-- `DerR` reads only the expression tables. -/
theorem DerR.lvl {m : Mem} {a a' : AState} (h1 : a'.store.pers = a.store.pers := by rfl)
    (h2 : a'.store.scr = a.store.scr := by rfl) (hD : DerR m a) : DerR m a' := by
  obtain ⟨b, f, s, c, l, ap, la, fa, le, pj⟩ := hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [DerT2, h1, h2] <;> assumption

section levels
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
  {r : Word}

/-- A level interning (a proto run over a level lens) from the stage relation: the expression
tables, caches and pins are untouched, so `DerR` and `cp` carry over. -/
theorem stage_of_level {β : Type} [BEq β] [Hashable β] {L : Lens β LDer .level} {op : AM LIdx}
    {key : β} {tag : UInt32} {wide : Bool} {pf : Option LIdx} {d : LDer} {err : CheckError}
    {A : List TieredArray} {C : List Word}
    (hS : StageR vis fe m a) (hrun : op.run a = protoRun L key tag wide pf d err a) (hok : AM.ok op a)
    (hR : ArenaR m' (AM.st op a)) (hres : AM.res op a = decI r) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b.arr < 42 ∨ (54 < b.arr ∧ b.arr < 64)) (hC : ∀ x ∈ C, x.toNat < 64)
    (hset : ∀ t, (DerR m' a → DerR m' (L.setP a t)) ∧ cp (L.setP a t) = cp a)
    (hsetS : ∀ t, (DerR m' a → DerR m' (L.setS a t)) ∧ cp (L.setS a t) = cp a)
    (hmode : ModeOK m') :
    ∃ a', op.run a = .ok (decI r, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hf (fun b hb => by have := hA b hb; omega) a
    hS.check.arena.der
  have hcs := AM.st_proto L op key tag wide pf d err a hrun hok
  have hDk : DerR m' (AM.st op a) ∧ cp (AM.st op a) = cp a := by
    rcases hcs with h | ⟨t, h⟩ | ⟨t, h⟩ <;> rw [h]
    · exact ⟨hD₁, rfl⟩
    · exact ⟨(hset t).1 hD₁, (hset t).2⟩
    · exact ⟨(hsetS t).1 hD₁, (hsetS t).2⟩
  have hrun' := AM.run_of_ok op a hok
  rw [hres] at hrun'
  obtain ⟨h1, h2⟩ := StageR.of_walkM hS ⟨hR, hDk.1⟩ hf (fun b hb => by have := hA b hb; simp only [InStoreTier]; omega)
    hC hDk.2 hmode
  exact ⟨_, hrun', h1, h2⟩

theorem internParam_stage (hS : StageR vis fe m a) (u : Word) (hu : u.toNat < 2 ^ 32)
    (hI : pinternW m u = some (r, m')) :
    ∃ a', (internLNode (.param (decI u))).run a = .ok (decI r, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' := by
  have hR := hS.check.arena.base
  obtain ⟨hok, hX, hres⟩ := pintern_correct m a hR.param u hu _ _ hI
  have hL := pintern_hp m a hR.param u hu hR.paramHp _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame paramCS_wf hI₂
  exact stage_of_level hS (internLNode_param_run _ a) hok
    (hR.lift_param _ _ _ _ ⟨hX, hL⟩ hfr (AM.st_proto paramLens _ _ _ _ _ _ _ a (internLNode_param_run _ a) hok))
    hres hfr (by simp [tier1, ConsSch.wset, paramCS, PREC, PSLOT]) (by simp [paramCS]) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩)
    (hS.check.mode.frame hfr (by decide) (by decide))

theorem internZero_stage (hS : StageR vis fe m a) (hI : zinternW m = some (r, m')) :
    ∃ a', (internLNode .zero).run a = .ok (decI r, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' := by
  have hR := hS.check.arena.base
  obtain ⟨hok, hX, hres⟩ := zintern_correct m a hR.zero _ _ hI
  have hL := zintern_hp m a hR.zero hR.zeroHp _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame zeroCS_wf hI₂
  exact stage_of_level hS (internLNode_zero_run a) hok
    (hR.lift_zero _ _ _ _ ⟨hX, hL⟩ hfr (AM.st_proto zeroLens _ _ _ _ _ _ _ a (internLNode_zero_run a) hok))
    hres hfr (by simp [tier1, ConsSch.wset, zeroCS, ZREC, ZSLOT]) (by simp [zeroCS]) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩)
    (hS.check.mode.frame hfr (by decide) (by decide))

theorem internMax_stage (hS : StageR vis fe m a) (u v : Word) (hu : u.toNat < 2 ^ 32)
    (hv : v.toNat < 2 ^ 32) (hI : minternW m u v = some (r, m')) :
    ∃ a', (internLNode (.max (decI u) (decI v))).run a = .ok (decI r, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' := by
  have hR := hS.check.arena.base
  obtain ⟨hok, hX, hres⟩ := mintern_correct m a hR.max u v hu hv _ _ hI
  have hfr := minternW_frame m u v _ _ hI
  exact stage_of_level hS (internLNode_max_run _ _ a) hok
    (hR.lift_max _ _ _ _ ⟨hX, mintern_hp m a hR.max u v hu hv hR.maxHp (lvlHPW_or m a hR u v hu hv) _ _ hI⟩
      hfr (AM.st_proto maxLens _ _ _ _ _ _ _ a (internLNode_max_run _ _ a) hok))
    hres hfr (by simp [tier1, MREC, MSLOT, MHP]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩)
    (hS.check.mode.frame hfr (by decide) (by decide))

end levels

/-! ## `iw_alloc` under the stage relation -/

theorem allocW_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {k q : Word} (h : allocW m k = some (q, m1)) (hS : StageR vis fe m a) :
    StageR vis fe m1 a ∧ IWGrow m m1 ∧ q.toNat = iwTop m ∧ iwTop m1 = iwTop m + k.toNat := by
  have hsz := hS.iw.iwSize
  have hc := hS.iw.ctl
  obtain ⟨rfl, rfl, hroom⟩ := allocW_facts h hsz
  have hf := allocMem_frame m k
  have htop : iwTop (allocMem m k) = iwTop m + k.toNat := by
    simp only [iwTop, allocMem, rdW_set64]
    have h200 : UInt64.toNat 200 < (m.arr64 CTL).size := by simpa using hc
    rw [ite_eq_left ⟨trivial, trivial, h200⟩, UInt64.toNat_add]
    omega
  refine ⟨⟨CheckR.frame_iw hf hS.check, IWOK.of_iw hf hS.iw (by
    rw [htop, hf.size IW]; simp only [iwTop]; omega)⟩, ?_, rfl, htop⟩
  exact allocMem_grow m k (by simp only [iwTop]; omega) hc

/-! ## `erec_alloc` and the constant records, under the stage relation

`erAllocMem`, `erAllocW`, `erecAlloc_specW`, `erecPutMem`, `erecPut_specW`: `IndIface.lean`. -/

/-- Write `ws` at the tagged addresses `q, q + 1, …` (`erec_put`). -/
def wrER (m : Mem) (q : Word) : List Word → Mem
  | [] => m
  | x :: xs => wrER (erecPutMem m q x) (q + 1) xs

theorem erecPutMem_frame (m : Mem) (a v : Word) : MemFrame [EREC, tier1 EREC] [] m (erecPutMem m a v) := by
  refine ⟨fun b hb _ => ?_, fun x _ => by rw [erecPutMem_ctl], fun b => ?_⟩
  · rw [erecPutMem_arr, if_neg]
    unfold erTier; split <;> (intro e; subst e; simp at hb)
  · rw [erecPutMem_arr]; split <;> simp

theorem wrER_frame : ∀ (ws : List Word) (m : Mem) (q : Word),
    MemFrame [EREC, tier1 EREC] [] m (wrER m q ws)
  | [], m, q => MemFrame.refl _ _ _
  | x :: ws, m, q => (erecPutMem_frame m q x).trans (wrER_frame ws _ _)

theorem wrER_ctl : ∀ (ws : List Word) (m : Mem) (q : Word), (wrER m q ws).arr64 CTL = m.arr64 CTL
  | [], _, _ => rfl
  | x :: ws, m, q => by simp only [wrER]; rw [wrER_ctl ws, erecPutMem_ctl]

/-- The next address stays in the tier, one word on. -/
theorem erOff_succ {q : Word} (h : erOff q + 1 < 2 ^ 40) (h64 : q.toNat + 1 < 2 ^ 64) :
    erOff (q + 1) = erOff q + 1 ∧ erTier (q + 1) = erTier q := by
  have hq : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  simp only [erOff, erTier, hq] at h ⊢
  have e1 : (q.toNat + 1) % 2 ^ 40 = q.toNat % 2 ^ 40 + 1 := by omega
  have e2 : (q.toNat + 1) / 2 ^ 40 = q.toNat / 2 ^ 40 := by omega
  rw [e1, e2]; exact ⟨rfl, rfl⟩

/-- **What `wrER` leaves in the tier arrays**: the written words at their offsets (in bounds), every
other word as it was. -/
theorem wrER_get : ∀ (ws : List Word) (m : Mem) (q : Word),
    erOff q + ws.length ≤ 2 ^ 40 → q.toNat + ws.length < 2 ^ 64 → ∀ (b : TieredArray) (i : Nat),
    ((wrER m q ws).arr64 b)[i]? =
      if b = erTier q ∧ erOff q ≤ i ∧ i < erOff q + ws.length ∧ i < (m.arr64 b).size
      then ws[i - erOff q]? else (m.arr64 b)[i]?
  | [], m, q, _, _, b, i => by simp [wrER]; intro _ _ h; omega
  | [x], m, q, _, _, b, i => by
    simp only [wrER, erecPutMem_arr, List.length_singleton]
    by_cases e : b = erTier q
    · subst e
      simp only [ite_true, true_and, Array.getElem?_setIfInBounds]
      by_cases hi : erOff q = i
      · subst hi
        by_cases hb : erOff q < (m.arr64 (erTier q)).size
        · simp [hb]
        · simp [hb, Array.getElem?_eq_none (Nat.le_of_not_lt hb)]
      · rw [if_neg hi, if_neg (by omega)]
    · simp [e]
  | x :: y :: ws, m, q, h1, h2, b, i => by
    have hlen : (x :: y :: ws).length = ws.length + 2 := rfl
    rw [hlen] at h1 h2
    obtain ⟨ho, ht⟩ := erOff_succ (q := q) (by omega) (by omega)
    have ih := wrER_get (y :: ws) (erecPutMem m q x) (q + 1)
      (by simp only [List.length_cons, ho]; omega)
      (by simp only [List.length_cons]; rw [UInt64.toNat_add]; simp; omega) b i
    simp only [wrER] at ih ⊢
    rw [ih, ho, ht]
    simp only [List.length_cons, erecPutMem_arr]
    by_cases e : b = erTier q
    · subst e
      simp only [ite_true, true_and, Array.size_setIfInBounds, Array.getElem?_setIfInBounds]
      by_cases hi : erOff q = i
      · subst hi
        by_cases hb : erOff q < (m.arr64 (erTier q)).size
        · simp [hb]; omega
        · simp [hb, Array.getElem?_eq_none (Nat.le_of_not_lt hb)]
      · rw [if_neg hi]
        by_cases hr : erOff q + 1 ≤ i ∧ i < erOff q + 1 + (ws.length + 1) ∧ i < (m.arr64 (erTier q)).size
        · rw [if_pos hr, if_pos ⟨by omega, by omega, hr.2.2⟩]
          have : i - erOff q = (i - (erOff q + 1)) + 1 := by omega
          rw [this]; simp
        · rw [if_neg hr, if_neg (by omega)]
    · simp [e]

/-- `IWOK` across a writer of the record pool's arrays (sizes and tops kept). -/
theorem IWOK.of_er {m m' : Mem} (hf : MemFrame [EREC, tier1 EREC] [] m m') (h : IWOK m) : IWOK m' := by
  have hI := hf.arr IW (by decide) (by decide)
  have hc := hf.size CTL
  have h1 := (IWOK_iff m).1 h
  simp only [IWOK_iff, iwTop, erTop, erecTop1, hI, hc, hf.size EREC, hf.size (tier1 EREC),
    hf.ctl 129 (by simp), hf.ctl 130 (by simp), hf.ctl 200 (by simp)] at h1 ⊢
  exact h1

/-- **A record allocated in `EREC` and written**: `erec_alloc(ws.length)` then `ws` at the
returned address keeps the stage relation and grows the pools; the words read back through
`erecP`, the address in the flag's tier at its old top. -/
theorem erRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) (hS : StageR vis fe m a)
    (ws : List Word) (hk : k.toNat = ws.length) :
    StageR vis fe (wrER m1 q ws) a ∧ IWGrow m (wrER m1 q ws) ∧ erOff q = erTopOf m q ∧
      erTopOf (wrER m1 q ws) q = erTopOf m q + ws.length ∧ q.toNat < 2 ^ 41 ∧
      (q.toNat / 2 ^ 40 % 2 = 0 ↔ rdW (m.arr64 CTL) 1 = 0) ∧
      (∀ j < ws.length, erecP (wrER m1 q ws) (q.toNat + j) = ws[j]?) := by
  obtain ⟨hg1, hf1, hoff, htop1, hsz1, htier, hq41, hW1⟩ := erAllocW_spec h hS.iw
  have hfw := wrER_frame ws m1 q
  have hcw := wrER_ctl ws m1 q
  have hcap : (m.arr64 (erTier q)).size < 2 ^ 40 := by
    unfold erTier; split
    · exact hS.iw.erCap
    · exact hS.iw.er1Cap
  have hsz : ∀ b, (m1.arr64 b).size = (m.arr64 b).size := hf1.size
  have hm1 : ∀ b : TieredArray, b ≠ CTL → m1.arr64 b = m.arr64 b := fun b hb => hf1.arr b (by simp) hb
  have hget := wrER_get ws m1 q (by omega) (by omega)
  have hT : ∀ m' : Mem, m'.arr64 CTL = m1.arr64 CTL → erTopOf m' q = erTopOf m1 q := fun m' e => by
    simp only [erTopOf, erecTop, erecTop1, e]
  -- the growth from `m`
  have hgrow : ErecGrow m (wrER m1 q ws) := by
    refine ⟨?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
    · simp only [erecTop, hcw]; exact hg1.top
    · rw [hget, if_neg, hm1 _ (by decide)]
      rintro ⟨e, h2, -⟩
      have : erTopOf m q = erecTop m := by
        unfold erTier at e; unfold erTopOf; split at e
        · rename_i t; simp [t]
        · cases e
      omega
    · simp only [erecTop1, hcw]; exact hg1.top1
    · rw [hget, if_neg, hm1 _ (by decide)]
      rintro ⟨e, h2, -⟩
      have : erTopOf m q = erecTop1 m := by
        unfold erTier at e; unfold erTopOf; split at e
        · cases e
        · rename_i t; simp [t]
      omega
  have hfr : MemFrame [EREC, tier1 EREC] [129, 130] m (wrER m1 q ws) :=
    (hf1.mono (by simp) (by simp)).trans (hfw.mono (by simp) (by simp))
  have hW : IWOK (wrER m1 q ws) := IWOK.of_er hfw hW1
  have hI : (wrER m1 q ws).arr64 IW = m.arr64 IW := by
    rw [hfw.arr IW (by decide) (by decide), hm1 _ (by decide)]
  have h200 : rdW ((wrER m1 q ws).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hfr.ctl 200 (by simp)
  refine ⟨⟨CheckR.erGrow hS.check hfr hgrow, hW⟩, ⟨by simp only [iwTop, h200]; exact Nat.le_refl _,
    hgrow.top, fun i _ => by rw [hI], hgrow.get, hgrow.top1, hgrow.get1⟩, hoff, ?_, hq41, htier,
    fun j hj => ?_⟩
  · rw [hT _ hcw, htop1, hk]
  · have hjl : erOff q + j < 2 ^ 40 := by
      have e1 := hsz1; have e2 := htop1; have e3 := hk; have e4 := hcap; omega
    have hoj : (q.toNat + j) % 2 ^ 40 = erOff q + j := by unfold erOff at hjl ⊢; omega
    have htj : (q.toNat + j) / 2 ^ 40 % 2 = q.toNat / 2 ^ 40 % 2 := by
      have : (q.toNat + j) / 2 ^ 40 = q.toNat / 2 ^ 40 := by unfold erOff at hjl; omega
      rw [this]
    have hlt : erOff q + j < (m1.arr64 (erTier q)).size := by
      rw [hsz]; have e1 := hsz1; have e2 := htop1; have e3 := hk; omega
    have hgj := hget (erTier q) (erOff q + j)
    rw [if_pos ⟨rfl, by omega, by omega, hlt⟩, show erOff q + j - erOff q = j by omega] at hgj
    have htopw : erOff q + j < erTopOf (wrER m1 q ws) q := by
      rw [hT _ hcw, htop1]; have e3 := hk; omega
    unfold erecP
    rw [if_pos (show q.toNat + j < 2 ^ 64 by omega), htj, hoj]
    unfold erTopOf at htopw
    unfold erTier at hgj
    by_cases t : q.toNat / 2 ^ 40 % 2 = 0
    · simp only [t, ite_true] at htopw hgj ⊢; rw [if_pos htopw]; exact hgj
    · simp only [t, ite_false] at htopw hgj ⊢; rw [if_pos htopw]; exact hgj

theorem mapM_congr_of {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..), mapM_congr_of f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- **A copied constant value with a new type** decodes as `{cv with type := ty}`: the name and
the level-parameter slice words copied from `cv`'s record, the slice itself unchanged. -/
theorem decCV_copy {a a' : Nat → Option Word} {cq q : Nat} {cv : IConstantVal} {ty : Word} (N : Nat)
    (h : decCV a cq = some cv) (h0 : a' (q) = a (cq)) (h1 : a' (q + 1) = a (cq + 1))
    (h2 : a' (q + 2) = a (cq + 2)) (h3 : a' (q + 3) = some ty) (hty : ty.toNat < 2 ^ 32)
    (hlow : ∀ i < N, a' (i) = a (i))
    (hsl : ∀ lo ll, nat? a (cq + 1) = some lo → nat? a (cq + 2) = some ll → lo + ll ≤ N ∨ ll = 0) :
    decCV a' q = some { cv with type := decI ty } := by
  simp only [decCV, bind, Option.bind, pure] at h ⊢
  have hn : (hd? a' q : Option NIdx) = hd? a cq := by simp only [hd?, h0]
  rw [hn]
  cases e0 : (hd? a cq : Option NIdx) with
  | none => rw [e0] at h; simp at h
  | some nm =>
  rw [e0] at h; simp only at h ⊢
  simp only [hlist?, bind, Option.bind] at h ⊢
  have hl1 : nat? a' (q + 1) = nat? a (cq + 1) := by simp only [nat?, h1]
  have hl2 : nat? a' (q + 1 + 1) = nat? a (cq + 1 + 1) := by simp only [nat?, show q + 1 + 1 = q + 2 by omega, h2]
  rw [hl1, hl2]
  cases e1 : nat? a (cq + 1) with
  | none => rw [e1] at h; simp at h
  | some lo =>
  cases e2 : nat? a (cq + 1 + 1) with
  | none => rw [e1, e2] at h; simp at h
  | some ll =>
  rw [e1, e2] at h; simp only at h ⊢
  have hN := hsl lo ll e1 (by simpa using e2)
  have hs : (hslice? a' lo ll : Option (List NIdx)) = hslice? a lo ll := by
    simp only [hslice?]
    exact mapM_congr_of _ _ _ (fun j hj => by
      have := List.mem_range.mp hj
      simp only [hd?, hlow (lo + j) (by omega)])
  rw [hs]
  cases e3 : (hslice? a lo ll : Option (List NIdx)) with
  | none => rw [e3] at h; simp at h
  | some lps =>
  rw [e3] at h; simp only at h ⊢
  cases e4 : (hd? a (cq + 3) : Option EIdx) with
  | none => rw [e4] at h; simp at h
  | some t =>
  rw [e4] at h
  simp only [Option.some.injEq] at h
  subst h
  simp [hd?, h3, hty]

/-! ## `cv_new`: a fresh constant-value record -/

/-- The memory after the four writes of `cv_new`. -/
def cvNewMem (m1 : Mem) (q nm lo ll ty : Word) : Mem :=
  erecPutMem (erecPutMem (erecPutMem (erecPutMem m1 q nm) (q + 1) lo) (q + 2) ll) (q + 3) ty

/-- The model of `cv_new(nm, lo, ll, ty)`. -/
def cvNewW (m : Mem) (nm lo ll ty : Word) : Option (Word × Mem) :=
  match erAllocW m 4 with
  | none => none
  | some (q, m1) => some (q, cvNewMem m1 q nm lo ll ty)

theorem cvNewMem_eq (m1 : Mem) (q nm lo ll ty : Word) :
    cvNewMem m1 q nm lo ll ty = wrER m1 q [nm, lo, ll, ty] := by
  simp only [cvNewMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl]

theorem cvNew_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "cv_new" = some cvNew) (n : Nat) (s₀ : St) (nm lo ll ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_new" [nm, lo, ll, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ cvNewW s₀.mem nm lo ll ty = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cvNew]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        erecAlloc_specW p ha n, erecPut_specW p hpu n] <;>
      finish [cvNewW, cvNewMem]

/-- A word the record pool reads at `cq + j` (as a number) is `EREC⦃cq + j⦄`. -/
theorem erRd_add {m : Mem} {cq : Word} {j : Nat} {w : Word} (h : erecP m (cq.toNat + j) = some w)
    (hj : j < 2 ^ 64) : erRd m (cq + UInt64.ofNat j) = w ∧ (cq + UInt64.ofNat j).toNat = cq.toNat + j := by
  have hlt : cq.toNat + j < 2 ^ 64 := by
    rcases Nat.lt_or_ge (cq.toNat + j) (2 ^ 64) with h' | h'
    · exact h'
    · unfold erecP at h; rw [if_neg (by omega)] at h; cases h
  have e : (cq + UInt64.ofNat j).toNat = cq.toNat + j := by
    rw [UInt64.toNat_add]; simp; omega
  exact ⟨(erRd_of_erecP (by rw [e]; exact h)).1, e⟩

/-- **`cv_new` with the name and level parameters of the record at `cq`** keeps the stage
relation and decodes as `{cv with type := ty}`. -/
theorem cvNew_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq ty q : Word} {cv : IConstantVal}
    (h : cvNewW m (erRd m cq) (erRd m (cq + 1)) (erRd m (cq + 2)) ty = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCVp m cq.toNat = some cv) (hty : ty.toNat < 2 ^ 32) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ erOff q = erTopOf m q ∧ erTopOf m' q = erTopOf m q + 4 ∧
      q.toNat < 2 ^ 41 ∧ (q.toNat / 2 ^ 40 % 2 = 0 ↔ rdW (m.arr64 CTL) 1 = 0) ∧
      decCVp m' q.toNat = some { cv with type := decI ty } := by
  simp only [cvNewW] at h
  cases h1 : erAllocW m 4 with
  | none => rw [h1] at h; cases h
  | some x =>
  obtain ⟨q1, m1⟩ := x
  rw [h1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [cvNewMem_eq]
  obtain ⟨hS', hg, hq, htop, hq41, htier, hget⟩ := erRec_stage h1 hS
    [erRd m cq, erRd m (cq + 1), erRd m (cq + 2), ty] (by simp)
  refine ⟨hS', hg, hq, htop, hq41, htier, ?_⟩
  -- the source record's words
  simp only [decCVp, decCV, hlist?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv
  obtain ⟨nm, hnm, lps, ⟨lo, hlo, ll, hll, hlps⟩, t, ht, rfl⟩ := hcv
  obtain ⟨w0, hw0, hw0l, rfl⟩ := hd?_some hnm
  obtain ⟨w1, hw1, rfl⟩ : ∃ w, erA m (cq.toNat + 1) = some w ∧ w.toNat = lo := by
    simp only [nat?, Option.map_eq_some_iff] at hlo; exact hlo
  obtain ⟨w2, hw2, rfl⟩ : ∃ w, erA m (cq.toNat + 1 + 1) = some w ∧ w.toNat = ll := by
    simp only [nat?, Option.map_eq_some_iff] at hll; exact hll
  have r0 : erRd m cq = w0 := (erRd_of_erecP (by simpa [erA] using hw0)).1
  obtain ⟨r1, -⟩ := erRd_add (j := 1) (cq := cq) (m := m) (by simpa [erA] using hw1) (by decide)
  obtain ⟨r2, -⟩ := erRd_add (j := 2) (cq := cq) (m := m) (by simpa [erA, Nat.add_assoc] using hw2) (by decide)
  simp only [show (UInt64.ofNat 1 : Word) = 1 from rfl, show (UInt64.ofNat 2 : Word) = 2 from rfl] at r1 r2
  have g0 := hget 0 (by simp)
  have g1 := hget 1 (by simp)
  have g2 := hget 2 (by simp)
  have g3 := hget 3 (by simp)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero, r0, r1, r2] at g0 g1 g2 g3
  have hlps' : (hslice? (erecP m) w1.toNat w2.toNat : Option (List NIdx)) = some lps := hlps
  have hs : (hslice? (erecP (wrER m1 q1 [w0, w1, w2, ty])) w1.toNat w2.toNat : Option (List NIdx)) =
      some lps := by rw [r0, r1, r2] at hg; exact ArrExt.hslice? (IWGrow.ext hg) hlps'
  rw [r0, r1, r2]
  simp only [decCVp, decCV, hlist?, erA, nat?, hd?, g0, g1, Nat.add_assoc, g2, g3, hw0l, hty,
    ite_true, Option.map_some, bind, Option.bind_some, pure]
  rw [hs]; rfl

end L.Ind
