module

public import ConAgua.Arena.IWFrame
import ConAgua.Arena.RecLayout.CIDec
import ConAgua.Arena.IndCopy2
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.DerRel
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndCopy
import all ConAgua.Arena.IndIface
public import ConAgua.Arena.Env

@[expose] public section

/-!
# The master callees of the inductive stage, under the stage relation (lane `indproofs`)

The stage calls master's expression constructors (`intern_bvar`, `intern_fvar`, `intern_sort`,
`intern_const`, `mk_app`, `mk_lam`, `mk_forall`, `mk_let`, `mk_proj`). Their L side is master's
word model and spec (`binternW`/`internBVar_spec`, `mkAppW`/`mkApp_spec`, …); this file gives the
twin side in the stage's shape, fully proved: from `StageR` a model run is a successful
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

theorem wrER_frame : ∀ (ws : List Word) (m : Mem) (q : Word),
    MemFrame [EREC, tier1 EREC] [] m (wrER m q ws)
  | [], _m, _q => MemFrame.refl _ _ _
  | x :: ws, _m, _q => (erecPutMem_frame _m _q x).trans (wrER_frame ws _ _)

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
        · simp [hb]
      · rw [ite_eq_right hi, ite_eq_right (by omega)]
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
        · simp [hb]
      · rw [ite_eq_right hi]
        by_cases hr : erOff q + 1 ≤ i ∧ i < erOff q + 1 + (ws.length + 1) ∧ i < (m.arr64 (erTier q)).size
        · rw [ite_eq_left hr, ite_eq_left ⟨by omega, by omega, hr.2.2⟩]
          have : i - erOff q = (i - (erOff q + 1)) + 1 := by omega
          rw [this]; simp
        · rw [ite_eq_right hr, ite_eq_right (by omega)]
    · simp [e]

/-- Write the `some` words of `ws` at the tagged addresses `q, q + 1, …` and skip the `none`s: a
record written field by field (`erec_put(q + ⟪R.f⟫, …)`), its image `R.img …` from the record's
layout (`RecLayout/`), the words between the fields left as they were. -/
def wrERo (m : Mem) (q : Word) : List (Option Word) → Mem
  | [] => m
  | none :: xs => wrERo m (q + 1) xs
  | some x :: xs => wrERo (erecPutMem m q x) (q + 1) xs

theorem wrERo_frame : ∀ (ws : List (Option Word)) (m : Mem) (q : Word),
    MemFrame [EREC, tier1 EREC] [] m (wrERo m q ws)
  | [], _m, _q => MemFrame.refl _ _ _
  | none :: ws, _m, _q => wrERo_frame ws _ _
  | some x :: ws, _m, _q => (erecPutMem_frame _m _q x).trans (wrERo_frame ws _ _)

theorem wrERo_ctl : ∀ (ws : List (Option Word)) (m : Mem) (q : Word),
    (wrERo m q ws).arr64 CTL = m.arr64 CTL
  | [], _, _ => rfl
  | none :: ws, m, q => by simp only [wrERo]; rw [wrERo_ctl ws]
  | some x :: ws, m, q => by simp only [wrERo]; rw [wrERo_ctl ws, erecPutMem_ctl]

theorem wrERo_append : ∀ (xs ys : List (Option Word)) (m : Mem) (q : Word),
    wrERo m q (xs ++ ys) = wrERo (wrERo m q xs) (q + UInt64.ofNat xs.length) ys
  | [], ys, m, q => by simp [wrERo]
  | none :: xs, ys, m, q => by
    simp only [List.cons_append, wrERo, List.length_cons]
    rw [wrERo_append xs ys, UInt64.add_assoc]; congr 2
    apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add]; omega
  | some x :: xs, ys, m, q => by
    simp only [List.cons_append, wrERo, List.length_cons]
    rw [wrERo_append xs ys, UInt64.add_assoc]; congr 2
    apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add]; omega

/-- A list of words all stored is `wrER`. -/
theorem wrERo_map_some : ∀ (ws : List Word) (m : Mem) (q : Word),
    wrERo m q (ws.map some) = wrER m q ws
  | [], _, _ => rfl
  | x :: ws, m, q => by simp only [List.map_cons, wrERo, wrER]; rw [wrERo_map_some ws]

/-- **What `wrERo` leaves in the tier arrays**: the written words at their offsets (in bounds), every
other word as it was. -/
theorem wrERo_get : ∀ (ws : List (Option Word)) (m : Mem) (q : Word),
    erOff q + ws.length ≤ 2 ^ 40 → q.toNat + ws.length < 2 ^ 64 → ∀ (b : TieredArray) (i : Nat),
    ((wrERo m q ws).arr64 b)[i]? =
      if b = erTier q ∧ erOff q ≤ i ∧ i < erOff q + ws.length ∧ i < (m.arr64 b).size ∧
        (ws[i - erOff q]?).join.isSome
      then (ws[i - erOff q]?).join else (m.arr64 b)[i]?
  | [], m, q, _, _, b, i => by simp [wrERo]
  | [none], m, q, _, _, b, i => by
    simp only [wrERo]; split
    · rename_i h; obtain ⟨-, h1, h2, -, h3⟩ := h
      rw [show i - erOff q = 0 by simp at h2; omega] at h3; simp at h3
    · rfl
  | [some x], m, q, _, _, b, i => by
    simp only [wrERo, erecPutMem_arr, List.length_singleton]
    by_cases e : b = erTier q
    · subst e
      simp only [ite_true, true_and, Array.getElem?_setIfInBounds]
      by_cases hi : erOff q = i
      · subst hi
        by_cases hb : erOff q < (m.arr64 (erTier q)).size
        · simp [hb]
        · simp [hb]
      · rw [ite_eq_right hi, ite_eq_right (by omega)]
    · simp [e]
  | a :: y :: ws, m, q, h1, h2, b, i => by
    have hlen : (a :: y :: ws).length = ws.length + 2 := rfl
    rw [hlen] at h1 h2
    obtain ⟨ho, ht⟩ := erOff_succ (q := q) (by omega) (by omega)
    have hm : ∃ m', wrERo m q (a :: y :: ws) = wrERo m' (q + 1) (y :: ws) ∧
        ∀ b', (m'.arr64 b').size = (m.arr64 b').size ∧ ∀ j, j ≠ erOff q ∨ b' ≠ erTier q →
          (m'.arr64 b')[j]? = (m.arr64 b')[j]? ∧
        ((m'.arr64 (erTier q))[erOff q]? = if erOff q < (m.arr64 (erTier q)).size then
          (a.or ((m.arr64 (erTier q))[erOff q]?)) else none) := by
      cases a with
      | none =>
        refine ⟨m, rfl, fun b' => ⟨rfl, fun j _ => ⟨rfl, ?_⟩⟩⟩
        split
        · simp
        · rename_i hb; simp [hb]
      | some x =>
        refine ⟨erecPutMem m q x, rfl, fun b' => ⟨?_, fun j hj => ⟨?_, ?_⟩⟩⟩
        · rw [erecPutMem_arr]; split <;> simp
        · rw [erecPutMem_arr]; split
          · rename_i e; subst e
            rcases hj with hj | hj
            · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hj)]
            · exact absurd rfl hj
          · rfl
        · rw [erecPutMem_arr, ite_eq_left rfl]
          split
          · rename_i hb; simp [hb]
          · rename_i hb; simp [hb]
    obtain ⟨m', e, hm'⟩ := hm
    have ih := wrERo_get (y :: ws) m' (q + 1)
      (by simp only [List.length_cons, ho]; omega)
      (by simp only [List.length_cons]; rw [UInt64.toNat_add]; simp; omega) b i
    rw [e, ih, ho, ht]
    obtain ⟨hsz, hrest⟩ := hm' b
    simp only [List.length_cons, hsz]
    by_cases hi : b = erTier q ∧ erOff q = i
    · obtain ⟨rfl, rfl⟩ := hi
      have h0 := (hrest (erOff q + 1) (.inl (by omega))).2
      rw [ite_eq_right (by omega)]
      by_cases hb : erOff q < (m.arr64 (erTier q)).size
      · rw [h0, ite_eq_left hb]
        cases a <;> simp [hb]
      · rw [h0, ite_eq_right hb]
        simp only [hb, and_false, false_and, ite_false]
        exact (Array.getElem?_eq_none (by omega)).symm
    · have hne : i ≠ erOff q ∨ b ≠ erTier q := by
        by_cases e1 : b = erTier q
        · exact .inl (fun e2 => hi ⟨e1, e2.symm⟩)
        · exact .inr e1
      rw [(hrest i hne).1]
      by_cases hr : b = erTier q ∧ erOff q + 1 ≤ i ∧ i < erOff q + 1 + (ws.length + 1) ∧
          i < (m.arr64 b).size
      · have : i - erOff q = (i - (erOff q + 1)) + 1 := by omega
        simp only [hr, true_and, this, List.getElem?_cons_succ]
        obtain ⟨-, h1', h2', h3'⟩ := hr
        simp only [show erOff q ≤ i by omega, show i < erOff q + (ws.length + 2) by omega, true_and]
      · by_cases e1 : b = erTier q
        · subst e1
          have hne' : i ≠ erOff q := fun e2 => hi ⟨rfl, e2.symm⟩
          rw [ite_eq_right (fun h => hr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩), ite_eq_right
            (fun h => hr ⟨h.1, by omega, by omega, h.2.2.2.1⟩)]
        · simp [e1]

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
    simp only [erTopOf, erTop, erecTop1, e]
  -- the growth from `m`
  have hgrow : ErecGrow m (wrER m1 q ws) := by
    refine ⟨?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
    · simp only [erTop, hcw]; exact hg1.top
    · rw [hget, ite_eq_right, hm1 _ (by decide)]
      rintro ⟨e, h2, -⟩
      have : erTopOf m q = erTop m := by
        unfold erTier at e; unfold erTopOf; split at e
        · rename_i t; simp [t]
        · cases e
      omega
    · simp only [erecTop1, hcw]; exact hg1.top1
    · rw [hget, ite_eq_right, hm1 _ (by decide)]
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
  refine ⟨⟨CheckR.erGrow hS.check hfr hgrow, hW⟩,
    { iw := (by simp only [iwTop, h200]; exact Nat.le_refl _),
      er := hgrow.top, iwGet := (fun i _ => by rw [hI]), erGet := hgrow.get, er1 := hgrow.top1,
      er1Get := hgrow.get1 }, hoff, ?_, hq41, htier,
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
    rw [ite_eq_left ⟨rfl, by omega, by omega, hlt⟩, show erOff q + j - erOff q = j by omega] at hgj
    have htopw : erOff q + j < erTopOf (wrER m1 q ws) q := by
      rw [hT _ hcw, htop1]; have e3 := hk; omega
    unfold erecP
    rw [ite_eq_left (show q.toNat + j < 2 ^ 64 by omega), htj, hoj]
    unfold erTopOf at htopw
    unfold erTier at hgj
    by_cases t : q.toNat / 2 ^ 40 % 2 = 0
    · simp only [t, ite_true] at htopw hgj ⊢; rw [ite_eq_left htopw]; exact hgj
    · simp only [t, ite_false] at htopw hgj ⊢; rw [ite_eq_left htopw]; exact hgj

/-- **A record allocated in `EREC` and written field by field** (`erRec_stage` for `wrERo`):
`erec_alloc(ws.length)` then the `some` words of `ws` at the
returned address keeps the stage relation and grows the pools; the words read back through
`erecP`, the address in the flag's tier at its old top. -/
theorem erRecO_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) (hS : StageR vis fe m a)
    (ws : List (Option Word)) (hk : k.toNat = ws.length) :
    StageR vis fe (wrERo m1 q ws) a ∧ IWGrow m (wrERo m1 q ws) ∧ erOff q = erTopOf m q ∧
      erTopOf (wrERo m1 q ws) q = erTopOf m q + ws.length ∧ q.toNat < 2 ^ 41 ∧
      (q.toNat / 2 ^ 40 % 2 = 0 ↔ rdW (m.arr64 CTL) 1 = 0) ∧
      (∀ j x, ws[j]? = some (some x) → erecP (wrERo m1 q ws) (q.toNat + j) = some x) := by
  obtain ⟨hg1, hf1, hoff, htop1, hsz1, htier, hq41, hW1⟩ := erAllocW_spec h hS.iw
  have hfw := wrERo_frame ws m1 q
  have hcw := wrERo_ctl ws m1 q
  have hcap : (m.arr64 (erTier q)).size < 2 ^ 40 := by
    unfold erTier; split
    · exact hS.iw.erCap
    · exact hS.iw.er1Cap
  have hsz : ∀ b, (m1.arr64 b).size = (m.arr64 b).size := hf1.size
  have hm1 : ∀ b : TieredArray, b ≠ CTL → m1.arr64 b = m.arr64 b := fun b hb => hf1.arr b (by simp) hb
  have hget := wrERo_get ws m1 q (by omega) (by omega)
  have hT : ∀ m' : Mem, m'.arr64 CTL = m1.arr64 CTL → erTopOf m' q = erTopOf m1 q := fun m' e => by
    simp only [erTopOf, erTop, erecTop1, e]
  -- the growth from `m`
  have hgrow : ErecGrow m (wrERo m1 q ws) := by
    refine ⟨?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
    · simp only [erTop, hcw]; exact hg1.top
    · rw [hget, ite_eq_right, hm1 _ (by decide)]
      rintro ⟨e, h2, -⟩
      have : erTopOf m q = erTop m := by
        unfold erTier at e; unfold erTopOf; split at e
        · rename_i t; simp [t]
        · cases e
      omega
    · simp only [erecTop1, hcw]; exact hg1.top1
    · rw [hget, ite_eq_right, hm1 _ (by decide)]
      rintro ⟨e, h2, -⟩
      have : erTopOf m q = erecTop1 m := by
        unfold erTier at e; unfold erTopOf; split at e
        · cases e
        · rename_i t; simp [t]
      omega
  have hfr : MemFrame [EREC, tier1 EREC] [129, 130] m (wrERo m1 q ws) :=
    (hf1.mono (by simp) (by simp)).trans (hfw.mono (by simp) (by simp))
  have hW : IWOK (wrERo m1 q ws) := IWOK.of_er hfw hW1
  have hI : (wrERo m1 q ws).arr64 IW = m.arr64 IW := by
    rw [hfw.arr IW (by decide) (by decide), hm1 _ (by decide)]
  have h200 : rdW ((wrERo m1 q ws).arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hfr.ctl 200 (by simp)
  refine ⟨⟨CheckR.erGrow hS.check hfr hgrow, hW⟩,
    { iw := (by simp only [iwTop, h200]; exact Nat.le_refl _),
      er := hgrow.top, iwGet := (fun i _ => by rw [hI]), erGet := hgrow.get, er1 := hgrow.top1,
      er1Get := hgrow.get1 }, hoff, ?_, hq41, htier,
    fun j x hx => ?_⟩
  · rw [hT _ hcw, htop1, hk]
  · have hj : j < ws.length := (List.getElem?_eq_some_iff.mp hx).1
    have hjl : erOff q + j < 2 ^ 40 := by
      have e1 := hsz1; have e2 := htop1; have e3 := hk; have e4 := hcap; omega
    have hoj : (q.toNat + j) % 2 ^ 40 = erOff q + j := by unfold erOff at hjl ⊢; omega
    have htj : (q.toNat + j) / 2 ^ 40 % 2 = q.toNat / 2 ^ 40 % 2 := by
      have : (q.toNat + j) / 2 ^ 40 = q.toNat / 2 ^ 40 := by unfold erOff at hjl; omega
      rw [this]
    have hlt : erOff q + j < (m1.arr64 (erTier q)).size := by
      rw [hsz]; have e1 := hsz1; have e2 := htop1; have e3 := hk; omega
    have hgj := hget (erTier q) (erOff q + j)
    simp only [show erOff q + j - erOff q = j by omega, hx, Option.join_some, Option.isSome_some,
      and_true] at hgj
    rw [ite_eq_left (by refine ⟨?_, ?_, ?_⟩ <;> first | trivial | omega)] at hgj
    have htopw : erOff q + j < erTopOf (wrERo m1 q ws) q := by
      rw [hT _ hcw, htop1]; have e3 := hk; omega
    unfold erecP
    rw [ite_eq_left (show q.toNat + j < 2 ^ 64 by omega), htj, hoj]
    unfold erTopOf at htopw
    unfold erTier at hgj
    by_cases t : q.toNat / 2 ^ 40 % 2 = 0
    · simp only [t, ite_true] at htopw hgj ⊢; rw [ite_eq_left htopw]; exact hgj
    · simp only [t, ite_false] at htopw hgj ⊢; rw [ite_eq_left htopw]; exact hgj


/-- **Every word of a record written field by field can be read** (the words between the fields
are the region's old words): the record's region lies below the new top. -/
theorem erRecO_words {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) (hW : IWOK m)
    (ws : List (Option Word)) (hk : k.toNat = ws.length) :
    ∀ j < ws.length, ∃ w, erecP (wrERo m1 q ws) (q.toNat + j) = some w := by
  obtain ⟨-, hf1, hoff, htop1, hsz1, -, hq41, -⟩ := erAllocW_spec h hW
  have hcw := wrERo_ctl ws m1 q
  have hcap : (m.arr64 (erTier q)).size < 2 ^ 40 := by
    unfold erTier; split
    · exact hW.erCap
    · exact hW.er1Cap
  have hsz : ∀ b, (m1.arr64 b).size = (m.arr64 b).size := hf1.size
  have hget := wrERo_get ws m1 q (by omega) (by omega)
  have hT : ∀ m' : Mem, m'.arr64 CTL = m1.arr64 CTL → erTopOf m' q = erTopOf m1 q := fun m' e => by
    simp only [erTopOf, erTop, erecTop1, e]
  intro j hj
  have hjl : erOff q + j < 2 ^ 40 := by
    have e1 := hsz1; have e2 := htop1; have e3 := hk; have e4 := hcap; omega
  have hoj : (q.toNat + j) % 2 ^ 40 = erOff q + j := by unfold erOff at hjl ⊢; omega
  have htj : (q.toNat + j) / 2 ^ 40 % 2 = q.toNat / 2 ^ 40 % 2 := by
    have : (q.toNat + j) / 2 ^ 40 = q.toNat / 2 ^ 40 := by unfold erOff at hjl; omega
    rw [this]
  have hlt : erOff q + j < (m1.arr64 (erTier q)).size := by
    rw [hsz]; have e1 := hsz1; have e2 := htop1; have e3 := hk; omega
  obtain ⟨w, hgj⟩ : ∃ w, ((wrERo m1 q ws).arr64 (erTier q))[erOff q + j]? = some w := by
    rw [hget (erTier q) (erOff q + j)]
    split
    · rename_i hc
      obtain ⟨-, -, -, -, hs⟩ := hc
      exact Option.isSome_iff_exists.mp hs
    · exact ⟨_, Array.getElem?_eq_getElem hlt⟩
  have htopw : erOff q + j < erTopOf (wrERo m1 q ws) q := by
    rw [hT _ hcw, htop1]; have e3 := hk; omega
  refine ⟨w, ?_⟩
  unfold erecP
  rw [ite_eq_left (show q.toNat + j < 2 ^ 64 by omega), htj, hoj]
  unfold erTopOf at htopw
  unfold erTier at hgj
  by_cases t : q.toNat / 2 ^ 40 % 2 = 0
  · simp only [t, ite_true] at htopw hgj ⊢; rw [ite_eq_left htopw]; exact hgj
  · simp only [t, ite_false] at htopw hgj ⊢; rw [ite_eq_left htopw]; exact hgj

theorem mapM_congr_of {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..), mapM_congr_of f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-! ## `cv_new`: a fresh constant-value record -/

/-- The model of `cv_new(nm, lo, ll, ty)`. -/
l_model cvNew_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut) (hp : p.lookup "cv_new" = some cvNew)
  fns [hp ↦ cvNewW]
  specs [erecAlloc_specW p ha n, erecPut_specW p hpu n]
  grind [arena_grind]

/-- A run of `cv_new`: the allocation and the record's image (`CV.img`). -/
theorem cvNewW_some {m m' : Mem} {nm lo ll ty q : Word} (h : cvNewW m nm lo ll ty = some (q, m')) :
    ∃ m1, erAllocW m CV.size = some (q, m1) ∧ m' = wrERo m1 q (CV.img nm lo ll ty) := by
  rcases h1 : erAllocW m CV.size with _ | ⟨q1, m1⟩ <;> rw [cvNewW.arm1, h1] at h
  · cases h
  simp only [cvNewW.k_erec_alloc] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨m1, rfl, ?_⟩
  -- the image's entries in order (the layout's numbers: a whole-record writer)
  simp [wrERo, CV.img, recImg, rec_unfold, List.replicate, UInt64.add_assoc]

/-- **`cv_new` with the name and level parameters of the record at `cq`** keeps the stage
relation and decodes as `{cv with type := ty}`. -/
theorem cvNew_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq ty q : Word} {cv : IConstantVal}
    (h : cvNewW m (erRd m cq) (erRd m (cq + CV.lpsOff)) (erRd m (cq + CV.lpsLen)) ty = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCVp m cq.toNat = some cv) (hty : ty.toNat < 2 ^ 32) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ erOff q = erTopOf m q ∧
      erTopOf m' q = erTopOf m q + CV.size.toNat ∧
      q.toNat < 2 ^ 41 ∧ (q.toNat / 2 ^ 40 % 2 = 0 ↔ rdW (m.arr64 CTL) 1 = 0) ∧
      decCVp m' q.toNat = some { cv with type := decI ty } := by
  obtain ⟨m1, h1, rfl⟩ := cvNewW_some h
  obtain ⟨hS', hg, hq, htop, hq41, htier, hget⟩ := erRecO_stage h1 hS
    (CV.img (erRd m cq) (erRd m (cq + CV.lpsOff)) (erRd m (cq + CV.lpsLen)) ty) (CV.img_length ..).symm
  rw [CV.img_length] at htop
  refine ⟨hS', hg, hq, htop, hq41, htier, ?_⟩
  obtain ⟨e1, e2, hs, -, -, -⟩ := decCV_rd (erRdOK m) hcv
  have hw : CVRecW (erecP (wrERo m1 q (CV.img (erRd m cq) (erRd m (cq + CV.lpsOff))
      (erRd m (cq + CV.lpsLen)) ty))) q.toNat (erRd m cq) (erRd m (cq + CV.lpsOff))
      (erRd m (cq + CV.lpsLen)) ty :=
    ⟨hget _ _ (CV.img_name ..), hget _ _ (CV.img_lo ..), hget _ _ (CV.img_ll ..),
      hget _ _ (CV.img_ty ..)⟩
  have := decCV_of_words hw e2 hty (ArrExt.hslice? (IWGrow.ext hg) hs)
  unfold decCVp
  unfold erA; rw [this, ← e1]

/-! ## `erec_put` and the tagged read; `env_push` under the stage relation -/

/-- **A word of the old pool and a freshly allocated word are at different places.** -/
theorem erFresh {m m1 : Mem} {k q x : Word} (h : erAllocW m k = some (q, m1)) (hW : IWOK m)
    {v : Word} (hx : erecP m x.toNat = some v) {j : Nat} (hj : j < k.toNat) :
    erTier x ≠ erTier (q + UInt64.ofNat j) ∨ erOff x ≠ erOff (q + UInt64.ofNat j) := by
  obtain ⟨-, -, hoff, htop1, hsz1, -, hq41, -⟩ := erAllocW_spec h hW
  have hcap : (m.arr64 (erTier q)).size < 2 ^ 40 := by
    unfold erTier; split
    · exact hW.erCap
    · exact hW.er1Cap
  have hjN : j < 2 ^ 40 := by omega
  have hqj : (q + UInt64.ofNat j).toNat = q.toNat + j := by
    rw [UInt64.toNat_add]; simp; omega
  have hlt : erOff q + j < 2 ^ 40 := by omega
  have eo : erOff (q + UInt64.ofNat j) = erOff q + j := by unfold erOff at hlt ⊢; rw [hqj]; omega
  have et : (q + UInt64.ofNat j).toNat / 2 ^ 40 % 2 = q.toNat / 2 ^ 40 % 2 := by
    rw [hqj]; unfold erOff at hlt; congr 1; omega
  -- the old word lies below its tier's top
  have hxl : erOff x < erTopOf m x := by
    unfold erecP at hx; unfold erOff erTopOf
    split at hx
    · split at hx
      · rename_i t; split at hx
        · simp only [t, ite_true]; omega
        · cases hx
      · rename_i t; split at hx
        · simp only [t, ite_false]; omega
        · cases hx
    · cases hx
  by_cases e : x.toNat / 2 ^ 40 % 2 = q.toNat / 2 ^ 40 % 2
  · right
    have : erTopOf m x = erTopOf m q := by unfold erTopOf; rw [e]
    rw [eo]; omega
  · left
    unfold erTier; rw [et]
    intro h'
    split at h' <;> split at h' <;> first | omega | cases h'

/-- `env_row_set`'s two writes stay in the name's own row array. -/
theorem ownSet_frame (m : Mem) (w c q : Word) : MemFrame [ownArr w] [] m (ownSet m w c q) :=
  (MemFrame.set64 m _ (Ne.symm (ctl_ne_ownArr w)) _ _).trans
    (MemFrame.set64 _ _ (Ne.symm (ctl_ne_ownArr w)) _ _)

/-- **A write of an own row** relating the memory to `fe'` at `vis'` keeps the stage relation (at
`fe'`) and the pools. -/
theorem StageR.of_own {vis vis' : Word} {fe fe' : IFEnv} {a : AState} {m : Mem} {w c q : Word}
    (hS : StageR vis fe m a) (hE : EnvR (ownSet m w c q) vis' fe') :
    StageR vis' fe' (ownSet m w c q) a ∧ IWGrow m (ownSet m w c q) := by
  have hf := ownSet_frame m w c q
  have ha := ownArr_arr w
  have hA : ∀ b ∈ [ownArr w], 140 ≤ b.arr ∧ b.arr ≤ 142 := by
    intro b hb; simp only [List.mem_singleton] at hb; subst hb; omega
  have hlow : ∀ y ∈ arenaArrs, y.arr < 64 := by decide
  have hA3 : (IW : TieredArray) ∉ [ownArr w] ∧ (EREC : TieredArray) ∉ [ownArr w] ∧
      tier1 EREC ∉ [ownArr w] :=
    ⟨fun h => by have := hA _ h; revert this; decide, fun h => by have := hA _ h; revert this; decide,
      fun h => by have := hA _ h; revert this; decide⟩
  have hC3 : (129 : Word) ∉ ([] : List Word) ∧ (130 : Word) ∉ ([] : List Word) ∧
      (200 : Word) ∉ ([] : List Word) := by simp
  refine ⟨⟨⟨⟨ArenaR.frame (fun b hb hm => by have := hlow b hm; have := hA b hb; omega)
      (fun x hx => by simp at hx) hf hS.check.arena.base,
      DerR.frameM _ _ m _ hf (fun b hb => by have := hA b hb; omega) a hS.check.arena.der⟩,
    hS.check.core.frame (fun b hb => .inr (by have := hA b hb; omega)) (fun x hx => by simp at hx) hf,
    hS.check.pins.frame (fun b hb => .inr (by have := hA b hb; omega)) hf, hE,
    hS.check.mode.frame hf (by simp) (by simp)⟩, IWOK.of_keep hf hA3 hC3 hS.iw⟩,
    IWGrow.of_keep hf hA3 hC3⟩

end L.Ind

