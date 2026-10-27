import ConAgua.Arena.IndCopy2
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

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
    {r : Word} {A₀ : List ArrId} {C₀ : List Word}
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
theorem stage_of_ok {op : AM EIdx} {A : List ArrId} {C : List Word} (hS : StageR dn vis fe m a)
    (hok : AM.ok op a) (hD : ArenaD m' (AM.st op a)) (hres : AM.res op a = decE r)
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64)
    (hk : Keeps cp op) (h01 : (0 : Word) ∉ C ∧ (1 : Word) ∉ C := by decide) :
    ∃ a', op.run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  have hrun := AM.run_of_ok op a hok
  rw [hres] at hrun
  obtain ⟨h1, h2⟩ := StageR.of_walk hS hD hf hA hC (hk.run hrun) h01
  exact ⟨_, hrun, h1, h2⟩

theorem internBVar_stage (hS : StageR dn vis fe m a) (u : Word) (hI : binternW m u = some (r, m')) :
    ∃ a', (internE (.bvar u.toNat)).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hS.1.arena u r m' hI
  have hI₂ := hI
  exact stage_of_ok hS hok hD hres (consInternM_frame bvarCS_wf hI₂)
    (by simp [tier1, tierOff, ConsSch.wset, bvarCS, BREC, BSLOT]) (by simp [bvarCS]) (keeps_internE _)

theorem internFVar_stage (hS : StageR dn vis fe m a) (u ty : Word) (hty : ty.toNat < 2 ^ 32)
    (hI : fvinternW m u ty = some (r, m')) :
    ∃ a', (internE (.fvar u.toNat (decE ty))).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.1.arena u ty r hty m' hI
  exact stage_of_ok hS hok hD hres (fvinternW_frame m u ty _ _ hI)
    (by simp [tier1, tierOff, FVREC, FVSLOT, FVLP]) (by simp) (keeps_internE _)

theorem internSort_stage (hS : StageR dn vis fe m a) (u : Word) (hu : u.toNat < 2 ^ 32)
    (hI : sointernW m u = some (r, m')) :
    ∃ a', (internE (.sort (decI u))).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internSort_D m a hS.1.arena u r hu m' hI
  exact stage_of_ok hS hok hD hres (sointernW_frame m u _ _ hI)
    (by simp [tier1, tierOff, SOREC, SOSLOT, SOLP]) (by simp) (keeps_internE _)

theorem internConst_stage (hS : StageR dn vis fe m a) (f x : Word) (hf : f.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (hI : ceinternW m f x = some (r, m')) :
    ∃ a', (internE (.const (decI (k := .name) f) (decI (k := .levels) x))).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := internConst_D m a hS.1.arena f x r hf hx m' hI
  exact stage_of_ok hS hok hD hres (ceinternW_frame m f x _ _ hI)
    (by simp [tier1, tierOff, CREC, CSLOT, CLP]) (by simp) (keeps_internE _)

theorem mkApp_stage (hS : StageR dn vis fe m a) (f x : Word) (hI : mkAppW m f x = some (r, m')) :
    ∃ a', (internE (.app (decE f) (decE x))).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkApp_ok m a hS.1.arena f x r m' hI
  have hf : MemFrame [ADER, tier1 ADER, AREC, tier1 AREC, ASLOT, tier1 ASLOT] [4, 5] m m' := by
    unfold mkAppW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame appCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, tierOff, ADER, AREC, ASLOT]) (by simp) (keeps_internE _)

theorem mkLam_stage (hS : StageR dn vis fe m a) (t b : Word) (hI : mkLamW m t b = some (r, m')) :
    ∃ a', (internE (.lam (decE t) (decE b))).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkLam_ok m a hS.1.arena t b r m' hI
  have hf : MemFrame [LADER, tier1 LADER, LAREC, tier1 LAREC, LASLOT, tier1 LASLOT] [28, 29] m m' := by
    unfold mkLamW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame lamCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, tierOff, LADER, LAREC, LASLOT]) (by simp) (keeps_internE _)

theorem mkForall_stage (hS : StageR dn vis fe m a) (t b : Word) (hI : mkForallW m t b = some (r, m')) :
    ∃ a', (internE (.forallE (decE t) (decE b))).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkForall_ok m a hS.1.arena t b r m' hI
  have hf : MemFrame [FADER, tier1 FADER, FAREC, tier1 FAREC, FASLOT, tier1 FASLOT] [30, 31] m m' := by
    unfold mkForallW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame forallCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, tierOff, FADER, FAREC, FASLOT]) (by simp) (keeps_internE _)

theorem mkLet_stage (hS : StageR dn vis fe m a) (t v b : Word) (hI : mkLetW m t v b = some (r, m')) :
    ∃ a', (internE (.letE (decE t) (decE v) (decE b))).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkLet_ok m a hS.1.arena t v b r m' hI
  have hf : MemFrame [LEDER, tier1 LEDER, LEREC, tier1 LEREC, LESLOT, tier1 LESLOT] [20, 21] m m' := by
    unfold mkLetW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame letCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, tierOff, LEDER, LEREC, LESLOT]) (by simp) (keeps_internE _)

theorem mkProj_stage (hS : StageR dn vis fe m a) (n i e : Word) (hI : mkProjW m n i e = some (r, m')) :
    ∃ a', (internE (.proj (decI n) i.toNat (decE e))).run a = .ok (decE r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  obtain ⟨hok, hD, hres⟩ := mkProj_ok m a hS.1.arena n i e r m' hI
  have hf : MemFrame [PJDER, tier1 PJDER, PJREC, tier1 PJREC, PJSLOT, tier1 PJSLOT] [32, 33] m m' := by
    unfold mkProjW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      exact consInternM_frame projCS_wf hx) hI
  exact stage_of_ok hS hok hD hres hf (by simp [tier1, tierOff, PJDER, PJREC, PJSLOT]) (by simp) (keeps_internE _)

end

/-! ## The pool's `sl_cons` under the stage relation -/

/-- The pool's top after a `sl_cons` stays within the array. -/
theorem consW_room {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word}
    (h : consW n m x o l = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hx : x.toNat < 2 ^ 32) {k : IdxKind} {xs : List (Idx k)} (hxs : decHL m o.toNat l.toNat = some xs) :
    iwTop m' ≤ (m'.arr64 IW).size := by
  obtain ⟨-, -, -, hf, -, ht⟩ := consW_dec h hsz hc hsrc hx hxs
  rw [← ht, hf.2.2.1 IW]
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
theorem consW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {k : IdxKind} {xs : List (Idx k)}
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m) (hx : x.toNat < 2 ^ 32)
    (hxs : decHL m o.toNat l.toNat = some xs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (decI x :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  obtain ⟨hr, hd, hg, hf, -, ht⟩ := consW_dec h hsz hc hsrc hx hxs
  have hroom := consW_room h hsz hc hsrc hx hxs
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  subst hr
  refine ⟨⟨CheckR.frame_iw hf hS.1, hroom, ?_, ?_, ?_, ?_⟩, hg, by simpa using hd, by simpa using ht⟩
  · simp only [erTop, h129, hE]; exact hE1
  · rw [hf.2.2.1 IW]; exact hsz
  · rw [hE]; exact hEs
  · rw [hf.2.2.1 CTL]; exact hc

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
    {key : β} {tag : UInt32} {pf : Option LIdx} {d : LDer} {err : CheckError}
    {A : List ArrId} {C : List Word}
    (hS : StageR dn vis fe m a) (hrun : op.run a = protoRun L key tag pf d err a) (hok : AM.ok op a)
    (hR : ArenaR m' (AM.st op a)) (hres : AM.res op a = decI r) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 42 ∨ (54 < b ∧ b < 64) ∨ (256 ≤ b ∧ b < 298) ∨ (310 < b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64)
    (hset : ∀ t, (DerR m' a → DerR m' (L.setP a t)) ∧ cp (L.setP a t) = cp a)
    (hsetS : ∀ t, (DerR m' a → DerR m' (L.setS a t)) ∧ cp (L.setS a t) = cp a)
    (hmode : ModeOK m') :
    ∃ a', op.run a = .ok (decI r, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hf (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) a
    hS.1.arena.2
  have hcs := AM.st_proto L op key tag pf d err a hrun hok
  have hDk : DerR m' (AM.st op a) ∧ cp (AM.st op a) = cp a := by
    rcases hcs with h | ⟨t, h⟩ | ⟨t, h⟩ <;> rw [h]
    · exact ⟨hD₁, rfl⟩
    · exact ⟨(hset t).1 hD₁, (hset t).2⟩
    · exact ⟨(hsetS t).1 hD₁, (hsetS t).2⟩
  have hrun' := AM.run_of_ok op a hok
  rw [hres] at hrun'
  obtain ⟨h1, h2⟩ := StageR.of_walkM hS ⟨hR, hDk.1⟩ hf (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
    hC hDk.2 hmode
  exact ⟨_, hrun', h1, h2⟩

theorem internParam_stage (hS : StageR dn vis fe m a) (u : Word) (hu : u.toNat < 2 ^ 32)
    (hI : pinternW m u = some (r, m')) :
    ∃ a', (internLNode (.param (decI u))).run a = .ok (decI r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  have hR := hS.1.arena.1
  obtain ⟨hok, hX, hres⟩ := pintern_correct m a hR.param u hu _ _ hI
  have hL := pintern_hp m a hR.param u hu hR.paramHp _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame paramCS_wf hI₂
  exact stage_of_level hS (internLNode_param_run _ a) hok
    (hR.lift_param _ _ _ _ ⟨hX, hL⟩ hfr (AM.st_proto paramLens _ _ _ _ _ _ a (internLNode_param_run _ a) hok))
    hres hfr (by simp [tier1, tierOff, ConsSch.wset, paramCS, PREC, PSLOT]) (by simp [paramCS]) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩)
    (hS.1.mode.frame hfr (by decide) (by decide))

theorem internZero_stage (hS : StageR dn vis fe m a) (hI : zinternW m = some (r, m')) :
    ∃ a', (internLNode .zero).run a = .ok (decI r, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' := by
  have hR := hS.1.arena.1
  obtain ⟨hok, hX, hres⟩ := zintern_correct m a hR.zero _ _ hI
  have hL := zintern_hp m a hR.zero hR.zeroHp _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame zeroCS_wf hI₂
  exact stage_of_level hS (internLNode_zero_run a) hok
    (hR.lift_zero _ _ _ _ ⟨hX, hL⟩ hfr (AM.st_proto zeroLens _ _ _ _ _ _ a (internLNode_zero_run a) hok))
    hres hfr (by simp [tier1, tierOff, ConsSch.wset, zeroCS, ZREC, ZSLOT]) (by simp [zeroCS]) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩)
    (hS.1.mode.frame hfr (by decide) (by decide))

theorem internMax_stage (hS : StageR dn vis fe m a) (u v : Word) (hu : u.toNat < 2 ^ 32)
    (hv : v.toNat < 2 ^ 32) (hI : minternW m u v = some (r, m')) :
    ∃ a', (internLNode (.max (decI u) (decI v))).run a = .ok (decI r, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  have hR := hS.1.arena.1
  obtain ⟨hok, hX, hres⟩ := mintern_correct m a hR.max u v hu hv _ _ hI
  have hfr := minternW_frame m u v _ _ hI
  exact stage_of_level hS (internLNode_max_run _ _ a) hok
    (hR.lift_max _ _ _ _ ⟨hX, mintern_hp m a hR.max u v hu hv hR.maxHp (lvlHPW_or m a hR u v hu hv) _ _ hI⟩
      hfr (AM.st_proto maxLens _ _ _ _ _ _ a (internLNode_max_run _ _ a) hok))
    hres hfr (by simp [tier1, tierOff, MREC, MSLOT, MHP]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩)
    (hS.1.mode.frame hfr (by decide) (by decide))

end levels

/-! ## `iw_alloc` under the stage relation -/

theorem allocW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {k q : Word} (h : allocW m k = some (q, m1)) (hS : StageR dn vis fe m a) :
    StageR dn vis fe m1 a ∧ IWGrow m m1 ∧ q.toNat = iwTop m ∧ iwTop m1 = iwTop m + k.toNat := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  obtain ⟨rfl, rfl, hroom⟩ := allocW_facts h hsz
  have hf := allocMem_frame m k
  have htop : iwTop (allocMem m k) = iwTop m + k.toNat := by
    simp only [iwTop, allocMem, rdW_set64]
    have h200 : UInt64.toNat 200 < (m.arr64 CTL).size := by simpa using hc
    rw [ite_eq_left ⟨trivial, trivial, h200⟩, UInt64.toNat_add]
    omega
  have h129 : rdW ((allocMem m k).arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : (allocMem m k).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  refine ⟨⟨CheckR.frame_iw hf hS.1, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl, htop⟩
  · rw [htop, hf.2.2.1 IW]; simp only [iwTop]; omega
  · simp only [erTop, h129, hE]; exact hE1
  · rw [hf.2.2.1 IW]; exact hsz
  · rw [hE]; exact hEs
  · rw [hf.2.2.1 CTL]; exact hc
  · exact allocMem_grow m k (by simp only [iwTop]; omega) hc

/-! ## `erec_alloc` and the constant records, under the stage relation -/

/-- The memory after `erec_alloc(k)`. -/
def erAllocMem (m : Mem) (k : Word) : Mem := m.set64 CTL 129 (rdW (m.arr64 CTL) 129 + k)

/-- The model of `erec_alloc(k)`. -/
def erAllocW (m : Mem) (k : Word) : Option (Word × Mem) :=
  let o := rdW (m.arr64 CTL) 129
  if m.len64 EREC < o then none
  else if m.len64 EREC - o < k then none
  else some (o, erAllocMem m k)

theorem erecAlloc_specW (p : Prog) (hp : p.lookup "erec_alloc" = some erecAlloc) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_alloc" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ erAllocW s₀.mem k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erecAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [erAllocW, erAllocMem]

/-- Write `ws` into `EREC` at `q, q + 1, …`. -/
def wrER (m : Mem) (q : Word) : List Word → Mem
  | [] => m
  | x :: xs => wrER (m.set64 EREC q x) (q + 1) xs

theorem wrER_frame : ∀ (ws : List Word) (m : Mem) (q : Word), MemFrame [EREC] [] m (wrER m q ws)
  | [], m, q => MemFrame.refl _ _ _
  | x :: ws, m, q =>
    (MemFrame.mono (MemFrame.set64 m EREC (by decide) q x) (by simp) (by simp)).trans
      (wrER_frame ws _ _)

theorem wrER_get : ∀ (ws : List Word) (m : Mem) (q : Word) (i : Nat),
    q.toNat + ws.length ≤ (m.arr64 EREC).size → (m.arr64 EREC).size < 2 ^ 64 →
    ((wrER m q ws).arr64 EREC)[i]? =
      if q.toNat ≤ i ∧ i < q.toNat + ws.length then ws[i - q.toNat]? else (m.arr64 EREC)[i]?
  | [], m, q, i, _, _ => by simp [wrER]; intro h1 h2; omega
  | x :: ws, m, q, i, h, hsz => by
    simp only [wrER, List.length_cons] at h ⊢
    have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hqlt : q.toNat < (m.arr64 EREC).size := by omega
    have hsz1 : ((m.set64 EREC q x).arr64 EREC).size = (m.arr64 EREC).size := size_set64 _ _ _ _ _
    rw [wrER_get ws _ _ i (by rw [hq1, hsz1]; omega) (by rw [hsz1]; exact hsz), hq1]
    have hg : (m.set64 EREC q x).arr64 EREC = (m.arr64 EREC).set! q.toNat x :=
      Mem.arr64_set64_same _ _ _ _
    by_cases h1 : q.toNat + 1 ≤ i ∧ i < q.toNat + 1 + ws.length
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
      have : i - q.toNat = (i - (q.toNat + 1)) + 1 := by omega
      rw [this]; simp
    · rw [ite_eq_right h1]
      by_cases hiq : i = q.toNat
      · subst hiq
        rw [ite_eq_left (by omega), hg, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp [hqlt]
      · rw [ite_eq_right (by omega), hg, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp [Ne.symm hiq]

/-- **A writer of `EREC` above its top and of `CTL[129]` keeps the stage relation** (lane
`decls`' `EnvR.grow`), given the records below the old top unchanged and the new top in range. -/
theorem StageR.erec {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} (hS : StageR dn vis fe m a) (hf : MemFrame [EREC] [129] m m')
    (hlow : ∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?)
    (htop : erTop m ≤ erTop m') (hroom : erTop m' ≤ (m'.arr64 EREC).size) :
    StageR dn vis fe m' a ∧ IWGrow m m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW (by simp [EREC, IW]) (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 200 (by simp)
  have hg : ErecGrow m m' := ⟨htop, hlow, hf.2.2.1 EREC⟩
  have hC : CheckR dn m' a vis fe :=
    ⟨⟨ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, EREC])
        (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hS.1.arena.1,
      DerR.frameM _ _ m m' hf (by decide) a hS.1.arena.2⟩,
     hS.1.core.frame (fun b hb => by simp at hb; subst hb; decide)
       (fun x hx => by simp at hx; subst hx; decide) hf,
     hS.1.pins.frame (fun b hb => by simp at hb; subst hb; decide) hf,
     EnvR.grow (fun b h1 h2 h3 => hf.1 b (fun hm => by simp at hm; subst hm; simp [EREC] at h3)
         (fun hm => by subst hm; simp [CTL] at h1))
       (hf.2.1 128 (by simp)) hg
       (TblSame.of_frame (fun b hb => by simp at hb; subst hb; decide)
         (fun b hb => by simp at hb; subst hb; decide) (by decide) (by decide) hf) hS.1.env,
     hS.1.mode.frame hf (by simp) (by simp)⟩
  refine ⟨⟨hC, ?_, hroom, ?_, ?_, ?_⟩, ?_⟩
  · simp only [iwTop, h200, hI]; exact hI1
  · rw [hI]; exact hsz
  · rw [hf.2.2.1 EREC]; exact hEs
  · rw [hf.2.2.1 CTL]; exact hc
  · refine ⟨by simp only [iwTop, h200]; exact Nat.le_refl _, htop, fun i _ => by rw [hI], hlow⟩

/-- **A record allocated in `EREC` and written**: `erec_alloc(ws.length)` then `ws` at the
returned pointer keeps the stage relation; the words are readable there, the top moved by the
record's length. -/
theorem erRec_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {k q : Word} (h : erAllocW m k = some (q, m1)) (hS : StageR dn vis fe m a)
    (ws : List Word) (hk : k.toNat = ws.length) :
    StageR dn vis fe (wrER m1 q ws) a ∧ IWGrow m (wrER m1 q ws) ∧ q.toNat = erTop m ∧
      erTop (wrER m1 q ws) = erTop m + ws.length ∧
      (∀ j < ws.length, ((wrER m1 q ws).arr64 EREC)[q.toNat + j]? = ws[j]?) := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  simp only [erAllocW] at h
  by_cases h1 : m.len64 EREC < rdW (m.arr64 CTL) 129
  · simp [h1] at h
  by_cases h2 : m.len64 EREC - rdW (m.arr64 CTL) 129 < k
  · simp [h1, h2] at h
  simp only [h1, h2, ite_false, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hlen : (m.len64 EREC).toNat = (m.arr64 EREC).size := by simp [Mem.len64]; omega
  have hq : (rdW (m.arr64 CTL) 129).toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC).toNat < (rdW (m.arr64 CTL) 129).toNat := h1
    omega
  have hroom : (rdW (m.arr64 CTL) 129).toNat + k.toNat ≤ (m.arr64 EREC).size := by
    have : ¬ (m.len64 EREC - rdW (m.arr64 CTL) 129).toNat < k.toNat := h2
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)] at this
    omega
  have hE : (erAllocMem m k).arr64 EREC = m.arr64 EREC := by
    simp only [erAllocMem]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hf : MemFrame [EREC] [129] m (wrER (erAllocMem m k) (rdW (m.arr64 CTL) 129) ws) :=
    (MemFrame.mono (MemFrame.setCtl m 129 _) (by simp) (by simp)).trans
      ((wrER_frame _ _ _).mono (by simp) (by simp))
  have h129 : (129 : Word).toNat < (m.arr64 CTL).size := by simp; omega
  have htop : erTop (wrER (erAllocMem m k) (rdW (m.arr64 CTL) 129) ws) = erTop m + ws.length := by
    simp only [erTop]
    rw [(wrER_frame ws (erAllocMem m k) (rdW (m.arr64 CTL) 129)).2.1 129 (by simp)]
    simp only [erAllocMem, rdW_set64]
    rw [ite_eq_left ⟨trivial, trivial, h129⟩, UInt64.toNat_add]
    omega
  have hget := fun i => wrER_get ws (erAllocMem m k) (rdW (m.arr64 CTL) 129) i
    (by rw [hE]; omega) (by rw [hE]; exact hEs)
  have hsize : ((wrER (erAllocMem m k) (rdW (m.arr64 CTL) 129) ws).arr64 EREC).size =
      (m.arr64 EREC).size := hf.2.2.1 EREC
  obtain ⟨hS', hg'⟩ := StageR.erec hS hf
    (fun i hi => by rw [hget, ite_eq_right (by simp only [erTop] at hi; omega), hE])
    (by rw [htop]; omega) (by rw [htop, hsize]; simp only [erTop]; omega)
  refine ⟨hS', hg', rfl, htop, fun j hj => ?_⟩
  rw [hget, ite_eq_left (by omega)]
  congr 1; omega

theorem mapM_congr_of {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..), mapM_congr_of f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- **A copied constant value with a new type** decodes as `{cv with type := ty}`: the name and
the level-parameter slice words copied from `cv`'s record, the slice itself unchanged. -/
theorem decCV_copy {a a' : Array Word} {cq q : Nat} {cv : IConstantVal} {ty : Word} (N : Nat)
    (h : decCV a cq = some cv) (h0 : a'[q]? = a[cq]?) (h1 : a'[q + 1]? = a[cq + 1]?)
    (h2 : a'[q + 2]? = a[cq + 2]?) (h3 : a'[q + 3]? = some ty) (hty : ty.toNat < 2 ^ 32)
    (hlow : ∀ i < N, a'[i]? = a[i]?)
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
  (((m1.set64 EREC q nm).set64 EREC (q + 1) lo).set64 EREC (q + 2) ll).set64 EREC (q + 3) ty

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
    (hp : p.lookup "cv_new" = some cvNew) (n : Nat) (s₀ : St) (nm lo ll ty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_new" [nm, lo, ll, ty]
    ⦃fun r s' => LocEq s' s₀ ∧ cvNewW s₀.mem nm lo ll ty = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, cvNew]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        erecAlloc_specW p ha n] <;>
      finish [cvNewW, cvNewMem]

/-- **`cv_new` with the name and level parameters of the record at `cq`** keeps the stage
relation and decodes as `{cv with type := ty}`. -/
theorem cvNew_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq ty q : Word} {cv : IConstantVal}
    (h : cvNewW m (rdW (m.arr64 EREC) cq) (rdW (m.arr64 EREC) (cq + 1)) (rdW (m.arr64 EREC) (cq + 2)) ty
      = some (q, m'))
    (hS : StageR dn vis fe m a) (hcv : decCVp m cq.toNat = some cv) (hcq : cq.toNat + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cq.toNat + 1) = some lo → nat? (erA m) (cq.toNat + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0)
    (hty : ty.toNat < 2 ^ 32) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ q.toNat = erTop m ∧ erTop m' = erTop m + 4 ∧
      (∀ lo ll, nat? (erA m') (q.toNat + 1) = some lo → nat? (erA m') (q.toNat + 2) = some ll →
        lo + ll ≤ erTop m ∨ ll = 0) ∧
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
  obtain ⟨hS', hg, hq, htop, hget⟩ := erRec_stage h1 hS [rdW (m.arr64 EREC) cq,
    rdW (m.arr64 EREC) (cq + 1), rdW (m.arr64 EREC) (cq + 2), ty] (by simp)
  refine ⟨hS', hg, hq, htop, ?_, ?_⟩
  rotate_left
  obtain ⟨-, hE1, -, hEs, -⟩ := hS.2
  have hlt : ∀ j, j < 4 → cq.toNat + j < (m.arr64 EREC).size := fun j hj => by
    simp only [erTop] at hcq hE1; omega
  have hw : ∀ (j : Nat) (x : Word), j < 3 → x.toNat = cq.toNat + j →
      (m.arr64 EREC)[cq.toNat + j]? = some (rdW (m.arr64 EREC) x) := by
    intro j x hj hx
    simp only [rdW, hx, Array.getElem?_eq_getElem (hlt j (by omega))]; rfl
  have hc1 : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hc2 : (cq + 2).toNat = cq.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have hlow : ∀ i < erTop m, ((wrER m1 q1 [rdW (m.arr64 EREC) cq,
      rdW (m.arr64 EREC) (cq + 1), rdW (m.arr64 EREC) (cq + 2), ty]).arr64 EREC)[i]? =
      (m.arr64 EREC)[i]? := fun i hi => hg.2.2.2 i hi
  refine decCV_copy (erTop m) hcv ?_ ?_ ?_ ?_ hty hlow hsl
  · have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp only [erA]; rw [this]; have := hw 0 cq (by decide) (by simp); simp only [Nat.add_zero] at this
    rw [this]; simp
  · simp only [erA]; rw [hget 1 (by simp), hw 1 (cq + 1) (by decide) hc1]; simp
  · simp only [erA]; rw [hget 2 (by simp), hw 2 (cq + 2) (by decide) hc2]; simp
  · simp only [erA]; rw [hget 3 (by simp)]; simp
  · intro lo ll e1 e2
    obtain ⟨-, hE1, -, hEs, -⟩ := hS.2
    have hlt : ∀ j, j < 4 → cq.toNat + j < (m.arr64 EREC).size := fun j hj => by
      simp only [erTop] at hcq hE1; omega
    simp only [nat?, erA] at e1 e2
    rw [hget 1 (by simp)] at e1
    rw [hget 2 (by simp)] at e2
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at e1 e2
    apply hsl
    · simp only [nat?, erA]
      have : (cq + 1).toNat = cq.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e1]; simp only [rdW, this, Array.getElem?_eq_getElem (hlt 1 (by decide)), Option.map_some,
        Option.getD_some]
    · simp only [nat?, erA]
      have : (cq + 2).toNat = cq.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
      rw [← e2]; simp only [rdW, this, Array.getElem?_eq_getElem (hlt 2 (by decide)), Option.map_some,
        Option.getD_some]

end L.Ind
