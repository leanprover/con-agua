import ConAgua.Arena.InferLeaves

/-!
# Interning under `CoreS`: the leaves the inference bodies build (lane `defeq`)

`mk_forall` under `CoreS` is `InferLeaves.lean`'s `mkForall_core`; here the others the bodies
call: the expression leaves `intern_fvar`, `intern_sort` (`CoreS.arena_frame`: the twin's state
keeps the caches, pins and level store), and the level nodes `intern_succ`, `intern_imax`, which
grow the twin's level store. Across a level node `CoreS` holds by `CoreS.of_level`: the expression
tables, caches and pins are kept (`LvlStep`), and the readback caches stay readbacks because the
level store only extends (`LStore.intern_ext`, `denoteLList_mono_of_lext`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## A memory read as a value

`vcgen`'s own unfolding of `ld64` leaves the read as `a[i.toNat]'h` with the bound hypothesis `h`
as a proof argument, which `simp_all` cannot rewrite under; this spec answers `rdW` instead. -/

theorem ld64_rdW_spec (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld64 a i ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, by simp [rdW, h]⟩
  · simp [throw, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift] at hrun
    cases hrun

/-! ## A level-node interning step -/

/-- **What a level-node interning keeps**: everything but the level store, which it extends. -/
structure LvlStep (a a' : AState) : Prop where
  caches : a'.caches = a.caches
  pins : a'.pins = a.pins
  pers : a'.store.pers = a.store.pers
  scr : a'.store.scr = a.store.scr
  lsp : a'.store.lss.pers = a.store.lss.pers
  lss : a'.store.lss.scr = a.store.lss.scr
  lon : a'.store.lss.scratchOn = a.store.lss.scratchOn
  ns : a'.store.lss.ls.ns = a.store.lss.ls.ns
  ext : LExt a.store.lss.ls a'.store.lss.ls

theorem LvlStep.refl (a : AState) : LvlStep a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, LExt.refl _⟩

theorem internLNode_step (v : LNodeView) (a a' : AState) (h : LIdx)
    (hrun : (internLNode v).run a = .ok (h, a')) : LvlStep a a' := by
  unfold internLNode at hrun
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrun
  repeat' split at hrun
  all_goals simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
    StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure] at hrun
  all_goals first
    | (obtain ⟨-, rfl⟩ := hrun; exact LvlStep.refl _)
    | (obtain ⟨-, rfl⟩ := hrun
       exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, LStore.ns_intern _ _, LStore.intern_ext _ _⟩)

/-- `DerR` reads only the expression tiers. -/
theorem DerR.of_tiers (m : Mem) (a a' : AState) (hD : DerR m a) (hp : a'.store.pers = a.store.pers)
    (hs : a'.store.scr = a.store.scr) : DerR m a' := by
  have e : ∀ {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64)
      (P : Word → Nat → α → UInt64 → Prop), DerT2 a g P → DerT2 a' g P := by
    intro α _ _ g P h; unfold DerT2 at *; rw [hp, hs]; exact h
  exact ⟨e _ _ hD.bvar, e _ _ hD.fvar, e _ _ hD.sort, e _ _ hD.const, e _ _ hD.lit, e _ _ hD.app,
    e _ _ hD.lam, e _ _ hD.forallE, e _ _ hD.letE, e _ _ hD.proj⟩

/-- **`CoreS` across a level-node interning** whose memory writes are confined to the level
store's arrays (below 42) and counts (`CTL` below 64). -/
theorem CoreS.of_level {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hL : LvlStep a a') (hR : ArenaR m' a')
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42) (hC : ∀ x ∈ C, x.toNat < 64) :
    CoreS dn m' a' vis fe M eb ∧ StackKept m m' := by
  have hD : DerR m' a' := DerR.of_tiers m' a a'
    (DerR.frameM A C m m' hf (fun b hb => .inl (hA b hb)) a hS.arena.2) hL.pers hL.scr
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 :=
    hf.2.1 136 (fun h => by have := hC _ h; simp at this)
  refine ⟨⟨⟨hR, hD⟩, ?_, ?_, hS.env.frame (fun b hb => .inl (by have := hA b hb; simp only [ArrId] at this ⊢; omega))
      (fun x hx => .inl (by have := hC x hx; omega)) hf, ?_, ?_, ?_,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn⟩,
    by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩
  · rw [hL.caches]
    exact CoreRM.frame (A := A) (C := C) (fun b hb => .inl (by have := hA b hb; simp only [ArrId] at this ⊢; omega))
      (fun x hx => .inl (by have := hC x hx; omega)) hf hS.core
  · rw [hL.pins]
    exact hS.pins.congr (hf.1 PINS (fun h => by have := hA _ h; simp only [PINS, ArrId] at this; omega)
      (by decide))
  · intro h l e
    rw [hL.caches] at e
    exact hL.ext.lvl h l (hS.readL h l e)
  · intro h l e
    rw [hL.caches] at e
    have h1 := hS.readLs h l e
    unfold denoteLs at h1 ⊢
    have hv : a'.store.lss.view h = a.store.lss.view h := by
      simp only [LsStore.view, hL.lsp, hL.lss, hL.lon]
    rw [hv]
    cases hw : a.store.lss.view h with
    | none => rw [hw] at h1; cases h1
    | some us => rw [hw] at h1; exact denoteLList_mono_of_lext hL.ext us l h1
  · rw [hL.ns]; exact hS.nwf

/-! ## The leaves -/

theorem keeps_cpl_internFVar (i : Nat) (ty : EIdx) : Keeps cpl (internE (.fvar i ty)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

theorem keeps_cpl_internSort (u : LIdx) : Keeps cpl (internE (.sort u)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

/-- A frame of arrays other than the stack and `CTL` words other than its top keeps the stack. -/
theorem StackKept.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : SPN ∉ A) (hC : (136 : Word) ∉ C) : StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN hA (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 hC
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

section leaves
variable {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
  {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-- **`intern_fvar` refines `internE (.fvar …)` under `CoreS`.** -/
theorem internFVar_core (hS : CoreS dn m a vis fe M eb) (u ty : Word) (hty : HW ty)
    (rs : List Word) (hI : fvinternW m u ty = some (rs.headD 0, m')) :
    CoreRef (internE (.fvar u.toNat (decE ty))) a decH dn m vis fe M eb rs m' := by
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.arena u ty _ hty m' hI
  have hI₂ := hI; rw [fvinternW_eq] at hI₂
  have hf := internM_frame _ fvarSch_wf _ _ _ _ _ _ _ _ hI₂
  have hw := internM_hw fvarSch FVRecRel fvhash fvarSch_wf m _ _ _ hS.arena.1.fvar (fvMt m u ty) _ _ _ _
    (probe_homeG fvarSch m 0 _ _ (fvprobeW_arm m u ty 0) _)
    (probe_homeG fvarSch m 1 _ _ (fvprobeW_arm m u ty 1) _) _ (fvpushOK_room m) _ _ _ m' hI₂
  have hS' := hS.arena_frame hD (Keeps.run (keeps_cpl_internFVar _ _)
      (AM.run_of_ok _ _ hok)) hf
    (fun b hb => by simp only [fvarSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (by simp [fvarSch, FVREC, FVSLOT])
    (fun b hb => by simp only [fvarSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (fun x hx => by simp only [fvarSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (fun x hx => by simp only [fvarSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
  have hst := StackKept.of_frame hf (by simp [fvarSch, FVREC, FVSLOT, SPN]) (by simp [fvarSch])
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- **`intern_sort` refines `internE (.sort …)` under `CoreS`.** -/
theorem internSort_core (hS : CoreS dn m a vis fe M eb) (u : Word) (hu : HW u)
    (rs : List Word) (hI : sointernW m u = some (rs.headD 0, m')) :
    CoreRef (internE (.sort (decI u))) a decH dn m vis fe M eb rs m' := by
  obtain ⟨hok, hD, hres⟩ := internSort_D m a hS.arena u _ hu m' hI
  have hI₂ := hI; rw [sointernW_eq] at hI₂
  have hf := internM_frame _ sortSch_wf _ _ _ _ _ _ _ _ hI₂
  have hw := internM_hw sortSch SoRecRel sohash sortSch_wf m _ _ _ hS.arena.1.sort (soMt m u) _ _ _ _
    (probe_homeG sortSch m 0 _ _ (soprobeW_arm m u 0) _)
    (probe_homeG sortSch m 1 _ _ (soprobeW_arm m u 1) _) _ (sopushOK_room m) _ _ _ m' hI₂
  have hS' := hS.arena_frame hD (Keeps.run (keeps_cpl_internSort _) (AM.run_of_ok _ _ hok)) hf
    (fun b hb => by simp only [sortSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (by simp [sortSch, SOREC, SOSLOT])
    (fun b hb => by simp only [sortSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (fun x hx => by simp only [sortSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (fun x hx => by simp only [sortSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
  have hst := StackKept.of_frame hf (by simp [sortSch, SOREC, SOSLOT, SPN]) (by simp [sortSch])
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- **`intern_succ` refines `internLNode (.succ …)` under `CoreS`.** -/
theorem internSucc_core (hS : CoreS dn m a vis fe M eb) (u : Word) (hu : HW u)
    (rs : List Word) (hI : sinternW m u = some (rs.headD 0, m')) :
    CoreRef (internLNode (.succ (decI u))) a decLv dn m vis fe M eb rs m' := by
  obtain ⟨hok, hX, hres⟩ := sintern_correct m a hS.arena.1.succ u hu _ _ hI
  have hI₂ := hI; rw [sinternW_eq] at hI₂
  have hf := internM_frame _ succSch_wf _ _ _ _ _ _ _ _ hI₂
  have hR' := hS.arena.1.lift_succ _ _ _ _ hX hf
    (AM.st_proto succLens _ _ _ _ _ _ a (internLNode_succ_run _ a) hok)
  have hL := internLNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hS.of_level hL hR' hf
    (fun b hb => by simp only [succSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (fun x hx => by simp only [succSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
  have hw := internM_hw succSch SRecRel shash succSch_wf m _ _ _ hS.arena.1.succ (sMt m u) _ _ _ _
    (probe_homeG succSch m 0 _ _ (sprobeW_arm m u 0) _)
    (probe_homeG succSch m 1 _ _ (sprobeW_arm m u 1) _) _ (spushOK_room m) _ _ _ m' hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- **`intern_imax` refines `internLNode (.imax …)` under `CoreS`.** -/
theorem internImax_core (hS : CoreS dn m a vis fe M eb) (u v : Word) (hu : HW u) (hv : HW v)
    (rs : List Word) (hI : iminternW m u v = some (rs.headD 0, m')) :
    CoreRef (internLNode (.imax (decI u) (decI v))) a decLv dn m vis fe M eb rs m' := by
  obtain ⟨hok, hX, hres⟩ := imintern_correct m a hS.arena.1.imax u v hu hv _ _ hI
  have hI₂ := hI; rw [iiminternW_eq] at hI₂
  have hf := internM_frame _ iimaxSch_wf _ _ _ _ _ _ _ _ hI₂
  have hR' := hS.arena.1.lift_imax _ _ _ _ hX hf
    (AM.st_proto imaxLens _ _ _ _ _ _ a (internLNode_imax_run _ _ a) hok)
  have hL := internLNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hS.of_level hL hR' hf
    (fun b hb => by simp only [imaxSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (fun x hx => by simp only [imaxSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
  have hw := internM_hw imaxSch IRecRel imhash iimaxSch_wf m _ _ _ hS.arena.1.imax (imMt m u v) _ _ _ _
    (probe_homeG imaxSch m 0 _ _ (iimprobeW_arm m u v 0) _)
    (probe_homeG imaxSch m 1 _ _ (iimprobeW_arm m u v 1) _) _ (iimpushOK_room m) _ _ _ m' hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

end leaves

end L.Arena
