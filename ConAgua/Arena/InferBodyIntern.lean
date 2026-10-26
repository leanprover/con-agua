import ConAgua.Arena.InferLeaves
import ConAgua.Arena.StoreDenLvl
import ConAgua.Arena.LevelView
import ConAgua.Arena.LvlGrow

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
    ⦃fun s => s = s₀⦄ ld64 a i
    ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i ∧ i.toNat < (s₀.mem.arr64 a).size; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  subst hs
  simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i h
    simp only [pure] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, by simp [rdW, h], h⟩
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
  son : a'.store.scratchOn = a.store.scratchOn

theorem LvlStep.refl (a : AState) : LvlStep a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, LExt.refl _, rfl⟩

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
       exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, LStore.ns_intern _ _, LStore.intern_ext _ _, rfl⟩)

/-- `DerR` reads only the expression tiers. -/
theorem DerR.of_tiers (m : Mem) (a a' : AState) (hD : DerR m a) (hp : a'.store.pers = a.store.pers)
    (hs : a'.store.scr = a.store.scr) : DerR m a' := by
  have e : ∀ {α : Type} [BEq α] [Hashable α] (g : ETables → Tbl α EIdx UInt64)
      (P : Word → Nat → α → UInt64 → Prop), DerT2 a g P → DerT2 a' g P := by
    intro α _ _ g P h; unfold DerT2 at *; rw [hp, hs]; exact h
  exact ⟨e _ _ hD.bvar, e _ _ hD.fvar, e _ _ hD.sort, e _ _ hD.const, e _ _ hD.lit, e _ _ hD.app,
    e _ _ hD.lam, e _ _ hD.forallE, e _ _ hD.letE, e _ _ hD.proj⟩

/-- **`CoreS` across a level-node interning** whose memory writes are confined to the level
store's arrays (below 42) and counts (`CTL` below 42). -/
theorem CoreS.of_level {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hL : LvlStep a a') (hR : ArenaR m' a')
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42 ∨ (54 < b ∧ b < 64) ∨ (256 ≤ b ∧ b < 298) ∨ (310 < b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 42)
    (hlv : LvlAll a') (hlc : LvlCnt m m') (hP : POOL ∉ A := by decide)
    (hP0 : (0 : Word) ∉ C := by decide) (hP1 : POOL1 ∉ A := by decide) (hPT : PT0 ∉ A := by decide) :
    CoreS dn m' a' vis fe M eb ∧ StackKept m m' := by
  have hmode : ModeOK m' := by
    have hfl : m'.flag = m.flag := hlc.flag
    unfold ModeOK; rw [hf.top_eq hP0, hfl]; exact hS.mode
  have hD : DerR m' a' := DerR.of_tiers m' a a'
    (DerR.frameM A C m m' hf (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) a hS.arena.2) hL.pers hL.scr
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 :=
    hf.2.1 136 (fun h => by have := hC _ h; simp at this)
  refine ⟨⟨⟨hR, hD⟩, ?_, ?_, hS.env.frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
      (fun x hx => .inl (by have := hC x hx; omega)) hf
      (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega), ?_, ?_, ?_,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
      hS.memos.frame hf ⟨fun h => absurd (hA _ h) (by simp), fun h => absurd (hA _ h) (by simp)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide)⟩
        ⟨fun h => absurd (hA _ h) (by simp), fun h => absurd (hA _ h) (by simp),
          fun h => absurd (hA _ h) (by simp)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide),
          fun h => absurd (hC _ h) (by decide)⟩
        ⟨fun h => absurd (hA _ h) (by simp), fun h => absurd (hA _ h) (by simp),
          fun h => absurd (hA _ h) (by simp)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide),
          fun h => absurd (hC _ h) (by decide)⟩,
      hf.2.2.1 145 ▸ hS.bstk,
      hS.den.mono (lsExt_of_tables hL.lsp hL.lss hL.lon hL.ext) (by rw [hL.pins])
        (by rw [hL.pins]) (fun _ _ hk => .inl (hL.caches ▸ hk))
        (fun x u hv => by simpa only [EStore.view, hL.pers, hL.scr, hL.son] using hv)
        (fun x c us hv => .inl (by simpa only [EStore.view, hL.pers, hL.scr, hL.son] using hv)) hlv
        (hS.den.lsAll.of_ext (fun u hu => by
            have e : a'.store.lss.view u = a.store.lss.view u := by
              unfold LsStore.view; rw [hL.lsp, hL.lss, hL.lon]
            rw [← e]; exact hu)
          (lsExt_of_tables hL.lsp hL.lss hL.lon hL.ext)), hmode⟩,
    StackKept.of_frameL hf
      ⟨fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega,
       fun h => by have := hA _ h; simp only [BSTK, ArrId] at this; omega, hP⟩
      ⟨fun h => by have := hC _ h; simp at this, fun h => by have := hC _ h; simp at this, hP0⟩ hlc hP1 hPT⟩
  · rw [hL.caches]
    exact CoreRM.frame (A := A) (C := C) (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
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


section leaves
variable {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
  {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-- **`intern_fvar` refines `internE (.fvar …)` under `CoreS`.** -/
theorem internFVar_core (hS : CoreS dn m a vis fe M eb) (u ty : Word) (hty : HW ty)
    (rs : List Word) (hI : fvinternW m u ty = some (rs.headD 0, m')) :
    CoreRef (internE (.fvar u.toNat (decE ty))) a decH dn m vis fe M eb rs m' := by
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.arena u ty _ hty m' hI
  have hf := (fvinternW_frame (hI := hI))
  have hI₂ := hI
  have hw := consInternM_lt fvarCS_wf hS.arena.1.fvar hI₂
  have hS' := hS.arena_frame hD (Keeps.run (keeps_cpl_internFVar _ _)
      (AM.run_of_ok _ _ hok)) hf
    (fun b hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp [FVREC, FVSLOT, FVLP])
    (fun b hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
  have hst := StackKept.of_frame hf
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- **`intern_sort` refines `internE (.sort …)` under `CoreS`.** -/
theorem internSort_core (hS : CoreS dn m a vis fe M eb) (u : Word) (hu : HW u)
    (rs : List Word) (hI : sointernW m u = some (rs.headD 0, m'))
    (hdu : ∃ l, denoteL a.store.ls (decI u) = some l) :
    CoreRef (internE (.sort (decI u))) a decH dn m vis fe M eb rs m' := by
  obtain ⟨hok, hD, hres⟩ := internSort_D m a hS.arena u _ hu m' hI
  have hf := (sointernW_frame (hI := hI))
  have hI₂ := hI
  have hw := consInternM_lt sortCS_wf hS.arena.1.sort hI₂
  have hS' := hS.arena_frameD hD (Keeps.run (keeps_cpl_internSort _) (AM.run_of_ok _ _ hok)) hf
    (fun b hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp [SOREC, SOSLOT, SOLP])
    (fun b hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (hS.den.of_internSort hdu (AM.run_of_ok _ _ hok) (hf.1 EREC (by simp [SOREC, SOSLOT, SOLP, EREC]) (by decide)))
    (hmode := hS.mode.frame hf (by simp) (by simp))
  have hst := StackKept.of_frame hf
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- The level an interning returns reads back (`lvlAll_internLNode`), at the state after it. -/
theorem internLNode_res_den {v : LNodeView} (hS : CoreS dn m a vis fe M eb)
    (hch : ∀ c ∈ v.lchildren, ∃ l, denoteL a.store.ls c = some l)
    (hnch : ∀ n ∈ v.nchildren, ∃ x, denoteN a.store.ls.ns n = some x)
    (hok : AM.ok (internLNode v) a) :
    ∃ l, denoteL (AM.st (internLNode v) a).store.ls (AM.res (internLNode v) a) = some l := by
  have hr := AM.run_of_ok _ _ hok
  exact (lvlAll_internLNode hS.arena.1 hS.den.lvlAll hch hnch hr).2

/-- **`intern_succ` refines `internLNode (.succ …)` under `CoreS`.** -/
theorem internSucc_core (hS : CoreS dn m a vis fe M eb) (u : Word) (hu : HW u)
    (rs : List Word) (hI : sinternW m u = some (rs.headD 0, m'))
    (hdu : ∃ l, denoteL a.store.ls (decI u) = some l) :
    CoreRef (internLNode (.succ (decI u))) a decLv dn m vis fe M eb rs m' := by
  obtain ⟨hok, hX, hres⟩ := sintern_correct m a hS.arena.1.succ u hu _ _ hI
  have hf := (sinternW_frame (hI := hI))
  have hI₂ := hI
  have hR' := hS.arena.1.lift_succ _ _ _ _
    ⟨hX, sintern_hp m a hS.arena.1.succ u hu hS.arena.1.succHp (lvlHPW_ok m a hS.arena.1 u hu) _ _ hI⟩ hf
    (AM.st_proto succLens _ _ _ _ _ _ a (internLNode_succ_run _ a) hok)
  have hL := internLNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hS.of_level hL hR' hf
    (fun b hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (lvlAll_internLNode hS.arena.1 hS.den.lvlAll
      (fun c hc => by simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc; subst hc; exact hdu)
      (fun n hn => by simp [LNodeView.nchildren] at hn) (AM.run_of_ok _ _ hok)).1
    (lvlCnt_of_arena hS.arena.1 hR' (hf.2.1 1 (by decide))
      (LTGrow.internLNode (AM.run_of_ok _ _ hok)).1 (LTGrow.internLNode (AM.run_of_ok _ _ hok)).2
      (by simp [hL.lsp]) (by simp [hL.lss]))
  have hw := consInternM_lt succCS_wf hS.arena.1.succ hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- **`intern_imax` refines `internLNode (.imax …)` under `CoreS`.** -/
theorem internImax_core (hS : CoreS dn m a vis fe M eb) (u v : Word) (hu : HW u) (hv : HW v)
    (rs : List Word) (hI : iminternW m u v = some (rs.headD 0, m'))
    (hdu : ∃ l, denoteL a.store.ls (decI u) = some l) (hdv : ∃ l, denoteL a.store.ls (decI v) = some l) :
    CoreRef (internLNode (.imax (decI u) (decI v))) a decLv dn m vis fe M eb rs m' := by
  obtain ⟨hok, hX, hres⟩ := imintern_correct m a hS.arena.1.imax u v hu hv _ _ hI
  have hf := (iminternW_frame (hI := hI))
  have hI₂ := hI
  have hR' := hS.arena.1.lift_imax _ _ _ _
    ⟨hX, imintern_hp m a hS.arena.1.imax u v hu hv hS.arena.1.imaxHp (lvlHPW_or m a hS.arena.1 u v hu hv) _ _ hI⟩ hf
    (AM.st_proto imaxLens _ _ _ _ _ _ a (internLNode_imax_run _ _ a) hok)
  have hL := internLNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hS.of_level hL hR' hf
    (fun b hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (lvlAll_internLNode hS.arena.1 hS.den.lvlAll
      (fun c hc => by
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc; rcases hc with rfl | rfl
        · exact hdu
        · exact hdv)
      (fun n hn => by simp [LNodeView.nchildren] at hn) (AM.run_of_ok _ _ hok)).1
    (lvlCnt_of_arena hS.arena.1 hR' (hf.2.1 1 (by decide))
      (LTGrow.internLNode (AM.run_of_ok _ _ hok)).1 (LTGrow.internLNode (AM.run_of_ok _ _ hok)).2
      (by simp [hL.lsp]) (by simp [hL.lss]))
  have hw := consInternM_lt imaxCS_wf hS.arena.1.imax hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

end leaves

end L.Arena
