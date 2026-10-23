import ConAgua.Front.FrontPreOK3
import ConAgua.Front.FrontPre
import ConAgua.Checker.HoistWalkRef
import ConAgua.Checker.FrontProg

/-!
# The frontend after the prelude, with the records' words (lane `pipeline`)

`frontAll_refines_pre_ok`: `frontAll_refines_pre` (`FrontPre.lean`) where, in addition, every record
of `DECL` before the run is `RecOK` (`Checker/HoistRefBase.lean`); then every record after it is,
and the twin's records are walkable (`WalkableDecl`, `Checker/HoistWalkRef.lean`: an inductive
block holds no projection table). The run is `runI_refines` with the stronger invariant
`FrontInvOK`. The memory side of a line is `DGrow` (`FrontPreOK1.lean`‥`FrontPreOK3.lean`); the
twin side is that a line pushes at most one record, and an inductive block of `indInfo`, `ctorInfo`
and `recInfo` constants (`applyLine_decls`). A pointer word of an inductive record decodes to one
of those, so it is not `0` (the truncated pool's word `0` decodes to an `axiomInfo`): `recOK_new`.
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD parseChunks
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-! ## The twin's records -/

/-- A block's constant as the twin's install builds it. -/
def GoodCI : IConstantInfo → Prop
  | .indInfo .. | .ctorInfo .. | .recInfo .. => True
  | _ => False

/-- A record as the twin's parse pushes it: an inductive block of `GoodCI` constants. -/
def GoodDecl : IDeclaration → Prop
  | .indDecl b _ => ∀ ci ∈ b, GoodCI ci
  | _ => True

theorem GoodDecl.walkable {d : IDeclaration} (h : GoodDecl d) : L.Checker.WalkableDecl d := by
  sorry

/-- **A line pushes at most one record**, a `GoodDecl` one. -/
theorem applyLine_decls {st st' : StateD} {r : LineRec} {a a' : AState}
    (h : (applyLine st r).run a = .ok (.inl st', a')) :
    st'.decls = st.decls ∨ ∃ d, st'.decls = st.decls.push d ∧ GoodDecl d := by
  sorry

theorem init_decls {a a₁ : AState} {st₀ : StateD} (h : StateD.init.run a = .ok (st₀, a₁)) :
    st₀.decls = #[] := by
  sorry

/-! ## `RecOK` across a line -/

/-- The old records keep `RecOK` when their words and the pool up to its top stay. -/
theorem recOK_keep {D P D' P' : Array Word} {ds : Array IDeclaration} (hF : DeclsF D P ds)
    (hR : ∀ x < ds.size, L.Checker.RecOK D P x)
    (g1 : ∀ j, 0 < j → j < 1 + 8 * ds.size → D'[j]? = D[j]?)
    (g2 : ∀ j, 0 < j → j ≤ (P[0]?.getD 0).toNat → P'[j]? = P[j]?) :
    ∀ x < ds.size, L.Checker.RecOK D' P' x := by
  sorry

/-- A new record is `RecOK`. -/
theorem recOK_new {D P : Array Word} {ds : Array IDeclaration} (hF : DeclsF D P ds) (x : Nat)
    (hx : x < ds.size) (hG : GoodDecl ds[x]) (hN : NewOK D x) : L.Checker.RecOK D P x := by
  sorry

/-- **`RecOK` across a line.** -/
theorem recOK_line {D : Array IDeclaration} {m m' : Mem} {st st' : StateD}
    (hD : StateDR m (st.pre D)) (hD' : StateDR m' (st'.pre D)) (hg : DGrow m m')
    (hR : ∀ x < D.size + st.decls.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x)
    (hd : st'.decls = st.decls ∨ ∃ d, st'.decls = st.decls.push d ∧ GoodDecl d) :
    ∀ x < D.size + st'.decls.size, L.Checker.RecOK (m'.arr64 DECL) (m'.arr64 DLP) x := by
  have hF := hD.decls
  have hF' := hD'.decls
  simp only [StateD.pre_decls, Array.size_append] at hF hF' hR ⊢
  have hc : dcnt m = D.size + st.decls.size := by
    have := hF.count; simp only [Array.size_append] at this; exact this
  have hc' : dcnt m' = D.size + st'.decls.size := by
    have := hF'.count; simp only [Array.size_append] at this; exact this
  have hk := recOK_keep hF (by simpa using hR) (fun j h1 h2 => hg.decl j h1 (by rw [hc]; simpa using h2))
    (fun j h1 h2 => hg.dlp j h1 h2)
  simp only [Array.size_append] at hk
  rcases hd with e | ⟨d, e, hgd⟩
  · rw [e]; exact hk
  · intro x hx
    rw [e, Array.size_push] at hx
    by_cases hx' : x < D.size + st.decls.size
    · exact hk x hx'
    have hxe : x = D.size + st.decls.size := by omega
    subst hxe
    refine recOK_new hF' _ (by simp [e]) ?_ (hg.new _ (by omega) (by rw [hc', e, Array.size_push]; omega))
    simp [e, Array.getElem_append_right]
    sorry

/-! ## The invariant -/

section pre
variable (D : Array IDeclaration)

/-- The driver's invariant after the prelude, with the records' words: `FrontInvP`, every record
`RecOK`, the twin's records `GoodDecl`. -/
def FrontInvOK (b : ByteArray) (m : Mem) (a : AState) (st : StateD) : Prop :=
  FrontInvP D b m a st ∧
    (∀ x < D.size + st.decls.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) ∧
    ∀ d ∈ st.decls, GoodDecl d

section refine
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem lineKW_step_ok (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (i : USize) (ok nx : Word) (st : StateD)
    (a : AState) (hI : FrontInvOK D b m a st) (hi : i < b.usize)
    (h : lineKW p b.data m i.toUInt64 = some (ok, nx, m'))
    (hok : ok ≠ 0) : LineStepI (FrontInvOK D b) b i nx st a m' := by
  obtain ⟨r', q, st₀, h1, h2, h3, h4, hInv⟩ :=
    lineKW_step_pre D b h64 hsize p hFI hAI hII hXI m m' i ok nx st a hI.1 hi h hok
  have hg := lineKW_grow b h64 hsize p hFI hAI hII hXI m m' hI.1.1 i a (st.pre D) hI.1.2.1
    hI.1.2.2.1 hI.1.2.2.2.1 ok nx h
  have hrun := AM.run_of_ok _ _ h3
  rw [h4] at hrun
  have hd := applyLine_decls hrun
  refine ⟨r', q, st₀, h1, h2, h3, h4, hInv, recOK_line hI.1.2.2.1 hInv.2.2.1 hg hI.2.1 hd, ?_⟩
  rcases hd with e | ⟨d, e, hgd⟩
  · rw [e]; exact hI.2.2
  · rw [e]
    intro d' hd'
    rcases Array.mem_push.mp hd' with h' | h'
    · exact hI.2.2 d' h'
    · rw [h']; exact hgd

/-- **The driver's model refines `parseBytes`, after the prelude, with the records' words.** -/
theorem frontRunW_refines_pre_ok (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (a₀ : AState) (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a₀) (hD : StateDR m (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x)
    (h : runI (lineKW p b.data) b.size (initKW m) = some (0, m')) :
    ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧ FrontInvOK D b m' a' st' := by
  refine runI_refines (FrontInvOK D b) b h64 hsize (lineKW p b.data)
    (lineKW_step_ok D b h64 hsize p hFI hAI hII hXI)
    (fun m a => m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m (StateD.blank.pre D) ∧
      ConRon.Bridge.StateOK a ∧ a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a ∧
      ∀ x < D.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) initKW ?_ m m' a₀
    ⟨hm, hA, hD, hok, hoff, hpins, hR⟩ h
  intro m m₁ a ⟨hm, hA, hD, hok, hoff, hpins, hR⟩ hi
  have hk := initKW_dk m m₁ hi
  unfold initKW at hi
  split at hi
  · cases hi
  rename_i m₂ hW
  split at hi
  · rename_i hk'
    cases hi
    obtain ⟨h1, h2, h3⟩ := frontInitW_refines_pre D m m₁ a hA hD hW
    have hr := AM.run_of_ok _ _ h1
    have he := init_decls hr
    refine ⟨AM.res ConRon.Arena.Frontend.StateD.init a, AM.st ConRon.Arena.Frontend.StateD.init a, hr,
      ⟨hk'.trans hm, h2, h3, TwinOK.init hok hoff hpins hr⟩, ?_, ?_⟩
    · rw [he, hk.1, hk.2]; simpa using hR
    · rw [he]; simp
  · cases hi

end refine

/-- **Bytes → stores after the prelude, with the records' words**: `frontAll_refines_pre`, and
when every record of `DECL` before is `RecOK`, so is every record after; the twin's records are
walkable. -/
theorem frontAll_refines_pre_ok (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, L.Checker.RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x) :
    ⦃fun s => s = s₀⦄
    invoke frontAllProg (exec frontAllProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st' ∧
      (∀ x < D.size + st'.decls.size, L.Checker.RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x) ∧
      ∀ d ∈ st'.decls, L.Checker.WalkableDecl d; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun h0
  have hW := M.of_run (P := fun s => s = s₀) hs hrun
    (frontRun_spec frontAllProg (lineKW frontAllProg b.data) b.data _
      (fun n s₀ i hm hz hi => frontLineK_spec frontAllProg frontAllProg_scan frontAllProg_front rfl
        rfl rfl rfl rfl rfl rfl frontAllProg_expr rfl frontAllProg_dfields frontAllProg_decl rfl
        b.data hsize _ hpool n s₀ i hm hz hi)
      initKW (fun n s₀ _ _ => frontInitK_spec frontAllProg frontAllProg_front frontAllProg_expr rfl
        n s₀) rfl n s₀ hm rfl)
  rw [h0] at hW
  obtain ⟨st', a', h1, ⟨-, h2, h3, h4⟩, h5, h6⟩ :=
    frontRunW_refines_pre_ok D b h64 hsize frontAllProg frontAllProg_indFields frontAllProg_indApply
      frontAllProg_indInstall frontAllProg_indLine s₀.mem s'.mem a₀ hm hA hD hok hoff hpins hR hW
  exact ⟨st', a', h1, h2, h3, h4, h5, fun d hd => (h6 d hd).walkable⟩

/-- **The streaming form** (`parseChunks [b]`), after the prelude, with the records' words. -/
theorem frontAll_refines_chunks_pre_ok (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, L.Checker.RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x) :
    ⦃fun s => s = s₀⦄
    invoke frontAllProg (exec frontAllProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseChunks [b]).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st' ∧
      (∀ x < D.size + st'.decls.size, L.Checker.RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x) ∧
      ∀ d ∈ st'.decls, L.Checker.WalkableDecl d; ⊤⦄ := by
  have hu : b.size < USize.size := by
    rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega
  rw [ConAgua.Front.ChunkBridge.parseChunks_single b hu]
  exact frontAll_refines_pre_ok D b h64 hsize n s₀ hm hpool a₀ hA hD hok hoff hpins hR

/-- **The same at the checker's program** (`checkerProg_front_run`). The walkability of `D` is not
used (the twin's records are walkable on their own). -/
theorem frontRunOK_checker' (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, L.Checker.RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x)
    (_hW : ∀ d ∈ D, L.Checker.WalkableDecl d) :
    ⦃fun s => s = s₀⦄
    invoke L.Checker.checkerProg (exec L.Checker.checkerProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st' ∧
      (∀ x < D.size + st'.decls.size, L.Checker.RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x) ∧
      ∀ d ∈ st'.decls, L.Checker.WalkableDecl d; ⊤⦄ := by
  rw [L.Checker.checkerProg_front_run n]
  exact frontAll_refines_pre_ok D b h64 hsize n s₀ hm hpool a₀ hA hD hok hoff hpins hR

end pre

end L.Front
