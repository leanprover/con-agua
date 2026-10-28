import ConAgua.Verdict.PosTopE1
import ConAgua.Arena.IndPosSpec.UnW2
import ConAgua.Checker.NoVerdictTree

/-!
# `nest_uniform`: one model and one refinement for both outcomes

`nuE` (`l_model … unified`, `PosTopE1`): `nest_uniform_cs` (no-verdict) through its `Option` model
`ucW1`, the recursive call through the model itself. `nu_ref` refines `nestUniform` for both
outcomes, under an invariant `J` the callers choose (`ucW_ok`'s): its answer `0` is the twin's
`allM` answering `false`, where it rejects.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

/-- What `nest_uniform` gives (from `m`, the invariant `J`): the stage, the growth, the frames,
the invariant. -/
structure NuPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (J : Mem → AState → Prop)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  pos : PosMR m'
  inv : J m' a'

/-- **`nest_uniform` refines `nestUniform`, both outcomes** (under the callers' invariant `J`). -/
theorem nu_ref {p : Prog} (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word)
    (c : NestCtx) (hhi : c.hiAt 0 < 2 ^ 64) (J : Mem → AState → Prop) (Pcv : IConstantVal → Prop)
    (hJI : ∀ (m : Mem) (a : AState) (cv : Word) (cvv : IConstantVal), J m a → Pcv cvv →
      decCV (erecP m) cv.toNat = some cvv → ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd (realCall p) dn vis fe (IlpBase m1 a1))
    (hJnu : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (cv : Word) (cvv : IConstantVal) (r : List Word) (x : Bool),
      J m a → Pcv cvv → nuWf (realCall p) k m ctx cv = some (r, m') →
      (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') → StageR dn vis fe m' a' → (NuAfr → AFr m m') →
      J m' a') (k : Nat) :
    ∀ {m : Mem} {a : AState} {off l : Word} {css : List (List (IConstantVal × Nat))},
    StageR dn vis fe m a → J m a → (∀ cs ∈ css, ∀ x ∈ cs, Pcv x.1) →
    UCtx dn vis fe m ctx c → l.toNat = css.length → CssAt m off.toNat css → PosMR m →
    RefE (closedNV p _root_.L.Checker.nvFns = true) (nuE p k m ctx off l) (ConRon.Arena.nestUniform c css) a
      (fun v _ a' => NuPost dn vis fe J m v.2 a') := by
  induction k with
  | zero => intros; rw [nuE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro m a off l css hS hJ hPc hU hl hcss hP
    by_cases hl0 : l = 0
    · rw [nuE.arm1 p k m ctx off l hl0]
      subst hl0
      have : css = [] := List.eq_nil_of_length_eq_zero (by rw [← hl]; rfl)
      subst this
      exact RefE.ret rfl ⟨hS, IWGrow.refl _, hP, hJ⟩
    rw [nuE.arm2 p k m ctx off l hl0]
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨cs, css', rfl⟩ := List.exists_cons_of_ne_nil (show css ≠ [] from fun e => by rw [e] at hl; exact hlz hl)
    obtain ⟨hdr, o, ll, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hcss 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h1 h6 h8
    have r1 : rdW (m.arr64 IW) off = hdr := by simp [rdW, h1]
    have r2 : rdW (m.arr64 IW) hdr = o := by simp [rdW, h2]
    have hh1 : (hdr + 1).toNat = hdr.toNat + 1 := word_add_toNat (by
      have := hS.2.1; have := hS.2.2.2.1; simp; omega)
    have r3 : rdW (m.arr64 IW) (hdr + 1) = ll := by simp [rdW, hh1, h3]
    rw [r1, r2, r3, ConRon.Arena.nestUniform.eq_2]
    rcases huc : ucW1 (realCall p) k m ctx o ll with _ | ⟨b1, m1⟩
    · rw [liftE_none, nuE.k_nest_uniform_cs.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨r, huc', hrb⟩ := ucW1_some huc
    obtain ⟨b, a1, hrun1, hS1, hg1, hr, hP1, hJ1⟩ := ucW_ok dn fe vis ctx c hhi (realCall p) J Pcv hJI hJnu k m m1 a
      o ll cs _ huc' hS hJ (hPc cs List.mem_cons_self) hU h6 (by omega) h8 hP
    rw [hrb] at hr
    refine RefE.bind_right hrun1 ?_
    cases b with
    | false =>
      rw [nuE.k_nest_uniform_cs.abort1 p k ctx off l b1 m1 (by simpa using hr)]
      exact fun _ => ErrClaim.fail _ _ (by decide)
    | true =>
      rw [nuE.k_nest_uniform_cs.arm1 p k ctx off l b1 m1 (by rw [hr]; decide)]
      refine RefE.ite_pos rfl ?_
      have ho1 : (off + 1).toNat = off.toNat + 1 := word_add_toNat (by
        have := hS.2.1; have := hS.2.2.2.1; simp; omega)
      have hl1 : (l - 1).toNat = l.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      have ih' := ih (m := m1) (a := a1) (off := off + 1) (l := l - 1) (css := css') hS1 hJ1
        (fun cs hcs => hPc cs (List.mem_cons_of_mem _ hcs)) (hU.grow hg1)
        (by rw [hl1, hl]; simp) (by rw [ho1]; exact hcss.tail.grow hg1) hP1
      rcases hx : nuE p k m1 ctx (off + 1) (l - 1) with ε | ⟨r0, m0⟩ <;> rw [hx] at ih'
      · rw [nuE.k_nest_uniform.none]; exact ih'
      · rw [nuE.k_nest_uniform.arm1]
        obtain ⟨y, a', hrun, hR⟩ := ih'
        exact RefE.ret hrun ⟨hR.stage, hg1.trans hR.grow, hR.pos, hR.inv⟩

end L.Ind
