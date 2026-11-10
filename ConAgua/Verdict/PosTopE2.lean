module

public import ConAgua.Verdict.PosTopE1
public import ConAgua.Arena.IndPosSpec.UnW2
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NuW
public import ConAgua.Arena.IlpRd
public import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.IndPosSpec.UCtx
public import ConAgua.Arena.Verdict

@[expose] public section

/-!
# `nest_uniform`: one model and one refinement for both outcomes

`nuE` (`l_model … unified`, `PosTopE1`): `nest_uniform_cs` (no-verdict) through its `Option` model
`ucW`, the recursive call through the model itself. `nu_ref` refines `nestUniform` for both
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
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  pos : PosMR m'
  inv : J m' a'

/-- **`nest_uniform` refines `nestUniform`, both outcomes** (under the callers' invariant `J`). -/
theorem nu_ref {p : Prog} (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word)
    (c : NestCtx) (hhi : c.hiAt 0 < 2 ^ 64) (J : Mem → AState → Prop) (Pcv : IConstantVal → Prop)
    (hJI : ∀ (m : Mem) (a : AState) (cv : Word) (cvv : IConstantVal), J m a → Pcv cvv →
      decCV (erecP m) cv.toNat = some cvv → ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (erRd m (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR vis fe m1 a1 → IlpRd (realCall p) dn vis fe (IlpBase m1 a1))
    (hJnu : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (cv : Word) (cvv : IConstantVal) (r : List Word) (x : Bool),
      J m a → Pcv cvv → nuWf (realCall p) k m ctx cv = some (r, m') →
      (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') → StageR vis fe m' a' → (NuAfr → AFr m m') →
      J m' a') (k : Nat) :
    ∀ {m : Mem} {a : AState} {off l : Word} {css : List (List (IConstantVal × Nat))},
    StageR vis fe m a → J m a → (∀ cs ∈ css, ∀ x ∈ cs, Pcv x.1) →
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
      have := hS.iw.iw; have := hS.iw.iwSize; simp; omega)
    have r3 : rdW (m.arr64 IW) (hdr + 1) = ll := by simp [rdW, hh1, h3]
    rw [r1, r2, r3, ConRon.Arena.nestUniform.eq_2]
    refine RefE.bindLift (fun _ => nuE.k_nest_uniform_cs.none ..) fun r m1 huc' => ?_
    obtain ⟨b, a1, hrun1, hS1, hg1, hr, hP1, hJ1⟩ := ucW_ok dn fe vis ctx c hhi (realCall p) J Pcv hJI hJnu k m m1 a
      o ll cs _ huc' hS hJ (hPc cs List.mem_cons_self) hU h6 (by omega) h8 hP
    refine ⟨_, _, hrun1, RefE.ofArms (fun h => nuE.k_nest_uniform_cs.abort1 (hc1 := h) ..)
      (fun h => nuE.k_nest_uniform_cs.arm1 (hc1 := h) ..) ?_⟩
    refine RefE.guardIf (by decide) (fun h => by grind) (fun h => by grind) fun _ _ => ?_
    have ho1 : (off + 1).toNat = off.toNat + 1 := word_add_toNat (by
      have := hS.iw.iw; have := hS.iw.iwSize; simp; omega)
    have hl1 : (l - 1).toNat = l.toNat - 1 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
    exact RefE.lastE (fun _ => nuE.k_nest_uniform.none ..) (f := fun v => ([0], v.2))
      (fun _ => nuE.k_nest_uniform.arm1 ..) id
      (ih (m := m1) (a := a1) (off := off + 1) (l := l - 1) (css := css') hS1 hJ1
        (fun cs hcs => hPc cs (List.mem_cons_of_mem _ hcs)) (hU.grow hg1)
        (by rw [hl1, hl]; simp) (by rw [ho1]; exact hcss.tail.grow hg1) hP1)
      fun _ _ _ _ hR => ⟨hR.stage, hg1.trans hR.grow, hR.pos, hR.inv⟩

end L.Ind
