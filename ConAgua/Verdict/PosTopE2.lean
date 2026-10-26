import ConAgua.Verdict.PosTopE1

/-!
# `nest_uniform`'s error claim (lane `verdicts-b`, helper `ia2`, fork `top`)

`unW_ok`'s proof on the model `nuE`: `nest_uniform_cs` claims nothing (`nvFns`); its answer `0`
is the twin's `allM` answering `false`, where it rejects.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

/-- **`nest_uniform`'s error claim** (the generic shape of `unW_ok`, at `realCall p`). -/
theorem nuE_claim {p : Prog} (hlk : NuLook p) (hc : p.lookup "nest_uniform_cs" = some nestUniformCsL)
    (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word) (c : NestCtx)
    (hhi : c.hiAt 0 < 2 ^ 64) (J : Mem → AState → Prop) (Pcv : IConstantVal → Prop)
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
    ∀ (m : Mem) (a : AState) (off l : Word) (css : List (List (IConstantVal × Nat))) (e : Err),
    nuE p k m ctx off l = .error e → StageR dn vis fe m a → J m a → (∀ cs ∈ css, ∀ x ∈ cs, Pcv x.1) →
    UCtx dn vis fe m ctx c → l.toNat = css.length → CssAt m off.toNat css → PosMR m →
    ErrClaim (ConRon.Arena.nestUniform c css) a e := by
  induction k with
  | zero =>
    intro m a off l css e he
    rw [nuE.eq_1] at he; cases he; intros; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro m a off l css e he hS hJ hPc hU hl hcss hP
    by_cases hl0 : l = 0
    · rw [nuE.arm1 p k m ctx off l hl0] at he; cases he
    rw [nuE.arm2 p k m ctx off l hl0] at he
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨cs, css', rfl⟩ := List.exists_cons_of_ne_nil (show css ≠ [] from fun e => by rw [e] at hl; exact hlz hl)
    obtain ⟨hdr, o, ll, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hcss 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h1 h6 h8
    have r1 : rdW (m.arr64 IW) off = hdr := by simp [rdW, h1]
    have r2 : rdW (m.arr64 IW) hdr = o := by simp [rdW, h2]
    have hh1 : (hdr + 1).toNat = hdr.toNat + 1 := word_add_toNat (by
      have := hS.2.1; have := hS.2.2.2.1; simp; omega)
    have r3 : rdW (m.arr64 IW) (hdr + 1) = ll := by simp [rdW, hh1, h3]
    rw [r1, r2, r3] at he
    rw [ConRon.Arena.nestUniform.eq_2]
    cases h1 : callE p k "nest_uniform_cs" [ctx, o, ll] m with
    | error e1 =>
      rw [h1, nuE.k_nest_uniform_cs.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
    | ok q =>
    obtain ⟨r, m1⟩ := q
    obtain ⟨s1, hs1, -, huc⟩ := triple_of_callW
      (nestUniformCs_spec p hlk hc (realCall p) (realCall_spec p) k ⟨m, Locals.init []⟩ ctx o ll) (callW_of_callE h1)
    simp only at huc hs1
    rw [hs1] at huc
    obtain ⟨b, a1, hrun1, hS1, hg1, hr, hP1, hJ1⟩ := ucW_ok dn fe vis ctx c hhi (realCall p) J Pcv hJI hJnu k m m1 a
      o ll cs _ huc hS hJ (hPc cs List.mem_cons_self) hU h6 (by omega) h8 hP
    simp only [List.headD_cons] at hr
    refine ErrClaim.bind_right hrun1 ?_
    cases b with
    | false =>
      rw [h1, nuE.k_nest_uniform_cs.abort1 p k ctx off l r m1 (by simpa using hr)] at he; cases he
      exact ErrClaim.fail _ _ (by decide)
    | true =>
      rw [h1, nuE.k_nest_uniform_cs.arm1 p k ctx off l r m1 (by rw [hr]; decide)] at he
      simp only [ite_true]
      have ho1 : (off + 1).toNat = off.toNat + 1 := word_add_toNat (by
        have := hS.2.1; have := hS.2.2.2.1; simp; omega)
      have hl1 : (l - 1).toNat = l.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      cases hx : nuE p k m1 ctx (off + 1) (l - 1) with
      | error ε =>
        rw [hx, nuE.k_nest_uniform.none] at he; cases he
        exact ih m1 a1 (off + 1) (l - 1) css' _ hx hS1 hJ1
          (fun cs hcs => hPc cs (List.mem_cons_of_mem _ hcs)) (hU.grow hg1)
          (by rw [hl1, hl]; simp) (by rw [ho1]; exact hcss.tail.grow hg1) hP1
      | ok q => obtain ⟨r0, m0⟩ := q; rw [hx, nuE.k_nest_uniform.arm1] at he; cases he

end L.Ind
