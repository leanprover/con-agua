import ConAgua.Arena.IndPosSpec.NuW

/-!
# UnW2

`unK_no`, `nestUniform_spec`, `CssAt`, `CssAt.tail`, `CssAt.grow`, `unW_ok`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena

section arms
variable (cR : CallM) (k : Nat) (m m1 : Mem) (ctx off l : Word) (r : List Word)
theorem unK_no (h : r.headD 0 = 0) : unK cR k ctx off l (some (r, m1)) = none := by rw [unK, ite_eq_left h]
end arms
attribute [ind_grind] unK_no

theorem nestUniform_spec (p : Prog) (hl : NuLook p) (hc : p.lookup "nest_uniform_cs" = some nestUniformCsL)
    (hp : p.lookup "nest_uniform" = some nestUniformL) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) :
    ∀ (s₀ : St) (ctx off l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform" [ctx, off, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ unW cR k s₀.mem ctx off l = some s'.mem; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ ctx off l
    rw [invoke_eq _ hp]; simp only [callFn, nestUniformL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ ctx off l
    simp only [invoke_eq _ hp, callFn, nestUniformL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestUniformCs_spec p hl hc cR hcR k, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The members' constructor lists: headers at `off, off + 1, …`, each a `[cv, nF]` pointer slice. -/
def CssAt (m : Mem) (off : Nat) (css : List (List (IConstantVal × Nat))) : Prop :=
  ∀ i (hi : i < css.length), ∃ hdr o l : Word, (m.arr64 IW)[off + i]? = some hdr ∧
    (m.arr64 IW)[hdr.toNat]? = some o ∧ (m.arr64 IW)[hdr.toNat + 1]? = some l ∧
    off + i < iwTop m ∧ hdr.toNat + 1 < iwTop m ∧ l.toNat = css[i].length ∧
    o.toNat + l.toNat ≤ iwTop m ∧ CsAt m o.toNat css[i] (· < iwTop m)

theorem CssAt.tail {m : Mem} {off : Nat} {x : List (IConstantVal × Nat)} {xs : List (List (IConstantVal × Nat))}
    (h : CssAt m off (x :: xs)) : CssAt m (off + 1) xs := fun i hi => by
  obtain ⟨hdr, o, l, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h (i + 1) (by simp; omega)
  exact ⟨hdr, o, l, by rw [show off + 1 + i = off + (i + 1) by omega]; exact h1, h2, h3, by omega, h5,
    by simpa using h6, h7, by simpa using h8⟩

theorem CssAt.grow {m m' : Mem} {off : Nat} {css : List (List (IConstantVal × Nat))} (h : CssAt m off css)
    (hg : IWGrow m m') : CssAt m' off css := fun i hi => by
  obtain ⟨hdr, o, l, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h i hi
  refine ⟨hdr, o, l, by rw [hg.2.2.1 _ h4]; exact h1, by rw [hg.2.2.1 _ (by omega)]; exact h2,
    by rw [hg.2.2.1 _ h5]; exact h3, by have := hg.1; omega, by have := hg.1; omega, h6,
    by have := hg.1; omega, h8.grow (by omega) hg⟩

theorem unW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word) (c : NestCtx)
    (hhi : c.hiAt 0 < 2 ^ 64) (cR : CallM) (J : Mem → AState → Prop) (Pcv : IConstantVal → Prop)
    (hJI : ∀ (m : Mem) (a : AState) (cv : Word) (cvv : IConstantVal), J m a → Pcv cvv →
      decCV (erecP m) cv.toNat = some cvv → ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (hJnu : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (cv : Word) (cvv : IConstantVal) (r : List Word) (x : Bool),
      J m a → Pcv cvv → nuWf cR k m ctx cv = some (r, m') →
      (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') → StageR dn vis fe m' a' → (NuAfr → AFr m m') →
      J m' a') (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (css : List (List (IConstantVal × Nat))),
    unW cR k m ctx off l = some m' → StageR dn vis fe m a → J m a → (∀ cs ∈ css, ∀ x ∈ cs, Pcv x.1) →
    UCtx dn vis fe m ctx c →
    l.toNat = css.length → CssAt m off.toNat css → PosMR m →
    ∃ a', (ConRon.Arena.nestUniform c css).run a = .ok ((), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      PosMR m' ∧ J m' a' := by
  induction k with
  | zero => intro m m' a off l css h; simp [unW] at h
  | succ k ih =>
    intro m m' a off l css h hS hJ hPc hU hl hcss hP
    by_cases hl0 : l = 0
    · rw [unW_nil (h := hl0)] at h
      cases h
      subst hl0
      have : css = [] := List.eq_nil_of_length_eq_zero (by rw [← hl]; rfl)
      subst this
      exact ⟨a, rfl, hS, IWGrow.refl _, hP, hJ⟩
    rw [unW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨cs, css', rfl⟩ := List.exists_cons_of_ne_nil (show css ≠ [] from fun e => by rw [e] at hl; exact hlz hl)
    obtain ⟨hdr, o, ll, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hcss 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h1 h6 h8
    have r1 : rdW (m.arr64 IW) off = hdr := by simp [rdW, h1]
    have r2 : rdW (m.arr64 IW) hdr = o := by simp [rdW, h2]
    have hh1 : (hdr + 1).toNat = hdr.toNat + 1 := word_add_toNat (by
      have := hS.2.1; have := hS.2.2.2.1; simp; omega)
    have r3 : rdW (m.arr64 IW) (hdr + 1) = ll := by simp [rdW, hh1, h3]
    rw [r1, r2, r3] at h
    rcases huc : ucW cR k m ctx o ll with _ | ⟨r, m1⟩ <;> rw [huc] at h; · simp [unK] at h
    obtain ⟨b, a1, hrun1, hS1, hg1, hr, hP1, hJ1⟩ := ucW_ok dn fe vis ctx c hhi cR J Pcv hJI hJnu k m m1 a o ll cs r
      huc hS hJ (hPc cs List.mem_cons_self) hU
      h6 (by omega) h8 hP
    rw [ConRon.Arena.nestUniform.eq_2]
    cases b with
    | false => rw [unK_no (h := hr)] at h; simp at h
    | true =>
      rw [unK_yes (h := by rw [hr]; decide)] at h
      have ho1 : (off + 1).toNat = off.toNat + 1 := word_add_toNat (by
        have := hS.2.1; have := hS.2.2.2.1; simp; omega)
      have hl1 : (l - 1).toNat = l.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      obtain ⟨a', hrun, hS', hg', hP', hJ'⟩ := ih m1 m' a1 (off + 1) (l - 1) css' h hS1 hJ1
        (fun cs hcs => hPc cs (List.mem_cons_of_mem _ hcs)) (hU.grow hg1)
        (by rw [hl1, hl]; simp) (by rw [ho1]; exact hcss.tail.grow hg1) hP1
      refine ⟨a', ?_, hS', hg1.trans hg', hP', hJ'⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, ite_true]
      exact hrun

end L.Ind

end
