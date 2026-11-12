module

public import ConAgua.Arena.IndRealOpf3
public import ConAgua.Arena.IndRealOpfLeaf
public import ConAgua.Arena.CoreWalks
import ConAgua.Arena.IndRealOpf2
import ConAgua.Arena.DeclNatCv
import ConAgua.Arena.StageInst1
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.DerRel
import ConRon.Bridge.Grind
import ConAgua.L.WordOff
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfIotaRefine2

@[expose] public section

/-!
# `opf_go` under `CoreS` (the core's `proj_guard_rows`)

The core reaches the raw opening `opf_go` through `infer_proj`'s `proj_guard_rows`, where only
`CoreS` (at any maps and eager bit) and the pool's `IWOK` hold. Its steps under `CoreS`: `e_view`
(the memory and the twin kept), `inst_list`/`inst_entry` (the core's own refinements,
`instListOK_core`, `inst1_core`), `intern_fvar` (`CoreS.of_walk`), `spn_push`
(`CoreS.frame_stk`); `opfGo_okC` the walk, its substitution the stack slice it pushed.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}

/-! ## The steps under `CoreS` -/

/-- **`e_view` at a `∀`**: the memory kept, the binder's words, the twin's `view`. -/
theorem opfV_okC {k : Nat} {m m' : Mem} {a : AState} {M : ModeMaps}
    (hS : CoreS dn m a vis fe M eb) {e : Word}
    (hg : tagW e = 6) {r : List Word} (hc : callW opfP k "e_view" [e] m = some (r, m')) :
    m' = m ∧ (r.tail.headD 0).toNat < 2 ^ 32 ∧ (r.tail.tail.headD 0).toNat < 2 ^ 32 ∧
      (view (decE e)).run a = .ok (.forallE (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)), a) := by
  obtain ⟨s', hm, hs', hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (eView_spec opfP rfl k ⟨m, Locals.init []⟩ e) hc
  subst hs'
  simp only at hr hm
  subst hr hm
  obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.arena.base e hne
  obtain ⟨-, hw⟩ := eViewW_forall m e hg hne
  rw [hw] at hvr ⊢
  generalize tfld m FORALL (tierW e) (idxW e) 0 = x at hvr ⊢
  generalize tfld m FORALL (tierW e) (idxW e) 1 = y at hvr ⊢
  refine ⟨rfl, ?_⟩
  cases v <;> simp [ViewR] at hvr
  simp only [List.tail_cons, List.headD_cons]
  exact ⟨hvr.1, hvr.2.2.1, by rw [L.Ind.view_run_of hv, hvr.2.1, hvr.2.2.2]⟩

/-- **`inst_list` under `CoreS`** (`instListOK_core`), the stack kept. -/
theorem opfIl_okC {k : Nat} {m m' : Mem} {a : AState} {M : ModeMaps}
    (hS : CoreS dn m a vis fe M eb) {e o l d : Word} {vs : Array EIdx} (hsl : SpineR m o l vs)
    (htop : o.toNat + l.toNat ≤ (spTop m).toNat) (he : e.toNat < 2 ^ 32)
    {r : List Word} (hc : callW opfP k "inst_list" [e, o, l, d] m = some (r, m')) :
    ∃ a' M', (instantiateListFast coreWalkFuel (decE e) vs d.toNat).run a = .ok (decE (r.headD 0), a') ∧
      CoreS dn m' a' vis fe M' eb ∧ KeptAll M M' eb ∧ m'.arr64 SPN = m.arr64 SPN ∧
      rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 ∧ (r.headD 0).toNat < 2 ^ 32 := by
  have h := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
    (instListOK_core opfP_il rfl k ⟨m, Locals.init []⟩ a dn vis fe M eb e o l d vs hS he hsl htop) hc
  obtain ⟨M', hS', hK, -⟩ := h.after
  have hfr : MemFrame instListA instListC m m' := instList_frame opfP_il rfl (run_of_callW hc)
  obtain ⟨h1, h2⟩ := spn_of_lt64 hfr (lt64A_of_all rfl) (lt64_of_all rfl)
  refine ⟨_, M', ?_, hS', hK, h1, h2, h.resOk⟩
  rw [AM.run_of_ok _ _ h.run, h.res]; rfl

/-- **`inst_entry` under `CoreS`** (`inst1_core`), the stack kept. -/
theorem opfI1_okC {k : Nat} {m m' : Mem} {a : AState} {M : ModeMaps}
    (hS : CoreS dn m a vis fe M eb) {e v d : Word} (he : e.toNat < 2 ^ 32) {r : List Word}
    (hc : callW opfP k "inst_entry" [e, v, d] m = some (r, m')) :
    ∃ a' M', (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat).run a = .ok (decE (r.headD 0), a') ∧
      CoreS dn m' a' vis fe M' eb ∧ KeptAll M M' eb ∧ m'.arr64 SPN = m.arr64 SPN ∧
      rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 ∧ (r.headD 0).toNat < 2 ^ 32 := by
  have h := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
    (inst1_core opfP_inst rfl rfl "inst_entry" rfl k ⟨m, Locals.init []⟩ a dn vis fe M eb e v d hS he) hc
  obtain ⟨M', hS', hK, -⟩ := h.after
  have hfr : MemFrame instA instC m m' := instEntry_frame opfP_inst rfl rfl (run_of_callW hc)
  obtain ⟨h1, h2⟩ := spn_of_lt64 hfr instA_lt instC_lt
  refine ⟨_, M', ?_, hS', hK, h1, h2, h.resOk⟩
  rw [AM.run_of_ok _ _ h.run, h.res]; rfl

/-- **`intern_fvar` under `CoreS`** (`CoreS.of_walk`), the stack kept. -/
theorem opfFv_okC {k : Nat} {m m' : Mem} {a : AState} {M : ModeMaps}
    (hS : CoreS dn m a vis fe M eb) {u ty : Word} (hty : ty.toNat < 2 ^ 32) {r : List Word}
    (hc : callW opfP k "intern_fvar" [u, ty] m = some (r, m')) :
    ∃ a', (internE (.fvar u.toNat (decE ty))).run a = .ok (decE (r.headD 0), a') ∧
      CoreS dn m' a' vis fe M eb ∧ m'.arr64 SPN = m.arr64 SPN ∧
      rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 ∧ (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internFVar_spec opfP rfl rfl rfl k ⟨m, Locals.init []⟩ u ty) hc
  rw [hs'] at hI
  have hfr := fvinternW_frame m u ty _ _ hI
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.arena u ty _ hty m' hI
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  have hk := (keepsW_internE _).run hrun
  obtain ⟨hS', -⟩ := hS.of_walk hD hk hfr (by simp [tier1, FVREC, FVSLOT, FVLP]) (by simp)
    (hS.memos.frame hfr (by decide) (by decide))
  obtain ⟨h1, h2⟩ := spn_of_lt64 hfr (by simp [tier1, FVREC, FVSLOT, FVLP]) (by simp)
  exact ⟨_, hrun, hS', h1, h2, fvinternW_hw m a hS.arena.base.fvar u ty _ _ hI⟩

/-- **`spn_push` under `CoreS`.** -/
theorem spnPushW_okC {m m' : Mem} {a : AState} {M : ModeMaps} (hS : CoreS dn m a vis fe M eb)
    {x : Word} {r : List Word} (h : spnPushW m x = some (r, m')) :
    CoreS dn m' a vis fe M eb ∧
      (rdW (m.arr64 CTL) 136).toNat < (m.arr64 SPN).size ∧
      rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 + 1 ∧
      (∀ w : Word, spW m' w = if w = rdW (m.arr64 CTL) 136 then x else spW m w) ∧
      (m'.arr64 SPN).size = (m.arr64 SPN).size := by
  simp only [spnPushW] at h
  split at h
  · cases h
  rename_i hlt
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hfr : MemFrame [SPN] [136] m
      ((m.set64 SPN (rdW (m.arr64 CTL) 136) x).set64 CTL 136 (rdW (m.arr64 CTL) 136 + 1)) :=
    ((MemFrame.set64 m SPN (by decide) _ _).mono (fun b hb => hb) (by simp)).trans
      ((MemFrame.setCtl _ 136 _).mono (by simp) (fun c hc => hc))
  have hS' := hS.frame_stk hfr (by simp) (by simp)
  have hsz : (rdW (m.arr64 CTL) 136).toNat < (m.arr64 SPN).size := by
    have : ¬ (((m.arr64 SPN).size : Nat).toUInt64 ≤ rdW (m.arr64 CTL) 136) := hlt
    rw [UInt64.le_iff_toNat_le] at this
    have h2 : (((m.arr64 SPN).size : Nat).toUInt64).toNat = (m.arr64 SPN).size % 2 ^ 64 := by
      simp [Nat.toUInt64]
    have h3 : (m.arr64 SPN).size < 2 ^ 64 := by have := hS.spn; omega
    omega
  refine ⟨hS', hsz, ?_, ?_, hfr.size SPN⟩
  · have hc := hS.ctl136
    rw [L.Arena.rdW_set64, Mem.arr64_set64_ne _ _ _ _ _ (by decide),
      ite_eq_left ⟨rfl, rfl, by simp; omega⟩]
  · intro w
    simp only [spW]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), L.Arena.rdW_set64]
    by_cases hw : w = rdW (m.arr64 CTL) 136
    · subst hw; simp [hsz]
    · simp [hw, Ne.symm hw]

/-! ## The walks -/

/-- **`opf_go` refines `openPisRawGo` under `CoreS`**, the twin's `acc` the stack slice
`(co, cn)` below the top. -/
theorem opfGo_okC : ∀ (k : Nat) (m m' : Mem) (a : AState) (M : ModeMaps) (n e i co cn : Word)
    (acc : Array EIdx) (r : List Word), callW opfP k "opf_go" [n, e, i, co, cn] m = some (r, m') →
    CoreS dn m a vis fe M eb → e.toNat < 2 ^ 32 → SpineR m co cn acc →
    rdW (m.arr64 CTL) 136 = co + cn →
    i.toNat + ((m.arr64 SPN).size - (co.toNat + cn.toNat)) < 2 ^ 64 →
    ∃ x a' M', (openPisRawGo acc n.toNat (decE e) i.toNat).run a = .ok (x, a') ∧
      CoreS dn m' a' vis fe M' eb ∧ KeptAll M M' eb ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
      (∀ w : Word, w.toNat < (co + cn).toNat → spW m' w = spW m w) ∧
      OGo (co + cn) n m m' r (rawFR x) ∧ RawAcc acc x := by
  intro k
  induction k with
  | zero => intro m m' a M n e i co cn acc r hc; rw [callW_zero] at hc; cases hc
  | succ k ih =>
  intro m m' a M n e i co cn acc r hc hS he hsl htop hib
  have c' := callW_model (M := fun mm => opfGoK opfP k mm n e i co cn)
    (fun s => opfGoK_spec opfP rfl k s n e i co cn) hc
  have hw63 : (m.arr64 SPN).size < 2 ^ 63 := hS.spn
  have hcc : (co + cn).toNat = co.toNat + cn.toNat := L.toNat_add_of_lt _ _ (by have := hsl.bound; omega)
  have hst : co.toNat + cn.toNat ≤ (spTop m).toNat := by
    simp only [spTop, htop, hcc]; exact Nat.le_refl _
  simp only [opfGoK] at c'
  by_cases hn : n = 0
  · rw [ite_eq_left hn] at c'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
    subst hn
    refine ⟨_, _, M, opfGo_run_zero acc (decE e) i.toNat a, hS, KeptAll.refl _ _, rfl,
      fun w _ => rfl, ?_, fun p hp => by cases hp; simp⟩
    refine ⟨rfl, he, rfl, by rw [htop]; simp, L.Arena.SpineR.nil_at _ _ ?_, fun w _ => rfl⟩
    rw [hcc]; exact hsl.bound
  rw [ite_eq_right hn] at c'
  have hn1 := wsub1 hn
  by_cases hg : tagW e ≠ 6
  · rw [ite_eq_left hg] at c'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
    refine ⟨none, a, M, by rw [← hn1]; exact opfGo_run_nf acc _ _ _ a (by rw [decE_tag_forallE_beq e he]; simpa using hg),
      hS, KeptAll.refl _ _, rfl, fun _ _ => rfl, rfl, fun p hp => by cases hp⟩
  rw [ite_eq_right hg] at c'
  have hg6 : tagW e = 6 := Decidable.not_not.mp hg
  obtain ⟨rv, m1, h1, c'⟩ := ntBW_some c'
  obtain ⟨hm1, hx, hy, hview⟩ := opfV_okC hS hg6 h1
  subst m1
  obtain ⟨rd, m2, h2, c'⟩ := ntBW_some c'
  obtain ⟨a2, M2, hrun2, hS2, hK2, hspn2, htop2, hlt2⟩ := opfIl_okC hS hsl hst hx h2
  obtain ⟨rf, m3, h3, c'⟩ := ntBW_some c'
  obtain ⟨a3, hrun3, hS3, hspn3, htop3, hlt3⟩ := opfFv_okC hS2 hlt2 h3
  obtain ⟨ru, m4, h4, c'⟩ := ntBW_some c'
  obtain ⟨hS4, hroom, htop4, hsp4, hsz4⟩ := spnPushW_okC hS3 (push_of_callW h4)
  obtain ⟨rb, m5, h5, c'⟩ := ntBW_some c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
  have ht3 : rdW (m3.arr64 CTL) 136 = co + cn := htop3.trans (htop2.trans htop)
  have hs3 : m3.arr64 SPN = m.arr64 SPN := hspn3.trans hspn2
  rw [ht3] at hroom htop4 hsp4
  rw [hs3, hcc] at hroom
  have hsl4 : SpineR m4 co (cn + 1) (acc.push (decE (rf.headD 0))) :=
    SpineR.push' (hsl.of_spn hs3) hlt3 hsz4 (by rw [hs3]; exact hroom) (by rw [hs3]; omega) hsp4
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hcn1 : (cn + 1).toNat = cn.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨x5, a5, M5, hrun5, hS5, hK5, hsz5, hkb5, hO, hacc⟩ := ih m4 m5 a3 M2 (n - 1) _ (i + 1) co (cn + 1) _ rb h5
    hS4 hy hsl4 (by rw [htop4]; grind) (by rw [hsz4, hs3, hi1, hcn1]; omega)
  have hrun := opfGo_run_step acc (n - 1).toNat (decE e) i.toNat a a2 a3 a5 _ _ _ _ x5
    (by rw [decE_tag_forallE_beq e he]; simpa using hg6) hview hrun2 hrun3 (by rw [← hi1]; exact hrun5)
  rw [hn1] at hrun
  have hsz : (m5.arr64 SPN).size = (m.arr64 SPN).size := by rw [hsz5, hsz4, hs3]
  have hcc1 : (co + (cn + 1)).toNat = co.toNat + cn.toNat + 1 := by
    rw [L.toNat_add_of_lt _ _ (by rw [hcn1]; omega), hcn1]; omega
  refine ⟨_, _, M5, hrun, hS5, hK2.trans hK5, hsz, fun w hw => ?_, ?_, ?_⟩
  · rw [hcc] at hw
    rw [hkb5 w (by rw [hcc1]; omega), hsp4, ite_eq_right (fun h => by subst h; omega)]
    simp only [spW, hs3]
  rotate_left
  · intro p hp
    cases x5 with
    | none => cases hp
    | some q =>
      cases hp
      have := hacc q rfl
      rw [this]; apply Array.ext'; simp
  rw [show co + (cn + 1) = co + cn + 1 by grind] at hO
  have hmap : rawFR (x5.map (fun p => (decE (rf.headD 0) :: p.1, p.2))) =
      (rawFR x5).map (fun p => (decE (rf.headD 0) :: p.1, p.2)) := by cases x5 <;> rfl
  rw [hmap]
  exact OGo.step hn hO (by rw [hsp4]; simp) hlt3 (by rw [hsz]; omega) (by rw [hsz, hcc]; omega)
    (fun w hw => by
      rw [hsp4, ite_eq_right (fun h => by subst h; omega)]
      simp only [spW, hs3])

/-- `open_pis_at_fvars_f`'s model from a call in a program with `opfP`. -/
theorem callW_opfF {p : Prog} (hOpf : OpfF p) {n : Nat} {args r : List Word} {m m' : Mem}
    (h : callW p n "open_pis_at_fvars_f" args m = some (r, m')) : opfF m args = some (r, m') := by
  obtain ⟨s', hs, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (opfF_spec p hOpf n _ args) h
  rw [← hs]; exact hW

end

end L.Ind
