module

public import ConAgua.Arena.ProjGuardRowsOpf
public import ConAgua.Arena.ProjGuardHlbi
public import ConAgua.Arena.ProjGuardRef
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.Infer
import ConAgua.Arena.WhnfCoreRefine

@[expose] public section

/-!
# The projection guard's rows under `CoreS` (lane `ronsync3`)

`proj_guard_row`, `proj_guard_rows_go`, `proj_guard_fast` and `proj_guard_rows_at` refine the
twin's `projGuardRowsGo`, `projGuardFast`, `projGuardRowsAt` under the core tier's relation: their
generated word models, the callees by their `CoreS` refinements (`opfV_okC`, `opfIl_okC`,
`opfI1_okC`, `opfFv_okC`, `hlbi_okC`, `hbFast_okC`), the rows on the stack (`RowsAt`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model pgRowW_spec (p : Prog) (hf : p.lookup "proj_guard_row" = some projGuardRowL)
  fns [hf ↦ pgRowW list]
  grind [arena_grind]

l_model pgGoW_spec (p : Prog) (hf : p.lookup "proj_guard_rows_go" = some projGuardRowsGoL)
  fns [hf ↦ pgGoW list]
  specs [callW_spec p n "e_view", callW_spec p n "proj_guard_row", callW_spec p n "has_loose_b_var_b_fast",
    callW_spec p n "intern_fvar", callW_spec p n "inst_entry", callW_spec p n "proj_guard_rows_go"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model pgFastW_spec (p : Prog) (hf : p.lookup "proj_guard_fast" = some projGuardFastL)
  fns [hf ↦ pgFastW list]
  specs [callW_spec p n "e_view", callW_spec p n "has_loose_bvar_in", callW_spec p n "proj_guard_fast"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

end L.Arena

namespace L.Ind

open L.Arena

/-! ## The twin's steps -/

theorem pgGo_run_nf (k d : Nat) (h : EIdx) (out : Array (Nat × EIdx)) (a : AState)
    (htag : (h.tag == ETag.forallE) = false) :
    (projGuardRowsGo k d h out).run a = .ok (none, a) := by
  rw [projGuardRowsGo]; simp [htag]; rfl

theorem pgGo_run_zero (d : Nat) (h dom body : EIdx) (out : Array (Nat × EIdx)) (a : AState)
    (htag : (h.tag == ETag.forallE) = true) (hv : (view h).run a = .ok (.forallE dom body, a)) :
    (projGuardRowsGo 0 d h out).run a = .ok (some (out.push (d, dom)), a) := by
  rw [projGuardRowsGo]; simp [htag, StateT.run_bind, hv, except_ok_bind]; rfl

theorem pgGo_run_used (k d : Nat) (h dom body fv b2 : EIdx) (out : Array (Nat × EIdx))
    (a a1 a2 a3 a4 : AState) (x : Option (Array (Nat × EIdx)))
    (htag : (h.tag == ETag.forallE) = true) (hv : (view h).run a = .ok (.forallE dom body, a))
    (hb : (hasLooseBVarBFast 0 body).run a = .ok (true, a1))
    (hf : (internE (.fvar d dom)).run a1 = .ok (fv, a2))
    (hi : (instantiate1Fast coreWalkFuel body fv 0).run a2 = .ok (b2, a3))
    (hr : (projGuardRowsGo k (d + 1) b2 (out.push (d, dom))).run a3 = .ok (x, a4)) :
    (projGuardRowsGo (k + 1) d h out).run a = .ok (x, a4) := by
  rw [projGuardRowsGo]; simp [htag, StateT.run_bind, hv, except_ok_bind, hb, hf, hi, hr]

theorem pgGo_run_unused (k d : Nat) (h dom body : EIdx) (out : Array (Nat × EIdx))
    (a a1 a4 : AState) (x : Option (Array (Nat × EIdx)))
    (htag : (h.tag == ETag.forallE) = true) (hv : (view h).run a = .ok (.forallE dom body, a))
    (hb : (hasLooseBVarBFast 0 body).run a = .ok (false, a1))
    (hr : (projGuardRowsGo k (d + 1) body out).run a1 = .ok (x, a4)) :
    (projGuardRowsGo (k + 1) d h out).run a = .ok (x, a4) := by
  rw [projGuardRowsGo]; simp [htag, StateT.run_bind, hv, except_ok_bind, hb, hr]

theorem pgFast_run_nf (k j : Nat) (h : EIdx) (a : AState) (htag : (h.tag == ETag.forallE) = false) :
    (projGuardFast k j h).run a = .ok (none, a) := by
  rw [projGuardFast]; simp [htag]; rfl

theorem pgFast_run_zero (j : Nat) (h dom body : EIdx) (a a1 : AState) (b : Bool)
    (htag : (h.tag == ETag.forallE) = true) (hv : (view h).run a = .ok (.forallE dom body, a))
    (hb : (hasLooseBVarIn 0 j h).run a = .ok (b, a1)) :
    (projGuardFast 0 j h).run a = .ok (if b then none else some dom, a1) := by
  rw [projGuardFast]; cases b <;> simp [htag, StateT.run_bind, hv, except_ok_bind, hb] <;> rfl

theorem pgFast_run_succ (k j : Nat) (h dom body : EIdx) (a a1 : AState) (b : Bool)
    (htag : (h.tag == ETag.forallE) = true) (hv : (view h).run a = .ok (.forallE dom body, a))
    (hb : (hasLooseBVarIn 0 j dom).run a = .ok (b, a1)) :
    (projGuardFast (k + 1) j h).run a =
      if b then .ok (none, a1) else (projGuardFast k (j + 1) body).run a1 := by
  rw [projGuardFast]; cases b <;> simp [htag, StateT.run_bind, hv, except_ok_bind, hb] <;> rfl

/-! ## The rows on the stack -/

theorem RowsAt.keepB {m m' : Mem} {ro : Word} {rows : Array (Nat × EIdx)} (h : RowsAt m ro rows)
    (hb : ro.toNat + 2 * rows.size < 2 ^ 64)
    (hk : ∀ w : Word, w.toNat < ro.toNat + 2 * rows.size → spW m' w = spW m w) : RowsAt m' ro rows := by
  intro i hi
  have e1 : (ro + 2 * i).toNat = ro.toNat + 2 * i.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  have e2 : (ro + 2 * i + 1).toNat = ro.toNat + 2 * i.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  rw [hk _ (by omega), hk _ (by omega)]; exact h i hi

theorem RowsAt.push {m m' : Mem} {ro rn d e : Word} {rows : Array (Nat × EIdx)} (h : RowsAt m ro rows)
    (hs : rows.size = rn.toNat) (hb : ro.toNat + 2 * rn.toNat + 2 < 2 ^ 64)
    (h1 : spW m' (ro + 2 * rn) = d) (h2 : spW m' (ro + 2 * rn + 1) = e) (he : HW e)
    (hk : ∀ w : Word, w.toNat < ro.toNat + 2 * rn.toNat → spW m' w = spW m w) :
    RowsAt m' ro (rows.push (d.toNat, decE e)) := by
  intro i hi
  simp only [Array.size_push] at hi
  by_cases hlt : i.toNat < rows.size
  · have := (RowsAt.keepB h (by omega) (by rw [hs]; exact hk)) i hlt
    simp only [Array.getElem_push, hlt, ↓reduceDIte]; exact this
  · have hi' : i = rn := UInt64.toNat_inj.mp (by omega)
    subst hi'
    simp only [Array.getElem_push, hlt, ↓reduceDIte]
    exact ⟨by rw [h1], by rw [h2]; exact he, by rw [h2]⟩

section
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}

/-- **`proj_guard_row` under `CoreS`**: the two words at `ro + 2 rn`, the top past them. -/
theorem pgRow_okC {m m' : Mem} {a : AState} {M : ModeMaps} (hS : CoreS dn m a vis fe M eb)
    {ro rn d e : Word} {r : List Word} (hb : ro.toNat + 2 * rn.toNat ≤ (m.arr64 SPN).size)
    (h : pgRowW m ro rn d e = some (r, m')) :
    CoreS dn m' a vis fe M eb ∧ r = [rn + 1] ∧ MemFrame [SPN] [136] m m' ∧
      (spTop m').toNat = ro.toNat + 2 * rn.toNat + 2 ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
      ro.toNat + 2 * rn.toNat + 2 ≤ (m.arr64 SPN).size ∧
      spW m' (ro + 2 * rn) = d ∧ spW m' (ro + 2 * rn + 1) = e ∧
      (∀ w : Word, w.toNat < ro.toNat + 2 * rn.toNat → spW m' w = spW m w) := by
  have hsp := hS.spn
  have hc := hS.ctl136
  simp only [pgRowW] at h
  split at h
  · cases h
  rename_i hlt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have e0 : (ro + 2 * rn).toNat = ro.toNat + 2 * rn.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  have e1 : (ro + 2 * rn + 1).toNat = ro.toNat + 2 * rn.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  have e2 : (ro + 2 * rn + 2).toNat = ro.toNat + 2 * rn.toNat + 2 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  have hlt' : ro.toNat + 2 * rn.toNat + 1 < (m.arr64 SPN).size := by
    have : ¬ ((((m.arr64 SPN).size : Nat).toUInt64) ≤ ro + 2 * rn + 1) := hlt
    rw [UInt64.le_iff_toNat_le, e1] at this
    have h2 : (((m.arr64 SPN).size : Nat).toUInt64).toNat = (m.arr64 SPN).size % 2 ^ 64 := by
      simp [Nat.toUInt64]
    omega
  have hfr : MemFrame [SPN] [136] m
      (((m.set64 SPN (ro + 2 * rn) d).set64 SPN (ro + 2 * rn + 1) e).set64 CTL 136 (ro + 2 * rn + 2)) :=
    (((MemFrame.set64 m SPN (by decide) _ _).trans (MemFrame.set64 _ SPN (by decide) _ _)).mono
      (fun b hb => by simpa using hb) (by simp)).trans
      ((MemFrame.setCtl _ 136 _).mono (by simp) (fun c hc => hc))
  have hS' := hS.frame_stk hfr (by simp) (by simp)
  have hsz1 : ((m.set64 SPN (ro + 2 * rn) d).arr64 SPN).size = (m.arr64 SPN).size := by
    simp [Mem.arr64_set64_same]
  have hspW : ∀ w : Word, spW (((m.set64 SPN (ro + 2 * rn) d).set64 SPN (ro + 2 * rn + 1) e).set64 CTL 136
      (ro + 2 * rn + 2)) w = if w = ro + 2 * rn + 1 then e else if w = ro + 2 * rn then d else spW m w := by
    intro w
    simp only [spW]
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), L.Arena.rdW_set64, L.Arena.rdW_set64, hsz1]
    by_cases h1 : w = ro + 2 * rn + 1
    · subst h1; simp; omega
    · by_cases h0 : w = ro + 2 * rn
      · subst h0; simp [h1, Ne.symm h1]; omega
      · simp [h1, h0, Ne.symm h1, Ne.symm h0]
  refine ⟨hS', rfl, hfr, ?_, hfr.size SPN, by omega, ?_, ?_, ?_⟩
  · simp only [spTop]
    rw [L.Arena.rdW_set64, ite_eq_left ⟨rfl, rfl, by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; simp; omega⟩, e2]
  · rw [hspW, ite_eq_right (fun h => by have := congrArg UInt64.toNat h; omega), ite_eq_left rfl]
  · rw [hspW, ite_eq_left rfl]
  · intro w hw
    rw [hspW, ite_eq_right (fun h => by have := congrArg UInt64.toNat h; omega),
      ite_eq_right (fun h => by have := congrArg UInt64.toNat h; omega)]

end

end L.Ind
