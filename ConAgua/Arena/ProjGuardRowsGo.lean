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

l_model pgraW_spec (p : Prog) (hf : p.lookup "proj_guard_rows_at" = some projGuardRowsAtL)
  fns [hf ↦ pgraW list]
  specs [callW_spec p n "proj_guard_fast", callW_spec p n "inst_list", callW_spec p n "proj_guard_row",
    callW_spec p n "proj_guard_rows_go"]
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

/-- What the guard's row functions need of a program. -/
structure PgGoProg (p : Prog) : Prop where
  go : p.lookup "proj_guard_rows_go" = some projGuardRowsGoL
  row : p.lookup "proj_guard_row" = some projGuardRowL
  fast : p.lookup "proj_guard_fast" = some projGuardFastL
  hl : HlF p
  opf : OpfF p

/-- The rows' words against the twin's answer, at `ro` on the stack. -/
def PgGoRes (ro : Word) (m : Mem) (r : List Word) : Option (Array (Nat × EIdx)) → Prop
  | none => r.headD 0 = 0
  | some rows => r.headD 0 = 1 ∧ rows.size = (r.tail.headD 0).toNat ∧ RowsAt m ro rows ∧
      ro.toNat + 2 * rows.size ≤ (spTop m).toNat

theorem callW_opfP {p : Prog} (hO : OpfF p) {n : Nat} {f : FnName} (hf : f ∈ opfPFns := by decide)
    {vs : List Word} {m : Mem} : callW p n f vs m = callW opfP n f vs m :=
  callW_agree opfP_closed (hO.agree opfPFns) n hf vs m

/-- **`proj_guard_rows_go` refines `projGuardRowsGo` under `CoreS`**: the rows `out` at `ro` on
the stack, the top just past them; the rows after at `ro`, the stack below the old top kept. -/
theorem pgGo_okC {p : Prog} (hP : PgGoProg p) : ∀ (n : Nat) (m m' : Mem) (a : AState) (M : ModeMaps)
    (k d h ro rn : Word) (out : Array (Nat × EIdx)) (r : List Word),
    callW p n "proj_guard_rows_go" [k, d, h, ro, rn] m = some (r, m') →
    CoreS dn m a vis fe M eb → HW h → RowsAt m ro out → out.size = rn.toNat →
    (spTop m).toNat = ro.toNat + 2 * rn.toNat → (spTop m).toNat ≤ (m.arr64 SPN).size →
    d.toNat + k.toNat < 2 ^ 64 →
    ∃ y a' M', (projGuardRowsGo k.toNat d.toNat (decE h) out).run a = .ok (y, a') ∧
      CoreS dn m' a' vis fe M' eb ∧ KeptAll M M' eb ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
      (spTop m).toNat ≤ (spTop m').toNat ∧
      (∀ w : Word, w.toNat < (spTop m).toNat → spW m' w = spW m w) ∧ PgGoRes ro m' r y := by
  intro n
  induction n with
  | zero => intro m m' a M k d h ro rn out r hc; rw [callW_zero] at hc; cases hc
  | succ n ih =>
  intro m m' a M k d h ro rn out r hc hS hh hrows hsz htop htb hdk
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pgGoW_spec p hP.go (n + 1) _ k d h ro rn) hc
  rw [hs'] at hW
  clear hc hs'
  have hsp := hS.spn
  simp only [pgGoW] at hW
  by_cases hg : tagW h ≠ 6
  · rw [ite_eq_left hg] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨none, a, M, pgGo_run_nf _ _ _ _ a (by rw [decE_tag_forallE_beq h hh]; simpa using hg),
      hS, KeptAll.refl _ _, rfl, Nat.le_refl _, fun _ _ => rfl, rfl⟩
  rw [ite_eq_right hg] at hW
  have hg6 : tagW h = 6 := Decidable.not_not.mp hg
  have htag : ((decE h).tag == ETag.forallE) = true := by rw [decE_tag_forallE_beq h hh]; simpa using hg6
  rcases c1 : callW p n "e_view" [h] m with _ | ⟨r1, m1⟩
  · rw [c1] at hW; cases hW
  rw [c1] at hW
  simp only [pgGoW.k_e_view] at hW
  rw [callW_opfP hP.opf] at c1
  obtain ⟨rfl, hx, hy, hview⟩ := opfV_okC hS hg6 c1
  generalize r1.tail.headD 0 = x at hW hx hview
  generalize r1.tail.tail.headD 0 = y at hW hy hview
  by_cases hk : k = 0
  · -- the projected field: its domain the last row
    subst hk
    rw [ite_eq_left rfl] at hW
    rcases c2 : callW p n "proj_guard_row" [ro, rn, d, x] m1 with _ | ⟨r2, m2⟩
    · rw [c2] at hW; cases hW
    rw [c2] at hW
    simp only [pgGoW.k_proj_guard_row] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (pgRowW_spec p hP.row n _ ro rn d x) c2
    rw [hs2] at hW2
    obtain ⟨hS2, rfl, -, htop2, hsz2, hb2, h1, h2, hk2⟩ := pgRow_okC hS (by omega) hW2
    have hrn : (rn + 1).toNat = rn.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    refine ⟨_, _, M, pgGo_run_zero _ _ _ _ _ a htag hview, hS2, KeptAll.refl _ _, hsz2,
      by omega, fun w hw => hk2 w (by omega), rfl, ?_, ?_, ?_⟩
    · simp [hrn, hsz]
    · exact RowsAt.push hrows hsz (by omega) h1 h2 hx hk2
    · simp only [Array.size_push]; omega
  rw [ite_eq_right hk] at hW
  have hk1 := wsub1 hk
  have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rcases c2 : callW p n "has_loose_b_var_b_fast" [0, y] m1 with _ | ⟨r2, m2⟩
  · rw [c2] at hW; cases hW
  rw [c2] at hW
  simp only [pgGoW.k_has_loose_b_var_b_fast] at hW
  obtain ⟨b, a1, hrun1, hb, -, hS2, hK2, -, -, -⟩ := hbFast_okC hP.hl n hy hS hS.iw hS.memos.hb c2
  have hrows2 : RowsAt m2 ro out :=
    RowsAt.keepB hrows (by omega) fun w hw => hK2.below w (by rw [UInt64.lt_iff_toNat_lt]; omega)
  have htop2 : spTop m2 = spTop m1 := hK2.top
  cases b with
  | false =>
    rw [ite_eq_right (by rw [hb]; simp)] at hW
    simp only [pgGoW.k_proj_guard_rows_go] at hW
    rcases c3 : callW p n "proj_guard_rows_go" [k - 1, d + 1, y, ro, rn] m2 with _ | ⟨r3, m3⟩
    · rw [c3] at hW; cases hW
    rw [c3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨z, a3, M3, hrun3, hS3, hK3, hsz3, ht3, hb3, hres3⟩ := ih m2 _ a1 M (k - 1) (d + 1) y ro rn out _
      c3 hS2 hy hrows2 hsz (by rw [htop2]; omega) (by rw [htop2, hK2.size]; omega) (by omega)
    refine ⟨z, a3, M3, ?_, hS3, hK3, by rw [hsz3, hK2.size], by rw [← htop2]; exact ht3,
      fun w hw => by rw [hb3 w (by rw [htop2]; exact hw), hK2.below w (by rw [UInt64.lt_iff_toNat_lt]; omega)],
      by cases z <;> exact hres3⟩
    rw [← hk1]
    exact pgGo_run_unused _ _ _ _ _ _ a a1 a3 z htag hview hrun1 (by rw [← hd1]; exact hrun3)
  | true =>
    rw [ite_eq_left (by rw [hb]; simp)] at hW
    rcases c3 : callW p n "intern_fvar" [d, x] m2 with _ | ⟨r3, m3⟩
    · rw [c3] at hW; cases hW
    rw [c3] at hW
    simp only [pgGoW.k_intern_fvar] at hW
    rw [callW_opfP hP.opf] at c3
    obtain ⟨a2, hrun2, hS3, hspn3, htop3, hfv⟩ := opfFv_okC hS2 hx c3
    rw [ite_eq_right (show ¬ (4294967296 : Word) ≤ r3.headD 0 from fun h => by
      rw [UInt64.le_iff_toNat_le] at h; have : (4294967296 : Word).toNat = 4294967296 := rfl; omega)] at hW
    rcases c4 : callW p n "inst_entry" [y, r3.headD 0, 0] m3 with _ | ⟨r4, m4⟩
    · rw [c4] at hW; cases hW
    rw [c4] at hW
    simp only [pgGoW.k_inst_entry] at hW
    rw [callW_opfP hP.opf] at c4
    obtain ⟨a3, M3, hrun3, hS4, hK4, hspn4, htop4, hb2⟩ := opfI1_okC hS3 hy c4
    have hsp4 : ∀ w, spW m4 w = spW m2 w := fun w => by simp only [spW, hspn4, hspn3]
    have ht4 : spTop m4 = spTop m1 := by simp only [spTop, htop4, htop3]; exact htop2
    rcases c5 : callW p n "proj_guard_row" [ro, rn, d, x] m4 with _ | ⟨r5, m5⟩
    · rw [c5] at hW; cases hW
    rw [c5] at hW
    simp only [pgGoW.k_proj_guard_row_2] at hW
    obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
      (pgRowW_spec p hP.row n _ ro rn d x) c5
    rw [hs5] at hW5
    have hsz4 : (m4.arr64 SPN).size = (m1.arr64 SPN).size := by rw [hspn4, hspn3, hK2.size]
    obtain ⟨hS5, rfl, -, htop5, hsz5, hb5, h1, h2, hk5⟩ := pgRow_okC hS4 (by omega) hW5
    simp only [List.headD_cons] at hW
    rcases c6 : callW p n "proj_guard_rows_go" [k - 1, d + 1, r4.headD 0, ro, rn + 1] m5 with _ | ⟨r6, m6⟩
    · rw [c6] at hW; cases hW
    rw [c6] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hrows4 : RowsAt m4 ro out := RowsAt.keepB hrows2 (by omega) fun w _ => hsp4 w
    have hrn : (rn + 1).toNat = rn.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hrows5 := RowsAt.push hrows4 hsz (by omega) h1 h2 hx hk5
    obtain ⟨z, a6, M6, hrun6, hS6, hK6, hsz6, ht6, hb6, hres6⟩ := ih m5 _ a3 M3 (k - 1) (d + 1) _ ro (rn + 1)
      _ _ c6 hS5 hb2 hrows5 (by simp [hsz, hrn]) (by rw [htop5, hrn]; omega) (by rw [htop5, hsz5]; omega)
      (by omega)
    refine ⟨z, a6, M6, ?_, hS6, hK4.trans hK6, by rw [hsz6, hsz5, hsz4], by omega, fun w hw => ?_,
      by cases z <;> exact hres6⟩
    · rw [← hk1]
      exact pgGo_run_used _ _ _ _ _ _ _ _ a a1 a2 a3 a6 z htag hview hrun1 hrun2 hrun3
        (by rw [← hd1]; exact hrun6)
    · rw [hb6 w (by omega), hk5 w (by omega), hsp4 w, hK2.below w (by rw [UInt64.lt_iff_toNat_lt]; omega)]

/-- The fast case's words against the twin's answer. -/
def PgFastRes (r : List Word) : Option EIdx → Prop
  | none => r.headD 0 = 0
  | some dom => r.headD 0 = 1 ∧ HW (r.tail.headD 0) ∧ decE (r.tail.headD 0) = dom

/-- **`proj_guard_fast` refines `projGuardFast` under `CoreS`** (the window queries read only). -/
theorem pgFast_okC {p : Prog} (hP : PgGoProg p) : ∀ (n : Nat) (m m' : Mem) (a : AState) (M : ModeMaps)
    (k j h : Word) (r : List Word), callW p n "proj_guard_fast" [k, j, h] m = some (r, m') →
    CoreS dn m a vis fe M eb → HW h → j.toNat + k.toNat < 2 ^ 64 →
    ∃ y a', (projGuardFast k.toNat j.toNat (decE h)).run a = .ok (y, a') ∧
      CoreS dn m' a' vis fe M eb ∧ StackKept m m' ∧ PgFastRes r y := by
  intro n
  induction n with
  | zero => intro m m' a M k j h r hc; rw [callW_zero] at hc; cases hc
  | succ n ih =>
  intro m m' a M k j h r hc hS hh hjk
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pgFastW_spec p hP.fast (n + 1) _ k j h) hc
  rw [hs'] at hW
  clear hc hs'
  simp only [pgFastW] at hW
  by_cases hg : tagW h ≠ 6
  · rw [ite_eq_left hg] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨none, a, pgFast_run_nf _ _ _ a (by rw [decE_tag_forallE_beq h hh]; simpa using hg),
      hS, StackKept.refl _, rfl⟩
  rw [ite_eq_right hg] at hW
  have hg6 : tagW h = 6 := Decidable.not_not.mp hg
  have htag : ((decE h).tag == ETag.forallE) = true := by rw [decE_tag_forallE_beq h hh]; simpa using hg6
  rcases c1 : callW p n "e_view" [h] m with _ | ⟨r1, m1⟩
  · rw [c1] at hW; cases hW
  rw [c1] at hW
  simp only [pgFastW.k_e_view] at hW
  rw [callW_opfP hP.opf] at c1
  obtain ⟨rfl, hx, hy, hview⟩ := opfV_okC hS hg6 c1
  generalize r1.tail.headD 0 = x at hW hx hview
  generalize r1.tail.tail.headD 0 = y at hW hy hview
  by_cases hk : k = 0
  · subst hk
    rw [ite_eq_left rfl] at hW
    rcases c2 : callW p n "has_loose_bvar_in" [0, j, h] m1 with _ | ⟨r2, m2⟩
    · rw [c2] at hW; cases hW
    rw [c2] at hW
    simp only [pgFastW.k_has_loose_bvar_in] at hW
    obtain ⟨b, a1, hrun1, hb, -, hS2, hK2, -, -, -⟩ := hlbi_okC hP.hl n hh hS hS.iw hS.memos.hb c2
    have hrun := pgFast_run_zero _ _ _ _ a a1 b htag hview hrun1
    cases b with
    | true =>
      rw [ite_eq_left (by rw [hb]; simp)] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      exact ⟨none, a1, hrun, hS2, hK2, rfl⟩
    | false =>
      rw [ite_eq_right (by rw [hb]; simp)] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      exact ⟨some _, a1, hrun, hS2, hK2, rfl, hx, rfl⟩
  rw [ite_eq_right hk] at hW
  have hk1 := wsub1 hk
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rcases c2 : callW p n "has_loose_bvar_in" [0, j, x] m1 with _ | ⟨r2, m2⟩
  · rw [c2] at hW; cases hW
  rw [c2] at hW
  simp only [pgFastW.k_has_loose_bvar_in_2] at hW
  obtain ⟨b, a1, hrun1, hb, -, hS2, hK2, -, -, -⟩ := hlbi_okC hP.hl n hx hS hS.iw hS.memos.hb c2
  have hrun := pgFast_run_succ (k - 1).toNat _ _ _ _ a a1 b htag hview hrun1
  rw [hk1] at hrun
  cases b with
  | true =>
    rw [ite_eq_left (by rw [hb]; simp)] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨none, a1, hrun, hS2, hK2, rfl⟩
  | false =>
    rw [ite_eq_right (by rw [hb]; simp)] at hW
    rw [hrun, if_neg (by decide)]
    rcases c3 : callW p n "proj_guard_fast" [k - 1, j + 1, y] m2 with _ | ⟨r3, m3⟩
    · rw [c3] at hW; cases hW
    rw [c3] at hW
    simp only [pgFastW.k_proj_guard_fast] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨z, a3, hrun3, hS3, hK3, hres⟩ := ih m2 _ a1 M (k - 1) (j + 1) y _ c3 hS2 hy (by omega)
    refine ⟨z, a3, by rw [← hj1]; exact hrun3, hS3, hK2.trans hK3, ?_⟩
    cases z <;> simpa [PgFastRes] using hres

/-- What `proj_guard_rows_at`'s refinement needs of a program. -/
structure PgraProg (p : Prog) : Prop extends PgGoProg p where
  at' : p.lookup "proj_guard_rows_at" = some projGuardRowsAtL

theorem RowsAt.empty (m : Mem) (ro : Word) : RowsAt m ro #[] := fun _ h => absurd h (by simp)

/-- **`proj_guard_rows_at` refines `projGuardRowsAt` under `CoreS`**: the substitution `acc` the
stack slice `(co, np)` below the top `ro`; the rows at `ro`. -/
theorem pgra_okC {p : Prog} (hP : PgraProg p) (n : Nat) {m m' : Mem} {a : AState} {M : ModeMaps}
    {i co np r ro : Word} {acc : Array EIdx} {rr : List Word} (e : IProjEntry) (he : e.idx = i.toNat)
    (hnp : e.numParams = np.toNat)
    (hc : callW p n "proj_guard_rows_at" [i, co, np, r, ro] m = some (rr, m'))
    (hS : CoreS dn m a vis fe M eb) (hr : HW r) (hsl : SpineR m co np acc)
    (hco : co.toNat + np.toNat ≤ (spTop m).toNat) (hro : spTop m = ro)
    (htb : (spTop m).toNat ≤ (m.arr64 SPN).size) :
    ∃ y a' M', (projGuardRowsAt e acc (decE r)).run a = .ok (y, a') ∧
      CoreS dn m' a' vis fe M' eb ∧ KeptAll M M' eb ∧ (m'.arr64 SPN).size = (m.arr64 SPN).size ∧
      (spTop m).toNat ≤ (spTop m').toNat ∧
      (∀ w : Word, w.toNat < (spTop m).toNat → spW m' w = spW m w) ∧ PgGoRes ro m' rr y := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (pgraW_spec p hP.at' n _ i co np r ro) hc
  rw [hs'] at hW
  clear hc hs'
  rcases n with _ | n
  · cases hW
  have hsp := hS.spn
  simp only [pgraW] at hW
  by_cases gw : np + i < np
  · rw [ite_eq_left gw] at hW; cases hW
  rw [ite_eq_right gw] at hW
  have hni : np.toNat + i.toNat < 2 ^ 64 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at gw
    have := np.toNat_lt; have := i.toNat_lt
    rcases Nat.lt_or_ge (np.toNat + i.toNat) (2 ^ 64) with hh | hh
    · exact hh
    · exfalso
      rw [Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega)] at gw
      omega
  have hni' : (np + i).toNat = np.toNat + i.toNat := by rw [UInt64.toNat_add]; omega
  rcases c1 : callW p n "proj_guard_fast" [i, 0, r] m with _ | ⟨r1, m1⟩
  · rw [c1] at hW; cases hW
  rw [c1] at hW
  simp only [pgraW.k_proj_guard_fast] at hW
  obtain ⟨y1, a1, hrun1, hS1, hK1, hres1⟩ := pgFast_okC hP.toPgGoProg n m m1 a M i 0 r r1 c1 hS hr
    (by simp; omega)
  have hsl1 : SpineR m1 co np acc := hsl.keep hK1.size hK1.below hco hsp
  have ht1 : spTop m1 = spTop m := hK1.top
  cases y1 with
  | some dom =>
    obtain ⟨g1, hdw, hdom⟩ := hres1
    rw [ite_eq_left (by rw [g1]; decide)] at hW
    rcases c2 : callW p n "inst_list" [r1.tail.headD 0, co, np, i] m1 with _ | ⟨r2, m2⟩
    · rw [c2] at hW; cases hW
    rw [c2] at hW
    simp only [pgraW.k_inst_list] at hW
    rw [callW_opfP hP.opf] at c2
    obtain ⟨a2, M2, hrun2, hS2, hK2, hspn2, htop2, hd2⟩ := opfIl_okC hS1 hsl1 (by rw [ht1]; exact hco) hdw c2
    rcases c3 : callW p n "proj_guard_row" [ro, 0, np + i, r2.headD 0] m2 with _ | ⟨r3, m3⟩
    · rw [c3] at hW; cases hW
    rw [c3] at hW
    simp only [pgraW.k_proj_guard_row] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (pgRowW_spec p hP.row n _ ro 0 (np + i) (r2.headD 0)) c3
    rw [hs3] at hW3
    have ht2 : spTop m2 = ro := by simp only [spTop] at ht1 hro ⊢; rw [htop2, ht1, hro]
    have hsz2 : (m2.arr64 SPN).size = (m.arr64 SPN).size := by rw [hspn2, hK1.size]
    have hsp2 : ∀ w, spW m2 w = spW m1 w := fun w => by simp only [spW, hspn2]
    obtain ⟨hS3, rfl, -, htop3, hsz3, hb3, h1, h2, hk3⟩ := pgRow_okC hS2 (by simp; rw [← hro] at *; omega) hW3
    have hrows := RowsAt.push (RowsAt.empty m2 ro) (rn := 0) rfl (by simp; rw [← hro]; omega) h1 h2 hd2 hk3
    refine ⟨some ((#[] : Array (Nat × EIdx)).push (e.numParams + e.idx, decE (r2.headD 0))), _, M2, ?_, hS3,
      hK2, by rw [hsz3, hsz2], by rw [htop3]; rw [← hro]; omega,
      fun w hw => by rw [hk3 w (by simp; rw [← hro]; exact hw), hsp2, hK1.below w (by rw [UInt64.lt_iff_toNat_lt]; exact hw)],
      rfl, by simp, ?_, by simp [htop3]⟩
    · simp only [UInt64.toNat_zero, ← he] at hrun1
      rw [hdom, ← he] at hrun2
      simp only [projGuardRowsAt, StateT.run_bind, hrun1, except_ok_bind, hrun2]
      rfl
    · rw [hni', ← hnp, ← he] at hrows; exact hrows
  | none =>
    have g1 : r1.headD 0 = 0 := hres1
    rw [ite_eq_right (by rw [g1]; decide)] at hW
    rcases c2 : callW p n "inst_list" [r, co, np, 0] m1 with _ | ⟨r2, m2⟩
    · rw [c2] at hW; cases hW
    rw [c2] at hW
    simp only [pgraW.k_inst_list_2] at hW
    rw [callW_opfP hP.opf] at c2
    obtain ⟨a2, M2, hrun2, hS2, hK2, hspn2, htop2, hd2⟩ := opfIl_okC hS1 hsl1 (by rw [ht1]; exact hco) hr c2
    rcases c3 : callW p n "proj_guard_rows_go" [i, np, r2.headD 0, ro, 0] m2 with _ | ⟨r3, m3⟩
    · rw [c3] at hW; cases hW
    rw [c3] at hW
    simp only [pgraW.k_proj_guard_rows_go] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have ht2 : spTop m2 = ro := by simp only [spTop] at ht1 hro ⊢; rw [htop2, ht1, hro]
    have hsz2 : (m2.arr64 SPN).size = (m.arr64 SPN).size := by rw [hspn2, hK1.size]
    have hsp2 : ∀ w, spW m2 w = spW m1 w := fun w => by simp only [spW, hspn2]
    obtain ⟨z, a3, M3, hrun3, hS3, hK3, hsz3, ht3, hb3, hres3⟩ := pgGo_okC hP.toPgGoProg n m2 m3 a2 M2
      i np _ ro 0 #[] r3 c3 hS2 hd2 (RowsAt.empty m2 ro) rfl (by rw [ht2]; simp)
      (by rw [ht2, hsz2, ← hro]; exact htb) (by omega)
    refine ⟨z, a3, M3, ?_, hS3, hK2.trans hK3, by rw [hsz3, hsz2], by rw [hro, ← ht2]; exact ht3,
      fun w hw => by rw [hb3 w (by rw [ht2, ← hro]; exact hw), hsp2, hK1.below w (by rw [UInt64.lt_iff_toNat_lt]; exact hw)],
      by cases z <;> simpa [PgGoRes] using hres3⟩
    simp only [UInt64.toNat_zero, ← he] at hrun1
    rw [← he, ← hnp] at hrun3
    simp only [projGuardRowsAt, StateT.run_bind, hrun1, except_ok_bind, UInt64.toNat_zero] at hrun2 ⊢
    rw [hrun2]
    simp only [except_ok_bind]
    exact hrun3

end

end L.Ind
