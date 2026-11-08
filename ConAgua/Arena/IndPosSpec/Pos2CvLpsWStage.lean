module

public import ConAgua.Arena.IndPosSpec.CtxFields
public import ConAgua.Arena.IndPosSpec.MkLook
public import ConAgua.Arena.IndPosSpec.PiBWStage
public import ConAgua.Arena.RecCheckSpec.ErToIwWStage
public import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.RecClassSpec.CloseLams

@[expose] public section

/-!
# Pos2CvLpsWStage

`pos2_cvLpsW_stage`, `nhGoW`, `nhK1`, `nhK2`, `nhK3`, `nhK4` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem pos2_cvLpsW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : cvLpsW n m q = some (r, m')) (hS : StageR vis fe m a)
    (hcv : decCVp m q.toNat = some cv) (hq : q.toNat + 3 < 2 ^ 64) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  sorry
/- ronsync2 stage 2: commented out (statement at the old twin/L)
def nhGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, mm, off, l, oo, ol =>
    if l = 0 then some ([1, oo, ol], m)
    else nhK1 k vis ctx mm off l oo ol (envFindW m (rdW (m.arr64 IW) off) vis)
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
def nhK1 (k : Nat) (vis ctx mm off l oo ol : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0], m1)
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then some ([0, 0, 0], m1)
    else nhK2 k vis ctx mm off l oo ol (instW k m1 (rdW (m1.arr64 IW) (ctx + 7)) (rdW (m1.arr64 IW) (ctx + 8))
      (rdW (m1.arr64 EREC) (r.tail.headD 0 + 4)))
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
def nhK2 (k : Nat) (vis ctx mm off l oo ol : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else nhK3 k vis ctx mm off l oo ol (fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0))
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
def nhK3 (k : Nat) (vis ctx mm off l oo ol : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (v, m3) => if 4294967296 ≤ v then none else nhK4 k vis ctx mm off l (snocW k m3 oo ol v)
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
def nhK4 (k : Nat) (vis ctx mm off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => nhGoW k m4 vis ctx (mm + 1) (off + 1) (l - 1) (r4.headD 0) (r4.tail.headD 0)
end
-/

section arms
variable (k : Nat) (m m1 m2 m3 m4 : Mem) (vis ctx mm off l oo ol v : Word) (r r2 r4 : List Word)
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhGoW_nil (h : l = 0) : nhGoW (k + 1) m vis ctx mm off l oo ol = some ([1, oo, ol], m) := by
  simp [nhGoW, h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhGoW_cons (h : ¬ l = 0) : nhGoW (k + 1) m vis ctx mm off l oo ol =
    nhK1 k vis ctx mm off l oo ol (envFindW m (rdW (m.arr64 IW) off) vis) := by simp [nhGoW, h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhK1_miss (h : r.headD 0 = 0) : nhK1 k vis ctx mm off l oo ol (some (r, m1)) = some ([0, 0, 0], m1) := by
  rw [nhK1, ite_eq_left h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhK1_noind (h : ¬ r.headD 0 = 0) (h3 : rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    nhK1 k vis ctx mm off l oo ol (some (r, m1)) = some ([0, 0, 0], m1) := by rw [nhK1, ite_eq_right h, ite_eq_left h3]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhK1_ind (h : ¬ r.headD 0 = 0) (h3 : ¬ rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    nhK1 k vis ctx mm off l oo ol (some (r, m1)) =
      nhK2 k vis ctx mm off l oo ol (instW k m1 (rdW (m1.arr64 IW) (ctx + 7)) (rdW (m1.arr64 IW) (ctx + 8))
        (rdW (m1.arr64 EREC) (r.tail.headD 0 + 4))) := by
  sorry
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhK2_none (h : r2.headD 0 = 0) : nhK2 k vis ctx mm off l oo ol (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [nhK2, ite_eq_left h]
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhK2_some (h : ¬ r2.headD 0 = 0) : nhK2 k vis ctx mm off l oo ol (some (r2, m2)) =
    nhK3 k vis ctx mm off l oo ol (fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0)) := by
  sorry
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhK3_ok (h : ¬ 4294967296 ≤ v) : nhK3 k vis ctx mm off l oo ol (some (v, m3)) =
    nhK4 k vis ctx mm off l (snocW k m3 oo ol v) := by
  sorry
-/
/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem nhK4_some : nhK4 k vis ctx mm off l (some (r4, m4)) =
    nhGoW k m4 vis ctx (mm + 1) (off + 1) (l - 1) (r4.headD 0) (r4.tail.headD 0) := by rw [nhK4]
-/
end arms
attribute [ind_grind] nhGoW_nil nhGoW_cons nhK1_miss nhK1_noind nhK1_ind nhK2_none nhK2_some nhK3_ok nhK4_some

/-- The lookups of `nest_holes`. -/
structure NhLook (p : Prog) : Prop where
  hi1 : I1Prog p
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hsn : p.lookup "sl_snoc" = some slSnoc
  hv : p.lookup "e_view" = some eView
  hip : p.lookup "inst_pis_with" = some instPisWith
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hff : p.lookup "fvar_find" = some fvarFind
  hfp : p.lookup "fvar_push" = some fvarPush
  hif : p.lookup "intern_fvar" = some internFVar
  hgo : p.lookup "nest_holes_go" = some nestHolesGoL
  hp : p.lookup "nest_holes" = some nestHolesL

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The model of `nest_holes(vis, ctx)` at exec fuel `k + 1`. -/
def nhW (k : Nat) (m : Mem) (vis ctx : Word) : Option (List Word × Mem) :=
  nhGoW k m vis ctx 0 (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) 0 0
-/

/-- A `NestCtx` record's slices end below the pool's top (`CtxIn` covers their words, this their
offsets when empty too). -/
def CtxSl (m : Mem) (p : Nat) : Prop :=
  ∀ i, (i = 0 ∨ i = 2 ∨ i = 5 ∨ i = 7) → ∀ o l, iwN m (p + i) = some o → iwN m (p + i + 1) = some l →
    o + l ≤ iwTop m

/-- `nest_holes`'s results: `(0, …)` or `(1, off, len)`, a handle slice below the top. -/
def NhOut (m : Mem) (r : List Word) : Option (List EIdx) → Prop
  | none => r.headD 0 = 0
  | some l => r.headD 0 = 1 ∧ decHL m (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some l ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m

/-! ## `nest_root_canon` refines `nestRootCanon` -/

/-- The lookups of `nest_canon_crest`. -/
structure PccLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hl : AhLook p
  hk : MkLook p
  hng : p.lookup "nest_phs_go" = some nestPhsGo
  hnp : p.lookup "nest_phs" = some nestPhs
  hip : p.lookup "inst_pis_with" = some instPisWith
  hf : p.lookup "ra_find" = some (memoFindG raSch)
  hput : p.lookup "ra_put" = some (memoPutG raSch)
  hgo : p.lookup "replace_apps_go" = some replaceAppsGo
  hnode : p.lookup "replace_apps_node" = some replaceAppsNode
  hcl : p.lookup "ra_clear" = some (memoClearG raSch)
  hra : p.lookup "replace_apps" = some replaceApps
  hp : p.lookup "nest_canon_crest" = some nestCanonCrest
  hp' : p.lookup "nest_root_canon" = some nestRootCanonL

/-- The names slice's end, as the words L reads. -/
theorem ctx_names_end {m : Mem} {p : Word} {c : NestCtx} (hc : decCtx m p.toNat = some c)
    (hin : CtxIn m p.toNat (· < iwTop m)) (hsl : CtxSl m p.toNat) (hsz : iwTop m < 2 ^ 64) :
    (rdW (m.arr64 IW) p).toNat + (rdW (m.arr64 IW) (p + 1)).toNat ≤ iwTop m := by
  obtain ⟨hn, -⟩ := decCtx_some hc
  obtain ⟨o, l, ho, hl, -⟩ := decAt_some hn
  have h11 := hin.1 10 (by omega)
  have r0 : (rdW (m.arr64 IW) p).toNat = o := by
    have := rd_iwN (m := m) (p := p) (i := 0) (by simpa using ho) (by simp; omega); simpa using this
  have r1 : (rdW (m.arr64 IW) (p + 1)).toNat = l := rd_iwN (by simpa using hl) (by simp; omega)
  rw [r0, r1]; exact hsl 0 (by omega) o l (by simpa using ho) hl

/-- The lookups of `nest_uniform_ok`. -/
structure NuLook (p : Prog) : Prop where
  pcc : PccLook p
  no : NoLook p
  hc : p.lookup "er_copy" = some erCopy
  he : p.lookup "er_to_iw" = some erToIw
  hcv : p.lookup "cv_lps" = some cvLps
  hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  hpd : p.lookup "pi_doms_occ" = some piDomsOccL
  hp : p.lookup "nest_uniform_ok" = some nestUniformOkL

end L.Ind

end
