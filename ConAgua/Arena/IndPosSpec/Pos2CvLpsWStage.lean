module

public import ConAgua.Arena.IndPosSpec.CtxFields
public import ConAgua.Arena.IndPosSpec.MkLook
public import ConAgua.Arena.IndPosSpec.PiBWStage
public import ConAgua.Arena.RecCheckSpec.ErToIwWStage
public import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.FVarStore
import ConAgua.Arena.IndCopy2
import ConAgua.Arena.LdRd
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# Pos2CvLpsWStage

`pos2_cvLpsW_stage`, `nest_holes_go`'s generated model `nhGoW` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem pos2_cvLpsW_stage {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : cvLpsW n m q = some (r, m')) (hS : StageR vis fe m a)
    (hcv : decCVp m q.toNat = some cv) (hq : q.toNat + 3 < 2 ^ 64) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' :=
  cvLpsW_stage h hS hcv hq

/-- The lookups of `nest_holes`. -/
structure NhLook (p : Prog) : Prop where
  hi1 : I1Prog p
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hsn : p.lookup "sl_snoc" = some slSnoc
  hv : p.lookup "e_view" = some eView
  hip : p.lookup "inst_pis_with" = some instPisWith
  hff : p.lookup "fvar_find" = some fvarFind
  hfp : p.lookup "fvar_push" = some fvarPush
  hif : p.lookup "intern_fvar" = some internFVar
  hgo : p.lookup "nest_holes_go" = some nestHolesGoL
  hp : p.lookup "nest_holes" = some nestHolesL

/-- **`nest_holes_go`'s model `nhGoW`** (generated). -/
l_model nhGo_spec (p : Prog) (hl : NhLook p)
  fns [hl.hgo ↦ nhGoW list]
  specs [instPisWith_spec p hl.hv hl.hip hl.hi1 n, internFVar_spec p hl.hff hl.hfp hl.hif n,
    slSnoc_specW p hl.ha hl.hc hl.hsn n]
  grind [arena_grind] extra [ld64_rd_spec] finish [rdW_eq] gen 20

/-- The model of `nest_holes(ctx)` at exec fuel `k + 1`. -/
def nhW (k : Nat) (m : Mem) (ctx : Word) : Option (List Word × Mem) :=
  nhGoW k m ctx 0 (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) 0 0

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
