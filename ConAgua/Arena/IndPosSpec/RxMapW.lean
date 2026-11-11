module

public import ConAgua.Arena.IndPosSpec.CtxFields
public import ConAgua.Arena.IndPosSpec.MkLook
public import ConAgua.Arena.IndRealSpine
import ConAgua.Arena.IndGrindAttr

@[expose] public section

/-!
# RxMapW

`hiW`, `kmW` (the total word models of `nest_ctx_hi_at`, `nest_key_map`), the lookups `RxLook`, the
banked memo's invariant and `FMOk`. The block's models are generated in `Rx`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Small callees as word models -/

/-- `nest_ctx_hi_at(ctx, nf)`. -/
def hiW (m : Mem) (ctx nf : Word) : Word :=
  rdW (m.arr64 IW) (ctx + 4) + rdW (m.arr64 IW) (ctx + 1) + nf

/-- `nest_key_map(dsOff, dsLen, hoOff, hoLen, i)`. -/
def kmW (m : Mem) (dO dL hO hL i : Word) : Word × Word :=
  if i < dL then (1, rdW (m.arr64 IW) (dO + i))
  else if i - dL < hL then (1, rdW (m.arr64 IW) (hO + (i - dL))) else (0, 0)

end L.Ind

namespace L.Ind

open L.Arena

/-- The lookups of the `replaceFVars` block. -/
structure RxLook (p : Prog) : Prop where
  ad : AdF p
  hl : AhLook p
  hk : MkLook p
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ci : p.lookup "intern_const" = some internConst
  ha : p.lookup "iw_alloc" = some iwAlloc
  h2 : p.lookup "rec2" = some rec2
  h4 : p.lookup "rec4" = some rec4
  h5 : p.lookup "rec5" = some rec5
  gd : p.lookup "sl_getd" = some slGetD
  hi : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  km : p.lookup "nest_key_map" = some nestKeyMap
  rff : p.lookup "rf_find" = some (memoFindG rfSch)
  rfp : p.lookup "rf_put" = some (memoPutG rfSch)
  rfe : p.lookup "rf_bank_enter" = some (bankEnterG 218)
  rfl' : p.lookup "rf_bank_leave" = some (bankLeaveG 218)
  rfc : p.lookup "rf_clear" = some (memoClearG rfSch)
  fma : p.lookup "fv_map_at" = some fvMapAt
  rt : p.lookup "nest_hole_img_root" = some nestHoleImgRoot
  dsg : p.lookup "nest_hole_img_ds_go" = some nestHoleImgDsGo
  ds : p.lookup "nest_hole_img_ds" = some nestHoleImgDs
  fr : p.lookup "nest_hole_img_frame" = some nestHoleImgFrame
  img : p.lookup "nest_hole_img" = some nestHoleImg
  nd : p.lookup "replace_fvars_node" = some replaceFVarsNode
  go : p.lookup "replace_fvars_go" = some replaceFVarsGo
  rf : p.lookup "replace_fvars" = some replaceFVars

end L.Ind

/-! ## The relational side: the banked memo's invariant -/

namespace L.Ind

open L.Arena

theorem rfK_h2 : ∀ k1 k2, bmKey.ok k1 k2 → k2.toNat < 2 ^ 32 := fun _ _ h => by rw [h.2]; decide

/-- The banked memo's keys: a handle and the generation. -/
def rfK : MemoKey (EIdx × Word) := genKey bmKey rfK_h2

/-- The word values denote handles. -/
def rfV (_ : Mem) (w : Word) (v : EIdx) : Prop := v = decE w

theorem rfSch_wf : rfSch.WF := ⟨by decide, by decide⟩

/-- **The banked memo's invariant**: the whole map `M`, the last generation `G`, the current `g`. -/
def RfInv (m : Mem) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) : Prop :=
  MemoRV rfSch rfK rfV m M ∧ BankW 218 m G g ∧ Fresh M G

/-- A writer that leaves the memo's array and its stamp and bank words alone. -/
def RfFr (m m' : Mem) : Prop :=
  ∃ (A : List TieredArray) (C : List Word), MemFrame A C m m' ∧ (RFM : TieredArray) ∉ A ∧ (208 : Word) ∉ C ∧
    (218 : Word) ∉ C ∧ (219 : Word) ∉ C

theorem RfInv.frame {m m' : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (h : RfInv m M G g)
    (hf : RfFr m m') : RfInv m' M G g := by
  obtain ⟨A, C, hfr, hA, hC, h218, h219⟩ := hf
  obtain ⟨hR, ⟨hB1, hB2, hgG, hGl, hsz⟩, hF⟩ := h
  refine ⟨memoRV_frame rfSch rfSch_wf rfK rfV A C hA hC m m' hfr (fun _ _ h => h) M hR,
    ⟨by rw [hfr.ctl 218 h218]; exact hB1, by rw [show (218 : Word) + 1 = 219 from rfl, hfr.ctl 219 h219]; exact hB2,
      hgG, hGl, by rw [hfr.size]; exact hsz⟩, hF⟩

theorem ceinternW_low {m m' : Mem} {f x r : Word} (h : ceinternW m f x = some (r, m')) : LowFr m m' := by
  exact ⟨_, _, (ceinternW_frame (hI := h)), by simp [tier1, CREC, CSLOT, CLP], by simp⟩

/-- The map at the generations up to `G` is unchanged, for a caller inside a bank (current
generation `g ≠ 0`); the outermost caller (`g = 0`) gets the memo cleared (`replace_fvars`'s
`rf_clear`, the twin's per-call map dropped). -/
def GKeep (M M' : Std.HashMap (EIdx × Word) EIdx) (G g : Word) : Prop :=
  g ≠ 0 → ∀ (k : EIdx) (gen : Word), gen ≤ G → M'[(k, gen)]? = M[(k, gen)]?

theorem GKeep.trans {M₁ M₂ M₃ : Std.HashMap (EIdx × Word) EIdx} {G G' g : Word} (h₁ : GKeep M₁ M₂ G g)
    (h₂ : GKeep M₂ M₃ G' g) (hG : G ≤ G') : GKeep M₁ M₃ G g :=
  fun hg0 k gen hg => (h₂ hg0 k gen (UInt64.le_trans hg hG)).trans (h₁ hg0 k gen hg)

/-- An optional handle as `(ok, e)`. -/
def OptE (r0 r1 : Word) : Option EIdx → Prop
  | none => r0 = 0
  | some e => r0 ≠ 0 ∧ decE r1 = e

end L.Ind

namespace L.Ind

open L.Arena

/-- **A `FvMap` record at `f`** (IndIface's layout `[tag, …]`), its reads below the top. -/
def FMOk (m : Mem) (f : Nat) : FvMap → Prop
  | .holeImg ctx prog n => iwN m f = some 0 ∧ f + 5 ≤ iwTop m ∧
      (∃ c, iwN m (f + 1) = some c ∧ decCtx m c = some ctx ∧ CtxIn m c (· < iwTop m)) ∧
      (∃ po pl, iwN m (f + 2) = some po ∧ iwN m (f + 3) = some pl ∧ HSl m po pl prog) ∧
      iwN m (f + 4) = some n ∧ ctx.nP + ctx.names.length + n < 2 ^ 64
  | .keyMap ds holes => iwN m f = some 1 ∧ f + 5 ≤ iwTop m ∧
      (∃ o l, iwN m (f + 1) = some o ∧ iwN m (f + 2) = some l ∧ decHL m o l = some ds ∧ o + l ≤ iwTop m) ∧
      (∃ o l, iwN m (f + 3) = some o ∧ iwN m (f + 4) = some l ∧ decHL m o l = some holes ∧ o + l ≤ iwTop m)
  | .erase => iwN m f = some 2 ∧ f + 1 ≤ iwTop m
  | .canon pfvs => iwN m f = some 3 ∧ f + 3 ≤ iwTop m ∧
      (∃ o l, iwN m (f + 1) = some o ∧ iwN m (f + 2) = some l ∧ decHL m o l = some pfvs ∧ o + l ≤ iwTop m)

end L.Ind

namespace L.Ind

open L.Arena

/-! ### The statements, by exec fuel -/

section stmts
variable (fe : IFEnv) (vis : Word)

/-- The common post: the stage relation, the pool grown, the memo's invariant at the same current
generation, the map unchanged up to the old last generation. -/
def RxPost (m m' : Mem) (a' : AState) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) : Prop :=
  ∃ M' G', StageR vis fe m' a' ∧ IWGrow m m' ∧ RfInv m' M' G' g ∧ GKeep M M' G g ∧ G ≤ G'

/-- A frame's hole, read back (`nestHoleImg`'s hit arm). -/
def frameTwin (c : NestCtx) (prog : List NestHole) (n1 : Nat) : AM (Option EIdx) := do
  let h := prog.getD n1 default
  let ds ← h.key.ds.mapM fun x => ConRon.Arena.replaceFVars (.holeImg c prog n1) x
  let hd ← internConstE h.key.cname h.key.lvls
  let r ← mkAppN hd ds
  pure (some r)

/-- The map unchanged up to `G` except at the current generation. -/
def GKeepX (M M' : Std.HashMap (EIdx × Word) EIdx) (G g : Word) : Prop :=
  ∀ (k : EIdx) (gen : Word), gen ≤ G → gen ≠ g → M'[(k, gen)]? = M[(k, gen)]?

end stmts

end L.Ind

namespace L.Ind

open L.Arena

theorem RxPost.trans {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a1 a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word}
    (h₁ : RxPost fe vis m m1 a1 M G g)
    (h₂ : ∀ M1 G1, RfInv m1 M1 G1 g → G ≤ G1 → ∃ M2 G2, StageR vis fe m2 a2 ∧ IWGrow m1 m2 ∧
      RfInv m2 M2 G2 g ∧ GKeep M1 M2 G1 g ∧ G1 ≤ G2) :
    RxPost fe vis m m2 a2 M G g := by
  obtain ⟨M1, G1, -, hg1, hR1, hk1, hG1⟩ := h₁
  obtain ⟨M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := h₂ M1 G1 hR1 hG1
  exact ⟨M2, G2, hS2, hg1.trans hg2, hR2, hk1.trans hk2 hG1, UInt64.le_trans hG1 hG2⟩

end L.Ind

end
