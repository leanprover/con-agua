module

import ConAgua.Arena.RecGenSpec.CfhW
public import ConAgua.Arena.RecClassSpec.ClassNPcOf
public import ConAgua.Arena.RecGenSpec.ClassFieldsOf
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.RecClassSpec.SlotProg
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.BlockCounts
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.RecGenSpec.CkcW
public import ConAgua.Arena.Verdict
public import ConAgua.Checker.NoVerdictFns
import all ConAgua.Arena.RecGen

@[expose] public section

/-!
# `class_fields_of_go`, `class_fields_of`: one model and one refinement for both outcomes

`cfgE` (`l_model … unified`): the recursive call through the model itself, the callees (all outside
the verdict closure) through their `Option` models. `cfg_ref` refines `classFieldsOf` for both
outcomes: an error comes from the single abort (`R_GENERATED_RECURSOR_THE_INDUCTIVE`, the twin's
`fail`) or is of class `0`. `class_fields_of`'s unified model `cfoE` calls it in tail position
(`cfo_ref`); its callers read `cfo_ref` through the run (`RefE.run_okW`, `RefE.run_err`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cfgE_spec (p : Prog) (hP : CfoProg p)
  fns [hP.go ↦ cfgE]
  specs [ftdF_spec0 p hP.ftd n, nestOcc_spec' p hP.no n, classFieldsOfHits_spec p hP.hits n,
    iwAlloc_specW p hP.alloc n, piBinders_spec p hP.alloc hP.copy hP.no.hv hP.cons hP.pb n,
    rec3_specW p hP.alloc n hP.r3, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_fields_of_go` gives besides the twin's kinds `ks` (from `m`): the stage relation,
growth, the kinds a slice stable above `m`'s top, `nest_occ`'s memo relation at some map, the
write set outside the other walk memos, the abstraction memo's frame. -/
structure CfgPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (m' : Mem) (ks : List ClassField) (a' : AState) : Prop where
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  kinds : SPLA (iwTop m) decCF m' (r.headD 0).toNat (r.tail.headD 0).toNat ks
  nomr : ∃ mp, noMR m' mp
  frame : MFr [NOM] [204, 205] m m'
  afr : AFr m m'

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
variable {p : Prog}

/-- The common tail of both arms: the record, the rest (the recursive call), the cons. -/
theorem cfgTailE {G : Prop} {n : Nat} {m m2 m5 : Mem} {a2 : AState} {k : Word} {ws r5 : List Word}
    {y : ClassField} {mp : Std.HashMap EIdx Bool} {mo ml io il i fo fl : Word}
    {opR : AM (List ClassField)}
    (hS2 : StageR vis fe m2 a2) (hg2 : IWGrow m m2) (hM2 : noMR m2 mp)
    (hf2 : MFr [NOM] [204, 205] m m2) (hA2 : AFr m m2) (hk : k.toNat = ws.length)
    (hy : ∀ m'', (∀ j (hj : j < ws.length), iwN m'' ((rdW (m2.arr64 CTL) 200).toNat + j) = some (ws[j]'hj).toNat) →
      decCF m'' (rdW (m2.arr64 CTL) 200).toNat = some y)
    (h5 : recW m2 k ws = some (r5, m5))
    (hrest : StageR vis fe m5 a2 → IWGrow m2 m5 → noMR m5 mp →
      RefE G (cfgE p n m5 mo ml io il (i + 1) (fo + 1) (fl - 1)) opR a2
        (fun v ks a' => CfgPost dn vis fe m5 v.1 v.2 ks a')) :
    RefE G (cfgE.j1 p n mo ml io il i fo fl (r5.headD 0) m5) (do let r ← opR; pure (y :: r)) a2
      (fun v ks a' => CfgPost dn vis fe m v.1 v.2 ks a') := by
  sorry

/-- **`class_fields_of_go` refines `classFieldsOf`, both outcomes** (twin side: the list recursion
of `classFieldsOf`): `fvar_type_d`, `nest_occ`, the hits, then the field's kind (an ordinary
field's one-word record, or a recursive field's `pi_binders` and three-word record), the rest, the
cons; the one reject site (neither kind) is the twin's `fail`. -/
theorem cfg_ref (bsh : BlockShape) (ihs : List (Nat × Nat)) (n : Nat) :
    ∀ {m : Mem} {a : AState} {mo ml io il i fo fl : Word} {fs : List EIdx}
    {mp0 : Std.HashMap EIdx Bool},
    StageR vis fe m a →
    decHL m mo.toNat ml.toNat = some bsh.memberNames → mo.toNat + ml.toNat ≤ iwTop m →
    StabD (fun m => decPL m (decNN m) io.toNat il.toNat) m ihs → io.toNat + il.toNat < 2 ^ 64 →
    decHL m fo.toNat fl.toNat = some fs → fo.toNat + fl.toNat ≤ iwTop m →
    i.toNat + fl.toNat < 2 ^ 64 → noMR m mp0 →
    RefE (closedNV p _root_.L.Checker.nvFns = true) (cfgE p n m mo ml io il i fo fl)
      (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a
      (fun v ks a' => CfgPost dn vis fe m v.1 v.2 ks a') := by
  sorry

end sims

/-! ## `class_fields_of` -/

l_model cfoE_spec (p : Prog) (hP : CfoProg p)
  fns [hP.cfo ↦ cfoE]
  specs [blockShapeMemberNames_spec p hP.alloc hP.mnc hP.mn n, cfgE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section cfo
variable {p : Prog} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`class_fields_of` refines `classFieldsOf`, both outcomes**: the block's member names
(`block_shape_member_names`, outside the verdict closure), then `class_fields_of_go` (`cfg_ref`) in
tail position. -/
theorem cfo_ref (bsh : BlockShape) (ihs : List (Nat × Nat)) (n : Nat) {m : Mem} {a : AState}
    {q io il i fo fl : Word} {fs : List EIdx} {mp0 : Std.HashMap EIdx Bool} (hS : StageR vis fe m a)
    (hb : BSOK m q.toNat bsh) (hih : StabD (fun m => decPL m (decNN m) io.toNat il.toNat) m ihs)
    (hib : io.toNat + il.toNat < 2 ^ 64) (hfs : decHL m fo.toNat fl.toNat = some fs)
    (hfb : fo.toNat + fl.toNat ≤ iwTop m) (hi : i.toNat + fl.toNat < 2 ^ 64) (hM : noMR m mp0) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (cfoE p n m q io il i fo fl)
      (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a
      (fun v ks a' => CfgPost dn vis fe m v.1 v.2 ks a') := by
  sorry

/-- **`class_fields_of` refines `classFieldsOf`** (through the stub `fvar_type_d`; `cfo_ref`'s ok
half): the fields' kinds are a stable slice of `ClassField` records; `nest_occ`'s memo relation is
needed before and holds after (at some map). -/
@[refines ConRon.Arena.classFieldsOf]
theorem classFieldsOf_refines (hp : CfoProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (q io il i fo fl : Word) (bsh : BlockShape)
    (ihs : List (Nat × Nat)) (fs : List EIdx) (mp0 : Std.HashMap EIdx Bool)
    (hS : StageR vis fe s₀.mem a₀) (hb : BSOK s₀.mem q.toNat bsh)
    (hih : StabD (fun m => decPL m (decNN m) io.toNat il.toNat) s₀.mem ihs) (hib : io.toNat + il.toNat < 2 ^ 64)
    (hfs : decHL s₀.mem fo.toNat fl.toNat = some fs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hi : i.toNat + fl.toNat < 2 ^ 64) (hM : noMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_of" [q, io, il, i, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀ ∧
      CfoQ dn vis fe s₀.mem (r, s'.mem) (AM.st (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀)
        (AM.res (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀); ⊤⦄ := by
  refine triple_post (RefE.triple (cfoE_spec p hp n s₀ q io il i fo fl)
    (cfo_ref dn vis fe bsh ihs n hS hb hih hib hfs hfb hi hM)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.kinds, hR.nomr, hR.frame⟩

end cfo

end L.Ind

end
