import ConAgua.Arena.Inst1Spec
import ConAgua.Arena.ArRangeSpec
import ConAgua.Arena.InstListSpec
import ConAgua.Arena.BvarB
import ConAgua.Arena.Frame
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The write sets of the walks and the store programs, from the text

`closedA` (`Frame.lean`, `L/WriteSet.lean`) checked on the concrete programs (`liftProg`,
`instProg`, `walkProg`, `fvarRangeProg`, `bvbProg`, `absProg`, `hasFvarProg`, `arProg`, `instListProg`, `storeProg`) by `decide +kernel`, then carried to every program that satisfies the walk's program
predicate (`LiftProg p`, `InstProg p`), since `closedW` reads only the lookups of the functions
it checks. With `run_keeps`, any memory predicate that is `Stable` under the write set survives
every run of the entries, with no lemma about the walk.
-/

open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## `lift_entry` -/

/-- The functions of `liftProg`: the walk, its memo, the `mk_*` and their stores. -/
def liftFns : List FnName :=
  ["der_b", "lf_find", "lf_put", "lf_clear", "lift_go", "lift_app", "lift_lam", "lift_forall",
    "lift_let", "lift_proj", "lift_entry", "mk_app", "mk_lam", "mk_forall", "mk_let", "mk_proj",
    "bvar_find", "bvar_push", "intern_bvar", "app_find", "app_push", "intern_app",
    "lam_find", "lam_push", "intern_lam", "forall_find", "forall_push", "intern_forall",
    "letE_find", "letE_push", "intern_letE", "proj_find", "proj_push", "intern_proj"]

/-- What they write: the lift memo `LMEMO` (41), the derived ranges 42‥46, and the tables `bvar`
(22, 23), `app` (4, 5), `lam` (27, 28), `forallE` (29, 30), `letE` (20, 21), `proj` (31, 32), the
tables and ranges in both tiers (tier 1 of array `a` is `a + 256`). -/
def liftA : List ArrId := [41, 42, 43, 44, 45, 46, 22, 23, 4, 5, 27, 28, 29, 30, 20, 21, 31, 32,
  298, 299, 300, 301, 302, 278, 279, 260, 261, 283, 284, 285, 286, 276, 277, 287, 288]
/-- The `CTL` words: the lift memo's stamp and count (42, 43) and the six tables' counts. -/
def liftC : List Word := [42, 43, 22, 23, 4, 5, 28, 29, 30, 31, 20, 21, 32, 33]

theorem liftProg_closed : closedA liftProg liftA liftC liftFns = true := by decide +kernel

theorem LiftProg.closed {p : Prog} (hp : LiftProg p)
    (he : p.lookup "lift_entry" = some liftEntry) : closedA p liftA liftC liftFns = true :=
  closedW_of_agree liftProg_closed (by
    simp only [liftFns, List.forall_mem_cons,
      List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨(hp.get "der_b").trans rfl, (hp.get "lf_find").trans rfl, (hp.get "lf_put").trans rfl, (hp.get "lf_clear").trans rfl, (hp.get "lift_go").trans
      rfl, (hp.get "lift_app").trans rfl, (hp.get "lift_lam").trans rfl, (hp.get "lift_forall").trans rfl, (hp.get "lift_let").trans rfl, (hp.get "lift_proj").trans
      rfl, he.trans rfl, (hp.get "mk_app").trans rfl, (hp.get "mk_lam").trans rfl, (hp.get "mk_forall").trans rfl,
      (hp.get "mk_let").trans rfl, (hp.get "mk_proj").trans rfl, (hp.get "bvar_find").trans rfl, (hp.get "bvar_push").trans rfl, (hp.get "intern_bvar").trans
      rfl, (hp.get "app_find").trans rfl, (hp.get "app_push").trans rfl, (hp.get "intern_app").trans rfl, (hp.get "lam_find").trans rfl,
      (hp.get "lam_push").trans rfl, (hp.get "intern_lam").trans rfl, (hp.get "forall_find").trans rfl, (hp.get "forall_push").trans rfl, (hp.get "intern_forall").trans
      rfl, (hp.get "letE_find").trans rfl, (hp.get "letE_push").trans rfl, (hp.get "intern_letE").trans rfl, (hp.get "proj_find").trans rfl, (hp.get "proj_push").trans
      rfl, (hp.get "intern_proj").trans rfl⟩)

/-! ## `inst_entry` -/

def instFns : List FnName :=
  ["if_find", "if_put", "if_clear", "inst_go", "inst_app", "inst_lam", "inst_forall", "inst_let",
    "inst_proj", "inst_entry"] ++ liftFns

/-- `liftA` and the `instantiate1` memo `IMEMO` (47). -/
def instA : List ArrId := 47 :: liftA
/-- `liftC` and the `instantiate1` memo's stamp and count (44, 45). -/
def instC : List Word := 44 :: 45 :: liftC

theorem instProg_closed : closedA instProg instA instC instFns = true := by decide +kernel

theorem InstProg.closed {p : Prog} (hp : InstProg p) (he : p.lookup "inst_entry" = some instEntry)
    (hle : p.lookup "lift_entry" = some liftEntry) : closedA p instA instC instFns = true :=
  closedW_of_agree instProg_closed (by
    simp only [instFns, liftFns, List.cons_append, List.nil_append, List.forall_mem_cons,
      List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨hp.iff.trans rfl, hp.ifp.trans rfl, hp.ifc.trans rfl, hp.go.trans rfl, hp.app.trans
      rfl, hp.lam.trans rfl, hp.fa.trans rfl, hp.le.trans rfl, hp.pj.trans rfl, he.trans rfl,
      (hp.base.get "der_b").trans rfl, (hp.base.get "lf_find").trans rfl, (hp.base.get "lf_put").trans rfl, (hp.base.get "lf_clear").trans
      rfl, (hp.base.get "lift_go").trans rfl, (hp.base.get "lift_app").trans rfl, (hp.base.get "lift_lam").trans rfl, (hp.base.get "lift_forall").trans
      rfl, (hp.base.get "lift_let").trans rfl, (hp.base.get "lift_proj").trans rfl, hle.trans rfl, (hp.base.get "mk_app").trans rfl,
      (hp.base.get "mk_lam").trans rfl, (hp.base.get "mk_forall").trans rfl, (hp.base.get "mk_let").trans rfl,
      (hp.base.get "mk_proj").trans rfl, (hp.base.get "bvar_find").trans rfl, (hp.base.get "bvar_push").trans rfl, (hp.base.get "intern_bvar").trans
      rfl, (hp.base.get "app_find").trans rfl, (hp.base.get "app_push").trans rfl, (hp.base.get "intern_app").trans rfl,
      (hp.base.get "lam_find").trans rfl, (hp.base.get "lam_push").trans rfl, (hp.base.get "intern_lam").trans rfl, (hp.base.get "forall_find").trans
      rfl, (hp.base.get "forall_push").trans rfl, (hp.base.get "intern_forall").trans rfl, (hp.base.get "letE_find").trans rfl,
      (hp.base.get "letE_push").trans rfl, (hp.base.get "intern_letE").trans rfl, (hp.base.get "proj_find").trans rfl, (hp.base.get "proj_push").trans
      rfl, (hp.base.get "intern_proj").trans rfl⟩)

/-- **Every run of `inst_entry` changes only `instA` and `instC`.** -/
theorem instEntry_frame {p : Prog} (hp : InstProg p) (he : p.lookup "inst_entry" = some instEntry)
    (hle : p.lookup "lift_entry" = some liftEntry)
    {n : Nat} {vs : List Word} {m : Mem} {rs : List Word} {m' : Mem}
    (h : run p n "inst_entry" vs m = .ok (rs, m')) : MemFrame instA instC m m' :=
  (run_memFrame (hp.closed he hle) (by decide) h).1

/-! ## `bb_memo` -/

def walkFns : List FnName := ["bm_find", "bm_put", "bm_clear", "bb_go", "bb_node", "bb_memo"]

/-- The walk writes only its memo `BMEMO` (24) and the memo's stamp and count (`CTL` 24, 25). -/
def walkA : List ArrId := [24]
def walkC : List Word := [24, 25]

/-! ## `fr_memo` -/

def frFns : List FnName := ["fm_find", "fm_put", "fm_clear", "fr_go", "fr_node", "fr_memo"]

/-- The `fvarRange` walk writes only its memo `FRMEMO` (48) and its stamp and count (`CTL` 46, 47). -/
def frA : List ArrId := [48]
def frC : List Word := [46, 47]

/-! ## `bvar_b`, `loose_bvars_bounded_fast` -/

def bvbFns : List FnName := ["bvar_b", "loose_bvars_bounded_fast", "der_b"] ++ walkFns

theorem bvbProg_closed : closedA bvbProg walkA walkC bvbFns = true := by decide +kernel

theorem bvb_closed {p : Prog} (hp : BvbProg p) : closedA p walkA walkC bvbFns = true :=
  closedW_of_agree bvbProg_closed (hp.agree bvbFns)

/-! ## The store's `mk_*` and `intern_*`, the `abstract1` walk, `has_fvar` -/

/-- The read of the packed ranges and the `mk_*`/`intern_*` functions of `liftProg`. -/
def mkFns : List FnName :=
  ["der_b", "mk_app", "mk_lam", "mk_forall", "mk_let", "mk_proj", "bvar_find", "bvar_push",
    "intern_bvar", "app_find", "app_push", "intern_app", "lam_find", "lam_push", "intern_lam",
    "forall_find", "forall_push", "intern_forall", "letE_find", "letE_push", "intern_letE",
    "proj_find", "proj_push", "intern_proj"]

/-- What they write: `liftA` without the lift memo `LMEMO` (41). -/
def mkA : List ArrId := [42, 43, 44, 45, 46, 22, 23, 4, 5, 27, 28, 29, 30, 20, 21, 31, 32,
  298, 299, 300, 301, 302, 278, 279, 260, 261, 283, 284, 285, 286, 276, 277, 287, 288]
/-- `liftC` without the lift memo's stamp and count. -/
def mkC : List Word := [22, 23, 4, 5, 28, 29, 30, 31, 20, 21, 32, 33]

/-- The `abstract1` walk without its entry, the `fvarRange` walk, and `mkFns`. -/
def absWalkFns : List FnName :=
  ["ab_find", "ab_put", "ab_clear", "ab_fvb", "abs_go", "ab_node", "abs_app", "abs_lam",
    "abs_forall", "abs_let", "abs_proj"] ++ frFns ++ mkFns

theorem AbsProg.agree {p : Prog} (hp : AbsProg p) :
    ∀ f ∈ absWalkFns, p.lookup f = absProg.lookup f :=
  ProgHas.agreeWith hp absProg_ok absWalkFns

/-- The `abstract1` memo `ABMEMO` (49), the `fvarRange` memo, and `mkA`. -/
def absA : List ArrId := 49 :: frA ++ mkA
/-- The `abstract1` memo's stamp and count (48, 49), `frC` and `mkC`. -/
def absC : List Word := 48 :: 49 :: frC ++ mkC

def absFns : List FnName := "abs_entry" :: absWalkFns

theorem absProg_closed : closedA absProg absA absC absFns = true := by decide +kernel

theorem AbsProg.closed {p : Prog} (hp : AbsProg p) (he : p.lookup "abs_entry" = some absEntry) :
    closedA p absA absC absFns = true :=
  closedW_of_agree absProg_closed (by
    simp only [absFns, List.forall_mem_cons]
    exact ⟨he.trans rfl, hp.agree⟩)

/-! ## `ar_entry` -/

def arFns : List FnName :=
  ["ar_go", "ar_node", "ar_app", "ar_lam", "ar_forall", "ar_let", "ar_proj", "ar_entry"] ++
    absWalkFns

theorem arProg_closed : closedA arProg absA absC arFns = true := by decide +kernel

theorem ArProg.closed {p : Prog} (hp : ArProg p) (he : p.lookup "ar_entry" = some arEntry) :
    closedA p absA absC arFns = true :=
  closedW_of_agree arProg_closed
    (ProgHas.agreeWith (ProgHas.append hp (ProgHas.cons he ProgHas.nil))
      (ProgHas.refl arProg).left arFns)

/-! ## `inst_list` -/

def instListFns : List FnName :=
  ["ilm_find", "ilm_put", "ilm_clear", "il_go", "il_app", "il_lam", "il_forall", "il_let",
    "il_proj", "il_bvar", "ilg_go", "ilg_app", "ilg_lam", "ilg_forall", "ilg_let", "ilg_proj",
    "inst_list"] ++ mkFns

/-- The `instantiateList` memo `ILMEMO` (50) and `mkA`; the spine stack `ILSPN` (144) is only
read. -/
def instListA : List ArrId := 50 :: mkA
/-- The memo's stamp and count (50, 51) and `mkC`. -/
def instListC : List Word := 50 :: 51 :: mkC

theorem instListProg_closed : closedA instListProg instListA instListC instListFns = true := by
  decide +kernel

theorem InstListProg.closed {p : Prog} (hp : InstListProg p)
    (he : p.lookup "inst_list" = some instListL) : closedA p instListA instListC instListFns = true :=
  closedW_of_agree instListProg_closed
    (ProgHas.agreeWith (ProgHas.append hp (ProgHas.cons he ProgHas.nil))
      (ProgHas.refl instListProg) instListFns)

/-- **Every run of `inst_list` changes only `instListA` and `instListC`.** -/
theorem instList_frame {p : Prog} (hp : InstListProg p) (he : p.lookup "inst_list" = some instListL)
    {n : Nat} {vs : List Word} {m : Mem} {rs : List Word} {m' : Mem}
    (h : run p n "inst_list" vs m = .ok (rs, m')) : MemFrame instListA instListC m m' :=
  (run_memFrame (hp.closed he) (by decide) h).1

/-! ## `nat_add_lit` -/

end L.Arena
