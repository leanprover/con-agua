import ConAgua.Arena.Inst1Spec
import ConAgua.Arena.Walk
import ConAgua.Arena.FVarRange
import ConAgua.Arena.Abs1Spec
import ConAgua.Arena.ArRangeSpec
import ConAgua.Arena.InstListSpec
import ConAgua.Arena.HasFvar
import ConAgua.Arena.BvarB
import ConAgua.Arena.LitRefine
import ConAgua.Arena.Frame

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

set_option linter.unusedSimpArgs false

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
(22, 23), `app` (4, 5), `lam` (27, 28), `forallE` (29, 30), `letE` (20, 21), `proj` (31, 32). -/
def liftA : List ArrId := [41, 42, 43, 44, 45, 46, 22, 23, 4, 5, 27, 28, 29, 30, 20, 21, 31, 32]
/-- The `CTL` words: the lift memo's stamp and count (42, 43) and the six tables' counts. -/
def liftC : List Word := [42, 43, 22, 23, 4, 5, 28, 29, 30, 31, 20, 21, 32, 33]

theorem liftProg_closed : closedA liftProg liftA liftC liftFns = true := by decide +kernel

theorem LiftProg.closed {p : Prog} (hp : LiftProg p)
    (he : p.lookup "lift_entry" = some liftEntry) : closedA p liftA liftC liftFns = true :=
  closedW_of_agree liftProg_closed (by
    simp only [liftFns, List.cons_append, List.nil_append, List.forall_mem_cons,
      List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨hp.derb.trans rfl, hp.lff.trans rfl, hp.lfp.trans rfl, hp.lfc.trans rfl, hp.go.trans
      rfl, hp.app.trans rfl, hp.lam.trans rfl, hp.fa.trans rfl, hp.le.trans rfl, hp.pj.trans
      rfl, he.trans rfl, hp.mkapp.trans rfl, hp.mklam.trans rfl, hp.mkfa.trans rfl,
      hp.mklet.trans rfl, hp.mkpj.trans rfl, hp.bvf.trans rfl, hp.bvp.trans rfl, hp.bvi.trans
      rfl, hp.appf.trans rfl, hp.appp.trans rfl, hp.appi.trans rfl, hp.lamf.trans rfl,
      hp.lamp.trans rfl, hp.lami.trans rfl, hp.faf.trans rfl, hp.fap.trans rfl, hp.fai.trans
      rfl, hp.lef.trans rfl, hp.lep.trans rfl, hp.lei.trans rfl, hp.pjf.trans rfl, hp.pjp.trans
      rfl, hp.pji.trans rfl⟩)

/-- **Every run of `lift_entry` changes only `liftA` and `liftC`.** -/
theorem liftEntry_frame {p : Prog} (hp : LiftProg p) (he : p.lookup "lift_entry" = some liftEntry)
    {n : Nat} {vs : List Word} {m : Mem} {rs : List Word} {m' : Mem}
    (h : run p n "lift_entry" vs m = .ok (rs, m')) : MemFrame liftA liftC m m' :=
  (run_memFrame (hp.closed he) (by decide) h).1

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
      hp.base.derb.trans rfl, hp.base.lff.trans rfl, hp.base.lfp.trans rfl, hp.base.lfc.trans
      rfl, hp.base.go.trans rfl, hp.base.app.trans rfl, hp.base.lam.trans rfl, hp.base.fa.trans
      rfl, hp.base.le.trans rfl, hp.base.pj.trans rfl, hle.trans rfl, hp.base.mkapp.trans rfl,
      hp.base.mklam.trans rfl, hp.base.mkfa.trans rfl, hp.base.mklet.trans rfl,
      hp.base.mkpj.trans rfl, hp.base.bvf.trans rfl, hp.base.bvp.trans rfl, hp.base.bvi.trans
      rfl, hp.base.appf.trans rfl, hp.base.appp.trans rfl, hp.base.appi.trans rfl,
      hp.base.lamf.trans rfl, hp.base.lamp.trans rfl, hp.base.lami.trans rfl, hp.base.faf.trans
      rfl, hp.base.fap.trans rfl, hp.base.fai.trans rfl, hp.base.lef.trans rfl,
      hp.base.lep.trans rfl, hp.base.lei.trans rfl, hp.base.pjf.trans rfl, hp.base.pjp.trans
      rfl, hp.base.pji.trans rfl⟩)

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

theorem walkProg_closed : closedA walkProg walkA walkC walkFns = true := by decide +kernel

theorem walk_closed {p : Prog} (hpf : p.lookup "bm_find" = some (memoFindG bmSch))
    (hps : p.lookup "bm_put" = some (memoPutG bmSch)) (hpc : p.lookup "bm_clear" = some (memoClearG bmSch))
    (hp : p.lookup "bb_go" = some bbGo) (hpn : p.lookup "bb_node" = some bbNode)
    (hpm : p.lookup "bb_memo" = some bbMemo) : closedA p walkA walkC walkFns = true :=
  closedW_of_agree walkProg_closed (by
    simp only [walkFns, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨hpf.trans rfl, hps.trans rfl, hpc.trans rfl, hp.trans rfl, hpn.trans rfl, hpm.trans rfl⟩)

/-- **Every run of `bb_memo` changes only the `bvarBound` memo.** -/
theorem bbMemo_frame {p : Prog} (hpf : p.lookup "bm_find" = some (memoFindG bmSch))
    (hps : p.lookup "bm_put" = some (memoPutG bmSch)) (hpc : p.lookup "bm_clear" = some (memoClearG bmSch))
    (hp : p.lookup "bb_go" = some bbGo) (hpn : p.lookup "bb_node" = some bbNode)
    (hpm : p.lookup "bb_memo" = some bbMemo) {n : Nat} {vs : List Word} {m : Mem} {rs : List Word}
    {m' : Mem} (h : run p n "bb_memo" vs m = .ok (rs, m')) : MemFrame walkA walkC m m' :=
  (run_memFrame (walk_closed hpf hps hpc hp hpn hpm) (by decide) h).1

/-! ## `fr_memo` -/

def frFns : List FnName := ["fm_find", "fm_put", "fm_clear", "fr_go", "fr_node", "fr_memo"]

/-- The `fvarRange` walk writes only its memo `FRMEMO` (48) and its stamp and count (`CTL` 46, 47). -/
def frA : List ArrId := [48]
def frC : List Word := [46, 47]

theorem fvarRangeProg_closed : closedA fvarRangeProg frA frC frFns = true := by decide +kernel

theorem fr_closed {p : Prog} (hpf : p.lookup "fm_find" = some (memoFindG frSch))
    (hps : p.lookup "fm_put" = some (memoPutG frSch)) (hpc : p.lookup "fm_clear" = some (memoClearG frSch))
    (hp : p.lookup "fr_go" = some frGo) (hpn : p.lookup "fr_node" = some frNode)
    (hpm : p.lookup "fr_memo" = some frMemo) : closedA p frA frC frFns = true :=
  closedW_of_agree fvarRangeProg_closed (by
    simp only [frFns, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact ⟨hpf.trans rfl, hps.trans rfl, hpc.trans rfl, hp.trans rfl, hpn.trans rfl, hpm.trans rfl⟩)

/-- **Every run of `fr_memo` changes only the `fvarRange` memo.** -/
theorem frMemo_frame {p : Prog} (hpf : p.lookup "fm_find" = some (memoFindG frSch))
    (hps : p.lookup "fm_put" = some (memoPutG frSch)) (hpc : p.lookup "fm_clear" = some (memoClearG frSch))
    (hp : p.lookup "fr_go" = some frGo) (hpn : p.lookup "fr_node" = some frNode)
    (hpm : p.lookup "fr_memo" = some frMemo) {n : Nat} {vs : List Word} {m : Mem} {rs : List Word}
    {m' : Mem} (h : run p n "fr_memo" vs m = .ok (rs, m')) : MemFrame frA frC m m' :=
  (run_memFrame (fr_closed hpf hps hpc hp hpn hpm) (by decide) h).1

/-! ## `bvar_b`, `loose_bvars_bounded_fast` -/

def bvbFns : List FnName := ["bvar_b", "loose_bvars_bounded_fast", "der_b"] ++ walkFns

theorem bvbProg_closed : closedA bvbProg walkA walkC bvbFns = true := by decide +kernel

theorem bvb_closed {p : Prog} (hp : BvbProg p) : closedA p walkA walkC bvbFns = true :=
  closedW_of_agree bvbProg_closed (hp.agree bvbFns)

/-- **Every run of `bvar_b` changes only the `bvarBound` memo.** -/
theorem bvarB_frame {p : Prog} (hp : BvbProg p) {n : Nat} {vs : List Word} {m : Mem}
    {rs : List Word} {m' : Mem} (h : run p n "bvar_b" vs m = .ok (rs, m')) :
    MemFrame walkA walkC m m' :=
  (run_memFrame (bvb_closed hp) (by decide) h).1

/-- **Every run of `loose_bvars_bounded_fast` changes only the `bvarBound` memo.** -/
theorem lbbFast_frame {p : Prog} (hp : BvbProg p) {n : Nat} {vs : List Word} {m : Mem}
    {rs : List Word} {m' : Mem} (h : run p n "loose_bvars_bounded_fast" vs m = .ok (rs, m')) :
    MemFrame walkA walkC m m' :=
  (run_memFrame (bvb_closed hp) (by decide) h).1

/-! ## The store's `mk_*` and `intern_*`, the `abstract1` walk, `has_fvar` -/

/-- The read of the packed ranges and the `mk_*`/`intern_*` functions of `liftProg`. -/
def mkFns : List FnName :=
  ["der_b", "mk_app", "mk_lam", "mk_forall", "mk_let", "mk_proj", "bvar_find", "bvar_push",
    "intern_bvar", "app_find", "app_push", "intern_app", "lam_find", "lam_push", "intern_lam",
    "forall_find", "forall_push", "intern_forall", "letE_find", "letE_push", "intern_letE",
    "proj_find", "proj_push", "intern_proj"]

/-- What they write: `liftA` without the lift memo `LMEMO` (41). -/
def mkA : List ArrId := [42, 43, 44, 45, 46, 22, 23, 4, 5, 27, 28, 29, 30, 20, 21, 31, 32]
/-- `liftC` without the lift memo's stamp and count. -/
def mkC : List Word := [22, 23, 4, 5, 28, 29, 30, 31, 20, 21, 32, 33]

/-- The `abstract1` walk without its entry, the `fvarRange` walk, and `mkFns`. -/
def absWalkFns : List FnName :=
  ["ab_find", "ab_put", "ab_clear", "ab_fvb", "abs_go", "ab_node", "abs_app", "abs_lam",
    "abs_forall", "abs_let", "abs_proj"] ++ frFns ++ mkFns

theorem AbsProg.agree {p : Prog} (hp : AbsProg p) : ∀ f ∈ absWalkFns, p.lookup f = absProg.lookup f :=
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

/-- **Every run of `abs_entry` changes only `absA` and `absC`.** -/
theorem absEntry_frame {p : Prog} (hp : AbsProg p) (he : p.lookup "abs_entry" = some absEntry)
    {n : Nat} {vs : List Word} {m : Mem} {rs : List Word} {m' : Mem}
    (h : run p n "abs_entry" vs m = .ok (rs, m')) : MemFrame absA absC m m' :=
  (run_memFrame (hp.closed he) (by decide) h).1

/-- `has_fvar`, `has_fvar_fast` over the `abstract1` walk. -/
def hasFvarProg : Prog := [("has_fvar", hasFvarL), ("has_fvar_fast", hasFvarFastL)] ++ absWalkProg

def hasFvarFns : List FnName := ["has_fvar", "has_fvar_fast", "ab_fvb", "der_b"] ++ frFns

theorem hasFvarProg_closed : closedA hasFvarProg frA frC hasFvarFns = true := by decide +kernel

theorem hasFvar_closed {p : Prog} (hp : AbsProg p) (h1 : p.lookup "has_fvar" = some hasFvarL)
    (h2 : p.lookup "has_fvar_fast" = some hasFvarFastL) : closedA p frA frC hasFvarFns = true :=
  closedW_of_agree hasFvarProg_closed
    (ProgHas.agreeWith (ProgHas.cons h1 (ProgHas.cons h2 hp)) (ProgHas.refl hasFvarProg) hasFvarFns)

/-- **Every run of `has_fvar` changes only the `fvarRange` memo.** -/
theorem hasFvar_frame {p : Prog} (hp : AbsProg p) (h1 : p.lookup "has_fvar" = some hasFvarL)
    (h2 : p.lookup "has_fvar_fast" = some hasFvarFastL) {n : Nat} {vs : List Word} {m : Mem}
    {rs : List Word} {m' : Mem} (h : run p n "has_fvar" vs m = .ok (rs, m')) :
    MemFrame frA frC m m' :=
  (run_memFrame (hasFvar_closed hp h1 h2) (by decide) h).1

/-- **Every run of `has_fvar_fast` changes only the `fvarRange` memo.** -/
theorem hasFvarFast_frame {p : Prog} (hp : AbsProg p) (h1 : p.lookup "has_fvar" = some hasFvarL)
    (h2 : p.lookup "has_fvar_fast" = some hasFvarFastL) {n : Nat} {vs : List Word} {m : Mem}
    {rs : List Word} {m' : Mem} (h : run p n "has_fvar_fast" vs m = .ok (rs, m')) :
    MemFrame frA frC m m' :=
  (run_memFrame (hasFvar_closed hp h1 h2) (by decide) h).1

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

/-- **Every run of `ar_entry` changes only `absA` and `absC`** (the `abstract1` memo is shared). -/
theorem arEntry_frame {p : Prog} (hp : ArProg p) (he : p.lookup "ar_entry" = some arEntry)
    {n : Nat} {vs : List Word} {m : Mem} {rs : List Word} {m' : Mem}
    (h : run p n "ar_entry" vs m = .ok (rs, m')) : MemFrame absA absC m m' :=
  (run_memFrame (hp.closed he) (by decide) h).1

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

def storeFns : List FnName := storeProg.map (·.1)

/-- `nat_add_lit` writes the pool (0) and the `lit` table (2, 3), the pool top and the counts. -/
def storeA : List ArrId := [0, 2, 3]
def storeC : List Word := [0, 2, 3]

theorem storeProg_closed : closedA storeProg storeA storeC storeFns = true := by decide +kernel

/-- **Every run of `nat_add_lit` (or `intern_lit`) changes only the pool and the `lit` table.** -/
theorem storeProg_frame {f : FnName} (hf : f ∈ storeFns) {n : Nat} {vs : List Word} {m : Mem}
    {rs : List Word} {m' : Mem} (h : run storeProg n f vs m = .ok (rs, m')) :
    MemFrame storeA storeC m m' :=
  (run_memFrame storeProg_closed hf h).1

end L.Arena
