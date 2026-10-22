import ConAgua.Arena.Inst1Spec
import ConAgua.Arena.Walk
import ConAgua.Arena.FVarRange
import ConAgua.Arena.LitRefine
import ConAgua.Arena.Frame

/-!
# The write sets of the walks and the store programs, from the text

`closedA` (`Frame.lean`, `L/WriteSet.lean`) checked on the concrete programs (`liftProg`,
`instProg`, `walkProg`, `fvarRangeProg`, `storeProg`) by `decide +kernel`, then carried to every program that satisfies the walk's program
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
