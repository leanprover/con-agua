import ConAgua.Arena.Walk
import ConAgua.Arena.LitRefine
import ConAgua.Arena.Frame

/-!
# The write sets of `bb_memo` and `nat_add_lit`, from the text

As `WriteSetLift.lean` for the `bvarBound` walk (`walkProg`) and the store's `nat_add_lit`
(`storeProg`). (`Walk.lean` and `Lift.lean` cannot be imported together: their arm helpers share
names.)
-/

set_option linter.unusedSimpArgs false

namespace L.Arena

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
