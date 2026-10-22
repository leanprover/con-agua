import ConAgua.Arena.PromoteCIRef31
import ConAgua.Census.Attr

/-!
# Census tags for the constant side of the promotion

Each relational lemma says: a returning run of the L function (`callW`) is a successful run of the
twin's function with the relations after; that is the refinement of the whole twin function (the
L code aborts only on capacities: fuel, an index past a table's end, a record count `≥ 2^60`).
-/

namespace L.Arena

@[refines ConRon.Arena.promoteNList] theorem promoteNList_refines : _ := @nlist_rel
@[refines ConRon.Arena.promoteLList] theorem promoteLList_refines : _ := @llist_rel
@[refines ConRon.Arena.promoteEList] theorem promoteEList_refines : _ := @elist_rel
@[refines ConRon.Arena.promoteCV] theorem promoteCV_refines : _ := @cv_rel
@[refines ConRon.Arena.promoteFire] theorem promoteFire_refines : _ := @fire_rel
@[refines ConRon.Arena.promoteRule] theorem promoteRule_refines : _ := @rule_rel
@[refines ConRon.Arena.promoteRules] theorem promoteRules_refines : _ := @rules_rel
@[refines ConRon.Arena.promoteCaps] theorem promoteCaps_refines : _ := @caps_rel
@[refines ConRon.Arena.promoteProjTable] theorem promoteProjTable_refines : _ := @proj_rel
@[refines ConRon.Arena.promoteCI] theorem promoteCI_refines : _ := @ci_rel
@[refines ConRon.Arena.promoteCIList] theorem promoteCIList_refines : _ := @ciList_rel
@[refines ConRon.Arena.eraseInstalled] theorem eraseInstalled_refines : _ := @erase_rel
@[refines ConRon.Arena.indexPromoted] theorem indexPromoted_refines : _ := @index_rel
@[refines ConRon.Arena.promoteNew] theorem promoteNew_refines : _ := @promoteNew_rel

#print axioms promoteNew_refines
#print axioms promoteCI_refines

end L.Arena
