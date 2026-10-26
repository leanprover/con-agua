import ConAgua.Arena.PromoteCIRef31
import ConAgua.Census.Attr

/-!
# Census tags for the constant side of the promotion

Each relational lemma says: a returning run of the L function (`callW`) is a successful run of the
twin's function with the relations after; that is the refinement of the whole twin function (the
L code aborts only on capacities: fuel, an index past a table's end, a record count `≥ 2^60`).
-/

namespace L.Arena

@[refines ConRon.Arena.promoteNList] theorem promoteNList_refines : type_of% @nlist_rel := @nlist_rel
@[refines ConRon.Arena.promoteLList] theorem promoteLList_refines : type_of% @llist_rel := @llist_rel
@[refines ConRon.Arena.promoteEList] theorem promoteEList_refines : type_of% @elist_rel := @elist_rel
@[refines ConRon.Arena.promoteCV] theorem promoteCV_refines : type_of% @cv_rel := @cv_rel
@[refines ConRon.Arena.promoteFire] theorem promoteFire_refines : type_of% @fire_rel := @fire_rel
@[refines ConRon.Arena.promoteRule] theorem promoteRule_refines : type_of% @rule_rel := @rule_rel
@[refines ConRon.Arena.promoteRules] theorem promoteRules_refines : type_of% @rules_rel := @rules_rel
@[refines ConRon.Arena.promoteCaps] theorem promoteCaps_refines : type_of% @caps_rel := @caps_rel
@[refines ConRon.Arena.promoteProjTable] theorem promoteProjTable_refines : type_of% @proj_rel := @proj_rel
@[refines ConRon.Arena.promoteCI] theorem promoteCI_refines : type_of% @ci_rel := @ci_rel
@[refines ConRon.Arena.promoteCIList] theorem promoteCIList_refines : type_of% @ciList_rel := @ciList_rel
@[refines ConRon.Arena.eraseInstalled] theorem eraseInstalled_refines : type_of% @erase_rel := @erase_rel
@[refines ConRon.Arena.indexPromoted] theorem indexPromoted_refines : type_of% @index_rel := @index_rel
@[refines ConRon.Arena.promoteProjTables] theorem promoteProjTables_refines : type_of% @ptables_rel := @ptables_rel
@[refines ConRon.Arena.eraseInstalledTables] theorem eraseInstalledTables_refines : type_of% @eraseT_rel := @eraseT_rel
@[refines ConRon.Arena.indexPromotedTables] theorem indexPromotedTables_refines : type_of% @indexT_rel := @indexT_rel
@[refines ConRon.Arena.promoteNewConsts] theorem promoteNewConsts_refines : type_of% @pconsts_rel := @pconsts_rel
@[refines ConRon.Arena.promoteNewTables] theorem promoteNewTables_refines : type_of% @ptablesNew_rel := @ptablesNew_rel
@[refines ConRon.Arena.promoteNew] theorem promoteNew_refines : type_of% @promoteNew_rel := @promoteNew_rel


end L.Arena
