import ConAgua.Arena.DeclCanonSpec2
import ConAgua.Arena.LevelArena
import ConAgua.Arena.LevelView

/-!
# `lv_node`, `view_ls`, `e_view` against the twin's views, converse direction (lane `decls3`)

`LevelArena.lvNodeW_store` says that if the twin's `viewL` succeeds then `lv_node` answers its
encoding. The canonical comparisons need the converse: a returning `lv_node` run means the twin's
`viewL` succeeds (the twin fails on a dangling handle).
-/

-- `lview_of_lvNodeW` moved to `LevelView.lean` (lane `defeq2`).
