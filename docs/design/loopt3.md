# Lane `loopt3`: the declaration loop, continued

Journal of lane `loopt3` (decisions, measurements, findings, open ends). Only this lane edits this
file. Continues lane `loopt2` (`docs/design/loopt2.md`, its table "`PipelineRefines checkerProg`:
remaining obligations", items 7, 10, 11, 12, 12a and option (a)). Start: master `c92f106b`.

## Item 7: the loop over the front's records (`DeclsF`)

`LoopR.decls` is `DeclsF` (the front's relation, inductive records included) instead of `DeclsR`
(one-constant kinds only). Every arm lemma that took `DeclsR` takes `DeclsF`: on a concrete
one-constant record `DeclAtF` unfolds to `DeclAt`, so the arms' proofs are unchanged.
