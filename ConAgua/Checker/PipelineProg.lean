import ConAgua.Checker.Pipeline
import ConAgua.Checker.Prog

/-!
# `PipelineRefines checkerProg` from its stages (lane `pipeline`)

The checker's program binds `check` to `checkL`, so `pipelineRefines_of_stages` applies: the eight
stage specs at `checkerProg`, over relations `ρ` between them, give `PipelineRefines checkerProg`
and with it `checker_x64_accepts` for the real checker. The stage specs are discharged one by
one (docs/design/pipeline.md, the obligations table).
-/

namespace L.Checker

set_option maxRecDepth 100000 in
theorem checkerProg_check : checkerProg.lookup "check" = some checkL := rfl

/-- **The checker refines the twin's pipeline**, given its eight stages at some relations. -/
theorem pipelineRefines_checkerProg (ρ : ∀ b pb s8 s64, PipeRels b pb s8 s64)
    (h1 : CapStage checkerProg ρ) (h2 : PbStage checkerProg ρ) (h3 : IrpStage checkerProg ρ)
    (h4 : PreludeStage checkerProg ρ) (h5 : FrontStage checkerProg ρ)
    (h6 : PrepareStage checkerProg ρ) (h7 : PinsStage checkerProg ρ)
    (h8 : LoopStage checkerProg ρ) : ConAgua.Final.PipelineRefines checkerProg :=
  pipelineRefines_of_stages checkerProg_check ρ h1 h2 h3 h4 h5 h6 h7 h8

end L.Checker
