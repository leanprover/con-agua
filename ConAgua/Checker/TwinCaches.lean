import ConAgua.Checker.PipeRest

/-!
# The twin's prefix leaves the caches and the pin table (lane `pipeline`)

`prefix_caches`: after the twin's five stages before the fold (`TwinPrefix`) the per-declaration
caches are the start state's and the pin table is the one `internReservedPins` filled.

con-ron's Bridge summarizes the parse by `ParseStep.cframe`, which lets the four readback and
level-verdict caches move; the twin's parse does not write them. `Keeps x` (for every `c p`,
`Fr c p x`: a run from caches `c` and pins `p` ends at `c`, `p`) is shown by a closure search
(`keeps_step`: pure, fail, bind, `get`-then-`set` of the same caches and pins, `mapM`, `forIn`,
`ite`/`dite`, `match`) over the parse (`applyLine`, `feedChunk`, `parseChunks`, `builtinPreludeE`)
and the preparation (`frontOf`, `hoistNatOpGround`). The only writes are the interns' `set`s of a
new store. The level comparison in `validateIndD` is on the unmemoised `readLevel`.
`internReservedPins` (caches) and `internAllPins` (caches, and pins by `internAllPins_pins`) come
from con-ron's run lemmas.
-/

namespace L.Checker.TwinCaches

open ConRon.Arena ConRon.Arena.Frontend

/-- `x` run from a state with caches `c` and pin table `p` leaves them. -/
def Fr {α : Type} (c : Caches) (p : Pins) (x : AM α) : Prop :=
  ∀ a r a', a.caches = c → a.pins = p → x a = .ok (r, a') → a'.caches = c ∧ a'.pins = p

/-- `x` leaves the per-declaration caches and the pin table as it found them. -/
abbrev Keeps {α : Type} (x : AM α) : Prop := ∀ c p, Fr c p x

theorem Keeps.run {α : Type} {x : AM α} (h : Keeps x) {a a' : AState} {r : α}
    (hr : x a = .ok (r, a')) : a'.caches = a.caches ∧ a'.pins = a.pins :=
  h a.caches a.pins a r a' rfl rfl hr

theorem fr_pure {α : Type} {c : Caches} {p : Pins} (v : α) : Fr c p (pure v : AM α) := by
  intro a r a' hc hp h; cases h; exact ⟨hc, hp⟩

theorem fr_fail {α : Type} {c : Caches} {p : Pins} (e : CheckError) : Fr c p (fail e : AM α) := by
  intro a r a' _ _ h; cases h

theorem fr_bind {α β : Type} {c : Caches} {p : Pins} {x : AM α} {f : α → AM β} (hx : Fr c p x)
    (hf : ∀ v, Fr c p (f v)) : Fr c p (x >>= f) := by
  intro a r a' hc hp h
  simp only [bind, StateT.bind] at h
  cases hxa : x a with
  | error e => rw [hxa] at h; cases h
  | ok q =>
    obtain ⟨v, a₁⟩ := q
    rw [hxa] at h
    obtain ⟨h1, h2⟩ := hx a v a₁ hc hp hxa
    exact hf v a₁ r a' h1 h2 h

theorem fr_get_bind {β : Type} {c : Caches} {p : Pins} {f : AState → AM β}
    (hf : ∀ s, s.caches = c → s.pins = p → Fr c p (f s)) : Fr c p (get >>= f) := by
  intro a r a' hc hp h
  exact hf a hc hp a r a' hc hp h

theorem fr_set_bind {β : Type} {c : Caches} {p : Pins} {t : AState} {g : PUnit → AM β}
    (hc : t.caches = c) (hp : t.pins = p) (hg : Fr c p (g ⟨⟩)) : Fr c p (set t >>= g) := by
  intro a r a' _ _ h
  exact hg t r a' hc hp h

theorem fr_mapM {α β : Type} {c : Caches} {p : Pins} {f : α → AM β} (hf : ∀ x, Fr c p (f x)) :
    ∀ l : List α, Fr c p (l.mapM f)
  | [] => by rw [List.mapM_nil]; exact fr_pure _
  | x :: l => by
    rw [List.mapM_cons]
    exact fr_bind (hf x) fun _ => fr_bind (fr_mapM hf l) fun _ => fr_pure _

theorem fr_forIn {α β : Type} {c : Caches} {p : Pins} {f : α → β → AM (ForInStep β)}
    (hf : ∀ x b, Fr c p (f x b)) : ∀ (l : List α) (b : β), Fr c p (forIn l b f)
  | [], b => by rw [List.forIn_nil]; exact fr_pure _
  | x :: l, b => by
    rw [List.forIn_cons]
    refine fr_bind (hf x b) fun r => ?_
    cases r with
    | done => exact fr_pure _
    | yield b' => exact fr_forIn hf l b'

theorem fr_ite {α : Type} {c : Caches} {p : Pins} {q : Prop} [Decidable q] {x y : AM α}
    (hx : Fr c p x) (hy : Fr c p y) : Fr c p (if q then x else y) := by
  split <;> assumption

theorem fr_dite {α : Type} {c : Caches} {p : Pins} {q : Prop} [Decidable q] {x : q → AM α}
    {y : ¬q → AM α} (hx : ∀ h, Fr c p (x h)) (hy : ∀ h, Fr c p (y h)) :
    Fr c p (if h : q then x h else y h) := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

/-- One step of the closure search; the bracketed terms are `Keeps` facts (or `Fr`-valued
functions of `c p`) for the callees. -/
syntax "keeps_step" ("[" term,* "]")? : tactic
macro_rules
  | `(tactic| keeps_step) => `(tactic| first
    | with_reducible exact fr_pure _
    | with_reducible exact fr_fail _
    | (with_reducible refine fr_set_bind ?_ ?_ ?_) <;> first | assumption | skip
    | with_reducible refine fr_get_bind fun _ _ _ => ?_
    | with_reducible refine fr_bind ?_ fun _ => ?_
    | with_reducible refine fr_mapM (fun _ => ?_) _
    | with_reducible refine fr_forIn (fun _ _ => ?_) _ _
    | with_reducible refine fr_ite ?_ ?_
    | with_reducible refine fr_dite (fun _ => ?_) (fun _ => ?_)
    | split
    | simp only []
    | assumption)
  | `(tactic| keeps_step [$ts,*]) => do
    let mut acc ← `(tactic| keeps_step)
    for t in ts.getElems.reverse do
      acc ← `(tactic| first | with_reducible apply $t | ($acc:tactic))
    return acc

theorem keeps_internNNode (v : NNodeView) : Keeps (internNNode v) := by
  intro c p
  unfold internNNode
  repeat' keeps_step

theorem keeps_internLNode (v : LNodeView) : Keeps (internLNode v) := by
  intro c p
  unfold internLNode
  repeat' keeps_step

theorem keeps_internLsNode (v : LsNodeView) : Keeps (internLsNode v) := by
  intro c p
  unfold internLsNode
  repeat' keeps_step

theorem keeps_internE (v : ENodeView) : Keeps (internE v) := by
  intro c p
  unfold internE internLamE internForallEE internNodeE
  repeat' keeps_step

theorem keeps_storeFuel : Keeps storeFuel := by
  intro c p; unfold storeFuel; repeat' keeps_step

theorem keeps_StateD_name (st : StateD) (i : Nat) : Keeps (st.name i) := by
  intro c p; unfold StateD.name; repeat' keeps_step

theorem keeps_StateD_level (st : StateD) (i : Nat) : Keeps (st.level i) := by
  intro c p; unfold StateD.level; repeat' keeps_step

theorem keeps_StateD_expr (st : StateD) (i : Nat) : Keeps (st.expr i) := by
  intro c p; unfold StateD.expr; repeat' keeps_step

theorem keeps_parseNameEntryD (st : StateD) (i : Nat) (r : ConLeche.Frontend.NameRec) :
    Keeps (parseNameEntryD st i r) := by
  intro c p
  unfold parseNameEntryD StateD.freshName
  repeat' keeps_step [keeps_StateD_name, keeps_internNNode]

theorem keeps_parseLevelEntryD (st : StateD) (i : Nat) (r : ConLeche.Frontend.LevelRec) :
    Keeps (parseLevelEntryD st i r) := by
  intro c p
  unfold parseLevelEntryD StateD.freshLevel
  repeat' keeps_step [keeps_StateD_name, keeps_StateD_level, keeps_internLNode]

theorem keeps_parseExprEntryD (st : StateD) (i : Nat) (r : ConLeche.Frontend.ExprRec) :
    Keeps (parseExprEntryD st i r) := by
  intro c p
  unfold parseExprEntryD StateD.freshExpr
  repeat' keeps_step [keeps_StateD_name, keeps_StateD_level, keeps_StateD_expr, keeps_internE,
    keeps_internLsNode]

theorem keeps_view (h : EIdx) : Keeps (view h) := by
  intro c p; unfold view; repeat' keeps_step

theorem keeps_viewN (h : NIdx) : Keeps (viewN h) := by
  intro c p; unfold viewN; repeat' keeps_step

theorem keeps_readName (h : NIdx) : Keeps (readName h) := by
  intro c p; unfold readName; repeat' keeps_step

theorem keeps_readLevel (h : LIdx) : Keeps (readLevel h) := by
  intro c p; unfold readLevel; repeat' keeps_step

theorem keeps_parseCVD (st : StateD) (cv : ConLeche.Frontend.CVRec) : Keeps (parseCVD st cv) := by
  intro c p; unfold parseCVD getDeclD; repeat' keeps_step [keeps_StateD_name, keeps_StateD_expr]

theorem keeps_parseRuleD (st : StateD) (ru : ConLeche.Frontend.RuleRec) :
    Keeps (parseRuleD st ru) := by
  intro c p; unfold parseRuleD getDeclD; repeat' keeps_step [keeps_StateD_name, keeps_StateD_expr]

theorem keeps_indPiTeleLen : ∀ (fuel : Nat) (h : EIdx), Keeps (indPiTeleLen fuel h)
  | 0, h => by intro c p; unfold indPiTeleLen; repeat' keeps_step
  | fuel + 1, h => by
    intro c p; unfold indPiTeleLen
    repeat' keeps_step [keeps_view, keeps_indPiTeleLen fuel]

theorem keeps_piResultD : ∀ (fuel : Nat) (h : EIdx), Keeps (piResultD fuel h)
  | 0, h => by intro c p; unfold piResultD; repeat' keeps_step
  | fuel + 1, h => by
    intro c p; unfold piResultD
    repeat' keeps_step [keeps_view, keeps_piResultD fuel]

theorem keeps_piSortTeleLen : ∀ (fuel : Nat) (h : EIdx), Keeps (piSortTeleLen? fuel h)
  | 0, h => by intro c p; unfold piSortTeleLen?; repeat' keeps_step
  | fuel + 1, h => by
    intro c p; unfold piSortTeleLen?
    repeat' keeps_step [keeps_view, keeps_piSortTeleLen fuel]

theorem keeps_validateIndD (st : StateD) (tys : List ConLeche.Frontend.IndTypeRec)
    (cts : List ConLeche.Frontend.IndCtorRec) (rcs : List ConLeche.Frontend.IndRecRec) :
    Keeps (validateIndD st tys cts rcs) := by
  intro c p; unfold validateIndD getDeclD
  repeat' keeps_step [keeps_StateD_name, keeps_StateD_expr, keeps_storeFuel, keeps_readName,
    keeps_indPiTeleLen, keeps_piResultD, keeps_view, keeps_readLevel, keeps_viewN,
    keeps_piSortTeleLen]

theorem keeps_installIndD (st : StateD) (tys : List ConLeche.Frontend.IndTypeRec)
    (cts : List ConLeche.Frontend.IndCtorRec) (rcs : List ConLeche.Frontend.IndRecRec) (nPd : Nat) :
    Keeps (installIndD st tys cts rcs nPd) := by
  intro c p; unfold installIndD pushDecl
  repeat' keeps_step [keeps_parseCVD, keeps_parseRuleD]

theorem keeps_applyLine (st : StateD) (r : ConLeche.Frontend.LineRec) : Keeps (applyLine st r) := by
  intro c p; unfold applyLine applyDeclD processLineCoreD pushDecl getDeclD
  repeat' keeps_step [keeps_parseExprEntryD, keeps_parseNameEntryD, keeps_parseLevelEntryD,
    keeps_parseCVD, keeps_StateD_expr, keeps_validateIndD, keeps_installIndD]

theorem keeps_StateD_init : Keeps StateD.init := by
  intro c p; unfold StateD.init; repeat' keeps_step [keeps_internNNode, keeps_internLNode]

theorem keeps_applyFinalLine (st : StateD) (b : ByteArray) (i : USize) (lineNo : Nat) :
    Keeps (applyFinalLine st b i lineNo) := by
  intro c p; unfold applyFinalLine; repeat' keeps_step [keeps_applyLine]

theorem keeps_feedChunk (st : StateD) (b : ByteArray) (i : USize) (lineNo : Nat) :
    Keeps (feedChunk st b i lineNo) := by
  fun_induction feedChunk st b i lineNo <;> intro c p <;>
    repeat' keeps_step [keeps_applyLine, ‹∀ st, _ → Keeps (feedChunk st _ _ _)›]

theorem keeps_parseBytes (b : ByteArray) : Keeps (parseBytes b) := by
  intro c p; unfold parseBytes
  repeat' keeps_step [keeps_StateD_init, keeps_feedChunk, keeps_applyFinalLine]

theorem keeps_builtinPreludeE : Keeps builtinPreludeE := by
  intro c p; unfold builtinPreludeE; repeat' keeps_step [keeps_parseBytes]

theorem keeps_parseChunksGo : ∀ (st : StateD) (carry : ByteArray) (lineNo total : Nat)
    (cs : List ByteArray), Keeps (parseChunksGo st carry lineNo total cs)
  | st, carry, lineNo, total, [] => by
    intro c p; unfold parseChunksGo chunkFinish; repeat' keeps_step [keeps_applyFinalLine]
  | st, carry, lineNo, total, b :: cs => by
    intro c p; unfold parseChunksGo chunkStep
    repeat' keeps_step [keeps_feedChunk, keeps_parseChunksGo _ _ _ _ cs]

theorem keeps_parseChunks (cs : List ByteArray) : Keeps (parseChunks cs) := by
  intro c p; unfold parseChunks; repeat' keeps_step [keeps_StateD_init, keeps_parseChunksGo]

theorem keeps_preludeKey (d : IDeclaration) : Keeps (preludeKey d) := by
  intro c p; unfold preludeKey; repeat' keeps_step [keeps_internNNode]

theorem keeps_frontOf : ∀ (acc : Array IDeclaration) (ps : List IDeclaration)
    (ds : Array IDeclaration), Keeps (frontOf acc ps ds)
  | acc, [], ds => by intro c p; unfold frontOf; repeat' keeps_step
  | acc, q :: ps, ds => by
    intro c p; unfold frontOf; repeat' keeps_step [keeps_preludeKey, keeps_frontOf _ ps]

theorem keeps_pinAt (i : Nat) : Keeps (pinAt i) := by
  intro c p; unfold pinAt; repeat' keeps_step

theorem keeps_natPredName : Keeps natPredName := keeps_pinAt _
theorem keeps_natAddName : Keeps natAddName := keeps_pinAt _
theorem keeps_natSubName : Keeps natSubName := keeps_pinAt _
theorem keeps_natMulName : Keeps natMulName := keeps_pinAt _
theorem keeps_natPowName : Keeps natPowName := keeps_pinAt _
theorem keeps_natBeqName : Keeps natBeqName := keeps_pinAt _
theorem keeps_natBleName : Keeps natBleName := keeps_pinAt _
theorem keeps_natDivName : Keeps natDivName := keeps_pinAt _
theorem keeps_natModName : Keeps natModName := keeps_pinAt _
theorem keeps_natGcdName : Keeps natGcdName := keeps_pinAt _
theorem keeps_natLandName : Keeps natLandName := keeps_pinAt _
theorem keeps_natLorName : Keeps natLorName := keeps_pinAt _
theorem keeps_natXorName : Keeps natXorName := keeps_pinAt _
theorem keeps_natShiftLeftName : Keeps natShiftLeftName := keeps_pinAt _
theorem keeps_natShiftRightName : Keeps natShiftRightName := keeps_pinAt _

theorem keeps_natOpNames : Keeps natOpNames := by
  intro c p; unfold natOpNames; repeat' keeps_step [keeps_natPredName, keeps_natAddName, keeps_natSubName, keeps_natMulName, keeps_natPowName, keeps_natBeqName, keeps_natBleName, keeps_natDivName, keeps_natModName, keeps_natGcdName, keeps_natLandName, keeps_natLorName, keeps_natXorName, keeps_natShiftLeftName, keeps_natShiftRightName]

theorem keeps_natDivModNames : Keeps natDivModNames := by
  intro c p; unfold natDivModNames; repeat' keeps_step [keeps_natPredName, keeps_natAddName, keeps_natSubName, keeps_natMulName, keeps_natPowName, keeps_natBeqName, keeps_natBleName, keeps_natDivName, keeps_natModName, keeps_natGcdName, keeps_natLandName, keeps_natLorName, keeps_natXorName, keeps_natShiftLeftName, keeps_natShiftRightName]

theorem keeps_natOpDeps (n : NIdx) : Keeps (natOpDeps n) := by
  intro c p; unfold natOpDeps; repeat' keeps_step [keeps_natPredName, keeps_natAddName, keeps_natSubName, keeps_natMulName, keeps_natPowName, keeps_natBeqName, keeps_natBleName, keeps_natDivName, keeps_natModName, keeps_natGcdName, keeps_natLandName, keeps_natLorName, keeps_natXorName, keeps_natShiftLeftName, keeps_natShiftRightName]

theorem keeps_usedConstsGo : ∀ (seen : Std.HashSet EIdx) (acc : Array NIdx) (fuel : Nat) (e : EIdx),
    Keeps (usedConstsGo seen acc fuel e)
  | seen, acc, 0, e => by intro c p; unfold usedConstsGo; repeat' keeps_step
  | seen, acc, fuel + 1, e => by
    intro c p; unfold usedConstsGo; repeat' keeps_step [keeps_view, keeps_usedConstsGo _ _ fuel]

theorem keeps_usedConstsRules : ∀ (seen : Std.HashSet EIdx) (acc : Array NIdx) (rs : List IRecRule),
    Keeps (usedConstsRules seen acc rs)
  | seen, acc, [] => by intro c p; unfold usedConstsRules; repeat' keeps_step
  | seen, acc, r :: rs => by
    intro c p; unfold usedConstsRules
    repeat' keeps_step [keeps_usedConstsGo, keeps_usedConstsRules _ _ rs]

theorem keeps_usedConstsBlock : ∀ (seen : Std.HashSet EIdx) (acc : Array NIdx)
    (cs : List IConstantInfo), Keeps (usedConstsBlock seen acc cs)
  | seen, acc, [] => by intro c p; unfold usedConstsBlock; repeat' keeps_step
  | seen, acc, ci :: cs => by
    intro c p; unfold usedConstsBlock
    repeat' keeps_step [keeps_usedConstsGo, keeps_usedConstsRules,
      keeps_usedConstsBlock _ _ cs]

theorem keeps_usedConsts (d : IDeclaration) : Keeps (IDeclaration.usedConsts d) := by
  intro c p; unfold IDeclaration.usedConsts
  repeat' keeps_step [keeps_usedConstsGo, keeps_usedConstsBlock]

theorem keeps_isNatOpRecord (d : IDeclaration) : Keeps (isNatOpRecord d) := by
  intro c p; unfold isNatOpRecord; repeat' keeps_step [keeps_natOpNames, keeps_natDivModNames]

theorem keeps_hoistClosure (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat) (i : Nat) :
    ∀ (fuel : Nat) (target : Std.HashMap Nat Nat) (stack : List Nat),
      Keeps (hoistClosure ds idx i fuel target stack)
  | 0, target, stack => by intro c p; unfold hoistClosure; repeat' keeps_step
  | fuel + 1, target, stack => by
    intro c p; unfold hoistClosure hoistClosure.pushDeps
    repeat' keeps_step [keeps_usedConsts, keeps_hoistClosure ds idx i fuel]

theorem keeps_hoistDeps (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat) (i : Nat) :
    ∀ (target : Std.HashMap Nat Nat) (gs : List NIdx),
      Keeps (hoistTargetsGo.hoistDeps ds idx target i gs)
  | target, [] => by intro c p; unfold hoistTargetsGo.hoistDeps; repeat' keeps_step
  | target, g :: gs => by
    intro c p; unfold hoistTargetsGo.hoistDeps
    repeat' keeps_step [keeps_hoistClosure, keeps_hoistDeps ds idx i _ gs]

theorem keeps_hoistTargetsGo (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat)
    (target : Std.HashMap Nat Nat) (i : Nat) : Keeps (hoistTargetsGo ds idx target i) := by
  fun_induction hoistTargetsGo ds idx target i <;> intro c p <;>
    repeat' keeps_step [keeps_isNatOpRecord, keeps_natOpDeps, keeps_hoistDeps,
      ‹∀ _, Keeps (hoistTargetsGo _ _ _ _)›, ‹Keeps (hoistTargetsGo _ _ _ _)›]

theorem keeps_hoistNatOpGround (ds : Array IDeclaration) : Keeps (hoistNatOpGround ds) := by
  intro c p; unfold hoistNatOpGround hoistTargets; repeat' keeps_step [keeps_hoistTargetsGo]

theorem keeps_preparePrelude (pre : PreludeIx) (ds : Array IDeclaration) :
    Keeps (preparePrelude pre ds) := by
  intro c p; unfold preparePrelude prepareD
  repeat' keeps_step [keeps_frontOf, keeps_hoistNatOpGround]


end L.Checker.TwinCaches

namespace L.Checker

open ConRon.Arena ConRon.Arena.Frontend TwinCaches

/-- **The twin's stages before the fold leave the per-declaration caches and the pin table alone**:
the caches are the start state's, the pin table is the one `internReservedPins` filled. -/
theorem prefix_caches {b sA pre sB rc sC ds sD pins ipins sE}
    (h : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE) :
    sE.caches = (AState.init EStore.empty).caches ∧ sE.pins = sA.pins := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := h
  have hok0 : ConRon.Bridge.StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  obtain ⟨-, -, -, -, -, -, hcA⟩ := ConRon.Bridge.internReservedPins_run hok0 rfl hA
  obtain ⟨hcB, hpB⟩ := keeps_builtinPreludeE.run hB
  obtain ⟨hcC, hpC⟩ := (keeps_parseChunks [b]).run hC
  obtain ⟨hcD, hpD⟩ := (keeps_preparePrelude pre rc.decls).run hD
  obtain ⟨hok, hoff, hpins, hpp⟩ := prefix4_facts ⟨hA, hB, hC, hD⟩
  obtain ⟨-, -, -, -, -, -, -, hcE, -⟩ := ConRon.Bridge.internAllPins_run hok hpins hpp hoff hE
  exact ⟨by rw [hcE, hcD, hcC, hcB, hcA],
    by rw [internAllPins_pins hok hpins hoff hE, hpD, hpC, hpB]⟩

end L.Checker
