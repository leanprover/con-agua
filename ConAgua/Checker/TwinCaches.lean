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

theorem keeps_toConstantVal (ci : IConstantInfo) : Keeps ci.toConstantVal := by
  intro c p; unfold IConstantInfo.toConstantVal
  repeat' keeps_step [keeps_internLNode, keeps_internE]

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
    repeat' keeps_step [keeps_toConstantVal, keeps_usedConstsGo, keeps_usedConstsRules,
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

section pins
open ConLeche ConRon.Bridge

/-- con-ron: ConRon/Bridge/Checker/Pins.lean internAllPins_run — the same walk, for the conjunct
that lemma does not export: `internAllPins` leaves the pin table (it builds the pin SETS, its
result). -/
theorem internAllPins_pins {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) : s'.pins = s.pins := by
  simp only [ConRon.Arena.internAllPins] at hrun
  have a0 : ConRon.Bridge.Frontend.IStepS s s := ConRon.Bridge.Frontend.IStepS.refl hok
  obtain ⟨_, u0, q0, w0⟩ := AM.bind_ok hrun
  have a1 := a0.trans (BasisKind.decls_sstep a0.ok q0)
  obtain ⟨_, u1, q1, w1⟩ := AM.bind_ok w0
  have a2 := a1.trans (BasisKind.declsA_sstep a1.ok q1)
  obtain ⟨_, u2, q2, w2⟩ := AM.bind_ok w1
  have a3 := a2.trans (BasisKind.decls_sstep a2.ok q2)
  obtain ⟨_, u3, q3, w3⟩ := AM.bind_ok w2
  have a4 := a3.trans (BasisKind.declsA_sstep a3.ok q3)
  obtain ⟨_, u4, q4, w4⟩ := AM.bind_ok w3
  have a5 := a4.trans (BasisKind.decls_sstep a4.ok q4)
  obtain ⟨_, u5, q5, w5⟩ := AM.bind_ok w4
  have a6 := a5.trans (BasisKind.declsA_sstep a5.ok q5)
  obtain ⟨_, u6, q6, w6⟩ := AM.bind_ok w5
  have a7 := a6.trans (BasisKind.decls_sstep a6.ok q6)
  obtain ⟨_, u7, q7, w7⟩ := AM.bind_ok w6
  have a8 := a7.trans (BasisKind.declsA_sstep a7.ok q7)
  obtain ⟨_, u8, q8, w8⟩ := AM.bind_ok w7
  have a9 := a8.trans (BasisKind.decls_sstep a8.ok q8)
  obtain ⟨_, u9, q9, w9⟩ := AM.bind_ok w8
  have a10 := a9.trans (BasisKind.declsA_sstep a9.ok q9)
  obtain ⟨_, u10, q10, w10⟩ := AM.bind_ok w9
  have a11 := a10.trans (internCI_fresh a10.ok q10).1
  obtain ⟨_, u11, q11, w11⟩ := AM.bind_ok w10
  have a12 := a11.trans (internCI_fresh a11.ok q11).1
  obtain ⟨_, u12, q12, w12⟩ := AM.bind_ok w11
  have a13 := a12.trans (internCI_fresh a12.ok q12).1
  obtain ⟨_, u13, q13, w13⟩ := AM.bind_ok w12
  have a14 := a13.trans (internCI_fresh a13.ok q13).1
  obtain ⟨_, u14, q14, w14⟩ := AM.bind_ok w13
  have a15 := a14.trans (internCI_fresh a14.ok q14).1
  obtain ⟨_, u15, q15, w15⟩ := AM.bind_ok w14
  have a16 := a15.trans (internCI_fresh a15.ok q15).1
  obtain ⟨_, u16, q16, w16⟩ := AM.bind_ok w15
  have a17 := a16.trans (internCV_fresh a16.ok q16).1
  obtain ⟨_, u17, q17, w17⟩ := AM.bind_ok w16
  have a18 := a17.trans (internCV_fresh a17.ok q17).1
  obtain ⟨_, u18, q18, w18⟩ := AM.bind_ok w17
  have a19 := a18.trans (internCV_fresh a18.ok q18).1
  obtain ⟨_, u19, q19, w19⟩ := AM.bind_ok w18
  have a20 := a19.trans (internCV_fresh a19.ok q19).1
  obtain ⟨_, u20, q20, w20⟩ := AM.bind_ok w19
  have a21 := a20.trans (internCV_fresh a20.ok q20).1
  obtain ⟨_, u21, q21, w21⟩ := AM.bind_ok w20
  have a22 := a21.trans (internCV_fresh a21.ok q21).1
  obtain ⟨_, u22, q22, w22⟩ := AM.bind_ok w21
  have a23 := a22.trans (internCV_fresh a22.ok q22).1
  obtain ⟨_, u23, q23, w23⟩ := AM.bind_ok w22
  have a24 := a23.trans (internCV_fresh a23.ok q23).1
  obtain ⟨_, u24, q24, w24⟩ := AM.bind_ok w23
  have a25 := a24.trans (internCV_fresh a24.ok q24).1
  obtain ⟨_, u25, q25, w25⟩ := AM.bind_ok w24
  have a26 := a25.trans (internCV_fresh a25.ok q25).1
  obtain ⟨_, u26, q26, w26⟩ := AM.bind_ok w25
  have a27 := a26.trans (ConRon.Bridge.Frontend.internExpr_sstep a26.ok q26).1
  obtain ⟨_, u27, q27, w27⟩ := AM.bind_ok w26
  have a28 := a27.trans (ConRon.Bridge.Frontend.internExpr_sstep a27.ok q27).1
  obtain ⟨_, u28, q28, w28⟩ := AM.bind_ok w27
  have a29 := a28.trans (reservedBasisNames_sstep a28.ok (hpins.mono a28.ext a28.pins) q28)
  obtain ⟨_, u29, q29, w29⟩ := AM.bind_ok w28
  obtain ⟨rfl, -⟩ := natOpNames_run (hpins.mono a29.ext a29.pins) q29
  have a30 := a29
  obtain ⟨_, u30, q30, w30⟩ := AM.bind_ok w29
  obtain ⟨rfl, -⟩ := natDivModNames_run (hpins.mono a30.ext a30.pins) q30
  have a31 := a30
  obtain ⟨_, u31, q31, w31⟩ := AM.bind_ok w30
  obtain rfl := reduceOpNames_state (hpins.mono a31.ext a31.pins) q31
  have a32 := a31
  obtain ⟨_, u32, q32, w32⟩ := AM.bind_ok w31
  obtain ⟨p32, -⟩ := pinAt_run (x := ConLeche.sorryAxName) (hpins.mono a32.ext a32.pins) rfl q32
  rw [p32] at w32
  have a33 := a32
  obtain ⟨_, u33, q33, w33⟩ := AM.bind_ok w32
  obtain ⟨p33, -⟩ := pinAt_run (x := ConLeche.quotSoundName) (hpins.mono a33.ext a33.pins) rfl q33
  rw [p33] at w33
  obtain ⟨-, -, -, -, -, hpe, -, -⟩ :=
    internPinSets_run a33.ok (by rw [a33.scratch]; exact hoff) w33
  rw [hpe, a33.pins]

end pins

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
