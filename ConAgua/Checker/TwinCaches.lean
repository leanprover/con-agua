import ConAgua.Checker.PipeRest

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
    | split
    | simp only [])
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

end L.Checker.TwinCaches
