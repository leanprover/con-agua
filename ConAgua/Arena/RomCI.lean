import ConAgua.Arena.RomItems
import ConAgua.Arena.Keeps
import ConRon.Arena.Checker
import ConAgua.Census.Attr

/-!
# The twin's constant interners have the store effect of their item streams

`Sim x m is proj`: whenever the items `is` run from memo `m` (`runItems`), the twin's `x` runs to
the same state, and `proj` of its result is the memo after. So `rom_items` at the encoding of
`is` refines `x`'s **store effect** (`refines_part … "the store effect"`: the result values,
`IConstantInfo`s and lists of handles, are not built in L; their consumers will read records).

Items of: `internNameList`, `internLevelList`, `internExprList`, `internCV`, `internCaps`,
`internFire`, `internRule(s)`, `internCI`, `internCIList`, and the `Arena` wrappers at a fresh
memo (`internExpr`, `internCV`, `internCI`, `internCIList`: a `reset` first).
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena

/-- The twin's `x` has the store effect of the items `is` from memo `m`. -/
def Sim {α : Type} (x : AM α) (m : EMemo) (is : List Item) (proj : α → EMemo) : Prop :=
  ∀ a m' a', (runItems m is).run a = .ok (m', a') → ∃ v, x.run a = .ok (v, a') ∧ proj v = m'

theorem runItems_append (m : EMemo) (is js : List Item) (a : AState) (m'' : EMemo) (a'' : AState)
    (h : (runItems m (is ++ js)).run a = .ok (m'', a'')) :
    ∃ m' a', (runItems m is).run a = .ok (m', a') ∧ (runItems m' js).run a' = .ok (m'', a'') := by
  induction is generalizing m a with
  | nil => exact ⟨m, a, rfl, h⟩
  | cons i is ih =>
    simp only [List.cons_append, runItems] at h ⊢
    rw [StateT.run_bind] at h
    cases hi : (runItem m i).run a with
    | error e => rw [hi] at h; cases h
    | ok p =>
      obtain ⟨m₁, a₁⟩ := p
      rw [hi] at h
      obtain ⟨m', a', h1, h2⟩ := ih m₁ a₁ h
      exact ⟨m', a', by rw [run_bind_of _ _ _ _ _ hi]; exact h1, h2⟩

theorem Sim.pure {α : Type} (v : α) (m : EMemo) (proj : α → EMemo) (hp : proj v = m) :
    Sim (Pure.pure v : AM α) m [] proj := by
  intro a m' a' h
  simp only [runItems] at h
  cases h
  exact ⟨v, rfl, hp⟩

theorem Sim.bind {α β : Type} {x : AM α} {f : α → AM β} {m : EMemo} {is js : List Item}
    {p₁ : α → EMemo} {p₂ : β → EMemo} (hx : Sim x m is p₁) (hf : ∀ v, Sim (f v) (p₁ v) js p₂) :
    Sim (x >>= f) m (is ++ js) p₂ := by
  intro a m'' a'' h
  obtain ⟨m', a', h1, h2⟩ := runItems_append m is js a m'' a'' h
  obtain ⟨v, hv, hp⟩ := hx a m' a' h1
  subst hp
  obtain ⟨w, hw, hq⟩ := hf v a' m'' a'' h2
  exact ⟨w, by rw [run_bind_of _ _ _ _ _ hv]; exact hw, hq⟩

theorem Sim.congr {α : Type} {x : AM α} {m : EMemo} {is js : List Item} {p : α → EMemo}
    (h : Sim x m is p) (e : is = js) : Sim x m js p := e ▸ h

/-! ## The primitives -/

theorem sim_one {α : Type} (x : AM α) (p : α → EMemo) (m : EMemo) (i : Item)
    (h : runItem m i = x >>= fun r => pure (p r)) : Sim x m [i] p := by
  intro a m' a' hr
  simp only [runItems] at hr
  rw [StateT.run_bind, h, StateT.run_bind] at hr
  cases hn : x.run a with
  | error e => rw [hn] at hr; cases hr
  | ok q =>
    obtain ⟨v, a₁⟩ := q
    rw [hn] at hr
    simp only [bind, Except.bind, pure, Except.pure, StateT.run_pure] at hr
    cases hr
    exact ⟨v, rfl, rfl⟩

theorem sim_name (n : ConLeche.Name) (m : EMemo) : Sim (internName n) m [.nm n] (fun _ => m) :=
  sim_one _ _ _ _ rfl
theorem sim_level (u : ConLeche.Level) (m : EMemo) : Sim (internLevel u) m [.lv u] (fun _ => m) :=
  sim_one _ _ _ _ rfl
theorem sim_expr (e : ConLeche.Expr) (m : EMemo) : Sim (internExprGo m e) m [.ex e] Prod.fst :=
  sim_one _ _ _ _ rfl

/-! ## Lists and constants -/

theorem sim_nameList (ns : List ConLeche.Name) (m : EMemo) :
    Sim (Frontend.internNameList ns) m (ns.map .nm) (fun _ => m) := by
  induction ns with
  | nil => exact Sim.pure _ _ _ rfl
  | cons n ns ih =>
    have e : Frontend.internNameList (n :: ns) =
        internName n >>= fun h => Frontend.internNameList ns >>= fun hs => pure (h :: hs) := rfl
    rw [e]
    exact (Sim.bind (sim_name n m) fun _ => Sim.bind ih fun _ => Sim.pure _ _ _ rfl).congr (by simp)

theorem sim_levelList (us : List ConLeche.Level) (m : EMemo) :
    Sim (internLevelList us) m (us.map .lv) (fun _ => m) := by
  induction us with
  | nil => exact Sim.pure _ _ _ rfl
  | cons u us ih =>
    have e : internLevelList (u :: us) =
        internLevel u >>= fun h => internLevelList us >>= fun hs => pure (h :: hs) := rfl
    rw [e]
    exact (Sim.bind (sim_level u m) fun _ => Sim.bind ih fun _ => Sim.pure _ _ _ rfl).congr (by simp)

theorem sim_exprList (es : List ConLeche.Expr) : ∀ (m : EMemo),
    Sim (Frontend.internExprList m es) m (es.map .ex) Prod.fst := by
  induction es with
  | nil => intro m; exact Sim.pure _ _ _ rfl
  | cons e es ih =>
    intro m
    have h : Frontend.internExprList m (e :: es) =
        internExprGo m e >>= fun r => match r with
          | (m, h) => Frontend.internExprList m es >>= fun r' => match r' with
            | (m, hs) => pure (m, h :: hs) := rfl
    rw [h]
    refine (Sim.bind (is := [.ex e]) (js := es.map .ex) (sim_expr e m) fun r => ?_).congr (by simp)
    obtain ⟨m₁, h₁⟩ := r
    refine (Sim.bind (is := es.map .ex) (js := []) (ih m₁) fun r' => ?_).congr (by simp)
    obtain ⟨m₂, hs⟩ := r'
    exact Sim.pure _ _ _ rfl

/-- A constant value's items. -/
def itemsCV (cv : ConLeche.ConstantVal) : List Item :=
  .nm cv.name :: (cv.levelParams.map .nm ++ [.ex cv.type])

theorem sim_cv (cv : ConLeche.ConstantVal) (m : EMemo) :
    Sim (Frontend.internCV m cv) m (itemsCV cv) Prod.fst := by
  have h : Frontend.internCV m cv =
      internName cv.name >>= fun n => Frontend.internNameList cv.levelParams >>= fun lps =>
        internExprGo m cv.type >>= fun r => match r with | (m, ty) => pure (m, ⟨n, lps, ty⟩) := rfl
  rw [h]
  refine (Sim.bind (is := [.nm cv.name]) (js := cv.levelParams.map .nm ++ [.ex cv.type])
    (sim_name _ m) fun n => ?_).congr (by simp [itemsCV])
  refine (Sim.bind (is := cv.levelParams.map .nm) (js := [.ex cv.type]) (sim_nameList _ m) fun lps => ?_)
  refine (Sim.bind (is := [.ex cv.type]) (js := []) (sim_expr _ m) fun r => ?_).congr (by simp)
  obtain ⟨m₁, ty⟩ := r
  exact Sim.pure _ _ _ rfl

/-- An inductive's capabilities' items. -/
def itemsCaps (c : ConLeche.IndCaps) : List Item := .nm c.etaCtor :: (c.all.map .nm ++ c.ctors.map .nm)

theorem sim_caps (c : ConLeche.IndCaps) (m : EMemo) : Sim (internCaps c) m (itemsCaps c) (fun _ => m) := by
  have h : internCaps c = internName c.etaCtor >>= fun ct => Frontend.internNameList c.all >>= fun all =>
      Frontend.internNameList c.ctors >>= fun ctors =>
        pure ⟨c.eta, ct, c.etaParams, c.etaFields, c.unitlike, c.unitParams, c.ruleK, c.sortZ, all,
          c.nparams, ctors⟩ := rfl
  rw [h]
  exact (Sim.bind (is := [.nm c.etaCtor]) (js := c.all.map .nm ++ (c.ctors.map .nm ++ [])) (sim_name _ m) fun _ =>
    Sim.bind (is := c.all.map .nm) (js := c.ctors.map .nm ++ []) (sim_nameList _ m) fun _ =>
    Sim.bind (is := c.ctors.map .nm) (js := []) (sim_nameList _ m) fun _ => Sim.pure _ _ _ rfl).congr
    (by simp [itemsCaps])

/-- A firing mode's items. -/
def itemsFire : ConLeche.RecRuleFire → List Item
  | .plain => []
  | .nested lvls pins => lvls.map .lv ++ pins.map .ex

theorem sim_fire (f : ConLeche.RecRuleFire) (m : EMemo) : Sim (internFire m f) m (itemsFire f) Prod.fst := by
  cases f with
  | plain => exact Sim.pure _ _ _ rfl
  | nested lvls pins =>
    have h : internFire m (.nested lvls pins) = internLevelList lvls >>= fun hls =>
        Frontend.internExprList m pins >>= fun r => match r with | (m, hps) => pure (m, .nested hls hps) := rfl
    rw [h]
    refine (Sim.bind (is := lvls.map .lv) (js := pins.map .ex) (sim_levelList _ m) fun _ => ?_).congr (by simp [itemsFire])
    refine (Sim.bind (is := pins.map .ex) (js := []) (sim_exprList _ m) fun r => ?_).congr (by simp)
    obtain ⟨m₁, _⟩ := r
    exact Sim.pure _ _ _ rfl

/-- A recursor rule's items. -/
def itemsRule (rl : ConLeche.RecRule) : List Item := .nm rl.ctor :: (itemsFire rl.fire ++ [.ex rl.rhs])

theorem sim_rule (rl : ConLeche.RecRule) (m : EMemo) : Sim (internRule m rl) m (itemsRule rl) Prod.fst := by
  have h : internRule m rl = internName rl.ctor >>= fun c => internFire m rl.fire >>= fun r => match r with
      | (m, f) => internExprGo m rl.rhs >>= fun r' => match r' with
        | (m, rh) => pure (m, ⟨c, rl.nfields, rl.ctorParams, f, rh, rl.k, rl.eta⟩) := rfl
  rw [h]
  refine (Sim.bind (is := [.nm rl.ctor]) (js := itemsFire rl.fire ++ [.ex rl.rhs]) (sim_name _ m) fun _ => ?_).congr (by simp [itemsRule])
  refine Sim.bind (is := itemsFire rl.fire) (js := [.ex rl.rhs]) (sim_fire _ m) fun r => ?_
  obtain ⟨m₁, _⟩ := r
  refine (Sim.bind (is := [.ex rl.rhs]) (js := []) (sim_expr _ m₁) fun r' => ?_).congr (by simp)
  obtain ⟨m₂, _⟩ := r'
  exact Sim.pure _ _ _ rfl

/-- A rule list's items. -/
def itemsRules : List ConLeche.RecRule → List Item
  | [] => []
  | r :: rs => itemsRule r ++ itemsRules rs

theorem sim_rules (rs : List ConLeche.RecRule) : ∀ (m : EMemo), Sim (internRules m rs) m (itemsRules rs) Prod.fst := by
  induction rs with
  | nil => intro m; exact Sim.pure _ _ _ rfl
  | cons r rs ih =>
    intro m
    have h : internRules m (r :: rs) = internRule m r >>= fun x => match x with
        | (m, h) => internRules m rs >>= fun y => match y with | (m, hs) => pure (m, h :: hs) := rfl
    rw [h]
    refine Sim.bind (is := itemsRule r) (js := itemsRules rs) (sim_rule r m) fun x => ?_
    obtain ⟨m₁, _⟩ := x
    refine (Sim.bind (is := itemsRules rs) (js := []) (ih m₁) fun y => ?_).congr (by simp)
    obtain ⟨m₂, _⟩ := y
    exact Sim.pure _ _ _ rfl

/-- A constant's items (a projection table has none: no constant datum is one). -/
def itemsCI : ConLeche.ConstantInfo → List Item
  | .axiomInfo v => itemsCV v
  | .defnInfo v e _ => itemsCV v ++ [.ex e]
  | .thmInfo v => itemsCV v
  | .indInfo v c => itemsCV v ++ itemsCaps c
  | .ctorInfo v _ _ => itemsCV v
  | .recInfo v _ _ rs => itemsCV v ++ itemsRules rs

theorem sim_ci (ci : ConLeche.ConstantInfo) (m : EMemo) :
    Sim (Frontend.internCI m ci) m (itemsCI ci) Prod.fst := by
  cases ci with
  | axiomInfo v =>
    have h : Frontend.internCI m (.axiomInfo v) = Frontend.internCV m v >>= fun r => match r with
        | (m, cv) => pure (m, .axiomInfo cv) := rfl
    rw [h]
    refine (Sim.bind (is := itemsCV v) (js := []) (sim_cv v m) fun r => ?_).congr (by simp [itemsCI])
    obtain ⟨m₁, _⟩ := r; exact Sim.pure _ _ _ rfl
  | defnInfo v e hh =>
    have h : Frontend.internCI m (.defnInfo v e hh) = Frontend.internCV m v >>= fun r => match r with
        | (m, cv) => internExprGo m e >>= fun r' => match r' with | (m, x) => pure (m, .defnInfo cv x hh) := rfl
    rw [h]
    refine (Sim.bind (is := itemsCV v) (js := [.ex e]) (sim_cv v m) fun r => ?_).congr (by simp [itemsCI])
    obtain ⟨m₁, _⟩ := r
    refine (Sim.bind (is := [.ex e]) (js := []) (sim_expr e m₁) fun r' => ?_).congr (by simp)
    obtain ⟨m₂, _⟩ := r'; exact Sim.pure _ _ _ rfl
  | thmInfo v =>
    have h : Frontend.internCI m (.thmInfo v) = Frontend.internCV m v >>= fun r => match r with
        | (m, cv) => pure (m, .thmInfo cv) := rfl
    rw [h]
    refine (Sim.bind (is := itemsCV v) (js := []) (sim_cv v m) fun r => ?_).congr (by simp [itemsCI])
    obtain ⟨m₁, _⟩ := r; exact Sim.pure _ _ _ rfl
  | indInfo v c =>
    have h : Frontend.internCI m (.indInfo v c) = Frontend.internCV m v >>= fun r => match r with
        | (m, cv) => internCaps c >>= fun caps => pure (m, .indInfo cv caps) := rfl
    rw [h]
    refine (Sim.bind (is := itemsCV v) (js := itemsCaps c) (sim_cv v m) fun r => ?_).congr (by simp [itemsCI])
    obtain ⟨m₁, _⟩ := r
    exact (Sim.bind (is := itemsCaps c) (js := []) (sim_caps c m₁) fun _ => Sim.pure _ _ _ rfl).congr (by simp)
  | ctorInfo v nP nF =>
    have h : Frontend.internCI m (.ctorInfo v nP nF) = Frontend.internCV m v >>= fun r => match r with
        | (m, cv) => pure (m, .ctorInfo cv nP nF) := rfl
    rw [h]
    refine (Sim.bind (is := itemsCV v) (js := []) (sim_cv v m) fun r => ?_).congr (by simp [itemsCI])
    obtain ⟨m₁, _⟩ := r; exact Sim.pure _ _ _ rfl
  | recInfo v mI rP rs =>
    have h : Frontend.internCI m (.recInfo v mI rP rs) = Frontend.internCV m v >>= fun r => match r with
        | (m, cv) => internRules m rs >>= fun r' => match r' with | (m, rules) => pure (m, .recInfo cv mI rP rules) := rfl
    rw [h]
    refine (Sim.bind (is := itemsCV v) (js := itemsRules rs) (sim_cv v m) fun r => ?_).congr (by simp [itemsCI])
    obtain ⟨m₁, _⟩ := r
    refine (Sim.bind (is := itemsRules rs) (js := []) (sim_rules rs m₁) fun r' => ?_).congr (by simp)
    obtain ⟨m₂, _⟩ := r'; exact Sim.pure _ _ _ rfl

/-- A block's items. -/
def itemsCIs : List ConLeche.ConstantInfo → List Item
  | [] => []
  | c :: cs => itemsCI c ++ itemsCIs cs

theorem sim_ciList (cs : List ConLeche.ConstantInfo) :
    ∀ (m : EMemo), Sim (Frontend.internCIList m cs) m (itemsCIs cs) Prod.fst := by
  induction cs with
  | nil => intro m; exact Sim.pure _ _ _ rfl
  | cons c cs ih =>
    intro m
    have h : Frontend.internCIList m (c :: cs) = Frontend.internCI m c >>= fun x => match x with
        | (m, h) => Frontend.internCIList m cs >>= fun y => match y with | (m, hs) => pure (m, h :: hs) := rfl
    rw [h]
    refine Sim.bind (is := itemsCI c) (js := itemsCIs cs) (sim_ci c m) fun x => ?_
    obtain ⟨m₁, _⟩ := x
    refine (Sim.bind (is := itemsCIs cs) (js := []) (ih m₁) fun y => ?_).congr (by simp)
    obtain ⟨m₂, _⟩ := y
    exact Sim.pure _ _ _ rfl

/-! ## The interns keep the caches and the pins -/

theorem keeps_internNNode (v : NNodeView) : Keeps cp (internNNode v) := by prim_keeps internNNode
theorem keeps_internLNode (v : LNodeView) : Keeps cp (internLNode v) := by prim_keeps internLNode
theorem keeps_internLsNode (v : LsNodeView) : Keeps cp (internLsNode v) := by prim_keeps internLsNode

theorem keeps_internName (n : ConLeche.Name) : Keeps cp (internName n) := by
  induction n with
  | anonymous => exact keeps_internNNode _
  | str p s ih => exact Keeps.bind ih fun _ => keeps_internNNode _
  | num p k ih => exact Keeps.bind ih fun _ => keeps_internNNode _

theorem keeps_internLevel (u : ConLeche.Level) : Keeps cp (internLevel u) := by
  induction u with
  | zero => exact keeps_internLNode _
  | succ u ih => exact Keeps.bind ih fun _ => keeps_internLNode _
  | max u v ihu ihv => exact Keeps.bind ihu fun _ => Keeps.bind ihv fun _ => keeps_internLNode _
  | imax u v ihu ihv => exact Keeps.bind ihu fun _ => Keeps.bind ihv fun _ => keeps_internLNode _
  | param n => exact Keeps.bind (keeps_internName n) fun _ => keeps_internLNode _

theorem keeps_internLevelList (us : List ConLeche.Level) : Keeps cp (internLevelList us) := by
  induction us with
  | nil => exact Keeps.pure _
  | cons u us ih => exact Keeps.bind (keeps_internLevel u) fun _ => Keeps.bind ih fun _ => Keeps.pure _

theorem keeps_internLevels (us : List ConLeche.Level) : Keeps cp (internLevels us) :=
  Keeps.bind (keeps_internLevelList us) fun _ => keeps_internLsNode _

theorem keeps_internExprGo (e : ConLeche.Expr) : ∀ m : EMemo, Keeps cp (internExprGo m e) := by
  induction e with
  | bvar i => intro m; exact Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | sort u => intro m; exact Keeps.bind (keeps_internLevel u) fun _ => Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | const n us =>
    intro m
    exact Keeps.bind (keeps_internName n) fun _ => Keeps.bind (keeps_internLevels us) fun _ =>
      Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | lit l => intro m; exact Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | fvar i ty ih =>
    intro m
    simp only [internExprGo]
    split
    · exact Keeps.pure _
    · exact Keeps.bind (ih m) fun r => Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | app f a ihf iha =>
    intro m
    simp only [internExprGo]
    split
    · exact Keeps.pure _
    · exact Keeps.bind (ihf m) fun r => Keeps.bind (iha _) fun _ => Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | lam f a ihf iha =>
    intro m
    simp only [internExprGo]
    split
    · exact Keeps.pure _
    · exact Keeps.bind (ihf m) fun r => Keeps.bind (iha _) fun _ => Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | forallE f a ihf iha =>
    intro m
    simp only [internExprGo]
    split
    · exact Keeps.pure _
    · exact Keeps.bind (ihf m) fun r => Keeps.bind (iha _) fun _ => Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | letE t v b iht ihv ihb =>
    intro m
    simp only [internExprGo]
    split
    · exact Keeps.pure _
    · exact Keeps.bind (iht m) fun r => Keeps.bind (ihv _) fun _ => Keeps.bind (ihb _) fun _ =>
        Keeps.bind (keeps_internE _) fun _ => Keeps.pure _
  | proj n i sub ih =>
    intro m
    simp only [internExprGo]
    split
    · exact Keeps.pure _
    · exact Keeps.bind (keeps_internName n) fun _ => Keeps.bind (ih m) fun _ =>
        Keeps.bind (keeps_internE _) fun _ => Keeps.pure _

theorem keeps_runItems (is : List Item) : ∀ m : EMemo, Keeps cp (runItems m is) := by
  induction is with
  | nil => intro m; exact Keeps.pure _
  | cons i is ih =>
    intro m
    refine Keeps.bind ?_ fun m' => ih m'
    cases i with
    | nm n => exact Keeps.bind (keeps_internName n) fun _ => Keeps.pure _
    | lv u => exact Keeps.bind (keeps_internLevel u) fun _ => Keeps.pure _
    | lvs us => exact Keeps.bind (keeps_internLevels us) fun _ => Keeps.pure _
    | ex e => exact Keeps.bind (keeps_internExprGo e m) fun _ => Keeps.pure _
    | reset => exact Keeps.pure _

/-! ## Fresh-memo blocks and the startup walk -/

/-- The twin's `x` has the store effect of the block `.reset :: is`, from any memo, at states with
`P` (`P` reads only the caches and pins, which no intern changes). -/
def SimZ {α : Type} (x : AM α) (is : List Item) (P : AState → Prop) : Prop :=
  ∀ (m : EMemo) a m' a', P a → (runItems m (.reset :: is)).run a = .ok (m', a') → ∃ v, x.run a = .ok (v, a')

/-- `x` changes nothing and succeeds at `P`. -/
def SimN {α : Type} (x : AM α) (P : AState → Prop) : Prop := ∀ a, P a → ∃ v, x.run a = .ok (v, a)

theorem runItems_reset (m : EMemo) (is : List Item) (a : AState) :
    (runItems m (.reset :: is)).run a = (runItems ∅ is).run a := by
  simp only [runItems, runItem]; rw [run_bind_of _ _ _ _ _ rfl]

theorem SimZ.of_sim {α : Type} {x : AM α} {is : List Item} {p : α → EMemo} (h : Sim x ∅ is p)
    (P : AState → Prop) : SimZ x is P := by
  intro m a m' a' _ hr
  rw [runItems_reset] at hr
  obtain ⟨v, hv, -⟩ := h a m' a' hr
  exact ⟨v, hv⟩

theorem SimZ.map {α β : Type} {x : AM α} {is : List Item} {P : AState → Prop} (h : SimZ x is P)
    (g : α → β) : SimZ (x >>= fun v => pure (g v)) is P := by
  intro m a m' a' hP hr
  obtain ⟨v, hv⟩ := h m a m' a' hP hr
  exact ⟨g v, by rw [run_bind_of _ _ _ _ _ hv]; rfl⟩

/-- `P` depends only on the caches and the pins. -/
def CpPred (P : AState → Prop) : Prop := ∀ a a', cp a' = cp a → P a → P a'

theorem SimZ.bind {α β : Type} {x : AM α} {f : α → AM β} {is js : List Item} {P : AState → Prop}
    (hP : CpPred P) (hx : SimZ x is P) (hf : ∀ v, SimZ (f v) js P) :
    SimZ (x >>= f) (is ++ .reset :: js) P := by
  intro m a m'' a'' hPa hr
  have hr' : (runItems m ((.reset :: is) ++ (.reset :: js))).run a = .ok (m'', a'') := by simpa using hr
  obtain ⟨m', a', h1, h2⟩ := runItems_append m _ _ a m'' a'' hr'
  obtain ⟨v, hv⟩ := hx m a m' a' hPa h1
  have hPa' : P a' := hP a a' ((keeps_runItems _ m).run h1) hPa
  obtain ⟨w, hw⟩ := hf v m' a' m'' a'' hPa' h2
  exact ⟨w, by rw [run_bind_of _ _ _ _ _ hv]; exact hw⟩

theorem SimZ.bindN {α β : Type} {x : AM α} {f : α → AM β} {is : List Item} {P : AState → Prop}
    (hx : SimN x P) (hf : ∀ v, SimZ (f v) is P) : SimZ (x >>= f) is P := by
  intro m a m' a' hPa hr
  obtain ⟨v, hv⟩ := hx a hPa
  obtain ⟨w, hw⟩ := hf v m a m' a' hPa hr
  exact ⟨w, by rw [run_bind_of _ _ _ _ _ hv]; exact hw⟩

/-! The `Arena` wrappers, at a fresh memo. -/

theorem simZ_ci (ci : ConLeche.ConstantInfo) (P : AState → Prop) :
    SimZ (ConRon.Arena.internCI ci) (itemsCI ci) P :=
  (SimZ.of_sim (sim_ci ci ∅) P).map Prod.snd
theorem simZ_cv (cv : ConLeche.ConstantVal) (P : AState → Prop) :
    SimZ (ConRon.Arena.internCV cv) (itemsCV cv) P :=
  (SimZ.of_sim (sim_cv cv ∅) P).map Prod.snd
theorem simZ_ciList (cs : List ConLeche.ConstantInfo) (P : AState → Prop) :
    SimZ (ConRon.Arena.internCIList cs) (itemsCIs cs) P :=
  (SimZ.of_sim (sim_ciList cs ∅) P).map Prod.snd
theorem simZ_expr (e : ConLeche.Expr) (P : AState → Prop) :
    SimZ (ConRon.Arena.internExpr e) [.ex e] P :=
  (SimZ.of_sim (sim_expr e ∅) P).map Prod.snd
theorem simZ_exprList (es : List ConLeche.Expr) (P : AState → Prop) :
    SimZ (ConRon.Arena.internExprList es) (es.map .ex) P :=
  (SimZ.of_sim (sim_exprList es ∅) P).map Prod.snd

/-! ## The pin reads -/

/-- The pin table is filled (what every pin read needs). -/
def PinsReadyP (a : AState) : Prop := a.pins.names.size = 51

theorem pinsReady_cp : CpPred PinsReadyP := fun a a' h hP => by
  have : a'.pins = a.pins := congrArg Prod.snd h
  simp only [PinsReadyP, this] at hP ⊢; exact hP

theorem SimN.bind {α β : Type} {x : AM α} {f : α → AM β} {P : AState → Prop} (hx : SimN x P)
    (hf : ∀ v, SimN (f v) P) : SimN (x >>= f) P := by
  intro a hP
  obtain ⟨v, hv⟩ := hx a hP
  obtain ⟨w, hw⟩ := hf v a hP
  exact ⟨w, by rw [run_bind_of _ _ _ _ _ hv]; exact hw⟩

theorem SimN.pure {α : Type} (v : α) (P : AState → Prop) : SimN (Pure.pure v : AM α) P :=
  fun a _ => ⟨v, rfl⟩

theorem simN_pinAt (i : Nat) (hi : i < 51) : SimN (pinAt i) PinsReadyP := by
  intro a hP
  have : i < a.pins.names.size := by simp only [PinsReadyP] at hP; omega
  exact ⟨a.pins.names[i], by simp [pinAt, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, pure, StateT.pure, Except.pure, this]⟩

theorem simN_pinReserved : SimN pinReserved PinsReadyP := by
  intro a hP
  have : pinsReady a = true := by simp [pinsReady, pinCount, show a.pins.names.size = 51 from hP]
  exact ⟨a.pins.reserved, by simp [pinReserved, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, Except.bind, pure, StateT.pure, Except.pure, this]⟩

theorem simN_natOpNames : SimN natOpNames PinsReadyP := by
  unfold natOpNames natPredName natAddName natSubName natMulName natPowName natBeqName natBleName
  repeat (first | exact SimN.pure _ _ | refine SimN.bind (simN_pinAt _ (by decide)) fun _ => ?_)

theorem simN_natDivModNames : SimN natDivModNames PinsReadyP := by
  unfold natDivModNames natDivName natModName natGcdName natLandName natLorName natXorName
    natShiftLeftName natShiftRightName
  repeat (first | exact SimN.pure _ _ | refine SimN.bind (simN_pinAt _ (by decide)) fun _ => ?_)

theorem simN_reduceOpNames : SimN reduceOpNames PinsReadyP := by
  unfold reduceOpNames reduceNatName reduceBoolName
  repeat (first | exact SimN.pure _ _ | refine SimN.bind (simN_pinAt _ (by decide)) fun _ => ?_)

/-! ## The pin sets and the startup walk -/

/-- Blocks in sequence, each at a fresh memo. -/
def seqZ : List (List Item) → List Item
  | [] => []
  | [x] => x
  | x :: y :: xs => x ++ .reset :: seqZ (y :: xs)

theorem simZ_pure {α : Type} (v : α) (P : AState → Prop) : SimZ (Pure.pure v : AM α) [] P := by
  intro m a m' a' _ hr
  rw [runItems_reset] at hr
  simp only [runItems] at hr
  cases hr
  exact ⟨v, rfl⟩

/-- A type-pin list's items: per pin its name, then its type at a fresh memo. -/
def itemsTypePins : List (ConLeche.Name × ConLeche.Expr) → List Item
  | [] => []
  | p :: rest => seqZ [[.nm p.1], [.ex p.2], itemsTypePins rest, []]

theorem simZ_typePins (P : AState → Prop) (hP : CpPred P) :
    ∀ tps : List (ConLeche.Name × ConLeche.Expr), SimZ (internTypePins tps) (itemsTypePins tps) P
  | [] => simZ_pure _ _
  | p :: rest => by
    simp only [internTypePins, itemsTypePins, seqZ]
    exact SimZ.bind hP ((SimZ.of_sim (sim_name p.1 ∅) P)) fun _ =>
      SimZ.bind hP (simZ_expr _ _) fun _ => SimZ.bind hP (simZ_typePins P hP rest) fun _ => simZ_pure _ _

/-- A pin set's items. -/
def itemsPinSet (ps : ConLeche.NatOpPinSet) : List Item :=
  seqZ [[.ex ps.divPin], [.ex ps.modPin], [.ex ps.gcdPin], [.ex ps.landPin], [.ex ps.lorPin],
    [.ex ps.xorPin], [.ex ps.shiftLeftPin], [.ex ps.shiftRightPin],
    ps.divProofs.map .ex, ps.modProofs.map .ex, ps.gcdProofs.map .ex, ps.landProofs.map .ex,
    ps.lorProofs.map .ex, ps.xorProofs.map .ex, ps.shiftLeftProofs.map .ex, ps.shiftRightProofs.map .ex,
    itemsTypePins ps.divTypePins, itemsTypePins ps.modTypePins, itemsTypePins ps.gcdTypePins,
    itemsTypePins ps.landTypePins, itemsTypePins ps.lorTypePins, itemsTypePins ps.xorTypePins,
    itemsTypePins ps.shiftLeftTypePins, itemsTypePins ps.shiftRightTypePins, []]

theorem simZ_pinSet (ps : ConLeche.NatOpPinSet) : SimZ (internPinSet ps) (itemsPinSet ps) PinsReadyP := by
  unfold internPinSet internPinSetTypePins itemsPinSet
  simp only [seqZ]
  repeat (first
    | exact simZ_pure _ _
    | refine SimZ.bind pinsReady_cp (simZ_expr _ _) fun _ => ?_
    | refine SimZ.bind pinsReady_cp (simZ_exprList _ _) fun _ => ?_
    | refine SimZ.bind pinsReady_cp (simZ_typePins _ pinsReady_cp _) fun _ => ?_)

/-- The pin sets' items. -/
def itemsPinSets : List ConLeche.NatOpPinSet → List Item
  | [] => []
  | ps :: rest => seqZ [itemsPinSet ps, itemsPinSets rest, []]

theorem simZ_pinSets (pins : List ConLeche.NatOpPinSet) :
    SimZ (internPinSets pins) (itemsPinSets pins) PinsReadyP := by
  induction pins with
  | nil => exact simZ_pure _ _
  | cons ps rest ih =>
    have h : internPinSets (ps :: rest) =
        internPinSet ps >>= fun h => internPinSets rest >>= fun hs => pure (h :: hs) := rfl
    rw [h]
    simp only [itemsPinSets, seqZ]
    exact SimZ.bind pinsReady_cp (simZ_pinSet ps) fun _ =>
      SimZ.bind pinsReady_cp ih fun _ => simZ_pure _ _

/-- The startup walk's items: the basis blocks in both forms, the axiom shapes, the declaration
pins, the pin sets. -/
def itemsAllPins (pins : List ConLeche.NatOpPinSet) : List Item :=
  seqZ [itemsCIs (ConLeche.BasisKind.decls .eqK),
    itemsCIs (ConLeche.BasisKind.declsA .eqK),
    itemsCIs (ConLeche.BasisKind.decls .natK),
    itemsCIs (ConLeche.BasisKind.declsA .natK),
    itemsCIs (ConLeche.BasisKind.decls .emptyK),
    itemsCIs (ConLeche.BasisKind.declsA .emptyK),
    itemsCIs (ConLeche.BasisKind.decls .falseK),
    itemsCIs (ConLeche.BasisKind.declsA .falseK),
    itemsCIs (ConLeche.BasisKind.decls .quotK),
    itemsCIs (ConLeche.BasisKind.declsA .quotK),
    itemsCI ConLeche.iffA,
    itemsCI ConLeche.iffIntroA,
    itemsCI ConLeche.iffRecA,
    itemsCI ConLeche.nonemptyA,
    itemsCI ConLeche.nonemptyIntroA,
    itemsCI ConLeche.nonemptyRecA,
    itemsCV ConLeche.propextA,
    itemsCV ConLeche.choiceA,
    itemsCV ConLeche.trueCvA,
    itemsCV ConLeche.trueIntroCvA,
    itemsCV ConLeche.trustCompilerA,
    itemsCV ConLeche.boolCvA,
    itemsCV ConLeche.reduceNatCvA,
    itemsCV ConLeche.reduceBoolCvA,
    itemsCV ConLeche.ofReduceNatA,
    itemsCV ConLeche.ofReduceBoolA,
    [.ex ConLeche.reduceNatDeclPin],
    [.ex ConLeche.reduceBoolDeclPin],
    itemsPinSets pins]

/-- **The startup walk has the store effect of its items** (at a filled pin table). -/
theorem simZ_internAllPins (pins : List ConLeche.NatOpPinSet) :
    SimZ (internAllPins pins) (itemsAllPins pins) PinsReadyP := by
  unfold internAllPins itemsAllPins
  simp only [seqZ]
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ciList _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ci _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ci _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ci _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ci _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ci _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_ci _ _) fun _ => ?_
  repeat refine SimZ.bind pinsReady_cp (simZ_cv _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_expr _ _) fun _ => ?_
  refine SimZ.bind pinsReady_cp (simZ_expr _ _) fun _ => ?_
  refine SimZ.bindN simN_pinReserved fun _ => ?_
  refine SimZ.bindN simN_natOpNames fun _ => ?_
  refine SimZ.bindN simN_natDivModNames fun _ => ?_
  refine SimZ.bindN simN_reduceOpNames fun _ => ?_
  refine SimZ.bindN (simN_pinAt _ (by decide)) fun _ => ?_
  refine SimZ.bindN (simN_pinAt _ (by decide)) fun _ => ?_
  exact simZ_pinSets pins

/-! ## `intern_all_pins()` -/

/-- `intern_all_pins_rom()` (the ROM-only pin stage, superseded by `L.Rom.internAllPinsPB`) for the ROM offset `off` of the startup walk's item stream.
con-ron: none — the offset-generic body of `internAllPinsL` (`Prelude.lean`, which cites the twin). -/
def internAllPinsAt (off : Word) : FunDecl := lfn () locals (q, z) {
  CTL.u64[132] := 0;
  z := call rset_clear();
  q := call rom_items(⟪off⟫);
  return 0
}

theorem MemoR.fresh (mem : Mem) (hc : 132 < (mem.arr64 CTL).size) : MemoR (resetMem mem) [] (∅ : EMemo) := by
  have hf := resetMem_frame1 mem
  have hc0 : memoCnt (resetMem mem) = 0 := by
    simp only [memoCnt, resetMem, mclearG, rsetSch, rdW_set64]
    simp [hc]
  refine ⟨by rw [hc0]; rfl, fun k hk => by simp at hk, fun e he => by simp at he, by simp, ?_⟩
  rw [hf.2.2.1]; exact hc

set_option experimental.vcgen true in
theorem internAllPins_specW (rom : List UInt8) (off : Word) (p : Prog) (hL : ItemsProg rom p)
    (hp : p.lookup "intern_all_pins_rom" = some (internAllPinsAt off)) (n : Nat) (s₀ : St)
    (hs : pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_all_pins_rom" []
    ⦃fun _ s' => LocEq s' s₀ ∧ 132 < (s₀.mem.arr64 CTL).size ∧
      ∃ n' q, rclearOK s₀.mem ∧ romItemsW rom n' (resetMem s₀.mem) off = some (q, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internAllPinsAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hi := fun s₁ pos₁ h₁ => romItems_specW rom p hL n s₁ pos₁ h₁
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hi,
        memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n] <;>
      finish [resetMem, rclearOK, mclearG, rsetSch]

/-- **`intern_all_pins` refines `internAllPins`'s store effect**: with the item stream at `off`,
from `ArenaD` at a filled pin table, the twin's walk succeeds (at the same pin list) and `ArenaD`
holds after; the result (the interned pin variants) is not built in L. -/
@[refines_part ConRon.Arena.internAllPins "the store effect"]
theorem internAllPins_refines (rom : List UInt8) (off : Word) (p : Prog) (hL : ItemsProg rom p)
    (hp : p.lookup "intern_all_pins_rom" = some (internAllPinsAt off)) (hr : RomOK rom)
    (pins : List ConLeche.NatOpPinSet)
    (hfit : (itemsAllPins pins).all itemFits = true) (rest : List UInt8)
    (hd : rom.drop off.toNat = encItems [] (itemsAllPins pins) ++ rest)
    (n : Nat) (s₀ : St) (a₀ : AState) (hA : ArenaD s₀.mem a₀) (hmo : ModeOK s₀.mem) (hP : PinsReadyP a₀)
    (hst : (stkTop s₀.mem).toNat < 2 ^ 61) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_all_pins_rom" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ v a', (internAllPins pins).run a₀ = .ok (v, a') ∧ ArenaD s'.mem a' ∧
      MemFrame ExprA ExprC s₀.mem s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hc, n', q, -, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (internAllPins_specW rom off p hL hp n s₀ ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩)
  subst hs
  have hA' : ArenaD (resetMem s.mem) a₀ := ArenaD.frameHi (resetMem_frame1 _) (by simp) (by simp) hA
  obtain ⟨m', a', -, hrunI, hR, -, -, hf, -⟩ := romItemsW_ok rom hr _ hfit n' (resetMem s.mem) a₀ off rest []
    ∅ q s'.mem hA' ((memFrame_top (resetMem_frame1 s.mem) (by decide)).mode hA.1.lit.1 hmo) (MemoR.fresh s.mem hc) hd (by rw [resetMem_stk]; exact hst)
    (by rw [(resetMem_frame1 _).2.2.1]; omega) hW
  obtain ⟨v, hv⟩ := simZ_internAllPins pins ∅ a₀ m' a' hP (by rw [runItems_reset]; exact hrunI)
  exact ⟨hloc, v, a', hv, hR, (resetMem_frame _).trans hf⟩

end L.Rom
