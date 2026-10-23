import ConAgua.Checker.HoistRefBase

/-!
# The hoist's walk refines `usedConsts` (lane `front4`)

`hoist_walk` and its arms, `hoist_rules_go`, `hoist_block_go`, `hoist_deps_of` against
`usedConstsGo`, `usedConstsRules`, `usedConstsBlock`, `IDeclaration.usedConsts`
(`ConRon/Arena/Frontend/NatOpGround.lean`). The twin collects the names a record references into an
array; L hands each to `hoist_note` as the walk finds it. The statements say: when L returns, the
twin returns (in the same state) the names `ns` (as words, `decI`), and L's memory is that of
`notesW` over `ns` except the visited set (`HSEEN`, `CTL[73‥74]`), which represents the twin's.
The walk counter `fu` is the twin's fuel exactly.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- **The notes commute with the visited set's writes.** -/
theorem notesW_frame {m₁ m₂ x₁ : Mem} {i k tg ws sp sp' : Word} {ns : List Word}
    (hf : MemFrame [HSEEN] [73, 74] m₁ m₂) (h : notesW m₁ i k tg ws sp ns = some (sp', x₁)) :
    ∃ x₂, notesW m₂ i k tg ws sp ns = some (sp', x₂) ∧ MemFrame [HSEEN] [73, 74] x₁ x₂ := by
  sorry

/-- **`hoist_walk` refines `usedConstsGo`.** -/
theorem hoistWalk_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (e i k tg ws sp fu sp' : Word) (seen : Std.HashSet EIdx)
      (acc : Array NIdx),
    ArenaR m a → e.toNat < 2 ^ 32 → SeenR m seen →
    hWalkW n m e i k tg ws sp fu = some (sp', m') →
    ∃ (seen' : Std.HashSet EIdx) (ns : List Word),
      (usedConstsGo seen acc fu.toNat (decE e)).run a = .ok ((seen', acc ++ (ns.map decI).toArray), a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ SeenR m' seen' ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  sorry

/-- The rules `rules` are the eleven-word records at `DIND[ro + 11 r ..]`, right-hand sides at
`+ 8`. -/
def RulesAt (m : Mem) (ro r : Word) (rules : List IRecRule) : Prop :=
  ∀ q (h : q < rules.length),
    (rdW (m.arr64 DIND) (ro + 11 * (r + UInt64.ofNat q) + 8)).toNat < 2 ^ 32 ∧
    rules[q].rhs = decE (rdW (m.arr64 DIND) (ro + 11 * (r + UInt64.ofNat q) + 8))

/-- **`hoist_rules_go` refines `usedConstsRules`.** -/
theorem hoistRulesGo_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k i tg ws sp ro rc r sp' : Word) (seen : Std.HashSet EIdx)
      (acc : Array NIdx) (rules : List IRecRule),
    ArenaR m a → SeenR m seen → r.toNat + rules.length = rc.toNat → RulesAt m ro r rules →
    hRulesGoW n m k i tg ws sp ro rc r = some (sp', m') →
    ∃ (seen' : Std.HashSet EIdx) (ns : List Word),
      (usedConstsRules seen acc rules).run a = .ok ((seen', acc ++ (ns.map decI).toArray), a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ SeenR m' seen' ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  sorry

/-- The block members `cs` are the constant records the pointers `DIND[o + q ‥ o + c)` point to
(`decCIs` below some `t` at most the pool's top, as `IndDeclAt`), none of them a projection table
(a parsed block has none). -/
def BlockAt (m : Mem) (o c q : Word) (cs : List IConstantInfo) : Prop :=
  (∃ t, t ≤ ((m.arr64 DLP)[0]?.getD 0).toNat ∧
    decCIs (trunc (m.arr64 DLP) t) (fun _ => none) (o.toNat + q.toNat) (c.toNat - q.toNat) = some cs) ∧
  o.toNat + c.toNat < 2 ^ 63 ∧ q ≤ c ∧ ∀ ci ∈ cs, ci.isTowerEntry = false

/-- **`hoist_block_go` refines `usedConstsBlock`.** -/
theorem hoistBlockGo_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k i tg ws sp o c q sp' : Word) (seen : Std.HashSet EIdx)
      (acc : Array NIdx) (cs : List IConstantInfo),
    ArenaR m a → SeenR m seen → BlockAt m o c q cs →
    hBlockGoW n m k i tg ws sp o c q = some (sp', m') →
    ∃ (seen' : Std.HashSet EIdx) (ns : List Word),
      (usedConstsBlock seen acc cs).run a = .ok ((seen', acc ++ (ns.map decI).toArray), a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ SeenR m' seen' ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  sorry

/-- A record the hoist can walk: an inductive block has no projection table. -/
def WalkableDecl : IDeclaration → Prop
  | .indDecl b _ => ∀ ci ∈ b, ci.isTowerEntry = false
  | _ => True

/-- **`hoist_deps_of` refines `IDeclaration.usedConsts`** (record `r` of `DECL`, `x = 1 + 8 r`). -/
theorem hoistDepsOf_ok (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (k i r tg ws sp sp' : Word) (d : IDeclaration),
    ArenaR m a → (∃ seen, SeenR m seen) → r.toNat < 2 ^ 59 →
    DeclAtF (m.arr64 DECL) (m.arr64 DLP) r.toNat d → RecOK (m.arr64 DECL) r.toNat → WalkableDecl d →
    hDepsOfW n m k i (1 + 8 * r) tg ws sp = some (sp', m') →
    ∃ ns : List Word,
      (IDeclaration.usedConsts d).run a = .ok ((ns.map decI).toArray, a) ∧
      (∀ w ∈ ns, w.toNat < 2 ^ 32) ∧ (∃ seen', SeenR m' seen') ∧
      ∃ mn, notesW m i k tg ws sp ns = some (sp', mn) ∧ MemFrame [HSEEN] [73, 74] mn m' := by
  sorry

end L.Checker
