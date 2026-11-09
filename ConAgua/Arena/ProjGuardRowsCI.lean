module

public import ConAgua.Arena.IndSumSpec.StructUsedHb
public import ConAgua.Arena.Keeps
public import ConAgua.Arena.MemoBank
public import ConAgua.Arena.DeclLvlStage
import ConAgua.Arena.CoreRefine
public import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.IndSumSpec.StructProjArgP

@[expose] public section

/-!
# Stage refinements under `CoreS`: the cache swap

The stage's refinements (`StageR`, whose `CheckR.core` is the core tier outside the eager tower)
lift to `CoreS` at any eager bit for a twin op that does not read the caches:

* `CI op`: a successful run of `op` stays a successful run, with the same result, after the
  caches are replaced (`CI.bind`, `CI.pure`, the store/memo primitives, `ci_auto` for a walk's
  `succ` case);
* `CoreS.swapCaches`: from `CoreS` at any maps and eager bit, the twin state with the caches
  rebuilt from the memory's maps (`bankOf`: the banks of generation `0` and `1`) is `CheckR`.

So a `StageR` theorem run at the swapped state gives the twin's run at the real state (`CI`).
Used for `strip_pis` and `has_loose_b_var_b_fast` (`struct_used_later`), reached by the core's
`proj_guard_rows`.
-/

open ConRon.Arena

namespace L.Arena

/-! ## The bank of a generation -/

section bank
variable {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]

/-- The bank of generation `g` of a generation-tagged map. -/
def bankOf (M : Std.HashMap (κ × Word) ν) (g : Word) : Std.HashMap κ ν :=
  Std.HashMap.ofList (M.toList.filterMap fun p => if p.1.2 = g then some (p.1.1, p.2) else none)

theorem bank_bankOf (M : Std.HashMap (κ × Word) ν) (g : Word) : Bank M g (bankOf M g) := by
  intro k
  unfold bankOf
  have hd : (M.toList.filterMap fun p => if p.1.2 = g then some (p.1.1, p.2) else none).Pairwise
      (fun a b => (a.1 == b.1) = false) := by
    refine List.Pairwise.filterMap _ ?_ (Std.HashMap.distinct_keys_toList (m := M))
    intro x y hxy b hb b' hb'
    by_cases hx : x.1.2 = g <;> by_cases hy : y.1.2 = g <;> simp [hx, hy] at hb hb'
    subst hb hb'
    simp only [beq_eq_false_iff_ne, ne_eq] at hxy ⊢
    intro e; apply hxy; exact Prod.ext e (hx.trans hy.symm)
  cases h : M[(k, g)]? with
  | some v =>
    have hm : ((k, g), v) ∈ M.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
    exact Std.HashMap.getElem?_ofList_of_mem (k := k) (BEq.rfl) hd
      (List.mem_filterMap.mpr ⟨((k, g), v), hm, by simp⟩)
  | none =>
    apply Std.HashMap.getElem?_ofList_of_contains_eq_false
    apply Bool.eq_false_iff.mpr
    intro hc
    have hx := List.contains_iff_mem.mp hc
    simp only [List.mem_map, List.mem_filterMap] at hx
    obtain ⟨⟨k', v⟩, ⟨⟨⟨k'', g'⟩, v'⟩, hm, hf⟩, hk⟩ := hx
    by_cases hg : g' = g
    · simp only [hg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only at hk; subst hk; subst hg
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm] at h; cases h
    · simp [hg] at hf

end bank

/-! ## The caches rebuilt from the memory's maps -/

/-- The six mode tables of generation `g` of the maps. -/
def ModeMaps.bank (M : ModeMaps) (g : Word) : ModeMemos :=
  ⟨bankOf M.wc g, bankOf M.wk g, bankOf M.wh g, bankOf M.inf g, bankOf M.io g, bankOf M.de g⟩

/-- The caches outside the eager tower whose mode tables are the maps' banks `0` (plain) and
`1` (stored eager tables); the other tables kept. -/
def swapC (c : Caches) (M : ModeMaps) : Caches :=
  { c with whnfCoreC := bankOf M.wc 0, whnfCoreCheapC := bankOf M.wk 0, whnfC := bankOf M.wh 0,
           inferC := bankOf M.inf 0, inferIOC := bankOf M.io 0, defeqC := bankOf M.de 0,
           eagerMemos := M.bank 1 }

theorem ModeR.swap {κ ν : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] {S : MemoSch}
    {K : MemoKey (κ × Word)} {VR : Mem → Word → ν → Prop} {m : Mem} {M : Std.HashMap (κ × Word) ν}
    {eb : Word} {t te : Std.HashMap κ ν} (h : ModeR S K VR m M eb t te) :
    ModeR S K VR m M 0 (bankOf M 0) (bankOf M 1) :=
  ⟨h.memo, bank_bankOf M 0, fun _ => bank_bankOf M 1, fun h => absurd rfl h⟩

theorem CoreRM.swap {m : Mem} {c : Caches} {M : ModeMaps} {eb : Word} (h : CoreRM m c M eb) :
    CoreRM m (swapC c M) M 0 :=
  ⟨h.wc.swap, h.wk.swap, h.wh.swap, h.inf.swap, h.io.swap, h.de.swap, by decide, h.ct, h.cv, h.rr,
    h.lq, h.lsq⟩

/-- **`CoreS` at any maps and eager bit is `CheckR` at the swapped caches.** -/
theorem CoreS.swapCheck {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) :
    CheckR m { a with caches := swapC a.caches M } vis fe :=
  ⟨hS.arena.caches_irrel _, ⟨M, hS.core.swap⟩, ⟨fun _ => hS.pins⟩, hS.env, hS.mode⟩

/-! ## Twin ops that do not read the caches -/

/-- A successful run stays one, with the same result, when the caches are replaced. -/
@[irreducible] def CI {α : Type} (op : AM α) : Prop :=
  ∀ (a : AState) (x : α) (a' : AState) (c : Caches), op.run a = .ok (x, a') →
    op.run { a with caches := c } = .ok (x, { a' with caches := c })

theorem CI.run {α : Type} {op : AM α} (h : CI op) {a : AState} {x : α} {a' : AState}
    (hr : op.run a = .ok (x, a')) (c : Caches) :
    op.run { a with caches := c } = .ok (x, { a' with caches := c }) := by
  unfold CI at h; exact h a x a' c hr

/-- Back from a run at swapped caches. -/
theorem CI.back {α : Type} {op : AM α} (h : CI op) {a : AState} {c : Caches} {x : α} {a' : AState}
    (hr : op.run { a with caches := c } = .ok (x, a')) :
    op.run a = .ok (x, { a' with caches := a.caches }) := by
  have := h.run hr a.caches
  simpa using this

theorem CI.pure {α : Type} (x : α) : CI (Pure.pure x : AM α) := by
  unfold CI; intro a r a' c h; cases h; rfl

theorem CI.fail {α : Type} (e : CheckError) : CI (ConRon.Arena.fail e : AM α) := by
  unfold CI; intro a r a' c h; cases h

theorem CI.bind {α γ : Type} {x : AM α} {f : α → AM γ} (hx : CI x) (hf : ∀ v, CI (f v)) :
    CI (x >>= f) := by
  unfold CI at *; intro a r a' c h
  simp only [StateT.run_bind] at h ⊢
  cases h1 : x.run a with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨v, a₁⟩ := p
    rw [h1] at h
    rw [hx a v a₁ c h1]
    exact hf v a₁ r a' c h

/-- A primitive: read the state, then answer, fail, or write back with only the store or the
memos changed. -/
macro "prim_ci " d:ident : tactic => `(tactic| (
  unfold CI; intro a r a' c h
  simp only [$d:ident, StateT.run_bind, StateT.run_get, pure_bind] at h ⊢
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | (simp only [throwThe, throw, Functor.map, Except.map, ConRon.Arena.fail, MonadExceptOf.throw] at h; cases h)
    | (exfalso; revert h; simp [throwThe, throw, Functor.map, Except.map, ConRon.Arena.fail])
    | simp_all [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        ConRon.Arena.fail, throwThe, MonadExceptOf.throw]))

theorem ci_view (h : EIdx) : CI (view h) := by prim_ci view
theorem ci_viewBind (h : EIdx) : CI (viewBind h) := by prim_ci viewBind
theorem ci_derivedE (h : EIdx) : CI (derivedE h) := by prim_ci derivedE
theorem ci_bvarBGet (k : EIdx) : CI (bvarBGet k) := by prim_ci bvarBGet
theorem ci_bvarBSet (k : EIdx) (v : Nat) : CI (bvarBSet k v) := by prim_ci bvarBSet
theorem ci_bvarBClear : CI bvarBClear := by prim_ci bvarBClear

/-- **One step of a walk family's `succ` case**: split binds, `if`s and `match`es, unfold the
named arms, close leaves by the primitives and the induction hypothesis `ih`. -/
macro "ci_auto " "[" arms:ident,* "]" " using " ih:term : tactic => `(tactic| (
  repeat' (first
    | exact CI.pure _ | exact CI.fail _ | exact $ih _ _ _ | exact $ih _ _ | exact $ih _
    | exact ci_view _ | exact ci_viewBind _ | exact ci_derivedE _
    | exact ci_bvarBGet _ | exact ci_bvarBSet _ _ | exact ci_bvarBClear
    | (unfold failDanglingE) | (dsimp only)
    | with_reducible apply CI.bind | intro _ | split $[| unfold $arms:ident]* )))

theorem ci_bvarBoundGo (F : Nat) : ∀ h, CI (bvarBoundGo F h) := by
  induction F with
  | zero => intro h; rw [bvarBoundGo_zero]; exact CI.fail _
  | succ F ih =>
    intro h; rw [bvarBoundGo_succ]
    ci_auto [bvarBoundArmApp, bvarBoundArmBind, bvarBoundArmLet] using ih

theorem ci_bvarBoundMemo (F : Nat) (e : EIdx) : CI (bvarBoundMemo F e) := by
  unfold bvarBoundMemo
  exact CI.bind ci_bvarBClear fun _ => CI.bind (ci_bvarBoundGo F e) fun _ =>
    CI.bind ci_bvarBClear fun _ => CI.pure _

theorem ci_bvarB (F : Nat) (e : EIdx) : CI (bvarB F e) := by
  unfold bvarB
  refine CI.bind (ci_derivedE _) fun x => ?_
  by_cases hc : ((ConLeche.bvarOfData x).toNat == ConLeche.satRange) = true
  · simp only [hc, ↓reduceIte]; exact ci_bvarBoundMemo F e
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact CI.pure _

theorem ci_hbGo (F : Nat) : ∀ (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat) (h : EIdx),
    CI (hasLooseBVarBGo memo i F h) := by
  induction F with
  | zero => intro memo i h; rw [hasLooseBVarBGo]; exact CI.fail _
  | succ F ih =>
    intro memo i h; rw [hasLooseBVarBGo]
    refine CI.bind (ci_bvarB _ _) fun bb => ?_
    ci_auto [] using ih

theorem ci_hbFast (i : Nat) (e : EIdx) : CI (hasLooseBVarBFast i e) := by
  unfold hasLooseBVarBFast
  exact CI.bind (ci_hbGo _ _ _ _) fun _ => CI.pure _

theorem ci_stripPis : ∀ (k : Nat) (h : EIdx), CI (stripPis k h) := by
  intro k
  induction k with
  | zero => intro h; rw [stripPis]; exact CI.pure _
  | succ k ih =>
    intro h; rw [stripPis]
    ci_auto [] using ih

theorem ci_structUsedLater (cty : EIdx) (nP j : Nat) : CI (structUsedLater cty nP j) := by
  unfold structUsedLater
  refine CI.bind (ci_stripPis _ _) fun x => ?_
  split
  · exact ci_hbFast _ _
  · exact CI.pure _

/-! ## The twin ops keep the store, the caches and the pins -/

theorem keepsSp_bvarB (F : Nat) (e : EIdx) : Keeps sp (bvarB F e) := by
  unfold bvarB
  refine Keeps.bind (keeps_derivedE _) fun x => ?_
  by_cases hc : ((ConLeche.bvarOfData x).toNat == ConLeche.satRange) = true
  · simp only [hc, ↓reduceIte]; exact keeps_bvarBoundMemo F e
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact Keeps.pure _

theorem keepsSp_hbGo (F : Nat) : ∀ (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat) (h : EIdx),
    Keeps sp (hasLooseBVarBGo memo i F h) := by
  induction F with
  | zero => intro memo i h; rw [hasLooseBVarBGo]; exact Keeps.fail _
  | succ F ih =>
    intro memo i h; rw [hasLooseBVarBGo]
    refine Keeps.bind (keepsSp_bvarB _ _) fun bb => ?_
    keeps_auto [] using (ih _), sp_blind

theorem keepsSp_stripPis : ∀ (k : Nat) (h : EIdx), Keeps sp (stripPis k h) := by
  intro k
  induction k with
  | zero => intro h; rw [stripPis]; exact Keeps.pure _
  | succ k ih =>
    intro h; rw [stripPis]
    keeps_auto [] using ih, sp_blind

theorem keepsSp_structUsedLater (cty : EIdx) (nP j : Nat) : Keeps sp (structUsedLater cty nP j) := by
  unfold structUsedLater
  refine Keeps.bind (keepsSp_stripPis _ _) fun x => ?_
  split
  · unfold hasLooseBVarBFast
    exact Keeps.bind (keepsSp_hbGo _ _ _ _) fun _ => Keeps.pure _
  · exact Keeps.pure _

end L.Arena

namespace L.Ind

open L.Arena

/-! ## `struct_used_later` under `CoreS` -/

theorem ustW_frameU {n : Nat} {m m' : Mem} {cty nP j r : Word} (h : ustW n m cty nP j = some (r, m')) :
    MemFrame usA usC m m' := by
  simp only [ustW] at h
  obtain ⟨rs, m1, hst, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  have h1 : MemFrame usA usC m m1 := (stripF_frame hst).mono (by simp [usA]) (by simp [usC])
  by_cases hz : rs.headD 0 = 0
  · rw [ustK1_some_zero hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact h1
  rw [ustK1_some_ne hz] at h
  exact h1.trans ((hbFastW_frame h).mono (by simp [usA, hbWA]) (by simp [usC, hbWC]))

/-- **`struct_used_later`'s model refines `structUsedLater` under `CoreS`**, the pool's `IWOK` and
the `hb` memo given: the stage refinement `ustW_ok` at the swapped caches (`CoreS.swapCheck`), the
twin's run back at the real caches (`CI`), `CoreS` after by the frame `usA`/`usC`. -/
theorem ustW_okC {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} (n : Nat) {m m' : Mem} {a : AState} {cty nP j r : Word}
    (hsum : nP.toNat + j.toNat + 1 < 2 ^ 64) (hc : H cty) (hS : CoreS dn m a vis fe M eb)
    (hI : IWOK m) (hM : ∃ mp, hbMR m mp) (h : ustW n m cty nP j = some (r, m')) :
    ∃ b a', (structUsedLater (decI cty) nP.toNat j.toNat).run a = .ok (b, a') ∧
      r = (if b then 1 else 0) ∧ (∃ mp, hbMR m' mp) ∧ CoreS dn m' a' vis fe M eb ∧
      StackKept m m' ∧ IWOK m' ∧ IWGrow m m' ∧ a'.store = a.store := by
  obtain ⟨mp, hM⟩ := hM
  obtain ⟨b, a1, hrun, hb, hM', hS1, hg⟩ := ustW_ok (vis := vis) (fe := fe) n m m'
    { a with caches := swapC a.caches M } cty nP j r mp hsum hc ⟨hS.swapCheck, hI⟩ hM h
  have hrun' := (ci_structUsedLater _ _ _).back hrun
  have hk := (keepsSp_structUsedLater _ _ _).run hrun
  simp only [sp, Prod.mk.injEq] at hk
  obtain ⟨hst, -, hpi⟩ := hk
  have hf := ustW_frameU h
  have hcpl : cpl { a1 with caches := a.caches } = cpl a := by
    simp only [cpl, hst, hpi]
  refine ⟨b, _, hrun', hb, hM', ?_, StackKept.of_frame hf, hS1.iw, hg, hst⟩
  exact hS.arena_frame (hS1.check.arena.caches_irrel _) hcpl hf
    (by intro b hb; simp only [usA, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> decide)
    (by simp only [usA]; decide)
    (by intro b hb; simp only [usA, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> decide)
    (by intro x hx; simp only [usC, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro x hx; simp only [usC, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)

end L.Ind
