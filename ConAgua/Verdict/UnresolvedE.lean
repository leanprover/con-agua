import ConAgua.Arena.StrLitSup
import ConAgua.Checker.NoVerdictFns
import ConAgua.Arena.Verdict
import ConAgua.Arena.IndSumSpec.McGoStep

/-!
# The verdict at a term whose constants do not resolve (lane `verdicts-b`, helper `ue`)

`unresolved_consts_error(vis, e, w)` (`ConstsResolveF.lean`) always aborts; its abort's class is
the class of the error the twin's `unresolvedConstsErrorL (← strLitSupported fe) where_ e`
(`w ≤ 1`) or `unresolvedConstsError where_ e` (`w ≥ 2`) computes.

Its two walks are memo-free (`docs/deviations.md` D16), the twin's memoized:

* `has_str_lit_go` (twin `hasStrLitGo`): the twin's visited set holds `false` for every key,
  inserted *before* the node's children are walked. A memo hit therefore answers `false` for a
  node that is either finished (its walk answered `false`: `HslDone`) or an ancestor still being
  walked. An ancestor is never reached again by a walk that succeeds: ranking nodes by the least
  fuel their walk succeeds at (`HslMin`), every child the walk visits ranks strictly below its
  parent (`HslPend`, `hslPend_child`). So the twin agrees with the memo-free walk `hslP`
  (`hsl_twin`), which is the L model's (`hslW_pure`).
* `ue_mentions_go` (twin `mentionsConstGo`): the twin's memo holds finished answers only, which
  agree with the memo-free walk `umP` at any fuel (`umP_agree`, `um_twin`); `umW_pure` relates the
  L model.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena
open L.Ind L.Stubs

l_model hasStrLitGo_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "has_str_lit_go" = some hasStrLitGoL)
  fns [hp ↦ hslW ro]
  specs [eView_spec p hv n]
  grind [ind_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW]

l_model ueMentionsGo_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "ue_mentions_go" = some ueMentionsGoL)
  fns [hp ↦ umW ro]
  specs [eView_spec p hv n]
  grind [ind_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW]

l_model unresolvedConstsErr_specE (p : Prog)
  (hf : p.lookup "unresolved_consts_error" = some unresolvedConstsErrL)
  fns [hf ↦ uceE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

/-! ## The pure memo-free walks on the twin's store -/

/-- Short-circuit `||` of two walk results (`none`: the walk failed). -/
def ueOrS : Option Bool → Option Bool → Option Bool
  | none, _ => none
  | some true, _ => some true
  | some false, y => y

/-- One node of the string-literal walk, the children answered by `F`. -/
def hslN (F : EIdx → Option Bool) : ENodeView → Option Bool
  | .lit (.strVal _) => some true
  | .lit (.natVal _) => some false
  | .bvar _ => some false
  | .sort _ => some false
  | .const _ _ => some false
  | .fvar _ ty => F ty
  | .app f x => ueOrS (F f) (F x)
  | .lam f x => ueOrS (F f) (F x)
  | .forallE f x => ueOrS (F f) (F x)
  | .letE t v b => ueOrS (F t) (ueOrS (F v) (F b))
  | .proj _ _ x => F x

/-- **The memo-free string-literal walk** at fuel `g`. -/
def hslP (st : EStore) : Nat → EIdx → Option Bool
  | 0, _ => none
  | g + 1, h => (st.view h).bind (hslN (hslP st g))

theorem hslP_succ (st : EStore) (g : Nat) (h : EIdx) :
    hslP st (g + 1) h = (st.view h).bind (hslN (hslP st g)) := rfl

/-- Agreeing children, agreeing short-circuit `||`. -/
theorem ueOrS_agree {a1 a2 c1 c2 : Option Bool} {x y : Bool}
    (ha : ∀ u v, a1 = some u → a2 = some v → u = v) (hc : ∀ u v, c1 = some u → c2 = some v → u = v)
    (h1 : ueOrS a1 c1 = some x) (h2 : ueOrS a2 c2 = some y) : x = y := by
  rcases a1 with _ | ⟨_ | _⟩ <;> rcases a2 with _ | ⟨_ | _⟩ <;> simp only [ueOrS] at h1 h2 <;>
    first | cases h1 | cases h2 | exact hc _ _ h1 h2 | (cases h1; cases h2; rfl) |
      exact absurd (ha _ _ rfl rfl) (by decide) | skip
  all_goals simp_all

theorem hslN_agree {F1 F2 : EIdx → Option Bool}
    (hF : ∀ c u v, F1 c = some u → F2 c = some v → u = v) (w : ENodeView) {x y : Bool}
    (h1 : hslN F1 w = some x) (h2 : hslN F2 w = some y) : x = y := by
  cases w with
  | lit l => cases l <;> simp only [hslN] at h1 h2 <;> (cases h1; cases h2; rfl)
  | bvar _ | sort _ | const _ _ => simp only [hslN] at h1 h2; cases h1; cases h2; rfl
  | fvar _ ty | proj _ _ ty => exact hF _ _ _ h1 h2
  | app f a | lam f a | forallE f a => exact ueOrS_agree (hF f) (hF a) h1 h2
  | letE t v b =>
    exact ueOrS_agree (hF t) (fun u w h1 h2 => ueOrS_agree (hF v) (hF b) h1 h2) h1 h2

/-- **The walk's answer does not depend on the fuel** (where it succeeds). -/
theorem hslP_agree (st : EStore) : ∀ (g1 g2 : Nat) (h : EIdx) (u v : Bool),
    hslP st g1 h = some u → hslP st g2 h = some v → u = v := by
  intro g1
  induction g1 with
  | zero => intro g2 h u v h1; cases h1
  | succ g ih =>
    intro g2 h u v h1 h2
    cases g2 with
    | zero => cases h2
    | succ g2 =>
      rw [hslP_succ] at h1 h2
      cases hv : st.view h with
      | none => rw [hv] at h1; cases h1
      | some w =>
        rw [hv] at h1 h2
        exact hslN_agree (fun c u v hu hv => ih g2 c u v hu hv) w h1 h2

/-- The least witness of a property of the naturals. -/
theorem ue_exists_least {P : Nat → Prop} : ∀ n, P n → ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : ∃ k, k < n ∧ P k
    · obtain ⟨k, hk, hpk⟩ := h; exact ih k hk hpk
    · exact ⟨n, hn, fun k hk => Nat.le_of_not_lt (fun hlt => h ⟨k, hlt, hk⟩)⟩

/-- A node whose every successful walk answers `false`. -/
def HslDone (st : EStore) (k : EIdx) : Prop := ∀ g b, hslP st g k = some b → b = false

/-- `ν` is the least fuel the walk of `h` succeeds at. -/
def HslMin (st : EStore) (ν : Nat) (h : EIdx) : Prop :=
  (hslP st ν h).isSome ∧ ∀ g, (hslP st g h).isSome → ν ≤ g

/-- The twin's visited set at a call whose node needs the least fuel `ν`: every key is finished
(`HslDone`) or pending, an ancestor of the call, which needs more fuel than `ν`. -/
def HslPend (st : EStore) (ν : Nat) (mp : Std.HashMap EIdx Bool) : Prop :=
  ∀ k, k ∈ mp → HslDone st k ∨ ∀ g, (hslP st g k).isSome → ν < g

theorem hslMin_exists (st : EStore) {g : Nat} {h : EIdx} (hs : (hslP st g h).isSome) :
    ∃ ν, HslMin st ν h := by
  obtain ⟨ν, h1, h2⟩ := ue_exists_least (P := fun g => (hslP st g h).isSome) g hs
  exact ⟨ν, h1, h2⟩

/-- The visited set at a child `c` of `h` (walked at `ν - 1`), after the memo grew by finished
nodes. -/
theorem hslPend_child {st : EStore} {ν ν' : Nat} {h c : EIdx} {mp mp' : Std.HashMap EIdx Bool}
    (hP : HslPend st ν mp) (hM : HslMin st ν h) (hν : ν = ν' + 1) (hc : (hslP st ν' c).isSome)
    (hmp : ∀ k, k ∈ mp' → k ∈ mp.insert h false ∨ HslDone st k) :
    ∃ μ, HslMin st μ c ∧ HslPend st μ mp' := by
  obtain ⟨μ, hμ⟩ := hslMin_exists st hc
  have hμν : μ < ν := by have := hμ.2 ν' hc; omega
  refine ⟨μ, hμ, fun k hk => ?_⟩
  rcases hmp k hk with hk | hk
  · rw [Std.HashMap.mem_insert] at hk
    rcases hk with hk | hk
    · have : h = k := by simpa using hk
      subst this
      exact .inr fun g hg => by have := hM.2 g hg; omega
    · rcases hP k hk with hd | hp
      · exact .inl hd
      · exact .inr fun g hg => by have := hp g hg; omega
  · exact .inl hk

/-! ## The twin's memoized `hasStrLitGo` -/

abbrev HM := Std.HashMap EIdx Bool

/-- The twin's short-circuit step: the first walk, then (on `false`) the rest. -/
def hslThen (X : AM (Bool × HM)) (Y : HM → AM (Bool × HM)) : AM (Bool × HM) := do
  let (r, memo) ← X
  if r then pure (true, memo) else Y memo

/-- The twin's arms of an inner node (after the memo insert). -/
def hslArm (memo : HM) (fuel : Nat) : ENodeView → AM (Bool × HM)
  | .fvar _ ty => hasStrLitGo memo fuel ty
  | .app f a => hslThen (hasStrLitGo memo fuel f) fun memo => hasStrLitGo memo fuel a
  | .lam ty b => hslThen (hasStrLitGo memo fuel ty) fun memo => hasStrLitGo memo fuel b
  | .forallE ty b => hslThen (hasStrLitGo memo fuel ty) fun memo => hasStrLitGo memo fuel b
  | .letE ty v b => hslThen (hasStrLitGo memo fuel ty) fun memo =>
      hslThen (hasStrLitGo memo fuel v) fun memo => hasStrLitGo memo fuel b
  | .proj _ _ x => hasStrLitGo memo fuel x
  | _ => pure (false, memo)

def HslNode : ENodeView → Prop
  | .fvar .. | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem hasStrLitGo_leaf (memo : HM) (fuel : Nat) (h : EIdx) (a : AState) (v : ENodeView)
    (hv : a.store.view h = some v) (hn : ¬ HslNode v) :
    (hasStrLitGo memo (fuel + 1) h).run a = .ok (((hslN (fun _ => none) v).getD false, memo), a) := by
  rw [hasStrLitGo.eq_2, StateT.run_bind, view_run _ a _ hv]
  cases v with
  | lit l => cases l <;> rfl
  | bvar _ | sort _ | const _ _ => rfl
  | _ => exact absurd trivial hn

theorem hasStrLitGo_node (memo : HM) (fuel : Nat) (h : EIdx) (a : AState) (v : ENodeView)
    (hv : a.store.view h = some v) (hn : HslNode v) :
    (hasStrLitGo memo (fuel + 1) h).run a =
      (match memo[h]? with
        | some _ => (pure (false, memo) : AM (Bool × HM))
        | none => hslArm (memo.insert h false) fuel v).run a := by
  rw [hasStrLitGo.eq_2, StateT.run_bind, view_run _ a _ hv]
  cases v with
  | lit _ | bvar _ | sort _ | const _ _ => exact absurd hn id
  | _ => cases memo[h]? <;> rfl

/-- A walk call `W` from any memo inside the allowed set `S`: where the pure walk answers `b`
(and succeeds at the least fuel's level, `oν`), the twin answers `b` without changing the state,
and on `false` the memo stays inside `S`. -/
def HslCall (S : EIdx → Prop) (a : AState) (o oν : Option Bool) (W : HM → AM (Bool × HM)) : Prop :=
  ∀ memo b, (∀ k, k ∈ memo → S k) → o = some b → oν.isSome →
    ∃ memo', (W memo).run a = .ok ((b, memo'), a) ∧ (b = false → ∀ k, k ∈ memo' → S k)

theorem hslCall_then {S : EIdx → Prop} {a : AState} {o1 o1ν o2 o2ν : Option Bool}
    {W1 W2 : HM → AM (Bool × HM)} (h1 : HslCall S a o1 o1ν W1) (h2 : HslCall S a o2 o2ν W2)
    (hag : ∀ c, o1 = some false → o1ν = some c → c = false) :
    HslCall S a (ueOrS o1 o2) (ueOrS o1ν o2ν) (fun memo => hslThen (W1 memo) W2) := by
  intro memo b hS ho hoν
  cases e1 : o1 with
  | none => rw [e1] at ho; cases ho
  | some b1 =>
  cases e1ν : o1ν with
  | none => rw [e1ν] at hoν; cases hoν
  | some c1 =>
  obtain ⟨m1, hr1, hp1⟩ := h1 memo b1 hS e1 (by rw [e1ν]; rfl)
  cases b1 with
  | true =>
    rw [e1] at ho; cases ho
    exact ⟨m1, by simp [hslThen, StateT.run_bind, hr1]; rfl, fun h => by cases h⟩
  | false =>
    have hc1 := hag c1 e1 e1ν
    subst hc1
    rw [e1] at ho; rw [e1ν] at hoν
    simp only [ueOrS] at ho hoν
    obtain ⟨m2, hr2, hp2⟩ := h2 m1 b (hp1 rfl) ho hoν
    exact ⟨m2, by simp [hslThen, StateT.run_bind, hr1]; exact hr2, hp2⟩

/-- **The twin's memoized walk answers the pure walk's answer**, from a visited set of finished
nodes and pending ancestors. -/
theorem hsl_twin (a : AState) : ∀ (g : Nat) (h : EIdx) (mp : HM) (b : Bool) (ν : Nat),
    hslP a.store g h = some b → HslMin a.store ν h → HslPend a.store ν mp →
    ∃ mp', (hasStrLitGo mp g h).run a = .ok ((b, mp'), a) ∧
      (b = false → ∀ k, k ∈ mp' → k ∈ mp ∨ HslDone a.store k) := by
  intro g
  induction g with
  | zero => intro h mp b ν hb; cases hb
  | succ g ih =>
    intro h mp b ν hb hM hP
    rw [hslP_succ] at hb
    cases hv : a.store.view h with
    | none => rw [hv] at hb; cases hb
    | some v =>
    rw [hv] at hb
    change hslN (hslP a.store g) v = some b at hb
    by_cases hn : ¬ HslNode v
    · refine ⟨mp, ?_, fun _ k hk => .inl hk⟩
      rw [hasStrLitGo_leaf mp g h a v hv hn]
      cases v with
      | lit l => cases l <;> simp only [hslN] at hb ⊢ <;> cases hb <;> rfl
      | bvar _ | sort _ | const _ _ => simp only [hslN] at hb ⊢; cases hb; rfl
      | _ => exact absurd trivial hn
    replace hn : HslNode v := Classical.not_not.mp hn
    rw [hasStrLitGo_node mp g h a v hv hn]
    cases hmem : mp[h]? with
    | some x =>
      have hin : h ∈ mp := by rw [Std.HashMap.mem_iff_isSome_getElem?, hmem]; rfl
      rcases hP h hin with hd | hp
      · have := hd _ _ (by rw [hslP_succ, hv]; exact hb)
        subst this
        exact ⟨mp, rfl, fun _ k hk => .inl hk⟩
      · exact absurd (hp ν hM.1) (Nat.lt_irrefl _)
    | none =>
    obtain ⟨ν', rfl⟩ : ∃ ν', ν = ν' + 1 := by
      cases ν with
      | zero => exact absurd hM.1 (by simp [hslP])
      | succ ν' => exact ⟨ν', rfl⟩
    have hνs : (hslN (hslP a.store ν') v).isSome := by
      have := hM.1; rw [hslP_succ, hv] at this; exact this
    let S : EIdx → Prop := fun k => k ∈ mp.insert h false ∨ HslDone a.store k
    have child : ∀ c, HslCall S a (hslP a.store g c) (hslP a.store ν' c)
        (fun memo => hasStrLitGo memo g c) := by
      intro c memo bc hS hc hcν
      obtain ⟨μ, hμ, hPμ⟩ := hslPend_child hP hM rfl hcν (fun k hk => hS k hk)
      obtain ⟨memo', hr, hp⟩ := ih c memo bc μ hc hμ hPμ
      refine ⟨memo', hr, fun hb k hk => ?_⟩
      rcases hp hb k hk with h1 | h1
      · exact hS k h1
      · exact .inr h1
    have ag : ∀ c x, hslP a.store g c = some false → hslP a.store ν' c = some x → x = false :=
      fun c x h1 h2 => (hslP_agree a.store g ν' c false x h1 h2).symm
    have arm : HslCall S a (hslN (hslP a.store g) v) (hslN (hslP a.store ν') v)
        (fun memo => hslArm memo g v) := by
      cases v with
      | lit _ | bvar _ | sort _ | const _ _ => exact absurd hn id
      | fvar _ ty => exact child ty
      | proj _ _ x => exact child x
      | app f x => exact hslCall_then (child f) (child x) (ag f)
      | lam f x => exact hslCall_then (child f) (child x) (ag f)
      | forallE f x => exact hslCall_then (child f) (child x) (ag f)
      | letE t u w =>
        exact hslCall_then (child t) (hslCall_then (child u) (child w) (ag u)) (ag t)
    obtain ⟨mp', hr, hp⟩ := arm (mp.insert h false) b (fun k hk => .inl hk) hb hνs
    refine ⟨mp', hr, fun hb0 k hk => ?_⟩
    rcases hp hb0 k hk with h1 | h1
    · rw [Std.HashMap.mem_insert] at h1
      rcases h1 with h1 | h1
      · have : h = k := by simpa using h1
        subst this
        subst hb0
        exact .inr fun g' b' h' => (hslP_agree a.store (g + 1) g' h false b'
          (by rw [hslP_succ, hv]; exact hb) h').symm
      · exact .inl h1
    · exact .inr h1

/-! ## The pure memo-free `mentionsConst` walk -/

/-- `||` of two walk results, both needed. -/
def ueOrA : Option Bool → Option Bool → Option Bool
  | some x, some y => some (x || y)
  | _, _ => none

/-- One node of the `mentionsConst T` walk. -/
def umN (T : NIdx) (F : EIdx → Option Bool) : ENodeView → Option Bool
  | .bvar _ => some false
  | .sort _ => some false
  | .lit _ => some false
  | .const n _ => some (n == T)
  | .fvar _ ty => F ty
  | .app f x => ueOrA (F f) (F x)
  | .lam f x => ueOrA (F f) (F x)
  | .forallE f x => ueOrA (F f) (F x)
  | .letE t v b => ueOrA (ueOrA (F t) (F v)) (F b)
  | .proj s _ x => (F x).map fun b => s == T || b

/-- **The memo-free `mentionsConst T` walk** at fuel `g`. -/
def umP (st : EStore) (T : NIdx) : Nat → EIdx → Option Bool
  | 0, _ => none
  | g + 1, h => (st.view h).bind (umN T (umP st T g))

theorem umP_succ (st : EStore) (T : NIdx) (g : Nat) (h : EIdx) :
    umP st T (g + 1) h = (st.view h).bind (umN T (umP st T g)) := rfl

theorem ueOrA_agree {a1 a2 c1 c2 : Option Bool} {x y : Bool}
    (ha : ∀ u v, a1 = some u → a2 = some v → u = v) (hc : ∀ u v, c1 = some u → c2 = some v → u = v)
    (h1 : ueOrA a1 c1 = some x) (h2 : ueOrA a2 c2 = some y) : x = y := by
  rcases a1 with _ | u1 <;> rcases c1 with _ | w1 <;> simp only [ueOrA] at h1 <;> cases h1
  rcases a2 with _ | u2 <;> rcases c2 with _ | w2 <;> simp only [ueOrA] at h2 <;> cases h2
  rw [ha _ _ rfl rfl, hc _ _ rfl rfl]

theorem umN_agree {T : NIdx} {F1 F2 : EIdx → Option Bool}
    (hF : ∀ c u v, F1 c = some u → F2 c = some v → u = v) (w : ENodeView) {x y : Bool}
    (h1 : umN T F1 w = some x) (h2 : umN T F2 w = some y) : x = y := by
  cases w with
  | lit _ | bvar _ | sort _ | const _ _ => simp only [umN] at h1 h2; cases h1; cases h2; rfl
  | fvar _ ty => exact hF _ _ _ h1 h2
  | proj s _ x =>
    simp only [umN] at h1 h2
    cases e1 : F1 x <;> cases e2 : F2 x <;> rw [e1] at h1 <;> rw [e2] at h2 <;> cases h1 <;> cases h2
    rw [hF _ _ _ e1 e2]
  | app f a | lam f a | forallE f a => exact ueOrA_agree (hF f) (hF a) h1 h2
  | letE t v b =>
    exact ueOrA_agree (fun u w h1 h2 => ueOrA_agree (hF t) (hF v) h1 h2) (hF b) h1 h2

theorem umP_agree (st : EStore) (T : NIdx) : ∀ (g1 g2 : Nat) (h : EIdx) (u v : Bool),
    umP st T g1 h = some u → umP st T g2 h = some v → u = v := by
  intro g1
  induction g1 with
  | zero => intro g2 h u v h1; cases h1
  | succ g ih =>
    intro g2 h u v h1 h2
    cases g2 with
    | zero => cases h2
    | succ g2 =>
      rw [umP_succ] at h1 h2
      cases hv : st.view h with
      | none => rw [hv] at h1; cases h1
      | some w =>
        rw [hv] at h1 h2
        exact umN_agree (fun c u v hu hv => ih g2 c u v hu hv) w h1 h2

/-- The twin's `mentionsConst` memo holds the walk's answers. -/
def UmMemo (st : EStore) (T : NIdx) (mp : HM) : Prop :=
  ∀ k r, mp[k]? = some r → ∀ g b, umP st T g k = some b → b = r

/-- A memoized walk call `W` from a memo of answers. -/
def UmCall (st : EStore) (T : NIdx) (a : AState) (o : Option Bool) (W : HM → AM (Bool × HM)) :
    Prop :=
  ∀ memo b, UmMemo st T memo → o = some b →
    ∃ memo', (W memo).run a = .ok ((b, memo'), a) ∧ UmMemo st T memo'

theorem umCall_two {st : EStore} {T : NIdx} {a : AState} {o1 o2 : Option Bool}
    {W1 W2 : HM → AM (Bool × HM)} (h1 : UmCall st T a o1 W1) (h2 : UmCall st T a o2 W2) :
    UmCall st T a (ueOrA o1 o2) (fun memo => do
      let (b1, m) ← W1 memo
      let (b2, m2) ← W2 m
      pure (b1 || b2, m2)) := by
  intro memo b hM ho
  rcases e1 : o1 with _ | b1 <;> rcases e2 : o2 with _ | b2 <;> rw [e1, e2] at ho <;>
    simp only [ueOrA] at ho <;> cases ho
  obtain ⟨m1, hr1, hM1⟩ := h1 memo b1 hM e1
  obtain ⟨m2, hr2, hM2⟩ := h2 m1 b2 hM1 e2
  exact ⟨m2, by simp [StateT.run_bind, hr1, except_ok_bind, hr2]; rfl, hM2⟩

theorem umCall_three {st : EStore} {T : NIdx} {a : AState} {o1 o2 o3 : Option Bool}
    {W1 W2 W3 : HM → AM (Bool × HM)} (h1 : UmCall st T a o1 W1) (h2 : UmCall st T a o2 W2)
    (h3 : UmCall st T a o3 W3) :
    UmCall st T a (ueOrA (ueOrA o1 o2) o3) (fun memo => do
      let (b1, m) ← W1 memo
      let (b2, m2) ← W2 m
      let (b3, m3) ← W3 m2
      pure (b1 || b2 || b3, m3)) := by
  intro memo b hM ho
  rcases e1 : o1 with _ | b1 <;> rcases e2 : o2 with _ | b2 <;> rcases e3 : o3 with _ | b3 <;>
    rw [e1, e2, e3] at ho <;> simp only [ueOrA] at ho <;> cases ho
  obtain ⟨m1, hr1, hM1⟩ := h1 memo b1 hM e1
  obtain ⟨m2, hr2, hM2⟩ := h2 m1 b2 hM1 e2
  obtain ⟨m3, hr3, hM3⟩ := h3 m2 b3 hM2 e3
  exact ⟨m3, by simp [StateT.run_bind, hr1, except_ok_bind, hr2, hr3]; rfl, hM3⟩

theorem umCall_proj {st : EStore} {T : NIdx} {a : AState} {o : Option Bool} (s : NIdx)
    {W : HM → AM (Bool × HM)} (h : UmCall st T a o W) :
    UmCall st T a (o.map fun b => s == T || b) (fun memo => do
      let (b, m) ← W memo
      pure (s == T || b, m)) := by
  intro memo b hM ho
  rcases e : o with _ | b1 <;> rw [e] at ho <;> simp only [Option.map] at ho <;> cases ho
  obtain ⟨m1, hr1, hM1⟩ := h memo b1 hM e
  exact ⟨m1, by simp [hr1]; rfl, hM1⟩

/-- **The twin's memoized `mentionsConstGo` answers the pure walk's answer**, from a memo of
answers. -/
theorem um_twin (a : AState) (T : NIdx) : ∀ (g : Nat) (h : EIdx) (mp : HM) (b : Bool),
    umP a.store T g h = some b → UmMemo a.store T mp →
    ∃ mp', (ConRon.Arena.mentionsConstGo T mp g h).run a = .ok ((b, mp'), a) ∧
      UmMemo a.store T mp' := by
  intro g
  induction g with
  | zero => intro h mp b hb; cases hb
  | succ g ih =>
    intro h mp b hb hM
    rw [umP_succ] at hb
    cases hv : a.store.view h with
    | none => rw [hv] at hb; cases hb
    | some v =>
    rw [hv] at hb
    change umN T (umP a.store T g) v = some b at hb
    have child : ∀ c, UmCall a.store T a (umP a.store T g c)
        (fun memo => ConRon.Arena.mentionsConstGo T memo g c) :=
      fun c memo bc hm hc => ih c memo bc hc hm
    cases v with
    | bvar _ | sort _ | lit _ | const _ _ =>
      refine ⟨mp, ?_, hM⟩
      rw [mentionsConstGo_succ', StateT.run_bind, view_run _ a _ hv]
      simp only [umN] at hb
      cases hb; rfl
    | _ =>
      rw [mcTwin_node T mp g h a _ hv trivial]
      cases hmem : mp[h]? with
      | some r =>
        have := hM h r hmem (g + 1) b (by rw [umP_succ, hv]; exact hb)
        subst this
        exact ⟨mp, rfl, hM⟩
      | none =>
        have arm : ∀ v', a.store.view h = some v' → NodeV v' →
            UmCall a.store T a (umN T (umP a.store T g) v') (fun memo => mcArm T memo g v') := by
          intro v' _ hn
          cases v' with
          | lit _ | bvar _ | sort _ | const _ _ => exact absurd hn id
          | fvar _ ty => exact child ty
          | proj s _ x => exact umCall_proj s (child x)
          | app f x => exact umCall_two (child f) (child x)
          | lam f x => exact umCall_two (child f) (child x)
          | forallE f x => exact umCall_two (child f) (child x)
          | letE t u w => exact umCall_three (child t) (child u) (child w)
        obtain ⟨mp', hr, hM'⟩ := arm _ hv trivial mp b hM hb
        refine ⟨mp'.insert h b, by simp [hr]; rfl, fun k r hk g' b' hb' => ?_⟩
        rw [Std.HashMap.getElem?_insert] at hk
        by_cases e : h = k
        · subst e
          simp at hk
          subst hk
          exact umP_agree a.store T g' (g + 1) h b' b hb' (by rw [umP_succ, hv]; exact hb)
        · simp [e] at hk
          exact hM' k r hk g' b' hb'

/-! ## The L walks' models are the pure walks -/

theorem ue_eViewW_lit {m : Mem} {h : Word} (hne : eViewW m h ≠ []) (h8 : (eViewW m h).headD 0 = 8) :
    viewOK m h LIT ∧ h >>> 28 = 8 := by
  unfold eViewW at hne h8
  simp only at hne h8
  by_cases c1 : (4294967295 : Word) < h
  · simp [c1] at hne
  rw [ite_eq_right c1] at hne h8
  by_cases c2 : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [c2] at hne
  rw [ite_eq_right c2] at hne h8
  by_cases g8 : h >>> 28 = 8
  · refine ⟨⟨c2, ?_⟩, g8⟩
    have n : ∀ k : Word, k ≠ 8 → ¬ (h >>> 28 = k) := fun k hk e => hk (e ▸ g8)
    rw [ite_eq_right (n 0 (by decide)), ite_eq_right (n 1 (by decide)), ite_eq_right (n 2 (by decide)),
      ite_eq_right (n 3 (by decide)), ite_eq_right (n 4 (by decide)), ite_eq_right (n 5 (by decide)),
      ite_eq_right (n 6 (by decide)), ite_eq_right (n 7 (by decide)), ite_eq_left g8] at hne
    by_cases c : tcnt m LIT (tierW h) ≤ idxW h
    · simp [c] at hne
    · exact UInt64.lt_iff_toNat_lt.mpr (by have := mt UInt64.le_iff_toNat_le.mpr c; omega)
  · exfalso
    repeat' split at h8
    all_goals first | (simp at h8; done) | exact g8 ‹_›

theorem ue_toNat_pred {f : Word} (hf0 : f ≠ 0) : f.toNat = (f - 1).toNat + 1 := by
  have : f.toNat ≠ 0 := fun e => hf0 (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-- **`has_str_lit_go`'s model is the pure walk** at the twin fuel `f.toNat`. -/
theorem hslW_pure (a : AState) : ∀ (n : Nat) (m : Mem) (f h r : Word), ArenaR m a → H h →
    hslW n m f h = some r → hslP a.store f.toNat (decE h) = some (r != 0) := by
  intro n
  induction n with
  | zero => intro m f h r _ _ hW; simp [hslW] at hW
  | succ n ih =>
    intro m f h r hA hh hW
    by_cases hf0 : f = 0
    · rw [hslW.abort1 n m f h hf0] at hW; cases hW
    by_cases hne : eViewW m h = []
    · rw [hslW.abort2 n m f h hf0 hne] at hW; cases hW
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h hne
    rw [ue_toNat_pred hf0, hslP_succ, hv]
    change hslN (hslP a.store (f - 1).toNat) v = some (r != 0)
    cases v with
    | bvar _ | sort _ | const _ _ =>
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      have hg := hvr.1
      rw [hslW.arm2 n m f h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide)] at hW
      cases hW; rfl
    | lit l =>
      have hg : (eViewW m h).headD 0 = 8 := hvr
      rw [hslW.arm1 n m f h hf0 hne hg] at hW
      cases hW
      obtain ⟨hok, h8⟩ := ue_eViewW_lit hne hg
      have hk := defeq_view_lit_nat m a hA h hh hok h8
      by_cases hk0 : tfld m LIT (tierW h) (idxW h) 0 = 0
      · obtain ⟨N, hN, -⟩ := hk.1 hk0
        rw [hv] at hN; cases hN
        simp [hslN, hk0]
      · obtain ⟨s, hs⟩ := hk.2 hk0
        rw [hv] at hs; cases hs
        simp [hslN, hk0]
    | fvar _ ty =>
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      obtain ⟨hg, -, hy, hdy⟩ := hvr
      rw [hslW.arm3 n m f h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide) hg] at hW
      simp only [hslN, ← hdy]
      exact ih m _ _ r hA hy hW
    | proj _ _ x =>
      simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
      obtain ⟨hg, -, -, -, hz, hdz⟩ := hvr
      rw [hslW.arm6 n m f h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)
        (by rw [hg]; decide) (by rw [hg]; decide)] at hW
      simp only [hslN, ← hdz]
      exact ih m _ _ r hA hz hW
    | app f0 x0 | lam f0 x0 | forallE f0 x0 =>
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
      rw [hslW.arm4 n m f h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)
        (by rw [hg]; decide)] at hW
      simp only [hslN, ← hdx, ← hdy]
      cases h1 : hslW n m (f - 1) ((eViewW m h).tail.headD 0) with
      | none => rw [h1, hslW.k_has_str_lit_go.none] at hW; cases hW
      | some r1 =>
        rw [h1] at hW
        rw [ih m _ _ r1 hA hx h1]
        by_cases e1 : r1 ≠ 0
        · rw [hslW.k_has_str_lit_go.arm1 n f _ m r1 e1] at hW
          cases hW; rw [show (r1 != 0) = true by simpa using e1]; rfl
        · have e1' : r1 = 0 := by simpa using e1
          rw [hslW.k_has_str_lit_go.arm2 n f _ m r1 e1'] at hW
          rw [ih m _ _ r hA hy hW]; simp [ueOrS, e1']
    | letE t0 v0 b0 =>
      simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
      obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
      rw [hslW.arm5 n m f h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)
        (by rw [hg]; decide) hg] at hW
      simp only [hslN, ← hdx, ← hdy, ← hdz]
      cases h1 : hslW n m (f - 1) ((eViewW m h).tail.headD 0) with
      | none => rw [h1, hslW.k_has_str_lit_go_2.none] at hW; cases hW
      | some r1 =>
        rw [h1] at hW
        rw [ih m _ _ r1 hA hx h1]
        by_cases e1 : r1 ≠ 0
        · rw [hslW.k_has_str_lit_go_2.arm1 n f _ _ m r1 e1] at hW
          cases hW; rw [show (r1 != 0) = true by simpa using e1]; rfl
        · have e1' : r1 = 0 := by simpa using e1
          rw [hslW.k_has_str_lit_go_2.arm2 n f _ _ m r1 e1'] at hW
          cases h2 : hslW n m (f - 1) ((eViewW m h).tail.tail.headD 0) with
          | none => rw [h2, hslW.k_has_str_lit_go_3.none] at hW; cases hW
          | some r2 =>
            rw [h2] at hW
            rw [ih m _ _ r2 hA hy h2]
            by_cases e2 : r2 ≠ 0
            · rw [hslW.k_has_str_lit_go_3.arm1 n f _ m r2 e2] at hW
              cases hW; subst e1'; rw [show (r2 != 0) = true by simpa using e2]; rfl
            · have e2' : r2 = 0 := by simpa using e2
              rw [hslW.k_has_str_lit_go_3.arm2 n f _ m r2 e2'] at hW
              rw [ih m _ _ r hA hz hW]; simp [ueOrS, e1', e2']

theorem ue_beq_ite (x T : Word) (hx : H x) (hT : H T) :
    ((if x = T then (1 : Word) else 0) != 0) = ((decI x : NIdx) == decI T) := by
  rw [decI_beq' x T hx hT]
  by_cases e : x = T <;> simp [e]

/-- **`ue_mentions_go`'s model is the pure walk** at the twin fuel `f.toNat`. -/
theorem umW_pure (a : AState) (T : Word) (hT : H T) : ∀ (n : Nat) (m : Mem) (f h r : Word),
    ArenaR m a → H h → umW n m f T h = some r →
    umP a.store (decI T) f.toNat (decE h) = some (r != 0) := by
  intro n
  induction n with
  | zero => intro m f h r _ _ hW; simp [umW] at hW
  | succ n ih =>
    intro m f h r hA hh hW
    by_cases hf0 : f = 0
    · rw [umW.abort1 n m f T h hf0] at hW; cases hW
    by_cases hne : eViewW m h = []
    · rw [umW.abort2 n m f T h hf0 hne] at hW; cases hW
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h hne
    rw [ue_toNat_pred hf0, umP_succ, hv]
    change umN (decI T) (umP a.store (decI T) (f - 1).toNat) v = some (r != 0)
    cases v with
    | bvar _ | sort _ =>
      simp only [ViewR, getD1_eq'] at hvr
      have hg := hvr.1
      rw [umW.arm1 n m f T h hf0 hne (by rw [hg]; decide)] at hW
      cases hW; rfl
    | lit _ =>
      have hg : (eViewW m h).headD 0 = 8 := hvr
      rw [umW.arm1 n m f T h hf0 hne (by rw [hg]; decide)] at hW
      cases hW; rfl
    | const _ _ =>
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      obtain ⟨hg, hx, hdx, -⟩ := hvr
      rw [umW.arm2 n m f T h hf0 hne (by rw [hg]; decide) hg] at hW
      cases hW
      simp only [umN, ← hdx]
      rw [ue_beq_ite _ T hx hT]
    | fvar _ ty =>
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      obtain ⟨hg, -, hy, hdy⟩ := hvr
      rw [umW.arm3 n m f T h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide) hg] at hW
      simp only [umN, ← hdy]
      cases h1 : umW n m (f - 1) T ((eViewW m h).tail.tail.headD 0) with
      | none => rw [h1, umW.k_ue_mentions_go.none] at hW; cases hW
      | some r1 =>
        rw [h1, umW.k_ue_mentions_go.arm1, umW.j1.arm1] at hW
        cases hW
        exact ih m _ _ _ hA hy h1
    | proj _ _ z =>
      simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
      obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
      rw [umW.arm6 n m f T h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)
        (by rw [hg]; decide) (by rw [hg]; decide)] at hW
      simp only [umN, ← hdx, ← hdz]
      cases h1 : umW n m (f - 1) T ((eViewW m h).tail.tail.tail.headD 0) with
      | none => rw [h1, umW.k_ue_mentions_go_7.none] at hW; cases hW
      | some r1 =>
        rw [h1, umW.k_ue_mentions_go_7.arm1, umW.j1.arm1] at hW
        cases hW
        rw [ih m _ _ _ hA hz h1, word_or_ne, ue_beq_ite _ T hx hT]
        rfl
    | app f0 x0 | lam f0 x0 | forallE f0 x0 =>
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
      rw [umW.arm4 n m f T h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)
        (by rw [hg]; decide)] at hW
      simp only [umN, ← hdx, ← hdy]
      cases h1 : umW n m (f - 1) T ((eViewW m h).tail.headD 0) with
      | none => rw [h1, umW.k_ue_mentions_go_2.none] at hW; cases hW
      | some r1 =>
      rw [h1, umW.k_ue_mentions_go_2.arm1] at hW
      cases h2 : umW n m (f - 1) T ((eViewW m h).tail.tail.headD 0) with
      | none => rw [h2, umW.k_ue_mentions_go_3.none] at hW; cases hW
      | some r2 =>
      rw [h2, umW.k_ue_mentions_go_3.arm1, umW.j1.arm1] at hW
      cases hW
      rw [ih m _ _ _ hA hx h1, ih m _ _ _ hA hy h2, word_or_ne]
      rfl
    | letE t0 v0 b0 =>
      simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
      obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
      rw [umW.arm5 n m f T h hf0 hne (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)
        (by rw [hg]; decide) hg] at hW
      simp only [umN, ← hdx, ← hdy, ← hdz]
      cases h1 : umW n m (f - 1) T ((eViewW m h).tail.headD 0) with
      | none => rw [h1, umW.k_ue_mentions_go_4.none] at hW; cases hW
      | some r1 =>
      rw [h1, umW.k_ue_mentions_go_4.arm1] at hW
      cases h2 : umW n m (f - 1) T ((eViewW m h).tail.tail.headD 0) with
      | none => rw [h2, umW.k_ue_mentions_go_5.none] at hW; cases hW
      | some r2 =>
      rw [h2, umW.k_ue_mentions_go_5.arm1] at hW
      cases h3 : umW n m (f - 1) T ((eViewW m h).tail.tail.tail.headD 0) with
      | none => rw [h3, umW.k_ue_mentions_go_6.none] at hW; cases hW
      | some r3 =>
      rw [h3, umW.k_ue_mentions_go_6.arm1, umW.j1.arm1] at hW
      cases hW
      rw [ih m _ _ _ hA hx h1, ih m _ _ _ hA hy h2, ih m _ _ _ hA hz h3, word_or_ne, word_or_ne]
      rfl

/-! ## The walks as calls -/

/-- **An ok `has_str_lit_go(f, h)` is the twin's `hasStrLitGo {} f.toNat`**, the memory and the
state unchanged. -/
theorem hsl_callE {p : Prog} (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "has_str_lit_go" = some hasStrLitGoL) {n : Nat} {m m' : Mem} {a : AState}
    {f h : Word} {r : List Word} (hc : callE p n "has_str_lit_go" [f, h] m = .ok (r, m'))
    (hA : ArenaR m a) (hh : H h) :
    m' = m ∧ ∃ mp', (hasStrLitGo {} f.toNat (decE h)).run a = .ok ((r.headD 0 != 0, mp'), a) := by
  obtain ⟨s', hs', -, hm, hW⟩ := triple_of_callE (hasStrLitGo_spec p hv hp n ⟨m, Locals.init []⟩ f h) hc
  refine ⟨hs'.symm.trans hm, ?_⟩
  have hP := hslW_pure a n m f h _ hA hh hW
  obtain ⟨ν, hν⟩ := hslMin_exists a.store (by rw [hP]; rfl)
  obtain ⟨mp', hr, -⟩ := hsl_twin a _ _ {} _ ν hP hν (fun k hk => by simp at hk)
  exact ⟨mp', hr⟩

/-- **An ok `ue_mentions_go(f, T, h)` is the twin's `mentionsConstGo (decI T) {} f.toNat`**. -/
theorem um_callE {p : Prog} (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "ue_mentions_go" = some ueMentionsGoL) {n : Nat} {m m' : Mem} {a : AState}
    {f T h : Word} {r : List Word} (hc : callE p n "ue_mentions_go" [f, T, h] m = .ok (r, m'))
    (hA : ArenaR m a) (hh : H h) (hT : H T) :
    m' = m ∧ ∃ mp', (ConRon.Arena.mentionsConstGo (decI T) {} f.toNat (decE h)).run a =
      .ok ((r.headD 0 != 0, mp'), a) := by
  obtain ⟨s', hs', -, hm, hW⟩ :=
    triple_of_callE (ueMentionsGo_spec p hv hp n ⟨m, Locals.init []⟩ f T h) hc
  refine ⟨hs'.symm.trans hm, ?_⟩
  obtain ⟨mp', hr, -⟩ := um_twin a (decI T) _ _ {} _ (umW_pure a T hT n m f h _ hA hh hW)
    (fun k r hk => by simp at hk)
  exact ⟨mp', hr⟩

/-! ## `unresolved_consts_error` -/

/-- The lookups of `unresolved_consts_error` and its callees. -/
structure UceLookups (p : Prog) : Prop where
  uce : p.lookup "unresolved_consts_error" = some unresolvedConstsErrL
  view : p.lookup "e_view" = some eView
  hsl : p.lookup "has_str_lit_go" = some hasStrLitGoL
  um : p.lookup "ue_mentions_go" = some ueMentionsGoL
  pin : p.lookup "pin_at" = some pinAtL

/-- `unresolved_consts_error`'s program: the lookups and `str_lit_supported`'s refinement
(`strLitSupported_core`, from a `StrLitProg`). -/
structure UceProg (p : Prog) : Prop extends UceLookups p where
  sup : StrLitSupportedOK p

/-- The callees of `unresolved_consts_error` outside the verdict closure. -/
def ueNvList : List FnName := ["pin_at", "ue_mentions_go", "has_str_lit_go", "str_lit_supported"]

theorem ueNv_mem : ∀ f ∈ ueNvList, f ∈ L.Checker.nvFns := by
  decide +kernel

theorem uceE_kum_cls {p : Prog} {w : Word} {r : List Word} {m : Mem} {er : Err}
    (h : uceE.k_ue_mentions_go p w (.ok (r, m)) = .error er) :
    er.cls = if r.headD 0 ≠ 0 then 2 else 1 := by
  rw [uceE.k_ue_mentions_go.eq_2] at h
  by_cases h0 : r.headD 0 ≠ 0
  · rw [ite_eq_left h0] at h ⊢
    repeat' split at h
    all_goals (cases h; rfl)
  · rw [ite_eq_right h0] at h ⊢
    repeat' split at h
    all_goals (cases h; rfl)

/-- The twin's verdict from the pin read and the walk's run (by `rw` only: a `simp` over the
term sends the kernel into the walk). -/
theorem unresolvedConstsError_run {a : AState} {T : NIdx} {b : Bool} {mp : Std.HashMap EIdx Bool}
    {e : EIdx} (wh : String) (hpin : pinSorryAx.run a = .ok (T, a))
    (hr : (mentionsConstGo T ∅ coreWalkFuel e).run a = .ok ((b, mp), a)) :
    (unresolvedConstsError wh e).run a =
      .ok ((if b then .notImplemented s!"use of the sorryAx axiom in {wh}"
        else .invalid s!"unknown constant in {wh}"), a) := by
  unfold unresolvedConstsError mentionsConst
  rw [StateT.run_bind, hpin, except_ok_bind]
  dsimp only
  rw [StateT.run_bind, StateT.run_bind, hr, except_ok_bind]
  dsimp only
  cases b <;> rfl
/-- **The `sorryAx` test and the verdict** (`uceE.j1`, the twin's `unresolvedConstsError`). -/
theorem uce_rest {p : Prog} (hU : UceProg p) (hnv : closedNV p L.Checker.nvFns = true)
    {n : Nat} {m : Mem} {a : AState} {e w : Word} {er : Err} (hA : ArenaR m a)
    (hF : PinsFull m a.pins) (he : H e) (hc : uceE.j1 p n e w m = .error er) (hk : er.cls ≠ 0)
    (wh : String) :
    ∃ ce, (unresolvedConstsError wh (decE e)).run a = .ok (ce, a) ∧ twinCls ce = er.cls := by
  rw [uceE.j1] at hc
  cases h1 : callE p n "pin_at" [13] m with
  | error e1 =>
    rw [h1, uceE.k_pin_at.eq_1] at hc; cases hc
    exact absurd (callE_nv hnv (ueNv_mem _ (by simp [ueNvList])) n _ m h1) hk
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, uceE.k_pin_at.eq_2] at hc
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (pinAt_specW p hU.pin n ⟨m, Locals.init []⟩ 13) h1
  simp only [pinAtW] at hW1
  have hflag : ¬ pinW m 0 = 0 := fun h0 => by simp [h0] at hW1
  rw [ite_eq_right hflag, ite_eq_right (by decide)] at hW1
  simp only [Option.some.injEq, Prod.mk.injEq] at hW1
  obtain ⟨rfl, hm1⟩ := hW1
  have hm1' : m1 = m := hs1 ▸ hm1.symm
  subst hm1'
  have hT : H (rdW (m1.arr64 PINS) (1 + 13)) := by
    have := hF.names_lt 13 (by decide); rwa [pinW_rdW m1 (1 + 13) (1 + 13) rfl] at this
  cases h2 : callE p n "ue_mentions_go" [CWF, rdW (m1.arr64 PINS) (1 + 13), e] m1 with
  | error e2 =>
    simp only [List.headD_cons] at hc
    rw [h2, uceE.k_ue_mentions_go.eq_1] at hc; cases hc
    exact absurd (callE_nv hnv (ueNv_mem _ (by simp [ueNvList])) n _ m1 h2) hk
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  simp only [List.headD_cons] at hc
  rw [h2] at hc
  have hcls := uceE_kum_cls hc
  obtain ⟨-, mp', hr2⟩ := um_callE hU.view hU.um h2 hA he hT
  rw [CWF_eq] at hr2
  have hpin : (pinSorryAx).run a = .ok (decI (rdW (m1.arr64 PINS) (1 + 13)), a) := by
    rw [← pinW_rdW m1 (1 + 13) (1 + 13) rfl]; exact pinAt_run hF 13 (by decide)
  generalize rdW (m1.arr64 PINS) (1 + 13) = T at hpin hr2
  rw [unresolvedConstsError_run wh hpin hr2]
  refine ⟨_, rfl, ?_⟩
  rw [hcls]
  by_cases h0 : r2.headD 0 ≠ 0
  · rw [ite_eq_left h0, show (r2.headD 0 != 0) = true by simpa using h0]; rfl
  · rw [ite_eq_right h0, show (r2.headD 0 != 0) = false by simpa using h0]; rfl

theorem unresolvedConstsErrorL_true (wh : String) (e : EIdx) :
    unresolvedConstsErrorL true wh e = unresolvedConstsError wh e := rfl

theorem unresolvedConstsErrorL_false_run {a : AState} {b : Bool} {mp : HM} {e : EIdx}
    (wh : String) (hr : (hasStrLitGo {} coreWalkFuel e).run a = .ok ((b, mp), a)) :
    (unresolvedConstsErrorL false wh e).run a =
      if b then .ok (.notImplemented "string literals before the String support declarations", a)
      else (unresolvedConstsError wh e).run a := by
  unfold unresolvedConstsErrorL
  rw [ite_eq_left (show (!false) = true from rfl), StateT.run_bind, hr, except_ok_bind]
  dsimp only
  cases b <;> rfl

/-- **The error claim of `unresolved_consts_error(vis, e, w)` for `w ≥ 2`**: a failing call of
class `1`/`2` aborts with the class of the twin's `unresolvedConstsError where_ e`, which succeeds
from the related state (for any `where_`: the class does not depend on it). -/
theorem uce_claim_hi {p : Prog} (hU : UceProg p) (hnv : closedNV p L.Checker.nvFns = true)
    {n : Nat} {m : Mem} {a : AState} {vis e w : Word} {er : Err} (hA : ArenaR m a)
    (hF : PinsFull m a.pins) (he : H e) (hw : ¬ w ≤ 1)
    (hc : callE p n "unresolved_consts_error" [vis, e, w] m = .error er) (hk : er.cls ≠ 0)
    (wh : String) :
    ∃ ce, (unresolvedConstsError wh (decE e)).run a = .ok (ce, a) ∧ twinCls ce = er.cls := by
  have hW := triple_of_callE_err (unresolvedConstsErr_specE p hU.uce n ⟨m, Locals.init []⟩ vis e w)
    hc (Err.code_ne_of_cls hk)
  cases n with
  | zero => rw [uceE.eq_1] at hW; cases hW; exact absurd rfl hk
  | succ n =>
  rw [uceE.arm2 p n m vis e w hw] at hW
  exact uce_rest hU hnv hA hF he hW hk wh

/-- **The error claim of `unresolved_consts_error(vis, e, w)` for `w ≤ 1`**: the twin's
`unresolvedConstsErrorL (← strLitSupported fe) where_ e` succeeds from the related state with an
error of the abort's class. -/
theorem uce_claim_lo {p : Prog} (hU : UceProg p) (hnv : closedNV p L.Checker.nvFns = true)
    {n : Nat} {m : Mem} {a : AState} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} {e w : Word} {er : Err} (hS : CoreS dn m a vis fe M eb)
    (he : H e) (hw : w ≤ 1)
    (hc : callE p n "unresolved_consts_error" [vis, e, w] m = .error er) (hk : er.cls ≠ 0)
    (wh : String) :
    ∃ ce a', (strLitSupported fe >>= fun s => unresolvedConstsErrorL s wh (decE e)).run a =
      .ok (ce, a') ∧ twinCls ce = er.cls := by
  have hW := triple_of_callE_err (unresolvedConstsErr_specE p hU.uce n ⟨m, Locals.init []⟩ vis e w)
    hc (Err.code_ne_of_cls hk)
  cases n with
  | zero => rw [uceE.eq_1] at hW; cases hW; exact absurd rfl hk
  | succ n =>
  rw [uceE.arm1 p n m vis e w hw] at hW
  cases h1 : callE p n "str_lit_supported" [vis] m with
  | error e1 =>
    rw [h1, uceE.k_str_lit_supported.eq_1] at hW; cases hW
    exact absurd (callE_nv hnv (ueNv_mem _ (by simp [ueNvList])) n _ m h1) hk
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, uceE.k_str_lit_supported.eq_2] at hW
  obtain ⟨hok, ⟨M', hS', -, -⟩, hres, -⟩ :=
    CoreSpec.of_callW (hU.sup n ⟨m, Locals.init []⟩ a dn vis fe M eb hS) (callW_of_callE h1)
  have hrun := AM.run_of_ok _ _ hok
  rw [hres] at hrun
  generalize AM.st (strLitSupported fe) a = a1 at hrun hS'
  rw [StateT.run_bind, hrun, except_ok_bind]
  dsimp only
  have hA1 : ArenaR m1 a1 := hS'.arena.1
  by_cases hr1 : r1.headD 0 = 0
  · rw [ite_eq_left hr1] at hW
    have hd : decBool r1 = false := by show (r1.headD 0 != 0) = false; rw [hr1]; rfl
    rw [hd]
    cases h2 : callE p n "has_str_lit_go" [CWF, e] m1 with
    | error e2 =>
      rw [h2, uceE.k_has_str_lit_go.eq_1] at hW; cases hW
      exact absurd (callE_nv hnv (ueNv_mem _ (by simp [ueNvList])) n _ m1 h2) hk
    | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, uceE.k_has_str_lit_go.eq_2] at hW
    obtain ⟨rfl, mp, hr2⟩ := hsl_callE hU.view hU.hsl h2 hA1 he
    rw [CWF_eq] at hr2
    rw [unresolvedConstsErrorL_false_run wh hr2]
    by_cases hr2' : r2.headD 0 ≠ 0
    · rw [ite_eq_left hr2'] at hW; cases hW
      rw [ite_eq_left (by simpa using hr2')]
      exact ⟨_, _, rfl, rfl⟩
    · rw [ite_eq_right hr2'] at hW
      rw [ite_eq_right (by simpa using hr2')]
      obtain ⟨ce, hce, hcl⟩ := uce_rest hU hnv hA1 hS'.pins he hW hk wh
      exact ⟨ce, a1, hce, hcl⟩
  · rw [ite_eq_right hr1] at hW
    have hd : decBool r1 = true := by show (r1.headD 0 != 0) = true; exact bne_iff_ne.mpr hr1
    rw [hd, unresolvedConstsErrorL_true]
    obtain ⟨ce, hce, hcl⟩ := uce_rest hU hnv hA1 hS'.pins he hW hk wh
    exact ⟨ce, a1, hce, hcl⟩

/-- **The site `fail (← unresolvedConstsError where_ e)`** (`w ≥ 2`) as an error claim. -/
theorem uce_errClaim_hi {α : Type} {p : Prog} (hU : UceProg p)
    (hnv : closedNV p L.Checker.nvFns = true) {n : Nat} {m : Mem} {a : AState} {vis e w : Word}
    {er : Err} (hA : ArenaR m a) (hF : PinsFull m a.pins) (he : H e) (hw : ¬ w ≤ 1)
    (hc : callE p n "unresolved_consts_error" [vis, e, w] m = .error er) (wh : String) :
    ErrClaim (unresolvedConstsError wh (decE e) >>= fun ce => (ConRon.Arena.fail ce : AM α)) a er :=
  fun hk => by
    obtain ⟨ce, hrun, hcl⟩ := uce_claim_hi hU hnv hA hF he hw hc hk wh
    exact ⟨ce, by rw [StateT.run_bind, hrun, except_ok_bind]; rfl, hcl⟩

/-- **The site `fail (← unresolvedConstsErrorL (← strLitSupported fe) where_ e)`** (`w ≤ 1`) as
an error claim. -/
theorem uce_errClaim_lo {α : Type} {p : Prog} (hU : UceProg p)
    (hnv : closedNV p L.Checker.nvFns = true) {n : Nat} {m : Mem} {a : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {e w : Word} {er : Err} (hS : CoreS dn m a vis fe M eb) (he : H e) (hw : w ≤ 1)
    (hc : callE p n "unresolved_consts_error" [vis, e, w] m = .error er) (wh : String) :
    ErrClaim (strLitSupported fe >>= fun s => unresolvedConstsErrorL s wh (decE e) >>= fun ce =>
      (ConRon.Arena.fail ce : AM α)) a er :=
  fun hk => by
    obtain ⟨ce, a', hrun, hcl⟩ := uce_claim_lo hU hnv hS he hw hc hk wh
    refine ⟨ce, ?_, hcl⟩
    rw [← bind_assoc, StateT.run_bind, hrun, except_ok_bind]
    rfl

end L.Arena
