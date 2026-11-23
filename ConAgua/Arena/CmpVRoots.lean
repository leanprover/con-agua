module

public import ConRon.Bridge.Compare.Needs
public import ConLeche.Cached.Needs
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Checker.NatOpNames
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.DivMod
import ConRon.Bridge.Compare.Justify
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.Frontend.Prepare
import ConRon.Bridge.Frontend.Lines

@[expose] public section

/-!
# The needs walks read back exactly (lane compare2, helper compare2-verdict)

The twin's needs walks (`needsGo`, `NeedsSt.expr/exprs/rule/rules/const/table`, `pinFootprint`)
list exactly the names upstream's do, read back (`XRel`). This is
`vendor/con-ron/ConRon/Bridge/Modular/Roots.lean` lines 38-593 unchanged (namespace `CmpV`), the
closure of what `Arena/CmpVCone.lean` uses; not imported because that module fails to build at
our pin from line 796 on (its modular-reach half). Delete when the vendored module builds.
-/

namespace ConRon.Bridge.CmpV

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Arena.Frontend (denoteNList)


/-! ## The memo -/

/-- con-leche: ConLeche/Cached/Needs.lean:42-69 needsGo — **the two memos are one**, keyed by
handle and by the expression it denotes. -/
structure NSeen (st : EStore) (seen : Std.HashMap EIdx Bool) (seenP : Std.HashSet Expr) : Prop where
  fwd : ∀ h e, denoteE st h = some e → seen.contains h = true → seenP.contains e = true
  bwd : ∀ eP, seenP.contains eP = true → ∃ h, seen.contains h = true ∧ denoteE st h = some eP
  dom : ∀ h, seen.contains h = true → (denoteE st h).isSome = true

theorem NSeen.empty (st : EStore) : NSeen st ∅ ∅ where
  fwd := by intro h e _ hc; simp at hc
  bwd := by intro eP hc; simp at hc
  dom := by intro h hc; simp at hc

theorem NSeen.contains {st : EStore} (hwf : StoreWF st) {seen : Std.HashMap EIdx Bool}
    {seenP : Std.HashSet Expr} (hs : NSeen st seen seenP) {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) : seen.contains h = seenP.contains e := by
  cases hc : seen.contains h with
  | true => exact (hs.fwd h e he hc).symm
  | false =>
    cases hp : seenP.contains e with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hdk⟩ := hs.bwd e hp
      obtain rfl : k = h := Arena.denoteE_inj hwf hdk he
      rw [hk] at hc; exact absurd hc (by simp)

theorem NSeen.insert {st : EStore} {seen : Std.HashMap EIdx Bool} {seenP : Std.HashSet Expr}
    (hs : NSeen st seen seenP) {h : EIdx} {e : Expr} (he : denoteE st h = some e) :
    NSeen st (seen.insert h true) (seenP.insert e) where
  fwd := by
    intro k ek hk hc
    rw [Std.HashMap.contains_insert] at hc
    rw [Std.HashSet.contains_insert]
    rcases Bool.or_eq_true .. |>.mp hc with h1 | h2
    · have hhk : h = k := eq_of_beq h1
      subst hhk
      obtain rfl : e = ek := Option.some.inj (he.symm.trans hk)
      simp
    · rw [hs.fwd k ek hk h2]; simp
  bwd := by
    intro eP hc
    rw [Std.HashSet.contains_insert] at hc
    rcases Bool.or_eq_true .. |>.mp hc with h1 | h2
    · obtain rfl : e = eP := eq_of_beq h1
      exact ⟨h, by rw [Std.HashMap.contains_insert]; simp, he⟩
    · obtain ⟨k, hk, hdk⟩ := hs.bwd eP h2
      exact ⟨k, by rw [Std.HashMap.contains_insert, hk]; simp, hdk⟩
  dom := by
    intro k hk
    rw [Std.HashMap.contains_insert] at hk
    rcases Bool.or_eq_true .. |>.mp hk with h1 | h2
    · have hhk : h = k := eq_of_beq h1
      subst hhk; rw [he]; rfl
    · exact hs.dom k h2

/-- con-leche: none — **the walk's state read back**: the memo, and the names so far. -/
@[expose] def XRel (st : EStore) (x : Arena.NeedsSt) (xP : ConLeche.Cached.NeedsSt) : Prop :=
  NSeen st x.seen xP.1 ∧ denoteNList st.ns x.acc = some xP.2.toList

theorem XRel.empty (st : EStore) : XRel st Arena.NeedsSt.empty ({}, #[]) :=
  ⟨NSeen.empty st, rfl⟩

/-! ## Names -/

theorem denoteNL_append {st : EStore} :
    ∀ {a b : List NIdx} {A B : List ConLeche.Name}, denoteNL st a A → denoteNL st b B →
      denoteNL st (a ++ b) (A ++ B)
  | [], _, [], _, _, hb => hb
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, hb => ⟨h1, denoteNL_append h2 hb⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

/-- `NeedsSt.names`, read back. -/
theorem names_exact {st : EStore} {x : Arena.NeedsSt} {xP : ConLeche.Cached.NeedsSt}
    (hx : XRel st x xP) {ns : List NIdx} {L : List ConLeche.Name}
    (hL : denoteNList st.ns ns = some L) : XRel st (x.names ns) (xP.names L) := by
  refine ⟨hx.1, ?_⟩
  simp only [Arena.NeedsSt.names, nidxAppend, List.drop_zero, Nat.sub_zero, List.take_length,
    ConLeche.Cached.NeedsSt.names, Array.toList_appendList]
  exact denoteNList_append' hx.2 hL

/-- `NeedsSt.name`, read back. -/
theorem name_exact {st : EStore} {x : Arena.NeedsSt} {xP : ConLeche.Cached.NeedsSt}
    (hx : XRel st x xP) {n : NIdx} {nm : ConLeche.Name} (hn : denoteN st.ns n = some nm) :
    XRel st (x.name n) (xP.names [nm]) := by
  refine ⟨hx.1, ?_⟩
  simp only [Arena.NeedsSt.name, ConLeche.Cached.NeedsSt.names, Array.toList_appendList]
  exact denoteNList_snoc hx.2 hn

/-- con-leche: ConLeche/Cached/Needs.lean:24-29 litNeeds — exactly. -/
theorem litNeeds_exact {s s' : AState} {l : Literal} {acc r : List NIdx} (hp : PinsOK s)
    {accP : List ConLeche.Name} (hacc : denoteNList s.store.ns acc = some accP)
    (hrun : Arena.litNeeds l acc s = .ok (r, s')) :
    s' = s ∧ denoteNList s.store.ns r = some (accP ++ ConLeche.Cached.litNeeds l) := by
  simp only [Arena.litNeeds] at hrun
  obtain ⟨ns, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hns⟩ := Inductives.litGuardNames_run hp h1
  subst hs1
  cases l with
  | natVal n =>
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    refine ⟨rfl, ?_⟩
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero]
    exact denoteNList_append' hacc (denoteNL_toList _ _ (denoteNL_take 3 hns))
  | strVal str =>
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    refine ⟨rfl, ?_⟩
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero, List.take_length]
    exact denoteNList_append' hacc (denoteNL_toList _ _ hns)

/-! ## The walk -/

/-- con-leche: ConLeche/Cached/Needs.lean:42-69 needsGo — **the twin's memoised walk is
upstream's**, the memos one (`NSeen`), the names the same list. -/
theorem needsGo_exact {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (fuel : Nat) {seen : Std.HashMap EIdx Bool} {acc : List NIdx}
      {seenP : Std.HashSet Expr} {accP : Array ConLeche.Name}
      {h : EIdx} {e : Expr} {r : Std.HashMap EIdx Bool × List NIdx} {s' : AState},
      NSeen s.store seen seenP → denoteNList s.store.ns acc = some accP.toList →
      denoteE s.store h = some e →
      Arena.needsGo seen acc fuel h s = .ok (r, s') →
      s' = s ∧ NSeen s.store r.1 (ConLeche.Cached.needsGo seenP accP e).1 ∧
        denoteNList s.store.ns r.2 = some (ConLeche.Cached.needsGo seenP accP e).2.toList := by
  have hwf : StoreWF s.store := hok.wf
  intro fuel
  induction fuel with
  | zero =>
    intro seen acc seenP accP h e r s' _ _ _ hrun
    rw [Arena.needsGo] at hrun
    exact absurd (AM.fail_ok hrun) (by simp)
  | succ fuel ih =>
    intro seen acc seenP accP h e r s' hseen hacc he hrun
    rw [Arena.needsGo] at hrun
    obtain ⟨v, s₁, hv, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hview⟩ := view_run hv
    rw [hs1] at hrest
    have hcont := hseen.contains hwf he
    -- a compound node: the memo's test, then the children and the node recorded (`rest`)
    have compound : ∀ (rest : AM (Std.HashMap EIdx Bool × List NIdx))
        (resP : Std.HashSet Expr × Array ConLeche.Name),
        (∀ (r' : Std.HashMap EIdx Bool × List NIdx) (s'' : AState), rest s = .ok (r', s'') →
          s'' = s ∧ NSeen s.store r'.1 resP.1 ∧ denoteNList s.store.ns r'.2 = some resP.2.toList) →
        (match seen[h]? with
          | some _ => pure (seen, acc)
          | none => rest : AM _) s = .ok (r, s') →
        s' = s ∧ NSeen s.store r.1 (if seenP.contains e then (seenP, accP) else resP).1 ∧
          denoteNList s.store.ns r.2 = some (if seenP.contains e then (seenP, accP) else resP).2.toList := by
      intro rest resP hbody hm
      cases hsh : seen[h]? with
      | some b =>
        rw [hsh] at hm
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hm
        have hc : seen.contains h = true := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, hsh]; rfl
        rw [hcont] at hc
        simp only [hc, ↓reduceIte]
        exact ⟨by trivial, hseen, hacc⟩
      | none =>
        rw [hsh] at hm
        have hc : seen.contains h = false := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, hsh]; rfl
        rw [hcont] at hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact hbody _ _ hm
    match v, hview with
    | .const m us, hview =>
      obtain ⟨mP, ls, rfl, hm, -⟩ := denote_const_inv hwf hview he
      simp only [] at hrest
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      simp only [ConLeche.Cached.needsGo, Array.toList_push]
      exact ⟨by trivial, hseen, denoteNList_snoc hacc hm⟩
    | .bvar i, hview =>
      obtain rfl := denote_bvar_inv hwf hview he
      simp only [] at hrest
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      simp only [ConLeche.Cached.needsGo]
      exact ⟨by trivial, hseen, hacc⟩
    | .sort u, hview =>
      obtain ⟨l, rfl, -⟩ := denote_sort_inv hwf hview he
      simp only [] at hrest
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      simp only [ConLeche.Cached.needsGo]
      exact ⟨by trivial, hseen, hacc⟩
    | .lit l, hview =>
      obtain rfl := denote_lit_inv hwf hview he
      simp only [] at hrest
      obtain ⟨a, s₂, h1, h2⟩ := AM.bind_ok hrest
      obtain ⟨rfl, ha⟩ := litNeeds_exact hp hacc h1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      simp only [ConLeche.Cached.needsGo, Array.toList_appendList]
      exact ⟨by trivial, hseen, ha⟩
    | .fvar k ty, hview =>
      obtain ⟨t, rfl, hdt⟩ := denote_fvar_inv hwf hview he
      try simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc hdt hg1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
      exact ⟨rfl, hs1.insert he, ha1⟩
    | .proj nn i sub, hview =>
      obtain ⟨nm, es, rfl, hnn, hsub⟩ := denote_proj_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih (accP := accP.push nm) hseen (by
        rw [Array.toList_push]; exact denoteNList_snoc hacc hnn) hsub hg1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
      exact ⟨rfl, hs1.insert he, ha1⟩
    | .app f a, hview =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc hf hg1
      obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
      obtain ⟨sn2, ac2⟩ := p2
      obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 ha hg2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
      exact ⟨rfl, hs2.insert he, ha2⟩
    | .lam ty body, hview =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_lam_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc hf hg1
      obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
      obtain ⟨sn2, ac2⟩ := p2
      obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 ha hg2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
      exact ⟨rfl, hs2.insert he, ha2⟩
    | .forallE ty body, hview =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_forallE_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc hf hg1
      obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
      obtain ⟨sn2, ac2⟩ := p2
      obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 ha hg2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
      exact ⟨rfl, hs2.insert he, ha2⟩
    | .letE ty w body, hview =>
      obtain ⟨et, ew, eb, rfl, h1d, h2d, h3d⟩ := denote_letE_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc h1d hg1
      obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
      obtain ⟨sn2, ac2⟩ := p2
      obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 h2d hg2
      obtain ⟨p3, s₄, hg3, hr3⟩ := AM.bind_ok hr2
      obtain ⟨sn3, ac3⟩ := p3
      obtain ⟨rfl, hs3, ha3⟩ := ih hs2 ha2 h3d hg3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr3
      exact ⟨rfl, hs3.insert he, ha3⟩

/-- con-leche: ConLeche/Cached/Needs.lean:74-75 NeedsSt.expr — exactly. -/
theorem expr_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {xP : ConLeche.Cached.NeedsSt} {e : EIdx} {t : Expr} (hx : XRel s.store x xP)
    (he : denoteE s.store e = some t) (hrun : x.expr e s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.expr t) := by
  simp only [Arena.NeedsSt.expr] at hrun
  obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, i1, i2⟩ := needsGo_exact hok hp _ hx.1 hx.2 he h1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  exact ⟨rfl, i1, i2⟩

/-- `pins.foldl NeedsSt.expr`, exactly. -/
theorem exprs_exact {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (es : List EIdx) (ts : List Expr) (x : Arena.NeedsSt) (xP : ConLeche.Cached.NeedsSt)
      {y : Arena.NeedsSt} {s' : AState},
      XRel s.store x xP → Frontend.denoteEList s.store es = some ts →
      x.exprs es s = .ok (y, s') → s' = s ∧ XRel s.store y (ts.foldl ConLeche.Cached.NeedsSt.expr xP)
  | [], ts, x, xP, y, s', hx, hts, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hts
    subst hts
    simp only [Arena.NeedsSt.exprs] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, hx⟩
  | e :: es, ts, x, xP, y, s', hx, hts, hrun => by
    obtain ⟨t, ts', he, hes, rfl⟩ := denoteEList_cons_inv hts
    simp only [Arena.NeedsSt.exprs] at hrun
    obtain ⟨x2, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, o1⟩ := expr_exact hok hp hx he h1
    exact exprs_exact hok hp es ts' x2 _ o1 hes h2

/-- con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule — exactly. -/
theorem rule_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {xP : ConLeche.Cached.NeedsSt} {r : IRecRule} {R : RecRule} (hx : XRel s.store x xP)
    (hR : Frontend.denoteRule s.store r = some R) (hrun : x.rule r s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.rule R) := by
  obtain ⟨hc, hf, hrhs, -⟩ := denoteRule_inv hR
  simp only [Arena.NeedsSt.rule] at hrun
  obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, o1⟩ := expr_exact hok hp hx hrhs h1
  have o2 := name_exact o1 hc
  unfold ConLeche.Cached.NeedsSt.rule
  cases hfr : r.fire with
  | nested lvls pins =>
    rw [hfr] at h2 hf
    rw [denoteFire_nested_opt] at hf
    simp only [opt2] at hf
    split at hf
    · next ls ps hls hps =>
      have hRf : R.fire = .nested ls ps := (Option.some.inj hf).symm
      rw [hRf]
      simp only at h2
      exact exprs_exact hok hp pins ps _ _ o2 hps h2
    · exact absurd hf (by simp)
  | plain =>
    rw [hfr] at h2 hf
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    rw [← hf]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨rfl, o2⟩
  | levels lvls =>
    rw [hfr] at h2 hf
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨_, -, hf⟩ := hf
    rw [← hf]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨rfl, o2⟩

/-- `rules.foldl NeedsSt.rule`, exactly. -/
theorem rules_exact {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (rs : List IRecRule) (Rs : List RecRule) (x : Arena.NeedsSt) (xP : ConLeche.Cached.NeedsSt)
      {y : Arena.NeedsSt} {s' : AState},
      XRel s.store x xP → Frontend.denoteRules s.store rs = some Rs →
      x.rules rs s = .ok (y, s') → s' = s ∧ XRel s.store y (Rs.foldl ConLeche.Cached.NeedsSt.rule xP)
  | [], Rs, x, xP, y, s', hx, hRs, hrun => by
    simp only [Frontend.denoteRules, Option.some.injEq] at hRs
    subst hRs
    simp only [Arena.NeedsSt.rules] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, hx⟩
  | r :: rs, Rs, x, xP, y, s', hx, hRs, hrun => by
    obtain ⟨R, Rs', hR, hRs', rfl⟩ := denoteRules_cons hRs
    simp only [Arena.NeedsSt.rules] at hrun
    obtain ⟨x2, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, o1⟩ := rule_exact hok hp hx hR h1
    exact rules_exact hok hp rs Rs' x2 _ o1 hRs' h2

/-! ## A pinned constant's fast-path names, exactly -/

theorem pinFootprintReduce_exact {n : NIdx} {nm : ConLeche.Name} {xs r : List NIdx}
    {L : List ConLeche.Name} {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    (hn : denoteN s.store.ns n = some nm) (hxs : denoteNList s.store.ns xs = some L)
    (hrun : Arena.pinFootprintReduce n xs s = .ok (r, s')) :
    s' = s ∧ denoteNList s.store.ns r = some (L ++
        (if ConLeche.reduceOpNames.contains nm then [ConLeche.reduceElemName nm] else [])) := by
  simp only [Arena.pinFootprintReduce] at hrun
  obtain ⟨ns, s0, g0, r0⟩ := AM.bind_ok hrun
  obtain ⟨p0, d0⟩ := reduceOpNames_run hp g0
  subst s0
  have hc := denoteNL_contains hok.wf d0 hn
  rcases AM.ite_ok r0 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨e, s1, g1, r1⟩ := AM.bind_ok k
    obtain ⟨p1, d1⟩ := reduceElemName_run hok hp hn g1
    subst s1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
    rw [hc] at hb
    rw [ite_eq_left hb]
    exact ⟨rfl, denoteNList_snoc hxs d1⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    rw [hc] at hb
    rw [ite_eq_right hb, List.append_nil]
    exact ⟨rfl, hxs⟩

theorem pinFootprintNat_exact {n : NIdx} {nm : ConLeche.Name} {dms r : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hdms : denoteNL s.store dms ConLeche.natDivModNames)
    (hrun : Arena.pinFootprintNat n dms s = .ok (r, s')) :
    s' = s ∧ denoteNList s.store.ns r = some
      (ConLeche.natOpDeps nm ++ [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName] ++
        (if nm = ConLeche.natBeqName || nm = ConLeche.natBleName ||
            ConLeche.natDivModNames.contains nm then
          [ConLeche.boolName, ConLeche.boolTrueName, ConLeche.boolFalseName] else [])) := by
  simp only [Arena.pinFootprintNat, Arena.natBeqName, Arena.pinNatBeq, Arena.natBleName,
    Arena.pinNatBle, Arena.boolName, Arena.pinBool, Arena.boolTrueName, Arena.pinBoolTrue,
    Arena.boolFalseName, Arena.pinBoolFalse] at hrun
  obtain ⟨deps, s0, g0, r0⟩ := AM.bind_ok hrun
  have p0 := natOpDeps_state hp g0
  obtain ⟨-, -, -, -, d0⟩ := natOpDeps_run hok hp hn g0
  subst s0
  obtain ⟨lits, s1, g1, r1⟩ := AM.bind_ok r0
  obtain ⟨p1, d1⟩ := Inductives.litGuardNames_run hp g1
  subst s1
  obtain ⟨be, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨p2, d2⟩ := pinAt_run (x := ConLeche.natBeqName) hp (by rfl) g2
  subst s2
  obtain ⟨bl, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨p3, d3⟩ := pinAt_run (x := ConLeche.natBleName) hp (by rfl) g3
  subst s3
  have hbase : denoteNList s.store.ns (nidxAppend deps lits 0 3) = some
      (ConLeche.natOpDeps nm ++ [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName]) := by
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero]
    exact denoteNL_toList _ _ (denoteNL_append d0 (denoteNL_take 3 d1))
  have hcond : ((n == be || n == bl || dms.contains n) = true) ↔
      ((nm = ConLeche.natBeqName || nm = ConLeche.natBleName ||
        ConLeche.natDivModNames.contains nm) = true) := by
    rw [denoteNL_contains hok.wf hdms hn]
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_handle_iff hok.wf hn d2,
      beq_handle_iff hok.wf hn d3]
  rcases AM.ite_ok r3 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨b, s4, g4, r4⟩ := AM.bind_ok k
    obtain ⟨p4, d4⟩ := pinAt_run (x := ConLeche.boolName) hp (by rfl) g4
    subst s4
    obtain ⟨bt, s5, g5, r5⟩ := AM.bind_ok r4
    obtain ⟨p5, d5⟩ := pinAt_run (x := ConLeche.boolTrueName) hp (by rfl) g5
    subst s5
    obtain ⟨bf, s6, g6, r6⟩ := AM.bind_ok r5
    obtain ⟨p6, d6⟩ := pinAt_run (x := ConLeche.boolFalseName) hp (by rfl) g6
    subst s6
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r6
    rw [ite_eq_left (hcond.mp hb)]
    refine ⟨rfl, ?_⟩
    have := denoteNList_snoc (denoteNList_snoc (denoteNList_snoc hbase d4) d5) d6
    simpa [List.append_assoc] using this
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    rw [ite_eq_right (fun h => hb (hcond.mpr h)), List.append_nil]
    exact ⟨rfl, hbase⟩

/-- con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint — **the names a pinned
constant's fast path reads, exactly**. -/
theorem pinFootprint_exact {n : NIdx} {nm : ConLeche.Name} {r : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hrun : Arena.pinFootprint n s = .ok (r, s')) :
    s' = s ∧ denoteNList s.store.ns r = some (ConLeche.pinFootprint nm) := by
  simp only [Arena.pinFootprint] at hrun
  obtain ⟨ops, s0, g0, r0⟩ := AM.bind_ok hrun
  obtain ⟨p0, d0⟩ := natOpNames_run hp g0
  subst s0
  obtain ⟨dms, s1, g1, r1⟩ := AM.bind_ok r0
  obtain ⟨p1, d1⟩ := natDivModNames_run hp g1
  subst s1
  have hcond : ((ops.contains n || dms.contains n) = true) ↔
      ((ConLeche.natOpNames.contains nm || ConLeche.natDivModNames.contains nm) = true) := by
    rw [denoteNL_contains hok.wf d0 hn, denoteNL_contains hok.wf d1 hn]
  unfold ConLeche.pinFootprint
  rcases AM.ite_ok r1 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨xs, s2, g2, r2⟩ := AM.bind_ok k
    obtain ⟨rfl, c2⟩ := pinFootprintNat_exact hok hp hn d1 g2
    obtain ⟨rfl, c3⟩ := pinFootprintReduce_exact hok hp hn c2 r2
    rw [ite_eq_left (hcond.mp hb)]
    exact ⟨rfl, c3⟩
  · obtain ⟨rfl, c3⟩ := pinFootprintReduce_exact hok hp hn rfl k
    rw [ite_eq_right (fun h => hb (hcond.mpr h))]
    exact ⟨rfl, by simpa using c3⟩

/-! ## A constant's, a table's and a record's reads, exactly -/

theorem constTail_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    {x2 y : Arena.NeedsSt} {xP : ConLeche.Cached.NeedsSt} {n : NIdx} {nm : ConLeche.Name}
    (hx : XRel s.store x2 xP) (hn : denoteN s.store.ns n = some nm)
    (hrun : (do let fp ← Arena.pinFootprint n; pure (x2.names fp) : AM _) s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.names (ConLeche.pinFootprint nm)) := by
  obtain ⟨fp, s3, h5, h6⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hfp⟩ := pinFootprint_exact hok hp hn h5
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
  exact ⟨rfl, names_exact hx hfp⟩

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — **what a constant's laws read,
exactly**. -/
theorem const_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {xP : ConLeche.Cached.NeedsSt} {ci : IConstantInfo} {c : ConstantInfo}
    (hx : XRel s.store x xP) (hc : Frontend.denoteCI s.store ci = some c)
    (hrun : x.const ci s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.const c) := by
  obtain ⟨-, -, hty⟩ := denoteCV_inv (denoteCI_toConstantVal hc)
  have hn := denoteCI_name hc
  simp only [Arena.NeedsSt.const] at hrun
  obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, o1⟩ := expr_exact hok hp hx hty h1
  unfold ConLeche.Cached.NeedsSt.const
  cases ci with
  | defnInfo v e hint =>
    obtain ⟨cv, xv, rfl, -, hxv⟩ := denoteCI_defn_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, o2⟩ := expr_exact hok hp o1 hxv h3
    exact constTail_exact hok hp o2 hn h4
  | recInfo v mI rP k rs =>
    obtain ⟨cv, Rs, rfl, -, hRs⟩ := denoteCI_rec_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, o2⟩ := rules_exact hok hp rs Rs x1 _ o1 hRs h3
    exact constTail_exact hok hp o2 hn h4
  | indInfo v cap =>
    obtain ⟨cv, d, rfl, -, hd⟩ := denoteCI_ind_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    simp only [Frontend.denoteCaps] at hd
    split at hd
    · next all ctors hall hctors =>
      obtain rfl := (Option.some.inj hd).symm
      exact constTail_exact hok hp (names_exact o1 hall) hn h4
    · exact absurd hd (by simp)
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    exact constTail_exact hok hp o1 hn h4
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    exact constTail_exact hok hp o1 hn h4
  | ctorInfo v nP nF T =>
    obtain ⟨cv, rfl, -⟩ := denoteCI_ctor_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    exact constTail_exact hok hp o1 hn h4

/-- con-leche: ConLeche/Cached/Needs.lean:97-99 NeedsSt.table — exactly. -/
theorem table_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {xP : ConLeche.Cached.NeedsSt} {t : IProjTable} {pt : ProjTable} (hx : XRel s.store x xP)
    (ht : Frontend.denoteProjTable s.store t = some pt) (hrun : x.table t s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.table pt) := by
  rw [denoteProjTable_opt, denoteEArray_map] at ht
  simp only [opt2, opt3] at ht
  split at ht
  · next a b hab hb =>
    split at hab
    · next sn lps c hsn hlps hc =>
      obtain rfl := (Option.some.inj hab).symm
      simp only [Option.map_eq_some_iff] at hb
      obtain ⟨bs, hbs, rfl⟩ := hb
      obtain rfl := (Option.some.inj ht).symm
      simp only [Arena.NeedsSt.table] at hrun
      have o1 := name_exact (name_exact hx hsn) hc
      obtain ⟨rfl, o2⟩ := exprs_exact hok hp t.bodies.toList bs _ _ o1 hbs hrun
      refine ⟨rfl, ?_⟩
      unfold ConLeche.Cached.NeedsSt.table
      have e : (xP.names [sn, c]) = ((xP.names [sn]).names [c]) := by
        simp [ConLeche.Cached.NeedsSt.names]
      simpa [e] using o2
    · exact absurd hab (by simp)
  · exact absurd ht (by simp)

end ConRon.Bridge.CmpV
