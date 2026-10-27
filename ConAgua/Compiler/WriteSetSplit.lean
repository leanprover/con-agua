import ConAgua.L.WriteSet
import ConAgua.Compiler.WFSplit
import ConAgua.Compiler.WFFast
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Write sets of a large program, one function at a time (lane `erecfix`)

`closedW ctl p A C fs` (`L/WriteSet.lean`) by `decide +kernel` looks up every `f ∈ fs` in `p`
and every callee in `fs` by `String` comparison, and checks every body in one kernel check: for
the checker's core (~500 of 1720 functions) that took 20 GB. As `prog_wf` (`WFSplit.lean`) does
for `Prog.wf`, this splits it:

* the function set as a search tree of name codes, a literal (`names_tree t : fs` declares `t`
  and `t.eq : namesTree fs = some t`, one kernel check that reads only the names);
* a per-function check `wsChk ctl pa pc t x` on one function `x = (name, decl)`: either its name
  is not in the tree, or its body stores only where `pa`/`pc` allow and calls only names of the
  tree (`Stmt.okWB`: numbers compared with GMP, no `String` comparison, no lookup in `p`);
* `prog_all h : p chk` declares `h : ∀ x ∈ p, chk x = true`, one kernel check per chunk of
  `progWfChunk` functions (each sees only its chunk's bodies), put together without evaluation;
* `closedW_of_all` composes them: the call closure comes from the tree (each callee is in `fs`),
  the lookups from `List.lookup`'s first match being a member of `p`.
-/

namespace L.Compiler

open L

/-! ## The function set as a tree of name codes -/

/-- The tree of a list of names (every value `0`, a repeated name once). -/
def namesTree : List FnName → Option NTree
  | [] => some .leaf
  | f :: fs => (namesTree fs).bind fun t =>
    if (t.find (nameCode f)).isSome then some t else t.insert (nameCode f) 0

theorem namesTree_spec : ∀ {fs : List FnName} {t : NTree}, namesTree fs = some t →
    ∀ f, (t.find (nameCode f)).isSome = decide (f ∈ fs)
  | [], t, h, f => by
    simp only [namesTree, Option.some.injEq] at h; subst h
    simp [NTree.find]
  | g :: fs, t, h, f => by
    simp only [namesTree, Option.bind_eq_some_iff] at h
    obtain ⟨t₀, h0, hi⟩ := h
    have ih := namesTree_spec h0
    split at hi
    · rename_i hg
      cases hi
      rw [ih] at hg ⊢
      by_cases hfg : f = g
      · subst hfg; simpa using hg
      · simp [hfg]
    · obtain ⟨-, hf⟩ := NTree.find_insert hi
      rw [hf]
      by_cases hc : nameCode f = nameCode g
      · have := nameCode_inj hc; subst this; simp
      · have : f ≠ g := fun e => hc (e ▸ rfl)
        simp [hc, ih, this]

/-! ## The per-function check -/

/-- `WArr.okW` with the store set as a predicate. -/
def _root_.L.WArr.okWB (ctl : ArrId) (pa : ArrId → Bool) : WArr → Bool
  | .plain a => a ≠ ctl && pa a
  | .tier a _ => a ≠ ctl && a + tierOff ≠ ctl && pa a && pa (a + tierOff)

/-- `Stmt.okW` with the store sets as predicates and the callee set as a name tree. -/
def _root_.L.Stmt.okWB (ctl : ArrId) (pa : ArrId → Bool) (pc : Word → Bool) (t : NTree) : Stmt → Bool
  | .st8 .. => false
  | .st64 a i _ =>
    if a = ctl then (match ctlIdx i with | some ws => ws.all pc | none => false)
    else pa a
  | .st64t a _ _ _ => a ≠ ctl && a + tierOff ≠ ctl && pa a && pa (a + tierOff)
  | .copy64 d .. | .copy8w d .. => d.okWB ctl pa
  | .seq s u => s.okWB ctl pa pc t && u.okWB ctl pa pc t
  | .ite _ s u => s.okWB ctl pa pc t && u.okWB ctl pa pc t
  | .while _ s => s.okWB ctl pa pc t
  | .call _ f _ => (t.find (nameCode f)).isSome
  | _ => true

theorem _root_.L.Stmt.okW_of_okWB {ctl : ArrId} {pa : ArrId → Bool} {pc : Word → Bool} {t : NTree}
    {A : List ArrId} {C : List Word} {fs : List FnName} (ht : namesTree fs = some t)
    (hpa : ∀ a, pa a = true → a ∈ A) (hpc : ∀ w, pc w = true → w ∈ C) :
    ∀ {s : Stmt}, s.okWB ctl pa pc t = true → s.okW ctl A C fs = true := by
  intro s h
  induction s with
  | st8 => simp [Stmt.okWB] at h
  | st64 a i e =>
    by_cases hc : a = ctl
    · cases hi : ctlIdx i with
      | none => simp [Stmt.okWB, hc, hi] at h
      | some ws =>
        simp only [Stmt.okWB, hc, hi, ite_true, List.all_eq_true] at h
        simp only [Stmt.okW, hc, hi, ite_true, List.all_eq_true, decide_eq_true_eq]
        exact fun w hw => hpc w (h w hw)
    · simp only [Stmt.okWB, hc, ite_false] at h
      simp only [Stmt.okW, hc, ite_false]
      exact decide_eq_true (hpa a h)
  | st64t a _ _ _ =>
    simp only [Stmt.okWB, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Stmt.okW, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, hpa a h.1.2⟩, hpa _ h.2⟩
  | copy64 d _ _ _ _ =>
    cases d with
    | plain a =>
      simp only [Stmt.okWB, WArr.okWB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [Stmt.okW, WArr.okW, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, hpa a h.2⟩
    | tier a _ =>
      simp only [Stmt.okWB, WArr.okWB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [Stmt.okW, WArr.okW, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, hpa a h.1.2⟩, hpa _ h.2⟩
  | copy8w d _ _ _ _ =>
    cases d with
    | plain a =>
      simp only [Stmt.okWB, WArr.okWB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [Stmt.okW, WArr.okW, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, hpa a h.2⟩
    | tier a _ =>
      simp only [Stmt.okWB, WArr.okWB, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [Stmt.okW, WArr.okW, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨h.1.1.1, h.1.1.2⟩, hpa a h.1.2⟩, hpa _ h.2⟩
  | seq s u ihs ihu | ite _ s u ihs ihu =>
    simp only [Stmt.okWB, Bool.and_eq_true] at h
    simp only [Stmt.okW, Bool.and_eq_true]
    exact ⟨ihs h.1, ihu h.2⟩
  | «while» _ s ih =>
    simp only [Stmt.okWB] at h
    exact ih h
  | «call» _ f _ =>
    simp only [Stmt.okWB, namesTree_spec ht] at h
    exact h
  | _ => rfl

/-- One function's write-set check: not in the set, or its body passes `okWB`. -/
def wsChk (ctl : ArrId) (pa : ArrId → Bool) (pc : Word → Bool) (t : NTree)
    (x : FnName × FunDecl) : Bool :=
  !(t.find (nameCode x.1)).isSome || x.2.body.okWB ctl pa pc t

/-- **A program's write set from per-function checks**: the function set `fs` as a tree, the
store sets as predicates, and `wsChk` for every function of `p` (by `prog_all`). -/
theorem closedW_of_all {ctl : ArrId} {p : Prog} {A : List ArrId} {C : List Word}
    {fs : List FnName} {t : NTree} {pa : ArrId → Bool} {pc : Word → Bool}
    (ht : namesTree fs = some t) (hpa : ∀ a, pa a = true → a ∈ A)
    (hpc : ∀ w, pc w = true → w ∈ C) (h : ∀ x ∈ p, wsChk ctl pa pc t x = true) :
    closedW ctl p A C fs = true := by
  simp only [closedW, List.all_eq_true]
  intro f hf
  split
  · rename_i fd hfd
    obtain ⟨_, _, hp, -⟩ := List.lookup_eq_some_iff.mp hfd
    have hx := h _ (hp ▸ List.mem_append_right _ List.mem_cons_self)
    simp only [wsChk, namesTree_spec ht, hf, decide_true, Bool.not_true, Bool.false_or] at hx
    exact Stmt.okW_of_okWB ht hpa hpc hx
  · rfl

/-! ## The commands -/

open Lean Elab Command Meta
open Lean.Elab.Term (elabTermEnsuringType synthesizeSyntheticMVarsNoPostponing)

/-- `names_tree t : fs` declares `t : NTree`, the literal tree of the names `fs` (evaluated by
compiled code), and `t.eq : namesTree fs = some t` (one kernel check over the names). -/
syntax (name := namesTreeCmd) (docComment)? "names_tree " ident " : " term : command

@[command_elab namesTreeCmd] unsafe def elabNamesTree : CommandElab := fun stx => do
  let `($[$doc?:docComment]? names_tree $n:ident : $fsS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let fsE ← elabTermEnsuringType fsS (mkApp (mkConst ``List [0]) (mkConst ``String))
    synthesizeSyntheticMVarsNoPostponing
    let fsE ← instantiateMVars fsE
    let some tree ← evalTree (mkApp (mkConst ``namesTree) fsE)
      | throwError "names_tree: the tree does not evaluate"
    let treeTy := mkConst ``NTree
    addAndCompile (.defnDecl (mkDefinitionValEx name [] treeTy (ntreeToExpr tree) .abbrev .safe []))
    addDocString' name .missing doc?
    let someTree := mkApp2 (mkConst ``Option.some [0]) treeTy (mkConst name)
    let optTy := mkApp (mkConst ``Option [0]) treeTy
    addDecl (thm (name ++ `eq)
      (mkApp3 (mkConst ``Eq [1]) optTy (mkApp (mkConst ``namesTree) fsE) someTree)
      (mkApp2 (mkConst ``Eq.refl [1]) optTy someTree) [])

/-- `prog_all h : p chk` declares `h : ∀ x ∈ p, chk x = true`: one kernel check
(`h.c<j>`) per chunk of `progWfChunk` functions, put together by `forall_mem_cons_of` (no
evaluation). `p` must reduce to a list literal by `whnf`. -/
syntax (name := progAll) (docComment)? "prog_all " ident " : " term:max term:max : command

@[command_elab progAll] unsafe def elabProgAll : CommandElab := fun stx => do
  let `($[$doc?:docComment]? prog_all $n:ident : $progS $chkS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    let chk ← elabTermEnsuringType chkS (← mkArrow elemTy (mkConst ``Bool))
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let chk ← instantiateMVars chk
    let elems ← listElems pE
    let boolTy := mkConst ``Bool
    let bTrue := mkConst ``Bool.true
    let P ← withLocalDeclD `x elemTy fun x =>
      mkLambdaFVars #[x] (mkApp3 (mkConst ``Eq [1]) boolTy (mkApp chk x) bTrue)
    let k := progWfChunk.get (← getOptions)
    let mut parts : Array Lean.Expr := #[]
    let mut i := 0
    while i < elems.size do
      let chunk := elems.extract i (i + k)
      let lit ← mkListLit elemTy chunk.toList
      let ty ← withLocalDeclD `x elemTy fun x => do
        mkForallFVars #[x] (← mkArrow (← mkAppM ``Membership.mem #[lit, x]) (P.beta #[x]))
      let hN := name ++ Name.mkSimple s!"c{parts.size}"
      let pf := mkAppN (mkConst ``forall_of_all) #[elemTy, chk, lit,
        mkApp2 (mkConst ``Eq.refl [1]) boolTy bTrue]
      addDecl (thm hN ty pf [])
      parts := parts.push (mkConst hN)
      i := i + k
    let mut chain := mkApp2 (mkConst ``forall_mem_nil_of) elemTy P
    let mut tl := mkApp (mkConst ``List.nil [0]) elemTy
    for e in (List.range elems.size).reverse do
      let chunk := elems.extract (e / k * k) (e / k * k + k)
      let he := mkApp2 parts[e / k]! elems[e]! (memProof elemTy chunk (e % k))
      chain := mkAppN (mkConst ``forall_mem_cons_of) #[elemTy, P, elems[e]!, tl, he, chain]
      tl := mkApp3 (mkConst ``List.cons [0]) elemTy elems[e]! tl
    let ty ← withLocalDeclD `x elemTy fun x => do
      mkForallFVars #[x] (← mkArrow (← mkAppM ``Membership.mem #[pE, x]) (P.beta #[x]))
    addDecl (thm name ty chain [])
    addDocString' name .missing doc?

end L.Compiler
