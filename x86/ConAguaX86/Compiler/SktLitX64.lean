module

public import Lean
public meta import Lean
public import ConAguaX86.Compiler.CompileX64
public meta import ConAguaX86.Compiler.CompileX64
public import ConAgua.Compiler.WFSplit
public meta import ConAgua.Compiler.WFSplit

@[expose] public section

namespace L.Compiler

open Lean Elab Command Meta
open Lean.Elab.Term (TermElab elabTermEnsuringType synthesizeSyntheticMVarsNoPostponing)

/-- Every entry of `Prog.skTree entry p` is the frame (`fnFrame`) of a function of `p` other than
`entry`. -/
theorem Prog.skTree_spec (entry : FnName) : ∀ {p : Prog} {t : NTree}, Prog.skTree entry p = some t →
    ∀ k v, t.find k = some v → ∃ f fd, (f, fd) ∈ p ∧ k = nameCode f ∧ f ≠ entry ∧ v = fnFrame fd
  | [], t, h => by
    simp only [Prog.skTree, Option.some.injEq] at h; subst h
    intro k v hv; simp [NTree.find] at hv
  | (f, fd) :: p, t, h => by
    simp only [Prog.skTree, Option.bind_eq_some_iff] at h
    obtain ⟨t₀, h0, hi⟩ := h
    have ih := Prog.skTree_spec entry h0
    intro k v hv
    by_cases hs : skipsCheck entry f fd = true
    · rw [ite_eq_left hs] at hi
      obtain ⟨_, hf'⟩ := NTree.find_insert hi
      rw [hf'] at hv
      by_cases hk : k = nameCode f
      · rw [ite_eq_left hk] at hv; cases hv
        simp only [skipsCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
        exact ⟨f, fd, List.mem_cons_self .., hk, hs.1.1, rfl⟩
      · rw [ite_eq_right hk] at hv
        obtain ⟨g, gd, hm, h1, h2, h3⟩ := ih k v hv
        exact ⟨g, gd, List.mem_cons_of_mem _ hm, h1, h2, h3⟩
    · rw [ite_eq_right hs] at hi; cases hi
      obtain ⟨g, gd, hm, h1, h2, h3⟩ := ih k v hv
      exact ⟨g, gd, List.mem_cons_of_mem _ hm, h1, h2, h3⟩

/-- Every entry of `Prog.skt p entry` is the frame of a function of `p` other than `entry`. -/
theorem Prog.skt_spec {p : Prog} {entry : FnName} {k v : Nat} (h : (Prog.skt p entry).find k = some v) :
    ∃ f fd, (f, fd) ∈ p ∧ k = nameCode f ∧ f ≠ entry ∧ v = fnFrame fd := by
  unfold Prog.skt at h
  cases ht : Prog.skTree entry p with
  | none => rw [ht] at h; simp [NTree.find] at h
  | some t => rw [ht] at h; exact Prog.skTree_spec entry ht k v h

/-- The entry is not in `Prog.skt`: it checks the stack itself. -/
theorem skOf_skt_entry (p : Prog) (entry : FnName) : skOf (Prog.skt p entry) entry = 0 := by
  unfold skOf
  cases h : (Prog.skt p entry).find (nameCode entry) with
  | none => rfl
  | some v =>
    obtain ⟨f, fd, -, hk, hne, -⟩ := Prog.skt_spec h
    exact absurd (nameCode_inj hk).symm hne

/-- `x`'s entry in `Prog.skt`'s tree, if it skips its stack check (`skipsCheck`). -/
def skEntry (entry : FnName) (x : FnName × FunDecl) : Option (Nat × Nat) :=
  if skipsCheck entry x.1 x.2 then some (nameCode x.1, fnFrame x.2) else none

/-- The tree of a list of entries, the last inserted first (`Prog.skTree`'s order). -/
def insAll : List (Nat × Nat) → Option NTree
  | [] => some .leaf
  | (k, v) :: l => (insAll l).bind (·.insert k v)

theorem skTree_eq_insAll (entry : FnName) :
    ∀ p : Prog, Prog.skTree entry p = insAll (p.filterMap (skEntry entry))
  | [] => rfl
  | (f, fd) :: p => by
    rw [Prog.skTree, skTree_eq_insAll entry p, List.filterMap_cons, skEntry]
    by_cases h : skipsCheck entry f fd <;> simp [h, insAll]

/-- `Prog.skt` from its parts: the program is the parts `cs`, whose entries are `ls`. -/
theorem skt_of_parts {p : Prog} {entry : FnName} {t : NTree} (cs : List Prog)
    (ls : List (List (Nat × Nat))) (hp : p = cs.flatten)
    (hl : cs.map (List.filterMap (skEntry entry)) = ls) (ht : (insAll ls.flatten).getD .leaf = t) :
    Prog.skt p entry = t := by
  subst hp
  rw [Prog.skt, skTree_eq_insAll, List.filterMap_flatten, hl, ht]

theorem map_cons_of {α β : Type} {f : α → β} {a : α} {b : β} {l : List α} {r : List β}
    (h : f a = b) (hr : l.map f = r) : (a :: l).map f = b :: r := by
  simp [h, hr]

meta unsafe def evalPairs (e : Lean.Expr) : MetaM (List (Nat × Nat)) :=
  evalExpr (List (Nat × Nat)) (mkApp (mkConst ``List [0])
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat))) e

/-- `skt_part name : p entry lo hi` declares `name.part<lo> : (chunk).filterMap (skEntry entry) =
lit`, for the functions `lo ≤ i < hi` of `p` as a list literal (`chunk`) and `lit` evaluated by
compiled code: a part of `skt_lit name`'s kernel check, in a module of its own (Lake builds the
parts in parallel). -/
syntax (name := sktPart) "skt_part " ident " : " term:max term:max num num : command

@[command_elab sktPart] meta unsafe def elabSktPart : CommandElab := fun stx => do
  let `(skt_part $n:ident : $progS $entryS $lo $hi) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    let entryE ← elabTermEnsuringType entryS (mkConst ``String)
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let entryE ← instantiateMVars entryE
    let elems ← listElems pE
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
    let chunk ← mkListLit elemTy (elems.extract lo.getNat hi.getNat).toList
    let lhs := mkApp4 (mkConst ``List.filterMap [0, 0]) elemTy pairTy (mkApp (mkConst ``skEntry) entryE) chunk
    let ps ← evalPairs lhs
    let lpTy := mkApp (mkConst ``List [0]) pairTy
    addDecl (thm (name ++ Name.mkSimple s!"part{lo.getNat}") (mkApp3 (mkConst ``Eq [1]) lpTy lhs (natPairsToExpr ps))
      (mkApp2 (mkConst ``Eq.refl [1]) lpTy lhs) [])

/-- The length of a list literal. -/
meta partial def litLength (e : Lean.Expr) : Nat :=
  if e.isAppOfArity ``List.cons 3 then 1 + litLength e.appArg! else 0

/-- `skt_lit name : p entry` declares `name : NTree`, the literal of `Prog.skt p entry` (the frames of
`p`'s leaves without a stack check, evaluated by compiled code), and `name_eq : Prog.skt p entry =
name`, checked by the kernel (once; the per-function checks of `asm_lit` then read the literal).
If parts `name.part0`, `name.part<i>`, … (`skt_part`, consecutive, covering `p`) are declared,
`name_eq` is put together from them (`skt_of_parts`): the kernel then inserts their entries into
the tree, without evaluating a function's frame. -/
syntax (name := sktLit) "skt_lit " ident " : " term:max term:max : command

@[command_elab sktLit] meta unsafe def elabSktLit : CommandElab := fun stx => do
  let `(skt_lit $n:ident : $progS $entryS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    let entryE ← elabTermEnsuringType entryS (mkConst ``String)
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let entryE ← instantiateMVars entryE
    let lhs := mkApp2 (mkConst ``Prog.skt) pE entryE
    let t ← evalNTree lhs
    let treeTy := mkConst ``NTree
    withExporting <| addAndCompile (.defnDecl (mkDefinitionValEx name [] treeTy (ntreeToExpr t) .abbrev .safe []))
    let eqTy := mkApp3 (mkConst ``Eq [1]) treeTy lhs (mkConst name)
    let partN (i : Nat) := name ++ Name.mkSimple s!"part{i}"
    if !(← getEnv).contains (partN 0) then
      addDecl (thm (name.appendAfter "_eq") eqTy (mkApp2 (mkConst ``Eq.refl [1]) treeTy lhs) [])
      return
    -- the parts, in order
    let mut cs : Array Lean.Expr := #[]
    let mut ls : Array Lean.Expr := #[]
    let mut hs : Array Lean.Expr := #[]
    let mut i := 0
    while true do
      let some ci := (← getEnv).find? (partN i) | break
      let some (_, l, r) := ci.type.eq? | throwError "skt_lit: {partN i} is not an equation"
      let c := l.appArg!
      cs := cs.push c; ls := ls.push r; hs := hs.push (mkConst (partN i))
      let len := litLength c
      if len == 0 then break
      i := i + len
    let n := (← listElems pE).size
    unless i == n do throwError "skt_lit: the parts cover {i} of the {n} functions"
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    let progTy := mkApp (mkConst ``List [0]) elemTy
    let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
    let lpTy := mkApp (mkConst ``List [0]) pairTy
    let csE ← mkListLit progTy cs.toList
    let lsE ← mkListLit lpTy ls.toList
    -- `p = cs.flatten`, by the kernel (the same element terms)
    let hp := mkApp2 (mkConst ``Eq.refl [1]) progTy pE
    -- `cs.map (filterMap (skEntry entry)) = ls`, one part at a time
    let f := mkApp3 (mkConst ``List.filterMap [0, 0]) elemTy pairTy (mkApp (mkConst ``skEntry) entryE)
    let mut hl := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``List [0]) lpTy) (mkApp (mkConst ``List.nil [0]) lpTy)
    let mut ctl := mkApp (mkConst ``List.nil [0]) progTy
    let mut ltl := mkApp (mkConst ``List.nil [0]) lpTy
    for j in (List.range cs.size).reverse do
      hl := mkAppN (mkConst ``map_cons_of) #[progTy, lpTy, f, cs[j]!, ls[j]!, ctl, ltl, hs[j]!, hl]
      ctl := mkApp3 (mkConst ``List.cons [0]) progTy cs[j]! ctl
      ltl := mkApp3 (mkConst ``List.cons [0]) lpTy ls[j]! ltl
    -- the tree of the entries, by the kernel (insertions of number pairs)
    let ht := mkApp2 (mkConst ``Eq.refl [1]) treeTy (mkConst name)
    let pf := mkAppN (mkConst ``skt_of_parts) #[pE, entryE, mkConst name, csE, lsE, hp, hl, ht]
    addDecl (thm (name.appendAfter "_eq") eqTy pf [])

end L.Compiler
