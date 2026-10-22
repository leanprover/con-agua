module

public import ConAgua.Compiler.WF

@[expose] public section

/-!
# A kernel-fast `Prog.wf`

`Prog.wf` compares function names as `String`s: `p.lookup f` at every call (calls × functions
comparisons) and `Nodup` of the names (functions² comparisons). In the kernel each `String`
comparison unfolds `String.decEq` down to UTF-8 byte lists, so `decide +kernel` on a program
of ~500 functions and ~1300 calls took ~55 s (DESIGN.md, "Slow declarations").

`Prog.wfFast` checks the same thing with each name turned into a `Nat` once (`nameCode`, injective)
and the names kept in a binary search tree keyed by that code (`NTree`, built by `NTree.insert`,
which fails on a duplicate). Key comparisons are `Nat.decLt`/`Nat.decEq`, which the kernel does on
literals with GMP. `Prog.wf_of_wfFast` turns the check into `Prog.wf`:
`Prog.wf_of_wfFast (by decide +kernel)`.
-/

namespace L.Compiler

/-! ## Names as numbers -/

/-- Bijective base-257 numeration of a byte list (digits `1..256`, least significant first). -/
def bytesCode : List UInt8 → Nat
  | [] => 0
  | b :: l => (b.toNat + 1) + 257 * bytesCode l

theorem bytesCode_inj : ∀ {a b : List UInt8}, bytesCode a = bytesCode b → a = b
  | [], [], _ => rfl
  | [], b :: l, h => by simp only [bytesCode] at h; omega
  | b :: l, [], h => by simp only [bytesCode] at h; omega
  | b :: l, b' :: l', h => by
    simp only [bytesCode] at h
    have hb := b.toNat_lt; have hb' := b'.toNat_lt
    have h1 : b.toNat = b'.toNat := by omega
    have h2 : bytesCode l = bytesCode l' := by omega
    rw [UInt8.toNat_inj.mp h1, bytesCode_inj h2]

/-- A function name as a number. -/
def nameCode (s : String) : Nat := bytesCode s.toByteArray.data.toList

theorem nameCode_inj {a b : String} (h : nameCode a = nameCode b) : a = b := by
  have h := bytesCode_inj h
  apply String.toByteArray_inj.mp
  cases ha : a.toByteArray; cases hb : b.toByteArray
  rw [ha, hb] at h
  simp_all [Array.toList_inj]

/-! ## A search tree of names -/

/-- Binary search tree: name code ↦ parameter count. -/
inductive NTree where
  | leaf
  | node (l : NTree) (k v : Nat) (r : NTree)

def NTree.find (k : Nat) : NTree → Option Nat
  | .leaf => none
  | .node l k' v r => if k < k' then find k l else if k = k' then some v else find k r

/-- Insert `k ↦ v`; `none` if `k` is there already. -/
def NTree.insert (k v : Nat) : NTree → Option NTree
  | .leaf => some (.node .leaf k v .leaf)
  | .node l k' v' r =>
    if k < k' then (insert k v l).map (.node · k' v' r)
    else if k = k' then none
    else (insert k v r).map (.node l k' v' ·)

theorem NTree.find_insert {k v : Nat} : ∀ {t t' : NTree}, t.insert k v = some t' →
    t.find k = none ∧ ∀ k', t'.find k' = if k' = k then some v else t.find k'
  | .leaf, t', h => by
    simp only [insert, Option.some.injEq] at h; subst h
    refine ⟨rfl, fun k' => ?_⟩
    by_cases h : k' = k <;> simp [find, h]
  | .node l k₀ v₀ r, t', h => by
    simp only [insert] at h
    by_cases h1 : k < k₀
    · simp only [h1, ite_true, Option.map_eq_some_iff] at h
      obtain ⟨l', hl, rfl⟩ := h
      obtain ⟨hn, hf⟩ := find_insert hl
      refine ⟨by simp [find, h1, hn], fun k' => ?_⟩
      simp only [find, hf]
      by_cases h2 : k' < k₀
      · simp [h2]
      · have : k' ≠ k := by omega
        simp [this, h2]
    · by_cases h3 : k = k₀
      · simp [h3] at h
      · simp only [h1, h3, ite_false, Option.map_eq_some_iff] at h
        obtain ⟨r', hr, rfl⟩ := h
        obtain ⟨hn, hf⟩ := find_insert hr
        refine ⟨by simp [find, h1, h3, hn], fun k' => ?_⟩
        simp only [find, hf]
        by_cases h2 : k' < k₀
        · have : k' ≠ k := by omega
          simp [this, h2]
        · by_cases h4 : k' = k₀
          · simp [h4]; omega
          · simp [h2, h4]

/-- The tree of a program's names, built right to left (so the tree's maps are `p.lookup`'s);
`none` if a name occurs twice. -/
def progTree : Prog → Option NTree
  | [] => some .leaf
  | (f, fd) :: p => (progTree p).bind (·.insert (nameCode f) fd.nparams)

theorem progTree_spec : ∀ {p : Prog} {t : NTree}, progTree p = some t →
    (p.map (·.1)).Nodup ∧ ∀ f, t.find (nameCode f) = (p.lookup f).map (·.nparams)
  | [], t, h => by
    simp only [progTree, Option.some.injEq] at h; subst h
    exact ⟨List.nodup_nil, fun _ => rfl⟩
  | (f, fd) :: p, t, h => by
    simp only [progTree, Option.bind_eq_some_iff] at h
    obtain ⟨t₀, h0, hi⟩ := h
    obtain ⟨hnd, hf⟩ := progTree_spec h0
    obtain ⟨hn, hf'⟩ := NTree.find_insert hi
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩, fun g => ?_⟩
    · have := hf f
      rw [hn, eq_comm, Option.map_eq_none_iff, List.lookup_eq_none_iff] at this
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
      simpa [hxe] using this x hx
    · rw [hf', hf, List.lookup_cons]
      by_cases hg : g = f
      · simp [hg]
      · have : nameCode g ≠ nameCode f := fun h => hg (nameCode_inj h)
        have hb : (g == f) = false := by simpa using hg
        simp [hb, this]

/-! ## The check -/

/-- `Stmt.wf` with call targets looked up in the tree. -/
def Stmt.wfT (t : NTree) (nl : Nat) (tab : Tab) : Stmt → Bool
  | .skip | .brk | .abort => true
  | .set x e => x < nl && Expr.wf nl tab e
  | .st8 a i e => a < tab.nb && Expr.wf nl tab i && Expr.wf nl tab e
  | .st64 a i e => a < tab.nw && Expr.wf nl tab i && Expr.wf nl tab e
  | .seq s u => Stmt.wfT t nl tab s && Stmt.wfT t nl tab u
  | .ite c s u => Cond.wf nl tab c && Stmt.wfT t nl tab s && Stmt.wfT t nl tab u
  | .while c s => Cond.wf nl tab c && Stmt.wfT t nl tab s
  | .ret es => es.all (Expr.wf nl tab) && es.length ≤ tab.nres
  | .call xs f args => xs.all (· < nl) && xs.length ≤ tab.nres &&
      args.all (Expr.wf nl tab) &&
      match t.find (nameCode f) with
      | some n => args.length == n
      | none => false
  | .gset g e => g.id < tab.ng && Expr.wf nl tab e

theorem Stmt.wfT_eq {t : NTree} {p : Prog}
    (h : ∀ f, t.find (nameCode f) = (p.lookup f).map (·.nparams)) (nl : Nat) (tab : Tab) :
    ∀ s, Stmt.wfT t nl tab s = Stmt.wf p nl tab s
  | .skip | .brk | .abort | .set .. | .st8 .. | .st64 .. | .ret .. | .gset .. => rfl
  | .seq s u => by simp only [Stmt.wfT, Stmt.wf, Stmt.wfT_eq h nl tab s, Stmt.wfT_eq h nl tab u]
  | .ite c s u => by simp only [Stmt.wfT, Stmt.wf, Stmt.wfT_eq h nl tab s, Stmt.wfT_eq h nl tab u]
  | .while c s => by simp only [Stmt.wfT, Stmt.wf, Stmt.wfT_eq h nl tab s]
  | .call xs f args => by
    simp only [Stmt.wfT, Stmt.wf, h f]
    cases p.lookup f <;> rfl

def FunDecl.wfT (t : NTree) (tab : Tab) (fd : FunDecl) : Bool :=
  fd.nparams ≤ fd.nlocals && Stmt.wfT t fd.nlocals tab fd.body && 8 * frameWords fd + 8 < maxOff

/-- `Prog.wf`, kernel-fast (see the module doc). -/
def Prog.wfFast (tab : Tab) (p : Prog) : Bool :=
  match progTree p with
  | some t => p.all (fun (_, fd) => FunDecl.wfT t tab fd) &&
      16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng < maxOff
  | none => false

theorem Prog.wf_of_wfFast {tab : Tab} {p : Prog} (h : Prog.wfFast tab p = true) :
    Prog.wf tab p = true := by
  unfold Prog.wfFast at h
  split at h
  · rename_i t ht
    obtain ⟨hnd, hf⟩ := progTree_spec ht
    have hfd : ∀ fd, FunDecl.wfT t tab fd = FunDecl.wf p tab fd := fun fd => by
      simp only [FunDecl.wfT, FunDecl.wf, Stmt.wfT_eq hf]
    simp only [Prog.wf, hfd] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨h.1, hnd⟩, h.2⟩
  · simp at h

end L.Compiler
