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

/-! ## Names as numbers (`nameCode`, in `Compile.lean`) -/


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


theorem nameCode_inj {a b : String} (h : nameCode a = nameCode b) : a = b := by
  have h := bytesCode_inj h
  apply String.toByteArray_inj.mp
  cases ha : a.toByteArray; cases hb : b.toByteArray
  rw [ha, hb] at h
  simp_all [Array.toList_inj]

/-! ## A search tree of names (`NTree`, in `Compile.lean`) -/


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

/-! ### The check without the constant data

A check of `D.c8[i]` compares the byte string `D` with the table's constant data. For a large
`D` (the ROM, 37 KB) that dominates a function's check, and checking each function separately
(`WFSplit.lean`) would repeat it per function. `FunDecl.wfTN` leaves it out; `FunDecl.wfT_of_wfTN`
adds it back from one `romOk` fact per byte string the function reads (`Stmt.roms`). -/

/-- The byte string `d` is in the table's constant data where the code reads it. -/
def romOk (tab : Tab) (d : List UInt8) : Bool := d.isPrefixOf (tab.rom.drop (romIdx d tab.rom))

def Expr.wfN (nl : Nat) (tab : Tab) : Expr → Bool
  | .const _ => true
  | .var x => x < nl
  | .bin _ a b => Expr.wfN nl tab a && Expr.wfN nl tab b
  | .ld8 a i => a < tab.nb && Expr.wfN nl tab i
  | .ld64 a i => a < tab.nw && Expr.wfN nl tab i
  | .len8 a => a < tab.nb
  | .len64 a => a < tab.nw
  | .cmpw _ a b => Expr.wfN nl tab a && Expr.wfN nl tab b
  | .ldc _ i => Expr.wfN nl tab i
  | .glob g => g.id < tab.ng

def Cond.wfN (nl : Nat) (tab : Tab) : Cond → Bool
  | .cmp _ a b => Expr.wfN nl tab a && Expr.wfN nl tab b
  | .and p q | .or p q => Cond.wfN nl tab p && Cond.wfN nl tab q
  | .not p => Cond.wfN nl tab p

def Stmt.wfTN (t : NTree) (nl : Nat) (tab : Tab) : Stmt → Bool
  | .skip | .brk | .abort => true
  | .set x e => x < nl && Expr.wfN nl tab e
  | .st8 a i e => a < tab.nb && Expr.wfN nl tab i && Expr.wfN nl tab e
  | .st64 a i e => a < tab.nw && Expr.wfN nl tab i && Expr.wfN nl tab e
  | .seq s u => Stmt.wfTN t nl tab s && Stmt.wfTN t nl tab u
  | .ite c s u => Cond.wfN nl tab c && Stmt.wfTN t nl tab s && Stmt.wfTN t nl tab u
  | .while c s => Cond.wfN nl tab c && Stmt.wfTN t nl tab s
  | .ret es => es.all (Expr.wfN nl tab) && es.length ≤ tab.nres
  | .call xs f args => xs.all (· < nl) && xs.length ≤ tab.nres &&
      args.all (Expr.wfN nl tab) &&
      match t.find (nameCode f) with
      | some n => args.length == n
      | none => false
  | .gset g e => g.id < tab.ng && Expr.wfN nl tab e

def FunDecl.wfTN (t : NTree) (tab : Tab) (fd : FunDecl) : Bool :=
  fd.nparams ≤ fd.nlocals && Stmt.wfTN t fd.nlocals tab fd.body && 8 * frameWords fd + 8 < maxOff

theorem Expr.wf_of_wfN {nl : Nat} {tab : Tab} : ∀ {e : Expr}, Expr.wfN nl tab e = true →
    (∀ d ∈ Expr.roms e, romOk tab d = true) → Expr.wf nl tab e = true
  | .const _, h, _ | .var _, h, _ | .len8 _, h, _ | .len64 _, h, _ | .glob _, h, _ => h
  | .bin _ a b, h, hr | .cmpw _ a b, h, hr => by
    simp only [Expr.wfN, Expr.wf, Bool.and_eq_true, Expr.roms, List.mem_append] at h hr ⊢
    exact ⟨Expr.wf_of_wfN h.1 fun d hd => hr d (.inl hd), Expr.wf_of_wfN h.2 fun d hd => hr d (.inr hd)⟩
  | .ld8 _ i, h, hr | .ld64 _ i, h, hr => by
    simp only [Expr.wfN, Expr.wf, Bool.and_eq_true, Expr.roms] at h hr ⊢
    exact ⟨h.1, Expr.wf_of_wfN h.2 hr⟩
  | .ldc d i, h, hr => by
    simp only [Expr.wfN, Expr.wf, Bool.and_eq_true, Expr.roms, List.mem_cons] at h hr ⊢
    exact ⟨hr d (.inl rfl), Expr.wf_of_wfN h fun d' hd => hr d' (.inr hd)⟩

theorem Cond.wf_of_wfN {nl : Nat} {tab : Tab} : ∀ {c : Cond}, Cond.wfN nl tab c = true →
    (∀ d ∈ Cond.roms c, romOk tab d = true) → Cond.wf nl tab c = true
  | .cmp _ a b, h, hr => by
    simp only [Cond.wfN, Cond.wf, Bool.and_eq_true, Cond.roms, List.mem_append] at h hr ⊢
    exact ⟨Expr.wf_of_wfN h.1 fun d hd => hr d (.inl hd), Expr.wf_of_wfN h.2 fun d hd => hr d (.inr hd)⟩
  | .and p q, h, hr | .or p q, h, hr => by
    simp only [Cond.wfN, Cond.wf, Bool.and_eq_true, Cond.roms, List.mem_append] at h hr ⊢
    exact ⟨Cond.wf_of_wfN h.1 fun d hd => hr d (.inl hd), Cond.wf_of_wfN h.2 fun d hd => hr d (.inr hd)⟩
  | .not p, h, hr => Cond.wf_of_wfN (c := p) h hr

theorem Expr.all_wf_of_wfN {nl : Nat} {tab : Tab} {es : List Expr}
    (h : es.all (Expr.wfN nl tab) = true) (hr : ∀ d ∈ es.flatMap Expr.roms, romOk tab d = true) :
    es.all (Expr.wf nl tab) = true := by
  simp only [List.all_eq_true, List.mem_flatMap] at h hr ⊢
  exact fun e he => Expr.wf_of_wfN (h e he) fun d hd => hr d ⟨e, he, hd⟩

theorem Stmt.wfT_of_wfTN {t : NTree} {nl : Nat} {tab : Tab} : ∀ {s : Stmt}, Stmt.wfTN t nl tab s = true →
    (∀ d ∈ Stmt.roms s, romOk tab d = true) → Stmt.wfT t nl tab s = true
  | .skip, _, _ | .brk, _, _ | .abort, _, _ => rfl
  | .set _ e, h, hr | .gset _ e, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms] at h hr ⊢
    exact ⟨h.1, Expr.wf_of_wfN h.2 hr⟩
  | .st8 _ i e, h, hr | .st64 _ i e, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms, List.mem_append] at h hr ⊢
    exact ⟨⟨h.1.1, Expr.wf_of_wfN h.1.2 fun d hd => hr d (.inl hd)⟩,
      Expr.wf_of_wfN h.2 fun d hd => hr d (.inr hd)⟩
  | .seq s u, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms, List.mem_append] at h hr ⊢
    exact ⟨Stmt.wfT_of_wfTN h.1 fun d hd => hr d (.inl hd), Stmt.wfT_of_wfTN h.2 fun d hd => hr d (.inr hd)⟩
  | .ite c s u, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms, List.mem_append] at h hr ⊢
    exact ⟨⟨Cond.wf_of_wfN h.1.1 fun d hd => hr d (.inl (.inl hd)),
      Stmt.wfT_of_wfTN h.1.2 fun d hd => hr d (.inl (.inr hd))⟩,
      Stmt.wfT_of_wfTN h.2 fun d hd => hr d (.inr hd)⟩
  | .while c s, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms, List.mem_append] at h hr ⊢
    exact ⟨Cond.wf_of_wfN h.1 fun d hd => hr d (.inl hd), Stmt.wfT_of_wfTN h.2 fun d hd => hr d (.inr hd)⟩
  | .ret es, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms] at h hr ⊢
    exact ⟨Expr.all_wf_of_wfN h.1 hr, h.2⟩
  | .call xs f args, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms] at h hr ⊢
    exact ⟨⟨h.1.1, Expr.all_wf_of_wfN h.1.2 hr⟩, h.2⟩

theorem FunDecl.wfT_of_wfTN {t : NTree} {tab : Tab} {fd : FunDecl} (h : FunDecl.wfTN t tab fd = true)
    (hr : ∀ d ∈ Stmt.roms fd.body, romOk tab d = true) : FunDecl.wfT t tab fd = true := by
  simp only [FunDecl.wfTN, FunDecl.wfT, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, Stmt.wfT_of_wfTN h.1.2 hr⟩, h.2⟩

/-- A function's part of `Prog.wf_of_parts'`. -/
def FunOk (t : NTree) (tab : Tab) (x : FnName × FunDecl) : Prop :=
  FunDecl.wfTN t tab x.2 = true ∧ ∀ d ∈ Stmt.roms x.2.body, romOk tab d = true

theorem forall_funOk {t : NTree} {tab : Tab} {l : Prog}
    (h : ∀ x ∈ l, FunDecl.wfTN t tab x.2 = true) (hr : ∀ x ∈ l, ∀ d ∈ Stmt.roms x.2.body, romOk tab d = true) :
    ∀ x ∈ l, FunOk t tab x := fun x hx => ⟨h x hx, hr x hx⟩

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
      simp only [FunDecl.wfT, FunDecl.wf_eq, FunDecl.wfSpec, Stmt.wfT_eq hf]
    simp only [Prog.wf_eq, Prog.wfSpec, hfd] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨h.1, hnd⟩, h.2⟩
  · simp at h

/-! ## Per-function checks composed (`WFSplit.lean`'s `prog_wf`)

`Prog.wf_of_parts`: the program check from the name tree (`progTree p = some t`, which reads only
the names), one `FunDecl.wfT t tab fd` per function (each its own kernel check, so no kernel
evaluation sees every body at once), and the table bound. -/

theorem Prog.wf_of_parts {tab : Tab} {p : Prog} {t : NTree} (ht : progTree p = some t)
    (hf : ∀ x ∈ p, FunDecl.wfT t tab x.2 = true)
    (htab : 16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng < maxOff) :
    Prog.wf tab p = true := by
  obtain ⟨hnd, hfind⟩ := progTree_spec ht
  have hfd : ∀ fd, FunDecl.wfT t tab fd = FunDecl.wf p tab fd := fun fd => by
    simp only [FunDecl.wfT, FunDecl.wf_eq, FunDecl.wfSpec, Stmt.wfT_eq hfind]
  simp only [Prog.wf_eq, Prog.wfSpec, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨⟨fun x hx => (hfd x.2) ▸ hf x hx, hnd⟩, htab⟩

theorem Prog.wf_of_parts' {tab : Tab} {p : Prog} {t : NTree} (ht : progTree p = some t)
    (hf : ∀ x ∈ p, FunOk t tab x)
    (htab : 16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng < maxOff) :
    Prog.wf tab p = true :=
  Prog.wf_of_parts ht (fun x hx => FunDecl.wfT_of_wfTN (hf x hx).1 (hf x hx).2) htab

theorem forall_mem_cons_of {α : Type} {P : α → Prop} {a : α} {l : List α} (h : P a)
    (hl : ∀ x ∈ l, P x) : ∀ x ∈ a :: l, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hl x hx

theorem forall_of_all {α : Type} (f : α → Bool) (l : List α) (h : l.all f = true) :
    ∀ x ∈ l, f x = true := by
  simpa [List.all_eq_true] using h

theorem forall_mem_append_of {α : Type} {P : α → Prop} {l₁ l₂ : List α} (h₁ : ∀ x ∈ l₁, P x)
    (h₂ : ∀ x ∈ l₂, P x) : ∀ x ∈ l₁ ++ l₂, P x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ x hx
  · exact h₂ x hx

theorem forall_mem_nil_of {α : Type} (P : α → Prop) : ∀ x ∈ ([] : List α), P x := by simp

/-- `KnotWF`-style checks of some functions of a program (`fs`, often a prefix of `p`) without
`Prog.wf`: each function's `FunDecl.wf` and the names' distinctness, from the fast check. -/
def Prog.funsWfFast (tab : Tab) (p fs : Prog) : Bool :=
  match progTree p with
  | some t => fs.all fun (_, fd) => FunDecl.wfT t tab fd
  | none => false

theorem Prog.funsWf_of_fast {tab : Tab} {p fs : Prog} (h : Prog.funsWfFast tab p fs = true) :
    (fs.all fun (_, fd) => FunDecl.wf p tab fd) = true ∧ decide (p.map (·.1)).Nodup = true := by
  unfold Prog.funsWfFast at h
  split at h
  · rename_i t ht
    obtain ⟨hnd, hf⟩ := progTree_spec ht
    have hfd : ∀ fd, FunDecl.wfT t tab fd = FunDecl.wf p tab fd := fun fd => by
      simp only [FunDecl.wfT, FunDecl.wf_eq, FunDecl.wfSpec, Stmt.wfT_eq hf]
    simp only [hfd] at h
    exact ⟨h, by simpa using hnd⟩
  · simp at h

end L.Compiler
