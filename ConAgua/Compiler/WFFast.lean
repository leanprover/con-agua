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

/-- Inserting a key that is not there succeeds. -/
theorem NTree.insert_isSome {k v : Nat} : ∀ {t : NTree}, t.find k = none → (t.insert k v).isSome
  | .leaf, _ => rfl
  | .node l k' v' r, h => by
    simp only [find] at h
    simp only [insert]
    by_cases h1 : k < k'
    · simp only [h1, ite_true] at h ⊢; simpa using insert_isSome h
    · by_cases h2 : k = k'
      · simp [h2] at h
      · simp only [h1, h2, ite_false] at h ⊢; simpa using insert_isSome h

/-- With distinct names, `Prog.nrt` maps every function to its result count (`Compile.lean`). -/
theorem Prog.nrTree_spec : ∀ {p : Prog}, (p.map (·.1)).Nodup →
    ∃ t, Prog.nrTree p = some t ∧ ∀ f, t.find (nameCode f) = (p.lookup f).map (Stmt.nret ·.body)
  | [], _ => ⟨.leaf, rfl, fun _ => rfl⟩
  | (f, fd) :: p, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨t₀, h0, hf⟩ := Prog.nrTree_spec hnd.2
    have hn : t₀.find (nameCode f) = none := by
      rw [hf, Option.map_eq_none_iff, List.lookup_eq_none_iff]
      intro x hx
      have : f ≠ x.1 := fun he => hnd.1 (List.mem_map.mpr ⟨x, hx, he.symm⟩)
      simpa using this
    obtain ⟨t₁, h1⟩ := Option.isSome_iff_exists.mp (NTree.insert_isSome (v := Stmt.nret fd.body) hn)
    obtain ⟨_, hf'⟩ := NTree.find_insert h1
    refine ⟨t₁, by simp [Prog.nrTree, h0, h1], fun g => ?_⟩
    rw [hf', hf, List.lookup_cons]
    by_cases hg : g = f
    · simp [hg]
    · have : nameCode g ≠ nameCode f := fun h => hg (nameCode_inj h)
      have hb : (g == f) = false := by simpa using hg
      simp [hb, this]

/-- `nrOf (Prog.nrt p)` gives every function's result count, if the names are distinct. -/
theorem nrOf_nrt {p : Prog} (hnd : (p.map (·.1)).Nodup) (tab : Tab) {f : FnName} {fd : FunDecl}
    (h : p.lookup f = some fd) : nrOf (Prog.nrt p) tab f = Stmt.nret fd.body := by
  obtain ⟨t, ht, hf⟩ := Prog.nrTree_spec hnd
  simp [nrOf, Prog.nrt, ht, hf, h]

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
    · rw [if_pos hs] at hi
      obtain ⟨_, hf'⟩ := NTree.find_insert hi
      rw [hf'] at hv
      by_cases hk : k = nameCode f
      · rw [if_pos hk] at hv; cases hv
        simp only [skipsCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
        exact ⟨f, fd, List.mem_cons_self .., hk, hs.1.1, rfl⟩
      · rw [if_neg hk] at hv
        obtain ⟨g, gd, hm, h1, h2, h3⟩ := ih k v hv
        exact ⟨g, gd, List.mem_cons_of_mem _ hm, h1, h2, h3⟩
    · rw [if_neg hs] at hi; cases hi
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
  | .st64t a tt i e => a < tab.wK && Expr.isSimple tt && Expr.wf nl tab tt &&
      Expr.wf nl tab i && Expr.wf nl tab e
  | .copy64 d di s si n => WArr.wf nl tab d && Expr.opndWf nl tab di && WArr.wf nl tab s &&
      Expr.opndWf nl tab si && Expr.opndWf nl tab n
  | .copy8w d di s si n => WArr.wf nl tab d && Expr.opndWf nl tab di && BSrc.wf tab s &&
      Expr.opndWf nl tab si && Expr.opndWf nl tab n
  | .scan8 x s i e c => x < nl && BSrc.wf tab s && Expr.opndWf nl tab i && Expr.opndWf nl tab e &&
      c.length == 256 && c.isPrefixOf (tab.rom.drop (romIdx c tab.rom))

theorem Stmt.wfT_eq {t : NTree} {p : Prog}
    (h : ∀ f, t.find (nameCode f) = (p.lookup f).map (·.nparams)) (nl : Nat) (tab : Tab) :
    ∀ s, Stmt.wfT t nl tab s = Stmt.wf p nl tab s
  | .skip | .brk | .abort | .set .. | .st8 .. | .st64 .. | .ret .. | .gset .. | .st64t ..
  | .copy64 .. | .copy8w .. | .scan8 .. => rfl
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

/-- `BSrc.wf` without the constant data check (the bytes come back through `Stmt.roms`). -/
def BSrc.wfN (tab : Tab) : BSrc → Bool
  | .arr a => a < tab.nb
  | .rom d => d.length < 2 ^ 31

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
  | .ld64t a t i => a < tab.wK && Expr.wfN nl tab t && Expr.wfN nl tab i
  | .len64t a t => a < tab.wK && Expr.wfN nl tab t
  | .ld8x8 s i => BSrc.wfN tab s && Expr.wfN nl tab i

def WArr.wfN (nl : Nat) (tab : Tab) : WArr → Bool
  | .plain a => a < tab.nw
  | .tier a t => a < tab.wK && Expr.isOpnd t && Expr.wfN nl tab t

def Expr.opndWfN (nl : Nat) (tab : Tab) (e : Expr) : Bool := Expr.isOpnd e && Expr.wfN nl tab e

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
  | .st64t a tt i e => a < tab.wK && Expr.isSimple tt && Expr.wfN nl tab tt &&
      Expr.wfN nl tab i && Expr.wfN nl tab e
  | .copy64 d di s si n => WArr.wfN nl tab d && Expr.opndWfN nl tab di && WArr.wfN nl tab s &&
      Expr.opndWfN nl tab si && Expr.opndWfN nl tab n
  | .copy8w d di s si n => WArr.wfN nl tab d && Expr.opndWfN nl tab di && BSrc.wfN tab s &&
      Expr.opndWfN nl tab si && Expr.opndWfN nl tab n
  | .scan8 x s i e c => x < nl && BSrc.wfN tab s && Expr.opndWfN nl tab i && Expr.opndWfN nl tab e &&
      c.length == 256

def FunDecl.wfTN (t : NTree) (tab : Tab) (fd : FunDecl) : Bool :=
  fd.nparams ≤ fd.nlocals && Stmt.wfTN t fd.nlocals tab fd.body && 8 * frameWords fd + 8 < maxOff

theorem BSrc.wf_of_wfN {tab : Tab} : ∀ {b : BSrc}, BSrc.wfN tab b = true →
    (∀ d ∈ BSrc.roms b, romOk tab d = true) → BSrc.wf tab b = true
  | .arr _, h, _ => h
  | .rom d, h, hr => by
    simp only [BSrc.wfN, BSrc.wf, BSrc.roms, List.mem_singleton, forall_eq, romOk, Bool.and_eq_true] at h hr ⊢
    exact ⟨hr, h⟩

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
  | .ld64t _ t i, h, hr => by
    simp only [Expr.wfN, Expr.wf, Bool.and_eq_true, Expr.roms, List.mem_append] at h hr ⊢
    exact ⟨⟨h.1.1, Expr.wf_of_wfN h.1.2 fun d hd => hr d (.inl hd)⟩,
      Expr.wf_of_wfN h.2 fun d hd => hr d (.inr hd)⟩
  | .len64t _ t, h, hr => by
    simp only [Expr.wfN, Expr.wf, Bool.and_eq_true, Expr.roms] at h hr ⊢
    exact ⟨h.1, Expr.wf_of_wfN h.2 hr⟩
  | .ld8x8 b i, h, hr => by
    simp only [Expr.wfN, Expr.wf, Bool.and_eq_true, Expr.roms, List.mem_append] at h hr ⊢
    exact ⟨BSrc.wf_of_wfN h.1 fun d hd => hr d (.inl hd), Expr.wf_of_wfN h.2 fun d hd => hr d (.inr hd)⟩

theorem WArr.wf_of_wfN {nl : Nat} {tab : Tab} : ∀ {w : WArr}, WArr.wfN nl tab w = true →
    (∀ d ∈ WArr.roms w, romOk tab d = true) → WArr.wf nl tab w = true
  | .plain _, h, _ => h
  | .tier _ t, h, hr => by
    simp only [WArr.wfN, WArr.wf, Bool.and_eq_true, WArr.roms] at h hr ⊢
    exact ⟨h.1, Expr.wf_of_wfN h.2 hr⟩

theorem Expr.opndWf_of_wfN {nl : Nat} {tab : Tab} {e : Expr} (h : Expr.opndWfN nl tab e = true)
    (hr : ∀ d ∈ Expr.roms e, romOk tab d = true) : Expr.opndWf nl tab e = true := by
  simp only [Expr.opndWfN, Expr.opndWf, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, Expr.wf_of_wfN h.2 hr⟩

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
  | .st64t _ t i e, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms, List.mem_append] at h hr ⊢
    exact ⟨⟨⟨⟨h.1.1.1.1, h.1.1.1.2⟩, Expr.wf_of_wfN h.1.1.2 fun d hd => hr d (.inl (.inl hd))⟩,
      Expr.wf_of_wfN h.1.2 fun d hd => hr d (.inl (.inr hd))⟩,
      Expr.wf_of_wfN h.2 fun d hd => hr d (.inr hd)⟩
  | .copy64 d di s si n, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms, List.mem_append] at h hr ⊢
    exact ⟨⟨⟨⟨WArr.wf_of_wfN h.1.1.1.1 fun x hx => hr x (.inl (.inl (.inl (.inl hx)))),
      Expr.opndWf_of_wfN h.1.1.1.2 fun x hx => hr x (.inl (.inl (.inl (.inr hx))))⟩,
      WArr.wf_of_wfN h.1.1.2 fun x hx => hr x (.inl (.inl (.inr hx)))⟩,
      Expr.opndWf_of_wfN h.1.2 fun x hx => hr x (.inl (.inr hx))⟩,
      Expr.opndWf_of_wfN h.2 fun x hx => hr x (.inr hx)⟩
  | .copy8w d di s si n, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms, List.mem_append] at h hr ⊢
    exact ⟨⟨⟨⟨WArr.wf_of_wfN h.1.1.1.1 fun x hx => hr x (.inl (.inl (.inl (.inl hx)))),
      Expr.opndWf_of_wfN h.1.1.1.2 fun x hx => hr x (.inl (.inl (.inl (.inr hx))))⟩,
      BSrc.wf_of_wfN h.1.1.2 fun x hx => hr x (.inl (.inl (.inr hx)))⟩,
      Expr.opndWf_of_wfN h.1.2 fun x hx => hr x (.inl (.inr hx))⟩,
      Expr.opndWf_of_wfN h.2 fun x hx => hr x (.inr hx)⟩
  | .scan8 x s i e c, h, hr => by
    simp only [Stmt.wfTN, Stmt.wfT, Bool.and_eq_true, Stmt.roms, List.mem_append,
      List.mem_singleton] at h hr ⊢
    exact ⟨⟨⟨⟨⟨h.1.1.1.1, BSrc.wf_of_wfN h.1.1.1.2 fun y hy => hr y (.inl (.inl (.inl hy)))⟩,
      Expr.opndWf_of_wfN h.1.1.2 fun y hy => hr y (.inl (.inl (.inr hy)))⟩,
      Expr.opndWf_of_wfN h.1.2 fun y hy => hr y (.inl (.inr hy))⟩, h.2⟩, hr c (.inr rfl)⟩

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

theorem forall_mem_nil_of {α : Type} (P : α → Prop) : ∀ x ∈ ([] : List α), P x := by simp

end L.Compiler
