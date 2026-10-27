module

public import ConAgua.L.Syntax

@[expose] public section

/-!
# Program-lookup bundles from the program text (lane `prooftools`)

`ProgHas p fs`: the program `p` binds every function of the list `fs` as `fs` does. It replaces
hand-written bundles

```
structure XProg (p : Prog) : Prop where
  base : YProg p
  f1 : p.lookup "f1" = some f1L
  …
```

by the function list the module already writes for its test program
(`def xProg : Prog := [("f1", f1L), …] ++ yProg`): `abbrev XProg (p : Prog) := ProgHas p xProg`.

* A lookup: `hp.get "f1" : p.lookup "f1" = some f1L` (the body is computed from `xProg` by `rfl`).
* A sub-bundle: `hp.right : ProgHas p yProg` for `xProg = l ++ yProg` (its names may not shadow
  `yProg`'s: a decided check on name codes, `by decide`), `hp.left`, `ProgHas.trans`.
* The test program's own bundle: `ProgHas.refl xProg` (no list of `rfl`s).
* An old-style structure bundle from a list: `by constructor <;> exact hp.get _`.
* `hp.agree fs'`: `p` agrees with `xProg` on a list of names (`closedW_of_agree`'s hypothesis).
-/

namespace L

/-- **`p` binds every function of `fs` as `fs` does** (`fs.lookup`, so a later duplicate in `fs`
says nothing). -/
def ProgHas (p fs : Prog) : Prop := ∀ f fd, fs.lookup f = some fd → p.lookup f = some fd

namespace ProgHas

variable {p q fs l₁ l₂ : Prog}

theorem refl (p : Prog) : ProgHas p p := fun _ _ h => h

theorem nil : ProgHas p [] := fun _ _ h => by cases h

theorem trans (h₁ : ProgHas p q) (h₂ : ProgHas q fs) : ProgHas p fs :=
  fun f fd h => h₁ f fd (h₂ f fd h)

/-- **One lookup**, its body computed from the list (`rfl` on `fs.lookup f`). -/
theorem get (h : ProgHas p fs) (f : FnName) {fd : FunDecl} (hf : fs.lookup f = some fd := by rfl) :
    p.lookup f = some fd := h f fd hf

theorem left (h : ProgHas p (l₁ ++ l₂)) : ProgHas p l₁ := fun f fd hf => h f fd (by
  rw [List.lookup_append, hf]; rfl)

/-- `l₁` binds none of `l₂`'s names (as `Nat` codes of their bytes, so the kernel does not compare
`String`s). -/
def NoShadow (l₁ l₂ : Prog) : Bool :=
  let ks := l₂.map fun x => x.1.toByteArray.data.toList
  l₁.all fun x => !ks.contains x.1.toByteArray.data.toList

theorem mem_of_lookup {l : Prog} {f : FnName} {fd : FunDecl} (h : l.lookup f = some fd) :
    ∃ x ∈ l, x.1 = f := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    rw [List.lookup_cons] at h
    split at h
    · rename_i hy; exact ⟨y, List.mem_cons_self, (beq_iff_eq.mp hy).symm⟩
    · obtain ⟨x, hx, e⟩ := ih h; exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

theorem lookup_none_of_noShadow {l₁ l₂ : Prog} (hd : NoShadow l₁ l₂ = true) {f : FnName}
    {fd : FunDecl} (hf : l₂.lookup f = some fd) : l₁.lookup f = none := by
  obtain ⟨y, hy, rfl⟩ := mem_of_lookup hf
  rw [List.lookup_eq_none_iff]
  intro x hx
  simp only [NoShadow, List.all_eq_true] at hd
  have := hd x hx
  rw [bne_iff_ne]
  intro e
  have hc : (List.map (fun x => x.fst.toByteArray.data.toList) l₂).contains
      x.fst.toByteArray.data.toList = true :=
    List.contains_iff_mem.mpr (List.mem_map.mpr ⟨y, hy, by rw [e]⟩)
  rw [hc] at this; simp at this

/-- **A sub-bundle**: the tail of the list, when the head does not shadow it. -/
theorem right (h : ProgHas p (l₁ ++ l₂)) (hd : NoShadow l₁ l₂ = true := by decide) :
    ProgHas p l₂ := fun f fd hf => h f fd (by
  rw [List.lookup_append, lookup_none_of_noShadow hd hf]; exact hf)

theorem append (h₁ : ProgHas p l₁) (h₂ : ProgHas p l₂) : ProgHas p (l₁ ++ l₂) := fun f fd hf => by
  rw [List.lookup_append] at hf
  cases h : l₁.lookup f with
  | none => rw [h] at hf; exact h₂ f fd hf
  | some g => rw [h] at hf; cases hf; exact h₁ f _ h

/-- Add one lookup in front. -/
theorem cons {f : FnName} {fd : FunDecl} (h₁ : p.lookup f = some fd) (h₂ : ProgHas p l₂) :
    ProgHas p ((f, fd) :: l₂) := fun g gd hg => by
  rw [List.lookup_cons] at hg
  split at hg
  · rename_i e; cases hg; rw [(beq_iff_eq.mp e)]; exact h₁
  · exact h₂ g gd hg

/-- **`p` and `q` agree on the names `ns`** (each bound in `fs`, which both have). -/
theorem agreeWith (h : ProgHas p fs) (hq : ProgHas q fs) (ns : List FnName)
    (hn : ns.all (fun f => (fs.lookup f).isSome) = true := by decide) :
    ∀ f ∈ ns, p.lookup f = q.lookup f := by
  intro f hf
  have := List.all_eq_true.mp hn f hf
  obtain ⟨fd, e⟩ := Option.isSome_iff_exists.mp this
  rw [h f fd e, hq f fd e]

/-- **`p` agrees with `fs` on the names `ns`** (each of them bound in `fs`). -/
theorem agree (h : ProgHas p fs) (ns : List FnName)
    (hn : ns.all (fun f => (fs.lookup f).isSome) = true := by decide) :
    ∀ f ∈ ns, p.lookup f = fs.lookup f := by
  intro f hf
  have := List.all_eq_true.mp hn f hf
  obtain ⟨fd, e⟩ := Option.isSome_iff_exists.mp this
  rw [e, h f fd e]

end ProgHas

end L
