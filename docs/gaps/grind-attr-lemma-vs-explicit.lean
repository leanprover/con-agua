/-
# grind: a `@[grind =]` lemma fails where the same lemma passed explicitly succeeds

Toolchain: leanprover/lean4:nightly-2026-10-20.

Expected: both examples succeed; `St.setLoc_mem` is registered with `@[grind =]`, so
`grind` should use it as when it is passed as `grind [St.setLoc_mem]`.

Observed: the first example fails, the second succeeds. With one `setLoc` layer instead of two
(`(s₃.setLoc 6 v).mem.words.size`) both succeed. The same happens with a lemma registered in a
custom attribute set (`register_grind_attr`) and `grind [lang_grind]`.

Found in con-agua (`ConAgua/Arena/NatAdd.lean`, the add loop, while trying plain
`vcgen … <;> grind [lang_grind, arena_grind]` instead of the house form): the frame `.mem` of a
state several `setLoc`s deep.
-/

structure Mem where
  words : Array (Array UInt64)

structure St where
  mem : Mem
  loc : Nat → UInt64

def St.setLoc (s : St) (x : Nat) (v : UInt64) : St :=
  { s with loc := fun y => if y = x then v else s.loc y }

def Mem.set64 (m : Mem) (a : Nat) (i v : UInt64) : Mem :=
  { m with words := m.words.set! a ((m.words.getD a #[]).set! i.toNat v) }

theorem St.setLoc_mem (s : St) (x : Nat) (v : UInt64) : (s.setLoc x v).mem = s.mem := rfl
theorem Mem.words_size_set64 (m : Mem) (a : Nat) (i v : UInt64) :
    (m.set64 a i v).words.size = m.words.size := by simp [Mem.set64]

attribute [grind =] St.setLoc_mem Mem.words_size_set64

-- fails
example (s₀ s₁ s₃ : St) (r v w : UInt64) (hw : 0 < s₀.mem.words.size) (h1 : s₁.mem = s₀.mem)
    (h5 : s₃.mem = (s₁.setLoc 9 r).mem.set64 0 v w) :
    0 < ((s₃.setLoc 7 r).setLoc 6 v).mem.words.size := by
  grind

-- works: the same lemma passed explicitly
example (s₀ s₁ s₃ : St) (r v w : UInt64) (hw : 0 < s₀.mem.words.size) (h1 : s₁.mem = s₀.mem)
    (h5 : s₃.mem = (s₁.setLoc 9 r).mem.set64 0 v w) :
    0 < ((s₃.setLoc 7 r).setLoc 6 v).mem.words.size := by
  grind [St.setLoc_mem]
