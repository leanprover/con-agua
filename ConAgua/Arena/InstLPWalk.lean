import ConAgua.Arena.InstLPSpec
import ConAgua.Arena.WhnfBase
import ConAgua.Census.Attr

/-!
# The `instLP` walk: models and specs

Word-level models of `sl_memo`, `sls_memo`, `lp_go`, its six arms, `inst_lp_core` and `inst_lp`
(`InstLP.lean`). Every callee but the three memos' `find`/`put`/`clear` is called through
`callW` (`WhnfBase.lean`: a callee's run is a function of the caller's memory), so the models are
plain transcriptions of the bodies and each spec is one `vcgen` with `callW_spec` as the callee
specs; what the callees do is the refinement's business (`InstLPWalkRef*.lean`). The recursion
`lp_go` ↔ arms is the L fuel `n`: the model at `n + 1` calls its callees at `n`.

`lp_app`, `lp_lam`, `lp_forall` have one body up to the record array and the node maker; they
share one model `ilwBinW R mk`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## Continuations -/

/-- A call's first result word. -/
def ilwHd : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) => some (r.headD 0, m)

/-- An interning call's result, checked to be a handle word (`if r >= 2^32 { abort }`). -/
def ilwChk : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) => if 4294967296 ≤ r.headD 0 then none else some (r.headD 0, m)

/-- Record the arm's result `r` at `(h, 0)` in `instLPC` (array 52) and return it. -/
def ilwSetK (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m) =>
    match msetG lpSch m h 0 r with
    | none => none
    | some m' => some (r, m')

@[arena_grind =] theorem ilwHd_some (r : List Word) (m : Mem) : ilwHd (some (r, m)) = some (r.headD 0, m) :=
  rfl
@[arena_grind =] theorem ilwChk_some (r : List Word) (m : Mem) :
    ilwChk (some (r, m)) = if 4294967296 ≤ r.headD 0 then none else some (r.headD 0, m) := rfl
@[arena_grind =] theorem ilwSetK_some (h r : Word) (m : Mem) :
    ilwSetK h (some (r, m)) = (match msetG lpSch m h 0 r with | none => none | some m' => some (r, m')) :=
  rfl

/-! ## `sl_memo(u, ko, kc, vo, vc)`: `substLMemoAt` -/

/-- After `lv_sub_int`: check the handle, record it in `instLPLC` (array 53). -/
def ilwSlK (u : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    if 4294967296 ≤ r.headD 0 then none
    else match msetG lplSch m₁ u 0 (r.headD 0) with
      | none => none
      | some m₂ => some (r.headD 0, m₂)

@[arena_grind =] theorem ilwSlK_some (u : Word) (r : List Word) (m₁ : Mem) :
    ilwSlK u (some (r, m₁)) = if 4294967296 ≤ r.headD 0 then none
      else (match msetG lplSch m₁ u 0 (r.headD 0) with | none => none | some m₂ => some (r.headD 0, m₂)) :=
  rfl

/-- **The model of `sl_memo`** at L fuel `n + 1` (its callees at `n`). -/
def ilwSlW (p : Prog) (n : Nat) (m : Mem) (u ko kc vo vc : Word) : Option (Word × Mem) :=
  if mfindG lplSch m u 0 = [] then none
  else if (mfindG lplSch m u 0).headD 0 ≠ 0 then
    some (rdW (m.arr64 LPLMEMO) ((mfindG lplSch m u 0).tail.headD 0 * 4 + 3), m)
  else ilwSlK u (callW p n "lv_sub_int" [u, ko, kc, vo, vc] m)

/-! ## `sls_memo(vs, ko, kc, vo, vc)`: `substLsMemoAt` -/

/-- After `spn_ls`: record the list in `instLPLsC` (array 54). -/
def ilwSlsK₂ (vs : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₂) =>
    match msetG lplsSch m₂ vs 0 (r.headD 0) with
    | none => none
    | some m₃ => some (r.headD 0, m₃)

/-- After `sls_go`: the stack slice interned as a list (`spn_ls`). -/
def ilwSlsK₁ (p : Prog) (n : Nat) (vs b l : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m₁) => ilwSlsK₂ vs (callW p n "spn_ls" [b, l] m₁)

@[arena_grind =] theorem ilwSlsK₂_some (vs : Word) (r : List Word) (m₂ : Mem) :
    ilwSlsK₂ vs (some (r, m₂)) =
      (match msetG lplsSch m₂ vs 0 (r.headD 0) with | none => none | some m₃ => some (r.headD 0, m₃)) :=
  rfl
@[arena_grind =] theorem ilwSlsK₁_some (p : Prog) (n : Nat) (vs b l : Word) (x : List Word) (m₁ : Mem) :
    ilwSlsK₁ p n vs b l (some (x, m₁)) = ilwSlsK₂ vs (callW p n "spn_ls" [b, l] m₁) := rfl

/-- **The model of `sls_memo`** at L fuel `n + 1`: the list's pool slice `ls_node(vs)`, each
element substituted onto the stack above the top (`sls_go`), the slice interned (`spn_ls`). -/
def ilwSlsW (p : Prog) (n : Nat) (m : Mem) (vs ko kc vo vc : Word) : Option (Word × Mem) :=
  if mfindG lplsSch m vs 0 = [] then none
  else if (mfindG lplsSch m vs 0).headD 0 ≠ 0 then
    some (rdW (m.arr64 LPLSMEMO) ((mfindG lplsSch m vs 0).tail.headD 0 * 4 + 3), m)
  else if m.len64 SPN < spTop m then none
  else if m.len64 SPN - spTop m < (lsNodeW m vs).tail.headD 0 then none
  else ilwSlsK₁ p n vs (spTop m) ((lsNodeW m vs).tail.headD 0)
    (callW p n "sls_go" [(lsNodeW m vs).headD 0, (lsNodeW m vs).tail.headD 0, spTop m, ko, kc, vo, vc] m)

/-! ## `lp_go(h, ko, kc, vo, vc, fu)`: `instLPGo` -/

/-- The `sort` arm after `sl_memo`: unchanged, or the new sort interned. -/
def ilwSortK (p : Prog) (n : Nat) (h x : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₁) => if y.headD 0 = x then some (h, m₁) else ilwChk (callW p n "intern_sort" [y.headD 0] m₁)

/-- The `const` arm after `sls_memo`: unchanged, or the new constant interned (its name read on
the memory after the call). -/
def ilwConstK (p : Prog) (n : Nat) (h x : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₁) =>
    if y.headD 0 = x then some (h, m₁)
    else ilwChk (callW p n "intern_const" [rdW (m₁.arr64 CREC) (idxW h * 4 + tierW h * 2), y.headD 0] m₁)

@[arena_grind =] theorem ilwSortK_some (p : Prog) (n : Nat) (h x : Word) (y : List Word) (m₁ : Mem) :
    ilwSortK p n h x (some (y, m₁)) =
      if y.headD 0 = x then some (h, m₁) else ilwChk (callW p n "intern_sort" [y.headD 0] m₁) := rfl
@[arena_grind =] theorem ilwConstK_some (p : Prog) (n : Nat) (h x : Word) (y : List Word) (m₁ : Mem) :
    ilwConstK p n h x (some (y, m₁)) =
      if y.headD 0 = x then some (h, m₁)
      else ilwChk (callW p n "intern_const" [rdW (m₁.arr64 CREC) (idxW h * 4 + tierW h * 2), y.headD 0] m₁) :=
  rfl

/-- **The dispatch of `lp_go`** past the fuel test and the cut-off: the scratch check, then by the
tag: the leaves `bvar`, `lit` (count check, `h`), `sort` and `const` inline, the six compound arms
called at `fu - 1`. -/
def ilwDispW (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) : Option (Word × Mem) :=
  if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if h >>> 28 = 0 then (if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none else some (h, m))
  else if h >>> 28 = 8 then (if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none else some (h, m))
  else if h >>> 28 = 2 then
    (if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none
     else ilwSortK p n h (rdW (m.arr64 SOREC) (idxW h * 2 + tierW h))
       (callW p n "sl_memo" [rdW (m.arr64 SOREC) (idxW h * 2 + tierW h), ko, kc, vo, vc] m))
  else if h >>> 28 = 3 then
    (if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none
     else ilwConstK p n h (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1))
       (callW p n "sls_memo" [rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1), ko, kc, vo, vc] m))
  else if h >>> 28 = 1 then
    (if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none
     else ilwHd (callW p n "lp_fvar" [h, ko, kc, vo, vc, fu - 1] m))
  else if h >>> 28 = 4 then
    (if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
     else ilwHd (callW p n "lp_app" [h, ko, kc, vo, vc, fu - 1] m))
  else if h >>> 28 = 5 then
    (if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
     else ilwHd (callW p n "lp_lam" [h, ko, kc, vo, vc, fu - 1] m))
  else if h >>> 28 = 6 then
    (if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
     else ilwHd (callW p n "lp_forall" [h, ko, kc, vo, vc, fu - 1] m))
  else if h >>> 28 = 7 then
    (if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
     else ilwHd (callW p n "lp_let" [h, ko, kc, vo, vc, fu - 1] m))
  else if h >>> 28 = 9 then
    (if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
     else ilwHd (callW p n "lp_proj" [h, ko, kc, vo, vc, fu - 1] m))
  else none

section disp
variable (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word)

theorem ilwDispW_sc (hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) :
    ilwDispW p n m h ko kc vo vc fu = none := by
  rw [ilwDispW, if_pos hs]

theorem ilwDispW_bvar (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 0) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none else some (h, m) := by
  rw [ilwDispW]; simp only [hs, hg, ↓reduceIte]

theorem ilwDispW_lit (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 8) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none else some (h, m) := by
  rw [ilwDispW]; simp [hs, hg]

theorem ilwDispW_sort (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 2) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none
      else ilwSortK p n h (rdW (m.arr64 SOREC) (idxW h * 2 + tierW h))
        (callW p n "sl_memo" [rdW (m.arr64 SOREC) (idxW h * 2 + tierW h), ko, kc, vo, vc] m) := by
  rw [ilwDispW]; simp [hs, hg]

theorem ilwDispW_const (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 3) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none
      else ilwConstK p n h (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1))
        (callW p n "sls_memo" [rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1), ko, kc, vo, vc] m) := by
  rw [ilwDispW]; simp [hs, hg]

/-- A compound arm: tag `g`, count word `c`, arm `f`. -/
theorem ilwDispW_arm (g c : Word) (f : FnName) (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hg : h >>> 28 = g)
    (hgc : (g = 1 ∧ c = 26 ∧ f = "lp_fvar") ∨ (g = 4 ∧ c = 4 ∧ f = "lp_app") ∨
      (g = 5 ∧ c = 28 ∧ f = "lp_lam") ∨ (g = 6 ∧ c = 30 ∧ f = "lp_forall") ∨
      (g = 7 ∧ c = 20 ∧ f = "lp_let") ∨ (g = 9 ∧ c = 32 ∧ f = "lp_proj")) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (c + tierW h) ≤ idxW h then none
      else ilwHd (callW p n f [h, ko, kc, vo, vc, fu - 1] m) := by
  rcases hgc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ <;> rw [ilwDispW] <;> simp [hs, hg]

theorem ilwDispW_fvar (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 1) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none
      else ilwHd (callW p n "lp_fvar" [h, ko, kc, vo, vc, fu - 1] m) :=
  ilwDispW_arm p n m h ko kc vo vc fu 1 26 "lp_fvar" hs hg ((.inl ⟨rfl, rfl, rfl⟩))

theorem ilwDispW_app (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 4) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
      else ilwHd (callW p n "lp_app" [h, ko, kc, vo, vc, fu - 1] m) :=
  ilwDispW_arm p n m h ko kc vo vc fu 4 4 "lp_app" hs hg (.inr ((.inl ⟨rfl, rfl, rfl⟩)))

theorem ilwDispW_lam (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 5) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
      else ilwHd (callW p n "lp_lam" [h, ko, kc, vo, vc, fu - 1] m) :=
  ilwDispW_arm p n m h ko kc vo vc fu 5 28 "lp_lam" hs hg (.inr (.inr ((.inl ⟨rfl, rfl, rfl⟩))))

theorem ilwDispW_forall (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 6) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
      else ilwHd (callW p n "lp_forall" [h, ko, kc, vo, vc, fu - 1] m) :=
  ilwDispW_arm p n m h ko kc vo vc fu 6 30 "lp_forall" hs hg (.inr (.inr (.inr ((.inl ⟨rfl, rfl, rfl⟩)))))

theorem ilwDispW_let (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 7) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
      else ilwHd (callW p n "lp_let" [h, ko, kc, vo, vc, fu - 1] m) :=
  ilwDispW_arm p n m h ko kc vo vc fu 7 20 "lp_let" hs hg (.inr (.inr (.inr (.inr ((.inl ⟨rfl, rfl, rfl⟩))))))

theorem ilwDispW_proj (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (hg : h >>> 28 = 9) :
    ilwDispW p n m h ko kc vo vc fu =
      if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
      else ilwHd (callW p n "lp_proj" [h, ko, kc, vo, vc, fu - 1] m) :=
  ilwDispW_arm p n m h ko kc vo vc fu 9 32 "lp_proj" hs hg (.inr (.inr (.inr (.inr (.inr (⟨rfl, rfl, rfl⟩))))))

theorem ilwDispW_other (hs : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0)) (h0 : h >>> 28 ≠ 0)
    (h1 : h >>> 28 ≠ 1) (h2 : h >>> 28 ≠ 2) (h3 : h >>> 28 ≠ 3) (h4 : h >>> 28 ≠ 4)
    (h5 : h >>> 28 ≠ 5) (h6 : h >>> 28 ≠ 6) (h7 : h >>> 28 ≠ 7) (h8 : h >>> 28 ≠ 8)
    (h9 : h >>> 28 ≠ 9) : ilwDispW p n m h ko kc vo vc fu = none := by
  rw [ilwDispW]; simp [hs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

end disp

/-- After `der_b`: the cut-off on the level-parameter bit (its third result). -/
def ilwGoK (p : Prog) (n : Nat) (h ko kc vo vc fu : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d, m₁) => if d.tail.tail.headD 0 = 0 then some (h, m₁) else ilwDispW p n m₁ h ko kc vo vc fu

@[arena_grind =] theorem ilwGoK_some (p : Prog) (n : Nat) (h ko kc vo vc fu : Word) (d : List Word)
    (m₁ : Mem) : ilwGoK p n h ko kc vo vc fu (some (d, m₁)) =
      if d.tail.tail.headD 0 = 0 then some (h, m₁) else ilwDispW p n m₁ h ko kc vo vc fu := rfl

/-- **The model of `lp_go`** at L fuel `n + 1`. -/
def ilwGoW (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) : Option (Word × Mem) :=
  if fu = 0 then none else ilwGoK p n h ko kc vo vc fu (callW p n "der_b" [h] m)

/-! ## The arms -/

/-- The memo probe every arm starts with: a hit answers the stored value, a miss runs `miss`. -/
def ilwProbe (m : Mem) (h : Word) (miss : Option (Word × Mem)) : Option (Word × Mem) :=
  if mfindG lpSch m h 0 = [] then none
  else if (mfindG lpSch m h 0).headD 0 ≠ 0 then
    some (rdW (m.arr64 LPMEMO) ((mfindG lpSch m h 0).tail.headD 0 * 4 + 3), m)
  else miss

/-- `lp_fvar` after the child: unchanged, or the new free variable interned; then recorded. -/
def ilwFvK (p : Prog) (n : Nat) (h ix ty : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) =>
    ilwSetK h (if x.headD 0 = ty then some (h, m₁) else ilwChk (callW p n "intern_fvar" [ix, x.headD 0] m₁))

@[arena_grind =] theorem ilwFvK_some (p : Prog) (n : Nat) (h ix ty : Word) (x : List Word) (m₁ : Mem) :
    ilwFvK p n h ix ty (some (x, m₁)) =
      ilwSetK h (if x.headD 0 = ty then some (h, m₁) else ilwChk (callW p n "intern_fvar" [ix, x.headD 0] m₁)) :=
  rfl

/-- **The model of `lp_fvar`** at L fuel `n + 1`. -/
def ilwFVarW (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) : Option (Word × Mem) :=
  ilwProbe m h (ilwFvK p n h (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2))
    (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1))
    (callW p n "lp_go" [rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1), ko, kc, vo, vc, fu] m))

/-- `internRebuilt*` of a two-child arm: `h` itself when both children came back equal, else the
node maker's result, checked. -/
def ilwRb (p : Prog) (n : Nat) (mk : FnName) (m₂ : Mem) (h f a x y : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a then some (h, m₂) else ilwChk (callW p n mk [x, y] m₂)

theorem ilwRb_same (p : Prog) (n : Nat) (mk : FnName) (m₂ : Mem) (h f a x y : Word) (hx : x = f) (hy : y = a) :
    ilwRb p n mk m₂ h f a x y = some (h, m₂) := by simp [ilwRb, hx, hy]
theorem ilwRb_new (p : Prog) (n : Nat) (mk : FnName) (m₂ : Mem) (h f a x y : Word) (hn : ¬ (x = f ∧ y = a)) :
    ilwRb p n mk m₂ h f a x y = ilwChk (callW p n mk [x, y] m₂) := by simp only [ilwRb, hn, ↓reduceIte]

grind_pattern [arena_grind] ilwRb_same => ilwRb p n mk m₂ h f a x y
grind_pattern [arena_grind] ilwRb_new => ilwRb p n mk m₂ h f a x y

/-- `internRebuiltLetE`. -/
def ilwRbLet (p : Prog) (n : Nat) (m₃ : Mem) (h f a b x y z : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a ∧ z = b then some (h, m₃) else ilwChk (callW p n "mk_let" [x, y, z] m₃)

theorem ilwRbLet_same (p : Prog) (n : Nat) (m₃ : Mem) (h f a b x y z : Word) (hx : x = f) (hy : y = a)
    (hz : z = b) : ilwRbLet p n m₃ h f a b x y z = some (h, m₃) := by simp [ilwRbLet, hx, hy, hz]
theorem ilwRbLet_new (p : Prog) (n : Nat) (m₃ : Mem) (h f a b x y z : Word) (hn : ¬ (x = f ∧ y = a ∧ z = b)) :
    ilwRbLet p n m₃ h f a b x y z = ilwChk (callW p n "mk_let" [x, y, z] m₃) := by
  simp only [ilwRbLet, hn, ↓reduceIte]

grind_pattern [arena_grind] ilwRbLet_same => ilwRbLet p n m₃ h f a b x y z
grind_pattern [arena_grind] ilwRbLet_new => ilwRbLet p n m₃ h f a b x y z

/-- A two-child arm after its second child. -/
def ilwBinK₂ (p : Prog) (n : Nat) (mk : FnName) (h f a x : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => ilwSetK h (ilwRb p n mk m₂ h f a x (y.headD 0))

/-- A two-child arm after its first child. -/
def ilwBinK₁ (p : Prog) (n : Nat) (mk : FnName) (h f a ko kc vo vc fu : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ilwBinK₂ p n mk h f a (x.headD 0) (callW p n "lp_go" [a, ko, kc, vo, vc, fu] m₁)

@[arena_grind =] theorem ilwBinK₂_some (p : Prog) (n : Nat) (mk : FnName) (h f a x : Word) (y : List Word)
    (m₂ : Mem) : ilwBinK₂ p n mk h f a x (some (y, m₂)) = ilwSetK h (ilwRb p n mk m₂ h f a x (y.headD 0)) :=
  rfl
@[arena_grind =] theorem ilwBinK₁_some (p : Prog) (n : Nat) (mk : FnName) (h f a ko kc vo vc fu : Word)
    (x : List Word) (m₁ : Mem) : ilwBinK₁ p n mk h f a ko kc vo vc fu (some (x, m₁)) =
      ilwBinK₂ p n mk h f a (x.headD 0) (callW p n "lp_go" [a, ko, kc, vo, vc, fu] m₁) := rfl

/-- **The model of `lp_app`, `lp_lam`, `lp_forall`** at L fuel `n + 1` (record array `R`, node
maker `mk`). -/
def ilwBinW (R : ArrId) (mk : FnName) (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) :
    Option (Word × Mem) :=
  ilwProbe m h (ilwBinK₁ p n mk h (rdW (m.arr64 R) (idxW h * 4 + tierW h * 2))
    (rdW (m.arr64 R) (idxW h * 4 + tierW h * 2 + 1)) ko kc vo vc fu
    (callW p n "lp_go" [rdW (m.arr64 R) (idxW h * 4 + tierW h * 2), ko, kc, vo, vc, fu] m))

/-- `lp_let` after its third child. -/
def ilwLetK₃ (p : Prog) (n : Nat) (h f a b x y : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m₃) => ilwSetK h (ilwRbLet p n m₃ h f a b x y (z.headD 0))

/-- `lp_let` after its second child. -/
def ilwLetK₂ (p : Prog) (n : Nat) (h f a b ko kc vo vc fu x : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => ilwLetK₃ p n h f a b x (y.headD 0) (callW p n "lp_go" [b, ko, kc, vo, vc, fu] m₂)

/-- `lp_let` after its first child. -/
def ilwLetK₁ (p : Prog) (n : Nat) (h f a b ko kc vo vc fu : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ilwLetK₂ p n h f a b ko kc vo vc fu (x.headD 0) (callW p n "lp_go" [a, ko, kc, vo, vc, fu] m₁)

@[arena_grind =] theorem ilwLetK₃_some (p : Prog) (n : Nat) (h f a b x y : Word) (z : List Word) (m₃ : Mem) :
    ilwLetK₃ p n h f a b x y (some (z, m₃)) = ilwSetK h (ilwRbLet p n m₃ h f a b x y (z.headD 0)) := rfl
@[arena_grind =] theorem ilwLetK₂_some (p : Prog) (n : Nat) (h f a b ko kc vo vc fu x : Word) (y : List Word)
    (m₂ : Mem) : ilwLetK₂ p n h f a b ko kc vo vc fu x (some (y, m₂)) =
      ilwLetK₃ p n h f a b x (y.headD 0) (callW p n "lp_go" [b, ko, kc, vo, vc, fu] m₂) := rfl
@[arena_grind =] theorem ilwLetK₁_some (p : Prog) (n : Nat) (h f a b ko kc vo vc fu : Word) (x : List Word)
    (m₁ : Mem) : ilwLetK₁ p n h f a b ko kc vo vc fu (some (x, m₁)) =
      ilwLetK₂ p n h f a b ko kc vo vc fu (x.headD 0) (callW p n "lp_go" [a, ko, kc, vo, vc, fu] m₁) := rfl

/-- **The model of `lp_let`** at L fuel `n + 1`. -/
def ilwLetW (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) : Option (Word × Mem) :=
  ilwProbe m h (ilwLetK₁ p n h (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3))
    (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2))
    ko kc vo vc fu
    (callW p n "lp_go" [rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3), ko, kc, vo, vc, fu] m))

/-- `internRebuiltProj`. -/
def ilwRbProj (p : Prog) (n : Nat) (m₁ : Mem) (h nm ix e x : Word) : Option (Word × Mem) :=
  if x = e then some (h, m₁) else ilwChk (callW p n "mk_proj" [nm, ix, x] m₁)

theorem ilwRbProj_same (p : Prog) (n : Nat) (m₁ : Mem) (h nm ix e x : Word) (hx : x = e) :
    ilwRbProj p n m₁ h nm ix e x = some (h, m₁) := by simp [ilwRbProj, hx]
theorem ilwRbProj_new (p : Prog) (n : Nat) (m₁ : Mem) (h nm ix e x : Word) (hx : ¬ x = e) :
    ilwRbProj p n m₁ h nm ix e x = ilwChk (callW p n "mk_proj" [nm, ix, x] m₁) := by
  simp only [ilwRbProj, hx, ↓reduceIte]

grind_pattern [arena_grind] ilwRbProj_same => ilwRbProj p n m₁ h nm ix e x
grind_pattern [arena_grind] ilwRbProj_new => ilwRbProj p n m₁ h nm ix e x

/-- `lp_proj` after its child. -/
def ilwProjK (p : Prog) (n : Nat) (h nm ix e : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ilwSetK h (ilwRbProj p n m₁ h nm ix e (x.headD 0))

@[arena_grind =] theorem ilwProjK_some (p : Prog) (n : Nat) (h nm ix e : Word) (x : List Word) (m₁ : Mem) :
    ilwProjK p n h nm ix e (some (x, m₁)) = ilwSetK h (ilwRbProj p n m₁ h nm ix e (x.headD 0)) := rfl

/-- **The model of `lp_proj`** at L fuel `n + 1`. -/
def ilwProjW (p : Prog) (n : Nat) (m : Mem) (h ko kc vo vc fu : Word) : Option (Word × Mem) :=
  ilwProbe m h (ilwProjK p n h (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3))
    (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1)) (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2))
    (callW p n "lp_go" [rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2), ko, kc, vo, vc, fu] m))

/-! ## The entries -/

/-- `inst_lp_core` after the walk: the three clears, the handle masked to 32 bits. -/
def ilwE3 (r : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m) => some (r &&& 4294967295, m)
def ilwE2 (p : Prog) (n : Nat) (r : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m) => ilwE3 r (callW p n "ilpls_clear" [] m)
def ilwE1 (p : Prog) (n : Nat) (r : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m) => ilwE2 p n r (callW p n "ilpl_clear" [] m)

/-- After the walk. -/
def ilwCoreK (p : Prog) (n : Nat) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => ilwE1 p n (r.headD 0) (callW p n "ilp_clear" [] m₁)

/-- The three clears before the walk, then the walk at `coreWalkFuel`. -/
def ilwC3 (p : Prog) (n : Nat) (ko kc e vo vc : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m) => ilwCoreK p n (callW p n "lp_go" [e, ko, kc, vo, vc, 4000000000] m)
def ilwC2 (p : Prog) (n : Nat) (ko kc e vo vc : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m) => ilwC3 p n ko kc e vo vc (callW p n "ilpls_clear" [] m)
def ilwC1 (p : Prog) (n : Nat) (ko kc e vo vc : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m) => ilwC2 p n ko kc e vo vc (callW p n "ilpl_clear" [] m)

/-- `inst_lp_core` after `der_b`: the cut-off, else the values' slice (`ls_node(us)`), the clears,
the walk. -/
def ilwCoreD (p : Prog) (n : Nat) (ko kc us e : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d, m₁) =>
    if d.tail.tail.headD 0 = 0 then some (e &&& 4294967295, m₁)
    else ilwC1 p n ko kc e ((lsNodeW m₁ us).headD 0) ((lsNodeW m₁ us).tail.headD 0)
      (callW p n "ilp_clear" [] m₁)

section entryK
variable (p : Prog) (n : Nat) (ko kc us e vo vc r : Word) (x : List Word) (m : Mem)
@[arena_grind =] theorem ilwE3_some : ilwE3 r (some (x, m)) = some (r &&& 4294967295, m) := rfl
@[arena_grind =] theorem ilwE2_some : ilwE2 p n r (some (x, m)) = ilwE3 r (callW p n "ilpls_clear" [] m) := rfl
@[arena_grind =] theorem ilwE1_some : ilwE1 p n r (some (x, m)) = ilwE2 p n r (callW p n "ilpl_clear" [] m) := rfl
@[arena_grind =] theorem ilwCoreK_some :
    ilwCoreK p n (some (x, m)) = ilwE1 p n (x.headD 0) (callW p n "ilp_clear" [] m) := rfl
@[arena_grind =] theorem ilwC3_some :
    ilwC3 p n ko kc e vo vc (some (x, m)) = ilwCoreK p n (callW p n "lp_go" [e, ko, kc, vo, vc, 4000000000] m) :=
  rfl
@[arena_grind =] theorem ilwC2_some :
    ilwC2 p n ko kc e vo vc (some (x, m)) = ilwC3 p n ko kc e vo vc (callW p n "ilpls_clear" [] m) := rfl
@[arena_grind =] theorem ilwC1_some :
    ilwC1 p n ko kc e vo vc (some (x, m)) = ilwC2 p n ko kc e vo vc (callW p n "ilpl_clear" [] m) := rfl
@[arena_grind =] theorem ilwCoreD_some :
    ilwCoreD p n ko kc us e (some (x, m)) =
      if x.tail.tail.headD 0 = 0 then some (e &&& 4294967295, m)
      else ilwC1 p n ko kc e ((lsNodeW m us).headD 0) ((lsNodeW m us).tail.headD 0) (callW p n "ilp_clear" [] m) :=
  rfl
end entryK

/-- **The model of `inst_lp_core`** at L fuel `n + 1`. -/
def ilwCoreW (p : Prog) (n : Nat) (m : Mem) (ko kc us e : Word) : Option (Word × Mem) :=
  ilwCoreD p n ko kc us e (callW p n "der_b" [e] m)

/-- `inst_lp` after `keys_push`: the walk, the stack top put back. -/
def ilwLPK₂ (b : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₂) => some (r.headD 0, m₂.set64 CTL 136 b)

/-- `inst_lp` after `keys_push`. -/
def ilwLPK₁ (p : Prog) (n : Nat) (pl us e : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b, m₁) => ilwLPK₂ (b.headD 0) (callW p n "inst_lp_core" [b.headD 0, pl, us, e] m₁)

@[arena_grind =] theorem ilwLPK₂_some (b : Word) (r : List Word) (m₂ : Mem) :
    ilwLPK₂ b (some (r, m₂)) = some (r.headD 0, m₂.set64 CTL 136 b) := rfl
@[arena_grind =] theorem ilwLPK₁_some (p : Prog) (n : Nat) (pl us e : Word) (b : List Word) (m₁ : Mem) :
    ilwLPK₁ p n pl us e (some (b, m₁)) = ilwLPK₂ (b.headD 0) (callW p n "inst_lp_core" [b.headD 0, pl, us, e] m₁) :=
  rfl

/-- **The model of `inst_lp`** at L fuel `n + 1`. -/
def ilwLPW (p : Prog) (n : Nat) (m : Mem) (po pl us e : Word) : Option (Word × Mem) :=
  ilwLPK₁ p n pl us e (callW p n "keys_push" [po, pl] m)

/-! ## The program -/

/-- The walk's functions and the memos' at their names. -/
structure ILWProg (p : Prog) : Prop where
  sl : p.lookup "sl_memo" = some slMemo
  sls : p.lookup "sls_memo" = some slsMemo
  go : p.lookup "lp_go" = some lpGo
  fv : p.lookup "lp_fvar" = some lpFVar
  app : p.lookup "lp_app" = some lpApp
  lam : p.lookup "lp_lam" = some lpLam
  fa : p.lookup "lp_forall" = some lpForall
  le : p.lookup "lp_let" = some lpLet
  pj : p.lookup "lp_proj" = some lpProj
  core : p.lookup "inst_lp_core" = some instLPCore
  lp : p.lookup "inst_lp" = some instLPL
  ilpf : p.lookup "ilp_find" = some (memoFindG lpSch)
  ilpp : p.lookup "ilp_put" = some (memoPutG lpSch)
  ilpc : p.lookup "ilp_clear" = some (memoClearG lpSch)
  ilplf : p.lookup "ilpl_find" = some (memoFindG lplSch)
  ilplp : p.lookup "ilpl_put" = some (memoPutG lplSch)
  ilplc : p.lookup "ilpl_clear" = some (memoClearG lplSch)
  ilplsf : p.lookup "ilpls_find" = some (memoFindG lplsSch)
  ilplsp : p.lookup "ilpls_put" = some (memoPutG lplsSch)
  ilplsc : p.lookup "ilpls_clear" = some (memoClearG lplsSch)
  lsn : p.lookup "ls_node" = some lsNode

/-! ## The specs -/

section specs
variable (p : Prog) (hp : ILWProg p)
include hp

theorem slMemo_spec (n : Nat) (s₀ : St) (u ko kc vo vc : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "sl_memo" [u, ko, kc, vo, vc]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwSlW p n s₀.mem u ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.sl]
  simp only [callFn, slMemo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lplSch p _ hp.ilplf n, memoPutG_spec lplSch p _ hp.ilplp n,
      callW_spec p n "lv_sub_int"] <;>
    finish [ilwSlW, msetG]

theorem slsMemo_spec (n : Nat) (s₀ : St) (vs ko kc vo vc : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "sls_memo" [vs, ko, kc, vo, vc]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwSlsW p n s₀.mem vs ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.sls]
  simp only [callFn, slsMemo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lplsSch p _ hp.ilplsf n, memoPutG_spec lplsSch p _ hp.ilplsp n,
      lsNode_spec p hp.lsn n, callW_spec p n "sls_go", callW_spec p n "spn_ls"] <;>
    finish [ilwSlsW, msetG, spTop]

theorem lpFVar_spec (n : Nat) (s₀ : St) (h ko kc vo vc fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lp_fvar" [h, ko, kc, vo, vc, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwFVarW p n s₀.mem h ko kc vo vc fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.fv]
  simp only [callFn, lpFVar]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
      callW_spec p n "lp_go", callW_spec p n "intern_fvar"] <;>
    finish [ilwFVarW, ilwProbe, msetG, tierW, idxW]

set_option maxHeartbeats 1000000 in
theorem lpProj_spec (n : Nat) (s₀ : St) (h ko kc vo vc fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lp_proj" [h, ko, kc, vo, vc, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwProjW p n s₀.mem h ko kc vo vc fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.pj]
  simp only [callFn, lpProj]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
      callW_spec p n "lp_go", callW_spec p n "mk_proj"] <;>
    finish (gen := 20) [ilwProjW, ilwProbe, msetG, tierW, idxW]

set_option maxHeartbeats 1000000 in
theorem instLPCore_spec (n : Nat) (s₀ : St) (ko kc us e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst_lp_core" [ko, kc, us, e]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwCoreW p n s₀.mem ko kc us e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.core]
  simp only [callFn, instLPCore]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "ilp_clear", callW_spec p n "ilpl_clear", callW_spec p n "ilpls_clear",
      callW_spec p n "der_b", lsNode_spec p hp.lsn n, callW_spec p n "lp_go"] <;>
    finish (gen := 20) [ilwCoreW]

theorem instLP_spec (n : Nat) (s₀ : St) (po pl us e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "inst_lp" [po, pl, us, e]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwLPW p n s₀.mem po pl us e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.lp]
  simp only [callFn, instLPL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "keys_push", callW_spec p n "inst_lp_core"] <;>
    finish [ilwLPW]

end specs

end L.Arena
