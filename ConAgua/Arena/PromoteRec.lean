import ConAgua.Arena.PromoteL
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The record side of the promotion: models and specs

`erec_alloc`, the three `EREC` list promotions (`promote_n_list`, `promote_l_list`,
`promote_e_list`), `promote_slice`, `promote_cv`, `promote_clear`, `promote_vg`. As
`PromoteN.lean`: models whose callees are `callW` runs, one `vcgen` per spec.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `erec_alloc` -/

/-- The record pool's top, `CTL[129]`. -/
abbrev etop (m : Mem) : Word := rdW (m.arr64 CTL) 129

/-- **The model of `erec_alloc(k)`**: the old top, the top raised by `k`. -/
def erAllocW (m : Mem) (k : Word) : Option (Word × Mem) :=
  if (m.arr64 CTL).size ≤ 129 ∨ m.len64 EREC < etop m ∨ m.len64 EREC - etop m < k then none
  else some (etop m, m.set64 CTL 129 (etop m + k))

theorem erecAlloc_spec (p : Prog) (hp : p.lookup "erec_alloc" = some L.Ind.erecAlloc) (n : Nat)
    (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "erec_alloc" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ erAllocW s₀.mem k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, L.Ind.erecAlloc]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
    finish [erAllocW]

/-! ## The lists -/

/-- After one element: write it at `q`, promote the rest with `g`. -/
def listK (p : Prog) (n : Nat) (g : FnName) (f o l q : Word) :
    Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m₁) =>
    if (m₁.arr64 EREC).size ≤ q.toNat then none
    else memK (callW p n g [f, o + 1, l - 1, q + 1] (m₁.set64 EREC q (r.headD 0)))

/-- **The model of an `EREC` list promotion** `g(f, o, l, q)` with element promotion `e`. -/
def listW (p : Prog) (n : Nat) (g e : FnName) (m : Mem) (f o l q : Word) : Option Mem :=
  if l = 0 then some m
  else if (m.arr64 EREC).size ≤ o.toNat then none
  else listK p n g f o l q (callW p n e [f, rdW (m.arr64 EREC) o] m)

section eqs
variable (p : Prog) (n : Nat) (m m₁ : Mem) (g e : FnName) (f o l q : Word) (r : List Word)

theorem listK_some (hq : ¬ (m₁.arr64 EREC).size ≤ q.toNat) :
    listK p n g f o l q (some (r, m₁)) =
      memK (callW p n g [f, o + 1, l - 1, q + 1] (m₁.set64 EREC q (r.headD 0))) := by
  simp only [listK, hq, ↓reduceIte]

theorem listW_nil (hl : l = 0) : listW p n g e m f o l q = some m := by simp [listW, hl]
theorem listW_cons (hl : l ≠ 0) (ho : ¬ (m.arr64 EREC).size ≤ o.toNat) :
    listW p n g e m f o l q = listK p n g f o l q (callW p n e [f, rdW (m.arr64 EREC) o] m) := by
  simp only [listW, hl, ho, ↓reduceIte]

end eqs

section specs
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

theorem promoteNList_spec (f o l q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_n_list" [f, o, l, q]
    ⦃fun _ s' => LocEq s' s₀ ∧
      listW p n "promote_n_list" "promote_n" s₀.mem f o l q = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_n_list")]
  simp only [callFn, promoteNListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "promote_n", callW_spec p n "promote_n_list"] <;>
    finish [listW_nil, listW_cons, listK_some, memK_some]

theorem promoteLList_spec (f o l q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_l_list" [f, o, l, q]
    ⦃fun _ s' => LocEq s' s₀ ∧
      listW p n "promote_l_list" "promote_l" s₀.mem f o l q = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_l_list")]
  simp only [callFn, promoteLListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "promote_l", callW_spec p n "promote_l_list"] <;>
    finish [listW_nil, listW_cons, listK_some, memK_some]

theorem promoteEList_spec (f o l q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_e_list" [f, o, l, q]
    ⦃fun _ s' => LocEq s' s₀ ∧
      listW p n "promote_e_list" "promote_e" s₀.mem f o l q = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_e_list")]
  simp only [callFn, promoteEListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "promote_e", callW_spec p n "promote_e_list"] <;>
    finish [listW_nil, listW_cons, listK_some, memK_some]

end specs

/-! ## `promote_slice`, `promote_cv` -/

/-- After the slice's elements: answer its offset `q`. -/
def offK (q : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m) => some (q, m)

/-- After the allocation: promote the elements with the kind's list function. -/
def sliceK (p : Prog) (n : Nat) (k f o l : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q, m₁) =>
    if k = 0 then offK (q.headD 0) (callW p n "promote_n_list" [f, o, l, q.headD 0] m₁)
    else if k = 1 then offK (q.headD 0) (callW p n "promote_l_list" [f, o, l, q.headD 0] m₁)
    else offK (q.headD 0) (callW p n "promote_e_list" [f, o, l, q.headD 0] m₁)

/-- **The model of `promote_slice(k, f, o, l)`.** -/
def sliceW (p : Prog) (n : Nat) (m : Mem) (k f o l : Word) : Option (Word × Mem) :=
  sliceK p n k f o l (callW p n "erec_alloc" [l] m)

/-- The four stores of a constant value at `d` (`cv_wr`'s model). -/
def cvStore (m : Mem) (d nm q l t : Word) : Option Mem :=
  if (m.arr64 EREC).size ≤ d.toNat ∨ (m.arr64 EREC).size ≤ (d + 1).toNat ∨
    (m.arr64 EREC).size ≤ (d + 2).toNat ∨ (m.arr64 EREC).size ≤ (d + 3).toNat then none
  else some ((((m.set64 EREC d nm).set64 EREC (d + 1) q).set64 EREC (d + 2) l).set64 EREC (d + 3) t)

/-- `cv_rd`'s model: the four words, or `[]` out of bounds. -/
def cvRdW (m : Mem) (s : Word) : List Word :=
  if (m.arr64 EREC).size ≤ s.toNat ∨ (m.arr64 EREC).size ≤ (s + 1).toNat ∨
    (m.arr64 EREC).size ≤ (s + 2).toNat ∨ (m.arr64 EREC).size ≤ (s + 3).toNat then []
  else [rdW (m.arr64 EREC) s, rdW (m.arr64 EREC) (s + 1), rdW (m.arr64 EREC) (s + 2),
    rdW (m.arr64 EREC) (s + 3)]

/-- `promote_cv`'s continuations: the four result words. -/
def cvK (p : Prog) (n : Nat) (f o l t : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (nm, m₁) => cvK₂ p n f l t (nm.headD 0) (callW p n "promote_slice" [0, f, o, l] m₁)
where
  cvK₂ (p : Prog) (n : Nat) (f l t nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (q, m₂) => cvK₃ l nm (q.headD 0) (callW p n "promote_e" [f, t] m₂)
  cvK₃ (l nm q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
    | none => none
    | some (t, m₃) => some ([nm, q, l, t.headD 0], m₃)

/-- **The model of `promote_cv(f, s)`**: the four words `(name, lps.off, lps.len, type)`. -/
def cvW (p : Prog) (n : Nat) (m : Mem) (f s : Word) : Option (List Word × Mem) :=
  if cvRdW m s = [] then none
  else cvK p n f ((cvRdW m s).tail.headD 0) ((cvRdW m s).tail.tail.headD 0)
    ((cvRdW m s).tail.tail.tail.headD 0) (callW p n "promote_n" [f, (cvRdW m s).headD 0] m)

section eqs2
variable (p : Prog) (n : Nat) (m m₁ : Mem) (k f o l t d nm q s : Word) (r : List Word)

theorem offK_some : offK q (some (r, m₁)) = some (q, m₁) := rfl
theorem sliceK_some : sliceK p n k f o l (some (r, m₁)) =
    if k = 0 then offK (r.headD 0) (callW p n "promote_n_list" [f, o, l, r.headD 0] m₁)
    else if k = 1 then offK (r.headD 0) (callW p n "promote_l_list" [f, o, l, r.headD 0] m₁)
    else offK (r.headD 0) (callW p n "promote_e_list" [f, o, l, r.headD 0] m₁) := rfl
theorem cvK_some : cvK p n f o l t (some (r, m₁)) =
    cvK.cvK₂ p n f l t (r.headD 0) (callW p n "promote_slice" [0, f, o, l] m₁) := rfl
theorem cvK₂_some : cvK.cvK₂ p n f l t nm (some (r, m₁)) =
    cvK.cvK₃ l nm (r.headD 0) (callW p n "promote_e" [f, t] m₁) := rfl
theorem cvK₃_some : cvK.cvK₃ l nm q (some (r, m₁)) = some ([nm, q, l, r.headD 0], m₁) := rfl
theorem cvW_eq (h : cvRdW m s ≠ []) :
    cvW p n m f s = cvK p n f ((cvRdW m s).tail.headD 0) ((cvRdW m s).tail.tail.headD 0)
      ((cvRdW m s).tail.tail.tail.headD 0) (callW p n "promote_n" [f, (cvRdW m s).headD 0] m) := by
  simp only [cvW, h, ↓reduceIte]

end eqs2

section specs2
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

theorem promoteSlice_spec (k f o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_slice" [k, f, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ sliceW p n s₀.mem k f o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_slice")]
  simp only [callFn, promoteSlice]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "erec_alloc", callW_spec p n "promote_n_list", callW_spec p n "promote_l_list",
      callW_spec p n "promote_e_list"] <;>
    finish [sliceW, sliceK_some, offK_some]

theorem cvRd_spec (s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_rd" [s]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = cvRdW s₀.mem s; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "cv_rd")]
  simp only [callFn, cvRd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [cvRdW]

theorem cvWr_spec (d nm q l t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cv_wr" [d, nm, q, l, t]
    ⦃fun _ s' => LocEq s' s₀ ∧ cvStore s₀.mem d nm q l t = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "cv_wr")]
  simp only [callFn, cvWr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [cvStore]

theorem promoteCV_spec (f s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_cv" [f, s]
    ⦃fun r s' => LocEq s' s₀ ∧ cvW p n s₀.mem f s = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_cv")]
  simp only [callFn, promoteCVL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, cvRd_spec p hp n,
      callW_spec p n "promote_n", callW_spec p n "promote_slice", callW_spec p n "promote_e"] <;>
    -- `l` is read after three calls: `LocEq` hops (depth, not search)
    finish (gen := 20) [cvW_eq, cvK_some, cvK₂_some, cvK₃_some]

end specs2

/-! ## `promote_clear`, `promote_vg` -/

/-- One memo cleared, if its stamp does not wrap. -/
def pmClrK (S : MemoSch) : Option Mem → Option Mem
  | none => none
  | some m => if rdW (m.arr64 CTL) S.cs + 2 = 0 then none else some (mclearG S m)

/-- **The model of `promote_clear()`**: the four memos cleared. -/
def clearW (m : Mem) : Option Mem := pmClrK peSch (pmClrK plsSch (pmClrK plSch (pmClrK pnSch (some m))))

/-- `vg_rd`'s model. -/
def vgRdW (m : Mem) (g : Word) : List Word :=
  if (m.arr64 EREC).size ≤ g.toNat ∨ (m.arr64 EREC).size ≤ (g + 5).toNat then []
  else [rdW (m.arr64 EREC) g, rdW (m.arr64 EREC) (g + 5)]

/-- `vg_wr`'s model: six words at `d`. -/
def vgStore (m : Mem) (d k nm q l t x : Word) : Option Mem :=
  if (m.arr64 EREC).size ≤ d.toNat ∨ (m.arr64 EREC).size ≤ (d + 1).toNat ∨
    (m.arr64 EREC).size ≤ (d + 2).toNat ∨ (m.arr64 EREC).size ≤ (d + 3).toNat ∨
    (m.arr64 EREC).size ≤ (d + 4).toNat ∨ (m.arr64 EREC).size ≤ (d + 5).toNat then none
  else some ((((((m.set64 EREC d k).set64 EREC (d + 1) nm).set64 EREC (d + 2) q).set64 EREC
    (d + 3) l).set64 EREC (d + 4) t).set64 EREC (d + 5) x)

/-- `promote_vg`'s continuations. -/
def vgK (p : Prog) (n : Nat) (k j : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c, m₁) => vgK₂ p n k c (callW p n "promote_e" [L.Ind.CWF, j] m₁)
where
  vgK₂ (p : Prog) (n : Nat) (k : Word) (c : List Word) :
      Option (List Word × Mem) → Option (Word × Mem)
    | none => none
    | some (x, m₂) => vgK₃ p n k c (x.headD 0) (callW p n "erec_alloc" [6] m₂)
  vgK₃ (p : Prog) (n : Nat) (k : Word) (c : List Word) (x : Word) :
      Option (List Word × Mem) → Option (Word × Mem)
    | none => none
    | some (d, m₃) => offK (d.headD 0) (callW p n "vg_wr" [d.headD 0, k, c.headD 0, c.tail.headD 0,
        c.tail.tail.headD 0, c.tail.tail.tail.headD 0, x] m₃)

/-- After the clears: read the record, promote its parts. -/
def vgK₀ (p : Prog) (n : Nat) (g : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, m₁) =>
    if vgRdW m₁ g = [] then none
    else vgK p n ((vgRdW m₁ g).headD 0) ((vgRdW m₁ g).tail.headD 0)
      (callW p n "promote_cv" [L.Ind.CWF, g + 1] m₁)

/-- **The model of `promote_vg(g, vis)`.** -/
def vgW (p : Prog) (n : Nat) (m : Mem) (g : Word) : Option (Word × Mem) :=
  vgK₀ p n g (callW p n "promote_clear" [] m)

section eqs3
variable (p : Prog) (n : Nat) (m m₁ : Mem) (g k j d x : Word) (r : List Word) (S : MemoSch)

theorem pmClrK_some (h : rdW (m.arr64 CTL) S.cs + 2 ≠ 0) : pmClrK S (some m) = some (mclearG S m) := by
  simp [pmClrK, h]
theorem vgK_some : vgK p n k j (some (r, m₁)) =
    vgK.vgK₂ p n k r (callW p n "promote_e" [L.Ind.CWF, j] m₁) := rfl
theorem vgK₂_some (c : List Word) : vgK.vgK₂ p n k c (some (r, m₁)) =
    vgK.vgK₃ p n k c (r.headD 0) (callW p n "erec_alloc" [6] m₁) := rfl
theorem vgK₃_some (c : List Word) : vgK.vgK₃ p n k c x (some (r, m₁)) =
    offK (r.headD 0) (callW p n "vg_wr" [r.headD 0, k, c.headD 0, c.tail.headD 0,
      c.tail.tail.headD 0, c.tail.tail.tail.headD 0, x] m₁) := rfl
theorem vgK₀_some (h : vgRdW m₁ g ≠ []) : vgK₀ p n g (some (r, m₁)) =
    vgK p n ((vgRdW m₁ g).headD 0) ((vgRdW m₁ g).tail.headD 0)
      (callW p n "promote_cv" [L.Ind.CWF, g + 1] m₁) := by
  simp only [vgK₀, h, ↓reduceIte]

end eqs3

section specs3
variable (p : Prog) (hp : PromoteProg p) (n : Nat) (s₀ : St)
include hp

theorem promoteClear_spec :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_clear" []
    ⦃fun _ s' => LocEq s' s₀ ∧ clearW s₀.mem = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_clear")]
  simp only [callFn, promoteClear]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      memoClearG_spec pnSch p _ (hp.get "pn_clear") n, memoClearG_spec plSch p _ (hp.get "pl_clear") n,
      memoClearG_spec plsSch p _ (hp.get "pls_clear") n, memoClearG_spec peSch p _ (hp.get "pe_clear") n] <;>
    finish [clearW, pmClrK_some]

theorem vgRd_spec (g : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vg_rd" [g]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = vgRdW s₀.mem g; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "vg_rd")]
  simp only [callFn, vgRd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [vgRdW]

theorem vgWr_spec (d k nm q l t x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "vg_wr" [d, k, nm, q, l, t, x]
    ⦃fun _ s' => LocEq s' s₀ ∧ vgStore s₀.mem d k nm q l t x = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "vg_wr")]
  simp only [callFn, vgWr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish [vgStore]

theorem promoteVG_specW (g vis : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "promote_vg" [g, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ vgW p n s₀.mem g = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "promote_vg")]
  simp only [callFn, promoteVGL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, vgRd_spec p hp n,
      callW_spec p n "promote_clear", callW_spec p n "promote_cv", callW_spec p n "promote_e",
      callW_spec p n "erec_alloc", callW_spec p n "vg_wr"] <;>
    -- `k` and the four words are read after several calls: `LocEq` hops (depth, not search)
    finish (gen := 20) [vgW, vgK₀_some, vgK_some, vgK₂_some, vgK₃_some, offK_some, L.Ind.CWF]

end specs3

end L.Arena
