import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.IndStubs
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# CtxFields

`posRecW`, `posRecW_eq`, `posRec2_eq`, `posRec4_eq`, `posRec5_eq`, `posRec6_eq` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The record writers as one model -/

/-- The model of `recK(ws…)`: allocate `|ws|` words, write `ws` at the old top. -/
def posRecW (m : Mem) (ws : List Word) : Option (Word × Mem) :=
  match allocW m (UInt64.ofNat ws.length) with
  | none => none
  | some (q, m1) => some (q, wrIW m1 q ws)

theorem posRecW_eq (m : Mem) (ws : List Word) (k : Word) (hk : k = UInt64.ofNat ws.length) :
    posRecW m ws = (match allocW m k with
      | none => none
      | some (q, _) => some (q, wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws)) := by
  subst hk
  simp only [posRecW]
  rcases h : allocW m (UInt64.ofNat ws.length) with _ | ⟨q, m1⟩; · rfl
  simp only [allocW] at h
  split at h
  · simp at h
  split at h
  · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  rfl

theorem posRec2_eq (m : Mem) (a b : Word) :
    (match allocW m 2 with | none => none | some (q, _) => some (q, rec2Mem m a b)) =
      posRecW m [a, b] := by
  rw [posRecW_eq m [a, b] 2 rfl, rec2Mem_eq]
theorem posRec4_eq (m : Mem) (a b c d : Word) :
    (match allocW m 4 with | none => none | some (q, _) => some (q, rec4Mem m a b c d)) =
      posRecW m [a, b, c, d] := by
  rw [posRecW_eq m [a, b, c, d] 4 rfl, rec4Mem_eq]
theorem posRec5_eq (m : Mem) (a b c d e : Word) :
    (match allocW m 5 with | none => none | some (q, _) => some (q, rec5Mem m a b c d e)) =
      posRecW m [a, b, c, d, e] := by
  rw [posRecW_eq m [a, b, c, d, e] 5 rfl, rec5Mem_eq]
theorem posRec6_eq (m : Mem) (a b c d e f : Word) :
    (match allocW m 6 with | none => none | some (q, _) => some (q, rec6Mem m a b c d e f)) =
      posRecW m [a, b, c, d, e, f] := by
  rw [posRecW_eq m [a, b, c, d, e, f] 6 rfl, rec6Mem_eq]

section recspecs
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
include ha

theorem posRec2_specW (h2 : p.lookup "rec2" = some rec2) (n : Nat) (s₀ : St) (a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec2" [a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b] = some (r.headD 0, s'.mem); ⊤⦄ := by
  simp only [← posRec2_eq, invoke_eq _ h2, callFn, rec2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec2Mem, allocMem, allocW]

theorem posRec4_specW (h4 : p.lookup "rec4" = some rec4) (n : Nat) (s₀ : St) (a b c d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec4" [a, b, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c, d] = some (r.headD 0, s'.mem); ⊤⦄ := by
  simp only [← posRec4_eq, invoke_eq _ h4, callFn, rec4]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec4Mem, allocMem, allocW]

theorem posRec5_specW (h5 : p.lookup "rec5" = some rec5) (n : Nat) (s₀ : St) (a b c d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec5" [a, b, c, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c, d, e] = some (r.headD 0, s'.mem); ⊤⦄ := by
  simp only [← posRec5_eq, invoke_eq _ h5, callFn, rec5]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec5Mem, allocMem, allocW]

theorem rec6_specW (h6 : p.lookup "rec6" = some rec6) (n : Nat) (s₀ : St) (a b c d e f : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec6" [a, b, c, d, e, f]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c, d, e, f] = some (r.headD 0, s'.mem); ⊤⦄ := by
  simp only [← posRec6_eq, invoke_eq _ h6, callFn, rec6]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec6Mem, allocMem, allocW]

end recspecs

/-- The indices `decNK m k` reads lie in `P`. -/
def NKIn (m : Mem) (k : Nat) (P : Nat → Prop) : Prop :=
  (∀ j < 4, P (k + j)) ∧ ∀ o l, iwN m (k + 2) = some o → iwN m (k + 3) = some l → ∀ j < l, P (o + j)

/-- The indices `decNH m w` reads lie in `P`. -/
def NHIn (m : Mem) (w : Nat) (P : Nat → Prop) : Prop :=
  P w ∧ P (w + 1) ∧ ∀ k, iwN m w = some k → NKIn m k P

/-! ## Word reads of decoded fields -/

/-- A decoded number at `p + i` is the word L reads there. -/
theorem rd_iwN {m : Mem} {p i : Word} {v : Nat} (h : iwN m (p.toNat + i.toNat) = some v)
    (hb : p.toNat + i.toNat < 2 ^ 64) : (rdW (m.arr64 IW) (p + i)).toNat = v := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have : (p + i).toNat = p.toNat + i.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hb
  simp [rdW, this, hw]

/-- A decoded handle at `p + i` is the word L reads there. -/
theorem rd_iwH {k : IdxKind} {m : Mem} {p i : Word} {x : Idx k} (h : iwH m (p.toNat + i.toNat) = some x)
    (hb : p.toNat + i.toNat < 2 ^ 64) :
    H (rdW (m.arr64 IW) (p + i)) ∧ decI (rdW (m.arr64 IW) (p + i)) = x := by
  obtain ⟨w, hw, hl, hx⟩ := hd?_some h
  have : (p + i).toNat = p.toNat + i.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hb
  simp only [iwA] at hw
  simp only [rdW, this, hw, Option.getD_some]
  exact ⟨hl, hx.symm⟩

theorem word_add_toNat {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-! ## `nest_ctx_root_holes(_go)` refines `NestCtx.rootHoles` -/

mutual
def rhGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, lv, po, pl, nP, q, j =>
    if nl ≤ j then some m
    else rhK1 k no nl lv po pl nP q j (posRecW m [rdW (m.arr64 IW) (no + j), lv, po, pl])
def rhK1 (k : Nat) (no nl lv po pl nP q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (key, m1) => rhK2 k no nl lv po pl nP q j (posRecW m1 [key, nP])
def rhK2 (k : Nat) (no nl lv po pl nP q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (h, m2) => rhGoW k (m2.set64 IW (q + j) h) no nl lv po pl nP q (j + 1)
end

def rhB (q nl : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m2 => some ([q, nl], m2)
/-- The pointers at `q, …, q + j - 1` decode to the first `j` holes, every read in `P`. -/
def HolesAt (m : Mem) (q j : Nat) (hs : List NestHole) (P : Nat → Prop) : Prop :=
  ∀ i < j, ∃ w : Word, (m.arr64 IW)[q + i]? = some w ∧ decNH m w.toNat = hs[i]? ∧ NHIn m w.toNat P

theorem decNK_of_words {m : Mem} {k : Nat} {c u o l : Word} {ds : List EIdx}
    (h0 : (m.arr64 IW)[k]? = some c) (hc : H c) (h1 : (m.arr64 IW)[k + 1]? = some u) (hu : H u)
    (h2 : (m.arr64 IW)[k + 2]? = some o) (h3 : (m.arr64 IW)[k + 3]? = some l)
    (hs : decHL m o.toNat l.toNat = some ds) : decNK m k = some ⟨decI c, decI u, ds⟩ := by
  simp only [decNK, decAt, iwH, iwN, nat?, hd?, iwA, h0, h1, h2, h3, hc, hu, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, ite_true]
  simp [hs]

/-! ### `NestCtx` records: where their reads lie -/

/-- The indices `decCtx m p` reads lie in `P`. -/
def CtxIn (m : Mem) (p : Nat) (P : Nat → Prop) : Prop :=
  (∀ j < 11, P (p + j)) ∧ ∀ i, (i = 0 ∨ i = 2 ∨ i = 5 ∨ i = 7) → ∀ o l, iwN m (p + i) = some o →
    iwN m (p + i + 1) = some l → ∀ j < l, P (o + j)

/-- A `NestCtx` record decoded below the top: its fields as the words L reads. -/
theorem ctx_fields {m : Mem} {p : Word} {c : NestCtx} (hc : decCtx m p.toNat = some c)
    (hin : CtxIn m p.toNat (· < iwTop m)) (hsz : iwTop m < 2 ^ 64) :
    decHL m (rdW (m.arr64 IW) p).toNat (rdW (m.arr64 IW) (p + 1)).toNat = some c.names ∧
    (∀ j < (rdW (m.arr64 IW) (p + 1)).toNat, (rdW (m.arr64 IW) p).toNat + j < iwTop m) ∧
    decHL m (rdW (m.arr64 IW) (p + 7)).toNat (rdW (m.arr64 IW) (p + 8)).toNat = some c.params ∧
    (∀ j < (rdW (m.arr64 IW) (p + 8)).toNat, (rdW (m.arr64 IW) (p + 7)).toNat + j < iwTop m) ∧
    (rdW (m.arr64 IW) (p + 4)).toNat = c.nP ∧
    H (rdW (m.arr64 IW) (p + 10)) ∧ decI (rdW (m.arr64 IW) (p + 10)) = c.lvls ∧
    H (rdW (m.arr64 IW) (p + 9)) ∧ decI (rdW (m.arr64 IW) (p + 9)) = c.sort ∧
    p.toNat + 11 ≤ iwTop m := by
  obtain ⟨hn, -, hnP, -, hpa, hso, hlv⟩ := decCtx_some hc
  have h10 := hin.1 10 (by omega)
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hn
  obtain ⟨o7, l7, ho7, hl7, hd7⟩ := decAt_some hpa
  have r0 : (rdW (m.arr64 IW) p).toNat = o := by
    have := rd_iwN (m := m) (p := p) (i := 0) (by simpa using ho) (by simp; omega); simpa using this
  have r1 : (rdW (m.arr64 IW) (p + 1)).toNat = l := rd_iwN (by simpa using hl) (by simp; omega)
  have r7 : (rdW (m.arr64 IW) (p + 7)).toNat = o7 := rd_iwN (by simpa using ho7) (by simp; omega)
  have r8 : (rdW (m.arr64 IW) (p + 8)).toNat = l7 := rd_iwN (by simpa using hl7) (by simp; omega)
  have r4 : (rdW (m.arr64 IW) (p + 4)).toNat = c.nP := rd_iwN (by simpa using hnP) (by simp; omega)
  obtain ⟨h10a, h10b⟩ := rd_iwH (p := p) (i := 10) (by simpa using hlv) (by simp; omega)
  obtain ⟨h9a, h9b⟩ := rd_iwH (p := p) (i := 9) (by simpa using hso) (by simp; omega)
  have hl0 := decHL_length m hd
  have hl7' := decHL_length m hd7
  have s0 : ∀ j < l, o + j < iwTop m := hin.2 0 (by omega) o l (by simpa using ho) (by simpa using hl)
  have s7 : ∀ j < l7, o7 + j < iwTop m := hin.2 7 (by omega) o7 l7 ho7 hl7
  exact ⟨by rw [r0, r1]; exact hd, by rw [r0, r1]; exact s0, by rw [r7, r8]; exact hd7,
    by rw [r7, r8]; exact s7, r4, h10a, h10b, h9a, h9b, by omega⟩

/-! ## `nest_hole_at` refines `nestHoleAt` -/

/-- A slice of `NestHole` pointers below the top, decoding to `hs`. -/
def HSl (m : Mem) (o l : Nat) (hs : List NestHole) : Prop :=
  hs.length = l ∧ o + l ≤ iwTop m ∧ HolesAt m o l hs (· < iwTop m)

/-- An optional hole: `(0, _)` or `(1, w)` with `w` decoding below the top. -/
def decONH (m : Mem) (r : List Word) : Option NestHole → Prop
  | none => r.headD 0 = 0
  | some h => r.headD 0 = 1 ∧ decNH m (r.tail.headD 0).toNat = some h ∧
      NHIn m (r.tail.headD 0).toNat (· < iwTop m)

def haK2 (idx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if idx < r2.tail.headD 0 then some ([1, rdW (m2.arr64 IW) (r2.headD 0 + idx)], m2)
    else some ([0, 0], m2)
end L.Ind

end
