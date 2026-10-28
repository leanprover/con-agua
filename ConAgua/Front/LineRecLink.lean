module

public import ConAgua.Front.LineRec
import ConAgua.Scan.Common

@[expose] public section

/-!
# The single pass against Stage B and the record passes

The single pass's sub-object model `subN` (`ConAgua.Front.LineRec`) walks the members as Stage
B's `objN` and the record pass's `objRecN` do (all three through `nextMemberN`). Its end is
`objN`'s with the object's key bits and the values `subVal` (`subN_objN`), which are Stage B's
per-record value scanners on every key the record has (`objN_congr`); on an object that scans,
its slots are the record pass's (`subN_objRecN`, `subN_strRecN`, `subN_numRecN`).
-/

namespace L.Front.LineRec

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Records
open L.Front.Fields

variable {b : Array UInt8}

/-! ## Stage B's object loop -/

/-- `objN` reads a key's value only for keys of the record. -/
theorem objN_congr (bit : Word → Word) (val val' : Word → Word → Word → Word) (mask : Word)
    (h : ∀ k ks v, bit k ≠ 0 → val k ks v = val' k ks v) :
    ∀ i w seen, objN bit val mask b i w seen = objN bit val' mask b i w seen := by
  intro i w seen
  induction i, w, seen using objN.induct bit val mask b with
  | case7 i w seen h0 h1 hb' hd hp ih =>
    have he := h _ (nextMemberN b i w).pos (nextMemberN b i w).val hb'
    rw [objN_step _ _ _ b i w seen _ _ h0 h1 hb' (by simpa using hd) rfl hp rfl, ih,
      objN_step _ _ _ b i w seen _ _ h0 h1 hb' (by simpa using hd) he.symm (he ▸ hp) rfl]
  | case8 i w seen h0 h1 hb' hd hp =>
    have he := h _ (nextMemberN b i w).pos (nextMemberN b i w).val hb'
    rw [objN_noprog _ _ _ b i w seen h0 h1 hb' (by simpa using hd) hp,
      objN_noprog _ _ _ b i w seen h0 h1 hb' (by simpa using hd) (by rw [← he]; exact hp)]
  | _ => simp_all [objN_err, objN_close, objN_unknown, objN_dup]

/-! ## The single pass's object loop against Stage B's -/

/-- **The single pass's object loop ends where Stage B's does**, with its key bits and values. -/
theorem subN_objN (kd mk : Word) : ∀ i w seen o,
    (subN b kd mk i w seen o).e = objN (subBit kd) (subVal b) mk b i w seen := by
  intro i w seen o
  induction i, w, seen, o using subN.induct b kd mk with
  | case7 i w seen o h0 h1 hb' hd hp ih =>
    rw [subN_key b kd mk i w seen o h0 h1, ite_eq_right hb', ite_eq_right (by simpa using hd),
      ite_eq_left hp, ih,
      objN_step _ _ _ b i w seen _ _ h0 h1 hb' (by simpa using hd) rfl hp rfl]
  | case8 i w seen o h0 h1 hb' hd hp =>
    rw [subN_key b kd mk i w seen o h0 h1, ite_eq_right hb', ite_eq_right (by simpa using hd),
      ite_eq_right hp, objN_noprog _ _ _ b i w seen h0 h1 hb' (by simpa using hd) hp]
    rfl
  | _ =>
    first
      | (simp_all [subN_err, subN_key, objN_err, objN_unknown, objN_dup, Obj.none]; done)
      | (rw [subN_close b kd mk _ _ _ _ ‹_›, objN_close _ _ _ b _ _ _ ‹_›]
         split <;> (try split) <;> rfl)

/-! ## The single pass's object loop against the record pass's -/

/-- The payload keys of an expression's sub-object. -/
def ExprKind (kd : Word) : Prop := kd = 2 ∨ kd = 29 ∨ kd = 14 ∨ kd = 30 ∨ kd = 9 ∨ kd = 48

/-- On a key of an expression's sub-object, the single pass reads and stores the value as the
record pass does. -/
theorem sub_expr_key {kd k : Word} (hkd : ExprKind kd) (hk : subBit kd k ≠ 0) (ks v : Word) :
    subVal b k ks v = exValN b k ks v ∧
      ∀ e o, subPut b k v e o = objPut k v (rdNatN b v e) o := by
  rcases hkd with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [subBit, appBit, binderBit, letEBit, constEBit, projBit] at hk
    simp at hk
    split at hk <;> (try split at hk) <;> (try split at hk) <;> (try split at hk) <;>
      (try split at hk) <;> (try split at hk) <;> simp_all [subVal, exValN, numKey, subPut, objPut]

/-- **On an expression's sub-object that scans, the single pass's slots are the record pass's.** -/
theorem subN_objRecN (kd mk : Word) (hkd : ExprKind kd) : ∀ i w seen o,
    (subN b kd mk i w seen o).e ≠ 0 → subN b kd mk i w seen o = objRecN b i w o := by
  intro i w seen o
  induction i, w, seen, o using subN.induct b kd mk with
  | case7 i w seen o h0 h1 hb' hd hp ih =>
    intro he
    obtain ⟨hv, hput⟩ := sub_expr_key (b := b) hkd hb' (nextMemberN b i w).pos (nextMemberN b i w).val
    rw [subN_key b kd mk i w seen o h0 h1, ite_eq_right hb', ite_eq_right (by simpa using hd),
      ite_eq_left hp] at he ⊢
    rw [ih he, objRecN_key b i w o h0 h1, ← hv, ite_eq_left hp, hput]
  | case6 i w seen o h0 h1 hb' hd =>
    intro he; rw [subN_key b kd mk i w seen o h0 h1, ite_eq_right hb', ite_eq_left (by simpa using hd)] at he
    exact absurd rfl he
  | case8 i w seen o h0 h1 hb' hd hp =>
    intro he
    rw [subN_key b kd mk i w seen o h0 h1, ite_eq_right hb', ite_eq_right (by simpa using hd),
      ite_eq_right hp] at he
    exact absurd rfl he
  | _ =>
    intro he
    first
      | (simp_all [subN_err, subN_key, Obj.none]; done)
      | (rw [subN_close b kd mk _ _ _ _ ‹_›] at he ⊢
         rw [objRecN_close b _ _ _ ‹_›]
         split at he <;> (try split at he) <;> (try split) <;> (try split) <;> simp_all [Obj.none])

/-! ## Names -/

/-- **On a `str` name that scans, the single pass reads the record pass's fields**: `pre`, the
body's start and its closing quote. -/
theorem subN_strRecN (mk : Word) : ∀ i w seen o,
    (subN b 56 mk i w seen o).e ≠ 0 →
    strRecN b i w o.x0 o.x1 o.x2 = ((subN b 56 mk i w seen o).e, (subN b 56 mk i w seen o).x0,
      (subN b 56 mk i w seen o).x1, (subN b 56 mk i w seen o).x2) := by
  intro i w seen o
  induction i, w, seen, o using subN.induct b 56 mk with
  | case7 i w seen o h0 h1 hb' hd hp ih =>
    intro he
    rw [subN_key b 56 mk i w seen o h0 h1, ite_eq_right hb', ite_eq_right (by simpa using hd),
      ite_eq_left hp] at he ⊢
    rw [← ih he, strRecN_key b i w _ _ _ h0 h1]
    have hk : (nextMemberN b i w).key = 47 ∨ (nextMemberN b i w).key = 56 := by
      simp only [subBit, strNameBit] at hb'; simp at hb'; split at hb' <;> (try split at hb') <;>
        simp_all
    rcases hk with hk | hk
    · rw [hk] at hp ⊢; rw [ite_eq_left rfl, ite_eq_left (by simpa [subVal] using hp)]
      simp [subPut, subVal]
    · rw [hk] at hp ⊢; rw [ite_eq_right (by decide), ite_eq_left (by simpa [subVal] using hp)]
      simp [subPut, subVal]
  | case6 i w seen o h0 h1 hb' hd =>
    intro he; rw [subN_key b 56 mk i w seen o h0 h1, ite_eq_right hb', ite_eq_left (by simpa using hd)] at he
    exact absurd rfl he
  | case8 i w seen o h0 h1 hb' hd hp =>
    intro he
    rw [subN_key b 56 mk i w seen o h0 h1, ite_eq_right hb', ite_eq_right (by simpa using hd),
      ite_eq_right hp] at he
    exact absurd rfl he
  | _ =>
    intro he
    first
      | (simp_all [subN_err, subN_key, Obj.none]; done)
      | (rw [subN_close b 56 mk _ _ _ _ ‹_›] at he ⊢
         rw [strRecN_close b _ _ _ _ _ ‹_›]
         split at he <;> (try split at he) <;> (try split) <;> (try split) <;> simp_all [Obj.none])

/-- **On a `num` name that scans, the single pass reads the record pass's fields**: `pre` and
`i`. -/
theorem subN_numRecN (mk : Word) : ∀ i w seen o,
    (subN b 38 mk i w seen o).e ≠ 0 →
    numRecN b i w o.x0 o.x1 = ((subN b 38 mk i w seen o).e, (subN b 38 mk i w seen o).x0,
      (subN b 38 mk i w seen o).x1) := by
  intro i w seen o
  induction i, w, seen, o using subN.induct b 38 mk with
  | case7 i w seen o h0 h1 hb' hd hp ih =>
    intro he
    rw [subN_key b 38 mk i w seen o h0 h1, ite_eq_right hb', ite_eq_right (by simpa using hd),
      ite_eq_left hp] at he ⊢
    rw [← ih he, numRecN_key b i w _ _ h0 h1]
    have hk : (nextMemberN b i w).key = 16 ∨ (nextMemberN b i w).key = 47 := by
      simp only [subBit, numNameBit] at hb'; simp at hb'; split at hb' <;> (try split at hb') <;>
        simp_all
    rcases hk with hk | hk
    · rw [hk] at hp ⊢; rw [ite_eq_left (by simpa [subVal] using hp), ite_eq_right (by decide)]
      simp [subPut, subVal]
    · rw [hk] at hp ⊢; rw [ite_eq_left (by simpa [subVal] using hp), ite_eq_left rfl]
      simp [subPut, subVal]
  | case6 i w seen o h0 h1 hb' hd =>
    intro he; rw [subN_key b 38 mk i w seen o h0 h1, ite_eq_right hb', ite_eq_left (by simpa using hd)] at he
    exact absurd rfl he
  | case8 i w seen o h0 h1 hb' hd hp =>
    intro he
    rw [subN_key b 38 mk i w seen o h0 h1, ite_eq_right hb', ite_eq_right (by simpa using hd),
      ite_eq_right hp] at he
    exact absurd rfl he
  | _ =>
    intro he
    first
      | (simp_all [subN_err, subN_key, Obj.none]; done)
      | (rw [subN_close b 38 mk _ _ _ _ ‹_›] at he ⊢
         rw [numRecN_close b _ _ _ _ ‹_›]
         split at he <;> (try split at he) <;> (try split) <;> (try split) <;> simp_all [Obj.none])

end L.Front.LineRec
