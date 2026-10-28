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

/-! ## The single pass's member step against Stage B's -/

theorem subRecN_e (kd mk : Word) (bit : Word → Word) (val : Word → Word → Word → Word)
    (hbit : subBit kd = bit) (hval : ∀ k ks v, bit k ≠ 0 → subVal b k ks v = val k ks v)
    (v : Word) : (subRecN b v kd mk).e = objEntryN bit val mk b v := by
  unfold subRecN objEntryN
  split
  · rw [subN_objN, hbit, objN_congr bit (subVal b) val mk hval]
  · rfl

/-- The object of a payload key is Stage B's (`lineVal`). -/
theorem subRecN_lineVal (k ks v : Word)
    (hk : k = 56 ∨ k = 38 ∨ k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48) :
    (subRecN b v k (if k = 56 ∨ k = 38 then 3 else exprMask k)).e = L.Scan.Line.lineVal b k ks v := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [L.Scan.Line.lineVal, exprMask, strNameN, numNameN, appN, binderN, letEN, constEN,
      projN]
    simp only [reduceIte, Nat.reduceEqDiff, or_false, false_or, or_true, true_or,
      show ∀ a b : Word, a = b ↔ a = b from fun _ _ => Iff.rfl]
    apply subRecN_e
    · funext k; simp [subBit]
    · intro k ks v hk
      simp only [strNameBit, numNameBit, appBit, binderBit, letEBit, constEBit, projBit] at hk
      split at hk <;> (try split at hk) <;> (try split at hk) <;> (try split at hk) <;>
        (try split at hk) <;>
        simp_all [subVal, strNameVal, numNameVal, appVal, binderVal, letEVal, constEVal, projVal]

open L.Scan.Line (lineStepN lineKind lineVal) in
/-- A payload key whose step has the standard form: Stage B's value end `E` and kind `K`. -/
theorem std_step {k ks v ik pk E K : Word} {g : Fld} (h1 : k ≠ 21) (h2 : k ≠ 19) (h3 : k ≠ 18)
    (hK : lineKind k = K) (hK0 : K ≠ 0) (hE : lineVal b k ks v = E) :
    (if pk = 0 ∧ E ≠ 0 ∧ ks < E then (⟨E, ik, K, g⟩ : LRS) else .fail).e =
      (lineStepN b k ks v ik pk).1 ∧
    ((if pk = 0 ∧ E ≠ 0 ∧ ks < E then (⟨E, ik, K, g⟩ : LRS) else .fail).e ≠ 0 →
      (if pk = 0 ∧ E ≠ 0 ∧ ks < E then (⟨E, ik, K, g⟩ : LRS) else .fail).ik =
        (lineStepN b k ks v ik pk).2.1 ∧
      (if pk = 0 ∧ E ≠ 0 ∧ ks < E then (⟨E, ik, K, g⟩ : LRS) else .fail).pk =
        (lineStepN b k ks v ik pk).2.2) := by
  rw [L.Scan.Line.lineStepN_pay b k ks v ik pk h1 h2 h3, hK, hE]
  by_cases h : pk = 0 ∧ E ≠ 0 ∧ ks < E
  · rw [if_pos h, if_pos ⟨hK0, h.1, h.2.2⟩]; simp
  · rw [if_neg h]
    by_cases h' : K ≠ 0 ∧ pk = 0 ∧ ks < E
    · exfalso; apply h; refine ⟨h'.2.1, fun h0 => ?_, h'.2.2⟩; rw [h0] at h'
      exact UInt64.not_lt_zero h'.2.2
    · rw [if_neg h']; simp [LRS.fail]

/-- A successful `slot_nat` passes the key: the nat arms in the standard form. -/
theorem slot_std (ks v : Word) (P : Prop) [Decidable P] (r : LRS) :
    (if P ∧ slotNatN b ks v ≠ 0 then r else .fail) =
      if P ∧ slotNatN b ks v ≠ 0 ∧ ks < slotNatN b ks v then r else .fail := by
  by_cases h : P ∧ slotNatN b ks v ≠ 0
  · rw [if_pos h, if_pos ⟨h.1, h.2, slotNatN_pos b ks v h.2⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]

open L.Scan.Line (lineStepN lineKind lineVal) in
/-- **One member: the single pass ends and classifies as Stage B does.** -/
theorem lrStepN_line (k ks v ik pk : Word) (f : Fld) :
    (lrStepN b k ks v ik pk f).e = (lineStepN b k ks v ik pk).1 ∧
    ((lrStepN b k ks v ik pk f).e ≠ 0 →
      (lrStepN b k ks v ik pk f).ik = (lineStepN b k ks v ik pk).2.1 ∧
      (lrStepN b k ks v ik pk f).pk = (lineStepN b k ks v ik pk).2.2) := by
  by_cases hi : k = 21 ∨ k = 19 ∨ k = 18
  · rw [L.Scan.Line.lineStepN_idx b k ks v ik pk hi]
    simp only [lrStepN, hi, reduceIte, lrIdx]
    rw [slot_std]
    by_cases h : ik = 0 ∧ slotNatN b ks v ≠ 0 ∧ ks < slotNatN b ks v
    · rw [if_pos h, if_pos ⟨h.1, h.2.2⟩]; simp
    · have hn : ¬ (ik = 0 ∧ ks < slotNatN b ks v) := fun h' => h ⟨h'.1, fun h0 => by
        have := h'.2; rw [h0] at this; exact UInt64.not_lt_zero this, h'.2⟩
      rw [if_neg h, if_neg hn]; simp [LRS.fail]
  have h1 : k ≠ 21 := fun e => hi (.inl e)
  have h2 : k ≠ 19 := fun e => hi (.inr (.inl e))
  have h3 : k ≠ 18 := fun e => hi (.inr (.inr e))
  by_cases hn : k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46
  · simp only [lrStepN, hi, hn, reduceIte, lrNat]
    rw [slot_std]
    exact std_step h1 h2 h3 (by rcases hn with rfl | rfl | rfl | rfl <;> decide)
      (by split <;> decide) (by rcases hn with rfl | rfl | rfl | rfl <;> simp [lineVal])
  by_cases hl : k = 32 ∨ k = 20
  · simp only [lrStepN, hi, hn, hl, reduceIte, lrList]
    have hE : lineVal b k ks v = if (natListEntryN b v).1 = 0 then 0
        else if (natListEntryN b v).2 = 2 then (natListEntryN b v).1 else 0 := by
      rcases hl with rfl | rfl <;> simp only [lineVal] <;> rfl
    have hstd : (if pk = 0 ∧ (natListEntryN b v).1 ≠ 0 ∧ (natListEntryN b v).2 = 2 ∧
          ks < (natListEntryN b v).1 then
        (⟨(natListEntryN b v).1, ik, 2,
          ⟨if k = 32 then 4 else 5, f.idx, (pairEntryN b v).2.1, (pairEntryN b v).2.2, f.d⟩⟩ : LRS)
        else .fail) =
        if pk = 0 ∧ lineVal b k ks v ≠ 0 ∧ ks < lineVal b k ks v then
          (⟨lineVal b k ks v, ik, 2,
            ⟨if k = 32 then 4 else 5, f.idx, (pairEntryN b v).2.1, (pairEntryN b v).2.2, f.d⟩⟩ : LRS)
        else .fail := by
      rw [hE]
      by_cases ha : (natListEntryN b v).1 = 0 <;> by_cases hc : (natListEntryN b v).2 = 2 <;>
        simp [ha, hc]
    rw [hstd]
    exact std_step h1 h2 h3 (by rcases hl with rfl | rfl <;> decide) (by decide) rfl
  by_cases hm : k = 56 ∨ k = 38
  · simp only [lrStepN, hi, hn, hl, hm, reduceIte, lrName]
    have he := subRecN_lineVal (b := b) k ks v (by rcases hm with h | h <;> simp [h])
    rw [if_pos hm] at he
    rw [he]
    exact std_step h1 h2 h3 (by rcases hm with rfl | rfl <;> decide) (by decide) rfl
  by_cases hx : k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48
  · simp only [lrStepN, hi, hn, hl, hm, hx, reduceIte, lrExpr]
    have he := subRecN_lineVal (b := b) k ks v (by
      rcases hx with h | h | h | h | h | h <;> simp [h])
    rw [if_neg hm] at he
    rw [he]
    exact std_step h1 h2 h3 (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by decide) rfl
  by_cases ht : k = 35 ∨ k = 57
  · simp only [lrStepN, hi, hn, hl, hm, hx, ht, reduceIte, lrLit]
    have he : litEnd b k v = lineVal b k ks v := by
      rcases ht with rfl | rfl <;> simp [litEnd, lineVal]
    rw [he]
    exact std_step h1 h2 h3 (by rcases ht with rfl | rfl <;> decide) (by decide) rfl
  by_cases hd : k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23
  · simp only [lrStepN, hi, hn, hl, hm, hx, ht, hd, reduceIte, lrDecl]
    exact std_step h1 h2 h3 (by rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by decide) rfl
  by_cases hme : k = 33
  · subst hme
    simp only [lrStepN, reduceIte, lrMeta, Nat.reduceEqDiff, or_self, or_false, false_or]
    exact std_step h1 h2 h3 (by decide) (by decide) (by simp [lineVal, metaN])
  · simp only [lrStepN, hi, hn, hl, hm, hx, ht, hd, hme, reduceIte]
    rw [L.Scan.Line.lineStepN_pay b k ks v ik pk h1 h2 h3]
    have hK : lineKind k = 0 := by
      simp only [lineKind]
      simp_all
    simp [hK, LRS.fail]

/-! ## The pair list -/

/-- On a list Stage B accepts, the record pass's pair reader ends where the validator does. -/
theorem pairN_natListN : ∀ i cnt w x0 x1, (natListN b i cnt w).1 ≠ 0 →
    (pairN b i cnt x0 x1).1 = (natListN b i cnt w).1 := by
  intro i cnt w x0 x1
  induction i, cnt, w using natListN.induct b generalizing x0 x1 with
  | case1 i cnt w h hc ih =>
    intro hn
    rw [natListN_ws b i cnt w _ rfl h hc] at hn ⊢
    have h93 : byteW b i ≠ 93 := by rcases hc with hc | hc | hc <;> rw [hc] <;> decide
    have hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57) := by
      rcases hc with hc | hc | hc <;> rw [hc] <;> decide
    rw [pairN_other b i cnt x0 x1 h h93 hd]; exact ih x0 x1 hn
  | case2 i cnt w h hc h93 hw =>
    intro hn; rw [natListN] at hn; simp [h, hc, h93, hw] at hn
  | case3 i cnt w h hc h93 hw =>
    intro _
    rw [natListN_close_ok b i cnt w h hc h93 hw, pairN_close b i cnt x0 x1 h h93]
  | case4 i cnt w h hc h93 h44 hw =>
    intro hn; rw [natListN] at hn; simp [h, hc, h93, h44, hw] at hn
  | case5 i cnt w h hc h93 h44 hw ih =>
    intro hn
    rw [natListN_comma b i cnt w _ rfl h hc h93 h44 (by simpa using hw)] at hn ⊢
    rw [pairN_other b i cnt x0 x1 h h93 (by rw [h44]; decide)]; exact ih x0 x1 hn
  | case8 i cnt w h hc h93 h44 hd hw he hlt ih =>
    intro hn
    rw [natListN_digit b i cnt w _ rfl h hc h93 h44 hd hw he hlt] at hn ⊢
    rw [pairN_digit b i cnt x0 x1 h h93 hd hlt]; exact ih _ _ hn
  | case9 i cnt w h hc h93 h44 hd hw he hlt =>
    intro hn
    rw [natListN, dite_eq_left h, if_neg (by simpa using hc), if_neg h93, if_neg h44, if_pos hd,
      if_neg hw, if_neg he, if_neg hlt] at hn
    exact absurd rfl hn
  | case10 i cnt w h hc h93 h44 hd =>
    intro hn
    rw [natListN_other b i cnt w h (by simpa using hc) h93 h44 (by simpa using hd)] at hn
    exact absurd rfl hn
  | _ =>
    intro hn
    first
      | (rw [natListN_end b _ _ _ ‹_›] at hn; exact absurd rfl hn)
      | (rw [natListN_digit_w0 b _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› rfl] at hn; exact absurd rfl hn)
      | (rw [natListN_digit_noprog b _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›] at hn; exact absurd rfl hn)

theorem pairEntryN_natList (v : Word) (h : (natListEntryN b v).1 ≠ 0) :
    (pairEntryN b v).1 = (natListEntryN b v).1 := by
  unfold natListEntryN at h ⊢
  split at h
  · rw [ite_eq_left ‹_›]; exact pairN_natListN _ _ _ _ _ h
  · exact absurd rfl h

/-! ## The line -/

theorem Fld.mk_eta (f : Fld) : (⟨f.pl, f.idx, f.a, f.c, f.d⟩ : Fld) = f := rfl

/-- **The single pass ends where Stage B's validator does**: it accepts exactly its lines. -/
theorem lineRecN_e (i w ik pk : Word) (f : Fld) :
    (lineRecN b i w ik pk f).e = L.Scan.Line.lineN b i w ik pk := by
  induction i, w, ik, pk, f using lineRecN.induct b with
  | case1 i w ik pk f h0 =>
    rw [lineRecN_err b i w ik pk f h0, L.Scan.Line.lineN_err b i w ik pk h0]; rfl
  | case5 i w ik pk f h0 h1 hlt ih =>
    obtain ⟨he, hk⟩ := lrStepN_line (b := b) (nextMemberN b i w).key (nextMemberN b i w).pos
      (nextMemberN b i w).val ik pk f
    have hne : (lrStepN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val
        ik pk f).e ≠ 0 := fun h => by rw [h] at hlt; exact UInt64.not_lt_zero hlt
    obtain ⟨hik, hpk⟩ := hk hne
    rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_right hne, Fld.mk_eta, ih,
      L.Scan.Line.lineN_step b i w ik pk h0 h1, ← he, ite_eq_right hne, hik, hpk]
  | case6 i w ik pk f h0 h1 hlt =>
    obtain ⟨he, -⟩ := lrStepN_line (b := b) (nextMemberN b i w).key (nextMemberN b i w).pos
      (nextMemberN b i w).val ik pk f
    have h0' : (lrStepN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val
        ik pk f).e = 0 := Decidable.byContradiction fun hne =>
      hlt (lrStepN_lt b ik pk f _ _ _ hne)
    rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_left h0', L.Scan.Line.lineN_step b i w ik pk h0 h1,
      ← he, ite_eq_left h0']; rfl
  | _ =>
    rw [lineRecN_close b _ _ _ _ _ ‹_›, L.Scan.Line.lineN_close b _ _ _ _ ‹_›]
    split <;> (try split) <;> simp_all [LRS.fail]

/-! ## The fields -/

theorem subRecN_some {v kd mk : Word} (h : (subRecN b v kd mk).e ≠ 0) :
    v < UInt64.ofNat b.size ∧ byteW b v = 123 ∧
      subRecN b v kd mk = subN b kd mk (v + 1) 1 0 ⟨0, 0, 0, 0, 0⟩ := by
  unfold subRecN at h ⊢
  split at h
  · exact ⟨‹_ ∧ _›.1, ‹_ ∧ _›.2, by rw [ite_eq_left ‹_›]⟩
  · exact absurd rfl h

theorem strRecEntryN_sub {v : Word} (h : (subRecN b v 56 3).e ≠ 0) :
    strRecEntryN b v = ((subRecN b v 56 3).e, (subRecN b v 56 3).x0, (subRecN b v 56 3).x1,
      (subRecN b v 56 3).x2) := by
  obtain ⟨-, -, hs⟩ := subRecN_some h
  rw [hs] at h ⊢
  exact subN_strRecN 3 _ _ _ ⟨0, 0, 0, 0, 0⟩ h

theorem numRecEntryN_sub {v : Word} (h : (subRecN b v 38 3).e ≠ 0) :
    numRecEntryN b v = ((subRecN b v 38 3).e, (subRecN b v 38 3).x0, (subRecN b v 38 3).x1) := by
  obtain ⟨-, -, hs⟩ := subRecN_some h
  rw [hs] at h ⊢
  exact subN_numRecN 3 _ _ _ ⟨0, 0, 0, 0, 0⟩ h

theorem recObjN_sub {v k mk : Word} (hk : ExprKind k) (h : (subRecN b v k mk).e ≠ 0) :
    recObjN b v = subRecN b v k mk := by
  obtain ⟨-, -, hs⟩ := subRecN_some h
  rw [hs] at h ⊢
  exact (subN_objRecN k mk hk _ _ _ _ h).symm

/-- **A member read by the record pass for names and levels**: on a step that scans and leaves a
name, level or header kind, `recN` moves on as the single pass does. -/
theorem recN_lrStep (i w ks w' k v ik pk : Word) (f : Fld)
    (hM : nextMemberN b i w = ⟨2, ks, w', k, v⟩) (he : (lrStepN b k ks v ik pk f).e ≠ 0)
    (hk : (lrStepN b k ks v ik pk f).pk = 0 ∨ (lrStepN b k ks v ik pk f).pk = 1 ∨
      (lrStepN b k ks v ik pk f).pk = 2 ∨ (lrStepN b k ks v ik pk f).pk = 5) :
    recN b i w f = recN b (lrStepN b k ks v ik pk f).e 0 (lrStepN b k ks v ik pk f).f := by
  rw [recN_key b i w f (by rw [hM]; simp) (by rw [hM]; simp), hM]
  simp only
  by_cases hkey : k = 21 ∨ k = 19 ∨ k = 18 ∨ k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46 ∨ k = 32 ∨ k = 20 ∨
      k = 56 ∨ k = 38 ∨ k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 ∨ k = 35 ∨ k = 57 ∨
      k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23 ∨ k = 33
  · rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) only [lrStepN, lrIdx, lrNat, lrList, lrName, lrExpr,
        lrLit, lrDecl, lrMeta, reduceIte] at he hk ⊢
      split at he
      · rename_i h
        simp only [h, ne_eq, not_false_eq_true, and_self, ite_true] at hk ⊢
        all_goals first
          | (simp only [natF, nameF, reduceIte] at hk ⊢; done)
          | (simp only [natF, nameF, reduceIte] at hk ⊢; simp_all; done)
          | (simp_all [slotNatN_pos, pairEntryN_natList, strRecEntryN_sub, numRecEntryN_sub,
              natF, nameF])
      · exact absurd rfl he
  · exfalso
    simp only [lrStepN] at he
    repeat' (rw [ite_eq_right (by simp_all)] at he)
    exact he rfl

/-- **A member read by the record pass for expressions**: on a step that scans and leaves no
payload kind or an expression's, `exprN` moves on as the single pass does. -/
theorem exprN_lrStep (i w ks w' k v ik pk : Word) (f : Fld)
    (hM : nextMemberN b i w = ⟨2, ks, w', k, v⟩) (he : (lrStepN b k ks v ik pk f).e ≠ 0)
    (hk : (lrStepN b k ks v ik pk f).pk = 0 ∨ (lrStepN b k ks v ik pk f).pk = 3) :
    exprN b i w f = exprN b (lrStepN b k ks v ik pk f).e 0 (lrStepN b k ks v ik pk f).f := by
  rw [exprN_key b i w f (by rw [hM]; simp) (by rw [hM]; simp), hM]
  simp only
  by_cases hkey : k = 21 ∨ k = 19 ∨ k = 18 ∨ k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46 ∨ k = 32 ∨ k = 20 ∨
      k = 56 ∨ k = 38 ∨ k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 ∨ k = 35 ∨ k = 57 ∨
      k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23 ∨ k = 33
  · rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) only [lrStepN, lrIdx, lrNat, lrList, lrName, lrExpr,
        lrLit, lrDecl, lrMeta, exVN, reduceIte] at he hk ⊢
      split at he
      · rename_i h
        simp only [h, ne_eq, not_false_eq_true, and_self, ite_true] at hk ⊢
        all_goals first
          | (simp only [natF, exprF, fldPut, litEnd, reduceIte] at hk ⊢; done)
          | (simp only [natF, exprF, fldPut, litEnd, reduceIte] at hk ⊢; simp_all; done)
          | (rw [recObjN_sub (by simp [ExprKind]) h.2.1]
             simp [objFld, fldPut, exprF, slotNatN_pos, h.2.2])
          | (simp_all [slotNatN_pos, fldPut, natF, litEnd])
      · exact absurd rfl he
  · exfalso
    simp only [lrStepN] at he
    repeat' (rw [ite_eq_right (by simp_all)] at he)
    exact he rfl

/-- Once a payload key is read, only index keys follow: the payload kind stays. -/
theorem lrStepN_pk (k ks v ik pk : Word) (f : Fld) (he : (lrStepN b k ks v ik pk f).e ≠ 0)
    (hp : pk ≠ 0) : (lrStepN b k ks v ik pk f).pk = pk := by
  by_cases hkey : k = 21 ∨ k = 19 ∨ k = 18 ∨ k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46 ∨ k = 32 ∨ k = 20 ∨
      k = 56 ∨ k = 38 ∨ k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 ∨ k = 35 ∨ k = 57 ∨
      k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23 ∨ k = 33
  · rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) only [lrStepN, lrIdx, lrNat, lrList, lrName, lrExpr,
        lrLit, lrDecl, lrMeta, reduceIte] at he ⊢
      split at he
      · rename_i h; simp_all
      · exact absurd rfl he
  · exfalso
    simp only [lrStepN] at he
    repeat' (rw [ite_eq_right (by simp_all)] at he)
    exact he rfl

/-- The payload kinds and the field `pl`: none or a declaration `0`, a name, level or the header
`1`–`7`, an expression `8` or more. -/
structure PlOK (pk pl : Word) : Prop where
  none : pk = 0 ∨ pk = 4 → pl = 0
  nm : pk = 1 ∨ pk = 2 ∨ pk = 5 → 1 ≤ pl ∧ pl ≤ 7
  expr : pk = 3 → 8 ≤ pl

theorem plOK_step (k ks v ik pk : Word) (f : Fld) (he : (lrStepN b k ks v ik pk f).e ≠ 0)
    (hp : PlOK pk f.pl) : PlOK (lrStepN b k ks v ik pk f).pk (lrStepN b k ks v ik pk f).f.pl := by
  obtain ⟨h1, h2, h3⟩ := hp
  by_cases hkey : k = 21 ∨ k = 19 ∨ k = 18 ∨ k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46 ∨ k = 32 ∨ k = 20 ∨
      k = 56 ∨ k = 38 ∨ k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 ∨ k = 35 ∨ k = 57 ∨
      k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23 ∨ k = 33
  · rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) only [lrStepN, lrIdx, lrNat, lrList, lrName, lrExpr,
        lrLit, lrDecl, lrMeta, reduceIte] at he ⊢
      split at he
      · rename_i h
        refine ⟨?_, ?_, ?_⟩ <;> intro hq <;>
          simp_all (config := { decide := true }) [natF, nameF, exprF, objFld]
        all_goals (try split) <;> decide
      · exact absurd rfl he
  · exfalso
    simp only [lrStepN] at he
    repeat' (rw [ite_eq_right (by simp_all)] at he)
    exact he rfl

/-- On an expression or a declaration key with no payload before, the record pass for names and
levels stops with `Fld.none`. -/
theorem recN_none_step (i w ks w' k v ik pk : Word) (f : Fld)
    (hM : nextMemberN b i w = ⟨2, ks, w', k, v⟩) (he : (lrStepN b k ks v ik pk f).e ≠ 0)
    (hk : (lrStepN b k ks v ik pk f).pk = 3 ∨ (lrStepN b k ks v ik pk f).pk = 4) (hp : pk = 0) :
    recN b i w f = .none := by
  subst hp
  rw [recN_key b i w f (by rw [hM]; simp) (by rw [hM]; simp), hM]
  simp only
  by_cases hkey : k = 21 ∨ k = 19 ∨ k = 18 ∨ k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46 ∨ k = 32 ∨ k = 20 ∨
      k = 56 ∨ k = 38 ∨ k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 ∨ k = 35 ∨ k = 57 ∨
      k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23 ∨ k = 33
  · rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) only [lrStepN, lrIdx, lrNat, lrList, lrName, lrExpr,
        lrLit, lrDecl, lrMeta, reduceIte] at he hk ⊢
      all_goals first
        | done
        | (split at he <;> first | (exact absurd rfl he) | simp_all)
  · exfalso
    simp only [lrStepN] at he
    repeat' (rw [ite_eq_right (by simp_all)] at he)
    exact he rfl

/-- On a declaration key, the record pass for expressions stops with `Fld.none`. -/
theorem exprN_none_step (i w ks w' k v ik pk : Word) (f : Fld)
    (hM : nextMemberN b i w = ⟨2, ks, w', k, v⟩) (he : (lrStepN b k ks v ik pk f).e ≠ 0)
    (hk : (lrStepN b k ks v ik pk f).pk = 4) (hp : pk = 0) :
    exprN b i w f = .none := by
  subst hp
  rw [exprN_key b i w f (by rw [hM]; simp) (by rw [hM]; simp), hM]
  simp only
  by_cases hkey : k = 21 ∨ k = 19 ∨ k = 18 ∨ k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46 ∨ k = 32 ∨ k = 20 ∨
      k = 56 ∨ k = 38 ∨ k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 ∨ k = 35 ∨ k = 57 ∨
      k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23 ∨ k = 33
  · rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) only [lrStepN, lrIdx, lrNat, lrList, lrName, lrExpr,
        lrLit, lrDecl, lrMeta, exVN, reduceIte] at he hk ⊢
      all_goals first
        | done
        | (split at he <;> first | (exact absurd rfl he) | simp_all [Obj.none])
  · exfalso
    simp only [lrStepN] at he
    repeat' (rw [ite_eq_right (by simp_all)] at he)
    exact he rfl

/-! ## The fields of a line -/

theorem mbr_eta (i w : Word) (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    nextMemberN b i w = ⟨2, (nextMemberN b i w).pos, (nextMemberN b i w).w,
      (nextMemberN b i w).key, (nextMemberN b i w).val⟩ := by
  have := nextMemberN_tag b i w h0 h1
  cases h : nextMemberN b i w; simp_all

/-- The step's state, written once. -/
abbrev lrSt (b : Array UInt8) (i w ik pk : Word) (f : Fld) : LRS :=
  lrStepN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val ik pk f

/-- The step case of an induction over `lineRecN`: the line goes on with the step's state. -/
theorem lineRecN_next (i w ik pk : Word) (f : Fld) (h0 : (nextMemberN b i w).tag ≠ 0)
    (h1 : (nextMemberN b i w).tag ≠ 1) (hne : (lrSt b i w ik pk f).e ≠ 0) :
    lineRecN b i w ik pk f =
      lineRecN b (lrSt b i w ik pk f).e 0 (lrSt b i w ik pk f).ik (lrSt b i w ik pk f).pk
        (lrSt b i w ik pk f).f := by
  rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_right hne, Fld.mk_eta]

/-- **What a line that scans ends with**: a payload kind of Stage B's, and `pl` as `PlOK` says. -/
theorem lineRecN_kind (i w ik pk : Word) (f : Fld) (hp : PlOK pk f.pl)
    (he : (lineRecN b i w ik pk f).e ≠ 0) :
    PlOK (lineRecN b i w ik pk f).pk (lineRecN b i w ik pk f).f.pl ∧
    ((lineRecN b i w ik pk f).pk = 1 ∨ (lineRecN b i w ik pk f).pk = 2 ∨
      (lineRecN b i w ik pk f).pk = 3 ∨ (lineRecN b i w ik pk f).pk = 4 ∨
      (lineRecN b i w ik pk f).pk = 5) ∧
    (pk ≠ 0 → (lineRecN b i w ik pk f).pk = pk) := by
  induction i, w, ik, pk, f using lineRecN.induct b with
  | case5 i w ik pk f h0 h1 hlt ih =>
    have hne : (lrSt b i w ik pk f).e ≠ 0 := fun h => by
      simp only [lrSt] at h; rw [h] at hlt; exact UInt64.not_lt_zero hlt
    rw [lineRecN_next i w ik pk f h0 h1 hne] at he ⊢
    obtain ⟨a, c, d⟩ := ih (plOK_step _ _ _ _ _ _ hne hp) he
    exact ⟨a, c, fun hp0 => by rw [d (by rw [lrStepN_pk _ _ _ _ _ _ hne hp0]; exact hp0),
      lrStepN_pk _ _ _ _ _ _ hne hp0]⟩
  | case6 i w ik pk f h0 h1 hlt =>
    rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_left (Decidable.byContradiction fun hne =>
      hlt (lrStepN_lt b ik pk f _ _ _ hne))] at he
    exact absurd rfl he
  | case1 i w ik pk f h0 => rw [lineRecN_err b i w ik pk f h0] at he; exact absurd rfl he
  | case2 i w ik pk f h0 h1 hw =>
    rw [lineRecN_close b i w ik pk f h1, ite_eq_left hw] at he; exact absurd rfl he
  | case3 i w ik pk f h0 h1 hw hk =>
    rw [lineRecN_close b i w ik pk f h1, ite_eq_right hw, ite_eq_left hk]
    refine ⟨hp, ?_, fun _ => rfl⟩
    rcases hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  | case4 i w ik pk f h0 h1 hw hk =>
    rw [lineRecN_close b i w ik pk f h1, ite_eq_right hw, ite_eq_right hk] at he
    exact absurd rfl he

/-- Once a line has a payload kind, it keeps it. -/
theorem lineRecN_pk (i w ik pk : Word) (f : Fld) (he : (lineRecN b i w ik pk f).e ≠ 0)
    (hp : pk ≠ 0) : (lineRecN b i w ik pk f).pk = pk := by
  induction i, w, ik, pk, f using lineRecN.induct b with
  | case5 i w ik pk f h0 h1 hlt ih =>
    have hne : (lrSt b i w ik pk f).e ≠ 0 := fun h => by
      simp only [lrSt] at h; rw [h] at hlt; exact UInt64.not_lt_zero hlt
    rw [lineRecN_next i w ik pk f h0 h1 hne] at he ⊢
    have hs := lrStepN_pk _ _ _ _ _ _ hne hp
    rw [ih he (by rw [hs]; exact hp), hs]
  | case6 i w ik pk f h0 h1 hlt =>
    rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_left (Decidable.byContradiction fun hne =>
      hlt (lrStepN_lt b ik pk f _ _ _ hne))] at he
    exact absurd rfl he
  | case1 i w ik pk f h0 => rw [lineRecN_err b i w ik pk f h0] at he; exact absurd rfl he
  | case2 i w ik pk f h0 h1 hw =>
    rw [lineRecN_close b i w ik pk f h1, ite_eq_left hw] at he; exact absurd rfl he
  | case3 i w ik pk f h0 h1 hw hk =>
    rw [lineRecN_close b i w ik pk f h1, ite_eq_right hw, ite_eq_left hk]
  | case4 i w ik pk f h0 h1 hw hk =>
    rw [lineRecN_close b i w ik pk f h1, ite_eq_right hw, ite_eq_right hk] at he
    exact absurd rfl he

/-- The shared cases of the field theorems: no step that fails, no close that fails. -/
theorem lineRecN_close_ok {i w ik pk : Word} {f : Fld} (h1 : (nextMemberN b i w).tag = 1)
    (he : (lineRecN b i w ik pk f).e ≠ 0) : lineRecN b i w ik pk f =
      ⟨(nextMemberN b i w).pos + 1, ik, pk, f⟩ := by
  rw [lineRecN_close b i w ik pk f h1] at he ⊢
  split at he
  · exact absurd rfl he
  · rename_i hw
    split at he
    · rename_i h; rw [ite_eq_left h, ite_eq_right hw]
    · exact absurd rfl he

/-- **On a name, level or header line, the record pass for them reads the single pass's fields.** -/
theorem lineRecN_recN (i w ik pk : Word) (f : Fld) (he : (lineRecN b i w ik pk f).e ≠ 0)
    (hk : (lineRecN b i w ik pk f).pk = 1 ∨ (lineRecN b i w ik pk f).pk = 2 ∨
      (lineRecN b i w ik pk f).pk = 5) (hp : pk = 0 ∨ pk = 1 ∨ pk = 2 ∨ pk = 5) :
    recN b i w f = (lineRecN b i w ik pk f).f := by
  induction i, w, ik, pk, f using lineRecN.induct b with
  | case5 i w ik pk f h0 h1 hlt ih =>
    have hne : (lrSt b i w ik pk f).e ≠ 0 := fun h => by
      simp only [lrSt] at h; rw [h] at hlt; exact UInt64.not_lt_zero hlt
    rw [lineRecN_next i w ik pk f h0 h1 hne] at he hk ⊢
    by_cases hs : (lrSt b i w ik pk f).pk = 0 ∨ (lrSt b i w ik pk f).pk = 1 ∨
        (lrSt b i w ik pk f).pk = 2 ∨ (lrSt b i w ik pk f).pk = 5
    · rw [recN_lrStep i w _ _ _ _ ik pk f (mbr_eta i w h0 h1) hne hs]
      exact ih he hk hs
    · exfalso
      have h0' : (lrSt b i w ik pk f).pk ≠ 0 := fun h => hs (.inl h)
      rw [lineRecN_pk _ _ _ _ _ he h0'] at hk
      exact hs (.inr hk)
  | case6 i w ik pk f h0 h1 hlt =>
    rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_left (Decidable.byContradiction fun hne =>
      hlt (lrStepN_lt b ik pk f _ _ _ hne))] at he
    exact absurd rfl he
  | case1 i w ik pk f h0 => rw [lineRecN_err b i w ik pk f h0] at he; exact absurd rfl he
  | _ => rw [lineRecN_close_ok ‹_› he, recN_close b _ _ _ ‹_›]

/-- **On an expression line, the record pass for expressions reads the single pass's fields.** -/
theorem lineRecN_exprN (i w ik pk : Word) (f : Fld) (he : (lineRecN b i w ik pk f).e ≠ 0)
    (hk : (lineRecN b i w ik pk f).pk = 3) (hp : pk = 0 ∨ pk = 3) :
    exprN b i w f = (lineRecN b i w ik pk f).f := by
  induction i, w, ik, pk, f using lineRecN.induct b with
  | case5 i w ik pk f h0 h1 hlt ih =>
    have hne : (lrSt b i w ik pk f).e ≠ 0 := fun h => by
      simp only [lrSt] at h; rw [h] at hlt; exact UInt64.not_lt_zero hlt
    rw [lineRecN_next i w ik pk f h0 h1 hne] at he hk ⊢
    by_cases hs : (lrSt b i w ik pk f).pk = 0 ∨ (lrSt b i w ik pk f).pk = 3
    · rw [exprN_lrStep i w _ _ _ _ ik pk f (mbr_eta i w h0 h1) hne hs]
      exact ih he hk hs
    · exfalso
      have h0' : (lrSt b i w ik pk f).pk ≠ 0 := fun h => hs (.inl h)
      rw [lineRecN_pk _ _ _ _ _ he h0'] at hk
      exact hs (.inr hk)
  | case6 i w ik pk f h0 h1 hlt =>
    rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_left (Decidable.byContradiction fun hne =>
      hlt (lrStepN_lt b ik pk f _ _ _ hne))] at he
    exact absurd rfl he
  | case1 i w ik pk f h0 => rw [lineRecN_err b i w ik pk f h0] at he; exact absurd rfl he
  | _ => rw [lineRecN_close_ok ‹_› he, exprN_close b _ _ _ ‹_›]

/-- **On an expression or a declaration line, the record pass for names and levels reads
nothing** (`pl = 0`). -/
theorem lineRecN_recN_none (i w ik pk : Word) (f : Fld) (he : (lineRecN b i w ik pk f).e ≠ 0)
    (hk : (lineRecN b i w ik pk f).pk = 3 ∨ (lineRecN b i w ik pk f).pk = 4) (hp : pk = 0) :
    (recN b i w f).pl = 0 := by
  induction i, w, ik, pk, f using lineRecN.induct b with
  | case5 i w ik pk f h0 h1 hlt ih =>
    have hne : (lrSt b i w ik pk f).e ≠ 0 := fun h => by
      simp only [lrSt] at h; rw [h] at hlt; exact UInt64.not_lt_zero hlt
    rw [lineRecN_next i w ik pk f h0 h1 hne] at he hk
    by_cases hs : (lrSt b i w ik pk f).pk = 0
    · rw [recN_lrStep i w _ _ _ _ ik pk f (mbr_eta i w h0 h1) hne (.inl hs)]
      exact ih he hk hs
    · rw [lineRecN_pk _ _ _ _ _ he hs] at hk
      rw [recN_none_step i w _ _ _ _ ik pk f (mbr_eta i w h0 h1) hne hk hp]; rfl
  | case6 i w ik pk f h0 h1 hlt =>
    rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_left (Decidable.byContradiction fun hne =>
      hlt (lrStepN_lt b ik pk f _ _ _ hne))] at he
    exact absurd rfl he
  | case1 i w ik pk f h0 => rw [lineRecN_err b i w ik pk f h0] at he; exact absurd rfl he
  | _ => rw [lineRecN_close_ok ‹_› he] at hk; simp_all

/-- **On a declaration line, the record pass for expressions reads nothing** (`pl = 0`). -/
theorem lineRecN_exprN_none (i w ik pk : Word) (f : Fld) (he : (lineRecN b i w ik pk f).e ≠ 0)
    (hk : (lineRecN b i w ik pk f).pk = 4) (hp : pk = 0) :
    (exprN b i w f).pl = 0 := by
  induction i, w, ik, pk, f using lineRecN.induct b with
  | case5 i w ik pk f h0 h1 hlt ih =>
    have hne : (lrSt b i w ik pk f).e ≠ 0 := fun h => by
      simp only [lrSt] at h; rw [h] at hlt; exact UInt64.not_lt_zero hlt
    rw [lineRecN_next i w ik pk f h0 h1 hne] at he hk
    by_cases hs : (lrSt b i w ik pk f).pk = 0
    · rw [exprN_lrStep i w _ _ _ _ ik pk f (mbr_eta i w h0 h1) hne (.inl hs)]
      exact ih he hk hs
    · rw [lineRecN_pk _ _ _ _ _ he hs] at hk
      rw [exprN_none_step i w _ _ _ _ ik pk f (mbr_eta i w h0 h1) hne hk hp]; rfl
  | case6 i w ik pk f h0 h1 hlt =>
    rw [lineRecN_step b i w ik pk f h0 h1, ite_eq_left (Decidable.byContradiction fun hne =>
      hlt (lrStepN_lt b ik pk f _ _ _ hne))] at he
    exact absurd rfl he
  | case1 i w ik pk f h0 => rw [lineRecN_err b i w ik pk f h0] at he; exact absurd rfl he
  | _ => rw [lineRecN_close_ok ‹_› he] at hk; simp_all

end L.Front.LineRec
