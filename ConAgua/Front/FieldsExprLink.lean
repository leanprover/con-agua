module

public import ConAgua.Front.ExprIface
public import ConAgua.Front.FieldsExpr
import ConAgua.Scan.LeafLink
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section


/-!
# The fields of expression lines, linked to con-leche

On a line con-leche's scanner accepts with an expression record, `rec_expr_loop`'s words are the
record's fields in the sense of `ExprR` (`exprLine_link`). As for name and level lines
(`ConAgua.Front.FieldsLink`), every link is on con-leche's `ok` path only.

The six sub-object loops of con-leche (`scanAppExprLoop`, …) are each related to the one generic
loop `objRecN` by one generic theorem, `objRec_link`, from `VLoop`: the shape of a con-leche
sub-object loop on its `ok` path (each byte arm, and at a key `VK`: the value's end is
`exValN`'s, and the loop's state after the member is related to the slots after `objPut`). The
state relation `R` and the result relation `Res` are the instance's; `vloop` proves the byte
arms of an instance, the key arms are per key (`vk_num`, `vk_usz`, `vk_res`).
-/

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Front.Fields

theorem objRecN_congr (b : Array UInt8) (i w j w' : Word) (o : Obj)
    (h : nextMemberN b i w = nextMemberN b j w') : objRecN b i w o = objRecN b j w' o := by
  conv => lhs; rw [objRecN]
  conv => rhs; rw [objRecN]
  simp only [h]

theorem exprN_congr (b : Array UInt8) (i w j w' : Word) (f : Fld)
    (h : nextMemberN b i w = nextMemberN b j w') : exprN b i w f = exprN b j w' f := by
  conv => lhs; rw [exprN]
  conv => rhs; rw [exprN]
  simp only [h]

/-! ## The generic sub-object loop -/

variable {σ α : Type}

/-- What a sub-object loop `F` does at a key `kc` whose value is at `v`, on its `ok` path: the
member's value ends at `exValN`'s position, and the loop goes on from there with a state
related to the slots after `objPut`. -/
def VK (b : ByteArray) (F : USize → Bool → UInt32 → σ → ScanRes α) (R : UInt32 → σ → Obj → Prop)
    (i v : USize) (kc : Word) (seen : UInt32) (st : σ) (r : α) (e : USize) (X : ScanRes α) : Prop :=
  X = .ok r e → ∃ e' seen' st', e'.toUInt64 = exValN b.data kc i.toUInt64 v.toUInt64 ∧ i < e' ∧
    F e' false seen' st' = .ok r e ∧
    ∀ o, R seen st o → R seen' st' (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 e'.toUInt64) o)

/-- The shape of a con-leche sub-object loop `F` on its `ok` path: `R` relates its state to the
slots, `Res` its result to the final slots. -/
structure VLoop (b : ByteArray) (F : USize → Bool → UInt32 → σ → ScanRes α)
    (R : UInt32 → σ → Obj → Prop) (Res : α → Obj → Prop) : Prop where
  stop : ∀ i w seen st r e, ¬ i < b.usize → F i w seen st ≠ .ok r e
  ws : ∀ i w seen st, i < b.usize → isWs (byteAt b i) = true → F i w seen st = F (i + 1) w seen st
  close : ∀ i w seen st r e, i < b.usize → byteAt b i = 125 → F i w seen st = .ok r e →
    e = i + 1 ∧ ∀ o, R seen st o → Res r o
  comma : ∀ i w seen st r e, i < b.usize → byteAt b i = 44 → F i w seen st = .ok r e →
    w = false ∧ F (i + 1) true seen st = .ok r e
  quote : ∀ i w seen st r e, i < b.usize → byteAt b i = 34 →
    (w = false ∨ keyEnd b (i + 1) = 0 ∨ valueAt b i (keyEnd b (i + 1)) = i) →
    F i w seen st ≠ .ok r e
  key : ∀ i seen st r e, i < b.usize → byteAt b i = 34 → keyEnd b (i + 1) ≠ 0 →
    valueAt b i (keyEnd b (i + 1)) ≠ i →
    VK b F R i (valueAt b i (keyEnd b (i + 1)))
      (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx) seen st r e (F i true seen st)
  other : ∀ i w seen st r e, i < b.usize → isWs (byteAt b i) = false → byteAt b i ≠ 125 →
    byteAt b i ≠ 44 → byteAt b i ≠ 34 → F i w seen st ≠ .ok r e
  res_e : ∀ r o x, Res r o → Res r ⟨x, o.x0, o.x1, o.x2, o.x3⟩

section generic
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem objRec_link (F : USize → Bool → UInt32 → σ → ScanRes α) (R : UInt32 → σ → Obj → Prop)
    (Res : α → Obj → Prop) (H : VLoop b F R Res) (i : USize) (w : Bool) (seen : UInt32) (st : σ)
    (r : α) (e : USize) (o : Obj) (h : F i w seen st = .ok r e) (hR : R seen st o) :
    (objRecN b.data i.toUInt64 (bw w) o).e = e.toUInt64 ∧
      Res r (objRecN b.data i.toUInt64 (bw w) o) := by
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    by_cases hws : isWs (byteAt b i) = true
    · rw [H.ws i w seen st hi hws] at h
      rw [objRecN_congr _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)]
      exact objRec_link F R Res H (i + 1) w seen st r e o h hR
    by_cases h125 : byteAt b i = 125
    · obtain ⟨rfl, hres⟩ := H.close i w seen st r e hi h125 h
      rw [objRecN_close _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125]),
        nm_close b h64 hsize i _ hi hws h125]
      exact ⟨by simp only [succ_toUInt64 h64], H.res_e _ _ _ (hres o hR)⟩
    by_cases h44 : byteAt b i = 44
    · obtain ⟨rfl, h'⟩ := H.comma i w seen st r e hi h44 h
      simp only [bw, Bool.false_eq_true, ite_false]
      rw [objRecN_congr _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)]
      exact objRec_link F R Res H (i + 1) true seen st r e o h' hR
    by_cases h34 : byteAt b i = 34
    · by_cases hbad : w = false ∨ keyEnd b (i + 1) = 0 ∨ valueAt b i (keyEnd b (i + 1)) = i
      · exact absurd h (H.quote i w seen st r e hi h34 hbad)
      simp only [not_or] at hbad
      obtain ⟨hw, hk, hv⟩ := hbad
      have hw' : w = true := by simpa using hw
      subst hw'
      have hm := nm_key b h64 hsize i hi h34 hk hv
      obtain ⟨e', seen', st', he, hie, h', hR'⟩ := H.key i seen st r e hi h34 hk hv h
      simp only [bw, ite_true]
      rw [objRecN_key _ _ _ _ (by rw [hm]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hm]; exact (by decide : (2 : Word) ≠ 1))]
      simp only [hm]
      rw [← he, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
      exact objRec_link F R Res H e' false seen' st' r e _ h' (hR' o hR)
    · exact absurd h (H.other i w seen st r e hi (by simpa using hws) h125 h44 h34)
  · exact absurd h (H.stop i w seen st r e hi)
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹i < _›; omega)

end generic

/-! ## One key of a sub-object loop -/

section keys
variable {b : ByteArray} {F : USize → Bool → UInt32 → σ → ScanRes α} {R : UInt32 → σ → Obj → Prop}
  {i v : USize} {kc : Word} {seen : UInt32} {st : σ} {r : α} {e : USize}

theorem vk_err (z : ScanErr) : VK b F R i v kc seen st r e (.err z) := fun h => by cases h

theorem vk_guard {sb : UInt32} {X : ScanRes α} {z : ScanErr}
    (hX : seen &&& sb = 0 → VK b F R i v kc seen st r e X) :
    VK b F R i v kc seen st r e (if seen &&& sb = 0 then X else .err z) := by
  by_cases hs : seen &&& sb = 0
  · rw [ite_eq_left hs]; exact hX hs
  · rw [ite_eq_right hs]; exact vk_err z

/-- A scanner that returns its end or `0` (`scanBinderInfo`), at a key whose slot does not
change. -/
theorem vk_usz {sb : UInt32} (u : USize) {G : ScanRes α} {x y : ScanErr} (st' : σ)
    (hG : G = F u false (seen ||| sb) st')
    (hval : exValN b.data kc i.toUInt64 v.toUInt64 = u.toUInt64)
    (hR : ∀ o, R seen st o →
      R (seen ||| sb) st' (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 u.toUInt64) o)) :
    VK b F R i v kc seen st r e (if u = 0 then .err x else if i < u then G else .err y) := by
  intro h
  split at h; cases h
  split at h
  · rename_i hie
    exact ⟨u, seen ||| sb, st', hval.symm, hie, hG ▸ h, hR⟩
  · cases h

/-- A scanner with a `ScanRes` (`scanBool`, `scanNatList`), its `ok` arm. -/
theorem vk_res {sb : UInt32} (e₁ : USize) {G : ScanRes α} {y : ScanErr} (st' : σ)
    (hG : G = F e₁ false (seen ||| sb) st')
    (hval : exValN b.data kc i.toUInt64 v.toUInt64 = e₁.toUInt64)
    (hR : ∀ o, R seen st o →
      R (seen ||| sb) st' (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 e₁.toUInt64) o)) :
    VK b F R i v kc seen st r e (if i < e₁ then G else .err y) := by
  intro h
  split at h
  · rename_i hie
    exact ⟨e₁, seen ||| sb, st', hval.symm, hie, hG ▸ h, hR⟩
  · cases h

end keys

section keynum
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
variable {F : USize → Bool → UInt32 → σ → ScanRes α} {R : UInt32 → σ → Obj → Prop}
  {i v : USize} {kc : Word} {seen : UInt32} {st : σ} {r : α} {e : USize}
include h64 hsize

/-- A number (`numEnd`, `slot_nat`). -/
theorem vk_num {sb : UInt32} {G : ScanRes α} {x y : ScanErr} (st' : σ)
    (hG : G = F (numEnd b v) false (seen ||| sb) st')
    (hval : exValN b.data kc i.toUInt64 v.toUInt64 = L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64)
    (hR : ∀ o, R seen st o →
      R (seen ||| sb) st' (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 (numEnd b v).toUInt64) o)) :
    VK b F R i v kc seen st r e
      (if numEnd b v = v then .err x else if i < numEnd b v then G else .err y) := by
  intro h
  split at h; cases h; rename_i hne
  split at h
  · rename_i hie
    refine ⟨numEnd b v, seen ||| sb, st', ?_, hie, hG ▸ h, hR⟩
    rw [hval, slotNatN_link b h64 hsize, ite_eq_right hne, ite_eq_left hie]
  · cases h

end keynum


section tuples
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
variable {β₁ β₂ β₃ : Type} {R : UInt32 → σ → Obj → Prop}
  {i v : USize} {kc : Word} {seen : UInt32} {r : α} {e : USize}

include h64 hsize in
/-- `vk_num`, `vk_usz`, `vk_res` for a loop over two and three fields. -/
theorem vk_num2 (f : USize → Bool → UInt32 → β₁ → β₂ → ScanRes α) {R : UInt32 → β₁ × β₂ → Obj → Prop}
    {st : β₁ × β₂} {sb : UInt32} {x y : ScanErr} (a1 : β₁) (a2 : β₂)
    (hval : exValN b.data kc i.toUInt64 v.toUInt64 = L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64)
    (hR : ∀ o, R seen st o →
      R (seen ||| sb) (a1, a2) (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 (numEnd b v).toUInt64) o)) :
    VK b (fun i w s (st : β₁ × β₂) => f i w s st.1 st.2) R i v kc seen st r e
      (if numEnd b v = v then .err x else if i < numEnd b v then f (numEnd b v) false (seen ||| sb) a1 a2
       else .err y) :=
  vk_num b h64 hsize (a1, a2) rfl hval hR

include h64 hsize in
theorem vk_num3 (f : USize → Bool → UInt32 → β₁ → β₂ → β₃ → ScanRes α)
    {R : UInt32 → β₁ × β₂ × β₃ → Obj → Prop}
    {st : β₁ × β₂ × β₃} {sb : UInt32} {x y : ScanErr} (a1 : β₁) (a2 : β₂) (a3 : β₃)
    (hval : exValN b.data kc i.toUInt64 v.toUInt64 = L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64)
    (hR : ∀ o, R seen st o →
      R (seen ||| sb) (a1, a2, a3) (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 (numEnd b v).toUInt64) o)) :
    VK b (fun i w s (st : β₁ × β₂ × β₃) => f i w s st.1 st.2.1 st.2.2) R i v kc seen st r e
      (if numEnd b v = v then .err x else if i < numEnd b v then f (numEnd b v) false (seen ||| sb) a1 a2 a3
       else .err y) :=
  vk_num b h64 hsize (a1, a2, a3) rfl hval hR

theorem vk_usz2 (f : USize → Bool → UInt32 → β₁ → β₂ → ScanRes α) {R : UInt32 → β₁ × β₂ → Obj → Prop}
    {st : β₁ × β₂} {sb : UInt32} {x y : ScanErr} (u : USize) (a1 : β₁) (a2 : β₂)
    (hval : exValN b.data kc i.toUInt64 v.toUInt64 = u.toUInt64)
    (hR : ∀ o, R seen st o →
      R (seen ||| sb) (a1, a2) (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 u.toUInt64) o)) :
    VK b (fun i w s (st : β₁ × β₂) => f i w s st.1 st.2) R i v kc seen st r e
      (if u = 0 then .err x else if i < u then f u false (seen ||| sb) a1 a2 else .err y) :=
  vk_usz u (a1, a2) rfl hval hR

theorem vk_res2 (f : USize → Bool → UInt32 → β₁ → β₂ → ScanRes α) {R : UInt32 → β₁ × β₂ → Obj → Prop}
    {st : β₁ × β₂} {sb : UInt32} {y : ScanErr} (e₁ : USize) (a1 : β₁) (a2 : β₂)
    (hval : exValN b.data kc i.toUInt64 v.toUInt64 = e₁.toUInt64)
    (hR : ∀ o, R seen st o →
      R (seen ||| sb) (a1, a2) (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 e₁.toUInt64) o)) :
    VK b (fun i w s (st : β₁ × β₂) => f i w s st.1 st.2) R i v kc seen st r e
      (if i < e₁ then f e₁ false (seen ||| sb) a1 a2 else .err y) :=
  vk_res e₁ (a1, a2) rfl hval hR

theorem vk_res3 (f : USize → Bool → UInt32 → β₁ → β₂ → β₃ → ScanRes α)
    {R : UInt32 → β₁ × β₂ × β₃ → Obj → Prop}
    {st : β₁ × β₂ × β₃} {sb : UInt32} {y : ScanErr} (e₁ : USize) (a1 : β₁) (a2 : β₂) (a3 : β₃)
    (hval : exValN b.data kc i.toUInt64 v.toUInt64 = e₁.toUInt64)
    (hR : ∀ o, R seen st o →
      R (seen ||| sb) (a1, a2, a3) (objPut kc v.toUInt64 (rdNatN b.data v.toUInt64 e₁.toUInt64) o)) :
    VK b (fun i w s (st : β₁ × β₂ × β₃) => f i w s st.1 st.2.1 st.2.2) R i v kc seen st r e
      (if i < e₁ then f e₁ false (seen ||| sb) a1 a2 a3 else .err y) :=
  vk_res e₁ (a1, a2, a3) rfl hval hR

end tuples

/-! ## The byte arms of an instance -/

/-- `stop`, `ws`, `comma`, `quote`, `other` of `VLoop` for con-leche's loop `f`. -/
syntax "vloop_stop " ident : tactic
macro_rules
  | `(tactic| vloop_stop $f) => `(tactic| (
      intro i w seen st r e h; rw [$f:ident, dite_eq_right h]; simp))
syntax "vloop_ws " ident : tactic
macro_rules
  | `(tactic| vloop_ws $f) => `(tactic| (
      intro i w seen st h hws; rw [$f:ident, dite_eq_left h]; simp only [uget_byteAt _ i h, hws, ite_true]))
syntax "vloop_comma " ident : tactic
macro_rules
  | `(tactic| vloop_comma $f) => `(tactic| (
      intro i w seen st r e h hc hok; rw [$f:ident, dite_eq_left h] at hok
      simp [uget_byteAt _ i h, hc, isWs] at hok
      split at hok; cases hok
      · rename_i hw; exact ⟨by simpa using hw, hok⟩))
syntax "vloop_quote " ident : tactic
macro_rules
  | `(tactic| vloop_quote $f) => `(tactic| (
      intro i w seen st r e h hc hbad hok; rw [$f:ident, dite_eq_left h] at hok
      simp [uget_byteAt _ i h, hc, isWs] at hok
      rcases hbad with hb | hb | hb <;> (repeat' split at hok) <;> simp_all))
syntax "vloop_other " ident : tactic
macro_rules
  | `(tactic| vloop_other $f) => `(tactic| (
      intro i w seen st r e h hws h1 h2 h3 hok; rw [$f:ident, dite_eq_left h] at hok
      simp [uget_byteAt _ i h, hws, h1, h2, h3] at hok))
/-- The `close` arm: the record, then the result relation `hres`. -/
syntax "vloop_close " ident : tactic
macro_rules
  | `(tactic| vloop_close $f) => `(tactic| (
      intro i w seen st r e h hc hok; rw [$f:ident, dite_eq_left h] at hok
      simp [uget_byteAt _ i h, hc, isWs] at hok
      split at hok; cases hok
      split at hok
      · cases hok; refine ⟨rfl, fun o ho => ?_⟩
      · cases hok))

/-- The fields a sub-object's slots give, without the end. -/
def ORes (b : ByteArray) (k : Word) (r : ExprRec) (o : Obj) : Prop :=
  ExprR b r ⟨(objFld k o).x0, 0, (objFld k o).x1, (objFld k o).x2, (objFld k o).x3⟩

theorem oRes_e (b : ByteArray) (k : Word) (r : ExprRec) (o : Obj) (x : Word) (h : ORes b k r o) :
    ORes b k r ⟨x, o.x0, o.x1, o.x2, o.x3⟩ := by
  unfold ORes objFld at *
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all

/-! ## The six sub-objects -/

section objs
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- The value of a numeric member, as `read_nat` reads it. -/
theorem rd_item (i : USize) (h : i < b.usize) (hk : keyEnd b (i + 1) ≠ 0)
    (hv : valueAt b i (keyEnd b (i + 1)) ≠ i) (hc : byteAt b i = 34) :
    ItemR (rdNatN b.data (valueAt b i (keyEnd b (i + 1))).toUInt64
      (numEnd b (valueAt b i (keyEnd b (i + 1)))).toUInt64)
      (readNatAt b (valueAt b i (keyEnd b (i + 1))) (numEnd b (valueAt b i (keyEnd b (i + 1))))) := by
  have hvle := nm_key_le b h64 hsize i h hc hk hv
  exact rdNat_link b h64 hsize _ _ (le_numEnd b h64 hsize _ hvle) (numEnd_le b h64 hsize _ hvle)

end objs

/-- The key arms of an instance: `vk_err` for keys the loop does not have, `vk_guard` then the
value's kind for its own; the slot obligations by `simp_all`. -/
syntax "vloop_key " ident ident : tactic
macro_rules
  | `(tactic| vloop_key $f $b) => `(tactic| (
      intro i seen st r e h hc hk hv
      have hRd := rd_item $b ‹_› ‹_› i h hk hv hc
      rw [$f:ident, dite_eq_left h]
      simp [uget_byteAt _ i h, hc, isWs, hk, hv]
      generalize valueAt $b i (keyEnd $b (i + 1)) = v at hRd ⊢
      generalize keyAt $b i (keyEnd $b (i + 1) - (i + 1)) = K
      cases K
      all_goals dsimp only
      all_goals first
        | exact vk_err _
        | (apply vk_guard
           intro hseen
           first
             | (apply vk_num2 $b ‹_› ‹_›
                · rfl
                · intro o ho; simp_all (config := {decide := true}) [objPut])
             | (apply vk_num3 $b ‹_› ‹_›
                · rfl
                · intro o ho; simp_all (config := {decide := true}) [objPut])
             | (apply vk_usz2 $b
                · exact (scanBinderInfo_link $b ‹_› ‹_› _).symm
                · intro o ho; simp_all (config := {decide := true}) [objPut])
             | (split
                all_goals first
                  | exact vk_err _
                  | (rename_i heq
                     apply vk_res3 $b
                     · have := scanBool_link $b ‹_› ‹_› v; rw [heq] at this; exact this.symm
                     · intro o ho; simp_all (config := {decide := true}) [objPut])))))

/-- `close`, with the result relation by `simp_all`. -/
syntax "vloop_res " ident : tactic
macro_rules
  | `(tactic| vloop_res $f) => `(tactic| (
      intro i w seen st r e h hc hok; rw [$f:ident, dite_eq_left h] at hok
      simp [uget_byteAt _ i h, hc, isWs] at hok
      split at hok; cases hok
      split at hok
      · cases hok
        exact ⟨rfl, fun o ho => by simp_all (config := {decide := true}) [ORes, objFld, ExprR]⟩
      · cases hok))

/-! ## The list of a `const` -/

theorem itemsR_append (xs ys : List Word) (ns ms : List Nat) (h1 : ItemsR xs ns) (h2 : ItemsR ys ms) :
    ItemsR (xs ++ ys) (ns ++ ms) := by
  induction xs generalizing ns with
  | nil => cases ns with
    | nil => simpa using h2
    | cons _ _ => exact h1.elim
  | cons x xs ih => cases ns with
    | nil => exact h1.elim
    | cons n ns => exact ⟨h1.1, ih ns h1.2⟩

section list
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem items_link (i : USize) (acc : List Nat) (w : Bool) (us : List Nat) (e : USize)
    (h : scanNatListLoop b i acc w = .ok us e) (xs : List Word) (hx : ItemsR xs acc.reverse) :
    ItemsR (xs ++ itemsN b.data i.toUInt64) us := by
  rw [scanNatListLoop] at h
  by_cases hi : i < b.usize
  · have hlt := (lt_usize_iff b h64 hsize i).mp hi
    have hcw := byteW_eq b h64 hsize i
    have hs := succ_toUInt64 h64 i
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    have hin := usizeInBounds b i hi
    rw [dite_eq_left hi] at h
    simp only [uget_byteAt _ i hi] at h
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true] at h
      have hne : byteW b.data i.toUInt64 ≠ 93 := by
        rw [hcw]; intro h'; have := (u8_toUInt64_eq _ 93 (by decide)).mp h'
        rw [this] at hws; exact absurd hws (by decide)
      have hnd : ¬ (48 ≤ byteW b.data i.toUInt64 ∧ byteW b.data i.toUInt64 ≤ 57) := by
        rw [hcw, ← digit_iff]; intro h'; simp [isWs, isDigit] at hws h'; grind
      rw [itemsN_other _ _ hlt hne hnd, ← hs]
      exact items_link (i + 1) acc w us e h xs hx
    simp only [hws, Bool.false_eq_true, ite_false] at h
    by_cases h93 : byteAt b i = 93
    · simp only [h93, show ((93 : UInt8) == 93) = true from rfl, ite_true] at h
      split at h
      · simp at h
      · obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
        rw [itemsN_close _ _ hlt (by rw [hcw, h93]; rfl)]
        simpa using hx
    have h93' : byteW b.data i.toUInt64 ≠ 93 := by
      rw [hcw]; exact fun h' => h93 ((u8_toUInt64_eq _ 93 (by decide)).mp h')
    simp only [show (byteAt b i == 93) = false by simpa using h93, Bool.false_eq_true, ite_false] at h
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true] at h
      split at h
      · simp at h
      have hnd : ¬ (48 ≤ byteW b.data i.toUInt64 ∧ byteW b.data i.toUInt64 ≤ 57) := by
        rw [hcw, h44]; decide
      rw [itemsN_other _ _ hlt h93' hnd, ← hs]
      exact items_link (i + 1) acc true us e h xs hx
    simp only [show (byteAt b i == 44) = false by simpa using h44, Bool.false_eq_true, ite_false] at h
    by_cases hd : isDigit (byteAt b i) = true
    · simp only [hd, ite_true] at h
      split at h
      · simp at h
      have hd' := (digit_iff _).mp hd
      rw [← hcw] at hd'
      split at h
      · simp at h
      split at h
      · rename_i hie
        have hne' := numEnd_toUInt64_eq b h64 (by omega) i
        have hieW : i.toUInt64 < UInt64.ofNat (L.Scan.Leaves.numEndN b.data i.toUInt64.toNat) := by
          rw [USize.toNat_toUInt64, ← hne']; exact (lt_toUInt64_iff _ _).mp hie
        rw [itemsN_digit _ _ hlt h93' hd' hieW]
        rw [USize.toNat_toUInt64, ← hne']
        have hle : (numEnd b i).toNat ≤ b.size := by
          have := numEnd_toNat_eq b h64 (by omega) i
          rw [this]; exact L.Scan.Values.numEndN_le b.data i.toNat (by have := usizeInBounds b i hi; have hb : b.data.size = b.size := rfl; omega)
        have hR := rdNat_link b h64 hsize i (numEnd b i) (USize.le_of_lt hie) hle
        have := items_link (numEnd b i) _ false us e h (xs ++ [rdNatN b.data i.toUInt64 (numEnd b i).toUInt64])
          (by simpa using itemsR_append _ _ _ _ hx (show ItemsR [_] [_] from ⟨hR, trivial⟩))
        simpa using this
      · simp at h
    · simp only [hd, Bool.false_eq_true, ite_false] at h
      simp at h
  · rw [dite_eq_right hi] at h; simp at h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹i < numEnd b i›; omega)

theorem list_link (v : USize) (us : List Nat) (e : USize) (h : scanNatList b v = .ok us e) :
    ItemsR (listN b.data v.toUInt64) us := by
  unfold scanNatList at h
  split at h
  · rename_i hc
    have hi : v < b.usize := by
      refine Classical.byContradiction fun hn => ?_
      have h0 : byteAt b v = 0 := by unfold byteAt; rw [dite_eq_right hn]
      rw [h0] at hc; exact absurd hc (by decide)
    unfold listN
    rw [← succ_toUInt64 h64]
    simpa using items_link b h64 hsize (v + 1) [] true us e h [] trivial
  · cases h

end list

/-! ## The instances -/

theorem and3_ne (s : UInt32) (h : s &&& 3 = 3) : s &&& 2 ≠ 0 := by
  have : s &&& 2 = (s &&& 3) &&& 2 := by rw [UInt32.and_assoc]; rfl
  rw [this, h]; decide

theorem or1_and2 (s : UInt32) : (s ||| 1) &&& 2 = s &&& 2 := by
  apply UInt32.toBitVec_inj.mp
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or]
  ext i hi
  rcases i with _ | _ | i <;> simp [BitVec.getElem_and, BitVec.getElem_or] <;> (try decide) <;>
    simp [Nat.testBit]

section inst
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- A binder's or an `app`'s state `(x1, x0)`. -/
def pairR (_ : UInt32) (st : Nat × Nat) (o : Obj) : Prop := ItemR o.x1 st.1 ∧ ItemR o.x0 st.2

/-- A `letE`'s state `(body, type, value)`. -/
def letR (_ : UInt32) (st : Nat × Nat × Nat) (o : Obj) : Prop :=
  ItemR o.x1 st.1 ∧ ItemR o.x0 st.2.1 ∧ ItemR o.x2 st.2.2

/-- A `proj`'s state `(idx, struct, typeName)`. -/
def projR (_ : UInt32) (st : Nat × Nat × Nat) (o : Obj) : Prop :=
  ItemR o.x2 st.1 ∧ ItemR o.x1 st.2.1 ∧ ItemR o.x0 st.2.2

/-- A `const`'s state `(name, us)`: the list once its key was seen. -/
def constR (b : ByteArray) (seen : UInt32) (st : Nat × List Nat) (o : Obj) : Prop :=
  ItemR o.x3 st.1 ∧ (seen &&& 2 ≠ 0 → ItemsR (listN b.data o.x1) st.2)

attribute [local simp] pairR letR projR

theorem appV : VLoop b (fun i w seen (st : Nat × Nat) => scanAppExprLoop b i w seen st.1 st.2)
    pairR (ORes b 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, oRes_e b 2⟩
  · vloop_stop scanAppExprLoop
  · vloop_ws scanAppExprLoop
  · vloop_res scanAppExprLoop
  · vloop_comma scanAppExprLoop
  · vloop_quote scanAppExprLoop
  · vloop_key scanAppExprLoop b
  · vloop_other scanAppExprLoop

theorem lamV : VLoop b (fun i w seen (st : Nat × Nat) => scanLamExprLoop b i w seen st.1 st.2)
    pairR (ORes b 29) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, oRes_e b 29⟩
  · vloop_stop scanLamExprLoop
  · vloop_ws scanLamExprLoop
  · vloop_res scanLamExprLoop
  · vloop_comma scanLamExprLoop
  · vloop_quote scanLamExprLoop
  · vloop_key scanLamExprLoop b
  · vloop_other scanLamExprLoop

theorem forallV : VLoop b (fun i w seen (st : Nat × Nat) => scanForallExprLoop b i w seen st.1 st.2)
    pairR (ORes b 14) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, oRes_e b 14⟩
  · vloop_stop scanForallExprLoop
  · vloop_ws scanForallExprLoop
  · vloop_res scanForallExprLoop
  · vloop_comma scanForallExprLoop
  · vloop_quote scanForallExprLoop
  · vloop_key scanForallExprLoop b
  · vloop_other scanForallExprLoop

theorem letV : VLoop b
    (fun i w seen (st : Nat × Nat × Nat) => scanLetExprLoop b i w seen st.1 st.2.1 st.2.2)
    letR (ORes b 30) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, oRes_e b 30⟩
  · vloop_stop scanLetExprLoop
  · vloop_ws scanLetExprLoop
  · vloop_res scanLetExprLoop
  · vloop_comma scanLetExprLoop
  · vloop_quote scanLetExprLoop
  · vloop_key scanLetExprLoop b
  · vloop_other scanLetExprLoop

theorem projV : VLoop b
    (fun i w seen (st : Nat × Nat × Nat) => scanProjExprLoop b i w seen st.1 st.2.1 st.2.2)
    projR (ORes b 48) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, oRes_e b 48⟩
  · vloop_stop scanProjExprLoop
  · vloop_ws scanProjExprLoop
  · vloop_res scanProjExprLoop
  · vloop_comma scanProjExprLoop
  · vloop_quote scanProjExprLoop
  · vloop_key scanProjExprLoop b
  · vloop_other scanProjExprLoop


theorem constV : VLoop b
    (fun i w seen (st : Nat × List Nat) => scanConstExprLoop b i w seen st.1 st.2)
    (constR b) (ORes b 9) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, oRes_e b 9⟩
  · vloop_stop scanConstExprLoop
  · vloop_ws scanConstExprLoop
  · intro i w seen st r e h hc hok; rw [scanConstExprLoop, dite_eq_left h] at hok
    simp [uget_byteAt _ i h, hc, isWs] at hok
    split at hok; cases hok
    split at hok
    · rename_i hm
      cases hok
      exact ⟨rfl, fun o ho => by
        simp only [constR] at ho
        have := ho.2 (and3_ne _ hm)
        simp_all (config := {decide := true}) [ORes, objFld, ExprR]⟩
    · cases hok
  · vloop_comma scanConstExprLoop
  · vloop_quote scanConstExprLoop
  · intro i seen st r e h hc hk hv
    have hRd := rd_item b ‹_› ‹_› i h hk hv hc
    rw [scanConstExprLoop, dite_eq_left h]
    simp [uget_byteAt _ i h, hc, isWs, hk, hv]
    generalize valueAt b i (keyEnd b (i + 1)) = v at hRd ⊢
    generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K
    cases K
    all_goals dsimp only
    all_goals try exact vk_err _
    case kName =>
      apply vk_guard
      intro hseen
      apply vk_num2 b ‹_› ‹_›
      · rfl
      · intro o ho
        simp only [constR] at ho ⊢
        simp (config := {decide := true}) only [objPut, ↓reduceIte]
        exact ⟨hRd, fun h2 => ho.2 (by rwa [or1_and2] at h2)⟩
    case kUs =>
      apply vk_guard
      intro hseen
      split
      · exact vk_err _
      · rename_i x e₁ heq
        apply vk_res2 b
        · have := scanNatList_link b ‹_› ‹_› v; rw [heq] at this; exact this.symm
        · intro o ho
          simp only [constR] at ho ⊢
          simp (config := {decide := true}) only [objPut, ↓reduceIte]
          exact ⟨ho.1, fun _ => list_link b ‹_› ‹_› v x e₁ heq⟩
  · vloop_other scanConstExprLoop

end inst

/-! ## The sub-object entries -/

theorem objFld_e (k : Word) (o : Obj) : (objFld k o).e = o.e := by
  unfold objFld; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem objFld_x0 (k : Word) (o : Obj) : (objFld k o).x0 ≠ 0 := by
  unfold objFld; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (dsimp only; decide)

theorem exprR_idx (b : ByteArray) (r : ExprRec) (f : Fld) (x : Word) (h : ExprR b r f) :
    ExprR b r ⟨f.pl, x, f.a, f.c, f.d⟩ := by
  cases r <;> exact h

/-- What the expression loop's words say about con-leche's payload so far. -/
def EPlR (b : ByteArray) : LinePayload → Fld → Prop
  | .absent, _ => True
  | .expr r, f => ExprR b r f
  | _, _ => False

theorem ePlR_idx (b : ByteArray) (pl : LinePayload) (f : Fld) (x : Word) (h : EPlR b pl f) :
    EPlR b pl ⟨f.pl, x, f.a, f.c, f.d⟩ := by
  rcases pl with _ | _ | _ | r | _ | _
  all_goals first | exact h | exact exprR_idx b r f x h

theorem ePlR_obj (b : ByteArray) (k : Word) (o : Obj) (f : Fld) (r : ExprRec) (h : ORes b k r o) :
    EPlR b (.expr r) (fldPut (objFld k o) f) := by
  unfold fldPut; rw [ite_eq_right (objFld_x0 k o)]
  exact exprR_idx b r _ f.idx h

section entries
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem objEntry_link {σ : Type} (F : USize → Bool → UInt32 → σ → ScanRes ExprRec)
    (R : UInt32 → σ → Obj → Prop) (k : Word) (H : VLoop b F R (ORes b k)) (st₀ : σ)
    (h₀ : R 0 st₀ ⟨0, 0, 0, 0, 0⟩) (v : USize) (hc : (byteAt b v == 123) = true) (r : ExprRec)
    (e : USize) (h : F (v + 1) true 0 st₀ = .ok r e) :
    (recObjN b.data v.toUInt64).e = e.toUInt64 ∧ ORes b k r (recObjN b.data v.toUInt64) := by
  unfold recObjN
  rw [← (obj_open b h64 hsize v hc).2]
  exact objRec_link b h64 hsize F R (ORes b k) H (v + 1) true 0 st₀ r e _ h h₀

/-- A sub-object at `v`, by the payload key `k` and its con-leche scanner. -/
theorem obj_link (k : Word) (v : USize) (r : ExprRec) (e : USize)
    (h : (k = 2 ∧ scanAppExpr b v = .ok r e) ∨ (k = 29 ∧ scanLamExpr b v = .ok r e) ∨
      (k = 14 ∧ scanForallExpr b v = .ok r e) ∨ (k = 30 ∧ scanLetExpr b v = .ok r e) ∨
      (k = 9 ∧ scanConstExpr b v = .ok r e) ∨ (k = 48 ∧ scanProjExpr b v = .ok r e)) :
    (recObjN b.data v.toUInt64).e = e.toUInt64 ∧ ORes b k r (recObjN b.data v.toUInt64) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · unfold scanAppExpr at h; split at h
    · exact objEntry_link b h64 hsize _ _ _ (appV b h64 hsize) (0, 0) ⟨itemR_zero, itemR_zero⟩ v ‹_› r e h
    · cases h
  · unfold scanLamExpr at h; split at h
    · exact objEntry_link b h64 hsize _ _ _ (lamV b h64 hsize) (0, 0) ⟨itemR_zero, itemR_zero⟩ v ‹_› r e h
    · cases h
  · unfold scanForallExpr at h; split at h
    · exact objEntry_link b h64 hsize _ _ _ (forallV b h64 hsize) (0, 0) ⟨itemR_zero, itemR_zero⟩ v ‹_› r e h
    · cases h
  · unfold scanLetExpr at h; split at h
    · exact objEntry_link b h64 hsize _ _ _ (letV b h64 hsize) (0, 0, 0)
        ⟨itemR_zero, itemR_zero, itemR_zero⟩ v ‹_› r e h
    · cases h
  · unfold scanConstExpr at h; split at h
    · exact objEntry_link b h64 hsize _ _ _ (constV b h64 hsize) (0, [])
        ⟨itemR_zero, fun h => absurd rfl h⟩ v ‹_› r e h
    · cases h
  · unfold scanProjExpr at h; split at h
    · exact objEntry_link b h64 hsize _ _ _ (projV b h64 hsize) (0, 0, 0)
        ⟨itemR_zero, itemR_zero, itemR_zero⟩ v ‹_› r e h
    · cases h

omit h64 hsize in
theorem skipDigits_ge (i : USize) : i.toNat ≤ (skipDigits b i).toNat := by
  fun_induction skipDigits b i with
  | case1 i h _ ih => have := usizeStep b i h; omega
  | case2 => exact Nat.le_refl _
  | case3 => exact Nat.le_refl _

/-- A `natVal`'s quoted digits. -/
theorem natVal_link (v : USize) (n : Nat) (e : USize) (h : scanQuotedNat b v = .ok n e) :
    L.Scan.Values.quotedNatN b.data v.toUInt64 = e.toUInt64 ∧
      ItemR (rdNatN b.data (v.toUInt64 + 1) (e.toUInt64 - 1)) n ∧
      NatValR b (v.toUInt64 + 1) (e.toUInt64 - 1) n := by
  have hq := scanQuotedNat_eq_quotedNatN b h64 hsize v
  rw [h] at hq
  refine ⟨hq.symm, ?_⟩
  unfold scanQuotedNat at h
  split at h; cases h; rename_i h34
  dsimp only at h
  split at h; cases h; rename_i hne
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hne
  obtain ⟨hne1, hq34⟩ := hne
  obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
  have hv : v < b.usize := by
    refine Classical.byContradiction fun hn => ?_
    have h0 : byteAt b v = 0 := by unfold byteAt; rw [dite_eq_right hn]
    rw [h0] at h34; exact h34 (by decide)
  have hd : skipDigits b (v + 1) < b.usize := by
    refine Classical.byContradiction fun hn => ?_
    have h0 : byteAt b (skipDigits b (v + 1)) = 0 := by unfold byteAt; rw [dite_eq_right hn]
    rw [h0] at hq34; exact absurd hq34 (by decide)
  have hv1 := succ_toUInt64 h64 v
  have hd1 := succ_toUInt64 h64 (skipDigits b (v + 1))
  have hge := skipDigits_ge b (v + 1)
  have hlt : v + 1 < skipDigits b (v + 1) := by
    rw [USize.lt_iff_toNat_lt]
    have : (v + 1).toNat ≠ (skipDigits b (v + 1)).toNat := fun h' => hne1 (USize.toNat_inj.mp h').symm
    omega
  have hdin := usizeInBounds b _ hd
  rw [← hv1, hd1, UInt64.add_sub_cancel]
  refine ⟨rdNat_link b h64 hsize _ _ (USize.le_of_lt hlt) (by omega),
    v + 1, skipDigits b (v + 1), rfl, rfl, hlt, rfl, rfl⟩

/-- A `strVal`'s body. -/
theorem strVal_link (v : USize) (s : String) (e : USize) (h : ConLeche.Frontend.scanString b v = .ok s e) :
    L.Scan.Str.scanStringN b.data v.toUInt64 = e.toUInt64 ∧
      StrR b (v.toUInt64 + 1) (e.toUInt64 - 1) s := by
  have hs := scanString_link b h64 hsize v
  rw [h] at hs
  exact ⟨hs.symm, v, e, rfl, rfl, h⟩

end entries

/-! ## `rec_expr_loop` -/

section line
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- **The expression line loop, linked**: on con-leche's `ok` path, if `rec_expr_loop`'s kind is
not `0`, its words are the fields of con-leche's expression record (`ERecR`). -/
theorem exprLine_link (i : USize) (w : Bool) (ik : UInt8) (idx : Nat) (pl : LinePayload) (f : Fld)
    (r : LineRec) (e : USize) (h : scanLineLoop b i w ik idx pl = .ok r e)
    (hI : ItemR f.idx idx) (hP : EPlR b pl f) :
    (exprN b.data i.toUInt64 (bw w) f).pl ≠ 0 → ERecR b r (exprN b.data i.toUInt64 (bw w) f) := by
  rw [scanLineLoop.eq_def] at h
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    rw [dite_eq_left hi] at h
    simp only [uget_byteAt _ i hi] at h
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true] at h
      rw [exprN_congr _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)]
      exact exprLine_link (i + 1) w ik idx pl f r e h hI hP
    simp only [hws, Bool.false_eq_true, ite_false] at h
    by_cases h125 : byteAt b i = 125
    · simp only [h125, show ((125 : UInt8) == 125) = true from rfl, ite_true] at h
      rw [exprN_close _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125])]
      split at h; cases h
      cases pl
      · simp at h
      · exact fun hpl => hP.elim
      · exact fun hpl => hP.elim
      · by_cases hk : ik = 3
        · subst hk; obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
          exact fun _ => ⟨hI, hP⟩
        · simp [hk] at h
      · exact fun hpl => hP.elim
      · exact fun hpl => hP.elim
    simp only [show (byteAt b i == 125) = false by simpa using h125, Bool.false_eq_true,
      ite_false] at h
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = false := by simpa using hw
      subst hw'
      simp only [bw, Bool.false_eq_true, ite_false]
      rw [exprN_congr _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)]
      exact exprLine_link (i + 1) true ik idx pl f r e h hI hP
    simp only [show (byteAt b i == 44) = false by simpa using h44, Bool.false_eq_true,
      ite_false] at h
    by_cases h34 : byteAt b i = 34
    · simp only [h34, show ((34 : UInt8) == 34) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = true := by simpa using hw
      subst hw'
      split at h; cases h; rename_i hk
      split at h; cases h; rename_i hv
      have hk' : keyEnd b (i + 1) ≠ 0 := by simpa using hk
      have hv' : valueAt b i (keyEnd b (i + 1)) ≠ i := by simpa using hv
      have hm := nm_key b h64 hsize i hi h34 hk' hv'
      have hR := rd_item b h64 hsize i hi hk' hv' h34
      simp only [bw, ite_true]
      rw [exprN_key _ _ _ _ (by rw [hm]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hm]; exact (by decide : (2 : Word) ≠ 1))]
      simp only [hm]
      generalize valueAt b i (keyEnd b (i + 1)) = v at h hR
      generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K at h
      cases K
      all_goals (try dsimp only at h)
      all_goals (try (cases h; done))
      all_goals simp (config := {decide := true}) only [exVN, ↓reduceIte, Obj.none,
        UInt64.not_lt_zero, Fld.none, ne_eq, false_implies]
      case kIn | kIl | kIe =>
        split at h; cases h
        split at h; cases h; rename_i hne
        split at h
        · rename_i hie
          have hsl : L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64 = (numEnd b v).toUInt64 := by
            rw [slotNatN_link b h64 hsize, ite_eq_right (by simpa using hne), ite_eq_left hie]
          rw [hsl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          simp only [fldPut, ↓reduceIte]
          exact exprLine_link (numEnd b v) false _ _ _ _ r e h hR (ePlR_idx b _ _ _ hP)
        · cases h
      case kBvar | kSort =>
        split at h; cases h
        split at h; cases h; rename_i hne
        split at h
        · rename_i hie
          have hsl : L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64 = (numEnd b v).toUInt64 := by
            rw [slotNatN_link b h64 hsize, ite_eq_right (by simpa using hne), ite_eq_left hie]
          rw [hsl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          simp (config := {decide := true}) only [fldPut, ↓reduceIte]
          exact exprLine_link (numEnd b v) false _ _ _ _ r e h hI ⟨rfl, hR⟩
        · cases h
      case kApp | kLam | kForallE | kLetE | kConst | kProj =>
        split at h; cases h
        split at h; cases h; rename_i r' e' hr
        split at h
        · rename_i hie
          have hp := obj_link b h64 hsize _ v r' e' (by
            first
              | exact .inl ⟨rfl, hr⟩ | exact .inr (.inl ⟨rfl, hr⟩)
              | exact .inr (.inr (.inl ⟨rfl, hr⟩)) | exact .inr (.inr (.inr (.inl ⟨rfl, hr⟩)))
              | exact .inr (.inr (.inr (.inr (.inl ⟨rfl, hr⟩))))
              | exact .inr (.inr (.inr (.inr (.inr ⟨rfl, hr⟩)))))
          rw [objFld_e, hp.1, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact exprLine_link e' false _ _ _ _ r e h hI (ePlR_obj b _ _ _ _ hp.2)
        · cases h
      case kNatVal =>
        split at h; cases h
        split at h; cases h; rename_i n e' hr
        split at h
        · rename_i hie
          obtain ⟨hq, hn, hnv⟩ := natVal_link b h64 hsize v n e' hr
          rw [hq, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          simp (config := {decide := true}) only [fldPut, ↓reduceIte]
          exact exprLine_link e' false _ _ _ _ r e h hI ⟨rfl, hn, hnv⟩
        · cases h
      case kStrVal =>
        split at h; cases h
        split at h; cases h; rename_i s' e' hr
        split at h
        · rename_i hie
          obtain ⟨hq, hs⟩ := strVal_link b h64 hsize v s' e' hr
          rw [hq, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          simp (config := {decide := true}) only [fldPut, ↓reduceIte]
          exact exprLine_link e' false _ _ _ _ r e h hI ⟨rfl, hs⟩
        · cases h
    · simp only [show (byteAt b i == 34) = false by simpa using h34, Bool.false_eq_true,
        ite_false] at h
      cases h
  · rw [dite_eq_right hi] at h; cases h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹i < numEnd b _›; omega)
    | (have := USize.lt_iff_toNat_lt.mp ‹i < _›; omega)

/-- `rec_expr_loop(i)`, from the line's first member: what `front_line` calls. -/
theorem exprLineN_link (i : USize) (r : LineRec) (e : USize)
    (h : scanLineLoop b i true 0 0 .absent = .ok r e) :
    (exprLineN b.data i.toUInt64).pl ≠ 0 → ERecR b r (exprLineN b.data i.toUInt64) :=
  exprLine_link b h64 hsize i true 0 0 .absent Fld.none r e h itemR_zero trivial

end line

/-- info: 'ConAgua.Front.FieldsLink.exprLineN_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exprLineN_link
/-- info: 'L.Front.Fields.recExprLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms L.Front.Fields.recExprLoop_spec

end ConAgua.Front.FieldsLink
