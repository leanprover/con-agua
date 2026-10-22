import ConAgua.Front.IndFieldsLink

/-!
# The fields pass of an `inductive` line, linked to con-leche: the record kinds

The instances of `IndFieldsLink.lean`'s generic loops: each record kind's relation (`RuleLR`,
`RecLR`, `CtLR`, `TyLR`, `BlkLR`), its loop instance and its list, bottom up, ending in
`indFields_link`.
-/


open L.Arena
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open ConAgua.Front.FieldsLink
open L.Front.Fields (rdNatN NONE rdLoopN listN itemsN)
open L.Front (lsCntN)
open L.Scan.Utf8 (byteW)
open L.Scan.Member (nextMemberN)
open L.Scan.Leaves (numEndN skipDigitsN keyEndN)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace L.Front.Ind

/-! ## The record kinds -/

set_option hygiene false in
/-- A key's arm of an `IObjLoop`, entering it: the key's `seen` check passed. -/
macro "iloop_key " f:ident : tactic => `(tactic| (
  intro i seen st m d e e' m' h hc hk hv hvle hok hR hmem hlt
  rw [$f:ident, dif_pos h] at hok
  simp [uget_byteAt _ i h, hc, isWs, hk, hv] at hok
  have hiv := valueAt_gt b h64 hsize i h hk hv
  generalize valueAt b i (keyEnd b (i + 1)) = v at hok hvle hmem hiv ⊢
  generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K at hok hmem ⊢
  cases K
  all_goals (try (simp at hok; done))))

set_option hygiene false in
/-- A number key's arm: `hne`, `hie` and the loop's `ok` after it. -/
macro "ikey_num" : tactic => `(tactic| (
  simp only at hok
  split at hok
  rotate_left
  · cases hok
  split at hok
  · cases hok
  rename_i hne
  split at hok
  rotate_left
  · cases hok
  rename_i hie))

section kinds
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- The rule record read so far. -/
def RuleLR (m₁ : Mem) (q : Word) (seen : UInt32) (st : Nat × Nat × Nat) (m : Mem) : Prop :=
  RecInv IFL 3 q m₁ m ∧ topN m IFL = topN m₁ IFL ∧ SeenR seen 1 (NumW (wd m IFL (q.toNat + 0)) st.1) ∧
    SeenR seen 2 (NumW (wd m IFL (q.toNat + 1)) st.2.1) ∧
    SeenR seen 4 (NumW (wd m IFL (q.toNat + 2)) st.2.2)

omit h64 hsize in
theorem fldPutW_rule (m : Mem) (q s x : Word) : fldPutW m 3 q s x = m.set64 IFL (q + s) x := by
  simp [fldPutW]

theorem rule_loop (m₁ : Mem) (q : Word) :
    IObjLoop b (fun i w seen (st : Nat × Nat × Nat) => scanRuleLoop b i w seen st.1 st.2.1 st.2.2)
      3 q (RuleLR m₁ q) (fun d m => (RecInv IFL 3 q m₁ m ∧ topN m IFL = topN m₁ IFL) ∧
        RuleF m q.toNat d) := by
  constructor
  · dloop_stop scanRuleLoop
  · dloop_ws scanRuleLoop
  · dloop_close scanRuleLoop
    obtain ⟨hI, ht, h1, h2, h3⟩ := hR
    exact ⟨⟨hI, ht⟩, seenR_close h1 hM (by decide) (by decide), seenR_close h2 hM (by decide) (by decide),
      seenR_close h3 hM (by decide) (by decide)⟩
  · dloop_comma scanRuleLoop
  · dloop_quote scanRuleLoop
  · iloop_key scanRuleLoop
    all_goals obtain ⟨hI, ht, h1, h2, h3⟩ := hR
    case kCtor =>
      rw [show UInt64.ofNat Key.kCtor.ctorIdx = (10 : Word) from rfl] at hmem
      ikey_num
      obtain ⟨he, x, rfl, hx⟩ := num_arm b h64 hsize m m' 3 q 10 0 0 i v e' rfl hne hie hvle hmem
      subst he
      rw [fldPutW_rule]
      obtain ⟨p1, p2, p3, -, p5⟩ := slot_put IFL (.inr rfl) 3 (by decide) q 0 x m₁ m hI (by decide)
      refine ⟨numEnd b v, _, (readNatAt b v (numEnd b v), st.2.1, st.2.2), rfl, hok,
        p1, by rw [p5, ht], .inl (by rw [show q.toNat + 0 = q.toNat + (0 : Word).toNat from rfl, p2]; exact hx),
        seenR_or h2 (by decide) (by rw [p3 _ (by simp)]; exact id),
        seenR_or h3 (by decide) (by rw [p3 _ (by simp)]; exact id)⟩
    case kNfields =>
      rw [show UInt64.ofNat Key.kNfields.ctorIdx = (36 : Word) from rfl] at hmem
      ikey_num
      obtain ⟨he, x, rfl, hx⟩ := num_arm b h64 hsize m m' 3 q 36 1 0 i v e' rfl hne hie hvle hmem
      subst he
      rw [fldPutW_rule]
      obtain ⟨p1, p2, p3, -, p5⟩ := slot_put IFL (.inr rfl) 3 (by decide) q 1 x m₁ m hI (by decide)
      refine ⟨numEnd b v, _, (st.1, readNatAt b v (numEnd b v), st.2.2), rfl, hok,
        p1, by rw [p5, ht], seenR_or h1 (by decide) (by rw [p3 _ (by simp)]; exact id),
        .inl (by rw [show q.toNat + 1 = q.toNat + (1 : Word).toNat from rfl, p2]; exact hx),
        seenR_or h3 (by decide) (by rw [p3 _ (by simp)]; exact id)⟩
    case kRhs =>
      rw [show UInt64.ofNat Key.kRhs.ctorIdx = (52 : Word) from rfl] at hmem
      ikey_num
      obtain ⟨he, x, rfl, hx⟩ := num_arm b h64 hsize m m' 3 q 52 2 0 i v e' rfl hne hie hvle hmem
      subst he
      rw [fldPutW_rule]
      obtain ⟨p1, p2, p3, -, p5⟩ := slot_put IFL (.inr rfl) 3 (by decide) q 2 x m₁ m hI (by decide)
      refine ⟨numEnd b v, _, (st.1, st.2.1, readNatAt b v (numEnd b v)), rfl, hok,
        p1, by rw [p5, ht], seenR_or h1 (by decide) (by rw [p3 _ (by simp)]; exact id),
        seenR_or h2 (by decide) (by rw [p3 _ (by simp)]; exact id),
        .inl (by rw [show q.toNat + 2 = q.toNat + (2 : Word).toNat from rfl, p2]; exact hx)⟩
  · dloop_other scanRuleLoop

/-- **One record of a list**: `ind_obj` on the record at `q`, from its loop instance. -/
theorem item_gen {σ α : Type} (F : USize → Bool → UInt32 → σ → ScanRes α) (kind : Word) (A : ArrId)
    (sz : Nat) (Fn : Mem → Word → α → Mem → Prop) (R : Mem → Word → UInt32 → σ → Mem → Prop)
    (st0 : σ)
    (S : USize → ScanRes α) (hS : ∀ i x e, S i = .ok x e → F (i + 1) true 0 st0 = .ok x e)
    (H : ∀ m₁ q, IObjLoop b F kind q (R m₁ q) (Fn m₁ q))
    (h0 : ∀ m₁ q, RecInv A sz q m₁ m₁ → R m₁ q 0 st0 m₁)
    (i : USize) (m₁ : Mem) (q : Word) (x : α) (e : USize) (e₂ : Word) (m₂ : Mem)
    (hS' : S i = .ok x e) (hI : RecInv A sz q m₁ m₁)
    (hob : objW b.data m₁ i.toUInt64 kind q = some (e₂, m₂)) :
    e₂ = e.toUInt64 ∧ Fn m₁ q x m₂ := by
  rw [objW_eq, ← succ_toUInt64 b h64 hsize, show (1 : Word) = bw true from rfl] at hob
  exact iobj_link b h64 hsize F kind q (R m₁ q) _ (H m₁ q) (i + 1) true 0 st0 m₁ x e
    e₂ m₂ (hS i x e hS') (h0 m₁ q hI) hob

omit h64 hsize in
/-- A freshly allocated record is being read. -/
theorem recInv_alloc (A : ArrId) (hA : A = IFR ∨ A = IFL) (sz : Nat) (n q : Word) (m m₁ : Mem)
    (hR : Room m) (hn : n.toNat = sz) (hal : allocW m A n = some (q, m₁)) : RecInv A sz q m₁ m₁ := by
  obtain ⟨a1, a2, a3, -, -, -, -⟩ := allocW_facts m m₁ A hA n q hR hal
  exact ⟨IGrow.refl _ _ _ _, a3, by omega, by omega⟩

set_option hygiene false in
macro "ilist_shape " G:ident : tactic => `(tactic| (
  constructor
  · intro i acc w l e h; rw [$G:ident, dif_neg h]; simp
  · intro i acc w h hws; rw [$G:ident, dif_pos h]; simp only [uget_byteAt _ i h, hws, if_true]
  · intro i acc w l e h hc hok
    rw [$G:ident, dif_pos h] at hok
    simp [uget_byteAt _ i h, hc, isWs] at hok
    split at hok
    · cases hok
    · simp only [ScanRes.ok.injEq] at hok; obtain ⟨rfl, rfl⟩ := hok; exact ⟨rfl, rfl⟩
  · intro i acc w l e h hc hok
    rw [$G:ident, dif_pos h] at hok
    simp [uget_byteAt _ i h, hc, isWs] at hok
    split at hok
    · cases hok
    · exact hok
  · intro i acc w l e h hc hok
    rw [$G:ident, dif_pos h] at hok
    simp [uget_byteAt _ i h, hc, isWs] at hok
    split at hok
    · cases hok
    split at hok
    · cases hok
    rename_i x e₁ hx
    split at hok
    · rename_i hie; exact ⟨x, e₁, hx, hie, hok⟩
    · cases hok
  · intro i acc w l e h hws h1 h2 h3 hok
    rw [$G:ident, dif_pos h] at hok
    simp [uget_byteAt _ i h, hws, h1, h2, h3] at hok))

theorem ruleList_shape : IListLoop b (scanRuleListLoop b) (scanRule b) := by
  ilist_shape scanRuleListLoop

omit h64 hsize in
/-- Stability of a rule record under growth that leaves it alone. -/
theorem ruleF_stab (t : Nat) (x : RuleRec) (m m' : Mem) (x0 x1 : Nat) (h : RuleF m t x)
    (h1 : 1 ≤ t) (h2 : t + 3 ≤ topN m IFL + 1) (hg : IGrow m m' IFL x0 x1) (h3 : t + 3 ≤ x0) :
    RuleF m' t x := by
  obtain ⟨r1, r2, r3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [hg.wd_keep IFL (.inr rfl) t (by omega) (by omega) (fun _ => by omega)]; exact r1
  · rw [hg.wd_keep IFL (.inr rfl) (t + 1) (by omega) (by omega) (fun _ => by omega)]; exact r2
  · rw [hg.wd_keep IFL (.inr rfl) (t + 2) (by omega) (by omega) (fun _ => by omega)]; exact r3

/-- The rules of a recursor: a run of rule records in `IFL`. -/
theorem rules_link (v : USize) (m : Mem) (l : List RuleRec) (e : USize) (r : Word × Word × Word)
    (m' : Mem) (h : scanRules b v = .ok l e) (hR : Room m)
    (hm : listW b.data m v.toUInt64 3 = some (r, m')) :
    r.2.2 = e.toUInt64 ∧ r.2.1.toNat = l.length ∧
      RunR (fun t x m => RuleF m t x) IFL 3 m' r.1.toNat l ∧ Grow m m' ∧ Room m' ∧
      r.1.toNat = topN m IFL + 1 ∧ r.1.toNat + 3 * l.length = topN m' IFL + 1 := by
  refine ilistW_link b h64 hsize (scanRuleListLoop b) (scanRule b) (ruleList_shape b h64 hsize)
    (scanRules b) (fun v l e h => ?_) 3 IFL (.inr rfl) 3 (by decide) rfl
    (fun m n => by simp [fldAllocW]) (fun t x m => RuleF m t x) ruleF_stab ?_ v m l e r m' h hR hm
  · unfold scanRules at h; split at h
    · rename_i h91; exact ⟨by simpa using h91, h⟩
    · cases h
  · intro i m m₁ q x e e₂ m₂ hi h123 hS hR hal hob
    rw [show flagsW m₁ 3 q = m₁ by simp [flagsW]] at hob
    have hI := recInv_alloc IFL (.inr rfl) 3 _ q m m₁ hR rfl hal
    obtain ⟨t1, ⟨t2, t3⟩, t4⟩ := item_gen b h64 hsize
      (fun i w seen (st : Nat × Nat × Nat) => scanRuleLoop b i w seen st.1 st.2.1 st.2.2) 3 IFL 3
      (fun m₁ q d m => (RecInv IFL 3 q m₁ m ∧ topN m IFL = topN m₁ IFL) ∧ RuleF m q.toNat d) RuleLR
      ((0 : Nat), (0 : Nat), (0 : Nat)) (scanRule b) (fun i x e h => by
        unfold scanRule at h; split at h
        · exact h
        · cases h) (rule_loop b h64 hsize)
      (fun m₁ q hI => ⟨hI, rfl, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _⟩)
      i m₁ q x e e₂ m₂ hS hI hob
    exact ⟨t1, t4, t2.1, t2.2.1, t3⟩

end kinds

end L.Front.Ind
