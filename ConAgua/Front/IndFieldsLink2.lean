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
  RecInv IFL 3 q m₁ m ∧ topN m IFL = topN m₁ IFL ∧ m.arr64 IFR = m₁.arr64 IFR ∧ SeenR seen 1 (NumW (wd m IFL (q.toNat + 0)) st.1) ∧
    SeenR seen 2 (NumW (wd m IFL (q.toNat + 1)) st.2.1) ∧
    SeenR seen 4 (NumW (wd m IFL (q.toNat + 2)) st.2.2)

omit h64 hsize in
theorem fldPutW_rule (m : Mem) (q s x : Word) : fldPutW m 3 q s x = m.set64 IFL (q + s) x := by
  simp [fldPutW]

theorem rule_loop (m₁ : Mem) (q : Word) :
    IObjLoop b (fun i w seen (st : Nat × Nat × Nat) => scanRuleLoop b i w seen st.1 st.2.1 st.2.2)
      3 q (RuleLR m₁ q) (fun d m => (RecInv IFL 3 q m₁ m ∧ topN m IFL = topN m₁ IFL ∧
        m.arr64 IFR = m₁.arr64 IFR) ∧ RuleF m q.toNat d) := by
  constructor
  · dloop_stop scanRuleLoop
  · dloop_ws scanRuleLoop
  · dloop_close scanRuleLoop
    obtain ⟨hI, ht, hfr, h1, h2, h3⟩ := hR
    exact ⟨⟨hI, ht, hfr⟩, seenR_close h1 hM (by decide) (by decide), seenR_close h2 hM (by decide) (by decide),
      seenR_close h3 hM (by decide) (by decide)⟩
  · dloop_comma scanRuleLoop
  · dloop_quote scanRuleLoop
  · iloop_key scanRuleLoop
    all_goals obtain ⟨hI, ht, hfr, h1, h2, h3⟩ := hR
    case kCtor =>
      rw [show UInt64.ofNat Key.kCtor.ctorIdx = (10 : Word) from rfl] at hmem
      ikey_num
      obtain ⟨he, x, rfl, hx⟩ := num_arm b h64 hsize m m' 3 q 10 0 0 i v e' rfl hne hie hvle hmem
      subst he
      rw [fldPutW_rule]
      obtain ⟨p1, p2, p3, -, p5⟩ := slot_put IFL (.inr rfl) 3 (by decide) q 0 x m₁ m hI (by decide)
      refine ⟨numEnd b v, _, (readNatAt b v (numEnd b v), st.2.1, st.2.2), rfl, hok,
        p1, by rw [p5, ht], by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hfr], .inl (by rw [show q.toNat + 0 = q.toNat + (0 : Word).toNat from rfl, p2]; exact hx),
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
        p1, by rw [p5, ht], by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hfr], seenR_or h1 (by decide) (by rw [p3 _ (by simp)]; exact id),
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
        p1, by rw [p5, ht], by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hfr], seenR_or h1 (by decide) (by rw [p3 _ (by simp)]; exact id),
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
      r.1.toNat = topN m IFL + 1 ∧ r.1.toNat + 3 * l.length = topN m' IFL + 1 ∧
      m'.arr64 IFR = m.arr64 IFR := by
  refine ilistW_link b h64 hsize (scanRuleListLoop b) (scanRule b) (ruleList_shape b h64 hsize)
    (scanRules b) (fun v l e h => ?_) 3 IFL (.inr rfl) 3 (by decide) rfl
    (fun m n => by simp [fldAllocW]) (fun t x m => RuleF m t x) ruleF_stab
    (fun m m' => m'.arr64 IFR = m.arr64 IFR) (fun _ => rfl) (fun _ _ _ h1 h2 => h2.trans h1)
    (fun m m₁ n q hal => allocW_facts' m m₁ IFL n q hal IFR (by decide)) ?_ v m l e r m' h hR hm
  · unfold scanRules at h; split at h
    · rename_i h91; exact ⟨by simpa using h91, h⟩
    · cases h
  · intro i m m₁ q x e e₂ m₂ hi h123 hS hR hal hob
    rw [show flagsW m₁ 3 q = m₁ by simp [flagsW]] at hob
    have hI := recInv_alloc IFL (.inr rfl) 3 _ q m m₁ hR rfl hal
    obtain ⟨t1, ⟨t2, t3, t5⟩, t4⟩ := item_gen b h64 hsize
      (fun i w seen (st : Nat × Nat × Nat) => scanRuleLoop b i w seen st.1 st.2.1 st.2.2) 3 IFL 3
      (fun m₁ q d m => (RecInv IFL 3 q m₁ m ∧ topN m IFL = topN m₁ IFL ∧
        m.arr64 IFR = m₁.arr64 IFR) ∧ RuleF m q.toNat d) RuleLR
      ((0 : Nat), (0 : Nat), (0 : Nat)) (scanRule b) (fun i x e h => by
        unfold scanRule at h; split at h
        · exact h
        · cases h) (rule_loop b h64 hsize)
      (fun m₁ q hI => ⟨hI, rfl, rfl, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _⟩)
      i m₁ q x e e₂ m₂ hS hI hob
    exact ⟨t1, t4, t2.1, t2.2.1, t3, t5⟩

set_option hygiene false in
/-- A value read by a `ScanRes` scanner: `xv`, `ev`, `hx`, `hie` and the loop's `ok` after it. -/
macro "ikey_res" : tactic => `(tactic| (
  simp only at hok
  split at hok
  rotate_left
  · cases hok
  split at hok
  · cases hok
  rename_i xv ev hx
  split at hok
  rotate_left
  · cases hok
  rename_i hie))


set_option hygiene false in
/-- Close the relation's fields after a write: the new field by `hx` (or `rfl`), the others
carried. -/
macro "rfields" : tactic => `(tactic| (
  repeat' (first
    | exact .inl hx
    | exact .inl rfl
    | exact seenR_or ‹_› (by decide) id
    | refine ⟨?_, ?_⟩)))

set_option hygiene false in
/-- A write of `xw` to slot `s` of an `IFR` record of size `sz`, the loop going on at `en` with the
state `st'`. -/
macro "rput " s:term "," sz:term "," xw:term "," st':term "," en:term : tactic => `(tactic| (
  rw [fldPutW_R _ _ _ _ _ (by decide)]
  obtain ⟨p1, -, -, p4, p5⟩ := slot_put IFR (.inl rfl) $sz (by decide) q $s $xw m₁ m hI (by decide)
  have e1 := slot_view IFR (.inl rfl) $sz (by decide) q $s $xw m₁ m hI (by decide)
  have p6 := runR_rule_eq (Mem.arr64_set64_ne m IFR IFL (q + $s) $xw (by decide))
  refine ⟨$en, _, $st', rfl, hok, p1, by rw [p5, ht], ?_⟩
  simp (config := {decide := true}) only [e1, p5, p6, ↓reduceIte]
  rfields))

set_option hygiene false in
/-- A number key of an `IFR` record (size `sz`, kind `kd`): key `kn` into slot `s`, the state
after `st'`. -/
macro "rnum_arm " kn:term "," kd:term "," s:term "," sz:term "," st':term : tactic => `(tactic| (
  ikey_num
  obtain ⟨he, x, rfl, hx⟩ := num_arm b h64 hsize m m' $kd q $kn $s 0 i v e' rfl hne hie hvle hmem
  subst he
  rput $s, $sz, x, $st', numEnd b v))

set_option hygiene false in
/-- A Boolean key into slot `s`. -/
macro "rbool_arm " kn:term "," kd:term "," s:term "," sz:term "," st':term : tactic => `(tactic| (
  ikey_res
  obtain ⟨he, rfl⟩ := bool_arm b h64 hsize m m' $kd q _ $kn $s 0 v xv ev e' rfl hx hmem
  subst he
  rput $s, $sz, (if xv then 1 else 0), $st', ev))

omit h64 hsize in
theorem fldPutW_R (m : Mem) (k q s x : Word) (hk : k ≠ 3) : fldPutW m k q s x = m.set64 IFR (q + s) x := by
  simp [fldPutW, hk]

omit h64 hsize in
/-- The record's slots after a write to slot `s`. -/
theorem slot_view (A : ArrId) (hA : A = IFR ∨ A = IFL) (sz : Nat) (hsz : sz ≤ 16) (q s x : Word)
    (m₁ m : Mem) (hI : RecInv A sz q m₁ m) (hs : s.toNat < sz) (j : Nat) :
    wd (m.set64 A (q + s) x) A (q.toNat + j) = if s.toNat = j then x else wd m A (q.toNat + j) := by
  obtain ⟨-, p2, p3, -, -⟩ := slot_put A hA sz hsz q s x m₁ m hI hs
  split
  · rename_i h; subst h; exact p2
  · exact p3 _ (by omega)

omit h64 hsize in
theorem runR_rule_eq {m m' : Mem} (h : m'.arr64 IFL = m.arr64 IFL) (o : Nat) (l : List RuleRec) :
    RunR (fun t x m => RuleF m t x) IFL 3 m' o l = RunR (fun t x m => RuleF m t x) IFL 3 m o l := by
  simp only [RunR, RuleF, topN, wd, h]

/-- con-leche's recursor loop state. -/
structure RecSt where
  isUns : Bool
  kf : Bool
  lps : List Nat
  nm : Nat
  nIdx : Nat
  nMin : Nat
  nMot : Nat
  nP : Nat
  rules : List RuleRec
  ty : Nat

/-- The recursor record read so far. -/
def RecLR (m₁ : Mem) (q : Word) (seen : UInt32) (st : RecSt) (m : Mem) : Prop :=
  RecInv IFR 11 q m₁ m ∧ topN m IFR = topN m₁ IFR ∧
    SeenR seen 16 (NumW (wd m IFR (q.toNat + 0)) st.nm) ∧
    SeenR seen 8 (ItemsR (listN b.data (wd m IFR (q.toNat + 1))) st.lps) ∧
    SeenR seen 1024 (NumW (wd m IFR (q.toNat + 2)) st.ty) ∧
    SeenR seen 4 (BoolW (wd m IFR (q.toNat + 4)) st.kf) ∧
    SeenR seen 32 (NumW (wd m IFR (q.toNat + 5)) st.nIdx) ∧
    SeenR seen 64 (NumW (wd m IFR (q.toNat + 6)) st.nMin) ∧
    SeenR seen 128 (NumW (wd m IFR (q.toNat + 7)) st.nMot) ∧
    SeenR seen 256 (NumW (wd m IFR (q.toNat + 8)) st.nP) ∧
    SeenR seen 512 ((wd m IFR (q.toNat + 10)).toNat = st.rules.length ∧
      RunR (fun t x m => RuleF m t x) IFL 3 m (wd m IFR (q.toNat + 9)).toNat st.rules)

set_option maxHeartbeats 2000000 in
theorem rec_loop (m₁ : Mem) (q : Word) :
    IObjLoop b (fun i w seen (st : RecSt) => scanIndRecLoop b i w seen st.isUns st.kf st.lps st.nm
        st.nIdx st.nMin st.nMot st.nP st.rules st.ty) 2 q (RecLR b m₁ q)
      (fun d m => (RecInv IFR 11 q m₁ m ∧ topN m IFR = topN m₁ IFR) ∧ RecF b m q.toNat d) := by
  constructor
  · dloop_stop scanIndRecLoop
  · dloop_ws scanIndRecLoop
  · dloop_close scanIndRecLoop
    obtain ⟨hI, ht, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hR
    have c9 := seenR_close h9 hM (by decide) (by decide)
    exact ⟨⟨hI, ht⟩, ⟨seenR_close h1 hM (by decide) (by decide), seenR_close h2 hM (by decide) (by decide),
      seenR_close h3 hM (by decide) (by decide)⟩, seenR_close h4 hM (by decide) (by decide),
      seenR_close h5 hM (by decide) (by decide), seenR_close h6 hM (by decide) (by decide),
      seenR_close h7 hM (by decide) (by decide), seenR_close h8 hM (by decide) (by decide),
      c9.1, c9.2.1, c9.2.2.1, c9.2.2.2⟩
  · dloop_comma scanIndRecLoop
  · dloop_quote scanIndRecLoop
  · iloop_key scanIndRecLoop
    all_goals obtain ⟨hI, ht, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl] at hmem
      rnum_arm 34, 2, 0, 11, { st with nm := readNatAt b v (numEnd b v) }
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl] at hmem
      rnum_arm 61, 2, 2, 11, { st with ty := readNatAt b v (numEnd b v) }
    case kNumIndices =>
      rw [show UInt64.ofNat Key.kNumIndices.ctorIdx = (40 : Word) from rfl] at hmem
      rnum_arm 40, 2, 5, 11, { st with nIdx := readNatAt b v (numEnd b v) }
    case kNumMinors =>
      rw [show UInt64.ofNat Key.kNumMinors.ctorIdx = (41 : Word) from rfl] at hmem
      rnum_arm 41, 2, 6, 11, { st with nMin := readNatAt b v (numEnd b v) }
    case kNumMotives =>
      rw [show UInt64.ofNat Key.kNumMotives.ctorIdx = (42 : Word) from rfl] at hmem
      rnum_arm 42, 2, 7, 11, { st with nMot := readNatAt b v (numEnd b v) }
    case kNumParams =>
      rw [show UInt64.ofNat Key.kNumParams.ctorIdx = (44 : Word) from rfl] at hmem
      rnum_arm 44, 2, 8, 11, { st with nP := readNatAt b v (numEnd b v) }
    case kK =>
      rw [show UInt64.ofNat Key.kK.ctorIdx = (27 : Word) from rfl] at hmem
      rbool_arm 27, 2, 4, 11, { st with kf := xv }
    case kIsUnsafe =>
      rw [show UInt64.ofNat Key.kIsUnsafe.ctorIdx = (26 : Word) from rfl] at hmem
      rbool_arm 26, 2, 3, 11, { st with isUns := xv }
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨he, rfl, hx⟩ := lps_arm b h64 hsize m m' 2 q _ 31 1 0 v xv ev e' rfl hx hmem
      subst he
      rput 1, 11, v.toUInt64, { st with lps := xv }, ev
    case kAll =>
      rw [show UInt64.ofNat Key.kAll.ctorIdx = (1 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨he, rfl⟩ := all_arm b h64 hsize m m' 2 q _ 1 0 0 v xv ev e' rfl hx hmem
      subst he
      refine ⟨ev, _, st, rfl, hok, hI, ht, ?_⟩
      rfields
    case kRules =>
      rw [show UInt64.ofNat Key.kRules.ctorIdx = (53 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨o, c, mL, hl, rfl⟩ := list_arm b h64 hsize m m' 2 q 53 9 3 i v e' rfl hiv hmem
      obtain ⟨l1, l2, l3, l4, l5, -, -, l8⟩ :=
        rules_link b h64 hsize v m xv ev (o, c, e') mL hx hI.2.1 hl
      simp only at l1 l2 l3
      subst l1
      rw [fldPutW_R _ _ _ _ _ (by decide), fldPutW_R _ _ _ _ _ (by decide),
        show (9 : Word) + 1 = 10 from rfl]
      have hI1 := hI.grow l4 l5
      have hw : ∀ j, wd mL IFR j = wd m IFR j := fun j => by simp only [wd, l8]
      have ht1 : topN mL IFR = topN m IFR := congrArg UInt64.toNat (hw 0)
      obtain ⟨p1, -, -, p4, p5⟩ := slot_put IFR (.inl rfl) 11 (by decide) q 9 o m₁ mL hI1 (by decide)
      have e1 := slot_view IFR (.inl rfl) 11 (by decide) q 9 o m₁ mL hI1 (by decide)
      obtain ⟨p1', -, -, p4', p5'⟩ :=
        slot_put IFR (.inl rfl) 11 (by decide) q 10 c m₁ _ p1 (by decide)
      have e1' := slot_view IFR (.inl rfl) 11 (by decide) q 10 c m₁ _ p1 (by decide)
      have p6 := runR_rule_eq (Mem.arr64_set64_ne (mL.set64 IFR (q + 9) o) IFR IFL (q + 10) c
        (by decide))
      have p7 := runR_rule_eq (Mem.arr64_set64_ne mL IFR IFL (q + 9) o (by decide))
      refine ⟨ev, _, { st with rules := xv }, rfl, hok, p1', by rw [p5', p5, ht1, ht], ?_⟩
      have hx : c.toNat = xv.length ∧ RunR (fun t x m => RuleF m t x) IFL 3 mL o.toNat xv := ⟨l2, l3⟩
      simp (config := {decide := true}) only [e1', e1, p6, p7, hw, ↓reduceIte]
      rfields
  · dloop_other scanIndRecLoop

omit h64 hsize in
/-- An `IFL` run of rules is kept by growth that writes `IFL` only above its top. -/
theorem rules_stab (o : Nat) (l : List RuleRec) (m m' : Mem) (xa : ArrId) (x0 x1 : Nat)
    (hg : IGrow m m' xa x0 x1) (hxa : xa = IFR)
    (h : RunR (fun t x m => RuleF m t x) IFL 3 m o l) :
    RunR (fun t x m => RuleF m t x) IFL 3 m' o l := by
  subst hxa
  obtain ⟨r1, r2, r3⟩ := h
  have htl := hg.top IFL (.inr rfl)
  refine ⟨r1, by omega, fun j hj => ?_⟩
  have hb := run_bound _ _ _ _ _ hj r2
  obtain ⟨u1, u2, u3⟩ := r3 j hj
  have hk : ∀ k, 1 ≤ k → k ≤ topN m IFL → wd m' IFL k = wd m IFL k := fun k h1 h2 =>
    hg.wd_keep IFL (.inr rfl) k h1 h2 (fun h => absurd h (by decide))
  refine ⟨?_, ?_, ?_⟩
  · rw [hk _ (by omega) (by omega)]; exact u1
  · rw [hk _ (by omega) (by omega)]; exact u2
  · rw [hk _ (by omega) (by omega)]; exact u3

omit h64 hsize in
/-- An `IFR` record's words are kept by growth that leaves them alone. -/
theorem irec_keep (t sz : Nat) (m m' : Mem) (x0 x1 : Nat) (hg : IGrow m m' IFR x0 x1) (h1 : 1 ≤ t)
    (h2 : t + sz ≤ topN m IFR + 1) (hd : t + sz ≤ x0 ∨ x1 ≤ t) (j : Nat) (hj : j < sz) :
    wd m' IFR (t + j) = wd m IFR (t + j) :=
  hg.keep IFR (.inl rfl) _ (by omega) (by omega) (by rintro ⟨-, h5, h6⟩; omega)

omit h64 hsize in
theorem recF_stab (t : Nat) (x : IndRecRec) (m m' : Mem) (x0 x1 : Nat) (h : RecF b m t x)
    (h1 : 1 ≤ t) (h2 : t + 11 ≤ topN m IFR + 1) (hg : IGrow m m' IFR x0 x1)
    (hd : t + 11 ≤ x0 ∨ x1 ≤ t) : RecF b m' t x := by
  have hw := irec_keep t 11 m m' x0 x1 hg h1 h2 hd
  obtain ⟨⟨c1, c2, c3⟩, k, i5, i6, i7, i8, r10, r9, rb, rr⟩ := h
  have hrun := rules_stab _ _ m m' IFR x0 x1 hg rfl ⟨r9, rb, rr⟩
  rw [← hw 9 (by decide)] at hrun
  obtain ⟨_, rb', rr'⟩ := hrun
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rb', rr'⟩
  · rw [show t = t + 0 from rfl, hw 0 (by decide)]; exact c1
  · rw [hw 1 (by decide)]; exact c2
  · rw [hw 2 (by decide)]; exact c3
  · rw [hw 4 (by decide)]; exact k
  · rw [hw 5 (by decide)]; exact i5
  · rw [hw 6 (by decide)]; exact i6
  · rw [hw 7 (by decide)]; exact i7
  · rw [hw 8 (by decide)]; exact i8
  · rw [hw 10 (by decide)]; exact r10
  · rw [hw 9 (by decide)]; exact r9

end kinds

end L.Front.Ind
