import ConAgua.Front.IndFieldsLink
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

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


namespace L.Front.Ind

/-! ## The record kinds -/

set_option hygiene false in
/-- A key's arm of an `IObjLoop`, entering it: the key's `seen` check passed. -/
macro "iloop_key " f:ident : tactic => `(tactic| (
  intro i seen st m d e e' m' h hc hk hv hvle hok hR hmem hlt
  rw [$f:ident, dite_eq_left h] at hok
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
theorem item_gen {σ α : Type} (F : USize → Bool → UInt32 → σ → ScanRes α) (kind : Word) (_A : ArrId)
    (_sz : Nat) (Fn : Mem → Word → α → Mem → Prop) (R : Mem → Word → UInt32 → σ → Mem → Prop)
    (st0 : σ)
    (S : USize → ScanRes α) (hS : ∀ i x e, S i = .ok x e → F (i + 1) true 0 st0 = .ok x e)
    (H : ∀ m₁ q, IObjLoop b F kind q (R m₁ q) (Fn m₁ q))
    (i : USize) (m₁ : Mem) (q : Word) (x : α) (e : USize) (e₂ : Word) (m₂ : Mem)
    (hS' : S i = .ok x e) (h0 : R m₁ q 0 st0 m₁)
    (hob : objW b.data m₁ i.toUInt64 kind q = some (e₂, m₂)) :
    e₂ = e.toUInt64 ∧ Fn m₁ q x m₂ := by
  rw [objW_eq, ← succ_toUInt64 b h64 hsize, show (1 : Word) = bw true from rfl] at hob
  exact iobj_link b h64 hsize F kind q (R m₁ q) _ (H m₁ q) (i + 1) true 0 st0 m₁ x e
    e₂ m₂ (hS i x e hS') h0 hob

omit h64 hsize in
/-- A freshly allocated record is being read. -/
theorem recInv_alloc (A : ArrId) (hA : A = IFR ∨ A = IFL) (sz : Nat) (n q : Word) (m m₁ : Mem)
    (hR : Room m) (hn : n.toNat = sz) (hal : allocW m A n = some (q, m₁)) : RecInv A sz q m₁ m₁ := by
  obtain ⟨a1, a2, a3, -, -, -, -⟩ := allocW_facts m m₁ A hA n q hR hal
  exact ⟨IGrow.refl _ _ _ _, a3, by omega, by omega⟩

set_option hygiene false in
macro "ilist_shape " G:ident : tactic => `(tactic| (
  constructor
  · intro i acc w l e h; rw [$G:ident, dite_eq_right h]; simp
  · intro i acc w h hws; rw [$G:ident, dite_eq_left h]; simp only [uget_byteAt _ i h, hws, ite_true]
  · intro i acc w l e h hc hok
    rw [$G:ident, dite_eq_left h] at hok
    simp [uget_byteAt _ i h, hc, isWs] at hok
    split at hok
    · cases hok
    · simp only [ScanRes.ok.injEq] at hok; obtain ⟨rfl, rfl⟩ := hok; exact ⟨rfl, rfl⟩
  · intro i acc w l e h hc hok
    rw [$G:ident, dite_eq_left h] at hok
    simp [uget_byteAt _ i h, hc, isWs] at hok
    split at hok
    · cases hok
    · exact hok
  · intro i acc w l e h hc hok
    rw [$G:ident, dite_eq_left h] at hok
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
    rw [$G:ident, dite_eq_left h] at hok
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
      i m₁ q x e e₂ m₂ hS ⟨hI, rfl, rfl, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _⟩ hob
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
    | assumption
    | exact hx
    | rfl
    | refine ⟨?_, ?_⟩)))

set_option hygiene false in
/-- A write of `xw` to slot `s` of an `IFR` record of size `sz`, the loop going on at `en` with the
state `st'`. -/
macro "rput " s:term "," sz:term "," xw:term "," st':term "," en:term : tactic => `(tactic| (
  rw [fldPutW_R _ _ _ _ _ (by decide)]
  obtain ⟨p1, -, -, p4, p5⟩ := slot_put IFR (.inl rfl) $sz (by decide) q $s $xw m₁ m hI (by decide)
  have e1 := slot_view IFR (.inl rfl) $sz (by decide) q $s $xw m₁ m hI (by decide)
  have p6 := runR_rule_eq (Mem.arr64_set64_ne m IFR IFL (q + $s) $xw (by decide))
  have p7 := numsF_eq (Mem.arr64_set64_ne m IFR IFL (q + $s) $xw (by decide))
  refine ⟨$en, _, $st', rfl, hok, p1, by rw [p5, ht], ?_⟩
  simp (config := {decide := true}) only [e1, p5, p6, p7, ↓reduceIte]
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
theorem numsF_eq {m m' : Mem} (h : m'.arr64 IFL = m.arr64 IFL) (o : Nat) (l : List Nat) :
    NumsF m' o l = NumsF m o l := by
  simp only [NumsF, topN, wd, h]

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

theorem recList_shape : IListLoop b (scanIndRecListLoop b) (scanIndRec b) := by
  ilist_shape scanIndRecListLoop

/-- The recursors of a block: a run of recursor records in `IFR`. -/
theorem recs_link (v : USize) (m : Mem) (l : List IndRecRec) (e : USize) (r : Word × Word × Word)
    (m' : Mem) (h : scanIndRecs b v = .ok l e) (hR : Room m)
    (hm : listW b.data m v.toUInt64 2 = some (r, m')) :
    r.2.2 = e.toUInt64 ∧ r.2.1.toNat = l.length ∧
      RunR (fun t x m => RecF b m t x) IFR 11 m' r.1.toNat l ∧ Grow m m' ∧ Room m' ∧
      r.1.toNat = topN m IFR + 1 ∧ r.1.toNat + 11 * l.length = topN m' IFR + 1 := by
  refine (fun H => ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1,
    H.2.2.2.2.2.2.1⟩) (ilistW_link b h64 hsize (scanIndRecListLoop b)
    (scanIndRec b) (recList_shape b h64 hsize) (scanIndRecs b) (fun v l e h => by
      unfold scanIndRecs at h; split at h
      · rename_i h91; exact ⟨by simpa using h91, h⟩
      · cases h) 2 IFR (.inl rfl) 11 (by decide) rfl
    (fun m n => by simp [fldAllocW]) (fun t x m => RecF b m t x)
    (fun t x m m' x0 x1 h1 h2 h3 hg h4 => recF_stab b t x m m' x0 x1 h1 h2 h3 hg (.inl h4))
    (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) ?_
    v m l e r m' h hR hm)
  · intro i m m₁ q x e e₂ m₂ hi h123 hS hR hal hob
    rw [show flagsW m₁ 2 q = m₁ by simp [flagsW]] at hob
    have hI := recInv_alloc IFR (.inl rfl) 11 _ q m m₁ hR rfl hal
    obtain ⟨t1, ⟨t2, t3⟩, t4⟩ := item_gen b h64 hsize
      (fun i w seen (st : RecSt) => scanIndRecLoop b i w seen st.isUns st.kf st.lps st.nm
        st.nIdx st.nMin st.nMot st.nP st.rules st.ty) 2 IFR 11
      (fun m₁ q d m => (RecInv IFR 11 q m₁ m ∧ topN m IFR = topN m₁ IFR) ∧ RecF b m q.toNat d)
      (RecLR b) ⟨false, false, [], 0, 0, 0, 0, 0, [], 0⟩ (scanIndRec b) (fun i x e h => by
        unfold scanIndRec at h; split at h
        · exact h
        · cases h) (rec_loop b h64 hsize)
      i m₁ q x e e₂ m₂ hS ⟨hI, rfl, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _,
        seenR_zero _ _, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _⟩ hob
    exact ⟨t1, t4, t2.1, t2.2.1, t3, trivial⟩

/-- An optional number's two words. -/
def OptR (w0 w1 : Word) : Option Nat → Prop
  | none => w0 = 0
  | some n => w0 = 1 ∧ NumW w1 n

/-- con-leche's constructor loop state. -/
structure CtSt where
  isUns : Bool
  lps : List Nat
  nm : Nat
  nF : Nat
  nP : Nat
  ty : Nat
  ci : Option Nat
  ind : Option Nat

/-- The constructor record read so far. -/
def CtLR (m₁ : Mem) (q : Word) (seen : UInt32) (st : CtSt) (m : Mem) : Prop :=
  RecInv IFR 10 q m₁ m ∧ topN m IFR = topN m₁ IFR ∧
    SeenR seen 16 (NumW (wd m IFR (q.toNat + 0)) st.nm) ∧
    SeenR seen 8 (ItemsR (listN b.data (wd m IFR (q.toNat + 1))) st.lps) ∧
    SeenR seen 128 (NumW (wd m IFR (q.toNat + 2)) st.ty) ∧
    SeenR seen 32 (NumW (wd m IFR (q.toNat + 4)) st.nF) ∧
    SeenR seen 64 (NumW (wd m IFR (q.toNat + 5)) st.nP) ∧
    OptR (wd m IFR (q.toNat + 6)) (wd m IFR (q.toNat + 7)) st.ci ∧
    OptR (wd m IFR (q.toNat + 8)) (wd m IFR (q.toNat + 9)) st.ind

set_option maxHeartbeats 2000000 in
theorem ct_loop (m₁ : Mem) (q : Word) :
    IObjLoop b (fun i w seen (st : CtSt) => scanIndCtorLoop b i w seen st.isUns st.lps st.nm st.nF
        st.nP st.ty st.ci st.ind) 1 q (CtLR b m₁ q)
      (fun d m => (RecInv IFR 10 q m₁ m ∧ topN m IFR = topN m₁ IFR) ∧ CtF b m q.toNat d) := by
  constructor
  · dloop_stop scanIndCtorLoop
  · dloop_ws scanIndCtorLoop
  · dloop_close scanIndCtorLoop
    obtain ⟨hI, ht, h1, h2, h3, h4, h5, o6, o8⟩ := hR
    exact ⟨⟨hI, ht⟩, ⟨seenR_close h1 hM (by decide) (by decide), seenR_close h2 hM (by decide) (by decide),
      seenR_close h3 hM (by decide) (by decide)⟩, seenR_close h4 hM (by decide) (by decide),
      seenR_close h5 hM (by decide) (by decide), o6, o8⟩
  · dloop_comma scanIndCtorLoop
  · dloop_quote scanIndCtorLoop
  · iloop_key scanIndCtorLoop
    all_goals obtain ⟨hI, ht, h1, h2, h3, h4, h5, o6, o8⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl] at hmem
      rnum_arm 34, 1, 0, 10, { st with nm := readNatAt b v (numEnd b v) }
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl] at hmem
      rnum_arm 61, 1, 2, 10, { st with ty := readNatAt b v (numEnd b v) }
    case kNumFields =>
      rw [show UInt64.ofNat Key.kNumFields.ctorIdx = (39 : Word) from rfl] at hmem
      rnum_arm 39, 1, 4, 10, { st with nF := readNatAt b v (numEnd b v) }
    case kNumParams =>
      rw [show UInt64.ofNat Key.kNumParams.ctorIdx = (44 : Word) from rfl] at hmem
      rnum_arm 44, 1, 5, 10, { st with nP := readNatAt b v (numEnd b v) }
    case kIsUnsafe =>
      rw [show UInt64.ofNat Key.kIsUnsafe.ctorIdx = (26 : Word) from rfl] at hmem
      rbool_arm 26, 1, 3, 10, { st with isUns := xv }
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨he, rfl, hx⟩ := lps_arm b h64 hsize m m' 1 q _ 31 1 0 v xv ev e' rfl hx hmem
      subst he
      rput 1, 10, v.toUInt64, { st with lps := xv }, ev
    case kCidx =>
      rw [show UInt64.ofNat Key.kCidx.ctorIdx = (8 : Word) from rfl] at hmem
      ikey_num
      obtain ⟨he, x, rfl, hx⟩ := opt_arm b h64 hsize m m' 1 q 8 6 0 i v e' rfl hne hie hvle hmem
      subst he
      rw [fldPutW_R _ _ _ _ _ (by decide), fldPutW_R _ _ _ _ _ (by decide),
        show (6 : Word) + 1 = 7 from rfl]
      obtain ⟨p1, -, -, -, p5⟩ := slot_put IFR (.inl rfl) 10 (by decide) q 6 1 m₁ m hI (by decide)
      have e1 := slot_view IFR (.inl rfl) 10 (by decide) q 6 1 m₁ m hI (by decide)
      obtain ⟨p1', -, -, -, p5'⟩ := slot_put IFR (.inl rfl) 10 (by decide) q 7 x m₁ _ p1 (by decide)
      have e1' := slot_view IFR (.inl rfl) 10 (by decide) q 7 x m₁ _ p1 (by decide)
      refine ⟨numEnd b v, _, { st with ci := some (readNatAt b v (numEnd b v)) }, rfl, hok, p1',
        by rw [p5', p5, ht], ?_⟩
      simp (config := {decide := true}) only [e1', e1, ↓reduceIte]
      rfields
    case kInduct =>
      rw [show UInt64.ofNat Key.kInduct.ctorIdx = (22 : Word) from rfl] at hmem
      ikey_num
      obtain ⟨he, x, rfl, hx⟩ := opt_arm b h64 hsize m m' 1 q 22 8 0 i v e' rfl hne hie hvle hmem
      subst he
      rw [fldPutW_R _ _ _ _ _ (by decide), fldPutW_R _ _ _ _ _ (by decide),
        show (8 : Word) + 1 = 9 from rfl]
      obtain ⟨p1, -, -, -, p5⟩ := slot_put IFR (.inl rfl) 10 (by decide) q 8 1 m₁ m hI (by decide)
      have e1 := slot_view IFR (.inl rfl) 10 (by decide) q 8 1 m₁ m hI (by decide)
      obtain ⟨p1', -, -, -, p5'⟩ := slot_put IFR (.inl rfl) 10 (by decide) q 9 x m₁ _ p1 (by decide)
      have e1' := slot_view IFR (.inl rfl) 10 (by decide) q 9 x m₁ _ p1 (by decide)
      refine ⟨numEnd b v, _, { st with ind := some (readNatAt b v (numEnd b v)) }, rfl, hok, p1',
        by rw [p5', p5, ht], ?_⟩
      simp (config := {decide := true}) only [e1', e1, ↓reduceIte]
      rfields
  · dloop_other scanIndCtorLoop

omit h64 hsize in
theorem ctF_stab (t : Nat) (x : IndCtorRec) (m m' : Mem) (x0 x1 : Nat) (h : CtF b m t x)
    (h1 : 1 ≤ t) (h2 : t + 10 ≤ topN m IFR + 1) (hg : IGrow m m' IFR x0 x1)
    (hd : t + 10 ≤ x0 ∨ x1 ≤ t) : CtF b m' t x := by
  have hw := irec_keep t 10 m m' x0 x1 hg h1 h2 hd
  obtain ⟨⟨c1, c2, c3⟩, f4, f5, o6, o8⟩ := h
  have hopt : ∀ i, i + 1 < 10 → ∀ o, OptW m (t + i) o → OptW m' (t + i) o := by
    intro i hi o ho
    cases o with
    | none => exact (hw i (by omega)).trans ho
    | some n =>
      refine ⟨(hw i (by omega)).trans ho.1, ?_⟩
      have h' := hw (i + 1) hi
      show NumW (wd m' IFR (t + i + 1)) n
      rw [show t + i + 1 = t + (i + 1) by omega, h']
      exact ho.2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hopt 6 (by decide) _ o6, hopt 8 (by decide) _ o8⟩
  · rw [show t = t + 0 from rfl, hw 0 (by decide)]; exact c1
  · rw [hw 1 (by decide)]; exact c2
  · rw [hw 2 (by decide)]; exact c3
  · rw [hw 4 (by decide)]; exact f4
  · rw [hw 5 (by decide)]; exact f5

theorem ctList_shape : IListLoop b (scanIndCtorListLoop b) (scanIndCtor b) := by
  ilist_shape scanIndCtorListLoop

/-- The constructors of a block: a run of constructor records in `IFR`. -/
theorem cts_link (v : USize) (m : Mem) (l : List IndCtorRec) (e : USize) (r : Word × Word × Word)
    (m' : Mem) (h : scanIndCtors b v = .ok l e) (hR : Room m)
    (hm : listW b.data m v.toUInt64 1 = some (r, m')) :
    r.2.2 = e.toUInt64 ∧ r.2.1.toNat = l.length ∧
      RunR (fun t x m => CtF b m t x) IFR 10 m' r.1.toNat l ∧ Grow m m' ∧ Room m' ∧
      r.1.toNat = topN m IFR + 1 ∧ r.1.toNat + 10 * l.length = topN m' IFR + 1 := by
  refine (fun H => ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1,
    H.2.2.2.2.2.2.1⟩) (ilistW_link b h64 hsize (scanIndCtorListLoop b)
    (scanIndCtor b) (ctList_shape b h64 hsize) (scanIndCtors b) (fun v l e h => by
      unfold scanIndCtors at h; split at h
      · rename_i h91; exact ⟨by simpa using h91, h⟩
      · cases h) 1 IFR (.inl rfl) 10 (by decide) rfl
    (fun m n => by simp [fldAllocW]) (fun t x m => CtF b m t x)
    (fun t x m m' x0 x1 h1 h2 h3 hg h4 => ctF_stab b t x m m' x0 x1 h1 h2 h3 hg (.inl h4))
    (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) ?_
    v m l e r m' h hR hm)
  · intro i m m₁ q x e e₂ m₂ hi h123 hS hR hal hob
    rw [show flagsW m₁ 1 q = (m₁.set64 IFR (q + 6) 0).set64 IFR (q + 8) 0 by simp [flagsW]] at hob
    have hI := recInv_alloc IFR (.inl rfl) 10 _ q m m₁ hR rfl hal
    obtain ⟨f1, -, -, -, f5⟩ := slot_put IFR (.inl rfl) 10 (by decide) q 6 0 m₁ m₁ hI (by decide)
    have g1 := slot_view IFR (.inl rfl) 10 (by decide) q 6 0 m₁ m₁ hI (by decide)
    obtain ⟨f1', -, -, -, f5'⟩ := slot_put IFR (.inl rfl) 10 (by decide) q 8 0 m₁ _ f1 (by decide)
    have g1' := slot_view IFR (.inl rfl) 10 (by decide) q 8 0 m₁ _ f1 (by decide)
    generalize hF : (m₁.set64 IFR (q + 6) 0).set64 IFR (q + 8) 0 = mF at hob f1' f5' g1'
    have hIF : RecInv IFR 10 q mF mF := ⟨IGrow.refl _ _ _ _, f1'.2.1, f1'.2.2.1,
      by rw [f5', f5]; exact f1'.2.2.2⟩
    obtain ⟨t1, ⟨t2, t3⟩, t4⟩ := item_gen b h64 hsize
      (fun i w seen (st : CtSt) => scanIndCtorLoop b i w seen st.isUns st.lps st.nm st.nF
        st.nP st.ty st.ci st.ind) 1 IFR 10
      (fun m₁ q d m => (RecInv IFR 10 q m₁ m ∧ topN m IFR = topN m₁ IFR) ∧ CtF b m q.toNat d)
      (CtLR b) ⟨false, [], 0, 0, 0, 0, none, none⟩ (scanIndCtor b) (fun i x e h => by
        unfold scanIndCtor at h; split at h
        · exact h
        · cases h) (ct_loop b h64 hsize)
      i mF q x e e₂ m₂ hS ⟨hIF, rfl, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _,
        seenR_zero _ _, seenR_zero _ _,
        (by show wd mF IFR (q.toNat + 6) = 0
            rw [g1', ite_eq_right (by decide), g1, ite_eq_left (by decide)]),
        (by show wd mF IFR (q.toNat + 8) = 0
            rw [g1', ite_eq_left (by decide)])⟩ hob
    exact ⟨t1, t4, f1'.1.trans t2.1, t2.2.1, ⟨by rw [t3, f5', f5], trivial⟩⟩

omit h64 hsize in
/-- An item of a number list, if not `NONE`, is below `10^18`. -/
theorem itemsN_lt (a : Array UInt8) (ha : a.size < 2 ^ 63) (i : Word) :
    ∀ x ∈ itemsN a i, x ≠ NONE → x.toNat < 10 ^ 18 := by
  fun_induction itemsN a i with
  | case1 => simp
  | case2 i h1 h2 h3 h4 ih =>
    intro x hx hne
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · have := L.Scan.lt_of_lt_ofNat h1
      have hle := L.Scan.Values.numEndN_le a i.toNat (by omega)
      apply rdNatN_lt a _ _ (by omega) _ hne
      intro j hj1 hj2
      rw [UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)] at hj2
      exact numEndN_digits a i.toNat j hj1 hj2
    · exact ih x hx hne
  | case3 => simp
  | case4 i h1 h2 h3 ih => exact ih
  | case5 => simp

omit h64 hsize in
theorem itemsR_get : ∀ (ws : List Word) (ns : List Nat), ItemsR ws ns → (∀ x ∈ ws, x ≠ NONE) →
    ws.length = ns.length ∧ ∀ k (h1 : k < ws.length) (h2 : k < ns.length), ws[k].toNat = ns[k]
  | [], [], _, _ => ⟨rfl, fun k h1 => by simp at h1⟩
  | w :: ws, n :: ns, ⟨hw, hws⟩, hne => by
    obtain ⟨l1, l2⟩ := itemsR_get ws ns hws (fun x hx => hne x (by simp [hx]))
    refine ⟨by simp [l1], fun k h1 h2 => ?_⟩
    cases k with
    | zero => exact hw (hne w (by simp))
    | succ k => exact l2 k (by simpa using h1) (by simpa using h2)
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- con-leche's type loop state. -/
structure TySt where
  ctors : List Nat
  isRec : Bool
  isRefl : Bool
  isUns : Bool
  lps : List Nat
  nm : Nat
  nIdx : Nat
  nNest : Nat
  nP : Nat
  ty : Nat

/-- The type record read so far. -/
def TyLR (m₁ : Mem) (q : Word) (seen : UInt32) (st : TySt) (m : Mem) : Prop :=
  RecInv IFR 11 q m₁ m ∧ topN m IFR = topN m₁ IFR ∧
    SeenR seen 64 (NumW (wd m IFR (q.toNat + 0)) st.nm) ∧
    SeenR seen 32 (ItemsR (listN b.data (wd m IFR (q.toNat + 1))) st.lps) ∧
    SeenR seen 1024 (NumW (wd m IFR (q.toNat + 2)) st.ty) ∧
    SeenR seen 2 ((wd m IFR (q.toNat + 4)).toNat = st.ctors.length ∧
      NumsF m (wd m IFR (q.toNat + 3)).toNat st.ctors) ∧
    SeenR seen 16 (BoolW (wd m IFR (q.toNat + 7)) st.isUns) ∧
    SeenR seen 256 (NumW (wd m IFR (q.toNat + 9)) st.nNest) ∧
    SeenR seen 512 (NumW (wd m IFR (q.toNat + 10)) st.nP)

set_option maxHeartbeats 2000000 in
theorem ty_loop (m₁ : Mem) (q : Word) :
    IObjLoop b (fun i w seen (st : TySt) => scanIndTypeLoop b i w seen st.ctors st.isRec st.isRefl
        st.isUns st.lps st.nm st.nIdx st.nNest st.nP st.ty) 0 q (TyLR b m₁ q)
      (fun d m => (RecInv IFR 11 q m₁ m ∧ topN m IFR = topN m₁ IFR) ∧ TyF b m q.toNat d) := by
  constructor
  · dloop_stop scanIndTypeLoop
  · dloop_ws scanIndTypeLoop
  · dloop_close scanIndTypeLoop
    obtain ⟨hI, ht, h1, h2, h3, h4, h5, h6, h7⟩ := hR
    have c4 := seenR_close h4 hM (by decide) (by decide)
    exact ⟨⟨hI, ht⟩, ⟨seenR_close h1 hM (by decide) (by decide), seenR_close h2 hM (by decide) (by decide),
      seenR_close h3 hM (by decide) (by decide)⟩, c4.1, c4.2, seenR_close h5 hM (by decide) (by decide),
      seenR_close h6 hM (by decide) (by decide), seenR_close h7 hM (by decide) (by decide)⟩
  · dloop_comma scanIndTypeLoop
  · dloop_quote scanIndTypeLoop
  · iloop_key scanIndTypeLoop
    all_goals obtain ⟨hI, ht, h1, h2, h3, h4, h5, h6, h7⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl] at hmem
      rnum_arm 34, 0, 0, 11, { st with nm := readNatAt b v (numEnd b v) }
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl] at hmem
      rnum_arm 61, 0, 2, 11, { st with ty := readNatAt b v (numEnd b v) }
    case kNumIndices =>
      rw [show UInt64.ofNat Key.kNumIndices.ctorIdx = (40 : Word) from rfl] at hmem
      rnum_arm 40, 0, 8, 11, { st with nIdx := readNatAt b v (numEnd b v) }
    case kNumNested =>
      rw [show UInt64.ofNat Key.kNumNested.ctorIdx = (43 : Word) from rfl] at hmem
      rnum_arm 43, 0, 9, 11, { st with nNest := readNatAt b v (numEnd b v) }
    case kNumParams =>
      rw [show UInt64.ofNat Key.kNumParams.ctorIdx = (44 : Word) from rfl] at hmem
      rnum_arm 44, 0, 10, 11, { st with nP := readNatAt b v (numEnd b v) }
    case kIsRec =>
      rw [show UInt64.ofNat Key.kIsRec.ctorIdx = (24 : Word) from rfl] at hmem
      rbool_arm 24, 0, 5, 11, { st with isRec := xv }
    case kIsReflexive =>
      rw [show UInt64.ofNat Key.kIsReflexive.ctorIdx = (25 : Word) from rfl] at hmem
      rbool_arm 25, 0, 6, 11, { st with isRefl := xv }
    case kIsUnsafe =>
      rw [show UInt64.ofNat Key.kIsUnsafe.ctorIdx = (26 : Word) from rfl] at hmem
      rbool_arm 26, 0, 7, 11, { st with isUns := xv }
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨he, rfl, hx⟩ := lps_arm b h64 hsize m m' 0 q _ 31 1 0 v xv ev e' rfl hx hmem
      subst he
      rput 1, 11, v.toUInt64, { st with lps := xv }, ev
    case kAll =>
      rw [show UInt64.ofNat Key.kAll.ctorIdx = (1 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨he, rfl⟩ := all_arm b h64 hsize m m' 0 q _ 1 0 0 v xv ev e' rfl hx hmem
      subst he
      refine ⟨ev, _, st, rfl, hok, hI, ht, ?_⟩
      rfields
    case kCtors =>
      rw [show UInt64.ofNat Key.kCtors.ctorIdx = (11 : Word) from rfl] at hmem
      ikey_res
      obtain ⟨he, mL, hids, rfl, hxs⟩ := ids_arm b h64 hsize m m' 0 q _ 11 3 0 v xv ev e' rfl hx hmem
      subst he
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := idsM_facts b.data m mL v.toUInt64 hI.2.1 hids
      rw [fldPutW_R _ _ _ _ _ (by decide), fldPutW_R _ _ _ _ _ (by decide),
        show (3 : Word) + 1 = 4 from rfl]
      have hI1 := hI.grow d3 d2
      have hw : ∀ j, wd mL IFR j = wd m IFR j := fun j => by simp only [wd, d4]
      have ht1 : topN mL IFR = topN m IFR := congrArg UInt64.toNat (hw 0)
      obtain ⟨p1, -, -, p4, p5⟩ := slot_put IFR (.inl rfl) 11 (by decide) q 3 _ m₁ mL hI1 (by decide)
      have e1 := slot_view IFR (.inl rfl) 11 (by decide) q 3 (rdW (m.arr64 IFL) 0 + 1) m₁ mL hI1
        (by decide)
      obtain ⟨p1', -, -, p4', p5'⟩ :=
        slot_put IFR (.inl rfl) 11 (by decide) q 4 (lsCntN b.data (v.toUInt64 + 1) 0) m₁ _ p1
          (by decide)
      have e1' := slot_view IFR (.inl rfl) 11 (by decide) q 4 (lsCntN b.data (v.toUInt64 + 1) 0) m₁ _
        p1 (by decide)
      have p6 := numsF_eq (Mem.arr64_set64_ne (mL.set64 IFR (q + 3) (rdW (m.arr64 IFL) 0 + 1)) IFR
        IFL (q + 4) (lsCntN b.data (v.toUInt64 + 1) 0) (by decide))
      have p7 := numsF_eq (Mem.arr64_set64_ne mL IFR IFL (q + 3) (rdW (m.arr64 IFL) 0 + 1)
        (by decide))
      refine ⟨ev, _, { st with ctors := xv }, rfl, hok, p1', by rw [p5', p5, ht1, ht], ?_⟩
      obtain ⟨g1, g2⟩ := itemsR_get _ _ hxs d6
      have hx : (lsCntN b.data (v.toUInt64 + 1) 0).toNat = xv.length ∧
          NumsF mL (rdW (m.arr64 IFL) 0 + 1).toNat xv := by
        refine ⟨by rw [d8, g1], by rw [d7]; omega, by rw [d7, d1, g1]; omega, fun k hk => ?_⟩
        rw [d7, d5 k (by rw [g1]; exact hk)]
        have hk' : k < (listN b.data v.toUInt64).length := by rw [g1]; exact hk
        refine ⟨g2 k hk' hk, ?_⟩
        rw [← g2 k hk' hk]
        exact itemsN_lt b.data (by have : b.data.size = b.size := rfl; omega) _ _
          (List.getElem_mem hk') (d6 _ (List.getElem_mem hk'))
      simp (config := {decide := true}) only [e1', e1, p6, p7, hw, ↓reduceIte]
      rfields
  · dloop_other scanIndTypeLoop

omit h64 hsize in
theorem numsF_stab (o : Nat) (l : List Nat) (m m' : Mem) (xa : ArrId) (x0 x1 : Nat)
    (hg : IGrow m m' xa x0 x1) (hxa : xa = IFR) (h : NumsF m o l) : NumsF m' o l := by
  subst hxa
  obtain ⟨r1, r2, r3⟩ := h
  have htl := hg.top IFL (.inr rfl)
  refine ⟨r1, by omega, fun k hk => ?_⟩
  rw [hg.wd_keep IFL (.inr rfl) _ (by omega) (by omega) (fun h => absurd h (by decide))]
  exact r3 k hk

omit h64 hsize in
theorem tyF_stab (t : Nat) (x : IndTypeRec) (m m' : Mem) (x0 x1 : Nat) (h : TyF b m t x)
    (h1 : 1 ≤ t) (h2 : t + 11 ≤ topN m IFR + 1) (hg : IGrow m m' IFR x0 x1)
    (hd : t + 11 ≤ x0 ∨ x1 ≤ t) : TyF b m' t x := by
  have hw := irec_keep t 11 m m' x0 x1 hg h1 h2 hd
  obtain ⟨⟨c1, c2, c3⟩, f4, f3, b7, n9, n10⟩ := h
  have hn := numsF_stab _ _ m m' IFR x0 x1 hg rfl f3
  rw [← hw 3 (by decide)] at hn
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hn, ?_, ?_, ?_⟩
  · rw [show t = t + 0 from rfl, hw 0 (by decide)]; exact c1
  · rw [hw 1 (by decide)]; exact c2
  · rw [hw 2 (by decide)]; exact c3
  · rw [hw 4 (by decide)]; exact f4
  · rw [hw 7 (by decide)]; exact b7
  · rw [hw 9 (by decide)]; exact n9
  · rw [hw 10 (by decide)]; exact n10

theorem tyList_shape : IListLoop b (scanIndTypeListLoop b) (scanIndType b) := by
  ilist_shape scanIndTypeListLoop

/-- The types of a block: a run of type records in `IFR`. -/
theorem tys_link (v : USize) (m : Mem) (l : List IndTypeRec) (e : USize) (r : Word × Word × Word)
    (m' : Mem) (h : scanIndTypes b v = .ok l e) (hR : Room m)
    (hm : listW b.data m v.toUInt64 0 = some (r, m')) :
    r.2.2 = e.toUInt64 ∧ r.2.1.toNat = l.length ∧
      RunR (fun t x m => TyF b m t x) IFR 11 m' r.1.toNat l ∧ Grow m m' ∧ Room m' ∧
      r.1.toNat = topN m IFR + 1 ∧ r.1.toNat + 11 * l.length = topN m' IFR + 1 := by
  refine (fun H => ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1,
    H.2.2.2.2.2.2.1⟩) (ilistW_link b h64 hsize (scanIndTypeListLoop b)
    (scanIndType b) (tyList_shape b h64 hsize) (scanIndTypes b) (fun v l e h => by
      unfold scanIndTypes at h; split at h
      · rename_i h91; exact ⟨by simpa using h91, h⟩
      · cases h) 0 IFR (.inl rfl) 11 (by decide) rfl
    (fun m n => by simp [fldAllocW]) (fun t x m => TyF b m t x)
    (fun t x m m' x0 x1 h1 h2 h3 hg h4 => tyF_stab b t x m m' x0 x1 h1 h2 h3 hg (.inl h4))
    (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) ?_
    v m l e r m' h hR hm)
  · intro i m m₁ q x e e₂ m₂ hi h123 hS hR hal hob
    rw [show flagsW m₁ 0 q = m₁ by simp [flagsW]] at hob
    have hI := recInv_alloc IFR (.inl rfl) 11 _ q m m₁ hR rfl hal
    obtain ⟨t1, ⟨t2, t3⟩, t4⟩ := item_gen b h64 hsize
      (fun i w seen (st : TySt) => scanIndTypeLoop b i w seen st.ctors st.isRec st.isRefl
        st.isUns st.lps st.nm st.nIdx st.nNest st.nP st.ty) 0 IFR 11
      (fun m₁ q d m => (RecInv IFR 11 q m₁ m ∧ topN m IFR = topN m₁ IFR) ∧ TyF b m q.toNat d)
      (TyLR b) ⟨[], false, false, false, [], 0, 0, 0, 0, 0⟩ (scanIndType b) (fun i x e h => by
        unfold scanIndType at h; split at h
        · exact h
        · cases h) (ty_loop b h64 hsize)
      i m₁ q x e e₂ m₂ hS ⟨hI, rfl, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _, seenR_zero _ _,
        seenR_zero _ _, seenR_zero _ _, seenR_zero _ _⟩ hob
    exact ⟨t1, t4, t2.1, t2.2.1, t3, trivial⟩

end kinds

end L.Front.Ind
