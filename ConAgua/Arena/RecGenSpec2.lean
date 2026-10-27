import ConAgua.Arena.IndSumSpec2A
import ConAgua.Arena.RecClassSpecA

/-!
# More refinements of `RecGen` (lane `indproofs`, helper `recb`)

Leaves whose loops were rewritten as self-recursions on the shifted slice.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `class_rule_ok_domains`: `rbs.allM (constsResolveFFast fe₀)`, the model of `idx_args_resolve` -/

theorem classRuleOkDomains_spec (p : Prog)
    (hp : p.lookup "class_rule_ok_domains" = some classRuleOkDomains) (hcr : CrfF p) (n : Nat) :
    ∀ (s₀ : St) (v o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rule_ok_domains" [v, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ iarW n s₀.mem v o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ v o l; rw [invoke_eq _ hp]; simp only [callFn, classRuleOkDomains]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ v o l
    rw [invoke_eq _ hp]
    simp only [callFn, classRuleOkDomains]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        crfF_spec p hcr n, ih] <;>
      finish (gen := 20)

/-- The twin's `allM` is `idxArgsResolve`. -/
theorem allM_resolve_eq (fe : IFEnv) : ∀ xs : List EIdx,
    xs.allM (fun b => constsResolveFFast fe b) = idxArgsResolve fe xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.allM_cons, idxArgsResolve, ih]

/-! ## `class_key_of_closed`: `ds.allM` of the `bvarB`/`fvarB` closedness test -/

mutual
/-- **The model of `class_key_of_closed`.** -/
def ckcW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, nP, o, l =>
    if l = 0 then some ([1], m)
    else ckcK1 n nP o l (rdW (m.arr64 IW) o) (bvbF m [CWF, rdW (m.arr64 IW) o])
/-- After `bvar_b`. -/
def ckcK1 (n : Nat) (nP o l e : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m1) =>
    if rb.headD 0 ≠ 0 then some ([0], m1) else ckcK2 n nP o l (fvbF m1 [CWF, e])
/-- After `fvar_b`. -/
def ckcK2 (n : Nat) (nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rf, m2) =>
    if nP < rf.headD 0 then some ([0], m2) else ckcK3 (ckcW n m2 nP (o + 1) (l - 1))
/-- After the recursive call: its first word. -/
def ckcK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (nP o l e : Word) (rb rf r : List Word)
theorem ckcK3_some : ckcK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] ckcK3_some => ckcK3 (some (r, m))

/-- The twin's per-parameter closedness test. -/
def keyClosedTest (nP : Nat) (x : EIdx) : AM Bool := do
  if (← bvarB coreWalkFuel x) != 0 then pure false
  else pure ((← fvarB coreWalkFuel x) ≤ nP)

/-! ## `class_fields_of_hits`: the count and class of `ihs.filter (·.1 == i)` -/

l_model classFieldsOfHits_spec (p : Prog)
    (hp : p.lookup "class_fields_of_hits" = some classFieldsOfHits)
  fns [hp ↦ cfhW ro tuple]
  grind [arena_grind] simp [getElem_rdW']

/-- What `class_fields_of_hits` returns about the twin's `hits`: their count, and, when there is
exactly one, its class. -/
def HitsRes (hits : List (Nat × Nat)) (cnt cls : Word) : Prop :=
  cnt.toNat = hits.length ∧ ∀ h, hits = [h] → cls = UInt64.ofNat h.2 ∧ h.2 < 2 ^ 64

theorem decNN_words {m : Mem} {pp : Nat} {a b : Nat} (h : decNN m pp = some (a, b)) (hp : pp + 1 < 2 ^ 64) :
    rdW (m.arr64 IW) (UInt64.ofNat pp) = UInt64.ofNat a ∧ a < 2 ^ 64 ∧
    rdW (m.arr64 IW) (UInt64.ofNat pp + 1) = UInt64.ofNat b ∧ b < 2 ^ 64 := by
  simp only [decNN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨a', ha, b', hb, rfl, rfl⟩ := h
  have h1 := iwN_rdW ha (by omega)
  have h2 := iwN_rdW hb hp
  refine ⟨h1.1, h1.2, ?_, h2.2⟩
  rw [← h2.1]
  congr 1
  rw [UInt64.ofNat_add]; rfl

theorem cfhW_ok (n : Nat) : ∀ (m : Mem) (o l i x y : Word) (ihs : List (Nat × Nat)),
    cfhW n m o l i = some (x, y) → decPL m (decNN m) o.toNat l.toNat = some ihs →
    o.toNat + l.toNat < 2 ^ 64 → (m.arr64 IW).size < 2 ^ 64 →
    HitsRes (ihs.filter (fun h => h.1 == i.toNat)) x y := by
  induction n with
  | zero => intro m o l i x y ihs h; simp [cfhW] at h
  | succ n ih =>
    intro m o l i x y ihs h hd hb hsz
    by_cases hl : l = 0
    · rw [cfhW.arm1 n m o l i hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp [hl, decPL] at hd; subst hd; simp [HitsRes]
    · obtain ⟨hsum, hco1⟩ := toNat_succ_of_lt hb hl
      obtain ⟨l1, hl1⟩ : ∃ l1, l.toNat = l1 + 1 :=
        ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
      rw [hl1] at hd
      obtain ⟨pp, hh, ys, rfl, hp, hx, hys⟩ := decPL_cons hd
      have hrd := iwN_rdW hp (by omega)
      rw [UInt64.ofNat_toNat] at hrd
      have hppsz : pp + 1 < (m.arr64 IW).size := by
        simp only [decNN, bind, Option.bind_eq_some_iff] at hx
        obtain ⟨a', ha, b', hb', -⟩ := hx
        exact iwN_lt hb'
      obtain ⟨hw1, ha64, hw2, hb64⟩ := decNN_words hx (by omega)
      rw [cfhW.arm2 n m o l i hl, hrd.1] at h
      obtain ⟨⟨c0, k0⟩, h2, h⟩ := of_K h rfl
      have hl1' : (l - 1).toNat = l1 := by omega
      have hys' : decPL m (decNN m) (o + 1).toNat (l - 1).toNat = some ys := by
        rw [hco1, hl1']; exact hys
      obtain ⟨g1, g2⟩ := ih m (o + 1) (l - 1) i c0 k0 ys h2 hys' (by omega) hsz
      have hlen := decPL_length m hys
      have hfl := List.length_filter_le (fun h => h.1 == i.toNat) ys
      by_cases hmatch : rdW (m.arr64 IW) (UInt64.ofNat pp) = i
      · have hai : hh.1 = i.toNat := by
          rw [hw1] at hmatch
          have := congrArg UInt64.toNat hmatch
          rw [UInt64.toNat_ofNat_of_lt' ha64] at this; exact this
        have hf : (hh :: ys).filter (fun h => h.1 == i.toNat) =
            hh :: ys.filter (fun h => h.1 == i.toNat) := by simp [hai]
        rw [hf]
        by_cases hc : c0 = 0
        · rw [cfhW.k_class_fields_of_hits.arm1 i _ m c0 k0 hmatch hc] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hnil : ys.filter (fun h => h.1 == i.toNat) = [] := by
            apply List.eq_nil_of_length_eq_zero; rw [← g1, hc]; rfl
          rw [hnil]
          refine ⟨by simp, fun h' hh' => ?_⟩
          obtain rfl : hh = h' := by simpa using hh'
          exact ⟨hw2, hb64⟩
        · rw [cfhW.k_class_fields_of_hits.arm2 i _ m c0 k0 hmatch hc] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hpos : c0.toNat ≠ 0 := fun h0 => hc (UInt64.toNat_inj.mp (by simpa using h0))
          refine ⟨?_, fun h' hh' => ?_⟩
          · rw [show (c0 + 1).toNat = c0.toNat + 1 by rw [UInt64.toNat_add]; simp; omega, g1]; simp
          · have : (hh :: ys.filter (fun h => h.1 == i.toNat)).length = 1 := by rw [hh']; rfl
            simp only [List.length_cons] at this; omega
      · rw [cfhW.k_class_fields_of_hits.arm3 i _ m c0 k0 hmatch] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hai : ¬ hh.1 = i.toNat := fun e => hmatch (by rw [hw1, e]; exact UInt64.ofNat_toNat)
        have hf : (hh :: ys).filter (fun h => h.1 == i.toNat) = ys.filter (fun h => h.1 == i.toNat) := by
          simp [hai]
        rw [hf]; exact ⟨g1, g2⟩

/-! ## `gen_rec_check_any_no_member`: `ms.any (·.member.isNone)` -/

/-- **The model of `gen_rec_check_any_no_member`.** -/
def anmW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, o, l =>
    if l = 0 then some 0
    else if rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = 0 then some 1
    else anmW n m (o + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (o l : Word)
theorem anmW_nil (h : l = 0) : anmW (n + 1) m o l = some 0 := by simp [anmW, h]
theorem anmW_hit (h : l ≠ 0) (hx : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = 0) :
    anmW (n + 1) m o l = some 1 := by simp [anmW, h, hx]
theorem anmW_next (h : l ≠ 0) (hx : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) ≠ 0) :
    anmW (n + 1) m o l = anmW n m (o + 1) (l - 1) := by simp [anmW, h, hx]
end arms

grind_pattern [ind_grind] anmW_nil => anmW (n + 1) m o l
grind_pattern [ind_grind] anmW_hit => anmW (n + 1) m o l
grind_pattern [ind_grind] anmW_next => anmW (n + 1) m o l

theorem genRecCheckAnyNoMember_spec (p : Prog)
    (hp : p.lookup "gen_rec_check_any_no_member" = some genRecCheckAnyNoMember) (n : Nat) :
    ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_any_no_member" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ anmW n s₀.mem o l = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o l; rw [invoke_eq _ hp]; simp only [callFn, genRecCheckAnyNoMember]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l
    rw [invoke_eq _ hp]
    simp only [callFn, genRecCheckAnyNoMember]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

theorem decTM_member {m : Mem} {pp : Nat} {t : TargetMajor} (h : decTM m pp = some t) :
    ∃ k, iwN m (pp + 8) = some k ∧ t.member = decON k := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, k, hk, _, -, _, -, rfl⟩ := h
  exact ⟨k, hk, rfl⟩

theorem anmW_ok (n : Nat) : ∀ (m : Mem) (o l r : Word) (ms : List TargetMajor),
    anmW n m o l = some r → decPL m (decTM m) o.toNat l.toNat = some ms →
    o.toNat + l.toNat < 2 ^ 64 → (m.arr64 IW).size < 2 ^ 64 →
    (r != 0) = ms.any (fun t => t.member.isNone) ∧ r.toNat ≤ 1 := by
  induction n with
  | zero => intro m o l r ms h; simp [anmW] at h
  | succ n ih =>
    intro m o l r ms h hd hb hsz
    by_cases hl : l = 0
    · rw [anmW_nil n m o l hl] at h
      simp only [Option.some.injEq] at h
      subst h
      have hz : l.toNat = 0 := by rw [hl]; rfl
      rw [hz] at hd
      simp [decPL] at hd
      subst hd
      simp
    · obtain ⟨hsum, hco1⟩ := toNat_succ_of_lt hb hl
      obtain ⟨l1, hl1⟩ : ∃ l1, l.toNat = l1 + 1 := ⟨l.toNat - 1, by
        have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
        omega⟩
      rw [hl1] at hd
      obtain ⟨pp, t, ys, rfl, hp, hx, hys⟩ := decPL_cons hd
      have hrd := iwN_rdW hp (by omega)
      rw [UInt64.ofNat_toNat] at hrd
      obtain ⟨k, hk, hmem⟩ := decTM_member hx
      have hk8 := iwN_lt hk
      have hk' := iwN_rdW hk (by omega)
      have e8 : UInt64.ofNat pp + 8 = UInt64.ofNat (pp + 8) := by rw [UInt64.ofNat_add]; rfl
      have hrd8 : rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 8) = UInt64.ofNat k := by
        rw [hrd.1, e8]; exact hk'.1
      have hk0 : (UInt64.ofNat k = 0) ↔ k = 0 := by
        constructor
        · intro e
          have := congrArg UInt64.toNat e
          rw [UInt64.toNat_ofNat_of_lt' hk'.2] at this; simpa using this
        · intro e; subst e; rfl
      by_cases he : k = 0
      · rw [anmW_hit n m o l hl (by rw [hrd8]; exact hk0.mpr he)] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [List.any_cons, hmem, decON, he]
      · rw [anmW_next n m o l hl (by rw [hrd8]; exact fun e => he (hk0.mp e))] at h
        have hys' : decPL m (decTM m) (o + 1).toNat (l - 1).toNat = some ys := by
          have hl1' : (l - 1).toNat = l1 := by omega
          rw [hco1, hl1']; exact hys
        have := ih m (o + 1) (l - 1) r ys h hys' (by omega) hsz
        simpa [List.any_cons, hmem, decON, he] using this

/-- **`gen_rec_check_any_no_member` is `ms.any (·.member.isNone)`** (a piece of `genRecCheck`;
pure, the state untouched). -/
theorem genRecCheckAnyNoMember_refines (p : Prog)
    (hp : p.lookup "gen_rec_check_any_no_member" = some genRecCheckAnyNoMember) (n : Nat) (s₀ : St)
    (o l : Word) (ms : List TargetMajor)
    (hd : decPL s₀.mem (decTM s₀.mem) o.toNat l.toNat = some ms) (hb : o.toNat + l.toNat < 2 ^ 64)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "gen_rec_check_any_no_member" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      (r.headD 0 != 0) = ms.any (fun t => t.member.isNone) ∧ (r.headD 0).toNat ≤ 1; ⊤⦄ := by
  refine triple_post (genRecCheckAnyNoMember_spec p hp n s₀ o l) ?_
  rintro r s' ⟨hl, hm, hw⟩
  exact ⟨hl, hm, anmW_ok n s₀.mem o l _ ms hw hd hb hsz⟩

end L.Ind
