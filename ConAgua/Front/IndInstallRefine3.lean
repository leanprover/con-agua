module

public import ConAgua.Front.IndInstallRefine2
import ConAgua.L.WordOff
import ConAgua.Front.IndApplyRefine
public import ConAgua.Arena.RecLayout.RuleDec
import ConAgua.Arena.DeclRec

@[expose] public section

/-!
# `install_ind_d` refines `installIndD`, III: the recursor records

`ruleW_twin` (`parse_rule_d` against `parseRuleD`), `rulesW_twin` (`ind_rules`: the rules as a
fresh slice of 11-word records, `decRules`), `recRW_twin` (`ind_rec` against the twin's `recInfo`
constant).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec)
open ConAgua.Front.FieldsLink
open L.Front.Fields (listN itemsN)


namespace L.Front.Ind

/-! ## A rule's words -/

theorem ruleM_frame (m : Mem) (q n nf e : Word) : MemFrame [DLP] [] m (ruleM m q n nf e) := by
  unfold ruleM
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  exact MemFrame.set64 _ DLP (by decide) _ _

/-- `parse_rule_d`'s stores hold the rule's fields (`RuleRecW`). -/
theorem ruleM_recW (m : Mem) (q n nf e : Word) (hs : q.toNat + Rule.size.toNat ≤ (m.arr64 DLP).size)
    (hq : q.toNat + Rule.size.toNat < 2 ^ 64) :
    RuleRecW (aread ((ruleM m q n nf e).arr64 DLP)) q.toNat n nf 0 0 0 0 0 e := by
  have h := ruleRecW_set64 (m := m) (A := DLP) (w0 := n) (w1 := nf) (w2 := 0) (w3 := 0) (w4 := 0)
    (w5 := 0) (w6 := 0) (w7 := e) hs hq
  have e0 : q + Rule.ctor = q :=
    UInt64.toNat_inj.mp (by rw [fld_toNat Rule.ctor_lt hq, ctor_add])
  rwa [e0] at h

/-- `parse_rule_d`'s words decode as the rule. -/
theorem ruleM_dec (m : Mem) (q n nf e : Word) (hs : q.toNat + Rule.size.toNat ≤ (m.arr64 DLP).size)
    (hq : q.toNat + Rule.size.toNat < 2 ^ 64) (hn : n.toNat < 2 ^ 32) (he : e.toNat < 2 ^ 32)
    (P : Array Word)
    (h : ∀ k, k < Rule.size.toNat → P[q.toNat + k]? = some (wd (ruleM m q n nf e) DLP (q.toNat + k))) :
    decRule (aread P) q.toNat = some ⟨decI n, nf.toNat, .plain, decI e⟩ := by
  have hW := (ruleM_recW m q n nf e hs hq).shift (b := aread P) (e := q.toNat) (fun j hj => by
    rw [aread_apply, aread_apply, h j hj,
      wd_some _ _ _ (by rw [(ruleM_frame m q n nf e).size DLP]; omega)])
  exact decRule_of_words hW hn he (hW.plain rfl)

/-- `parse_rule_d` writes only its record's words. -/
theorem ruleM_out (m : Mem) (q n nf e : Word) (hq : q.toNat + Rule.size.toNat < 2 ^ 64) (j : Nat)
    (hj : j < q.toNat ∨ q.toNat + Rule.size.toNat ≤ j) : wd (ruleM m q n nf e) DLP j = wd m DLP j := by
  have e : ∀ f : Word, f.toNat < Rule.size.toNat → (q + f).toNat ≠ j := fun f hf => by
    rw [fld_toNat hf hq]; omega
  have := Rule.size_pos
  unfold ruleM
  rw [wd_set_ne _ _ _ _ _ (e _ Rule.rhs_lt), wd_set_ne _ _ _ _ _ (e _ Rule.pinsLen_lt),
    wd_set_ne _ _ _ _ _ (e _ Rule.pinsOff_lt), wd_set_ne _ _ _ _ _ (e _ Rule.lvlsLen_lt),
    wd_set_ne _ _ _ _ _ (e _ Rule.lvlsOff_lt), wd_set_ne _ _ _ _ _ (e _ Rule.fire_lt),
    wd_set_ne _ _ _ _ _ (e _ Rule.nfields_lt), wd_set_ne _ _ _ _ _ (by omega)]


/-! ## `parse_rule_d`, `ind_rules` -/

theorem RuleF.congr {m m' : Mem} {q : Nat} {ru : RuleRec} (h : m'.arr64 IFL = m.arr64 IFL)
    (hR : RuleF m q ru) : RuleF m' q ru := by
  unfold RuleF wd at *; rw [h]; exact hR

theorem w_addmul (lo j : Word) (c : Nat) (hc : c < 2 ^ 32) (h : lo.toNat + c * j.toNat < 2 ^ 64) :
    (lo + (UInt64.ofNat c) * j).toNat = lo.toNat + c * j.toNat := by
  have hc' : (UInt64.ofNat c).toNat = c := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  rw [UInt64.toNat_add, UInt64.toNat_mul, hc', Nat.mod_eq_of_lt (a := c * j.toNat) (by omega)]
  omega

/-- A slice's `j`-th record `lo + c * j` (records of `c` words), as a number. -/
theorem w_addmulW (lo c j : Word) (h : lo.toNat + c.toNat * j.toNat < 2 ^ 64) :
    (lo + c * j).toNat = lo.toNat + c.toNat * j.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt (a := c.toNat * j.toNat) (by omega)]
  omega

/-- **`parse_rule_d` against `parseRuleD`.** -/
@[refines ConRon.Arena.Frontend.parseRuleD]
theorem ruleW_twin {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st) {q rp : Word} {ru : RuleRec}
    (hR : RuleF m rp.toNat ru) (hrp : rp.toNat + 3 < 2 ^ 63)
    (hs : q.toNat + Rule.size.toNat ≤ (m.arr64 DLP).size) (hq : q.toNat + Rule.size.toNat < 2 ^ 64)
    (h : ruleW m q rp = some m') :
    (ConRon.Arena.Frontend.parseRuleD st ru).run a = .ok (resOf (ConRon.Arena.Frontend.parseRuleD st ru) a, a) ∧ MemFrame [DLP] [] m m' ∧
      (∀ j, (j < q.toNat ∨ q.toNat + Rule.size.toNat ≤ j) → wd m' DLP j = wd m DLP j) ∧
      (∀ P : Array Word, (∀ k, k < Rule.size.toNat → P[q.toNat + k]? = some (wd m' DLP (q.toNat + k))) →
        decRule (aread P) q.toNat = some (resOf (ConRon.Arena.Frontend.parseRuleD st ru) a)) := by
  obtain ⟨n0, f0, e0⟩ := hR
  rw [ruleW_eq] at h
  have r0 : rdW (m.arr64 IFL) rp = wd m IFL rp.toNat := rfl
  have r1 : rdW (m.arr64 IFL) (rp + 1) = wd m IFL (rp.toNat + 1) := by
    rw [rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have r2 : rdW (m.arr64 IFL) (rp + 2) = wd m IFL (rp.toNat + 2) := by
    rw [rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [r0, r1, r2] at h
  rcases hn : lkW m NID (wd m IFL rp.toNat) with _ | nh <;> simp only [hn, wK, reduceCtorEq] at h
  rcases he : lkW m EID (wd m IFL (rp.toNat + 2)) with _ | eh <;> simp only [he, reduceCtorEq] at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨n1, n2⟩ := lkR_name hD a hn
  obtain ⟨y1, y2⟩ := lkR_expr hD a he
  rw [n0.1] at n1; rw [e0.1] at y1
  have hrun : (ConRon.Arena.Frontend.parseRuleD st ru).run a =
      .ok (⟨decI nh, ru.nfields, .plain, decE eh⟩, a) := by
    unfold ConRon.Arena.Frontend.parseRuleD; rw [run_bind _ _ a _ n1, run_bind _ _ a _ y1]; rfl
  rw [resOf_eq hrun]
  refine ⟨hrun, ruleM_frame _ _ _ _ _, fun j hj => ruleM_out _ _ _ _ _ hq j hj, fun P hP => ?_⟩
  rw [ruleM_dec m q _ _ _ hs hq n2 y2 P hP, f0.1, decE_eq]

/-- **`ind_rules_go`**: the rules from the `j`-th on. -/
theorem rulesGoW_twin {st : StateD} (a : AState) {lo o l : Word} {rules : List RuleRec}
    (hl : l.toNat = rules.length) (ho : o.toNat + 3 * rules.length < 2 ^ 63) :
    ∀ n (m m' : Mem) (j : Word), LkR m st →
      (∀ k (hk : k < rules.length), RuleF m (o.toNat + 3 * k) rules[k]) →
      lo.toNat + Rule.size.toNat * rules.length ≤ (m.arr64 DLP).size → 1 ≤ lo.toNat →
      j.toNat ≤ rules.length → rulesGoW n m lo o l j = some m' →
      MemFrame [DLP] [] m m' ∧
      (∀ i, (i < lo.toNat + Rule.size.toNat * j.toNat ∨ lo.toNat + Rule.size.toNat * rules.length ≤ i) →
        wd m' DLP i = wd m DLP i) ∧
      ∀ k (hk : k < rules.length), j.toNat ≤ k →
        (ConRon.Arena.Frontend.parseRuleD st rules[k]).run a = .ok (resOf (ConRon.Arena.Frontend.parseRuleD st rules[k]) a, a) ∧
        ∀ P : Array Word, (∀ i, i < Rule.size.toNat →
            P[lo.toNat + Rule.size.toNat * k + i]? = some (wd m' DLP (lo.toNat + Rule.size.toNat * k + i))) →
          decRule (aread P) (lo.toNat + Rule.size.toNat * k) = some (resOf (ConRon.Arena.Frontend.parseRuleD st rules[k]) a)
  | 0, _, _, _, _, _, _, _, _, h => by simp [rulesGoW] at h
  | n + 1, m, m', j, hL, hRF, hlo, hlo1, hj, h => by
    have hps := hL.psize
    by_cases hlj : l ≤ j
    · rw [rulesGoW.arm1 (hc1 := hlj)] at h
      cases h
      have : rules.length ≤ j.toNat := by rw [← hl]; exact UInt64.le_iff_toNat_le.mp hlj
      exact ⟨MemFrame.refl _ _ _, fun _ _ => rfl, fun k hk hk' => by omega⟩
    rw [rulesGoW.arm2 (hc1 := hlj)] at h
    have hjl : j.toNat < rules.length := by
      rw [← hl]; exact Classical.byContradiction fun h' => hlj (UInt64.le_iff_toNat_le.mpr (by omega))
    rcases h1 : ruleW m (lo + Rule.size * j) (o + 3 * j) with _ | m₁ <;>
      simp only [h1, rulesGoW.k_parse_rule_d.none, rulesGoW.k_parse_rule_d.arm1, rulesGoW.k_ind_rules_go_id,
        reduceCtorEq] at h
    have hS : Rule.size.toNat * j.toNat + Rule.size.toNat ≤ Rule.size.toNat * rules.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hjl
    have hw1 : (lo + Rule.size * j).toNat = lo.toNat + Rule.size.toNat * j.toNat :=
      w_addmulW lo Rule.size j (by omega)
    have hw3 : (o + 3 * j).toNat = o.toNat + 3 * j.toNat := w_addmul o j 3 (by decide) (by omega)
    obtain ⟨R1, R2, R3, R4⟩ := ruleW_twin a hL (by rw [hw3]; exact hRF _ hjl) (by omega)
      (by rw [hw1]; omega) (by rw [hw1]; omega) h1
    rw [hw1] at R3 R4
    have hj1 : (j + 1).toNat = j.toNat + 1 := L.toNat_add_of_lt _ _ (by simp; omega)
    have hL1 : LkR m₁ st := hL.frame R2 (by
      unfold topN; rw [R3 0 (.inl (by omega)), R2.size DLP]; exact hL.ptop)
    have hifl : m₁.arr64 IFL = m.arr64 IFL := R2.1 IFL (by decide) (by decide)
    obtain ⟨I1, I2, I3⟩ := rulesGoW_twin a hl ho n m₁ m' (j + 1) hL1
      (fun k hk => (hRF k hk).congr hifl) (by rw [R2.size DLP]; exact hlo) hlo1 (by omega) h
    rw [hj1, Nat.mul_succ] at I2
    rw [hj1] at I3
    refine ⟨R2.trans I1, fun i hi => ?_, fun k hk hk' => ?_⟩
    · rw [I2 i (by omega), R3 i (by omega)]
    · by_cases hkj : k = j.toNat
      · subst hkj
        refine ⟨R1, fun P hP => R4 P (fun i hi => ?_)⟩
        rw [hP i hi, I2 _ (by omega)]
      · exact I3 k hk (by omega)

/-- **`ind_rules` against the twin's rules**: a fresh slice of 11-word rules. -/
theorem rulesW_twin {n : Nat} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {o l lo ln : Word} {rules : List RuleRec} (hl : l.toNat = rules.length)
    (hRF : ∀ k (hk : k < rules.length), RuleF m (o.toNat + 3 * k) rules[k])
    (ho : o.toNat + 3 * rules.length < 2 ^ 63) (h : rulesW n m o l = some (lo, ln, m')) :
    (rules.mapM (ConRon.Arena.Frontend.parseRuleD st)).run a = .ok (rules.map (fun ru => resOf (ConRon.Arena.Frontend.parseRuleD st ru) a), a) ∧
      PExt m m' ∧ lo.toNat = topN m DLP + 1 ∧ ln = l ∧
      topN m' DLP = topN m DLP + Rule.size.toNat * rules.length ∧ LkR m' st ∧
      ∀ P : Array Word, (∀ i, lo.toNat ≤ i → i < lo.toNat + Rule.size.toNat * rules.length →
        P[i]? = some (wd m' DLP i)) →
        decRules (aread P) lo.toNat ln.toNat = some (rules.map (fun ru => resOf (ConRon.Arena.Frontend.parseRuleD st ru) a)) := by
  have hps := hD.psize
  have hpt := hD.ptop
  cases n with
  | zero => simp [rulesW] at h
  | succ n =>
  by_cases hbig : 4294967296 ≤ l
  · rw [rulesW.abort1 (hc1 := hbig)] at h; cases h
  rw [rulesW.arm1 (hc1 := hbig)] at h
  have hl32 : l.toNat < 2 ^ 32 := Classical.byContradiction fun h' =>
    hbig (UInt64.le_iff_toNat_le.mpr (by simp; omega))
  rcases h1 : allocW m DLP (Rule.size * l) with _ | ⟨lo1, m₁⟩ <;>
    simp only [h1, rulesW.k_dind_alloc.none, rulesW.k_dind_alloc.arm1, reduceCtorEq] at h
  rcases h2 : rulesGoW n m₁ lo1 o l 0 with _ | m₂ <;>
    simp only [h2, rulesW.k_ind_rules_go.none, rulesW.k_ind_rules_go.arm1, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have h11 : (Rule.size * l).toNat = Rule.size.toNat * rules.length := by
    have : Rule.size.toNat * l.toNat ≤ 64 * l.toNat := Nat.mul_le_mul_right _ Rule.size_le
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega), hl]
  obtain ⟨P1, P2, P3, P4, P5⟩ := allocP_facts hps hpt h1
  rw [h11] at P3 P4
  have hs1 : (m₁.arr64 DLP).size = (m.arr64 DLP).size := P1.size DLP
  have hL1 : LkR m₁ st := hD.frame P1.frame (by rw [P3, hs1]; omega)
  have hifl : m₁.arr64 IFL = m.arr64 IFL := P1.other IFL (by decide) (by decide)
  obtain ⟨I1, I2, I3⟩ := rulesGoW_twin a hl ho n m₁ m₂ 0 hL1 (fun k hk => (hRF k hk).congr hifl)
    (by rw [hs1]; omega) (by omega) (by simp) h2
  simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at I2 I3
  have ht2 : topN m₂ DLP = topN m DLP + Rule.size.toNat * rules.length := by
    unfold topN; rw [I2 0 (.inl (by omega))]; exact P3
  have hrun : ∀ ru ∈ rules, (ConRon.Arena.Frontend.parseRuleD st ru).run a = .ok (resOf (ConRon.Arena.Frontend.parseRuleD st ru) a, a) := by
    intro ru hru
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hru
    exact (I3 k hk (Nat.zero_le _)).1
  refine ⟨mapM_run _ _ a rules hrun, ⟨P1.frame.trans I1, by omega, fun i h1 h2 => ?_⟩, P2, rfl, ht2,
    hL1.frame I1 (by rw [ht2, I1.size DLP, hs1]; omega), fun P hP => ?_⟩
  · rw [I2 i (.inl (by omega)), P1.keep i h1 h2]
  · unfold decRules
    rw [hl]
    rw [L.Arena.mapM_some_of _ (fun j => if hj : j < rules.length then resOf (ConRon.Arena.Frontend.parseRuleD st rules[j]) a else default)
      _ (fun j hj => by
        have hj' := List.mem_range.mp hj
        rw [dite_eq_left hj']
        have hS : Rule.size.toNat * j + Rule.size.toNat ≤ Rule.size.toNat * rules.length := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj'
        exact (I3 j hj' (Nat.zero_le _)).2 P (fun i hi => hP _ (by omega) (by omega)))]
    congr 1
    exact range_map_eq rules _ _ (fun j hj => by rw [dite_eq_left hj])

/-! ## The recursor record -/

/-- The twin's constant of a recursor record (`installIndD`'s `recs`). -/
def recT (st : StateD) (r : IndRecRec) : AM IConstantInfo := do
  let rules ← r.rules.mapM (ConRon.Arena.Frontend.parseRuleD st)
  pure (IConstantInfo.recInfo (← parseCVD st r.cv)
    (r.numParams + r.numMotives + r.numMinors + r.numIndices)
    (r.numParams + r.numMotives + r.numMinors) r.k rules)

/-- **A `recInfo` record's layout**: the kind word, the constant value, then the five fields in
order (the rules' slice: offset word, length word). -/
theorem rec_layout : 0 < CI.cv.toNat ∧ CI.cv.toNat + CV.size.toNat ≤ CI.recMajor.toNat ∧
    CI.recMajor.toNat < CI.recPrefix.toNat ∧ CI.recPrefix.toNat < CI.recRulesOff.toNat ∧
    CI.recRulesLen.toNat = CI.recRulesOff.toNat + 1 ∧ CI.recRulesLen.toNat < CI.recIsK.toNat ∧
    CI.recIsK.toNat < CI.recSize.toNat ∧ CI.recSize.toNat ≤ 128 := by
  simp [CI.cv, CV.size, CI.recMajor, CI.recPrefix, CI.recRulesOff, CI.recRulesLen, CI.recIsK,
    CI.recSize]

/-- `ind_rec`'s own stores write only the record's words after the constant value. -/
theorem recTailM_out (m : Mem) (q r lo ln : Word) (hq : q.toNat + CI.recSize.toNat < 2 ^ 64) (j : Nat)
    (hj : j < q.toNat + CI.recMajor.toNat ∨ q.toNat + CI.recSize.toNat ≤ j) :
    wd (recTailM m q r lo ln) DLP j = wd m DLP j := by
  obtain ⟨-, -, o1, o2, o3, o4, o5, -⟩ := rec_layout
  have e : ∀ f : Word, CI.recMajor.toNat ≤ f.toNat → f.toNat < CI.recSize.toNat → (q + f).toNat ≠ j :=
    fun f h1 hf => by rw [fld_toNat hf hq]; omega
  unfold recTailM
  rw [wd_set_ne _ _ _ _ _ (e _ (by omega) (by omega)), wd_set_ne _ _ _ _ _ (e _ (by omega) (by omega)),
    wd_set_ne _ _ _ _ _ (e _ (by omega) (by omega)), wd_set_ne _ _ _ _ _ (e _ (by omega) (by omega)),
    wd_set_ne _ _ _ _ _ (e _ (by omega) (by omega))]

theorem recTailM_frame (m : Mem) (q r lo ln : Word) : MemFrame [DLP] [] m (recTailM m q r lo ln) := by
  unfold recTailM
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  exact MemFrame.set64 _ DLP (by decide) _ _

/-- **`ind_rec` against the twin's recursor constant.** -/
theorem recRW_twin {n : Nat} {b : ByteArray} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {r q : Word} {rc : IndRecRec} (hF : RecF b m r.toNat rc) (hr : r.toNat + 11 < 2 ^ 63)
    (hIFL : topN m IFL < 2 ^ 62) (h : recRW b.data n m r = some (q, m')) :
    (recT st rc).run a = .ok (resOf (recT st rc) a, a) ∧ PExt m m' ∧ q.toNat = topN m DLP + 1 ∧
      LkR m' st ∧ RecAt m' q.toNat (resOf (recT st rc) a) := by
  have hps := hD.psize
  have hpt := hD.ptop
  obtain ⟨cvF, fK, fI, fMi, fMo, fP, fL, fO1, fO2, fR⟩ := hF
  obtain ⟨n0, l0, y0⟩ := cvF
  cases n with
  | zero => simp [recRW] at h
  | succ n =>
  rw [recRW.arm1] at h
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := rec_layout
  have := CV.size_pos; have := Rule.size_pos
  rcases h1 : allocW m DLP CI.recSize with _ | ⟨q1, m₁⟩ <;> rw [h1] at h
  · rw [recRW.k_dind_alloc.none] at h; cases h
  rw [recRW.k_dind_alloc.arm1] at h
  simp only [DIND, Mem.arr64_set64_ne _ _ _ _ _ (show (IFR : TieredArray) ≠ DLP by decide)] at h
  obtain ⟨P1, P2, P3, P4, P5⟩ := allocP_facts hps hpt h1
  have hifr : m₁.arr64 IFR = m.arr64 IFR := P1.other IFR (by decide) (by decide)
  have hifl : m₁.arr64 IFL = m.arr64 IFL := P1.other IFL (by decide) (by decide)
  have hsm1 : (m₁.arr64 DLP).size = (m.arr64 DLP).size := P1.size DLP
  have Pq : PExt m (m₁.set64 DLP q1 5) := P1.set q1 5 (by omega) (by omega)
  have hs1 : ((m₁.set64 DLP q1 5).arr64 DLP).size = (m.arr64 DLP).size := Pq.size DLP
  have ht1 : topN (m₁.set64 DLP q1 5) DLP = topN m DLP + CI.recSize.toNat := by
    rw [← P3]; unfold topN; rw [wd_set_ne _ _ _ _ _ (by omega)]
  have hL1 : LkR (m₁.set64 DLP q1 5) st := hD.frame Pq.frame (by rw [ht1, hs1]; omega)
  have r9 : rdW (m₁.arr64 IFR) (r + 9) = wd m IFR (r.toNat + 9) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have r10 : rdW (m₁.arr64 IFR) (r + 10) = wd m IFR (r.toNat + 10) := by
    rw [hifr, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [r9, r10] at h
  rcases h2 : rulesW n (m₁.set64 DLP q1 5) (wd m IFR (r.toNat + 9)) (wd m IFR (r.toNat + 10)) with _ | ⟨lo, ln, m₃⟩ <;>
    simp only [h2, recRW.k_ind_rules.none, recRW.k_ind_rules.arm1, reduceCtorEq] at h
  have hifl1 : (m₁.set64 DLP q1 5).arr64 IFL = m.arr64 IFL := Pq.other IFL (by decide) (by decide)
  obtain ⟨Q1, Q2, Q3, Q4, Q5, Q6, Q7⟩ := rulesW_twin a hL1 fL (fun k hk => (fR k hk).congr hifl1)
    (by omega) h2
  subst Q4
  have hifr3 : m₃.arr64 IFR = m.arr64 IFR := by
    rw [Q2.other IFR (by decide) (by decide), Pq.other IFR (by decide) (by decide)]
  have s0 : rdW (m₃.arr64 IFR) r = wd m IFR r.toNat := by rw [hifr3]; rfl
  have s1 : rdW (m₃.arr64 IFR) (r + 1) = wd m IFR (r.toNat + 1) := by
    rw [hifr3, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  have s2 : rdW (m₃.arr64 IFR) (r + 2) = wd m IFR (r.toNat + 2) := by
    rw [hifr3, rdW_wdI _ _ _ _ (by simp; omega)]; rfl
  rw [s0, s1, s2] at h
  rcases h3 : cvW b.data m₃ (q1 + CI.cv) (wd m IFR r.toNat) (wd m IFR (r.toNat + 1)) (wd m IFR (r.toNat + 2)) with _ | m₄ <;>
    simp only [h3, recRW.k_ind_cv.none, recRW.k_ind_cv.arm1, reduceCtorEq] at h
  simp only [DIND, Mem.arr64_set64_ne _ _ _ _ _ (show (IFR : TieredArray) ≠ DLP by decide)] at h
  replace h : some (q1, recTailM m₄ q1 r lo (wd m IFR (r.toNat + 10))) = some (q, m') := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hq1 : (q1 + CI.cv).toNat = q1.toNat + CI.cv.toNat := L.toNat_add_of_lt _ _ (by omega)
  have ht3 : topN m₃ DLP = topN m DLP + CI.recSize.toNat + Rule.size.toNat * rc.rules.length := by
    rw [Q5, ht1]
  have hs3 : (m₃.arr64 DLP).size = (m.arr64 DLP).size := by rw [Q2.size DLP, hs1]
  obtain ⟨cvp, C1, C2, C3, C3', C4, C5, C6⟩ :=
    cvW_facts a Q6 n0.1 y0.1 l0 (by omega) (by rw [hq1, ht3]; omega) h3
  have hrun : (recT st rc).run a = .ok (.recInfo cvp (rc.numParams + rc.numMotives + rc.numMinors + rc.numIndices)
      (rc.numParams + rc.numMotives + rc.numMinors) rc.k (rc.rules.map fun ru =>
        resOf (ConRon.Arena.Frontend.parseRuleD st ru) a), a) := by
    unfold recT; rw [run_bind _ _ a _ Q1, run_bind _ _ a _ C1]; rfl
  rw [resOf_eq hrun]
  have hs4 : (m₄.arr64 DLP).size = (m.arr64 DLP).size := by rw [C2.size DLP, hs3]
  have ht4 : topN m₄ DLP = topN m DLP + CI.recSize.toNat + Rule.size.toNat * rc.rules.length +
      rc.cv.levelParams.length := by
    rw [C3, ht3]
  have hc0 : ∀ i, (i < q1.toNat + CI.recMajor.toNat ∨ q1.toNat + CI.recSize.toNat ≤ i) →
      wd (recTailM m₄ q1 r lo (wd m IFR (r.toNat + 10))) DLP i = wd m₄ DLP i :=
    fun i hi => recTailM_out _ _ _ _ _ (by omega) i hi
  have ht5 : topN (recTailM m₄ q1 r lo (wd m IFR (r.toNat + 10))) DLP = topN m₄ DLP := by
    unfold topN; rw [hc0 0 (by omega)]
  have hfr := Pq.frame.trans (Q2.frame.trans (C2.trans (recTailM_frame m₄ q1 r lo (wd m IFR (r.toNat + 10)))))
  have hsz5 : ((recTailM m₄ q1 r lo (wd m IFR (r.toNat + 10))).arr64 DLP).size = (m.arr64 DLP).size := by
    rw [(recTailM_frame m₄ q1 r lo _).size DLP, hs4]
  refine ⟨hrun, ⟨hfr, by rw [ht5, ht4]; omega, fun i h1 h2 => ?_⟩, P2, ?_, ?_⟩
  · rw [hc0 i (by omega), C4 i h1 (by omega), Q2.keep i h1 (by omega), Pq.keep i h1 h2]
  · exact hD.frame hfr (by rw [ht5, hsz5, ← hs4]; exact C3')
  · intro P hP
    have hifr4 : m₄.arr64 IFR = m.arr64 IFR := by rw [C2.1 IFR (by decide) (by decide), hifr3]
    have htop : topN (recTailM m₄ q1 r lo (wd m IFR (r.toNat + 10))) DLP =
        topN m DLP + CI.recSize.toNat + Rule.size.toNat * rc.rules.length + rc.cv.levelParams.length := by
      rw [ht5, ht4]
    have g0 : P[q1.toNat]? = some 5 := by
      rw [hP.get (Nat.le_refl _) (by omega), hc0 _ (by omega), C4 _ (by omega) (by omega),
        Q2.keep _ (by omega) (by omega), wd_set_eq _ _ _ _ _ rfl (by omega)]
    have gcv : decCV (aread P) (q1.toNat + CI.cv.toNat) = some cvp := by
      rw [← hq1]
      exact C6 (aread P) (fun i hi => by rw [aread_apply, hP.get (by omega) (by omega), hc0 i (by omega)])
    have gru : decRules (aread P) lo.toNat (wd m IFR (r.toNat + 10)).toNat =
        some (rc.rules.map fun ru => resOf (ConRon.Arena.Frontend.parseRuleD st ru) a) :=
      Q7 P (fun i h1 h2 => by
        rw [hP.get (by omega) (by omega), hc0 i (by omega), C5 i (by omega) (by omega)])
    have hq64 : q1.toNat + CI.recSize.toNat < 2 ^ 64 := by omega
    have e5 := fld_toNat (q := q1) (f := CI.recMajor) (by omega) hq64
    have e6 := fld_toNat (q := q1) (f := CI.recPrefix) (by omega) hq64
    have e7 := fld_toNat (q := q1) (f := CI.recRulesOff) (by omega) hq64
    have e8 := fld_toNat (q := q1) (f := CI.recRulesLen) (by omega) hq64
    have e9 := fld_toNat (q := q1) (f := CI.recIsK) (by omega) hq64
    have hsz : q1.toNat + CI.recSize.toNat ≤ (m₄.arr64 DLP).size := by omega
    have g5 : P[q1.toNat + CI.recMajor.toNat]? = some (wd m IFR (r.toNat + 8) + wd m IFR (r.toNat + 7) +
        wd m IFR (r.toNat + 6) + wd m IFR (r.toNat + 5)) := by
      rw [hP.get (by omega) (by omega)]
      unfold recTailM
      rw [wd_set_ne _ _ _ _ _ (by omega), wd_set_ne _ _ _ _ _ (by omega), wd_set_ne _ _ _ _ _ (by omega),
        wd_set_ne _ _ _ _ _ (by omega), wd_set_eq _ _ _ _ _ e5 (by omega), hifr4, rdW_wdI _ _ _ _ (by simp; omega),
        rdW_wdI _ _ _ _ (by simp; omega), rdW_wdI _ _ _ _ (by simp; omega), rdW_wdI _ _ _ _ (by simp; omega)]
      rfl
    have g6 : P[q1.toNat + CI.recPrefix.toNat]? = some (wd m IFR (r.toNat + 8) + wd m IFR (r.toNat + 7) +
        wd m IFR (r.toNat + 6)) := by
      rw [hP.get (by omega) (by omega)]
      unfold recTailM
      rw [wd_set_ne _ _ _ _ _ (by omega), wd_set_ne _ _ _ _ _ (by omega), wd_set_ne _ _ _ _ _ (by omega),
        wd_set_eq _ _ _ _ _ e6 (by simp only [L.Mem.size64_set64]; omega), hifr4, rdW_wdI _ _ _ _ (by simp; omega),
        rdW_wdI _ _ _ _ (by simp; omega), rdW_wdI _ _ _ _ (by simp; omega)]
      rfl
    have g7 : P[q1.toNat + CI.recRulesOff.toNat]? = some lo := by
      rw [hP.get (by omega) (by omega)]
      unfold recTailM
      rw [wd_set_ne _ _ _ _ _ (by omega), wd_set_ne _ _ _ _ _ (by omega),
        wd_set_eq _ _ _ _ _ e7 (by simp only [L.Mem.size64_set64]; omega)]
    have g8 : P[q1.toNat + CI.recRulesLen.toNat]? = some (wd m IFR (r.toNat + 10)) := by
      rw [hP.get (by omega) (by omega)]
      unfold recTailM
      rw [wd_set_ne _ _ _ _ _ (by omega),
        wd_set_eq _ _ _ _ _ e8 (by simp only [L.Mem.size64_set64]; omega)]
    have g9 : P[q1.toNat + CI.recIsK.toNat]? = some (wd m IFR (r.toNat + 4)) := by
      rw [hP.get (by omega) (by omega)]
      unfold recTailM
      rw [wd_set_eq _ _ _ _ _ e9 (by simp only [L.Mem.size64_set64]; omega), hifr4,
        rdW_wdI _ _ _ _ (by simp; omega)]
      rfl
    have a3 : (wd m IFR (r.toNat + 8) + wd m IFR (r.toNat + 7) + wd m IFR (r.toNat + 6)).toNat =
        rc.numParams + rc.numMotives + rc.numMinors := by
      rw [UInt64.toNat_add, UInt64.toNat_add, fP.1, fMo.1, fMi.1]
      have := fP.2; have := fMo.2; have := fMi.2
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have a4 : (wd m IFR (r.toNat + 8) + wd m IFR (r.toNat + 7) + wd m IFR (r.toNat + 6) +
        wd m IFR (r.toNat + 5)).toNat = rc.numParams + rc.numMotives + rc.numMinors + rc.numIndices := by
      rw [UInt64.toNat_add, a3, fI.1]
      have := fP.2; have := fMo.2; have := fMi.2; have := fI.2
      rw [Nat.mod_eq_of_lt (by omega)]
    have a9 : (wd m IFR (r.toNat + 4) != 0) = rc.k := by
      rw [fK]; cases rc.k <;> decide
    exact decCI_recInfo_iff.mpr ⟨by simp [nat?, g0], gcv, by simp [nat?, g5, a4],
      by simp [nat?, g6, a3], by simp [bool?, g9, a9], _, _, by simp [nat?, g7], by simp [nat?, g8], gru⟩

end L.Front.Ind
