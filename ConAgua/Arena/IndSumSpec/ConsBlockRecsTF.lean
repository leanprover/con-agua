module

public import ConAgua.Arena.IndSumSpec.TsrW
public import ConAgua.Arena.RecGenSpec.DecRR
import ConAgua.Arena.IndInstallSpec.IcbiW
public import ConAgua.Arena.RecLayout.RuleDec
import ConAgua.Arena.RecLayout.CIDec
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndSumSpec.ConsSumCtors
public import ConAgua.Arena.RecInfoW
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.IndInstallSpec.InstallIwB
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# ConsBlockRecsTF: `ConRon.Arena.consBlockRecsTF`

The models and stage lemmas of `block_rec_infos_tf`'s record writers: `rule_copy`, `rules_to_erec(_go)`
(the copied run decodes as the rules), `rec_info_rec` (a 10-word `.recInfo` record at `erec_put`);
`rec_k_expected` (`rkW_ok`), and `block_rec_infos_tf` itself (`briW_ok`, `blockRecInfosTF_refines`:
the records at a slice of `EREC` pointers, `decPL m (decCI (erecP m))`).
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_struct_proj_table_scoped` -/

/-- **The model of `check_struct_proj_table_scoped(vis, nP, lo, ll, bO, bL)`** at exec fuel `n`,
reading `all_level_params_defined` through `c` (`stubCall`: the stub contract; `realCall p`: the
program's own call, `IndRealSctC.lean`). -/
l_model sctW_spec (p : Prog) (hb : BvbProg p) (hf : HfF p) (hcr : CrfF p)
    (hp : p.lookup "check_struct_proj_table_scoped" = some checkStructProjTableScopedL)
    (c : CallM) (hc : CallSpec p c)
  fns [hp ↦ sctW list]
  specs [hffF_spec p hf n, hc n "all_level_params_defined", crfF_spec p hcr n, lbbF_spec p hb n]
  grind [arena_grind]

/-- The twin's per-body scoping test (`checkStructProjTable`'s `allM` body, verbatim). -/
def scopeT (fe : IFEnv) (lps : List NIdx) (nP : Nat) (b : EIdx) : AM Bool := do
  pure (!(← hasFvarFast coreWalkFuel b) &&
    (← allLevelParamsDefined lps b) &&
    (← constsResolveFFast fe b) &&
    (← looseBVarsBoundedFast coreWalkFuel (nP + 1) b))

theorem sumB01 {r : Word} {b : Bool} (h : (r != 0) = b) (hl : r.toNat ≤ 1) :
    (r = 1 ↔ b = true) ∧ (r = 0 ↔ b = false) := by
  subst h
  have : r = 0 ∨ r = 1 := by
    rcases (show r.toNat = 0 ∨ r.toNat = 1 by omega) with h | h
    · exact .inl (UInt64.toNat_inj.mp (by simpa using h))
    · exact .inr (UInt64.toNat_inj.mp (by simpa using h))
  rcases this with rfl | rfl <;> decide


end L.Ind

end

end

section

noncomputable section

/-!
# `RecCheck`: `targetMajorNfs` (lane `indproofs3`, helper `rec`)

The walk's recorded constructor normal forms of a class. L (D18): the loop became the twin's list
recursion (the tail first, so the class-match calls fire from the last entry to the first), each
kept entry `sl_cons`ed onto the kept tail (a copy, so the result is a pointer slice decoded below
the tops). Callees: `ctors_have_name` (helper `recb`'s `chnW`), `target_class_match`
(`RecCheckSpec/TcmLook`), `sl_cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The head of a pointer slice decoded below the tops. -/
theorem PSlR.uncons {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) (hl : l ≠ 0) (_hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ x ys, xs = x :: ys ∧ DecB (fun m' => f m' (rdW (m.arr64 IW) o).toNat) m x ∧
      PSlR f ys (o + 1) (l - 1) m := by
  obtain ⟨hd, hb⟩ := h
  have hb64 : o.toNat + l.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hb (Nat.lt_of_le_of_lt (by
    simp only [iwTop]; exact Nat.le_refl _) (rdW (m.arr64 CTL) 200).toNat_lt)
  obtain ⟨eo, el, hl0⟩ := slice_step hl hb64
  obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
  have hd' : decPL (truncM m) (f (truncM m)) o.toNat (l' + 1) = some xs := by rw [← hl']; exact hd
  obtain ⟨pp, x, ys, rfl, hp, hx, hys⟩ := decPL_cons hd'
  obtain ⟨-, hpm⟩ := L.Ind.iwN_truncM_some hp
  have hr := (iwN_rdW hpm (by omega)).1
  rw [UInt64.ofNat_toNat] at hr
  refine ⟨x, ys, rfl, ?_, ?_, ?_⟩
  · show f (truncM m) (rdW (m.arr64 IW) o).toNat = some x
    rw [hr, UInt64.toNat_ofNat_of_lt' (iwN_rdW hpm (by omega)).2]; exact hx
  · show decPL (truncM m) (f (truncM m)) (o + 1).toNat (l - 1).toNat = some ys
    rw [eo, el, hl']; exact hys
  · rw [eo, el]; omega

end L.Ind

end
end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `rules_to_erec` -/

/-- The memory after one record's field copies (each copy reads the memory of its time). -/
def cpMem (m : Mem) (b old : Word) : Mem :=
  let m1 := erecPutMem m b (erRd m old)
  let m2 := erecPutMem m1 (b + Rule.nfields) (erRd m1 (old + Rule.nfields))
  let m3 := erecPutMem m2 (b + Rule.fire) (erRd m2 (old + Rule.fire))
  let m4 := erecPutMem m3 (b + Rule.lvlsOff) (erRd m3 (old + Rule.lvlsOff))
  let m5 := erecPutMem m4 (b + Rule.lvlsLen) (erRd m4 (old + Rule.lvlsLen))
  let m6 := erecPutMem m5 (b + Rule.pinsOff) (erRd m5 (old + Rule.pinsOff))
  let m7 := erecPutMem m6 (b + Rule.pinsLen) (erRd m6 (old + Rule.pinsLen))
  erecPutMem m7 (b + Rule.rhs) (erRd m7 (old + Rule.rhs))

/-- The lookups of `block_rec_infos_tf`. -/
structure CbrLook (p : Prog) : Prop where
  tsr : TsrLook p
  rp : RecProg p
  rc : p.lookup "rule_copy" = some ruleCopy
  rteg : p.lookup "rules_to_erec_go" = some rulesToErecGo
  rir : p.lookup "rec_info_rec" = some recInfoRec
  rte : p.lookup "rules_to_erec" = some rulesToErec
  mi : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt
  rpa : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt
  rke : p.lookup "rec_k_expected" = some recKExpected
  bri : p.lookup "block_rec_infos_tf" = some blockRecInfosTF

/-- **The model of `rule_copy`**: each copy after the first is a join point `rcpW.jᵢ` over the
memory the copy before it left (`share`); `rcpW_some` gives its memory as `cpMem`. -/
l_model rc_spec (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.rc ↦ rcpW list]
  specs [erecPut_specW p hpu n]
  grind [arena_grind] share

theorem rcpW_some {m m' : Mem} {b old : Word} {r : List Word} (h : rcpW m b old = some (r, m')) :
    m' = cpMem m b old := by
  -- one guard per copy (the `EREC` bound `erec_put` checks), then the next join point
  simp only [rcpW] at h; split at h; · cases h
  simp only [rcpW.j1] at h; split at h; · cases h
  simp only [rcpW.j2] at h; split at h; · cases h
  simp only [rcpW.j3] at h; split at h; · cases h
  simp only [rcpW.j4] at h; split at h; · cases h
  simp only [rcpW.j5] at h; split at h; · cases h
  simp only [rcpW.j6] at h; split at h; · cases h
  simp only [rcpW.j7] at h; split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; rfl

l_model rteGo_spec (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.rteg ↦ rteGoW list]
  specs [rc_spec p hL hpu n]
  grind [arena_grind]

l_model rte_spec (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.rte ↦ rteW]
  specs [erecAlloc_specW p hL.tsr.ea n, rteGo_spec p hL hpu n]
  grind [arena_grind]

/-! ## `rules_to_erec`: the copied run decodes as the rules -/

theorem ofNat_shift (q : Word) (a j : Nat) : q + UInt64.ofNat a + UInt64.ofNat j = q + UInt64.ofNat (a + j) := by
  rw [UInt64.ofNat_add]; ac_rfl

theorem ErApart.shift {q x : Word} {a k : Nat} (h : ErApart q (a + k) x) : ErApart (q + UInt64.ofNat a) k x :=
  fun j hj => by rw [ofNat_shift]; exact h (a + j) (by omega)

/-- `EREC⦃x⦄` across a run of `erec_put`s elsewhere. -/
theorem erRd_wrER_ne : ∀ (ws : List Word) (m : Mem) (q x : Word), ErApart q ws.length x →
    erRd (wrER m q ws) x = erRd m x
  | [], _, _, _, _ => rfl
  | w :: ws, m, q, x, h => by
    simp only [wrER]
    rw [erRd_wrER_ne ws _ (q + 1) x (fun j hj => by
      have := h (j + 1) (by simp; omega)
      rwa [show q + UInt64.ofNat (j + 1) = q + 1 + UInt64.ofNat j by rw [UInt64.ofNat_add]; ac_rfl] at this)]
    exact erRd_erecPutMem_ne (by simpa using h 0 (by simp))

/-- The image of the copy of the record at `old` (`Rule.img`, its fields read in `m`). -/
def recImgOf (m : Mem) (old : Word) : List (Option Word) :=
  Rule.img (erRd m (old + Rule.ctor)) (erRd m (old + Rule.nfields)) (erRd m (old + Rule.fire))
    (erRd m (old + Rule.lvlsOff)) (erRd m (old + Rule.lvlsLen)) (erRd m (old + Rule.pinsOff))
    (erRd m (old + Rule.pinsLen)) (erRd m (old + Rule.rhs))

theorem recImgOf_length (m : Mem) (old : Word) : (recImgOf m old).length = Rule.size.toNat :=
  Rule.img_length ..

theorem recImgOf_get (m : Mem) (old : Word) {o : Word} (ho : o ∈ Rule.fields) :
    (recImgOf m old)[o.toNat]? = some (some (erRd m (old + o))) := by
  simp only [Rule.fields, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rule.img_ctor ..
  · exact Rule.img_nf ..
  · exact Rule.img_fk ..
  · exact Rule.img_lo ..
  · exact Rule.img_ll ..
  · exact Rule.img_po ..
  · exact Rule.img_pl ..
  · exact Rule.img_rhs ..

theorem recImgOf_congr {m m' : Mem} {old : Word}
    (h : ∀ o ∈ Rule.fields, erRd m' (old + o) = erRd m (old + o)) : recImgOf m' old = recImgOf m old := by
  simp only [recImgOf]
  rw [h _ (by simp [Rule.fields]), h _ (by simp [Rule.fields]), h _ (by simp [Rule.fields]),
    h _ (by simp [Rule.fields]), h _ (by simp [Rule.fields]), h _ (by simp [Rule.fields]),
    h _ (by simp [Rule.fields]), h _ (by simp [Rule.fields])]

/-- The images of the copies of the records the pointers `IW[ro ‥ ro + k)` point to, in order. -/
def ruleWords (m : Mem) (ro : Word) : Nat → List (Option Word)
  | 0 => []
  | k + 1 => recImgOf m (rdW (m.arr64 IW) ro) ++ ruleWords m (ro + 1) k

theorem ruleWords_length (m : Mem) : ∀ (ro : Word) (k : Nat),
    (ruleWords m ro k).length = Rule.size.toNat * k
  | _, 0 => rfl
  | ro, k + 1 => by
    simp only [ruleWords, List.length_append, recImgOf_length, ruleWords_length m (ro + 1) k]
    rw [Nat.mul_succ]; omega

theorem ruleWords_get (m : Mem) : ∀ (ro : Word) (k j : Nat) {o : Word}, j < k → o ∈ Rule.fields →
    (ruleWords m ro k)[Rule.size.toNat * j + o.toNat]? =
      some (some (erRd m (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + o)))
  | _, 0, _, _, hj, _ => absurd hj (by omega)
  | ro, k + 1, 0, o, _, ho => by
    have hos : o.toNat < Rule.size.toNat := by
      simp only [Rule.fields, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [ruleWords, Nat.mul_zero, Nat.zero_add, show (UInt64.ofNat 0 : Word) = 0 from rfl,
      UInt64.add_zero]
    rw [List.getElem?_append_left (by rw [recImgOf_length]; exact hos), recImgOf_get _ _ ho]
  | ro, k + 1, j + 1, o, hj, ho => by
    have hos : o.toNat < Rule.size.toNat := by
      simp only [Rule.fields, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [ruleWords]
    rw [List.getElem?_append_right (by rw [recImgOf_length, Nat.mul_succ]; omega)]
    have e : Rule.size.toNat * (j + 1) + o.toNat - (recImgOf m (rdW (m.arr64 IW) ro)).length =
        Rule.size.toNat * j + o.toNat := by rw [recImgOf_length, Nat.mul_succ]; omega
    rw [e, ruleWords_get m (ro + 1) k j (by omega) ho]
    have e2 : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by rw [UInt64.ofNat_add]; ac_rfl
    rw [e2]

/-- `IW` the same and the source records' fields read the same: the images agree. -/
theorem ruleWords_congr {m m' : Mem} (hI : m'.arr64 IW = m.arr64 IW) :
    ∀ (ro : Word) (k : Nat), (∀ j < k, ∀ o ∈ Rule.fields,
      erRd m' (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + o) =
        erRd m (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + o)) →
      ruleWords m' ro k = ruleWords m ro k
  | _, 0, _ => rfl
  | ro, k + 1, h => by
    simp only [ruleWords, hI]
    congr 1
    · exact recImgOf_congr (fun o ho => by simpa using h 0 (by omega) o ho)
    · exact ruleWords_congr hI (ro + 1) k (fun j hj o ho => by
        have e : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by
          rw [UInt64.ofNat_add]; ac_rfl
        rw [e]; exact h (j + 1) (by omega) o ho)

/-- `EREC⦃x⦄` across an image's stores elsewhere. -/
theorem erRd_wrERo_ne : ∀ (ws : List (Option Word)) (m : Mem) (q x : Word), ErApart q ws.length x →
    erRd (wrERo m q ws) x = erRd m x
  | [], _, _, _, _ => rfl
  | none :: ws, m, q, x, h => by
    simp only [wrERo]
    exact erRd_wrERo_ne ws _ (q + 1) x (fun j hj => by
      have := h (j + 1) (by simp; omega)
      rwa [show q + UInt64.ofNat (j + 1) = q + 1 + UInt64.ofNat j by rw [UInt64.ofNat_add]; ac_rfl] at this)
  | some w :: ws, m, q, x, h => by
    simp only [wrERo]
    rw [erRd_wrERo_ne ws _ (q + 1) x (fun j hj => by
      have := h (j + 1) (by simp; omega)
      rwa [show q + UInt64.ofNat (j + 1) = q + 1 + UInt64.ofNat j by rw [UInt64.ofNat_add]; ac_rfl] at this)]
    exact erRd_erecPutMem_ne (by simpa using h 0 (by simp))

theorem cpMem_frame (m : Mem) (b old : Word) : MemFrame [EREC, tier1 EREC] [] m (cpMem m b old) := by
  simp only [cpMem]
  repeat' refine MemFrame.trans ?_ (erecPutMem_frame _ _ _)
  exact MemFrame.refl _ _ _

theorem cpMem_eq {m : Mem} {b old : Word}
    (hfr : ∀ o ∈ Rule.fields, ErApart b Rule.size.toNat (old + o)) :
    cpMem m b old = wrERo m b (recImgOf m old) := by
  have hA : ∀ o ∈ Rule.fields, ∀ j : Word, j.toNat < Rule.size.toNat →
      erTier (old + o) ≠ erTier (b + j) ∨ erOff (old + o) ≠ erOff (b + j) := by
    intro o ho j hj
    simpa using hfr o ho j.toNat hj
  have hA0 : ∀ o ∈ Rule.fields, erTier (old + o) ≠ erTier b ∨ erOff (old + o) ≠ erOff b :=
    fun o ho => by simpa using hA o ho 0 (by decide)
  have h0 : ∀ j : Word, j.toNat < Rule.size.toNat → erTier old ≠ erTier (b + j) ∨ erOff old ≠ erOff (b + j) :=
    fun j hj => by simpa using hA Rule.ctor (by simp [Rule.fields]) j hj
  have h00 : erTier old ≠ erTier b ∨ erOff old ≠ erOff b := by simpa using h0 0 (by decide)
  simp only [cpMem]
  -- the reads first (each at a word outside the record), then the stores in field order
  simp (disch := first
    | exact h00
    | exact h0 _ (by decide)
    | exact hA0 _ (by simp [Rule.fields])
    | exact hA _ (by simp [Rule.fields]) _ (by decide)) only [erRd_erecPutMem_ne]
  -- the image's entries in order (the layout's numbers: a whole-record writer)
  simp [wrERo, recImgOf, Rule.img, recImg, rec_unfold, UInt64.add_assoc]

theorem rteGoW_mem : ∀ (n : Nat) (m m' : Mem) (b ro rl : Word) (r : List Word),
    rteGoW n m b ro rl = some (r, m') →
    (∀ j < rl.toNat, ∀ o ∈ Rule.fields,
      ErApart b (Rule.size.toNat * rl.toNat) (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + o)) →
    m' = wrERo m b (ruleWords m ro rl.toNat)
  | 0, _, _, _, _, _, _, h, _ => by simp [rteGoW] at h
  | n + 1, m, m', b, ro, rl, r, h, hfr => by
    by_cases h0 : rl = 0
    · rw [rteGoW.arm1 (hc1 := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      subst h0; rw [← h.2]; simp [ruleWords, wrERo]
    rw [rteGoW.arm2 (hc1 := h0)] at h
    rcases h1 : rcpW m b (rdW (m.arr64 IW) ro) with _ | ⟨r1, m1⟩ <;>
      simp only [h1, rteGoW.k_rule_copy.none, reduceCtorEq] at h
    rw [rteGoW.k_rule_copy.arm1] at h
    obtain rfl := rcpW_some h1
    have hl0 : rl.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
    have hl1 : (rl - 1).toNat = rl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    rcases h2 : rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + Rule.size) (ro + 1) (rl - 1) with
      _ | ⟨r2, m2⟩ <;> simp only [h2, rteGoW.k_rules_to_erec_go, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    have hsrc : ∀ j, ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := fun j => by
      rw [UInt64.ofNat_add]; ac_rfl
    have hmul : Rule.size.toNat ≤ Rule.size.toNat * rl.toNat := Nat.le_mul_of_pos_right _ (by omega)
    have hfr0 : ∀ o ∈ Rule.fields, ErApart b Rule.size.toNat (rdW (m.arr64 IW) ro + o) := fun o ho => by
      have := hfr 0 (by omega) o ho
      simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at this
      exact this.mono hmul
    rw [cpMem_eq hfr0] at h2
    have hI : (wrERo m b (recImgOf m (rdW (m.arr64 IW) ro))).arr64 IW = m.arr64 IW :=
      (wrERo_frame _ m b).arr IW (by decide) (by decide)
    have hsz : b + Rule.size = b + UInt64.ofNat Rule.size.toNat := by rw [UInt64.ofNat_toNat]
    have hk : Rule.size.toNat * rl.toNat = Rule.size.toNat + Rule.size.toNat * (rl.toNat - 1) := by
      calc Rule.size.toNat * rl.toNat = Rule.size.toNat * ((rl.toNat - 1) + 1) := by congr 1; omega
        _ = _ := by rw [Nat.mul_add_one]; omega
    have ih := rteGoW_mem n _ m2 (b + Rule.size) (ro + 1) (rl - 1) r2 h2 (fun j hj o ho => by
      rw [hI, hsrc, hsz]
      exact ErApart.shift (by rw [hl1] at hj ⊢; rw [← hk]; exact hfr (j + 1) (by omega) o ho))
    rw [ih, hl1, ruleWords_congr hI (ro + 1) (rl.toNat - 1) (fun j hj o ho => by
      rw [hsrc]
      exact erRd_wrERo_ne _ _ _ _ ((hfr (j + 1) (by omega) o ho).mono (by rw [recImgOf_length]; exact hmul)))]
    conv => rhs; rw [show rl.toNat = (rl.toNat - 1) + 1 by omega]
    simp only [ruleWords]
    rw [wrERo_append, recImgOf_length, ← hsz]

theorem mapM_range_some {α : Type} : ∀ (xs : List α) (f : Nat → Option α),
    (∀ j (hj : j < xs.length), f j = some xs[j]) → (List.range xs.length).mapM f = some xs
  | [], f, _ => rfl
  | x :: xs, f, h => by
    simp only [List.length_cons, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
    have h0 : f 0 = some x := h 0 (by simp)
    have ih := mapM_range_some xs (f ∘ Nat.succ) (fun j hj => h (j + 1) (by simp; omega))
    simp only [h0, Option.bind_eq_bind, Option.bind_some]
    rw [ih]; rfl

/-- **`rules_to_erec` under the stage relation**: a fresh run of copies of the rule records (every
source record's fields in the record pool), decoding as the rules. -/
theorem rteW_ok {vis : Word} {fe : IFEnv} (n : Nat) {m m' : Mem} {a : AState} {ro rl : Word}
    {r : List Word} {rules : List IRecRule}
    (h : rteW n m ro rl = some (r, m')) (hS : StageR vis fe m a)
    (hd : decPL m (rlDec m) ro.toNat rl.toNat = some rules)
    (hall : ∀ j < rl.toNat, ∀ v, iwN m (ro.toNat + j) = some v → ∀ i < Rule.size.toNat,
      ∃ w, erecP m (v + i) = some w) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r.tail.headD 0 = rl ∧
      decRules (erecP m') (r.headD 0).toNat rl.toNat = some rules := by
  obtain _ | n := n
  · simp [rteW] at h
  by_cases hbig : 4294967296 ≤ rl
  · rw [rteW.abort1 (hc1 := hbig)] at h; cases h
  rw [rteW.arm1 (hc1 := hbig)] at h
  have hrl : rl.toNat < 2 ^ 32 := by rw [UInt64.le_iff_toNat_le] at hbig; simp at hbig; omega
  rcases ha : erAllocW m (rl * Rule.size) with _ | ⟨b, m1⟩ <;>
    simp only [ha, rteW.k_erec_alloc, reduceCtorEq] at h
  rcases h1 : rteGoW n m1 b ro rl with _ | ⟨r1, m2⟩ <;>
    simp only [h1, rteW.k_rules_to_erec_go, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hmul := Nat.mul_le_mul_right rl.toNat Rule.size_le
  have hk : (rl * Rule.size).toNat = Rule.size.toNat * rl.toNat := by
    rw [UInt64.toNat_mul, Nat.mul_comm]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨-, hf1, -⟩ := erAllocW_spec ha hS.iw
  have hI1 : m1.arr64 IW = m.arr64 IW := hf1.arr IW (by simp) (by decide)
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  have hsz := hS.iw.iwSize
  have hfo : ∀ o ∈ Rule.fields, o.toNat < Rule.size.toNat := fun o ho => by
    simp only [Rule.fields, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  -- the source records: their pointers, their fields' words in the old pool
  have hsrc : ∀ j < rl.toNat, ∃ v, iwN m (ro.toNat + j) = some v ∧
      rdW (m.arr64 IW) (ro + UInt64.ofNat j) = UInt64.ofNat v ∧ (UInt64.ofNat v : Word).toNat = v := by
    intro j hj
    obtain ⟨v, -, hv, -, -⟩ := decPL_get rl.toNat ro.toNat rules hd j hj
    obtain ⟨e, hlt⟩ := iwN_rdW_at (w := ro) (k := j) hv hsz
    exact ⟨v, hv, e, UInt64.toNat_ofNat_of_lt' hlt⟩
  have hword : ∀ j < rl.toNat, ∀ o ∈ Rule.fields, ∃ v w, iwN m (ro.toNat + j) = some v ∧
      erecP m (v + o.toNat) = some w ∧
      erRd m (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + o) = w ∧
      (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + o).toNat = v + o.toNat := by
    intro j hj o ho
    obtain ⟨v, hv, e, hvv⟩ := hsrc j hj
    obtain ⟨w, hw⟩ := hall j hj v hv o.toNat (hfo o ho)
    rw [← hvv] at hw
    have ht := rd_off_toNat (erRdOK m) hw
    refine ⟨v, w, hv, by rw [← hvv]; exact hw, by rw [e]; exact (erRdOK m).off hw rfl, by rw [e, ht, hvv]⟩
  have hfr : ∀ j < rl.toNat, ∀ o ∈ Rule.fields,
      ErApart b (Rule.size.toNat * rl.toNat) (rdW (m1.arr64 IW) (ro + UInt64.ofNat j) + o) := by
    intro j hj o ho k hk'
    obtain ⟨v, w, -, hw, -, ht⟩ := hword j hj o ho
    rw [hI1]
    exact erFresh ha hS.iw (x := rdW (m.arr64 IW) (ro + UInt64.ofNat j) + o)
      (by rw [ht]; exact hw) (by rw [hk]; exact hk')
  have hm2 := rteGoW_mem n m1 m2 b ro rl r1 h1 hfr
  subst hm2
  have hrw : ruleWords m1 ro rl.toNat = ruleWords m ro rl.toNat :=
    ruleWords_congr hI1 ro rl.toNat (fun _ _ _ _ => hr1 _)
  rw [hrw]
  obtain ⟨hS1, hg1, -, -, -, -, hget1⟩ := erRecO_stage ha hS (ruleWords m ro rl.toNat)
    (by rw [ruleWords_length, hk])
  refine ⟨hS1, hg1, rfl, ?_⟩
  simp only [List.headD_cons]
  generalize hM : wrERo m1 b (ruleWords m ro rl.toNat) = M at hS1 hg1 hget1 ⊢
  have hlen := decPL_length (m := m) hd
  unfold decRules
  rw [← hlen]
  apply mapM_range_some
  intro j hj
  rw [hlen] at hj
  obtain ⟨v, rlj, hvj, hfj, hgj⟩ := decPL_get rl.toNat ro.toNat rules hd j hj
  have hrj : rules[j] = rlj := by
    rw [List.getElem?_eq_getElem (by omega)] at hgj; exact Option.some.inj hgj
  rw [hrj]
  -- `rules_to_erec` copies each record's fields
  refine decRule_congrF (fun o ho w hw => ?_) (IWGrow.ext hg1) hfj
  obtain ⟨v', w', hv', hw', hrd, -⟩ := hword j hj o ho
  rw [hvj] at hv'; cases hv'
  rw [hw] at hw'; cases hw'
  rw [Nat.add_assoc, hget1 _ _ (ruleWords_get m ro rl.toNat j hj ho), hrd]

/-! ## `rec_info_rec` -/

l_model ri_spec (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.rir ↦ riW]
  specs [erecAlloc_specW p hL.tsr.ea n, erecPut_specM p hpu n]
  grind [arena_grind]

/-- `riW` by its memory `recInfoMem`. -/
theorem riW_eq (m : Mem) (cv mi rp isK reo rel : Word) : riW m cv mi rp isK reo rel =
    match erAllocW m CI.recSize with
    | none => none
    | some (q, m1) =>
      if 4294967296 ≤ erRd (recInfoMem m1 q cv mi rp isK reo rel) (q + (CI.cv + CV.name)) then none
      else some (q, recInfoMem m1 q cv mi rp isK reo rel) := by
  rw [riW.arm1]; rcases erAllocW m CI.recSize with _ | ⟨q, m1⟩ <;> rfl

/-- **`rec_info_rec` under the stage relation**: a fresh `.recInfo` record of the constant at `cq`,
its K flag `isK != 0` and its rules the run `(reo, rel)`. -/
theorem riRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq mi rp isK reo rel q : Word} {cv : IConstantVal} {rules : List IRecRule}
    (h : riW m cq mi rp isK reo rel = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv)
    (hru : decRules (erecP m) reo.toNat rel.toNat = some rules) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat = some (.recInfo cv mi.toNat rp.toNat (isK != 0) rules) := by
  rcases h1 : erAllocW m CI.recSize with _ | ⟨q1, m1⟩
  · simp [riW_eq, h1] at h
  have e : riW m cq mi rp isK reo rel = if 4294967296 ≤ erRd (recInfoMem m1 q1 cq mi rp isK reo rel) (q1 + (CI.cv + CV.name))
      then none else some (q1, recInfoMem m1 q1 cq mi rp isK reo rel) := by simp [riW_eq, h1]
  rw [e] at h
  split at h
  · cases h
  obtain ⟨rfl, rfl⟩ : q1 = q ∧ recInfoMem m1 q1 cq mi rp isK reo rel = m' := by simpa using h
  exact recInfo_stage h1 hS hcv hru

/-! ## The `abstract1` memo -/

theorem rteGoW_afr : ∀ (n : Nat) (m m' : Mem) (b ro rl : Word) (r : List Word),
    rteGoW n m b ro rl = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [rteGoW] at h
  | n + 1, m, m', b, ro, rl, r, h => by
    by_cases h0 : rl = 0
    · rw [rteGoW.arm1 (hc1 := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact AFr.refl _
    rw [rteGoW.arm2 (hc1 := h0)] at h
    rcases h1 : rcpW m b (rdW (m.arr64 IW) ro) with _ | ⟨r1, m1⟩ <;>
      simp only [h1, rteGoW.k_rule_copy.none, reduceCtorEq] at h
    rw [rteGoW.k_rule_copy.arm1] at h
    obtain rfl := rcpW_some h1
    rcases h2 : rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + Rule.size) (ro + 1) (rl - 1) with _ | ⟨r2, m2⟩ <;> simp only [h2, rteGoW.k_rules_to_erec_go, reduceCtorEq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    exact (AFr.of_frame (cpMem_frame m b (rdW (m.arr64 IW) ro))).trans (rteGoW_afr n _ _ _ _ _ _ h2)

theorem rteW_afr {n : Nat} {m m' : Mem} {ro rl : Word} {r : List Word}
    (h : rteW n m ro rl = some (r, m')) : AFr m m' := by
  obtain _ | n := n
  · simp [rteW] at h
  by_cases hb : 4294967296 ≤ rl
  · rw [rteW.abort1 (hc1 := hb)] at h; cases h
  rw [rteW.arm1 (hc1 := hb)] at h
  rcases h1 : erAllocW m (rl * Rule.size) with _ | ⟨b, m1⟩ <;> simp only [h1, rteW.k_erec_alloc, reduceCtorEq] at h
  rcases h2 : rteGoW n m1 b ro rl with _ | ⟨r2, m2⟩ <;> simp only [h2, rteW.k_rules_to_erec_go, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (erAllocW_afr h1).trans (rteGoW_afr n _ _ _ _ _ _ h2)

theorem recInfoMem_frame (m : Mem) (q cv mi rp isK reo rel : Word) :
    MemFrame [EREC, tier1 EREC] [] m (recInfoMem m q cv mi rp isK reo rel) := by
  simp only [recInfoMem]
  repeat' refine MemFrame.trans ?_ (erecPutMem_frame _ _ _)
  exact MemFrame.refl _ _ _

theorem riW_afr {m m' : Mem} {cv mi rp isK reo rel q : Word}
    (h : riW m cv mi rp isK reo rel = some (q, m')) : AFr m m' := by
  simp only [riW_eq] at h
  split at h; · cases h
  rename_i q1 m1 h1
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact (erAllocW_afr h1).trans (AFr.of_frame (recInfoMem_frame _ _ _ _ _ _ _ _))

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem decRR_mono (p : Nat) : OMono (fun m => decRR m p) := by
  unfold decRR
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.decHL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply decTM_mono
    | apply OMono.bind
    | intro _)

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The major index and rule prefix of recursor `r` -/

def bmjW (m : Mem) (q r : Word) : Word :=
  if rdW (m.arr64 IW) (q + 3) ≤ r then 0
  else rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (q + 2) + r) + 2)

def brpW (m : Mem) (q r : Word) : Word :=
  if rdW (m.arr64 IW) (q + 3) ≤ r then 0
  else rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (q + 2) + r) + 1)

theorem mj_spec (p : Prog) (hp : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt) (n : Nat)
    (s₀ : St) (q r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_major_idx_at" [q, r]
    ⦃fun res s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ res.headD 0 = bmjW s₀.mem q r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeMajorIdxAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [bmjW, rdW_eq]

theorem rp_spec (p : Prog) (hp : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt) (n : Nat)
    (s₀ : St) (q r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_rule_prefix_at" [q, r]
    ⦃fun res s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ res.headD 0 = brpW s₀.mem q r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeRulePrefixAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [brpW, rdW_eq]

/-- The models at a shape record decoded below the tops. -/
theorem bmjW_rpW_eq {m : Mem} {q r : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m q.toNat) m bs)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (bmjW m q r).toNat = bs.majorIdxAt r.toNat ∧ (brpW m q r).toNat = bs.rulePrefixAt r.toNat := by
  have h' : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨-, hrecs, -⟩ := decBS_some h'
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hrecs
  obtain ⟨-, hom⟩ := L.Ind.iwN_truncM_some ho
  obtain ⟨hlt3, hlm⟩ := L.Ind.iwN_truncM_some hl
  obtain ⟨e2, t2⟩ := rec2RdN (w := q) (k := 2) hom hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := q) (k := 3) (by simpa using hlm) hsz
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at e2 e3
  have hlen := decPL_length (truncM m) hd
  unfold bmjW brpW BlockShape.majorIdxAt BlockShape.rulePrefixAt
  rw [e3, e2]
  by_cases hle : UInt64.ofNat l ≤ r
  · rw [ite_eq_left hle, ite_eq_left hle]
    have : bs.recs[r.toNat]? = none := by
      rw [List.getElem?_eq_none_iff, hlen]; have := UInt64.le_iff_toNat_le.mp hle; rw [t3] at this; exact this
    rw [this]; exact ⟨rfl, rfl⟩
  rw [ite_eq_right hle, ite_eq_right hle]
  have hrl : r.toNat < l := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle); rwa [t3] at this
  obtain ⟨v, rc, hv, hrc, hget⟩ := decPL_get l o bs.recs hd r.toNat hrl
  rw [hget]
  obtain ⟨hvt, hvm⟩ := L.Ind.iwN_truncM_some hv
  have hor : (UInt64.ofNat o + r).toNat = o + r.toNat := by
    rw [UInt64.toNat_add, t2]; exact Nat.mod_eq_of_lt (by
      have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hvt; omega)
  have hrd := iwN_rdW hvm (by have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hvt; omega)
  have e : UInt64.ofNat (o + r.toNat) = UInt64.ofNat o + r := by
    apply UInt64.toNat_inj.mp; rw [hor]; simp; have := (rdW (m.arr64 CTL) 200).toNat_lt
    simp only [iwTop] at hvt; omega
  rw [e] at hrd
  rw [hrd.1]
  obtain ⟨-, hrP, hmI, -, -⟩ := decRS_some hrc
  obtain ⟨-, hrPm⟩ := L.Ind.iwN_truncM_some hrP
  obtain ⟨-, hmIm⟩ := L.Ind.iwN_truncM_some hmI
  have hvv : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd.2
  obtain ⟨e1', t1'⟩ := rec2RdN (w := UInt64.ofNat v) (k := 1) (by rw [hvv]; exact hrPm) hsz
  obtain ⟨e2', t2'⟩ := rec2RdN (w := UInt64.ofNat v) (k := 2) (by rw [hvv]; exact hmIm) hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at e1' e2'
  exact ⟨by rw [e2', t2'], by rw [e1', t1']⟩

/-! ## `rec_k_expected` -/

l_model rk_spec (p : Prog) (hL : CbrLook p)
  fns [hL.rke ↦ rkW ro]
  specs []
  grind [arena_grind]

/-- **`rec_k_expected` is `recKExpected`** at a shape and a target major decoded below the tops. -/
theorem rkW_ok {m : Mem} {p M : Word} {bs : BlockShape} {TM : TargetMajor}
    (hbs : DecB (fun m => decBS m p.toNat) m bs) (hM : DecB (fun m => decTM m M.toNat) m TM)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ w, rkW m p M = some w ∧ (w != 0) = ConRon.Arena.recKExpected bs TM := by
  have hM0 : decTM (truncM m) M.toNat = some TM := hM
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hM0
  obtain ⟨i0, -, l0, -, ds0, -, nP, -, nI, -, cs, hcs, k8, hk8, nfs0, -, pf0, -, hTM⟩ := hM0
  have eCs : TM.ctors = cs := by rw [← hTM]
  have eMem : TM.member = decON k8 := by rw [← hTM]
  obtain ⟨co, cl, hco, hcl, hcsd⟩ := decAt_some hcs
  obtain ⟨-, hcom⟩ := L.Ind.iwN_truncM_some hco
  obtain ⟨-, hclm⟩ := L.Ind.iwN_truncM_some hcl
  obtain ⟨-, hk8m⟩ := L.Ind.iwN_truncM_some hk8
  obtain ⟨e6, t6⟩ := rec2RdN (w := M) (k := 6) hcom hsz
  obtain ⟨e7, t7⟩ := rec2RdN (w := M) (k := 7) (by simpa [Nat.add_assoc] using hclm) hsz
  obtain ⟨e8, t8⟩ := rec2RdN (w := M) (k := 8) hk8m hsz
  simp only [show UInt64.ofNat 6 = (6 : Word) from rfl, show UInt64.ofNat 7 = (7 : Word) from rfl,
    show UInt64.ofNat 8 = (8 : Word) from rfl] at e6 e7 e8
  have hbs0 : decBS (truncM m) p.toNat = some bs := hbs
  obtain ⟨hmem, -, -, -, -, -, hprop⟩ := decBS_some hbs0
  obtain ⟨mo, ml, -, hml, hmd⟩ := decAt_some hmem
  obtain ⟨-, hmlm⟩ := L.Ind.iwN_truncM_some hml
  obtain ⟨e1, t1⟩ := rec2RdN (w := p) (k := 1) hmlm hsz
  have ek : bs.k = ml := by
    have := decPL_length _ hmd; simp only [BlockShape.k]; exact this
  have eP := installIwB (k := 8) hprop hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 8 = (8 : Word) from rfl] at e1 eP
  unfold rkW ConRon.Arena.recKExpected
  rw [e8, e7, eMem, eCs]
  by_cases hk0 : k8 = 0
  · subst hk0
    exact ⟨0, by simp, by simp [decON]⟩
  have hk8' : UInt64.ofNat k8 ≠ (0 : Word) := fun e => hk0 (by rw [← t8, e]; rfl)
  simp only [hk8', ↓reduceIte]
  have hlen : cs.length = cl := decPL_length _ hcsd
  by_cases hc1 : cl = 1
  · subst hc1
    obtain ⟨cp, c, ys, rfl, hcp, hc, hys⟩ := decPL_cons (l := 0) hcsd
    have : ys = [] := by have := decPL_length _ hys; simpa using this
    subst this
    obtain ⟨-, hcpm⟩ := L.Ind.iwN_truncM_some (i := (UInt64.ofNat co : Word).toNat + 0) (by rw [t6]; simpa using hcp)
    obtain ⟨e9, t9⟩ := rec2RdN (w := UInt64.ofNat co) (k := 0) hcpm hsz
    simp only [decCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨_, -, cv, -, nF, hnF, hceq⟩ := hc
    subst hceq
    obtain ⟨-, hnFm⟩ := L.Ind.iwN_truncM_some (i := (UInt64.ofNat cp : Word).toNat + 1) (by rw [t9]; exact hnF)
    obtain ⟨e10, t10⟩ := rec2RdN (w := UInt64.ofNat cp) (k := 1) hnFm hsz
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
      UInt64.add_zero] at e9 e10
    have h1' : ¬ (UInt64.ofNat 1 : Word) ≠ 1 := by decide
    simp only [h1', ↓reduceIte]
    rw [e6, e9, e10, e1]
    refine ⟨_, rfl, ?_⟩
    simp only [decON, hk0, ite_false, ek]
    rw [← eP, ← t1, ← t10]
    generalize (UInt64.ofNat ml : Word) = a
    generalize (UInt64.ofNat nF : Word) = b
    generalize rdW (m.arr64 IW) (p + 8) = c
    have ha' : a.toNat = 1 ↔ a = 1 := by rw [← UInt64.toNat_inj]; rfl
    have hb' : b.toNat = 0 ↔ b = 0 := by rw [← UInt64.toNat_inj]; rfl
    by_cases ha : a = 1 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> simp [ha, hb, hc, ha', hb']
  · have h7 : (UInt64.ofNat cl : Word) ≠ 1 := by
      intro e; apply hc1; rw [← t7, e]; rfl
    simp only [ne_eq, h7, not_false_eq_true, ↓reduceIte]
    refine ⟨0, rfl, ?_⟩
    simp only [decON, hk0, ite_false]
    match cs, hlen with
    | [], _ => rfl
    | [_], h => exact absurd h.symm hc1
    | _ :: _ :: _, _ => rfl

/-! ## `block_rec_infos_tf` -/

l_model bri_spec (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
  fns [hL.bri ↦ briW list]
  specs [rp_spec p hL.rpa n, tsr_spec p hL.tsr hpu n, mj_spec p hL.mi n, rk_spec p hL n, rte_spec p hL hpu n,
    ri_spec p hL hpu n, slCons_specW p hL.tsr.rc.rx.ha hL.tsr.ic hL.tsr.sc n]
  grind [arena_grind]

/-- A record pointer consed onto a slice of `EREC` record pointers (`sl_cons`). -/
theorem consW_ci {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} {cis : List IConstantInfo} {ci : IConstantInfo}
    (h : consW n m x o l = some (r, m')) (hS : StageR vis fe m a) (hb : o.toNat + l.toNat ≤ iwTop m)
    (hd : decPL m (decCI (erecP m)) o.toNat l.toNat = some cis) (hx : decCI (erecP m) x.toNat = some ci) :
    decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some (ci :: cis) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' ∧ StageR vis fe m' a ∧ IWGrow m m' := by
  rw [decPL_eq_bind] at hd
  rcases hps : decNL m o.toNat l.toNat with _ | ps <;> rw [hps] at hd
  · cases hd
  simp only [Option.bind_some] at hd
  obtain ⟨hS', hg, hd', ht'⟩ := consW_stageN h hS hb hps
  have hext := IWGrow.ext hg
  refine ⟨?_, ht', hS', hg⟩
  rw [decPL_eq_bind, hd']
  simp only [Option.bind_some, List.mapM_cons]
  rw [show decCI (erecP m') x.toNat = some ci from hext.decCI hx,
    ArrExt.mapM (f := decCI (erecP m)) (g := decCI (erecP m')) (fun _ _ hy => hext.decCI hy) _ _ hd]
  rfl

/-- A slice of `EREC` record pointers below the `IW` top, across pool growth. -/
theorem decPL_ci_grow {m m' : Mem} (hg : IWGrow m m') {o l : Nat} {cis : List IConstantInfo}
    (hb : o + l ≤ iwTop m) (hd : decPL m (decCI (erecP m)) o l = some cis) :
    decPL m' (decCI (erecP m')) o l = some cis := by
  rw [decPL_eq_bind] at hd ⊢
  rcases hps : decNL m o l with _ | ps <;> rw [hps] at hd
  · cases hd
  have hps' : decNL m' o l = some ps := by
    rw [← hps]; simp only [decNL]; apply L.Ind.mapM_congr_of; intro j hj
    simp only [iwN, nat?, iwA, aread_apply, aread_apply]; rw [hg.iwGet _ (by simp at hj; omega)]
  rw [hps']
  simp only [Option.bind_some] at hd ⊢
  exact ArrExt.mapM (fun _ _ hy => (IWGrow.ext hg).decCI hy) _ _ hd

/-- **`block_rec_infos_tf` refines `blockRecInfosTF`**: the records at the returned slice of
`EREC` pointers. -/
theorem briW_ok (n : Nat) : ∀ {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {pp mm lo ll : Word} {r : List Word} {bs : BlockShape} {xs : List (IConstantVal × TargetMajor × List EIdx)},
    briW n m pp mm lo ll = some (r, m') → StageR vis fe m a →
    DecB (fun m => decBS m pp.toNat) m bs → PSlR decRR xs lo ll m → mm.toNat + ll.toNat < 2 ^ 64 →
    AbsOK m →
    ∃ infos a', (ConRon.Arena.blockRecInfosTF bs mm.toNat xs).run a = .ok (infos, a') ∧
      decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some infos ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a vis fe pp mm lo ll r bs xs h; simp [briW] at h
  | succ n ih =>
  intro m m' a vis fe pp mm lo ll r bs xs h hS hbs hxs hml hA
  by_cases hl : ll = 0
  · rw [briW.arm1 n m pp mm lo ll hl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : xs = [] := by
      have := decPL_length _ (hxs.1.get (OMono.decPL decRR_mono _ _)); simpa using this
    subst this
    exact ⟨[], a, rfl, by simp [decPL], by simp, hS, IWGrow.refl _, hA⟩
  rw [briW.arm2 n m pp mm lo ll hl] at h
  have hsz := hS.iw.iwSize
  obtain ⟨x, ys, rfl, hx, hys⟩ := hxs.uncons hl hsz
  obtain ⟨cvv, TM, rhss⟩ := x
  generalize hT : rdW (m.arr64 IW) lo = trip at h hx
  -- the record's fields
  have hx' : decRR (truncM m) trip.toNat = some (cvv, TM, rhss) := hx
  simp only [decRR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hx'
  obtain ⟨cvp, hcvp, cv', hcv', mp, hmp, TM', hTM', rh', hrh', he⟩ := hx'
  simp only [Prod.mk.injEq] at he; obtain ⟨e1', e2', e3'⟩ := he
  rw [e1'] at hcv'; rw [e2'] at hTM'; rw [e3'] at hrh'
  obtain ⟨-, hcvpm⟩ := L.Ind.iwN_truncM_some (i := trip.toNat + 0) (by simpa using hcvp)
  obtain ⟨e0, t0⟩ := rec2RdN (w := trip) (k := 0) hcvpm hsz
  obtain ⟨-, hmpm⟩ := L.Ind.iwN_truncM_some hmp
  obtain ⟨e1, t1⟩ := rec2RdN (w := trip) (k := 1) hmpm hsz
  obtain ⟨o, l, ho, hl', hd⟩ := decAt_some hrh'
  obtain ⟨-, hom⟩ := L.Ind.iwN_truncM_some ho
  obtain ⟨-, hlm⟩ := L.Ind.iwN_truncM_some hl'
  obtain ⟨e2, t2⟩ := rec2RdN (w := trip) (k := 2) hom hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := trip) (k := 3) (by simpa [Nat.add_assoc] using hlm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
    show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl, UInt64.add_zero] at e0 e1 e2 e3
  rw [e0, e1, e2, e3] at h
  have hM : DecB (fun m => decTM m (UInt64.ofNat mp : Word).toNat) m TM := by
    show decTM (truncM m) _ = some TM; rw [t1]; exact hTM'
  have hrh : DecB (fun m => decHL m (UInt64.ofNat o : Word).toNat (UInt64.ofNat l : Word).toNat) m rhss := by
    show decHL (truncM m) _ _ = some rhss; rw [t2, t3]; exact hd
  have hcvE : decCV (erecP m) (UInt64.ofNat cvp : Word).toNat = some cvv := by rw [t0]; exact decCVp_truncM hcv'
  obtain ⟨-, hrp⟩ := bmjW_rpW_eq (r := mm) hbs hsz
  -- the generated rules
  rcases h1 : tsrW n m (brpW m pp mm) (UInt64.ofNat mp) (UInt64.ofNat o) (UInt64.ofNat l) with _ | ⟨rr, m1⟩
  · rw [h1, briW.k_generated_rules.none] at h; cases h
  rw [h1, briW.k_generated_rules.arm1] at h
  obtain ⟨rules, a1, run1, hd1, hR1, hb1, hS1, hg1, hA1⟩ := tsrW_ok fe vis n h1 hS hM hrh hA
  rw [hrp] at run1
  -- the tail's records
  have hl0 : ll.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
  have hmm1 : (mm + 1).toNat = mm.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hll1 : (ll - 1).toNat = ll.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  rcases h2 : briW n m1 pp (mm + 1) (lo + 1) (ll - 1) with _ | ⟨ri, m2⟩
  · rw [h2] at h; simp [briW.k_block_rec_infos_tf] at h
  rw [h2, briW.k_block_rec_infos_tf.arm1] at h
  obtain ⟨infos, a2, run2, hd2, hb2, hS2, hg2, hA2⟩ := ih h2 hS1 (hbs.grow (decBS_mono _) hg1)
    (hys.grow (fun q => decRR_mono q) hg1) (by rw [hmm1, hll1]; omega) hA1
  rw [hmm1] at run2
  -- the K flag, the major index
  have hsz2 := hS2.iw.iwSize
  have hg12 := hg1.trans hg2
  obtain ⟨isK, hk, hkE⟩ := rkW_ok (hbs.grow (decBS_mono _) hg12) (hM.grow (decTM_mono _) hg12) hsz2
  obtain ⟨hmj, -⟩ := bmjW_rpW_eq (r := mm) (hbs.grow (decBS_mono _) hg12) hsz2
  rw [hk, briW.k_rec_k_expected.arm1] at h
  -- the rules copied
  rcases h3 : rteW n m2 (rr.headD 0) (rr.tail.headD 0) with _ | ⟨re, m3⟩
  · rw [h3] at h; simp [briW.k_rules_to_erec] at h
  rw [h3, briW.k_rules_to_erec.arm1] at h
  obtain ⟨hS3, hg3, hrl3, hru3⟩ := rteW_ok n h3 hS2 (decPL_rl_grow hg2 hb1 hd1) (hR1.grow hg2 hb1)
  rw [← hrl3] at hru3
  -- the record
  rcases h4 : riW m3 (UInt64.ofNat cvp) (bmjW m2 pp mm) (brpW m pp mm) isK (re.headD 0) (re.tail.headD 0)
    with _ | ⟨q, m4⟩
  · rw [h4] at h; simp [briW.k_rec_info_rec] at h
  rw [h4, briW.k_rec_info_rec.arm1] at h
  have hg13 := hg12.trans hg3
  obtain ⟨hS4, hg4, hci⟩ := riRec_stage h4 hS3 ((IWGrow.ext hg13).decCV hcvE) hru3
  -- consed
  rcases h5 : consW n m4 q (ri.headD 0) (ri.tail.headD 0) with _ | ⟨r5, m5⟩
  · rw [h5] at h; simp [briW.k_sl_cons] at h
  rw [h5, briW.k_sl_cons.arm1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hg34 := hg3.trans hg4
  obtain ⟨hd5, hb5, hS5, hg5⟩ := consW_ci h5 hS4 (by have := hg34.iw; omega)
    (decPL_ci_grow hg34 hb2 hd2) hci
  refine ⟨_, a2, ?_, by simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega, hS5, hg13.trans (hg4.trans hg5),
    consW_afr h5 (riW_afr h4 (rteW_afr h3 hA2))⟩
  simp only [ConRon.Arena.blockRecInfosTF, StateT.run_bind, run1, except_ok_bind, run2]
  rw [hmj, hrp, hkE]
  rfl

/-- **`block_rec_infos_tf` refines `blockRecInfosTF`**: the shape and the family's `rec4` records
decoded below the tops; the records (each recursor at its record's major index and rule prefix, its
K flag `rec_k_expected`, its rules at its major by `generated_rules`) at the returned slice of
`EREC` pointers. -/
@[refines ConRon.Arena.blockRecInfosTF]
theorem blockRecInfosTF_refines (p : Prog) (hL : CbrLook p) (hpu : p.lookup "erec_put" = some erecPut)
    (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (vis pp mm lo ll : Word) (bs : BlockShape) (xs : List (IConstantVal × TargetMajor × List EIdx))
    (hS : StageR vis fe s₀.mem a₀) (hbs : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hxs : PSlR decRR xs lo ll s₀.mem) (hml : mm.toNat + ll.toNat < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_infos_tf" [pp, mm, lo, ll]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ infos a',
      (ConRon.Arena.blockRecInfosTF bs mm.toNat xs).run a₀ = .ok (infos, a') ∧
      decPL s'.mem (decCI (erecP s'.mem)) (r.headD 0).toNat (r.tail.headD 0).toNat = some infos ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem ∧ StageR vis fe s'.mem a' ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (bri_spec p hL hpu n s₀ pp mm lo ll) fun _ _ ⟨hl, hm⟩ =>
    ⟨hl, briW_ok n hm hS hbs hxs hml hA⟩



end L.Ind

end

end
