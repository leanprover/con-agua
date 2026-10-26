import ConAgua.Arena.RecCheckSpec17
import ConAgua.Arena.IndInstallSpec14

/-!
# `RecCheck`: `consBlockRecsTF` (lane `indproofs3`, helper `rec`)

Each checked recursor with its stored rules (`tgt_stored_rules`, `RecCheckSpec17`) at its major,
the rules copied into one consecutive run (`rules_to_erec`), a fresh `.recInfo` record
(`cons_block_recs_push`) pushed by lane `decls2`'s `env_push`. The rules' lookups at the
constructors' view `vis₂` (the twin's `fe.restrictTo vis₂`: `StageR.restrict`/`unrestrict`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `rules_to_erec` -/

/-- The memory after one record's eleven copies (each copy reads the memory of its time). -/
def cpMem (m : Mem) (b old : Word) : Mem :=
  let m1 := m.set64 EREC b (rdW (m.arr64 EREC) old)
  let m2 := m1.set64 EREC (b + 1) (rdW (m1.arr64 EREC) (old + 1))
  let m3 := m2.set64 EREC (b + 2) (rdW (m2.arr64 EREC) (old + 2))
  let m4 := m3.set64 EREC (b + 3) (rdW (m3.arr64 EREC) (old + 3))
  let m5 := m4.set64 EREC (b + 4) (rdW (m4.arr64 EREC) (old + 4))
  let m6 := m5.set64 EREC (b + 5) (rdW (m5.arr64 EREC) (old + 5))
  let m7 := m6.set64 EREC (b + 6) (rdW (m6.arr64 EREC) (old + 6))
  let m8 := m7.set64 EREC (b + 7) (rdW (m7.arr64 EREC) (old + 7))
  let m9 := m8.set64 EREC (b + 8) (rdW (m8.arr64 EREC) (old + 8))
  let m10 := m9.set64 EREC (b + 9) (rdW (m9.arr64 EREC) (old + 9))
  m10.set64 EREC (b + 10) (rdW (m10.arr64 EREC) (old + 10))

/-- **The model of `rule_copy`.** -/
def rcpW (m : Mem) (b old : Word) : Option (List Word × Mem) := some ([0], cpMem m b old)

def rteK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

/-- **The model of `rules_to_erec_go`** (exec fuel). -/
def rteGoW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, b, ro, rl =>
    if rl = 0 then some ([0], m)
    else rteK1 (rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1))

section arms
variable (n : Nat) (m : Mem) (b ro rl : Word) (r : List Word)
theorem rcW_eq (old : Word) : rcpW m b old = some ([0], cpMem m b old) := rfl
theorem rteGoW_nil (h : rl = 0) : rteGoW (n + 1) m b ro rl = some ([0], m) := by simp [rteGoW, h]
theorem rteGoW_cons (h : ¬ rl = 0) : rteGoW (n + 1) m b ro rl =
    rteK1 (rteGoW n (cpMem m b (rdW (m.arr64 IW) ro)) (b + 11) (ro + 1) (rl - 1)) := by simp [rteGoW, h]
theorem rteK1_some : rteK1 (some (r, m)) = some ([0], m) := rfl
end arms
attribute [ind_grind] rcW_eq rteGoW_nil rteGoW_cons rteK1_some

/-- The lookups of `cons_block_recs_tf`. -/
structure CbrLook (p : Prog) : Prop where
  tsr : TsrLook p
  rp : RecProg p
  rc : p.lookup "rule_copy" = some ruleCopy
  rteg : p.lookup "rules_to_erec_go" = some rulesToErecGo
  rir : p.lookup "rec_info_rec" = some recInfoRec
  rte : p.lookup "rules_to_erec" = some rulesToErec
  push : p.lookup "cons_block_recs_push" = some consBlockRecsPush
  mi : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt
  rpa : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt
  cbr : p.lookup "cons_block_recs_tf" = some consBlockRecsTF

theorem rc_spec (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (b old : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rule_copy" [b, old]
    ⦃fun r s' => LocEq s' s₀ ∧ rcpW s₀.mem b old = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ L.rc]
  simp only [callFn, ruleCopy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [rcpW, cpMem]

theorem rteGo_spec (p : Prog) (L : CbrLook p) (n : Nat) :
    ∀ (s₀ : St) (b ro rl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rules_to_erec_go" [b, ro, rl]
    ⦃fun r s' => LocEq s' s₀ ∧ rteGoW n s₀.mem b ro rl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ b ro rl
    rw [invoke_eq _ L.rteg]; simp only [callFn, rulesToErecGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ b ro rl
    rw [invoke_eq _ L.rteg]
    simp only [callFn, rulesToErecGo]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, rc_spec p L n, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

l_model rte_spec (p : Prog) (hL : CbrLook p)
  fns [hL.rte ↦ rteW]
  specs [erecAlloc_specW p hL.tsr.ea n, rteGo_spec p hL n]
  grind [arena_grind] simp []

/-! ## `rules_to_erec`: the copied run decodes as the rules -/

/-- The eleven words of the record at `old`. -/
def recWords (E : Array Word) (old : Word) : List Word :=
  [rdW E old, rdW E (old + 1), rdW E (old + 2), rdW E (old + 3), rdW E (old + 4), rdW E (old + 5),
    rdW E (old + 6), rdW E (old + 7), rdW E (old + 8), rdW E (old + 9), rdW E (old + 10)]

/-- The words of the records the pointers `IW[ro ‥ ro + k)` point to, in order. -/
def ruleWords (m : Mem) (ro : Word) : Nat → List Word
  | 0 => []
  | k + 1 => recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro) ++ ruleWords m (ro + 1) k

theorem ruleWords_length (m : Mem) : ∀ (ro : Word) (k : Nat), (ruleWords m ro k).length = 11 * k
  | _, 0 => rfl
  | ro, k + 1 => by simp [ruleWords, recWords, ruleWords_length m (ro + 1) k]; omega

set_option maxHeartbeats 2000000 in
theorem cpMem_eq {m : Mem} {b old : Word} (hlt : old.toNat + 11 ≤ b.toNat) (hb : b.toNat + 11 < 2 ^ 64) :
    cpMem m b old = wrER m b (recWords (m.arr64 EREC) old) := by
  have t1 : (b + 1).toNat = b.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have t2 : (b + 2).toNat = b.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have t3 : (b + 3).toNat = b.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have t4 : (b + 4).toNat = b.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have t5 : (b + 5).toNat = b.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have t6 : (b + 6).toNat = b.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have t7 : (b + 7).toNat = b.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have t8 : (b + 8).toNat = b.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have t9 : (b + 9).toNat = b.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have t10 : (b + 10).toNat = b.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  have c1 : (old + 1).toNat = old.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have c2 : (old + 2).toNat = old.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have c3 : (old + 3).toNat = old.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have c4 : (old + 4).toNat = old.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have c5 : (old + 5).toNat = old.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have c6 : (old + 6).toNat = old.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have c7 : (old + 7).toNat = old.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have c8 : (old + 8).toNat = old.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have c9 : (old + 9).toNat = old.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have c10 : (old + 10).toNat = old.toNat + 10 := by rw [UInt64.toNat_add]; simp; omega
  simp only [cpMem, wrER, recWords]
  rw [show b + 1 + 1 = b + 2 by ac_rfl, show b + 2 + 1 = b + 3 by ac_rfl,
    show b + 3 + 1 = b + 4 by ac_rfl, show b + 4 + 1 = b + 5 by ac_rfl,
    show b + 5 + 1 = b + 6 by ac_rfl, show b + 6 + 1 = b + 7 by ac_rfl, show b + 7 + 1 = b + 8 by ac_rfl,
    show b + 8 + 1 = b + 9 by ac_rfl, show b + 9 + 1 = b + 10 by ac_rfl]
  -- The discharger rewrites with `t1 … c10` and clears them before `omega`: twenty chained
  -- `(x + k).toNat` facts in context make each `omega` slow and the module peak at ~10 GB.
  simp (disch := (
    (try simp only [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10])
    clear t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    omega)) only [rdW_set64_ne_er]

theorem rdW_agree {a a' : Array Word} {B : Nat} (hE : ∀ i < B, a'[i]? = a[i]?) {y : Word} (hy : y.toNat < B) :
    rdW a' y = rdW a y := by
  unfold rdW; rw [hE _ hy]

/-- `EREC` below `B` and `IW` agreeing: the record words read the same. -/
theorem ruleWords_congr {m m' : Mem} (hI : m'.arr64 IW = m.arr64 IW) {B : Nat}
    (hE : ∀ i < B, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) :
    ∀ (ro : Word) (k : Nat), (∀ j < k, (rdW (m.arr64 IW) (ro + UInt64.ofNat j)).toNat + 11 ≤ B) →
      ruleWords m' ro k = ruleWords m ro k
  | _, 0, _ => rfl
  | ro, k + 1, h => by
    simp only [ruleWords, hI]
    have h0 := h 0 (by omega)
    simp only [show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero] at h0
    have hr : ∀ i : Nat, i ≤ 10 → rdW (m'.arr64 EREC) (rdW (m.arr64 IW) ro + UInt64.ofNat i) =
        rdW (m.arr64 EREC) (rdW (m.arr64 IW) ro + UInt64.ofNat i) := fun i hi =>
      rdW_agree hE (by rw [UInt64.toNat_add]; simp; omega)
    congr 1
    · simp only [recWords]
      have := hr 0 (by omega); have := hr 1 (by omega); have := hr 2 (by omega); have := hr 3 (by omega)
      have := hr 4 (by omega); have := hr 5 (by omega); have := hr 6 (by omega); have := hr 7 (by omega)
      have := hr 8 (by omega); have := hr 9 (by omega); have := hr 10 (by omega)
      simp_all
    · exact ruleWords_congr hI hE (ro + 1) k (fun j hj => by
        have e : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by
          rw [UInt64.ofNat_add]; ac_rfl
        rw [e]; exact h (j + 1) (by omega))


theorem ruleWords_get (m : Mem) : ∀ (ro : Word) (k j i : Nat), j < k → i < 11 →
    (ruleWords m ro k)[11 * j + i]? = some (rdW (m.arr64 EREC) (rdW (m.arr64 IW) (ro + UInt64.ofNat j) + UInt64.ofNat i))
  | _, 0, _, _, hj, _ => absurd hj (by omega)
  | ro, k + 1, 0, i, _, hi => by
    simp only [ruleWords, Nat.mul_zero, Nat.zero_add, show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero]
    rw [List.getElem?_append_left (by simp [recWords]; omega)]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [recWords] <;> rfl
  | ro, k + 1, j + 1, i, hj, hi => by
    simp only [ruleWords]
    rw [List.getElem?_append_right (by simp [recWords]; omega)]
    have e : 11 * (j + 1) + i - (recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro)).length = 11 * j + i := by
      simp [recWords]; omega
    rw [e, ruleWords_get m (ro + 1) k j i (by omega) hi]
    have e2 : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by rw [UInt64.ofNat_add]; ac_rfl
    rw [e2]

theorem rteGoW_mem (n : Nat) : ∀ (m m' : Mem) (b ro rl : Word) (r : List Word),
    rteGoW n m b ro rl = some (r, m') →
    (∀ j < rl.toNat, (rdW (m.arr64 IW) (ro + UInt64.ofNat j)).toNat + 11 ≤ b.toNat) →
    b.toNat + 11 * rl.toNat ≤ (m.arr64 EREC).size → (m.arr64 EREC).size < 2 ^ 64 →
    m' = wrER m b (ruleWords m ro rl.toNat) := by
  induction n with
  | zero => intro m m' b ro rl r h; simp [rteGoW] at h
  | succ n ih =>
  intro m m' b ro rl r h hold hsz hEs
  by_cases h0 : rl = 0
  · rw [rteGoW_nil (h := h0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
    subst h0; rfl
  rw [rteGoW_cons (h := h0)] at h
  have hl0 : rl.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
  have h00 := hold 0 (by omega)
  simp only [show (UInt64.ofNat 0 : Word) = 0 from rfl, UInt64.add_zero] at h00
  have hb11 : b.toNat + 11 < 2 ^ 64 := by omega
  rw [cpMem_eq h00 hb11] at h
  rcases h1 : rteGoW n (wrER m b (recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro))) (b + 11) (ro + 1) (rl - 1) with _ | ⟨r1, m1⟩ <;> simp only [h1, rteK1, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  generalize hW : wrER m b (recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro)) = W at h1
  have hfr := wrER_frame (recWords (m.arr64 EREC) (rdW (m.arr64 IW) ro)) m b
  rw [hW] at hfr
  have hI : W.arr64 IW = m.arr64 IW := hfr.1 IW (by decide) (by decide)
  have hEsz : (W.arr64 EREC).size = (m.arr64 EREC).size := hfr.2.2.1 EREC
  have hlow : ∀ i < b.toNat, (W.arr64 EREC)[i]? = (m.arr64 EREC)[i]? := fun i hi => by
    rw [← hW, wrER_get _ m b i (by simp [recWords]; omega) hEs]
    rw [ite_eq_right (by omega)]
  have hb1 : (b + 11).toNat = b.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
  have hl1 : (rl - 1).toNat = rl.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have hshift : ∀ j < (rl - 1).toNat, (rdW (W.arr64 IW) (ro + 1 + UInt64.ofNat j)).toNat + 11 ≤ (b + 11).toNat := by
    intro j hj
    have e2 : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by rw [UInt64.ofNat_add]; ac_rfl
    rw [hI, e2, hb1]; have := hold (j + 1) (by omega); omega
  have := ih W m1 (b + 11) (ro + 1) (rl - 1) r1 h1 hshift (by rw [hb1, hEsz, hl1]; omega) (by rw [hEsz]; exact hEs)
  rw [this, hl1]
  have hcong : ruleWords W (ro + 1) (rl.toNat - 1) = ruleWords m (ro + 1) (rl.toNat - 1) :=
    ruleWords_congr hI hlow (ro + 1) _ (fun j hj => by
      have e2 : ro + 1 + UInt64.ofNat j = ro + UInt64.ofNat (j + 1) := by rw [UInt64.ofNat_add]; ac_rfl
      rw [e2]; exact hold (j + 1) (by omega))
  rw [hcong, ← hW]
  obtain ⟨k, hk⟩ : ∃ k, rl.toNat = k + 1 := ⟨rl.toNat - 1, by omega⟩
  rw [hk, show k + 1 - 1 = k from rfl]
  simp only [ruleWords]
  rw [wrER_append]
  rfl

theorem mapM_range_some {α : Type} : ∀ (xs : List α) (f : Nat → Option α),
    (∀ j (hj : j < xs.length), f j = some xs[j]) → (List.range xs.length).mapM f = some xs
  | [], f, _ => rfl
  | x :: xs, f, h => by
    simp only [List.length_cons, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
    have h0 : f 0 = some x := h 0 (by simp)
    have ih := mapM_range_some xs (f ∘ Nat.succ) (fun j hj => h (j + 1) (by simp; omega))
    simp only [h0, Option.bind_eq_bind, Option.bind_some]
    rw [ih]; rfl

end L.Ind
