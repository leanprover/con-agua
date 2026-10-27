import ConAgua.Arena.IndPartsSpec4

/-!
# Refinements of `IndParts`, part 6 (lane `indproofs`, helper `parts`)

`block_shape_all_ctors`: the members' constructor lists concatenated (a copy per member).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The models -/

/-- **The model of `block_shape_ctors_copy`**: the length and the memory after the copy. -/
def ccW (n : Nat) (m : Mem) (off q k : Word) : Option (Word × Mem) :=
  match n with
  | 0 => none
  | n + 1 =>
    match copyW n m (q + k) (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3)) with
    | none => none
    | some m1 => some (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3), m1)

mutual
/-- **The model of `block_shape_all_ctors_go`**: the memory after the copies. -/
def acGoW : Nat → Mem → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _ => none
  | n + 1, m, off, l, q, k =>
    if l = 0 then some m else acK1 n off l q k (ccW n m off q k)

/-- After `block_shape_ctors_copy`. -/
def acK1 (n : Nat) (off l q k : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (cl, m1) => acGoW n m1 (off + 1) (l - 1) q (k + cl)
end

section arms
variable (n : Nat) (m m1 : Mem) (off l q k cl : Word)
theorem acGoW_nil (h : l = 0) : acGoW (n + 1) m off l q k = some m := by simp [acGoW, h]
theorem acGoW_cons (h : l ≠ 0) : acGoW (n + 1) m off l q k = acK1 n off l q k (ccW n m off q k) := by
  simp [acGoW, h]
theorem acK1_some : acK1 n off l q k (some (cl, m1)) = acGoW n m1 (off + 1) (l - 1) q (k + cl) := by
  simp [acK1]
end arms

grind_pattern [ind_grind] acGoW_nil => acGoW (n + 1) m off l q k
grind_pattern [ind_grind] acGoW_cons => acGoW (n + 1) m off l q k
grind_pattern [ind_grind] acK1_some => acK1 n off l q k (some (cl, m1))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hnc : p.lookup "num_ctors_of" = some numCtorsOf)
  (hcc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy)
  (hg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo)
  (hp : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors)

include hcp hcc in
theorem blockShapeCtorsCopy_spec (n : Nat) (s₀ : St) (off q k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_ctors_copy" [off, q, k]
    ⦃fun r s' => LocEq s' s₀ ∧ ccW n s₀.mem off q k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hcc]
  simp only [callFn, blockShapeCtorsCopy]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        iwCopy_spec p hcp n] <;>
      finish (gen := 20) [rdW_eq, ccW]

include hcp hcc hg in
theorem blockShapeAllCtorsGo_spec (n : Nat) : ∀ (s₀ : St) (off l q k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_all_ctors_go" [off, l, q, k]
    ⦃fun _ s' => LocEq s' s₀ ∧ acGoW n s₀.mem off l q k = some s'.mem; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off l q k; rw [invoke_eq _ hg]; simp only [callFn, blockShapeAllCtorsGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off l q k
    rw [invoke_eq _ hg]
    simp only [callFn, blockShapeAllCtorsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        blockShapeCtorsCopy_spec p hcp hcc n, ih] <;>
      finish (gen := 20)

/-- **`block_shape_all_ctors` is its model `acW`** (generated). -/
l_model blockShapeAllCtors_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hcp : p.lookup "iw_copy" = some iwCopy) (hnc : p.lookup "num_ctors_of" = some numCtorsOf)
    (hcc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy)
    (hg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo)
    (hp : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors)
  fns [hp ↦ acW list]
  specs [numCtorsOf_spec p hnc n, iwAlloc_specW p ha n, blockShapeAllCtorsGo_spec p hcp hcc hg n]
  grind [ind_grind] finish [rdW_eq] gen 20

end spec


/-! ## Word lists behind a decoded pointer slice -/

theorem decPL_words {m : Mem} {α : Type} {f : Nat → Option α} :
    ∀ (l o : Nat) (xs : List α), decPL m f o l = some xs →
    ∃ ws : List Word, ws.length = l ∧ (∀ j (hj : j < ws.length), (m.arr64 IW)[o + j]? = some ws[j]) ∧
      ws.mapM (fun w => f w.toNat) = some xs
  | 0, o, xs, h => by
    simp only [decPL, List.range_zero, List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨[], rfl, fun j hj => absurd hj (by simp), rfl⟩
  | l + 1, o, xs, h => by
    rw [decPL_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v, hv, x, hx, ys, hys, rfl⟩ := h
    obtain ⟨ws, hlen, hcells, hmap⟩ := decPL_words l (o + 1) ys hys
    simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨w :: ws, by simp [hlen], fun j hj => ?_, ?_⟩
    · cases j with
      | zero => simpa using hw
      | succ j =>
        have := hcells j (by simpa using hj)
        simpa [Nat.add_assoc, Nat.add_comm 1 j, Nat.add_left_comm] using
          (by rw [show o + (j + 1) = o + 1 + j by omega]; exact this)
    · simp [hx, hmap]

theorem decPL_of_words {m : Mem} {α : Type} {f : Nat → Option α} :
    ∀ (ws : List Word) (o : Nat) (xs : List α),
    (∀ j (hj : j < ws.length), (m.arr64 IW)[o + j]? = some ws[j]) →
    ws.mapM (fun w => f w.toNat) = some xs → decPL m f o ws.length = some xs
  | [], o, xs, _, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; simp [decPL]
  | w :: ws, o, xs, hc, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    have ih := decPL_of_words ws (o + 1) ys (fun j hj => by
      have := hc (j + 1) (by simpa using hj)
      rw [show o + (j + 1) = o + 1 + j by omega] at this
      simpa using this) hys
    rw [List.length_cons, decPL_succ]
    have hw : iwN m o = some w.toNat := by
      have := hc 0 (by simp)
      simp only [iwN, nat?, iwA, Option.map_eq_some_iff]
      exact ⟨w, by simpa using this, rfl⟩
    rw [hw]
    simp only [bind, Option.bind_some, hx, ih, pure]


/-! ## One member's copy -/

/-- Copying zero words reads no source. -/
theorem copyW_src0 (n : Nat) (m : Mem) (d s : Word) : copyW n m d s 0 = copyW n m d 0 0 := by
  cases n <;> simp [copyW]

theorem ccW_get {n : Nat} {m m1 : Mem} {off q k cl : Word}
    (h : ccW n m off q k = some (cl, m1))
    (hsd : cl.toNat = 0 ∨
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2)).toNat + cl.toNat ≤ (q + k).toNat)
    (hd : (q + k).toNat + cl.toNat ≤ (m.arr64 IW).size) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    cl = rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) ∧
    (∀ b, b ≠ IW → m1.arr64 b = m.arr64 b) ∧ (m1.arr64 IW).size = (m.arr64 IW).size ∧
    m1.words.size = m.words.size ∧
    ∀ i, (m1.arr64 IW)[i]? =
      if (q + k).toNat ≤ i ∧ i < (q + k).toNat + cl.toNat then
        (m.arr64 IW)[(rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2)).toNat + (i - (q + k).toNat)]?
      else (m.arr64 IW)[i]? := by
  cases n with
  | zero => simp [ccW] at h
  | succ n =>
    simp only [ccW] at h
    rcases hc : copyW n m (q + k) (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3)) with _ | m2 <;> rw [hc] at h
    · simp at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rcases hsd with h0 | hsd
    · have hz : rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) = 0 := UInt64.toNat_inj.mp (by simpa using h0)
      rw [hz] at hc hd ⊢
      rw [copyW_src0] at hc
      obtain ⟨hA, hS, hW, hG⟩ := copyW_get n m m2 _ _ _ hc (by simp) hd hsz
      refine ⟨rfl, hA, hS, hW, fun i => ?_⟩
      rw [hG i]
      have : ¬ ((q + k).toNat ≤ i ∧ i < (q + k).toNat + (0 : Word).toNat) := by simp
      rw [ite_eq_right this, ite_eq_right this]
    · exact ⟨rfl, copyW_get n m m2 _ _ _ hc hsd hd hsz⟩

theorem ccW_len {n : Nat} {m m1 : Mem} {off q k cl : Word}
    (h : ccW n m off q k = some (cl, m1)) : cl = rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) := by
  cases n with
  | zero => simp [ccW] at h
  | succ n =>
    simp only [ccW] at h
    rcases hc : copyW n m (q + k) (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3)) with _ | m2 <;> rw [hc] at h
    · simp at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

/-- A copy above the original top keeps the pool's growth relation. -/
theorem iwGrow_of_copy {m0 m m1 : Mem} (hg : IWGrow m0 m) (hA : ∀ b, b ≠ IW → m1.arr64 b = m.arr64 b)
    (q : Nat) (hq : iwTop m0 ≤ q)
    (hG : ∀ i, i < q → (m1.arr64 IW)[i]? = (m.arr64 IW)[i]?) : IWGrow m0 m1 := by
  have htop : iwTop m1 = iwTop m := by simp only [iwTop, hA CTL (by decide)]
  have hEr : erTop m1 = erTop m := by simp only [erTop, hA CTL (by decide)]
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [htop]; exact hg.1
  · rw [hEr]; exact hg.2.1
  · rw [hG i (by omega)]; exact hg.2.2.1 i hi
  · rw [hA EREC (by decide)]; exact hg.2.2.2 i hi


theorem iwN_eq_agree {m m0 : Mem} {q i : Nat} (hag : ∀ j, j < q → (m.arr64 IW)[j]? = (m0.arr64 IW)[j]?)
    (hi : i < q) : iwN m i = iwN m0 i := by
  simp only [iwN, nat?, iwA]
  rw [hag i hi]

/-- A read of the cut pool: below the top, and the pool's own. -/
theorem acTr {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) : i < iwTop m ∧ iwN m i = some v := by
  have hi : i < iwTop m := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, -⟩ := h; exact (truncM_iw_get hx).1
  exact ⟨hi, by rw [← iwN_truncM hi]; exact h⟩

/-- A nonempty pointer slice decoded in the cut pool lies below the top. -/
theorem acPLb {α : Type} {m : Mem} {f : Nat → Option α} {o l : Nat} {xs : List α}
    (h : decPL (truncM m) f o l = some xs) : ∀ j < l, o + j < iwTop m := by
  obtain ⟨ws, hl, hc, -⟩ := decPL_words l o xs h
  intro j hj
  exact (truncM_iw_get (hc j (by omega))).1

/-- Constructor records decoded below the tops stay decoded as the pools grow. -/
theorem acMapGrow {m m' : Mem} (hg : IWGrow m m') : ∀ {ws : List Word} {xs : List (IConstantVal × Nat)},
    ws.mapM (fun w => decCN (truncM m) w.toNat) = some xs →
    ws.mapM (fun w => decCN (truncM m') w.toNat) = some xs
  | [], xs, h => h
  | w :: ws, xs, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    exact ⟨x, DecB.grow (decCN_mono _) hg hx, ys, acMapGrow hg hys, rfl⟩

theorem acGoW_ok (n : Nat) : ∀ (m0 m mf : Mem) (off l q k : Word) (ms : List MemberShape),
    acGoW n m off l q k = some mf → IWGrow m0 m → (m.arr64 IW).size < 2 ^ 64 →
    (∀ i, i < q.toNat → (m.arr64 IW)[i]? = (m0.arr64 IW)[i]?) → iwTop m0 ≤ q.toNat →
    DecB (fun m => decPL m (decMS m) off.toNat l.toNat) m0 ms →
    q.toNat + k.toNat + (ms.map fun x => x.ctors.length).sum ≤ (m.arr64 IW).size →
    ∃ ws : List Word, ws.length = (ms.map fun x => x.ctors.length).sum ∧
      (∀ i (hi : i < ws.length), (mf.arr64 IW)[q.toNat + k.toNat + i]? = some ws[i]) ∧
      ws.mapM (fun w => decCN (truncM m0) w.toNat) = some (ms.map (·.ctors)).flatten ∧
      (∀ i, ¬ (q.toNat + k.toNat ≤ i ∧ i < q.toNat + k.toNat + ws.length) →
        (mf.arr64 IW)[i]? = (m.arr64 IW)[i]?) ∧
      (∀ b, b ≠ IW → mf.arr64 b = m.arr64 b) ∧ (mf.arr64 IW).size = (m.arr64 IW).size ∧
      mf.words.size = m.words.size := by
  induction n with
  | zero => intro m0 m mf off l q k ms h; simp [acGoW] at h
  | succ n ih =>
    intro m0 m mf off l q k ms h hg0 hsz hag hq hmsB hroom
    by_cases hl : l = 0
    · rw [acGoW_nil n m off l q k hl] at h
      simp only [Option.some.injEq] at h
      subst h
      have hmsn : ms = [] := by
        have := decPL_length _ (show decPL _ _ _ _ = _ from hmsB)
        rw [hl] at this; simpa using this
      subst hmsn
      exact ⟨[], rfl, fun i hi => absurd hi (by simp), rfl, fun i _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    · obtain ⟨j', hj'⟩ : ∃ j', l.toNat = j' + 1 := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        exact ⟨l.toNat - 1, by omega⟩
      have hdB : decPL (truncM m0) (decMS (truncM m0)) off.toNat (j' + 1) = some ms := by
        rw [← hj']; exact hmsB
      have hlen := decPL_length _ hdB
      cases hmsl : ms with
      | nil => rw [hmsl] at hlen; simp at hlen
      | cons ms0 rest =>
      rw [hmsl] at hdB hroom
      obtain ⟨v, hvB, hms0B⟩ := decPL_head hdB
      obtain ⟨-, -, hctB⟩ := decMS_some hms0B
      obtain ⟨co, cl', hcoB, hclB, hctorsB⟩ := decAt_some hctB
      obtain ⟨hofft, hv0⟩ := acTr hvB
      obtain ⟨-, hco0⟩ := acTr hcoB
      obtain ⟨hcl3t, hcl0⟩ := acTr hclB
      have hlenc : ms0.ctors.length = cl' := decPL_length _ hctorsB
      obtain ⟨wsj, hlj, hcjB, hmj⟩ := decPL_words cl' co ms0.ctors hctorsB
      have hcc : ∀ i < cl', co + i < iwTop m0 := acPLb hctorsB
      have hoq : off.toNat < q.toNat := by omega
      have hv : iwN m off.toNat = some v := by rw [iwN_eq_agree hag hoq]; exact hv0
      have hco : iwN m (v + 2) = some co := by rw [iwN_eq_agree hag (by omega)]; exact hco0
      have hcl3 : iwN m (v + 3) = some cl' := by rw [iwN_eq_agree hag (by omega)]; exact hcl0
      -- the words the model reads
      obtain ⟨hvw, hvb⟩ := iwN_rdW hv (by omega)
      obtain ⟨hcow, hcob⟩ := iwN_rdW hco (by omega)
      obtain ⟨hclw, hclb⟩ := iwN_rdW hcl3 (by omega)
      rw [ofNat_toNat_word] at hvw
      have e2 : UInt64.ofNat v + 2 = UInt64.ofNat (v + 2) := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
      have e3 : UInt64.ofNat v + 3 = UInt64.ofNat (v + 3) := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
      rw [acGoW_cons n m off l q k hl] at h
      obtain ⟨cl, m1, hc1, h⟩ := ipK_inv h (by simp [acK1])
      rw [acK1_some] at h
      have hcoW : rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2) = UInt64.ofNat co := by
        rw [hvw, e2]; exact hcow
      have hclW : rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) = UInt64.ofNat cl' := by
        rw [hvw, e3]; exact hclw
      have hTle : cl' ≤ (List.map (fun x => x.ctors.length) (ms0 :: rest)).sum := by
        simp only [List.map_cons, List.sum_cons]; omega
      have hqk : (q + k).toNat = q.toNat + k.toNat := by
        rw [UInt64.toNat_add]; simp; omega
      have hclv : cl.toNat = cl' := by
        rw [ccW_len hc1, hclW]; exact UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hclb)
      have hcoV : (UInt64.ofNat co).toNat = co := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hcob)
      obtain ⟨hcl_eq, hA, hS1, hW1, hcells⟩ := ccW_get hc1
        (by
          rcases Nat.eq_zero_or_pos cl' with h0 | hp
          · left; rw [hclv]; exact h0
          · right; have := hcc (cl' - 1) (by omega); rw [hcoW, hcoV, hclv, hqk]; omega)
        (by rw [hqk, hclv]; omega) hsz
      have hag1 : ∀ i, i < q.toNat → (m1.arr64 IW)[i]? = (m0.arr64 IW)[i]? := by
        intro i hi
        rw [hcells i, ite_eq_right (by rw [hqk]; omega)]; exact hag i hi
      have hg1 : IWGrow m0 m1 := iwGrow_of_copy hg0 hA q.toNat hq (fun i hi => by
        rw [hcells i, ite_eq_right (by rw [hqk]; omega)])
      have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hS1]; exact hsz
      have hl1 : (l - 1).toNat = j' := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp [hj']
      have hoff1 : (off + 1).toNat = off.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hkc : (k + cl).toNat = k.toNat + cl' := by
        rw [UInt64.toNat_add]; simp; rw [hclv]; omega
      have hrestsum : (List.map (fun x => x.ctors.length) (ms0 :: rest)).sum =
          cl' + (List.map (fun x => x.ctors.length) rest).sum := by
        simp only [List.map_cons, List.sum_cons]; rw [hlenc]
      obtain ⟨wsr, hlr, hcr, hmr, hor, hAr, hSr, hWr⟩ := ih m0 m1 mf (off + 1) (l - 1) q (k + cl)
        rest h hg1 hsz1 hag1 hq
        (by show decPL _ _ _ _ = _; rw [hoff1, hl1]; exact decPL_tail hdB)
        (by rw [hkc, hS1]; omega)
      refine ⟨wsj ++ wsr, by rw [List.length_append, hlj, hlr, hrestsum], fun i hi => ?_, ?_, fun i hi => ?_,
        fun b hb => (hAr b hb).trans (hA b hb), hSr.trans hS1, hWr.trans hW1⟩
      · by_cases hi1 : i < wsj.length
        · rw [List.getElem_append_left hi1]
          have e1 := hor (q.toNat + k.toNat + i) (by rw [hkc]; omega)
          have e2 := hcells (q.toNat + k.toNat + i)
          rw [ite_eq_left (by rw [hqk, hclv]; omega), hcoW, hcoV, hqk] at e2
          have e3 : q.toNat + k.toNat + i - (q.toNat + k.toNat) = i := by omega
          rw [e3] at e2
          have hci := hcc i (by omega)
          rw [e1, e2, hag (co + i) (by omega)]
          have := hcjB i hi1
          rw [← this]; exact (truncM_iw_eq hci).symm
        · have hi2 : i - wsj.length < wsr.length := by rw [List.length_append] at hi; omega
          have key := hcr (i - wsj.length) hi2
          rw [List.getElem_append_right (by omega)]
          have e : q.toNat + k.toNat + i = q.toNat + (k + cl).toNat + (i - wsj.length) := by
            rw [hkc, hlj]; omega
          rw [e]; exact key
      · rw [List.mapM_append, hmj, hmr]
        simp
      · have hnot : ¬ (q.toNat + k.toNat ≤ i ∧ i < q.toNat + k.toNat + (wsj.length + wsr.length)) := by
          rw [List.length_append] at hi; exact hi
        rw [hor i (by rw [hkc]; omega), hcells i, ite_eq_right (by rw [hqk, hclv]; omega)]


theorem numCtorsOf_sum (ms : List MemberShape) :
    ConRon.Arena.numCtorsOf ms = (ms.map fun x => x.ctors.length).sum := by
  induction ms with
  | nil => rfl
  | cons a as ih => simp [ConRon.Arena.numCtorsOf, ih]

theorem acW_ok (n : Nat) (m m2 : Mem) (p : Word) (r : List Word) (bs : BlockShape)
    (h : acW n m p = some (r, m2)) (hq : DecB (fun m => decBS m p.toNat) m bs)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size) :
    ∃ q tot, r = [q, tot] ∧ DecB (fun m => decPL m (decCN m) q.toNat tot.toNat) m2 bs.allCtors ∧
      IWGrow m m2 ∧ MemFrame [IW] [200] m m2 ∧ q.toNat + tot.toNat = iwTop m2 ∧
      q.toNat + tot.toNat ≤ (m.arr64 IW).size := by
  cases n with
  | zero => simp [acW] at h
  | succ n =>
  have h64 : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  obtain ⟨hmem, -⟩ := decBS_some (show decBS (truncM m) p.toNat = some bs from hq)
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some hmem
  obtain ⟨hpt, ho⟩ := acTr ho
  obtain ⟨hp1t, hl⟩ := acTr hl
  have hgB : DecB (fun m => decPL m (decMS m) o l) m bs.members := hg
  have hgm : decPL m (decMS m) o l = some bs.members := hgB.get (OMono.decPL (fun q => decMS_mono q) o l)
  have hlen := decPL_length m hgm
  have hol : o + l < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos l with h0 | hp
    · subst h0
      simp only [iwN, nat?, Option.map_eq_some_iff] at ho
      obtain ⟨w, -, rfl⟩ := ho; simpa using w.toNat_lt
    · have := acPLb hg (l - 1) (by omega); omega
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (p.toNat + 1) = p + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [ofNat_toNat_word] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hob)
  have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hlb)
  rw [acW.arm1, ho', hl'] at h
  rcases hn : numCtorsOfW n m (UInt64.ofNat o) (UInt64.ofNat l) with _ | tot <;> rw [hn] at h
  · rw [acW.k_num_ctors_of.none] at h; cases h
  rw [acW.k_num_ctors_of.arm1] at h
  obtain ⟨htot, hnc⟩ := numCtorsOfW_ok n m (UInt64.ofNat o) (UInt64.ofNat l) tot bs.members hsz
    (by rw [hoo, hll]; exact hol) (by rw [hoo, hll]; exact hgm) hn
  rcases hal : allocW m tot with _ | ⟨q, m1⟩ <;> rw [hal] at h
  · rw [acW.k_iw_alloc.none] at h; cases h
  rw [acW.k_iw_alloc.arm1] at h
  cases hgo : acGoW n m1 (UInt64.ofNat o) (UInt64.ofNat l) q 0 with
  | none => rw [hgo, acW.k_block_shape_all_ctors_go.none] at h; cases h
  | some m2' =>
  rw [hgo, acW.k_block_shape_all_ctors_go.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hqq, hm1, hroom⟩ := allocW_facts hal hsz
  subst hm1
  have hIW1 : (allocMem m tot).arr64 IW = m.arr64 IW := allocMem_IW m tot
  have hqtop : q.toNat = iwTop m := by rw [hqq]; rfl
  have hT : tot.toNat = (bs.members.map fun x => x.ctors.length).sum := by
    rw [htot, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hnc), numCtorsOf_sum]
  have hg1 : IWGrow m (allocMem m tot) := allocMem_grow m tot (by omega) hc
  obtain ⟨ws, hwl, hwc, hwm, hwo, hwA, hwS, hwW⟩ := acGoW_ok n m (allocMem m tot) m2' (UInt64.ofNat o)
    (UInt64.ofNat l) q 0 bs.members hgo hg1 (by rw [hIW1]; exact hsz)
    (fun i hi => by rw [hIW1]) (by omega)
    (by show decPL _ _ _ _ = _; rw [hoo, hll]; exact hg)
    (by rw [hIW1, ← hT]; simp only [UInt64.toNat_zero]; omega)
  have hf : MemFrame [IW] [200] m m2' :=
    (allocMem_frame m tot).trans (copy_frame hwA hwS hwW)
  have htop : rdW (m2'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + tot := by
    rw [hwA CTL (by decide), allocMem_top m tot hc]
  have hlow : ∀ i < iwTop m, (m2'.arr64 IW)[i]? = (m.arr64 IW)[i]? := by
    intro i hi
    rw [hwo i (by simp only [UInt64.toNat_zero]; omega), hIW1]
  have hroom' : iwTop m + tot.toNat ≤ (m.arr64 IW).size := by omega
  have hg2 : IWGrow m m2' := iwGrow_of_frame hf (N := tot) htop hroom' hsz hlow
  have htop2 : q.toNat + tot.toNat = iwTop m2' := by
    simp only [iwTop, htop]
    rw [UInt64.toNat_add]
    have : (rdW (m.arr64 CTL) 200).toNat = q.toNat := by rw [hqq]
    omega
  refine ⟨q, tot, rfl, ?_, hg2, hf, htop2, by omega⟩
  have := decPL_of_words (m := truncM m2') (f := decCN (truncM m2')) ws q.toNat
    (bs.members.map (·.ctors)).flatten
    (fun j hj => by
      have := hwc j hj
      simp only [UInt64.toNat_zero, Nat.add_zero] at this
      have hlt : q.toNat + j < iwTop m2' := by rw [← htop2, hT, ← hwl]; omega
      have e := truncM_iw_eq (m := m2') hlt
      simp only [iwA] at e
      rw [e]; exact this)
    (acMapGrow hg2 hwm)
  rw [hwl, ← hT] at this
  exact this


/-- **`block_shape_all_ctors` refines `BlockShape.allCtors`**: a fresh `IW` slice of the members'
constructor pointers, concatenated, decoded below the tops. The shape decoded below the tops; the
sum's wrap is a capacity (`num_ctors_of` aborts). -/
@[refines ConRon.Arena.BlockShape.allCtors]
theorem blockShapeAllCtors_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hcp : p.lookup "iw_copy" = some iwCopy) (hnc : p.lookup "num_ctors_of" = some numCtorsOf)
    (hcc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy)
    (hg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo)
    (hp : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (q : Word) (bs : BlockShape) (hS : StageR dn vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m q.toNat) s₀.mem bs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_all_ctors" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      DecB (fun m => decPL m (decCN m) (r.headD 0).toNat (r.getD 1 0).toNat) s'.mem bs.allCtors ∧
      (r.headD 0).toNat + (r.getD 1 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (blockShapeAllCtors_spec p ha hcp hnc hcc hg hp n s₀ q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨-, -, hsz, -, hcl⟩ := hS.2
  obtain ⟨q', tot, hr, hdec, hgrow, hfr, htop, hroom⟩ := acW_ok n s₀.mem s'.mem q r bs hm hq hsz hcl
  subst hr
  exact ⟨hl, stage_frame_iw hS hfr (by omega), hgrow, by simpa using hdec, by simp; omega⟩

end L.Ind
