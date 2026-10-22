import ConAgua.Arena.IndPartsSpec5

/-!
# Refinements of `IndParts`, part 6 (lane `indproofs`, helper `parts`)

`block_shape_all_ctors`: the members' constructor lists concatenated (a copy per member).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

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

/-- **The model of `block_shape_all_ctors`.** -/
def acW (n : Nat) (m : Mem) (p : Word) : Option (List Word × Mem) :=
  match n with
  | 0 => none
  | n + 1 =>
    match numCtorsOfW n m (rdW (m.arr64 IW) p) (rdW (m.arr64 IW) (p + 1)) with
    | none => none
    | some tot =>
      match allocW m tot with
      | none => none
      | some (q, m1) =>
        match acGoW n m1 (rdW (m.arr64 IW) p) (rdW (m.arr64 IW) (p + 1)) q 0 with
        | none => none
        | some m2 => some ([q, tot], m2)

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

include ha hcp hnc hcc hg hp in
theorem blockShapeAllCtors_spec (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_all_ctors" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ acW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeAllCtors]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        numCtorsOf_spec p hnc n, iwAlloc_specW p ha n,
        blockShapeAllCtorsGo_spec p hcp hcc hg n] <;>
      finish (gen := 20) [rdW_eq, acW]

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

theorem ccW_get {n : Nat} {m m1 : Mem} {off q k cl : Word}
    (h : ccW n m off q k = some (cl, m1))
    (hsd : (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2)).toNat + cl.toNat ≤ (q + k).toNat)
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
    cases hc : copyW n m (q + k) (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3)) with
    | none => rw [hc] at h; simp at h
    | some m2 =>
      rw [hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, copyW_get n m m2 _ _ _ hc hsd hd hsz⟩

theorem ccW_len {n : Nat} {m m1 : Mem} {off q k cl : Word}
    (h : ccW n m off q k = some (cl, m1)) : cl = rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) := by
  cases n with
  | zero => simp [ccW] at h
  | succ n =>
    simp only [ccW] at h
    cases hc : copyW n m (q + k) (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3)) with
    | none => rw [hc] at h; simp at h
    | some m2 =>
      rw [hc] at h
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

theorem acGoW_ok (n : Nat) : ∀ (m0 m mf : Mem) (off l q k : Word) (ms : List MemberShape),
    acGoW n m off l q k = some mf → IWGrow m0 m → (m.arr64 IW).size < 2 ^ 64 →
    (∀ i, i < q.toNat → (m.arr64 IW)[i]? = (m0.arr64 IW)[i]?) → iwTop m0 ≤ q.toNat →
    (∀ m'', IWGrow m0 m'' → decPL m'' (decMS m'') off.toNat l.toNat = some ms) →
    off.toNat + l.toNat ≤ iwTop m0 →
    (∀ j v, j < l.toNat → iwN m0 (off.toNat + j) = some v → v + 4 ≤ iwTop m0) →
    (∀ j v co cl, j < l.toNat → iwN m0 (off.toNat + j) = some v → iwN m0 (v + 2) = some co →
      iwN m0 (v + 3) = some cl → co + cl ≤ iwTop m0) →
    q.toNat + k.toNat + (ms.map fun x => x.ctors.length).sum ≤ (m.arr64 IW).size →
    ∃ ws : List Word, ws.length = (ms.map fun x => x.ctors.length).sum ∧
      (∀ i (hi : i < ws.length), (mf.arr64 IW)[q.toNat + k.toNat + i]? = some ws[i]) ∧
      ws.mapM (fun w => decCN mf w.toNat) = some (ms.map (·.ctors)).flatten ∧
      (∀ i, ¬ (q.toNat + k.toNat ≤ i ∧ i < q.toNat + k.toNat + ws.length) →
        (mf.arr64 IW)[i]? = (m.arr64 IW)[i]?) ∧
      (∀ b, b ≠ IW → mf.arr64 b = m.arr64 b) ∧ (mf.arr64 IW).size = (m.arr64 IW).size ∧
      mf.words.size = m.words.size := by
  induction n with
  | zero => intro m0 m mf off l q k ms h; simp [acGoW] at h
  | succ n ih =>
    intro m0 m mf off l q k ms h hg0 hsz hag hq hms hoff hbd hbd2 hroom
    by_cases hl : l = 0
    · rw [acGoW_nil n m off l q k hl] at h
      simp only [Option.some.injEq] at h
      subst h
      have hmsn : ms = [] := by
        have := hms m hg0
        rw [hl] at this
        simp only [UInt64.toNat_zero, decPL, List.range_zero, List.mapM_nil, pure,
          Option.some.injEq] at this
        exact this.symm
      subst hmsn
      exact ⟨[], rfl, fun i hi => absurd hi (by simp), rfl, fun i _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    · obtain ⟨j', hj'⟩ : ∃ j', l.toNat = j' + 1 := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        exact ⟨l.toNat - 1, by omega⟩
      have hd := hms m hg0
      rw [hj'] at hd
      have hlen := decPL_length m hd
      cases hmsl : ms with
      | nil => rw [hmsl] at hlen; simp at hlen
      | cons ms0 rest =>
      rw [hmsl] at hd hms hroom
      obtain ⟨v, hv, hms0d⟩ := decPL_head hd
      obtain ⟨-, -, hct⟩ := decMS_some hms0d
      obtain ⟨co, cl', hco, hcl, hctors⟩ := decAt_some hct
      have hcl3 : iwN m (v + 3) = some cl' := hcl
      have hlenc : ms0.ctors.length = cl' := decPL_length m hctors
      have hoq : off.toNat < q.toNat := by omega
      have hv0 : iwN m0 (off.toNat + 0) = some v := by
        rw [Nat.add_zero, ← iwN_eq_agree hag hoq]; exact hv
      -- bounds on the member's data
      have hvq : v + 4 ≤ iwTop m0 := hbd 0 v (by omega) hv0
      have hvq' : v + 3 < q.toNat := by omega
      have hco0 : iwN m0 (v + 2) = some co := by
        rw [← iwN_eq_agree hag (by omega)]; exact hco
      have hcl0 : iwN m0 (v + 3) = some cl' := by
        rw [← iwN_eq_agree hag hvq']; exact hcl
      have hcc := hbd2 0 v co cl' (by omega) hv0 hco0 hcl0
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
      cases hc1 : ccW n m off q k with
      | none => rw [hc1] at h; simp [acK1] at h
      | some rm1 =>
      obtain ⟨cl, m1⟩ := rm1
      rw [hc1, acK1_some] at h
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
        (by rw [hcoW, hcoV, hclv, hqk]; omega) (by rw [hqk, hclv]; omega) hsz
      have hag1 : ∀ i, i < q.toNat → (m1.arr64 IW)[i]? = (m0.arr64 IW)[i]? := by
        intro i hi
        rw [hcells i, if_neg (by rw [hqk]; omega)]; exact hag i hi
      have hg1 : IWGrow m0 m1 := iwGrow_of_copy hg0 hA q.toNat hq (fun i hi => by
        rw [hcells i, if_neg (by rw [hqk]; omega)])
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
        (fun m'' hg'' => by
          have := hms m'' hg''
          rw [hj'] at this
          rw [hoff1, hl1]; exact decPL_tail this)
        (by rw [hoff1, hl1]; omega)
        (fun j v hj ha => hbd (j + 1) v (by omega) (by
          rw [show off.toNat + (j + 1) = (off + 1).toNat + j by rw [hoff1]; omega]; exact ha))
        (fun j v co2 cl2 hj ha hb hc2 => hbd2 (j + 1) v co2 cl2 (by omega) (by
          rw [show off.toNat + (j + 1) = (off + 1).toNat + j by rw [hoff1]; omega]; exact ha) hb hc2)
        (by rw [hkc, hS1]; omega)
      have hgf : IWGrow m0 mf := iwGrow_of_copy hg1 hAr q.toNat hq (fun i hi => by
        rw [hor i (by rw [hkc]; omega)])
      have hagf : ∀ i, i < q.toNat → (mf.arr64 IW)[i]? = (m0.arr64 IW)[i]? := by
        intro i hi
        rw [hor i (by rw [hkc]; omega), hag1 i hi]
      have hmsf := hms mf hgf
      rw [hj'] at hmsf
      obtain ⟨vf, hvf, hmsfd⟩ := decPL_head hmsf
      have hvf' : vf = v := by
        have h1 : iwN mf off.toNat = some v := by
          rw [iwN_eq_agree hagf hoq]; rw [← iwN_eq_agree hag hoq]; exact hv
        exact Option.some.inj (hvf.symm.trans h1)
      subst hvf'
      obtain ⟨-, -, hctf⟩ := decMS_some hmsfd
      obtain ⟨cof, clf, hcof, hclf, hctorsf⟩ := decAt_some hctf
      have hcof' : cof = co := by
        have h1 : iwN mf (vf + 2) = some co := by
          rw [iwN_eq_agree hagf (by omega)]; exact hco0
        exact Option.some.inj (hcof.symm.trans h1)
      have hclf' : clf = cl' := by
        have h1 : iwN mf (vf + 2 + 1) = some cl' := by
          rw [iwN_eq_agree hagf (by omega)]; exact hcl0
        exact Option.some.inj (hclf.symm.trans h1)
      subst hcof' hclf'
      obtain ⟨wsj, hlj, hcj, hmj⟩ := decPL_words clf cof ms0.ctors hctorsf
      refine ⟨wsj ++ wsr, by rw [List.length_append, hlj, hlr, hrestsum], fun i hi => ?_, ?_, fun i hi => ?_,
        fun b hb => (hAr b hb).trans (hA b hb), hSr.trans hS1, hWr.trans hW1⟩
      · by_cases hi1 : i < wsj.length
        · rw [List.getElem_append_left hi1]
          have e1 := hor (q.toNat + k.toNat + i) (by rw [hkc]; omega)
          have e2 := hcells (q.toNat + k.toNat + i)
          rw [if_pos (by rw [hqk, hclv]; omega), hcoW, hcoV, hqk] at e2
          have e3 : q.toNat + k.toNat + i - (q.toNat + k.toNat) = i := by omega
          rw [e3] at e2
          rw [e1, e2, hag (cof + i) (by omega), ← hagf (cof + i) (by omega)]
          exact hcj i hi1
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
        rw [hor i (by rw [hkc]; omega), hcells i, if_neg (by rw [hqk, hclv]; omega)]


theorem numCtorsOf_sum (ms : List MemberShape) :
    ConRon.Arena.numCtorsOf ms = (ms.map fun x => x.ctors.length).sum := by
  induction ms with
  | nil => rfl
  | cons a as ih => simp [ConRon.Arena.numCtorsOf, ih]

theorem acW_ok (n : Nat) (m m2 : Mem) (p : Word) (r : List Word) (bs : BlockShape)
    (h : acW n m p = some (r, m2)) (hq : decBS m p.toNat = some bs)
    (hstab : ∀ m'', IWGrow m m'' → decBS m'' p.toNat = some bs)
    (hb : p.toNat + 9 ≤ iwTop m) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size)
    (hnc : ConRon.Arena.numCtorsOf bs.members < 2 ^ 64)
    (hoff : ∀ o l, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → o + l ≤ iwTop m)
    (hbd : ∀ o l j v, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → v + 4 ≤ iwTop m)
    (hbd2 : ∀ o l j v co cl, iwN m p.toNat = some o → iwN m (p.toNat + 1) = some l → j < l →
      iwN m (o + j) = some v → iwN m (v + 2) = some co → iwN m (v + 3) = some cl →
      co + cl ≤ iwTop m) :
    ∃ q tot, r = [q, tot] ∧ decPL m2 (decCN m2) q.toNat tot.toNat = some bs.allCtors ∧
      IWGrow m m2 ∧ MemFrame [IW] [200] m m2 ∧ q.toNat + tot.toNat = iwTop m2 := by
  cases n with
  | zero => simp [acW] at h
  | succ n =>
  have h64 : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
  obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hq).1
  have hlen := decPL_length m hg
  obtain ⟨ho', hob⟩ := iwN_rdW ho (by omega)
  obtain ⟨hl', hlb⟩ := iwN_rdW hl (by omega)
  have e1 : UInt64.ofNat (p.toNat + 1) = p + 1 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  rw [ofNat_toNat_word] at ho'
  rw [e1] at hl'
  have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hob)
  have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hlb)
  simp only [acW, ho', hl'] at h
  cases hn : numCtorsOfW n m (UInt64.ofNat o) (UInt64.ofNat l) with
  | none => rw [hn] at h; simp at h
  | some tot =>
  rw [hn] at h
  dsimp only at h
  have hoff' := hoff o l ho hl
  have htot := numCtorsOfW_ok n m (UInt64.ofNat o) (UInt64.ofNat l) tot bs.members hsz
    (by rw [hoo, hll]; omega) (by rw [hoo, hll]; exact hg) hn
  cases hal : allocW m tot with
  | none => rw [hal] at h; simp at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  rw [hal] at h
  dsimp only at h
  cases hgo : acGoW n m1 (UInt64.ofNat o) (UInt64.ofNat l) q 0 with
  | none => rw [hgo] at h; simp at h
  | some m2' =>
  rw [hgo] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
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
    (fun m'' hg'' => by
      have hd := hstab m'' hg''
      obtain ⟨o'', l'', ho'', hl'', hdd⟩ := decAt_some (decBS_some hd).1
      have e1 := iwN_cell hg'' (by omega) ho
      have e2 := iwN_cell hg'' (by omega) hl
      have eo : o'' = o := Option.some.inj (ho''.symm.trans e1)
      have el : l'' = l := Option.some.inj (hl''.symm.trans e2)
      rw [hoo, hll, ← eo, ← el]; exact hdd)
    (by rw [hoo, hll]; exact hoff')
    (fun j v hj hv => by
      rw [hoo] at hv
      exact hbd o l j v ho hl (by rw [hll] at hj; exact hj) hv)
    (fun j v co cl hj hv hco hcl => by
      rw [hoo] at hv
      exact hbd2 o l j v co cl ho hl (by rw [hll] at hj; exact hj) hv hco hcl)
    (by rw [hIW1, ← hT]; simp only [UInt64.toNat_zero]; omega)
  have hf : MemFrame [IW] [200] m m2' :=
    (allocMem_frame m tot).trans (copy_frame hwA hwS hwW)
  have htop : rdW (m2'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + tot := by
    rw [hwA CTL (by decide), allocMem_top m tot hc]
  have hlow : ∀ i < iwTop m, (m2'.arr64 IW)[i]? = (m.arr64 IW)[i]? := by
    intro i hi
    rw [hwo i (by simp only [UInt64.toNat_zero]; omega), hIW1]
  have hroom' : iwTop m + tot.toNat ≤ (m.arr64 IW).size := by omega
  refine ⟨q, tot, rfl, ?_, iwGrow_of_frame hf (N := tot) htop hroom' hsz hlow, hf, ?_⟩
  · have := decPL_of_words ws q.toNat (bs.members.map (·.ctors)).flatten
      (fun j hj => by
        have := hwc j hj
        simpa using this) hwm
    rw [hwl] at this
    rw [hT]
    exact this
  · simp only [iwTop, htop]
    rw [UInt64.toNat_add]
    have : (rdW (m.arr64 CTL) 200).toNat = q.toNat := by rw [hqq]
    omega


/-- **`block_shape_all_ctors` refines `BlockShape.allCtors`**: a fresh `IW` slice of the members'
constructor pointers, concatenated. The shape keeps decoding as the pool grows (`hstab`); its
records lie below the pool's top (`hoff`, `hbd`, `hbd2`). -/
@[refines ConRon.Arena.BlockShape.allCtors]
theorem blockShapeAllCtors_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hcp : p.lookup "iw_copy" = some iwCopy) (hnc : p.lookup "num_ctors_of" = some numCtorsOf)
    (hcc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy)
    (hg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo)
    (hp : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors)
    (n : Nat) (s₀ : St) (q : Word) (bs : BlockShape) (hq : decBS s₀.mem q.toNat = some bs)
    (hstab : ∀ m'', IWGrow s₀.mem m'' → decBS m'' q.toNat = some bs)
    (hb : q.toNat + 9 ≤ iwTop s₀.mem) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hcl : 200 < (s₀.mem.arr64 CTL).size)
    (hnum : ConRon.Arena.numCtorsOf bs.members < 2 ^ 64)
    (hoff : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l →
      o + l ≤ iwTop s₀.mem)
    (hbd : ∀ o l j v, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → j < l →
      iwN s₀.mem (o + j) = some v → v + 4 ≤ iwTop s₀.mem)
    (hbd2 : ∀ o l j v co cl, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l →
      j < l → iwN s₀.mem (o + j) = some v → iwN s₀.mem (v + 2) = some co →
      iwN s₀.mem (v + 3) = some cl → co + cl ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_all_ctors" [q]
    ⦃fun r s' => LocEq s' s₀ ∧
      decPL s'.mem (decCN s'.mem) (r.headD 0).toNat (r.getD 1 0).toNat = some bs.allCtors ∧
      IWGrow s₀.mem s'.mem ∧ MemFrame [IW] [200] s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (blockShapeAllCtors_spec p ha hcp hnc hcc hg hp n s₀ q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨q', tot, hr, hdec, hgrow, hfr, -⟩ := acW_ok n s₀.mem s'.mem q r bs hm hq hstab hb hsz hcl
    hnum hoff hbd hbd2
  subst hr
  exact ⟨hl, hdec, hgrow, hfr⟩

end L.Ind
