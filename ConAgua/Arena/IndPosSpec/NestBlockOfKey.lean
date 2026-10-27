import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.IndRealAbs

/-!
# NestBlockOfKey

`decCI_kind3`, `decCI_indInfo_kind`, `erN_rdW`, `nat?_lt`, `hlist?_some`, `nestBlockOf_key` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `decCI`'s `indInfo` arm, at a known kind word -/

/-- **A decoded record at kind word `3` is `indInfo`**, with its caps: `decCI`'s match only
reaches the `.indInfo` arm from `nat? a p = some 3` (`Env.lean`'s `decCI_name` destructures the
same match generically, for the name field). -/
theorem decCI_kind3 {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) (hk : nat? a p = some 3) :
    ∃ cv caps, ci = .indInfo cv caps ∧ decCaps a dn (p + 5) = some caps := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk', h⟩ := h
  have hk3 : k = 3 := Option.some.inj (hk'.symm.trans hk)
  subst hk3
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨cv, hcv, caps, hcaps, rfl⟩ := h
  exact ⟨cv, caps, rfl, hcaps⟩

/-- The contrapositive: an `indInfo` record's kind word is `3`. -/
theorem decCI_indInfo_kind {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a dn p = some (.indInfo cv caps)) :
    nat? a p = some 3 := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  rw [hk]
  congr 1
  match k, h with
  | 0, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 1, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 2, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 3, h => rfl
  | 4, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 5, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 6, h => simp_all []
  | (_ + 7), h => simp_all

/-- A word read off `EREC` at a `Nat` position, as `nat?` decodes it. -/
theorem erN_rdW {m : Mem} {q : Nat} {k : Nat} (h : nat? (erA m) q = some k) (hq : q < 2 ^ 64) :
    rdW (m.arr64 EREC) (UInt64.ofNat q) = UInt64.ofNat k := by
  simp only [nat?, erA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have hqq : (UInt64.ofNat q).toNat = q := by simp; omega
  simp only [rdW, hqq, hw, Option.getD_some, UInt64.ofNat_toNat]

/-- A `nat?`-decoded value is below `2 ^ 64` (it is some word's `toNat`). -/
theorem nat?_lt {a : Array Word} {i k : Nat} (h : nat? a i = some k) : k < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, -, rfl⟩ := h
  exact w.toNat_lt

/-- `hlist?`'s two-word header, unfolded. -/
theorem hlist?_some {k : IdxKind} {a : Array Word} {i : Nat} {xs : List (Idx k)}
    (h : hlist? a i = some xs) :
    ∃ o l, nat? a i = some o ∧ nat? a (i + 1) = some l ∧ hslice? a o l = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, h⟩ := h
  exact ⟨o, l, ho, hl, h⟩

/-! ## `nest_block_of` refines `nestBlockOf`: the pure fact -/

/-- **What `nest_block_of` computes, as a function of `env_find`'s result**: the key lemma,
proved purely over `Mem`/`Word`, outside the L execution.

Two extra hypotheses, beyond `hfound`, are needed and not discharged this round (see the
report): `hwf` — the found record, if its kind word is `3`, fully decodes as `indInfo` (true for
any row actually installed through `IFEnv.push`, by `EnvR`'s own `consts` invariant — relating
that to a *found* row's pointer needs more of `Env.lean`'s machinery than this round reaches) —
and `hqb`, a slack bound on pointers so `q + 15`/`q + 16` do not wrap (true for any real `EREC`,
whose size is nowhere near `2 ^ 64`). -/
theorem nestBlockOf_key {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q)
    (hwf : rdW (m.arr64 EREC) q = (3 : Word) →
      ∃ cv caps, decCI (erecP m) dn q.toNat = some (.indInfo cv caps))
    (hqb : rdW (m.arr64 EREC) q = (3 : Word) → q.toNat + 16 < 2 ^ 64) :
    hslice? (erA m)
        (if found = 0 then (0 : Word) else if rdW (m.arr64 EREC) q = 3 then
          rdW (m.arr64 EREC) (q + 15) else 0).toNat
        (if found = 0 then (0 : Word) else if rdW (m.arr64 EREC) q = 3 then
          rdW (m.arr64 EREC) (q + 16) else 0).toNat
      = some (nestBlockOf fe (decI c)) := by
  rw [nestBlockOf]
  unfold decFound at hfound
  by_cases h0 : found = 0
  · simp only [h0, hfound, ite_true]
    simp [hslice?]
  · simp only [h0, ite_false] at hfound ⊢
    have hqlt : q.toNat < 2 ^ 64 := q.toNat_lt
    have hsize : UInt64.size = 2 ^ 64 := rfl
    by_cases hk3 : rdW (m.arr64 EREC) q = (3 : Word)
    · obtain ⟨cv, caps, hci0⟩ := hwf hk3
      have hqb := hqb hk3
      rw [hci0] at hfound
      have hci := (erecP_ext m).decCI hci0
      simp only [hfound, ite_eq_left hk3]
      obtain ⟨cv', caps', he, hcaps⟩ := decCI_kind3 hci (decCI_indInfo_kind hci)
      obtain rfl : caps = caps' := by
        have := he.symm; simp only [IConstantInfo.indInfo.injEq] at this; exact this.2.symm
      simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, vall, hvall, _, _, hcapseq⟩ := hcaps
      obtain ⟨actors, -, heq⟩ := hcapseq
      have hallcaps : caps.all = vall := by
        have h' := Option.some.inj heq; rw [← h']
      obtain ⟨o, l, ho, hl, hslc⟩ := hlist?_some hvall
      have ho' : nat? (erA m) (q.toNat + 15) = some o := by
        have heq2 : q.toNat + 5 + 10 = q.toNat + 15 := by omega
        rwa [heq2] at ho
      have hl' : nat? (erA m) (q.toNat + 16) = some l := by
        have heq2 : q.toNat + 5 + 10 + 1 = q.toNat + 16 := by omega
        rwa [heq2] at hl
      have hwo : rdW (m.arr64 EREC) (q + 15) = UInt64.ofNat o := by
        have e15 : (q + 15 : Word) = UInt64.ofNat (q.toNat + 15) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add]
          have hA : (UInt64.ofNat (q.toNat + 15)).toNat = q.toNat + 15 :=
            UInt64.toNat_ofNat_of_lt' (by omega)
          have hB : (15 : Word).toNat = 15 := by decide
          rw [hA, hB]
          omega
        rw [e15]; exact erN_rdW ho' (by omega)
      have hwl : rdW (m.arr64 EREC) (q + 16) = UInt64.ofNat l := by
        have e16 : (q + 16 : Word) = UInt64.ofNat (q.toNat + 16) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add]
          have hA : (UInt64.ofNat (q.toNat + 16)).toNat = q.toNat + 16 :=
            UInt64.toNat_ofNat_of_lt' (by omega)
          have hB : (16 : Word).toNat = 16 := by decide
          rw [hA, hB]
          omega
        rw [e16]; exact erN_rdW hl' (by omega)
      rw [hwo, hwl]
      have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' (nat?_lt ho')
      have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' (nat?_lt hl')
      rw [hoo, hll, hallcaps]
      exact hslc
    · simp only [ite_eq_right hk3]
      have hnind : ∀ cv caps, fe.find? (decI c) ≠ some (.indInfo cv caps) := by
        intro cv caps hfc
        rw [hfound] at hfc
        have hfc := (erecP_ext m).decCI hfc
        exact hk3 (by
          have hk := decCI_indInfo_kind hfc
          have := erN_rdW hk hqlt
          rwa [UInt64.ofNat_toNat] at this)
      rcases hm : fe.find? (decI c) with _ | ci; · simp [hslice?]
      cases ci with
      | indInfo cv caps => exact absurd hm (hnind cv caps)
      | axiomInfo _ => simp [hslice?]
      | defnInfo _ _ _ => simp [hslice?]
      | thmInfo _ => simp [hslice?]
      | ctorInfo _ _ _ => simp [hslice?]
      | recInfo _ _ _ _ => simp [hslice?]

/-- `nat?` reads inside the array. -/
theorem nat?_idx {a : Array Word} {i k : Nat} (h : nat? a i = some k) : i < a.size := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hw).1

/-- An `indInfo` record is fully inside the array it decodes from. -/
theorem decCI_indInfo_bound {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a dn p = some (.indInfo cv caps)) :
    p + 16 < a.size := by
  obtain ⟨cv', caps', he, hcaps⟩ := decCI_kind3 h (decCI_indInfo_kind h)
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, vall, hvall, _, _, hcapseq⟩ := hcaps
  obtain ⟨o, l, ho, hl, hs⟩ := hlist?_some hvall
  have := nat?_idx hl
  omega

theorem EnvR.row_dec {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) :
    rowTag w ≤ 2 → rowC m w ≠ 0 → ∃ ci, decCI (erecP m) dn (rowP m w).toNat = some ci := by
  intro ht h0
  have hk := h.keys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.vals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  have hv := hv h0
  simp only [rowW, h0, ite_false, Option.map_some] at hk
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => simp [e] at hk
  | some r =>
    simp only [e, Option.map_some] at hv
    exact ⟨r.2, hv.symm⟩

/-- A found `indInfo` row, seen through `erecP`, gives the pointer bound. -/
theorem erecP_size_lt (m : Mem) : (erecP m).size < 2 ^ 64 := by
  have h : (erecP m).size ≤ erecTop m := by simp [erecP]; exact Nat.min_le_left _ _
  have := (rdW (m.arr64 CTL) 129).toNat_lt
  simp only [erecTop] at h
  omega

theorem blk_nok3 {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found ≠ 0)
    (hk : rdW (m.arr64 EREC) q ≠ 3) :
    hslice? (erA m) (0 : Word).toNat (0 : Word).toNat = some (nestBlockOf fe (decI c)) := by
  have := nestBlockOf_key found q hfound (fun h => absurd h hk) (fun h => absurd h hk)
  simpa [h0, hk] using this

/-! ## `nest_ctor_entry_strip`, `nest_ctor_entry` -/

def stripK (ciq nPc nF : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0, 0], m1)
    else some ([1, ciq + 1, nPc, nF, r.tail.tail.tail.headD 0], m1)

def stripW (m : Mem) (ciq : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 EREC) ciq ≠ 4 then some ([0, 0, 0, 0, 0], m)
  else if rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5) then none
  else stripK ciq (rdW (m.arr64 EREC) (ciq + 5)) (rdW (m.arr64 EREC) (ciq + 6))
    (stripF 6 m [rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6),
      rdW (m.arr64 EREC) (ciq + 1 + 3)])

section arms
variable (m m1 : Mem) (ciq nPc nF : Word) (r : List Word)
theorem stripW_notctor (h : rdW (m.arr64 EREC) ciq ≠ 4) : stripW m ciq = some ([0, 0, 0, 0, 0], m) := by
  simp [stripW, h]
theorem stripW_ctor (h : rdW (m.arr64 EREC) ciq = 4)
    (h2 : ¬ rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5)) :
    stripW m ciq =
    stripK ciq (rdW (m.arr64 EREC) (ciq + 5)) (rdW (m.arr64 EREC) (ciq + 6))
    (stripF 6 m [rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6),
      rdW (m.arr64 EREC) (ciq + 1 + 3)]) := by
  unfold stripW; rw [ite_eq_right (by simp [h]), ite_eq_right h2]
theorem stripK_fail (h : r.headD 0 = 0) : stripK ciq nPc nF (some (r, m1)) = some ([0, 0, 0, 0, 0], m1) := by
  simp only [stripK]; rw [ite_eq_left h]
theorem stripK_ok (h : r.headD 0 ≠ 0) :
    stripK ciq nPc nF (some (r, m1)) = some ([1, ciq + 1, nPc, nF, r.tail.tail.tail.headD 0], m1) := by
  simp only [stripK]; rw [ite_eq_right h]
end arms
grind_pattern [ind_grind] stripW_notctor => stripW m ciq
grind_pattern [ind_grind] stripW_ctor => stripW m ciq
grind_pattern [ind_grind] stripK_fail => stripK ciq nPc nF (some (r, m1))
grind_pattern [ind_grind] stripK_ok => stripK ciq nPc nF (some (r, m1))

/-! ### Reading `EREC` records at a word index -/

theorem erec_rd {m : Mem} {w : Word} {c : Nat} {v : Word} (h : (erecP m)[w.toNat + c]? = some v)
    (hc : c < 2 ^ 64) : rdW (m.arr64 EREC) (w + UInt64.ofNat c) = v := by
  have hlt := (Array.getElem?_eq_some_iff.mp h).1
  have hsz := erecP_size_lt m
  have e : (w + UInt64.ofNat c).toNat = w.toNat + c := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hc]; exact Nat.mod_eq_of_lt (by omega)
  simp only [rdW, e, erecP_get h, Option.getD_some]

theorem decCV_type {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    hd? a (q + 3) = some cv.type := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, hd, hq⟩ := h
  rw [← Option.some.inj hq]; exact hd

theorem drop3_eq (r : List Word) : r.drop 3 = r.tail.tail.tail := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp

/-! ### `viewConst` against `view` -/

theorem ETables.getConst_of_get (t : ETables) (i : EIdx) (ht : i.tag = ETag.const) (n : NIdx) (us : LsIdx)
    (h : t.get i = some (.const n us)) : t.getConst i = some (n, us) := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const] at h
  simp only [ETables.getConst]
  revert h
  cases t.consts.node? i.idxNat <;> simp_all [ETag.const]

theorem EStore.viewConst_of_view (st : EStore) (i : EIdx) (ht : i.tag = ETag.const) (n : NIdx)
    (us : LsIdx) (h : st.view i = some (.const n us)) : st.viewConst i = some (n, us) := by
  unfold EStore.view at h
  unfold EStore.viewConst EStore.persGetConst
  split at h
  · rename_i hp; rw [ite_eq_left hp]; exact ETables.getConst_of_get _ _ ht n us h
  · rename_i hp; rw [ite_eq_right hp]
    split at h
    · rename_i hs; rw [ite_eq_left hs]; exact ETables.getConst_of_get _ _ ht n us h
    · simp at h

/-! ### `nest_ctor_entry` -/

def entryK3 (C : Word) (r : List Word) (m2 : Mem) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else if v.tail.headD 0 ≠ C then some ([0, 0, 0, 0], m2)
  else some ([1, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], m2)

def entryK2 (C : Word) (r : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 >>> 28 ≠ 3 then some ([0, 0, 0, 0], m2)
    else entryK3 C r m2 (eViewW m2 (r2.headD 0))

def entryK1 (C : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0], m1)
    else entryK2 C r (gafF m1 [CWF, r.tail.tail.tail.tail.headD 0])

def entryW (m : Mem) (C ciq : Word) : Option (List Word × Mem) := entryK1 C (stripW m ciq)

section arms
variable (C : Word) (r r2 v : List Word) (m1 m2 : Mem)
theorem entryK3_miss (h : v ≠ []) (h2 : v.tail.headD 0 ≠ C) : entryK3 C r m2 v = some ([0, 0, 0, 0], m2) := by
  simp only [entryK3]; rw [ite_eq_right h, ite_eq_left h2]
theorem entryK3_hit (h : v ≠ []) (h2 : ¬ v.tail.headD 0 ≠ C) :
    entryK3 C r m2 v = some ([1, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], m2) := by
  simp only [entryK3]; rw [ite_eq_right h, ite_eq_right h2]
theorem entryK2_notconst (h : r2.headD 0 >>> 28 ≠ 3) : entryK2 C r (some (r2, m2)) = some ([0, 0, 0, 0], m2) := by
  simp only [entryK2]; rw [ite_eq_left h]
theorem entryK2_const (h : ¬ r2.headD 0 >>> 28 ≠ 3) :
    entryK2 C r (some (r2, m2)) = entryK3 C r m2 (eViewW m2 (r2.headD 0)) := by
  simp only [entryK2]; rw [ite_eq_right h]
theorem entryK1_fail (h : r.headD 0 = 0) : entryK1 C (some (r, m1)) = some ([0, 0, 0, 0], m1) := by
  simp only [entryK1]; rw [ite_eq_left h]
theorem entryK1_ok (h : ¬ r.headD 0 = 0) :
    entryK1 C (some (r, m1)) = entryK2 C r (gafF m1 [CWF, r.tail.tail.tail.tail.headD 0]) := by
  simp only [entryK1]; rw [ite_eq_right h]
end arms
grind_pattern [ind_grind] entryK3_miss => entryK3 C r m2 v
grind_pattern [ind_grind] entryK3_hit => entryK3 C r m2 v
grind_pattern [ind_grind] entryK2_notconst => entryK2 C r (some (r2, m2))
grind_pattern [ind_grind] entryK2_const => entryK2 C r (some (r2, m2))
grind_pattern [ind_grind] entryK1_fail => entryK1 C (some (r, m1))
grind_pattern [ind_grind] entryK1_ok => entryK1 C (some (r, m1))

theorem viewConst_run (h : EIdx) (a : AState) :
    (viewConst h).run a = .ok (a.store.viewConst h, a) := rfl

theorem tag_const_iff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.const) = decide (w >>> 28 = 3) := by
  have := decE_tag_eq w hw 3 (by decide)
  have e1 : (ETag.const : UInt32) = UInt32.ofNat 3 := rfl
  show ((decE w).tag == ETag.const) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

theorem getD1_eq (vl : List Word) : vl.getD 1 0 = vl.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl

theorem ETables.get_const (t : ETables) (i : EIdx) (ht : i.tag = ETag.const) (v : ENodeView)
    (h : t.get i = some v) : ∃ n us, v = .const n us := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const] at h
  cases hn : t.consts.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_const (st : EStore) (i : EIdx) (ht : i.tag = ETag.const) (v : ENodeView)
    (h : st.view i = some v) : ∃ n us, v = .const n us := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_const _ _ ht v h
  · split at h
    · exact ETables.get_const _ _ ht v h
    · simp at h

theorem decI_beq' {k : IdxKind} (v w : Word) (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) :
    ((decI v : Idx k) == decI w) = decide (v = w) := by
  by_cases h : v = w
  · subst h; simp
  · have : (decI v : Idx k) ≠ decI w := fun e => h (by
      rw [(decI_eq_iff v hv _).mp e]; exact decI_word_self w hw)
    simp [h, this]

/-! ## `nest_res_head` -/

def resHeadK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => some ([if r.headD 0 >>> 28 = 1 then 1 else 0], m1)

def resHeadW (m : Mem) (e : Word) : Option (List Word × Mem) :=
  resHeadK (gafF m [CWF, e])

/-! ## `inst_pis_with` -/

mutual
def instW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, ao, al, e =>
    if al = 0 then some ([1, e], m)
    else if e >>> 28 ≠ 6 then some ([0, 0], m)
    else instK1 n m ao al (eViewW m e)
def instK1 (n : Nat) (m : Mem) (ao al : Word) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else instK2 n ao al
    (i1F m [CWF, v.tail.tail.headD 0, rdW (m.arr64 IW) ao, 0])
def instK2 (n : Nat) (ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m1) => instK3 (instW n m1 (ao + 1) (al - 1) (rb.headD 0))
def instK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0, r.tail.headD 0], m2)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (ao al e : Word) (v rb r : List Word)
theorem instW_nil (h : al = 0) : instW (n + 1) m ao al e = some ([1, e], m) := by simp [instW, h]
theorem instW_nopi (h : al ≠ 0) (h2 : e >>> 28 ≠ 6) : instW (n + 1) m ao al e = some ([0, 0], m) := by
  simp [instW, h, h2]
theorem instW_pi (h : al ≠ 0) (h2 : ¬ e >>> 28 ≠ 6) :
    instW (n + 1) m ao al e = instK1 n m ao al (eViewW m e) := by simp only [instW]; rw [ite_eq_right h, ite_eq_right h2]
theorem instK1_ok (h : v ≠ []) : instK1 n m ao al v = instK2 n ao al
    (i1F m [CWF, v.tail.tail.headD 0, rdW (m.arr64 IW) ao, 0]) := by simp [instK1, h]
theorem instK2_some : instK2 n ao al (some (rb, m1)) = instK3 (instW n m1 (ao + 1) (al - 1) (rb.headD 0)) := by rw [instK2]
theorem instK3_some : instK3 (some (r, m2)) = some ([r.headD 0, r.tail.headD 0], m2) := by rw [instK3]
end arms
grind_pattern [ind_grind] instW_nil => instW (n + 1) m ao al e
grind_pattern [ind_grind] instW_nopi => instW (n + 1) m ao al e
grind_pattern [ind_grind] instW_pi => instW (n + 1) m ao al e
grind_pattern [ind_grind] instK1_ok => instK1 n m ao al v
grind_pattern [ind_grind] instK2_some => instK2 n ao al (some (rb, m1))
grind_pattern [ind_grind] instK3_some => instK3 (some (r, m2))

theorem instPisWith_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "inst_pis_with" = some instPisWith) (hi1 : I1Prog p) (n : Nat) :
    ∀ (s₀ : St) (ao al e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_pis_with" [ao, al, e]
    ⦃fun r s' => LocEq s' s₀ ∧ instW n s₀.mem ao al e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ao al e
    rw [invoke_eq _ hp]; simp only [callFn, instPisWith]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ao al e
    simp only [invoke_eq _ hp, callFn, instPisWith]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        eView_spec p hv n, i1F_spec p hi1 n, ih] <;> finish (gen := 20)

theorem ETables.get_forall (t : ETables) (i : EIdx) (ht : i.tag = ETag.forallE) (v : ENodeView)
    (h : t.get i = some v) : ∃ ty b, v = .forallE ty b := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
    ETag.forallE] at h
  cases hn : t.foralls.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_forall (st : EStore) (i : EIdx) (ht : i.tag = ETag.forallE) (v : ENodeView)
    (h : st.view i = some v) : ∃ ty b, v = .forallE ty b := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_forall _ _ ht v h
  · split at h
    · exact ETables.get_forall _ _ ht v h
    · simp at h

theorem ETables.getBind_of_get (t : ETables) (i : EIdx) (ht : i.tag = ETag.forallE) (ty b : EIdx)
    (h : t.get i = some (.forallE ty b)) : t.getBind i = some (ty, b) := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
    ETag.forallE] at h
  simp only [ETables.getBind, ht, ETag.lam, ETag.forallE]
  cases hn : t.foralls.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h ⊢; simp [ETag.forallE] at *; exact h

theorem EStore.viewBind_of_view (st : EStore) (i : EIdx) (ht : i.tag = ETag.forallE) (ty b : EIdx)
    (h : st.view i = some (.forallE ty b)) : st.viewBind i = some (ty, b) := by
  unfold EStore.view at h
  unfold EStore.viewBind EStore.persGetBind
  split at h
  · rename_i hp; rw [ite_eq_left hp]; exact ETables.getBind_of_get _ _ ht ty b h
  · rename_i hp; rw [ite_eq_right hp]
    split at h
    · rename_i hs; rw [ite_eq_left hs]; exact ETables.getBind_of_get _ _ ht ty b h
    · simp at h

theorem tag_forall_iff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.forallE) = decide (w >>> 28 = 6) := by
  have := decE_tag_eq w hw 6 (by decide)
  have e1 : (ETag.forallE : UInt32) = UInt32.ofNat 6 := rfl
  show ((decE w).tag == ETag.forallE) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

theorem viewBind_run (h : EIdx) (a : AState) :
    (viewBind h).run a = .ok (a.store.viewBind h, a) := rfl

/-- `inst_pis_with` keeps the `abstract1` memo. -/
theorem instW_afr (n : Nat) : ∀ (m m' : Mem) (ao al e : Word) (r : List Word), instW n m ao al e = some (r, m') →
    AFr m m' := by
  induction n with
  | zero => intro m m' ao al e r h; simp [instW] at h
  | succ n ih =>
    intro m m' ao al e r h
    simp only [instW, instK1, instK2.eq_def, instK3.eq_def] at h
    afr_auto h [i1F_afr, ih _ _ _ _ _ _]

/-! ## `close_telescope` -/

mutual
def closeW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, dO, dl, i, body =>
    if dl = 0 then some ([body], m)
    else closeK1 dO i (closeW n m (dO + 1) (dl - 1) (i + 1) body)
def closeK1 (dO i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => closeK2 dO (abF m1 [CWF, r1.headD 0, i, 0])
def closeK2 (dO : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => closeK3 (mkForallW m2 (rdW (m2.arr64 IW) dO) (r2.headD 0))
def closeK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => if 4294967296 ≤ r then none else some ([r], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (dO dl i body r : Word) (r1 r2 : List Word)
theorem closeW_nil (h : dl = 0) : closeW (n + 1) m dO dl i body = some ([body], m) := by simp [closeW, h]
theorem closeW_cons (h : dl ≠ 0) : closeW (n + 1) m dO dl i body =
    closeK1 dO i (closeW n m (dO + 1) (dl - 1) (i + 1) body) := by simp [closeW, h]
theorem closeK1_some : closeK1 dO i (some (r1, m1)) =
    closeK2 dO (abF m1 [CWF, r1.headD 0, i, 0]) := by rw [closeK1]
theorem closeK2_some : closeK2 dO (some (r2, m2)) =
    closeK3 (mkForallW m2 (rdW (m2.arr64 IW) dO) (r2.headD 0)) := by rw [closeK2]
theorem closeK3_big (h : 4294967296 ≤ r) : closeK3 (some (r, m3)) = none := by simp [closeK3, h]
theorem closeK3_ok (h : ¬ 4294967296 ≤ r) : closeK3 (some (r, m3)) = some ([r], m3) := by simp [closeK3, h]
end arms
grind_pattern [ind_grind] closeW_nil => closeW (n + 1) m dO dl i body
grind_pattern [ind_grind] closeW_cons => closeW (n + 1) m dO dl i body
grind_pattern [ind_grind] closeK1_some => closeK1 dO i (some (r1, m1))
grind_pattern [ind_grind] closeK2_some => closeK2 dO (some (r2, m2))
grind_pattern [ind_grind] closeK3_big => closeK3 (some (r, m3))
grind_pattern [ind_grind] closeK3_ok => closeK3 (some (r, m3))

section spec
variable (p : Prog) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hp : p.lookup "close_telescope" = some closeTelescope) (hab : AbF p)
include hd hpf hpp hpi hmk hp hab

theorem closeTelescope_spec (n : Nat) : ∀ (s₀ : St) (dO dl i body : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_telescope" [dO, dl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ closeW n s₀.mem dO dl i body = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ dO dl i body
    rw [invoke_eq _ hp]; simp only [callFn, closeTelescope]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ dO dl i body
    simp only [invoke_eq _ hp, callFn, closeTelescope]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        abF_spec p hab n, mkForall_spec p hd hpf hpp hpi hmk n, ih] <;>
      finish (gen := 20)

end spec

theorem rdW_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hi : x.toNat < iwTop m) :
    rdW (m'.arr64 IW) x = rdW (m.arr64 IW) x := by
  simp only [rdW, hg.2.2.1 _ hi]

theorem closeW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (dO dl i body : Word) (ds : List EIdx) (r : List Word),
    closeW n m dO dl i body = some (r, m') → StageR dn vis fe m a → H body →
    decHL m dO.toNat dl.toNat = some ds → dO.toNat + dl.toNat < 2 ^ 64 →
    dO.toNat + dl.toNat ≤ iwTop m → i.toNat + dl.toNat < 2 ^ 64 → AbsOK m →
    ∃ x a', (ConRon.Arena.closeTelescope ds i.toNat (decI body)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0E m' r x ∧ AbsOK m' := by
  induction n with
  | zero => intro dn fe vis m m' a dO dl i body ds r h; simp [closeW] at h
  | succ n ih =>
    intro dn fe vis m m' a dO dl i body ds r h hS hbody hdec hb hit hib hA
    by_cases hdl : dl = 0
    · rw [closeW_nil n m dO dl i body hdl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : ds = [] := by
        have h0 : dl.toNat = 0 := by rw [hdl]; rfl
        rw [h0] at hdec; simpa [decHL, hslice?] using hdec.symm
      subst this
      exact ⟨decI body, a, rfl, hS, IWGrow.refl _, ⟨hbody, rfl⟩, hA⟩
    · have hl1 : dl.toNat = (dl.toNat - 1) + 1 := by have := toNat_ne_zero' hdl; omega
      rw [hl1, decHL, hslice?_succ] at hdec
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdec
      obtain ⟨d, hdd, bs, hbs, rfl⟩ := hdec
      rw [closeW_cons n m dO dl i body hdl] at h
      have hdo1 : (dO + 1).toNat = dO.toNat + 1 := toNat_add_one' (by omega)
      have hdl1 : (dl - 1).toNat = dl.toNat - 1 := toNat_sub_one' hdl
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_one' (by omega)
      rcases hr1 : closeW n m (dO + 1) (dl - 1) (i + 1) body with _ | ⟨r1, m1⟩ <;> rw [hr1] at h; · simp [closeK1] at h
      rw [closeK1_some] at h
      obtain ⟨x1, a1, hrun1, hS1, hg1, ⟨hlt1, hdec1⟩, hA1⟩ :=
        ih dn fe vis m m1 a (dO + 1) (dl - 1) (i + 1) body bs r1 hr1 hS hbody
          (by rw [hdo1, hdl1]; exact hbs) (by rw [hdo1, hdl1]; omega) (by rw [hdo1, hdl1]; omega)
          (by rw [hi1, hdl1]; omega) hA
      rw [hi1] at hrun1
      rcases hr2 : abF m1 [CWF, r1.headD 0, i, 0] with _ | ⟨r2, m2⟩ <;> rw [hr2] at h; · simp [closeK2] at h
      rw [closeK2_some] at h
      obtain ⟨x2, a2, hrun2, ⟨hS2, hg2, hlt2, hdec2⟩, hA2⟩ :=
        abF_ok dn vis fe (r1.headD 0) i 0 hlt1 m1 m2 a1 r2 hr2 ⟨hS1, hA1⟩
      rw [CWF_eq, hdec1, show (0 : Word).toNat = 0 from rfl] at hrun2
      have hg12 := hg1.trans hg2
      have hd0 : dO.toNat < iwTop m := by omega
      obtain ⟨wd, hwd_eq, hwd_lt, hwd_dec⟩ := iwH_rdW hdd (by omega)
      rw [UInt64.ofNat_toNat] at hwd_eq
      rw [rdW_grow hg12 hd0, hwd_eq] at h
      rcases hm : mkForallW m2 wd (r2.headD 0) with _ | ⟨rr, m3⟩ <;> rw [hm] at h; · simp [closeK3] at h
      by_cases hbig : 4294967296 ≤ rr
      · rw [closeK3_big _ _ hbig] at h; simp at h
      · rw [closeK3_ok _ _ hbig] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨a3, hrun3, hS3, hg3⟩ := mkForall_stage hS2 wd (r2.headD 0) hm
        refine ⟨decE rr, a3, ?_, hS3, hg12.trans hg3, ⟨?_, rfl⟩, mkForallW_afr hm hA2⟩
        · simp only [ConRon.Arena.closeTelescope, StateT.run_bind]
          simp only [hrun1, except_ok_bind, hrun2, ← hwd_dec, ← hdec2]
          exact hrun3
        · have : rr.toNat < 2 ^ 32 := by
            have : ¬ (4294967296 : Nat) ≤ rr.toNat := hbig
            omega
          simpa using this

end L.Ind

end
