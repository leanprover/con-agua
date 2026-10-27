import ConAgua.Arena.IndPosSpec.CtxFields
import ConAgua.Arena.IndPosSpec.NestBlockOfKey

/-!
# EnvFindWHit

`ncGoW`, `ncK1`, `ncK2`, `ncK3`, `NtLook`, `posRowPW_eq` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_container(_ctors(_go))` refines `nestContainer`: word models -/

mutual
def ncGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, C, co, cl, cs, ol, fp =>
    if cl = 0 then some ([ol, fp], m)
    else ncK1 k vis C co cl cs ol fp (envFindW m (rdW (m.arr64 EREC) co) vis)
def ncK1 (k : Nat) (vis C co cl cs ol fp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then ncGoW k m1 vis C (co + 1) (cl - 1) cs ol fp
    else ncK2 k vis C co cl cs ol fp (entryW m1 C (r.tail.headD 0))
def ncK2 (k : Nat) (vis C co cl cs ol fp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then ncGoW k m2 vis C (co + 1) (cl - 1) cs ol fp
    else ncK3 k vis C co cl cs ol fp (r2.tail.tail.headD 0)
      (posRecW m2 [r2.tail.headD 0, r2.tail.tail.tail.headD 0])
def ncK3 (k : Nat) (vis C co cl cs ol fp nPc : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m3) =>
    if ol = 0 then ncGoW k (m3.set64 IW (cs + ol) q) vis C (co + 1) (cl - 1) cs (ol + 1) nPc
    else ncGoW k (m3.set64 IW (cs + ol) q) vis C (co + 1) (cl - 1) cs (ol + 1) fp
end

/-- The lookups of `nest_container`. -/
structure NtLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  h2 : p.lookup "rec2" = some rec2
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip
  hst : StripProg p
  ad : AdF p
  hv : p.lookup "e_view" = some eView
  he : p.lookup "nest_ctor_entry" = some nestCtorEntry
  hgo : p.lookup "nest_container_ctors_go" = some nestContainerCtorsGo
  hcc : p.lookup "nest_container_ctors" = some nestContainerCtors
  hnt : p.lookup "nest_container" = some nestContainer

/-! ### `nest_container`: the relational side -/

theorem posRowPW_eq (m : Mem) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : tagW w ≤ 2) :
    rowPW m w = rowP m w := by
  have h1 := tagW_toNat w
  have h2 := ixW_toNat w hw
  have ht' : rowTag w ≤ 2 := by rw [← h1]; exact UInt64.le_iff_toNat_le.mp ht
  have hix : rowIx w < 2 ^ 30 := by simp only [rowIx]; omega
  have h3 : (ixW w + 1).toNat = rowIx w + 1 := by rw [word_add_toNat (by rw [h2]; simp; omega), h2]; rfl
  simp only [rowPW, rowP, ht', ite_true, rdW, h3]
  simp [selArr_rowSelW w ht']

/-- **A hit of `env_find` is a `find?`** of the record it points to. -/
theorem envFindW_hit {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem}
    {w : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) (hE : EnvR dn m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : r.headD 0 ≠ 0) :
    m1 = m ∧ fe.find? (decI w) = decCI (erecP m) dn (r.tail.headD 0).toNat ∧
      ∃ ci, decCI (erecP m) dn (r.tail.headD 0).toNat = some ci := by
  unfold envFindW at h
  by_cases ht : 2 < tagW w
  · simp [ht] at h
  rw [ite_eq_right ht] at h
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => ht (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  rw [EnvR.find?_eq hE w hw htag, ← rowCW_eq m w hw ht2, ← posRowPW_eq m w hw ht2]
  by_cases hc : rowCW m w = 0
  · rw [ite_eq_left hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0
  rw [ite_eq_right hc] at h
  by_cases hv : rowCW m w - 1 < vis
  · rw [ite_eq_left hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hrc : rowC m w ≠ 0 := by rw [← rowCW_eq m w hw ht2]; exact hc
    refine ⟨rfl, ?_, by rw [List.tail_cons, List.headD_cons, posRowPW_eq m w hw ht2]; exact EnvR.row_dec hE w hw htag hrc⟩
    have hc' : (rowCW m w).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
    have : (rowCW m w).toNat - 1 < vis.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp hv
      rwa [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))] at this
    simp [hc, this]
  · rw [ite_eq_right hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0

theorem envFindW_mem {m m1 : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) :
    m1 = m := by
  unfold envFindW at h
  split at h; · simp at h
  split at h; · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)

/-- A `[cv, nF]` record at `p` denoting `x`, its pool reads in `P`, its constant below `EREC`'s top. -/
def CNOk (m : Mem) (p : Nat) (x : IConstantVal × Nat) (P : Nat → Prop) : Prop :=
  P p ∧ P (p + 1) ∧ ∃ q, iwN m p = some q ∧ decCV (erecP m) q = some x.1 ∧ iwN m (p + 1) = some x.2

/-- The pointers at `o, o + 1, …` are `[cv, nF]` records denoting `xs`. -/
def CsAt (m : Mem) (o : Nat) (xs : List (IConstantVal × Nat)) (P : Nat → Prop) : Prop :=
  ∀ i (hi : i < xs.length), ∃ w : Word, (m.arr64 IW)[o + i]? = some w ∧ CNOk m w.toNat xs[i] P

theorem decCI_idx {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {ci : IConstantInfo}
    (h : decCI a dn p = some ci) : p < a.size := by
  simp only [decCI, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, -⟩ := h
  exact nat?_idx hk

theorem erecP_size_le (m : Mem) : (erecP m).size ≤ erTop m := by
  simp only [erecP, Array.size_extract, erecTop, erTop]; omega

/-- `nest_container`'s results: `(0, …)` or `(1, nPc, cs.off, cs.len)`, the records below the top. -/
def NcOut (m : Mem) (r : List Word) : Option (Nat × List (IConstantVal × Nat)) → Prop
  | none => r.headD 0 = 0
  | some (nPc, cs) => r.headD 0 = 1 ∧ (r.tail.headD 0).toNat = nPc ∧
      (r.tail.tail.tail.headD 0).toNat = cs.length ∧
      (r.tail.tail.headD 0).toNat + cs.length ≤ iwTop m ∧
      CsAt m (r.tail.tail.headD 0).toNat cs (· < iwTop m)

end L.Ind

end
