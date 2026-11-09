module

public import ConAgua.Arena.IndPosSpec.CtxFields
public import ConAgua.Arena.IndPosSpec.NestBlockOfKey

@[expose] public section

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
    else ncK1 k vis C co cl cs ol fp (some (findRes m vis (erRd m co), m))
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
  hg : p.lookup "env_row_get" = some envRowGetL
  hb : p.lookup "base_row_get" = some baseRowGetL
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

/-- **A hit of `env_find` is a `find?`** of the record it points to. -/
theorem findRes_hit {vis : Word} {fe : IFEnv} {m : Mem} {w : Word} (hE : EnvR m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : (findRes m vis w).headD 0 ≠ 0) :
    fe.find? (decI w) = decCI (erecP m) ((findRes m vis w).tail.headD 0).toNat ∧
      ∃ ci, decCI (erecP m) ((findRes m vis w).tail.headD 0).toNat = some ci := by
  obtain ⟨h1, h2⟩ := hE.find_res hw
  exact ⟨by rw [h1, envFound, if_neg h0], h2 h0⟩

/-- **A miss of `env_find`**: `find?` finds nothing. -/
theorem findRes_miss {vis : Word} {fe : IFEnv} {m : Mem} {w : Word} (hE : EnvR m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : (findRes m vis w).headD 0 = 0) : fe.find? (decI w) = none := by
  rw [(hE.find_res hw).1, envFound, if_pos h0]

/-- A `[cv, nF]` record at `p` denoting `x`, its pool reads in `P`, its constant below `EREC`'s top. -/
def CNOk (m : Mem) (p : Nat) (x : IConstantVal × Nat) (P : Nat → Prop) : Prop :=
  P p ∧ P (p + 1) ∧ ∃ q, iwN m p = some q ∧ decCV (erecP m) q = some x.1 ∧ iwN m (p + 1) = some x.2

/-- The pointers at `o, o + 1, …` are `[cv, nF]` records denoting `xs`. -/
def CsAt (m : Mem) (o : Nat) (xs : List (IConstantVal × Nat)) (P : Nat → Prop) : Prop :=
  ∀ i (hi : i < xs.length), ∃ w : Word, (m.arr64 IW)[o + i]? = some w ∧ CNOk m w.toNat xs[i] P

/-- A decoded record's kind word is read. -/
theorem decCI_rd {a : Nat → Option Word} {p : Nat} {ci : IConstantInfo}
    (h : decCI a p = some ci) : ∃ w, a p = some w := by
  simp only [decCI, Option.bind_eq_bind, Option.bind_eq_some_iff, nat?, Option.map_eq_some_iff] at h
  obtain ⟨k, ⟨w, hw, -⟩, -⟩ := h
  exact ⟨w, hw⟩

/-- `nest_container`'s results: `(0, …)` or `(1, nPc, cs.off, cs.len)`, the records below the top. -/
def NcOut (m : Mem) (r : List Word) : Option (Nat × List (IConstantVal × Nat)) → Prop
  | none => r.headD 0 = 0
  | some (nPc, cs) => r.headD 0 = 1 ∧ (r.tail.headD 0).toNat = nPc ∧
      (r.tail.tail.tail.headD 0).toNat = cs.length ∧
      (r.tail.tail.headD 0).toNat + cs.length ≤ iwTop m ∧
      CsAt m (r.tail.tail.headD 0).toNat cs (· < iwTop m)

end L.Ind

end
