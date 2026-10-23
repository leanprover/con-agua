import ConAgua.Checker.Prelude
import ConAgua.Checker.HoistRef

/-!
# `prepare_prelude`'s leaves: `decl_declares`, `decl_key`, `prep_find` (lane `front4`)

Against `declares`, `preludeKey` and the `findIdx` of `pick`, over the records of `DECL`
(`DeclAtF`, with `RecOK`).
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- What the prepare stage's other passes keep: the arrays and `CTL` words from `64` on (the
records, the pool, the pins, the hoist's memos), every array's size. -/
def HighFr (m m' : Mem) : Prop :=
  (∀ b : ArrId, 64 ≤ b → m'.arr64 b = m.arr64 b) ∧
    (∀ x : Word, 64 ≤ x.toNat → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) ∧
    (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size


/-! ## Helpers -/

theorem pl_contains_cons (x y : NIdx) (l : List NIdx) :
    (x :: l).contains y = (x == y || l.contains y) := by
  rw [List.contains_cons, BEq.comm]

/-- `decl_declares_go` against the block's names (the slice `DIND[o + q ‥ o + c)`). -/
theorem pDeclGo_ok (n : Nat) : ∀ (m : Mem) (o c q w r : Word) (P : Array Word) (t : Nat)
    (cs : List IConstantInfo), m.arr64 DIND = P → t ≤ (P[0]?.getD 0).toNat → o.toNat ≠ 0 →
    decCIs (trunc P t) (fun _ => none) (o.toNat + q.toNat) (c.toNat - q.toNat) = some cs →
    w.toNat < 2 ^ 32 → pDeclGoW n m o c w q = some r →
    (r ≠ 0 ↔ (cs.map (·.name)).contains (decI w) = true) := by
  induction n with
  | zero => intro m o c q w r P t cs _ _ _ _ _ h; simp [pDeclGoW.eq_1] at h
  | succ n ih =>
    intro m o c q w r P t cs hP ht ho hd hw h
    by_cases hcq : c ≤ q
    · rw [pDeclGoW.arm1 n m o c w q hcq] at h
      cases h
      have : c.toNat - q.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hcq; omega
      rw [this, decCIs] at hd
      simp at hd; subst hd
      simp
    · have hqc : q.toNat < c.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hcq); omega
      rw [show c.toNat - q.toNat = (c.toNat - q.toNat - 1) + 1 by omega, hix_decCIs_succ] at hd
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hd
      obtain ⟨ci, ⟨p, hp, hci⟩, cs', hcs', rfl⟩ := hd
      simp only [nat?, Option.map_eq_some_iff] at hp
      obtain ⟨pw, hpw, rfl⟩ := hp
      obtain ⟨hPq, hqt⟩ := hix_trunc_get hpw (by omega)
      obtain ⟨w', hw', hw32, hname⟩ := hix_decCI_name hci
      obtain ⟨hPw, hpt⟩ := hix_trunc_get hw' (by omega)
      have hP0 : (P[0]?.getD 0).toNat < 2 ^ 64 := UInt64.toNat_lt _
      have e1 : rdW (m.arr64 DIND) (o + q) = pw :=
        hix_rdW (hP ▸ hPq) (by rw [UInt64.toNat_add]; omega)
      have e2 : rdW (m.arr64 DIND) (pw + 1) = w' :=
        hix_rdW (hP ▸ hPw) (by rw [UInt64.toNat_add]; simp; omega)
      simp only [List.map_cons, pl_contains_cons, hname]
      by_cases hww : w' = w
      · subst hww
        rw [pDeclGoW.arm2 n m o c w' q hcq (by rw [e1, e2])] at h
        cases h
        simp
      · rw [pDeclGoW.arm3 n m o c w q hcq (by rw [e1, e2]; exact hww)] at h
        have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have := ih m o c (q + 1) w r P t cs' hP ht ho
          (by rw [hq1, show o.toNat + (q.toNat + 1) = o.toNat + q.toNat + 1 by omega,
            show c.toNat - (q.toNat + 1) = c.toNat - q.toNat - 1 by omega]; exact hcs') hw h
        have hne : (decI w' == (decI w : NIdx)) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun e => hww (decI_inj hw32 hw e)
        rw [hne, Bool.false_or]
        exact this

theorem pl_names_ind (b : List IConstantInfo) (nP : Nat) :
    (IDeclaration.indDecl b nP).names = b.map (·.name) := rfl

/-- **`decl_declares(i, w)` is `declares (decI w) d`** for the record `i` representing `d`. -/
theorem pDecl_ok (n : Nat) (m : Mem) (i w r : Word) (d : IDeclaration)
    (hD : DeclAtF (m.arr64 DECL) (m.arr64 DLP) i.toNat d) (hok : RecOK (m.arr64 DECL) (m.arr64 DLP) i.toNat)
    (hi : i.toNat < 2 ^ 59) (hw : w.toNat < 2 ^ 32) (h : pDeclW n m i w = some r) :
    (r ≠ 0 ↔ declares (decI w) d = true) := by
  cases n with
  | zero => cases h
  | succ n =>
  have e0 := hix_rd_dw0 (m.arr64 DECL) i hi
  have e1 := hix_rd_dw (m.arr64 DECL) i 1 hi (by decide)
  have e2 := hix_rd_dw (m.arr64 DECL) i 2 hi (by decide)
  have e3 := hix_rd_dw (m.arr64 DECL) i 3 hi (by decide)
  simp only [UInt64.reduceToNat] at e1 e2 e3
  by_cases hind : ∃ b nP, d = .indDecl b nP
  · obtain ⟨b, nP, rfl⟩ := hind
    obtain ⟨h6, -, t, ht, hb⟩ := hD
    rw [pDeclW.arm3 n m i w (by rw [e0, h6]; simp), e2, e3] at h
    rw [declares, pl_names_ind]
    exact pDeclGo_ok n m _ _ 0 w r _ t b rfl ht (hok.2 h6).1 (by simpa using hb) hw h
  · have hD' := hix_declAtF (fun b nP e => hind ⟨b, nP, e⟩) hD
    obtain ⟨h6, hn⟩ := hix_declAt_names hD'
    have h32 := (hok.1 h6).1
    rw [declares, hn]
    by_cases hww : dw (m.arr64 DECL) i.toNat 1 = w
    · rw [pDeclW.arm1 n m i w (by rw [e0]; exact h6) (by rw [e1]; exact hww)] at h
      cases h; subst hww; simp
    · rw [pDeclW.arm2 n m i w (by rw [e0]; exact h6) (by rw [e1]; exact hww)] at h
      cases h
      simp only [ne_eq, not_true_eq_false, false_iff, List.contains_cons, List.contains_nil,
        Bool.or_false, beq_iff_eq]
      exact fun e => hww (decI_inj h32 hw e.symm)

/-- **`decl_key(i)` is `preludeKey d`**: the key word (below `2 ^ 32`), the twin's state after
(interning the anonymous name for an empty block), the store relation; nothing from array and
`CTL` word `64` on changes, and the pins stay. -/
theorem pKey_ok (m m' : Mem) (a : AState) (i r : Word) (d : IDeclaration)
    (hD : DeclAtF (m.arr64 DECL) (m.arr64 DLP) i.toNat d) (hok : RecOK (m.arr64 DECL) (m.arr64 DLP) i.toNat)
    (hi : i.toNat < 2 ^ 59) (hA : ArenaR m a) (h : pKeyW m i = some (r, m')) :
    ∃ a', (preludeKey d).run a = .ok (decI r, a') ∧ r.toNat < 2 ^ 32 ∧ ArenaR m' a' ∧
      HighFr m m' ∧ a'.pins = a.pins := by
  sorry

/-- **`prep_find(mk, n, w, j)`** is the first record `x ∈ [j, n)` with `IW[mk + x] = 0` that
declares `decI w`, plus one; `0` when there is none. -/
theorem pFind_ok (n : Nat) (m : Mem) (dsAll : Array IDeclaration) (mk nw w j r : Word)
    (hD : ∀ x (h : x < dsAll.size), DeclAtF (m.arr64 DECL) (m.arr64 DLP) x dsAll[x] ∧
      RecOK (m.arr64 DECL) (m.arr64 DLP) x)
    (hn : nw.toNat = dsAll.size) (hn59 : nw.toNat < 2 ^ 59) (hmk : mk.toNat + nw.toNat < 2 ^ 64)
    (hw : w.toNat < 2 ^ 32) (h : pFindW n m mk nw w j = some r) :
    (r = 0 → ∀ x (hx : x < dsAll.size), j.toNat ≤ x → rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0 →
      declares (decI w) dsAll[x] = false) ∧
    (r ≠ 0 → ∃ hx : r.toNat - 1 < dsAll.size, j.toNat ≤ r.toNat - 1 ∧
      rdW (m.arr64 IW) (mk + UInt64.ofNat (r.toNat - 1)) = 0 ∧ declares (decI w) dsAll[r.toNat - 1] = true ∧
      ∀ x (hx : x < dsAll.size), j.toNat ≤ x → x < r.toNat - 1 →
        rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0 → declares (decI w) dsAll[x] = false) := by
  sorry

end L.Checker
