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

/-- What the prepare stage's other passes keep: the arrays outside the store tier's
(`lowTierArrs`: the records, the pool, the pins, the hoist's memos) and the `CTL` words from `64`
on, every array's size. -/
def HighFr (m m' : Mem) : Prop :=
  (∀ b : ArrId, b ∉ lowTierArrs → m'.arr64 b = m.arr64 b) ∧
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
    rw [pDeclW.arm3 n m i w (by rw [e0, h6]), e2, e3] at h
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
      HighFr m m' ∧ a'.pins = a.pins ∧ a'.store.pers = a.store.pers ∧ a'.store.scr = a.store.scr := by
  have e0 := hix_rd_dw0 (m.arr64 DECL) i hi
  have e1 := hix_rd_dw (m.arr64 DECL) i 1 hi (by decide)
  have e2 := hix_rd_dw (m.arr64 DECL) i 2 hi (by decide)
  have e3 := hix_rd_dw (m.arr64 DECL) i 3 hi (by decide)
  simp only [UInt64.reduceToNat] at e1 e2 e3
  have hHF : HighFr m m := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
  by_cases hind : ∃ b nP, d = .indDecl b nP
  · obtain ⟨b, nP, rfl⟩ := hind
    obtain ⟨h6, -, t, ht, hb⟩ := hD
    have hne6 : ¬rdW (m.arr64 DECL) (1 + 8 * i) ≠ 6 := by rw [e0, h6]; simp
    by_cases hc : dw (m.arr64 DECL) i.toNat 3 = 0
    · rw [pKeyW.arm3 m i (Decidable.of_not_not hne6) (by rw [e3]; simpa using hc)] at h
      rw [hc] at hb
      simp [decCIs] at hb; subst hb
      obtain ⟨hok', hX, hres⟩ := naintern_correct m a hA.nanon r m' h
      have hI := h
      have hF := consInternM_frame nanonCS_wf hI
      have hst := AM.st_proto nanonLens _ _ _ _ _ _ a (internNNode_anon_run a) hok'
      refine ⟨AM.st (internNNode .anonymous) a, ?_, ?_, hA.lift_nanon _ _ _ _ hX hF hst, ?_, ?_⟩
      · have := AM.run_of_ok _ a hok'
        rw [hres] at this
        simpa [preludeKey, pl_names_ind] using this
      · exact consInternM_lt nanonCS_wf hA.nanon hI
      · refine ⟨fun b hb => hF.1 b ?_ ?_, fun x hx => hF.2.1 x ?_, hF.2.2.1, hF.2.2.2⟩
        · intro hm; simp [nanonCS, ConsSch.wset] at hm
          rcases hm with rfl | rfl | rfl | rfl <;> revert hb <;> decide
        · intro e; subst e; revert hb; decide
        · intro hm; simp [nanonCS] at hm; rcases hm with rfl | rfl <;> revert hx <;> decide
      · rcases hst with e | ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> exact ⟨rfl, rfl, rfl⟩
    · rw [pKeyW.arm2 m i (Decidable.of_not_not hne6) (by rw [e3]; intro e; exact hc (by simpa using e)), e2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have ho := (hok.2 h6).1
      rw [show (dw (m.arr64 DECL) i.toNat 3).toNat = ((dw (m.arr64 DECL) i.toNat 3).toNat - 1) + 1 by
        have : (dw (m.arr64 DECL) i.toNat 3).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
        omega, hix_decCIs_succ] at hb
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hb
      obtain ⟨ci, ⟨p, hp, hci⟩, cs', -, rfl⟩ := hb
      simp only [nat?, Option.map_eq_some_iff] at hp
      obtain ⟨pw, hpw, rfl⟩ := hp
      obtain ⟨hPq, hqt⟩ := hix_trunc_get hpw ho
      obtain ⟨w', hw', hw32, hname⟩ := hix_decCI_name hci
      obtain ⟨hPw, hpt⟩ := hix_trunc_get hw' (by omega)
      have hP0 : ((m.arr64 DLP)[0]?.getD 0).toNat < 2 ^ 64 := UInt64.toNat_lt _
      have e1' : rdW (m.arr64 DIND) (dw (m.arr64 DECL) i.toNat 2) = pw := hix_rdW hPq rfl
      have e2' : rdW (m.arr64 DIND) (pw + 1) = w' :=
        hix_rdW hPw (by rw [UInt64.toNat_add]; simp; omega)
      rw [e1', e2']
      refine ⟨a, ?_, hw32, hA, hHF, rfl, rfl, rfl⟩
      simp [preludeKey, pl_names_ind, hname]
      rfl
  · have hD' := hix_declAtF (fun b nP e => hind ⟨b, nP, e⟩) hD
    obtain ⟨h6, hn⟩ := hix_declAt_names hD'
    rw [pKeyW.arm1 m i (by rw [e0]; exact h6), e1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨a, ?_, (hok.1 h6).1, hA, hHF, rfl, rfl, rfl⟩
    simp [preludeKey, hn]
    rfl

/-- **`prep_find(mk, n, w, j)`** is the first record `x ∈ [j, n)` with `IW[mk + x] = 0` that
declares `decI w`, plus one; `0` when there is none. -/
theorem pFind_ok (n : Nat) (m : Mem) (dsAll : Array IDeclaration) (mk nw w j r : Word)
    (hD : ∀ x (h : x < dsAll.size), DeclAtF (m.arr64 DECL) (m.arr64 DLP) x dsAll[x] ∧
      RecOK (m.arr64 DECL) (m.arr64 DLP) x)
    (hn : nw.toNat = dsAll.size) (hn59 : nw.toNat < 2 ^ 59) (_hmk : mk.toNat + nw.toNat < 2 ^ 64)
    (hw : w.toNat < 2 ^ 32) (h : pFindW n m mk nw w j = some r) :
    (r = 0 → ∀ x (hx : x < dsAll.size), j.toNat ≤ x → rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0 →
      declares (decI w) dsAll[x] = false) ∧
    (r ≠ 0 → ∃ hx : r.toNat - 1 < dsAll.size, j.toNat ≤ r.toNat - 1 ∧
      rdW (m.arr64 IW) (mk + UInt64.ofNat (r.toNat - 1)) = 0 ∧ declares (decI w) dsAll[r.toNat - 1] = true ∧
      ∀ x (hx : x < dsAll.size), j.toNat ≤ x → x < r.toNat - 1 →
        rdW (m.arr64 IW) (mk + UInt64.ofNat x) = 0 → declares (decI w) dsAll[x] = false) := by
  induction n generalizing j r with
  | zero => simp [pFindW.eq_1] at h
  | succ n ih =>
    by_cases hnj : nw ≤ j
    · rw [pFindW.arm1 n m mk nw w j hnj] at h
      cases h
      have := UInt64.le_iff_toNat_le.mp hnj
      exact ⟨fun _ x hx hjx _ => absurd hx (by omega), fun h => absurd rfl h⟩
    have hjn : j.toNat < nw.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hnj)
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hjx : UInt64.ofNat j.toNat = j := UInt64.ofNat_toNat
    have hjs : j.toNat < dsAll.size := hn ▸ hjn
    obtain ⟨hDj, hokj⟩ := hD j.toNat hjs
    have key : (rdW (m.arr64 IW) (mk + j) = 0 ∧ declares (decI w) dsAll[j.toNat] = true ∧
        r = j + 1) ∨ ((rdW (m.arr64 IW) (mk + j) = 0 → declares (decI w) dsAll[j.toNat] = false) ∧
        pFindW n m mk nw w (j + 1) = some r) := by
      by_cases hz : rdW (m.arr64 IW) (mk + j) = 0
      · rw [pFindW.arm2 n m mk nw w j hnj hz] at h
        cases hd : pDeclW n m j w with
        | none => rw [hd] at h; simp [pFindW.k_decl_declares] at h
        | some dv =>
          have hdec := pDecl_ok n m j w dv dsAll[j.toNat] hDj hokj (by omega) hw hd
          rw [hd] at h
          by_cases hdv : dv ≠ 0
          · rw [pFindW.k_decl_declares.arm1 n mk nw w j m dv hdv] at h
            cases h
            exact .inl ⟨hz, hdec.mp hdv, rfl⟩
          · rw [pFindW.k_decl_declares.arm2 n mk nw w j m dv (Decidable.of_not_not hdv), pFindW.j1.arm1] at h
            refine .inr ⟨fun _ => ?_, h⟩
            cases e : declares (decI w) dsAll[j.toNat]
            · rfl
            · exact absurd (hdec.mpr e) hdv
      · rw [pFindW.arm3 n m mk nw w j hnj hz, pFindW.j1.arm1] at h
        exact .inr ⟨fun e => absurd e hz, h⟩
    rcases key with ⟨hz, hdec, rfl⟩ | ⟨hex, h'⟩
    · have hr1 : (j + 1).toNat - 1 = j.toNat := by omega
      refine ⟨fun h0 => absurd (congrArg UInt64.toNat h0) (by rw [hj1]; simp), fun _ => ?_⟩
      refine ⟨by omega, by omega, ?_, ?_, fun x _ h1 h2 _ => absurd h2 (by omega)⟩
      · simp only [hr1, hjx]; exact hz
      · simp only [hr1]; exact hdec
    · obtain ⟨ih0, ih1⟩ := ih (j + 1) r h'
      rw [hj1] at ih0 ih1
      refine ⟨fun h0 x hx hjx' hIW => ?_, fun h0 => ?_⟩
      · by_cases e : x = j.toNat
        · subst e; rw [hjx] at hIW; exact hex hIW
        · exact ih0 h0 x hx (by omega) hIW
      · obtain ⟨hx, hle, hIW, hdec, hmin⟩ := ih1 h0
        refine ⟨hx, by omega, hIW, hdec, fun x hx' hjx' hxr hIW' => ?_⟩
        by_cases e : x = j.toNat
        · subst e; rw [hjx] at hIW'; exact hex hIW'
        · exact hmin x hx' (by omega) hxr hIW'

end L.Checker
