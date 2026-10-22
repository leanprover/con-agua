import ConAgua.Front.IndApplyRefine4

/-!
# The apply step of an `inductive` line against the twin, V: the constructors in the block's order

`vi_order_in`/`vi_order_go`/`vi_order`: every constructor of every type, in the block's order,
passes `vi_ctor` (`ctorW_twin`), its record's pointer written to the ordered slice at `oo`. The
facts are collected per position (`CtorOK`); `ordList` reads the ordered constructors back from
the slice.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)

set_option linter.unusedSimpArgs false

namespace L.Front.Ind

instance : Inhabited IndCtorRec := ⟨⟨⟨0, [], 0⟩, false, 0, 0, none, none⟩⟩

/-- `m'` is `m` but for `IFL` at `B` and above. -/
def IOnly (B : Nat) (m m' : Mem) : Prop :=
  MemFrame [IFL] [] m m' ∧ ∀ i, i < B → wd m' IFL i = wd m IFL i

theorem IOnly.refl (B : Nat) (m : Mem) : IOnly B m m := ⟨MemFrame.refl _ _ _, fun _ _ => rfl⟩

theorem IOnly.trans {B : Nat} {m₁ m₂ m₃ : Mem} (h₁ : IOnly B m₁ m₂) (h₂ : IOnly B m₂ m₃) :
    IOnly B m₁ m₃ := ⟨h₁.1.trans h₂.1, fun i hi => (h₂.2 i hi).trans (h₁.2 i hi)⟩

theorem IOnly.set {B : Nat} {m₁ m₂ : Mem} (h : IOnly B m₁ m₂) (i v : Word) (hi : B ≤ i.toNat) :
    IOnly B m₁ (m₂.set64 IFL i v) :=
  ⟨h.1.trans (MemFrame.set64 _ _ (by decide) _ _), fun j hj => by
    rw [wd_set64, if_neg (by omega)]; exact h.2 j hj⟩

theorem IOnly.ifr {B : Nat} {m m' : Mem} (h : IOnly B m m') : m'.arr64 IFR = m.arr64 IFR :=
  h.1.1 IFR (by decide) (by decide)

theorem IOnly.other {B : Nat} {m m' : Mem} (h : IOnly B m m') (A : ArrId) (h1 : A ≠ IFL) (h2 : A ≠ CTL) :
    m'.arr64 A = m.arr64 A := h.1.1 A (by simp [h1]) h2

theorem IOnly.arena {B : Nat} {m m' : Mem} {a : AState} (h : IOnly B m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame_ext [IFL] [] (by decide) (by simp) m m' h.1 a hR

theorem IOnly.stateDR {B : Nat} {m m' : Mem} {st : StateD} (h : IOnly B m m') (hD : StateDR m st) :
    StateDR m' st :=
  hD.frame h.1 (by decide) (by decide) (by decide) (by decide) (by decide)

theorem IOnly.wdR {B : Nat} {m m' : Mem} (h : IOnly B m m') (i : Nat) : wd m' IFR i = wd m IFR i := by
  simp only [wd, h.ifr]

theorem IOnly.listF {B : Nat} {m m' : Mem} {b : ByteArray} {co : Nat} {cts : List IndCtorRec}
    (h : IOnly B m m') (hC : ListF (CtF b m) m 10 co cts) : ListF (CtF b m') m' 10 co cts := by
  obtain ⟨h1, h2, h3⟩ := hC
  refine ⟨h1, by simp only [topN, h.wdR]; exact h2, fun j hj => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := h3 j hj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [CVF, h.wdR] at c1 ⊢; exact c1
  · simpa only [h.wdR] using c2
  · simpa only [h.wdR] using c3
  · cases hc : cts[j].cidx <;> rw [hc] at c4 <;> simp only [OptW, h.wdR] at c4 ⊢ <;> exact c4
  · cases hc : cts[j].induct <;> rw [hc] at c5 <;> simp only [OptW, h.wdR] at c5 ⊢ <;> exact c5

theorem IOnly.islice {B : Nat} {m m' : Mem} (h : IOnly B m m') (o l : Nat) (hb : o + l ≤ B) :
    islice (k := .name) m' o l = islice m o l := by
  simp only [L.Front.Ind.islice]
  apply List.map_congr_left
  intro c hc
  simp only [List.mem_range] at hc
  rw [h.2 _ (by omega)]

/-- **The twin's checks of one constructor pass**: record `k` is the last one named `nn` among the
constructor names `CN`, and its `cidx`, `induct` and telescope agree. -/
def CtorOK (st : StateD) (a : AState) (cts : List IndCtorRec) (CN : List NIdx) (nn : NIdx)
    (j : Nat) (T : NIdx) (np fuel : Nat) (k : Nat) : Prop :=
  ∃ hk : k < cts.length,
    (CN.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) x => (mi.1.insert x mi.2, mi.2 + 1)) (∅, 0)).1[nn]? =
      some k ∧
    (∀ ci, cts[k].cidx = some ci → ci = j) ∧
    (∀ iw, cts[k].induct = some iw → (st.name iw).run a = .ok (T, a)) ∧
    ∃ cty, (getDeclD st cts[k].cv.type).run a = .ok (cty, a) ∧
      (ConRon.Arena.Frontend.indPiTeleLen fuel cty).run a = .ok (np + cts[k].numFields, a)

/-- The ordered constructors read back from the slice at `oo`: record `(w - co) / 10` for each
pointer `w`. -/
def ordList (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l : Nat) : List IndCtorRec :=
  (List.range l).map fun p => cts.getD (((wd m IFL (oo + p)).toNat - co) / 10) default

theorem ordList_succ (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l : Nat) :
    ordList m oo co cts (l + 1) =
      ordList m oo co cts l ++ [cts.getD (((wd m IFL (oo + l)).toNat - co) / 10) default] := by
  simp [ordList, List.range_succ]

theorem ordList_length (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l : Nat) :
    (ordList m oo co cts l).length = l := by simp [ordList]

/-- A pointer `co + 10 k` reads back as record `k`. -/
theorem ptr_rec (cts : List IndCtorRec) (co : Word) (k : Nat) (hk : k < cts.length)
    (hb : co.toNat + 10 * cts.length < 2 ^ 63) (w : Word) (hw : w = co + 10 * UInt64.ofNat k) :
    cts.getD ((w.toNat - co.toNat) / 10) default = cts[k] := by
  have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  subst hw
  rw [widx2 _ _ (by rw [UInt64.toNat_mul, hk']; simp; omega), UInt64.toNat_mul, hk']
  simp only [show (10 : Word).toNat = 10 from rfl]
  rw [Nat.mod_eq_of_lt (by omega), show co.toNat + 10 * k - co.toNat = 10 * k by omega,
    Nat.mul_div_cancel_left _ (by decide)]
  simp [List.getD_eq_getElem?_getD, hk]

end L.Front.Ind
