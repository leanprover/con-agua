import ConAgua.Front.IndApplyRefine
import ConAgua.Front.ApplyDeclRefine

/-!
# The apply step of an `inductive` line against the twin, II: the scratch pool and the lookups

`IExt m m'`: what the validation does to the memory (`IFL` appended to, the level heap and its
top `CTL[192]` written, every word of `IFL` up to its old top kept). The allocator's and the push's
facts (`allocW_factsA`, `pushLW_factsA`), the table lookups against `StateD.name`/`getDeclD`
(`lkW_name`, `lkW_expr`), word indices without overflow (`widx`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend


namespace L.Front.Ind

/-! ## Words and indices -/

theorem wd_eq (m : Mem) (A : ArrId) (x : Word) : rdW (m.arr64 A) x = wd m A x.toNat := rfl

theorem wd_setA (m : Mem) (A B : ArrId) (i v : Word) (j : Nat) :
    wd (m.set64 A i v) B j =
      if A = B ∧ i.toNat = j ∧ j < (m.arr64 A).size then v else wd m B j := by
  by_cases hAB : A = B
  · subst hAB
    unfold wd
    rw [arr_set64]
    by_cases hc : i.toNat = j ∧ j < (m.arr64 A).size <;> simp [hc]
  · unfold wd
    rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hAB)]
    simp [hAB]

/-- A word index `o + c * k + s` without overflow. -/
theorem widx (o c k s : Word) (h : o.toNat + c.toNat * k.toNat + s.toNat < 2 ^ 64) :
    (o + c * k + s).toNat = o.toNat + c.toNat * k.toNat + s.toNat := by
  have h1 : c.toNat * k.toNat < 2 ^ 64 := by omega
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_eq_of_lt h1]
  omega

theorem widx2 (o k : Word) (h : o.toNat + k.toNat < 2 ^ 64) : (o + k).toNat = o.toNat + k.toNat := by
  rw [UInt64.toNat_add]; omega

theorem wsucc (j : Word) (l : Word) (h : j < l) : (j + 1).toNat = j.toNat + 1 := by
  have := UInt64.lt_iff_toNat_lt.mp h
  have := UInt64.toNat_lt l
  rw [UInt64.toNat_add]; simp; omega

theorem len64_toNat (m : Mem) (A : ArrId) (hs : (m.arr64 A).size < 2 ^ 63) :
    (m.len64 A).toNat = (m.arr64 A).size := by
  simp only [Mem.len64]; exact toNat_ofNat_size _ hs

/-! ## The scratch pool's growth -/

/-- **What the validation does to the memory**: `IFL` is appended to (its top grows, every word up
to the old top kept), the level heap and its top are written, nothing else. -/
structure IExt (m m' : Mem) : Prop where
  frame : MemFrame [IFL, LH] [192] m m'
  top : topN m IFL ≤ topN m' IFL
  keep : ∀ i, 1 ≤ i → i ≤ topN m IFL → wd m' IFL i = wd m IFL i

theorem IExt.refl (m : Mem) : IExt m m := ⟨MemFrame.refl _ _ _, Nat.le_refl _, fun _ _ _ => rfl⟩

theorem IExt.trans {m₁ m₂ m₃ : Mem} (h₁ : IExt m₁ m₂) (h₂ : IExt m₂ m₃) : IExt m₁ m₃ :=
  ⟨h₁.frame.trans h₂.frame, Nat.le_trans h₁.top h₂.top,
    fun i h1 h2 => (h₂.keep i h1 (Nat.le_trans h2 h₁.top)).trans (h₁.keep i h1 h2)⟩

theorem IExt.ifr {m m' : Mem} (h : IExt m m') : m'.arr64 IFR = m.arr64 IFR :=
  h.frame.1 IFR (by decide) (by decide)

theorem IExt.size {m m' : Mem} (h : IExt m m') (A : ArrId) : (m'.arr64 A).size = (m.arr64 A).size :=
  h.frame.2.2.1 A

theorem IExt.other {m m' : Mem} (h : IExt m m') (A : ArrId) (h1 : A ≠ IFL) (h2 : A ≠ LH) (h3 : A ≠ CTL) :
    m'.arr64 A = m.arr64 A :=
  h.frame.1 A (by simp [h1, h2]) h3

/-- The allocator's facts. -/
theorem allocW_factsA {m m' : Mem} {A : ArrId} {k o : Word} (hA : A ≠ CTL)
    (hs : (m.arr64 A).size < 2 ^ 63) (ht : topN m A < 2 ^ 63) (h : allocW m A k = some (o, m')) :
    o.toNat = topN m A + 1 ∧ topN m' A = topN m A + k.toNat ∧
    topN m A + 1 + k.toNat ≤ (m.arr64 A).size ∧ (∀ i, i ≠ 0 → wd m' A i = wd m A i) ∧
    MemFrame [A] [] m m' := by
  unfold allocW at h
  have hl := len64_toNat m A hs
  have hw0 : rdW (m.arr64 A) 0 = wd m A 0 := rfl
  have e1 : (rdW (m.arr64 A) 0 + 1).toNat = topN m A + 1 := by
    rw [widx2 _ _ (by rw [hw0]; simp [topN] at ht ⊢; omega)]; simp [topN, hw0]
  split at h; cases h
  split at h; cases h; rename_i h1
  split at h; cases h; rename_i h2
  cases h
  have h1' := UInt64.not_lt.mp h1
  rw [UInt64.le_iff_toNat_le, hl, e1] at h1'
  have h2' := UInt64.not_lt.mp h2
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hl, e1]; exact h1'),
    hl, e1] at h2'
  have e2 : (rdW (m.arr64 A) 0 + 1 - 1 + k).toNat = topN m A + k.toNat := by
    have : rdW (m.arr64 A) 0 + 1 - 1 = rdW (m.arr64 A) 0 := by simp
    rw [this, widx2 _ _ (by rw [hw0]; simp [topN] at ht ⊢; omega)]
    simp [topN, hw0]
  refine ⟨e1, ?_, by omega, fun i hi => ?_, MemFrame.set64 _ _ hA _ _⟩
  · simp only [topN, wd_setA, show (0 : Word).toNat = 0 from rfl, true_and]
    rw [if_pos (by omega)]
    exact e2
  · rw [wd_setA, if_neg (by simp; omega)]

/-- The push's facts. -/
theorem pushLW_factsA {m m' : Mem} {x o : Word} (hs : (m.arr64 IFL).size < 2 ^ 63)
    (ht : topN m IFL < 2 ^ 63) (h : pushLW m x = some (o, m')) :
    o.toNat = topN m IFL + 1 ∧ topN m' IFL = topN m IFL + 1 ∧ o.toNat < (m.arr64 IFL).size ∧
    wd m' IFL o.toNat = x ∧ (∀ i, i ≠ 0 → i ≠ o.toNat → wd m' IFL i = wd m IFL i) ∧
    MemFrame [IFL] [] m m' := by
  unfold pushLW at h
  rcases ha : allocW m IFL 1 with _ | ⟨o', m₁⟩ <;> simp only [ha, pushK, reduceCtorEq] at h
  cases h
  obtain ⟨a1, a2, a3, a4, a5⟩ := allocW_factsA (by decide) hs ht ha
  have hs1 : (m₁.arr64 IFL).size = (m.arr64 IFL).size := a5.2.2.1 IFL
  simp only [show (1 : Word).toNat = 1 from rfl] at a2 a3
  refine ⟨a1, ?_, by omega, ?_, fun i h1 h2 => ?_, a5.trans (MemFrame.set64 _ _ (by decide) _ _)⟩
  · simp only [topN, wd_setA]
    rw [if_neg (by simp; omega)]
    exact a2
  · rw [wd_setA, if_pos ⟨rfl, rfl, by omega⟩]
  · rw [wd_setA, if_neg (by simp; omega), a4 i h1]

/-- A push as an `IExt`, with the pushed word on top. -/
theorem pushLW_ext {m m' : Mem} {x o : Word} (hs : (m.arr64 IFL).size < 2 ^ 63)
    (ht : topN m IFL < 2 ^ 63) (h : pushLW m x = some (o, m')) :
    IExt m m' ∧ topN m' IFL = topN m IFL + 1 ∧ wd m' IFL (topN m IFL + 1) = x := by
  obtain ⟨p1, p2, -, p4, p5, p6⟩ := pushLW_factsA hs ht h
  refine ⟨⟨p6.mono (by simp) (by simp), by omega, fun i h1 h2 => p5 i (by omega) (by omega)⟩, p2, ?_⟩
  rw [← p1]; exact p4

/-- An allocation in `IFL` as an `IExt`. -/
theorem allocW_ext {m m' : Mem} {k o : Word} (hs : (m.arr64 IFL).size < 2 ^ 63)
    (ht : topN m IFL < 2 ^ 63) (h : allocW m IFL k = some (o, m')) :
    IExt m m' ∧ o.toNat = topN m IFL + 1 ∧ topN m' IFL = topN m IFL + k.toNat ∧
      topN m IFL + 1 + k.toNat ≤ (m.arr64 IFL).size := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := allocW_factsA (by decide) hs ht h
  exact ⟨⟨a5.mono (by simp) (by simp), by omega, fun i h1 _ => a4 i (by omega)⟩, a1, a2, a3⟩

/-! ## Lookups -/

theorem lkW_name {m : Mem} {st : StateD} (hD : StateDR m st) {x w : Word} (a : AState)
    (h : lkW m NID x = some w) :
    (st.name x.toNat).run a = .ok (decI w, a) ∧ w.toNat < 2 ^ 32 := by
  unfold lkW at h
  split at h
  · rename_i hok
    cases h
    obtain ⟨h1, h2⟩ := hD.names.read _ _ _ _ hok
    exact ⟨by simp [StateD.name, h1]; rfl, h2⟩
  · cases h

theorem lkW_expr {m : Mem} {st : StateD} (hD : StateDR m st) {x w : Word} (a : AState)
    (h : lkW m EID x = some w) :
    (getDeclD st x.toNat).run a = .ok (decE w, a) ∧ w.toNat < 2 ^ 32 := by
  unfold lkW at h
  split at h
  · rename_i hok
    cases h
    obtain ⟨h1, h2⟩ := hD.exprs.read _ _ _ _ hok
    exact ⟨by simp [getDeclD, StateD.expr, h1, decE_eq]; rfl, h2⟩
  · cases h

/-! ## The pool's top in range -/

/-- The scratch pool's top is in range, the pool below `2^63` words. -/
def TopOK (m : Mem) : Prop := (m.arr64 IFL).size < 2 ^ 63 ∧ topN m IFL ≤ (m.arr64 IFL).size

theorem pushLW_ok {m m' : Mem} {x o : Word} (hT : TopOK m) (h : pushLW m x = some (o, m')) :
    IExt m m' ∧ TopOK m' ∧ topN m' IFL = topN m IFL + 1 ∧ wd m' IFL (topN m IFL + 1) = x := by
  have ht : topN m IFL < 2 ^ 63 := by have := hT.1; have := hT.2; omega
  obtain ⟨p1, p2, p3, -, -, -⟩ := pushLW_factsA hT.1 ht h
  obtain ⟨e1, e2, e3⟩ := pushLW_ext hT.1 ht h
  exact ⟨e1, ⟨by rw [e1.size]; exact hT.1, by rw [e1.size, e2]; omega⟩, e2, e3⟩

theorem allocW_ok {m m' : Mem} {k o : Word} (hT : TopOK m) (h : allocW m IFL k = some (o, m')) :
    IExt m m' ∧ TopOK m' ∧ o.toNat = topN m IFL + 1 ∧ topN m' IFL = topN m IFL + k.toNat := by
  have ht : topN m IFL < 2 ^ 63 := by have := hT.1; have := hT.2; omega
  obtain ⟨e1, e2, e3, e4⟩ := allocW_ext hT.1 ht h
  exact ⟨e1, ⟨by rw [e1.size]; exact hT.1, by rw [e1.size, e3]; omega⟩, e2, e3⟩

/-- `IExt` leaves the id tables alone. -/
theorem IExt.tbl {m m' : Mem} (h : IExt m m') (b : ArrId) (hb : TblIx b) : TblSame m m' b :=
  TblSame.of_frameD h.frame hb (by rcases hb with rfl | rfl | rfl <;> decide)
    (by rcases hb with rfl | rfl | rfl <;> decide) (by rcases hb with rfl | rfl | rfl <;> simp [szC])
    (by rcases hb with rfl | rfl | rfl <;> simp [spS])

theorem lkW_congr {m m' : Mem} {B : ArrId} (h : TblSame m m' B) (x : Word) :
    lkW m' B x = lkW m B x := by
  unfold lkW; rw [tblOK_congr h, tblW_congr h]

theorem mapLk_ext {m m' : Mem} (h : IExt m m') (f x : Word) : mapLk m' f x = mapLk m f x := by
  simp only [mapLk, lkW_congr (h.tbl NID (.inl rfl)),
    lkW_congr (h.tbl EID (.inr (.inr rfl)))]

theorem ofNat_toNat' (j : Word) : UInt64.ofNat j.toNat = j := UInt64.ofNat_toNat

/-! ## `vi_map_go`, `vi_ids_go`, `vi_listed_go` -/

/-- **`vi_map_go`**: the lookups of the records `j ‥ l` pushed in order. -/
theorem mapGoW_facts : ∀ (n : Nat) (m m' : Mem) (o l sz s f j : Word),
    mapGoW n m o l sz s f j = some m' → TopOK m → j ≤ l →
    IExt m m' ∧ TopOK m' ∧ topN m' IFL = topN m IFL + (l.toNat - j.toNat) ∧
    ∀ k : Nat, j.toNat ≤ k → k < l.toNat →
      mapLk m f (rdW (m.arr64 IFR) (o + sz * UInt64.ofNat k + s)) =
        some (wd m' IFL (topN m IFL + 1 + (k - j.toNat))) := by
  intro n
  induction n with
  | zero => intro m m' o l sz s f j h; simp [mapGoW] at h
  | succ n ih =>
    intro m m' o l sz s f j h hT hjl
    simp only [mapGoW] at h
    split at h
    · rename_i hlj
      cases h
      have : j = l := by
        apply UInt64.toNat_inj.mp
        have := UInt64.le_iff_toNat_le.mp hjl; have := UInt64.le_iff_toNat_le.mp hlj; omega
      subst this
      exact ⟨IExt.refl _, hT, by simp, fun k h1 h2 => by omega⟩
    rename_i hlj
    have hjl' : j < l := UInt64.not_le.mp hlj
    cases hk : mapLk m f (rdW (m.arr64 IFR) (o + sz * j + s)) with
    | none => rw [hk, lkPushK_none, restK_none] at h; cases h
    | some w =>
    rw [hk, lkPushK_some] at h
    rcases hp : pushLW m w with _ | ⟨o1, m₁⟩ <;> simp only [hp, restK, reduceCtorEq] at h
    obtain ⟨x1, x2, x3, x4⟩ := pushLW_ok hT hp
    have hj1 := wsucc j l hjl'
    obtain ⟨y1, y2, y3, y4⟩ := ih m₁ m' o l sz s f (j + 1) h x2
      (UInt64.le_iff_toNat_le.mpr (by rw [hj1]; exact UInt64.lt_iff_toNat_lt.mp hjl'))
    have hjn := UInt64.lt_iff_toNat_lt.mp hjl'
    refine ⟨x1.trans y1, y2, by rw [y3, x3, hj1]; omega, fun k h1 h2 => ?_⟩
    by_cases hkj : k = j.toNat
    · subst hkj
      rw [ofNat_toNat', hk, Nat.sub_self, Nat.add_zero, ← x4, y1.keep _ (by omega) (by omega)]
    · have := y4 k (by rw [hj1]; omega) h2
      rw [mapLk_ext x1, x1.ifr, x3, hj1] at this
      rw [this]
      congr 2; omega

/-- **`vi_ids_go`**: the names of `IFL[o + k ‥ o + l)` pushed in order. -/
theorem idsGoW_facts : ∀ (n : Nat) (m m' : Mem) (o l k : Word),
    idsGoW n m o l k = some m' → TopOK m → k ≤ l → o.toNat + l.toNat ≤ topN m IFL + 1 →
    IExt m m' ∧ TopOK m' ∧ topN m' IFL = topN m IFL + (l.toNat - k.toNat) ∧
    ∀ c : Nat, k.toNat ≤ c → c < l.toNat →
      lkW m NID (wd m IFL (o.toNat + c)) = some (wd m' IFL (topN m IFL + 1 + (c - k.toNat))) := by
  intro n
  induction n with
  | zero => intro m m' o l k h; simp [idsGoW] at h
  | succ n ih =>
    intro m m' o l k h hT hkl hol
    simp only [idsGoW] at h
    split at h
    · rename_i hlk
      cases h
      have : k = l := by
        apply UInt64.toNat_inj.mp
        have := UInt64.le_iff_toNat_le.mp hkl; have := UInt64.le_iff_toNat_le.mp hlk; omega
      subst this
      exact ⟨IExt.refl _, hT, by simp, fun c h1 h2 => by omega⟩
    rename_i hlk
    have hkl' : k < l := UInt64.not_le.mp hlk
    have hkn := UInt64.lt_iff_toNat_lt.mp hkl'
    have hok : (o + k).toNat = o.toNat + k.toNat := widx2 _ _ (by have := hT.1; have := hT.2; omega)
    cases hk : lkW m NID (rdW (m.arr64 IFL) (o + k)) with
    | none => rw [hk, lkPushK_none, restK_none] at h; cases h
    | some w =>
    rw [hk, lkPushK_some] at h
    rcases hp : pushLW m w with _ | ⟨o1, m₁⟩ <;> simp only [hp, restK, reduceCtorEq] at h
    obtain ⟨x1, x2, x3, x4⟩ := pushLW_ok hT hp
    have hk1 := wsucc k l hkl'
    obtain ⟨y1, y2, y3, y4⟩ := ih m₁ m' o l (k + 1) h x2
      (UInt64.le_iff_toNat_le.mpr (by rw [hk1]; exact hkn)) (by rw [x3]; omega)
    refine ⟨x1.trans y1, y2, by rw [y3, x3, hk1]; omega, fun c h1 h2 => ?_⟩
    by_cases hck : c = k.toNat
    · subst hck
      rw [wd_eq, hok] at hk
      rw [hk, Nat.sub_self, Nat.add_zero, ← x4, y1.keep _ (by omega) (by omega)]
    · have := y4 c (by rw [hk1]; omega) h2
      rw [lkW_congr (x1.tbl NID (.inl rfl)),
        x1.keep _ (by omega) (by omega), x3, hk1] at this
      rw [this]
      congr 2; omega

/-! ## The records survive the validation's writes -/

section frame
variable {b : ByteArray} {m m' : Mem} (hE : IExt m m')
include hE

theorem IExt.wdR (i : Nat) : wd m' IFR i = wd m IFR i := by simp only [wd, hE.ifr]

theorem IExt.topR : topN m' IFR = topN m IFR := by unfold topN; rw [hE.wdR]

theorem NumsF.ext {off : Nat} {ns : List Nat} (h : NumsF m off ns) : NumsF m' off ns := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by have := hE.top; omega, fun k hk => ?_⟩
  rw [hE.keep _ (by omega) (by omega)]; exact h3 k hk

theorem CVF.ext {p : Nat} {cv : ConLeche.Frontend.CVRec} (h : CVF b m p cv) : CVF b m' p cv := by
  simp only [CVF, hE.wdR] at h ⊢; exact h

theorem TyF.ext {t : Nat} {ty : ConLeche.Frontend.IndTypeRec} (h : TyF b m t ty) : TyF b m' t ty := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.ext hE, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hE.wdR] at * <;> first | assumption | exact h3.ext hE

theorem OptW.ext {i : Nat} {o : Option Nat} (h : OptW m i o) : OptW m' i o := by
  cases o <;> simp only [OptW, hE.wdR] at h ⊢ <;> exact h

theorem CtF.ext {c : Nat} {ct : ConLeche.Frontend.IndCtorRec} (h : CtF b m c ct) : CtF b m' c ct := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.ext hE, by simpa only [hE.wdR] using h2, by simpa only [hE.wdR] using h3, h4.ext hE,
    h5.ext hE⟩

theorem RecF.ext {r : Nat} {rc : ConLeche.Frontend.IndRecRec} (h : RecF b m r rc) : RecF b m' r rc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨h1.ext hE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [hE.wdR]) <;> try assumption
  · have := hE.top; omega
  · intro j hj
    obtain ⟨r1, r2, r3⟩ := h10 j hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hE.keep _ (by omega) (by omega)]; exact r1
    · rw [hE.keep _ (by omega) (by omega)]; exact r2
    · rw [hE.keep _ (by omega) (by omega)]; exact r3

theorem ListF.ext {α : Type} {F F' : Nat → α → Prop} {sz off : Nat} {xs : List α}
    (hF : ∀ p x, F p x → F' p x) (h : ListF F m sz off xs) : ListF F' m' sz off xs :=
  ⟨h.1, by rw [hE.topR]; exact h.2.1, fun j hj => hF _ _ (h.2.2 j hj)⟩

/-- **`IndFR` survives the validation's writes.** -/
theorem IndFR.ext {to tn co cn ro rn : Word} {tys : List ConLeche.Frontend.IndTypeRec}
    {cts : List ConLeche.Frontend.IndCtorRec} {rcs : List ConLeche.Frontend.IndRecRec}
    (h : IndFR b m to tn co cn ro rn tys cts rcs) : IndFR b m' to tn co cn ro rn tys cts rcs := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2.ext hE (fun _ _ x => x.ext hE), h3, h4.ext hE (fun _ _ x => x.ext hE), h5,
    h6.ext hE (fun _ _ x => x.ext hE)⟩

end frame

/-! ## `mapM` by index -/

theorem mapM_run_idx {α β : Type} (f : α → AM β) (a : AState) :
    ∀ (xs : List α) (ys : List β) (hl : ys.length = xs.length),
      (∀ k (hk : k < xs.length), (f xs[k]).run a = .ok (ys[k]'(by rw [hl]; exact hk), a)) →
      (xs.mapM f).run a = .ok (ys, a)
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [List.mapM_cons]
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [run_bind _ _ a _ h0, run_bind _ _ a _ (mapM_run_idx f a xs ys (by simpa using hl)
      fun k hk => by have := h (k + 1) (by simp; omega); simpa using this)]
    rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- The handles of `IFL[o ‥ o + l)`. -/
def islice {k : IdxKind} (m : Mem) (o l : Nat) : List (Idx k) :=
  (List.range l).map fun c => decI (wd m IFL (o + c))

theorem islice_length {k : IdxKind} (m : Mem) (o l : Nat) : (islice (k := k) m o l).length = l := by
  simp [islice]

theorem islice_get {k : IdxKind} (m : Mem) (o l c : Nat) (hc : c < (islice (k := k) m o l).length) :
    (islice (k := k) m o l)[c] = decI (wd m IFL (o + c)) := by
  simp [islice]

/-! ## `vi_map`: the twin's `mapM` of lookups -/

/-- **`vi_map` is a twin `mapM` of lookups**: on a list `xs` whose ids are the records' words, a
lookup `look` that the model's lookup answers (`hlk`), the twin's `mapM` returns the handles the
model pushed, the slice `(lo, l)`. -/
theorem mapW_twin {α : Type} {kd : IdxKind} {n : Nat} {m m' : Mem} {o l sz s f lo l' : Word} (hT : TopOK m)
    (h : mapW n m o l sz s f = some ((lo, l'), m')) (a : AState) (xs : List α) (ids : α → Nat)
    (look : Nat → AM (Idx kd)) (hlen : l.toNat = xs.length)
    (hid : ∀ k (hk : k < xs.length), (rdW (m.arr64 IFR) (o + sz * UInt64.ofNat k + s)).toNat = ids xs[k])
    (hlk : ∀ x w, mapLk m f x = some w → (look x.toNat).run a = .ok (decI w, a) ∧ w.toNat < 2 ^ 32) :
    (xs.mapM fun x => look (ids x)).run a = .ok (islice (k := kd) m' lo.toNat xs.length, a) ∧
      IExt m m' ∧ TopOK m' ∧ l' = l ∧ lo.toNat = topN m IFL + 1 ∧ topN m' IFL = topN m IFL + xs.length ∧
      ∀ c, c < xs.length → (wd m' IFL (lo.toNat + c)).toNat < 2 ^ 32 := by
  cases n with
  | zero => simp [mapW] at h
  | succ n =>
  simp only [mapW] at h
  rcases ha : allocW m IFL 0 with _ | ⟨lo', m₁⟩ <;> simp only [ha, allocK, reduceCtorEq] at h
  rcases hg : mapGoW n m₁ o l sz s f 0 with _ | m₂ <;> simp only [hg, sliceK, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  obtain ⟨a1, a2, a3, a4⟩ := allocW_ok hT ha
  simp only [show (0 : Word).toNat = 0 from rfl, Nat.add_zero] at a4
  obtain ⟨g1, g2, g3, g4⟩ := mapGoW_facts n m₁ _ o l sz s f 0 hg a2 (UInt64.le_iff_toNat_le.mpr (Nat.zero_le _))
  simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at g3
  have hw : ∀ c (hc : c < xs.length),
      (look (ids xs[c])).run a = .ok (decI (wd m₂ IFL (lo'.toNat + c)), a) ∧
        (wd m₂ IFL (lo'.toNat + c)).toNat < 2 ^ 32 := by
    intro c hc
    have := g4 c (Nat.zero_le _) (by rw [hlen]; exact hc)
    simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at this
    rw [mapLk_ext a1, a1.ifr] at this
    have hh := hlk _ _ this
    rw [hid c hc, a4, ← a3] at hh
    exact hh
  refine ⟨mapM_run_idx _ a xs _ (islice_length _ _ _) (fun k hk => ?_), a1.trans g1, g2, rfl, a3,
    by rw [g3, a4, hlen], fun c hc => (hw c hc).2⟩
  rw [islice_get]; exact (hw k hk).1

end L.Front.Ind
