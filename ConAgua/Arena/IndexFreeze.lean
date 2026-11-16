module

public import ConAgua.Arena.IndexRel
public import ConAgua.Arena.CheckerL
public import ConAgua.Arena.EnvFlags
import all ConAgua.Arena.CheckerL
import ConAgua.Arena.WhnfDeltaRefine
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

@[expose] public section

/-!
# The frozen stream index: `lit_from`, `index_freeze`, `from_le`

The twin freezes a stream's index past its last record (`IStreamIndex.freeze`, upstream #579): the
ten literal names off the pin table into the base (`IFBase.lits`), and for each literal flag the
first counter from which a record's view holds its names (`litFrom`: `natFrom`, `strFrom`). L
writes the names into `CTL[162‥171]` and the thresholds into `CTL[172]`, `CTL[173]` (`optW`:
`FrozenR`); a job sets its flags by one comparison each (`fromLe`, `from_le`). Generated models
and their refinements.
-/

set_option experimental.vcgen true

open ConRon.Arena Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The models (generated) -/

/-- **`from_le` is its model** (generated). -/
l_model fromLe_specW (p : Prog) (hp : p.lookup "from_le" = some fromLeL)
  fns [hp ↦ fromLeW]
  grind [arena_grind]

/-- **`lit_from` is its model** (generated; the recursive call through its own run). -/
l_model litFrom_specW (p : Prog) (hp : p.lookup "lit_from" = some litFromL)
  fns [hp ↦ litFromW]
  specs [callW_spec p n "base_row_get", callW_spec p n "lit_from"]
  grind [arena_grind]

/-- **`index_freeze` is its model** (generated). -/
l_model indexFreeze_specW (p : Prog) (hp : p.lookup "index_freeze" = some indexFreezeL)
  fns [hp ↦ indexFreezeW]
  specs [callW_spec p n "pin_at", callW_spec p n "lit_from"]
  grind [arena_grind]

/-! ## `from_le` -/

variable {p : Prog}

/-- **`from_le(o, c)` refines `fromLe`** of the threshold `optW o` at the counter `c`. -/
@[refines ConRon.Arena.fromLe]
theorem fromLe_refines (hp : p.lookup "from_le" = some fromLeL) (n : Nat) (s₀ : St) (o c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "from_le" [o, c]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ (r.headD 0 != 0) = fromLe (optW o) c.toNat; ⊤⦄ :=
  triple_post (fromLe_specW p hp n s₀ o c) fun r s ⟨hL, hm⟩ => by
    rw [fromLeW.eq_1] at hm
    by_cases ho : o = 0
    · rw [ite_eq_left ho] at hm
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hm)
      refine ⟨hL, h2.symm, ?_⟩
      rw [← h1, optW, ite_eq_left ho]; rfl
    · rw [ite_eq_right ho] at hm
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hm)
      refine ⟨hL, h2.symm, ?_⟩
      have ho' : 1 ≤ o.toNat := by
        have : o.toNat ≠ 0 := fun e => ho (UInt64.toNat_inj.mp (by simpa using e)); omega
      have hsub : (o - 1).toNat = o.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using ho'))]; simp
      rw [← h1, optW, ite_eq_right ho, fromLe]
      by_cases hle : o - 1 ≤ c
      · rw [ite_eq_left hle]
        rw [UInt64.le_iff_toNat_le, hsub] at hle
        simp [hle]
      · rw [ite_eq_right hle]
        rw [UInt64.le_iff_toNat_le, hsub] at hle
        simp [hle]

/-! ## `lit_from` -/

/-- A row of the stream index and the twin's entry. -/
theorem IndexR.idx_cases {m : Mem} {I : IStreamIndex} (hI : IndexR m I) (n : NIdx) :
    ((baseRow m n.word.toUInt64).1 = 0 ∧ I.base.idx[n]? = none) ∨
      ((baseRow m n.word.toUInt64).1 ≠ 0 ∧
        ∃ ci, I.base.idx[n]? = some ((baseRow m n.word.toUInt64).1.toNat - 1, ci)) := by
  have h := hI.base n
  rcases hx : I.base.idx[n]? with _ | ⟨c, ci⟩ <;>
    by_cases hz : (baseRow m n.word.toUInt64).1 = 0 <;> simp_all

/-- **`lit_from`'s recursion is `litFrom`** over the stream index's rows. -/
theorem litFrom_rec (hp : p.lookup "lit_from" = some litFromL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) {m : Mem} {I : IStreamIndex}
    {lits : List NIdx} (hI : IndexR m I) (hl : lits.map (·.word.toUInt64) = litWords m)
    :
    ∀ (n : Nat) (i stop r : Word) (m' : Mem), i.toNat ≤ 10 →
      litFromW p n m i stop = some (r, m') →
      m' = m ∧ optW r = litFrom I.base.idx lits i.toNat stop.toNat := by
  have ⟨hlen, hg⟩ := lits_get hl
  intro n
  induction n with
  | zero => intro i stop r m' _ h; rw [litFromW.eq_1] at h; cases h
  | succ n ih =>
    intro i stop r m' hi h
    rw [litFrom]
    by_cases hs : stop ≤ i
    · rw [litFromW.arm1 _ _ _ _ _ hs] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have : i.toNat ≥ stop.toNat := by rw [UInt64.le_iff_toNat_le] at hs; omega
      refine ⟨h2.symm, ?_⟩
      rw [ite_eq_left this, ← h1]; rfl
    have hs' : ¬ i.toNat ≥ stop.toNat := by rw [UInt64.le_iff_toNat_le] at hs; omega
    rw [ite_eq_right hs']
    by_cases h10 : 10 ≤ i
    · rw [litFromW.arm2 _ _ _ _ _ hs h10] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      have : ¬ i.toNat < lits.length := by rw [UInt64.le_iff_toNat_le] at h10; simp at h10; omega
      refine ⟨h2.symm, ?_⟩
      rw [dite_eq_right this, ← h1]; rfl
    have hi10 : i.toNat < 10 := by rw [UInt64.le_iff_toNat_le] at h10; simp at h10; omega
    have hlt : i.toNat < lits.length := by omega
    rw [dite_eq_left hlt]
    rw [litFromW.arm3 _ _ _ _ _ hs h10] at h
    have hw := hg i.toNat hlt
    simp only [UInt64.ofNat_toNat] at hw
    rcases c1 : callW p n "base_row_get" [rdW (m.arr64 CTL) (162 + i)] m with _ | ⟨r₁, m₁⟩
    · rw [c1, litFromW.k_base_row_get.none] at h; cases h
    rw [c1] at h
    obtain ⟨s₁, hs₁, hm₁, -, hr₁⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (baseRowGet_spec p hb n ⟨m, Locals.init []⟩ _) c1
    simp only at hm₁
    have hm1 : m = m₁ := by rw [← hs₁, hm₁]
    subst hm1
    rcases hI.idx_cases lits[i.toNat] with ⟨hz, hn⟩ | ⟨hz, ci, hn⟩
    · rw [hw] at hz
      rw [litFromW.k_base_row_get.arm1 _ _ _ _ _ _ (by rw [hr₁]; exact hz)] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨h2.symm, ?_⟩
      rw [hn, ← h1]; rfl
    rw [hw] at hz hn
    have hc0 : r₁.headD 0 ≠ 0 := by rw [hr₁]; exact hz
    rw [litFromW.k_base_row_get.arm2 _ _ _ _ _ _ hc0] at h
    rw [hn]
    dsimp only
    have e1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rcases c2 : callW p n "lit_from" [i + 1, stop] m with _ | ⟨r₂, m₂⟩
    · rw [c2, litFromW.k_lit_from.none] at h; cases h
    rw [c2] at h
    obtain ⟨s₂, hs₂, -, hW₂⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (litFrom_specW p hp n ⟨m, Locals.init []⟩ (i + 1) stop) c2
    simp only at hW₂
    rw [hs₂] at hW₂
    obtain ⟨hm₂, ho₂⟩ := ih (i + 1) stop _ _ (by omega) hW₂
    have hm2 : m = m₂ := hm₂.symm
    subst hm2
    rw [e1] at ho₂
    rw [← ho₂]
    have hcr : (r₁.headD 0).toNat < 2 ^ 63 := by
      have h32 := litW_lt32 hl i.toNat hi10
      simp only [UInt64.ofNat_toNat] at h32
      rw [hr₁]; have := hI.rows _ h32; simp; omega
    by_cases h2z : r₂.headD 0 = 0
    · rw [litFromW.k_lit_from.arm1 _ _ _ _ h2z] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨h2.symm, ?_⟩
      rw [← h1, optW, optW, ite_eq_left h2z, ite_eq_left rfl]
    have hr2 : 1 ≤ (r₂.headD 0).toNat := by
      have : (r₂.headD 0).toNat ≠ 0 := fun e => h2z (UInt64.toNat_inj.mp (by simpa using e)); omega
    have hsub : (r₂.headD 0 - 1).toNat = (r₂.headD 0).toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hr2))]; simp
    have hc1 : 1 ≤ (r₁.headD 0).toNat := by
      have : (r₁.headD 0).toNat ≠ 0 := fun e => hc0 (UInt64.toNat_inj.mp (by simpa using e)); omega
    have hrh : r₁.headD 0 = (baseRow m (rdW (m.arr64 CTL) (162 + i))).fst := by rw [hr₁]; rfl
    simp only [optW, ite_eq_right h2z]
    by_cases hle : r₁.headD 0 ≤ r₂.headD 0 - 1
    · rw [litFromW.k_lit_from.arm2 _ _ _ _ h2z hle] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨h2.symm, ?_⟩
      rw [UInt64.le_iff_toNat_le, hsub, hrh] at hle
      rw [hrh] at hc1
      rw [← h1, ite_eq_right h2z, ite_eq_left (by omega)]
    · rw [litFromW.k_lit_from.eq_2, ite_eq_right (by simpa using h2z), ite_eq_right hle] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨h2.symm, ?_⟩
      rw [UInt64.le_iff_toNat_le, hsub] at hle
      have ec : (r₁.headD 0 + 1).toNat = (r₁.headD 0).toNat + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
      have hne : r₁.headD 0 + 1 ≠ 0 := fun e => by
        have := congrArg UInt64.toNat e; rw [ec] at this; simp at this
      rw [← h1, ite_eq_right hne, ec]
      rw [hrh] at hle hc1
      rw [hrh, ite_eq_right (by omega)]
      congr 1; omega

/-- **`lit_from(i, stop)` refines `litFrom`** over the stream index's rows of the literal names
`CTL[162 + i‥]`, its result an `optW` (`FrozenR`'s encoding). -/
@[refines ConRon.Arena.litFrom]
theorem litFrom_refines (hp : p.lookup "lit_from" = some litFromL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (n : Nat) (s₀ : St) {I : IStreamIndex}
    {lits : List NIdx} (hI : IndexR s₀.mem I) (hl : lits.map (·.word.toUInt64) = litWords s₀.mem)
    (i stop : Word) (hi : i.toNat ≤ 10) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_from" [i, stop]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      optW (r.headD 0) = litFrom I.base.idx lits i.toNat stop.toNat; ⊤⦄ :=
  triple_post (litFrom_specW p hp n s₀ i stop) fun r s ⟨hL, hm⟩ => by
    obtain ⟨h1, h2⟩ := litFrom_rec hp hb hI hl n i stop _ _ hi hm
    exact ⟨hL, h1, h2⟩

/-! ## `index_freeze` -/

/-- **`IndexR` across a memory that changes only `CTL` words outside `0‥159`.** -/
theorem IndexR.ctlHi {m m' : Mem} {I : IStreamIndex} (h : IndexR m I)
    (ha : ∀ b : TieredArray, b ≠ CTL → m'.arr64 b = m.arr64 b)
    (hc : ∀ x : Word, x.toNat < 160 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) : IndexR m' I := by
  have hP : erecP m' = erecP m := by
    funext i
    simp only [erecP, erTop, erecTop1, ha EREC (by decide), ha (tier1 EREC) (by decide),
      hc 129 (by decide), hc 130 (by decide)]
    rfl
  have hb : ∀ w, baseRow m' w = baseRow m w := fun w => by
    simp only [baseRow, ha (eixArr (rowTag w) : TieredArray)
      (by unfold eixArr; split <;> (try split) <;> decide)]
  have hbt : ∀ w, baseTbl m' w = baseTbl m w := fun w => by
    simp only [baseTbl, ha (tixArr (rowTag w) : TieredArray)
      (by unfold tixArr; split <;> (try split) <;> decide)]
  have hF : m'.arr64 FIRSTS = m.arr64 FIRSTS := ha _ (by decide)
  exact ⟨fun n => by rw [hb, hP]; exact h.base n, fun n => by rw [hbt, hP]; exact h.btbl n,
    fun i hi => by rw [hF]; exact h.firsts i hi, by rw [hF]; exact h.firstsSize,
    by rw [hc 128 (by decide)]; exact h.next, fun x hx => by rw [hb]; exact h.rows x hx⟩

/-- The lookups of the freeze. -/
structure FreezeProg (p : Prog) : Prop where
  pin : p.lookup "pin_at" = some pinAtL
  litFrom : p.lookup "lit_from" = some litFromL
  baseGet : p.lookup "base_row_get" = some baseRowGetL
  freeze : p.lookup "index_freeze" = some indexFreezeL

theorem pinW_setCtl (m : Mem) (k v : Word) (i : Nat) : pinW (m.set64 CTL k v) i = pinW m i := by
  simp only [pinW, Mem.arr64_set64_ne _ _ _ _ _ (by decide : (PINS : TieredArray) ≠ CTL)]

/-- The frozen index of `I` at the literal names `L` (`IStreamIndex.freeze`'s result). -/
def frozenAt (I : IStreamIndex) (L : List NIdx) : IStreamIndex :=
  ⟨{ I.base with lits := L }, I.firsts, I.next, litFrom I.base.idx L 0 NAT_LIT_COUNT,
    litFrom I.base.idx L 0 STR_LIT_COUNT⟩

theorem IndexR.frozenAt {m : Mem} {I : IStreamIndex} (h : IndexR m I) (L : List NIdx) :
    IndexR m (frozenAt I L) :=
  ⟨h.base, h.btbl, h.firsts, h.firstsSize, h.next, h.rows⟩

/-- The literal names off the pin table, `strLitNames`' order. -/
def pinLits (m : Mem) : List NIdx :=
  [1, 2, 3, 5, 6, 7, 8, 9, 10, 12].map fun i => decI (pinW m (1 + i))

/-- **The twin's freeze** at a filled pin table. -/
theorem freeze_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) (I : IStreamIndex) :
    (I.freeze).run a = .ok (frozenAt I (pinLits m), a) := by
  simp only [IStreamIndex.freeze, strLitNames, natLitNames, pinNat, pinNatZero, pinNatSucc, pinString,
    pinStringOfList, pinList, pinListNil, pinListCons, pinChar, pinCharOfNat, PIN_NAT, PIN_NAT_ZERO,
    PIN_NAT_SUCC, PIN_STRING, PIN_STRING_OF_LIST, PIN_LIST, PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR,
    PIN_CHAR_OF_NAT, StateT.run_bind, pinAt_run hF 1 (by decide), pinAt_run hF 2 (by decide), pinAt_run hF 3 (by decide), pinAt_run hF 5 (by decide), pinAt_run hF 6 (by decide), pinAt_run hF 7 (by decide), pinAt_run hF 8 (by decide), pinAt_run hF 9 (by decide), pinAt_run hF 10 (by decide), pinAt_run hF 12 (by decide), StateT.run_pure, pure_bind, except_ok_bind]
  rfl

/-- The freeze past the ten names: the two thresholds (`lit_from`) and their writes. -/
theorem freeze_tail (hP : FreezeProg p) {n : Nat} {m M : Mem} {I : IStreamIndex} {r : Word} {m' : Mem}
    (hI : IndexR m I) (hc : 173 < (m.arr64 CTL).size)
    (ha : ∀ b : TieredArray, b ≠ CTL → M.arr64 b = m.arr64 b)
    (hout : ∀ x : Word, x ∉ frozenCtl → rdW (M.arr64 CTL) x = rdW (m.arr64 CTL) x)
    (hsz : (M.arr64 CTL).size = (m.arr64 CTL).size)
    (hl : (pinLits m).map (·.word.toUInt64) = litWords M)
    (hm : indexFreezeW.k_lit_from p n (callW p n "lit_from" [0, 3] M) = some (r, m')) :
    FrozenR m' (frozenAt I (pinLits m)) ∧ IndexR m' (frozenAt I (pinLits m)) ∧
      MemFrame [] frozenCtl m m' := by
  have hlo : ∀ x : Word, x.toNat < 160 → rdW (M.arr64 CTL) x = rdW (m.arr64 CTL) x :=
    fun x hx => hout x (not_mem_frozenCtl (.inl (by omega)))
  have hIM : IndexR M I := hI.ctlHi ha hlo
  rcases c1 : callW p n "lit_from" [0, 3] M with _ | ⟨r₁, m₁⟩
  · rw [c1, indexFreezeW.k_lit_from.none] at hm; cases hm
  rw [c1, indexFreezeW.k_lit_from.eq_2] at hm
  obtain ⟨t₁, ht₁, -, hm₁, ho₁⟩ := triple_of_callW (s₀ := ⟨M, Locals.init []⟩)
    (litFrom_refines hP.litFrom hP.baseGet n ⟨M, Locals.init []⟩ hIM hl 0 3 (by decide)) c1
  simp only at hm₁ ho₁
  have e1 : M = m₁ := by rw [← ht₁, hm₁]
  subst e1
  rcases c2 : callW p n "lit_from" [0, 10] M with _ | ⟨r₂, m₂⟩
  · rw [c2, indexFreezeW.k_lit_from_2.none] at hm; cases hm
  rw [c2, indexFreezeW.k_lit_from_2.arm1] at hm
  obtain ⟨t₂, ht₂, -, hm₂, ho₂⟩ := triple_of_callW (s₀ := ⟨M, Locals.init []⟩)
    (litFrom_refines hP.litFrom hP.baseGet n ⟨M, Locals.init []⟩ hIM hl 0 10 (by decide)) c2
  simp only at hm₂ ho₂
  have e2 : M = m₂ := by rw [← ht₂, hm₂]
  subst e2
  obtain ⟨-, hme⟩ := Prod.mk.inj (Option.some.inj hm)
  subst hme
  have hcM : 173 < (M.arr64 CTL).size := by rw [hsz]; exact hc
  have hfr : MemFrame [] [172, 173] M ((M.set64 CTL 172 (r₁.headD 0)).set64 CTL 173 (r₂.headD 0)) :=
    ((MemFrame.setCtl _ _ _).mono (fun _ h => h) (by simp)).trans ((MemFrame.setCtl _ _ _).mono (fun _ h => h) (by simp))
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show (pinLits m).map (·.word.toUInt64) = _
    have hnot : ∀ i < 10, (162 + UInt64.ofNat i : Word) ∉ ([172, 173] : List Word) := by decide
    rw [hl]; exact (litWords_congr fun i hi => hfr.ctl _ (hnot i hi)).symm
  · have ho₁' : optW (r₁.headD 0) = litFrom I.base.idx (pinLits m) 0 NAT_LIT_COUNT := ho₁
    show litFrom I.base.idx (pinLits m) 0 NAT_LIT_COUNT = _
    rw [← ho₁']; congr 1
    simp [rdW_set64, Mem.size64_set64]; omega
  · have ho₂' : optW (r₂.headD 0) = litFrom I.base.idx (pinLits m) 0 STR_LIT_COUNT := ho₂
    show litFrom I.base.idx (pinLits m) 0 STR_LIT_COUNT = _
    rw [← ho₂']; congr 1
    simp [rdW_set64, Mem.size64_set64]; omega
  · exact IndexR.frozenAt (hIM.ctlHi (fun b hb => by simp only [Mem.arr64_set64_ne _ _ _ _ _ hb])
      (fun x hx => hfr.ctl x (by simp; constructor <;> (intro e; subst e; simp at hx)))) _
  · refine ⟨fun b _ hb => ?_, fun x hx => ?_, fun b => ?_⟩
    · simp only [Mem.arr64_set64_ne _ _ _ _ _ hb]; exact ha b hb
    · rw [hfr.ctl x (by simp; constructor <;> (intro e; subst e; revert hx; decide))]; exact hout x hx
    · by_cases hb : b = CTL
      · subst hb; simp [Mem.size64_set64, hsz]
      · simp only [Mem.arr64_set64_ne _ _ _ _ _ hb, ha b hb]

/-- **`index_freeze` refines `IStreamIndex.freeze`**: the names and the thresholds written
(`FrozenR`), nothing else but `CTL[162‥173]`, the index's rows untouched. -/
@[refines ConRon.Arena.IStreamIndex.freeze ConRon.Arena.strLitNames ConRon.Arena.natLitNames]
theorem indexFreeze_refines (hP : FreezeProg p) (n : Nat) (s₀ : St) {I : IStreamIndex} {a : AState}
    (hI : IndexR s₀.mem I) (hF : PinsFull s₀.mem a.pins) (hc : 173 < (s₀.mem.arr64 CTL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "index_freeze" []
    ⦃fun _ s' => LocEq s' s₀ ∧ (I.freeze).run a = .ok (frozenAt I (pinLits s₀.mem), a) ∧
      FrozenR s'.mem (frozenAt I (pinLits s₀.mem)) ∧ IndexR s'.mem (frozenAt I (pinLits s₀.mem)) ∧
      MemFrame [] frozenCtl s₀.mem s'.mem; ⊤⦄ :=
  triple_post (indexFreeze_specW p hP.freeze n s₀) fun r s ⟨hL, hm⟩ => by
    refine ⟨hL, freeze_run hF I, ?_⟩
    cases n with
    | zero => rw [indexFreezeW.eq_1] at hm; cases hm
    | succ n =>
    rw [indexFreezeW.arm1] at hm
    rcases c0 : callW p n "pin_at" [1] s₀.mem with _ | ⟨r0, m0⟩
    · rw [c0, indexFreezeW.k_pin_at.none] at hm; cases hm
    rw [c0, indexFreezeW.k_pin_at.arm1] at hm
    obtain ⟨hm0, -, -, hr0⟩ := callW_pinAt p hP.pin n _ 1 r0 m0 c0
    subst hm0
    try simp only [pinW_setCtl] at hr0
    rcases c1 : callW p n "pin_at" [2] (s₀.mem.set64 CTL 162 (r0.headD 0)) with _ | ⟨r1, m1⟩
    · rw [c1, indexFreezeW.k_pin_at_2.none] at hm; cases hm
    rw [c1, indexFreezeW.k_pin_at_2.arm1] at hm
    obtain ⟨hm1, -, -, hr1⟩ := callW_pinAt p hP.pin n _ 2 r1 m1 c1
    subst hm1
    try simp only [pinW_setCtl] at hr1
    rcases c2 : callW p n "pin_at" [3] ((s₀.mem.set64 CTL 162 (r0.headD 0)).set64 CTL 163 (r1.headD 0)) with _ | ⟨r2, m2⟩
    · rw [c2, indexFreezeW.k_pin_at_3.none] at hm; cases hm
    rw [c2, indexFreezeW.k_pin_at_3.arm1] at hm
    obtain ⟨hm2, -, -, hr2⟩ := callW_pinAt p hP.pin n _ 3 r2 m2 c2
    subst hm2
    try simp only [pinW_setCtl] at hr2
    rcases c3 : callW p n "pin_at" [5] (((s₀.mem.set64 CTL 162 (r0.headD 0)).set64 CTL 163 (r1.headD 0)).set64 CTL 164 (r2.headD 0)) with _ | ⟨r3, m3⟩
    · rw [c3, indexFreezeW.k_pin_at_4.none] at hm; cases hm
    rw [c3, indexFreezeW.k_pin_at_4.arm1] at hm
    obtain ⟨hm3, -, -, hr3⟩ := callW_pinAt p hP.pin n _ 5 r3 m3 c3
    subst hm3
    try simp only [pinW_setCtl] at hr3
    rcases c4 : callW p n "pin_at" [6] ((((s₀.mem.set64 CTL 162 (r0.headD 0)).set64 CTL 163 (r1.headD 0)).set64 CTL 164 (r2.headD 0)).set64 CTL 165 (r3.headD 0)) with _ | ⟨r4, m4⟩
    · rw [c4, indexFreezeW.k_pin_at_5.none] at hm; cases hm
    rw [c4, indexFreezeW.k_pin_at_5.arm1] at hm
    obtain ⟨hm4, -, -, hr4⟩ := callW_pinAt p hP.pin n _ 6 r4 m4 c4
    subst hm4
    try simp only [pinW_setCtl] at hr4
    rcases c5 : callW p n "pin_at" [7] (((((s₀.mem.set64 CTL 162 (r0.headD 0)).set64 CTL 163 (r1.headD 0)).set64 CTL 164 (r2.headD 0)).set64 CTL 165 (r3.headD 0)).set64 CTL 166 (r4.headD 0)) with _ | ⟨r5, m5⟩
    · rw [c5, indexFreezeW.k_pin_at_6.none] at hm; cases hm
    rw [c5, indexFreezeW.k_pin_at_6.arm1] at hm
    obtain ⟨hm5, -, -, hr5⟩ := callW_pinAt p hP.pin n _ 7 r5 m5 c5
    subst hm5
    try simp only [pinW_setCtl] at hr5
    rcases c6 : callW p n "pin_at" [8] ((((((s₀.mem.set64 CTL 162 (r0.headD 0)).set64 CTL 163 (r1.headD 0)).set64 CTL 164 (r2.headD 0)).set64 CTL 165 (r3.headD 0)).set64 CTL 166 (r4.headD 0)).set64 CTL 167 (r5.headD 0)) with _ | ⟨r6, m6⟩
    · rw [c6, indexFreezeW.k_pin_at_7.none] at hm; cases hm
    rw [c6, indexFreezeW.k_pin_at_7.arm1] at hm
    obtain ⟨hm6, -, -, hr6⟩ := callW_pinAt p hP.pin n _ 8 r6 m6 c6
    subst hm6
    try simp only [pinW_setCtl] at hr6
    rcases c7 : callW p n "pin_at" [9] (((((((s₀.mem.set64 CTL 162 (r0.headD 0)).set64 CTL 163 (r1.headD 0)).set64 CTL 164 (r2.headD 0)).set64 CTL 165 (r3.headD 0)).set64 CTL 166 (r4.headD 0)).set64 CTL 167 (r5.headD 0)).set64 CTL 168 (r6.headD 0)) with _ | ⟨r7, m7⟩
    · rw [c7, indexFreezeW.k_pin_at_8.none] at hm; cases hm
    rw [c7, indexFreezeW.k_pin_at_8.arm1] at hm
    obtain ⟨hm7, -, -, hr7⟩ := callW_pinAt p hP.pin n _ 9 r7 m7 c7
    subst hm7
    try simp only [pinW_setCtl] at hr7
    rcases c8 : callW p n "pin_at" [10] ((((((((s₀.mem.set64 CTL 162 (r0.headD 0)).set64 CTL 163 (r1.headD 0)).set64 CTL 164 (r2.headD 0)).set64 CTL 165 (r3.headD 0)).set64 CTL 166 (r4.headD 0)).set64 CTL 167 (r5.headD 0)).set64 CTL 168 (r6.headD 0)).set64 CTL 169 (r7.headD 0)) with _ | ⟨r8, m8⟩
    · rw [c8, indexFreezeW.k_pin_at_9.none] at hm; cases hm
    rw [c8, indexFreezeW.k_pin_at_9.arm1] at hm
    obtain ⟨hm8, -, -, hr8⟩ := callW_pinAt p hP.pin n _ 10 r8 m8 c8
    subst hm8
    try simp only [pinW_setCtl] at hr8
    rcases c9 : callW p n "pin_at" [12] (((((((((s₀.mem.set64 CTL 162 (r0.headD 0)).set64 CTL 163 (r1.headD 0)).set64 CTL 164 (r2.headD 0)).set64 CTL 165 (r3.headD 0)).set64 CTL 166 (r4.headD 0)).set64 CTL 167 (r5.headD 0)).set64 CTL 168 (r6.headD 0)).set64 CTL 169 (r7.headD 0)).set64 CTL 170 (r8.headD 0)) with _ | ⟨r9, m9⟩
    · rw [c9, indexFreezeW.k_pin_at_10.none] at hm; cases hm
    rw [c9, indexFreezeW.k_pin_at_10.arm1] at hm
    obtain ⟨hm9, -, -, hr9⟩ := callW_pinAt p hP.pin n _ 12 r9 m9 c9
    subst hm9
    try simp only [pinW_setCtl] at hr9
    -- the ten names written
    have hlitW : ∀ (m : Mem) (hm : 173 < (m.arr64 CTL).size),
        (pinLits s₀.mem).map (·.word.toUInt64) = litWords m ↔
          (rdW (m.arr64 CTL) 162 = pinW s₀.mem 2 ∧ rdW (m.arr64 CTL) 163 = pinW s₀.mem 3 ∧
           rdW (m.arr64 CTL) 164 = pinW s₀.mem 4 ∧ rdW (m.arr64 CTL) 165 = pinW s₀.mem 6 ∧
           rdW (m.arr64 CTL) 166 = pinW s₀.mem 7 ∧ rdW (m.arr64 CTL) 167 = pinW s₀.mem 8 ∧
           rdW (m.arr64 CTL) 168 = pinW s₀.mem 9 ∧ rdW (m.arr64 CTL) 169 = pinW s₀.mem 10 ∧
           rdW (m.arr64 CTL) 170 = pinW s₀.mem 11 ∧ rdW (m.arr64 CTL) 171 = pinW s₀.mem 13) := by
      intro m _
      have hw : ∀ i, i < 51 → (decI (pinW s₀.mem (1 + i)) : NIdx).word.toUInt64 = pinW s₀.mem (1 + i) :=
        fun i hi => decI_word_self _ (hF.names_lt i hi)
      simp only [pinLits, List.map_cons, List.map_nil, hw _ (by decide : (1:Nat) < 51),
        hw 2 (by decide), hw 3 (by decide), hw 5 (by decide), hw 6 (by decide), hw 7 (by decide),
        hw 8 (by decide), hw 9 (by decide), hw 10 (by decide), hw 12 (by decide), litWords]
      simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      constructor <;> intro h <;> (obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := h) <;>
        exact ⟨e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm, e7.symm, e8.symm, e9.symm, e10.symm⟩
    obtain ⟨h1, h2, h3⟩ := freeze_tail hP hI hc
      (fun b hb => by simp only [Mem.arr64_set64_ne _ _ _ _ _ hb])
      (fun x hx => by
        simp only [frozenCtl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp only [rdW_set64]; simp [Ne.symm hx.1, Ne.symm hx.2.1, Ne.symm hx.2.2.1, Ne.symm hx.2.2.2.1,
          Ne.symm hx.2.2.2.2.1, Ne.symm hx.2.2.2.2.2.1, Ne.symm hx.2.2.2.2.2.2.1,
          Ne.symm hx.2.2.2.2.2.2.2.1, Ne.symm hx.2.2.2.2.2.2.2.2.1, Ne.symm hx.2.2.2.2.2.2.2.2.2.1])
      (by simp [Mem.size64_set64])
      ((hlitW _ (by simp [Mem.size64_set64]; omega)).mpr (by
        simp only [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9]
        simp [rdW_set64, Mem.size64_set64]
        omega)) hm
    exact ⟨h1, h2, h3⟩

end L.Arena
