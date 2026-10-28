import ConAgua.Verdict.FrontViE
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The apply step of an `inductive` line against the twin, V: the constructors in the block's order

`vi_order_in`/`vi_order_go` (`orderIn_ref`, `orderGo_ref`; `vi_order` in `IndApplyRefine8`):
every constructor of every type, in the block's order, passes `vi_ctor` (`ctor_ref`), its record's
pointer written to the ordered slice at `oo`, or the loop stops at the first that fails
(`CtorFail`). The facts are collected per position (`CtorOK`); `ordList` reads the ordered
constructors back from the slice.
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true


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
    rw [wd_setA, ite_eq_right (by omega)]; exact h.2 j hj⟩

theorem IOnly.ifr {B : Nat} {m m' : Mem} (h : IOnly B m m') : m'.arr64 IFR = m.arr64 IFR :=
  h.1.1 IFR (by decide) (by decide)

theorem IOnly.other {B : Nat} {m m' : Mem} (h : IOnly B m m') (A : ArrId) (h1 : A ≠ IFL) (h2 : A ≠ CTL) :
    m'.arr64 A = m.arr64 A := h.1.1 A (by simp [h1]) (TieredArray.t0_ne h2)

theorem IOnly.arena {B : Nat} {m m' : Mem} {a : AState} (h : IOnly B m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame_ext [IFL] [] (by decide) (by simp) m m' h.1 a hR

theorem IOnly.stateDR {B : Nat} {m m' : Mem} {st : StateD} (h : IOnly B m m') (hD : StateDR m st) :
    StateDR m' st :=
  hD.frame h.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [IFL, idArrs, NID, LID, EID, NIDS, LIDS, EIDS])
    (by simp)

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

/-- The ordered constructors read back from the slice at `oo`: record `(w - co) / 10` for each
pointer `w`. -/
def ordList (m : Mem) (oo co : Nat) (cts : List IndCtorRec) (l : Nat) : List IndCtorRec :=
  (List.range l).map fun p => cts.getD (((wd m IFL (oo + p)).toNat - co) / 10) default

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

/-! ## `vi_order_in`, `vi_order_go`: the unified models -/

l_model viOrderIn_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_order_in ↦ viOrderInE]
  specs [viCtor_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp []
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model viOrderGo_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_order_go ↦ viOrderGoE]
  specs [viOrderIn_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE] simp []
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-! ## `vi_order_in` -/

section order
variable {p : Prog} {b : ByteArray} {m₀ : Mem} {a : AState} {st : StateD} (hR : ArenaR m₀ a)
  (hD : StateDR m₀ st) {cts : List IndCtorRec} {fo cno co cn fuel np oo : Word}
  (hCt : ListF (CtF b m₀) m₀ 10 co.toNat cts) (hcn : cn.toNat = cts.length)
  (hCN : ∀ k, k < cts.length → (wd m₀ IFL (cno.toNat + k)).toNat < 2 ^ 32)
  (hcnB : cno.toNat + cts.length ≤ oo.toNat) (hnp : np.toNat < 10 ^ 18)
  (hco : co.toNat + 10 * cts.length < 2 ^ 63) (hsz : oo.toNat + cts.length ≤ (m₀.arr64 IFL).size)
  (hsz63 : (m₀.arr64 IFL).size < 2 ^ 63)
include hR hD hCt hcn hCN hcnB hnp hco hsz hsz63

/-- **`vi_order_in`'s ok half**: only `IFL` from `oo` on written, the position after the type's
constructors, the words below `oo + pos` kept, and each constructor from `jj` on passes the twin's
checks, its record's pointer at its position of the slice. -/
structure OrderInPost (st : StateD) (a : AState) (cts : List IndCtorRec) (m₀ m : Mem)
    (fo cno co np fuel oo t tt jj pos : Word) (v : Word × Mem) : Prop where
  only : IOnly oo.toNat m₀ v.2
  next : v.1.toNat = pos.toNat + ((wd m₀ IFR (t.toNat + 4)).toNat - jj.toNat)
  keep : ∀ i, i < oo.toNat + pos.toNat → wd v.2 IFL i = wd m IFL i
  ctors : ∀ c, jj.toNat ≤ c → c < (wd m₀ IFR (t.toNat + 4)).toNat →
    ∃ k, wd v.2 IFL (oo.toNat + pos.toNat + (c - jj.toNat)) = co + 10 * UInt64.ofNat k ∧
      CtorOK st a cts (islice m₀ cno.toNat cts.length)
        (decI (wd m₀ IFL (fo.toNat + pos.toNat + (c - jj.toNat)))) c (decI tt) np.toNat fuel.toNat k

/-- **`vi_order_in`'s error half**: an error of class `≠ 0` (with the type's name handle below
`2^32`) stops at a constructor `c` of the type (from `jj` on): the ones before pass the twin's
checks, `c` fails them. -/
def OrderInFail (st : StateD) (a : AState) (cts : List IndCtorRec) (m₀ : Mem)
    (fo cno np fuel t tt jj pos : Word) (e : Err) : Prop :=
  tt.toNat < 2 ^ 32 → e.cls ≠ 0 → e.cls = 1 ∧ ∃ c, jj.toNat ≤ c ∧ c < (wd m₀ IFR (t.toNat + 4)).toNat ∧
    (∀ c', jj.toNat ≤ c' → c' < c → ∃ k,
      CtorOK st a cts (islice m₀ cno.toNat cts.length)
        (decI (wd m₀ IFL (fo.toNat + pos.toNat + (c' - jj.toNat)))) c' (decI tt) np.toNat fuel.toNat k) ∧
    CtorFail st a cts (islice m₀ cno.toNat cts.length)
      (decI (wd m₀ IFL (fo.toNat + pos.toNat + (c - jj.toNat)))) c (decI tt) np.toNat fuel.toNat

/-- **`vi_order_in`, both outcomes.** -/
theorem orderIn_ref : ∀ (n : Nat) (m : Mem) (t tt jj pos : Word),
    IOnly oo.toNat m₀ m → t.toNat + 4 < 2 ^ 63 → jj.toNat ≤ (wd m₀ IFR (t.toNat + 4)).toNat →
    pos.toNat + ((wd m₀ IFR (t.toNat + 4)).toNat - jj.toNat) ≤ cts.length →
    (∀ c, jj.toNat ≤ c → c < (wd m₀ IFR (t.toNat + 4)).toNat →
      fo.toNat + pos.toNat + (c - jj.toNat) < oo.toNat ∧
      (wd m₀ IFL (fo.toNat + pos.toNat + (c - jj.toNat))).toNat < 2 ^ 32) →
    RefC True (viOrderInE p n m fo cno co cn fuel np oo t tt jj pos)
      (OrderInPost st a cts m₀ m fo cno co np fuel oo t tt jj pos)
      (OrderInFail st a cts m₀ fo cno np fuel t tt jj pos) := by
  intro n
  induction n with
  | zero =>
    intro m t tt jj pos _ _ _ _ _
    simp only [viOrderInE, RefC_error]; exact fun _ _ hk => absurd Err.cls_outOfFuel hk
  | succ n ih =>
    intro m t tt jj pos hI ht hjj hpos hfo
    have h4 : rdW (m.arr64 IFR) (t + 4) = wd m₀ IFR (t.toNat + 4) := by
      rw [wd_eq, widx2 _ _ (by simp; omega), hI.wdR]; rfl
    by_cases hle : rdW (m.arr64 IFR) (t + 4) ≤ jj
    · rw [viOrderInE.arm1 p n m _ _ _ _ _ _ _ _ _ _ _ hle]
      rw [h4] at hle
      have := UInt64.le_iff_toNat_le.mp hle
      exact ⟨hI, by dsimp only; omega, fun _ _ => rfl, fun c h1 h2 => by omega⟩
    rw [viOrderInE.arm2 p n m _ _ _ _ _ _ _ _ _ _ _ hle]
    rw [h4] at hle
    have hlt' := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    obtain ⟨hf1, hf2⟩ := hfo jj.toNat (Nat.le_refl _) hlt'
    simp only [Nat.sub_self, Nat.add_zero] at hf1 hf2
    have hfp : (fo + pos).toNat = fo.toNat + pos.toNat := widx2 _ _ (by omega)
    have hop : (oo + pos).toNat = oo.toNat + pos.toNat := widx2 _ _ (by omega)
    have hnn : rdW (m.arr64 IFL) (fo + pos) = wd m₀ IFL (fo.toNat + pos.toNat) := by
      rw [wd_eq, hfp, hI.2 _ hf1]
    rw [hnn]
    have hCN' : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32 := fun k hk => by
      rw [hI.2 _ (by omega)]; exact hCN k hk
    have hc := ctor_ref (hI.arena hR) (hI.stateDR hD) (hI.listF hCt) hcn hCN' (by omega) hf2 hnp hco p n
      (j := jj) (tt := tt) (fuel := fuel)
    rcases h1 : viCtorE p n m (wd m₀ IFL (fo.toNat + pos.toNat)) jj tt np fuel cno cn co with e1 | ⟨r, mc⟩ <;>
      rw [h1] at hc
    · rw [viOrderInE.k_vi_ctor.none]
      intro _ htt hk
      obtain ⟨hc1, hfail⟩ := hc trivial htt hk
      rw [hI.islice _ _ hcnB] at hfail
      exact ⟨hc1, jj.toNat, Nat.le_refl _, hlt', fun c' h1 h2 => by omega, by simpa using hfail⟩
    rw [viOrderInE.k_vi_ctor.arm1]
    obtain ⟨hmc, k, hck, hk, hfold, hcidx, hind, htele⟩ := hc
    dsimp only at hmc hck
    rw [hmc]
    rw [hI.islice _ _ hcnB] at hfold
    have hj1 := wsucc jj _ (UInt64.not_le.mp hle)
    have hp1 : (pos + 1).toNat = pos.toNat + 1 := widx2 _ _ (by simp; omega)
    have ih1 := ih (m.set64 IFL (oo + pos) r) t tt (jj + 1) (pos + 1)
      (hI.set _ _ (by rw [hop]; omega)) ht (by rw [hj1]; omega) (by rw [hj1, hp1]; omega)
      (fun c' h1 h2 => by
        rw [hj1] at h1; rw [hp1, hj1]
        have := hfo c' (by omega) h2
        rw [show fo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c' - jj.toNat) by omega]
        exact this)
    rcases h2 : viOrderInE p n (m.set64 IFL (oo + pos) r) fo cno co cn fuel np oo t tt (jj + 1) (pos + 1)
      with e2 | ⟨pos', m'⟩ <;> rw [h2] at ih1
    · intro _ htt hk0
      obtain ⟨hcl, c, y1, y2, y3, y4⟩ := ih1 trivial htt hk0
      simp only [hj1, hp1] at y1 y3 y4
      refine ⟨hcl, c, by omega, y2, fun c' h1 h2 => ?_, ?_⟩
      · by_cases hcj : c' = jj.toNat
        · subst hcj
          simp only [Nat.sub_self, Nat.add_zero]
          exact ⟨k, hk, hfold, hcidx, hind, htele⟩
        · obtain ⟨k', e2⟩ := y3 c' (by omega) h2
          rw [show fo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c' - jj.toNat) by omega] at e2
          exact ⟨k', e2⟩
      · rw [show fo.toNat + (pos.toNat + 1) + (c - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c - jj.toNat) by omega] at y4
        exact y4
    obtain ⟨y1, y2, y3, y4⟩ := ih1
    dsimp only at y1 y2 y3 y4 ⊢
    rw [hj1, hp1] at y2 y4
    rw [hp1] at y3
    have hwc : wd m' IFL (oo.toNat + pos.toNat) = r := by
      rw [y3 _ (by omega), wd_setA, ite_eq_left ⟨rfl, hop, by
             have := hI.1.size IFL; rw [this]; omega⟩]
    refine ⟨y1, by dsimp only; omega, fun i hi => by rw [y3 _ (by omega), wd_setA, ite_eq_right (by omega)], fun c' h1 h2 => ?_⟩
    by_cases hcj : c' = jj.toNat
    · subst hcj
      simp only [Nat.sub_self, Nat.add_zero]
      exact ⟨k, by rw [hwc, hck], hk, hfold, hcidx, hind, htele⟩
    · obtain ⟨k', e1, e2⟩ := y4 c' (by omega) h2
      rw [show oo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = oo.toNat + pos.toNat + (c' - jj.toNat) by omega] at e1
      rw [show fo.toNat + (pos.toNat + 1) + (c' - (jj.toNat + 1)) = fo.toNat + pos.toNat + (c' - jj.toNat) by omega] at e2
      exact ⟨k', e1, e2⟩

end order

/-! ## `vi_order_go` -/

/-- The constructor count of type record `k` (at `to + 11 k`). -/
def cntF (m : Mem) (to : Word) (k : Nat) : Nat := (wd m IFR (to.toNat + 11 * k + 4)).toNat

/-- The position of type `i`'s first constructor in the block's order. -/
def psum (m : Mem) (to : Word) (i : Nat) : Nat := ((List.range i).map (cntF m to)).sum

theorem psum_succ (m : Mem) (to : Word) (i : Nat) : psum m to (i + 1) = psum m to i + cntF m to i := by
  simp [psum, List.range_succ]

theorem psum_mono (m : Mem) (to : Word) (i j : Nat) (h : i ≤ j) : psum m to i ≤ psum m to j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rw [psum_succ]
    by_cases hij : i = j + 1
    · subst hij; rw [psum_succ]; exact Nat.le_refl _
    · have := ih (by omega); omega

section orderGo
variable {p : Prog} {b : ByteArray} {m₀ : Mem} {a : AState} {st : StateD} (hR : ArenaR m₀ a)
  (hD : StateDR m₀ st) {cts : List IndCtorRec} {to tn tyn fo cno co cn fuel np oo : Word}
  (hCt : ListF (CtF b m₀) m₀ 10 co.toNat cts) (hcn : cn.toNat = cts.length)
  (hCN : ∀ k, k < cts.length → (wd m₀ IFL (cno.toNat + k)).toNat < 2 ^ 32)
  (hcnB : cno.toNat + cts.length ≤ oo.toNat) (hnp : np.toNat < 10 ^ 18)
  (hco : co.toNat + 10 * cts.length < 2 ^ 63) (hsz : oo.toNat + cts.length ≤ (m₀.arr64 IFL).size)
  (hsz63 : (m₀.arr64 IFL).size < 2 ^ 63)
  (hto : to.toNat + 11 * tn.toNat < 2 ^ 63) (htyn : tyn.toNat + tn.toNat ≤ oo.toNat)
  (hfo : ∀ p, p < psum m₀ to tn.toNat → fo.toNat + p < oo.toNat ∧ (wd m₀ IFL (fo.toNat + p)).toNat < 2 ^ 32)
  (hps : psum m₀ to tn.toNat ≤ cts.length)
include hR hD hCt hcn hCN hcnB hnp hco hsz hsz63 hto htyn hfo hps

/-- **`vi_order_go`'s ok half**: only `IFL` from `oo` on written, the words below `oo + pos` kept,
and every constructor of every type from `ti` on passes the twin's checks, its record's pointer at
its position of the slice. -/
structure OrderGoPost (st : StateD) (a : AState) (cts : List IndCtorRec) (m₀ m : Mem)
    (to tn tyn fo cno co np fuel oo ti pos : Word) (v : Word × Mem) : Prop where
  only : IOnly oo.toNat m₀ v.2
  keep : ∀ i, i < oo.toNat + pos.toNat → wd v.2 IFL i = wd m IFL i
  ctors : ∀ k, ti.toNat ≤ k → k < tn.toNat → ∀ c, c < cntF m₀ to k →
    ∃ kk, wd v.2 IFL (oo.toNat + psum m₀ to k + c) = co + 10 * UInt64.ofNat kk ∧
      CtorOK st a cts (islice m₀ cno.toNat cts.length) (decI (wd m₀ IFL (fo.toNat + psum m₀ to k + c)))
        c (decI (wd m₀ IFL (tyn.toNat + k))) np.toNat fuel.toNat kk

/-- **`vi_order_go`'s error half**: an error of class `≠ 0` (with the type name handles below
`2^32`) stops at constructor `c` of type `k` (from `ti` on): every constructor before passes the
twin's checks, `c` fails them. -/
def OrderGoFail (st : StateD) (a : AState) (cts : List IndCtorRec) (m₀ : Mem)
    (to tn tyn fo cno np fuel ti : Word) (e : Err) : Prop :=
  (∀ k, k < tn.toNat → (wd m₀ IFL (tyn.toNat + k)).toNat < 2 ^ 32) → e.cls ≠ 0 →
    e.cls = 1 ∧ ∃ k, ti.toNat ≤ k ∧ k < tn.toNat ∧ ∃ c, c < cntF m₀ to k ∧
      (∀ k', ti.toNat ≤ k' → k' < k → ∀ c', c' < cntF m₀ to k' → ∃ kk,
        CtorOK st a cts (islice m₀ cno.toNat cts.length) (decI (wd m₀ IFL (fo.toNat + psum m₀ to k' + c')))
          c' (decI (wd m₀ IFL (tyn.toNat + k'))) np.toNat fuel.toNat kk) ∧
      (∀ c', c' < c → ∃ kk,
        CtorOK st a cts (islice m₀ cno.toNat cts.length) (decI (wd m₀ IFL (fo.toNat + psum m₀ to k + c')))
          c' (decI (wd m₀ IFL (tyn.toNat + k))) np.toNat fuel.toNat kk) ∧
      CtorFail st a cts (islice m₀ cno.toNat cts.length) (decI (wd m₀ IFL (fo.toNat + psum m₀ to k + c)))
        c (decI (wd m₀ IFL (tyn.toNat + k))) np.toNat fuel.toNat

/-- **`vi_order_go`, both outcomes.** -/
theorem orderGo_ref : ∀ (n : Nat) (m : Mem) (ti pos : Word),
    IOnly oo.toNat m₀ m → ti ≤ tn → pos.toNat = psum m₀ to ti.toNat →
    RefC True (viOrderGoE p n m to tn tyn fo cno co cn fuel np oo ti pos)
      (OrderGoPost st a cts m₀ m to tn tyn fo cno co np fuel oo ti pos)
      (OrderGoFail st a cts m₀ to tn tyn fo cno np fuel ti) := by
  intro n
  induction n with
  | zero =>
    intro m ti pos _ _ _
    simp only [viOrderGoE, RefC_error]; exact fun _ _ hk => absurd Err.cls_outOfFuel hk
  | succ n ih =>
    intro m ti pos hI hti hpos
    by_cases hle : tn ≤ ti
    · rw [viOrderGoE.arm1 p n m _ _ _ _ _ _ _ _ _ _ _ _ hle]
      have := UInt64.le_iff_toNat_le.mp hle
      have := UInt64.le_iff_toNat_le.mp hti
      exact ⟨hI, fun _ _ => rfl, fun k h1 h2 => by omega⟩
    rw [viOrderGoE.arm2 p n m _ _ _ _ _ _ _ _ _ _ _ _ hle]
    have hlt' := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hti1 := wsucc ti tn (UInt64.not_le.mp hle)
    have htt' : rdW (m.arr64 IFL) (tyn + ti) = wd m₀ IFL (tyn.toNat + ti.toNat) := by
      rw [wd_eq, widx2 _ _ (by omega), hI.2 _ (by omega)]
    rw [htt']
    have hmono := psum_mono m₀ to (ti.toNat + 1) tn.toNat (by omega)
    rw [psum_succ] at hmono
    have ht : (to + 11 * ti).toNat = to.toNat + 11 * ti.toNat := by
      have := widx to 11 ti 0 (by simp; omega); simpa using this
    have hc4 : wd m₀ IFR ((to + 11 * ti).toNat + 4) = wd m₀ IFR (to.toNat + 11 * ti.toNat + 4) := by rw [ht]
    have hin := orderIn_ref (p := p) (fuel := fuel) hR hD hCt hcn hCN hcnB hnp hco hsz hsz63 n m (to + 11 * ti)
      (wd m₀ IFL (tyn.toNat + ti.toNat)) 0 pos hI (by rw [ht]; omega) (by simp)
      (by simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero]; rw [hc4]; unfold cntF at hmono; omega)
      (fun c h1 h2 => by
        simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at h2 ⊢
        rw [hc4] at h2
        have := hfo (pos.toNat + c) (by rw [hpos]; unfold cntF at hmono; omega)
        rw [Nat.add_assoc]; exact this)
    rcases h1 : viOrderInE p n m fo cno co cn fuel np oo (to + 11 * ti) (wd m₀ IFL (tyn.toNat + ti.toNat)) 0 pos
      with e1 | ⟨q, m₁⟩ <;> rw [h1] at hin
    · rw [viOrderGoE.k_vi_order_in.none]
      intro _ htt hk
      obtain ⟨hcl, c, -, c2, c3, c4⟩ := hin trivial (htt _ hlt') hk
      simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at c2 c3 c4
      rw [hc4] at c2
      refine ⟨hcl, ti.toNat, Nat.le_refl _, hlt', c, c2, fun k' h1 h2 => by omega, fun c' hc' => ?_, ?_⟩
      · obtain ⟨kk, hkk⟩ := c3 c' (Nat.zero_le _) hc'
        rw [← hpos]; exact ⟨kk, hkk⟩
      · rw [← hpos]; exact c4
    rw [viOrderGoE.k_vi_order_in.arm1]
    obtain ⟨x1, x2, x3, x4⟩ := hin
    dsimp only at x1 x2 x3 x4
    simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at x2
    rw [hc4] at x2
    have ih1 := ih m₁ (ti + 1) q x1 (UInt64.le_iff_toNat_le.mpr (by rw [hti1]; exact hlt'))
      (by rw [hti1, psum_succ, x2, hpos]; rfl)
    rcases h2 : viOrderGoE p n m₁ to tn tyn fo cno co cn fuel np oo (ti + 1) q with e2 | ⟨u, m₂⟩ <;>
      rw [h2] at ih1
    · rw [viOrderGoE.k_vi_order_go.none]
      intro _ htt hk
      obtain ⟨hcl, k, y1, y2, c, y3, y4, y5, y6⟩ := ih1 trivial htt hk
      rw [hti1] at y1 y4
      refine ⟨hcl, k, by omega, y2, c, y3, fun k' h1 h2 c' hc' => ?_, y5, y6⟩
      by_cases hk' : k' = ti.toNat
      · subst hk'
        obtain ⟨kk, e2⟩ := x4 c' (Nat.zero_le _) (by rw [hc4]; exact hc')
        simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at e2
        rw [← hpos]; exact ⟨kk, e2.2⟩
      · exact y4 k' (by omega) h2 c' hc'
    rw [viOrderGoE.k_vi_order_go.arm1]
    obtain ⟨y1, y2, y3⟩ := ih1
    dsimp only at y1 y2 y3 ⊢
    rw [hti1] at y3
    refine ⟨y1, fun i hi => by rw [y2 _ (by rw [x2]; omega), x3 _ hi], fun k h1 h2 c hc => ?_⟩
    by_cases hk : k = ti.toNat
    · subst hk
      obtain ⟨kk, e1, e2⟩ := x4 c (Nat.zero_le _) (by rw [hc4]; exact hc)
      simp only [show (0 : Word).toNat = 0 from rfl, Nat.sub_zero] at e1 e2
      refine ⟨kk, ?_, by rw [← hpos]; exact e2⟩
      rw [y2 _ (by rw [x2]; unfold cntF at hc; omega), ← hpos]; exact e1
    · exact y3 k (by omega) h2 c hc

end orderGo

end L.Front.Ind
