module

import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.RecGenSpec.Rec3CVX
import ConAgua.Arena.RecGenSpec.RgW
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.LdRd
import ConRon.Bridge.Grind
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.RecGenSpec.DecCVX
public import ConAgua.Arena.RecSim
public import ConAgua.Arena.RecStab
import all ConAgua.Arena.RecGen
import ConAgua.L.WordOff

@[expose] public section

/-!
# ClassFeR: `ConRon.Arena.classFeR`

The refinement theorems `classFeR_refines` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A constant record below the top decodes in the record pool in use. -/
theorem rec2DecCV_erecP {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv) (_hq : CVExt m q) :
    decCV (erecP m) q = some cv := h

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem rec3SPL_uncons {m : Mem} {o l : Nat} {cvs : List IConstantVal} (h : SPL decCVX m o (l + 1) cvs) :
    ∃ p cv cvs', cvs = cv :: cvs' ∧ iwN m o = some p ∧ o < iwTop m ∧
      StabD (fun m => decCVX m p) m cv ∧ SPL decCVX m (o + 1) l cvs' := by
  obtain ⟨hb, ps, hps, hf⟩ := h
  rw [decNL_succ] at hps
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hps
  obtain ⟨p, hp, ps', hps', rfl⟩ := hps
  cases hf with
  | cons h1 h2 => exact ⟨p, _, _, rfl, hp, by omega, h1, by omega, ps', hps', h2⟩

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `class_fe_r_rec` -/

/-- The memory after `class_fe_r_rec`'s ten `erec_put`s (each copy reads the memory of its time). -/
def cfrMem (m1 : Mem) (q cv mi rp3 : Word) : Mem :=
  let m2 := erecPutMem m1 q 5
  let m3 := erecPutMem m2 (q + 1) (erRd m2 cv)
  let m4 := erecPutMem m3 (q + 2) (erRd m3 (cv + 1))
  let m5 := erecPutMem m4 (q + 3) (erRd m4 (cv + 2))
  let m6 := erecPutMem m5 (q + 4) (erRd m5 (cv + 3))
  erecPutMem (erecPutMem (erecPutMem (erecPutMem (erecPutMem m6 (q + 5) mi) (q + 6) rp3) (q + 7) 0)
    (q + 8) 0) (q + 9) 0

/-- **`class_fe_r_rec(cv, mi, rp3)`'s model `cfrRecW`** (generated). -/
l_model cfrRec_specW (p : Prog) (ha : p.lookup "erec_alloc" = some erecAlloc)
    (hpu : p.lookup "erec_put" = some erecPut)
    (hp : p.lookup "class_fe_r_rec" = some classFeRRec)
  fns [hp ↦ cfrRecW]
  specs [erecAlloc_specW p ha n, erecPut_specW p hpu n]
  grind [arena_grind] extra [ld64_rd_spec] simp []

/-! ## `class_fe_r_go`: the word model -/

/-- The recursor record's major index and rule prefix (`0`, `0` off the list). -/
def ferMi (m : Mem) (ro rl M : Word) : Word :=
  if M < rl then rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 2) else 0
def ferRp (m : Mem) (ro rl M : Word) : Word :=
  if M < rl then rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 1) else 0

section arms
variable (m : Mem) (ro rl M : Word)
theorem ferMi_hit (h : M < rl) : ferMi m ro rl M = rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 2) := by
  simp [ferMi, h]
theorem ferMi_miss (h : ¬ M < rl) : ferMi m ro rl M = 0 := by simp [ferMi, h]
theorem ferRp_hit (h : M < rl) : ferRp m ro rl M = rdW (m.arr64 IW) (rdW (m.arr64 IW) (ro + M) + 1) := by
  simp [ferRp, h]
theorem ferRp_miss (h : ¬ M < rl) : ferRp m ro rl M = 0 := by simp [ferRp, h]
end arms

/-- The lookups of `class_fe_r`. -/
structure CfrProg (p : Prog) : Prop where
  rp : RecProg p
  rg : p.lookup "env_row_get" = some envRowGetL
  ia : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  rec3 : p.lookup "rec3" = some rec3
  frec : p.lookup "class_fe_r_rec" = some classFeRRec
  go : p.lookup "class_fe_r_go" = some classFeRGo
  top : p.lookup "class_fe_r" = some classFeRL

/-- **`class_fe_r_go`'s model `ferW`** (generated). -/
l_model classFeRGo_spec (p : Prog) (h : CfrProg p)
  fns [h.go ↦ ferW list]
  specs [envRowGet_spec p h.rg n, cfrRec_specW p h.rp.alloc h.rp.put h.frec n, callW_spec p n "env_push",
    rec3_specW p h.ia n h.rec3, slCons_specW p h.ia h.copy h.cons n]
  grind [arena_grind] finish [rdW_eq]

l_model classFeR_spec (p : Prog) (h : CfrProg p)
  fns [h.top ↦ ferAW]
  specs [classFeRGo_spec p h n]
  grind [arena_grind]

/-! ## `class_fe_r_rec` under the stage relation -/

theorem cfrMem_eq {m1 : Mem} {q cq mi rp3 : Word}
    (hfr : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], ∀ j < 10,
      erTier x ≠ erTier (q + UInt64.ofNat j) ∨ erOff x ≠ erOff (q + UInt64.ofNat j)) :
    cfrMem m1 q cq mi rp3 = wrER m1 q [5, erRd m1 cq, erRd m1 (cq + 1), erRd m1 (cq + 2),
      erRd m1 (cq + 3), mi, rp3, 0, 0, 0] := by
  have f0 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier q ∨ erOff x ≠ erOff q :=
    fun x hx => by simpa using hfr x hx 0 (by decide)
  have f1 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 1) ∨ erOff x ≠ erOff (q + 1) :=
    fun x hx => hfr x hx 1 (by decide)
  have f2 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 2) ∨ erOff x ≠ erOff (q + 2) :=
    fun x hx => hfr x hx 2 (by decide)
  have f3 : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], erTier x ≠ erTier (q + 3) ∨ erOff x ≠ erOff (q + 3) :=
    fun x hx => hfr x hx 3 (by decide)
  simp only [cfrMem, wrER]
  rw [show q + 1 + 1 = q + 2 by ac_rfl, show q + 2 + 1 = q + 3 by ac_rfl,
    show q + 3 + 1 = q + 4 by ac_rfl, show q + 4 + 1 = q + 5 by ac_rfl,
    show q + 5 + 1 = q + 6 by ac_rfl, show q + 6 + 1 = q + 7 by ac_rfl,
    show q + 7 + 1 = q + 8 by ac_rfl, show q + 8 + 1 = q + 9 by ac_rfl]
  simp (disch := first
    | exact f0 _ (by simp) | exact f1 _ (by simp) | exact f2 _ (by simp) | exact f3 _ (by simp))
    only [erRd_erecPutMem_ne]

/-- A run of `class_fe_r_rec`'s model: the allocation, then the ten writes (`cfrMem`). -/
theorem cfrRecW_some {m m' : Mem} {cq mi rp3 q : Word} (h : cfrRecW m cq mi rp3 = some (q, m')) :
    ∃ q1 m1, erAllocW m 10 = some (q1, m1) ∧ q1 = q ∧ m' = cfrMem m1 q1 cq mi rp3 := by
  rw [cfrRecW.arm1] at h
  rcases h1 : erAllocW m 10 with _ | ⟨q1, m1⟩
  · rw [h1, cfrRecW.k_erec_alloc.none] at h; cases h
  rw [h1, cfrRecW.k_erec_alloc.eq_2] at h
  iterate 11 (obtain ⟨-, h⟩ := of_ite_none h)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨_, _, rfl, rfl, rfl⟩

/-- **`class_fe_r_rec` under the stage relation**: a fresh rule-less `.recInfo` record (K flag
`false`) of the constant at `cq`. -/
theorem cfrRec_stage {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {cq mi rp3 q : Word} {cv : IConstantVal} (h : cfrRecW m cq mi rp3 = some (q, m'))
    (hS : StageR vis fe m a) (hcv : decCV (erecP m) cq.toNat = some cv) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      decCI (erecP m') q.toNat = some (.recInfo cv mi.toNat rp3.toNat false []) := by
  obtain ⟨q1, m1, h1, rfl, rfl⟩ := cfrRecW_some h
  have hcv0 := hcv
  simp only [decCV, hlist?, bind, Option.bind_eq_some_iff, pure] at hcv0
  obtain ⟨nm, hnm, lps, ⟨lo, hlo, ll, hll, -⟩, t, ht, -⟩ := hcv0
  obtain ⟨w0, hw0, -, -⟩ := hd?_some hnm
  obtain ⟨w1, hw1, -⟩ : ∃ w, erecP m (cq.toNat + 1) = some w ∧ w.toNat = lo := by
    simp only [nat?, Option.map_eq_some_iff] at hlo; exact hlo
  obtain ⟨w2, hw2, -⟩ : ∃ w, erecP m (cq.toNat + 2) = some w ∧ w.toNat = ll := by
    simp only [nat?, Option.map_eq_some_iff, Nat.add_assoc] at hll; exact hll
  obtain ⟨w3, hw3, -, -⟩ := hd?_some ht
  have hW : ∀ i < 4, ∃ w, erecP m (cq.toNat + i) = some w := by
    intro i hi
    rcases i with _ | _ | _ | _ | i
    · exact ⟨w0, by simpa using hw0⟩
    · exact ⟨w1, hw1⟩
    · exact ⟨w2, hw2⟩
    · exact ⟨w3, hw3⟩
    · omega
  have r0 : erRd m cq = w0 := (erRd_of_erecP (by simpa using hw0)).1
  obtain ⟨r1, e1⟩ := erRd_add (j := 1) (cq := cq) (m := m) hw1 (by decide)
  obtain ⟨r2, e2⟩ := erRd_add (j := 2) (cq := cq) (m := m) hw2 (by decide)
  obtain ⟨r3, e3⟩ := erRd_add (j := 3) (cq := cq) (m := m) hw3 (by decide)
  simp only [show (UInt64.ofNat 1 : Word) = 1 from rfl, show (UInt64.ofNat 2 : Word) = 2 from rfl,
    show (UInt64.ofNat 3 : Word) = 3 from rfl] at r1 r2 r3 e1 e2 e3
  have hfr : ∀ x ∈ [cq, cq + 1, cq + 2, cq + 3], ∀ j < 10,
      erTier x ≠ erTier (q1 + UInt64.ofNat j) ∨ erOff x ≠ erOff (q1 + UInt64.ofNat j) := by
    intro x hx j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact erFresh h1 hS.iw (by simpa using hw0) hj
    · exact erFresh h1 hS.iw (by rw [e1]; exact hw1) hj
    · exact erFresh h1 hS.iw (by rw [e2]; exact hw2) hj
    · exact erFresh h1 hS.iw (by rw [e3]; exact hw3) hj
  obtain ⟨-, hf1, -⟩ := erAllocW_spec h1 hS.iw
  have hr1 : ∀ x, erRd m1 x = erRd m x := fun x => by
    unfold erRd; rw [hf1.arr _ (by simp) (by rw [tierA_EREC]; split <;> decide)]
  rw [cfrMem_eq hfr, hr1, hr1, hr1, hr1, r0, r1, r2, r3]
  obtain ⟨hS', hg, -, -, -, -, hget⟩ :=
    erRec_stage h1 hS [5, w0, w1, w2, w3, mi, rp3, 0, 0, 0] (by simp)
  refine ⟨hS', hg, ?_⟩
  generalize wrER m1 q1 _ = M at hS' hg hget
  have hw : ∀ i, i < 4 → erecP M (q1.toNat + 1 + i) = erecP M (cq.toNat + i) := by
    intro i hi
    obtain ⟨w, hw⟩ := hW i hi
    rw [IWGrow.ext hg _ _ hw, Nat.add_assoc, hget (1 + i) (by simp; omega)]
    rcases i with _ | _ | _ | _ | i
    · simp at hw ⊢; rw [hw0] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw1] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw2] at hw; exact Option.some.inj hw
    · simp at hw ⊢; rw [hw3] at hw; exact Option.some.inj hw
    · omega
  have hcv' : decCV (erecP M) (q1.toNat + CI.cv.toNat) = some cv := by
    rw [decCV_shift (by simpa using hw 0 (by decide)) (by simpa using hw 1 (by decide))
      (by simpa [Nat.add_assoc] using hw 2 (by decide)) (by simpa [Nat.add_assoc] using hw 3 (by decide))]
    exact ArrExt.decCV (IWGrow.ext hg) hcv
  have n0 : nat? (erecP M) q1.toNat = some 5 := by
    have := hget 0 (by simp); simp only [Nat.add_zero] at this; simp [nat?, this]
  have n5 : nat? (erecP M) (q1.toNat + 5) = some mi.toNat := by simp [nat?, hget 5 (by simp)]
  have n6 : nat? (erecP M) (q1.toNat + 6) = some rp3.toNat := by simp [nat?, hget 6 (by simp)]
  have n7 : nat? (erecP M) (q1.toNat + 7) = some 0 := by simp [nat?, hget 7 (by simp)]
  have n8 : nat? (erecP M) (q1.toNat + 8) = some 0 := by simp [nat?, hget 8 (by simp)]
  have b9 : bool? (erecP M) (q1.toNat + 9) = some false := by simp [bool?, hget 9 (by simp)]
  simp only [decCI, Option.bind_eq_bind, n0, Option.bind_some, hcv', n5, n6, n7, n8, b9, Option.pure_def]
  simp [decRules]

/-! ## The twin's accumulator, the displaced rows -/

theorem rec3FerGo_acc (P : BlockShape) : ∀ (L : List (IConstantVal × Nat)) (k : Nat) (fe : IFEnv)
    (prevs : List (NIdx × Option IConstantInfo)),
    ConRon.Arena.classFeR.go P k L fe prevs =
      ((ConRon.Arena.classFeR.go P k L fe []).1, prevs ++ (ConRon.Arena.classFeR.go P k L fe []).2)
  | [], k, fe, prevs => by rw [ConRon.Arena.classFeR.go.eq_1, ConRon.Arena.classFeR.go.eq_1]; simp
  | (cv, c) :: rest, k, fe, prevs => by
    rw [ConRon.Arena.classFeR.go.eq_2, ConRon.Arena.classFeR.go.eq_2]
    rw [rec3FerGo_acc P rest _ _ (prevs ++ _), rec3FerGo_acc P rest _ _ ([] ++ _)]
    simp

/-- A displaced own row `(c, q)` as `env_pop_temp` takes it back: none for `c = 0`, else the
decoded record. -/
def prevD (m : Mem) (c q : Word) : Option (Option IConstantInfo) :=
  if c = 0 then some none else (decCI (erecP m) q.toNat).map some

/-- The own row of a name handle is the twin's `idx` entry. -/
theorem rec3PrevD {m : Mem} {vis : Word} {fe : IFEnv} (h : EnvR m vis fe) {w : Word}
    (hw : w.toNat < 2 ^ 32) :
    prevD m (ownRaw m w).1 (ownRaw m w).2 = some (fe.idx[(decI w : NIdx)]?) := by
  have hn : (decI w : NIdx).word.toUInt64 = w := decI_word_self w hw
  have ho := h.own (decI w)
  have hf := h.fresh (decI w)
  have hd := h.own_dec (decI w)
  rw [hn] at ho hf hd
  rw [ho]
  unfold prevD ownFind
  by_cases h0 : (ownRaw m w).1 = 0
  · simp [h0]
  · obtain ⟨ci, hci⟩ := hd h0
    simp [h0, hf h0, hci]

theorem rec3PrevD_grow {m m' : Mem} (hg : IWGrow m m') {c q : Word}
    {x : Option IConstantInfo} (h : prevD m c q = some x) : prevD m' c q = some x := by
  unfold prevD at h ⊢
  split
  · rename_i h0; rw [ite_eq_left h0] at h; exact h
  · rename_i h0; rw [ite_eq_right h0] at h
    obtain ⟨ci, hci, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [ArrExt.decCI (IWGrow.ext hg) hci]; rfl

/-- A displaced row `[name, c, q]` (a `rec3` record). -/
def decPrev (m : Mem) (p : Nat) : Option (NIdx × Option IConstantInfo) := do
  let nm ← (iwH m p : Option NIdx)
  let c ← iwA m (p + 1)
  let q ← iwA m (p + 2)
  let pv ← prevD m c q
  pure (nm, pv)

theorem rec3DecPrev_stab {m : Mem} {p : Nat}
    {x : NIdx × Option IConstantInfo} (h : decPrev m p = some x) (hp : p + 3 ≤ iwTop m) :
    StabD (fun m => decPrev m p) m x := by
  intro m' hg
  have e : ∀ i, i < iwTop m → (iwA m') i = (iwA m) i := fun i hi => by
    simp only [iwA, aread_apply]; exact hg.iwGet i hi
  simp only [decPrev, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
  obtain ⟨nm, hnm, c, hc, q, hq, pv, hpv, rfl⟩ := h
  refine ⟨nm, ?_, c, by rw [e _ (by omega)]; exact hc, q, by rw [e _ (by omega)]; exact hq, pv,
    rec3PrevD_grow hg hpv, rfl⟩
  simp only [iwH, hd?] at hnm ⊢; rw [e _ (by omega)]; exact hnm

/-! ## The temporary pushes' stack (what `gen_rec_check_pop_all` needs) -/

/-- The own row counter of a name (its push's view plus nothing: `0` when it has no own row). -/
def ownC (m : Mem) (n : NIdx) : Word := (ownRaw m n.word.toUInt64).1

/-- `O` with name `n` set to `c`. -/
def updC (O : NIdx → Word) (n : NIdx) (c : Word) : NIdx → Word := fun x => if x = n then c else O x

theorem updC_idem (O : NIdx → Word) (n : NIdx) (c d : Word) : updC (updC O n c) n d = updC O n d := by
  funext x; simp only [updC]; split <;> rfl

theorem updC_self {O : NIdx → Word} {n : NIdx} {c : Word} (h : O n = c) : updC O n c = O := by
  funext x; simp only [updC]; split
  · rename_i e; subst e; exact h.symm
  · rfl

/-- **The temporary pushes as a stack**, newest first: each entry the pushed name and the counter
its push displaced. The name's row is the newest (its counter the view), the displaced counter is
a 32-bit word older than the view and no other name's, and putting it back leaves the rest a
stack at the view below (what `env_pop_temp` needs at each pop). -/
def PopOK : (NIdx → Word) → Word → List (NIdx × Word) → Prop
  | _, _, [] => True
  | O, vis, (n, c) :: rest => O n = vis ∧ vis ≠ 0 ∧ c.toNat < 2 ^ 32 ∧
      (c ≠ 0 → c.toNat - 1 < vis.toNat - 1) ∧ (c ≠ 0 → ∀ n', n' ≠ n → O n' ≠ c) ∧
      PopOK (updC O n c) (vis - 1) rest

/-- A displaced row's name and counter (the first two words of `decPrev`'s `rec3`). -/
def decPrevC (m : Mem) (p : Nat) : Option (NIdx × Word) := do
  let nm ← (iwH m p : Option NIdx)
  let c ← iwA m (p + 1)
  pure (nm, c)

theorem rec3DecPrevC_stab {m : Mem} {p : Nat} {x : NIdx × Word} (h : decPrevC m p = some x)
    (hp : p + 3 ≤ iwTop m) : StabD (fun m => decPrevC m p) m x := by
  intro m' hg
  have e : ∀ i, i < iwTop m → (iwA m') i = (iwA m) i := fun i hi => by
    simp only [iwA, aread_apply]; exact hg.iwGet i hi
  simp only [decPrevC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
  obtain ⟨nm, hnm, c, hc, rfl⟩ := h
  refine ⟨nm, ?_, c, by rw [e _ (by omega)]; exact hc, rfl⟩
  simp only [iwH, hd?] at hnm ⊢; rw [e _ (by omega)]; exact hnm

theorem ownRaw_fst_lt (m : Mem) (w : Word) : (ownRaw m w).1.toNat < 2 ^ 32 := by
  unfold ownRaw; split
  · rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp

theorem oix_ne (g : Nat) (t : UInt64) : tierA (oixArr g) t ≠ CTL ∧ tierA (oixArr g) t ≠ IW ∧
    tierA (oixArr g) t ≠ EREC ∧ tierA (oixArr g) t ≠ tier1 EREC := by
  unfold tierA oixArr; generalize (t &&& 1 != 0) = b
  cases b <;> split <;> (try split) <;> decide

/-- `ownC` reads only the own row arrays and the stamp. -/
theorem ownC_frame {A : List TieredArray} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, ∀ g t, b ≠ tierA (oixArr g) t) (hC : (133 : Word) ∉ C) : ownC m' = ownC m := by
  have e1 : ∀ g t, m'.arr64 (tierA (oixArr g) t) = m.arr64 (tierA (oixArr g) t) := fun g t =>
    hf.arr _ (fun h => hA _ h g t rfl) (oix_ne g t).1
  have e2 : stampW m' = stampW m := hf.ctl 133 hC
  have e3 : ∀ w, ownRow m' w = ownRow m w := fun w => by simp only [ownRow, e1]
  funext n
  simp only [ownC, ownRaw, e2, e3]

theorem ownC_iw {m m' : Mem} (hf : MemFrame [IW] [200] m m') : ownC m' = ownC m :=
  ownC_frame hf (by simp only [List.mem_singleton]; rintro b rfl g t; exact (oix_ne g t).2.1.symm)
    (by decide)

theorem ownC_erecPutMem (m : Mem) (a v : Word) : ownC (erecPutMem m a v) = ownC m :=
  ownC_frame (erecPutMem_frame m a v) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl) g t
    · exact (oix_ne g t).2.2.1.symm
    · exact (oix_ne g t).2.2.2.symm) (by simp)

theorem ownC_cfrRecW {m m' : Mem} {cq mi rp3 q : Word} (h : cfrRecW m cq mi rp3 = some (q, m')) :
    ownC m' = ownC m := by
  obtain ⟨q1, m1, h1, rfl, rfl⟩ := cfrRecW_some h
  have hm1 : m1 = erAllocMem m 10 := by
    unfold erAllocW at h1; split at h1 <;> (repeat' split at h1) <;> simp_all
  simp only [cfrMem, ownC_erecPutMem, hm1]
  unfold erAllocMem; split
  · exact ownC_frame (MemFrame.setCtl m 129 _) (by simp) (by decide)
  · exact ownC_frame (MemFrame.setCtl m 130 _) (by simp) (by decide)

/-- **`env_push` at name `ci.name`**: that name's own counter becomes the new view, the others stay. -/
theorem envPush_ownC {p : Prog} (hrs : p.lookup "env_row_set" = some envRowSetL)
    (hpu : p.lookup "env_push" = some envPushL) {n : Nat} {vis : Word} {fe : IFEnv}
    {m m' : Mem} {c : Word} {r : List Word} {ci : IConstantInfo}
    (hc : callW p n "env_push" [vis, c] m = some (r, m')) (hE : EnvR m vis fe)
    (hci : decCI (erecP m) c.toNat = some ci) :
    ownC m' = updC (ownC m) ci.name (vis + 1) ∧ r = [vis + 1] ∧ vis.toNat < 4294967294 := by
  obtain ⟨s', hs', hm, -, hr, hv, ht, hb⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envPush_spec p hrs hpu n ⟨m, Locals.init []⟩ vis c) hc
  obtain ⟨w, hw, hw32, hnm⟩ := decCI_name hci
  have hq : (c + 1).toNat = c.toNat + 1 := by
    have := erecP_lt64 hw; rw [UInt64.toNat_add]; simp; omega
  have hrd : erecRd m (c + 1) = w := erecRd_of (by rw [hq]; exact hw)
  simp only [hrd] at hm ht hb
  refine ⟨?_, hr, hv⟩
  rw [← hs', hm]
  have hv1 : (vis + 1).toNat < 2 ^ 32 := by rw [UInt64.toNat_add]; simp; omega
  funext n'
  simp only [ownC, updC]
  split
  · rename_i e; subst e
    rw [hnm, decI_word_self w hw32]
    exact (ownRaw_ownSet_self ht hb hv1 hE.stamp).1
  · rename_i hne
    rw [ownRaw_ownSet_other hw32 (L.Arena.idx_word_lt32 n') ht fun e => hne (by rw [hnm, ← e, decI_word])]

/-! ## `class_fe_r_go`: the relation to the twin -/

/-- The record's major index and rule prefix are the twin's. -/
theorem rec3FerMiRp {m : Mem} {ro rl M : Word} {P : BlockShape}
    (hrecs : DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) m P.recs) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (ferMi m ro rl M).toNat = P.majorIdxAt M.toNat ∧ (ferRp m ro rl M).toNat = P.rulePrefixAt M.toNat := by
  have hlen := decPL_length _ hrecs
  by_cases hM : M < rl
  · rw [ferMi_hit (h := hM), ferRp_hit (h := hM)]
    have hM' : M.toNat < rl.toNat := UInt64.lt_iff_toNat_lt.mp hM
    obtain ⟨v, hv, hRS⟩ := decPL_getH (truncM m) hrecs M.toNat hM'
    obtain ⟨-, -, -, hrP, hmI, -⟩ := rec2DecRS_parts hRS
    obtain ⟨ev, tv⟩ := rec2RdN (w := ro) (k := M.toNat) (L.Ind.iwN_truncM_some hv).2 hsz
    rw [UInt64.ofNat_toNat] at ev
    obtain ⟨e2, t2⟩ := rec2RdN (w := UInt64.ofNat v) (k := 2) (by rw [tv]; exact (L.Ind.iwN_truncM_some hmI).2) hsz
    obtain ⟨e1, t1⟩ := rec2RdN (w := UInt64.ofNat v) (k := 1) (by rw [tv]; exact (L.Ind.iwN_truncM_some hrP).2) hsz
    simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl] at e1 e2
    rw [ev, e2, e1, t2, t1]
    simp [ConRon.Arena.BlockShape.majorIdxAt, ConRon.Arena.BlockShape.rulePrefixAt,
      List.getElem?_eq_getElem (show M.toNat < P.recs.length by omega)]
  · rw [ferMi_miss (h := hM), ferRp_miss (h := hM)]
    have hM' : ¬ M.toNat < rl.toNat := fun x => hM (UInt64.lt_iff_toNat_lt.mpr x)
    simp [ConRon.Arena.BlockShape.majorIdxAt, ConRon.Arena.BlockShape.rulePrefixAt,
      List.getElem?_eq_none (show P.recs.length ≤ M.toNat by omega)]

theorem ferW_ok (p : Prog) (hp : CfrProg p) (P : BlockShape) (ro rl : Word) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (cvo cvl rcl M : Word) (cvs : List IConstantVal)
      (rcs : List Nat) (r : List Word) (S : List (NIdx × Word)),
    ferW p k m cvo cvl rcl ro rl vis M = some (r, m') → StageR vis fe m a →
    DecB (fun m => decPL m (decRS m) ro.toNat rl.toNat) m P.recs →
    SPL decCVX m cvo.toNat cvl.toNat cvs → rcs.length = rcl.toNat → M.toNat + cvl.toNat < 2 ^ 64 →
    PopOK (ownC m) vis S →
    StageR (r.headD 0) (ConRon.Arena.classFeR.go P M.toNat (cvs.zip rcs) fe []).1 m' a ∧ IWGrow m m' ∧
      SPL decPrev m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat
        (ConRon.Arena.classFeR.go P M.toNat (cvs.zip rcs) fe []).2 ∧
      ∃ cs, SPL decPrevC m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat cs ∧
        PopOK (ownC m') (r.headD 0) (cs.reverse ++ S) := by
  induction k with
  | zero => intro m m' a vis fe cvo cvl rcl M cvs rcs r S h; simp [ferW] at h
  | succ k ih =>
  intro m m' a vis fe cvo cvl rcl M cvs rcs r S h hS hrecs hcvs hrcs hMb hPop
  have hsz := hS.iw.iwSize
  by_cases hz : cvl = 0 ∨ rcl = 0
  · have hz' : cvs.zip rcs = [] := by
      rcases hz with hvl | hcl
      · have := hcvs.length; rw [hvl] at this; simp [List.eq_nil_of_length_eq_zero (by simpa using this)]
      · simp [List.eq_nil_of_length_eq_zero (show rcs.length = 0 by rw [hrcs, hcl]; rfl)]
    rw [show ferW p (k + 1) m cvo cvl rcl ro rl vis M = some ([vis, 0, 0], m) by
      by_cases hvl : cvl = 0
      · exact ferW.arm1 p k m cvo cvl rcl ro rl vis M hvl
      · exact ferW.arm2 p k m cvo cvl rcl ro rl vis M hvl (hz.resolve_left hvl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rw [hz']
    exact ⟨by simpa [ConRon.Arena.classFeR.go.eq_1] using hS, IWGrow.refl m,
      by simpa [ConRon.Arena.classFeR.go.eq_1] using SPL.nil (dec := decPrev) (m := m) 0 (by omega),
      [], by simpa using SPL.nil (dec := decPrevC) (m := m) 0 (by omega), by simpa using hPop⟩
  obtain ⟨hvl, hcl⟩ := not_or.mp hz
  obtain ⟨jv, hjv⟩ : ∃ j, cvl.toNat = j + 1 :=
    ⟨cvl.toNat - 1, by have : cvl.toNat ≠ 0 := fun e => hvl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨p0, cv, cvs', rfl, hp0, hp0t, hcvS, hcvsT⟩ := rec3SPL_uncons (by rw [← hjv]; exact hcvs)
  obtain _ | ⟨rc0, rcs'⟩ := rcs
  · exact absurd (UInt64.toNat_inj.mp (by simpa using hrcs.symm)) hcl
  obtain ⟨e0, t0⟩ := rec2RdN (w := cvo) (k := 0) (by simpa using hp0) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at e0
  obtain ⟨hcvp, hcvx⟩ := rec3CVX hcvS
  obtain ⟨w, hw, hwH, hwnm⟩ := decCV_name (show decCV (erA m) p0 = some cv from hcvp)
  have ew : erRd m (UInt64.ofNat p0) = w := L.Arena.erRd_of _ _ (by rw [t0]; exact hw)
  have hj : ferW p (k + 1) m cvo cvl rcl ro rl vis M =
      ferW.j1 p k cvo cvl rcl ro rl vis M (rdW (m.arr64 IW) cvo) (erRd m (rdW (m.arr64 IW) cvo))
        (ownRaw m (erRd m (rdW (m.arr64 IW) cvo))).1 (ownRaw m (erRd m (rdW (m.arr64 IW) cvo))).2
        (ferMi m ro rl M) (ferRp m ro rl M) m := by
    by_cases hM : M < rl
    · rw [ferW.arm3 (hc1 := hvl) (hc2 := hcl) (hc3 := hM), ferMi_hit (h := hM), ferRp_hit (h := hM)]; rfl
    · rw [ferW.arm4 (hc1 := hvl) (hc2 := hcl) (hc3 := hM), ferMi_miss (h := hM), ferRp_miss (h := hM)]; rfl
  rw [hj, ferW.j1.arm1, e0, ew] at h
  have hprev := rec3PrevD hS.check.env hwH
  obtain ⟨hmi, hrp⟩ := rec3FerMiRp (M := M) hrecs hsz
  -- the record
  obtain ⟨⟨kq, m1⟩, h1, h⟩ := of_K h (ferW.k_class_fe_r_rec.none ..)
  rw [ferW.k_class_fe_r_rec.arm1] at h
  obtain ⟨hS1, hg1, hci⟩ := cfrRec_stage h1 hS (by rw [t0]; exact rec2DecCV_erecP hcvp hcvx)
  rw [hmi, hrp] at hci
  -- the push
  obtain ⟨⟨rv, m2⟩, h2, h⟩ := of_K h (ferW.k_env_push.none ..)
  rw [ferW.k_env_push.arm1] at h
  obtain ⟨hS2, hg2⟩ := envPush_stage hp.rp.rs hp.rp.push h2 hS1 hci
  obtain ⟨hO2, hrv, hv2⟩ := envPush_ownC hp.rp.rs hp.rp.push h2 hS1.check.env hci
  have hO1 : ownC m1 = ownC m := ownC_cfrRecW h1
  -- the displaced row
  obtain ⟨⟨re, m3⟩, h3, h⟩ := of_K h (ferW.k_rec3.none ..)
  rw [ferW.k_rec3.arm1] at h
  obtain ⟨hS3, hg3, hre, hget3, htop3⟩ := recW_stage h3 hS2 rfl
  have hO3 : ownC m3 = ownC m2 := ownC_iw (recW_post h3 hS2.iw.ctl hS2.iw.iwSize rfl).2.2.2.1
  -- the stack grows by the push
  have hcC : (ownRaw m w).1 = ownC m cv.name := by rw [hwnm]; simp only [ownC, decI_word_self w hwH]
  have hvis1 : (vis + 1).toNat = vis.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hE1 := hS1.check.env
  have hO2' : ownC m2 = updC (ownC m1) cv.name (vis + 1) := hO2
  have hcm1 : (ownRaw m1 cv.name.word.toUInt64).1 = (ownRaw m w).1 := by rw [hcC, ← hO1]; rfl
  have hPop3 : PopOK (ownC m3) (rv.headD 0) ((cv.name, (ownRaw m w).1) :: S) := by
    rw [hO3, hO2', hO1, hrv, List.headD_cons]
    refine ⟨by simp [updC], fun e => by have := congrArg UInt64.toNat e; rw [hvis1] at this; simp at this,
      ownRaw_fst_lt m w, fun hc0 => ?_, fun hc0 n' hn' => ?_, ?_⟩
    · have := hE1.fresh cv.name (by rw [hcm1]; exact hc0)
      rw [hcm1] at this; rw [hvis1]; omega
    · simp only [updC, ite_eq_right hn']
      intro e
      have hn1 : (ownRaw m1 n'.word.toUInt64).1 = ownC m n' := by rw [← hO1]; rfl
      exact hn' (hE1.uniq n' cv.name (by rw [hn1, e]; exact hc0) (by rw [hn1, e, hcm1]))
    · rw [updC_idem, hcC, updC_self rfl, show vis + 1 - 1 = vis by simp]
      exact hPop
  have hg03 := (hg1.trans hg2).trans hg3
  have hent : decPrev m3 (re.headD 0).toNat = some (cv.name, fe.idx[cv.name]?) := by
    rw [hre]
    simp only [List.headD_cons, decPrev, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    have g0 := hget3 0 (by simp); have g1 := hget3 1 (by simp); have g2 := hget3 2 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at g0 g1 g2
    refine ⟨decI w, ?_, (ownRaw m w).1, by simpa [iwA, aread_apply] using g1, (ownRaw m w).2,
      by simpa [iwA, aread_apply] using g2, _, rec3PrevD_grow hg03 hprev, by rw [hwnm]⟩
    simp only [iwH, hd?, iwA, aread_apply, g0]; simp [hwH]
  have hentC : StabD (fun m => decPrevC m (re.headD 0).toNat) m3 (cv.name, (ownRaw m w).1) := by
    refine rec3DecPrevC_stab ?_ (by
      have := htop3; simp only [List.length_cons, List.length_nil, iwTop] at this
      rw [hre]; simp only [List.headD_cons, iwTop]; omega)
    rw [hre]
    simp only [List.headD_cons, decPrevC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    have g0 := hget3 0 (by simp); have g1 := hget3 1 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at g0 g1
    refine ⟨decI w, ?_, (ownRaw m w).1, by simpa [iwA, aread_apply] using g1, by rw [hwnm]⟩
    simp only [iwH, hd?, iwA, aread_apply, g0]; simp [hwH]
  have hentS := rec3DecPrev_stab hent (by
    have := htop3; simp only [List.length_cons, List.length_nil, iwTop] at this
    rw [hre]; simp only [List.headD_cons, iwTop]; omega)
  -- the rest
  have hcvo1 := rec2ToNat_succ (o := cvo) (i := cvo.toNat) (Nat.le_refl _) (by have := hS.iw.iw; omega)
  have hcvl1 := L.toNat_sub_one_of_ne hvl
  have hrcl1 := L.toNat_sub_one_of_ne hcl
  have hM1 : (M + 1).toNat = M.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (ferW.k_class_fe_r_go.none ..)
  rw [ferW.k_class_fe_r_go.arm1] at h
  obtain ⟨hS4, hg4, hsp4, cs', hcs4, hPop4⟩ := ih m3 m4 a (rv.headD 0) _ (cvo + 1) (cvl - 1) (rcl - 1) (M + 1)
    cvs' rcs' r4 _ h4 hS3
    (hrecs.grow (OMono.decPL (fun q => decRS_mono q) _ _) hg03)
    (by rw [hcvo1, hcvl1, hjv]; exact hcvsT.grow hg03) (by simp at hrcs; omega) (by omega) hPop3
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h (ferW.k_sl_cons.none ..)
  rw [ferW.k_sl_cons.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS5, hg5, hsp5⟩ := SPL.cons h5 hS4 hsp4 (hentS.grow hg4)
  obtain ⟨-, -, hcs5⟩ := SPL.cons h5 hS4 hcs4 (hentC.grow hg4)
  have hO5 : ownC m5 = ownC m4 := by
    obtain ⟨hb4, ps4, hps4, -⟩ := id hcs4
    exact ownC_iw (consW_decN h5 hS4.iw.iwSize hS4.iw.ctl hb4 hps4).2.2.2.1
  have htw : ConRon.Arena.classFeR.go P M.toNat ((cv :: cvs').zip (rc0 :: rcs')) fe [] =
      ((ConRon.Arena.classFeR.go P (M.toNat + 1) (cvs'.zip rcs')
        (fe.push (.recInfo cv (P.majorIdxAt M.toNat) (P.rulePrefixAt M.toNat) false [])) []).1,
       (cv.name, fe.idx[cv.name]?) :: (ConRon.Arena.classFeR.go P (M.toNat + 1) (cvs'.zip rcs')
        (fe.push (.recInfo cv (P.majorIdxAt M.toNat) (P.rulePrefixAt M.toNat) false [])) []).2) := by
    simp only [List.zip_cons_cons, ConRon.Arena.classFeR.go]
    rw [rec3FerGo_acc]; simp
  rw [hM1] at hS4 hS5 hsp5
  rw [htw]
  refine ⟨by simpa using hS5, (hg03.trans hg4).trans hg5, by simpa using hsp5, (cv.name, (ownRaw m w).1) :: cs',
    by simpa using hcs5, by simpa [hO5] using hPop4⟩

/-- **`class_fe_r` refines `classFeR`**: the rule-less generated recursors pushed (the stage relation
at the returned view of the twin's environment), the displaced rows a stable slice of `rec3`
records, in push order, which pop as a stack (`PopOK`). -/
@[refines ConRon.Arena.classFeR]
theorem classFeR_refines (p : Prog) (hp : CfrProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (vis : Word) (fe : IFEnv) (pp cgo cgl rco rcl : Word) (P : BlockShape)
    (cvGs : List IConstantVal) (recCls : List Nat) (hS : StageR vis fe s₀.mem a₀)
    (hP : DecB (fun m => decBS m pp.toNat) s₀.mem P) (hcg : SPL decCVX s₀.mem cgo.toNat cgl.toNat cvGs)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) s₀.mem recCls) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fe_r" [pp, cgo, cgl, rco, rcl, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR (r.headD 0) (ConRon.Arena.classFeR P cvGs recCls fe).1 s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem ∧
      SPL decPrev s'.mem (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat
        (ConRon.Arena.classFeR P cvGs recCls fe).2 ∧
      ∃ cs, SPL decPrevC s'.mem (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat cs ∧
        PopOK (ownC s'.mem) (r.headD 0) cs.reverse; ⊤⦄ := by
  refine triple_post (classFeR_spec p hp n s₀ pp cgo cgl rco rcl vis) ?_
  rintro r s' ⟨hl, hm⟩
  cases n with
  | zero => simp [ferAW] at hm
  | succ n =>
  rw [ferAW.arm1] at hm
  obtain ⟨⟨r1, m1⟩, h1, hm⟩ := of_K hm rfl
  rw [ferAW.k_class_fe_r_go.arm1] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  have hP' : decBS (truncM s₀.mem) pp.toNat = some P := hP
  simp only [decBS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hP'
  obtain ⟨_m1, _hm1, rs, hrs, _x2, _h2, _x3, _h3, _x4, _h4, _x5, _h5, _x6, _h6, hPe⟩ := hP'
  obtain ⟨ro, rl, hro, hrl, hrecs⟩ := decAt_some hrs
  have hrsP : rs = P.recs := by rw [← hPe]
  rw [hrsP] at hrecs
  have hsz := hS.iw.iwSize
  obtain ⟨e2, t2⟩ := rec2RdN (w := pp) (k := 2) (L.Ind.iwN_truncM_some hro).2 hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := pp) (k := 3) (by simpa using (L.Ind.iwN_truncM_some hrl).2) hsz
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at e2 e3
  rw [e2, e3] at h1
  obtain ⟨hS1, hg1, hsp1, cs, hcs, hPop⟩ := ferW_ok p hp P _ _ n _ _ a₀ vis fe cgo cgl rcl 0 cvGs recCls r1 []
    h1 hS (by rw [t2, t3]; exact hrecs) hcg (decNL_length _ (hrc.get (OMono.decNL _ _)))
    (by simp; exact cgl.toNat_lt) trivial
  exact ⟨hl, by simpa [ConRon.Arena.classFeR] using hS1, hg1, by simpa [ConRon.Arena.classFeR] using hsp1,
    cs, hcs, by simpa using hPop⟩

end L.Ind

end

end
