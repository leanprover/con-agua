import ConAgua.Arena.IndPosSpec.CtxFields
import ConAgua.Arena.IndPosSpec.DpGoW
import ConAgua.Arena.IndPosSpec.NoGoStep
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndInstallSpec.DomsW

/-!
# RootHoles: `ConRon.Arena.NestCtx.rootHoles`, `ConRon.Arena.nestHoleAt`

The refinement theorems `nestCtxRootHoles_refines`, `nestHoleAt_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- Words written into the pool keep the stage relation. -/
theorem StageR.wrIW {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} :
    ∀ {m : Mem}, StageR dn vis fe m a → ∀ (q : Word) (ws : List Word), StageR dn vis fe (wrIW m q ws) a
  | _, hS, _, [] => hS
  | _, hS, q, x :: ws => StageR.wrIW (hS.set_iw q x) (q + 1) ws

/-- **A record write under the stage relation**: the relation kept, the pool grown by `|ws|`
words at the old top, where `ws` is readable. -/
theorem posRecW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m'))
    (hS : StageR dn vis fe m a) (hl : ws.length < 2 ^ 64) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ q.toNat = iwTop m ∧ iwTop m' = iwTop m + ws.length ∧
      (∀ j < ws.length, (m'.arr64 IW)[q.toNat + j]? = ws[j]?) := by
  simp only [posRecW] at h
  rcases hal : allocW m (UInt64.ofNat ws.length) with _ | ⟨q1, m1⟩ <;> rw [hal] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.2
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal h3
  subst hm1
  have hk : (UInt64.ofNat ws.length).toNat = ws.length := UInt64.toNat_ofNat_of_lt' hl
  rw [hk] at hroom
  obtain ⟨hget, hg, hf, htop⟩ := recMem_post m ws (UInt64.ofNat ws.length) hk h5
    (by rw [← hq]; exact hroom) h3
  rw [← hq] at hget hg hf htop
  have hqi : q1.toNat = iwTop m := by simp only [iwTop, hq]
  have htop' : iwTop (wrIW (allocMem m (UInt64.ofNat ws.length)) q1 ws) = iwTop m + ws.length := by
    simp only [iwTop] at hqi ⊢
    rw [htop, UInt64.toNat_add, hk, ← hq]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨StageR.wrIW (hS.alloc hal).1 q1 ws, hg, hqi, htop', hget⟩

/-! ## Agreement on a set of pool indices -/

/-- `m'` agrees with `m` on the pool indices `P`. -/
def RdS (m m' : Mem) (P : Nat → Prop) : Prop := ∀ i, P i → (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?

theorem RdS.mono {m m' : Mem} {P Q : Nat → Prop} (h : RdS m m' P) (hq : ∀ i, Q i → P i) : RdS m m' Q :=
  fun i hi => h i (hq i hi)

theorem RdS.of_grow {m m' : Mem} (h : IWGrow m m') : RdS m m' (fun i => i < iwTop m) :=
  fun i hi => h.2.2.1 i hi

theorem RdS.trans {m₁ m₂ m₃ : Mem} {P : Nat → Prop} (h₁ : RdS m₁ m₂ P) (h₂ : RdS m₂ m₃ P) : RdS m₁ m₃ P :=
  fun i hi => (h₂ i hi).trans (h₁ i hi)

theorem RdS.set {m : Mem} {P : Nat → Prop} (x v : Word) (hx : ¬ P x.toNat) : RdS m (m.set64 IW x v) P := by
  intro i hi
  rw [set64IW_get]
  have : ¬ (i = x.toNat ∧ i < (m.arr64 IW).size) := fun ⟨e, _⟩ => hx (e ▸ hi)
  simp only [this, ite_false]

theorem iwN_agree {m m' : Mem} {P : Nat → Prop} (h : RdS m m' P) {i : Nat} (hi : P i) : iwN m' i = iwN m i := by
  simp only [iwN, nat?, iwA]; rw [h i hi]

theorem iwH_agree {k : IdxKind} {m m' : Mem} {P : Nat → Prop} (h : RdS m m' P) {i : Nat} (hi : P i) :
    (iwH m' i : Option (Idx k)) = iwH m i := by
  simp only [iwH, hd?, iwA]; rw [h i hi]

theorem decHL_agree {k : IdxKind} {m m' : Mem} {P : Nat → Prop} (h : RdS m m' P) {o l : Nat}
    (hi : ∀ j < l, P (o + j)) : (decHL m' o l : Option (List (Idx k))) = decHL m o l := by
  simp only [decHL, hslice?]
  apply mapM_opt_congr
  intro j hj
  simp only [hd?, iwA, h (o + j) (hi j (List.mem_range.mp hj))]

theorem NKIn.agree {m m' : Mem} {P : Nat → Prop} {k : Nat} (hk : NKIn m k P) (h : RdS m m' P) :
    decNK m' k = decNK m k ∧ NKIn m' k P := by
  obtain ⟨h4, hs⟩ := hk
  have e2 := iwN_agree h (h4 2 (by omega))
  have e3 := iwN_agree h (h4 3 (by omega))
  refine ⟨?_, h4, fun o l ho hl => hs o l (e2 ▸ ho) (e3 ▸ hl)⟩
  simp only [decNK, iwH_agree h (show P k from by simpa using h4 0 (by omega)), iwH_agree h (h4 1 (by omega)), decAt, e2, e3]
  rcases ho : iwN m (k + 2) with _ | o; · simp
  rcases hl : iwN m (k + 2 + 1) with _ | l; · simp
  have hl' : iwN m (k + 3) = some l := by simpa using hl
  simp only [Option.bind_eq_bind, Option.bind_some, decHL_agree h (hs o l ho hl')]

theorem NHIn.agree {m m' : Mem} {P : Nat → Prop} {w : Nat} (hw : NHIn m w P) (h : RdS m m' P) :
    decNH m' w = decNH m w ∧ NHIn m' w P := by
  obtain ⟨h0, h1, hk⟩ := hw
  have e0 := iwN_agree h h0
  refine ⟨?_, h0, h1, fun k hk' => (hk k (e0 ▸ hk')).agree h |>.2⟩
  simp only [decNH, e0, iwN_agree h h1]
  rcases hkk : iwN m w with _ | k; · simp
  simp only [Option.bind_eq_bind, Option.bind_some, ((hk k hkk).agree h).1]

theorem NKIn.mono {m : Mem} {P Q : Nat → Prop} {k : Nat} (h : NKIn m k P) (hq : ∀ i, P i → Q i) :
    NKIn m k Q := ⟨fun j hj => hq _ (h.1 j hj), fun o l ho hl j hj => hq _ (h.2 o l ho hl j hj)⟩

theorem NHIn.mono {m : Mem} {P Q : Nat → Prop} {w : Nat} (h : NHIn m w P) (hq : ∀ i, P i → Q i) :
    NHIn m w Q := ⟨hq _ h.1, hq _ h.2.1, fun k hk => (h.2.2 k hk).mono hq⟩

/-- Below the top: a decoding there survives every growth. -/
theorem NHIn.grow {m m' : Mem} {w : Nat} (hw : NHIn m w (· < iwTop m)) (h : IWGrow m m') :
    decNH m' w = decNH m w ∧ NHIn m' w (· < iwTop m') :=
  let ⟨e, hw'⟩ := hw.agree (RdS.of_grow h)
  ⟨e, hw'.mono fun _ hi => Nat.lt_of_lt_of_le hi h.1⟩

section arms
variable (k : Nat) (m m1 m2 : Mem) (no nl lv po pl nP q j key h : Word)
theorem rhGoW_done (hd : nl ≤ j) : rhGoW (k + 1) m no nl lv po pl nP q j = some m := by
  simp [rhGoW, hd]
theorem rhGoW_step (hd : ¬ nl ≤ j) : rhGoW (k + 1) m no nl lv po pl nP q j =
    rhK1 k no nl lv po pl nP q j (posRecW m [rdW (m.arr64 IW) (no + j), lv, po, pl]) := by
  simp [rhGoW, hd]
theorem rhK1_some : rhK1 k no nl lv po pl nP q j (some (key, m1)) =
    rhK2 k no nl lv po pl nP q j (posRecW m1 [key, nP]) := by rw [rhK1]
theorem rhK2_some : rhK2 k no nl lv po pl nP q j (some (h, m2)) =
    rhGoW k (m2.set64 IW (q + j) h) no nl lv po pl nP q (j + 1) := by rw [rhK2]
end arms
attribute [ind_grind] rhGoW_done rhGoW_step rhK1_some rhK2_some

def rhA (k : Nat) (no nl lv po pl nP : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => rhB q nl (rhGoW k m1 no nl lv po pl nP q 0)
/-- The model of `nest_ctx_root_holes(ctx)` (its go at `k`). -/
def rhW (k : Nat) (m : Mem) (ctx : Word) : Option (List Word × Mem) :=
  rhA k (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 10))
    (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8)) (rdW (m.arr64 IW) (ctx + 4))
    (allocW m (rdW (m.arr64 IW) (ctx + 1)))
theorem rhB_some (q nl : Word) (m2 : Mem) : rhB q nl (some m2) = some ([q, nl], m2) := rfl
theorem rhA_some (k : Nat) (no nl lv po pl nP q : Word) (m1 : Mem) :
    rhA k no nl lv po pl nP (some (q, m1)) = rhB q nl (rhGoW k m1 no nl lv po pl nP q 0) := rfl
attribute [ind_grind] rhB_some rhA_some

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (h2 : p.lookup "rec2" = some rec2)
  (h4 : p.lookup "rec4" = some rec4)
  (hg : p.lookup "nest_ctx_root_holes_go" = some nestCtxRootHolesGo)

include ha h2 h4 hg in
theorem rhGo_spec (k : Nat) : ∀ (s₀ : St) (no nl lv po pl nP q j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_ctx_root_holes_go" [no, nl, lv, po, pl, nP, q, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ rhGoW k s₀.mem no nl lv po pl nP q j = some s'.mem; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ no nl lv po pl nP q j
    rw [invoke_eq _ hg]; simp only [callFn, nestCtxRootHolesGo]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ no nl lv po pl nP q j
    simp only [invoke_eq _ hg, callFn, nestCtxRootHolesGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        posRec4_specW p ha h4 k, posRec2_specW p ha h2 k, ih] <;>
      finish (gen := 20) [rdW_eq]

include ha h2 h4 hg in
theorem rootHoles_spec (hp : p.lookup "nest_ctx_root_holes" = some nestCtxRootHoles) (k : Nat)
    (s₀ : St) (ctx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_ctx_root_holes" [ctx]
    ⦃fun r s' => LocEq s' s₀ ∧ rhW k s₀.mem ctx = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtxRootHoles]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      iwAlloc_specW p ha k, rhGo_spec p ha h2 h4 hg k] <;>
    finish (gen := 20) [rhW, rdW_eq]

end spec

/-! ### The relational side -/

/-- Below the top `t`, outside the region `[q, q + n)`. -/
def OutR (q n t : Nat) (x : Nat) : Prop := x < t ∧ (x < q ∨ q + n ≤ x)

/-- The pool grew, and outside `[q, q + n)` its old words stayed (a writer into an allocated
region). -/
def GrowX (q n : Nat) (m m' : Mem) : Prop :=
  iwTop m ≤ iwTop m' ∧ erTop m ≤ erTop m' ∧ RdS m m' (OutR q n (iwTop m)) ∧
  (∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?)

theorem GrowX.of_grow {q n : Nat} {m m' : Mem} (h : IWGrow m m') : GrowX q n m m' :=
  ⟨h.1, h.2.1, (RdS.of_grow h).mono fun _ hi => hi.1, h.2.2.2⟩

theorem GrowX.trans {q n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : GrowX q n m₁ m₂) (h₂ : GrowX q n m₂ m₃) :
    GrowX q n m₁ m₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2.1 h₂.2.1,
    h₁.2.2.1.trans (h₂.2.2.1.mono fun _ hi => ⟨Nat.lt_of_lt_of_le hi.1 h₁.1, hi.2⟩),
    fun i hi => (h₂.2.2.2 i (Nat.lt_of_lt_of_le hi h₁.2.1)).trans (h₁.2.2.2 i hi)⟩

theorem GrowX.set {q n : Nat} (m : Mem) (x v : Word) (hx : q ≤ x.toNat ∧ x.toNat < q + n) :
    GrowX q n m (m.set64 IW x v) := by
  have hC : (m.set64 IW x v).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hE : (m.set64 IW x v).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨by simp only [iwTop, hC]; exact Nat.le_refl _, by simp only [erTop, hC]; exact Nat.le_refl _,
    RdS.set x v (fun h => by rcases h.2 with h | h <;> omega), fun i _ => by rw [hE]⟩

theorem GrowX.grow {q n : Nat} {m m' : Mem} (h : GrowX q n m m') (hq : iwTop m ≤ q) : IWGrow m m' :=
  ⟨h.1, h.2.1, fun i hi => h.2.2.1 i ⟨hi, Or.inl (by omega)⟩, h.2.2.2⟩

theorem GrowX.grow' {q n : Nat} {m m1 m2 : Mem} (h : GrowX q n m1 m2) (hg : IWGrow m m1)
    (hq : iwTop m ≤ q) : IWGrow m m2 :=
  ⟨Nat.le_trans hg.1 h.1, Nat.le_trans hg.2.1 h.2.1,
    fun i hi => (h.2.2.1 i ⟨Nat.lt_of_lt_of_le hi hg.1, Or.inl (by omega)⟩).trans (hg.2.2.1 i hi),
    fun i hi => (h.2.2.2 i (Nat.lt_of_lt_of_le hi hg.2.1)).trans (hg.2.2.2 i hi)⟩

theorem HolesAt.decPL {m : Mem} {q : Nat} {hs : List NestHole} {P : Nat → Prop}
    (h : HolesAt m q hs.length hs P) : decPL m (decNH m) q hs.length = some hs :=
  decPL_of_get _ hs q fun j hj => by
    obtain ⟨w, hw, hd, -⟩ := h j hj
    refine ⟨w.toNat, by simp [iwN, nat?, iwA, hw], ?_⟩
    rw [hd]; exact List.getElem?_eq_getElem hj

theorem decNH_of_words {m : Mem} {w : Nat} {k b : Word} {key : NestKey}
    (h0 : (m.arr64 IW)[w]? = some k) (h1 : (m.arr64 IW)[w + 1]? = some b)
    (hk : decNK m k.toNat = some key) : decNH m w = some ⟨key, b.toNat⟩ := by
  simp [decNH, iwN, nat?, iwA, h0, h1, hk]

/-- `ctx.rootHoles`, over its fields. -/
def rhList (names : List NIdx) (lv : LsIdx) (params : List EIdx) (nP : Nat) : List NestHole :=
  names.map fun n => { key := ⟨n, lv, params⟩, base := nP }

theorem rhGoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (a : AState)
    (no nl lv po pl nP q : Word) (names : List NIdx) (params : List EIdx) (k : Nat) :
    ∀ (m m' : Mem) (j : Word),
    rhGoW k m no nl lv po pl nP q j = some m' → StageR dn vis fe m a →
    decHL m no.toNat nl.toNat = some names → decHL m po.toNat pl.toNat = some params → H lv →
    (∀ i < nl.toNat, no.toNat + i < q.toNat) → (∀ i < pl.toNat, po.toNat + i < q.toNat) →
    q.toNat + nl.toNat ≤ iwTop m → j.toNat ≤ nl.toNat →
    HolesAt m q.toNat j.toNat (rhList names (decI lv) params nP.toNat) (OutR q.toNat nl.toNat (iwTop m)) →
    StageR dn vis fe m' a ∧ GrowX q.toNat nl.toNat m m' ∧
      HolesAt m' q.toNat nl.toNat (rhList names (decI lv) params nP.toNat)
        (OutR q.toNat nl.toNat (iwTop m')) := by
  induction k with
  | zero => intro m m' j h; simp [rhGoW] at h
  | succ k ih =>
    intro m m' j h hS hn hp hlv hno hpo hq hj hH
    have hsz := hS.2.2.2.1
    have htop := hS.2.1
    by_cases hd : nl ≤ j
    · rw [rhGoW_done k m no nl lv po pl nP q j hd] at h
      cases h
      have : j.toNat = nl.toNat := by have := UInt64.le_iff_toNat_le.mp hd; omega
      exact ⟨hS, GrowX.of_grow (IWGrow.refl _), this ▸ hH⟩
    rw [rhGoW_step k m no nl lv po pl nP q j hd] at h
    have hjl : j.toNat < nl.toNat := by
      have : ¬ nl.toNat ≤ j.toNat := fun hh => hd (UInt64.le_iff_toNat_le.mpr hh)
      omega
    have hnlen := decHL_length m hn
    -- the member's name
    obtain ⟨hwH, hwd⟩ := rd_iwH (decHL_getI hn j.toNat hjl) (by have := hno j.toNat hjl; omega)
    generalize hw : rdW (m.arr64 IW) (no + j) = w at h hwH hwd
    rcases hr1 : posRecW m [w, lv, po, pl] with _ | ⟨key, m1⟩ <;> rw [hr1] at h; · simp [rhK1] at h
    rw [rhK1_some] at h
    obtain ⟨hS1, hg1, hk1, ht1, hget1⟩ := posRecW_stage hr1 hS (by simp)
    rcases hr2 : posRecW m1 [key, nP] with _ | ⟨hh, m2⟩ <;> rw [hr2] at h; · simp [rhK2] at h
    rw [rhK2_some] at h
    obtain ⟨hS2, hg2, hk2, ht2, hget2⟩ := posRecW_stage hr2 hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht1 ht2
    have hqj : (q + j).toNat = q.toNat + j.toNat := word_add_toNat (by omega)
    have hj1 : (j + 1).toNat = j.toNat + 1 :=
      word_add_toNat (show j.toNat + 1 < 2 ^ 64 by have := nl.toNat_lt; omega)
    have hg12 := hg1.trans hg2
    -- the new hole, in `m2`
    have hgk : ∀ i < 4, (m2.arr64 IW)[key.toNat + i]? = [w, lv, po, pl][i]? := fun i hi => by
      rw [hg2.2.2.1 _ (by omega)]; exact hget1 i (by simpa using hi)
    have hdk : decNK m2 key.toNat = some ⟨names[j.toNat], decI lv, params⟩ := by
      rw [← hwd]
      refine decNK_of_words (hgk 0 (by omega)) hwH (hgk 1 (by omega)) hlv (hgk 2 (by omega))
        (hgk 3 (by omega)) ?_
      rw [decHL_agree (RdS.of_grow hg12) (fun i hi => by have := hpo i hi; omega)]; exact hp
    have hdh : decNH m2 hh.toNat = some ⟨⟨names[j.toNat], decI lv, params⟩, nP.toNat⟩ :=
      decNH_of_words (by simpa using hget2 0 (by simp)) (hget2 1 (by simp)) hdk
    have hin : NHIn m2 hh.toNat (OutR q.toNat nl.toNat (iwTop m2)) := by
      refine ⟨⟨by omega, Or.inr (by omega)⟩, ⟨by omega, Or.inr (by omega)⟩, fun k' hk' => ?_⟩
      have : k' = key.toNat := by
        have h0 : (m2.arr64 IW)[hh.toNat]? = some key := by simpa using hget2 0 (by simp)
        have : iwN m2 hh.toNat = some key.toNat := by simp [iwN, nat?, iwA, h0]
        rw [this] at hk'; exact (Option.some.inj hk').symm
      subst this
      refine ⟨fun i hi => ⟨by omega, Or.inr (by omega)⟩, fun o l ho hl i hi => ?_⟩
      have e2 : o = po.toNat := by
        have := hgk 2 (by omega); simp [iwN, nat?, iwA, this] at ho; exact ho.symm
      have e3 : l = pl.toNat := by
        have := hgk 3 (by omega); simp [iwN, nat?, iwA, this] at hl; exact hl.symm
      subst e2 e3
      have := hpo i hi
      exact ⟨by omega, Or.inl this⟩
    -- the write
    have hS3 := hS2.set_iw (q + j) hh
    have hset : RdS m2 (m2.set64 IW (q + j) hh) (OutR q.toNat nl.toNat (iwTop m2)) :=
      RdS.set _ _ (fun hx => by rcases hx.2 with h' | h' <;> omega)
    have ht3 : iwTop (m2.set64 IW (q + j) hh) = iwTop m2 := by
      simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    have hGX : GrowX q.toNat nl.toNat m (m2.set64 IW (q + j) hh) :=
      (GrowX.of_grow hg12).trans (GrowX.set m2 (q + j) hh (by omega))
    have hRm : RdS m (m2.set64 IW (q + j) hh) (OutR q.toNat nl.toNat (iwTop m)) := hGX.2.2.1
    have hH3 : HolesAt (m2.set64 IW (q + j) hh) q.toNat (j + 1).toNat
        (rhList names (decI lv) params nP.toNat) (OutR q.toNat nl.toNat (iwTop (m2.set64 IW (q + j) hh))) := by
      rw [hj1, ht3]
      intro i hi
      by_cases hij : i = j.toNat
      · subst hij
        refine ⟨hh, ?_, ?_, ?_⟩
        · rw [set64IW_get, ite_eq_left ⟨hqj.symm, by have := hS2.2.1; omega⟩]
        · rw [(hin.agree hset).1, hdh]
          simp [rhList, List.getElem?_map, List.getElem?_eq_getElem (show j.toNat < names.length by omega)]
        · exact (hin.agree hset).2
      · obtain ⟨wi, hwi, hdi, hini⟩ := hH i (by omega)
        refine ⟨wi, ?_, ?_, ?_⟩
        · rw [set64IW_get, ite_eq_right (by omega), hg12.2.2.1 _ (by omega)]; exact hwi
        · rw [(hini.agree hRm).1]; exact hdi
        · exact (hini.agree hRm).2.mono fun x hx => ⟨Nat.lt_of_lt_of_le hx.1 (by omega), hx.2⟩
    have hOut : ∀ {o l : Nat}, (∀ j < l, o + j < q.toNat) → ∀ j < l, OutR q.toNat nl.toNat (iwTop m) (o + j) :=
      fun hol j hj => ⟨by have := hol j hj; omega, Or.inl (hol j hj)⟩
    obtain ⟨hS', hGX', hH'⟩ := ih (m2.set64 IW (q + j) hh) m' (j + 1) h hS3
      (by rw [decHL_agree hRm (hOut hno)]; exact hn) (by rw [decHL_agree hRm (hOut hpo)]; exact hp)
      hlv hno hpo (by rw [ht3]; omega) (by rw [hj1]; omega) hH3
    exact ⟨hS', hGX.trans hGX', hH'⟩

theorem decAt_agree {α : Type} {g g' : Nat → Nat → Option (List α)} {m m' : Mem} {i : Nat}
    (h0 : iwN m' i = iwN m i) (h1 : iwN m' (i + 1) = iwN m (i + 1))
    (hg : ∀ o l, iwN m i = some o → iwN m (i + 1) = some l → g' o l = g o l) :
    decAt m' g' i = decAt m g i := by
  simp only [decAt, h0, h1]
  rcases ho : iwN m i with _ | o; · simp
  cases hl : iwN m (i + 1) with
  | none => simp
  | some l => simp only [Option.bind_eq_bind, Option.bind_some]; exact hg o l ho hl

theorem decNL_agree {m m' : Mem} {P : Nat → Prop} (h : RdS m m' P) {o l : Nat}
    (hi : ∀ j < l, P (o + j)) : decNL m' o l = decNL m o l := by
  simp only [decNL]
  apply mapM_opt_congr
  intro j hj
  exact iwN_agree h (hi j (List.mem_range.mp hj))

theorem CtxIn.agree {m m' : Mem} {P : Nat → Prop} {p : Nat} (hc : CtxIn m p P) (h : RdS m m' P) :
    decCtx m' p = decCtx m p ∧ CtxIn m' p P := by
  obtain ⟨h11, hs⟩ := hc
  have e : ∀ j < 11, iwN m' (p + j) = iwN m (p + j) := fun j hj => iwN_agree h (h11 j hj)
  have eH : ∀ {k : IdxKind} j, j < 11 → (iwH m' (p + j) : Option (Idx k)) = iwH m (p + j) :=
    fun j hj => iwH_agree h (h11 j hj)
  have hat : ∀ {α : Type} {g g' : Nat → Nat → Option (List α)} (i : Nat), (i = 0 ∨ i = 2 ∨ i = 5 ∨ i = 7) →
      (∀ o l, (∀ j < l, P (o + j)) → g' o l = g o l) → decAt m' g' (p + i) = decAt m g (p + i) := by
    intro α g g' i hi hg
    exact decAt_agree (e i (by omega)) (by rw [show p + i + 1 = p + (i + 1) by omega]; exact e (i + 1) (by omega))
      (fun o l ho hl => hg o l (hs i hi o l ho hl))
  refine ⟨?_, h11, fun i hi o l ho hl => hs i hi o l (by rw [← e i (by omega)]; exact ho)
    (by rw [show p + i + 1 = p + (i + 1) by omega, ← e (i + 1) (by omega)]; rw [show p + (i + 1) = p + i + 1 by omega]; exact hl)⟩
  simp only [decCtx]
  rw [show p = p + 0 by omega, hat 0 (by omega) (fun o l hol => decHL_agree h hol),
    hat 2 (by omega) (fun o l hol => decHL_agree h hol), e 4 (by omega),
    hat 5 (by omega) (fun o l hol => decNL_agree h hol), hat 7 (by omega) (fun o l hol => decHL_agree h hol),
    eH 9 (by omega), eH 10 (by omega)]

theorem CtxIn.mono {m : Mem} {P Q : Nat → Prop} {p : Nat} (h : CtxIn m p P) (hq : ∀ i, P i → Q i) :
    CtxIn m p Q := ⟨fun j hj => hq _ (h.1 j hj), fun i hi o l ho hl j hj => hq _ (h.2 i hi o l ho hl j hj)⟩

theorem CtxIn.grow {m m' : Mem} {p : Nat} (hc : CtxIn m p (· < iwTop m)) (h : IWGrow m m') :
    decCtx m' p = decCtx m p ∧ CtxIn m' p (· < iwTop m') :=
  let ⟨e, hc'⟩ := hc.agree (RdS.of_grow h)
  ⟨e, hc'.mono fun _ hi => Nat.lt_of_lt_of_le hi h.1⟩

theorem rhW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (a : AState)
    (m m' : Mem) (ctx : Word) (r : List Word) (c : NestCtx) (h : rhW k m ctx = some (r, m'))
    (hS : StageR dn vis fe m a) (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ (r.tail.headD 0).toNat = c.rootHoles.length ∧
      (r.headD 0).toNat + c.rootHoles.length ≤ iwTop m' ∧
      HolesAt m' (r.headD 0).toNat c.rootHoles.length c.rootHoles (· < iwTop m') := by
  have hsz : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, hn', hpa, hpa', hnP, hlvH, hlv, -, -, -⟩ := ctx_fields hc hin hsz
  unfold rhW at h
  generalize rdW (m.arr64 IW) ctx = no at h hn hn'
  generalize rdW (m.arr64 IW) (ctx + 1) = nl at h hn hn'
  generalize rdW (m.arr64 IW) (ctx + 7) = po at h hpa hpa'
  generalize rdW (m.arr64 IW) (ctx + 8) = pl at h hpa hpa'
  generalize rdW (m.arr64 IW) (ctx + 4) = nP at h hnP
  generalize rdW (m.arr64 IW) (ctx + 10) = lv at h hlvH hlv
  have hlen : c.rootHoles.length = nl.toNat := by
    simp [NestCtx.rootHoles, decHL_length m hn]
  have hrh : c.rootHoles = rhList c.names (decI lv) c.params nP.toNat := by
    simp [NestCtx.rootHoles, rhList, hlv, hnP]
  rcases hal : allocW m nl with _ | ⟨q, m1⟩ <;> rw [hal] at h; · simp [rhA] at h
  rw [rhA_some] at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  have hqt : q.toNat = iwTop m := by simp only [iwTop, hqd]
  rcases hgo : rhGoW k m1 no nl lv po pl nP q 0 with _ | m2 <;> rw [hgo] at h; · simp [rhB] at h
  rw [rhB_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS2, hGX, hH⟩ := rhGoW_ok dn fe vis a no nl lv po pl nP q c.names c.params k m1 m2 0 hgo hS1
    (by rw [decHL_agree (RdS.of_grow hg1) hn']; exact hn) (by rw [decHL_agree (RdS.of_grow hg1) hpa']; exact hpa)
    hlvH (fun i hi => by have := hn' i hi; omega) (fun i hi => by have := hpa' i hi; omega) (by omega)
    (by simp) (fun i hi => by simp at hi)
  have hgr : IWGrow m m2 := hGX.grow' hg1 (by omega)
  refine ⟨hS2, hgr, by simp [hlen], ?_, ?_⟩
  · simp only [List.headD_cons]; have := hGX.1; omega
  · rw [hrh, show (rhList c.names (decI lv) c.params nP.toNat).length = nl.toNat by
      rw [← hrh]; exact hlen]
    simp only [List.headD_cons]
    intro i hi
    obtain ⟨w, hw, hd, hni⟩ := hH i hi
    exact ⟨w, hw, hd, hni.mono fun _ hx => hx.1⟩

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (h2 : p.lookup "rec2" = some rec2)
  (h4 : p.lookup "rec4" = some rec4)
  (hg : p.lookup "nest_ctx_root_holes_go" = some nestCtxRootHolesGo)
  (hp : p.lookup "nest_ctx_root_holes" = some nestCtxRootHoles)
include ha h2 h4 hg hp

/-- **`nest_ctx_root_holes` refines `NestCtx.rootHoles`**: the holes as a new `IW` slice of
`NestHole` pointers, each decoded below the top. -/
@[refines ConRon.Arena.NestCtx.rootHoles]
theorem nestCtxRootHoles_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ctx : Word) (c : NestCtx) (hS : StageR dn vis fe s₀.mem a₀)
    (hc : decCtx s₀.mem ctx.toNat = some c) (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_ctx_root_holes" [ctx]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      (r.tail.headD 0).toNat = c.rootHoles.length ∧
      (r.headD 0).toNat + c.rootHoles.length ≤ iwTop s'.mem ∧
      decPL s'.mem (decNH s'.mem) (r.headD 0).toNat c.rootHoles.length = some c.rootHoles ∧
      HolesAt s'.mem (r.headD 0).toNat c.rootHoles.length c.rootHoles (· < iwTop s'.mem); ⊤⦄ := by
  refine triple_post (rootHoles_spec p ha h2 h4 hg hp k s₀ ctx) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hS', hg', h1, h2, h3⟩ := rhW_ok k dn fe vis a₀ _ _ ctx r c hm hS hc hin
  exact ⟨hl, hS', hg', h1, h2, h3.decPL, h3⟩

end census

/-! ## `sl_append` over words, under the stage relation -/

theorem StageR.ofCopyW {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} :
    ∀ (n : Nat) {m m' : Mem} {d s l : Word}, copyW n m d s l = some m' → StageR dn vis fe m a →
    StageR dn vis fe m' a
  | 0, _, _, _, _, _, h, _ => by simp [copyW] at h
  | n + 1, m, m', d, s, l, h, hS => by
    by_cases hl : l = 0
    · rw [copyW_nil n m d s l hl] at h; cases h; exact hS
    · rw [copyW_step n m d s l hl] at h
      exact StageR.ofCopyW n h (hS.set_iw d _)

/-- **`sl_append` keeps the stage relation**: the pool grew by the new slice, whose words are the
two sources' (any words: pointers too). -/
theorem appendW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) (hS : StageR dn vis fe m a)
    (hsrc1 : o1.toNat + l1.toNat ≤ iwTop m) (hsrc2 : o2.toNat + l2.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ (r.headD 0).toNat = iwTop m ∧
      (r.tail.headD 0).toNat = l1.toNat + l2.toNat ∧ iwTop m' = iwTop m + l1.toNat + l2.toNat ∧
      (∀ i < l1.toNat, (m'.arr64 IW)[iwTop m + i]? = (m.arr64 IW)[o1.toNat + i]?) ∧
      (∀ i < l2.toNat, (m'.arr64 IW)[iwTop m + l1.toNat + i]? = (m.arr64 IW)[o2.toNat + i]?) := by
  have hsz := hS.2.2.2.1
  have hc := hS.2.2.2.2.2
  simp only [appendW] at h
  by_cases h0 : l1 + l2 < l1
  · simp [h0] at h
  simp only [h0, ite_false] at h
  rcases hal : allocW m (l1 + l2) with _ | ⟨q, m1⟩; · simp [hal] at h
  obtain ⟨hS1, -, -, -, -⟩ := hS.alloc hal
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  rcases hcp1 : copyW (n - 1) m1 q o1 l1 with _ | m2; · simp [hcp1] at h
  simp only [hcp1] at h
  rcases hcp2 : copyW (n - 1) m2 (q + l1) o2 l2 with _ | m3; · simp [hcp2] at h
  simp only [hcp2, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hS3 := StageR.ofCopyW _ hcp2 (StageR.ofCopyW _ hcp1 hS1)
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hlt : ¬ (l1 + l2).toNat < l1.toNat := by
    intro hh; exact h0 (UInt64.lt_iff_toNat_lt.mpr hh)
  have hs : (l1 + l2).toNat = l1.toNat + l2.toNat := by
    rw [UInt64.toNat_add] at hlt ⊢
    have := l1.toNat_lt; have := l2.toNat_lt
    omega
  rw [hs] at hroom
  have hql : (q + l1).toNat = q.toNat + l1.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hIW := allocMem_IW m (l1 + l2)
  have hqt : q.toNat = iwTop m := by simp only [iwTop, hqq]
  obtain ⟨hA1, hS1', hW1, hG1⟩ := copyW_get (n - 1) _ _ _ _ _ hcp1 (by omega)
    (by rw [hIW]; omega) (by rw [hIW]; exact hsz)
  obtain ⟨hA2, hS2', hW2, hG2⟩ := copyW_get (n - 1) _ _ _ _ _ hcp2 (by rw [hql]; omega)
    (by rw [hql, hS1', hIW]; omega) (by rw [hS1', hIW]; exact hsz)
  rw [hIW] at hS1' hG1
  have hfr : MemFrame [IW] [200] m m3 :=
    (allocMem_frame m (l1 + l2)).trans
      ((copy_frame hA1 (by rw [hS1', hIW]) hW1).trans
       (copy_frame hA2 hS2' hW2))
  have hget : ∀ i, (m3.arr64 IW)[i]? =
      if q.toNat ≤ i ∧ i < q.toNat + l1.toNat then (m.arr64 IW)[o1.toNat + (i - q.toNat)]?
      else if q.toNat + l1.toNat ≤ i ∧ i < q.toNat + l1.toNat + l2.toNat then
        (m.arr64 IW)[o2.toNat + (i - (q.toNat + l1.toNat))]?
      else (m.arr64 IW)[i]? := by
    intro i
    rw [hG2 i, hql]
    by_cases h1 : q.toNat ≤ i ∧ i < q.toNat + l1.toNat
    · rw [ite_eq_right (by omega), hG1, ite_eq_left h1, ite_eq_left h1]
    · by_cases h2 : q.toNat + l1.toNat ≤ i ∧ i < q.toNat + l1.toNat + l2.toNat
      · rw [ite_eq_left h2, hG1, ite_eq_right (by omega), ite_eq_right h1, ite_eq_left h2]
      · rw [ite_eq_right h2, hG1, ite_eq_right h1, ite_eq_right h1, ite_eq_right h2]
  have htop : rdW (m3.arr64 CTL) 200 = q + (l1 + l2) := by
    rw [hA2 CTL (by decide), hA1 CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + (l1 + l2)).toNat = q.toNat + (l1.toNat + l2.toNat) := by
    rw [UInt64.toNat_add, hs]; simp; omega
  refine ⟨hS3, ?_, by simp [hqt], by simp [hs], ?_, fun i hi => ?_, fun i hi => ?_⟩
  · refine iwGrow_of_frame hfr (N := l1 + l2) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hget, ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [iwTop, htop, hsum]; simp only [iwTop] at hqt; omega
  · rw [hget, ← hqt, ite_eq_left (by omega)]; congr 2; omega
  · rw [hget, ← hqt, ite_eq_right (by omega), ite_eq_left (by omega)]; congr 2; omega

theorem HSl.grow {m m' : Mem} {o l : Nat} {hs : List NestHole} (h : HSl m o l hs) (hg : IWGrow m m') :
    HSl m' o l hs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, Nat.le_trans h2 hg.1, fun i hi => ?_⟩
  obtain ⟨w, hw, hd, hn⟩ := h3 i hi
  obtain ⟨e, hn'⟩ := hn.grow hg
  exact ⟨w, by rw [hg.2.2.1 _ (by omega)]; exact hw, by rw [e]; exact hd, hn'⟩

/-- `nest_ctx_root_holes` at any exec fuel. -/
def rhWf : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, ctx => rhW k m ctx

def haK1 (k : Nat) (po pl idx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => haK2 idx (appendW k m1 (r.headD 0) (r.tail.headD 0) po pl)
/-- The model of `nest_hole_at(ctx, progOff, progLen, i)` at exec fuel `k + 1`. -/
def haW (k : Nat) (m : Mem) (ctx po pl i : Word) : Option (List Word × Mem) :=
  if i < rdW (m.arr64 IW) (ctx + 4) then some ([0, 0], m)
  else haK1 k po pl (i - rdW (m.arr64 IW) (ctx + 4)) (rhWf k m ctx)

section arms
variable (k : Nat) (m1 m2 : Mem) (po pl idx : Word) (r r2 : List Word)
theorem haK2_hit (h : idx < r2.tail.headD 0) :
    haK2 idx (some (r2, m2)) = some ([1, rdW (m2.arr64 IW) (r2.headD 0 + idx)], m2) := by
  simp only [haK2]; rw [ite_eq_left h]
theorem haK2_miss (h : ¬ idx < r2.tail.headD 0) : haK2 idx (some (r2, m2)) = some ([0, 0], m2) := by
  simp only [haK2]; rw [ite_eq_right h]
theorem haK1_some : haK1 k po pl idx (some (r, m1)) =
    haK2 idx (appendW k m1 (r.headD 0) (r.tail.headD 0) po pl) := rfl
end arms
attribute [ind_grind] haK2_hit haK2_miss haK1_some

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (h2 : p.lookup "rec2" = some rec2)
  (h4 : p.lookup "rec4" = some rec4)
  (hg : p.lookup "nest_ctx_root_holes_go" = some nestCtxRootHolesGo)
  (hr : p.lookup "nest_ctx_root_holes" = some nestCtxRootHoles)
  (hc : p.lookup "iw_copy" = some iwCopy) (hap : p.lookup "sl_append" = some slAppend)
  (hp : p.lookup "nest_hole_at" = some nestHoleAt)

include ha h2 h4 hg hr in
theorem rootHoles_spec' (k : Nat) (s₀ : St) (ctx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_ctx_root_holes" [ctx]
    ⦃fun r s' => LocEq s' s₀ ∧ rhWf k s₀.mem ctx = some (r, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ hr]; simp only [callFn, nestCtxRootHoles]; vcgen [exec] <;> grind
  | succ k => exact rootHoles_spec p ha h2 h4 hg hr k s₀ ctx

include ha h2 h4 hg hr hc hap hp in
theorem nestHoleAt_spec (k : Nat) (s₀ : St) (ctx po pl i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_hole_at" [ctx, po, pl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ haW k s₀.mem ctx po pl i = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestHoleAt]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      rootHoles_spec' p ha h2 h4 hg hr k, slAppend_specW p ha hc hap k] <;>
    finish (gen := 20) [haW, rdW_eq]

end spec

theorem rdW_of_get' {a : Array Word} {x : Word} {i : Nat} {w : Word} (hx : x.toNat = i) (h : a[i]? = some w) :
    rdW a x = w := by simp [rdW, hx, h]

theorem haW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (a : AState)
    (m m' : Mem) (ctx po pl i : Word) (r : List Word) (c : NestCtx) (prog : List NestHole)
    (h : haW k m ctx po pl i = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m))
    (hpr : HSl m po.toNat pl.toNat prog) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ decONH m' r (ConRon.Arena.nestHoleAt c prog i.toNat) := by
  have hsz : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, -, -, -, hnP, -, -, -, -, -⟩ := ctx_fields hc hin hsz
  unfold haW at h
  by_cases hlt : i < rdW (m.arr64 IW) (ctx + 4)
  · rw [ite_eq_left hlt] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨hS, IWGrow.refl _, ?_⟩
    have : ¬ c.nP ≤ i.toNat := by rw [← hnP]; have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    simp [ConRon.Arena.nestHoleAt, this, decONH]
  rw [ite_eq_right hlt] at h
  have hge : c.nP ≤ i.toNat := by
    rw [← hnP]
    have : ¬ (i.toNat < (rdW (m.arr64 IW) (ctx + 4)).toNat) := fun h' => hlt (UInt64.lt_iff_toNat_lt.mpr h')
    omega
  have hidx : (i - rdW (m.arr64 IW) (ctx + 4)).toNat = i.toNat - c.nP := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega), hnP]
  generalize i - rdW (m.arr64 IW) (ctx + 4) = idx at h hidx
  cases k with
  | zero => simp [rhWf, haK1] at h
  | succ k =>
  simp only [rhWf] at h
  rcases hrh : rhW k m ctx with _ | ⟨r1, m1⟩ <;> rw [hrh] at h; · simp [haK1] at h
  rw [haK1_some] at h
  obtain ⟨hS1, hg1, hl1, hb1, hH1⟩ := rhW_ok k dn fe vis a m m1 ctx r1 c hrh hS hc hin
  obtain ⟨hplen, hpb, hpH⟩ := hpr
  rcases hap : appendW (k + 1) m1 (r1.headD 0) (r1.tail.headD 0) po pl with _ | ⟨r2, m2⟩ <;> rw [hap] at h; · simp [haK2] at h
  obtain ⟨hS2, hg2, hr20, hr21, ht2, hw1, hw2⟩ := appendW_stage hap hS1 (by rw [hl1]; exact hb1)
    (by have := hg1.1; omega)
  rw [hl1] at hr21 hw1 ht2 hw2
  have hsz2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hlen := c.rootHoles.length
  by_cases hh : idx < r2.tail.headD 0
  · rw [haK2_hit (h := hh)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hh' : idx.toNat < c.rootHoles.length + pl.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp hh; omega
    have hx : (r2.headD 0 + idx).toNat = iwTop m1 + idx.toNat := by
      rw [word_add_toNat (by omega), hr20]
    refine ⟨hS2, hg1.trans hg2, ?_⟩
    simp only [ConRon.Arena.nestHoleAt, ite_eq_left hge, decONH, List.headD_cons, List.tail_cons, true_and]
    by_cases hr : idx.toNat < c.rootHoles.length
    · obtain ⟨w, hw, hd, hni⟩ := hH1 idx.toNat hr
      have hw' : (m2.arr64 IW)[iwTop m1 + idx.toNat]? = some w := by
        rw [hw1 _ hr]; exact hw
      obtain ⟨e, hni'⟩ := hni.grow hg2
      rw [rdW_of_get' hx hw', ← hidx, List.getElem?_append_left hr, List.getElem?_eq_getElem hr]
      rw [List.getElem?_eq_getElem hr] at hd
      exact ⟨by rw [e, hd], hni'⟩
    · obtain ⟨w, hw, hd, hni⟩ := hpH (idx.toNat - c.rootHoles.length) (by omega)
      have hw' : (m2.arr64 IW)[iwTop m1 + idx.toNat]? = some w := by
        have := hw2 (idx.toNat - c.rootHoles.length) (by omega)
        rw [show iwTop m1 + c.rootHoles.length + (idx.toNat - c.rootHoles.length) = iwTop m1 + idx.toNat by omega]
          at this
        rw [this, hg1.2.2.1 _ (by omega)]; exact hw
      obtain ⟨e, hni'⟩ := hni.grow (hg1.trans hg2)
      have hr' : idx.toNat - c.rootHoles.length < prog.length := by omega
      rw [rdW_of_get' hx hw', ← hidx, List.getElem?_append_right (by omega), List.getElem?_eq_getElem hr']
      rw [List.getElem?_eq_getElem hr'] at hd
      exact ⟨by rw [e, hd], hni'⟩
  · rw [haK2_miss (h := hh)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨hS2, hg1.trans hg2, ?_⟩
    have hh' : ¬ idx.toNat < c.rootHoles.length + pl.toNat := by
      intro hc'; exact hh (UInt64.lt_iff_toNat_lt.mpr (by omega))
    simp only [ConRon.Arena.nestHoleAt, ite_eq_left hge, decONH]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (h2 : p.lookup "rec2" = some rec2)
  (h4 : p.lookup "rec4" = some rec4)
  (hg : p.lookup "nest_ctx_root_holes_go" = some nestCtxRootHolesGo)
  (hr : p.lookup "nest_ctx_root_holes" = some nestCtxRootHoles)
  (hc : p.lookup "iw_copy" = some iwCopy) (hap : p.lookup "sl_append" = some slAppend)
  (hp : p.lookup "nest_hole_at" = some nestHoleAt)
include ha h2 h4 hg hr hc hap hp

/-- **`nest_hole_at` refines `nestHoleAt`**: the hole's record pointer, decoded below the top. -/
@[refines ConRon.Arena.nestHoleAt]
theorem nestHoleAt_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ctx po pl i : Word) (c : NestCtx) (prog : List NestHole)
    (hS : StageR dn vis fe s₀.mem a₀) (hcx : decCtx s₀.mem ctx.toNat = some c)
    (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) (hpr : HSl s₀.mem po.toNat pl.toNat prog) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_hole_at" [ctx, po, pl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      decONH s'.mem r (ConRon.Arena.nestHoleAt c prog i.toNat); ⊤⦄ := by
  refine triple_post (nestHoleAt_spec p ha h2 h4 hg hr hc hap hp k s₀ ctx po pl i) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, haW_ok k dn fe vis a₀ _ _ ctx po pl i r c prog hm hS hcx hin hpr⟩

end census

end L.Ind

end
