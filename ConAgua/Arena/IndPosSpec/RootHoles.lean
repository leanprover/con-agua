module

public import ConAgua.Arena.IndPosSpec.CtxFields
import ConAgua.Arena.IndPosSpec.DpGoW
import ConAgua.Arena.IndInstallSpec.BlockCapsAt
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.Env
import ConAgua.Arena.StripTeleSpec
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos

@[expose] public section

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
    ∀ {m : Mem}, StageR vis fe m a → ∀ (q : Word) (ws : List Word), StageR vis fe (wrIW m q ws) a := by
  sorry

/-- **A record write under the stage relation**: the relation kept, the pool grown by `|ws|`
words at the old top, where `ws` is readable. -/
theorem posRecW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m'))
    (hS : StageR vis fe m a) (hl : ws.length < 2 ^ 64) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ q.toNat = iwTop m ∧ iwTop m' = iwTop m + ws.length ∧
      (∀ j < ws.length, (m'.arr64 IW)[q.toNat + j]? = ws[j]?) := by
  sorry

/-! ## Agreement on a set of pool indices -/

/-- `m'` agrees with `m` on the pool indices `P`. -/
def RdS (m m' : Mem) (P : Nat → Prop) : Prop := ∀ i, P i → (m'.arr64 IW)[i]? = (m.arr64 IW)[i]?

theorem RdS.mono {m m' : Mem} {P Q : Nat → Prop} (h : RdS m m' P) (hq : ∀ i, Q i → P i) : RdS m m' Q :=
  fun i hi => h i (hq i hi)

theorem RdS.of_grow {m m' : Mem} (h : IWGrow m m') : RdS m m' (fun i => i < iwTop m) :=
  fun i hi => h.iwGet i hi

theorem RdS.trans {m₁ m₂ m₃ : Mem} {P : Nat → Prop} (h₁ : RdS m₁ m₂ P) (h₂ : RdS m₂ m₃ P) : RdS m₁ m₃ P :=
  fun i hi => (h₂ i hi).trans (h₁ i hi)

theorem RdS.set {m : Mem} {P : Nat → Prop} (x v : Word) (hx : ¬ P x.toNat) : RdS m (m.set64 IW x v) P := by
  intro i hi
  rw [set64IW_get]
  have : ¬ (i = x.toNat ∧ i < (m.arr64 IW).size) := fun ⟨e, _⟩ => hx (e ▸ hi)
  simp only [this, ite_false]

theorem iwN_agree {m m' : Mem} {P : Nat → Prop} (h : RdS m m' P) {i : Nat} (hi : P i) : iwN m' i = iwN m i := by
  sorry

theorem iwH_agree {k : IdxKind} {m m' : Mem} {P : Nat → Prop} (h : RdS m m' P) {i : Nat} (hi : P i) :
    (iwH m' i : Option (Idx k)) = iwH m i := by
  sorry

theorem decHL_agree {k : IdxKind} {m m' : Mem} {P : Nat → Prop} (h : RdS m m' P) {o l : Nat}
    (hi : ∀ j < l, P (o + j)) : (decHL m' o l : Option (List (Idx k))) = decHL m o l := by
  sorry

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
  sorry

theorem NKIn.mono {m : Mem} {P Q : Nat → Prop} {k : Nat} (h : NKIn m k P) (hq : ∀ i, P i → Q i) :
    NKIn m k Q := ⟨fun j hj => hq _ (h.1 j hj), fun o l ho hl j hj => hq _ (h.2 o l ho hl j hj)⟩

theorem NHIn.mono {m : Mem} {P Q : Nat → Prop} {w : Nat} (h : NHIn m w P) (hq : ∀ i, P i → Q i) :
    NHIn m w Q := ⟨hq _ h.1, hq _ h.2.1, fun k hk => (h.2.2 k hk).mono hq⟩

/-- Below the top: a decoding there survives every growth. -/
theorem NHIn.grow {m m' : Mem} {w : Nat} (hw : NHIn m w (· < iwTop m)) (h : IWGrow m m') :
    decNH m' w = decNH m w ∧ NHIn m' w (· < iwTop m') :=
  let ⟨e, hw'⟩ := hw.agree (RdS.of_grow h)
  ⟨e, hw'.mono fun _ hi => Nat.lt_of_lt_of_le hi h.iw⟩

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
  sorry

include ha h2 h4 hg in
theorem rootHoles_spec (hp : p.lookup "nest_ctx_root_holes" = some nestCtxRootHoles) (k : Nat)
    (s₀ : St) (ctx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_ctx_root_holes" [ctx]
    ⦃fun r s' => LocEq s' s₀ ∧ rhW k s₀.mem ctx = some (r, s'.mem); ⊤⦄ := by
  sorry

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
  ⟨h.iw, h.er, (RdS.of_grow h).mono fun _ hi => hi.1, h.erGet⟩

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
  ⟨Nat.le_trans hg.iw h.1, Nat.le_trans hg.er h.2.1,
    fun i hi => (h.2.2.1 i ⟨Nat.lt_of_lt_of_le hi hg.iw, Or.inl (by omega)⟩).trans (hg.iwGet i hi),
    fun i hi => (h.2.2.2 i (Nat.lt_of_lt_of_le hi hg.er)).trans (hg.erGet i hi)⟩

theorem HolesAt.decPL {m : Mem} {q : Nat} {hs : List NestHole} {P : Nat → Prop}
    (h : HolesAt m q hs.length hs P) : decPL m (decNH m) q hs.length = some hs :=
  decPL_of_get _ hs q fun j hj => by
    obtain ⟨w, hw, hd, -⟩ := h j hj
    refine ⟨w.toNat, by simp [iwN, nat?, iwA, hw], ?_⟩
    rw [hd]; exact List.getElem?_eq_getElem hj

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem decNH_of_words {m : Mem} {w : Nat} {k b : Word} {key : NestKey}
    (h0 : (m.arr64 IW)[w]? = some k) (h1 : (m.arr64 IW)[w + 1]? = some b)
    (hk : decNK m k.toNat = some key) : decNH m w = some ⟨key, b.toNat⟩ := by
  simp [decNH, iwN, nat?, iwA, h0, h1, hk]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `ctx.rootHoles`, over its fields. -/
def rhList (names : List NIdx) (lv : LsIdx) (params : List EIdx) (nP : Nat) : List NestHole :=
  names.map fun n => { key := ⟨n, lv, params⟩, base := nP }
-/

theorem rhGoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (a : AState)
    (no nl lv po pl nP q : Word) (names : List NIdx) (params : List EIdx) (k : Nat) :
    ∀ (m m' : Mem) (j : Word),
    rhGoW k m no nl lv po pl nP q j = some m' → StageR vis fe m a →
    decHL m no.toNat nl.toNat = some names → decHL m po.toNat pl.toNat = some params → H lv →
    (∀ i < nl.toNat, no.toNat + i < q.toNat) → (∀ i < pl.toNat, po.toNat + i < q.toNat) →
    q.toNat + nl.toNat ≤ iwTop m → j.toNat ≤ nl.toNat →
    HolesAt m q.toNat j.toNat (rhList names (decI lv) params nP.toNat) (OutR q.toNat nl.toNat (iwTop m)) →
    StageR vis fe m' a ∧ GrowX q.toNat nl.toNat m m' ∧
      HolesAt m' q.toNat nl.toNat (rhList names (decI lv) params nP.toNat)
        (OutR q.toNat nl.toNat (iwTop m')) := by
  sorry

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
  sorry

theorem CtxIn.mono {m : Mem} {P Q : Nat → Prop} {p : Nat} (h : CtxIn m p P) (hq : ∀ i, P i → Q i) :
    CtxIn m p Q := ⟨fun j hj => hq _ (h.1 j hj), fun i hi o l ho hl j hj => hq _ (h.2 i hi o l ho hl j hj)⟩

theorem CtxIn.grow {m m' : Mem} {p : Nat} (hc : CtxIn m p (· < iwTop m)) (h : IWGrow m m') :
    decCtx m' p = decCtx m p ∧ CtxIn m' p (· < iwTop m') :=
  let ⟨e, hc'⟩ := hc.agree (RdS.of_grow h)
  ⟨e, hc'.mono fun _ hi => Nat.lt_of_lt_of_le hi h.iw⟩

theorem rhW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (a : AState)
    (m m' : Mem) (ctx : Word) (r : List Word) (c : NestCtx) (h : rhW k m ctx = some (r, m'))
    (hS : StageR vis fe m a) (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ (r.tail.headD 0).toNat = c.rootHoles.length ∧
      (r.headD 0).toNat + c.rootHoles.length ≤ iwTop m' ∧
      HolesAt m' (r.headD 0).toNat c.rootHoles.length c.rootHoles (· < iwTop m') := by
  sorry

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
    (fe : IFEnv) (vis ctx : Word) (c : NestCtx) (hS : StageR vis fe s₀.mem a₀)
    (hc : decCtx s₀.mem ctx.toNat = some c) (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_ctx_root_holes" [ctx]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
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
    ∀ (n : Nat) {m m' : Mem} {d s l : Word}, copyW n m d s l = some m' → StageR vis fe m a →
    StageR vis fe m' a := by
  sorry

/-- **`sl_append` keeps the stage relation**: the pool grew by the new slice, whose words are the
two sources' (any words: pointers too). -/
theorem appendW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) (hS : StageR vis fe m a)
    (hsrc1 : o1.toNat + l1.toNat ≤ iwTop m) (hsrc2 : o2.toNat + l2.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ (r.headD 0).toNat = iwTop m ∧
      (r.tail.headD 0).toNat = l1.toNat + l2.toNat ∧ iwTop m' = iwTop m + l1.toNat + l2.toNat ∧
      (∀ i < l1.toNat, (m'.arr64 IW)[iwTop m + i]? = (m.arr64 IW)[o1.toNat + i]?) ∧
      (∀ i < l2.toNat, (m'.arr64 IW)[iwTop m + l1.toNat + i]? = (m.arr64 IW)[o2.toNat + i]?) := by
  sorry

theorem HSl.grow {m m' : Mem} {o l : Nat} {hs : List NestHole} (h : HSl m o l hs) (hg : IWGrow m m') :
    HSl m' o l hs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, Nat.le_trans h2 hg.iw, fun i hi => ?_⟩
  obtain ⟨w, hw, hd, hn⟩ := h3 i hi
  obtain ⟨e, hn'⟩ := hn.grow hg
  exact ⟨w, by rw [hg.iwGet _ (by omega)]; exact hw, by rw [e]; exact hd, hn'⟩

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
    (h : haW k m ctx po pl i = some (r, m')) (hS : StageR vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m))
    (hpr : HSl m po.toNat pl.toNat prog) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ decONH m' r (ConRon.Arena.nestHoleAt c prog i.toNat) := by
  sorry

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
    (hS : StageR vis fe s₀.mem a₀) (hcx : decCtx s₀.mem ctx.toNat = some c)
    (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) (hpr : HSl s₀.mem po.toNat pl.toNat prog) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_hole_at" [ctx, po, pl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      decONH s'.mem r (ConRon.Arena.nestHoleAt c prog i.toNat); ⊤⦄ := by
  refine triple_post (nestHoleAt_spec p ha h2 h4 hg hr hc hap hp k s₀ ctx po pl i) ?_
  rintro r s' ⟨hl, hm⟩
  exact ⟨hl, haW_ok k dn fe vis a₀ _ _ ctx po pl i r c prog hm hS hcx hin hpr⟩

end census

end L.Ind

end
