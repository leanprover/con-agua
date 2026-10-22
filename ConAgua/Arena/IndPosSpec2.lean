import ConAgua.Arena.IndPos2Spec
import ConAgua.Arena.IndInstallSpec2
import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclRec

/-! # `IndPos`'s remaining functions (lane `indproofs2`, helper `pos`)

`NestCtx.rootHoles`, `nestHoleAt`, `nestContainer`, … — the template of `IndPos2Spec*.lean`.

Shared pieces here: `posRecW` (the record writers `rec2`‥`rec6` as one word model, no
precondition) with `posRecW_stage` (the stage relation kept, the words readable, the pool grown);
`RdS` (two memories agree on a set of `IW` indices) and the decoders' agreement lemmas
(`decNK_agree`, `decNH_agree`): a decoding whose reads all lie in the set survives. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The record writers as one model -/

/-- The model of `recK(ws…)`: allocate `|ws|` words, write `ws` at the old top. -/
def posRecW (m : Mem) (ws : List Word) : Option (Word × Mem) :=
  match allocW m (UInt64.ofNat ws.length) with
  | none => none
  | some (q, m1) => some (q, wrIW m1 q ws)

theorem posRecW_eq (m : Mem) (ws : List Word) (k : Word) (hk : k = UInt64.ofNat ws.length) :
    posRecW m ws = (match allocW m k with
      | none => none
      | some (q, _) => some (q, wrIW (allocMem m k) (rdW (m.arr64 CTL) 200) ws)) := by
  subst hk
  simp only [posRecW]
  cases h : allocW m (UInt64.ofNat ws.length) with
  | none => rfl
  | some pr =>
    obtain ⟨q, m1⟩ := pr
    simp only [allocW] at h
    split at h
    · simp at h
    split at h
    · simp at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem posRec2_eq (m : Mem) (a b : Word) :
    (match allocW m 2 with | none => none | some (q, _) => some (q, rec2Mem m a b)) =
      posRecW m [a, b] := by
  rw [posRecW_eq m [a, b] 2 rfl, rec2Mem_eq]
theorem posRec4_eq (m : Mem) (a b c d : Word) :
    (match allocW m 4 with | none => none | some (q, _) => some (q, rec4Mem m a b c d)) =
      posRecW m [a, b, c, d] := by
  rw [posRecW_eq m [a, b, c, d] 4 rfl, rec4Mem_eq]
theorem posRec5_eq (m : Mem) (a b c d e : Word) :
    (match allocW m 5 with | none => none | some (q, _) => some (q, rec5Mem m a b c d e)) =
      posRecW m [a, b, c, d, e] := by
  rw [posRecW_eq m [a, b, c, d, e] 5 rfl, rec5Mem_eq]
theorem posRec6_eq (m : Mem) (a b c d e f : Word) :
    (match allocW m 6 with | none => none | some (q, _) => some (q, rec6Mem m a b c d e f)) =
      posRecW m [a, b, c, d, e, f] := by
  rw [posRecW_eq m [a, b, c, d, e, f] 6 rfl, rec6Mem_eq]

section recspecs
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
include ha

theorem rec2_specW (h2 : p.lookup "rec2" = some rec2) (n : Nat) (s₀ : St) (a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec2" [a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← posRec2_eq, invoke_eq _ h2]
  simp only [callFn, rec2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec2Mem, allocMem, allocW]

theorem rec4_specW (h4 : p.lookup "rec4" = some rec4) (n : Nat) (s₀ : St) (a b c d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec4" [a, b, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c, d] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← posRec4_eq, invoke_eq _ h4]
  simp only [callFn, rec4]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec4Mem, allocMem, allocW]

theorem rec5_specW (h5 : p.lookup "rec5" = some rec5) (n : Nat) (s₀ : St) (a b c d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec5" [a, b, c, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c, d, e] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← posRec5_eq, invoke_eq _ h5]
  simp only [callFn, rec5]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec5Mem, allocMem, allocW]

theorem rec6_specW (h6 : p.lookup "rec6" = some rec6) (n : Nat) (s₀ : St) (a b c d e f : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec6" [a, b, c, d, e, f]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c, d, e, f] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← posRec6_eq, invoke_eq _ h6]
  simp only [callFn, rec6]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec6Mem, allocMem, allocW]

end recspecs

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
  cases hal : allocW m (UInt64.ofNat ws.length) with
  | none => rw [hal] at h; simp at h
  | some pr =>
    obtain ⟨q1, m1⟩ := pr
    rw [hal] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
  simp only [hd?, iwA]
  rw [h (o + j) (hi j (List.mem_range.mp hj))]

/-- The indices `decNK m k` reads lie in `P`. -/
def NKIn (m : Mem) (k : Nat) (P : Nat → Prop) : Prop :=
  (∀ j < 4, P (k + j)) ∧ ∀ o l, iwN m (k + 2) = some o → iwN m (k + 3) = some l → ∀ j < l, P (o + j)

/-- The indices `decNH m w` reads lie in `P`. -/
def NHIn (m : Mem) (w : Nat) (P : Nat → Prop) : Prop :=
  P w ∧ P (w + 1) ∧ ∀ k, iwN m w = some k → NKIn m k P

theorem NKIn.agree {m m' : Mem} {P : Nat → Prop} {k : Nat} (hk : NKIn m k P) (h : RdS m m' P) :
    decNK m' k = decNK m k ∧ NKIn m' k P := by
  obtain ⟨h4, hs⟩ := hk
  have e2 := iwN_agree h (h4 2 (by omega))
  have e3 := iwN_agree h (h4 3 (by omega))
  refine ⟨?_, h4, fun o l ho hl => hs o l (e2 ▸ ho) (e3 ▸ hl)⟩
  simp only [decNK]
  rw [iwH_agree h (show P k from by simpa using h4 0 (by omega)), iwH_agree h (h4 1 (by omega))]
  simp only [decAt]
  rw [e2, e3]
  cases ho : iwN m (k + 2) with
  | none => simp
  | some o =>
    cases hl : iwN m (k + 2 + 1) with
    | none => simp
    | some l =>
      have hl' : iwN m (k + 3) = some l := by simpa using hl
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [decHL_agree h (hs o l ho hl')]

theorem NHIn.agree {m m' : Mem} {P : Nat → Prop} {w : Nat} (hw : NHIn m w P) (h : RdS m m' P) :
    decNH m' w = decNH m w ∧ NHIn m' w P := by
  obtain ⟨h0, h1, hk⟩ := hw
  have e0 := iwN_agree h h0
  refine ⟨?_, h0, h1, fun k hk' => (hk k (e0 ▸ hk')).agree h |>.2⟩
  simp only [decNH]
  rw [e0, iwN_agree h h1]
  cases hkk : iwN m w with
  | none => simp
  | some k =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [((hk k hkk).agree h).1]

theorem NKIn.mono {m : Mem} {P Q : Nat → Prop} {k : Nat} (h : NKIn m k P) (hq : ∀ i, P i → Q i) :
    NKIn m k Q := ⟨fun j hj => hq _ (h.1 j hj), fun o l ho hl j hj => hq _ (h.2 o l ho hl j hj)⟩

theorem NHIn.mono {m : Mem} {P Q : Nat → Prop} {w : Nat} (h : NHIn m w P) (hq : ∀ i, P i → Q i) :
    NHIn m w Q := ⟨hq _ h.1, hq _ h.2.1, fun k hk => (h.2.2 k hk).mono hq⟩

/-- Below the top: a decoding there survives every growth. -/
theorem NHIn.grow {m m' : Mem} {w : Nat} (hw : NHIn m w (· < iwTop m)) (h : IWGrow m m') :
    decNH m' w = decNH m w ∧ NHIn m' w (· < iwTop m') :=
  let ⟨e, hw'⟩ := hw.agree (RdS.of_grow h)
  ⟨e, hw'.mono fun _ hi => Nat.lt_of_lt_of_le hi h.1⟩

/-! ## Word reads of decoded fields -/

/-- A decoded number at `p + i` is the word L reads there. -/
theorem rd_iwN {m : Mem} {p i : Word} {v : Nat} (h : iwN m (p.toNat + i.toNat) = some v)
    (hb : p.toNat + i.toNat < 2 ^ 64) : (rdW (m.arr64 IW) (p + i)).toNat = v := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have : (p + i).toNat = p.toNat + i.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hb
  simp [rdW, this, hw]

/-- A decoded handle at `p + i` is the word L reads there. -/
theorem rd_iwH {k : IdxKind} {m : Mem} {p i : Word} {x : Idx k} (h : iwH m (p.toNat + i.toNat) = some x)
    (hb : p.toNat + i.toNat < 2 ^ 64) :
    H (rdW (m.arr64 IW) (p + i)) ∧ decI (rdW (m.arr64 IW) (p + i)) = x := by
  obtain ⟨w, hw, hl, hx⟩ := hd?_some h
  have : (p + i).toNat = p.toNat + i.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt hb
  simp only [iwA] at hw
  simp only [rdW, this, hw, Option.getD_some]
  exact ⟨hl, hx.symm⟩

theorem word_add_toNat {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-! ## `nest_ctx_root_holes(_go)` refines `NestCtx.rootHoles` -/

mutual
def rhGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, lv, po, pl, nP, q, j =>
    if nl ≤ j then some m
    else rhK1 k no nl lv po pl nP q j (posRecW m [rdW (m.arr64 IW) (no + j), lv, po, pl])
def rhK1 (k : Nat) (no nl lv po pl nP q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (key, m1) => rhK2 k no nl lv po pl nP q j (posRecW m1 [key, nP])
def rhK2 (k : Nat) (no nl lv po pl nP q j : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (h, m2) => rhGoW k (m2.set64 IW (q + j) h) no nl lv po pl nP q (j + 1)
end

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

def rhB (q nl : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m2 => some ([q, nl], m2)
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
    rw [invoke_eq _ hg]
    simp only [callFn, nestCtxRootHolesGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        rec4_specW p ha h4 k, rec2_specW p ha h2 k, ih] <;>
      finish (gen := 20) [rdW_eq]

include ha h2 h4 hg in
theorem rootHoles_spec (hp : p.lookup "nest_ctx_root_holes" = some nestCtxRootHoles) (k : Nat)
    (s₀ : St) (ctx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_ctx_root_holes" [ctx]
    ⦃fun r s' => LocEq s' s₀ ∧ rhW k s₀.mem ctx = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestCtxRootHoles]
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

/-- The pointers at `q, …, q + j - 1` decode to the first `j` holes, every read in `P`. -/
def HolesAt (m : Mem) (q j : Nat) (hs : List NestHole) (P : Nat → Prop) : Prop :=
  ∀ i < j, ∃ w : Word, (m.arr64 IW)[q + i]? = some w ∧ decNH m w.toNat = hs[i]? ∧ NHIn m w.toNat P

theorem HolesAt.decPL {m : Mem} {q : Nat} {hs : List NestHole} {P : Nat → Prop}
    (h : HolesAt m q hs.length hs P) : decPL m (decNH m) q hs.length = some hs :=
  decPL_of_get _ hs q fun j hj => by
    obtain ⟨w, hw, hd, -⟩ := h j hj
    refine ⟨w.toNat, by simp [iwN, nat?, iwA, hw], ?_⟩
    rw [hd]; exact List.getElem?_eq_getElem hj

theorem decNK_of_words {m : Mem} {k : Nat} {c u o l : Word} {ds : List EIdx}
    (h0 : (m.arr64 IW)[k]? = some c) (hc : H c) (h1 : (m.arr64 IW)[k + 1]? = some u) (hu : H u)
    (h2 : (m.arr64 IW)[k + 2]? = some o) (h3 : (m.arr64 IW)[k + 3]? = some l)
    (hs : decHL m o.toNat l.toNat = some ds) : decNK m k = some ⟨decI c, decI u, ds⟩ := by
  simp only [decNK, decAt, iwH, iwN, nat?, hd?, iwA, h0, h1, h2, h3, hc, hu, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, if_true]
  simp [hs]

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
    cases hr1 : posRecW m [w, lv, po, pl] with
    | none => rw [hr1] at h; simp [rhK1] at h
    | some pr1 =>
    obtain ⟨key, m1⟩ := pr1
    rw [hr1, rhK1_some] at h
    obtain ⟨hS1, hg1, hk1, ht1, hget1⟩ := posRecW_stage hr1 hS (by simp)
    cases hr2 : posRecW m1 [key, nP] with
    | none => rw [hr2] at h; simp [rhK2] at h
    | some pr2 =>
    obtain ⟨hh, m2⟩ := pr2
    rw [hr2, rhK2_some] at h
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
        · rw [set64IW_get, if_pos ⟨hqj.symm, by have := hS2.2.1; omega⟩]
        · rw [(hin.agree hset).1, hdh]
          simp [rhList, List.getElem?_map, List.getElem?_eq_getElem (show j.toNat < names.length by omega)]
        · exact (hin.agree hset).2
      · obtain ⟨wi, hwi, hdi, hini⟩ := hH i (by omega)
        refine ⟨wi, ?_, ?_, ?_⟩
        · rw [set64IW_get, if_neg (by omega), hg12.2.2.1 _ (by omega)]; exact hwi
        · rw [(hini.agree hRm).1]; exact hdi
        · exact (hini.agree hRm).2.mono fun x hx => ⟨Nat.lt_of_lt_of_le hx.1 (by omega), hx.2⟩
    have hOut : ∀ {o l : Nat}, (∀ j < l, o + j < q.toNat) → ∀ j < l, OutR q.toNat nl.toNat (iwTop m) (o + j) :=
      fun hol j hj => ⟨by have := hol j hj; omega, Or.inl (hol j hj)⟩
    obtain ⟨hS', hGX', hH'⟩ := ih (m2.set64 IW (q + j) hh) m' (j + 1) h hS3
      (by rw [decHL_agree hRm (hOut hno)]; exact hn) (by rw [decHL_agree hRm (hOut hpo)]; exact hp)
      hlv hno hpo (by rw [ht3]; omega) (by rw [hj1]; omega) hH3
    exact ⟨hS', hGX.trans hGX', hH'⟩


/-! ### `NestCtx` records: where their reads lie -/

/-- The indices `decCtx m p` reads lie in `P`. -/
def CtxIn (m : Mem) (p : Nat) (P : Nat → Prop) : Prop :=
  (∀ j < 11, P (p + j)) ∧ ∀ i, (i = 0 ∨ i = 2 ∨ i = 5 ∨ i = 7) → ∀ o l, iwN m (p + i) = some o →
    iwN m (p + i + 1) = some l → ∀ j < l, P (o + j)

theorem decAt_agree {α : Type} {g g' : Nat → Nat → Option (List α)} {m m' : Mem} {i : Nat}
    (h0 : iwN m' i = iwN m i) (h1 : iwN m' (i + 1) = iwN m (i + 1))
    (hg : ∀ o l, iwN m i = some o → iwN m (i + 1) = some l → g' o l = g o l) :
    decAt m' g' i = decAt m g i := by
  simp only [decAt, h0, h1]
  cases ho : iwN m i with
  | none => simp
  | some o =>
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

/-- A `NestCtx` record decoded below the top: its fields as the words L reads. -/
theorem ctx_fields {m : Mem} {p : Word} {c : NestCtx} (hc : decCtx m p.toNat = some c)
    (hin : CtxIn m p.toNat (· < iwTop m)) (hsz : iwTop m < 2 ^ 64) :
    decHL m (rdW (m.arr64 IW) p).toNat (rdW (m.arr64 IW) (p + 1)).toNat = some c.names ∧
    (∀ j < (rdW (m.arr64 IW) (p + 1)).toNat, (rdW (m.arr64 IW) p).toNat + j < iwTop m) ∧
    decHL m (rdW (m.arr64 IW) (p + 7)).toNat (rdW (m.arr64 IW) (p + 8)).toNat = some c.params ∧
    (∀ j < (rdW (m.arr64 IW) (p + 8)).toNat, (rdW (m.arr64 IW) (p + 7)).toNat + j < iwTop m) ∧
    (rdW (m.arr64 IW) (p + 4)).toNat = c.nP ∧
    H (rdW (m.arr64 IW) (p + 10)) ∧ decI (rdW (m.arr64 IW) (p + 10)) = c.lvls ∧
    H (rdW (m.arr64 IW) (p + 9)) ∧ decI (rdW (m.arr64 IW) (p + 9)) = c.sort ∧
    p.toNat + 11 ≤ iwTop m := by
  obtain ⟨hn, -, hnP, -, hpa, hso, hlv⟩ := decCtx_some hc
  have h10 := hin.1 10 (by omega)
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hn
  obtain ⟨o7, l7, ho7, hl7, hd7⟩ := decAt_some hpa
  have r0 : (rdW (m.arr64 IW) p).toNat = o := by
    have := rd_iwN (m := m) (p := p) (i := 0) (by simpa using ho) (by simp; omega); simpa using this
  have r1 : (rdW (m.arr64 IW) (p + 1)).toNat = l := rd_iwN (by simpa using hl) (by simp; omega)
  have r7 : (rdW (m.arr64 IW) (p + 7)).toNat = o7 := rd_iwN (by simpa using ho7) (by simp; omega)
  have r8 : (rdW (m.arr64 IW) (p + 8)).toNat = l7 := rd_iwN (by simpa using hl7) (by simp; omega)
  have r4 : (rdW (m.arr64 IW) (p + 4)).toNat = c.nP := rd_iwN (by simpa using hnP) (by simp; omega)
  obtain ⟨h10a, h10b⟩ := rd_iwH (p := p) (i := 10) (by simpa using hlv) (by simp; omega)
  obtain ⟨h9a, h9b⟩ := rd_iwH (p := p) (i := 9) (by simpa using hso) (by simp; omega)
  have hl0 := decHL_length m hd
  have hl7' := decHL_length m hd7
  have s0 : ∀ j < l, o + j < iwTop m := hin.2 0 (by omega) o l (by simpa using ho) (by simpa using hl)
  have s7 : ∀ j < l7, o7 + j < iwTop m := hin.2 7 (by omega) o7 l7 ho7 hl7
  exact ⟨by rw [r0, r1]; exact hd, by rw [r0, r1]; exact s0, by rw [r7, r8]; exact hd7,
    by rw [r7, r8]; exact s7, r4, h10a, h10b, h9a, h9b, by omega⟩

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
  cases hal : allocW m nl with
  | none => rw [hal] at h; simp [rhA] at h
  | some pq =>
  obtain ⟨q, m1⟩ := pq
  rw [hal, rhA_some] at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  have hqt : q.toNat = iwTop m := by simp only [iwTop, hqd]
  cases hgo : rhGoW k m1 no nl lv po pl nP q 0 with
  | none => rw [hgo] at h; simp [rhB] at h
  | some m2 =>
  rw [hgo, rhB_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
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
  simp only [h0, if_false] at h
  cases hal : allocW m (l1 + l2) with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hS1, -, -, -, -⟩ := hS.alloc hal
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp1 : copyW (n - 1) m1 q o1 l1 with
  | none => simp [hcp1] at h
  | some m2 =>
  simp only [hcp1] at h
  cases hcp2 : copyW (n - 1) m2 (q + l1) o2 l2 with
  | none => simp [hcp2] at h
  | some m3 =>
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
    · rw [if_neg (by omega), hG1, if_pos h1, if_pos h1]
    · by_cases h2 : q.toNat + l1.toNat ≤ i ∧ i < q.toNat + l1.toNat + l2.toNat
      · rw [if_pos h2, hG1, if_neg (by omega), if_neg h1, if_pos h2]
      · rw [if_neg h2, hG1, if_neg h1, if_neg h1, if_neg h2]
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
      rw [hget, if_neg (by omega), if_neg (by omega)]
  · simp only [iwTop, htop, hsum]; simp only [iwTop] at hqt; omega
  · rw [hget, ← hqt, if_pos (by omega)]; congr 2; omega
  · rw [hget, ← hqt, if_neg (by omega), if_pos (by omega)]; congr 2; omega

/-! ## `nest_hole_at` refines `nestHoleAt` -/

/-- A slice of `NestHole` pointers below the top, decoding to `hs`. -/
def HSl (m : Mem) (o l : Nat) (hs : List NestHole) : Prop :=
  hs.length = l ∧ o + l ≤ iwTop m ∧ HolesAt m o l hs (· < iwTop m)

theorem HSl.grow {m m' : Mem} {o l : Nat} {hs : List NestHole} (h : HSl m o l hs) (hg : IWGrow m m') :
    HSl m' o l hs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, Nat.le_trans h2 hg.1, fun i hi => ?_⟩
  obtain ⟨w, hw, hd, hn⟩ := h3 i hi
  obtain ⟨e, hn'⟩ := hn.grow hg
  exact ⟨w, by rw [hg.2.2.1 _ (by omega)]; exact hw, by rw [e]; exact hd, hn'⟩

/-- An optional hole: `(0, _)` or `(1, w)` with `w` decoding below the top. -/
def decONH (m : Mem) (r : List Word) : Option NestHole → Prop
  | none => r.headD 0 = 0
  | some h => r.headD 0 = 1 ∧ decNH m (r.tail.headD 0).toNat = some h ∧
      NHIn m (r.tail.headD 0).toNat (· < iwTop m)

/-- `nest_ctx_root_holes` at any exec fuel. -/
def rhWf : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, ctx => rhW k m ctx

def haK2 (idx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if idx < r2.tail.headD 0 then some ([1, rdW (m2.arr64 IW) (r2.headD 0 + idx)], m2)
    else some ([0, 0], m2)
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
  simp only [haK2]; rw [if_pos h]
theorem haK2_miss (h : ¬ idx < r2.tail.headD 0) : haK2 idx (some (r2, m2)) = some ([0, 0], m2) := by
  simp only [haK2]; rw [if_neg h]
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
  rw [invoke_eq _ hp]
  simp only [callFn, nestHoleAt]
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
  · rw [if_pos hlt] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hS, IWGrow.refl _, ?_⟩
    have : ¬ c.nP ≤ i.toNat := by rw [← hnP]; have := UInt64.lt_iff_toNat_lt.mp hlt; omega
    simp [ConRon.Arena.nestHoleAt, this, decONH]
  rw [if_neg hlt] at h
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
  cases hrh : rhW k m ctx with
  | none => rw [hrh] at h; simp [haK1] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  rw [hrh, haK1_some] at h
  obtain ⟨hS1, hg1, hl1, hb1, hH1⟩ := rhW_ok k dn fe vis a m m1 ctx r1 c hrh hS hc hin
  obtain ⟨hplen, hpb, hpH⟩ := hpr
  cases hap : appendW (k + 1) m1 (r1.headD 0) (r1.tail.headD 0) po pl with
  | none => rw [hap] at h; simp [haK2] at h
  | some pr2 =>
  obtain ⟨r2, m2⟩ := pr2
  rw [hap] at h
  obtain ⟨hS2, hg2, hr20, hr21, ht2, hw1, hw2⟩ := appendW_stage hap hS1 (by rw [hl1]; exact hb1)
    (by have := hg1.1; omega)
  rw [hl1] at hr21 hw1 ht2 hw2
  have hsz2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hlen := c.rootHoles.length
  by_cases hh : idx < r2.tail.headD 0
  · rw [haK2_hit (h := hh)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hh' : idx.toNat < c.rootHoles.length + pl.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp hh; omega
    have hx : (r2.headD 0 + idx).toNat = iwTop m1 + idx.toNat := by
      rw [word_add_toNat (by omega), hr20]
    refine ⟨hS2, hg1.trans hg2, ?_⟩
    simp only [ConRon.Arena.nestHoleAt, if_pos hge, decONH, List.headD_cons, List.tail_cons, true_and]
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
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hS2, hg1.trans hg2, ?_⟩
    have hh' : ¬ idx.toNat < c.rootHoles.length + pl.toNat := by
      intro hc'; exact hh (UInt64.lt_iff_toNat_lt.mpr (by omega))
    simp only [ConRon.Arena.nestHoleAt, if_pos hge, decONH]
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

/-! ## `nest_container(_ctors(_go))` refines `nestContainer`: word models -/

mutual
def ncGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, C, co, cl, cs, ol, fp =>
    if cl = 0 then some ([ol, fp], m)
    else ncK1 k vis C co cl cs ol fp (envFindW m (rdW (m.arr64 EREC) co) vis)
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

section arms
variable (k : Nat) (m m1 m2 m3 : Mem) (vis C co cl cs ol fp nPc q : Word) (r r2 : List Word)
theorem ncGoW_done (h : cl = 0) : ncGoW (k + 1) m vis C co cl cs ol fp = some ([ol, fp], m) := by
  simp [ncGoW, h]
theorem ncGoW_step (h : ¬ cl = 0) : ncGoW (k + 1) m vis C co cl cs ol fp =
    ncK1 k vis C co cl cs ol fp (envFindW m (rdW (m.arr64 EREC) co) vis) := by simp [ncGoW, h]
theorem ncK1_miss (h : r.headD 0 = 0) : ncK1 k vis C co cl cs ol fp (some (r, m1)) =
    ncGoW k m1 vis C (co + 1) (cl - 1) cs ol fp := by rw [ncK1, if_pos h]
theorem ncK1_hit (h : ¬ r.headD 0 = 0) : ncK1 k vis C co cl cs ol fp (some (r, m1)) =
    ncK2 k vis C co cl cs ol fp (entryW m1 C (r.tail.headD 0)) := by rw [ncK1, if_neg h]
theorem ncK2_miss (h : r2.headD 0 = 0) : ncK2 k vis C co cl cs ol fp (some (r2, m2)) =
    ncGoW k m2 vis C (co + 1) (cl - 1) cs ol fp := by rw [ncK2, if_pos h]
theorem ncK2_hit (h : ¬ r2.headD 0 = 0) : ncK2 k vis C co cl cs ol fp (some (r2, m2)) =
    ncK3 k vis C co cl cs ol fp (r2.tail.tail.headD 0)
      (posRecW m2 [r2.tail.headD 0, r2.tail.tail.tail.headD 0]) := by rw [ncK2, if_neg h]
theorem ncK3_first (h : ol = 0) : ncK3 k vis C co cl cs ol fp nPc (some (q, m3)) =
    ncGoW k (m3.set64 IW (cs + ol) q) vis C (co + 1) (cl - 1) cs (ol + 1) nPc := by rw [ncK3, if_pos h]
theorem ncK3_next (h : ¬ ol = 0) : ncK3 k vis C co cl cs ol fp nPc (some (q, m3)) =
    ncGoW k (m3.set64 IW (cs + ol) q) vis C (co + 1) (cl - 1) cs (ol + 1) fp := by rw [ncK3, if_neg h]
end arms
attribute [ind_grind] ncGoW_done ncGoW_step ncK1_miss ncK1_hit ncK2_miss ncK2_hit ncK3_first ncK3_next

def ncB (cs : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([cs, r.headD 0, r.tail.headD 0], m2)
/-- The model of `nest_container_ctors` at exec fuel `k + 1`. -/
def ncW (k : Nat) (m : Mem) (vis C co cl : Word) : Option (List Word × Mem) :=
  match allocW m cl with
  | none => none
  | some (cs, m1) => ncB cs (ncGoW k m1 vis C co cl cs 0 0)
def ncWf : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, C, co, cl => ncW k m vis C co cl
theorem ncB_some (cs : Word) (r : List Word) (m2 : Mem) :
    ncB cs (some (r, m2)) = some ([cs, r.headD 0, r.tail.headD 0], m2) := rfl
attribute [ind_grind] ncB_some

def ntK2 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.tail.headD 0 = 0 then some ([1, rdW (m2.arr64 EREC) (q + 5 + 12), r2.headD 0, 0], m2)
    else some ([1, r2.tail.tail.headD 0, r2.headD 0, r2.tail.headD 0], m2)
def ntK1 (k : Nat) (vis C : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0], m1)
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then some ([0, 0, 0, 0], m1)
    else ntK2 (r.tail.headD 0) (ncWf k m1 vis C (rdW (m1.arr64 EREC) (r.tail.headD 0 + 5 + 13))
      (rdW (m1.arr64 EREC) (r.tail.headD 0 + 5 + 14)))
/-- The model of `nest_container(vis, C)` at exec fuel `k + 1`. -/
def ntW (k : Nat) (m : Mem) (vis C : Word) : Option (List Word × Mem) := ntK1 k vis C (envFindW m C vis)

section arms
variable (k : Nat) (m1 m2 : Mem) (vis C q : Word) (r r2 : List Word)
theorem ntK2_empty (h : r2.tail.headD 0 = 0) :
    ntK2 q (some (r2, m2)) = some ([1, rdW (m2.arr64 EREC) (q + 5 + 12), r2.headD 0, 0], m2) := by
  rw [ntK2, if_pos h]
theorem ntK2_cons (h : ¬ r2.tail.headD 0 = 0) :
    ntK2 q (some (r2, m2)) = some ([1, r2.tail.tail.headD 0, r2.headD 0, r2.tail.headD 0], m2) := by
  rw [ntK2, if_neg h]
theorem ntK1_miss (h : r.headD 0 = 0) : ntK1 k vis C (some (r, m1)) = some ([0, 0, 0, 0], m1) := by
  rw [ntK1, if_pos h]
theorem ntK1_noind (h : ¬ r.headD 0 = 0) (h3 : rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    ntK1 k vis C (some (r, m1)) = some ([0, 0, 0, 0], m1) := by rw [ntK1, if_neg h, if_pos h3]
theorem ntK1_ind (h : ¬ r.headD 0 = 0) (h3 : ¬ rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    ntK1 k vis C (some (r, m1)) = ntK2 (r.tail.headD 0) (ncWf k m1 vis C
      (rdW (m1.arr64 EREC) (r.tail.headD 0 + 5 + 13)) (rdW (m1.arr64 EREC) (r.tail.headD 0 + 5 + 14))) := by
  rw [ntK1, if_neg h, if_neg h3]
end arms
attribute [ind_grind] ntK2_empty ntK2_cons ntK1_miss ntK1_noind ntK1_ind

/-- The lookups of `nest_container`. -/
structure NtLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  h2 : p.lookup "rec2" = some rec2
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip
  hv : p.lookup "e_view" = some eView
  he : p.lookup "nest_ctor_entry" = some nestCtorEntry
  hgo : p.lookup "nest_container_ctors_go" = some nestContainerCtorsGo
  hcc : p.lookup "nest_container_ctors" = some nestContainerCtors
  hnt : p.lookup "nest_container" = some nestContainer

section spec
variable (p : Prog) (hl : NtLook p)

set_option maxHeartbeats 1000000 in
include hl in
theorem ncGo_spec (k : Nat) : ∀ (s₀ : St) (vis C co cl cs ol fp : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_container_ctors_go" [vis, C, co, cl, cs, ol, fp]
    ⦃fun r s' => LocEq s' s₀ ∧
      ncGoW k s₀.mem vis C co cl cs ol fp = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ vis C co cl cs ol fp
    rw [invoke_eq _ hl.hgo]; simp only [callFn, nestContainerCtorsGo]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ vis C co cl cs ol fp
    rw [invoke_eq _ hl.hgo]
    simp only [callFn, nestContainerCtorsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        envFind_specW p hl.hx hl.hg hl.hf k, nestCtorEntry_spec p hl.hs hl.hv hl.he k,
        rec2_specW p hl.ha hl.h2 k, ih] <;>
      finish (gen := 20) [rdW_eq, St.setLocs_mem']

include hl in
theorem nc_spec (k : Nat) (s₀ : St) (vis C co cl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_container_ctors" [vis, C, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ ncWf k s₀.mem vis C co cl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hl.hcc]
  simp only [callFn, nestContainerCtors]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iwAlloc_specW p hl.ha k, ncGo_spec p hl k] <;>
      finish (gen := 20) [ncWf, ncW]

include hl in
theorem nt_spec (k : Nat) (s₀ : St) (vis C : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_container" [vis, C]
    ⦃fun r s' => LocEq s' s₀ ∧ ntW k s₀.mem vis C = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hl.hnt]
  simp only [callFn, nestContainer]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      envFind_specW p hl.hx hl.hg hl.hf k, nc_spec p hl k] <;>
    finish (gen := 20) [ntW, rdW_eq]

end spec

/-! ### `nest_container`: the relational side -/

theorem rowPW_eq (m : Mem) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : tagW w ≤ 2) :
    rowPW m w = rowP m w := by
  have h1 := tagW_toNat w
  have h2 := ixW_toNat w hw
  have ht' : rowTag w ≤ 2 := by rw [← h1]; exact UInt64.le_iff_toNat_le.mp ht
  have hix : rowIx w < 2 ^ 30 := by simp only [rowIx]; omega
  have h3 : (ixW w + 1).toNat = rowIx w + 1 := by rw [word_add_toNat (by rw [h2]; simp; omega), h2]; rfl
  simp only [rowPW, rowP, ht', if_true, rdW, h3]
  have : rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2 := by omega
  rcases this with h | h | h
  · have : tagW w = 0 := UInt64.toNat_inj.mp (by rw [h1, h]; rfl)
    simp [this, h, EIXA]
  · have : tagW w = 1 := UInt64.toNat_inj.mp (by rw [h1, h]; rfl)
    simp [this, h, EIXS]
  · have : tagW w = 2 := UInt64.toNat_inj.mp (by rw [h1, h]; rfl)
    simp [this, h, EIXN]

/-- **A hit of `env_find` is a `find?`** of the record it points to. -/
theorem envFindW_hit {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem}
    {w : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) (hE : EnvR dn m vis fe)
    (hw : w.toNat < 2 ^ 32) (h0 : r.headD 0 ≠ 0) :
    m1 = m ∧ fe.find? (decI w) = decCI (erecP m) dn (r.tail.headD 0).toNat ∧
      ∃ ci, decCI (erecP m) dn (r.tail.headD 0).toNat = some ci := by
  unfold envFindW at h
  by_cases ht : 2 < tagW w
  · simp [ht] at h
  rw [if_neg ht] at h
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => ht (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  rw [EnvR.find?_eq hE w hw htag, ← rowCW_eq m w hw ht2, ← rowPW_eq m w hw ht2]
  by_cases hc : rowCW m w = 0
  · rw [if_pos hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0
  rw [if_neg hc] at h
  by_cases hv : rowCW m w - 1 < vis
  · rw [if_pos hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hrc : rowC m w ≠ 0 := by rw [← rowCW_eq m w hw ht2]; exact hc
    refine ⟨rfl, ?_, by rw [List.tail_cons, List.headD_cons, rowPW_eq m w hw ht2]; exact EnvR.row_dec hE w hw htag hrc⟩
    have hc' : (rowCW m w).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
    have : (rowCW m w).toNat - 1 < vis.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp hv
      rwa [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))] at this
    simp [hc, this]
  · rw [if_neg hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at h0; simp at h0

theorem envFindW_mem {m m1 : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) :
    m1 = m := by
  unfold envFindW at h
  split at h; · simp at h
  split at h; · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm)

theorem decCI_ctor_cv {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {nPc nF : Nat} (h : decCI a dn p = some (.ctorInfo cv nPc nF)) :
    decCV a (p + 1) = some cv := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  match k, h with
  | 0, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 1, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 2, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 3, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 4, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv', h1, _, _, _, _, h2⟩ := h
    cases h2; exact h1
  | 5, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 6, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | (_ + 7), h => simp_all

theorem erecP_ext_of {m m' : Mem} (h1 : erTop m ≤ erTop m')
    (h2 : ∀ i < erTop m, (m'.arr64 EREC)[i]? = (m.arr64 EREC)[i]?) : ArrExt (erecP m) (erecP m') := by
  intro i v hv
  have hlt : i < erTop m := by
    have := (Array.getElem?_eq_some_iff.mp hv).1
    simp only [erecP, Array.size_extract, erecTop] at this
    simp only [erTop]; omega
  rw [erecP_getE (by omega), h2 i hlt, ← erecP_getE hlt]; exact hv

/-- A `[cv, nF]` record at `p` denoting `x`, its pool reads in `P`, its constant below `EREC`'s top. -/
def CNOk (m : Mem) (p : Nat) (x : IConstantVal × Nat) (P : Nat → Prop) : Prop :=
  P p ∧ P (p + 1) ∧ ∃ q, iwN m p = some q ∧ decCV (erecP m) q = some x.1 ∧ iwN m (p + 1) = some x.2

theorem CNOk.agree {m m' : Mem} {p : Nat} {x : IConstantVal × Nat} {P : Nat → Prop} (h : CNOk m p x P)
    (hR : RdS m m' P) (hE : ArrExt (erecP m) (erecP m')) : CNOk m' p x P := by
  obtain ⟨h0, h1, q, hq, hcv, hn⟩ := h
  exact ⟨h0, h1, q, by rw [iwN_agree hR h0]; exact hq, hE.decCV hcv, by rw [iwN_agree hR h1]; exact hn⟩

theorem CNOk.mono {m : Mem} {p : Nat} {x : IConstantVal × Nat} {P Q : Nat → Prop} (h : CNOk m p x P)
    (hq : ∀ i, P i → Q i) : CNOk m p x Q := ⟨hq _ h.1, hq _ h.2.1, h.2.2⟩

theorem CNOk.dec {m : Mem} {p : Nat} {x : IConstantVal × Nat} {P : Nat → Prop} (h : CNOk m p x P) :
    decCN m p = some x := by
  obtain ⟨-, -, q, hq, hcv, hn⟩ := h
  have : decCVp m q = some x.1 := (erecP_ext m).decCV hcv
  simp [decCN, hq, this, hn]

/-- The pointers at `o, o + 1, …` are `[cv, nF]` records denoting `xs`. -/
def CsAt (m : Mem) (o : Nat) (xs : List (IConstantVal × Nat)) (P : Nat → Prop) : Prop :=
  ∀ i (hi : i < xs.length), ∃ w : Word, (m.arr64 IW)[o + i]? = some w ∧ CNOk m w.toNat xs[i] P

theorem CsAt.decPL {m : Mem} {o : Nat} {xs : List (IConstantVal × Nat)} {P : Nat → Prop}
    (h : CsAt m o xs P) : decPL m (decCN m) o xs.length = some xs :=
  decPL_of_get _ xs o fun j hj => by
    obtain ⟨w, hw, hc⟩ := h j hj
    exact ⟨w.toNat, by simp [iwN, nat?, iwA, hw], hc.dec⟩

/-- The constructor records of the environment have parameter and field counts that sum below
`2^64` (`nest_ctor_entry` adds them as words). -/
def CtorSums (fe : IFEnv) : Prop :=
  ∀ n cv nPc nF, fe.find? n = some (.ctorInfo cv nPc nF) → nPc + nF < 2 ^ 64

/-- The twin's per-name step of `nestContainer`'s `filterMapM`. -/
def ncF (fe : IFEnv) (C : NIdx) (n : NIdx) : AM (Option (IConstantVal × Nat × Nat)) :=
  match fe.find? n with
  | some ci => ConRon.Arena.nestCtorEntry C ci
  | none => pure none

def ncProj (c : IConstantVal × Nat × Nat) : IConstantVal × Nat := (c.1, c.2.2)


theorem decCI_idx {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {ci : IConstantInfo}
    (h : decCI a dn p = some ci) : p < a.size := by
  simp only [decCI, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, -⟩ := h
  exact nat?_idx hk

theorem erecP_size_le (m : Mem) : (erecP m).size ≤ erTop m := by
  simp only [erecP, Array.size_extract, erecTop, erTop]; omega

theorem GrowX.erecP {q n : Nat} {m m' : Mem} (h : GrowX q n m m') : ArrExt (erecP m) (erecP m') :=
  erecP_ext_of h.2.1 h.2.2.2

theorem nestCtorEntry_some {C : NIdx} {cv : IConstantVal} {nPc nF : Nat} {a a' : AState}
    {x : IConstantVal × Nat × Nat}
    (h : (ConRon.Arena.nestCtorEntry C (.ctorInfo cv nPc nF)).run a = .ok (some x, a')) :
    x = (cv, nPc, nF) := by
  simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind] at h
  cases h1 : (stripPis (nPc + nF) cv.type).run a with
  | error e => rw [h1] at h; contradiction
  | ok p =>
    obtain ⟨o, a1⟩ := p
    rw [h1] at h
    simp only [except_ok_bind] at h
    cases o with
    | none => exact absurd h (by simp [StateT.run, StateT.pure, pure, Except.pure])
    | some q =>
      simp only [StateT.run_bind] at h
      cases h2 : (getAppFn coreWalkFuel q.2).run a1 with
      | error e => rw [h2] at h; contradiction
      | ok p2 =>
        obtain ⟨hd, a2⟩ := p2
        rw [h2] at h
        simp only [except_ok_bind] at h
        split at h
        · simp only [StateT.run_bind] at h
          cases h3 : (viewConst hd).run a2 with
          | error e => rw [h3] at h; contradiction
          | ok p3 =>
            obtain ⟨o3, a3⟩ := p3
            rw [h3] at h
            simp only [except_ok_bind] at h
            cases o3 with
            | none =>
              simp only [failDanglingE] at h
              exact absurd h (by
                simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift,
                  Except.bind, bind, ExceptT.lift, throw])
            | some nu =>
              obtain ⟨n0, u0⟩ := nu
              simp only at h
              split at h
              · simp only [StateT.run, StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
                  Option.some.injEq] at h
                exact h.1.symm
              · exact absurd h (by simp [StateT.run, StateT.pure, pure, Except.pure])
        · exact absurd h (by simp [StateT.run, StateT.pure, pure, Except.pure])

theorem CsAt.agree {m m' : Mem} {o : Nat} {xs : List (IConstantVal × Nat)} {P : Nat → Prop}
    (h : CsAt m o xs P) (hR : RdS m m' P) (hE : ArrExt (erecP m) (erecP m'))
    (hw : ∀ i < xs.length, (m'.arr64 IW)[o + i]? = (m.arr64 IW)[o + i]?) : CsAt m' o xs P :=
  fun i hi => let ⟨w, h1, h2⟩ := h i hi; ⟨w, by rw [hw i hi]; exact h1, h2.agree hR hE⟩

theorem CsAt.mono {m : Mem} {o : Nat} {xs : List (IConstantVal × Nat)} {P Q : Nat → Prop}
    (h : CsAt m o xs P) (hq : ∀ i, P i → Q i) : CsAt m o xs Q :=
  fun i hi => let ⟨w, h1, h2⟩ := h i hi; ⟨w, h1, h2.mono hq⟩

theorem ncGoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis C cs : Word) (N : Nat)
    (hC : H C) (hcs : CtorSums fe) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (co cl ol fp : Word) (ns : List NIdx)
      (acc : List (IConstantVal × Nat × Nat)) (r : List Word),
    ncGoW k m vis C co cl cs ol fp = some (r, m') → StageR dn vis fe m a →
    hslice? (erecP m) co.toNat cl.toNat = some ns → cs.toNat + N ≤ iwTop m →
    ol.toNat = acc.length → acc.length + cl.toNat ≤ N →
    CsAt m cs.toNat (acc.map ncProj) (OutR cs.toNat N (iwTop m)) →
    fp.toNat = (acc.head?.map (·.2.1)).getD 0 →
    ∃ ys a', (ns.filterMapM (ncF fe (decI C))).run a = .ok (ys, a') ∧ StageR dn vis fe m' a' ∧
      GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ys.length ∧
      CsAt m' cs.toNat ((acc ++ ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
      (r.tail.headD 0).toNat = ((acc ++ ys).head?.map (·.2.1)).getD 0 := by
  induction k with
  | zero => intro m m' a co cl ol fp ns acc r h; simp [ncGoW] at h
  | succ k ih =>
    intro m m' a co cl ol fp ns acc r h hS hns hreg hol hN hacc hfp
    have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
    by_cases hc0 : cl = 0
    · rw [ncGoW_done k m vis C co cl cs ol fp hc0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hc0
      have : ns = [] := by simpa [hslice?] using hns.symm
      subst this
      refine ⟨[], a, rfl, hS, GrowX.of_grow (IWGrow.refl _), by simp [hol], by simpa using hacc,
        by simpa using hfp⟩
    rw [ncGoW_step k m vis C co cl cs ol fp hc0] at h
    have hcl : cl.toNat ≠ 0 := fun e => hc0 (UInt64.toNat_inj.mp (by simpa using e))
    have hcl1 : (cl - 1).toNat = cl.toNat - 1 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
    -- the name
    obtain ⟨cl', hcl'⟩ : ∃ c', cl.toNat = c' + 1 := ⟨cl.toNat - 1, by omega⟩
    rw [hcl', hslice?_succ] at hns
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hns
    obtain ⟨n, hn, ns', hns', rfl⟩ := hns
    obtain ⟨w, hw, hwH, rfl⟩ := hd?_some hn
    have hwE : rdW (m.arr64 EREC) co = w := by simp [rdW, erecP_get hw]
    have hco : co.toNat < erTop m := by
      have := (Array.getElem?_eq_some_iff.mp hw).1; have := erecP_size_le m; omega
    have hco1 : (co + 1).toNat = co.toNat + 1 :=
      word_add_toNat (show co.toNat + 1 < 2 ^ 64 by have := hS.2.2.1; have := hS.2.2.2.2.1; omega)
    rw [hwE] at h
    have hE := hS.1.env
    rw [List.filterMapM_cons]
    cases hef : envFindW m w vis with
    | none => rw [hef] at h; simp [ncK1] at h
    | some pr =>
    obtain ⟨r1, m1⟩ := pr
    rw [hef] at h
    have hm1 := envFindW_mem hef
    rw [hm1] at h hef
    by_cases hf0 : r1.headD 0 = 0
    · -- not found
      rw [ncK1_miss (h := hf0)] at h
      obtain ⟨-, hfind⟩ := envFindW_miss hef hE hwH hf0
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3⟩ := ih m m' a (co + 1) (cl - 1) ol fp ns' acc r h hS
        (by rw [hco1, hcl1]; simpa [hcl'] using hns') hreg hol (by omega) hacc hfp
      refine ⟨ys, a', ?_, hS', hGX, h1, h2, h3⟩
      simp only [ncF, hfind, StateT.run_bind]
      exact hrun
    rw [ncK1_hit (h := hf0)] at h
    obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hwH hf0
    rw [hci] at hfind
    generalize r1.tail.headD 0 = ciq at h hfind hci
    have hsum : ∀ cv nPc nF, ci = .ctorInfo cv nPc nF → nPc + nF < 2 ^ 64 := fun cv nPc nF e =>
      hcs _ cv nPc nF (by rw [hfind, e])
    cases hent : entryW m C ciq with
    | none => rw [hent] at h; simp [ncK2] at h
    | some pr2 =>
    obtain ⟨r2, m2⟩ := pr2
    rw [hent] at h
    obtain ⟨x, a1, hrun1, hS2, hg2, hout⟩ := entryW_ok hC hent hS hci hsum
    have hE2 : ArrExt (erecP m) (erecP m2) := (GrowX.of_grow (q := 0) (n := 0) hg2).erecP
    have hstep : ncF fe (decI C) (decI w) = ConRon.Arena.nestCtorEntry (decI C) ci := by
      simp only [ncF, hfind]
    rw [hstep]
    have hlen : (acc.map ncProj).length = acc.length := List.length_map ..
    cases x with
    | none =>
      have hr2 : r2 = [0, 0, 0, 0] := hout
      subst hr2
      rw [ncK2_miss (h := rfl)] at h
      have hacc2 : CsAt m2 cs.toNat (acc.map ncProj) (OutR cs.toNat N (iwTop m)) :=
        hacc.agree ((RdS.of_grow hg2).mono fun _ hi => hi.1) hE2
          (fun i hi => hg2.2.2.1 _ (by rw [hlen] at hi; omega))
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3⟩ := ih m2 m' a1 (co + 1) (cl - 1) ol fp ns' acc r h hS2
        (by rw [hco1, hcl1, show cl.toNat - 1 = cl' by omega]; exact hE2.hslice? hns')
        (by have := hg2.1; omega) hol (by omega)
        (hacc2.mono fun _ hx => ⟨Nat.lt_of_lt_of_le hx.1 hg2.1, hx.2⟩) hfp
      refine ⟨ys, a', ?_, hS', (GrowX.of_grow hg2).trans hGX, h1, h2, h3⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind]
      exact hrun
    | some c =>
      obtain ⟨cv, nPc, nF⟩ := c
      obtain ⟨hr2, -⟩ := hout
      subst hr2
      rw [ncK2_hit (h := by simp)] at h
      simp only [List.tail_cons, List.headD_cons] at h
      have hci' : ci = .ctorInfo cv nPc nF := by
        cases ci with
        | ctorInfo cv' nPc' nF' =>
          have := nestCtorEntry_some hrun1
          simp only [Prod.mk.injEq] at this
          obtain ⟨rfl, rfl, rfl⟩ := this; rfl
        | _ => exact absurd hrun1 (by simp [ConRon.Arena.nestCtorEntry, StateT.run, StateT.pure, pure, Except.pure])
      subst hci'
      have hs := hsum cv nPc nF rfl
      have hcvE : decCV (erecP m) (ciq.toNat + 1) = some cv := decCI_ctor_cv hci
      have hciqb : ciq.toNat < erTop m := by
        have := decCI_idx hci; have := erecP_size_le m; omega
      have hciq1 : (ciq + 1).toNat = ciq.toNat + 1 :=
        word_add_toNat (show ciq.toNat + 1 < 2 ^ 64 by have := hS.2.2.1; have := hS.2.2.2.2.1; omega)
      have hU : UInt64.size = 2 ^ 64 := rfl
      have hnF : (UInt64.ofNat nF).toNat = nF := UInt64.toNat_ofNat_of_lt' (by omega)
      have hnPc : (UInt64.ofNat nPc).toNat = nPc := UInt64.toNat_ofNat_of_lt' (by omega)
      have htopb : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hsz
      cases hrec : posRecW m2 [ciq + 1, UInt64.ofNat nF] with
      | none => rw [hrec] at h; simp [ncK3] at h
      | some pr3 =>
      obtain ⟨q3, m3⟩ := pr3
      rw [hrec] at h
      obtain ⟨hS3, hg3, hq3, ht3, hget3⟩ := posRecW_stage hrec hS2 (by simp)
      simp only [List.length_cons, List.length_nil] at ht3
      have hcol : (cs + ol).toNat = cs.toNat + ol.toNat := word_add_toNat (by omega)
      have hS4 := hS3.set_iw (cs + ol) q3
      have hg23 := hg2.trans hg3
      have hGX4 : GrowX cs.toNat N m (m3.set64 IW (cs + ol) q3) :=
        (GrowX.of_grow hg23).trans (GrowX.set m3 _ _ (by omega))
      have hE4 : ArrExt (erecP m) (erecP (m3.set64 IW (cs + ol) q3)) := hGX4.erecP
      have ht4 : iwTop (m3.set64 IW (cs + ol) q3) = iwTop m3 := by
        simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
      have hsz3 : cs.toNat + ol.toNat < (m3.arr64 IW).size := by
        have := hS3.2.1; have := hg23.1; omega
      have hnew : CNOk (m3.set64 IW (cs + ol) q3) q3.toNat (cv, nF)
          (OutR cs.toNat N (iwTop (m3.set64 IW (cs + ol) q3))) := by
        have hg2' := hg2.1
        refine ⟨⟨by rw [ht4]; omega, Or.inr (by omega)⟩, ⟨by rw [ht4]; omega, Or.inr (by omega)⟩,
          (ciq + 1).toNat, ?_, by rw [hciq1]; exact hE4.decCV hcvE, ?_⟩
        · have := hget3 0 (by simp)
          simp only [iwN, nat?, iwA, set64IW_get]
          rw [if_neg (by omega)]; simp at this; simp [this]
        · have := hget3 1 (by simp)
          simp only [iwN, nat?, iwA, set64IW_get]
          rw [if_neg (by omega)]; simp at this; simp [this, hnF]
      have hacc4 : CsAt (m3.set64 IW (cs + ol) q3) cs.toNat
          ((acc ++ [(cv, nPc, nF)]).map ncProj) (OutR cs.toNat N (iwTop (m3.set64 IW (cs + ol) q3))) := by
        intro i hi
        simp only [List.map_append, List.length_append, List.length_map, List.map_cons, List.map_nil,
          List.length_cons, List.length_nil] at hi
        by_cases hia : i < acc.length
        · obtain ⟨w', hw1, hw2⟩ := hacc i (by rw [hlen]; exact hia)
          refine ⟨w', ?_, ?_⟩
          · rw [set64IW_get, if_neg (by omega), hg23.2.2.1 _ (by omega)]; exact hw1
          · simp only [List.map_append, List.map_cons, List.map_nil]
            rw [List.getElem_append_left (by rw [hlen]; exact hia)]
            exact (hw2.agree hGX4.2.2.1 hE4).mono fun _ hx =>
              ⟨Nat.lt_of_lt_of_le hx.1 (by rw [ht4]; exact hg23.1), hx.2⟩
        · have hie : i = acc.length := by omega
          subst hie
          refine ⟨q3, ?_, ?_⟩
          · rw [set64IW_get, if_pos ⟨by omega, by omega⟩]
          · simp only [List.map_append, List.map_cons, List.map_nil]
            rw [List.getElem_append_right (by rw [hlen]; exact Nat.le_refl _)]
            simp only [hlen, Nat.sub_self, List.getElem_cons_zero, ncProj]
            exact hnew
      have hol1 : (ol + 1).toNat = acc.length + 1 := by
        rw [word_add_toNat (show ol.toNat + (1 : Word).toNat < 2 ^ 64 by simp; omega)]; simp [hol]
      have hrest : ∀ fp' : Word, fp'.toNat = ((acc ++ [(cv, nPc, nF)]).head?.map (·.2.1)).getD 0 →
          ncGoW k (m3.set64 IW (cs + ol) q3) vis C (co + 1) (cl - 1) cs (ol + 1) fp' = some (r, m') →
          ∃ ys a', (List.filterMapM (ncF fe (decI C)) ns').run a1 = .ok (ys, a') ∧ StageR dn vis fe m' a' ∧
            GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ((cv, nPc, nF) :: ys).length ∧
            CsAt m' cs.toNat ((acc ++ (cv, nPc, nF) :: ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
            (r.tail.headD 0).toNat = ((acc ++ (cv, nPc, nF) :: ys).head?.map (·.2.1)).getD 0 := by
        intro fp' hfp' h'
        obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3⟩ := ih _ m' a1 (co + 1) (cl - 1) (ol + 1) fp' ns'
          (acc ++ [(cv, nPc, nF)]) r h' hS4
          (by rw [hco1, hcl1, show cl.toNat - 1 = cl' by omega]; exact hE4.hslice? hns')
          (by rw [ht4]; have := hg23.1; omega) (by rw [hol1]; simp) (by simp; omega) hacc4 hfp'
        refine ⟨ys, a', hrun, hS', hGX4.trans hGX, by rw [h1]; simp; omega, ?_, ?_⟩
        · simpa using h2
        · simpa using h3
      obtain ⟨ys, a', hrun, hS', hGX, h1, h2, h3⟩ : ∃ ys a', (List.filterMapM (ncF fe (decI C)) ns').run a1 =
          .ok (ys, a') ∧ StageR dn vis fe m' a' ∧
            GrowX cs.toNat N m m' ∧ (r.headD 0).toNat = acc.length + ((cv, nPc, nF) :: ys).length ∧
            CsAt m' cs.toNat ((acc ++ (cv, nPc, nF) :: ys).map ncProj) (OutR cs.toNat N (iwTop m')) ∧
            (r.tail.headD 0).toNat = ((acc ++ (cv, nPc, nF) :: ys).head?.map (·.2.1)).getD 0 := by
        by_cases h0 : ol = 0
        · rw [ncK3_first (h := h0)] at h
          have : acc = [] := List.eq_nil_of_length_eq_zero (by rw [← hol, h0]; rfl)
          subst this
          exact hrest _ (by simp [hnPc]) h
        · rw [ncK3_next (h := h0)] at h
          have hne : acc ≠ [] := fun e => h0 (UInt64.toNat_inj.mp (by rw [hol, e]; rfl))
          obtain ⟨c0, acc', rfl⟩ := List.exists_cons_of_ne_nil hne
          exact hrest _ (by simpa using hfp) h
      refine ⟨(cv, nPc, nF) :: ys, a', ?_, hS', hGX, h1, h2, h3⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, hrun, StateT.run_pure]
      rfl

end L.Ind
