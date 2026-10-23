import ConAgua.Arena.IndT.Base
import ConAgua.Arena.StageC
import ConAgua.Arena.IndRealAbs
import ConRon.Bridge.Inductives.Rel

/-!
# Lifting stage facts to `StageC` by con-ron's specs (lane `indstaget`)

`StageC dn vis fe env m a` (`TwinStep.lean`) is `StageR` with con-ron's `CheckOK .verified env fe a`,
the memory's half of `TwinOK` (`TwinMem`) and the pin flag. A stage theorem proved under `StageR`
for a callee that calls no core entry point lifts to `StageC` by con-ron's spec of the twin
(`PSpec`/`PSpecP`/`PSpecL`, `Bridge/Inductives/Run.lean`: from `StateOK` and the inputs'
denotations, the twin's run is a `PStep`, which with `CheckOK` before is a `CoreStep`) and the
L run's memory facts (array sizes kept, `CoreMemos` after, the pin flag kept).
-/

set_option linter.deprecated false

open ConRon.Arena
open ConRon.Bridge.Inductives (PStep PSpec PSpecP PSpecL)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section lift
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- The memory facts a callee's L run owes `StageC`: the arrays' sizes, the core memos after,
the pin table. -/
structure MemKeep (m m' : Mem) : Prop where
  size : ∀ b, (m'.arr64 b).size = (m.arr64 b).size
  memos : CoreMemos m'
  pins : m'.arr64 PINS = m.arr64 PINS

/-- `MemKeep` from a frame that leaves the core memos and the pins alone. -/
theorem MemKeep.of_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hM : CoreMemos m) (hP : PINS ∉ A) (hA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A)
    (hC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C)
    (hWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A)
    (hWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C)
    (hLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A)
    (hLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C) : MemKeep m m' :=
  ⟨fun _ => hf.2.2.1 _ ▸ rfl, hM.frame hf hA hC hWA hWC hLA hLC, hf.1 PINS hP (by decide)⟩

/-- **`StageC` across a twin step con-ron calls a `PStep`**: the stage relation after it, the
memory facts. -/
theorem StageC.of_pstep {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hk : MemKeep m m') (hs : PStep a a') :
    StageC dn vis fe env m' a' :=
  ⟨hS, (hs.toCore h.check).ok,
    ⟨by rw [hk.size]; exact h.mem.erec, by rw [hk.size]; exact h.mem.spn,
      by rw [hk.size]; exact h.mem.bstk, hk.memos,
      fun k x e => hs.ext.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    by simp only [pinW, hk.pins]; exact h.flag⟩

/-- **A `StageR` `RSim` of a core-free callee is a `StageC` `RSim`**, by con-ron's `PSpec` of the
twin at the inputs' denotation `P` and the L run's memory facts. -/
theorem RSim.liftP {β α : Type} {o : Option (β × Mem)} {op : AM α} {m : Mem} {a : AState}
    {Q : β × Mem → AState → α → Prop} {P : EStore → Prop} {R : EStore → α → Prop}
    (hC : StageC dn vis fe env m a)
    (h : RSim o op a (fun b a' x => StageR dn vis fe b.2 a' ∧ Q b a' x))
    (hsp : PSpec P op R) (hP : P a.store) (hk : ∀ b, o = some b → MemKeep m b.2) :
    RSim o op a (fun b a' x => StageC dn vis fe env b.2 a' ∧ Q b a' x ∧ R a'.store x ∧
      PStep a a') := by
  intro b hb
  obtain ⟨x, a', hr, hS, hq⟩ := h b hb
  obtain ⟨hs, hR⟩ := hsp a a' x hC.check.state hP hr
  exact ⟨x, a', hr, hC.of_pstep hS (hk b hb) hs, hq, hR, hs⟩

/-- `RSim.liftP` for a `PSpecP` (the twin reads the pins). -/
theorem RSim.liftPP {β α : Type} {o : Option (β × Mem)} {op : AM α} {m : Mem} {a : AState}
    {Q : β × Mem → AState → α → Prop} {P : EStore → Prop} {R : EStore → α → Prop}
    (hC : StageC dn vis fe env m a)
    (h : RSim o op a (fun b a' x => StageR dn vis fe b.2 a' ∧ Q b a' x))
    (hsp : PSpecP P op R) (hP : P a.store) (hk : ∀ b, o = some b → MemKeep m b.2) :
    RSim o op a (fun b a' x => StageC dn vis fe env b.2 a' ∧ Q b a' x ∧ R a'.store x ∧
      PStep a a') := by
  intro b hb
  obtain ⟨x, a', hr, hS, hq⟩ := h b hb
  obtain ⟨hs, hR⟩ := hsp a a' x hC.check.state hC.check.pins hP hr
  exact ⟨x, a', hr, hC.of_pstep hS (hk b hb) hs, hq, hR, hs⟩

/-- `RSim.liftP` for a `PSpecL` (the twin reads levels back through the cache). -/
theorem RSim.liftPL {β α : Type} {o : Option (β × Mem)} {op : AM α} {m : Mem} {a : AState}
    {Q : β × Mem → AState → α → Prop} {P : EStore → Prop} {R : EStore → α → Prop}
    (hC : StageC dn vis fe env m a)
    (h : RSim o op a (fun b a' x => StageR dn vis fe b.2 a' ∧ Q b a' x))
    (hsp : PSpecL P op R) (hP : P a.store) (hk : ∀ b, o = some b → MemKeep m b.2) :
    RSim o op a (fun b a' x => StageC dn vis fe env b.2 a' ∧ Q b a' x ∧ R a'.store x ∧
      PStep a a') := by
  intro b hb
  obtain ⟨x, a', hr, hS, hq⟩ := h b hb
  obtain ⟨hs, hR⟩ := hsp a a' x hC.check.state hC.check.caches.readL hP hr
  exact ⟨x, a', hr, hC.of_pstep hS (hk b hb) hs, hq, hR, hs⟩

end lift

/-! ## The memory facts of a model run (`KFr`)

`StageC` asks of a callee's L run the arrays' sizes, the pin table and `CoreMemos` after
(`MemKeep`). Of `CoreMemos` the stage's theorems thread two parts already (`AbsOK`'s `AbMemo`,
`IlMemo`: arrays 49, 50); the rest is `WalkMemos` (arrays 151‥153, 52‥54). `KFr m m'` is the
frame fact of a model run for the rest, proved per model as lane `indproofs4`'s `AFr`
(`kfr_auto`). -/

/-- The memory facts of a model run beside `AbsOK`: sizes, pins, `WalkMemos`. -/
def KFr (m m' : Mem) : Prop :=
  (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.arr64 PINS = m.arr64 PINS ∧
    (WalkMemos m → WalkMemos m')

theorem KFr.refl (m : Mem) : KFr m m := ⟨fun _ => rfl, rfl, id⟩

theorem KFr.trans {m₁ m₂ m₃ : Mem} (h₁ : KFr m₁ m₂) (h₂ : KFr m₂ m₃) : KFr m₁ m₃ :=
  ⟨fun b => by rw [h₂.1, h₁.1], by rw [h₂.2.1, h₁.2.1], h₂.2.2 ∘ h₁.2.2⟩

/-- The arrays `KFr` reads (the pins, the walk memos). -/
def kfrFreeA (A : List ArrId) : Bool :=
  A.all fun b => b != PINS && b != 151 && b != 152 && b != 153 && b != 52 && b != 53 && b != 54

/-- The `CTL` words `KFr` reads (the walk memos' epochs). -/
def kfrFreeC (C : List Word) : Bool :=
  C.all fun x => x != 152 && x != 154 && x != 156 && x != 54 && x != 56 && x != 58

/-- A writer apart from the pins and the walk memos. -/
theorem KFr.of_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hA : kfrFreeA A = true := by decide) (hC : kfrFreeC C = true := by decide) : KFr m m' := by
  simp only [kfrFreeA, kfrFreeC, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hA hC
  have nA : ∀ b : ArrId, (b = PINS ∨ b = 151 ∨ b = 152 ∨ b = 153 ∨ b = 52 ∨ b = 53 ∨ b = 54) →
      b ∉ A := fun b hb hm => by
        have := hA b hm
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [PINS]
  have nC : ∀ x : Word, (x = 152 ∨ x = 154 ∨ x = 156 ∨ x = 54 ∨ x = 56 ∨ x = 58) → x ∉ C :=
    fun x hx hm => by
      have := hC x hm
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  refine ⟨hf.2.2.1, hf.1 PINS (nA _ (.inl rfl)) (by decide), fun h => h.frame hf
    ⟨nA _ (by simp), nA _ (by simp), nA _ (by simp)⟩ ⟨nC _ (by simp), nC _ (by simp), nC _ (by simp)⟩
    ⟨nA _ (by simp), nA _ (by simp), nA _ (by simp)⟩ ⟨nC _ (by simp), nC _ (by simp), nC _ (by simp)⟩⟩

theorem KFr.set64 (m : Mem) (a : ArrId) (ha : a ≠ CTL) (hk : kfrFreeA [a] = true) (k v : Word) :
    KFr m (m.set64 a k v) := KFr.of_frame (MemFrame.set64 m a ha k v) hk rfl

theorem KFr.setCtl (m : Mem) (c : Word) (hk : kfrFreeC [c] = true) (v : Word) :
    KFr m (m.set64 CTL c v) := KFr.of_frame (MemFrame.setCtl m c v) rfl hk

/-- `kfr_set`: `KFr m m'` for `m'` a chain of writes of `m` apart from the pins and walk memos. -/
macro "kfr_set" : tactic => `(tactic|
  repeat (first
    | with_reducible refine KFr.trans ?_ (KFr.set64 _ _ (by decide) (by decide) _ _)
    | with_reducible refine KFr.trans ?_ (KFr.setCtl _ _ (by decide) _)
    | with_reducible exact KFr.refl _))

syntax "kfr_auto" ident "[" term,* "]" : tactic
macro_rules
  | `(tactic| kfr_auto $h [$ts,*]) => `(tactic|
    repeat' (first
      | with_reducible exact KFr.refl _
      | (simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident; rw [← ($h).2]
         first | with_reducible exact KFr.refl _ | (kfr_set; done))
      | (simp only [Option.some.injEq] at $h:ident; subst $h:ident; exact KFr.refl _)
      | (simp only [reduceCtorEq] at $h:ident; done)
      | (first $[| refine KFr.trans ($ts (by with_reducible assumption)) ?_]*)
      | split at $h:ident))

/-- `MemKeep` from a model run's `KFr`, the walk memos it threads (`AbsOK` after) and `CoreMemos`
before. -/
theorem MemKeep.of_kfr {m m' : Mem} (hk : KFr m m') (hA : AbsOK m') (hM : CoreMemos m) :
    MemKeep m m' :=
  ⟨hk.1, ⟨hA.2.2.2, hA.1, hk.2.2 hM.2.2⟩, hk.2.1⟩

end L.Ind
