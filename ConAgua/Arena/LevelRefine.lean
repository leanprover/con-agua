import ConAgua.Arena.StoreLib
import ConAgua.Arena.LevelStore
import ConAgua.Arena.LpColRel

/-!
# The level `succ` store refines the arena's `succ` tables

The third table on the store library (`StoreLib.lean`), written fresh: the record
`SuccNode { u : LIdx }` of the level store (`ConAgua/Arena/LevelStore.lean` has the L code). The
schema `succSch` (`SREC`, `SSLOT`, one word per node, counts at `CTL[6 + t]`, tag `1`), the
record relation `SRecRel` (the word is the child's handle word), the node hash `shash`, the lens
`succLens` on the level store's two `succ` tables (`a.store.lss.ls`). `SuccR m a` is the
library's `StoreR` for them. `internSucc_refines`: `intern_succ(u)` refines
`internLNode (.succ (decI u))` under `SuccR`.

Not represented: the derived column (`LStore.derOfView`, through `mixHash`) and every other
table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `succ` cons key. -/
abbrev succKey (u : LIdx) : SuccNode := ⟨u⟩

/-- `a` with the scratch / persistent `succ` table of the level store replaced. -/
def withScrSuccs (a : AState) (t : Tbl SuccNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      scr := { a.store.lss.ls.scr with succs := t } } } } }
def withPersSuccs (a : AState) (t : Tbl SuccNode LIdx LDer) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with
      pers := { a.store.lss.ls.pers with succs := t } } } } }

/-- The level store's two `succ` tables. -/
def succLens : Lens SuccNode LDer .level where
  on a := a.store.lss.ls.scratchOn
  getP a := a.store.lss.ls.pers.succs
  getS a := a.store.lss.ls.scr.succs
  setP := withPersSuccs
  setS := withScrSuccs
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internLNode` at a `succ` node is the library's protocol, with no skip. -/
theorem internLNode_succ_run (u : LIdx) (a : AState) :
    (internLNode (.succ u)).run a =
      protoRun succLens (succKey u) LTag.succ a.store.lss.ls.pers.succs.cons[succKey u]?
        (a.store.lss.ls.derOfView (.succ u)) (.native "arena: level constructor array full") a := by
  simp only [internLNode, LStore.find?, LTables.find?, Tbl.find?, LTables.sizeOf, EStore.ls,
    EStore.internLevel, LsStore.internLevel, LStore.intern, LTables.push]
  cases hp : a.store.lss.ls.pers.succs.cons[succKey u]? <;> cases hs : a.store.lss.ls.scratchOn <;>
    cases hc : a.store.lss.ls.scr.succs.cons[succKey u]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, succKey, ite_self, protoRun, succLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrSuccs, withPersSuccs, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `succ` tables -/

/-- The `succ` schema: `SREC`, `SSLOT`, one word per node, the counts at `CTL[6 + t]`. -/
def succSch : Schema := ⟨SREC, SSLOT, 1, 2, 6, LTag.succ⟩

theorem succSch_wf : succSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_succ0 (m : Mem) (t i : Word) : fld succSch m t i 0 = rdW (m.arr64 SREC) (i * 2 + t) := by
  simp [fld, Schema.ad, succSch]

/-- Node `i` of tier `t` holds `succ k.u`: its word is the child's handle word. -/
def SRecRel (m : Mem) (t i : Word) (k : SuccNode) : Prop :=
  rdW (m.arr64 SREC) (i * 2 + t) = k.u.word.toUInt64

/-- **The state relation** of the `succ` store: the library's relation for the level store's two
`succ` tables. -/
def SuccR (m : Mem) (a : AState) : Prop :=
  StoreR succSch SRecRel shash m a.store.lss.ls.scratchOn a.store.lss.ls.pers.succs
    a.store.lss.ls.scr.succs

/-- A node's relation and hash depend only on its word. -/
theorem succFrame : RFrame succSch SRecRel shash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_succ0, fld_succ0] at h0
  exact ⟨fun a h => by simpa only [SRecRel, h0] using h, by simp only [shash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `succ_find` on node `i` of tier `t`. -/
def sMt (m : Mem) (u t i : Word) : Bool := smatchW (m.arr64 SREC) t i u

section query
variable (m : Mem) (u : Word) (hu : u.toNat < 2 ^ 32)

include hu in
/-- **Matching is equality of `succ` nodes.** -/
theorem succMatchOK : MatchOK SRecRel (sMt m u) m (succKey (decI u)) := by
  intro t i k hr
  have := word_decI k.u u hu
  obtain ⟨ku⟩ := k
  grind [sMt, smatchW, SRecRel]

theorem succHomeOK : HomeOK shash (sMt m u) m (succHashW u) := by
  intro t i hm
  simp only [sMt, smatchW, beq_iff_eq] at hm
  simp only [shash, hm]

include hu in
/-- The record `succ_push` writes holds the node. -/
theorem succNewOK : NewOK succSch SRecRel shash m [u] (succKey (decI u)) (succHashW u) := by
  intro t j ht hroom
  have e : fld succSch (pushG succSch m t [u] j (cntW succSch m t)) t (cntW succSch m t) 0 = u := by
    have := hroom.1
    have := hroom.2
    rw [fld_pushG succSch succSch_wf] <;> simp only [succSch, Schema.ad] at * <;> grind
  rw [fld_succ0] at e
  have := word_decI (decI u : LIdx) u hu
  simp only [SRecRel, shash, succKey, e]
  grind

end query

/-! ## The bridges from the L models -/

theorem sprobeW_arm (m : Mem) (u t : Word) :
    ∀ j d, sprobeW (m.arr64 SSLOT) (m.arr64 SREC) t u (baseW m t) (nSlotsS m) j d =
      probeArm succSch m t (sMt m u t) (sprobeW (m.arr64 SSLOT) (m.arr64 SREC) t u (baseW m t) (nSlotsS m)) j d := by
  intro j d; rw [sprobeW]; rfl

theorem spushOK_room (m : Mem) (t : Word) (h : spushOK m t = true) : PushRoom succSch m t := by
  simp only [spushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 SREC) 1
  simp only [PushRoom, cntW, scnt, succSch, len64_eq] at *
  grind

theorem spushMem_eq (m : Mem) (t u j c : Word) :
    spushMem m t u j c = (pushG succSch m t [u] j c).set64 SHP (c * 2 + t) (lvlHPW m u) := by
  simp [spushMem, pushG, wrRec, Schema.ad, succSch]

theorem sinternW_eq (m : Mem) (u : Word) :
    sinternW m u = internMD succSch SHP (lvlHPW m u) m 0 (spushOK m) [u]
      (sprobeW (m.arr64 SSLOT) (m.arr64 SREC) 0 u (baseW m 0) (nSlotsS m) (homeW (succHashW u) (nSlotsS m)) 0)
      (sprobeW (m.arr64 SSLOT) (m.arr64 SREC) 1 u (baseW m 1) (nSlotsS m) (homeW (succHashW u) (nSlotsS m)) 0)
      shash := by
  have e0 : ∀ x, hdW succSch.tag.toUInt64 0 x = succP + x := fun x => by
    simp [hdW, succSch, succP, LTag.succ]
  have e1 : ∀ x, hdW succSch.tag.toUInt64 1 x = succS + x := fun x => by
    simp [hdW, succSch, succS, LTag.succ]
  simp only [sinternW, internMD, spushMem_eq, e0, e1, true_and]
  rfl

/-- **What `intern_succ` changes**: the table's arrays, the column, the counts. -/
theorem sinternW_frame (m : Mem) (u : Word) (w : Word) (m' : Mem) (hI : sinternW m u = some (w, m')) :
    MemFrame [SREC, SSLOT, SHP] [6, 7] m m' := by
  rw [sinternW_eq] at hI
  exact internMD_frame succSch succSch_wf SHP (by decide) _ _ _ _ _ _ _ _ _ hI

/-- `intern_succ`'s model as the library's interning and the `mk_*` tail (`mkK`), given the count
words. -/
theorem sinternW_eqK (m : Mem) (u : Word) (hctl : succSch.ca.toNat + 2 ≤ (m.arr64 CTL).size) :
    sinternW m u = mkK SHP succSch.ca (cnt2 m succSch.ca) (lvlHPW m u)
      (internM succSch m 0 (spushOK m) [u]
      (sprobeW (m.arr64 SSLOT) (m.arr64 SREC) 0 u (baseW m 0) (nSlotsS m) (homeW (succHashW u) (nSlotsS m)) 0)
      (sprobeW (m.arr64 SSLOT) (m.arr64 SREC) 1 u (baseW m 1) (nSlotsS m) (homeW (succHashW u) (nSlotsS m)) 0) shash) := by
  rw [sinternW_eq]
  refine internMD_mkK succSch succSch_wf _ _ _ _ _ _ _ _ shash (by decide) (by decide)
    (fun m k x t i => by simp only [shash, Mem.arr64_set64_ne _ _ _ _ _ (show SREC ≠ SHP by decide)])
    hctl (fun t ht hp => ?_)
  simp only [spushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨h1, -⟩, h2⟩ := hp
  exact ⟨h1, col_room _ _ _ ht h1 h2⟩

theorem succLocal : RLocal succSch SRecRel shash [] [] := by
  intro m m' hra _ _; simp only [succSch] at hra
  exact ⟨fun t i k h => by simpa only [SRecRel, hra] using h, fun t i => by simp only [shash, hra]⟩

/-! ## `intern_succ` refines `internLNode (.succ _)` -/

section intern
variable (m : Mem) (a : AState) (hR : SuccR m a) (u : Word) (hu : u.toNat < 2 ^ 32)

include hR hu in
/-- The library's half of `intern_succ` (before the column). -/
theorem sintern_core (w : Word) (m₁ : Mem)
    (hI : internM succSch m 0 (spushOK m) [u]
      (sprobeW (m.arr64 SSLOT) (m.arr64 SREC) 0 u (baseW m 0) (nSlotsS m) (homeW (succHashW u) (nSlotsS m)) 0)
      (sprobeW (m.arr64 SSLOT) (m.arr64 SREC) 1 u (baseW m 1) (nSlotsS m) (homeW (succHashW u) (nSlotsS m)) 0) shash =
      some (w, m₁)) :
    AM.ok (internLNode (.succ (decI u))) a ∧
    SuccR m₁ (AM.st (internLNode (.succ (decI u))) a) ∧
    AM.res (internLNode (.succ (decI u))) a = decI w :=
  intern_correctG succSch SRecRel shash succSch_wf succFrame succLens a m hR _ _ _ _ _
    (internLNode_succ_run _ a) false rfl 0 (by simp) (by simp) _ _ (succMatchOK m u hu)
    (succHomeOK m u) _ _ (probe_homeG succSch m 0 _ _ (sprobeW_arm m u 0) _)
    (probe_homeG succSch m 1 _ _ (sprobeW_arm m u 1) _) _ (spushOK_room m) _ rfl
    (succNewOK m u hu) w m₁ hI

include hR hu in
/-- **`intern_succ`'s model refines the arena's `internLNode` at a `succ` node.** -/
theorem sintern_correct (w : Word) (m' : Mem) (hI : sinternW m u = some (w, m')) :
    AM.ok (internLNode (.succ (decI u))) a ∧
    SuccR m' (AM.st (internLNode (.succ (decI u))) a) ∧
    AM.res (internLNode (.succ (decI u))) a = decI w := by
  rw [sinternW_eqK m u hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := sintern_core m a hR u hu w m₁ h₁
  exact ⟨hok, storeR_frame succSch SRecRel shash succSch_wf [] [] succLocal [SHP] []
    (by simp [Apart, succSch, SREC, SSLOT, SHP, SCB, POOL, CTL]) m₁ m'
    (derPutW_frame SHP (by decide) _ m₁ m' _ _ _ hput) _ _ _ hX, hres⟩

include hR hu in
/-- **The column across `intern_succ`**: the new node's word is its record's bit (`hb`). -/
theorem sintern_hp (hC : ColT2 succLens SHP hpW m a)
    (hb : lvlHPW m u = b2w (a.store.lss.ls.derived (decI u)).hasParam) (w : Word) (m' : Mem)
    (hI : sinternW m u = some (w, m')) :
    ColT2 succLens SHP hpW m' (AM.st (internLNode (.succ (decI u))) a) := by
  rw [sinternW_eqK m u hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := sintern_core m a hR u hu w m₁ h₁
  have hcs := AM.proto_casesG succLens _ _ _ _ _ _ a (internLNode_succ_run _ a) hok
  have hfr : m₁.arr64 SHP = m.arr64 SHP :=
    (internM_frame _ succSch_wf _ _ _ _ _ _ _ _ h₁).1 SHP (by simp [succSch, SREC, SSLOT, SHP])
      (by decide)
  exact colMk succSch succSch_wf SRecRel shash succLens SHP hpW m m₁ m' a _ _ _ _ _ _ hR hX hC hfr
    hcs hres.symm (by rw [hb]; rfl) hput

end intern

/-- `intern_succ` refines `internLNode (.succ _)` under `SuccR`. -/
theorem internSucc_refines (p : Prog) (hpf : p.lookup "succ_find" = some succFind)
    (hpp : p.lookup "succ_push" = some succPush) (hp : p.lookup "intern_succ" = some internSucc)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : SuccR s₀.mem a₀) (hu : u.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_succ" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLNode (.succ (decI u))) a₀ ∧
      SuccR s'.mem (AM.st (internLNode (.succ (decI u))) a₀) ∧
      AM.res (internLNode (.succ (decI u))) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internSucc_spec p hpf hpp hp n s₀ u)
  subst hs
  exact ⟨hloc, sintern_correct s.mem a₀ hR u hu _ _ hI⟩

end L.Arena
