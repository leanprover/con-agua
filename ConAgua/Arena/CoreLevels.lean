import ConAgua.Arena.WhnfBase

/-!
# The level-verdict caches in front of the level algorithms

con-ron caches `Level.isEquiv`'s verdict at a pair of level handles (`lvlEqC`) and
`Level.isEquivList`'s at a pair of level-list handles (`lvlsEqC`); a `none` (con-leche's fuel
exhaustion) is not cached (`Arena/Core.lean:135`, `:154`). Lane `levels`' `lvl_eq`/`lvls_eq`
run the algorithm; here the caches go in front of them, so that L does no more work than the
twin (every con-ron cache is mirrored in L):

* `lvl_eq_c(u, v)`: probe `lq` (array 105, `CoreCaches.lean`); a hit answers its verdict (as
  `encO`: `1` false, `2` true); a miss runs `lvl_eq` and records a `some` answer.
* `lvls_eq_c(us, vs)`: the same with `lsq` (array 106) and `lvls_eq`.

The models `lvlEqCW`/`lvlsEqCW` follow the code; the refinements combine lane `levels`'
`lvlEq_refines`/`lvlsEq_refines` (the algorithm on the handles is `isEquiv` of the readbacks)
with the cache relation of `CoreRM` (`lq`, `lsq`) and the twin's readback caches (`CoreS.readL`,
`readLs`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

abbrev LQ : ArrId := 105
abbrev LSQ : ArrId := 106

/-- The answer word of a level comparison, decoded (`encO`'s inverse). -/
def decO (w : Word) : Option Bool := if w = 0 then none else if w = 1 then some false else some true

theorem decO_encO (o : Option Bool) : decO (encO o) = o := by
  cases o with
  | none => rfl
  | some b => cases b <;> rfl

/-! ## The L code -/

/-- con-ron: ConRon/Arena/Core.lean:132-149 ConRon.Arena.lvlEq? -/
@[l_impl ConRon.Arena.lvlEq?]
def lvlEqCL : FunDecl := lfn (u, v) locals (fd, j, d, z) {
  (fd, j, d) := call lq_find(u, v);
  if fd != 0 { return u64(LQ.u64[j * 4 + 3] != 0) + 1 };
  z := call lvl_eq_rec(u, v);
  return z
}

/-- A miss of `lvl_eq_c`: run the algorithm, record a `some` answer. -/
-- con-ron: ConRon/Arena/Core.lean:132-149 ConRon.Arena.lvlEq?
def lvlEqRecL : FunDecl := lfn (u, v) locals (fd, j, d, z, x) {
  z := call lvl_eq(u, v);
  if z == 0 { return 0 };
  (fd, j, d) := call lq_find(u, v);
  x := call lq_put(u, v, z - 1, fd, j);
  return z
}

/-- con-ron: ConRon/Arena/Core.lean:151-168 ConRon.Arena.lvlsEq? -/
@[l_impl ConRon.Arena.lvlsEq?]
def lvlsEqCL : FunDecl := lfn (us, vs) locals (fd, j, d, z) {
  (fd, j, d) := call lsq_find(us, vs);
  if fd != 0 { return u64(LSQ.u64[j * 4 + 3] != 0) + 1 };
  z := call lvls_eq_rec(us, vs);
  return z
}

/-- A miss of `lvls_eq_c`. -/
-- con-ron: ConRon/Arena/Core.lean:151-168 ConRon.Arena.lvlsEq?
def lvlsEqRecL : FunDecl := lfn (us, vs) locals (fd, j, d, z, x) {
  z := call lvls_eq(us, vs);
  if z == 0 { return 0 };
  (fd, j, d) := call lsq_find(us, vs);
  x := call lsq_put(us, vs, z - 1, fd, j);
  return z
}

/-! ## The models -/

/-- Record a `some` answer `z` at `(u, v)` in memo `S`. -/
def rcdK (S : MemoSch) (u v : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m₁) =>
    if z = 0 then some (0, m₁) else
    match msetG S m₁ u v (z - 1) with
    | none => none
    | some m₂ => some (z, m₂)

/-- The model of `lvl_eq_c`: the probe, then `lvl_eq` on a miss. -/
def lvlEqCW (n : Nat) (m : Mem) (u v : Word) : Option (Word × Mem) :=
  if mfindG lqSch m u v = [] then none
  else if (mfindG lqSch m u v).headD 0 ≠ 0 then
    some ((if mvG lqSch m ((mfindG lqSch m u v).tail.headD 0) ≠ 0 then 1 else 0) + 1, m)
  else rcdK lqSch u v (lvlEqW n m u v)

/-- The model of `lvls_eq_c`. -/
def lvlsEqCW (n : Nat) (m : Mem) (us vs : Word) : Option (Word × Mem) :=
  if mfindG lsqSch m us vs = [] then none
  else if (mfindG lsqSch m us vs).headD 0 ≠ 0 then
    some ((if mvG lsqSch m ((mfindG lsqSch m us vs).tail.headD 0) ≠ 0 then 1 else 0) + 1, m)
  else rcdK lsqSch us vs (lvlsEqW n m us vs)

/-- What the cached comparisons need of a program. -/
structure LvlCacheProg (p : Prog) : Prop where
  lev : LevelProg p
  equiv : p.lookup "lv_equiv" = some lvEquiv
  equivs : p.lookup "lv_equivs" = some lvEquivs
  lsnode : p.lookup "ls_node" = some lsNode
  lvleq : p.lookup "lvl_eq" = some lvlEqL
  lvlseq : p.lookup "lvls_eq" = some lvlsEqL
  lqf : p.lookup "lq_find" = some (memoFindG lqSch)
  lqp : p.lookup "lq_put" = some (memoPutG lqSch)
  lsqf : p.lookup "lsq_find" = some (memoFindG lsqSch)
  lsqp : p.lookup "lsq_put" = some (memoPutG lsqSch)
  c : p.lookup "lvl_eq_c" = some lvlEqCL
  cs : p.lookup "lvls_eq_c" = some lvlsEqCL
  r : p.lookup "lvl_eq_rec" = some lvlEqRecL
  rs : p.lookup "lvls_eq_rec" = some lvlsEqRecL

section specs
variable (p : Prog) (hp : LvlCacheProg p)

theorem lvlEqCW_hit (n : Nat) (m : Mem) (u v : Word) (h0 : mfindG lqSch m u v ≠ [])
    (h1 : (mfindG lqSch m u v).headD 0 ≠ 0) :
    lvlEqCW n m u v =
      some ((if mvG lqSch m ((mfindG lqSch m u v).tail.headD 0) ≠ 0 then 1 else 0) + 1, m) := by
  unfold lvlEqCW; rw [if_neg h0, if_pos h1]

theorem lvlEqCW_miss (n : Nat) (m : Mem) (u v : Word) (h0 : mfindG lqSch m u v ≠ [])
    (h1 : (mfindG lqSch m u v).headD 0 = 0) :
    lvlEqCW n m u v = rcdK lqSch u v (lvlEqW n m u v) := by
  unfold lvlEqCW; rw [if_neg h0, if_neg (by simp only [ne_eq, Decidable.not_not]; exact h1)]

theorem lvlsEqCW_hit (n : Nat) (m : Mem) (u v : Word) (h0 : mfindG lsqSch m u v ≠ [])
    (h1 : (mfindG lsqSch m u v).headD 0 ≠ 0) :
    lvlsEqCW n m u v =
      some ((if mvG lsqSch m ((mfindG lsqSch m u v).tail.headD 0) ≠ 0 then 1 else 0) + 1, m) := by
  unfold lvlsEqCW; rw [if_neg h0, if_pos h1]

theorem lvlsEqCW_miss (n : Nat) (m : Mem) (u v : Word) (h0 : mfindG lsqSch m u v ≠ [])
    (h1 : (mfindG lsqSch m u v).headD 0 = 0) :
    lvlsEqCW n m u v = rcdK lsqSch u v (lvlsEqW n m u v) := by
  unfold lvlsEqCW; rw [if_neg h0, if_neg (by simp only [ne_eq, Decidable.not_not]; exact h1)]

theorem rcdK_zero (S : MemoSch) (u v z : Word) (m₁ : Mem) (hz : z = 0) :
    rcdK S u v (some (z, m₁)) = some (0, m₁) := by simp [rcdK, hz]

theorem rcdK_ne (S : MemoSch) (u v z : Word) (m₁ m₂ : Mem) (hz : ¬ z = 0)
    (hs : msetG S m₁ u v (z - 1) = some m₂) : rcdK S u v (some (z, m₁)) = some (z, m₂) := by
  simp [rcdK, hz, hs]

include hp in
theorem lvlEqRec_spec (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lvl_eq_rec" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ rcdK lqSch u v (lvlEqW n s₀.mem u v) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.r]
  simp only [callFn, lvlEqRecL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      memoFindG_spec lqSch p _ hp.lqf n, memoPutG_spec lqSch p _ hp.lqp n,
      lvlEq_spec p hp.lev hp.equiv hp.lvleq n] <;>
    finish [rcdK_zero, rcdK_ne, msetG_eq]

include hp in
theorem lvlsEqRec_spec (n : Nat) (s₀ : St) (us vs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lvls_eq_rec" [us, vs]
    ⦃fun r s' => LocEq s' s₀ ∧ rcdK lsqSch us vs (lvlsEqW n s₀.mem us vs) = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.rs]
  simp only [callFn, lvlsEqRecL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      memoFindG_spec lsqSch p _ hp.lsqf n, memoPutG_spec lsqSch p _ hp.lsqp n,
      lvlsEq_spec p hp.lev hp.equiv hp.equivs hp.lsnode hp.lvlseq n] <;>
    finish [rcdK_zero, rcdK_ne, msetG_eq]

include hp in
theorem lvlEqC_spec (n : Nat) (s₀ : St) (u v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "lvl_eq_c" [u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ lvlEqCW n s₀.mem u v = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.c]
  simp only [callFn, lvlEqCL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lqSch p _ hp.lqf (n + 1), lvlEqRec_spec p hp n] <;>
    finish [lvlEqCW_hit, lvlEqCW_miss, mvG]

include hp in
theorem lvlsEqC_spec (n : Nat) (s₀ : St) (us vs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "lvls_eq_c" [us, vs]
    ⦃fun r s' => LocEq s' s₀ ∧ lvlsEqCW n s₀.mem us vs = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.cs]
  simp only [callFn, lvlsEqCL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lsqSch p _ hp.lsqf (n + 1), lvlsEqRec_spec p hp n] <;>
    finish [lvlsEqCW_hit, lvlsEqCW_miss, mvG]

end specs

end L.Arena

/-! ## The twin's `lvlEq?` on a hit and on a miss -/

namespace L.Arena

open ConLeche

/-- `readLevelM` at a defined handle: its readback, and only `readLC` changes. -/
theorem readLevelM_run' (a : AState) (h : LIdx) (l : Level) (hd : denoteL a.store.ls h = some l)
    (hc : ReadLCOK a) :
    ∃ X, (readLevelM h).run a = .ok (l, { a with caches := { a.caches with readLC := X } }) ∧
      ReadLCOK { a with caches := { a.caches with readLC := X } } := by
  simp only [readLevelM]
  cases e : a.caches.readLC[h]? with
  | some l' =>
    have := hc _ _ e; rw [hd] at this; cases this
    exact ⟨a.caches.readLC, by simp [e]; rfl, by simpa using hc⟩
  | none =>
    refine ⟨a.caches.readLC.insert h l, ?_, ?_⟩
    · simp [e, hd]; rfl
    · intro h' l' e'
      simp only [Std.HashMap.getElem?_insert] at e'
      split at e'
      · rename_i hb; cases e'; rw [← eq_of_beq hb]; exact hd
      · exact hc _ _ e'

/-- The verdict table after a miss. -/
def lvlEqIns (t : Std.HashMap (LIdx × LIdx) Bool) (u v : LIdx) : Option Bool →
    Std.HashMap (LIdx × LIdx) Bool
  | some r => t.insert (u, v) r
  | none => t

/-- **`lvlEq?` on a miss**: `isEquiv` of the readbacks; `readLC` and `lvlEqC` change. -/
theorem lvlEq?_miss (a : AState) (u v : LIdx) (lu lv : Level)
    (hu : denoteL a.store.ls u = some lu) (hv : denoteL a.store.ls v = some lv)
    (hc : ReadLCOK a) (hm : a.caches.lvlEqC[(u, v)]? = none) :
    ∃ X, (lvlEq? u v).run a = .ok (Level.isEquiv lu lv, { a with caches := { a.caches with
        readLC := X, lvlEqC := lvlEqIns a.caches.lvlEqC u v (Level.isEquiv lu lv) } }) ∧
      ReadLCOK { a with caches := { a.caches with readLC := X } } := by
  obtain ⟨X₁, h₁, hc₁⟩ := readLevelM_run' a u lu hu hc
  obtain ⟨X₂, h₂, hc₂⟩ := readLevelM_run' { a with caches := { a.caches with readLC := X₁ } } v lv
    hv hc₁
  refine ⟨X₂, ?_, by simpa using hc₂⟩
  simp only [lvlEq?]
  cases eq : Level.isEquiv lu lv with
  | none => simp [hm, StateT.run_bind, h₁, except_ok_bind, h₂, eq, lvlEqIns]; rfl
  | some r => simp [hm, StateT.run_bind, h₁, except_ok_bind, h₂, eq, lvlEqIns]; rfl

/-- **`lvlEq?` on a hit**: the cached verdict, nothing changes. -/
theorem lvlEq?_hit (a : AState) (u v : LIdx) (r : Bool) (hm : a.caches.lvlEqC[(u, v)]? = some r) :
    (lvlEq? u v).run a = .ok (some r, a) := by
  simp [lvlEq?, hm]; rfl

end L.Arena

/-! ## The relation across the verdict caches' writes -/

namespace L.Arena

open ConLeche

/-- The core tier does not read the readback caches. -/
theorem CoreRM.readLC {m : Mem} {c : Caches} {M : ModeMaps} {eb : Word} (h : CoreRM m c M eb)
    (X : Std.HashMap LIdx Level) : CoreRM m { c with readLC := X } M eb :=
  ⟨h.wc, h.wk, h.wh, h.inf, h.io, h.de, h.eb1, h.ct, h.cv, h.rr, h.lq, h.lsq⟩

theorem lqSch_wf : lqSch.WF := ⟨by decide, by decide⟩
theorem lsqSch_wf : lsqSch.WF := ⟨by decide, by decide⟩

/-- **A `find; put` of `lvlEqC`** keeps the relation, the twin's table gaining the entry. -/
theorem CoreS.set_lq {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (u v w : Word)
    (hu : HW u) (hv : HW v) (hs : msetG lqSch m u v w = some m') :
    CoreS dn m' { a with caches := { a.caches with
        lvlEqC := a.caches.lvlEqC.insert ((decI u : LIdx), (decI v : LIdx)) (decB w) } } vis fe M eb ∧
      StackKept m m' := by
  have hf : MemFrame [105] [117] m m' := msetG_frame lqSch lqSch_wf m m' u v w hs
  have nA : ∀ b : ArrId, 96 ≤ b → b < 145 → b ≠ 105 → b ∉ [(105 : ArrId)] := fun b _ _ h hb => by
    simp at hb; exact h hb
  have hq := memoRG_set lqSch lqSch_wf pairKey decB m _ hS.core.lq u v w ⟨hu, hv⟩ m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 105 → S.cs ≠ 117 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [105] [117] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 105 → S.cs ≠ 117 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 105 → S.cs ≠ 117 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [105] [117] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [105] [117] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [105] [117] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.io,
        mr (coreSch_wf _ _ (by decide) (by decide)) vb_const (by decide) (by decide) hS.core.de,
        hS.core.eb1,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.ct,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.cv,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.rr,
        hq,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lsq⟩,
      hS.pins.congr (hf.1 PINS (by simp [PINS]) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hS.memos.frame hf (by decide) (by decide), hf.2.2.1 145 ▸ hS.bstk,
      (hS.den.frameE (hf.1 EREC (by simp [EREC]) (by decide))).caches rfl rfl rfl,
      hS.mode.frame hf (by simp) (by simp)⟩,
    StackKept.of_frame hf⟩

end L.Arena

/-! ## `lvl_eq_c` refines `lvlEq?` -/

namespace L.Arena

open ConLeche

theorem encO_zero {o : Option Bool} (h : encO o = 0) : o = none := by
  cases o with
  | none => rfl
  | some b => cases b <;> simp [encO] at h

theorem encO_pred (r : Bool) : decB (encO (some r) - 1) = r := by
  cases r <;> rfl

theorem decO_hit (w : Word) : decO ((if w ≠ 0 then 1 else 0) + 1) = some (decB w) := by
  by_cases h : w = 0 <;> simp [h, decO, decB]

theorem hw_hit (w : Word) : HW ((if w ≠ 0 then 1 else 0) + 1) := by
  unfold HW; split <;> decide

theorem hw_encO (r : Bool) : HW (encO (some r)) := by
  unfold HW; cases r <;> decide

/-- **The model of `lvl_eq_c` refines `lvlEq?`** under `CoreS`, at handles whose readbacks are
defined: the twin runs, returns the decoded answer, and the relation holds after. -/
theorem lvlEqCW_ok {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (n : Nat) (u v : Word)
    (hu : HW u) (hv : HW v) (lu lv : Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) (z : Word) (h : lvlEqCW n m u v = some (z, m')) :
    ∃ a', (lvlEq? (decI u) (decI v)).run a = .ok (decO z, a') ∧
      CoreAfter dn m m' a' vis fe M eb ∧ HW z := by
  unfold lvlEqCW at h
  by_cases h0 : mfindG lqSch m u v = []
  · simp [h0] at h
  rw [if_neg h0] at h
  by_cases h1 : (mfindG lqSch m u v).headD 0 ≠ 0
  · rw [if_pos h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hit := memoRG_hit lqSch pairKey decB m _ hS.core.lq u v h0 h1 ⟨hu, hv⟩
    exact ⟨a, by rw [lvlEq?_hit a _ _ _ hit, decO_hit], ⟨M, hS, KeptAll.refl _ _,
      StackKept.refl _⟩, hw_hit _⟩
  rw [if_neg h1] at h
  have miss := memoRG_miss lqSch pairKey decB m _ hS.core.lq u v ⟨hu, hv⟩ h0
    (by simpa using h1)
  cases hl : lvlEqW n m u v with
  | none => simp [hl, rcdK] at h
  | some p =>
  obtain ⟨z₁, m₁⟩ := p
  rw [hl] at h
  cases n with
  | zero => simp [lvlEqW] at hl
  | succ n =>
  simp only [lvlEqW] at hl
  have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
    ArenaR.frame (by decide) c192_not_arena (reset_frame m) hS.arena.1
  have hwu : (decI u : LIdx).word.toUInt64 = u := (word_decI _ u hu).mpr rfl
  have hwv : (decI v : LIdx).word.toUInt64 = v := (word_decI _ v hv).mpr rfl
  have hl' := denoteL_lvR hR₀ (decI u) lu hdu
  have hr' := denoteL_lvR hR₀ (decI v) lv hdv
  rw [hwu] at hl'; rw [hwv] at hr'
  obtain ⟨hx, hz⟩ := equivW_ok (nameN_rel _ hS.nwf) n _ _ _ _ _ _ _ hl' hr' hl
  have hf₁ : MemFrame [LH] [192] m m₁ :=
    ((reset_frame m).mono (by simp) (by simp)).trans hx.memFrame
  obtain ⟨hS₁, hK₁⟩ := hS.frame hf₁ (by simp [LH]) (by simp)
  obtain ⟨X, hrun, hrl⟩ := lvlEq?_miss a (decI u) (decI v) lu lv hdu hdv hS.readL miss
  -- the state after the miss, before the insert
  have hS₂ : CoreS dn m₁ { a with caches := { a.caches with readLC := X } } vis fe M eb :=
    ⟨⟨ArenaR.caches_irrel _ hS₁.arena.1, DerR.of_store _ _ _ hS₁.arena.2 rfl⟩, hS₁.core.readLC X,
      hS₁.pins,
      hS₁.env, hrl, fun h l e => hS₁.readLs h l e, hS₁.nwf, hS₁.erec, hS₁.spn, hS₁.memos, hS₁.bstk,
      hS₁.den.caches rfl rfl rfl, hS₁.mode⟩
  by_cases hz0 : z₁ = 0
  · rw [rcdK_zero _ _ _ _ _ hz0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ho := encO_zero (hz ▸ hz0)
    rw [ho] at hrun
    refine ⟨_, hrun, ⟨M, ?_, KeptAll.refl _ _, hK₁⟩, by unfold HW; decide⟩
    simp only [ho, lvlEqIns]
    exact hS₂
  · cases hs : msetG lqSch m₁ u v (z₁ - 1) with
    | none => simp [rcdK, hz0, hs] at h
    | some m₂ =>
    rw [rcdK_ne _ _ _ _ _ _ hz0 hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hS₃, hK₃⟩ := hS₂.set_lq u v (z₁ - 1) hu hv hs
    cases eo : Level.isEquiv lu lv with
    | none => rw [eo] at hz; exact absurd hz hz0
    | some r =>
    rw [eo] at hz hrun
    subst hz
    refine ⟨_, by rw [hrun, decO_encO], ⟨M, ?_, KeptAll.refl _ _, hK₁.trans hK₃⟩, hw_encO _⟩
    rw [encO_pred] at hS₃
    simpa [lvlEqIns] using hS₃

/-- **`lvl_eq_c` refines con-ron's `lvlEq?`** (the verdict cache in front of lane `levels`'
`lvl_eq`), under `CoreS`, at level handles whose readbacks are defined. -/
@[refines ConRon.Arena.lvlEq?]
theorem lvlEqC_refines (p : Prog) (hp : LvlCacheProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (u v : Word) (hu : HW u) (hv : HW v) (lu lv : Level)
    (hdu : denoteL a₀.store.ls (decI u) = some lu) (hdv : denoteL a₀.store.ls (decI v) = some lv) :
    CoreSpec p (n + 2) "lvl_eq_c" [u, v] (lvlEq? (decI u) (decI v)) (fun r => decO (r.headD 0))
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun (lvlEqC_spec p hp n s₀ u v)
  subst hs
  obtain ⟨a', ha', hA', hz⟩ := lvlEqCW_ok hS n u v hu hv lu lv hdu hdv _ hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hz⟩

end L.Arena

/-! ## `lvls_eq_c` refines `lvlsEq?` -/

namespace L.Arena

open ConLeche

theorem CoreRM.readLsC {m : Mem} {c : Caches} {M : ModeMaps} {eb : Word} (h : CoreRM m c M eb)
    (X : Std.HashMap LsIdx (List Level)) : CoreRM m { c with readLsC := X } M eb :=
  ⟨h.wc, h.wk, h.wh, h.inf, h.io, h.de, h.eb1, h.ct, h.cv, h.rr, h.lq, h.lsq⟩

/-- `readLevelsM` at a defined handle: its readback, and only `readLsC` changes. -/
theorem readLevelsM_run' (a : AState) (h : LsIdx) (ls : List Level)
    (hd : denoteLs a.store.lss h = some ls) (hc : ReadLsCOK a) :
    ∃ X, (readLevelsM h).run a = .ok (ls, { a with caches := { a.caches with readLsC := X } }) ∧
      ReadLsCOK { a with caches := { a.caches with readLsC := X } } := by
  simp only [readLevelsM]
  cases e : a.caches.readLsC[h]? with
  | some l' =>
    have := hc _ _ e; rw [hd] at this; cases this
    exact ⟨a.caches.readLsC, by simp [e]; rfl, by simpa using hc⟩
  | none =>
    refine ⟨a.caches.readLsC.insert h ls, ?_, ?_⟩
    · simp [e, hd]; rfl
    · intro h' l' e'
      simp only [Std.HashMap.getElem?_insert] at e'
      split at e'
      · rename_i hb; cases e'; rw [← eq_of_beq hb]; exact hd
      · exact hc _ _ e'

/-- The list-verdict table after a miss. -/
def lvlsEqIns (t : Std.HashMap (LsIdx × LsIdx) Bool) (u v : LsIdx) : Option Bool →
    Std.HashMap (LsIdx × LsIdx) Bool
  | some r => t.insert (u, v) r
  | none => t

theorem lvlsEq?_miss (a : AState) (us vs : LsIdx) (lu lv : List Level)
    (hu : denoteLs a.store.lss us = some lu) (hv : denoteLs a.store.lss vs = some lv)
    (hc : ReadLsCOK a) (hm : a.caches.lvlsEqC[(us, vs)]? = none) :
    ∃ X, (lvlsEq? us vs).run a = .ok (Level.isEquivList lu lv, { a with caches := { a.caches with
        readLsC := X, lvlsEqC := lvlsEqIns a.caches.lvlsEqC us vs (Level.isEquivList lu lv) } }) ∧
      ReadLsCOK { a with caches := { a.caches with readLsC := X } } := by
  obtain ⟨X₁, h₁, hc₁⟩ := readLevelsM_run' a us lu hu hc
  obtain ⟨X₂, h₂, hc₂⟩ := readLevelsM_run' { a with caches := { a.caches with readLsC := X₁ } } vs
    lv hv hc₁
  refine ⟨X₂, ?_, by simpa using hc₂⟩
  simp only [lvlsEq?]
  cases eq : Level.isEquivList lu lv with
  | none => simp [hm, StateT.run_bind, h₁, except_ok_bind, h₂, eq, lvlsEqIns]; rfl
  | some r => simp [hm, StateT.run_bind, h₁, except_ok_bind, h₂, eq, lvlsEqIns]; rfl

theorem lvlsEq?_hit (a : AState) (us vs : LsIdx) (r : Bool)
    (hm : a.caches.lvlsEqC[(us, vs)]? = some r) : (lvlsEq? us vs).run a = .ok (some r, a) := by
  simp [lvlsEq?, hm]; rfl

/-- A `find; put` of `lvlsEqC` keeps the relation. -/
theorem CoreS.set_lsq {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (u v w : Word)
    (hu : HW u) (hv : HW v) (hs : msetG lsqSch m u v w = some m') :
    CoreS dn m' { a with caches := { a.caches with
        lvlsEqC := a.caches.lvlsEqC.insert ((decI u : LsIdx), (decI v : LsIdx)) (decB w) } } vis fe M eb ∧
      StackKept m m' := by
  have hf : MemFrame [106] [119] m m' := msetG_frame lsqSch lsqSch_wf m m' u v w hs
  have hq := memoRG_set lsqSch lsqSch_wf pairKey decB m _ hS.core.lsq u v w ⟨hu, hv⟩ m' hs
  have fr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ) (dv : Word → ν)
      (mp : Std.HashMap κ ν), S.WF → S.arr ≠ 106 → S.cs ≠ 119 → MemoRG S K dv m mp →
      MemoRG S K dv m' mp :=
    fun S K dv mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [106] [119] (by simpa using h1) (by simpa using h2) m m' hf
        (fun _ _ h => h) mp hR
  have mr : ∀ {κ ν : Type} [BEq κ] [Hashable κ] {S : MemoSch} {K : MemoKey (κ × Word)}
      {VR : Mem → Word → ν → Prop} {M₀ : Std.HashMap (κ × Word) ν} {t te : Std.HashMap κ ν}, S.WF →
      VConst VR → S.arr ≠ 106 → S.cs ≠ 119 → ModeR S K VR m M₀ eb t te →
      ModeR S K VR m' M₀ eb t te :=
    fun hS' hV h1 h2 h => h.frame hS' hV (by simpa using h1) (by simpa using h2) hf
  have frv : ∀ {κ : Type} [BEq κ] [Hashable κ] (S : MemoSch) (K : MemoKey κ)
      (mp : Std.HashMap κ EIdx), S.WF → S.arr ≠ 106 → S.cs ≠ 119 → MemoRV S K VH m mp →
      MemoRV S K VH m' mp :=
    fun S K mp hS' h1 h2 hR =>
      memoRV_frame S hS' K _ [106] [119] (by simpa using h1) (by simpa using h2) m m' hf
        (vh_const m m') mp hR
  have hspn : m'.arr64 SPN = m.arr64 SPN := hf.1 SPN (by simp [SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  refine ⟨⟨⟨ArenaR.caches_irrel _ (ArenaR.frame_ext [106] [119] (by simp) (by simp) m m' hf a
        hS.arena.1), DerR.of_store _ _ _ (DerR.frameM [106] [119] m m' hf (by simp) a hS.arena.2) rfl⟩,
      ⟨mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wc,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wk,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.wh,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.inf,
        mr (coreSch_wf _ _ (by decide) (by decide)) vh_const (by decide) (by decide) hS.core.io,
        mr (coreSch_wf _ _ (by decide) (by decide)) vb_const (by decide) (by decide) hS.core.de,
        hS.core.eb1,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.ct,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.cv,
        frv _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.rr,
        fr _ _ _ _ (coreSch_wf _ _ (by decide) (by decide)) (by decide) (by decide) hS.core.lq,
        hq⟩,
      hS.pins.congr (hf.1 PINS (by simp [PINS]) (by decide)),
      hS.env.frame (fun b hb => by simp at hb; subst hb; decide)
        (fun x hx => by simp at hx; subst hx; decide) hf,
      fun h l e => hS.readL h l e, fun h l e => hS.readLs h l e, hS.nwf,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn, hS.memos.frame hf (by decide) (by decide), hf.2.2.1 145 ▸ hS.bstk,
      (hS.den.frameE (hf.1 EREC (by simp [EREC]) (by decide))).caches rfl rfl rfl,
      hS.mode.frame hf (by simp) (by simp)⟩,
    StackKept.of_frame hf⟩

/-- **The model of `lvls_eq_c` refines `lvlsEq?`** under `CoreS`. -/
theorem lvlsEqCW_ok {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (n : Nat)
    (us vs : Word) (hu : HW us) (hv : HW vs) (z : Word) (h : lvlsEqCW n m us vs = some (z, m')) :
    ∃ a', (lvlsEq? (decI us) (decI vs)).run a = .ok (decO z, a') ∧
      CoreAfter dn m m' a' vis fe M eb ∧ HW z := by
  unfold lvlsEqCW at h
  by_cases h0 : mfindG lsqSch m us vs = []
  · simp [h0] at h
  rw [if_neg h0] at h
  by_cases h1 : (mfindG lsqSch m us vs).headD 0 ≠ 0
  · rw [if_pos h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hit := memoRG_hit lsqSch pairKey decB m _ hS.core.lsq us vs h0 h1 ⟨hu, hv⟩
    exact ⟨a, by rw [lvlsEq?_hit a _ _ _ hit, decO_hit], ⟨M, hS, KeptAll.refl _ _,
      StackKept.refl _⟩, hw_hit _⟩
  rw [if_neg h1] at h
  have miss := memoRG_miss lsqSch pairKey decB m _ hS.core.lsq us vs ⟨hu, hv⟩ h0
    (by simpa using h1)
  cases hl : lvlsEqW n m us vs with
  | none => simp [hl, rcdK] at h
  | some p =>
  obtain ⟨z₁, m₁⟩ := p
  rw [hl] at h
  cases n with
  | zero => simp [lvlsEqW] at hl
  | succ n =>
  simp only [lvlsEqW] at hl
  have hn : ¬ (lsNodeW m us = [] ∨ lsNodeW m vs = []) := fun c => by rw [if_pos c] at hl; cases hl
  rw [if_neg hn] at hl
  -- `ls_node` read both handles, so both are stored and read back (`StoreDen.lsAll`)
  obtain ⟨lu, hdu⟩ := hS.den.lsAll _ (by
    obtain ⟨ids, e, -⟩ := lsNodeW_view hS.arena.1 hu (fun e => hn (.inl e)); rw [e]; rfl)
  obtain ⟨lv, hdv⟩ := hS.den.lsAll _ (by
    obtain ⟨ids, e, -⟩ := lsNodeW_view hS.arena.1 hv (fun e => hn (.inr e)); rw [e]; rfl)
  have hwu : (decI us : LsIdx).word.toUInt64 = us := (word_decI _ us hu).mpr rfl
  have hwv : (decI vs : LsIdx).word.toUInt64 = vs := (word_decI _ vs hv).mpr rfl
  obtain ⟨ids₁, hv₁, hd₁⟩ := denoteLs_view a (decI us) lu hdu
  obtain ⟨ids₂, hv₂, hd₂⟩ := denoteLs_view a (decI vs) lv hdv
  obtain ⟨e₁, t₁, s₁⟩ := lsNodeW_store hS.arena.1 hu (by exact hv₁)
  obtain ⟨e₂, t₂, s₂⟩ := lsNodeW_store hS.arena.1 hv (by exact hv₂)
  rw [e₁, e₂] at hl
  simp only [List.headD_cons, List.tail_cons] at hl
  have hR₀ : ArenaR (m.set64 CTL 192 0) a :=
    ArenaR.frame (by decide) c192_not_arena (reset_frame m) hS.arena.1
  have hpool : (m.set64 CTL 192 0).arr64 POOL = m.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpool1 : (m.set64 CTL 192 0).arr64 POOL1 = m.arr64 POOL1 :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpoolv := vpool_congr hpool hpool1
  have htop := (hS.arena.1).lit.1.top41
  have hl₁ := lvsR_of_slice hR₀ ids₁ lu _ _ (by rw [hpoolv]; exact s₁) (by omega) hd₁
  have hl₂ := lvsR_of_slice hR₀ ids₂ lv _ _ (by rw [hpoolv]; exact s₂) (by omega) hd₂
  obtain ⟨hx, hz⟩ := equivsW_ok (nameN_rel _ hS.nwf) n _ _ _ _ _ _ _ _ _ hl₁ hl₂ hl
  have hf₁ : MemFrame [LH] [192] m m₁ :=
    ((reset_frame m).mono (by simp) (by simp)).trans hx.memFrame
  obtain ⟨hS₁, hK₁⟩ := hS.frame hf₁ (by simp [LH]) (by simp)
  obtain ⟨X, hrun, hrl⟩ := lvlsEq?_miss a (decI us) (decI vs) lu lv hdu hdv hS.readLs miss
  have hS₂ : CoreS dn m₁ { a with caches := { a.caches with readLsC := X } } vis fe M eb :=
    ⟨⟨ArenaR.caches_irrel _ hS₁.arena.1, DerR.of_store _ _ _ hS₁.arena.2 rfl⟩,
      hS₁.core.readLsC X, hS₁.pins, hS₁.env, fun h l e => hS₁.readL h l e, hrl, hS₁.nwf,
      hS₁.erec, hS₁.spn, hS₁.memos, hS₁.bstk,
      hS₁.den.caches rfl rfl rfl, hS₁.mode⟩
  by_cases hz0 : z₁ = 0
  · rw [rcdK_zero _ _ _ _ _ hz0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ho := encO_zero (hz ▸ hz0)
    rw [ho] at hrun
    refine ⟨_, hrun, ⟨M, ?_, KeptAll.refl _ _, hK₁⟩, by unfold HW; decide⟩
    simp only [ho, lvlsEqIns]
    exact hS₂
  · cases hs : msetG lsqSch m₁ us vs (z₁ - 1) with
    | none => simp [rcdK, hz0, hs] at h
    | some m₂ =>
    rw [rcdK_ne _ _ _ _ _ _ hz0 hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hS₃, hK₃⟩ := hS₂.set_lsq us vs (z₁ - 1) hu hv hs
    cases eo : Level.isEquivList lu lv with
    | none => rw [eo] at hz; exact absurd hz hz0
    | some r =>
    rw [eo] at hz hrun
    subst hz
    refine ⟨_, by rw [hrun, decO_encO], ⟨M, ?_, KeptAll.refl _ _, hK₁.trans hK₃⟩, hw_encO _⟩
    rw [encO_pred] at hS₃
    simpa [lvlsEqIns] using hS₃

/-- **`lvls_eq_c` refines con-ron's `lvlsEq?`** (the verdict cache in front of `lvls_eq`). -/
@[refines ConRon.Arena.lvlsEq?]
theorem lvlsEqC_refines (p : Prog) (hp : LvlCacheProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (us vs : Word) (hu : HW us) (hv : HW vs) :
    CoreSpec p (n + 2) "lvls_eq_c" [us, vs] (lvlsEq? (decI us) (decI vs))
      (fun r => decO (r.headD 0)) s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun (lvlsEqC_spec p hp n s₀ us vs)
  subst hs
  obtain ⟨a', ha', hA', hz⟩ := lvlsEqCW_ok hS n us vs hu hv _ hI
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ ha'
  exact ⟨hloc, hok, hst ▸ hA', hres, hz⟩

end L.Arena
