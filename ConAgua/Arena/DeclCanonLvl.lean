import ConAgua.Arena.DeclCanonView2
import ConAgua.Arena.IndInstallSpec.DomsW

/-!
# The canonical level comparison in L (lane `decls3`, helper `decls3-canon`)

`canon_name_map`, `canon_level_eq`, `canon_level_list_eq` against `canonNameMap`, `canonLevelEq`,
`canonLevelListEq`. None of them writes memory. The renaming context is three `IW` slices
(`CtxR`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The renaming context** `(po, pl, qo, ql, co, cl)`: the two parameter lists and the numerals,
three `IW` slices of handles below the pool's top. -/
structure CtxR (m : Mem) (po pl qo ql co cl : Word) (ps qs cs : List NIdx) : Prop where
  p : decHL m po.toNat pl.toNat = some ps
  q : decHL m qo.toNat ql.toNat = some qs
  c : decHL m co.toNat cl.toNat = some cs
  pt : po.toNat + pl.toNat ≤ iwTop m
  qt : qo.toNat + ql.toNat ≤ iwTop m
  ct : co.toNat + cl.toNat ≤ iwTop m

theorem CtxR.grow {m m' : Mem} {po pl qo ql co cl : Word} {ps qs cs : List NIdx}
    (h : CtxR m po pl qo ql co cl ps qs cs) (hg : IWGrow m m') :
    CtxR m' po pl qo ql co cl ps qs cs :=
  ⟨by rw [decHL_grow hg h.pt]; exact h.p, by rw [decHL_grow hg h.qt]; exact h.q,
   by rw [decHL_grow hg h.ct]; exact h.c, Nat.le_trans h.pt hg.1, Nat.le_trans h.qt hg.1,
   Nat.le_trans h.ct hg.1⟩

theorem iwTop_lt (m : Mem) : iwTop m < 2 ^ 64 := UInt64.toNat_lt _

/-! ## `canon_name_map` -/

theorem findIdx_map_decI {k : IdxKind} (x : Word) (hx : x.toNat < 2 ^ 32) :
    ∀ ws : List Word, (∀ w ∈ ws, w.toNat < 2 ^ 32) →
    (ws.map (decI : Word → Idx k)).findIdx? (fun p => p == decI x) = ws.findIdx? (· == x)
  | [], _ => rfl
  | w :: ws, h => by
    have hw : w.toNat < 2 ^ 32 := h w (by simp)
    have e : ((decI w : Idx k) == decI x) = (w == x) := by
      rw [decI_beq w x hw hx]; rfl
    have ih := findIdx_map_decI (k := k) x hx ws (fun v hv => h v (by simp [hv]))
    simp [List.findIdx?_cons, e, ih]


/-- `sl_getd(o, l, j, z)` of a handle slice is the twin's `getD j z`. -/
theorem getDW_handle' {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)}
    (h : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64) (j z : Word)
    (hz : z.toNat < 2 ^ 32) :
    (getDW m o l j z).toNat < 2 ^ 32 ∧ decI (getDW m o l j z) = xs.getD j.toNat (decI z) := by
  have hl := decHL_length m h
  unfold getDW
  by_cases hj : l ≤ j
  · have : l.toNat ≤ j.toNat := UInt64.le_iff_toNat_le.mp hj
    simp [hj, hz, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : xs.length ≤ j.toNat)]
  · have hjl : j.toNat < l.toNat := by
      have : ¬ l.toNat ≤ j.toNat := fun h' => hj (UInt64.le_iff_toNat_le.mpr h'); omega
    rw [ite_eq_right hj]
    obtain ⟨w, hw, hw32, hwd⟩ := decHL_get' h j.toNat hjl hb
    have hoj : o + j = UInt64.ofNat (o.toNat + j.toNat) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    rw [hoj, hw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact ⟨hw32, by simp [hwd]⟩

/-- `sl_find` on a handle slice is `findIdx? (· == decI x)`. -/
theorem findW_handle {k : IdxKind} {n : Nat} {m : Mem} {o l x : Word} {r : List Word}
    {xs : List (Idx k)} (hxs : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat < 2 ^ 64)
    (hx : x.toNat < 2 ^ 32) (h : findW n m o l x = some r) :
    match xs.findIdx? (fun p => p == decI x) with
    | some i => r = [1, UInt64.ofNat i]
    | none => r = [0, 0] := by
  obtain ⟨ws, hws, rfl, hlt⟩ := slR_of_decHL m l.toNat o.toNat xs hxs hb
  simp only [UInt64.ofNat_toNat] at hws
  have := findW_ok n m o l x r ws hws h (by
    have := decHL_length m hxs
    simp only [List.length_map] at this; omega)
  rw [findIdx_map_decI x hx ws hlt]
  cases hf : ws.findIdx? (· == x) <;> rw [hf] at this <;> exact this


/-- **The model of `canon_name_map`** at the caller's fuel. -/
def nmW : Nat → Mem → Word → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, po, pl, co, cl, x =>
    match findW n m po pl x with
    | none => none
    | some r => if r.headD 0 = 0 then some x else some (getDW m co cl (r.tail.headD 0) x)

section specs
variable (p : Prog)

theorem canonNameMap_spec (hf : p.lookup "sl_find" = some slFind) (hg : p.lookup "sl_getd" = some slGetD)
    (hp : p.lookup "canon_name_map" = some canonNameMap) (n : Nat) (s₀ : St) (po pl co cl x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_name_map" [po, pl, co, cl, x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ nmW n s₀.mem po pl co cl x = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, canonNameMap]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slFind_spec p hf n, slGetD_specW p hg n] <;>
      finish (gen := 20) [nmW]

end specs

theorem nmW_ok {n : Nat} {m : Mem} {po pl co cl x y : Word} {ps cs : List NIdx}
    (h : nmW n m po pl co cl x = some y) (hps : decHL m po.toNat pl.toNat = some ps)
    (hcs : decHL m co.toNat cl.toNat = some cs) (hpb : po.toNat + pl.toNat < 2 ^ 64)
    (hcb : co.toNat + cl.toNat < 2 ^ 64) (hx : x.toNat < 2 ^ 32) :
    y.toNat < 2 ^ 32 ∧ decI y = ConRon.Arena.canonNameMap ps cs (decI x) := by
  cases n with
  | zero => simp [nmW] at h
  | succ n =>
  simp only [nmW] at h
  rcases hf : findW n m po pl x with _ | r <;> simp only [hf, reduceCtorEq] at h
  have hr := findW_handle hps hpb hx hf
  unfold ConRon.Arena.canonNameMap
  by_cases h0 : r.headD 0 = 0
  · rw [ite_eq_left h0] at h
    simp only [Option.some.injEq] at h; subst h
    cases hi : ps.findIdx? (fun p => p == decI x) with
    | none => simpa [hi] using hx
    | some i => rw [hi] at hr; simp [hr] at h0
  · rw [ite_eq_right h0] at h
    simp only [Option.some.injEq] at h; subst h
    cases hi : ps.findIdx? (fun p => p == decI x) with
    | none => rw [hi] at hr; simp [hr] at h0
    | some i =>
      rw [hi] at hr
      subst hr
      have hil : i < ps.length := by
        exact (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).1
      have hi64 : (UInt64.ofNat i).toNat = i := by
        have := decHL_length m hps
        simp; omega
      have := getDW_handle' hcs hcb (UInt64.ofNat i) x hx
      simp only [List.tail_cons, List.headD_cons, hi64] at this ⊢
      exact this


/-- **`canon_name_map` refines `canonNameMap`**: pure, memory untouched. -/
@[refines ConRon.Arena.canonNameMap]
theorem canonNameMap_refines (p : Prog) (hf : p.lookup "sl_find" = some slFind)
    (hg : p.lookup "sl_getd" = some slGetD)
    (hp : p.lookup "canon_name_map" = some canonNameMap) (n : Nat) (s₀ : St) (po pl co cl x : Word)
    (ps cs : List NIdx) (hps : decHL s₀.mem po.toNat pl.toNat = some ps)
    (hcs : decHL s₀.mem co.toNat cl.toNat = some cs) (hpb : po.toNat + pl.toNat < 2 ^ 64)
    (hcb : co.toNat + cl.toNat < 2 ^ 64) (hx : x.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_name_map" [po, pl, co, cl, x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      decI (r.headD 0) = ConRon.Arena.canonNameMap ps cs (decI x); ⊤⦄ := by
  refine triple_post (canonNameMap_spec p hf hg hp n s₀ po pl co cl x) ?_
  rintro r s' ⟨hl, hm, hr⟩
  obtain ⟨h1, h2⟩ := nmW_ok hr hps hcs hpb hcb hx
  exact ⟨hl, hm, h1, h2⟩

/-! ## `canon_level_eq` -/

mutual
/-- **The model of `canon_level_eq`**. -/
def cnClW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, po, pl, qo, ql, co, cl, fuel, u, v =>
    if fuel = 0 then none
    else cnClK0 n m po pl qo ql co cl fuel (lvNodeW m u) (lvNodeW m v)

/-- After the two `lv_node` calls. -/
def cnClK0 (n : Nat) (m : Mem) (po pl qo ql co cl fuel : Word) (ru rv : List Word) : Option Word :=
  if ru = [] ∨ rv = [] then none
  else if ru.headD 0 ≠ rv.headD 0 then some 0
  else if ru.headD 0 = 0 then some 1
  else if ru.headD 0 = 1 then
    cnClW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0)
  else if ru.headD 0 = 2 ∨ ru.headD 0 = 3 then
    cnClK1 n m po pl qo ql co cl fuel (ru.tail.tail.headD 0) (rv.tail.tail.headD 0)
      (cnClW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0))
  else if ru.headD 0 = 4 then
    cnClK2 n m qo ql co cl (rv.tail.headD 0) (nmW n m po pl co cl (ru.tail.headD 0))
  else some 0

/-- After the first child of a `max`/`imax`. -/
def cnClK1 (n : Nat) (m : Mem) (po pl qo ql co cl fuel a2 b2 : Word) : Option Word → Option Word
  | none => none
  | some r => if r = 0 then some 0 else cnClW n m po pl qo ql co cl (fuel - 1) a2 b2

/-- After the first `canon_name_map`. -/
def cnClK2 (n : Nat) (m : Mem) (qo ql co cl b1 : Word) : Option Word → Option Word
  | none => none
  | some x => cnClK3 x (nmW n m qo ql co cl b1)

/-- After the second. -/
def cnClK3 (x : Word) : Option Word → Option Word
  | none => none
  | some y => some (if x = y then 1 else 0)
end

section arms
variable (n : Nat) (m : Mem) (po pl qo ql co cl fuel u v a2 b2 b1 x y r : Word) (ru rv : List Word)
theorem clW_succ : cnClW (n + 1) m po pl qo ql co cl fuel u v =
    (if fuel = 0 then none else cnClK0 n m po pl qo ql co cl fuel (lvNodeW m u) (lvNodeW m v)) := by
  rw [cnClW]
theorem cnClK0_def : cnClK0 n m po pl qo ql co cl fuel ru rv =
    (if ru = [] ∨ rv = [] then none
  else if ru.headD 0 ≠ rv.headD 0 then some 0
  else if ru.headD 0 = 0 then some 1
  else if ru.headD 0 = 1 then
    cnClW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0)
  else if ru.headD 0 = 2 ∨ ru.headD 0 = 3 then
    cnClK1 n m po pl qo ql co cl fuel (ru.tail.tail.headD 0) (rv.tail.tail.headD 0)
      (cnClW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0))
  else if ru.headD 0 = 4 then
    cnClK2 n m qo ql co cl (rv.tail.headD 0) (nmW n m po pl co cl (ru.tail.headD 0))
  else some 0) := by
  rw [cnClK0]
theorem cnClK1_some : cnClK1 n m po pl qo ql co cl fuel a2 b2 (some r) =
    (if r = 0 then some 0 else cnClW n m po pl qo ql co cl (fuel - 1) a2 b2) := by
  rw [cnClK1]
theorem cnClK2_some : cnClK2 n m qo ql co cl b1 (some x) = cnClK3 x (nmW n m qo ql co cl b1) := rfl
theorem cnClK3_some : cnClK3 x (some y) = some (if x = y then 1 else 0) := rfl
end arms

grind_pattern [ind_grind] clW_succ => cnClW (n + 1) m po pl qo ql co cl fuel u v
grind_pattern [ind_grind] cnClK0_def => cnClK0 n m po pl qo ql co cl fuel ru rv
grind_pattern [ind_grind] cnClK1_some => cnClK1 n m po pl qo ql co cl fuel a2 b2 (some r)
grind_pattern [ind_grind] cnClK2_some => cnClK2 n m qo ql co cl b1 (some x)
grind_pattern [ind_grind] cnClK3_some => cnClK3 x (some y)


section specs2
variable (p : Prog) (hp : CanonProg p)
include hp

set_option maxHeartbeats 4000000 in
theorem canonLevelEq_spec (n : Nat) : ∀ (s₀ : St) (po pl qo ql co cl fuel u v : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_level_eq" [po, pl, qo, ql, co, cl, fuel, u, v]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      cnClW n s₀.mem po pl qo ql co cl fuel u v = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ po pl qo ql co cl fuel u v
    rw [invoke_eq _ (hp.get "canon_level_eq")]; simp only [callFn, canonLevelEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ po pl qo ql co cl fuel u v
    rw [invoke_eq _ (hp.get "canon_level_eq")]
    simp only [callFn, canonLevelEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lvNode_spec p (hp.get "lv_node") n,
        canonNameMap_spec p (hp.get "sl_find") (hp.get "sl_getd") (hp.get "canon_name_map") n, ih] <;>
      finish (gen := 20)

end specs2


theorem viewL_run' {a : AState} {h : LIdx} {v : LNodeView} (hv : a.store.lss.ls.view h = some v) :
    (viewL h).run a = .ok (v, a) := by
  have hv' : a.store.ls.view h = some v := hv
  simp [viewL, hv', StateT.run_bind, StateT.run_get]; rfl

theorem lvView {m : Mem} {a : AState} (hR : ArenaR m a) {u : Word} (hu : u.toNat < 2 ^ 32)
    (hne : lvNodeW m u ≠ []) :
    ∃ v, (viewL (decI u)).run a = .ok (v, a) ∧ lvNodeW m u = lvEnc v := by
  obtain ⟨v, hv⟩ := lview_of_lvNodeW hR hu hne
  exact ⟨v, viewL_run' hv, lvNodeW_store hR hu hv⟩

theorem andThen_ok {A B : AM Bool} {a : AState} {r r1 : Word} {b1 : Bool}
    (hA : A.run a = .ok (b1, a)) (hr1 : r1 = if b1 then 1 else 0)
    (hB : r1 ≠ 0 → ∃ b2, B.run a = .ok (b2, a) ∧ r = if b2 then 1 else 0) (h0 : r1 = 0 → r = 0) :
    ∃ b, (do let x ← A; if x = true then B else pure false : AM Bool).run a = .ok (b, a) ∧
      r = if b then 1 else 0 := by
  cases b1
  · refine ⟨false, ?_, by simp [h0 (by simpa using hr1)]⟩
    simp [StateT.run_bind, hA, exc_ok_bind']; rfl
  · obtain ⟨b2, hb2, hr⟩ := hB (by simp [hr1])
    refine ⟨b2, ?_, hr⟩
    simp [StateT.run_bind, hA, exc_ok_bind', hb2]

theorem clW_ok (n : Nat) : ∀ (m : Mem) (a : AState) (po pl qo ql co cl fuel u v r : Word)
    (ps qs cs : List NIdx), cnClW n m po pl qo ql co cl fuel u v = some r → ArenaR m a →
    CtxR m po pl qo ql co cl ps qs cs → u.toNat < 2 ^ 32 → v.toNat < 2 ^ 32 →
    ∃ b, (ConRon.Arena.canonLevelEq ps qs cs fuel.toNat (decI u) (decI v)).run a = .ok (b, a) ∧
      r = if b then 1 else 0 := by
  induction n with
  | zero => intro m a po pl qo ql co cl fuel u v r ps qs cs h; simp [cnClW] at h
  | succ n ih =>
    intro m a po pl qo ql co cl fuel u v r ps qs cs h hR hC hu hv
    rw [clW_succ] at h
    have hf : ¬ fuel = 0 := fun hf => by rw [ite_eq_left hf] at h; simp at h
    rw [ite_eq_right hf, cnClK0_def] at h
    have hne : ¬ (lvNodeW m u = [] ∨ lvNodeW m v = []) := fun hne => by rw [ite_eq_left hne] at h; simp at h
    rw [ite_eq_right hne] at h
    rw [not_or] at hne
    obtain ⟨vu, hru, hlu⟩ := lvView hR hu hne.1
    obtain ⟨vv, hrv, hlv⟩ := lvView hR hv hne.2
    have hfuel : fuel.toNat = (fuel - 1).toNat + 1 := toNat_pred hf
    rw [hfuel, ConRon.Arena.canonLevelEq.eq_2, StateT.run_bind, hru, exc_ok_bind', StateT.run_bind, hrv,
      exc_ok_bind']
    rw [hlu, hlv] at h
    cases vu <;> cases vv <;> simp only [lvEnc] at h <;> dsimp only <;> simp at h
    all_goals first
      | (exact ⟨false, rfl, by simp [← h]⟩)
      | (exact ⟨true, rfl, by simp [← h]⟩)
      | skip
    all_goals first
      | (-- succ.succ
         obtain ⟨b, hb, hr⟩ := ih m a po pl qo ql co cl (fuel - 1) _ _ r ps qs cs h hR hC
           (word_lt32 _) (word_lt32 _)
         rw [decI_word, decI_word] at hb
         exact ⟨b, hb, hr⟩)
      | (-- max.max, imax.imax
         generalize hx1 : cnClW n m po pl qo ql co cl (fuel - 1) _ _ = x1 at h
         cases x1 with
         | none => simp [cnClK1] at h
         | some r1 =>
         rw [cnClK1_some] at h
         obtain ⟨b1, hb1, hr1⟩ := ih m a po pl qo ql co cl (fuel - 1) _ _ r1 ps qs cs hx1 hR hC
           (word_lt32 _) (word_lt32 _)
         rw [decI_word, decI_word] at hb1
         refine andThen_ok hb1 hr1 (fun hne => ?_) (fun h0 => ?_)
         · rw [ite_eq_right hne] at h
           obtain ⟨b2, hb2, hr2⟩ := ih m a po pl qo ql co cl (fuel - 1) _ _ r ps qs cs h hR hC
             (word_lt32 _) (word_lt32 _)
           rw [decI_word, decI_word] at hb2
           exact ⟨b2, hb2, hr2⟩
         · rw [ite_eq_left h0] at h; simp at h; simp [← h])
      | (-- param.param
         unfold cnClK2 at h
         split at h
         · simp at h
         rename_i x hx
         unfold cnClK3 at h
         split at h
         · simp at h
         rename_i y hy
         simp only [Option.some.injEq] at h
         obtain ⟨hx32, hxd⟩ := nmW_ok hx hC.p hC.c (by have := iwTop_lt m; have := hC.pt; omega)
           (by have := iwTop_lt m; have := hC.ct; omega) (word_lt32 _)
         obtain ⟨hy32, hyd⟩ := nmW_ok hy hC.q hC.c (by have := iwTop_lt m; have := hC.qt; omega)
           (by have := iwTop_lt m; have := hC.ct; omega) (word_lt32 _)
         rw [decI_word] at hxd hyd
         refine ⟨ConRon.Arena.canonNameMap ps cs _ == ConRon.Arena.canonNameMap qs cs _, rfl, ?_⟩
         rw [← hxd, ← hyd, ← h]
         by_cases hxy : x = y
         · subst hxy; simp
         · have : decI x ≠ (decI y : NIdx) := fun e => hxy (decI_inj hx32 hy32 e)
           simp [hxy, this])


/-- The shape of a comparison that leaves memory and twin state alone. -/
theorem refAM_same {α : Type} [Inhabited α] (p : Prog) (f : FnName) (args : List Word)
    (pre : Mem → AState → Prop) (op : AM α) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (dec : Mem → List Word → α → Prop)
    (hpre : ∀ m a, pre m a → StageR dn vis fe m a)
    (h : ∀ (n : Nat) (s₀ : St) (a₀ : AState), pre s₀.mem a₀ →
      ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ ∃ x, op.run a₀ = .ok (x, a₀) ∧ dec s₀.mem r x; ⊤⦄) :
    RefAM p f args pre op (KeepPost dn vis fe dec) := by
  intro n s₀ a₀ hp
  refine triple_post (h n s₀ a₀ hp) ?_
  rintro r s' ⟨hl, hm, x, hx, hd⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hx
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres, hm]
  exact ⟨hpre _ _ hp, IWGrow.refl _, hd⟩

theorem decW0B_of' {m : Mem} {r : List Word} {b : Bool} (h : r.headD 0 = if b then 1 else 0) :
    decW0B m r b := by
  cases b <;> (simp only [decW0B]; rw [h]; simp)

/-- **`canon_level_eq` refines `canonLevelEq`.** -/
@[refines ConRon.Arena.canonLevelEq]
theorem canonLevelEq_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (po pl qo ql co cl fuel u v : Word) (ps qs cs : List NIdx) :
    RefAM p "canon_level_eq" [po, pl, qo, ql, co, cl, fuel, u, v]
      (fun m a => StageR dn vis fe m a ∧ CtxR m po pl qo ql co cl ps qs cs ∧ u.toNat < 2 ^ 32 ∧
        v.toNat < 2 ^ 32)
      (ConRon.Arena.canonLevelEq ps qs cs fuel.toNat (decI u) (decI v))
      (KeepPost dn vis fe decW0B) := by
  refine refAM_same p _ _ _ _ dn vis fe _ (fun m a h => h.1) ?_
  intro n s₀ a₀ ⟨hS, hC, hu, hv⟩
  refine triple_post (canonLevelEq_spec p hp n s₀ po pl qo ql co cl fuel u v) ?_
  rintro r s' ⟨hl, hm, hr⟩
  obtain ⟨b, hb, hrb⟩ := clW_ok n _ a₀ _ _ _ _ _ _ fuel u v _ ps qs cs hr hS.1.arena.1 hC hu hv
  exact ⟨hl, hm, b, hb, decW0B_of' hrb⟩


/-! ## `canon_level_list_eq` -/

theorem init11_0 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 0 = a0 := rfl
theorem init11_1 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 1 = a1 := rfl
theorem init11_2 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 2 = a2 := rfl
theorem init11_3 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 3 = a3 := rfl
theorem init11_4 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 4 = a4 := rfl
theorem init11_5 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 5 = a5 := rfl
theorem init11_6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 6 = a6 := rfl
theorem init11_7 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 7 = a7 := rfl
theorem init11_8 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 8 = a8 := rfl
theorem init11_9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 9 = a9 := rfl
theorem init11_10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] 10 = a10 := rfl


mutual
/-- **The model of `canon_level_list_eq`**. -/
def llW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option Word
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, po, pl, qo, ql, co, cl, fuel, ao, al, bo, bl =>
    if al = 0 ∧ bl = 0 then some 1
    else if al = 0 ∨ bl = 0 then some 0
    else llK1 n m po pl qo ql co cl fuel ao al bo bl
      (cnClW n m po pl qo ql co cl fuel (rdW (m.arr64 IW) ao) (rdW (m.arr64 IW) bo))

/-- After the head comparison. -/
def llK1 (n : Nat) (m : Mem) (po pl qo ql co cl fuel ao al bo bl : Word) : Option Word → Option Word
  | none => none
  | some r =>
    if r = 0 then some 0 else llW n m po pl qo ql co cl fuel (ao + 1) (al - 1) (bo + 1) (bl - 1)
end

section arms
variable (n : Nat) (m : Mem) (po pl qo ql co cl fuel ao al bo bl r : Word)
theorem llW_succ : llW (n + 1) m po pl qo ql co cl fuel ao al bo bl =
    (if al = 0 ∧ bl = 0 then some 1
    else if al = 0 ∨ bl = 0 then some 0
    else llK1 n m po pl qo ql co cl fuel ao al bo bl
      (cnClW n m po pl qo ql co cl fuel (rdW (m.arr64 IW) ao) (rdW (m.arr64 IW) bo))) := by
  rw [llW]
theorem llK1_some : llK1 n m po pl qo ql co cl fuel ao al bo bl (some r) =
    (if r = 0 then some 0 else llW n m po pl qo ql co cl fuel (ao + 1) (al - 1) (bo + 1) (bl - 1)) := by
  rw [llK1]
end arms

grind_pattern [ind_grind] llW_succ => llW (n + 1) m po pl qo ql co cl fuel ao al bo bl
grind_pattern [ind_grind] llK1_some => llK1 n m po pl qo ql co cl fuel ao al bo bl (some r)

section specs3
variable (p : Prog) (hp : CanonProg p)
include hp

set_option maxHeartbeats 4000000 in
theorem canonLevelListEq_spec (n : Nat) : ∀ (s₀ : St) (po pl qo ql co cl fuel ao al bo bl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_level_list_eq"
      [po, pl, qo, ql, co, cl, fuel, ao, al, bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      llW n s₀.mem po pl qo ql co cl fuel ao al bo bl = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ po pl qo ql co cl fuel ao al bo bl
    rw [invoke_eq _ (hp.get "canon_level_list_eq")]; simp only [callFn, canonLevelListEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ po pl qo ql co cl fuel ao al bo bl
    rw [invoke_eq _ (hp.get "canon_level_list_eq")]
    simp only [callFn, canonLevelListEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        canonLevelEq_spec p hp n, ih] <;>
      finish (gen := 20) [rdW_eq, init11_0, init11_1, init11_2, init11_3, init11_4, init11_5, init11_6, init11_7, init11_8, init11_9, init11_10]

end specs3

theorem llW_ok (n : Nat) : ∀ (m : Mem) (a : AState) (po pl qo ql co cl fuel ao al bo bl r : Word)
    (ws1 ws2 : List Word) (ps qs cs : List NIdx), llW n m po pl qo ql co cl fuel ao al bo bl = some r →
    ArenaR m a → CtxR m po pl qo ql co cl ps qs cs → SlR m ao al ws1 → SlR m bo bl ws2 →
    (∀ w ∈ ws1, w.toNat < 2 ^ 32) → (∀ w ∈ ws2, w.toNat < 2 ^ 32) →
    ∃ b, (ConRon.Arena.canonLevelListEq ps qs cs fuel.toNat (ws1.map decI) (ws2.map decI)).run a =
      .ok (b, a) ∧ r = if b then 1 else 0 := by
  induction n with
  | zero => intro m a po pl qo ql co cl fuel ao al bo bl r ws1 ws2 ps qs cs h; simp [llW] at h
  | succ n ih =>
    intro m a po pl qo ql co cl fuel ao al bo bl r ws1 ws2 ps qs cs h hR hC h1 h2 hw1 hw2
    rw [llW_succ] at h
    cases h1 with
    | nil =>
      cases h2 with
      | nil =>
        simp at h
        exact ⟨true, by simp [ConRon.Arena.canonLevelListEq]; rfl, by simp [← h]⟩
      | cons hl2 h2' =>
        have : bl ≠ 0 := hl2
        simp [this] at h
        exact ⟨false, by simp [ConRon.Arena.canonLevelListEq]; rfl, by simp [← h]⟩
    | @cons ao' al' ws1' hl1 h1' =>
      cases h2 with
      | nil =>
        simp [hl1] at h
        exact ⟨false, by simp [ConRon.Arena.canonLevelListEq]; rfl, by simp [← h]⟩
      | @cons bo' bl' ws2' hl2 h2' =>
        simp only [hl1, hl2, false_and, ↓reduceIte, or_self] at h
        unfold llK1 at h
        split at h
        · simp at h
        rename_i r1 hx1
        have hh1 : (rdW (m.arr64 IW) ao).toNat < 2 ^ 32 := hw1 _ (by simp)
        have hh2 : (rdW (m.arr64 IW) bo).toNat < 2 ^ 32 := hw2 _ (by simp)
        obtain ⟨b1, hb1, hr1⟩ := clW_ok n m a po pl qo ql co cl fuel _ _ r1 ps qs cs hx1 hR hC hh1 hh2
        simp only [List.map_cons]
        rw [ConRon.Arena.canonLevelListEq.eq_2]
        refine andThen_ok hb1 hr1 (fun hne => ?_) (fun h0 => ?_)
        · rw [ite_eq_right hne] at h
          exact ih m a po pl qo ql co cl fuel _ _ _ _ r ws1' ws2' ps qs cs h hR hC h1' h2'
            (fun w hw => hw1 w (by simp [hw])) (fun w hw => hw2 w (by simp [hw]))
        · rw [ite_eq_left h0] at h; simp at h; simp [← h]


/-- **`canon_level_list_eq` refines `canonLevelListEq`.** -/
@[refines ConRon.Arena.canonLevelListEq]
theorem canonLevelListEq_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (po pl qo ql co cl fuel ao al bo bl : Word) (ps qs cs : List NIdx)
    (xs ys : List LIdx) :
    RefAM p "canon_level_list_eq" [po, pl, qo, ql, co, cl, fuel, ao, al, bo, bl]
      (fun m a => StageR dn vis fe m a ∧ CtxR m po pl qo ql co cl ps qs cs ∧
        decHL m ao.toNat al.toNat = some xs ∧ decHL m bo.toNat bl.toNat = some ys ∧
        ao.toNat + al.toNat ≤ iwTop m ∧ bo.toNat + bl.toNat ≤ iwTop m)
      (ConRon.Arena.canonLevelListEq ps qs cs fuel.toNat xs ys)
      (KeepPost dn vis fe decW0B) := by
  refine refAM_same p _ _ _ _ dn vis fe _ (fun m a h => h.1) ?_
  intro n s₀ a₀ ⟨hS, hC, hx, hy, hxt, hyt⟩
  refine triple_post (canonLevelListEq_spec p hp n s₀ po pl qo ql co cl fuel ao al bo bl) ?_
  rintro r s' ⟨hl, hm, hr⟩
  have t := iwTop_lt s₀.mem
  obtain ⟨ws1, hs1, rfl, hw1⟩ := slR_of_decHL s₀.mem al.toNat ao.toNat xs hx (by omega)
  obtain ⟨ws2, hs2, rfl, hw2⟩ := slR_of_decHL s₀.mem bl.toNat bo.toNat ys hy (by omega)
  simp only [UInt64.ofNat_toNat] at hs1 hs2
  obtain ⟨b, hb, hrb⟩ := llW_ok n _ a₀ _ _ _ _ _ _ fuel ao al bo bl _ ws1 ws2 ps qs cs hr
    hS.1.arena.1 hC hs1 hs2 hw1 hw2
  exact ⟨hl, hm, b, hb, decW0B_of' hrb⟩


/-! ## `canon_levels_eq` -/

theorem init9_0 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 0 = a0 := rfl
theorem init9_1 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 1 = a1 := rfl
theorem init9_2 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 2 = a2 := rfl
theorem init9_3 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 3 = a3 := rfl
theorem init9_4 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 4 = a4 := rfl
theorem init9_5 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 5 = a5 := rfl
theorem init9_6 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 6 = a6 := rfl
theorem init9_7 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 7 = a7 := rfl
theorem init9_8 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) : Locals.init [a0, a1, a2, a3, a4, a5, a6, a7, a8] 8 = a8 := rfl

/-- **The model of `canon_levels_eq`**: two `view_ls`, then the list comparison. -/
def lsEqW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, po, pl, qo, ql, co, cl, fuel, us, vs =>
    match viewLsW n m us with
    | none => none
    | some (r1, m1) =>
      match viewLsW n m1 vs with
      | none => none
      | some (r2, m2) =>
        match llW n m2 po pl qo ql co cl fuel (r1.headD 0) (r1.tail.headD 0) (r2.headD 0)
            (r2.tail.headD 0) with
        | none => none
        | some r => some (r, m2)

set_option maxHeartbeats 4000000 in
theorem canonLevelsEq_spec (p : Prog) (hp : CanonProg p) (n : Nat) (s₀ : St)
    (po pl qo ql co cl fuel us vs : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_levels_eq"
      [po, pl, qo, ql, co, cl, fuel, us, vs]
    ⦃fun r s' => LocEq s' s₀ ∧ lsEqW n s₀.mem po pl qo ql co cl fuel us vs = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ (hp.get "canon_levels_eq")]
  simp only [callFn, canonLevelsEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        viewLs_specW p (hp.get "ls_node") (hp.get "iw_alloc") (hp.get "pool_copy") (hp.get "view_ls") n,
        canonLevelListEq_spec p hp n] <;>
      finish (gen := 20) [rdW_eq, lsEqW, init11_0, init11_1, init11_2, init11_3, init11_4, init11_5,
        init11_6, init11_7, init11_8, init11_9, init11_10, init9_0, init9_1, init9_2, init9_3,
        init9_4, init9_5, init9_6, init9_7, init9_8]


theorem getD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by cases r <;> rfl
theorem cnGetD1 (r : List Word) : r.getD (0 + 1) 0 = r.tail.headD 0 := by
  cases r with
  | nil => rfl
  | cons x xs => cases xs <;> rfl

theorem decRL_unpack {k : IdxKind} {m : Mem} {r : List Word} {ids : List (Idx k)}
    (h : decRL (fun m => decHL m) 0 m r ids) :
    decHL m (r.headD 0).toNat (r.tail.headD 0).toNat = some ids ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m := by
  simpa only [decRL, getD0, cnGetD1] using h

theorem lsEqW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat)
    {m m' : Mem} {a : AState} {po pl qo ql co cl fuel us vs r : Word} {ps qs cs : List NIdx}
    (h : lsEqW n m po pl qo ql co cl fuel us vs = some (r, m')) (hS : StageR dn vis fe m a)
    (hC : CtxR m po pl qo ql co cl ps qs cs) (hu : us.toNat < 2 ^ 32) (hv : vs.toNat < 2 ^ 32)
    (hP : PoolSmall m) :
    ∃ b, (ConRon.Arena.canonLevelsEq ps qs cs fuel.toNat (decI us) (decI vs)).run a = .ok (b, a) ∧
      r = (if b then 1 else 0) ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m' := by
  cases n with
  | zero => simp [lsEqW] at h
  | succ n =>
  rw [lsEqW] at h
  cases h1 : viewLsW n m us with
  | none => rw [h1] at h; simp at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h; dsimp only at h
  cases h2 : viewLsW n m1 vs with
  | none => rw [h2] at h; simp at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2] at h; dsimp only at h
  cases hll : llW n m2 po pl qo ql co cl fuel (r1.headD 0) (r1.tail.headD 0) (r2.headD 0)
      (r2.tail.headD 0) with
  | none => rw [hll] at h; simp at h
  | some rr =>
  rw [hll] at h; dsimp only at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨ids1, hrun1, hS1, hg1, hd1, hP1⟩ := viewLsW_ok h1 hS hu hP
  obtain ⟨ids2, hrun2, hS2, hg2, hd2, hP2⟩ := viewLsW_ok h2 hS1 hv hP1
  have t := iwTop_lt m
  have t2 := iwTop_lt m2
  have hd1u := decRL_unpack hd1
  have hd2u := decRL_unpack hd2
  have hd1' : decHL m2 (r1.headD 0).toNat (r1.tail.headD 0).toNat = some ids1 := by
    rw [decHL_grow hg2 hd1u.2]; exact hd1u.1
  have hC2 := (hC.grow hg1).grow hg2
  obtain ⟨ws1, hs1, rfl, hw1⟩ := slR_of_decHL m2 _ _ ids1 hd1' (by have := hd1u.2; have := hg2.1; omega)
  obtain ⟨ws2, hs2, rfl, hw2⟩ := slR_of_decHL m2 _ _ ids2 hd2u.1 (by have := hd2u.2; omega)
  simp only [UInt64.ofNat_toNat] at hs1 hs2
  obtain ⟨b, hb, hrb⟩ := llW_ok n m2 a po pl qo ql co cl fuel _ _ _ _ rr _ _ ps qs cs hll
    hS2.1.arena.1 hC2 hs1 hs2 hw1 hw2
  refine ⟨b, ?_, hrb, hS2, hg1.trans hg2, hP2⟩
  unfold ConRon.Arena.canonLevelsEq
  rw [StateT.run_bind, hrun1, exc_ok_bind', StateT.run_bind, hrun2, exc_ok_bind']
  exact hb


/-- The post of a comparison that may grow the pool: the usual one, and the pool array stays
addressable by a word (`PoolSmall`). -/
def CPost {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (dec : Mem → List Word → α → Prop) (m m' : Mem) (a : AState) (r : List Word) (x : α) : Prop :=
  KeepPost dn vis fe dec m m' a r x ∧ PoolSmall m'

/-- **`canon_levels_eq` refines `canonLevelsEq`.** -/
@[refines ConRon.Arena.canonLevelsEq]
theorem canonLevelsEq_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (po pl qo ql co cl fuel us vs : Word) (ps qs cs : List NIdx) :
    RefAM p "canon_levels_eq" [po, pl, qo, ql, co, cl, fuel, us, vs]
      (fun m a => StageR dn vis fe m a ∧ CtxR m po pl qo ql co cl ps qs cs ∧ us.toNat < 2 ^ 32 ∧
        vs.toNat < 2 ^ 32 ∧ PoolSmall m)
      (ConRon.Arena.canonLevelsEq ps qs cs fuel.toNat (decI us) (decI vs))
      (CPost dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hC, hu, hv, hP⟩
  refine triple_post (canonLevelsEq_spec p hp n s₀ po pl qo ql co cl fuel us vs) ?_
  rintro r s' ⟨hl, hr⟩
  obtain ⟨b, hb, hrb, hS', hg, hP'⟩ := lsEqW_ok n hr hS hC hu hv hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hb
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact ⟨⟨hS', hg, decW0B_of' hrb⟩, hP'⟩

end L.Ind
