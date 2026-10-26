import ConAgua.Arena.DeclReduceSpec2

/-!
# The `ofReduce*` axioms: `of_reduce_ax_ok(vis, q)` refines `ofReduceAxOk` (lane `decls3`)

The pinned `Eq` basis (`find_is` against `rom_ci(0)`), the element inductive and the stored reduce
opaque (`reduce_elem_ok`, `reduce_stored_ok`), the pin (`of_reduce_pin_a`, `matches_pin`). L
change: the axiom's name word loaded once into a local (it was loaded inside two call arguments).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

section model
variable (p : Prog)

/-- After `of_reduce_pin_a`: the comparison. -/
def oraK7 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) => mpW m7 q (r7.headD 0)

/-- After `reduce_stored_ok`. -/
def oraK6 (n : Nat) (q nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    if r6.headD 0 = 0 then some ([0], m6) else oraK7 q (callW p n "of_reduce_pin_a" [nm] m6)

/-- After `reduce_elem_ok`. -/
def oraK5 (n : Nat) (vis q nm c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) =>
    if r5.headD 0 = 0 then some ([0], m5)
    else oraK6 p n q nm (callW p n "reduce_stored_ok" [vis, c] m5)

/-- After `find_is`. -/
def oraK4 (n : Nat) (vis q nm c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) =>
    if r4.headD 0 = 0 then some ([0], m4)
    else oraK5 p n vis q nm c (callW p n "reduce_elem_ok" [vis, c] m4)

/-- After `rom_ci(0)`. -/
def oraK3 (n : Nat) (vis q nm c en : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => oraK4 p n vis q nm c (callW p n "find_is" [vis, en, r3.headD 0] m3)

/-- After the `Eq` pin. -/
def oraK2 (n : Nat) (vis q nm c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => oraK3 p n vis q nm c (r2.headD 0) (callW p n "rom_ci" [0] m2)

/-- After `of_reduce_op`. -/
def oraK1 (n : Nat) (vis q nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => oraK2 p n vis q nm (r1.headD 0) (pinAtW m1 0)

/-- **The model of `of_reduce_ax_ok(vis, q)`.** -/
def oraW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q =>
    oraK1 p n vis q (rdW (m.arr64 EREC) q) (oroW m (rdW (m.arr64 EREC) q))

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 m6 m7 : Mem) (vis q nm c en : Word)
  (r1 r2 r3 r4 r5 r6 r7 : List Word)
theorem oraW_step : oraW p (n + 1) m vis q =
    oraK1 p n vis q (rdW (m.arr64 EREC) q) (oroW m (rdW (m.arr64 EREC) q)) := rfl
theorem oraK1_some : oraK1 p n vis q nm (some (r1, m1)) =
    oraK2 p n vis q nm (r1.headD 0) (pinAtW m1 0) := rfl
theorem oraK2_some : oraK2 p n vis q nm c (some (r2, m2)) =
    oraK3 p n vis q nm c (r2.headD 0) (callW p n "rom_ci" [0] m2) := rfl
theorem oraK3_some : oraK3 p n vis q nm c en (some (r3, m3)) =
    oraK4 p n vis q nm c (callW p n "find_is" [vis, en, r3.headD 0] m3) := rfl
theorem oraK4_some : oraK4 p n vis q nm c (some (r4, m4)) =
    if r4.headD 0 = 0 then some ([0], m4)
    else oraK5 p n vis q nm c (callW p n "reduce_elem_ok" [vis, c] m4) := rfl
theorem oraK5_some : oraK5 p n vis q nm c (some (r5, m5)) =
    if r5.headD 0 = 0 then some ([0], m5)
    else oraK6 p n q nm (callW p n "reduce_stored_ok" [vis, c] m5) := rfl
theorem oraK6_some : oraK6 p n q nm (some (r6, m6)) =
    if r6.headD 0 = 0 then some ([0], m6) else oraK7 q (callW p n "of_reduce_pin_a" [nm] m6) := rfl
theorem oraK7_some : oraK7 q (some (r7, m7)) = mpW m7 q (r7.headD 0) := rfl
end arms

grind_pattern [ind_grind] oraW_step => oraW p (n + 1) m vis q
grind_pattern [ind_grind] oraK1_some => oraK1 p n vis q nm (some (r1, m1))
grind_pattern [ind_grind] oraK2_some => oraK2 p n vis q nm c (some (r2, m2))
grind_pattern [ind_grind] oraK3_some => oraK3 p n vis q nm c en (some (r3, m3))
grind_pattern [ind_grind] oraK4_some => oraK4 p n vis q nm c (some (r4, m4))
grind_pattern [ind_grind] oraK5_some => oraK5 p n vis q nm c (some (r5, m5))
grind_pattern [ind_grind] oraK6_some => oraK6 p n q nm (some (r6, m6))
grind_pattern [ind_grind] oraK7_some => oraK7 q (some (r7, m7))

/-- The lookups of `of_reduce_ax_ok`. -/
structure OraProg (p : Prog) : Prop where
  red : RedProg p
  ora : p.lookup "of_reduce_ax_ok" = some ofReduceAxOkL
  oro : p.lookup "of_reduce_op" = some ofReduceOpL
  orp : p.lookup "of_reduce_pin_a" = some ofReducePinAL

set_option maxHeartbeats 1600000 in
theorem ora_specW (h : OraProg p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "of_reduce_ax_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ oraW p n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.ora]
  simp only [callFn, ofReduceAxOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        oro_specW p h.red.pa h.oro n, pinAt_specW p h.red.pa n, callW_spec p n "rom_ci",
        callW_spec p n "find_is", callW_spec p n "reduce_elem_ok",
        callW_spec p n "reduce_stored_ok", callW_spec p n "of_reduce_pin_a",
        mp_specW p h.red.canon h.red.mp n] <;>
      finish (gen := 20) [rdW_eq, mpW]

end model

/-- **`of_reduce_ax_ok(vis, q)` refines `ofReduceAxOk`** at the model level. -/
theorem oraW_ok {p : Prog} (h : OraProg p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal} (hW : oraW p n m vis q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    ∃ b a', (ofReduceAxOk fe cv).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨⟨wn, hwn, hwnl, hname⟩, -, -⟩ := decCV_words hq
  have ewn : rdW (m.arr64 EREC) q = wn := rdW_of_get? rfl (erecP_get hwn)
  cases n with
  | zero => simp [oraW] at hW
  | succ n =>
  rw [oraW_step, ewn] at hW
  -- `of_reduce_op`
  rcases h1 : oroW m wn with _ | ⟨r1, m1⟩ <;> simp only [h1, oraK1, reduceCtorEq] at hW
  obtain ⟨rfl, hcl, hrun1⟩ := oroW_ok h1 hS.1.pins hwnl
  generalize r1.headD 0 = c at hW hcl hrun1
  -- the `Eq` pin and `eqA`
  rcases h2 : pinAtW m1 0 with _ | ⟨r2, m2⟩ <;> simp only [h2, oraK2, reduceCtorEq] at hW
  obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok h2 hS.1.pins
  rw [hm2, hr2] at hW
  simp only [List.headD_cons] at hW
  rcases h3 : callW p n "rom_ci" [0] m1 with _ | ⟨r3, m3⟩ <;> simp only [h3, oraK3, reduceCtorEq] at hW
  obtain ⟨ea, a3, hrun3, hS3, hg3, hea⟩ := h.red.rom.ci dn vis fe 0 (by decide) n _ a r3 m3 hS h3
  have hrun3' : eqA.run a = .ok (ea, a3) := hrun3
  -- `find_is`
  rcases h4 : callW p n "find_is" [vis, pinW m1 (1 + (0 : Word).toNat), r3.headD 0] m3 with _ | ⟨r4, m4⟩ <;> simp only [h4, oraK4, reduceCtorEq] at hW
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (findIs_spec p h.red.canon dn vis fe hdn _ _ ea n ⟨m3, Locals.init []⟩ a3
      ⟨hS3, hl2, decRCI_get hea⟩) h4
  subst hs4
  simp only [AM.st_pure, AM.res_pure] at hS4 hb4
  have hpre : (ofReduceAxOk fe cv).run a =
      (if fe.find? (decI (pinW m1 (1 + (0 : Word).toNat))) != some ea then pure false
       else (do
        if !(← reduceElemOk fe (decI c)) then pure false
        else if !(← reduceStoredOk fe (decI c)) then pure false
        else cv.matchesPin (← ofReducePinA cv.name)) : AM Bool).run a3 := by
    simp only [ofReduceAxOk, StateT.run_bind, hname, hrun1, exc_ok_bind', pinEq,
      show PIN_EQ = (0 : Word).toNat from rfl, hrun2, hrun3']
  by_cases e4 : r4.headD 0 = 0
  · rw [ite_eq_left e4] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hf : (fe.find? (decI (pinW m1 (1 + (0 : Word).toNat))) == some ea) = false := by
      rw [← hb4]; simpa using e4
    refine ⟨false, a3, ?_, hS4, hg3.trans hg4, by simp [decW0B]⟩
    rw [hpre]
    simp only [bne, hf, Bool.not_false, ite_true]
    rfl
  rw [ite_eq_right e4] at hW
  have ht : (fe.find? (decI (pinW m1 (1 + (0 : Word).toNat))) == some ea) = true := by
    rw [← hb4]; simpa using e4
  rw [hpre]
  simp only [bne, ht, Bool.not_true, Bool.false_eq_true, ite_false]
  -- `reduce_elem_ok`
  rcases h5 : callW p n "reduce_elem_ok" [vis, c] s4.mem with _ | ⟨r5, m5⟩ <;> simp only [h5, oraK5, reduceCtorEq] at hW
  obtain ⟨s5, hs5, -, hok5, hS5, hg5, hb5, -⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (reduceElemOk_refines p h.red dn hdn vis fe c hcl n ⟨s4.mem, Locals.init []⟩ a3 hS4) h5
  subst hs5
  have hrun5 := AM.run_of_ok _ _ hok5
  generalize AM.res (reduceElemOk fe (decI c)) a3 = b5 at hrun5 hb5
  generalize AM.st (reduceElemOk fe (decI c)) a3 = a5 at hrun5 hS5
  simp only [StateT.run_bind, hrun5, exc_ok_bind']
  by_cases e5 : r5.headD 0 = 0
  · rw [ite_eq_left e5] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hf : b5 = false := by rw [← hb5]; simpa using e5
    refine ⟨false, a5, by simp [hf]; rfl, hS5, hg3.trans (hg4.trans hg5), by simp [decW0B]⟩
  rw [ite_eq_right e5] at hW
  have ht5 : b5 = true := by rw [← hb5]; simpa using e5
  simp only [ht5, Bool.not_true, Bool.false_eq_true, ite_false]
  -- `reduce_stored_ok`
  rcases h6 : callW p n "reduce_stored_ok" [vis, c] s5.mem with _ | ⟨r6, m6⟩ <;> simp only [h6, oraK6, reduceCtorEq] at hW
  obtain ⟨s6, hs6, -, hok6, hS6, hg6, hb6, -⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (reduceStoredOk_refines p h.red dn vis fe c hcl n ⟨s5.mem, Locals.init []⟩ a5 hS5) h6
  subst hs6
  have hrun6 := AM.run_of_ok _ _ hok6
  generalize AM.res (reduceStoredOk fe (decI c)) a5 = b6 at hrun6 hb6
  generalize AM.st (reduceStoredOk fe (decI c)) a5 = a6 at hrun6 hS6
  simp only [StateT.run_bind, hrun6, exc_ok_bind']
  by_cases e6 : r6.headD 0 = 0
  · rw [ite_eq_left e6] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hf : b6 = false := by rw [← hb6]; simpa using e6
    refine ⟨false, a6, by simp [hf]; rfl, hS6, hg3.trans (hg4.trans (hg5.trans hg6)),
      by simp [decW0B]⟩
  rw [ite_eq_right e6] at hW
  have ht6 : b6 = true := by rw [← hb6]; simpa using e6
  simp only [ht6, Bool.not_true, Bool.false_eq_true, ite_false]
  -- the pin
  rcases h7 : callW p n "of_reduce_pin_a" [wn] s6.mem with _ | ⟨r7, m7⟩ <;> simp only [h7, oraK7, reduceCtorEq] at hW
  obtain ⟨s7, hs7, -, hok7, hS7, hg7, hpin⟩ := triple_of_callW (s₀ := ⟨s6.mem, Locals.init []⟩)
    (ofReducePinA_refines p h.red.pa n ⟨s6.mem, Locals.init []⟩ a6 dn fe vis wn hS6 hwnl h.red.rom h.orp) h7
  subst hs7
  have hrun7 := AM.run_of_ok _ _ hok7
  have hg := hg3.trans (hg4.trans (hg5.trans (hg6.trans hg7)))
  have hq7 : decCV (erA s7.mem) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg) hq
  obtain ⟨hm8, hrun8, hd8⟩ := mpW_ok (a := AM.st (ofReducePinA (decI wn)) a6) hW
    hS7.2.2.2.2.1 hq7 (DecB.get ⟨fun _ _ _ he h => he.2.decCV h⟩ hpin)
  subst hm8
  refine ⟨_, _, ?_, hS7, hg, hd8⟩
  rw [hname]
  simp only [StateT.run_bind, hrun7, exc_ok_bind']
  exact hrun8

/-- **`of_reduce_ax_ok(vis, q)` refines `ofReduceAxOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.ofReduceAxOk]
theorem ofReduceAxOk_refines (p : Prog) (h : OraProg p) (dn : NIdx → Option ConLeche.Name)
    (hdn : DnInj dn) (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "of_reduce_ax_ok" [vis, q]
      (fun m a => StageR dn vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (ofReduceAxOk fe cv) (KeepPost dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hq⟩
  refine triple_post (ora_specW p h n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := oraW_ok h hdn hm hS hq
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

end L.Arena
