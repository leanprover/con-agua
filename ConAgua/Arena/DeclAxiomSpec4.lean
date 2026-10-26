import ConAgua.Arena.DeclAxiomSpec3

/-!
# `std_axiom_ok(vis, q)` refines `stdAxiomOk` (lane `decls3`)

The model runs the three clauses of a family (`famK*`: pin, `find_pinned`, abort-free `0` on a
miss) for `propext` (after the pinned `Eq` test) or `Classical.choice`; the relational lemma runs
`stdAxiomOk_eq`'s flattened twin. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

section model
variable (p : Prog) (n : Nat) (vis q : Word)

/-- The family's end: the axiom's own pin. -/
def famK7 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => mpW m q (r.headD 0)

/-- After the third clause. -/
def famK6 (cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then some ([0], m) else famK7 q (callW p n "rom_cv" [cvid] m)

/-- After the third pin. -/
def famK5 (i3 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => famK6 p n q cvid (callW p n "find_pinned" [vis, r.headD 0, 5, c3, c3, i3] m)

/-- After the second clause. -/
def famK4 (s3 i3 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then some ([0], m) else famK5 p n vis q i3 c3 cvid (pinAtW m s3)

/-- After the second pin. -/
def famK3 (s3 i2 i3 c2 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    famK4 p n vis q s3 i3 c3 cvid (callW p n "find_pinned" [vis, r.headD 0, 4, c2, c2, i2] m)

/-- After the first clause. -/
def famK2 (s2 s3 i2 i3 c2 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0], m) else famK3 p n vis q s3 i2 i3 c2 c3 cvid (pinAtW m s2)

/-- After the first pin. -/
def famK1 (s2 s3 i1 i2 i3 c2 c3 cvid : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    famK2 p n vis q s2 s3 i2 i3 c2 c3 cvid (callW p n "find_pinned" [vis, r.headD 0, 3, 0, 0, i1] m)

/-- After a family. -/
def stdRet : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- `propext`: after `find_is`. -/
def stdP3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0], m)
    else stdRet (callW p n "std_ax_family" [vis, q, 34, 35, 36, 2, 3, 4, 2, 4, 0] m)

/-- `propext`: after `rom_ci(0)`. -/
def stdP2 (en : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => stdP3 p n vis q (callW p n "find_is" [vis, en, r.headD 0] m)

/-- `propext`: after the `Eq` pin. -/
def stdP1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => stdP2 p n vis q (r.headD 0) (callW p n "rom_ci" [0] m)

/-- `choice`: after its pin. -/
def stdC1 (nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = r.headD 0 then stdRet (callW p n "std_ax_family" [vis, q, 37, 38, 39, 5, 6, 7, 1, 3, 1] m)
    else some ([0], m)

/-- After the `propext` pin. -/
def stdK1 (nm : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if nm = r.headD 0 then stdP1 p n vis q (pinAtW m 0) else stdC1 p n vis q nm (pinAtW m 33)

end model

/-- **The model of `std_ax_family(vis, q, s1, …)`.** -/
def famW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid =>
    famK1 p n vis q s2 s3 i1 i2 i3 c2 c3 cvid (pinAtW m s1)

/-- **The model of `std_axiom_ok(vis, q)`.** -/
def stdW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q => stdK1 p n vis q (rdW (m.arr64 EREC) q) (pinAtW m 32)

section arms
variable (p : Prog) (n : Nat) (vis q nm en s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word) (r : List Word)
  (m : Mem)
theorem famW_step : famW p (n + 1) m vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid =
    famK1 p n vis q s2 s3 i1 i2 i3 c2 c3 cvid (pinAtW m s1) := rfl
theorem stdW_step : stdW p (n + 1) m vis q = stdK1 p n vis q (rdW (m.arr64 EREC) q) (pinAtW m 32) :=
  rfl
theorem stdK1_some : stdK1 p n vis q nm (some (r, m)) =
    if nm = r.headD 0 then stdP1 p n vis q (pinAtW m 0) else stdC1 p n vis q nm (pinAtW m 33) := rfl
theorem stdC1_some : stdC1 p n vis q nm (some (r, m)) =
    if nm = r.headD 0 then stdRet (callW p n "std_ax_family" [vis, q, 37, 38, 39, 5, 6, 7, 1, 3, 1] m)
    else some ([0], m) := rfl
theorem stdP1_some : stdP1 p n vis q (some (r, m)) =
    stdP2 p n vis q (r.headD 0) (callW p n "rom_ci" [0] m) := rfl
theorem stdP2_some : stdP2 p n vis q en (some (r, m)) =
    stdP3 p n vis q (callW p n "find_is" [vis, en, r.headD 0] m) := rfl
theorem stdP3_some : stdP3 p n vis q (some (r, m)) =
    if r.headD 0 = 0 then some ([0], m)
    else stdRet (callW p n "std_ax_family" [vis, q, 34, 35, 36, 2, 3, 4, 2, 4, 0] m) := rfl
theorem stdRet_some : stdRet (some (r, m)) = some ([r.headD 0], m) := rfl
theorem famK1_some : famK1 p n vis q s2 s3 i1 i2 i3 c2 c3 cvid (some (r, m)) =
    famK2 p n vis q s2 s3 i2 i3 c2 c3 cvid
      (callW p n "find_pinned" [vis, r.headD 0, 3, 0, 0, i1] m) := rfl
theorem famK2_some : famK2 p n vis q s2 s3 i2 i3 c2 c3 cvid (some (r, m)) =
    if r.headD 0 = 0 then some ([0], m) else famK3 p n vis q s3 i2 i3 c2 c3 cvid (pinAtW m s2) :=
  rfl
theorem famK3_some : famK3 p n vis q s3 i2 i3 c2 c3 cvid (some (r, m)) =
    famK4 p n vis q s3 i3 c3 cvid (callW p n "find_pinned" [vis, r.headD 0, 4, c2, c2, i2] m) := rfl
theorem famK4_some : famK4 p n vis q s3 i3 c3 cvid (some (r, m)) =
    if r.headD 0 = 0 then some ([0], m) else famK5 p n vis q i3 c3 cvid (pinAtW m s3) := rfl
theorem famK5_some : famK5 p n vis q i3 c3 cvid (some (r, m)) =
    famK6 p n q cvid (callW p n "find_pinned" [vis, r.headD 0, 5, c3, c3, i3] m) := rfl
theorem famK6_some : famK6 p n q cvid (some (r, m)) =
    if r.headD 0 = 0 then some ([0], m) else famK7 q (callW p n "rom_cv" [cvid] m) := rfl
theorem famK7_some : famK7 q (some (r, m)) = mpW m q (r.headD 0) := rfl
end arms

grind_pattern [ind_grind] famW_step => famW p (n + 1) m vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid
grind_pattern [ind_grind] stdW_step => stdW p (n + 1) m vis q
grind_pattern [ind_grind] stdK1_some => stdK1 p n vis q nm (some (r, m))
grind_pattern [ind_grind] stdC1_some => stdC1 p n vis q nm (some (r, m))
grind_pattern [ind_grind] stdP1_some => stdP1 p n vis q (some (r, m))
grind_pattern [ind_grind] stdP2_some => stdP2 p n vis q en (some (r, m))
grind_pattern [ind_grind] stdP3_some => stdP3 p n vis q (some (r, m))
grind_pattern [ind_grind] stdRet_some => stdRet (some (r, m))
grind_pattern [ind_grind] famK1_some => famK1 p n vis q s2 s3 i1 i2 i3 c2 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK2_some => famK2 p n vis q s2 s3 i2 i3 c2 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK3_some => famK3 p n vis q s3 i2 i3 c2 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK4_some => famK4 p n vis q s3 i3 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK5_some => famK5 p n vis q i3 c3 cvid (some (r, m))
grind_pattern [ind_grind] famK6_some => famK6 p n q cvid (some (r, m))
grind_pattern [ind_grind] famK7_some => famK7 q (some (r, m))

/-- The lookups of `std_axiom_ok`. -/
structure StdProg2 (p : Prog) : Prop where
  std : StdProg p
  fam : p.lookup "std_ax_family" = some stdAxFamily

set_option maxHeartbeats 1600000 in
theorem fam_specW (p : Prog) (h : StdProg2 p) (n : Nat) (s₀ : St)
    (vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "std_ax_family" [vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid]
    ⦃fun r s' => LocEq s' s₀ ∧ famW p n s₀.mem vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid = some (r, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ h.fam]
  simp only [callFn, stdAxFamily]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p h.std.red.pa n,
        callW_spec p n "find_pinned", callW_spec p n "rom_cv",
        mp_specW p h.std.red.canon h.std.red.mp n] <;>
      finish (gen := 20) (instances := 5000) [mpW]

set_option maxHeartbeats 1600000 in
theorem std_specW (p : Prog) (h : StdProg2 p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "std_axiom_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ stdW p n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.std.std]
  simp only [callFn, stdAxiomOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        pinAt_specW p h.std.red.pa n, callW_spec p n "rom_ci", callW_spec p n "find_is",
        callW_spec p n "std_ax_family"] <;>
      finish (gen := 20) [rdW_eq, pinAtW]

local notation "V" => ConLeche.CheckMode.verified

/-- A `find_pinned` call's run, against its clause. -/
theorem fp_call {p : Prog} (h : StdProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k ca cb id : Word} {r : List Word}
    (hc : callW p n "find_pinned" [vis, nm, k, ca, cb, id] m = some (r, m'))
    (hS : StageR dn vis fe m a) (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4 ∨ k = 5)
    (hid : id.toNat < 8) :
    ∃ b a', (clausePT fe (decI nm) k ca cb (romPinT id.toNat)).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fp_specW p h n ⟨m, Locals.init []⟩ vis nm k ca cb id) hc
  rw [hs'] at hW
  obtain ⟨b, a', hS', hg, hd, hF⟩ := fpW_ok h hW hS hnm hk hid
  exact ⟨b, a', clausePT_of_fp hF, hS', hg, hd⟩

/-- A family of `stdAxiomOk`, flattened (`stdAxiomOk_eq`). -/
def famT (fe : IFEnv) (cv : IConstantVal) (s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word) : AM Bool := do
  let x1 ← pinAt s1.toNat
  let b1 ← clausePT fe x1 3 0 0 (romPinT i1.toNat)
  if !b1 then pure false else do
    let x2 ← pinAt s2.toNat
    let b2 ← clausePT fe x2 4 c2 c2 (romPinT i2.toNat)
    if !b2 then pure false else do
      let x3 ← pinAt s3.toNat
      let b3 ← clausePT fe x3 5 c3 c3 (romPinT i3.toNat)
      if !b3 then pure false else cv.matchesPin (← romCvT cvid.toNat)

/-- **`std_ax_family` refines a family of `stdAxiomOk`** at the model level. -/
theorem famW_ok {p : Prog} (h : StdProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word}
    {r : List Word} {cv : IConstantVal}
    (hW : famW p n m vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : decCV (erecP m) q.toNat = some cv)
    (h1 : i1.toNat < 8) (h2 : i2.toNat < 8) (h3 : i3.toNat < 8) (hcv : cvid.toNat < 10) :
    ∃ b a', (famT fe cv s1 s2 s3 i1 i2 i3 c2 c3 cvid).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  cases n with
  | zero => simp [famW] at hW
  | succ n =>
  rw [famW_step] at hW
  unfold famT
  -- the first clause
  rcases e1 : pinAtW m s1 with _ | ⟨r1, m1⟩ <;> simp only [e1, famK1, reduceCtorEq] at hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok e1 hS.1.pins
  rw [hm1, hr1] at hW
  simp only [List.headD_cons] at hW
  simp only [StateT.run_bind, hrun1, exc_ok_bind']
  rcases e2 : callW p n "find_pinned" [vis, pinW m (1 + s1.toNat), 3, 0, 0, i1] m with _ | ⟨r2, m2⟩ <;> simp only [e2, famK2, reduceCtorEq] at hW
  obtain ⟨b2, a2, hrun2, hS2, hg2, hd2⟩ := fp_call h e2 hS hl1 (.inl rfl) h1
  simp only [hrun2, exc_ok_bind']
  by_cases z2 : r2.headD 0 = 0
  · rw [if_pos z2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b2 = false := by rw [← hd2.1]; simpa using z2
    exact ⟨false, a2, by simp [hb]; rfl, hS2, hg2, by simp [decW0B]⟩
  rw [if_neg z2] at hW
  have hb2 : b2 = true := by rw [← hd2.1]; simpa using z2
  simp only [hb2, Bool.not_true, Bool.false_eq_true, if_false]
  -- the second clause
  rcases e3 : pinAtW m2 s2 with _ | ⟨r3, m3⟩ <;> simp only [e3, famK3, reduceCtorEq] at hW
  obtain ⟨hm3, hr3, hl3, hrun3⟩ := pinAtW_ok e3 hS2.1.pins
  rw [hm3, hr3] at hW
  simp only [List.headD_cons] at hW
  simp only [StateT.run_bind, hrun3, exc_ok_bind']
  rcases e4 : callW p n "find_pinned" [vis, pinW m2 (1 + s2.toNat), 4, c2, c2, i2] m2 with _ | ⟨r4, m4⟩ <;> simp only [e4, famK4, reduceCtorEq] at hW
  obtain ⟨b4, a4, hrun4, hS4, hg4, hd4⟩ := fp_call h e4 hS2 hl3 (.inr (.inl rfl)) h2
  simp only [hrun4, exc_ok_bind']
  by_cases z4 : r4.headD 0 = 0
  · rw [if_pos z4] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b4 = false := by rw [← hd4.1]; simpa using z4
    exact ⟨false, a4, by simp [hb]; rfl, hS4, hg2.trans hg4, by simp [decW0B]⟩
  rw [if_neg z4] at hW
  have hb4 : b4 = true := by rw [← hd4.1]; simpa using z4
  simp only [hb4, Bool.not_true, Bool.false_eq_true, if_false]
  -- the third clause
  rcases e5 : pinAtW m4 s3 with _ | ⟨r5, m5⟩ <;> simp only [e5, famK5, reduceCtorEq] at hW
  obtain ⟨hm5, hr5, hl5, hrun5⟩ := pinAtW_ok e5 hS4.1.pins
  rw [hm5, hr5] at hW
  simp only [List.headD_cons] at hW
  simp only [StateT.run_bind, hrun5, exc_ok_bind']
  rcases e6 : callW p n "find_pinned" [vis, pinW m4 (1 + s3.toNat), 5, c3, c3, i3] m4 with _ | ⟨r6, m6⟩ <;> simp only [e6, famK6, reduceCtorEq] at hW
  obtain ⟨b6, a6, hrun6, hS6, hg6, hd6⟩ := fp_call h e6 hS4 hl5 (.inr (.inr rfl)) h3
  simp only [hrun6, exc_ok_bind']
  by_cases z6 : r6.headD 0 = 0
  · rw [if_pos z6] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b6 = false := by rw [← hd6.1]; simpa using z6
    exact ⟨false, a6, by simp [hb]; rfl, hS6, hg2.trans (hg4.trans hg6), by simp [decW0B]⟩
  rw [if_neg z6] at hW
  have hb6 : b6 = true := by rw [← hd6.1]; simpa using z6
  simp only [hb6, Bool.not_true, Bool.false_eq_true, if_false]
  -- the axiom's own pin
  rcases e7 : callW p n "rom_cv" [cvid] m6 with _ | ⟨r7, m7⟩ <;> simp only [e7, famK7, reduceCtorEq] at hW
  obtain ⟨pin, a7, hrun7, hS7, hg7, hpin⟩ := h.red.rom.cv dn vis fe cvid hcv n m6 a6 r7 m7 hS6 e7
  have hg := hg2.trans (hg4.trans (hg6.trans hg7))
  have hq7 : decCV (erA m7) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg) hq
  obtain ⟨hm8, hrun8, hd8⟩ := mpW_ok (a := a7) hW hS7.2.2.2.2.1 hq7
    (DecB.get ⟨fun _ _ _ he h => he.2.decCV h⟩ hpin)
  subst hm8
  refine ⟨_, a7, ?_, hS7, hg, hd8⟩
  simp only [StateT.run_bind, hrun7, exc_ok_bind']
  exact hrun8

theorem stdAxiomOk_fam (fe : IFEnv) (cv : IConstantVal) :
    stdAxiomOk fe cv = (do
      let pn ← pinAt (32 : Word).toNat
      if cv.name == pn then do
        let en ← pinAt (0 : Word).toNat
        let ea ← eqA
        if fe.find? en != some ea then pure false else famT fe cv 34 35 36 2 3 4 2 4 0
      else do
        let cn ← pinAt (33 : Word).toNat
        if cv.name == cn then famT fe cv 37 38 39 5 6 7 1 3 1 else pure false) := by
  rw [stdAxiomOk_eq]; rfl

/-- A family call's run. -/
theorem fam_call {p : Prog} (h : StdProg2 p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word}
    {r : List Word} {cv : IConstantVal}
    (hc : callW p n "std_ax_family" [vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid] m = some (r, m'))
    (hS : StageR dn vis fe m a) (hq : decCV (erecP m) q.toNat = some cv)
    (h1 : i1.toNat < 8) (h2 : i2.toNat < 8) (h3 : i3.toNat < 8) (hcv : cvid.toNat < 10) :
    ∃ b a', (famT fe cv s1 s2 s3 i1 i2 i3 c2 c3 cvid).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fam_specW p h n ⟨m, Locals.init []⟩ vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid) hc
  rw [hs'] at hW
  exact famW_ok h.std hW hS hq h1 h2 h3 hcv

/-- **`std_axiom_ok(vis, q)` refines `stdAxiomOk`** at the model level. -/
theorem stdW_ok {p : Prog} (h : StdProg2 p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal} (hW : stdW p n m vis q = some (r, m')) (hS : StageR dn vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    ∃ b a', (stdAxiomOk fe cv).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨⟨wn, hwn, hwnl, hname⟩, -, -⟩ := decCV_words hq
  have ewn : rdW (m.arr64 EREC) q = wn := rdW_of_get? rfl (erecP_get hwn)
  cases n with
  | zero => simp [stdW] at hW
  | succ n =>
  rw [stdW_step, ewn] at hW
  rw [stdAxiomOk_fam, hname]
  rcases e1 : pinAtW m 32 with _ | ⟨r1, m1⟩ <;> simp only [e1, stdK1, reduceCtorEq] at hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok e1 hS.1.pins
  rw [hm1] at hW
  have ep : r1.headD 0 = pinW m (1 + (32 : Word).toNat) := by rw [hr1]; rfl
  have hbeq : ((decI wn : NIdx) == decI (pinW m (1 + (32 : Word).toNat))) =
      decide (wn = pinW m (1 + (32 : Word).toNat)) := decI_beq wn _ hwnl hl1
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hbeq]
  by_cases ep1 : wn = r1.headD 0
  · rw [if_pos ep1] at hW
    rw [ep] at ep1
    simp only [ep1, decide_true, if_true]
    -- `propext`: the pinned `Eq`
    rcases e2 : pinAtW m 0 with _ | ⟨r2, m2⟩ <;> simp only [e2, stdP1, reduceCtorEq] at hW
    obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok e2 hS.1.pins
    rw [hm2, hr2] at hW
    simp only [List.headD_cons] at hW
    simp only [StateT.run_bind, hrun2, exc_ok_bind']
    rcases e3 : callW p n "rom_ci" [0] m with _ | ⟨r3, m3⟩ <;> simp only [e3, stdP2, reduceCtorEq] at hW
    obtain ⟨ea, a3, hrun3, hS3, hg3, hea⟩ := h.std.red.rom.ci dn vis fe 0 (by decide) n m a r3 m3 hS e3
    have hrun3' : eqA.run a = .ok (ea, a3) := hrun3
    simp only [hrun3', exc_ok_bind']
    rcases e4 : callW p n "find_is" [vis, pinW m (1 + (0 : Word).toNat), r3.headD 0] m3 with _ | ⟨r4, m4⟩ <;> simp only [e4, stdP3, reduceCtorEq] at hW
    obtain ⟨s4, hs4, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (findIs_spec p h.std.red.canon dn vis fe hdn _ _ ea n ⟨m3, Locals.init []⟩ a3
        ⟨hS3, hl2, decRCI_get hea⟩) e4
    subst hs4
    simp only [AM.st_pure, AM.res_pure] at hS4 hb4
    by_cases z4 : r4.headD 0 = 0
    · rw [if_pos z4] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hf : (fe.find? (decI (pinW m (1 + (0 : Word).toNat))) == some ea) = false := by
        rw [← hb4]; simpa using z4
      refine ⟨false, a3, ?_, hS4, hg3.trans hg4, by simp [decW0B]⟩
      simp only [bne, hf, Bool.not_false, if_true]
      rfl
    rw [if_neg z4] at hW
    have ht : (fe.find? (decI (pinW m (1 + (0 : Word).toNat))) == some ea) = true := by
      rw [← hb4]; simpa using z4
    simp only [bne, ht, Bool.not_true, Bool.false_eq_true, if_false]
    -- the `Iff` family
    rcases e5 : callW p n "std_ax_family" [vis, q, 34, 35, 36, 2, 3, 4, 2, 4, 0] s4.mem with _ | ⟨r5, m5⟩ <;> simp only [e5, stdRet, reduceCtorEq] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨b, a5, hrun5, hS5, hg5, hd5⟩ := fam_call h e5 hS4
      (ArrExt.decCV (IWGrow.erecPExt (hg3.trans hg4)) hq) (by decide) (by decide) (by decide)
      (by decide)
    exact ⟨b, a5, hrun5, hS5, hg3.trans (hg4.trans hg5), hd5⟩
  · rw [if_neg ep1] at hW
    rw [ep] at ep1
    simp only [ep1, decide_false, Bool.false_eq_true, if_false]
    -- `choice`
    rcases e2 : pinAtW m 33 with _ | ⟨r2, m2⟩ <;> simp only [e2, stdC1, reduceCtorEq] at hW
    obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok e2 hS.1.pins
    rw [hm2] at hW
    have ec : r2.headD 0 = pinW m (1 + (33 : Word).toNat) := by rw [hr2]; rfl
    have hbeqc : ((decI wn : NIdx) == decI (pinW m (1 + (33 : Word).toNat))) =
        decide (wn = pinW m (1 + (33 : Word).toNat)) := decI_beq wn _ hwnl hl2
    simp only [StateT.run_bind, hrun2, exc_ok_bind', hbeqc]
    by_cases ec1 : wn = r2.headD 0
    · rw [if_pos ec1] at hW
      rw [ec] at ec1
      simp only [ec1, decide_true, if_true]
      rcases e3 : callW p n "std_ax_family" [vis, q, 37, 38, 39, 5, 6, 7, 1, 3, 1] m with _ | ⟨r3, m3⟩ <;> simp only [e3, stdRet, reduceCtorEq] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨b, a3, hrun3, hS3, hg3, hd3⟩ := fam_call h e3 hS hq (by decide) (by decide)
        (by decide) (by decide)
      exact ⟨b, a3, hrun3, hS3, hg3, hd3⟩
    · rw [if_neg ec1] at hW
      rw [ec] at ec1
      simp only [ec1, decide_false, Bool.false_eq_true, if_false]
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩

/-- **`std_axiom_ok(vis, q)` refines `stdAxiomOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.stdAxiomOk]
theorem stdAxiomOk_refines (p : Prog) (h : StdProg2 p) (dn : NIdx → Option ConLeche.Name)
    (hdn : DnInj dn) (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "std_axiom_ok" [vis, q]
      (fun m a => StageR dn vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (stdAxiomOk fe cv) (KeepPost dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hq⟩
  refine triple_post (std_specW p h n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := stdW_ok h hdn hm hS hq
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

end L.Arena
