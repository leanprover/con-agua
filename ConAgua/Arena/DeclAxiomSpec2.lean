module

public import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.LocNF
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPosSpec.EnvFindWHit
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# `Lean.trustCompiler`: `find_pinned_cv`, `trust_compiler_ok` (lane `decls3`)

`find_pinned_cv(vis, n, k, id)` is one clause of `trustCompilerOk`: the stored constant `n` has the
pinned shape (`k = 3`: an inductive; `k = 4`: a constructor without parameters and fields), and its
constant value matches `rom_cv(id)`. Its relational lemma says what the twin's clause does
(`fpcShape`: the shape test as a partial function), and `trust_compiler_ok` chains two clauses and
the axiom's own pin. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The pinned shape `k` of a stored constant: its constant value when it has the shape. -/
def fpcShape (k : Word) : IConstantInfo → Option IConstantVal
  | .indInfo cv _ => if k = 3 then some cv else none
  | .ctorInfo cv nP nF => if k = 4 ∧ nP = 0 ∧ nF = 0 then some cv else none
  | _ => none

/-- The lookups of the compiler-trust family. -/
structure TcoProg (p : Prog) : Prop where
  red : RedProg p
  fpc : p.lookup "find_pinned_cv" = some findPinnedCv
  tco : p.lookup "trust_compiler_ok" = some trustCompilerOkL

/-- **The model of `find_pinned_cv(vis, n, k, id)`.** -/
l_model fpc_specW (p : Prog) (hp : p.lookup "find_pinned_cv" = some findPinnedCv)
  fns [hp ↦ fpcW list]
  specs [callW_spec p n "env_find", callW_spec p n "rom_cv", callW_spec p n "matches_pin"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-! ## `trust_compiler_ok(vis, q)` -/

section tco
variable (p : Prog)

/-- After `rom_cv(4)`: the axiom's own pin. -/
def tcoK5 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => mpW m5 q (r5.headD 0)

/-- After the `True.intro` clause. -/
def tcoK4 (n : Nat) (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => if r4.headD 0 = 0 then some ([0], m4) else tcoK5 q (callW p n "rom_cv" [4] m4)

/-- After the `True.intro` pin. -/
def tcoK3 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tcoK4 p n q (callW p n "find_pinned_cv" [vis, r3.headD 0, 4, 3] m3)

/-- After the `True` clause. -/
def tcoK2 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => if r2.headD 0 = 0 then some ([0], m2) else tcoK3 p n vis q (pinAtW m2 41)

/-- After the `True` pin. -/
def tcoK1 (n : Nat) (vis q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => tcoK2 p n vis q (callW p n "find_pinned_cv" [vis, r1.headD 0, 3, 2] m1)

/-- **The model of `trust_compiler_ok(vis, q)`.** -/
def tcoW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, vis, q => tcoK1 p n vis q (pinAtW m 40)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (vis q : Word) (r1 r2 r3 r4 r5 : List Word)
theorem tcoW_step : tcoW p (n + 1) m vis q = tcoK1 p n vis q (pinAtW m 40) := rfl
theorem tcoK1_some : tcoK1 p n vis q (some (r1, m1)) =
    tcoK2 p n vis q (callW p n "find_pinned_cv" [vis, r1.headD 0, 3, 2] m1) := rfl
theorem tcoK2_some : tcoK2 p n vis q (some (r2, m2)) =
    if r2.headD 0 = 0 then some ([0], m2) else tcoK3 p n vis q (pinAtW m2 41) := rfl
theorem tcoK3_some : tcoK3 p n vis q (some (r3, m3)) =
    tcoK4 p n q (callW p n "find_pinned_cv" [vis, r3.headD 0, 4, 3] m3) := rfl
theorem tcoK4_some : tcoK4 p n q (some (r4, m4)) =
    if r4.headD 0 = 0 then some ([0], m4) else tcoK5 q (callW p n "rom_cv" [4] m4) := rfl
theorem tcoK5_some : tcoK5 q (some (r5, m5)) = mpW m5 q (r5.headD 0) := rfl
end arms

grind_pattern [ind_grind] tcoW_step => tcoW p (n + 1) m vis q
grind_pattern [ind_grind] tcoK1_some => tcoK1 p n vis q (some (r1, m1))
grind_pattern [ind_grind] tcoK2_some => tcoK2 p n vis q (some (r2, m2))
grind_pattern [ind_grind] tcoK3_some => tcoK3 p n vis q (some (r3, m3))
grind_pattern [ind_grind] tcoK4_some => tcoK4 p n q (some (r4, m4))
grind_pattern [ind_grind] tcoK5_some => tcoK5 q (some (r5, m5))

set_option maxHeartbeats 1600000 in
theorem tco_specW (h : TcoProg p) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "trust_compiler_ok" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ tcoW p n s₀.mem vis q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tco]
  simp only [callFn, trustCompilerOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_specW p h.red.pa n,
        callW_spec p n "find_pinned_cv", callW_spec p n "rom_cv",
        mp_specW p h.red.canon h.red.mp n] <;>
      finish (gen := 20) [mpW]

end tco

/-! ### The twin's clauses, flattened -/

/-- A clause of the twin's environment-shape tests: the stored constant has the pinned shape `k`,
and its constant value matches the pin `T`. -/
def clauseT (fe : IFEnv) (nm : NIdx) (k : Word) (T : AM IConstantVal) : AM Bool :=
  match (fe.find? nm).bind (fpcShape k) with
  | some cvT => do cvT.matchesPin (← T)
  | none => pure false

/-- `trustCompilerOk` as two clauses and the axiom's pin. -/
theorem trustCompilerOk_eq (fe : IFEnv) (cv : IConstantVal) :
    trustCompilerOk fe cv = (do
      let t ← trueName
      let b ← clauseT fe t 3 trueCvA
      if !b then pure false else do
        let ti ← trueIntroName
        let b2 ← clauseT fe ti 4 trueIntroCvA
        if !b2 then pure false else cv.matchesPin (← trustCompilerA)) := by
  unfold trustCompilerOk
  congr 1; funext t
  unfold clauseT
  cases hf : fe.find? t with
  | none => simp
  | some ci =>
    cases ci with
    | indInfo cvT caps =>
      simp only [Option.bind_some, fpcShape, ite_true, bind_assoc]
      congr 1; funext pin
      simp only [matchesPin_eq, pure_bind]
      split <;> try rfl
      congr 1; funext ti
      cases hf2 : fe.find? ti with
      | none => simp
      | some ci2 =>
        cases ci2 with
        | ctorInfo cvTi nP nF =>
          simp only [Option.bind_some, fpcShape]
          by_cases e : nP = 0 ∧ nF = 0
          · obtain ⟨rfl, rfl⟩ := e
            simp only [and_self, ite_true, bind_assoc, pure_bind]
          · rcases Nat.eq_zero_or_pos nP with h0 | h0 <;> rcases Nat.eq_zero_or_pos nF with h1 | h1 <;>
              simp_all [Nat.pos_iff_ne_zero]
        | _ => simp [fpcShape]
    | _ => simp [fpcShape]

/-- A `find_pinned_cv` call's run, against its clause. -/
theorem fpc_call {p : Prog} (h : TcoProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k id : Word} {r : List Word}
    (hc : callW p n "find_pinned_cv" [vis, nm, k, id] m = some (r, m'))
    (hS : StageR vis fe m a) (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4)
    (hid : id.toNat < 10) :
    ∃ b a', (clauseT fe (decI nm) k (romCvT id.toNat)).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fpc_specW p h.fpc n _ vis nm k id) hc
  generalize s'.mem = m' at hW
  cases n with
  | zero => simp [fpcW.eq_1] at hW
  | succ n =>
  rw [fpcW.arm1] at hW
  rcases h1 : callW p n "env_find" [nm, vis] m with _ | ⟨r1, m1⟩
  · rw [h1, fpcW.k_env_find.none] at hW; cases hW
  rw [h1] at hW
  obtain ⟨hm1, hr1⟩ := envFind_callR h.red h1
  subst m1 r1
  -- a decline: no matching shape, `[0]`, the twin's `false`
  have decl : (fe.find? (decI nm)).bind (fpcShape k) = none → some ([0], m) = some (r, m') →
      ∃ b a', (clauseT fe (decI nm) k (romCvT id.toNat)).run a = .ok (b, a') ∧
        StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
    intro hn e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
    simp only [clauseT, hn]; rfl
  by_cases hf : (findRes m vis nm).headD 0 = 0
  · rw [fpcW.k_env_find.arm1 p n k id _ _ hf] at hW
    exact decl (by rw [findRes_miss hS.check.env hnm hf]; rfl) hW
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hS.check.env hnm hf
  generalize hq : (findRes m vis nm).tail.headD 0 = q at hW hci hfind
  obtain ⟨wk, hwk⟩ := decCI_rd hci
  have ek := erecKind hwk
  -- a pass: the shape's constant value against the pin
  have pass : ∀ cv, fpcShape k ci = some cv → decCV (erecP m) (q.toNat + 1) = some cv →
      fpcW.j1 p n id q m = some (r, m') →
      ∃ b a', (clauseT fe (decI nm) k (romCvT id.toNat)).run a = .ok (b, a') ∧
        StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
    intro cv hsh hcv hJ
    rw [fpcW.j1.arm1] at hJ
    rcases h2 : callW p n "rom_cv" [id] m with _ | ⟨r2, m2⟩
    · rw [h2, fpcW.k_rom_cv.none] at hJ; cases hJ
    rw [h2, fpcW.k_rom_cv.arm1] at hJ
    obtain ⟨pin, a2, hrun2, hS2, hg2, hpin⟩ := h.red.rom.cv vis fe id hid n _ a r2 m2 hS h2
    obtain ⟨wn, hwn, -⟩ := decCV_name hcv
    have hq1 : (q + 1).toNat = q.toNat + 1 := by
      have := erecP_lt64 hwn; rw [UInt64.toNat_add]; simp; omega
    have hcv2 : decCV (erA m2) (q + 1).toNat = some cv := by
      rw [hq1]; exact ArrExt.decCV (L.Ind.IWGrow.ext hg2) hcv
    rcases h3 : callW p n "matches_pin" [q + 1, r2.headD 0] m2 with _ | ⟨r3, m3⟩
    · rw [h3, fpcW.k_matches_pin.none] at hJ; cases hJ
    rw [h3, fpcW.k_matches_pin.arm1] at hJ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hJ)
    obtain ⟨rfl, hrun3, hd3⟩ := mpW_ok (a := a2) (mp_callR h.red h3) hS2.iw.erSize hcv2
      (decRCV_get hpin)
    refine ⟨_, _, ?_, hS2, hg2, by simpa [decW0B] using hd3⟩
    simp only [clauseT, hfind, hci, Option.bind_some, hsh, StateT.run_bind, hrun2, L.Arena.except_ok_bind]
    exact hrun3
  by_cases hkw : wk = k
  rotate_left
  · rw [fpcW.k_env_find.arm2 p n k id _ _ hf (by rw [hq, ek]; exact hkw)] at hW
    refine decl ?_ hW
    rw [hfind, hci, Option.bind_some]
    rcases hk with rfl | rfl
    · have := (decCI_kind3 hci hwk).2 hkw; cases ci <;> simp_all [fpcShape]
    · have := (decCI_kind4 hci hwk).2 hkw; cases ci <;> simp_all [fpcShape]
  subst hkw
  rcases hk with hk3 | hk4
  · subst hk3
    rw [fpcW.k_env_find.arm5 p n _ id _ _ hf (by rw [hq, ek]) (by decide)] at hW
    obtain ⟨cv, caps, hcv, rfl⟩ := (decCI_kind3 hci hwk).1 rfl
    rw [hq] at hW
    exact pass cv (by simp [fpcShape]) hcv hW
  subst hk4
  obtain ⟨cv, np, nf, hcv, h5, h6, rfl⟩ := (decCI_kind4 hci hwk).1 rfl
  obtain ⟨w5, e5, rfl⟩ := natD h5
  obtain ⟨w6, e6, rfl⟩ := natD h6
  have hq5 : (q + 5).toNat = q.toNat + 5 := by
    have := erecP_lt64 e5; rw [UInt64.toNat_add]; simp; omega
  have hq6 : (q + 6).toNat = q.toNat + 6 := by
    have := erecP_lt64 e6; rw [UInt64.toNat_add]; simp; omega
  have r5 := erecKind (q := q + 5) (by rw [hq5]; exact e5)
  have r6 := erecKind (q := q + 6) (by rw [hq6]; exact e6)
  have i5 : w5 = 0 ↔ w5.toNat = 0 := ⟨fun h => by simp [h], fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
  have i6 : w6 = 0 ↔ w6.toNat = 0 := ⟨fun h => by simp [h], fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
  by_cases hz : w5 ≠ 0 ∨ w6 ≠ 0
  · rw [fpcW.k_env_find.arm3 p n _ id _ _ hf (by rw [hq, ek]) rfl (by rw [hq, r5, r6]; exact hz)] at hW
    refine decl ?_ hW
    rw [hfind, hci, Option.bind_some]
    simp only [fpcShape, true_and]
    rw [ite_eq_right_iff.mpr (fun h0 => absurd h0 (by
      rintro ⟨a5, a6⟩; rcases hz with hz | hz
      · exact hz (i5.mpr a5)
      · exact hz (i6.mpr a6)))]
  · rw [fpcW.k_env_find.arm4 p n _ id _ _ hf (by rw [hq, ek]) rfl (by rw [hq, r5, r6]; exact hz)] at hW
    have h0 : w5.toNat = 0 ∧ w6.toNat = 0 :=
      ⟨i5.mp (Classical.byContradiction fun c => hz (.inl c)),
        i6.mp (Classical.byContradiction fun c => hz (.inr c))⟩
    rw [hq] at hW
    exact pass cv (by simp [fpcShape, h0]) hcv hW

/-- **`trust_compiler_ok(vis, q)` refines `trustCompilerOk`** at the model level. -/
theorem tcoW_ok {p : Prog} (h : TcoProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal} (hW : tcoW p n m vis q = some (r, m')) (hS : StageR vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    ∃ b a', (trustCompilerOk fe cv).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  cases n with
  | zero => simp [tcoW] at hW
  | succ n =>
  rw [tcoW_step] at hW
  rcases h1 : pinAtW m 40 with _ | ⟨r1, m1⟩ <;> simp only [h1, tcoK1, reduceCtorEq] at hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.check.pins
  subst m1 r1
  simp only [List.headD_cons] at hW
  rw [trustCompilerOk_eq]
  have ht : trueName.run a = .ok (decI (pinW m (1 + (40 : Word).toNat)), a) := by
    simpa [trueName, pinTrue, show PIN_TRUE = (40 : Word).toNat from rfl] using hrun1
  simp only [StateT.run_bind, ht, L.Arena.except_ok_bind]
  rcases h2 : callW p n "find_pinned_cv" [vis, pinW m (1 + (40 : Word).toNat), 3, 2] m
    with _ | ⟨r2, m2⟩ <;> simp only [h2, tcoK2, reduceCtorEq] at hW
  obtain ⟨b2, a2, hrun2, hS2, hg2, hd2⟩ := fpc_call h h2 hS hl1 (.inl rfl) (by decide)
  simp only [show trueCvA = romCvT (2 : Word).toNat from rfl, hrun2, L.Arena.except_ok_bind]
  by_cases h20 : r2.headD 0 = 0
  · rw [ite_eq_left h20] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : b2 = false := by rw [← hd2.1, h20]; rfl
    subst this
    exact ⟨false, a2, rfl, hS2, hg2, by simp [decW0B]⟩
  rw [ite_eq_right h20] at hW
  have : b2 = true := by rw [← hd2.1]; simpa using h20
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rcases h3 : pinAtW m2 41 with _ | ⟨r3, m3⟩ <;> simp only [h3, tcoK3, reduceCtorEq] at hW
  obtain ⟨hm3, hr3, hl3, hrun3⟩ := pinAtW_ok h3 hS2.check.pins
  subst m3 r3
  simp only [List.headD_cons] at hW
  have hti : trueIntroName.run a2 = .ok (decI (pinW m2 (1 + (41 : Word).toNat)), a2) := by
    simpa [trueIntroName, pinTrueIntro, show PIN_TRUE_INTRO = (41 : Word).toNat from rfl] using hrun3
  simp only [StateT.run_bind, hti, L.Arena.except_ok_bind]
  rcases h4 : callW p n "find_pinned_cv" [vis, pinW m2 (1 + (41 : Word).toNat), 4, 3] m2
    with _ | ⟨r4, m4⟩ <;> simp only [h4, tcoK4, reduceCtorEq] at hW
  obtain ⟨b4, a4, hrun4, hS4, hg4, hd4⟩ := fpc_call h h4 hS2 hl3 (.inr rfl) (by decide)
  simp only [show trueIntroCvA = romCvT (3 : Word).toNat from rfl, hrun4, L.Arena.except_ok_bind]
  by_cases h40 : r4.headD 0 = 0
  · rw [ite_eq_left h40] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : b4 = false := by rw [← hd4.1, h40]; rfl
    subst this
    exact ⟨false, a4, rfl, hS4, hg2.trans hg4, by simp [decW0B]⟩
  rw [ite_eq_right h40] at hW
  have : b4 = true := by rw [← hd4.1]; simpa using h40
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rcases h5 : callW p n "rom_cv" [4] m4 with _ | ⟨r5, m5⟩ <;> simp only [h5, tcoK5, reduceCtorEq] at hW
  obtain ⟨pin, a5, hrun5, hS5, hg5, hpin⟩ := h.red.rom.cv vis fe 4 (by decide) n _ a4 r5 m5 hS4 h5
  have hq5 : decCV (erA m5) q.toNat = some cv :=
    ArrExt.decCV (L.Ind.IWGrow.ext ((hg2.trans hg4).trans hg5)) hq
  obtain ⟨rfl, hrun6, hd6⟩ := mpW_ok (a := a5) hW hS5.iw.erSize hq5 (decRCV_get hpin)
  refine ⟨_, _, ?_, hS5, hg2.trans (hg4.trans hg5), hd6⟩
  simp only [show trustCompilerA = romCvT (4 : Word).toNat from rfl, StateT.run_bind, hrun5,
    L.Arena.except_ok_bind]
  exact hrun6

/-- **`trust_compiler_ok(vis, q)` refines `trustCompilerOk`** (through the ROM stubs). -/
@[refines ConRon.Arena.trustCompilerOk]
theorem trustCompilerOk_refines (p : Prog) (h : TcoProg p) (_dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "trust_compiler_ok" [vis, q]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (trustCompilerOk fe cv) (KeepPost vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hq⟩
  refine triple_post (tco_specW p h n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := tcoW_ok h hm hS hq
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

end L.Arena
