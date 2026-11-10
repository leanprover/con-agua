module

public import ConAgua.Arena.DeclAxiomSpec3
import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.L.ModelGen
import all ConAgua.Arena.DeclArms
import ConAgua.Arena.DeclCvg

@[expose] public section

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

/-- The lookups of `std_axiom_ok`. -/
structure StdProg2 (p : Prog) : Prop where
  std : StdProg p
  fam : p.lookup "std_ax_family" = some stdAxFamily
  eqs : p.lookup "eq_stored" = some eqStoredL

l_model fam_specW (p : Prog) (h : StdProg2 p)
  fns [h.fam ↦ famW list]
  specs [pinAt_specW p h.std.red.pa n, callW_spec p n "find_pinned", callW_spec p n "rom_cv",
    callW_spec p n "eq_stored",
    mp_specW p h.std.red.canon h.std.red.mp n]
  grind [arena_grind] extra [ld64_rd_spec]

l_model std_specW (p : Prog) (h : StdProg2 p)
  fns [h.std.std ↦ stdW list]
  specs [pinAt_specW p h.std.red.pa n, callW_spec p n "rom_ci", callW_spec p n "find_is",
    callW_spec p n "std_ax_family", callW_spec p n "eq_stored"]
  grind [arena_grind] extra [ld64_rd_spec]

local notation "V" => ConLeche.CheckMode.verified

/-- A family of `stdAxiomOk`, flattened (`stdAxiomOk_eq`). -/
def famT (fe : IFEnv) (cv : IConstantVal) (N1 N2 N3 : AM NIdx) (P1 P2 P3 : AM IConstantInfo)
    (c2 c3 : Word) (PA : AM IConstantVal) : AM Bool := do
  let x1 ← N1
  let b1 ← clausePT fe x1 3 0 0 (do return (← P1).toConstantVal)
  if !b1 then pure false else do
    let x2 ← N2
    let b2 ← clausePT fe x2 4 c2 c2 (do return (← P2).toConstantVal)
    if !b2 then pure false else do
      let x3 ← N3
      let b3 ← clausePT fe x3 5 c3 c3 (do return (← P3).toConstantVal)
      if !b3 then pure false else cv.matchesPin (← PA)

/-- `stdAxiomOk` as the pinned `Eq` test and two families. -/
theorem stdAxiomOk_eq (fe : IFEnv) (cv : IConstantVal) :
    stdAxiomOk fe cv = (do
      let pn ← propextName
      if cv.name == pn then do
        if !(← eqStored fe) then pure false
        else famT fe cv iffName iffIntroName iffRecName iffA iffIntroA iffRecA 2 4 propextA
      else do
        let cn ← choiceName
        if cv.name == cn then
          famT fe cv nonemptyName nonemptyIntroName nonemptyRecName nonemptyA nonemptyIntroA
            nonemptyRecA 1 3 choiceA
        else pure false) := by
  unfold stdAxiomOk famT clausePT
  simp only [bind_assoc]
  congr 1; funext pn
  split
  · congr 1; funext e
    split
    · rfl
    · congr 1; funext x1
      cases h1 : fe.find? x1 with
      | none => simp
      | some c1 =>
        cases c1
        all_goals try (simp [fpShape]; done)
        simp only [Option.bind_some, fpShape, ↓reduceIte, bind_assoc, pure_bind]
        congr 1; funext c; congr 1; funext b
        split
        · rfl
        congr 1; funext x2
        cases h2 : fe.find? x2 with
        | none => simp
        | some c2 =>
          cases c2
          all_goals try (simp [fpShape]; done)
          simp only [Option.bind_some, fpShape, true_and]
          split
          · rename_i heq
            simp only [Option.some.injEq, IConstantInfo.ctorInfo.injEq] at heq
            obtain ⟨rfl, rfl, rfl⟩ := heq
            simp only [UInt64.reduceToNat, and_self, ↓reduceIte, bind_assoc]
            congr 1; funext c; congr 1; funext b
            split
            · rfl
            congr 1; funext x3
            cases h3 : fe.find? x3 with
            | none => simp
            | some c3 =>
              cases c3
              all_goals try (simp [fpShape]; done)
              simp only [Option.bind_some, fpShape, true_and]
              split
              · rename_i heq
                simp only [Option.some.injEq, IConstantInfo.recInfo.injEq] at heq
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
                simp only [UInt64.reduceToNat, and_self, ↓reduceIte, bind_assoc]
              · rename_i hne
                rw [ite_eq_right (by rintro ⟨rfl, rfl⟩; exact hne _ _ _ rfl)]
                simp
          · rename_i hne
            rw [ite_eq_right (by rintro ⟨rfl, rfl⟩; exact hne _ rfl)]
            simp
  · congr 1; funext cn
    split
    · congr 1; funext x1
      cases h1 : fe.find? x1 with
      | none => simp
      | some c1 =>
        cases c1
        all_goals try (simp [fpShape]; done)
        simp only [Option.bind_some, fpShape, ↓reduceIte, bind_assoc, pure_bind]
        congr 1; funext c; congr 1; funext b
        split
        · rfl
        congr 1; funext x2
        cases h2 : fe.find? x2 with
        | none => simp
        | some c2 =>
          cases c2
          all_goals try (simp [fpShape]; done)
          simp only [Option.bind_some, fpShape, true_and]
          split
          · rename_i heq
            simp only [Option.some.injEq, IConstantInfo.ctorInfo.injEq] at heq
            obtain ⟨rfl, rfl, rfl⟩ := heq
            simp only [UInt64.reduceToNat, and_self, ↓reduceIte, bind_assoc]
            congr 1; funext c; congr 1; funext b
            split
            · rfl
            congr 1; funext x3
            cases h3 : fe.find? x3 with
            | none => simp
            | some c3 =>
              cases c3
              all_goals try (simp [fpShape]; done)
              simp only [Option.bind_some, fpShape, true_and]
              split
              · rename_i heq
                simp only [Option.some.injEq, IConstantInfo.recInfo.injEq] at heq
                obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
                simp only [UInt64.reduceToNat, and_self, ↓reduceIte, bind_assoc]
              · rename_i hne
                rw [ite_eq_right (by rintro ⟨rfl, rfl⟩; exact hne _ _ _ rfl)]
                simp
          · rename_i hne
            rw [ite_eq_right (by rintro ⟨rfl, rfl⟩; exact hne _ rfl)]
            simp
    · rfl

/-- **`std_ax_family` refines a family of `stdAxiomOk`** at the model level. -/
theorem famW_ok {p : Prog} (h : StdProg2 p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q s1 s2 s3 i1 i2 i3 c2 c3 cvid : Word}
    {r : List Word} {cv : IConstantVal}
    (hW : famW p n m vis q s1 s2 s3 i1 i2 i3 c2 c3 cvid = some (r, m'))
    (hS : StageR vis fe m a) (hq : decCV (erecP m) q.toNat = some cv)
    (h1 : s1 ≠ 51) (h2 : s2 ≠ 51) (h3 : s3 ≠ 51)
    (hi1 : i1.toNat < 7) (hi2 : i2.toNat < 7) (hi3 : i3.toNat < 7) (hcv : cvid.toNat < 10) :
    ∃ b a', (famT fe cv (pinAt s1.toNat) (pinAt s2.toNat) (pinAt s3.toNat) (romCiT i1.toNat)
        (romCiT i2.toNat) (romCiT i3.toNat) c2 c3 (romCvT cvid.toNat)).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  cases n with
  | zero => simp [famW.eq_1] at hW
  | succ n =>
  rw [famW.arm1] at hW
  simp only [famT]
  -- the inductive
  rcases e1 : pinAtW m s1 with _ | ⟨r1, m1⟩
  · rw [e1, famW.k_pin_at.none] at hW; cases hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok e1 hS.check.pins h1
  subst m1 r1
  rw [e1, famW.k_pin_at.arm1] at hW
  simp only [List.headD_cons] at hW
  rcases f1 : callW p n "find_pinned" [vis, pinW m (1 + s1.toNat), 3, 0, 0, i1] m with _ | ⟨q1, n1⟩
  · rw [f1, famW.k_find_pinned.none] at hW; cases hW
  obtain ⟨b1, a1, hb1, hS1, hg1, hd1⟩ := fp_call h.std f1 hS hl1 (.inl rfl) hi1
  simp only [StateT.run_bind, hrun1, exc_ok_bind']
  rw [show (do return (← romCiT i1.toNat).toConstantVal : AM IConstantVal) = romPinT i1.toNat
    from rfl, hb1, exc_ok_bind']
  rw [f1] at hW
  by_cases z1 : q1.headD 0 = 0
  · rw [famW.k_find_pinned.arm1 p n _ _ _ _ _ _ _ _ _ q1 n1 z1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : b1 = false := by rw [← hd1.1, z1]; rfl
    subst this
    exact ⟨false, a1, rfl, hS1, hg1, by simp [decW0B]⟩
  rw [famW.k_find_pinned.arm2 p n _ _ _ _ _ _ _ _ _ q1 n1 z1] at hW
  have : b1 = true := by rw [← hd1.1]; simpa using z1
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  -- the constructor
  rcases e2 : pinAtW n1 s2 with _ | ⟨r2, m2⟩
  · rw [e2, famW.k_pin_at_2.none] at hW; cases hW
  obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok e2 hS1.check.pins h2
  subst m2 r2
  rw [e2, famW.k_pin_at_2.arm1] at hW
  simp only [List.headD_cons] at hW
  rcases f2 : callW p n "find_pinned" [vis, pinW n1 (1 + s2.toNat), 4, c2, c2, i2] n1
    with _ | ⟨q2, n2⟩
  · rw [f2, famW.k_find_pinned_2.none] at hW; cases hW
  obtain ⟨b2, a2, hb2, hS2, hg2, hd2⟩ := fp_call h.std f2 hS1 hl2 (.inr (.inl rfl)) hi2
  simp only [StateT.run_bind, hrun2, exc_ok_bind']
  rw [show (do return (← romCiT i2.toNat).toConstantVal : AM IConstantVal) = romPinT i2.toNat
    from rfl, hb2, exc_ok_bind']
  rw [f2] at hW
  by_cases z2 : q2.headD 0 = 0
  · rw [famW.k_find_pinned_2.arm1 p n _ _ _ _ _ _ q2 n2 z2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : b2 = false := by rw [← hd2.1, z2]; rfl
    subst this
    exact ⟨false, a2, rfl, hS2, hg1.trans hg2, by simp [decW0B]⟩
  rw [famW.k_find_pinned_2.arm2 p n _ _ _ _ _ _ q2 n2 z2] at hW
  have : b2 = true := by rw [← hd2.1]; simpa using z2
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  -- the recursor
  rcases e3 : pinAtW n2 s3 with _ | ⟨r3, m3⟩
  · rw [e3, famW.k_pin_at_3.none] at hW; cases hW
  obtain ⟨hm3, hr3, hl3, hrun3⟩ := pinAtW_ok e3 hS2.check.pins h3
  subst m3 r3
  rw [e3, famW.k_pin_at_3.arm1] at hW
  simp only [List.headD_cons] at hW
  rcases f3 : callW p n "find_pinned" [vis, pinW n2 (1 + s3.toNat), 5, c3, c3, i3] n2
    with _ | ⟨q3, n3⟩
  · rw [f3, famW.k_find_pinned_3.none] at hW; cases hW
  obtain ⟨b3, a3, hb3, hS3, hg3, hd3⟩ := fp_call h.std f3 hS2 hl3 (.inr (.inr rfl)) hi3
  simp only [StateT.run_bind, hrun3, exc_ok_bind']
  rw [show (do return (← romCiT i3.toNat).toConstantVal : AM IConstantVal) = romPinT i3.toNat
    from rfl, hb3, exc_ok_bind']
  rw [f3] at hW
  by_cases z3 : q3.headD 0 = 0
  · rw [famW.k_find_pinned_3.arm1 p n _ _ q3 n3 z3] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have : b3 = false := by rw [← hd3.1, z3]; rfl
    subst this
    exact ⟨false, a3, rfl, hS3, hg1.trans (hg2.trans hg3), by simp [decW0B]⟩
  rw [famW.k_find_pinned_3.arm2 p n _ _ q3 n3 z3] at hW
  have : b3 = true := by rw [← hd3.1]; simpa using z3
  subst this
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  -- the axiom's pin
  rcases e4 : callW p n "rom_cv" [cvid] n3 with _ | ⟨r4, m4⟩
  · rw [e4, famW.k_rom_cv.none] at hW; cases hW
  rw [e4, famW.k_rom_cv.arm1] at hW
  obtain ⟨pin, a4, hrun4, hS4, hg4, hpin⟩ := h.std.red.rom.cv vis fe cvid hcv n _ a3 r4 m4 hS3 e4
  have hg04 := hg1.trans (hg2.trans (hg3.trans hg4))
  rcases e5 : mpW m4 q (r4.headD 0) with _ | ⟨r5, m5⟩
  · rw [e5, famW.k_matches_pin.none] at hW; cases hW
  rw [e5, famW.k_matches_pin.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨rfl, hrun5, hd5⟩ := mpW_ok (a := a4) e5 hS4.iw.erSize
    (ArrExt.decCV (L.Ind.IWGrow.ext hg04) hq) (decRCV_get hpin)
  refine ⟨_, _, ?_, hS4, hg04, by simpa [decW0B] using hd5⟩
  simp only [StateT.run_bind, hrun4, exc_ok_bind']
  exact hrun5

/-- **`std_axiom_ok(vis, q)` refines `stdAxiomOk`** at the model level. -/
theorem stdW_ok {p : Prog} (h : StdProg2 p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {q : Word} {r : List Word}
    {cv : IConstantVal} (hW : stdW p n m vis q = some (r, m')) (hS : StageR vis fe m a)
    (hq : decCV (erecP m) q.toNat = some cv) :
    ∃ b a', (stdAxiomOk fe cv).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hq
  cases n with
  | zero => simp [stdW.eq_1] at hW
  | succ n =>
  rw [stdW.arm1] at hW
  rw [stdAxiomOk_eq]
  have ex : rdW (m.arr64 (L.tierA EREC (q >>> 40))) (q &&& 1099511627775) = wn := erecKind hwn
  rcases e1 : pinAtW m 32 with _ | ⟨r1, m1⟩
  · rw [e1, stdW.k_pin_at.none] at hW; cases hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok e1 hS.check.pins
  subst m1 r1
  rw [e1] at hW
  have hpn : propextName.run a = .ok (decI (pinW m (1 + (32 : Word).toNat)), a) := by
    simpa [propextName, pinPropext, show PIN_PROPEXT = (32 : Word).toNat from rfl] using hrun1
  simp only [StateT.run_bind, hpn, exc_ok_bind', hname, decI_beq (k := .name) wn _ hwnl hl1]
  by_cases hp : wn = pinW m (1 + (32 : Word).toNat)
  · rw [stdW.k_pin_at.arm1 p n vis q _ m (by rw [ex]; exact hp)] at hW
    simp only [hp, decide_true, ↓reduceIte]
    rcases e2 : callW p n "eq_stored" [vis] m with _ | ⟨r2, m2⟩
    · rw [e2, stdW.k_eq_stored.none] at hW; cases hW
    obtain ⟨hm2, hrun2, hle2⟩ := eqs_call h.std.red h.eqs e2 hS
    subst m2
    rw [e2] at hW
    simp only [StateT.run_bind, hrun2, exc_ok_bind']
    by_cases z2 : r2.headD 0 = 0
    · rw [stdW.k_eq_stored.arm1 p n vis q r2 m z2] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      simp only [z2, bne_self_eq_false, Bool.not_false, ↓reduceIte]
      exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
    rw [stdW.k_eq_stored.arm2 p n vis q r2 m z2] at hW
    simp only [show (r2.headD 0 != 0) = true by simpa using z2, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    rcases e3 : callW p n "std_ax_family" [vis, q, 34, 35, 36, 1, 2, 3, 2, 4, 0] m
      with _ | ⟨r3, m3⟩
    · rw [e3, stdW.k_std_ax_family.none] at hW; cases hW
    rw [e3, stdW.k_std_ax_family.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (fam_specW p h n _ vis q 34 35 36 1 2 3 2 4 0) e3
    obtain ⟨b, a', hrun, hS', hg, hd⟩ := famW_ok h hW3 hS hq (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact ⟨b, a', hrun, hS', hg, by simpa [decW0B] using hd⟩
  rw [stdW.k_pin_at.arm2 p n vis q _ m (by rw [ex]; exact hp), ex] at hW
  simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte]
  rcases e2 : pinAtW m 33 with _ | ⟨r2, m2⟩
  · rw [e2, stdW.k_pin_at_2.none] at hW; cases hW
  obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok e2 hS.check.pins
  subst m2 r2
  rw [e2] at hW
  have hcn : choiceName.run a = .ok (decI (pinW m (1 + (33 : Word).toNat)), a) := by
    simpa [choiceName, pinChoice, show PIN_CHOICE = (33 : Word).toNat from rfl] using hrun2
  simp only [StateT.run_bind, hcn, exc_ok_bind', decI_beq (k := .name) wn _ hwnl hl2]
  by_cases hc : wn = pinW m (1 + (33 : Word).toNat)
  · rw [stdW.k_pin_at_2.arm1 p n vis q wn _ m (by simpa using hc)] at hW
    simp only [hc, decide_true, ↓reduceIte]
    rcases e3 : callW p n "std_ax_family" [vis, q, 37, 38, 39, 4, 5, 6, 1, 3, 1] m
      with _ | ⟨r3, m3⟩
    · rw [e3, stdW.k_std_ax_family.none] at hW; cases hW
    rw [e3, stdW.k_std_ax_family.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (fam_specW p h n _ vis q 37 38 39 4 5 6 1 3 1) e3
    obtain ⟨b, a', hrun, hS', hg, hd⟩ := famW_ok h hW3 hS hq (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    exact ⟨b, a', hrun, hS', hg, by simpa [decW0B] using hd⟩
  rw [stdW.k_pin_at_2.arm2 p n vis q wn _ m (by simpa using hc)] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
  exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩

/-- **`std_axiom_ok(vis, q)` refines `stdAxiomOk`** (through the ROM readers' refinements). -/
@[refines ConRon.Arena.stdAxiomOk]
theorem stdAxiomOk_refines (p : Prog) (h : StdProg2 p) (dn : NIdx → Option ConLeche.Name)
    (_hdn : DnInj dn) (vis : Word) (fe : IFEnv) (q : Word) (cv : IConstantVal) :
    RefAM p "std_axiom_ok" [vis, q]
      (fun m a => StageR vis fe m a ∧ decCV (erecP m) q.toNat = some cv)
      (stdAxiomOk fe cv) (KeepPost vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hq⟩
  refine triple_post (std_specW p h n s₀ vis q) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, a', hrun, hS', hg, hd⟩ := stdW_ok h hm hS hq
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst, hres]; exact ⟨hS', hg, hd⟩⟩

end L.Arena
