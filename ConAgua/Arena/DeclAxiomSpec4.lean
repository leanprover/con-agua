module

public import ConAgua.Arena.DeclAxiomSpec3
public import ConAgua.Arena.DeclStepSpec
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Arena.LdRd
public import ConAgua.L.ModelGen

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

l_model fam_specW (p : Prog) (h : StdProg2 p)
  fns [h.fam ↦ famW list]
  specs [pinAt_specW p h.std.red.pa n, callW_spec p n "find_pinned", callW_spec p n "rom_cv",
    mp_specW p h.std.red.canon h.std.red.mp n]
  grind [arena_grind] extra [ld64_rd_spec]

l_model std_specW (p : Prog) (h : StdProg2 p)
  fns [h.std.std ↦ stdW list]
  specs [pinAt_specW p h.std.red.pa n, callW_spec p n "rom_ci", callW_spec p n "find_is",
    callW_spec p n "std_ax_family"]
  grind [arena_grind] extra [ld64_rd_spec]

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
  rw [famW.arm1] at hW
  unfold famT
  -- the first clause
  rcases e1 : pinAtW m s1 with _ | ⟨r1, m1⟩ <;> simp only [e1, famW.k_pin_at, reduceCtorEq] at hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok e1 hS.check.pins
  rw [hm1, hr1] at hW
  simp only [List.headD_cons] at hW
  simp only [StateT.run_bind, hrun1, exc_ok_bind']
  rcases e2 : callW p n "find_pinned" [vis, pinW m (1 + s1.toNat), 3, 0, 0, i1] m with _ | ⟨r2, m2⟩ <;> simp only [e2, famW.k_find_pinned, reduceCtorEq] at hW
  obtain ⟨b2, a2, hrun2, hS2, hg2, hd2⟩ := fp_call h e2 hS hl1 (.inl rfl) h1
  simp only [hrun2, exc_ok_bind']
  by_cases z2 : r2.headD 0 = 0
  · rw [ite_eq_left z2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b2 = false := by rw [← hd2.1]; simpa using z2
    exact ⟨false, a2, by simp [hb]; rfl, hS2, hg2, by simp [decW0B]⟩
  rw [ite_eq_right z2] at hW
  have hb2 : b2 = true := by rw [← hd2.1]; simpa using z2
  simp only [hb2, Bool.not_true, Bool.false_eq_true, ite_false]
  -- the second clause
  rcases e3 : pinAtW m2 s2 with _ | ⟨r3, m3⟩ <;> simp only [e3, famW.k_pin_at_2, reduceCtorEq] at hW
  obtain ⟨hm3, hr3, hl3, hrun3⟩ := pinAtW_ok e3 hS2.check.pins
  rw [hm3, hr3] at hW
  simp only [List.headD_cons] at hW
  simp only [StateT.run_bind, hrun3, exc_ok_bind']
  rcases e4 : callW p n "find_pinned" [vis, pinW m2 (1 + s2.toNat), 4, c2, c2, i2] m2 with _ | ⟨r4, m4⟩ <;> simp only [e4, famW.k_find_pinned_2, reduceCtorEq] at hW
  obtain ⟨b4, a4, hrun4, hS4, hg4, hd4⟩ := fp_call h e4 hS2 hl3 (.inr (.inl rfl)) h2
  simp only [hrun4, exc_ok_bind']
  by_cases z4 : r4.headD 0 = 0
  · rw [ite_eq_left z4] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b4 = false := by rw [← hd4.1]; simpa using z4
    exact ⟨false, a4, by simp [hb]; rfl, hS4, hg2.trans hg4, by simp [decW0B]⟩
  rw [ite_eq_right z4] at hW
  have hb4 : b4 = true := by rw [← hd4.1]; simpa using z4
  simp only [hb4, Bool.not_true, Bool.false_eq_true, ite_false]
  -- the third clause
  rcases e5 : pinAtW m4 s3 with _ | ⟨r5, m5⟩ <;> simp only [e5, famW.k_pin_at_3, reduceCtorEq] at hW
  obtain ⟨hm5, hr5, hl5, hrun5⟩ := pinAtW_ok e5 hS4.check.pins
  rw [hm5, hr5] at hW
  simp only [List.headD_cons] at hW
  simp only [StateT.run_bind, hrun5, exc_ok_bind']
  rcases e6 : callW p n "find_pinned" [vis, pinW m4 (1 + s3.toNat), 5, c3, c3, i3] m4 with _ | ⟨r6, m6⟩ <;> simp only [e6, famW.k_find_pinned_3, reduceCtorEq] at hW
  obtain ⟨b6, a6, hrun6, hS6, hg6, hd6⟩ := fp_call h e6 hS4 hl5 (.inr (.inr rfl)) h3
  simp only [hrun6, exc_ok_bind']
  by_cases z6 : r6.headD 0 = 0
  · rw [ite_eq_left z6] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b6 = false := by rw [← hd6.1]; simpa using z6
    exact ⟨false, a6, by simp [hb]; rfl, hS6, hg2.trans (hg4.trans hg6), by simp [decW0B]⟩
  rw [ite_eq_right z6] at hW
  have hb6 : b6 = true := by rw [← hd6.1]; simpa using z6
  simp only [hb6, Bool.not_true, Bool.false_eq_true, ite_false]
  -- the axiom's own pin
  rcases e7 : callW p n "rom_cv" [cvid] m6 with _ | ⟨r7, m7⟩ <;> simp only [e7, famW.k_rom_cv, reduceCtorEq] at hW
  obtain ⟨pin, a7, hrun7, hS7, hg7, hpin⟩ := h.red.rom.cv dn vis fe cvid hcv n m6 a6 r7 m7 hS6 e7
  have hg := hg2.trans (hg4.trans (hg6.trans hg7))
  have hq7 : decCV (erA m7) q.toNat = some cv := ArrExt.decCV (IWGrow.erecExt hg) hq
  have hW' : mpW m7 q (r7.headD 0) = some (r, m') := by
    unfold mpW at hW ⊢; simpa [famW.k_matches_pin] using hW
  obtain ⟨hm8, hrun8, hd8⟩ := mpW_ok (a := a7) hW' hS7.iw.erSize hq7
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
  rw [stdW.arm1] at hW
  rw [stdAxiomOk_fam, hname]
  rcases e1 : pinAtW m 32 with _ | ⟨r1, m1⟩ <;> simp only [e1, stdW.k_pin_at, reduceCtorEq] at hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok e1 hS.check.pins
  rw [hm1, ewn] at hW
  have ep : r1.headD 0 = pinW m (1 + (32 : Word).toNat) := by rw [hr1]; rfl
  have hbeq : ((decI wn : NIdx) == decI (pinW m (1 + (32 : Word).toNat))) =
      decide (wn = pinW m (1 + (32 : Word).toNat)) := decI_beq wn _ hwnl hl1
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hbeq]
  by_cases ep1 : wn = r1.headD 0
  · rw [ite_eq_left ep1] at hW
    rw [ep] at ep1
    simp only [ep1, decide_true, ite_true]
    -- `propext`: the pinned `Eq`
    rcases e2 : pinAtW m 0 with _ | ⟨r2, m2⟩ <;> simp only [e2, stdW.k_pin_at_2, reduceCtorEq] at hW
    obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok e2 hS.check.pins
    rw [hm2, hr2] at hW
    simp only [List.headD_cons] at hW
    simp only [StateT.run_bind, hrun2, exc_ok_bind']
    rcases e3 : callW p n "rom_ci" [0] m with _ | ⟨r3, m3⟩ <;> simp only [e3, stdW.k_rom_ci, reduceCtorEq] at hW
    obtain ⟨ea, a3, hrun3, hS3, hg3, hea⟩ := h.std.red.rom.ci dn vis fe 0 (by decide) n m a r3 m3 hS e3
    have hrun3' : eqA.run a = .ok (ea, a3) := hrun3
    simp only [hrun3', exc_ok_bind']
    rcases e4 : callW p n "find_is" [vis, pinW m (1 + (0 : Word).toNat), r3.headD 0] m3 with _ | ⟨r4, m4⟩ <;> simp only [e4, stdW.k_find_is, reduceCtorEq] at hW
    obtain ⟨s4, hs4, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (findIs_spec p h.std.red.canon dn vis fe hdn _ _ ea n ⟨m3, Locals.init []⟩ a3
        ⟨hS3, hl2, decRCI_get hea⟩) e4
    subst hs4
    simp only [AM.st_pure, AM.res_pure] at hS4 hb4
    by_cases z4 : r4.headD 0 = 0
    · rw [ite_eq_left z4] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hf : (fe.find? (decI (pinW m (1 + (0 : Word).toNat))) == some ea) = false := by
        rw [← hb4]; simpa using z4
      refine ⟨false, a3, ?_, hS4, hg3.trans hg4, by simp [decW0B]⟩
      simp only [bne, hf, Bool.not_false, ite_true]
      rfl
    rw [ite_eq_right z4] at hW
    have ht : (fe.find? (decI (pinW m (1 + (0 : Word).toNat))) == some ea) = true := by
      rw [← hb4]; simpa using z4
    simp only [bne, ht, Bool.not_true, Bool.false_eq_true, ite_false]
    -- the `Iff` family
    rcases e5 : callW p n "std_ax_family" [vis, q, 34, 35, 36, 2, 3, 4, 2, 4, 0] s4.mem with _ | ⟨r5, m5⟩ <;> simp only [e5, stdW.k_std_ax_family, reduceCtorEq] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨b, a5, hrun5, hS5, hg5, hd5⟩ := fam_call h e5 hS4
      (ArrExt.decCV (IWGrow.erecPExt (hg3.trans hg4)) hq) (by decide) (by decide) (by decide)
      (by decide)
    exact ⟨b, a5, hrun5, hS5, hg3.trans (hg4.trans hg5), hd5⟩
  · rw [ite_eq_right ep1] at hW
    rw [ep] at ep1
    simp only [ep1, decide_false, Bool.false_eq_true, ite_false]
    -- `choice`
    rcases e2 : pinAtW m 33 with _ | ⟨r2, m2⟩ <;> simp only [e2, stdW.k_pin_at_3, reduceCtorEq] at hW
    obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok e2 hS.check.pins
    rw [hm2] at hW
    have ec : r2.headD 0 = pinW m (1 + (33 : Word).toNat) := by rw [hr2]; rfl
    have hbeqc : ((decI wn : NIdx) == decI (pinW m (1 + (33 : Word).toNat))) =
        decide (wn = pinW m (1 + (33 : Word).toNat)) := decI_beq wn _ hwnl hl2
    simp only [StateT.run_bind, hrun2, exc_ok_bind', hbeqc]
    by_cases ec1 : wn = r2.headD 0
    · rw [ite_eq_left ec1] at hW
      rw [ec] at ec1
      simp only [ec1, decide_true, ite_true]
      rcases e3 : callW p n "std_ax_family" [vis, q, 37, 38, 39, 5, 6, 7, 1, 3, 1] m with _ | ⟨r3, m3⟩ <;> simp only [e3, stdW.k_std_ax_family, reduceCtorEq] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨b, a3, hrun3, hS3, hg3, hd3⟩ := fam_call h e3 hS hq (by decide) (by decide)
        (by decide) (by decide)
      exact ⟨b, a3, hrun3, hS3, hg3, hd3⟩
    · rw [ite_eq_right ec1] at hW
      rw [ec] at ec1
      simp only [ec1, decide_false, Bool.false_eq_true, ite_false]
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
