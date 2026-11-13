module

import ConAgua.Arena.DeclCanonSpec2
public import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.Arena.DeclAxiomSpec2
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPosSpec.EnvFindWHit
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsNat
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# The standard axioms: `find_pinned`, `std_axiom_ok` (lane `decls3`)

`find_pinned(vis, n, k, a, b, id)` is one clause of `stdAxiomOk`: the stored constant `n` has the
pinned shape (`k = 3` an inductive, `4` a constructor with counts `a`, `b`, `5` a recursor with
counts `a`, `b`) and its constant value matches the pin `rom_ci(id)`'s (`ci_to_cv`, helper
`decls3-canon`). `std_axiom_ok(vis, q)` runs the pinned `Eq` test and three clauses for `propext`,
or three clauses for `Classical.choice`. Through the ROM stubs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The pinned shape `(k, a, b)` of a stored constant: its constant value when it has the shape. -/
def fpShape (k a b : Word) : IConstantInfo → Option IConstantVal
  | .indInfo cv _ => if k = 3 then some cv else none
  | .ctorInfo cv nP nF _ => if k = 4 ∧ nP = a.toNat ∧ nF = b.toNat then some cv else none
  | .recInfo cv mI rP _ _ => if k = 5 ∧ mI = a.toNat ∧ rP = b.toNat then some cv else none
  | _ => none

/-- The pin of a clause: the ROM constant's constant value. -/
def romPinT (id : Nat) : AM IConstantVal := do return (← romCiT id).toConstantVal

/-- A clause of `stdAxiomOk`: the stored constant has the pinned shape, its constant value matches
the pin. -/
def clausePT (fe : IFEnv) (nm : NIdx) (k a b : Word) (T : AM IConstantVal) : AM Bool :=
  match (fe.find? nm).bind (fpShape k a b) with
  | some cvT => do cvT.matchesPin (← T)
  | none => pure false

/-- The lookups of the standard axioms' test. -/
structure StdProg (p : Prog) : Prop where
  red : RedProg p
  fp : p.lookup "find_pinned" = some findPinned
  std : p.lookup "std_axiom_ok" = some stdAxiomOkL

/-- **The model of `find_pinned(vis, n, k, a, b, id)`.** -/
l_model fp_specW (p : Prog) (hp : p.lookup "find_pinned" = some findPinned)
  fns [hp ↦ fpW list]
  specs [callW_spec p n "env_find", callW_spec p n "rom_ci", callW_spec p n "ci_to_cv",
    callW_spec p n "matches_pin"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- Two count words against `a`, `b`, as the shape's counts. -/
theorem counts_iff {w5 w6 a b : Word} : (w5 = a ∧ w6 = b) ↔ (w5.toNat = a.toNat ∧ w6.toNat = b.toNat) :=
  ⟨fun ⟨h5, h6⟩ => ⟨by rw [h5], by rw [h6]⟩,
    fun ⟨h5, h6⟩ => ⟨UInt64.toNat_inj.mp h5, UInt64.toNat_inj.mp h6⟩⟩

/-- **A `find_pinned` call's run, against its clause.** -/
theorem fp_call {p : Prog} (h : StdProg p) {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {nm k ca cb id : Word} {r : List Word}
    (hc : callW p n "find_pinned" [vis, nm, k, ca, cb, id] m = some (r, m'))
    (hS : StageR vis fe m a) (hnm : nm.toNat < 2 ^ 32) (hk : k = 3 ∨ k = 4 ∨ k = 5)
    (hid : id.toNat < 7) :
    ∃ b a', (clausePT fe (decI nm) k ca cb (romPinT id.toNat)).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fp_specW p h.fp n _ vis nm k ca cb id) hc
  generalize s'.mem = m' at hW
  cases n with
  | zero => simp [fpW.eq_1] at hW
  | succ n =>
  rw [fpW.arm1] at hW
  rcases h1 : callW p n "env_find" [nm, vis] m with _ | ⟨r1, m1⟩
  · rw [h1, fpW.k_env_find.none] at hW; cases hW
  rw [h1] at hW
  obtain ⟨hm1, hr1⟩ := envFind_callR h.red h1
  subst m1 r1
  have decl : (fe.find? (decI nm)).bind (fpShape k ca cb) = none → some ([0], m) = some (r, m') →
      ∃ b a', (clausePT fe (decI nm) k ca cb (romPinT id.toNat)).run a = .ok (b, a') ∧
        StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
    intro hn e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
    simp only [clausePT, hn]; rfl
  by_cases hf : (findRes m vis nm).headD 0 = 0
  · rw [fpW.k_env_find.arm1 p n k ca cb id _ _ hf] at hW
    exact decl (by rw [findRes_miss hS.check.env hnm hf]; rfl) hW
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hS.check.env hnm hf
  generalize hq : (findRes m vis nm).tail.headD 0 = q at hW hci hfind
  obtain ⟨wk, hwk⟩ := decCI_rd hci
  have ek := erecKind hwk
  have pass : ∀ cv, fpShape k ca cb ci = some cv → decCV (erecP m) (q.toNat + CI.cv.toNat) = some cv →
      fpW.j1 p n id q m = some (r, m') →
      ∃ b a', (clausePT fe (decI nm) k ca cb (romPinT id.toNat)).run a = .ok (b, a') ∧
        StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
    intro cv hsh hcv hJ
    rw [fpW.j1.arm1] at hJ
    rcases h2 : callW p n "rom_ci" [id] m with _ | ⟨r2, m2⟩
    · rw [h2, fpW.k_rom_ci.none] at hJ; cases hJ
    rw [h2, fpW.k_rom_ci.arm1] at hJ
    obtain ⟨ci2, a2, hrun2, hS2, hg2, hci2⟩ :=
      h.red.rom.ci (fun _ => none) vis fe id hid n _ a r2 m2 hS h2
    rcases h3 : callW p n "ci_to_cv" [r2.headD 0] m2 with _ | ⟨r3, m3⟩
    · rw [h3, fpW.k_ci_to_cv.none] at hJ; cases hJ
    rw [h3, fpW.k_ci_to_cv.arm1] at hJ
    obtain ⟨s3, rfl, -, hm3, hr3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (ciToCv_spec' p h.red.canon n _ (r2.headD 0)) h3
    simp only at hm3
    rw [hm3] at hJ
    have hpin : decCV (erA m2) (r3.headD 0).toNat = some ci2.toConstantVal := by
      rw [hr3]; exact decCI_cv_rd (erRdOK _) (DecB.get ⟨fun _ _ _ he h => he.2.decCI h⟩ hci2)
    obtain ⟨wn, hwn, -⟩ := decCV_name hcv
    have hq1 : (q + CI.cv).toNat = q.toNat + CI.cv.toNat := off_add_toNat rfl (erecP_lt64 hwn)
    have hcv2 : decCV (erA m2) (q + CI.cv).toNat = some cv := by
      rw [hq1]; exact ArrExt.decCV (L.Ind.IWGrow.ext hg2) hcv
    rcases h4 : callW p n "matches_pin" [q + CI.cv, r3.headD 0] m2 with _ | ⟨r4, m4⟩
    · rw [h4, fpW.k_matches_pin.none] at hJ; cases hJ
    rw [h4, fpW.k_matches_pin.arm1] at hJ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hJ)
    obtain ⟨rfl, hrun4, hd4⟩ := mpW_ok (a := a2) (mp_callR h.red h4) hS2.iw.erSize hcv2 hpin
    refine ⟨_, _, ?_, hS2, hg2, by simpa [decW0B] using hd4⟩
    simp only [clausePT, hfind, hci, Option.bind_some, hsh, romPinT, StateT.run_bind, hrun2,
      L.Arena.except_ok_bind]
    exact hrun4
  by_cases hkw : wk = k
  rotate_left
  · rw [fpW.k_env_find.arm2 p n k ca cb id _ _ hf (by rw [hq, ek]; exact hkw)] at hW
    refine decl ?_ hW
    rw [hfind, hci, Option.bind_some]
    rcases hk with rfl | rfl | rfl
    · have := (decCI_kind3 hci hwk).2 hkw; cases ci <;> simp_all [fpShape]
    · have := (decCI_kind4 hci hwk).2 hkw
      cases ci with
      | ctorInfo cv np nf fam => exact absurd rfl (this cv np nf fam)
      | _ => simp_all [fpShape]
    · have := (decCI_kind5 hci hwk).2 hkw
      cases ci with
      | recInfo cv mi rp kk rules => exact absurd rfl (this cv mi rp kk rules)
      | _ => simp [fpShape]
  subst hkw
  rcases hk with hk3 | hk45
  · subst hk3
    rw [fpW.k_env_find.arm5 p n _ ca cb id _ _ hf (by rw [hq, ek]) rfl, hq] at hW
    obtain ⟨cv, caps, hcv, rfl⟩ := (decCI_kind3 hci hwk).1 rfl
    exact pass cv (by simp [fpShape]) hcv hW
  have hk3 : wk ≠ 3 := by rcases hk45 with rfl | rfl <;> decide
  -- the counts at `+5`, `+6`
  have counts : ∀ {w5 w6 : Word} {cv : IConstantVal} {x y : Nat},
      erecP m (q.toNat + 5) = some w5 → erecP m (q.toNat + 6) = some w6 → x = w5.toNat →
      y = w6.toNat → decCV (erecP m) (q.toNat + CI.cv.toNat) = some cv →
      (∀ cv', fpShape wk ca cb ci = some cv' ↔ (x = ca.toNat ∧ y = cb.toNat) ∧ cv' = cv) →
      ∃ b a', (clausePT fe (decI nm) wk ca cb (romPinT id.toNat)).run a = .ok (b, a') ∧
        StageR vis fe m' a' ∧ IWGrow m m' ∧ decW0B m' r b := by
    intro w5 w6 cv x y e5 e6 hx hy hcv hsh
    have hq5 : (q + 5).toNat = q.toNat + 5 := by
      have := erecP_lt64 e5; rw [UInt64.toNat_add]; simp; omega
    have hq6 : (q + 6).toNat = q.toNat + 6 := by
      have := erecP_lt64 e6; rw [UInt64.toNat_add]; simp; omega
    have r5 := erecKind (q := q + 5) (by rw [hq5]; exact e5)
    have r6 := erecKind (q := q + 6) (by rw [hq6]; exact e6)
    by_cases hz : w5 = ca ∧ w6 = cb
    · rw [fpW.k_env_find.arm4 p n _ ca cb id _ _ hf (by rw [hq, ek]) hk3
        (by rw [hq, r5, r6]; intro c; rcases c with c | c; exact c hz.1; exact c hz.2), hq] at hW
      exact pass cv ((hsh cv).mpr ⟨by rw [hx, hy]; exact counts_iff.mp hz, rfl⟩) hcv hW
    · rw [fpW.k_env_find.arm3 p n _ ca cb id _ _ hf (by rw [hq, ek]) hk3
        (by rw [hq, r5, r6]; exact Classical.byContradiction fun c =>
          hz ⟨Classical.byContradiction fun c5 => c (.inl c5),
            Classical.byContradiction fun c6 => c (.inr c6)⟩)] at hW
      refine decl ?_ hW
      rw [hfind, hci, Option.bind_some]
      cases e : fpShape wk ca cb ci with
      | none => rfl
      | some cv' =>
        obtain ⟨hxy, -⟩ := (hsh cv').mp e
        exact absurd (counts_iff.mpr (by rw [← hx, ← hy]; exact hxy)) hz
  rcases hk45 with rfl | rfl
  · obtain ⟨cv, np, nf, fam, hcv, h5, h6, rfl⟩ := (decCI_kind4 hci hwk).1 rfl
    obtain ⟨w5, e5, rfl⟩ := natD h5
    obtain ⟨w6, e6, rfl⟩ := natD h6
    exact counts e5 e6 rfl rfl hcv fun cv' => by
      simp only [fpShape, true_and]; constructor
      · intro hh; split at hh <;> simp_all
      · rintro ⟨hxy, rfl⟩; simp [hxy]
  · obtain ⟨cv, mi, rp, kk, rules, hcv, h5, h6, rfl⟩ := (decCI_kind5 hci hwk).1 rfl
    obtain ⟨w5, e5, rfl⟩ := natD h5
    obtain ⟨w6, e6, rfl⟩ := natD h6
    exact counts e5 e6 rfl rfl hcv fun cv' => by
      simp only [fpShape, true_and]; constructor
      · intro hh; split at hh <;> simp_all
      · rintro ⟨hxy, rfl⟩; simp [hxy]

/-! ## `eq_stored(vis)` -/

/-- **The model of `eq_stored(vis)`.** -/
l_model eqs_specW (p : Prog) (hp : p.lookup "eq_stored" = some eqStoredL)
  (hpa : p.lookup "pin_at" = some pinAtL)
  fns [hp ↦ eqsW list]
  specs [pinAt_specW p hpa n, callW_spec p n "env_find"]
  grind [arena_grind]

/-- **`eq_stored(vis)` refines `eqStored`**: the memory and the twin unchanged. -/
theorem eqs_call {p : Prog} (h : RedProg p) (hp : p.lookup "eq_stored" = some eqStoredL)
    {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} {m m' : Mem} {r : List Word}
    (hc : callW p n "eq_stored" [vis] m = some (r, m')) (hS : StageR vis fe m a) :
    m' = m ∧ (eqStored fe).run a = .ok ((r.headD 0 != 0), a) ∧ (r.headD 0).toNat ≤ 1 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (eqs_specW p hp h.pa n _ vis) hc
  generalize s'.mem = m' at hW
  cases n with
  | zero => simp [eqsW.eq_1] at hW
  | succ n =>
  rw [eqsW.arm1] at hW
  rcases h1 : pinAtW m 0 with _ | ⟨r1, m1⟩
  · rw [h1, eqsW.k_pin_at.none] at hW; cases hW
  obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok h1 hS.check.pins
  subst m1 r1
  rw [h1, eqsW.k_pin_at.arm1] at hW
  simp only [List.headD_cons] at hW
  rcases h2 : callW p n "env_find" [pinW m (1 + (0 : Word).toNat), vis] m with _ | ⟨r2, m2⟩
  · rw [h2, eqsW.k_env_find.none] at hW; cases hW
  rw [h2, eqsW.k_env_find.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hm2, hr2⟩ := envFind_callR h h2
  subst m2 r2
  refine ⟨rfl, ?_, ?_⟩
  · have hpe : pinEq.run a = .ok (decI (pinW m (1 + (0 : Word).toNat)), a) := by
      simpa [pinEq, show PIN_EQ = (0 : Word).toNat from rfl] using hrun1
    simp only [eqStored, StateT.run_bind, hpe, L.Arena.except_ok_bind]
    show Except.ok _ = Except.ok _
    by_cases h0 : (findRes m vis (pinW m (1 + (0 : Word).toNat))).headD 0 = 0
    · rw [findRes_miss hS.check.env hl1 h0, h0]; rfl
    · obtain ⟨e, ci, hci⟩ := findRes_hit hS.check.env hl1 h0
      rw [e, hci]; simpa [List.headD] using h0
  · simp only [findRes]; split
    · simp
    · split <;> simp

end L.Arena
