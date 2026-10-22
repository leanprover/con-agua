import ConAgua.Arena.IndPartsSpec14

/-!
# Refinements of `IndParts`, part 15 (lane `indproofs2`, helper `parts`): `blockShape?`, relations

The twin's `blockShape?` cut at the L functions' boundaries (`blockShape_eq`, by `rfl`: `buildTwin`,
`tailJP` — the result sort's match with the twin's join point — and `finJP`), and the relational lemmas
of `block_shape_seal`, `block_shape_fin`, `block_shape_tail`, `block_shape_build`, `block_shape`,
`block_parts`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The twin, cut -/

def finJP (nP : Nat) (cvTs : List IConstantVal) (nIdxs : List Nat) (lps : List NIdx)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (cvR0 : IConstantVal) (s : LIdx) : AM (Option BlockShape) := do
  let z ← zeroLevel
  let eq ← lvlEq? s z
  let isProp : Bool := match eq with
    | some true => true
    | some false => false
    | none => false
  let ctors : List (IConstantVal × Nat) := cs.map fun c => (c.1, c.2.2)
  let lvls ← paramLevels lps
  let groups ← ConRon.Arena.blockGroups (cvTs.map (·.name)) lvls nP cvTs.length ctors
  let members : List MemberShape := ((cvTs.zip nIdxs).zip groups).map fun a => ⟨a.1.1, a.1.2, a.2⟩
  let recsL ← rs.mapM fun r => do
    let tgt ← ConRon.Arena.recTargetOf (cvTs.map (·.name)) r.2.1 r.1.type
    pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩ : RecShape)
  let large? : Option NIdx := match cvR0.levelParams with
    | [] => none
    | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
  match large? with
  | some elim => pure (some ⟨members, recsL, nP, elim, s, true, isProp⟩)
  | none => do
    let anon ← internNNode .anonymous
    pure (some ⟨members, recsL, nP, anon, s, false, isProp⟩)

def tailJP {X : Type} (nP : Nat) (nIdxs : List Nat) (ty : EIdx) (jp : LIdx → AM X) : AM X := do
  let x ← stripPis (nP + nIdxs.headD 0) ty
  match x with
  | some q => do
    let v ← view q.2
    match v with
    | .sort s => do
      let s ← pure s
      jp s
    | _ => do
      let s ← zeroLevel
      jp s
  | none => do
    let s ← zeroLevel
    jp s

def pinsOf (nP : Nat) (R : List NIdx) (lps : List NIdx) (cvTs : List IConstantVal)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × List IRecRule)) : Bool :=
  (cvTs.all fun c => !R.contains c.name && c.levelParams == lps) &&
    (rs.all fun r => !R.contains r.1.name) &&
    (cs.all fun c => c.2.1 == nP && c.1.levelParams == lps && !R.contains c.1.name)

def buildTwin (nPd : Nat) (cvTs : List IConstantVal) (cvT0 : IConstantVal)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (cvR0 : IConstantVal) : AM (Option BlockShape) := do
  match ← blockMemberCounts? nPd cvTs.length cs.length (cvTs.map (·.name)) rs 0 cvTs with
  | none => pure none
  | some nIdxs =>
    let reserved ← reservedBasisNames
    if pinsOf nPd reserved cvT0.levelParams cvTs cs rs then
      tailJP nPd nIdxs cvT0.type (finJP nPd cvTs nIdxs cvT0.levelParams cs rs cvR0)
    else pure none

theorem blockShape_eq (nPd : Nat) (block : List IConstantInfo) :
    ConRon.Arena.blockShape? nPd block = (match ConRon.Arena.blockSplit block with
      | none => pure none
      | some (cvTs, cs, rs) =>
        match cvTs, rs with
        | cvT0 :: _, (cvR0, _, _, _) :: _ => buildTwin nPd cvTs cvT0 cs rs cvR0
        | _, _ => pure none) := by
  unfold ConRon.Arena.blockShape?
  rfl

theorem tailJP_eq {X : Type} (nP : Nat) (nIdxs : List Nat) (ty : EIdx) (jp : LIdx → AM X) :
    tailJP nP nIdxs ty jp = bsoTwin nP nIdxs ty >>= jp := by
  unfold tailJP bsoTwin
  rw [bind_assoc]
  congr 1; funext x
  cases x with
  | none => rfl
  | some q =>
    simp only [bind_assoc]
    congr 1; funext v
    cases v <;> simp

/-- `paramLevels` as a `Sim` (from lane `indproofs`' `plgW_ok`, through `intern_ls_iw`). -/
theorem plW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {k : Nat} {m : Mem}
    {a : AState} {o l : Word} {lps : List NIdx} (hS : StageR dn vis fe m a)
    (hd : decHL m o.toNat l.toNat = some lps) (ht : o.toNat + l.toNat ≤ iwTop m) :
    Sim (plW k m o l) (paramLevels lps) a
      (fun r x m' a' => H (r.headD 0) ∧ decI (r.headD 0) = x ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro r m' hm
  cases k with
  | zero => cases hm
  | succ k =>
  rw [plW_succ] at hm
  cases h1 : plgW k m o l with
  | none => rw [h1] at hm; cases hm
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1] at hm
  simp only [plW.plK4] at hm
  cases h2 : stubM "intern_ls_iw" m1 [r1.headD 0, r1.tail.headD 0] with
  | none => rw [h2] at hm; cases hm
  | some y =>
  obtain ⟨r2, m2⟩ := y
  rw [h2] at hm
  simp only [plW.plK5, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨us, a1, hrun1, hS1, hg1, hd1, -⟩ := plgW_ok dn vis fe k _ _ _ _ _ _ _ h1 hS hd (by omega) ht
  obtain ⟨x, a2, hrun2, hS2, hg2, hH, hx⟩ :=
    internLsIw_spec dn vis fe (r1.headD 0) (r1.tail.headD 0) us m1 _ a1 r2 h2 ⟨hS1, hd1⟩
  refine ⟨x, a2, ?_, by simpa using hH, by simpa using hx, hS2, hg1.trans hg2⟩
  simp only [paramLevels, StateT.run_bind, hrun1]
  exact hrun2

/-! ## `block_shape_seal` -/

/-- `block_shape`'s result `(ok, q)` against the twin's `Option BlockShape`. -/
def ShapeR (x : Option BlockShape) (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some bs => r.headD 0 = 1 ∧ DecB (fun m => decBS m (r.tail.headD 0).toNat) m bs

/-- A fresh record's words, in the cut pool. -/
theorem partsFreshGet {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m'))
    (hS : StageR dn vis fe m a) (hl : ws.length < 2 ^ 64) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ q.toNat + ws.length = iwTop m' ∧
      ∀ j (hj : j < ws.length), (iwA (truncM m'))[q.toNat + j]? = some ws[j] := by
  obtain ⟨hS', hg, hq, htop, hget⟩ := posRecW_stage h hS hl
  refine ⟨hS', hg, by omega, fun j hj => ?_⟩
  rw [truncM_iw_eq (by omega)]
  simp only [iwA, hget j hj, List.getElem?_eq_getElem hj]

/-- **The packed `BlockShape` record, decoded.** -/
theorem partsPack {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {q mo ml ro rl nP elim s lg ip : Word} {ms : List MemberShape} {recs : List RecShape}
    (h : posRecW m [mo, ml, ro, rl, nP, elim, s, lg, ip] = some (q, m')) (hS : StageR dn vis fe m a)
    (hms : PSlR decMS ms mo ml m) (hrs : PSlR decRS recs ro rl m) (he : H elim) (hs : H s) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      DecB (fun m => decBS m q.toNat) m' ⟨ms, recs, nP.toNat, decI elim, decI s, lg != 0, ip != 0⟩ := by
  obtain ⟨hS', hg, -, hget⟩ := partsFreshGet h hS (by simp)
  refine ⟨hS', hg, ?_⟩
  have g : ∀ j (hj : j < 9), (iwA (truncM m'))[q.toNat + j]? = some ([mo, ml, ro, rl, nP, elim, s, lg, ip][j]'(by simpa using hj)) :=
    fun j hj => hget j (by simpa using hj)
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega); have g3 := g 3 (by omega)
  have g4 := g 4 (by omega); have g5 := g 5 (by omega); have g6 := g 6 (by omega); have g7 := g 7 (by omega)
  have g8 := g 8 (by omega)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  have hm2 := (hms.grow decMS_mono hg).1
  have hr2 := (hrs.grow decRS_mono hg).1
  show decBS (truncM m') q.toNat = _
  simp only [decBS, decAt, iwN, iwH, iwB, nat?, hd?, bool?, g0, g1, g2, g3, g4, g5, g6, g7, g8, Nat.add_assoc,
    Option.map_some, Option.bind_some, bind, pure]
  have he' : elim.toNat < 2 ^ 32 := he
  have hs' : s.toNat < 2 ^ 32 := hs
  simp only [show decPL (truncM m') (decMS (truncM m')) mo.toNat ml.toNat = some ms from hm2,
    show decPL (truncM m') (decRS (truncM m')) ro.toNat rl.toNat = some recs from hr2, he', hs', if_true,
    Option.bind_some]

end L.Ind
