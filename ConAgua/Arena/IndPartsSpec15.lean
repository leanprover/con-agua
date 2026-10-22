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

/-- **`block_shape_seal`'s model refines the twin's last `match large?`.** -/
theorem bsealW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem}
    {a : AState} {mo ml ro2 rl2 nPd s ip lgw elimw : Word} {ms : List MemberShape} {recs : List RecShape}
    {sv : LIdx} {isProp : Bool} {lg : Option NIdx} (hS : StageR dn vis fe m a)
    (hms : PSlR decMS ms mo ml m) (hrs : PSlR decRS recs ro2 rl2 m) (hs : H s) (hsv : decI s = sv)
    (hip : (ip != 0) = isProp) (hlg : LargeR lg [lgw, elimw]) :
    Sim (bsealW n m mo ml ro2 rl2 nPd s ip lgw elimw)
      (match lg with
        | some elim => pure (some ⟨ms, recs, nPd.toNat, elim, sv, true, isProp⟩)
        | none => do
          let anon ← internNNode .anonymous
          pure (some ⟨ms, recs, nPd.toNat, anon, sv, false, isProp⟩)) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro r m' e
  unfold bsealW at e
  cases lg with
  | some el =>
    obtain ⟨h1, he, hee⟩ := hlg
    simp only [List.headD_cons] at h1
    simp only [List.tail_cons, List.headD_cons] at he hee
    rw [if_pos (by rw [h1]; decide)] at e
    cases h2 : posRecW m [mo, ml, ro2, rl2, nPd, elimw, s, 1, ip] with
    | none => rw [h2] at e; cases e
    | some x =>
    obtain ⟨q, m2⟩ := x
    rw [h2, bbPack_some] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨hS2, hg2, hd2⟩ := partsPack h2 hS hms hrs he hs
    refine ⟨_, a, rfl, ⟨rfl, ?_⟩, hS2, hg2⟩
    rw [← hee, ← hsv, ← hip]; exact hd2
  | none =>
    have h1 : lgw = 0 := hlg
    rw [if_neg (by rw [h1]; decide)] at e
    cases h3 : stubM "intern_nanon" m [] with
    | none => rw [h3] at e; cases e
    | some x =>
    obtain ⟨r3, m3⟩ := x
    rw [h3, bbK14_some] at e
    obtain ⟨an, a3, hrun3, hS3, hg3, hal, hae⟩ := internNanonStub_spec dn vis fe m m3 a r3 h3 hS
    cases h2 : posRecW m3 [mo, ml, ro2, rl2, nPd, r3.headD 0, s, 0, ip] with
    | none => rw [h2] at e; cases e
    | some x =>
    obtain ⟨q, m2⟩ := x
    rw [h2, bbPack_some] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨hS2, hg2, hd2⟩ := partsPack h2 hS3 (hms.grow decMS_mono hg3) (hrs.grow decRS_mono hg3) hal hs
    refine ⟨some ⟨ms, recs, nPd.toNat, an, sv, false, isProp⟩, a3,
      by simp only [StateT.run_bind, hrun3]; rfl, ⟨rfl, ?_⟩, hS2, hg3.trans hg2⟩
    rw [← hae, ← hsv, ← hip]; exact hd2

/-! ## `block_shape_fin` -/

/-- Re-tupling the two result words. -/
theorem Sim.k3 {α : Type} {mo : Option (List Word × Mem)} {op : AM α} {a : AState}
    {Q R : List Word → α → Mem → AState → Prop} (h : Sim mo op a Q)
    (hq : ∀ r x m a', Q r x m a' → R [r.headD 0, r.tail.headD 0] x m a') : Sim (bgoK3 mo) op a R := by
  intro r m' e
  cases hm : mo with
  | none => rw [hm] at e; cases e
  | some y =>
    obtain ⟨r1, m1⟩ := y
    rw [hm, bgoK3_some] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨x, a', h1, h2⟩ := h r1 m1 hm
    exact ⟨x, a', h1, hq _ _ _ _ h2⟩

/-- A `Sim` also records the twin's run. -/
theorem Sim.withRun {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q r x m' a' ∧ op.run a = .ok (x, a')) := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, h2, h1⟩

/-- `finJP` after `isProp`. -/
def finRest (nP : Nat) (cvTs : List IConstantVal) (nIdxs : List Nat) (lps : List NIdx)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (cvR0 : IConstantVal) (s : LIdx) (isProp : Bool) : AM (Option BlockShape) := do
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

theorem finJP_eq (nP : Nat) (cvTs : List IConstantVal) (nIdxs : List Nat) (lps : List NIdx)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (cvR0 : IConstantVal) (s : LIdx) :
    finJP nP cvTs nIdxs lps cs rs cvR0 s = (do
      let z ← zeroLevel
      let eq ← lvlEq? s z
      finRest nP cvTs nIdxs lps cs rs cvR0 s (isPropOf eq)) := by
  unfold finJP finRest; congr 1

theorem partsMapM_length {α β : Type} (f : α → AM β) : ∀ (l : List α) (a a' : AState) (ys : List β),
    (l.mapM f).run a = .ok (ys, a') → ys.length = l.length
  | [], a, a', ys, h => by simp [StateT.run, pure, StateT.pure, Except.pure] at h; simp [← h.1]
  | x :: l, a, a', ys, h => by
    rw [List.mapM_cons] at h
    simp only [StateT.run_bind] at h
    obtain ⟨⟨y, a1⟩, -, h⟩ := partsExBind h
    obtain ⟨⟨zs, a2⟩, hz, h⟩ := partsExBind h
    have := partsMapM_length f l a1 a2 zs hz
    simp [StateT.run, pure, StateT.pure, Except.pure] at h
    rw [← h.1]; simp [this]

theorem blockGroups_length {names : List NIdx} {lvls : LsIdx} {nP k : Nat} {cs : List (IConstantVal × Nat)}
    {a a' : AState} {gss : List (List (IConstantVal × Nat))}
    (h : (ConRon.Arena.blockGroups names lvls nP k cs).run a = .ok (gss, a')) : gss.length = k := by
  unfold ConRon.Arena.blockGroups at h
  split at h
  · rename_i hk
    simp [StateT.run, pure, StateT.pure, Except.pure] at h
    rw [← h.1]; simp at hk; simp [hk]
  · rw [partsMapM_length _ _ _ _ _ h]; simp

/-- **`block_shape_fin`'s model refines `finRest`.** -/
theorem bfW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem} {a : AState}
    {nPd cto ctl cso csl rso rsl no nl io lo ll s ip : Word} {cvTs : List IConstantVal} {nIdxs : List Nat}
    {lps : List NIdx} {cs : List (IConstantVal × Nat × Nat)} {r0 : IConstantVal × Nat × Nat × List IRecRule}
    {rs : List (IConstantVal × Nat × Nat × List IRecRule)} {sv : LIdx} {isProp : Bool}
    (hS : StageR dn vis fe m a) (hts : PSlR decCVp cvTs cto ctl m) (hcs : PSlR decSC cs cso csl m)
    (hrs : PSlR decSR (r0 :: rs) rso rsl m)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m (cvTs.map (·.name))) (hnb : no.toNat + nl.toNat ≤ iwTop m)
    (hns : DecB (fun m => decNL m io.toNat ctl.toNat) m nIdxs) (hnsb : io.toNat + ctl.toNat ≤ iwTop m)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hs : H s) (hsv : decI s = sv) (hip : (ip != 0) = isProp) :
    Sim (bfW n m nPd cto ctl cso csl rso rsl no nl io lo ll s ip)
      (finRest nPd.toNat cvTs nIdxs lps cs (r0 :: rs) r0.1 sv isProp) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  have hctl : cvTs.length = ctl.toNat := decPL_length _ hts.1
  -- `cvR0`, read first
  have hrl : rsl ≠ 0 := by
    intro e; subst e; exact absurd (partsPSl_nil hrs) (by simp)
  obtain ⟨pc, r0', rs', he, hw, hpb, hr0, -⟩ := partsPSl_cons hrs hrl
  simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨cvp, hcvp, hcv⟩, -, -⟩ := decSR_fields (show decSR (truncM m) pc = some (r0.1, r0.2.1, r0.2.2.1, r0.2.2.2) from hr0)
  obtain ⟨hcw, hcvb, -⟩ := partsIwRd hcvp (UInt64.toNat_ofNat_of_lt' hpb)
  intro r m' e
  unfold bfW at e
  rw [hw, hcw] at e
  -- `block_shape_ctors_of` (model only)
  cases h1 : bctW (n + 1) m cso csl with
  | none => rw [h1] at e; cases e
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1, bbK8_some] at e
  obtain ⟨hS1, hg1, hct⟩ := bctW_ok (n + 1) m m1 a cso csl cs r1 h1 hS hcs
  revert r m' e
  unfold finRest
  -- `param_levels`
  refine Sim.bindK (K := bbK9 n nPd cto ctl cso csl rso rsl 0 (UInt64.ofNat cvp) no nl io lo ll s ip
      (r1.headD 0) (r1.tail.headD 0)) (body := fun r2 m2 => bbK10 n nPd cto ctl cso csl rso rsl 0 (UInt64.ofNat cvp)
      no nl io lo ll s ip (bgW n m2 no nl (r2.headD 0) nPd ctl (r1.headD 0) (r1.tail.headD 0)))
    rfl (fun _ _ => rfl) (plW_sim hS1 (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.1)) ?_
  rintro r2 lvls m2 a2 ⟨hlh, hlv, hS2, hg2⟩
  have hg02 := hg1.trans hg2
  -- `block_groups`
  have hgr := bgW_sim (no := no) (nl := nl) (nP := nPd) (k := ctl) hlh n hS2 (hct.grow decCN_mono hg2)
    (hnm.grow (OMono.decHL _ _) hg02) (Nat.le_trans hnb hg02.1)
  rw [hlv, ← hctl] at hgr
  refine Sim.bindK (K := bbK10 n nPd cto ctl cso csl rso rsl 0 (UInt64.ofNat cvp) no nl io lo ll s ip)
    (body := fun r3 m3 => bbK11 n nPd cto ctl cso csl rso rsl 0 (UInt64.ofNat cvp) no nl lo ll s ip
      (bmoW (n + 1) m3 cto ctl io (r3.headD 0))) rfl (fun _ _ => rfl) hgr.withRun ?_
  rintro r3 gss m3 a3 ⟨⟨hgs, hS3, hg3⟩, hgrun⟩
  have hg03 := hg02.trans hg3
  have hgl : (r3.tail.headD 0) = ctl := by
    apply UInt64.toNat_inj.mp
    rw [← decPL_length _ hgs.1, blockGroups_length hgrun, hctl]
  rw [hgl] at hgs
  -- `block_shape_members_of` (model only)
  intro r m' e
  cases h4 : bmoW (n + 1) m3 cto ctl io (r3.headD 0) with
  | none => rw [h4] at e; cases e
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4, bbK11_some] at e
  obtain ⟨hS4, hg4, hms⟩ := bmoW_ok (n + 1) m3 m4 a3 cto ctl io (r3.headD 0) cvTs nIdxs gss r4 h4 hS3
    (hts.grow (fun _ => OMono.decCVp _) hg03) (hns.grow (OMono.decNL _ _) hg03)
    (Nat.le_trans hnsb hg03.1) hgs
  have hg04 := hg03.trans hg4
  revert r m' e
  show Sim _ _ a3 _
  -- `block_shape_recs_of`
  refine Sim.bindK (K := bbK12 n nPd cto ctl cso csl rso rsl 0 (UInt64.ofNat cvp) lo ll s ip (r4.headD 0)
      (r4.tail.headD 0)) (body := fun r5 m5 => bbK13' n (r4.headD 0) (r4.tail.headD 0) (r5.headD 0)
      (r5.tail.headD 0) nPd s ip (bslW n m5 (UInt64.ofNat cvp) lo ll)) rfl (fun _ _ => rfl)
    (brsW_sim (n + 1) m4 a3 rso rsl (r0 :: rs) hS4 (hrs.grow decSR_mono hg04) (hnm.grow (OMono.decHL _ _) hg04)
      (Nat.le_trans hnb hg04.1)) ?_
  rintro r5 recsL m5 a5 ⟨hrsl, hS5, hg5⟩
  have hg05 := hg04.trans hg5
  -- `block_shape_large` (model only)
  intro r m' e
  cases h6 : bslW n m5 (UInt64.ofNat cvp) lo ll with
  | none => rw [h6] at e; cases e
  | some x6 =>
  obtain ⟨r6, m6⟩ := x6
  rw [h6] at e
  simp only [bbK13'] at e
  obtain ⟨hS6, hg6, hlg⟩ := bslW_ok h6 hS5 (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact (show DecB (fun m => decCVp m cvp) m r0.1 from hcv).grow (OMono.decCVp _) hg05)
    (by rw [decHL_grow3 hg05 hlb]; exact hl) (Nat.le_trans hlb hg05.1)
  have hlg' : LargeR (largeOf lps r0.1) [r6.headD 0, r6.tail.headD 0] := by
    cases hx : largeOf lps r0.1 <;> rw [hx] at hlg <;> exact hlg
  revert r m' e
  show Sim _ _ a5 _
  refine Sim.k3 (bsealW_sim n hS6 (hms.grow decMS_mono (hg5.trans hg6)) (hrsl.grow decRS_mono hg6) hs hsv hip hlg') ?_
  rintro r7 x m7 a7 ⟨hR7, hS7, hg7⟩
  refine ⟨?_, hS7, hg05.trans (hg6.trans hg7)⟩
  cases x with
  | none => exact hR7
  | some bs => exact hR7

/-! ## `block_shape_tail` -/

/-- **`block_shape_tail`'s model refines the twin's result sort and the rest (`tailJP`).** -/
theorem btW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem} {a : AState}
    {nPd cto ctl cso csl rso rsl no nl io lo ll : Word} {cvT0 : IConstantVal} {cvTs : List IConstantVal}
    {nIdxs : List Nat} {cs : List (IConstantVal × Nat × Nat)} {r0 : IConstantVal × Nat × Nat × List IRecRule}
    {rs : List (IConstantVal × Nat × Nat × List IRecRule)}
    (hS : StageR dn vis fe m a) (hts : PSlR decCVp (cvT0 :: cvTs) cto ctl m) (hcs : PSlR decSC cs cso csl m)
    (hrs : PSlR decSR (r0 :: rs) rso rsl m)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m ((cvT0 :: cvTs).map (·.name)))
    (hnb : no.toNat + nl.toNat ≤ iwTop m)
    (hns : DecB (fun m => decNL m io.toNat ctl.toNat) m nIdxs) (hnsb : io.toNat + ctl.toNat ≤ iwTop m)
    (hl : decHL m lo.toNat ll.toNat = some cvT0.levelParams) (hlb : lo.toNat + ll.toNat ≤ iwTop m) :
    Sim (btW n m nPd cto ctl cso csl rso rsl no nl io ctl lo ll)
      (tailJP nPd.toNat nIdxs cvT0.type
        (finJP nPd.toNat (cvT0 :: cvTs) nIdxs cvT0.levelParams cs (r0 :: rs) r0.1)) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  have hctl : ctl ≠ 0 := by intro e; subst e; exact absurd (partsPSl_nil hts) (by simp)
  obtain ⟨p0, cv0, ts', he, hw, hpb, hcv0, -⟩ := partsPSl_cons hts hctl
  simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨htyl, htye⟩ := partsCVType hcv0 (UInt64.toNat_ofNat_of_lt' hpb)
  rw [tailJP_eq]
  unfold btW
  rw [hw]
  refine Sim.bindK (K := btK1 n nPd cto ctl cso csl rso rsl no nl io lo ll)
    (body := fun r1 m1 => btK2 n nPd cto ctl cso csl rso rsl no nl io lo ll (r1.headD 0) m1 (pinWordV m1 53))
    rfl (fun _ _ => rfl)
    (Q := fun r s m' a' => H (r.headD 0) ∧ decI (r.headD 0) = s ∧ StageR dn vis fe m' a' ∧ IWGrow m m') ?_ ?_
  · have := bsoW_sim (nP := nPd) (ty := rdW (m.arr64 EREC) (UInt64.ofNat p0 + 3)) hS hns hnsb htyl
    rwa [htye] at this
  rintro r1 sv m1 a1 ⟨hs, hsv, hS1, hg1⟩
  rw [finJP_eq]
  intro r m' e
  cases hz : pinWordV m1 53 with
  | none => rw [hz] at e; cases e
  | some z =>
  rw [hz, btK2_some] at e
  obtain ⟨hzrun, hzh⟩ := pinZero_stage hS1 hz
  revert r m' e
  refine Sim.bind_twin hzrun ?_
  refine Sim.bindK (K := btK3 n nPd cto ctl cso csl rso rsl no nl io lo ll (r1.headD 0))
    (body := fun r2 m2 => bgoK3 (bfW n m2 nPd cto ctl cso csl rso rsl no nl io lo ll (r1.headD 0)
      (if r2.headD 0 = 2 then 1 else 0))) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => KeepPost dn vis fe decLvlEq m1 m' a' r x) ?_ ?_
  · have := partsSimStub (lvlEqStub_spec dn vis fe (r1.headD 0) z hs hzh) hS1
    rwa [hsv] at this
  rintro r2 x2 m2 a2 ⟨hS2, hg2, hd2⟩
  have hg02 := hg1.trans hg2
  refine Sim.k3 (bfW_sim n hS2 (hts.grow (fun _ => OMono.decCVp _) hg02) (hcs.grow decSC_mono hg02)
    (hrs.grow decSR_mono hg02) (hnm.grow (OMono.decHL _ _) hg02) (Nat.le_trans hnb hg02.1)
    (hns.grow (OMono.decNL _ _) hg02) (Nat.le_trans hnsb hg02.1) (by rw [decHL_grow3 hg02 hlb]; exact hl)
    (Nat.le_trans hlb hg02.1) hs hsv (lvlEq_prop rfl hd2)) ?_
  rintro r x m3 a3 ⟨hR, hS3, hg3⟩
  exact ⟨by cases x <;> exact hR, hS3, hg02.trans hg3⟩

end L.Ind
