import ConAgua.Arena.IndRealPartsC1

/-!
# Refinements of `IndParts`, part 15 (lane `indproofs2`, helper `parts`): `blockShape?`, relations

The twin's `blockShape?` cut at the L functions' boundaries (`blockShape_eq`, by `rfl`: `buildTwin`,
`tailJP` — the result sort's match with the twin's join point — and `finJP`), and the relational lemmas
of `block_shape_seal`, `block_shape_fin`, `block_shape_tail`, `block_shape_build`, `block_shape`,
`block_parts`.

The sims read `lvl_eq_c` through a `CallM` `c` and a hypothesis on it, `LvlHyp`: the call's `Sim` at
every twin state the twin's prefix reaches (`T`) and every memory the model's prefix reaches (`AFr`).
The stubs meet it everywhere (`lvlHyp_stub`); the real call under `StageC` meets it at the prefix of
`blockShape?` (`IndRealPartsC2.lvlHyp_real`).
-/

noncomputable section

set_option experimental.vcgen true

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
  rcases h1 : plgW k m o l with _ | ⟨r1, m1⟩ <;> rw [h1] at hm
  · cases hm
  simp only [plW.plK4] at hm
  rcases h2 : ilF m1 [r1.headD 0, r1.tail.headD 0] with _ | ⟨r2, m2⟩ <;> rw [h2] at hm
  · cases hm
  simp only [plW.plK5, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨us, a1, hrun1, hS1, hg1, hd1, -⟩ := plgW_ok dn vis fe k _ _ _ _ _ _ _ h1 hS hd (by omega) ht
  obtain ⟨x, a2, hrun2, hS2, hg2, hH, hx⟩ :=
    ilF_ok dn vis fe (r1.headD 0) (r1.tail.headD 0) us m1 _ a1 r2 h2 ⟨hS1, hd1⟩
  refine ⟨x, a2, ?_, by simpa using hH, by simpa using hx, hS2, hg1.trans hg2⟩
  simp only [paramLevels, StateT.run_bind, hrun1]
  exact hrun2

/-! ## `block_shape_seal` -/

/-- The shape record's two slices (members at words `0, 1`, recursors at `2, 3`) lie below the
top (lane `indproofs4`: `ShapeSrc` and `RecsB` for `check_block`). -/
def ShapeSl (m : Mem) (q : Word) : Prop :=
  (∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m) ∧
  (∀ o l, iwN m (q.toNat + 2) = some o → iwN m (q.toNat + 3) = some l → o + l ≤ iwTop m)

/-- `block_shape`'s result `(ok, q)` against the twin's `Option BlockShape`. -/
def ShapeR (x : Option BlockShape) (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some bs => r.headD 0 = 1 ∧ DecB (fun m => decBS m (r.tail.headD 0).toNat) m bs ∧ ShapeSl m (r.tail.headD 0)

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
      DecB (fun m => decBS m q.toNat) m' ⟨ms, recs, nP.toNat, decI elim, decI s, lg != 0, ip != 0⟩ ∧
      ShapeSl m' q := by
  obtain ⟨hS', hg, htq, hget⟩ := partsFreshGet h hS (by simp)
  refine ⟨hS', hg, ?_, ?_⟩
  rotate_left
  · have gm : ∀ j (hj : j < 9), iwN m' (q.toNat + j) =
        some ([mo, ml, ro, rl, nP, elim, s, lg, ip][j]'(by simpa using hj)).toNat := fun j hj => by
      have := hget j (by simpa using hj)
      rw [← iwN_truncM (show q.toNat + j < iwTop m' by simp at htq; omega)]
      simp only [iwN, nat?, this]; rfl
    have m0 := gm 0 (by omega); have m1 := gm 1 (by omega); have m2 := gm 2 (by omega)
    have m3 := gm 3 (by omega)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at m0 m1 m2 m3
    refine ⟨fun o l ho hl => ?_, fun o l ho hl => ?_⟩
    · rw [m0] at ho; rw [m1] at hl; cases ho; cases hl; exact Nat.le_trans hms.2 hg.1
    · rw [m2] at ho; rw [m3] at hl; cases ho; cases hl; exact Nat.le_trans hrs.2 hg.1
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
    show decPL (truncM m') (decRS (truncM m')) ro.toNat rl.toNat = some recs from hr2, he', hs', ite_true,
    Option.bind_some]

/-- **`block_shape_seal`'s model refines the twin's last `match large?`.** -/
theorem bsealW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} {mo ml ro2 rl2 nPd s ip lgw elimw : Word} {ms : List MemberShape} {recs : List RecShape}
    {sv : LIdx} {isProp : Bool} {lg : Option NIdx} (hS : StageR dn vis fe m a)
    (hms : PSlR decMS ms mo ml m) (hrs : PSlR decRS recs ro2 rl2 m) (hs : H s) (hsv : decI s = sv)
    (hip : (ip != 0) = isProp) (hlg : LargeR lg [lgw, elimw]) :
    Sim (bsealW m mo ml ro2 rl2 nPd s ip lgw elimw)
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
    rw [ite_eq_left (by rw [h1]; decide)] at e
    rcases h2 : posRecW m [mo, ml, ro2, rl2, nPd, elimw, s, 1, ip] with _ | ⟨q, m2⟩ <;> rw [h2] at e
    · cases e
    rw [bsealW.k_block_shape_pack.arm1] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS2, hg2, hd2, hsl2⟩ := partsPack h2 hS hms hrs he hs
    refine ⟨_, a, rfl, ⟨rfl, ?_, hsl2⟩, hS2, hg2⟩
    rw [← hee, ← hsv, ← hip]; exact hd2
  | none =>
    have h1 : lgw = 0 := hlg
    rw [ite_eq_right (by rw [h1]; decide)] at e
    rcases h3 : naF m [] with _ | ⟨r3, m3⟩ <;> rw [h3] at e
    · cases e
    rw [bsealW.k_intern_nanon.arm1] at e
    obtain ⟨an, a3, hrun3, hS3, hg3, hal, hae⟩ := naF_ok dn vis fe m m3 a r3 h3 hS
    rcases h2 : posRecW m3 [mo, ml, ro2, rl2, nPd, r3.headD 0, s, 0, ip] with _ | ⟨q, m2⟩ <;> rw [h2] at e
    · cases e
    rw [bsealW.k_block_shape_pack.arm1] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨hS2, hg2, hd2, hsl2⟩ := partsPack h2 hS3 (hms.grow decMS_mono hg3) (hrs.grow decRS_mono hg3) hal hs
    refine ⟨some ⟨ms, recs, nPd.toNat, an, sv, false, isProp⟩, a3,
      by simp only [StateT.run_bind, hrun3]; rfl, ⟨rfl, ?_, hsl2⟩, hS2, hg3.trans hg2⟩
    rw [← hae, ← hsv, ← hip]; exact hd2

/-! ## `block_shape_fin` -/

/-- Re-tupling the two result words. -/
theorem _root_.L.Arena.Sim.k3 {α : Type} {mo : Option (List Word × Mem)} {op : AM α} {a : AState}
    {Q R : List Word → α → Mem → AState → Prop} (h : Sim mo op a Q)
    (hq : ∀ r x m a', Q r x m a' → R [r.headD 0, r.tail.headD 0] x m a') : Sim (bgoK3 mo) op a R := by
  intro r m' e
  rcases hm : mo with _ | ⟨r1, m1⟩ <;> rw [hm] at e
  · cases e
  rw [bgoK3_some] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨x, a', h1, h2⟩ := h r1 m1 hm
  exact ⟨x, a', h1, hq _ _ _ _ h2⟩

/-- A `Sim` also records the twin's run. -/
theorem _root_.L.Arena.Sim.withRun {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
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
  rcases h1 : bctW (n + 1) m cso csl with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  rw [bbK8_some] at e
  obtain ⟨hS1, hg1, hct⟩ := bctW_ok (n + 1) m m1 a cso csl cs r1 h1 hS hcs
  revert r m' e
  unfold finRest
  -- `param_levels`
  refine Sim.bindK rfl (fun _ _ => by rw [bbK9])
    (plW_sim hS1 (by rw [decHL_grow3 hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.1)) ?_
  rintro r2 lvls m2 a2 ⟨hlh, hlv, hS2, hg2⟩
  have hg02 := hg1.trans hg2
  -- `block_groups`
  have hgr := bgW_sim (no := no) (nl := nl) (nP := nPd) (k := ctl) hlh n hS2 (hct.grow decCN_mono hg2)
    (hnm.grow (OMono.decHL _ _) hg02) (Nat.le_trans hnb hg02.1)
  rw [hlv, ← hctl] at hgr
  refine Sim.bindK rfl (fun _ _ => by rw [bbK10]) hgr.withRun ?_
  rintro r3 gss m3 a3 ⟨⟨hgs, hS3, hg3⟩, hgrun⟩
  have hg03 := hg02.trans hg3
  have hgl : (r3.tail.headD 0) = ctl := by
    apply UInt64.toNat_inj.mp
    rw [← decPL_length _ hgs.1, blockGroups_length hgrun, hctl]
  rw [hgl] at hgs
  -- `block_shape_members_of` (model only)
  intro r m' e
  rcases h4 : bmoW (n + 1) m3 cto ctl io (r3.headD 0) with _ | ⟨r4, m4⟩ <;> rw [h4] at e
  · cases e
  rw [bbK11_some] at e
  obtain ⟨hS4, hg4, hms⟩ := bmoW_ok (n + 1) m3 m4 a3 cto ctl io (r3.headD 0) cvTs nIdxs gss r4 h4 hS3
    (hts.grow (fun _ => OMono.decCVp _) hg03) (hns.grow (OMono.decNL _ _) hg03)
    (Nat.le_trans hnsb hg03.1) hgs
  have hg04 := hg03.trans hg4
  revert r m' e
  show Sim _ _ a3 _
  -- `block_shape_recs_of`
  refine Sim.bindK rfl (fun _ _ => by rw [bbK12])
    (brsW_sim (n + 1) m4 a3 rso rsl (r0 :: rs) hS4 (hrs.grow decSR_mono hg04) (hnm.grow (OMono.decHL _ _) hg04)
      (Nat.le_trans hnb hg04.1)) ?_
  rintro r5 recsL m5 a5 ⟨hrsl, hS5, hg5⟩
  have hg05 := hg04.trans hg5
  -- `block_shape_large` (model only)
  intro r m' e
  rcases h6 : bslW n m5 (UInt64.ofNat cvp) lo ll with _ | ⟨r6, m6⟩ <;> rw [h6] at e
  · cases e
  simp only [bbK13'] at e
  obtain ⟨hS6, hg6, hlg⟩ := bslW_ok h6 hS5 (by rw [UInt64.toNat_ofNat_of_lt' hcvb]; exact (show DecB (fun m => decCVp m cvp) m r0.1 from hcv).grow (OMono.decCVp _) hg05)
    (by rw [decHL_grow3 hg05 hlb]; exact hl) (Nat.le_trans hlb hg05.1)
  have hlg' : LargeR (largeOf lps r0.1) [r6.headD 0, r6.tail.headD 0] := by
    cases hx : largeOf lps r0.1 <;> rw [hx] at hlg <;> exact hlg
  revert r m' e
  show Sim _ _ a5 _
  refine Sim.k3 (bsealW_sim hS6 (hms.grow decMS_mono (hg5.trans hg6)) (hrsl.grow decRS_mono hg6) hs hsv hip hlg') ?_
  rintro r7 x m7 a7 ⟨hR7, hS7, hg7⟩
  refine ⟨?_, hS7, hg05.trans (hg6.trans hg7)⟩
  cases x with
  | none => exact hR7
  | some bs => exact hR7

/-! ## `block_shape_tail` -/

/-- **What the sims need of the `lvl_eq_c` call** (at fuel `n + 2`, through `c`): its `Sim` at every
twin state `a1` the twin's prefix reaches with the sort `sv` (`T sv a1`) and every memory `m1` the
model's prefix reaches from `m` (`AFr m m1`). -/
def LvlHyp (c : CallM) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (m : Mem) (T : LIdx → AState → Prop) : Prop :=
  ∀ (sv : LIdx) (a1 : AState) (s z : Word) (m1 : Mem), T sv a1 → AFr m m1 → StageR dn vis fe m1 a1 →
    H s → decI s = sv → pinWordV m1 53 = some z →
    Sim (c (n + 2) "lvl_eq_c" [s, z] m1) (lvlEq? sv (decI z)) a1
      (fun r x m' a' => KeepPost dn vis fe decLvlEq m1 m' a' r x)

theorem LvlHyp.mono {c : CallM} {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m m' : Mem} {T T' : LIdx → AState → Prop} (h : LvlHyp c n dn vis fe m T) (hf : AFr m m')
    (hT : ∀ sv a1, T' sv a1 → T sv a1) : LvlHyp c n dn vis fe m' T' :=
  fun sv a1 s z m1 hT' hf1 hS hs hsv hz => h sv a1 s z m1 (hT _ _ hT') (hf.trans hf1) hS hs hsv hz

/-- A `Sim` also records the model's run. -/
theorem _root_.L.Arena.Sim.withEq {β α : Type} {mo : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : Sim mo op a Q) :
    Sim mo op a (fun r x m' a' => Q r x m' a' ∧ mo = some (r, m')) := by
  intro r m' e; obtain ⟨x, a', h1, h2⟩ := h r m' e; exact ⟨x, a', h1, h2, e⟩

/-- **`block_shape_tail`'s model refines the twin's result sort and the rest (`tailJP`).** -/
theorem btW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (c : CallM) (n : Nat) {m : Mem} {a : AState}
    {nPd cto ctl cso csl rso rsl no nl io lo ll : Word} {cvT0 : IConstantVal} {cvTs : List IConstantVal}
    {nIdxs : List Nat} {cs : List (IConstantVal × Nat × Nat)} {r0 : IConstantVal × Nat × Nat × List IRecRule}
    {rs : List (IConstantVal × Nat × Nat × List IRecRule)}
    (hS : StageR dn vis fe m a) (hts : PSlR decCVp (cvT0 :: cvTs) cto ctl m) (hcs : PSlR decSC cs cso csl m)
    (hrs : PSlR decSR (r0 :: rs) rso rsl m)
    (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m ((cvT0 :: cvTs).map (·.name)))
    (hnb : no.toNat + nl.toNat ≤ iwTop m)
    (hns : DecB (fun m => decNL m io.toNat ctl.toNat) m nIdxs) (hnsb : io.toNat + ctl.toNat ≤ iwTop m)
    (hl : decHL m lo.toNat ll.toNat = some cvT0.levelParams) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hc : LvlHyp c n dn vis fe m (fun sv a1 => (bsoTwin nPd.toNat nIdxs cvT0.type).run a = .ok (sv, a1))) :
    Sim (btW c n m nPd cto ctl cso csl rso rsl no nl io ctl lo ll)
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
  refine Sim.bindK rfl (fun _ _ => by rw [btK1])
    (Q := fun r s m' a' => ((H (r.headD 0) ∧ decI (r.headD 0) = s ∧ StageR dn vis fe m' a' ∧ IWGrow m m') ∧
      (bsoTwin nPd.toNat nIdxs cvT0.type).run a = .ok (s, a')) ∧
      bsoW m nPd io ctl (rdW (m.arr64 EREC) (UInt64.ofNat p0 + 3)) = some (r, m')) ?_ ?_
  · have := bsoW_sim (nP := nPd) (ty := rdW (m.arr64 EREC) (UInt64.ofNat p0 + 3)) hS hns hnsb htyl
    rw [htye] at this
    exact this.withRun.withEq
  rintro r1 sv m1 a1 ⟨⟨⟨hs, hsv, hS1, hg1⟩, hrun1⟩, he1⟩
  rw [finJP_eq]
  intro r m' e
  rcases hz : pinWordV m1 53 with _ | z <;> rw [hz] at e
  · cases e
  rw [btK2_some] at e
  obtain ⟨hzrun, -⟩ := pinZero_stage hS1 hz
  revert r m' e
  refine Sim.bind_twin hzrun ?_
  refine Sim.bindK rfl (fun _ _ => by rw [btK3])
    (Q := fun r x m' a' => KeepPost dn vis fe decLvlEq m1 m' a' r x) ?_ ?_
  · exact hc sv a1 (r1.headD 0) z m1 hrun1 (bsoW_afr he1) hS1 hs hsv hz
  rintro r2 x2 m2 a2 ⟨hS2, hg2, hd2⟩
  have hg02 := hg1.trans hg2
  refine Sim.k3 (bfW_sim n hS2 (hts.grow (fun _ => OMono.decCVp _) hg02) (hcs.grow decSC_mono hg02)
    (hrs.grow decSR_mono hg02) (hnm.grow (OMono.decHL _ _) hg02) (Nat.le_trans hnb hg02.1)
    (hns.grow (OMono.decNL _ _) hg02) (Nat.le_trans hnsb hg02.1) (by rw [decHL_grow3 hg02 hlb]; exact hl)
    (Nat.le_trans hlb hg02.1) hs hsv (lvlEq_prop rfl hd2)) ?_
  rintro r x m3 a3 ⟨hR, hS3, hg3⟩
  exact ⟨by cases x <;> exact hR, hS3, hg02.trans hg3⟩

/-! ## `block_shape_build` -/

theorem partsBindOk {α β : Type} {x : AM α} {f : α → AM β} {a a' : AState} {v : β}
    (h : (x >>= f).run a = .ok (v, a')) : ∃ y a1, x.run a = .ok (y, a1) ∧ (f y).run a1 = .ok (v, a') := by
  simp only [StateT.run_bind] at h
  obtain ⟨⟨y, a1⟩, h1, h2⟩ := partsExBind h
  exact ⟨y, a1, h1, h2⟩

theorem bmc_length {nPd k nC : Nat} {names : List NIdx} {rs : List (IConstantVal × Nat × Nat × List IRecRule)} :
    ∀ (cvTs : List IConstantVal) (mm : Nat) (a a' : AState) (ns : List Nat),
    (ConRon.Arena.blockMemberCounts? nPd k nC names rs mm cvTs).run a = .ok (some ns, a') →
    ns.length = cvTs.length
  | [], mm, a, a', ns, h => by
    simp [ConRon.Arena.blockMemberCounts?, StateT.run, pure, StateT.pure, Except.pure] at h; simp [← h]
  | c :: cs, mm, a, a', ns, h => by
    simp only [ConRon.Arena.blockMemberCounts?] at h
    obtain ⟨q, a1, -, h⟩ := partsBindOk h
    obtain ⟨x, a2, -, h⟩ := partsBindOk h
    cases x with
    | none => simp [StateT.run, pure, StateT.pure, Except.pure] at h
    | some c2 =>
      simp only at h
      obtain ⟨y, a3, hy, h⟩ := partsBindOk h
      cases y with
      | none => simp [StateT.run, pure, StateT.pure, Except.pure] at h
      | some ns' =>
        simp [StateT.run, pure, StateT.pure, Except.pure] at h
        rw [← h.1]; simp [bmc_length cs (mm + 1) a2 a3 ns' hy]

/-- `block_member_counts`' model as a `Sim` (from `blockMemberCounts_refines`' proof). -/
theorem bmcW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem} {a : AState}
    {nPd k nC no nl ro rl cto ctl : Word} {names : List NIdx} {cvTs : List IConstantVal}
    {rs : List (IConstantVal × Nat × Nat × List IRecRule)}
    (hS : StageR dn vis fe m a) (hts : PSlR decCVp cvTs cto ctl m)
    (hrs : PSlR decSR rs ro rl m) (hnm : DecB (fun m => decHL m no.toNat nl.toNat) m names)
    (hnb : no.toNat + nl.toNat ≤ iwTop m) :
    Sim (bmcW n m nPd k nC no nl ro rl cto ctl)
      (ConRon.Arena.blockMemberCounts? nPd.toNat k.toNat nC.toNat names rs 0 cvTs) a
      (fun r x m' a' => NsR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro r m' hm
  unfold bmcW at hm
  split at hm
  · cases hm
  rename_i hg
  have b : ∀ w : Word, ¬ 4294967296 ≤ w → w.toNat < 2 ^ 32 := fun w h => by
    rw [UInt64.le_iff_toNat_le] at h; simpa using h
  have hsim := bmgW_sim (b nPd (fun h => hg (Or.inl h))) (b k (fun h => hg (Or.inr (Or.inl h))))
    (b nC (fun h => hg (Or.inr (Or.inr (Or.inl h))))) (b rl (fun h => hg (Or.inr (Or.inr (Or.inr h))))) n
    m a cto ctl 0 cvTs hS hts hrs hnm hnb (by simp; have := hts.2; omega)
  rcases hb : bmgW n m nPd k nC no nl ro rl cto ctl 0 with _ | ⟨r1, m1⟩ <;> rw [hb] at hm
  · cases hm
  rw [bmfK2_some] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨x, a', h1, hR, hS', hg'⟩ := hsim r1 m1 hb
  exact ⟨x, a', h1, NsR_three hR, hS', hg'⟩

/-- A pins pass that returned read the reserved names: the pins are ready. -/
theorem bpoW_ready {n : Nat} {m m' : Mem} {nP cto ctl lo ll ro rl cso csl : Word} {r : List Word}
    (h : bpoW n m nP cto ctl lo ll ro rl cso csl = some (r, m')) (hc : ctl ≠ 0) : pinW m 0 ≠ 0 := by
  unfold bpoW at h
  rcases h1 : bpfW n m cto ctl lo ll with _ | x
  · rw [h1] at h; cases h
  cases n with
  | zero => simp [bpfW] at h1
  | succ n =>
  rw [bpfW_cons n m cto ctl lo ll hc] at h1
  rcases h2 : resContW n m (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cto)) with _ | b
  · rw [h2] at h1; simp [bpfK1] at h1
  cases n with
  | zero => simp [resContW] at h2
  | succ n =>
  rw [resContW_step] at h2
  intro h0; rw [ite_eq_left h0] at h2; cases h2

/-- The twin's prefix of `buildTwin` up to `lvlEq?`: the counts, the reserved names, the result sort
`sv` (`LvlHyp`'s `T`). -/
def TbbT (nP : Nat) (cvT0 : IConstantVal) (cvTs : List IConstantVal) (cs : List (IConstantVal × Nat × Nat))
    (rs : List (IConstantVal × Nat × Nat × List IRecRule)) (a : AState) (sv : LIdx) (a1 : AState) : Prop :=
  ∃ nIdxs a2 R a3,
    (ConRon.Arena.blockMemberCounts? nP cvTs.length cs.length (cvTs.map (·.name)) rs 0 cvTs).run a =
      .ok (some nIdxs, a2) ∧
    (reservedBasisNames : AM (List NIdx)).run a2 = .ok (R, a3) ∧
    (bsoTwin nP nIdxs cvT0.type).run a3 = .ok (sv, a1)

/-- The twin's prefix of `blockShape?` up to `lvlEq?`: the split, then `TbbT`. -/
def TshT (nP : Nat) (blk : List IConstantInfo) (a : AState) (sv : LIdx) (a1 : AState) : Prop :=
  ∃ cvT0 cvTs cs r0 rs, ConRon.Arena.blockSplit blk = some (cvT0 :: cvTs, cs, r0 :: rs) ∧
    TbbT nP cvT0 (cvT0 :: cvTs) cs (r0 :: rs) a sv a1

/-- **`block_shape_build`'s model refines `buildTwin`.** -/
theorem bbW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (c : CallM) (n : Nat) {m : Mem} {a : AState}
    {nPd cto ctl cso csl rso rsl : Word} {cvT0 : IConstantVal} {cvTs : List IConstantVal}
    {cs : List (IConstantVal × Nat × Nat)} {r0 : IConstantVal × Nat × Nat × List IRecRule}
    {rs : List (IConstantVal × Nat × Nat × List IRecRule)}
    (hS : StageR dn vis fe m a) (hts : PSlR decCVp (cvT0 :: cvTs) cto ctl m) (hcs : PSlR decSC cs cso csl m)
    (hrs : PSlR decSR (r0 :: rs) rso rsl m)
    (hc : LvlHyp c n dn vis fe m (TbbT nPd.toNat cvT0 (cvT0 :: cvTs) cs (r0 :: rs) a)) :
    Sim (bbW c n m nPd cto ctl cso csl rso rsl) (buildTwin nPd.toNat (cvT0 :: cvTs) cvT0 cs (r0 :: rs) r0.1) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  have hctl : ctl ≠ 0 := by intro e; subst e; exact absurd (partsPSl_nil hts) (by simp)
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨p0, cv0, ts', he, hw, hpb, hcv0, -⟩ := partsPSl_cons hts hctl
  simp only [List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  have hlen : (cvT0 :: cvTs).length = ctl.toNat := decPL_length _ hts.1
  have hclen : cs.length = csl.toNat := decPL_length _ hcs.1
  intro r m' e
  unfold bbW at e
  rw [hw] at e
  -- names (model only)
  rcases h1 : bsnW (n + 3) m cto ctl with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  rw [bbH1_some] at e
  obtain ⟨hS1, hg1, hd1, hb1⟩ := bsnW_ok (n + 3) m m1 a cto ctl (cvT0 :: cvTs) r1 h1 hS hts
  revert r m' e
  unfold buildTwin
  -- member counts
  have hmc := bmcW_sim (n + 2) (nPd := nPd) (k := ctl) (nC := csl) hS1 (hts.grow (fun _ => OMono.decCVp _) hg1)
    (hrs.grow decSR_mono hg1) (decHL_decB hd1 hb1) hb1
  rw [← hlen, ← hclen] at hmc
  refine Sim.bindK rfl (fun _ _ => by rw [bbH2]) hmc.withRun.withEq ?_
  rintro r2 x2 m2 a2 ⟨⟨⟨hR2, hS2, hg2⟩, hrun2⟩, he2⟩
  have hg02 := hg1.trans hg2
  cases x2 with
  | none =>
    have h0 : r2.headD 0 = 0 := hR2
    simp only [h0, ite_true]
    exact Sim.ret ⟨rfl, hS2, hg02⟩
  | some nIdxs =>
  obtain ⟨h21, hd2, hb2⟩ := hR2
  simp only [h21, show (1 : Word) ≠ 0 by decide, ite_false]
  -- level parameters (model only)
  intro r m' e
  rcases h3 : erToIwW (n + 3) m2 (rdW (m2.arr64 EREC) (UInt64.ofNat p0 + 1)) (rdW (m2.arr64 EREC) (UInt64.ofNat p0 + 2)) with _ | ⟨r3, m3⟩ <;> rw [h3] at e
  · cases e
  rw [bbH3_some] at e
  obtain ⟨hS3, hg3, hd3, ht3⟩ := partsLpsCopy h3 hS2 (hcv0.grow (OMono.decCVp _) hg02) hpb
  have hg03 := hg02.trans hg3
  -- the pins
  rcases h4 : bpoW (n + 2) m3 nPd cto ctl (r3.headD 0) (r3.tail.headD 0) rso rsl cso csl with _ | ⟨r4, m4⟩ <;> rw [h4] at e
  · cases e
  have h0 := bpoW_ready h4 hctl
  have hRrun := pinReserved_run (hS3.1.pins.full h0)
  obtain ⟨hS4, hg4, hr4⟩ := bpoW_ok hRrun h4 hS3 (hts.grow (fun _ => OMono.decCVp _) hg03)
    (hrs.grow decSR_mono hg03) (hcs.grow decSC_mono hg03) hd3 (Nat.le_of_eq ht3)
  have hg04 := hg03.trans hg4
  have hr4' : r4 = [if pinsOf nPd.toNat ((List.range 16).map fun i => decI (pinW m3 (55 + i)))
      cvT0.levelParams (cvT0 :: cvTs) cs (r0 :: rs) then 1 else 0] := hr4
  revert r m' e
  refine Sim.bind_twin hRrun ?_
  cases hpb : pinsOf nPd.toNat ((List.range 16).map fun i => decI (pinW m3 (55 + i)))
      cvT0.levelParams (cvT0 :: cvTs) cs (r0 :: rs) with
  | false =>
    rw [hpb] at hr4'
    rw [bbH4_fail (h := by rw [hr4']; rfl)]
    exact Sim.ret ⟨rfl, hS4, hg04⟩
  | true =>
  rw [hpb] at hr4'
  rw [bbH4_ok (h := by rw [hr4']; decide)]
  simp only [ite_true]
  have hil : r2.tail.tail.headD 0 = ctl := by
    apply UInt64.toNat_inj.mp
    have e1 := mapM_opt_length _ _ _ (show decNL (truncM m2) _ _ = some nIdxs from hd2)
    simp only [List.length_range] at e1
    rw [← e1, bmc_length _ _ _ _ _ hrun2, hlen]
  rw [hil] at hd2 hb2 ⊢
  refine Sim.k3 (btW_sim c n hS4 (hts.grow (fun _ => OMono.decCVp _) hg04) (hcs.grow decSC_mono hg04)
    (hrs.grow decSR_mono hg04) ((decHL_decB hd1 hb1).grow (OMono.decHL _ _) (hg2.trans (hg3.trans hg4)))
    (Nat.le_trans hb1 (hg2.trans (hg3.trans hg4)).1) (hd2.grow (OMono.decNL _ _) (hg3.trans hg4))
    (Nat.le_trans hb2 (hg3.trans hg4).1) (by rw [decHL_grow3 hg4 (Nat.le_of_eq ht3)]; exact hd3)
    (Nat.le_trans (Nat.le_of_eq ht3) hg4.1)
    (hc.mono ((bsnW_afr _ _ _ _ _ _ h1).trans ((bmcW_afr he2).trans ((erToIwW_afr h3).trans (bpoW_afr h4))))
      (fun sv a1 h => ⟨nIdxs, a2, _, a2, hrun2, hRrun, h⟩))) ?_
  rintro r x m5 a5 ⟨hR, hS5, hg5⟩
  exact ⟨by cases x <;> exact hR, hS5, hg04.trans hg5⟩

/-! ## `block_shape`, `block_parts` -/

/-- **The model of `block_shape`** (at exec fuel `n + 5`). -/
def bshW (c : CallM) (n : Nat) (m : Mem) (nPd off l : Word) : Option (List Word × Mem) :=
  match bsW (n + 4) m off l with
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else if rdW (m1.arr64 IW) (r1.tail.headD 0 + 1) = 0 ∨ rdW (m1.arr64 IW) (r1.tail.headD 0 + 5) = 0 then
      some ([0, 0], m1)
    else bgoK3 (bbW c n m1 nPd (rdW (m1.arr64 IW) (r1.tail.headD 0)) (rdW (m1.arr64 IW) (r1.tail.headD 0 + 1))
      (rdW (m1.arr64 IW) (r1.tail.headD 0 + 2)) (rdW (m1.arr64 IW) (r1.tail.headD 0 + 3))
      (rdW (m1.arr64 IW) (r1.tail.headD 0 + 4)) (rdW (m1.arr64 IW) (r1.tail.headD 0 + 5)))

theorem bsh_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St) (nPd off l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 5)) "block_shape" [nPd, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ bshW c n s₀.mem nPd off l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.shape]
  simp only [callFn, blockShape]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      bs_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.rec3 hP.rec6 hP.recs hP.ctors hP.split (n + 4),
      bb_spec p hP c hc n] <;>
    finish (gen := 20) [bshW, rdW_eq, bgoK3_some]

theorem partsW0 {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) : (l = 0) ↔ xs = [] := by
  have := decPL_length _ h.1
  constructor
  · intro e; subst e; simpa using this
  · intro e; subst e; exact UInt64.toNat_inj.mp (by simpa using this.symm)

/-- **`block_shape`'s model refines `blockShape?`.** -/
theorem bshW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (c : CallM) (n : Nat) {m : Mem}
    {a : AState} {nPd off l : Word} {blk : List IConstantInfo} (hS : StageR dn vis fe m a)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) m blk)
    (hc : LvlHyp c n dn vis fe m (TshT nPd.toNat blk a)) :
    Sim (bshW c n m nPd off l) (ConRon.Arena.blockShape? nPd.toNat blk) a
      (fun r x m' a' => ShapeR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  rw [blockShape_eq]
  intro r m' e
  unfold bshW at e
  rcases h1 : bsW (n + 4) m off l with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  simp only at e
  obtain ⟨hS1, hg1, hR1⟩ := bsW_ok (n + 4) m m1 a off l blk r1 h1 hS hblk
  revert r m' e
  cases hsp : ConRon.Arena.blockSplit blk with
  | none =>
    rw [hsp] at hR1
    have h0 : r1.headD 0 = 0 := hR1
    intro r m' e
    rw [ite_eq_left h0] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    exact ⟨none, a, rfl, rfl, hS1, hg1⟩
  | some t =>
  obtain ⟨cvTs, cs, rs⟩ := t
  rw [hsp] at hR1
  obtain ⟨h01, hq6, hts, hcs, hrs⟩ := hR1
  intro r m' e
  rw [ite_eq_right (by rw [h01]; decide)] at e
  dsimp only
  generalize hq : r1.tail.headD 0 = q at e hq6 hts hcs hrs
  by_cases hz : rdW (m1.arr64 IW) (q + 1) = 0 ∨ rdW (m1.arr64 IW) (q + 5) = 0
  · rw [ite_eq_left hz] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    have : cvTs = [] ∨ rs = [] := by
      rcases hz with hz | hz
      · exact Or.inl ((partsW0 hts).mp hz)
      · exact Or.inr ((partsW0 hrs).mp hz)
    refine ⟨none, a, ?_, rfl, hS1, hg1⟩
    rcases this with rfl | rfl
    · rfl
    · cases cvTs <;> rfl
  rw [ite_eq_right hz] at e
  obtain ⟨cvT0, cvTs', rfl⟩ : ∃ c cs', cvTs = c :: cs' := by
    cases cvTs with
    | nil => exact absurd (Or.inl ((partsW0 hts).mpr rfl)) hz
    | cons c cs' => exact ⟨c, cs', rfl⟩
  obtain ⟨r0, rs', rfl⟩ : ∃ c cs', rs = c :: cs' := by
    cases rs with
    | nil => exact absurd (Or.inr ((partsW0 hrs).mpr rfl)) hz
    | cons c cs' => exact ⟨c, cs', rfl⟩
  revert r m' e
  show Sim _ (buildTwin nPd.toNat (cvT0 :: cvTs') cvT0 cs (r0 :: rs') r0.1) a _
  refine Sim.k3 (bbW_sim c n hS1 hts hcs hrs
    (hc.mono (bsW_afr _ _ _ _ _ _ h1) (fun sv a1 h => ⟨cvT0, cvTs', cs, r0, rs', hsp, h⟩))) ?_
  rintro r x m2 a2 ⟨hR, hS2, hg2⟩
  exact ⟨by cases x <;> exact hR, hS2, hg1.trans hg2⟩

/-- `block_parts`' result against the twin's `Option BlockParts`. -/
def PartsR (x : Option BlockParts) (r : List Word) (m : Mem) : Prop :=
  match x with
  | none => r.headD 0 = 0
  | some bp => r.headD 0 = 1 ∧ DecB (fun m => decBP m (r.tail.headD 0).toNat) m bp ∧
      ShapeSl m (r.tail.headD 0)

theorem bpa_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c) (n : Nat) (s₀ : St) (nPd off l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 6)) "block_parts" [nPd, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ bgoK3 (bshW c n s₀.mem nPd off l) = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hP.parts]
  simp only [callFn, blockParts]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, bsh_spec p hP c hc n] <;>
    finish (gen := 20) [bgoK3_some]

/-- **`block_parts`' model refines `blockParts?`** (`bshW_sim`). -/
theorem bpW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (c : CallM) (n : Nat) {m : Mem}
    {a : AState} {nPd off l : Word} {blk : List IConstantInfo} (hS : StageR dn vis fe m a)
    (hblk : DecB (fun m => decEBlk dn m off.toNat l.toNat) m blk)
    (hc : LvlHyp c n dn vis fe m (TshT nPd.toNat blk a)) :
    Sim (bgoK3 (bshW c n m nPd off l)) (ConRon.Arena.blockParts? nPd.toNat blk) a
      (fun r x m' a' => PartsR x r m' ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  unfold ConRon.Arena.blockParts?
  intro r m' e
  rcases h1 : bshW c n m nPd off l with _ | ⟨r1, m1⟩ <;> rw [h1] at e
  · cases e
  rw [bgoK3_some] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨x, a', hrun, hR, hS', hg'⟩ := bshW_sim c n hS hblk hc r1 m1 h1
  cases x with
  | none =>
    exact ⟨none, a', by simp only [StateT.run_bind, hrun]; rfl, hR, hS', hg'⟩
  | some bs =>
    obtain ⟨h1', hd, hsl⟩ := hR
    refine ⟨some ⟨bs⟩, a', by simp only [StateT.run_bind, hrun]; rfl, ⟨h1', ?_, hsl⟩, hS', hg'⟩
    show decBP (truncM m1) _ = _
    simp only [decBP, show decBS (truncM m1) (r1.tail.headD 0).toNat = some bs from hd, bind, pure,
      Option.bind_some, List.headD_cons, List.tail_cons]

end L.Ind
