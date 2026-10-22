import ConAgua.Arena.IndInstallSpec22

/-!
# Refinements of `IndInstall`, part 23 (lane `indproofs2`, helper `install`): `checkBlockCtors`,
the relation
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A member's fields' sorts: a pointer to `[off, len]` of `[off, len]` level-handle slices. -/
def decISS (m : Mem) (q : Nat) : Option (List (List LIdx)) := decAt m (fun o l => decPL m (decIS m) o l) q

theorem decISS_mono (q : Nat) : OMono (fun m => decISS m q) :=
  OMono.decAt (fun o l => OMono.decPL decIS_mono o l) q

/-- A `bool?` word of a record decoded below the tops, read at its word address. -/
theorem installIwB {m : Mem} {w : Word} {k : Nat} {b : Bool} (h : iwB (truncM m) (w.toNat + k) = some b)
    (hsz : (m.arr64 IW).size < 2 ^ 64) : (rdW (m.arr64 IW) (w + UInt64.ofNat k) != 0) = b := by
  simp only [iwB, bool?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_iw_get hx
  simp only [iwA] at hx'
  have hlt : w.toNat + k < (m.arr64 IW).size := (Array.getElem?_eq_some_iff.mp hx').1
  have hk : k < 2 ^ 64 := by omega
  have hwk : w.toNat + k < 2 ^ 64 := by omega
  have he : (w + UInt64.ofNat k).toNat = w.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hk]; exact Nat.mod_eq_of_lt hwk
  rw [rdW_of_get? he.symm hx']

/-- The lookups of `check_block_ctors`. -/
structure CtorsProg (p : Prog) : Prop extends CstProg p where
  rec2 : p.lookup "rec2" = some rec2
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  one : p.lookup "check_block_ctors_one" = some checkBlockCtorsOne
  go : p.lookup "check_block_ctors_go" = some checkBlockCtorsGo
  ctors : p.lookup "check_block_ctors" = some checkBlockCtors

/-- **A `rec2` header `[off, len]` of a slice decoded below the tops**, decoded below the tops. -/
theorem installRec2PSl {p : Prog} (hP : CtorsProg p) {n : Nat} {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (h : callW p n "rec2" [o, l] m = some (r, m')) (hS : StageR dn vis fe m a) (hx : PSlR f xs o l m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      DecB (fun m => decAt m (fun o l => decPL m (f m) o l) (r.headD 0).toNat) m' xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  refine ⟨hS', hg, ?_⟩
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM s'.mem) (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM s'.mem) ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hd := hx.1.grow (OMono.decPL hf _ _) hg
  show decAt (truncM s'.mem) _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hd

/-- **`check_block_ctors_one`'s model refines one member's `checkSumCtors`.** -/
theorem icboW_sim {p : Prog} (hP : CtorsProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp lo ll ms cv : Word} {bs : BlockShape}
    {msh : MemberShape} {cvv : IConstantVal}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hlps : decHL m lo.toNat ll.toNat = some bs.lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcv : DecB (fun m => decCVp m cv.toNat) m cvv) :
    Sim (icboW p n m vis vis pp lo ll ms cv)
      (checkSumCtors V fe fe msh.cvT.name bs.lps bs.nP msh.nIdx bs.resSort bs.isProp bs.large cvv msh.ctors) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decCNS m (r.headD 0).toNat) m' x.1 ∧
        DecB (fun m => decISS m (r.tail.headD 0).toNat) m' x.2) := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hsz := hS.2.2.2.1
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨-, -, -, -, -, hlg, hpr⟩ := decBS_some hqt
  have h8 := installIwB (w := pp) (k := 8) hpr hsz
  have h7 := installIwB (w := pp) (k := 7) hlg hsz
  rw [show (UInt64.ofNat 8 : Word) = 8 from rfl] at h8
  rw [show (UInt64.ofNat 7 : Word) = 7 from rfl] at h7
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨⟨cvp, hcvp, hcvT⟩, hni, hct⟩ := decMS_some hmsT
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono hct
  have l3 := partsIwLt hcl
  obtain ⟨hw0, hcvb, -⟩ := partsIwRd hcvp (w := ms) rfl
  obtain ⟨hw1, hnib, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hw2, -, -⟩ := partsIwRd hco (w := ms + 2) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hw3, -, -⟩ := partsIwRd hcl (w := ms + 3) (by rw [UInt64.toNat_add]; simp; omega)
  rw [UInt64.ofNat_toNat] at hw2 hw3
  obtain ⟨hn32, hnm⟩ := partsCVName (IWGrow.refl m) hcvT hcvb
  unfold icboW
  rw [hw0, hw1, hw2, hw3, hnpw]
  refine Sim.tail (K := icboK1 p n) (body := fun r1 m1 => icboK2 p n r1 (callW p n "rec2"
      [r1.headD 0, r1.tail.headD 0] m1)) rfl (fun _ _ => rfl)
    (by
      have h := installSimStub (p := p) (n := n) (checkSumCtors_pending dn vis fe
        (rdW (m.arr64 EREC) (UInt64.ofNat cvp)) lo ll (UInt64.ofNat bs.nP) (UInt64.ofNat msh.nIdx)
        (rdW (m.arr64 IW) (pp + 6)) (rdW (m.arr64 IW) (pp + 8)) (rdW (m.arr64 IW) (pp + 7)) cv co cl
        hn32 hrs32 bs.lps cvv msh.ctors) ⟨hS, hlps, hlb, hcv, hcd, hcb⟩
      rw [hnm, hrse, h8, h7, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib] at h
      exact h) ?_
  rintro r1 ⟨cs, ss⟩ m1 a1 ⟨hS1, hg1, hcs1, hss1⟩ r' m' e
  cases h2 : callW p n "rec2" [r1.headD 0, r1.tail.headD 0] m1 with
  | none => rw [h2] at e; cases e
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, icboK2_some] at e
  obtain ⟨hS2, hg2, hd2⟩ := installRec2PSl hP decCN_mono h2 hS1 hcs1
  cases h3 : callW p n "rec2" [r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0] m2 with
  | none => rw [h3] at e; cases e
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3, icboK3_some] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨hS3, hg3, hd3⟩ := installRec2PSl hP decIS_mono h3 hS2 (hss1.grow decIS_mono hg2)
  exact ⟨hS3, (hg1.trans hg2).trans hg3, hd2.grow (decCNS_mono _) hg3, hd3⟩

/-- **`check_block_ctors_go`'s model refines `checkBlockCtors`.** -/
theorem icbgW_sim {p : Prog} (hP : CtorsProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (pp lo ll : Word) (bs : BlockShape) (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml co cl : Word) (mss : List MemberShape) (cvs : List IConstantVal),
    StageR dn vis fe m a → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    decHL m lo.toNat ll.toNat = some bs.lps → lo.toNat + ll.toNat ≤ iwTop m →
    PSlR decMS mss mo ml m → PSlR decCVp cvs co cl m →
    Sim (icbgW p n m vis vis pp lo ll mo ml co cl) (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        PSlR decCNS x.1 (r.headD 0) (r.tail.headD 0) m' ∧
        PSlR decISS x.2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m') := by
  induction n with
  | zero => intro m a mo ml co cl mss cvs _ _ _ _ _ _ _; rw [icbgW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a mo ml co cl mss cvs hS hq hsrc hlps hlb hmss hcvs
  by_cases hml : ml = 0
  · rw [icbgW_nil1 p n m vis vis pp lo ll mo ml co cl hml]
    have : mss = [] := by
      have h := hmss.1; simp only [DecB, hml] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hS, IWGrow.refl m, PSlR.nil decCNS m, PSlR.nil decISS m⟩
  by_cases hcl : cl = 0
  · rw [icbgW_nil2 p n m vis vis pp lo ll mo ml co cl hml hcl]
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hcl] at h
      simpa [decPL] using h.symm
    subst this
    have : ConRon.Arena.checkBlockCtors V fe fe bs mss [] = pure ([], []) := by
      cases mss <;> simp [ConRon.Arena.checkBlockCtors]
    rw [this]
    exact Sim.ret ⟨hS, IWGrow.refl m, PSlR.nil decCNS m, PSlR.nil decISS m⟩
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨c, cvv, cvs', rfl, hwc, hcb, hdc, hcvs'⟩ := partsPSl_cons hcvs hcl
  rw [icbgW_cons p n m vis vis pp lo ll mo ml co cl hml hcl, hw, hwc]
  simp only [ConRon.Arena.checkBlockCtors]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  refine Sim.bindK (K := icbgK1 p n vis vis pp lo ll mo ml co cl) (body := fun r1 m1 => icbgK2 p n r1
      (icbgW p n m1 vis vis pp lo ll (mo + 1) (ml - 1) (co + 1) (cl - 1))) (by simp [icbgK1])
      (fun r m₁ => icbgK1_some p n m₁ vis vis pp lo ll mo ml co cl r)
    (Sim.callW_pos (Q := fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decCNS m (r.headD 0).toNat) m' x.1 ∧
        DecB (fun m => decISS m (r.tail.headD 0).toNat) m' x.2) (fun k r m' e => by
      obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (icbo_spec p hP.one k _ vis vis pp lo ll (UInt64.ofNat q) (UInt64.ofNat c)) e
      exact icboW_sim hP k hS hq hsrc hlps hlb (by rw [hq']; exact hdm) (by rw [hc']; exact hdc) r s'.mem hW) n) ?_
  rintro r1 ⟨cs, ss⟩ m1 a1 ⟨hS1, hg1, hd1, he1⟩
  dsimp only
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  refine Sim.bindK (K := icbgK2 p n r1) (body := fun r2 m2 => icbgK3 p n r1 r2 (callW p n "sl_cons"
      [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2)) rfl (fun _ _ => rfl)
    (ih m1 a1 (mo + 1) (ml - 1) (co + 1) (cl - 1) rest cvs' hS1 (hq.grow (decBS_mono _) hg1)
      (partsHsrc_grow hg1 hq9 hsrc) (by rw [decHL_grow3 hg1 hlb]; exact hlps) (Nat.le_trans hlb hg1.1)
      (hrest.grow decMS_mono hg1) (hcvs'.grow (fun q => OMono.decCVp q) hg1)) ?_
  rintro r2 ⟨rc, rs⟩ m2 a2 ⟨hS2, hg2, hc2, hs2⟩
  dsimp only
  refine Sim.mstep (K := icbgK3 p n r1 r2) rfl (fun _ _ => rfl) fun r3 m3 h3 => ?_
  obtain ⟨hS3, hg3, hd3⟩ := installConsRun hP.toCstProg decCNS_mono h3 hS2 hc2 (hd1.grow (decCNS_mono _) hg2)
  refine Sim.mstep (K := icbgK4 r3) rfl (fun _ _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨hS4, hg4, hd4⟩ := installConsRun hP.toCstProg decISS_mono h4 hS3 (hs2.grow decISS_mono hg3)
    (he1.grow (decISS_mono _) (hg2.trans hg3))
  exact Sim.ret ⟨hS4, ((hg1.trans hg2).trans hg3).trans hg4, by simpa using hd3.grow decCNS_mono hg4,
    by simpa using hd4⟩

/-- **`check_block_ctors` refines `checkBlockCtors`** (at one environment, `vis0 = vis`, as
`check_block_pass` calls it; through `check_sum_ctors`' pending contract): the shape, member and
former slices decoded below the tops; the stored constructors and their fields' sorts, per member,
two slices of `[off, len]` pointers decoded below the tops (`sl_cons`-built, D18). -/
@[refines ConRon.Arena.checkBlockCtors]
theorem checkBlockCtors_refines (p : Prog) (hP : CtorsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (pp mo ml co cl : Word)
    (bs : BlockShape) (mss : List MemberShape) (cvs : List IConstantVal)
    (hS : StageR dn vis fe s₀.mem a₀) (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem pp) (hmss : PSlR decMS mss mo ml s₀.mem) (hcvs : PSlR decCVp cvs co cl s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_ctors" [vis, vis, pp, mo, ml, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PSlR decCNS (AM.res (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀).1 (r.headD 0)
        (r.tail.headD 0) s'.mem ∧
      PSlR decISS (AM.res (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀).2 (r.tail.tail.headD 0)
        (r.tail.tail.tail.headD 0) s'.mem; ⊤⦄ := by
  refine triple_post (ict_spec p hP.ctors n s₀ vis vis pp mo ml co cl) ?_
  rintro r s' ⟨hl, hm⟩
  have hsim : Sim (ictW p n s₀.mem vis vis pp mo ml co cl) (ConRon.Arena.checkBlockCtors V fe fe bs mss cvs) a₀
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow s₀.mem m' ∧
        PSlR decCNS x.1 (r.headD 0) (r.tail.headD 0) m' ∧
        PSlR decISS x.2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) m') := by
    unfold ictW
    refine Sim.mstep (K := ictK1 p n vis vis pp mo ml co cl) rfl (fun _ _ => rfl) fun r1 m1 h1 => ?_
    obtain ⟨s1, rfl, -, hW1, -⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (blockShapeLps_spec2 p hP.alloc hP.erCopy hP.erToIw hP.lps n _ pp) h1
    obtain ⟨hS1, hg1, hd1, hb1⟩ := lpsW_ok' hW1 hS hq
    obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
    refine Sim.post (K := ictK2) rfl (fun _ _ => rfl) (fun r2 m2 e => icbgW_sim hP dn vis fe pp _ _ bs n s1.mem a₀
      mo ml co cl mss cvs hS1 (hq.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hd1 hb1
      (hmss.grow decMS_mono hg1) (hcvs.grow (fun q => OMono.decCVp q) hg1) r2 m2 (by
        obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
          (icbg_spec p hP.go n _ vis vis pp (r1.headD 0) (r1.tail.headD 0) mo ml co cl) e
        exact hW2)) ?_
    rintro r2 x m2 a2 ⟨h1, h2, h3, h4⟩
    exact ⟨h1, hg1.trans h2, h3, h4⟩
  obtain ⟨hok, hQ⟩ := Sim.run hsim hm
  exact ⟨hl, hok, hQ⟩

end L.Ind
