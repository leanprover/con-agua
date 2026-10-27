import ConAgua.Arena.DeclNatTy
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The structural-`Nat` gate: the recurrence equations (lane `decls3`, helper `decls3-nat`)

`nat_ap1`, `nat_ap2`, the equation lists and `nat_op_equations`. A `List (EIdx × EIdx)` is an `IW`
slice of pointers to two-word records `[lhs, rhs]` (`EqL`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The two-word record at `p` holds `a`, `b`, below the pool's top. -/
def RecAt (m : Mem) (p a b : Word) : Prop :=
  p.toNat + 2 ≤ iwTop m ∧ (iwA m)[p.toNat]? = some a ∧ (iwA m)[p.toNat + 1]? = some b

theorem RecAt.grow {m m' : Mem} {p a b : Word} (h : RecAt m p a b) (hg : IWGrow m m') :
    RecAt m' p a b := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, ?_, ?_⟩
  · simp only [iwA] at h2 ⊢; rw [hg.2.2.1 _ (by omega)]; exact h2
  · simp only [iwA] at h3 ⊢; rw [hg.2.2.1 _ (by omega)]; exact h3

/-- `List (EIdx × EIdx)` as the slice `(o, l)` of pointers to equation records. -/
def EqL (m : Mem) (o l : Nat) (ps : List (EIdx × EIdx)) : Prop :=
  o + l ≤ iwTop m ∧ l = ps.length ∧ ∀ (j : Nat) (hj : j < ps.length), ∃ p a b : Word,
    (iwA m)[o + j]? = some p ∧ RecAt m p a b ∧ a.toNat < 2 ^ 32 ∧ b.toNat < 2 ^ 32 ∧
      ps[j] = (decE a, decE b)

theorem EqL.grow {m m' : Mem} {o l : Nat} {ps : List (EIdx × EIdx)} (h : EqL m o l ps)
    (hg : IWGrow m m') : EqL m' o l ps := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, h2, fun j hj => ?_⟩
  obtain ⟨p, a, b, hp, hr, ha, hb, he⟩ := h3 j hj
  refine ⟨p, a, b, ?_, hr.grow hg, ha, hb, he⟩
  simp only [iwA] at hp ⊢; rw [hg.2.2.1 _ (by omega)]; exact hp

/-- The post of a function returning an equation list `(o, l)`. -/
def decEqRL (m : Mem) (r : List Word) (ps : List (EIdx × EIdx)) : Prop :=
  EqL m (r.getD 0 0).toNat (r.getD 1 0).toNat ps

section eq
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatEqProg (p : Prog) : Prop extends NatTyProg p where
  lNatAp1 : p.lookup "nat_ap1" = some natAp1L
  lNatAp2 : p.lookup "nat_ap2" = some natAp2L
  lNatEqList2 : p.lookup "nat_eq_list2" = some natEqList2
  lNatEqList3 : p.lookup "nat_eq_list3" = some natEqList3
  lNatEqList4 : p.lookup "nat_eq_list4" = some natEqList4
  lNatEqPr : p.lookup "nat_eq_pr" = some natEqPr
  lNatEqUn : p.lookup "nat_eq_un" = some natEqUn
  lNatEqMu : p.lookup "nat_eq_mu" = some natEqMu
  lNatEqPo : p.lookup "nat_eq_po" = some natEqPo
  lNatEqBe : p.lookup "nat_eq_be" = some natEqBe
  lNatEqBl : p.lookup "nat_eq_bl" = some natEqBl
  lNatCertify : p.lookup "certify_nat_eqs" = some certifyNatEqsL
  lNatOpEquations : p.lookup "nat_op_equations" = some natOpEquationsL

/-! ### `nat_ap1`, `nat_ap2` -/

/-- **`nat_ap1` is its model `natAp1W`** (generated). -/
l_model natAp1_specW (p : Prog) (hp : p.lookup "nat_ap1" = some natAp1L)
  fns [hp ↦ natAp1W list]
  specs [callW_spec p n "const_e", callW_spec p n "mk_app"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natAp1_ref (hN : NatEqProg p) (nm a : Word) :
    CallRef p "nat_ap1" [nm, a] (fun m s => StageR dn vis fe m s ∧ H nm ∧ H a)
      (natAp1 (decI nm) (decE a)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mm => natAp1W p (k + 1) mm nm a) (fun k s₀ => natAp1_specW p hN.lNatAp1 (k + 1) s₀ nm a)
    fun k m s ⟨hS, hn, ha⟩ => ?_
  rw [natAp1W.arm1]
  refine Sim.ntB ((constE_ref hN.toMasterProg nm).sim ⟨hS, hn⟩) fun r1 _ m1 a1 ⟨hS1, hg1, _, e1⟩ => ?_
  subst e1
  exact Sim.ntRet ((mkApp_ref hN.toMasterProg (r1.headD 0) a).sim hS1)
    fun _ _ _ _ _ ⟨hS2, hg2, hl, hx⟩ => ⟨hS2, hg1.trans hg2, hl, hx⟩

/-- **`nat_ap2` is its model `natAp2W`** (generated). -/
l_model natAp2_specW (p : Prog) (hp : p.lookup "nat_ap2" = some natAp2L)
  fns [hp ↦ natAp2W list]
  specs [callW_spec p n "nat_ap1", callW_spec p n "mk_app"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natAp2_ref (hN : NatEqProg p) (nm a b : Word) :
    CallRef p "nat_ap2" [nm, a, b] (fun m s => StageR dn vis fe m s ∧ H nm ∧ H a ∧ H b)
      (natAp2 (decI nm) (decE a) (decE b)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mm => natAp2W p (k + 1) mm nm a b) (fun k s₀ => natAp2_specW p hN.lNatAp2 (k + 1) s₀ nm a b)
    fun k m s ⟨hS, hn, ha, hb⟩ => ?_
  rw [natAp2W.arm1]
  refine Sim.ntB ((natAp1_ref hN nm a).sim ⟨hS, hn, ha⟩) fun r1 _ m1 a1 ⟨hS1, hg1, _, e1⟩ => ?_
  subst e1
  exact Sim.ntRet ((mkApp_ref hN.toMasterProg (r1.headD 0) b).sim hS1)
    fun _ _ _ _ _ ⟨hS2, hg2, hl, hx⟩ => ⟨hS2, hg1.trans hg2, hl, hx⟩

@[refines ConRon.Arena.natAp1]
theorem natAp1_refines (hN : NatEqProg p) (nm a : Word) :
    RefAM p "nat_ap1" [nm, a] (fun m s => StageR dn vis fe m s ∧ H nm ∧ H a)
      (natAp1 (decI nm) (decE a)) (KeepPost dn vis fe decW0E) :=
  (natAp1_ref hN nm a).refAM

@[refines ConRon.Arena.natAp2]
theorem natAp2_refines (hN : NatEqProg p) (nm a b : Word) :
    RefAM p "nat_ap2" [nm, a, b] (fun m s => StageR dn vis fe m s ∧ H nm ∧ H a ∧ H b)
      (natAp2 (decI nm) (decE a) (decE b)) (KeepPost dn vis fe decW0E) :=
  (natAp2_ref hN nm a b).refAM

/-- A twin-free callee (`FRef`) as a model-only `Sim` step. -/
theorem FRef.simB {α γ : Type} {f : FnName} {args : List Word} {pre : Mem → Prop}
    {post : Mem → Mem → List Word → Prop} (h : FRef p f args pre post) {n : Nat} {m : Mem} (hp : pre m)
    {body : List Word → Mem → Option (γ × Mem)} {op : AM α} {a : AState} {R : γ → α → Mem → AState → Prop}
    (h2 : ∀ r m1, post m m1 r → Sim (body r m1) op a R) : Sim (ntBW (callW p n f args m) body) op a R := by
  intro r m' e
  cases hc : callW p n f args m with
  | none => rw [hc] at e; cases e
  | some q => obtain ⟨r1, m1⟩ := q; rw [hc, bW_some] at e; exact h2 r1 m1 (h n m r1 m1 hp hc) r m' e

/-- A callee whose twin is `pure v`, as a model-only `Sim` step. -/
theorem CallRef.simP {α β γ : Type} {f : FnName} {args : List Word} {pre : Mem → AState → Prop} {v : β}
    {post : Mem → Mem → AState → List Word → β → Prop} (h : CallRef p f args pre (pure v) post) {n : Nat}
    {m : Mem} {a : AState} (hp : pre m a) {body : List Word → Mem → Option (γ × Mem)} {op : AM α}
    {R : γ → α → Mem → AState → Prop} (h2 : ∀ r m1, post m m1 a r v → Sim (body r m1) op a R) :
    Sim (ntBW (callW p n f args m) body) op a R := by
  intro r m' e
  cases hc : callW p n f args m with
  | none => rw [hc] at e; cases e
  | some q =>
    obtain ⟨r1, m1⟩ := q; rw [hc, bW_some] at e
    obtain ⟨x, a', hr, hq⟩ := h n m a r1 m1 hp hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hr)
    exact h2 r1 m1 hq r m' e

theorem recAt_of_post {m m1 : Mem} {r : List Word} {a b : Word} (h : RecPost m m1 r [a, b])
    (_hI : IWOK m) : RecAt m1 (r.headD 0) a b := by
  obtain ⟨hq, hK, hroom, htop, hget⟩ := h
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  refine ⟨by rw [hq']; simp at htop; omega, ?_, ?_⟩
  · have := hget 0 (by simp); simp only [iwA, hq']; simpa using this
  · have := hget 1 (by simp); simp only [iwA, hq']; simpa using this

/-- The words `ws` point at two-word records holding the pairs `ps`. -/
def RecsAt (m : Mem) (ws : List Word) (ps : List (EIdx × EIdx)) : Prop :=
  ps.length = ws.length ∧ ∀ (j : Nat) (hj : j < ws.length), ∃ x y : Word, RecAt m ws[j] x y ∧ H x ∧ H y ∧
    ps[j]? = some (decE x, decE y)

theorem RecsAt.nil (m : Mem) : RecsAt m [] [] := ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

theorem RecsAt.snoc {m m1 : Mem} {ws : List Word} {ps : List (EIdx × EIdx)} {w a b : Word}
    (hR : RecsAt m ws ps) (hg : IWGrow m m1) (hr : RecAt m1 w a b) (ha : H a) (hb : H b) :
    RecsAt m1 (ws ++ [w]) (ps ++ [(decE a, decE b)]) := by
  refine ⟨by simp [hR.1], fun j hj => ?_⟩
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hj' : j < ws.length
  · obtain ⟨x, y, hxy, hx, hy, hp⟩ := hR.2 j hj'
    refine ⟨x, y, ?_, hx, hy, ?_⟩
    · rw [List.getElem_append_left hj']; exact hxy.grow hg
    · rw [List.getElem?_append_left (by have := hR.1; omega)]; exact hp
  · obtain rfl : j = ws.length := by omega
    exact ⟨a, b, by simpa using hr, ha, hb, by simp [hR.1]⟩

/-- **One `rec2` of an equation list**: the record joins the list. -/
theorem recs_step (hN : NatEqProg p) {n : Nat} {m m0 : Mem} {s : AState} {ws : List Word}
    {ps : List (EIdx × EIdx)} {a b : Word} {γ α : Type} {body : List Word → Mem → Option (γ × Mem)}
    {op : AM α} {R : γ → α → Mem → AState → Prop} (hS : StageR dn vis fe m s) (hG : IWGrow m0 m)
    (hR : RecsAt m ws ps) (ha : H a) (hb : H b) (h2 : ∀ r m1, StageR dn vis fe m1 s → IWGrow m0 m1 →
      RecsAt m1 (ws ++ [r.headD 0]) (ps ++ [(decE a, decE b)]) → Sim (body r m1) op s R) :
    Sim (ntBW (callW p n "rec2" [a, b] m) body) op s R :=
  (rec2_fref p hN.lIwAlloc hN.lRec2 a b).simB hS.2 fun r m1 hR1 =>
    h2 r m1 (hR1.2.1.stage hS) (hG.trans hR1.2.1.1) (hR.snoc hR1.2.1.1 (recAt_of_post hR1 hS.2) ha hb)

/-- **Emitting an equation list**: the record pointers `ws`, written into a fresh slice. -/
theorem emit_sim (hal : p.lookup "iw_alloc" = some iwAlloc) {n : Nat} {m m0 : Mem} {s : AState}
    {ws : List Word} {ps : List (EIdx × EIdx)} {N : Word} {body : List Word → Mem → Option (List Word × Mem)}
    (hS : StageR dn vis fe m s) (hG : IWGrow m0 m) (hR : RecsAt m ws ps) (hN : N.toNat = ws.length)
    (hb : ∀ rq mq, body rq mq = some ([rq.headD 0, N], wrIW mq (rq.headD 0) ws)) :
    Sim (ntBW (callW p n "iw_alloc" [N] m) body) (pure ps) s
      (fun r x m' a' => KeepPost dn vis fe decEqRL m0 m' a' r x) :=
  (iwAlloc_fref p hal N).simB hS.2 fun rq mq ⟨hq0, hmq, _, hroom, _⟩ => by
    rw [hb]; refine Sim.ret ?_
    obtain ⟨hqq, hKp, hroom', htop', hget⟩ := recPost_wr m ws N hN hS.2 (by simpa [iwTop, hN] using hroom)
    subst hmq; rw [hq0]
    have hq' : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
    have hl := hR.1
    refine ⟨hKp.stage hS, hG.trans hKp.1, ?_⟩
    simp only [decEqRL, EqL, List.getD_cons_zero, List.getD_cons_succ, hq', hN]
    refine ⟨by omega, hR.1.symm, fun j hj => ?_⟩
    obtain ⟨x, y, hr', hx, hy, he⟩ := hR.2 j (by omega)
    refine ⟨ws[j]'(by omega), x, y, ?_, hr'.grow hKp.1, hx, hy, (List.getElem?_eq_some_iff.mp he).2⟩
    simp only [iwA]
    rw [hget j (by omega)]
    simp [List.getElem?_eq_getElem (show j < ws.length by omega)]

/-- **`nat_eq_list2` is its model `natEqList2W`** (generated). -/
l_model natEqList2_specW (p : Prog) (hp : p.lookup "nat_eq_list2" = some natEqList2)
  fns [hp ↦ natEqList2W list]
  specs [callW_spec p n "rec2", callW_spec p n "iw_alloc"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqList2_ref (hN : NatEqProg p) (a1 b1 a2 b2 : Word) :
    CallRef p "nat_eq_list2" [a1, b1, a2, b2] (fun m s => StageR dn vis fe m s ∧ H a1 ∧ H b1 ∧ H a2 ∧ H b2)
      (pure [(decE a1, decE b1), (decE a2, decE b2)] : AM (List (EIdx × EIdx))) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqList2W p (k + 1) mm a1 b1 a2 b2)
    (fun k s₀ => natEqList2_specW p hN.lNatEqList2 (k + 1) s₀ a1 b1 a2 b2) fun k m s ⟨hS, ha1, hb1, ha2, hb2⟩ => ?_
  rw [natEqList2W.arm1]
  refine recs_step hN hS (.refl m) (.nil m) ha1 hb1 fun r1 m1 hS1 hG1 hR1 => ?_
  refine recs_step hN hS1 hG1 hR1 ha2 hb2 fun r2 m2 hS2 hG2 hR2 => ?_
  exact emit_sim hN.lIwAlloc hS2 hG2 hR2 rfl fun _ _ => by simp [wrIW]

/-- **`nat_eq_list3` is its model `natEqList3W`** (generated). -/
l_model natEqList3_specW (p : Prog) (hp : p.lookup "nat_eq_list3" = some natEqList3)
  fns [hp ↦ natEqList3W list]
  specs [callW_spec p n "rec2", callW_spec p n "iw_alloc"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqList3_ref (hN : NatEqProg p) (a1 b1 a2 b2 a3 b3 : Word) :
    CallRef p "nat_eq_list3" [a1, b1, a2, b2, a3, b3] (fun m s => StageR dn vis fe m s ∧ H a1 ∧ H b1 ∧ H a2 ∧ H b2 ∧ H a3 ∧ H b3)
      (pure [(decE a1, decE b1), (decE a2, decE b2), (decE a3, decE b3)] : AM (List (EIdx × EIdx))) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqList3W p (k + 1) mm a1 b1 a2 b2 a3 b3)
    (fun k s₀ => natEqList3_specW p hN.lNatEqList3 (k + 1) s₀ a1 b1 a2 b2 a3 b3) fun k m s ⟨hS, ha1, hb1, ha2, hb2, ha3, hb3⟩ => ?_
  rw [natEqList3W.arm1]
  refine recs_step hN hS (.refl m) (.nil m) ha1 hb1 fun r1 m1 hS1 hG1 hR1 => ?_
  refine recs_step hN hS1 hG1 hR1 ha2 hb2 fun r2 m2 hS2 hG2 hR2 => ?_
  refine recs_step hN hS2 hG2 hR2 ha3 hb3 fun r3 m3 hS3 hG3 hR3 => ?_
  exact emit_sim hN.lIwAlloc hS3 hG3 hR3 rfl fun _ _ => by simp [wrIW, UInt64.add_assoc]

/-- **`nat_eq_list4` is its model `natEqList4W`** (generated). -/
l_model natEqList4_specW (p : Prog) (hp : p.lookup "nat_eq_list4" = some natEqList4)
  fns [hp ↦ natEqList4W list]
  specs [callW_spec p n "rec2", callW_spec p n "iw_alloc"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqList4_ref (hN : NatEqProg p) (a1 b1 a2 b2 a3 b3 a4 b4 : Word) :
    CallRef p "nat_eq_list4" [a1, b1, a2, b2, a3, b3, a4, b4] (fun m s => StageR dn vis fe m s ∧ H a1 ∧ H b1 ∧ H a2 ∧ H b2 ∧ H a3 ∧ H b3 ∧ H a4 ∧ H b4)
      (pure [(decE a1, decE b1), (decE a2, decE b2), (decE a3, decE b3), (decE a4, decE b4)] : AM (List (EIdx × EIdx))) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqList4W p (k + 1) mm a1 b1 a2 b2 a3 b3 a4 b4)
    (fun k s₀ => natEqList4_specW p hN.lNatEqList4 (k + 1) s₀ a1 b1 a2 b2 a3 b3 a4 b4) fun k m s ⟨hS, ha1, hb1, ha2, hb2, ha3, hb3, ha4, hb4⟩ => ?_
  rw [natEqList4W.arm1]
  refine recs_step hN hS (.refl m) (.nil m) ha1 hb1 fun r1 m1 hS1 hG1 hR1 => ?_
  refine recs_step hN hS1 hG1 hR1 ha2 hb2 fun r2 m2 hS2 hG2 hR2 => ?_
  refine recs_step hN hS2 hG2 hR2 ha3 hb3 fun r3 m3 hS3 hG3 hR3 => ?_
  refine recs_step hN hS3 hG3 hR3 ha4 hb4 fun r4 m4 hS4 hG4 hR4 => ?_
  exact emit_sim hN.lIwAlloc hS4 hG4 hR4 rfl fun _ _ => by simp [wrIW, UInt64.add_assoc]

theorem eqL_retag {m : Mem} {rl : List Word} {xl : List (EIdx × EIdx)} {k : Nat}
    (h : decEqRL m rl xl) (hk : xl.length = k) :
    EqL m (rl.headD 0).toNat k xl := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ntGetD0, ntGetD1] at h1 h2 h3
  exact ⟨by omega, hk.symm, h3⟩

def natEqPrT (c : NIdx) (z : EIdx) (x : EIdx) (sx : EIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp1 c z
  let l2 ← natAp1 c sx
  pure [(l1, z), (l2, x)]

/-- **`nat_eq_pr` is its model `natEqPrW`** (generated). -/
l_model natEqPr_specW (p : Prog) (hp : p.lookup "nat_eq_pr" = some natEqPr)
  fns [hp ↦ natEqPrW list]
  specs [callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list2"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqPr_ref (hN : NatEqProg p) (c z x sx : Word) :
    CallRef p "nat_eq_pr" [c, z, x, sx] (fun m s => StageR dn vis fe m s ∧ H c ∧ H z ∧ H x ∧ H sx)
      (natEqPrT (decI c) (decE z) (decE x) (decE sx)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqPrW p (k + 1) mm c z x sx) (fun k s₀ => natEqPr_specW p hN.lNatEqPr (k + 1) s₀ c z x sx)
    fun k m s ⟨hS, h_c, h_z, h_x, h_sx⟩ => ?_
  rw [natEqPrW.arm1]; unfold natEqPrT
  refine Sim.ntB ((natAp1_ref hN c z).sim ⟨hS, h_c, h_z⟩)
    fun r_l1 _ m_l1 a_l1 ⟨hS_l1, hg_l1, hl_l1, rfl⟩ => ?_
  refine Sim.ntB ((natAp1_ref hN c sx).sim ⟨hS_l1, h_c, h_sx⟩)
    fun r_l2 _ m_l2 a_l2 ⟨hS_l2, hg_l2, hl_l2, rfl⟩ => ?_
  exact Sim.ntRet ((natEqList2_ref hN (r_l1.headD 0) z (r_l2.headD 0) x).sim ⟨hS_l2, hl_l1, h_z, hl_l2, h_x⟩)
    fun _ _ _ _ e ⟨hSl, hgl, hdl⟩ => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e); exact ⟨hSl, (hg_l1.trans hg_l2).trans hgl, eqL_retag hdl rfl⟩

def natEqUnT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sy : EIdx) (w : NIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c x z
  let l2 ← natAp2 c x sy
  let r3 ← natAp2 c x y
  let r2 ← natAp1 w r3
  pure [(l1, x), (l2, r2)]

/-- **`nat_eq_un` is its model `natEqUnW`** (generated). -/
l_model natEqUn_specW (p : Prog) (hp : p.lookup "nat_eq_un" = some natEqUn)
  fns [hp ↦ natEqUnW list]
  specs [callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list2"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqUn_ref (hN : NatEqProg p) (c x y z sy w : Word) :
    CallRef p "nat_eq_un" [c, x, y, z, sy, w] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sy ∧ H w)
      (natEqUnT (decI c) (decE x) (decE y) (decE z) (decE sy) (decI w)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqUnW p (k + 1) mm c x y z sy w) (fun k s₀ => natEqUn_specW p hN.lNatEqUn (k + 1) s₀ c x y z sy w)
    fun k m s ⟨hS, h_c, h_x, h_y, h_z, h_sy, h_w⟩ => ?_
  rw [natEqUnW.arm1]; unfold natEqUnT
  refine Sim.ntB ((natAp2_ref hN c x z).sim ⟨hS, h_c, h_x, h_z⟩)
    fun r_l1 _ m_l1 a_l1 ⟨hS_l1, hg_l1, hl_l1, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c x sy).sim ⟨hS_l1, h_c, h_x, h_sy⟩)
    fun r_l2 _ m_l2 a_l2 ⟨hS_l2, hg_l2, hl_l2, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c x y).sim ⟨hS_l2, h_c, h_x, h_y⟩)
    fun r_r3 _ m_r3 a_r3 ⟨hS_r3, hg_r3, hl_r3, rfl⟩ => ?_
  refine Sim.ntB ((natAp1_ref hN w (r_r3.headD 0)).sim ⟨hS_r3, h_w, hl_r3⟩)
    fun r_r2 _ m_r2 a_r2 ⟨hS_r2, hg_r2, hl_r2, rfl⟩ => ?_
  exact Sim.ntRet ((natEqList2_ref hN (r_l1.headD 0) x (r_l2.headD 0) (r_r2.headD 0)).sim ⟨hS_r2, hl_l1, h_x, hl_l2, hl_r2⟩)
    fun _ _ _ _ e ⟨hSl, hgl, hdl⟩ => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e); exact ⟨hSl, (((hg_l1.trans hg_l2).trans hg_r3).trans hg_r2).trans hgl, eqL_retag hdl rfl⟩

def natEqMuT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sy : EIdx) (ad : NIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c x z
  let l2 ← natAp2 c x sy
  let r3 ← natAp2 c x y
  let r2 ← natAp2 ad r3 x
  pure [(l1, z), (l2, r2)]

/-- **`nat_eq_mu` is its model `natEqMuW`** (generated). -/
l_model natEqMu_specW (p : Prog) (hp : p.lookup "nat_eq_mu" = some natEqMu)
  fns [hp ↦ natEqMuW list]
  specs [callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list2"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqMu_ref (hN : NatEqProg p) (c x y z sy ad : Word) :
    CallRef p "nat_eq_mu" [c, x, y, z, sy, ad] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sy ∧ H ad)
      (natEqMuT (decI c) (decE x) (decE y) (decE z) (decE sy) (decI ad)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqMuW p (k + 1) mm c x y z sy ad) (fun k s₀ => natEqMu_specW p hN.lNatEqMu (k + 1) s₀ c x y z sy ad)
    fun k m s ⟨hS, h_c, h_x, h_y, h_z, h_sy, h_ad⟩ => ?_
  rw [natEqMuW.arm1]; unfold natEqMuT
  refine Sim.ntB ((natAp2_ref hN c x z).sim ⟨hS, h_c, h_x, h_z⟩)
    fun r_l1 _ m_l1 a_l1 ⟨hS_l1, hg_l1, hl_l1, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c x sy).sim ⟨hS_l1, h_c, h_x, h_sy⟩)
    fun r_l2 _ m_l2 a_l2 ⟨hS_l2, hg_l2, hl_l2, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c x y).sim ⟨hS_l2, h_c, h_x, h_y⟩)
    fun r_r3 _ m_r3 a_r3 ⟨hS_r3, hg_r3, hl_r3, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN ad (r_r3.headD 0) x).sim ⟨hS_r3, h_ad, hl_r3, h_x⟩)
    fun r_r2 _ m_r2 a_r2 ⟨hS_r2, hg_r2, hl_r2, rfl⟩ => ?_
  exact Sim.ntRet ((natEqList2_ref hN (r_l1.headD 0) z (r_l2.headD 0) (r_r2.headD 0)).sim ⟨hS_r2, hl_l1, h_z, hl_l2, hl_r2⟩)
    fun _ _ _ _ e ⟨hSl, hgl, hdl⟩ => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e); exact ⟨hSl, (((hg_l1.trans hg_l2).trans hg_r3).trans hg_r2).trans hgl, eqL_retag hdl rfl⟩

def natEqPoT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sy : EIdx) (sN : NIdx) (mu : NIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c x z
  let sz ← natAp1 sN z
  let l2 ← natAp2 c x sy
  let r3 ← natAp2 c x y
  let r2 ← natAp2 mu r3 x
  pure [(l1, sz), (l2, r2)]

/-- **`nat_eq_po` is its model `natEqPoW`** (generated). -/
l_model natEqPo_specW (p : Prog) (hp : p.lookup "nat_eq_po" = some natEqPo)
  fns [hp ↦ natEqPoW list]
  specs [callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list2"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqPo_ref (hN : NatEqProg p) (c x y z sy sN mu : Word) :
    CallRef p "nat_eq_po" [c, x, y, z, sy, sN, mu] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sy ∧ H sN ∧ H mu)
      (natEqPoT (decI c) (decE x) (decE y) (decE z) (decE sy) (decI sN) (decI mu)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqPoW p (k + 1) mm c x y z sy sN mu) (fun k s₀ => natEqPo_specW p hN.lNatEqPo (k + 1) s₀ c x y z sy sN mu)
    fun k m s ⟨hS, h_c, h_x, h_y, h_z, h_sy, h_sN, h_mu⟩ => ?_
  rw [natEqPoW.arm1]; unfold natEqPoT
  refine Sim.ntB ((natAp2_ref hN c x z).sim ⟨hS, h_c, h_x, h_z⟩)
    fun r_l1 _ m_l1 a_l1 ⟨hS_l1, hg_l1, hl_l1, rfl⟩ => ?_
  refine Sim.ntB ((natAp1_ref hN sN z).sim ⟨hS_l1, h_sN, h_z⟩)
    fun r_sz _ m_sz a_sz ⟨hS_sz, hg_sz, hl_sz, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c x sy).sim ⟨hS_sz, h_c, h_x, h_sy⟩)
    fun r_l2 _ m_l2 a_l2 ⟨hS_l2, hg_l2, hl_l2, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c x y).sim ⟨hS_l2, h_c, h_x, h_y⟩)
    fun r_r3 _ m_r3 a_r3 ⟨hS_r3, hg_r3, hl_r3, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN mu (r_r3.headD 0) x).sim ⟨hS_r3, h_mu, hl_r3, h_x⟩)
    fun r_r2 _ m_r2 a_r2 ⟨hS_r2, hg_r2, hl_r2, rfl⟩ => ?_
  exact Sim.ntRet ((natEqList2_ref hN (r_l1.headD 0) (r_sz.headD 0) (r_l2.headD 0) (r_r2.headD 0)).sim ⟨hS_r2, hl_l1, hl_sz, hl_l2, hl_r2⟩)
    fun _ _ _ _ e ⟨hSl, hgl, hdl⟩ => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e); exact ⟨hSl, ((((hg_l1.trans hg_sz).trans hg_l2).trans hg_r3).trans hg_r2).trans hgl, eqL_retag hdl rfl⟩

def natEqBeT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sx : EIdx) (sy : EIdx) (bT : EIdx) (bF : EIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c z z
  let l2 ← natAp2 c z sy
  let l3 ← natAp2 c sx z
  let l4 ← natAp2 c sx sy
  let r4 ← natAp2 c x y
  pure [(l1, bT), (l2, bF), (l3, bF), (l4, r4)]

/-- **`nat_eq_be` is its model `natEqBeW`** (generated). -/
l_model natEqBe_specW (p : Prog) (hp : p.lookup "nat_eq_be" = some natEqBe)
  fns [hp ↦ natEqBeW list]
  specs [callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list4"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqBe_ref (hN : NatEqProg p) (c x y z sx sy bT bF : Word) :
    CallRef p "nat_eq_be" [c, x, y, z, sx, sy, bT, bF] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sx ∧ H sy ∧ H bT ∧ H bF)
      (natEqBeT (decI c) (decE x) (decE y) (decE z) (decE sx) (decE sy) (decE bT) (decE bF)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqBeW p (k + 1) mm c x y z sx sy bT bF) (fun k s₀ => natEqBe_specW p hN.lNatEqBe (k + 1) s₀ c x y z sx sy bT bF)
    fun k m s ⟨hS, h_c, h_x, h_y, h_z, h_sx, h_sy, h_bT, h_bF⟩ => ?_
  rw [natEqBeW.arm1]; unfold natEqBeT
  refine Sim.ntB ((natAp2_ref hN c z z).sim ⟨hS, h_c, h_z, h_z⟩)
    fun r_l1 _ m_l1 a_l1 ⟨hS_l1, hg_l1, hl_l1, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c z sy).sim ⟨hS_l1, h_c, h_z, h_sy⟩)
    fun r_l2 _ m_l2 a_l2 ⟨hS_l2, hg_l2, hl_l2, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c sx z).sim ⟨hS_l2, h_c, h_sx, h_z⟩)
    fun r_l3 _ m_l3 a_l3 ⟨hS_l3, hg_l3, hl_l3, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c sx sy).sim ⟨hS_l3, h_c, h_sx, h_sy⟩)
    fun r_l4 _ m_l4 a_l4 ⟨hS_l4, hg_l4, hl_l4, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c x y).sim ⟨hS_l4, h_c, h_x, h_y⟩)
    fun r_r4 _ m_r4 a_r4 ⟨hS_r4, hg_r4, hl_r4, rfl⟩ => ?_
  exact Sim.ntRet ((natEqList4_ref hN (r_l1.headD 0) bT (r_l2.headD 0) bF (r_l3.headD 0) bF (r_l4.headD 0) (r_r4.headD 0)).sim ⟨hS_r4, hl_l1, h_bT, hl_l2, h_bF, hl_l3, h_bF, hl_l4, hl_r4⟩)
    fun _ _ _ _ e ⟨hSl, hgl, hdl⟩ => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e); exact ⟨hSl, ((((hg_l1.trans hg_l2).trans hg_l3).trans hg_l4).trans hg_r4).trans hgl, eqL_retag hdl rfl⟩

def natEqBlT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sx : EIdx) (sy : EIdx) (bT : EIdx) (bF : EIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c z y
  let l2 ← natAp2 c sx z
  let l3 ← natAp2 c sx sy
  let r3 ← natAp2 c x y
  pure [(l1, bT), (l2, bF), (l3, r3)]

/-- **`nat_eq_bl` is its model `natEqBlW`** (generated). -/
l_model natEqBl_specW (p : Prog) (hp : p.lookup "nat_eq_bl" = some natEqBl)
  fns [hp ↦ natEqBlW list]
  specs [callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list3"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem natEqBl_ref (hN : NatEqProg p) (c x y z sx sy bT bF : Word) :
    CallRef p "nat_eq_bl" [c, x, y, z, sx, sy, bT, bF] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sx ∧ H sy ∧ H bT ∧ H bF)
      (natEqBlT (decI c) (decE x) (decE y) (decE z) (decE sx) (decE sy) (decE bT) (decE bF)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_sim (M := fun k mm => natEqBlW p (k + 1) mm c x y z sx sy bT bF) (fun k s₀ => natEqBl_specW p hN.lNatEqBl (k + 1) s₀ c x y z sx sy bT bF)
    fun k m s ⟨hS, h_c, h_x, h_y, h_z, h_sx, h_sy, h_bT, h_bF⟩ => ?_
  rw [natEqBlW.arm1]; unfold natEqBlT
  refine Sim.ntB ((natAp2_ref hN c z y).sim ⟨hS, h_c, h_z, h_y⟩)
    fun r_l1 _ m_l1 a_l1 ⟨hS_l1, hg_l1, hl_l1, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c sx z).sim ⟨hS_l1, h_c, h_sx, h_z⟩)
    fun r_l2 _ m_l2 a_l2 ⟨hS_l2, hg_l2, hl_l2, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c sx sy).sim ⟨hS_l2, h_c, h_sx, h_sy⟩)
    fun r_l3 _ m_l3 a_l3 ⟨hS_l3, hg_l3, hl_l3, rfl⟩ => ?_
  refine Sim.ntB ((natAp2_ref hN c x y).sim ⟨hS_l3, h_c, h_x, h_y⟩)
    fun r_r3 _ m_r3 a_r3 ⟨hS_r3, hg_r3, hl_r3, rfl⟩ => ?_
  exact Sim.ntRet ((natEqList3_ref hN (r_l1.headD 0) bT (r_l2.headD 0) bF (r_l3.headD 0) (r_r3.headD 0)).sim ⟨hS_r3, hl_l1, h_bT, hl_l2, h_bF, hl_l3, hl_r3⟩)
    fun _ _ _ _ e ⟨hSl, hgl, hdl⟩ => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e); exact ⟨hSl, (((hg_l1.trans hg_l2).trans hg_l3).trans hg_r3).trans hgl, eqL_retag hdl rfl⟩

/-! ### `certify_nat_eqs` -/

theorem EqL.cons {m : Mem} {o l : Nat} {e : EIdx × EIdx} {es : List (EIdx × EIdx)}
    (h : EqL m o l (e :: es)) :
    ∃ p a b : Word, l ≠ 0 ∧ (iwA m)[o]? = some p ∧ RecAt m p a b ∧ a.toNat < 2 ^ 32 ∧
      b.toNat < 2 ^ 32 ∧ e = (decE a, decE b) ∧ EqL m (o + 1) (l - 1) es := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨p, a, b, hp, hr, ha, hb, he⟩ := h3 0 (by simp)
  refine ⟨p, a, b, by simp at h2; omega, by simpa using hp, hr, ha, hb, by simpa using he, ?_, ?_, ?_⟩
  · simp at h2 ⊢; omega
  · simp at h2 ⊢; omega
  · intro j hj
    obtain ⟨p', a', b', hp', hr', ha', hb', he'⟩ := h3 (j + 1) (by simpa using hj)
    refine ⟨p', a', b', ?_, hr', ha', hb', by simpa using he'⟩
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using hp'

def certW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vis o l : Word) : Option (List Word × Mem) :=
  if l = 0 then some ([1], m) else
  ntBW (cl n "is_def_eq_core" [vis, 2, rdW (m.arr64 IW) (rdW (m.arr64 IW) o),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1)] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1)
  else ntBW (callW p n "certify_nat_eqs" [vis, o + 1, l - 1] m1) fun r2 m2 => some ([r2.headD 0], m2)

theorem certify_specW (p : Prog) (hp : p.lookup "certify_nat_eqs" = some certifyNatEqsL)
    (cl : CallM) (hc : CallSpec p cl) (n : Nat)
    (s₀ : St) (vis o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "certify_nat_eqs" [vis, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ certW p cl n s₀.mem vis o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certifyNatEqsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      hc n "is_def_eq_core", callW_spec p n "certify_nat_eqs"] <;>
    finish (gen := 20) [certW, ntBW]

local notation "V" => ConLeche.CheckMode.verified

end eq

end L.Ind
