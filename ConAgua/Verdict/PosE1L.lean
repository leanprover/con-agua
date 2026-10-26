import ConAgua.Verdict.PosE1N

/-!
# `nest_pos_fvar`, `nest_cont_checks`: error claims (lane `verdicts-b`, helper `ia2`, fork `kn1`)

`pfvE_claim`: the twin's `pfK` (the `.fvar` arm of `nestPos`) fails, whatever its continuation
(`pfW_ok`'s proof on the error model). `nccE_claim`: `nestCont`'s checks (`nccT`, the rest of the
twin `REST`) fail (`p2ccW_okW`'s proof on the error model).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind
open L.Arena

/-- **`nest_pos_fvar`'s error claim**: the twin's `pfK` fails, whatever its continuation (the
hypotheses of `pfW_ok`). -/
theorem pfvE_claim {p : Prog} (L : PfLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m : Mem} {a : AState} {ctx po pl kb hi i aO aL : Word} {c : NestCtx}
    {prog : List NestHole} {args : List EIdx} {e : Err}
    (h : pfvE p k m vis ctx po pl kb hi i aO aL = .error e) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hpr : HSl m po.toNat pl.toNat prog)
    (hargs : decHL m aO.toNat aL.toNat = some args) (hab : aO.toNat + aL.toNat ≤ iwTop m) (hP : PosMR m) :
    ∀ {β : Type} (K : NestFieldKind → AM β), ErrClaim (pfK fe c prog kb.toNat hi.toNat i.toNat args K) a e := by
  intro β K
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  cases k with
  | zero => rw [pfvE.eq_1] at h; cases h; exact absurd rfl hk0
  | succ k =>
  rw [pfvE.arm1] at h
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  cases h1 : callE p k "nest_hole_at" [ctx, po, pl, i] m with
  | error e1 =>
    rw [h1, pfvE.k_nest_hole_at.eq_1] at h; cases h
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hha⟩ := triple_of_callW (nestHoleAt_spec' p L k ⟨m, Locals.init []⟩ ctx po pl i)
    (callW_of_callE h1)
  dsimp only at hha
  rw [hs1] at hha
  rw [h1] at h
  cases k with
  | zero => simp [haWf] at hha
  | succ k =>
  obtain ⟨hS1, hg1, hon⟩ := haW_ok k dn fe vis a m m1 ctx po pl i r1 c prog (by simpa [haWf] using hha) hS hU.dec
    hU.inn hpr
  unfold pfK
  cases hnh : ConRon.Arena.nestHoleAt c prog i.toNat with
  | none =>
    rw [hnh] at hon; simp only [decONH] at hon
    rw [pfvE.k_nest_hole_at.abort1 _ _ _ _ _ _ _ _ _ _ _ hon] at h; cases h
    exact ErrClaim.fail _ _ (by decide)
  | some hl =>
  rw [hnh] at hon
  obtain ⟨hon1, hdec, hnin⟩ := hon
  rw [pfvE.k_nest_hole_at.arm1 _ _ _ _ _ _ _ _ _ _ _ (by rw [hon1]; decide)] at h
  dsimp only
  have hU1 := hU.grow hg1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨hn1, -, -, -, hnP1, -⟩ := ctx_fields hU1.dec hU1.inn htop1
  have hne1 := ctx_names_end hU1.dec hU1.inn hU1.sl htop1
  cases h2 : callE p (k + 1) "nest_occ_any" [rdW (m1.arr64 IW) ctx, rdW (m1.arr64 IW) (ctx + 1),
      rdW (m1.arr64 IW) (ctx + 4), hi, aO, aL] m1 with
  | error e2 =>
    rw [h2, pfvE.k_nest_occ_any.eq_1] at h; cases h
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hoa⟩ := triple_of_callW (nestOccAny_spec p L.no L.hoa (k + 1) ⟨m1, Locals.init []⟩ _ _ _ _ _ _)
    (callW_of_callE h2)
  dsimp only at hoa
  rw [hs2] at hoa
  rw [h2] at h
  obtain ⟨b, hrunoa, hS2, hg2, hr2, hP2⟩ := noaW_ok dn fe vis _ _ _ _ c.names (k + 1) m1 m2 a aO aL args _ hoa hS1
    hn1 hne1 (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hargs)
    (fun j hj => by have := hg1.1; omega) (hP.fr (haW_mfr (by simpa [haWf] using hha)))
  rw [hnP1] at hrunoa
  simp only [List.headD_cons] at hr2
  refine ErrClaim.bind_right hrunoa ?_
  cases b with
  | true =>
    rw [pfvE.k_nest_occ_any.abort1 _ _ _ _ _ _ _ _ _ _ (by rw [hr2]; decide)] at h; cases h
    exact ErrClaim.ite_pos rfl (ErrClaim.fail _ _ (by decide))
  | false =>
  rw [pfvE.k_nest_occ_any.arm1 _ _ _ _ _ _ _ _ _ _ (by rw [hr2]; rfl)] at h
  refine ErrClaim.ite_neg (by simp) ?_
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hd2, hnin2⟩ := hnin.grow hg2
  rw [← hd2] at hdec
  obtain ⟨hcH, hcd, hdl⟩ := nh_key_words hdec hnin2 htop2
  cases h3 : callE p (k + 1) "nest_arity" [vis, rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0))] m2 with
  | error e3 =>
    rw [h3, pfvE.k_nest_arity.eq_1] at h; cases h
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hna⟩ := triple_of_callW (nestArity_spec' p L.na (k + 1) ⟨m2, Locals.init []⟩ _ _)
    (callW_of_callE h3)
  dsimp only at hna
  rw [hs3] at hna
  rw [h3] at h
  obtain ⟨ar, a3, hrun3, hS3, hg3, hr3⟩ := naW_ok dn fe vis _ hcH k m2 m3 a r3 (by simpa [naWf] using hna) hS2
  rw [hcd] at hrun3
  refine ErrClaim.bind_right hrun3 ?_
  have hal := decHL_length m hargs
  by_cases hov : aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3) < aL
  · rw [pfvE.k_nest_arity.abort1 _ _ _ _ _ _ _ _ _ hov] at h; cases h; exact absurd rfl hk0
  have hsum : (aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat =
      aL.toNat + hl.key.ds.length := by
    rw [← hdl]
    rcases Nat.lt_or_ge (aL.toNat + (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat) (2 ^ 64)
      with hl' | hl'
    · exact word_add_toNat hl'
    · exfalso; apply hov; apply UInt64.lt_iff_toNat_lt.mpr; rw [UInt64.toNat_add]
      have := aL.toNat_lt; have := (rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3)).toNat_lt; omega
  by_cases hne : aL + rdW (m2.arr64 IW) (rdW (m2.arr64 IW) (r1.tail.headD 0) + 3) ≠ r3.headD 0
  · rw [pfvE.k_nest_arity.abort2 _ _ _ _ _ _ _ _ _ hov hne] at h; cases h
    refine ErrClaim.ite_neg ?_ (ErrClaim.fail _ _ (by decide))
    intro hq
    apply hne
    apply UInt64.toNat_inj.mp
    rw [hsum, hr3, ← hal]; simpa using hq
  · rw [pfvE.k_nest_arity.arm1 _ _ _ _ _ _ _ _ _ hov (by simpa using hne)] at h
    cases h4 : callE p (k + 1) "nest_pos_hole_kind" [ctx, kb, i] m3 with
    | error e4 =>
      rw [h4, pfvE.k_nest_pos_hole_kind.eq_1] at h; cases h
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, pfvE.k_nest_pos_hole_kind.arm1] at h; cases h

/-- `nestCont`'s checks between the container and the instantiation's former (`nest_cont_checks`),
the rest of the twin `REST`. -/
def nccT {β : Type} (c : NestCtx) (hp : Nat) (n : NIdx) (ds idx : List EIdx) (REST : AM β) : AM β := do
  if ← idx.anyM (fun x => ConRon.Arena.nestOcc c.names c.nP hp x) then fail nestNonValid
  else do
    let q ← pinQuot
    if n == q then fail nestNonValid
    else do
      let pc ← ds.allM (pcF hp)
      if !pc then
        fail (.invalid "nested positivity: nested inductive datatypes parameters cannot contain local variables")
      else REST

/-- **`nest_cont_checks`' error claim** (the hypotheses of `p2ccW_okW`). -/
theorem nccE_claim {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m : Mem} {a : AState} {ctx hp nn dO dL iO iL : Word}
    {c : NestCtx} {ds idx : List EIdx} {e : Err}
    (h : nccE p k m ctx hp nn dO dL iO iL = .error e) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hds : decHL m dO.toNat dL.toNat = some ds)
    (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop m) (hidx : decHL m iO.toNat iL.toNat = some idx)
    (hidxb : ∀ j < iL.toNat, iO.toNat + j < iwTop m) (hnH : H nn) (hP : PosMR m) :
    ∀ {β : Type} (REST : AM β), ErrClaim (nccT c hp.toNat (decI nn) ds idx REST) a e := by
  intro β REST
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  cases k with
  | zero => rw [nccE.eq_1] at h; cases h; exact absurd rfl hk0
  | succ k =>
  rw [nccE.arm1] at h
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, -, -, -, hnP, -⟩ := ctx_fields hU.dec hU.inn htop
  have hne := ctx_names_end hU.dec hU.inn hU.sl htop
  cases h1 : callE p k "nest_occ_any" [rdW (m.arr64 IW) ctx, rdW (m.arr64 IW) (ctx + 1),
      rdW (m.arr64 IW) (ctx + 4), hp, iO, iL] m with
  | error e1 =>
    rw [h1, nccE.k_nest_occ_any.eq_1] at h; cases h
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hoa⟩ := triple_of_callW (nestOccAny_spec p L.nit.no L.nit.hoa k ⟨m, Locals.init []⟩ _ _ _ _ _ _)
    (callW_of_callE h1)
  dsimp only at hoa
  rw [hs1] at hoa
  rw [h1] at h
  obtain ⟨b, hrunoa, hS1, hg1, hr1, hP1⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m m1 a iO iL idx _ hoa hS
    hn hne hidx hidxb hP
  simp only [List.headD_cons] at hr1
  rw [hnP] at hrunoa
  unfold nccT
  refine ErrClaim.bind_right hrunoa ?_
  cases b with
  | true =>
    rw [nccE.k_nest_occ_any.abort1 _ _ _ _ _ _ _ _ (by rw [hr1]; decide)] at h; cases h
    exact ErrClaim.ite_pos rfl (ErrClaim.fail _ _ (by decide))
  | false =>
  rw [nccE.k_nest_occ_any.arm1 _ _ _ _ _ _ _ _ (by rw [hr1]; rfl)] at h
  refine ErrClaim.ite_neg (by simp) ?_
  cases h2 : callE p k "pin_at" [47] m1 with
  | error e2 =>
    rw [h2, nccE.k_pin_at.eq_1] at h; cases h
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨rq, m2⟩ := q2
  obtain ⟨s2, hs2, -, hq⟩ := triple_of_callW (pos2Pin_spec p L.hpa k ⟨m1, Locals.init []⟩ 47) (callW_of_callE h2)
  dsimp only at hq
  rw [hs2] at hq
  rw [h2] at h
  obtain ⟨hm2, hqH, hqrun⟩ := pos2PinW_ok hq hS1.1.pins
  rw [hm2] at h
  have hpq : pinQuot = pinAt 47 := rfl
  refine ErrClaim.bind_right (v := decI (rq.headD 0)) (a₁ := a) (by rw [hpq]; simpa using hqrun) ?_
  by_cases hnq : nn = rq.headD 0
  · rw [nccE.k_pin_at.abort1 _ _ _ _ _ _ _ _ hnq] at h; cases h
    exact ErrClaim.ite_pos (by rw [hnq]; simp) (ErrClaim.fail _ _ (by decide))
  rw [nccE.k_pin_at.arm1 _ _ _ _ _ _ _ _ hnq] at h
  refine ErrClaim.ite_neg (by rw [decI_beq' _ _ hnH hqH]; simpa using hnq) ?_
  cases h3 : callE p k "nest_cont_params_closed" [hp, dO, dL] m1 with
  | error e3 =>
    rw [h3, nccE.k_nest_cont_params_closed.eq_1] at h; cases h
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hcp⟩ := triple_of_callW
    (nestContParamsClosed_spec p L.usl.hbp L.dc.hf L.hpc k ⟨m1, Locals.init []⟩ _ _ _) (callW_of_callE h3)
  dsimp only at hcp
  rw [hs3] at hcp
  rw [h3] at h
  obtain ⟨b3, a3, hrun3, -, -, hr3⟩ := cpW_okW dn fe vis hp k m1 m3 a dO dL ds _ hcp hS1
    (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => hdsb j hj)]; exact hds)
    (fun j hj => by have := hdsb j hj; have := hg1.1; omega)
  simp only [List.headD_cons] at hr3
  refine ErrClaim.bind_right hrun3 ?_
  cases b3 with
  | false =>
    rw [nccE.k_nest_cont_params_closed.abort1 _ _ _ (by rw [hr3]; rfl)] at h; cases h
    exact ErrClaim.ite_pos rfl (ErrClaim.fail _ _ (by decide))
  | true =>
    rw [nccE.k_nest_cont_params_closed.arm1 _ _ _ (by rw [hr3]; decide)] at h; cases h

end L.Ind
