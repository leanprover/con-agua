import ConAgua.Arena.IndInstallSpec6

/-!
# Refinements of `IndInstall`, part 7 (lane `indproofs2`, helper `parts`): `blockNestCtx`

The direct-recursion context: member 0's former telescope opened at the parameters
(`open_pis_at_fvars_f`, a stub), the walk's context (`BlockShape.nestCtx`), its holes
(`nest_holes`, helper `pos`'s). `nP + k` past `2^64` is a capacity abort, and so is the opened
parameters' count plus `k` (it bounds the context's `params.length + names.length`, which
`nest_root` needs).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `nest_holes`' model as a `Sim` (helper `pos`'s `nestHoles_refines`, unpacked). -/
theorem nhW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) {m : Mem}
    {a : AState} {ctx : Word} {c : NestCtx} (hS : StageR dn vis fe m a) (hc : decCtx m ctx.toNat = some c)
    (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat) (hhi : c.hiAt 0 < 2 ^ 64) :
    Sim (nhW k m vis ctx) (ConRon.Arena.nestHoles fe c) a
      (fun r x m' a' => NhOut m' r x ∧ StageR dn vis fe m' a' ∧ IWGrow m m') := by
  intro r m' hm
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, hnb, -⟩ := ctx_fields hc hin htop
  have hlen := decHL_length _ hn
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := nhGoW_ok dn fe vis ctx c k _ _ a 0 _ _ 0 0 c.names [] _ hm hS hc hin
    hsl hn hnb (by simp [decHL, hslice?]) (by simp) (by have := hlen; simp [NestCtx.hiAt] at hhi; simp; omega)
  have he : ConRon.Arena.nestHoles fe c = ConRon.Arena.nestHoles.go fe c 0 c.names [] := rfl
  rw [show (0 : Word).toNat = 0 from rfl, ← he] at hrun
  refine ⟨x, a', hrun, ?_, hS', hg⟩
  cases x with
  | none => exact hout
  | some l => obtain ⟨h1, h2, h3⟩ := hout; exact ⟨h1, h2, h3⟩

/-- After `nest_holes`. -/
def bncK3 (ctx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else some ([ctx, r.tail.headD 0, r.tail.tail.headD 0], m)

/-- After `block_shape_nest_ctx`. -/
def bncK2 (n : Nat) (vis : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bncK3 (r.headD 0) (nhW n m vis (r.headD 0))

/-- After `open_pis_at_fvars_f`. -/
def bncK1 (n : Nat) (vis p : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else if r.tail.tail.headD 0 + rdW (m.arr64 IW) (p + 1) < r.tail.tail.headD 0 then none
    else bncK2 n vis (nckW n m p (r.tail.headD 0) (r.tail.tail.headD 0))

/-- **The model of `block_nest_ctx`** (at exec fuel `n + 2`). -/
def bncW (n : Nat) (m : Mem) (vis p cvO cvL : Word) : Option (List Word × Mem) :=
  if cvL = 0 then none
  else if rdW (m.arr64 IW) (p + 4) + rdW (m.arr64 IW) (p + 1) < rdW (m.arr64 IW) (p + 4) then none
  else bncK1 n vis p (stubM "open_pis_at_fvars_f" m [rdW (m.arr64 IW) (p + 4),
    rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvO + 3), 0])

section arms
variable (n : Nat) (m : Mem) (vis p ctx : Word) (r : List Word)
theorem bncK3_none (h : r.headD 0 = 0) : bncK3 ctx (some (r, m)) = none := by
  simp only [bncK3]; exact if_pos h
theorem bncK3_some (h : ¬ r.headD 0 = 0) : bncK3 ctx (some (r, m)) =
    some ([ctx, r.tail.headD 0, r.tail.tail.headD 0], m) := by simp only [bncK3]; exact if_neg h
theorem bncK2_some : bncK2 n vis (some (r, m)) = bncK3 (r.headD 0) (nhW n m vis (r.headD 0)) := rfl
theorem bncK1_none (h : r.headD 0 = 0) : bncK1 n vis p (some (r, m)) = none := by
  simp only [bncK1]; exact if_pos h
theorem bncK1_ov (h : ¬ r.headD 0 = 0)
    (ho : r.tail.tail.headD 0 + rdW (m.arr64 IW) (p + 1) < r.tail.tail.headD 0) :
    bncK1 n vis p (some (r, m)) = none := by simp only [bncK1]; rw [if_neg h, if_pos ho]
theorem bncK1_some (h : ¬ r.headD 0 = 0)
    (ho : ¬ r.tail.tail.headD 0 + rdW (m.arr64 IW) (p + 1) < r.tail.tail.headD 0) : bncK1 n vis p (some (r, m)) =
    bncK2 n vis (nckW n m p (r.tail.headD 0) (r.tail.tail.headD 0)) := by
  simp only [bncK1]; rw [if_neg h, if_neg ho]
end arms
attribute [ind_grind] bncK3_none bncK3_some bncK2_some bncK1_none bncK1_ov bncK1_some

theorem bnc_spec (p : Prog) (hP : NckProg p) (hl : NhLook p)
    (hp : p.lookup "block_nest_ctx" = some blockNestCtx) (n : Nat) (s₀ : St) (vis q cvO cvL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 2)) "block_nest_ctx" [vis, q, cvO, cvL]
    ⦃fun r s' => LocEq s' s₀ ∧ bncW n s₀.mem vis q cvO cvL = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockNestCtx]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      stubM_spec p "open_pis_at_fvars_f" (n + 1), nck_spec p hP n, nestHoles_spec p hl n] <;>
    finish (gen := 20) [bncW, rdW_eq]

theorem partsRunOfOk {α : Type} [Inhabited α] {x : AM α} {a : AState} (h : AM.ok x a) :
    x.run a = .ok (AM.res x a, AM.st x a) := by
  unfold AM.ok at h; unfold AM.res AM.st
  cases hx : x.run a with
  | error e => rw [hx] at h; cases h
  | ok v => obtain ⟨v1, v2⟩ := v; rfl

/-- **`block_nest_ctx`'s model refines `blockNestCtx`.** -/
theorem bncW_sim {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) {m : Mem} {a : AState}
    {q cvO cvL : Word} {bs : BlockShape} {cvTas : List IConstantVal} (hS : StageR dn vis fe m a)
    (hq : DecB (fun m => decBS m q.toNat) m bs)
    (hsrc : ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → o + l ≤ iwTop m)
    (hcv : PSlR decCVp cvTas cvO cvL m) :
    Sim (bncW n m vis q cvO cvL) (ConRon.Arena.blockNestCtx fe bs cvTas) a
      (fun r x m' a' => DecB (fun m => decCtx m (r.headD 0).toNat) m' x.1 ∧
        decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some x.2 ∧
        (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m' ∧
        StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        CtxIn m' (r.headD 0).toNat (· < iwTop m') ∧ CtxSl m' (r.headD 0).toNat ∧ x.1.hiAt 0 < 2 ^ 64 ∧
        x.1.params.length + x.1.names.length < 2 ^ 64) := by
  intro r m' e
  unfold bncW at e
  split at e
  · cases e
  rename_i hl
  split at e
  · cases e
  rename_i hov
  obtain ⟨pc, cv0, cvs, rfl, hw, hpb, hcv0, -⟩ := partsPSl_cons hcv hl
  obtain ⟨htyl, htye⟩ := partsCVType hcv0 (UInt64.toNat_ofNat_of_lt' hpb)
  obtain ⟨hq', hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hkw := partsShapeK hq' hq9
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hq').1
    have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  have hhi : bs.nP + bs.k < 2 ^ 64 := by
    have := partsAddNoOv hov
    rw [hnpw, hkw, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hkb] at this
    have := (rdW (m.arr64 IW) (q + 4) + rdW (m.arr64 IW) (q + 1)).toNat_lt
    rw [hnpw, hkw] at this; omega
  rw [hw] at e
  revert r m' e
  unfold ConRon.Arena.blockNestCtx
  dsimp only
  have h1 := partsSimStub (openPisAtFvarsF_spec dn vis fe (rdW (m.arr64 IW) (q + 4))
    (rdW (m.arr64 EREC) (UInt64.ofNat pc + 3)) 0 htyl) hS
  rw [show (rdW (m.arr64 IW) (q + 4)).toNat = bs.nP from by rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb],
    show decI (rdW (m.arr64 EREC) (UInt64.ofNat pc + 3)) = cv0.type from htye,
    show (0 : Word).toNat = 0 from rfl] at h1
  refine Sim.bindK (K := bncK1 n vis q) (body := fun r1 m1 => if r1.headD 0 = 0 then none
      else if r1.tail.tail.headD 0 + rdW (m1.arr64 IW) (q + 1) < r1.tail.tail.headD 0 then none
      else bncK2 n vis (nckW n m1 q (r1.tail.headD 0) (r1.tail.tail.headD 0))) rfl (fun _ _ => rfl) h1 ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, if_true]
    exact Sim.of_none
  | some pq =>
  obtain ⟨fvs, body⟩ := pq
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  simp only [h1', show (1 : Word) ≠ 0 by decide, if_false]
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  by_cases hov2 : r1.tail.tail.headD 0 + rdW (m1.arr64 IW) (q + 1) < r1.tail.tail.headD 0
  · simp only [hov2, if_true]; exact Sim.of_none
  simp only [hov2, if_false]
  have hTm : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hk1 : rdW (m1.arr64 IW) (q + 1) = UInt64.ofNat bs.k := by
    rw [← hkw]; simp only [rdW]
    rw [show (q + 1 : Word).toNat = q.toNat + 1 by rw [UInt64.toNat_add]; simp; omega, hg1.2.2.1 _ (by omega)]
  have hpk : fvs.length + bs.k < 2 ^ 64 := by
    have := partsAddNoOv hov2
    rw [hk1, UInt64.toNat_ofNat_of_lt' hkb] at this
    have := (r1.tail.tail.headD 0 + UInt64.ofNat bs.k).toNat_lt
    rw [decHL_length _ hfd]; omega
  intro r m' e
  cases h2 : nckW n m1 q (r1.tail.headD 0) (r1.tail.tail.headD 0) with
  | none => rw [h2] at e; cases e
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, bncK2_some] at e
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hok2, hd2, hS2, hg2, hin2, hsl2⟩ := nckW_ok n ⟨m1, Locals.init []⟩ ⟨m2, Locals.init []⟩ a1 dn vis fe q
    (r1.tail.headD 0) (r1.tail.tail.headD 0) bs fvs hS1 (hq.grow (decBS_mono _) hg1)
    (partsHsrc_grow hg1 hq9 hsrc) hfd hfb r2 h2
  have hrun2 := partsRunOfOk hok2
  generalize hc : AM.res (bs.nestCtx fvs) a1 = c at hrun2 hd2
  generalize ha2 : AM.st (bs.nestCtx fvs) a1 = a2 at hrun2 hS2
  have hnc : c = ⟨bs.memberNames, bs.lps, bs.nP, bs.nIdxs, fvs, bs.resSort, c.lvls⟩ := by
    have h' := hrun2
    unfold ConRon.Arena.BlockShape.nestCtx at h'
    obtain ⟨lv, a', -, h'⟩ := partsBindOk h'
    simp [StateT.run, pure, StateT.pure, Except.pure] at h'
    rw [← h'.1]
  have hhi' : c.hiAt 0 < 2 ^ 64 := by
    rw [hnc]; simp only [NestCtx.hiAt, BlockShape.memberNames, List.length_map]
    have : bs.k = bs.members.length := rfl
    omega
  cases h3 : nhW n m2 vis (r2.headD 0) with
  | none => rw [h3] at e; simp [bncK3] at e
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at e
  obtain ⟨holes, a3, hrun3, hR3, hS3, hg3⟩ := nhW_sim n hS2 (hd2.get (decCtx_mono _)) hin2 hsl2 hhi' r3 m3 h3
  cases holes with
  | none =>
    have h0 : r3.headD 0 = 0 := hR3
    rw [bncK3_none (h := h0)] at e; cases e
  | some hs =>
  obtain ⟨h31, hd3, hb3⟩ := hR3
  rw [bncK3_some (h := by rw [h31]; decide)] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨(c, hs), a3, ?_, ?_, hd3, hb3, hS3, (hg1.trans hg2).trans hg3, (CtxIn.grow hin2 hg3).2,
    hsl2.grow hin2 hg3, hhi', ?_⟩
  · simp only [unwrapOr, StateT.run_bind, pure_bind]
    simp only [StateT.run_pure, except_ok_bind, hrun2, hrun3]
    rfl
  · exact hd2.grow (decCtx_mono _) hg3
  · rw [hnc]; simp only [BlockShape.memberNames, List.length_map]
    have : bs.k = bs.members.length := rfl
    omega

/-- **`block_nest_ctx` refines `blockNestCtx`** (through `open_pis_at_fvars_f`'s and
`intern_ls_iw`'s stubs; `nP + k ≥ 2^64` a capacity abort): the shape record decoded below the tops
with its members' slice below the top, the checked formers a slice of constants. -/
@[refines ConRon.Arena.blockNestCtx]
theorem blockNestCtx_refines (p : Prog) (hP : NckProg p) (hl : NhLook p)
    (hp : p.lookup "block_nest_ctx" = some blockNestCtx) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q cvO cvL : Word) (bs : BlockShape)
    (cvTas : List IConstantVal) (hS : StageR dn vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m q.toNat) s₀.mem bs)
    (hsrc : ∀ o l, iwN s₀.mem q.toNat = some o → iwN s₀.mem (q.toNat + 1) = some l → o + l ≤ iwTop s₀.mem)
    (hcv : PSlR decCVp cvTas cvO cvL s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "block_nest_ctx" [vis, q, cvO, cvL]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.blockNestCtx fe bs cvTas) a₀ ∧
      DecB (fun m => decCtx m (r.headD 0).toNat) s'.mem (AM.res (ConRon.Arena.blockNestCtx fe bs cvTas) a₀).1 ∧
      decHL s'.mem (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat =
        some (AM.res (ConRon.Arena.blockNestCtx fe bs cvTas) a₀).2 ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop s'.mem ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.blockNestCtx fe bs cvTas) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ CtxIn s'.mem (r.headD 0).toNat (· < iwTop s'.mem) ∧
      CtxSl s'.mem (r.headD 0).toNat ∧ (AM.res (ConRon.Arena.blockNestCtx fe bs cvTas) a₀).1.hiAt 0 < 2 ^ 64 ∧
      (AM.res (ConRon.Arena.blockNestCtx fe bs cvTas) a₀).1.params.length +
        (AM.res (ConRon.Arena.blockNestCtx fe bs cvTas) a₀).1.names.length < 2 ^ 64; ⊤⦄ :=
  triple_post (bnc_spec p hP hl hp n s₀ vis q cvO cvL) fun _ _ ⟨hl', hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (bncW_sim n hS hq hsrc hcv) hm
    ⟨hl', hok, hQ⟩

end L.Ind
