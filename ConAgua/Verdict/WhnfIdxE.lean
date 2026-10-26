import ConAgua.Verdict.WhnfIotaRecE

/-!
# `iota_index_ok`'s and `iota_rec_cmp`'s verdict claims (lane `verdicts-b`, helper `k2`)

No verdict site of their own: their claims are `defeq_list`'s (a callee of the `defeq` family:
`DefeqListE`, a hypothesis, the premises of `defeqList_refines`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace L.Arena

theorem whnfIdxE_nv : ∀ f ∈ ["pi_residual", "get_app_args", "erec_push", "rec_fire_args",
    "stack_cover"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- `defeq_list`'s error claim at fuel `N + 1` (the premises of `defeqList_refines`). -/
def DefeqListE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d ao an bo bn : Word) (aas bs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    SpineN s₀.mem ao an aas → SpineN s₀.mem bo bn bs →
    (an ≠ 0 → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) →
    (bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) →
    CoreSpecE p (N + 1) "defeq_list" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat aas.toList bs.toList) s₀ a₀

/-! ## `iota_index_ok` -/

/-- Error model of `iota_index_ok` (the ok model `ioW`, `callE` for `callW`). -/
def ioE (p : Prog) (n : Nat) (m : Mem) (mode vis d mI rP cnP tyCtor mo mn xo xn : Word) :
    Except Err (List Word × Mem) :=
  if mI = rP then .ok ([1], m)
  else match callE p n "pi_residual" [tyCtor, mo, mn] m with
    | .error e => .error e
    | .ok (r₁, m₁) =>
      if r₁.headD 0 = 0 then .ok ([0], m₁)
      else if ¬ (136 : Word).toNat < (m₁.arr64 CTL).size then .error (.abort 0)
      else match callE p n "get_app_args" [r₁.tail.headD 0] m₁ with
        | .error e => .error e
        | .ok (r₂, m₂) =>
          match callE p n "defeq_list" [mode, vis, d, r₂.headD 0 + cnP,
              (r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0), xo, xn] m₂ with
          | .error e => .error e
          | .ok (r₃, m₃) => .ok ([r₃.headD 0], m₃.set64 CTL 136 (rdW (m₁.arr64 CTL) 136))

theorem ioE_spec (p : Prog) (hp : p.lookup "iota_index_ok" = some iotaIndexOkL) (n : Nat)
    (s₀ : St) (mode vis d mI rP cnP tyCtor mo mn xo xn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_index_ok" [mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      ioE p n s₀.mem mode vis d mI rP cnP tyCtor mo mn xo xn = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaIndexOkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callE_spec p n "pi_residual", callE_spec p n "get_app_args", callE_spec p n "defeq_list"] <;>
  simp_all [ioE, Cmp.eval, Cmp.evalW, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, rdW, CTL] <;>
  (intro hc; exfalso; have h1 := ‹UInt64.toNat 136 < _›; (try simp at h1); (try simp at hc); omega)

theorem iotaIndexOk_err (r : CoreFnsA) (fe : IFEnv) (d mI rP cnP : Nat) (tyCtor : EIdx)
    (margs idx : List EIdx) (a a₁ : AState) (res : EIdx) (xs : List EIdx)
    (h : mI ≠ rP) (hp : (piResidual tyCtor margs).run a = .ok (some res, a₁))
    (hg : (getAppArgs coreWalkFuel res).run a₁ = .ok (xs, a₁)) (ce : CheckError)
    (hd : (defEqList r fe d (xs.drop cnP) idx).run a₁ = .error ce) :
    (iotaIndexOk r fe d mI rP cnP tyCtor margs idx).run a = .error ce := by
  simp only [iotaIndexOk, h, ↓reduceIte, StateT.run_bind, hp, except_ok_bind, hg, hd]

section idx
variable (p : Prog) (hp : IotaProg' p) (hi1 : IotaInst1OK p) (hnv : closedNV p L.Checker.nvFns = true)
  (hDL : DefeqListE p)

set_option maxHeartbeats 1000000 in
include hp hi1 hnv hDL in
/-- **`IotaIndexOkE`**: `iota_index_ok`'s verdicts are `defeq_list`'s. -/
theorem iotaIndexOkE_of : IotaIndexOkE p := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d mI rP cnP tyCtor mo mn xo xn margs idx hS hm4
    hebm hty hsm hsx htm htx
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (ioE_spec p hp.iotaIndexOk n ⟨s₀.mem, Locals.init []⟩
    mode vis d mI rP cnP tyCtor mo mn xo xn) hc0 (Err.code_ne_of_cls hk0)
  simp only [ioE] at hW
  by_cases hI : mI = rP
  · rw [if_pos hI] at hW; cases hW
  rw [if_neg hI] at hW
  have hI' : mI.toNat ≠ rP.toNat := fun h => hI (UInt64.toNat_inj.mp h)
  cases hc1 : callE p n "pi_residual" [tyCtor, mo, mn] s₀.mem with
  | error e1 =>
    rw [hc1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIdxE_nv "pi_residual" (by simp)) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only at hW
  obtain ⟨hrunP, ⟨M₁, hS₁, hK₁, hSt₁⟩, hr₁⟩ := CoreSpec.run
    (piResidual_refines p hp hi1 n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb tyCtor mo mn margs hS hty
      hsm htm) (callW_of_callE hc1)
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  by_cases h136 : ¬ (136 : Word).toNat < (m₁.arr64 CTL).size
  · rw [if_pos h136] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg h136] at hW
  obtain ⟨hf1, hh1⟩ := hr₁
  have hsome : decOptR r₁ = some (decE (r₁.tail.headD 0)) := by
    simp only [decOptR, decOpt, h0, ↓reduceIte]
  rw [hsome] at hrunP
  cases hc2 : callE p n "get_app_args" [r₁.tail.headD 0] m₁ with
  | error e2 =>
    rw [hc2] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIdxE_nv "get_app_args" (by simp)) hc2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  simp only at hW
  have hW' := err_of_k (k := fun (x : Except Err (List Word × Mem)) => match x with
      | .error e => (.error e : Except Err (List Word × Mem))
      | .ok (r₃, m₃) => .ok ([r₃.headD 0], m₃.set64 CTL 136 (rdW (m₁.arr64 CTL) 136)))
    (by intro q e; simp) (fun _ => rfl) hW
  obtain ⟨t₂, ht₂, hloc2, hfr, hgrew, hhead, htop2, xs, hga, hsp2⟩ := triple_of_callE
    (getAppArgs_refines p hp.spine n ⟨m₁, Locals.init []⟩ (AM.st (piResidual (decE tyCtor) margs.toList) a₀)
      hS₁.arena.1 (r₁.tail.headD 0) hh1 hS₁.spn) hc2
  rw [ht₂] at hfr hgrew htop2 hsp2
  have hS₂ : CoreS dn m₂ (AM.st (piResidual (decE tyCtor) margs.toList) a₀) vis fe M₁ eb :=
    hS₁.frame_stk hfr (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have hsx₁ : SpineR m₁ xo xn idx := hsx.keep hSt₁.size hSt₁.below htx hS.spn
  have htx₁ : xo.toNat + xn.toNat ≤ (spTop m₁).toNat := by rw [hSt₁.1]; exact htx
  have hsx₂ : SpineR m₂ xo xn idx := hsx₁.keep hgrew.size hgrew.below htx₁ hS₁.spn
  have htx₂ : xo.toNat + xn.toNat ≤ (spTop m₂).toNat :=
    Nat.le_trans htx₁ (by have := hgrew.1; exact this)
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ n' =>
  have hhead' : r₂.headD 0 = spTop m₁ := hhead
  have htop2' : spTop m₂ = spTop m₁ + r₂.tail.headD 0 := htop2
  obtain ⟨hsd, hsd2⟩ := spine_drop m₂ (r₂.headD 0) (r₂.tail.headD 0) cnP xs.toArray hsp2 hS₂.spn
  have hdrop : xs.toArray.toList.drop cnP.toNat = xs.drop cnP.toNat := by simp
  rw [hdrop] at hsd
  have htd : (r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0) ≠ 0 →
      (r₂.headD 0 + cnP).toNat + ((r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0)).toNat
        ≤ (spTop m₂).toNat := by
    intro hne
    have hcle : cnP ≤ r₂.tail.headD 0 := by
      exact Classical.byContradiction fun hn => by
        simp only [hn, ↓reduceIte, UInt64.mul_zero, ne_eq, not_true_eq_false] at hne
    simp only [hcle, ↓reduceIte, UInt64.mul_one] at hne ⊢
    rw [hsd2 hcle]
    have hb := hsp2.bound
    rw [hhead'] at hb
    have hsp := hS₂.spn
    have : (spTop m₂).toNat = (spTop m₁).toNat + (r₂.tail.headD 0).toNat := by
      rw [htop2', UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [hhead', this]
    exact Nat.le_refl _
  have hD := hDL n' (hk.mono (Nat.le_succ n')) (hkE.mono (Nat.le_succ n')) F (by omega) (by omega)
      ⟨m₂, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₂.headD 0 + cnP) _ xo xn
      (xs.drop cnP.toNat).toArray idx hS₂ hm4 hebm hsd hsx₂.toN htd (fun _ => htx₂)
  simp only [List.toList_toArray] at hD
  exact ErrClaim.of_run_err (fun ce h' => iotaIndexOk_err _ fe d.toNat mI.toNat rP.toNat cnP.toNat
      (decE tyCtor) margs.toList idx.toList a₀ _ (decE (r₁.tail.headD 0)) xs hI' hrunP hga ce h')
    (CoreSpecE.of_callE hD hW')

end idx

/-! ## `iota_rec_cmp` -/

/-- Error model of `iota_rec_cmp` (the ok model `irCmpW`, `callE` for `callW`). -/
def irCmpE (p : Prog) (n : Nat) (m : Mem) (mode vis d us recP so rl mo : Word) :
    Except Err (Word × Mem) :=
  match callE p n "erec_push" [rdW (m.arr64 EREC) (rl + 6), rdW (m.arr64 EREC) (rl + 7),
      rdW (m.arr64 EREC) (rl + 3)] m with
  | .error e => .error e
  | .ok (rp, m1) =>
  match callE p n "rec_fire_args" [rdW (m1.arr64 EREC) (rl + 3), rp.headD 0,
      rdW (m1.arr64 EREC) (rl + 7), rdW (m1.arr64 EREC) (recP + 2), rdW (m1.arr64 EREC) (recP + 3),
      us, so, rdW (m1.arr64 EREC) (recP + 5) + 1, rdW (m1.arr64 EREC) (recP + 6),
      rdW (m1.arr64 EREC) (rl + 2)] m1 with
  | .error e => .error e
  | .ok (ra, m2) =>
  match callE p n "stack_cover" [ra.headD 0 + ra.tail.headD 0] m2 with
  | .error e => .error e
  | .ok (_, m3) =>
  match callE p n "defeq_list" [mode, vis, d, mo, rdW (m3.arr64 EREC) (rl + 2), ra.headD 0,
      ra.tail.headD 0] m3 with
  | .error e => .error e
  | .ok (rd, m4) => .ok (rd.headD 0, m4.set64 CTL 136 (rdW (m.arr64 CTL) 136))

theorem irCmpE_spec (p : Prog) (hp : p.lookup "iota_rec_cmp" = some iotaRecCmpL) (n : Nat)
    (s₀ : St) (mode vis d us recP so rl mo : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_rec_cmp" [mode, vis, d, us, recP, so, rl, mo]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      irCmpE p n s₀.mem mode vis d us recP so rl mo = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaRecCmpL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callE_spec p n "erec_push", callE_spec p n "rec_fire_args", callE_spec p n "stack_cover",
    callE_spec p n "defeq_list"] <;>
  simp_all [-UInt64.toNat_add, irCmpE, EREC, CTL, BinOp.eval, getElem_rdW', Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

section cmp
variable (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
  (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hnv : closedNV p L.Checker.nvFns = true)
  (hDL : DefeqListE p)

include hp hc hw hEI hER hnv hDL in
/-- **`IotaRecCmpE`**: `iota_rec_cmp`'s verdicts are `defeq_list`'s. -/
theorem iotaRecCmpE_of : IotaRecCmpE p := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d us recP so rl mo mn sn lps rule args margs hS
    hm4 hebm hus hlps hrule hsa hsat hmI hsm hsmt hcpm
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (irCmpE_spec p hp.cmp n ⟨s₀.mem, Locals.init []⟩
    mode vis d us recP so rl mo) hc0 (Err.code_ne_of_cls hk0)
  simp only [irCmpE] at hW
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "erec_push" [rdW (s₀.mem.arr64 EREC) (rl + 6),
      rdW (s₀.mem.arr64 EREC) (rl + 7), rdW (s₀.mem.arr64 EREC) (rl + 3)] s₀.mem
    rw [he'] at hW; cases hW; exact absurd h0 hk0
  | succ N =>
  have hk' : KnotUpTo p N := hk.mono (Nat.le_succ N)
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨-, -, -, hcpw, hfpl, hfne, -, -, -⟩ := decRule_rd herec hrule
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  cases c1 : callE p (N + 1) "erec_push" [rdW E (rl + 6), rdW E (rl + 7), rdW E (rl + 3)] s₀.mem with
  | error e1 =>
    rw [c1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIdxE_nv "erec_push" (by simp)) c1
  | ok q =>
  obtain ⟨rp, m1⟩ := q
  rw [c1] at hW
  simp only at hW
  have P1 : MemFrame [SPN] [136] s₀.mem m1 ∧ StackGrew s₀.mem m1 ∧
      (rdW E (rl + 3) = 1 → rp.headD 0 = spTop s₀.mem ∧
        ∃ lv pins, rule.fire = .nested lv pins ∧ SpineR m1 (rp.headD 0) (rdW E (rl + 7)) pins.toArray ∧
          (rp.headD 0).toNat + (rdW E (rl + 7)).toNat ≤ (spTop m1).toNat) := by
    by_cases hk1 : rdW E (rl + 3) = 1
    · obtain ⟨lv, pins, hfire, hpins⟩ := hfne hk1
      have c1' := callW_of_callE c1
      rw [hk1] at c1'
      obtain ⟨fr, gr, hr0, ht1, hsp⟩ := callW_erecPush p hp.erecPush (N + 1) s₀.mem _ _ pins
        (by rw [hE0]; exact herec) hspn (by rw [hE0]; exact hpins) rp m1 c1'
      refine ⟨fr, gr, fun _ => ⟨hr0, lv, pins, hfire, by rw [hr0]; exact hsp, ?_⟩⟩
      have hb := hsp.bound
      have hsz := fr.2.2.1 SPN
      rw [hr0, ht1, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _
    · obtain ⟨-, rfl⟩ := callW_erecPush_no p hp.erecPush (N + 1) s₀.mem _ _ _ hk1 rp m1
        (callW_of_callE c1)
      exact ⟨MemFrame.refl _ _ _, (StackKept.refl _).toGrew, fun h => absurd h hk1⟩
  obtain ⟨fr1, gr1, hpush⟩ := P1
  have hS1 : CoreS dn m1 a₀ vis fe MM eb := hS.frame_stk fr1 (by simp) (by simp)
  have e1 : m1.arr64 EREC = E := by rw [← hE0]; exact fr1.1 EREC (by simp [SPN, EREC]) (by decide)
  rw [e1] at hW
  have hsa1 : SpineR m1 so sn args := hsa.keep gr1.size gr1.below hsat hspn
  have hsn : rdW E (recP + 5) + 1 = sn := by
    apply UInt64.toNat_inj.mp
    have := sn.toNat_lt
    rw [UInt64.toNat_add]; simp; omega
  cases c2 : callE p (N + 1) "rec_fire_args" [rdW E (rl + 3), rp.headD 0, rdW E (rl + 7),
      rdW E (recP + 2), rdW E (recP + 3), us, so, rdW E (recP + 5) + 1, rdW E (recP + 6),
      rdW E (rl + 2)] m1 with
  | error e2 =>
    rw [c2] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIdxE_nv "rec_fire_args" (by simp)) c2
  | ok q =>
  obtain ⟨ra, m2⟩ := q
  rw [c2] at hW
  simp only at hW
  have htop1 : (spTop s₀.mem).toNat ≤ (spTop m1).toNat := gr1.1
  obtain ⟨t2, ht2, -, ok2, ⟨M2, hS2, hK2, gr2⟩, xs, res2, hxs⟩ := triple_of_callE
    (recFireArgs_refines' p hp.toIotaProg' hc hw hEI (N + 1) ⟨m1, Locals.init []⟩ a₀ dn vis fe MM eb
      (rdW E (rl + 3)) (rp.headD 0) (rdW E (rl + 7)) (rdW E (recP + 2)) (rdW E (recP + 3)) us so
      (rdW E (recP + 5) + 1) (rdW E (recP + 6)) (rdW E (rl + 2)) rule lps args hS1 hus
      (by rw [e1]; exact hlps) (by rw [hsn]; exact hsa1)
      (fun h => let ⟨_, lv, pins, hf, hsp, _⟩ := hpush h; ⟨lv, pins, hf, hsp⟩)
      hfpl hcpw
      (by rw [hsn]; show so.toNat + sn.toNat ≤ (spTop m1).toNat; omega)
      (fun h => let ⟨_, _, _, _, _, hb⟩ := hpush h; hb)) c2
  rw [ht2] at hS2 gr2 hxs
  have e2 : m2.arr64 EREC = E := by
    rw [hER _ _ _ _ _ _ (by simp) (callW_of_callE c2), e1]
  cases c3 : callE p (N + 1) "stack_cover" [ra.headD 0 + ra.tail.headD 0] m2 with
  | error e3 =>
    rw [c3] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIdxE_nv "stack_cover" (by simp)) c3
  | ok q =>
  obtain ⟨rx, m3⟩ := q
  rw [c3] at hW
  simp only at hW
  obtain ⟨fr3, gr3, hcov⟩ := callW_stackCover p hp.stackCover (N + 1) m2 _ rx m3 (callW_of_callE c3)
  have hS3 : CoreS dn m3 _ vis fe M2 eb := hS2.frame_stk fr3 (by simp) (by simp)
  have e3 : m3.arr64 EREC = E := by rw [fr3.1 EREC (by simp) (by decide), e2]
  rw [e3] at hW
  have hxs3 : SpineR m3 (ra.headD 0) (ra.tail.headD 0) xs.toArray := SpineR.of_spn_core hxs
    (by rw [fr3.1 SPN (by simp) (by decide)])
  have hxb := hxs.bound
  have hsz2 : (m2.arr64 SPN).size = (s₀.mem.arr64 SPN).size := gr2.size.trans gr1.size
  have hxt : (ra.headD 0).toNat + (ra.tail.headD 0).toNat ≤ (spTop m3).toNat := by
    have h1 : (ra.headD 0 + ra.tail.headD 0).toNat = (ra.headD 0).toNat + (ra.tail.headD 0).toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have h2 := UInt64.le_iff_toNat_le.mp hcov
    omega
  have hgr13 : StackGrew s₀.mem m3 := gr1.trans (gr2.trans gr3)
  have hsm3 : SpineR m3 mo mn margs := hsm.keep hgr13.size hgr13.below hsmt hspn
  have hcpm' : (rdW E (rl + 2)).toNat ≤ mn.toNat := by rw [← hcpw]; exact hcpm
  have hmt3 : mo.toNat + mn.toNat ≤ (spTop m3).toNat := by
    have := UInt64.le_iff_toNat_le.mp hgr13.1; omega
  have hW' := err_of_k (k := fun (x : Except Err (List Word × Mem)) => match x with
      | .error e => (.error e : Except Err (Word × Mem))
      | .ok (rd, m4) => .ok (rd.headD 0, m4.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136)))
    (by intro q e; simp) (fun _ => rfl) hW
  have hD := hDL N hk' (hkE.mono (Nat.le_succ N)) F (by omega) (by omega) ⟨m3, Locals.init []⟩ _ dn vis fe
      M2 eb mode d mo (rdW E (rl + 2)) (ra.headD 0) (ra.tail.headD 0)
      (margs.toList.take (rdW E (rl + 2)).toNat).toArray xs.toArray hS3 hm4 hebm
      (hsm3.take _ hcpm').toN hxs3.toN
      (fun _ => by show mo.toNat + (rdW E (rl + 2)).toNat ≤ (spTop m3).toNat; omega)
      (fun _ => hxt)
  simp only [List.toList_toArray] at hD
  have hrunA := AM.run_of_ok _ _ ok2
  rw [res2] at hrunA
  refine ErrClaim.of_run_err (fun ce h' => ?_) (CoreSpecE.of_callE hD hW')
  simp only [iotaRecCmpT, StateT.run_bind, hrunA, except_ok_bind]
  rw [hcpw]
  exact h'

end cmp

end L.Arena
