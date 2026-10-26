import ConAgua.Verdict.WhnfModels5E
import ConAgua.Verdict.WhnfIotaRecE

/-!
# `iota_certs_full`'s verdict claims (lane `verdicts-b`, helper `k2`)

No verdict site of its own: the claims are the `infer` and `defeq` slots' (`KnotUpToE`), through
the mutual recursion `iota_certs_full_aux` ↔ `_forall`/`_flush` (by induction on the L fuel, as
`icf_all`), then `iota_certs_full` (`iotaCertsFullE_of`: `IotaCertsFullE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace L.Arena

theorem whnfCertsE_nv : ∀ f ∈ ["inst_list", "iota_certs_full_parts", "spn_get", "expr_view_ok",
    "ctl_get"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- The three functions' common error statement (the premises of `ICFSpec`). -/
def ICFSpecE (p : Prog) (f : FnName) (cond : Word → Word → Word → Prop) (N : Nat) : Prop :=
  ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 → KnotUpTo p N → KnotUpToE p N →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h aco acn ao an i : Word) (acc args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW h → cond h an i →
    SpineR s₀.mem aco acn acc → SpineR s₀.mem ao an args → aco + acn = spTop s₀.mem →
    ao.toNat + an.toNat ≤ aco.toNat →
    CoreSpecE p (N + 1) f [mode, vis, d, h, aco, acn, ao, an, i]
      (iotaCertsFullAux (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args i.toNat) s₀ a₀

section icfErr
variable (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (acc args : Array EIdx) (i : Nat)

theorem icf_err_inst (hi : i < args.size) (a : AState) (ty body : EIdx)
    (hv : a.store.view h = some (.forallE ty body)) (ce : CheckError)
    (h1 : (instantiateListFast coreWalkFuel ty acc 0).run a = .error ce) :
    (iotaCertsFullAux r fe d h acc args i).run a = .error ce := by
  have hv' : (view h).run a = .ok (.forallE ty body, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h1]; rfl

theorem icf_err_infer (hi : i < args.size) (a a1 : AState) (ty body ty2 : EIdx)
    (hv : a.store.view h = some (.forallE ty body))
    (h1 : (instantiateListFast coreWalkFuel ty acc 0).run a = .ok (ty2, a1)) (ce : CheckError)
    (h2 : (r.infer d args[i]).run a1 = .error ce) :
    (iotaCertsFullAux r fe d h acc args i).run a = .error ce := by
  have hv' : (view h).run a = .ok (.forallE ty body, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h1, h2]; rfl

theorem icf_err_defeq (hi : i < args.size) (a a1 a2 : AState) (ty body ty2 ta : EIdx)
    (hv : a.store.view h = some (.forallE ty body))
    (h1 : (instantiateListFast coreWalkFuel ty acc 0).run a = .ok (ty2, a1))
    (h2 : (r.infer d args[i]).run a1 = .ok (ta, a2)) (ce : CheckError)
    (h3 : (r.defeq d ta ty2).run a2 = .error ce) :
    (iotaCertsFullAux r fe d h acc args i).run a = .error ce := by
  have hv' : (view h).run a = .ok (.forallE ty body, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h1, h2, h3]; rfl

theorem icf_err_cont (hi : i < args.size) (a a1 a2 a3 : AState) (ty body ty2 ta : EIdx)
    (hv : a.store.view h = some (.forallE ty body))
    (h1 : (instantiateListFast coreWalkFuel ty acc 0).run a = .ok (ty2, a1))
    (h2 : (r.infer d args[i]).run a1 = .ok (ta, a2))
    (h3 : (r.defeq d ta ty2).run a2 = .ok (true, a3)) (ce : CheckError)
    (h4 : (iotaCertsFullAux r fe d body (acc.push args[i]) args (i + 1)).run a3 = .error ce) :
    (iotaCertsFullAux r fe d h acc args i).run a = .error ce := by
  have hv' : (view h).run a = .ok (.forallE ty body, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h1, h2, h3, h4]
  simp [h4]

theorem icf_err_flush (hi : i < args.size) (a a1 : AState) (x : Nat) (ty2 : EIdx)
    (hv : a.store.view h = some (.bvar x)) (h0 : acc.size ≠ 0)
    (h1 : (instantiateListFast coreWalkFuel h acc 0).run a = .ok (ty2, a1)) (ce : CheckError)
    (h2 : (iotaCertsFullAux r fe d ty2 #[] args i).run a1 = .error ce) :
    (iotaCertsFullAux r fe d h acc args i).run a = .error ce := by
  have hv' : (view h).run a = .ok (.bvar x, a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  rw [iotaCertsFullAux]
  simp only [hi, ↓reduceDIte, StateT.run_bind, hv', except_ok_bind, h0, h1, h2, ↓reduceIte]

end icfErr

section icf
variable (p : Prog) (hp : IotaProg4 p) (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true)

include hp hil hnv in
theorem icfForallE_ok (N : Nat)
    (hA : ∀ N', N = N' + 1 → ICFSpec p "iota_certs_full_aux" (fun _ _ _ => True) N')
    (hAE : ∀ N', N = N' + 1 → ICFSpecE p "iota_certs_full_aux" (fun _ _ _ => True) N') :
    ICFSpecE p "iota_certs_full_forall" (fun h an i => h >>> 28 = 6 ∧ i < an) N := by
  intro F hnF hn62 hk hkE s₀ a₀ dn vis fe MM eb mode d h aco acn ao an i acc args hS hm4 hebm hh
    ⟨h6, hi⟩ hacc hargs htop hao
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (icfForallE_spec p hp.iotaCertsFullForall N ⟨s₀.mem, Locals.init []⟩
    mode vis d h aco acn ao an i) hc0 (Err.code_ne_of_cls hk0)
  simp only [icfForallE] at hW
  cases N with
  | zero =>
    obtain ⟨e', he', h0'⟩ := callE_zero p "iota_certs_full_parts" [h] s₀.mem
    rw [he'] at hW; cases hW; exact absurd h0' hk0
  | succ N' =>
  have hA' := hA N' rfl
  have hAE' := hAE N' rfl
  have hk' : KnotUpTo p N' := hk.mono (by omega)
  have hkE' : KnotUpToE p N' := hkE.mono (by omega)
  cases c1 : callE p (N' + 1) "iota_certs_full_parts" [h] s₀.mem with
  | error e1 =>
    rw [c1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfCertsE_nv "iota_certs_full_parts" (by simp)) c1
  | ok q =>
  obtain ⟨pr, m0⟩ := q
  rw [c1] at hW
  simp only at hW
  obtain ⟨t1, ht1, -, hmem1, hparts⟩ := triple_of_callE
    (icfParts_spec p hp.iotaCertsFullParts N' ⟨s₀.mem, Locals.init []⟩ h) c1
  obtain rfl : m0 = s₀.mem := by rw [← ht1]; exact hmem1
  simp only [icfPartsW] at hparts
  obtain ⟨g1, hparts⟩ := of_ite_none hparts
  obtain ⟨g2, hparts⟩ := of_ite_none hparts
  simp only [Option.some.injEq] at hparts
  obtain ⟨hvw, hn1, hn2⟩ := view_forall s₀.mem a₀ hS.arena.1 h hh ⟨g1, UInt64.not_le.mp g2⟩ h6
  simp only [List.cons.injEq, and_true] at hparts
  obtain ⟨hp0, hp1⟩ := hparts
  rw [hp0] at hvw hn1
  rw [hp1] at hvw hn2
  cases c2 : callE p (N' + 1) "spn_get" [ao + i] s₀.mem with
  | error e2 =>
    rw [c2] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfCertsE_nv "spn_get" (by simp)) c2
  | ok q =>
  obtain ⟨ra, m00⟩ := q
  rw [c2] at hW
  simp only at hW
  obtain ⟨t2, ht2, -, hmem2, hget⟩ := triple_of_callE
    (spnGet_spec p hp.spnGet N' ⟨s₀.mem, Locals.init []⟩ (ao + i)) c2
  obtain rfl : m00 = s₀.mem := by rw [← ht2]; exact hmem2
  obtain ⟨hisz, hargw, hargget⟩ := spine_entry s₀.mem ao an i args hargs hi
  have hra : ra.headD 0 = spW s₀.mem (ao + i) := by
    simp only [spnGetW] at hget
    split at hget
    · simp only [Option.some.injEq] at hget; rw [← hget]; rfl
    · cases hget
  rw [← hra] at hargw hargget
  have hbd := hacc.bound
  have hspn := hS.spn
  have h263 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
  have htopc : aco.toNat + acn.toNat ≤ (spTop s₀.mem).toNat := by
    rw [← htop, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _
  have hty : HW (pr.headD 0) := hn1
  cases c3 : callE p (N' + 1) "iota_certs_full_check"
      [mode, vis, d, pr.headD 0, aco, acn, ra.headD 0] s₀.mem with
  | error e3 =>
    rw [c3] at hW; cases hW
    -- the check's own failure: `inst_list`, `infer`, `defeq`
    have hC := triple_of_callE_err (icfCheckE_spec p hp.iotaCertsFullCheck N' ⟨s₀.mem, Locals.init []⟩
      mode vis d (pr.headD 0) aco acn (ra.headD 0)) c3 (Err.code_ne_of_cls hk0)
    simp only [icfCheckE] at hC
    cases d1 : callE p N' "inst_list" [pr.headD 0, aco, acn, 0] s₀.mem with
    | error f1 =>
      rw [d1] at hC; cases hC
      exact ErrClaim.of_callE_nv hnv (whnfCertsE_nv "inst_list" (by simp)) d1
    | ok q =>
    obtain ⟨r1, m1⟩ := q
    rw [d1] at hC
    simp only at hC
    obtain ⟨ok1, ⟨M1, hS1, -, -⟩, res1, hr1⟩ := CoreSpec.of_callW
      (hil N' ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb (pr.headD 0) aco acn 0 acc hS hty hacc htopc)
      (callW_of_callE d1)
    have hrun1 := AM.run_of_ok _ _ ok1
    rw [res1] at hrun1
    cases d2 : callE p N' "infer" [mode, vis, d, ra.headD 0] m1 with
    | error f2 =>
      rw [d2] at hC; cases hC
      exact ErrClaim.of_run_err (fun ce h' => icf_err_infer _ fe d.toNat (decE h) acc args i.toNat hisz a₀
          _ _ _ _ hvw hrun1 ce (by rw [hargget]; exact h'))
        (CoreSpecE.of_callE ((hkE' N' (Nat.le_refl _)).infer F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb
          mode d (ra.headD 0) (by omega) (by omega) ⟨hS1, hm4, hebm⟩ hargw) d2)
    | ok q =>
    obtain ⟨r2, m2⟩ := q
    rw [d2] at hC
    simp only at hC
    obtain ⟨ok2, ⟨M2, hS2, -, -⟩, res2, hr2⟩ := CoreSpec.of_callW
      ((hk' N' (Nat.le_refl _)).infer F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d (ra.headD 0)
        (by omega) (by omega) ⟨hS1, hm4, hebm⟩ hargw) (callW_of_callE d2)
    have hrun2 := AM.run_of_ok _ _ ok2
    rw [res2] at hrun2
    have hC' := err_of_k (k := fun (x : Except Err (List Word × Mem)) => match x with
        | .error e => (.error e : Except Err (List Word × Mem))
        | .ok (ok, m3) => .ok ([ok.headD 0], m3)) (by intro q e; simp) (fun _ => rfl) hC
    exact ErrClaim.of_run_err (fun ce h' => icf_err_defeq _ fe d.toNat (decE h) acc args i.toNat hisz a₀
        _ _ _ _ _ _ hvw hrun1 (by rw [hargget]; exact hrun2) ce h')
      (CoreSpecE.of_callE ((hkE' N' (Nat.le_refl _)).defeq F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb
        mode d _ _ (by omega) (by omega) ⟨hS2, hm4, hebm⟩ hr2 hr1) hC')
  | ok q =>
  obtain ⟨ok, m3⟩ := q
  rw [c3] at hW
  simp only at hW
  obtain ⟨t3, ht3, -, hchk⟩ := triple_of_callE
    (icfCheck_spec p hp.iotaCertsFullCheck N' ⟨s₀.mem, Locals.init []⟩ mode vis d (pr.headD 0) aco acn
      (ra.headD 0)) c3
  rw [ht3] at hchk
  obtain ⟨ty2, ta, a1, a2, a3, b, hr1, hr2, hr3, hCA3, hbk, hwok⟩ := icfCheck_ok p hil N' F hk'
    (by omega) (by omega) dn vis fe eb mode d (pr.headD 0) aco acn (ra.headD 0) hm4 hebm hty hargw
    acc s₀.mem a₀ MM hS hacc htopc [ok.headD 0] m3 hchk
  rw [← hargget] at hr2
  have hr1' : (instantiateListFast coreWalkFuel (decE (pr.headD 0)) acc 0).run a₀ = .ok (ty2, a1) := hr1
  by_cases hok0 : ok.headD 0 = 0
  · rw [if_pos hok0] at hW; cases hW
  rw [if_neg hok0] at hW
  by_cases hg : ¬ ((aco + acn).toNat < (m3.arr64 SPN).size ∧ (136 : Word).toNat < (m3.arr64 CTL).size)
  · rw [if_neg hg] at hW; cases hW; exact absurd rfl hk0
  have hg := Classical.not_not.mp hg
  rw [if_pos hg] at hW
  have hW' := err_of_k (k := fun (x : Except Err (List Word × Mem)) => match x with
      | .error e => (.error e : Except Err (List Word × Mem))
      | .ok (r, m4) => .ok ([r.headD 0], m4)) (by intro q e; simp) (fun _ => rfl) hW
  obtain ⟨M3, hS3, hK3, hSt3⟩ := hCA3
  have hb : b = true := by
    rw [← hbk]; simpa using hok0
  subst hb
  have htop3 : spTop m3 = aco + acn := by rw [hSt3.1, ← htop]
  have hq1 : (aco + acn).toNat + 1 < 2 ^ 64 := by
    have : (aco + acn).toNat < (m3.arr64 SPN).size := hg.1
    have hsz3 : (m3.arr64 SPN).size = (s₀.mem.arr64 SPN).size := hSt3.size
    omega
  obtain ⟨hfr, hsp', hgrew, hslot, hsz⟩ := push_step m3 (aco + acn) (ra.headD 0) hg.1 hg.2 htop3 hq1
  have hS3p := hS3.frame_stk hfr (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have hacc3 : SpineR m3 aco acn acc := hacc.keep hSt3.size hSt3.below htopc hS.spn
  have htop3' : aco.toNat + acn.toNat ≤ (spTop m3).toNat := by rw [htop3]; exact (by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _)
  have hsum : (aco + acn).toNat = aco.toNat + acn.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hpush := (SpineR.push hacc3 hS3.spn (by rw [← hsum]; exact hg.1) (ra.headD 0) hargw).setCtl 136
    (aco + acn + 1)
  have hargs3 : SpineR m3 ao an args := hargs.keep hSt3.size hSt3.below (by omega) hS.spn
  have hargs3p : SpineR _ ao an args := hargs3.keep hgrew.size hgrew.below (by omega) hS3.spn
  have htopp : aco + (acn + 1) = spTop ((m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1)) := by
    rw [hsp', UInt64.add_assoc]
  generalize (m3.set64 SPN (aco + acn) (ra.headD 0)).set64 CTL 136 (aco + acn + 1) = m3p at *
  have hi1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hi
  have hE4 := hAE' F (by omega) (by omega) hk' hkE' ⟨m3p, Locals.init []⟩ a3 dn vis fe M3 eb mode d
    (pr.tail.headD 0) aco (acn + 1) ao an (i + 1) (acc.push (decE (ra.headD 0))) args hS3p hm4 hebm hn2
    trivial hpush hargs3p htopp hao
  rw [hi1] at hE4
  exact ErrClaim.of_run_err (fun ce h' => icf_err_cont _ fe d.toNat (decE h) acc args i.toNat hisz a₀
      _ _ _ _ _ _ _ hvw hr1' hr2 hr3 ce (by rw [hargget]; exact h'))
    (CoreSpecE.of_callE hE4 hW')

end icf

end L.Arena
