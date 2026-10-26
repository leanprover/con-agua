import ConAgua.Verdict.WhnfModels2E
import ConAgua.Verdict.WhnfSlotE

/-!
# The `app` arm's verdict claims (lane `verdicts-b`, helper `k2`)

`whnf_core_app`, `whnf_core_app2`, `whnf_app` have no verdict site of their own: their claims are
the head's `whnf_core` slot's (`KnotUpToE`) and `iota_rec_at`'s (`IotaRecAtE`, a hypothesis),
propagated (`coreAppE_of`: `CoreAppE`). The `whnf_app` loop's claim (`appLoopE_ref`) is the ok
loop's induction (`appFull_ref`) with the error model in place of the ok one: the invariants are
carried the same way up to the failing iteration.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfAppE_nv : ∀ f ∈ ["beta_peel", "mk_app", "mk_app_n_from", "get_app_spine",
    "head_and_args"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- `iota_rec_at`'s error claim at fuel `N + 1` (the shape of `IotaRecAtOK`). -/
def IotaRecAtE (p : Prog) : Prop :=
  ∀ N, KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d hd so sn : Word) (xs : Array EIdx), N ≤ F → N ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW hd → SpineR s₀.mem so sn xs →
    so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p (N + 1) "iota_rec_at" [mode, vis, d, hd, so, sn]
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE hd) xs xs.size) s₀ a₀

theorem apW_of_callE {p : Prog} {k : Nat} {m : Mem} {v same aW nW : Word} {r : List Word} {m₁ : Mem}
    (hs : same = 0) (h : callE p k "mk_app" [v, aW] m = .ok (r, m₁)) :
    apW p k m v same aW nW = some (r.headD 0, m₁) := by
  simp [apW, hs, callW_of_callE h]

theorem apW_same {p : Prog} {k : Nat} {m : Mem} {v same aW nW : Word} (hs : same ≠ 0) :
    apW p k m v same aW nW = some (nW, m) := by
  simp [apW, hs]

section appRef
variable (p : Prog) (hp : WhnfCoreProg p) (hnv : closedNV p L.Checker.nvFns = true)
  (hI : IotaRecAtE p)
  (hiok : ∀ n, KnotUpTo p n → IotaRecAtOK p (n + 1))

include hp hnv hI hiok in
/-- **The `whnf_app` loop's error model fails only where `whnfApp` does**, by induction on the L
fuel (the invariants of `appFull_ref`). -/
theorem appLoopE_ref (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62)
    (mode vis d hd vo ao an top : Word) (args nodes : Array EIdx)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (eb : Word) (m₀ : Mem)
    (hmode : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hhd : HW hd)
    (har₀ : SpineR m₀ ao an args) (hno₀ : SpineR m₀ (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) (hvot : vo.toNat ≤ top.toNat)
    (hspn0 : (m₀.arr64 SPN).size < 2 ^ 63) :
    ∀ (k : Nat), k ≤ n + 1 → ∀ (a : AState) (m : Mem) (v vn same i : Word) (va : Array EIdx)
      (MM : ModeMaps),
      CoreS dn m a vis fe MM eb → HW v → SpineR m vo vn va → spTop m = vo + vn →
      top.toNat ≤ (vo + vn).toNat → (∀ j : Word, j < top → spW m j = spW m₀ j) →
      (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      ∀ er, whnfAppE.loop1 p k m mode vis d v hd vo vn same ao an i top = .error er →
      ErrClaim (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE hd)
        va (same != 0) args nodes i.toNat) a er := by
  intro k
  induction k with
  | zero =>
    intro _ a m v vn same i va MM _ _ _ _ _ _ _ er hF
    simp only [whnfAppE.loop1] at hF; cases hF; exact ErrClaim.of_cls0 rfl
  | succ k ih =>
    intro hkn a m v vn same i va MM hS hv hva htop htv hb hsz er hF
    by_cases hk0 : er.cls = 0
    · exact ErrClaim.of_cls0 hk0
    have hspn := hS.spn
    have hvn64 : vo.toNat + vn.toNat < 2 ^ 64 := by have := hva.bound; omega
    have hadd : (vo + vn).toNat = vo.toNat + vn.toNat := addW _ _ hvn64
    have hlt_args : args.size = an.toNat := har₀.size
    simp only [whnfAppE.loop1] at hF
    by_cases hlt : ¬ i < an
    · rw [ite_eq_right hlt] at hF; cases hF
    have hlt : i < an := Classical.not_not.mp hlt
    rw [ite_eq_left hlt] at hF
    have hlt' : i.toNat < args.size := by
      rw [hlt_args]; exact UInt64.lt_iff_toNat_lt.mp hlt
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp
      have := UInt64.lt_iff_toNat_lt.mp hlt
      have := an.toNat_lt
      omega
    have hjtop : ∀ j : Word, j < top → j < spTop m := fun j hj => by
      rw [htop, UInt64.lt_iff_toNat_lt, hadd]
      have := UInt64.lt_iff_toNat_lt.mp hj; omega
    have haoT : ao.toNat + an.toNat ≤ top.toNat := by omega
    have hnoT : (ao + an).toNat + an.toNat ≤ top.toNat := by
      have := har₀.bound
      rw [addW _ _ (by omega)]; omega
    have har : SpineR m ao an args := har₀.keepT top hsz hb haoT hspn0
    have hno : SpineR m (ao + an) an nodes := hno₀.keepT top hsz hb hnoT hspn0
    have hit : (i.toNat).toUInt64 = i := by simp
    have hxi : args[i.toNat] = decE (spW m (ao + i)) := by
      have h := har.get i.toNat hlt'
      rwa [hit] at h
    have hvv : (spW m (ao + i)).toNat < 2 ^ 32 := by
      have h := har.lt i.toNat (by rw [← har.size]; exact hlt')
      rwa [hit] at h
    by_cases hlam : v >>> 28 = 5
    · rw [ite_eq_left hlam] at hF
      by_cases c1 : tierW v ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
      · rw [ite_eq_left c1] at hF; cases hF; exact absurd rfl hk0
      rw [ite_eq_right c1] at hF
      by_cases c2 : tcnt m LAM (tierW v) ≤ idxW v
      · rw [ite_eq_left c2] at hF; cases hF; exact absurd rfl hk0
      rw [ite_eq_right c2] at hF
      exact ErrClaim.of_callE_nv hnv (whnfAppE_nv "beta_peel" (by simp))
        (err_of_k (by intro q e; simp [whnfAppE.k_beta_peel]) (fun _ => rfl) hF)
    rw [ite_eq_right hlam] at hF
    have hnodeget : nodes[i.toNat]! = decE (rdW (m.arr64 SPN) (ao + an + i)) := by
      have hi2 : i.toNat < nodes.size := by rw [hno.size]; exact UInt64.lt_iff_toNat_lt.mp hlt
      have h := hno.get i.toNat hi2
      have hit2 : (ao + an) + (i.toNat).toUInt64 = ao + an + i := by rw [hit]
      rw [getElem!_pos nodes i.toNat hi2, h, hit2]; rfl
    have hnW : HW (rdW (m.arr64 SPN) (ao + an + i)) := by
      have h := hno.lt i.toNat (UInt64.lt_iff_toNat_lt.mp hlt)
      rwa [hit] at h
    -- the next spine node: `apW`
    have hap : ∃ ap m₁, apW p k m v same (rdW (m.arr64 SPN) (ao + i))
        (rdW (m.arr64 SPN) (ao + an + i)) = some (ap, m₁) ∧
        whnfAppE.j1 p k mode vis d v hd vo vn ao an i top (rdW (m.arr64 SPN) (ao + i))
          (rdW (m.arr64 SPN) (ao + an + i)) ap m₁ = .error er := by
      by_cases hs : same ≠ 0
      · rw [ite_eq_left hs] at hF
        exact ⟨_, _, apW_same hs, hF⟩
      · rw [ite_eq_right hs] at hF
        have hs' : same = 0 := by simpa using hs
        cases hmk : callE p k "mk_app" [v, rdW (m.arr64 SPN) (ao + i)] m with
        | error e1 =>
          rw [hmk, whnfAppE.k_mk_app.none] at hF; cases hF
          exact absurd (callE_nv hnv (whnfAppE_nv "mk_app" (by simp)) k _ m hmk) hk0
        | ok q =>
        obtain ⟨r₁, m₁⟩ := q
        rw [hmk] at hF
        simp only [whnfAppE.k_mk_app] at hF
        exact ⟨_, _, apW_of_callE hs' hmk, hF⟩
    obtain ⟨ap, m₁, hapE, hF⟩ := hap
    obtain ⟨a₁, hrunAp, hS₁, hSt₁, hapW⟩ := apW_ref p hp k m a dn vis fe MM eb hS v same
      (rdW (m.arr64 SPN) (ao + i)) (rdW (m.arr64 SPN) (ao + an + i)) hv hvv hnW ap m₁ hapE
    simp only [whnfAppE.j1] at hF
    by_cases hlen : m₁.len64 SPN ≤ vo + vn
    · rw [ite_eq_left hlen] at hF; cases hF; exact absurd rfl hk0
    rw [ite_eq_right hlen] at hF
    -- the stack top is in bounds (it is `vo + vn ≠ 0`)
    have hc136 : (136 : Word).toNat < (m₁.arr64 CTL).size := by
      have ht1 : spTop m₁ = vo + vn := hSt₁.1.trans htop
      refine Classical.byContradiction fun hc => ?_
      have : spTop m₁ = 0 := by
        unfold spTop rdW
        rw [Array.getElem?_eq_none (by omega)]; rfl
      rw [this] at ht1
      have h0 : (vo + vn).toNat = 0 := by rw [← ht1]; rfl
      rw [hadd] at h0
      have := UInt64.lt_iff_toNat_lt.mp hlt
      omega
    have hbd : vo.toNat + vn.toNat < (m₁.arr64 SPN).size := by
      have h : ¬ UInt64.ofNat (m₁.arr64 SPN).size ≤ vo + vn := hlen
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by
        have := hSt₁.size; omega), hadd] at h
      omega
    have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hSt₁.size ▸ hspn
    have hva₁ : SpineR m₁ vo vn va := hva.keep hSt₁.size hSt₁.below (by rw [htop, hadd]; exact Nat.le_refl _) hspn
    have hS₂ := hS₁.frame_stk (spnCtl_frame m₁ (vo + vn) (rdW (m.arr64 SPN) (ao + i))
      (vo + vn + 1)) (by simp) (by simp)
    have hva₂ : SpineR ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
        (vo + vn + 1)) vo (vn + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) :=
      (hva₁.push hspn₁ hbd _ hvv).setCtl 136 (vo + vn + 1)
    have htop₂ : spTop ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
        (vo + vn + 1)) = vo + (vn + 1) := by
      unfold spTop
      rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [size_set64]; exact hc136⟩, UInt64.add_assoc]
    have hvn1 : (vn + 1).toNat = vn.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hadd2 : (vo + (vn + 1)).toNat = vo.toNat + vn.toNat + 1 := by
      rw [← UInt64.add_assoc, addW _ _ (by rw [hadd]; have : (1 : Word).toNat = 1 := rfl; omega),
        hadd]
      have : (1 : Word).toNat = 1 := rfl
      omega
    have htv₂ : top.toNat ≤ (vo + (vn + 1)).toNat := by rw [hadd2]; omega
    have hb₂ : ∀ j : Word, j < top →
        spW ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136 (vo + vn + 1)) j =
          spW m₀ j := by
      intro j hj
      rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
        have := UInt64.lt_iff_toNat_lt.mp hj
        rw [← h, hadd] at this; omega), hSt₁.below j (hjtop j hj)]
      exact hb j hj
    have hsz₂ : (((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
        (vo + vn + 1)).arr64 SPN).size = (m₀.arr64 SPN).size := by
      simp only [size_set64]; exact hSt₁.size.trans hsz
    have hnotlam : ((decE v).tag == ETag.lam) = false := by
      rw [decE_tag_lam v hv]; simp [hlam]
    have hunf := whnfApp_nolam (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
      (decE v) (decE hd) va (same != 0) args nodes i.toNat hlt' hnotlam
    have hxi' : args[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := hxi
    rw [hnodeget, hxi'] at hunf
    have hkn' : k ≤ n + 1 := by omega
    have hsame : (if ap = rdW (m.arr64 SPN) (ao + an + i) then (1 : Word) else 0) =
        Cmp.evalW .eq ap (rdW (m.arr64 SPN) (ao + an + i)) := by
      simp [Cmp.evalW, Cmp.eval]
    rw [hsame] at hF
    have hvo1 : vo + vn + 1 = vo + (vn + 1) := UInt64.add_assoc _ _ _
    rw [← hvo1] at hF
    by_cases hconst : hd >>> 28 = 3
    · rw [ite_eq_left hconst] at hF
      generalize hm₂ : ((m₁.set64 SPN (vo + vn) (rdW (m.arr64 SPN) (ao + i))).set64 CTL 136
        (vo + vn + 1)) = m₂ at hS₂ hva₂ htop₂ hb₂ hsz₂ hF
      have hctag : ((decE hd).tag == ETag.const) = true := by
        rw [decE_tag_const hd hhd]; simp [hconst]
      cases hcI : callE p k "iota_rec_at" [mode, vis, d, hd, vo, vn + 1] m₂ with
      | error e2 =>
        rw [hcI, whnfAppE.k_iota_rec_at.none] at hF; cases hF
        cases k with
        | zero => exact ErrClaim.of_callE_zeroW hcI
        | succ k' =>
        refine ErrClaim.of_run_err (fun ce h' => ?_) (CoreSpecE.of_callE (hI k' (hk.mono (by omega))
          (hkE.mono (by omega)) F ⟨m₂, Locals.init []⟩ a₁ dn vis fe MM eb mode d hd vo (vn + 1) _
          (by omega) (by omega) ⟨hS₂, hmode, hebm⟩ hhd hva₂ (by rw [htop₂, hadd2]; omega)) hcI)
        rw [hunf]
        simp only [StateT.run_bind, hrunAp, except_ok_bind, hctag, ite_true, h']
        rfl
      | ok q =>
      obtain ⟨rr, m₃⟩ := q
      rw [hcI] at hF
      cases k with
      | zero =>
        obtain ⟨e', he', -⟩ := callE_zero p "iota_rec_at" [mode, vis, d, hd, vo, vn + 1] m₂
        rw [hcI] at he'; cases he'
      | succ k' =>
      have hiota := hiok k' (hk.mono (by omega)) F ⟨m₂, Locals.init []⟩ a₁
        dn vis fe MM eb mode d hd vo (vn + 1) _ (by omega) (by omega) ⟨hS₂, hmode, hebm⟩ hhd
        hva₂ (by rw [htop₂, hadd2]; omega)
      obtain ⟨hokI, ⟨M', hS₃, -, hSt₃⟩, hresI, hrwI⟩ := CoreSpec.of_callW hiota (callW_of_callE hcI)
      have hva₃ : SpineR m₃ vo (vn + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) :=
        hva₂.keep hSt₃.size hSt₃.below (by rw [htop₂, hadd2]; omega) (hsz₂ ▸ hspn0)
      have htop₃ : spTop m₃ = vo + (vn + 1) := hSt₃.1.trans htop₂
      have hb₃ : ∀ j : Word, j < top → spW m₃ j = spW m₀ j := fun j hj => by
        rw [hSt₃.below j (by rw [htop₂, UInt64.lt_iff_toNat_lt, hadd2]
                             have := UInt64.lt_iff_toNat_lt.mp hj; omega)]
        exact hb₂ j hj
      have hsz₃ : (m₃.arr64 SPN).size = (m₀.arr64 SPN).size := hSt₃.size.trans hsz₂
      by_cases hz : rr.headD 0 ≠ 0
      · simp only [whnfAppE.k_iota_rec_at, ite_eq_left hz] at hF
        exact ErrClaim.of_callE_nv hnv (whnfAppE_nv "mk_app_n_from" (by simp))
          (err_of_k (by intro q e; simp [whnfAppE.k_mk_app_n_from]) (fun _ => rfl) hF)
      simp only [whnfAppE.k_iota_rec_at, ite_eq_right hz, whnfAppE.j2] at hF
      have hz' : rr.headD 0 = 0 := by simpa using hz
      have := ih (by omega) _ m₃ ap (vn + 1) _ (i + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) M'
        hS₃ hapW hva₃ htop₃ (by rw [hadd2]; omega) hb₃ hsz₃ er hF
      rw [hi1, evalW_eq_ne ap _ hapW hnW] at this
      refine ErrClaim.of_run_eqW ?_ this
      rw [hunf]
      simp only [StateT.run_bind, hrunAp, except_ok_bind, hctag, ite_true]
      have hopt : decOptR rr = none := by unfold decOptR decOpt; rw [ite_eq_left hz']
      rw [AM.run_of_ok _ _ hokI, hresI, hopt]
      simp only [except_ok_bind, appStepT]
    · rw [ite_eq_right hconst] at hF
      simp only [whnfAppE.j2] at hF
      have hctag : ((decE hd).tag == ETag.const) = false := by
        rw [decE_tag_const hd hhd]; simp [hconst]
      have := ih hkn' a₁ _ ap (vn + 1) _ (i + 1) (va.push (decE (rdW (m.arr64 SPN) (ao + i)))) MM hS₂
        hapW hva₂ htop₂ htv₂ hb₂ hsz₂ er hF
      rw [hi1, evalW_eq_ne ap _ hapW hnW] at this
      refine ErrClaim.of_run_eqW ?_ this
      rw [hunf]
      simp only [StateT.run_bind, hrunAp, except_ok_bind, hctag, Bool.false_eq_true, ite_false,
        appStepT]

include hp hnv hI hiok in
/-- **`whnf_app`'s verdicts** are `whnfApp`'s (the ι steps' failures). -/
theorem whnfApp_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d v hd vo vn same ao an i : Word)
    (vargs args nodes : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v)
    (hhd : HW hd) (hva : SpineR s₀.mem vo vn vargs) (htop : spTop s₀.mem = vo + vn)
    (har : SpineR s₀.mem ao an args) (hno : SpineR s₀.mem (ao + an) an nodes)
    (hlo : ao.toNat + an.toNat + an.toNat ≤ vo.toNat) :
    CoreSpecE p (n + 1) "whnf_app" [mode, vis, d, v, hd, vo, vn, same, ao, an, i]
      (whnfApp (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE hd) vargs
        (same != 0) args nodes i.toNat) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (whnfApp_specE p hp.app (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d v hd vo vn same ao an i) hc (Err.code_ne_of_cls hk0)
  simp only [whnfAppE] at hW
  have hW' := err_of_k (by intro q e; simp only [whnfAppE.k_loop1]; split <;> simp) (fun _ => rfl) hW
  have hS := hs.rel
  have hvn64 : vo.toNat + vn.toNat < 2 ^ 64 := by have := hva.bound; have := hS.spn; omega
  have hadd : (vo + vn).toNat = vo.toNat + vn.toNat := addW _ _ hvn64
  exact appLoopE_ref p hp hnv hI hiok n hk hkE F hF hn mode vis d hd vo ao an (spTop s₀.mem) args nodes
    dn fe eb s₀.mem hs.mode4 hs.eb_mode hhd har hno hlo (by rw [htop, hadd]; omega) hS.spn (n + 1)
    (Nat.le_refl _) a₀ s₀.mem v vn same i vargs MM hS hv hva htop (by rw [htop]; exact Nat.le_refl _)
    (fun _ _ => rfl) rfl er hW'

end appRef

section app
variable (p : Prog) (hp : WhnfCoreProg p) (hnv : closedNV p L.Checker.nvFns = true)
  (hI : IotaRecAtE p) (hiok : ∀ n, KnotUpTo p n → IotaRecAtOK p (n + 1))

include hp hnv hI hiok in
/-- **`whnf_core_app2`'s verdicts** are `whnf_app`'s. -/
theorem coreApp2_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d v h so sn : Word) (args nodes : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hv : HW v) (hh : HW h)
    (har : SpineR s₀.mem so sn args) (hno : SpineR s₀.mem (so + sn) sn nodes)
    (hlo : so.toNat + sn.toNat + sn.toNat ≤ (spTop s₀.mem).toNat)
    (htop : (spTop s₀.mem).toNat ≤ (s₀.mem.arr64 SPN).size) :
    CoreSpecE p (n + 1) "whnf_core_app2" [mode, vis, d, v, h, so, sn]
      (whnfCoreApp2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE v) (decE h)
        args nodes) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (coreApp2_specE p hp.capp2 (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d v h so sn) hc (Err.code_ne_of_cls hk0)
  simp only [coreApp2E] at hW
  have hS := hs.rel
  cases h3 : callE p n "head_and_args" [v] s₀.mem with
  | error e3 =>
    rw [h3, coreApp2E.k_head_and_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfAppE_nv "head_and_args" (by simp)) h3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  cases n with
  | zero =>
    obtain ⟨e', he', -⟩ := callE_zero p "head_and_args" [v] s₀.mem
    rw [h3] at he'; cases he'
  | succ n =>
  rw [h3] at hW
  simp only [coreApp2E.k_head_and_args] at hW
  have hW' := err_of_k (by intro q e; simp [coreApp2E.k_whnf_app]) (fun _ => rfl) hW
  obtain ⟨t₃, ht₃, -, hf₃, hg₃, hhw, ho3, htop3, xs, hha, hxs⟩ := triple_of_callE
    (headAndArgs_refines p hp.spine (n + 1) ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.1 v hv hS.spn htop) h3
  rw [ht₃] at hf₃ hg₃ htop3 hxs
  have hS₃ := hS.frame_stk hf₃ (by simp) (by simp)
  obtain ⟨hgt, hgsz, hgk, hgb, hgp⟩ := hg₃
  have har₃ := har.keep hgsz hgk (by omega) hS.spn
  have hno₃ := hno.keep hgsz hgk (by
    have hb := har.bound; have := hS.spn
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega) hS.spn
  have hvo : spTop m₃ = r₃.tail.headD 0 + r₃.tail.tail.headD 0 := by rw [htop3, ho3]
  have hsame : (if v = h then (1 : Word) else 0) = Cmp.evalW .eq v h := by
    simp [Cmp.evalW, Cmp.eval]
  rw [hsame] at hW'
  have hE := whnfApp_refinesE p hp hnv hI hiok n (hk.mono (by omega)) (hkE.mono (by omega)) F
    (by omega) (by omega) ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb
    mode d v (r₃.headD 0) (r₃.tail.headD 0) (r₃.tail.tail.headD 0) (Cmp.evalW .eq v h) so sn 0 xs
    args nodes ⟨hS₃, hs.mode4, hs.eb_mode⟩ hv hhw hxs hvo har₃ hno₃ (by rw [ho3]; omega)
  have hc4 := CoreSpecE.of_callE hE hW'
  rw [evalW_eq_ne v h hv hh] at hc4
  refine ErrClaim.of_run_eqW ?_ hc4
  simp only [whnfCoreApp2T, StateT.run_bind, hha, except_ok_bind]
  rfl

theorem coreAppT_err1 (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) (a : AState) (sp : EIdx × Array EIdx × Array EIdx)
    (hsp : (getAppSpine coreWalkFuel e).run a = .ok (sp, a)) (ce : CheckError)
    (h : (r.whnfCore cheap depth sp.1).run a = .error ce) :
    (whnfCoreAppT mode r fe cheap depth e).run a = .error ce := by
  rw [whnfCoreAppT_eq]
  simp only [StateT.run_bind, hsp, except_ok_bind, h]; rfl

theorem coreAppT_err2 (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) (a a₁ : AState) (sp : EIdx × Array EIdx × Array EIdx)
    (hsp : (getAppSpine coreWalkFuel e).run a = .ok (sp, a)) (v : EIdx)
    (hw : (r.whnfCore cheap depth sp.1).run a = .ok (v, a₁)) (ce : CheckError)
    (h : (whnfCoreApp2T mode r fe depth v sp.1 sp.2.1 sp.2.2).run a₁ = .error ce) :
    (whnfCoreAppT mode r fe cheap depth e).run a = .error ce := by
  rw [whnfCoreAppT_eq]
  simp only [StateT.run_bind, hsp, except_ok_bind, hw, h]

include hp hnv hI hiok in
/-- **`whnf_core_app`'s verdicts** are the head's `whnf_core` slot's and `whnf_core_app2`'s. -/
theorem coreApp_refinesE (N : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (F : Nat) (hF : N ≤ F)
    (hn : N ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpecE p (N + 1) "whnf_core_app" [mode, cheap, vis, d, e]
      (whnfCoreAppT (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat (decE e))
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (coreApp_specE p hp.capp (N + 1) ⟨s₀.mem, Locals.init []⟩
    mode cheap vis d e) hc (Err.code_ne_of_cls hk0)
  simp only [coreAppE] at hW
  have hS := hs.rel
  cases h1 : callE p N "get_app_spine" [e] s₀.mem with
  | error e1 =>
    rw [h1, coreAppE.k_get_app_spine.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfAppE_nv "get_app_spine" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [coreAppE.k_get_app_spine] at hW
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, hhw, ho1, htop1, xs, ns, hsp, hxs, hns⟩ := triple_of_callE
    (getAppSpine_refines p hp.spine N ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.1 e he hS.spn) h1
  rw [ht₁] at hf₁ hg₁ htop1 hxs hns
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  obtain ⟨hgt, hgsz, hgk, hgb, hgp⟩ := hg₁
  cases h2 : callE p N "whnf_core" [mode, cheap, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [h2, coreAppE.k_whnf_core.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => coreAppT_err1 _ _ _ _ _ _ a₀ _ hsp ce h')
      (CoreSpecE.of_callE ((hkE N (Nat.le_refl _)).whnfCore F ⟨m₁, Locals.init []⟩ a₀ dn vis fe MM eb
        mode cheap d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw) h2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  simp only [coreAppE.k_whnf_core] at hW
  have hW' := err_of_k (by intro q e; simp [coreAppE.k_whnf_core_app2]) (fun _ => rfl) hW
  have hslot := (hk N (Nat.le_refl _)).whnfCore F ⟨m₁, Locals.init []⟩ a₀ dn vis fe MM eb mode cheap
    d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hhw
  obtain ⟨hok₂, ⟨M', hS₂, hK₂, hSt₂⟩, hres₂, hrw₂⟩ := CoreSpec.of_callW hslot (callW_of_callE h2)
  cases N with
  | zero =>
    obtain ⟨e', he', -⟩ := callE_zero p "get_app_spine" [e] s₀.mem
    rw [h1] at he'; cases he'
  | succ n' =>
  have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hS₁.spn
  have hb1 := hxs.bound
  have hb2 := hns.bound
  have e1 : (r₁.tail.headD 0 + r₁.tail.tail.headD 0).toNat =
      (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat := addW _ _ (by omega)
  rw [e1] at hb2
  have htopN : (spTop m₁).toNat = (r₁.tail.headD 0).toNat + (r₁.tail.tail.headD 0).toNat +
      (r₁.tail.tail.headD 0).toNat := by
    rw [htop1, ← ho1, addW _ _ (by rw [e1]; omega), e1]
  have hxs₂ := hxs.keep hSt₂.size hSt₂.below (by omega) hspn₁
  have hns₂ := hns.keep hSt₂.size hSt₂.below (by rw [e1]; omega) hspn₁
  have happ := coreApp2_refinesE p hp hnv hI hiok n' (hk.mono (by omega)) (hkE.mono (by omega)) F
    (by omega) (by omega)
    ⟨m₂, Locals.init []⟩ _ dn vis fe M' eb mode d (r₂.headD 0) (r₁.headD 0) (r₁.tail.headD 0)
    (r₁.tail.tail.headD 0) xs ns ⟨hS₂, hs.mode4, hs.eb_mode⟩ hrw₂ hhw hxs₂ hns₂
    (by have h22 := hSt₂.1; simp only at h22 ⊢; rw [h22]; omega)
    (by show (spTop m₂).toNat ≤ (m₂.arr64 SPN).size
        have a := hSt₂.1; have b := hSt₂.size; simp only at a b; rw [a, b]; omega)
  have hrun₂ := AM.run_of_ok _ _ hok₂
  rw [hres₂] at hrun₂
  exact ErrClaim.of_run_err (fun ce h' => coreAppT_err2 _ _ _ _ _ _ a₀ _ _ hsp _ hrun₂ ce h')
    (CoreSpecE.of_callE happ hW')

end app

/-- **`CoreAppE`**: the `app` arm's error claim, from `iota_rec_at`'s (`IotaRecAtE`). -/
theorem coreAppE_of (p : Prog) (hp : WhnfCoreProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (hI : IotaRecAtE p) (hiok : ∀ n, KnotUpTo p n → IotaRecAtOK p (n + 1)) : CoreAppE p :=
  fun N hk hkE F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he =>
    coreApp_refinesE p hp hnv hI hiok N hk hkE F hF hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he

end L.Arena

