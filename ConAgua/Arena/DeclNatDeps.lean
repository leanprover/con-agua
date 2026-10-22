import ConAgua.Arena.DeclNatSpec

/-!
# `nat_op_deps` refines `natOpDeps` (lane `decls3`, helper `decls3-nat`)

Split from `DeclNatSpec.lean` for its `vcgen` spec's cost (fifteen branches, ten minutes).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section deps
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

def depsW (m : Mem) (c : Word) : List Word :=
  if c = pinW m 15 then [pinW m 15] else
  if c = pinW m 16 then [pinW m 16] else
  if c = pinW m 17 then [pinW m 15, pinW m 17] else
  if c = pinW m 18 then [pinW m 16, pinW m 18] else
  if c = pinW m 19 then [pinW m 16, pinW m 18, pinW m 19] else
  if c = pinW m 20 then [pinW m 20] else
  if c = pinW m 21 then [pinW m 21] else
  if c = pinW m 22 then [pinW m 15, pinW m 17, pinW m 21, pinW m 22] else
  if c = pinW m 23 then [pinW m 15, pinW m 17, pinW m 21, pinW m 23] else
  if c = pinW m 24 then [pinW m 21, pinW m 23, pinW m 24] else
  if c = pinW m 25 then [pinW m 16, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 25] else
  if c = pinW m 26 then [pinW m 16, pinW m 17, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 26] else
  if c = pinW m 27 then [pinW m 16, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 27] else
  if c = pinW m 28 then [pinW m 17, pinW m 18, pinW m 21, pinW m 28] else
  if c = pinW m 29 then [pinW m 17, pinW m 21, pinW m 22, pinW m 29] else
  []

/-- The word `j` of the pin record at `pi`. -/
def pw (m1 : Mem) (pi j : Word) : Word := rdW (m1.arr64 IW) (pi + j)

def natOpDepsW (p : Prog) (n : Nat) (m : Mem) (c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_op_pins" [] m) fun rp m1 =>
  let pi := rp.headD 0
  if c = pw m1 pi 0 then ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0))) else
  if c = pw m1 pi 1 then ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1))) else
  if c = pw m1 pi 2 then ntBW (callW p n "iw_alloc" [2] m1) fun rq mq => some ([rq.headD 0, 2], ((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2))) else
  if c = pw m1 pi 3 then ntBW (callW p n "iw_alloc" [2] m1) fun rq mq => some ([rq.headD 0, 2], ((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3))) else
  if c = pw m1 pi 4 then ntBW (callW p n "iw_alloc" [3] m1) fun rq mq => some ([rq.headD 0, 3], (((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 4))) else
  if c = pw m1 pi 5 then ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 5))) else
  if c = pw m1 pi 6 then ntBW (callW p n "iw_alloc" [1] m1) fun rq mq => some ([rq.headD 0, 1], (mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 6))) else
  if c = pw m1 pi 7 then ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7))) else
  if c = pw m1 pi 8 then ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 0)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 8))) else
  if c = pw m1 pi 9 then ntBW (callW p n "iw_alloc" [3] m1) fun rq mq => some ([rq.headD 0, 3], (((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 6)).set64 IW (rq.headD 0 + 1) (pw m1 pi 8)).set64 IW (rq.headD 0 + 2) (pw m1 pi 9))) else
  if c = pw m1 pi 10 then ntBW (callW p n "iw_alloc" [6] m1) fun rq mq => some ([rq.headD 0, 6], ((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7)).set64 IW (rq.headD 0 + 4) (pw m1 pi 8)).set64 IW (rq.headD 0 + 5) (pw m1 pi 10))) else
  if c = pw m1 pi 11 then ntBW (callW p n "iw_alloc" [7] m1) fun rq mq => some ([rq.headD 0, 7], (((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 2)).set64 IW (rq.headD 0 + 2) (pw m1 pi 3)).set64 IW (rq.headD 0 + 3) (pw m1 pi 6)).set64 IW (rq.headD 0 + 4) (pw m1 pi 7)).set64 IW (rq.headD 0 + 5) (pw m1 pi 8)).set64 IW (rq.headD 0 + 6) (pw m1 pi 11))) else
  if c = pw m1 pi 12 then ntBW (callW p n "iw_alloc" [6] m1) fun rq mq => some ([rq.headD 0, 6], ((((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 1)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 7)).set64 IW (rq.headD 0 + 4) (pw m1 pi 8)).set64 IW (rq.headD 0 + 5) (pw m1 pi 12))) else
  if c = pw m1 pi 13 then ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 2)).set64 IW (rq.headD 0 + 1) (pw m1 pi 3)).set64 IW (rq.headD 0 + 2) (pw m1 pi 6)).set64 IW (rq.headD 0 + 3) (pw m1 pi 13))) else
  if c = pw m1 pi 14 then ntBW (callW p n "iw_alloc" [4] m1) fun rq mq => some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0 + 0) (pw m1 pi 2)).set64 IW (rq.headD 0 + 1) (pw m1 pi 6)).set64 IW (rq.headD 0 + 2) (pw m1 pi 7)).set64 IW (rq.headD 0 + 3) (pw m1 pi 14))) else
  some ([0, 0], m1)

set_option maxHeartbeats 8000000 in
theorem natOpDeps_specW (p : Prog) (hp : p.lookup "nat_op_deps" = some natOpDepsL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_op_deps" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ natOpDepsW p n s₀.mem c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpDepsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "nat_op_pins", callW_spec p n "iw_alloc"] <;>
    finish (gen := 20) [natOpDepsW, ntBW, pw]

theorem pw_rec {m m1 : Mem} {pi : Word} {ws : List Word} (hI : IWOK m)
    (hrec : RecPost m m1 [pi] ws) (j : Nat) (hj : j < ws.length) :
    pw m1 pi (UInt64.ofNat j) = ws[j] := by
  obtain ⟨hq, hKeep, hroom, htop, hget⟩ := hrec
  have h1 := hget j hj
  have hpi : pi.toNat = iwTop m := by simp only [List.headD_cons] at hq; rw [hq]; rfl
  have hsz := hI.2.2.1
  have hj64 : (UInt64.ofNat j).toNat = j := by
    rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hj (by show ws.length ≤ 2 ^ 64; omega))]
  have hadd : (pi + UInt64.ofNat j).toNat = iwTop m + j := by
    rw [UInt64.toNat_add, hj64, hpi]; omega
  simp only [pw, rdW, hadd]
  have h2 := hget j hj
  rw [h2]
  simp [List.getElem?_eq_getElem hj]

theorem decI_inj_iff {κ : IdxKind} {x y : Word} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    ((decI x : Idx κ) = decI y) ↔ x = y :=
  ⟨fun e => (decI_eq_iff x hx _).mp e ▸ decI_word_self y hy, fun e => e ▸ rfl⟩

theorem natOpDeps_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) {c : Word}
    (hc : c.toNat < 2 ^ 32) :
    (natOpDeps (decI c)).run a = .ok ((depsW m c).map decI, a) := by
  simp [natOpDeps, StateT.run_bind, pinAt_run hF, exc_ok_bind', StateT.run_map,
decI_inj_iff hc (hF.names_lt 14 (by decide)),
    decI_inj_iff hc (hF.names_lt 15 (by decide)),
    decI_inj_iff hc (hF.names_lt 16 (by decide)),
    decI_inj_iff hc (hF.names_lt 17 (by decide)),
    decI_inj_iff hc (hF.names_lt 18 (by decide)),
    decI_inj_iff hc (hF.names_lt 19 (by decide)),
    decI_inj_iff hc (hF.names_lt 20 (by decide)),
    decI_inj_iff hc (hF.names_lt 21 (by decide)),
    decI_inj_iff hc (hF.names_lt 22 (by decide)),
    decI_inj_iff hc (hF.names_lt 23 (by decide)),
    decI_inj_iff hc (hF.names_lt 24 (by decide)),
    decI_inj_iff hc (hF.names_lt 25 (by decide)),
    decI_inj_iff hc (hF.names_lt 26 (by decide)),
    decI_inj_iff hc (hF.names_lt 27 (by decide)),
    decI_inj_iff hc (hF.names_lt 28 (by decide)), depsW]
  by_cases e1 : c = pinW m 15
  · simp only [if_pos e1]; rfl
  simp only [if_neg e1]
  by_cases e2 : c = pinW m 16
  · simp only [if_pos e2]; rfl
  simp only [if_neg e2]
  by_cases e3 : c = pinW m 17
  · simp only [if_pos e3]; rfl
  simp only [if_neg e3]
  by_cases e4 : c = pinW m 18
  · simp only [if_pos e4]; rfl
  simp only [if_neg e4]
  by_cases e5 : c = pinW m 19
  · simp only [if_pos e5]; rfl
  simp only [if_neg e5]
  by_cases e6 : c = pinW m 20
  · simp only [if_pos e6]; rfl
  simp only [if_neg e6]
  by_cases e7 : c = pinW m 21
  · simp only [if_pos e7]; rfl
  simp only [if_neg e7]
  by_cases e8 : c = pinW m 22
  · simp only [if_pos e8]; rfl
  simp only [if_neg e8]
  by_cases e9 : c = pinW m 23
  · simp only [if_pos e9]; rfl
  simp only [if_neg e9]
  by_cases e10 : c = pinW m 24
  · simp only [if_pos e10]; rfl
  simp only [if_neg e10]
  by_cases e11 : c = pinW m 25
  · simp only [if_pos e11]; rfl
  simp only [if_neg e11]
  by_cases e12 : c = pinW m 26
  · simp only [if_pos e12]; rfl
  simp only [if_neg e12]
  by_cases e13 : c = pinW m 27
  · simp only [if_pos e13]; rfl
  simp only [if_neg e13]
  by_cases e14 : c = pinW m 28
  · simp only [if_pos e14]; rfl
  simp only [if_neg e14]
  by_cases e15 : c = pinW m 29
  · simp only [if_pos e15]; rfl
  simp only [if_neg e15]
  rfl

theorem natOpDeps_ref (hN : NatGateProg p) (c : Word) :
    CallRef p "nat_op_deps" [c] (fun m a => StageR dn vis fe m a ∧ H c) (natOpDeps (decI c))
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => natOpDepsW p k mm c) (natOpDeps_specW p hN.lNatOpDeps k · c) hcall
  unfold natOpDepsW at hw
  cases hp : callW p k "nat_op_pins" [] m with
  | none => rw [hp] at hw; simp at hw
  | some qp =>
  obtain ⟨rp, m1⟩ := qp
  rw [hp, bW_some] at hw
  obtain ⟨h0, hrec, hPINS, hr⟩ := natOpPins_fref hN k m rp m1 hS.2 hp
  have hF := hS.1.pins.full h0
  have hS1 := hrec.2.1.stage hS
  have hg1 := hrec.2.1.1
  have hrec' : RecPost m m1 [rp.headD 0] (pinRecW m) := by rw [← hr]; exact hrec
  dsimp only at hw
  have v0 : pw m1 (rp.headD 0) 0 = pinW m 15 := pw_rec hS.2 hrec' 0 (by simp [pinRecW])
  have v1 : pw m1 (rp.headD 0) 1 = pinW m 16 := pw_rec hS.2 hrec' 1 (by simp [pinRecW])
  have v2 : pw m1 (rp.headD 0) 2 = pinW m 17 := pw_rec hS.2 hrec' 2 (by simp [pinRecW])
  have v3 : pw m1 (rp.headD 0) 3 = pinW m 18 := pw_rec hS.2 hrec' 3 (by simp [pinRecW])
  have v4 : pw m1 (rp.headD 0) 4 = pinW m 19 := pw_rec hS.2 hrec' 4 (by simp [pinRecW])
  have v5 : pw m1 (rp.headD 0) 5 = pinW m 20 := pw_rec hS.2 hrec' 5 (by simp [pinRecW])
  have v6 : pw m1 (rp.headD 0) 6 = pinW m 21 := pw_rec hS.2 hrec' 6 (by simp [pinRecW])
  have v7 : pw m1 (rp.headD 0) 7 = pinW m 22 := pw_rec hS.2 hrec' 7 (by simp [pinRecW])
  have v8 : pw m1 (rp.headD 0) 8 = pinW m 23 := pw_rec hS.2 hrec' 8 (by simp [pinRecW])
  have v9 : pw m1 (rp.headD 0) 9 = pinW m 24 := pw_rec hS.2 hrec' 9 (by simp [pinRecW])
  have v10 : pw m1 (rp.headD 0) 10 = pinW m 25 := pw_rec hS.2 hrec' 10 (by simp [pinRecW])
  have v11 : pw m1 (rp.headD 0) 11 = pinW m 26 := pw_rec hS.2 hrec' 11 (by simp [pinRecW])
  have v12 : pw m1 (rp.headD 0) 12 = pinW m 27 := pw_rec hS.2 hrec' 12 (by simp [pinRecW])
  have v13 : pw m1 (rp.headD 0) 13 = pinW m 28 := pw_rec hS.2 hrec' 13 (by simp [pinRecW])
  have v14 : pw m1 (rp.headD 0) 14 = pinW m 29 := pw_rec hS.2 hrec' 14 (by simp [pinRecW])
  rw [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] at hw
  refine ⟨_, a, natOpDeps_run hF hc, ?_⟩
  by_cases b1 : c = pinW m 15
  · rw [if_pos b1] at hw
    have hd : depsW m c = [pinW m 15] := by simp only [depsW, if_pos b1]
    rw [hd]
    cases hq : callW p k "iw_alloc" [1] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 15], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl
      · exact hF.names_lt 14 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 1) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b1] at hw
  by_cases b2 : c = pinW m 16
  · rw [if_pos b2] at hw
    have hd : depsW m c = [pinW m 16] := by simp only [depsW, if_neg b1, if_pos b2]
    rw [hd]
    cases hq : callW p k "iw_alloc" [1] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 16], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl
      · exact hF.names_lt 15 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 1) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b2] at hw
  by_cases b3 : c = pinW m 17
  · rw [if_pos b3] at hw
    have hd : depsW m c = [pinW m 15, pinW m 17] := by simp only [depsW, if_neg b1, if_neg b2, if_pos b3]
    rw [hd]
    cases hq : callW p k "iw_alloc" [2] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 15, pinW m 17], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hF.names_lt 14 (by decide)
      · exact hF.names_lt 16 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 2) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b3] at hw
  by_cases b4 : c = pinW m 18
  · rw [if_pos b4] at hw
    have hd : depsW m c = [pinW m 16, pinW m 18] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_pos b4]
    rw [hd]
    cases hq : callW p k "iw_alloc" [2] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 16, pinW m 18], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hF.names_lt 15 (by decide)
      · exact hF.names_lt 17 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 2) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b4] at hw
  by_cases b5 : c = pinW m 19
  · rw [if_pos b5] at hw
    have hd : depsW m c = [pinW m 16, pinW m 18, pinW m 19] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_pos b5]
    rw [hd]
    cases hq : callW p k "iw_alloc" [3] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 16, pinW m 18, pinW m 19], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hF.names_lt 15 (by decide)
      · exact hF.names_lt 17 (by decide)
      · exact hF.names_lt 18 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 3) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b5] at hw
  by_cases b6 : c = pinW m 20
  · rw [if_pos b6] at hw
    have hd : depsW m c = [pinW m 20] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_pos b6]
    rw [hd]
    cases hq : callW p k "iw_alloc" [1] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 20], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl
      · exact hF.names_lt 19 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 1) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b6] at hw
  by_cases b7 : c = pinW m 21
  · rw [if_pos b7] at hw
    have hd : depsW m c = [pinW m 21] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_pos b7]
    rw [hd]
    cases hq : callW p k "iw_alloc" [1] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 21], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl
      · exact hF.names_lt 20 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 1) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b7] at hw
  by_cases b8 : c = pinW m 22
  · rw [if_pos b8] at hw
    have hd : depsW m c = [pinW m 15, pinW m 17, pinW m 21, pinW m 22] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_pos b8]
    rw [hd]
    cases hq : callW p k "iw_alloc" [4] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 15, pinW m 17, pinW m 21, pinW m 22], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hF.names_lt 14 (by decide)
      · exact hF.names_lt 16 (by decide)
      · exact hF.names_lt 20 (by decide)
      · exact hF.names_lt 21 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 4) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b8] at hw
  by_cases b9 : c = pinW m 23
  · rw [if_pos b9] at hw
    have hd : depsW m c = [pinW m 15, pinW m 17, pinW m 21, pinW m 23] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_neg b8, if_pos b9]
    rw [hd]
    cases hq : callW p k "iw_alloc" [4] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 15, pinW m 17, pinW m 21, pinW m 23], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hF.names_lt 14 (by decide)
      · exact hF.names_lt 16 (by decide)
      · exact hF.names_lt 20 (by decide)
      · exact hF.names_lt 22 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 4) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b9] at hw
  by_cases b10 : c = pinW m 24
  · rw [if_pos b10] at hw
    have hd : depsW m c = [pinW m 21, pinW m 23, pinW m 24] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_neg b8, if_neg b9, if_pos b10]
    rw [hd]
    cases hq : callW p k "iw_alloc" [3] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 21, pinW m 23, pinW m 24], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hF.names_lt 20 (by decide)
      · exact hF.names_lt 22 (by decide)
      · exact hF.names_lt 23 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 3) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b10] at hw
  by_cases b11 : c = pinW m 25
  · rw [if_pos b11] at hw
    have hd : depsW m c = [pinW m 16, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 25] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_neg b8, if_neg b9, if_neg b10, if_pos b11]
    rw [hd]
    cases hq : callW p k "iw_alloc" [6] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 16, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 25], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hF.names_lt 15 (by decide)
      · exact hF.names_lt 17 (by decide)
      · exact hF.names_lt 20 (by decide)
      · exact hF.names_lt 21 (by decide)
      · exact hF.names_lt 22 (by decide)
      · exact hF.names_lt 24 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 6) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b11] at hw
  by_cases b12 : c = pinW m 26
  · rw [if_pos b12] at hw
    have hd : depsW m c = [pinW m 16, pinW m 17, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 26] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_neg b8, if_neg b9, if_neg b10, if_neg b11, if_pos b12]
    rw [hd]
    cases hq : callW p k "iw_alloc" [7] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 16, pinW m 17, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 26], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hF.names_lt 15 (by decide)
      · exact hF.names_lt 16 (by decide)
      · exact hF.names_lt 17 (by decide)
      · exact hF.names_lt 20 (by decide)
      · exact hF.names_lt 21 (by decide)
      · exact hF.names_lt 22 (by decide)
      · exact hF.names_lt 25 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 7) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b12] at hw
  by_cases b13 : c = pinW m 27
  · rw [if_pos b13] at hw
    have hd : depsW m c = [pinW m 16, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 27] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_neg b8, if_neg b9, if_neg b10, if_neg b11, if_neg b12, if_pos b13]
    rw [hd]
    cases hq : callW p k "iw_alloc" [6] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 16, pinW m 18, pinW m 21, pinW m 22, pinW m 23, pinW m 27], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hF.names_lt 15 (by decide)
      · exact hF.names_lt 17 (by decide)
      · exact hF.names_lt 20 (by decide)
      · exact hF.names_lt 21 (by decide)
      · exact hF.names_lt 22 (by decide)
      · exact hF.names_lt 26 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 6) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b13] at hw
  by_cases b14 : c = pinW m 28
  · rw [if_pos b14] at hw
    have hd : depsW m c = [pinW m 17, pinW m 18, pinW m 21, pinW m 28] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_neg b8, if_neg b9, if_neg b10, if_neg b11, if_neg b12, if_neg b13, if_pos b14]
    rw [hd]
    cases hq : callW p k "iw_alloc" [4] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 17, pinW m 18, pinW m 21, pinW m 28], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hF.names_lt 16 (by decide)
      · exact hF.names_lt 17 (by decide)
      · exact hF.names_lt 20 (by decide)
      · exact hF.names_lt 27 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 4) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b14] at hw
  by_cases b15 : c = pinW m 29
  · rw [if_pos b15] at hw
    have hd : depsW m c = [pinW m 17, pinW m 21, pinW m 22, pinW m 29] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_neg b8, if_neg b9, if_neg b10, if_neg b11, if_neg b12, if_neg b13, if_neg b14, if_pos b15]
    rw [hd]
    cases hq : callW p k "iw_alloc" [4] m1 with
    | none => rw [hq] at hw; simp at hw
    | some qq =>
    obtain ⟨rq, mq⟩ := qq
    rw [hq, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hlt : ∀ w ∈ [pinW m 17, pinW m 21, pinW m 22, pinW m 29], w.toNat < 2 ^ 32 := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hF.names_lt 16 (by decide)
      · exact hF.names_lt 20 (by decide)
      · exact hF.names_lt 21 (by decide)
      · exact hF.names_lt 28 (by decide)
    exact (emit_keep hN.lIwAlloc hS1 (N := 4) rfl hlt hq rfl (by simp [wrIW, UInt64.add_assoc])).of_grow hg1
  rw [if_neg b15] at hw
  have hd : depsW m c = [] := by simp only [depsW, if_neg b1, if_neg b2, if_neg b3, if_neg b4, if_neg b5, if_neg b6, if_neg b7, if_neg b8, if_neg b9, if_neg b10, if_neg b11, if_neg b12, if_neg b13, if_neg b14, if_neg b15]
  rw [hd]
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨hS1, hg1, ?_⟩
  simp [decRL, decHL, hslice?]

@[refines ConRon.Arena.natOpDeps]
theorem natOpDeps_refines (hN : NatGateProg p) (c : Word) :
    RefAM p "nat_op_deps" [c] (fun m a => StageR dn vis fe m a ∧ H c) (natOpDeps (decI c))
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) :=
  (natOpDeps_ref hN c).refAM

end deps

end L.Ind

