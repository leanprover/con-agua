module

public import ConAgua.Arena.IndRealCrF
public import ConAgua.Arena.IndSumSpec.StructElimLevel
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.Arena.IndRealFvtD
import ConAgua.Arena.IndMaster
import ConRon.Bridge.Grind
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# StructProjArgP: `ConRon.Arena.structProjArgP`, `ConRon.Arena.structProjPs`, `ConRon.Arena.structPsAt`

The refinement theorems `structProjArgP_refines`, `structPsAt_refines`, `structProjPs_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **Inverting a model continuation** (`K none = none`, `K (some (r, m)) = body r m`): a result
of `K o` comes from a result of `o`. Replaces `cases h : o | none => … | some …` blocks. -/
theorem kSome_inv {β γ : Type} {K : Option (β × Mem) → Option γ} {body : β → Mem → Option γ}
    {o : Option (β × Mem)} {y : γ} (h : K o = some y) (hn : K none = none)
    (hs : ∀ r m, K (some (r, m)) = body r m) : ∃ r m, o = some (r, m) ∧ body r m = some y := by
  rcases o with _ | ⟨r, m⟩
  · rw [hn] at h; cases h
  · exact ⟨r, m, rfl, hs r m ▸ h⟩

local notation "V" => ConLeche.CheckMode.verified

end L.Ind

namespace L.Ind

open L.Arena

/-! ## Slices, head first -/

/-- **A decoding slice of length `l ≥ 1`**: its head is the word at `o`, its tail decodes at
`o + 1`. -/
theorem decHL_cons {k : IdxKind} {m : Mem} {o l : Word} {xs : List (Idx k)}
    (h : decHL m o.toNat l.toNat = some xs) (hl : l ≠ 0) (hb : o.toNat + l.toNat < 2 ^ 64) :
    ∃ w xs', xs = decI w :: xs' ∧ rdW (m.arr64 IW) o = w ∧ w.toNat < 2 ^ 32 ∧
      decHL m (o + 1).toNat (l - 1).toNat = some xs' := by
  have hl1 : 1 ≤ l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
    · omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hlm : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hl1))]; simp
  rw [ho1, hlm]
  have hs : l.toNat = (l.toNat - 1) + 1 := by omega
  rw [hs] at h
  simp only [decHL] at h
  rw [hslice?_succ] at h
  cases hx : hd? (iwA m) o.toNat with
  | none => rw [hx] at h; cases h
  | some x =>
    cases ht : (hslice? (iwA m) (o.toNat + 1) (l.toNat - 1) : Option (List (Idx k))) with
    | none => rw [hx, ht] at h; cases h
    | some xs' =>
      rw [hx, ht] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW (m := m) (i := o.toNat) (x := x) hx (by omega)
      refine ⟨w, xs', by rw [← h, hw3], by simpa using hw1, hw2, ht⟩

/-! ## `field_doms_resolve`, `idx_args_resolve` -/

mutual
/-- After a recursive call: its first word. -/
def resK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

mutual
/-- After a recursive call: its first word. -/
def resK' : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (v o l : Word) (ra rb r : List Word)
theorem resK_some : resK (some (r, m)) = some ([r.headD 0], m) := rfl
theorem resK'_some : resK' (some (r, m)) = some ([r.headD 0], m) := rfl
end arms

grind_pattern [ind_grind] resK_some => resK (some (r, m))
grind_pattern [ind_grind] resK'_some => resK' (some (r, m))

section spec
variable (p : Prog)

end spec

/-! ## The relational lemmas -/

theorem toNat_succ_of_lt {o l : Word} (hb : o.toNat + l.toNat < 2 ^ 64) (hl : l ≠ 0) :
    (o + 1).toNat + (l - 1).toNat = o.toNat + l.toNat ∧ (o + 1).toNat = o.toNat + 1 := by
  have hl1 : 1 ≤ l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
    · omega
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hlm : (l - 1).toNat = l.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hl1))]; simp
  omega

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_proj_arg_p`: `t.j` -/

/-- After `mk_proj`. -/
def spaK2 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (e, m2) => some ([e], m2)
/-- After `intern_bvar`. -/
def spaK (T j : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (b, m1) => spaK2 (mkProjW m1 T j b)
/-- **The model of `struct_proj_arg_p`.** -/
def spaW (m : Mem) (T j : Word) : Option (List Word × Mem) := spaK T j (binternW m 0)

theorem spaK_some (T j b : Word) (m1 : Mem) : spaK T j (some (b, m1)) = spaK2 (mkProjW m1 T j b) := by rfl
theorem spaK2_some (e : Word) (m2 : Mem) : spaK2 (some (e, m2)) = some ([e], m2) := rfl
grind_pattern [ind_grind] spaK_some => spaK T j (some (b, m1))
grind_pattern [ind_grind] spaK2_some => spaK2 (some (e, m2))

theorem spaW_spec (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
    (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
    (hp : p.lookup "struct_proj_arg_p" = some structProjArgPL) (n : Nat) (s₀ : St) (T j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_arg_p" [T, j]
    ⦃fun r s' => LocEq s' s₀ ∧ spaW s₀.mem T j = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structProjArgPL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        internBVar_spec p hpf hpp hib n, mkProj_spec p hd hjf hjp hji hmp n] <;>
      finish [spaW]

/-- **`struct_proj_arg_p` refines `structProjArgP`** under the stage relation. -/
@[refines ConRon.Arena.structProjArgP]
theorem structProjArgP_refines (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hjf : p.lookup "proj_find" = some projFind) (hjp : p.lookup "proj_push" = some projPush)
    (hji : p.lookup "intern_proj" = some internProj) (hmp : p.lookup "mk_proj" = some mkProj)
    (hp : p.lookup "struct_proj_arg_p" = some structProjArgPL) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (T j : Word)
    (hS : StageR vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_arg_p" [T, j]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjArgP (decI T) j.toNat) a₀ ∧
      StageR vis fe s'.mem (AM.st (structProjArgP (decI T) j.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      AM.res (structProjArgP (decI T) j.toNat) a₀ = decE (r.headD 0); ⊤⦄ := by
  sorry

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_ps_at`, `struct_proj_ps`: the spine wrappers -/

/-- **The model of `struct_ps_at`** (the callee runs at the caller's fuel less one). -/
def psAtW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, o, nP => psK3 (psGoW n m o nP nP 0)

theorem psAtW_succ (n : Nat) (m : Mem) (o nP : Word) :
    psAtW (n + 1) m o nP = psK3 (psGoW n m o nP nP 0) := rfl
grind_pattern [ind_grind] psAtW_succ => psAtW (n + 1) m o nP

/-- **The model of `struct_proj_ps`.** -/
def projPsW : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | n + 1, m, nP => psK3 (psAtW n m 1 nP)

theorem projPsW_succ (n : Nat) (m : Mem) (nP : Word) :
    projPsW (n + 1) m nP = psK3 (psAtW n m 1 nP) := rfl
grind_pattern [ind_grind] projPsW_succ => projPsW (n + 1) m nP

section
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
  (hib : p.lookup "intern_bvar" = some internBVar)
  (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
  (hp : p.lookup "struct_ps_at" = some structPsAtL)
include ha hc hsc hpf hpp hib hg hp

theorem psAtW_spec (n : Nat) (s₀ : St) (o nP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_ps_at" [o, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ psAtW n s₀.mem o nP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, structPsAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        structPsAtGo_spec p ha hc hsc hpf hpp hib hg n] <;>
      finish

theorem projPsW_spec (hq : p.lookup "struct_proj_ps" = some structProjPsL) (n : Nat) (s₀ : St)
    (nP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_ps" [nP]
    ⦃fun r s' => LocEq s' s₀ ∧ projPsW n s₀.mem nP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq]
  simp only [callFn, structProjPsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        psAtW_spec p ha hc hsc hpf hpp hib hg hp n] <;>
      finish

end

/-- The model of `struct_ps_at` refines `structPsAt`. -/
theorem psAtW_ok (n : Nat) (m m' : Mem) (a : AState) (o nP : Word) (r : List Word)
    (h : psAtW n m o nP = some (r, m')) (hR : ArenaR m a) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hon : o.toNat + nP.toNat < 2 ^ 64) :
    ∃ xs a', (structPsAt o.toNat nP.toNat).run a = .ok (xs, a') ∧
      ArenaR m' a' ∧ IWGrow m m' ∧ (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  cases n with
  | zero => cases h
  | succ n =>
    rw [psAtW_succ] at h
    obtain ⟨r0, m0, hg, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [psK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨xs, a', hrun, hR', hgr, hs, hd, ht⟩ :=
      psGoW_ok n m m0 a o nP nP 0 r0 hg hR hsz hc hon (by simp)
    exact ⟨xs, a', by simpa [structPsAt] using hrun, hR', hgr, hs, by simpa using hd, by simpa using ht⟩

/-- **`struct_ps_at` refines `structPsAt`** under `ArenaR`. -/
@[refines ConRon.Arena.structPsAt]
theorem structPsAt_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
    (hp : p.lookup "struct_ps_at" = some structPsAtL) (n : Nat) (s₀ : St) (a₀ : AState)
    (o nP : Word) (hR : ArenaR s₀.mem a₀) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hc2 : 200 < (s₀.mem.arr64 CTL).size) (hon : o.toNat + nP.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_ps_at" [o, nP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structPsAt o.toNat nP.toNat) a₀ ∧
      ArenaR s'.mem (AM.st (structPsAt o.toNat nP.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structPsAt o.toNat nP.toNat) a₀); ⊤⦄ := by
  sorry

/-- **`struct_proj_ps` refines `structProjPs`** under `ArenaR`. -/
@[refines ConRon.Arena.structProjPs]
theorem structProjPs_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
    (hpf : p.lookup "bvar_find" = some bvarFind) (hpp : p.lookup "bvar_push" = some bvarPush)
    (hib : p.lookup "intern_bvar" = some internBVar)
    (hg : p.lookup "struct_ps_at_go" = some structPsAtGoL)
    (hp : p.lookup "struct_ps_at" = some structPsAtL)
    (hq : p.lookup "struct_proj_ps" = some structProjPsL) (n : Nat) (s₀ : St) (a₀ : AState)
    (nP : Word) (hR : ArenaR s₀.mem a₀) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hc2 : 200 < (s₀.mem.arr64 CTL).size) (hon : 1 + nP.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_proj_ps" [nP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (structProjPs nP.toNat) a₀ ∧
      ArenaR s'.mem (AM.st (structProjPs nP.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (AM.res (structProjPs nP.toNat) a₀); ⊤⦄ := by
  sorry

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `whnf_telescope` -/

local notation "V" => ConLeche.CheckMode.verified

/-! ### The twin, one level unfolded

`whnfTelescope` is structural recursion that matches under a bind, so Lean generates no equation
lemma for it (PLAN.md's vcgen gaps). `wtArm` is its body after the view, and `whnfTelescope_eq`
the unfolding, by `Nat.brecOn` and a case split on the view. -/

/-- The arms of `whnfTelescope` after the view. -/
def wtArm (mode : ConLeche.CheckMode) (fe : IFEnv) (i : Nat) (out : List EIdx) :
    ENodeView → Nat → AM (List EIdx × LIdx)
  | .sort s, 0 => pure (out, s)
  | .sort _, _ + 1 =>
    fail (.invalid "direct sum: type former does not reduce to a telescope                ")
  | .forallE _ _, 0 =>
    fail (.invalid "direct sum: type former does not reduce to a sort                 ")
  | .forallE dom body, n + 1 => do
      let fv ← internFVarE i dom
      let b ← instantiate1Fast coreWalkFuel body fv 0
      whnfTelescope mode fe (i + 1) n b (out ++ [dom])
  | _, 0 => fail (.invalid "direct sum: type former does not reduce to a sort                 ")
  | _, _ + 1 =>
    fail (.invalid "direct sum: type former does not reduce to a telescope                ")

theorem whnfTelescope_eq (mode : ConLeche.CheckMode) (fe : IFEnv) (i n : Nat) (e : EIdx)
    (out : List EIdx) :
    whnfTelescope mode fe i n e out = (do
      let e' ← whnf mode fe checkFuel i e
      let v ← view e'
      wtArm mode fe i out v n) := by
  sorry

end L.Ind

end
