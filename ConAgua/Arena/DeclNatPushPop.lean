module

public import ConAgua.Arena.IndInstallSpec.PapW
public import ConAgua.Arena.IndSumSpec.ConsSumCtors
import all ConAgua.Arena.Env

@[expose] public section

/-!
# A temporary push, popped (lane `ronsync2`, stage 3)

The definition arm's two gates (`check_structural_nat_pin`, `check_div_mod_pin`) read the
environment with the checked record pushed and pop it again: `env_row_get(n)` reads the own row
the push displaces, `env_push(vis, p)` pushes, the reads run at the pushed view, and
`env_pop_temp(w, n, c, q)` puts the row back (the twin's `fe.push ci`, then
`(fe.push ci).popTemp ci.name fe.idx[ci.name]?`, `IFEnv.popTemp`). `pushPop_stage` is the stage
relation across the pair, at any memory in between that kept the own rows.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **A push popped**: from the stage relation at `vis` before the push of record `pw` (name `nw`),
and the stage relation at the pushed view after reads that kept the own rows, `env_pop_temp` with
the own row read before the push gives the stage relation at `vis` of the twin's popped index. -/
theorem pushPop_stage {p : Prog} (hrs : p.lookup "env_row_set" = some envRowSetL)
    (hpu : p.lookup "env_push" = some envPushL) (hpt : p.lookup "env_pop_temp" = some envPopTempL)
    {k k' : Nat} {vis pw nw : Word} {fe : IFEnv} {a a2 : AState} {m m1 m2 m3 : Mem}
    {ci : IConstantInfo} {r1 r3 : List Word}
    (hS : StageR vis fe m a) (hci : decCI (erecP m) pw.toNat = some ci) (hnm : ci.name = decI nw)
    (hn : nw.toNat < 2 ^ 32)
    (h1 : callW p k "env_push" [vis, pw] m = some (r1, m1))
    (hS2 : StageR (r1.headD 0) (fe.push ci) m2 a2) (hg : IWGrow m m2) (hO : ownC m2 = ownC m1)
    (h3 : callW p k' "env_pop_temp" [r1.headD 0, nw, (ownRaw m nw).1, (ownRaw m nw).2] m2 =
      some (r3, m3)) :
    StageR (r3.headD 0) ((fe.push ci).popTemp ci.name fe.idx[ci.name]?) m3 a2 ∧ IWGrow m2 m3 ∧
      r3.headD 0 = vis := by
  have hE := hS.check.env
  have hwn : (decI nw : NIdx).word.toUInt64 = nw := decI_word_self nw hn
  obtain ⟨hO1, hr1, hv1⟩ := envPush_ownC hrs hpu h1 hE hci
  have hvis1 : (vis + 1).toNat = vis.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hprev := rec3PrevD_grow hg (rec3PrevD hE hn)
  obtain ⟨hpvE, hcd⟩ := prevD_eq hprev
  have hown : ∀ n' : NIdx, (ownRaw m2 n'.word.toUInt64).1 = updC (ownC m) ci.name (vis + 1) n' := by
    intro n'; rw [← hO1, ← hO]; rfl
  have hcC : (ownRaw m nw).1 = ownC m ci.name := by rw [hnm]; simp only [ownC, hwn]
  rw [hr1, List.headD_cons] at h3 hS2
  obtain ⟨s3, hs3, -, hr3, hE3, hm3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (envPopTemp_refines p hrs hpt k' _ (vis + 1) nw (ownRaw m nw).1 (ownRaw m nw).2 hS2.check.env hn
      (fun e => by have := congrArg UInt64.toNat e; rw [hvis1] at this; simp at this)
      (by have := hown ci.name; rw [hnm, hwn] at this; rw [this]; simp [updC])
      (ownRaw_fst_lt m nw)
      (fun hc0 => by
        have := hE.fresh (decI nw) (by rw [hwn]; exact hc0)
        rw [hwn] at this; rw [hvis1]; omega)
      hcd
      (fun hc0 n' hn' e => by
        rw [hown n'] at e
        have hne : n' ≠ ci.name := fun h => hn' (by rw [h, hnm, hwn])
        simp only [updC, if_neg hne] at e
        exact hne (hE.uniq n' ci.name (by simp only [ownC] at e; rw [e]; exact hc0)
          (by simp only [ownC] at e; rw [e, hcC]; rfl))))
    h3
  rw [hpvE, ← hnm, hm3] at hE3
  have hm3' : m3 = ownSet m2 nw (ownRaw m nw).1 (ownRaw m nw).2 := by rw [← hs3, hm3]
  subst hm3'
  obtain ⟨hS3, hg3⟩ := StageR.of_own hS2 hE3
  rw [hr3, List.headD_cons, show vis + 1 - 1 = vis by simp] at *
  exact ⟨hS3, hg3, rfl⟩

end L.Ind
