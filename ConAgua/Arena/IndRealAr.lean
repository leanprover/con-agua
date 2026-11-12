module

public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.ArRangeSpec
import ConAgua.Arena.ArRangeRefine
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.CallF
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `ar_entry` under the stage relation and the walk memos (lane `ronsync3`)

`ar_entry(e, d, k, c)` (`ArRangeSpec.lean`, con-ron's `abstractRangeFast coreWalkFuel`) refines
under `ArenaA` (`arEntry_refines`); its memo is the `abstract1` memo (`ABMEMO`, `CTL[48]`), which
`AbsOK`'s `AbMemo` holds, so the walk is `abstract1_fast`'s case (`IndRealAbs.lean`'s `abF_ok`)
with the range walk in place of the one-variable walk. The one-pass closers
(`close_telescope_go`, `close_lams_go`, `abstract_prefix`) call it.

* **The model** `arF := callF arProg "ar_entry"`, write set `absA`/`absC` (below 64).
* **`arF_ok`**: `RelW arF [e, d, k, c] (StageR ∧ AbsOK) (abstractRangeFast coreWalkFuel …)
  (KeepPost … ∧ AbsOK)`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The program bundle. -/
abbrev ArF (p : Prog) : Prop := ProgHas p arProg

/-- **The model of `ar_entry`** (program- and fuel-free). -/
noncomputable def arF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF arProg "ar_entry" m args

theorem arF_spec (p : Prog) (hp : ArF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_entry" args
    ⦃fun r s' => LocEq s' s₀ ∧ arF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec arProg_closed (hp.agree arFns) (by decide) n s₀ args

/-- `ar_entry` writes only the `abstract1` memo, the `fvarRange` memo and the store. -/
theorem arF_frame {m m' : Mem} {args r : List Word} (h : arF m args = some (r, m')) :
    MemFrame absA absC m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame arProg_closed (by decide) (run_of_callW hc)).1

theorem arProg_ar : ArProg arProg := (ProgHas.refl arProg).left.left

theorem arProg_entry : arProg.lookup "ar_entry" = some arEntry := (ProgHas.refl arProg).get "ar_entry"

/-- **`ar_entry` refines `abstractRangeFast coreWalkFuel` under the stage relation and a
well-formed `abstract1` memo**; the memo is well formed after. -/
theorem arF_ok (_dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e d k c : Word)
    (he : H e) :
    RelW arF [e, d, k, c] (fun m a => StageR vis fe m a ∧ AbsOK m)
      (abstractRangeFast coreWalkFuel (decI e) d.toNat k.toNat c.toNat)
      (fun m m' a r x => KeepPost vis fe decW0E m m' a r x ∧ AbsOK m') := by
  intro m m' a r h ⟨hS, ⟨mp, hmp⟩, hI1, hCr, hIl, hWk, ⟨hp, hhp⟩⟩
  have hfr := arF_frame h
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  by_cases hk : k = 0
  · obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (arEntry_spec arProg arProg_ar arProg_entry n _ e d k c) hc
    rw [arEntryW_zero n m e d k c hk, hs'] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hk0 : k.toNat = 0 := by rw [hk]; rfl
    refine ⟨decE e, a, by simp [abstractRangeFast, hk0]; rfl,
      ⟨hS, IWGrow.refl _, by rw [← hr]; exact mask_lt e, by rw [← hr]; exact decI_mask e⟩,
      ⟨⟨mp, hmp⟩, hI1, hCr, hIl, hWk, ⟨hp, hhp⟩⟩⟩
  have hk' : k.toNat ≠ 0 := fun e => hk (UInt64.toNat_inj.mp e)
  have hA : ArenaA m { a with memos := { a.memos with abs1C := mp } } :=
    ⟨hS.check.arena.memo_irrel a.memos.instLC mp, hmp⟩
  obtain ⟨s'', hs'', -, hok, hA', hres, hlt⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (arEntry_refines arProg arProg_ar arProg_entry n _ _ hA e d k c he) hc
  rw [hs''] at hA'
  have hrun := AM.run_of_ok _ _ hok
  have hrun' : (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat).run a =
      .ok (AM.res (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat)
          { a with memos := { a.memos with abs1C := mp } },
        AM.st (abstractRangeFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat)
          { a with memos := { a.memos with abs1C := mp } }) := by
    rw [← hrun, arFast_run _ _ _ _ _ hk', arFast_run _ _ _ _ _ hk']; rfl
  have hcp := (keepsW_arFast coreWalkFuel (decE e) d.toNat k.toNat c.toNat).cp_of_cpl.run hrun'
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hA'.1 hfr (lt64A_of_all rfl) (lt64_of_all rfl) hcp
  exact ⟨_, _, hrun', ⟨hS', hg, hlt, hres.symm⟩, ⟨_, hA'.2⟩,
    hI1.frame hfr (by decide) (by decide), hCr.frame hfr (by decide) (by decide),
    hIl.frame hfr (by decide) (by decide),
    hWk.frame hfr (by decide) (by decide) (by decide) (by decide) (by decide),
    ⟨hp, hbMR_frame hfr (by decide) (by decide) hhp⟩⟩

end L.Ind
