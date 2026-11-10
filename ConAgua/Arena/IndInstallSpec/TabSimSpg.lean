module

public import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
public import ConAgua.Arena.IndSumSpec.StructProjBodies
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.WhnfCoreProj
public import ConAgua.Arena.IndPartsSpec.MemberNames

@[expose] public section

/-!
# TabSimSpg

`binternW_mfr`, `minternW_mfr`, `mkProjW_mfr`, `erAllocW_mfr`, `set64ER_mfr` and the lemmas only they use.
-/

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem binternW_mfr {m m' : Mem} {u r : Word} (h : binternW m u = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (binternW_frame m u r m' h) (by simp [tier1, BREC, BSLOT]) (by simp)
theorem minternW_mfr {m m' : Mem} {u v r : Word} (h : minternW m u v = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (minternW_frame m u v r m' h) (by simp [tier1, MREC, MSLOT, MHP]) (by simp)
theorem mkProjW_mfr {m m' : Mem} {a b c r : Word} (h : mkProjW m a b c = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low (mkProjW_low h)
theorem erAllocW_mfr {m m' : Mem} {k q : Word} (h : erAllocW m k = some (q, m')) : MFr [] [] m m' := by
  have hm : m' = erAllocMem m k := by
    unfold erAllocW at h; split at h <;> (repeat' split at h) <;> simp_all
  subst hm; unfold erAllocMem; split
  · exact MFr.of_frame (MemFrame.setCtl m 129 _) (by simp) (by simp)
  · exact MFr.of_frame (MemFrame.setCtl m 130 _) (by simp) (by simp)

theorem set64ER_mfr (m : Mem) (k v : Word) : MFr [] [] m (m.set64 EREC k v) :=
  MFr.of_frame (MemFrame.set64 m EREC (by decide) k v) (by simp [EREC]) (by simp)

/-! ## `check_struct_proj_table` -/

theorem lpsW_mfrT {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : lpsW n m q = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    simp only [lpsW] at h
    mfr_auto h [erToIwW_mfr]

theorem psGoW_mfr : ∀ (n : Nat) (m m' : Mem) (o nP N k : Word) (r : List Word),
    psGoW n m o nP N k = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, h => by simp [psGoW] at h
  | n + 1, m, m', o, nP, N, k, r, h => by
    simp only [psGoW, psK0.eq_def, psK1.eq_def, psK2.eq_def, psK3.eq_def] at h
    mfr_auto h [psGoW_mfr n _ _ _ _ _ _ _, binternW_mfr, allocW_mfr, consW_mfr]

theorem projPsW_mfr {n : Nat} {m m' : Mem} {nP : Word} {r : List Word} (h : projPsW n m nP = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [projPsW] at h
  | succ n =>
    cases n with
    | zero => simp [projPsW, psAtW, psK3] at h
    | succ n =>
      simp only [projPsW, psAtW, psK3.eq_def] at h
      cases h1 : psGoW n m 1 nP nP 0 with
      | none => simp [h1] at h
      | some x =>
        obtain ⟨r1, m1⟩ := x
        simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact psGoW_mfr _ _ _ _ _ _ _ _ h1

theorem spaW_mfr {m m' : Mem} {T j : Word} {r : List Word} (h : spaW m T j = some (r, m')) : MFr [] [] m m' := by
  simp only [spaW, spaK.eq_def, spaK2.eq_def] at h
  mfr_auto h [binternW_mfr, mkProjW_mfr]

theorem i1lF_mfr {m m' : Mem} {args r : List Word} (h : i1lF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low ⟨_, _, i1lF_frame h, lt64A_of_all rfl, lt64_of_all rfl⟩

theorem ipalF_mfr {m m' : Mem} {args r : List Word} (h : ipalF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_low ⟨_, _, ipalF_frame h, lt64A_of_all rfl, lt64_of_all rfl⟩

theorem pbW_mfr : ∀ (n : Nat) (m m' : Mem) (T k i h : Word) (r : List Word),
    pbW n m T k i h = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, hh => by rw [pbW.eq_1] at hh; cases hh
  | n + 1, m, m', T, k, i, h, r, hh => by
    simp only [pbW.eq_2, pbW.k_struct_proj_arg_p.eq_def, pbW.k_instantiate1_lift_fast.eq_def,
      pbW.k_struct_proj_bodies_go.eq_def, pbW.k_sl_cons.eq_def] at hh
    mfr_auto hh [pbW_mfr n _ _ _ _ _ _ _, spaW_mfr, i1lF_mfr, consW_mfr]

theorem spbW_mfr {k : Nat} {m m' : Mem} {T nP nF cty : Word} {r : List Word}
    (h : spbW k m T nP nF cty = some (r, m')) : MFr [] [] m m' := by
  cases k with
  | zero => simp [spbW] at h
  | succ k =>
    simp only [spbW, spbK1.eq_def, spbK2.eq_def, spbK3.eq_def] at h
    mfr_auto h [projPsW_mfr, ipalF_mfr, pbW_mfr _ _ _ _ _ _ _ _]

theorem crfF_mfr {m m' : Mem} {args r : List Word} (h : crfF m args = some (r, m')) : MFr [] [] m m' :=
  MFr.of_frame (crfF_frame h)
    (fun b hb => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; subst hb; decide))
    (fun x hx => .inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> decide))

/-- `sctW`'s frame, from its reading `c` of `all_level_params_defined`'s (`sctW_mfr_stub`: the stub's). -/
theorem sctW_mfr {c : CallM}
    (hc : ∀ (k : Nat) (args : List Word) (m m' : Mem) (r : List Word),
      c k "all_level_params_defined" args m = some (r, m') → MFr [] [] m m') :
    ∀ (n : Nat) (m m' : Mem) (vis nP lo ll bO bL : Word) (r : List Word),
    sctW c n m vis nP lo ll bO bL = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [sctW] at h
  | n + 1, m, m', vis, nP, lo, ll, bO, bL, r, h => by
    simp only [sctW, sctW.k_has_fvar_fast.eq_def, sctW.k_all_level_params_defined.eq_def,
      sctW.k_consts_resolve_ffast.eq_def, sctW.k_loose_bvars_bounded_fast.eq_def,
      sctW.k_check_struct_proj_table_scoped.eq_def] at h
    mfr_auto h [sctW_mfr hc n _ _ _ _ _ _ _ _ _, hc _ _ _ _ _, crfF_mfr, MFr.ofHffF, MFr.ofLbbF]

theorem wrER_mfr (ws : List Word) (m : Mem) (q : Word) : MFr [] [] m (wrER m q ws) :=
  MFr.of_frame (wrER_frame ws m q) (by simp [EREC]) (by simp)

end L.Ind

end
