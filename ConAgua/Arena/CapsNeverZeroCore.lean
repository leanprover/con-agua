import ConAgua.Arena.PropReadRefine

/-!
# `caps_never_zero` under `CoreS` (lane `defeq2`)

`CapsNeverZeroOK` (`WhnfIota.lean`), a `KnotCallees` field until now, from the model's refinement
`capsNeverZeroW_ok` (helper `whnf3-lp`, at `ArenaD`). What `CoreS` did not give before:

* the universe arguments `us` read back: `caps_never_zero` calls `ls_node(us)`, which aborts on a
  handle that is not stored, so a run that returns has a stored list (`lsNodeW_view`), and
  `StoreDen.lsAll` reads it back;
* the `PropWhen` datum's names related by the name store (`PWR (nameN ns)`) rather than by the
  record decoder `dn` (`decPWw`): `StoreDen.dnN`;
* the level parameters read back: a hypothesis of `CapsNeverZeroOK` (its caller's constant is
  found in the environment, `StoreDen.constLps`).

The run writes the level heap and the spine stack above its top (`CoreS.frame_lhs`), and the
twin's two readback caches (`CoreS.readCaches`).
-/

open ConRon.Arena
open ConLeche
open Std.WP

namespace L.Arena

/-- **The relation across a writer of the level heap and the spine stack** (`LH`, `SPN`,
`CTL` 192 and 136). -/
theorem CoreS.frame_lhs {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (hf : MemFrame [LH, SPN] [192, 136] m m') : CoreS dn m' a vis fe M eb := by
  have hA64 : ∀ b ∈ [LH, SPN], 64 ≤ b ∧ b < 256 := by decide
  have hC2 : ∀ x ∈ ([192, 136] : List Word), x = 192 ∨ x = 136 := by simp
  have hC64 : ∀ x ∈ ([192, 136] : List Word), 64 ≤ x.toNat := fun x hx => by
    rcases hC2 x hx with rfl | rfl <;> simp
  have aC : ∀ lo hi : Nat, hi ≤ 136 → AvoidC lo hi [192, 136] := fun lo hi h x hx => by
    right; rcases hC2 x hx with rfl | rfl <;> simp <;> omega
  exact ⟨⟨ArenaR.frame_ext _ _ hA64 hC64 m m' hf a hS.arena.1,
      DerR.frameM _ _ m m' hf (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl <;> decide) a hS.arena.2⟩,
    hS.core.frame (by decide) (aC 96 128 (by omega)) hf,
    hS.pins.congr (hf.1 PINS (by decide) (by decide)),
    hS.env.frame (by decide) (aC 128 136 (by omega)) hf,
    hS.readL, hS.readLs, hS.nwf, hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
    hS.memos.frame_hi hf hA64 hC64 (by decide) (fun x hx => by
      rcases hC2 x hx with rfl | rfl <;> simp),
    hf.2.2.1 145 ▸ hS.bstk,
    hS.den.frameE (hf.1 EREC (by decide) (by decide)), hS.mode.frame hf (by decide) (by decide)⟩

/-- A writer of the level heap and of the spine stack above its top, the top put back, keeps
the stack. -/
theorem StackKept.of_lhsFrame {m m' : Mem} (hf : MemFrame [LH, SPN] [192, 136] m m')
    (ht : spTop m' = spTop m) (hb : ∀ i : Word, i < spTop m → spW m' i = spW m i) :
    StackKept m m' :=
  ⟨ht, hf.2.2.1 SPN, hb, BKept.of_frame hf (by decide) (by decide),
    PoolGrew.of_frame hf (by decide) (by decide)⟩

theorem mapM_of_sub {f g : NIdx → Option Name} (hfg : ∀ k x, f k = some x → g k = some x) :
    ∀ (l : List NIdx) (xs : List Name), l.mapM f = some xs → l.mapM g = some xs
  | [], xs, h => by simpa using h
  | y :: ys, xs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨z, hz, zs, hzs, rfl⟩ := h
    exact ⟨z, hfg _ _ hz, zs, mapM_of_sub hfg ys zs hzs, rfl⟩

/-- A slice of the record pool that reads back has no wrapping offset. -/
theorem hslice_noWrap {k : IdxKind} {a : Array Word} (ha : a.size < 2 ^ 63) {o c : Word}
    {l : List (Idx k)} (h : hslice? a o.toNat c.toNat = some l) : o.toNat + c.toNat < 2 ^ 64 := by
  rcases hslice?_bound_fsz _ _ _ _ h with h0 | h0
  · have := o.toNat_lt; omega
  · omega

/-- **The `PropWhen` datum at its words**, related by the name store: its names decode by `dn`,
which agrees with the store (`StoreDen.dnN`). -/
theorem pwR_of_decPWw {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    (hd : StoreDen dn m a fe) (he : (m.arr64 EREC).size < 2 ^ 63) {swd so sc : Word}
    {pw : PropWhen} (h : decPWw (m.arr64 EREC) dn swd so sc = some pw) :
    PWR (nameN a.store.lss.ls.ns) m EREC swd so sc pw := by
  by_cases h0 : swd.toNat = 0
  · simp only [decPWw, h0, Option.some.injEq] at h
    subst h
    exact .inl ⟨UInt64.toNat_inj.mp (by rw [h0]; rfl), rfl⟩
  by_cases h1 : swd.toNat = 1
  · simp only [decPWw, h1, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨l, hl, ps, hps, rfl⟩ := h
    refine .inr ⟨fun e => by rw [e] at h0; exact h0 rfl, ps, rfl, ?_⟩
    exact lp_nmsR_of_hslice _ m EREC l ps so sc hl (hslice_noWrap he hl)
      (mapM_of_sub hd.dnN l ps hps)
  · unfold decPWw at h
    split at h <;> first | omega | cases h

/-- **`caps_never_zero` refines `capsNeverZeroPW`** under `CoreS`: `CapsNeverZeroOK`. -/
theorem capsNeverZeroOK_of (p : Prog) (hL : LvSubProg p) : CapsNeverZeroOK p := by
  intro n s₀ a₀ dn vis fe MM eb po pc us swd so sc lps pw hS hus hlps hks hpw
  obtain ⟨ks, hks⟩ := hks
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun
    (capsNeverZero_spec p hL n s₀ po pc us swd so sc)
  subst hs
  refine ⟨hloc, ?_⟩
  -- `ls_node(us)` returned: `us` is stored, so it reads back
  have hne : lsNodeW s.mem us ≠ [] := by
    intro e
    cases n with
    | zero => simp [capsNeverZeroW] at hW
    | succ n => simp [capsNeverZeroW, e] at hW
  obtain ⟨vs, hdl⟩ := hS.den.lsAll _ (by
    obtain ⟨ids, e, -⟩ := lsNodeW_view hS.arena.1 hus hne; rw [e]; rfl)
  have hk := lp_nmsR_of_hslice a₀.store.lss.ls.ns s.mem EREC lps ks po pc hlps
    (hslice_noWrap hS.erec hlps) hks
  have hp := pwR_of_decPWw hS.den hS.erec hpw
  obtain ⟨hA', hf, htop, hbel, hx, hlt⟩ := capsNeverZeroW_ok n s.mem s'.mem a₀ po pc us swd so sc
    (r.headD 0) ks vs pw hS.arena hS.nwf hus hS.spn hdl hk hp hW
  -- the twin's two readbacks
  obtain ⟨X, hX, hcX⟩ := pr_readNamesM_run lps a₀ ks hks hS.den.readN
  obtain ⟨Y, hY, hcY⟩ := readLevelsM_run' { a₀ with caches := { a₀.caches with readNC := X } }
    (decI us) vs hdl (by exact hS.readLs)
  have hb : (Level.substPW ks vs pw).isNever = (r.headD 0 != 0) := by
    cases h : (Level.substPW ks vs pw).isNever
    · rw [h] at hx
      have h0 : r.headD 0 = 0 := Classical.byContradiction fun h0 => by have := Eq.mp hx h0; cases this
      rw [h0]; rfl
    · rw [h] at hx
      have h0 : r.headD 0 ≠ 0 := Eq.mpr hx rfl
      exact (bne_iff_ne.mpr h0).symm
  have hrun : (capsNeverZeroPW lps (decI us) pw).run a₀ =
      .ok (r.headD 0 != 0, { a₀ with caches := { a₀.caches with readNC := X, readLsC := Y } }) := by
    simp only [capsNeverZeroPW, StateT.run_bind, hX, except_ok_bind, hY, hb]
    rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, by rw [hres]; rfl, hlt⟩
  rw [hst]
  exact ⟨MM, CoreS.readCaches (hS.frame_lhs hf) X Y (by exact hcY) hcX, KeptAll.refl _ _,
    StackKept.of_lhsFrame hf htop hbel⟩

end L.Arena
