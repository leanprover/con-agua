module

public import ConAgua.Arena.JustifyRef4
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# `cone_entry` and `cone_go` refine the twin's (lane compare, helper compare-cone)

`cone_entry(w, vis)`: the input's constant (`env_find`), the solution's (`sol_find`), the
comparison (`refines_b`), the tables (`find_table`, `sol_find_table`, `tbl_beq_p`), then what the
name reads (`entry_needs`). `cone_go(f, vis)`: the loop over the stack `CWK`, each name looked up
in the memo `csSch` (`cs_find`), compared (`cone_entry`), recorded (`cs_put`), and what it reads
pushed (`cone_push`), against the twin's recursion `coneGo`.
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind L.Stubs

/-! ## `cone_push` -/

/-- **`cone_push()` is the cited `ns ++ work`**: the needs walk's names `NACC[0‥CTL[227])` on top
of the stack, `NACC[0]` the new top; only the stack and its top written. -/
theorem conePush_ok {p : Prog} (hp : p.lookup "cone_push" = some conePushL) {n : Nat} {m m' : Mem}
    {r : List Word} {seen : Std.HashMap NIdx Bool} {work : List NIdx} {x : NeedsSt}
    (h : callW p n "cone_push" [] m = some (r, m')) (hC : CnR m seen work) (hx : NdR m x) :
    CnR m' seen (x.acc ++ work) ∧ MemFrame [CWK] [CTOPC] m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (conePush_specW p hp n _) h
  rcases n with _ | n
  · rw [conePushW.eq_1] at hW; cases hW
  rw [conePushW.arm1] at hW
  cases e : conePushW.loop1 (n + 1) m (rdW (m.arr64 CTL) NTOPC) (rdW (m.arr64 CTL) CTOPC) with
  | none => rw [e, conePushW.k_loop1.none] at hW; cases hW
  | some q =>
  obtain ⟨h', m1⟩ := q
  rw [e, conePushW.k_loop1.arm1] at hW
  obtain ⟨-, e'⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [← e']
  obtain ⟨eh, hf, hro, hrd⟩ := conePush_loop (n + 1) m _ _ h' m1 e
  have hsz : CTOPC.toNat < (m1.arr64 CTL).size := by rw [hf.size]; exact hC.ctl
  have htop : ctlW (m1.set64 CTL CTOPC h') CTOPC = h' := by
    simp only [ctlW, rdW_set64, hsz, and_self, ite_true]
  have hf2 : MemFrame [CWK] [CTOPC] m (m1.set64 CTL CTOPC h') :=
    (hf.mono (fun _ h => h) (by simp)).trans (MemFrame.setCtl m1 CTOPC h' |>.mono (by simp) (fun _ h => h))
  have hWk : (m1.set64 CTL CTOPC h').arr64 CWK = m1.arr64 CWK := (MemFrame.setCtl m1 CTOPC h').arr _ (by simp) (by decide)
  generalize hK : (rdW (m.arr64 CTL) NTOPC).toNat = K at eh hrd
  generalize hH : (rdW (m.arr64 CTL) CTOPC).toNat = H at eh hrd hro
  have hacc := hx.rel.acc
  have hwork := hC.rel.work
  have hlenA : x.acc.length = K := by rw [← hacc]; simp [naccList, ctlW, hK]
  have hlenW : work.length = H := by rw [← hwork]; simp [cwkList, ctlW, hH]
  refine ⟨⟨⟨memoRG_frame csSch csSch_wf nmKey _ [CWK] [CTOPC] (by decide) (by decide) _ _ hf2 _ hC.rel.seen,
    ?_, ?_, ?_⟩, by rw [Mem.size64_set64, hf.size]; exact hC.ctl⟩, hf2⟩
  · apply List.ext_getElem
    · simp [cwkList, htop, eh, hlenA, hlenW]; omega
    intro j h1 h2
    have h2' : j < K + H := by simpa [hlenA, hlenW] using h2
    simp only [cwkList, htop, hWk, List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.length_range] at h1 ⊢
    rw [eh] at h1 ⊢
    rw [hrd]
    by_cases hj : j < K
    · rw [List.getElem_append_left (by rw [hlenA]; exact hj)]
      have c : H ≤ H + K - 1 - j ∧ H + K - 1 - j < H + K := by omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true c), show K - 1 - (H + K - 1 - j - H) = j by omega]
      have : x.acc[j]'(by omega) = (naccList m)[j]'(by rw [hacc, hlenA]; exact hj) := by
        simp only [hacc]
      rw [this]; simp [naccList]
    · rw [List.getElem_append_right (by rw [hlenA]; omega)]
      have c : ¬ (H ≤ H + K - 1 - j ∧ H + K - 1 - j < H + K) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false c)]
      have : work[j - x.acc.length]'(by rw [hlenA, hlenW]; omega) =
          (cwkList m)[j - K]'(by rw [hwork, hlenW]; omega) := by
        simp only [hwork, hlenA]
      rw [this]
      simp only [cwkList, ctlW, hH, List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range]
      congr 2; omega
  · intro i hi
    have htop' : rdW ((m1.set64 CTL CTOPC h').arr64 CTL) CTOPC = h' := htop
    simp only [ctlW, htop', eh] at hi
    rw [hWk, hrd]
    split
    · exact hx.rel.words _ (by simp only [ctlW, hK]; omega)
    · exact hC.rel.words _ (by simp only [ctlW, hH]; omega)
  · have htop' : rdW ((m1.set64 CTL CTOPC h').arr64 CTL) CTOPC = h' := htop
    simp only [ctlW, htop', hWk]; rw [hf.size CWK]
    exact hro (by have := hC.rel.room; simp only [ctlW, hH] at this; exact this)

section ce
variable {p : Prog} (P : ConeProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

theorem cmp_frame {f : FnName} (hf : f ∈ cmpFns) {n : Nat} {args r : List Word} {m m' : Mem}
    (h : callW p n f args m = some (r, m')) : MemFrame coneA coneC m m' :=
  (run_memFrame P.cmpClosed hf (run_of_callW h)).1.mono
    (fun _ hb => List.mem_append_left _ hb) (fun _ hx => List.mem_append_left _ hx)

omit P in
theorem NdR.coneFrame {m m' : Mem} {x : NeedsSt} (hf : MemFrame cmpA cmpC m m') (h : NdR m x) :
    NdR m' x :=
  h.frame hf ⟨not_mem_cmpA (by decide), not_mem_cmpA (by decide)⟩
    ⟨not_mem_cmpC (by decide), not_mem_cmpC (by decide)⟩

/-- **`cone_entry(w, vis)` refines `coneEntry`**: `0` for the twin's `none`, else `1` and what the
name reads on `NACC`; the context kept, the cone's state and the solution untouched (a frame of
`coneA`, `coneC`). -/
@[refines ConRon.Arena.coneEntry]
theorem coneEntry_ok {n : Nat} {m m' : Mem} {a : AState} {w : Word} {r : List Word}
    {J : ISolution} (h : callW p n "cone_entry" [w, vis] m = some (r, m'))
    (hC : ConeT dn vis fe J m a) (hw : HW w) (hN : ∃ x, NdR m x) :
    ∃ y a', (ConRon.Arena.coneEntry J fe (decI w)).run a = .ok (y, a') ∧
      ConeT dn vis fe J m' a' ∧ IWGrow m m' ∧ MemFrame coneA coneC m m' ∧
      (r.headD 0 = 0 ↔ y = none) ∧ (∃ x, NdR m' x) ∧
      (∀ ns, y = some ns → ∃ seen, NdR m' ⟨seen, ns⟩) := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (coneEntry_specW p P.ce n _ w vis) h
  rcases n with _ | n
  · rw [coneEntryW.eq_1] at hW; cases hW
  rw [coneEntryW.arm1] at hW
  have refl : ∀ y, (ConRon.Arena.coneEntry J fe (decI w)).run a = .ok (y, a) → y = none →
      ∀ m1, m1 = m → s'.mem = m1 → r = [0] →
      ∃ y a', (ConRon.Arena.coneEntry J fe (decI w)).run a = .ok (y, a') ∧
        ConeT dn vis fe J s'.mem a' ∧ IWGrow m s'.mem ∧ MemFrame coneA coneC m s'.mem ∧
        (r.headD 0 = 0 ↔ y = none) ∧ (∃ x, NdR s'.mem x) ∧
        (∀ ns, y = some ns → ∃ seen, NdR s'.mem ⟨seen, ns⟩) := by
    rintro y hy rfl m1 rfl e rfl
    subst e
    exact ⟨none, a, hy, hC, IWGrow.refl _, MemFrame.refl _ _ _, by simp, hN, fun _ h => nomatch h⟩
  -- `env_find`
  replace hW := opt_some hW (coneEntryW.k_env_find.eq_1 ..)
  obtain ⟨⟨r1, m1⟩, c1, hW⟩ := hW
  obtain ⟨s1, rfl, hm1, -, hf1, hd1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p P.ft.rowGet P.ft.baseGet P.ft.find n _ vis w hC.T.stage.check.env hw) c1
  simp only at hm1 hf1 hd1
  rw [hm1] at hW
  by_cases e1 : r1.headD 0 = 0
  · rw [coneEntryW.k_env_find.arm1 _ _ _ _ _ _ e1] at hW
    obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
    have hn : fe.find? (decI w) = none := by rw [hf1]; simp only [envFound, e1, ↓reduceIte]
    exact refl none (by simp [ConRon.Arena.coneEntry, hn]; rfl) rfl m rfl e.symm rfl
  rw [coneEntryW.k_env_find.arm2 _ _ _ _ _ _ e1] at hW
  obtain ⟨ci, hci⟩ := hd1 e1
  have hfi : fe.find? (decI w) = some ci := by rw [hf1]; simp only [envFound, e1, hci, ↓reduceIte]
  -- `sol_find`
  replace hW := opt_some hW (coneEntryW.k_sol_find.eq_1 ..)
  obtain ⟨⟨r2, m2⟩, c2, hW⟩ := hW
  obtain ⟨s2, rfl, hm2, -, hs2n, hs2s⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (solFind_refines p P.srg P.sf n _ w hC.sol hw) c2
  simp only at hm2 hs2n hs2s
  rw [hm2] at hW
  by_cases e2 : r2.headD 0 = 0
  · rw [coneEntryW.k_sol_find.arm1 _ _ _ _ _ _ _ e2] at hW
    obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
    have hn : J.find? (decI w) = none := hs2n.mpr e2
    exact refl none (by simp [ConRon.Arena.coneEntry, hfi, hn]; rfl) rfl m rfl e.symm rfl
  rw [coneEntryW.k_sol_find.arm2 _ _ _ _ _ _ _ e2] at hW
  obtain ⟨ci', hci'⟩ := Option.ne_none_iff_exists'.mp (fun h => e2 (hs2n.mp h))
  obtain ⟨-, hd⟩ := (hs2s ci').mp hci'
  -- `refines_b`
  replace hW := opt_some hW (coneEntryW.k_refines_b.eq_1 ..)
  obtain ⟨⟨r3, m3⟩, c3, hW⟩ := hW
  obtain ⟨C, hdc⟩ := hC.fden _ _ hfi
  obtain ⟨C', hdd⟩ := hC.sden _ _ hci'
  obtain ⟨b3, a3, hrun3, hT3, hg3, hok3, hr3, hx3, hb3⟩ :=
    refinesB_sim P.cmp n hC.T hC.ok hC.rd hci hd hdc hdd r3 m3 c3
  have hf3 : MemFrame coneA coneC m m3 := cmp_frame P (by decide) c3
  have hf3c : MemFrame cmpA cmpC m m3 := (run_memFrame P.cmpClosed (by decide) (run_of_callW c3)).1
  have hJ3 : SolR m3 J := hC.sol.growF hf3 coneA_sol coneC_sol hg3.erecGrow
  have hC3 : ConeT dn vis fe J m3 a3 :=
    ⟨hT3, hok3, hr3, hJ3, hC.fden.ext hx3, hC.sden.ext hx3⟩
  have hN3 : ∃ x, NdR m3 x := let ⟨x, hx⟩ := hN; ⟨x, hx.coneFrame hf3c⟩
  have hrun3' : (ConRon.Arena.coneEntry J fe (decI w)).run a =
      (if b3 then
        (if tableBeqP (fe.findTable? (decI w)) (J.findTable? (decI w)) then
          (do let ns ← ConRon.Arena.entryNeeds J.mates fe ci; pure (some ns) : AM (Option (List NIdx)))
        else pure none)
      else pure none).run a3 := by
    simp only [ConRon.Arena.coneEntry, hfi, hci', StateT.run_bind, hrun3, except_ok_bind]
  by_cases e3 : r3.headD 0 = 0
  · rw [coneEntryW.k_refines_b.arm1 _ _ _ _ _ _ _ e3] at hW
    obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
    have hb : b3 = false := by cases hq : b3; rfl; exact absurd (hb3.mpr hq) (by simpa using e3)
    rw [hb] at hrun3'
    refine ⟨none, a3, by rw [hrun3']; rfl, by rw [← e]; exact hC3, by rw [← e]; exact hg3,
      by rw [← e]; exact hf3, by simp, by rw [← e]; exact hN3, fun _ h => nomatch h⟩
  rw [coneEntryW.k_refines_b.arm2 _ _ _ _ _ _ _ e3] at hW
  have hb : b3 = true := hb3.mp e3
  rw [hb] at hrun3'
  simp only [↓reduceIte] at hrun3'
  -- `find_table`, `sol_find_table`
  replace hW := opt_some hW (coneEntryW.k_find_table.eq_1 ..)
  obtain ⟨⟨r4, m4⟩, c4, hW⟩ := hW
  obtain ⟨s4, rfl, hm4, -, ht4, htd4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (findTable_refines p P.ft n _ vis w hT3.stage.check.env hw) c4
  simp only at hm4 ht4 htd4
  rw [hm4] at hW
  rw [coneEntryW.k_find_table.arm1] at hW
  replace hW := opt_some hW (coneEntryW.k_sol_find_table.eq_1 ..)
  obtain ⟨⟨r5, m5⟩, c5, hW⟩ := hW
  obtain ⟨s5, rfl, hm5, -, ht5, htd5⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (solFindTable_refines p P.srg P.sf P.stg P.sft n _ w hJ3 hw) c5
  simp only at hm5 ht5 htd5
  rw [hm5] at hW
  rw [coneEntryW.k_sol_find_table.arm1] at hW
  replace hW := opt_some hW (coneEntryW.k_tbl_beq_p.eq_1 ..)
  obtain ⟨⟨r6, m6⟩, c6, hW⟩ := hW
  obtain ⟨hm6, hb6⟩ := tblBeqP_ok P.cmp htd4 htd5 c6
  subst hm6
  have hJt : J.findTable? (decI w) = tblFound m6 (r5.headD 0) := by rw [ht5, tblFound]
  rw [← ht4, ← hJt] at hb6
  by_cases e6 : r6.headD 0 = 0
  · rw [coneEntryW.k_tbl_beq_p.arm1 _ _ _ _ _ _ e6] at hW
    obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
    have ht : tableBeqP (fe.findTable? (decI w)) (J.findTable? (decI w)) = false := by
      cases hq : tableBeqP (fe.findTable? (decI w)) (J.findTable? (decI w))
      · rfl
      · exact absurd (hb6.mpr hq) (by simpa using e6)
    rw [ht] at hrun3'
    refine ⟨none, a3, by rw [hrun3']; rfl, by rw [← e]; exact hC3, by rw [← e]; exact hg3,
      by rw [← e]; exact hf3, by simp, by rw [← e]; exact hN3, fun _ h => nomatch h⟩
  rw [coneEntryW.k_tbl_beq_p.arm2 _ _ _ _ _ _ e6] at hW
  simp only [hb6.mp e6, ↓reduceIte] at hrun3'
  -- `entry_needs`
  replace hW := opt_some hW (coneEntryW.k_entry_needs.none ..)
  obtain ⟨⟨r7, m7⟩, c7, hW⟩ := hW
  rw [coneEntryW.k_entry_needs.arm1] at hW
  obtain ⟨rfl, e⟩ := Prod.mk.inj (Option.some.inj hW)
  subst e
  obtain ⟨x3, hx3'⟩ := hN3
  have hci3 : decCI (erecP m6) (r1.tail.headD 0).toNat = some ci := ArrExt.decCI hg3.ext hci
  obtain ⟨ns, a7, hrun7, hT7, hst7, hg7, ⟨seen, hy7⟩, hf7⟩ :=
    entryNeeds_ok P c7 hT3 hok3 hr3 hJ3 hci3 ⟨C, ConRon.Bridge.denoteCI_ext hdc hx3⟩ hx3'
  have hf7' : MemFrame coneA coneC m6 s'.mem :=
    hf7.mono (fun _ hb => List.mem_append_right _ hb) (fun _ hx => List.mem_append_right _ hx)
  refine ⟨some ns, a7, ?_, ⟨hT7, hst7.ok, hst7.read,
      hJ3.growF hf7' coneA_sol coneC_sol hg7.erecGrow, (hC.fden.ext hx3).ext hst7.ext,
      (hC.sden.ext hx3).ext hst7.ext⟩, hg3.trans hg7, hf3.trans hf7', by simp,
      ⟨_, hy7⟩, fun ns' e => by cases e; exact ⟨seen, hy7⟩⟩
  rw [hrun3']
  simp only [StateT.run_bind, hrun7, except_ok_bind]
  rfl

end ce

end L.Arena
