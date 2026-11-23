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

/-- **`StageT` across a frame** that writes none of the core's memos and stamps and not the pins
(its `StageR` given). -/
theorem _root_.L.Ind.StageT.of_fr {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {A : List TieredArray} {C : List Word} (hT : StageT dn vis fe m a)
    (hS : StageR vis fe m' a) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ [(ILMEMO : TieredArray), ABMEMO, WSM, FLM, LSM, LPMEMO, LPLMEMO, LPLSMEMO, HBM, PINS],
      b ∉ A)
    (hC' : ∀ x ∈ C, 214 < x.toNat) :
    StageT dn vis fe m' a :=
  have hC : ∀ x ∈ ([50, 48, 152, 154, 156, 54, 56, 58, 214] : List Word), x ∉ C := by
    intro x hx hm
    have := hC' x hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at this
  ⟨hS, hT.twin.frame hf ⟨hA _ (by simp), hA _ (by simp)⟩ ⟨hC _ (by simp), hC _ (by simp)⟩
    ⟨hA _ (by simp), hA _ (by simp), hA _ (by simp)⟩ ⟨hC _ (by simp), hC _ (by simp), hC _ (by simp)⟩
    ⟨hA _ (by simp), hA _ (by simp), hA _ (by simp)⟩ ⟨hC _ (by simp), hC _ (by simp), hC _ (by simp)⟩
    (hA _ (by simp)) (hC _ (by simp)),
    by simp only [pinW, hf.arr PINS (hA _ (by simp)) (by decide)]; exact hT.flag⟩

theorem hiCtl {x : Word} (h : 214 < x.toNat ∧ x.toNat < 1000) :
    ∀ y ∈ [x], 131 ≤ y.toNat ∧ y.toNat ≠ 133 ∧ y.toNat ≠ 134 ∧ y.toNat ≠ 135 ∧
      (y.toNat < 160 ∨ 172 ≤ y.toNat) := by
  intro y hy; simp only [List.mem_singleton] at hy; subst hy; omega

theorem solCtl_not {x : Word} (h : x.toNat < 224 ∨ 226 < x.toNat) : ∀ y ∈ [x], y ∉ solCtl := by
  intro y hy hm
  simp only [List.mem_singleton] at hy; subst hy
  simp only [solCtl, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> simp [SOLC, SNEXTC, SCNTC] at h

theorem hiCtl' {x : Word} (h : 214 < x.toNat ∧ x.toNat < 1000) : ∀ y ∈ [x], 214 < y.toNat := by
  intro y hy; simp only [List.mem_singleton] at hy; subst hy; omega

/-! ## `cone_go` -/

/-- **The stack's pop**: a nonempty stack's top word is the work list's head, a handle word; the
rest is the stack below it. -/
theorem CnR.pop {m : Mem} {seen : Std.HashMap NIdx Bool} {work : List NIdx} (hC : CnR m seen work)
    (h0 : rdW (m.arr64 CTL) CTOPC ≠ 0) :
    HW (rdW ((m.set64 CTL CTOPC (rdW (m.arr64 CTL) CTOPC - 1)).arr64 CWK)
      (rdW (m.arr64 CTL) CTOPC - 1)) ∧
    ∃ rest, work = decI (rdW ((m.set64 CTL CTOPC (rdW (m.arr64 CTL) CTOPC - 1)).arr64 CWK)
      (rdW (m.arr64 CTL) CTOPC - 1)) :: rest ∧
      CnR (m.set64 CTL CTOPC (rdW (m.arr64 CTL) CTOPC - 1)) seen rest := by
  generalize hh : rdW (m.arr64 CTL) CTOPC = h at h0 ⊢
  have hf := MemFrame.setCtl m CTOPC (h - 1)
  have hW : (m.set64 CTL CTOPC (h - 1)).arr64 CWK = m.arr64 CWK := hf.arr _ (by simp) (by decide)
  obtain ⟨k, hk, hk1⟩ := ndFuel_pred h0
  have hsz := hC.ctl
  have htop : ctlW (m.set64 CTL CTOPC (h - 1)) CTOPC = h - 1 := by
    simp only [ctlW, rdW_set64, hsz, and_self, ite_true]
  have hH : (ctlW m CTOPC).toNat = k + 1 := by simp only [ctlW, hh, hk]
  rw [hW]
  have hwr : rdW (m.arr64 CWK) (h - 1) = rdN (m.arr64 CWK) k := by
    show rdN _ (h - 1).toNat = _; rw [hk1]
  rw [hwr]
  refine ⟨hC.rel.words k (by omega), cwkList (m.set64 CTL CTOPC (h - 1)), ?_, ⟨⟨?_, rfl, ?_, ?_⟩, ?_⟩⟩
  · rw [← hC.rel.work]
    simp only [cwkList, htop, hk1, hW, hH, List.range_succ, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.map_cons]
  · exact memoRG_frame csSch csSch_wf nmKey _ [] [CTOPC] (by simp) (by decide) _ _ hf _ hC.rel.seen
  · intro i hi; rw [htop, hk1] at hi; rw [hW]; exact hC.rel.words i (by omega)
  · rw [htop, hk1, hW]; have := hC.rel.room; omega
  · rw [Mem.size64_set64]; exact hsz

section cg
variable {p : Prog} (P : ConeProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include P

/-- **`cone_go`'s loop refines `coneGo`**: from the stack `work` and the memo `seen`, the twin's
walk at the fuel `f` runs, `(0, _)` exactly for its `none`; the context kept, a needs walk's and
the cone's state related after. -/
theorem coneGo_loop {J : ISolution} : ∀ (k : Nat) (m m' : Mem) (a : AState) (f : Word)
    (r : List Word) (seen : Std.HashMap NIdx Bool) (work : List NIdx),
    coneGoW.loop1 p k m f vis (rdW (m.arr64 CTL) CTOPC) = some (r, m') →
    ConeT dn vis fe J m a → CnR m seen work → (∃ x, NdR m x) →
    ∃ y a', (ConRon.Arena.coneGo J fe f.toNat seen work).run a = .ok (y, a') ∧
      ConeT dn vis fe J m' a' ∧ IWGrow m m' ∧ (∃ x, NdR m' x) ∧ (∃ s w, CnR m' s w) ∧
      (r.headD 0 = 0 ↔ y.1 = none) := by
  intro k
  induction k with
  | zero => intro m m' a f r seen work h; rw [coneGoW.loop1.eq_1] at h; cases h
  | succ k ih =>
  intro m m' a f r seen work h hC hW hN
  by_cases h0 : rdW (m.arr64 CTL) CTOPC = 0
  · rw [coneGoW.loop1.arm2 _ _ _ _ _ _ h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hw : work = [] := by
      rw [← hW.rel.work]; simp [cwkList, ctlW, h0]
    subst hw
    exact ⟨(none, f.toNat, seen), a, by simp [ConRon.Arena.coneGo]; rfl, hC, IWGrow.refl _, hN,
      ⟨_, _, hW⟩, by simp⟩
  rw [coneGoW.loop1.arm1 _ _ _ _ _ _ h0] at h
  obtain ⟨hw, rest, rfl, hW1⟩ := hW.pop h0
  generalize hm1 : m.set64 CTL CTOPC (rdW (m.arr64 CTL) CTOPC - 1) = m1 at h hw hW1
  generalize hn' : rdW (m1.arr64 CWK) (rdW (m.arr64 CTL) CTOPC - 1) = w at h hw hW1 ⊢
  have hf1 : MemFrame [] [CTOPC] m m1 := by rw [← hm1]; exact MemFrame.setCtl m CTOPC _
  have hC1 : ConeT dn vis fe J m1 a :=
    ⟨hC.T.of_fr (hC.T.stage.frame_hi hf1 (by simp) (hiCtl (by decide)) (by simp) (by decide)).1 hf1
      (by decide) (hiCtl' (by decide)), hC.ok, hC.rd,
      hC.sol.growF hf1 (by simp) (by simp [solCtl, CTOPC, SOLC, SNEXTC, SCNTC])
        (iwGrow_frame hf1 (by simp) (by decide)).erecGrow, hC.fden, hC.sden⟩
  have hN1 : ∃ x, NdR m1 x := let ⟨x, hx⟩ := hN; ⟨x, hx.frame hf1 (by simp) (by simp; decide)⟩
  have hg1 : IWGrow m m1 := iwGrow_frame hf1 (by simp) (by decide)
  -- `cs_find(w, 0)`
  replace h := opt_some h (coneGoW.k_cs_find.eq_1 ..)
  obtain ⟨⟨r2, m2⟩, c2, h⟩ := h
  obtain ⟨s2, hs2, hs, hne2, hr2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (memoFindG_spec csSch p "cs_find" P.csf k _ w 0) c2
  subst hs; simp only at hs2; subst hs2
  have hk : nmKey.ok w 0 := ⟨hw, rfl⟩
  by_cases hhit : r2.headD 0 ≠ 0
  · -- seen: the rest
    rw [coneGoW.k_cs_find.arm3 _ _ _ _ _ _ _ hhit, coneGoW.j1.arm1] at h
    rw [hr2] at hhit
    have hs := memoRG_hit csSch nmKey _ _ seen hW1.rel.seen w 0 (by rw [← hr2]; exact hne2) hhit hk
    obtain ⟨y, a', e, hC', hg', hN', hW', hr⟩ := ih _ _ a f r seen rest h hC1 hW1 hN1
    refine ⟨y, a', ?_, hC', hg1.trans hg', hN', hW', hr⟩
    have hc : seen.contains (decI w) = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?]; simp only [nmKey] at hs; rw [hs]; rfl
    unfold ConRon.Arena.coneGo
    simp only [hc, ↓reduceIte]
    exact e
  have hmiss : r2.headD 0 = 0 := Classical.not_not.mp hhit
  have hs := memoRG_miss csSch nmKey _ _ seen hW1.rel.seen w 0 hk (by rw [← hr2]; exact hne2)
    (by rw [← hr2]; exact hmiss)
  have hc : seen.contains (decI w) = false := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]; simp only [nmKey] at hs; rw [hs]; rfl
  by_cases hf0 : f = 0
  · rw [coneGoW.k_cs_find.arm1 _ _ _ _ _ _ _ hmiss hf0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst hf0
    exact ⟨(some (decI w), 0, seen), a, by simp [ConRon.Arena.coneGo, hc]; rfl, hC1, hg1, hN1,
      ⟨_, _, hW1⟩, by simp⟩
  rw [coneGoW.k_cs_find.arm2 _ _ _ _ _ _ _ hmiss hf0] at h
  obtain ⟨fk, hfk, hfk1⟩ := ndFuel_pred hf0
  -- `cone_entry(w, vis)`
  replace h := opt_some h (coneGoW.k_cone_entry.eq_1 ..)
  obtain ⟨⟨r3, m3⟩, c3, h⟩ := h
  obtain ⟨y3, a3, hrun3, hC3, hg3, hf3, hr3, hN3, hy3⟩ := coneEntry_ok P c3 hC1 hw hN1
  have hW3 : CnR m3 seen rest := hW1.coneFrame hf3
  have hrun' : (ConRon.Arena.coneGo J fe f.toNat seen (decI w :: rest)).run a =
      (match y3 with
        | none => pure (some (decI w), fk + 1, seen)
        | some ns => ConRon.Arena.coneGo J fe fk (seen.insert (decI w) true) (ns ++ rest) :
        AM (Option NIdx × Nat × Std.HashMap NIdx Bool)).run a3 := by
    rw [hfk]
    simp only [ConRon.Arena.coneGo, hc, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hrun3,
      except_ok_bind]
    cases y3 <;> rfl
  by_cases e3 : r3.headD 0 = 0
  · rw [coneGoW.k_cone_entry.arm1 _ _ _ _ _ _ _ e3] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have e3' := hr3.mp e3
    subst e3'
    exact ⟨_, a3, hrun', hC3, hg1.trans hg3, hN3, ⟨_, _, hW3⟩, by simp⟩
  rw [coneGoW.k_cone_entry.arm2 _ _ _ _ _ _ _ e3] at h
  obtain ⟨ns, rfl⟩ := Option.ne_none_iff_exists'.mp (fun e => e3 (hr3.mpr e))
  obtain ⟨sn, hx3⟩ := hy3 ns rfl
  simp only at hrun'
  -- `cs_find(w, 0)`, `cs_put(w, 0, 1, …)`
  replace h := opt_some h (coneGoW.k_cs_find_2.eq_1 ..)
  obtain ⟨⟨r4, m4⟩, c4, h⟩ := h
  obtain ⟨s4, hs4, hs, hne4, hr4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (memoFindG_spec csSch p "cs_find" P.csf k _ w 0) c4
  subst hs; simp only at hs4; subst hs4
  rw [coneGoW.k_cs_find_2.arm1] at h
  replace h := opt_some h (coneGoW.k_cs_put.eq_1 ..)
  obtain ⟨⟨r5, m5⟩, c5, h⟩ := h
  obtain ⟨s5, rfl, -, hput⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (memoPutG_spec csSch p "cs_put" P.csp k _ w 0 1 _ _) c5
  rw [hr4, ← msetG_eq csSch m3 w 0 1 (by rw [← hr4]; exact hne4)] at hput
  have hf5 := msetG_frame csSch csSch_wf _ _ w 0 1 hput
  have hseen5 := memoRG_set csSch csSch_wf nmKey (fun w : Word => w != 0) _ seen hW3.rel.seen w 0 1
    hk _ hput
  have hW5 : CnR s5.mem (seen.insert (decI w) true) rest := by
    have hK : s5.mem.arr64 CWK = m3.arr64 CWK := hf5.arr _ (by decide) (by decide)
    have hT : ctlW s5.mem CTOPC = ctlW m3 CTOPC := hf5.ctl _ (by decide)
    refine ⟨⟨hseen5, ?_, ?_, ?_⟩, by rw [hf5.size]; exact hW3.ctl⟩
    · rw [← hW3.rel.work]; simp only [cwkList, hK, hT]
    · intro i hi; rw [hK]; exact hW3.rel.words i (by rw [← hT]; exact hi)
    · rw [hK, hT]; exact hW3.rel.room
  have hx5 : NdR s5.mem ⟨sn, ns⟩ := hx3.frame hf5 (by decide) (by decide)
  have hg5 : IWGrow m3 s5.mem := iwGrow_frame hf5 (by decide) (by decide)
  have hC5 : ConeT dn vis fe J s5.mem a3 :=
    ⟨hC3.T.of_fr (hC3.T.stage.frame_hi hf5 (by decide) (hiCtl (by decide)) (by decide) (by decide)).1 hf5
      (by decide) (hiCtl' (by decide)), hC3.ok, hC3.rd,
      hC3.sol.growF hf5 (by decide) (solCtl_not (by decide)) hg5.erecGrow, hC3.fden, hC3.sden⟩
  -- `cone_push`, the loop
  rw [coneGoW.k_cs_put.arm1] at h
  replace h := opt_some h (coneGoW.k_cone_push.eq_1 ..)
  obtain ⟨⟨r6, m6⟩, c6, h⟩ := h
  rw [coneGoW.k_cone_push.arm1, coneGoW.j1.arm1] at h
  obtain ⟨hW6, hf6⟩ := conePush_ok P.cp c6 hW5 hx5
  have hg6 : IWGrow s5.mem m6 := iwGrow_frame hf6 (by decide) (by decide)
  have hC6 : ConeT dn vis fe J m6 a3 :=
    ⟨hC5.T.of_fr (hC5.T.stage.frame_hi hf6 (by decide) (hiCtl (by decide)) (by decide) (by decide)).1 hf6
      (by decide) (hiCtl' (by decide)), hC5.ok, hC5.rd,
      hC5.sol.growF hf6 (by decide) (solCtl_not (by decide)) hg6.erecGrow, hC5.fden, hC5.sden⟩
  have hN6 : ∃ x, NdR m6 x := ⟨_, hx5.frame hf6 (by decide) (by decide)⟩
  obtain ⟨y, a', e, hC', hg', hN', hW', hr⟩ := ih _ _ a3 (f - 1) r _ _ h hC6 hW6 hN6
  rw [hfk1] at e
  exact ⟨y, a', by rw [hrun']; exact e, hC', hg1.trans (hg3.trans (hg5.trans (hg6.trans hg'))), hN',
    hW', hr⟩

/-- **`cone_go(f, vis)` refines `coneGo`** at the fuel `f`, from the memo `seen` and the stack
`work`: `(0, _)` exactly for the twin's `none`. -/
@[refines ConRon.Arena.coneGo]
theorem coneGo_ok {J : ISolution} {n : Nat} {m m' : Mem} {a : AState} {f : Word} {r : List Word}
    {seen : Std.HashMap NIdx Bool} {work : List NIdx}
    (h : callW p n "cone_go" [f, vis] m = some (r, m'))
    (hC : ConeT dn vis fe J m a) (hW : CnR m seen work) (hN : ∃ x, NdR m x) :
    ∃ y a', (ConRon.Arena.coneGo J fe f.toNat seen work).run a = .ok (y, a') ∧
      ConeT dn vis fe J m' a' ∧ IWGrow m m' ∧ (∃ x, NdR m' x) ∧ (∃ s w, CnR m' s w) ∧
      (r.headD 0 = 0 ↔ y.1 = none) := by
  obtain ⟨s', rfl, -, hW'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (coneGo_specW p P.cg n _ f vis) h
  rcases n with _ | n
  · rw [coneGoW.eq_1] at hW'; cases hW'
  rw [coneGoW.arm1] at hW'
  exact coneGo_loop P _ _ _ a f r seen work hW' hC hW hN

end cg

end L.Arena
