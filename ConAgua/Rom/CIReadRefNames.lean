import ConAgua.Rom.CIReadRefBase

/-!
# The ROM constant readers: the callees under the invariant, and name slices (helper `decls4-rom`)

`nameCall`, `exprCall`, `u64Call`, `allocCall`, `freshCall`: a returning `callW` of a callee is
the twin's run, with the invariant `Inv` after. Then `rci_names_to` (`internNameList`, the
handles to `EREC[o ‥]`) and `rci_name_sl` (a counted name list as a fresh `EREC` slice).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

namespace L.Rom

open L.Arena L.Ind

/-- `MemoR` across a writer that leaves `RMEMO` and `CTL[132]` alone. -/
theorem MemoR.frameG {A : List ArrId} {C : List Word} {mem mem' : Mem} {seen : List ConLeche.Expr}
    {m : EMemo} (h : MemoR mem seen m) (hf : MemFrame A C mem mem') (hA : RMEMO ∉ A)
    (hC : (132 : Word) ∉ C) : MemoR mem' seen m := by
  have hR : mem'.arr64 RMEMO = mem.arr64 RMEMO := hf.1 RMEMO hA (by decide)
  have hc : memoCnt mem' = memoCnt mem := hf.2.1 132 hC
  exact ⟨by rw [hc]; exact h.cnt, fun k hk => by rw [hR]; exact h.ent k hk, h.keys, h.room,
    by rw [hf.2.2.1]; exact h.csz⟩

section calls
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

theorem nameCall (x : ConLeche.Name) (hx : nameFits x = true) {n : Nat} {m m' : Mem} {a : AState}
    {pos : Word} {rest : List UInt8} {r : List Word} (hA : ArenaD m a)
    (hd : rom.drop pos.toNat = encName x ++ rest) (hc : callW p n "rom_name" [pos] m = some (r, m')) :
    ∃ a', (internName x).run a = .ok (decI (r.headD 0), a') ∧ ArenaD m' a' ∧ cp a' = cp a ∧
      (r.headD 0).toNat < 2 ^ 32 ∧ (r.tail.headD 0).toNat = pos.toNat + (encName x).length ∧
      MemFrame StoreA StoreC m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (romName_specW rom p hL.toNameProg n _ pos hA.1.lit.1.2.2.1) hc
  obtain ⟨ok, hR, res, hlt, hq, hf⟩ := romNameW_ok rom hr x hx n _ a pos rest _ _ _ hA hd hW
  have hrun := AM.run_of_ok _ _ ok
  rw [res] at hrun
  exact ⟨_, hrun, hR, (keeps_internName x).run hrun, hlt, hq, hf⟩

theorem exprCall (e : ConLeche.Expr) (he : exprFits e = true) {n : Nat} {mem mem' : Mem} {a : AState}
    {pos : Word} {rest : List UInt8} {seen : List ConLeche.Expr} {memo : EMemo} {r : List Word}
    (hA : ArenaD mem a) (hM : MemoR mem seen memo) (hd : rom.drop pos.toNat = (encExprM seen e).1 ++ rest)
    (hst : (stkTop mem).toNat < 2 ^ 61) (hcs : 131 < (mem.arr64 CTL).size)
    (hc : callW p n "rom_expr" [pos] mem = some (r, mem')) :
    ∃ (memo' : EMemo) (a' : AState), (internExprGo memo e).run a = .ok ((memo', decI (r.headD 0)), a') ∧
      ArenaD mem' a' ∧ cp a' = cp a ∧ MemoR mem' (encExprM seen e).2 memo' ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (r.tail.headD 0).toNat = pos.toNat + (encExprM seen e).1.length ∧ MemFrame ExprA ExprC mem mem' ∧
      stkTop mem' = stkTop mem := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨mem, Locals.init []⟩)
    ((romExpr_specsW rom p hL.toExprProg n).1 _ pos hA.1.lit.1.2.2.1) hc
  obtain ⟨memo', a', hrun, hR, hM', hlt, hq, hf, hs, -⟩ :=
    romExprW_ok rom hr e he n _ a pos rest seen memo _ _ _ hA hM hd hst hcs hW
  exact ⟨memo', a', hrun, hR, (keeps_internExprGo e memo).run hrun, hM', hlt, hq, hf, hs⟩

end calls

theorem u64Call {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m m' : Mem}
    {i : Word} {r : List Word} (hc : callW p n "rom_u64" [i] m = some (r, m')) :
    m' = m ∧ r = [u64W rom i] := by
  obtain ⟨s', rfl, hs, -, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (romU64_spec rom p hL.rom_u64 n _ i) hc
  exact ⟨by rw [hs], hr⟩

theorem erAllocCall {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m m' : Mem}
    {k : Word} {r : List Word} (hc : callW p n "erec_alloc" [k] m = some (r, m')) :
    erAllocW m k = some (r.headD 0, m') := by
  obtain ⟨s', rfl, -, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (erecAlloc_specW p hL.erec_alloc n _ k) hc
  exact hr

theorem iwAllocCall {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m m' : Mem}
    {k : Word} {r : List Word} (hc : callW p n "iw_alloc" [k] m = some (r, m')) :
    allocW m k = some (r.headD 0, m') := by
  obtain ⟨s', rfl, -, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iwAlloc_specW p hL.iw_alloc n _ k) hc
  exact hr

/-- The word just written. -/
theorem er_set_get (m : Mem) (i w : Word) (hi : i.toNat < (m.arr64 EREC).size) :
    (erA (m.set64 EREC i w))[i.toNat]? = some w := by
  simp only [erA]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hi]

theorem iw_set_get (m : Mem) (i w : Word) (hi : i.toNat < (m.arr64 IW).size) :
    (iwA (m.set64 IW i w))[i.toNat]? = some w := by
  simp only [iwA]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hi]

/-- A word index below a top within an array of word size. -/
theorem toNat_add_of_lt (o : Word) (k : Nat) (h : o.toNat + k < 2 ^ 64) :
    (o + UInt64.ofNat k).toNat = o.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega

theorem Inv.er_lt {m₀ m : Mem} {a₀ a : AState} (h : Inv m₀ a₀ m a) : erTop m < 2 ^ 64 := by
  have := h.ok.2.1; have := h.ok.2.2.2.1; omega

theorem Inv.iw_lt {m₀ m : Mem} {a₀ a : AState} (h : Inv m₀ a₀ m a) : iwTop m < 2 ^ 64 := by
  have := h.ok.1; have := h.ok.2.2.1; omega

section names
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_names_to` refines `internNameList`**, the handles to `EREC[o ‥]`. -/
theorem namesTo_rel {m₀ : Mem} {a₀ : AState} (seen : List ConLeche.Expr) (memo : EMemo) :
    ∀ (ns : List ConLeche.Name), ns.all nameFits = true → ∀ (k : Nat) (m : Mem) (a : AState)
      (q o kw : Word) (rest : List UInt8) (r : List Word) (m' : Mem), Inv m₀ a₀ m a →
      MemoR m seen memo → rom.drop q.toNat = encNames ns ++ rest → kw.toNat = ns.length →
      erTop m₀ ≤ o.toNat → o.toNat + ns.length ≤ erTop m →
      callW p k "rci_names_to" [q, o, kw] m = some (r, m') →
      ∃ (ws : List Word) (a' : AState), (Frontend.internNameList ns).run a = .ok (ws.map decI, a') ∧
        ws.length = ns.length ∧ (∀ w ∈ ws, w.toNat < 2 ^ 32) ∧
        (∀ j (hj : j < ws.length), (erA m')[o.toNat + j]? = some ws[j]) ∧
        Inv m₀ a₀ m' a' ∧ MemoR m' seen memo ∧ stkTop m' = stkTop m ∧
        (r.headD 0).toNat = q.toNat + (encNames ns).length ∧
        EKeep (fun i => o.toNat ≤ i ∧ i < o.toNat + ns.length) m m' ∧ erTop m' = erTop m ∧
        m'.arr64 IW = m.arr64 IW := by
  intro ns
  induction ns with
  | nil =>
    intro _ k m a q o kw rest r m' hI hM hd hk ho hot hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mq => namesToW p k mq q o kw) (namesTo_specW rom p hL k · q o kw) hc
    have hk0 : kw = 0 := by apply UInt64.toNat_inj.mp; simpa using hk
    simp only [namesToW, hk0, if_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨[], a, rfl, rfl, by simp, by simp, hI, hM, rfl, by simp [encNames], EKeep.refl _ _, rfl, rfl⟩
  | cons x xs ih =>
    intro hfit k m a q o kw rest r m' hI hM hd hk ho hot hc
    simp only [List.all_cons, Bool.and_eq_true] at hfit
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mq => namesToW p k mq q o kw) (namesTo_specW rom p hL k · q o kw) hc
    have hk0 : kw ≠ 0 := fun h => by subst h; simp at hk
    simp only [namesToW, hk0, if_false] at hw
    cases h1 : callW p k "rom_name" [q] m with
    | none => rw [h1] at hw; simp at hw
    | some t1 =>
    obtain ⟨r1, m1⟩ := t1
    rw [h1, bW_some] at hw
    have hd0 : rom.drop q.toNat = encName x ++ (encNames xs ++ rest) := by
      rw [hd, encNames, List.append_assoc]
    obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1⟩ := nameCall hL hr x hfit.1 hI.arena hd0 h1
    obtain ⟨hI1, hE1, hIW1, ht1, -⟩ := hI.expr hA1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
      (fun x hx => by simp [ExprC, RomC, hx])) hk1
    have hM1 := hM.frameG hf1 (by decide) (by decide)
    have hs1 : stkTop m1 = stkTop m := hf1.2.1 131 (by decide)
    have hlen : xs.length + 1 = kw.toNat := by simp [hk]
    have hoE : o.toNat < (m1.arr64 EREC).size := by
      have := hI1.ok.2.1; rw [ht1] at this; simp at hot; omega
    have hI2 := hI1.setER o (r1.headD 0) ho
    have hf2 := MemFrame.set64 m1 EREC (by decide) o (r1.headD 0)
    have hM2 := hM1.frameG hf2 (by decide) (by simp)
    have hC2 : (m1.set64 EREC o (r1.headD 0)).arr64 CTL = m1.arr64 CTL :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have ht2 : erTop (m1.set64 EREC o (r1.headD 0)) = erTop m1 := by simp only [erTop, hC2]
    have hs2 : stkTop (m1.set64 EREC o (r1.headD 0)) = stkTop m1 := by simp only [stkTop, hC2]
    have hIW2 : (m1.set64 EREC o (r1.headD 0)).arr64 IW = m1.arr64 IW :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hd1 : rom.drop (r1.tail.headD 0).toNat = encNames xs ++ rest :=
      drop_shift rom hr q (encName x) (encNames xs) rest (by rw [hd0, List.append_assoc]) _ hq1
    have ho1 : (o + 1).toNat = o.toNat + 1 := by
      have := hI.er_lt; simp at hot; rw [UInt64.toNat_add]; simp; omega
    have hk1' : (kw - 1).toNat = xs.length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    cases h2 : callW p k "rci_names_to" [r1.tail.headD 0, o + 1, kw - 1] (m1.set64 EREC o (r1.headD 0)) with
    | none => rw [h2] at hw; simp at hw
    | some t2 =>
    obtain ⟨r2, m3⟩ := t2
    rw [h2, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    simp only [List.length_cons] at hot
    obtain ⟨ws, a', hrun2, hwl, hwlt, hwd, hI3, hM3, hs3, hq3, hek3, ht3, hiw3⟩ :=
      ih hfit.2 k _ a1 _ (o + 1) (kw - 1) rest r2 m3 hI2 hM2 hd1 hk1' (by omega)
        (by rw [ht2, ht1, ho1]; omega) h2
    refine ⟨r1.headD 0 :: ws, a', ?_, by simp [hwl], ?_, ?_, hI3, hM3, by rw [hs3, hs2, hs1], ?_, ?_,
      by rw [ht3, ht2, ht1], by rw [hiw3, hIW2, hIW1]⟩
    · show (internName x >>= fun h => Frontend.internNameList xs >>= fun hs => pure (h :: hs)).run a = _
      rw [run_bind_of _ _ _ _ _ hrun1, run_bind_of _ _ _ _ _ hrun2]; rfl
    · intro w hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact hlt1
      · exact hwlt w hw'
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [hek3.2 o.toNat (by rw [ht2, ht1]; omega) (by rw [ho1]; omega)]
        exact er_set_get m1 o _ hoE
      | succ j =>
        simp only [List.getElem_cons_succ]
        have := hwd j (by simp at hj; omega)
        rw [ho1, Nat.add_assoc, Nat.add_comm 1 j] at this
        exact this
    · rw [hq3, hq1]; simp [encNames]; omega
    · refine ((EKeep.of_eq hE1 (by rw [ht1])).trans (EKeep.set _ o _ ⟨Nat.le_refl _, by omega⟩)).trans
        (hek3.mono fun i hi => ⟨by rw [ho1] at hi; omega, by rw [ho1] at hi; omega⟩)
end names

end L.Rom
