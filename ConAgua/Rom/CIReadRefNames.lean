import ConAgua.Rom.CIReadRefBase
import ConAgua.Rom.CIReadRefW

/-!
# The ROM constant readers: the callees under the invariant, and name slices (helper `decls4-rom`)

`nameCall`, `exprCall`, `u64Call`, `allocCall`, `freshCall`: a returning `callW` of a callee is
the twin's run, with the invariant `RInv` after. Then `rci_names_to` (`internNameList`, the
handles to `EREC[o ‥]`) and `rci_name_sl` (a counted name list as a fresh `EREC` slice).
-/


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
    {pos : Word} {rest : List UInt8} {r : List Word} (hA : ArenaD m a) (hmo : ModeOK m)
    (hd : rom.drop pos.toNat = encName x ++ rest) (hc : callW p n "rom_name" [pos] m = some (r, m')) :
    ∃ a', (internName x).run a = .ok (decI (r.headD 0), a') ∧ ArenaD m' a' ∧ cp a' = cp a ∧
      (r.headD 0).toNat < 2 ^ 32 ∧ (r.tail.headD 0).toNat = pos.toNat + (encName x).length ∧
      MemFrame StoreA StoreC m m' ∧ ModeOK m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (romName_specW rom p hL.toNameProg n _ pos ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩) hc
  obtain ⟨ok, hR, res, hlt, hq, hf⟩ := romNameW_ok rom hr x hx n _ a pos rest _ _ _ hA hmo hd hW
  have hrun := AM.run_of_ok _ _ ok
  rw [res] at hrun
  exact ⟨_, hrun, hR, (keeps_internName x).run hrun, hlt, hq, hf, (romNameW_topK hW).mode hA.1.lit.1 hmo⟩

theorem exprCall (e : ConLeche.Expr) (he : exprFits e = true) {n : Nat} {mem mem' : Mem} {a : AState}
    {pos : Word} {rest : List UInt8} {seen : List ConLeche.Expr} {memo : EMemo} {r : List Word}
    (hA : ArenaD mem a) (hmo : ModeOK mem) (hM : MemoR mem seen memo) (hd : rom.drop pos.toNat = (encExprM seen e).1 ++ rest)
    (hst : (stkTop mem).toNat < 2 ^ 61) (hcs : 131 < (mem.arr64 CTL).size)
    (hc : callW p n "rom_expr" [pos] mem = some (r, mem')) :
    ∃ (memo' : EMemo) (a' : AState), (internExprGo memo e).run a = .ok ((memo', decI (r.headD 0)), a') ∧
      ArenaD mem' a' ∧ cp a' = cp a ∧ MemoR mem' (encExprM seen e).2 memo' ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (r.tail.headD 0).toNat = pos.toNat + (encExprM seen e).1.length ∧ MemFrame ExprA ExprC mem mem' ∧
      stkTop mem' = stkTop mem ∧ ModeOK mem' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨mem, Locals.init []⟩)
    ((romExpr_specsW rom p hL.toExprProg n).1 _ pos ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩) hc
  obtain ⟨memo', a', hrun, hR, hM', hlt, hq, hf, hs, -⟩ :=
    romExprW_ok rom hr e he n _ a pos rest seen memo _ _ _ hA hmo hM hd hst hcs hW
  exact ⟨memo', a', hrun, hR, (keeps_internExprGo e memo).run hrun, hM', hlt, hq, hf, hs,
    ((romExprW_topK rom n).1 _ _ _ _ _ hW).mode hA.1.lit.1 hmo⟩

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

theorem RInv.er_lt {m₀ m : Mem} {a₀ a : AState} {T : Nat} (h : RInv m₀ a₀ T m a) : erTop m < 2 ^ 64 := by
  have := h.ok.2.1; have := h.ok.2.2.2.1; omega

theorem RInv.iw_lt {m₀ m : Mem} {a₀ a : AState} {T : Nat} (h : RInv m₀ a₀ T m a) : iwTop m < 2 ^ 64 := by
  have := h.ok.1; have := h.ok.2.2.1; omega

section names
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_names_to` refines `internNameList`**, the handles to `EREC[o ‥]`. -/
@[refines ConRon.Arena.Frontend.internNameList]
theorem namesTo_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo) :
    ∀ (ns : List ConLeche.Name), ns.all nameFits = true → ∀ (k : Nat) (m : Mem) (a : AState)
      (q o kw : Word) (rest : List UInt8) (r : List Word) (m' : Mem), RInv m₀ a₀ T m a →
      MemoR m seen memo → rom.drop q.toNat = encNames ns ++ rest → kw.toNat = ns.length →
      erTop m₀ ≤ o.toNat → o.toNat + ns.length ≤ erTop m →
      callW p k "rci_names_to" [q, o, kw] m = some (r, m') →
      ∃ (ws : List Word) (a' : AState), (Frontend.internNameList ns).run a = .ok (ws.map decI, a') ∧
        ws.length = ns.length ∧ (∀ w ∈ ws, w.toNat < 2 ^ 32) ∧
        (∀ j (hj : j < ws.length), (erA m')[o.toNat + j]? = some ws[j]) ∧
        RInv m₀ a₀ T m' a' ∧ MemoR m' seen memo ∧ stkTop m' = stkTop m ∧
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
    simp only [namesToW, hk0, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
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
    simp only [namesToW, hk0, ite_false] at hw
    obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
    have hd0 : rom.drop q.toNat = encName x ++ (encNames xs ++ rest) := by
      rw [hd, encNames, List.append_assoc]
    obtain ⟨a1, hrun1, hA1, hk1, hlt1, hq1, hf1, hmo1⟩ := nameCall hL hr x hfit.1 hI.arena hI.mode hd0 h1
    obtain ⟨hI1, hE1, hIW1, ht1, -⟩ := hI.expr hA1 hmo1 (hf1.mono (fun b hb => by simp [ExprA, RomA, hb])
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
      drop_shift rom q (encName x) (encNames xs) rest (by rw [hd0, List.append_assoc]) _ hq1
    have ho1 : (o + 1).toNat = o.toNat + 1 := by
      have := hI.er_lt; simp at hot; rw [UInt64.toNat_add]; simp; omega
    have hk1' : (kw - 1).toNat = xs.length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    obtain ⟨r2, m3, h2, hw⟩ := ntBW_inv hw
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
    · simp only [List.headD_cons]; rw [hq3, hq1]; simp [encNames]; omega
    · refine ((EKeep.of_eq hE1 (by rw [ht1]; exact Nat.le_refl _)).trans (EKeep.set _ o _ ⟨Nat.le_refl _, by omega⟩)).trans
        (hek3.mono fun i hi => ⟨by rw [ho1] at hi; omega, by rw [ho1] at hi; omega⟩)
end names

/-! ## Name slices as decodings -/

theorem rmapM_some_of {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
    simp [List.mapM_cons, h x (by simp), rmapM_some_of f g xs (fun y hy => h y (by simp [hy]))]

/-- A slice of handle words decodes to their handles. -/
theorem hslice_of {k : IdxKind} (a : Array Word) (o : Nat) (ws : List Word)
    (hw : ∀ j (hj : j < ws.length), a[o + j]? = some ws[j]) (hlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) :
    (hslice? a o ws.length : Option (List (Idx k))) = some (ws.map decI) := by
  unfold hslice?
  rw [rmapM_some_of _ (fun j => (decI (ws.getD j 0) : Idx k)) _ (fun j hj => by
    have hj' := List.mem_range.mp hj
    simp only [hd?, hw j hj', Option.bind_eq_bind, Option.bind_some]
    rw [ite_eq_left (hlt _ (List.getElem_mem hj'))]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'])]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]

/-- **A name slice `(o, c)` at words `d`, `d + 1`** decodes to the handles, from the words read. -/
theorem holds_hlist {k : IdxKind} (m : Mem) (d : Nat) (ow cw : Word) (ws : List Word)
    (hd : (erA m)[d]? = some ow) (hc : (erA m)[d + 1]? = some cw) (hcw : cw.toNat = ws.length)
    (hw : ∀ j (hj : j < ws.length), (erA m)[ow.toNat + j]? = some ws[j])
    (hlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) :
    Holds (fun i => i = d ∨ i = d + 1 ∨ (ow.toNat ≤ i ∧ i < ow.toNat + ws.length)) (fun _ => False)
      (fun m => (hlist? (erA m) d : Option (List (Idx k)))) m (ws.map decI) := by
  intro m' h1 _
  have e1 := (h1 d (.inl rfl)).trans hd
  have e2 := (h1 (d + 1) (.inr (.inl rfl))).trans hc
  simp only [hlist?, nat?, e1, e2, Option.map_some, Option.bind_eq_bind, Option.bind_some, hcw]
  exact hslice_of _ _ ws (fun j hj => (h1 _ (.inr (.inr ⟨by omega, by omega⟩))).trans (hw j hj)) hlt

theorem encNames_len : ∀ ns : List ConLeche.Name, ns.length ≤ (encNames ns).length
  | [] => by simp [encNames]
  | x :: xs => by
    have h1 : 0 < (encName x).length := by cases x <;> simp [encName]
    have := encNames_len xs
    simp only [encNames, List.length_append, List.length_cons]; omega

section namesl
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

/-- **`rci_name_sl` refines `internNameList`** of a counted name list, the slice allocated fresh
and its `(offset, count)` written to `EREC[d]`, `EREC[d + 1]`. -/
theorem nameSl_rel {m₀ : Mem} {a₀ : AState} {T : Nat} (seen : List ConLeche.Expr) (memo : EMemo)
    (ns : List ConLeche.Name) (hfit : ns.all nameFits = true) (k : Nat) (m : Mem) (a : AState)
    (q d : Word) (rest : List UInt8) (r : List Word) (m' : Mem) (hI : RInv m₀ a₀ T m a)
    (hM : MemoR m seen memo) (hd : rom.drop q.toNat = encNameL ns ++ rest)
    (hd0 : erTop m₀ ≤ d.toNat) (hd2 : d.toNat + 2 ≤ erTop m)
    (hc : callW p (k + 1) "rci_name_sl" [q, d] m = some (r, m')) :
    ∃ (ws : List Word) (a' : AState), (Frontend.internNameList ns).run a = .ok (ws.map decI, a') ∧
      (∀ w ∈ ws, w.toNat < 2 ^ 32) ∧
      RInv m₀ a₀ T m' a' ∧ MemoR m' seen memo ∧ stkTop m' = stkTop m ∧
      (r.headD 0).toNat = q.toNat + (encNameL ns).length ∧
      EKeep (fun i => d.toNat ≤ i ∧ i < d.toNat + 2) m m' ∧ erTop m ≤ erTop m' ∧
      m'.arr64 IW = m.arr64 IW ∧
      Holds (fun i => (d.toNat ≤ i ∧ i < d.toNat + 2) ∨ (erTop m ≤ i ∧ i < erTop m')) (fun _ => False)
        (fun m => (hlist? (erA m) d.toNat : Option (List NIdx))) m' (ws.map decI) := by
  have hw := callW_model (M := fun mq => nameSlW p k mq q d) (nameSl_specW rom p hL k · q d) hc
  simp only [nameSlW, rdU] at hw
  obtain ⟨r0, m0, h0, hw⟩ := ntBW_inv hw
  obtain ⟨hm0, hr0⟩ := u64Call hL h0
  rw [hm0, hr0] at hw
  simp only [List.headD_cons] at hw
  have hlenR := drop_len rom _ _ _ hd (by simp [encNameL, u64B])
  have hrom := hr; simp only [RomOK] at hrom
  simp only [encNameL, List.length_append, u64B, List.length_cons, List.length_nil] at hlenR
  have hd' : rom.drop q.toNat = u64B ns.length ++ (encNames ns ++ rest) := by
    rw [hd, encNameL, List.append_assoc]
  have hlen63 : ns.length < 2 ^ 63 := by
    have := encNames_len ns
    omega
  have hc0 : u64W rom q = UInt64.ofNat ns.length := u64W_of_drop rom q _ _ hd' (by omega) hr
  rw [hc0] at hw
  have hcN : (UInt64.ofNat ns.length).toNat = ns.length := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨r1, m1, h1, hw⟩ := ntBW_inv hw
  obtain ⟨hI1, ho1, ht1, hE1, hIW1, -⟩ := hI.erAlloc (erAllocCall hL h1)
  rw [hcN] at ht1
  have hf1 : MemFrame [] [129] m m1 := by
    have := erAllocCall hL h1; simp only [erAllocW] at this
    split at this; · cases this
    split at this; · cases this
    simp only [Option.some.injEq, Prod.mk.injEq] at this; rw [← this.2]; exact MemFrame.setCtl _ _ _
  have hM1 := hM.frameG hf1 (by simp) (by decide)
  have hs1 : stkTop m1 = stkTop m := hf1.2.1 131 (by decide)
  have hlt := hI.er_lt
  have hgo := hI.grow.2.1
  have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hI2 := (hI1.setER d (r1.headD 0) hd0).setER (d + 1) (UInt64.ofNat ns.length) (by omega)
  have hfA := (MemFrame.set64 m1 EREC (by decide) d (r1.headD 0)).trans
    (MemFrame.set64 (m1.set64 EREC d (r1.headD 0)) EREC (by decide) (d + 1) (UInt64.ofNat ns.length))
  have hM2 := hM1.frameG hfA (by decide) (by simp)
  have hC2 : ((m1.set64 EREC d (r1.headD 0)).set64 EREC (d + 1) (UInt64.ofNat ns.length)).arr64 CTL =
      m1.arr64 CTL := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hIW2 : ((m1.set64 EREC d (r1.headD 0)).set64 EREC (d + 1) (UInt64.ofNat ns.length)).arr64 IW =
      m1.arr64 IW := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have ht2 : erTop ((m1.set64 EREC d (r1.headD 0)).set64 EREC (d + 1) (UInt64.ofNat ns.length)) =
      erTop m1 := by simp only [erTop, hC2]
  have hs2 : stkTop ((m1.set64 EREC d (r1.headD 0)).set64 EREC (d + 1) (UInt64.ofNat ns.length)) =
      stkTop m1 := by simp only [stkTop, hC2]
  have hsz1 : erTop m1 ≤ (m1.arr64 EREC).size := hI1.ok.2.1
  have hget2 : ∀ i, (erA ((m1.set64 EREC d (r1.headD 0)).set64 EREC (d + 1) (UInt64.ofNat ns.length)))[i]? =
      if i = d.toNat + 1 then some (UInt64.ofNat ns.length) else if i = d.toNat then some (r1.headD 0)
      else (erA m1)[i]? := by
    intro i
    simp only [erA]
    rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp only [Array.size_setIfInBounds, hd1]
    by_cases e1 : i = d.toNat + 1
    · subst e1; simp; omega
    · by_cases e2 : i = d.toNat
      · subst e2; simp; omega
      · simp [e1, e2, Ne.symm e1, Ne.symm e2]
  have hq8 : (q + 8).toNat = q.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have hdn : rom.drop (q + 8).toNat = encNames ns ++ rest := by
    rw [hq8, ← List.drop_drop, hd']; simp [u64B]
  obtain ⟨r2, m3, h2, hw⟩ := ntBW_inv hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨ws, a', hrun, hwl, hwlt, hwd, hI3, hM3, hs3, hq3, hek3, ht3, hiw3⟩ :=
    namesTo_rel hL hr seen memo ns hfit k _ a _ _ _ rest r2 m3 hI2 hM2 hdn hcN (by omega)
      (by omega) h2
  have hkeep : ∀ i, i < erTop m → (erA m3)[i]? =
      (erA ((m1.set64 EREC d (r1.headD 0)).set64 EREC (d + 1) (UInt64.ofNat ns.length)))[i]? :=
    fun i hi => hek3.2 i (by omega) (by omega)
  have hE1' : ∀ i : Nat, (erA m1)[i]? = (erA m)[i]? := fun i => by unfold erA; rw [hE1]
  refine ⟨ws, a', hrun, hwlt, hI3, hM3, by rw [hs3, hs2, hs1], ?_, ?_, by omega,
    by rw [hiw3, hIW2, hIW1], ?_⟩
  · simp only [List.headD_cons]; rw [hq3, hq8]; simp [encNameL, u64B]; omega
  · refine ⟨by omega, fun i hi hR => ?_⟩
    rw [hkeep i hi, hget2, ite_eq_right (by omega), ite_eq_right (by omega), hE1']
  · have hH := holds_hlist (k := .name) m3 d.toNat (r1.headD 0) (UInt64.ofNat ns.length) ws
      (by rw [hkeep _ (by omega), hget2, ite_eq_right (by omega), ite_eq_left rfl])
      (by rw [hkeep _ (by omega), hget2, ite_eq_left rfl]) (by rw [hcN, hwl]) hwd hwlt
    refine hH.mono (fun i hi => ?_) (fun _ h => h)
    rcases hi with rfl | rfl | ⟨h1, h2⟩
    · left; omega
    · left; omega
    · right; omega

end namesl

end L.Rom
