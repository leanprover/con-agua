module

public import ConAgua.Rom.CIReadRefBase
import ConAgua.Rom.CIReadRefW
public import ConAgua.Rom.CIReadSpec

@[expose] public section

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
theorem MemoR.frameG {A : List TieredArray} {C : List Word} {mem mem' : Mem} {seen : List ConLeche.Expr}
    {m : EMemo} (h : MemoR mem seen m) (hf : MemFrame A C mem mem') (hA : (RMEMO : TieredArray) ∉ A)
    (hC : (132 : Word) ∉ C) : MemoR mem' seen m := by
  have hR : mem'.arr64 RMEMO = mem.arr64 RMEMO := hf.arr RMEMO hA (by decide)
  have hc : memoCnt mem' = memoCnt mem := hf.ctl 132 hC
  exact ⟨by rw [hc]; exact h.cnt, fun k hk => by rw [hR]; exact h.ent k hk, h.keys, h.room,
    by rw [hf.size]; exact h.csz⟩

section calls
variable {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) (hr : RomOK rom)
include hL hr

theorem nameCall (x : ConLeche.Name) (hx : nameFits x = true) {n : Nat} {m m' : Mem} {a : AState}
    {pos : Word} {rest : List UInt8} {r : List Word} (hA : ArenaD m a) (hmo : ModeOK m)
    (hd : rom.drop pos.toNat = encName x ++ rest) (hc : callW p n "rom_name_c" [pos] m = some (r, m')) :
    ∃ a', (internName x).run a = .ok (decI (r.headD 0), a') ∧ ArenaD m' a' ∧ cp a' = cp a ∧
      (r.headD 0).toNat < 2 ^ 32 ∧ (r.tail.headD 0).toNat = pos.toNat + (encName x).length ∧
      MemFrame StoreA StoreC m m' ∧ ModeOK m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (triple_renameCalls (g := "rom_name") hL.ren (by decide)
      (romName_specW rom _ hL.via.toNameProg n _ pos ⟨hA.base.lit.1.cap, hA.base.lit.1.top41⟩)) hc
  obtain ⟨ok, hR, res, hlt, hq, hf⟩ := romNameW_ok rom hr x hx n _ a pos rest _ _ _ hA hmo hd hW
  have hrun := AM.run_of_ok _ _ ok
  rw [res] at hrun
  exact ⟨_, hrun, hR, (keeps_internName x).run hrun, hlt, hq, hf, (romNameW_topK hW).mode hA.base.lit.1 hmo⟩

theorem exprCall (e : ConLeche.Expr) (he : exprFits e = true) {n : Nat} {mem mem' : Mem} {a : AState}
    {pos : Word} {rest : List UInt8} {seen : List ConLeche.Expr} {memo : EMemo} {r : List Word}
    (hA : ArenaD mem a) (hmo : ModeOK mem) (hM : MemoR mem seen memo) (hd : rom.drop pos.toNat = (encExprM seen e).1 ++ rest)
    (hst : (stkTop mem).toNat < 2 ^ 61) (hcs : 131 < (mem.arr64 CTL).size)
    (hc : callW p n "rom_expr_c" [pos] mem = some (r, mem')) :
    ∃ (memo' : EMemo) (a' : AState), (internExprGo memo e).run a = .ok ((memo', decI (r.headD 0)), a') ∧
      ArenaD mem' a' ∧ cp a' = cp a ∧ MemoR mem' (encExprM seen e).2 memo' ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (r.tail.headD 0).toNat = pos.toNat + (encExprM seen e).1.length ∧ MemFrame ExprA ExprC mem mem' ∧
      stkTop mem' = stkTop mem ∧ ModeOK mem' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨mem, Locals.init []⟩)
    (triple_renameCalls (g := "rom_expr") hL.ren (by decide)
      ((romExpr_specsW rom _ hL.via n).1 _ pos ⟨hA.base.lit.1.cap, hA.base.lit.1.top41⟩)) hc
  obtain ⟨memo', a', hrun, hR, hM', hlt, hq, hf, hs, -⟩ :=
    romExprW_ok rom hr e he n _ a pos rest seen memo _ _ _ hA hmo hM hd hst hcs hW
  exact ⟨memo', a', hrun, hR, (keeps_internExprGo e memo).run hrun, hM', hlt, hq, hf, hs,
    ((romExprW_topK rom n).1 _ _ _ _ _ hW).mode hA.base.lit.1 hmo⟩

end calls

theorem u64Call {rom : List UInt8} {p : Prog} (hL : RomCIProg rom p) {n : Nat} {m m' : Mem}
    {i : Word} {r : List Word} (hc : callW p n "rom_u64_c" [i] m = some (r, m')) :
    m' = m ∧ r = [u64W rom i] := by
  obtain ⟨s', rfl, hs, -, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (triple_renameCalls (g := "rom_u64") hL.ren (by decide) (romU64_spec rom _ hL.via.rom_u64 n _ i)) hc
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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The word just written. -/
theorem er_set_get (m : Mem) (i w : Word) (hi : i.toNat < (m.arr64 EREC).size) :
    (erA (m.set64 EREC i w))[i.toNat]? = some w := by
  simp only [erA]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hi]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem iw_set_get (m : Mem) (i w : Word) (hi : i.toNat < (m.arr64 IW).size) :
    (iwA (m.set64 IW i w))[i.toNat]? = some w := by
  simp only [iwA]
  rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hi]
-/

theorem RInv.er_lt {m₀ m : Mem} {a₀ a : AState} {T : Nat} (h : RInv m₀ a₀ T m a) : erTop m < 2 ^ 64 := by
  have := h.ok.er; have := h.ok.erSize; omega

theorem RInv.iw_lt {m₀ m : Mem} {a₀ a : AState} {T : Nat} (h : RInv m₀ a₀ T m a) : iwTop m < 2 ^ 64 := by
  have := h.ok.iw; have := h.ok.iwSize; omega

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
        (∀ j (hj : j < ws.length), erA m' (o.toNat + j) = some ws[j]) ∧
        RInv m₀ a₀ T m' a' ∧ MemoR m' seen memo ∧ stkTop m' = stkTop m ∧
        (r.headD 0).toNat = q.toNat + (encNames ns).length ∧
        EKeep (fun i => o.toNat ≤ i ∧ i < o.toNat + ns.length) m m' ∧ erTop m' = erTop m ∧
        m'.arr64 IW = m.arr64 IW := by
  sorry
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
    (hslice? (aread a) o ws.length : Option (List (Idx k))) = some (ws.map decI) := by
  sorry

/-- **A name slice `(o, c)` at words `d`, `d + 1`** decodes to the handles, from the words read. -/
theorem holds_hlist {k : IdxKind} (m : Mem) (d : Nat) (ow cw : Word) (ws : List Word)
    (hd : erA m d = some ow) (hc : erA m (d + 1) = some cw) (hcw : cw.toNat = ws.length)
    (hw : ∀ j (hj : j < ws.length), erA m (ow.toNat + j) = some ws[j])
    (hlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) :
    Holds (fun i => i = d ∨ i = d + 1 ∨ (ow.toNat ≤ i ∧ i < ow.toNat + ws.length)) (fun _ => False)
      (fun m => (hlist? (erA m) d : Option (List (Idx k)))) m (ws.map decI) := by
  sorry

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
  sorry

end namesl

end L.Rom
