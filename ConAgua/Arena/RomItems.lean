import ConAgua.Arena.RomExprRef
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The ROM's item streams: one interpreter for every constant datum's store effect

The startup walk (`internAllPins`) and the interning of constants (`internCV`, `internCI`,
`internCIList`, `internCaps`, `internRules`, `internPinSet`, …) are, as far as the store and the
expression memo are concerned, a **sequence of primitive interns**: names, levels, universe
lists, expressions (memoised), and fresh memos. So the ROM holds them as an **item stream**
(`Item`, `encItems`, tags `0` name, `1` level, `2` level list, `3` expression, `4` memo reset,
`5` end) and one L function, `rom_items(pos)`, runs it. Its refinement is against `runItems`, the
twin's primitives folded over the items (here); `RomCI.lean` shows each twin function has the
store effect of its items.
-/

open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Rom

open L.Arena

/-! ## Items and the twin's fold -/

/-- One primitive intern. -/
inductive Item where
  | nm (n : ConLeche.Name)
  | lv (u : ConLeche.Level)
  | lvs (us : List ConLeche.Level)
  | ex (e : ConLeche.Expr)
  | reset

/-- The twin's primitive at the memo `m`; returns the memo after. -/
def runItem (m : EMemo) : Item → AM EMemo
  | .nm n => do let _ ← internName n; pure m
  | .lv u => do let _ ← internLevel u; pure m
  | .lvs us => do let _ ← internLevels us; pure m
  | .ex e => do let r ← internExprGo m e; pure r.1
  | .reset => pure ∅

/-- The items in order. -/
def runItems (m : EMemo) : List Item → AM EMemo
  | [] => pure m
  | i :: is => do let m' ← runItem m i; runItems m' is

/-- Every datum of the item fits its encoding. -/
def itemFits : Item → Bool
  | .nm n => nameFits n
  | .lv u => levelFits u
  | .lvs us => us.all levelFits && decide (us.length < 2 ^ 60)
  | .ex e => exprFits e
  | .reset => true

/-! ## The encoding -/

/-- The items, threading the expression memo's `seen` (a reset empties it); the end tag last. -/
def encItems (seen : List ConLeche.Expr) : List Item → List UInt8
  | [] => [5]
  | .nm n :: is => 0 :: (encName n ++ encItems seen is)
  | .lv u :: is => 1 :: (encLevel u ++ encItems seen is)
  | .lvs us :: is => 2 :: (encLevels us ++ encItems seen is)
  | .ex e :: is => 3 :: ((encExprM seen e).1 ++ encItems (encExprM seen e).2 is)
  | .reset :: is => 4 :: encItems [] is

/-! ## `rom_items(pos)` -/

section prog
variable (rom : List UInt8)

/-- `rom_items(pos)`: run the item stream at `pos`; returns the position after its end tag. -/
-- con-ron: ConRon/Arena/Checker.lean:312-342 ConRon.Arena.internAllPins
def romItems : FunDecl := lfn (pos) locals (t, h, q, r) {
  t := rom.c8[pos];
  if t == 5 { return pos + 1 };
  if t == 4 {
    CTL.u64[132] := 0;
    h := call rset_clear();
    r := call rom_items(pos + 1);
    return r
  };
  if t == 0 { (h, q) := call rom_name(pos + 1) } else if t == 1 { (h, q) := call rom_level(pos + 1) }
  else if t == 2 { (h, q) := call rom_levels(pos + 1) } else if t == 3 { (h, q) := call rom_expr(pos + 1) }
  else { abort };
  r := call rom_items(q);
  return r
}

/-- The memory after a memo reset: the memo and its handle set empty. -/
def resetMem (m : Mem) : Mem := mclearG rsetSch (m.set64 CTL 132 0)

/-- The handle set can be cleared (its stamp does not wrap). -/
def rclearOK (m : Mem) : Prop := rdW ((m.set64 CTL 132 0).arr64 CTL) rsetSch.cs + 2 ≠ 0

instance (m : Mem) : Decidable (rclearOK m) := by unfold rclearOK; infer_instance

/-- After one item: continue at its end. -/
def itK (_n : Nat) (romItemsW : Mem → Word → Option (Word × Mem)) :
    Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (_, q, m₁) => romItemsW m₁ q

/-- **The model of `rom_items`** at L fuel `n`. -/
def romItemsW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, pos =>
    if romB rom pos = 5 then some (pos + 1, m)
    else if romB rom pos = 4 then (if rclearOK m then romItemsW n (resetMem m) (pos + 1) else none)
    else if romB rom pos = 0 then itK n (romItemsW n) (romNameW rom n m (pos + 1))
    else if romB rom pos = 1 then itK n (romItemsW n) (romLevelW rom n m (pos + 1))
    else if romB rom pos = 2 then itK n (romItemsW n) (romLevelsW rom n m (pos + 1))
    else if romB rom pos = 3 then itK n (romItemsW n) (romExprW rom n m (pos + 1))
    else none

end prog

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ : Mem) (pos q h : Word)
theorem itK_some (F : Mem → Word → Option (Word × Mem)) : itK n F (some (h, q, m₁)) = F m₁ q := rfl
theorem romItemsW_end (h5 : romB rom pos = 5) : romItemsW rom (n + 1) m pos = some (pos + 1, m) := by
  simp [romItemsW, h5]
theorem romItemsW_reset (_h5 : romB rom pos ≠ 5) (h4 : romB rom pos = 4) :
    romItemsW rom (n + 1) m pos = if rclearOK m then romItemsW rom n (resetMem m) (pos + 1) else none := by
  simp [romItemsW, h4]
theorem romItemsW_reset_ok (_h5 : romB rom pos ≠ 5) (h4 : romB rom pos = 4) (hok : rclearOK m) :
    romItemsW rom (n + 1) m pos = romItemsW rom n (resetMem m) (pos + 1) := by
  simp [romItemsW, h4, hok]
theorem romItemsW_nm (_h5 : romB rom pos ≠ 5) (_h4 : romB rom pos ≠ 4) (h0 : romB rom pos = 0) :
    romItemsW rom (n + 1) m pos = itK n (romItemsW rom n) (romNameW rom n m (pos + 1)) := by
  simp [romItemsW, h0]
theorem romItemsW_lv (_h5 : romB rom pos ≠ 5) (_h4 : romB rom pos ≠ 4) (_h0 : romB rom pos ≠ 0)
    (h1 : romB rom pos = 1) :
    romItemsW rom (n + 1) m pos = itK n (romItemsW rom n) (romLevelW rom n m (pos + 1)) := by
  simp [romItemsW, h1]
theorem romItemsW_lvs (_h5 : romB rom pos ≠ 5) (_h4 : romB rom pos ≠ 4) (_h0 : romB rom pos ≠ 0)
    (_h1 : romB rom pos ≠ 1) (h2 : romB rom pos = 2) :
    romItemsW rom (n + 1) m pos = itK n (romItemsW rom n) (romLevelsW rom n m (pos + 1)) := by
  simp [romItemsW, h2]
theorem romItemsW_ex (_h5 : romB rom pos ≠ 5) (_h4 : romB rom pos ≠ 4) (_h0 : romB rom pos ≠ 0)
    (_h1 : romB rom pos ≠ 1) (_h2 : romB rom pos ≠ 2) (h3 : romB rom pos = 3) :
    romItemsW rom (n + 1) m pos = itK n (romItemsW rom n) (romExprW rom n m (pos + 1)) := by
  simp [romItemsW, h3]
end arms

attribute [arena_grind =] itK_some
grind_pattern [arena_grind] romItemsW_end => romItemsW rom (n + 1) m pos
grind_pattern [arena_grind] romItemsW_reset_ok => romItemsW rom (n + 1) m pos
grind_pattern [arena_grind] romItemsW_nm => romItemsW rom (n + 1) m pos
grind_pattern [arena_grind] romItemsW_lv => romItemsW rom (n + 1) m pos
grind_pattern [arena_grind] romItemsW_lvs => romItemsW rom (n + 1) m pos
grind_pattern [arena_grind] romItemsW_ex => romItemsW rom (n + 1) m pos

/-- The functions `rom_items` calls. -/
structure ItemsProg (rom : List UInt8) (p : Prog) : Prop extends ExprProg rom p where
  rom_items : p.lookup "rom_items" = some (romItems rom)
  rset_clear : p.lookup "rset_clear" = some (memoClearG rsetSch)

section spec
variable (rom : List UInt8) (p : Prog) (hL : ItemsProg rom p)
include hL

theorem romItems_specW (n : Nat) : ∀ (s₀ : St) (pos : Word),
    pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_items" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ romItemsW rom n s₀.mem pos = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ pos _
    rw [invoke_eq _ hL.rom_items]; simp only [callFn, romItems]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ pos hs
    have ih' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (ih s₁ pos₁ h₁)
    have hn' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (romName_specW rom p hL.toNameProg n s₁ pos₁ h₁)
    have hl' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (romLevel_specW rom p hL.toLevelProg n s₁ pos₁ h₁)
    have hls' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8
      (romLevels_specW rom p hL.toLevelsProg n s₁ pos₁ h₁)
    have he' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8
      ((romExpr_specsW rom p hL.toExprProg n).1 s₁ pos₁ h₁)
    rw [invoke_eq _ hL.rom_items]
    simp only [callFn, romItems]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ldc, st64, hn', hl', hls', he', ih',
        memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n] <;>
      finish [Keep.size, Keep.pcap, resetMem, rclearOK, mclearG, rsetSch]

end spec

/-! ## `rom_items` refines `runItems` -/

theorem RsetR.reset {m : Mem} (hR : RsetR m) (hok : rclearOK m) : RsetR (resetMem m) := by
  obtain ⟨mp, hG, -⟩ := hR
  have hG1 := memoRG_frame rsetSch rsetSch_wf bmKey (fun _ => ()) [] [132] (by simp) (by simp [rsetSch])
    _ _ ((MemFrame.setCtl m 132 0).mono (by simp) (by simp)) mp hG
  have hG2 := memoRG_clear rsetSch rsetSch_wf bmKey (fun _ => ()) _ mp hG1 hok
  refine ⟨_, hG2, fun k hk => ?_⟩
  have hc : memoCnt (resetMem m) = 0 := by
    have := hG.1
    simp only [rsetSch] at this
    simp only [memoCnt, resetMem, mclearG, rsetSch, rdW_set64]
    have h148 : (UInt64.toNat 148) = 148 := rfl
    rw [h148] at this
    simp
    omega
  rw [hc] at hk; simp at hk

theorem resetMem_frame1 (m : Mem) : MemFrame [] [132, 148, 149] m (resetMem m) :=
  ((MemFrame.setCtl m 132 0).mono (by simp) (by simp)).trans
    ((mclearG_frame rsetSch _).mono (by simp) (by simp [rsetSch]))

/-- **`rom_items`'s model keeps the top in a tier.** -/
theorem romItemsW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (pos q : Word) (m' : Mem),
    romItemsW rom n m pos = some (q, m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m pos q m' hW; simp [romItemsW] at hW
  | succ n ih =>
    intro m pos q m' hW
    by_cases h5 : romB rom pos = 5
    · rw [romItemsW_end rom n m pos h5] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    by_cases h4 : romB rom pos = 4
    · rw [romItemsW_reset rom n m pos h5 h4] at hW
      split at hW
      · exact (memFrame_top (resetMem_frame1 m) (by decide)).trans (ih _ _ _ _ hW)
      · simp at hW
    have step : ∀ (r : Option (Word × Word × Mem)), (∀ h q₁ m₁, r = some (h, q₁, m₁) → TopK m m₁) →
        itK n (romItemsW rom n) r = some (q, m') → TopK m m' := by
      intro r hr hK
      cases r with
      | none => simp [itK] at hK
      | some r =>
        obtain ⟨h, q₁, m₁⟩ := r
        rw [itK_some] at hK
        exact (hr h q₁ m₁ rfl).trans (ih _ _ _ _ hK)
    by_cases h0 : romB rom pos = 0
    · rw [romItemsW_nm rom n m pos h5 h4 h0] at hW
      exact step _ (fun _ _ _ hP => romNameW_topK hP) hW
    by_cases h1 : romB rom pos = 1
    · rw [romItemsW_lv rom n m pos h5 h4 h0 h1] at hW
      exact step _ (fun _ _ _ hP => romLevelW_topK hP) hW
    by_cases h2 : romB rom pos = 2
    · rw [romItemsW_lvs rom n m pos h5 h4 h0 h1 h2] at hW
      exact step _ (fun _ _ _ hP => romLevelsW_topK hP) hW
    by_cases h3 : romB rom pos = 3
    · rw [romItemsW_ex rom n m pos h5 h4 h0 h1 h2 h3] at hW
      exact step _ (fun h q₁ m₁ hP => (romExprW_topK rom n).1 m _ h q₁ m₁ hP) hW
    simp [romItemsW, h5, h4, h0, h1, h2, h3] at hW

theorem romItemsW_top' (rom : List UInt8) (n : Nat) (m : Mem) (pos q : Word) (m' : Mem)
    (hW : romItemsW rom n m pos = some (q, m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romItemsW_topK rom n m pos q m' hW hc ht).1
grind_pattern [arena_grind] romItemsW_top' => romItemsW rom n m pos, some (q, m')

theorem MemoR.reset {mem : Mem} {seen : List ConLeche.Expr} {m : EMemo} (h : MemoR mem seen m) :
    MemoR (resetMem mem) [] (∅ : EMemo) := by
  have hf := resetMem_frame1 mem
  have hc0 : memoCnt (resetMem mem) = 0 := by
    simp only [memoCnt, resetMem, mclearG, rsetSch, rdW_set64]
    simp [h.csz]
  refine ⟨by rw [hc0]; rfl, fun k hk => by simp at hk, fun e he => by simp at he, by simp, ?_⟩
  rw [hf.2.2.1]; exact h.csz

theorem resetMem_frame (m : Mem) : MemFrame ExprA ExprC m (resetMem m) :=
  (resetMem_frame1 m).mono (by simp) (by simp [ExprC])

theorem resetMem_stk (m : Mem) : stkTop (resetMem m) = stkTop m :=
  (resetMem_frame1 m).2.1 131 (by simp)

theorem run_bind_of {α β : Type} (x : AM α) (f : α → AM β) (a a' : AState) (v : α)
    (h : x.run a = .ok (v, a')) : (x >>= f).run a = (f v).run a' := by
  rw [StateT.run_bind, h]; rfl

section ref
variable (rom : List UInt8) (hr : RomOK rom)
include hr

set_option linter.constructorNameAsVariable false in
/-- **The model of `rom_items` refines `runItems`.** -/
theorem romItemsW_ok (is : List Item) (hfit : is.all itemFits = true) :
    ∀ (n : Nat) (mem : Mem) (a : AState) (pos : Word) (rest : List UInt8) (seen : List ConLeche.Expr)
      (m : EMemo) (q : Word) (mem' : Mem), ArenaD mem a → ModeOK mem → MemoR mem seen m →
      rom.drop pos.toNat = encItems seen is ++ rest → (stkTop mem).toNat < 2 ^ 61 →
      131 < (mem.arr64 CTL).size → romItemsW rom n mem pos = some (q, mem') →
      ∃ (m' : EMemo) (a' : AState) (seen' : List ConLeche.Expr), (runItems m is).run a = .ok (m', a') ∧
        ArenaD mem' a' ∧ MemoR mem' seen' m' ∧ q.toNat = pos.toNat + (encItems seen is).length ∧
        MemFrame ExprA ExprC mem mem' ∧ stkTop mem' = stkTop mem ∧ (RsetR mem → RsetR mem') := by
  induction is with
  | nil =>
    intro n mem a pos rest seen m q mem' hA hmo hM hd hst hc hW
    simp only [encItems] at hd ⊢
    have h0 : romB rom pos = 5 := romB_head rom hr pos 5 [] rest hd
    cases n with
    | zero => simp [romItemsW] at hW
    | succ n =>
    rw [romItemsW_end rom n mem pos h0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨m, a, seen, rfl, hA, hM, ?_, MemFrame.refl _ _ _, rfl, id⟩
    have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
    simp only [UInt64.ofNat_one] at hp1
    rw [hp1]; simp
  | cons it is ih =>
    intro n mem a pos rest seen m q mem' hA hmo hM hd hst hc hW
    simp only [List.all_cons, Bool.and_eq_true] at hfit
    cases it with
    | reset =>
      simp only [encItems] at hd ⊢
      have h0 : romB rom pos = 4 := romB_head rom hr pos 4 _ rest hd
      cases n with
      | zero => simp [romItemsW] at hW
      | succ n =>
      rw [romItemsW_reset rom n mem pos (by simp [h0]) h0] at hW
      split at hW
      case isFalse => simp at hW
      have hd1 : rom.drop (pos + 1).toNat = encItems [] is ++ rest := by
        have := drop_shift rom hr pos [4] (encItems [] is) rest (by simpa using hd)
          (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
        simpa using this
      obtain ⟨m', a', seen', r, hR, hM', hq, hf, hs, hz⟩ := ih hfit.2 n (resetMem mem) a (pos + 1) rest [] ∅ q mem'
        (ArenaD.frameHi (resetMem_frame1 mem) (by simp) (by simp) hA)
        ((memFrame_top (resetMem_frame1 mem) (by decide)).mode hA.1.lit.1 hmo) hM.reset hd1
        (by rw [resetMem_stk]; exact hst) (by rw [(resetMem_frame1 mem).2.2.1]; exact hc) hW
      refine ⟨m', a', seen', by simp only [runItems, runItem]; rw [run_bind_of _ _ _ _ _ rfl]; exact r,
        hR, hM', ?_, (resetMem_frame mem).trans hf, by rw [hs, resetMem_stk],
        fun h0 => hz (h0.reset (by assumption))⟩
      have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
      simp only [UInt64.ofNat_one] at hp1
      rw [hq, hp1]; simp; omega
    | nm nme =>
      simp only [encItems, itemFits] at hd hfit ⊢
      have h0 : romB rom pos = 0 := romB_head rom hr pos 0 _ rest hd
      cases n with
      | zero => simp [romItemsW] at hW
      | succ n =>
      rw [romItemsW_nm rom n mem pos (by simp [h0]) (by simp [h0]) h0] at hW
      have hd1 : rom.drop (pos + 1).toNat = encName nme ++ (encItems seen is ++ rest) := by
        have := drop_shift rom hr pos [0] (encName nme ++ encItems seen is) rest (by simpa using hd)
          (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
        simpa using this
      cases hN : romNameW rom n mem (pos + 1) with
      | none => rw [hN] at hW; simp [itK] at hW
      | some r =>
      obtain ⟨h₁, q₁, m₁⟩ := r
      rw [hN, itK_some] at hW
      obtain ⟨ok1, hR1, -, -, hq1, hf1⟩ := romNameW_ok rom hr nme hfit.1 n mem a (pos + 1) _ h₁ q₁ m₁ hA hmo hd1 hN
      have hd2 : rom.drop q₁.toNat = encItems seen is ++ rest :=
        drop_shift rom hr (pos + 1) _ _ rest (by rw [hd1, List.append_assoc]) q₁ hq1
      obtain ⟨m', a', seen', r, hR, hM', hq, hf, hs, hz⟩ := ih hfit.2 n m₁ _ q₁ rest seen m q mem' hR1
        ((romNameW_topK hN).mode hA.1.lit.1 hmo) (hM.frame (frame_romA hf1)) hd2 (by rw [frame_exprA_stk hf1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hW
      refine ⟨m', a', seen', ?_, hR, hM', ?_, (frame_storeE hf1).trans hf, by rw [hs, frame_exprA_stk hf1],
        fun h0 => hz (h0.frameS hf1)⟩
      · simp only [runItems, runItem]
        rw [run_bind_of _ _ _ _ m (by rw [run_bind_of _ _ _ _ _ (AM.run_of_ok _ _ ok1)]; rfl)]; exact r
      · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
        simp only [UInt64.ofNat_one] at hp1
        rw [hq, hq1, hp1]; simp; omega
    | lv u =>
      simp only [encItems, itemFits] at hd hfit ⊢
      have h0 : romB rom pos = 1 := romB_head rom hr pos 1 _ rest hd
      cases n with
      | zero => simp [romItemsW] at hW
      | succ n =>
      rw [romItemsW_lv rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]) h0] at hW
      have hd1 : rom.drop (pos + 1).toNat = encLevel u ++ (encItems seen is ++ rest) := by
        have := drop_shift rom hr pos [1] (encLevel u ++ encItems seen is) rest (by simpa using hd)
          (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
        simpa using this
      cases hN : romLevelW rom n mem (pos + 1) with
      | none => rw [hN] at hW; simp [itK] at hW
      | some r =>
      obtain ⟨h₁, q₁, m₁⟩ := r
      rw [hN, itK_some] at hW
      obtain ⟨ok1, hR1, -, -, hq1, hf1⟩ := romLevelW_ok rom hr u hfit.1 n mem a (pos + 1) _ h₁ q₁ m₁ hA hmo hd1 hN
      have hd2 : rom.drop q₁.toNat = encItems seen is ++ rest :=
        drop_shift rom hr (pos + 1) _ _ rest (by rw [hd1, List.append_assoc]) q₁ hq1
      obtain ⟨m', a', seen', r, hR, hM', hq, hf, hs, hz⟩ := ih hfit.2 n m₁ _ q₁ rest seen m q mem' hR1
        ((romLevelW_topK hN).mode hA.1.lit.1 hmo) (hM.frame (frame_romA hf1)) hd2 (by rw [frame_exprA_stk hf1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hW
      refine ⟨m', a', seen', ?_, hR, hM', ?_, (frame_storeE hf1).trans hf, by rw [hs, frame_exprA_stk hf1],
        fun h0 => hz (h0.frameS hf1)⟩
      · simp only [runItems, runItem]
        rw [run_bind_of _ _ _ _ m (by rw [run_bind_of _ _ _ _ _ (AM.run_of_ok _ _ ok1)]; rfl)]; exact r
      · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
        simp only [UInt64.ofNat_one] at hp1
        rw [hq, hq1, hp1]; simp; omega
    | lvs us =>
      simp only [encItems, itemFits, Bool.and_eq_true, decide_eq_true_eq] at hd hfit ⊢
      have h0 : romB rom pos = 2 := romB_head rom hr pos 2 _ rest hd
      cases n with
      | zero => simp [romItemsW] at hW
      | succ n =>
      rw [romItemsW_lvs rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]) (by simp [h0]) h0] at hW
      have hd1 : rom.drop (pos + 1).toNat = encLevels us ++ (encItems seen is ++ rest) := by
        have := drop_shift rom hr pos [2] (encLevels us ++ encItems seen is) rest (by simpa using hd)
          (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
        simpa using this
      cases hN : romLevelsW rom n mem (pos + 1) with
      | none => rw [hN] at hW; simp [itK] at hW
      | some r =>
      obtain ⟨h₁, q₁, m₁⟩ := r
      rw [hN, itK_some] at hW
      obtain ⟨ok1, hR1, -, -, hq1, hf1, hs1⟩ := romLevelsW_ok rom hr us hfit.1.1 n mem a (pos + 1) _ h₁ q₁ m₁ hA hmo hd1
        (by omega) hc hN
      have hd2 : rom.drop q₁.toNat = encItems seen is ++ rest :=
        drop_shift rom hr (pos + 1) _ _ rest (by rw [hd1, List.append_assoc]) q₁ hq1
      obtain ⟨m', a', seen', r, hR, hM', hq, hf, hs, hz⟩ := ih hfit.2 n m₁ _ q₁ rest seen m q mem' hR1
        ((romLevelsW_topK hN).mode hA.1.lit.1 hmo) (hM.frame hf1) hd2 (by rw [hs1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hW
      refine ⟨m', a', seen', ?_, hR, hM', ?_, (frame_exprA hf1).trans hf, by rw [hs, hs1],
        fun h0 => hz (h0.frameR hf1)⟩
      · simp only [runItems, runItem]
        rw [run_bind_of _ _ _ _ m (by rw [run_bind_of _ _ _ _ _ (AM.run_of_ok _ _ ok1)]; rfl)]; exact r
      · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
        simp only [UInt64.ofNat_one] at hp1
        rw [hq, hq1, hp1]; simp; omega
    | ex e =>
      simp only [encItems, itemFits] at hd hfit ⊢
      have h0 : romB rom pos = 3 := romB_head rom hr pos 3 _ rest hd
      cases n with
      | zero => simp [romItemsW] at hW
      | succ n =>
      rw [romItemsW_ex rom n mem pos (by simp [h0]) (by simp [h0]) (by simp [h0]) (by simp [h0])
        (by simp [h0]) h0] at hW
      have hd1 : rom.drop (pos + 1).toNat = (encExprM seen e).1 ++ (encItems (encExprM seen e).2 is ++ rest) := by
        have := drop_shift rom hr pos [3] ((encExprM seen e).1 ++ encItems (encExprM seen e).2 is) rest
          (by simpa using hd) (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp))
        simpa using this
      cases hN : romExprW rom n mem (pos + 1) with
      | none => rw [hN] at hW; simp [itK] at hW
      | some r =>
      obtain ⟨h₁, q₁, m₁⟩ := r
      rw [hN, itK_some] at hW
      obtain ⟨me, a₁, r1, hR1, hM1, -, hq1, hf1, hs1, hz1⟩ := romExprW_ok rom hr e hfit.1 n mem a (pos + 1) _ seen m
        h₁ q₁ m₁ hA hmo hM hd1 hst hc hN
      have hd2 : rom.drop q₁.toNat = encItems (encExprM seen e).2 is ++ rest :=
        drop_shift rom hr (pos + 1) _ _ rest (by rw [hd1, List.append_assoc]) q₁ hq1
      obtain ⟨m', a', seen', r, hR, hM', hq, hf, hs, hz⟩ := ih hfit.2 n m₁ a₁ q₁ rest _ me q mem' hR1
        (((romExprW_topK rom n).1 _ _ _ _ _ hN).mode hA.1.lit.1 hmo) hM1 hd2
        (by rw [hs1]; exact hst) (by rw [hf1.2.2.1]; exact hc) hW
      refine ⟨m', a', seen', ?_, hR, hM', ?_, hf1.trans hf, by rw [hs, hs1], fun h0 => hz (hz1 h0)⟩
      · simp only [runItems, runItem]
        rw [run_bind_of _ _ _ _ me (by rw [run_bind_of _ _ _ _ _ r1]; rfl)]; exact r
      · have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp)
        simp only [UInt64.ofNat_one] at hp1
        rw [hq, hq1, hp1]; simp; omega

end ref

end L.Rom
