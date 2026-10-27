import ConAgua.Arena.Rom
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The ROM's levels: `rom_level(pos)` refines `internLevel`

`encLevel`: a tag byte (`0` zero, `1` succ, `2` max, `3` imax, `4` param), the children in the
twin's intern order (`internLevel` interns `u` before `v`, a parameter's name before the node),
nothing else. `rom_level(pos)` interns the level encoded at `pos` and returns the handle and the
position after it (the W-model `romLevelW`, then `romLevelW_ok` by induction on the level over
the front's `zero_A`, `succ_A`, `max_A`, `imax_A`, `param_A`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Rom

open L.Arena

/-! ## The encoding -/

/-- A level, children first in the twin's order. -/
def encLevel : ConLeche.Level → List UInt8
  | .zero => [0]
  | .succ u => 1 :: encLevel u
  | .max u v => 2 :: (encLevel u ++ encLevel v)
  | .imax u v => 3 :: (encLevel u ++ encLevel v)
  | .param n => 4 :: encName n

/-- Every name of the level fits its encoding. -/
def levelFits : ConLeche.Level → Bool
  | .zero => true
  | .succ u => levelFits u
  | .max u v | .imax u v => levelFits u && levelFits v
  | .param n => nameFits n

/-! ## `rom_level(pos)` and its model -/

section prog
variable (rom : List UInt8)

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
def romLevel : FunDecl := lfn (pos) locals (t, h, q, u, v) {
  t := rom.c8[pos];
  if t == 0 {
    h := call intern_zero();
    if h >= 4294967296 { abort };
    return (h, pos + 1)
  };
  if t == 4 {
    (u, q) := call rom_name(pos + 1);
    h := call intern_param(u);
    if h >= 4294967296 { abort };
    return (h, q)
  };
  (u, q) := call rom_level(pos + 1);
  if t == 1 {
    h := call intern_succ(u);
    if h >= 4294967296 { abort };
    return (h, q)
  };
  (v, q) := call rom_level(q);
  if t == 2 {
    h := call intern_max(u, v);
    if h >= 4294967296 { abort };
    return (h, q)
  };
  if t != 3 { abort };
  h := call intern_imax(u, v);
  if h >= 4294967296 { abort };
  return (h, q)
}

/-- A node interned: the handle checked, the position given. -/
def lvNodeK (q : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h, m') => if 4294967296 ≤ h then none else some (h, q, m')

/-- After a parameter's name. -/
def lvParamK : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (u, q, m₁) => lvNodeK q (pinternW m₁ u)

/-- After the second child. -/
def lvTwoK (t u : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (v, q, m₂) =>
    if t = 2 then lvNodeK q (minternW m₂ u v)
    else if t = 3 then lvNodeK q (iminternW m₂ u v)
    else none

mutual
/-- **The model of `rom_level`** at L fuel `n`. -/
def romLevelW : Nat → Mem → Word → Option (Word × Word × Mem)
  | 0, _, _ => none
  | n + 1, m, pos =>
    if romB rom pos = 0 then lvNodeK (pos + 1) (zinternW m)
    else if romB rom pos = 4 then lvParamK (romNameW rom n m (pos + 1))
    else lvOneK n (romB rom pos) (romLevelW n m (pos + 1))

/-- After the first child. -/
def lvOneK (n : Nat) (t : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (u, q, m₁) =>
    if t = 1 then lvNodeK q (sinternW m₁ u)
    else lvTwoK t u (romLevelW n m₁ q)
end

end prog

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ : Mem) (pos q t u v h : Word)
theorem lvNodeK_some (hh : ¬ 4294967296 ≤ h) : lvNodeK q (some (h, m)) = some (h, q, m) := by
  simp [lvNodeK, hh]
theorem lvParamK_some : lvParamK (some (u, q, m)) = lvNodeK q (pinternW m u) := rfl
theorem lvTwoK_max (ht : t = 2) : lvTwoK t u (some (v, q, m)) = lvNodeK q (minternW m u v) := by
  simp [lvTwoK, ht]
theorem lvTwoK_imax (ht : t = 3) : lvTwoK t u (some (v, q, m)) = lvNodeK q (iminternW m u v) := by
  simp [lvTwoK, ht]
theorem romLevelW_zero (h0 : romB rom pos = 0) :
    romLevelW rom (n + 1) m pos = lvNodeK (pos + 1) (zinternW m) := by simp [romLevelW, h0]
theorem romLevelW_param (_h0 : romB rom pos ≠ 0) (h4 : romB rom pos = 4) :
    romLevelW rom (n + 1) m pos = lvParamK (romNameW rom n m (pos + 1)) := by
  simp [romLevelW, h4]
theorem romLevelW_rec (h0 : romB rom pos ≠ 0) (h4 : romB rom pos ≠ 4) :
    romLevelW rom (n + 1) m pos = lvOneK rom n (romB rom pos) (romLevelW rom n m (pos + 1)) := by
  simp [romLevelW, h0, h4]
theorem lvOneK_succ (ht : t = 1) : lvOneK rom n t (some (u, q, m)) = lvNodeK q (sinternW m u) := by
  simp [lvOneK, ht]
theorem lvOneK_two (ht : t ≠ 1) :
    lvOneK rom n t (some (u, q, m)) = lvTwoK t u (romLevelW rom n m q) := by simp [lvOneK, ht]
end arms

attribute [arena_grind =] lvNodeK_some lvParamK_some lvTwoK_max lvTwoK_imax lvOneK_succ lvOneK_two
grind_pattern [arena_grind] romLevelW_zero => romLevelW rom (n + 1) m pos
grind_pattern [arena_grind] romLevelW_param => romLevelW rom (n + 1) m pos
grind_pattern [arena_grind] romLevelW_rec => romLevelW rom (n + 1) m pos

/-! ## `rom_level`'s model keeps the top in a tier -/

theorem lvNodeK_eq {q h q' : Word} {r : Option (Word × Mem)} {m' : Mem}
    (hW : lvNodeK q r = some (h, q', m')) : r = some (h, m') := by
  cases r with
  | none => simp [lvNodeK] at hW
  | some r =>
    obtain ⟨w, m₁⟩ := r
    simp only [lvNodeK] at hW
    split at hW
    · simp at hW
    · simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, -, rfl⟩ := hW; rfl

theorem romLevelW_top (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem),
    romLevelW rom n m pos = some (h, q, m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m pos h q m' hW; simp [romLevelW] at hW
  | succ n ih =>
    intro m pos h q m' hW
    by_cases h0 : romB rom pos = 0
    · rw [romLevelW_zero rom n m pos h0] at hW
      exact cons_topK zeroCS_wf (by decide) (by decide) (lvNodeK_eq hW)
    by_cases h4 : romB rom pos = 4
    · rw [romLevelW_param rom n m pos h0 h4] at hW
      cases hP : romNameW rom n m (pos + 1) with
      | none => rw [hP] at hW; simp [lvParamK] at hW
      | some r =>
        obtain ⟨u, q₁, m₁⟩ := r
        rw [hP, lvParamK_some] at hW
        exact (romNameW_topK hP).trans (cons_topK paramCS_wf (by decide) (by decide) (lvNodeK_eq hW))
    rw [romLevelW_rec rom n m pos h0 h4] at hW
    cases hP : romLevelW rom n m (pos + 1) with
    | none => rw [hP] at hW; simp [lvOneK] at hW
    | some r =>
      obtain ⟨u, q₁, m₁⟩ := r
      have k1 := ih m (pos + 1) u q₁ m₁ hP
      rw [hP] at hW
      by_cases h1 : romB rom pos = 1
      · rw [lvOneK_succ rom n m₁ q₁ _ u h1] at hW
        exact k1.trans (cons_topK succCS_wf (by decide) (by decide) (lvNodeK_eq hW))
      rw [lvOneK_two rom n m₁ q₁ _ u h1] at hW
      cases hQ : romLevelW rom n m₁ q₁ with
      | none => rw [hQ] at hW; simp [lvTwoK] at hW
      | some r =>
        obtain ⟨v, q₂, m₂⟩ := r
        have k2 := k1.trans (ih m₁ q₁ v q₂ m₂ hQ)
        rw [hQ] at hW
        by_cases h2 : romB rom pos = 2
        · rw [lvTwoK_max m₂ q₂ _ u v h2] at hW
          exact k2.trans (cons_topK maxCS_wf (by decide) (by decide) (lvNodeK_eq hW))
        by_cases h3 : romB rom pos = 3
        · rw [lvTwoK_imax m₂ q₂ _ u v h3] at hW
          exact k2.trans (cons_topK imaxCS_wf (by decide) (by decide) (lvNodeK_eq hW))
        simp [lvTwoK, h2, h3] at hW

theorem romLevelW_topK {rom : List UInt8} {n : Nat} {m : Mem} {pos h q : Word} {m' : Mem}
    (hW : romLevelW rom n m pos = some (h, q, m')) : TopK m m' := romLevelW_top rom n m pos h q m' hW

theorem romLevelW_top' (rom : List UInt8) (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem)
    (hW : romLevelW rom n m pos = some (h, q, m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romLevelW_top rom n m pos h q m' hW hc ht).1
grind_pattern [arena_grind] romLevelW_top' => romLevelW rom n m pos, some (h, q, m')

/-- The functions `rom_level` calls. -/
structure LevelProg (rom : List UInt8) (p : Prog) : Prop extends NameProg rom p where
  rom_level : p.lookup "rom_level" = some (romLevel rom)
  zero_find : p.lookup "zero_find" = some zeroFind
  zero_push : p.lookup "zero_push" = some zeroPush
  intern_zero : p.lookup "intern_zero" = some internZero
  succ_find : p.lookup "succ_find" = some succFind
  succ_push : p.lookup "succ_push" = some succPush
  intern_succ : p.lookup "intern_succ" = some internSucc
  max_find : p.lookup "max_find" = some maxFind
  max_push : p.lookup "max_push" = some maxPush
  intern_max : p.lookup "intern_max" = some internMax
  imax_find : p.lookup "imax_find" = some imaxFind
  imax_push : p.lookup "imax_push" = some imaxPush
  intern_imax : p.lookup "intern_imax" = some internImax
  param_find : p.lookup "param_find" = some paramFind
  param_push : p.lookup "param_push" = some paramPush
  intern_param : p.lookup "intern_param" = some internParam

section spec
variable (rom : List UInt8) (p : Prog) (hL : LevelProg rom p)
include hL

/-- **`rom_level` computes its model.** -/
theorem romLevel_specW (n : Nat) : ∀ (s₀ : St) (pos : Word),
    pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_level" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ romLevelW rom n s₀.mem pos = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ pos _
    rw [invoke_eq _ hL.rom_level]; simp only [callFn, romLevel]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ pos hs
    have ih' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (ih s₁ pos₁ h₁)
    have hn' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (romName_specW rom p hL.toNameProg n s₁ pos₁ h₁)
    rw [invoke_eq _ hL.rom_level]
    simp only [callFn, romLevel]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ldc,
        internZero_spec p hL.zero_find hL.zero_push hL.intern_zero n,
        internSucc_spec p hL.succ_find hL.succ_push hL.intern_succ n,
        internMax_spec p hL.max_find hL.max_push hL.intern_max n,
        internImax_spec p hL.imax_find hL.imax_push hL.intern_imax n,
        internParam_spec p hL.param_find hL.param_push hL.intern_param n, hn', ih'] <;>
      finish [Keep.size, Keep.pcap]

end spec

/-! ## `rom_level` refines `internLevel` -/

/-- Facts of a bind from facts of its two halves. -/
theorem AM.bind_facts {α β : Type} [Inhabited α] [Inhabited β] (x : AM α) (f : α → AM β) (a : AState)
    (ok1 : AM.ok x a) (ok2 : AM.ok (f (AM.res x a)) (AM.st x a)) :
    AM.ok (x >>= f) a ∧ AM.st (x >>= f) a = AM.st (f (AM.res x a)) (AM.st x a) ∧
      AM.res (x >>= f) a = AM.res (f (AM.res x a)) (AM.st x a) := by
  have ok : AM.ok (x >>= f) a := by rw [AM.ok_bind]; exact ⟨ok1, ok2⟩
  exact ⟨ok, AM.st_bind _ _ _ ok, AM.res_bind _ _ _ ok1⟩


section ref
variable (rom : List UInt8) (hr : RomOK rom)
include hr

omit hr in
/-- One node interned by a store function, under `ArenaD`: the twin's step, the frame. -/
theorem lvNode_ok (op : AM LIdx) (W : Mem → Option (Word × Mem))
    (hop : ∀ m a w m', ArenaD m a → W m = some (w, m') →
      AM.ok op a ∧ ArenaD m' (AM.st op a) ∧ AM.res op a = decI w ∧ MemFrame StoreA StoreC m m')
    (m : Mem) (a : AState) (q h q' : Word) (m' : Mem) (hA : ArenaD m a)
    (hW : lvNodeK q (W m) = some (h, q', m')) :
    AM.ok op a ∧ ArenaD m' (AM.st op a) ∧ AM.res op a = decI h ∧ h.toNat < 2 ^ 32 ∧ q' = q ∧
      MemFrame StoreA StoreC m m' := by
  cases hI : W m with
  | none => rw [hI] at hW; simp [lvNodeK] at hW
  | some r =>
    obtain ⟨w, m₁⟩ := r
    rw [hI] at hW
    simp only [lvNodeK] at hW
    split at hW
    · simp at hW
    rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    obtain ⟨ok, hR, res, hf⟩ := hop m a _ _ hA hI
    exact ⟨ok, hR, res, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, rfl, hf⟩

set_option linter.constructorNameAsVariable false in
/-- **The model of `rom_level` refines `internLevel`**: from `ArenaD`, at the encoding of `l`. -/
theorem romLevelW_ok (l : ConLeche.Level) (hl : levelFits l = true) :
    ∀ (n : Nat) (m : Mem) (a : AState) (pos : Word) (rest : List UInt8) (h q : Word) (m' : Mem),
    ArenaD m a → ModeOK m → rom.drop pos.toNat = encLevel l ++ rest → romLevelW rom n m pos = some (h, q, m') →
    AM.ok (internLevel l) a ∧ ArenaD m' (AM.st (internLevel l) a) ∧ AM.res (internLevel l) a = decI h ∧
    h.toNat < 2 ^ 32 ∧ q.toNat = pos.toNat + (encLevel l).length ∧ MemFrame StoreA StoreC m m' := by
  induction l with
  | zero =>
    intro n m a pos rest h q m' hA hmo hd hW
    have h0 : romB rom pos = 0 := romB_head rom pos 0 [] rest hd
    cases n with
    | zero => simp [romLevelW] at hW
    | succ n =>
    rw [romLevelW_zero rom n m pos h0] at hW
    obtain ⟨ok, hR, res, hlt, rfl, hf⟩ := lvNode_ok (internLNode .zero) zinternW
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.zero_A m a hA w m' hI
        exact ⟨ok, hR, res, frame_store hf (by simp [zeroSch, ZREC, ZSLOT]) (by simp [zeroSch])⟩)
      m a (pos + 1) h q m' hA hW
    exact ⟨ok, hR, res, hlt, drop_pos rom hr pos _ rest hd 1 (by simp [encLevel]), hf⟩
  | param nm =>
    intro n m a pos rest h q m' hA hmo hd hW
    simp only [levelFits] at hl
    have h0 : romB rom pos = 4 := romB_head rom pos 4 _ rest hd
    cases n with
    | zero => simp [romLevelW] at hW
    | succ n =>
    rw [romLevelW_param rom n m pos (by simp [h0]) h0] at hW
    have hd1 : rom.drop (pos + 1).toNat = encName nm ++ rest := by
      have := drop_shift rom pos [4] (encName nm) rest (by simpa [encLevel] using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp [encLevel]))
      simpa using this
    cases hN : romNameW rom n m (pos + 1) with
    | none => rw [hN] at hW; simp [lvParamK] at hW
    | some r =>
    obtain ⟨u, q₁, m₁⟩ := r
    rw [hN, lvParamK_some] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romNameW_ok rom hr nm hl n m a (pos + 1) rest u q₁ m₁ hA hmo hd1 hN
    obtain ⟨ok2, hR2, res2, hlt2, rfl, hf2⟩ := lvNode_ok (internLNode (.param (decI u))) (fun m => pinternW m u)
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.param_A m a hA w m' u hlt1 hI
        exact ⟨ok, hR, res, frame_store hf (by simp [paramSch, PREC, PSLOT]) (by simp [paramSch])⟩)
      m₁ _ q₁ h q m' hR1 hW
    rw [← res1] at ok2 hR2 res2
    obtain ⟨okX, stX, resX⟩ := AM.bind_facts _ (fun hn => internLNode (.param hn)) a ok1 ok2
    have e : internLevel (.param nm) = internName nm >>= fun hn => internLNode (.param hn) := rfl
    refine ⟨e ▸ okX, by rw [e, stX]; exact hR2, by rw [e, resX]; exact res2, hlt2, ?_, hf1.trans hf2⟩
    have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp [encLevel])
    simp only [UInt64.ofNat_one] at hp1
    rw [hq1, hp1]; simp [encLevel]; omega
  | succ u ih =>
    intro n m a pos rest h q m' hA hmo hd hW
    simp only [levelFits] at hl
    have h0 : romB rom pos = 1 := romB_head rom pos 1 _ rest hd
    cases n with
    | zero => simp [romLevelW] at hW
    | succ n =>
    rw [romLevelW_rec rom n m pos (by simp [h0]) (by simp [h0])] at hW
    have hd1 : rom.drop (pos + 1).toNat = encLevel u ++ rest := by
      have := drop_shift rom pos [1] (encLevel u) rest (by simpa [encLevel] using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp [encLevel]))
      simpa using this
    cases hU : romLevelW rom n m (pos + 1) with
    | none => rw [hU] at hW; simp [lvOneK] at hW
    | some r =>
    obtain ⟨hu, q₁, m₁⟩ := r
    rw [hU, h0, lvOneK_succ rom n _ _ _ _ rfl] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := ih hl n m a (pos + 1) rest hu q₁ m₁ hA hmo hd1 hU
    obtain ⟨ok2, hR2, res2, hlt2, rfl, hf2⟩ := lvNode_ok (internLNode (.succ (decI hu))) (fun m => sinternW m hu)
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.succ_A m a hA w m' hu hlt1 hI
        exact ⟨ok, hR, res, frame_store hf (by simp [succSch, SREC, SSLOT, SHP]) (by simp [succSch])⟩)
      m₁ _ q₁ h q m' hR1 hW
    rw [← res1] at ok2 hR2 res2
    obtain ⟨okX, stX, resX⟩ := AM.bind_facts _ (fun hu => internLNode (.succ hu)) a ok1 ok2
    have e : internLevel (.succ u) = internLevel u >>= fun hu => internLNode (.succ hu) := rfl
    refine ⟨e ▸ okX, by rw [e, stX]; exact hR2, by rw [e, resX]; exact res2, hlt2, ?_, hf1.trans hf2⟩
    have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp [encLevel])
    simp only [UInt64.ofNat_one] at hp1
    rw [hq1, hp1]; simp [encLevel]; omega
  | max u v ihu ihv =>
    intro n m a pos rest h q m' hA hmo hd hW
    simp only [levelFits, Bool.and_eq_true] at hl
    have h0 : romB rom pos = 2 := romB_head rom pos 2 _ rest hd
    cases n with
    | zero => simp [romLevelW] at hW
    | succ n =>
    rw [romLevelW_rec rom n m pos (by simp [h0]) (by simp [h0])] at hW
    have hd1 : rom.drop (pos + 1).toNat = encLevel u ++ (encLevel v ++ rest) := by
      have := drop_shift rom pos [2] (encLevel u ++ encLevel v) rest (by simpa [encLevel] using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp [encLevel]))
      simpa using this
    cases hU : romLevelW rom n m (pos + 1) with
    | none => rw [hU] at hW; simp [lvOneK] at hW
    | some r =>
    obtain ⟨hu, q₁, m₁⟩ := r
    rw [hU, h0, lvOneK_two (ht := by simp)] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := ihu hl.1 n m a (pos + 1) _ hu q₁ m₁ hA hmo hd1 hU
    have hd2 : rom.drop q₁.toNat = encLevel v ++ rest :=
      drop_shift rom (pos + 1) (encLevel u) (encLevel v) rest (by rw [hd1, List.append_assoc]) q₁ hq1
    cases hV : romLevelW rom n m₁ q₁ with
    | none => rw [hV] at hW; simp [lvTwoK] at hW
    | some r =>
    obtain ⟨hv, q₂, m₂⟩ := r
    rw [hV, lvTwoK_max _ _ _ _ _ rfl] at hW
    obtain ⟨ok2, hR2, res2, hlt2, hq2, hf2⟩ := ihv hl.2 n m₁ _ q₁ rest hv q₂ m₂ hR1 ((romLevelW_topK hU).mode hA.1.lit.1 hmo) hd2 hV
    obtain ⟨ok3, hR3, res3, hlt3, rfl, hf3⟩ := lvNode_ok (internLNode (.max (decI hu) (decI hv))) (fun m => minternW m hu hv)
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.max_A m a hA w m' hu hv hlt1 hlt2 hI
        exact ⟨ok, hR, res, frame_store hf (by simp [maxSch, MREC, MSLOT, MHP]) (by simp [maxSch])⟩)
      m₂ _ q₂ h q m' hR2 hW
    rw [← res1] at ok3 hR3 res3
    rw [← res2] at ok3 hR3 res3
    obtain ⟨okV, stV, resV⟩ := AM.bind_facts _ (fun hv => internLNode (.max (AM.res (internLevel u) a) hv))
      (AM.st (internLevel u) a) ok2 ok3
    obtain ⟨okX, stX, resX⟩ := AM.bind_facts _
      (fun hu => internLevel v >>= fun hv => internLNode (.max hu hv)) a ok1 okV
    have e : internLevel (.max u v) =
        internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.max hu hv) := rfl
    refine ⟨e ▸ okX, by rw [e, stX, stV]; exact hR3, by rw [e, resX, resV]; exact res3, hlt3, ?_,
      hf1.trans (hf2.trans hf3)⟩
    have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp [encLevel])
    simp only [UInt64.ofNat_one] at hp1
    rw [hq2, hq1, hp1]; simp [encLevel]; omega
  | imax u v ihu ihv =>
    intro n m a pos rest h q m' hA hmo hd hW
    simp only [levelFits, Bool.and_eq_true] at hl
    have h0 : romB rom pos = 3 := romB_head rom pos 3 _ rest hd
    cases n with
    | zero => simp [romLevelW] at hW
    | succ n =>
    rw [romLevelW_rec rom n m pos (by simp [h0]) (by simp [h0])] at hW
    have hd1 : rom.drop (pos + 1).toNat = encLevel u ++ (encLevel v ++ rest) := by
      have := drop_shift rom pos [3] (encLevel u ++ encLevel v) rest (by simpa [encLevel] using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp [encLevel]))
      simpa using this
    cases hU : romLevelW rom n m (pos + 1) with
    | none => rw [hU] at hW; simp [lvOneK] at hW
    | some r =>
    obtain ⟨hu, q₁, m₁⟩ := r
    rw [hU, h0, lvOneK_two (ht := by simp)] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := ihu hl.1 n m a (pos + 1) _ hu q₁ m₁ hA hmo hd1 hU
    have hd2 : rom.drop q₁.toNat = encLevel v ++ rest :=
      drop_shift rom (pos + 1) (encLevel u) (encLevel v) rest (by rw [hd1, List.append_assoc]) q₁ hq1
    cases hV : romLevelW rom n m₁ q₁ with
    | none => rw [hV] at hW; simp [lvTwoK] at hW
    | some r =>
    obtain ⟨hv, q₂, m₂⟩ := r
    rw [hV, lvTwoK_imax _ _ _ _ _ rfl] at hW
    obtain ⟨ok2, hR2, res2, hlt2, hq2, hf2⟩ := ihv hl.2 n m₁ _ q₁ rest hv q₂ m₂ hR1 ((romLevelW_topK hU).mode hA.1.lit.1 hmo) hd2 hV
    obtain ⟨ok3, hR3, res3, hlt3, rfl, hf3⟩ := lvNode_ok (internLNode (.imax (decI hu) (decI hv))) (fun m => iminternW m hu hv)
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.imax_A m a hA w m' hu hv hlt1 hlt2 hI
        exact ⟨ok, hR, res, frame_store hf (by simp [imaxSch, IREC, ISLOT, IHP]) (by simp [imaxSch])⟩)
      m₂ _ q₂ h q m' hR2 hW
    rw [← res1] at ok3 hR3 res3
    rw [← res2] at ok3 hR3 res3
    obtain ⟨okV, stV, resV⟩ := AM.bind_facts _ (fun hv => internLNode (.imax (AM.res (internLevel u) a) hv))
      (AM.st (internLevel u) a) ok2 ok3
    obtain ⟨okX, stX, resX⟩ := AM.bind_facts _
      (fun hu => internLevel v >>= fun hv => internLNode (.imax hu hv)) a ok1 okV
    have e : internLevel (.imax u v) =
        internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.imax hu hv) := rfl
    refine ⟨e ▸ okX, by rw [e, stX, stV]; exact hR3, by rw [e, resX, resV]; exact res3, hlt3, ?_,
      hf1.trans (hf2.trans hf3)⟩
    have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp [encLevel])
    simp only [UInt64.ofNat_one] at hp1
    rw [hq2, hq1, hp1]; simp [encLevel]; omega

end ref


/-- **`rom_level` refines `internLevel`** at a position holding the level's encoding. -/
@[refines ConRon.Arena.internLevel]
theorem romLevel_refines (rom : List UInt8) (p : Prog) (hL : LevelProg rom p) (hr : RomOK rom)
    (l : ConLeche.Level) (hl : levelFits l = true) (n : Nat) (s₀ : St) (a₀ : AState) (pos : Word)
    (rest : List UInt8) (hA : ArenaD s₀.mem a₀) (hmo : ModeOK s₀.mem) (hd : rom.drop pos.toNat = encLevel l ++ rest) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_level" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internLevel l) a₀ ∧ ArenaD s'.mem (AM.st (internLevel l) a₀) ∧
      AM.res (internLevel l) a₀ = decI (r.headD 0) ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (r.tail.headD 0).toNat = pos.toNat + (encLevel l).length ∧
      MemFrame StoreA StoreC s₀.mem s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (romLevel_specW rom p hL n s₀ pos ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩)
  subst hs
  exact ⟨hloc, romLevelW_ok rom hr l hl n _ a₀ pos rest _ _ _ hA hmo hd hW⟩

end L.Rom
