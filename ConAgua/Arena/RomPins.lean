import ConAgua.Arena.Rom
import ConAgua.Arena.Tiers
import ConAgua.Front.ApplyExprRefine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `internReservedPins` in L: the pin table filled from the ROM

The twin's `internReservedPins` (`vendor/con-ron/ConRon/Arena/Pins.lean`) interns the 51 pinned
names (`pinNames`) and the 16 reserved basis names (`reservedBasisNameValues`), then the empty
universe-argument list, the level `0`, the level `1` and the expression `Sort 1`, and installs
them as the state's `Pins`. In L the two name lists are ROM bytes (`encNames`, one after the
other at the offset `off` the program is built with) and the table is the word array `PINS`
(`Tiers.lean`'s `PinsR`):

* `rom_names_to(q, k, d)`: intern `k` names from ROM position `q`, the `j`-th handle to
  `PINS[d + j]`; returns the position after them (the twin's `internNameList`).
* `intern_reserved_pins()`: the two lists to `PINS[1‥51]` and `PINS[55‥70]`, then `intern_ls(0,
  0)`, `intern_zero`, `intern_succ`, `intern_sort` to `PINS[52‥54]`, and the flag `PINS[0] := 1`
  last. It refines `internReservedPins` from any state whose pin flag is `0`: afterwards
  `PinsR` holds with the flag set (`PinsFull`), so every pin reader works.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Rom

open L.Arena

/-! ## `rom_names_to(q, k, d)` -/

section namesTo
variable (rom : List UInt8)

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
def romNamesTo : FunDecl := lfn (q, k, d) locals (h, r) {
  if k == 0 { return q };
  (h, q) := call rom_name(q);
  PINS.u64[d] := h;
  r := call rom_names_to(q, k - 1, d + 1);
  return r
}

mutual
/-- **The model of `rom_names_to`** at L fuel `n`: the position after, the memory after. -/
def romNamesToW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, k, d => if k = 0 then some (q, m) else namesToK n k d (romNameW rom n m q)

/-- After one name. -/
def namesToK (n : Nat) (k d : Word) : Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (h, q', m₁) =>
    if d.toNat < (m₁.arr64 PINS).size then romNamesToW n (m₁.set64 PINS d h) q' (k - 1) (d + 1)
    else none
end

theorem romNamesToW_zero (n : Nat) (m : Mem) (q d : Word) : romNamesToW rom (n + 1) m q 0 d = some (q, m) := by
  simp [romNamesToW]
theorem romNamesToW_succ (n : Nat) (m : Mem) (q k d : Word) (hk : k ≠ 0) :
    romNamesToW rom (n + 1) m q k d = namesToK rom n k d (romNameW rom n m q) := by
  simp [romNamesToW, hk]
theorem namesToK_some (n : Nat) (k d h q' : Word) (m₁ : Mem) (hd : d.toNat < (m₁.arr64 PINS).size) :
    namesToK rom n k d (some (h, q', m₁)) = romNamesToW rom n (m₁.set64 PINS d h) q' (k - 1) (d + 1) := by
  simp [namesToK, hd]

end namesTo

grind_pattern [arena_grind] romNamesToW_zero => romNamesToW rom (n + 1) m q 0 d
grind_pattern [arena_grind] romNamesToW_succ => romNamesToW rom (n + 1) m q k d
grind_pattern [arena_grind] namesToK_some => namesToK rom n k d (some (h, q', m₁))

/-- **`rom_names_to`'s model keeps the top in a tier.** -/
theorem romNamesToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q k d q' : Word) (m' : Mem),
    romNamesToW rom n m q k d = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q k d q' m' hW; simp [romNamesToW] at hW
  | succ n ih =>
    intro m q k d q' m' hW
    by_cases hk : k = 0
    · subst hk
      rw [romNamesToW_zero] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    rw [romNamesToW_succ rom n m q k d hk] at hW
    cases hP : romNameW rom n m q with
    | none => rw [hP] at hW; simp [namesToK] at hW
    | some r =>
      obtain ⟨h, q₁, m₁⟩ := r
      rw [hP] at hW
      by_cases hd : d.toNat < (m₁.arr64 PINS).size
      · rw [namesToK_some rom n k d h q₁ m₁ hd] at hW
        exact ((romNameW_topK hP).trans (TopK.of_eq (top_set64_arr _ _ _ _ (by decide)) (pcap_set64 _ _ _ _) (Mem.flag_set64_ne _ _ _ _ (by decide)))).trans
          (ih _ _ _ _ _ _ hW)
      · simp [namesToK, hd] at hW

theorem romNamesToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q k d q' : Word) (m' : Mem)
    (hW : romNamesToW rom n m q k d = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romNamesToW_topK rom n m q k d q' m' hW hc ht).1
grind_pattern [arena_grind] romNamesToW_top' => romNamesToW rom n m q k d, some (q', m')

section namesToSpec
variable (rom : List UInt8) (p : Prog) (hL : NameProg rom p)
  (hp : p.lookup "rom_names_to" = some romNamesTo)
include hL hp

theorem romNamesTo_specW (n : Nat) : ∀ (s₀ : St) (q k d : Word),
    pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_names_to" [q, k, d]
    ⦃fun r s' => LocEq s' s₀ ∧ romNamesToW rom n s₀.mem q k d = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q k d _
    rw [invoke_eq _ hp]; simp only [callFn, romNamesTo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q k d hs
    have ih' := fun s₁ q₁ k₁ d₁ h₁ => Triple.keep hL.no_st8 (ih s₁ q₁ k₁ d₁ h₁)
    have hn' := fun s₁ q₁ h₁ => Triple.keep hL.no_st8 (romName_specW rom p hL n s₁ q₁ h₁)
    rw [invoke_eq _ hp]
    simp only [callFn, romNamesTo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hn', ih'] <;>
      finish [Keep.size, Keep.pcap]

end namesToSpec

/-! ## `rom_names_to` refines `internNameList` -/

theorem pinW_set (m : Mem) (d h : Word) (i : Nat) (hd : d.toNat < (m.arr64 PINS).size) :
    pinW (m.set64 PINS d h) i = if i = d.toNat then h else pinW m i := by
  simp only [pinW, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hi : i = d.toNat
  · subst hi; simp [hd]
  · simp [hi, Ne.symm hi]

/-- The pin store's frame: `PINS` and the store tier. -/
def PinA : List ArrId := PINS :: StoreA

theorem frame_pinA {m m' : Mem} (h : MemFrame StoreA StoreC m m') : MemFrame PinA StoreC m m' :=
  h.mono (fun _b hb => List.mem_cons_of_mem _ hb) (fun _ hx => hx)

section namesToRef
variable (rom : List UInt8) (hr : RomOK rom)
include hr

theorem romNamesToW_ok (ns : List ConLeche.Name) (hns : ns.all nameFits = true) :
    ∀ (n : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8) (k d r : Word) (m' : Mem),
    ArenaD m a → ModeOK m → rom.drop q.toNat = encNames ns ++ rest → k.toNat = ns.length →
    d.toNat + ns.length < 2 ^ 63 → romNamesToW rom n m q k d = some (r, m') →
    AM.ok (internNameList ns) a ∧ ArenaD m' (AM.st (internNameList ns) a) ∧
    r.toNat = q.toNat + (encNames ns).length ∧ MemFrame PinA StoreC m m' ∧
    (AM.res (internNameList ns) a).length = ns.length ∧
    (∀ j, j < ns.length → (AM.res (internNameList ns) a)[j]? = some (decI (pinW m' (d.toNat + j))) ∧
      (pinW m' (d.toNat + j)).toNat < 2 ^ 32) ∧
    (∀ i, (i < d.toNat ∨ d.toNat + ns.length ≤ i) → pinW m' i = pinW m i) := by
  induction ns with
  | nil =>
    intro n m a q rest k d r m' hA hmo hd hk hdl hW
    have hk0 : k = 0 := by simp at hk; exact UInt64.toNat_inj.mp (by simpa using hk)
    subst hk0
    cases n with
    | zero => simp [romNamesToW] at hW
    | succ n =>
    rw [romNamesToW_zero] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨trivial, hA, by simp [encNames], MemFrame.refl _ _ _, rfl, fun j hj => by simp at hj,
      fun _ _ => rfl⟩
  | cons x xs ih =>
    intro n m a q rest k d r m' hA hmo hd hk hdl hW
    simp only [List.all_cons, Bool.and_eq_true] at hns
    have hk0 : k ≠ 0 := by intro h; subst h; simp at hk
    cases n with
    | zero => simp [romNamesToW] at hW
    | succ n =>
    rw [romNamesToW_succ rom n m q k d hk0] at hW
    have hd' : rom.drop q.toNat = encName x ++ (encNames xs ++ rest) := by
      rw [hd, encNames, List.append_assoc]
    cases hN : romNameW rom n m q with
    | none => rw [hN] at hW; simp [namesToK] at hW
    | some t =>
    obtain ⟨h₁, q₁, m₁⟩ := t
    rw [hN] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romNameW_ok rom hr x hns.1 n m a q _ h₁ q₁ m₁ hA hmo hd' hN
    simp only [namesToK] at hW
    split at hW
    case isFalse => simp at hW
    rename_i hdlt
    have hf2 : MemFrame PinA StoreC m₁ (m₁.set64 PINS d h₁) :=
      (MemFrame.set64 m₁ PINS (by decide) d h₁).mono (by simp [PinA]) (by simp)
    have hR2 : ArenaD (m₁.set64 PINS d h₁) (AM.st (internName x) a) :=
      ArenaD.frameHi (MemFrame.set64 m₁ PINS (by decide) d h₁) (by simp [PINS]) (by simp) hR1
    have hdq : rom.drop q₁.toNat = encNames xs ++ rest :=
      drop_shift rom hr q (encName x) (encNames xs) rest (by rw [hd', List.append_assoc]) q₁ hq1
    have hk1 : (k - 1).toNat = xs.length := by
      have : 1 ≤ k.toNat := by simp at hk; omega
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using this))]
      simp at hk ⊢; omega
    have hd1 : (d + 1).toNat = d.toNat + 1 := by
      rw [UInt64.toNat_add]; simp at hdl ⊢; omega
    obtain ⟨ok2, hR3, hr2, hf3, hlen2, hres2, hkeep2⟩ := ih hns.2 n _ _ q₁ rest (k - 1) (d + 1) r m' hR2
      (((romNameW_topK hN).trans (TopK.of_eq (top_set64_arr _ _ _ _ (by decide)) (pcap_set64 _ _ _ _)
        (Mem.flag_set64_ne _ _ _ _ (by decide)))).mode hA.1.lit.1 hmo) hdq hk1
      (by simp at hdl; omega) hW
    have hX : internNameList (x :: xs) =
        internName x >>= fun h => internNameList xs >>= fun hs => pure (h :: hs) := rfl
    have okX : AM.ok (internNameList (x :: xs)) a := by
      rw [hX, AM.ok_bind, AM.ok_bind]; exact ⟨ok1, ok2, trivial⟩
    have hok1 : AM.ok (internNameList xs >>= fun hs => pure (AM.res (internName x) a :: hs))
        (AM.st (internName x) a) := by rw [AM.ok_bind]; exact ⟨ok2, trivial⟩
    have hst : AM.st (internNameList (x :: xs)) a = AM.st (internNameList xs) (AM.st (internName x) a) := by
      rw [hX, AM.st_bind _ _ _ (hX ▸ okX), AM.st_bind _ _ _ hok1]; rfl
    have hres : AM.res (internNameList (x :: xs)) a =
        AM.res (internName x) a :: AM.res (internNameList xs) (AM.st (internName x) a) := by
      rw [hX, AM.res_bind _ _ _ ok1, AM.res_bind _ _ _ ok2]; rfl
    refine ⟨okX, hst ▸ hR3, ?_, (frame_pinA hf1).trans (hf2.trans hf3), by rw [hres]; simp [hlen2], ?_, ?_⟩
    · rw [hr2, hq1]; simp [encNames]; omega
    · intro j hj
      rw [hres]
      cases j with
      | zero =>
        have hp := hkeep2 d.toNat (.inl (by omega))
        rw [pinW_set _ _ _ _ hdlt] at hp
        simp only [↓reduceIte] at hp
        simp only [List.getElem?_cons_zero, Nat.add_zero, hp, res1, true_and]
        exact hlt1
      | succ j =>
        obtain ⟨e1, e2⟩ := hres2 j (by simp at hj; omega)
        rw [hd1, show d.toNat + 1 + j = d.toNat + (j + 1) by omega] at e1 e2
        exact ⟨by simpa using e1, e2⟩
    · intro i hi
      rw [hkeep2 i (by rw [hd1]; simp at hi; omega), pinW_set _ _ _ _ hdlt]
      have : i ≠ d.toNat := by simp at hi; omega
      simp [this, pinW, hf1.1 PINS (by decide) (by decide)]

end namesToRef

/-! ## `intern_reserved_pins()` -/

/-- `intern_reserved_pins()` for the ROM offset `off` of `encNames pinNames ++ encNames
reservedBasisNameValues`. -/
-- con-ron: ConRon/Arena/Pins.lean:228-242 ConRon.Arena.internReservedPins
def internReservedPinsAt (off : Word) : FunDecl := lfn () locals (q, us, z, o, s1) {
  if len(PINS.u64) < 71 { abort };
  q := call rom_names_to(⟪off⟫, 51, 1);
  q := call rom_names_to(q, 16, 55);
  us := call intern_ls(0, 0);
  if us >= 4294967296 { abort };
  z := call intern_zero();
  if z >= 4294967296 { abort };
  o := call intern_succ(z);
  if o >= 4294967296 { abort };
  s1 := call intern_sort(o);
  if s1 >= 4294967296 { abort };
  PINS.u64[52] := us;
  PINS.u64[53] := z;
  PINS.u64[54] := s1;
  PINS.u64[0] := 1;
  return 0
}

/-- `intern_reserved_pins()` as the program has it: the ROM starts with the two name lists. -/
-- con-ron: ConRon/Arena/Pins.lean:228-242 ConRon.Arena.internReservedPins
@[l_impl ConRon.Arena.internReservedPins]
def internReservedPinsL : FunDecl := internReservedPinsAt 0

section irpModel
variable (rom : List UInt8)

/-- The table's last writes. -/
def irpFill (m : Mem) (us z s1 : Word) : Mem :=
  ((((m.set64 PINS 52 us).set64 PINS 53 z).set64 PINS 54 s1).set64 PINS 0 1)

def irp6K (us z : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (s1, m₆) => if 4294967296 ≤ s1 then none else some (irpFill m₆ us z s1)
def irp5K (us z : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (o, m₅) => if 4294967296 ≤ o then none else irp6K us z (sointernW m₅ o)
def irp4K (us : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (z, m₄) => if 4294967296 ≤ z then none else irp5K us z (sinternW m₄ z)
def irp3K : Option (Word × Mem) → Option Mem
  | none => none
  | some (us, m₃) => if 4294967296 ≤ us then none else irp4K us (zinternW m₃)
def irp2K : Option (Word × Mem) → Option Mem
  | none => none
  | some (_, m₂) => irp3K (lsinternW m₂ 0 0)
def irp1K (n : Nat) : Option (Word × Mem) → Option Mem
  | none => none
  | some (q, m₁) => irp2K (romNamesToW rom n m₁ q 16 55)

/-- **The model of `intern_reserved_pins`** at L fuel `n`. -/
def irpW : Nat → Word → Mem → Option Mem
  | 0, _, _ => none
  | n + 1, off, m => if m.len64 PINS < 71 then none else irp1K rom n (romNamesToW rom n m off 51 1)

end irpModel

section irpArms
variable (rom : List UInt8) (n : Nat) (us z o s1 q : Word) (m m₁ : Mem)
theorem irp6K_some (h : ¬ 4294967296 ≤ s1) : irp6K us z (some (s1, m)) = some (irpFill m us z s1) := by
  simp [irp6K, h]
theorem irp5K_some (h : ¬ 4294967296 ≤ o) : irp5K us z (some (o, m)) = irp6K us z (sointernW m o) := by
  simp [irp5K, h]
theorem irp4K_some (h : ¬ 4294967296 ≤ z) : irp4K us (some (z, m)) = irp5K us z (sinternW m z) := by
  simp [irp4K, h]
theorem irp3K_some (h : ¬ 4294967296 ≤ us) : irp3K (some (us, m)) = irp4K us (zinternW m) := by
  simp [irp3K, h]
theorem irp2K_some : irp2K (some (q, m)) = irp3K (lsinternW m 0 0) := rfl
theorem irp1K_some : irp1K rom n (some (q, m)) = irp2K (romNamesToW rom n m q 16 55) := rfl
theorem irpW_eq (off : Word) (h : ¬ m.len64 PINS < 71) :
    irpW rom (n + 1) off m = irp1K rom n (romNamesToW rom n m off 51 1) := by simp [irpW, h]
end irpArms

attribute [arena_grind =] irp6K_some irp5K_some irp4K_some irp3K_some irp2K_some irp1K_some irpW_eq

/-- The functions `intern_reserved_pins` calls. -/
structure IrpProg (rom : List UInt8) (off : Word) (p : Prog) : Prop extends NameProg rom p where
  rom_names_to : p.lookup "rom_names_to" = some romNamesTo
  ls_match : p.lookup "ls_match" = some lsMatch
  ls_find : p.lookup "ls_find" = some lsFind
  ls_push : p.lookup "ls_push" = some lsPush
  intern_ls : p.lookup "intern_ls" = some internLs
  zero_find : p.lookup "zero_find" = some zeroFind
  zero_push : p.lookup "zero_push" = some zeroPush
  intern_zero : p.lookup "intern_zero" = some internZero
  succ_find : p.lookup "succ_find" = some succFind
  succ_push : p.lookup "succ_push" = some succPush
  intern_succ : p.lookup "intern_succ" = some internSucc
  sort_find : p.lookup "sort_find" = some sortFind
  sort_push : p.lookup "sort_push" = some sortPush
  intern_sort : p.lookup "intern_sort" = some internSort
  irp : p.lookup "intern_reserved_pins" = some (internReservedPinsAt off)

section irpSpec
variable (rom : List UInt8) (off : Word) (p : Prog) (hL : IrpProg rom off p)
include hL

theorem internReservedPins_specW (n : Nat) (s₀ : St)
    (hs : pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_reserved_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ irpW rom n off s₀.mem = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hL.irp]
  simp only [callFn, internReservedPinsAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hnt := fun s₁ q₁ k₁ d₁ h₁ =>
      Triple.keep hL.no_st8 (romNamesTo_specW rom p hL.toNameProg hL.rom_names_to n s₁ q₁ k₁ d₁ h₁)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hnt,
        internLs_spec p hL.lit_hash hL.limbs_eq hL.ls_match hL.ls_find hL.ls_push hL.intern_ls n,
        internZero_spec p hL.zero_find hL.zero_push hL.intern_zero n,
        internSucc_spec p hL.succ_find hL.succ_push hL.intern_succ n,
        internSort_spec p hL.sort_find hL.sort_push hL.intern_sort n] <;>
      finish [Keep.size, Keep.pcap, irpFill]

end irpSpec

/-! ## `intern_reserved_pins` refines `internReservedPins` -/

theorem run_bind_ok {α β : Type} [Inhabited α] (x : AM α) (f : α → AM β) (a : AState) (h : AM.ok x a) :
    (x >>= f).run a = (f (AM.res x a)).run (AM.st x a) := by
  rw [StateT.run_bind, AM.run_of_ok _ _ h]; rfl

attribute [local irreducible] pinNames reservedBasisNameValues AM.st AM.res AM.ok in
/-- The twin's run, from its six pieces. -/
theorem internReservedPins_run (a : AState)
    (ok1 : AM.ok (internNameList pinNames) a)
    (ok2 : AM.ok (internNameList reservedBasisNameValues) (AM.st (internNameList pinNames) a))
    (ok3 : AM.ok (internLsNode []) (AM.st (internNameList reservedBasisNameValues)
      (AM.st (internNameList pinNames) a)))
    (a₃ : AState) (ha₃ : a₃ = AM.st (internLsNode []) (AM.st (internNameList reservedBasisNameValues)
      (AM.st (internNameList pinNames) a)))
    (ok4 : AM.ok (internLNode .zero) a₃)
    (ok5 : AM.ok (internLNode (.succ (AM.res (internLNode .zero) a₃))) (AM.st (internLNode .zero) a₃))
    (a₅ : AState) (ha₅ : a₅ = AM.st (internLNode (.succ (AM.res (internLNode .zero) a₃)))
      (AM.st (internLNode .zero) a₃))
    (ok6 : AM.ok (internSortE (AM.res (internLNode (.succ (AM.res (internLNode .zero) a₃)))
      (AM.st (internLNode .zero) a₃))) a₅) :
    internReservedPins.run a = .ok ((), { AM.st (internSortE (AM.res (internLNode (.succ
      (AM.res (internLNode .zero) a₃))) (AM.st (internLNode .zero) a₃))) a₅ with
      pins := { names := (AM.res (internNameList pinNames) a).toArray,
                reserved := AM.res (internNameList reservedBasisNameValues) (AM.st (internNameList pinNames) a),
                emptyLevels := AM.res (internLsNode []) (AM.st (internNameList reservedBasisNameValues)
                  (AM.st (internNameList pinNames) a)),
                zeroLevel := AM.res (internLNode .zero) a₃,
                sortOne := AM.res (internSortE (AM.res (internLNode (.succ (AM.res (internLNode .zero) a₃)))
                  (AM.st (internLNode .zero) a₃))) a₅ } }) := by
  subst ha₃ ha₅
  unfold internReservedPins
  rw [run_bind_ok _ _ _ ok1]; try dsimp only
  rw [run_bind_ok _ _ _ ok2]; try dsimp only
  rw [run_bind_ok _ _ _ ok3]; try dsimp only
  rw [run_bind_ok _ _ _ ok4]; try dsimp only
  rw [run_bind_ok _ _ _ ok5]; try dsimp only
  refine (run_bind_ok _ _ _ ok6).trans ?_
  rfl

theorem pinW_frame {C : List Word} {m m' : Mem} (h : MemFrame StoreA C m m') (i : Nat) :
    pinW m' i = pinW m i := by
  simp only [pinW, h.1 PINS (by decide) (by decide)]

theorem pinW_fill (m : Mem) (us z s1 : Word) (i : Nat) (hs : 55 ≤ (m.arr64 PINS).size) :
    pinW (irpFill m us z s1) i =
      if i = 0 then 1 else if i = 54 then s1 else if i = 53 then z else if i = 52 then us
      else pinW m i := by
  have s1' : ((m.set64 PINS 52 us).arr64 PINS).size = (m.arr64 PINS).size := size_set64 _ _ _ _ _
  have s2' : (((m.set64 PINS 52 us).set64 PINS 53 z).arr64 PINS).size = (m.arr64 PINS).size := by
    rw [size_set64, s1']
  have s3' : ((((m.set64 PINS 52 us).set64 PINS 53 z).set64 PINS 54 s1).arr64 PINS).size =
      (m.arr64 PINS).size := by rw [size_set64, s2']
  simp only [irpFill]
  rw [pinW_set _ _ _ _ (by rw [s3']; simp; omega), pinW_set _ _ _ _ (by rw [s2']; simp; omega),
    pinW_set _ _ _ _ (by rw [s1']; simp; omega), pinW_set _ _ _ _ (by simp; omega)]
  by_cases h0 : i = 0 <;> simp [h0] <;> by_cases h4 : i = 54 <;> simp [h4] <;>
    by_cases h3 : i = 53 <;> simp [h3] <;> by_cases h2 : i = 52 <;> simp [h2]

theorem irpFill_frame (m : Mem) (us z s1 : Word) : MemFrame [PINS] [] m (irpFill m us z s1) := by
  simp only [irpFill]
  exact (((MemFrame.set64 _ PINS (by decide) _ _).trans (MemFrame.set64 _ PINS (by decide) _ _)).trans
    (MemFrame.set64 _ PINS (by decide) _ _)).trans (MemFrame.set64 _ PINS (by decide) _ _)

theorem ArenaD.with_pins {m : Mem} {a : AState} (P : Pins) (h : ArenaD m a) :
    ArenaD m { a with pins := P } := by
  obtain ⟨hR, hD⟩ := h
  exact ⟨{ hR with }, { hD with }⟩

theorem pinNames_length : pinNames.length = 51 := by simp [pinNames]
theorem reserved_length : reservedBasisNameValues.length = 16 := by simp [reservedBasisNameValues]

section irpRef
variable (rom : List UInt8) (hr : RomOK rom)
include hr

set_option linter.constructorNameAsVariable false in
attribute [local irreducible] pinNames reservedBasisNameValues AM.st AM.res AM.ok in
/-- **The model of `intern_reserved_pins` refines `internReservedPins`**: from `ArenaD`, with the
two name lists at `off`, the pin table is filled (`PinsFull`, the flag set). -/
theorem irpW_ok (off : Word) (rest : List UInt8)
    (hd : rom.drop off.toNat = encNames pinNames ++ (encNames reservedBasisNameValues ++ rest))
    (hf1 : pinNames.all nameFits = true) (hf2 : reservedBasisNameValues.all nameFits = true)
    (n : Nat) (m : Mem) (a : AState) (m' : Mem) (hA : ArenaD m a) (hmo : ModeOK m)
    (hW : irpW rom n off m = some m') :
    AM.ok internReservedPins a ∧ ArenaD m' (AM.st internReservedPins a) ∧
    PinsFull m' (AM.st internReservedPins a).pins ∧ pinW m' 0 ≠ 0 ∧ MemFrame PinA StoreC m m' ∧
    ModeOK m' := by
  cases n with
  | zero => simp [irpW] at hW
  | succ n =>
  simp only [irpW] at hW
  split at hW
  case isTrue => simp at hW
  rename_i hlen
  cases h1 : romNamesToW rom n m off 51 1 with
  | none => rw [h1] at hW; simp [irp1K] at hW
  | some t =>
  obtain ⟨q, m₁⟩ := t
  rw [h1] at hW
  simp only [irp1K] at hW
  obtain ⟨ok1, hR1, hq, hf1', hl1, hj1, hk1⟩ := romNamesToW_ok rom hr pinNames hf1 n m a off _ 51 1 q m₁ hA hmo
    hd (by simp [pinNames_length]) (by simp [pinNames_length]) h1
  have hd2 : rom.drop q.toNat = encNames reservedBasisNameValues ++ rest :=
    drop_shift rom hr off (encNames pinNames) (encNames reservedBasisNameValues) rest
      (by rw [hd, List.append_assoc]) q hq
  cases h2 : romNamesToW rom n m₁ q 16 55 with
  | none => rw [h2] at hW; simp [irp2K] at hW
  | some t =>
  obtain ⟨q₂, m₂⟩ := t
  rw [h2] at hW
  simp only [irp2K] at hW
  obtain ⟨ok2, hR2, -, hf2', hl2, hj2, hk2⟩ := romNamesToW_ok rom hr reservedBasisNameValues hf2 n m₁ _ q
    rest 16 55 q₂ m₂ hR1 ((romNamesToW_topK rom _ _ _ _ _ _ _ h1).mode hA.1.lit.1 hmo) hd2 (by simp [reserved_length]) (by simp [reserved_length]) h2
  cases h3 : lsinternW m₂ 0 0 with
  | none => rw [h3] at hW; simp [irp3K] at hW
  | some t =>
  obtain ⟨us, m₃⟩ := t
  rw [h3] at hW
  simp only [irp3K] at hW
  split at hW
  case isTrue => simp at hW
  rename_i hus
  obtain ⟨ok3, hR3, res3, hf3⟩ := L.Front.internLs_D m₂ _ hR2 us m₃ 0 0 (by simp [SliceOK])
    [] (by simp [sliceL, lsWords]) (fun _ => by decide) h3
  cases h4 : zinternW m₃ with
  | none => rw [h4] at hW; simp [irp4K] at hW
  | some t =>
  obtain ⟨z, m₄⟩ := t
  rw [h4] at hW
  simp only [irp4K] at hW
  split at hW
  case isTrue => simp at hW
  rename_i hz
  obtain ⟨ok4, hR4, res4, hf4⟩ := L.Front.zero_A m₃ _ hR3 z m₄ h4
  cases h5 : sinternW m₄ z with
  | none => rw [h5] at hW; simp [irp5K] at hW
  | some t =>
  obtain ⟨o, m₅⟩ := t
  rw [h5] at hW
  simp only [irp5K] at hW
  split at hW
  case isTrue => simp at hW
  rename_i ho
  have hzl : z.toNat < 2 ^ 32 := by simp at hz; exact UInt64.lt_iff_toNat_lt.mp hz
  obtain ⟨ok5, hR5, res5, hf5⟩ := L.Front.succ_A m₄ _ hR4 o m₅ z hzl h5
  cases h6 : sointernW m₅ o with
  | none => rw [h6] at hW; simp [irp6K] at hW
  | some t =>
  obtain ⟨s1, m₆⟩ := t
  rw [h6] at hW
  simp only [irp6K] at hW
  split at hW
  case isTrue => simp at hW
  rename_i hs1
  simp only [Option.some.injEq] at hW
  subst hW
  have hol : o.toNat < 2 ^ 32 := by simp at ho; exact UInt64.lt_iff_toNat_lt.mp ho
  obtain ⟨ok6, hR6, res6, hf6⟩ := L.Front.internSort_D m₅ _ hR5 s1 m₆ o hol h6
  rw [← res4] at ok5 hR5 res5 ok6 hR6 res6
  rw [← res5] at ok6 hR6 res6
  have hrun := internReservedPins_run a ok1 ok2 ok3 _ rfl ok4 ok5 _ rfl ok6
  obtain ⟨okX, stX, -⟩ := AM.of_run_ok _ _ _ _ hrun
  have hfS : MemFrame StoreA StoreC m₂ m₆ :=
    ((frame_store hf3 (by simp [tier1, tierOff, lsSch, LSREC, LSSLOT, LSHP]) (by simp [lsSch])).trans
      (frame_store hf4 (by simp [tier1, tierOff, zeroSch, ZREC, ZSLOT]) (by simp [zeroSch]))).trans
      ((frame_store hf5 (by simp [tier1, tierOff, succSch, SREC, SSLOT, SHP]) (by simp [succSch])).trans
      (frame_store hf6 (by simp [tier1, tierOff, sortSch, SOREC, SOSLOT, SOLP]) (by simp [sortSch])))
  have hsz : (m₆.arr64 PINS).size = (m.arr64 PINS).size := by
    rw [hfS.2.2.1, hf2'.2.2.1, hf1'.2.2.1]
  have hsz71 : 71 ≤ (m.arr64 PINS).size := by
    have : ¬ (UInt64.ofNat (m.arr64 PINS).size) < 71 := by simpa [Mem.len64] using hlen
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', show (71 : UInt64).toNat = 71 from rfl] at this
    have := Nat.mod_le (m.arr64 PINS).size (2 ^ 64)
    omega
  have hpw := fun i => pinW_fill m₆ us z s1 i (by omega)
  have h26 := fun i => pinW_frame hfS i
  refine ⟨okX, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stX]
    exact ArenaD.with_pins _ (ArenaD.frameHi (irpFill_frame m₆ us z s1) (by simp [PINS]) (by simp) hR6)
  · rw [stX]
    simp only [reserved_length, show (55 : UInt64).toNat = 55 from rfl] at hk2
    have hlo : ∀ i, 1 ≤ i → i < 52 → pinW (irpFill m₆ us z s1) i = pinW m₁ i := fun i h1 h2 => by
      rw [hpw, h26, hk2 i (.inl (by omega))]
      have : i ≠ 0 := by omega
      have : i ≠ 54 := by omega
      have : i ≠ 53 := by omega
      have : i ≠ 52 := by omega
      simp [*]
    have hhi : ∀ i, 55 ≤ i → pinW (irpFill m₆ us z s1) i = pinW m₂ i := fun i h1 => by
      rw [hpw, h26]
      have : i ≠ 0 := by omega
      have : i ≠ 54 := by omega
      have : i ≠ 53 := by omega
      have : i ≠ 52 := by omega
      simp [*]
    have h52 : pinW (irpFill m₆ us z s1) 52 = us := by rw [hpw]; simp
    have h53 : pinW (irpFill m₆ us z s1) 53 = z := by rw [hpw]; simp
    have h54 : pinW (irpFill m₆ us z s1) 54 = s1 := by rw [hpw]; simp
    simp only [pinNames_length, reserved_length, show (55 : UInt64).toNat = 55 from rfl,
      show (1 : UInt64).toNat = 1 from rfl] at hl1 hl2 hj1 hj2 hk2
    refine { size := ?_, names_size := ?_, names_lt := ?_, names := ?_, lv_lt := ?_,
             emptyLevels := ?_, zeroLevel := ?_, sortOne := ?_, reserved_lt := ?_, reserved := ?_ }
    · rw [(irpFill_frame m₆ us z s1).2.2.1, hsz]; exact hsz71
    · simp [hl1]
    · intro i hi
      rw [hlo _ (by omega) (by omega)]
      simpa [Nat.add_comm] using (hj1 i hi).2
    · intro i hi
      rw [hlo _ (by omega) (by omega)]
      have := (hj1 i hi).1
      simp only [Nat.add_comm 1 i] at this ⊢
      simp only [List.getElem_toArray]
      rw [List.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    · rw [h52, h53, h54]
      refine ⟨by simp at hus; exact UInt64.lt_iff_toNat_lt.mp hus, hzl, ?_⟩
      simp at hs1; exact UInt64.lt_iff_toNat_lt.mp hs1
    · rw [h52]; exact res3
    · rw [h53]; exact res4.symm ▸ rfl
    · rw [h54]; exact res6
    · intro i hi
      rw [hhi _ (by omega)]
      exact (hj2 i hi).2
    · dsimp only
      apply List.ext_getElem
      · simp [hl2]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [hhi _ (by omega)]
        have := (hj2 i (by omega)).1
        rw [List.getElem?_eq_getElem h1] at this
        exact Option.some.inj this
  · rw [hpw]; simp
  · refine hf1'.trans (hf2'.trans ((frame_pinA hfS).trans ?_))
    exact (irpFill_frame m₆ us z s1).mono (by simp [PinA]) (by simp)
  · exact ((((((romNamesToW_topK rom _ _ _ _ _ _ _ h1).trans (romNamesToW_topK rom _ _ _ _ _ _ _ h2)).trans
      (cons_topK lsCS_wf (by decide) (by decide) h3)).trans (cons_topK zeroCS_wf (by decide) (by decide) h4)).trans
      (cons_topK succCS_wf (by decide) (by decide) h5)).trans ((cons_topK sortCS_wf (by decide) (by decide) h6).trans
      (memFrame_top (irpFill_frame m₆ us z s1) (by simp)))).mode hA.1.lit.1 hmo

end irpRef

/-- **`intern_reserved_pins` refines `internReservedPins`**: with the two name lists at `off` in
the ROM, from `ArenaD`, the run fills the pin table (`PinsFull`, flag set) and writes only the
store tier and `PINS`. -/
@[refines ConRon.Arena.internReservedPins]
theorem internReservedPins_refines (rom : List UInt8) (off : Word) (p : Prog) (hL : IrpProg rom off p)
    (hr : RomOK rom) (rest : List UInt8)
    (hd : rom.drop off.toNat = encNames pinNames ++ (encNames reservedBasisNameValues ++ rest))
    (hf1 : pinNames.all nameFits = true) (hf2 : reservedBasisNameValues.all nameFits = true)
    (n : Nat) (s₀ : St) (a₀ : AState) (hA : ArenaD s₀.mem a₀) (hmo : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_reserved_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok internReservedPins a₀ ∧
      ArenaD s'.mem (AM.st internReservedPins a₀) ∧ PinsFull s'.mem (AM.st internReservedPins a₀).pins ∧
      pinW s'.mem 0 ≠ 0 ∧ MemFrame PinA StoreC s₀.mem s'.mem ∧ ModeOK s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (internReservedPins_specW rom off p hL n s₀ ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩)
  subst hs
  exact ⟨hloc, irpW_ok rom hr off rest hd hf1 hf2 n _ a₀ _ hA hmo hW⟩


end L.Rom
