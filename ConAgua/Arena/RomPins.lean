module

public import ConAgua.Arena.Rom
public import ConAgua.Arena.Tiers
public import ConRon.Arena.Pins
import ConAgua.Front.ApplyExprRefine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Arena.RomItems

@[expose] public section

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
  0)`, `intern_zero`, `intern_succ`, `intern_sort` to `PINS[52‥54]`, the default maximum `Nat`
  size (`maxNatSizeDefault`, 134 217 728 bytes) to `PINS[72]`, and the flag `PINS[0] := 1` last. It refines `internReservedPins` from any state whose pin flag is `0`: afterwards
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
@[no_expose] def romNamesTo : FunDecl := lfn (q, k, d) locals (h, r) {
  if k == 0 { return q };
  (h, q) := call rom_name(q);
  PINS.u64[d] := h;
  r := call rom_names_to(q, k - 1, d + 1);
  return r
}

end namesTo

/-- **The model of `rom_names_to`** at L fuel `n` (generated): the names interned one after the
other (`rom_name`), the `j`-th handle stored to `PINS[d + j]`; the position after, the memory. -/
l_model romNamesTo_specW (rom : List UInt8) (p : Prog) (hL : NameProg rom p)
    (hp : p.lookup "rom_names_to" = some romNamesTo)
  fns [hp ↦ romNamesToW]
  specs [romName_specW rom p hL n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap] defs

/-- **`rom_names_to`'s model keeps the top in a tier.** -/
theorem romNamesToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q k d q' : Word) (m' : Mem),
    romNamesToW rom n m q k d = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q k d q' m' hW; simp [romNamesToW] at hW
  | succ n ih =>
    intro m q k d q' m' hW
    by_cases hk : k = 0
    · rw [romNamesToW.arm1 _ _ _ _ _ _ hk] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    rw [romNamesToW.arm2 _ _ _ _ _ _ hk] at hW
    cases hP : romNameW rom n m q with
    | none => rw [hP, romNamesToW.k_rom_name.none] at hW; cases hW
    | some r =>
      obtain ⟨h, q₁, m₁⟩ := r
      rw [hP, romNamesToW.k_rom_name.arm1] at hW
      exact ((romNameW_topK hP).trans (TopK.of_eq (top_set64_arr _ _ _ _ (by decide)) (pcap_set64 _ _ _ _)
        (Mem.flag_set64_ne _ _ _ _ (by decide)))).trans (ih _ _ _ _ _ _ hW)

theorem romNamesToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q k d q' : Word) (m' : Mem)
    (hW : romNamesToW rom n m q k d = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romNamesToW_topK rom n m q k d q' m' hW hc ht).1
grind_pattern [arena_grind] romNamesToW_top' => romNamesToW rom n m q k d, some (q', m')

l_model romNamesTo_specW (rom : List UInt8) (p : Prog) (hL : NameProg rom p)
    (hp : p.lookup "rom_names_to" = some romNamesTo)
  fns [hp ↦ romNamesToW]
  specs [romName_specW rom p hL n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap] nodefs


/-! ## `rom_names_to` refines `internNameList` -/

theorem pinW_set (m : Mem) (d h : Word) (i : Nat) (hd : d.toNat < (m.arr64 PINS).size) :
    pinW (m.set64 PINS d h) i = if i = d.toNat then h else pinW m i := by
  simp only [pinW, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hi : i = d.toNat
  · subst hi; simp [hd]
  · simp [hi, Ne.symm hi]

/-- The pin store's frame: `PINS` and the store tier. -/
def PinA : List TieredArray := (PINS : TieredArray) :: StoreA

theorem frame_pinA {m m' : Mem} (h : MemFrame StoreA StoreC m m') : MemFrame PinA StoreC m m' :=
  h.mono (fun _b hb => List.mem_cons_of_mem _ hb) (fun _ hx => hx)

section namesToRef
variable (rom : List UInt8) (hr : RomOK rom)
include hr

theorem romNamesToW_ok (ns : List ConLeche.Name) (hns : ns.all nameFits = true) :
    ∀ (n : Nat) (m : Mem) (a : AState) (q : Word) (rest : List UInt8) (k d r : Word) (m' : Mem),
    ArenaD m a → ModeOK m → rom.drop q.toNat = encNames ns ++ rest → k.toNat = ns.length →
    d.toNat + ns.length < 2 ^ 63 → d.toNat + ns.length ≤ (m.arr64 PINS).size →
    romNamesToW rom n m q k d = some (r, m') →
    AM.ok (internNameList ns) a ∧ ArenaD m' (AM.st (internNameList ns) a) ∧
    r.toNat = q.toNat + (encNames ns).length ∧ MemFrame PinA StoreC m m' ∧
    (AM.res (internNameList ns) a).length = ns.length ∧
    (∀ j, j < ns.length → (AM.res (internNameList ns) a)[j]? = some (decI (pinW m' (d.toNat + j))) ∧
      (pinW m' (d.toNat + j)).toNat < 2 ^ 32) ∧
    (∀ i, (i < d.toNat ∨ d.toNat + ns.length ≤ i) → pinW m' i = pinW m i) := by
  induction ns with
  | nil =>
    intro n m a q rest k d r m' hA hmo hd hk hdl _ hW
    have hk0 : k = 0 := by simp at hk; exact UInt64.toNat_inj.mp (by simpa using hk)
    subst hk0
    cases n with
    | zero => simp [romNamesToW] at hW
    | succ n =>
    rw [romNamesToW.arm1 _ _ _ _ _ _ rfl] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨trivial, hA, by simp [encNames], MemFrame.refl _ _ _, rfl, fun j hj => by simp at hj,
      fun _ _ => rfl⟩
  | cons x xs ih =>
    intro n m a q rest k d r m' hA hmo hd hk hdl hsz hW
    simp only [List.all_cons, Bool.and_eq_true] at hns
    have hk0 : k ≠ 0 := by intro h; subst h; simp at hk
    cases n with
    | zero => simp [romNamesToW] at hW
    | succ n =>
    rw [romNamesToW.arm2 _ _ _ _ _ _ hk0] at hW
    have hd' : rom.drop q.toNat = encName x ++ (encNames xs ++ rest) := by
      rw [hd, encNames, List.append_assoc]
    cases hN : romNameW rom n m q with
    | none => rw [hN, romNamesToW.k_rom_name.none] at hW; cases hW
    | some t =>
    obtain ⟨h₁, q₁, m₁⟩ := t
    rw [hN, romNamesToW.k_rom_name.arm1] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := romNameW_ok rom hr x hns.1 n m a q _ h₁ q₁ m₁ hA hmo hd' hN
    have hpins : m₁.arr64 PINS = m.arr64 PINS := hf1.1 PINS (by decide) (by decide)
    have hdlt : d.toNat < (m₁.arr64 PINS).size := by rw [hpins]; simp at hsz; omega
    have hf2 : MemFrame PinA StoreC m₁ (m₁.set64 PINS d h₁) :=
      (MemFrame.set64 m₁ PINS (by decide) d h₁).mono (by simp [PinA]) (by simp)
    have hR2 : ArenaD (m₁.set64 PINS d h₁) (AM.st (internName x) a) :=
      L.Arena.ArenaD.frameHi (MemFrame.set64 m₁ PINS (by decide) d h₁) (by simp [PINS]) (by simp) hR1
    have hdq : rom.drop q₁.toNat = encNames xs ++ rest :=
      drop_shift rom q (encName x) (encNames xs) rest (by rw [hd', List.append_assoc]) q₁ hq1
    have hk1 : (k - 1).toNat = xs.length := by
      have : 1 ≤ k.toNat := by simp at hk; omega
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using this))]
      simp at hk ⊢; omega
    have hd1 : (d + 1).toNat = d.toNat + 1 := by
      rw [UInt64.toNat_add]; simp at hdl ⊢; omega
    obtain ⟨ok2, hR3, hr2, hf3, hlen2, hres2, hkeep2⟩ := ih hns.2 n _ _ q₁ rest (k - 1) (d + 1) r m' hR2
      (((romNameW_topK hN).trans (TopK.of_eq (top_set64_arr _ _ _ _ (by decide)) (pcap_set64 _ _ _ _)
        (Mem.flag_set64_ne _ _ _ _ (by decide)))).mode hA.1.lit.1 hmo) hdq hk1
      (by simp at hdl; omega)
      (by rw [hd1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hpins]
          simp at hsz; omega) hW
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
-- con-ron: ConRon/Arena/Pins.lean:235-249 ConRon.Arena.internReservedPins
@[no_expose] def internReservedPinsAt (off : Word) : FunDecl := lfn () locals (q, us, z, o, s1) {
  if len(PINS.u64) < 73 { abort };
  q := call rom_names_to(⟪off⟫, 51, 1);
  q := call rom_names_to(q, 1, 71);
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
  PINS.u64[72] := 134217728;
  PINS.u64[0] := 1;
  return 0
}

/-- `intern_reserved_pins()` as the program has it: the ROM starts with the two name lists. -/
-- con-ron: ConRon/Arena/Pins.lean:235-249 ConRon.Arena.internReservedPins
@[no_expose, l_impl ConRon.Arena.internReservedPins]
def internReservedPinsL : FunDecl := internReservedPinsAt 0

/-- The table's last writes. -/
def irpFill (m : Mem) (us z s1 : Word) : Mem :=
  (((((m.set64 PINS 52 us).set64 PINS 53 z).set64 PINS 54 s1).set64 PINS 72 134217728).set64 PINS 0 1)

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

/-- **The model of `intern_reserved_pins`** at L fuel `n` (generated). -/
l_model internReservedPins_specW (rom : List UInt8) (off : Word) (p : Prog) (hL : IrpProg rom off p)
  fns [hL.irp ↦ irpW]
  specs [romNamesTo_specW rom p hL.toNameProg hL.rom_names_to n,
    internLs_spec p hL.lit_hash hL.limbs_eq hL.ls_match hL.ls_find hL.ls_push hL.intern_ls n,
    internZero_spec p hL.zero_find hL.zero_push hL.intern_zero n,
    internSucc_spec p hL.succ_find hL.succ_push hL.intern_succ n,
    internSort_spec p hL.sort_find hL.sort_push hL.intern_sort n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap]

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
                  (AM.st (internLNode .zero) a₃))) a₅,
                maxNatSize := maxNatSizeDefault } }) := by
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
  simp only [pinW, h.arr PINS (by decide) (by decide)]

theorem pinW_fill (m : Mem) (us z s1 : Word) (i : Nat) (hs : 73 ≤ (m.arr64 PINS).size) :
    pinW (irpFill m us z s1) i =
      if i = 0 then 1 else if i = 72 then 134217728 else if i = 54 then s1 else if i = 53 then z
      else if i = 52 then us else pinW m i := by
  have s1' : ((m.set64 PINS 52 us).arr64 PINS).size = (m.arr64 PINS).size := L.Mem.size64_set64 _ _ _ _ _
  have s2' : (((m.set64 PINS 52 us).set64 PINS 53 z).arr64 PINS).size = (m.arr64 PINS).size := by
    rw [L.Mem.size64_set64, s1']
  have s3' : ((((m.set64 PINS 52 us).set64 PINS 53 z).set64 PINS 54 s1).arr64 PINS).size =
      (m.arr64 PINS).size := by rw [L.Mem.size64_set64, s2']
  have s4' : (((((m.set64 PINS 52 us).set64 PINS 53 z).set64 PINS 54 s1).set64 PINS 72
      134217728).arr64 PINS).size = (m.arr64 PINS).size := by rw [L.Mem.size64_set64, s3']
  simp only [irpFill]
  rw [pinW_set _ _ _ _ (by rw [s4']; simp; omega), pinW_set _ _ _ _ (by rw [s3']; simp; omega),
    pinW_set _ _ _ _ (by rw [s2']; simp; omega),
    pinW_set _ _ _ _ (by rw [s1']; simp; omega), pinW_set _ _ _ _ (by simp; omega)]
  by_cases h0 : i = 0 <;> simp [h0] <;> by_cases h7 : i = 72 <;> simp [h7] <;>
    by_cases h4 : i = 54 <;> simp [h4] <;>
    by_cases h3 : i = 53 <;> simp [h3] <;> by_cases h2 : i = 52 <;> simp [h2]

theorem irpFill_frame (m : Mem) (us z s1 : Word) : MemFrame [PINS] [] m (irpFill m us z s1) := by
  simp only [irpFill]
  exact ((((MemFrame.set64 _ PINS (by decide) _ _).trans (MemFrame.set64 _ PINS (by decide) _ _)).trans
    (MemFrame.set64 _ PINS (by decide) _ _)).trans (MemFrame.set64 _ PINS (by decide) _ _)).trans
    (MemFrame.set64 _ PINS (by decide) _ _)

theorem ArenaD.with_pins {m : Mem} {a : AState} (P : Pins) (h : ArenaD m a) :
    ArenaD m { a with pins := P } := by
  obtain ⟨hR, hD⟩ := h
  exact ⟨{ hR with }, { hD with }⟩

theorem pinNames_length : pinNames.length = 52 := by simp [pinNames]

theorem reserved_length : reservedBasisNameValues.length = 16 := by simp [reservedBasisNameValues]

theorem internNameList_append_run (xs ys : List ConLeche.Name) : ∀ (a a₁ a₂ : AState) (hs hs' : List NIdx),
    (internNameList xs).run a = .ok (hs, a₁) → (internNameList ys).run a₁ = .ok (hs', a₂) →
    (internNameList (xs ++ ys)).run a = .ok (hs ++ hs', a₂) := by
  induction xs with
  | nil => intro a a₁ a₂ hs hs' h1 h2; simp only [internNameList] at h1; cases h1; exact h2
  | cons x xs ih =>
    intro a a₁ a₂ hs hs' h1 h2
    simp only [List.cons_append, internNameList] at h1 ⊢
    cases hx : (internName x).run a with
    | error e => rw [StateT.run_bind, hx] at h1; cases h1
    | ok p =>
      obtain ⟨h, a₀⟩ := p
      rw [L.Rom.run_bind_of _ _ _ _ _ hx] at h1
      cases hr : (internNameList xs).run a₀ with
      | error e => rw [StateT.run_bind, hr] at h1; cases h1
      | ok p' =>
        obtain ⟨hs0, a₀'⟩ := p'
        rw [L.Rom.run_bind_of _ _ _ _ _ hr] at h1
        have e : (pure (h :: hs0) : AM (List NIdx)).run a₀' = .ok (h :: hs0, a₀') := rfl
        rw [e] at h1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [L.Rom.run_bind_of _ _ _ _ _ hx, L.Rom.run_bind_of _ _ _ _ _ (ih a₀ _ a₂ hs0 hs' hr h2)]
        rfl

theorem internNameList_append (xs ys : List ConLeche.Name) (a : AState) (h1 : AM.ok (internNameList xs) a)
    (h2 : AM.ok (internNameList ys) (AM.st (internNameList xs) a)) :
    AM.ok (internNameList (xs ++ ys)) a ∧
      AM.st (internNameList (xs ++ ys)) a = AM.st (internNameList ys) (AM.st (internNameList xs) a) ∧
      AM.res (internNameList (xs ++ ys)) a =
        AM.res (internNameList xs) a ++ AM.res (internNameList ys) (AM.st (internNameList xs) a) :=
  AM.of_run_ok _ _ _ _ (internNameList_append_run xs ys _ _ _ _ _ (AM.run_of_ok _ _ h1) (AM.run_of_ok _ _ h2))

theorem encNames_append (xs ys : List ConLeche.Name) : encNames (xs ++ ys) = encNames xs ++ encNames ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, encNames, ih, List.append_assoc]

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
    (n : Nat) (m : Mem) (a : AState) (r : Word) (m' : Mem) (hA : ArenaD m a) (hmo : ModeOK m)
    (hW : irpW rom off n m = some (r, m')) :
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
  have hP : 73 ≤ (m.arr64 PINS).size := Nat.le_of_not_lt fun hc => hlen (by
    simp only [Mem.len64]; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hc (by decide))]; simp; omega)
  have hsplit : pinNames = pinNames.take 51 ++ pinNames.drop 51 := (List.take_append_drop 51 pinNames).symm
  have hlA : (pinNames.take 51).length = 51 := by simp [pinNames_length]
  have hlB : (pinNames.drop 51).length = 1 := by simp [pinNames_length]
  have hfA : (pinNames.take 51).all nameFits = true := by
    rw [List.all_eq_true] at hf1 ⊢; exact fun x hx => hf1 x (List.mem_of_mem_take hx)
  have hfB : (pinNames.drop 51).all nameFits = true := by
    rw [List.all_eq_true] at hf1 ⊢; exact fun x hx => hf1 x (List.mem_of_mem_drop hx)
  have hd' : rom.drop off.toNat = encNames (pinNames.take 51) ++
      (encNames (pinNames.drop 51) ++ (encNames reservedBasisNameValues ++ rest)) := by
    rw [hd]; conv => lhs; rw [hsplit]
    rw [encNames_append, List.append_assoc]
  cases h1 : romNamesToW rom n m off 51 1 with
  | none => rw [h1] at hW; simp [irpW.k_rom_names_to] at hW
  | some t =>
  obtain ⟨q, m₁⟩ := t
  rw [h1] at hW
  simp only [irpW.k_rom_names_to] at hW
  obtain ⟨ok1, hR1, hq, hf1', hl1, hj1, hk1⟩ := romNamesToW_ok rom hr _ hfA n m a off _ 51 1 q m₁ hA hmo
    hd' (by simp [hlA]) (by simp [hlA]) (by simp [hlA]; omega) h1
  have hd1 : rom.drop q.toNat = encNames (pinNames.drop 51) ++ (encNames reservedBasisNameValues ++ rest) :=
    drop_shift rom off (encNames (pinNames.take 51)) (encNames (pinNames.drop 51))
      (encNames reservedBasisNameValues ++ rest) (by rw [hd', List.append_assoc]) q hq
  have hmo1 := (romNamesToW_topK rom _ _ _ _ _ _ _ h1).mode hA.base.lit.1 hmo
  cases h1b : romNamesToW rom n m₁ q 1 71 with
  | none => rw [h1b] at hW; simp [irpW.k_rom_names_to_2] at hW
  | some t =>
  obtain ⟨q₁, m₁b⟩ := t
  rw [h1b] at hW
  simp only [irpW.k_rom_names_to_2] at hW
  obtain ⟨ok1b, hR1b, hq1, hf1b', hl1b, hj1b, hk1b⟩ := romNamesToW_ok rom hr _ hfB n m₁ _ q _ 1 71 q₁ m₁b hR1
    hmo1 hd1 (by simp [hlB]) (by simp [hlB])
    (by simp [hlB]; rw [hf1'.size]; omega) h1b
  have hd2 : rom.drop q₁.toNat = encNames reservedBasisNameValues ++ rest :=
    drop_shift rom q (encNames (pinNames.drop 51)) (encNames reservedBasisNameValues) rest
      (by rw [hd1, List.append_assoc]) q₁ hq1
  obtain ⟨okP, stP, resP⟩ := internNameList_append _ _ a ok1 ok1b
  rw [← hsplit] at okP stP resP
  rw [← stP] at hR1b
  have hmo1b := ((romNamesToW_topK rom _ _ _ _ _ _ _ h1).trans
    (romNamesToW_topK rom _ _ _ _ _ _ _ h1b)).mode hA.base.lit.1 hmo
  cases h2 : romNamesToW rom n m₁b q₁ 16 55 with
  | none => rw [h2] at hW; simp [irpW.k_rom_names_to_3] at hW
  | some t =>
  obtain ⟨q₂, m₂⟩ := t
  rw [h2] at hW
  simp only [irpW.k_rom_names_to_3] at hW
  obtain ⟨ok2, hR2, -, hf2', hl2, hj2, hk2⟩ := romNamesToW_ok rom hr reservedBasisNameValues hf2 n m₁b _ q₁
    rest 16 55 q₂ m₂ hR1b hmo1b hd2 (by simp [reserved_length]) (by simp [reserved_length])
    (by simp [reserved_length]; rw [hf1b'.size, hf1'.size]; omega) h2
  cases h3 : lsinternW m₂ 0 0 with
  | none => rw [h3] at hW; simp [irpW.k_intern_ls] at hW
  | some t =>
  obtain ⟨us, m₃⟩ := t
  rw [h3] at hW
  simp only [irpW.k_intern_ls] at hW
  split at hW
  case isTrue => simp at hW
  rename_i hus
  obtain ⟨ok3, hR3, res3, hf3⟩ := L.Front.internLs_D m₂ _ hR2 us m₃ 0 0 (by simp [SliceOK])
    [] (by simp [sliceL, lsWords]) (fun _ => by decide) h3
  cases h4 : zinternW m₃ with
  | none => rw [h4] at hW; simp [irpW.k_intern_zero] at hW
  | some t =>
  obtain ⟨z, m₄⟩ := t
  rw [h4] at hW
  simp only [irpW.k_intern_zero] at hW
  split at hW
  case isTrue => simp at hW
  rename_i hz
  obtain ⟨ok4, hR4, res4, hf4⟩ := L.Front.zero_A m₃ _ hR3 z m₄ h4
  cases h5 : sinternW m₄ z with
  | none => rw [h5] at hW; simp [irpW.k_intern_succ] at hW
  | some t =>
  obtain ⟨o, m₅⟩ := t
  rw [h5] at hW
  simp only [irpW.k_intern_succ] at hW
  split at hW
  case isTrue => simp at hW
  rename_i ho
  have hzl : z.toNat < 2 ^ 32 := by simp at hz; exact UInt64.lt_iff_toNat_lt.mp hz
  obtain ⟨ok5, hR5, res5, hf5⟩ := L.Front.succ_A m₄ _ hR4 o m₅ z hzl h5
  cases h6 : sointernW m₅ o with
  | none => rw [h6] at hW; simp [irpW.k_intern_sort] at hW
  | some t =>
  obtain ⟨s1, m₆⟩ := t
  rw [h6] at hW
  simp only [irpW.k_intern_sort] at hW
  split at hW
  case isTrue => simp at hW
  rename_i hs1
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨-, hW⟩ := hW
  change irpFill _ us z s1 = m' at hW
  subst hW
  have hol : o.toNat < 2 ^ 32 := by simp at ho; exact UInt64.lt_iff_toNat_lt.mp ho
  obtain ⟨ok6, hR6, res6, hf6⟩ := L.Front.internSort_D m₅ _ hR5 s1 m₆ o hol h6
  rw [← res4] at ok5 hR5 res5 ok6 hR6 res6
  rw [← res5] at ok6 hR6 res6
  have hrun := internReservedPins_run a okP ok2 ok3 _ rfl ok4 ok5 _ rfl ok6
  obtain ⟨okX, stX, -⟩ := AM.of_run_ok _ _ _ _ hrun
  have hfS : MemFrame StoreA StoreC m₂ m₆ :=
    ((frame_store hf3 (by simp [tier1, lsSch, LSREC, LSSLOT, LSHP]) (by simp [lsSch])).trans
      (frame_store hf4 (by simp [tier1, zeroSch, ZREC, ZSLOT]) (by simp [zeroSch]))).trans
      ((frame_store hf5 (by simp [tier1, succSch, SREC, SSLOT, SHP]) (by simp [succSch])).trans
      (frame_store hf6 (by simp [tier1, sortSch, SOREC, SOSLOT, SOLP]) (by simp [sortSch])))
  have hsz : (m₆.arr64 PINS).size = (m.arr64 PINS).size := by
    rw [hfS.size, hf2'.size, hf1b'.size, hf1'.size]
  have hsz72 : 73 ≤ (m.arr64 PINS).size := by
    have : ¬ (UInt64.ofNat (m.arr64 PINS).size) < 73 := by simpa [Mem.len64] using hlen
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', show (73 : UInt64).toNat = 73 from rfl] at this
    have := Nat.mod_le (m.arr64 PINS).size (2 ^ 64)
    omega
  have hpw := fun i => pinW_fill m₆ us z s1 i (by omega)
  have h26 := fun i => pinW_frame hfS i
  refine ⟨okX, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stX]
    exact ArenaD.with_pins _ (L.Arena.ArenaD.frameHi (irpFill_frame m₆ us z s1) (by simp [PINS]) (by simp) hR6)
  · rw [stX]
    simp only [reserved_length, show (55 : UInt64).toNat = 55 from rfl] at hk2
    simp only [hlB, show (71 : UInt64).toNat = 71 from rfl] at hk1b hj1b hl1b
    simp only [hlA, show (1 : UInt64).toNat = 1 from rfl] at hl1 hj1
    have hlo : ∀ i, 1 ≤ i → i < 52 → pinW (irpFill m₆ us z s1) i = pinW m₁ i := fun i h1 h2 => by
      rw [hpw, h26, hk2 i (.inl (by omega)), hk1b i (.inl (by omega))]
      have e0 : i ≠ 0 := by omega
      have e7 : i ≠ 72 := by omega
      have e4 : i ≠ 54 := by omega
      have e3 : i ≠ 53 := by omega
      have e2 : i ≠ 52 := by omega
      rw [ite_eq_right e0, ite_eq_right e7, ite_eq_right e4, ite_eq_right e3, ite_eq_right e2]
    have h71 : pinW (irpFill m₆ us z s1) 71 = pinW m₁b 71 := by
      rw [hpw, h26, hk2 71 (.inr (by omega))]; simp
    have hhi : ∀ i, 55 ≤ i → i ≠ 72 → pinW (irpFill m₆ us z s1) i = pinW m₂ i := fun i h1 h7 => by
      rw [hpw, h26]
      have e0 : i ≠ 0 := by omega
      have e4 : i ≠ 54 := by omega
      have e3 : i ≠ 53 := by omega
      have e2 : i ≠ 52 := by omega
      rw [ite_eq_right e0, ite_eq_right h7, ite_eq_right e4, ite_eq_right e3, ite_eq_right e2]
    have h72 : pinW (irpFill m₆ us z s1) 72 = 134217728 := by rw [hpw]; simp
    have h52 : pinW (irpFill m₆ us z s1) 52 = us := by rw [hpw]; simp
    have h53 : pinW (irpFill m₆ us z s1) 53 = z := by rw [hpw]; simp
    have h54 : pinW (irpFill m₆ us z s1) 54 = s1 := by rw [hpw]; simp
    simp only [reserved_length, show (55 : UInt64).toNat = 55 from rfl] at hl2 hj2
    have hget : ∀ i (h : i < 52), (AM.res (internNameList pinNames) a)[i]? =
        some (decI (if i < 51 then pinW m₁ (1 + i) else pinW m₁b 71)) := fun i h => by
      rw [resP]
      by_cases hi : i < 51
      · rw [List.getElem?_append_left (by omega), ite_eq_left hi]
        simpa [Nat.add_comm] using (hj1 i hi).1
      · rw [List.getElem?_append_right (by omega), ite_eq_right hi, hl1, show i - 51 = 0 by omega]
        simpa using (hj1b 0 (by omega)).1
    have hlenP : (AM.res (internNameList pinNames) a).length = 52 := by
      rw [resP, List.length_append, hl1, hl1b]
    refine { size := ?_, names_size := ?_, names_lt := ?_, names := ?_, quotMk_lt := ?_, quotMk := ?_,
             lv_lt := ?_, emptyLevels := ?_, zeroLevel := ?_, sortOne := ?_, reserved_lt := ?_,
             reserved := ?_, maxNatSize := by rw [h72]; rfl }
    · rw [(irpFill_frame m₆ us z s1).size, hsz]; exact hsz72
    · simp [hlenP]
    · intro i hi
      rw [hlo _ (by omega) (by omega)]
      simpa [Nat.add_comm] using (hj1 i hi).2
    · intro i hi
      rw [hlo _ (by omega) (by omega)]
      have := hget i (by omega)
      rw [ite_eq_left hi] at this
      simp only [List.getElem_toArray]
      rw [List.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    · rw [h71]; simpa using (hj1b 0 (by omega)).2
    · rw [h71]
      have := hget 51 (by omega)
      rw [ite_eq_right (by omega)] at this
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
      rw [hhi _ (by omega) (by omega)]
      exact (hj2 i hi).2
    · dsimp only
      apply List.ext_getElem
      · simp [hl2]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [hhi _ (by omega) (by omega)]
        have := (hj2 i (by omega)).1
        rw [List.getElem?_eq_getElem h1] at this
        exact Option.some.inj this
  · rw [hpw]; simp
  · refine hf1'.trans (hf1b'.trans (hf2'.trans ((frame_pinA hfS).trans ?_)))
    exact (irpFill_frame m₆ us z s1).mono (by simp [PinA]) (by simp)
  · exact (((((((romNamesToW_topK rom _ _ _ _ _ _ _ h1).trans (romNamesToW_topK rom _ _ _ _ _ _ _ h1b)).trans
      (romNamesToW_topK rom _ _ _ _ _ _ _ h2)).trans
      (cons_topK lsCS_wf (by decide) (by decide) h3)).trans (cons_topK zeroCS_wf (by decide) (by decide) h4)).trans
      (cons_topK succCS_wf (by decide) (by decide) h5)).trans ((cons_topK sortCS_wf (by decide) (by decide) h6).trans
      (memFrame_top (irpFill_frame m₆ us z s1) (by simp)))).mode hA.base.lit.1 hmo

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
    (internReservedPins_specW rom off p hL n s₀ ⟨hA.base.lit.1.cap, hA.base.lit.1.top41⟩)
  subst hs
  exact ⟨hloc, irpW_ok rom hr off rest hd hf1 hf2 n _ a₀ _ _ hA hmo hW⟩

end L.Rom
