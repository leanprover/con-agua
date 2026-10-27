import ConAgua.Rom.PinRead
import ConAgua.Arena.IndMaster
import ConAgua.Arena.PromoteCIRef.Of

/-!
# The pin-data readers compute their models (lane `romload`)

The W-models of the new L functions of `ConAgua/Rom/PinRead.lean`, and their "computes its
model" specs, for the ROM version of the program (`Prog.subPB bs`, `rom := bs`):

* `pb_check` (`pbCheck.subPB rom = pbCheckG rom romData`): `rom = romData ++ rom.drop |romData|`.
* `rom_exprs_to`, `rom_pins_to`, `rom_lists_to`, `rom_tpairs_to`, `rom_tpins_to`, `rom_sets_to`,
  `intern_pin_sets`, `rom_pin_sets`: no `PB` read, so `f.subPB bs = f`; models `romExprsToW`,
  `romPinsToW`, `romListsToW`, `romTPairsToW`, `romTPinsToW`, `romSetsToW`, `internPinSetsW`,
  `romPinSetsW`.
* `intern_all_pins`: `internAllPinsW` (no `PB` read either).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Rom

open L.Arena L.Ind

/-! ## `pb_check()` -/

/-- `pb_check`'s loop, over any two byte strings (`bs` the buffer, `d` the expected prefix). -/
def pbLoop (bs d : List UInt8) : Stmt := lblk (i) {
  while i < len(d.c8) {
    if bs.c8[i] != d.c8[i] { abort };
    i += 1
  }
}

/-- `pb_check` over the buffer `bs`, expecting the prefix `d`. -/
-- con-ron: none — the pin-data buffer's header (the startup data the twin interns exactly)
def pbCheckG (bs d : List UInt8) : FunDecl := lfn () locals (i) {
  if len(bs.c8) < len(d.c8) { abort };
  ⟪pbLoop bs d⟫;
  return 0
}

theorem pbCheck_subPB (bs : List UInt8) : pbCheck.subPB bs = pbCheckG bs romData := by
  rw [← romDataLit_eq]; rfl

section eqW
variable (bs d : List UInt8)

/-- The model of the loop: bytes `j ‥ |d|` of `bs` and `d` agree (as words). -/
def eqW (j : Word) : Bool :=
  if j < UInt64.ofNat d.length then decide (romB bs j = romB d j) && eqW (j + 1) else true
termination_by (UInt64.ofNat d.length).toNat - j.toNat
decreasing_by
  have : j.toNat < (UInt64.ofNat d.length).toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹_›
  have := (UInt64.ofNat d.length).toNat_lt
  have : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

theorem eqW_end (j : Word) (hj : ¬ j < UInt64.ofNat d.length) : eqW bs d j = true := by
  rw [eqW]; simp only [hj, ↓reduceIte]

theorem eqW_step (j j' : Word) (hj : j < UInt64.ofNat d.length) (hj' : j' = j + 1)
    (hb : romB bs j = romB d j) : eqW bs d j = eqW bs d j' := by
  subst hj'
  rw [eqW]; simp [hj, hb]

/-- `eqW` from `j` on: the bytes agree. -/
theorem eqW_get (hd : d.length < 2 ^ 63) (hl : d.length ≤ bs.length) :
    ∀ (e : Nat) (j : Word), d.length - j.toNat = e → eqW bs d j = true →
      ∀ k, j.toNat ≤ k → k < d.length → bs[k]? = d[k]? := by
  have hdN : (UInt64.ofNat d.length).toNat = d.length := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  intro e
  induction e with
  | zero => intro j he _ k hk hk'; omega
  | succ e ih =>
    intro j he hW k hk hk'
    have hj : j < UInt64.ofNat d.length := by rw [UInt64.lt_iff_toNat_lt, hdN]; omega
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rw [eqW] at hW
    simp only [hj, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hW
    by_cases hk0 : k = j.toNat
    · subst hk0
      have := hW.1
      simp only [romB, List.getElem?_eq_getElem (show j.toNat < bs.length by omega),
        List.getElem?_eq_getElem (show j.toNat < d.length by omega), Option.getD_some] at this
      have e : bs[j.toNat]'(by omega) = d[j.toNat]'(by omega) := by
        have h2 := congrArg UInt64.toNat this
        simp only [UInt8.toNat_toUInt64] at h2
        exact UInt8.toNat_inj.mp h2
      simp [List.getElem?_eq_getElem (show j.toNat < bs.length by omega),
        List.getElem?_eq_getElem (show j.toNat < d.length by omega), e]
    · exact ih (j + 1) (by omega) hW.2 k (by omega) hk'

end eqW

grind_pattern [arena_grind] eqW_end => eqW bs d j
grind_pattern [arena_grind] eqW_step => eqW bs d j, eqW bs d j'

section pbSpec
variable (p : Prog)

theorem pbLoop_spec (bs d : List UInt8) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (pbLoop bs d)
    ⦃fun r s' => r = .normal ∧ s'.mem = s₀.mem ∧ eqW bs d (s₀.loc 0) = true; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := pbLoop bs d) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ldc, ih] <;> finish [romB]


theorem pbCheckG_spec (bs d : List UInt8) (hp : p.lookup "pb_check" = some (pbCheckG bs d)) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pb_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      ¬ UInt64.ofNat bs.length < UInt64.ofNat d.length ∧ eqW bs d 0 = true; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pbCheckG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, fun s₀ => Triple.step_exec (pbLoop_spec p bs d (n + 1) s₀)] <;>
      finish

/-- What `pb_check`'s checks give: the buffer starts with `d`. -/
theorem pbCheck_prefix (bs d : List UInt8) (hb : RomOK bs) (hd : d.length < 2 ^ 63)
    (h1 : ¬ UInt64.ofNat bs.length < UInt64.ofNat d.length) (h2 : eqW bs d 0 = true) :
    d.length ≤ bs.length ∧ (∀ i < d.length, bs[i]? = d[i]?) ∧ bs = d ++ bs.drop d.length := by
  simp only [RomOK] at hb
  have hl : d.length ≤ bs.length := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hg := eqW_get bs d hd hl _ 0 rfl h2
  have hg' : ∀ i < d.length, bs[i]? = d[i]? := fun i hi => hg i (by simp) hi
  refine ⟨hl, hg', ?_⟩
  have ht : bs.take d.length = d := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < d.length
    · rw [List.getElem?_take_of_lt hi, hg' i hi]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  conv => lhs; rw [← List.take_append_drop d.length bs]
  rw [ht]

/-- **`pb_check` (ROM version) computes its model**: the buffer starts with `romData`. -/
theorem pbCheck_specW (rom : List UInt8) (hr : RomOK rom)
    (hp : p.lookup "pb_check" = some (pbCheck.subPB rom)) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "pb_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ romData.length ≤ rom.length ∧
      (∀ i < romData.length, rom[i]? = romData[i]?) ∧ rom = romData ++ rom.drop romData.length; ⊤⦄ := by
  rw [pbCheck_subPB] at hp
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hm, h1, h2⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (pbCheckG_spec p rom romData hp n s₀)
  exact ⟨hloc, hm, pbCheck_prefix rom romData hr romData_len h1 h2⟩

end pbSpec

/-! ## The functions without `PB` reads -/

theorem internAllPinsPB_subPB (bs : List UInt8) : internAllPinsPB.subPB bs = internAllPinsPB := rfl

/-! ## The models -/

section models
variable (rom : List UInt8)

mutual
/-- **The model of `rom_exprs_to(q, o, k)`**: the position after, the memory after. -/
def romExprsToW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, o, k => if k = 0 then some (q, m) else exsToK n o k (romExprW rom n m q)

/-- After one expression: its handle to `EREC[o]`, then the rest. -/
def exsToK (n : Nat) (o k : Word) : Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (h, q', m₁) => romExprsToW n (m₁.set64 EREC o h) q' (o + 1) (k - 1)
end

/-- After one pin: the next. -/
def pinsK (romPinsToW : Mem → Word → Word → Word → Option (Word × Mem)) (r k : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q', m₁) => romPinsToW m₁ q' r (k + 1)

/-- **The model of `rom_pins_to(q, r, k)`**. -/
def romPinsToW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, r, k =>
    if k = 8 then some (q, m)
    else if rclearOK m then pinsK (romPinsToW n) r k (romExprsToW rom n (resetMem m) q (r + k) 1)
    else none

/-- A certificate list's slice header written to the variant's record. -/
def listHdr (m : Mem) (r j o l : Word) : Mem :=
  (m.set64 EREC (r + 8 + 2 * j) o).set64 EREC (r + 9 + 2 * j) l

/-- After a certificate list: the next. -/
def lists2K (romListsToW : Mem → Word → Word → Word → Option (Word × Mem)) (r j : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q', m₃) => romListsToW m₃ q' r (j + 1)

/-- After the list's slice was allocated. -/
def listsK (n : Nat) (romListsToW : Mem → Word → Word → Word → Option (Word × Mem)) (q r j l : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (o, m₁) =>
    if rclearOK (listHdr m₁ r j o l) then
      lists2K romListsToW r j (romExprsToW rom n (resetMem (listHdr m₁ r j o l)) (q + 8) o l)
    else none

/-- **The model of `rom_lists_to(q, r, j)`** (the count inside the ROM, as `rom_u64` checks). -/
def romListsToW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, r, j =>
    if j = 8 then some (q, m)
    else if ¬ u64OK rom q then none
    else listsK rom n (romListsToW n) q r j (u64W rom q) (erAllocW m (u64W rom q))

/-- After a type pin's type: the next pin. -/
def tp2K (romTPairsToW : Mem → Word → Word → Word → Option (Word × Mem)) (o k : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q', m₂) => romTPairsToW m₂ q' (o + 2) (k - 1)

/-- After a type pin's name: its handle to `EREC[o]`, a memo reset, the type to `EREC[o + 1]`. -/
def tpK (n : Nat) (romTPairsToW : Mem → Word → Word → Word → Option (Word × Mem)) (o k : Word) :
    Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (h, q', m₁) =>
    if rclearOK (m₁.set64 EREC o h) then
      tp2K romTPairsToW o k (romExprsToW rom n (resetMem (m₁.set64 EREC o h)) q' (o + 1) 1)
    else none

/-- **The model of `rom_tpairs_to(q, o, k)`**. -/
def romTPairsToW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, o, k => if k = 0 then some (q, m) else tpK rom n (romTPairsToW n) o k (romNameW rom n m q)

/-- A type-pin list's slice header written to the variant's record. -/
def tpinsHdr (m : Mem) (r j o l : Word) : Mem :=
  (m.set64 EREC (r + 24 + 2 * j) o).set64 EREC (r + 25 + 2 * j) l

/-- After a type-pin list: the next. -/
def tpins2K (romTPinsToW : Mem → Word → Word → Word → Option (Word × Mem)) (r j : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q', m₃) => romTPinsToW m₃ q' r (j + 1)

/-- After the list's slice was allocated. -/
def tpinsK (n : Nat) (romTPinsToW : Mem → Word → Word → Word → Option (Word × Mem)) (q r j l : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (o, m₁) => tpins2K romTPinsToW r j (romTPairsToW rom n (tpinsHdr m₁ r j o l) (q + 8) o l)

/-- **The model of `rom_tpins_to(q, r, j)`** (the count inside the ROM and below `2^32`). -/
def romTPinsToW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, r, j =>
    if j = 8 then some (q, m)
    else if ¬ u64OK rom q then none
    else if 4294967296 ≤ u64W rom q then none
    else tpinsK rom n (romTPinsToW n) q r j (u64W rom q) (erAllocW m (2 * u64W rom q))

/-- After a variant's type pins: the record's pointer to `EREC[o]`, then the next variant. -/
def sets4K (romSetsToW : Mem → Word → Word → Word → Option (Word × Mem)) (o k r : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q', m₄) => romSetsToW (m₄.set64 EREC o r) q' (o + 1) (k - 1)

/-- After a variant's lists. -/
def sets3K (n : Nat) (romSetsToW : Mem → Word → Word → Word → Option (Word × Mem)) (o k r : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q', m₃) => sets4K romSetsToW o k r (romTPinsToW rom n m₃ q' r 0)

/-- After a variant's pins. -/
def sets2K (n : Nat) (romSetsToW : Mem → Word → Word → Word → Option (Word × Mem)) (o k r : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q', m₂) => sets3K rom n romSetsToW o k r (romListsToW rom n m₂ q' r 0)

/-- After a variant's record was allocated. -/
def setsK (n : Nat) (romSetsToW : Mem → Word → Word → Word → Option (Word × Mem)) (q o k : Word) :
    Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => sets2K rom n romSetsToW o k r (romPinsToW rom n m₁ q r 0)

/-- **The model of `rom_sets_to(q, o, k)`**. -/
def romSetsToW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, q, o, k =>
    if k = 0 then some (q, m) else setsK rom n (romSetsToW n) q o k (erAllocW m 40)

/-- After the list of records was allocated. -/
def ipsK (n : Nat) (q c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (o, m₁) => romSetsToW rom n ((m₁.set64 CTL 150 o).set64 CTL 151 c) (q + 8) o c

/-- **The model of `intern_pin_sets(q)`** (the count inside the ROM). -/
def internPinSetsW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, q =>
    if ¬ u64OK rom q then none
    else ipsK rom n q (u64W rom q) (erAllocW m (u64W rom q))

/-- **The model of `rom_pin_sets()`**: `[IW offset, count]`. -/
def romPinSetsW : Nat → Mem → Option (List Word × Mem)
  | 0, _ => none
  | n + 1, m => erToIwW n m (rdW (m.arr64 CTL) 150) (rdW (m.arr64 CTL) 151)

/-- After the variant list. -/
def iap2K : Option (Word × Mem) → Option Mem
  | none => none
  | some (_, m₂) => some m₂

/-- After the startup items. -/
def iapK (n : Nat) : Option (Word × Mem) → Option Mem
  | none => none
  | some (q, m₁) => iap2K (internPinSetsW rom n m₁ q)

/-- **The model of `intern_all_pins()`** (ROM version): the memory after. -/
def internAllPinsW : Nat → Mem → Option Mem
  | 0, _ => none
  | n + 1, m => if rclearOK m then iapK rom n (romItemsW rom n (resetMem m) allPinsOff) else none

end models

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ : Mem) (q q' o k r j l h c : Word)
  (F : Mem → Word → Word → Word → Option (Word × Mem))

theorem romExprsToW_zero : romExprsToW rom (n + 1) m q o 0 = some (q, m) := by simp [romExprsToW]
theorem romExprsToW_succ (hk : k ≠ 0) :
    romExprsToW rom (n + 1) m q o k = exsToK rom n o k (romExprW rom n m q) := by
  simp [romExprsToW, hk]
theorem exsToK_some :
    exsToK rom n o k (some (h, q', m₁)) = romExprsToW rom n (m₁.set64 EREC o h) q' (o + 1) (k - 1) := by
  simp [exsToK]
theorem pinsK_some : pinsK F r k (some (q', m₁)) = F m₁ q' r (k + 1) := rfl
theorem romPinsToW_end : romPinsToW rom (n + 1) m q r 8 = some (q, m) := by simp [romPinsToW]
theorem romPinsToW_step (hk : k ≠ 8) (hc : rclearOK m) :
    romPinsToW rom (n + 1) m q r k =
      pinsK (romPinsToW rom n) r k (romExprsToW rom n (resetMem m) q (r + k) 1) := by
  simp [romPinsToW, hk, hc]
theorem lists2K_some : lists2K F r j (some (q', m₁)) = F m₁ q' r (j + 1) := rfl
theorem listsK_some (hc : rclearOK (listHdr m₁ r j o l)) :
    listsK rom n F q r j l (some (o, m₁)) =
      lists2K F r j (romExprsToW rom n (resetMem (listHdr m₁ r j o l)) (q + 8) o l) := by
  simp [listsK, hc]
theorem romListsToW_end : romListsToW rom (n + 1) m q r 8 = some (q, m) := by simp [romListsToW]
theorem romListsToW_step (hj : j ≠ 8) (hb : u64OK rom q) :
    romListsToW rom (n + 1) m q r j =
      listsK rom n (romListsToW rom n) q r j (u64W rom q) (erAllocW m (u64W rom q)) := by
  simp [romListsToW, hj, hb]
theorem tp2K_some : tp2K F o k (some (q', m₁)) = F m₁ q' (o + 2) (k - 1) := rfl
theorem tpK_some (hc : rclearOK (m₁.set64 EREC o h)) :
    tpK rom n F o k (some (h, q', m₁)) =
      tp2K F o k (romExprsToW rom n (resetMem (m₁.set64 EREC o h)) q' (o + 1) 1) := by
  simp [tpK, hc]
theorem romTPairsToW_zero : romTPairsToW rom (n + 1) m q o 0 = some (q, m) := by simp [romTPairsToW]
theorem romTPairsToW_succ (hk : k ≠ 0) :
    romTPairsToW rom (n + 1) m q o k = tpK rom n (romTPairsToW rom n) o k (romNameW rom n m q) := by
  simp [romTPairsToW, hk]
theorem tpins2K_some : tpins2K F r j (some (q', m₁)) = F m₁ q' r (j + 1) := rfl
theorem tpinsK_some :
    tpinsK rom n F q r j l (some (o, m₁)) = tpins2K F r j (romTPairsToW rom n (tpinsHdr m₁ r j o l) (q + 8) o l) :=
  rfl
theorem romTPinsToW_end : romTPinsToW rom (n + 1) m q r 8 = some (q, m) := by simp [romTPinsToW]
theorem romTPinsToW_step (hj : j ≠ 8) (hb : u64OK rom q) (hl : ¬ 4294967296 ≤ u64W rom q) :
    romTPinsToW rom (n + 1) m q r j =
      tpinsK rom n (romTPinsToW rom n) q r j (u64W rom q) (erAllocW m (2 * u64W rom q)) := by
  simp [romTPinsToW, hj, hb, hl]
theorem sets4K_some : sets4K F o k r (some (q', m₁)) = F (m₁.set64 EREC o r) q' (o + 1) (k - 1) := rfl
theorem sets3K_some :
    sets3K rom n F o k r (some (q', m₁)) = sets4K F o k r (romTPinsToW rom n m₁ q' r 0) := rfl
theorem sets2K_some :
    sets2K rom n F o k r (some (q', m₁)) = sets3K rom n F o k r (romListsToW rom n m₁ q' r 0) := rfl
theorem setsK_some : setsK rom n F q o k (some (r, m₁)) = sets2K rom n F o k r (romPinsToW rom n m₁ q r 0) :=
  rfl
theorem romSetsToW_zero : romSetsToW rom (n + 1) m q o 0 = some (q, m) := by simp [romSetsToW]
theorem romSetsToW_succ (hk : k ≠ 0) :
    romSetsToW rom (n + 1) m q o k = setsK rom n (romSetsToW rom n) q o k (erAllocW m 40) := by
  simp [romSetsToW, hk]
theorem ipsK_some :
    ipsK rom n q c (some (o, m₁)) = romSetsToW rom n ((m₁.set64 CTL 150 o).set64 CTL 151 c) (q + 8) o c :=
  rfl
theorem internPinSetsW_eq (hb : u64OK rom q) :
    internPinSetsW rom (n + 1) m q = ipsK rom n q (u64W rom q) (erAllocW m (u64W rom q)) := by
  simp [internPinSetsW, hb]
theorem romPinSetsW_eq :
    romPinSetsW (n + 1) m = erToIwW n m (rdW (m.arr64 CTL) 150) (rdW (m.arr64 CTL) 151) := rfl
theorem iap2K_some : iap2K (some (q, m)) = some m := rfl
theorem iapK_some : iapK rom n (some (q, m)) = iap2K (internPinSetsW rom n m q) := rfl
theorem internAllPinsW_eq (hc : rclearOK m) :
    internAllPinsW rom (n + 1) m = iapK rom n (romItemsW rom n (resetMem m) allPinsOff) := by
  simp [internAllPinsW, hc]
end arms

attribute [arena_grind =] exsToK_some pinsK_some lists2K_some sets4K_some sets3K_some sets2K_some setsK_some
  tp2K_some tpins2K_some tpinsK_some romTPairsToW_zero romTPinsToW_end
  ipsK_some romPinSetsW_eq iapK_some iap2K_some romExprsToW_zero romPinsToW_end romListsToW_end romSetsToW_zero
grind_pattern [arena_grind] romExprsToW_succ => romExprsToW rom (n + 1) m q o k
grind_pattern [arena_grind] romPinsToW_step => romPinsToW rom (n + 1) m q r k
grind_pattern [arena_grind] listsK_some => listsK rom n F q r j l (some (o, m₁))
grind_pattern [arena_grind] romListsToW_step => romListsToW rom (n + 1) m q r j
grind_pattern [arena_grind] romSetsToW_succ => romSetsToW rom (n + 1) m q o k
grind_pattern [arena_grind] tpK_some => tpK rom n F o k (some (h, q', m₁))
grind_pattern [arena_grind] romTPairsToW_succ => romTPairsToW rom (n + 1) m q o k
grind_pattern [arena_grind] romTPinsToW_step => romTPinsToW rom (n + 1) m q r j
grind_pattern [arena_grind] internPinSetsW_eq => internPinSetsW rom (n + 1) m q
grind_pattern [arena_grind] internAllPinsW_eq => internAllPinsW rom (n + 1) m

/-! ## The models keep the top in a tier -/

@[arena_grind =] theorem erAllocMem_top (m : Mem) (k : Word) : (erAllocMem m k).top = m.top :=
  top_set64_ne _ _ _ (by decide)
@[arena_grind =] theorem erAllocMem_pcap (m : Mem) (k : Word) : pcap (erAllocMem m k) = pcap m :=
  pcap_set64 _ _ _ _

theorem erAllocW_topK {m m' : Mem} {k o : Word} (h : erAllocW m k = some (o, m')) : TopK m m' := by
  simp only [erAllocW] at h
  split at h; · cases h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact TopK.of_eq (erAllocMem_top _ _) (erAllocMem_pcap _ _) (flag_set64_ctl _ _ _ (by decide))

theorem erAllocW_eqs {m m' : Mem} {k o : Word} (h : erAllocW m k = some (o, m')) :
    m'.top = m.top ∧ pcap m' = pcap m := by
  simp only [erAllocW] at h
  split at h; · cases h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨erAllocMem_top _ _, erAllocMem_pcap _ _⟩
theorem erAllocW_top' (m m' : Mem) (k o : Word) (h : erAllocW m k = some (o, m')) : m'.top = m.top :=
  (erAllocW_eqs h).1
theorem erAllocW_pcap' (m m' : Mem) (k o : Word) (h : erAllocW m k = some (o, m')) : pcap m' = pcap m :=
  (erAllocW_eqs h).2
grind_pattern [arena_grind] erAllocW_top' => erAllocW m k, some (o, m')
grind_pattern [arena_grind] erAllocW_pcap' => erAllocW m k, some (o, m')

theorem resetMem_topK (m : Mem) : TopK m (resetMem m) := memFrame_top (resetMem_frame1 m) (by decide)

theorem setEREC_topK (m : Mem) (i v : Word) : TopK m (m.set64 EREC i v) :=
  TopK.of_eq (top_set64_arr _ _ _ _ (by decide)) (pcap_set64 _ _ _ _) (Mem.flag_set64_ne _ _ _ _ (by decide))

theorem romExprsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem),
    romExprsToW rom n m q o k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q o k q' m' hW; simp [romExprsToW] at hW
  | succ n ih =>
    intro m q o k q' m' hW
    by_cases hk : k = 0
    · subst hk; rw [romExprsToW_zero] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    rw [romExprsToW_succ rom n m q o k hk] at hW
    cases hP : romExprW rom n m q with
    | none => rw [hP] at hW; simp [exsToK] at hW
    | some r =>
      obtain ⟨h, q₁, m₁⟩ := r
      rw [hP, exsToK_some] at hW
      exact (((romExprW_topK rom n).1 m q h q₁ m₁ hP).trans (setEREC_topK _ _ _)).trans (ih _ _ _ _ _ _ hW)

theorem romPinsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q r k q' : Word) (m' : Mem),
    romPinsToW rom n m q r k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q r k q' m' hW; simp [romPinsToW] at hW
  | succ n ih =>
    intro m q r k q' m' hW
    by_cases hk : k = 8
    · subst hk; rw [romPinsToW_end] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    by_cases hc : rclearOK m
    case neg => simp [romPinsToW, hk, hc] at hW
    rw [romPinsToW_step (rom := rom) (n := n) (m := m) (q := q) (r := r) (k := k) hk hc] at hW
    cases hP : romExprsToW rom n (resetMem m) q (r + k) 1 with
    | none => rw [hP] at hW; simp [pinsK] at hW
    | some x =>
      obtain ⟨q₁, m₁⟩ := x
      rw [hP, pinsK_some] at hW
      exact ((resetMem_topK m).trans (romExprsToW_topK rom n _ _ _ _ _ _ hP)).trans (ih _ _ _ _ _ _ hW)

theorem romListsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q r j q' : Word) (m' : Mem),
    romListsToW rom n m q r j = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q r j q' m' hW; simp [romListsToW] at hW
  | succ n ih =>
    intro m q r j q' m' hW
    by_cases hj : j = 8
    · subst hj; rw [romListsToW_end] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    by_cases hb : u64OK rom q
    case neg => simp [romListsToW, hj, hb] at hW
    rw [romListsToW_step rom n m q r j hj hb] at hW
    cases hA : erAllocW m (u64W rom q) with
    | none => rw [hA] at hW; simp [listsK] at hW
    | some x =>
      obtain ⟨o, m₁⟩ := x
      rw [hA] at hW
      by_cases hc : rclearOK (listHdr m₁ r j o (u64W rom q))
      case neg => simp [listsK, hc] at hW
      rw [listsK_some (rom := rom) (n := n) (m₁ := m₁) (q := q) (r := r) (j := j) (o := o) (l := u64W rom q) (hc := hc)] at hW
      cases hP : romExprsToW rom n (resetMem (listHdr m₁ r j o (u64W rom q))) (q + 8) o (u64W rom q) with
      | none => rw [hP] at hW; simp [lists2K] at hW
      | some y =>
        obtain ⟨q₁, m₂⟩ := y
        rw [hP, lists2K_some] at hW
        exact ((((erAllocW_topK hA).trans ((setEREC_topK _ _ _).trans (setEREC_topK _ _ _))).trans
          (resetMem_topK _)).trans (romExprsToW_topK rom n _ _ _ _ _ _ hP)).trans (ih _ _ _ _ _ _ hW)

theorem romTPairsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem),
    romTPairsToW rom n m q o k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q o k q' m' hW; simp [romTPairsToW] at hW
  | succ n ih =>
    intro m q o k q' m' hW
    by_cases hk : k = 0
    · subst hk; rw [romTPairsToW_zero] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    rw [romTPairsToW_succ rom n m q o k hk] at hW
    cases hN : romNameW rom n m q with
    | none => rw [hN] at hW; simp [tpK] at hW
    | some x =>
      obtain ⟨h, q₁, m₁⟩ := x
      rw [hN] at hW
      by_cases hc : rclearOK (m₁.set64 EREC o h)
      case neg => simp [tpK, hc] at hW
      rw [tpK_some (rom := rom) (n := n) (m₁ := m₁) (o := o) (h := h) (q' := q₁) (k := k) (F := romTPairsToW rom n) hc] at hW
      cases hP : romExprsToW rom n (resetMem (m₁.set64 EREC o h)) q₁ (o + 1) 1 with
      | none => rw [hP] at hW; simp [tp2K] at hW
      | some y =>
        obtain ⟨q₂, m₂⟩ := y
        rw [hP, tp2K_some] at hW
        exact ((((romNameW_topK hN).trans (setEREC_topK _ _ _)).trans (resetMem_topK _)).trans
          (romExprsToW_topK rom n _ _ _ _ _ _ hP)).trans (ih _ _ _ _ _ _ hW)

theorem romTPinsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q r j q' : Word) (m' : Mem),
    romTPinsToW rom n m q r j = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q r j q' m' hW; simp [romTPinsToW] at hW
  | succ n ih =>
    intro m q r j q' m' hW
    by_cases hj : j = 8
    · subst hj; rw [romTPinsToW_end] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    by_cases hb : u64OK rom q
    case neg => simp [romTPinsToW, hj, hb] at hW
    by_cases hl : 4294967296 ≤ u64W rom q
    · simp [romTPinsToW, hj, hb, hl] at hW
    rw [romTPinsToW_step rom n m q r j hj hb hl] at hW
    cases hA : erAllocW m (2 * u64W rom q) with
    | none => rw [hA] at hW; simp [tpinsK] at hW
    | some x =>
      obtain ⟨o, m₁⟩ := x
      rw [hA, tpinsK_some] at hW
      cases hP : romTPairsToW rom n (tpinsHdr m₁ r j o (u64W rom q)) (q + 8) o (u64W rom q) with
      | none => rw [hP] at hW; simp [tpins2K] at hW
      | some y =>
        obtain ⟨q₁, m₂⟩ := y
        rw [hP, tpins2K_some] at hW
        exact (((erAllocW_topK hA).trans ((setEREC_topK _ _ _).trans (setEREC_topK _ _ _))).trans
          (romTPairsToW_topK rom n _ _ _ _ _ _ hP)).trans (ih _ _ _ _ _ _ hW)

theorem romSetsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem),
    romSetsToW rom n m q o k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q o k q' m' hW; simp [romSetsToW] at hW
  | succ n ih =>
    intro m q o k q' m' hW
    by_cases hk : k = 0
    · subst hk; rw [romSetsToW_zero] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    rw [romSetsToW_succ rom n m q o k hk] at hW
    cases hA : erAllocW m 40 with
    | none => rw [hA] at hW; simp [setsK] at hW
    | some x =>
      obtain ⟨r, m₁⟩ := x
      rw [hA, setsK_some] at hW
      cases hP : romPinsToW rom n m₁ q r 0 with
      | none => rw [hP] at hW; simp [sets2K] at hW
      | some y =>
        obtain ⟨q₁, m₂⟩ := y
        rw [hP, sets2K_some] at hW
        cases hQ : romListsToW rom n m₂ q₁ r 0 with
        | none => rw [hQ] at hW; simp [sets3K] at hW
        | some z =>
          obtain ⟨q₂, m₃⟩ := z
          rw [hQ, sets3K_some] at hW
          cases hT : romTPinsToW rom n m₃ q₂ r 0 with
          | none => rw [hT] at hW; simp [sets4K] at hW
          | some w =>
            obtain ⟨q₃, m₄⟩ := w
            rw [hT, sets4K_some] at hW
            exact (((((erAllocW_topK hA).trans (romPinsToW_topK rom n _ _ _ _ _ _ hP)).trans
              (romListsToW_topK rom n _ _ _ _ _ _ hQ)).trans (romTPinsToW_topK rom n _ _ _ _ _ _ hT)).trans
              (setEREC_topK _ _ _)).trans (ih _ _ _ _ _ _ hW)

theorem romExprsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem)
    (hW : romExprsToW rom n m q o k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romExprsToW_topK rom n m q o k q' m' hW hc ht).1
grind_pattern [arena_grind] romExprsToW_top' => romExprsToW rom n m q o k, some (q', m')
theorem romPinsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q r k q' : Word) (m' : Mem)
    (hW : romPinsToW rom n m q r k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romPinsToW_topK rom n m q r k q' m' hW hc ht).1
grind_pattern [arena_grind] romPinsToW_top' => romPinsToW rom n m q r k, some (q', m')
theorem romListsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q r j q' : Word) (m' : Mem)
    (hW : romListsToW rom n m q r j = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romListsToW_topK rom n m q r j q' m' hW hc ht).1
grind_pattern [arena_grind] romListsToW_top' => romListsToW rom n m q r j, some (q', m')
theorem romSetsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem)
    (hW : romSetsToW rom n m q o k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romSetsToW_topK rom n m q o k q' m' hW hc ht).1
grind_pattern [arena_grind] romSetsToW_top' => romSetsToW rom n m q o k, some (q', m')
theorem romTPairsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem)
    (hW : romTPairsToW rom n m q o k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romTPairsToW_topK rom n m q o k q' m' hW hc ht).1
grind_pattern [arena_grind] romTPairsToW_top' => romTPairsToW rom n m q o k, some (q', m')
theorem romTPinsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q r j q' : Word) (m' : Mem)
    (hW : romTPinsToW rom n m q r j = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romTPinsToW_topK rom n m q r j q' m' hW hc ht).1
grind_pattern [arena_grind] romTPinsToW_top' => romTPinsToW rom n m q r j, some (q', m')

/-! ## The specs -/

/-- The functions the pin-data stage calls, for the ROM version of the program. -/
structure PinProg (rom : List UInt8) (p : Prog) : Prop extends ItemsProg rom p where
  pb_check : p.lookup "pb_check" = some (pbCheck.subPB rom)
  rom_exprs_to : p.lookup "rom_exprs_to" = some romExprsTo
  rom_pins_to : p.lookup "rom_pins_to" = some romPinsTo
  rom_lists_to : p.lookup "rom_lists_to" = some romListsTo
  rom_tpairs_to : p.lookup "rom_tpairs_to" = some romTPairsTo
  rom_tpins_to : p.lookup "rom_tpins_to" = some romTPinsTo
  rom_sets_to : p.lookup "rom_sets_to" = some romSetsTo
  intern_pin_sets : p.lookup "intern_pin_sets" = some internPinSetsL
  rom_pin_sets : p.lookup "rom_pin_sets" = some romPinSetsL
  intern_all_pins : p.lookup "intern_all_pins" = some (internAllPinsPB.subPB rom)
  erec_alloc : p.lookup "erec_alloc" = some erecAlloc
  iw_alloc : p.lookup "iw_alloc" = some iwAlloc
  er_copy : p.lookup "er_copy" = some erCopy
  er_to_iw : p.lookup "er_to_iw" = some erToIw

section spec
variable (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
include hL

theorem romExprsTo_specW (n : Nat) : ∀ (s₀ : St) (q o k : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_exprs_to" [q, o, k]
    ⦃fun r s' => LocEq s' s₀ ∧ romExprsToW rom n s₀.mem q o k = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q o k _
    rw [invoke_eq _ hL.rom_exprs_to]; simp only [callFn, romExprsTo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q o k hs
    have ih' := fun s₁ q₁ o₁ k₁ h₁ => Triple.keep hL.no_st8 (ih s₁ q₁ o₁ k₁ h₁)
    have he' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8
      ((romExpr_specsW rom p hL.toExprProg n).1 s₁ pos₁ h₁)
    rw [invoke_eq _ hL.rom_exprs_to]
    simp only [callFn, romExprsTo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, he', ih'] <;>
      finish [Keep.size, Keep.pcap]

theorem romPinsTo_specW (n : Nat) : ∀ (s₀ : St) (q r k : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_pins_to" [q, r, k]
    ⦃fun res s' => LocEq s' s₀ ∧ romPinsToW rom n s₀.mem q r k = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q r k _
    rw [invoke_eq _ hL.rom_pins_to]; simp only [callFn, romPinsTo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q r k hs
    have ih' := fun s₁ q₁ r₁ k₁ h₁ => Triple.keep hL.no_st8 (ih s₁ q₁ r₁ k₁ h₁)
    have hx' := fun s₁ q₁ o₁ k₁ h₁ => Triple.keep hL.no_st8 (romExprsTo_specW rom p hL n s₁ q₁ o₁ k₁ h₁)
    rw [invoke_eq _ hL.rom_pins_to]
    simp only [callFn, romPinsTo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hx', ih',
        memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n] <;>
      finish [Keep.size, Keep.pcap, resetMem, rclearOK, mclearG, rsetSch]

theorem romListsTo_specW (n : Nat) : ∀ (s₀ : St) (q r j : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_lists_to" [q, r, j]
    ⦃fun res s' => LocEq s' s₀ ∧ romListsToW rom n s₀.mem q r j = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q r j _
    rw [invoke_eq _ hL.rom_lists_to]; simp only [callFn, romListsTo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q r j hs
    have ih' := fun s₁ q₁ r₁ j₁ h₁ => Triple.keep hL.no_st8 (ih s₁ q₁ r₁ j₁ h₁)
    have hx' := fun s₁ q₁ o₁ k₁ h₁ => Triple.keep hL.no_st8 (romExprsTo_specW rom p hL n s₁ q₁ o₁ k₁ h₁)
    have ha' := fun s₁ k₁ => Triple.keep hL.no_st8 (erecAlloc_specW p hL.erec_alloc n s₁ k₁)
    rw [invoke_eq _ hL.rom_lists_to]
    simp only [callFn, romListsTo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hx', ih', ha',
        romU64_spec rom p hL.rom_u64 n,
        memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n] <;>
      finish [Keep.size, Keep.pcap, resetMem, rclearOK, mclearG, rsetSch, listHdr, u64OK]

theorem romTPairsTo_specW (n : Nat) : ∀ (s₀ : St) (q o k : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_tpairs_to" [q, o, k]
    ⦃fun res s' => LocEq s' s₀ ∧ romTPairsToW rom n s₀.mem q o k = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q o k _
    rw [invoke_eq _ hL.rom_tpairs_to]; simp only [callFn, romTPairsTo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q o k hs
    have ih' := fun s₁ q₁ o₁ k₁ h₁ => Triple.keep hL.no_st8 (ih s₁ q₁ o₁ k₁ h₁)
    have hx' := fun s₁ q₁ o₁ k₁ h₁ => Triple.keep hL.no_st8 (romExprsTo_specW rom p hL n s₁ q₁ o₁ k₁ h₁)
    have hn' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8
      (romName_specW rom p hL.toNameProg n s₁ pos₁ h₁)
    rw [invoke_eq _ hL.rom_tpairs_to]
    simp only [callFn, romTPairsTo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hx', hn', ih',
        memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n] <;>
      finish [Keep.size, Keep.pcap, resetMem, rclearOK, mclearG, rsetSch]

theorem romTPinsTo_specW (n : Nat) : ∀ (s₀ : St) (q r j : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_tpins_to" [q, r, j]
    ⦃fun res s' => LocEq s' s₀ ∧ romTPinsToW rom n s₀.mem q r j = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q r j _
    rw [invoke_eq _ hL.rom_tpins_to]; simp only [callFn, romTPinsTo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q r j hs
    have ih' := fun s₁ q₁ r₁ j₁ h₁ => Triple.keep hL.no_st8 (ih s₁ q₁ r₁ j₁ h₁)
    have hx' := fun s₁ q₁ o₁ k₁ h₁ => Triple.keep hL.no_st8 (romTPairsTo_specW rom p hL n s₁ q₁ o₁ k₁ h₁)
    have ha' := fun s₁ k₁ => Triple.keep hL.no_st8 (erecAlloc_specW p hL.erec_alloc n s₁ k₁)
    rw [invoke_eq _ hL.rom_tpins_to]
    simp only [callFn, romTPinsTo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hx', ih', ha',
        romU64_spec rom p hL.rom_u64 n] <;>
      finish [Keep.size, Keep.pcap, tpinsHdr, u64OK]

theorem romSetsTo_specW (n : Nat) : ∀ (s₀ : St) (q o k : Word), pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_sets_to" [q, o, k]
    ⦃fun res s' => LocEq s' s₀ ∧ romSetsToW rom n s₀.mem q o k = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ q o k _
    rw [invoke_eq _ hL.rom_sets_to]; simp only [callFn, romSetsTo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q o k hs
    have ih' := fun s₁ q₁ o₁ k₁ h₁ => Triple.keep hL.no_st8 (ih s₁ q₁ o₁ k₁ h₁)
    have hp' := fun s₁ q₁ r₁ k₁ h₁ => Triple.keep hL.no_st8 (romPinsTo_specW rom p hL n s₁ q₁ r₁ k₁ h₁)
    have hl' := fun s₁ q₁ r₁ j₁ h₁ => Triple.keep hL.no_st8 (romListsTo_specW rom p hL n s₁ q₁ r₁ j₁ h₁)
    have ht' := fun s₁ q₁ r₁ j₁ h₁ => Triple.keep hL.no_st8 (romTPinsTo_specW rom p hL n s₁ q₁ r₁ j₁ h₁)
    have ha' := fun s₁ k₁ => Triple.keep hL.no_st8 (erecAlloc_specW p hL.erec_alloc n s₁ k₁)
    rw [invoke_eq _ hL.rom_sets_to]
    simp only [callFn, romSetsTo]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hp', hl', ht', ih', ha'] <;>
      finish (gen := 30) (instances := 10000) [Keep.size, Keep.pcap, sets2K, sets3K, sets4K, setsK]

theorem internPinSets_specW (n : Nat) (s₀ : St) (q : Word) (hs : pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_pin_sets" [q]
    ⦃fun res s' => LocEq s' s₀ ∧ internPinSetsW rom n s₀.mem q = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.intern_pin_sets]
  simp only [callFn, internPinSetsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hs' := fun s₁ q₁ o₁ k₁ h₁ => Triple.keep hL.no_st8 (romSetsTo_specW rom p hL n s₁ q₁ o₁ k₁ h₁)
    have ha' := fun s₁ k₁ => Triple.keep hL.no_st8 (erecAlloc_specW p hL.erec_alloc n s₁ k₁)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hs', ha',
        romU64_spec rom p hL.rom_u64 n] <;>
      finish [Keep.size, Keep.pcap]

theorem internAllPinsPB_specW (n : Nat) (s₀ : St) (hs : pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_all_pins" []
    ⦃fun _ s' => LocEq s' s₀ ∧ internAllPinsW rom n s₀.mem = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hL.intern_all_pins, internAllPinsPB_subPB]
  simp only [callFn, internAllPinsPB]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hi' := fun s₁ q₁ h₁ => Triple.keep hL.no_st8 (romItems_specW rom p hL.toItemsProg n s₁ q₁ h₁)
    have hp' := fun s₁ q₁ h₁ => Triple.keep hL.no_st8 (internPinSets_specW rom p hL n s₁ q₁ h₁)
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, hi', hp',
        memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n] <;>
      finish [Keep.size, Keep.pcap, resetMem, rclearOK, mclearG, rsetSch]

end spec

end L.Rom
