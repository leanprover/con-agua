module

public import ConAgua.Rom.PinRead
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndCopy2
import all ConAgua.Rom.PinRead
import ConAgua.Arena.DeclRec

@[expose] public section

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
@[no_expose] def pbCheckG (bs d : List UInt8) : FunDecl := lfn () locals (i) {
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

theorem internAllPinsPB_subPB (bs : List UInt8) : internAllPinsPB.subPB bs = internAllPinsPB := by rfl

/-! ## The models -/

section models
variable (rom : List UInt8)

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
  erec_put : p.lookup "erec_put" = some erecPut

end models

theorem tierA_EREC_ne (a : Word) : tierA EREC (a >>> 40) ≠ CTL := by
  rw [tierA_EREC]; exact (ctl_ne_erTier a).symm
@[arena_grind =] theorem erecPutMem_top (m : Mem) (a v : Word) : (erecPutMem m a v).top = m.top :=
  top_set64_arr _ _ _ _ (tierA_EREC_ne a)
@[arena_grind =] theorem erecPutMem_pcap (m : Mem) (a v : Word) : pcap (erecPutMem m a v) = pcap m :=
  pcap_set64 _ _ _ _
@[arena_grind =] theorem erecPutMem_flag (m : Mem) (a v : Word) : (erecPutMem m a v).flag = m.flag :=
  Mem.flag_set64_ne _ _ _ _ (tierA_EREC_ne a)

/-- `erec_put`'s bound below the tier boundary (the generated models' guard). -/
theorem erecGuard_lo (m : Mem) (x : Word) (h : x.toNat < 2 ^ 40) (hx : x.toNat < (m.arr64 EREC).size) :
    (x &&& 1099511627775).toNat < (m.arr64 (tierA EREC (x >>> 40))).size := by
  have hb : x.toNat / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt h]
  have hm : x &&& 0xFFFFFFFFFF = x :=
    UInt64.toNat_inj.mp (by rw [L.Arena.tag_idx_toNat]; exact Nat.mod_eq_of_lt h)
  rw [tierA_EREC, ite_eq_left hb, hm]; exact hx

/-- The same over a memory after a put below the boundary. -/
theorem erecGuard_put (m : Mem) (x y v : Word) (hx : x.toNat < 2 ^ 40) (hy : y.toNat < 2 ^ 40)
    (hs : y.toNat < (m.arr64 EREC).size) :
    (y &&& 1099511627775).toNat < ((erecPutMem m x v).arr64 (tierA EREC (y >>> 40))).size := by
  rw [erecPutMem_lo m x v hx]
  exact erecGuard_lo _ y hy (by rw [Mem.size_arr64_set64]; exact hs)

theorem setEREC_topK (m : Mem) (i v : Word) : TopK m (erecPutMem m i v) :=
  TopK.of_eq (erecPutMem_top _ _ _) (erecPutMem_pcap _ _ _) (erecPutMem_flag _ _ _)

@[arena_grind =] theorem erAllocMem_top (m : Mem) (k : Word) : (erAllocMem m k).top = m.top := by
  unfold erAllocMem; split <;> exact top_set64_ne _ _ _ (by decide)
@[arena_grind =] theorem erAllocMem_pcap (m : Mem) (k : Word) : pcap (erAllocMem m k) = pcap m := by
  unfold erAllocMem; split <;> exact pcap_set64 _ _ _ _
theorem erAllocMem_flag (m : Mem) (k : Word) : (erAllocMem m k).flag = m.flag := by
  unfold erAllocMem; split <;> exact flag_set64_ctl _ _ _ (by decide)

theorem erAllocW_topK {m m' : Mem} {k o : Word} (h : erAllocW m k = some (o, m')) : TopK m m' := by
  rw [L.Arena.erAllocW_mem h]
  exact TopK.of_eq (erAllocMem_top _ _) (erAllocMem_pcap _ _) (erAllocMem_flag _ _)

theorem erAllocW_eqs {m m' : Mem} {k o : Word} (h : erAllocW m k = some (o, m')) :
    m'.top = m.top ∧ pcap m' = pcap m := by
  rw [L.Arena.erAllocW_mem h]
  exact ⟨erAllocMem_top _ _, erAllocMem_pcap _ _⟩
theorem erAllocW_top' (m m' : Mem) (k o : Word) (h : erAllocW m k = some (o, m')) : m'.top = m.top :=
  (erAllocW_eqs h).1
theorem erAllocW_pcap' (m m' : Mem) (k o : Word) (h : erAllocW m k = some (o, m')) : pcap m' = pcap m :=
  (erAllocW_eqs h).2
grind_pattern [arena_grind] erAllocW_top' => erAllocW m k, some (o, m')
grind_pattern [arena_grind] erAllocW_pcap' => erAllocW m k, some (o, m')

theorem resetMem_topK (m : Mem) : TopK m (resetMem m) := memFrame_top (resetMem_frame1 m) (by decide)

/-- **The model of `rom_exprs_to(q, o, k)`** (generated): the position after, the memory after. -/
l_model romExprsTo_specW (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
  fns [hL.rom_exprs_to ↦ romExprsToW]
  specs [(romExpr_specsW rom p hL.toExprProg n).1, erecPut_specW p hL.erec_put n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap]

theorem romExprsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem),
    romExprsToW rom n m q o k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q o k q' m' hW; simp [romExprsToW] at hW
  | succ n ih =>
    intro m q o k q' m' hW
    by_cases hk : k = 0
    · rw [romExprsToW.arm1 (hc1 := hk)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    rw [romExprsToW.arm2 (hc1 := hk)] at hW
    cases hP : romExprW rom n m q with
    | none => rw [hP, romExprsToW.k_rom_expr.none] at hW; cases hW
    | some r =>
      obtain ⟨h, q₁, m₁⟩ := r
      rw [hP] at hW
      unfold romExprsToW.k_rom_expr at hW
      split at hW
      · cases hW
      exact (((romExprW_topK rom n).1 m q h q₁ m₁ hP).trans (setEREC_topK _ _ _)).trans (ih _ _ _ _ _ _ hW)

theorem romExprsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem)
    (hW : romExprsToW rom n m q o k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romExprsToW_topK rom n m q o k q' m' hW hc ht).1
grind_pattern [arena_grind] romExprsToW_top' => romExprsToW rom n m q o k, some (q', m')

/-- **The model of `rom_pins_to(q, r, k)`** (generated): pins `k ‥ 7`, each at a fresh memo, to
`EREC[r + k ‥]`. -/
l_model romPinsTo_specW (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
  fns [hL.rom_pins_to ↦ romPinsToW]
  specs [romExprsTo_specW rom p hL n, memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap, resetMem, rclearOK, mclearG, rsetSch]

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ : Mem) (q q' o k r j l h : Word)

/-- `rom_pins_to`'s step, with the memo reset as `resetMem` (its guard `rclearOK`). -/
theorem romPinsToW_step (hk : k ≠ 8) (hc : rclearOK m) :
    romPinsToW rom (n + 1) m q r k =
      romPinsToW.k_rom_exprs_to rom n r k (romExprsToW rom n (resetMem m) q (r + k) 1) :=
  romPinsToW.arm2 rom n m q r k hk hc
theorem romPinsToW_clear (hk : k ≠ 8) (hc : ¬ rclearOK m) : romPinsToW rom (n + 1) m q r k = none :=
  romPinsToW.abort1 rom n m q r k hk (Decidable.not_not.mp hc)
end arms

theorem romPinsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q r k q' : Word) (m' : Mem),
    romPinsToW rom n m q r k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q r k q' m' hW; simp [romPinsToW] at hW
  | succ n ih =>
    intro m q r k q' m' hW
    by_cases hk : k = 8
    · rw [romPinsToW.arm1 (hc1 := hk)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    by_cases hc : rclearOK m
    case neg => rw [romPinsToW_clear rom n m q k r hk hc] at hW; cases hW
    rw [romPinsToW_step rom n m q k r hk hc] at hW
    cases hP : romExprsToW rom n (resetMem m) q (r + k) 1 with
    | none => rw [hP, romPinsToW.k_rom_exprs_to.none] at hW; cases hW
    | some x =>
      obtain ⟨q₁, m₁⟩ := x
      rw [hP, romPinsToW.k_rom_exprs_to.arm1] at hW
      exact ((resetMem_topK m).trans (romExprsToW_topK rom n _ _ _ _ _ _ hP)).trans (ih _ _ _ _ _ _ hW)

theorem romPinsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q r k q' : Word) (m' : Mem)
    (hW : romPinsToW rom n m q r k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romPinsToW_topK rom n m q r k q' m' hW hc ht).1
grind_pattern [arena_grind] romPinsToW_top' => romPinsToW rom n m q r k, some (q', m')

/-- **The model of `rom_lists_to(q, r, j)`** (generated): certificate lists `j ‥ 7`. -/
l_model romListsTo_specW (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
  fns [hL.rom_lists_to ↦ romListsToW]
  specs [romU64_spec rom p hL.rom_u64 n, erecAlloc_specW p hL.erec_alloc n, erecPut_specW p hL.erec_put n,
    memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n, romExprsTo_specW rom p hL n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap, resetMem, rclearOK, mclearG, rsetSch]
  guards ["rom_u64"]

/-- A certificate list's slice header written to the variant's record. -/
def listHdr (m : Mem) (r j o l : Word) : Mem :=
  erecPutMem (erecPutMem m (r + 8 + 2 * j) o) (r + 9 + 2 * j) l

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ : Mem) (q q' o k r j l h : Word)

theorem romListsToW_step (hj : j ≠ 8) (hb : u64OK rom q) :
    romListsToW rom (n + 1) m q r j =
      romListsToW.k_erec_alloc rom n q r j (u64W rom q) (erAllocW m (u64W rom q)) :=
  romListsToW.arm2 rom n m q r j hj (decide_eq_true hb)

/-- After the list's slice was allocated: the header (both words below the tier boundary and
inside `EREC`), the memo reset, the list. -/
theorem listsK_some (h8 : (r + 8 + 2 * j).toNat < 2 ^ 40) (h8s : (r + 8 + 2 * j).toNat < (m₁.arr64 EREC).size)
    (h9 : (r + 9 + 2 * j).toNat < 2 ^ 40) (h9s : (r + 9 + 2 * j).toNat < (m₁.arr64 EREC).size)
    (hc : rclearOK (listHdr m₁ r j o l)) :
    romListsToW.k_erec_alloc rom n q r j l (some (o, m₁)) =
      romListsToW.k_rom_exprs_to rom n r j (romExprsToW rom n (resetMem (listHdr m₁ r j o l)) (q + 8) o l) :=
  romListsToW.k_erec_alloc.arm1 rom n q r j l o m₁ (decide_eq_true (erecGuard_lo _ _ h8 h8s))
    (decide_eq_true (erecGuard_put _ _ _ _ h8 h9 h9s)) hc
theorem listsK_clear (h8 : (r + 8 + 2 * j).toNat < 2 ^ 40) (h8s : (r + 8 + 2 * j).toNat < (m₁.arr64 EREC).size)
    (h9 : (r + 9 + 2 * j).toNat < 2 ^ 40) (h9s : (r + 9 + 2 * j).toNat < (m₁.arr64 EREC).size)
    (hc : ¬ rclearOK (listHdr m₁ r j o l)) :
    romListsToW.k_erec_alloc rom n q r j l (some (o, m₁)) = none :=
  romListsToW.k_erec_alloc.abort3 rom n q r j l o m₁ (decide_eq_true (erecGuard_lo _ _ h8 h8s))
    (decide_eq_true (erecGuard_put _ _ _ _ h8 h9 h9s)) (Decidable.not_not.mp hc)
end arms

theorem romListsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q r j q' : Word) (m' : Mem),
    romListsToW rom n m q r j = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q r j q' m' hW; simp [romListsToW] at hW
  | succ n ih =>
    intro m q r j q' m' hW
    by_cases hj : j = 8
    · rw [romListsToW.arm1 (hc1 := hj)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    by_cases hb : u64OK rom q
    case neg => rw [romListsToW.abort1 (hc1 := hj) (hc2 := by simpa using hb)] at hW; cases hW
    rw [romListsToW_step rom n m q r j hj hb] at hW
    cases hA : erAllocW m (u64W rom q) with
    | none => rw [hA, romListsToW.k_erec_alloc.none] at hW; cases hW
    | some x =>
      obtain ⟨o, m₁⟩ := x
      rw [hA] at hW
      unfold romListsToW.k_erec_alloc at hW
      split at hW
      · cases hW
      split at hW
      · cases hW
      split at hW
      · cases hW
      change romListsToW.k_rom_exprs_to rom n r j
        (romExprsToW rom n (resetMem (listHdr m₁ r j o (u64W rom q))) (q + 8) o (u64W rom q)) = _ at hW
      cases hP : romExprsToW rom n (resetMem (listHdr m₁ r j o (u64W rom q))) (q + 8) o (u64W rom q) with
      | none => rw [hP, romListsToW.k_rom_exprs_to.none] at hW; cases hW
      | some y =>
        obtain ⟨q₁, m₂⟩ := y
        rw [hP, romListsToW.k_rom_exprs_to.arm1] at hW
        exact ((((erAllocW_topK hA).trans ((setEREC_topK _ _ _).trans (setEREC_topK _ _ _))).trans
          (resetMem_topK _)).trans (romExprsToW_topK rom n _ _ _ _ _ _ hP)).trans (ih _ _ _ _ _ _ hW)

theorem romListsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q r j q' : Word) (m' : Mem)
    (hW : romListsToW rom n m q r j = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romListsToW_topK rom n m q r j q' m' hW hc ht).1
grind_pattern [arena_grind] romListsToW_top' => romListsToW rom n m q r j, some (q', m')

/-- **The model of `rom_tpairs_to(q, o, k)`** (generated): `k` type pins, name and type. -/
l_model romTPairsTo_specW (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
  fns [hL.rom_tpairs_to ↦ romTPairsToW]
  specs [romName_specW rom p hL.toNameProg n, erecPut_specW p hL.erec_put n,
    memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n, romExprsTo_specW rom p hL n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap, resetMem, rclearOK, mclearG, rsetSch]

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ : Mem) (q q' o k r j l h : Word)

/-- After a type pin's name: its handle to `EREC[o]` (below the boundary, inside `EREC`), a memo
reset, the type to `EREC[o + 1]`. -/
theorem tpK_some (ho : o.toNat < 2 ^ 40) (hs : o.toNat < (m₁.arr64 EREC).size)
    (hc : rclearOK (erecPutMem m₁ o h)) :
    romTPairsToW.k_rom_name rom n o k (some (h, q', m₁)) =
      romTPairsToW.k_rom_exprs_to rom n o k (romExprsToW rom n (resetMem (erecPutMem m₁ o h)) q' (o + 1) 1) :=
  romTPairsToW.k_rom_name.arm1 rom n o k h q' m₁ (decide_eq_true (erecGuard_lo _ _ ho hs)) hc
theorem tpK_clear (ho : o.toNat < 2 ^ 40) (hs : o.toNat < (m₁.arr64 EREC).size)
    (hc : ¬ rclearOK (erecPutMem m₁ o h)) : romTPairsToW.k_rom_name rom n o k (some (h, q', m₁)) = none :=
  romTPairsToW.k_rom_name.abort2 rom n o k h q' m₁ (decide_eq_true (erecGuard_lo _ _ ho hs))
    (Decidable.not_not.mp hc)
end arms

theorem romTPairsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem),
    romTPairsToW rom n m q o k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q o k q' m' hW; simp [romTPairsToW] at hW
  | succ n ih =>
    intro m q o k q' m' hW
    by_cases hk : k = 0
    · rw [romTPairsToW.arm1 (hc1 := hk)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    rw [romTPairsToW.arm2 (hc1 := hk)] at hW
    cases hN : romNameW rom n m q with
    | none => rw [hN, romTPairsToW.k_rom_name.none] at hW; cases hW
    | some x =>
      obtain ⟨h, q₁, m₁⟩ := x
      rw [hN] at hW
      unfold romTPairsToW.k_rom_name at hW
      split at hW
      · cases hW
      split at hW
      · cases hW
      change romTPairsToW.k_rom_exprs_to rom n o k
        (romExprsToW rom n (resetMem (erecPutMem m₁ o h)) q₁ (o + 1) 1) = _ at hW
      cases hP : romExprsToW rom n (resetMem (erecPutMem m₁ o h)) q₁ (o + 1) 1 with
      | none => rw [hP, romTPairsToW.k_rom_exprs_to.none] at hW; cases hW
      | some y =>
        obtain ⟨q₂, m₂⟩ := y
        rw [hP, romTPairsToW.k_rom_exprs_to.arm1] at hW
        exact ((((romNameW_topK hN).trans (setEREC_topK _ _ _)).trans (resetMem_topK _)).trans
          (romExprsToW_topK rom n _ _ _ _ _ _ hP)).trans (ih _ _ _ _ _ _ hW)

theorem romTPairsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem)
    (hW : romTPairsToW rom n m q o k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romTPairsToW_topK rom n m q o k q' m' hW hc ht).1
grind_pattern [arena_grind] romTPairsToW_top' => romTPairsToW rom n m q o k, some (q', m')

/-- **The model of `rom_tpins_to(q, r, j)`** (generated): type-pin lists `j ‥ 7`. -/
l_model romTPinsTo_specW (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
  fns [hL.rom_tpins_to ↦ romTPinsToW]
  specs [romU64_spec rom p hL.rom_u64 n, erecAlloc_specW p hL.erec_alloc n, erecPut_specW p hL.erec_put n,
    romTPairsTo_specW rom p hL n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap]
  guards ["rom_u64"]

/-- A type-pin list's slice header written to the variant's record. -/
def tpinsHdr (m : Mem) (r j o l : Word) : Mem :=
  erecPutMem (erecPutMem m (r + 24 + 2 * j) o) (r + 25 + 2 * j) l

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ : Mem) (q q' o k r j l h : Word)

theorem romTPinsToW_step (hj : j ≠ 8) (hb : u64OK rom q) (hl : ¬ 4294967296 ≤ u64W rom q) :
    romTPinsToW rom (n + 1) m q r j =
      romTPinsToW.k_erec_alloc rom n q r j (u64W rom q) (erAllocW m (2 * u64W rom q)) :=
  romTPinsToW.arm2 rom n m q r j hj (decide_eq_true hb) hl

/-- After the list's slice was allocated: the header (below the boundary, inside `EREC`), the
pairs. -/
theorem tpinsK_some (h8 : (r + 24 + 2 * j).toNat < 2 ^ 40) (h8s : (r + 24 + 2 * j).toNat < (m₁.arr64 EREC).size)
    (h9 : (r + 25 + 2 * j).toNat < 2 ^ 40) (h9s : (r + 25 + 2 * j).toNat < (m₁.arr64 EREC).size) :
    romTPinsToW.k_erec_alloc rom n q r j l (some (o, m₁)) =
      romTPinsToW.k_rom_tpairs_to rom n r j (romTPairsToW rom n (tpinsHdr m₁ r j o l) (q + 8) o l) :=
  romTPinsToW.k_erec_alloc.arm1 rom n q r j l o m₁ (decide_eq_true (erecGuard_lo _ _ h8 h8s))
    (decide_eq_true (erecGuard_put _ _ _ _ h8 h9 h9s))
end arms

theorem romTPinsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q r j q' : Word) (m' : Mem),
    romTPinsToW rom n m q r j = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q r j q' m' hW; simp [romTPinsToW] at hW
  | succ n ih =>
    intro m q r j q' m' hW
    by_cases hj : j = 8
    · rw [romTPinsToW.arm1 (hc1 := hj)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    by_cases hb : u64OK rom q
    case neg => rw [romTPinsToW.abort1 (hc1 := hj) (hc2 := by simpa using hb)] at hW; cases hW
    by_cases hl : 4294967296 ≤ u64W rom q
    · rw [romTPinsToW.abort2 (hc1 := hj) (hc2 := decide_eq_true hb) (hc3 := hl)] at hW; cases hW
    rw [romTPinsToW_step rom n m q r j hj hb hl] at hW
    cases hA : erAllocW m (2 * u64W rom q) with
    | none => rw [hA, romTPinsToW.k_erec_alloc.none] at hW; cases hW
    | some x =>
      obtain ⟨o, m₁⟩ := x
      rw [hA] at hW
      unfold romTPinsToW.k_erec_alloc at hW
      split at hW
      · cases hW
      split at hW
      · cases hW
      change romTPinsToW.k_rom_tpairs_to rom n r j
        (romTPairsToW rom n (tpinsHdr m₁ r j o (u64W rom q)) (q + 8) o (u64W rom q)) = _ at hW
      cases hP : romTPairsToW rom n (tpinsHdr m₁ r j o (u64W rom q)) (q + 8) o (u64W rom q) with
      | none => rw [hP, romTPinsToW.k_rom_tpairs_to.none] at hW; cases hW
      | some y =>
        obtain ⟨q₁, m₂⟩ := y
        rw [hP, romTPinsToW.k_rom_tpairs_to.arm1] at hW
        exact (((erAllocW_topK hA).trans ((setEREC_topK _ _ _).trans (setEREC_topK _ _ _))).trans
          (romTPairsToW_topK rom n _ _ _ _ _ _ hP)).trans (ih _ _ _ _ _ _ hW)

theorem romTPinsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q r j q' : Word) (m' : Mem)
    (hW : romTPinsToW rom n m q r j = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romTPinsToW_topK rom n m q r j q' m' hW hc ht).1
grind_pattern [arena_grind] romTPinsToW_top' => romTPinsToW rom n m q r j, some (q', m')

/-- **The model of `rom_sets_to(q, o, k)`** (generated): `k` variants. -/
l_model romSetsTo_specW (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
  fns [hL.rom_sets_to ↦ romSetsToW]
  specs [erecAlloc_specW p hL.erec_alloc n, romPinsTo_specW rom p hL n, romListsTo_specW rom p hL n,
    romTPinsTo_specW rom p hL n, erecPut_specW p hL.erec_put n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap]

section arms
variable (rom : List UInt8) (n : Nat) (m m₁ : Mem) (q q' o k r : Word)

/-- After a variant's type pins: the record's pointer to `EREC[o]` (below the boundary, inside
`EREC`), then the next variant. -/
theorem sets4K_some (ho : o.toNat < 2 ^ 40) (hs : o.toNat < (m₁.arr64 EREC).size) :
    romSetsToW.k_rom_tpins_to rom n o k r (some (q', m₁)) =
      romSetsToW rom n (erecPutMem m₁ o r) q' (o + 1) (k - 1) :=
  romSetsToW.k_rom_tpins_to.arm1 rom n o k r q' m₁ (decide_eq_true (erecGuard_lo _ _ ho hs))
end arms

theorem romSetsToW_topK (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem),
    romSetsToW rom n m q o k = some (q', m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m q o k q' m' hW; simp [romSetsToW] at hW
  | succ n ih =>
    intro m q o k q' m' hW
    by_cases hk : k = 0
    · rw [romSetsToW.arm1 (hc1 := hk)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨-, rfl⟩ := hW; exact TopK.refl _
    rw [romSetsToW.arm2 (hc1 := hk)] at hW
    cases hA : erAllocW m 40 with
    | none => rw [hA, romSetsToW.k_erec_alloc.none] at hW; cases hW
    | some x =>
      obtain ⟨r, m₁⟩ := x
      rw [hA, romSetsToW.k_erec_alloc.arm1] at hW
      cases hP : romPinsToW rom n m₁ q r 0 with
      | none => rw [hP, romSetsToW.k_rom_pins_to.none] at hW; cases hW
      | some y =>
        obtain ⟨q₁, m₂⟩ := y
        rw [hP, romSetsToW.k_rom_pins_to.arm1] at hW
        cases hQ : romListsToW rom n m₂ q₁ r 0 with
        | none => rw [hQ, romSetsToW.k_rom_lists_to.none] at hW; cases hW
        | some z =>
          obtain ⟨q₂, m₃⟩ := z
          rw [hQ, romSetsToW.k_rom_lists_to.arm1] at hW
          cases hT : romTPinsToW rom n m₃ q₂ r 0 with
          | none => rw [hT, romSetsToW.k_rom_tpins_to.none] at hW; cases hW
          | some w =>
            obtain ⟨q₃, m₄⟩ := w
            rw [hT] at hW
            unfold romSetsToW.k_rom_tpins_to at hW
            split at hW
            · cases hW
            exact (((((erAllocW_topK hA).trans (romPinsToW_topK rom n _ _ _ _ _ _ hP)).trans
              (romListsToW_topK rom n _ _ _ _ _ _ hQ)).trans (romTPinsToW_topK rom n _ _ _ _ _ _ hT)).trans
              (setEREC_topK _ _ _)).trans (ih _ _ _ _ _ _ hW)

theorem romSetsToW_top' (rom : List UInt8) (n : Nat) (m : Mem) (q o k q' : Word) (m' : Mem)
    (hW : romSetsToW rom n m q o k = some (q', m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romSetsToW_topK rom n m q o k q' m' hW hc ht).1
grind_pattern [arena_grind] romSetsToW_top' => romSetsToW rom n m q o k, some (q', m')

/-- **The model of `intern_pin_sets(q)`** (generated). -/
l_model internPinSets_specW (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
  fns [hL.intern_pin_sets ↦ internPinSetsW]
  specs [romU64_spec rom p hL.rom_u64 n, erecAlloc_specW p hL.erec_alloc n, romSetsTo_specW rom p hL n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap]
  guards ["rom_u64"]

theorem internPinSetsW_eq (rom : List UInt8) (n : Nat) (m : Mem) (q : Word) (hb : u64OK rom q) :
    internPinSetsW rom (n + 1) m q =
      internPinSetsW.k_erec_alloc rom n q (u64W rom q) (erAllocW m (u64W rom q)) :=
  internPinSetsW.arm1 rom n m q (decide_eq_true hb)

section models
variable (rom : List UInt8)

/-- **The model of `rom_pin_sets()`**: `[IW offset, count]`. -/
def romPinSetsW : Nat → Mem → Option (List Word × Mem)
  | 0, _ => none
  | n + 1, m => erToIwW n m (rdW (m.arr64 CTL) 150) (rdW (m.arr64 CTL) 151)

theorem romPinSetsW_eq (n : Nat) (m : Mem) :
    romPinSetsW (n + 1) m = erToIwW n m (rdW (m.arr64 CTL) 150) (rdW (m.arr64 CTL) 151) := rfl
attribute [arena_grind =] romPinSetsW_eq

end models

/-- **The model of `intern_all_pins()`** (ROM version, generated): the memory after. -/
l_model internAllPinsPB_specW (rom : List UInt8) (p : Prog) (hL : PinProg rom p)
  fns [(show p.lookup "intern_all_pins" = some internAllPinsPB from
    internAllPinsPB_subPB rom ▸ hL.intern_all_pins) ↦ internAllPinsW void]
  specs [memoClearG_spec rsetSch p "rset_clear" hL.rset_clear n, romItems_specW rom p hL.toItemsProg n,
    internPinSets_specW rom p hL n]
  pre [pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41]
  keep [hL.no_st8]
  grind [arena_grind] finish [Keep.size, L.Front.Keep.pcap, resetMem, rclearOK, mclearG, rsetSch]

theorem internAllPinsW_eq (rom : List UInt8) (n : Nat) (m : Mem) (hc : rclearOK m) :
    internAllPinsW rom (n + 1) m = internAllPinsW.k_rom_items rom n (romItemsW rom n (resetMem m) allPinsOff) :=
  internAllPinsW.arm1 rom n m hc

end L.Rom
