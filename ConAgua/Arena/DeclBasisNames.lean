module

public import ConAgua.Arena.QuotRecW
public import ConAgua.Arena.DeclBasisRef
public import ConAgua.Arena.BasisBlockT
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.L.WordOff
import ConAgua.Arena.DeclAndPinIndCopy2
import ConAgua.Arena.StageC
import ConAgua.Arena.ErToIwBlk
import ConRon.Bridge.Checker.Basis
import all ConAgua.Arena.BasisL

@[expose] public section

/-!
# The reserved names' check (`basis_names_ok`, `basis_names_error`) refines the twin's

con-ron #493's `basisNamesOk`/`basisNamesError` (`Basis.lean`): a block under a pinned block's
names compared with its pin (`basis_name_hit`, `rom_basis_decls`, `er_to_iw`, `pin_list_ok`),
any other block's members unreserved (`block_names_unreserved`), a one-constant declaration's
name unreserved (`basis_name_unreserved`) but for `Quot.sound` and the quotient records.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `reserved_contains` -/

theorem resFromW_hit (n : Nat) : ∀ (m : Mem) (x j : Word) (b : Word), j.toNat ≤ 16 →
    resFromW n m x j = some b → b ≠ 0 → ∃ i, j.toNat ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x := by
  induction n with
  | zero => intro m x j b _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j b hj h hb
    rw [resFromW_step] at h
    by_cases h16 : 16 ≤ j
    · rw [ite_eq_left h16] at h; simp at h; exact absurd h.symm hb
    rw [ite_eq_right h16] at h
    have hj16 : j.toNat < 16 := by rw [UInt64.le_iff_toNat_le] at h16; simp at h16; omega
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · refine ⟨j.toNat, Nat.le_refl _, hj16, ?_⟩
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he
    rw [ite_eq_right he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨i, hi1, hi2, hi3⟩ := ih m x (j + 1) b (by omega) h hb
    exact ⟨i, by omega, hi2, hi3⟩

theorem resFromW_01 (n : Nat) : ∀ (m : Mem) (x j : Word) (b : Word), resFromW n m x j = some b →
    b = 0 ∨ b = 1 := by
  induction n with
  | zero => intro m x j b h; simp [resFromW] at h
  | succ n ih =>
    intro m x j b h
    rw [resFromW_step] at h
    split at h
    · simp at h; exact Or.inl h.symm
    split at h
    · simp at h; exact Or.inr h.symm
    exact ih _ _ _ _ h

/-- **`reserved_contains` is the twin's `reservedBasisNames.contains`**, as a word. -/
theorem resContW_res {m : Mem} {a : AState} {n : Nat} {x b : Word} (hx : x.toNat < 2 ^ 32)
    (h : resContW n m x = some b) (hP : PinsR m a.pins) :
    ∃ R, reservedBasisNames.run a = .ok (R, a) ∧ b = if R.contains (decI x) then 1 else 0 := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at h; simp at h
  rw [ite_eq_right h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  rcases resFromW_01 n m x 0 b h with rfl | rfl
  · have hm := resFromW_miss n m x 0 (by simp) h
    have : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, e⟩ := hc
      exact hm i (Nat.zero_le _) hi ((decI_eq_iff _ (hF.reserved_lt i hi) _).mp e ▸ decI_word_self x hx)
    rw [this]; rfl
  · obtain ⟨i, -, hi, he⟩ := resFromW_hit n m x 0 1 (by simp) h (by decide)
    have : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = true := by
      simp only [List.contains_iff_mem, List.mem_map, List.mem_range]
      exact ⟨i, hi, by rw [he]⟩
    rw [this]; rfl


/-! ## `basis_name_unreserved` -/

theorem bnuW_ok {m m' : Mem} {a : AState} {n : Nat} {x : Word} {r : List Word}
    (hx : x.toNat < 2 ^ 32) (hP : PinsR m a.pins) (h : basisNameUnreservedW n m x = some (r, m')) :
    m' = m ∧ ∃ b, (ConRon.Arena.basisNameUnreserved (decI x)).run a = .ok (b, a) ∧ (r.headD 0 ≠ 0 ↔ b = true) := by
  cases n with
  | zero => simp [basisNameUnreservedW] at h
  | succ n =>
  simp only [basisNameUnreservedW] at h
  rcases hc : resContW n m x with _ | c <;> rw [hc] at h
  · simp [basisNameUnreservedW.k_reserved_contains] at h
  simp only [basisNameUnreservedW.k_reserved_contains, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨R, hR, hb⟩ := resContW_res hx hc hP
  refine ⟨rfl, !R.contains (decI x), ?_, ?_⟩
  · simp only [ConRon.Arena.basisNameUnreserved, StateT.run_bind, hR, except_ok_bind]; rfl
  · rw [hb]; cases R.contains (decI x) <;> simp

/-! ## The models -/

/-- **The model of `basis_names_ok(k, n, bo, bl)`**. -/
l_model basisNamesOk_specW (p : Prog) (hp : p.lookup "basis_names_ok" = some L.Ind.basisNamesOk)
  fns [hp ↦ basisNamesOkW list]
  specs [callW_spec p n "basis_name_hit", callW_spec p n "rom_basis_decls", callW_spec p n "er_to_iw",
    callW_spec p n "pin_list_ok", callW_spec p n "block_names_unreserved", callW_spec p n "pin_at",
    callW_spec p n "basis_name_unreserved"]
  grind [arena_grind]

/-- **The model of `basis_names_error(k, bo, bl)`**. -/
l_model basisNamesError_specW (p : Prog) (hp : p.lookup "basis_names_error" = some L.Ind.basisNamesError)
  fns [hp ↦ basisNamesErrorW list]
  specs [callW_spec p n "basis_name_hit"]
  grind [arena_grind]

/-! ## `block_names_unreserved` -/

/-- **`block_names_unreserved(bo, bl)` is the twin's `block.all fun c => !rs.contains c.name`**
at the reserved names `R` (`reservedBasisNames`), for a block at the `EREC` slice `(bo, bl)`. -/
theorem bluW_ok {m : Mem} {a : AState} {R : List NIdx} (hP : PinsR m a.pins)
    (hR : reservedBasisNames.run a = .ok (R, a)) :
    ∀ (n : Nat) (bo bl : Word) (block : List IConstantInfo) (r : List Word) (m' : Mem),
    L.Front.decCIsR (erecP m) bo.toNat bl.toNat = some block → bo.toNat + bl.toNat < 2 ^ 64 →
    blockNamesUnreservedW n m bo bl = some (r, m') →
    m' = m ∧ (r.headD 0 ≠ 0 ↔ (block.all fun c => !R.contains c.name) = true) := by
  intro n
  induction n with
  | zero => intro bo bl block r m' _ _ h; simp [blockNamesUnreservedW.eq_1] at h
  | succ n ih =>
  intro bo bl block r m' hd hb h
  by_cases h0 : bl = 0
  · rw [blockNamesUnreservedW.arm1 n m bo bl h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst h0
    simp only [L.Front.decCIsR, UInt64.toNat_zero, List.range_zero, List.mapM_nil, Option.pure_def,
      Option.some.injEq] at hd
    subst hd
    simp
  rw [blockNamesUnreservedW.eq_2, ite_eq_right h0] at h
  have hbl0 : bl.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
  obtain ⟨l, hl⟩ : ∃ l, bl.toNat = l + 1 := ⟨bl.toNat - 1, by omega⟩
  rw [hl, decCIsR_succ] at hd
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hd
  obtain ⟨c, ⟨v, hv, hc⟩, cs, hcs, rfl⟩ := hd
  obtain ⟨w, hw, rfl⟩ : ∃ w, erecP m bo.toNat = some w ∧ w.toNat = v := by
    simp only [nat?, Option.map_eq_some_iff] at hv; exact hv
  have hcv := decCI_cvA (q := w) hc
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hcv
  have hq1 : (w + 1).toNat = w.toNat + 1 := L.toNat_add_ofNat_of_lt w 1 (erecP_lt64 hwn)
  have e1 : rdW (m.arr64 (tierA EREC (bo >>> 40))) (bo &&& 1099511627775) = w := by
    rw [erRd_congr (m := m) (m' := m) rfl rfl]; exact erRd_of _ _ hw
  have e2 : rdW (m.arr64 (tierA EREC ((w + 1) >>> 40))) ((w + 1) &&& 1099511627775) = wn := by
    rw [erRd_congr (m := m) (m' := m) rfl rfl]; exact erRd_of _ _ (by rw [hq1]; exact hwn)
  rw [e1, e2] at h
  have hcn : c.name = decI wn := by
    rw [← hname]; cases c <;> rfl
  rcases hc3 : resContW n m wn with _ | cw
  · rw [hc3, blockNamesUnreservedW.k_reserved_contains.none] at h; cases h
  rw [hc3] at h
  obtain ⟨R', hR', hcw⟩ := resContW_res hwnl hc3 hP
  have hRR : R' = R := by
    rw [hR] at hR'; exact (Prod.mk.inj (Except.ok.inj hR')).1.symm
  subst hRR
  by_cases hk : cw ≠ 0
  · rw [blockNamesUnreservedW.k_reserved_contains.arm1 n bo bl m cw hk] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hin : R'.contains (decI wn) = true := by
      cases hcc : R'.contains (decI wn)
      · rw [hcc] at hcw; exact absurd (by simpa using hcw) hk
      · rfl
    refine ⟨rfl, ?_⟩
    simp only [List.all_cons, hcn, hin, Bool.not_true, Bool.false_and, List.headD_cons]
    simp
  have hk' : cw = 0 := by simpa using hk
  rw [blockNamesUnreservedW.k_reserved_contains.arm2 n bo bl m cw hk'] at h
  have hout : R'.contains (decI wn) = false := by
    cases hcc : R'.contains (decI wn)
    · rfl
    · rw [hcc, hk'] at hcw; simp at hcw
  rcases h2 : blockNamesUnreservedW n m (bo + 1) (bl - 1) with _ | ⟨r2, m2⟩
  · rw [h2, blockNamesUnreservedW.k_block_names_unreserved.eq_1] at h; cases h
  rw [h2, blockNamesUnreservedW.k_block_names_unreserved.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hb1 : (bo + 1).toNat = bo.toNat + 1 := L.toNat_add_ofNat_of_lt bo 1 (by omega)
  have hl1 : (bl - 1).toNat = l := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  obtain ⟨rfl, hi⟩ := ih (bo + 1) (bl - 1) cs r2 m2 (by rw [hb1, hl1]; exact hcs)
    (by rw [hb1, hl1]; omega) h2
  refine ⟨rfl, ?_⟩
  simp only [List.headD_cons, List.all_cons, hcn, hout, Bool.not_false, Bool.true_and]
  exact hi

/-! ## The program facts -/

/-- **The program `basis_names_ok`/`basis_names_error` run in**: their lookups and their callees'
(`reserved_contains`, `pin_at`, `er_to_iw`), the entry points' refinements (`BasisRefs`: the name
test), the ROM's (`RomRefs`: the pinned blocks), the comparison's (`PinListOkRef`), the leaves'
write set (`rom_basis_decls` is a leaf). -/
structure BnoProg (p : Prog) : Prop where
  bno : p.lookup "basis_names_ok" = some L.Ind.basisNamesOk
  bne : p.lookup "basis_names_error" = some L.Ind.basisNamesError
  bnu : p.lookup "basis_name_unreserved" = some L.Ind.basisNameUnreserved
  blu : p.lookup "block_names_unreserved" = some L.Ind.blockNamesUnreserved
  rf : p.lookup "reserved_from" = some reservedFrom
  rc : p.lookup "reserved_contains" = some reservedContains
  pa : p.lookup "pin_at" = some pinAtL
  ia : p.lookup "iw_alloc" = some iwAlloc
  ec : p.lookup "er_copy" = some erCopy
  eti : p.lookup "er_to_iw" = some erToIw
  basis : BasisRefs p
  rom : L.Rom.RomRefs p
  pl : PinListOkRef p
  leaf : LeafClosed p

/-- A name word: a handle below `2 ^ 32` decoding to the constant value's name. -/
def NameW (w : Word) (cv : IConstantVal) : Prop := w.toNat < 2 ^ 32 ∧ decI w = cv.name

/-- **`basis_names_ok`'s arguments for the declaration `d`**: the front's kind word `k`
(`1` axiom, `2` definition, `3` theorem, `4` opaque, `5` quotient, `6` inductive block), a
one-constant declaration's name word `nw`, an inductive block's `EREC` slice `(bo, bl)`. -/
def BnoArgs (d : IDeclaration) (k nw bo bl : Word) (m : Mem) : Prop :=
  match d with
  | .indDecl block _ => k = 6 ∧ BlockAt bo bl block m
  | .axiomDecl cv => k = 1 ∧ NameW nw cv
  | .defnDecl cv _ _ => k = 2 ∧ NameW nw cv
  | .thmDecl cv _ => k = 3 ∧ NameW nw cv
  | .opaqueDecl cv _ => k = 4 ∧ NameW nw cv
  | .quotDecl _ _ => k = 5

section bno
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- A one-constant declaration's unreserved-name test (`basis_name_unreserved`). -/
theorem bnu_sim (hP : BnoProg p) {n : Nat} {m : Mem} {a : AState} {nw : Word} {cv : IConstantVal}
    (hT : StageT dn vis fe m a) (hw : NameW nw cv) :
    Sim (callW p n "basis_name_unreserved" [nw] m) (ConRon.Arena.basisNameUnreserved cv.name) a
      (fun r b m' a' => m' = m ∧ a' = a ∧ (r.headD 0 ≠ 0 ↔ b = true)) := by
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (basisNameUnreserved_specW p hP.rf hP.rc hP.bnu n _ nw) h
  obtain ⟨hm, b, hrun, hb⟩ := bnuW_ok hw.1 hT.stage.check.pins hW
  rw [← hw.2]
  exact ⟨b, a, hrun, hm, rfl, hb⟩

/-- **`basis_names_ok(k, nw, bo, bl)` refines `basisNamesOk d`** under `StageT`, a well-formed
twin state (`StateOK`, `ReadOK`, `PinsOK`) and the declaration's words (`BnoArgs`): an inductive
block's name test (`basis_name_hit`), a pinned block's comparison (`rom_basis_decls`, `er_to_iw`,
`pin_list_ok`) or the members' names (`block_names_unreserved`); `Quot.sound` (pin slot `4`) and
the quotient records pass; every other declaration's name (`basis_name_unreserved`). The twin's
step is con-ron's `RStep` (`basisNamesOk_run`). -/
theorem bno_sim (hP : BnoProg p) {n : Nat} {m : Mem} {a : AState} {d : IDeclaration}
    {k nw bo bl : Word} (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a)
    (hr : ConRon.Bridge.ReadOK a) (hpo : ConRon.Bridge.PinsOK a) (hA : BnoArgs d k nw bo bl m)
    (hden : ∃ x, Frontend.denoteDecl a.store d = some x) :
    Sim (callW p n "basis_names_ok" [k, nw, bo, bl] m) (ConRon.Arena.basisNamesOk d) a
      (fun r b m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ ConRon.Bridge.RStep a a' ∧
        (r.headD 0 ≠ 0 ↔ b = true)) := by
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (basisNamesOk_specW p hP.bno n _ k nw bo bl) h
  generalize s'.mem = m' at hW ⊢
  suffices H : ∃ b a', (ConRon.Arena.basisNamesOk d).run a = .ok (b, a') ∧
      StageT dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 ≠ 0 ↔ b = true) by
    obtain ⟨b, a', hrun, hT', hg', hb⟩ := H
    obtain ⟨x, hx⟩ := hden
    exact ⟨b, a', hrun, hT', hg', (ConRon.Bridge.basisNamesOk_run hok hr hpo hx hrun).1, hb⟩
  cases n with
  | zero => simp [basisNamesOkW] at hW
  | succ n =>
  -- the one-constant arms but the axiom's: the name test
  have one : ∀ {cv : IConstantVal}, NameW nw cv → k ≠ 6 → k ≠ 1 → k ≠ 5 →
      ∃ b a', (ConRon.Arena.basisNameUnreserved cv.name).run a = .ok (b, a') ∧
        StageT dn vis fe m' a' ∧ IWGrow m m' ∧ (r.headD 0 ≠ 0 ↔ b = true) := by
    intro cv hw h6 h1 h5
    rw [basisNamesOkW.arm4 p n m k nw bo bl h6 h1 h5] at hW
    rcases c1 : callW p n "basis_name_unreserved" [nw] m with _ | ⟨r1, m1⟩
    · rw [c1] at hW; simp [basisNamesOkW.k_pin_list_ok] at hW
    rw [c1, basisNamesOkW.k_pin_list_ok.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨b, a1, hrun, hm1, ha1, hb⟩ := bnu_sim hP hT hw r1 m1 c1
    rw [ha1] at hrun
    subst hm1
    exact ⟨b, a, hrun, hT, IWGrow.refl _, by simpa using hb⟩
  cases d with
  | defnDecl cv v hh =>
    obtain ⟨rfl, hw⟩ := hA
    exact one hw (by decide) (by decide) (by decide)
  | thmDecl cv v =>
    obtain ⟨rfl, hw⟩ := hA
    exact one hw (by decide) (by decide) (by decide)
  | opaqueDecl cv v =>
    obtain ⟨rfl, hw⟩ := hA
    exact one hw (by decide) (by decide) (by decide)
  | quotDecl qk cv =>
    obtain rfl := hA
    rw [basisNamesOkW.arm3 p n m 5 nw bo bl (by decide) (by decide) rfl] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨true, a, rfl, hT, IWGrow.refl _, by simp⟩
  | axiomDecl cv =>
    obtain ⟨rfl, hw⟩ := hA
    rw [basisNamesOkW.arm2 p n m 1 nw bo bl (by decide) rfl] at hW
    rcases c1 : callW p n "pin_at" [4] m with _ | ⟨r1, m1⟩
    · rw [c1] at hW; simp [basisNamesOkW.k_pin_at] at hW
    rw [c1] at hW
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (pinAt_specW p hP.pa n _ 4) c1
    obtain ⟨hm1, hr1, hl1, hrun1⟩ := pinAtW_ok hW1 hT.stage.check.pins
    try simp only at hm1
    subst hm1
    have ep : r1.headD 0 = pinW s1.mem (1 + (4 : Word).toNat) := by rw [hr1]; rfl
    have hpq : pinQuotSound.run a = .ok (decI (pinW s1.mem (1 + (4 : Word).toNat)), a) := by
      simpa [pinQuotSound, show PIN_QUOT_SOUND = (4 : Word).toNat from rfl] using hrun1
    have hb2 := decI_beq (k := .name) nw _ hw.1 hl1
    have htw : (ConRon.Arena.basisNamesOk (.axiomDecl cv)).run a =
        (if decide (nw = pinW s1.mem (1 + (4 : Word).toNat)) = true then pure true
          else ConRon.Arena.basisNameUnreserved cv.name : AM Bool).run a := by
      simp only [ConRon.Arena.basisNamesOk, StateT.run_bind, hpq, except_ok_bind, ← hw.2, hb2]
    by_cases eq : nw = r1.headD 0
    · rw [basisNamesOkW.k_pin_at.arm1 p n nw r1 s1.mem eq] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      rw [ep] at eq
      refine ⟨true, a, ?_, hT, IWGrow.refl _, by simp⟩
      rw [htw, ite_eq_left (by simpa using eq)]; rfl
    rw [basisNamesOkW.k_pin_at.arm2 p n nw r1 s1.mem eq] at hW
    rw [ep] at eq
    rcases c2 : callW p n "basis_name_unreserved" [nw] s1.mem with _ | ⟨r2, m2⟩
    · rw [c2] at hW; simp [basisNamesOkW.k_pin_list_ok] at hW
    rw [c2, basisNamesOkW.k_pin_list_ok.arm1] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨b, a2, hrun, hm2, ha2, hb⟩ := bnu_sim hP hT hw r2 m2 c2
    rw [ha2] at hrun
    subst hm2
    refine ⟨b, a, ?_, hT, IWGrow.refl _, by simpa using hb⟩
    rw [htw, ite_eq_right (by simpa using eq)]; exact hrun
  | indDecl block nP =>
    obtain ⟨rfl, hBA⟩ := hA
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨bP, hbP, -⟩ := hx
    rw [basisNamesOkW.arm1 p n m 6 nw bo bl rfl] at hW
    -- `basis_name_hit`
    rcases c1 : callW p n "basis_name_hit" [bo, bl] m with _ | ⟨r1, m1⟩
    · rw [c1] at hW; simp [basisNamesOkW.k_basis_name_hit] at hW
    rw [c1] at hW
    obtain ⟨hit, a1, hrun1, hT1, hg1, hd1⟩ :=
      (hP.basis.nameHit dn vis fe) bo bl block n m a r1 m1 ⟨hT, hok, hr, hBA, _, hbP⟩ c1
    obtain ⟨hok1, hx1, hp1, hc1, -, hsc1, -⟩ := ConRon.Bridge.basisNameHit_run hok hbP hrun1
    have hR1 : ConRon.Bridge.RStep a a1 :=
      ConRon.Bridge.RStep.of_frame hok1 hx1 hsc1 hp1 hc1 hr
    have hbP1 := ConRon.Bridge.denoteCIList_mono hx1 _ _ hbP
    cases hit with
    | none =>
      -- the members' names
      have h0 : r1.headD 0 = 0 := hd1
      rw [basisNamesOkW.k_basis_name_hit.arm2 p n bo bl r1 m1 h0] at hW
      rcases c2 : callW p n "block_names_unreserved" [bo, bl] m1 with _ | ⟨r2, m2⟩
      · rw [c2] at hW; simp [basisNamesOkW.k_pin_list_ok] at hW
      rw [c2, basisNamesOkW.k_pin_list_ok.arm1] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
        (blockNamesUnreserved_specW p hP.rf hP.rc hP.blu n _ bo bl) c2
      have hR : reservedBasisNames.run a1 =
          .ok ((List.range 16).map fun i => (decI (pinW m1 (55 + i)) : NIdx), a1) :=
        pinReserved_run (hT1.stage.check.pins.full hT1.flag)
      obtain ⟨hm2, hb2⟩ := bluW_ok hT1.stage.check.pins hR n bo bl block _ _
        (decCIsR_ext hg1.erecGrow.ext hBA.1) hBA.2 hW2
      try simp only at hm2
      rw [hm2]
      refine ⟨_, a1, ?_, hT1, hg1, by simpa only [List.headD_cons] using hb2⟩
      simp only [ConRon.Arena.basisNamesOk, StateT.run_bind, hrun1, except_ok_bind, hR]
      rfl
    | some kind =>
      obtain ⟨h1, hk4, hkind⟩ := hd1
      rw [basisNamesOkW.k_basis_name_hit.arm1 p n bo bl r1 m1 (by rw [h1]; decide)] at hW
      -- `rom_basis_decls`
      rcases c2 : callW p n "rom_basis_decls" [r1.tail.headD 0] m1 with _ | ⟨r2, m2⟩
      · rw [c2] at hW; simp [basisNamesOkW.k_rom_basis_decls] at hW
      rw [c2] at hW
      simp only [basisNamesOkW.k_rom_basis_decls] at hW
      obtain ⟨pins, a2, hrun2, hS2, hg2, hpd2⟩ :=
        hP.rom.basis dn vis fe _ hk4 n m1 a1 r2 m2 hT1.stage c2
      rw [hkind] at hrun2
      obtain ⟨hs2, hP2⟩ := ConRon.Bridge.BasisKind.decls_run hok1 hrun2
      have hf2 : MemFrame leafA leafC m1 m2 :=
        (run_memFrame hP.leaf (leaf_mem _ rfl) (run_of_callW c2)).1
      have hT2 := hT1.of_leafI hS2 hs2 hf2
      have hR2 : ConRon.Bridge.RStep a1 a2 := ConRon.Bridge.RStep.of_istep hs2 hR1.read
      have hbP2 := ConRon.Bridge.denoteCIList_mono hR2.ext _ _ hbP1
      -- `er_to_iw`
      rcases c3 : callW p n "er_to_iw" [bo, bl] m2 with _ | ⟨r3, m3⟩
      · rw [c3] at hW; simp [basisNamesOkW.k_er_to_iw] at hW
      rw [c3] at hW
      simp only [basisNamesOkW.k_er_to_iw] at hW
      obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
        (erToIw_specW p hP.ia hP.ec hP.eti n _ bo bl) c3
      simp only at hs3 hW3
      subst hs3
      obtain ⟨hS3, hg3, hf3, hr3, hsl3⟩ := erToIwW_blkR hW3 hT2.stage
        (decCIsR_ext (hg1.trans hg2).erecGrow.ext hBA.1)
      have hT3 := StageT.of_iw hT2 hS3 hf3
      -- `pin_list_ok`
      rcases c4 : callW p n "pin_list_ok" [r3.headD 0, r3.tail.headD 0, r2.headD 0, r2.tail.headD 0]
          s3.mem with _ | ⟨r4, m4⟩
      · rw [c4] at hW; simp [basisNamesOkW.k_pin_list_ok] at hW
      rw [c4, basisNamesOkW.k_pin_list_ok.arm1] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      have hl3 : r3.tail.headD 0 = bl := by rw [hr3]; rfl
      obtain ⟨b4, a4, hrun4, hT4, hg4, hb4⟩ := hP.pl dn vis fe _ _ _ _ block pins n s3.mem a2 r4 m4
        ⟨hT3, hR2.ok, hR2.read, by rw [hl3]; exact hsl3.dec, hpd2.1.grow (basisDec_mono dn _ _) hg3,
          ⟨_, hbP2⟩, ⟨_, hP2⟩⟩ c4
      refine ⟨b4, a4, ?_, hT4, hg1.trans (hg2.trans (hg3.trans hg4)), by simpa using hb4⟩
      simp only [ConRon.Arena.basisNamesOk, StateT.run_bind, hrun1, except_ok_bind]
      show (do ConRon.Arena.pinListOk block (← ConRon.Arena.BasisKind.decls kind)).run a1 = _
      simp only [StateT.run_bind, hrun2, except_ok_bind]
      exact hrun4

/-- **`basis_names_error(k, bo, bl)` refines `basisNamesError d`**: an inductive block's name test
again (`basis_name_hit`); the twin's error a reject (`invalid`). -/
theorem bne_sim (hP : BnoProg p) {n : Nat} {m : Mem} {a : AState} {d : IDeclaration}
    {k nw bo bl : Word} (hT : StageT dn vis fe m a) (hok : ConRon.Bridge.StateOK a)
    (hr : ConRon.Bridge.ReadOK a) (hA : BnoArgs d k nw bo bl m)
    (hden : ∃ x, Frontend.denoteDecl a.store d = some x) :
    Sim (callW p n "basis_names_error" [k, bo, bl] m) (ConRon.Arena.basisNamesError d) a
      (fun _ ce m' a' => StageT dn vis fe m' a' ∧ IWGrow m m' ∧ twinCls ce = 1) := by
  intro r m' h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (basisNamesError_specW p hP.bne n _ k bo bl) h
  generalize s'.mem = m' at hW ⊢
  cases n with
  | zero => simp [basisNamesErrorW] at hW
  | succ n =>
  have one : k ≠ 6 → ∀ ce : CheckError, ce = .invalid "reserved basis name" →
      (ConRon.Arena.basisNamesError d).run a = .ok (ce, a) →
      ∃ x a', (ConRon.Arena.basisNamesError d).run a = .ok (x, a') ∧ StageT dn vis fe m' a' ∧
        IWGrow m m' ∧ twinCls x = 1 := by
    intro h6 ce hce hrun
    rw [basisNamesErrorW.arm2 p n m k bo bl h6] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨ce, a, hrun, hT, IWGrow.refl _, by rw [hce]; rfl⟩
  cases d with
  | defnDecl cv v hh =>
    obtain ⟨rfl, -⟩ := hA; exact one (by decide) (.invalid "reserved basis name") rfl rfl
  | thmDecl cv v =>
    obtain ⟨rfl, -⟩ := hA; exact one (by decide) (.invalid "reserved basis name") rfl rfl
  | opaqueDecl cv v =>
    obtain ⟨rfl, -⟩ := hA; exact one (by decide) (.invalid "reserved basis name") rfl rfl
  | axiomDecl cv =>
    obtain ⟨rfl, -⟩ := hA; exact one (by decide) (.invalid "reserved basis name") rfl rfl
  | quotDecl qk cv =>
    obtain rfl := hA; exact one (by decide) (.invalid "reserved basis name") rfl rfl
  | indDecl block nP =>
    obtain ⟨rfl, hBA⟩ := hA
    obtain ⟨x, hx⟩ := hden
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hx
    obtain ⟨bP, hbP, -⟩ := hx
    rw [basisNamesErrorW.arm1 p n m 6 bo bl rfl] at hW
    rcases c1 : callW p n "basis_name_hit" [bo, bl] m with _ | ⟨r1, m1⟩
    · rw [c1] at hW; simp [basisNamesErrorW.k_basis_name_hit] at hW
    rw [c1] at hW
    obtain ⟨hit, a1, hrun1, hT1, hg1, hd1⟩ :=
      (hP.basis.nameHit dn vis fe) bo bl block n m a r1 m1 ⟨hT, hok, hr, hBA, _, hbP⟩ c1
    cases hit with
    | none =>
      have h0 : r1.headD 0 = 0 := hd1
      rw [basisNamesErrorW.k_basis_name_hit.arm2 p r1 m1 h0] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨.invalid "reserved basis name in the block of", a1, ?_, hT1, hg1, rfl⟩
      simp only [ConRon.Arena.basisNamesError, StateT.run_bind, hrun1, except_ok_bind]; rfl
    | some kind =>
      obtain ⟨h1, -, -⟩ := hd1
      rw [basisNamesErrorW.k_basis_name_hit.arm1 p r1 m1 (by rw [h1]; decide)] at hW
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      refine ⟨.invalid "reserved basis name: the block is not the pinned one", a1, ?_, hT1, hg1, rfl⟩
      simp only [ConRon.Arena.basisNamesError, StateT.run_bind, hrun1, except_ok_bind]; rfl

end bno

end L.Ind
