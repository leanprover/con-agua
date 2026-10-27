import ConAgua.Front.Line
import ConAgua.Front.IndApplyTwin
import ConAgua.Scan.LineLink
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `front_line` refines con-ron's per-line step

`frontLineW_refines`: if `front_line(i)`'s model returns `(1, next)`, con-leche's scanner reads a
record `r` at `i` with `next` the position after it (`scanLineFwd`), and con-ron's `applyLine st r`
succeeds from the arena state `a₀` with a parse state `st'` such that the memory after is related
to its arena state by `ArenaD` and to `st'` by `StateDR`. `frontLine_refines` is the same for the
L run.
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line L.Front.Fields
open ConLeche.Frontend hiding StateD RecordVerdict applyLine
open ConAgua.Scan ConAgua.Scan.RecordsLink ConAgua.Scan.LineLink
open ConAgua.Front.FieldsLink
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-- **One line, as con-ron applies it**: the scanner reads the record `r` at `i` and the next
position `q` (the word `nx`), `applyLine st r` succeeds from `a₀` with the parse state `st'`, and
the memory `m` is related to the arena state after by `ArenaD` and to `st'` by `StateDR`. -/
def LineStep (b : ByteArray) (i : USize) (nx : Word) (st : StateD) (a₀ : AState) (m : Mem) : Prop :=
  ∃ r q st', scanLineFwd b i = .ok r q ∧ q.toUInt64 = nx ∧ AM.ok (applyLine st r) a₀ ∧
    AM.res (applyLine st r) a₀ = .inl st' ∧ ArenaD m (AM.st (applyLine st r) a₀) ∧ StateDR m st'

/-- The pure arena steps of `applyLine`. -/
theorem applyLine_pure (st : StateD) (a₀ : AState) (r : LineRec)
    (hr : r = .header ∨ r = .blank) :
    AM.ok (applyLine st r) a₀ ∧ AM.res (applyLine st r) a₀ = .inl st ∧
      AM.st (applyLine st r) a₀ = a₀ := by
  rcases hr with rfl | rfl <;> exact ⟨trivial, rfl, rfl⟩

theorem applyLine_name (st : StateD) (a₀ : AState) (i : Nat) (r : NameRec)
    (h : AM.ok (parseNameEntryD st i r) a₀) :
    AM.ok (applyLine st (.name i r)) a₀ ∧
      AM.res (applyLine st (.name i r) : AM (StateD ⊕ RecordVerdict)) a₀ = .inl (AM.res (parseNameEntryD st i r) a₀) ∧
      AM.st (applyLine st (.name i r)) a₀ = AM.st (parseNameEntryD st i r) a₀ := by
  obtain ⟨h1, h2, h3⟩ := AM.bind_pure (parseNameEntryD st i r) (Sum.inl : StateD → StateD ⊕ RecordVerdict) a₀ h
  exact ⟨h1, h3, h2⟩

theorem applyLine_level (st : StateD) (a₀ : AState) (i : Nat) (r : LevelRec)
    (h : AM.ok (parseLevelEntryD st i r) a₀) :
    AM.ok (applyLine st (.level i r)) a₀ ∧
      AM.res (applyLine st (.level i r) : AM (StateD ⊕ RecordVerdict)) a₀ = .inl (AM.res (parseLevelEntryD st i r) a₀) ∧
      AM.st (applyLine st (.level i r)) a₀ = AM.st (parseLevelEntryD st i r) a₀ := by
  obtain ⟨h1, h2, h3⟩ := AM.bind_pure (parseLevelEntryD st i r) (Sum.inl : StateD → StateD ⊕ RecordVerdict) a₀ h
  exact ⟨h1, h3, h2⟩

section refine
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- A name or level line: the fields `f` against the record `r`, applied. -/
theorem lineRecW_refines (m m' : Mem) (_hm : m.arr8 IN = b.data) (a₀ : AState) (st : StateD)
    (hR : ArenaD m a₀) (hD : StateDR m st) (hmode : ModeOK m) (f : Fld) (r : LineRec)
    (hRec : f.pl ≠ 0 → RecR b r f) (h : lineRecW b.data m f.pl f.idx f.a f.c f.d = some m') :
    ∃ st', AM.ok (applyLine st r) a₀ ∧ AM.res (applyLine st r) a₀ = .inl st' ∧
      ArenaD m' (AM.st (applyLine st r) a₀) ∧ StateDR m' st' ∧ ModeOK m' := by
  unfold lineRecW at h
  split at h
  · cases h
  rename_i hpl0
  have hRR := hRec hpl0
  split at h
  · -- the header
    rename_i hpl7
    simp only [Option.some.injEq] at h
    subst h
    have hr : r = .header := by
      rcases r with ⟨_, _ | _⟩ | ⟨_, _ | _ | _ | _⟩ | _ | _ | _ | _ <;>
        simp_all [RecR, PlR, NameR]
    obtain ⟨h1, h2, h3⟩ := applyLine_pure st a₀ r (.inl hr)
    exact ⟨st, h1, h2, by rw [h3]; exact hR, hD, hmode⟩
  rename_i hpl7
  split at h
  · cases h
  rename_i hnone
  simp only [not_or] at hnone
  obtain ⟨hidx, ha⟩ := hnone
  split at h
  · -- a `str` name
    rename_i hpl1
    unfold applyStrW at h
    split at h
    · cases h
    rename_i hc0
    cases hP : L.Front.Unescape.strPutEscW b.data m f.c f.d with
    | none => rw [hP, strK_none] at h; cases h
    | some q =>
    obtain ⟨l, m₁⟩ := q
    rw [hP] at h
    replace h := strK_intern h
    rcases r with ⟨I, (⟨P, S⟩ | ⟨P, N⟩)⟩ | ⟨_, (_ | ⟨_, _⟩ | ⟨_, _⟩ | _)⟩ | _ | _ | _ | _ <;>
      simp only [RecR, PlR, NameR] at hRR
    · obtain ⟨hI, -, hP', hS⟩ := hRR
      obtain ⟨hg, hq, hk⟩ := ConAgua.Front.UnescapeLink.strPutEsc_link h64 b hsize m m₁ hR.1.lit.1 f.c f.d S
        (hS hc0) l hP
      have hmo₁ := ModeOK.growsF hmode hg
      obtain ⟨hok', hR', hD', hM'⟩ := applyNStrW_refines m₁ m' a₀ st
        (ArenaD.grow _ _ hg _ hR) (hD.frame (grows_frame _ _ hg) (by tapart) (by tapart))
        f.idx f.a m.top l hq S hk (ModeOK.slice0 hmo₁ hq) h
      rw [hI hidx, hP' ha] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_name st a₀ I (.str P S) hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmo₁⟩
    all_goals simp_all
  rename_i hpl1
  split at h
  · cases h
  rename_i hcn
  split at h
  · -- a `num` name
    rename_i hpl2
    have hc : f.c ≠ NONE := fun h' => hcn ⟨h', .inl hpl2⟩
    rcases r with ⟨I, (⟨P, S⟩ | ⟨P, N⟩)⟩ | ⟨_, (_ | ⟨_, _⟩ | ⟨_, _⟩ | _)⟩ | _ | _ | _ | _ <;>
      simp only [RecR, PlR, NameR] at hRR
    · exact absurd (hRR.2.1.symm.trans hpl2) (by decide)
    · obtain ⟨hI, -, hP, hN⟩ := hRR
      obtain ⟨hok', hR', hD', hM'⟩ := applyNNumW_refines m m' a₀ st hR hD f.idx f.a f.c h
      rw [hI hidx, hP ha, hN hc] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_name st a₀ I (.num P N) hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    all_goals simp_all
  · -- a level
    rename_i hpl2
    obtain ⟨hok', hR', hD', hM'⟩ := applyLevelW_refines m m' a₀ st hR hD f.idx (f.pl - 2) f.a f.c h
    rcases r with ⟨_, (⟨_, _⟩ | ⟨_, _⟩)⟩ | ⟨I, (U | ⟨U, V⟩ | ⟨U, V⟩ | U)⟩ | _ | _ | _ | _ <;>
      simp only [RecR, PlR, NameR] at hRR
    · simp_all
    · simp_all
    · obtain ⟨hI, hp, hU⟩ := hRR
      have hk : levelRecW (f.pl - 2) f.a f.c = .succ U := by
        rw [hp]; show LevelRec.succ f.a.toNat = _; rw [hU ha]
      rw [hk, hI hidx] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_level st a₀ I _ hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    · obtain ⟨hI, hp, hU, hV⟩ := hRR
      have hc : f.c ≠ NONE := fun h' => hcn ⟨h', .inr (.inl hp)⟩
      have hk : levelRecW (f.pl - 2) f.a f.c = .max U V := by
        rw [hp]; show LevelRec.max f.a.toNat f.c.toNat = _; rw [hU ha, hV hc]
      rw [hk, hI hidx] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_level st a₀ I _ hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    · obtain ⟨hI, hp, hU, hV⟩ := hRR
      have hc : f.c ≠ NONE := fun h' => hcn ⟨h', .inr (.inr hp)⟩
      have hk : levelRecW (f.pl - 2) f.a f.c = .imax U V := by
        rw [hp]; show LevelRec.imax f.a.toNat f.c.toNat = _; rw [hU ha, hV hc]
      rw [hk, hI hidx] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_level st a₀ I _ hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    · obtain ⟨hI, hp, hU⟩ := hRR
      have hk : levelRecW (f.pl - 2) f.a f.c = .param U := by
        rw [hp]; show LevelRec.param f.a.toNat = _; rw [hU ha]
      rw [hk, hI hidx] at hok' hR' hD'
      obtain ⟨h1, h2, h3⟩ := applyLine_level st a₀ I _ hok'
      exact ⟨_, h1, h2, by rw [h3]; exact hR', hD', hM' hmode⟩
    all_goals simp_all

omit h64 hsize in
/-- An expression line, as `applyLine` applies it. -/
theorem applyLine_expr (st : StateD) (a₀ : AState) (i : Nat) (r : ExprRec)
    (h : AM.ok (parseExprEntryD st i r) a₀) :
    AM.ok (applyLine st (.expr i r)) a₀ ∧
      AM.res (applyLine st (.expr i r) : AM (StateD ⊕ RecordVerdict)) a₀ =
        .inl (AM.res (parseExprEntryD st i r) a₀) ∧
      AM.st (applyLine st (.expr i r)) a₀ = AM.st (parseExprEntryD st i r) a₀ := by
  obtain ⟨h1, h2, h3⟩ := AM.bind_pure (parseExprEntryD st i r)
    (Sum.inl : StateD → StateD ⊕ RecordVerdict) a₀ h
  exact ⟨h1, h3, h2⟩

omit h64 hsize in
/-- A declaration line keeps the mode: it writes `DLP` and `DECL` only. -/
theorem applyDeclW_mode (b : Array UInt8) (m m' : Mem) (st : StateD) (hD : StateDR m st)
    (pl name lps type value hk hn flag : Word)
    (h : applyDeclW b m pl name lps type value hk hn flag = some m') (hmo : ModeOK m) : ModeOK m' := by
  unfold applyDeclW at h
  rcases hK : declKindW pl hk hn flag with _ | ⟨k, q⟩ <;> simp only [hK, declK0, reduceCtorEq] at h
  unfold declCvW at h
  have hok : tblOK m NID name = true ∧ tblOK m EID type = true :=
    Classical.byContradiction fun hok => by simp [hok] at h
  simp only [hok, and_self, ↓reduceIte] at h
  rcases hP : lpPutW b m lps with _ | m₁ <;> simp only [hP, declK1, reduceCtorEq] at h
  have hDR := hD.decls
  unfold lpPutW at hP
  split at hP; cases hP
  have hps := hDR.psize
  have hptop := hDR.ptop
  have hrd : rdW (m.arr64 DLP) 0 = (m.arr64 DLP)[0]?.getD 0 := rfl
  obtain ⟨-, F2, -⟩ := lpLoopM_facts b (rdW (m.arr64 DLP) 0) m (lps + 1) 0 m₁
    hP (by rw [hrd]; simp; omega) hps
  have hm'D : m₁.arr64 DECL = m.arr64 DECL := F2.1 DECL (by decide) (by decide)
  have hpush : ∃ v, pushW m₁ k (tblW m NID name) (rdW (m.arr64 DLP) 0) (lsCntN b (lps + 1) 0)
      (tblW m EID type) v q hn = some m' := by
    split at h
    · split at h
      · exact ⟨_, h⟩
      · cases h
    · exact ⟨0, h⟩
  obtain ⟨v, hpu⟩ := hpush
  have hds : (m₁.arr64 DECL).size < 2 ^ 63 := by rw [hm'D]; exact hDR.dsize
  obtain ⟨G1, -⟩ := pushW_facts m₁ m' _ _ _ _ _ _ _ _ _ rfl hpu hds
  exact MemFrame.modeOK G1 (by simp) (by simp) (MemFrame.modeOK F2 (by simp) (by simp) hmo)

/-- **The fields after a line's `{`, applied**: on the record con-leche's line loop reads there,
`apply_any`'s model is con-ron's `applyLine`. -/
theorem applyAnyW_refines (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (hm : m.arr8 IN = b.data) (a₀ : AState)
    (st : StateD) (hR : ArenaD m a₀) (hD : StateDR m st) (hmode : ModeOK m)
    (hok : ConRon.Bridge.StateOK a₀)
    (j : USize) (r : LineRec) (e : USize)
    (hloop : scanLineLoop b j true 0 0 .absent = .ok r e)
    (h : applyAnyW p b.data m j.toUInt64 = some m') :
    ∃ st', AM.ok (applyLine st r) a₀ ∧ AM.res (applyLine st r) a₀ = .inl st' ∧
      ArenaD m' (AM.st (applyLine st r) a₀) ∧ StateDR m' st' ∧ ModeOK m' := by
  unfold applyAnyW at h
  split at h
  · rename_i hpl
    have hRec := recLine_link b h64 hsize j true 0 0 .absent Fld.none r e hloop itemR_zero trivial
    exact lineRecW_refines b h64 hsize m m' hm a₀ st hR hD hmode _ r hRec h
  split at h
  · rename_i _ hpl
    have hX := exprLineN_link b h64 hsize j r e hloop hpl
    generalize exprLineN b.data j.toUInt64 = f at hX h
    rcases r with _ | _ | ⟨i, er⟩ | _ | _ | _ <;> simp only [ERecR] at hX
    obtain ⟨hI, hE⟩ := hX
    obtain ⟨hok, hA', hD', hM'⟩ := applyExprW_refines b h64 hsize m m' a₀ st hR hD hmode f i er hI hE h
    obtain ⟨h1, h2, h3⟩ := applyLine_expr st a₀ i er hok
    exact ⟨_, h1, h2, by rw [h3]; exact hA', hD', hM'⟩
  · unfold applyDLineW at h
    split at h
    · cases h
    rename_i _ _ hpl
    have hX : (declLineN b.data j.toUInt64).pl ≠ 0 → DRecR b r (declLineN b.data j.toUInt64) :=
      declLine_link b h64 hsize j true 0 0 .absent DFld.none r e hloop trivial
    replace hX := hX hpl
    generalize declLineN b.data j.toUInt64 = f at hX h
    rcases r with _ | _ | _ | d | _ | _ <;> simp only [DRecR] at hX
    split at h
    · -- an inductive block: `apply_ind`'s run, its model, the twin's `.ind` arm
      rename_i h25
      cases d with
      | ind tys cts rcs =>
        obtain ⟨-, v, hv, e', hscan⟩ := hX
        obtain ⟨x, hx, hxm⟩ := runF_some h
        have hW := M.of_run (P := fun s => s = ⟨m, Locals.init []⟩) rfl hx
          (L.Front.Ind.applyInd_spec p hFI hAI hII hXI b.data hsize x.1 _ hm f.name)
        rw [hxm, hv] at hW
        obtain ⟨st', h1, h2, h3, h4⟩ := L.Front.Ind.applyIndW_twin h64 hsize hR hD hok hscan hW.2
        have h1' : (applyLine st (.decl (.ind tys cts rcs))).run a₀ = .ok (.inl st', a₀) := h1
        refine ⟨st', by simp [AM.ok, h1'], by simp [AM.res, h1'], by simp [AM.st, h1']; exact h2, h3,
          h4 hmode⟩
      | ax _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
      | defn _ _ _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
      | thm _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
      | opaq _ _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
      | quot _ _ => exact absurd (hX.1.symm.trans h25) (by decide)
    obtain ⟨st', h1, h2, h3, hA', hD'⟩ := applyDeclW_refinesAM b m m' a₀ st hR hD f d hX h
    refine ⟨st', h1, ?_, by rw [h3]; exact hA', hD', applyDeclW_mode b.data m m' st hD _ _ _ _ _ _ _ _ h hmode⟩
    simp only [AM.res, h2]

/-- **`front_line`'s model refines con-ron's per-line step**: a line it accepts (`(1, nx)`) is one
con-leche's scanner reads and con-ron's `applyLine` applies, with `ArenaD` and `StateDR` after. -/
theorem frontLineW_refines (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (hm : m.arr8 IN = b.data) (i : USize)
    (a₀ : AState) (st : StateD) (hR : ArenaD m a₀) (hD : StateDR m st) (hmode : ModeOK m)
    (hsok : ConRon.Bridge.StateOK a₀) (nx : Word)
    (h : frontLineW p b.data m i.toUInt64 = some ([1, nx], m')) :
    LineStep b i nx st a₀ m' ∧ ModeOK m' := by
  have hL := lineFwd_link b h64 hsize i
  have hs := ConAgua.Scan.skipWs_toUInt64_eq b h64 (by omega) i
  unfold frontLineW at h
  split at h
  · simp at h
  rename_i hok
  obtain ⟨r, q, hsc, hq⟩ : ∃ r q, scanLineFwd b i = .ok r q ∧
      q.toUInt64 = (lineFwdN b.data i.toUInt64).2 := by
    revert hL hok
    cases scanLineFwd b i with
    | ok r q => intro hL _; exact ⟨r, q, rfl, by rw [← hL]; rfl⟩
    | err e => intro hL hok; rw [← hL] at hok; exact absurd rfl hok
  rw [USize.toNat_toUInt64, ← hs] at h
  have hsc' := hsc
  unfold scanLineFwd at hsc'
  dsimp only at hsc'
  generalize hsw : skipWs b i = s at hsc' h
  have hbs : b.data.size = b.size := rfl
  split at h
  · -- a record
    rename_i hrec
    obtain ⟨hslt, hs123⟩ := hrec
    have hsU : s < b.usize := (lt_usize_iff b h64 hsize s).mpr hslt
    have hb123 : byteAt b s = 123 := by
      rw [byteW_eq b h64 hsize] at hs123; exact (u8_toUInt64_eq _ 123 (by decide)).mp hs123
    simp only [hb123, show ((123 : UInt8) == 10) = false by decide, Bool.false_eq_true, ite_false,
      show (b.usize ≤ s) = False from propext ⟨fun h' => absurd hsU (USize.not_lt.mpr h'), False.elim⟩,
      show ((123 : UInt8) != 123) = false by decide] at hsc'
    split at hsc'
    · cases hsc'
    rename_i r' j hloop
    have hrr : r' = r := by
      split at hsc'
      · cases hsc'; rfl
      · split at hsc'
        · cases hsc'; rfl
        · cases hsc'
    subst hrr
    obtain ⟨m₁, hW, hm₁⟩ := Option.map_eq_some_iff.mp h
    rw [← succ_toUInt64 h64] at hW
    simp only [okRes, Prod.mk.injEq] at hm₁
    obtain ⟨hnx, rfl⟩ := hm₁
    have hnx' : nx = (lineFwdN b.data i.toUInt64).2 := by
      have := congrArg (fun l => l.tail.headD 0) hnx; simpa using this.symm
    obtain ⟨st', h1, h2, h3, h4, h5⟩ :=
      applyAnyW_refines b h64 hsize p hFI hAI hII hXI m m₁ hm a₀ st hR hD hmode hsok _ r' j hloop hW
    exact ⟨⟨r', q, st', hsc, by rw [hq, hnx'], h1, h2, h3, h4⟩, h5⟩
  · -- a blank line
    rename_i hrec
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and, and_true] at h
    obtain ⟨hnx, rfl⟩ := h
    have hr : r = .blank := by
      split at hsc'
      · cases hsc'; rfl
      split at hsc'
      · cases hsc'; rfl
      rename_i h10 hle
      split at hsc'
      · cases hsc'
      rename_i h123
      exfalso; apply hrec
      have hsU : s < b.usize := by
        have := USize.not_le.mp hle; exact this
      refine ⟨(lt_usize_iff b h64 hsize s).mp hsU, ?_⟩
      rw [byteW_eq b h64 hsize]
      have : byteAt b s = 123 := by simpa using h123
      rw [this]; rfl
    subst hr
    obtain ⟨h1, h2, h3⟩ := applyLine_pure st a₀ .blank (.inr rfl)
    exact ⟨⟨.blank, q, st, hsc, by rw [hq, hnx], h1, h2, by rw [h3]; exact hR, hD⟩, hmode⟩

end refine

/-- **`front_line(i)` refines con-ron's per-line step**: when it returns `(1, nx)`, con-leche's
scanner reads a record at `i` whose next position is `nx`, and con-ron's `applyLine` applies it,
with `ArenaD` and `StateDR` holding of the memory after. -/
@[refines ConRon.Arena.Frontend.applyLine]
theorem frontLine_refines (p : Prog) (hS : ScanLookups p) (hL : FrontLookups p)
    (hpf : p.lookup "front_line" = some frontLine)
    (hpn : p.lookup "apply_nstr" = some applyNStr) (hpu : p.lookup "apply_nnum" = some applyNNum)
    (hpl : p.lookup "apply_level" = some applyLevel) (hpr : p.lookup "apply_rec" = some applyRec)
    (hpt : p.lookup "apply_str" = some applyStr) (hE : ExprLookups p)
    (hpy : p.lookup "apply_any" = some applyAny) (hF : DeclFieldLookups p) (hDL : DeclLookups p)
    (hpz : p.lookup "apply_dline" = some applyDLine) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
    (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data) (i : USize) (hi : i.toNat ≤ b.size)
    (a₀ : AState) (st : StateD) (hR : ArenaD s₀.mem a₀) (hD : StateDR s₀.mem st)
    (hmode : ModeOK s₀.mem) (hok : ConRon.Bridge.StateOK a₀) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "front_line" [i.toUInt64]
    ⦃fun r s' => ∀ nx, r = [1, nx] → LineStep b i nx st a₀ s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  have hW := M.of_run (P := fun s => s = s₀) hs hrun
    (frontLine_spec p hS hL hpf hpn hpu hpl hpr hpt hE hpy hF hDL hpz b.data hsize n s₀ hm i.toUInt64
      (by rw [USize.toNat_toUInt64]; exact hi) hR.1.lit.1.2.2.1 hR.1.lit.1.2.2.2.1)
  intro nx hr
  subst hr
  exact (frontLineW_refines b h64 hsize p hFI hAI hII hXI s₀.mem s'.mem hm i a₀ st hR hD hmode hok nx hW).1

end L.Front
