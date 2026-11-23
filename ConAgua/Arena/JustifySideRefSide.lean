module

public import ConAgua.Arena.JustifySideModels
public import ConAgua.Arena.Pins
public import ConAgua.Arena.IndSumSpec.MentionsConst
public import ConAgua.Arena.IndRealFvt
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Arena.JustifySideModels

@[expose] public section

/-!
# The side records: the refinements (lane compare)

`builtin_axiom_name` refines `builtinAxiomName` (a read of the pin table), `side_record` refines
`sideRecord` (the record rewritten in place: its kind word `1` when it becomes the axiom of its
statement), `side_records` refines `sideRecordsGo` over the front's records: `DECL` decodes to
the twin's result.
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option autoImplicit false

open Std.WP
open scoped Lean.Order
open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP DeclsF DeclAtF DeclAt CVAt dw)
open L.Ind (StageR IWGrow IWOK mcMR eView mcSch mcSch_wf mentionsConstGoL mentionsConstL MCM CWF)

/-! ## `builtin_axiom_name` -/

/-- The twin's built-in axiom test at a filled pin table: the name is one of the seven pin words. -/
theorem builtinAxiomName_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) (n : NIdx) :
    (builtinAxiomName n).run a = .ok (n == decI (pinW m 33) || n == decI (pinW m 34) ||
      n == decI (pinW m 5) || n == decI (pinW m 14) || n == decI (pinW m 43) ||
      n == decI (pinW m 46) || n == decI (pinW m 47), a) := by
  have r1 := pinAt_run hF 32 (by decide); have r2 := pinAt_run hF 33 (by decide)
  have r3 := pinAt_run hF 4 (by decide); have r4 := pinAt_run hF 13 (by decide)
  have r5 := pinAt_run hF 42 (by decide); have r6 := pinAt_run hF 45 (by decide)
  have r7 := pinAt_run hF 46 (by decide)
  simp only [builtinAxiomName, propextName, pinPropext, choiceName, pinChoice, pinQuotSound,
    pinSorryAx, trustCompilerName, pinTrustCompiler, ofReduceNatName, pinOfReduceNat,
    ofReduceBoolName, pinOfReduceBool, PIN_PROPEXT, PIN_CHOICE, PIN_QUOT_SOUND, PIN_SORRY_AX,
    PIN_TRUST_COMPILER, PIN_OF_REDUCE_NAT, PIN_OF_REDUCE_BOOL, StateT.run_bind, r1, r2, r3, r4, r5,
    r6, r7]
  have q2 : pinAt 33 a = _ := r2; have q3 : pinAt 4 a = _ := r3; have q4 : pinAt 13 a = _ := r4
  have q5 : pinAt 42 a = _ := r5; have q6 : pinAt 45 a = _ := r6; have q7 : pinAt 46 a = _ := r7
  simp [bind, Except.bind, q2, q3, q4, q5, q6, q7, StateT.run, pure, StateT.pure, Except.pure]

/-- **`builtin_axiom_name` refines `builtinAxiomName`**: at a name handle word, a returning run
leaves the memory and returns the twin's answer (`0`/`1`), which keeps the state. -/
@[refines ConRon.Arena.builtinAxiomName]
theorem builtinAxiomName_refines (p : Prog) (hp : p.lookup "builtin_axiom_name" = some builtinAxiomNameL)
    (n : Nat) (s₀ : St) (a : AState) (hP : PinsR s₀.mem a.pins) (w : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "builtin_axiom_name" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      (builtinAxiomName (decI w)).run a = .ok (r.headD 0 != 0, a); ⊤⦄ :=
  triple_post (builtinAxiomName_specW p hp n s₀ w) fun r s ⟨hl, hm, hW⟩ => by
    refine ⟨hm, hl, ?_⟩
    simp only [builtinAxiomNameW] at hW
    split at hW
    · cases hW
    rename_i h0
    have hF := hP.full h0
    rw [builtinAxiomName_run hF]
    have hl : ∀ i, i < 51 → (decI w == (decI (pinW s₀.mem (1 + i)) : NIdx)) = decide (w = pinW s₀.mem (1 + i)) :=
      fun i hi => by
        rw [nidx_beq, decI_word_self _ (hF.names_lt i hi), decI_word_self _ hw]
        exact decide_eq_decide.mpr eq_comm
    have e33 := hl 32 (by decide); have e34 := hl 33 (by decide); have e5 := hl 4 (by decide)
    have e14 := hl 13 (by decide); have e43 := hl 42 (by decide); have e46 := hl 45 (by decide)
    have e47 := hl 46 (by decide)
    simp only [show 1 + 32 = 33 from rfl, show 1 + 33 = 34 from rfl, show 1 + 4 = 5 from rfl,
      show 1 + 13 = 14 from rfl, show 1 + 42 = 43 from rfl, show 1 + 45 = 46 from rfl,
      show 1 + 46 = 47 from rfl] at e33 e34 e5 e14 e43 e46 e47
    rw [e33, e34, e5, e14, e43, e46, e47]
    simp only [pinW] at *
    split at hW
    · rename_i hc
      rw [← Option.some.inj hW]
      simp only [rdW] at hc
      simp only [show (33 : Word).toNat = 33 from rfl, show (34 : Word).toNat = 34 from rfl,
        show (5 : Word).toNat = 5 from rfl, show (14 : Word).toNat = 14 from rfl,
        show (43 : Word).toNat = 43 from rfl, show (46 : Word).toNat = 46 from rfl,
        show (47 : Word).toNat = 47 from rfl] at hc
      rcases hc with h | h | h | h | h | h | h <;> simp [h]
    · rename_i hc
      rw [← Option.some.inj hW]
      simp only [rdW] at hc
      simp only [show (33 : Word).toNat = 33 from rfl, show (34 : Word).toNat = 34 from rfl,
        show (5 : Word).toNat = 5 from rfl, show (14 : Word).toNat = 14 from rfl,
        show (43 : Word).toNat = 43 from rfl, show (46 : Word).toNat = 46 from rfl,
        show (47 : Word).toNat = 47 from rfl, not_or] at hc
      simp [hc]

/-! ## Frames -/

/-- **The stage relation across a write of the front's records** (`DECL`, `DLP`: front arrays
the checker's relations do not read). -/
theorem _root_.L.Ind.StageR.frame_front {vis : Word} {fe : IFEnv} {m m' : Mem} {a : AState}
    (hS : StageR vis fe m a) (hf : MemFrame [DECL] [] m m') : StageR vis fe m' a ∧ IWGrow m m' := by
  have hA3 : (L.Ind.IW : TieredArray) ∉ [(DECL : TieredArray)] ∧ (EREC : TieredArray) ∉ [(DECL : TieredArray)] ∧
      tier1 EREC ∉ [(DECL : TieredArray)] := by decide
  have hC3 : (129 : Word) ∉ ([] : List Word) ∧ (130 : Word) ∉ ([] : List Word) ∧ (200 : Word) ∉ ([] : List Word) := by
    simp
  refine ⟨⟨⟨⟨?_, ?_⟩, hS.check.core.frame (by decide) (by simp [AvoidC]) hf,
    hS.check.pins.frame (by decide) hf,
    hS.check.env.frame (by decide) (by simp) hf,
    hS.check.mode.frame hf (by simp) (by simp)⟩, IWOK.of_keep hf hA3 hC3 hS.iw⟩, IWGrow.of_keep hf hA3 hC3⟩
  · exact ArenaR.frame_ext _ _ (by decide) (by simp) m m' hf a hS.check.arena.base
  · exact DerR.frameM _ _ m m' hf (by decide) a hS.check.arena.der

/-! ## `mentions_const`, with its frame -/

/-- **`mentions_const` with its write set**: `mentionsConst_refines`, and only the `mc` memo
changes (`MCM`, `CTL[216]`, `CTL[217]`). -/
theorem mentionsConst_fr (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "mc_find" = some (memoFindG mcSch)) (hput : p.lookup "mc_put" = some (memoPutG mcSch))
    (hgo : p.lookup "mentions_const_go" = some mentionsConstGoL)
    (hcl : p.lookup "mc_clear" = some (memoClearG mcSch))
    (hp : p.lookup "mentions_const" = some mentionsConstL) {n : Nat} {m m' : Mem} {r : List Word}
    {T e : Word} {vis : Word} {fe : IFEnv} {a : AState}
    (hc : callW p n "mentions_const" [T, e] m = some (r, m')) (hh : L.Ind.H e) (hT : L.Ind.H T)
    (hS : StageR vis fe m a) (hM : ∃ mp, mcMR m mp) :
    (mentionsConst (decI T) (decE e)).run a = .ok (r.headD 0 != 0, a) ∧ (∃ mp, mcMR m' mp) ∧
      StageR vis fe m' a ∧ MemFrame [MCM] [mcSch.cs, mcSch.cs + 1] m m' := by
  obtain ⟨mp0, hM⟩ := hM
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.mentionsConst_spec p hv hf hput hgo hcl hp n _ T e) hc
  subst hs'
  simp only at hm
  by_cases h0 : rdW (m.arr64 CTL) mcSch.cs + 2 = 0
  · simp [L.Ind.mcConstW, h0] at hm
  rw [L.Ind.mcConstW_eq n _ T e h0] at hm
  have hf0 := mclearG_frame mcSch m
  have hM0 := memoRG_clear mcSch mcSch_wf bmKey (fun w : Word => w != 0) m mp0 hM h0
  have hA0 : ArenaR (mclearG mcSch m) a :=
    ArenaR.frame (A := []) (C := [mcSch.cs, mcSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by simp [mcSch] at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.check.arena.base
  obtain ⟨⟨c, mp1⟩, _, hrun, rfl, hbb, hM1, hfr1⟩ := L.Ind.mcGoOK n _ a CWF T e ∅ hA0 hh hT hM0 _ _ hm
  have hfall : MemFrame [MCM] [mcSch.cs, mcSch.cs + 1] m s'.mem :=
    (hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp [mcSch]))
  obtain ⟨hS', -⟩ := L.Ind.StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp [mcSch] at hx; rcases hx with rfl | rfl <;> decide) (by decide)
    (by simp [mcSch])
  have hrun' : (ConRon.Arena.mentionsConst (decI T) (decE e)).run a = .ok (c, a) := by
    simp only [ConRon.Arena.mentionsConst, StateT.run_bind]
    rw [L.Ind.CWF_eq] at hrun
    rw [hrun]
    rfl
  rw [hrun', hbb]
  exact ⟨rfl, ⟨mp1, hM1⟩, hS', hfall⟩

/-! ## A record made an axiom -/

/-- `sideRecord`'s result for a value record: itself, or the axiom of its statement. -/
def sideRes (d : IDeclaration) (cv : IConstantVal) (b c : Bool) : IDeclaration :=
  if b then d else if c then .axiomDecl cv else d

theorem sideRecordVal_run {a : AState} {d : IDeclaration} {cv : IConstantVal} {v : EIdx} {b : Bool}
    (hb : (builtinAxiomName cv.name).run a = .ok (b, a)) {sa : NIdx} {c : Bool}
    (hs : b = false → pinSorryAx.run a = .ok (sa, a))
    (hm : b = false → (mentionsConst sa v).run a = .ok (c, a)) :
    (sideRecordVal d cv v).run a = .ok (sideRes d cv b c, a) := by
  have hb' : builtinAxiomName cv.name a = .ok (b, a) := hb
  show sideRecordVal d cv v a = _
  cases b with
  | true => simp only [sideRecordVal, bind, StateT.bind, hb', Except.bind, ite_true, sideRes]; rfl
  | false =>
    have hs' : pinSorryAx a = .ok (sa, a) := hs rfl
    have hm' : mentionsConst sa v a = .ok (c, a) := hm rfl
    cases c <;> simp only [sideRecordVal, bind, StateT.bind, hb', hs', hm', Except.bind, sideRes,
      Bool.false_eq_true, ite_true, ite_false] <;> rfl

theorem dw_set! {D : Array Word} {i j q : Nat} (v : Word) (hj : j < 8) :
    dw (D.set! (1 + 8 * q) v) i j = if i = q ∧ j = 0 ∧ 1 + 8 * q < D.size then v else dw D i j := by
  simp only [dw, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : i = q ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    by_cases hb : 1 + 8 * i < D.size
    · simp [hb]
    · simp [hb, Array.getElem?_eq_none (Nat.le_of_not_lt hb)]
  · have : ¬ (1 + 8 * q = 1 + 8 * i + j) := by omega
    simp only [this, ite_false]
    rw [ite_eq_right (fun c => h ⟨c.1, c.2.1⟩)]

/-- **A value record's kind word set to `1`**: the records decode with record `k` the axiom of
its statement. -/
theorem DeclsF.setAxiom {D P : Array Word} {ds : Array IDeclaration} (hD : DeclsF D P ds) {k : Nat}
    (hk : k < ds.size) {cv : IConstantVal} (hcv : CVAt D P k cv) :
    DeclsF (D.set! (1 + 8 * k) 1) P (ds.set k (.axiomDecl cv)) := by
  have hb : 1 + 8 * k < D.size := by have := hD.room; omega
  have hdw : ∀ i j, j < 8 → dw (D.set! (1 + 8 * k) 1) i j = if i = k ∧ j = 0 then 1 else dw D i j :=
    fun i j hj => by rw [dw_set! 1 hj]; simp [hb]
  have hcv' : CVAt (D.set! (1 + 8 * k) 1) P k cv := by
    obtain ⟨c1, c2, c3, c4⟩ := hcv
    simp only [CVAt, hdw k 1 (by decide), hdw k 2 (by decide), hdw k 3 (by decide),
      hdw k 4 (by decide), show ¬ (1 = 0) from by decide, show ¬ (2 = 0) from by decide,
      show ¬ (3 = 0) from by decide, show ¬ (4 = 0) from by decide, and_false, ite_false]
    exact ⟨c1, c2, c3, c4⟩
  refine ⟨by simp; exact hD.dsize, hD.psize, ?_, by simp; exact hD.room, hD.ptop, fun i hi => ?_,
    fun i hi b nP he => ?_⟩
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.size_set]
    rw [ite_eq_right (by omega)]; exact hD.count
  · simp only [Array.size_set] at hi
    by_cases e : i = k
    · subst e; simp only [Array.getElem_set_self]
      exact ⟨by rw [hdw _ _ (by decide)]; simp, hcv'⟩
    · rw [Array.getElem_set_ne (by omega) (by omega) (Ne.symm e)]
      have hr := hD.recs i (by omega)
      have hc : ∀ j, j < 8 → dw (D.set! (1 + 8 * k) 1) i j = dw D i j := fun j hj => by
        rw [hdw i j hj]; simp [e]
      have h0 := hc 0 (by decide); have h1 := hc 1 (by decide); have h2 := hc 2 (by decide)
      have h3 := hc 3 (by decide); have h4 := hc 4 (by decide); have h5 := hc 5 (by decide)
      have h6 := hc 6 (by decide); have h7 := hc 7 (by decide)
      cases hx : ds[i] <;> rw [hx] at hr <;> simp_all [DeclAtF, DeclAt, CVAt, L.Front.IndDeclAt]
  · simp only [Array.size_set] at hi
    by_cases e : i = k
    · subst e; simp at he
    · rw [Array.getElem_set_ne (by omega) (by omega) (Ne.symm e)] at he
      exact hD.npb i (by omega) b nP he

end L.Arena
