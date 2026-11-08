module

public import ConAgua.Front.FrontPreOK
public import ConAgua.Arena.DeclAndPinIndDec
public import ConAgua.Checker.Pipeline
import ConRon.Bridge.Frontend.Prepare
import all Init.Data.Array.Basic
import all ConAgua.Front.IndApply

@[expose] public section

/-!
# The twin's prepared records have the front's shape (lane `pipeline`)

`prefix_frontDecls`: after the twin's five stages before the fold (`TwinPrefix`), every inductive
record of the prepared array is a `FrontBlock` (`Arena/DeclAndPinIndDec.lean`): an inductive with
the default capabilities (`installIndD` builds it from `indInfo cv {}`), any constructor, a
recursor whose rules are all `.plain` (`parseRuleD`).

* A line pushes at most one record, a `FrontDecl` one (`post_applyLineF`, the `FrontCI` strength
  of `FrontPreOK.lean`'s `post_applyLine`).
* The drivers keep "every record is `FrontDecl`" (`feedChunk`, `applyFinalLine`, `parseBytes`,
  `chunkStep`, `chunkFinish`, `parseChunks`); the prelude is `parseBytes` of its text.
* `preparePrelude` builds no record: every output record is a prelude record or a stream record
  (`frontOf` moves them, `hoistNatOpGround` permutes them).
-/

open ConRon.Arena ConRon.Arena.Frontend
open ConLeche.Frontend (RuleRec IndTypeRec IndCtorRec IndRecRec LineRec scanLineFwd)
open L.Front

namespace L.Checker

/-! ## The records' shape -/

/-- A record as the twin's parse pushes it: an inductive block of the front's shape. -/
def FrontDecl : IDeclaration → Prop
  | .indDecl b _ => L.Arena.FrontBlock b
  | _ => True

/-- Every record of an array has the front's shape. -/
def FrontDecls (ds : Array IDeclaration) : Prop := ∀ d ∈ ds.toList, FrontDecl d

theorem FrontDecls.empty : FrontDecls #[] := by intro d hd; simp at hd

theorem FrontDecls.push {ds : Array IDeclaration} {d : IDeclaration} (h : FrontDecls ds)
    (hd : FrontDecl d) : FrontDecls (ds.push d) := by
  intro x hx
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact h x hx
  · exact hd

/-- What a line's parse step leaves: the same records, or one `FrontDecl` record pushed. -/
def PushedOneF (st st' : StateD) : Prop :=
  st'.decls = st.decls ∨ ∃ d, st'.decls = st.decls.push d ∧ FrontDecl d

theorem PushedOneF.keep {st st' : StateD} (h : PushedOneF st st') (hs : FrontDecls st.decls) :
    FrontDecls st'.decls := by
  rcases h with h | ⟨d, h, hd⟩
  · rw [h]; exact hs
  · rw [h]; exact hs.push hd

/-! ## One line -/

theorem post_pushF (st : StateD) (d : IDeclaration) (hd : FrontDecl d) :
    L.Front.Post (do pure (Sum.inl (← pushDecl st d)) : AM (StateD ⊕ RecordVerdict))
      (fun x => ∀ st', x = .inl st' → PushedOneF st st') :=
  Post.bind (Q := fun s => s.decls = st.decls.push d) (Post.ret rfl) fun s hs =>
    Post.ret (by intro st' h; cases h; exact .inr ⟨d, hs, hd⟩)

theorem post_parseRuleD (st : StateD) (ru : RuleRec) :
    L.Front.Post (parseRuleD st ru) (fun r => r.fire = .plain) := by
  unfold ConRon.Arena.Frontend.parseRuleD
  exact Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ => Post.ret rfl

theorem post_installIndDF (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (nPd : Nat) :
    L.Front.Post (installIndD st tys cts rcs nPd)
      (fun s => ∃ d, s.decls = st.decls.push d ∧ FrontDecl d) := by
  sorry

/-- **A line pushes at most one record**, a `FrontDecl` one. -/
theorem post_applyLineF (st : StateD) (r : LineRec) :
    L.Front.Post (applyRecord st r) (fun x => ∀ st', x = .inl st' → PushedOneF st st') := by
  sorry

theorem applyLine_front {st st' : StateD} {r : LineRec} {a a' : AState}
    (h : applyRecord st r a = .ok (.inl st', a')) (hs : FrontDecls st.decls) :
    FrontDecls st'.decls :=
  (post_applyLineF st r a _ a' h st' rfl).keep hs

/-! ## The drivers -/

theorem feedChunk_front_le :
    ∀ (n : Nat) {s s' : AState} {sd sd' : StateD} {b : ByteArray} {i : USize}
      {lineNo lineNo' : Nat} {tail : USize},
      b.size - i.toNat ≤ n →
      feedChunk sd b i lineNo s = .ok (.ok (sd', lineNo', tail), s') →
      FrontDecls sd.decls → FrontDecls sd'.decls := by
  sorry

theorem feedChunk_front {s s' : AState} {sd sd' : StateD} {b : ByteArray} {i : USize}
    {lineNo lineNo' : Nat} {tail : USize}
    (hrun : feedChunk sd b i lineNo s = .ok (.ok (sd', lineNo', tail), s'))
    (hf : FrontDecls sd.decls) : FrontDecls sd'.decls :=
  feedChunk_front_le _ (Nat.le_refl _) hrun hf

theorem applyFinalLine_front {s s' : AState} {sd sd' : StateD} {b : ByteArray} {i : USize}
    {lineNo : Nat} (hrun : applyFinalLine sd b i lineNo s = .ok (.ok sd', s'))
    (hf : FrontDecls sd.decls) : FrontDecls sd'.decls := by
  sorry

theorem init_front {s s' : AState} {sd : StateD} (h : StateD.init s = .ok (sd, s')) :
    FrontDecls sd.decls := by
  rw [L.Front.init_decls h]; exact FrontDecls.empty

theorem parseBytes_front {s s' : AState} {b : ByteArray} {rc : ParseResultD}
    (hrun : parseBytes b s = .ok (.ok rc, s')) : FrontDecls rc.decls := by
  unfold parseBytes at hrun
  split at hrun
  · exact absurd (ConRon.Bridge.AM.pure_ok hrun).1 (by simp)
  · obtain ⟨sd, s₁, hinit, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
    obtain ⟨x, s₂, hfeed, hrest⟩ := ConRon.Bridge.AM.bind_ok hrest
    have hf0 := init_front hinit
    split at hrest
    · exact absurd (ConRon.Bridge.AM.pure_ok hrest).1 (by simp)
    · have hf1 := feedChunk_front hfeed hf0
      split at hrest
      · obtain ⟨y, s₃, hfin, hrest⟩ := ConRon.Bridge.AM.bind_ok hrest
        split at hrest
        · exact absurd (ConRon.Bridge.AM.pure_ok hrest).1 (by simp)
        · obtain ⟨hv, -⟩ := ConRon.Bridge.AM.pure_ok hrest
          cases hv
          exact applyFinalLine_front hfin hf1
      · obtain ⟨hv, -⟩ := ConRon.Bridge.AM.pure_ok hrest
        cases hv
        exact hf1

theorem chunkStep_front {s s' : AState} {sd sd' : StateD} {carry carry' buf0 : ByteArray}
    {lineNo lineNo' total total' : Nat}
    (hrun : chunkStep sd carry lineNo total buf0 s = .ok (.ok (sd', carry', lineNo', total'), s'))
    (hf : FrontDecls sd.decls) : FrontDecls sd'.decls := by
  unfold chunkStep at hrun
  split at hrun
  · exact absurd (ConRon.Bridge.AM.pure_ok hrun).1 (by simp)
  · obtain ⟨x, s₁, hfeed, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
    split at hrest
    · exact absurd (ConRon.Bridge.AM.pure_ok hrest).1 (by simp)
    · obtain ⟨hv, -⟩ := ConRon.Bridge.AM.pure_ok hrest
      cases hv
      exact feedChunk_front hfeed hf

theorem chunkFinish_front {s s' : AState} {sd : StateD} {carry : ByteArray} {lineNo : Nat}
    {rc : ParseResultD} (hrun : chunkFinish sd carry lineNo s = .ok (.ok rc, s'))
    (hf : FrontDecls sd.decls) : FrontDecls rc.decls := by
  unfold chunkFinish at hrun
  split at hrun
  · obtain ⟨hv, -⟩ := ConRon.Bridge.AM.pure_ok hrun
    cases hv; exact hf
  · obtain ⟨y, s₁, hfin, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
    split at hrest
    · exact absurd (ConRon.Bridge.AM.pure_ok hrest).1 (by simp)
    · obtain ⟨hv, -⟩ := ConRon.Bridge.AM.pure_ok hrest
      cases hv
      exact applyFinalLine_front hfin hf

theorem parseChunksGo_front :
    ∀ (cs : List ByteArray) {s s' : AState} {sd : StateD} {carry : ByteArray}
      {lineNo total : Nat} {rc : ParseResultD},
      parseChunksGo sd carry lineNo total cs s = .ok (.ok rc, s') →
      FrontDecls sd.decls → FrontDecls rc.decls := by
  intro cs
  induction cs with
  | nil =>
    intro s s' sd carry lineNo total rc hrun hf
    rw [parseChunksGo] at hrun
    exact chunkFinish_front hrun hf
  | cons c cs ih =>
    intro s s' sd carry lineNo total rc hrun hf
    rw [parseChunksGo] at hrun
    obtain ⟨x, s₁, hstep, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
    split at hrest
    · exact absurd (ConRon.Bridge.AM.pure_ok hrest).1 (by simp)
    · exact ih hrest (chunkStep_front hstep hf)

theorem parseChunks_front {s s' : AState} {chunks : List ByteArray} {rc : ParseResultD}
    (hrun : parseChunks chunks s = .ok (.ok rc, s')) : FrontDecls rc.decls := by
  unfold parseChunks at hrun
  obtain ⟨sd, s₁, hinit, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
  exact parseChunksGo_front chunks hrest (init_front hinit)

theorem builtinPreludeE_front {s s' : AState} {pre : PreludeIx}
    (hrun : builtinPreludeE s = .ok (.ok pre, s')) : FrontDecls pre.decls := by
  unfold builtinPreludeE at hrun
  obtain ⟨x, s₁, hparse, hrest⟩ := ConRon.Bridge.AM.bind_ok hrun
  split at hrest
  · exact absurd (ConRon.Bridge.AM.pure_ok hrest).1 (by simp)
  · obtain ⟨hv, -⟩ := ConRon.Bridge.AM.pure_ok hrest
    cases hv
    exact parseBytes_front hparse

/-! ## The preparation moves records -/

theorem pick_mem {n : NIdx} {ds : Array IDeclaration} :
    (∀ m, (pick n ds).1 = some m → m ∈ ds.toList) ∧
      ∀ d ∈ (pick n ds).2.toList, d ∈ ds.toList := by
  refine ⟨fun m hm => ?_, fun d hd => ?_⟩
  · simp only [pick] at hm
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm)
  · simp only [pick] at hd
    unfold Array.eraseIdxIfInBounds at hd
    split at hd
    · simp only [Array.toList_eraseIdx] at hd
      exact List.mem_of_mem_eraseIdx hd
    · exact hd

theorem post_mono {α : Type} {x : AM α} {P Q : α → Prop} (h : L.Front.Post x P)
    (hq : ∀ v, P v → Q v) : L.Front.Post x Q :=
  fun a r a' hr => hq r (h a r a' hr)

theorem post_frontOf :
    ∀ (ps : List IDeclaration) (acc ds : Array IDeclaration),
      L.Front.Post (frontOf acc ps ds) (fun r => ∀ d, d ∈ r.1.toList ∨ d ∈ r.2.toList →
        d ∈ acc.toList ∨ d ∈ ps ∨ d ∈ ds.toList) := by
  intro ps
  induction ps with
  | nil =>
    intro acc ds
    rw [frontOf]
    exact Post.ret fun d hd => by
      rcases hd with hd | hd
      · exact .inl hd
      · exact .inr (.inr hd)
  | cons p ps ih =>
    intro acc ds
    rw [frontOf]
    refine Post.bind (Post.any _) fun n _ => ?_
    obtain ⟨hm, hr⟩ := pick_mem (n := n) (ds := ds)
    rcases hpk : pick n ds with ⟨m', ds'⟩
    rw [hpk] at hm hr
    refine post_mono (ih _ _) fun r hr' d hd => ?_
    rcases hr' d hd with h | h | h
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact .inl h
      · cases m' with
        | none => simp
        | some m => simp only [Option.getD_some]; exact .inr (.inr (hm m rfl))
    · exact .inr (.inl (List.mem_cons_of_mem _ h))
    · exact .inr (.inr (hr d h))

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem post_hoistNatOpGround (ds : Array IDeclaration) :
    L.Front.Post (hoistNatOpGround ds) (fun r => ∀ d ∈ r.1.toList, d ∈ ds.toList) := by
  unfold hoistNatOpGround
  refine Post.bind (Post.any _) fun target _ => ?_
  split
  · exact Post.ret fun d hd => hd
  · refine Post.ret fun d hd => ?_
    simp only [applyHoist, reorder, ConRon.Bridge.Frontend.reorder_toList,
      List.nil_append, List.mem_filterMap] at hd
    obtain ⟨k, -, hk⟩ := hd
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk)
-/

theorem post_preparePrelude (pre : PreludeIx) (ds : Array IDeclaration) :
    L.Front.Post (preparePrelude pre ds)
      (fun out => ∀ d ∈ out.toList, d ∈ pre.decls.toList ∨ d ∈ ds.toList) := by
  sorry

/-! ## The prefix -/

/-- **The twin's prepared records have the front's shape**: every inductive block of the
prepared array is a `FrontBlock`. -/
theorem prefix_frontDecls {b : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List ConLeche.NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState}
    (h : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE) :
    ∀ blk nP, IDeclaration.indDecl blk nP ∈ ds.toList → L.Arena.FrontBlock blk := by
  obtain ⟨-, hB, hC, hD, -⟩ := h
  have hpre := builtinPreludeE_front hB
  have hrc := parseChunks_front hC
  intro blk nP hmem
  rcases post_preparePrelude pre rc.decls sC ds sD hD _ hmem with hm | hm
  · exact hpre _ hm
  · exact hrc _ hm

end L.Checker
