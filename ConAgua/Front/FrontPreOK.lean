module

public import ConAgua.Front.FrontPre
public import ConAgua.Checker.HoistWalkRef
import ConAgua.Front.IndInstallRefine
import ConRon.Bridge.Grind
import all ConAgua.Front.IndApply

@[expose] public section

/-!
# The frontend after the prelude, with the records' words (lane `pipeline`)

`FrontInvOK`, the driver's invariant (`FrontRunRef.lean`): `FrontInvP` (`FrontPre.lean`) and,
in addition, every record of `DECL` is `RecOK` (`Checker/HoistRefBase.lean`) and the twin's records
are walkable (`GoodDecl`). `front_init` establishes it (`initKW_inv_ok`) and every line keeps it
(`recOK_line`). The memory side of a line is `DGrow` (`FrontPreOK1.lean`, `FrontPreOK2.lean`); the
twin side is that a line pushes at most one record, and an inductive block of `indInfo`, `ctorInfo`
and `recInfo` constants (`applyLine_decls`). A pointer word of an inductive record decodes to one
of those, so it is not `0` (the truncated pool's word `0` decodes to an `axiomInfo`): `recOK_new`.
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open ConLeche.Frontend hiding StateD RecordVerdict applyLine parseBytes ParseResultD parseChunks
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-! ## The twin's records -/

/-- A block's constant as the twin's install builds it. -/
def GoodCI : IConstantInfo → Prop
  | .indInfo .. | .ctorInfo .. | .recInfo .. => True
  | _ => False

/-- A record as the twin's parse pushes it: an inductive block of `GoodCI` constants. -/
def GoodDecl : IDeclaration → Prop
  | .indDecl b _ => ∀ ci ∈ b, GoodCI ci
  | _ => True

/-- Every result of `x` satisfies `P`. -/
def Post {α : Type} (x : AM α) (P : α → Prop) : Prop :=
  ∀ a r a', x.run a = .ok (r, a') → P r

theorem Post.ret {α : Type} {v : α} {P : α → Prop} (h : P v) : Post (pure v : AM α) P := by
  intro a r a' hr
  simp only [StateT.run_pure] at hr
  cases hr
  exact h

theorem Post.any {α : Type} (x : AM α) : Post x (fun _ => True) := fun _ _ _ _ => trivial

theorem Post.bind {α β : Type} {x : AM α} {f : α → AM β} {Q : α → Prop} {P : β → Prop}
    (hx : Post x Q) (h : ∀ v, Q v → Post (f v) P) : Post (x >>= f) P := by
  intro a r a' hr
  rw [StateT.run_bind] at hr
  cases hxa : x.run a with
  | error e => rw [hxa] at hr; cases hr
  | ok p =>
    rw [hxa] at hr
    exact h p.1 (hx a p.1 p.2 hxa) p.2 r a' hr

theorem Post.mapM {γ α : Type} {f : γ → AM α} {Q : α → Prop} :
    ∀ (xs : List γ), (∀ x ∈ xs, Post (f x) Q) → Post (xs.mapM f) (fun ys => ∀ y ∈ ys, Q y)
  | [], _ => by rw [List.mapM_nil]; exact Post.ret (by simp)
  | x :: xs, h => by
    rw [List.mapM_cons]
    exact Post.bind (h x (by simp)) fun y hy =>
      Post.bind (Post.mapM xs (fun z hz => h z (by simp [hz]))) fun ys hys =>
        Post.ret (by intro z hz; rcases List.mem_cons.mp hz with rfl | hz; exact hy; exact hys z hz)

/-- A chain of binds ending in `pure` of a state with the same records. -/
macro "post_chain" : tactic => `(tactic| repeat' (first | exact Post.ret rfl |
  refine Post.bind (Post.any _) fun _ _ => ?_))

/-- What a line's parse step leaves: the same records, or one `GoodDecl` record pushed. -/
def PushedOne (st st' : StateD) : Prop :=
  st'.decls = st.decls ∨ ∃ d, st'.decls = st.decls.push d ∧ GoodDecl d

theorem post_push (st : StateD) (d : IDeclaration) (hd : GoodDecl d) :
    Post (do pure (Sum.inl (← pushDecl st d)) : AM (StateD ⊕ RecordVerdict))
      (fun x => ∀ st', x = .inl st' → PushedOne st st') :=
  Post.bind (Q := fun s => s.decls = st.decls.push d) (Post.ret rfl) fun s hs =>
    Post.ret (by intro st' h; cases h; exact .inr ⟨d, hs, hd⟩)

theorem post_installIndD (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (nPd : Nat) :
    Post (installIndD st tys cts rcs nPd) (fun s => ∃ d, s.decls = st.decls.push d ∧ GoodDecl d) := by
  unfold installIndD
  refine Post.bind (Post.mapM (Q := GoodCI) _ fun t _ =>
    Post.bind (Post.any _) fun _ _ => Post.ret trivial) fun types ht => ?_
  refine Post.bind (Post.mapM (Q := GoodCI) _ fun t _ =>
    Post.bind (Post.any _) fun _ _ => Post.ret trivial) fun ctors hc => ?_
  refine Post.bind (Post.mapM (Q := GoodCI) _ fun t _ =>
    Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ => Post.ret trivial)
    fun recs hr => ?_
  refine Post.ret ⟨_, rfl, ?_⟩
  intro ci hci
  simp only [List.mem_append] at hci
  rcases hci with (h | h) | h
  · exact ht ci h
  · exact hc ci h
  · exact hr ci h

/-- **A line pushes at most one record**, a `GoodDecl` one. -/
theorem post_applyLine (st : StateD) (r : LineRec) :
    Post (applyRecord st r) (fun x => ∀ st', x = .inl st' → PushedOne st st') := by
  sorry

theorem applyLine_decls {st st' : StateD} {r : LineRec} {a a' : AState}
    (h : (applyRecord st r).run a = .ok (.inl st', a')) : PushedOne st st' :=
  post_applyLine st r a _ a' h st' rfl

theorem init_decls {a a₁ : AState} {st₀ : StateD} (h : StateD.init.run a = .ok (st₀, a₁)) :
    st₀.decls = #[] :=
  (show Post StateD.init (fun s => s.decls = #[]) from by
    unfold ConRon.Arena.Frontend.StateD.init
    exact Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ => Post.ret rfl) a st₀ a₁ h

/-! ## `RecOK` across a line -/

/-- A record of kind `6` is an inductive block. -/
theorem kind6 {D P : Array Word} {x : Nat} {d : IDeclaration} (h : DeclAtF D P x d)
    (h6 : dw D x 0 = 6) : ∃ b nP, d = .indDecl b nP ∧ IndDeclAt D P x b nP := by
  sorry

theorem mapM_some_mem {γ α : Type} {f : γ → Option α} :
    ∀ (xs : List γ) (ys : List α), xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], _, _, x, hx => by simp at hx
  | x :: xs, ys, h, z, hz => by
    rw [List.mapM_cons] at h
    cases hfx : f x with
    | none => rw [hfx] at h; cases h
    | some y =>
      rw [hfx] at h
      cases hr : xs.mapM f with
      | none => rw [hr] at h; cases h
      | some ys' =>
        rw [hr] at h
        cases h
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨y, by simp, hfx⟩
        · obtain ⟨y', hy', e⟩ := mapM_some_mem xs ys' hr z hz
          exact ⟨y', by simp [hy'], e⟩

/-- A pointer of a decoded block: its slot is in the array, its constant in the block. -/
theorem decCIs_slot {a : Array Word} {off cnt : Nat}
    {bl : List IConstantInfo} (h : decCIs a off cnt = some bl) (j : Nat) (hj : j < cnt) :
    ∃ w ci, a[off + j]? = some w ∧ decCI (aread a) w.toNat = some ci ∧ ci ∈ bl := by
  obtain ⟨ci, hci, e⟩ := mapM_some_mem _ _ h j (List.mem_range.mpr hj)
  cases hw : a[off + j]? with
  | none => simp [L.Arena.nat?, hw] at e
  | some w => exact ⟨w, ci, rfl, by simpa [L.Arena.nat?, hw] using e, hci⟩

theorem trunc_size_le (P : Array Word) (t : Nat) : (trunc P t).size ≤ t + 1 := by
  simp [trunc]; omega

/-- The old records keep `RecOK` when their words and the pool up to its top stay. -/
theorem recOK_keep {D P D' P' : Array Word} {ds : Array IDeclaration} (hF : DeclsF D P ds)
    (hR : ∀ x < ds.size, L.Checker.RecOK D P x)
    (g1 : ∀ j, 0 < j → j < 1 + 8 * ds.size → D'[j]? = D[j]?)
    (g2 : ∀ j, 0 < j → j ≤ (P[0]?.getD 0).toNat → P'[j]? = P[j]?) :
    ∀ x < ds.size, L.Checker.RecOK D' P' x := by
  intro x hx
  have hw : ∀ k, k < 8 → dw D' x k = dw D x k := fun k hk => by
    simp only [dw]; rw [g1 _ (by omega) (by omega)]
  obtain ⟨r1, r2⟩ := hR x hx
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rw [hw 0 (by omega)] at h0
    rw [hw 1 (by omega), hw 4 (by omega), hw 5 (by omega)]
    exact r1 h0
  · rw [hw 0 (by omega)] at h0
    obtain ⟨r2a, r2b⟩ := r2 h0
    refine ⟨by rw [hw 2 (by omega)]; exact r2a, fun j hj => ?_⟩
    rw [hw 3 (by omega)] at hj
    rw [hw 2 (by omega)]
    obtain ⟨b, nP, -, -, -, t, ht, hdec⟩ := kind6 (hF.recs x hx) h0
    obtain ⟨w, ci, hwj, -, -⟩ := decCIs_slot hdec j hj
    have hlt : (dw D x 2).toNat + j < (trunc P t).size := by
      rcases Nat.lt_or_ge ((dw D x 2).toNat + j) (trunc P t).size with hc | hc
      · exact hc
      · rw [Array.getElem?_eq_none hc] at hwj; cases hwj
    have := trunc_size_le P t
    rw [g2 _ (by omega) (by omega)]
    exact r2b j hj

/-- A new record is `RecOK`. -/
theorem recOK_new {D P : Array Word} {ds : Array IDeclaration} (hF : DeclsF D P ds) (x : Nat)
    (hx : x < ds.size) (hG : GoodDecl ds[x]) (hN : NewOK D x) : L.Checker.RecOK D P x := by
  sorry

/-- **`RecOK` across a line.** -/
theorem recOK_line {D : Array IDeclaration} {m m' : Mem} {st st' : StateD}
    (hD : StateDR m (st.pre D)) (hD' : StateDR m' (st'.pre D)) (hg : DGrow m m')
    (hR : ∀ x < D.size + st.decls.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x)
    (hd : st'.decls = st.decls ∨ ∃ d, st'.decls = st.decls.push d ∧ GoodDecl d) :
    ∀ x < D.size + st'.decls.size, L.Checker.RecOK (m'.arr64 DECL) (m'.arr64 DLP) x := by
  have hF := hD.decls
  have hF' := hD'.decls
  simp only [StateD.pre_decls] at hF hF' hR ⊢
  have hc : dcnt m = D.size + st.decls.size := by
    have := hF.count; simp only [Array.size_append] at this; exact this
  have hc' : dcnt m' = D.size + st'.decls.size := by
    have := hF'.count; simp only [Array.size_append] at this; exact this
  have hk := recOK_keep hF (by simpa using hR) (fun j h1 h2 => hg.decl j h1 (by rw [hc]; simpa using h2))
    (fun j h1 h2 => hg.dlp j h1 h2)
  simp only [Array.size_append] at hk
  rcases hd with e | ⟨d, e, hgd⟩
  · rw [e]; exact hk
  · intro x hx
    rw [e, Array.size_push] at hx
    by_cases hx' : x < D.size + st.decls.size
    · exact hk x hx'
    have hxe : x = D.size + st.decls.size := by omega
    subst hxe
    refine recOK_new hF' _ (by simp [e]) ?_ (hg.new _ (by omega) (by rw [hc', e, Array.size_push]; omega))
    have hget : ∀ (h : D.size + st.decls.size < (D ++ st'.decls).size),
        (D ++ st'.decls)[D.size + st.decls.size] = d := by
      intro h; rw [Array.getElem_append_right (by omega)]; simp [e]
    rw [hget]; exact hgd

/-! ## The invariant -/

section pre
variable (D : Array IDeclaration)

/-- The driver's invariant after the prelude, with the records' words: `FrontInvP`, every record
`RecOK`, the twin's records `GoodDecl`. -/
def FrontInvOK (b : ByteArray) (m : Mem) (a : AState) (st : StateD) : Prop :=
  FrontInvP D b m a st ∧
    (∀ x < D.size + st.decls.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) ∧
    ∀ d ∈ st.decls, GoodDecl d

/-- **`front_init` leaves `DECL`, `DLP` alone.** -/
theorem initKW_dk (m m' : Mem) (h : initKW m = some m') : DK m m' := by
  unfold initKW at h
  split at h; cases h; rename_i m₂ hW
  split at h
  · cases h
    simp only [frontInitW] at hW
    cases h1 : putK NID 0 (nainternW m) with
    | none => rw [h1] at hW; simp [initK] at hW
    | some m₁ =>
      rw [h1, initK_some] at hW
      refine (DK.putK (.inl rfl) (fun w m₃ hI => ?_) h1).trans
        (DK.putK (.inr (.inl rfl)) (fun w m₃ hI => ?_) hW)
      · exact DK.ofFrame (consInternM_frame nanonCS_wf hI)
      · exact DK.ofFrame (consInternM_frame zeroCS_wf hI)
  · cases h

section refine
variable (b : ByteArray)

/-- `front_init`'s model, after the prelude, establishes the driver's invariant. -/
theorem initKW_inv_ok : ∀ (m m₁ : Mem) (a : AState),
    (m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m (StateD.blank.pre D) ∧
      ConRon.Bridge.StateOK a ∧ a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a ∧
      (∀ x < D.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) ∧ ModeOK m) → initKW m = some m₁ →
    ∃ st₀ a₁, StateD.init.run a = .ok (st₀, a₁) ∧ FrontInvOK D b m₁ a₁ st₀ := by
  intro m m₁ a ⟨hm, hA, hD, hok, hoff, hpins, hR, hmo⟩ hi
  have hk := initKW_dk m m₁ hi
  unfold initKW at hi
  split at hi; cases hi; rename_i m₂ hW
  split at hi
  · rename_i hk'
    cases hi
    obtain ⟨h1, h2, h3⟩ := frontInitW_refines_pre D m m₁ a hA hD hW
    have hr := AM.run_of_ok _ _ h1
    have he := init_decls hr
    refine ⟨AM.res ConRon.Arena.Frontend.StateD.init a, AM.st ConRon.Arena.Frontend.StateD.init a, hr,
      ⟨hk'.trans hm, h2, h3, TwinOK.init hok hoff hpins hr, frontInitW_mode m m₁ hW hmo⟩, ?_, ?_⟩
    · rw [he, hk.1, hk.2]; simpa using hR
    · rw [he]; simp
  · cases hi

end refine

end pre

end L.Front
