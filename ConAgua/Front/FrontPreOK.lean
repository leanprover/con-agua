import ConAgua.Front.FrontPreOK3
import ConAgua.Front.FrontPre
import ConAgua.Checker.HoistWalkRef
import ConAgua.Checker.FrontProg

/-!
# The frontend after the prelude, with the records' words (lane `pipeline`)

`frontAll_refines_pre_ok`: `frontAll_refines_pre` (`FrontPre.lean`) where, in addition, every record
of `DECL` before the run is `RecOK` (`Checker/HoistRefBase.lean`); then every record after it is.
The run is `runI_refines` with the stronger invariant
`FrontInvOK`. The memory side of a line is `DGrow` (`FrontPreOK1.lean`‥`FrontPreOK3.lean`); the
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
    Post (applyLine st r) (fun x => ∀ st', x = .inl st' → PushedOne st st') := by
  cases r with
  | expr i e =>
    refine Post.bind (Q := fun s => s.decls = st.decls) ?_ fun s hs =>
      Post.ret (by intro st' h; cases h; exact .inl hs)
    unfold ConRon.Arena.Frontend.parseExprEntryD
    refine Post.bind (Post.any _) fun _ _ => ?_
    cases e <;> dsimp only <;> post_chain
  | name i n =>
    refine Post.bind (Q := fun s => s.decls = st.decls) ?_ fun s hs =>
      Post.ret (by intro st' h; cases h; exact .inl hs)
    cases n <;> unfold ConRon.Arena.Frontend.parseNameEntryD <;>
      exact Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ =>
        Post.bind (Post.any _) fun _ _ => Post.ret rfl
  | level i l =>
    refine Post.bind (Q := fun s => s.decls = st.decls) ?_ fun s hs =>
      Post.ret (by intro st' h; cases h; exact .inl hs)
    unfold ConRon.Arena.Frontend.parseLevelEntryD
    refine Post.bind (Post.any _) fun _ _ => ?_
    cases l <;> dsimp only <;> post_chain
  | header => exact Post.ret (by intro st' h; cases h; exact .inl rfl)
  | blank => exact Post.ret (by intro st' h; cases h; exact .inl rfl)
  | decl d =>
    simp only [ConRon.Arena.Frontend.applyLine, ConRon.Arena.Frontend.applyDeclD]
    cases d with
    | ax cv u =>
      unfold ConRon.Arena.Frontend.processLineCoreD
      refine Post.bind (Post.any _) fun cvp _ => ?_
      split
      · exact Post.ret (by intro st' h; cases h)
      · exact post_push st _ (by simp [GoodDecl])
    | defn cv v hints safety =>
      unfold ConRon.Arena.Frontend.processLineCoreD
      refine Post.bind (Post.any _) fun cvp _ => ?_
      split
      · exact Post.bind (Post.any _) fun _ _ => post_push st _ (by simp [GoodDecl])
      · exact Post.ret (by intro st' h; cases h)
    | thm cv v =>
      unfold ConRon.Arena.Frontend.processLineCoreD
      exact Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ => post_push st _ (by simp [GoodDecl])
    | opaq cv v u =>
      unfold ConRon.Arena.Frontend.processLineCoreD
      refine Post.bind (Post.any _) fun cvp _ => ?_
      split
      · exact Post.ret (by intro st' h; cases h)
      · exact Post.bind (Post.any _) fun _ _ => post_push st _ (by simp [GoodDecl])
    | quot cv k =>
      unfold ConRon.Arena.Frontend.processLineCoreD
      refine Post.bind (Post.any _) fun cvp _ => ?_
      dsimp only
      split <;> exact Post.bind (Post.any _) fun qk _ => post_push st _ (by simp [GoodDecl])
    | ind tys cts rcs =>
      unfold ConRon.Arena.Frontend.processLineCoreD
      refine Post.bind (Post.any _) fun x _ => ?_
      split
      · exact Post.ret (by intro st' h; cases h)
      · exact Post.bind (post_installIndD st _ _ _ _) fun s hs =>
          Post.ret (by intro st' h; cases h; exact .inr hs)

theorem applyLine_decls {st st' : StateD} {r : LineRec} {a a' : AState}
    (h : (applyLine st r).run a = .ok (.inl st', a')) : PushedOne st st' :=
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
  cases d with
  | indDecl b nP => exact ⟨b, nP, rfl, h⟩
  | axiomDecl _ => simp only [DeclAtF, DeclAt] at h; rw [h.1] at h6; cases h6
  | defnDecl _ _ _ => simp only [DeclAtF, DeclAt] at h; rw [h.1] at h6; cases h6
  | thmDecl _ _ => simp only [DeclAtF, DeclAt] at h; rw [h.1] at h6; cases h6
  | opaqueDecl _ _ => simp only [DeclAtF, DeclAt] at h; rw [h.1] at h6; cases h6
  | quotDecl _ _ => simp only [DeclAtF, DeclAt] at h; rw [h.1] at h6; cases h6
  | basisDecl _ => simp [DeclAtF, DeclAt] at h

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
theorem decCIs_slot {a : Array Word} {dn : NIdx → Option ConLeche.Name} {off cnt : Nat}
    {bl : List IConstantInfo} (h : decCIs a dn off cnt = some bl) (j : Nat) (hj : j < cnt) :
    ∃ w ci, a[off + j]? = some w ∧ decCI a dn w.toNat = some ci ∧ ci ∈ bl := by
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
  refine ⟨hN.1, fun h0 => ?_⟩
  have h2 := hN.2 h0
  have h2' : (dw D x 2).toNat ≠ 0 := fun e => h2 (UInt64.toNat_inj.mp (by simpa using e))
  refine ⟨h2', fun j hj => ?_⟩
  obtain ⟨b, nP, hd, -, -, t, ht, hdec⟩ := kind6 (hF.recs x hx) h0
  rw [hd] at hG
  obtain ⟨w, ci, hwj, hci, hmem⟩ := decCIs_slot hdec j hj
  have hlt : (dw D x 2).toNat + j < (trunc P t).size := by
    rcases Nat.lt_or_ge ((dw D x 2).toNat + j) (trunc P t).size with hc | hc
    · exact hc
    · rw [Array.getElem?_eq_none hc] at hwj; cases hwj
  have hts := trunc_size_le P t
  have hpt := hF.ptop
  rw [← L.Front.Ind.trunc_get P t _ (by omega) (by omega) (by omega), hwj]
  intro hw0
  simp only [Option.getD_some] at hw0
  subst hw0
  have h00 : (trunc P t)[0]? = some 0 := by
    simp only [trunc, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp only [Array.size_extract, Array.getElem?_extract]
    have : 0 < min (t + 1) P.size - 0 := by omega
    simp only [this, ↓reduceIte]
  simp only [UInt64.toNat_zero, L.Arena.decCI, L.Arena.nat?, h00, Option.map_some,
    UInt64.toNat_zero, Option.bind_eq_bind, Option.bind_some] at hci
  have := hG ci hmem
  revert hci this
  cases L.Arena.decCV (trunc P t) (0 + 1) <;> intro hci <;> simp at hci
  subst hci
  simp [GoodCI]

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

section refine
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem lineKW_step_ok (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (i : USize) (ok nx : Word) (st : StateD)
    (a : AState) (hI : FrontInvOK D b m a st) (hi : i < b.usize)
    (h : lineKW p b.data m i.toUInt64 = some (ok, nx, m'))
    (hok : ok ≠ 0) : LineStepI (FrontInvOK D b) b i nx st a m' := by
  obtain ⟨r', q, st₀, h1, h2, h3, h4, hInv⟩ :=
    lineKW_step_pre D b h64 hsize p hFI hAI hII hXI m m' i ok nx st a hI.1 hi h hok
  have hg := lineKW_grow b h64 hsize p hFI hAI hII hXI m m' hI.1.1 i a (st.pre D) hI.1.2.1
    hI.1.2.2.1 hI.1.2.2.2.1.1 ok nx h
  have hrun := AM.run_of_ok _ _ h3
  rw [h4] at hrun
  have hd := applyLine_decls hrun
  refine ⟨r', q, st₀, h1, h2, h3, h4, hInv, recOK_line hI.1.2.2.1 hInv.2.2.1 hg hI.2.1 hd, ?_⟩
  rcases hd with e | ⟨d, e, hgd⟩
  · rw [e]; exact hI.2.2
  · rw [e]
    intro d' hd'
    rcases Array.mem_push.mp hd' with h' | h'
    · exact hI.2.2 d' h'
    · rw [h']; exact hgd

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


/-- **The driver's model refines `parseBytes`, after the prelude, with the records' words.** -/
theorem frontRunW_refines_pre_ok (p : Prog) (hFI : L.Front.Ind.IndFieldLookups p)
    (hAI : L.Front.Ind.IndApplyLookups p) (hII : L.Front.Ind.IndInstallLookups p)
    (hXI : L.Front.Ind.IndLineLookups p) (m m' : Mem) (a₀ : AState) (hm : m.arr8 IN = b.data)
    (hA : ArenaD m a₀) (hD : StateDR m (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) (hmo : ModeOK m)
    (h : runI (lineKW p b.data) b.size (initKW m) = some (0, m')) :
    ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧ FrontInvOK D b m' a' st' :=
  runI_refines (FrontInvOK D b) b h64 hsize (lineKW p b.data)
    (lineKW_step_ok D b h64 hsize p hFI hAI hII hXI)
    (fun m a => m.arr8 IN = b.data ∧ ArenaD m a ∧ StateDR m (StateD.blank.pre D) ∧
      ConRon.Bridge.StateOK a ∧ a.store.scratchOn = false ∧ ConRon.Bridge.PinsOK a ∧
      (∀ x < D.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) ∧ ModeOK m) initKW
    (initKW_inv_ok D b h64 hsize) m m' a₀ ⟨hm, hA, hD, hok, hoff, hpins, hR, hmo⟩ h

end refine

/-- **Bytes → stores after the prelude, with the records' words**: `frontAll_refines_pre`, and
when every record of `DECL` before is `RecOK`, so is every record after; the twin's records are
walkable. -/
theorem frontAll_refines_pre_ok (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, L.Checker.RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke frontAllProg (exec frontAllProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st' ∧ ModeOK s'.mem ∧
      (∀ x < D.size + st'.decls.size, L.Checker.RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun h0
  have hW := M.of_run (P := fun s => s = s₀) hs hrun
    (frontRun_specI frontAllProg (lineKW frontAllProg b.data) b.data
      (fun m => ∃ a st, FrontInvOK D b m a st)
      (fun n s₁ i hm hI hi => frontLineK_spec frontAllProg frontAllProg_scan frontAllProg_front rfl
        rfl rfl rfl rfl rfl rfl frontAllProg_expr rfl frontAllProg_dfields frontAllProg_decl rfl
        b.data hsize _
        (fun m ⟨_, _, hI⟩ => ⟨hI.1.2.1.1.lit.1.2.2.1, hI.1.2.1.1.lit.1.2.2.2.1⟩)
        (inv_step frontAllProg (FrontInvOK D b) b h64 hsize
          (fun m m' i ok nx st a hI hi h hok => lineKW_step_ok D b h64 hsize frontAllProg
            frontAllProg_indFields frontAllProg_indApply frontAllProg_indInstall frontAllProg_indLine
            m m' i ok nx st a hI hi h hok)) n s₁ i hm hI hi)
      initKW s₀.mem (fun n s₁ hs₁ => initK_inv frontAllProg frontAllProg_front frontAllProg_expr rfl
        (FrontInvOK D b) _ (initKW_inv_ok D b h64 hsize) s₀ a₀ ⟨hm, hA, hD, hok, hoff, hpins, hR, hmode⟩
        n s₁ hs₁) rfl n s₀ hm rfl)
  rw [h0] at hW
  obtain ⟨st', a', h1, ⟨-, h2, h3, h4, hM⟩, h5, -⟩ :=
    frontRunW_refines_pre_ok D b h64 hsize frontAllProg frontAllProg_indFields frontAllProg_indApply
      frontAllProg_indInstall frontAllProg_indLine s₀.mem s'.mem a₀ hm hA hD hok hoff hpins hR hmode hW
  exact ⟨st', a', h1, h2, h3, h4, hM, h5⟩

/-- **The same at the checker's program** (`checkerProg_front_run`). -/
theorem frontRunOK_checker (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 63) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b.data)
    (hpool : (s₀.mem.arr64 POOL).size < 2 ^ 63) (a₀ : AState) (hA : ArenaD s₀.mem a₀)
    (hD : StateDR s₀.mem (StateD.blank.pre D)) (hok : ConRon.Bridge.StateOK a₀)
    (hoff : a₀.store.scratchOn = false) (hpins : ConRon.Bridge.PinsOK a₀)
    (hR : ∀ x < D.size, L.Checker.RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x) (hmode : ModeOK s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke L.Checker.checkerProg (exec L.Checker.checkerProg n) "front_run" []
    ⦃fun r s' => r.headD 0 = 0 → ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧
      ArenaD s'.mem a' ∧ StateDR s'.mem (st'.pre D) ∧ TwinOK a' st' ∧ ModeOK s'.mem ∧
      (∀ x < D.size + st'.decls.size, L.Checker.RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x); ⊤⦄ := by
  rw [L.Checker.checkerProg_front_run n]
  exact frontAll_refines_pre_ok D b h64 hsize n s₀ hm hpool a₀ hA hD hok hoff hpins hR hmode

end pre

end L.Front
