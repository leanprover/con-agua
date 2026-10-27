import ConAgua.Arena.PromotePi
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The expression interners `pi_*` under `ArenaD`

As `PromotePi.lean`, for the eleven expression constructors: the callee's own `_D`/`_ok`
lemma (`DerRel.lean`) at the cleared flags gives `ArenaD`, the model gives the persistent handle
word (`consInternM_pw`; through `mkK` for the `mk_*`), `PromoteTwin.lean` the twin's equation.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- **The bracket around an expression interning**: from the callee's facts at the cleared
flags and the twin's equation `heq`. -/
theorem pi_E {op opP : AM EIdx} {m m₁ : Mem} {a : AState} {r : Word} (hD : ArenaD m a)
    (hok : AM.ok op (onA false a)) (hD₁ : ArenaD m₁ (AM.st op (onA false a)))
    (hres : AM.res op (onA false a) = decE r) (hk : Keeps cp op)
    (heq : opP.run a = (op.run (onA false a)).map (fun r => (r.1, onA a.store.scratchOn r.2))) :
    ∃ a', opP.run a = .ok (decE r, a') ∧
      ArenaD (m₁.set64 CTL 1 (rdW (m.arr64 CTL) 1)) a' ∧ cp a' = cp a := by
  have hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn := hD.1.flag_eq
  have hrun := AM.run_of_ok op _ hok
  refine ⟨onA a.store.scratchOn (AM.st op (onA false a)), ?_, ?_, ?_⟩
  · rw [heq, hrun, hres]; rfl
  · have h2 := ArenaD.flag hD₁ (rdW (m.arr64 CTL) 1)
    rw [hfl] at h2; exact h2
  · exact (hk.run hrun : cp (AM.st op (onA false a)) = cp (onA false a))

/-- A `mk_*`'s result is its interning's, after the derived range: the word and the frame. -/
theorem mkK_pw {A : ArrId} (hA : A ≠ CTL) {c s d : Word} {x : Option (Word × Mem)} {m m' : Mem}
    {r : Word} {A₀ : List ArrId} {C₀ : List Word}
    (hx : ∀ r₁ m₁, x = some (r₁, m₁) → PW r₁ ∧ MemFrame A₀ C₀ m m₁)
    (h : mkK A c s d x = some (r, m')) : PW r ∧ MemFrame (A :: (tier1 A) :: A₀) C₀ m m' := by
  match x, hx, h with
  | some (r₁, m₁), hx, h =>
    rw [mkK_some] at h
    split at h
    · cases h
    · rename_i m₂ hP
      cases h
      obtain ⟨h1, h2⟩ := hx _ _ rfl
      exact ⟨h1, (h2.mono (fun b hb => by simp [hb]) (by simp)).trans
        ((derPutW_frame A hA _ _ _ _ _ _ hP).mono (by simp) (by simp))⟩

/-- `intern_lit_str`'s model refines `internE (.lit (.strVal s))` under `ArenaD`
(`DerRel.lean`'s `internLit_D` at the `strVal` arm). -/
theorem internLitStr_D (m : Mem) (a : AState) (hA : ArenaD m a) (o l r : Word)
    (hq : SliceOK m o l) (s : String) (hk : sliceL (vpool m) o.toNat l.toNat = strWords s)
    (hq0 : m.flag = 0 → o.toNat < 2 ^ 40) (m' : Mem) (hI : internWStr m o l = some (r, m')) :
    AM.ok (internE (.lit (.strVal s))) a ∧ ArenaD m' (AM.st (internE (.lit (.strVal s))) a) ∧
    AM.res (internE (.lit (.strVal s))) a = decE r := by
  obtain ⟨hR, hD⟩ := hA
  obtain ⟨hok, hX, hres⟩ := internStr_correct m a hR.lit o l hq s hk hq0 _ _ hI
  have hI₂ := hI
  have hfr := consInternM_frame litStrCS_wf hI₂
  have hcs := AM.proto_cases litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok
  have hR₁ := hR.lift_lit _ _ _ _ hX hfr
    (AM.st_proto litLens _ _ _ _ _ _ a (internE_lit_run _ a) hok)
  have hD₁ : DerR m' a := DerR.frameM _ _ m m' hfr (by simp [ConsSch.wset, litStrCS, litCSk, REC, SLOT]) a hD
  refine ⟨hok, ⟨hR₁, ?_⟩, hres⟩
  rcases hcs with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> rw [h]
  · exact hD₁
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨derT_push hD₁.lit.1 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩, hD₁.lit.2⟩, hD₁.app, hD₁.lam,
      hD₁.forallE, hD₁.letE, hD₁.proj⟩
  · exact ⟨hD₁.bvar, hD₁.fvar, hD₁.sort, hD₁.const,
      ⟨hD₁.lit.1, derT_push hD₁.lit.2 _ _ _ ⟨bvar_derLit _ _, fvar_derLit _ _, lp_derLit _ _⟩⟩, hD₁.app, hD₁.lam,
      hD₁.forallE, hD₁.letE, hD₁.proj⟩

section exprs
variable (p : Prog) (hp : PromoteProg p) (n : Nat)
include hp

omit hp in
/-- **The common shape of the `pi_*`**: from the callee's run at the cleared flag (`hc`: the
twin's facts, the persistent result word, the frame) and the twin's equation `heq`. -/
theorem pi_gen {g : FnName} {args : List Word} {op opP : AM EIdx} {A : List ArrId} {C : List Word}
    {m : Mem} {a : AState} (hD : ArenaD m a)
    (hc : ∀ rr m₁, callW p n g args (m.set64 CTL 1 0) = some (rr, m₁) →
      AM.ok op (onA false a) ∧ ArenaD m₁ (AM.st op (onA false a)) ∧
      AM.res op (onA false a) = decE (rr.headD 0) ∧ PW (rr.headD 0) ∧ MemFrame A C (m.set64 CTL 1 0) m₁)
    (hk : Keeps cp op)
    (heq : opP.run a = (op.run (onA false a)).map (fun r => (r.1, onA a.store.scratchOn r.2)))
    {r : Word} {m' : Mem} (h : piW p n g args m = some (r, m')) :
    ∃ a', opP.run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧ cp a' = cp a ∧
      MemFrame A C m m' := by
  have hcs := ctl_size hD.1
  rw [piW_eq _ _ _ _ _ hcs] at h
  cases hcall : callW p n g args (m.set64 CTL 1 0) with
  | none => rw [hcall] at h; cases h
  | some x =>
  obtain ⟨rr, m₁⟩ := x
  obtain ⟨hok, hD₁, hres, hpw, hf⟩ := hc rr m₁ hcall
  have hsz : 1 < (m₁.arr64 CTL).size := by rw [hf.2.2.1]; simpa [size_set64] using hcs
  rw [hcall, piK_some _ _ _ hsz] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', h1, h2, h3⟩ := pi_E hD hok hD₁ hres hk heq
  exact ⟨a', h1, h2, hpw, h3, frame_pi hcs hf⟩

omit hp in
theorem flag0 {m : Mem} {a : AState} (hD : ArenaD m a) : rdW ((m.set64 CTL 1 0).arr64 CTL) 1 = 0 := by
  rw [rdW_set64]; simp [ctl_size hD.1]

/-- **`pi_bvar` refines `internPersistentE (.bvar u.toNat)`.** -/
theorem piBVar_rel (m : Mem) (a : AState) (hD : ArenaD m a) (u : Word) (r : Word) (m' : Mem)
    (h : piW p n "intern_bvar" [u] m = some (r, m')) :
    ∃ a', (internPersistentE (.bvar u.toNat)).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [BREC, tier1 BREC, BSLOT, tier1 BSLOT] [22, 23] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (internBVar_spec p (hp.get "bvar_find") (hp.get "bvar_push")
      (hp.get "intern_bvar") n ⟨m.set64 CTL 1 0, Locals.init []⟩ u) hcall
    obtain ⟨hok, hD₁, hres⟩ := internBVar_D _ (onA false a) (hD.flag 0) u _ _ hI
    exact ⟨hok, hD₁, hres, consInternM_pw bvarCS_wf (hD.flag 0).1.bvar (flag0 hD) hI,
      (consInternM_frame bvarCS_wf hI).mono (by simp [ConsSch.wset, bvarCS]) (by simp [bvarCS])⟩)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact trivial)) h

/-- **`pi_fvar` refines `internPersistentE (.fvar u.toNat (decE ty))`.** -/
theorem piFVar_rel (m : Mem) (a : AState) (hD : ArenaD m a) (u ty : Word) (hty : PW ty) (r : Word) (m' : Mem)
    (h : piW p n "intern_fvar" [u, ty] m = some (r, m')) :
    ∃ a', (internPersistentE (.fvar u.toNat (decE ty))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [FVREC, tier1 FVREC, FVSLOT, tier1 FVSLOT, FVLP, tier1 FVLP] [26, 27] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (internFVar_spec p (hp.get "fvar_find") (hp.get "fvar_push")
      (hp.get "intern_fvar") n ⟨m.set64 CTL 1 0, Locals.init []⟩ u ty) hcall
    obtain ⟨hok, hD₁, hres⟩ := internFVar_D _ (onA false a) (hD.flag 0) u ty _ hty.1 _ hI
    exact ⟨hok, hD₁, hres, consInternM_pw fvarCS_wf (hD.flag 0).1.fvar (flag0 hD) hI,
      (fvinternW_frame (hI := hI)).mono (by simp) (by simp)⟩)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact hty.pers)) h

/-- **`pi_sort` refines `internPersistentE (.sort (decI u))`.** -/
theorem piSort_rel (m : Mem) (a : AState) (hD : ArenaD m a) (u : Word) (hu : PW u) (r : Word) (m' : Mem)
    (h : piW p n "intern_sort" [u] m = some (r, m')) :
    ∃ a', (internPersistentE (.sort (decI u))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [SOREC, tier1 SOREC, SOSLOT, tier1 SOSLOT, SOLP, tier1 SOLP] [16, 17] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (internSort_spec p (hp.get "sort_find") (hp.get "sort_push")
      (hp.get "intern_sort") n ⟨m.set64 CTL 1 0, Locals.init []⟩ u) hcall
    obtain ⟨hok, hD₁, hres⟩ := internSort_D _ (onA false a) (hD.flag 0) u _ hu.1 _ hI
    exact ⟨hok, hD₁, hres, consInternM_pw sortCS_wf (hD.flag 0).1.sort (flag0 hD) hI,
      (sointernW_frame (hI := hI)).mono (by simp) (by simp)⟩)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact hu.pers)) h

/-- **`pi_const` refines `internPersistentE (.const (decI (k := .name) x) (decI (k := .levels) us))`.** -/
theorem piConst_rel (m : Mem) (a : AState) (hD : ArenaD m a) (x us : Word) (hx : PW x) (hus : PW us) (r : Word) (m' : Mem)
    (h : piW p n "intern_const" [x, us] m = some (r, m')) :
    ∃ a', (internPersistentE (.const (decI (k := .name) x) (decI (k := .levels) us))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [CREC, tier1 CREC, CSLOT, tier1 CSLOT, CLP, tier1 CLP] [18, 19] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (internConst_spec p (hp.get "const_find") (hp.get "const_push")
      (hp.get "intern_const") n ⟨m.set64 CTL 1 0, Locals.init []⟩ x us) hcall
    obtain ⟨hok, hD₁, hres⟩ := internConst_D _ (onA false a) (hD.flag 0) x us _ hx.1 hus.1 _ hI
    exact ⟨hok, hD₁, hres, consInternM_pw constCS_wf (hD.flag 0).1.const (flag0 hD) hI,
      (ceinternW_frame (hI := hI)).mono (by simp) (by simp)⟩)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact ⟨hx.pers, hus.pers⟩)) h

/-- **`pi_app` refines `internPersistentE (.app (decE f) (decE x))`.** -/
theorem piApp_rel (m : Mem) (a : AState) (hD : ArenaD m a) (f x : Word) (hf : PW f) (hx : PW x) (r : Word) (m' : Mem)
    (h : piW p n "mk_app" [f, x] m = some (r, m')) :
    ∃ a', (internPersistentE (.app (decE f) (decE x))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [ADER, tier1 ADER, AREC, tier1 AREC, ASLOT, tier1 ASLOT] [4, 5] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (mkApp_spec p (hp.get "der_b") (hp.get "app_find") (hp.get "app_push")
      (hp.get "intern_app") (hp.get "mk_app") n ⟨m.set64 CTL 1 0, Locals.init []⟩ f x) hcall
    obtain ⟨hok, hD₁, hres⟩ := mkApp_ok _ (onA false a) (hD.flag 0) f x _ _ hI
    refine ⟨hok, hD₁, hres, ?_⟩
    unfold mkAppW at hI; split at hI; · cases hI
    exact mkK_pw (A₀ := [AREC, tier1 AREC, ASLOT, tier1 ASLOT]) (by decide) (fun _ _ hx =>
      ⟨consInternM_pw appCS_wf (hD.flag 0).1.app (flag0 hD) hx, (consInternM_frame appCS_wf hx).mono
        (by simp [ConsSch.wset, appCS]) (by simp [appCS])⟩) hI)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact ⟨hf.pers, hx.pers⟩)) h

/-- **`pi_lam` refines `internPersistentE (.lam (decE t) (decE b))`.** -/
theorem piLam_rel (m : Mem) (a : AState) (hD : ArenaD m a) (t b : Word) (ht : PW t) (hb : PW b) (r : Word) (m' : Mem)
    (h : piW p n "mk_lam" [t, b] m = some (r, m')) :
    ∃ a', (internPersistentE (.lam (decE t) (decE b))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [LADER, tier1 LADER, LAREC, tier1 LAREC, LASLOT, tier1 LASLOT] [28, 29] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (mkLam_spec p (hp.get "der_b") (hp.get "lam_find") (hp.get "lam_push")
      (hp.get "intern_lam") (hp.get "mk_lam") n ⟨m.set64 CTL 1 0, Locals.init []⟩ t b) hcall
    obtain ⟨hok, hD₁, hres⟩ := mkLam_ok _ (onA false a) (hD.flag 0) t b _ _ hI
    refine ⟨hok, hD₁, hres, ?_⟩
    unfold mkLamW at hI; split at hI; · cases hI
    exact mkK_pw (A₀ := [LAREC, tier1 LAREC, LASLOT, tier1 LASLOT]) (by decide) (fun _ _ hx =>
      ⟨consInternM_pw lamCS_wf (hD.flag 0).1.lam (flag0 hD) hx, (consInternM_frame lamCS_wf hx).mono
        (by simp [ConsSch.wset, lamCS]) (by simp [lamCS])⟩) hI)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact ⟨ht.pers, hb.pers⟩)) h

/-- **`pi_forall` refines `internPersistentE (.forallE (decE t) (decE b))`.** -/
theorem piForall_rel (m : Mem) (a : AState) (hD : ArenaD m a) (t b : Word) (ht : PW t) (hb : PW b) (r : Word) (m' : Mem)
    (h : piW p n "mk_forall" [t, b] m = some (r, m')) :
    ∃ a', (internPersistentE (.forallE (decE t) (decE b))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [FADER, tier1 FADER, FAREC, tier1 FAREC, FASLOT, tier1 FASLOT] [30, 31] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push")
      (hp.get "intern_forall") (hp.get "mk_forall") n ⟨m.set64 CTL 1 0, Locals.init []⟩ t b) hcall
    obtain ⟨hok, hD₁, hres⟩ := mkForall_ok _ (onA false a) (hD.flag 0) t b _ _ hI
    refine ⟨hok, hD₁, hres, ?_⟩
    unfold mkForallW at hI; split at hI; · cases hI
    exact mkK_pw (A₀ := [FAREC, tier1 FAREC, FASLOT, tier1 FASLOT]) (by decide) (fun _ _ hx =>
      ⟨consInternM_pw forallCS_wf (hD.flag 0).1.forallE (flag0 hD) hx, (consInternM_frame forallCS_wf hx).mono
        (by simp [ConsSch.wset, forallCS]) (by simp [forallCS])⟩) hI)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact ⟨ht.pers, hb.pers⟩)) h

/-- **`pi_let` refines `internPersistentE (.letE (decE t) (decE v) (decE b))`.** -/
theorem piLet_rel (m : Mem) (a : AState) (hD : ArenaD m a) (t v b : Word) (ht : PW t) (hv : PW v) (hb : PW b) (r : Word) (m' : Mem)
    (h : piW p n "mk_let" [t, v, b] m = some (r, m')) :
    ∃ a', (internPersistentE (.letE (decE t) (decE v) (decE b))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [LEDER, tier1 LEDER, LEREC, tier1 LEREC, LESLOT, tier1 LESLOT] [20, 21] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (mkLet_spec p (hp.get "der_b") (hp.get "letE_find") (hp.get "letE_push")
      (hp.get "intern_letE") (hp.get "mk_let") n ⟨m.set64 CTL 1 0, Locals.init []⟩ t v b) hcall
    obtain ⟨hok, hD₁, hres⟩ := mkLet_ok _ (onA false a) (hD.flag 0) t v b _ _ hI
    refine ⟨hok, hD₁, hres, ?_⟩
    unfold mkLetW at hI; split at hI; · cases hI
    exact mkK_pw (A₀ := [LEREC, tier1 LEREC, LESLOT, tier1 LESLOT]) (by decide) (fun _ _ hx =>
      ⟨consInternM_pw letCS_wf (hD.flag 0).1.letE (flag0 hD) hx, (consInternM_frame letCS_wf hx).mono
        (by simp [ConsSch.wset, letCS]) (by simp [letCS])⟩) hI)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact ⟨ht.pers, hv.pers, hb.pers⟩)) h

/-- **`pi_proj` refines `internPersistentE (.proj (decI x) i.toNat (decE e))`.** -/
theorem piProj_rel (m : Mem) (a : AState) (hD : ArenaD m a) (x i e : Word) (hx : PW x) (he : PW e) (r : Word) (m' : Mem)
    (h : piW p n "mk_proj" [x, i, e] m = some (r, m')) :
    ∃ a', (internPersistentE (.proj (decI x) i.toNat (decE e))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧
      cp a' = cp a ∧ MemFrame [PJDER, tier1 PJDER, PJREC, tier1 PJREC, PJSLOT, tier1 PJSLOT] [32, 33] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (mkProj_spec p (hp.get "der_b") (hp.get "proj_find") (hp.get "proj_push")
      (hp.get "intern_proj") (hp.get "mk_proj") n ⟨m.set64 CTL 1 0, Locals.init []⟩ x i e) hcall
    obtain ⟨hok, hD₁, hres⟩ := mkProj_ok _ (onA false a) (hD.flag 0) x i e _ _ hI
    refine ⟨hok, hD₁, hres, ?_⟩
    unfold mkProjW at hI; split at hI; · cases hI
    exact mkK_pw (A₀ := [PJREC, tier1 PJREC, PJSLOT, tier1 PJSLOT]) (by decide) (fun _ _ hx =>
      ⟨consInternM_pw projCS_wf (hD.flag 0).1.proj (flag0 hD) hx, (consInternM_frame projCS_wf hx).mono
        (by simp [ConsSch.wset, projCS]) (by simp [projCS])⟩) hI)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact ⟨hx.pers, he.pers⟩)) h

omit hp in
/-- The pool slice at the cleared flag. -/
theorem slice0 {m : Mem} {o l : Word} (hsl : SliceOK m o l) :
    (m.set64 CTL 1 0).arr64 POOL = m.arr64 POOL ∧ SliceOK (m.set64 CTL 1 0) o l := by
  have htop' : (m.set64 CTL 1 0).top = m.top := by simp only [top_rdW, rdW_set64]; simp
  exact ⟨Mem.arr64_set64_ne _ _ _ _ _ (by decide),
    by simp only [SliceOK, htop', Mem.ptop0_set64_ne m CTL 1 0 (by decide)] at hsl ⊢; exact hsl⟩

/-- **`pi_lit` refines `internPersistentE (.lit (.natVal _))`**, the number the pool slice
holds. -/
theorem piLit_rel0 (m : Mem) (a : AState) (hD : ArenaD m a) (o l : Word) (hsl : SliceOK m o l)
    (ho : o.toNat < 2 ^ 40) (hn : Norm (vpool m) o.toNat l.toNat) (r : Word) (m' : Mem)
    (h : piW p n "intern_lit" [o, l] m = some (r, m')) :
    ∃ a', (internPersistentE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))).run a =
      .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧ cp a' = cp a ∧ MemFrame [REC, tier1 REC, SLOT, tier1 SLOT] [2, 3] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    have ⟨_, _, hps, htop⟩ := (hD.flag 0).1.lit.1
    obtain ⟨hpool, hsl₀⟩ := slice0 hsl
    have hpoolv := vpool_congr hpool (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (internLit_spec p (hp.get "lit_hash") (hp.get "limbs_eq") (hp.get "lit_match")
      (hp.get "lit_find") (hp.get "lit_push") (hp.get "intern_lit") n ⟨m.set64 CTL 1 0, Locals.init []⟩ o l
      (by dsimp only; omega) (by simp only [SliceOK] at hsl₀; dsimp only; omega)) hcall
    obtain ⟨hok, hD₁, hres⟩ := internLit_D _ (onA false a) (hD.flag 0) o l _ hsl₀ (by rw [hpoolv]; exact hn)
      (fun _ => ho) _ hI
    rw [hpoolv] at hok hD₁ hres
    exact ⟨hok, hD₁, hres, consInternM_pw litCS_wf (hD.flag 0).1.lit.2 (flag0 hD) hI,
      (consInternM_frame litCS_wf hI).mono (by simp [ConsSch.wset, litCS, litCSk]) (by simp [litCS, litCSk])⟩)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact trivial)) h

/-- **`pi_lit_str` refines `internPersistentE (.lit (.strVal s))`**, `s` the string the pool
slice holds. -/
theorem piLitStr_rel0 (m : Mem) (a : AState) (hD : ArenaD m a) (o l : Word) (hsl : SliceOK m o l)
    (ho : o.toNat < 2 ^ 40) (s : String) (hk : sliceL (vpool m) o.toNat l.toNat = strWords s) (r : Word) (m' : Mem)
    (h : piW p n "intern_lit_str" [o, l] m = some (r, m')) :
    ∃ a', (internPersistentE (.lit (.strVal s))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧
      PW r ∧ cp a' = cp a ∧ MemFrame [REC, tier1 REC, SLOT, tier1 SLOT] [2, 3] m m' :=
  pi_gen p n hD (fun _ _ hcall => by
    have ⟨_, _, hps, htop⟩ := (hD.flag 0).1.lit.1
    obtain ⟨hpool, hsl₀⟩ := slice0 hsl
    have hpoolv := vpool_congr hpool (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
    obtain ⟨s', rfl, -, hI⟩ := callW_triple (internLitStr_spec p (hp.get "lit_hash") (hp.get "limbs_eq")
      (hp.get "lit_match_str") (hp.get "lit_find_str") (hp.get "lit_push_str") (hp.get "intern_lit_str") n
      ⟨m.set64 CTL 1 0, Locals.init []⟩ o l
      (by dsimp only; omega) (by simp only [SliceOK] at hsl₀; dsimp only; omega)) hcall
    obtain ⟨hok, hD₁, hres⟩ := internLitStr_D _ (onA false a) (hD.flag 0) o l _ hsl₀ s
      (by rw [hpoolv]; exact hk) (fun _ => ho) _ hI
    exact ⟨hok, hD₁, hres, consInternM_pw litStrCS_wf (litR_str.mp (hD.flag 0).1.lit.2) (flag0 hD) hI,
      (consInternM_frame litStrCS_wf hI).mono (by simp [ConsSch.wset, litStrCS, litCSk])
        (by simp [litStrCS, litCSk])⟩)
    (keeps_internE _) (internPersistentE_eq _ a hD.1.flagsEq (by exact trivial)) h

/-- **`pi_lit` refines `internPersistentE (.lit (.natVal _))`**, the number the pool slice
holds; a tier-1 slice is first copied to tier 0 (lane tierpool). -/
theorem piLit_rel (m : Mem) (a : AState) (hD : ArenaD m a) (o l : Word) (hsl : SliceOK m o l)
    (hn : Norm (vpool m) o.toNat l.toNat) (r : Word) (m' : Mem)
    (h : pcW p n "intern_lit" [] o l m = some (r, m')) :
    ∃ a', (internPersistentE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))).run a =
      .ok (decE r, a') ∧ ArenaD m' a' ∧ PW r ∧ cp a' = cp a ∧
      MemFrame [POOL, PT0, REC, tier1 REC, SLOT, tier1 SLOT] [2, 3] m m' ∧ SlKeep m m' := by
  obtain ⟨m₁, o₁, h₁, hD₁, hs₁, ho₁, hf₁, -, hv, hk₁⟩ := pc_cases hD hsl h
  have hpv : pv (vpool m₁) o₁.toNat l.toNat = pv (vpool m) o.toNat l.toNat := pv_congr _ _ _ _ _ hv
  obtain ⟨a', e1, e2, e3, e4, e5⟩ := piLit_rel0 p hp n m₁ a hD₁ o₁ l hs₁ ho₁
    (fun hl => by rw [hv _ (by omega)]; exact hn hl) r m' h₁
  rw [hpv] at e1
  exact ⟨a', e1, e2, e3, e4, (hf₁.mono (by simp) (by simp)).trans (e5.mono (by simp) (by simp)),
    hk₁.trans (SlKeep.of_frame e5 (by decide) (by decide))⟩

/-- **`pi_lit_str` refines `internPersistentE (.lit (.strVal s))`**; a tier-1 slice is first
copied to tier 0 (lane tierpool). -/
theorem piLitStr_rel (m : Mem) (a : AState) (hD : ArenaD m a) (o l : Word) (hsl : SliceOK m o l)
    (s : String) (hk : sliceL (vpool m) o.toNat l.toNat = strWords s) (r : Word) (m' : Mem)
    (h : pcW p n "intern_lit_str" [] o l m = some (r, m')) :
    ∃ a', (internPersistentE (.lit (.strVal s))).run a = .ok (decE r, a') ∧ ArenaD m' a' ∧
      PW r ∧ cp a' = cp a ∧ MemFrame [POOL, PT0, REC, tier1 REC, SLOT, tier1 SLOT] [2, 3] m m' ∧
      SlKeep m m' := by
  obtain ⟨m₁, o₁, h₁, hD₁, hs₁, ho₁, hf₁, -, hv, hk₁⟩ := pc_cases hD hsl h
  obtain ⟨a', e1, e2, e3, e4, e5⟩ := piLitStr_rel0 p hp n m₁ a hD₁ o₁ l hs₁ ho₁ s
    (by rw [← hk]; exact (sliceL_eq_iff _ _ _ _ _).mpr hv) r m' h₁
  exact ⟨a', e1, e2, e3, e4, (hf₁.mono (by simp) (by simp)).trans (e5.mono (by simp) (by simp)),
    hk₁.trans (SlKeep.of_frame e5 (by decide) (by decide))⟩

end exprs

end L.Arena
