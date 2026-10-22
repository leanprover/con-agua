import ConAgua.Arena.InstLPWalkRef

/-!
# The `instLP` walk refines `instLPGo`: the arms `fvar`, `proj`, `letE`

Each arm is the memo probe and write around a body (`ilwArmT`, `ilw_arm`): the children (the walk
at the arm's fuel) and the rebuild.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem instLPArmApp_eq (ks : List Name) (vs : List Level) (fuel : Nat) (h f a : EIdx) :
    instLPArmApp ks vs fuel h f a = ilwArmT h (do
      let t ← instLPGo ks vs fuel f; let b ← instLPGo ks vs fuel a
      ilwRbT (t == f && b == a) h (internE (.app t b))) := by
  rw [instLPArmApp]; unfold ilwArmT; congr 1; funext x; cases x <;> simp only [bind_assoc] <;> rfl
theorem instLPArmLam_eq (ks : List Name) (vs : List Level) (fuel : Nat) (h f a : EIdx) :
    instLPArmLam ks vs fuel h f a = ilwArmT h (do
      let t ← instLPGo ks vs fuel f; let b ← instLPGo ks vs fuel a
      ilwRbT (t == f && b == a) h (internE (.lam t b))) := by
  rw [instLPArmLam]; unfold ilwArmT; congr 1; funext x; cases x <;> simp only [bind_assoc] <;> rfl
theorem instLPArmForallE_eq (ks : List Name) (vs : List Level) (fuel : Nat) (h f a : EIdx) :
    instLPArmForallE ks vs fuel h f a = ilwArmT h (do
      let t ← instLPGo ks vs fuel f; let b ← instLPGo ks vs fuel a
      ilwRbT (t == f && b == a) h (internE (.forallE t b))) := by
  rw [instLPArmForallE]; unfold ilwArmT; congr 1; funext x; cases x <;> simp only [bind_assoc] <;> rfl
theorem instLPArmFVar_eq (ks : List Name) (vs : List Level) (fuel : Nat) (h : EIdx) (i : Nat) (ty : EIdx) :
    instLPArmFVar ks vs fuel h i ty =
      ilwArmT h (do let t ← instLPGo ks vs fuel ty; ilwRbT (t == ty) h (internE (.fvar i t))) := by
  rw [instLPArmFVar]; unfold ilwArmT; congr 1; funext x; cases x <;> simp only [bind_assoc] <;> rfl
theorem instLPArmProj_eq (ks : List Name) (vs : List Level) (fuel : Nat) (h : EIdx) (n : NIdx) (i : Nat)
    (sub : EIdx) :
    instLPArmProj ks vs fuel h n i sub =
      ilwArmT h (do let u ← instLPGo ks vs fuel sub; ilwRbT (u == sub) h (internE (.proj n i u))) := by
  rw [instLPArmProj]; unfold ilwArmT; congr 1; funext x; cases x <;> simp only [bind_assoc] <;> rfl
theorem instLPArmLet_eq (ks : List Name) (vs : List Level) (fuel : Nat) (h ty val body : EIdx) :
    instLPArmLet ks vs fuel h ty val body =
      ilwArmT h (do
        let t ← instLPGo ks vs fuel ty
        let w ← instLPGo ks vs fuel val
        let b ← instLPGo ks vs fuel body
        ilwRbT (t == ty && w == val && b == body) h (internE (.letE t w b))) := by
  rw [instLPArmLet]; unfold ilwArmT; congr 1; funext x; cases x <;> simp only [bind_assoc] <;> rfl

section arms
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {eb : Word}

section armsP
variable {p : Prog} {n : Nat} (hp : ILWMkProg p) (ih : ILWGoOK p n)
include hp ih

/-- **`lp_fvar` refines `instLPArmFVar`.** -/
theorem ilw_fvarArm {m m' : Mem} {a : AState} {M : ModeMaps} {h ko kc vo vc fu r : Word}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hE : ILWEnv m a ko kc vo vc ks us vs) (hh : HW h)
    (hty : HW (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)))
    (hW : ilwFVarW p n m h ko kc vo vc fu = some (r, m')) :
    ILWStep (instLPArmFVar ks vs fu.toNat (decE h) (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2)).toNat
      (decE (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1)))) a dn m m' vis fe M eb r := by
  rw [instLPArmFVar_eq]
  unfold ilwFVarW at hW
  generalize rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) = iw at hW ⊢
  generalize rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2 + 1) = tw at hty hW ⊢
  refine ilw_arm hS hM hh (Y := match callW p n "lp_go" [tw, ko, kc, vo, vc, fu] m with
      | none => none
      | some (x, m₁) => if x.headD 0 = tw then some (h, m₁) else ilwChk (callW p n "intern_fvar" [iw, x.headD 0] m₁))
    (by rw [← hW]; congr 1; cases callW p n "lp_go" [tw, ko, kc, vo, vc, fu] m <;> rfl) ?_
  intro r₃ m₃ _ hY
  cases h1 : callW p n "lp_go" [tw, ko, kc, vo, vc, fu] m with
  | none => rw [h1] at hY; simp at hY
  | some q =>
  obtain ⟨xs, m₁⟩ := q
  rw [h1] at hY; dsimp only at hY
  refine ILWStep.bind (ih m m₁ a dn vis fe M eb tw ko kc vo vc fu ks us vs xs hS hM hE hty h1) ?_
  intro a₁ M₁ _ hS₁ hM₁ _ _ hx
  exact ilw_rebuild (c := decE (xs.headD 0) == decE tw)
    (Y := if xs.headD 0 = tw then some (h, m₁) else ilwChk (callW p n "intern_fvar" [iw, xs.headD 0] m₁))
    (Yn := callW p n "intern_fvar" [iw, xs.headD 0] m₁) hS₁ hM₁ hh (by rw [ilw_beq hx hty]; by_cases e : xs.headD 0 = tw <;> simp [e]) hY
    (fun _ zs h5 hz => ilw_internFVar p hp n iw (xs.headD 0) zs hS₁ hM₁ hx h5 hz)

/-- **`lp_proj` refines `instLPArmProj`.** -/
theorem ilw_projArm {m m' : Mem} {a : AState} {M : ModeMaps} {h ko kc vo vc fu r : Word}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hE : ILWEnv m a ko kc vo vc ks us vs) (hh : HW h)
    (he : HW (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)))
    (hW : ilwProjW p n m h ko kc vo vc fu = some (r, m')) :
    ILWStep (instLPArmProj ks vs fu.toNat (decE h) (decI (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3)))
      (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1)).toNat
      (decE (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)))) a dn m m' vis fe M eb r := by
  rw [instLPArmProj_eq]
  unfold ilwProjW at hW
  generalize rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3) = nw at hW ⊢
  generalize rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1) = iw at hW ⊢
  generalize rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2) = ew at he hW ⊢
  refine ilw_arm hS hM hh (Y := match callW p n "lp_go" [ew, ko, kc, vo, vc, fu] m with
      | none => none
      | some (x, m₁) => ilwRbProj p n m₁ h nw iw ew (x.headD 0))
    (by rw [← hW]; congr 1; cases callW p n "lp_go" [ew, ko, kc, vo, vc, fu] m <;> rfl) ?_
  intro r₃ m₃ _ hY
  cases h1 : callW p n "lp_go" [ew, ko, kc, vo, vc, fu] m with
  | none => rw [h1] at hY; simp at hY
  | some q =>
  obtain ⟨xs, m₁⟩ := q
  rw [h1] at hY; dsimp only at hY
  refine ILWStep.bind (ih m m₁ a dn vis fe M eb ew ko kc vo vc fu ks us vs xs hS hM hE he h1) ?_
  intro a₁ M₁ _ hS₁ hM₁ _ _ hx
  exact ilw_rebuild (c := decE (xs.headD 0) == decE ew)
    (Y := ilwRbProj p n m₁ h nw iw ew (xs.headD 0))
    (Yn := callW p n "mk_proj" [nw, iw, xs.headD 0] m₁) hS₁ hM₁ hh (by rw [ilw_beq hx he, ilwRbProj]; by_cases e : xs.headD 0 = ew <;> simp [e]) hY
    (fun _ zs h5 hz => ilw_mkProj p hp n nw iw (xs.headD 0) zs hS₁ hM₁ h5 hz)

/-- **`lp_let` refines `instLPArmLet`.** -/
theorem ilw_letArm {m m' : Mem} {a : AState} {M : ModeMaps} {h ko kc vo vc fu r : Word}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hE : ILWEnv m a ko kc vo vc ks us vs) (hh : HW h)
    (hf : HW (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)))
    (ha : HW (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)))
    (hb : HW (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)))
    (hW : ilwLetW p n m h ko kc vo vc fu = some (r, m')) :
    ILWStep (instLPArmLet ks vs fu.toNat (decE h) (decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)))
      (decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)))
      (decE (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)))) a dn m m' vis fe M eb r := by
  rw [instLPArmLet_eq]
  unfold ilwLetW at hW
  generalize rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3) = fw at hf hW ⊢
  generalize rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1) = aw at ha hW ⊢
  generalize rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2) = bw at hb hW ⊢
  refine ilw_arm hS hM hh (Y := match callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with
      | none => none
      | some (x, m₁) => match callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ with
        | none => none
        | some (y, m₂) => match callW p n "lp_go" [bw, ko, kc, vo, vc, fu] m₂ with
          | none => none
          | some (z, m₃) => ilwRbLet p n m₃ h fw aw bw (x.headD 0) (y.headD 0) (z.headD 0))
    (by
      rw [← hW]; congr 1
      cases callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with
      | none => rfl
      | some q =>
        obtain ⟨x, m₁⟩ := q
        simp only [ilwLetK₁_some]
        cases callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ with
        | none => rfl
        | some q =>
          obtain ⟨y, m₂⟩ := q
          simp only [ilwLetK₂_some]
          cases callW p n "lp_go" [bw, ko, kc, vo, vc, fu] m₂ <;> rfl) ?_
  intro r₃ m₃ _ hY
  cases h1 : callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with
  | none => rw [h1] at hY; simp at hY
  | some q =>
  obtain ⟨xs, m₁⟩ := q
  rw [h1] at hY; dsimp only at hY
  cases h2 : callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ with
  | none => rw [h2] at hY; simp at hY
  | some q =>
  obtain ⟨ys, m₂⟩ := q
  rw [h2] at hY; dsimp only at hY
  cases h3 : callW p n "lp_go" [bw, ko, kc, vo, vc, fu] m₂ with
  | none => rw [h3] at hY; simp at hY
  | some q =>
  obtain ⟨zs, m₄⟩ := q
  rw [h3] at hY; dsimp only at hY
  refine ILWStep.bind (ih m m₁ a dn vis fe M eb fw ko kc vo vc fu ks us vs xs hS hM hE hf h1) ?_
  intro a₁ M₁ _ hS₁ hM₁ hg₁ hSt₁ hx
  refine ILWStep.bind (ih m₁ m₂ a₁ dn vis fe M₁ eb aw ko kc vo vc fu ks us vs ys hS₁ hM₁
    (hE.keep hSt₁ hg₁) ha h2) ?_
  intro a₂ M₂ _ hS₂ hM₂ hg₂ hSt₂ hy
  refine ILWStep.bind (ih m₂ m₄ a₂ dn vis fe M₂ eb bw ko kc vo vc fu ks us vs zs hS₂ hM₂
    ((hE.keep hSt₁ hg₁).keep hSt₂ hg₂) hb h3) ?_
  intro a₃ M₃ _ hS₃ hM₃ _ _ hz
  exact ilw_rebuild
    (c := decE (xs.headD 0) == decE fw && decE (ys.headD 0) == decE aw && decE (zs.headD 0) == decE bw)
    (Y := ilwRbLet p n m₄ h fw aw bw (xs.headD 0) (ys.headD 0) (zs.headD 0))
    (Yn := callW p n "mk_let" [xs.headD 0, ys.headD 0, zs.headD 0] m₄) hS₃ hM₃ hh
    (by rw [ilw_beq hx hf, ilw_beq hy ha, ilw_beq hz hb, ilwRbLet]
        generalize xs.headD 0 = x; generalize ys.headD 0 = y; generalize zs.headD 0 = z
        by_cases e1 : x = fw <;> by_cases e2 : y = aw <;> by_cases e3 : z = bw <;> simp [e1, e2, e3, ilwRbLet2]) hY
    (fun _ ws h5 hw => ilw_mkLet p hp n _ _ _ ws hS₃ hM₃ h5 hw)

/-- **A two-child arm** (`lp_app`, `lp_lam`, `lp_forall`: record array `R`, node maker `mk`, node
constructor `C`) refines the twin's. -/
theorem ilw_binArm (R : ArrId) (mk : FnName) (C : EIdx → EIdx → ENodeView)
    (hmk : ∀ (m m' : Mem) (a : AState) (M : ModeMaps) (x y : Word) (rs : List Word),
      CoreS dn m a vis fe M eb → ILWMemo m a → HW x → HW y → callW p n mk [x, y] m = some (rs, m') →
      HW (rs.headD 0) → ILWStep (internE (C (decE x) (decE y))) a dn m m' vis fe M eb (rs.headD 0))
    {m m' : Mem} {a : AState} {M : ModeMaps} {h ko kc vo vc fu r : Word}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hE : ILWEnv m a ko kc vo vc ks us vs) (hh : HW h)
    (hf : HW (rdW (m.arr64 R) (idxW h * 4 + tierW h * 2)))
    (ha : HW (rdW (m.arr64 R) (idxW h * 4 + tierW h * 2 + 1)))
    (hW : ilwBinW R mk p n m h ko kc vo vc fu = some (r, m')) :
    ILWStep (ilwArmT (decE h) (do
      let t ← instLPGo ks vs fu.toNat (decE (rdW (m.arr64 R) (idxW h * 4 + tierW h * 2)))
      let b ← instLPGo ks vs fu.toNat (decE (rdW (m.arr64 R) (idxW h * 4 + tierW h * 2 + 1)))
      ilwRbT (t == decE (rdW (m.arr64 R) (idxW h * 4 + tierW h * 2)) &&
        b == decE (rdW (m.arr64 R) (idxW h * 4 + tierW h * 2 + 1))) (decE h) (internE (C t b))))
      a dn m m' vis fe M eb r := by
  unfold ilwBinW at hW
  generalize rdW (m.arr64 R) (idxW h * 4 + tierW h * 2) = fw at hf hW ⊢
  generalize rdW (m.arr64 R) (idxW h * 4 + tierW h * 2 + 1) = aw at ha hW ⊢
  refine ilw_arm hS hM hh (Y := match callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with
      | none => none
      | some (x, m₁) => match callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ with
        | none => none
        | some (y, m₂) => ilwRb p n mk m₂ h fw aw (x.headD 0) (y.headD 0))
    (by
      rw [← hW]; congr 1
      cases callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with
      | none => rfl
      | some q =>
        obtain ⟨x, m₁⟩ := q
        simp only [ilwBinK₁_some]
        cases callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ <;> rfl) ?_
  intro r₃ m₃ _ hY
  cases h1 : callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with
  | none => rw [h1] at hY; simp at hY
  | some q =>
  obtain ⟨xs, m₁⟩ := q
  rw [h1] at hY; dsimp only at hY
  cases h2 : callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ with
  | none => rw [h2] at hY; simp at hY
  | some q =>
  obtain ⟨ys, m₂⟩ := q
  rw [h2] at hY; dsimp only at hY
  refine ILWStep.bind (ih m m₁ a dn vis fe M eb fw ko kc vo vc fu ks us vs xs hS hM hE hf h1) ?_
  intro a₁ M₁ _ hS₁ hM₁ hg₁ hSt₁ hx
  refine ILWStep.bind (ih m₁ m₂ a₁ dn vis fe M₁ eb aw ko kc vo vc fu ks us vs ys hS₁ hM₁
    (hE.keep hSt₁ hg₁) ha h2) ?_
  intro a₂ M₂ _ hS₂ hM₂ _ _ hy
  exact ilw_rebuild (c := decE (xs.headD 0) == decE fw && decE (ys.headD 0) == decE aw)
    (Y := ilwRb p n mk m₂ h fw aw (xs.headD 0) (ys.headD 0))
    (Yn := callW p n mk [xs.headD 0, ys.headD 0] m₂) hS₂ hM₂ hh
    (by rw [ilw_beq hx hf, ilw_beq hy ha, ilwRb]
        by_cases e1 : xs.headD 0 = fw <;> by_cases e2 : ys.headD 0 = aw <;> simp [e1, e2]) hY
    (fun _ zs h5 hz => hmk m₂ _ a₂ M₂ _ _ zs hS₂ hM₂ hx hy h5 hz)

end armsP

end arms

end L.Arena
