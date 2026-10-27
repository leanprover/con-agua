import ConAgua.Arena.InstLPWalkRef

/-!
# The `instLP` walk refines `instLPGo`: the arms `fvar`, `proj`, `letE`

Each arm is the memo probe and write around a body (`ilwArmT`, `ilw_arm`): the children (the walk
at the arm's fuel) and the rebuild.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


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
    (hty : HW (tfld m FVAR (tierW h) (idxW h) 1))
    (hW : ilwFVarW p n m h ko kc vo vc fu = some (r, m')) :
    ILWStep (instLPArmFVar ks vs fu.toNat (decE h) (tfld m FVAR (tierW h) (idxW h) 0).toNat
      (decE (tfld m FVAR (tierW h) (idxW h) 1))) a dn m m' vis fe M eb r := by
  rw [instLPArmFVar_eq]
  unfold ilwFVarW at hW
  generalize tfld m FVAR (tierW h) (idxW h) 0 = iw at hW ⊢
  generalize tfld m FVAR (tierW h) (idxW h) 1 = tw at hty hW ⊢
  refine ilw_arm hS hM hh (Y := match callW p n "lp_go" [tw, ko, kc, vo, vc, fu] m with
      | none => none
      | some (x, m₁) => if x.headD 0 = tw then some (h, m₁) else ilwChk (callW p n "intern_fvar" [iw, x.headD 0] m₁))
    (by rw [← hW]; congr 1; cases callW p n "lp_go" [tw, ko, kc, vo, vc, fu] m <;> rfl) ?_
  intro r₃ m₃ _ hY
  rcases h1 : callW p n "lp_go" [tw, ko, kc, vo, vc, fu] m with _ | ⟨xs, m₁⟩ <;> rw [h1] at hY
  · simp at hY
  dsimp only at hY
  refine ILWStep.bind (ih m m₁ a dn vis fe M eb tw ko kc vo vc fu ks us vs xs hS hM hE hty h1) ?_
  intro a₁ M₁ _ hS₁ hM₁ _ _ hx
  exact ilw_rebuild (c := decE (xs.headD 0) == decE tw)
    (Y := if xs.headD 0 = tw then some (h, m₁) else ilwChk (callW p n "intern_fvar" [iw, xs.headD 0] m₁))
    (Yn := callW p n "intern_fvar" [iw, xs.headD 0] m₁) hS₁ hM₁ hh (by rw [ilw_beq hx hty]; by_cases e : xs.headD 0 = tw <;> simp) hY
    (fun _ zs h5 hz => ilw_internFVar p hp n iw (xs.headD 0) zs hS₁ hM₁ hx h5 hz)

/-- **`lp_proj` refines `instLPArmProj`.** -/
theorem ilw_projArm {m m' : Mem} {a : AState} {M : ModeMaps} {h ko kc vo vc fu r : Word}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hE : ILWEnv m a ko kc vo vc ks us vs) (hh : HW h)
    (he : HW (tfld m PROJ (tierW h) (idxW h) 2))
    (hW : ilwProjW p n m h ko kc vo vc fu = some (r, m')) :
    ILWStep (instLPArmProj ks vs fu.toNat (decE h) (decI (tfld m PROJ (tierW h) (idxW h) 0))
      (tfld m PROJ (tierW h) (idxW h) 1).toNat
      (decE (tfld m PROJ (tierW h) (idxW h) 2))) a dn m m' vis fe M eb r := by
  rw [instLPArmProj_eq]
  unfold ilwProjW at hW
  generalize tfld m PROJ (tierW h) (idxW h) 0 = nw at hW ⊢
  generalize tfld m PROJ (tierW h) (idxW h) 1 = iw at hW ⊢
  generalize tfld m PROJ (tierW h) (idxW h) 2 = ew at he hW ⊢
  refine ilw_arm hS hM hh (Y := match callW p n "lp_go" [ew, ko, kc, vo, vc, fu] m with
      | none => none
      | some (x, m₁) => ilwRbProj p n m₁ h nw iw ew (x.headD 0))
    (by rw [← hW]; congr 1; cases callW p n "lp_go" [ew, ko, kc, vo, vc, fu] m <;> rfl) ?_
  intro r₃ m₃ _ hY
  rcases h1 : callW p n "lp_go" [ew, ko, kc, vo, vc, fu] m with _ | ⟨xs, m₁⟩ <;> rw [h1] at hY
  · simp at hY
  dsimp only at hY
  refine ILWStep.bind (ih m m₁ a dn vis fe M eb ew ko kc vo vc fu ks us vs xs hS hM hE he h1) ?_
  intro a₁ M₁ _ hS₁ hM₁ _ _ hx
  exact ilw_rebuild (c := decE (xs.headD 0) == decE ew)
    (Y := ilwRbProj p n m₁ h nw iw ew (xs.headD 0))
    (Yn := callW p n "mk_proj" [nw, iw, xs.headD 0] m₁) hS₁ hM₁ hh (by rw [ilw_beq hx he, ilwRbProj]; by_cases e : xs.headD 0 = ew <;> simp) hY
    (fun _ zs h5 hz => ilw_mkProj p hp n nw iw (xs.headD 0) zs hS₁ hM₁ h5 hz)

/-- **`lp_let` refines `instLPArmLet`.** The third child and the rebuild are `lp_let_tail`'s, one
L fuel down (`ih'`). -/
theorem ilw_letArm (hil : ILWProg p) (ih' : ∀ k, n = k + 1 → ILWGoOK p k) {m m' : Mem} {a : AState}
    {M : ModeMaps} {h ko kc vo vc fu r : Word}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hE : ILWEnv m a ko kc vo vc ks us vs) (hh : HW h)
    (hf : HW (tfld m LET (tierW h) (idxW h) 0))
    (ha : HW (tfld m LET (tierW h) (idxW h) 1))
    (hb : HW (tfld m LET (tierW h) (idxW h) 2))
    (hW : ilwLetW p n m h ko kc vo vc fu = some (r, m')) :
    ILWStep (instLPArmLet ks vs fu.toNat (decE h) (decE (tfld m LET (tierW h) (idxW h) 0))
      (decE (tfld m LET (tierW h) (idxW h) 1))
      (decE (tfld m LET (tierW h) (idxW h) 2))) a dn m m' vis fe M eb r := by
  rw [instLPArmLet_eq]
  unfold ilwLetW at hW
  generalize tfld m LET (tierW h) (idxW h) 0 = fw at hf hW ⊢
  generalize tfld m LET (tierW h) (idxW h) 1 = aw at ha hW ⊢
  generalize tfld m LET (tierW h) (idxW h) 2 = bw at hb hW ⊢
  refine ilw_arm hS hM hh (Y := match callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with
      | none => none
      | some (x, m₁) => match callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ with
        | none => none
        | some (y, m₂) =>
          ilwHd (callW p n "lp_let_tail" [h, fw, aw, bw, x.headD 0, y.headD 0, ko, kc, vo, vc, fu] m₂))
    (by
      rw [← hW]; congr 1
      cases callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with
      | none => rfl
      | some q =>
        obtain ⟨x, m₁⟩ := q
        simp only [ilwLetK₁_some]
        cases callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ <;> rfl) ?_
  intro r₃ m₃ _ hY
  rcases h1 : callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with _ | ⟨xs, m₁⟩ <;> rw [h1] at hY
  · simp at hY
  dsimp only at hY
  rcases h2 : callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ with _ | ⟨ys, m₂⟩ <;> rw [h2] at hY
  · simp at hY
  dsimp only at hY
  refine ILWStep.bind (ih m m₁ a dn vis fe M eb fw ko kc vo vc fu ks us vs xs hS hM hE hf h1) ?_
  intro a₁ M₁ _ hS₁ hM₁ hg₁ hSt₁ hx
  refine ILWStep.bind (ih m₁ m₂ a₁ dn vis fe M₁ eb aw ko kc vo vc fu ks us vs ys hS₁ hM₁
    (hE.keep hSt₁ hg₁) ha h2) ?_
  intro a₂ M₂ _ hS₂ hM₂ hg₂ hSt₂ hy
  -- the tail, `lp_let_tail` at the arm's fuel
  cases n with
  | zero => rw [callW_zero] at hY; cases hY
  | succ k =>
  rcases h4 : callW p (k + 1) "lp_let_tail" [h, fw, aw, bw, xs.headD 0, ys.headD 0, ko, kc, vo, vc, fu] m₂ with _ | ⟨ts, m₅⟩ <;> simp only [h4, ilwHd, reduceCtorEq] at hY
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (lpLetTail_spec p hil k _ h fw aw bw (xs.headD 0) (ys.headD 0) ko kc vo vc fu) h4
  rw [hs4] at hW4
  change ilwLetTW p k m₂ h fw aw bw _ _ ko kc vo vc fu = some (ts.headD 0, m₅) at hW4
  rw [hY] at hW4
  unfold ilwLetTW at hW4
  rcases h3 : callW p k "lp_go" [bw, ko, kc, vo, vc, fu] m₂ with _ | ⟨zs, m₄⟩ <;> simp only [h3, ilwLetTK, reduceCtorEq] at hW4
  refine ILWStep.bind (ih' k rfl m₂ m₄ a₂ dn vis fe M₂ eb bw ko kc vo vc fu ks us vs zs hS₂ hM₂
    ((hE.keep hSt₁ hg₁).keep hSt₂ hg₂) hb h3) ?_
  intro a₃ M₃ _ hS₃ hM₃ _ _ hz
  -- the rebuild, `lp_rb_let` at the tail's fuel
  cases k with
  | zero => rw [callW_zero] at hW4; cases hW4
  | succ j =>
  rcases h5 : callW p (j + 1) "lp_rb_let" [h, fw, aw, bw, xs.headD 0, ys.headD 0, zs.headD 0] m₄ with _ | ⟨ws, m₆⟩ <;> simp only [h5, ilwHd, reduceCtorEq] at hW4
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨m₄, Locals.init []⟩)
    (lpRbLet_spec p hil j _ h fw aw bw (xs.headD 0) (ys.headD 0) (zs.headD 0)) h5
  rw [hs5] at hW5
  change ilwRbLet p j m₄ h fw aw bw _ _ _ = some (ws.headD 0, m₆) at hW5
  rw [hW4] at hW5
  exact ilw_rebuild
    (c := decE (xs.headD 0) == decE fw && decE (ys.headD 0) == decE aw && decE (zs.headD 0) == decE bw)
    (Y := ilwRbLet p j m₄ h fw aw bw (xs.headD 0) (ys.headD 0) (zs.headD 0))
    (Yn := callW p j "mk_let" [xs.headD 0, ys.headD 0, zs.headD 0] m₄) hS₃ hM₃ hh
    (by rw [ilw_beq hx hf, ilw_beq hy ha, ilw_beq hz hb, ilwRbLet]
        generalize xs.headD 0 = x; generalize ys.headD 0 = y; generalize zs.headD 0 = z
        by_cases e1 : x = fw <;> by_cases e2 : y = aw <;> by_cases e3 : z = bw <;> simp [e1, e2, e3, ilwRbLet2])
    hW5
    (fun _ ws h6 hw => ilw_mkLet p hp j _ _ _ ws hS₃ hM₃ h6 hw)

/-- **A two-child arm** (`lp_app`, `lp_lam`, `lp_forall`: record array `R`, node maker `mk`, node
constructor `C`) refines the twin's. -/
theorem ilw_binArm (R : TRec) (mk : FnName) (C : EIdx → EIdx → ENodeView)
    (hmk : ∀ (m m' : Mem) (a : AState) (M : ModeMaps) (x y : Word) (rs : List Word),
      CoreS dn m a vis fe M eb → ILWMemo m a → HW x → HW y → callW p n mk [x, y] m = some (rs, m') →
      HW (rs.headD 0) → ILWStep (internE (C (decE x) (decE y))) a dn m m' vis fe M eb (rs.headD 0))
    {m m' : Mem} {a : AState} {M : ModeMaps} {h ko kc vo vc fu r : Word}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hM : ILWMemo m a) (hE : ILWEnv m a ko kc vo vc ks us vs) (hh : HW h)
    (hf : HW (tfld m R (tierW h) (idxW h) 0))
    (ha : HW (tfld m R (tierW h) (idxW h) 1))
    (hW : ilwBinW R mk p n m h ko kc vo vc fu = some (r, m')) :
    ILWStep (ilwArmT (decE h) (do
      let t ← instLPGo ks vs fu.toNat (decE (tfld m R (tierW h) (idxW h) 0))
      let b ← instLPGo ks vs fu.toNat (decE (tfld m R (tierW h) (idxW h) 1))
      ilwRbT (t == decE (tfld m R (tierW h) (idxW h) 0) &&
        b == decE (tfld m R (tierW h) (idxW h) 1)) (decE h) (internE (C t b))))
      a dn m m' vis fe M eb r := by
  unfold ilwBinW at hW
  generalize tfld m R (tierW h) (idxW h) 0 = fw at hf hW ⊢
  generalize tfld m R (tierW h) (idxW h) 1 = aw at ha hW ⊢
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
  rcases h1 : callW p n "lp_go" [fw, ko, kc, vo, vc, fu] m with _ | ⟨xs, m₁⟩ <;> rw [h1] at hY
  · simp at hY
  dsimp only at hY
  rcases h2 : callW p n "lp_go" [aw, ko, kc, vo, vc, fu] m₁ with _ | ⟨ys, m₂⟩ <;> rw [h2] at hY
  · simp at hY
  dsimp only at hY
  refine ILWStep.bind (ih m m₁ a dn vis fe M eb fw ko kc vo vc fu ks us vs xs hS hM hE hf h1) ?_
  intro a₁ M₁ _ hS₁ hM₁ hg₁ hSt₁ hx
  refine ILWStep.bind (ih m₁ m₂ a₁ dn vis fe M₁ eb aw ko kc vo vc fu ks us vs ys hS₁ hM₁
    (hE.keep hSt₁ hg₁) ha h2) ?_
  intro a₂ M₂ _ hS₂ hM₂ _ _ hy
  exact ilw_rebuild (c := decE (xs.headD 0) == decE fw && decE (ys.headD 0) == decE aw)
    (Y := ilwRb p n mk m₂ h fw aw (xs.headD 0) (ys.headD 0))
    (Yn := callW p n mk [xs.headD 0, ys.headD 0] m₂) hS₂ hM₂ hh
    (by rw [ilw_beq hx hf, ilw_beq hy ha, ilwRb]
        by_cases e1 : xs.headD 0 = fw <;> by_cases e2 : ys.headD 0 = aw <;> simp) hY
    (fun _ zs h5 hz => hmk m₂ _ a₂ M₂ _ _ zs hS₂ hM₂ hx hy h5 hz)

end armsP

end arms

end L.Arena
