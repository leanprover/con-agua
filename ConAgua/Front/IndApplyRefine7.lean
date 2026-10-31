module

public import ConAgua.Verdict.FrontViE
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# The apply step of an `inductive` line against the twin, VII: the recursor records

`rec_ref`: `vi_rec` on a recursor record passes the twin's checks of it (`RecOK`): its name is
bound, its counts are the block's, its `k` is `kExpected?`'s, and if it is named `T.rec`, every type
named `T` has a sort telescope of `nP + numIndices` binders, if any; or it fails them (`RecFail`).
`recsGo_ref` for all of them (`RecsFail`), `recs_ref` unless the block is nested (`nestedW_twin`
the `nested` flag), `nparams_ref` the `numParams` check. One refinement each for both outcomes
(`RefC`, on the unified models).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true


namespace L.Front.Ind

/-! ## The unified models -/

l_model viNparams_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_nparams ↦ viNparamsE]
  specs [viNpGo_specE p hL.vi_np_go n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE] unified

l_model rec_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_rec ↦ recE]
  specs [nameGetL_spec p hL n, nrp_spec p hL n, recIdx_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model recsGo_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_recs_go ↦ recsGoE]
  specs [rec_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model recs_specE (p : Prog) (hL : IndApplyLookups p)
  fns [hL.vi_recs ↦ recsE]
  specs [nested_spec p hL n, recsGo_specE p hL n]
  grind [arena_grind] extra [L.Arena.ld64_rdW_specE]
  unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- **The twin's checks of one recursor record pass.** -/
def RecOK (st : StateD) (a : AState) (TN : List NIdx) (TT : List EIdx) (nPd nTypes nCtors : Nat)
    (KE : Option Bool) (fuel : Nat) (rc : IndRecRec) : Prop :=
  ∃ rn, (st.name rc.cv.name).run a = .ok (rn, a) ∧ rc.numParams = nPd ∧ rc.numMotives = nTypes ∧
    rc.numMinors = nCtors ∧ (∀ kE, KE = some kE → rc.k = kE) ∧
    ∃ v, (viewN rn).run a = .ok (v, a) ∧
      ∀ T, v = .str T "rec" → ∀ j (hj : j < TN.length) (hj' : j < TT.length), TN[j] = T →
        ∃ o, (piSortTeleLen? fuel TT[j]).run a = .ok (o, a) ∧ ∀ k, o = some k → nPd + rc.numIndices = k

/-- `kExpected?` from its word (`0` none, `1` `some false`, `2` `some true`). -/
def keOf (ke : Word) : Option Bool := if ke = 0 then none else some (ke = 2)


/-- **One recursor record fails the twin's checks**: its name is bound, and the first of its
checks that fails is the parameter count, the motive count, the minor count, `k` against
`kExpected?`, or (named `T.rec`) the indices at some type named `T`, the earlier types of that
loop passing. -/
def RecFail (st : StateD) (a : AState) (TN : List NIdx) (TT : List EIdx) (nPd nTypes nCtors : Nat)
    (KE : Option Bool) (fuel : Nat) (rc : IndRecRec) : Prop :=
  ∃ rn, (st.name rc.cv.name).run a = .ok (rn, a) ∧
    (rc.numParams ≠ nPd ∨ rc.numParams = nPd ∧ (rc.numMotives ≠ nTypes ∨ rc.numMotives = nTypes ∧
      (rc.numMinors ≠ nCtors ∨ rc.numMinors = nCtors ∧
        ((∃ kE, KE = some kE ∧ rc.k ≠ kE) ∨ (∀ kE, KE = some kE → rc.k = kE) ∧
          ∃ T, (viewN rn).run a = .ok (.str T "rec", a) ∧
            ∃ j, ∃ hj : j < TN.length, ∃ hj' : j < TT.length,
              (∀ j' (h1 : j' < j), TN[j'] = T → ∃ o,
                (piSortTeleLen? fuel (TT[j']'(by omega))).run a = .ok (o, a) ∧
                ∀ k, o = some k → nPd + rc.numIndices = k) ∧
              TN[j] = T ∧ ∃ k, (piSortTeleLen? fuel TT[j]).run a = .ok (some k, a) ∧
                nPd + rc.numIndices ≠ k))))

/-- **The recursor loop stops at record `j`**: the records before it pass, record `j` fails. -/
def RecsFail (st : StateD) (a : AState) (TN : List NIdx) (TT : List EIdx) (nPd nTypes nCtors : Nat)
    (KE : Option Bool) (fuel : Nat) (rcs : List IndRecRec) : Prop :=
  ∃ j, ∃ hj : j < rcs.length, (∀ i (hi : i < j), RecOK st a TN TT nPd nTypes nCtors KE fuel
    (rcs[i]'(by omega))) ∧ RecFail st a TN TT nPd nTypes nCtors KE fuel rcs[j]

/-- **`vi_rec`'s ok half**: the memory unchanged, the record passes the twin's checks. -/
structure RecPost (st : StateD) (a : AState) (m : Mem) (np tn cn ke tyn tyt fuel : Word)
    (rc : IndRecRec) (v : Word × Mem) : Prop where
  mem : v.2 = m
  ok : RecOK st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat) np.toNat tn.toNat
    cn.toNat (keOf ke) fuel.toNat rc

/-- **`vi_rec`'s error half**: a class-`≠ 0` error is an `.invalid` (class `1`), the record fails
the twin's checks. -/
def RecErr (st : StateD) (a : AState) (m : Mem) (np tn cn ke tyn tyt fuel : Word) (rc : IndRecRec)
    (e : Err) : Prop :=
  e.cls ≠ 0 → e.cls = 1 ∧ RecFail st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat)
    np.toNat tn.toNat cn.toNat (keOf ke) fuel.toNat rc

/-- **`vi_rec`, both outcomes**: against the twin's checks of one recursor record. -/
theorem rec_ref {b : ByteArray} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {rc : IndRecRec} {r np tn cn ke tyn tyt fuel : Word}
    (hrec : RecF b m r.toNat rc) (hr : r.toNat + 11 < 2 ^ 63) (hnp : np.toNat < 10 ^ 18)
    (hke : ke = 0 ∨ ke = 1 ∨ ke = 2) (hb : tyn.toNat + tn.toNat ≤ 2 ^ 63)
    (hb' : tyt.toNat + tn.toNat ≤ 2 ^ 63)
    (hTN : ∀ k, k < tn.toNat → (wd m IFL (tyn.toNat + k)).toNat < 2 ^ 32) (p : Prog) (n : Nat) :
    RefC True (recE p n m r np tn cn ke tyn tyt fuel) (RecPost st a m np tn cn ke tyn tyt fuel rc)
      (RecErr st a m np tn cn ke tyn tyt fuel rc) := by
  cases n with
  | zero => simp only [recE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  rw [recE.arm1]
  have ix : ∀ s : Word, s.toNat ≤ 10 → rdW (m.arr64 IFR) (r + s) = wd m IFR (r.toNat + s.toNat) := by
    intro s hs; rw [wd_eq, widx2 _ _ (by omega)]
  obtain ⟨⟨c1, -, -⟩, c2, c3, c4, c5, c6, -⟩ := hrec
  rcases hl : lkW m NID (rdW (m.arr64 IFR) r) with _ | rnw
  · rw [liftE_none, recE.k_name_get.none]; exact fun _ hk => absurd Err.cls_oob hk
  rw [liftE_some]
  rw [wd_eq] at hl
  have hname := (lkW_name hD a hl).1
  rw [c1.1] at hname
  have e5 : rdW (m.arr64 IFR) (r + 5) = wd m IFR (r.toNat + 5) := by
    have := ix 5 (by decide); simpa using this
  -- the indices check (`j1`), after the counts and `k`
  have hJ : ∀ (hkp : ∀ kE, keOf ke = some kE → rc.k = kE)
      (e8' : rc.numParams = np.toNat) (e7' : rc.numMotives = tn.toNat) (e6' : rc.numMinors = cn.toNat),
      RefC True (recE.j1 p n r np tn tyn tyt fuel rnw m) (RecPost st a m np tn cn ke tyn tyt fuel rc)
        (RecErr st a m np tn cn ke tyn tyt fuel rc) := by
    intro hkp e8' e7' e6'
    rw [recE.j1.arm1]
    rcases hn : nrpW m rnw with _ | ⟨f, tt⟩
    · rw [liftE_none, recE.k_name_rec_pre.none]; exact fun _ hk => absurd Err.cls_oob hk
    rw [liftE_some]
    obtain ⟨v, hv, hv1, hv0⟩ := nrpW_ok hR rnw f tt hn
    by_cases hf : f = 0
    · rw [recE.k_name_rec_pre.arm2 p n r np tn tyn tyt fuel m f tt hf, recE.j2.arm1]
      refine ⟨rfl, _, hname, e8', e7', e6', hkp, v, hv, fun T hT => absurd hT (hv0 hf T)⟩
    rw [recE.k_name_rec_pre.arm1 p n r np tn tyn tyt fuel m f tt hf]
    obtain ⟨hvs, htt⟩ := hv1 hf
    have hi := recIdx_ref hR hnp (by rw [e5, c3.1]; exact c3.2) hb hb' p n 0
      (T := tt) (ni := rdW (m.arr64 IFR) (r + 5)) (fuel := fuel)
    rcases h3 : recIdxE p n m tt (rdW (m.arr64 IFR) (r + 5)) np tn tyn tyt fuel 0 with e3 | ⟨u, mr⟩ <;>
      rw [h3] at hi
    · rw [recE.k_vi_rec_idx.none]
      intro _ hk
      obtain ⟨he, k, -, k2, k3, k4, x, k5, k6⟩ := hi trivial hk
      rw [e5, c3.1] at k4 k6
      rw [hvs] at hv
      refine ⟨by rw [he]; decide, _, hname, .inr ⟨e8', .inr ⟨e7', .inr ⟨e6', .inr ⟨hkp, _, hv, k,
        by rw [islice_length]; exact k2, by rw [islice_length]; exact k2, fun j' hj' hT' => ?_,
        by rw [islice_get, k3], x, by rw [islice_get]; exact k5, k6⟩⟩⟩⟩⟩
      rw [islice_get] at hT' ⊢
      have hw : wd m IFL (tyn.toNat + j') = tt := decI_inj (hTN j' (by omega)) htt hT'
      exact k4 j' (Nat.zero_le _) hj' hw
    rw [recE.k_vi_rec_idx.arm1, recE.j2.arm1]
    obtain ⟨hmr, hidx⟩ := hi
    refine ⟨hmr, _, hname, e8', e7', e6', hkp, v, hv, fun T hT j hj hj' hTj => ?_⟩
    rw [hvs] at hT
    simp only [NNodeView.str.injEq, and_true] at hT
    subst hT
    simp only [islice_length] at hj hj'
    rw [islice_get] at hTj ⊢
    have hw : wd m IFL (tyn.toNat + j) = tt := decI_inj (hTN j hj) htt hTj
    obtain ⟨o, ho1, ho2⟩ := hidx j (Nat.zero_le _) hj hw
    exact ⟨o, ho1, fun x hx => by rw [← ho2 x hx, e5, c3.1]⟩
  have hcls : ∀ R : Word, R &&& 3 = 1 → ∀ e : Err, e = .abort R → e.cls = 1 := by
    intro R hR' e he; subst he; simpa [Err.cls] using hR'
  by_cases e8 : rdW (m.arr64 IFR) (r + 8) = np
  rotate_left
  · rw [recE.k_name_get.abort1 p n r np tn cn ke tyn tyt fuel m rnw e8]
    refine fun _ _ => ⟨by decide, _, hname, .inl fun heq => e8 ?_⟩
    rw [ix 8 (by decide)]; apply UInt64.toNat_inj.mp; simp only [show (8 : Word).toNat = 8 from rfl]
    rw [c6.1, heq]
  have e8' : rc.numParams = np.toNat := by
    rw [ix 8 (by decide)] at e8; rw [← c6.1]; simp only [show (8 : Word).toNat = 8 from rfl] at e8; rw [e8]
  by_cases e7 : rdW (m.arr64 IFR) (r + 7) = tn
  rotate_left
  · rw [recE.k_name_get.abort2 p n r np tn cn ke tyn tyt fuel m rnw e8 e7]
    refine fun _ _ => ⟨by decide, _, hname, .inr ⟨e8', .inl fun heq => e7 ?_⟩⟩
    rw [ix 7 (by decide)]; apply UInt64.toNat_inj.mp; simp only [show (7 : Word).toNat = 7 from rfl]
    rw [c5.1, heq]
  have e7' : rc.numMotives = tn.toNat := by
    rw [ix 7 (by decide)] at e7; rw [← c5.1]; simp only [show (7 : Word).toNat = 7 from rfl] at e7; rw [e7]
  by_cases e6 : rdW (m.arr64 IFR) (r + 6) = cn
  rotate_left
  · rw [recE.k_name_get.abort3 p n r np tn cn ke tyn tyt fuel m rnw e8 e7 e6]
    refine fun _ _ => ⟨by decide, _, hname, .inr ⟨e8', .inr ⟨e7', .inl fun heq => e6 ?_⟩⟩⟩
    rw [ix 6 (by decide)]; apply UInt64.toNat_inj.mp; simp only [show (6 : Word).toNat = 6 from rfl]
    rw [c4.1, heq]
  have e6' : rc.numMinors = cn.toNat := by
    rw [ix 6 (by decide)] at e6; rw [← c4.1]; simp only [show (6 : Word).toNat = 6 from rfl] at e6; rw [e6]
  have e4r : rdW (m.arr64 IFR) (r + 4) = wd m IFR (r.toNat + 4) := by
    have := ix 4 (by decide); simpa using this
  by_cases hk0 : ke = 0
  · rw [recE.k_name_get.arm2 p n r np tn cn ke tyn tyt fuel m rnw e8 e7 e6 hk0]
    exact hJ (fun kE hkE => by simp [keOf, hk0] at hkE) e8' e7' e6'
  by_cases e4 : rdW (m.arr64 IFR) (r + 4) = ke - 1
  · rw [recE.k_name_get.arm1 p n r np tn cn ke tyn tyt fuel m rnw e8 e7 e6 hk0 e4]
    refine hJ (fun kE hkE => ?_) e8' e7' e6'
    simp only [keOf, hk0, ite_false, Option.some.injEq] at hkE
    rw [e4r, c2] at e4
    rcases hke with rfl | rfl | rfl
    · exact absurd rfl hk0
    · subst hkE; cases hk' : rc.k <;> simp_all
    · subst hkE; cases hk' : rc.k <;> simp_all
  · rw [recE.k_name_get.abort4 p n r np tn cn ke tyn tyt fuel m rnw e8 e7 e6 hk0 e4]
    refine fun _ _ => ⟨by decide, _, hname, .inr ⟨e8', .inr ⟨e7', .inr ⟨e6', .inl ⟨ke = 2, by simp [keOf, hk0], ?_⟩⟩⟩⟩⟩
    rw [e4r, c2] at e4
    rcases hke with rfl | rfl | rfl
    · exact absurd rfl hk0
    · cases hk' : rc.k <;> simp_all
    · cases hk' : rc.k <;> simp_all

/-- **`vi_recs_go`'s ok half**: the memory unchanged, every recursor record from `j` on passes
the twin's checks. -/
structure RecsGoPost (st : StateD) (a : AState) (m : Mem) (np tn cn ke tyn tyt fuel j : Word)
    (rcs : List IndRecRec) (v : Word × Mem) : Prop where
  mem : v.2 = m
  ok : ∀ k (hk : k < rcs.length), j.toNat ≤ k →
    RecOK st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat) np.toNat tn.toNat
      cn.toNat (keOf ke) fuel.toNat rcs[k]

/-- **`vi_recs_go`'s error half**: a class-`≠ 0` error is an `.invalid` at the first recursor
record from `j` on that fails the twin's checks, the ones before it passing. -/
def RecsGoErr (st : StateD) (a : AState) (m : Mem) (np tn cn ke tyn tyt fuel j : Word)
    (rcs : List IndRecRec) (e : Err) : Prop :=
  e.cls ≠ 0 → e.cls = 1 ∧ ∃ k, ∃ hk : k < rcs.length, j.toNat ≤ k ∧
    (∀ i (hi : i < k), j.toNat ≤ i →
      RecOK st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat) np.toNat tn.toNat
        cn.toNat (keOf ke) fuel.toNat (rcs[i]'(by omega))) ∧
    RecFail st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat) np.toNat tn.toNat
      cn.toNat (keOf ke) fuel.toNat rcs[k]

/-- **`vi_recs_go`, both outcomes.** -/
theorem recsGo_ref {b : ByteArray} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {rcs : List IndRecRec} {ro rn np tn cn ke tyn tyt fuel : Word}
    (hL : ListF (RecF b m) m 11 ro.toNat rcs) (hrn : rn.toNat = rcs.length)
    (hro : ro.toNat + 11 * rcs.length < 2 ^ 63) (hnp : np.toNat < 10 ^ 18)
    (hke : ke = 0 ∨ ke = 1 ∨ ke = 2) (hb : tyn.toNat + tn.toNat ≤ 2 ^ 63)
    (hb' : tyt.toNat + tn.toNat ≤ 2 ^ 63)
    (hTN : ∀ k, k < tn.toNat → (wd m IFL (tyn.toNat + k)).toNat < 2 ^ 32) (p : Prog) :
    ∀ n j, RefC True (recsGoE p n m ro rn np tn cn ke tyn tyt fuel j)
      (RecsGoPost st a m np tn cn ke tyn tyt fuel j rcs) (RecsGoErr st a m np tn cn ke tyn tyt fuel j rcs) := by
  intro n
  induction n with
  | zero => intro j; simp only [recsGoE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n ih =>
    intro j
    by_cases hle : rn ≤ j
    · rw [recsGoE.arm1 p n m ro rn np tn cn ke tyn tyt fuel j hle]
      exact ⟨rfl, fun k hk hjk => by have := UInt64.le_iff_toNat_le.mp hle; omega⟩
    rw [recsGoE.arm2 p n m ro rn np tn cn ke tyn tyt fuel j hle]
    have hj1 := wsucc j rn (UInt64.not_le.mp hle)
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle)
    have hix : (ro + 11 * j).toNat = ro.toNat + 11 * j.toNat := by
      have := widx ro 11 j 0 (by simp; omega); simpa using this
    have hrec := hL.2.2 j.toNat (by omega)
    rw [← hix] at hrec
    have h1 := rec_ref hR hD hrec (by rw [hix]; omega) hnp hke hb hb' hTN p n (st := st) (cn := cn) (fuel := fuel)
    rcases hc : recE p n m (ro + 11 * j) np tn cn ke tyn tyt fuel with e1 | ⟨u, m₁⟩ <;> rw [hc] at h1
    · rw [recsGoE.k_vi_rec.none]
      intro _ hk
      obtain ⟨hcl, hF⟩ := h1 trivial hk
      exact ⟨hcl, j.toNat, by omega, Nat.le_refl _, fun i hi h2 => by omega, hF⟩
    rw [recsGoE.k_vi_rec.arm1]
    obtain ⟨hm₁, hok⟩ := h1
    dsimp only at hm₁
    subst hm₁
    have h2 := ih (j + 1)
    rcases hg : recsGoE p n m₁ ro rn np tn cn ke tyn tyt fuel (j + 1) with e2 | ⟨u2, m₂⟩ <;> rw [hg] at h2
    · rw [recsGoE.k_vi_recs_go.none]
      intro _ hk
      obtain ⟨hc, k, hk', k1, k2, k3⟩ := h2 trivial hk
      rw [hj1] at k1
      refine ⟨hc, k, hk', by omega, fun i hi h3 => ?_, k3⟩
      by_cases hij : i = j.toNat
      · subst hij; exact hok
      · exact k2 i hi (by rw [hj1]; omega)
    rw [recsGoE.k_vi_recs_go.arm1]
    obtain ⟨hm, ih2⟩ := h2
    refine ⟨hm, fun k hk hjk => ?_⟩
    by_cases hkj : k = j.toNat
    · subst hkj; exact hok
    · exact ih2 k hk (by rw [hj1]; omega)

theorem nestedW_twin {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) :
    ∀ n j u, nestedW n m to tn j = some u →
      (u = 0 → ∀ k (hk : k < tys.length), j.toNat ≤ k → tys[k].numNested = 0) ∧
      (u ≠ 0 → ∃ k, ∃ hk : k < tys.length, tys[k].numNested ≠ 0) := by
  intro n
  induction n with
  | zero => intro j u h; simp [nestedW] at h
  | succ n ih =>
    intro j u h
    simp only [nestedW] at h
    split at h
    · rename_i hle
      cases h
      have := UInt64.le_iff_toNat_le.mp hle
      exact ⟨fun _ k hk h1 => by omega, fun h => absurd rfl h⟩
    rename_i hlt
    have hj1 := wsucc j tn (UInt64.not_le.mp hlt)
    have hjn := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hlt)
    have hix : (to + 11 * j + 9).toNat = to.toNat + 11 * j.toNat + 9 := widx _ _ _ _ (by simp; omega)
    have hty := hL.2.2 j.toNat (by omega)
    obtain ⟨-, -, -, -, h9, -⟩ := hty
    split at h
    · rename_i hne
      cases h
      refine ⟨fun h => absurd h (by decide), fun _ => ⟨j.toNat, by omega, fun h0 => hne ?_⟩⟩
      rw [wd_eq, hix, show to.toNat + 11 * j.toNat + 9 = to.toNat + 11 * j.toNat + 9 from rfl]
      apply UInt64.toNat_inj.mp; rw [h9.1, h0]; rfl
    · rename_i h0
      obtain ⟨i1, i2⟩ := ih (j + 1) u h
      rw [hj1] at i1
      refine ⟨fun hu k hk hjk => ?_, i2⟩
      by_cases hkj : k = j.toNat
      · subst hkj
        have : rdW (m.arr64 IFR) (to + 11 * j + 9) = 0 := Classical.byContradiction h0
        rw [wd_eq, hix] at this
        rw [← h9.1, this]; rfl
      · exact i1 hu k hk (by omega)


/-- **`vi_recs`' ok half**: the memory unchanged, and unless the block is nested, every recursor
record passes the twin's checks. -/
structure RecsPost (st : StateD) (a : AState) (m : Mem) (tys : List IndTypeRec)
    (np tn cn ke tyn tyt fuel : Word) (rcs : List IndRecRec) (v : Word × Mem) : Prop where
  mem : v.2 = m
  ok : ∀ r ∈ (if (tys.any fun x => x.numNested != 0) = true then [] else rcs),
    RecOK st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat) np.toNat tn.toNat
      cn.toNat (keOf ke) fuel.toNat r

/-- **`vi_recs`' error half**: a class-`≠ 0` error is an `.invalid`; the block is not nested and
the twin's recursor loop stops at a failing record. -/
def RecsErr (st : StateD) (a : AState) (m : Mem) (tys : List IndTypeRec)
    (np tn cn ke tyn tyt fuel : Word) (rcs : List IndRecRec) (e : Err) : Prop :=
  e.cls ≠ 0 → e.cls = 1 ∧ (tys.any fun x => x.numNested != 0) = false ∧
    RecsFail st a (islice m tyn.toNat tn.toNat) (islice m tyt.toNat tn.toNat) np.toNat tn.toNat
      cn.toNat (keOf ke) fuel.toNat rcs

/-- **`vi_recs`, both outcomes.** -/
theorem recs_ref {b : ByteArray} {m : Mem} {a : AState} {st : StateD} (hR : ArenaR m a)
    (hD : StateDR m st) {tys : List IndTypeRec} {rcs : List IndRecRec}
    {to tn ro rn np cn ke tyn tyt fuel : Word}
    (hTy : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63)
    (hL : ListF (RecF b m) m 11 ro.toNat rcs) (hrn : rn.toNat = rcs.length)
    (hro : ro.toNat + 11 * rcs.length < 2 ^ 63) (hnp : np.toNat < 10 ^ 18)
    (hke : ke = 0 ∨ ke = 1 ∨ ke = 2) (hb : tyn.toNat + tn.toNat ≤ 2 ^ 63)
    (hb' : tyt.toNat + tn.toNat ≤ 2 ^ 63)
    (hTN : ∀ k, k < tn.toNat → (wd m IFL (tyn.toNat + k)).toNat < 2 ^ 32) (p : Prog) (n : Nat) :
    RefC True (recsE p n m to tn ro rn np cn ke tyn tyt fuel)
      (RecsPost st a m tys np tn cn ke tyn tyt fuel rcs) (RecsErr st a m tys np tn cn ke tyn tyt fuel rcs) := by
  cases n with
  | zero => simp only [recsE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  rw [recsE.arm1]
  rcases hW : nestedW n m to tn 0 with _ | u
  · rw [liftE_none, recsE.k_vi_nested.none]; exact fun _ hk => absurd Err.cls_oob hk
  rw [liftE_some]
  obtain ⟨n1, n2⟩ := nestedW_twin hTy htn hto n 0 u hW
  by_cases hu : u ≠ 0
  · rw [recsE.k_vi_nested.arm1 p n tn ro rn np cn ke tyn tyt fuel m u hu]
    obtain ⟨k, hk, hk'⟩ := n2 hu
    have hany : (tys.any fun x => x.numNested != 0) = true := by
      rw [List.any_eq_true]; exact ⟨tys[k], List.getElem_mem hk, by simpa using hk'⟩
    exact ⟨rfl, fun r hr => by rw [hany] at hr; simp at hr⟩
  have hu' : u = 0 := Classical.byContradiction hu
  rw [recsE.k_vi_nested.arm2 p n tn ro rn np cn ke tyn tyt fuel m u hu']
  have hany : (tys.any fun x => x.numNested != 0) = false := by
    rw [List.any_eq_false]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    simp [n1 hu' k hk (Nat.zero_le _)]
  have hg := recsGo_ref hR hD hL hrn hro hnp hke hb hb' hTN p n 0 (st := st) (cn := cn) (fuel := fuel)
  rcases h2 : recsGoE p n m ro rn np tn cn ke tyn tyt fuel 0 with e2 | ⟨u2, m₂⟩ <;> rw [h2] at hg
  · rw [recsE.k_vi_recs_go.none]
    intro _ hk
    obtain ⟨hc, k, hk', -, k2, k3⟩ := hg trivial hk
    exact ⟨hc, hany, k, hk', fun i hi => k2 i hi (Nat.zero_le _), k3⟩
  rw [recsE.k_vi_recs_go.arm1]
  obtain ⟨hm, hok⟩ := hg
  refine ⟨hm, fun r hr => ?_⟩
  rw [hany] at hr
  simp only [Bool.false_eq_true, ite_false] at hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  exact hok k hk (Nat.zero_le _)

/-- **`vi_nparams`' ok half**: the memory unchanged, the result `nPd` (the first type's
`numParams`, `0` without types), every type agrees with it, and it is below `10^18`. -/
structure NparamsPost (m : Mem) (tys : List IndTypeRec) (v : Word × Mem) : Prop where
  mem : v.2 = m
  first : v.1.toNat = ((tys.map fun x => x.numParams).head?.getD 0)
  all : ((tys.map fun x => x.numParams).all fun x => x == v.1.toNat) = true
  small : v.1.toNat < 10 ^ 18

/-- **`vi_nparams`' error half**: an error of class `≠ 0` is the decline, the type records
disagree on `numParams`. -/
def NparamsFail (tys : List IndTypeRec) (e : Err) : Prop :=
  e.cls ≠ 0 → e = .abort R_INDUCTIVE_BLOCK_WHOSE ∧ ((tys.map fun x => x.numParams).all fun x =>
    x == (tys.map fun x => x.numParams).head?.getD 0) = false

/-- **`vi_nparams`, both outcomes.** -/
theorem nparams_ref {b : ByteArray} {m : Mem} {tys : List IndTypeRec} {to tn : Word}
    (hL : ListF (TyF b m) m 11 to.toNat tys) (htn : tn.toNat = tys.length)
    (hto : to.toNat + 11 * tys.length < 2 ^ 63) (p : Prog) (n : Nat) :
    RefC True (viNparamsE p n m to tn) (NparamsPost m tys) (NparamsFail tys) := by
  cases n with
  | zero => simp only [viNparamsE, RefC_error]; exact fun _ hk => absurd Err.cls_outOfFuel hk
  | succ n =>
  by_cases h0 : tn = 0
  · rw [viNparamsE.arm1 p n m to tn h0]
    have : tys = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← htn, h0]; rfl
    subst this
    exact ⟨rfl, by simp, by simp, by simp⟩
  rw [viNparamsE.arm2 p n m to tn h0]
  have hne : tys ≠ [] := fun e => h0 (by apply UInt64.toNat_inj.mp; rw [htn, e]; rfl)
  have h0' : 0 < tys.length := by cases tys with | nil => exact absurd rfl hne | cons _ _ => simp
  have hix : (to + 10).toNat = to.toNat + 10 := widx2 _ _ (by simp; omega)
  obtain ⟨-, -, -, -, -, h10⟩ := hL.2.2 0 h0'
  simp only [Nat.mul_zero, Nat.add_zero] at h10
  have hd : (rdW (m.arr64 IFR) (to + 10)).toNat = tys[0].numParams := by rw [wd_eq, hix, h10.1]
  have hg := npGo_ref hL htn hto p n (d := rdW (m.arr64 IFR) (to + 10)) 0
  rcases h1 : viNpGoE p n m to tn (rdW (m.arr64 IFR) (to + 10)) 0 with e1 | ⟨u, mg⟩ <;> rw [h1] at hg
  · rw [viNparamsE.k_vi_np_go.none]
    intro _ hk
    obtain ⟨he, k, hk', -, hne'⟩ := hg trivial hk
    refine ⟨he, ?_⟩
    rw [hd] at hne'
    rw [List.all_eq_false]
    refine ⟨tys[k].numParams, List.mem_map.mpr ⟨tys[k], List.getElem_mem hk', rfl⟩, ?_⟩
    cases tys with
    | nil => simp at h0'
    | cons t ts => simpa using hne'
  rw [viNparamsE.k_vi_np_go.arm1]
  obtain ⟨hmg, hall⟩ := hg
  have hfirst := hall 0 h0' (Nat.zero_le _)
  refine ⟨hmg, ?_, ?_, ?_⟩
  · dsimp only; rw [← hfirst]
    cases tys with
    | nil => exact absurd rfl hne
    | cons t ts => rfl
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    simp [hall k hk (Nat.zero_le _)]
  · dsimp only; rw [← hfirst]; exact h10.2

end L.Front.Ind
