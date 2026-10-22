import ConAgua.Arena.IndInstallSpec17

/-!
# Refinements of `IndInstall`, part 18 (lane `indproofs2`, helper `install`): `checkBlockIdxSorts`,
the relation
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A pointer to `[off, len]` of level handles. -/
def decIS (m : Mem) (rp : Nat) : Option (List LIdx) := decAt m (decHL m) rp

theorem decIS_mono (q : Nat) : OMono (fun m => decIS m q) :=
  OMono.decAt (fun o l => OMono.decHL o l) q

/-- **A model-only tail** after the twin's last step. -/
theorem Sim.tail {β γ α : Type} {K : Option (β × Mem) → Option (γ × Mem)} {body : β → Mem → Option (γ × Mem)}
    {mo : Option (β × Mem)} {op : AM α} {a : AState} {Q : β → α → Mem → AState → Prop}
    {R : γ → α → Mem → AState → Prop}
    (hn : K Option.none = Option.none) (hs : ∀ r m₁, K (some (r, m₁)) = body r m₁)
    (h : Sim mo op a Q) (h2 : ∀ r x m₁ a₁, Q r x m₁ a₁ → ∀ r' m', body r m₁ = some (r', m') → R r' x m' a₁) :
    Sim (K mo) op a R := by
  intro r' m' e
  cases hmo : mo with
  | none => rw [hmo, hn] at e; cases e
  | some x =>
    obtain ⟨r, m₁⟩ := x
    rw [hmo, hs] at e
    obtain ⟨y, a₁, h1, hq⟩ := h r m₁ hmo
    exact ⟨y, a₁, h1, h2 r y m₁ a₁ hq r' m' e⟩

/-- One member's index sorts, as the twin computes them. -/
def idxOneAM (fe : IFEnv) (bs : BlockShape) (ms : MemberShape) (cvTa : IConstantVal) : AM (List LIdx) := do
  let tq ← unwrapOr (← openPisAtFvarsF (bs.nP + ms.nIdx) cvTa.type 0)
    (.internal "direct rec: type former telescope")
  checkStructFieldSortsI V fe true false bs.resSort bs.nP (tq.1.drop bs.nP) [] ms.nIdx

theorem installIdx_cons (fe : IFEnv) (bs : BlockShape) (ms : MemberShape) (rest : List MemberShape)
    (cvTa : IConstantVal) (cvTas : List IConstantVal) :
    ConRon.Arena.checkBlockIdxSorts V fe bs (ms :: rest) (cvTa :: cvTas) =
      (idxOneAM fe bs ms cvTa >>= fun is =>
        ConRon.Arena.checkBlockIdxSorts V fe bs rest cvTas >>= fun rs => pure (is :: rs)) := by
  simp only [ConRon.Arena.checkBlockIdxSorts, idxOneAM, bind_assoc]

/-- A handle slice whose tail past `k` is taken: `idxTail`'s slice. -/
theorem installIdxTail {m : Mem} {o l : Word} {xs : List EIdx} {k : Word}
    (hd : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    decHL m (idxTail k o l).1.toNat (idxTail k o l).2.toNat = some (xs.drop k.toNat) ∧
      (idxTail k o l).1.toNat + (idxTail k o l).2.toNat ≤ iwTop m := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlen := decHL_length m hd
  unfold idxTail
  split
  · rename_i hk
    have hk' : k.toNat < l.toNat := hk
    have e1 : (o + k).toNat = o.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
    have e2 : (l - k).toNat = l.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; omega)
    rw [e1, e2]
    exact ⟨decHL_drop k.toNat hd (by omega), by omega⟩
  · rename_i hk
    have hk' : ¬ k.toNat < l.toNat := hk
    have : xs.drop k.toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    exact ⟨by simp [decHL, hslice?], by simp⟩

/-- The lookups of `check_block_idx_sorts`. -/
structure IdxProg (p : Prog) : Prop extends CstProg p where
  rec2 : p.lookup "rec2" = some rec2
  one : p.lookup "check_block_idx_sorts_one" = some checkBlockIdxSortsOne
  idx : p.lookup "check_block_idx_sorts" = some checkBlockIdxSorts

/-- **`check_block_idx_sorts_one`'s model refines one member's index sorts.** -/
theorem iisW_sim {p : Prog} (hP : IdxProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {pp ms cv : Word} {bs : BlockShape}
    {msh : MemberShape} {cvv : IConstantVal}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcv : DecB (fun m => decCVp m cv.toNat) m cvv) :
    Sim (iisW p n m vis pp ms cv) (idxOneAM fe bs msh cvv) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decIS m (r.headD 0).toNat) m' x) := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hq hq9
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨-, hni, -⟩ := decMS_some hmsT
  have hnilt := partsIwLt hni
  obtain ⟨hw1, hnib, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨htyl, htye⟩ := partsCVType hcv (w := cv) rfl
  unfold iisW
  rw [hnpw, hw1]
  split
  · exact Sim.of_none
  rename_i hov
  have hk : (UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx : Word).toNat = bs.nP + msh.nIdx := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib]
  unfold idxOneAM
  refine Sim.bindK (K := iisK1 p n vis (UInt64.ofNat bs.nP) (UInt64.ofNat msh.nIdx) (rdW (m.arr64 IW) (pp + 6)))
    (body := fun r1 m1 => if r1.headD 0 = 0 then none else iisK2 p n (callW p n "check_struct_field_sorts_i"
      [vis, 1, 0, rdW (m.arr64 IW) (pp + 6), UInt64.ofNat bs.nP,
        (idxTail (UInt64.ofNat bs.nP) (r1.tail.headD 0) (r1.tail.tail.headD 0)).1,
        (idxTail (UInt64.ofNat bs.nP) (r1.tail.headD 0) (r1.tail.tail.headD 0)).2, 0, 0,
        UInt64.ofNat msh.nIdx] m1)) (by simp [iisK1])
    (fun r m₁ => by
      by_cases h : r.headD 0 = 0
      · rw [iisK1_none p n m₁ _ _ _ _ r h, if_pos h]
      · rw [iisK1_some p n m₁ _ _ _ _ r h, if_neg h])
    (by
      have h := installSimKeep (p := p) (n := n) (openPisAtFvarsF_spec dn vis fe
        (UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx) _ 0 htyl) hS
      rw [hk, htye] at h; exact h) ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, if_true]; exact Sim.of_none
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  simp only [h1', show (1 : Word) ≠ 0 by decide, if_false]
  show Sim _ (checkStructFieldSortsI V fe true false bs.resSort bs.nP (fvs.drop bs.nP) [] msh.nIdx) a1 _
  obtain ⟨hdT, hbT⟩ := installIdxTail (k := UInt64.ofNat bs.nP) hfd hfb
  rw [UInt64.toNat_ofNat_of_lt' hnpb] at hdT
  refine Sim.tail (K := iisK2 p n) (body := fun r2 m2 => iisK3 (callW p n "rec2"
      [r2.headD 0, r2.tail.headD 0] m2)) rfl (fun _ _ => rfl)
    (by
      have h := installSimStub (p := p) (n := n) (checkStructFieldSortsI_pending dn vis fe 1 0
        (rdW (m.arr64 IW) (pp + 6)) (UInt64.ofNat bs.nP) _ _ 0 0 (UInt64.ofNat msh.nIdx) hrs32
        (fvs.drop bs.nP) []) ⟨hS1, hdT, hbT, by simp [decHL, hslice?], by simp⟩
      rw [hrse, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib,
        show ((1 : Word) != 0) = true from rfl, show ((0 : Word) != 0) = false from rfl] at h
      exact h) ?_
  rintro r2 isorts m2 a2 ⟨hS2, hg2, hd2⟩ r' m' e
  cases h3 : callW p n "rec2" [r2.headD 0, r2.tail.headD 0] m2 with
  | none => rw [h3] at e; cases e
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3, iisK3_some] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h3
  obtain ⟨hS3, hg3, hr3, hget, htop⟩ := recW_stage hW3 hS2 rfl
  subst hr3
  refine ⟨hS3, (hg1.trans hg2).trans hg3, ?_⟩
  simp only [List.headD_cons]
  obtain ⟨hdl, hbl⟩ := hd2
  simp only [show (0 : Nat) + 1 = 1 from rfl] at hdl hbl
  have e0 : r2.getD 0 0 = r2.headD 0 := by rcases r2 with _ | ⟨_, _⟩ <;> rfl
  have e1 : r2.getD 1 0 = r2.tail.headD 0 := by rcases r2 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  rw [e0, e1] at hdl hbl
  have hq0 : (rdW (m2.arr64 CTL) 200).toNat < iwTop s3.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m2.arr64 CTL) 200).toNat + 1 < iwTop s3.mem := by rw [htop]; simp [iwTop]
  show decIS (truncM s3.mem) _ = some isorts
  have w0 : iwN (truncM s3.mem) (rdW (m2.arr64 CTL) 200).toNat = some (r2.headD 0).toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM s3.mem) ((rdW (m2.arr64 CTL) 200).toNat + 1) = some (r2.tail.headD 0).toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hdB := (decHL_decB hdl hbl).grow (OMono.decHL _ _) hg3
  simp only [decIS, decAt, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hdB

end L.Ind
