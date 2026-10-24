import ConAgua.Arena.IndInstallSpec8

/-!
# Refinements of `IndInstall`, part 9 (lane `indproofs2`, helper `install`): `checkBlockTeles`

The members' formers, by recursion as the twin's; each `[cvTa, s]` record consed onto the rest's
slice (`sl_cons`, D18), so every written word lies above the old pool top and the decodings stay
stable (`partsConsPL`).
-/

noncomputable section

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The member slice -/

/-- A slice of member records: decoded below the tops, every former's constant record below the
tops (`CVExt`). -/
def MemsOK (m : Mem) (o l : Word) (mss : List MemberShape) : Prop :=
  PSlR decMS mss o l m ∧
    ∀ j < l.toNat, ∀ c, iwN m (o.toNat + j) = some c → ∀ d, iwN m c = some d → CVExt m d

theorem MemsOK.grow {m m' : Mem} {o l : Word} {mss : List MemberShape} (h : MemsOK m o l mss)
    (hg : IWGrow m m') : MemsOK m' o l mss := by
  obtain ⟨hp, hx⟩ := h
  refine ⟨hp.grow decMS_mono hg, fun j hj c hc d hd => ?_⟩
  have hb := hp.2
  have hoj : o.toNat + j < iwTop m := by omega
  rw [iwN_grow hg hoj] at hc
  -- the member pointer `c` is decoded below the top
  have hd0 := hp.1
  simp only [DecB] at hd0
  obtain ⟨v, hv, x, hx', -⟩ : ∃ v, iwN (truncM m) (o.toNat + j) = some v ∧ ∃ x, decMS (truncM m) v = some x ∧ True := by
    have hlen := decPL_length _ hd0
    obtain ⟨v, y, hv, hy, -⟩ := decPL_get l.toNat o.toNat mss hd0 j hj
    exact ⟨v, hv, y, hy, trivial⟩
  rw [iwN_truncM hoj, hc] at hv
  cases hv
  obtain ⟨⟨c', hc', -⟩, -, -⟩ := decMS_some hx'
  obtain ⟨hclt, -⟩ := rec2IwN_trunc hc'
  rw [iwN_grow hg hclt] at hd
  exact CVExt_grow hg (hx j hj c hc d hd)

theorem MemsOK.cons {m : Mem} {o l : Word} {mss : List MemberShape} (h : MemsOK m o l mss)
    (hl : l ≠ 0) : ∃ q x rest, mss = x :: rest ∧ rdW (m.arr64 IW) o = UInt64.ofNat q ∧ q < 2 ^ 64 ∧
      MemOK m (UInt64.ofNat q : Word).toNat x ∧ MemsOK m (o + 1) (l - 1) rest := by
  obtain ⟨hp, hx⟩ := h
  obtain ⟨q, x, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hp hl
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlpos : 0 < l.toNat := by
    rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
    · exact h0
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 := ⟨l.toNat - 1, by omega⟩
  have hd1 : decPL (truncM m) (decMS (truncM m)) o.toNat (L + 1) = some (x :: rest) := by
    have := hp.1; simp only [DecB, hL] at this; exact this
  obtain ⟨v, hv, -⟩ := decPL_head hd1
  obtain ⟨hwv, -, -⟩ := partsIwRd hv rfl
  have hvq : v = q := by
    have h1 := congrArg UInt64.toNat (hwv.symm.trans hw)
    rw [UInt64.toNat_ofNat_of_lt' (partsIwRd hv rfl).2.1, hq'] at h1; exact h1
  subst hvq
  obtain ⟨-, hvm⟩ := rec2IwN_trunc hv
  have ho1 : (o + 1).toNat = o.toNat + 1 := by
    have := hp.2; rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = L := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  refine ⟨v, x, rest, rfl, hw, hqb, ⟨by rw [hq']; exact hdx, fun c hc => ?_⟩, hrest, ?_⟩
  · rw [hq'] at hc; exact hx 0 hlpos v (by simpa using hvm) c hc
  · intro j hj c hc d hd
    rw [ho1] at hc; rw [hl1] at hj
    exact hx (j + 1) (by omega) c (by rw [show o.toNat + (j + 1) = o.toNat + 1 + j by omega]; exact hc) d hd

/-! ## `check_block_teles` -/

/-- A checked former's record `[cvTa, s]`. -/
def decTele (m : Mem) (rp : Nat) : Option (IConstantVal × LIdx) := do
  pure (← decCVp m (← iwN m rp), ← iwH m (rp + 1))

theorem decTele_mono (q : Nat) : OMono (fun m => decTele m q) := by
  unfold decTele
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.iwH
    | apply OMono.decCVp
    | apply OMono.bind
    | intro _
    )

/-- After `sl_cons`. -/
def ibtsK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)
/-- After the rest. -/
def ibtsK3 (p : Prog) (n : Nat) (rp : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ibtsK4 (callW p n "sl_cons" [rp, r.headD 0, r.tail.headD 0] m)

mutual
/-- **The model of `check_block_teles(vis, nP, o, l)`** at exec fuel `n`. -/
def ibtsW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, vis, nP, o, l =>
    if l = 0 then some ([0, 0], m)
    else ibtsK1 p n vis nP o l (callW p n "check_block_tele" [vis, nP, rdW (m.arr64 IW) o] m)
/-- After `check_block_tele`. -/
def ibtsK1 (p : Prog) (n : Nat) (vis nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ibtsK2 p n vis nP o l (callW p n "rec2" [r.headD 0, r.tail.headD 0] m)
/-- After `rec2`: the rest, then the cons. -/
def ibtsK2 (p : Prog) (n : Nat) (vis nP o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ibtsK3 p n (r.headD 0) (ibtsW p n m vis nP (o + 1) (l - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis nP o l rp : Word) (r : List Word)
theorem ibtsW_nil (h : l = 0) : ibtsW p (n + 1) m vis nP o l = some ([0, 0], m) := by simp [ibtsW, h]
theorem ibtsW_cons (h : l ≠ 0) : ibtsW p (n + 1) m vis nP o l =
    ibtsK1 p n vis nP o l (callW p n "check_block_tele" [vis, nP, rdW (m.arr64 IW) o] m) := by
  simp [ibtsW, h]
theorem ibtsK1_some : ibtsK1 p n vis nP o l (some (r, m)) =
    ibtsK2 p n vis nP o l (callW p n "rec2" [r.headD 0, r.tail.headD 0] m) := by simp [ibtsK1]
theorem ibtsK2_some : ibtsK2 p n vis nP o l (some (r, m)) =
    ibtsK3 p n (r.headD 0) (ibtsW p n m vis nP (o + 1) (l - 1)) := by simp [ibtsK2]
theorem ibtsK3_some : ibtsK3 p n rp (some (r, m)) =
    ibtsK4 (callW p n "sl_cons" [rp, r.headD 0, r.tail.headD 0] m) := rfl
theorem ibtsK4_some : ibtsK4 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
theorem ibtsW_zero : ibtsW p 0 m vis nP o l = none := by simp [ibtsW]
end arms
attribute [ind_grind] ibtsW_nil ibtsW_cons ibtsK1_some ibtsK2_some ibtsK3_some ibtsK4_some

theorem ibts_spec (p : Prog) (hp : p.lookup "check_block_teles" = some checkBlockTeles) (n : Nat) :
    ∀ (s₀ : St) (vis nP o l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_teles" [vis, nP, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ibtsW p n s₀.mem vis nP o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis nP o l; rw [invoke_eq _ hp]; simp only [callFn, checkBlockTeles]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis nP o l
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockTeles]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "check_block_tele", callW_spec p n "rec2", callW_spec p n "sl_cons", ih] <;>
      finish (gen := 20) [rdW_eq]

/-! ## The relation -/

/-- **A model-only step** (an L allocation the twin does not make): every run of it continues
simulated. -/
theorem Sim.mstep {β γ α : Type} {K : Option (β × Mem) → Option (γ × Mem)} {body : β → Mem → Option (γ × Mem)}
    {mo : Option (β × Mem)} {op : AM α} {a : AState} {R : γ → α → Mem → AState → Prop}
    (hn : K Option.none = Option.none) (hs : ∀ r m₁, K (some (r, m₁)) = body r m₁)
    (h : ∀ r m₁, mo = some (r, m₁) → Sim (body r m₁) op a R) : Sim (K mo) op a R := by
  cases hmo : mo with
  | none => rw [hn]; exact Sim.of_none
  | some x => obtain ⟨r, m₁⟩ := x; rw [hs]; exact h r m₁ hmo

/-- A model step that only reshapes the result (the twin does nothing more). -/
theorem Sim.post {β γ α : Type} {K : Option (β × Mem) → Option (γ × Mem)} {f : β → γ}
    {mo : Option (β × Mem)} {op : AM α} {a : AState} {Q : β → α → Mem → AState → Prop}
    {R : γ → α → Mem → AState → Prop}
    (hn : K Option.none = Option.none) (hs : ∀ r m₁, K (some (r, m₁)) = some (f r, m₁))
    (h : Sim mo op a Q) (hq : ∀ r x m a', Q r x m a' → R (f r) x m a') : Sim (K mo) op a R := by
  intro r m' e
  cases hmo : mo with
  | none => rw [hmo, hn] at e; cases e
  | some x =>
    obtain ⟨r₁, m₁⟩ := x
    rw [hmo, hs] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨y, a', h1, h2⟩ := h r₁ m₁ hmo
    exact ⟨y, a', h1, hq _ _ _ _ h2⟩

/-- The lookups of this module's parents. -/
structure InstProg (p : Prog) : Prop extends CstProg p where
  rec2 : p.lookup "rec2" = some rec2
  bTele : p.lookup "check_block_tele" = some checkBlockTele
  bTeles : p.lookup "check_block_teles" = some checkBlockTeles

/-- **A `rec2` record of a checked former**, decoded below the tops. -/
theorem installRec2Tele {p : Prog} (hP : InstProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m m1 m2 : Mem} {a : AState} {r1 r2 : List Word} {x : IConstantVal × LIdx}
    (hT : TeleOut dn vis fe m r1 x m1 a)
    (h : callW p n "rec2" [r1.headD 0, r1.tail.headD 0] m1 = some (r2, m2)) :
    StageR dn vis fe m2 a ∧ IWGrow m m2 ∧ DecB (fun m => decTele m (r2.headD 0).toNat) m2 x ∧
      (r2.headD 0).toNat < iwTop m2 := by
  obtain ⟨hS1, hg1, hcv, hcx, hs32, hsd⟩ := hT
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h
  obtain ⟨hS2, hg2, hr, hget, htop⟩ := recW_stage hW hS1 rfl
  refine ⟨hS2, hg1.trans hg2, ?_, ?_⟩
  · subst hr
    have hq0 : (rdW (m1.arr64 CTL) 200).toNat < iwTop s'.mem := by rw [htop]; simp [iwTop]
    have hq1 : (rdW (m1.arr64 CTL) 200).toNat + 1 < iwTop s'.mem := by rw [htop]; simp [iwTop]
    show decTele (truncM s'.mem) _ = some x
    have e0 : iwN (truncM s'.mem) (rdW (m1.arr64 CTL) 200).toNat = some (r1.headD 0).toNat := by
      rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
      simp [iwN, nat?, iwA, this]
    have e1 : (iwH (truncM s'.mem) ((rdW (m1.arr64 CTL) 200).toNat + 1) : Option LIdx) = some x.2 := by
      rw [iwH_truncM hq1]; have h1 := hget 1 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h1
      simp only [iwH, hd?, iwA, h1, Option.bind_eq_bind, Option.bind_some]
      rw [if_pos hs32, hsd]
    have e2 : decCVp (truncM s'.mem) (r1.headD 0).toNat = some x.1 :=
      (installCvDecB hcv hcx).grow (OMono.decCVp _) hg2
    simp only [decTele, List.headD_cons, e0, e1, bind, Option.bind_some, e2, pure]
  · subst hr; rw [htop]; simp [iwTop]

end L.Ind
