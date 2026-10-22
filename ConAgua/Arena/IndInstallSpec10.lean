import ConAgua.Arena.IndInstallSpec9

/-!
# Refinements of `IndInstall`, part 10 (lane `indproofs2`, helper `install`): `checkBlockAgree`

Recursion on the other members, member 0's telescope opened per member as the twin does
(`open_pis_at_fvars_f`'s stub), then helper `install`'s `check_block_agree_one` (the twin's
`agreeBodyAM`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem installIteBind {α β : Type} (c : Prop) [Decidable c] (x y : AM α) (f : α → AM β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

/-- The twin's `checkBlockAgree` at a member: member 0's telescope, the member's body, the rest. -/
theorem installAgree_cons (fe : IFEnv) (nP : Nat) (cvTa₀ cvTa : IConstantVal) (s₀ s : LIdx)
    (rest : List (IConstantVal × LIdx)) :
    ConRon.Arena.checkBlockAgree V fe nP cvTa₀ s₀ ((cvTa, s) :: rest) =
      (openPisAtFvarsF nP cvTa₀.type 0 >>= fun x =>
        unwrapOr x (.internal "block: type former telescope") >>= fun tq₀ =>
        agreeBodyAM fe nP tq₀.1 cvTa s s₀ >>= fun _ =>
        ConRon.Arena.checkBlockAgree V fe nP cvTa₀ s₀ rest) := by
  simp only [ConRon.Arena.checkBlockAgree, agreeBodyAM, bind_assoc, installIteBind, pure_bind]

/-- After the rest. -/
def iagK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([0], m)

mutual
/-- **The model of `check_block_agree(vis, nP, c0, s0, o, l)`** at exec fuel `n`. -/
def iagW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, nP, c0, s0, o, l =>
    if l = 0 then some ([0], m)
    else iagK1 p n vis nP c0 s0 o l (callW p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (c0 + 3), 0] m)
/-- After member 0's telescope. -/
def iagK1 (p : Prog) (n : Nat) (vis nP c0 s0 o l : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else iagK2 p n vis nP c0 s0 o l (callW p n "check_block_agree_one" [vis, nP, r.tail.headD 0,
      r.tail.tail.headD 0, s0, rdW (m.arr64 IW) (rdW (m.arr64 IW) o),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1)] m)
/-- After the member's agreements: the rest. -/
def iagK2 (p : Prog) (n : Nat) (vis nP c0 s0 o l : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => iagK3 (iagW p n m vis nP c0 s0 (o + 1) (l - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis nP c0 s0 o l : Word) (r : List Word)
theorem iagW_zero : iagW p 0 m vis nP c0 s0 o l = none := by simp [iagW]
theorem iagW_nil (h : l = 0) : iagW p (n + 1) m vis nP c0 s0 o l = some ([0], m) := by simp [iagW, h]
theorem iagW_cons (h : l ≠ 0) : iagW p (n + 1) m vis nP c0 s0 o l =
    iagK1 p n vis nP c0 s0 o l (callW p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (c0 + 3), 0] m) := by
  simp [iagW, h]
theorem iagK1_none (h : r.headD 0 = 0) : iagK1 p n vis nP c0 s0 o l (some (r, m)) = none := by
  simp only [iagK1, h, ↓reduceIte]
theorem iagK1_some (h : ¬ r.headD 0 = 0) : iagK1 p n vis nP c0 s0 o l (some (r, m)) =
    iagK2 p n vis nP c0 s0 o l (callW p n "check_block_agree_one" [vis, nP, r.tail.headD 0,
      r.tail.tail.headD 0, s0, rdW (m.arr64 IW) (rdW (m.arr64 IW) o),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1)] m) := by simp only [iagK1, h, ↓reduceIte, if_false]
theorem iagK2_some : iagK2 p n vis nP c0 s0 o l (some (r, m)) =
    iagK3 (iagW p n m vis nP c0 s0 (o + 1) (l - 1)) := by simp [iagK2]
theorem iagK3_some : iagK3 (some (r, m)) = some ([0], m) := rfl
end arms
attribute [ind_grind] iagW_nil iagW_cons iagK1_none iagK1_some iagK2_some iagK3_some

theorem iag_spec (p : Prog) (hp : p.lookup "check_block_agree" = some checkBlockAgree) (n : Nat) :
    ∀ (s₀ : St) (vis nP c0 s0 o l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_agree" [vis, nP, c0, s0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ iagW p n s₀.mem vis nP c0 s0 o l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis nP c0 s0 o l; rw [invoke_eq _ hp]; simp only [callFn, checkBlockAgree]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis nP c0 s0 o l
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockAgree]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "open_pis_at_fvars_f", callW_spec p n "check_block_agree_one", ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The lookups of `check_block_agree`. -/
structure AgreeProg (p : Prog) : Prop where
  doms : p.lookup "check_block_doms_at" = some checkBlockDomsAt
  lvl : p.lookup "lvl_eq_fueled" = some lvlEqFueled
  one : p.lookup "check_block_agree_one" = some checkBlockAgreeOne
  agree : p.lookup "check_block_agree" = some checkBlockAgree

/-- **`check_block_agree`'s model refines `checkBlockAgree`.** -/
theorem iagW_sim (p : Prog) (hP : AgreeProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (nP c0 s0 : Word) (cv0 : IConstantVal) (n : Nat) :
    ∀ (m : Mem) (a : AState) (o l : Word) (rest : List (IConstantVal × LIdx)),
    StageR dn vis fe m a → DecB (fun m => decCVp m c0.toNat) m cv0 → H s0 →
    PSlR decTele rest o l m →
    Sim (iagW p n m vis nP c0 s0 o l) (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a
      (fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m m') := by
  induction n with
  | zero => intro m a o l rest _ _ _ _; rw [iagW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a o l rest hS hc0 hs0 hrest
  by_cases hl : l = 0
  · rw [iagW_nil p n m vis nP c0 s0 o l hl]
    have : rest = [] := by
      have h := hrest.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hS, IWGrow.refl m⟩
  obtain ⟨q, ⟨cvTa, sx⟩, rest', rfl, hw, hqb, hdx, hrest'⟩ := partsPSl_cons hrest hl
  rw [iagW_cons p n m vis nP c0 s0 o l hl, installAgree_cons]
  obtain ⟨hty0, htye0⟩ := partsCVType hc0 (w := c0) rfl
  refine Sim.bindK (K := iagK1 p n vis nP c0 s0 o l) (body := fun r1 m1 => if r1.headD 0 = 0 then none
      else iagK2 p n vis nP c0 s0 o l (callW p n "check_block_agree_one" [vis, nP, r1.tail.headD 0,
        r1.tail.tail.headD 0, s0, rdW (m1.arr64 IW) (rdW (m1.arr64 IW) o),
        rdW (m1.arr64 IW) (rdW (m1.arr64 IW) o + 1)] m1)) (by simp [iagK1])
      (fun r m₁ => by
        by_cases h : r.headD 0 = 0
        · rw [iagK1_none p n m₁ vis nP c0 s0 o l r h, if_pos h]
        · rw [iagK1_some p n m₁ vis nP c0 s0 o l r h, if_neg h])
    (by
      have h := installSimKeep (p := p) (n := n) (openPisAtFvarsF_spec dn vis fe nP _ 0 hty0) hS
      rw [htye0] at h; exact h) ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, if_true]; exact Sim.of_none
  | some fb =>
  obtain ⟨fvs0, body0⟩ := fb
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  simp only [h1', show (1 : Word) ≠ 0 by decide, if_false]
  show Sim _ (agreeBodyAM fe nP.toNat fvs0 cvTa sx (decI s0) >>= fun _ =>
    ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest') a1 _
  -- the member's record words, read in `m1`
  have hd1x : decTele (truncM m1) q = some (cvTa, sx) := hdx.grow (decTele_mono _) hg1
  simp only [decTele, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hd1x
  obtain ⟨c, hc, cvv, hcv, sv, hsv, rfl, rfl⟩ := hd1x
  have hT1 : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hol : o.toNat < iwTop m := by
    have := hrest.2
    have : 0 < l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
      · exact h0
    omega
  have hw1 : rdW (m1.arr64 IW) o = UInt64.ofNat q := by
    rw [← hw]; simp only [rdW]; rw [hg1.2.2.1 _ hol]
  rw [hw1]
  obtain ⟨hwc, hcb, -⟩ := partsIwRd hc (w := UInt64.ofNat q) hq'
  obtain ⟨-, hsv'⟩ := rec2IwH_trunc hsv
  obtain ⟨v, hv, hv32, hve⟩ := iwH_rdW_at (w := UInt64.ofNat q) (k := 1) (by rw [hq']; exact hsv')
    hS1.2.2.2.1
  rw [show (UInt64.ofNat 1 : Word) = 1 from rfl] at hv
  rw [hwc, hv]
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hty := partsCVType hcv (w := UInt64.ofNat c) hc'
  rw [← hve]
  refine Sim.bindK (K := iagK2 p n vis nP c0 s0 o l) (body := fun _ m2 =>
      iagK3 (iagW p n m2 vis nP c0 s0 (o + 1) (l - 1))) (by simp [iagK2]) (fun _ _ => by simp [iagK2])
    (Sim.callW_pos (fun k => installSimCall
      (Q := fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m1 m') (checkBlockAgreeOne_refines p hP.doms hP.lvl hP.one k
      ⟨m1, Locals.init []⟩ a1 dn fe vis nP _ _ s0 _ v cvv fvs0 hS1 hty hfd hfb hv32 hs0)
      fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩) n) ?_
  rintro - - m2 a2 ⟨hS2, hg2⟩
  refine Sim.post (K := iagK3) rfl (fun _ _ => rfl)
    (ih m2 a2 (o + 1) (l - 1) rest' hS2 (hc0.grow (OMono.decCVp _) (hg1.trans hg2)) hs0
      (hrest'.grow decTele_mono (hg1.trans hg2))) ?_
  rintro _ _ _ _ ⟨hS3, hg3⟩
  exact ⟨hS3, (hg1.trans hg2).trans hg3⟩

/-- **`check_block_agree` refines `checkBlockAgree`** (through `open_pis_at_fvars_f`'s,
`fvar_type_ds`', `fvar_type_d`'s, `is_def_eq_core`'s and `lvl_eq_c`'s stubs): member 0's constant
decoded below the tops, its sort a handle, the other members a slice of checked formers. -/
@[refines ConRon.Arena.checkBlockAgree]
theorem checkBlockAgree_refines (p : Prog) (hP : AgreeProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nP c0 s0 o l : Word)
    (cv0 : IConstantVal) (rest : List (IConstantVal × LIdx)) (hS : StageR dn vis fe s₀.mem a₀)
    (hc0 : DecB (fun m => decCVp m c0.toNat) s₀.mem cv0) (hs0 : H s0)
    (hrest : PSlR decTele rest o l s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_agree" [vis, nP, c0, s0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (iag_spec p hP.agree n s₀ vis nP c0 s0 o l) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (iagW_sim p hP dn vis fe nP c0 s0 cv0 n _ a₀ o l rest hS hc0 hs0 hrest) hm
    ⟨hl, hok, hQ⟩

end L.Ind
