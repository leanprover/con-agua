import ConAgua.Arena.IndPos2SpecF

/-! # `IndPos2`'s leaves, continued (lane `indproofs2`, helper `pos`, fork E): `nestUniform`; small-fuel
facts (`invoke_exec0`: a call at exec fuel `0` never returns). -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena

/-- A call at exec fuel `0` never returns. -/
theorem invoke_exec0 (p : Prog) (f : FnName) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p 0) f vs ⦃fun _ _ => False; ⊤⦄ := by
  simp only [invoke, callFn, lookupFn]
  vcgen [exec] <;> grind

theorem cvLps_exec1 (p : Prog) (hcv : p.lookup "cv_lps" = some cvLps) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p 1) "cv_lps" [q] ⦃fun _ _ => False; ⊤⦄ := by
  rw [invoke_eq _ hcv]; simp only [callFn, cvLps]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish

theorem rootCanon_small (p : Prog) (hcv : p.lookup "cv_lps" = some cvLps)
    (hp : p.lookup "nest_root_canon" = some nestRootCanonL) (k : Nat) (hk : k ≤ 2) (s₀ : St) (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_root_canon" [ctx, cv] ⦃fun _ _ => False; ⊤⦄ := by
  match k, hk with
  | 0, _ => exact invoke_exec0 p _ _ s₀
  | 1, _ =>
    rw [invoke_eq _ hp]; simp only [callFn, nestRootCanonL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish
  | 2, _ =>
    rw [invoke_eq _ hp]; simp only [callFn, nestRootCanonL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, cvLps_exec1 p hcv] <;> finish
  | _ + 3, h => exact absurd h (by omega)

/-- `nest_uniform_ok` at any exec fuel (below `4` it never returns). -/
def nuWf (cR : CallM) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | k + 4, m, ctx, cv => nuW cR k m ctx cv
  | _, _, _, _ => none

theorem nestUniformOk_spec' (p : Prog) (hl : NuLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform_ok" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nuWf cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  match k with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | 1 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_exec0 p] <;> finish
  | 2 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtxHiAt_specE p hl.hh 1, piDomsOcc_spec p hl.no hl.hpd 1,
        rootCanon_small p hl.hcv hl.pcc.hp' 1 (by omega)] <;> finish [pdoW, pdoK1, noConstWf]
  | 3 =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, nestUniformOkL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtxHiAt_specE p hl.hh 2, piDomsOcc_spec p hl.no hl.hpd 2,
        rootCanon_small p hl.hcv hl.pcc.hp' 2 (by omega)] <;>
      finish [pdoW, pdoK1, noConstWf, noConstW, noClrK, noGoW]
  | k + 4 => exact nestUniformOk_spec p hl cR hcR k s₀ ctx cv

mutual
def ucW (cR : CallM) : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, ctx, o, l =>
    if l = 0 then some ([1], m) else ucK cR k ctx o l (nuWf cR k m ctx (rdW (m.arr64 IW) (rdW (m.arr64 IW) o)))
def ucK (cR : CallM) (k : Nat) (ctx o l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then some ([0], m1) else ucW cR k m1 ctx (o + 1) (l - 1)
end

section arms
variable (cR : CallM) (k : Nat) (m m1 : Mem) (ctx o l : Word) (r : List Word)
theorem ucW_nil (h : l = 0) : ucW cR (k + 1) m ctx o l = some ([1], m) := by simp [ucW, h]
theorem ucW_cons (h : ¬ l = 0) : ucW cR (k + 1) m ctx o l =
    ucK cR k ctx o l (nuWf cR k m ctx (rdW (m.arr64 IW) (rdW (m.arr64 IW) o))) := by simp [ucW, h]
theorem ucK_no (h : r.headD 0 = 0) : ucK cR k ctx o l (some (r, m1)) = some ([0], m1) := by rw [ucK, ite_eq_left h]
theorem ucK_yes (h : ¬ r.headD 0 = 0) : ucK cR k ctx o l (some (r, m1)) = ucW cR k m1 ctx (o + 1) (l - 1) := by
  rw [ucK, ite_eq_right h]
end arms
attribute [ind_grind] ucW_nil ucW_cons ucK_no ucK_yes

theorem nestUniformCs_spec (p : Prog) (hl : NuLook p) (hp : p.lookup "nest_uniform_cs" = some nestUniformCsL)
    (cR : CallM) (hcR : CallSpec p cR) (k : Nat) : ∀ (s₀ : St) (ctx o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform_cs" [ctx, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ucW cR k s₀.mem ctx o l = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ ctx o l
    rw [invoke_eq _ hp]; simp only [callFn, nestUniformCsL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ ctx o l
    simp only [invoke_eq _ hp, callFn, nestUniformCsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestUniformOk_spec' p hl cR hcR k, ih] <;>
      finish (gen := 20) [rdW_eq]

mutual
def unW (cR : CallM) : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | k + 1, m, ctx, off, l =>
    if l = 0 then some m
    else unK cR k ctx off l (ucW cR k m ctx (rdW (m.arr64 IW) (rdW (m.arr64 IW) off))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 1)))
def unK (cR : CallM) (k : Nat) (ctx off l : Word) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m1) => if r.headD 0 = 0 then none else unW cR k m1 ctx (off + 1) (l - 1)
end

section arms
variable (cR : CallM) (k : Nat) (m m1 : Mem) (ctx off l : Word) (r : List Word)
theorem unW_nil (h : l = 0) : unW cR (k + 1) m ctx off l = some m := by simp [unW, h]
theorem unW_cons (h : ¬ l = 0) : unW cR (k + 1) m ctx off l =
    unK cR k ctx off l (ucW cR k m ctx (rdW (m.arr64 IW) (rdW (m.arr64 IW) off))
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 1))) := by simp [unW, h]
theorem unK_no (h : r.headD 0 = 0) : unK cR k ctx off l (some (r, m1)) = none := by rw [unK, ite_eq_left h]
theorem unK_yes (h : ¬ r.headD 0 = 0) : unK cR k ctx off l (some (r, m1)) = unW cR k m1 ctx (off + 1) (l - 1) := by
  rw [unK, ite_eq_right h]
end arms
attribute [ind_grind] unW_nil unW_cons unK_no unK_yes

theorem nestUniform_spec (p : Prog) (hl : NuLook p) (hc : p.lookup "nest_uniform_cs" = some nestUniformCsL)
    (hp : p.lookup "nest_uniform" = some nestUniformL) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) :
    ∀ (s₀ : St) (ctx off l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_uniform" [ctx, off, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ unW cR k s₀.mem ctx off l = some s'.mem; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ ctx off l
    rw [invoke_eq _ hp]; simp only [callFn, nestUniformL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ ctx off l
    simp only [invoke_eq _ hp, callFn, nestUniformL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestUniformCs_spec p hl hc cR hcR k, ih] <;>
      finish (gen := 20) [rdW_eq]

/-! ### `nest_uniform`: the relational side -/

theorem nuWf_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (h : nuWf cR k m ctx cv = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv) (hhi : c.hiAt 0 < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ r = [if x then 1 else 0] ∧ PosMR m' ∧ (NuAfr → AFr m m') := by
  match k, h with
  | k + 4, h => exact nuW_ok k dn fe vis m m' a ctx cv c cvv r cR (hI k) h hS hc hin hsl hcv hhi hP

theorem CsAt.tail {m : Mem} {o : Nat} {x : IConstantVal × Nat} {xs : List (IConstantVal × Nat)}
    {P : Nat → Prop} (h : CsAt m o (x :: xs) P) : CsAt m (o + 1) xs P := fun i hi => by
  obtain ⟨w, hw, hc⟩ := h (i + 1) (by simp; omega)
  exact ⟨w, by rw [show o + 1 + i = o + (i + 1) by omega]; exact hw, by simpa using hc⟩

/-- The context facts the uniform checks need, at one memory. -/
structure UCtx (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (ctx : Word)
    (c : NestCtx) : Prop where
  dec : decCtx m ctx.toNat = some c
  inn : CtxIn m ctx.toNat (· < iwTop m)
  sl : CtxSl m ctx.toNat

theorem UCtx.grow {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem} {ctx : Word}
    {c : NestCtx} (h : UCtx dn vis fe m ctx c) (hg : IWGrow m m') : UCtx dn vis fe m' ctx c :=
  ⟨by rw [(CtxIn.grow h.inn hg).1]; exact h.dec, (CtxIn.grow h.inn hg).2, h.sl.grow h.inn hg⟩

theorem ucW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word) (c : NestCtx)
    (hhi : c.hiAt 0 < 2 ^ 64) (cR : CallM) (J : Mem → AState → Prop) (Pcv : IConstantVal → Prop)
    (hJI : ∀ (m : Mem) (a : AState) (cv : Word) (cvv : IConstantVal), J m a → Pcv cvv →
      decCV (erecP m) cv.toNat = some cvv → ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (hJnu : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (cv : Word) (cvv : IConstantVal) (r : List Word) (x : Bool),
      J m a → Pcv cvv → nuWf cR k m ctx cv = some (r, m') →
      (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') → StageR dn vis fe m' a' → (NuAfr → AFr m m') →
      J m' a') (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (o l : Word) (cs : List (IConstantVal × Nat)) (r : List Word),
    ucW cR k m ctx o l = some (r, m') → StageR dn vis fe m a → J m a → (∀ x ∈ cs, Pcv x.1) →
    UCtx dn vis fe m ctx c →
    l.toNat = cs.length → o.toNat + cs.length ≤ iwTop m → CsAt m o.toNat cs (· < iwTop m) → PosMR m →
    ∃ b a', (cs.allM (fun x => ConRon.Arena.nestUniformOk c x.1)).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' ∧ J m' a' := by
  induction k with
  | zero => intro m m' a o l cs r h; simp [ucW] at h
  | succ k ih =>
    intro m m' a o l cs r h hS hJ hPc hU hl hob hcs hP
    by_cases hl0 : l = 0
    · rw [ucW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : cs = [] := List.eq_nil_of_length_eq_zero (by rw [← hl]; rfl)
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl _, rfl, hP, hJ⟩
    rw [ucW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨x, cs', rfl⟩ := List.exists_cons_of_ne_nil (show cs ≠ [] from fun e => by rw [e] at hl; exact hlz hl)
    obtain ⟨w, hw, h0, h1, qn, hqn, hcvv, -⟩ := hcs 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hw hcvv
    have hrw : rdW (m.arr64 IW) o = w := by simp [rdW, hw]
    obtain ⟨q, hq, rfl⟩ : ∃ q : Word, (m.arr64 IW)[w.toNat]? = some q ∧ q.toNat = qn := by
      simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at hqn; exact hqn
    have hrq : rdW (m.arr64 IW) w = q := by simp [rdW, hq]
    rw [hrw, hrq] at h
    rcases hnu : nuWf cR k m ctx q with _ | ⟨r1, m1⟩ <;> rw [hnu] at h; · simp [ucK] at h
    have hPx := hPc x List.mem_cons_self
    obtain ⟨b1, a1, hrun1, hS1, hg1, hr1, hP1, hA1⟩ := nuWf_ok k dn fe vis m m1 a ctx q c x.1 r1 cR
      (hJI m a q x.1 hJ hPx hcvv) hnu hS hU.dec hU.inn hU.sl hcvv hhi hP
    have hJ1 := hJnu k m m1 a a1 q x.1 r1 b1 hJ hPx hnu hrun1 hS1 hA1
    rw [List.allM_cons]
    cases b1 with
    | false =>
      subst hr1
      rw [ucK_no (h := rfl)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, a1, ?_, hS1, hg1, rfl, hP1, hJ1⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind]; rfl
    | true =>
      subst hr1
      rw [ucK_yes (h := by simp)] at h
      have ho1 : (o + 1).toNat = o.toNat + 1 := word_add_toNat (by
        have := hS.2.1; have := hS.2.2.2.1; simp at hob; simp; omega)
      have hl1 : (l - 1).toNat = l.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      have hcs1 := hcs.tail
      have hb1 : o.toNat + 1 + cs'.length ≤ iwTop m := by simp at hob; omega
      obtain ⟨b, a', hrun, hS', hg', hr, hP', hJ'⟩ := ih m1 m' a1 (o + 1) (l - 1) cs' r h hS1 hJ1
        (fun y hy => hPc y (List.mem_cons_of_mem _ hy)) (hU.grow hg1)
        (by rw [hl1, hl]; simp) (by rw [ho1]; have := hg1.1; omega)
        (by rw [ho1]; exact hcs1.grow hb1 hg1) hP1
      refine ⟨b, a', ?_, hS', hg1.trans hg', hr, hP', hJ'⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, ite_true]
      exact hrun

/-- The members' constructor lists: headers at `off, off + 1, …`, each a `[cv, nF]` pointer slice. -/
def CssAt (m : Mem) (off : Nat) (css : List (List (IConstantVal × Nat))) : Prop :=
  ∀ i (hi : i < css.length), ∃ hdr o l : Word, (m.arr64 IW)[off + i]? = some hdr ∧
    (m.arr64 IW)[hdr.toNat]? = some o ∧ (m.arr64 IW)[hdr.toNat + 1]? = some l ∧
    off + i < iwTop m ∧ hdr.toNat + 1 < iwTop m ∧ l.toNat = css[i].length ∧
    o.toNat + l.toNat ≤ iwTop m ∧ CsAt m o.toNat css[i] (· < iwTop m)

theorem CssAt.tail {m : Mem} {off : Nat} {x : List (IConstantVal × Nat)} {xs : List (List (IConstantVal × Nat))}
    (h : CssAt m off (x :: xs)) : CssAt m (off + 1) xs := fun i hi => by
  obtain ⟨hdr, o, l, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h (i + 1) (by simp; omega)
  exact ⟨hdr, o, l, by rw [show off + 1 + i = off + (i + 1) by omega]; exact h1, h2, h3, by omega, h5,
    by simpa using h6, h7, by simpa using h8⟩

theorem CssAt.grow {m m' : Mem} {off : Nat} {css : List (List (IConstantVal × Nat))} (h : CssAt m off css)
    (hg : IWGrow m m') : CssAt m' off css := fun i hi => by
  obtain ⟨hdr, o, l, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h i hi
  refine ⟨hdr, o, l, by rw [hg.2.2.1 _ h4]; exact h1, by rw [hg.2.2.1 _ (by omega)]; exact h2,
    by rw [hg.2.2.1 _ h5]; exact h3, by have := hg.1; omega, by have := hg.1; omega, h6,
    by have := hg.1; omega, h8.grow (by omega) hg⟩

theorem unW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word) (c : NestCtx)
    (hhi : c.hiAt 0 < 2 ^ 64) (cR : CallM) (J : Mem → AState → Prop) (Pcv : IConstantVal → Prop)
    (hJI : ∀ (m : Mem) (a : AState) (cv : Word) (cvv : IConstantVal), J m a → Pcv cvv →
      decCV (erecP m) cv.toNat = some cvv → ∀ (k' : Nat) (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k' + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (hJnu : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (cv : Word) (cvv : IConstantVal) (r : List Word) (x : Bool),
      J m a → Pcv cvv → nuWf cR k m ctx cv = some (r, m') →
      (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') → StageR dn vis fe m' a' → (NuAfr → AFr m m') →
      J m' a') (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (css : List (List (IConstantVal × Nat))),
    unW cR k m ctx off l = some m' → StageR dn vis fe m a → J m a → (∀ cs ∈ css, ∀ x ∈ cs, Pcv x.1) →
    UCtx dn vis fe m ctx c →
    l.toNat = css.length → CssAt m off.toNat css → PosMR m →
    ∃ a', (ConRon.Arena.nestUniform c css).run a = .ok ((), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      PosMR m' ∧ J m' a' := by
  induction k with
  | zero => intro m m' a off l css h; simp [unW] at h
  | succ k ih =>
    intro m m' a off l css h hS hJ hPc hU hl hcss hP
    by_cases hl0 : l = 0
    · rw [unW_nil (h := hl0)] at h
      cases h
      subst hl0
      have : css = [] := List.eq_nil_of_length_eq_zero (by rw [← hl]; rfl)
      subst this
      exact ⟨a, rfl, hS, IWGrow.refl _, hP, hJ⟩
    rw [unW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨cs, css', rfl⟩ := List.exists_cons_of_ne_nil (show css ≠ [] from fun e => by rw [e] at hl; exact hlz hl)
    obtain ⟨hdr, o, ll, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hcss 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h1 h6 h8
    have r1 : rdW (m.arr64 IW) off = hdr := by simp [rdW, h1]
    have r2 : rdW (m.arr64 IW) hdr = o := by simp [rdW, h2]
    have hh1 : (hdr + 1).toNat = hdr.toNat + 1 := word_add_toNat (by
      have := hS.2.1; have := hS.2.2.2.1; simp; omega)
    have r3 : rdW (m.arr64 IW) (hdr + 1) = ll := by simp [rdW, hh1, h3]
    rw [r1, r2, r3] at h
    rcases huc : ucW cR k m ctx o ll with _ | ⟨r, m1⟩ <;> rw [huc] at h; · simp [unK] at h
    obtain ⟨b, a1, hrun1, hS1, hg1, hr, hP1, hJ1⟩ := ucW_ok dn fe vis ctx c hhi cR J Pcv hJI hJnu k m m1 a o ll cs r
      huc hS hJ (hPc cs List.mem_cons_self) hU
      h6 (by omega) h8 hP
    rw [ConRon.Arena.nestUniform.eq_2]
    cases b with
    | false => rw [unK_no (h := hr)] at h; simp at h
    | true =>
      rw [unK_yes (h := by rw [hr]; decide)] at h
      have ho1 : (off + 1).toNat = off.toNat + 1 := word_add_toNat (by
        have := hS.2.1; have := hS.2.2.2.1; simp; omega)
      have hl1 : (l - 1).toNat = l.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      obtain ⟨a', hrun, hS', hg', hP', hJ'⟩ := ih m1 m' a1 (off + 1) (l - 1) css' h hS1 hJ1
        (fun cs hcs => hPc cs (List.mem_cons_of_mem _ hcs)) (hU.grow hg1)
        (by rw [hl1, hl]; simp) (by rw [ho1]; exact hcss.tail.grow hg1) hP1
      refine ⟨a', ?_, hS', hg1.trans hg', hP', hJ'⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, ite_true]
      exact hrun

section census
variable (p : Prog) (hl : NuLook p) (hc : p.lookup "nest_uniform_cs" = some nestUniformCsL)
  (hp : p.lookup "nest_uniform" = some nestUniformL)
include hl hc hp

end census

end L.Ind
