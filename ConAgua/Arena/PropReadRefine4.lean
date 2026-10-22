import ConAgua.Arena.PropReadRefine3

/-!
# The prop-ness readers: `headProofPW`, `proofPW`, `notProofFast`, `isProofFast` (helper `defeq2-prop`)

`head_proof_proj` calls lane `whnf3`'s `find_proj` (its spec `FindProjOK` a hypothesis here, with
the two facts `reduce_proj_core`'s proof also takes: `ErecKept`, `ProjFound`). After it the core
relation holds at other maps (`CoreAfter`), so from here on the posts are `CoreAfter`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

open ConLeche (Name Level PropWhen)

theorem pr_run_of_ok {α : Type} [Inhabited α] {x : AM α} {a : AState} (h : AM.ok x a) :
    x.run a = .ok (AM.res x a, AM.st x a) := by
  unfold AM.ok at h; unfold AM.res AM.st
  split at h
  · rename_i v hv; rw [hv]
  · cases h

/-- **A projection table's body at field `i`**: the words `head_proof_proj` reads are the
handle of `tbl.bodies.getD i default`. -/
theorem decTbl_body {E : Array Word} {q : Word} {tbl : IProjTable} (h : decTbl E q.toNat = some tbl)
    (hsz : E.size < 2 ^ 63) (i : Word) :
    HW (if i < rdW E (q + 10) then rdW E (rdW E (q + 9) + i) else 0) ∧
      decE (if i < rdW E (q + 10) then rdW E (rdW E (q + 9) + i) else 0) =
        tbl.bodies.getD i.toNat default := by
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, bs, hbs, -, -, -, -, rfl⟩ := h
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.map_eq_some_iff] at hbs
  obtain ⟨off, ⟨wo, hwo, rfl⟩, cnt, ⟨wc, hwc, rfl⟩, hs⟩ := hbs
  have hext : ArrExt E E := fun _ _ h => h
  have h9 : rdW E (q + 9) = wo := rdW_ext hext hsz (k := 9) (by decide) hwo
  have h10 : rdW E (q + 10) = wc := rdW_ext hext hsz (k := 10) (by decide)
    (by simpa [Nat.add_assoc] using hwc)
  rw [h9, h10]
  obtain ⟨hlen, hget⟩ := hslice?_get hs
  by_cases hi : i < wc
  · have hi' : i.toNat < wc.toNat := UInt64.lt_iff_toNat_lt.mp hi
    obtain ⟨w, hw, hw32, hl⟩ := hget i.toNat hi'
    have hlt : wo.toNat + i.toNat < E.size := (Array.getElem?_eq_some_iff.mp hw).1
    have hrd : rdW E (wo + i) = w := by
      have : (wo + i).toNat = wo.toNat + i.toNat := by rw [UInt64.toNat_add]; omega
      simp [rdW, this, hw]
    simp only [hi, ↓reduceIte, hrd]
    refine ⟨hw32, ?_⟩
    have hb : i.toNat < bs.length := by omega
    rw [Array.getD_eq_getD_getElem?]
    simp only [List.getElem?_toArray, hl, Option.getD_some, decE_eq]
  · simp only [hi, ↓reduceIte]
    refine ⟨by unfold HW; decide, ?_⟩
    have hb : ¬ i.toNat < bs.length := by
      rw [hlen]; exact fun h => hi (UInt64.lt_iff_toNat_lt.mpr h)
    rw [Array.getD_eq_getD_getElem?]
    simp only [List.getElem?_toArray, List.getElem?_eq_none (Nat.le_of_not_lt hb), Option.getD_none]
    rfl

/-! ## `head_proof_proj` -/

/-- `headProofPW`'s `.proj` arm. -/
def hpProjT (fe : IFEnv) (f : Nat) (S : NIdx) (i : Nat) : AM (Option PropWhen) := do
  match ← fe.findProj? S i with
  | some entry => do
    match ← typeSortPW fe f entry.body with
    | some pw => pure (if pw.isNever then some pw else none)
    | none => pure none
  | none => pure none

section hpp
variable {p : Prog} (hp : PropReadProg p) (hden : CoreDen) (hlps : ConstLpsDen)
  (hfp : FindProjOK p) (hek : ErecKept p) (hpf : ProjFound p)
include hp hden hlps hfp hek hpf

/-- **`head_proof_proj` refines `headProofPW`'s `.proj` arm.** -/
theorem hpp_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {f sn i : Word}
    (hf : f.toNat ≤ coreWalkFuel) (hsn : HW sn) {r : List Word}
    (hc : callW p n "head_proof_proj" [vis, f, sn, i] m = some (r, m')) :
    ∃ res a', (hpProjT fe f.toNat (decI sn) i.toNat).run a = .ok (res, a') ∧
      CoreAfter dn m m' a' vis fe M eb ∧
      PWD (nameN a'.store.lss.ls.ns) m' (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) res := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (headProofProj_spec p hp n ⟨m, Locals.init []⟩ vis f sn i) hc
  rw [ht] at hW
  generalize r.headD 0 = x₀ at hW ⊢
  generalize r.tail.headD 0 = x₁ at hW ⊢
  generalize r.tail.tail.headD 0 = x₂ at hW ⊢
  rcases hc1 : callW p n "find_proj" [vis, sn, i] m with _ | ⟨r₁, m₁⟩
  · rw [hc1] at hW; cases hW
  rw [hc1] at hW
  obtain ⟨hok, hafter, hres, -⟩ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hfp n ⟨m, Locals.init []⟩ a dn vis fe M eb sn i hS hsn) hc1
  have hrun₁ := pr_run_of_ok hok
  rw [hres] at hrun₁
  dsimp only at hrun₁
  generalize AM.st (fe.findProj? (decI sn) i.toNat) a = a₁ at hrun₁ hafter
  simp only [hppK1] at hW
  by_cases h0 : r₁.headD 0 = 0
  · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    refine ⟨none, a₁, ?_, hafter, rfl⟩
    simp only [hpProjT, StateT.run_bind, hrun₁, decEntry, h0, ↓reduceIte, except_ok_bind]
    rfl
  simp only [h0, ↓reduceIte] at hW
  obtain ⟨tbl, htbl⟩ := hpf n m a dn vis fe M eb sn i r₁ m₁ hS hc1 h0
  have hE : m₁.arr64 EREC = m.arr64 EREC := hek n "find_proj" _ m r₁ m₁ (Or.inl rfl) hc1
  obtain ⟨hbw, hbe⟩ := decTbl_body htbl hS.erec i
  simp only [hppB, hE] at hW
  generalize (if i < rdW (m.arr64 EREC) (r₁.tail.headD 0 + 10) then
    rdW (m.arr64 EREC) (rdW (m.arr64 EREC) (r₁.tail.headD 0 + 9) + i) else 0) = b at hW hbw hbe
  obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := hafter
  rcases hc2 : callW p n "type_sort_pw" [vis, f, b] m₁ with _ | ⟨r₂, m₂⟩
  · rw [hc2] at hW; cases hW
  rw [hc2] at hW
  obtain ⟨res₂, a₂, hrun₂, hRd₂, hd₂⟩ := tsp_call hp hden hlps hS₁ hf hbw hc2
  have hentry : decEntry (m.arr64 EREC) (r₁.headD 0) (r₁.tail.headD 0) i.toNat =
      some (tbl.entry i.toNat) := by
    simp only [decEntry, h0, ↓reduceIte, htbl, Option.map_some]
  have hbody : (tbl.entry i.toNat).body = decE b := hbe.symm
  have hcalc : ∀ res, (typeSortPW fe f.toNat (decE b)).run a₁ = .ok (res, a₂) →
      (hpProjT fe f.toNat (decI sn) i.toNat).run a =
      (match res with
        | some pw => pure (if pw.isNever then some pw else none)
        | none => pure none : AM (Option PropWhen)).run a₂ := by
    intro res h
    simp only [hpProjT, StateT.run_bind, hrun₁, hentry, except_ok_bind, hbody, h]
  have hpre := hcalc res₂ hrun₂
  clear hcalc
  have hA : CoreAfter dn m m₂ a₂ vis fe M eb := CoreAfter.comp hK₁ hSt₁ hRd₂.core
  simp only [hppK2] at hW
  by_cases h1 : r₂.headD 0 = 1
  · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    rcases res₂ with _ | _ | ps
    · simp only [PWD] at hd₂; rw [h1] at hd₂; exact absurd hd₂ (by decide)
    · exact ⟨some .never, a₂, by rw [hpre]; rfl, hA, rfl⟩
    · rw [h1] at hd₂; exact absurd hd₂.1 (by decide)
  simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
  refine ⟨none, a₂, ?_, hA, rfl⟩
  rw [hpre]
  rcases res₂ with _ | _ | ps
  · rfl
  · simp only [PWD] at hd₂; exact absurd hd₂ h1
  · rfl

end hpp

/-! ## `head_proof_pw`, `proof_pw` -/

section hpw
variable {p : Prog} (hp : PropReadProg p) (hden : CoreDen) (hlps : ConstLpsDen)
  (hfp : FindProjOK p) (hek : ErecKept p) (hpf : ProjFound p)
include hp hden hlps hfp hek hpf

/-- **`head_proof_pw` refines `headProofPW`.** -/
@[refines ConRon.Arena.headProofPW]
theorem hpw_call {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {f h : Word}
    (hf : f.toNat ≤ coreWalkFuel) (hh : HW h) {r : List Word}
    (hc : callW p n "head_proof_pw" [vis, f, h] m = some (r, m')) :
    ∃ res a', (headProofPW fe f.toNat (decE h)).run a = .ok (res, a') ∧
      CoreAfter dn m m' a' vis fe M eb ∧
      PWD (nameN a'.store.lss.ls.ns) m' (r.headD 0) (r.tail.headD 0) (r.tail.tail.headD 0) res := by
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (headProofPW_spec p hp n ⟨m, Locals.init []⟩ vis f h) hc
  rw [ht] at hW
  generalize r.headD 0 = x₀ at hW ⊢
  generalize r.tail.headD 0 = x₁ at hW ⊢
  generalize r.tail.tail.headD 0 = x₂ at hW ⊢
  have hR := hS.arena.1
  unfold hpwW at hW
  by_cases hne : L.Ind.eViewW m h = []
  · simp [hne] at hW
  simp only [hne, ↓reduceIte] at hW
  obtain ⟨v, hv, hVR⟩ := L.Ind.eViewW_ok m a hR h hne
  generalize L.Ind.eViewW m h = w at hW hVR
  have hpre : (headProofPW fe f.toNat (decE h)).run a =
      (match v with
        | .const c us => cArmT fe (typeSortPW fe f.toNat) c us
        | .fvar _ ty => typeSortPW fe f.toNat ty
        | .sort _ | .forallE .. | .lit _ => pure (some .never)
        | .proj S i _ => hpProjT fe f.toNat S i
        | _ => pure none).run a := by
    simp only [headProofPW, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
    rcases v <;> rfl
  have hnone : ∀ c : Word, w.headD 0 = c → c ≠ 3 → c ≠ 1 → c ≠ 2 → c ≠ 6 → c ≠ 8 → c ≠ 9 →
      (headProofPW fe f.toNat (decE h)).run a = .ok (none, a) →
      ∃ res a', (headProofPW fe f.toNat (decE h)).run a = .ok (res, a') ∧
        CoreAfter dn m m' a' vis fe M eb ∧ PWD (nameN a'.store.lss.ls.ns) m' x₀ x₁ x₂ res := by
    intro c hg h3 h1 h2 h6 h8 h9 hrun
    simp only [vG, hg, h3, h1, h2, h6, h8, h9, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    exact ⟨none, a, hrun, (RdAfter.refl hS).core, rfl⟩
  have hnev : ∀ c : Word, w.headD 0 = c → c ≠ 3 → c ≠ 1 → (c = 2 ∨ c = 6 ∨ c = 8) →
      (headProofPW fe f.toNat (decE h)).run a = .ok (some .never, a) →
      ∃ res a', (headProofPW fe f.toNat (decE h)).run a = .ok (res, a') ∧
        CoreAfter dn m m' a' vis fe M eb ∧ PWD (nameN a'.store.lss.ls.ns) m' x₀ x₁ x₂ res := by
    intro c hg h3 h1 hc hrun
    have hW' : some (1, 0, 0, m) = some (x₀, x₁, x₂, m') := by
      rw [← hW]; simp only [vG, hg, h3, h1, ↓reduceIte]
      rcases hc with rfl | rfl | rfl <;> simp
    simp only [Option.some.injEq, Prod.mk.injEq] at hW'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW'
    exact ⟨some .never, a, hrun, (RdAfter.refl hS).core, rfl⟩
  rcases v with i | ⟨i, ty⟩ | u | ⟨I, us⟩ | ⟨g, x⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, vv, b⟩ | l | ⟨sn, i, pe⟩
  · exact hnone 0 hVR.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hpre]; rfl)
  · -- fvar
    obtain ⟨hg, -, hty, hty'⟩ := hVR
    rw [pr_getD2] at hty hty'
    simp only [vG, vY, hg, show (1 : Word) ≠ 3 by decide, ↓reduceIte] at hW
    rcases hc2 : callW p n "type_sort_pw" [vis, f, w.tail.tail.headD 0] m with _ | ⟨r₂, m₂⟩
    · rw [hc2] at hW; cases hW
    rw [hc2] at hW
    simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    obtain ⟨res, a', hrun, hRd, hd⟩ := tsp_call hp hden hlps hS hf hty hc2
    refine ⟨res, a', ?_, hRd.core, by rw [hRd.2.2.2]; exact hd⟩
    rw [hpre, ← hty']; exact hrun
  · exact hnev 2 hVR.1 (by decide) (by decide) (Or.inl rfl) (by rw [hpre]; rfl)
  · -- const
    obtain ⟨hg, hn, hn', husw, hus'⟩ := hVR
    rw [pr_getD1] at hn hn'
    rw [pr_getD2] at husw hus'
    simp only [vG, vX, vY, hg, ↓reduceIte, eq_self_iff_true, if_true] at hW
    rcases hc2 : callW p n "head_proof_const" [vis, f, w.tail.headD 0, w.tail.tail.headD 0] m
      with _ | ⟨r₂, m₂⟩
    · rw [hc2] at hW; cases hW
    rw [hc2] at hW
    simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    cases n with
    | zero => rw [callW_zero] at hc2; cases hc2
    | succ n =>
    obtain ⟨t₂, ht₂, -, hW₂⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (headProofConst_spec p hp n ⟨m, Locals.init []⟩ vis f _ _) hc2
    rw [ht₂] at hW₂
    have hls := (hden dn m a vis fe M eb hS).constLs _ _ _ hv
    rw [← hus'] at hls
    obtain ⟨res, a', hrun, hRd, hd⟩ := cArm_ok hp hden hlps
      (sub := fun ty m => callW p n "type_sort_pw" [vis, f, ty] m) (T := typeSortPW fe f.toNat)
      (fun hS₁ hty hc => tsp_call hp hden hlps hS₁ hf hty hc) hS hn husw hls hW₂
    refine ⟨res, a', ?_, hRd.core, by rw [hRd.2.2.2]; exact hd⟩
    rw [hpre, ← hn', ← hus']; exact hrun
  · exact hnone 4 hVR.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hpre]; rfl)
  · exact hnone 5 hVR.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hpre]; rfl)
  · exact hnev 6 hVR.1 (by decide) (by decide) (Or.inr (Or.inl rfl)) (by rw [hpre]; rfl)
  · exact hnone 7 hVR.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hpre]; rfl)
  · exact hnev 8 hVR (by decide) (by decide) (Or.inr (Or.inr rfl)) (by rw [hpre]; rfl)
  · -- proj
    obtain ⟨hg, hsw, hsn, hiw, -, -⟩ := hVR
    rw [pr_getD1] at hsw hsn
    rw [pr_getD2] at hiw
    simp only [vG, vX, vY, hg, show (9 : Word) ≠ 3 by decide, show (9 : Word) ≠ 1 by decide,
      show (9 : Word) ≠ 2 by decide, show (9 : Word) ≠ 6 by decide, show (9 : Word) ≠ 8 by decide,
      ↓reduceIte] at hW
    rcases hc2 : callW p n "head_proof_proj" [vis, f, w.tail.headD 0, w.tail.tail.headD 0] m
      with _ | ⟨r₂, m₂⟩
    · rw [hc2] at hW; cases hW
    rw [hc2] at hW
    simp only [t3W, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hW
    obtain ⟨res, a', hrun, hA, hd⟩ := hpp_call hp hden hlps hfp hek hpf hS hf hsw hc2
    refine ⟨res, a', ?_, hA, hd⟩
    rw [hpre, ← hsn, ← hiw]; exact hrun

end hpw

end L.Arena
