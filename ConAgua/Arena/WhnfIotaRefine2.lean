import ConAgua.Arena.CoreErec
import ConAgua.Arena.WhnfIotaRefine
import ConAgua.L.ModelGen

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 2 (`defeq_list` … `inst_spine_pins`)

Split from `WhnfIotaRefine.lean` (primed theorems, program hypotheses explicit).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `defeq_list(mode, vis, d, ao, an, bo, bn)` -/

/-- Model of the `defeq_list` loop at L fuel `k`. -/
def dlW (p : Prog) (mode vis d ao an bo bn : Word) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | k + 1, m, i =>
    if i < an ∧ i < bn then
      match callW p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)] m with
      | none => none
      | some (r, m₁) => if r.headD 0 = 0 then some ([0], m₁) else dlW p mode vis d ao an bo bn k m₁ (i + 1)
    else some ([Cmp.eq.evalW an bn], m)

theorem dlW_end (p : Prog) (mode vis d ao an bo bn : Word) (k : Nat) (m : Mem) (i : Word)
    (h : ¬ (i < an ∧ i < bn)) :
    dlW p mode vis d ao an bo bn (k + 1) m i = some ([Cmp.eq.evalW an bn], m) := by
  simp only [dlW, h, ↓reduceIte]

theorem dlW_stop (p : Prog) (mode vis d ao an bo bn : Word) (k : Nat) (m m₁ : Mem) (i : Word)
    (r : List Word) (h : i < an ∧ i < bn)
    (hc : callW p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)] m =
      some (r, m₁)) (h0 : r.headD 0 = 0) :
    dlW p mode vis d ao an bo bn (k + 1) m i = some ([0], m₁) := by
  simp only [dlW, h.1, h.2, and_self, ↓reduceIte, hc, h0]

theorem dlW_cont (p : Prog) (mode vis d ao an bo bn : Word) (k : Nat) (m m₁ : Mem) (i : Word)
    (r : List Word) (h : i < an ∧ i < bn)
    (hc : callW p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)] m =
      some (r, m₁)) (h0 : ¬ r.headD 0 = 0) :
    dlW p mode vis d ao an bo bn (k + 1) m i = dlW p mode vis d ao an bo bn k m₁ (i + 1) := by
  simp only [dlW, h.1, h.2, and_self, ↓reduceIte, hc, h0]

theorem defeqListLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k defeqListLoop
    ⦃fun r s' => r ≠ .brk ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 6 = s₀.loc 6 ∧
      dlW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
      (s₀.loc 6) k s₀.mem (s₀.loc 7) =
        some (r.retOr [Cmp.eq.evalW (s₀.loc 4) (s₀.loc 6)], s'.mem); ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := defeqListLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p k "defeq", ih] <;> finish [dlW_end, dlW_stop, dlW_cont]

theorem defeqList_spec (p : Prog) (hp : p.lookup "defeq_list" = some defeqListL) (k : Nat)
    (s₀ : St) (mode vis d ao an bo bn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "defeq_list" [mode, vis, d, ao, an, bo, bn]
    ⦃fun r s' => LocEq s' s₀ ∧ dlW p mode vis d ao an bo bn (k + 1) s₀.mem 0 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, defeqListL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, fun s₀ => Triple.step_exec (defeqListLoop_spec p (k + 1) s₀)] <;>
    finish

theorem defEqList_nil_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (a : AState) :
    (defEqList r fe d [] []).run a = .ok (true, a) := by
  simp [defEqList]; rfl

theorem defEqList_nil_cons_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (b : EIdx) (bs : List EIdx)
    (a : AState) : (defEqList r fe d [] (b :: bs)).run a = .ok (false, a) := by
  simp [defEqList]; rfl

theorem defEqList_cons_nil_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (x : EIdx) (xs : List EIdx)
    (a : AState) : (defEqList r fe d (x :: xs) []).run a = .ok (false, a) := by
  simp [defEqList]; rfl

theorem defEqList_stop_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (x y : EIdx) (xs ys : List EIdx)
    (a a₁ : AState) (h : (r.defeq d x y).run a = .ok (false, a₁)) :
    (defEqList r fe d (x :: xs) (y :: ys)).run a = .ok (false, a₁) := by
  simp only [defEqList, StateT.run_bind, h, except_ok_bind]; rfl

theorem defEqList_cont_run (r : CoreFnsA) (fe : IFEnv) (d : Nat) (x y : EIdx) (xs ys : List EIdx)
    (a a₁ a₂ : AState) (res : Bool) (h : (r.defeq d x y).run a = .ok (true, a₁))
    (hr : (defEqList r fe d xs ys).run a₁ = .ok (res, a₂)) :
    (defEqList r fe d (x :: xs) (y :: ys)).run a = .ok (res, a₂) := by
  simp only [defEqList, StateT.run_bind, h, except_ok_bind, ite_true]; exact hr

theorem toUInt64_toNat_self (i : Word) : i.toNat.toUInt64 = i := by
  simp [Nat.toUInt64]

/-- A spine slice that may be empty anywhere (an empty slice has no bound to keep). -/
def SpineN (m : Mem) (off cnt : Word) (xs : Array EIdx) : Prop :=
  xs.size = cnt.toNat ∧ (cnt ≠ 0 → SpineR m off cnt xs)

theorem SpineR.toN {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs) :
    SpineN m off cnt xs := ⟨h.size, fun _ => h⟩

theorem SpineN.keep {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineN m off cnt xs)
    (hsz : (m'.arr64 SPN).size = (m.arr64 SPN).size)
    (hk : ∀ i : Word, i < spTop m → spW m' i = spW m i)
    (htop : off.toNat + cnt.toNat ≤ (spTop m).toNat) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineN m' off cnt xs :=
  ⟨h.1, fun hc => (h.2 hc).keep hsz hk htop hspn⟩

/-- The loop's exit: one of the two spines is used up. -/
theorem dl_exit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (an bn i : Word) (aas bs : Array EIdx)
    (hna : aas.size = an.toNat) (hnb : bs.size = bn.toNat) (hia : i.toNat ≤ an.toNat)
    (hib : i.toNat ≤ bn.toNat) (hn : ¬ (i < an ∧ i < bn)) (a : AState) :
    (defEqList r fe d (aas.toList.drop i.toNat) (bs.toList.drop i.toNat)).run a =
      .ok (decide (an = bn), a) := by
  have h1 : ¬ (i.toNat < an.toNat ∧ i.toNat < bn.toNat) := fun h => hn ⟨h.1, h.2⟩
  by_cases hab : an = bn
  · subst hab
    have : aas.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp [hna]; omega)
    have h2 : bs.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp [hnb]; omega)
    rw [this, h2]; simpa using defEqList_nil_run r fe d a
  · have hne : an.toNat ≠ bn.toNat := fun h => hab (UInt64.toNat_inj.mp h)
    simp only [hab, decide_false]
    by_cases hi : i.toNat < an.toNat
    · have hb : bn.toNat ≤ i.toNat := by omega
      have h2 : bs.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp [hnb]; omega)
      rw [h2, List.drop_eq_getElem_cons (by simp [hna]; omega)]
      exact defEqList_cons_nil_run r fe d _ _ a
    · have h2 : aas.toList.drop i.toNat = [] := List.drop_eq_nil_of_le (by simp [hna]; omega)
      rw [h2, List.drop_eq_getElem_cons (by simp [hnb]; omega)]
      exact defEqList_nil_cons_run r fe d _ _ a

/-- **The `defeq_list` loop refines `defEqList`**, by induction on the remaining count. -/
theorem dlW_ok (p : Prog) (n F : Nat) (hknot : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d ao an bo bn : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (aas bs : Array EIdx) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (i : Word) (L : List Word) (m' : Mem),
      an.toNat - i.toNat = K → i.toNat ≤ an.toNat → i.toNat ≤ bn.toNat → k ≤ n + 1 →
      CoreS dn m a vis fe M eb → SpineN m ao an aas → SpineN m bo bn bs →
      (an ≠ 0 → ao.toNat + an.toNat ≤ (spTop m).toNat) →
      (bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop m).toNat) →
      dlW p mode vis d ao an bo bn k m i = some (L, m') →
      AM.ok (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (aas.toList.drop i.toNat)
        (bs.toList.drop i.toNat)) a ∧
      CoreAfter dn m m' (AM.st (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat
        (aas.toList.drop i.toNat) (bs.toList.drop i.toNat)) a) vis fe M eb ∧
      AM.res (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat (aas.toList.drop i.toNat)
        (bs.toList.drop i.toNat)) a = decBool L ∧ HW (L.headD 0) := by
  intro K
  induction K with
  | zero =>
    intro k m a M i L m' hK hia hib hk hS hsa hsb hta htb hL
    have hn : ¬ (i < an ∧ i < bn) := fun h => by
      have : i.toNat < an.toNat := h.1
      omega
    cases k with
    | zero => simp [dlW] at hL
    | succ k =>
    rw [dlW_end p mode vis d ao an bo bn k m i hn] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    refine CoreRef.of_run (ok := ResH) (dl_exit (coreKnot (decMode mode) fe id F) fe d.toNat an bn i aas bs
      hsa.1 hsb.1 hia hib hn a) ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩ ?_ ?_
    · simp only [decBool, Cmp.evalW, Cmp.eval]; by_cases h : an = bn <;> simp [h]
    · simp only [ResH, Cmp.evalW]; split <;> simp [HW]
  | succ K ih =>
    intro k m a M i L m' hK hia hib hk hS hsa hsb hta htb hL
    cases k with
    | zero => simp [dlW] at hL
    | succ k =>
    rcases Classical.em ¬(i < an ∧ i < bn) with hn | hn
    · rw [dlW_end p mode vis d ao an bo bn k m i hn] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      refine CoreRef.of_run (ok := ResH) (dl_exit (coreKnot (decMode mode) fe id F) fe d.toNat an bn i aas bs
        hsa.1 hsb.1 hia hib hn a) ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩ ?_ ?_
      · simp only [decBool, Cmp.evalW, Cmp.eval]; by_cases h : an = bn <;> simp [h]
      · simp only [ResH, Cmp.evalW]; split <;> simp [HW]
    replace hn := Classical.not_not.mp hn
    have hia' : i.toNat < an.toNat := hn.1
    have hib' : i.toNat < bn.toNat := hn.2
    have hna : an ≠ 0 := fun h => by rw [h] at hia'; simp at hia'
    have hnb : bn ≠ 0 := fun h => by rw [h] at hib'; simp at hib'
    have hsa := hsa.2 hna
    have hsb := hsb.2 hnb
    have hsza : i.toNat < aas.size := by rw [hsa.size]; exact hia'
    have hszb : i.toNat < bs.size := by rw [hsb.size]; exact hib'
    have hdra : aas.toList.drop i.toNat = aas[i.toNat] :: aas.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hsza)]; simp
    have hdrb : bs.toList.drop i.toNat = bs[i.toNat] :: bs.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hszb)]; simp
    have hga : aas[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsa.get i.toNat hsza
      simpa [spW, toUInt64_toNat_self] using this
    have hgb : bs[i.toNat] = decE (rdW (m.arr64 SPN) (bo + i)) := by
      have := hsb.get i.toNat hszb
      simpa [spW, toUInt64_toNat_self] using this
    have hxa : HW (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsa.lt i.toNat hia'
      unfold HW; simpa [spW, toUInt64_toNat_self] using this
    have hxb : HW (rdW (m.arr64 SPN) (bo + i)) := by
      have := hsb.lt i.toNat hib'
      unfold HW; simpa [spW, toUInt64_toNat_self] using this
    rw [hga] at hdra
    rw [hgb] at hdrb
    rcases hc : callW p k "defeq" [mode, vis, d, rdW (m.arr64 SPN) (ao + i), rdW (m.arr64 SPN) (bo + i)] m with _ | ⟨r₁, m₁⟩
    · simp [dlW, hn.1, hn.2, hc] at hL
    obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hr₁⟩ := CoreSpec.of_callW
      ((hknot k (by omega)).defeq F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d _ _ (by omega)
        (by omega) ⟨hS, hm4, hebm⟩ hxa hxb) hc
    have hrunT := AM.run_of_ok _ _ hok
    by_cases h0 : r₁.headD 0 = 0
    · rw [dlW_stop p mode vis d ao an bo bn k m m₁ i r₁ hn hc h0] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      have hres' : AM.res ((coreKnot (decMode mode) fe id F).defeq d.toNat
          (decE (rdW (m.arr64 SPN) (ao + i))) (decE (rdW (m.arr64 SPN) (bo + i)))) a = false := by
        rw [hres]; simpa [decBool] using h0
      rw [hres'] at hrunT
      have hrun := defEqList_stop_run (coreKnot (decMode mode) fe id F) fe d.toNat _ _
        (aas.toList.drop (i.toNat + 1)) (bs.toList.drop (i.toNat + 1)) a _ hrunT
      rw [hdra, hdrb]
      refine CoreRef.of_run (ok := ResH) hrun ⟨M₁, hS₁, hK₁, hSt₁⟩ ?_ (by simp [ResH, HW])
      · simp [decBool]
    · rw [dlW_cont p mode vis d ao an bo bn k m m₁ i r₁ hn hc h0] at hL
      have hsa₁ : SpineN m₁ ao an aas := hsa.toN.keep hSt₁.size hSt₁.below (hta hna) hS.spn
      have hsb₁ : SpineN m₁ bo bn bs := hsb.toN.keep hSt₁.size hSt₁.below (htb hnb) hS.spn
      have hta₁ : an ≠ 0 → ao.toNat + an.toNat ≤ (spTop m₁).toNat := fun h => by
        rw [hSt₁.1]; exact hta h
      have htb₁ : bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop m₁).toNat := fun h => by
        rw [hSt₁.1]; exact htb h
      have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hn.1
      obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hL1⟩ := ih k m₁ _ M₁ (i + 1) L m'
        (by omega) (by omega) (by omega) (by omega) hS₁ hsa₁ hsb₁ hta₁ htb₁ hL
      have hres' : AM.res ((coreKnot (decMode mode) fe id F).defeq d.toNat
          (decE (rdW (m.arr64 SPN) (ao + i))) (decE (rdW (m.arr64 SPN) (bo + i)))) a = true := by
        rw [hres]; simpa [decBool] using h0
      rw [hres'] at hrunT
      have hrunR := AM.run_of_ok _ _ hok2
      rw [h1] at hrunR
      rw [h1] at hS₂ hres2
      have hrun := defEqList_cont_run (coreKnot (decMode mode) fe id F) fe d.toNat _ _
        (aas.toList.drop (i.toNat + 1)) (bs.toList.drop (i.toNat + 1)) a _ _ _
        hrunT hrunR
      rw [hdra, hdrb]
      refine CoreRef.of_run (ok := ResH) hrun ⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩ hres2 hL1

/-- **`defeq_list` refines `defEqList`.** Statement changes (the knot's `defeq` slot needs them):
`n ≤ 2 ^ 62`, the eager bit `eb = (mode >>> 1) &&& 1`, and both slices (when not empty) below the stack top. -/
theorem defeqList_refines (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d ao an bo bn : Word) (aas bs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    SpineN s₀.mem ao an aas → SpineN s₀.mem bo bn bs →
    (an ≠ 0 → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) →
    (bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) →
    CoreSpec p (n + 1) "defeq_list" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat aas.toList bs.toList) decBool s₀ a₀ dn
      vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d ao an bo bn aas bs hS hm4 hebm hsa hsb hta htb
  refine triple_post (defeqList_spec p hp.defeqList n s₀ mode vis d ao an bo bn) fun r s' ⟨hloc,
    hW⟩ => ⟨hloc, ?_⟩
  obtain ⟨hok, hca, hres, hL1⟩ := dlW_ok p n F hk hnF hn62 dn vis fe eb mode d ao an bo bn hm4 hebm aas bs
    (an.toNat - (0 : Word).toNat) (n + 1) s₀.mem a₀ MM 0 r s'.mem rfl (by simp) (by simp) (Nat.le_refl _)
    hS hsa hsb hta htb hW
  refine ⟨hok, ?_, ?_, hL1⟩
  · simpa using hca
  · simpa using hres

/-! ## `iota_index_ok` -/

/-- Model of `iota_index_ok`. -/
def ioW (p : Prog) (n : Nat) (m : Mem) (mode vis d mI rP cnP tyCtor mo mn xo xn : Word) :
    Option (List Word × Mem) :=
  if mI = rP then some ([1], m)
  else match callW p n "pi_residual" [tyCtor, mo, mn] m with
    | none => none
    | some (r₁, m₁) =>
      if r₁.headD 0 = 0 then some ([0], m₁)
      else if ¬ (136 : Word).toNat < (m₁.arr64 CTL).size then none
      else match callW p n "get_app_args" [r₁.tail.headD 0] m₁ with
        | none => none
        | some (r₂, m₂) =>
          match callW p n "defeq_list" [mode, vis, d, r₂.headD 0 + cnP,
              (r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0), xo, xn] m₂ with
          | none => none
          | some (r₃, m₃) =>
            if (136 : Word).toNat < (m₃.arr64 CTL).size then
              some ([r₃.headD 0], m₃.set64 CTL 136 (rdW (m₁.arr64 CTL) 136))
            else none

theorem iotaIndexOk_spec (p : Prog) (hp : p.lookup "iota_index_ok" = some iotaIndexOkL) (n : Nat)
    (s₀ : St) (mode vis d mI rP cnP tyCtor mo mn xo xn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_index_ok" [mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn]
    ⦃fun r s' => LocEq s' s₀ ∧
      ioW p n s₀.mem mode vis d mI rP cnP tyCtor mo mn xo xn = some (r.headD 0 :: [], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaIndexOkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "pi_residual", callW_spec p n "get_app_args", callW_spec p n "defeq_list"] <;>
  simp_all [ioW, Cmp.eval, Cmp.evalW, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, rdW, CTL] <;>
  (try refine ⟨?_, ?_⟩) <;>
  first
    | (congr 1; rw [Array.getElem?_eq_getElem]; rfl)
    | assumption
    | simpa using ‹UInt64.toNat 136 < _›

/-- The slice after the first `c` words, as `iota_index_ok` computes it. -/
theorem spine_drop (m : Mem) (off cnt c : Word) (xs : Array EIdx) (h : SpineR m off cnt xs)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineN m (off + c) ((cnt - c) * (if c ≤ cnt then 1 else 0)) (xs.toList.drop c.toNat).toArray ∧
    (c ≤ cnt → (off + c).toNat + (cnt - c).toNat = off.toNat + cnt.toNat) := by
  by_cases hc : c ≤ cnt
  · have hc' : c.toNat ≤ cnt.toNat := hc
    have h1 : (cnt - c).toNat = cnt.toNat - c.toNat := UInt64.toNat_sub_of_le _ _ hc
    have hb := h.bound
    have h2 : (off + c).toNat = off.toNat + c.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    simp only [hc, ↓reduceIte, UInt64.mul_one]
    refine ⟨⟨by simp [h.size, h1], fun hne => ?_⟩, fun _ => by rw [h2, h1]; omega⟩
    have hcnt : (cnt - c).toNat = xs.size - c.toNat := by rw [h1, h.size]
    refine ⟨by simp [h.size, h1], by rw [h2, h1]; omega, fun i hi => ?_, fun i hi => ?_⟩
    · have hi' : c.toNat + i < cnt.toNat := by omega
      have := h.lt (c.toNat + i) hi'
      have e : off + c + i.toUInt64 = off + (c.toNat + i).toUInt64 := by
        simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc]
      rw [e]; exact this
    · have hi' : c.toNat + i < xs.size := by
        simp at hi; omega
      have := h.get (c.toNat + i) hi'
      have e : off + c + i.toUInt64 = off + (c.toNat + i).toUInt64 := by
        simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc]
      rw [e]
      simpa using this
  · have hc' : cnt.toNat < c.toNat := by
      have : ¬ c.toNat ≤ cnt.toNat := hc
      omega
    simp only [hc, ↓reduceIte, UInt64.mul_zero]
    refine ⟨⟨by simp [h.size]; omega, fun hne => absurd rfl hne⟩, fun h => h.elim⟩

theorem iotaIndexOk_run_eq (r : CoreFnsA) (fe : IFEnv) (d mI rP cnP : Nat) (tyCtor : EIdx)
    (margs idx : List EIdx) (a : AState) (h : mI = rP) :
    (iotaIndexOk r fe d mI rP cnP tyCtor margs idx).run a = .ok (true, a) := by
  simp [iotaIndexOk, h]; rfl

theorem iotaIndexOk_run_none (r : CoreFnsA) (fe : IFEnv) (d mI rP cnP : Nat) (tyCtor : EIdx)
    (margs idx : List EIdx) (a a₁ : AState) (h : mI ≠ rP)
    (hp : (piResidual tyCtor margs).run a = .ok (none, a₁)) :
    (iotaIndexOk r fe d mI rP cnP tyCtor margs idx).run a = .ok (false, a₁) := by
  simp only [iotaIndexOk, h, ↓reduceIte, StateT.run_bind, hp, except_ok_bind]; rfl

theorem iotaIndexOk_run_some (r : CoreFnsA) (fe : IFEnv) (d mI rP cnP : Nat) (tyCtor : EIdx)
    (margs idx : List EIdx) (a a₁ a₂ : AState) (res : EIdx) (xs : List EIdx) (b : Bool)
    (h : mI ≠ rP) (hp : (piResidual tyCtor margs).run a = .ok (some res, a₁))
    (hg : (getAppArgs coreWalkFuel res).run a₁ = .ok (xs, a₁))
    (hd : (defEqList r fe d (xs.drop cnP) idx).run a₁ = .ok (b, a₂)) :
    (iotaIndexOk r fe d mI rP cnP tyCtor margs idx).run a = .ok (b, a₂) := by
  simp only [iotaIndexOk, h, ↓reduceIte, StateT.run_bind, hp, except_ok_bind, hg, hd]

/-- **`iota_index_ok` refines `iotaIndexOk`.** Statement changes (the callees need them): `n ≤ 2 ^ 62`,
the eager bit `eb = (mode >>> 1) &&& 1`, and both slices below the stack top. -/
theorem iotaIndexOk_refines' (p : Prog) (hp : IotaProg' p) (hi1 : IotaInst1OK p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d mI rP cnP tyCtor mo mn xo xn : Word) (margs idx : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW tyCtor →
    SpineR s₀.mem mo mn margs → SpineR s₀.mem xo xn idx →
    mo.toNat + mn.toNat ≤ (spTop s₀.mem).toNat → xo.toNat + xn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p (n + 1) "iota_index_ok" [mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn]
      (iotaIndexOk (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat cnP.toNat
        (decE tyCtor) margs.toList idx.toList) decBool s₀ a₀ dn vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d mI rP cnP tyCtor mo mn xo xn margs idx hS hm4
    hebm hty hsm hsx htm htx
  refine triple_post (iotaIndexOk_spec p hp.iotaIndexOk n s₀ mode vis d mI rP cnP tyCtor mo mn xo
    xn) fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [ioW] at hW
  by_cases hI : mI = rP
  · rw [ite_eq_left hI] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hr1 : r.headD 0 = 1 := by simpa using hr.symm
    have hrun1 := iotaIndexOk_run_eq (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat
      cnP.toNat (decE tyCtor) margs.toList idx.toList a₀ (by rw [hI])
    refine CoreRef.of_pure hS hrun1 hm.symm ?_ ?_
    · simp only [decBool]; rw [hr1]; rfl
    · unfold ResH HW; rw [hr1]; decide
  rw [ite_eq_right hI] at hW
  have hI' : mI.toNat ≠ rP.toNat := fun h => hI (UInt64.toNat_inj.mp h)
  rcases hc1 : callW p n "pi_residual" [tyCtor, mo, mn] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
    simp only [hc1, reduceCtorEq] at hW
  obtain ⟨hrunP, ⟨M₁, hS₁, hK₁, hSt₁⟩, hr₁⟩ := CoreSpec.run
    (piResidual_refines p hp hi1 n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb tyCtor mo mn margs hS hty
      hsm htm) hc1
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hnone : decOptR r₁ = none := by simp only [decOptR, decOpt, h0, ↓reduceIte]
    rw [hnone] at hrunP
    have hrun1 := iotaIndexOk_run_none (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat
      cnP.toNat (decE tyCtor) margs.toList idx.toList a₀ _ hI' hrunP
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine CoreRef.of_run hrun1 ⟨M₁, hS₁, hK₁, hSt₁⟩ ?_ ?_
    · simp only [decBool]; rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [ite_eq_right h0] at hW
  obtain ⟨h136, hW⟩ := of_ite_none hW
  have h136' : (136 : Word).toNat < (m₁.arr64 CTL).size := Classical.not_not.mp h136
  obtain ⟨hf1, hh1⟩ := hr₁
  have hsome : decOptR r₁ = some (decE (r₁.tail.headD 0)) := by
    simp only [decOptR, decOpt, h0, ↓reduceIte]
  rw [hsome] at hrunP
  rcases hc2 : callW p n "get_app_args" [r₁.tail.headD 0] m₁ with _ | ⟨r₂, m₂⟩ <;>
    simp only [hc2, reduceCtorEq] at hW
  obtain ⟨t₂, ht₂, hloc2, hfr, hgrew, hhead, htop2, xs, hga, hsp2⟩ := triple_of_callW
    (getAppArgs_refines p hp.spine n ⟨m₁, Locals.init []⟩ (AM.st (piResidual (decE tyCtor) margs.toList) a₀)
      hS₁.arena.1 (r₁.tail.headD 0) hh1 hS₁.spn) hc2
  rw [ht₂] at hfr hgrew htop2 hsp2
  have hS₂ : CoreS dn m₂ (AM.st (piResidual (decE tyCtor) margs.toList) a₀) vis fe M₁ eb :=
    hS₁.frame_stk hfr (fun b hb => by simpa using hb) (fun x hx => by simpa using hx)
  have hsx₁ : SpineR m₁ xo xn idx := hsx.keep hSt₁.size hSt₁.below htx hS.spn
  have htx₁ : xo.toNat + xn.toNat ≤ (spTop m₁).toNat := by rw [hSt₁.1]; exact htx
  have hsx₂ : SpineR m₂ xo xn idx := hsx₁.keep hgrew.size hgrew.below htx₁ hS₁.spn
  have htx₂ : xo.toNat + xn.toNat ≤ (spTop m₂).toNat :=
    Nat.le_trans htx₁ (by have := hgrew.1; exact this)
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ n' =>
  rcases hc3 : callW p (n' + 1) "defeq_list" [mode, vis, d, r₂.headD 0 + cnP,
      (r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0), xo, xn] m₂ with _ | ⟨r₃, m₃⟩ <;>
    simp only [hc3, reduceCtorEq] at hW
  by_cases h136n : ¬ (136 : Word).toNat < (m₃.arr64 CTL).size
  · rw [ite_eq_right (by simpa using h136n)] at hW; cases hW
  have h136₃ : (136 : Word).toNat < (m₃.arr64 CTL).size := Classical.not_not.mp h136n
  rw [ite_eq_left h136₃] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hhead' : r₂.headD 0 = spTop m₁ := hhead
  have htop2' : spTop m₂ = spTop m₁ + r₂.tail.headD 0 := htop2
  obtain ⟨hsd, hsd2⟩ := spine_drop m₂ (r₂.headD 0) (r₂.tail.headD 0) cnP xs.toArray hsp2 hS₂.spn
  have hdrop : xs.toArray.toList.drop cnP.toNat = xs.drop cnP.toNat := by simp
  rw [hdrop] at hsd
  have htd : (r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0) ≠ 0 →
      (r₂.headD 0 + cnP).toNat + ((r₂.tail.headD 0 - cnP) * (if cnP ≤ r₂.tail.headD 0 then 1 else 0)).toNat
        ≤ (spTop m₂).toNat := by
    intro hne
    have hcle : cnP ≤ r₂.tail.headD 0 := by
      exact Classical.byContradiction fun hn => by
        simp only [hn, ↓reduceIte, UInt64.mul_zero, ne_eq, not_true_eq_false] at hne
    simp only [hcle, ↓reduceIte, UInt64.mul_one] at hne ⊢
    rw [hsd2 hcle]
    have hb := hsp2.bound
    rw [hhead'] at hb
    have hsp := hS₂.spn
    have : (spTop m₂).toNat = (spTop m₁).toNat + (r₂.tail.headD 0).toNat := by
      rw [htop2', UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [hhead', this]
    exact Nat.le_refl _
  obtain ⟨hrun3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hr₃⟩ := CoreSpec.run
    (defeqList_refines p hp n' (hk.mono (Nat.le_succ n')) F (by omega) (by omega)
      ⟨m₂, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₂.headD 0 + cnP) _ xo xn
      (xs.drop cnP.toNat).toArray idx hS₂ hm4 hebm hsd hsx₂.toN htd (fun _ => htx₂)) hc3
  simp only at hrun3
  have hrunF := iotaIndexOk_run_some (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat
    cnP.toNat (decE tyCtor) margs.toList idx.toList a₀ _ _ (decE (r₁.tail.headD 0)) xs (decBool r₃)
    hI' hrunP hga hrun3
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrunF
  have hr3 : r₃.headD 0 = r.headD 0 := by simpa using hr
  refine ⟨hokF, ⟨M₃, ?_, hK₁.trans hK₃, ?_⟩, ?_, ?_⟩
  · rw [hstF, ← hm]
    exact hS₃.frame_stk (MemFrame.setCtl m₃ 136 _) (by simp) (by simp)
  · rw [← hm]
    have t1 : spTop m₁ = spTop s₀.mem := hSt₁.1
    refine hSt₁.trans ?_
    exact StackKept.restoreG (hgrew.trans hSt₃.toGrew) h136₃
  · rw [hresF]; simp only [decBool]; rw [← hr3]
  · unfold ResH HW; rw [← hr3]; exact hr₃

/-! ## `tower_slots_all(vis, T, nF)` -/

/-- **`tower_slots_all` is its model `tsW`** (generated; the loop is `tsW.loop1`). -/
l_model towerSlotsAll_spec (p : Prog) (hp : p.lookup "tower_slots_all" = some towerSlotsAllL)
  fns [hp ↦ tsW list]
  specs [callW_spec p n "find_proj"]
  grind [arena_grind] simp []

theorem towerSlotsAllGo_stop (fe : IFEnv) (T : NIdx) (n j : Nat) (h : fe.findProj? T j = none) :
    towerSlotsAllGo fe T (n + 1) j = false := by
  simp only [towerSlotsAllGo, h]

theorem towerSlotsAllGo_cont (fe : IFEnv) (T : NIdx) (n j : Nat) (e : IProjEntry)
    (h : fe.findProj? T j = some e) :
    towerSlotsAllGo fe T (n + 1) j = towerSlotsAllGo fe T n (j + 1) := by
  simp only [towerSlotsAllGo, h]

/-- **The `tower_slots_all` loop refines `towerSlotsAllGo`**, by induction on the remaining count. -/
theorem tsW_ok (p : Prog) (hfp : FindProjOK p) (hpf : ProjFound p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb T nF : Word) (hT : HW T) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (j : Word) (L : List Word) (m' : Mem),
      nF.toNat - j.toNat = K → j.toNat ≤ nF.toNat → CoreS dn m a vis fe M eb →
      tsW.loop1 p k m vis T nF j = some (L, m') →
      CoreAfter dn m m' a vis fe M eb ∧
      towerSlotsAllGo fe (decI T) K j.toNat = decBool L ∧ HW (L.headD 0) := by
  intro K
  induction K with
  | zero =>
    intro k m a M j L m' hK hj hS hL
    have hn : ¬ j < nF := fun h => by
      have : j.toNat < nF.toNat := h
      omega
    cases k with
    | zero => simp [tsW.loop1] at hL
    | succ k =>
    rw [tsW.loop1.arm2 (hc1 := hn)] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    exact ⟨⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, by simp [towerSlotsAllGo, decBool],
      by simp [HW]⟩
  | succ K ih =>
    intro k m a M j L m' hK hj hS hL
    have hlt : j < nF := by
      have : j.toNat < nF.toNat := by omega
      exact this
    cases k with
    | zero => simp [tsW.loop1] at hL
    | succ k =>
    rcases hc : callW p k "find_proj" [vis, T, j] m with _ | ⟨r₁, m₁⟩
    · rw [tsW.loop1.arm1 (hc1 := hlt), hc, tsW.k_find_proj.none] at hL; cases hL
    obtain ⟨-, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hr₁⟩ := CoreSpec.of_callW
      (hfp k ⟨m, Locals.init []⟩ a dn vis fe M eb T j hS hT) hc
    have hfx : fe.findProj? (decI T) j.toNat =
        decEntry (m.arr64 EREC) (r₁.headD 0) (r₁.tail.headD 0) j.toNat := hres
    by_cases h0 : r₁.headD 0 = 0
    · rw [tsW.loop1.arm1 (hc1 := hlt), hc, tsW.k_find_proj.arm1 (hc1 := h0)] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      have hnone : fe.findProj? (decI T) j.toNat = none := by
        rw [hfx]; simp only [decEntry, h0, ↓reduceIte]
      exact ⟨⟨M₁, hS₁, hK₁, hSt₁⟩, by rw [towerSlotsAllGo_stop _ _ _ _ hnone]; simp [decBool],
        by simp [HW]⟩
    · rw [tsW.loop1.arm1 (hc1 := hlt), hc, tsW.k_find_proj.arm2 (hc1 := h0)] at hL
      obtain ⟨tbl, htbl, -⟩ := hpf k m a dn vis fe M eb T j r₁ m₁ hS hc h0
      have hsome : fe.findProj? (decI T) j.toNat = some (tbl.entry j.toNat) := by
        rw [hfx]; simp only [decEntry, ite_eq_right h0, htbl, Option.map_some]
      have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat nF j hlt
      obtain ⟨⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hL1⟩ := ih k m₁ _ M₁ (j + 1) L m'
        (by omega) (by omega) hS₁ hL
      rw [h1] at hres2
      exact ⟨⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩,
        by rw [towerSlotsAllGo_cont _ _ _ _ _ hsome]; exact hres2, hL1⟩

/-- **`tower_slots_all` refines `towerSlotsAll`** (`find_proj` and its decoding fact as
`ProjCallees`'s two fields). -/
theorem towerSlotsAll_refines' (p : Prog) (hp : IotaProg' p) (hfp : FindProjOK p) (hpf : ProjFound p) :
    TowerSlotsAllOK p := by
  intro n s₀ a₀ dn vis fe MM eb T nF hS hT
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (towerSlotsAll_spec p hp.towerSlotsAll (n + 1) s₀ vis T nF) fun r s' ⟨hloc, hW⟩ =>
    ⟨hloc, ?_⟩
  rw [tsW.arm1] at hW
  obtain ⟨hca, hres, hL1⟩ := tsW_ok p hfp hpf dn vis fe eb T nF hT (nF.toNat - (0 : Word).toNat) (n + 1)
    s₀.mem a₀ MM 0 r s'.mem rfl (by simp) hS hW
  refine ⟨by unfold AM.ok; exact trivial, hca, ?_, hL1⟩
  · show towerSlotsAll fe (decI T) nF.toNat = decBool r
    simpa [towerSlotsAll] using hres


/-! ## `inst_spine(ao, an, t, e)` -/

/-- **`inst_spine` is its model `isW`** (generated; the loop is `isW.loop1`). -/
l_model instSpine_spec (p : Prog) (hp : p.lookup "inst_spine" = some instSpineL)
  fns [hp ↦ isW]
  specs [callW_spec p n "inst_entry"]
  grind [arena_grind] simp []

theorem instSpine_nil_run (fuel : Nat) (t : Nat) (e : EIdx) (a : AState) :
    (instSpine fuel [] t e).run a = .ok (e, a) := by
  simp [instSpine]; rfl

theorem instSpine_cons_run (fuel : Nat) (x : EIdx) (xs : List EIdx) (t : Nat) (e e' : EIdx)
    (a a₁ a₂ : AState) (res : EIdx) (h : (instantiate1Fast fuel e x t).run a = .ok (e', a₁))
    (hr : (instSpine fuel xs (t - 1) e').run a₁ = .ok (res, a₂)) :
    (instSpine fuel (x :: xs) t e).run a = .ok (res, a₂) := by
  simp only [instSpine, StateT.run_bind, h, except_ok_bind]; exact hr

/-- **The `inst_spine` loop refines `instSpine`**, by induction on the remaining count. -/
theorem isW_ok (p : Prog) (hinst : IotaInst1OK p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb ao an : Word) (args : Array EIdx) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (t e i : Word) (tN : Nat) (r : Word) (m' : Mem),
      an.toNat - i.toNat = K → i.toNat ≤ an.toNat → an.toNat - i.toNat ≤ t.toNat + 1 →
      (an.toNat - i.toNat ≠ 0 → tN = t.toNat) →
      CoreS dn m a vis fe M eb → HW e → SpineR m ao an args →
      ao.toNat + an.toNat ≤ (spTop m).toNat →
      isW.loop1 p k m ao an t e i = some (r, m') →
      AM.ok (instSpine coreWalkFuel (args.toList.drop i.toNat) tN (decE e)) a ∧
      CoreAfter dn m m' (AM.st (instSpine coreWalkFuel (args.toList.drop i.toNat) tN (decE e)) a) vis fe M eb ∧
      AM.res (instSpine coreWalkFuel (args.toList.drop i.toNat) tN (decE e)) a = decE r ∧ HW r := by
  intro K
  induction K with
  | zero =>
    intro k m a M t e i tN r m' hK hia ht htN hS he hsp htop hL
    have hn : ¬ i < an := fun h => by
      have : i.toNat < an.toNat := h
      omega
    cases k with
    | zero => simp [isW.loop1] at hL
    | succ k =>
    rw [isW.loop1.arm2 (hc1 := hn)] at hL
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
    have hdrop : args.toList.drop i.toNat = [] := by
      apply List.drop_eq_nil_of_le; simp [hsp.size]; omega
    rw [hdrop]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (instSpine_nil_run coreWalkFuel tN (decE e) a)
    exact ⟨hok, by rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hres, he⟩
  | succ K ih =>
    intro k m a M t e i tN r m' hK hia ht htN hS he hsp htop hL
    have hlt : i < an := by
      have : i.toNat < an.toNat := by omega
      exact this
    have hlt' : i.toNat < an.toNat := hlt
    have hsz : i.toNat < args.size := by rw [hsp.size]; exact hlt'
    have hdrop : args.toList.drop i.toNat = args[i.toNat] :: args.toList.drop (i.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hsz)]; simp
    have hget : args[i.toNat] = decE (rdW (m.arr64 SPN) (ao + i)) := by
      have := hsp.get i.toNat hsz
      simpa [spW, toUInt64_toNat_self] using this
    rw [hget] at hdrop
    have htt : tN = t.toNat := htN (by omega)
    cases k with
    | zero => simp [isW.loop1] at hL
    | succ k =>
    rcases hc : callW p k "inst_entry" [e, rdW (m.arr64 SPN) (ao + i), t] m with _ | ⟨r₁, m₁⟩
    · rw [isW.loop1.arm1 (hc1 := hlt), hc, isW.k_inst_entry.none] at hL; cases hL
    rw [isW.loop1.arm1 (hc1 := hlt), hc, isW.k_inst_entry.arm1] at hL
    obtain ⟨hrunT, ⟨M₁, hS₁, hK₁, hSt₁⟩, hr₁⟩ := CoreSpec.run
      (hinst k ⟨m, Locals.init []⟩ a dn vis fe M eb e (rdW (m.arr64 SPN) (ao + i)) t hS he) hc
    have hsp₁ : SpineR m₁ ao an args := hsp.keep hSt₁.size hSt₁.below htop hS.spn
    have htop₁ : ao.toNat + an.toNat ≤ (spTop m₁).toNat := by rw [hSt₁.1]; exact htop
    have h1 : (i + 1).toNat = i.toNat + 1 := uint64_succ_toNat an i hlt
    have ht1 : (an.toNat - (i.toNat + 1) ≠ 0 → tN - 1 = (t - 1).toNat) := by
      intro hne
      have ht0 : t ≠ 0 := fun h => by subst h; simp at ht; omega
      have : (t - 1).toNat = t.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by
          have : t.toNat ≠ 0 := fun h => ht0 (UInt64.toNat_inj.mp (by simpa using h))
          simp [UInt64.le_iff_toNat_le]; omega)]
        simp
      rw [this, htt]
    obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hr⟩ := ih k m₁ _ M₁ (t - 1) (r₁.headD 0) (i + 1) (tN - 1)
      r m' (by omega) (by omega) (by
        have e0 : an.toNat - (i + 1).toNat = an.toNat - i.toNat - 1 := by omega
        by_cases ht0 : t = 0
        · have h00 : t.toNat = 0 := by rw [ht0]; rfl
          rw [e0]; omega
        · have ht0' : t.toNat ≠ 0 := fun h => ht0 (UInt64.toNat_inj.mp (by simpa using h))
          have : (t - 1).toNat = t.toNat - 1 := by
            rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
            simp
          rw [e0, this]; omega)
      (by rw [h1]; exact ht1) hS₁ hr₁ hsp₁ htop₁ hL
    have hrunR := AM.run_of_ok _ _ hok2
    rw [h1] at hrunR
    rw [h1] at hS₂ hres2
    have hrun := instSpine_cons_run coreWalkFuel (decE (rdW (m.arr64 SPN) (ao + i)))
      (args.toList.drop (i.toNat + 1)) tN (decE e) (decH r₁) a _ _ _
      (by rw [htt]; exact hrunT) hrunR
    rw [hdrop]
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hokF, ⟨M₂, ?_, hK₁.trans hK₂, hSt₁.trans hSt₂⟩, ?_, hr⟩
    · rw [hstF]; exact hS₂
    · rw [hresF]; exact hres2

/-- **`inst_spine` refines `instSpine`.** Statement changes: `ao + an ≤ spTop` (the slice is below the
top, so `inst_entry` leaves it alone) and `an ≤ t + 1` (the L counter `t - 1` wraps where the twin's
`Nat` subtraction saturates; with `an ≤ t + 1` it is only after the last use). -/
theorem instSpine_refines' (p : Prog) (hp : IotaProg' p) (hi1 : IotaInst1OK p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ao an t e : Word) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW e → SpineR s₀.mem ao an args → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    an.toNat ≤ t.toNat + 1 →
    CoreSpec p n "inst_spine" [ao, an, t, e] (instSpine coreWalkFuel args.toList t.toNat (decE e))
      decH s₀ a₀ dn vis fe MM eb := by
  intro n s₀ a₀ dn vis fe MM eb ao an t e args hS he hsp htop ht
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (instSpine_spec p hp.instSpine (n + 1) s₀ ao an t e) fun r s' ⟨hloc, hW⟩ => ⟨hloc,
    ?_⟩
  rw [isW.arm1] at hW
  cases hL : isW.loop1 p (n + 1) s₀.mem ao an t e 0 with
  | none => rw [hL, isW.k_loop1.none] at hW; cases hW
  | some q =>
  obtain ⟨e', m'⟩ := q
  rw [hL, isW.k_loop1.arm1] at hW
  obtain ⟨he', hm'⟩ := Prod.mk.inj (Option.some.inj hW)
  subst he' hm'
  obtain ⟨hok, hca, hres, hr⟩ := isW_ok p hi1 dn vis fe eb ao an args
    (an.toNat - (0 : Word).toNat) (n + 1) s₀.mem a₀ MM t e 0 t.toNat (r.headD 0) s'.mem rfl (by simp)
    (by simpa using ht) (fun _ => rfl) hS he hsp htop hL
  refine ⟨hok, ?_, ?_, hr⟩
  · simpa using hca
  · simpa [decH] using hres

/-! ## `inst_spine_pins(po, pl, us, ao, an, rP, pvo, pvc)` -/

/-- Model of the `inst_spine_pins` loop at L fuel `k`. -/
def ispW (p : Prog) (po pl us ao an rP pvo pvc so : Word) : Nat → Mem → Word → Option Mem
  | 0, _, _ => none
  | k + 1, m, j =>
    if j < pvc then
      match callW p k "inst_lp" [po, pl, us, rdW (m.arr64 SPN) (pvo + j)] m with
      | none => none
      | some (r₁, m₁) =>
        match callW p k "inst_spine" [ao, an, rP - 1, r₁.headD 0] m₁ with
        | none => none
        | some (r₂, m₂) =>
          if (so + j).toNat < (m₂.arr64 SPN).size ∧ (136 : Word).toNat < (m₂.arr64 CTL).size then
            ispW p po pl us ao an rP pvo pvc so k
              ((m₂.set64 SPN (so + j) (r₂.headD 0)).set64 CTL 136 (so + j + 1)) (j + 1)
          else none
    else some m

theorem ispW_end (p : Prog) (po pl us ao an rP pvo pvc so : Word) (k : Nat) (m : Mem) (j : Word)
    (h : ¬ j < pvc) : ispW p po pl us ao an rP pvo pvc so (k + 1) m j = some m := by
  simp only [ispW, h, ↓reduceIte]

theorem ispW_cont (p : Prog) (po pl us ao an rP pvo pvc so : Word) (k : Nat) (m m₁ m₂ : Mem) (j : Word)
    (r₁ r₂ : List Word) (h : j < pvc)
    (hc1 : callW p k "inst_lp" [po, pl, us, rdW (m.arr64 SPN) (pvo + j)] m = some (r₁, m₁))
    (hc2 : callW p k "inst_spine" [ao, an, rP - 1, r₁.headD 0] m₁ = some (r₂, m₂))
    (hg : (so + j).toNat < (m₂.arr64 SPN).size ∧ (136 : Word).toNat < (m₂.arr64 CTL).size) :
    ispW p po pl us ao an rP pvo pvc so (k + 1) m j =
      ispW p po pl us ao an rP pvo pvc so k
        ((m₂.set64 SPN (so + j) (r₂.headD 0)).set64 CTL 136 (so + j + 1)) (j + 1) := by
  simp only [ispW, h, ↓reduceIte, hc1, hc2, hg, and_self]

theorem ispW_bad (p : Prog) (po pl us ao an rP pvo pvc so : Word) (k : Nat) (m m₁ m₂ : Mem) (j : Word)
    (r₁ r₂ : List Word) (h : j < pvc)
    (hc1 : callW p k "inst_lp" [po, pl, us, rdW (m.arr64 SPN) (pvo + j)] m = some (r₁, m₁))
    (hc2 : callW p k "inst_spine" [ao, an, rP - 1, r₁.headD 0] m₁ = some (r₂, m₂))
    (hg : ¬ ((so + j).toNat < (m₂.arr64 SPN).size ∧ (136 : Word).toNat < (m₂.arr64 CTL).size)) :
    ispW p po pl us ao an rP pvo pvc so (k + 1) m j = none := by
  simp only [ispW, h, ↓reduceIte, hc1, hc2, hg]

theorem instSpinePinsLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p k instSpinePinsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 7 = s₀.loc 7 ∧ s'.loc 8 = s₀.loc 8 ∧
      ispW p (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6) (s₀.loc 7)
        (s₀.loc 8) k s₀.mem (s₀.loc 9) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := instSpinePinsLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        callW_spec p k "inst_lp", callW_spec p k "inst_spine", ih] <;>
      finish [ispW_end, ispW_cont, ispW_bad]


/-- A leading part of a spine slice. -/
theorem SpineR.take {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (c : Word) (hc : c.toNat ≤ cnt.toNat) :
    SpineR m off c (xs.toList.take c.toNat).toArray := by
  have hb := h.bound
  refine ⟨by simp [h.size]; omega, by omega, fun i hi => h.lt i (by omega), fun i hi => ?_⟩
  have hi' : i < xs.size := by
    simp only [List.size_toArray, List.length_take, Array.length_toList] at hi
    omega
  have := h.get i hi'
  simpa [List.getElem_take] using this

theorem instSpinePins_take (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat) :
    ∀ pins : List EIdx, instSpinePins lps us (args.take rP) rP pins = instSpinePins lps us args rP pins
  | [] => rfl
  | x :: xs => by
    simp only [instSpinePins, List.take_take, Nat.min_self, instSpinePins_take lps us args rP xs]

/-- The spine length `inst_spine_pins` reads: `an`, at most `rP` (the twin's `args.take rP`). -/
def ispLen (an rP : Word) : Word := if rP < an then rP else an

theorem ispLen_le (an rP : Word) : (ispLen an rP).toNat ≤ an.toNat ∧ (ispLen an rP).toNat ≤ rP.toNat := by
  unfold ispLen
  split
  · rename_i h; have := UInt64.lt_iff_toNat_lt.mp h; omega
  · rename_i h; have := UInt64.not_lt.mp h; have := UInt64.le_iff_toNat_le.mp this; omega

theorem ispLen_take (an rP : Word) (xs : List EIdx) (h : xs.length = an.toNat) :
    xs.take (ispLen an rP).toNat = xs.take rP.toNat := by
  unfold ispLen
  split
  · rfl
  · rename_i h'
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h')
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- `ispLen` as a cap: a list of length `an` taken to `min cp an` is the list taken to `cp`. -/
theorem ispLen_take' (cp an : Word) (xs : List EIdx) (h : xs.length = an.toNat) :
    xs.take (ispLen cp an).toNat = xs.take cp.toNat := by
  unfold ispLen
  split
  · rename_i h'
    have := UInt64.lt_iff_toNat_lt.mp h'
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  · rfl

/-- Model of `inst_spine_pins`. -/
def ispTop (p : Prog) (k : Nat) (m : Mem) (po pl us ao an rP pvo pvc : Word) :
    Option (List Word × Mem) :=
  if (136 : Word).toNat < (m.arr64 CTL).size then
    if UInt64.ofNat (m.arr64 SPN).size < rdW (m.arr64 CTL) 136 then none
    else if UInt64.ofNat (m.arr64 SPN).size - rdW (m.arr64 CTL) 136 < pvc then none
    else match ispW p po pl us ao (ispLen an rP) rP pvo pvc (rdW (m.arr64 CTL) 136) (k + 1) m 0 with
      | none => none
      | some m' => some ([rdW (m.arr64 CTL) 136, pvc], m')
  else none

theorem getD_136 (a : Array Word) (h : 136 < a.size) : a[136]?.getD 0 = a[136] := by simp [h]

theorem instSpinePins_spec (p : Prog) (hp : p.lookup "inst_spine_pins" = some instSpinePinsL)
    (k : Nat) (s₀ : St) (po pl us ao an rP pvo pvc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (k + 1)) "inst_spine_pins" [po, pl, us, ao, an, rP, pvo, pvc]
    ⦃fun r s' => LocEq s' s₀ ∧ ispTop p k s₀.mem po pl us ao an rP pvo pvc = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, instSpinePinsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    fun s₀ => Triple.step_exec (instSpinePinsLoop_spec p (k + 1) s₀)] <;>
  simp_all [ispTop, Cmp.eval, BinOp.eval, Mem.len64, LocEq, St.setLoc_loc,
    St.setLoc_mem, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr, rdW, CTL] <;>
  (have h136 : 136 < (s₀.mem.arr64 1).size := by assumption
   refine ⟨h136, ?_⟩
   first
   | (rw [show ispLen an rP = rP from ite_eq_left (of_decide_eq_true (by assumption))]; simp_all [SPN])
   | (rw [show ispLen an rP = an from ite_eq_right (fun h => absurd (decide_eq_true h) (by simp_all))]
            simp_all [SPN])
   | simp_all [getD_136 _ h136, SPN])

/-! ### The push of `inst_spine_pins`: one word stored at the top, the top raised -/

/-- Storing `v` at the top `q` of the stack and raising the top: the frame, the new top, the slot,
and that the stack below the old top is as it was. -/
theorem push_step (m : Mem) (q v : Word) (hq : q.toNat < (m.arr64 SPN).size)
    (h136 : (136 : Word).toNat < (m.arr64 CTL).size) (htop : spTop m = q)
    (hq1 : q.toNat + 1 < 2 ^ 64) :
    MemFrame [SPN] [136] m ((m.set64 SPN q v).set64 CTL 136 (q + 1)) ∧
    spTop ((m.set64 SPN q v).set64 CTL 136 (q + 1)) = q + 1 ∧
    StackGrew m ((m.set64 SPN q v).set64 CTL 136 (q + 1)) ∧
    spW ((m.set64 SPN q v).set64 CTL 136 (q + 1)) q = v ∧
    (((m.set64 SPN q v).set64 CTL 136 (q + 1)).arr64 SPN).size = (m.arr64 SPN).size := by
  have f1 : MemFrame [SPN] [136] m (m.set64 SPN q v) :=
    (MemFrame.set64 m SPN (by decide) q v).mono (fun b hb => hb)
      (fun x hx => absurd hx (by simp))
  have f2 : MemFrame [SPN] [136] (m.set64 SPN q v) ((m.set64 SPN q v).set64 CTL 136 (q + 1)) :=
    (MemFrame.setCtl (m.set64 SPN q v) 136 (q + 1)).mono (fun b hb => absurd hb (by simp))
      (fun x hx => hx)
  have hsz : (((m.set64 SPN q v).set64 CTL 136 (q + 1)).arr64 SPN).size = (m.arr64 SPN).size := by
    rw [size_set64, size_set64]
  have htop' : spTop ((m.set64 SPN q v).set64 CTL 136 (q + 1)) = q + 1 := by
    unfold spTop
    rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [size_set64]; exact h136⟩]
  have hq1' : (q + 1).toNat = q.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  refine ⟨f1.trans f2, htop', ⟨?_, hsz, fun i hi => ?_, BKept.of_frame (f1.trans f2) (by decide) (by decide),
    PoolGrew.of_frame (f1.trans f2) (by decide) (by decide)⟩, ?_, hsz⟩
  · rw [htop', htop, UInt64.le_iff_toNat_le, hq1']; omega
  · rw [spW_setCtl]
    have : q ≠ i := by
      intro h; rw [htop, ← h] at hi
      exact absurd (UInt64.lt_iff_toNat_lt.mp hi) (Nat.lt_irrefl _)
    rw [spW_set64_ne _ _ _ _ this]
  · rw [spW_setCtl, spW_set64_eq _ _ _ hq]

theorem word_succ_add (off : Word) (i : Nat) :
    off + (i + 1).toUInt64 = (off + 1) + i.toUInt64 := by
  simp [Nat.toUInt64, UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm]

/-- A slot followed by a spine slice is a spine slice. -/
theorem SpineR.cons_slot (m : Mem) (off cnt v : Word) (ys : List EIdx) (hv : HW v)
    (hslot : spW m off = v) (htail : SpineR m (off + 1) cnt ys.toArray)
    (hb : off.toNat + cnt.toNat + 1 ≤ (m.arr64 SPN).size) (hcap : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m off (cnt + 1) (decE v :: ys).toArray := by
  have hc1 : (cnt + 1).toNat = cnt.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have ho1 : (off + 1).toNat = off.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hsize := htail.size
  simp only [List.size_toArray] at hsize
  refine ⟨by simp [hsize, hc1], by rw [hc1]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hc1] at hi
    cases i with
    | zero => simpa [hslot, HW] using hv
    | succ i =>
      rw [word_succ_add]
      exact htail.lt i (by omega)
  · simp only [List.size_toArray, List.length_cons] at hi
    cases i with
    | zero => simp [hslot]
    | succ i =>
      rw [word_succ_add]
      have := htail.get i (by simp only [List.size_toArray]; omega)
      simpa using this

theorem instSpinePins_nil_run (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat)
    (a : AState) : (instSpinePins lps us args rP []).run a = .ok ([], a) := by
  simp [instSpinePins]; rfl

theorem instSpinePins_cons_run (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat)
    (x : EIdx) (xs : List EIdx) (a a₁ a₂ a₃ : AState) (q s : EIdx) (ys : List EIdx)
    (h1 : (instLPFast coreWalkFuel lps us x).run a = .ok (q, a₁))
    (h2 : (instSpine coreWalkFuel (args.take rP) (rP - 1) q).run a₁ = .ok (s, a₂))
    (h3 : (instSpinePins lps us args rP xs).run a₂ = .ok (ys, a₃)) :
    (instSpinePins lps us args rP (x :: xs)).run a = .ok (s :: ys, a₃) := by
  simp only [instSpinePins, StateT.run_bind, h1, except_ok_bind, h2, h3]; rfl

/-- **`inst_lp` and `inst_spine` leave the record pool alone** (new stub assumption, as `ErecKept`
for `find_proj`/`fire_ok`): `inst_spine_pins` re-reads the level-parameter slice `(po, pl)` of
`EREC` at every iteration, the twin holds it as a value. -/
def ErecKeptInst (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    (f = "inst_lp" ∨ f = "inst_spine") → callW p n f vs m = some (r, m') →
    m'.arr64 EREC = m.arr64 EREC

set_option maxRecDepth 8192 in
/-- `ErecKeptInst` from the core's write set (`CoreErec.lean`). -/
theorem ErecKeptInst.of_closed {p : Prog} (hcl : closedA p coreErecA coreErecC coreFns = true) :
    ErecKeptInst p :=
  fun _ _ _ _ _ _ hf h => callW_erec_closed hcl (by rcases hf with rfl | rfl <;> decide) h

theorem SpineR.nil_at (m : Mem) (off : Word) (h : off.toNat ≤ (m.arr64 SPN).size) :
    SpineR m off 0 #[] :=
  ⟨rfl, by simpa using h, fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩

/-- **The `inst_spine_pins` loop refines `instSpinePins`**, by induction on the remaining count. -/
theorem ispW_ok (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hE : ErecKeptInst p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb po pl us ao an rP pvo pvc so : Word) (hus : HW us) (lps : List NIdx) (args pins : Array EIdx) :
    ∀ (K k : Nat) (m : Mem) (a : AState) (M : ModeMaps) (j : Word) (m' : Mem),
      pvc.toNat - j.toNat = K → j.toNat ≤ pvc.toNat → CoreS dn m a vis fe M eb →
      hslice? (m.arr64 EREC) po.toNat pl.toNat = some lps →
      spTop m = so + j → so.toNat + pvc.toNat ≤ (m.arr64 SPN).size →
      ao.toNat + an.toNat ≤ so.toNat → pvo.toNat + pvc.toNat ≤ so.toNat →
      an.toNat ≤ rP.toNat → SpineR m ao an args → SpineR m pvo pvc pins →
      ispW p po pl us ao an rP pvo pvc so k m j = some m' →
      ∃ ys, AM.ok (instSpinePins lps (decI us) args.toList rP.toNat (pins.toList.drop j.toNat)) a ∧
        CoreAfterG dn m m' (AM.st (instSpinePins lps (decI us) args.toList rP.toNat
          (pins.toList.drop j.toNat)) a) vis fe M eb ∧
        AM.res (instSpinePins lps (decI us) args.toList rP.toNat (pins.toList.drop j.toNat)) a = ys ∧
        SpineR m' (so + j) (pvc - j) ys.toArray := by
  intro K
  induction K with
  | zero =>
    intro k m a M j m' hK hj hS hlps htop hso hat hpt hanr hsa hsp hL
    have hn : ¬ j < pvc := fun h => by
      have : j.toNat < pvc.toNat := h
      omega
    cases k with
    | zero => simp [ispW] at hL
    | succ k =>
    rw [ispW_end p po pl us ao an rP pvo pvc so k m j hn] at hL
    cases hL
    have hdrop : pins.toList.drop j.toNat = [] := by
      apply List.drop_eq_nil_of_le; simp [hsp.size]; omega
    rw [hdrop]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
      (instSpinePins_nil_run lps (decI us) args.toList rP.toNat a)
    refine ⟨[], hok, ?_, hres, ?_⟩
    · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, (StackKept.refl _).toGrew⟩
    · have hjp : pvc - j = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
        simp; omega
      rw [hjp]
      have hlen : (so + j).toNat ≤ (m.arr64 SPN).size := by
        have := hS.spn
        rw [UInt64.toNat_add]; simp; omega
      exact SpineR.nil_at m _ hlen
  | succ K ih =>
    intro k m a M j m' hK hj hS hlps htop hso hat hpt hanr hsa hsp hL
    have hlt : j < pvc := by
      have : j.toNat < pvc.toNat := by omega
      exact this
    have hlt' : j.toNat < pvc.toNat := hlt
    cases k with
    | zero => simp [ispW] at hL
    | succ k =>
    have hspn := hS.spn
    have hsoj : (so + j).toNat = so.toNat + j.toNat := by
      rw [UInt64.toNat_add]; simp; omega
    have hszp : j.toNat < pins.size := by rw [hsp.size]; exact hlt'
    have hdrop : pins.toList.drop j.toNat = pins[j.toNat] :: pins.toList.drop (j.toNat + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hszp)]; simp
    have hget : pins[j.toNat] = decE (rdW (m.arr64 SPN) (pvo + j)) := by
      have := hsp.get j.toNat hszp
      simpa [spW, toUInt64_toNat_self] using this
    have hpinw : HW (rdW (m.arr64 SPN) (pvo + j)) := by
      have := hsp.lt j.toNat hlt'
      unfold HW; simpa [spW, toUInt64_toNat_self] using this
    rw [hget] at hdrop
    rcases hc1 : callW p k "inst_lp" [po, pl, us, rdW (m.arr64 SPN) (pvo + j)] m with _ | ⟨r₁, m₁⟩
    · simp only [ispW, hlt, ↓reduceIte, hc1] at hL; cases hL
    obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hr₁⟩ := CoreSpec.of_callW
      (hw.instLP k ⟨m, Locals.init []⟩ a dn vis fe M eb po pl us _ lps hS hpinw hus hlps) hc1
    have hSt₁ : StackKept m m₁ := hSt₁
    have hEr1 : m₁.arr64 EREC = m.arr64 EREC := hE k "inst_lp" _ m r₁ m₁ (Or.inl rfl) hc1
    have hlps₁ : hslice? (m₁.arr64 EREC) po.toNat pl.toNat = some lps := by rw [hEr1]; exact hlps
    have htopm : (so.toNat + j.toNat) ≤ (spTop m).toNat := by rw [htop, hsoj]; exact Nat.le_refl _
    have hsa₁ : SpineR m₁ ao an args := hsa.keep hSt₁.size hSt₁.below (by omega) hspn
    have hat₁ : ao.toNat + an.toNat ≤ (spTop m₁).toNat := by
      rw [hSt₁.1]; omega
    rcases hc2 : callW p k "inst_spine" [ao, an, rP - 1, r₁.headD 0] m₁ with _ | ⟨r₂, m₂⟩
    · simp only [ispW, hlt, ↓reduceIte, hc1, hc2] at hL; cases hL
    have hrP : an.toNat ≤ (rP - 1).toNat + 1 := by
      by_cases h0 : rP = 0
      · subst h0; simp at hanr; omega
      · have : rP.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
        rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
        simp; omega
    obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hr₂⟩ := CoreSpec.of_callW
      (instSpine_refines' p hp hc.inst1 k ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb ao an (rP - 1) (r₁.headD 0)
        args hS₁ hr₁ hsa₁ hat₁ hrP) hc2
    have hEr2 : m₂.arr64 EREC = m₁.arr64 EREC := hE k "inst_spine" _ m₁ r₂ m₂ (Or.inr rfl) hc2
    have hSt₂ : StackKept m₁ m₂ := hSt₂
    by_cases hgn : ¬ ((so + j).toNat < (m₂.arr64 SPN).size ∧ (136 : Word).toNat < (m₂.arr64 CTL).size)
    · rw [ispW_bad p po pl us ao an rP pvo pvc so k m m₁ m₂ j r₁ r₂ hlt hc1 hc2 hgn] at hL; cases hL
    have hg := Classical.not_not.mp hgn
    rw [ispW_cont p po pl us ao an rP pvo pvc so k m m₁ m₂ j r₁ r₂ hlt hc1 hc2 hg] at hL
    have hv32 : HW (r₂.headD 0) := hr₂
    have htop₂ : spTop m₂ = so + j := by rw [hSt₂.1, hSt₁.1]; exact htop
    have hsz1 : (m₁.arr64 SPN).size = (m.arr64 SPN).size := hSt₁.size
    have hsz2 : (m₂.arr64 SPN).size = (m.arr64 SPN).size := hSt₂.size.trans hsz1
    have hjpv : (so + j).toNat + 1 < 2 ^ 64 := by omega
    obtain ⟨hfr, hsp3, hgrew, hslot, hsz3⟩ := push_step m₂ (so + j) (r₂.headD 0) hg.1 hg.2 htop₂ hjpv
    have hS₃ := hS₂.frame_stk hfr (by simp) (by simp)
    have hEr3 : ((m₂.set64 SPN (so + j) (r₂.headD 0)).set64 CTL 136 (so + j + 1)).arr64 EREC =
        m.arr64 EREC := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide), hEr2, hEr1]
    have hso₂ : so.toNat + pvc.toNat ≤ (m₂.arr64 SPN).size := by rw [hsz2]; exact hso
    have hat₂ : ao.toNat + an.toNat ≤ (spTop m₂).toNat := by rw [htop₂, hsoj]; omega
    have hpt₂ : pvo.toNat + pvc.toNat ≤ (spTop m₂).toNat := by rw [htop₂, hsoj]; omega
    have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := by rw [hsz2]; exact hS.spn
    have hsa₂ : SpineR m₂ ao an args := hsa₁.keep hSt₂.size hSt₂.below hat₁ hS₁.spn
    have hsp₁ : SpineR m₁ pvo pvc pins := hsp.keep hSt₁.size hSt₁.below (by omega) hspn
    have hsp₂ : SpineR m₂ pvo pvc pins := hsp₁.keep hSt₂.size hSt₂.below (by rw [hSt₁.1]; omega) hS₁.spn
    have hsa₃ := hsa₂.keep hgrew.size hgrew.below hat₂ hspn₂
    have hsp₃ := hsp₂.keep hgrew.size hgrew.below hpt₂ hspn₂
    have h1 : (j + 1).toNat = j.toNat + 1 := uint64_succ_toNat pvc j hlt
    have hlps₃ : hslice? (((m₂.set64 SPN (so + j) (r₂.headD 0)).set64 CTL 136 (so + j + 1)).arr64 EREC)
        po.toNat pl.toNat = some lps := by rw [hEr3]; exact hlps
    obtain ⟨ys, hok3, ⟨M₄, hS₄, hK₄, hSt₄⟩, hres3, hys⟩ := ih k _ _ M₂ (j + 1) m' (by omega)
      (by omega) hS₃ hlps₃ (by rw [hsp3, UInt64.add_assoc]) (by rw [hsz3]; exact hso₂) hat hpt hanr hsa₃ hsp₃ hL
    -- the twin
    have hSt₄ : StackGrew _ m' := hSt₄
    have hrunT1 := AM.run_of_ok _ _ hok1
    rw [hres1] at hrunT1
    have hI : ∀ q : EIdx, instSpine coreWalkFuel (args.toList.take rP.toNat) (rP.toNat - 1) q =
        instSpine coreWalkFuel args.toList (rP - 1 : Word).toNat q := by
      intro q
      by_cases h0 : rP = 0
      · have : args.toList = [] := by
          have := hsa.size
          rw [h0] at hanr
          simp at hanr
          simpa [hanr] using this
        rw [this]; simp only [List.take_nil, instSpine]
      · have h0' : rP.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
        have hsub : (rP - 1 : Word).toNat = rP.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
          simp
        rw [hsub, List.take_of_length_le (by simp [hsa.size]; omega)]
    have hrunT2 := AM.run_of_ok _ _ hok2
    rw [hres2] at hrunT2
    have hrunR := AM.run_of_ok _ _ hok3
    rw [h1] at hrunR hres3
    have hrun := instSpinePins_cons_run lps (decI us) args.toList rP.toNat
      (decE (rdW (m.arr64 SPN) (pvo + j))) (pins.toList.drop (j.toNat + 1)) a _ _ _ _ _ _
      hrunT1 (by rw [hI]; exact hrunT2) hrunR
    rw [hdrop]
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨decE (r₂.headD 0) :: ys, hokF, ⟨M₄, ?_, hK₁.trans (hK₂.trans hK₄), ?_⟩, hresF.trans (by rw [hres3]; rfl), ?_⟩
    · rw [hstF]; rw [h1] at hS₄; exact hS₄
    · exact (hSt₁.toGrew.trans (hSt₂.toGrew.trans (hgrew.trans hSt₄)))
    · have e1 : pvc - j = (pvc - (j + 1)) + 1 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega),
          UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), h1]
        simp; omega
      have e2 : so + (j + 1) = so + j + 1 := by rw [UInt64.add_assoc]
      have hsjp1 : (so + j + 1).toNat = (so + j).toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      rw [e1]
      rw [e2] at hys
      have hsize' : (m'.arr64 SPN).size = (m.arr64 SPN).size := by
        rw [hSt₄.size, hsz3, hsz2]
      refine SpineR.cons_slot m' (so + j) (pvc - (j + 1)) (r₂.headD 0) ys hv32 ?_ hys ?_ (by rw [hsize']; exact hS.spn)
      · have := hSt₄.below (so + j) (by
          rw [hsp3, UInt64.lt_iff_toNat_lt, hsjp1]; omega)
        rw [this, hslot]
      · rw [hsize', UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega), hsoj]
        omega

/-- **`inst_spine_pins` refines `instSpinePins`.** Statement changes: `CoreAfterG` (the function leaves
its result slice on the stack: the top grows) in place of `CoreAfter`; both input slices below the
top; and the L code now raises the top after each store (see `instSpinePinsLoop`). -/
theorem instSpinePins_refines' (p : Prog) (hp : IotaProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hE : ErecKeptInst p) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb po pl us ao an rP pvo pvc : Word) (lps : List NIdx) (args pins : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps → SpineR s₀.mem ao an args →
    SpineR s₀.mem pvo pvc pins → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat →
    pvo.toNat + pvc.toNat ≤ (spTop s₀.mem).toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "inst_spine_pins" [po, pl, us, ao, an, rP, pvo, pvc]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀ ∧
      CoreAfterG dn s₀.mem s'.mem
        (AM.st (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀) vis fe MM eb ∧
      ∃ xs, AM.res (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ := by
  intro n s₀ a₀ dn vis fe MM eb po pl us ao an rP pvo pvc lps args pins hS hus hlps hsa hsp hat hpt
  cases n with
  | zero => exact invoke_zero_triple
  | succ n =>
  refine triple_post (instSpinePins_spec p hp.instSpinePins n s₀ po pl us ao an rP pvo pvc) fun r
    s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [ispTop] at hW
  obtain ⟨h136, hW⟩ := of_ite_none' hW
  obtain ⟨hg1, hW⟩ := of_ite_none hW
  obtain ⟨hg2, hW⟩ := of_ite_none hW
  cases hm : ispW p po pl us ao (ispLen an rP) rP pvo pvc (rdW (s₀.mem.arr64 CTL) 136) (n + 1) s₀.mem 0 with
  | none => rw [hm] at hW; cases hW
  | some m' =>
  rw [hm] at hW
  obtain ⟨hr, hmm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hspn := hS.spn
  have h64 : (s₀.mem.arr64 SPN).size < 2 ^ 64 := by omega
  have hsolt : (rdW (s₀.mem.arr64 CTL) 136).toNat ≤ (s₀.mem.arr64 SPN).size := by
    have : ¬ (s₀.mem.arr64 SPN).size < (rdW (s₀.mem.arr64 CTL) 136).toNat := by
      intro h
      apply hg1
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' h64]; exact h
    omega
  have hso : (rdW (s₀.mem.arr64 CTL) 136).toNat + pvc.toNat ≤ (s₀.mem.arr64 SPN).size := by
    have h2 : ¬ UInt64.ofNat (s₀.mem.arr64 SPN).size - rdW (s₀.mem.arr64 CTL) 136 < pvc := hg2
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' h64]; exact hsolt),
      UInt64.toNat_ofNat_of_lt' h64] at h2
    omega
  have hspt : spTop s₀.mem = rdW (s₀.mem.arr64 CTL) 136 + 0 := by
    rw [UInt64.add_zero]; rfl
  obtain ⟨hla, hlr⟩ := ispLen_le an rP
  obtain ⟨ys, hok, hca, hres, hys⟩ := ispW_ok p hp hc hw hE dn vis fe eb po pl us ao (ispLen an rP) rP
    pvo pvc (rdW (s₀.mem.arr64 CTL) 136) hus lps (args.toList.take (ispLen an rP).toNat).toArray pins
    (pvc.toNat - (0 : Word).toNat) (n + 1) s₀.mem a₀ MM 0
    m' rfl (by simp) hS hlps hspt hso
    (by rw [← show (spTop s₀.mem) = rdW (s₀.mem.arr64 CTL) 136 from rfl]; omega)
    (by rw [← show (spTop s₀.mem) = rdW (s₀.mem.arr64 CTL) 136 from rfl]; exact hpt) hlr
    (hsa.take _ hla) hsp hm
  rw [List.toList_toArray, ispLen_take an rP args.toList (by simp [hsa.size]),
    instSpinePins_take] at hok hca hres
  have hr1 : r.headD 0 = rdW (s₀.mem.arr64 CTL) 136 := by
    have := congrArg (fun l => l.headD 0) hr.symm; simpa using this
  have hr2 : r.tail.headD 0 = pvc := by
    have := congrArg (fun l => l.tail.headD 0) hr.symm; simpa using this
  refine ⟨hok, ?_, ys, hres, ?_⟩
  · simpa [← hmm] using hca
  · rw [hr1, hr2, ← hmm]
    simpa using hys

end L.Arena
