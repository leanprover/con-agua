import ConAgua.Arena.InferBodyBind
import ConAgua.Arena.IndSumSpec3

/-!
# The ∀ telescope: `infer_pis_leaf`, `infer_pis`, `infer_forall` (lane `defeq`)

`InferBodyBind.lean`'s λ telescope with the binder's sort level on the binder stack (`ws` level
words, the twin's `stk : Array LIdx` is `ws.map decI`) and the outward `imax` fold.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## `infer_pis_leaf`: the outward fold as a named block -/

/-- The outward loop of `inferPisLeafL` (Infer.lean), named for its spec. -/
def pisOutW : Stmt := lblk (mode, vis, d, t, k, fo, lo, ob, bt, v, n, r) {
  while n != 0 {
    n -= 1;
    v := call intern_imax(BSTK.u64[lo + n], v)
  }
}

/-- `inferPisLeafL`, with its outward loop spliced from `pisOutW`. -/
-- con-ron: none — `inferPisLeafL` itself (`rfl`), its loop a named block for the proof
def inferPisLeafL' : FunDecl := lfn (mode, vis, d, t, k, fo, lo) locals (ob, bt, v, n, r) {
  ob := call inst_list(t, fo, k, 0);
  bt := call infer(mode, vis, d + k, ob);
  v := call ensure_sort(mode, vis, d + k, bt);
  n := k;
  ⟪pisOutW⟫;
  r := call intern_sort(v);
  return r
}

theorem inferPisLeafL_eq : inferPisLeafL = inferPisLeafL' := rfl

/-- **The model of the outward `imax` fold** at L fuel `k`. -/
def pisOut (p : Prog) : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, lo, n, v =>
    if n ≠ 0 then
      match callW p k "intern_imax" [rdW (m.arr64 BSTK) (lo + (n - 1)), v] m with
      | none => none
      | some (r₁, m₁) => pisOut p k m₁ lo (n - 1) (r₁.headD 0)
    else some (v, m)

theorem pisOutW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n pisOutW
    ⦃fun r s' => r = .normal ∧
      pisOut p n s₀.mem (s₀.loc 6) (s₀.loc 10) (s₀.loc 9) = some (s'.loc 9, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := pisOutW) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, ih,
      callW_spec p n "intern_imax"] <;>
    simp_all [pisOut, Cmp.eval, LocEq, BinOp.eval, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil]

/-- **The model of `infer_pis_leaf`.** -/
def pisLeafK (p : Prog) (n : Nat) (m : Mem) (mode vis d t k fo lo : Word) : Option (Word × Mem) :=
  match callW p n "inst_list" [t, fo, k, 0] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
    | none => none
    | some (r₂, m₂) =>
      match callW p n "ensure_sort" [mode, vis, d + k, r₂.headD 0] m₂ with
      | none => none
      | some (r₃, m₃) =>
        match pisOut p (n + 1) m₃ lo k (r₃.headD 0) with
        | none => none
        | some (v, m₄) => call1W p n "intern_sort" [v] m₄

theorem inferPisLeaf_spec (p : Prog) (hq : BindProg p) (n : Nat) (s₀ : St)
    (mode vis d t k fo lo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_pis_leaf" [mode, vis, d, t, k, fo, lo]
    ⦃fun r s' => LocEq s' s₀ ∧ pisLeafK p n s₀.mem mode vis d t k fo lo = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.pisLeaf, inferPisLeafL_eq]
  simp only [callFn, inferPisLeafL']
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (pisOutW_spec p (n + 1) s), callW_spec p n "inst_list",
      callW_spec p n "infer", callW_spec p n "ensure_sort", callW_spec p n "intern_sort"] <;>
  simp_all [pisLeafK, call1W, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-! ## `infer_pis_leaf` refines `inferPisLeaf` -/

theorem BKept.of_imax {m m' : Mem} {u v r : Word} (h : iminternW m u v = some (r, m')) : BKept m m' := by
  have hI₂ := h; rw [iiminternW_eq] at hI₂
  exact BKept.of_frame (internM_frame _ iimaxSch_wf _ _ _ _ _ _ _ _ hI₂)
    (by simp [imaxSch, IREC, ISLOT, BSTK]) (by simp [imaxSch])

/-- **The outward fold refines `inferPisOut`**, and keeps the binder stack. -/
theorem pisOut_ref (p : Prog) (hb : InferBodyProg p) (hcap : BStkCap) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (eb lo K : Word) (ws : Array Word)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) :
    ∀ k (m : Mem) (a : AState) (M : ModeMaps) (n v : Word),
      CoreS dn m a vis fe M eb → HW v → BStkR m lo K ws → n.toNat ≤ K.toNat →
      lo.toNat + K.toNat ≤ (bTop m).toNat →
      ∀ w mF, pisOut p k m lo n v = some (w, mF) →
      CoreRef (inferPisOut (ws.map decI) n.toNat (decI v)) a decLv dn m vis fe M eb [w] mF ∧
        BKept m mF := by
  intro k
  induction k with
  | zero => intro m a M n v _ _ _ _ _ w mF h; simp [pisOut] at h
  | succ k ih =>
    intro m a M n v hS hv hB hnK htop w mF h
    by_cases hn : n = 0
    · subst hn
      simp only [pisOut, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hrun : (inferPisOut (ws.map decI) (0 : Word).toNat (decI v)).run a = .ok (decI v, a) := by
        rw [inferPisOut]; rfl
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
      exact ⟨⟨hok, by rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, by rw [hres]; rfl,
        hv⟩, BKept.refl _⟩
    simp only [pisOut, hn, ne_eq, not_false_eq_true, ↓reduceIte] at h
    have hn1 := sub1_toNat hn
    have hn0' : n.toNat ≠ 0 := fun h' => hn (UInt64.toNat_inj.mp (by simpa using h'))
    have hjK : (n - 1).toNat < ws.size := by rw [hB.size, hn1]; omega
    have hwsj : ws[(n - 1).toNat] = rdW (m.arr64 BSTK) (lo + (n - 1)) := by
      rw [hB.get _ hjK]; simp
    cases h1 : callW p k "intern_imax" [rdW (m.arr64 BSTK) (lo + (n - 1)), v] m with
    | none => rw [h1] at h; cases h
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [h1] at h; dsimp only at h
    have hwj : HW (rdW (m.arr64 BSTK) (lo + (n - 1))) := hwsj ▸ hws _ hjK
    obtain ⟨s₁, hs₁, -, him⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internImax_spec p hb.imf hb.imp hb.imi k _ _ v) h1
    rw [hs₁] at him
    have h₁ := internImax_core hS _ _ hwj hv r₁ him
    have hK₁ := BKept.of_imax him
    have hsz := hcap _ _ _ _ _ _ _ hS
    have hB₁ : BStkR m₁ lo K ws := hB.keep hK₁ htop hsz
    have htop₁ : lo.toNat + K.toNat ≤ (bTop m₁).toNat := by rw [hK₁.1]; exact htop
    have hT : inferPisOut (ws.map decI) n.toNat (decI v) =
        (internLNode (.imax (decI (rdW (m.arr64 BSTK) (lo + (n - 1)))) (decI v)) >>= fun v2 =>
          inferPisOut (ws.map decI) (n - 1).toNat v2) := by
      rw [inferPisOut]
      simp only [hn0', ↓reduceIte, hn1]
      rw [show (ws.map decI)[n.toNat - 1]! = decI (rdW (m.arr64 BSTK) (lo + (n - 1))) by
        rw [← hn1, getElem!_pos (ws.map decI) _ (by simpa using hjK), Array.getElem_map, hwsj]]
    refine ⟨?_, hK₁.trans ?_⟩
    · rw [hT]
      refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
      exact (ih m₁ _ M₁ (n - 1) (r₁.headD 0) hS₁ h₁.2.2.2 hB₁ (by omega) htop₁ w mF h).1
    · obtain ⟨M₁, hS₁, -⟩ := h₁.2.1
      exact (ih m₁ _ M₁ (n - 1) (r₁.headD 0) hS₁ h₁.2.2.2 hB₁ (by omega) htop₁ w mF h).2

/-- **`infer_pis_leaf` refines `inferPisLeaf`** at the knot. -/
@[refines ConRon.Arena.inferPisLeaf ConRon.Arena.inferPisOut]
theorem inferPisLeaf_refines (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hbc : BStkCallees p) (hcap : BStkCap) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (hftop : fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat) (hB : BStkR s₀.mem lo k ws)
    (hbtop : lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "infer_pis_leaf" [mode, vis, d, t, k, fo, lo]
      (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI))
      decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferPisLeaf_spec p hq n s₀ mode vis d t k fo lo)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold pisLeafK at hW
  cases h1 : callW p n "inst_list" [t, fo, k, 0] s.mem with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW; dsimp only at hW
  cases h2 : callW p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW; dsimp only at hW
  cases h3 : callW p n "ensure_sort" [mode, vis, d + k, r₂.headD 0] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW; dsimp only at hW
  cases h4 : pisOut p (n + 1) m₃ lo k (r₃.headD 0) with
  | none => rw [h4] at hW; cases hW
  | some q =>
  obtain ⟨v, m₄⟩ := q
  rw [h4] at hW; dsimp only at hW
  have hsz := hcap _ _ _ _ _ _ _ hS
  have h₁ := CoreSpec.of_callW (hil n s a₀ dn vis fe M eb t fo k 0 fvs hS ht hf hftop) h1
  have hK₁ := hbc n "inst_list" _ _ _ _ (by simp) h1
  have hdk' : (d + k).toNat = d.toNat + k.toNat := addW _ _ hdk
  have h0 : (0 : Word).toNat = 0 := rfl
  have hT : inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI) =
      (instantiateListFast coreWalkFuel (decE t) fvs (0 : Word).toNat >>= fun ob =>
        (coreKnot (decMode mode) fe id F).infer (d + k).toNat ob >>= fun bt =>
        ensureSort (coreKnot (decMode mode) fe id F) fe (d + k).toNat bt >>= fun v =>
        inferPisOut (ws.map decI) k.toNat v >>= fun iv => internSortE iv) := by
    rw [hdk', h0, inferPisLeaf, Array.size_map, hB.size]
  rw [hT]
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode (d + k) (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) h2
  have hK₂ := hbc n "infer" _ _ _ _ (by simp) h2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_callW (ensureSortSpec_of_knot p hp n hk F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂
    eb mode (d + k) (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.2.2.2) h3
  have hK₃ := hbc n "ensure_sort" _ _ _ _ (by simp) h3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have hB₁ := hB.keep hK₁ hbtop hsz
  have hB₂ := hB₁.keep hK₂ (by rw [hK₁.1]; exact hbtop) (by rw [hK₁.2.1]; exact hsz)
  have hB₃ := hB₂.keep hK₃ (by rw [hK₂.1, hK₁.1]; exact hbtop)
    (by rw [hK₂.2.1, hK₁.2.1]; exact hsz)
  have h₄ := (pisOut_ref p hb hcap dn vis fe eb lo k ws hws (n + 1) m₃ _ M₃ k (r₃.headD 0) hS₃
    h₃.2.2.2 hB₃ (Nat.le_refl _) (by rw [hK₃.1, hK₂.1, hK₁.1]; exact hbtop) _ _ h4).1
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  have hso := of_call1W (X := fun m w m' => sointernW m v = some (w, m'))
    (fun s₀ => internSort_spec p hb.sof hb.sop hb.soi n s₀ v) hW
  exact internSort_core hS₄ v h₄.2.2.2 r hso

end L.Arena
