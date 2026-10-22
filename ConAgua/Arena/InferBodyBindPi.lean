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

/-! ## `infer_pis`: the peel loop as a named block -/

/-- The peel loop of `inferPisL` (Infer.lean), named for its spec. -/
def pisW : Stmt := lblk (mode, vis, d, peel, t, k, fo, lo, s, i, ty, body, tyo, tty, w, u, fv, r) {
  while peel != 0 && t >> 28 == 6 {
    s := (t >> 27) & 1;
    i := t & 134217727;
    if s != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[30 + s] <= i { abort };
    ty := FAREC.u64[i * 4 + s * 2];
    body := FAREC.u64[i * 4 + s * 2 + 1];
    tyo := call inst_list(ty, fo, k, 0);
    tty := call infer(mode, vis, d + k, tyo);
    w := call whnf(mode, vis, d + k, tty);
    if w >> 28 != 2 { abort };
    s := (w >> 27) & 1;
    i := w & 134217727;
    if s != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[16 + s] <= i { abort };
    u := SOREC.u64[i * 2 + s];
    fv := call intern_fvar(d + k, tyo);
    if len(SPN.u64) <= fo + k { abort };
    if len(BSTK.u64) <= lo + k { abort };
    SPN.u64[fo + k] := fv;
    BSTK.u64[lo + k] := u;
    k += 1;
    CTL.u64[136] := fo + k;
    CTL.u64[137] := lo + k;
    peel -= 1;
    t := body
  }
}

/-- `inferPisL`, with its loop spliced from `pisW`. -/
-- con-ron: none — `inferPisL` itself (`rfl`), its loop a named block for the proof
def inferPisL' : FunDecl :=
    lfn (mode, vis, d, peel, t, k, fo, lo) locals (s, i, ty, body, tyo, tty, w, u, fv, r) {
  ⟪pisW⟫;
  r := call infer_pis_leaf(mode, vis, d, t, k, fo, lo);
  return r
}

theorem inferPisL_eq : inferPisL = inferPisL' := rfl

/-- **The model of the ∀ peel loop** at L fuel `n`: the exit's `(t, k, memory)`. -/
def pisLoop (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, mode, vis, d, peel, t, k, fo, lo =>
    if peel ≠ 0 ∧ t >>> 28 = 6 then
      if tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if rdW (m.arr64 CTL) (30 + tierW t) ≤ idxW t then none
      else
        match callW p n "inst_list" [rdW (m.arr64 FAREC) (idxW t * 4 + tierW t * 2), fo, k, 0] m with
        | none => none
        | some (r₁, m₁) =>
          match callW p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
          | none => none
          | some (r₂, m₂) =>
            match callW p n "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with
            | none => none
            | some (r₃, m₃) =>
              if r₃.headD 0 >>> 28 ≠ 2 then none
              else if tierW (r₃.headD 0) ≠ 0 ∧ rdW (m₃.arr64 CTL) 1 = 0 then none
              else if rdW (m₃.arr64 CTL) (16 + tierW (r₃.headD 0)) ≤ idxW (r₃.headD 0) then none
              else
                match callW p n "intern_fvar" [d + k, r₁.headD 0] m₃ with
                | none => none
                | some (r₄, m₄) =>
                  if tPushOK m₄ fo lo k then
                    pisLoop p n (tPush m₄ fo lo k (r₄.headD 0)
                        (rdW (m₃.arr64 SOREC) (idxW (r₃.headD 0) * 2 + tierW (r₃.headD 0)))) mode vis d
                      (peel - 1) (rdW (m.arr64 FAREC) (idxW t * 4 + tierW t * 2 + 1)) (k + 1) fo lo
                  else none
    else some (t, k, m)

theorem pisW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n pisW
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
      pisLoop p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
        (s₀.loc 6) (s₀.loc 7) = some (s'.loc 4, s'.loc 5, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := pisW) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec, ih,
      callW_spec p n "inst_list", callW_spec p n "infer", callW_spec p n "whnf",
      callW_spec p n "intern_fvar"] <;>
    simp_all [pisLoop, tPush, tPushOK, Cmp.eval, LocEq, BinOp.eval, tierW, idxW, St.setLocs_cons,
      St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, size_set64, w_lt_false, Mem.arr64_set64_ne]

/-- **The model of `infer_pis`.** -/
def pisFull (p : Prog) (n k : Nat) (m : Mem) (mode vis d peel t kk fo lo : Word) : Option (Word × Mem) :=
  match pisLoop p k m mode vis d peel t kk fo lo with
  | none => none
  | some (t', k', m') => call1W p n "infer_pis_leaf" [mode, vis, d, t', k', fo, lo] m'

theorem inferPis_spec (p : Prog) (hq : BindProg p) (n : Nat) (s₀ : St)
    (mode vis d peel t k fo lo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_pis" [mode, vis, d, peel, t, k, fo, lo]
    ⦃fun r s' => LocEq s' s₀ ∧
      pisFull p n (n + 1) s₀.mem mode vis d peel t k fo lo = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.pis, inferPisL_eq]
  simp only [callFn, inferPisL']
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (pisW_spec p (n + 1) s), callW_spec p n "infer_pis_leaf"] <;>
  simp_all [pisFull, call1W, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-- `infer_pis_leaf` at every L fuel up to `n + 1`. -/
theorem inferPisLeaf_any (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hbc : BStkCallees p) (hcap : BStkCap) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs →
    fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat → BStkR s₀.mem lo k ws →
    lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
    d.toNat + k.toNat < 2 ^ 64 →
    CoreSpec p n "infer_pis_leaf" [mode, vis, d, t, k, fo, lo]
      (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI))
      decH s₀ a₀ dn vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zero p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, t, k, fo, lo, fvs, ws, hs, ht, hf,
      hftop, hB, hbtop, hws, hdk =>
      inferPisLeaf_refines p hp hq hb hil hbc hcap n (hk.mono (by omega)) F (by omega) (by omega)
        s₀ a₀ dn vis fe M eb mode d t k fo lo fvs ws hs ht hf hftop hB hbtop hws hdk

/-- **The ∀ peel loop with its leaf refines `inferPis`** by induction on the loop fuel. -/
theorem pisFull_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hbc : BStkCallees p) (hcap : BStkCap)
    (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hFN : N ≤ F) (hN : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo lo eb : Word)
    (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) :
    ∀ j, j ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (peel t k : Word) (fvs : Array EIdx)
      (ws : Array Word),
      CoreS dn m a vis fe M eb → HW t → SpineR m fo k fvs → spTop m = fo + k →
      BStkR m lo k ws → bTop m = lo + k → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
      d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      (∀ j, j < fo → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      ∀ w mF, pisFull p N j m mode vis d peel t k fo lo = some (w, mF) →
      TelPost dn vis fe M eb m₀ fo a
        (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
          (ws.map decI)) w mF := by
  intro j
  induction j with
  | zero => intro _ m a M peel t k fvs ws _ _ _ _ _ _ _ _ _ _ w mF hF; simp [pisFull, pisLoop] at hF
  | succ j ih =>
    intro hjN m a M peel t k fvs ws hS ht hf htop hB hbt hws hdk hb0 hsz w mF hF
    have hspn := hS.spn
    have hcp := hcap _ _ _ _ _ _ _ hS
    have hfb := hf.bound
    have hBb := hB.bound
    have haddf : (fo + k).toNat = fo.toNat + k.toNat := addW _ _ (by omega)
    have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
    have haddd : (d + k).toNat = d.toNat + k.toNat := addW _ _ (by omega)
    have hftop : fo.toNat + k.toNat ≤ (spTop m).toNat := by rw [htop, haddf]; exact Nat.le_refl _
    have hbtop : lo.toNat + k.toNat ≤ (bTop m).toNat := by rw [hbt, haddl]; exact Nat.le_refl _
    -- the exit: the leaf
    have hexit : ∀ (hT : (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t)
          k.toNat fvs (ws.map decI)).run a = (inferPisLeaf (coreKnot (decMode mode) fe id F) fe
          d.toNat (decE t) k.toNat fvs (ws.map decI)).run a),
        call1W p N "infer_pis_leaf" [mode, vis, d, t, k, fo, lo] m = some (w, mF) →
        TelPost dn vis fe M eb m₀ fo a (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat
          peel.toNat (decE t) k.toNat fvs (ws.map decI)) w mF := by
      intro hT hc
      have hl := CoreSpec.of_call1W (r := [w]) (s₀ := ⟨m, Locals.init []⟩)
        (inferPisLeaf_any p hp hq hb hil hbc hcap N hk F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb
          mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩ ht hf hftop hB hbtop hws (by omega))
        (fun r r' h => by simp only [decH, h]) hc
      obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := hl
      refine ⟨_, _, hT.trans (AM.run_of_ok _ _ hok), hres, hrw, M', hS', hK', fun i hi => ?_,
        hSt'.2.1.trans hsz⟩
      have hi' : i < spTop m := by
        rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
      exact (hSt'.2.2 i hi').trans (hb0 i hi)
    by_cases hc : peel ≠ 0 ∧ t >>> 28 = 6
    · obtain ⟨hp0, ht6⟩ := hc
      have hc1 : ¬ (tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun g => by
        simp only [pisFull, pisLoop, hp0, ht6, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      have hc2 : ¬ rdW (m.arr64 CTL) (30 + tierW t) ≤ idxW t := fun g => by
        simp only [pisFull, pisLoop, hp0, ht6, hc1, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      have hv : viewOK m t 30 := ⟨hc1, UInt64.not_le.mp hc2⟩
      obtain ⟨-, hty, hbody⟩ := view_forall m a hS.arena.1 t ht hv ht6
      have hvb := viewBind_forall m a hS.arena.1 t ht hv ht6
      cases h1 : callW p j "inst_list" [rdW (m.arr64 FAREC) (idxW t * 4 + tierW t * 2), fo, k, 0] m with
      | none => simp only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      cases h2 : callW p j "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
      | none => simp only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      | some q =>
      obtain ⟨r₂, m₂⟩ := q
      cases h3 : callW p j "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with
      | none => simp only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, h2, h3, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      | some q =>
      obtain ⟨r₃, m₃⟩ := q
      have g1 : r₃.headD 0 >>> 28 = 2 := Classical.byContradiction fun g => by
        simp only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, h2, h3, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      have gs1 : ¬ (tierW (r₃.headD 0) ≠ 0 ∧ rdW (m₃.arr64 CTL) 1 = 0) := fun g => by
        simp only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, h2, h3, g1, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      have gs2 : ¬ rdW (m₃.arr64 CTL) (16 + tierW (r₃.headD 0)) ≤ idxW (r₃.headD 0) := fun g => by
        simp only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, h2, h3, g1, gs1, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      cases h4 : callW p j "intern_fvar" [d + k, r₁.headD 0] m₃ with
      | none => simp only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, h2, h3, g1, gs1, gs2, h4, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      | some q =>
      obtain ⟨r₄, m₄⟩ := q
      have g2 : tPushOK m₄ fo lo k := Classical.byContradiction fun g => by
        simp only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, h2, h3, g1, gs1, gs2, h4, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      have hF' : pisFull p N j (tPush m₄ fo lo k (r₄.headD 0)
          (rdW (m₃.arr64 SOREC) (idxW (r₃.headD 0) * 2 + tierW (r₃.headD 0)))) mode vis d (peel - 1)
          (rdW (m.arr64 FAREC) (idxW t * 4 + tierW t * 2 + 1)) (k + 1) fo lo = some (w, mF) := by
        simpa only [pisFull, pisLoop, hp0, ht6, hc1, hc2, h1, h2, h3, g1, gs1, gs2, h4, g2, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] using hF
      have h0 : (0 : Word).toNat = 0 := rfl
      -- the domain opened
      have hinst := hil j ⟨m, Locals.init []⟩ a dn vis fe M eb _ fo k 0 fvs hS hty hf hftop
      obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW hinst h1
      rw [h0] at hok1 hres1 hS₁
      have hB₁ := hbc j "inst_list" _ _ _ _ (by simp) h1
      -- its type, a sort
      have hi := CoreSpec.of_callW ((hk j (by omega)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
        mode (d + k) (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) h2
      obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := hi
      have hB₂ := hbc j "infer" _ _ _ _ (by simp) h2
      have hw := CoreSpec.of_callW ((hk j (by omega)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb
        mode (d + k) (r₂.headD 0) (by omega) (by omega) ⟨hS₂, hmode, heb⟩ hrw2) h3
      obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := hw
      have hB₃ := hbc j "whnf" _ _ _ _ (by simp) h3
      -- the binder's free variable
      obtain ⟨s₄, hs₄, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
        (internFVar_spec p hb.fvf hb.fvp hb.fvi j _ (d + k) (r₁.headD 0)) h4
      rw [hs₄] at hfv
      have h₄ := internFVar_core hS₃ (d + k) (r₁.headD 0) hrw1 r₄ hfv
      obtain ⟨hok4, ⟨M₄, hS₄, hK₄, hSt₄⟩, hres4, hrw4⟩ := h₄
      have hB₄ : BKept m₃ m₄ := by
        have hI₂ := hfv; rw [fvinternW_eq] at hI₂
        exact BKept.of_frame (internM_frame _ fvarSch_wf _ _ _ _ _ _ _ _ hI₂)
          (by simp [fvarSch, FVREC, FVSLOT, BSTK]) (by simp [fvarSch])
      -- the stacks kept across the four calls
      have hSt14 := hSt₁.trans (hSt₂.trans (hSt₃.trans hSt₄))
      have hBK := hB₁.trans (hB₂.trans (hB₃.trans hB₄))
      have hf₄ : SpineR m₄ fo k fvs := hf.keep hSt14.2.1 hSt14.2.2 hftop hspn
      have hB4 : BStkR m₄ lo k ws := hB.keep hBK hbtop hcp
      have hb₄ : ∀ i, i < fo → spW m₄ i = spW m₀ i := fun i hi => by
        have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt14.2.2 i hi').trans (hb0 i hi)
      obtain ⟨hS', hf', htop', hB', hbt', hb', hsz', -⟩ := tPush_step (m₀ := m₀) hS₄
        (by rw [hBK.2.1]; exact hcp) hf₄ hB4 hb₄ (hSt14.2.1.trans hsz) g2 hrw4
      obtain ⟨hvs, hu⟩ := L.Ind.view_sort_f m₃ _ hS₃.arena.1 (r₃.headD 0) hrw3 ⟨gs1, UInt64.not_le.mp gs2⟩ g1
      have hws' : ∀ (i : Nat) (h : i < (ws.push (rdW (m₃.arr64 SOREC) (idxW (r₃.headD 0) * 2 +
          tierW (r₃.headD 0)))).size), HW (ws.push (rdW (m₃.arr64 SOREC) (idxW (r₃.headD 0) * 2 +
          tierW (r₃.headD 0))))[i] := by
        intro i hi
        rw [Array.getElem_push]
        split
        · exact hws i _
        · exact hu
      have hpeel1 : (peel - 1).toNat = peel.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le]; · rfl
        rw [UInt64.le_iff_toNat_le]; simp
        have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega
      have hk1 : (k + 1).toNat = k.toNat + 1 := addW _ _ (by simp; omega)
      have hp0' : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h'))
      obtain ⟨x, a', hrun', hx, hrw, M', hS'', hK, hb'', hsz''⟩ := ih (by omega) _ _ M₄ (peel - 1)
        _ (k + 1) _ _ hS' hbody hf' htop' hB' hbt' hws' (by rw [hk1, hpeel1]; omega) hb' hsz' w mF hF'
      refine ⟨x, a', ?_, hx, hrw, M', hS'', hK₁.trans (hK₂.trans (hK₃.trans (hK₄.trans hK))), hb'', hsz''⟩
      rw [← hrun']
      obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 := ⟨peel.toNat - 1, by omega⟩
      have hlam : ((decE t).tag != ETag.forallE) = false := by
        rw [bne_eq_false_iff_eq, ← beq_iff_eq, tag_fa_beq t ht]; simp [ht6]
      have hsort : ((decE (r₃.headD 0)).tag == ETag.sort) = true := tag_sort_beq _ hrw3 g1
      rw [hp', inferPis]
      simp only [hlam, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, viewBind_run', hvb,
        except_ok_bind]
      rw [AM.run_of_ok _ _ hok1, except_ok_bind, hres1]
      simp only [decH] at hres2 hres3 hres4 ⊢
      rw [← haddd, AM.run_of_ok _ _ hok2, except_ok_bind, hres2, AM.run_of_ok _ _ hok3, except_ok_bind,
        hres3]
      rw [hsort, if_pos rfl, StateT.run_bind,
        L.Ind.viewSort_run (L.Ind.viewSort_of_view _ _ _ ((decE_tag_eq _ hrw3 2 (by decide)).mpr g1) hvs),
        except_ok_bind]
      simp only [internFVarE, StateT.run_bind]
      rw [AM.run_of_ok _ _ hok4, except_ok_bind, hres4, hk1, hpeel1, hp', Nat.add_sub_cancel,
        Array.map_push]
    · -- the exit
      have hL : pisLoop p (j + 1) m mode vis d peel t k fo lo = some (t, k, m) := by
        simp only [pisLoop, hc, ↓reduceIte]
      simp only [pisFull, hL] at hF
      refine hexit ?_ hF
      by_cases hp0 : peel = 0
      · subst hp0; rfl
      · have ht6 : ¬ t >>> 28 = 6 := fun h => hc ⟨hp0, h⟩
        obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
          ⟨peel.toNat - 1, by
            have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
        have hlam : ((decE t).tag != ETag.forallE) = true := by
          rw [bne_iff_ne, ne_eq, ← beq_iff_eq, tag_fa_beq t ht]; simp [ht6]
        rw [hp', inferPis]
        simp only [hlam, ↓reduceIte]

/-- **`infer_pis` refines `inferPis`** from a telescope state (`fvs` at the spine top, `stk` at
the binder top), up to the tops it leaves raised (`TelPost`). -/
@[refines ConRon.Arena.inferPis]
theorem inferPis_tel (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hbc : BStkCallees p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (htop : spTop s₀.mem = fo + k) (hB : BStkR s₀.mem lo k ws) (hbt : bTop s₀.mem = lo + k)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64)
    (hb0 : ∀ j, j < fo → spW s₀.mem j = spW m₀ j) (hsz : (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_pis" [mode, vis, d, peel, t, k, fo, lo]
    ⦃fun r s' => LocEq s' s₀ ∧ TelPost dn vis fe M eb m₀ fo a₀
      (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decI)) (r.headD 0) s'.mem; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferPis_spec p hq n s₀ mode vis d peel t k fo lo)
  subst hs0
  exact ⟨hloc, pisFull_ref p hp hq hb hil hbc hcap n hk F hF hn dn vis fe mode d fo lo eb hs.mode4
    hs.eb_mode m₀ (n + 1) (Nat.le_refl _) s.mem a₀ M peel t k fvs ws hs.rel ht hf htop hB hbt hws hdk
    hb0 hsz _ _ hW⟩


end L.Arena
