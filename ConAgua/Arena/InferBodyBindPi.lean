import ConAgua.Arena.InferBodyBind
import ConAgua.Arena.IndSumSpec.DecCVpGrow
import ConAgua.Arena.InferBodyBindPiModels

/-!
# The ∀ telescope: `infer_pis_leaf`, `infer_pis`, `infer_forall` (lane `defeq`)

`InferBodyBind.lean`'s λ telescope with the binder's sort level on the binder stack (`ws` level
words, the twin's `stk : Array LIdx` is `ws.map decI`) and the outward `imax` fold.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `infer_pis_leaf` refines `inferPisLeaf` -/

theorem BKept.of_imax {m m' : Mem} {u v r : Word} (h : iminternW m u v = some (r, m')) : BKept m m' := by
  exact BKept.of_frame ((iminternW_frame (hI := h)))
    (by simp [tier1, IREC, ISLOT, IHP, BSTK]) (by simp)

/-- **The outward fold refines `inferPisOut`, both outcomes** (`intern_imax` lifted), with the
result level's denotation. -/
theorem pisOut_ref (p : Prog) (hb : InferBodyProg p) (hcap : BStkCap) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (eb lo K : Word) (ws : Array Word)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) {G : Prop} :
    ∀ k (m : Mem) (a : AState) (M : ModeMaps) (n v : Word),
      CoreS dn m a vis fe M eb → HW v → (∃ l, denoteL a.store.ls (decI v) = some l) →
      (∀ (i : Nat) (h : i < ws.size), lvNodeW m ws[i] ≠ []) →
      BStkR m lo K ws → n.toNat ≤ K.toNat →
      lo.toNat + K.toNat ≤ (bTop m).toNat →
      RefE G (iplE.loop1 p k m lo v n) (inferPisOut (ws.map decI) n.toNat (decI v)) a
        (fun w y a' => CorePost decLv dn m vis fe M eb ResH ([w.1], w.2) y a' ∧
          ∃ l, denoteL a'.store.ls y = some l) := by
  intro k
  induction k with
  | zero => intro m a M n v _ _ _ _ _ _ _; rw [iplE.loop1.eq_1]; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro m a M n v hS hv hdv hwl hB hnK htop
    rw [iplE.loop1.eq_2]
    by_cases hn : n = 0
    · subst hn
      rw [ite_eq_right (by simp)]
      exact RefE.ret (by rw [inferPisOut]; rfl) ⟨CorePost.ret hS rfl hv, hdv⟩
    rw [ite_eq_left hn]
    have hn1 := sub1_toNat hn
    have hn0' : n.toNat ≠ 0 := fun h' => hn (UInt64.toNat_inj.mp (by simpa using h'))
    have hjK : (n - 1).toNat < ws.size := by rw [hB.size, hn1]; omega
    have hwsj : ws[(n - 1).toNat] = rdW (m.arr64 BSTK) (lo + (n - 1)) := by
      rw [hB.get _ hjK]; simp
    have hwj : HW (rdW (m.arr64 BSTK) (lo + (n - 1))) := hwsj ▸ hws _ hjK
    have hdu : ∃ l, denoteL a.store.ls (decI (rdW (m.arr64 BSTK) (lo + (n - 1)))) = some l := by
      obtain ⟨vv, hvv⟩ := L.Ind.lview_of_lvNodeW hS.arena.1 hwj (hwsj ▸ hwl _ hjK)
      exact hS.den.lvlAll _ (by show (a.store.lss.ls.view _).isSome = true; rw [hvv]; rfl)
    have hT : inferPisOut (ws.map decI) n.toNat (decI v) =
        (internLNode (.imax (decI (rdW (m.arr64 BSTK) (lo + (n - 1)))) (decI v)) >>= fun v2 =>
          inferPisOut (ws.map decI) (n - 1).toNat v2) := by
      rw [inferPisOut]
      simp only [hn0', ↓reduceIte, hn1]
      rw [show (ws.map decI)[n.toNat - 1]! = decI (rdW (m.arr64 BSTK) (lo + (n - 1))) by
        rw [← hn1, getElem!_pos (ws.map decI) _ (by simpa using hjK), Array.getElem_map, hwsj]]
    rw [hT]
    rcases h1 : callW p k "intern_imax" [rdW (m.arr64 BSTK) (lo + (n - 1)), v] m with _ | ⟨r₁, m₁⟩
    · rw [liftE_none, iplE.k_intern_imax.eq_1]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, iplE.k_intern_imax.eq_2]
    obtain ⟨s₁, hs₁, -, him⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internImax_spec p hb.imf hb.imp hb.imi k _ _ v) h1
    rw [hs₁] at him
    have h₁ := internImax_core hS _ _ hwj hv r₁ him hdu hdv
    have hdv₁ : ∃ l, denoteL (AM.st (internLNode (.imax (decI (rdW (m.arr64 BSTK) (lo + (n - 1))))
        (decI v))) a).store.ls (decI (r₁.headD 0)) = some l := by
      have hd := internLNode_res_den hS
        (fun c hc => by
          simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc
          rcases hc with rfl | rfl
          · exact hdu
          · exact hdv)
        (fun n hn => by simp [LNodeView.nchildren] at hn) h₁.1
      rw [h₁.2.2.1] at hd; exact hd
    have hK₁ := BKept.of_imax him
    have hsz := hcap _ _ _ _ _ _ _ hS
    have hB₁ : BStkR m₁ lo K ws := hB.keep hK₁ htop hsz
    have hwl₁ : ∀ (i : Nat) (h : i < ws.size), lvNodeW m₁ ws[i] ≠ [] := by
      obtain ⟨_, _, _, hT₁⟩ := h₁.2.1
      exact fun i hi => lvNodeW_mono hT₁.pool.lvl (hws i hi) (hwl i hi)
    have htop₁ : lo.toNat + K.toNat ≤ (bTop m₁).toNat := by rw [hK₁.1]; exact htop
    obtain ⟨M₁, hS₁, hK₁', hSt₁⟩ := h₁.2.1
    refine RefE.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1]) ?_
    exact (ih m₁ _ M₁ (n - 1) (r₁.headD 0) hS₁ h₁.2.2.2 hdv₁ hwl₁ hB₁ (by omega) htop₁).mono
      fun _ _ _ h => ⟨⟨CoreAfter.comp hK₁' hSt₁ h.1.after, h.1.res, h.1.valid⟩, h.2⟩

/-- **`infer_pis_leaf` refines `inferPisLeaf`, both outcomes**, at the knot: the residual
codomain's type (the `infer` slot at `d + k`), `ensure_sort`'s; the opening, the outward fold and the
sort claim nothing. -/
theorem ipl_ref (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (hftop : fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat) (hB : BStkR s₀.mem lo k ws)
    (hbtop : lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i])
    (hwl : ∀ (i : Nat) (h : i < ws.size), lvNodeW s₀.mem ws[i] ≠ []) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (InferG p n) (iplE p (n + 1) s₀.mem mode vis d t k fo lo)
      (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hsz := hcap _ _ _ _ _ _ _ hS
  have hdk' : (d + k).toNat = d.toNat + k.toNat := addW _ _ hdk
  have h0 : (0 : Word).toNat = 0 := rfl
  have hT : inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI) =
      (instantiateListFast coreWalkFuel (decE t) fvs (0 : Word).toNat >>= fun ob =>
        (coreKnot (decMode mode) fe id F).infer (d + k).toNat ob >>= fun bt =>
        ensureSort (coreKnot (decMode mode) fe id F) fe (d + k).toNat bt >>= fun v =>
        inferPisOut (ws.map decI) k.toNat v >>= fun iv => internSortE iv) := by
    rw [hdk', h0, inferPisLeaf, Array.size_map, hB.size]
  rw [hT]
  simp only [iplE]
  rcases h1 : callW p n "inst_list" [t, fo, k, 0] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [iplE.k_inst_list]
  have h₁ := CoreSpec.of_callW (hil n s₀ a₀ dn vis fe M eb t fo k 0 fvs hS ht hf hftop) h1
  have hK₁ := h₁.2.1.bkept
  obtain ⟨_, _, _, hT₁⟩ := h₁.2.1
  refine RefE.bind_core (w := id) h₁ (fun M₁ hS₁ _ => ?_)
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  rcases h2 : callE p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).infer F _ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0) hF hn hs₁
        h₁.2.2.2) h2
  have h₂ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode (d + k) (r₁.headD 0) hF hn hs₁ h₁.2.2.2) (callW_of_callE h2)
  have hK₂ := h₂.2.1.bkept
  obtain ⟨_, _, _, hT₂⟩ := h₂.2.1
  refine RefE.bind_core (w := id) h₂ (fun M₂ hS₂ _ => ?_)
  simp only [iplE.k_infer]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  rcases h3 : callE p n "ensure_sort" [mode, vis, d + k, r₂.headD 0] m₂ with e3 | ⟨r₃, m₃⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
      (ensureSortSpecE_of_knot p hp n hk hG.knot F _ _ dn vis fe M₂ eb mode (d + k) (r₂.headD 0) hF hn
        hs₂ h₂.2.2.2) h3
  have h₃ := CoreSpec.of_callW (ensureSortSpec_of_knot p hp n hk F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂
    eb mode (d + k) (r₂.headD 0) hF hn hs₂ h₂.2.2.2) (callW_of_callE h3)
  have hK₃ := h₃.2.1.bkept
  obtain ⟨_, _, _, hT₃⟩ := h₃.2.1
  obtain ⟨x₃, hx₃⟩ := ensureSort_view (AM.run_of_ok _ _ h₃.1)
  rw [h₃.2.2.1] at hx₃
  refine RefE.bind_core (w := id) h₃ (fun M₃ hS₃ _ => ?_)
  simp only [iplE.k_ensure_sort]
  have hB₁ := hB.keep hK₁ hbtop hsz
  have hB₂ := hB₁.keep hK₂ (by rw [hK₁.1]; exact hbtop) (by rw [hK₁.2.1]; exact hsz)
  have hB₃ := hB₂.keep hK₃ (by rw [hK₂.1, hK₁.1]; exact hbtop)
    (by rw [hK₂.2.1, hK₁.2.1]; exact hsz)
  have hdv3 := hS₃.den.sort _ _ hx₃
  have hwl₃ : ∀ (i : Nat) (h : i < ws.size), lvNodeW m₃ ws[i] ≠ [] :=
    fun i hi => lvNodeW_mono (hT₁.trans (hT₂.trans hT₃)).pool.lvl (hws i hi) (hwl i hi)
  have hL := pisOut_ref p hb hcap dn vis fe eb lo k ws hws (G := InferG p n) (n + 1) m₃ _ M₃ k
    (r₃.headD 0) hS₃ h₃.2.2.2 hdv3 hwl₃ hB₃ (Nat.le_refl _) (by rw [hK₃.1, hK₂.1, hK₁.1]; exact hbtop)
  rcases hl : iplE.loop1 p (n + 1) m₃ lo (r₃.headD 0) k with e4 | ⟨v, m₄⟩
  · rw [hl] at hL; exact RefE.bind_left hL
  rw [hl] at hL
  obtain ⟨y, a', hrun, hP, hdl⟩ := hL
  refine RefE.bind_right hrun ?_
  simp only [iplE.k_loop1]
  obtain ⟨M₄, hS₄, hK₄, hSt₄⟩ := hP.after
  rcases h5 : callW p n "intern_sort" [v] m₄ with _ | ⟨r₅, m₅⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [iplE.k_intern_sort]
  obtain ⟨s₅, hs₅, -, hso⟩ := triple_of_callW (s₀ := ⟨m₄, Locals.init []⟩)
    (internSort_spec p hb.sof hb.sop hb.soi n _ v) h5
  rw [hs₅] at hso
  rw [hP.res] at hdl ⊢
  obtain ⟨hrun5, hP5⟩ := (internSort_core hS₄ v hP.valid r₅ hso hdl).post
  exact RefE.ret hrun5 ⟨CoreAfter.comp hK₄ hSt₄ hP5.after, hP5.res, hP5.valid⟩

/-- **`infer_pis_leaf` refines `inferPisLeaf`** at the knot (`ipl_ref`'s ok half). -/
@[refines ConRon.Arena.inferPisLeaf ConRon.Arena.inferPisOut]
theorem inferPisLeaf_refines (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (hftop : fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat) (hB : BStkR s₀.mem lo k ws)
    (hbtop : lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i])
    (hwl : ∀ (i : Nat) (h : i < ws.size), lvNodeW s₀.mem ws[i] ≠ []) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "infer_pis_leaf" [mode, vis, d, t, k, fo, lo]
      (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI))
      decH s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (iplE_spec p hq.pisLeaf (n + 1) s₀ mode vis d t k fo lo)
    (ipl_ref p hp hb hil hcap n hk F hF hn s₀ a₀ dn vis fe M eb mode d t k fo lo fvs ws hs ht hf hftop
      hB hbtop hws hwl hdk)

/-- `infer_pis_leaf` at every L fuel up to `n + 1`. -/
theorem inferPisLeaf_any (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs →
    fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat → BStkR s₀.mem lo k ws →
    lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
    (∀ (i : Nat) (h : i < ws.size), lvNodeW s₀.mem ws[i] ≠ []) →
    d.toNat + k.toNat < 2 ^ 64 →
    CoreSpec p n "infer_pis_leaf" [mode, vis, d, t, k, fo, lo]
      (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI))
      decH s₀ a₀ dn vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, t, k, fo, lo, fvs, ws, hs, ht, hf,
      hftop, hB, hbtop, hws, hwl, hdk =>
      inferPisLeaf_refines p hp hq hb hil hcap n (hk.mono (by omega)) F (by omega) (by omega)
        s₀ a₀ dn vis fe M eb mode d t k fo lo fvs ws hs ht hf hftop hB hbtop hws hwl hdk

/-- `infer_pis_leaf`'s error claim at every L fuel up to `n + 1` (`ipl_ref`'s error half). -/
theorem inferPisLeaf_anyE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap) :
    ∀ n, KnotUpTo p n → InferG p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs →
    fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat → BStkR s₀.mem lo k ws →
    lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
    (∀ (i : Nat) (h : i < ws.size), lvNodeW s₀.mem ws[i] ≠ []) → d.toNat + k.toNat < 2 ^ 64 →
    CoreSpecE p n "infer_pis_leaf" [mode, vis, d, t, k, fo, lo]
      (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI)) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hG, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, t, k, fo, lo, fvs, ws, hs, ht, hf,
      hftop, hB, hbtop, hws, hwl, hdk =>
      RefE.coreSpecE (iplE_spec p hq.pisLeaf (n + 1) s₀ mode vis d t k fo lo) hG.nv (hG.mono (by omega))
        (ipl_ref p hp hb hil hcap n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb
          mode d t k fo lo fvs ws hs ht hf hftop hB hbtop hws hwl hdk)

/-- **The ∀ peel loop with its leaf refines `inferPis`, both outcomes**, by induction on the loop
fuel: a domain's type and its `whnf` (the slots' errors), a domain type that is no sort (a reject),
the leaf's errors. -/
theorem pisLoop_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap)
    (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hFN : N ≤ F) (hN : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo lo eb : Word)
    (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) :
    ∀ j, j ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (peel t k ty u : Word) (fvs : Array EIdx)
      (ws : Array Word),
      CoreS dn m a vis fe M eb → HW t → SpineR m fo k fvs → spTop m = fo + k →
      BStkR m lo k ws → bTop m = lo + k → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
      (∀ (i : Nat) (h : i < ws.size), lvNodeW m ws[i] ≠ []) → d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      (∀ j, j < fo → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      (∀ j, j < lo → rdW (m.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) →
      (m.arr64 BSTK).size = (m₀.arr64 BSTK).size → PoolGrew m₀ m →
      RefE (InferG p N) (ipsE.k_loop1 p N mode vis d fo lo (ipsE.loop1 p j m mode vis d peel t k fo lo ty u))
        (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
          (ws.map decI)) a (TelP dn vis fe M eb m₀ fo lo) := by
  intro j
  induction j with
  | zero =>
    intro _ m a M peel t k ty u fvs ws _ _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [ipsE.loop1.eq_1]; exact RefE.of_cls0 rfl
  | succ j ih =>
    intro hjN m a M peel t k ty u fvs ws hS ht hf htop hB hbt hws hwl hdk hb0 hsz hbb0 hbsz0 hpg0
    rw [ipsE.loop1.eq_2]
    have hspn := hS.spn
    have hcp := hcap _ _ _ _ _ _ _ hS
    have hfb := hf.bound
    have hBb := hB.bound
    have haddf : (fo + k).toNat = fo.toNat + k.toNat := addW _ _ (by omega)
    have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
    have haddd : (d + k).toNat = d.toNat + k.toNat := addW _ _ (by omega)
    have hftop : fo.toNat + k.toNat ≤ (spTop m).toNat := by rw [htop, haddf]; exact Nat.le_refl _
    have hbtop : lo.toNat + k.toNat ≤ (bTop m).toNat := by rw [hbt, haddl]; exact Nat.le_refl _
    by_cases hc : peel ≠ 0 ∧ t >>> 28 = 6
    · rw [ite_eq_left hc]
      obtain ⟨hp0, ht5⟩ := hc
      by_cases hc1 : tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
      · rw [ite_eq_left hc1]; exact RefE.of_cls0 rfl
      rw [ite_eq_right hc1]
      by_cases hc2 : tcnt m FORALL (tierW t) ≤ idxW t
      · rw [ite_eq_left hc2]; exact RefE.of_cls0 rfl
      rw [ite_eq_right hc2]
      have hv : viewOK m t FORALL := ⟨hc1, UInt64.not_le.mp hc2⟩
      obtain ⟨-, hty, hbody⟩ := view_forall m a hS.arena.1 t ht hv ht5
      have hvb := viewBind_forall m a hS.arena.1 t ht hv ht5
      obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
        ⟨peel.toNat - 1, by have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
      have hlam : ((decE t).tag != ETag.forallE) = false := by
        rw [bne_eq_false_iff_eq, ← beq_iff_eq, decE_tag_forallE_beq t ht]; simp [ht5]
      rw [hp', inferPis]
      simp only [hlam, Bool.false_eq_true, ↓reduceIte]
      rw [← haddd]
      refine RefE.bind_right (by rw [viewBind_run', hvb]) ?_
      dsimp only
      have h0 : (0 : Word).toNat = 0 := rfl
      rcases h1 : callW p j "inst_list" [tfld m FORALL (tierW t) (idxW t) 0, fo, k, 0] m with _ | ⟨r₁, m₁⟩
      · rw [liftE_none, ipsE.k_inst_list.eq_1]; exact RefE.of_cls0 (by simp)
      rw [liftE_some, ipsE.k_inst_list.eq_2]
      obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW
        (hil j ⟨m, Locals.init []⟩ a dn vis fe M eb _ fo k 0 fvs hS hty hf hftop) h1
      rw [h0] at hok1 hres1 hS₁
      have hB₁ := hSt₁.bstk
      refine RefE.bind_right (AM.run_of_ok _ _ hok1) ?_
      rw [hres1]
      have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hmode, heb⟩
      rcases h2 : callE p j "infer" [mode, vis, d + k, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
      · rw [ipsE.k_infer.eq_1]
        exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
          ((hG.knot j (by omega)).infer F _ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0) (by omega)
            (by omega) hs₁ hrw1) h2
      rw [ipsE.k_infer.eq_2]
      obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW ((hk j (by omega)).infer F
        ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0) (by omega) (by omega) hs₁ hrw1)
        (callW_of_callE h2)
      have hB₂ := hSt₂.bstk
      refine RefE.bind_right (AM.run_of_ok _ _ hok2) ?_
      erw [hres2]
      have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hmode, heb⟩
      rcases h3 : callE p j "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with e3 | ⟨r₃, m₃⟩
      · rw [ipsE.k_whnf.eq_1]
        exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
          ((hG.knot j (by omega)).whnf F _ _ dn vis fe M₂ eb mode (d + k) (r₂.headD 0) (by omega)
            (by omega) hs₂ hrw2) h3
      rw [ipsE.k_whnf.eq_2]
      obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW ((hk j (by omega)).whnf F
        ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode (d + k) (r₂.headD 0) (by omega) (by omega) hs₂ hrw2)
        (callW_of_callE h3)
      have hB₃ := hSt₃.bstk
      refine RefE.bind_right (AM.run_of_ok _ _ hok3) ?_
      erw [hres3]
      by_cases g1 : r₃.headD 0 >>> 28 ≠ 2
      · rw [ite_eq_left g1]
        simp only [show decH r₃ = decE (r₃.headD 0) from rfl, tag_sort_ne _ hrw3 g1,
          Bool.false_eq_true, ↓reduceIte]
        exact fun _ => ErrClaim.fail _ _ rfl
      rw [ite_eq_right g1]
      have g1' : r₃.headD 0 >>> 28 = 2 := by simpa using g1
      have hsort : ((decH r₃).tag == ETag.sort) = true := tag_sort_beq _ hrw3 g1'
      simp only [hsort, ↓reduceIte]
      by_cases gs1 : tierW (r₃.headD 0) ≠ 0 ∧ rdW (m₃.arr64 CTL) 1 = 0
      · rw [ite_eq_left gs1]; exact RefE.of_cls0 rfl
      rw [ite_eq_right gs1]
      by_cases gs2 : tcnt m₃ SORT (tierW (r₃.headD 0)) ≤ idxW (r₃.headD 0)
      · rw [ite_eq_left gs2]; exact RefE.of_cls0 rfl
      rw [ite_eq_right gs2]
      obtain ⟨hvs, hu⟩ := L.Ind.view_sort_f m₃ _ hS₃.arena.1 (r₃.headD 0) hrw3 ⟨gs1, UInt64.not_le.mp gs2⟩ g1'
      refine RefE.bind_right (L.Ind.viewSort_run (L.Ind.viewSort_of_view _ _ _
        ((decE_tag_eq _ hrw3 2 (by decide)).mpr g1') hvs)) ?_
      dsimp only
      simp only [internFVarE]
      rcases h4 : callW p j "intern_fvar" [d + k, r₁.headD 0] m₃ with _ | ⟨r₄, m₄⟩
      · rw [liftE_none, ipsE.k_intern_fvar.eq_1]; exact RefE.of_cls0 (by simp)
      rw [liftE_some, ipsE.k_intern_fvar.eq_2]
      obtain ⟨s₄, hs₄, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
        (internFVar_spec p hb.fvf hb.fvp hb.fvi j _ (d + k) (r₁.headD 0)) h4
      rw [hs₄] at hfv
      obtain ⟨hok4, ⟨M₄, hS₄, hK₄, hSt₄⟩, hres4, hrw4⟩ := internFVar_core hS₃ (d + k) (r₁.headD 0) hrw1 r₄ hfv
      have hB₄ : BKept m₃ m₄ :=
        BKept.of_frame ((fvinternW_frame (hI := hfv))) (by simp [tier1, FVREC, FVSLOT, FVLP, BSTK]) (by simp)
      refine RefE.bind_right (AM.run_of_ok _ _ hok4) ?_
      erw [hres4]
      by_cases e1 : m₄.len64 SPN ≤ fo + k
      · rw [ite_eq_left e1]; exact RefE.of_cls0 rfl
      rw [ite_eq_right e1]
      by_cases e2 : m₄.len64 BSTK ≤ lo + k
      · rw [ite_eq_left e2]; exact RefE.of_cls0 rfl
      rw [ite_eq_right e2]
      have hSt14 := hSt₁.trans (hSt₂.trans (hSt₃.trans hSt₄))
      have hBK := hB₁.trans (hB₂.trans (hB₃.trans hB₄))
      have hf₄ : SpineR m₄ fo k fvs := hf.keep hSt14.size hSt14.below hftop hspn
      have hB4 : BStkR m₄ lo k ws := hB.keep hBK hbtop hcp
      have hb₄ : ∀ i, i < fo → spW m₄ i = spW m₀ i := fun i hi => by
        have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt14.below i hi').trans (hb0 i hi)
      have hbb₄ : ∀ i, i < lo → rdW (m₄.arr64 BSTK) i = rdW (m₀.arr64 BSTK) i := fun i hi => by
        have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hBK.2.2 i hi').trans (hbb0 i hi)
      have g2 : tPushOK m₄ fo lo k := tPushOK_of hS₄ e1 e2
      obtain ⟨hS', hf', htop', hB', hbt', hb', hsz', hbszT, hbbT, hpgT⟩ := tPush_step (m₀ := m₀) hS₄
        (by rw [hBK.2.1]; exact hcp) hf₄ hB4 hb₄ (hSt14.size.trans hsz) g2 hrw4
      have hws' : ∀ (i : Nat) (h : i < (ws.push (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0)).size),
          HW (ws.push (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0))[i] := by
        intro i hi
        rw [Array.getElem_push]
        split
        · exact hws i _
        · exact hu
      have hl4 := hSt₄.pool.lvl.trans hpgT.lvl
      have hwl' : ∀ (i : Nat) (h : i < (ws.push (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0)).size),
          lvNodeW (tPush m₄ fo lo k (r₄.headD 0) (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0))
          (ws.push (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0))[i] ≠ [] := by
        intro i hi
        rw [Array.getElem_push]
        split
        · exact lvNodeW_mono ((hSt₁.trans (hSt₂.trans hSt₃)).pool.lvl.trans hl4) (hws i _) (hwl i _)
        · exact lvNodeW_mono hl4 hu (lvNodeW_of_den hS₃.arena.1 hu (hS₃.den.sort _ _ hvs))
      have hpeel1 : (peel - 1).toNat = peel.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le]; · rfl
        rw [UInt64.le_iff_toNat_le]; simp
        have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega
      have hk1 : (k + 1).toNat = k.toNat + 1 := addW _ _ (by simp; omega)
      have hih := ih (by omega) (tPush m₄ fo lo k (r₄.headD 0) (tfld m₃ SORT (tierW (r₃.headD 0))
        (idxW (r₃.headD 0)) 0)) _ M₄ (peel - 1) _ (k + 1) (tfld m FORALL (tierW t) (idxW t) 0)
        (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0) _ _ hS' hbody hf' htop' hB' hbt' hws'
        hwl' (by rw [hk1, hpeel1]; omega) hb' hsz' (fun i hi => (hbbT i hi).trans (hbb₄ i hi))
        (hbszT.trans (hBK.2.1.trans hbsz0)) ((hpg0.trans hSt14.pool).trans hpgT)
      rw [hk1, hpeel1, hp', Nat.add_sub_cancel, Array.map_push] at hih
      exact hih.mono fun _ _ _ h => h.keep (hK₁.trans (hK₂.trans (hK₃.trans hK₄)))
    · -- the exit: the leaf
      rw [ite_eq_right hc]
      have hT : (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
          (ws.map decI)).run a = (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t)
          k.toNat fvs (ws.map decI)).run a := by
        by_cases hp0 : peel = 0
        · subst hp0; rfl
        · have ht5 : ¬ t >>> 28 = 6 := fun h => hc ⟨hp0, h⟩
          obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
            ⟨peel.toNat - 1, by
              have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
          have hlam : ((decE t).tag != ETag.forallE) = true := by
            rw [bne_iff_ne, ne_eq, ← beq_iff_eq, decE_tag_forallE_beq t ht]; simp [ht5]
          rw [hp', inferPis]
          simp only [hlam, ↓reduceIte]
      refine RefE.of_run_eq hT ?_
      simp only [ipsE.k_loop1]
      rcases hc' : callE p N "infer_pis_leaf" [mode, vis, d, t, k, fo, lo] m with e | ⟨r, mF⟩
      · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
          (inferPisLeaf_anyE p hp hq hb hil hcap N hk hG F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb
            mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩ ht hf hftop hB hbtop hws hwl (by omega)) hc'
      obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW
        (inferPisLeaf_any p hp hq hb hil hcap N hk F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb
          mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩ ht hf hftop hB hbtop hws hwl (by omega))
        (callW_of_callE hc')
      refine RefE.ret (AM.run_of_ok _ _ hok) ⟨hres, hrw, ⟨M', hS', hK'⟩, fun i hi => ?_,
        hSt'.size.trans hsz, fun i hi => ?_, hSt'.bstk.2.1.trans hbsz0, hpg0.trans hSt'.pool⟩
      · have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt'.below i hi').trans (hb0 i hi)
      · have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt'.bstk.2.2 i hi').trans (hbb0 i hi)

/-- **`infer_pis` refines `inferPis`, both outcomes**, from a telescope state (`fvs` at the spine
top, `stk` at the binder top), up to the tops it leaves raised (`TelP`). -/
theorem ips_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (htop : spTop s₀.mem = fo + k) (hB : BStkR s₀.mem lo k ws) (hbt : bTop s₀.mem = lo + k)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i])
    (hwl : ∀ (i : Nat) (h : i < ws.size), lvNodeW s₀.mem ws[i] ≠ []) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64)
    (hb0 : ∀ j, j < fo → spW s₀.mem j = spW m₀ j) (hsz : (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbb0 : ∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j)
    (hbsz0 : (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size) (hpg0 : PoolGrew m₀ s₀.mem) :
    RefE (InferG p n) (ipsE p (n + 1) s₀.mem mode vis d peel t k fo lo)
      (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decI)) a₀ (TelP dn vis fe M eb m₀ fo lo) := by
  simp only [ipsE]
  exact pisLoop_ref p hp hq hb hil hcap n hk F hF hn dn vis fe mode d fo lo eb hs.mode4 hs.eb_mode
    m₀ (n + 1) (Nat.le_refl _) s₀.mem a₀ M peel t k 0 0 fvs ws hs.rel ht hf htop hB hbt hws hwl hdk hb0 hsz
    hbb0 hbsz0 hpg0

/-- **`infer_pis` refines `inferPis`** (`ips_ref`'s ok half, as a triple at every L fuel up to
`n + 1`). -/
@[refines ConRon.Arena.inferPis]
theorem inferPis_tel (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (htop : spTop s₀.mem = fo + k) (hB : BStkR s₀.mem lo k ws) (hbt : bTop s₀.mem = lo + k)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i])
    (hwl : ∀ (i : Nat) (h : i < ws.size), lvNodeW s₀.mem ws[i] ≠ []) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64)
    (hb0 : ∀ j, j < fo → spW s₀.mem j = spW m₀ j) (hsz : (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbb0 : ∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j)
    (hbsz0 : (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size) (hpg0 : PoolGrew m₀ s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_pis" [mode, vis, d, peel, t, k, fo, lo]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ y a', (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat
      (decE t) k.toNat fvs (ws.map decI)).run a₀ = .ok (y, a') ∧
      TelP dn vis fe M eb m₀ fo lo (r, s'.mem) y a'; ⊤⦄ :=
  RefE.triple (ipsE_spec p hq.pis (n + 1) s₀ mode vis d peel t k fo lo)
    (ips_ref p hp hq hb hil hcap n hk F hF hn s₀ a₀ dn vis fe M eb mode d peel t k fo lo fvs ws m₀ hs
      ht hf htop hB hbt hws hwl hdk hb0 hsz hbb0 hbsz0 hpg0)

/-- `infer_pis`' error claim at every L fuel up to `n + 1` (`ips_ref`'s error half). -/
theorem inferPis_anyE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap) :
    ∀ n, KnotUpTo p n → InferG p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs → spTop s₀.mem = fo + k →
    BStkR s₀.mem lo k ws → bTop s₀.mem = lo + k → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
    (∀ (i : Nat) (h : i < ws.size), lvNodeW s₀.mem ws[i] ≠ []) → d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
    (∀ j, j < fo → spW s₀.mem j = spW m₀ j) → (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size →
    (∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) →
    (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size → PoolGrew m₀ s₀.mem →
    CoreSpecE p n "infer_pis" [mode, vis, d, peel, t, k, fo, lo]
      (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decI)) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hG, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, peel, t, k, fo, lo, fvs, ws, m₀, hs,
      ht, hf, htop, hB, hbt, hws, hwl, hdk, hb0, hsz, hbb0, hbsz0, hpg0 =>
      RefE.coreSpecE (ipsE_spec p hq.pis (n + 1) s₀ mode vis d peel t k fo lo) hG.nv (hG.mono (by omega))
        (ips_ref p hp hq hb hil hcap n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe
          M eb mode d peel t k fo lo fvs ws m₀ hs ht hf htop hB hbt hws hwl hdk hb0 hsz hbb0 hbsz0 hpg0)

/-! ## `infer_forall` -/

/-- **`infer_forall` refines `inferForall`, both outcomes**, at the knot (the `.forallE` clause of
`inferBody`): the domain's type and its `whnf` (the slots' errors), a domain type that is no sort (a
reject), the telescope's (`infer_pis`). -/
theorem ifr_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    RefE (InferG p n) (ifrE p (n + 1) s₀.mem mode vis d ty body)
      (inferForall (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE body)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  simp only [ifrE]
  by_cases hd : d >>> 63 ≠ 0
  · rw [ite_eq_left hd]; exact RefE.of_cls0 rfl
  rw [ite_eq_right hd]
  have hd63 : d.toNat < 2 ^ 63 := by
    have : d >>> 63 = 0 := by simpa using hd
    have h2 := congrArg UInt64.toNat this
    rw [UInt64.toNat_shiftRight] at h2
    simp [Nat.shiftRight_eq_div_pow] at h2
    have := d.toNat_lt
    omega
  simp only [inferForall]
  rcases h1 : callE p n "infer" [mode, vis, d, ty] s₀.mem with e1 | ⟨r₁, m₁⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE ((hG.knot n (Nat.le_refl _)).infer F s₀ a₀ dn vis
      fe M eb mode d ty hF hn hs hty) h1
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW (hK.infer F s₀ a₀ dn vis fe M eb
    mode d ty hF hn hs hty) (callW_of_callE h1)
  refine RefE.bind_right (AM.run_of_ok _ _ hok1) ?_
  simp only [ifrE.k_infer]
  erw [hres1]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  rcases h2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn hs₁ hrw1) h2
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩
    _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn hs₁ hrw1) (callW_of_callE h2)
  refine RefE.bind_right (AM.run_of_ok _ _ hok2) ?_
  simp only [ifrE.k_whnf]
  erw [hres2]
  by_cases g1 : r₂.headD 0 >>> 28 ≠ 2
  · rw [ite_eq_left g1]
    simp only [show decH r₂ = decE (r₂.headD 0) from rfl, tag_sort_ne _ hrw2 g1, Bool.false_eq_true,
      ↓reduceIte]
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [ite_eq_right g1]
  have g1' : r₂.headD 0 >>> 28 = 2 := by simpa using g1
  have hsort : ((decH r₂).tag == ETag.sort) = true := tag_sort_beq _ hrw2 g1'
  simp only [hsort, ↓reduceIte]
  by_cases gs1 : tierW (r₂.headD 0) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0
  · rw [ite_eq_left gs1]; exact RefE.of_cls0 rfl
  rw [ite_eq_right gs1]
  by_cases gs2 : tcnt m₂ SORT (tierW (r₂.headD 0)) ≤ idxW (r₂.headD 0)
  · rw [ite_eq_left gs2]; exact RefE.of_cls0 rfl
  rw [ite_eq_right gs2]
  obtain ⟨hvs, hu⟩ := L.Ind.view_sort_f m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 ⟨gs1, UInt64.not_le.mp gs2⟩ g1'
  refine RefE.bind_right (L.Ind.viewSort_run (L.Ind.viewSort_of_view _ _ _
    ((decE_tag_eq _ hrw2 2 (by decide)).mpr g1') hvs)) ?_
  dsimp only
  simp only [internFVarE]
  rcases h3 : callW p n "intern_fvar" [d, ty] m₂ with _ | ⟨r₃, m₃⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s₃, hs₃, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internFVar_spec p hb.fvf hb.fvp hb.fvi n _ d ty) h3
  rw [hs₃] at hfv
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := internFVar_core hS₂ d ty hty r₃ hfv
  refine RefE.bind_right (AM.run_of_ok _ _ hok3) ?_
  simp only [ifrE.k_intern_fvar]
  erw [hres3]
  have hSt13 := hSt₁.trans (hSt₂.trans hSt₃)
  generalize hso : rdW (m₃.arr64 CTL) 136 = so
  generalize hlo : rdW (m₃.arr64 CTL) 137 = lo
  by_cases e1 : m₃.len64 SPN ≤ so
  · rw [ite_eq_left e1]; exact RefE.of_cls0 rfl
  rw [ite_eq_right e1]
  by_cases e2 : m₃.len64 BSTK ≤ lo
  · rw [ite_eq_left e2]; exact RefE.of_cls0 rfl
  rw [ite_eq_right e2]
  have g2 : tPushOK m₃ so lo 0 := tPushOK_of hS₃ (by simpa using e1) (by simpa using e2)
  have hcp := hcap _ _ _ _ _ _ _ hS₃
  have hsoS : so.toNat ≤ (m₃.arr64 SPN).size := by
    have := g2.2.2.1; simp at this; omega
  have hloS : lo.toNat ≤ (m₃.arr64 BSTK).size := by
    have := g2.2.2.2.1; simp at this; omega
  obtain ⟨hS', hf', htop', hB', hbt', hb', hsz', hbszT, hbbT, hpgT⟩ := tPush_step (m₀ := m₃)
    (fvs := #[]) (ws := #[]) hS₃ hcp (SpineR.empty _ _ hsoS) (BStkR.empty _ _ hloS) (fun _ _ => rfl) rfl
    g2 hrw3 (x := (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0))
  have e01 : (0 : Word) + 1 = 1 := rfl
  rw [e01] at hf' htop' hB' hbt'
  rw [show (((m₃.set64 SPN so (r₃.headD 0)).set64 BSTK lo (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)).set64 CTL 136
    (so + 1)).set64 CTL 137 (lo + 1) = tPush m₃ so lo 0 (r₃.headD 0) (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0) by simp [tPush]]
  have hpf : peelFuel = (16777216 : Word).toNat := rfl
  rw [hpf, show (1 : Nat) = (1 : Word).toNat from rfl, show #[decI (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)] = ((#[] : Array Word).push (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)).map (decI (k := .level))
    by simp, show #[decH r₃] = (#[] : Array EIdx).push (decE (r₃.headD 0)) from rfl]
  rcases h4 : callE p n "infer_pis" [mode, vis, d, 16777216, body, 1, so, lo]
      (tPush m₃ so lo 0 (r₃.headD 0) (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)) with e4 | ⟨r₄, m₄⟩
  · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨_, Locals.init []⟩) (inferPis_anyE p hp hq hb hil hcap
      n hk hG F hF hn _ _ dn vis fe M₃ eb mode d 16777216 body 1 so lo _ _ m₃ ⟨hS', hs.mode4, hs.eb_mode⟩
      hbody hf' htop' hB' hbt' (by intro i hi; simp at hi; subst hi; simpa [HW] using hu)
      (by
        intro i hi
        simp at hi; subst hi
        exact lvNodeW_mono (hSt₃.pool.lvl.trans hpgT.lvl) hu
          (lvNodeW_of_den hS₂.arena.1 hu (hS₂.den.sort _ _ hvs))) (by simp; omega) hb'
      hsz' hbbT hbszT hpgT) h4
  obtain _ | n' := n
  · obtain ⟨e', he', -⟩ := callE_zero p "infer_pis" [mode, vis, d, 16777216, body, 1, so, lo]
      (tPush m₃ so lo 0 (r₃.headD 0) (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0))
    rw [h4] at he'; cases he'
  obtain ⟨t₄, ht₄, -, y, a', hrun4, hT⟩ := triple_of_callE (s₀ := ⟨_, Locals.init []⟩)
    (inferPis_tel p hp hq hb hil hcap n' (hk.mono (by omega)) F (by omega) (by omega) _ _ dn
      vis fe M₃ eb mode d 16777216 body 1 so lo _ _ m₃ ⟨hS', hs.mode4, hs.eb_mode⟩ hbody hf' htop' hB'
      hbt' (by intro i hi; simp at hi; subst hi; simpa [HW] using hu)
      (by
        intro i hi
        simp at hi; subst hi
        exact lvNodeW_mono (hSt₃.pool.lvl.trans hpgT.lvl) hu
          (lvNodeW_of_den hS₂.arena.1 hu (hS₂.den.sort _ _ hvs))) (by simp; omega) hb' hsz' hbbT hbszT
      hpgT) h4
  rw [ht₄] at hT
  simp only [ifrE.k_infer_pis]
  obtain ⟨M', hS₄, hK₄⟩ := hT.rel
  have htop3 : spTop m₃ = so := hso
  obtain ⟨hSF, hkF⟩ := tops_restore (m₀ := s₀.mem) hS₄ hSt13
    (fun j hj => hT.below j (htop3 ▸ hj)) hT.size (fun j hj => hT.bbelow j (by rw [← hlo]; exact hj))
    hT.bsize hT.pool hS₄.ctl137
  rw [hso, hlo] at hSF hkF
  exact RefE.ret hrun4 ⟨⟨M', hSF, hK₁.trans (hK₂.trans (hK₃.trans hK₄)), hkF⟩, hT.res, hT.valid⟩

/-- **`infer_lam` refines `inferLam`** at the knot (`ifr_ref`'s ok half). -/
@[refines ConRon.Arena.inferForall]
theorem inferForall_refines (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpec p (n + 1) "infer_forall" [mode, vis, d, ty, body]
      (inferForall (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE body)) decH s₀ a₀ dn vis fe
        M eb :=
  RefE.coreSpec (ifrE_spec p hq.fa (n + 1) s₀ mode vis d ty body)
    (ifr_ref p hp hq hb hil hcap n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty body hs hty hbody)

/-- `inferBody`'s `.forallE` arm is `inferForall`. -/
@[refines_part ConRon.Arena.inferBody "forallE"]
theorem inferBody_forall (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (ty body : EIdx) (hv : a.store.view e = some (.forallE ty body)) :
    (inferBody r fe d e).run a = (inferForall r fe d ty body).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

end L.Arena
