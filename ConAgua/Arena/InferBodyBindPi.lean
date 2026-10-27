import ConAgua.Arena.InferBodyBind
import ConAgua.Arena.IndSumSpec.DecCVpGrow

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

/-- **`infer_pis_leaf` is its model `inferPisLeafW`** (generated), its outward fold the loop
`inferPisLeafW.loop1`. -/
l_model inferPisLeaf_spec (p : Prog) (hq : BindProg p)
  fns [hq.pisLeaf ↦ inferPisLeafW]
  specs [callW_spec p n "inst_list", callW_spec p n "infer", callW_spec p n "ensure_sort",
    callW_spec p n "intern_imax", callW_spec p n "intern_sort"]
  grind [arena_grind] simp []

/-! ## `infer_pis_leaf` refines `inferPisLeaf` -/

theorem BKept.of_imax {m m' : Mem} {u v r : Word} (h : iminternW m u v = some (r, m')) : BKept m m' := by
  exact BKept.of_frame ((iminternW_frame (hI := h)))
    (by simp [tier1, IREC, ISLOT, IHP, BSTK]) (by simp)

/-- **The outward fold refines `inferPisOut`**, and keeps the binder stack. -/
theorem pisOut_ref (p : Prog) (hb : InferBodyProg p) (hcap : BStkCap) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (eb lo K : Word) (ws : Array Word)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) :
    ∀ k (m : Mem) (a : AState) (M : ModeMaps) (n v : Word),
      CoreS dn m a vis fe M eb → HW v → (∃ l, denoteL a.store.ls (decI v) = some l) →
      (∀ (i : Nat) (h : i < ws.size), lvNodeW m ws[i] ≠ []) →
      BStkR m lo K ws → n.toNat ≤ K.toNat →
      lo.toNat + K.toNat ≤ (bTop m).toNat →
      ∀ w mF, inferPisLeafW.loop1 p k m lo v n = some (w, mF) →
      CoreRef (inferPisOut (ws.map decI) n.toNat (decI v)) a decLv dn m vis fe M eb [w] mF ∧
        BKept m mF ∧
        ∃ l, denoteL (AM.st (inferPisOut (ws.map decI) n.toNat (decI v)) a).store.ls (decI w) = some l := by
  intro k
  induction k with
  | zero => intro m a M n v _ _ _ _ _ _ _ w mF h; simp [inferPisLeafW.loop1] at h
  | succ k ih =>
    intro m a M n v hS hv hdv hwl hB hnK htop w mF h
    by_cases hn : n = 0
    · subst hn
      rw [inferPisLeafW.loop1.arm2 _ _ _ _ _ _ rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hrun : (inferPisOut (ws.map decI) (0 : Word).toNat (decI v)).run a = .ok (decI v, a) := by
        rw [inferPisOut]; rfl
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
      exact ⟨⟨hok, by rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, by rw [hres]; rfl,
        hv⟩, BKept.refl _, by rw [hst]; exact hdv⟩
    rw [inferPisLeafW.loop1.arm1 _ _ _ _ _ _ hn] at h
    have hn1 := sub1_toNat hn
    have hn0' : n.toNat ≠ 0 := fun h' => hn (UInt64.toNat_inj.mp (by simpa using h'))
    have hjK : (n - 1).toNat < ws.size := by rw [hB.size, hn1]; omega
    have hwsj : ws[(n - 1).toNat] = rdW (m.arr64 BSTK) (lo + (n - 1)) := by
      rw [hB.get _ hjK]; simp
    have hwj : HW (rdW (m.arr64 BSTK) (lo + (n - 1))) := hwsj ▸ hws _ hjK
    have hdu : ∃ l, denoteL a.store.ls (decI (rdW (m.arr64 BSTK) (lo + (n - 1)))) = some l := by
      obtain ⟨vv, hvv⟩ := L.Ind.lview_of_lvNodeW hS.arena.1 hwj (hwsj ▸ hwl _ hjK)
      exact hS.den.lvlAll _ (by show (a.store.lss.ls.view _).isSome = true; rw [hvv]; rfl)
    cases h1 : callW p k "intern_imax" [rdW (m.arr64 BSTK) (lo + (n - 1)), v] m with
    | none => rw [h1, inferPisLeafW.k_intern_imax.none] at h; cases h
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [h1, inferPisLeafW.k_intern_imax.arm1] at h
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
    have hT : inferPisOut (ws.map decI) n.toNat (decI v) =
        (internLNode (.imax (decI (rdW (m.arr64 BSTK) (lo + (n - 1)))) (decI v)) >>= fun v2 =>
          inferPisOut (ws.map decI) (n - 1).toNat v2) := by
      rw [inferPisOut]
      simp only [hn0', ↓reduceIte, hn1]
      rw [show (ws.map decI)[n.toNat - 1]! = decI (rdW (m.arr64 BSTK) (lo + (n - 1))) by
        rw [← hn1, getElem!_pos (ws.map decI) _ (by simpa using hjK), Array.getElem_map, hwsj]]
    have hR : CoreRef (inferPisOut (ws.map decI) n.toNat (decI v)) a decLv dn m vis fe M eb [w] mF := by
      rw [hT]
      refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
      exact (ih m₁ _ M₁ (n - 1) (r₁.headD 0) hS₁ h₁.2.2.2 hdv₁ hwl₁ hB₁ (by omega) htop₁ w mF h).1
    obtain ⟨M₁, hS₁, -⟩ := h₁.2.1
    have hih := ih m₁ _ M₁ (n - 1) (r₁.headD 0) hS₁ h₁.2.2.2 hdv₁ hwl₁ hB₁ (by omega) htop₁ w mF h
    refine ⟨hR, hK₁.trans hih.2.1, ?_⟩
    have hok := hR.1
    rw [hT] at hok ⊢
    rw [AM.st_bind _ _ _ hok, h₁.2.2.1]
    exact hih.2.2

/-- **`infer_pis_leaf` refines `inferPisLeaf`** at the knot. -/
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
      decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferPisLeaf_spec p hq (n + 1) s₀ mode vis d t k fo lo)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [inferPisLeafW.arm1] at hW
  cases h1 : callW p n "inst_list" [t, fo, k, 0] s.mem with
  | none => rw [h1, inferPisLeafW.k_inst_list.none] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1, inferPisLeafW.k_inst_list.arm1] at hW
  cases h2 : callW p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
  | none => rw [h2, inferPisLeafW.k_infer.none] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2, inferPisLeafW.k_infer.arm1] at hW
  cases h3 : callW p n "ensure_sort" [mode, vis, d + k, r₂.headD 0] m₂ with
  | none => rw [h3, inferPisLeafW.k_ensure_sort.none] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3, inferPisLeafW.k_ensure_sort.arm1] at hW
  cases h4 : inferPisLeafW.loop1 p (n + 1) m₃ lo (r₃.headD 0) k with
  | none => rw [h4, inferPisLeafW.k_loop1.none] at hW; cases hW
  | some q =>
  obtain ⟨v, m₄⟩ := q
  rw [h4, inferPisLeafW.k_loop1.arm1] at hW
  have hsz := hcap _ _ _ _ _ _ _ hS
  have h₁ := CoreSpec.of_callW (hil n s a₀ dn vis fe M eb t fo k 0 fvs hS ht hf hftop) h1
  have hK₁ := h₁.2.1.bkept
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
  have hK₂ := h₂.2.1.bkept
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_callW (ensureSortSpec_of_knot p hp n hk F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂
    eb mode (d + k) (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.2.2.2) h3
  have hK₃ := h₃.2.1.bkept
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have hB₁ := hB.keep hK₁ hbtop hsz
  have hB₂ := hB₁.keep hK₂ (by rw [hK₁.1]; exact hbtop) (by rw [hK₁.2.1]; exact hsz)
  have hB₃ := hB₂.keep hK₃ (by rw [hK₂.1, hK₁.1]; exact hbtop)
    (by rw [hK₂.2.1, hK₁.2.1]; exact hsz)
  obtain ⟨x₃, hx₃⟩ := ensureSort_view (AM.run_of_ok _ _ h₃.1)
  rw [h₃.2.2.1] at hx₃
  have hdv3 := hS₃.den.sort _ _ hx₃
  have hwl₃ : ∀ (i : Nat) (h : i < ws.size), lvNodeW m₃ ws[i] ≠ [] := by
    obtain ⟨_, _, _, hT₁⟩ := h₁.2.1
    obtain ⟨_, _, _, hT₂⟩ := h₂.2.1
    obtain ⟨_, _, _, hT₃⟩ := h₃.2.1
    exact fun i hi => lvNodeW_mono (hT₁.trans (hT₂.trans hT₃)).pool.lvl (hws i hi) (hwl i hi)
  have h₄' := pisOut_ref p hb hcap dn vis fe eb lo k ws hws (n + 1) m₃ _ M₃ k (r₃.headD 0) hS₃
    h₃.2.2.2 hdv3 hwl₃ hB₃ (Nat.le_refl _) (by rw [hK₃.1, hK₂.1, hK₁.1]; exact hbtop) _ _ h4
  have h₄ := h₄'.1
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  have hso := of_call1W (X := fun m w m' => sointernW m v = some (w, m'))
    (fun s₀ => internSort_spec p hb.sof hb.sop hb.soi n s₀ v) hW
  exact internSort_core hS₄ v h₄.2.2.2 r hso h₄'.2.2

/-- **`infer_pis` is its model `inferPisW`** (generated), its peel loop `inferPisW.loop1`. -/
l_model inferPis_spec (p : Prog) (hq : BindProg p)
  fns [hq.pis ↦ inferPisW]
  specs [callW_spec p n "inst_list", callW_spec p n "infer", callW_spec p n "whnf",
    callW_spec p n "intern_fvar", callW_spec p n "infer_pis_leaf"]
  grind [arena_grind] extra [ld64_rdW_spec, st64_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [tierW, idxW, tfld]

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

/-- A store bound from the L code's length check. -/
theorem pis_lt_of_not_len64_le {m : Mem} {a : ArrId} {x : Word} (hsz : (m.arr64 a).size < 2 ^ 63)
    (h : ¬ m.len64 a ≤ x) : x.toNat < (m.arr64 a).size := by
  have h' := UInt64.not_le.mp h
  rw [UInt64.lt_iff_toNat_lt, Mem.len64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h'
  exact h'

/-- `CTL[137]` (the binder top) is a word of the control array. -/
theorem pis_ctl137 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb) :
    137 < (m.arr64 CTL).size := by
  obtain ⟨mp, h⟩ := hS.memos.2.2.2.2.1
  unfold MemoRG MemoRV at h
  have := h.1
  simp only at this
  have e : (156 : Word).toNat = 156 := rfl
  omega

/-- The guards of a telescope step's pushes from the L code's length checks and `CoreS`. -/
theorem pis_tPushOK_of {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m : Mem} {a : AState} {fo lo k : Word} (hS : CoreS dn m a vis fe M eb)
    (h1 : ¬ m.len64 SPN ≤ fo + k) (h2 : ¬ m.len64 BSTK ≤ lo + k) : tPushOK m fo lo k := by
  exact ⟨h1, h2, pis_lt_of_not_len64_le hS.spn h1, pis_lt_of_not_len64_le hS.bstk h2, pis_ctl137 hS⟩

/-- **The ∀ peel loop with its leaf refines `inferPis`** by induction on the loop fuel. -/
theorem pisFull_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap)
    (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hFN : N ≤ F) (hN : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo lo eb : Word)
    (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) :
    ∀ j, j ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (peel t k ty0 u0 : Word)
      (fvs : Array EIdx) (ws : Array Word),
      CoreS dn m a vis fe M eb → HW t → SpineR m fo k fvs → spTop m = fo + k →
      BStkR m lo k ws → bTop m = lo + k → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
      (∀ (i : Nat) (h : i < ws.size), lvNodeW m ws[i] ≠ []) →
      d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      (∀ j, j < fo → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      (∀ j, j < lo → rdW (m.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) →
      (m.arr64 BSTK).size = (m₀.arr64 BSTK).size → PoolGrew m₀ m →
      ∀ w mF, inferPisW.k_loop1 p N mode vis d fo lo
        (inferPisW.loop1 p j m mode vis d peel t k fo lo ty0 u0) = some (w, mF) →
      TelPost dn vis fe M eb m₀ fo lo a
        (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
          (ws.map decI)) w mF := by
  intro j
  induction j with
  | zero =>
    intro _ m a M peel t k ty0 u0 fvs ws _ _ _ _ _ _ _ _ _ _ _ _ _ _ w mF hF
    rw [inferPisW.loop1.eq_1, inferPisW.k_loop1.none] at hF; cases hF
  | succ j ih =>
    intro hjN m a M peel t k ty0 u0 fvs ws hS ht hf htop hB hbt hws hwl hdk hb0 hsz hbb0 hbsz0 hpg0 w mF hF
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
        TelPost dn vis fe M eb m₀ fo lo a (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat
          peel.toNat (decE t) k.toNat fvs (ws.map decI)) w mF := by
      intro hT hc
      have hl := CoreSpec.of_call1W (r := [w]) (s₀ := ⟨m, Locals.init []⟩)
        (inferPisLeaf_any p hp hq hb hil hcap N hk F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb
          mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩ ht hf hftop hB hbtop hws hwl (by omega))
        (fun r r' h => by simp only [decH, h]) hc
      obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := hl
      refine ⟨_, _, hT.trans (AM.run_of_ok _ _ hok), hres, hrw, M', hS', hK', fun i hi => ?_,
        hSt'.size.trans hsz, fun i hi => ?_, hSt'.bstk.2.1.trans hbsz0, hpg0.trans hSt'.pool⟩
      · have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt'.below i hi').trans (hb0 i hi)
      · have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
        have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt'.bstk.2.2 i hi').trans (hbb0 i hi)
    by_cases hc : peel ≠ 0 ∧ t >>> 28 = 6
    · obtain ⟨hp0, ht6⟩ := hc
      have hc1 : ¬ (tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun g => by
        rw [inferPisW.loop1.abort1 (hc1 := ⟨hp0, ht6⟩) (hc2 := g), inferPisW.k_loop1.none] at hF
        cases hF
      have hc2 : ¬ tcnt m FORALL (tierW t) ≤ idxW t := fun g => by
        rw [inferPisW.loop1.abort2 (hc1 := ⟨hp0, ht6⟩) (hc2 := hc1) (hc3 := g),
          inferPisW.k_loop1.none] at hF
        cases hF
      have hv : viewOK m t FORALL := ⟨hc1, UInt64.not_le.mp hc2⟩
      obtain ⟨-, hty, hbody⟩ := view_forall m a hS.arena.1 t ht hv ht6
      have hvb := viewBind_forall m a hS.arena.1 t ht hv ht6
      rw [inferPisW.loop1.arm1 (hc1 := ⟨hp0, ht6⟩) (hc2 := hc1) (hc3 := hc2)] at hF
      cases h1 : callW p j "inst_list" [tfld m FORALL (tierW t) (idxW t) 0, fo, k, 0] m with
      | none => rw [h1, inferPisW.k_inst_list.none, inferPisW.k_loop1.none] at hF; cases hF
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [h1, inferPisW.k_inst_list.arm1] at hF
      cases h2 : callW p j "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
      | none => rw [h2, inferPisW.k_infer.none, inferPisW.k_loop1.none] at hF; cases hF
      | some q =>
      obtain ⟨r₂, m₂⟩ := q
      rw [h2, inferPisW.k_infer.arm1] at hF
      cases h3 : callW p j "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with
      | none => rw [h3, inferPisW.k_whnf.none, inferPisW.k_loop1.none] at hF; cases hF
      | some q =>
      obtain ⟨r₃, m₃⟩ := q
      rw [h3] at hF
      have g1 : r₃.headD 0 >>> 28 = 2 := Classical.byContradiction fun g => by
        rw [inferPisW.k_whnf.abort1 (hc1 := g), inferPisW.k_loop1.none] at hF; cases hF
      have gs1 : ¬ (tierW (r₃.headD 0) ≠ 0 ∧ rdW (m₃.arr64 CTL) 1 = 0) := fun g => by
        rw [inferPisW.k_whnf.abort2 (hc1 := g1) (hc2 := g), inferPisW.k_loop1.none] at hF; cases hF
      have gs2 : ¬ tcnt m₃ SORT (tierW (r₃.headD 0)) ≤ idxW (r₃.headD 0) := fun g => by
        rw [inferPisW.k_whnf.abort3 (hc1 := g1) (hc2 := gs1) (hc3 := g), inferPisW.k_loop1.none] at hF
        cases hF
      rw [inferPisW.k_whnf.arm1 (hc1 := g1) (hc2 := gs1) (hc3 := gs2)] at hF
      cases h4 : callW p j "intern_fvar" [d + k, r₁.headD 0] m₃ with
      | none => rw [h4, inferPisW.k_intern_fvar.none, inferPisW.k_loop1.none] at hF; cases hF
      | some q =>
      obtain ⟨r₄, m₄⟩ := q
      rw [h4] at hF
      have e1 : ¬ m₄.len64 SPN ≤ fo + k := fun g => by
        rw [inferPisW.k_intern_fvar.abort1 (hc1 := g), inferPisW.k_loop1.none] at hF; cases hF
      have e2 : ¬ m₄.len64 BSTK ≤ lo + k := fun g => by
        rw [inferPisW.k_intern_fvar.abort2 (hc1 := e1) (hc2 := g), inferPisW.k_loop1.none] at hF
        cases hF
      rw [inferPisW.k_intern_fvar.arm1 (hc1 := e1) (hc2 := e2)] at hF
      have h0 : (0 : Word).toNat = 0 := rfl
      -- the domain opened
      have hinst := hil j ⟨m, Locals.init []⟩ a dn vis fe M eb _ fo k 0 fvs hS hty hf hftop
      obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW hinst h1
      rw [h0] at hok1 hres1 hS₁
      have hB₁ := hSt₁.bstk
      -- its type, a sort
      have hi := CoreSpec.of_callW ((hk j (by omega)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
        mode (d + k) (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) h2
      obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := hi
      have hB₂ := hSt₂.bstk
      have hw := CoreSpec.of_callW ((hk j (by omega)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb
        mode (d + k) (r₂.headD 0) (by omega) (by omega) ⟨hS₂, hmode, heb⟩ hrw2) h3
      obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := hw
      have hB₃ := hSt₃.bstk
      -- the binder's free variable
      obtain ⟨s₄, hs₄, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
        (internFVar_spec p hb.fvf hb.fvp hb.fvi j _ (d + k) (r₁.headD 0)) h4
      rw [hs₄] at hfv
      have h₄ := internFVar_core hS₃ (d + k) (r₁.headD 0) hrw1 r₄ hfv
      obtain ⟨hok4, ⟨M₄, hS₄, hK₄, hSt₄⟩, hres4, hrw4⟩ := h₄
      have hB₄ : BKept m₃ m₄ := by
        exact BKept.of_frame ((fvinternW_frame (hI := hfv)))
          (by simp [tier1, FVREC, FVSLOT, FVLP, BSTK]) (by simp)
      -- the stacks kept across the four calls
      have hSt14 := hSt₁.trans (hSt₂.trans (hSt₃.trans hSt₄))
      have hBK := hB₁.trans (hB₂.trans (hB₃.trans hB₄))
      have hf₄ : SpineR m₄ fo k fvs := hf.keep hSt14.size hSt14.below hftop hspn
      have hB4 : BStkR m₄ lo k ws := hB.keep hBK hbtop hcp
      have hb₄ : ∀ i, i < fo → spW m₄ i = spW m₀ i := fun i hi => by
        have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt14.below i hi').trans (hb0 i hi)
      have hbb₄ : ∀ i, i < lo → rdW (m₄.arr64 BSTK) i = rdW (m₀.arr64 BSTK) i := fun i hi => by
        have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
        have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hBK.2.2 i hi').trans (hbb0 i hi)
      have g2 : tPushOK m₄ fo lo k := pis_tPushOK_of hS₄ e1 e2
      have hF' : inferPisW.k_loop1 p N mode vis d fo lo
          (inferPisW.loop1 p j (tPush m₄ fo lo k (r₄.headD 0)
            (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0)) mode vis d (peel - 1)
            (tfld m FORALL (tierW t) (idxW t) 1) (k + 1) fo lo
            (tfld m FORALL (tierW t) (idxW t) 0)
            (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0)) = some (w, mF) := hF
      obtain ⟨hS', hf', htop', hB', hbt', hb', hsz', hbszT, hbbT, hpgT⟩ := tPush_step (m₀ := m₀) hS₄
        (by rw [hBK.2.1]; exact hcp) hf₄ hB4 hb₄ (hSt14.size.trans hsz) g2 hrw4
      obtain ⟨hvs, hu⟩ := L.Ind.view_sort_f m₃ _ hS₃.arena.1 (r₃.headD 0) hrw3 ⟨gs1, UInt64.not_le.mp gs2⟩ g1
      have hl4 := hSt₄.pool.lvl.trans hpgT.lvl
      have hwl' : ∀ (i : Nat) (h : i < (ws.push (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0)).size), lvNodeW (tPush m₄ fo lo k (r₄.headD 0)
          (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0))
          (ws.push (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0))[i] ≠ [] := by
        intro i hi
        rw [Array.getElem_push]
        split
        · exact lvNodeW_mono ((hSt₁.trans (hSt₂.trans hSt₃)).pool.lvl.trans hl4) (hws i _) (hwl i _)
        · exact lvNodeW_mono hl4 hu (lvNodeW_of_den hS₃.arena.1 hu (hS₃.den.sort _ _ hvs))
      have hws' : ∀ (i : Nat) (h : i < (ws.push (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0)).size), HW (ws.push (tfld m₃ SORT (tierW (r₃.headD 0)) (idxW (r₃.headD 0)) 0))[i] := by
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
      obtain ⟨x, a', hrun', hx, hrw, M', hS'', hK, hb'', hsz'', hbb'', hbsz'', hpg''⟩ := ih (by omega)
        _ _ M₄ (peel - 1) _ (k + 1) _ _ _ _ hS' hbody hf' htop' hB' hbt' hws' hwl' (by rw [hk1, hpeel1]; omega)
        hb' hsz' (fun i hi => (hbbT i hi).trans (hbb₄ i hi)) (hbszT.trans (hBK.2.1.trans hbsz0))
        ((hpg0.trans hSt14.pool).trans hpgT) w mF hF'
      refine ⟨x, a', ?_, hx, hrw, M', hS'', hK₁.trans (hK₂.trans (hK₃.trans (hK₄.trans hK))), hb'',
        hsz'', hbb'', hbsz'', hpg''⟩
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
      rw [hsort, ite_eq_left rfl, StateT.run_bind,
        L.Ind.viewSort_run (L.Ind.viewSort_of_view _ _ _ ((decE_tag_eq _ hrw3 2 (by decide)).mpr g1) hvs),
        except_ok_bind]
      simp only [internFVarE, StateT.run_bind]
      rw [AM.run_of_ok _ _ hok4, except_ok_bind, hres4, hk1, hpeel1, hp', Nat.add_sub_cancel,
        Array.map_push]
    · -- the exit
      rw [inferPisW.loop1.arm2 (hc1 := hc), inferPisW.k_loop1.arm1] at hF
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
    (hil : InstListOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (htop : spTop s₀.mem = fo + k) (hB : BStkR s₀.mem lo k ws) (hbt : bTop s₀.mem = lo + k)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i])
    (hwl : ∀ (i : Nat) (h : i < ws.size), lvNodeW s₀.mem ws[i] ≠ [])
    (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64)
    (hb0 : ∀ j, j < fo → spW s₀.mem j = spW m₀ j) (hsz : (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbb0 : ∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j)
    (hbsz0 : (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size) (hpg0 : PoolGrew m₀ s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_pis" [mode, vis, d, peel, t, k, fo, lo]
    ⦃fun r s' => LocEq s' s₀ ∧ TelPost dn vis fe M eb m₀ fo lo a₀
      (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decI)) (r.headD 0) s'.mem; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferPis_spec p hq (n + 1) s₀ mode vis d peel t k fo lo)
  subst hs0
  exact ⟨hloc, pisFull_ref p hp hq hb hil hcap n hk F hF hn dn vis fe mode d fo lo eb hs.mode4
    hs.eb_mode m₀ (n + 1) (Nat.le_refl _) s.mem a₀ M peel t k 0 0 fvs ws hs.rel ht hf htop hB hbt hws hwl hdk
    hb0 hsz hbb0 hbsz0 hpg0 _ _ (by rw [inferPisW.arm1] at hW; exact hW)⟩


/-! ## `infer_forall` -/

/-- **`infer_forall` is its model `inferForallW`** (generated). -/
l_model inferForall_spec (p : Prog) (hq : BindProg p)
  fns [hq.fa ↦ inferForallW]
  specs [callW_spec p n "infer", callW_spec p n "whnf", callW_spec p n "intern_fvar",
    callW_spec p n "infer_pis"]
  grind [arena_grind] extra [ld64_rdW_spec, st64_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [tierW, idxW, tfld]

@[refines ConRon.Arena.inferForall]
theorem inferForall_refines (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpec p (n + 1) "infer_forall" [mode, vis, d, ty, body]
      (inferForall (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE body)) decH s₀ a₀ dn vis fe
        M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (inferForall_spec p hq (n + 1) s₀ mode vis d ty body)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  by_cases hd : d >>> 63 ≠ 0
  · rw [inferForallW.abort1 (hc1 := hd)] at hW; cases hW
  have hd0 : d >>> 63 = 0 := by simpa using hd
  rw [inferForallW.arm1 (hc1 := hd0)] at hW
  have hd63 : d.toNat < 2 ^ 63 := by
    have : d >>> 63 = 0 := by simpa using hd
    have h2 := congrArg UInt64.toNat this
    rw [UInt64.toNat_shiftRight] at h2
    simp [Nat.shiftRight_eq_div_pow] at h2
    have := d.toNat_lt
    omega
  cases h1 : callW p n "infer" [mode, vis, d, ty] s.mem with
  | none => rw [h1, inferForallW.k_infer.none] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1, inferForallW.k_infer.arm1] at hW
  cases h2 : callW p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
  | none => rw [h2, inferForallW.k_whnf.none] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  by_cases g1 : r₂.headD 0 >>> 28 ≠ 2
  · rw [inferForallW.k_whnf.abort1 (hc1 := g1)] at hW; cases hW
  have hg2 : r₂.headD 0 >>> 28 = 2 := by simpa using g1
  by_cases gs1 : tierW (r₂.headD 0) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0
  · rw [inferForallW.k_whnf.abort2 (hc1 := hg2) (hc2 := gs1)] at hW; cases hW
  by_cases gs2 : tcnt m₂ SORT (tierW (r₂.headD 0)) ≤ idxW (r₂.headD 0)
  · rw [inferForallW.k_whnf.abort3 (hc1 := hg2) (hc2 := gs1) (hc3 := gs2)] at hW; cases hW
  rw [inferForallW.k_whnf.arm1 (hc1 := hg2) (hc2 := gs1) (hc3 := gs2)] at hW
  cases h3 : callW p n "intern_fvar" [d, ty] m₂ with
  | none => rw [h3, inferForallW.k_intern_fvar.none] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW
  have e1 : ¬ m₃.len64 SPN ≤ rdW (m₃.arr64 CTL) 136 := fun g => by
    rw [inferForallW.k_intern_fvar.abort1 (hc1 := g)] at hW; cases hW
  have e2 : ¬ m₃.len64 BSTK ≤ rdW (m₃.arr64 CTL) 137 := fun g => by
    rw [inferForallW.k_intern_fvar.abort2 (hc1 := e1) (hc2 := g)] at hW; cases hW
  rw [inferForallW.k_intern_fvar.arm1 (hc1 := e1) (hc2 := e2)] at hW
  rw [← show tPush m₃ (rdW (m₃.arr64 CTL) 136) (rdW (m₃.arr64 CTL) 137) 0 (r₃.headD 0)
      (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0) =
      ((((m₃.set64 SPN (rdW (m₃.arr64 CTL) 136) (r₃.headD 0)).set64 BSTK (rdW (m₃.arr64 CTL) 137)
        (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)).set64 CTL 136
          (rdW (m₃.arr64 CTL) 136 + 1)).set64 CTL 137 (rdW (m₃.arr64 CTL) 137 + 1)) by
    simp [tPush]] at hW
  cases h4 : callW p n "infer_pis" [mode, vis, d, 16777216, body, 1, rdW (m₃.arr64 CTL) 136,
      rdW (m₃.arr64 CTL) 137] (tPush m₃ (rdW (m₃.arr64 CTL) 136) (rdW (m₃.arr64 CTL) 137) 0 (r₃.headD 0)
        (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)) with
  | none => rw [h4, inferForallW.k_infer_pis.none] at hW; cases hW
  | some q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [h4, inferForallW.k_infer_pis.arm1] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  -- the domain's type, a sort
  have h₁ := CoreSpec.of_callW (hK.infer F s a₀ dn vis fe M eb mode d ty hF hn hs hty) h1
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := h₁
  have hB₁ := hSt₁.bstk
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn
    ⟨hS₁, hs.mode4, hs.eb_mode⟩ hrw1) h2
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := h₂
  have hB₂ := hSt₂.bstk
  obtain ⟨hvs, hu⟩ := L.Ind.view_sort_f m₂ _ hS₂.arena.1 (r₂.headD 0) hrw2 ⟨gs1, by simpa using gs2⟩ hg2
  obtain ⟨s₃, hs₃, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internFVar_spec p hb.fvf hb.fvp hb.fvi n _ d ty) h3
  rw [hs₃] at hfv
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := internFVar_core hS₂ d ty hty r₃ hfv
  -- the pushes
  have hSt13 := hSt₁.trans (hSt₂.trans hSt₃)
  obtain ⟨so, hso⟩ : ∃ so, so = rdW (m₃.arr64 CTL) 136 := ⟨_, rfl⟩
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = rdW (m₃.arr64 CTL) 137 := ⟨_, rfl⟩
  have g2 : tPushOK m₃ (rdW (m₃.arr64 CTL) 136) (rdW (m₃.arr64 CTL) 137) 0 :=
    pis_tPushOK_of hS₃ (by simpa using e1) (by simpa using e2)
  rw [← hso, ← hlo] at g2 h4 hm
  have hcp := hcap _ _ _ _ _ _ _ hS₃
  have hsoS : so.toNat ≤ (m₃.arr64 SPN).size := by
    have := g2.2.2.1; simp at this; omega
  have hloS : lo.toNat ≤ (m₃.arr64 BSTK).size := by
    have := g2.2.2.2.1; simp at this; omega
  have g2' : tPushOK m₃ so lo 0 := g2
  obtain ⟨hS', hf', htop', hB', hbt', hb', hsz', hbszT, hbbT, hpgT⟩ := tPush_step (m₀ := m₃) (fvs := #[]) (ws := #[])
    hS₃ hcp (SpineR.empty _ _ hsoS) (BStkR.empty _ _ hloS) (fun _ _ => rfl) rfl g2' hrw3
  have e01 : (0 : Word) + 1 = 1 := rfl
  rw [e01] at hf' htop' hB' hbt'
  cases n with
  | zero => rw [callW_zero] at h4; cases h4
  | succ n' =>
  obtain ⟨t₄, ht₄, -, hTel⟩ := triple_of_callW (s₀ := ⟨_, Locals.init []⟩)
    (inferPis_tel p hp hq hb hil hcap n' (hk.mono (by omega)) F (by omega) (by omega) _ _ dn
      vis fe M₃ eb mode d 16777216 body 1 so lo _ _ m₃ ⟨hS', hs.mode4, hs.eb_mode⟩ hbody hf' htop' hB'
      hbt' (by intro i hi; simp at hi; subst hi; simpa [HW] using hu)
      (by
        intro i hi
        simp at hi; subst hi
        exact lvNodeW_mono (hSt₃.pool.lvl.trans hpgT.lvl) hu
          (lvNodeW_of_den hS₂.arena.1 hu (hS₂.den.sort _ _ hvs)))
      (by simp; omega) hb' hsz' hbbT hbszT hpgT) h4
  rw [ht₄] at hTel
  obtain ⟨x, a', hrun4, hx, hrw4, M', hS₄, hK₄, hb₄, hsz₄, hbb₄, hbsz₄, hpg₄⟩ := hTel
  -- the twin's run
  have hsort : ((decE (r₂.headD 0)).tag == ETag.sort) = true := tag_sort_beq _ hrw2 (by simpa using g1)
  have hrun : (inferForall (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE body)).run a₀ =
      .ok (x, a') := by
    simp only [inferForall, StateT.run_bind]
    have hpf : (16777216 : Word).toNat = peelFuel := rfl
    rw [hpf] at hrun4
    generalize peelFuel = P at hrun4 ⊢
    rw [AM.run_of_ok _ _ hok1, except_ok_bind, hres1]
    simp only [decH] at hres2 hres3 ⊢
    rw [AM.run_of_ok _ _ hok2, except_ok_bind, hres2]
    rw [hsort, ite_eq_left rfl, StateT.run_bind,
      L.Ind.viewSort_run (L.Ind.viewSort_of_view _ _ _ ((decE_tag_eq _ hrw2 2 (by decide)).mpr hg2) hvs),
      except_ok_bind, internFVarE, StateT.run_bind]
    rw [AM.run_of_ok _ _ hok3, except_ok_bind, hres3]
    have ha2 : ((#[] : Array Word).push (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)).map (decI (k := .level)) = #[decI (tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0)] := by simp
    rw [ha2] at hrun4
    exact hrun4
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, by rw [hres, hx, decH, hr], by unfold ResH; rw [← hr]; exact hrw4⟩
  rw [hst, ← hm, hso, hlo]
  have htop3 : spTop m₃ = so := hso.symm
  obtain ⟨hSF, hkF⟩ := tops_restore (m₀ := s.mem) hS₄ hSt13
    (fun j hj => hb₄ j (htop3 ▸ hj)) hsz₄ (fun j hj => hbb₄ j (by rw [hlo]; exact hj)) hbsz₄ hpg₄ (pis_ctl137 hS₄)
  exact ⟨M', hSF, hK₁.trans (hK₂.trans (hK₃.trans hK₄)), hkF⟩


/-- `inferBody`'s `.forallE` arm is `inferForall`. -/
@[refines_part ConRon.Arena.inferBody "forallE"]
theorem inferBody_forall (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (ty body : EIdx) (hv : a.store.view e = some (.forallE ty body)) :
    (inferBody r fe d e).run a = (inferForall r fe d ty body).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

end L.Arena
