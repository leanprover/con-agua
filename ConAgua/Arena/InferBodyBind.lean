import ConAgua.Arena.InferBodySpine
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.InferBodyBindModels

/-!
# The binder telescopes: `infer_lams`, `infer_pis`, their leaves, `infer_lam`, `infer_forall`

The telescopes keep two stacks growing in step: the free variables `fvs` on the spine stack `SPN`
(array 144, top `CTL[136]`; `SpineR`) and the second list `stk` on the binder stack `BSTK`
(array 145, top `CTL[137]`; `BStkR`, a slice of words). `CoreS` survives writes to both
(`CoreS.frame_stk`, `CoreS.frame`).

**What the callees must keep.** The callees a telescope calls while its stack holds entries
(`infer`, `whnf`, `inst_list`, `ar_entry`, `ensure_sort`) keep `BSTK` below `CTL[137]` and
`CTL[137]`: `CoreAfter`'s `StackKept.bstk` (lane `whnf3`; `CoreAfter.bkept`); the interning
callees by their frames (`BKept.of_frame`).

Each function has one unified model and one refinement for both outcomes (`RefE`, `InferG`): the
leaves `ilf_ref`/`ipl_ref` (their outward loops `lamsOut_ref`/`pisOut_ref`), the peel loops
`lamsLoop_ref`/`pisLoop_ref` (post `TelP`, the telescope's tops left raised), `ilm_ref`/`ifr_ref`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- A core run keeps the binder stack (`StackKept.bstk`, lane `whnf3`). -/
theorem CoreAfter.bkept {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (h : CoreAfter dn m₀ m a vis fe M eb) : BKept m₀ m := by
  obtain ⟨_, _, _, hSt⟩ := h; exact hSt.bstk

/-! ## The binder stack -/

/-- **A slice of the binder stack**, as words. -/
structure BStkR (m : Mem) (lo k : Word) (ws : Array Word) : Prop where
  size : ws.size = k.toNat
  bound : lo.toNat + k.toNat ≤ (m.arr64 BSTK).size
  get : ∀ (i : Nat) (h : i < ws.size), ws[i] = rdW (m.arr64 BSTK) (lo + i.toUInt64)

theorem BStkR.keep {m m' : Mem} {lo k : Word} {ws : Array Word} (h : BStkR m lo k ws)
    (hK : BKept m m') (htop : lo.toNat + k.toNat ≤ (bTop m).toNat)
    (hsz : (m.arr64 BSTK).size < 2 ^ 63) : BStkR m' lo k ws := by
  have hb := h.bound
  refine ⟨h.size, hK.2.1 ▸ hb, fun i hi => ?_⟩
  have hi' : i < k.toNat := h.size ▸ hi
  have hlt : lo + i.toUInt64 < bTop m := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat']
    have : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.mod_eq_of_lt (by omega)]; omega
  rw [hK.2.2 _ hlt]; exact h.get i hi

theorem BStkR.empty (m : Mem) (lo : Word) (h : lo.toNat ≤ (m.arr64 BSTK).size) : BStkR m lo 0 #[] :=
  ⟨rfl, by simpa using h, fun i hi => by simp at hi⟩

theorem BStkR.push {m : Mem} {lo k : Word} {ws : Array Word} (h : BStkR m lo k ws)
    (hcap : (m.arr64 BSTK).size < 2 ^ 63) (hb : (lo + k).toNat < (m.arr64 BSTK).size) (v : Word) :
    BStkR (m.set64 BSTK (lo + k) v) lo (k + 1) (ws.push v) := by
  have hsz := h.bound
  have hsize := h.size
  have h1 : (1 : Word).toNat = 1 := by decide
  have hoc : (lo + k).toNat = lo.toNat + k.toNat := by simp only [UInt64.toNat_add]; omega
  have hcnt1 : (k + 1).toNat = k.toNat + 1 := by simp only [UInt64.toNat_add, h1]; omega
  have hidx : ∀ i : Nat, i ≤ k.toNat → (lo + (i.toUInt64 : Word)).toNat = lo.toNat + i := by
    intro i hi
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  have heqv : lo + (k.toNat.toUInt64 : Word) = lo + k :=
    UInt64.toNat_inj.mp (by rw [hidx k.toNat (by omega), hoc])
  refine ⟨by rw [Array.size_push, h.size, hcnt1], by rw [size_set64L, hcnt1]; omega, fun i hi => ?_⟩
  rw [Array.size_push, h.size] at hi
  rw [rdW_set64]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
  · rw [Array.getElem_push, dite_eq_left (by rw [h.size]; exact hi'), h.get i (by rw [h.size]; exact hi')]
    rw [ite_eq_right]
    rintro ⟨-, hco, -⟩
    have := congrArg UInt64.toNat hco
    rw [hidx i (by omega), hoc] at this
    omega
  · have hieq : i = k.toNat := hi'
    subst hieq
    rw [Array.getElem_push, dite_eq_right (by omega), heqv, ite_eq_left ⟨rfl, rfl, hb⟩]

theorem BStkR.frame {m m' : Mem} {lo k : Word} {ws : Array Word} (h : BStkR m lo k ws)
    (hb : m'.arr64 BSTK = m.arr64 BSTK) : BStkR m' lo k ws :=
  ⟨h.size, hb ▸ h.bound, fun i hi => by rw [hb]; exact h.get i hi⟩

/-- **The binder stack's capacity**: under `CoreS` it is below `2^63` words (as `CoreS.spn` for the
spine stack; a field `CoreS` lacks, assumed here). -/
def BStkCap : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb → (m.arr64 BSTK).size < 2 ^ 63

/-! ## `infer_lams_leaf` -/

/-- What the telescope specs need of a program. -/
structure BindProg (p : Prog) : Prop where
  lamsLeaf : p.lookup "infer_lams_leaf" = some inferLamsLeafL
  lams : p.lookup "infer_lams" = some inferLamsL
  lam : p.lookup "infer_lam" = some inferLamL
  pisLeaf : p.lookup "infer_pis_leaf" = some inferPisLeafL
  pis : p.lookup "infer_pis" = some inferPisL
  fa : p.lookup "infer_forall" = some inferForallL

/-! ## `infer_lams_leaf` refines `inferLamsLeaf` -/

theorem BKept.of_mkForall {m m' : Mem} {t b r : Word} (h : mkForallW m t b = some (r, m')) :
    BKept m m' :=
  BKept.of_frame (mkForallW_frame h) (by simp [tier1, FADER, FAREC, FASLOT, BSTK]) (by simp)

theorem sub1_toNat {n : Word} (h : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have : n.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  rw [UInt64.toNat_sub_of_le]; · rfl
  rw [UInt64.le_iff_toNat_le]; simp; omega

/-- **The outward rebuild refines `inferLamsOut`, both outcomes** (by induction on the loop fuel;
`ar_entry` and `mk_forall` are lifted, their errors of class `0`). -/
theorem lamsOut_ref (p : Prog) (hp : InferLeafProg p) (hab : AbstractRangeOK p)
    (hcap : BStkCap) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb d lo K : Word) (ws : Array Word) (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i])
    {G : Prop} :
    ∀ k (m : Mem) (a : AState) (M : ModeMaps) (n cur : Word),
      CoreS dn m a vis fe M eb → HW cur → BStkR m lo K ws → n.toNat ≤ K.toNat →
      lo.toNat + K.toNat ≤ (bTop m).toNat →
      RefE G (ilfE.loop1 p k m d lo cur n) (inferLamsOut d.toNat (ws.map decE) n.toNat (decE cur)) a
        (fun v y a' => CorePost decH dn m vis fe M eb ResH ([v.1], v.2) y a') := by
  intro k
  induction k with
  | zero => intro m a M n cur _ _ _ _ _; rw [ilfE.loop1.eq_1]; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro m a M n cur hS hc hB hnK htop
    rw [ilfE.loop1.eq_2]
    by_cases hn : n = 0
    · subst hn
      rw [ite_eq_right (by simp)]
      exact RefE.ret (by rw [inferLamsOut]; rfl) (CorePost.ret hS rfl hc)
    rw [ite_eq_left hn]
    have hn1 := sub1_toNat hn
    have hn0' : n.toNat ≠ 0 := fun h' => hn (UInt64.toNat_inj.mp (by simpa using h'))
    have hjK : (n - 1).toNat < ws.size := by rw [hB.size, hn1]; omega
    have hwsj : ws[(n - 1).toNat] = rdW (m.arr64 BSTK) (lo + (n - 1)) := by
      rw [hB.get _ hjK]; simp
    have hwj : HW (rdW (m.arr64 BSTK) (lo + (n - 1))) := hwsj ▸ hws _ hjK
    have hT : inferLamsOut d.toNat (ws.map decE) n.toNat (decE cur) =
        (abstractRangeFast coreWalkFuel (decE (rdW (m.arr64 BSTK) (lo + (n - 1)))) d.toNat
          (n - 1).toNat (0 : Word).toNat >>= fun tyAbs => internForallEE tyAbs (decE cur) >>= fun nd =>
          inferLamsOut d.toNat (ws.map decE) (n - 1).toNat nd) := by
      rw [inferLamsOut]
      simp only [hn0', ↓reduceIte, hn1]
      rw [show (ws.map decE)[n.toNat - 1]! = decE (rdW (m.arr64 BSTK) (lo + (n - 1))) by
        rw [← hn1, getElem!_pos (ws.map decE) _ (by simpa using hjK), Array.getElem_map, hwsj]]
      rfl
    rw [hT]
    rcases h1 : callW p k "ar_entry" [rdW (m.arr64 BSTK) (lo + (n - 1)), d, n - 1, 0] m with _ | ⟨r₁, m₁⟩
    · rw [liftE_none, ilfE.k_ar_entry_2.eq_1]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, ilfE.k_ar_entry_2.eq_2]
    have h₁ := CoreSpec.of_callW (hab k ⟨m, Locals.init []⟩ a dn vis fe M eb _ d (n - 1) 0 hS hwj) h1
    have hK₁ := h₁.2.1.bkept
    have hsz := hcap _ _ _ _ _ _ _ hS
    refine RefE.bind_core (w := fun (v : Word × Mem) => ([v.1], v.2)) h₁ (fun M₁ hS₁ _ => ?_)
    rcases h2 : callW p k "mk_forall" [r₁.headD 0, cur] m₁ with _ | ⟨r₂, m₂⟩
    · rw [liftE_none, ilfE.k_mk_forall.eq_1]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, ilfE.k_mk_forall.eq_2]
    obtain ⟨s₂, hs₂, -, hmk⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (mkForall_spec p hp.derb hp.faf hp.fap hp.fai hp.mkfa k _ (r₁.headD 0) cur) h2
    rw [hs₂] at hmk
    have hK₂ := BKept.of_mkForall hmk
    have hB₂ : BStkR m₂ lo K ws := (hB.keep hK₁ htop hsz).keep hK₂ (by rw [hK₁.1]; exact htop)
      (by rw [hK₁.2.1]; exact hsz)
    have htop₂ : lo.toNat + K.toNat ≤ (bTop m₂).toNat := by rw [hK₂.1, hK₁.1]; exact htop
    refine RefE.bind_core (w := fun (v : Word × Mem) => ([v.1], v.2)) (mkForall_core hS₁ (r₁.headD 0) cur r₂ hmk)
      (fun M₂ hS₂ _ => ?_)
    exact ih m₂ _ M₂ (n - 1) (r₂.headD 0) hS₂ (mkForallW_hw _ _ hS₁.arena _ _ _ _ hmk) hB₂ (by omega)
      htop₂

/-- **`infer_lams_leaf` refines `inferLamsLeaf`, both outcomes**, at the knot: `fvs` the stack slice
`(fo, k)` at the top, `stk` the binder-stack slice `(lo, k)` below the binder top. Its errors are the
`infer` slot's at `d + k`; the opening and the outward rebuild claim nothing. -/
theorem ilf_ref (p : Prog) (hp : InferLeafProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (hftop : fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat) (hB : BStkR s₀.mem lo k ws)
    (hbtop : lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (InferG p n) (ilfE p (n + 1) s₀.mem mode vis d t k fo lo)
      (inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hsz := hcap _ _ _ _ _ _ _ hS
  have hdk' : (d + k).toNat = d.toNat + k.toNat := addW _ _ hdk
  have h0 : (0 : Word).toNat = 0 := rfl
  have hT : inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE) =
      (instantiateListFast coreWalkFuel (decE t) fvs (0 : Word).toNat >>= fun ob =>
        (coreKnot (decMode mode) fe id F).infer (d + k).toNat ob >>= fun bt =>
        abstractRangeFast coreWalkFuel bt d.toNat k.toNat (0 : Word).toNat >>= fun cur =>
        inferLamsOut d.toNat (ws.map decE) k.toNat cur) := by
    rw [hdk', h0, inferLamsLeaf, Array.size_map, hB.size]
  rw [hT]
  simp only [ilfE]
  rcases h1 : callW p n "inst_list" [t, fo, k, 0] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [ilfE.k_inst_list]
  have h₁ := CoreSpec.of_callW (hil n s₀ a₀ dn vis fe M eb t fo k 0 fvs hS ht hf hftop) h1
  have hK₁ := h₁.2.1.bkept
  refine RefE.bind_core (w := id) h₁ (fun M₁ hS₁ _ => ?_)
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  rcases h2 : callE p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).infer F _ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0) hF hn hs₁
        h₁.2.2.2) h2
  have h₂ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode (d + k) (r₁.headD 0) hF hn hs₁ h₁.2.2.2) (callW_of_callE h2)
  have hK₂ := h₂.2.1.bkept
  refine RefE.bind_core (w := id) h₂ (fun M₂ hS₂ _ => ?_)
  simp only [ilfE.k_infer]
  rcases h3 : callW p n "ar_entry" [r₂.headD 0, d, k, 0] m₂ with _ | ⟨r₃, m₃⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [ilfE.k_ar_entry]
  have h₃ := CoreSpec.of_callW (hab n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb (r₂.headD 0) d k 0 hS₂
    h₂.2.2.2) h3
  have hK₃ := h₃.2.1.bkept
  refine RefE.bind_core (w := id) h₃ (fun M₃ hS₃ _ => ?_)
  have hB₁ := hB.keep hK₁ hbtop hsz
  have hB₂ := hB₁.keep hK₂ (by rw [hK₁.1]; exact hbtop) (by rw [hK₁.2.1]; exact hsz)
  have hB₃ := hB₂.keep hK₃ (by rw [hK₂.1, hK₁.1]; exact hbtop)
    (by rw [hK₂.2.1, hK₁.2.1]; exact hsz)
  have hL := lamsOut_ref p hp hab hcap dn vis fe eb d lo k ws hws (G := InferG p n) (n + 1) m₃ _ M₃ k
    (r₃.headD 0) hS₃ h₃.2.2.2 hB₃ (Nat.le_refl _) (by rw [hK₃.1, hK₂.1, hK₁.1]; exact hbtop)
  rcases hl : ilfE.loop1 p (n + 1) m₃ d lo (r₃.headD 0) k with e4 | ⟨cur, m₄⟩
  · rw [hl] at hL; exact hL
  rw [hl] at hL
  obtain ⟨y, a', hrun, hP⟩ := hL
  exact RefE.ret hrun hP

/-- **`infer_lams_leaf` refines `inferLamsLeaf`** at the knot (`ilf_ref`'s ok half). -/
@[refines ConRon.Arena.inferLamsLeaf ConRon.Arena.inferLamsOut]
theorem inferLamsLeaf_refines (p : Prog) (hp : InferLeafProg p) (hq : BindProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (hftop : fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat) (hB : BStkR s₀.mem lo k ws)
    (hbtop : lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "infer_lams_leaf" [mode, vis, d, t, k, fo, lo]
      (inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE))
      decH s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (ilfE_spec p hq.lamsLeaf (n + 1) s₀ mode vis d t k fo lo)
    (ilf_ref p hp hil hab hcap n hk F hF hn s₀ a₀ dn vis fe M eb mode d t k fo lo fvs ws hs ht hf hftop
      hB hbtop hws hdk)

/-! ## `infer_lams`: the peel loop -/

/-- The two pushes of a telescope step and the two tops. -/
def tPush (m : Mem) (fo lo k fv x : Word) : Mem :=
  (((m.set64 SPN (fo + k) fv).set64 BSTK (lo + k) x).set64 CTL 136 (fo + (k + 1))).set64 CTL 137
    (lo + (k + 1))

/-- The guards of a telescope step's pushes (the length checks, then `st64`'s bounds). -/
def tPushOK (m : Mem) (fo lo k : Word) : Prop :=
  ¬ m.len64 SPN ≤ fo + k ∧ ¬ m.len64 BSTK ≤ lo + k ∧ (fo + k).toNat < (m.arr64 SPN).size ∧
    (lo + k).toNat < (m.arr64 BSTK).size ∧ 137 < (m.arr64 CTL).size

instance (m : Mem) (fo lo k : Word) : Decidable (tPushOK m fo lo k) := by
  unfold tPushOK; infer_instance

/-- `CTL[137]` (the binder top) is a word of the control array (as `CoreS.ctl136`). -/
theorem CoreS.ctl137 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb) :
    137 < (m.arr64 CTL).size := by
  obtain ⟨mp, h⟩ := hS.memos.2.2.2.2.1
  unfold MemoRG MemoRV at h
  have := h.1
  simp only at this
  have e : (156 : Word).toNat = 156 := rfl
  omega

/-- The guards of a telescope step's pushes from the L code's length checks and `CoreS`. -/
theorem tPushOK_of {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m : Mem} {a : AState} {fo lo k : Word} (hS : CoreS dn m a vis fe M eb)
    (h1 : ¬ m.len64 SPN ≤ fo + k) (h2 : ¬ m.len64 BSTK ≤ lo + k) : tPushOK m fo lo k :=
  ⟨h1, h2, lt_of_not_len64_le hS.spn h1, lt_of_not_len64_le hS.bstk h2, hS.ctl137⟩

/-- **A telescope step's two pushes**: both slices grow by their word, both tops with them, the
spine stack below the slice is kept, the relation holds. -/
theorem tPush_step {dn : NIdx → Option ConLeche.Name} {m m₀ : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb fo lo k fv x : Word} {fvs : Array EIdx} {ws : Array Word}
    (hS : CoreS dn m a vis fe M eb) (hcap : (m.arr64 BSTK).size < 2 ^ 63)
    (hf : SpineR m fo k fvs) (hB : BStkR m lo k ws)
    (hb : ∀ j, j < fo → spW m j = spW m₀ j) (hsz : (m.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hok : tPushOK m fo lo k) (hfv : HW fv) :
    CoreS dn (tPush m fo lo k fv x) a vis fe M eb ∧
      SpineR (tPush m fo lo k fv x) fo (k + 1) (fvs.push (decE fv)) ∧
      spTop (tPush m fo lo k fv x) = fo + (k + 1) ∧
      BStkR (tPush m fo lo k fv x) lo (k + 1) (ws.push x) ∧
      bTop (tPush m fo lo k fv x) = lo + (k + 1) ∧
      (∀ j, j < fo → spW (tPush m fo lo k fv x) j = spW m₀ j) ∧
      ((tPush m fo lo k fv x).arr64 SPN).size = (m₀.arr64 SPN).size ∧
      ((tPush m fo lo k fv x).arr64 BSTK).size = (m.arr64 BSTK).size ∧
      (∀ j, j < lo → rdW ((tPush m fo lo k fv x).arr64 BSTK) j = rdW (m.arr64 BSTK) j) ∧
      PoolGrew m (tPush m fo lo k fv x) := by
  obtain ⟨-, -, h1, h2, h3⟩ := hok
  have hspn := hS.spn
  have hco := hf.bound
  have hadd : (fo + k).toNat = fo.toNat + k.toNat := addW _ _ (by omega)
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = m.set64 SPN (fo + k) fv := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m₂, m₂ = m₁.set64 BSTK (lo + k) x := ⟨_, rfl⟩
  obtain ⟨m₃, hm₃⟩ : ∃ m₃, m₃ = m₂.set64 CTL 136 (fo + (k + 1)) := ⟨_, rfl⟩
  have htp : tPush m fo lo k fv x = m₃.set64 CTL 137 (lo + (k + 1)) := by
    rw [hm₃, hm₂, hm₁]; rfl
  have e1 : m₂.arr64 SPN = m₁.arr64 SPN := by rw [hm₂]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have e2 : m₁.arr64 BSTK = m.arr64 BSTK := by rw [hm₁]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have eS : (tPush m fo lo k fv x).arr64 SPN = m₁.arr64 SPN := by
    rw [htp, Mem.arr64_set64_ne _ _ _ _ _ (by decide), hm₃, Mem.arr64_set64_ne _ _ _ _ _ (by decide), e1]
  have eB : (tPush m fo lo k fv x).arr64 BSTK = m₂.arr64 BSTK := by
    rw [htp, Mem.arr64_set64_ne _ _ _ _ _ (by decide), hm₃, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hS₁ : CoreS dn m₁ a vis fe M eb := by
    rw [hm₁]
    exact hS.frame_stk (MemFrame.set64 m SPN (by decide) _ fv) (by simp) (by simp)
  have hS₂ : CoreS dn m₂ a vis fe M eb := by
    rw [hm₂]; exact hS₁.frameS (MemFrame.set64 m₁ BSTK (by decide) _ x) (by simp [BSTK]) (by simp)
  have hS₃ : CoreS dn m₃ a vis fe M eb := by
    rw [hm₃]
    exact hS₂.frame_stk (MemFrame.setCtl m₂ 136 _) (by simp) (by simp)
  have hS₄ : CoreS dn (tPush m fo lo k fv x) a vis fe M eb := by
    rw [htp]; exact hS₃.frameS (MemFrame.setCtl m₃ 137 _) (by simp) (by simp)
  have h136 : (136 : Word).toNat < (m.arr64 CTL).size := Nat.lt_trans (by decide) h3
  have h137 : (137 : Word).toNat < (m.arr64 CTL).size := by simpa using h3
  have hfv' := (hf.push hspn (by rw [← hadd]; exact h1) fv hfv)
  rw [← hm₁] at hfv'
  have hsz1 : (m₁.arr64 SPN).size = (m.arr64 SPN).size := by rw [hm₁]; exact size_set64 _ _ _ _ _
  have hctl : ∀ {mm : Mem} (c v : Word), ((mm.set64 CTL c v).arr64 SPN) = mm.arr64 SPN := fun c v =>
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨hS₄, ⟨hfv'.size, by rw [eS]; exact hfv'.bound, fun i hi => by simp only [spW, eS]; exact hfv'.lt i hi,
    fun i hi => by simp only [spW, eS]; exact hfv'.get i hi⟩, ?_, ?_, ?_, ?_, by rw [eS, hsz1, hsz],
    by rw [eB, hm₂, size_set64, e2], ?_, ?_⟩
  · simp only [spTop]
    rw [htp, rdW_set64, ite_eq_right (fun h => absurd h.2.1 (by decide)), hm₃, rdW_set64, ite_eq_left ⟨rfl, rfl, by
                 rw [hm₂, hm₁, size_set64, size_set64]; exact h136⟩]
  · have hB₁ : BStkR m₁ lo k ws := hB.frame e2
    have hpush := hB₁.push (by rw [e2]; exact hcap) (by rw [e2]; exact h2) x
    rw [← hm₂] at hpush
    exact hpush.frame eB
  · simp only [bTop]
    rw [htp, rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [hm₃, hm₂, hm₁, size_set64, size_set64, size_set64]; exact h137⟩]
  · intro j hj
    simp only [spW, eS]
    rw [show rdW (m₁.arr64 SPN) j = spW m₁ j from rfl, hm₁, spW_set64_ne _ _ _ _ (fun h => by
      have := UInt64.lt_iff_toNat_lt.mp hj; rw [← h, hadd] at this; omega)]
    exact hb j hj
  · intro j hj
    have hBb := hB.bound
    have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
    rw [eB, hm₂, rdW_set64, ite_eq_right (fun h => by
            have := UInt64.lt_iff_toNat_lt.mp hj; rw [← h.2.1, haddl] at this; omega), e2]
  · have hfr : MemFrame [SPN, BSTK] [136, 137] m (tPush m fo lo k fv x) := by
      rw [htp, hm₃, hm₂, hm₁]
      exact ((((MemFrame.set64 m SPN (by decide) _ fv).mono (by simp) (by simp)).trans
        ((MemFrame.set64 _ BSTK (by decide) _ x).mono (by simp) (by simp))).trans
        ((MemFrame.setCtl _ 136 _).mono (by simp) (by simp))).trans
        ((MemFrame.setCtl _ 137 _).mono (by simp) (by simp))
    exact PoolGrew.of_frame hfr (by decide) (by decide)

/-- **What a telescope's run gives** from an inner memory, besides the twin's result `y` and final
state `a'`: the result decoded and valid, the relation at maps kept from `M`, the spine stack below
the telescope's `fvs` slice and the binder stack below its slice kept from the entry memory `m₀`. -/
structure TelP (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (m₀ : Mem) (fo lo : Word) (v : List Word × Mem) (y : EIdx) (a' : AState) : Prop where
  res : y = decH v.1
  valid : ResH v.1
  rel : ∃ M', CoreS dn v.2 a' vis fe M' eb ∧ KeptAll M M' eb
  below : ∀ j, j < fo → spW v.2 j = spW m₀ j
  size : (v.2.arr64 SPN).size = (m₀.arr64 SPN).size
  bbelow : ∀ j, j < lo → rdW (v.2.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j
  bsize : (v.2.arr64 BSTK).size = (m₀.arr64 BSTK).size
  pool : PoolGrew m₀ v.2

theorem TelP.keep {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M M' : ModeMaps}
    {eb : Word} {m₀ : Mem} {fo lo : Word} {v : List Word × Mem} {y : EIdx} {a' : AState}
    (hK : KeptAll M M' eb) (h : TelP dn vis fe M' eb m₀ fo lo v y a') : TelP dn vis fe M eb m₀ fo lo v y a' :=
  { h with rel := let ⟨M'', hS, hK'⟩ := h.rel; ⟨M'', hS, hK.trans hK'⟩ }

/-- `infer_lams_leaf` at every L fuel up to `n + 1`. -/
theorem inferLamsLeaf_any (p : Prog) (hp : InferLeafProg p) (hq : BindProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap) :
    ∀ n, KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs →
    fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat → BStkR s₀.mem lo k ws →
    lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
    d.toNat + k.toNat < 2 ^ 64 →
    CoreSpec p n "infer_lams_leaf" [mode, vis, d, t, k, fo, lo]
      (inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE))
      decH s₀ a₀ dn vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, t, k, fo, lo, fvs, ws, hs, ht, hf,
      hftop, hB, hbtop, hws, hdk =>
      inferLamsLeaf_refines p hp hq hil hab hcap n (hk.mono (by omega)) F (by omega) (by omega)
        s₀ a₀ dn vis fe M eb mode d t k fo lo fvs ws hs ht hf hftop hB hbtop hws hdk

/-- `infer_lams_leaf`'s error claim at every L fuel up to `n + 1` (`ilf_ref`'s error half). -/
theorem inferLamsLeaf_anyE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap) :
    ∀ n, KnotUpTo p n → InferG p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs →
    fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat → BStkR s₀.mem lo k ws →
    lo.toNat + k.toNat ≤ (bTop s₀.mem).toNat → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
    d.toNat + k.toNat < 2 ^ 64 →
    CoreSpecE p n "infer_lams_leaf" [mode, vis, d, t, k, fo, lo]
      (inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE)) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hG, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, t, k, fo, lo, fvs, ws, hs, ht, hf,
      hftop, hB, hbtop, hws, hdk =>
      RefE.coreSpecE (ilfE_spec p hq.lamsLeaf (n + 1) s₀ mode vis d t k fo lo) hG.nv (hG.mono (by omega))
        (ilf_ref p hp hil hab hcap n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb
          mode d t k fo lo fvs ws hs ht hf hftop hB hbtop hws hdk)

/-- **The λ peel loop with its leaf refines `inferLams`, both outcomes**, by induction on the loop
fuel: a domain's type and its `whnf` (the slots' errors), a domain type that is no sort (a reject),
the leaf's errors. -/
theorem lamsLoop_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap)
    (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hFN : N ≤ F) (hN : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo lo eb : Word)
    (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) :
    ∀ j, j ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (peel t k ty : Word) (fvs : Array EIdx)
      (ws : Array Word),
      CoreS dn m a vis fe M eb → HW t → SpineR m fo k fvs → spTop m = fo + k →
      BStkR m lo k ws → bTop m = lo + k → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
      d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      (∀ j, j < fo → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      (∀ j, j < lo → rdW (m.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) →
      (m.arr64 BSTK).size = (m₀.arr64 BSTK).size → PoolGrew m₀ m →
      RefE (InferG p N) (ilsE.k_loop1 p N mode vis d fo lo (ilsE.loop1 p j m mode vis d peel t k fo lo ty))
        (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t) k.toNat fvs
          (ws.map decE)) a (TelP dn vis fe M eb m₀ fo lo) := by
  intro j
  induction j with
  | zero =>
    intro _ m a M peel t k ty fvs ws _ _ _ _ _ _ _ _ _ _ _ _ _
    rw [ilsE.loop1.eq_1]; exact RefE.of_cls0 rfl
  | succ j ih =>
    intro hjN m a M peel t k ty fvs ws hS ht hf htop hB hbt hws hdk hb0 hsz hbb0 hbsz0 hpg0
    rw [ilsE.loop1.eq_2]
    have hspn := hS.spn
    have hcp := hcap _ _ _ _ _ _ _ hS
    have hfb := hf.bound
    have hBb := hB.bound
    have haddf : (fo + k).toNat = fo.toNat + k.toNat := addW _ _ (by omega)
    have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
    have haddd : (d + k).toNat = d.toNat + k.toNat := addW _ _ (by omega)
    have hftop : fo.toNat + k.toNat ≤ (spTop m).toNat := by rw [htop, haddf]; exact Nat.le_refl _
    have hbtop : lo.toNat + k.toNat ≤ (bTop m).toNat := by rw [hbt, haddl]; exact Nat.le_refl _
    by_cases hc : peel ≠ 0 ∧ t >>> 28 = 5
    · rw [ite_eq_left hc]
      obtain ⟨hp0, ht5⟩ := hc
      by_cases hc1 : tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
      · rw [ite_eq_left hc1]; exact RefE.of_cls0 rfl
      rw [ite_eq_right hc1]
      by_cases hc2 : tcnt m LAM (tierW t) ≤ idxW t
      · rw [ite_eq_left hc2]; exact RefE.of_cls0 rfl
      rw [ite_eq_right hc2]
      have hv : viewOK m t LAM := ⟨hc1, UInt64.not_le.mp hc2⟩
      obtain ⟨-, hty, hbody⟩ := view_lam m a hS.arena.1 t ht hv ht5
      have hvb := viewBind_lam m a hS.arena.1 t ht hv ht5
      obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
        ⟨peel.toNat - 1, by have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
      have hlam : ((decE t).tag != ETag.lam) = false := by
        rw [bne_eq_false_iff_eq, ← beq_iff_eq, decE_tag_lam_beq t ht]; simp [ht5]
      rw [hp', inferLams]
      simp only [hlam, Bool.false_eq_true, ↓reduceIte]
      rw [← haddd]
      refine RefE.bind_right (by rw [viewBind_run', hvb]) ?_
      dsimp only
      have h0 : (0 : Word).toNat = 0 := rfl
      rcases h1 : callW p j "inst_list" [tfld m LAM (tierW t) (idxW t) 0, fo, k, 0] m with _ | ⟨r₁, m₁⟩
      · rw [liftE_none, ilsE.k_inst_list.eq_1]; exact RefE.of_cls0 (by simp)
      rw [liftE_some, ilsE.k_inst_list.eq_2]
      obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW
        (hil j ⟨m, Locals.init []⟩ a dn vis fe M eb _ fo k 0 fvs hS hty hf hftop) h1
      rw [h0] at hok1 hres1 hS₁
      have hB₁ := hSt₁.bstk
      refine RefE.bind_right (AM.run_of_ok _ _ hok1) ?_
      rw [hres1]
      have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hmode, heb⟩
      rcases h2 : callE p j "infer" [mode, vis, d + k, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
      · rw [ilsE.k_infer.eq_1]
        exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
          ((hG.knot j (by omega)).infer F _ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0) (by omega)
            (by omega) hs₁ hrw1) h2
      rw [ilsE.k_infer.eq_2]
      obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW ((hk j (by omega)).infer F
        ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0) (by omega) (by omega) hs₁ hrw1)
        (callW_of_callE h2)
      have hB₂ := hSt₂.bstk
      refine RefE.bind_right (AM.run_of_ok _ _ hok2) ?_
      erw [hres2]
      have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hmode, heb⟩
      rcases h3 : callE p j "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with e3 | ⟨r₃, m₃⟩
      · rw [ilsE.k_whnf.eq_1]
        exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
          ((hG.knot j (by omega)).whnf F _ _ dn vis fe M₂ eb mode (d + k) (r₂.headD 0) (by omega)
            (by omega) hs₂ hrw2) h3
      rw [ilsE.k_whnf.eq_2]
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
      have hsort : ((decH r₃).tag == ETag.sort) = true := tag_sort_beq _ hrw3 (by simpa using g1)
      simp only [hsort, ↓reduceIte, internFVarE]
      rcases h4 : callW p j "intern_fvar" [d + k, r₁.headD 0] m₃ with _ | ⟨r₄, m₄⟩
      · rw [liftE_none, ilsE.k_intern_fvar.eq_1]; exact RefE.of_cls0 (by simp)
      rw [liftE_some, ilsE.k_intern_fvar.eq_2]
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
      have hws' : ∀ (i : Nat) (h : i < (ws.push (r₁.headD 0)).size), HW (ws.push (r₁.headD 0))[i] := by
        intro i hi
        rw [Array.getElem_push]
        split
        · exact hws i _
        · exact hrw1
      have hpeel1 : (peel - 1).toNat = peel.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le]; · rfl
        rw [UInt64.le_iff_toNat_le]; simp
        have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega
      have hk1 : (k + 1).toNat = k.toNat + 1 := addW _ _ (by simp; omega)
      have hih := ih (by omega) (tPush m₄ fo lo k (r₄.headD 0) (r₁.headD 0)) _ M₄ (peel - 1) _ (k + 1)
        (tfld m LAM (tierW t) (idxW t) 0) _ _ hS' hbody hf' htop' hB' hbt' hws'
        (by rw [hk1, hpeel1]; omega) hb' hsz' (fun i hi => (hbbT i hi).trans (hbb₄ i hi))
        (hbszT.trans (hBK.2.1.trans hbsz0)) ((hpg0.trans hSt14.pool).trans hpgT)
      rw [hk1, hpeel1, hp', Nat.add_sub_cancel, Array.map_push] at hih
      exact hih.mono fun _ _ _ h => h.keep (hK₁.trans (hK₂.trans (hK₃.trans hK₄)))
    · -- the exit: the leaf
      rw [ite_eq_right hc]
      have hT : (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t) k.toNat fvs
          (ws.map decE)).run a = (inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t)
          k.toNat fvs (ws.map decE)).run a := by
        by_cases hp0 : peel = 0
        · subst hp0; rfl
        · have ht5 : ¬ t >>> 28 = 5 := fun h => hc ⟨hp0, h⟩
          obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
            ⟨peel.toNat - 1, by
              have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
          have hlam : ((decE t).tag != ETag.lam) = true := by
            rw [bne_iff_ne, ne_eq, ← beq_iff_eq, decE_tag_lam_beq t ht]; simp [ht5]
          rw [hp', inferLams]
          simp only [hlam, ↓reduceIte]
      refine RefE.of_run_eq hT ?_
      simp only [ilsE.k_loop1]
      rcases hc' : callE p N "infer_lams_leaf" [mode, vis, d, t, k, fo, lo] m with e | ⟨r, mF⟩
      · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
          (inferLamsLeaf_anyE p hp hq hil hab hcap N hk hG F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb
            mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩ ht hf hftop hB hbtop hws (by omega)) hc'
      obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := CoreSpec.of_callW
        (inferLamsLeaf_any p hp hq hil hab hcap N hk F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb
          mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩ ht hf hftop hB hbtop hws (by omega))
        (callW_of_callE hc')
      refine RefE.ret (AM.run_of_ok _ _ hok) ⟨hres, hrw, ⟨M', hS', hK'⟩, fun i hi => ?_,
        hSt'.size.trans hsz, fun i hi => ?_, hSt'.bstk.2.1.trans hbsz0, hpg0.trans hSt'.pool⟩
      · have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt'.below i hi').trans (hb0 i hi)
      · have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt'.bstk.2.2 i hi').trans (hbb0 i hi)

/-- **`infer_lams` refines `inferLams`, both outcomes**, from a telescope state (`fvs` at the spine
top, `stk` at the binder top), up to the tops it leaves raised (`TelP`). -/
theorem ils_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (htop : spTop s₀.mem = fo + k) (hB : BStkR s₀.mem lo k ws) (hbt : bTop s₀.mem = lo + k)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64)
    (hb0 : ∀ j, j < fo → spW s₀.mem j = spW m₀ j) (hsz : (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbb0 : ∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j)
    (hbsz0 : (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size) (hpg0 : PoolGrew m₀ s₀.mem) :
    RefE (InferG p n) (ilsE p (n + 1) s₀.mem mode vis d peel t k fo lo)
      (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decE)) a₀ (TelP dn vis fe M eb m₀ fo lo) := by
  simp only [ilsE]
  exact lamsLoop_ref p hp hq hb hil hab hcap n hk F hF hn dn vis fe mode d fo lo eb hs.mode4 hs.eb_mode
    m₀ (n + 1) (Nat.le_refl _) s₀.mem a₀ M peel t k 0 fvs ws hs.rel ht hf htop hB hbt hws hdk hb0 hsz
    hbb0 hbsz0 hpg0

/-- **`infer_lams` refines `inferLams`** (`ils_ref`'s ok half, as a triple at every L fuel up to
`n + 1`). -/
@[refines ConRon.Arena.inferLams]
theorem inferLams_tel (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (htop : spTop s₀.mem = fo + k) (hB : BStkR s₀.mem lo k ws) (hbt : bTop s₀.mem = lo + k)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64)
    (hb0 : ∀ j, j < fo → spW s₀.mem j = spW m₀ j) (hsz : (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbb0 : ∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j)
    (hbsz0 : (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size) (hpg0 : PoolGrew m₀ s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_lams" [mode, vis, d, peel, t, k, fo, lo]
    ⦃fun r s' => LocEq s' s₀ ∧ ∃ y a', (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat
      (decE t) k.toNat fvs (ws.map decE)).run a₀ = .ok (y, a') ∧
      TelP dn vis fe M eb m₀ fo lo (r, s'.mem) y a'; ⊤⦄ :=
  RefE.triple (ilsE_spec p hq.lams (n + 1) s₀ mode vis d peel t k fo lo)
    (ils_ref p hp hq hb hil hab hcap n hk F hF hn s₀ a₀ dn vis fe M eb mode d peel t k fo lo fvs ws m₀ hs
      ht hf htop hB hbt hws hdk hb0 hsz hbb0 hbsz0 hpg0)

/-- `infer_lams`' error claim at every L fuel up to `n + 1` (`ils_ref`'s error half). -/
theorem inferLams_anyE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap) :
    ∀ n, KnotUpTo p n → InferG p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs → spTop s₀.mem = fo + k →
    BStkR s₀.mem lo k ws → bTop s₀.mem = lo + k → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
    d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
    (∀ j, j < fo → spW s₀.mem j = spW m₀ j) → (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size →
    (∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) →
    (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size → PoolGrew m₀ s₀.mem →
    CoreSpecE p n "infer_lams" [mode, vis, d, peel, t, k, fo, lo]
      (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decE)) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hG, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, peel, t, k, fo, lo, fvs, ws, m₀, hs,
      ht, hf, htop, hB, hbt, hws, hdk, hb0, hsz, hbb0, hbsz0, hpg0 =>
      RefE.coreSpecE (ilsE_spec p hq.lams (n + 1) s₀ mode vis d peel t k fo lo) hG.nv (hG.mono (by omega))
        (ils_ref p hp hq hb hil hab hcap n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe
          M eb mode d peel t k fo lo fvs ws m₀ hs ht hf htop hB hbt hws hdk hb0 hsz hbb0 hbsz0 hpg0)

/-! ## `infer_lam` -/

/-- `inferBody`'s `.lam` arm is `inferLam`. -/
@[refines_part ConRon.Arena.inferBody "lam"]
theorem inferBody_lam (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e : EIdx) (a : AState)
    (ty body : EIdx) (hv : a.store.view e = some (.lam ty body)) :
    (inferBody r fe d e).run a = (inferLam r d ty body).run a := by
  simp only [inferBody, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]

/-- The two tops put back after a telescope. -/
theorem tops_restore {dn : NIdx → Option ConLeche.Name} {m₀ m₃ m₄ : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m₄ a vis fe M eb)
    (hk3 : StackKept m₀ m₃) (hb : ∀ j, j < spTop m₃ → spW m₄ j = spW m₃ j)
    (hsz : (m₄.arr64 SPN).size = (m₃.arr64 SPN).size)
    (hbb : ∀ j, j < bTop m₃ → rdW (m₄.arr64 BSTK) j = rdW (m₃.arr64 BSTK) j)
    (hbsz : (m₄.arr64 BSTK).size = (m₃.arr64 BSTK).size) (hpg : PoolGrew m₃ m₄)
    (h137 : 137 < (m₄.arr64 CTL).size) :
    CoreS dn ((m₄.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)).set64 CTL 137 (rdW (m₃.arr64 CTL) 137)) a
      vis fe M eb ∧
    StackKept m₀ ((m₄.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)).set64 CTL 137 (rdW (m₃.arr64 CTL) 137)) := by
  have h136 : (136 : Word).toNat < (m₄.arr64 CTL).size := Nat.lt_trans (by decide) h137
  have hS₁ := hS.frame_stk (MemFrame.setCtl m₄ 136 (rdW (m₃.arr64 CTL) 136)) (by simp) (by simp)
  have hS₂ := hS₁.frameS (MemFrame.setCtl _ 137 (rdW (m₃.arr64 CTL) 137)) (by simp) (by simp)
  refine ⟨hS₂, hk3.trans ?_⟩
  have hfr : MemFrame [] [136, 137] m₄
      ((m₄.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)).set64 CTL 137 (rdW (m₃.arr64 CTL) 137)) :=
    ((MemFrame.setCtl m₄ 136 _).mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ 137 _).mono (by simp) (by simp))
  have eS := hfr.arr SPN (by simp) (by decide)
  have eB := hfr.arr BSTK (by simp) (by decide)
  refine ⟨?_, by rw [eS, hsz], fun j hj => by simp only [spW, eS]; exact hb j hj,
    ⟨?_, by rw [eB, hbsz], fun j hj => by rw [eB]; exact hbb j hj⟩,
    hpg.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩
  · unfold spTop
    rw [rdW_set64, ite_eq_right (fun h => absurd h.2.1 (by decide)), rdW_set64, ite_eq_left ⟨rfl, rfl, h136⟩]
  · unfold bTop
    rw [rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [size_set64]; exact h137⟩]

/-- **`infer_lam` refines `inferLam`, both outcomes**, at the knot (the `.lam` clause of
`inferBody`): the domain's type and its `whnf` (the slots' errors), a domain type that is no sort (a
reject), the telescope's (`infer_lams`). -/
theorem ilm_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    RefE (InferG p n) (ilmE p (n + 1) s₀.mem mode vis d ty body)
      (inferLam (coreKnot (decMode mode) fe id F) d.toNat (decE ty) (decE body)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  simp only [ilmE]
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
  simp only [inferLam]
  rcases h1 : callE p n "infer" [mode, vis, d, ty] s₀.mem with e1 | ⟨r₁, m₁⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE ((hG.knot n (Nat.le_refl _)).infer F s₀ a₀ dn vis
      fe M eb mode d ty hF hn hs hty) h1
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW (hK.infer F s₀ a₀ dn vis fe M eb
    mode d ty hF hn hs hty) (callW_of_callE h1)
  refine RefE.bind_right (AM.run_of_ok _ _ hok1) ?_
  simp only [ilmE.k_infer]
  erw [hres1]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  rcases h2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with e2 | ⟨r₂, m₂⟩
  · exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).whnf F _ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn hs₁ hrw1) h2
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩
    _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn hs₁ hrw1) (callW_of_callE h2)
  refine RefE.bind_right (AM.run_of_ok _ _ hok2) ?_
  simp only [ilmE.k_whnf]
  erw [hres2]
  by_cases g1 : r₂.headD 0 >>> 28 ≠ 2
  · rw [ite_eq_left g1]
    simp only [show decH r₂ = decE (r₂.headD 0) from rfl, tag_sort_ne _ hrw2 g1, Bool.false_eq_true,
      ↓reduceIte]
    exact fun _ => ErrClaim.fail _ _ rfl
  rw [ite_eq_right g1]
  have hsort : ((decH r₂).tag == ETag.sort) = true := tag_sort_beq _ hrw2 (by simpa using g1)
  simp only [hsort, ↓reduceIte, internFVarE]
  rcases h3 : callW p n "intern_fvar" [d, ty] m₂ with _ | ⟨r₃, m₃⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s₃, hs₃, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internFVar_spec p hb.fvf hb.fvp hb.fvi n _ d ty) h3
  rw [hs₃] at hfv
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := internFVar_core hS₂ d ty hty r₃ hfv
  refine RefE.bind_right (AM.run_of_ok _ _ hok3) ?_
  simp only [ilmE.k_intern_fvar]
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
    g2 hrw3
  have e01 : (0 : Word) + 1 = 1 := rfl
  rw [e01] at hf' htop' hB' hbt'
  rw [show (((m₃.set64 SPN so (r₃.headD 0)).set64 BSTK lo ty).set64 CTL 136 (so + 1)).set64 CTL 137
    (lo + 1) = tPush m₃ so lo 0 (r₃.headD 0) ty by simp [tPush]]
  have hpf : peelFuel = (16777216 : Word).toNat := rfl
  rw [hpf, show (1 : Nat) = (1 : Word).toNat from rfl, show #[decE ty] = ((#[] : Array Word).push ty).map decE
    by simp, show #[decH r₃] = (#[] : Array EIdx).push (decE (r₃.headD 0)) from rfl]
  rcases h4 : callE p n "infer_lams" [mode, vis, d, 16777216, body, 1, so, lo]
      (tPush m₃ so lo 0 (r₃.headD 0) ty) with e4 | ⟨r₄, m₄⟩
  · exact fun hG => CoreSpecE.of_callE (s₀ := ⟨_, Locals.init []⟩) (inferLams_anyE p hp hq hb hil hab hcap
      n hk hG F hF hn _ _ dn vis fe M₃ eb mode d 16777216 body 1 so lo _ _ m₃ ⟨hS', hs.mode4, hs.eb_mode⟩
      hbody hf' htop' hB' hbt' (by intro i hi; simp at hi; subst hi; simpa using hty) (by simp; omega) hb'
      hsz' hbbT hbszT hpgT) h4
  obtain _ | n' := n
  · obtain ⟨e', he', -⟩ := callE_zero p "infer_lams" [mode, vis, d, 16777216, body, 1, so, lo]
      (tPush m₃ so lo 0 (r₃.headD 0) ty)
    rw [h4] at he'; cases he'
  obtain ⟨t₄, ht₄, -, y, a', hrun4, hT⟩ := triple_of_callE (s₀ := ⟨_, Locals.init []⟩)
    (inferLams_tel p hp hq hb hil hab hcap n' (hk.mono (by omega)) F (by omega) (by omega) _ _ dn
      vis fe M₃ eb mode d 16777216 body 1 so lo _ _ m₃ ⟨hS', hs.mode4, hs.eb_mode⟩ hbody hf' htop' hB'
      hbt' (by intro i hi; simp at hi; subst hi; simpa using hty) (by simp; omega) hb' hsz' hbbT hbszT
      hpgT) h4
  rw [ht₄] at hT
  simp only [ilmE.k_infer_lams]
  obtain ⟨M', hS₄, hK₄⟩ := hT.rel
  have htop3 : spTop m₃ = so := hso
  obtain ⟨hSF, hkF⟩ := tops_restore (m₀ := s₀.mem) hS₄ hSt13
    (fun j hj => hT.below j (htop3 ▸ hj)) hT.size (fun j hj => hT.bbelow j (by rw [← hlo]; exact hj))
    hT.bsize hT.pool hS₄.ctl137
  rw [hso, hlo] at hSF hkF
  exact RefE.ret hrun4 ⟨⟨M', hSF, hK₁.trans (hK₂.trans (hK₃.trans hK₄)), hkF⟩, hT.res, hT.valid⟩

/-- **`infer_lam` refines `inferLam`** at the knot (`ilm_ref`'s ok half). -/
@[refines ConRon.Arena.inferLam]
theorem inferLam_refines (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpec p (n + 1) "infer_lam" [mode, vis, d, ty, body]
      (inferLam (coreKnot (decMode mode) fe id F) d.toNat (decE ty) (decE body)) decH s₀ a₀ dn vis fe
        M eb :=
  RefE.coreSpec (ilmE_spec p hq.lam (n + 1) s₀ mode vis d ty body)
    (ilm_ref p hp hq hb hil hab hcap n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty body hs hty hbody)

end L.Arena
