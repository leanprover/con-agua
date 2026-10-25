import ConAgua.Arena.InferBodySpineF

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
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

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
  · rw [Array.getElem_push, dif_pos (by rw [h.size]; exact hi'), h.get i (by rw [h.size]; exact hi')]
    rw [if_neg]
    rintro ⟨-, hco, -⟩
    have := congrArg UInt64.toNat hco
    rw [hidx i (by omega), hoc] at this
    omega
  · have hieq : i = k.toNat := hi'
    subst hieq
    rw [Array.getElem_push, dif_neg (by omega), heqv, if_pos ⟨rfl, rfl, hb⟩]

theorem BStkR.frame {m m' : Mem} {lo k : Word} {ws : Array Word} (h : BStkR m lo k ws)
    (hb : m'.arr64 BSTK = m.arr64 BSTK) : BStkR m' lo k ws :=
  ⟨h.size, hb ▸ h.bound, fun i hi => by rw [hb]; exact h.get i hi⟩

/-- **The binder stack's capacity**: under `CoreS` it is below `2^63` words (as `CoreS.spn` for the
spine stack; a field `CoreS` lacks, assumed here). -/
def BStkCap : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb → (m.arr64 BSTK).size < 2 ^ 63

/-! ## `infer_lams_leaf`: the outward rebuild as a named block -/

/-- The outward loop of `inferLamsLeafL` (Infer.lean), named for its spec. -/
def lamsOutW : Stmt := lblk (mode, vis, d, t, k, fo, lo, ob, bt, cur, n, ta) {
  while n != 0 {
    n -= 1;
    ta := call ar_entry(BSTK.u64[lo + n], d, n, 0);
    cur := call mk_forall(ta, cur)
  }
}

/-- `inferLamsLeafL`, with its outward loop spliced from `lamsOutW`. -/
-- con-ron: none — `inferLamsLeafL` itself (`rfl`), its loop a named block for the proof
def inferLamsLeafL' : FunDecl := lfn (mode, vis, d, t, k, fo, lo) locals (ob, bt, cur, n, ta) {
  ob := call inst_list(t, fo, k, 0);
  bt := call infer(mode, vis, d + k, ob);
  cur := call ar_entry(bt, d, k, 0);
  n := k;
  ⟪lamsOutW⟫;
  return cur
}

theorem inferLamsLeafL_eq : inferLamsLeafL = inferLamsLeafL' := rfl

/-- **The model of the outward rebuild** at L fuel `k`. -/
def lamsOut (p : Prog) : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, d, lo, n, cur =>
    if n ≠ 0 then
      match callW p k "ar_entry" [rdW (m.arr64 BSTK) (lo + (n - 1)), d, n - 1, 0] m with
      | none => none
      | some (r₁, m₁) =>
        match callW p k "mk_forall" [r₁.headD 0, cur] m₁ with
        | none => none
        | some (r₂, m₂) => lamsOut p k m₂ d lo (n - 1) (r₂.headD 0)
    else some (cur, m)

theorem lamsOutW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n lamsOutW
    ⦃fun r s' => r = .normal ∧
      lamsOut p n s₀.mem (s₀.loc 2) (s₀.loc 6) (s₀.loc 10) (s₀.loc 9) = some (s'.loc 9, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lamsOutW) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, ih,
      callW_spec p n "ar_entry", callW_spec p n "mk_forall"] <;>
    simp_all [lamsOut, Cmp.eval, LocEq, BinOp.eval, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil]

/-- **The model of `infer_lams_leaf`.** -/
def lamsLeafK (p : Prog) (n : Nat) (m : Mem) (mode vis d t k fo lo : Word) : Option (Word × Mem) :=
  match callW p n "inst_list" [t, fo, k, 0] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
    | none => none
    | some (r₂, m₂) =>
      match callW p n "ar_entry" [r₂.headD 0, d, k, 0] m₂ with
      | none => none
      | some (r₃, m₃) => lamsOut p (n + 1) m₃ d lo k (r₃.headD 0)

/-- What the telescope specs need of a program. -/
structure BindProg (p : Prog) : Prop where
  lamsLeaf : p.lookup "infer_lams_leaf" = some inferLamsLeafL
  lams : p.lookup "infer_lams" = some inferLamsL
  lam : p.lookup "infer_lam" = some inferLamL
  pisLeaf : p.lookup "infer_pis_leaf" = some inferPisLeafL
  pis : p.lookup "infer_pis" = some inferPisL
  fa : p.lookup "infer_forall" = some inferForallL

theorem inferLamsLeaf_spec (p : Prog) (hq : BindProg p) (n : Nat) (s₀ : St)
    (mode vis d t k fo lo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_lams_leaf" [mode, vis, d, t, k, fo, lo]
    ⦃fun r s' => LocEq s' s₀ ∧ lamsLeafK p n s₀.mem mode vis d t k fo lo = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.lamsLeaf, inferLamsLeafL_eq]
  simp only [callFn, inferLamsLeafL']
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (lamsOutW_spec p (n + 1) s), callW_spec p n "inst_list",
      callW_spec p n "infer", callW_spec p n "ar_entry"] <;>
  simp_all [lamsLeafK, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

/-! ## `infer_lams_leaf` refines `inferLamsLeaf` -/

theorem BKept.of_mkForall {m m' : Mem} {t b r : Word} (h : mkForallW m t b = some (r, m')) :
    BKept m m' :=
  BKept.of_frame (mkForallW_frame h) (by simp [FADER, FAREC, FASLOT, BSTK]) (by simp)

theorem sub1_toNat {n : Word} (h : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have : n.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  rw [UInt64.toNat_sub_of_le]; · rfl
  rw [UInt64.le_iff_toNat_le]; simp; omega

/-- **The outward rebuild refines `inferLamsOut`** (by induction on the loop fuel), and keeps the
binder stack. -/
theorem lamsOut_ref (p : Prog) (hp : InferLeafProg p) (hab : AbstractRangeOK p)
    (hcap : BStkCap) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (eb d lo K : Word) (ws : Array Word) (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) :
    ∀ k (m : Mem) (a : AState) (M : ModeMaps) (n cur : Word),
      CoreS dn m a vis fe M eb → HW cur → BStkR m lo K ws → n.toNat ≤ K.toNat →
      lo.toNat + K.toNat ≤ (bTop m).toNat →
      ∀ w mF, lamsOut p k m d lo n cur = some (w, mF) →
      CoreRef (inferLamsOut d.toNat (ws.map decE) n.toNat (decE cur)) a decH dn m vis fe M eb [w] mF ∧
        BKept m mF := by
  intro k
  induction k with
  | zero => intro m a M n cur _ _ _ _ _ w mF h; simp [lamsOut] at h
  | succ k ih =>
    intro m a M n cur hS hc hB hnK htop w mF h
    by_cases hn : n = 0
    · subst hn
      simp only [lamsOut, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hrun : (inferLamsOut d.toNat (ws.map decE) (0 : Word).toNat (decE cur)).run a =
          .ok (decE cur, a) := by rw [inferLamsOut]; rfl
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨⟨hok, by rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, by rw [hres]; rfl,
        hc⟩, BKept.refl _⟩
    simp only [lamsOut, hn, ne_eq, not_false_eq_true, ↓reduceIte] at h
    have hn1 := sub1_toNat hn
    have hn0' : n.toNat ≠ 0 := fun h' => hn (UInt64.toNat_inj.mp (by simpa using h'))
    have hjK : (n - 1).toNat < ws.size := by rw [hB.size, hn1]; omega
    have hwsj : ws[(n - 1).toNat] = rdW (m.arr64 BSTK) (lo + (n - 1)) := by
      rw [hB.get _ hjK]; simp
    rcases h1 : callW p k "ar_entry" [rdW (m.arr64 BSTK) (lo + (n - 1)), d, n - 1, 0] m with _ | ⟨r₁, m₁⟩
      <;> simp only [h1, reduceCtorEq] at h
    rcases h2 : callW p k "mk_forall" [r₁.headD 0, cur] m₁ with _ | ⟨r₂, m₂⟩
      <;> simp only [h2, reduceCtorEq] at h
    have hwj : HW (rdW (m.arr64 BSTK) (lo + (n - 1))) := hwsj ▸ hws _ hjK
    have h₁ := CoreSpec.of_callW (hab k ⟨m, Locals.init []⟩ a dn vis fe M eb _ d (n - 1) 0 hS hwj) h1
    have hK₁ := h₁.2.1.bkept
    obtain ⟨s₂, hs₂, -, hmk⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (mkForall_spec p hp.derb hp.faf hp.fap hp.fai hp.mkfa k _ (r₁.headD 0) cur) h2
    rw [hs₂] at hmk
    have hK₂ := BKept.of_mkForall hmk
    have hsz := hcap _ _ _ _ _ _ _ hS
    have hB₂ : BStkR m₂ lo K ws := (hB.keep hK₁ htop hsz).keep hK₂ (by rw [hK₁.1]; exact htop)
      (by rw [hK₁.2.1]; exact hsz)
    have htop₂ : lo.toNat + K.toNat ≤ (bTop m₂).toNat := by rw [hK₂.1, hK₁.1]; exact htop
    have hT : inferLamsOut d.toNat (ws.map decE) n.toNat (decE cur) =
        (abstractRangeFast coreWalkFuel (decE (rdW (m.arr64 BSTK) (lo + (n - 1)))) d.toNat
          (n - 1).toNat (0 : Word).toNat >>= fun tyAbs => internForallEE tyAbs (decE cur) >>= fun nd =>
          inferLamsOut d.toNat (ws.map decE) (n - 1).toNat nd) := by
      rw [inferLamsOut]
      have hn0 : n.toNat ≠ 0 := fun h' => hn (UInt64.toNat_inj.mp (by simpa using h'))
      simp only [hn0, ↓reduceIte, hn1]
      rw [show (ws.map decE)[n.toNat - 1]! = decE (rdW (m.arr64 BSTK) (lo + (n - 1))) by
        rw [← hn1, getElem!_pos (ws.map decE) _ (by simpa using hjK), Array.getElem_map, hwsj]]
      rfl
    refine ⟨?_, hK₁.trans (hK₂.trans ?_)⟩
    · rw [hT]
      refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
      refine coreRef_bind (mkForall_core hS₁ (r₁.headD 0) cur r₂ hmk) (fun M₂ hS₂ => ?_)
      exact (ih m₂ _ M₂ (n - 1) (r₂.headD 0) hS₂ (mkForallW_hw _ _ hS₁.arena _ _ _ _ hmk) hB₂
        (by omega) htop₂ w mF h).1
    · obtain ⟨M₁, hS₁, -⟩ := h₁.2.1
      have hm := mkForall_core hS₁ (r₁.headD 0) cur r₂ hmk
      obtain ⟨M₂, hS₂, -⟩ := hm.2.1
      exact (ih m₂ _ M₂ (n - 1) (r₂.headD 0) hS₂
        (mkForallW_hw _ _ hS₁.arena _ _ _ _ hmk) hB₂ (by omega) htop₂ w mF h).2

/-- **`infer_lams_leaf` refines `inferLamsLeaf`** at the knot: `fvs` the stack slice `(fo, k)` at
the top, `stk` the binder-stack slice `(lo, k)` below the binder top. -/
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
      decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferLamsLeaf_spec p hq n s₀ mode vis d t k fo lo)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold lamsLeafK at hW
  rcases h1 : callW p n "inst_list" [t, fo, k, 0] s.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [h1, reduceCtorEq] at hW
  rcases h2 : callW p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with _ | ⟨r₂, m₂⟩
    <;> simp only [h2, reduceCtorEq] at hW
  rcases h3 : callW p n "ar_entry" [r₂.headD 0, d, k, 0] m₂ with _ | ⟨r₃, m₃⟩
    <;> simp only [h3, reduceCtorEq] at hW
  have hsz := hcap _ _ _ _ _ _ _ hS
  have h₁ := CoreSpec.of_callW (hil n s a₀ dn vis fe M eb t fo k 0 fvs hS ht hf hftop) h1
  have hK₁ := h₁.2.1.bkept
  have hdk' : (d + k).toNat = d.toNat + k.toNat := addW _ _ hdk
  have h0 : (0 : Word).toNat = 0 := rfl
  have hT : inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE) =
      (instantiateListFast coreWalkFuel (decE t) fvs (0 : Word).toNat >>= fun ob =>
        (coreKnot (decMode mode) fe id F).infer (d + k).toNat ob >>= fun bt =>
        abstractRangeFast coreWalkFuel bt d.toNat k.toNat (0 : Word).toNat >>= fun cur =>
        inferLamsOut d.toNat (ws.map decE) k.toNat cur) := by
    rw [hdk', h0, inferLamsLeaf, Array.size_map, hB.size]
  rw [hT]
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode (d + k) (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) h2
  have hK₂ := h₂.2.1.bkept
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_callW (hab n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb (r₂.headD 0) d k 0 hS₂
    h₂.2.2.2) h3
  have hK₃ := h₃.2.1.bkept
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have hB₁ := hB.keep hK₁ hbtop hsz
  have hB₂ := hB₁.keep hK₂ (by rw [hK₁.1]; exact hbtop) (by rw [hK₁.2.1]; exact hsz)
  have hB₃ := hB₂.keep hK₃ (by rw [hK₂.1, hK₁.1]; exact hbtop)
    (by rw [hK₂.2.1, hK₁.2.1]; exact hsz)
  exact (lamsOut_ref p hp hab hcap dn vis fe eb d lo k ws hws (n + 1) m₃ _ M₃ k (r₃.headD 0) hS₃
    h₃.2.2.2 hB₃ (Nat.le_refl _) (by rw [hK₃.1, hK₂.1, hK₁.1]; exact hbtop) _ _ hW).1

/-! ## `infer_lams`: the peel loop as a named block -/

/-- The peel loop of `inferLamsL` (Infer.lean), named for its spec. -/
def inferLamsW : Stmt := lblk (mode, vis, d, peel, t, k, fo, lo, s, i, ty, body, tyo, tty, w, fv, r) {
  while peel != 0 && t >> 28 == 5 {
    s := ⟦t⟧.tier;
    i := ⟦t⟧.idx;
    if s != 0 && CTL.u64[1] == 0 { abort };
    if LAM⟨s⟩.count <= i { abort };
    ty := LAM⟨s, i⟩.ty;
    body := LAM⟨s, i⟩.b;
    tyo := call inst_list(ty, fo, k, 0);
    tty := call infer(mode, vis, d + k, tyo);
    w := call whnf(mode, vis, d + k, tty);
    if w >> 28 != 2 { fail R_EXPECTED_A_SORT };
    fv := call intern_fvar(d + k, tyo);
    if len(SPN.u64) <= fo + k { abort };
    if len(BSTK.u64) <= lo + k { abort };
    SPN.u64[fo + k] := fv;
    BSTK.u64[lo + k] := tyo;
    k += 1;
    CTL.u64[136] := fo + k;
    CTL.u64[137] := lo + k;
    peel -= 1;
    t := body
  }
}

/-- `inferLamsL`, with its loop spliced from `inferLamsW`. -/
-- con-ron: none — `inferLamsL` itself (`rfl`), its loop a named block for the proof
def inferLamsL' : FunDecl :=
    lfn (mode, vis, d, peel, t, k, fo, lo) locals (s, i, ty, body, tyo, tty, w, fv, r) {
  ⟪inferLamsW⟫;
  r := call infer_lams_leaf(mode, vis, d, t, k, fo, lo);
  return r
}

theorem inferLamsL_eq : inferLamsL = inferLamsL' := rfl

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

/-- **The model of the λ peel loop** at L fuel `n`: the exit's `(t, k, memory)`. -/
def lamsLoop (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, mode, vis, d, peel, t, k, fo, lo =>
    if peel ≠ 0 ∧ t >>> 28 = 5 then
      if tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if tcnt m LAM (tierW t) ≤ idxW t then none
      else
        match callW p n "inst_list" [tfld m LAM (tierW t) (idxW t) 0, fo, k, 0] m with
        | none => none
        | some (r₁, m₁) =>
          match callW p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
          | none => none
          | some (r₂, m₂) =>
            match callW p n "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with
            | none => none
            | some (r₃, m₃) =>
              if r₃.headD 0 >>> 28 ≠ 2 then none
              else
                match callW p n "intern_fvar" [d + k, r₁.headD 0] m₃ with
                | none => none
                | some (r₄, m₄) =>
                  if tPushOK m₄ fo lo k then
                    lamsLoop p n (tPush m₄ fo lo k (r₄.headD 0) (r₁.headD 0)) mode vis d (peel - 1)
                      (tfld m LAM (tierW t) (idxW t) 1) (k + 1) fo lo
                  else none
    else some (t, k, m)

theorem lamsW_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n inferLamsW
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
      lamsLoop p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
        (s₀.loc 6) (s₀.loc 7) = some (s'.loc 4, s'.loc 5, s'.mem); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := inferLamsW) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec, ih,
      callW_spec p n "inst_list", callW_spec p n "infer", callW_spec p n "whnf",
      callW_spec p n "intern_fvar", evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
    simp_all [lamsLoop, tPush, tPushOK, Cmp.eval, LocEq, BinOp.eval, tierW, idxW, St.setLocs_cons,
      St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, size_set64, w_lt_false, Mem.arr64_set64_ne]

/-- **The model of `infer_lams`.** -/
def lamsFull (p : Prog) (n k : Nat) (m : Mem) (mode vis d peel t kk fo lo : Word) : Option (Word × Mem) :=
  match lamsLoop p k m mode vis d peel t kk fo lo with
  | none => none
  | some (t', k', m') => call1W p n "infer_lams_leaf" [mode, vis, d, t', k', fo, lo] m'

theorem inferLams_spec (p : Prog) (hq : BindProg p) (n : Nat) (s₀ : St)
    (mode vis d peel t k fo lo : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_lams" [mode, vis, d, peel, t, k, fo, lo]
    ⦃fun r s' => LocEq s' s₀ ∧
      lamsFull p n (n + 1) s₀.mem mode vis d peel t k fo lo = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.lams, inferLamsL_eq]
  simp only [callFn, inferLamsL']
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (lamsW_spec p (n + 1) s), callW_spec p n "infer_lams_leaf"] <;>
  simp_all [lamsFull, call1W, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ]

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
    rw [htp, rdW_set64, if_neg (fun h => absurd h.2.1 (by decide)), hm₃, rdW_set64, if_pos ⟨rfl, rfl, by
      rw [hm₂, hm₁, size_set64, size_set64]; exact h136⟩]
  · have hB₁ : BStkR m₁ lo k ws := hB.frame e2
    have hpush := hB₁.push (by rw [e2]; exact hcap) (by rw [e2]; exact h2) x
    rw [← hm₂] at hpush
    exact hpush.frame eB
  · simp only [bTop]
    rw [htp, rdW_set64, if_pos ⟨rfl, rfl, by rw [hm₃, hm₂, hm₁, size_set64, size_set64, size_set64]; exact h137⟩]
  · intro j hj
    simp only [spW, eS]
    rw [show rdW (m₁.arr64 SPN) j = spW m₁ j from rfl, hm₁, spW_set64_ne _ _ _ _ (fun h => by
      have := UInt64.lt_iff_toNat_lt.mp hj; rw [← h, hadd] at this; omega)]
    exact hb j hj
  · intro j hj
    have hBb := hB.bound
    have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
    rw [eB, hm₂, rdW_set64, if_neg (fun h => by
      have := UInt64.lt_iff_toNat_lt.mp hj; rw [← h.2.1, haddl] at this; omega), e2]
  · have hfr : MemFrame [SPN, BSTK] [136, 137] m (tPush m fo lo k fv x) := by
      rw [htp, hm₃, hm₂, hm₁]
      exact ((((MemFrame.set64 m SPN (by decide) _ fv).mono (by simp) (by simp)).trans
        ((MemFrame.set64 _ BSTK (by decide) _ x).mono (by simp) (by simp))).trans
        ((MemFrame.setCtl _ 136 _).mono (by simp) (by simp))).trans
        ((MemFrame.setCtl _ 137 _).mono (by simp) (by simp))
    exact PoolGrew.of_frame hfr (by decide) (by decide)

/-- The conclusion of a telescope run from an inner memory: the twin's run, the result, the
relation, the spine stack below the telescope's `fvs` slice kept from the entry memory `m₀`. -/
def TelPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (m₀ : Mem) (fo lo : Word) (a : AState) (T : AM EIdx) (w : Word) (mF : Mem) : Prop :=
  ∃ x a', T.run a = .ok (x, a') ∧ x = decE w ∧ HW w ∧
    ∃ M', CoreS dn mF a' vis fe M' eb ∧ KeptAll M M' eb ∧
      (∀ j, j < fo → spW mF j = spW m₀ j) ∧ (mF.arr64 SPN).size = (m₀.arr64 SPN).size ∧
      (∀ j, j < lo → rdW (mF.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) ∧
      (mF.arr64 BSTK).size = (m₀.arr64 BSTK).size ∧ PoolGrew m₀ mF

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

/-- **The λ peel loop with its leaf refines `inferLams`** by induction on the loop fuel. -/
theorem lamsFull_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap)
    (N : Nat) (hk : KnotUpTo p N) (F : Nat) (hFN : N ≤ F) (hN : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo lo eb : Word)
    (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) :
    ∀ j, j ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (peel t k : Word) (fvs : Array EIdx)
      (ws : Array Word),
      CoreS dn m a vis fe M eb → HW t → SpineR m fo k fvs → spTop m = fo + k →
      BStkR m lo k ws → bTop m = lo + k → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
      d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      (∀ j, j < fo → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      (∀ j, j < lo → rdW (m.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) →
      (m.arr64 BSTK).size = (m₀.arr64 BSTK).size → PoolGrew m₀ m →
      ∀ w mF, lamsFull p N j m mode vis d peel t k fo lo = some (w, mF) →
      TelPost dn vis fe M eb m₀ fo lo a
        (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t) k.toNat fvs
          (ws.map decE)) w mF := by
  intro j
  induction j with
  | zero => intro _ m a M peel t k fvs ws _ _ _ _ _ _ _ _ _ _ _ _ _ w mF hF; simp [lamsFull, lamsLoop] at hF
  | succ j ih =>
    intro hjN m a M peel t k fvs ws hS ht hf htop hB hbt hws hdk hb0 hsz hbb0 hbsz0 hpg0 w mF hF
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
    have hexit : ∀ (hT : (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t)
          k.toNat fvs (ws.map decE)).run a = (inferLamsLeaf (coreKnot (decMode mode) fe id F)
          d.toNat (decE t) k.toNat fvs (ws.map decE)).run a),
        call1W p N "infer_lams_leaf" [mode, vis, d, t, k, fo, lo] m = some (w, mF) →
        TelPost dn vis fe M eb m₀ fo lo a (inferLams (coreKnot (decMode mode) fe id F) d.toNat
          peel.toNat (decE t) k.toNat fvs (ws.map decE)) w mF := by
      intro hT hc
      have hl := CoreSpec.of_call1W (r := [w]) (s₀ := ⟨m, Locals.init []⟩)
        (inferLamsLeaf_any p hp hq hil hab hcap N hk F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb
          mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩ ht hf hftop hB hbtop hws (by omega))
        (fun r r' h => by simp only [decH, h]) hc
      obtain ⟨hok, ⟨M', hS', hK', hSt'⟩, hres, hrw⟩ := hl
      refine ⟨_, _, hT.trans (AM.run_of_ok _ _ hok), hres, hrw, M', hS', hK', fun i hi => ?_,
        hSt'.size.trans hsz, fun i hi => ?_, hSt'.bstk.2.1.trans hbsz0, hpg0.trans hSt'.pool⟩
      · have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt'.below i hi').trans (hb0 i hi)
      · have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt'.bstk.2.2 i hi').trans (hbb0 i hi)
    by_cases hc : peel ≠ 0 ∧ t >>> 28 = 5
    · obtain ⟨hp0, ht5⟩ := hc
      have hc1 : ¬ (tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun g => by
        simp only [lamsFull, lamsLoop, hp0, ht5, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      have hc2 : ¬ tcnt m LAM (tierW t) ≤ idxW t := fun g => by
        simp only [lamsFull, lamsLoop, hp0, ht5, hc1, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      have hv : viewOK m t LAM := ⟨hc1, UInt64.not_le.mp hc2⟩
      obtain ⟨-, hty, hbody⟩ := view_lam m a hS.arena.1 t ht hv ht5
      have hvb := viewBind_lam m a hS.arena.1 t ht hv ht5
      cases h1 : callW p j "inst_list" [tfld m LAM (tierW t) (idxW t) 0, fo, k, 0] m with
      | none => simp only [lamsFull, lamsLoop, hp0, ht5, hc1, hc2, h1, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      | some q =>
      obtain ⟨r₁, m₁⟩ := q
      cases h2 : callW p j "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
      | none => simp only [lamsFull, lamsLoop, hp0, ht5, hc1, hc2, h1, h2, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      | some q =>
      obtain ⟨r₂, m₂⟩ := q
      cases h3 : callW p j "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with
      | none => simp only [lamsFull, lamsLoop, hp0, ht5, hc1, hc2, h1, h2, h3, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      | some q =>
      obtain ⟨r₃, m₃⟩ := q
      have g1 : r₃.headD 0 >>> 28 = 2 := Classical.byContradiction fun g => by
        simp only [lamsFull, lamsLoop, hp0, ht5, hc1, hc2, h1, h2, h3, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      cases h4 : callW p j "intern_fvar" [d + k, r₁.headD 0] m₃ with
      | none => simp only [lamsFull, lamsLoop, hp0, ht5, hc1, hc2, h1, h2, h3, g1, h4, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      | some q =>
      obtain ⟨r₄, m₄⟩ := q
      have g2 : tPushOK m₄ fo lo k := Classical.byContradiction fun g => by
        simp only [lamsFull, lamsLoop, hp0, ht5, hc1, hc2, h1, h2, h3, g1, h4, g, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] at hF
      have hF' : lamsFull p N j (tPush m₄ fo lo k (r₄.headD 0) (r₁.headD 0)) mode vis d (peel - 1)
          (tfld m LAM (tierW t) (idxW t) 1) (k + 1) fo lo = some (w, mF) := by
        simpa only [lamsFull, lamsLoop, hp0, ht5, hc1, hc2, h1, h2, h3, g1, h4, g2, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true, reduceCtorEq, Option.some.injEq, and_self, true_and, and_true] using hF
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
          (by simp [fvarSch, FVREC, FVSLOT, FVLP, BSTK]) (by simp [fvarSch])
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
        have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hBK.2.2 i hi').trans (hbb0 i hi)
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
      have hp0' : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h'))
      obtain ⟨x, a', hrun', hx, hrw, M', hS'', hK, hb'', hsz'', hbb'', hbsz'', hpg''⟩ := ih (by omega)
        _ _ M₄ (peel - 1) _ (k + 1) _ _ hS' hbody hf' htop' hB' hbt' hws' (by rw [hk1, hpeel1]; omega)
        hb' hsz' (fun i hi => (hbbT i hi).trans (hbb₄ i hi)) (hbszT.trans (hBK.2.1.trans hbsz0))
        ((hpg0.trans hSt14.pool).trans hpgT) w mF hF'
      refine ⟨x, a', ?_, hx, hrw, M', hS'', hK₁.trans (hK₂.trans (hK₃.trans (hK₄.trans hK))), hb'',
        hsz'', hbb'', hbsz'', hpg''⟩
      rw [← hrun']
      obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 := ⟨peel.toNat - 1, by omega⟩
      have hlam : ((decE t).tag != ETag.lam) = false := by
        rw [bne_eq_false_iff_eq, ← beq_iff_eq, decE_tag_lam t ht]; simp [ht5]
      have hsort : ((decE (r₃.headD 0)).tag == ETag.sort) = true := tag_sort_beq _ hrw3 g1
      rw [hp', inferLams]
      simp only [hlam, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, viewBind_run', hvb,
        except_ok_bind]
      rw [AM.run_of_ok _ _ hok1, except_ok_bind, hres1]
      simp only [decH] at hres2 hres3 hres4 ⊢
      rw [← haddd, AM.run_of_ok _ _ hok2, except_ok_bind, hres2, AM.run_of_ok _ _ hok3, except_ok_bind,
        hres3]
      simp only [hsort, ↓reduceIte, internFVarE, StateT.run_bind]
      rw [AM.run_of_ok _ _ hok4, except_ok_bind, hres4, hk1, hpeel1, hp', Nat.add_sub_cancel,
        Array.map_push]
    · -- the exit
      have hL : lamsLoop p (j + 1) m mode vis d peel t k fo lo = some (t, k, m) := by
        simp only [lamsLoop, hc, ↓reduceIte]
      simp only [lamsFull, hL] at hF
      refine hexit ?_ hF
      by_cases hp0 : peel = 0
      · subst hp0; rfl
      · have ht5 : ¬ t >>> 28 = 5 := fun h => hc ⟨hp0, h⟩
        obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
          ⟨peel.toNat - 1, by
            have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
        have hlam : ((decE t).tag != ETag.lam) = true := by
          rw [bne_iff_ne, ne_eq, ← beq_iff_eq, decE_tag_lam t ht]; simp [ht5]
        rw [hp', inferLams]
        simp only [hlam, ↓reduceIte]

/-- **`infer_lams` refines `inferLams`** from a telescope state (`fvs` at the spine top, `stk` at
the binder top), up to the tops it leaves raised (`TelPost`). -/
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
    ⦃fun r s' => LocEq s' s₀ ∧ TelPost dn vis fe M eb m₀ fo lo a₀
      (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decE)) (r.headD 0) s'.mem; ⊤⦄ := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferLams_spec p hq n s₀ mode vis d peel t k fo lo)
  subst hs0
  exact ⟨hloc, lamsFull_ref p hp hq hb hil hab hcap n hk F hF hn dn vis fe mode d fo lo eb hs.mode4
    hs.eb_mode m₀ (n + 1) (Nat.le_refl _) s.mem a₀ M peel t k fvs ws hs.rel ht hf htop hB hbt hws hdk
    hb0 hsz hbb0 hbsz0 hpg0 _ _ hW⟩

/-! ## `infer_lam` -/

/-- **The model of `infer_lam`.** -/
def lamK (p : Prog) (n : Nat) (m : Mem) (mode vis d ty body : Word) : Option (Word × Mem) :=
  if d >>> 63 ≠ 0 then none
  else match callW p n "infer" [mode, vis, d, ty] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
    | none => none
    | some (r₂, m₂) =>
      if r₂.headD 0 >>> 28 ≠ 2 then none
      else match callW p n "intern_fvar" [d, ty] m₂ with
      | none => none
      | some (r₃, m₃) =>
        if tPushOK m₃ (rdW (m₃.arr64 CTL) 136) (rdW (m₃.arr64 CTL) 137) 0 then
          match callW p n "infer_lams" [mode, vis, d, 16777216, body, 1, rdW (m₃.arr64 CTL) 136,
              rdW (m₃.arr64 CTL) 137]
              (tPush m₃ (rdW (m₃.arr64 CTL) 136) (rdW (m₃.arr64 CTL) 137) 0 (r₃.headD 0) ty) with
          | none => none
          | some (r₄, m₄) =>
            if 137 < (m₄.arr64 CTL).size then
              some (r₄.headD 0, (m₄.set64 CTL 136 (rdW (m₃.arr64 CTL) 136)).set64 CTL 137
                (rdW (m₃.arr64 CTL) 137))
            else none
        else none

theorem inferLam_spec (p : Prog) (hq : BindProg p) (n : Nat) (s₀ : St) (mode vis d ty body : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_lam" [mode, vis, d, ty, body]
    ⦃fun r s' => LocEq s' s₀ ∧ lamK p n s₀.mem mode vis d ty body = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.lam]
  simp only [callFn, inferLamL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      callW_spec p n "infer", callW_spec p n "whnf", callW_spec p n "intern_fvar",
      callW_spec p n "infer_lams"] <;>
  simp_all [lamK, tPush, tPushOK, LocEq, BinOp.eval, St.setLocs_cons, CTL, Cmp.eval,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero,
    Locals.init_cons_succ, size_set64]

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
  have eS := hfr.1 SPN (by simp) (by decide)
  have eB := hfr.1 BSTK (by simp) (by decide)
  refine ⟨?_, by rw [eS, hsz], fun j hj => by simp only [spW, eS]; exact hb j hj,
    ⟨?_, by rw [eB, hbsz], fun j hj => by rw [eB]; exact hbb j hj⟩,
    hpg.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩
  · unfold spTop
    rw [rdW_set64, if_neg (fun h => absurd h.2.1 (by decide)), rdW_set64, if_pos ⟨rfl, rfl, h136⟩]
  · unfold bTop
    rw [rdW_set64, if_pos ⟨rfl, rfl, by rw [size_set64]; exact h137⟩]

/-- **`infer_lam` refines `inferLam`** at the knot (the `.lam` clause of `inferBody`). -/
@[refines ConRon.Arena.inferLam]
theorem inferLam_refines (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpec p (n + 1) "infer_lam" [mode, vis, d, ty, body]
      (inferLam (coreKnot (decMode mode) fe id F) d.toNat (decE ty) (decE body)) decH s₀ a₀ dn vis fe
        M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (inferLam_spec p hq n s₀ mode vis d ty body)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  unfold lamK at hW
  by_cases hd : d >>> 63 ≠ 0
  · rw [if_pos hd] at hW; cases hW
  rw [if_neg hd] at hW
  have hd63 : d.toNat < 2 ^ 63 := by
    have : d >>> 63 = 0 := by simpa using hd
    have h2 := congrArg UInt64.toNat this
    rw [UInt64.toNat_shiftRight] at h2
    simp [Nat.shiftRight_eq_div_pow] at h2
    have := d.toNat_lt
    omega
  rcases h1 : callW p n "infer" [mode, vis, d, ty] s.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [h1, reduceCtorEq] at hW
  rcases h2 : callW p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with _ | ⟨r₂, m₂⟩
    <;> simp only [h2, reduceCtorEq] at hW
  by_cases g1 : r₂.headD 0 >>> 28 ≠ 2
  · rw [if_pos g1] at hW; cases hW
  rw [if_neg g1] at hW
  rcases h3 : callW p n "intern_fvar" [d, ty] m₂ with _ | ⟨r₃, m₃⟩
    <;> simp only [h3, reduceCtorEq] at hW
  have g2 : tPushOK m₃ (rdW (m₃.arr64 CTL) 136) (rdW (m₃.arr64 CTL) 137) 0 := by
    refine Classical.byContradiction fun g => ?_; rw [if_neg g] at hW; cases hW
  rw [if_pos g2] at hW
  cases h4 : callW p n "infer_lams" [mode, vis, d, 16777216, body, 1, rdW (m₃.arr64 CTL) 136,
      rdW (m₃.arr64 CTL) 137] (tPush m₃ (rdW (m₃.arr64 CTL) 136) (rdW (m₃.arr64 CTL) 137) 0 (r₃.headD 0) ty) with
  | none => rw [h4] at hW; cases hW
  | some q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [h4] at hW; dsimp only at hW
  have g3 : 137 < (m₄.arr64 CTL).size := by
    refine Classical.byContradiction fun g => ?_; rw [if_neg g] at hW; cases hW
  rw [if_pos g3] at hW
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
  obtain ⟨s₃, hs₃, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internFVar_spec p hb.fvf hb.fvp hb.fvi n _ d ty) h3
  rw [hs₃] at hfv
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := internFVar_core hS₂ d ty hty r₃ hfv
  -- the pushes
  have hSt13 := hSt₁.trans (hSt₂.trans hSt₃)
  obtain ⟨so, hso⟩ : ∃ so, so = rdW (m₃.arr64 CTL) 136 := ⟨_, rfl⟩
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = rdW (m₃.arr64 CTL) 137 := ⟨_, rfl⟩
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
    (inferLams_tel p hp hq hb hil hab hcap n' (hk.mono (by omega)) F (by omega) (by omega) _ _ dn
      vis fe M₃ eb mode d 16777216 body 1 so lo _ _ m₃ ⟨hS', hs.mode4, hs.eb_mode⟩ hbody hf' htop' hB'
      hbt' (by intro i hi; simp at hi; subst hi; simpa using hty) (by simp; omega) hb' hsz' hbbT hbszT
      hpgT) h4
  rw [ht₄] at hTel
  obtain ⟨x, a', hrun4, hx, hrw4, M', hS₄, hK₄, hb₄, hsz₄, hbb₄, hbsz₄, hpg₄⟩ := hTel
  -- the twin's run
  have hsort : ((decE (r₂.headD 0)).tag == ETag.sort) = true := tag_sort_beq _ hrw2 (by simpa using g1)
  have hrun : (inferLam (coreKnot (decMode mode) fe id F) d.toNat (decE ty) (decE body)).run a₀ =
      .ok (x, a') := by
    simp only [inferLam, StateT.run_bind]
    have hpf : (16777216 : Word).toNat = peelFuel := rfl
    rw [hpf] at hrun4
    generalize peelFuel = P at hrun4 ⊢
    rw [AM.run_of_ok _ _ hok1, except_ok_bind, hres1]
    simp only [decH] at hres2 hres3 ⊢
    rw [AM.run_of_ok _ _ hok2, except_ok_bind, hres2]
    rw [hsort, if_pos rfl, internFVarE, StateT.run_bind]
    rw [AM.run_of_ok _ _ hok3, except_ok_bind, hres3]
    have ha2 : ((#[] : Array Word).push ty).map decE = #[decE ty] := by simp
    rw [ha2] at hrun4
    exact hrun4
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, by rw [hres, hx, decH, hr], by unfold ResH; rw [← hr]; exact hrw4⟩
  rw [hst, ← hm, hso, hlo]
  have htop3 : spTop m₃ = so := hso.symm
  obtain ⟨hSF, hkF⟩ := tops_restore (m₀ := s.mem) hS₄ hSt13
    (fun j hj => hb₄ j (htop3 ▸ hj)) hsz₄ (fun j hj => hbb₄ j (by rw [hlo]; exact hj)) hbsz₄ hpg₄ g3
  exact ⟨M', hSF, hK₁.trans (hK₂.trans (hK₃.trans hK₄)), hkF⟩

end L.Arena
