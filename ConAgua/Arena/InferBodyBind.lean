import ConAgua.Arena.InferBodySpineF

/-!
# The binder telescopes: `infer_lams`, `infer_pis`, their leaves, `infer_lam`, `infer_forall`

The telescopes keep two stacks growing in step: the free variables `fvs` on the spine stack `SPN`
(array 144, top `CTL[136]`; `SpineR`) and the second list `stk` on the binder stack `BSTK`
(array 145, top `CTL[137]`; `BStkR`, a slice of words). `CoreS` survives writes to both
(`CoreS.frame_stk`, `CoreS.frame`).

**What the callees must keep.** `CoreAfter` (lane `whnf`'s `StackKept`) says nothing about
`BSTK`: a knot slot run inside the telescope could, as far as its spec goes, overwrite the binder
stack below its top. The telescopes assume it of the callees they call while the stack holds
entries (`BStkCallees`: `infer`, `whnf`, `inst_list`, `ar_entry`, `ensure_sort` keep `BSTK` below
`CTL[137]`, and `CTL[137]`); the interning callees are proved to (their frames, `BKept.of_frame`).
Discharging `BStkCallees` needs `StackKept` (or `CoreAfter`) to carry the binder stack, which every
core body would then prove (DESIGN.md).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The binder stack -/

/-- The binder stack's top. -/
def bTop (m : Mem) : Word := rdW (m.arr64 CTL) 137

/-- **A slice of the binder stack**, as words. -/
structure BStkR (m : Mem) (lo k : Word) (ws : Array Word) : Prop where
  size : ws.size = k.toNat
  bound : lo.toNat + k.toNat ≤ (m.arr64 BSTK).size
  get : ∀ (i : Nat) (h : i < ws.size), ws[i] = rdW (m.arr64 BSTK) (lo + i.toUInt64)

/-- The binder stack below its top is kept, and so is the top. -/
def BKept (m m' : Mem) : Prop :=
  bTop m' = bTop m ∧ (m'.arr64 BSTK).size = (m.arr64 BSTK).size ∧
    ∀ j : Word, j < bTop m → rdW (m'.arr64 BSTK) j = rdW (m.arr64 BSTK) j

theorem BKept.refl (m : Mem) : BKept m m := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem BKept.trans {m₁ m₂ m₃ : Mem} (h₁ : BKept m₁ m₂) (h₂ : BKept m₂ m₃) : BKept m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun j hj => (h₂.2.2 j (h₁.1 ▸ hj)).trans (h₁.2.2 j hj)⟩

theorem BKept.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m')
    (hA : BSTK ∉ A) (hC : (137 : Word) ∉ C) : BKept m m' := by
  have hb : m'.arr64 BSTK = m.arr64 BSTK := hf.1 BSTK hA (by decide)
  exact ⟨hf.2.1 137 hC, by rw [hb], fun j _ => by rw [hb]⟩

/-- **The callees a telescope calls while its binder stack holds entries keep it.** -/
def BStkCallees (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    (f = "infer" ∨ f = "whnf" ∨ f = "inst_list" ∨ f = "ar_entry" ∨ f = "ensure_sort") →
    callW p n f vs m = some (r, m') → BKept m m'

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
    (hbc : BStkCallees p) (hcap : BStkCap) (dn : NIdx → Option ConLeche.Name) (vis : Word)
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
    cases h1 : callW p k "ar_entry" [rdW (m.arr64 BSTK) (lo + (n - 1)), d, n - 1, 0] m with
    | none => rw [h1] at h; cases h
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [h1] at h; dsimp only at h
    cases h2 : callW p k "mk_forall" [r₁.headD 0, cur] m₁ with
    | none => rw [h2] at h; cases h
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [h2] at h; dsimp only at h
    have hwj : HW (rdW (m.arr64 BSTK) (lo + (n - 1))) := hwsj ▸ hws _ hjK
    have h₁ := CoreSpec.of_callW (hab k ⟨m, Locals.init []⟩ a dn vis fe M eb _ d (n - 1) 0 hS hwj) h1
    have hK₁ := hbc k "ar_entry" _ m r₁ m₁ (by simp) h1
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
    (hil : InstListOK p) (hab : AbstractRangeOK p) (hbc : BStkCallees p) (hcap : BStkCap) (n : Nat)
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
  cases h3 : callW p n "ar_entry" [r₂.headD 0, d, k, 0] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW; dsimp only at hW
  have hsz := hcap _ _ _ _ _ _ _ hS
  have h₁ := CoreSpec.of_callW (hil n s a₀ dn vis fe M eb t fo k 0 fvs hS ht hf hftop) h1
  have hK₁ := hbc n "inst_list" _ _ _ _ (by simp) h1
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
  have hK₂ := hbc n "infer" _ _ _ _ (by simp) h2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have h₃ := CoreSpec.of_callW (hab n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb (r₂.headD 0) d k 0 hS₂
    h₂.2.2.2) h3
  have hK₃ := hbc n "ar_entry" _ _ _ _ (by simp) h3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have hB₁ := hB.keep hK₁ hbtop hsz
  have hB₂ := hB₁.keep hK₂ (by rw [hK₁.1]; exact hbtop) (by rw [hK₁.2.1]; exact hsz)
  have hB₃ := hB₂.keep hK₃ (by rw [hK₂.1, hK₁.1]; exact hbtop)
    (by rw [hK₂.2.1, hK₁.2.1]; exact hsz)
  exact (lamsOut_ref p hp hab hbc hcap dn vis fe eb d lo k ws hws (n + 1) m₃ _ M₃ k (r₃.headD 0) hS₃
    h₃.2.2.2 hB₃ (Nat.le_refl _) (by rw [hK₃.1, hK₂.1, hK₁.1]; exact hbtop) _ _ hW).1

end L.Arena
