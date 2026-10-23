import ConAgua.Arena.RecCheckSpec16
import ConAgua.Arena.RecGenSpec

/-!
# `classNodesAgree` (lane `indproofs4`, helper `cls`)

`class_nodes_agree(vis, p, ft.off, ft.len, mc, tele.off, tele.len, leaf, fvs.off, fvs.len, i,
es.off, es.len)`: K.53′ at every entry of `es`. L walks `es` with a `while` loop (the twin: a list
recursion); the loop is a named block here (`cnaLoop`, spliced back by `rfl`), its model `cnaW`
runs the callees by `callW` at the iteration's fuel, and `cnaW_ok` relates it to the twin by
induction on the loop fuel, the cursor `j` advancing over the slice `(es.off + j, es.len - j)`.
Callees: `target_pi_doms_with` (`pdW_ok`, its write set `pdW_mfr`), `target_k53` (`tkW_ok`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The loop as a named block -/

/-- The loop of `classNodesAgreeL` (RecGen.lean), named for its spec. -/
-- con-ron: none — `classNodesAgreeL`'s own loop (`rfl`), a named block for the proof
def cnaLoop : Stmt := lblk (vis, p, ftOff, ftLen, mc, teleOff, teleLen, leaf, fvsOff, fvsLen, i,
    esOff, esLen, j, e, ok, domsOff, domsLen, f, b) {
  while j < esLen {
    e := IW.u64[esOff + j];
    (ok, domsOff, domsLen) := call target_pi_doms_with(fvsOff, fvsLen, IW.u64[e + 4]);
    if ok == 0 { domsLen := 0 };
    if domsLen <= i { abort };
    f := IW.u64[domsOff + i];
    b := call target_k53(vis, p, ftOff, ftLen, mc, teleOff, teleLen, leaf, f);
    if b == 0 { abort };
    j += 1
  }
}

/-- `classNodesAgreeL`, with its loop spliced from `cnaLoop`. -/
-- con-ron: none — `classNodesAgreeL` itself (`rfl`), its loop a named block for the proof
def classNodesAgreeL' : FunDecl := lfn
    (vis, p, ftOff, ftLen, mc, teleOff, teleLen, leaf, fvsOff, fvsLen, i, esOff, esLen)
    locals (j, e, ok, domsOff, domsLen, f, b) {
  j := 0;
  ⟪cnaLoop⟫;
  return 0
}

theorem classNodesAgreeL_eq : classNodesAgreeL = classNodesAgreeL' := rfl

/-! ## The model -/

section model
variable (p : Prog)

/-- After `target_k53`: the next entry. -/
def cnaK2 (rest : Mem → Option Mem) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else rest m

/-- After `target_pi_doms_with`: field `i` of the opened domains, then `target_k53`. -/
def cnaK1 (k : Nat) (vis q fto ftl mc teo tel leaf i : Word) (rest : Mem → Option Mem) :
    Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then none
    else if r.tail.tail.headD 0 ≤ i then none
    else cnaK2 rest (callW p k "target_k53" [vis, q, fto, ftl, mc, teo, tel, leaf,
      rdW (m.arr64 IW) (r.tail.headD 0 + i)] m)

/-- **The model of `class_nodes_agree`'s loop** at L fuel `k`, from cursor `j`: the memory at the
exit. -/
def cnaW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, q, fto, ftl, mc, teo, tel, leaf, fvo, fvl, i, eo, el, j =>
    if j < el then
      cnaK1 p k vis q fto ftl mc teo tel leaf i
        (fun m' => cnaW k m' vis q fto ftl mc teo tel leaf fvo fvl i eo el (j + 1))
        (callW p k "target_pi_doms_with" [fvo, fvl, rdW (m.arr64 IW) (rdW (m.arr64 IW) (eo + j) + 4)] m)
    else some m

section arms
variable (k : Nat) (m : Mem) (vis q fto ftl mc teo tel leaf fvo fvl i eo el j : Word) (r : List Word)
  (rest : Mem → Option Mem)
theorem cnaK2_bad (h : r.headD 0 = 0) : cnaK2 rest (some (r, m)) = none := by
  simp only [cnaK2]; rw [if_pos h]
theorem cnaK2_ok (h : ¬ r.headD 0 = 0) : cnaK2 rest (some (r, m)) = rest m := by
  simp only [cnaK2]; rw [if_neg h]
theorem cnaK1_bad (h : r.headD 0 = 0) : cnaK1 p k vis q fto ftl mc teo tel leaf i rest (some (r, m)) = none := by
  simp only [cnaK1]; rw [if_pos h]
theorem cnaK1_short (h0 : ¬ r.headD 0 = 0) (h : r.tail.tail.headD 0 ≤ i) :
    cnaK1 p k vis q fto ftl mc teo tel leaf i rest (some (r, m)) = none := by
  simp only [cnaK1]; rw [if_neg h0, if_pos h]
theorem cnaK1_ok (h0 : ¬ r.headD 0 = 0) (h : ¬ r.tail.tail.headD 0 ≤ i) :
    cnaK1 p k vis q fto ftl mc teo tel leaf i rest (some (r, m)) =
      cnaK2 rest (callW p k "target_k53" [vis, q, fto, ftl, mc, teo, tel, leaf,
        rdW (m.arr64 IW) (r.tail.headD 0 + i)] m) := by
  simp only [cnaK1]; rw [if_neg h0, if_neg h]
theorem cnaW_exit (h : ¬ j < el) :
    cnaW p (k + 1) m vis q fto ftl mc teo tel leaf fvo fvl i eo el j = some m := by
  simp only [cnaW]; rw [if_neg h]
theorem cnaW_step (h : j < el) :
    cnaW p (k + 1) m vis q fto ftl mc teo tel leaf fvo fvl i eo el j =
      cnaK1 p k vis q fto ftl mc teo tel leaf i
        (fun m' => cnaW p k m' vis q fto ftl mc teo tel leaf fvo fvl i eo el (j + 1))
        (callW p k "target_pi_doms_with" [fvo, fvl, rdW (m.arr64 IW) (rdW (m.arr64 IW) (eo + j) + 4)] m) := by
  simp only [cnaW]; rw [if_pos h]
end arms

end model

attribute [ind_grind] cnaK2_bad cnaK2_ok cnaK1_bad cnaK1_short cnaK1_ok cnaW_exit cnaW_step

/-! ## The `vcgen` specs -/

theorem cnaLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k cnaLoop
    ⦃fun r s' => r = .normal ∧
      cnaW p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)
        (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) (s₀.loc 12) (s₀.loc 13) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := cnaLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        callW_spec p k "target_pi_doms_with", callW_spec p k "target_k53"] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

theorem cna_spec (p : Prog) (hp : p.lookup "class_nodes_agree" = some classNodesAgreeL) (n : Nat)
    (s₀ : St) (vis q fto ftl mc teo tel leaf fvo fvl i eo el : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_nodes_agree"
      [vis, q, fto, ftl, mc, teo, tel, leaf, fvo, fvl, i, eo, el]
    ⦃fun _ s' => LocEq s' s₀ ∧
      cnaW p n s₀.mem vis q fto ftl mc teo tel leaf fvo fvl i eo el 0 = some s'.mem; ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
  rw [invoke_eq _ hp, classNodesAgreeL_eq]
  simp only [callFn, classNodesAgreeL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (cnaLoop_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
      loc_init9, loc_init10, loc_init11, loc_init12]

/-! ## The relational side -/

/-- The type field of a `NestCtorNf` record decoded below the tops. -/
theorem decNCN_ty {m : Mem} {e : Word} {nf : NestCtorNf} (h : DecB (fun m => decNCN m e.toNat) m nf)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (e + 4)) ∧ decI (rdW (m.arr64 IW) (e + 4)) = nf.ty := by
  have h' : decNCN (truncM m) e.toNat = some nf := h
  simp only [decNCN, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨c, -, lv, -, ds, -, x4, h4, rfl⟩ := h'
  exact truncH (i := 4) h4 hsz

/-- `target_pi_doms_with` writes no walk memo. -/
theorem pdW_mfr : ∀ (n : Nat) (m m' : Mem) (xo xl e : Word) (r : List Word),
    pdW n m xo xl e = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [pdW] at h
  | n + 1, m, m', xo, xl, e, r, h => by
    by_cases h0 : xl = 0
    · rw [pdW_nil (h := h0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    by_cases h6 : e >>> 28 ≠ 6
    · rw [pdW_nf (h := h0) (h1 := h6)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    by_cases hv : eViewW m e = []
    · rw [pdW_ev (h := h0) (h1 := h6) (h2 := hv)] at h; cases h
    rw [pdW_cons (h := h0) (h1 := h6) (h2 := hv)] at h
    cases h1 : i1F m [CWF, (eViewW m e).tail.tail.headD 0, rdW (m.arr64 IW) xo, 0] with
    | none => rw [h1] at h; simp [pdK1] at h
    | some x =>
    obtain ⟨r1, m1⟩ := x
    rw [h1, pdK1_some] at h
    refine (MFr.ofI1F h1).trans ?_
    cases h2 : pdW n m1 (xo + 1) (xl - 1) (r1.headD 0) with
    | none => rw [h2] at h; simp [pdK2] at h
    | some y =>
    obtain ⟨r2, m2⟩ := y
    rw [h2] at h
    refine (pdW_mfr n _ _ _ _ _ _ h2).trans ?_
    by_cases h3 : r2.headD 0 = 0
    · rw [pdK2_none (h := h3)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [pdK2_ok (h := h3)] at h
    cases h4 : consW n m2 ((eViewW m e).tail.headD 0) (r2.tail.headD 0) (r2.tail.tail.headD 0) with
    | none => rw [h4] at h; simp [pdK3] at h
    | some z =>
    obtain ⟨r3, m3⟩ := z
    rw [h4, pdK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
    exact consW_mfr h4

/-- The lookups of `class_nodes_agree`. -/
structure CnaProg (p : Prog) : Prop where
  k53 : K53Look p
  hv : p.lookup "e_view" = some eView
  hc : p.lookup "iw_copy" = some iwCopy
  ha : p.lookup "iw_alloc" = some iwAlloc
  hsc : p.lookup "sl_cons" = some slCons
  pd : p.lookup "target_pi_doms_with" = some L.Ind.targetPiDomsWith
  hi1 : I1Prog p
  cna : p.lookup "class_nodes_agree" = some classNodesAgreeL

section rel
variable {p : Prog} (P : CnaProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl mc teo tel leaf fvo fvl i eo el : Word) (bs : BlockShape) (formerTys : List EIdx)
  (TM : TargetMajor) (tele fvs : List EIdx)
include P

/-- **`class_nodes_agree`'s loop refines `classNodesAgree`** on the entries from the cursor `j`. -/
theorem cnaW_ok (k : Nat) : ∀ (m m' : Mem) (a : AState) (j : Word) (es : List NestCtorNf),
    cnaW p k m vis q fto ftl mc teo tel leaf fvo fvl i eo el j = some m' →
    StageR dn vis fe m a → BSOK m q.toNat bs → decHL m fto.toNat ftl.toNat = some formerTys →
    fto.toNat + ftl.toNat ≤ iwTop m → DecB (fun m => decTM m mc.toNat) m TM → HSl0 m teo tel tele →
    H leaf → decHL m fvo.toNat fvl.toNat = some fvs → fvo.toNat + fvl.toNat ≤ iwTop m →
    j ≤ el → PSlR decNCN es (eo + j) (el - j) m → RcMR m →
    ∃ a', (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es).run a =
      .ok ((), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  induction k with
  | zero => intro m m' a j es h; simp [cnaW] at h
  | succ k ih =>
  intro m m' a j es h hS hbs hft hftb hMc htl hl hfv hfvb hje hes hP
  by_cases hj : j < el
  rotate_left
  · rw [cnaW_exit (h := hj)] at h
    simp only [Option.some.injEq] at h; subst h
    have hjl : el - j = 0 := by
      apply UInt64.toNat_inj.mp
      have h1 : el.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
      have h2 : j.toNat ≤ el.toNat := UInt64.le_iff_toNat_le.mp hje
      rw [UInt64.toNat_sub_of_le _ _ hje]; simp <;> omega
    have : es = [] := by
      have := decPL_length _ (hes.1.get (OMono.decPL decNCN_mono _ _)); rw [hjl] at this; simpa using this
    subst this
    exact ⟨a, rfl, hS, IWGrow.refl _, hP⟩
  rw [cnaW_step (h := hj)] at h
  have hsz := hS.2.2.2.1
  have hne : el - j ≠ 0 := by
    intro h0
    have h1 : j.toNat < el.toNat := UInt64.lt_iff_toNat_lt.mp hj
    have := congrArg UInt64.toNat h0
    rw [UInt64.toNat_sub_of_le _ _ hje] at this; simp at this; omega
  obtain ⟨nf, es', rfl, hnf0, hes'⟩ := hes.uncons hne hsz
  generalize hE : rdW (m.arr64 IW) (eo + j) = ew at h hnf0
  obtain ⟨htyH, htyD⟩ := decNCN_ty hnf0 hsz
  -- `target_pi_doms_with`
  cases c1 : callW p k "target_pi_doms_with" [fvo, fvl, rdW (m.arr64 IW) (ew + 4)] m with
  | none => rw [c1] at h; simp [cnaK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [c1] at h
  obtain ⟨s1, hs1, -, hw1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (targetPiDomsWith_spec p P.hv P.hc P.ha P.hsc P.pd P.hi1 k _ fvo fvl (rdW (m.arr64 IW) (ew + 4))) c1
  simp only at hs1 hw1
  subst hs1
  obtain ⟨res, a1, run1, hS1, hg1, hpd⟩ := pdW_ok dn vis fe k _ _ a _ _ _ r1 fvs hw1 hS htyH hfv
    (hS.lt64 hfvb) hfvb
  have hP1 := hP.fr (pdW_mfr _ _ _ _ _ _ _ hw1)
  rw [htyD] at run1
  cases res with
  | none =>
    have h0 : r1.headD 0 = 0 := hpd
    rw [cnaK1_bad (h := h0)] at h; cases h
  | some ds =>
  obtain ⟨h1, hdd, hdb⟩ := hpd
  have h0 : ¬ r1.headD 0 = 0 := by rw [h1]; decide
  by_cases hsh : r1.tail.tail.headD 0 ≤ i
  · rw [cnaK1_short (h0 := h0) (h := hsh)] at h; cases h
  rw [cnaK1_ok (h0 := h0) (h := hsh)] at h
  have hi : i.toNat < (r1.tail.tail.headD 0).toNat := by
    exact Nat.lt_of_not_le (fun hc => hsh (UInt64.le_iff_toNat_le.mpr hc))
  have hdb64 := hS1.lt64 hdb
  obtain ⟨w, hw, hwH, hwD⟩ := decHL_get' hdd i.toNat hi (by omega)
  have hadd : r1.tail.headD 0 + i = UInt64.ofNat ((r1.tail.headD 0).toNat + i.toNat) := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp <;> omega
  rw [hadd, hw] at h
  -- `target_k53`
  cases c2 : callW p k "target_k53" [vis, q, fto, ftl, mc, teo, tel, leaf, w] s1.mem with
  | none => rw [c2] at h; simp [cnaK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [c2] at h
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (tk_spec p P.k53 stubCall (stubCall_spec p) k _ vis q fto ftl mc teo tel leaf w) c2
  simp only at hs2 hw2
  subst hs2
  obtain ⟨c, a2, run2, hc, hS2, hg2, hP2⟩ := tkW_ok dn fe vis k hw2 hS1 (hbs.grow hg1)
    (by rw [decHL_grow hg1 hftb]; exact hft) (by have := hg1.1; omega) (hMc.grow (decTM_mono _) hg1)
    (htl.grow hg1) hl hwH hP1
  by_cases hb : r2.headD 0 = 0
  · rw [cnaK2_bad (h := hb)] at h; cases h
  rw [cnaK2_ok (h := hb)] at h
  have hct : c = true := by rw [← hc]; simpa using hb
  subst hct
  have hg12 := hg1.trans hg2
  have hj1 : j + 1 ≤ el := by
    have h1 : j.toNat < el.toNat := UInt64.lt_iff_toNat_lt.mp hj
    apply UInt64.le_iff_toNat_le.mpr; rw [UInt64.toNat_add]; simp <;> omega
  have hes2 : PSlR decNCN es' (eo + (j + 1)) (el - (j + 1)) s2.mem := by
    rw [show eo + (j + 1) = eo + j + 1 by grind, show el - (j + 1) = el - j - 1 by grind]
    exact hes'.grow (fun q => decNCN_mono q) hg12
  obtain ⟨a3, run3, hS3, hg3, hP3⟩ := ih s2.mem m' a2 (j + 1) es' h hS2 (hbs.grow hg12)
    (by rw [decHL_grow hg12 hftb]; exact hft) (by have := hg12.1; omega) (hMc.grow (decTM_mono _) hg12)
    (htl.grow hg12) hl (by rw [decHL_grow hg12 hfvb]; exact hfv) (by have := hg12.1; omega) hj1 hes2 hP2
  refine ⟨a3, ?_, hS3, hg12.trans hg3, hP3⟩
  have hget : ds[i.toNat]? = some (decI w) := by
    rw [List.getElem?_eq_getElem (by rw [decHL_length _ hdd]; exact hi)]; rw [hwD]
  rw [← decE_eq] at hget
  simp only [ConRon.Arena.classNodesAgree, StateT.run_bind, run1, except_ok_bind, Option.getD_some, hget]
  simp only [StateT.run_bind, run2, except_ok_bind, if_true]
  exact run3

end rel

/-- **`class_nodes_agree` refines `classNodesAgree`** (through `target_k53`'s contracts and
stubs): the class's shape (`BSOK`), former types, the inductive hypothesis's class, the recorded
telescope, the datum's variables and the class's entries decoded below the tops, the walk memos
well formed. -/
@[refines ConRon.Arena.classNodesAgree]
theorem classNodesAgree_refines {p : Prog} (P : CnaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl mc teo tel leaf fvo fvl i eo el : Word)
    (bs : BlockShape) (formerTys : List EIdx) (TM : TargetMajor) (tele fvs : List EIdx)
    (es : List NestCtorNf) (hS : StageR dn vis fe s₀.mem a₀) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hMc : DecB (fun m => decTM m mc.toNat) s₀.mem TM) (htl : HSl0 s₀.mem teo tel tele) (hl : H leaf)
    (hfv : decHL s₀.mem fvo.toNat fvl.toNat = some fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hes : PSlR decNCN es eo el s₀.mem) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_nodes_agree"
      [vis, q, fto, ftl, mc, teo, tel, leaf, fvo, fvl, i, eo, el]
    ⦃fun _ s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a₀ ∧
      StageR dn vis fe s'.mem
        (AM.st (ConRon.Arena.classNodesAgree V fe bs formerTys TM tele (decE leaf) fvs i.toNat es) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (cna_spec p P.cna n s₀ vis q fto ftl mc teo tel leaf fvo fvl i eo el) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨a', run, hS', hg, hP'⟩ := cnaW_ok P dn fe vis q fto ftl mc teo tel leaf fvo fvl i eo el bs
    formerTys TM tele fvs n _ _ a₀ 0 es hm hS hbs hft hftb hMc htl hl hfv hfvb UInt64.zero_le
    (by simpa using hes) hP
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hst]; exact hS', hg, hP'⟩

end L.Ind
