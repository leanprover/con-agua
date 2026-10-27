import ConAgua.Arena.RecCheckSpec14

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
    if domsLen <= i { fail R_GENERATED_RECURSOR_A };
    f := IW.u64[domsOff + i];
    b := call target_k53(vis, p, ftOff, ftLen, mc, teleOff, teleLen, leaf, f);
    if b == 0 { fail R_GENERATED_RECURSOR_FIELD_OF };
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
  simp only [cnaK2]; rw [ite_eq_left h]
theorem cnaK2_ok (h : ¬ r.headD 0 = 0) : cnaK2 rest (some (r, m)) = rest m := by
  simp only [cnaK2]; rw [ite_eq_right h]
theorem cnaK1_bad (h : r.headD 0 = 0) : cnaK1 p k vis q fto ftl mc teo tel leaf i rest (some (r, m)) = none := by
  simp only [cnaK1]; rw [ite_eq_left h]
theorem cnaK1_short (h0 : ¬ r.headD 0 = 0) (h : r.tail.tail.headD 0 ≤ i) :
    cnaK1 p k vis q fto ftl mc teo tel leaf i rest (some (r, m)) = none := by
  simp only [cnaK1]; rw [ite_eq_right h0, ite_eq_left h]
theorem cnaK1_ok (h0 : ¬ r.headD 0 = 0) (h : ¬ r.tail.tail.headD 0 ≤ i) :
    cnaK1 p k vis q fto ftl mc teo tel leaf i rest (some (r, m)) =
      cnaK2 rest (callW p k "target_k53" [vis, q, fto, ftl, mc, teo, tel, leaf,
        rdW (m.arr64 IW) (r.tail.headD 0 + i)] m) := by
  simp only [cnaK1]; rw [ite_eq_right h0, ite_eq_right h]
theorem cnaW_exit (h : ¬ j < el) :
    cnaW p (k + 1) m vis q fto ftl mc teo tel leaf fvo fvl i eo el j = some m := by
  simp only [cnaW]; rw [ite_eq_right h]
theorem cnaW_step (h : j < el) :
    cnaW p (k + 1) m vis q fto ftl mc teo tel leaf fvo fvl i eo el j =
      cnaK1 p k vis q fto ftl mc teo tel leaf i
        (fun m' => cnaW p k m' vis q fto ftl mc teo tel leaf fvo fvl i eo el (j + 1))
        (callW p k "target_pi_doms_with" [fvo, fvl, rdW (m.arr64 IW) (rdW (m.arr64 IW) (eo + j) + 4)] m) := by
  simp only [cnaW]; rw [ite_eq_left h]
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
  rcases n with _ | n
  · exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
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
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp only [pdK1])
    rw [pdK1_some] at h
    refine (MFr.ofI1F h1).trans ?_
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
    refine (pdW_mfr n _ _ _ _ _ _ h2).trans ?_
    by_cases h3 : r2.headD 0 = 0
    · rw [pdK2_none (h := h3)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [pdK2_ok (h := h3)] at h
    obtain ⟨⟨r3, m3⟩, h4, h⟩ := of_K h rfl
    rw [pdK3_some] at h
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

end rel

end L.Ind
