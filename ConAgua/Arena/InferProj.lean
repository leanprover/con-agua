import ConAgua.Arena.InferBodyDisp
import ConAgua.Arena.DefEqMidQuick
import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.DefEqLeaves2

/-!
# `inferProj`: `proj_type_at` and `infer_proj_at` (lane `defeq2`, helper `defeq2-proj`)

The callW pattern (`InferBodyLet.lean`): a word model of each function with its callees through
their runs, the L spec by `vcgen`, the refinement from the callees' specs, the twin's run computed
step by step from the callees' runs.

* `proj_type_at(q, i, us, to, tn, pe)` refines `IProjEntry.typeAt` at the entry of the table record
  `q` (`projTypeAt_refines`): `inst_lp` on the body, `pe` pushed onto the argument slice at the
  stack top, `inst_list`.
* `infer_proj_at(vis, sn, i, pe, te, T, us, q)` refines `projAtT`, `inferProj` past the table
  lookup (`inferProjAt_refines`).

The table's words are read from `EREC` after `lvl_eq_c` and `field_sort_zero` ran: `ErecKeptProj`
(a hypothesis, as lane `whnf`'s `ErecKept`) says those two leave the record pool alone.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The words of a projection table record -/

/-- A decoded handle list at words `q + j`, `q + j + 1`: the slice those two words name. -/
theorem hlist_words {k : IdxKind} {a : Array Word} {q : Word} {j : Nat} {l : List (Idx k)}
    (hsz : a.size < 2 ^ 63) (hj : j < 15) (h : hlist? a (q.toNat + j) = some l) :
    hslice? a (rdW a (q + UInt64.ofNat j)).toNat (rdW a (q + UInt64.ofNat (j + 1))).toNat = some l := by
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩ := h
  have r1 : rdW a (q + UInt64.ofNat j) = wo := rdW_ext (fun _ _ h => h) hsz (by omega) hwo
  have r2 : rdW a (q + UInt64.ofNat (j + 1)) = wc :=
    rdW_ext (fun _ _ h => h) hsz (by omega) (by simpa [Nat.add_assoc] using hwc)
  rw [r1, r2]; exact hs

/-- A decoded handle at word `q + j`. -/
theorem hd_word {k : IdxKind} {a : Array Word} {q : Word} {j : Nat} {x : Idx k}
    (hsz : a.size < 2 ^ 63) (hj : j < 16) (h : hd? a (q.toNat + j) = some x) :
    HW (rdW a (q + UInt64.ofNat j)) ∧ x = decI (rdW a (q + UInt64.ofNat j)) := by
  obtain ⟨w, hw, hw32, rfl⟩ := hd?_eq h
  rw [rdW_ext (fun _ _ h => h) hsz hj hw]
  exact ⟨hw32, rfl⟩

/-- **The fields of a decoded projection table** `infer_proj` reads: the level parameters' slice
(words `q + 3`, `q + 4`), the structure's sort (`q + 8`), the bodies' slice (`q + 9`, `q + 10`),
the guards' slice (`q + 11`, `q + 12`). -/
theorem decTbl_fields {a : Array Word} {q : Word} {tbl : IProjTable}
    (h : decTbl a q.toNat = some tbl) (hsz : a.size < 2 ^ 63) :
    hslice? a (rdW a (q + 3)).toNat (rdW a (q + 4)).toNat = some tbl.levelParams ∧
    HW (rdW a (q + 8)) ∧ tbl.structSort = decI (rdW a (q + 8)) ∧
    hslice? a (rdW a (q + 9)).toNat (rdW a (q + 10)).toNat = some tbl.bodies.toList ∧
    hslice? a (rdW a (q + 11)).toNat (rdW a (q + 12)).toNat = some tbl.guards := by
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨tn, -, sn, -, lps, hlps, np, -, ct, -, nf, -, ss, hss, bd, hbd, gd, hgd, off, -, hc⟩ := h
  subst hc
  exact ⟨hlist_words (j := 3) hsz (by decide) hlps, (hd_word (j := 8) hsz (by decide) hss).1,
    (hd_word (j := 8) hsz (by decide) hss).2, by simpa using hlist_words (j := 9) hsz (by decide) hbd,
    hlist_words (j := 11) hsz (by decide) hgd⟩

/-- Element `i` of a decoded slice, or `0` past its end, as L reads it (`if i < cnt { a[off + i] }`). -/
def sliceAt (a : Array Word) (o c i : Word) : Word := if i < c then rdW a (o + i) else 0

/-- **`sliceAt` decodes to `getD … default`.** -/
theorem sliceAt_dec {k : IdxKind} {a : Array Word} {o c : Word} {l : List (Idx k)}
    (hsz : a.size < 2 ^ 63) (h : hslice? a o.toNat c.toNat = some l) (i : Word) :
    HW (sliceAt a o c i) ∧ (decI (sliceAt a o c i) : Idx k) = l.getD i.toNat default := by
  obtain ⟨hl, hg⟩ := hslice?_get h
  unfold sliceAt
  by_cases hi : i < c
  · rw [if_pos hi]
    have hi' : i.toNat < c.toNat := UInt64.lt_iff_toNat_lt.mp hi
    obtain ⟨w, hw, hw32, hl'⟩ := hg i.toNat hi'
    have hb : o.toNat + i.toNat < a.size := (Array.getElem?_eq_some_iff.mp hw).1
    have ho : (o + i).toNat = o.toNat + i.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hr : rdW a (o + i) = w := by simp only [rdW, ho, hw, Option.getD_some]
    rw [hr]
    refine ⟨hw32, ?_⟩
    rw [List.getD_eq_getElem?_getD, hl']; rfl
  · rw [if_neg hi]
    have hi' : ¬ i.toNat < c.toNat := fun h' => hi (UInt64.lt_iff_toNat_lt.mpr h')
    refine ⟨by unfold HW; decide, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-! ## The programs and the callees -/

/-- What `infer_proj`'s three functions need of a program. -/
structure InferProjProg (p : Prog) : Prop where
  leaf : DefEqLeafProg p
  lv : LvlCacheProg p
  fsz : FieldSortZeroProg p
  walk : CoreWalkProg p
  ip : p.lookup "infer_proj" = some inferProjL
  ipa : p.lookup "infer_proj_at" = some inferProjAtL
  pta : p.lookup "proj_type_at" = some projTypeAtL

/-- **`lvl_eq_c` and `field_sort_zero` leave the record pool alone** (new stub assumption, as lane
`whnf`'s `ErecKept`/`ErecKeptRec`): `infer_proj_at` and `proj_type_at` read the table's words
after them. Both write only the level heap (`LH`, `CTL[192]`) and, for `lvl_eq_c`, its verdict
memo (`lqSch`); their proofs (`CoreLevels.lean`, `InferFieldSort.lean`) build these frames but do
not export them. -/
def ErecKeptProj (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    (f = "lvl_eq_c" ∨ f = "field_sort_zero") → callW p n f vs m = some (r, m') →
    m'.arr64 EREC = m.arr64 EREC

/-! ## `proj_type_at` -/

/-- The body word `proj_type_at` reads: entry `i` of the bodies' slice, or `0`. -/
def bodyW (m : Mem) (q i : Word) : Word :=
  sliceAt (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 9)) (rdW (m.arr64 EREC) (q + 10)) i

/-- The guard word `infer_proj_at` reads: entry `i` of the guards' slice, or `0`. -/
def guardW (m : Mem) (q i : Word) : Word :=
  sliceAt (m.arr64 EREC) (rdW (m.arr64 EREC) (q + 11)) (rdW (m.arr64 EREC) (q + 12)) i

/-- `pe` pushed at the top of the slice `(to, tn)`, the top one past it (L's word order). -/
def ptPush (m : Mem) (to tn pe : Word) : Mem :=
  (m.set64 SPN (to + tn) pe).set64 CTL 136 (to + tn + 1)

theorem ptPush_eq (m : Mem) (to tn pe : Word) : ptPush m to tn pe = spPush m to tn pe := by
  simp only [ptPush, spPush, UInt64.add_assoc]

section ptaK
variable (p : Prog) (n : Nat) (to tn pe : Word)

/-- After `inst_list`: the top put back at the slice's end. -/
def ptaK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if ¬ (136 : Word).toNat < (m.arr64 CTL).size then none
    else some (r.headD 0, m.set64 CTL 136 (to + tn))

/-- After `inst_lp`: the push, then `inst_list` on the slice with `pe`. -/
def ptaK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if m.len64 SPN ≤ to + tn then none
    else if ¬ (to + tn).toNat < (m.arr64 SPN).size then none
    else if ¬ (136 : Word).toNat < (m.arr64 CTL).size then none
    else ptaK2 to tn (callW p n "inst_list" [r.headD 0, to, tn + 1, 0] (ptPush m to tn pe))

end ptaK

/-- **The model of `proj_type_at`.** -/
def ptaW (p : Prog) (n : Nat) (m : Mem) (q i us to tn pe : Word) : Option (Word × Mem) :=
  ptaK1 p n to tn pe (callW p n "inst_lp" [rdW (m.arr64 EREC) (q + 3), rdW (m.arr64 EREC) (q + 4),
    us, bodyW m q i] m)

theorem projTypeAt_spec (p : Prog) (hp : InferProjProg p) (n : Nat) (s₀ : St)
    (q i us to tn pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_type_at" [q, i, us, to, tn, pe]
    ⦃fun r s' => LocEq s' s₀ ∧ ptaW p n s₀.mem q i us to tn pe = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.pta]
  simp only [callFn, projTypeAtL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      callW_spec p n "inst_lp", callW_spec p n "inst_list"] <;>
  simp_all [ptaW, ptaK1, ptaK2, ptPush, bodyW, sliceAt, Cmp.eval, LocEq, BinOp.eval,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ, size_set64, CTL, EREC, SPN, w_lt_false]

/-! ## Refinement helpers -/

/-- **A twin run that succeeded, with the relation after it**, is a `CoreRef`. -/
theorem ipRef_of_run {α : Type} [Inhabited α] {T : AM α} {a₀ a' : AState} {v : α}
    {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv}
    {M M' : ModeMaps} {eb : Word} {r : List Word} {ok : List Word → Prop}
    (hrun : T.run a₀ = .ok (v, a')) (hv : v = dec r) (hS : CoreS dn m a' vis fe M' eb)
    (hK : KeptAll M M' eb) (hSt : StackKept m₀ m) (hr : ok r) :
    CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hok, by rw [hst]; exact ⟨M', hS, hK, hSt⟩, by rw [hres, hv], hr⟩

/-- A callee's `CoreRef` as a run of the twin. -/
theorem ipRun_of_ref {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) : T.run a₀ = .ok (dec r, AM.st T a₀) := by
  rw [AM.run_of_ok _ _ h.1, h.2.2.1]

theorem array_getD_toList {α : Type} (xs : Array α) (j : Nat) (d : α) :
    xs.getD j d = xs.toList.getD j d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## `proj_type_at` refines `IProjEntry.typeAt` -/

/-- **`proj_type_at` refines `IProjEntry.typeAt`** at the entry of the table record `q`, the
arguments the slice `(to, tn)` at the stack top. -/
@[refines ConRon.Arena.IProjEntry.typeAt]
theorem projTypeAt_refines (p : Prog) (hp : InferProjProg p) (hlp : InstLPOK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb q i us to tn pe : Word) (tbl : IProjTable) (xs : List EIdx)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hq : decTbl (s₀.mem.arr64 EREC) q.toNat = some tbl)
    (hus : HW us) (hpe : HW pe) (hsp : SpineR s₀.mem to tn xs.toArray)
    (htop : spTop s₀.mem = to + tn) :
    CoreSpec p (n + 1) "proj_type_at" [q, i, us, to, tn, pe]
      ((tbl.entry i.toNat).typeAt (decI us) xs (decE pe)) decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (projTypeAt_spec p hp n s₀ q i us to tn pe)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hil := hp.walk.instListOK
  obtain ⟨hlps, -, -, hbd, -⟩ := decTbl_fields hq hS.erec
  obtain ⟨hbw, hbdec⟩ := sliceAt_dec (k := .expr) hS.erec hbd i
  have hbody : (decE (bodyW s.mem q i) : EIdx) = (tbl.entry i.toNat).body := by
    simp only [IProjTable.entry, array_getD_toList]; exact hbdec
  unfold ptaW at hW
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (hlp n s a₀ dn vis fe M eb _ _ us (bodyW s.mem q i) tbl.levelParams
    hS hbw hus hlps) hc1
  rw [hbody] at h₁
  have hrun1 := ipRun_of_ref h₁
  obtain ⟨-, ⟨M₁, hS₁, hK₁, hSt₁⟩, -, hrw1⟩ := h₁
  have hbnd := hsp.bound
  have hspn := hS.spn
  have hadd : (to + tn).toNat = to.toNat + tn.toNat := addW _ _ (by omega)
  simp only [ptaK1] at hW
  by_cases g1 : m₁.len64 SPN ≤ to + tn
  · rw [if_pos g1] at hW; cases hW
  rw [if_neg g1] at hW
  by_cases g2 : ¬ (to + tn).toNat < (m₁.arr64 SPN).size
  · rw [if_pos g2] at hW; cases hW
  rw [if_neg g2] at hW
  by_cases g3 : ¬ (136 : Word).toNat < (m₁.arr64 CTL).size
  · rw [if_pos g3] at hW; cases hW
  rw [if_neg g3, ptPush_eq] at hW
  have g2' : (to + tn).toNat < (m₁.arr64 SPN).size := Classical.not_not.mp g2
  have g3' : (136 : Word).toNat < (m₁.arr64 CTL).size := Classical.not_not.mp g3
  have htn1 : (tn + 1).toNat = tn.toNat + 1 := addW _ _ (by have h1 := hsp.bound; have h2 := hS.spn; simp only [UInt64.toNat_one]; omega)
  have htopv : to.toNat + tn.toNat ≤ (spTop s.mem).toNat := by rw [htop, hadd]; exact Nat.le_refl _
  have hsp₁ : SpineR m₁ to tn xs.toArray := hsp.keep hSt₁.2.1 hSt₁.2.2 htopv hspn
  obtain ⟨hspR, htop₂, -, -, -⟩ := spPush_step (m₀ := m₁) hS₁.spn hsp₁ (fun _ _ => rfl) rfl g3' g2' hpe
  have hS₂ := hS₁.frame_stk (spnCtl_frame m₁ (to + tn) pe (to + (tn + 1))) (by simp) (by simp)
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  have hsz₁ : (m₁.arr64 SPN).size = (s.mem.arr64 SPN).size := hSt₁.2.1
  have hadd1 : (to + (tn + 1)).toNat = to.toNat + (tn + 1).toNat := addW _ _ (by omega)
  have h₂ := CoreSpec.of_callW (hil n ⟨spPush m₁ to tn pe, Locals.init []⟩ (AM.st _ a₀) dn vis fe M₁ eb
    (r₁.headD 0) to (tn + 1) 0 _ hS₂ hrw1 hspR (by rw [htop₂, hadd1]; exact Nat.le_refl _)) hc2
  have hrun2 := ipRun_of_ref h₂
  obtain ⟨-, ⟨M₂, hS₂', hK₂, hSt₂⟩, -, hrw2⟩ := h₂
  simp only [ptaK2] at hW
  by_cases g4 : ¬ (136 : Word).toNat < (m₂.arr64 CTL).size
  · rw [if_pos g4] at hW; cases hW
  rw [if_neg g4] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  rw [← hm]
  have hfin : to + tn = rdW (s.mem.arr64 CTL) 136 := htop.symm
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0] at hrun2 hS₂'
  refine ipRef_of_run (M' := M₂) (v := decH r₂) (a' := AM.st (instantiateListFast coreWalkFuel
    (decE (r₁.headD 0)) (xs.toArray.push (decE pe)) 0) (AM.st (instLPFast coreWalkFuel
    tbl.levelParams (decI us) (tbl.entry i.toNat).body) a₀)) ?_ (by simp only [decH, hr]) ?_ (hK₁.trans hK₂) ?_
    (by unfold ResH; rw [← hr]; exact hrw2)
  · simp only [IProjEntry.typeAt, show (tbl.entry i.toNat).levelParams = tbl.levelParams from rfl,
      StateT.run_bind, hrun1, except_ok_bind]
    exact hrun2
  · exact hS₂'.frame_stk (MemFrame.setCtl m₂ 136 _) (by simp) (by simp)
  · rw [hfin]
    refine StackKept.restore ?_ ?_ (Classical.not_not.mp g4)
    · intro j hj
      have hj' : j.toNat < to.toNat + tn.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hj; rw [htop, hadd] at this; exact this
      have hj2 : j < spTop (spPush m₁ to tn pe) := by
        rw [htop₂]; apply UInt64.lt_iff_toNat_lt.mpr; rw [hadd1]; omega
      rw [hSt₂.2.2 j hj2]
      simp only [spPush]
      rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
        have := congrArg UInt64.toNat h; rw [hadd] at this; omega)]
      exact hSt₁.2.2 j hj
    · rw [hSt₂.2.1]; simp only [spPush, size_set64]; exact hsz₁

end L.Arena
