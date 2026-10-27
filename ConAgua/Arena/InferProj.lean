import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.DefEqLeaves2
import ConAgua.Arena.CoreDen
import ConAgua.Arena.InferBodySpine
import ConAgua.Census.Attr

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
  obtain ⟨sn, -, lps, hlps, np, -, ct, -, nf, -, ss, hss, bd, hbd, gd, hgd, hc⟩ := h
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
  · rw [ite_eq_left hi]
    have hi' : i.toNat < c.toNat := UInt64.lt_iff_toNat_lt.mp hi
    obtain ⟨w, hw, hw32, hl'⟩ := hg i.toNat hi'
    have hb : o.toNat + i.toNat < a.size := (Array.getElem?_eq_some_iff.mp hw).1
    have ho : (o + i).toNat = o.toNat + i.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hr : rdW a (o + i) = w := by simp only [rdW, ho, hw, Option.getD_some]
    rw [hr]
    refine ⟨hw32, ?_⟩
    rw [List.getD_eq_getElem?_getD, hl']; rfl
  · rw [ite_eq_right hi]
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
def projBodyW (m : Mem) (q i : Word) : Word :=
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
    us, projBodyW m q i] m)

theorem projTypeAt_spec (p : Prog) (hp : InferProjProg p) (n : Nat) (s₀ : St)
    (q i us to tn pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_type_at" [q, i, us, to, tn, pe]
    ⦃fun r s' => LocEq s' s₀ ∧ ptaW p n s₀.mem q i us to tn pe = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.pta]
  simp only [callFn, projTypeAtL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      callW_spec p n "inst_lp", callW_spec p n "inst_list"] <;>
  simp_all [ptaW, ptaK1, ptaK2, ptPush, projBodyW, sliceAt, Cmp.eval, LocEq, BinOp.eval,
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
  have hbody : (decE (projBodyW s.mem q i) : EIdx) = (tbl.entry i.toNat).body := by
    simp only [IProjTable.entry, array_getD_toList]; exact hbdec
  unfold ptaW at hW
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (hlp n s a₀ dn vis fe M eb _ _ us (projBodyW s.mem q i) tbl.levelParams
    hS hbw hus hlps) hc1
  rw [hbody] at h₁
  have hrun1 := ipRun_of_ref h₁
  obtain ⟨-, ⟨M₁, hS₁, hK₁, hSt₁⟩, -, hrw1⟩ := h₁
  have hbnd := hsp.bound
  have hspn := hS.spn
  have hadd : (to + tn).toNat = to.toNat + tn.toNat := addW _ _ (by omega)
  simp only [ptaK1] at hW
  obtain ⟨g1, hW⟩ := of_ite_none hW
  obtain ⟨g2, hW⟩ := of_ite_none hW
  have g3 : ¬ ¬ (136 : Word).toNat < (m₁.arr64 CTL).size := fun g3 => by rw [ite_eq_left g3] at hW; cases hW
  rw [ite_eq_right g3, ptPush_eq] at hW
  have g2' : (to + tn).toNat < (m₁.arr64 SPN).size := Classical.not_not.mp g2
  have g3' : (136 : Word).toNat < (m₁.arr64 CTL).size := Classical.not_not.mp g3
  have htn1 : (tn + 1).toNat = tn.toNat + 1 := addW _ _ (by have h1 := hsp.bound; have h2 := hS.spn; simp only [UInt64.toNat_one]; omega)
  have htopv : to.toNat + tn.toNat ≤ (spTop s.mem).toNat := by rw [htop, hadd]; exact Nat.le_refl _
  have hsp₁ : SpineR m₁ to tn xs.toArray := hsp.keep hSt₁.size hSt₁.below htopv hspn
  obtain ⟨hspR, htop₂, -, -, -, -, -⟩ := spPush_step (m₀ := m₁) hS₁.spn hsp₁ (fun _ _ => rfl) rfl
    (BKept.refl _) (PoolGrew.refl _) g3' g2' hpe
  have hS₂ := hS₁.frame_stk (spnCtl_frame m₁ (to + tn) pe (to + (tn + 1))) (by simp) (by simp)
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  have hsz₁ : (m₁.arr64 SPN).size = (s.mem.arr64 SPN).size := hSt₁.size
  have hadd1 : (to + (tn + 1)).toNat = to.toNat + (tn + 1).toNat := addW _ _ (by omega)
  have h₂ := CoreSpec.of_callW (hil n ⟨spPush m₁ to tn pe, Locals.init []⟩ (AM.st _ a₀) dn vis fe M₁ eb
    (r₁.headD 0) to (tn + 1) 0 _ hS₂ hrw1 hspR (by rw [htop₂, hadd1]; exact Nat.le_refl _)) hc2
  have hrun2 := ipRun_of_ref h₂
  obtain ⟨-, ⟨M₂, hS₂', hK₂, hSt₂⟩, -, hrw2⟩ := h₂
  simp only [ptaK2] at hW
  obtain ⟨g4, hW⟩ := of_ite_none hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
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
    have hfp : MemFrame [SPN] [136] m₁ (spPush m₁ to tn pe) := spnCtl_frame m₁ (to + tn) pe (to + (tn + 1))
    refine StackKept.restore ?_ ?_
      (hSt₁.bstk.trans ((BKept.of_frame hfp (by decide) (by decide)).trans hSt₂.bstk))
      (hSt₁.pool.trans ((PoolGrew.of_frame hfp (by decide) (by decide)).trans hSt₂.pool))
      (Classical.not_not.mp g4)
    · intro j hj
      have hj' : j.toNat < to.toNat + tn.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hj; rw [htop, hadd] at this; exact this
      have hj2 : j < spTop (spPush m₁ to tn pe) := by
        rw [htop₂]; apply UInt64.lt_iff_toNat_lt.mpr; rw [hadd1]; omega
      rw [hSt₂.below j hj2]
      simp only [spPush]
      rw [spW_setCtl, spW_set64_ne _ _ _ _ (fun h => by
        have := congrArg UInt64.toNat h; rw [hadd] at this; omega)]
      exact hSt₁.below j hj
    · rw [hSt₂.size]; simp only [spPush, size_set64]; exact hsz₁

/-! ## The twin past the table lookup -/

/-- `inferProj`'s propositional-structure test and the type (its innermost block, copied). -/
def fszTail (entry : IProjEntry) (us : LsIdx) (targs : List EIdx) (pe : EIdx) : AM EIdx := do
  let ks ← readNamesM entry.levelParams
  let vs ← readLevelsM us
  let fs ← readLevelM entry.fieldSort
  if !(ConLeche.Level.isEquiv (ConLeche.Level.subst ks vs fs) .zero == some true) then
    fail (.invalid "projection from a propositional structure must be a proposition")
  else entry.typeAt us targs pe

/-- **`inferProj` past the table lookup** (copied; `inferProj_hit`): the subject type's arguments,
the shape checks, the propositional-structure test, the type. -/
def projAtT (sn T : NIdx) (us : LsIdx) (entry : IProjEntry) (te pe : EIdx) : AM EIdx := do
  let targs ← getAppArgs coreWalkFuel te
  if T != sn then
    fail (.invalid "invalid projection: the node names another structure")
  else if targs.length != entry.numParams then
    fail (.invalid "projection parameter mismatch")
  else
    match ← viewLsLen us with
    | none => failDanglingLs
    | some usl =>
    if usl = entry.levelParams.length then do
      let z ← zeroLevel
      if (← lvlEq? entry.structSort z) == some true then fszTail entry us targs pe
      else entry.typeAt us targs pe
    else fail (.notImplemented "projection without a native entry")

/-- **`inferProj` at a hit** is `projAtT` from the state after the lookup. -/
theorem inferProj_hit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ a₂ : AState) (it te hh : EIdx) (T : NIdx) (us : LsIdx) (entry : IProjEntry)
    (h1 : (r.infer d pe).run a = .ok (it, a₁)) (h2 : (r.whnf d it).run a₁ = .ok (te, a₂))
    (h3 : (getAppFn coreWalkFuel te).run a₂ = .ok (hh, a₂)) (ht : (hh.tag == ETag.const) = true)
    (hv : a₂.store.view hh = some (.const T us))
    (h4 : fe.findProj? T i = some entry) :
    (inferProj r fe d sn i pe).run a = (projAtT sn T us entry te pe).run a₂ := by
  simp only [inferProj, StateT.run_bind, h1, except_ok_bind, h2, h3, ht, ite_true,
    view_run _ _ _ hv, h4]
  rfl

/-- **The test's run is the twin's three readbacks** (`fieldSortZeroT`, `Knot.lean`). -/
theorem fszTail_run (entry : IProjEntry) (us : LsIdx) (targs : List EIdx) (pe : EIdx)
    (a a' : AState) (b : Bool)
    (h : (fieldSortZeroT entry.levelParams us entry.fieldSort).run a = .ok (b, a')) :
    (fszTail entry us targs pe).run a =
      (if !b then fail (.invalid "projection from a propositional structure must be a proposition")
        else entry.typeAt us targs pe).run a' := by
  simp only [fieldSortZeroT, StateT.run_bind] at h
  simp only [fszTail, StateT.run_bind]
  cases h1 : (readNamesM entry.levelParams).run a with
  | error e => rw [h1] at h; cases h
  | ok x =>
  rw [h1] at h
  simp only [except_ok_bind] at h ⊢
  cases h2 : (readLevelsM us).run x.2 with
  | error e => rw [h2] at h; cases h
  | ok y =>
  rw [h2] at h
  simp only [except_ok_bind] at h ⊢
  cases h3 : (readLevelM entry.fieldSort).run y.2 with
  | error e => rw [h3] at h; cases h
  | ok z =>
  rw [h3] at h
  simp only [except_ok_bind] at h ⊢
  cases h
  rfl

/-- **`lvlEq?` leaves the store alone** (it writes the readback and verdict caches only). -/
theorem lvlEq?_store (u v : LIdx) (a a' : AState) (o : Option Bool) (lu lv : ConLeche.Level)
    (hu : denoteL a.store.ls u = some lu) (hv : denoteL a.store.ls v = some lv) (hc : ReadLCOK a)
    (h : (lvlEq? u v).run a = .ok (o, a')) : a'.store = a.store := by
  cases hm : a.caches.lvlEqC[(u, v)]? with
  | some r => rw [lvlEq?_hit a u v r hm] at h; cases h; rfl
  | none =>
    obtain ⟨X, hr, -⟩ := lvlEq?_miss a u v lu lv hu hv hc hm
    rw [hr] at h; cases h; rfl

theorem w_le_false {a b : Word} (h : a < b) : (b ≤ a) = False := eq_false (UInt64.not_le.mpr h)

/-! ## `infer_proj_at` -/

section ipaK
variable (p : Prog) (n : Nat) (top i pe us q to tn : Word)

/-- After `proj_type_at`: the top put back. -/
def ipaK5 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if ¬ (136 : Word).toNat < (m.arr64 CTL).size then none
    else some (r.headD 0, m.set64 CTL 136 top)

/-- After `field_sort_zero`: its verdict, then the type. -/
def ipaK4 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then none
    else ipaK5 top (callW p n "proj_type_at" [q, i, us, to, tn, pe] m)

/-- After `lvl_eq_c`: the propositional-structure test when the structure is a `Prop`. -/
def ipaK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if 2 ≤ r.headD 0 then
      ipaK4 p n top i pe us q to tn (callW p n "field_sort_zero"
        [rdW (m.arr64 EREC) (q + 3), rdW (m.arr64 EREC) (q + 4), us, guardW m q i] m)
    else ipaK5 top (callW p n "proj_type_at" [q, i, us, to, tn, pe] m)

/-- After `ls_node`: the level count, then `lvl_eq_c` against the pinned zero. -/
def ipaK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.tail.headD 0 ≠ rdW (m.arr64 EREC) (q + 4) then none
    else ipaK3 p n top i pe us q to tn
      (callW p n "lvl_eq_c" [rdW (m.arr64 EREC) (q + 8), rdW (m.arr64 PINS) 53] m)

end ipaK

/-- After `get_app_args`: the structure and the parameter count, then `ls_node`. -/
def ipaK1 (p : Prog) (n : Nat) (top sn i pe T us q : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if T ≠ sn then none
    else if r.tail.headD 0 ≠ rdW (m.arr64 EREC) (q + 5) then none
    else ipaK2 p n top i pe us q (r.headD 0) (r.tail.headD 0) (callW p n "ls_node" [us] m)

/-- **The model of `infer_proj_at`.** -/
def ipaW (p : Prog) (n : Nat) (m : Mem) (sn i pe te T us q : Word) : Option (Word × Mem) :=
  ipaK1 p n (rdW (m.arr64 CTL) 136) sn i pe T us q (callW p n "get_app_args" [te] m)

theorem inferProjAt_spec (p : Prog) (hp : InferProjProg p) (n : Nat) (s₀ : St)
    (vis sn i pe te T us q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "infer_proj_at" [vis, sn, i, pe, te, T, us, q]
    ⦃fun r s' => LocEq s' s₀ ∧ ipaW p n s₀.mem sn i pe te T us q = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ipa]
  simp only [callFn, inferProjAtL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64_spec,
      callW_spec p n "get_app_args", callW_spec p n "ls_node", pinWord_rd p hp.leaf.pinword n,
      callW_spec p n "lvl_eq_c", callW_spec p n "field_sort_zero", callW_spec p n "proj_type_at"] <;>
  simp_all [ipaW, ipaK1, ipaK2, ipaK3, ipaK4, ipaK5, guardW, sliceAt, Cmp.eval, LocEq, BinOp.eval,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Sig.retVal, Sig.retOr,
    Locals.init_cons_zero, Locals.init_cons_succ, CTL, EREC, PINS, w_lt_false,
    w_le_false]

/-! ## `infer_proj_at` refines `projAtT` -/

/-- **The callees of `infer_proj` with no proof here** (each a named hypothesis). -/
structure InferProjCallees (p : Prog) : Prop where
  /-- Stored levels read back under `CoreS` (`StoreDen.lean`; meant as a field of `CoreS`). -/
  den : CoreDen
  /-- Lane `whnf`'s stubs (`WhnfCore.lean`, `WhnfBase.lean`). -/
  findProj : FindProjOK p
  projFound : ProjFound p
  erec : ErecKept p
  instLP : InstLPOK p
  /-- `lvl_eq_c` and `field_sort_zero` keep `EREC` (this file). -/
  erecProj : ErecKeptProj p

/-- `lvl_eq_c`'s answer word: `2` and above is `some true` (`decO`). -/
theorem decO_true (w : Word) : (decO w == some true) = decide (2 ≤ w) := by
  unfold decO
  by_cases h0 : w = 0
  · subst h0; decide
  by_cases h1 : w = 1
  · subst h1; decide
  have h2 : 2 ≤ w := by
    have a0 : w.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
    have a1 : w.toNat ≠ 1 := fun e => h1 (UInt64.toNat_inj.mp e)
    exact UInt64.le_iff_toNat_le.mpr (by simp; omega)
  simp [h0, h1, h2]

/-- `lvl_eq_c` cannot run on fuel below two (as `WhnfIotaRefine4.lean`'s `lvlEqC_small`, which this
file does not import). -/
theorem ip_lvlEqC_small (p : Prog) (hp : p.lookup "lvl_eq_c" = some lvlEqCL) (n : Nat) (hn : n < 2)
    (vs : List Word) (m : Mem) : callW p n "lvl_eq_c" vs m = none := by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · have : n = 0 := by omega
    subst this; exact callW_zero _ _ _ _
  · have : n = 1 := by omega
    subst this
    cases hc : callW p 1 "lvl_eq_c" vs m with
    | none => rfl
    | some q =>
      exfalso
      obtain ⟨t, -, hF⟩ := triple_of_callW (p := p) (n := 1) (f := "lvl_eq_c") (args := vs)
        (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => False) (by
          rw [invoke_eq _ hp]
          simp only [callFn, lvlEqCL]
          vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
            callW_spec p 0 "lq_find", callW_spec p 0 "lvl_eq_rec"] <;>
          simp_all [callW_zero]) hc
      exact hF

theorem ip_viewLsLen_run (a : AState) (h : LsIdx) :
    (viewLsLen h).run a = .ok (a.store.lss.viewLen h, a) := rfl

/-- **`projAtT` up to its branch on `lvlEq?`.** -/
theorem projAtT_run (sn T : NIdx) (us : LsIdx) (entry : IProjEntry) (te pe : EIdx)
    (a a₃ : AState) (xs : List EIdx) (l : Nat) (z : LIdx) (o : Option Bool)
    (hxs : (getAppArgs coreWalkFuel te).run a = .ok (xs, a)) (hT : T = sn)
    (hlen : xs.length = entry.numParams) (hvl : a.store.lss.viewLen us = some l)
    (hl : l = entry.levelParams.length) (hz : zeroLevel.run a = .ok (z, a))
    (hlv : (lvlEq? entry.structSort z).run a = .ok (o, a₃)) :
    (projAtT sn T us entry te pe).run a =
      (if o == some true then fszTail entry us xs pe else entry.typeAt us xs pe).run a₃ := by
  subst hT hl
  simp only [projAtT, StateT.run_bind, hxs, except_ok_bind, bne_self_eq_false, hlen,
    Bool.false_eq_true, ↓reduceIte, ip_viewLsLen_run, hvl, hz, hlv]

/-- **`infer_proj_at` refines `projAtT`** (`inferProj` past the table lookup) at the table record
`q` of field `i`, the subject type `te` headed by `T.{us}`. -/
@[refines_part ConRon.Arena.inferProj "past the table lookup (projAtT)"]
theorem inferProjAt_refines (p : Prog) (hp : InferProjProg p) (hc : InferProjCallees p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb sn i pe te T us q : Word) (tbl : IProjTable)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hq : decTbl (s₀.mem.arr64 EREC) q.toNat = some tbl)
    (hfe : ∃ c, fe.findTable? c = some tbl)
    (hi : i.toNat < tbl.numFields) (hus : HW us) (hte : HW te) (hpe : HW pe)
    (hden : ∃ ls, denoteLs a₀.store.lss (decI us) = some ls) :
    CoreSpec p (n + 1) "infer_proj_at" [vis, sn, i, pe, te, T, us, q]
      (projAtT (decI sn) (decI T) (decI us) (tbl.entry i.toNat) (decE te) (decE pe)) decH
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (inferProjAt_spec p hp n s₀ vis sn i pe te T us q)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨cT, hfeT⟩ := hfe
  unfold ipaW at hW
  -- `get_app_args`
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, ho₁, htop₁, xs, hxs, hsp₁⟩ := triple_of_callW
    (getAppArgs_refines p hp.leaf.core.spine n s a₀ hS.arena.1 te hte hS.spn) hc1
  rw [ht₁] at hf₁ hg₁ htop₁ hsp₁
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hE₁ : m₁.arr64 EREC = s.mem.arr64 EREC := hf₁.1 EREC (by simp [SPN, EREC]) (by decide)
  have hq₁ : decTbl (m₁.arr64 EREC) q.toNat = some tbl := by rw [hE₁]; exact hq
  simp only [ipaK1] at hW
  obtain ⟨g1, hW⟩ := of_ite_none hW
  have hTs : T = sn := Classical.not_not.mp g1
  obtain ⟨g2, hW⟩ := of_ite_none hW
  have g2' : r₁.tail.headD 0 = rdW (m₁.arr64 EREC) (q + 5) := Classical.not_not.mp g2
  -- `ls_node`
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  obtain ⟨t₂, ht₂, ht₂s, hne₂, hr₂⟩ :=
    triple_of_callW (lsNode_spec p hp.lv.lsnode n { s with mem := m₁ } us) hc2
  have hm₂ : m₂ = m₁ := by rw [← ht₂, ht₂s]
  subst hm₂
  obtain ⟨o₂, l₂, hl₂⟩ : ∃ o l, lsNodeW m₂ us = [o, l] := by
    rcases lsNodeW_cases m₂ us with h | h
    · rw [h] at hr₂; exact absurd hr₂ hne₂
    · exact h
  have hr₂' : r₂ = [o₂, l₂] := by rw [hr₂]; exact hl₂
  subst hr₂'
  have hvl : a₀.store.lss.viewLen (decI us) = some l₂.toNat := lsNodeW_viewLen hS₁.arena.1 hus hl₂
  simp only [ipaK2] at hW
  obtain ⟨g3, hW⟩ := of_ite_none hW
  have g3' : l₂ = rdW (m₂.arr64 EREC) (q + 4) := by simpa using g3
  -- the table's words
  obtain ⟨hlp, hnp, -, -, -⟩ := decTbl_words hq₁ hS₁.erec
  obtain ⟨-, hss, hssd, -, -⟩ := decTbl_fields hq₁ hS₁.erec
  have hlen : xs.length = (tbl.entry i.toNat).numParams := by
    have := hsp₁.size; simp only [List.size_toArray] at this
    rw [this, g2']; exact hnp.symm
  have hlpl : l₂.toNat = (tbl.entry i.toNat).levelParams.length := by rw [g3']; exact hlp.symm
  -- the pinned zero
  have hP := hS₁.pins
  have hzw : pinW m₂ 53 = rdW (m₂.arr64 PINS) 53 := pinW_rdW m₂ 53 53 rfl
  have hz32 : HW (rdW (m₂.arr64 PINS) 53) := by rw [← hzw]; exact hP.lv_lt.2.1
  have hzl : (zeroLevel).run a₀ = .ok (decI (rdW (m₂.arr64 PINS) 53), a₀) := by
    rw [← hzw]; exact pinZeroLevel_run hP
  -- readbacks
  have hD := hc.den dn m₂ a₀ vis fe M eb hS₁
  obtain ⟨lz, hdz⟩ := hD.zero
  rw [hP.zeroLevel, hzw] at hdz
  obtain ⟨⟨lss, hdss⟩, -, -⟩ := hD.proj cT tbl hfeT
  rw [hssd] at hdss
  -- `lvl_eq_c`
  rcases Nat.lt_or_ge n 2 with hsm | hbig
  · rw [ip_lvlEqC_small p hp.lv.c n hsm] at hW; cases hW
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  have h₃ := CoreSpec.of_callW (lvlEqC_refines p hp.lv N ⟨m₂, Locals.init []⟩ a₀ dn vis fe M eb hS₁
    _ _ hss hz32 _ _ hdss hdz) hc3
  have hrun3 := ipRun_of_ref h₃
  obtain ⟨-, ⟨M₃, hS₃, hK₃, hSt₃⟩, -, -⟩ := h₃
  have hE₃ : m₃.arr64 EREC = m₂.arr64 EREC := hc.erecProj _ _ _ _ _ _ (Or.inl rfl) hc3
  have hq₃ : decTbl (m₃.arr64 EREC) q.toNat = some tbl := by rw [hE₃]; exact hq₁
  have hst₃ := lvlEq?_store _ _ _ _ _ _ _ hdss hdz hS.readL hrun3
  have hss' : (tbl.entry i.toNat).structSort = decI (rdW (m₂.arr64 EREC) (q + 8)) := hssd
  have hT1 := projAtT_run (decI sn) (decI T) (decI us) (tbl.entry i.toNat) (decE te) (decE pe) a₀ _
    xs l₂.toNat _ _ hxs (by rw [hTs]) hlen hvl hlpl hzl (by rw [hss']; exact hrun3)
  rw [decO_true] at hT1
  -- the slice and the top for `proj_type_at`
  have hto : r₁.headD 0 = spTop s.mem := ho₁
  have htop₂ : spTop m₂ = r₁.headD 0 + r₁.tail.headD 0 := by rw [htop₁, hto]
  have hspn₁ := hS₁.spn
  have hbnd := hsp₁.bound
  have htopv : (r₁.headD 0).toNat + (r₁.tail.headD 0).toNat ≤ (spTop m₂).toNat := by
    rw [htop₂, addW _ _ (by omega)]; exact Nat.le_refl _
  have hfin : rdW (s.mem.arr64 CTL) 136 = spTop s.mem := rfl
  simp only [ipaK3] at hW
  by_cases g4 : 2 ≤ r₃.headD 0
  · rw [ite_eq_left g4] at hW
    rw [ite_eq_left (by simpa using g4)] at hT1
    -- `field_sort_zero`
    obtain ⟨hlps₃, -, -, -, hgd₃⟩ := decTbl_fields hq₃ hS₃.erec
    obtain ⟨hfw, hfdec⟩ := sliceAt_dec (k := .level) hS₃.erec hgd₃ i
    have hD₃ := hc.den dn m₃ _ vis fe M₃ eb hS₃
    obtain ⟨-, hgds, hks⟩ := hD₃.proj cT tbl hfeT
    obtain ⟨lf, hdf⟩ := hgds i.toNat hi
    rw [← hfdec] at hdf
    have hdus : ∃ ls, denoteLs (AM.st (lvlEq? (decI (rdW (m₂.arr64 EREC) (q + 8)))
        (decI (rdW (m₂.arr64 PINS) 53))) a₀).store.lss (decI us) = some ls := by
      rw [hst₃]; exact hden
    obtain ⟨r₄, m₄, hc4, hW⟩ := callW_cases rfl hW
    have h₄ := CoreSpec.of_callW (fieldSortZero_core p hp.fsz (N + 2) ⟨m₃, Locals.init []⟩ _ dn vis fe
      M₃ eb _ _ us (guardW m₃ q i) tbl.levelParams hS₃ hus hfw hlps₃ hD₃.readN hks hdus ⟨lf, hdf⟩) hc4
    have hrun4 := ipRun_of_ref h₄
    obtain ⟨-, ⟨M₄, hS₄, hK₄, hSt₄⟩, -, -⟩ := h₄
    have hE₄ : m₄.arr64 EREC = m₃.arr64 EREC := hc.erecProj _ _ _ _ _ _ (Or.inr rfl) hc4
    have hq₄ : decTbl (m₄.arr64 EREC) q.toNat = some tbl := by rw [hE₄]; exact hq₃
    simp only [ipaK4] at hW
    obtain ⟨g5, hW⟩ := of_ite_none hW
    have hb : decBool r₄ = true := by simp only [decBool, bne_iff_ne]; exact g5
    have hfs : (tbl.entry i.toNat).fieldSort = decI (guardW m₃ q i) := hfdec.symm
    have hT2 := fszTail_run (tbl.entry i.toNat) (decI us) xs (decE pe) _ _ _
      (by rw [hfs]; exact hrun4)
    rw [hb] at hT2
    -- `proj_type_at`
    have hSt14 := (hSt₃.trans hSt₄)
    have hsp₄ : SpineR m₄ (r₁.headD 0) (r₁.tail.headD 0) xs.toArray :=
      hsp₁.keep hSt14.size hSt14.below htopv hspn₁
    obtain ⟨r₅, m₅, hc5, hW⟩ := callW_cases rfl hW
    have h₅ := CoreSpec.of_callW (projTypeAt_refines p hp hc.instLP (N + 1) ⟨m₄, Locals.init []⟩ _ dn
      vis fe M₄ eb q i us _ _ pe tbl xs hS₄ hq₄ hus hpe hsp₄ (by rw [hSt14.1, htop₂])) hc5
    have hrun5 := ipRun_of_ref h₅
    obtain ⟨-, ⟨M₅, hS₅, hK₅, hSt₅⟩, -, hrw5⟩ := h₅
    simp only [ipaK5] at hW
    obtain ⟨g6, hW⟩ := of_ite_none hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [← hm]
    have hgK := hg₁.trans (hSt14.trans hSt₅).toGrew
    refine ipRef_of_run (M' := M₅) (v := decH r₅)
      (by rw [hT1, hT2]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hrun5)
      (by simp only [decH, hr]) ?_ ((hK₃.trans hK₄).trans hK₅) ?_
      (by unfold ResH; rw [← hr]; exact hrw5)
    · exact hS₅.frame_stk (MemFrame.setCtl m₅ 136 _) (by simp) (by simp)
    · exact StackKept.restoreG hgK (Classical.not_not.mp g6)
  · rw [ite_eq_right g4] at hW
    rw [ite_eq_right (by simpa using g4)] at hT1
    have hsp₃ : SpineR m₃ (r₁.headD 0) (r₁.tail.headD 0) xs.toArray :=
      hsp₁.keep hSt₃.size hSt₃.below htopv hspn₁
    obtain ⟨r₅, m₅, hc5, hW⟩ := callW_cases rfl hW
    have h₅ := CoreSpec.of_callW (projTypeAt_refines p hp hc.instLP (N + 1) ⟨m₃, Locals.init []⟩ _ dn
      vis fe M₃ eb q i us _ _ pe tbl xs hS₃ hq₃ hus hpe hsp₃ (by rw [hSt₃.1, htop₂])) hc5
    have hrun5 := ipRun_of_ref h₅
    obtain ⟨-, ⟨M₅, hS₅, hK₅, hSt₅⟩, -, hrw5⟩ := h₅
    simp only [ipaK5] at hW
    obtain ⟨g6, hW⟩ := of_ite_none hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [← hm]
    have hgK := hg₁.trans (hSt₃.trans hSt₅).toGrew
    refine ipRef_of_run (M' := M₅) (v := decH r₅) (by rw [hT1]; exact hrun5)
      (by simp only [decH, hr]) ?_ (hK₃.trans hK₅) ?_ (by unfold ResH; rw [← hr]; exact hrw5)
    · exact hS₅.frame_stk (MemFrame.setCtl m₅ 136 _) (by simp) (by simp)
    · exact StackKept.restoreG hgK (Classical.not_not.mp g6)

end L.Arena
