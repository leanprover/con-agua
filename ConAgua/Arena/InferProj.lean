module

import ConAgua.Arena.DefEqLeaves2
public import ConAgua.Arena.InferBodySpine
import ConAgua.Arena.WhnfCoreProj
public import ConAgua.Arena.InferProjModels
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.CoreWalks
public import ConAgua.Arena.ProjGuardRowsT
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.Infer

@[expose] public section

/-!
# `inferProj`: `proj_type_at` and `infer_proj_at` (lane `defeq2`, helper `defeq2-proj`)

* `proj_type_at(q, i, us, to, tn, pe)` refines `IProjEntry.typeAt` at the entry of the table record
  `q` (`projTypeAt_refines`, the callW pattern of `InferBodyLet.lean`): `inst_lp` on the body, `pe`
  pushed onto the argument slice at the stack top, `inst_list`.
* `infer_proj_at(mode, vis, sn, i, pe, te, T, us, q)` refines `projAtT`, `inferProj` past the
  table lookup, both outcomes (`ipa_ref` over its unified model `ipaE`): another structure, a
  parameter-count mismatch reject, a level-count mismatch declines; then the guard at this use
  (`check_proj_guard`, `cpg_ref` in `ProjGuardRef.lean`) and the type.

The table's words are read from `EREC` after `check_proj_guard` ran (`cpgE_erec`: the core's calls
keep the record pool, `ErecPKept`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The words of a projection table record -/

/-- A decoded handle list at words `q + j`, `q + j + 1`: the slice those two words name. -/
theorem hlist_words {k : IdxKind} {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd)
    {q : Word} {j : Nat} {l : List (Idx k)}
    (h : hlist? R (q.toNat + j) = some l) :
    hslice? R (rd (q + UInt64.ofNat j)).toNat (rd (q + UInt64.ofNat (j + 1))).toNat = some l := by
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩ := h
  have hj := hR.lt _ _ hwc
  have r1 : rd (q + UInt64.ofNat j) = wo := hR.offN hwo (by omega)
  have r2 : rd (q + UInt64.ofNat (j + 1)) = wc :=
    hR.offN (by simpa [Nat.add_assoc] using hwc) (by omega)
  rw [r1, r2]; exact hs

/-- A decoded handle at word `q + j`. -/
theorem hd_word {k : IdxKind} {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd)
    {q : Word} {j : Nat} {x : Idx k} (h : hd? R (q.toNat + j) = some x) :
    HW (rd (q + UInt64.ofNat j)) ∧ x = decI (rd (q + UInt64.ofNat j)) := by
  obtain ⟨w, hw, hw32, rfl⟩ := hd?_some h
  have hj := hR.lt _ _ hw
  rw [hR.offN hw (by omega)]
  exact ⟨hw32, rfl⟩

/-- **The fields of a decoded projection table** `proj_type_at` reads: the level parameters' slice
(words `q + 3`, `q + 4`) and the bodies' slice (`q + 9`, `q + 10`). -/
theorem decTbl_fields {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {tbl : IProjTable} (h : decTbl R q.toNat = some tbl) :
    hslice? R (rd (q + 3)).toNat (rd (q + 4)).toNat = some tbl.levelParams ∧
    hslice? R (rd (q + 9)).toNat (rd (q + 10)).toNat = some tbl.bodies.toList := by
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨sn, -, lps, hlps, np, -, ct, -, nf, -, bd, hbd, hc⟩ := h
  subst hc
  exact ⟨hlist_words hR (j := 3) hlps, by simpa using hlist_words hR (j := 9) hbd⟩

/-- Element `i` of a decoded slice, or `0` past its end, as L reads it (`if i < cnt { a[off + i] }`). -/
def sliceAt (rd : Word → Word) (o c i : Word) : Word := if i < c then rd (o + i) else 0

/-- **`sliceAt` decodes to `getD … default`.** -/
theorem sliceAt_dec {k : IdxKind} {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd)
    {o c : Word} {l : List (Idx k)} (h : hslice? R o.toNat c.toNat = some l) (i : Word) :
    HW (sliceAt rd o c i) ∧ (decI (sliceAt rd o c i) : Idx k) = l.getD i.toNat default := by
  obtain ⟨hl, hg⟩ := hslice?_get h
  unfold sliceAt
  by_cases hi : i < c
  · rw [ite_eq_left hi]
    have hi' : i.toNat < c.toNat := UInt64.lt_iff_toNat_lt.mp hi
    obtain ⟨w, hw, hw32, hl'⟩ := hg i.toNat hi'
    have hr : rd (o + i) = w := hR.off hw rfl
    rw [hr]
    refine ⟨hw32, ?_⟩
    rw [List.getD_eq_getElem?_getD, hl']; rfl
  · rw [ite_eq_right hi]
    have hi' : ¬ i.toNat < c.toNat := fun h' => hi (UInt64.lt_iff_toNat_lt.mpr h')
    refine ⟨by unfold HW; decide, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-! ## The programs and the callees -/

/-- What `infer_proj`'s functions need of a program: `infer_proj`, `infer_proj_at`,
`proj_type_at`, and `check_proj_guard` with its callees. -/
structure InferProjProg (p : Prog) : Prop where
  leaf : DefEqLeafProg p
  lv : LvlCacheProg p
  walk : CoreWalkProg p
  ip : p.lookup "infer_proj" = some inferProjL
  ipa : p.lookup "infer_proj_at" = some inferProjAtL
  pta : p.lookup "proj_type_at" = some projTypeAtL
  cpg : p.lookup "check_proj_guard" = some checkProjGuardL
  pgs : p.lookup "proj_guard_sort" = some projGuardSortL
  cgr : p.lookup "check_guard_rows" = some checkGuardRowsL
  fsl : p.lookup "former_sort_loop" = some formerSortLoopL
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  fvi : p.lookup "intern_fvar" = some internFVar
  pr : p.lookup "pi_result" = some piResultL
  frs : p.lookup "former_res_sort" = some formerResSortL
  laz : p.lookup "lv_always_zero" = some lvAlwaysZero
  pin : p.lookup "pin_word" = some pinWordL
  lvn : p.lookup "lv_never" = some lvNever
  lzw : p.lookup "lv_zero_where_zero" = some lvZeroWhereZero
  lhc : p.lookup "lh_contains" = some lhContains
  envFind : p.lookup "env_find" = some envFindL
  envRowGet : p.lookup "env_row_get" = some envRowGetL
  baseRowGet : p.lookup "base_row_get" = some baseRowGetL
  /-- `proj_guard_rows` and its callees (`pgr_okH`). -/
  pgr : L.Ind.PgrProg p

/-- **The callees of `infer_proj` with no proof here** (each a named hypothesis). -/
structure InferProjCallees (p : Prog) : Prop where
  /-- Stored levels read back under `CoreS` (`StoreDen.lean`; meant as a field of `CoreS`). -/
  den : CoreDen
  /-- Lane `whnf`'s stubs (`WhnfCore.lean`, `WhnfBase.lean`). -/
  findProj : FindProjOK p
  projFound : ProjFound p
  erec : ErecKept p
  instLP : InstLPOK p
  /-- The core's calls keep the record pool's view (`ErecPKept.of_closed`). -/
  erecP : ErecPKept p
  /-- `proj_guard_rows` (`ProjGuardRef.lean`). -/
  pgr : PgrOK p
  inst1 : IotaInst1OK p
  prop : PropReadProg p

/-- `check_proj_guard`'s program facts. -/
theorem InferProjProg.cpgProg {p : Prog} (hp : InferProjProg p) (hc : InferProjCallees p) :
    CpgProg p where
  fsl := hp.fsl
  fvf := hp.fvf
  fvp := hp.fvp
  fvi := hp.fvi
  inst := hc.inst1
  pgs := hp.pgs
  pr := hp.pr
  frs := hp.frs
  laz := hp.laz
  pin := hp.pin
  lvn := hp.lvn
  prop := hc.prop
  ilp := hc.instLP
  cgrP := ⟨hp.cgr, hp.lzw, hp.lhc, hc.prop⟩
  cpg := hp.cpg
  envFind := hp.envFind
  envRowGet := hp.envRowGet
  baseRowGet := hp.baseRowGet

/-! ## `proj_type_at` -/

/-- The body word `proj_type_at` reads: entry `i` of the bodies' slice, or `0`. -/
def projBodyW (m : Mem) (q i : Word) : Word :=
  sliceAt (erRd m) (erRd m (q + 9)) (erRd m (q + 10)) i

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
  rw [AM.run_of_ok _ _ h.run, h.res]

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
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hq : decTbl (erecP s₀.mem) q.toNat = some tbl)
    (hus : HW us) (hpe : HW pe) (hsp : SpineR s₀.mem to tn xs.toArray)
    (htop : spTop s₀.mem = to + tn) :
    CoreSpec p (n + 1) "proj_type_at" [q, i, us, to, tn, pe]
      ((tbl.entry i.toNat).typeAt (decI us) xs (decE pe)) decH s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (ptaW_spec p hp.pta (n + 1) s₀ q i us to tn pe)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hil := hp.walk.instListOK
  obtain ⟨hlps, hbd⟩ := decTbl_fields (erRdOK s.mem) hq
  obtain ⟨hbw, hbdec⟩ := sliceAt_dec (k := .expr) (erRdOK s.mem) hbd i
  have hbody : (decE (projBodyW s.mem q i) : EIdx) = (tbl.entry i.toNat).body := by
    simp only [IProjTable.entry, array_getD_toList]; exact hbdec
  rw [ptaW.eq_2] at hW
  have hj : (if i < erRd s.mem (q + 10) then
        ptaW.j1 p n q us to tn pe (erRd s.mem (erRd s.mem (q + 9) + i)) s.mem
      else ptaW.j1 p n q us to tn pe 0 s.mem) = ptaW.j1 p n q us to tn pe (projBodyW s.mem q i) s.mem := by
    unfold projBodyW sliceAt; split <;> rfl
  erw [hj, ptaW.j1.eq_1] at hW
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (hlp n s a₀ dn vis fe M eb _ _ us (projBodyW s.mem q i) tbl.levelParams
    hS hbw hus hlps) hc1
  rw [hbody] at h₁
  have hrun1 := ipRun_of_ref h₁
  obtain ⟨-, ⟨M₁, hS₁, hK₁, hSt₁⟩, -, hrw1⟩ := h₁
  have hbnd := hsp.bound
  have hspn := hS.spn
  have hadd : (to + tn).toNat = to.toNat + tn.toNat := addW _ _ (by omega)
  rw [ptaW.k_inst_lp.eq_2] at hW
  obtain ⟨g1, hW⟩ := of_ite_none hW
  have g2' : (to + tn).toNat < (m₁.arr64 SPN).size := by
    have hsz := hS₁.spn
    have e : (UInt64.ofNat (m₁.arr64 SPN).size).toNat = (m₁.arr64 SPN).size := by
      simp only [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    have : ¬ (UInt64.ofNat (m₁.arr64 SPN).size ≤ to + tn) := g1
    rw [UInt64.le_iff_toNat_le, e] at this
    omega
  have g3' : (136 : Word).toNat < (m₁.arr64 CTL).size := hS₁.ctl136
  have htn1 : (tn + 1).toNat = tn.toNat + 1 := addW _ _ (by have h1 := hsp.bound; have h2 := hS.spn; simp only [UInt64.toNat_one]; omega)
  have htopv : to.toNat + tn.toNat ≤ (spTop s.mem).toNat := by rw [htop, hadd]; exact Nat.le_refl _
  have hsp₁ : SpineR m₁ to tn xs.toArray := hsp.keep hSt₁.size hSt₁.below htopv hspn
  obtain ⟨hspR, htop₂, -, -, -, -, -⟩ := spPush_step (m₀ := m₁) hS₁.spn hsp₁ (fun _ _ => rfl) rfl
    (BKept.refl _) (PoolGrew.refl _) g3' g2' hpe
  have hS₂ := hS₁.frame_stk (spnCtl_frame m₁ (to + tn) pe (to + (tn + 1))) (by simp) (by simp)
  have hpush : (m₁.set64 SPN (to + tn) pe).set64 CTL 136 (to + tn + 1) = spPush m₁ to tn pe := by
    simp only [spPush, UInt64.add_assoc]
  rw [hpush] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  have hsz₁ : (m₁.arr64 SPN).size = (s.mem.arr64 SPN).size := hSt₁.size
  have hadd1 : (to + (tn + 1)).toNat = to.toNat + (tn + 1).toNat := addW _ _ (by omega)
  have h₂ := CoreSpec.of_callW (hil n ⟨spPush m₁ to tn pe, Locals.init []⟩ (AM.st _ a₀) dn vis fe M₁ eb
    (r₁.headD 0) to (tn + 1) 0 _ hS₂ hrw1 hspR (by rw [htop₂, hadd1]; exact Nat.le_refl _)) hc2
  have hrun2 := ipRun_of_ref h₂
  obtain ⟨-, ⟨M₂, hS₂', hK₂, hSt₂⟩, -, hrw2⟩ := h₂
  rw [ptaW.k_inst_list.eq_2] at hW
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
      hS₂'.ctl136
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

/-- **`inferProj` past the table lookup** (copied; `inferProj_hit`): the subject type's arguments,
the shape checks, the guard at this use, the type. -/
def projAtT (r : CoreFnsA) (fe : IFEnv) (sn T : NIdx) (us : LsIdx) (entry : IProjEntry)
    (te pe : EIdx) : AM EIdx := do
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
      checkProjGuard r fe entry us
      entry.typeAt us targs pe
    else fail (.notImplemented "projection without a native entry")

/-- **`inferProj` at a hit** is `projAtT` from the state after the lookup. -/
theorem inferProj_hit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ a₂ : AState) (it te hh : EIdx) (T : NIdx) (us : LsIdx) (entry : IProjEntry)
    (h1 : (r.infer d pe).run a = .ok (it, a₁)) (h2 : (r.whnf d it).run a₁ = .ok (te, a₂))
    (h3 : (getAppFn coreWalkFuel te).run a₂ = .ok (hh, a₂)) (ht : (hh.tag == ETag.const) = true)
    (hv : a₂.store.view hh = some (.const T us))
    (h4 : fe.findProj? T i = some entry) :
    (inferProj r fe d sn i pe).run a = (projAtT r fe sn T us entry te pe).run a₂ := by
  simp only [inferProj, StateT.run_bind, h1, except_ok_bind, h2, h3, ht, ite_true,
    view_run _ _ _ hv, h4]
  rfl

theorem ip_viewLsLen_run (a : AState) (h : LsIdx) :
    (viewLsLen h).run a = .ok (a.store.lss.viewLen h, a) := rfl

/-- **`projAtT` past its checks**: the guard, then the type. -/
theorem projAtT_run (r : CoreFnsA) (fe : IFEnv) (sn T : NIdx) (us : LsIdx) (entry : IProjEntry)
    (te pe : EIdx) (a : AState) (xs : List EIdx) (l : Nat)
    (hxs : (getAppArgs coreWalkFuel te).run a = .ok (xs, a)) (hT : T = sn)
    (hlen : xs.length = entry.numParams) (hvl : a.store.lss.viewLen us = some l)
    (hl : l = entry.levelParams.length) :
    (projAtT r fe sn T us entry te pe).run a =
      (checkProjGuard r fe entry us >>= fun _ => entry.typeAt us xs pe).run a := by
  subst hT hl
  simp only [projAtT, StateT.run_bind, hxs, except_ok_bind, bne_self_eq_false, hlen,
    Bool.false_eq_true, ↓reduceIte, ip_viewLsLen_run, hvl]

theorem projAtT_errT (r : CoreFnsA) (fe : IFEnv) (sn T : NIdx) (us : LsIdx) (entry : IProjEntry)
    (te pe : EIdx) (a : AState)
    (xs : List EIdx) (hxs : (getAppArgs coreWalkFuel te).run a = .ok (xs, a)) (hT : (T != sn) = true) :
    (projAtT r fe sn T us entry te pe).run a =
      .error (.invalid "invalid projection: the node names another structure") := by
  simp only [projAtT, StateT.run_bind, hxs, except_ok_bind, hT, ↓reduceIte]; rfl

theorem projAtT_errNP (r : CoreFnsA) (fe : IFEnv) (sn T : NIdx) (us : LsIdx) (entry : IProjEntry)
    (te pe : EIdx) (a : AState)
    (xs : List EIdx) (hxs : (getAppArgs coreWalkFuel te).run a = .ok (xs, a)) (hT : T = sn)
    (hl : (xs.length != entry.numParams) = true) :
    (projAtT r fe sn T us entry te pe).run a = .error (.invalid "projection parameter mismatch") := by
  subst hT
  simp only [projAtT, StateT.run_bind, hxs, except_ok_bind, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, hl]; rfl

theorem projAtT_errLP (r : CoreFnsA) (fe : IFEnv) (sn T : NIdx) (us : LsIdx) (entry : IProjEntry)
    (te pe : EIdx) (a : AState)
    (xs : List EIdx) (l : Nat) (hxs : (getAppArgs coreWalkFuel te).run a = .ok (xs, a)) (hT : T = sn)
    (hlen : xs.length = entry.numParams) (hvl : a.store.lss.viewLen us = some l)
    (hl : l ≠ entry.levelParams.length) :
    (projAtT r fe sn T us entry te pe).run a =
      .error (.notImplemented "projection without a native entry") := by
  subst hT
  simp only [projAtT, StateT.run_bind, hxs, except_ok_bind, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, hlen, ip_viewLsLen_run, hvl, hl]; rfl

/-! ## `infer_proj_at` refines `projAtT` -/

/-- **`infer_proj_at` refines `projAtT`, both outcomes** (`inferProj` past the table lookup) at the
table record `q` of field `i`, the subject type `te` headed by `T.{us}`: another structure, a
parameter-count mismatch reject, a level-count mismatch declines, then the guard (`cpg_ref`) and
the type (`projTypeAt_refines`). -/
theorem ipa_ref (p : Prog) (hp : InferProjProg p) (hc : InferProjCallees p) (n F : Nat)
    (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (R : CoreFnsA)
    (hRW : R.whnf = (coreKnot (decMode mode) (decEager mode) fe id F).whnf)
    (hRI : R.inferIO = (coreKnot (decMode mode) (decEager mode) fe id F).inferIO)
    (m : Mem) (a₀ : AState) (M : ModeMaps) (sn i pe te T us q : Word) (tbl : IProjTable)
    (hS : CoreS dn m a₀ vis fe M eb) (hq : decTbl (erecP m) q.toNat = some tbl)
    (hfe : ∃ c, fe.findTable? c = some tbl) (hus : HW us) (hte : HW te) (hpe : HW pe)
    (hsn : HW sn) (hT : HW T) :
    RefE (KnotUpToE p n) (ipaE p (n + 1) m mode vis sn i pe te T us q)
      (projAtT R fe (decI sn) (decI T) (decI us) (tbl.entry i.toNat) (decE te) (decE pe)) a₀
      (CorePost decH dn m vis fe M eb ResH) := by
  rw [ipaE.eq_2]
  -- `get_app_args`
  refine RefE.onlySim (fun _ => ipaE.k_get_app_args.none ..) (fun _ _ h => h) fun r₁ m₁ hc1 => ?_
  rw [ipaE.k_get_app_args.eq_2]
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, ho₁, htop₁, xs, hxs, hsp₁⟩ := triple_of_callW
    (getAppArgs_refines p hp.leaf.core.spine n ⟨m, Locals.init []⟩ a₀ hS.arena.base te hte hS.spn) hc1
  rw [ht₁] at hf₁ hg₁ htop₁ hsp₁
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hE₁ : erecP m₁ = erecP m := erecP_frame hf₁ (by simp [EREC, SPN]) (by simp [EREC, SPN, tier1])
    (by simp) (by simp)
  have hq₁ : decTbl (erecP m₁) q.toNat = some tbl := by rw [hE₁]; exact hq
  obtain ⟨hlp, hnp, -, -, -⟩ := decTbl_words (erRdOK m₁) hq₁
  simp only [erRd] at hlp hnp
  have hlen0 : xs.length = (r₁.tail.headD 0).toNat := by
    have := hsp₁.size; simp only [List.size_toArray] at this; exact this
  by_cases g1 : T ≠ sn
  · have hne : ((decI T : NIdx) != decI sn) = true := by
      simp only [bne_iff_ne, ne_eq]; exact fun h => g1 (decI_inj hT hsn h)
    exact RefE.abortAt g1 fun _ => ErrClaim.of_error (projAtT_errT _ _ _ _ _ _ _ _ _ xs hxs hne) rfl
  refine RefE.pass g1 ?_
  have hTs : T = sn := Classical.not_not.mp g1
  by_cases g2 : r₁.tail.headD 0 ≠ rdW (m₁.arr64 (tierA EREC ((q + 5) >>> 40))) (q + 5 &&& 1099511627775)
  · have hl : (xs.length != (tbl.entry i.toNat).numParams) = true := by
      simp only [bne_iff_ne, ne_eq, hlen0]
      intro h; apply g2; apply UInt64.toNat_inj.mp; rw [h]; exact hnp
    exact RefE.abortAt g2 fun _ =>
      ErrClaim.of_error (projAtT_errNP _ _ _ _ _ _ _ _ _ xs hxs (by rw [hTs]) hl) rfl
  refine RefE.pass g2 ?_
  have g2' : r₁.tail.headD 0 = rdW (m₁.arr64 (tierA EREC ((q + 5) >>> 40))) (q + 5 &&& 1099511627775) :=
    Classical.not_not.mp g2
  have hlen : xs.length = (tbl.entry i.toNat).numParams := by rw [hlen0, g2']; exact hnp.symm
  -- `ls_node`
  refine RefE.onlySim (fun _ => ipaE.k_ls_node.none ..) (fun _ _ h => h) fun r₂ m₂ hc2 => ?_
  rw [ipaE.k_ls_node.eq_2]
  obtain ⟨t₂, ht₂, ht₂s, hne₂, hr₂⟩ :=
    triple_of_callW (lsNode_spec p hp.lv.lsnode n ⟨m₁, Locals.init []⟩ us) hc2
  have hm₂ : m₂ = m₁ := by rw [← ht₂, ht₂s]
  subst hm₂
  obtain ⟨o₂, l₂, hl₂⟩ : ∃ o l, lsNodeW m₂ us = [o, l] := by
    rcases lsNodeW_cases m₂ us with h | h
    · rw [h] at hr₂; exact absurd hr₂ hne₂
    · exact h
  have hr₂' : r₂ = [o₂, l₂] := by rw [hr₂]; exact hl₂
  subst hr₂'
  have hvl : a₀.store.lss.viewLen (decI us) = some l₂.toNat := lsNodeW_viewLen hS₁.arena.base hus hl₂
  by_cases g3 : [o₂, l₂].tail.headD 0 ≠ rdW (m₂.arr64 (tierA EREC ((q + 4) >>> 40))) (q + 4 &&& 1099511627775)
  · have hl : l₂.toNat ≠ (tbl.entry i.toNat).levelParams.length := by
      intro h; apply g3; apply UInt64.toNat_inj.mp; simp only [List.tail_cons, List.headD_cons]
      rw [h]; exact hlp
    exact RefE.abortAt g3 fun _ =>
      ErrClaim.of_error (projAtT_errLP _ _ _ _ _ _ _ _ _ xs _ hxs (by rw [hTs]) hlen hvl hl) rfl
  refine RefE.pass g3 ?_
  have g3' : l₂ = rdW (m₂.arr64 (tierA EREC ((q + 4) >>> 40))) (q + 4 &&& 1099511627775) := by
    simpa using g3
  have hlpl : l₂.toNat = (tbl.entry i.toNat).levelParams.length := by rw [g3']; exact hlp.symm
  have hT1 := projAtT_run R fe (decI sn) (decI T) (decI us) (tbl.entry i.toNat) (decE te) (decE pe) a₀
    xs l₂.toNat hxs (by rw [hTs]) hlen hvl hlpl
  refine RefE.of_run_eq hT1 ?_
  -- `check_proj_guard`
  rcases n with _ | n
  · rw [cpgE.eq_1, ipaE.k_check_proj_guard.none]; exact RefE.of_cls0 (by simp)
  have hcpg := cpg_ref p (hp.cpgProg hc) hc.pgr hc.erecP n F (hk.mono (Nat.le_succ _)) (by omega)
    (by omega) dn vis fe eb mode hm4 hebm R hRW hRI m₂ a₀ M q i us tbl hS₁ hq₁ hfe hus
  rcases hx3 : cpgE p (n + 1) m₂ mode vis q i us with e3 | ⟨r₃, m₃⟩
  · rw [hx3] at hcpg; rw [ipaE.k_check_proj_guard.none]
    exact RefE.bind_left fun hg => hcpg (hg.mono (Nat.le_succ _))
  rw [hx3] at hcpg
  obtain ⟨y3, a3, hrun3, hP3⟩ := hcpg
  refine RefE.bind_right hrun3 ?_
  obtain ⟨M₃, hS₃, hK₃, hSt₃⟩ := hP3.after
  have hE₃ : erecP m₃ = erecP m₂ := cpgE_erec hc.erecP hx3
  rw [ipaE.k_check_proj_guard.eq_2]
  -- `proj_type_at`
  have hto : r₁.headD 0 = spTop m := ho₁
  have htop₂ : spTop m₂ = r₁.headD 0 + r₁.tail.headD 0 := by rw [htop₁, hto]
  have hspn₁ := hS₁.spn
  have hbnd := hsp₁.bound
  have htopv : (r₁.headD 0).toNat + (r₁.tail.headD 0).toNat ≤ (spTop m₂).toNat := by
    rw [htop₂, addW _ _ (by omega)]; exact Nat.le_refl _
  have hsp' : SpineR m₃ (r₁.headD 0) (r₁.tail.headD 0) xs.toArray :=
    hsp₁.keep hSt₃.size hSt₃.below htopv hspn₁
  rcases c5 : callW p (n + 1) "proj_type_at" [q, i, us, r₁.headD 0, r₁.tail.headD 0, pe] m₃ with
    _ | ⟨r₅, m₅⟩
  · rw [liftE_none, ipaE.k_proj_type_at.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, ipaE.k_proj_type_at.eq_2]
  have h₅ := CoreSpec.of_callW (projTypeAt_refines p hp hc.instLP n ⟨m₃, Locals.init []⟩ _ dn
    vis fe M₃ eb q i us _ _ pe tbl xs hS₃ (by rw [hE₃]; exact hq₁) hus hpe hsp'
    (by rw [hSt₃.1, htop₂])) c5
  have hrun5 := ipRun_of_ref h₅
  obtain ⟨-, ⟨M₅, hS₅, hK₅, hSt₅⟩, -, hrw5⟩ := h₅
  have hgK := hg₁.trans (hSt₃.trans hSt₅).toGrew
  exact RefE.ret hrun5 ⟨⟨M₅, hS₅.frame_stk (MemFrame.setCtl m₅ 136 _) (by simp) (by simp),
    hK₃.trans hK₅, StackKept.restoreG' hgK⟩, rfl, hrw5⟩

/-- **`proj_guard_rows` refines `projGuardRows`** (`PgrOK`, from `pgr_okH`; the pool's `IWOK` and
the `hb` memo come from `CoreS`). -/
theorem pgrOK_of (p : Prog) (hp : InferProjProg p) (hct : ConstTyAtOK p) : PgrOK p :=
  fun n _ m m' a _ _ M _ q i us tbl r hS hq _ hus h =>
    L.Ind.pgr_okH p hp.pgr hct n m m' a M q i us tbl r hS hS.iw hS.memos.hb hq hus h

end L.Arena
