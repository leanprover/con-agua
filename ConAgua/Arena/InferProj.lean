module

public import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.DefEqLeaves2
public import ConAgua.Arena.CoreDen
public import ConAgua.Arena.InferBodySpine
import ConAgua.Arena.WhnfCoreProj
public import ConAgua.Arena.InferProjModels
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.CoreLevels
public import ConAgua.Arena.CoreWalks
public import ConAgua.Arena.DefEqLeaves
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.Infer

@[expose] public section

/-!
# `inferProj`: `proj_type_at` and `infer_proj_at` (lane `defeq2`, helper `defeq2-proj`)

* `proj_type_at(q, i, us, to, tn, pe)` refines `IProjEntry.typeAt` at the entry of the table record
  `q` (`projTypeAt_refines`, the callW pattern of `InferBodyLet.lean`): `inst_lp` on the body, `pe`
  pushed onto the argument slice at the stack top, `inst_list`.
* `infer_proj_at(vis, sn, i, pe, te, T, us, q)` refines `projAtT`, `inferProj` past the table
  lookup, both outcomes (`ipa_ref` over its unified model `ipaE`): another structure, a
  parameter-count mismatch, a propositional structure's non-propositional field reject, a
  level-count mismatch declines; every callee is outside the verdict closure.

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
  obtain ⟨w, hw, hw32, rfl⟩ := hd?_eq h
  have hj := hR.lt _ _ hw
  rw [hR.offN hw (by omega)]
  exact ⟨hw32, rfl⟩

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The fields of a decoded projection table** `infer_proj` reads: the level parameters' slice
(words `q + 3`, `q + 4`), the structure's sort (`q + 8`), the bodies' slice (`q + 9`, `q + 10`),
the guards' slice (`q + 11`, `q + 12`). -/
theorem decTbl_fields {a : Array Word} {q : Word} {tbl : IProjTable}
    (h : decTbl (aread a) q.toNat = some tbl) (hsz : a.size < 2 ^ 63) :
    hslice? (aread a) (rdW a (q + 3)).toNat (rdW a (q + 4)).toNat = some tbl.levelParams ∧
    HW (rdW a (q + 8)) ∧ tbl.structSort = decI (rdW a (q + 8)) ∧
    hslice? (aread a) (rdW a (q + 9)).toNat (rdW a (q + 10)).toNat = some tbl.bodies.toList ∧
    hslice? (aread a) (rdW a (q + 11)).toNat (rdW a (q + 12)).toNat = some tbl.guards := by
  sorry

-/

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

/-- What `infer_proj`'s three functions need of a program. -/
structure InferProjProg (p : Prog) : Prop where
  leaf : DefEqLeafProg p
  lv : LvlCacheProg p
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
  sliceAt (erRdT m) (erRdT m (q + 9)) (erRdT m (q + 10)) i

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

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
theorem projTypeAt_spec (p : Prog) (hp : InferProjProg p) (n : Nat) (s₀ : St)
    (q i us to tn pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_type_at" [q, i, us, to, tn, pe]
    ⦃fun r s' => LocEq s' s₀ ∧ ptaW p n s₀.mem q i us to tn pe = some (r.headD 0, s'.mem); ⊤⦄ := by
  sorry

-- RS2E

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

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
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
  sorry

-- RS2E

/-! ## The twin past the table lookup -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `inferProj`'s propositional-structure test and the type (its innermost block, copied). -/
def fszTail (entry : IProjEntry) (us : LsIdx) (targs : List EIdx) (pe : EIdx) : AM EIdx := do
  let ks ← readNamesM entry.levelParams
  let vs ← readLevelsM us
  let fs ← readLevelM entry.fieldSort
  if !(ConLeche.Level.isEquiv (ConLeche.Level.subst ks vs fs) .zero == some true) then
    fail (.invalid "projection from a propositional structure must be a proposition")
  else entry.typeAt us targs pe
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`inferProj` at a hit** is `projAtT` from the state after the lookup. -/
theorem inferProj_hit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (sn : NIdx) (i : Nat) (pe : EIdx)
    (a a₁ a₂ : AState) (it te hh : EIdx) (T : NIdx) (us : LsIdx) (entry : IProjEntry)
    (h1 : (r.infer d pe).run a = .ok (it, a₁)) (h2 : (r.whnf d it).run a₁ = .ok (te, a₂))
    (h3 : (getAppFn coreWalkFuel te).run a₂ = .ok (hh, a₂)) (ht : (hh.tag == ETag.const) = true)
    (hv : a₂.store.view hh = some (.const T us))
    (h4 : fe.findProj? T i = some entry) :
    (inferProj r fe d sn i pe).run a = (projAtT sn T us entry te pe).run a₂ := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The test's run is the twin's three readbacks** (`fieldSortZeroT`, `Knot.lean`). -/
theorem fszTail_run (entry : IProjEntry) (us : LsIdx) (targs : List EIdx) (pe : EIdx)
    (a a' : AState) (b : Bool)
    (h : (fieldSortZeroT entry.levelParams us entry.fieldSort).run a = .ok (b, a')) :
    (fszTail entry us targs pe).run a =
      (if !b then fail (.invalid "projection from a propositional structure must be a proposition")
        else entry.typeAt us targs pe).run a' := by
  sorry

-/

/-- **`lvlEq?` leaves the store alone** (it writes the readback and verdict caches only). -/
theorem lvlEq?_store (u v : LIdx) (a a' : AState) (o : Option Bool) (lu lv : ConLeche.Level)
    (hu : denoteL a.store.ls u = some lu) (hv : denoteL a.store.ls v = some lv) (hc : ReadLCOK a)
    (h : (lvlEq? u v).run a = .ok (o, a')) : a'.store = a.store := by
  cases hm : a.caches.lvlEqC[(u, v)]? with
  | some r => rw [lvlEq?_hit a u v r hm] at h; cases h; rfl
  | none =>
    obtain ⟨X, hr, -⟩ := lvlEq?_miss a u v lu lv hu hv hc hm
    rw [hr] at h; cases h; rfl

/-! ## `infer_proj_at` -/

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
          vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
            callW_spec p 0 "lq_find", callW_spec p 0 "lvl_eq_rec"] <;>
          simp_all [callW_zero]) hc
      exact hF

theorem ip_viewLsLen_run (a : AState) (h : LsIdx) :
    (viewLsLen h).run a = .ok (a.store.lss.viewLen h, a) := rfl

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
-/

theorem ErrClaim.of_error {α : Type} {T : AM α} {a : AState} {e : Err} {ce : CheckError}
    (h : T.run a = .error ce) (hk : e.cls = twinCls ce) : ErrClaim T a e :=
  fun _ => ⟨ce, h, hk.symm⟩

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem projAtT_errT (sn T : NIdx) (us : LsIdx) (entry : IProjEntry) (te pe : EIdx) (a : AState)
    (xs : List EIdx) (hxs : (getAppArgs coreWalkFuel te).run a = .ok (xs, a)) (hT : (T != sn) = true) :
    (projAtT sn T us entry te pe).run a =
      .error (.invalid "invalid projection: the node names another structure") := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem projAtT_errNP (sn T : NIdx) (us : LsIdx) (entry : IProjEntry) (te pe : EIdx) (a : AState)
    (xs : List EIdx) (hxs : (getAppArgs coreWalkFuel te).run a = .ok (xs, a)) (hT : T = sn)
    (hl : (xs.length != entry.numParams) = true) :
    (projAtT sn T us entry te pe).run a = .error (.invalid "projection parameter mismatch") := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem projAtT_errLP (sn T : NIdx) (us : LsIdx) (entry : IProjEntry) (te pe : EIdx) (a : AState)
    (xs : List EIdx) (l : Nat) (hxs : (getAppArgs coreWalkFuel te).run a = .ok (xs, a)) (hT : T = sn)
    (hlen : xs.length = entry.numParams) (hvl : a.store.lss.viewLen us = some l)
    (hl : l ≠ entry.levelParams.length) :
    (projAtT sn T us entry te pe).run a =
      .error (.notImplemented "projection without a native entry") := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`infer_proj_at` refines `projAtT`, both outcomes** (`inferProj` past the table lookup) at the
table record `q` of field `i`, the subject type `te` headed by `T.{us}`. -/
theorem ipa_ref (p : Prog) (hp : InferProjProg p) (hc : InferProjCallees p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb sn i pe te T us q : Word) (tbl : IProjTable)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hq : decTbl (erecP s₀.mem) q.toNat = some tbl)
    (hfe : ∃ c, fe.findTable? c = some tbl)
    (hi : i.toNat < tbl.numFields) (hus : HW us) (hte : HW te) (hpe : HW pe)
    (hden : ∃ ls, denoteLs a₀.store.lss (decI us) = some ls) (hsn : HW sn) (hT : HW T) :
    RefE (closedNV p L.Checker.nvFns = true) (ipaE p (n + 1) s₀.mem vis sn i pe te T us q)
      (projAtT (decI sn) (decI T) (decI us) (tbl.entry i.toNat) (decE te) (decE pe)) a₀
      (CorePost decH dn s₀.mem vis fe M eb ResH) := by
  sorry

-/

end L.Arena
