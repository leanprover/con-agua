module

import ConAgua.Arena.WhnfIotaRefine3
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
public import ConAgua.Arena.DefEqStuck
public import ConAgua.Arena.WhnfIotaRefine

@[expose] public section

/-!
# The structure-η certificate's tail: `struct_eta_cert_tail` (lane `defeq`, helper `defeq-top`)

The level comparison and the two spine comparisons of `structEtaCertWith` (`setTailT`). The
projections' slice stays on the stack, so the post is a `GrowPost` (`RefE.bind_grow`/
`bind_growK` thread it); the errors are the level comparison's decline and `defeq_lst`'s (`SetG`). `eta_projs` from lane `whnf`'s `etaProjs_refines`
and `etaProjs_spec` (the new top), `defeq_lst` from `DefeqLstOK`, `lvls_eq_c` from `LvlsEqCH`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Runs that grow the stack -/

theorem GrowRef.of_core {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) : GrowRef T a₀ dec dn m₀ vis fe M eb r m ok :=
  ⟨h.run, h.after.toG, h.res, h.resOk⟩

/-- **A run that grew the stack, then one from its state.** -/
theorem growRef_then {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {T₂ T : AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : GrowRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb →
      GrowRef T₂ (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok)
    (hT : T.run a₀ = T₂.run (AM.st T₁ a₀)) : GrowRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  obtain ⟨hok2, ⟨M'', hS'', hK'', hSt''⟩, hres2, hrw2⟩ := h₂ M' hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hT.trans (AM.run_of_ok _ _ hok2))
  exact ⟨hok, hst ▸ ⟨M'', hS'', hK.trans hK'', hSt.trans hSt''⟩, hres.trans hres2, hrw2⟩

/-- **The refinement of a `>>=`**, the stack possibly grown. -/
theorem growRef_bindS {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {T₂ : α → AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : GrowRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb →
      GrowRef (T₂ (dec₁ r₁)) (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok) :
    GrowRef (T₁ >>= T₂) a₀ dec dn m₀ vis fe M eb r m ok :=
  growRef_then h₁ h₂ (by rw [StateT.run_bind, AM.run_of_ok _ _ h₁.1, h₁.2.2.1]; rfl)

/-- A value with no effect. -/
theorem growRef_pure {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {r : List Word} {v : α} (hS : CoreS dn m a₀ vis fe M eb) (hrun : T.run a₀ = .ok (v, a₀))
    (hv : v = dec r) (hr : ResH r) : GrowRef T a₀ dec dn m vis fe M eb r m :=
  GrowRef.of_core (coreRef_pure hS hrun hv hr)

/-- **The top put back** after a run that grew the stack: a `CoreRef`. -/
theorem GrowRef.restore {α : Type} [Inhabited α] {T : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : GrowRef T a₀ dec dn m₀ vis fe M eb r m ok) (h136 : (136 : Word).toNat < (m.arr64 CTL).size) :
    CoreRef T a₀ dec dn m₀ vis fe M eb r (m.set64 CTL 136 (rdW (m₀.arr64 CTL) 136)) ok := by
  obtain ⟨hok, ⟨M', hS, hK, hg⟩, hres, hr⟩ := h
  have hS' := hS.frame_stk (MemFrame.setCtl m 136 (rdW (m₀.arr64 CTL) 136)) (by simp) (by simp)
  exact ⟨hok, ⟨M', hS', hK, StackKept.restoreG hg h136⟩, hres, hr⟩

/-- A slice below the top survives a run that kept the stack below the top. -/
theorem SpineR.grew {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (hg : StackGrew m m') (htop : off.toNat + cnt.toNat ≤ (spTop m).toNat)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) : SpineR m' off cnt xs :=
  h.keep hg.size hg.below htop hspn

/-- A trailing part of a spine slice. -/
theorem SpineR.drop {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (c : Word) (hc : c.toNat ≤ cnt.toNat) (hspn : (m.arr64 SPN).size < 2 ^ 63) :
    SpineR m (off + c) (cnt - c) (xs.toList.drop c.toNat).toArray := by
  have hb := h.bound
  have hsz := h.size
  have hoc : (off + c).toNat = off.toNat + c.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hcc : (cnt - c).toNat = cnt.toNat - c.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hc)
  have hw : ∀ i : Nat, i < cnt.toNat - c.toNat →
      off + c + i.toUInt64 = off + (c.toNat + i).toUInt64 := by
    intro i hi
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    have : off.toNat < 2 ^ 64 := off.toNat_lt
    omega
  refine ⟨by simp [hsz, hcc], by rw [hoc, hcc]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hcc] at hi; rw [hw i hi]; exact h.lt _ (by omega)
  · simp only [List.size_toArray, List.length_drop, Array.length_toList] at hi
    have hi' : c.toNat + i < xs.size := by omega
    rw [hw i (by omega)]
    have := h.get (c.toNat + i) hi'
    simpa [List.getElem_drop] using this

/-! ## The twin's tail -/

/-- **`structEtaCertWith` after its pure conditions**, copied (`ep`/`nf` the caps' counts). -/
def setTailT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (us : LsIdx) (T : NIdx)
    (us' : LsIdx) (ep nf : Nat) (aargs targs : List EIdx) : AM Bool := do
  if ← liftFueled "level comparison" (← lvlsEq? us us') then do
    if ← defEqList r fe depth (aargs.take ep) targs then do
      let projs ← etaProjs T b nf
      defEqList r fe depth (aargs.drop ep) projs
    else pure false
  else pure false

theorem wmin_le {a b : Word} (h : b ≤ a) : (if a < b then a else b) = b := by
  have : ¬ a < b := by rw [UInt64.lt_iff_toNat_lt]; rw [UInt64.le_iff_toNat_le] at h; omega
  simp only [this, ↓reduceIte]

/-! ## Leaves at any fuel -/

theorem defeqLst_at (p : Prog) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
      (M : ModeMaps) (eb mode d ao an bo bn : Word) (xs ys : Array EIdx),
      SlotPre s₀ a₀ dn vis fe M eb mode → SpineR s₀.mem ao an xs → SpineR s₀.mem bo bn ys →
      ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat →
      CoreSpec p n "defeq_lst" [mode, vis, d, ao, an, bo, bn]
        (defEqList (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat xs.toList ys.toList) decBool s₀ a₀
        dn vis fe M eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, M, eb, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, ao, an, bo, bn, xs, ys, hs, h1, h2,
      h3, h4 =>
      hc.defeqLst n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb mode d ao an
        bo bn xs ys hs h1 h2 h3 h4

theorem growRef_congrS {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₀)
    (h' : GrowRef T' a₀ dec dn m₀ vis fe M eb r m ok) : GrowRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  unfold GrowRef AM.ok AM.st AM.res at *; rw [h]; exact h'

/-- **A run of `eta_projs`**: the twin's projections as a slice at the old top, the top raised
past it. -/
theorem etaProjs_callW {p : Prog} (hi : IotaProg' p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) {T b nF : Word} (hT : HW T) (hb : HW b) {r : List Word}
    (hc : callW p n "eta_projs" [T, b, nF] m = some (r, m')) :
    GrowRef (etaProjs (decI T) (decE b) nF.toNat) a
      (fun _ => AM.res (etaProjs (decI T) (decE b) nF.toNat) a) dn m vis fe M eb r m' (fun _ => True) ∧
      r.headD 0 = spTop m ∧ r.tail.headD 0 = nF ∧ spTop m' = spTop m + nF ∧
      (spTop m).toNat + nF.toNat ≤ (m.arr64 SPN).size ∧
      SpineR m' (r.headD 0) (r.tail.headD 0) (AM.res (etaProjs (decI T) (decE b) nF.toNat) a).toArray := by
  obtain ⟨t, ht, -, hok, hA, hr0, hr1, xs, hxs, hsp⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (etaProjs_refines p hi n ⟨m, Locals.init []⟩ a dn vis fe M eb T b nF hS hT hb) hc
  subst ht
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ k =>
  obtain ⟨t', ht', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (etaProjs_spec p hi.etaProjs k ⟨m, Locals.init []⟩ T b nF) hc
  rw [ht'] at hW
  have hsz : (m.arr64 SPN).size < 2 ^ 63 := hS.spn
  simp only [etpTop] at hW
  have h136 : (136 : Word).toNat < (m.arr64 CTL).size := by
    by_cases h : (136 : Word).toNat < (m.arr64 CTL).size
    · exact h
    · simp only [h, ↓reduceIte] at hW; cases hW
  simp only [h136, ↓reduceIte] at hW
  by_cases hle : UInt64.ofNat (m.arr64 SPN).size < rdW (m.arr64 CTL) 136
  · simp only [hle, ↓reduceIte] at hW; cases hW
  simp only [hle, ↓reduceIte] at hW
  by_cases hroom : UInt64.ofNat (m.arr64 SPN).size - rdW (m.arr64 CTL) 136 < nF
  · simp only [hroom, ↓reduceIte] at hW; cases hW
  simp only [hroom, ↓reduceIte] at hW
  cases hL : etpW p T b nF (rdW (m.arr64 CTL) 136) (k + 1) m 0 with
  | none => rw [hL] at hW; cases hW
  | some m'' =>
  rw [hL] at hW
  have h136' : (136 : Word).toNat < (m''.arr64 CTL).size := by
    by_cases h : (136 : Word).toNat < (m''.arr64 CTL).size
    · exact h
    · simp only [h, ↓reduceIte] at hW; cases hW
  simp only [h136', ↓reduceIte, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hW
  obtain ⟨-, em⟩ := hW
  have hle' : (spTop m).toNat ≤ (m.arr64 SPN).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hle
    simp only [spTop]; omega
  have hroom' : (spTop m).toNat + nF.toNat ≤ (m.arr64 SPN).size := by
    have hle2 : rdW (m.arr64 CTL) 136 ≤ UInt64.ofNat (m.arr64 SPN).size := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      simpa [spTop] using hle'
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ hle2, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)] at hroom
    simp only [spTop] at hle' ⊢; omega
  refine ⟨⟨hok, hA, rfl, trivial⟩, hr0, hr1, ?_, hroom', by rw [hxs]; exact hsp⟩
  rw [← em]
  simp only [spTop, rdW_set64, h136', and_self, ↓reduceIte]

/-! ## `struct_eta_cert_tail` refines `setTailT` -/

theorem some_pair_inj {x y : Word} {m m' : Mem} (h : some (x, m) = some (y, m')) : x = y ∧ m = m' := by
  simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h

theorem take_min_eq (xs : List EIdx) (an ep : Word) (h : xs.length = an.toNat) :
    xs.take (if an < ep then an else ep).toNat = xs.take ep.toNat := by
  by_cases hl : an < ep
  · simp only [hl, ↓reduceIte]
    rw [List.take_of_length_le (by omega), List.take_of_length_le]
    rw [UInt64.lt_iff_toNat_lt] at hl; omega
  · simp only [hl, ↓reduceIte]

theorem drop_min_eq (xs : List EIdx) (an ep : Word) (h : xs.length = an.toNat) :
    xs.drop (if an < ep then an else ep).toNat = xs.drop ep.toNat := by
  by_cases hl : an < ep
  · simp only [hl, ↓reduceIte]
    rw [List.drop_of_length_le (by omega), List.drop_of_length_le]
    rw [UInt64.lt_iff_toNat_lt] at hl; omega
  · simp only [hl, ↓reduceIte]

theorem min_le_an (an ep : Word) : (if an < ep then an else ep).toNat ≤ an.toNat := by
  by_cases hl : an < ep
  · simp only [hl, ↓reduceIte]; exact Nat.le_refl _
  · simp only [hl, ↓reduceIte]; rw [UInt64.lt_iff_toNat_lt] at hl; omega

/-- `defeq_lst`'s error claim at fuel `n + 1` (the premises of `DefeqLstOK`). -/
def DefeqLstWE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ao an bo bn : Word) (xs ys : Array EIdx),
    SlotPre s₀ a₀ dn vis fe M eb mode → SpineR s₀.mem ao an xs → SpineR s₀.mem bo bn ys →
    ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p (n + 1) "defeq_lst" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat xs.toList ys.toList) s₀ a₀

/-- **What the structure-η certificate's errors assume** at L fuel `n`: the knot's slots' claims,
`defeq_lst`'s. -/
structure SetG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  lst : DefeqLstWE p

theorem SetG.mono {p : Prog} {n n' : Nat} (h : SetG p n) (hn : n' ≤ n) : SetG p n' :=
  ⟨h.knot.mono hn, h.lst⟩

/-- `defeq_lst`'s claim at a call of fuel `n` under `SetG p n`. -/
theorem SetG.lstE {p : Prog} {n : Nat} (hG : SetG p n) (hk : KnotUpTo p n) {F : Nat} (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) {s₀ : St} {a₀ : AState} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb mode d ao an bo bn : Word} {xs ys : Array EIdx}
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (h1 : SpineR s₀.mem ao an xs)
    (h2 : SpineR s₀.mem bo bn ys) (h3 : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (h4 : bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) {e : Err}
    (hc : callE p n "defeq_lst" [mode, vis, d, ao, an, bo, bn] s₀.mem = .error e) :
    ErrClaim (defEqList (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat xs.toList ys.toList) a₀ e := by
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "defeq_lst" [mode, vis, d, ao, an, bo, bn] s₀.mem
    rw [hc] at he'; cases he'; exact ErrClaim.of_cls0 h0
  | succ N =>
    exact CoreSpecE.of_callE (hG.lst N (hk.mono (Nat.le_succ N)) (hG.knot.mono (Nat.le_succ N)) F
      (by omega) (by omega) s₀ a₀ dn vis fe M eb mode d ao an bo bn xs ys hs h1 h2 h3 h4) hc

/-- **`struct_eta_cert_tail` refines `setTailT`, both outcomes** (the projections' slice left on
the stack): the errors are the level comparison's out-of-fuel decline and `defeq_lst`'s. -/
@[refines_part ConRon.Arena.structEtaCertWith "the level comparison and the spines (setTailT)"]
theorem sect_ref (p : Prog) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us T us2 ao an to tn ep nf : Word) (aargs targs : Array EIdx) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hus : HW us)
    (hT : HW T) (hus2 : HW us2) (hdus : ∃ lu, denoteLs a₀.store.lss (decI us) = some lu)
    (hdus2 : ∃ lv, denoteLs a₀.store.lss (decI us2) = some lv) (ha : SpineR s₀.mem ao an aargs)
    (ht : SpineR s₀.mem to tn targs)
    (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (htt : to.toNat + tn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (SetG p n) (sectE p (n + 1) s₀.mem mode vis d b us T us2 ao an to tn ep nf)
      (setTailT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE b) (decI us) (decI T) (decI us2)
        ep.toNat nf.toNat aargs.toList targs.toList) a₀
      (GrowPost decBool dn s₀.mem vis fe M eb ResH) := by
  have hspn := hs.rel.spn
  simp only [sectE]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => CoreSpec.of_callW
    (hc.lvlsEqC n s₀ a₀ dn vis fe M eb us us2 hs.rel hus hus2 hdus hdus2) h) fun r₁ m₁ h₁ => ?_
  obtain ⟨_, _, _, hst₁⟩ := h₁.after
  unfold setTailT
  refine RefE.bind_growK (w := id) h₁ (fun M₁ hS₁ _ => ?_)
  dsimp only [sectE.k_lvls_eq_c]
  -- the decline: `lvls_eq_c` ran out of fuel, the twin's `liftFueled` fails
  refine RefE.guardOpt rfl (fun z0 => ite_eq_left z0) (fun h => by unfold decO at h; grind)
    fun v hv h0 => ?_
  by_cases h1 : r₁.headD 0 = 1
  · rw [decO, ite_eq_right h0, ite_eq_left h1] at hv; cases hv
    rw [ite_eq_left h1]
    exact RefE.ret rfl (GrowPost.of_core (CorePost.ret hS₁ rfl hw0))
  rw [decO, ite_eq_right h0, ite_eq_right h1] at hv; cases hv
  rw [ite_eq_right h1]
  simp only [↓reduceIte]
  obtain ⟨tk, htk⟩ : ∃ tk, tk = (if an < ep then an else ep) := ⟨_, rfl⟩
  have hj : (if an < ep then sectE.j1 p n mode vis d b T ao an to tn nf an m₁
      else sectE.j1 p n mode vis d b T ao an to tn nf ep m₁) =
      sectE.j1 p n mode vis d b T ao an to tn nf tk m₁ := by rw [htk]; split <;> rfl
  rw [hj, sectE.j1]
  have hmin : tk.toNat ≤ an.toNat := htk ▸ min_le_an an ep
  have hlen : aargs.toList.length = an.toNat := by simpa using ha.size
  have hsp₁ : SpineR m₁ ao an aargs := ha.keep hst₁.size hst₁.below hat hspn
  have htp₁ : SpineR m₁ to tn targs := ht.keep hst₁.size hst₁.below htt hspn
  have htop₁ : spTop m₁ = spTop s₀.mem := hst₁.1
  have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hS₁.spn
  have htake := hsp₁.take tk hmin
  have etake : ((aargs.toList.take tk.toNat).toArray).toList = aargs.toList.take ep.toNat := by
    rw [htk]; exact take_min_eq _ _ _ hlen
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  have hb₁ : ao.toNat + tk.toNat ≤ (spTop m₁).toNat := by rw [htop₁]; omega
  have ht₁ : to.toNat + tn.toNat ≤ (spTop m₁).toNat := by rw [htop₁]; exact htt
  have hD := defeqLst_at p hc n hk F hF hn _ _ dn vis fe M₁ eb mode d ao tk to tn _ targs hs₁ htake htp₁
      hb₁ ht₁
  rw [etake] at hD
  refine RefE.bind_callE (fun _ => rfl) hD (fun hG => CoreSpecE.of_runs fun _ c => by
      have h := hG.lstE hk hF hn hs₁ htake htp₁ hb₁ ht₁ c; rwa [etake] at h)
    fun r₂ m₂ _ h₂ => ?_
  obtain ⟨M₂, hS₂, hK₂, hst₂⟩ := h₂.after
  refine RefE.mono (R := GrowPost decBool dn m₂ vis fe M₂ eb ResH) ?_
    (fun _ _ _ h => ⟨CoreAfterG.compK hK₂ hst₂.toGrew h.after, h.res, h.valid⟩)
  dsimp only [sectE.k_defeq_lst]
  by_cases h20 : r₂.headD 0 = 0
  · rw [ite_eq_left h20, L.Arena.decBool_false_of h20]
    exact RefE.ret rfl (GrowPost.of_core (CorePost.ret hS₂ rfl hw0))
  rw [ite_eq_right h20, L.Arena.decBool_true_of h20]
  simp only [↓reduceIte]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => etaProjs_callW hi hS₂ hT hb h)
    fun r₃ m₃ ⟨h₃, hr30, hr31, htop₃, hroom₃, hsp₃⟩ => ?_
  obtain ⟨_, _, _, hst₃⟩ := h₃.2.1
  refine RefE.bind_grow (w := id) h₃ (fun M₃ hS₃ _ => ?_)
  dsimp only [sectE.k_eta_projs]
  have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := hS₂.spn
  have htop₂ : spTop m₂ = spTop s₀.mem := hst₂.1.trans htop₁
  have hdrop := hsp₁.drop tk hmin hspn₁
  have e1 : (ao + tk).toNat = ao.toNat + tk.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by have := hsp₁.bound; omega)
  have e2 : (an - tk).toNat = an.toNat - tk.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hmin)
  have hsum : (ao + tk).toNat + (an - tk).toNat = ao.toNat + an.toNat := by rw [e1, e2]; omega
  have hle3 : (spTop s₀.mem).toNat ≤ (spTop m₃).toNat := htop₂ ▸ hst₃.1
  have hdrop₃ : SpineR m₃ (ao + tk) (an - tk) (aargs.toList.drop tk.toNat).toArray :=
    (hdrop.keep hst₂.size hst₂.below (by rw [hsum, htop₁]; exact hat) hspn₁).keep hst₃.size
      hst₃.below (by rw [hsum, htop₂]; exact hat) hspn₂
  have hb₃ : (ao + tk).toNat + (an - tk).toNat ≤ (spTop m₃).toNat := by rw [hsum]; omega
  have hp₃ : (r₃.headD 0).toNat + (r₃.tail.headD 0).toNat ≤ (spTop m₃).toNat := by
    rw [hr30, hr31, htop₃, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _
  have edrop : ((aargs.toList.drop tk.toNat).toArray).toList = aargs.toList.drop ep.toNat := by
    rw [htk]; exact drop_min_eq _ _ _ hlen
  have hs₃ : SlotPre ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hS₃, hs.mode4, hs.eb_mode⟩
  have hD := defeqLst_at p hc n hk F hF hn _ _ dn vis fe M₃ eb mode d (ao + tk) (an - tk) (r₃.headD 0)
    (r₃.tail.headD 0) _ _ hs₃ hdrop₃ hsp₃ hb₃ hp₃
  rw [edrop, List.toList_toArray] at hD
  rw [← bind_pure (defEqList _ _ _ _ _)]
  exact RefE.bind_callE (fun _ => rfl) hD (fun hG => CoreSpecE.of_runs fun _ c => by
      have h := hG.lstE hk hF hn hs₃ hdrop₃ hsp₃ hb₃ hp₃ c; rwa [edrop, List.toList_toArray] at h)
    fun _ _ _ h => RefE.ret rfl (GrowPost.of_core ⟨h.after, rfl, h.resOk⟩)

end L.Arena
