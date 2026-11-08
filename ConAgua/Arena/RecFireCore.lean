module

import ConAgua.Arena.InstLPLevel2
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.InstLPRef
import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Front.StateDR
import ConRon.Bridge.Grind
public import ConAgua.Arena.InstLPLevel
public import ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# `rec_fire_levels` under `CoreS` (lane `defeq2`)

`RecFireLevelsOK` (`WhnfIota.lean`), the last `KnotCallees` field of lane `defeq2`'s, from the
pieces of `InstLPRef2.lean`'s `recFireLevelsW_ok` (helper `whnf3-lp`, at `ArenaD` and
`StoreWF`), each redone under `CoreS` with lane `whnf4`'s level arms (`InstLPLevel*.lean`):

* `ls_node(us)` returns only on a stored list, so `StoreDen.lsAll` reads it back;
* `keys_push` writes the recursor's level-parameter names above the stack top (`CoreS.frame_stk`);
* the elements: `sle_go` (a nested rule's stored levels, each read back and substituted,
  `lvSubIntW_core`) or `slp_go` (a plain rule's constructor parameters, each looked up and
  interned, `lvInternW_core`, or interned as a parameter node), the results on the stack;
* `spn_ls` interns them as a list (`spnLs_core`), and the stack top is put back.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

section lev
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-- `CoreS` with the name readback cache replaced by one that holds readbacks. -/
theorem CoreS.withReadNC {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb)
    (X : Std.HashMap NIdx Name) (hc : ReadNCOK { a with caches := { a.caches with readNC := X } }) :
    CoreS dn m { a with caches := { a.caches with readNC := X } } vis fe M eb :=
  CoreS.readCaches hS X a.caches.readLsC (by exact hS.readLs) hc

/-- **A result put on the stack at or above the top** keeps the relation and the stack. -/
theorem stackPut_core {m₀ m₁ : Mem} {a : AState} {b h : Word} (hS : CoreS dn m₁ a vis fe M eb)
    (hk : StackKept m₀ m₁) (hb : (spTop m₀).toNat ≤ b.toNat) :
    CoreS dn (m₁.set64 SPN b h) a vis fe M eb ∧ StackKept m₀ (m₁.set64 SPN b h) := by
  have hf₂ : MemFrame [SPN] [] m₁ (m₁.set64 SPN b h) := MemFrame.set64 _ _ (by decide) _ _
  have htop₂ : spTop (m₁.set64 SPN b h) = spTop m₁ := by
    simp only [spTop, Mem.arr64_set64_ne _ _ _ _ _ (show (CTL : TieredArray) ≠ SPN by decide)]
  refine ⟨hS.frame_stk hf₂ (by simp) (by simp), hk.trans ?_⟩
  exact StackKept.of_spnFrame (hf₂.mono (by simp) (by simp)) htop₂ (fun i hi => by
    simp only [spW]; rw [rdW_set64]
    have : ¬ b = i := fun e => by
      subst e; rw [hk.top] at hi; have := UInt64.lt_iff_toNat_lt.mp hi; omega
    simp [this])

/-- A handle word of a record-pool slice. -/
theorem hslice_cons {k : IdxKind} {b : Array Word} {o : Word} {j : Nat} {x : Idx k}
    {xs : List (Idx k)} (h : hslice? (aread b) o.toNat (j + 1) = some (x :: xs)) :
    ∃ w : Word, HW w ∧ x = decI w ∧ rdW b o = w ∧ hslice? (aread b) (o.toNat + 1) j = some xs := by
  sorry

/-- An empty slice. -/
theorem hslice_nil {k : IdxKind} {b : Array Word} {o l : Word}
    (h : hslice? (aread b) o.toNat l.toNat = some ([] : List (Idx k))) : l = 0 := by
  sorry

/-! ## `sle_go`: a nested rule's stored levels -/

/-- **The model of `sle_go` refines `substLevelsAt ks vs lvls`** under `CoreS`, over the record-pool
slice `(o, l)` of levels that read back: the results land at `SPN[b ‥ b + l)`, at or above the
stack top. -/
theorem sleElemW_core {ko kc vo vc : Word} {ks : List Name} {us : List LIdx} {vs : List Level} :
    ∀ (lvls : List LIdx) (n : Nat) (m m' : Mem) (a : AState) (o l b : Word),
    CoreS dn m a vis fe M eb → ILWEnv m a ko kc vo vc ks us vs →
    hslice? (erecP m) o.toNat l.toNat = some lvls → o.toNat + l.toNat < 2 ^ 64 →
    (∀ u ∈ lvls, ∃ L, denoteL a.store.ls u = some L) →
    (spTop m).toNat ≤ b.toNat → b.toNat + l.toNat ≤ (m.arr64 SPN).size →
    slElemW EREC n m o l b ko kc vo vc = some m' →
    ∃ hs a', (substLevelsAt ks vs lvls).run a = .ok (hs, a') ∧
      CoreS dn m' a' vis fe M eb ∧ ILWGrow a a' ∧ StackKept m m' ∧
      sliceL (m'.arr64 SPN) b.toNat l.toNat = lsWords hs ∧
      (∀ i : Word, i.toNat < b.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i) ∧
      (∀ c ∈ hs, ∃ L, denoteL a'.store.ls c = some L) := by
  sorry

/-! ## `slp_go`: a plain rule's constructor parameters -/

/-- **One parameter's substitute under `CoreS`**: its value interned on a hit, the parameter
node on a miss. -/
theorem slpOne_core {n : Nat} {m m₁ : Mem} {a : AState} {ko kc vo vc w h : Word} {nm : Name}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hE : ILWEnv m a ko kc vo vc ks us vs)
    (hn : nameN a.store.lss.ls.ns w nm) (hh : h.toNat < 2 ^ 32)
    (hW : slpOne n m w (lookupW SPN POOL n m ko kc vo vc w) = some (h, m₁)) :
    ∃ a₁, (internLevel (Level.subst ks vs (.param nm))).run a = .ok (decI h, a₁) ∧
      LvOut dn vis fe M eb m m₁ a a₁ h := by
  have htop := m.top.toNat_lt
  have h41 := hS.arena.base.lit.1.top41
  have hv := lvsR_of_slice hS.arena.base us vs vo vc hE.vals (by have := hE.vtop; omega) hE.vden
  cases e : lookupW SPN POOL n m ko kc vo vc w with
  | none => rw [e] at hW; simp [slpOne] at hW
  | some fv =>
  obtain ⟨f, v⟩ := fv
  rw [e] at hW
  rcases lookupW_ok (nameN_rel _ hS.nwf) n _ _ _ _ _ _ _ _ _ _ _ hE.keys hv.toAR hn e with
    ⟨hf, hvl⟩ | ⟨rfl, hgo⟩
  · rw [slpOne_hit n m w f v hf] at hW
    obtain ⟨a₁, hrun, o⟩ := lvInternW_core _ n m a v h m₁ hS hvl hW
    exact ⟨a₁, by simpa [Level.subst] using hrun, o⟩
  · rw [slpOne_miss] at hW
    have hnb : ¬ (4294967296 : Word) ≤ h := fun c => by
      have := UInt64.le_iff_toNat_le.mp c; simp at this; omega
    have hW' : liNodeK (pinternW m w) = some (h, m₁) := by rw [hW]; simp [liNodeK, hnb]
    obtain ⟨a', hrun, ho⟩ := liNode_core (.param (decI w)) (fun m => pinternW m w)
      (fun m a w' m' hA hI => by
        obtain ⟨ok, hR, res, hfr⟩ := L.Front.param_A m a hA w' m' w hn.1 hI
        exact ⟨ok, hR, res, hfr.mono lvSch_sub.2.2.2.2.2.2.2.2.1 lvSch_sub.2.2.2.2.2.2.2.2.2⟩)
      hS (fun c hc => by simp [LNodeView.lchildren] at hc)
      (fun n hn' => by
        simp only [LNodeView.nchildren, List.mem_cons, List.mem_nil_iff, or_false] at hn'
        subst hn'; exact ⟨nm, hn.2⟩) hW'
    refine ⟨a', ?_, ho⟩
    simp only [Level.subst, hgo]
    show (internName nm >>= fun hn => internLNode (.param hn)).run a = _
    rw [StateT.run_bind, internName_nameN_run a hS.nwf hn]; exact hrun

/-- **The model of `slp_go` refines `substParamLevels ks vs ids`** under `CoreS`, over the
record-pool name slice `(o, l)` of names that read back: the results land at `SPN[b ‥ b + l)`. -/
theorem slpElemW_core {ko kc vo vc : Word} {ks : List Name} {us : List LIdx} {vs : List Level} :
    ∀ (ids : List NIdx) (n : Nat) (m m' : Mem) (a : AState) (o l b : Word),
    CoreS dn m a vis fe M eb → ILWEnv m a ko kc vo vc ks us vs →
    hslice? (erecP m) o.toNat l.toNat = some ids → o.toNat + l.toNat < 2 ^ 64 →
    (∀ u ∈ ids, ∃ nm, denoteN a.store.ns u = some nm) →
    (spTop m).toNat ≤ b.toNat → b.toNat + l.toNat ≤ (m.arr64 SPN).size →
    slpW n m o l b ko kc vo vc = some m' →
    ∃ hs a', (substParamLevels ks vs ids).run a = .ok (hs, a') ∧
      CoreS dn m' a' vis fe M eb ∧ ILWGrow a a' ∧ StackKept m m' ∧
      sliceL (m'.arr64 SPN) b.toNat l.toNat = lsWords hs ∧
      (∀ i : Word, i.toNat < b.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i) ∧
      (∀ c ∈ hs, ∃ L, denoteL a'.store.ls c = some L) := by
  sorry

end lev

/-! ## `rec_fire_levels` -/

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, x, hx => by simp at hx
  | y :: ys, zs, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨z, hz, ws, hws, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨z, hz⟩
    · exact mapM_some_mem ys ws hws x hx

/-- **The tail of `rec_fire_levels` under `CoreS`**: the list interned from the stack slice, the
stack top put back. -/
theorem rflTail_core {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} (p : Prog) (hL : LsProg p) {n : Nat} {m₀ m₂ m₃ : Mem} {a₂ : AState}
    {b c l : Word} {hs : List LIdx} {rs : List Word} (hS₃ : CoreS dn m₂ a₂ vis fe M eb)
    (hgr : StackGrew m₀ m₂) (hb : b = spTop m₀)
    (hsl : sliceL (m₂.arr64 SPN) c.toNat l.toNat = lsWords hs) (hcl : c.toNat + l.toNat < 2 ^ 64)
    (hel : ∀ c ∈ hs, ∃ L, denoteL a₂.store.ls c = some L)
    (h4 : callW p n "spn_ls" [c, l] m₂ = some (rs, m₃)) :
    ∃ a₄, (internLsNode hs).run a₂ = .ok (decI (rs.headD 0), a₄) ∧
      CoreS dn (m₃.set64 CTL 136 b) a₄ vis fe M eb ∧ StackKept m₀ (m₃.set64 CTL 136 b) ∧
      HW (rs.headD 0) := by
  obtain ⟨a₄, hrun, hS₄, hk₄, hw₄, -⟩ := spnLs_core p hL hS₃ hsl hcl hel h4
  refine ⟨a₄, hrun, hS₄.frame_stk (MemFrame.setCtl m₃ 136 _) (by simp) (by simp), ?_, hw₄⟩
  rw [hb]
  exact StackKept.restoreG (hgr.trans hk₄.toGrew) (by have := hS₄.ctl136; simpa using this)

/-- **`rec_fire_levels` refines `recFireLevels` under `CoreS`** (`RecFireLevelsOK`). -/
theorem recFireLevelsOK_of (p : Prog) (hL : LsProg p) : RecFireLevelsOK p := by
  sorry

end L.Arena
