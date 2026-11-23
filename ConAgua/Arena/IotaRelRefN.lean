module

public import ConAgua.Arena.IotaRelRef
public import ConAgua.Arena.IndRealNames
import all ConAgua.Arena.IndRealNames

@[expose] public section

/-!
# The ι reading rule, part 2: the annotations' names (lane ronsync8)

`name_opt_param`, `name_auto_param`, `name_out_param`, `name_semi_out_param` (the twin's
`topName s`) and `name_missing` (`internNNode (.str n "missing")`): `pool_room(k)`, the bytes of
the string stored word by word, `intern_nstr`. The stores are `irWr0` (any list of words), so one
lemma (`strIntern_step`) serves the five functions (`name_rec`'s `recBytes_ok`, generalized).
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-! ## Words stored at the pool top -/

/-- The words `ws` stored at `T + k`, `T + k + 1`, … (`POOL⟨⦃T⦄.tier⟩[⦃T⦄.idx + k] := w`). -/
def irWr (T : Word) : Mem → List Word → Word → Mem
  | m, [], _ => m
  | m, w :: ws, k => irWr T (m.set64 (tierA POOL (T >>> 40)) ((T &&& 1099511627775) + k) w) ws (k + 1)

/-- The words `ws` stored from `T` on (the first store at `⦃T⦄.idx` itself). -/
def irWr0 (T : Word) (m : Mem) : List Word → Mem
  | [] => m
  | w :: ws => irWr T (m.set64 (tierA POOL (T >>> 40)) (T &&& 1099511627775) w) ws 1

/-- The same on the virtual pool. -/
def irSet : Array Word → Nat → List Word → Array Word
  | a, _, [] => a
  | a, o, w :: ws => irSet (a.set! o w) (o + 1) ws

theorem irSet_size : ∀ (ws : List Word) (a : Array Word) (o : Nat), (irSet a o ws).size = a.size
  | [], _, _ => rfl
  | w :: ws, a, o => by simp only [irSet]; rw [irSet_size ws]; simp

theorem irSet_lt : ∀ (ws : List Word) (a : Array Word) (o i : Nat), i < o → (irSet a o ws)[i]? = a[i]?
  | [], _, _, _, _ => rfl
  | w :: ws, a, o, i, h => by
    simp only [irSet]
    rw [irSet_lt ws _ _ _ (by omega), Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [show o ≠ i by omega]

theorem irSet_slice : ∀ (ws : List Word) (a : Array Word) (o : Nat), o + ws.length ≤ a.size →
    sliceL (irSet a o ws) o ws.length = ws
  | [], _, _, _ => by simp [sliceL]
  | w :: ws, a, o, h => by
    simp only [List.length_cons] at h ⊢
    rw [sliceL_succ]
    simp only [irSet]
    rw [irSet_lt ws _ _ _ (by omega), irSet_slice ws _ _ (by simp; omega)]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [show o < a.size by omega]

theorem irWr_top : ∀ (T : Word) (ws : List Word) (X : Mem) (k : Word), (irWr T X ws k).top = X.top
  | _, [], _, _ => rfl
  | T, w :: ws, X, k => by
    simp only [irWr]
    rw [irWr_top T ws]
    exact L.Rom.top_set64_arr _ _ _ _ (Ne.symm (tierA_pool_ne _ _ (by decide) (by decide)))

/-- **Stores above the original top**: a growth stays a growth, the virtual pool is `irSet`. -/
theorem irWr_ok {m : Mem} (hok : PoolOK m) (T : Word) (hT : T = m.top) :
    ∀ (ws : List Word) (X : Mem) (k : Word), Grows m X →
      (X.arr64 (tierA POOL (T >>> 40))).size = (m.arr64 (tierA POOL (T >>> 40))).size →
      (T &&& 1099511627775).toNat + k.toNat + ws.length ≤ (m.arr64 (tierA POOL (T >>> 40))).size →
      Grows m (irWr T X ws k) ∧ vpool (irWr T X ws k) = irSet (vpool X) (T.toNat + k.toNat) ws ∧
        (∀ b, ((irWr T X ws k).arr64 b).size = (X.arr64 b).size)
  | [], X, k, hg, _, _ => ⟨hg, rfl, fun _ => rfl⟩
  | w :: ws, X, k, hg, hsz, hb => by
    simp only [List.length_cons] at hb
    have h41 := hok.top41
    have hsm := hok.small.tier (T >>> 40)
    have hsplit := tag_split T
    have htier := tag_tier_le T (hT ▸ h41)
    subst hT
    have hk1 : (m.top &&& 1099511627775).toNat + k.toNat < (X.arr64 (tierA POOL (m.top >>> 40))).size := by
      rw [hsz]; omega
    have hkk : (m.top + k).toNat = m.top.toNat + k.toNat := by rw [UInt64.toNat_add]; simp; omega
    have g1 := grows_pset_k hg hok (T := m.top) (k := k) (x := w) h41 (by omega) hk1
    have hv1 := vpool_st_k X m.top k w h41 (by rw [hsz]; omega) hk1
    have hk2 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨g, hv, hs⟩ := irWr_ok hok m.top rfl ws _ (k + 1) g1 (by rw [Mem.size_arr64_set64, hsz])
      (by rw [hk2]; omega)
    simp only [irWr]
    refine ⟨g, ?_, fun b => by rw [hs, L.Mem.size64_set64]⟩
    rw [hv, hv1, hkk, hk2]
    simp only [irSet, Nat.add_assoc]

/-- **`pool_room(k)` and the stores of `ws`** (`k = |ws|`): the pool grown, a fresh slice holding
`ws`, the other arrays' sizes kept. -/
theorem irWr0_ok {m : Mem} (hok : PoolOK m) (ws : List Word) (hne : ws ≠ [])
    (hroom : (m.top &&& 1099511627775).toNat + ws.length ≤ (m.arr64 (tierA POOL (m.top >>> 40))).size)
    (hlen : ws.length < 2 ^ 32) :
    Grows m (irWr0 m.top (m.set64 CTL 0 (m.top + ws.length.toUInt64)) ws) ∧
      SliceOK (irWr0 m.top (m.set64 CTL 0 (m.top + ws.length.toUInt64)) ws) m.top ws.length.toUInt64 ∧
      sliceL (vpool (irWr0 m.top (m.set64 CTL 0 (m.top + ws.length.toUInt64)) ws)) m.top.toNat
        ws.length = ws := by
  obtain ⟨w, ws', rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.length_cons] at hroom hlen ⊢
  have hc := hok.ctl
  have h41 := hok.top41
  have hsm := hok.small.tier (m.top >>> 40)
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top h41
  have hne' : tierA POOL (m.top >>> 40) ≠ CTL := Ne.symm (tierA_pool_ne _ _ (by decide) (by decide))
  have hX : (m.set64 CTL 0 (m.top + (ws'.length + 1).toUInt64)).arr64 (tierA POOL (m.top >>> 40)) =
      m.arr64 (tierA POOL (m.top >>> 40)) := Mem.arr64_set64_ne _ _ _ _ _ hne'
  have hn : ((ws'.length + 1).toUInt64).toNat = ws'.length + 1 := by simp; omega
  have g0 := grows_raise m ((ws'.length + 1).toUInt64) hok (by rw [hn]; exact hroom)
  have hlt0 : (m.top &&& 1099511627775).toNat < (m.arr64 (tierA POOL (m.top >>> 40))).size := by omega
  have g1 := grows_pset0 g0 hok (T := m.top) (x := w) h41 (Nat.le_refl _) (by rw [hX]; exact hlt0)
  have hv1 := vpool_stidx0 (m.set64 CTL 0 (m.top + (ws'.length + 1).toUInt64)) m.top w h41
    (by rw [hX]; omega) (by rw [hX]; omega)
  obtain ⟨g, hv, -⟩ := irWr_ok hok m.top rfl ws' _ 1 g1 (by rw [Mem.size_arr64_set64, hX])
    (by rw [show (1 : Word).toNat = 1 from rfl]; omega)
  have htop : (irWr0 m.top (m.set64 CTL 0 (m.top + (ws'.length + 1).toUInt64)) (w :: ws')).top =
      m.top + (ws'.length + 1).toUInt64 := by
    simp only [irWr0]
    rw [irWr_top, L.Rom.top_set64_arr _ _ _ _ hne']
    exact Mem.top_set64 _ _ hc
  refine ⟨g, SliceOK.fresh g htop, ?_⟩
  simp only [irWr0]
  rw [hv, hv1, vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]
  have := irSet_slice (w :: ws') (vpool m) m.top.toNat (by simp [vpool_size]; omega)
  simpa [irSet] using this

/-! ## `pool_room`, the stores, `intern_nstr` -/

section step
variable {p : Prog} {vis : Word} {feR : IFEnv}

/-- **A string name interned from its stored bytes** (`nrF_ok`'s body, any string): `pool_room(k)`,
the words `strWords s` stored at the room, `intern_nstr(x, room, k)` refine
`internNNode (.str x s)` under `StageR`. -/
theorem strIntern_step (hp : NrF p) {n : Nat} {m m1 m3 : Mem} {a : AState} {x k : Word}
    {r1 r3 : List Word} {s : String} {ws : List Word} (hs : strWords s = ws) (hne : ws ≠ [])
    (hk : k = ws.length.toUInt64) (hlen : ws.length < 2 ^ 32)
    (hS : StageR vis feR m a) (hx : H x)
    (h1 : callW p n "pool_room" [k] m = some (r1, m1))
    (h2 : callW p n "intern_nstr" [x, r1.headD 0, k] (irWr0 (r1.headD 0) m1 ws) = some (r3, m3))
    (hlt : ¬ 4294967296 ≤ r3.headD 0) :
    ∃ a', (internNNode (.str (decI x) s)).run a = .ok (decI (r3.headD 0), a') ∧ StageR vis feR m3 a' ∧
      IWGrow m m3 ∧ (r3.headD 0).toNat < 2 ^ 32 := by
  have hpool : PoolOK m := hS.check.arena.base.lit.1
  obtain ⟨ho, hm₁, hno, hroom⟩ := prW_some (callW_pr (hp "pool_room" _ rfl) h1) (by have := hpool.cap; omega)
  have hkn : k.toNat = ws.length := by subst hk; simp; omega
  rw [ho, hm₁] at h2
  rw [hk] at h2
  obtain ⟨hg, hsl, hkw⟩ := irWr0_ok hpool ws hne (by rw [← hkn]; exact hroom) hlen
  generalize hm₂ : irWr0 m.top (m.set64 CTL 0 (m.top + ws.length.toUInt64)) ws = m₂ at h2 hg hsl hkw
  have hR₂ : ArenaR m₂ a := ArenaR.grow m m₂ hg a hS.check.arena.base
  have hmo₂ : ModeOK m₂ := hS.check.mode.grows hg
  have hpc₂ : pcap m₂ < 2 ^ 64 := by rw [hg.pcapEq]; have := hpool.cap; omega
  have hkn' : (ws.length.toUInt64).toNat = ws.length := by simp; omega
  have hcap₂ : m.top.toNat + (ws.length.toUInt64).toNat ≤ pcap m₂ := by
    have := hsl.le; have := hg.cap; omega
  obtain ⟨s₃, hs₃, -, hok, hR₃, hres⟩ := triple_of_callW
    (internNStr_refinesA p (hp "lit_hash" _ rfl) (hp "limbs_eq" _ rfl) (hp "nstr_match" _ rfl)
      (hp "nstr_find" _ rfl) (hp "nstr_push" _ rfl) (hp "intern_nstr" _ rfl) a n ⟨m₂, Locals.init []⟩
      x m.top _ hR₂ hx hsl s (by rw [hkn', hs]; exact hkw) (ModeOK.slice0 hmo₂ hsl)) h2
  obtain ⟨s₃', hs₃', -, hI⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internNStr_spec p (hp "lit_hash" _ rfl) (hp "limbs_eq" _ rfl) (hp "nstr_match" _ rfl)
      (hp "nstr_find" _ rfl) (hp "nstr_push" _ rfl) (hp "intern_nstr" _ rfl) n _ x m.top _ hpc₂ hcap₂) h2
  simp only at hs₃ hR₃ hs₃' hI
  rw [hs₃] at hR₃
  rw [hs₃'] at hI
  have hfr : MemFrame [POOL, POOL1, NSREC, tier1 NSREC, NSSLOT, tier1 NSSLOT] [0, 36, 37] m m3 :=
    ((grows_frame m m₂ hg).mono (by simp) (by simp)).trans
      ((consInternM_frame nstrCS_wf hI).mono (by simp [ConsSch.wset, nstrCS]) (by simp [nstrCS]))
  have hmo₃ : ModeOK m3 := hmo₂.frame (consInternM_frame nstrCS_wf hI) (by simp [nstrCS]) (by simp [nstrCS])
  obtain ⟨a', hrun, hS', hg', -, -⟩ := stage_of_name hS (internNNode_str_run (decI x) s a) hok hR₃
    hres hfr (by simp [tier1, POOL, POOL1, NSREC, NSSLOT]) (by simp) (fun _ => ⟨DerR.lvl, rfl⟩)
    (fun _ => ⟨DerR.lvl, rfl⟩) (fun _ => ⟨rfl, rfl⟩) hmo₃
  refine ⟨a', hrun, hS', hg', ?_⟩
  have := mt UInt64.le_iff_toNat_le.mpr hlt
  have e : (4294967296 : Word).toNat = 4294967296 := rfl
  rw [e] at this; omega

end step

/-! ## The five name functions -/

section names
variable {p : Prog} {vis : Word} {feR : IFEnv}

theorem strWords_missing : strWords "missing" = [109, 105, 115, 115, 105, 110, 103] := by decide
theorem strWords_optParam : strWords "optParam" = [111, 112, 116, 80, 97, 114, 97, 109] := by decide
theorem strWords_autoParam : strWords "autoParam" = [97, 117, 116, 111, 80, 97, 114, 97, 109] := by decide
theorem strWords_outParam : strWords "outParam" = [111, 117, 116, 80, 97, 114, 97, 109] := by decide
theorem strWords_semiOutParam :
    strWords "semiOutParam" = [115, 101, 109, 105, 79, 117, 116, 80, 97, 114, 97, 109] := by decide

/-- **`name_missing(x)` refines `internNNode (.str x "missing")`** (`annWitness`'s `n.missing`). -/
theorem nameMissing_rel (hf : p.lookup "name_missing" = some nameMissingL) (hp : NrF p) {n : Nat}
    {m m' : Mem} {a : AState} {x : Word} {r : List Word}
    (hc : callW p n "name_missing" [x] m = some (r, m')) (hS : StageR vis feR m a) (hx : H x) :
    ∃ a', (internNNode (.str (decI x) "missing")).run a = .ok (decI (r.headD 0), a') ∧
      StageR vis feR m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (nameMissing_specW p hf n _ x) hc
  rcases n with _ | n
  · rw [nameMissingW.eq_1] at hW; cases hW
  rw [nameMissingW.arm1] at hW
  rcases h1 : callW p n "pool_room" [7] m with _ | ⟨r1, m1⟩
  · rw [h1, nameMissingW.k_pool_room.none] at hW; cases hW
  rw [h1, nameMissingW.k_pool_room.arm1] at hW
  change nameMissingW.k_intern_nstr p (callW p n "intern_nstr" [x, r1.headD 0, 7]
    (irWr0 (r1.headD 0) m1 [109, 105, 115, 115, 105, 110, 103])) = _ at hW
  rcases h2 : callW p n "intern_nstr" [x, r1.headD 0, 7]
    (irWr0 (r1.headD 0) m1 [109, 105, 115, 115, 105, 110, 103]) with _ | ⟨r3, m3⟩
  · rw [h2, nameMissingW.k_intern_nstr.none] at hW; cases hW
  by_cases hlt : 4294967296 ≤ r3.headD 0
  · rw [h2, nameMissingW.k_intern_nstr.abort1 _ _ _ hlt] at hW; cases hW
  rw [h2, nameMissingW.k_intern_nstr.arm1 _ _ _ hlt] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  exact strIntern_step (k := 7) (r3 := r3) hp strWords_missing (by simp) (by decide) (by simp) hS hx h1 h2 hlt

/-- **`name_opt_param()` refines `topName "optParam"`**. -/
@[refines ConRon.Arena.topName]
theorem nameOptParam_rel (hf : p.lookup "name_opt_param" = some nameOptParamL) (hpa : NaF p) (hp : NrF p) {n : Nat}
    {m m' : Mem} {a : AState} {r : List Word}
    (hc : callW p n "name_opt_param" [] m = some (r, m')) (hS : StageR vis feR m a) :
    ∃ a', (topName "optParam").run a = .ok (decI (r.headD 0), a') ∧
      StageR vis feR m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (nameOptParam_specW p hf n _) hc
  rcases n with _ | n
  · rw [nameOptParamW.eq_1] at hW; cases hW
  rw [nameOptParamW.arm1] at hW
  rcases h0 : callW p n "intern_nanon" [] m with _ | ⟨r0, m0⟩
  · rw [h0, nameOptParamW.k_intern_nanon.none] at hW; cases hW
  by_cases hl0 : 4294967296 ≤ r0.headD 0
  · rw [h0, nameOptParamW.k_intern_nanon.abort1 _ _ _ _ hl0] at hW; cases hW
  rw [h0, nameOptParamW.k_intern_nanon.arm1 _ _ _ _ hl0] at hW
  obtain ⟨s0, hs0, -, hW0⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (naF_spec p hpa n _ []) h0
  simp only at hs0 hW0
  rw [hs0] at hW0
  obtain ⟨x0, a0, hrun0, hS0, hg0, hx0, hd0⟩ := naF_ok (fun _ => none) vis feR m m0 a r0 hW0 hS
  rcases h1 : callW p n "pool_room" [8] m0 with _ | ⟨r1, m1⟩
  · rw [h1, nameOptParamW.k_pool_room.none] at hW; cases hW
  rw [h1, nameOptParamW.k_pool_room.arm1] at hW
  change nameOptParamW.k_intern_nstr p (callW p n "intern_nstr" [r0.headD 0, r1.headD 0, 8]
    (irWr0 (r1.headD 0) m1 [111, 112, 116, 80, 97, 114, 97, 109])) = _ at hW
  rcases h2 : callW p n "intern_nstr" [r0.headD 0, r1.headD 0, 8]
    (irWr0 (r1.headD 0) m1 [111, 112, 116, 80, 97, 114, 97, 109]) with _ | ⟨r3, m3⟩
  · rw [h2, nameOptParamW.k_intern_nstr.none] at hW; cases hW
  by_cases hlt : 4294967296 ≤ r3.headD 0
  · rw [h2, nameOptParamW.k_intern_nstr.abort1 _ _ _ hlt] at hW; cases hW
  rw [h2, nameOptParamW.k_intern_nstr.arm1 _ _ _ hlt] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨a3, hrun3, hS3, hg3, hlt3⟩ := strIntern_step (k := 8) (r3 := r3) hp strWords_optParam (by simp)
    (by decide) (by simp) hS0 hx0 h1 h2 hlt
  refine ⟨a3, ?_, hS3, hg0.trans hg3, hlt3⟩
  simp only [topName]
  rw [StateT.run_bind, hrun0, except_ok_bind, ← hd0]
  exact hrun3

/-- **`name_auto_param()` refines `topName "autoParam"`**. -/
@[refines ConRon.Arena.topName]
theorem nameAutoParam_rel (hf : p.lookup "name_auto_param" = some nameAutoParamL) (hpa : NaF p) (hp : NrF p) {n : Nat}
    {m m' : Mem} {a : AState} {r : List Word}
    (hc : callW p n "name_auto_param" [] m = some (r, m')) (hS : StageR vis feR m a) :
    ∃ a', (topName "autoParam").run a = .ok (decI (r.headD 0), a') ∧
      StageR vis feR m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (nameAutoParam_specW p hf n _) hc
  rcases n with _ | n
  · rw [nameAutoParamW.eq_1] at hW; cases hW
  rw [nameAutoParamW.arm1] at hW
  rcases h0 : callW p n "intern_nanon" [] m with _ | ⟨r0, m0⟩
  · rw [h0, nameAutoParamW.k_intern_nanon.none] at hW; cases hW
  by_cases hl0 : 4294967296 ≤ r0.headD 0
  · rw [h0, nameAutoParamW.k_intern_nanon.abort1 _ _ _ _ hl0] at hW; cases hW
  rw [h0, nameAutoParamW.k_intern_nanon.arm1 _ _ _ _ hl0] at hW
  obtain ⟨s0, hs0, -, hW0⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (naF_spec p hpa n _ []) h0
  simp only at hs0 hW0
  rw [hs0] at hW0
  obtain ⟨x0, a0, hrun0, hS0, hg0, hx0, hd0⟩ := naF_ok (fun _ => none) vis feR m m0 a r0 hW0 hS
  rcases h1 : callW p n "pool_room" [9] m0 with _ | ⟨r1, m1⟩
  · rw [h1, nameAutoParamW.k_pool_room.none] at hW; cases hW
  rw [h1, nameAutoParamW.k_pool_room.arm1] at hW
  change nameAutoParamW.k_intern_nstr p (callW p n "intern_nstr" [r0.headD 0, r1.headD 0, 9]
    (irWr0 (r1.headD 0) m1 [97, 117, 116, 111, 80, 97, 114, 97, 109])) = _ at hW
  rcases h2 : callW p n "intern_nstr" [r0.headD 0, r1.headD 0, 9]
    (irWr0 (r1.headD 0) m1 [97, 117, 116, 111, 80, 97, 114, 97, 109]) with _ | ⟨r3, m3⟩
  · rw [h2, nameAutoParamW.k_intern_nstr.none] at hW; cases hW
  by_cases hlt : 4294967296 ≤ r3.headD 0
  · rw [h2, nameAutoParamW.k_intern_nstr.abort1 _ _ _ hlt] at hW; cases hW
  rw [h2, nameAutoParamW.k_intern_nstr.arm1 _ _ _ hlt] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨a3, hrun3, hS3, hg3, hlt3⟩ := strIntern_step (k := 9) (r3 := r3) hp strWords_autoParam (by simp)
    (by decide) (by simp) hS0 hx0 h1 h2 hlt
  refine ⟨a3, ?_, hS3, hg0.trans hg3, hlt3⟩
  simp only [topName]
  rw [StateT.run_bind, hrun0, except_ok_bind, ← hd0]
  exact hrun3

/-- **`name_out_param()` refines `topName "outParam"`**. -/
@[refines ConRon.Arena.topName]
theorem nameOutParam_rel (hf : p.lookup "name_out_param" = some nameOutParamL) (hpa : NaF p) (hp : NrF p) {n : Nat}
    {m m' : Mem} {a : AState} {r : List Word}
    (hc : callW p n "name_out_param" [] m = some (r, m')) (hS : StageR vis feR m a) :
    ∃ a', (topName "outParam").run a = .ok (decI (r.headD 0), a') ∧
      StageR vis feR m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (nameOutParam_specW p hf n _) hc
  rcases n with _ | n
  · rw [nameOutParamW.eq_1] at hW; cases hW
  rw [nameOutParamW.arm1] at hW
  rcases h0 : callW p n "intern_nanon" [] m with _ | ⟨r0, m0⟩
  · rw [h0, nameOutParamW.k_intern_nanon.none] at hW; cases hW
  by_cases hl0 : 4294967296 ≤ r0.headD 0
  · rw [h0, nameOutParamW.k_intern_nanon.abort1 _ _ _ _ hl0] at hW; cases hW
  rw [h0, nameOutParamW.k_intern_nanon.arm1 _ _ _ _ hl0] at hW
  obtain ⟨s0, hs0, -, hW0⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (naF_spec p hpa n _ []) h0
  simp only at hs0 hW0
  rw [hs0] at hW0
  obtain ⟨x0, a0, hrun0, hS0, hg0, hx0, hd0⟩ := naF_ok (fun _ => none) vis feR m m0 a r0 hW0 hS
  rcases h1 : callW p n "pool_room" [8] m0 with _ | ⟨r1, m1⟩
  · rw [h1, nameOutParamW.k_pool_room.none] at hW; cases hW
  rw [h1, nameOutParamW.k_pool_room.arm1] at hW
  change nameOutParamW.k_intern_nstr p (callW p n "intern_nstr" [r0.headD 0, r1.headD 0, 8]
    (irWr0 (r1.headD 0) m1 [111, 117, 116, 80, 97, 114, 97, 109])) = _ at hW
  rcases h2 : callW p n "intern_nstr" [r0.headD 0, r1.headD 0, 8]
    (irWr0 (r1.headD 0) m1 [111, 117, 116, 80, 97, 114, 97, 109]) with _ | ⟨r3, m3⟩
  · rw [h2, nameOutParamW.k_intern_nstr.none] at hW; cases hW
  by_cases hlt : 4294967296 ≤ r3.headD 0
  · rw [h2, nameOutParamW.k_intern_nstr.abort1 _ _ _ hlt] at hW; cases hW
  rw [h2, nameOutParamW.k_intern_nstr.arm1 _ _ _ hlt] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨a3, hrun3, hS3, hg3, hlt3⟩ := strIntern_step (k := 8) (r3 := r3) hp strWords_outParam (by simp)
    (by decide) (by simp) hS0 hx0 h1 h2 hlt
  refine ⟨a3, ?_, hS3, hg0.trans hg3, hlt3⟩
  simp only [topName]
  rw [StateT.run_bind, hrun0, except_ok_bind, ← hd0]
  exact hrun3

/-- **`name_semi_out_param()` refines `topName "semiOutParam"`**. -/
@[refines ConRon.Arena.topName]
theorem nameSemiOutParam_rel (hf : p.lookup "name_semi_out_param" = some nameSemiOutParamL) (hpa : NaF p) (hp : NrF p) {n : Nat}
    {m m' : Mem} {a : AState} {r : List Word}
    (hc : callW p n "name_semi_out_param" [] m = some (r, m')) (hS : StageR vis feR m a) :
    ∃ a', (topName "semiOutParam").run a = .ok (decI (r.headD 0), a') ∧
      StageR vis feR m' a' ∧ IWGrow m m' ∧ (r.headD 0).toNat < 2 ^ 32 := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (nameSemiOutParam_specW p hf n _) hc
  rcases n with _ | n
  · rw [nameSemiOutParamW.eq_1] at hW; cases hW
  rw [nameSemiOutParamW.arm1] at hW
  rcases h0 : callW p n "intern_nanon" [] m with _ | ⟨r0, m0⟩
  · rw [h0, nameSemiOutParamW.k_intern_nanon.none] at hW; cases hW
  by_cases hl0 : 4294967296 ≤ r0.headD 0
  · rw [h0, nameSemiOutParamW.k_intern_nanon.abort1 _ _ _ _ hl0] at hW; cases hW
  rw [h0, nameSemiOutParamW.k_intern_nanon.arm1 _ _ _ _ hl0] at hW
  obtain ⟨s0, hs0, -, hW0⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (naF_spec p hpa n _ []) h0
  simp only at hs0 hW0
  rw [hs0] at hW0
  obtain ⟨x0, a0, hrun0, hS0, hg0, hx0, hd0⟩ := naF_ok (fun _ => none) vis feR m m0 a r0 hW0 hS
  rcases h1 : callW p n "pool_room" [12] m0 with _ | ⟨r1, m1⟩
  · rw [h1, nameSemiOutParamW.k_pool_room.none] at hW; cases hW
  rw [h1, nameSemiOutParamW.k_pool_room.arm1] at hW
  change nameSemiOutParamW.k_intern_nstr p (callW p n "intern_nstr" [r0.headD 0, r1.headD 0, 12]
    (irWr0 (r1.headD 0) m1 [115, 101, 109, 105, 79, 117, 116, 80, 97, 114, 97, 109])) = _ at hW
  rcases h2 : callW p n "intern_nstr" [r0.headD 0, r1.headD 0, 12]
    (irWr0 (r1.headD 0) m1 [115, 101, 109, 105, 79, 117, 116, 80, 97, 114, 97, 109]) with _ | ⟨r3, m3⟩
  · rw [h2, nameSemiOutParamW.k_intern_nstr.none] at hW; cases hW
  by_cases hlt : 4294967296 ≤ r3.headD 0
  · rw [h2, nameSemiOutParamW.k_intern_nstr.abort1 _ _ _ hlt] at hW; cases hW
  rw [h2, nameSemiOutParamW.k_intern_nstr.arm1 _ _ _ hlt] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨a3, hrun3, hS3, hg3, hlt3⟩ := strIntern_step (k := 12) (r3 := r3) hp strWords_semiOutParam (by simp)
    (by decide) (by simp) hS0 hx0 h1 h2 hlt
  refine ⟨a3, ?_, hS3, hg0.trans hg3, hlt3⟩
  simp only [topName]
  rw [StateT.run_bind, hrun0, except_ok_bind, ← hd0]
  exact hrun3

end names

end L.Ind
