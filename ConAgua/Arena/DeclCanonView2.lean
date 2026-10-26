import ConAgua.Arena.DeclCanonView
import ConAgua.Arena.LevelEquiv
import ConAgua.Arena.LevelArena

/-!
# `view_ls` in L: the level-list handle's slice copied into the pool (lane `decls3`)

`pool_copy(d, s, l)` (`IW[d + j] := POOL[s + j]`), `view_ls(us)` = `ls_node`, `iw_alloc`,
`pool_copy`: word models with the source bound checked (the L code aborts out of bounds), specs,
and the relational lemma against the twin's `viewLs` under the stage relation.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The model of `pool_copy`. -/
def poolCopyW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | n + 1, m, d, s, l =>
    if l = 0 then some m
    else if (m.arr64 (tierA 0 (s >>> 40))).size ≤ (s &&& 1099511627775).toNat then none
    else poolCopyW n (m.set64 IW d (prd m s)) (d + 1) (s + 1) (l - 1)

section arms
variable (n : Nat) (m : Mem) (d s l : Word)
theorem poolCopyW_nil (hl : l = 0) : poolCopyW (n + 1) m d s l = some m := by simp [poolCopyW, hl]
theorem poolCopyW_step (hl : l ≠ 0) (hs : (s &&& 1099511627775).toNat < (m.arr64 (tierA 0 (s >>> 40))).size) :
    poolCopyW (n + 1) m d s l =
      poolCopyW n (m.set64 IW d (prd m s)) (d + 1) (s + 1) (l - 1) := by
  rw [poolCopyW]; simp only [hl, ↓reduceIte]; rw [ite_eq_right (Nat.not_le.mpr hs)]
theorem poolCopyW_oob (hl : l ≠ 0) (hs : (m.arr64 (tierA 0 (s >>> 40))).size ≤ (s &&& 1099511627775).toNat) :
    poolCopyW (n + 1) m d s l = none := by
  rw [poolCopyW]; simp only [hl, ↓reduceIte]; rw [ite_eq_left hs]
end arms

grind_pattern [ind_grind] poolCopyW_nil => poolCopyW (n + 1) m d s l
grind_pattern [ind_grind] poolCopyW_step => poolCopyW (n + 1) m d s l

theorem poolCopy_spec (p : Prog) (hp : p.lookup "pool_copy" = some poolCopy) (n : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "pool_copy" [d, s, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ poolCopyW n s₀.mem d s l = some s'.mem; ⊤⦄ := by
  induction n with
  | zero => intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, poolCopy]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, poolCopy]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20)


/-- **What a `POOL → IW` copy leaves**: every array but `IW` as it was, `IW` the same size, the
destination holding the pool source (a slice of addresses below `2^41`), the rest of `IW`
unchanged. -/
theorem poolCopyW_get (n : Nat) : ∀ (m m' : Mem) (d s l : Word), poolCopyW n m d s l = some m' →
    s.toNat + l.toNat ≤ 2 ^ 41 → d.toNat + l.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 →
    (∀ b, b ≠ IW → m'.arr64 b = m.arr64 b) ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
    m'.words.size = m.words.size ∧
    ∀ i, (m'.arr64 IW)[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + l.toNat then (vpool m)[s.toNat + (i - d.toNat)]?
      else (m.arr64 IW)[i]? := by
  induction n with
  | zero => intro m m' d s l h; simp [poolCopyW] at h
  | succ n ih =>
    intro m m' d s l h hE hd hsz
    by_cases hl : l = 0
    · rw [poolCopyW_nil n m d s l hl] at h
      cases h
      subst hl
      refine ⟨fun _ _ => rfl, rfl, rfl, fun i => ?_⟩
      have : ¬ (d.toNat ≤ i ∧ i < d.toNat + (0 : Word).toNat) := by
        simp only [UInt64.toNat_zero]; omega
      simp only [this, ite_false]
    · by_cases hso : (m.arr64 (tierA 0 (s >>> 40))).size ≤ (s &&& 1099511627775).toNat
      · rw [poolCopyW_oob n m d s l hl hso] at h; simp at h
      rw [poolCopyW_step n m d s l hl (by omega)] at h
      have hl0 : 0 < l.toNat := by
        have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hl1 : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub]; simp; omega
      have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hdlt : d.toNat < (m.arr64 IW).size := by omega
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.set64 IW d (prd m s) := ⟨_, rfl⟩
      rw [← hm1] at h
      have hsz1 : (m1.arr64 IW).size = (m.arr64 IW).size := by
        rw [hm1, Mem.arr64_set64_same]; simp
      have hE1v : vpool m1 = vpool m := by rw [hm1]; exact vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩
      have hget1 : ∀ i, (m1.arr64 IW)[i]? = if i = d.toNat then (vpool m)[s.toNat]?
          else (m.arr64 IW)[i]? := by
        intro i
        rw [hm1, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        by_cases hi : d.toNat = i
        · subst hi
          simp only [hdlt, ite_true]
          rw [vpool_get? m s (by omega)]
        · simp [hi, Ne.symm hi]
      obtain ⟨hA, hS, hW, hG⟩ := ih m1 m' (d + 1) (s + 1) (l - 1) h
        (by rw [hs1, hl1]; omega) (by rw [hd1, hl1, hsz1]; omega) (by rw [hsz1]; exact hsz)
      rw [hE1v] at hG
      refine ⟨fun b hb => (hA b hb).trans ?_, hS.trans hsz1, hW.trans ?_, fun i => ?_⟩
      · rw [hm1, Mem.arr64_set64_ne _ _ _ _ _ hb]
      · rw [hm1]; exact Mem.words_size_set64 _ _ _ _
      · rw [hG i, hd1, hl1, hs1]
        by_cases hi : d.toNat ≤ i ∧ i < d.toNat + l.toNat
        · rw [ite_eq_left hi]
          by_cases hid : i = d.toNat
          · subst hid
            have : ¬ (d.toNat + 1 ≤ d.toNat ∧ d.toNat < d.toNat + 1 + (l.toNat - 1)) := by omega
            rw [ite_eq_right this, hget1, ite_eq_left rfl]; simp
          · have h2 : d.toNat + 1 ≤ i ∧ i < d.toNat + 1 + (l.toNat - 1) := by omega
            rw [ite_eq_left h2]
            congr 1; omega
        · rw [ite_eq_right hi, ite_eq_right (by omega), hget1, ite_eq_right (by omega)]


/-! ## `view_ls` -/

/-- The model of `view_ls(us)` at the caller's fuel `n`: the node's slice, a fresh pool slice, the
copy (at `n - 1`). -/
def viewLsW (n : Nat) (m : Mem) (us : Word) : Option (List Word × Mem) :=
  if lsNodeW m us = [] then none
  else
    match allocW m ((lsNodeW m us).tail.headD 0) with
    | none => none
    | some (q, m1) =>
      match poolCopyW (n - 1) m1 q ((lsNodeW m us).headD 0) ((lsNodeW m us).tail.headD 0) with
      | none => none
      | some m2 => some ([q, (lsNodeW m us).tail.headD 0], m2)

theorem viewLs_specW (p : Prog) (hn : p.lookup "ls_node" = some lsNode)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hc : p.lookup "pool_copy" = some poolCopy)
    (hp : p.lookup "view_ls" = some viewLsL) (n : Nat) (s₀ : St) (us : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "view_ls" [us]
    ⦃fun r s' => LocEq s' s₀ ∧ viewLsW n s₀.mem us = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, viewLsL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        lsNode_spec p hn n, iwAlloc_specW p ha n, poolCopy_spec p hc n] <;>
      finish (gen := 20) [viewLsW]

/-- **The converse of `lsNodeW_store`**: a returning `ls_node` means the twin's `viewLs` succeeds. -/
theorem lsView_of_lsNodeW {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word}
    (hh : h.toNat < 2 ^ 32) (hne : lsNodeW m h ≠ []) :
    ∃ ids : List LIdx, a.store.lss.view (decI h) = some ids := by
  have hg : h >>> 28 = 0 := Classical.byContradiction fun c => hne (by simp [lsNodeW, c])
  have hsc : ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := fun c => hne (by simp [lsNodeW, hg, c])
  have hc : ¬ tcnt m LVLS (tierW h) ≤ idxW h := fun c => hne (by
    rw [lsNodeW, ite_eq_right (by simpa using hg), ite_eq_right hsc, ite_eq_left c])
  obtain ⟨x, hx, hr⟩ := ConsR.node hR.ls (tierW h) (tierW_le h)
    (idxW h) (UInt64.not_le.mp hc)
  refine ⟨x.us, ?_⟩
  have hfl := ConsR.flag hR.ls
  have hpers : (decI h : LsIdx).isPersistent = (tierW h == 0) := by
    rw [isPersistent_decI h hh]; rfl
  have hget : ∀ T : LsTables, T.lists.nodes[(idxW h).toNat]? = some x →
      T.get (decI h) = some x.us := fun T hT => by
    simp only [LsTables.get, decLs_tag0 h hh, hg, beq_self_eq_true, ↓reduceIte, Tbl.node?,
      decLs_idx h, hT, Option.map_some]
  unfold LsStore.view
  rw [hpers]
  by_cases ht : tierW h = 0
  · simp only [ht, ↓reduceIte] at hx; simp only [ht, beq_self_eq_true, ↓reduceIte]; exact hget _ hx
  · simp only [ht, ↓reduceIte] at hx
    have hon : a.store.lss.scratchOn = true := by
      rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hsc ⟨ht, h1⟩
    simp only [ht, beq_iff_eq, ↓reduceIte, hon]; exact hget _ hx

theorem viewLs_run' (h : LsIdx) (a : AState) (ids : List LIdx) (hv : a.store.lss.view h = some ids) :
    (viewLs h).run a = .ok (ids, a) := by
  simp [viewLs, hv, StateT.run_bind, StateT.run_get]; rfl


theorem lsWords_length (ids : List LIdx) : (lsWords ids).length = ids.length := by simp [lsWords]

theorem word_lt32 {k : IdxKind} (x : Idx k) : x.word.toUInt64.toNat < 2 ^ 32 := by
  simp only [UInt32.toNat_toUInt64]; exact x.word.toNat_lt

theorem hslice_sliceL {P : Array Word} {o l : Nat} {ids : List LIdx}
    (hb : l = 0 ∨ o + l ≤ P.size) (h : sliceL P o l = lsWords ids) :
    hslice? P o l = some ids := by
  have hlen : ids.length = l := by
    have := sliceL_length P o l
    rw [h, lsWords_length] at this; exact this
  rcases hb with rfl | hb
  · have : ids = [] := List.length_eq_zero_iff.mp hlen
    subst this; simp [hslice?]
  · have hgood : ∀ j ∈ List.range l, hd? P (o + j) = some (decI (P[o + j]?.getD 0) : LIdx) := by
      intro j hj
      have hj' : j < l := List.mem_range.mp hj
      have hlt : o + j < P.size := by omega
      have e1 : P[o + j]? = some P[o + j] := Array.getElem?_eq_getElem hlt
      have e2 : (sliceL P o l)[j]'(by rw [sliceL_length]; exact hj') = P[o + j]?.getD 0 := by
        simp [sliceL]
      have hw : (P[o + j]?.getD 0).toNat < 2 ^ 32 := by
        rw [← e2]
        simp only [h]
        simp only [lsWords, List.getElem_map]
        exact word_lt32 _
      simp only [hd?, e1, Option.getD_some] at hw ⊢
      simp [hw]
    have := mapM_some_of (fun j => (hd? P (o + j) : Option LIdx)) (fun j => (decI (P[o + j]?.getD 0) : LIdx))
      (List.range l) hgood
    simp only [hslice?]
    have e3 : (List.range l).map (fun j => (decI (P[o + j]?.getD 0) : LIdx)) = ids := by
      rw [sliceL_map_decI, h]; simp [lsWords, Function.comp_def, decI_word]
    rw [this, e3]


/-- **`view_ls` refines `viewLs` under the stage relation**: the twin's view succeeds without
changing the state, the stage relation holds after, the pool only grew, and the new slice (below
the top) holds the list's handles. -/
def PoolSmall (m : Mem) : Prop := pcap m < 2 ^ 64

theorem viewLsW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {us : Word} {r : List Word} (h : viewLsW n m us = some (r, m'))
    (hS : StageR dn vis fe m a) (hu : us.toNat < 2 ^ 32) (hP : PoolSmall m) :
    ∃ ids : List LIdx, (viewLs (decI us)).run a = .ok (ids, a) ∧ StageR dn vis fe m' a ∧
      IWGrow m m' ∧ decRL (fun m => decHL m) 0 m' r ids ∧ PoolSmall m' := by
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  have hR := hS.1.arena.1
  unfold viewLsW at h
  have hne : ¬ lsNodeW m us = [] := fun hne => by rw [ite_eq_left hne] at h; simp at h
  rw [ite_eq_right hne] at h
  obtain ⟨ids, hv⟩ := lsView_of_lsNodeW hR hu hne
  obtain ⟨hlsn, hbnd, hsl⟩ := lsNodeW_store hR hu hv
  rw [hlsn] at h
  simp only [List.headD_cons, List.tail_cons] at h
  generalize tfld m LVLS (tierW us) (idxW us) 0 = o at *
  generalize tfld m LVLS (tierW us) (idxW us) 1 = l at *
  rcases hal : allocW m l with _ | ⟨q, m1⟩ <;> simp only [hal, reduceCtorEq] at h
  rcases hcp : poolCopyW (n - 1) m1 q o l with _ | m2 <;> simp only [hcp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hIW := allocMem_IW m l
  have hPPv : vpool (allocMem m l) = vpool m := by
    simp only [allocMem]; exact vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩
  have h41 := hR.lit.1.top41
  obtain ⟨hA, hS2, hW, hG⟩ := poolCopyW_get (n - 1) _ _ _ _ _ hcp (by omega)
    (by rw [hIW]; exact hroom) (by rw [hIW]; exact hsz)
  rw [hIW] at hS2 hG
  rw [hPPv] at hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m l).trans (copy_frame hA (by rw [hS2, hIW]) hW)
  have htop : rdW (m2.arr64 CTL) 200 = q + l := by
    rw [hA CTL (by decide), allocMem_top m _ hc, hqq]
  have hsum : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hgrow : IWGrow m m2 := by
    refine iwGrow_of_frame hfr (N := l) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hG, ite_eq_right (by omega)]
  have htop' : iwTop m2 = q.toNat + l.toNat := by simp only [iwTop, htop, hsum]
  have hdec : decHL m2 q.toNat l.toNat = some ids := by
    have e1 : (decHL m2 q.toNat l.toNat : Option (List LIdx)) = hslice? (vpool m) o.toNat l.toNat := by
      simp only [decHL]
      apply hslice?_congr
      intro j hj
      simp only [iwA, hG]
      rw [ite_eq_left (by omega)]
      congr 1; omega
    rw [e1]
    exact hslice_sliceL (.inr (by rw [vpool_size]; omega)) hsl
  have hroom2 : iwTop m2 ≤ (m2.arr64 IW).size := by rw [htop', hS2]; omega
  have hSt : StageR dn vis fe m2 a := by
    refine ⟨CheckR.frame_iw hfr hS.1, hroom2, ?_, ?_, ?_, ?_⟩
    · have h129 : rdW (m2.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hfr.2.1 129 (by simp)
      have hE2 : m2.arr64 EREC = m.arr64 EREC := hfr.1 EREC (by decide) (by decide)
      simp only [erTop, h129, hE2]; exact hE1
    · rw [hfr.2.2.1 IW]; exact hsz
    · rw [hfr.1 EREC (by decide) (by decide)]; exact hEs
    · rw [hfr.2.2.1 CTL]; exact hc
  refine ⟨ids, viewLs_run' _ _ _ hv, hSt, hgrow, ⟨?_, ?_⟩, ?_⟩
  · simpa using hdec
  · show q.toNat + l.toNat ≤ iwTop m2
    omega
  · simp only [PoolSmall]
    rw [pcap_congr (hfr.2.2.1 POOL) (hfr.2.2.1 POOL1)]; exact hP

end L.Ind
