import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.IndPartsSpec.EqW
import ConAgua.Arena.IndPartsSpec.RecTW

/-!
# BlockRecLpsOk: `ConRon.Arena.blockRecLpsOk`

The refinement theorems `blockRecLpsOk_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
  (hq : p.lookup "sl_eq" = some slEq)
  (ho : p.lookup "block_rec_lps_one" = some blockRecLpsOne)
  (hp : p.lookup "block_rec_lps_ok_go" = some blockRecLpsOkGo)

include ha hc he hq ho in
theorem blockRecLpsOne_spec (n : Nat) (s₀ : St) (rc wo wl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_lps_one" [rc, wo, wl]
    ⦃fun r s' => LocEq s' s₀ ∧ lpsOneW n s₀.mem rc wo wl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ ho]
  simp only [callFn, blockRecLpsOne]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        erToIw_specW2 p ha hc he n, slEq_spec p hq n] <;>
      finish (gen := 20) [rdW_eq, List.getD_cons_zero, List.getD_cons_succ,
        List.tail_cons]

include ha hc he hq ho hp in
theorem blockRecLpsOkGo_spec (n : Nat) : ∀ (s₀ : St) (ro rl wo wl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_lps_ok_go" [ro, rl, wo, wl]
    ⦃fun r s' => LocEq s' s₀ ∧ lpsGoW n s₀.mem ro rl wo wl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ro rl wo wl; rw [invoke_eq _ hp]; simp only [callFn, blockRecLpsOkGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ro rl wo wl
    rw [invoke_eq _ hp]
    simp only [callFn, blockRecLpsOkGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        blockRecLpsOne_spec p ha hc he hq ho n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

section spec2
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
  (hq : p.lookup "sl_eq" = some slEq) (hcp : p.lookup "iw_copy" = some iwCopy)
  (hsc : p.lookup "sl_cons" = some slCons)
  (ho : p.lookup "block_rec_lps_one" = some blockRecLpsOne)
  (hg : p.lookup "block_rec_lps_ok_go" = some blockRecLpsOkGo)
  (hl : p.lookup "block_shape_lps" = some blockShapeLps)
  (hp : p.lookup "block_rec_lps_ok" = some blockRecLpsOk)

include ha hc he hq hcp hsc ho hg hl hp in
theorem blockRecLpsOk_spec (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_lps_ok" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ lokW n s₀.mem q = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockRecLpsOk]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        blockShapeLps_spec2 p ha hc he hl n, slConsSpec2 p ha hcp hsc n,
        blockRecLpsOkGo_spec p ha hc he hq ho hg n] <;>
      finish (gen := 20) [rdW_eq, List.getD_cons_zero, List.getD_cons_succ,
        List.tail_cons]

end spec2

/-- **`er_to_iw` of a constant's level parameters**: for the constant at `EREC` pointer `a0`, the
copy of `(EREC[a0 + 1], EREC[a0 + 2])` decodes as its `levelParams`. -/
theorem erLpsW_dec {n : Nat} {m m' : Mem} {a0 : Nat} {cv : IConstantVal} {r : List Word}
    (h : erToIwW n m (rdW (m.arr64 EREC) (UInt64.ofNat a0 + 1))
      (rdW (m.arr64 EREC) (UInt64.ofNat a0 + 2)) = some (r, m'))
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size)
    (hE : (m.arr64 EREC).size < 2 ^ 64) (hcv : decCVp m a0 = some cv) :
    r = [r.headD 0, r.getD 1 0] ∧
    decHL m' (r.headD 0).toNat (r.getD 1 0).toNat = some cv.levelParams ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
    (r.headD 0).toNat + (r.getD 1 0).toNat = iwTop m' ∧ IWRoom m m' := by
  have hcv' := hcv
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv'
  obtain ⟨nm, -, lv, hlv, ce, -, hcvT⟩ := hcv'
  have hlvE : lv = cv.levelParams := by rw [← hcvT]
  simp only [hlist?, bind, Option.bind_eq_some_iff] at hlv
  obtain ⟨o', ho2, l', hl2, hsl⟩ := hlv
  simp only [nat?, erA, Option.map_eq_some_iff] at ho2 hl2
  obtain ⟨w1, hw1, rfl⟩ := ho2
  obtain ⟨w2, hw2, rfl⟩ := hl2
  have hi1 := (Array.getElem?_eq_some_iff.mp hw1).1
  have hi2 := (Array.getElem?_eq_some_iff.mp hw2).1
  replace hi1 : a0 + 1 < (m.arr64 EREC).size := hi1
  replace hi2 : a0 + 2 < (m.arr64 EREC).size := hi2
  have hrd1 : rdW (m.arr64 EREC) (UInt64.ofNat a0 + 1) = w1 := by
    have e3 : UInt64.ofNat a0 + 1 = UInt64.ofNat (a0 + 1) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    have : (UInt64.ofNat (a0 + 1)).toNat = a0 + 1 :=
      UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
    rw [e3]; simp only [rdW, this]; rw [hw1]; rfl
  have hrd2 : rdW (m.arr64 EREC) (UInt64.ofNat a0 + 2) = w2 := by
    have e4 : UInt64.ofNat a0 + 2 = UInt64.ofNat (a0 + 2) := by
      apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
    have : (UInt64.ofNat (a0 + 2)).toNat = a0 + 2 :=
      UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)
    rw [e4]; simp only [rdW, this]; rw [hw2]; rfl
  rw [hrd1, hrd2] at h
  obtain ⟨hr, hdec, hgrow, hfr, -, htp, hroom⟩ := erToIwW_decS (k := IdxKind.name) h hsz hc hE hsl
  have hh := erToIwW_two h
  refine ⟨by rw [getD1]; exact hh, ?_, hgrow, hfr, ?_, hroom⟩
  · rw [hr] at hh ⊢
    simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
    rw [hdec, ← hlvE]
    exact hsl
  · rw [hr]; simpa using htp

theorem lpsOneW_ok (n : Nat) (m m' : Mem) (rc wo wl : Word) (r : List Word) (rec : RecShape)
    (ns : List NIdx)
    (h : lpsOneW n m rc wo wl = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64)
    (hrc : decRS m rc.toNat = some rec) (hwant : decHL m wo.toNat wl.toNat = some ns)
    (hwb : wo.toNat + wl.toNat ≤ iwTop m) :
    r = [if rec.cvR.levelParams == ns then 1 else 0] ∧ IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
      IWRoom m m' := by
  cases n with
  | zero => simp [lpsOneW] at h
  | succ n =>
  rw [lpsOneW_step] at h
  obtain ⟨⟨a0, ha0, hcvR⟩, -, -, -, -⟩ := decRS_some hrc
  obtain ⟨hrw, hab⟩ := iwN_rdW ha0 (by have := rc.toNat_lt; omega)
  rw [ofNat_toNat_word] at hrw
  rw [hrw] at h
  obtain ⟨rp, m1, hh, h⟩ := ipK_inv h (by simp [lpsOneW.loK1])
  rw [loK1_some] at h
  obtain ⟨hsh, hdec, hg, hf, htp, hroom⟩ := erLpsW_dec hh hsz hc hE hcvR
  obtain ⟨e, he, h⟩ := ipK_inv1 h (by simp [lpsOneW.loK2])
  rw [loK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hf.2.2.1 IW]; exact hsz
  have hbound1 : (rp.headD 0).toNat + (rp.getD 1 0).toNat < 2 ^ 64 := by
    rw [htp]; simp only [iwTop]; exact UInt64.toNat_lt _
  obtain ⟨ws1, hs1, hn1, hl1⟩ := slR_of_decHL m1 _ _ _ hdec hbound1
  rw [ofNat_toNat_word, ofNat_toNat_word] at hs1
  have hwant1 : decHL m1 wo.toNat wl.toNat = some ns := by
    rw [decHL_grow3 hg hwb]; exact hwant
  obtain ⟨ws2, hs2, hn2, hl2⟩ := slR_of_decHL m1 _ _ _ hwant1 (by
    have : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
    omega)
  rw [ofNat_toNat_word, ofNat_toNat_word] at hs2
  have hres := eqW_ok n m1 _ _ _ _ e ws1 ws2 hs1 hs2 he
  refine ⟨?_, hg, hf, hroom⟩
  rw [hn1, hn2, map_decI_beq ws1 ws2 hl1 hl2, hres]
  by_cases hw : ws1 = ws2 <;> simp [hw]

theorem lpsGoW_ok (n : Nat) : ∀ (m0 m m' : Mem) (ro rl wo wl : Word) (r : List Word)
    (recs : List RecShape) (ns : List NIdx),
    lpsGoW n m ro rl wo wl = some (r, m') → IWGrow m0 m → m.arr64 EREC = m0.arr64 EREC →
    (m.arr64 IW).size < 2 ^ 64 → 200 < (m.arr64 CTL).size → (m0.arr64 EREC).size < 2 ^ 64 →
    (∀ m'', IWGrow m0 m'' → decPL m'' (decRS m'') ro.toNat rl.toNat = some recs) →
    (∀ m'', IWGrow m0 m'' → decHL m'' wo.toNat wl.toNat = some ns) →
    wo.toNat + wl.toNat ≤ iwTop m0 → ro.toNat + rl.toNat < 2 ^ 64 →
    r = [if recs.all (fun rc => rc.cvR.levelParams == ns) then 1 else 0] ∧ IWGrow m m' ∧
      MemFrame [IW] [200] m m' ∧ IWRoom m m' := by
  induction n with
  | zero => intro m0 m m' ro rl wo wl r recs ns h; simp [lpsGoW] at h
  | succ n ih =>
    intro m0 m m' ro rl wo wl r recs ns h hg0 hE hsz hc hE64 hdr hdn hwb hb
    by_cases hl : rl = 0
    · rw [lpsGoW_nil n m ro rl wo wl hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hrecs : recs = [] := by
        have := hdr m hg0
        rw [hl] at this
        simp only [UInt64.toNat_zero, decPL, List.range_zero, List.mapM_nil, pure,
          Option.some.injEq] at this
        exact this.symm
      subst hrecs
      exact ⟨rfl, IWGrow.refl _, MemFrame.refl _ _ _, IWRoom.refl _⟩
    · obtain ⟨k, hk⟩ : ∃ k, rl.toNat = k + 1 := by
        have : rl.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
        exact ⟨rl.toNat - 1, by omega⟩
      have hd := hdr m hg0
      rw [hk] at hd
      have hlen := decPL_length m hd
      cases hrecs : recs with
      | nil => rw [hrecs] at hlen; simp at hlen
      | cons rc rest =>
      rw [hrecs] at hd hdr
      obtain ⟨v, hv, hrcd⟩ := decPL_head hd
      obtain ⟨hv', hvb⟩ := iwN_rdW hv (by omega)
      rw [ofNat_toNat_word] at hv'
      rw [lpsGoW_cons n m ro rl wo wl hl, hv'] at h
      obtain ⟨r1, m1, h1, h⟩ := ipK_inv h (by simp [lgK1])
      have hvv : (UInt64.ofNat v).toNat = v := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hvb)
      have hwb' : wo.toNat + wl.toNat ≤ iwTop m := by have := hg0.1; omega
      obtain ⟨hr1, hg1, hf1, hw1⟩ := lpsOneW_ok n m m1 (UInt64.ofNat v) wo wl r1 rc ns h1 hsz hc
        (by rw [hE]; exact hE64) (by rw [hvv]; exact hrcd) (hdn m hg0) hwb'
      have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hf1.2.2.1 IW]; exact hsz
      have hc1 : 200 < (m1.arr64 CTL).size := by rw [hf1.2.2.1 CTL]; exact hc
      have hE1 : m1.arr64 EREC = m0.arr64 EREC := by
        rw [hf1.1 EREC (by simp [EREC, IW]) (by decide)]; exact hE
      by_cases hbeq : (rc.cvR.levelParams == ns) = true
      · have hone : r1.headD 0 ≠ 0 := by rw [hr1]; simp [hbeq]
        rw [lgK1_ne n m1 ro rl wo wl r1 hone] at h
        have hro1 : (ro + 1).toNat = ro.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have hrl1 : (rl - 1).toNat = k := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp [hk]
        obtain ⟨r2, m2, hrec, h⟩ := ipK_inv h (by simp [lgK3])
        rw [lgK3_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨hr2, hg2, hf2, hw2⟩ := ih m0 m1 m2 (ro + 1) (rl - 1) wo wl r2 rest ns hrec
          (hg0.trans hg1) hE1 hsz1 hc1 hE64
          (fun m'' hg'' => by
            rw [hro1, hrl1]
            exact decPL_tail (by rw [← hk]; exact hdr m'' hg'')) hdn hwb (by rw [hro1, hrl1]; omega)
        refine ⟨?_, hg1.trans hg2, hf1.trans hf2, hw1.trans hw2⟩
        rw [hr2]
        simp [List.all_cons, hbeq]
      · have hz : r1.headD 0 = 0 := by rw [hr1]; simp [hbeq]
        rw [lgK1_zero n m1 ro rl wo wl r1 hz] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨?_, hg1, hf1, hw1⟩
        simp [List.all_cons, hbeq]

theorem iwB_rdW {m : Mem} {i : Nat} {b : Bool} (h : iwB m i = some b) (hi : i < 2 ^ 64) :
    (rdW (m.arr64 IW) (UInt64.ofNat i) != 0) = b := by
  simp only [iwB, bool?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hi)
  simp only [rdW, this, hw, Option.getD_some]

theorem iwN_lt_p {m : Mem} {i v : Nat} (h : iwN m i = some v) : i < (m.arr64 IW).size := by
  simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hw).1

theorem iwN_cell {m m' : Mem} {i v : Nat} (hg : IWGrow m m') (hi : i < iwTop m)
    (h : iwN m i = some v) : iwN m' i = some v := by
  simp only [iwN, nat?, iwA] at h ⊢
  rw [hg.2.2.1 i hi]; exact h

/-- The record loop on top of a wanted list. -/
theorem lokKey (n : Nat) (m m2 m' : Mem) (p wo wl : Word) (r : List Word) (bs : BlockShape)
    (ns : List NIdx) (hq : decBS m p.toNat = some bs)
    (hstab : ∀ m'', IWGrow m m'' → decBS m'' p.toNat = some bs)
    (hb : p.toNat + 9 ≤ iwTop m) (hsz : (m.arr64 IW).size < 2 ^ 64) (hg : IWGrow m m2) (hE2 : m2.arr64 EREC = m.arr64 EREC)
    (hsz2 : (m2.arr64 IW).size < 2 ^ 64) (hc2 : 200 < (m2.arr64 CTL).size)
    (hE64 : (m.arr64 EREC).size < 2 ^ 64)
    (hwant : decHL m2 wo.toNat wl.toNat = some ns) (hwb : wo.toNat + wl.toNat ≤ iwTop m2)
    (hgo : lpsGoW n m2 (rdW (m2.arr64 IW) (p + 2)) (rdW (m2.arr64 IW) (p + 3)) wo wl = some (r, m')) :
    r = [if bs.recs.all (fun rc => rc.cvR.levelParams == ns) then 1 else 0] ∧ IWGrow m2 m' ∧
      MemFrame [IW] [200] m2 m' ∧ IWRoom m2 m' := by
  obtain ⟨o, l, ho, hl, hrecs⟩ := decAt_some (decBS_some hq).2.1
  have hp64 : p.toNat + 9 < 2 ^ 64 := by
    have h64 : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
    omega
  have e2 : UInt64.ofNat (p.toNat + 2) = p + 2 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have e3 : UInt64.ofNat (p.toNat + 2 + 1) = p + 3 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have ho2 := iwN_cell hg (by omega) ho
  have hl2 := iwN_cell hg (by omega) hl
  obtain ⟨hro, hob⟩ := iwN_rdW ho2 (by omega)
  obtain ⟨hrl, hlb⟩ := iwN_rdW hl2 (by omega)
  rw [e2] at hro
  rw [e3] at hrl
  rw [hro, hrl] at hgo
  have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hob)
  have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; exact hlb)
  have hrecs_len : o + l < 2 ^ 64 := by
    by_cases hl0 : l = 0
    · subst hl0; omega
    · obtain ⟨v, y, hv, -, -⟩ := decPL_get l o bs.recs hrecs (l - 1) (by omega)
      have hlt := iwN_lt_p hv
      omega
  refine lpsGoW_ok n m2 m2 m' _ _ wo wl r bs.recs ns hgo (IWGrow.refl _) rfl hsz2 hc2
    (by rw [hE2]; exact hE64) ?_ ?_ hwb (by rw [hoo, hll]; exact hrecs_len)
  · intro m'' hg''
    rw [hoo, hll]
    have hgg := hg.trans hg''
    have hd := hstab m'' hgg
    obtain ⟨o', l', ho', hl', hrecs'⟩ := decAt_some (decBS_some hd).2.1
    have h1 := iwN_cell hgg (by omega) ho
    have h2 := iwN_cell hgg (by omega) hl
    have eo : o' = o := Option.some.inj (ho'.symm.trans h1)
    have el : l' = l := Option.some.inj (hl'.symm.trans h2)
    rw [← eo, ← el]; exact hrecs'
  · intro m'' hg''
    rw [decHL_grow3 hg'' hwb]; exact hwant

theorem lokW_ok (n : Nat) (m m' : Mem) (p : Word) (r : List Word) (bs : BlockShape)
    (h : lokW n m p = some (r, m')) (hq : decBS m p.toNat = some bs)
    (hstab : ∀ m'', IWGrow m m'' → decBS m'' p.toNat = some bs)
    (hb : p.toNat + 9 ≤ iwTop m) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hE : (m.arr64 EREC).size < 2 ^ 64) :
    r = [if ConRon.Arena.blockRecLpsOk bs then 1 else 0] ∧ IWGrow m m' ∧
      MemFrame [IW] [200] m m' ∧ IWRoom m m' := by
  cases n with
  | zero => simp [lokW] at h
  | succ n =>
  rw [lokW_step] at h
  have hp64 : p.toNat + 9 < 2 ^ 64 := by
    have h64 : iwTop m < 2 ^ 64 := UInt64.toNat_lt _
    omega
  obtain ⟨lr, m1, h1, h⟩ := ipK_inv h (by simp [lokK1])
  obtain ⟨hlr, hdec1, hg1, hf1, hlt1, hw1⟩ := lpsW_dec h1 hsz hc hE hq hp64
  have hq1 := hstab m1 hg1
  have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := by rw [hf1.2.2.1 IW]; exact hsz
  have hc1 : 200 < (m1.arr64 CTL).size := by rw [hf1.2.2.1 CTL]; exact hc
  have hE1 : m1.arr64 EREC = m.arr64 EREC := hf1.1 EREC (by simp [EREC, IW]) (by decide)
  obtain ⟨-, -, -, h4, -, h6, -⟩ := decBS_some hq1
  have e7 : UInt64.ofNat (p.toNat + 7) = p + 7 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have e5 : UInt64.ofNat (p.toNat + 5) = p + 5 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp
  have hlarge := iwB_rdW h6 (by omega)
  rw [e7] at hlarge
  have hlr0 : lr.getD 1 0 = lr.tail.headD 0 := getD1 lr
  by_cases hL : rdW (m1.arr64 IW) (p + 7) ≠ 0
  · -- large
    rw [lokK1_large n m1 p lr hL] at h
    obtain ⟨cr, m2, h2, h⟩ := ipK_inv h (by simp [lokK2])
    rw [lokK2_some] at h
    obtain ⟨w5, hw5, hw532, hw5I⟩ := iwH_rdW h4 (by omega)
    rw [e5] at hw5
    have hsrc : (lr.headD 0).toNat + (lr.getD 1 0).toNat ≤ iwTop m1 := by rw [hlr0]; exact hlt1
    obtain ⟨hcr, hdec2, hg2, hf2, hl1, htop2⟩ := consW_dec h2 hsz1 hc1 hsrc (by rw [hw5]; exact hw532)
      (by rw [hlr0]; exact hdec1)
    have hw2 : IWRoom m1 m2 := fun _ => consW_room h2 hsz1 hc1 hsrc (by rw [hw5]; exact hw532)
      (by rw [hlr0]; exact hdec1)
    have hlargeT : bs.large = true := by rw [← hlarge]; simpa using hL
    have hgm : IWGrow m (m2) := hg1.trans hg2
    have hE2 : m2.arr64 EREC = m.arr64 EREC := by
      rw [hf2.1 EREC (by simp [EREC, IW]) (by decide)]; exact hE1
    have hsz2 : (m2.arr64 IW).size < 2 ^ 64 := by rw [hf2.2.2.1 IW]; exact hsz1
    have hc2 : 200 < (m2.arr64 CTL).size := by rw [hf2.2.2.1 CTL]; exact hc1
    obtain ⟨r3, m3, h3, h⟩ := ipK_inv h (by simp [lokK3])
    rw [lokK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hwant : decHL m2 (cr.headD 0).toNat (cr.getD 1 0).toNat = some (bs.elim :: bs.lps) := by
      rw [hcr]
      simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
      rw [hl1, hw5, hw5I] at hdec2
      rw [hl1]
      exact hdec2
    obtain ⟨hr3, hg3, hf3, hw3⟩ := lokKey n m m2 m3 p (cr.headD 0) (cr.getD 1 0) r3 bs (bs.elim :: bs.lps)
      hq hstab hb hsz hgm hE2 hsz2 hc2 hE hwant (by
        rw [hcr]; simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
        have := htop2; rw [hl1] at this; omega) h3
    refine ⟨?_, hgm.trans hg3, ?_, ?_⟩
    · rw [hr3]
      simp only [ConRon.Arena.blockRecLpsOk, hlargeT, ite_true]
      rfl
    · exact ((hf1.trans hf2).trans hf3)
    · exact (hw1.trans hw2).trans hw3
  · have hz : rdW (m1.arr64 IW) (p + 7) = 0 := by simpa using hL
    rw [lokK1_small n m1 p lr hz] at h
    have hlargeF : bs.large = false := by rw [← hlarge, hz]; rfl
    obtain ⟨r3, m3, h3, h⟩ := ipK_inv h (by simp [lokK3])
    rw [lokK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hwant : decHL m1 (lr.headD 0).toNat (lr.getD 1 0).toNat = some bs.lps := by
      rw [hlr0]; exact hdec1
    obtain ⟨hr3, hg3, hf3, hw3⟩ := lokKey n m m1 m3 p (lr.headD 0) (lr.getD 1 0) r3 bs bs.lps
      hq hstab hb hsz hg1 hE1 hsz1 hc1 hE hwant (by rw [hlr0]; exact hlt1) h3
    refine ⟨?_, hg1.trans hg3, hf1.trans hf3, hw1.trans hw3⟩
    rw [hr3]
    simp only [ConRon.Arena.blockRecLpsOk, hlargeF]
    simp

/-- **`block_rec_lps_ok` refines `blockRecLpsOk`** (pure: the pool grows by the level-parameter
copies; the shape keeps decoding as it grows, `hstab`). -/
@[refines ConRon.Arena.blockRecLpsOk]
theorem blockRecLpsOk_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hq : p.lookup "sl_eq" = some slEq) (hcp : p.lookup "iw_copy" = some iwCopy)
    (hsc : p.lookup "sl_cons" = some slCons)
    (ho : p.lookup "block_rec_lps_one" = some blockRecLpsOne)
    (hg : p.lookup "block_rec_lps_ok_go" = some blockRecLpsOkGo)
    (hl : p.lookup "block_shape_lps" = some blockShapeLps)
    (hp : p.lookup "block_rec_lps_ok" = some blockRecLpsOk)
    (n : Nat) (s₀ : St) (q : Word) (bs : BlockShape) (hdec : decBS s₀.mem q.toNat = some bs)
    (hstab : ∀ m'', IWGrow s₀.mem m'' → decBS m'' q.toNat = some bs)
    (hb : q.toNat + 9 ≤ iwTop s₀.mem) (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64)
    (hcl : 200 < (s₀.mem.arr64 CTL).size) (hE : (s₀.mem.arr64 EREC).size < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_rec_lps_ok" [q]
    ⦃fun r s' => LocEq s' s₀ ∧
      r = [if ConRon.Arena.blockRecLpsOk bs then 1 else 0] ∧ IWGrow s₀.mem s'.mem ∧
      MemFrame [IW] [200] s₀.mem s'.mem ∧ IWRoom s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (blockRecLpsOk_spec p ha hc he hq hcp hsc ho hg hl hp n s₀ q) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨hr, hgr, hf, hw⟩ := lokW_ok n s₀.mem s'.mem q r bs hm hdec hstab hb hsz hcl hE
  exact ⟨hlc, hr, hgr, hf, hw⟩

end L.Ind

end
