module

public import ConAgua.Arena.IndT.BlockC
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Grind
import all ConAgua.Arena.IndParts
import ConAgua.L.ModelGen

@[expose] public section

/-!
# `block_shape_with_members`' contract (lane `ronsync2`, stage 3)

`block_shape_with_members(p, ms.off, ms.len)` (`IndParts.lean`): a fresh 9-word record, words `0, 1`
the members' slice, `2‥8` copied from `p`. Its model `wmW` (the nine writes `wmWrites`, as
`block_shape_with_sort`'s `wsWrites`), the record's decoding (`decBS_wm`), and the contract
`bswmRefS_of` (the twin has no step).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true

namespace L.Ind

open L.Arena

/-- The nine writes of `block_shape_with_members` to the fresh record `q`. -/
def wmWrites (m : Mem) (q p mo ml : Word) : Mem :=
  let m1 := m.set64 IW q mo
  let m2 := m1.set64 IW (q + 1) ml
  let m3 := cpyIW m2 (q + 2) (p + 2)
  let m4 := cpyIW m3 (q + 3) (p + 3)
  let m5 := cpyIW m4 (q + 4) (p + 4)
  let m6 := cpyIW m5 (q + 5) (p + 5)
  let m7 := cpyIW m6 (q + 6) (p + 6)
  let m8 := cpyIW m7 (q + 7) (p + 7)
  cpyIW m8 (q + 8) (p + 8)

/-- **`block_shape_with_members`' model `wmW`** (generated; its stores are `wmWrites`). -/
l_model blockShapeWithMembers_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "block_shape_with_members" = some blockShapeWithMembers)
  fns [hp ↦ wmW list]
  specs [iwAlloc_specW p ha n]
  grind [arena_grind] extra [ld64_rd_spec] simp []

/-- Word `j` of the new record. -/
def wmWd (m : Mem) (p s f : Word) (j : Nat) : Word :=
  if j = 0 then s else if j = 1 then f else rdW (m.arr64 IW) (p + UInt64.ofNat j)

section wmget
variable (m : Mem) (q p s f : Word) (hpq : p.toNat + 9 ≤ q.toNat)
  (hqs : q.toNat + 9 ≤ (m.arr64 IW).size) (hsz : (m.arr64 IW).size < 2 ^ 64)

/-- After `k` writes the first `k` cells of the record hold their words. -/
def WmP (k : Nat) (m' : Mem) : Prop :=
  (m'.arr64 IW).size = (m.arr64 IW).size ∧
  ∀ i, (m'.arr64 IW)[i]? =
    if q.toNat ≤ i ∧ i < q.toNat + k then some (wmWd m p s f (i - q.toNat)) else (m.arr64 IW)[i]?

include hpq hqs hsz in
theorem wmP_step (k : Nat) (hk : k < 9) (m' : Mem) (hP : WmP m q p s f k m') (d v : Word)
    (hd : d.toNat = q.toNat + k) (hv : v = wmWd m p s f k) :
    WmP m q p s f (k + 1) (m'.set64 IW d v) := by
  obtain ⟨hS, hG⟩ := hP
  refine ⟨by rw [Mem.arr64_set64_same]; simpa using hS, fun i => ?_⟩
  rw [set64IW_get, hG]
  by_cases hi : i = q.toNat + k
  · subst hi
    have : (q.toNat + k < (m'.arr64 IW).size) := by omega
    rw [ite_eq_left ⟨by omega, this⟩, ite_eq_left ⟨by omega, by omega⟩]
    have : q.toNat + k - q.toNat = k := by omega
    rw [this, hv]
  · by_cases hi2 : q.toNat ≤ i ∧ i < q.toNat + k
    · rw [ite_eq_right (by omega), ite_eq_left hi2, ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right hi2, ite_eq_right (by omega)]

include hpq hqs hsz in
theorem wmP_rd (k : Nat) (m' : Mem) (hP : WmP m q p s f k m') (j : Nat) (hj : j < 9) :
    rdW (m'.arr64 IW) (p + UInt64.ofNat j) = rdW (m.arr64 IW) (p + UInt64.ofNat j) := by
  obtain ⟨hS, hG⟩ := hP
  have hx : (p + UInt64.ofNat j).toNat = p.toNat + j := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [rdW, hx, hG, ite_eq_right (show ¬ (q.toNat ≤ p.toNat + j ∧ p.toNat + j < q.toNat + k) by omega)]

include hpq hqs hsz in
theorem wmWrites_get : WmP m q p s f 9 (wmWrites m q p s f) := by
  have h0 : WmP m q p s f 0 m := ⟨rfl, fun i => by rw [ite_eq_right (by omega)]⟩
  have qk : ∀ k : Nat, k < 9 → (q + UInt64.ofNat k).toNat = q.toNat + k := by
    intro k hk
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have cpy : ∀ (k : Nat) (hk : k < 9) (hk6 : k ≠ 0) (hk8 : k ≠ 1) (m' : Mem) (d e : Word)
      (hd : d = q + UInt64.ofNat k) (he : e = p + UInt64.ofNat k), WmP m q p s f k m' →
      WmP m q p s f (k + 1) (cpyIW m' d e) := by
    intro k hk hk6 hk8 m' d e hd he hP
    subst hd he
    exact wmP_step m q p s f hpq hqs hsz k hk m' hP (q + UInt64.ofNat k)
      (rdW (m'.arr64 IW) (p + UInt64.ofNat k)) (qk k hk)
      (by rw [wmP_rd m q p s f hpq hqs hsz k m' hP k hk]; simp [wmWd, hk6, hk8])
  have lit : ∀ (k : Nat) (hk : k < 9) (v : Word) (hv : v = wmWd m p s f k) (m' : Mem) (d : Word)
      (hd : d = q + UInt64.ofNat k), WmP m q p s f k m' → WmP m q p s f (k + 1) (m'.set64 IW d v) := by
    intro k hk v hv m' d hd hP
    subst hd
    exact wmP_step m q p s f hpq hqs hsz k hk m' hP _ v (qk k hk) hv
  have h1 := lit 0 (by omega) s (by simp [wmWd]) m q (by simp) h0
  have h2 := lit 1 (by omega) f (by simp [wmWd]) _ (q + 1) (by simp) h1
  have h3 := cpy 2 (by omega) (by omega) (by omega) _ (q + 2) (p + 2) (by simp) (by simp) h2
  have h4 := cpy 3 (by omega) (by omega) (by omega) _ (q + 3) (p + 3) (by simp) (by simp) h3
  have h5 := cpy 4 (by omega) (by omega) (by omega) _ (q + 4) (p + 4) (by simp) (by simp) h4
  have h6 := cpy 5 (by omega) (by omega) (by omega) _ (q + 5) (p + 5) (by simp) (by simp) h5
  have h7 := cpy 6 (by omega) (by omega) (by omega) _ (q + 6) (p + 6) (by simp) (by simp) h6
  have h8 := cpy 7 (by omega) (by omega) (by omega) _ (q + 7) (p + 7) (by simp) (by simp) h7
  have h9 := cpy 8 (by omega) (by omega) (by omega) _ (q + 8) (p + 8) (by simp) (by simp) h8
  exact h9

end wmget

/-- **A record with `p`'s words `2‥8` and the members' slice at words `0, 1` decodes as the shape
with those members.** -/
theorem decBS_wm {M : Mem} {q p : Nat} {mo ml : Word} {bs : BlockShape} {ms : List MemberShape}
    (hp : decBS M p = some bs) (hms : decPL M (decMS M) mo.toNat ml.toNat = some ms)
    (c0 : iwA M q = some mo) (c1 : iwA M (q + 1) = some ml)
    (c : ∀ j, 2 ≤ j → j < 9 → iwA M (q + j) = iwA M (p + j)) :
    decBS M q = some { bs with members := ms } := by
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := decBS_some hp
  simp only [iwA, aread_apply] at c0 c1 c
  have e1 : decAt M (decPL M (decMS M)) q = some ms := by
    simp only [decAt, iwN, nat?, iwA, aread_apply, c0, c1, Option.map_some, bind, Option.bind_some]
    exact hms
  have e2 := decAt_congr (m := M) (decPL M (decRS M)) (i := q + 2) (j := p + 2) (c 2 (by omega) (by omega))
    (by simpa [Nat.add_assoc] using c 3 (by omega) (by omega))
  rw [decBS]
  simp only [bind, pure]
  rw [e1]
  simp only [Option.bind_some]
  rw [e2, h2]
  simp only [Option.bind_some]
  rw [iwN_congr (c 4 (by omega) (by omega)), h3]
  simp only [Option.bind_some]
  have e5 : iwH M (q + 5) = (iwH M (p + 5) : Option NIdx) := by
    simp only [iwH, hd?, iwA, aread_apply, c 5 (by omega) (by omega)]
  rw [e5, h4]
  simp only [Option.bind_some]
  have e6 : iwH M (q + 6) = (iwH M (p + 6) : Option LIdx) := by
    simp only [iwH, hd?, iwA, aread_apply, c 6 (by omega) (by omega)]
  rw [e6, h5]
  simp only [Option.bind_some]
  have e7 : iwB M (q + 7) = iwB M (p + 7) := by
    simp only [iwB, bool?, iwA, aread_apply, c 7 (by omega) (by omega)]
  rw [e7, h6]
  simp only [Option.bind_some]
  have e8 : iwB M (q + 8) = iwB M (p + 8) := by
    simp only [iwB, bool?, iwA, aread_apply, c 8 (by omega) (by omega)]
  rw [e8, h7]
  rfl

theorem wmWrites_frame (m : Mem) (q p mo ml : Word) : MemFrame [IW] [] m (wmWrites m q p mo ml) := by
  have fr : ∀ (m : Mem) (d x : Word), MemFrame [IW] [] m (m.set64 IW d x) :=
    fun m d x => MemFrame.set64 m IW (by decide) d x
  unfold wmWrites cpyIW
  exact ((((((((fr _ _ _).trans (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)).trans
    (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)).trans (fr _ _ _)

/-- **`block_shape_with_members`' model**: a fresh record of `{ bs with members := ms }` above
the old top, the stage kept. -/
theorem wmW_ok {vis : Word} {fe : IFEnv} {a : AState} {m m' : Mem} {p mo ml : Word}
    {r : List Word} {bs : BlockShape} {ms : List MemberShape} (h : wmW m p mo ml = some (r, m'))
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m p.toNat) m bs) (hsl : ShapeSl m p)
    (hmsB : DecB (fun m => decPL m (decMSB m) mo.toNat ml.toNat) m ms) (hb : mo.toNat + ml.toNat ≤ iwTop m) :
    ∃ q, r = [q] ∧ StageR vis fe m' a ∧ IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧
      DecB (fun m => decBS m q.toNat) m' { bs with members := ms } ∧ ShapeSl m' q := by
  have hms : DecB (fun m => decPL m (decMS m) mo.toNat ml.toNat) m ms := decPL_decMSB hmsB
  rw [wmW.arm1] at h
  rcases hal : allocW m 9 with _ | ⟨q, m3⟩
  · rw [hal, wmW.k_iw_alloc.none] at h; cases h
  rw [hal, wmW.k_iw_alloc.arm1] at h
  change some ([q], wmWrites m3 q p mo ml) = some (r, m') at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hIsz2 := hS.iw.iwSize
  have hCsz2 := hS.iw.ctl
  obtain ⟨hqe, hm3, hroom⟩ := allocW_facts hal hIsz2
  subst hm3
  have hIW3 : (allocMem m 9).arr64 IW = m.arr64 IW := allocMem_IW m 9
  have hqtop : q.toNat = iwTop m := by rw [hqe]; rfl
  have hqd : decBS (truncM m) p.toNat = some bs := hq
  have hp4 : p.toNat + 8 < iwTop m := by
    obtain ⟨-, -, -, -, -, -, h8⟩ := decBS_some hqd
    simp only [iwB, bool?, Option.map_eq_some_iff] at h8
    obtain ⟨w, hw, -⟩ := h8
    exact (truncM_iw_get hw).1
  have hpq : p.toNat + 9 ≤ q.toNat := by omega
  have hqs : q.toNat + 9 ≤ ((allocMem m 9).arr64 IW).size := by
    rw [hIW3]; simpa using hroom
  have hsz3 : ((allocMem m 9).arr64 IW).size < 2 ^ 64 := by rw [hIW3]; exact hIsz2
  have hWs := wmWrites_get (allocMem m 9) q p mo ml hpq hqs hsz3
  have hfr : MemFrame [IW] [] (allocMem m 9) (wmWrites (allocMem m 9) q p mo ml) :=
    wmWrites_frame _ _ _ _ _
  generalize hm' : wmWrites (allocMem m 9) q p mo ml = m' at hWs hfr
  have hfr2 : MemFrame [IW] [200] m m' := ((allocMem_frame m 9).trans (hfr.mono (by simp) (by simp)))
  have htop : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 + 9 := by
    rw [hfr.ctl 200 (by simp), allocMem_top m 9 hCsz2]
  have hlow : ∀ i < iwTop m, (m'.arr64 IW)[i]? = (m.arr64 IW)[i]? := by
    intro i hi
    rw [hWs.2 i, ite_eq_right (by omega), hIW3]
  have hg : IWGrow m m' := iwGrow_of_frame hfr2 (N := 9) htop (by have := hroom; simp at this; omega) hIsz2 hlow
  have htopq : q.toNat + 9 ≤ iwTop m' := by
    simp only [iwTop, htop]; rw [UInt64.toNat_add]; simp
    have := hroom; simp at this; simp only [iwTop] at hqtop; omega
  have htop' : iwTop m' ≤ (m.arr64 IW).size := by
    have e : iwTop m' = iwTop m + 9 := by
      simp only [iwTop, htop]; rw [UInt64.toNat_add]; simp
      have := hroom; simp at this; simp only [iwTop] at hqtop; omega
    rw [e]; have := hroom; simp at this; omega
  -- the record's cells, in the cut pool
  have cell : ∀ j, j < 9 → (m'.arr64 IW)[q.toNat + j]? = some (wmWd (allocMem m 9) p mo ml j) := by
    intro j hj
    rw [hWs.2, ite_eq_left (by omega)]
    have e : q.toNat + j - q.toNat = j := by omega
    rw [e]
  have cpT : ∀ j, j < 9 → iwA (truncM m') (p.toNat + j) = iwA m (p.toNat + j) := by
    intro j hj
    rw [truncM_iw_eq (by have := hg.iw; omega)]
    simp only [iwA, aread_apply]; exact hlow _ (by omega)
  have cqT : ∀ j, j < 9 → iwA (truncM m') (q.toNat + j) = some (wmWd (allocMem m 9) p mo ml j) := by
    intro j hj
    rw [truncM_iw_eq (by omega)]
    simp only [iwA, aread_apply]; exact cell j hj
  have cpm : ∀ j, j < 9 → 2 ≤ j → wmWd (allocMem m 9) p mo ml j = rdW (m.arr64 IW) (p + UInt64.ofNat j) := by
    intro j hj h2
    simp only [wmWd, show j ≠ 0 by omega, show j ≠ 1 by omega, ite_false, hIW3]
  have hpj : ∀ j, j < 9 → (p + UInt64.ofNat j).toNat = p.toNat + j := fun j hj => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by rw [UInt64_size_eq]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have cc : ∀ j, 2 ≤ j → j < 9 → iwA (truncM m') (q.toNat + j) = iwA (truncM m') (p.toNat + j) := by
    intro j h2 hj
    rw [cqT j hj, cpT j hj, cpm j hj h2]
    simp only [iwA, aread_apply, rdW]
    rw [hpj j hj, Array.getElem?_eq_getElem (by have := hg.iw; omega)]
    rfl
  have c0 : iwA (truncM m') q.toNat = some mo := by
    have := cqT 0 (by omega); simpa [wmWd] using this
  have c1 : iwA (truncM m') (q.toNat + 1) = some ml := by
    have := cqT 1 (by omega); simpa [wmWd] using this
  have hdec : DecB (fun m => decBS m q.toNat) m' { bs with members := ms } :=
    decBS_wm (hq.grow (decBS_mono _) hg) (hms.grow (OMono.decPL decMS_mono _ _) hg) c0 c1 cc
  refine ⟨q, rfl, stage_frame_iw hS hfr2 htop', hg, hfr2, hdec, ?_, ?_, ms, ?_⟩
  · intro o l ho hl
    have e0 : iwN m' q.toNat = some mo.toNat := by simp [iwN, nat?, (truncM_iw_get c0).2]
    have e1 : iwN m' (q.toNat + 1) = some ml.toNat := by simp [iwN, nat?, (truncM_iw_get c1).2]
    rw [e0] at ho; rw [e1] at hl
    cases ho; cases hl
    exact Nat.le_trans hb hg.iw
  · have cm : ∀ j, 2 ≤ j → j < 9 → iwN m' (q.toNat + j) = iwN m' (p.toNat + j) := by
      intro j h2 hj
      have := cc j h2 hj
      rw [truncM_iw_eq (by omega), truncM_iw_eq (by have := hg.iw; omega)] at this
      simp only [iwN, nat?, this]
    intro o l ho hl
    rw [cm 2 (by omega) (by omega)] at ho
    rw [show q.toNat + 2 + 1 = q.toNat + 3 by omega, cm 3 (by omega) (by omega)] at hl
    exact (hsl.grow' hq hg).2.1 o l ho (by simpa [Nat.add_assoc] using hl)
  · show decAt (truncM m') _ q.toNat = some ms
    simp only [decAt, iwN, nat?, c0, c1, Option.map_some, Option.bind_some, bind]
    exact (hmsB.grow (OMono.decPL decMSB_mono _ _) hg)


/-- The lookups `block_shape_with_members` takes. -/
structure BswmLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hp : p.lookup "block_shape_with_members" = some blockShapeWithMembers

/-- **`block_shape_with_members`' contract.** -/
theorem bswmRefS_of {G : Prop} {p : Prog} {dn : NIdx → Option ConLeche.Name} (hL : BswmLook p)
    (hGnv : G → closedNV p _root_.L.Checker.nvFns = true) : BswmRefS G p dn := by
  intro n vis fe env m a p0 mo ml bs ms hB hq hsl hms hb
  rcases c : callE p n "block_shape_with_members" [p0, mo, ml] m with e | ⟨r, m'⟩
  · exact fun hG => ErrClaim.of_callE_nv (hGnv hG) (_root_.L.Checker.nv_mem (by decide +kernel)) c
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeWithMembers_spec p hL.ha hL.hp n _ p0 mo ml) (callW_of_callE c)
  obtain ⟨q, rfl, hS', hg, hfr, hdec, hsl'⟩ := wmW_ok hW hB.c.stage hq hsl hms hb
  have hA' : AbsOK s'.mem := AFr.of_frame hfr (by decide) (by decide) hB.abs
  have hI' : IndMemos s'.mem := hB.ind.frame hfr (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; exact ⟨by decide, by decide, by decide⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; decide)
  exact ⟨(), a, rfl,
    ⟨⟨StageC.of_check hB.c hS' hA' hB.c.check (ConRon.Arena.Ext.refl _), hI', hA'⟩, hg,
      ⟨hB.c.check.state, ConRon.Arena.Ext.refl _, rfl⟩⟩, hdec, hsl'⟩

end L.Ind

end
