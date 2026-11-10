module

import ConAgua.Arena.IndPosSpec.EntryW
import ConAgua.Arena.IndPosSpec.EnvFindWHit
import ConAgua.Arena.RecStab
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConAgua.Arena.RecSim
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.IndPartsSpec.MemberNames
import all ConAgua.Arena.RecClass
public import ConAgua.Arena.IndStubs
public import ConAgua.Arena.RecClass
public import ConAgua.Arena.Env

@[expose] public section

/-!
# ClassNPcOf: `ConRon.Arena.classNPcOf`

The refinement theorems `classNPcOf_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## A block shape the stage reads -/

/-- **A block shape decoded below the tops**, its member slice below the top, every member record
below the top (what `block_shape_member_names` reads). -/
def BSOK (m : Mem) (p : Nat) (bs : BlockShape) : Prop :=
  DecB (fun m => decBS m p) m bs ∧
  (∀ o l, iwN m p = some o → iwN m (p + 1) = some l → o + l ≤ iwTop m) ∧
  (∀ o l j v, iwN m p = some o → iwN m (p + 1) = some l → j < l → iwN m (o + j) = some v →
    v < iwTop m)

theorem BSOK.dec {m : Mem} {p : Nat} {bs : BlockShape} (h : BSOK m p bs) : decBS m p = some bs :=
  h.1.get (decBS_mono p)

theorem BSOK.ptop {m : Mem} {p : Nat} {bs : BlockShape} (h : BSOK m p bs) : p + 8 < iwTop m := by
  have h8 := (decBS_some h.1).2.2.2.2.2.2
  simp only [iwB, bool?, Option.map_eq_some_iff] at h8
  obtain ⟨v, hv, -⟩ := h8
  exact (truncM_iw_get hv).1

theorem BSOK.grow {m m' : Mem} {p : Nat} {bs : BlockShape} (h : BSOK m p bs) (hg : IWGrow m m') :
    BSOK m' p bs := by
  obtain ⟨hd, hs, hp⟩ := h
  have ht := BSOK.ptop ⟨hd, hs, hp⟩
  refine ⟨hd.grow (decBS_mono p) hg, fun o l ho hl => ?_, fun o l j v ho hl hj hv => ?_⟩
  · rw [iwN_grow hg (by omega)] at ho; rw [iwN_grow hg (by omega)] at hl
    exact Nat.le_trans (hs o l ho hl) hg.iw
  · rw [iwN_grow hg (by omega)] at ho; rw [iwN_grow hg (by omega)] at hl
    have := hs o l ho hl
    rw [iwN_grow hg (by omega)] at hv
    exact Nat.lt_of_lt_of_le (hp o l j v ho hl hj hv) hg.iw

/-- `block_shape_member_names` under the stage relation. -/
theorem memberNamesW_stage {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : memberNamesW n m p = some (r, m')) (hS : StageR vis fe m a) (hb : BSOK m p.toNat bs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
    decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.memberNames ∧
    (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  have ht := hb.ptop
  have hsz := hS.iw.iwSize
  have hts : iwTop m ≤ (m.arr64 IW).size := hS.iw.iw
  have hk : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hb.dec).1
    have := decPL_length m hg; simp only [BlockShape.k, this]; exact (iwN_rdW hl (by omega)).2
  obtain ⟨hr, hd, hg, hf, htop⟩ := memberNamesW_dec h hsz hS.iw.ctl hb.dec (by omega) hb.2.1 hb.2.2
  have hroom : iwTop m' ≤ (m'.arr64 IW).size := by
    simp only [memberNamesW] at h
    rcases hal : allocW m (rdW (m.arr64 IW) (p + 1)) with _ | qm
    · rw [hal] at h; cases h
    obtain ⟨q, m1⟩ := qm
    obtain ⟨hq, rfl, hroom⟩ := allocW_facts hal hsz
    rw [hf.size IW, ← htop]
    have hl := (decBS_some hb.dec).1
    obtain ⟨o, l, ho, hl', hgl⟩ := decAt_some hl
    have hlen := decPL_length m hgl
    have e1 : rdW (m.arr64 IW) (p + 1) = UInt64.ofNat l := by
      have := (iwN_rdW hl' (by omega)).1
      rwa [show UInt64.ofNat (p.toNat + 1) = p + 1 by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp] at this
    rw [e1, UInt64.toNat_ofNat_of_lt' (by rw [← hlen]; exact hk)] at hroom
    rw [← hq, BlockShape.k, hlen]; exact hroom
  refine ⟨stage_frame_iw hS hf (by rw [← hf.size IW]; exact hroom), hg, hr, ?_, ?_⟩
  · rw [hr]; simpa [UInt64.toNat_ofNat_of_lt' hk] using hd
  · rw [hr]; simpa [UInt64.toNat_ofNat_of_lt' hk] using htop

/-- An `indInfo` record's `nparams` word, and no other kind is one. -/
theorem decCI_ind_cases {a : Nat → Option Word} {p : Nat}
    {ci : IConstantInfo} (h : decCI a p = some ci) :
    ∃ k, nat? a p = some k ∧
      ((k = 3 ∧ ∃ cv caps, ci = .indInfo cv caps ∧ nat? a (p + 17) = some caps.nparams) ∨
       (k ≠ 3 ∧ ∀ cv caps, ci ≠ .indInfo cv caps)) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  refine ⟨k, hk, ?_⟩
  match k, h with
  | 0, h => right; refine ⟨by decide, fun cv c hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 1, h => right; refine ⟨by decide, fun cv c hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 2, h => right; refine ⟨by decide, fun cv c hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 3, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, caps, hcaps, rfl⟩ := h
    left; refine ⟨rfl, cv, caps, rfl, ?_⟩
    simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hcaps
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, np, hnp, _, _, rfl⟩ := hcaps
    simpa [Nat.add_assoc] using hnp
  | 4, h => right; refine ⟨by decide, fun cv c hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 5, h => right; refine ⟨by decide, fun cv c hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 6, h => right; refine ⟨by decide, fun cv c hc => ?_⟩; subst hc; simp_all []
  | (_ + 7), h => simp at h

/-! ## `class_n_pc_of` -/

def npcK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0], m3)
    else if erRd m3 (r3.tail.headD 0) = 3 then
      some ([erRd m3 (r3.tail.headD 0 + 17)], m3)
    else some ([0], m3)

def npcK2 (m1 : Mem) (p vis i : Word) : Option Word → Option (List Word × Mem)
  | none => none
  | some b => if b = 1 then some ([rdW (m1.arr64 IW) (p + 4)], m1) else npcK3 (some (findRes m1 vis i, m1))

def npcK1 (n : Nat) (p vis i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => npcK2 m1 p vis i (containsW n m1 (r1.headD 0) (r1.tail.headD 0) i)

/-- **The model of `class_n_pc_of`.** -/
def npcW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, p, vis, i => npcK1 n p vis i (memberNamesW n m p)

section arms
variable (n : Nat) (m m1 m3 : Mem) (p vis i b : Word) (r1 r3 : List Word)
theorem npcW_eq : npcW (n + 1) m p vis i = npcK1 n p vis i (memberNamesW n m p) := rfl
theorem npcK1_some : npcK1 n p vis i (some (r1, m1)) =
    npcK2 m1 p vis i (containsW n m1 (r1.headD 0) (r1.tail.headD 0) i) := rfl
theorem npcK2_hit (h : b = 1) : npcK2 m1 p vis i (some b) = some ([rdW (m1.arr64 IW) (p + 4)], m1) := by
  rw [npcK2, ite_eq_left h]
theorem npcK2_miss (h : b ≠ 1) : npcK2 m1 p vis i (some b) = npcK3 (some (findRes m1 vis i, m1)) := by
  rw [npcK2, ite_eq_right h]
theorem npcK3_none (h : r3.headD 0 = 0) : npcK3 (some (r3, m3)) = some ([0], m3) := by
  rw [npcK3, ite_eq_left h]
theorem npcK3_ind (h : r3.headD 0 ≠ 0) (h3 : erRd m3 (r3.tail.headD 0) = 3) :
    npcK3 (some (r3, m3)) = some ([erRd m3 (r3.tail.headD 0 + 17)], m3) := by
  rw [npcK3, ite_eq_right h, ite_eq_left h3]
theorem npcK3_other (h : r3.headD 0 ≠ 0) (h3 : erRd m3 (r3.tail.headD 0) ≠ 3) :
    npcK3 (some (r3, m3)) = some ([0], m3) := by
  rw [npcK3, ite_eq_right h, ite_eq_right h3]
end arms

grind_pattern [ind_grind] npcW_eq => npcW (n + 1) m p vis i
grind_pattern [ind_grind] npcK1_some => npcK1 n p vis i (some (r1, m1))
grind_pattern [ind_grind] npcK2_hit => npcK2 m1 p vis i (some b)
grind_pattern [ind_grind] npcK2_miss => npcK2 m1 p vis i (some b)
grind_pattern [ind_grind] npcK3_none => npcK3 (some (r3, m3))
grind_pattern [ind_grind] npcK3_ind => npcK3 (some (r3, m3))
grind_pattern [ind_grind] npcK3_other => npcK3 (some (r3, m3))

set_option maxHeartbeats 1000000 in
theorem classNPcOf_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hmc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hmn : p.lookup "block_shape_member_names" = some blockShapeMemberNames)
    (hct : p.lookup "sl_contains" = some slContains) (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hef : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "class_n_pc_of" = some classNPcOf) (n : Nat) (s₀ : St) (q vis i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_n_pc_of" [q, vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧ npcW n s₀.mem q vis i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classNPcOf]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      blockShapeMemberNames_spec p ha hmc hmn n, slContains_spec p hct n,
      envFind_spec p hg hb hef n] <;>
    finish (gen := 20) [rdW_eq, St.setLocs_mem', erRd_get]

theorem npc_mem {bs : BlockShape} {fe : IFEnv} {i : NIdx} (h : bs.memberNames.contains i = true) :
    ConRon.Arena.classNPcOf bs fe i = bs.nP := by
  unfold ConRon.Arena.classNPcOf; rw [ite_eq_left h]

theorem npc_none {bs : BlockShape} {fe : IFEnv} {i : NIdx} (h : ¬ bs.memberNames.contains i = true)
    (hf : fe.find? i = none) : ConRon.Arena.classNPcOf bs fe i = 0 := by
  unfold ConRon.Arena.classNPcOf; rw [ite_eq_right h, hf]

theorem npc_ind {bs : BlockShape} {fe : IFEnv} {i : NIdx} (h : ¬ bs.memberNames.contains i = true)
    {cv : IConstantVal} {caps : IIndCaps} (hf : fe.find? i = some (.indInfo cv caps)) :
    ConRon.Arena.classNPcOf bs fe i = caps.nparams := by
  unfold ConRon.Arena.classNPcOf; rw [ite_eq_right h, hf]

theorem npc_other {bs : BlockShape} {fe : IFEnv} {i : NIdx} (h : ¬ bs.memberNames.contains i = true)
    {ci : IConstantInfo} (hf : fe.find? i = some ci) (hn : ∀ cv caps, ci ≠ .indInfo cv caps) :
    ConRon.Arena.classNPcOf bs fe i = 0 := by
  unfold ConRon.Arena.classNPcOf; rw [ite_eq_right h, hf]
  cases ci with
  | indInfo cv caps => exact absurd rfl (hn cv caps)
  | _ => rfl

/-- **`class_n_pc_of` computes `classNPcOf`** (a pure twin), under the stage relation. -/
theorem npcW_ok {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {p i : Word} {r : List Word} {bs : BlockShape}
    (h : npcW n m p vis i = some (r, m')) (hS : StageR vis fe m a) (hb : BSOK m p.toNat bs)
    (hi : H i) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      r = [UInt64.ofNat (ConRon.Arena.classNPcOf bs fe (decI i))] ∧
      ConRon.Arena.classNPcOf bs fe (decI i) < 2 ^ 64 := by
  rcases n with _ | n
  · simp [npcW] at h
  rw [npcW_eq] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  rw [npcK1_some] at h
  obtain ⟨hS1, hg1, hr1, hd1, ht1⟩ := memberNamesW_stage h1 hS hb
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    have := hS1.iw.iw; have := hS1.iw.iwSize; omega
  obtain ⟨ws, hws, hnm, hwH⟩ := slR_of_decHL m1 _ _ _ hd1 hb1
  rw [UInt64.ofNat_toNat, UInt64.ofNat_toNat] at hws
  rcases h2 : containsW n m1 (r1.headD 0) (r1.tail.headD 0) i with _ | b
  · rw [h2] at h; simp [npcK2] at h
  rw [h2] at h
  have hcb := containsW_ok n m1 _ _ i b ws hws h2
  have hcon : bs.memberNames.contains (decI i) = ws.contains i := by
    rw [hnm]; exact contains_map_decI i hi ws hwH
  have hpt := hb.ptop
  by_cases hc : ws.contains i = true
  · rw [ite_eq_left hc] at hcb
    rw [npcK2_hit (h := hcb)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hnp := (decBS_some hb.dec).2.2.1
    have hrd := iwN_rdW_at (w := p) (k := 4) hnp hS.iw.iwSize
    have hpb : p.toNat + 4 < 2 ^ 64 := by have := hS.iw.iw; have := hS.iw.iwSize; omega
    have e4 : rdW (m1.arr64 IW) (p + 4) = rdW (m.arr64 IW) (p + 4) := by
      simp only [rdW]
      rw [show (p + 4).toNat = p.toNat + 4 by rw [UInt64.toNat_add]; simp; omega, hg1.iwGet _ (by omega)]
    have hm : bs.memberNames.contains (decI i) = true := by rw [hcon]; exact hc
    rw [npc_mem hm]
    refine ⟨hS1, hg1, ?_, hrd.2⟩
    rw [e4, show (4 : Word) = UInt64.ofNat 4 from rfl, hrd.1]
  rw [ite_eq_right hc] at hcb
  rw [npcK2_miss (h := by rw [hcb]; decide)] at h
  have hnc : ¬ bs.memberNames.contains (decI i) = true := by rw [hcon]; exact hc
  have hE := hS1.check.env
  by_cases h0 : (findRes m1 vis i).headD 0 = 0
  · rw [npcK3_none (h := h0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [npc_none hnc (findRes_miss hE hi h0)]
    exact ⟨hS1, hg1, rfl, by decide⟩
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hi h0
  have hfci : fe.find? (decI i) = some ci := by rw [hfind, hci]
  generalize findRes m1 vis i = r3 at h h0 hci
  obtain ⟨k, hk, hcase⟩ := decCI_ind_cases hci
  have hkr := erec_nat (m := m1) (w := r3.tail.headD 0) (c := 0) (by simpa using hk) (by decide)
  rw [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at hkr
  rcases hcase with ⟨rfl, cv, caps, rfl, hnp⟩ | ⟨hk3, hni⟩
  · rw [npcK3_ind (h := h0) (h3 := by rw [hkr.1]; rfl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hr17 := erec_nat (m := m1) (w := r3.tail.headD 0) (c := 17) hnp (by decide)
    rw [npc_ind hnc hfci]
    refine ⟨hS1, hg1, ?_, hr17.2⟩
    rw [show (17 : Word) = UInt64.ofNat 17 from rfl, hr17.1]
  · have hne : erRd m1 (r3.tail.headD 0) ≠ 3 := by
      rw [hkr.1]; intro e
      have := congrArg UInt64.toNat e
      rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; exact hkr.2)] at this
      exact hk3 this
    rw [npcK3_other (h := h0) (h3 := hne)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [npc_other hnc hfci hni]
    exact ⟨hS1, hg1, rfl, by decide⟩


/-- **`class_n_pc_of` refines `classNPcOf`** (a pure twin: the result word is its value). -/
@[refines ConRon.Arena.classNPcOf]
theorem classNPcOf_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hmc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hmn : p.lookup "block_shape_member_names" = some blockShapeMemberNames)
    (hct : p.lookup "sl_contains" = some slContains) (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hef : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "class_n_pc_of" = some classNPcOf) (n : Nat) (s₀ : St) (a₀ : AState)
    (vis : Word) (fe : IFEnv) (q i : Word) (bs : BlockShape)
    (hS : StageR vis fe s₀.mem a₀) (hb' : BSOK s₀.mem q.toNat bs) (hi : H i) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_n_pc_of" [q, vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      r = [UInt64.ofNat (ConRon.Arena.classNPcOf bs fe (decI i))]; ⊤⦄ :=
  triple_post (classNPcOf_spec p ha hmc hmn hct hg hb hef hp n s₀ q vis i) fun _ _ ⟨hl, hw⟩ =>
    have h := npcW_ok hw hS hb' hi
    ⟨hl, h.1, h.2.1, h.2.2.1⟩

end L.Ind

end
