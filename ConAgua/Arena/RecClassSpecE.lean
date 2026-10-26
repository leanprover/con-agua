import ConAgua.Arena.RecClassSpecD
import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndPos2SpecA
import ConAgua.Arena.DeclHeader

/-!
# `RecClass`: `classNPcOf`, `classReadSlot`, `classReadSlots` (lane `indproofs2`, helper `rec`)
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
    exact Nat.le_trans (hs o l ho hl) hg.1
  · rw [iwN_grow hg (by omega)] at ho; rw [iwN_grow hg (by omega)] at hl
    have := hs o l ho hl
    rw [iwN_grow hg (by omega)] at hv
    exact Nat.lt_of_lt_of_le (hp o l j v ho hl hj hv) hg.1

/-- `block_shape_member_names` under the stage relation. -/
theorem memberNamesW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {p : Word} {r : List Word} {bs : BlockShape}
    (h : memberNamesW n m p = some (r, m')) (hS : StageR dn vis fe m a) (hb : BSOK m p.toNat bs) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ r = [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k] ∧
    decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs.memberNames ∧
    (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  have ht := hb.ptop
  have hsz := hS.2.2.2.1
  have hts : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  have hk : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, ho, hl, hg⟩ := decAt_some (decBS_some hb.dec).1
    have := decPL_length m hg; simp only [BlockShape.k, this]; exact (iwN_rdW hl (by omega)).2
  obtain ⟨hr, hd, hg, hf, htop⟩ := memberNamesW_dec h hsz hS.2.2.2.2.2 hb.dec (by omega) hb.2.1 hb.2.2
  have hroom : iwTop m' ≤ (m'.arr64 IW).size := by
    simp only [memberNamesW] at h
    rcases hal : allocW m (rdW (m.arr64 IW) (p + 1)) with _ | qm
    · rw [hal] at h; cases h
    obtain ⟨q, m1⟩ := qm
    obtain ⟨hq, rfl, hroom⟩ := allocW_facts hal hsz
    rw [hf.2.2.1 IW, ← htop]
    have hl := (decBS_some hb.dec).1
    obtain ⟨o, l, ho, hl', hgl⟩ := decAt_some hl
    have hlen := decPL_length m hgl
    have e1 : rdW (m.arr64 IW) (p + 1) = UInt64.ofNat l := by
      have := (iwN_rdW hl' (by omega)).1
      rwa [show UInt64.ofNat (p.toNat + 1) = p + 1 by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp] at this
    rw [e1, UInt64.toNat_ofNat_of_lt' (by rw [← hlen]; exact hk)] at hroom
    rw [← hq, BlockShape.k, hlen]; exact hroom
  refine ⟨stage_frame_iw hS hf (by rw [← hf.2.2.1 IW]; exact hroom), hg, hr, ?_, ?_⟩
  · rw [hr]; simpa [UInt64.toNat_ofNat_of_lt' hk] using hd
  · rw [hr]; simpa [UInt64.toNat_ofNat_of_lt' hk] using htop

/-! ## `env_find` through the rows -/

theorem rowPW_eq (m : Mem) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : tagW w ≤ 2) :
    rowPW m w = rowP m w := by
  have h1 := tagW_toNat w
  have h2 := ixW_toNat w hw
  have ht' : rowTag w ≤ 2 := by rw [← h1]; exact UInt64.le_iff_toNat_le.mp ht
  have hix : (ixW w + 1).toNat = rowIx w + 1 := by
    rw [UInt64.toNat_add, h2]; simp [rowIx]; omega
  simp only [rowPW, rowP, ht', ite_true, rdW, hix]
  simp [selArr_rowSelW w ht']

/-- **`env_find` is `find?`**: the memory unchanged, the result decoded by `decFound`, a found row
decoding. -/
theorem envFindW_found {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m1 : Mem}
    {w : Word} {r : List Word} (h : envFindW m w vis = some (r, m1)) (hE : EnvR dn m vis fe)
    (hw : w.toNat < 2 ^ 32) :
    m1 = m ∧ fe.find? (decI w) = decFound dn m (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) dn (r.tail.headD 0).toNat = some ci) := by
  unfold envFindW at h
  obtain ⟨ht, h⟩ := of_ite_none h
  have ht2 : tagW w ≤ 2 := by
    have : ¬ (2 : Word).toNat < (tagW w).toNat := fun e => ht (UInt64.lt_iff_toNat_lt.mpr e)
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have htag : rowTag w ≤ 2 := by rw [← tagW_toNat]; exact UInt64.le_iff_toNat_le.mp ht2
  have key := EnvR.find?_eq hE w hw htag
  have key2 := EnvR.row_dec hE w hw htag
  rw [rowCW_eq m w hw ht2, rowPW_eq m w hw ht2] at h
  by_cases hc : rowC m w = 0
  · rw [ite_eq_left hc] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp [key, hc, decFound]
  rw [ite_eq_right hc] at h
  by_cases hv : rowC m w - 1 < vis
  · rw [ite_eq_left hv] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hc' : (rowC m w).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
    have hv' : (rowC m w).toNat - 1 < vis.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp hv
      rwa [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))] at this
    refine ⟨rfl, by simp [key, hc, hv', decFound], fun _ => key2 hc⟩
  rw [ite_eq_right hv] at h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hc' : (rowC m w).toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
  have : ¬ (rowC m w).toNat - 1 < vis.toNat := by
    intro e; apply hv; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simpa using e
  simp [key, hc, this, decFound]

theorem contains_map_decI {k : IdxKind} (x : Word) (hx : H x) : ∀ (ws : List Word),
    (∀ w ∈ ws, H w) → (ws.map (decI : Word → Idx k)).contains (decI x) = ws.contains x
  | [], _ => rfl
  | w :: ws, h => by
    simp only [List.map_cons, List.contains_cons]
    rw [decI_beq x w hx (h w (by simp)), contains_map_decI x hx ws (fun v hv => h v (by simp [hv]))]
    by_cases e : w = x
    · subst e; simp
    · simp [Ne.symm e]

/-- An `indInfo` record's `nparams` word, and no other kind is one. -/
theorem decCI_ind_cases {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
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
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, np, hnp, _, _, rfl⟩ := hcaps
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
    else if rdW (m3.arr64 EREC) (r3.tail.headD 0) = 3 then
      some ([rdW (m3.arr64 EREC) (r3.tail.headD 0 + 17)], m3)
    else some ([0], m3)

def npcK2 (m1 : Mem) (p vis i : Word) : Option Word → Option (List Word × Mem)
  | none => none
  | some b => if b = 1 then some ([rdW (m1.arr64 IW) (p + 4)], m1) else npcK3 (envFindW m1 i vis)

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
theorem npcK2_miss (h : b ≠ 1) : npcK2 m1 p vis i (some b) = npcK3 (envFindW m1 i vis) := by
  rw [npcK2, ite_eq_right h]
theorem npcK3_none (h : r3.headD 0 = 0) : npcK3 (some (r3, m3)) = some ([0], m3) := by
  rw [npcK3, ite_eq_left h]
theorem npcK3_ind (h : r3.headD 0 ≠ 0) (h3 : rdW (m3.arr64 EREC) (r3.tail.headD 0) = 3) :
    npcK3 (some (r3, m3)) = some ([rdW (m3.arr64 EREC) (r3.tail.headD 0 + 17)], m3) := by
  rw [npcK3, ite_eq_right h, ite_eq_left h3]
theorem npcK3_other (h : r3.headD 0 ≠ 0) (h3 : rdW (m3.arr64 EREC) (r3.tail.headD 0) ≠ 3) :
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

theorem classNPcOf_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hmc : p.lookup "member_names_copy" = some memberNamesCopy)
    (hmn : p.lookup "block_shape_member_names" = some blockShapeMemberNames)
    (hct : p.lookup "sl_contains" = some slContains) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hef : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "class_n_pc_of" = some classNPcOf) (n : Nat) (s₀ : St) (q vis i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_n_pc_of" [q, vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧ npcW n s₀.mem q vis i = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, classNPcOf]
  rcases n with _ | n
  · vcgen [exec] <;> grind
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      blockShapeMemberNames_spec p ha hmc hmn n, slContains_spec p hct n,
      envFind_specW p hx hg hef n] <;>
    finish (gen := 20) [rdW_eq]

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
theorem npcW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {p i : Word} {r : List Word} {bs : BlockShape}
    (h : npcW n m p vis i = some (r, m')) (hS : StageR dn vis fe m a) (hb : BSOK m p.toNat bs)
    (hi : H i) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      r = [UInt64.ofNat (ConRon.Arena.classNPcOf bs fe (decI i))] ∧
      ConRon.Arena.classNPcOf bs fe (decI i) < 2 ^ 64 := by
  rcases n with _ | n
  · simp [npcW] at h
  rw [npcW_eq] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  rw [npcK1_some] at h
  obtain ⟨hS1, hg1, hr1, hd1, ht1⟩ := memberNamesW_stage h1 hS hb
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    have := hS1.2.1; have := hS1.2.2.2.1; omega
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
    have hrd := iwN_rdW_at (w := p) (k := 4) hnp hS.2.2.2.1
    have hpb : p.toNat + 4 < 2 ^ 64 := by have := hS.2.1; have := hS.2.2.2.1; omega
    have e4 : rdW (m1.arr64 IW) (p + 4) = rdW (m.arr64 IW) (p + 4) := by
      simp only [rdW]
      rw [show (p + 4).toNat = p.toNat + 4 by rw [UInt64.toNat_add]; simp; omega, hg1.2.2.1 _ (by omega)]
    have hm : bs.memberNames.contains (decI i) = true := by rw [hcon]; exact hc
    rw [npc_mem hm]
    refine ⟨hS1, hg1, ?_, hrd.2⟩
    rw [e4, show (4 : Word) = UInt64.ofNat 4 from rfl, hrd.1]
  rw [ite_eq_right hc] at hcb
  rw [npcK2_miss (h := by rw [hcb]; decide)] at h
  rcases h3 : envFindW m1 i vis with _ | rm3
  · rw [h3] at h; simp [npcK3] at h
  obtain ⟨r3, m3⟩ := rm3
  rw [h3] at h
  obtain ⟨hm3, hfind, hdec⟩ := envFindW_found h3 hS1.1.env hi
  subst hm3
  have hnc : ¬ bs.memberNames.contains (decI i) = true := by rw [hcon]; exact hc
  by_cases h0 : r3.headD 0 = 0
  · rw [npcK3_none (h := h0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hfn : fe.find? (decI i) = none := by rw [hfind, decFound, ite_eq_left h0]
    rw [npc_none hnc hfn]
    exact ⟨hS1, hg1, rfl, by decide⟩
  obtain ⟨ci, hci⟩ := hdec h0
  have hfci : fe.find? (decI i) = some ci := by rw [hfind, decFound, ite_eq_right h0, hci]
  obtain ⟨k, hk, hcase⟩ := decCI_ind_cases hci
  have hkr := erec_nat (w := r3.tail.headD 0) (c := 0) (by simpa using hk) (by decide)
  rw [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at hkr
  rcases hcase with ⟨rfl, cv, caps, rfl, hnp⟩ | ⟨hk3, hni⟩
  · rw [npcK3_ind (h := h0) (h3 := by rw [hkr.1]; rfl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hr17 := erec_nat (w := r3.tail.headD 0) (c := 17) hnp (by decide)
    rw [npc_ind hnc hfci]
    refine ⟨hS1, hg1, ?_, hr17.2⟩
    rw [show (17 : Word) = UInt64.ofNat 17 from rfl, hr17.1]
  · have hne : rdW (m3.arr64 EREC) (r3.tail.headD 0) ≠ 3 := by
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
    (hct : p.lookup "sl_contains" = some slContains) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hef : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "class_n_pc_of" = some classNPcOf) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (q i : Word) (bs : BlockShape)
    (hS : StageR dn vis fe s₀.mem a₀) (hb : BSOK s₀.mem q.toNat bs) (hi : H i) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_n_pc_of" [q, vis, i]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      r = [UInt64.ofNat (ConRon.Arena.classNPcOf bs fe (decI i))]; ⊤⦄ :=
  triple_post (classNPcOf_spec p ha hmc hmn hct hx hg hef hp n s₀ q vis i) fun _ _ ⟨hl, hw⟩ =>
    have h := npcW_ok hw hS hb hi
    ⟨hl, h.1, h.2.1, h.2.2.1⟩

end L.Ind
