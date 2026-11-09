module

public import ConAgua.Arena.IndSumSpec.StructUsedLater
public import ConAgua.Arena.CallF
import ConAgua.Arena.IndSumSpec.StructProjArgP
public import ConAgua.Arena.WriteSets
public import ConAgua.Arena.IndCopy2
import ConAgua.Arena.WalkLiftRefine
import ConAgua.Arena.DeclBase
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.Walk
import all ConAgua.Arena.MemoLib

@[expose] public section

/-!
# `struct_used_later`'s memory effect, at any arguments

`struct_used_later` is a leaf of the core stage's and of `imFns`' write-set checks (the twin's core
reaches it through `infer_proj`); what it does to memory, at any arguments and fuel:

* its call closure (`usFns`: the strippers, the `hb` walk, the bound walk) writes only `IW`, `HBM`,
  `BMEMO` and their control words (`usP_closed`, decided);
* `structUsedLater_specV`: its model `ustW` at any argument list;
* the pool only grows (`ustW_grow`: `IWGrow`, `IWOK` kept), the `hb` walk writes only its memo and
  the bound walk's (`hbFastW_frame`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The program and its write set -/

/-- `struct_used_later`'s functions and their callees. -/
def usP : Prog :=
  [("struct_used_later", structUsedLaterL), ("has_loose_b_var_b_fast", hasLooseBVarBFastL),
   ("hb_clear", memoClearG hbSch), ("has_loose_b_var_b_go", hasLooseBVarBGoL),
   ("hb_find", memoFindG hbSch), ("has_loose_b_var_b_ins", hasLooseBVarBInsL),
   ("hb_put", memoPutG hbSch)] ++ stripProg ++ bvbProg

/-- The functions `struct_used_later` reaches. -/
def usFns : List FnName :=
  ["struct_used_later", "has_loose_b_var_b_fast", "hb_clear", "has_loose_b_var_b_go", "hb_find",
   "has_loose_b_var_b_ins", "hb_put", "strip_pis", "strip_lams", "e_view", "iw_alloc"] ++ bvbFns

/-- The arrays `struct_used_later` writes. -/
def usA : List TieredArray := [IW, HBM, BMEMO]

/-- The `CTL` words `struct_used_later` writes. -/
def usC : List Word := [200, 214, 215, 24, 25]

theorem usP_closed : closedA usP usA usC usFns = true := by decide +kernel

/-- The program bundle. -/
abbrev UsF (p : Prog) : Prop := ProgHas p usP

theorem UsF.closed {p : Prog} (hp : UsF p) : closedA p usA usC usFns = true :=
  closedW_of_agree usP_closed (hp.agree usFns)

/-! ## The spec at any arguments -/

theorem structUsedLater_specV {p : Prog} (hp : UsF p) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "struct_used_later" vs
    ⦃fun r s' => LocEq s' s₀ ∧
      ustW n s₀.mem (vs.getD 0 0) (vs.getD 1 0) (vs.getD 2 0) = some (r.headD 0, s'.mem); ⊤⦄ := by
  have hv : p.lookup "e_view" = some eView := hp.get _
  have hf : p.lookup "hb_find" = some (memoFindG hbSch) := hp.get _
  have hput : p.lookup "hb_put" = some (memoPutG hbSch) := hp.get _
  have hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL := hp.get _
  have hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL := hp.get _
  have hbp : BvbProg p := ProgHas.right hp
  have hst : StripProg p := ProgHas.right (ProgHas.left hp)
  have hcl : p.lookup "hb_clear" = some (memoClearG hbSch) := hp.get _
  have hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL := hp.get _
  have hpu : p.lookup "struct_used_later" = some structUsedLaterL := hp.get _
  rw [invoke_eq _ hpu]
  simp only [callFn, structUsedLaterL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      stripPis_specF p hst (n + 1), hbFast_spec p hv hf hput hins hgo hbp hcl hfast n] <;>
    finish [ustW, Locals.init]


/-! ## The `hb` walk writes only the two memos -/

/-- What the `hb` walk writes: its memo and the bound walk's, with their control words. -/
def hbWA : List TieredArray := [HBM, BMEMO]
def hbWC : List Word := [214, 215, 24, 25]

theorem hbInsW_frame {m m' : Mem} {e i r x : Word} (h : hbInsW m e i r = some (x, m')) :
    MemFrame hbWA hbWC m m' := by
  simp only [hbInsW] at h
  cases hm : msetG hbSch m e i r with
  | none => rw [hm] at h; simp at h
  | some m2 =>
    rw [hm] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact (msetG_frame hbSch hbSch_wf m m2 e i r hm).mono (by simp [hbSch, hbWA]) (by simp [hbSch, hbWC])

theorem bvbW_hbFrame {n : Nat} {m m' : Mem} {h f x : Word} (hb : bvbW n m h f = some (x, m')) :
    MemFrame hbWA hbWC m m' :=
  (bvbW_frame n m m' h f x hb).mono (by simp [hbWA]) (by simp [hbWC])

/-- `mfr_auto` for `MemFrame hbWA hbWC`. -/
syntax "hbf_auto" ident "[" term,* "]" : tactic
macro_rules
  | `(tactic| hbf_auto $h [$ts,*]) => `(tactic|
    repeat' (first
      | with_reducible exact MemFrame.refl _ _ _
      | (simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident; rw [← ($h).2]; exact MemFrame.refl _ _ _)
      | (simp only [Option.some.injEq] at $h:ident; subst $h:ident; exact MemFrame.refl _ _ _)
      | (simp only [reduceCtorEq] at $h:ident; done)
      | (first $[| refine MemFrame.trans ($ts (by with_reducible assumption)) ?_]*)
      | split at $h:ident))

theorem hbGoW_frame : ∀ (n : Nat) (m m' : Mem) (f i h r : Word), hbGoW n m f i h = some (r, m') →
    MemFrame hbWA hbWC m m'
  | 0, _, _, _, _, _, _, hh => by simp [hbGoW] at hh
  | n + 1, m, m', f, i, h, r, hh => by
    have node : ∀ {m m' : Mem} {f i g x y z r : Word}, hbNodeW n f m i g x y z = some (r, m') →
        MemFrame hbWA hbWC m m' := by
      intro m m' f i g x y z r h
      unfold hbNodeW hbO1 hbL1 hbL2 at h
      hbf_auto h [hbGoW_frame n _ _ _ _ _ _]
    unfold hbGoW hbK1 hbK2 hbK3 hbK4 at hh
    hbf_auto hh [bvbW_hbFrame, node, hbInsW_frame]

theorem hbFastW_frame {n : Nat} {m m' : Mem} {i e r : Word} (h : hbFastW n m i e = some (r, m')) :
    MemFrame hbWA hbWC m m' := by
  unfold hbFastW at h
  split at h
  · simp at h
  exact ((mclearG_frame hbSch m).mono (by simp) (by simp [hbSch, hbWC])).trans (hbGoW_frame _ _ _ _ _ _ _ h)

/-- A frame of the two memos keeps `IWOK` and the pools. -/
theorem iw_of_hbFrame {m m' : Mem} (hf : MemFrame hbWA hbWC m m') (hI : IWOK m) : IWOK m' ∧ IWGrow m m' := by
  have hW := hf.arr IW (by decide) (by decide)
  have hE := hf.arr EREC (by decide) (by decide)
  have hE1 := hf.arr (tier1 EREC) (by decide) (by decide)
  have h129 := hf.ctl 129 (by decide)
  have h130 := hf.ctl 130 (by decide)
  have h200 := hf.ctl 200 (by decide)
  exact ⟨L.Arena.IWOK.frame hf (by decide) (by decide) (by decide) (by decide) hI (by decide) (by decide),
    ⟨by simp [iwTop, h200], by simp [erTop, h129], fun i _ => by rw [hW], fun i _ => by rw [hE],
      by simp [erecTop1, h130], fun i _ => by rw [hE1]⟩⟩

/-! ## The strippers only grow the pool -/

/-- The cut of `IW` and the top word that a frame of `IW`, `CTL[200]` and these facts keep. -/
theorem stripGoW_iw (tg k o : Word) : ∀ (f : Nat) (m m' : Mem) (n h : Word) (r : List Word),
    stripGoW tg k o f m n h = some (r, m') → IWOK m → iwTop m = o.toNat + n.toNat → n ≤ k →
    IWOK m' ∧ MemFrame [IW] [200] m m' ∧ o.toNat ≤ iwTop m' ∧
      ∀ i < o.toNat, (m'.arr64 IW)[i]? = (m.arr64 IW)[i]? := by
  intro f
  induction f with
  | zero => intro m m' n h r hm; simp [stripGoW] at hm
  | succ f ih =>
  intro m m' n h r hm hI htop hnk
  by_cases hn : ¬ n < k
  · rw [stripGoW_ge tg k o f m n h hn] at hm
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    exact ⟨hI, MemFrame.refl _ _ _, by omega, fun _ _ => rfl⟩
  have hn' : n < k := Classical.not_not.mp hn
  have hnk' : n.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp hn'
  by_cases hg : tagW h ≠ tg
  · rw [stripGoW_tag tg k o f m n h hn' hg] at hm
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    have hf : MemFrame [IW] [200] m (m.set64 CTL 200 o) :=
      MemFrame.mono (MemFrame.setCtl m 200 o) (by simp) (by simp)
    have hc := hI.ctl
    have ht : iwTop (m.set64 CTL 200 o) = o.toNat := by
      simp only [iwTop, rdW_set64]; rw [ite_eq_left ⟨trivial, trivial, by simpa using hc⟩]
    refine ⟨IWOK.of_iw hf hI (by rw [ht, hf.size IW]; have := hI.iw; omega), hf, by omega, fun i _ => ?_⟩
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  by_cases hv : eViewW m h = []
  · simp [stripGoW, hn', hg, hv] at hm
  cases ha : allocW m 1 with
  | none => simp [stripGoW, hn', hg, ha] at hm
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  rw [stripGoW_step tg k o f m m1 n h q hn' hg hv ha] at hm
  obtain ⟨hq, rfl, hroom⟩ := allocW_facts ha hI.iwSize
  have hc := hI.ctl
  have hq' : q.toNat = iwTop m := by rw [hq]; rfl
  have hsz := hI.iwSize
  have h200 : UInt64.toNat 200 < (m.arr64 CTL).size := by simpa using hc
  have hr : iwTop m + 1 ≤ (m.arr64 IW).size := by rw [← hq']; simpa using hroom
  have ht1 : iwTop (allocMem m 1) = iwTop m + 1 := by
    simp only [iwTop] at hr ⊢
    simp only [allocMem, rdW_set64]
    rw [ite_eq_left ⟨trivial, trivial, h200⟩, UInt64.toNat_add]; simp; omega
  have hf1 := allocMem_frame m 1
  have hI1 : IWOK (allocMem m 1) := IWOK.of_iw hf1 hI (by rw [ht1, hf1.size IW]; omega)
  have hf2 := set64IW_frame (allocMem m 1) q ((eViewW m h).tail.headD 0)
  have ht2 : iwTop ((allocMem m 1).set64 IW q ((eViewW m h).tail.headD 0)) = iwTop m + 1 := by
    have e : iwTop ((allocMem m 1).set64 IW q ((eViewW m h).tail.headD 0)) = iwTop (allocMem m 1) := by
      simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    rw [e, ht1]
  have hI2 : IWOK ((allocMem m 1).set64 IW q ((eViewW m h).tail.headD 0)) :=
    IWOK.of_iw hf2 hI1 (by rw [ht2, hf2.size IW, hf1.size IW]; omega)
  have hn1 : (n + 1).toNat = n.toNat + 1 := by
    have := k.toNat_lt
    rw [UInt64.toNat_add]; simp; first | omega | rw [Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hI', hf', hot, hlow⟩ := ih _ m' (n + 1) ((eViewW m h).tail.tail.headD 0) r hm hI2
    (by rw [ht2, htop, hn1]; omega) (UInt64.le_iff_toNat_le.mpr (by omega))
  refine ⟨hI', (hf1.trans hf2).trans hf', hot, fun i hi => ?_⟩
  rw [hlow i hi, set64IW_get, ite_eq_right (by omega), allocMem_IW]

/-- **The strippers keep `IWOK` and only grow the pool**, at any memory. -/
theorem stripF_grow {tg : Word} {m m' : Mem} {args r : List Word} (h : stripF tg m args = some (r, m'))
    (hI : IWOK m) : IWOK m' ∧ IWGrow m m' := by
  simp only [stripF] at h
  generalize (args.headD 0).toNat + 2 = F at h
  match F, h with
  | f + 1, h =>
  simp only [stripTW] at h
  obtain ⟨hI', hf, hot, hlow⟩ := stripGoW_iw tg _ _ (f + 1) m m' 0 _ r h hI (by simp only [iwTop, UInt64.toNat_zero, Nat.add_zero])
    (UInt64.le_iff_toNat_le.mpr (by simp))
  have hE := hf.arr EREC (by decide) (by decide)
  have hE1 := hf.arr (tier1 EREC) (by decide) (by decide)
  have h129 := hf.ctl 129 (by decide)
  have h130 := hf.ctl 130 (by decide)
  refine ⟨hI', ⟨by simpa [iwTop] using hot, by simp [erTop, h129], fun i hi => hlow i (by simpa [iwTop] using hi),
    fun i _ => by rw [hE], by simp [erecTop1, h130], fun i _ => by rw [hE1]⟩⟩

/-- **`struct_used_later`'s model keeps `IWOK` and only grows the pool**, at any memory. -/
theorem ustW_grow {n : Nat} {m m' : Mem} {cty nP j r : Word} (h : ustW n m cty nP j = some (r, m'))
    (hI : IWOK m) : IWOK m' ∧ IWGrow m m' := by
  simp only [ustW] at h
  obtain ⟨rs, m1, hst, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨hI1, hg1⟩ := stripF_grow hst hI
  by_cases hz : rs.headD 0 = 0
  · rw [ustK1_some_zero hz] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨hI1, hg1⟩
  rw [ustK1_some_ne hz] at h
  obtain ⟨hI2, hg2⟩ := iw_of_hbFrame (hbFastW_frame h) hI1
  exact ⟨hI2, hg1.trans hg2⟩

end L.Ind

end
