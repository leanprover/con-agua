module

public import ConAgua.Arena.IndInstallSpec.DecCNS
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConRon.Arena.Inductives.BlockInstall
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import ConAgua.Arena.LdRd

@[expose] public section

/-!
# ConsBlockCtors: `ConRon.Arena.consBlockCtors`

The refinement theorems `consBlockCtors_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decCNS_mono (q : Nat) : OMono (fun m => decCNS m q) :=
  OMono.decAt (fun o l => OMono.decPL decCN_mono o l) q

/-- **A constructor group** (`BlockShape.ctorGroups`): a member record read as its `cvT`'s name and
its constructors (`block_shape_ctor_groups` hands out the members' slice itself). -/
def decCtorGrp (m : Mem) (p : Nat) : Option (NIdx × List (IConstantVal × Nat)) := do
  let ms ← decMS m p
  pure (ms.cvT.name, ms.ctors)

theorem decCtorGrp_mono (q : Nat) : OMono (fun m => decCtorGrp m q) :=
  OMono.bind (decMS_mono q) fun _ => OMono.const _

theorem mapM_some_map {α β γ : Type} {f : α → Option β} {g : α → Option γ} {k : β → γ}
    (hfg : ∀ x y, f x = some y → g x = some (k y)) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.mapM g = some (ys.map k)
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    simp [List.mapM_cons, hfg x y hy, mapM_some_map hfg xs ys' hys]

/-- The members' slice decodes as the groups. -/
theorem decPL_decCtorGrp {m : Mem} {o l : Nat} {ms : List MemberShape}
    (h : decPL m (decMS m) o l = some ms) :
    decPL m (decCtorGrp m) o l = some (ms.map fun ms => (ms.cvT.name, ms.ctors)) := by
  unfold decPL at h ⊢
  refine mapM_some_map (fun j y hy => ?_) _ _ h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hy ⊢
  obtain ⟨v, hv, hd⟩ := hy
  exact ⟨v, hv, by simp [decCtorGrp, hd]⟩

/-- **The model of `cons_block_ctors(nP, o, l, vis)`** (generated). -/
l_model icbc_spec (p : Prog) (hp : p.lookup "cons_block_ctors" = some consBlockCtors)
  fns [hp ↦ icbcW list]
  specs [callW_spec p n "cons_sum_ctors"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE]

/-- **The model of `block_shape_ctor_groups(p)`** (generated): the members' slice header. -/
l_model bscg_spec (p : Prog) (hp : p.lookup "block_shape_ctor_groups" = some blockShapeCtorGroups)
  fns [hp ↦ bscgW ro list]
  grind [arena_grind] extra [ld64_rd_spec] simp []

/-- **`block_shape_ctor_groups` refines `BlockShape.ctorGroups`**: the members' slice, read as the
groups. -/
theorem ctorGroups_psl {m : Mem} {pp : Word} {bs : BlockShape}
    (hm : DecB (fun m' => decPL m' (decMS m') (rdW (m.arr64 IW) pp).toNat (rdW (m.arr64 IW) (pp + 1)).toNat)
      m bs.members)
    (hb : (rdW (m.arr64 IW) pp).toNat + (rdW (m.arr64 IW) (pp + 1)).toNat ≤ iwTop m) :
    PSlR decCtorGrp bs.ctorGroups (rdW (m.arr64 IW) pp) (rdW (m.arr64 IW) (pp + 1)) m :=
  ⟨decPL_decCtorGrp hm, hb⟩

/-- **`cons_block_ctors`' model refines `consBlockCtors`.** -/
theorem icbcW_ok (p : Prog) (hRp : RecProg p) (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hcs : p.lookup "cons_sum_ctors" = some consSumCtorsL) (nP : Word) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv) (o l : Word)
      (gs : List (NIdx × List (IConstantVal × Nat))) (r : List Word),
    icbcW p n m nP o l vis = some (r, m') → StageR vis fe m a → PSlR decCtorGrp gs o l m →
    StageR (r.headD 0) (ConRon.Arena.consBlockCtors nP.toNat gs fe) m' a ∧ IWGrow m m' := by
  induction n with
  | zero => intro m m' a vis fe o l gs r h; rw [icbcW.eq_1] at h; cases h
  | succ n ih =>
  intro m m' a vis fe o l gs r h hS hgs
  by_cases hl : l = 0
  · rw [icbcW.arm1 p n m nP o l vis hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : gs = [] := by
      have h := hgs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨hS, IWGrow.refl m⟩
  obtain ⟨q, g, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hgs hl
  rw [icbcW.arm2 p n m nP o l vis hl, hw] at h
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hdx' : decCtorGrp (truncM m) q = some g := hdx
  simp only [decCtorGrp, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hdx'
  obtain ⟨ms, hms, rfl⟩ := hdx'
  obtain ⟨⟨av, hav, hcvT⟩, -, -, hct⟩ := decMS_some hms
  -- the member's `cvT` pointer and its name word
  obtain ⟨hwa, havb, -⟩ := partsIwRd hav (w := UInt64.ofNat q) hq'
  have hcvE : decCV (erecP m) av = some ms.cvT := decCVp_truncM hcvT
  obtain ⟨wn, hwn, hwnl, hname⟩ := decCV_name hcvE
  have hav' : (UInt64.ofNat av : Word).toNat = av := UInt64.toNat_ofNat_of_lt' havb
  have hrn : erRd m (UInt64.ofNat av) = wn := (erRd_of_erecP (by rw [hav']; exact hwn)).1
  -- the member's constructor slice
  obtain ⟨co, cl, hco, hcl, hcsd⟩ := decAt_some hct
  have hq2 : (UInt64.ofNat q + 2 : Word).toNat = q + 2 := by
    have := partsIwLt hcl; rw [UInt64.toNat_add, hq']; simp; omega
  have hq3 : (UInt64.ofNat q + 3 : Word).toNat = q + 2 + 1 := by
    have := partsIwLt hcl; rw [UInt64.toNat_add, hq']; simp; omega
  obtain ⟨hwo, hcob, -⟩ := partsIwRd hco (w := UInt64.ofNat q + 2) hq2
  obtain ⟨hwl, hclb, -⟩ := partsIwRd hcl (w := UInt64.ofNat q + 3) hq3
  have hrd : rdW (m.arr64 (tierA EREC (rdW (m.arr64 IW) (UInt64.ofNat q) >>> 40)))
      (rdW (m.arr64 IW) (UInt64.ofNat q) &&& 1099511627775) = wn := by
    rw [hwa]; exact hrn
  rw [hrd, hwo, hwl] at h
  rcases h1 : callW p n "cons_sum_ctors" [nP, wn, UInt64.ofNat co, UInt64.ofNat cl, vis] m
    with _ | ⟨r1, m1⟩
  · rw [h1, icbcW.k_cons_sum_ctors.none] at h; cases h
  rw [h1, icbcW.k_cons_sum_ctors.arm1] at h
  obtain ⟨s1, rfl, -, hS1, hg1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (consSumCtors_refines p hRp hci hcs n ⟨m, Locals.init []⟩ a fe vis nP wn _ _ ms.ctors hS
      (by rw [UInt64.toNat_ofNat_of_lt' hcob, UInt64.toNat_ofNat_of_lt' hclb]; exact hcsd)) h1
  rcases h2 : icbcW p n s1.mem nP (o + 1) (l - 1) (r1.headD 0) with _ | ⟨r2, m2⟩
  · rw [h2, icbcW.k_cons_block_ctors.none] at h; cases h
  rw [h2, icbcW.k_cons_block_ctors.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨hS2, hg2⟩ := ih s1.mem m2 a (r1.headD 0) _ (o + 1) (l - 1) rest r2 h2 hS1
    (hrest.grow decCtorGrp_mono hg1)
  refine ⟨?_, hg1.trans hg2⟩
  simpa [ConRon.Arena.consBlockCtors, hname] using hS2

/-- **`cons_block_ctors` refines `consBlockCtors`**: from the stage relation at `vis` of `fe` and
the groups decoded below the tops (the members' slice read by `decCtorGrp`), a returning run returns
the view of the environment with every member's constructors pushed under its name, member by
member. -/
@[refines ConRon.Arena.consBlockCtors]
theorem consBlockCtors_refines (p : Prog) (hRp : RecProg p)
    (hci : p.lookup "ctor_info_rec" = some ctorInfoRecL)
    (hcs : p.lookup "cons_sum_ctors" = some consSumCtorsL)
    (hp : p.lookup "cons_block_ctors" = some consBlockCtors) (n : Nat) (s₀ : St) (a₀ : AState)
    (fe : IFEnv) (nP o l vis : Word)
    (gs : List (NIdx × List (IConstantVal × Nat))) (hS : StageR vis fe s₀.mem a₀)
    (hgs : PSlR decCtorGrp gs o l s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_block_ctors" [nP, o, l, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR (r.headD 0) (ConRon.Arena.consBlockCtors nP.toNat gs fe) s'.mem a₀ ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (icbc_spec p hp n s₀ nP o l vis) fun r _ ⟨hl, hm⟩ =>
    ⟨hl, icbcW_ok p hRp hci hcs nP n _ _ a₀ vis fe o l gs r hm hS hgs⟩

end L.Ind

end
