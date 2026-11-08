module

import ConAgua.Arena.IndPosSpec.Grow
public import ConAgua.Arena.RecGenSpec.DecNLAt
import ConAgua.Arena.RecGenSpec.KcW
public import ConAgua.Arena.RecGenSpec.KeysProg
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
public import ConAgua.Arena.IndPosSpec.NestSeedOf
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndPartsSpec.IndPartsProg2
import ConAgua.Arena.IndPosSpec.DecNHFields
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.IndPosSpec.Rx
import ConAgua.Arena.IndPosSpec.SgGoW
import ConAgua.Arena.IndPosSpec.SnocWStage
import Std.Tactic.BVDecide.Normalize.BitVec
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
public import ConAgua.Arena.IndPosSpec.UCtx
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.RecGen

@[expose] public section

/-!
# ClassSeeds: `ConRon.Arena.classSeeds`

The refinement theorems `classSeeds_refines` and the lemmas only they use.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Pieces -/

/-- A class decoded below the tops: its first four words are a nest key. -/
theorem decTM_decNK {m : Mem} {q : Nat} {tm : TargetMajor} (h : DecB (fun m => decTM m q) m tm) :
    DecB (fun m => decNK m q) m ⟨tm.ind, tm.lvls, tm.ds⟩ := by
  have h' : decTM (truncM m) q = some tm := h
  show decNK (truncM m) q = _
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h'
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h'
  simp [decNK, h5, ha1, h4]

/-- A class's member word and its `nPc` word, read at the word address. -/
theorem decTM_words {m : Mem} {q : Word} {tm : TargetMajor} (h : DecB (fun m => decTM m q.toNat) m tm) :
    ∃ k, rdW (m.arr64 IW) (q + 8) = UInt64.ofNat k ∧ k < 2 ^ 64 ∧ tm.member = decON k ∧
      (rdW (m.arr64 IW) (q + 4)).toNat = tm.nPc := by
  have h' : decTM (truncM m) q.toNat = some tm := h
  obtain ⟨k, hk, hmem⟩ := decTM_member h'
  have h'' := h'
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h''
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h''
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨r8, hk8, -⟩ := partsIwRd hk (w := q + 8) (by
    have := partsIwLt hk
    exact word_add_toNat (by rw [show (8 : Word).toNat = 8 from rfl]; omega))
  obtain ⟨r4, hk4, -⟩ := partsIwRd h3 (w := q + 4) (by
    have := partsIwLt h3
    exact word_add_toNat (by rw [show (4 : Word).toNat = 4 from rfl]; omega))
  exact ⟨k, r8, hk8, hmem, by rw [r4, UInt64.toNat_ofNat_of_lt' hk4]⟩

section sgw
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **The seed's key slice lies below the top** (the fresh parameter slice, `NKSl`). -/
theorem sgW_nksl (k : Nat)
    (m m' : Mem) (a : AState) (ctx hO hL ind us dO dL nPc : Word) (r : List Word) (c : NestCtx)
    (holes ds : List EIdx) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (h : sgW k m ctx hO hL ind us dO dL nPc = some (r, m')) (hS : StageR vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hb : c.nP + c.names.length < 2 ^ 64) (hho : decHL m hO.toNat hL.toNat = some holes)
    (hhob : hO.toNat + hL.toNat ≤ iwTop m) (hds : decHL m dO.toNat dL.toNat = some ds)
    (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop m) (hR : RfInv m M G g) (hP : PosMR m) :
    NKSl m' (r.headD 0) := by
  sorry

end sgw

theorem SdRes.grow {m m' : Mem} {o l : Word} {seeds : List (NestKey × Nat)} (h : SdRes m o l seeds)
    (hg : IWGrow m m') (htop : iwTop m < 2 ^ 64) : SdRes m' o l seeds := by
  obtain ⟨h1, h2, ⟨ps, hps⟩, h4⟩ := h
  exact ⟨Nat.le_trans h1 hg.iw, h2, ⟨ps, by rw [decNL_grow hg h1]; exact hps⟩, h4.grow hg htop⟩

theorem SdRes.nil (m : Mem) : SdRes m 0 0 [] :=
  ⟨by simp, by simp, ⟨[], by simp [decNL]⟩, fun i hi => by simp at hi⟩

theorem NKSl.grow' {m m' : Mem} {key : Word} {nk : NestKey} (h : NKSl m key)
    (hk : DecB (fun m => decNK m key.toNat) m nk) (hg : IWGrow m m') (htop : iwTop m < 2 ^ 64) :
    NKSl m' key := by
  have hk4 := (pos2_nk_fields hk htop).2.2.2.2.2.2
  have e2 := pos2_key_rd hg htop hk4 (j := 2) (by omega)
  have e3 := pos2_key_rd hg htop hk4 (j := 3) (by omega)
  simp only [NKSl] at h ⊢
  rw [show (key + 2 : Word) = key + UInt64.ofNat 2 from rfl, show (key + 3 : Word) = key + UInt64.ofNat 3 from rfl,
    e2, e3]
  exact Nat.le_trans h hg.iw

/-- **`sl_cons` of a seed record onto the seeds' slice.** -/
theorem sdCons {p : Prog} (hP : KeysProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {m m' : Mem} {x o l : Word} {r : List Word} {seeds : List (NestKey × Nat)}
    {sd : NestKey × Nat} {key nPc : Word}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) (hS : StageR vis fe m a)
    (hsd : SdRes m o l seeds) (hx1 : x.toNat + 1 < iwTop m) (hx0 : (m.arr64 IW)[x.toNat]? = some key)
    (hxk : (m.arr64 IW)[x.toNat + 1]? = some nPc) (hk : DecB (fun m => decNK m key.toNat) m sd.1)
    (hksl : NKSl m key) (hn : nPc.toNat = sd.2) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ SdRes m' (r.headD 0) (r.tail.headD 0) (sd :: seeds) ∧
      MFr [] [] m m' := by
  sorry

/-! ## `class_seeds` -/

l_model csd_spec (p : Prog) (hp : p.lookup "class_seeds" = some classSeedsL)
  fns [hp ↦ csdW]
  specs [callW_spec p n "nest_seed_of", callW_spec p n "rec2", callW_spec p n "sl_cons"]
  grind [arena_grind] finish [rdW_eq] gen 40 instances 20000

/-- The lookups of `class_seeds`. -/
structure SdProg (p : Prog) : Prop extends KeysProg p where
  sg : SgLook p
  sds : p.lookup "class_seeds" = some classSeedsL

/-- **`nest_seed_of`'s run simulates `nestSeedOf`** at a class's words. -/
theorem sgCall_sim {p : Prog} (L : SgLook p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    (n : Nat) {m : Mem} {a : AState} {ctx hO hL q : Word} {c : NestCtx} {holes : List EIdx} {tm : TargetMajor}
    (hS : StageR vis fe m a) (hU : UCtx dn vis fe m ctx c) (hhi : c.hiAt 0 < 2 ^ 64)
    (hho : decHL m hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop m)
    (hdt : DecB (fun m => decTM m q.toNat) m tm) (hP : PosMR m) :
    Sim (callW p n "nest_seed_of" [ctx, hO, hL, rdW (m.arr64 IW) q, rdW (m.arr64 IW) (q + 1),
        rdW (m.arr64 IW) (q + 2), rdW (m.arr64 IW) (q + 3), rdW (m.arr64 IW) (q + 4)] m)
      (ConRon.Arena.nestSeedOf c holes tm.ind tm.lvls tm.ds tm.nPc) a
      (fun r x m' a' => DecB (fun m => decNK m (r.headD 0).toNat) m' x.1 ∧ NKSl m' (r.headD 0) ∧
        (r.tail.headD 0).toNat = x.2 ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧ PosMR m') := by
  sorry

/-- **`class_seeds`' model simulates `classSeeds`**: the classes a slice of records decoded below
the tops, the walk's context as `nestRoot` takes it. -/
theorem csdW_sim {p : Prog} (hP : SdProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (ctx hO hL : Word) (c : NestCtx) (holes : List EIdx) (hhi : c.hiAt 0 < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml : Word) (ms : List TargetMajor),
    StageR vis fe m a → UCtx dn vis fe m ctx c → decHL m hO.toNat hL.toNat = some holes →
    hO.toNat + hL.toNat ≤ iwTop m → PSlR decTM ms mo ml m → PosMR m →
    Sim (csdW p n m ctx hO hL mo ml) (ConRon.Arena.classSeeds c holes ms) a
      (fun r x m' a' => StageR vis fe m' a' ∧ IWGrow m m' ∧ SdRes m' (r.headD 0) (r.tail.headD 0) x ∧
        PosMR m') := by
  sorry

/-- **`class_seeds` refines `classSeeds`** (through the stubs below `nest_seed_of`): the classes a
slice of `TargetMajor` records decoded below the tops, the walk's context `UCtx`, the holes a slice
below the top, the walk memos well formed (`PosMR`); the seeds as `nestSeeds_refines` takes them
(`SdRes`: `SeedsAt`, the length, the slice below the top). -/
@[refines ConRon.Arena.classSeeds]
theorem classSeeds_refines {p : Prog} (hP : SdProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (ctx hO hL mo ml : Word) (c : NestCtx)
    (holes : List EIdx) (ms : List TargetMajor) (hS : StageR vis fe s₀.mem a₀)
    (hU : UCtx dn vis fe s₀.mem ctx c) (hhi : c.hiAt 0 < 2 ^ 64)
    (hho : decHL s₀.mem hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop s₀.mem)
    (hms : PSlR decTM ms mo ml s₀.mem) (hPm : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_seeds" [ctx, hO, hL, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classSeeds c holes ms) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.classSeeds c holes ms) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      SdRes s'.mem (r.headD 0) (r.tail.headD 0) (AM.res (ConRon.Arena.classSeeds c holes ms) a₀) ∧
      PosMR s'.mem; ⊤⦄ :=
  triple_post (csd_spec p hP.sds n s₀ ctx hO hL mo ml) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (csdW_sim hP dn vis fe ctx hO hL c holes hhi n _ a₀ mo ml ms hS hU hho hhob hms hPm) hm
    ⟨hl, hok, hQ⟩

end L.Ind
