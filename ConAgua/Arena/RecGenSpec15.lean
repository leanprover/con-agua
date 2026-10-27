import ConAgua.Arena.RecGenSpec14
import ConAgua.Arena.IndPos2SpecV
import ConAgua.Arena.IndPosSpec7

/-!
# `classSeeds` (lane `indproofs3`, helper `indproofs3-pos-cls`)

`class_seeds(ctx, holes, ms)`: every outside class of `ms` through `nest_seed_of`, each seed a
fresh `[key, nPc]` record consed onto the rest's slice (D18). The result is stated as
`nestSeeds_refines`' input (`SeedsAt`), so `check_block_pass` chains the two.
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
    (h : sgW k m ctx hO hL ind us dO dL nPc = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hb : c.nP + c.names.length < 2 ^ 64) (hho : decHL m hO.toNat hL.toNat = some holes)
    (hhob : hO.toNat + hL.toNat ≤ iwTop m) (hds : decHL m dO.toNat dL.toNat = some ds)
    (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop m) (hR : RfInv m M G g) (hP : PosMR m) :
    NKSl m' (r.headD 0) := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, -, hpa, hpa', -, -, -, -, -, h11⟩ := ctx_fields hc hin htop
  have hpsum : (rdW (m.arr64 IW) (ctx + 7)).toNat + (rdW (m.arr64 IW) (ctx + 8)).toNat ≤ iwTop m := by
    obtain ⟨-, -, -, -, hpm, -⟩ := decCtx_some hc
    obtain ⟨o, l, ho, hl, -⟩ := decAt_some hpm
    rw [rd_iwN (m := m) (p := ctx) (i := 7) (by simpa using ho) (by simp; omega),
      rd_iwN (m := m) (p := ctx) (i := 8) (by simpa using hl) (by simp; omega)]
    exact hsl 7 (by omega) o l ho hl
  unfold sgW at h
  obtain ⟨⟨f, m1⟩, hr1, h⟩ := of_K h rfl
  simp only [sgA] at h
  obtain ⟨hS1, hg1, hf1, ht1, hget1⟩ := posRecW_stage hr1 hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht1
  have g0 := iwN_of_get (by simpa using hget1 0 (by simp))
  have g1 := iwN_of_get (by simpa using hget1 1 (by simp))
  have g2 := iwN_of_get (by simpa using hget1 2 (by simp))
  have g3 := iwN_of_get (by simpa using hget1 3 (by simp))
  have g4 := iwN_of_get (by simpa using hget1 4 (by simp))
  have hfm : FMOk m1 f.toNat (.keyMap c.params holes) :=
    ⟨by simpa using g0, by omega, ⟨_, _, g1, g2, by rw [decHL_grow hg1 hpsum]; exact hpa, by have := hg1.1; omega⟩,
      ⟨_, _, g3, g4, by rw [decHL_grow hg1 hhob]; exact hho, by have := hg1.1; omega⟩⟩
  obtain ⟨ec1, hci1⟩ := hin.grow hg1
  have hsl1 := hsl.grow hin hg1
  have hR1 := hR.frame (posRecW_fr hr1)
  obtain ⟨⟨q, m2⟩, hal, h⟩ := of_K h rfl
  simp only [sgB] at h
  obtain ⟨hS2, hg2, hqd, hroom, htop2⟩ := hS1.alloc hal
  have hqt : q.toNat = iwTop m1 := by simp only [iwTop, hqd]
  rcases hgo : sgGoW k m2 ctx f dO dL q 0 with _ | m3
  · rw [hgo] at h; simp at h
  rw [hgo] at h
  simp only at h
  obtain ⟨ys, a3, -, -, hS3, hg13, ht3, -, -⟩ := sgGoW_ok dn fe vis k m1 m2 m3 a ctx f
    dO dL q 0 c holes ds [] M G g hgo hS2 hg2 (by omega) (by omega) (by rw [ec1]; exact hc) hci1 hsl1 hb hfm
    (by rw [decHL_agree (RdS.of_grow hg1) hdsb]; exact hds) (fun j hj => Nat.lt_of_lt_of_le (hdsb j hj) hg1.1)
    (by simp) (by simp [decHL, hslice?]) (hR1.frame (allocW_fr hal))
    ((hP.fr (posRecW_mfr hr1)).fr (allocW_mfr hal))
  obtain ⟨⟨key, m4⟩, hr4, h⟩ := of_K h rfl
  simp only [sgC, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS4, hg4, hk4, ht4, hget4⟩ := posRecW_stage hr4 hS3 (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have htop4 : iwTop m4 < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  have r2 : rdW (m4.arr64 IW) (key + 2) = q := by
    have := hget4 2 (by simp)
    have e : (key + 2).toNat = key.toNat + 2 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; simp at this; rw [this]; rfl
  have r3 : rdW (m4.arr64 IW) (key + 3) = dL := by
    have := hget4 3 (by simp)
    have e : (key + 3).toNat = key.toNat + 3 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; simp at this; rw [this]; rfl
  simp only [NKSl, List.headD_cons]
  rw [r2, r3]
  have := hg4.1; omega

end sgw

/-! ## The seeds' slice -/

theorem decNL_at {m : Mem} {o l : Nat} {xs : List Nat} (h : decNL m o l = some xs) (j : Nat) (hj : j < l) :
    iwN m (o + j) = some (xs[j]'(by rw [decNL_length m h]; exact hj)) := by
  have := mapM_opt_get (fun j => iwN m (o + j)) (List.range l) xs h j (by simpa using hj)
  simpa using this

/-- What `class_seeds` returns: `nestSeeds`' input slice. -/
def SdRes (m : Mem) (o l : Word) (seeds : List (NestKey × Nat)) : Prop :=
  o.toNat + l.toNat ≤ iwTop m ∧ l.toNat = seeds.length ∧
    (∃ ps, decNL m o.toNat l.toNat = some ps) ∧ SeedsAt m o.toNat seeds

theorem SdRes.grow {m m' : Mem} {o l : Word} {seeds : List (NestKey × Nat)} (h : SdRes m o l seeds)
    (hg : IWGrow m m') (htop : iwTop m < 2 ^ 64) : SdRes m' o l seeds := by
  obtain ⟨h1, h2, ⟨ps, hps⟩, h4⟩ := h
  exact ⟨Nat.le_trans h1 hg.1, h2, ⟨ps, by rw [decNL_grow hg h1]; exact hps⟩, h4.grow hg htop⟩

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
  exact Nat.le_trans h hg.1

/-- **`sl_cons` of a seed record onto the seeds' slice.** -/
theorem sdCons {p : Prog} (hP : KeysProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {m m' : Mem} {x o l : Word} {r : List Word} {seeds : List (NestKey × Nat)}
    {sd : NestKey × Nat} {key nPc : Word}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hsd : SdRes m o l seeds) (hx1 : x.toNat + 1 < iwTop m) (hx0 : (m.arr64 IW)[x.toNat]? = some key)
    (hxk : (m.arr64 IW)[x.toNat + 1]? = some nPc) (hk : DecB (fun m => decNK m key.toNat) m sd.1)
    (hksl : NKSl m key) (hn : nPc.toNat = sd.2) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ SdRes m' (r.headD 0) (r.tail.headD 0) (sd :: seeds) ∧
      MFr [] [] m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.rx.ha hP.copy hP.cons n _ x o l) h
  obtain ⟨hb, hlen, ⟨ps, hps⟩, hat⟩ := hsd
  obtain ⟨hS', hg, hdn, htop'⟩ := consW_stageN hW hS hb hps
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have htop1 : iwTop s'.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS'.2.1 hS'.2.2.2.1
  have hl1 : (r.tail.headD 0).toNat = l.toNat + 1 := by
    have h1 := decNL_length _ hdn; have h2 := decNL_length _ hps
    simp only [List.length_cons] at h1; omega
  refine ⟨hS', hg, ⟨Nat.le_of_eq htop', by rw [hl1, List.length_cons, hlen], ⟨_, hdn⟩, ?_⟩, consW_mfr hW⟩
  have hat' := hat.grow hg htop
  -- the words of the new slice
  have hw : ∀ j (hj : j < l.toNat + 1), ∃ w, (s'.mem.arr64 IW)[(r.headD 0).toNat + j]? = some w ∧
      w.toNat = (x.toNat :: ps)[j]'(by have := decNL_length m hps; simp; omega) := by
    intro j hj
    have := decNL_at hdn j (by omega)
    simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at this
    obtain ⟨w, hw, hwe⟩ := this
    exact ⟨w, hw, hwe⟩
  intro i hi
  rcases i with _ | i
  · obtain ⟨w, hw0, hwe⟩ := hw 0 (by omega)
    have hwx : w = x := UInt64.toNat_inj.mp (by simpa using hwe)
    rw [hwx] at hw0
    have hgt := hg.1
    have hx1' : x.toNat + 1 < iwTop s'.mem := Nat.lt_of_lt_of_le hx1 hgt
    have hb0 : (r.headD 0).toNat + 0 < iwTop s'.mem := by rw [← htop']; omega
    refine ⟨x, key, nPc, hw0, hb0, hx1', by rw [hg.2.2.1 x.toNat (Nat.lt_of_succ_lt hx1)]; exact hx0,
      by rw [hg.2.2.1 _ hx1]; exact hxk, hk.grow (decNK_mono _) hg, hksl.grow' hk hg htop, by simpa using hn⟩
  have hi' : i < l.toNat := by simp only [List.length_cons] at hi; omega
  obtain ⟨sp, key', nPc', h1, h2, rest⟩ := hat' i (by rw [← hlen]; exact hi')
  obtain ⟨w, hwi, hwe⟩ := hw (i + 1) (by omega)
  have hold := decNL_at hps i hi'
  rw [show o.toNat + i = o.toNat + i from rfl] at hold
  have hsp : (m.arr64 IW)[o.toNat + i]? = some sp := by
    rw [← hg.2.2.1 (o.toNat + i) (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi' _) hb)]; exact h1
  have e1 : sp.toNat = ps[i]'(by have := decNL_length m hps; omega) := by
    have := iwN_of_get hsp; rw [hold] at this; exact (Option.some.inj this).symm
  have : w = sp := UInt64.toNat_inj.mp (by rw [hwe, e1]; simp)
  subst this
  exact ⟨w, key', nPc', by rw [show (r.headD 0).toNat + (i + 1) = (r.headD 0).toNat + (i + 1) from rfl]; exact hwi,
    by omega, by simpa using rest⟩

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
    (hS : StageR dn vis fe m a) (hU : UCtx dn vis fe m ctx c) (hhi : c.hiAt 0 < 2 ^ 64)
    (hho : decHL m hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop m)
    (hdt : DecB (fun m => decTM m q.toNat) m tm) (hP : PosMR m) :
    Sim (callW p n "nest_seed_of" [ctx, hO, hL, rdW (m.arr64 IW) q, rdW (m.arr64 IW) (q + 1),
        rdW (m.arr64 IW) (q + 2), rdW (m.arr64 IW) (q + 3), rdW (m.arr64 IW) (q + 4)] m)
      (ConRon.Arena.nestSeedOf c holes tm.ind tm.lvls tm.ds tm.nPc) a
      (fun r x m' a' => DecB (fun m => decNK m (r.headD 0).toNat) m' x.1 ∧ NKSl m' (r.headD 0) ∧
        (r.tail.headD 0).toNat = x.2 ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m') := by
  intro r m' e
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rcases n with _ | k
  · rw [callW_zero] at e; cases e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (nestSeedOf_spec p L k _ ctx hO hL _ _ _ _ _) e
  obtain ⟨hcH, hcd, huH, hud, hds, hdsb, hk4⟩ := pos2_nk_fields (decTM_decNK hdt) htop
  obtain ⟨-, -, -, -, h4⟩ := decTM_words hdt
  have hb : c.nP + c.names.length < 2 ^ 64 := by simpa [NestCtx.hiAt] using hhi
  obtain ⟨M, G, g, hR⟩ := hP.rf
  obtain ⟨x, a', hrun, h1, h2, h3, ⟨M', G', hS', hg, -⟩, hP'⟩ := sgW_ok dn fe vis k m s'.mem a ctx hO hL _ _ _ _ _ r c
    holes tm.ds M G g hW hS hU.dec hU.inn hU.sl hb hho hhob hds hdsb hcH huH hR hP
  have hsl := sgW_nksl dn fe vis k m s'.mem a ctx hO hL _ _ _ _ _ r c holes tm.ds M G g hW hS hU.dec hU.inn hU.sl hb
    hho hhob hds hdsb hR hP
  rw [hcd, hud, h4] at hrun
  have htop' : iwTop s'.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS'.2.1 hS'.2.2.2.1
  exact ⟨x, a', hrun, decNK_decB_of_in h1 h3, hsl, h2, hS', hg, hP'⟩

/-- **`class_seeds`' model simulates `classSeeds`**: the classes a slice of records decoded below
the tops, the walk's context as `nestRoot` takes it. -/
theorem csdW_sim {p : Prog} (hP : SdProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (ctx hO hL : Word) (c : NestCtx) (holes : List EIdx) (hhi : c.hiAt 0 < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (mo ml : Word) (ms : List TargetMajor),
    StageR dn vis fe m a → UCtx dn vis fe m ctx c → decHL m hO.toNat hL.toNat = some holes →
    hO.toNat + hL.toNat ≤ iwTop m → PSlR decTM ms mo ml m → PosMR m →
    Sim (csdW p n m ctx hO hL mo ml) (ConRon.Arena.classSeeds c holes ms) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ SdRes m' (r.headD 0) (r.tail.headD 0) x ∧
        PosMR m') := by
  induction n with
  | zero => intro m a mo ml ms _ _ _ _ _ _; rw [csdW.eq_1]; exact Sim.of_none
  | succ n ih =>
  intro m a mo ml ms hS hU hho hhob hms hPm
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases hml : ml = 0
  · rw [csdW.arm1 p n m ctx hO hL mo ml hml]
    have : ms = [] := by
      have h := hms.1; simp only [DecB, hml] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hS, IWGrow.refl m, by simpa using SdRes.nil m, hPm⟩
  obtain ⟨q, tm, ms', rfl, hw, hqb, hdt, hms'⟩ := partsPSl_cons hms hml
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  rw [← hq'] at hdt
  obtain ⟨k, hk8, hkb, hmem, -⟩ := decTM_words hdt
  by_cases hk : k = 0
  · -- an outside class: its seed
    subst hk
    rw [csdW.arm3 p n m ctx hO hL mo ml hml (by rw [hw, hk8]; simp), hw]
    have hmn : tm.member = none := by rw [hmem]; rfl
    simp only [ConRon.Arena.classSeeds, hmn]
    refine Sim.bindK (K := csdW.k_nest_seed_of p n ctx hO hL mo ml) (body := fun r1 m1 => csdW.k_rec2 p n ctx hO hL mo ml
        (callW p n "rec2" [r1.headD 0, r1.tail.headD 0] m1)) (by simp [csdW.k_nest_seed_of])
        (fun r m₁ => csdW.k_nest_seed_of.arm1 p n ctx hO hL mo ml r m₁)
      (sgCall_sim hP.sg n hS hU hhi hho hhob hdt hPm) ?_
    rintro r1 sd m1 a1 ⟨hk1, hksl1, hn1, hS1, hg1, hP1⟩
    refine Sim.mstep (K := csdW.k_rec2 p n ctx hO hL mo ml) (by simp [csdW.k_rec2])
      (fun r m₁ => csdW.k_rec2.arm1 p n ctx hO hL mo ml r m₁) fun r2 m2 h2 => ?_
    obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (posRec2_specW p hP.rx.ha hP.rx.h2 n _ (r1.headD 0) (r1.tail.headD 0)) h2
    obtain ⟨hS2, hg2, hp2, ht2, hget2⟩ := posRecW_stage hW2 hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht2
    have hf2 := posRecW_mfr hW2
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    have hg12 := hg1.trans hg2
    refine Sim.bindK (K := csdW.k_class_seeds_2 p n (r2.headD 0)) (body := fun r3 m3 => csdW.k_class_seeds p (callW p n "sl_cons"
        [r2.headD 0, r3.headD 0, r3.tail.headD 0] m3)) rfl (fun _ _ => rfl)
      (ih s2.mem a1 (mo + 1) (ml - 1) ms' hS2 (hU.grow hg12) (by rw [decHL_grow hg12 hhob]; exact hho)
        (Nat.le_trans hhob hg12.1) (hms'.grow decTM_mono hg12) (hP1.fr hf2)) ?_
    rintro r3 xs m3 a3 ⟨hS3, hg3, hd3, hP3⟩
    refine Sim.mstep (K := csdW.k_class_seeds p) rfl (fun _ _ => rfl) fun r4 m4 h4 => ?_
    have htop2 : iwTop s2.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
    have g0 := hget2 0 (by simp)
    have g1 := hget2 1 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at g0 g1
    have hp2' : (r2.headD 0).toNat = iwTop m1 := hp2
    have ht2' : iwTop s2.mem = iwTop m1 + 2 := ht2
    have hg3t := hg3.1
    obtain ⟨hS4, hg4, hd4, hf4⟩ := sdCons hP.toKeysProg h4 hS3 hd3 (key := r1.headD 0) (nPc := r1.tail.headD 0)
      (sd := sd) (by omega) (by rw [hg3.2.2.1 (r2.headD 0).toNat (by omega)]; exact g0)
      (by rw [hg3.2.2.1 ((r2.headD 0).toNat + 1) (by omega)]; exact g1)
      ((hk1.grow (decNK_mono _) hg2).grow (decNK_mono _) hg3)
      ((hksl1.grow' hk1 hg2 htop1).grow' (hk1.grow (decNK_mono _) hg2) hg3 htop2) hn1
    exact Sim.ret ⟨hS4, ((hg1.trans hg2).trans hg3).trans hg4, by simpa using hd4, hP3.fr hf4⟩
  · -- a member: skipped
    rw [csdW.arm2 p n m ctx hO hL mo ml hml (by
      rw [hw, hk8]; intro e; apply hk
      have := congrArg UInt64.toNat e; rwa [UInt64.toNat_ofNat_of_lt' hkb] at this)]
    obtain ⟨t, ht⟩ : ∃ t, tm.member = some t := ⟨k - 1, by rw [hmem]; simp [decON, hk]⟩
    simp only [ConRon.Arena.classSeeds, ht]
    refine Sim.post (K := csdW.k_class_seeds p) (f := fun r => [r.headD 0, r.tail.headD 0]) rfl (fun _ _ => rfl)
      (ih m a (mo + 1) (ml - 1) ms' hS hU hho hhob hms' hPm) ?_
    rintro r x m' a' ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by simpa using h3, h4⟩

/-- **`class_seeds` refines `classSeeds`** (through the stubs below `nest_seed_of`): the classes a
slice of `TargetMajor` records decoded below the tops, the walk's context `UCtx`, the holes a slice
below the top, the walk memos well formed (`PosMR`); the seeds as `nestSeeds_refines` takes them
(`SdRes`: `SeedsAt`, the length, the slice below the top). -/
@[refines ConRon.Arena.classSeeds]
theorem classSeeds_refines {p : Prog} (hP : SdProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (ctx hO hL mo ml : Word) (c : NestCtx)
    (holes : List EIdx) (ms : List TargetMajor) (hS : StageR dn vis fe s₀.mem a₀)
    (hU : UCtx dn vis fe s₀.mem ctx c) (hhi : c.hiAt 0 < 2 ^ 64)
    (hho : decHL s₀.mem hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop s₀.mem)
    (hms : PSlR decTM ms mo ml s₀.mem) (hPm : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_seeds" [ctx, hO, hL, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classSeeds c holes ms) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classSeeds c holes ms) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      SdRes s'.mem (r.headD 0) (r.tail.headD 0) (AM.res (ConRon.Arena.classSeeds c holes ms) a₀) ∧
      PosMR s'.mem; ⊤⦄ :=
  triple_post (csd_spec p hP.sds n s₀ ctx hO hL mo ml) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (csdW_sim hP dn vis fe ctx hO hL c holes hhi n _ a₀ mo ml ms hS hU hho hhob hms hPm) hm
    ⟨hl, hok, hQ⟩

end L.Ind
