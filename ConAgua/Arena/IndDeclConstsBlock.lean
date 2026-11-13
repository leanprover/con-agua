module

public import ConAgua.Arena.IndDeclConstsRecs
public import ConAgua.Arena.IndInstallSpec.BlockRawRec
import ConAgua.Arena.IndInstallSpec.PartsAt
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts

import ConAgua.L.ModelGen

@[expose] public section

/-!
# A declaration's constants: a block's (lane `ronsync2`, stage 3)

`block_constants(p)` refines con-ron's `blockConstants` (`Arena/Install.lean`): `block_is_rec`
(`blockIsRec_refines`), the formers (`bfW_ok`), the constructors (`dbctW_ok`), the recursors
(`brsW_ok`), appended (`sl_append`, `appendW_ci`) into an `IW` slice of `EREC` constant records.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `block_constants`. -/
structure BlockProg (p : Prog) : Prop extends RecsProg p where
  ma : MaProg p
  memberNamesCopy : p.lookup "member_names_copy" = some memberNamesCopy
  pdma : p.lookup "pi_doms_mention_any" = some piDomsMentionAny
  birm : p.lookup "block_is_rec_member" = some blockIsRecMember
  birg : p.lookup "block_is_rec_go" = some blockIsRecGo
  bir : p.lookup "block_is_rec" = some blockIsRec
  bk : p.lookup "block_constants" = some blockConstants

/-! ## `block_constants` -/

/-- **The model of `block_constants(p)`** at exec fuel `n`. -/
l_model bk_spec (p : Prog) (hp : p.lookup "block_constants" = some blockConstants)
  fns [hp ↦ bkW list]
  specs [callW_spec p n "block_is_rec", callW_spec p n "block_formers", callW_spec p n "block_ctors",
    callW_spec p n "block_recs", callW_spec p n "sl_append"]
  grind [arena_grind]

/-- **`block_constants` refines `blockConstants`**: the formers (at `block_is_rec`), the
constructors and the recursors, an `IW` slice of `EREC` constant records below the pool's top. -/
theorem bkW_ok {p : Prog} (hP : BlockProg p) {vis : Word} {fe : IFEnv} {n : Nat} {m m' : Mem}
    {a : AState} {pp : Word} {bs : BlockShape} {r : List Word} {mp : Std.HashMap EIdx Bool}
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hmp : maMR m mp) (hrl : ReadLCOK a) (hsd : SortsDen a) (h : bkW p n m pp = some (r, m')) :
    ∃ cis a', (ConRon.Arena.blockConstants bs).run a = .ok (cis, a') ∧
      decPL m' (decCI (erecP m')) (r.headD 0).toNat (r.tail.headD 0).toNat = some cis ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ StageR vis fe m' a' ∧ IWGrow m m' := by
  rcases n with _ | n
  · simp [bkW] at h
  rw [bkW.arm1] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (by simp [bkW.k_block_is_rec.none])
  rw [bkW.k_block_is_rec.arm1] at h
  rcases n with _ | n
  · exact (callW_zero_false h1).elim
  obtain ⟨s1, rfl, -, hok, hst, hr1, -, hS1, hg1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockIsRec_refines p hP.ma hP.alloc hP.memberNamesCopy hP.names hP.pdma hP.birm hP.birg hP.bir n
      ⟨m, Locals.init []⟩ a vis fe pp bs mp hS hq hsrc hmp) h1
  have hrunb := AM.run_of_ok _ _ hok
  rw [hst] at hrunb
  generalize hb : AM.res (ConRon.Arena.blockIsRec bs) a = b at hrunb hr1
  have hbw : (r1.headD 0 != 0) = b := by subst hr1; cases b <;> rfl
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hq hsrc
  -- the formers
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (by simp [bkW.k_block_formers.none])
  rw [bkW.k_block_formers.arm1] at h
  obtain ⟨s2, rfl, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (dbf_spec p hP.bf (n + 1) _ pp (r1.headD 0)) h2
  obtain ⟨L2, a2, hrun2, hd2, hb2, hS2, hg2, -, -⟩ := bfW_ok hP.toFormersProg hbw hS1 hrl hsd
    (hq.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hW2
  have hg02 := hg1.trans hg2
  -- the constructors
  obtain ⟨⟨r3, m3⟩, h3, h⟩ := of_K h (by simp [bkW.k_block_ctors.none])
  rw [bkW.k_block_ctors.arm1] at h
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (dbct_spec p hP.bc (n + 1) _ pp) h3
  obtain ⟨hd3, hb3, hS3, hg3⟩ := dbctW_ok hP.toDcCtorsProg hS2 (hq.grow (decBS_mono _) hg02)
    (partsHsrc_grow hg02 hq9 hsrc) hW3
  have hg03 := hg02.trans hg3
  -- the recursors
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨-, hrecs, -⟩ := decBS_some hqt
  obtain ⟨o, l, ho, hl, hdr, hob⟩ := partsAt decRS_mono hrecs
  obtain ⟨hoW, ho2⟩ := iwRd (o := pp) (w := 2) (by simpa using ho)
  obtain ⟨hlW, hl3⟩ := iwRd (o := pp) (w := 3) (by simpa [Nat.add_assoc] using hl)
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have e2 : rdW (s3.mem.arr64 IW) (pp + 2) = o := by
    rw [rdW_iw_grow hg03 (by rw [UInt64.toNat_add]; simp at ho2 ⊢; omega)]; exact UInt64.toNat_inj.mp hoW
  have e3 : rdW (s3.mem.arr64 IW) (pp + 3) = l := by
    rw [rdW_iw_grow hg03 (by rw [UInt64.toNat_add]; simp at hl3 ⊢; omega)]; exact UInt64.toNat_inj.mp hlW
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (by simp [bkW.k_block_recs.none])
  rw [e2, e3] at h4
  rw [bkW.k_block_recs.arm1] at h
  obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (dbrs_spec hP.toRecsProg (n + 1) _ pp o l) h4
  obtain ⟨cis, a4, hrun4, hd4, hb4, hS4, hg4⟩ := brsW_ok hP.toRecsProg pp bs vis fe (n + 1) _ _ a2 o l bs.recs _
    hS3 (hq.grow (decBS_mono _) hg03) (PSlR0.grow decRS_mono ⟨hdr, hob⟩ hg03) hW4
  -- the appends
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h (by simp [bkW.k_sl_append.none])
  rw [bkW.k_sl_append.arm1] at h
  obtain ⟨s5, rfl, -, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (slAppend_specW p hP.alloc hP.iwCopy hP.slAppend (n + 1) _ _ _ _ _) h5
  have hg24 := hg3.trans hg4
  have hb2' : (r2.headD 0).toNat + (r2.tail.headD 0).toNat ≤ iwTop s4.mem := by have := hg24.iw; omega
  have hb3' : (r3.headD 0).toNat + (r3.tail.headD 0).toNat ≤ iwTop s4.mem := by have := hg4.iw; omega
  obtain ⟨hd5, hb5, hS5, hg5⟩ := appendW_ci hW5 hS4 hb2' hb3'
    (decPL_ci_grow hg24 hb2 hd2) (decPL_ci_grow hg4 hb3 hd3)
  obtain ⟨⟨r6, m6⟩, h6, h⟩ := of_K h (by simp [bkW.k_sl_append_2.none])
  rw [bkW.k_sl_append_2.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨s6, rfl, -, hW6⟩ := triple_of_callW (s₀ := ⟨s5.mem, Locals.init []⟩)
    (slAppend_specW p hP.alloc hP.iwCopy hP.slAppend (n + 1) _ _ _ _ _) h6
  have hb4' : (r4.headD 0).toNat + (r4.tail.headD 0).toNat ≤ iwTop s5.mem := Nat.le_trans hb4 hg5.iw
  obtain ⟨hd6, hb6, hS6, hg6⟩ := appendW_ci hW6 hS5 (Nat.le_of_eq hb5) hb4'
    hd5 (decPL_ci_grow hg5 hb4 hd4)
  refine ⟨L2 ++ ConRon.Arena.blockCtors bs ++ cis, a4, ?_, by simpa using hd6, by simp only [List.headD_cons, List.tail_cons]; omega, hS6,
    hg03.trans (hg4.trans (hg5.trans hg6))⟩
  simp only [ConRon.Arena.blockConstants, StateT.run_bind, hrunb, except_ok_bind, hrun2, hrun4]
  rfl

end L.Ind

end
