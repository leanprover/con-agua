module

public import ConAgua.Arena.IndT.Tail
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndStream
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndPartsSpec.BlockRecLpsOk
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndDecStab
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RefWalk

@[expose] public section

/-!
# `check_block_tail_stream` and `stream_k_check`: the unified models (lane `ronsync2`, stage 3)

`check_block_tail_stream(p, fe2b, out.off, out.len)` (`IndInstall.lean`) is `tailStreamT`
(`IndT/Tail`): `stream_k_check` and `stream_recs_check` through their calls, `block_rec_infos_tf`,
`cons_block_recs_temp`, the flushes and `gen_rec_check_pop_all` (outside the verdict closure) lifted.
The refinements (`streamKCheck`, `streamRecsCheck` and its callees in `Arena/IndStream`) are still
to write (handoff in `_tmp/ronsync2/area-ind.md`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of the stream half's models. -/
structure TsLook (p : Prog) : Prop where
  ts : p.lookup "check_block_tail_stream" = some checkBlockTailStream
  skc : p.lookup "stream_k_check" = some streamKCheckL

set_option experimental.vcgen true in
/-- **`stream_k_check`'s unified model**: `rec_k_expected` lifted. -/
l_model skcE_spec (p : Prog) (hP : TsLook p)
  fns [hP.skc ↦ skcE]
  specs [callW_spec p n "rec_k_expected"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`check_block_tail_stream`'s unified model**: the K flags and the stream's recursors through
their calls, the rest lifted. -/
l_model ctsE_spec (p : Prog) (hP : TsLook p)
  fns [hP.ts ↦ ctsE]
  specs [callW_spec p n "block_rec_infos_tf", callW_spec p n "cons_block_recs_temp",
    callW_spec p n "flush_caches", callW_spec p n "gen_rec_check_pop_all"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## `stream_k_check` -/

/-- A flag word of a record decoded below the top, read. -/
theorem iwB_trunc_rd {m : Mem} {w : Word} {k : Nat} {b : Bool}
    (h : iwB (truncM m) (w.toNat + k) = some b) : (rdW (m.arr64 IW) (w + UInt64.ofNat k) != 0) = b := by
  simp only [iwB, bool?, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  obtain ⟨hlt, hv'⟩ := truncM_iw_get hv
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hi : w.toNat + k < 2 ^ 64 := by omega
  have := iwB_rdW (m := m) (i := w.toNat + k) (b := v != 0) (by simp [iwB, bool?, hv']) hi
  have e : (UInt64.ofNat (w.toNat + k) : Word) = w + UInt64.ofNat k := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hi, UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)]
    omega
  rwa [e] at this

/-- `rec_k_expected` answers `0` or `1`. -/
theorem rkW_01 {m : Mem} {p M w : Word} (h : rkW m p M = some w) : w = 0 ∨ w = 1 := by
  unfold rkW at h
  split at h
  · exact .inl (Option.some.inj h).symm
  split at h
  · exact .inl (Option.some.inj h).symm
  obtain rfl := (Option.some.inj h).symm
  split <;> split <;> split <;> simp

/-- **`stream_k_check` refines `streamKCheck`, both outcomes**: the records' flags against
`rec_k_expected` (`rkW_ok`), the memory and the twin's state unchanged. -/
theorem skc_ref {p : Prog} (hL : CbrLook p) {G : Prop} (pp : Word) (bs : BlockShape) :
    ∀ (n : Nat) (m : Mem) (a : AState) (ro rl go gl : Word) (rcs : List RecShape)
      (gs : List (IConstantVal × TargetMajor × List EIdx)),
    DecB (fun m => decBS m pp.toNat) m bs → PSlR decRS rcs ro rl m → PSlR decRR gs go gl m →
    (m.arr64 IW).size < 2 ^ 64 →
    RefE G (skcE p n m pp ro rl go gl) (ConRon.Arena.streamKCheck bs rcs gs) a
      (fun v _ a' => a' = a ∧ v.2 = m) := by
  intro n
  induction n with
  | zero => intro m a ro rl go gl rcs gs _ _ _ _; rw [skcE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a ro rl go gl rcs gs hbs hr hg hsz
  by_cases hz : rl = 0 ∨ gl = 0
  · rw [skcE.arm1 _ _ _ _ _ _ _ _ hz]
    refine RefE.ret (y := ()) (a' := a) ?_ ⟨rfl, rfl⟩
    rcases hz with h0 | h0
    · have hlen : rcs.length = rl.toNat := decPL_length _ (show decPL (truncM m) _ _ _ = some rcs from hr.dec)
      rw [h0] at hlen
      obtain rfl : rcs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      cases gs <;> rfl
    · have hlen : gs.length = gl.toNat := decPL_length _ (show decPL (truncM m) _ _ _ = some gs from hg.dec)
      rw [h0] at hlen
      obtain rfl : gs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      cases rcs <;> rfl
  obtain ⟨hr0, hg0⟩ := not_or.mp hz
  obtain ⟨rc, rcs', rfl, hrc, hr'⟩ := PSlR.uncons hr hr0 hsz
  obtain ⟨g, gs', rfl, hgd, hg'⟩ := PSlR.uncons hg hg0 hsz
  rw [skcE.arm2 _ _ _ _ _ _ _ _ hz]
  -- the generated recursor's major
  have hgd0 : decRR (truncM m) (rdW (m.arr64 IW) go).toNat = some g := hgd
  obtain ⟨cv, M, rh⟩ := g
  simp only [decRR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hgd0
  obtain ⟨cvp, -, cv', -, mp, hmp, TM', hTM', rh', -, he⟩ := hgd0
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl, -⟩ := he
  obtain ⟨-, hmpm⟩ := rec2IwN_trunc hmp
  obtain ⟨e1, t1⟩ := rec2RdN (w := rdW (m.arr64 IW) go) (k := 1) hmpm hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at e1
  have hM : DecB (fun m => decTM m (UInt64.ofNat mp : Word).toNat) m TM' := by
    show decTM (truncM m) _ = some TM'; rw [t1]; exact hTM'
  obtain ⟨isK, hk, hkE⟩ := rkW_ok hbs hM hsz
  -- the record's flag
  have hrc0 : decRS (truncM m) (rdW (m.arr64 IW) ro).toNat = some rc := hrc
  have hK : (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 6) != 0) = rc.isK :=
    iwB_trunc_rd (k := 6) (decRS_some hrc0).2.2.2.2.2
  rw [e1]
  refine RefE.onlySim (fun _ => skcE.k_rec_k_expected.none _ _ _ _ _ _ _ _ _)
    (Q := fun r m₁ => m₁ = m ∧ r.headD 0 = isK) (fun r m₁ hc => ?_) fun r m₁ ⟨hm₁, hr⟩ => ?_
  · obtain ⟨s', hs', -, hm', hrk⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (rk_spec p hL n ⟨m, Locals.init []⟩ pp (UInt64.ofNat mp)) hc
    rw [hk] at hrk
    exact ⟨hs' ▸ hm', (Option.some.inj hrk).symm⟩
  subst m₁
  have hcond : (rc.isK == ConRon.Arena.recKExpected bs TM') = true ↔
      ((if rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 6) ≠ 0 then (1 : Word) else 0) = r.headD 0) := by
    rw [← hK, ← hkE, hr]
    rcases rkW_01 hk with rfl | rfl <;>
      by_cases hX : rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 6) = 0 <;> simp [hX]
  by_cases hkk : (if rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 6) ≠ 0 then (1 : Word) else 0) = r.headD 0
  · rw [skcE.k_rec_k_expected.arm1 _ _ _ _ _ _ _ _ _ _ hkk]
    have hc' : (rc.isK == ConRon.Arena.recKExpected bs TM') = true := hcond.mpr hkk
    have htw : ConRon.Arena.streamKCheck bs (rc :: rcs') ((cv, TM', rh) :: gs') =
        ConRon.Arena.streamKCheck bs rcs' gs' := by
      simp only [ConRon.Arena.streamKCheck, hc']; rfl
    have IH := ih m a (ro + 1) (rl - 1) (go + 1) (gl - 1) rcs' gs' hbs hr' hg' hsz
    rw [htw]
    rcases hx : skcE p n m pp (ro + 1) (rl - 1) (go + 1) (gl - 1) with e | ⟨v, m2⟩
    · rw [skcE.k_stream_k_check.none]; rw [hx] at IH; exact IH
    · rw [skcE.k_stream_k_check.arm1]; rw [hx] at IH
      obtain ⟨y, a', hrun, rfl, hv⟩ := IH
      exact RefE.ret hrun ⟨rfl, hv⟩
  · rw [skcE.k_rec_k_expected.abort1 _ _ _ _ _ _ _ _ _ _ hkk]
    have hc' : (rc.isK == ConRon.Arena.recKExpected bs TM') = false := by
      exact Bool.eq_false_iff.mpr (mt hcond.mp hkk)
    intro _
    simp only [ConRon.Arena.streamKCheck, hc']
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))

end L.Ind

end
