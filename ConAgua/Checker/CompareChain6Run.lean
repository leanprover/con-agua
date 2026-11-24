module

public import ConAgua.Checker.CompareChain6B
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
import ConAgua.Checker.CheckARun
public import ConAgua.Checker.CmpStashFrame
import ConAgua.L.Blocks
meta import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgTac
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# Mode `6` in L (lane compare)

`checkC3_run`: a run of `check` with the mode word `6` from a memory that agrees with the
solution's index build's but in `OUT` ends, on a return, in the frozen buffer's memory
(`par_compact(0)`) after the challenge's index build (`G6`) and the flag `CTL[224] := 1`, and
returns `2^63 + c` (`c` the challenge's side records' count).
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

theorem StageSpecC.mono {p : Prog} {f : FnName} {Pre Pre' Post Post' : Word → Mem → Prop}
    (h : StageSpecC p f Pre Post) (h1 : ∀ c m, Pre' c m → Pre c m) (h2 : ∀ c m, Post c m → Post' c m) :
    StageSpecC p f Pre' Post' := fun n hn s₀ c =>
  triple_post (h n hn s₀ c) fun _ _ ⟨hl, hP⟩ => ⟨hl, fun hp => h2 _ _ (hP (h1 _ _ hp))⟩

set_option experimental.vcgen true in
/-- **`check`'s dispatch to modes `6` and `7`**: with the mode word `6` (resp. `7`), `check` is
`check_c3(0)` (resp. `check_c3(1)`). -/
theorem check_dispatch67 {p : Prog} (hp : p.lookup "check" = some checkL) (n : Nat) (s₀ : St)
    (md k : Word) (hmk : (md = 6 ∧ k = 0) ∨ (md = 7 ∧ k = 1)) (P : Word → Mem → Prop)
    (hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_c3" [k]
      ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check" []
    ⦃fun r s' => s₀.mem.glob MODE = md → P (r.headD 0) s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkL]
  rcases hmk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hC ·),
      (L.invoke_loc p (exec p n) "check_a" [·] ·), (L.invoke_loc p (exec p n) "check_bs" [] ·), (L.invoke_loc p (exec p n) "check_bc" [] ·), (L.invoke_loc p (exec p n) "check_b" [] ·),
      (L.invoke_loc p (exec p n) "check_c1" [] ·), (L.invoke_loc p (exec p n) "check_c2" [] ·),
      (L.invoke_loc p (exec p n) "check_c3" [1] ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc] at *)
    all_goals grind [lang_grind]
  · vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hC ·),
      (L.invoke_loc p (exec p n) "check_a" [·] ·), (L.invoke_loc p (exec p n) "check_bs" [] ·), (L.invoke_loc p (exec p n) "check_bc" [] ·), (L.invoke_loc p (exec p n) "check_b" [] ·),
      (L.invoke_loc p (exec p n) "check_c1" [] ·), (L.invoke_loc p (exec p n) "check_c2" [] ·),
      (L.invoke_loc p (exec p n) "check_c3" [0] ·)]
    all_goals (try simp only [Sig.retVal, Sig.retOr, L.St.setLoc_mem, List.headD_cons,
      St.setLocs_cons, St.setLocs_nil, St.setLoc_loc] at *)
    all_goals grind [lang_grind]

set_option maxRecDepth 100000 in
/-- The compared run's extra image functions in the checker's program. -/
theorem checkerProg_fzs : ∀ x ∈ fzsImgs, checkerProg.lookup (fzsName x.1) = some (fzsF x.1) := by
  intro x hx
  have h1 : x.1 ∈ [60, 61, 62] := by
    rw [← (by decide : fzsImgs.map (·.1) = [60, 61, 62])]; exact List.mem_map_of_mem hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
  rcases h1 with h | h | h <;> rw [h]
  · show checkerProg.lookup "fzs_60" = some (fzsF 60); chk_lk
  · show checkerProg.lookup "fzs_61" = some (fzsF 61); chk_lk
  · show checkerProg.lookup "fzs_62" = some (fzsF 62); chk_lk

/-- **Mode `6`'s end** before `par_compact(0)`: the challenge's index build (`G6`), then the flag and the extent words (`cmp_ext`);
the solution's stash (`cmp_sstash`) kept (`CsStash`). -/
def F6 {bC bS : ByteArray} (PS : PhaseS bC bS) (m : Mem) (c : Word) (m9 : Mem) : Prop :=
  ∃ m6, G6 PS m c m6 ∧ m9 = cmpExtM (m6.set64 CTL 224 1) ∧ CsStash m m9

/-- **The solution's stash in mode `6`'s frozen memory.** -/
theorem F6.csStash {bC bS : ByteArray} {PS : PhaseS bC bS} {m : Mem} {c : Word} {m9 : Mem}
    (h : F6 PS m c m9) : CsStash m m9 := by
  obtain ⟨_, _, _, h⟩ := h; exact h

/-- **A stage of mode `6` keeps the solution's stash** (`checkerProg_ssW`). -/
theorem StageSpecC.keepS {f : FnName} {Pre Post : Word → Mem → Prop}
    (h : StageSpecC checkerProg f Pre Post) (hf : f ∈ c3StageFns) (m : Mem) :
    StageSpecC checkerProg f (fun c x => Pre c x ∧ CsStash m x) (fun c x => Post c x ∧ CsStash m x) := by
  intro n hn s₀ c
  exact triple_post (L.Arena.triple_and (h n hn s₀ c) (invoke_memFrame checkerProg_ssW n hf [c] s₀))
    fun _ _ ⟨⟨hl, hP⟩, hfr, _⟩ => ⟨hl, fun ⟨h1, h2⟩ => ⟨hP h1, h2.frame hfr⟩⟩

theorem StageSpec.keepS {f : FnName} {Pre : Mem → Prop} {Post : List Word → Mem → Prop}
    (h : StageSpec checkerProg f Pre Post) (hf : f ∈ c3StageFns) (m : Mem) :
    StageSpec checkerProg f (fun x => Pre x ∧ CsStash m x) (fun r x => Post r x ∧ CsStash m x) := by
  intro n hn s₀
  exact triple_post (L.Arena.triple_and (h n hn s₀) (invoke_memFrame checkerProg_ssW n hf [] s₀))
    fun _ _ ⟨⟨hl, hP⟩, hfr, _⟩ => ⟨hl, fun ⟨h1, h2⟩ => ⟨hP h1, h2.frame hfr⟩⟩

/-- **Mode `6` in L**: after the solution's index build (`FoldOn`, the challenge's records
`Stash`, `Keep6`), a run of `check` from a memory `M` that agrees with it but in `OUT`, with the
mode word `6`, that returns, ends in the frozen buffer's memory of a memory `F6 c`, and returns
`2^63 + c`. -/
theorem checkC3_run {bC bS pb : ByteArray} {sz : TieredArray → Nat} (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) (hst : Stash m PS.pre PS.rC)
    (hk6 : Keep6 m PS.pre) (hsz : ∀ s, sz s < 2 ^ 64) (hpb : pb.size < 2 ^ 63)
    (hsz6 : ∀ g ≤ 2, sz (sixArr g) = sz (eixArr g) ∧ sz (stxArr g) = sz (tixArr g))
    {M : Mem} (hO : OutEq m M) (md k : Word) (hmk : (md = 6 ∧ k = 0) ∨ (md = 7 ∧ k = 1))
    (hmode : M.glob MODE = md)
    (N : Nat) (hN : N < 2 ^ 62) (rs : List Word) (m' : Mem)
    (hrun : L.run checkerProg N "check" [] M = .ok (rs, m')) :
    ∃ c, PostC3 k (F6 PS m c) m' ∧ rs.headD 0 = (9223372036854775808 : Word) + c := by
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hc3 : checkerProg.lookup "check_c3" = some checkC3L := by chk_lk
  have hpc : checkerProg.lookup "par_compact" = some parCompactL := by chk_lk
  let B : Mem → Prop := fun x => x.bytes = m.bytes
  have hB : ∀ x y, L.Keep x y → B x → B y := fun x y hk hx => hk.1.trans hx
  have hpD : (rdW (m.arr64 L.Front.DLP) 0).toNat + 1 < 2 ^ 63 := by
    have := hF.build.decls.ptop; have := hF.build.decls.psize
    simp only [L.Arena.rdW, UInt64.toNat_zero]; omega
  let S : Mem → Prop := CsStash m
  have h0 : StageSpec checkerProg "cmp_sstash" (fun x => OutEq m x ∧ B x)
      (fun _ x => (OutEq m x ∧ B x) ∧ S x) :=
    fun n _ s₀ => triple_post (cmpSStash_spec checkerProg (by chk_lk) n s₀) fun _ _ h =>
      ⟨h.1, fun hp => by
        rw [h.2.2]
        exact ⟨⟨hp.1.sstash, by
          show (sstashM s₀.mem).bytes = m.bytes
          simp only [sstashM, Mem.copy64_bytes]; exact hp.2⟩, csStash_sstash hp.1 h.2.1 hpD⟩⟩
  have hfs := checkerProg_fzs
  have h1 := (((moveStep6 (PS := PS) (m₇ := m₇) hF hsz6).keepB B hB).keepS (by decide) m).mono
    (Pre' := fun c x => ((OutEq m x ∧ B x) ∧ S x) ∧ CntAt c x) (Post' := fun _ x => (Q61 PS m x ∧ B x) ∧ S x)
    (fun _ _ ⟨⟨⟨a, b⟩, s⟩, c⟩ => ⟨⟨⟨a, c⟩, b⟩, s⟩) (fun _ _ h => h)
  have h2 := ((restoreStep6 (PS := PS) (m := m)).keepB B hB).keepS (by decide) m
  have h3 := ((prepStep6 hF hst hk6).keepB B hB).keepS (by decide) m
  have h4 := (((sideStep6 hF hst hk6).keepB B hB).keepS (by decide) m).mono
    (Pre' := fun c x => ((Q63 PS m x ∧ B x) ∧ S x) ∧ CntAt c x) (Post' := fun c x => (Q64 PS m c x ∧ B x) ∧ S x)
    (fun _ _ ⟨⟨⟨a, b⟩, s⟩, c⟩ => ⟨⟨⟨a, c⟩, b⟩, s⟩) (fun _ _ h => h)
  have h5 := ((matesStep6 hF).keepB B hB).keepS (by decide) m
  have h6 := (buildStep6 hF hst hk6 hsz hpb).keepS (by decide) m
  cases N with
  | zero =>
    exfalso
    refine run_post (Q := fun _ _ => False) hrun ?_
    rw [invoke_eq _ hlc]
    simp only [callFn]
    vcgen [exec] <;> grind
  | succ n =>
    have hn : n ≤ 2 ^ 62 := by omega
    let s₀ : St := { mem := M, loc := Locals.init [] }
    let P : Word → Mem → Prop := fun x m'' => ∃ c, PostC3 k (F6 PS m c) m'' ∧ x = 9223372036854775808 + c
    have hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke checkerProg (exec checkerProg n) "check_c3" [k]
        ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄ := fun s₁ =>
      triple_post (checkC3_of_stages hc3 hpc checkerProg_fz (by chk_lk) hfs (by chk_lk) h0 h1 h2 h3 h4 h5 h6
        (F := F6 PS m) (fun c x hx => ⟨x, hx.1, rfl, (((hx.2.setCtl 224 1).setCtl 229 1).setCtl 230 _).setCtl 231 _⟩) k n hn s₁)
        fun _ _ h e => h (by rw [e]; exact ⟨hO, hO.bytes⟩)
    exact run_post (Q := fun x m'' => s₀.mem.glob MODE = md → P (x.headD 0) m'') hrun
      (check_dispatch67 hlc n s₀ md k hmk P hC) hmode

end L.Checker
