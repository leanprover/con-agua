module

public import ConAgua.Checker.CompareChain6B
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
import ConAgua.Checker.CheckARun
meta import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.LoopProgTac

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

/-- **Mode `6`'s end** before `par_compact(0)`: the challenge's index build (`G6`), then the flag. -/
def F6 {bC bS : ByteArray} (PS : PhaseS bC bS) (m : Mem) (c : Word) (m9 : Mem) : Prop :=
  ∃ m6, G6 PS m c m6 ∧ m9 = m6.set64 CTL 224 1

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
    ∃ c, PostPC k (F6 PS m c) m' ∧ rs.headD 0 = (9223372036854775808 : Word) + c := by
  have hlc : checkerProg.lookup "check" = some checkL := by chk_lk
  have hc3 : checkerProg.lookup "check_c3" = some checkC3L := by chk_lk
  have hpc : checkerProg.lookup "par_compact" = some parCompactL := by chk_lk
  let B : Mem → Prop := fun x => x.bytes = m.bytes
  have hB : ∀ x y, L.Keep x y → B x → B y := fun x y hk hx => hk.1.trans hx
  have h1 := ((moveStep6 (PS := PS) (m₇ := m₇) hF hsz6).keepB B hB).mono
    (Pre' := fun c x => (OutEq m x ∧ B x) ∧ CntAt c x) (Post' := fun _ x => Q61 PS m x ∧ B x)
    (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) (fun _ _ h => h)
  have h2 := (restoreStep6 (PS := PS) (m := m)).keepB B hB
  have h3 := (prepStep6 hF hst hk6).keepB B hB
  have h4 := ((sideStep6 hF hst hk6).keepB B hB).mono
    (Pre' := fun c x => (Q63 PS m x ∧ B x) ∧ CntAt c x) (Post' := fun c x => Q64 PS m c x ∧ B x)
    (fun _ _ ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩) (fun _ _ h => h)
  have h5 := (matesStep6 hF).keepB B hB
  have h6 := buildStep6 hF hst hk6 hsz hpb
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
    let P : Word → Mem → Prop := fun x m'' => ∃ c, PostPC k (F6 PS m c) m'' ∧ x = 9223372036854775808 + c
    have hC : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke checkerProg (exec checkerProg n) "check_c3" [k]
        ⦃fun r s' => s₁.mem = s₀.mem → P (r.headD 0) s'.mem; ⊤⦄ := fun s₁ =>
      triple_post (checkC3_of_stages hc3 hpc checkerProg_fz h1 h2 h3 h4 h5 h6
        (F := F6 PS m) (fun c x hx => ⟨x, hx, rfl⟩) k n hn s₁)
        fun _ _ h e => h (by rw [e]; exact ⟨hO, hO.bytes⟩)
    exact run_post (Q := fun x m'' => s₀.mem.glob MODE = md → P (x.headD 0) m'') hrun
      (check_dispatch67 hlc n s₀ md k hmk P hC) hmode

end L.Checker
