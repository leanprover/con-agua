import ConAgua.Arena.IndInstallSpec7
import ConAgua.Arena.RecClassSpecI
import ConAgua.Arena.IndSumSpec9
import ConAgua.Arena.IndSumSpec3
import ConAgua.Arena.RecClassSpec

/-!
# Refinements of `IndInstall`, part 8 (lane `indproofs2`, helper `install`): `checkBlockTele`

The round-3 template for this module's parents: every callee enters the word model as its run
`callW p n f args m` (so the `vcgen` spec needs no callee spec but `callW_spec`), and the
relational lemma turns each run into the twin's through the callee's own refinement triple
(`installSimCall`) or its stub contract (`installSimStub`), composed by `Sim.bindK`.

A former's constant record carries `CVExt` (rec lane's: the record and its level-parameter slice
below the record pool's top), a precondition on the member records (the twin's decoding of an
empty slice ignores its offset, so `DecB` alone does not give it); `check_sum_tele` now returns it
for its result.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Callees as runs -/

/-- **A callee's refinement triple, as a `Sim` on its run.** -/
theorem installSimCall {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName} {args : List Word}
    {m : Mem} {op : AM α} {a : AState} {Q : List Word → α → Mem → AState → Prop}
    {P : List Word → St → Prop}
    (h : ⦃fun s => s = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p n) f args ⦃fun r s' => P r s'; ⊤⦄)
    (hP : ∀ r s', P r s' → AM.ok op a ∧ Q r (AM.res op a) s'.mem (AM.st op a)) :
    Sim (callW p n f args m) op a Q := by
  intro r m' e
  obtain ⟨s', rfl, hp⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) h e
  obtain ⟨hok, hq⟩ := hP r s' hp
  exact ⟨_, _, partsRunOfOk hok, hq⟩

/-- **A stub's contract, as a `Sim` on its run.** -/
theorem installSimStub {α : Type} {p : Prog} {n : Nat} {f : FnName} {args : List Word} {m : Mem}
    {pre : Mem → AState → Prop} {op : AM α} {a : AState}
    {post : Mem → Mem → AState → List Word → α → Prop}
    (h : RelAM f args pre op post) (hpre : pre m a) :
    Sim (callW p n f args m) op a (fun r x m' a' => post m m' a' r x) := by
  intro r m' e
  obtain ⟨s', rfl, -, hs⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (stubM_spec p f n _ args) e
  exact h m s'.mem a r hs hpre

/-- A `KeepPost` stub, unpacked. -/
theorem installSimKeep {α : Type} {p : Prog} {n : Nat} {f : FnName} {args : List Word} {m : Mem}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {op : AM α} {a : AState}
    {dec : Mem → List Word → α → Prop}
    (h : RelAM f args (StageR dn vis fe) op (KeepPost dn vis fe dec)) (hS : StageR dn vis fe m a) :
    Sim (callW p n f args m) op a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ dec m' r x) :=
  installSimStub h hS

/-! ## Constant records below the tops -/

/-- A constant decoded in a memory whose record lies below the tops (`CVExt`) is decoded below
the tops. -/
theorem installCvDecB {m : Mem} {q : Nat} {cv : IConstantVal} (h : decCVp m q = some cv)
    (hx : CVExt m q) : DecB (fun m => decCVp m q) m cv := by
  obtain ⟨hq, hsl⟩ := hx
  have e : ∀ i, i < erTop m → (erA (truncM m))[i]? = (erA m)[i]? := fun i hi => truncM_er_eq hi
  show decCVp (truncM m) q = some cv
  simp only [decCVp] at h ⊢
  simp only [decCV, bind, Option.bind, pure, hlist?] at h ⊢
  have e0 : (hd? (erA (truncM m)) q : Option NIdx) = hd? (erA m) q := by simp only [hd?, e q (by omega)]
  have e1 : nat? (erA (truncM m)) (q + 1) = nat? (erA m) (q + 1) := by simp only [nat?, e (q + 1) (by omega)]
  have e2 : nat? (erA (truncM m)) (q + 1 + 1) = nat? (erA m) (q + 1 + 1) := by
    simp only [nat?, e (q + 1 + 1) (by omega)]
  have e3 : (hd? (erA (truncM m)) (q + 3) : Option EIdx) = hd? (erA m) (q + 3) := by
    simp only [hd?, e (q + 3) (by omega)]
  rw [e0, e1, e2, e3]
  cases h1 : nat? (erA m) (q + 1) with
  | none => rw [h1] at h; revert h; cases (hd? (erA m) q : Option NIdx) <;> simp
  | some lo =>
  cases h2 : nat? (erA m) (q + 1 + 1) with
  | none => rw [h1, h2] at h; revert h; cases (hd? (erA m) q : Option NIdx) <;> simp
  | some ll =>
  have hN := hsl lo ll h1 (by simpa using h2)
  have hs : (hslice? (erA (truncM m)) lo ll : Option (List NIdx)) = hslice? (erA m) lo ll := by
    simp only [hslice?]
    exact mapM_congr_of _ _ _ (fun j hj => by
      have := List.mem_range.mp hj
      simp only [hd?, e (lo + j) (by omega)])
  rw [h1, h2] at h
  simp only [hs]
  exact h

/-! ## The lookups of `check_sum_tele` -/

/-- The lookups `check_sum_tele`'s refinement takes. -/
structure CstProg (p : Prog) : Prop where
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  view : p.lookup "e_view" = some eView
  fvarFind : p.lookup "fvar_find" = some fvarFind
  fvarPush : p.lookup "fvar_push" = some fvarPush
  internFVar : p.lookup "intern_fvar" = some internFVar
  wt : p.lookup "whnf_telescope" = some whnfTelescopeL
  sortFind : p.lookup "sort_find" = some sortFind
  sortPush : p.lookup "sort_push" = some sortPush
  internSort : p.lookup "intern_sort" = some internSort
  derB : p.lookup "der_b" = some derB
  forallFind : p.lookup "forall_find" = some forallFind
  forallPush : p.lookup "forall_push" = some forallPush
  internForall : p.lookup "intern_forall" = some internForallL
  mkForall : p.lookup "mk_forall" = some mkForall
  closeTele : p.lookup "close_telescope" = some closeTelescope
  erAlloc : p.lookup "erec_alloc" = some erecAlloc
  cvNew : p.lookup "cv_new" = some cvNew
  slow : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL
  tele : p.lookup "check_sum_tele" = some checkSumTeleL
  strip : StripProg p

/-- `check_sum_tele` as a `Sim`: the constant and the start record below the tops. -/
theorem installCstSim {p : Prog} (hP : CstProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {cv k : Word} {cvv : IConstantVal}
    (hS : StageR dn vis fe m a) (hcv : decCVp m cv.toNat = some cvv) (hx : CVExt m cv.toNat) :
    Sim (callW p n "check_sum_tele" [vis, cv, k, cv] m) (checkSumTele V fe cvv k.toNat cvv) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        decCVp m' (r.headD 0).toNat = some x.1 ∧ CVExt m' (r.headD 0).toNat ∧
        H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2) :=
  installSimCall (checkSumTele_refines p hP.alloc hP.copy hP.cons hP.view hP.fvarFind hP.fvarPush
    hP.internFVar hP.wt hP.sortFind hP.sortPush hP.internSort hP.derB hP.forallFind hP.forallPush
    hP.internForall hP.mkForall hP.closeTele hP.erAlloc hP.cvNew hP.slow hP.tele hP.strip n _ a dn vis fe cv k cv
    cvv cvv hS hcv hx.1 hx.2 hcv hx.1 hx.2)
    fun _ _ ⟨_, hok, hS', hg, hd, h32, hs, hb, hsl⟩ => ⟨hok, hS', hg, hd, ⟨hb, hsl⟩, h32, hs⟩

/-- `intern_sort` as a `Sim` (master's, through its stage lemma). -/
theorem installSortSim {p : Prog} (hP : CstProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {u : Word} (hS : StageR dn vis fe m a) (hu : H u) :
    Sim (callW p n "intern_sort" [u] m) (internSortE (decI u)) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decE (r.headD 0) = x) := by
  intro r m' e
  obtain ⟨s', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSort_spec p hP.sortFind hP.sortPush hP.internSort n _ u) e
  obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS u hu hI
  exact ⟨_, a', hrun, hS', hg, rfl⟩

/-! ## `check_block_tele` -/

/-- After `intern_sort`: the result sort is the telescope's body. -/
def ibtK4 (cvTa s body : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if body = r.headD 0 then some ([cvTa, s], m) else none
/-- After `strip_pis`. -/
def ibtK3 (p : Prog) (n : Nat) (cvTa s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none
    else ibtK4 cvTa s (r.tail.tail.tail.headD 0) (callW p n "intern_sort" [s] m)
/-- After `check_sum_tele`. -/
def ibtK2 (p : Prog) (n : Nat) (k : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => ibtK3 p n (r.headD 0) (r.tail.headD 0)
      (callW p n "strip_pis" [k, rdW (m.arr64 EREC) (r.headD 0 + 3)] m)
/-- After `check_constant_val`. -/
def ibtK1 (p : Prog) (n : Nat) (vis k cvT : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ibtK2 p n k (callW p n "check_sum_tele" [vis, cvT, k, cvT] m)

/-- **The model of `check_block_tele(vis, nP, ms)`** (body fuel `n`). -/
def ibtW (p : Prog) (n : Nat) (m : Mem) (vis nP ms : Word) : Option (List Word × Mem) :=
  if nP + rdW (m.arr64 IW) (ms + 1) < nP then none
  else ibtK1 p n vis (nP + rdW (m.arr64 IW) (ms + 1)) (rdW (m.arr64 IW) ms)
    (callW p n "check_constant_val" [vis, rdW (m.arr64 IW) ms] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis k cvT cvTa s body : Word) (r : List Word)
theorem ibtK4_ok (h : body = r.headD 0) : ibtK4 cvTa s body (some (r, m)) = some ([cvTa, s], m) := by
  simp only [ibtK4]; exact if_pos h
theorem ibtK4_ne (h : ¬ body = r.headD 0) : ibtK4 cvTa s body (some (r, m)) = none := by
  simp only [ibtK4]; exact if_neg h
theorem ibtK3_none (h : r.headD 0 = 0) : ibtK3 p n cvTa s (some (r, m)) = none := by
  simp only [ibtK3]; exact if_pos h
theorem ibtK3_some (h : ¬ r.headD 0 = 0) : ibtK3 p n cvTa s (some (r, m)) =
    ibtK4 cvTa s (r.tail.tail.tail.headD 0) (callW p n "intern_sort" [s] m) := by
  simp only [ibtK3]; exact if_neg h
theorem ibtK2_some : ibtK2 p n k (some (r, m)) = ibtK3 p n (r.headD 0) (r.tail.headD 0)
    (callW p n "strip_pis" [k, rdW (m.arr64 EREC) (r.headD 0 + 3)] m) := rfl
theorem ibtK1_some : ibtK1 p n vis k cvT (some (r, m)) =
    ibtK2 p n k (callW p n "check_sum_tele" [vis, cvT, k, cvT] m) := rfl
end arms
attribute [ind_grind] ibtK4_ok ibtK4_ne ibtK3_none ibtK3_some ibtK2_some ibtK1_some

theorem ibt_spec (p : Prog) (hp : p.lookup "check_block_tele" = some checkBlockTele) (n : Nat)
    (s₀ : St) (vis nP ms : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_tele" [vis, nP, ms]
    ⦃fun r s' => LocEq s' s₀ ∧ ibtW p n s₀.mem vis nP ms = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockTele]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "check_constant_val", callW_spec p n "check_sum_tele",
      callW_spec p n "strip_pis", callW_spec p n "intern_sort"] <;>
    finish (gen := 20) [ibtW, rdW_eq]

/-- The post of `check_block_tele`: the checked former below the tops, its result sort a handle. -/
def TeleOut (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (x : IConstantVal × LIdx) (m' : Mem) (a' : AState) : Prop :=
  StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some x.1 ∧
    CVExt m' (r.headD 0).toNat ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2

/-- What a member record must satisfy: decoded below the tops, its former's constant record
below the tops (`CVExt`). -/
def MemOK (m : Mem) (q : Nat) (ms : MemberShape) : Prop :=
  DecB (fun m => decMS m q) m ms ∧ ∀ c, iwN m q = some c → CVExt m c

theorem MemOK.grow {m m' : Mem} {q : Nat} {ms : MemberShape} (h : MemOK m q ms) (hg : IWGrow m m') :
    MemOK m' q ms := by
  refine ⟨h.1.grow (decMS_mono _) hg, fun c hc => ?_⟩
  have hq : q < iwTop m := by
    have := h.1; simp only [DecB, decMS, bind, Option.bind_eq_some_iff] at this
    obtain ⟨c', hc', -⟩ := this; exact partsIwLt hc'
  rw [iwN_grow hg hq] at hc
  exact CVExt_grow hg (h.2 c hc)

/-- **`check_block_tele`'s model refines `checkBlockTele`.** -/
theorem ibtW_sim (p : Prog) (hP : CstProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {m : Mem} {a : AState} {nP ms : Word} {msh : MemberShape}
    (hS : StageR dn vis fe m a) (hms : MemOK m ms.toNat msh) :
    Sim (ibtW p n m vis nP ms) (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a
      (fun r x m' a' => TeleOut dn vis fe m r x m' a') := by
  obtain ⟨hmsB, hcx⟩ := hms
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨⟨c, hc, hcv⟩, hni, -⟩ := decMS_some (m := truncM m) hmsB
  obtain ⟨hw0, hcb, hmsl⟩ := partsIwRd hc rfl
  obtain ⟨hw1, hnb, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨-, hcN⟩ := rec2IwN_trunc hc
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hcvx : CVExt m (UInt64.ofNat c : Word).toNat := by rw [hc']; exact hcx c hcN
  have hcvm : decCVp m (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.get (OMono.decCVp _) hcv
  unfold ibtW
  rw [hw0, hw1]
  split
  · exact Sim.of_none
  rename_i hov
  have hk : (nP + UInt64.ofNat msh.nIdx).toNat = nP.toNat + msh.nIdx := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnb]
  unfold ConRon.Arena.checkBlockTele
  refine Sim.bindK (K := ibtK1 p n vis _ _) (body := fun _ m1 => ibtK2 p n _
    (callW p n "check_sum_tele" [vis, UInt64.ofNat c, nP + UInt64.ofNat msh.nIdx, UInt64.ofNat c] m1))
    rfl (fun _ _ => rfl)
    (installSimStub (p := p) (n := n) (checkConstantVal_spec dn vis fe _ msh.cvT) ⟨hS, hcvm⟩) ?_
  rintro - - m1 a1 ⟨hS1, hg1, -⟩
  have hcvm1 : decCVp m1 (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.stab (OMono.decCVp _) hcv m1 hg1
  refine Sim.bindK (K := ibtK2 p n _) (body := fun r2 m2 => ibtK3 p n (r2.headD 0) (r2.tail.headD 0)
      (callW p n "strip_pis" [nP + UInt64.ofNat msh.nIdx, rdW (m2.arr64 EREC) (r2.headD 0 + 3)] m2))
    rfl (fun _ _ => rfl) (by rw [← hk]; exact installCstSim hP n hS1 hcvm1 (CVExt_grow hg1 hcvx)) ?_
  rintro r2 ⟨cvTa, sx⟩ m2 a2 ⟨hS2, hg2, hcvTa, hxTa, hs32, hsd⟩
  obtain ⟨htyl, htye⟩ := partsCVType (installCvDecB hcvTa hxTa) (w := r2.headD 0) rfl
  refine Sim.bindK (K := ibtK3 p n _ _) (body := fun r3 m3 => if r3.headD 0 = 0 then none
      else ibtK4 (r2.headD 0) (r2.tail.headD 0) (r3.tail.tail.tail.headD 0)
        (callW p n "intern_sort" [r2.tail.headD 0] m3)) rfl (fun _ _ => rfl)
    (by
      have h : Sim (callW p n "strip_pis" [nP + UInt64.ofNat msh.nIdx, rdW (m2.arr64 EREC) (r2.headD 0 + 3)] m2)
          _ a2 _ := fun r m' e =>
        stripF_pis_ok dn vis fe (nP + UInt64.ofNat msh.nIdx) _ htyl m2 m' a2 r (stripF_of_callW hP.strip e) hS2
      rw [hk, htye] at h; exact h) ?_
  rintro r3 x3 m3 a3 ⟨hS3, hg3, hd3⟩
  cases x3 with
  | none =>
    have h0 : r3.headD 0 = 0 := hd3
    simp only [h0, if_true]; exact Sim.of_none
  | some bb =>
  obtain ⟨bs, body⟩ := bb
  obtain ⟨h1, -, hb32, hbe⟩ := hd3
  simp only [h1, show (1 : Word) ≠ 0 by decide, if_false]
  have hd3' : (r3.drop 3).headD 0 = r3.tail.tail.tail.headD 0 := by
    rcases r3 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
  rw [hd3'] at hb32 hbe
  refine Sim.bindK (K := ibtK4 _ _ _) (body := fun r4 m4 => if r3.tail.tail.tail.headD 0 = r4.headD 0
      then some ([r2.headD 0, r2.tail.headD 0], m4) else none) rfl (fun _ _ => rfl)
    (by have hsd' : decI (r2.tail.headD 0) = sx := hsd; rw [← hsd']; exact installSortSim hP n hS3 hs32) ?_
  rintro r4 srt m4 a4 ⟨hS4, hg4, hsrt⟩
  split
  · rename_i heq
    have hb : (body == srt) = true := by rw [← hbe, ← hsrt, heq, decE_eq]; exact beq_self_eq_true _
    simp only [hb, if_true]
    refine Sim.ret ⟨hS4, ((hg1.trans hg2).trans hg3).trans hg4, ?_, ?_, hs32, hsd⟩
    · exact DecB.stab (OMono.decCVp _) (installCvDecB hcvTa hxTa) m4 (hg3.trans hg4)
    · exact CVExt_grow (hg3.trans hg4) hxTa
  · exact Sim.of_none

/-- **`check_block_tele` refines `checkBlockTele`** (through `check_constant_val`'s and
`strip_pis`'s stubs; `nP + nIdx ≥ 2^64` a capacity abort): the member record decoded below the
tops with its former's constant record below the tops; the checked former below the tops, its
result sort a handle. -/
@[refines ConRon.Arena.checkBlockTele]
theorem checkBlockTele_refines (p : Prog) (hP : CstProg p)
    (hp : p.lookup "check_block_tele" = some checkBlockTele) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nP ms : Word) (msh : MemberShape)
    (hS : StageR dn vis fe s₀.mem a₀) (hms : MemOK s₀.mem ms.toNat msh) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_tele" [vis, nP, ms]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀ ∧
      TeleOut dn vis fe s₀.mem r (AM.res (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀); ⊤⦄ :=
  triple_post (ibt_spec p hp n s₀ vis nP ms) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (ibtW_sim p hP n hS hms) hm
    ⟨hl, hok, hQ⟩

/-- A callee proved at every positive fuel is simulated at every fuel (`callW` at `0` fails). -/
theorem Sim.callW_pos {α : Type} {p : Prog} {f : FnName} {args : List Word} {m : Mem} {op : AM α}
    {a : AState} {Q : List Word → α → Mem → AState → Prop}
    (h : ∀ k, Sim (callW p (k + 1) f args m) op a Q) (n : Nat) : Sim (callW p n f args m) op a Q := by
  cases n with
  | zero => rw [callW_zero]; exact Sim.of_none
  | succ k => exact h k

end L.Ind
