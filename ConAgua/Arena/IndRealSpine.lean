import ConAgua.Arena.IndRealFvt

/-!
# The spine adapters' stub contracts discharged (lane `indproofs4`, helper `spine`)

`get_app_fn_f`, `pi_result_f` and `mk_app_n_f`, lane `induct`'s adapters over the whnf lane's
spine walks (`WhnfEntry.lean`), as program- and fuel-free models `callF P f` (`CallF.lean`, the
recipe of `IndReal.lean`) with the relational facts of the `IndStubs` contracts (`gafF_ok`,
`pirF_ok`, `mknF_ok`), and one program bundle `AdF` for the three. This file sits below the
stage's spec files (`IndPartsSpec3`, …), so it does not import `IndReal`/`StubIndRefine`: the
adapter specs are restated here.

* `get_app_fn_f`, `pi_result_f` abort at any fuel word other than `CWF`, so the contracts hold at
  every fuel word: a returning run has `f = CWF`, and `CWF.toNat = coreWalkFuel` (`CWF_eq`) is the
  walks' fuel. They write nothing.
* `mk_app_n_f` copies the `IW` slice to the stack top (`iw_to_spn`, `i2sW_ok`), runs `mk_app_n`
  (`mkAppNFromW_ok` under `ArenaD`) and puts the top back. The room check `len(SPN) - top ≥ cnt`
  bounds the copy without a bound on `|SPN|` (which `StageR` does not carry).
* `get_app_args_f`, `fvar_type_d`, `fvar_type_ds` are in `IndRealFvt.lean` (helper `fvt`); their
  program bundles are fields of `AdF`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **An adapter `g_f(f, e)` over a spine walk `g(e)`** (`get_app_fn_f`, `pi_result_f`): its
model refines the twin's walk `op`, memory and twin state unchanged. -/
theorem adF_ok {P : Prog} {fF g : FnName} {op : Nat → EIdx → AM EIdx}
    (hspec : ∀ k s₀ f e, ⦃fun s => s = s₀⦄ invoke P (exec P (k + 1)) fF [f, e]
      ⦃fun r s' => LocEq s' s₀ ∧ (if f ≠ CWF then none else
        ntBW (callW P k g [e] s₀.mem) fun r m' => some ([r.headD 0], m')) = some (r, s'.mem); ⊤⦄)
    (href : ∀ k s₀ a₀, ArenaR s₀.mem a₀ → ∀ e, HW e → ⦃fun s => s = s₀⦄ invoke P (exec P k) g [e]
      ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ HW (r.headD 0) ∧
        (op coreWalkFuel (decE e)).run a₀ = .ok (decE (r.headD 0), a₀); ⊤⦄)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word) (he : H e) :
    RelW (callF P fF) [f, e] (StageR dn vis fe) (op f.toNat (decI e)) (KeepPost dn vis fe decW0E) := by
  intro m m' a r h hS
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | k
  · simp [callW_zero] at hc
  have c' := callW_model (M := fun mm => if f ≠ CWF then none else
    ntBW (callW P k g [e] mm) fun r m' => some ([r.headD 0], m')) (fun s => hspec k s f e) hc
  obtain ⟨hf, c1⟩ := of_ite_none c'
  obtain rfl : f = CWF := Decidable.not_not.mp hf
  obtain ⟨⟨r', m''⟩, c'', c'⟩ := of_K (K := (ntBW · _)) c1 rfl; rw [bW_some] at c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
  obtain ⟨t, ht, hm, -, hHW, hrun⟩ := triple_of_callW (href k ⟨m, Locals.init []⟩ a hS.1.arena.1 e he) c''
  have e_m : m = m'' := by rw [← ht, hm]
  subst e_m
  exact ⟨decE (r'.headD 0), a, by rw [CWF_eq]; exact hrun, hS, IWGrow.refl _, hHW, rfl⟩

/-! ## `get_app_fn_f` -/

/-- The adapter `get_app_fn_f(f, e)` over its callee's run. -/
def gafAdW (p : Prog) (n : Nat) (m : Mem) (f e : Word) : Option (List Word × Mem) :=
  if f ≠ CWF then none else
  ntBW (callW p n "get_app_fn" [e] m) fun r m' => some ([r.headD 0], m')

theorem gafAd_spec (p : Prog) (hp : p.lookup "get_app_fn_f" = some getAppFnFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "get_app_fn_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ gafAdW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, getAppFnFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "get_app_fn"] <;>
    finish (gen := 20) [gafAdW, ntBW, CWF]

/-- `get_app_fn_f` and its callee. -/
def gafProg : Prog := [("get_app_fn_f", getAppFnFL), ("get_app_fn", getAppFnL)]

def gafFns : List FnName := gafProg.map (·.1)

/-- `get_app_fn_f` writes nothing. -/
theorem gafProg_closed : closedA gafProg [] [] gafFns = true := by decide +kernel

/-- The program bundle. -/
abbrev GafF (p : Prog) : Prop := ProgHas p gafProg

/-- **The model of `get_app_fn_f`.** -/
noncomputable def gafF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF gafProg "get_app_fn_f" m args

theorem gafF_spec0 (p : Prog) (hp : GafF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "get_app_fn_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ gafF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec gafProg_closed (hp.agree gafFns) (by decide) n s₀ args

/-- **`get_app_fn_f`'s model refines `getAppFn`** (replaces `IndStubs.getAppFn_spec`): memory and
twin state unchanged. -/
theorem gafF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word) (he : H e) :
    RelW gafF [f, e] (StageR dn vis fe) (getAppFn f.toNat (decI e)) (KeepPost dn vis fe decW0E) :=
  adF_ok (fun k s f e => gafAd_spec gafProg rfl k s f e) (getAppFn_refines' gafProg rfl) dn vis fe f e he

/-- `get_app_fn_f` writes nothing. -/
theorem gafF_frame {m m' : Mem} {args r : List Word} (h : gafF m args = some (r, m')) :
    MemFrame [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame gafProg_closed (by decide) (run_of_callW hc)).1

/-! ## `pi_result_f` -/

/-- The adapter `pi_result_f(f, e)` over its callee's run. -/
def pirAdW (p : Prog) (n : Nat) (m : Mem) (f e : Word) : Option (List Word × Mem) :=
  if f ≠ CWF then none else
  ntBW (callW p n "pi_result" [e] m) fun r m' => some ([r.headD 0], m')

theorem pirAd_spec (p : Prog) (hp : p.lookup "pi_result_f" = some piResultFL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "pi_result_f" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pirAdW p n s₀.mem f e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, piResultFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "pi_result"] <;>
    finish (gen := 20) [pirAdW, ntBW, CWF]

/-- `pi_result_f` and its callee. -/
def pirProg : Prog := [("pi_result_f", piResultFL), ("pi_result", piResultL)]

def pirFns : List FnName := pirProg.map (·.1)

/-- `pi_result_f` writes nothing. -/
theorem pirProg_closed : closedA pirProg [] [] pirFns = true := by decide +kernel

/-- The program bundle. -/
abbrev PirF (p : Prog) : Prop := ProgHas p pirProg

/-- **The model of `pi_result_f`.** -/
noncomputable def pirF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF pirProg "pi_result_f" m args

theorem pirF_spec0 (p : Prog) (hp : PirF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_result_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ pirF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec pirProg_closed (hp.agree pirFns) (by decide) n s₀ args

/-- **`pi_result_f`'s model refines `piResult`** (replaces `IndStubs.piResult_spec`): memory and
twin state unchanged. -/
theorem pirF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word) (he : H e) :
    RelW pirF [f, e] (StageR dn vis fe) (piResult f.toNat (decI e)) (KeepPost dn vis fe decW0E) :=
  adF_ok (fun k s f e => pirAd_spec pirProg rfl k s f e) (piResult_refines' pirProg rfl) dn vis fe f e he

/-- `pi_result_f` writes nothing. -/
theorem pirF_frame {m m' : Mem} {args r : List Word} (h : pirF m args = some (r, m')) :
    MemFrame [] [] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame pirProg_closed (by decide) (run_of_callW hc)).1

/-! ## `mk_app_n_f` -/

/-- The model of `iw_to_spn(d, s, l)` by L fuel: `SPN[d + j] := IW[s + j]` for `j < l`. -/
def i2sW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, d, s, l =>
    if l = 0 then some ([0], m)
    else ntBW (i2sW k (m.set64 SPN d (rdW (m.arr64 IW) s)) (d + 1) (s + 1) (l - 1))
      fun _ m' => some ([0], m')

theorem i2sW_nil (k : Nat) (m : Mem) (d s l : Word) (h : l = 0) :
    i2sW (k + 1) m d s l = some ([0], m) := by simp [i2sW, h]
theorem i2sW_cons (k : Nat) (m : Mem) (d s l : Word) (h : l ≠ 0) :
    i2sW (k + 1) m d s l = ntBW (i2sW k (m.set64 SPN d (rdW (m.arr64 IW) s)) (d + 1) (s + 1) (l - 1))
      fun _ m' => some ([0], m') := by simp [i2sW, h]

theorem i2s_spec (p : Prog) (hp : p.lookup "iw_to_spn" = some iwToSpnL) (k : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "iw_to_spn" [d, s, l]
    ⦃fun r s' => LocEq s' s₀ ∧ i2sW k s₀.mem d s l = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, iwToSpnL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, iwToSpnL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20) [i2sW_nil, i2sW_cons, ntBW]

theorem word_add_nat_succ (d : Word) (j : Nat) : d + (j + 1).toUInt64 = (d + 1) + j.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, Nat.toUInt64]
  omega

/-- **What `iw_to_spn` does**: the stack words `d ‥ d + l` are the pool's `s ‥ s + l`, nothing
else changes. -/
theorem i2sW_ok : ∀ (k : Nat) (m m' : Mem) (d s l : Word) (r : List Word),
    i2sW k m d s l = some (r, m') → d.toNat + l.toNat ≤ (m.arr64 SPN).size →
    d.toNat + l.toNat < 2 ^ 64 →
    MemFrame [SPN] [] m m' ∧ m'.arr64 IW = m.arr64 IW ∧
      (∀ j, j < l.toNat → spW m' (d + j.toUInt64) = rdW (m.arr64 IW) (s + j.toUInt64)) ∧
      (∀ w : Word, (w.toNat < d.toNat ∨ d.toNat + l.toNat ≤ w.toNat) → spW m' w = spW m w) := by
  intro k
  induction k with
  | zero => intro m m' d s l r h; simp [i2sW] at h
  | succ k ih =>
    intro m m' d s l r h hb hw
    by_cases hl : l = 0
    · rw [i2sW_nil k m d s l hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl
      exact ⟨MemFrame.refl _ _ _, rfl, fun j hj => absurd hj (by simp), fun _ _ => rfl⟩
    rw [i2sW_cons k m d s l hl] at h
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K (K := (ntBW · _)) h rfl; rw [bW_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hl0 : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
    have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hl1 : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
    have hsz : ((m.set64 SPN d (rdW (m.arr64 IW) s)).arr64 SPN).size = (m.arr64 SPN).size :=
      size_set64 _ _ _ _ _
    obtain ⟨hfr, hiw, hget, hout⟩ := ih _ _ _ _ _ _ h1 (by rw [hsz, hd1, hl1]; omega)
      (by rw [hd1, hl1]; omega)
    have hiw0 : (m.set64 SPN d (rdW (m.arr64 IW) s)).arr64 IW = m.arr64 IW :=
      Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have hset : spW (m.set64 SPN d (rdW (m.arr64 IW) s)) d = rdW (m.arr64 IW) s := by
      simp only [spW, rdW_set64]; simp; omega
    have hoth : ∀ w : Word, w ≠ d → spW (m.set64 SPN d (rdW (m.arr64 IW) s)) w = spW m w := by
      intro w hw; simp only [spW, rdW_set64]; simp [Ne.symm hw]
    refine ⟨(MemFrame.set64 m SPN (by decide) _ _).trans hfr, hiw.trans hiw0, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero =>
        have e0 : ∀ x : Word, x + (0 : Nat).toUInt64 = x := fun x => by simp
        rw [e0, e0, hout d (Or.inl (by rw [hd1]; omega)), hset]
      | succ j =>
        rw [word_add_nat_succ, word_add_nat_succ, hget j (by rw [hl1]; omega), hiw0]
    · intro w hw'
      rw [hout w (by rw [hd1, hl1]; omega)]
      apply hoth
      intro he; subst he; omega

/-- The adapter `mk_app_n_f(f, off, cnt)` over its callees' runs. -/
def mknAdW (p : Prog) (n : Nat) (m : Mem) (f off cnt : Word) : Option (List Word × Mem) :=
  if m.len64 SPN < rdW (m.arr64 CTL) 136 then none else
  if m.len64 SPN - rdW (m.arr64 CTL) 136 < cnt then none else
  ntBW (callW p n "iw_to_spn" [rdW (m.arr64 CTL) 136, off, cnt] m) fun _ m1 =>
  ntBW (callW p n "mk_app_n" [f, rdW (m.arr64 CTL) 136, cnt]
      (m1.set64 CTL 136 (rdW (m.arr64 CTL) 136 + cnt))) fun r m2 =>
  some ([r.headD 0], m2.set64 CTL 136 (rdW (m.arr64 CTL) 136))

theorem mknAd_spec (p : Prog) (hp : p.lookup "mk_app_n_f" = some mkAppNFL) (n : Nat) (s₀ : St)
    (f off cnt : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mk_app_n_f" [f, off, cnt]
    ⦃fun r s' => LocEq s' s₀ ∧ mknAdW p n s₀.mem f off cnt = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, mkAppNFL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "iw_to_spn", callW_spec p n "mk_app_n"] <;>
    finish (gen := 20) [mknAdW, ntBW]

/-- `mk_app_n_f` and its callees. -/
def mknProg : Prog :=
  [("mk_app_n_f", mkAppNFL), ("iw_to_spn", iwToSpnL), ("mk_app_n", mkAppNL), ("mk_app", mkApp),
   ("der_b", derB), ("intern_app", internApp), ("app_find", appFind), ("app_push", appPush)]

def mknFns : List FnName := mknProg.map (·.1)

/-- `mk_app_n_f` writes the stack, its top, and the app tables (`mk_app`). -/
theorem mknProg_closed : closedA mknProg [SPN, AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [136, 4, 5] mknFns = true := by
  decide +kernel

abbrev MknF (p : Prog) : Prop := ProgHas p mknProg

/-- **The model of `mk_app_n_f`.** -/
noncomputable def mknF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF mknProg "mk_app_n_f" m args

theorem mknF_spec0 (p : Prog) (hp : MknF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mk_app_n_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ mknF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec mknProg_closed (hp.agree mknFns) (by decide) n s₀ args

theorem mknF_frame {m m' : Mem} {args r : List Word} (h : mknF m args = some (r, m')) :
    MemFrame [SPN, AREC, ASLOT, ADER, AREC + 256, ASLOT + 256, ADER + 256] [136, 4, 5] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame mknProg_closed (by decide) (run_of_callW hc)).1

/-- **`mk_app_n_f`'s model refines `mkAppN`** (replaces `IndStubs.mkAppN_spec`): the slice copied
to the stack top, `mk_app_n` (lane `whnf`'s `mkAppNFromW_ok` under `ArenaD`), the top put back;
the stage relation across the copy and the top (above array 136, `stageR_hi`) and across
`mk_app` (the app tables, below 64, `StageR.of_walk`; the twin keeps `cp`). -/
theorem mknF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f o l : Word) (hf : H f)
    (xs : List EIdx) :
    RelW mknF [f, o, l] (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some xs)
      (mkAppN (decI f) xs) (KeepPost dn vis fe decW0E) := by
  intro m m' a r h ⟨hS, hxs⟩
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | k
  · simp [callW_zero] at hc
  have c' := callW_model (M := fun mm => mknAdW mknProg k mm f o l)
    (fun s => mknAd_spec mknProg rfl k s f o l) hc
  simp only [mknAdW] at c'
  obtain ⟨g1, c'⟩ := of_ite_none c'
  obtain ⟨g2, c'⟩ := of_ite_none c'
  generalize htop : rdW (m.arr64 CTL) 136 = top at c' g1 g2
  cases c1 : callW mknProg k "iw_to_spn" [top, o, l] m with
  | none => rw [c1] at c'; simp at c'
  | some q1 =>
  obtain ⟨r1', m1⟩ := q1
  rw [c1, bW_some] at c'
  obtain ⟨⟨r2, m2⟩, c2, c'⟩ := of_K (K := (ntBW · _)) c' rfl; rw [bW_some] at c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
  -- the room: `top + l ≤ len64 SPN ≤ |SPN|`, no wrap
  have hlen : (m.len64 SPN).toNat ≤ (m.arr64 SPN).size ∧ (m.len64 SPN).toNat < 2 ^ 64 := by
    refine ⟨?_, UInt64.toNat_lt _⟩
    show (((m.arr64 SPN).size : Nat).toUInt64).toNat ≤ _
    simp only [Nat.toUInt64]; exact Nat.mod_le _ _
  have hroom : top.toNat + l.toNat ≤ (m.len64 SPN).toNat := by
    have a1 := UInt64.not_lt.mp g1
    have a2 := UInt64.not_lt.mp g2
    rw [UInt64.le_iff_toNat_le] at a1
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp g1)] at a2
    omega
  -- the copy
  obtain ⟨t1, ht1, -, hW1⟩ := triple_of_callW (i2s_spec mknProg rfl k ⟨m, Locals.init []⟩ top o l) c1
  rw [ht1] at hW1
  obtain ⟨hfr1, hiw1, hget1, -⟩ := i2sW_ok _ m m1 top o l r1' hW1 (by omega) (by omega)
  have hfrA : MemFrame [SPN] [136] m (m1.set64 CTL 136 (top + l)) :=
    (hfr1.mono (fun b hb => hb) (fun x hx => by simp at hx)).trans
      ((MemFrame.setCtl m1 136 _).mono (fun b hb => by simp at hb) (fun x hx => hx))
  obtain ⟨hS1, hg1⟩ := stageR_hi hS hfrA (by simp [SPN]) (by simp) (by decide) (by decide)
  have hspn1 : ∀ w, spW (m1.set64 CTL 136 (top + l)) w = spW m1 w := fun w => by
    simp only [spW]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hsz1 : ((m1.set64 CTL 136 (top + l)).arr64 SPN).size = (m.arr64 SPN).size := hfrA.2.2.1 SPN
  have hl : xs.length = l.toNat := decHL_length m hxs
  have hiwsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  have hsp : SpineR (m1.set64 CTL 136 (top + l)) top l xs.toArray := by
    refine ⟨by simp [hl], by rw [hsz1]; omega, fun i hi => ?_, fun i hi => ?_⟩
    · obtain ⟨w, hw, hw32, -⟩ := decHL_word hxs hiwsz i hi
      rw [hspn1, hget1 i hi, hw]; exact hw32
    · have hi' : i < l.toNat := by simpa [hl] using hi
      obtain ⟨w, hw, -, hx⟩ := decHL_word hxs hiwsz i hi'
      rw [hspn1, hget1 i hi', hw]
      have := List.getElem?_eq_getElem (l := xs) (i := i) (by omega)
      rw [hx] at this
      simp only [List.getElem_toArray]
      exact (Option.some.inj this).symm
  -- `mk_app_n`
  obtain ⟨t2, ht2, -, hL⟩ := triple_of_callW
    (mkAppNL_spec mknProg rfl rfl rfl rfl rfl rfl k ⟨m1.set64 CTL 136 (top + l), Locals.init []⟩
      f top l) c2
  rw [ht2] at hL
  have h0 : (0 : Word).toNat = 0 := rfl
  obtain ⟨hok, hD2, hres⟩ := mkAppNFromW_ok l.toNat _ a f top l 0 xs.toArray (by rw [h0]; omega)
    (by rw [h0]; omega) hS1.1.arena hsp (r2.headD 0) m2 hL
  have hhw := mkAppNFromW_hw l.toNat _ a f top l 0 (by rw [h0]; omega) hS1.1.arena hf _ _ hL
  have hfr2 := mkAppNFromW_frame l.toNat _ m2 f top l 0 (r2.headD 0) hL
  have hkeep := keeps_cpl_mkAppNFrom (decE f) xs.toArray 0
  rw [h0, mkAppNFrom_eq_mkAppN, List.toList_toArray] at hok hD2 hres
  rw [mkAppNFrom_eq_mkAppN, List.toList_toArray] at hkeep
  have hrun := AM.run_of_ok _ a hok
  have hcp : cp (AM.st (mkAppN (decE f) xs) a) = cp a :=
    congrArg (fun x => (x.1, x.2.1)) (hkeep.run hrun)
  obtain ⟨hS2, hg2⟩ := StageR.of_walk hS1 hD2 hfr2
    (fun b hb => by simp only [List.mem_cons, List.not_mem_nil] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | h <;> simp_all [AREC, ASLOT, ADER])
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil] at hx; rcases hx with rfl | rfl | h <;> simp_all) hcp
  -- the top put back
  obtain ⟨hS3, hg3⟩ := stageR_hi hS2 (MemFrame.setCtl m2 136 top) (by simp) (by simp) (by decide) (by decide)
  exact ⟨_, _, hrun, hS3, hg1.trans (hg2.trans hg3), hhw, hres.symm⟩

/-! ## The bundle -/

/-- **The adapters' program bundle**: `p` binds each adapter's call-closed list as the list does. -/
structure AdF (p : Prog) : Prop where
  gaf : GafF p
  pir : PirF p
  mkn : MknF p
  gaa : GaaF p
  ftd : FtdF p
  ftds : FtdsF p

theorem gafF_spec (p : Prog) (hp : AdF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "get_app_fn_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ gafF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  gafF_spec0 p hp.gaf n s₀ args

theorem pirF_spec (p : Prog) (hp : AdF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pi_result_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ pirF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  pirF_spec0 p hp.pir n s₀ args

theorem mknF_spec (p : Prog) (hp : AdF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mk_app_n_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ mknF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  mknF_spec0 p hp.mkn n s₀ args

theorem gaaF_spec (p : Prog) (hp : AdF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "get_app_args_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ gaaF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  gaaF_spec0 p hp.gaa n s₀ args

theorem ftdF_spec (p : Prog) (hp : AdF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_type_d" args
    ⦃fun r s' => LocEq s' s₀ ∧ ftdF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  ftdF_spec0 p hp.ftd n s₀ args

theorem ftdsF_spec (p : Prog) (hp : AdF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_type_ds" args
    ⦃fun r s' => LocEq s' s₀ ∧ ftdsF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  ftdsF_spec0 p hp.ftds n s₀ args

end L.Ind
