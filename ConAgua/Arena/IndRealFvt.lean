import ConAgua.Arena.IndRealFvtD
import ConAgua.Arena.CallF
import ConAgua.Arena.WhnfEntry
import ConAgua.Arena.WhnfSpineArgs
import ConAgua.Arena.DeclNatSpec
import ConAgua.Arena.IndStubs
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndView
import ConAgua.Arena.TeleLift
import ConAgua.Arena.StripTeleSpec
import ConAgua.Arena.StageInst1
import ConAgua.Arena.IndPartsSpec2

/-!
# `fvar_type_ds`, `get_app_args_f`: stub contracts discharged (lane `indproofs4`, helper `fvt`)

Program- and fuel-free models `callF P f` (`CallF.lean`, the recipe of `IndReal.lean`) with the
relational facts of the `IndStubs` contracts, under `StageR`:

* `fvar_type_d` (`ftdF`, `ftdF_ok`) is in `IndRealFvtD.lean` (imports below `IndInstallSpec`).
* `fvar_type_ds` (`ftdsF`, `ftdsF_ok`): a fresh `IW` slice, then one `fvar_type_d` per input
  word, written at the slice; the memory after is `wrIW (allocMem m l) q ws` and `slice_keep`
  gives the post. **The contract's pre is strengthened** by `0 < l → o + l ≤ iwTop m` (a
  non-empty input slice below the pool's top): an input slice straddling the top overlaps the
  fresh output slice, and the loop then reads a word it wrote (`fvarTypeD` of an earlier result)
  where the twin reads the input. The callers' slices come from `decRL`s or stable decodings
  (`DecB`), which carry the bound.
* `get_app_args_f` (`gaaF`, `gaaF_ok`): `get_app_args` (`getAppArgs_refinesR`, the whnf lane's
  `getAppArgs_refines'` without its bound `|SPN| < 2^63`, which `StageR` does not carry: the room
  checks give `top + n ≤ len64 SPN < 2^64`, as `mknF_ok` argues), a fresh `IW` slice, the stack
  slice copied into it (`spn_to_iw`, `s2iW_wr`), the stack top put back.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Shared facts (moved here from `IndRealSpine.lean`, which imports this file) -/

/-- The stage relation across a writer above array 136 and `CTL[129]` that leaves the pool alone
(`IndPos2SpecB`'s `StageR.frame_hi`, which sits above this file). -/
theorem stageR_hi {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {A : List ArrId} {C : List Word} (hS : StageR dn vis fe m a) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 137 ≤ b ∧ b < 256 ∧ (b < 140 ∨ 144 ≤ b)) (hC : ∀ x ∈ C, 130 ≤ x.toNat ∧ x.toNat ≠ 133) (hA2 : IW ∉ A) (hC2 : (200 : Word) ∉ C) :
    StageR dn vis fe m' a ∧ IWGrow m m' := by
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW hA2 (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (fun h => by have := hA _ h; simp [EREC] at this)
    (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 200 hC2
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 :=
    hf.2.1 129 (fun h => by have := (hC _ h).1; simp at this)
  refine ⟨⟨CheckR.frame_hi hA hC hf hS.1, ?_⟩, ?_⟩
  · simp only [IWOK, iwTop, erTop, hI, hE, h200, h129, hf.2.2.1 CTL]; exact hS.2
  · refine ⟨?_, ?_, fun i _ => by rw [hI], fun i _ => by rw [hE]⟩
    · simp only [iwTop, h200]; exact Nat.le_refl _
    · simp only [erTop, h129]; exact Nat.le_refl _

/-- A decoded `IW` handle slice, word by word. -/
theorem decHL_word {m : Mem} {o l : Word} {xs : List EIdx} (h : decHL m o.toNat l.toNat = some xs)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (i : Nat) (hi : i < l.toNat) :
    ∃ w, rdW (m.arr64 IW) (o + i.toUInt64) = w ∧ w.toNat < 2 ^ 32 ∧
      xs[i]? = some (decI w) := by
  have hl : xs.length = l.toNat := decHL_length m h
  have hb : o.toNat + l.toNat ≤ (m.arr64 IW).size := hslice?_bound _ _ _ _ h (by omega)
  have hg := mapM_opt_get (fun j => hd? (iwA m) (o.toNat + j)) (List.range l.toNat) xs h i
    (by simpa using hi)
  have hiw : iwH m (o.toNat + i) = some (xs[i]'(by omega)) := by simpa [iwH] using hg
  obtain ⟨w, h1, h2, h3⟩ := iwH_rdW hiw (by omega)
  have ho : UInt64.ofNat (o.toNat + i) = o + i.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_add, Nat.toUInt64]
  rw [ho] at h1
  exact ⟨w, h1, h2, by rw [List.getElem?_eq_getElem (by omega), h3]⟩

/-! ## `fvar_type_ds` -/

/-- `fvar_type_ds`' loop (named, for its spec; `fvarTypeDsL_eq`). -/
def ftdsLoop : Stmt := lblk (o, l, q, k, t) {
  while k < l {
    t := call fvar_type_d(IW.u64[o + k]);
    IW.u64[q + k] := t;
    k := k + 1
  }
}

theorem fvarTypeDsL_eq : fvarTypeDsL = lfn (o, l) locals (q, k, t) {
  q := call iw_alloc(l);
  k := 0;
  ⟪ftdsLoop⟫;
  return (q, l)
} := rfl

/-- The model of `fvar_type_ds`' loop at the loop's fuel, from index `k`; `q` the fresh slice. -/
noncomputable def ftdsGoW (o l q : Word) : Nat → Mem → Word → Option (List Word × Mem)
  | 0, _, _ => none
  | f + 1, m, k =>
    if k < l then
      match ftdF m [rdW (m.arr64 IW) (o + k)] with
      | none => none
      | some (r, m1) => ftdsGoW o l q f (m1.set64 IW (q + k) (r.headD 0)) (k + 1)
    else some ([q, l], m)

theorem ftdsGoW_ge (o l q : Word) (f : Nat) (m : Mem) (k : Word) (hk : ¬ k < l) : ftdsGoW o l q (f + 1) m k = some ([q, l], m) := by
  simp only [ftdsGoW, hk, if_false]

theorem ftdsGoW_none (o l q : Word) (f : Nat) (m : Mem) (k : Word) (hk : k < l) (h : ftdF m [rdW (m.arr64 IW) (o + k)] = none) :
    ftdsGoW o l q (f + 1) m k = none := by
  simp only [ftdsGoW, if_pos hk, h]

theorem ftdsGoW_step (o l q : Word) (f : Nat) (m m1 : Mem) (k : Word) (r : List Word) (hk : k < l) (h : ftdF m [rdW (m.arr64 IW) (o + k)] = some (r, m1)) :
    ftdsGoW o l q (f + 1) m k = ftdsGoW o l q f (m1.set64 IW (q + k) (r.headD 0)) (k + 1) := by
  simp only [ftdsGoW, if_pos hk, h]

/-- `fvar_type_ds` and its callees. -/
def ftdsProg : Prog := [("fvar_type_ds", fvarTypeDsL), ("iw_alloc", iwAlloc)] ++ ftdProg

def ftdsFns : List FnName := ftdsProg.map (·.1)

/-- `fvar_type_ds` writes the pool and its top. -/
theorem ftdsProg_closed : closedA ftdsProg [IW] [200] ftdsFns = true := by decide +kernel

/-- The program bundle. -/
abbrev FtdsF (p : Prog) : Prop := ProgHas p ftdsProg

theorem ftdsLoop_spec (p : Prog) (hp : FtdF p) (f : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p f ftdsLoop
    ⦃fun r s' => r ≠ .brk ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      ftdsGoW (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) f s₀.mem (s₀.loc 3) =
        some (r.retOr [s'.loc 2, s'.loc 1], s'.mem); ⊤⦄ := by
  induction f generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ f ih =>
    rw [exec, step_while (w := ftdsLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih, ftdF_spec0 p hp f] <;>
      finish [ftdsGoW_ge, ftdsGoW_none, ftdsGoW_step]

/-- The model of `fvar_type_ds(o, l)` at the call's L fuel. -/
noncomputable def ftdsW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | f + 1, m, o, l =>
    match allocW m l with
    | none => none
    | some (q, m1) => ftdsGoW o l q (f + 1) m1 0

theorem ftdsW_none (f : Nat) (m : Mem) (o l : Word) (h : allocW m l = none) :
    ftdsW (f + 1) m o l = none := by simp only [ftdsW, h]

theorem ftdsW_some (f : Nat) (m m1 : Mem) (o l q : Word) (h : allocW m l = some (q, m1)) :
    ftdsW (f + 1) m o l = ftdsGoW o l q (f + 1) m1 0 := by simp only [ftdsW, h]

theorem ftds_specW (p : Prog) (hp : FtdsF p) (n : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_type_ds" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ ftdsW n s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "fvar_type_ds"), fvarTypeDsL_eq]
  simp only [callFn]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        iwAlloc_specW p (hp.get "iw_alloc") n,
        fun s => Triple.step_exec (ftdsLoop_spec p hp.right (n + 1) s)] <;>
      finish [ftdsW_some]

/-- **The model of `fvar_type_ds`.** -/
noncomputable def ftdsF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF ftdsProg "fvar_type_ds" m args

theorem ftdsF_spec0 (p : Prog) (hp : FtdsF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fvar_type_ds" args
    ⦃fun r s' => LocEq s' s₀ ∧ ftdsF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec ftdsProg_closed (hp.agree ftdsFns) (by decide) n s₀ args

theorem word_ofNat_toNat (k : Word) : (k.toNat).toUInt64 = k := by simp [Nat.toUInt64]

/-- **The loop of `fvar_type_ds`**: the words `ws` written from `q + k` on, the twin's
`fvarTypeDs` of the rest of the input, its state unchanged. The input slice lies below `q`. -/
theorem ftdsGoW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (a : AState)
    (o l q : Word) (m0 : Mem) (xs : List EIdx) (hxs : decHL m0 o.toNat l.toNat = some xs)
    (hsz0 : (m0.arr64 IW).size < 2 ^ 64) (hol : 0 < l.toNat → o.toNat + l.toNat ≤ q.toNat) :
    ∀ (f : Nat) (m : Mem) (k : Word) (r : List Word) (m' : Mem),
      ftdsGoW o l q f m k = some (r, m') → StageR dn vis fe m a → k.toNat ≤ l.toNat →
      q.toNat + l.toNat ≤ (m.arr64 IW).size →
      (∀ j : Nat, k.toNat ≤ j → j < l.toNat →
        rdW (m.arr64 IW) (o + j.toUInt64) = rdW (m0.arr64 IW) (o + j.toUInt64)) →
      r = [q, l] ∧ ∃ ws : List Word, m' = wrIW m (q + k) ws ∧ ws.length = l.toNat - k.toNat ∧
        (∀ w ∈ ws, w.toNat < 2 ^ 32) ∧
        (fvarTypeDs (xs.drop k.toNat)).run a = .ok (ws.map decI, a) := by
  have hxl : xs.length = l.toNat := decHL_length m0 hxs
  intro f
  induction f with
  | zero => intro m k r m' h; simp [ftdsGoW] at h
  | succ f ih =>
    intro m k r m' h hS hkl hroom hin
    by_cases hk : k < l
    · have hk' : k.toNat < l.toNat := hk
      rcases h1 : ftdF m [rdW (m.arr64 IW) (o + k)] with _ | ⟨r1, m1⟩
      · rw [ftdsGoW_none o l q f m k hk h1] at h; cases h
      rw [ftdsGoW_step o l q f m m1 k r1 hk h1] at h
      obtain ⟨w, hw, hw32, hxk⟩ := decHL_word hxs hsz0 k.toNat hk'
      rw [word_ofNat_toNat] at hw
      have hx : rdW (m.arr64 IW) (o + k) = w := by
        have := hin k.toNat (Nat.le_refl _) hk'
        rw [word_ofNat_toNat] at this
        rw [this, hw]
      rw [hx] at h1
      obtain ⟨hm1, hrun1, hlt1⟩ := ftdW_ok m m1 a hS.1.arena.1 w hw32 r1 (ftdF_eq h1)
      rw [hm1] at h
      have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
      have hk1 : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have hqk : (q + k).toNat = q.toNat + k.toNat := by
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hsz2 : ((m.set64 IW (q + k) (r1.headD 0)).arr64 IW).size = (m.arr64 IW).size :=
        size_set64 _ _ _ _ _
      obtain ⟨rfl, ws, hm', hlen, hws, hrun⟩ := ih _ _ _ _ h (hS.set_iw _ _) (by omega)
        (by rw [hsz2]; exact hroom) (fun j hj1 hj2 => by
          rw [← hin j (by omega) hj2, rdW_set64]
          have hoj : (o + j.toUInt64).toNat = o.toNat + j := by
            rw [UInt64.toNat_add]; simp [Nat.toUInt64]; omega
          have hol' := hol (by omega)
          have hne : q + k ≠ o + j.toUInt64 := by
            intro he; have := congrArg UInt64.toNat he; rw [hqk, hoj] at this; omega
          simp [hne])
      refine ⟨rfl, r1.headD 0 :: ws, ?_, by simp [hlen]; omega, ?_, ?_⟩
      · rw [hm']; simp only [wrIW]; rw [UInt64.add_assoc]
      · intro x hx; simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hlt1
        · exact hws x hx
      · have hd : xs.drop k.toNat = decI w :: xs.drop (k.toNat + 1) := by
          rw [List.drop_eq_getElem_cons (by omega)]
          have := List.getElem?_eq_getElem (l := xs) (i := k.toNat) (by omega)
          rw [hxk] at this
          rw [← Option.some.inj this]
        rw [hd, hk1] at *
        rw [hk1] at hrun
        simp only [fvarTypeDs, StateT.run_bind, hrun1, except_ok_bind, hrun, List.map_cons]
        rfl
    · rw [ftdsGoW_ge o l q f m k hk] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hkl' : k.toNat = l.toNat := by
        have : ¬ k.toNat < l.toNat := hk
        omega
      refine ⟨rfl, [], rfl, by simp; omega, by simp, ?_⟩
      rw [hkl', ← hxl, List.drop_length]
      rfl

/-- **`fvar_type_ds`' model refines `fvarTypeDs`** (replaces `IndStubs.fvarTypeDs_spec`, with the
input slice below the pool's top, see the header): a fresh slice, the twin state unchanged. -/
theorem ftdsF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (o l : Word)
    (xs : List EIdx) :
    RelW ftdsF [o, l]
      (fun m a => StageR dn vis fe m a ∧ decHL m o.toNat l.toNat = some xs ∧
        (0 < l.toNat → o.toNat + l.toNat ≤ iwTop m))
      (fvarTypeDs xs) (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := by
  intro m m' a r h ⟨hS, hxs, hol⟩
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | k
  · simp [callW_zero] at hc
  have c' := callW_model (M := fun mm => ftdsW (k + 1) mm o l)
    (fun s => ftds_specW ftdsProg (ProgHas.refl _) (k + 1) s o l) hc
  rcases ha : allocW m l with _ | ⟨q, m1⟩
  · rw [ftdsW_none k m o l ha] at c'; cases c'
  rw [ftdsW_some k m m1 o l q ha] at c'
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hS.2.2.2.1
  obtain ⟨hq, rfl, hroom⟩ := allocW_facts ha hsz
  obtain ⟨hS1, -, -, -⟩ := allocW_stage ha hS
  have hqt : q.toNat = iwTop m := by rw [hq]; rfl
  have hI1 : (allocMem m l).arr64 IW = m.arr64 IW := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  obtain ⟨rfl, ws, hm', hlen, hws, hrun⟩ := ftdsGoW_ok dn vis fe a o l q m xs hxs hsz (fun hl => by rw [hqt]; exact hol hl)
    (k + 1) (allocMem m l) 0 r m' c' hS1 (by simp) (by rw [hI1]; exact hroom)
    (fun j _ _ => by rw [hI1])
  have hlen' : l.toNat = ws.length := by simpa using hlen.symm
  have e0 : q + (0 : Word) = q := by simp
  rw [e0, hq] at hm'
  have hrec := recPost_wr m ws l hlen' hS.2 (by rw [← hlen', ← hqt]; exact hroom)
  rw [← hm'] at hrec
  rw [← hq] at hrec
  have hK := slice_keep (κ := .expr) hS hrec hws hlen'
  have hd0 : xs.drop (0 : Word).toNat = xs := rfl
  rw [hd0] at hrun
  exact ⟨_, a, hrun, hK⟩

/-- `fvar_type_ds` writes the pool and its top. -/
theorem ftdsF_frame {m m' : Mem} {args r : List Word} (h : ftdsF m args = some (r, m')) :
    MemFrame [IW] [200] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame ftdsProg_closed (by decide) (run_of_callW hc)).1

/-! ## `get_app_args` without a bound on `|SPN|` -/

/-- `fillW_ok` with the slice's end below `2^64` in place of `|SPN| < 2^63`. -/
theorem fillW_okR (o : Word) : ∀ (j k : Nat) (m : Mem) (e : Word), j < k →
    o.toNat + j ≤ (m.arr64 SPN).size → o.toNat + j < 2 ^ 64 →
    ∃ m', fillW k m e o j.toUInt64 = some m' ∧ MemFrame [SPN] [] m m' ∧
      (∀ i, i < j → spW m' (o + i.toUInt64) = (argsW m e j).getD i 0) ∧
      (∀ w : Word, (w.toNat < o.toNat ∨ o.toNat + j ≤ w.toNat) → spW m' w = spW m w) := by
  intro j
  induction j with
  | zero =>
    intro k m e hk _ _
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ⟨m, by simpa using fillW_zero k' m e o, MemFrame.refl _ _ _, fun i hi => absurd hi (by omega),
      fun _ _ => rfl⟩
  | succ j ih =>
    intro k m e hk hb hw
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hne := toUInt64_ne_zero j (by omega)
    rw [fillW_succ k' m e o _ hne, toUInt64_succ_sub_one]
    have hoj : (o + j.toUInt64).toNat = o.toNat + j := by
      have hs : UInt64.size = 2 ^ 64 := rfl
      rw [UInt64.toNat_add, Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by omega)]
      try rw [hs]
      omega
    obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ = m.set64 SPN (o + j.toUInt64) (argW m e) := ⟨_, rfl⟩
    rw [← hm₁]
    have hsz₁ : (m₁.arr64 SPN).size = (m.arr64 SPN).size := by rw [hm₁]; exact size_set64 _ _ _ _ _
    obtain ⟨m', hf, hfr, hget, hout⟩ := ih k' m₁ (fnW m e) (by omega) (by rw [hsz₁]; omega)
      (by omega)
    have hset : spW m₁ (o + j.toUInt64) = argW m e := by
      simp only [spW, hm₁, rdW_set64]; simp [hoj]; omega
    have hoth : ∀ w : Word, w ≠ o + j.toUInt64 → spW m₁ w = spW m w := by
      intro w hw; simp only [spW, hm₁, rdW_set64]; simp [Ne.symm hw]
    refine ⟨m', hf, (hm₁ ▸ MemFrame.set64 m SPN (by decide) _ _).trans hfr, ?_, ?_⟩
    · intro i hi
      have ha : argsW m₁ (fnW m e) j = argsW m (fnW m e) j := by rw [hm₁, argsW_set]
      rw [ha] at hget
      rw [argsW]
      rcases Nat.lt_or_ge i j with h | h
      · rw [hget i h]
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [argsW_length]; exact h : i < (argsW m (fnW m e) j).length)]
      · have hij : i = j := by omega
        subst hij
        rw [hout _ (Or.inr (by rw [hoj]; exact Nat.le_refl _)), hset]
        simp [List.getD_eq_getElem?_getD, argsW_length]
    · intro w hw'
      rw [hout w (by omega)]
      apply hoth
      intro h; subst h; rw [hoj] at hw'; omega

/-- **`get_app_args` refines `getAppArgs coreWalkFuel`** with no bound on `|SPN|` (lane `whnf`'s
`getAppArgs_refines'` assumes `|SPN| < 2^63`; its room checks give the slice's end below
`len64 SPN < 2^64`, which is all the fill needs). -/
theorem getAppArgs_refinesR (p : Prog) (hg : p.lookup "get_app_args" = some getAppArgsL)
    (hc : p.lookup "app_count" = some appCountL) (hf : p.lookup "app_fill" = some appFillL)
    (n : Nat) (s₀ : St) (a₀ : AState) (hR : ArenaR s₀.mem a₀) (e : Word) (he : HW e) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_args" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧
      r.headD 0 = spTop s₀.mem ∧
      ∃ xs, (getAppArgs coreWalkFuel (decE e)).run a₀ = .ok (xs, a₀) ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat < 2 ^ 64; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs0 hrun
  subst hs0
  obtain ⟨hloc, hcall⟩ := M.of_run (P := fun x => x = s) rfl hrun (callW_spec p n "get_app_args" [e] s)
  rcases n with _ | n
  · rw [callW_zero] at hcall; cases hcall
  obtain ⟨t, ht, -, hW, h136⟩ := triple_of_callW (gaa_spec p hg n s e) hcall
  rw [ht] at hW h136
  refine ⟨hloc, ?_⟩
  simp only [gaaW] at hW
  rcases h1 : callW p n "app_count" [e] s.mem with _ | ⟨r₁, m₁⟩
  · rw [h1] at hW; simp at hW
  simp only [h1] at hW
  cases n with
  | zero => rw [callW_zero] at h1; cases h1
  | succ n' =>
  obtain ⟨t₁, ht₁, ht₁s, hcnt⟩ := triple_of_callW (appCount_spec p hc (n' + 1) s e) h1
  have hm₁ : m₁ = s.mem := by rw [← ht₁, ht₁s]
  subst hm₁
  try rw [ht₁s] at hcnt
  simp only [appCntW] at hcnt
  cases hL : gafLoopW s.mem e 4000000000 with
  | none => rw [hL] at hcnt; simp at hcnt
  | some q =>
  obtain ⟨e', f'⟩ := q
  rw [hL] at hcnt
  by_cases hf0 : f' = 0
  · simp [hf0] at hcnt
  simp only [hf0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hcnt
  obtain ⟨hcnt, -⟩ := hcnt
  obtain ⟨hrun', hlt, hle⟩ := gaaTwin s.mem a₀ hR _ e 4000000000 e' f' (Nat.le_refl _) he hL hf0
  have hfuel : (4000000000 : Word).toNat = coreWalkFuel := by simp [UInt64.toNat_ofNat, coreWalkFuel]
  rw [hfuel] at hrun' hlt hle
  have hcw : (r₁.headD 0).toNat = coreWalkFuel - f'.toNat := by
    have hle' : f' ≤ 4000000000 := by
      rw [UInt64.le_iff_toNat_le, hfuel]; exact hle
    rw [← hcnt, UInt64.toNat_sub_of_le _ _ hle', hfuel]
  have hlen : s.mem.len64 SPN = ((s.mem.arr64 SPN).size : Nat).toUInt64 := rfl
  obtain ⟨hk1, hW⟩ := of_ite_none hW
  obtain ⟨hk2, hW⟩ := of_ite_none hW
  -- the room: `top + n ≤ len64 SPN ≤ |SPN|`, below `2^64`
  have hszl : (((s.mem.arr64 SPN).size : Nat).toUInt64).toNat ≤ (s.mem.arr64 SPN).size := by
    simp only [Nat.toUInt64]; exact Nat.mod_le _ _
  have hroom : (rdW (s.mem.arr64 CTL) 136).toNat + (r₁.headD 0).toNat ≤
      (((s.mem.arr64 SPN).size : Nat).toUInt64).toNat := by
    rw [hlen] at hk1 hk2
    have a1 := UInt64.not_lt.mp hk1
    have a2 := UInt64.not_lt.mp hk2
    rw [UInt64.le_iff_toNat_le] at a1
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp hk1)] at a2
    omega
  have hw64 : (((s.mem.arr64 SPN).size : Nat).toUInt64).toNat < 2 ^ 64 := UInt64.toNat_lt _
  rcases h2 : callW p (n' + 1) "app_fill" [e, rdW (s.mem.arr64 CTL) 136, r₁.headD 0] s.mem with _ | ⟨r₂, m₂⟩
  · rw [h2] at hW; simp at hW
  simp only [h2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  obtain ⟨t₂, ht₂, hfill⟩ := triple_of_callW (appFill_spec p hf n' s e _ _) h2
  rw [ht₂] at hfill
  have hcN : r₁.headD 0 = (coreWalkFuel - f'.toNat).toUInt64 := by
    apply UInt64.toNat_inj.mp; rw [hcw]; simp [Nat.toUInt64]
    exact (Nat.mod_eq_of_lt (by simp [coreWalkFuel]; omega)).symm
  rw [hcN] at hfill
  have hfu := fillW_fuel _ _ _ _ _ _ (by simp [coreWalkFuel]; omega) hfill
  obtain ⟨m', hf', hfr, hget, -⟩ := fillW_okR (rdW (s.mem.arr64 CTL) 136) (coreWalkFuel - f'.toNat)
    (n' + 1) s.mem e hfu (by rw [← hcw]; omega) (by rw [← hcw]; omega)
  rw [hf'] at hfill
  cases hfill
  have hsp : ∀ w : Word, spW s'.mem w = spW m₂ w := by
    intro w; rw [← hm]; simp only [spW]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hszs : (s'.mem.arr64 SPN).size = (s.mem.arr64 SPN).size := by
    rw [← hm, size_set64]; exact hfr.2.2.1 SPN
  have hcN' : (r₁.headD 0).toNat = coreWalkFuel - f'.toNat := hcw
  refine ⟨?_, ?_, _, hrun', ?_, ?_⟩
  · rw [← hm]
    exact (hfr.mono (fun b hb => hb) (fun x hx => by simp at hx)).trans
      ((MemFrame.setCtl m₂ 136 _).mono (fun b hb => by simp at hb) (fun x hx => hx))
  · rw [← hr0]; rfl
  · rw [← hr0, ← hr1]
    refine ⟨by simp only [List.size_toArray, List.length_map, argsW_length]; exact hcN'.symm,
      by rw [hszs]; omega, ?_, ?_⟩
    · intro i hi
      rw [hcN'] at hi
      rw [hsp, hget i hi, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [argsW_length]; exact hi)]
      exact hlt _ (List.getElem_mem _)
    · intro i hi
      simp only [List.size_toArray, List.length_map, argsW_length] at hi
      have hi' : i < (argsW s.mem e (coreWalkFuel - f'.toNat)).length := by rw [argsW_length]; exact hi
      rw [hsp, hget i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      simp
  · rw [← hr0, ← hr1]; omega

/-! ## `get_app_args_f` -/

/-- The model of `spn_to_iw(d, s, l)` by L fuel: `IW[d + j] := SPN[s + j]` for `j < l`. -/
def s2iW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | k + 1, m, d, s, l =>
    if l = 0 then some ([0], m)
    else ntBW (s2iW k (m.set64 IW d (rdW (m.arr64 SPN) s)) (d + 1) (s + 1) (l - 1))
      fun _ m' => some ([0], m')

theorem s2iW_nil (k : Nat) (m : Mem) (d s l : Word) (h : l = 0) :
    s2iW (k + 1) m d s l = some ([0], m) := by simp [s2iW, h]
theorem s2iW_cons (k : Nat) (m : Mem) (d s l : Word) (h : l ≠ 0) :
    s2iW (k + 1) m d s l = ntBW (s2iW k (m.set64 IW d (rdW (m.arr64 SPN) s)) (d + 1) (s + 1) (l - 1))
      fun _ m' => some ([0], m') := by simp [s2iW, h]

theorem s2i_spec (p : Prog) (hp : p.lookup "spn_to_iw" = some spnToIwL) (k : Nat) :
    ∀ (s₀ : St) (d s l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "spn_to_iw" [d, s, l]
    ⦃fun r s' => LocEq s' s₀ ∧ s2iW k s₀.mem d s l = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ d s l; rw [invoke_eq _ hp]; simp only [callFn, spnToIwL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ d s l
    rw [invoke_eq _ hp]
    simp only [callFn, spnToIwL]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih] <;>
      finish (gen := 20) [s2iW_nil, s2iW_cons, ntBW]

/-- The stack words `s, s + 1, …` (`j` of them). -/
def spnWs (m : Mem) : Word → Nat → List Word
  | _, 0 => []
  | s, j + 1 => spW m s :: spnWs m (s + 1) j

theorem spnWs_length (m : Mem) : ∀ (s : Word) (j : Nat), (spnWs m s j).length = j
  | _, 0 => rfl
  | s, j + 1 => by simp [spnWs, spnWs_length m (s + 1) j]

theorem spnWs_congr {m m' : Mem} (h : m'.arr64 SPN = m.arr64 SPN) :
    ∀ (s : Word) (j : Nat), spnWs m' s j = spnWs m s j
  | _, 0 => rfl
  | s, j + 1 => by simp only [spnWs, spW, h, spnWs_congr h (s + 1) j]

theorem spnWs_get (m : Mem) : ∀ (j : Nat) (s : Word) (i : Nat), i < j →
    (spnWs m s j)[i]? = some (spW m (s + i.toUInt64))
  | 0, _, _, hi => absurd hi (by omega)
  | j + 1, s, 0, _ => by simp [spnWs]
  | j + 1, s, i + 1, hi => by
    simp only [spnWs, List.getElem?_cons_succ]
    rw [spnWs_get m j (s + 1) i (by omega)]
    congr 2
    rw [UInt64.add_assoc]; congr 1
    apply UInt64.toNat_inj.mp; simp [Nat.toUInt64, UInt64.toNat_add]; omega

/-- **What `spn_to_iw` does**: the stack words written into the pool from `d` on. -/
theorem s2iW_wr : ∀ (k : Nat) (m m' : Mem) (d s l : Word) (r : List Word),
    s2iW k m d s l = some (r, m') → m' = wrIW m d (spnWs m s l.toNat) := by
  intro k
  induction k with
  | zero => intro m m' d s l r h; simp [s2iW] at h
  | succ k ih =>
    intro m m' d s l r h
    by_cases hl : l = 0
    · rw [s2iW_nil k m d s l hl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl; rfl
    rw [s2iW_cons k m d s l hl] at h
    obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K (K := (ntBW · _)) h rfl; rw [bW_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hl0 : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
    have hl1 : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp
    rw [ih _ _ _ _ _ _ h1, hl1,
      spnWs_congr (Mem.arr64_set64_ne _ _ _ _ _ (by decide)) (s + 1) (l.toNat - 1)]
    obtain ⟨j, hj⟩ : ∃ j, l.toNat = j + 1 := ⟨l.toNat - 1, by omega⟩
    rw [hj]
    simp only [spnWs, wrIW, spW, Nat.add_sub_cancel]

/-- **The adapter `get_app_args_f(f, e)` is its model `gaaAdW`** (generated), over its callees' runs. -/
l_model gaaAd_spec (p : Prog) (hp : p.lookup "get_app_args_f" = some getAppArgsFL)
    (ha : p.lookup "iw_alloc" = some iwAlloc) (hs : p.lookup "spn_to_iw" = some spnToIwL)
  fns [hp ↦ gaaAdW]
  specs [callW_spec p n "get_app_args", iwAlloc_specW p ha n, s2i_spec p hs n]
  grind [arena_grind] bind ntBW simp [CWF]

/-- `get_app_args_f` and its callees. -/
def gaaProg : Prog :=
  [("get_app_args_f", getAppArgsFL), ("get_app_args", getAppArgsL), ("app_count", appCountL),
   ("app_fill", appFillL), ("iw_alloc", iwAlloc), ("spn_to_iw", spnToIwL)]

def gaaFns : List FnName := gaaProg.map (·.1)

/-- `get_app_args_f` writes the stack, its top, the pool and its top. -/
theorem gaaProg_closed : closedA gaaProg [SPN, IW] [136, 200] gaaFns = true := by decide +kernel

abbrev GaaF (p : Prog) : Prop := ProgHas p gaaProg

/-- **The model of `get_app_args_f`.** -/
noncomputable def gaaF (m : Mem) (args : List Word) : Option (List Word × Mem) :=
  callF gaaProg "get_app_args_f" m args

theorem gaaF_spec0 (p : Prog) (hp : GaaF p) (n : Nat) (s₀ : St) (args : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "get_app_args_f" args
    ⦃fun r s' => LocEq s' s₀ ∧ gaaF s₀.mem args = some (r, s'.mem); ⊤⦄ :=
  callF_spec gaaProg_closed (hp.agree gaaFns) (by decide) n s₀ args

theorem gaaF_frame {m m' : Mem} {args r : List Word} (h : gaaF m args = some (r, m')) :
    MemFrame [SPN, IW] [136, 200] m m' := by
  obtain ⟨n, hc⟩ := callF_run h
  exact (run_memFrame gaaProg_closed (by decide) (run_of_callW hc)).1

/-- **`get_app_args_f`'s model refines `getAppArgs`** (replaces `IndStubs.getAppArgs_spec`):
`get_app_args` (`getAppArgs_refinesR`), the stack slice into a fresh pool slice
(`s2iW_wr`, `recPost_wr`, `slice_keep`), the stack top put back (`stageR_hi`). -/
theorem gaaF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (f e : Word) (he : H e) :
    RelW gaaF [f, e] (StageR dn vis fe) (getAppArgs f.toNat (decI e))
      (KeepPost dn vis fe (decRL (fun m => decHL m) 0)) := by
  intro m m' a r h hS
  obtain ⟨n, hc⟩ := callF_run h
  rcases n with _ | k
  · simp [callW_zero] at hc
  have c' := callW_model (M := fun mm => gaaAdW gaaProg (k + 1) mm f e)
    (fun s => gaaAd_spec gaaProg rfl rfl rfl (k + 1) s f e) hc
  simp only [gaaAdW] at c'
  obtain ⟨hf, c'⟩ := of_ite_none c'
  have hf' : f = CWF := Decidable.not_not.mp hf
  subst hf'
  generalize htop : rdW (m.arr64 CTL) 136 = top at c'
  rcases c1 : callW gaaProg k "get_app_args" [e] m with _ | ⟨r1, m1⟩
  · rw [c1] at c'; simp at c'
  rw [c1, bW_some] at c'
  rcases ha : allocW m1 (r1.tail.headD 0) with _ | ⟨q, m2⟩
  · rw [ha] at c'; cases c'
  rw [ha, gaaAdW.k_iw_alloc.arm1] at c'
  rcases c3 : s2iW k m2 q (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r3, m3⟩
  · rw [c3] at c'; simp at c'
  rw [c3, bW_some] at c'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj c')
  -- `get_app_args`
  obtain ⟨t1, ht1, -, hfr1, hr0, xs, hrun, hsp, hb64⟩ := triple_of_callW
    (getAppArgs_refinesR gaaProg rfl rfl rfl k ⟨m, Locals.init []⟩ a hS.1.arena.1 e he) c1
  rw [ht1] at hfr1 hsp
  obtain ⟨hS1, hg1⟩ := stageR_hi hS hfr1 (by simp [SPN]) (by simp) (by decide) (by decide)
  -- the fresh slice
  have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
  obtain ⟨hq, rfl, hroom⟩ := allocW_facts ha hsz1
  generalize hn : r1.tail.headD 0 = cnt at hsp hb64 ha c3 hroom
  generalize ho : r1.headD 0 = o at hsp hb64 c3
  have hm3 := s2iW_wr k _ _ _ _ _ _ c3
  generalize hws : spnWs (allocMem m1 cnt) o cnt.toNat = ws at hm3
  have hspn2 : (allocMem m1 cnt).arr64 SPN = m1.arr64 SPN :=
    (allocMem_frame m1 cnt).1 SPN (by simp [SPN, IW]) (by decide)
  have hlen : cnt.toNat = ws.length := by rw [← hws, spnWs_length]
  have hrec := recPost_wr m1 ws cnt hlen hS1.2 (by
    have : q.toNat = iwTop m1 := by rw [hq]; rfl
    rw [← hlen, ← this]; exact hroom)
  rw [← hq, ← hm3] at hrec
  have hget : ∀ i, i < cnt.toNat → ws[i]? = some (spW m1 (o + i.toUInt64)) := by
    intro i hi; rw [← hws, spnWs_get _ _ _ _ hi]; simp only [spW, hspn2]
  have hlt : ∀ w ∈ ws, w.toNat < 2 ^ 32 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hi' : i < cnt.toNat := by rw [hlen]; exact hi
    have := hget i hi'
    rw [List.getElem?_eq_getElem hi] at this
    rw [Option.some.inj this]; exact hsp.lt i hi'
  have hxs : ws.map (decI : Word → EIdx) = xs := by
    apply List.ext_getElem
    · simp only [List.length_map]; rw [← hlen, ← hsp.size]; simp
    · intro i h1 h2
      simp only [List.getElem_map]
      have hi1 : i < ws.length := by simpa using h1
      have hi' : i < cnt.toNat := by rw [hlen]; exact hi1
      have := hget i hi'
      rw [List.getElem?_eq_getElem hi1] at this
      rw [Option.some.inj this]
      have hg := hsp.get i (by simpa using h2)
      simp only [List.getElem_toArray] at hg
      rw [hg]; rfl
  have hK := slice_keep (κ := .expr) hS1 hrec hlt hlen
  rw [hxs] at hK
  obtain ⟨hS3, hg3, hdec⟩ := hK
  -- the top put back
  obtain ⟨hS4, hg4⟩ := stageR_hi hS3 (MemFrame.setCtl m3 136 top) (by simp) (by simp) (by decide)
    (by decide)
  have hI4 : (m3.set64 CTL 136 top).arr64 IW = m3.arr64 IW := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have ht4 : iwTop (m3.set64 CTL 136 top) = iwTop m3 := by
    simp only [iwTop, rdW_set64]; simp
  refine ⟨xs, a, by rw [CWF_eq]; exact hrun, hS4, hg1.trans (hg3.trans hg4), ?_⟩
  refine ⟨?_, ?_⟩
  · rw [← hdec.1]; simp only [decHL, iwA, hI4]
  · rw [ht4]; exact hdec.2

end L.Ind
