import ConAgua.Arena.IndPos2
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.Env
import ConAgua.Arena.IndPosSpec
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndPartsSpec3
import ConAgua.Arena.Pins
import ConAgua.Arena.IndCopy2
import ConAgua.Arena.MemoLibRel
import ConAgua.Arena.StageInst1
import ConAgua.Arena.IndRealAbs

/-!
# Refinements of `IndPos2` (lane `induct`, worker E, round 2)

`nest_block_of` refines `nestBlockOf`, through `envFind_refines` (`ConAgua/Arena/Env.lean`) and a
decoding lemma for `decCI`'s `indInfo` arm at a known kind word (`decCI_kind3`, in the shape of
`Env.lean`'s `decCI_name`). `IndCaps.all` (like `IndCaps.ctors`, per `IndInstall.lean`'s own note)
is an `EREC` slice, read directly off the found constant's record (as module `IndPos`'s
`nest_container_ctors` already does for `caps.ctors`): `decCaps`'s `all` field is `hlist?` over the
SAME array `decCI` was given, which for a row found through `env_find` is `erA m` — so the twin's
`nestBlockOf fe C` decodes at `hslice? (erA m) (EREC.u64[q + 15]) (EREC.u64[q + 16])` where `q` is
the found row's record pointer, via `IndIface.lean`'s generic `hslice?`.

**A round-1 bug found while proving this**: the original `nestFrameMates.go` read its input slice
(`nestBlockOf`'s result) off `IW`, but it is `EREC`-resident. Fixed in `IndPos2.lean` (now reading
`EREC.u64[off + j]`), together with its `#guard` (now building its test block in `EREC`). Not
reproved this round: see the report (blocked on `sl_snoc`'s and `iw_copy`'s word models, not yet
in `IndLibSpec.lean`, and — for `nestWalkStack` — on `nest_ctx_hi_at`'s refinement, not yet proved
by module `IndPos`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `decCI`'s `indInfo` arm, at a known kind word -/

/-- **A decoded record at kind word `3` is `indInfo`**, with its caps: `decCI`'s match only
reaches the `.indInfo` arm from `nat? a p = some 3` (`Env.lean`'s `decCI_name` destructures the
same match generically, for the name field). -/
theorem decCI_kind3 {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) (hk : nat? a p = some 3) :
    ∃ cv caps, ci = .indInfo cv caps ∧ decCaps a dn (p + 5) = some caps := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk', h⟩ := h
  have hk3 : k = 3 := Option.some.inj (hk'.symm.trans hk)
  subst hk3
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨cv, hcv, caps, hcaps, rfl⟩ := h
  exact ⟨cv, caps, rfl, hcaps⟩

/-- The contrapositive: an `indInfo` record's kind word is `3`. -/
theorem decCI_indInfo_kind {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a dn p = some (.indInfo cv caps)) :
    nat? a p = some 3 := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  rw [hk]
  congr 1
  match k, h with
  | 0, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 1, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 2, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 3, h => rfl
  | 4, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 5, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | 6, h => simp_all [Option.bind_eq_some_iff, Option.some.injEq]
  | (_ + 7), h => simp_all

/-- A word read off `EREC` at a `Nat` position, as `nat?` decodes it. -/
theorem erN_rdW {m : Mem} {q : Nat} {k : Nat} (h : nat? (erA m) q = some k) (hq : q < 2 ^ 64) :
    rdW (m.arr64 EREC) (UInt64.ofNat q) = UInt64.ofNat k := by
  simp only [nat?, erA, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  have hqq : (UInt64.ofNat q).toNat = q := by simp; omega
  simp only [rdW, hqq, hw, Option.getD_some, UInt64.ofNat_toNat]

/-- A `nat?`-decoded value is below `2 ^ 64` (it is some word's `toNat`). -/
theorem nat?_lt {a : Array Word} {i k : Nat} (h : nat? a i = some k) : k < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, -, rfl⟩ := h
  exact w.toNat_lt

/-- `hlist?`'s two-word header, unfolded. -/
theorem hlist?_some {k : IdxKind} {a : Array Word} {i : Nat} {xs : List (Idx k)}
    (h : hlist? a i = some xs) :
    ∃ o l, nat? a i = some o ∧ nat? a (i + 1) = some l ∧ hslice? a o l = some xs := by
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, l, hl, h⟩ := h
  exact ⟨o, l, ho, hl, h⟩

/-! ## `nest_block_of` refines `nestBlockOf`: the pure fact -/

/-- **What `nest_block_of` computes, as a function of `env_find`'s result**: the key lemma,
proved purely over `Mem`/`Word`, outside the L execution.

Two extra hypotheses, beyond `hfound`, are needed and not discharged this round (see the
report): `hwf` — the found record, if its kind word is `3`, fully decodes as `indInfo` (true for
any row actually installed through `IFEnv.push`, by `EnvR`'s own `consts` invariant — relating
that to a *found* row's pointer needs more of `Env.lean`'s machinery than this round reaches) —
and `hqb`, a slack bound on pointers so `q + 15`/`q + 16` do not wrap (true for any real `EREC`,
whose size is nowhere near `2 ^ 64`). -/
theorem nestBlockOf_key {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q)
    (hwf : rdW (m.arr64 EREC) q = (3 : Word) →
      ∃ cv caps, decCI (erecP m) dn q.toNat = some (.indInfo cv caps))
    (hqb : rdW (m.arr64 EREC) q = (3 : Word) → q.toNat + 16 < 2 ^ 64) :
    hslice? (erA m)
        (if found = 0 then (0 : Word) else if rdW (m.arr64 EREC) q = 3 then
          rdW (m.arr64 EREC) (q + 15) else 0).toNat
        (if found = 0 then (0 : Word) else if rdW (m.arr64 EREC) q = 3 then
          rdW (m.arr64 EREC) (q + 16) else 0).toNat
      = some (nestBlockOf fe (decI c)) := by
  rw [nestBlockOf]
  unfold decFound at hfound
  by_cases h0 : found = 0
  · simp only [h0, hfound, ite_true]
    simp [hslice?]
  · simp only [h0, ite_false] at hfound ⊢
    have hqlt : q.toNat < 2 ^ 64 := q.toNat_lt
    have hsize : UInt64.size = 2 ^ 64 := rfl
    by_cases hk3 : rdW (m.arr64 EREC) q = (3 : Word)
    · obtain ⟨cv, caps, hci0⟩ := hwf hk3
      have hqb := hqb hk3
      rw [hci0] at hfound
      have hci := (erecP_ext m).decCI hci0
      simp only [hfound, if_pos hk3]
      obtain ⟨cv', caps', he, hcaps⟩ := decCI_kind3 hci (decCI_indInfo_kind hci)
      obtain rfl : caps = caps' := by
        have := he.symm; simp only [IConstantInfo.indInfo.injEq] at this; exact this.2.symm
      simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, vall, hvall, _, _, hcapseq⟩ := hcaps
      obtain ⟨actors, -, heq⟩ := hcapseq
      have hallcaps : caps.all = vall := by
        have h' := Option.some.inj heq; rw [← h']
      obtain ⟨o, l, ho, hl, hslc⟩ := hlist?_some hvall
      have ho' : nat? (erA m) (q.toNat + 15) = some o := by
        have heq2 : q.toNat + 5 + 10 = q.toNat + 15 := by omega
        rwa [heq2] at ho
      have hl' : nat? (erA m) (q.toNat + 16) = some l := by
        have heq2 : q.toNat + 5 + 10 + 1 = q.toNat + 16 := by omega
        rwa [heq2] at hl
      have hwo : rdW (m.arr64 EREC) (q + 15) = UInt64.ofNat o := by
        have e15 : (q + 15 : Word) = UInt64.ofNat (q.toNat + 15) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add]
          have hA : (UInt64.ofNat (q.toNat + 15)).toNat = q.toNat + 15 :=
            UInt64.toNat_ofNat_of_lt' (by omega)
          have hB : (15 : Word).toNat = 15 := by decide
          rw [hA, hB]
          omega
        rw [e15]; exact erN_rdW ho' (by omega)
      have hwl : rdW (m.arr64 EREC) (q + 16) = UInt64.ofNat l := by
        have e16 : (q + 16 : Word) = UInt64.ofNat (q.toNat + 16) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add]
          have hA : (UInt64.ofNat (q.toNat + 16)).toNat = q.toNat + 16 :=
            UInt64.toNat_ofNat_of_lt' (by omega)
          have hB : (16 : Word).toNat = 16 := by decide
          rw [hA, hB]
          omega
        rw [e16]; exact erN_rdW hl' (by omega)
      rw [hwo, hwl]
      have hoo : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' (nat?_lt ho')
      have hll : (UInt64.ofNat l).toNat = l := UInt64.toNat_ofNat_of_lt' (nat?_lt hl')
      rw [hoo, hll, hallcaps]
      exact hslc
    · simp only [if_neg hk3]
      have hnind : ∀ cv caps, fe.find? (decI c) ≠ some (.indInfo cv caps) := by
        intro cv caps hfc
        rw [hfound] at hfc
        have hfc := (erecP_ext m).decCI hfc
        exact hk3 (by
          have hk := decCI_indInfo_kind hfc
          have := erN_rdW hk hqlt
          rwa [UInt64.ofNat_toNat] at this)
      rcases hm : fe.find? (decI c) with _ | ci; · simp [hslice?]
      cases ci with
      | indInfo cv caps => exact absurd hm (hnind cv caps)
      | axiomInfo _ => simp [hslice?]
      | defnInfo _ _ _ => simp [hslice?]
      | thmInfo _ => simp [hslice?]
      | ctorInfo _ _ _ => simp [hslice?]
      | recInfo _ _ _ _ => simp [hslice?]

/-- `nat?` reads inside the array. -/
theorem nat?_idx {a : Array Word} {i k : Nat} (h : nat? a i = some k) : i < a.size := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hw).1

/-- An `indInfo` record is fully inside the array it decodes from. -/
theorem decCI_indInfo_bound {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI a dn p = some (.indInfo cv caps)) :
    p + 16 < a.size := by
  obtain ⟨cv', caps', he, hcaps⟩ := decCI_kind3 h (decCI_indInfo_kind h)
  simp only [decCaps, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, vall, hvall, _, _, hcapseq⟩ := hcaps
  obtain ⟨o, l, ho, hl, hs⟩ := hlist?_some hvall
  have := nat?_idx hl
  omega

theorem EnvR.row_dec {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) :
    rowTag w ≤ 2 → rowC m w ≠ 0 → ∃ ci, decCI (erecP m) dn (rowP m w).toNat = some ci := by
  intro ht h0
  have hk := h.keys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.vals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  have hv := hv h0
  simp only [rowW, h0, ite_false, Option.map_some] at hk
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => simp [e] at hk
  | some r =>
    simp only [e, Option.map_some] at hv
    exact ⟨r.2, hv.symm⟩

/-- `env_find`, with: a found row decodes. -/
theorem envFind_refines' (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis w : Word)
    (hE : EnvR dn s₀.mem vis fe) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      fe.find? (decI w) = decFound dn s₀.mem (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP s₀.mem) dn (r.tail.headD 0).toNat = some ci); ⊤⦄ := by
  have key := EnvR.find?_eq hE w hw
  have key2 := EnvR.row_dec hE w hw
  simp only [invoke_eq _ hp, callFn, envFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, envRowGet_spec p hx hg n] <;>
      finish [decFound]

/-- A found `indInfo` row, seen through `erecP`, gives the pointer bound. -/
theorem erecP_size_lt (m : Mem) : (erecP m).size < 2 ^ 64 := by
  have h : (erecP m).size ≤ erecTop m := by simp [erecP]; exact Nat.min_le_left _ _
  have := (rdW (m.arr64 CTL) 129).toNat_lt
  simp only [erecTop] at h
  omega

theorem blk_none {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found = 0) :
    hslice? (erA m) (0 : Word).toNat (0 : Word).toNat = some (nestBlockOf fe (decI c)) := by
  have : fe.find? (decI c) = none := by rw [hfound]; simp [decFound, h0]
  simp [nestBlockOf, this, hslice?]

theorem blk_nok3 {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found ≠ 0)
    (hk : rdW (m.arr64 EREC) q ≠ 3) :
    hslice? (erA m) (0 : Word).toNat (0 : Word).toNat = some (nestBlockOf fe (decI c)) := by
  have := nestBlockOf_key found q hfound (fun h => absurd h hk) (fun h => absurd h hk)
  simpa [h0, hk] using this

theorem blk_k3 {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found ≠ 0)
    (hex : ∃ ci, decCI (erecP m) dn q.toNat = some ci) (hk : rdW (m.arr64 EREC) q = 3) :
    hslice? (erA m) (rdW (m.arr64 EREC) (q + 15)).toNat (rdW (m.arr64 EREC) (q + 16)).toNat =
      some (nestBlockOf fe (decI c)) := by
  obtain ⟨ci, hci⟩ := hex
  obtain ⟨k, hkn⟩ : ∃ k, nat? (erecP m) q.toNat = some k := by
    simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
    obtain ⟨k, hk, -⟩ := hci
    exact ⟨k, hk⟩
  have hkn' : nat? (erA m) q.toNat = some k := by
    simp only [nat?, Option.map_eq_some_iff] at hkn ⊢
    obtain ⟨w, hw, rfl⟩ := hkn
    exact ⟨w, erecP_get hw, rfl⟩
  have hrd := erN_rdW hkn' q.toNat_lt
  rw [UInt64.ofNat_toNat] at hrd
  have hk3 : k = 3 := by
    have h1 : UInt64.ofNat k = 3 := by rw [← hrd]; exact hk
    have h2 := congrArg UInt64.toNat h1
    rw [UInt64.toNat_ofNat_of_lt' (nat?_lt hkn')] at h2
    simpa using h2
  subst hk3
  obtain ⟨cv, caps, hI, -⟩ := decCI_kind3 hci hkn
  subst hI
  have hb := decCI_indInfo_bound hci
  have hsz := erecP_size_lt m
  have := nestBlockOf_key found q hfound (fun _ => ⟨cv, caps, hci⟩) (fun _ => by omega)
  simpa [h0, hk] using this

theorem blk_k3' {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {c : Word} {m : Mem}
    (found q : Word) (hfound : fe.find? (decI c) = decFound dn m found q) (h0 : found ≠ 0)
    (hex : ∃ ci, decCI (erecP m) dn q.toNat = some ci) (hk : rdW (m.arr64 EREC) q = 3)
    (h15 : (q + 15).toNat < (m.arr64 EREC).size) (h16 : (q + 16).toNat < (m.arr64 EREC).size) :
    hslice? (erA m) ((m.arr64 EREC)[(q + 15).toNat]'h15).toNat ((m.arr64 EREC)[(q + 16).toNat]'h16).toNat =
      some (nestBlockOf fe (decI c)) := by
  have := blk_k3 found q hfound h0 hex hk
  rwa [rdW_eq _ _ _ rfl h15, rdW_eq _ _ _ rfl h16] at this

section blockof
variable (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hf : p.lookup "env_find" = some envFindL)
    (hp : p.lookup "nest_block_of" = some nestBlockOfL)
include hx hg hf hp

/-- **`nest_block_of` refines `nestBlockOf`**: the result is the `IndCaps.all` slice of `EREC`. -/
@[refines ConRon.Arena.nestBlockOf]
theorem nestBlockOf_refines (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv}
    (vis c : Word) (hE : EnvR dn s₀.mem vis fe) (hc : c.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_block_of" [vis, c]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      hslice? (erA s₀.mem) (r.headD 0).toNat (r.tail.headD 0).toNat = some (nestBlockOf fe (decI c));
      ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestBlockOfL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_refines' p hx hg hf n (dn := dn) (fe := fe)] <;> finish (gen := 20) [blk_none, blk_nok3, blk_k3', rdW_eq]

end blockof

/-! ## `nest_ctor_entry_strip`, `nest_ctor_entry` -/

def stripK (ciq nPc nF : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0, 0], m1)
    else some ([1, ciq + 1, nPc, nF, r.tail.tail.tail.headD 0], m1)

def stripW (m : Mem) (ciq : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 EREC) ciq ≠ 4 then some ([0, 0, 0, 0, 0], m)
  else if rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5) then none
  else stripK ciq (rdW (m.arr64 EREC) (ciq + 5)) (rdW (m.arr64 EREC) (ciq + 6))
    (stripF 6 m [rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6),
      rdW (m.arr64 EREC) (ciq + 1 + 3)])

section arms
variable (m m1 : Mem) (ciq nPc nF : Word) (r : List Word)
theorem stripW_notctor (h : rdW (m.arr64 EREC) ciq ≠ 4) : stripW m ciq = some ([0, 0, 0, 0, 0], m) := by
  simp [stripW, h]
theorem stripW_wrap (h : rdW (m.arr64 EREC) ciq = 4)
    (h2 : rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5)) :
    stripW m ciq = none := by
  simp [stripW, h, h2]
theorem stripW_ctor (h : rdW (m.arr64 EREC) ciq = 4)
    (h2 : ¬ rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5)) :
    stripW m ciq =
    stripK ciq (rdW (m.arr64 EREC) (ciq + 5)) (rdW (m.arr64 EREC) (ciq + 6))
    (stripF 6 m [rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6),
      rdW (m.arr64 EREC) (ciq + 1 + 3)]) := by
  unfold stripW; rw [if_neg (by simp [h]), if_neg h2]
theorem stripK_fail (h : r.headD 0 = 0) : stripK ciq nPc nF (some (r, m1)) = some ([0, 0, 0, 0, 0], m1) := by
  simp only [stripK]; rw [if_pos h]
theorem stripK_ok (h : r.headD 0 ≠ 0) :
    stripK ciq nPc nF (some (r, m1)) = some ([1, ciq + 1, nPc, nF, r.tail.tail.tail.headD 0], m1) := by
  simp only [stripK]; rw [if_neg h]
end arms
grind_pattern [ind_grind] stripW_notctor => stripW m ciq
grind_pattern [ind_grind] stripW_wrap => stripW m ciq
grind_pattern [ind_grind] stripW_ctor => stripW m ciq
grind_pattern [ind_grind] stripK_fail => stripK ciq nPc nF (some (r, m1))
grind_pattern [ind_grind] stripK_ok => stripK ciq nPc nF (some (r, m1))

theorem nestCtorEntryStrip_spec (p : Prog) (hp : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hst : StripProg p) (n : Nat) (s₀ : St) (ciq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry_strip" [ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ stripW s₀.mem ciq = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorEntryStrip]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stripPis_specF p hst n] <;> finish (gen := 20)

/-! ### Reading `EREC` records at a word index -/

theorem erec_rd {m : Mem} {w : Word} {c : Nat} {v : Word} (h : (erecP m)[w.toNat + c]? = some v)
    (hc : c < 2 ^ 64) : rdW (m.arr64 EREC) (w + UInt64.ofNat c) = v := by
  have hlt := (Array.getElem?_eq_some_iff.mp h).1
  have hsz := erecP_size_lt m
  have e : (w + UInt64.ofNat c).toNat = w.toNat + c := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hc]; exact Nat.mod_eq_of_lt (by omega)
  simp only [rdW, e, erecP_get h, Option.getD_some]

theorem erec_nat {m : Mem} {w : Word} {c : Nat} {k : Nat} (h : nat? (erecP m) (w.toNat + c) = some k)
    (hc : c < 2 ^ 64) : rdW (m.arr64 EREC) (w + UInt64.ofNat c) = UInt64.ofNat k ∧ k < 2 ^ 64 := by
  simp only [nat?, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  exact ⟨by rw [erec_rd hv hc]; simp, v.toNat_lt⟩

theorem erec_hd {m : Mem} {w : Word} {c : Nat} {k : IdxKind} {x : Idx k}
    (h : hd? (erecP m) (w.toNat + c) = some x) (hc : c < 2 ^ 64) :
    ∃ v, rdW (m.arr64 EREC) (w + UInt64.ofNat c) = v ∧ v.toNat < 2 ^ 32 ∧ decI v = x := by
  obtain ⟨v, hv, hlt, rfl⟩ := hd?_some h
  exact ⟨v, erec_rd hv hc, hlt, rfl⟩

/-- A record's kind word and, for a constructor, its fields. -/
theorem decCI_kind_cases {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
    ∃ k, nat? a p = some k ∧
      ((k = 4 ∧ ∃ cv nPc nF, ci = .ctorInfo cv nPc nF ∧ decCV a (p + 1) = some cv ∧
          nat? a (p + 5) = some nPc ∧ nat? a (p + 6) = some nF) ∨
       (k ≠ 4 ∧ ∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF)) := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  refine ⟨k, hk, ?_⟩
  match k, h with
  | 0, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 1, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 2, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 3, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 4, h =>
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, a1, h1, b1, h2, rfl⟩ := h
    left; exact ⟨rfl, cv, a1, b1, rfl, hcv, h1, h2⟩
  | 5, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | 6, h => right; refine ⟨by decide, fun cv n f hc => ?_⟩; subst hc; simp_all [Option.bind_eq_some_iff]
  | (_ + 7), h => simp at h

theorem erecP_ext_grow {m m' : Mem} (hg : IWGrow m m') : ArrExt (erecP m) (erA m') := by
  intro i v hv
  have hlt : i < erTop m := by
    have := (Array.getElem?_eq_some_iff.mp hv).1
    simp only [erecP, Array.size_extract, erecTop] at this
    simp only [erTop]; omega
  rw [erA, hg.2.2.2 i hlt]
  exact erecP_get hv

theorem decCV_type {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    hd? a (q + 3) = some cv.type := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, hd, hq⟩ := h
  rw [← Option.some.inj hq]; exact hd

theorem drop3_eq (r : List Word) : r.drop 3 = r.tail.tail.tail := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩ <;> simp

/-- What `nest_ctor_entry_strip` returns, against the twin's `stripPis` result. -/
def StripOut (m : Mem) (r : List Word) (ciq : Word) (cv : IConstantVal) (nPc nF : Nat) :
    Option (List EIdx × EIdx) → Prop
  | none => r = [0, 0, 0, 0, 0]
  | some (_, b) => ∃ w, r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF, w] ∧ w.toNat < 2 ^ 32 ∧
      decI w = b ∧ decCV (erecP m) (ciq.toNat + 1) = some cv

theorem stripW_ok {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {ciq : Word} {r : List Word} {ci : IConstantInfo}
    (h : stripW m ciq = some (r, m')) (hS : StageR dn vis fe m a)
    (hci : decCI (erecP m) dn ciq.toNat = some ci) :
    (∀ cv nPc nF, ci = .ctorInfo cv nPc nF → nPc + nF < 2 ^ 64 ∧
      ∃ x a', (stripPis (nPc + nF) cv.type).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ StripOut m r ciq cv nPc nF x) ∧
    ((∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF) → r = [0, 0, 0, 0, 0] ∧ m' = m) := by
  obtain ⟨k, hk, hcases⟩ := decCI_kind_cases hci
  have hk0 := erec_nat (m := m) (w := ciq) (c := 0) (by simpa using hk) (by decide)
  have e0 : UInt64.ofNat 0 = 0 := rfl
  rw [e0, UInt64.add_zero] at hk0
  rcases hcases with ⟨rfl, cv, nPc, nF, rfl, hcv, hnP, hnF⟩ | ⟨hne, hnc⟩
  · have hker : rdW (m.arr64 EREC) ciq = 4 := by rw [hk0.1]; rfl
    have hP := erec_nat (m := m) (w := ciq) (c := 5) hnP (by decide)
    have hF := erec_nat (m := m) (w := ciq) (c := 6) hnF (by decide)
    have hP' : rdW (m.arr64 EREC) (ciq + 5) = UInt64.ofNat nPc := hP.1
    have hF' : rdW (m.arr64 EREC) (ciq + 6) = UInt64.ofNat nF := hF.1
    by_cases hw : rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6) < rdW (m.arr64 EREC) (ciq + 5)
    · rw [stripW_wrap m ciq hker hw] at h; cases h
    have hsum : nPc + nF < 2 ^ 64 := by
      rw [hP', hF', UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hP.2,
        UInt64.toNat_ofNat_of_lt' hF.2] at hw
      have := hP.2; have := hF.2
      omega
    rw [stripW_ctor m ciq hker hw] at h
    have hty := decCV_type hcv
    rw [Nat.add_assoc] at hty
    obtain ⟨wt, hwt, hwtlt, hwtd⟩ := erec_hd (m := m) (w := ciq) (c := 1 + 3) hty (by decide)
    have e13 : ciq + 1 + 3 = ciq + UInt64.ofNat (1 + 3) := by rw [UInt64.add_assoc]; rfl
    rw [e13, hwt, hP', hF'] at h
    refine ⟨?_, fun hh => absurd rfl (hh cv nPc nF)⟩
    intro cv' nPc' nF' hc
    obtain ⟨rfl, rfl, rfl⟩ : cv = cv' ∧ nPc = nPc' ∧ nF = nF' := by
      simp only [IConstantInfo.ctorInfo.injEq] at hc; exact ⟨hc.1, hc.2.1, hc.2.2⟩
    refine ⟨hsum, ?_⟩
    rcases hs : stripF 6 m [UInt64.ofNat nPc + UInt64.ofNat nF, wt] with _ | ⟨r1, m1⟩ <;> rw [hs] at h; · simp [stripK] at h
    have hk' : (UInt64.ofNat nPc + UInt64.ofNat nF).toNat = nPc + nF := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hP.2, UInt64.toNat_ofNat_of_lt' hF.2]
      exact Nat.mod_eq_of_lt hsum
    obtain ⟨x, a1, hrun, hS1, hg, hdec⟩ :=
      stripF_pis_ok dn vis fe (UInt64.ofNat nPc + UInt64.ofNat nF) wt hwtlt m m1 a r1 hs hS
    rw [hk', hwtd] at hrun
    refine ⟨x, a1, hrun, ?_⟩
    by_cases hz : r1.headD 0 = 0
    · rw [stripK_fail _ _ _ _ _ hz] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases x with
      | none => exact ⟨hS1, hg, rfl⟩
      | some xv =>
        obtain ⟨l, e⟩ := xv
        simp only [decOLE] at hdec
        exact absurd hdec.1 (by rw [hz]; decide)
    · rw [stripK_ok _ _ _ _ _ hz] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      cases x with
      | none => simp only [decOLE] at hdec; exact absurd hdec hz
      | some xv =>
        obtain ⟨l, e⟩ := xv
        simp only [decOLE, decW0E] at hdec
        obtain ⟨-, -, hel, hed⟩ := hdec
        refine ⟨hS1, hg, r1.tail.tail.tail.headD 0, rfl, ?_, ?_, ?_⟩
        · rwa [drop3_eq] at hel
        · rwa [drop3_eq] at hed
        · exact hcv
  · have hker : rdW (m.arr64 EREC) ciq ≠ 4 := by
      rw [hk0.1]; intro h4
      have := congrArg UInt64.toNat h4
      rw [UInt64.toNat_ofNat_of_lt' hk0.2] at this
      exact hne (by simpa using this)
    rw [stripW_notctor m ciq hker] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨fun cv nPc nF hc => absurd hc (hnc cv nPc nF), fun _ => ⟨rfl, rfl⟩⟩

/-! ### `viewConst` against `view` -/

theorem ETables.getConst_of_get (t : ETables) (i : EIdx) (ht : i.tag = ETag.const) (n : NIdx) (us : LsIdx)
    (h : t.get i = some (.const n us)) : t.getConst i = some (n, us) := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const] at h
  simp only [ETables.getConst]
  revert h
  cases t.consts.node? i.idxNat <;> simp_all [ETag.bvar, ETag.fvar, ETag.sort, ETag.const]

theorem EStore.viewConst_of_view (st : EStore) (i : EIdx) (ht : i.tag = ETag.const) (n : NIdx)
    (us : LsIdx) (h : st.view i = some (.const n us)) : st.viewConst i = some (n, us) := by
  unfold EStore.view at h
  unfold EStore.viewConst EStore.persGetConst
  split at h
  · rename_i hp; rw [if_pos hp]; exact ETables.getConst_of_get _ _ ht n us h
  · rename_i hp; rw [if_neg hp]
    split at h
    · rename_i hs; rw [if_pos hs]; exact ETables.getConst_of_get _ _ ht n us h
    · simp at h

/-! ### `nest_ctor_entry` -/

def entryK3 (C : Word) (r : List Word) (m2 : Mem) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else if v.tail.headD 0 ≠ C then some ([0, 0, 0, 0], m2)
  else some ([1, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], m2)

def entryK2 (C : Word) (r : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 >>> 28 ≠ 3 then some ([0, 0, 0, 0], m2)
    else entryK3 C r m2 (eViewW m2 (r2.headD 0))

def entryK1 (C : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0], m1)
    else entryK2 C r (gafF m1 [CWF, r.tail.tail.tail.tail.headD 0])

def entryW (m : Mem) (C ciq : Word) : Option (List Word × Mem) := entryK1 C (stripW m ciq)

section arms
variable (C : Word) (r r2 v : List Word) (m1 m2 : Mem)
theorem entryK3_miss (h : v ≠ []) (h2 : v.tail.headD 0 ≠ C) : entryK3 C r m2 v = some ([0, 0, 0, 0], m2) := by
  simp only [entryK3]; rw [if_neg h, if_pos h2]
theorem entryK3_hit (h : v ≠ []) (h2 : ¬ v.tail.headD 0 ≠ C) :
    entryK3 C r m2 v = some ([1, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], m2) := by
  simp only [entryK3]; rw [if_neg h, if_neg h2]
theorem entryK2_notconst (h : r2.headD 0 >>> 28 ≠ 3) : entryK2 C r (some (r2, m2)) = some ([0, 0, 0, 0], m2) := by
  simp only [entryK2]; rw [if_pos h]
theorem entryK2_const (h : ¬ r2.headD 0 >>> 28 ≠ 3) :
    entryK2 C r (some (r2, m2)) = entryK3 C r m2 (eViewW m2 (r2.headD 0)) := by
  simp only [entryK2]; rw [if_neg h]
theorem entryK1_fail (h : r.headD 0 = 0) : entryK1 C (some (r, m1)) = some ([0, 0, 0, 0], m1) := by
  simp only [entryK1]; rw [if_pos h]
theorem entryK1_ok (h : ¬ r.headD 0 = 0) :
    entryK1 C (some (r, m1)) = entryK2 C r (gafF m1 [CWF, r.tail.tail.tail.tail.headD 0]) := by
  simp only [entryK1]; rw [if_neg h]
end arms
grind_pattern [ind_grind] entryK3_miss => entryK3 C r m2 v
grind_pattern [ind_grind] entryK3_hit => entryK3 C r m2 v
grind_pattern [ind_grind] entryK2_notconst => entryK2 C r (some (r2, m2))
grind_pattern [ind_grind] entryK2_const => entryK2 C r (some (r2, m2))
grind_pattern [ind_grind] entryK1_fail => entryK1 C (some (r, m1))
grind_pattern [ind_grind] entryK1_ok => entryK1 C (some (r, m1))

theorem nestCtorEntry_spec (p : Prog) (hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "nest_ctor_entry" = some nestCtorEntry) (hst : StripProg p) (had : AdF p) (n : Nat) (s₀ : St)
    (C ciq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry" [C, ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ entryW s₀.mem C ciq = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorEntry]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtorEntryStrip_spec p hs hst n, gafF_spec p had n, eView_spec p hv n] <;>
      finish (gen := 20) [entryW]

theorem viewConst_run (h : EIdx) (a : AState) :
    (viewConst h).run a = .ok (a.store.viewConst h, a) := rfl

def EntryOut (m' : Mem) (r : List Word) (ciq : Word) : Option (IConstantVal × Nat × Nat) → Prop
  | none => r = [0, 0, 0, 0]
  | some (cv, nPc, nF) => r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF] ∧
      decCVp m' (ciq.toNat + 1) = some cv ∧ nPc + nF < 2 ^ 64

theorem tag_const_iff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.const) = decide (w >>> 28 = 3) := by
  have := decE_tag_eq w hw 3 (by decide)
  have e1 : (ETag.const : UInt32) = UInt32.ofNat 3 := rfl
  show ((decE w).tag == ETag.const) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

theorem getD1_eq (vl : List Word) : vl.getD 1 0 = vl.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl

theorem ETables.get_const (t : ETables) (i : EIdx) (ht : i.tag = ETag.const) (v : ENodeView)
    (h : t.get i = some v) : ∃ n us, v = .const n us := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const] at h
  cases hn : t.consts.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_const (st : EStore) (i : EIdx) (ht : i.tag = ETag.const) (v : ENodeView)
    (h : st.view i = some v) : ∃ n us, v = .const n us := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_const _ _ ht v h
  · split at h
    · exact ETables.get_const _ _ ht v h
    · simp at h

theorem decI_beq' {k : IdxKind} (v w : Word) (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) :
    ((decI v : Idx k) == decI w) = decide (v = w) := by
  by_cases h : v = w
  · subst h; simp
  · have : (decI v : Idx k) ≠ decI w := fun e => h (by
      rw [(decI_eq_iff v hv _).mp e]; exact decI_word_self w hw)
    simp [h, this]

theorem entryW_ok {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m' : Mem}
    {a : AState} {C ciq : Word} {r : List Word} {ci : IConstantInfo} (hC : H C)
    (h : entryW m C ciq = some (r, m')) (hS : StageR dn vis fe m a)
    (hci : decCI (erecP m) dn ciq.toNat = some ci) :
    ∃ x a', (ConRon.Arena.nestCtorEntry (decI C) ci).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ EntryOut m' r ciq x := by
  unfold entryW at h
  rcases h0 : stripW m ciq with _ | ⟨r0, m0⟩ <;> rw [h0] at h; · simp [entryK1] at h
  obtain ⟨hctor, hnon⟩ := stripW_ok h0 hS hci
  by_cases hc : ∃ cv nPc nF, ci = .ctorInfo cv nPc nF
  · obtain ⟨cv, nPc, nF, rfl⟩ := hc
    obtain ⟨hsum, x, a1, hrun1, hS1, hg1, hout⟩ := hctor cv nPc nF rfl
    cases x with
    | none =>
      simp only [StripOut] at hout
      subst hout
      rw [entryK1_fail _ _ _ (by rfl)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨none, a1, ?_, hS1, hg1, rfl⟩
      simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind]
      rw [hrun1]; rfl
    | some xv =>
      obtain ⟨l, b⟩ := xv
      obtain ⟨w, rfl, hwlt, hwd, hcvm0⟩ := hout
      rw [entryK1_ok _ _ _ (by simp)] at h
      simp only [List.tail_cons, List.headD_cons] at h
      rcases hg : gafF m0 [CWF, w] with _ | ⟨r2, m2⟩ <;> rw [hg] at h; · simp [entryK2] at h
      obtain ⟨x2, a2, hrun2, hS2, hg2, hlt2, hdec2⟩ :=
        gafF_ok dn vis fe CWF w hwlt m0 m2 a1 r2 hg hS1
      rw [CWF_eq, hwd] at hrun2
      have htagiff := tag_const_iff (r2.headD 0) hlt2
      rw [hdec2] at htagiff
      by_cases hk : r2.headD 0 >>> 28 ≠ 3
      · rw [entryK2_notconst _ _ _ _ hk] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl⟩
        simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind, hrun1, except_ok_bind, hrun2]
        have ht : ¬ (x2.tag == ETag.const) = true := by rw [htagiff]; simpa using hk
        simp only [ht, if_false]; rfl
      · rw [entryK2_const _ _ _ _ hk] at h
        have hk3 : r2.headD 0 >>> 28 = 3 := by simpa using hk
        cases hvl : eViewW m2 (r2.headD 0) with
        | nil => rw [hvl] at h; simp [entryK3] at h
        | cons g vt =>
          have hne : eViewW m2 (r2.headD 0) ≠ [] := by rw [hvl]; simp
          rw [hvl] at h
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m2 a2 hS2.1.arena.1 (r2.headD 0) hne
          rw [hvl] at hvr
          have hdE : decE (r2.headD 0) = x2 := hdec2
          have ht : x2.tag = ETag.const := by
            have := htagiff
            rw [show decide (r2.headD 0 >>> 28 = 3) = true by rw [hk3]; decide] at this
            simpa using this
          obtain ⟨n0, us0, rfl⟩ := EStore.view_const a2.store x2 ht v (hdE ▸ hv)
          simp only [ViewR, getD1_eq] at hvr
          obtain ⟨-, hn1, hn2, -, -⟩ := hvr
          simp only [List.tail_cons, List.headD_cons] at hn1 hn2
          have hview : a2.store.viewConst x2 = some (n0, us0) :=
            EStore.viewConst_of_view _ _ ht n0 us0 (hdE ▸ hv)
          have hbeq : (n0 == decI C) = decide (vt.headD 0 = C) := by
            rw [← hn2]; exact decI_beq' _ _ hn1 hC
          have htwin : (ConRon.Arena.nestCtorEntry (decI C) (.ctorInfo cv nPc nF)).run a =
              .ok (if vt.headD 0 = C then some (cv, nPc, nF) else none, a2) := by
            simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind, hrun1, except_ok_bind, hrun2, ht, beq_self_eq_true, if_true, viewConst_run, hview, hbeq]
            by_cases hcn : vt.headD 0 = C
            · simp only [hcn, decide_true, if_true]; rfl
            · simp only [hcn, decide_false]; rfl
          by_cases hcn : vt.headD 0 = C
          · rw [entryK3_hit _ _ _ _ (by simp) (by simpa using hcn)] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            refine ⟨_, a2, htwin, hS2, hg1.trans hg2, ?_⟩
            simp only [hcn, if_true, EntryOut]
            exact ⟨rfl, (erecP_ext_grow (hg1.trans hg2)).decCV hcvm0, hsum⟩
          · rw [entryK3_miss _ _ _ _ (by simp) (by simpa using hcn)] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            refine ⟨_, a2, htwin, hS2, hg1.trans hg2, ?_⟩
            simp only [hcn, if_false, EntryOut]
  · have hne : ∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF := fun cv n f hh => hc ⟨cv, n, f, hh⟩
    obtain ⟨rfl, rfl⟩ := hnon hne
    rw [entryK1_fail _ _ _ (by rfl)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    cases ci with
    | ctorInfo cv n f => exact absurd ⟨cv, n, f, rfl⟩ hc
    | _ => rfl

section census
variable (p : Prog) (hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "nest_ctor_entry" = some nestCtorEntry) (hst : StripProg p) (had : AdF p)
include hs hv hp hst had

/-- **`nest_ctor_entry` refines `nestCtorEntry`** (through the `get_app_fn` stub; L aborts where the
parameter and field counts' sum wraps, a capacity guard). -/
@[refines ConRon.Arena.nestCtorEntry]
theorem nestCtorEntry_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis C ciq : Word) (ci : IConstantInfo) (hC : H C)
    (hS : StageR dn vis fe s₀.mem a₀) (hci : decCI (erecP s₀.mem) dn ciq.toNat = some ci) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry" [C, ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestCtorEntry (decI C) ci) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestCtorEntry (decI C) ci) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      EntryOut s'.mem r ciq (AM.res (ConRon.Arena.nestCtorEntry (decI C) ci) a₀); ⊤⦄ := by
  refine triple_post (nestCtorEntry_spec p hs hv hp hst had n s₀ C ciq) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := entryW_ok hC hm hS hci
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-! ## `nest_res_head` -/

def resHeadK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => some ([if r.headD 0 >>> 28 = 1 then 1 else 0], m1)

def resHeadW (m : Mem) (e : Word) : Option (List Word × Mem) :=
  resHeadK (gafF m [CWF, e])

theorem resHeadK_some (r : List Word) (m1 : Mem) :
    resHeadK (some (r, m1)) = some ([if r.headD 0 >>> 28 = 1 then 1 else 0], m1) := rfl
grind_pattern [ind_grind] resHeadK_some => resHeadK (some (r, m1))

theorem nestResHead_spec (p : Prog) (hg : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_res_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ resHeadW s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hg, callFn, nestResHeadL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        gafF_spec p had n] <;> finish [resHeadW]

theorem resHeadW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem) (a : AState)
    (e : Word) (r : List Word) (he : H e) (h : resHeadW m e = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ a', (ConRon.Arena.nestResHead (decI e)).run a = .ok (r.headD 0 != 0, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  unfold resHeadW at h
  rcases hs : gafF m [CWF, e] with _ | ⟨r1, m1⟩ <;> rw [hs] at h; · simp [resHeadK] at h
  simp only [resHeadK, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a1, hrun, hS1, hg, hlt, hdec⟩ := gafF_ok dn vis fe CWF e he m m1 a r1 hs hS
  refine ⟨a1, ?_, hS1, hg⟩
  rw [CWF_eq] at hrun
  have htag : (x.tag == ETag.fvar) = decide (r1.headD 0 >>> 28 = 1) := by
    rw [← hdec]
    have := decE_tag_eq (r1.headD 0) hlt 1 (by decide)
    have e1 : (ETag.fvar : UInt32) = UInt32.ofNat 1 := rfl
    show ((decE (r1.headD 0)).tag == ETag.fvar) = _
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
    exact Iff.rfl
  simp only [ConRon.Arena.nestResHead, StateT.run_bind]
  rw [hrun]
  simp only [bind, Except.bind, pure, StateT.run_pure, StateT.pure, htag]
  show (StateT.pure (decide (r1.headD 0 >>> 28 = 1))).run a1 = _
  generalize r1.headD 0 = w
  by_cases hc : w >>> 28 = 1 <;> simp [hc, StateT.pure, StateT.run, pure, Except.pure]

/-- **`nest_res_head` refines `nestResHead`** (through the `get_app_fn` stub). -/
@[refines ConRon.Arena.nestResHead]
theorem nestResHead_refines (p : Prog) (hg : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis e : Word)
    (he : H e) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_res_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestResHead (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestResHead (decI e)) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      (r.headD 0 != 0) = AM.res (ConRon.Arena.nestResHead (decI e)) a₀; ⊤⦄ := by
  refine triple_post (nestResHead_spec p hg had n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hgr⟩ := resHeadW_ok dn fe vis _ _ a₀ e r he hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hgr, hres.symm⟩

/-! ## `inst_pis_with` -/

mutual
def instW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, ao, al, e =>
    if al = 0 then some ([1, e], m)
    else if e >>> 28 ≠ 6 then some ([0, 0], m)
    else instK1 n m ao al (eViewW m e)
def instK1 (n : Nat) (m : Mem) (ao al : Word) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else instK2 n ao al
    (i1F m [CWF, v.tail.tail.headD 0, rdW (m.arr64 IW) ao, 0])
def instK2 (n : Nat) (ao al : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rb, m1) => instK3 (instW n m1 (ao + 1) (al - 1) (rb.headD 0))
def instK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => some ([r.headD 0, r.tail.headD 0], m2)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (ao al e : Word) (v rb r : List Word)
theorem instW_nil (h : al = 0) : instW (n + 1) m ao al e = some ([1, e], m) := by simp [instW, h]
theorem instW_nopi (h : al ≠ 0) (h2 : e >>> 28 ≠ 6) : instW (n + 1) m ao al e = some ([0, 0], m) := by
  simp [instW, h, h2]
theorem instW_pi (h : al ≠ 0) (h2 : ¬ e >>> 28 ≠ 6) :
    instW (n + 1) m ao al e = instK1 n m ao al (eViewW m e) := by simp only [instW]; rw [if_neg h, if_neg h2]
theorem instK1_abort (h : v = []) : instK1 n m ao al v = none := by simp [instK1, h]
theorem instK1_ok (h : v ≠ []) : instK1 n m ao al v = instK2 n ao al
    (i1F m [CWF, v.tail.tail.headD 0, rdW (m.arr64 IW) ao, 0]) := by simp [instK1, h]
theorem instK2_some : instK2 n ao al (some (rb, m1)) = instK3 (instW n m1 (ao + 1) (al - 1) (rb.headD 0)) := by rw [instK2]
theorem instK3_some : instK3 (some (r, m2)) = some ([r.headD 0, r.tail.headD 0], m2) := by rw [instK3]
end arms
grind_pattern [ind_grind] instW_nil => instW (n + 1) m ao al e
grind_pattern [ind_grind] instW_nopi => instW (n + 1) m ao al e
grind_pattern [ind_grind] instW_pi => instW (n + 1) m ao al e
grind_pattern [ind_grind] instK1_abort => instK1 n m ao al v
grind_pattern [ind_grind] instK1_ok => instK1 n m ao al v
grind_pattern [ind_grind] instK2_some => instK2 n ao al (some (rb, m1))
grind_pattern [ind_grind] instK3_some => instK3 (some (r, m2))

theorem instPisWith_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "inst_pis_with" = some instPisWith) (hi1 : I1Prog p) (n : Nat) :
    ∀ (s₀ : St) (ao al e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_pis_with" [ao, al, e]
    ⦃fun r s' => LocEq s' s₀ ∧ instW n s₀.mem ao al e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ao al e
    rw [invoke_eq _ hp]; simp only [callFn, instPisWith]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ao al e
    simp only [invoke_eq _ hp, callFn, instPisWith]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        eView_spec p hv n, i1F_spec p hi1 n, ih] <;> finish (gen := 20)

theorem ETables.get_forall (t : ETables) (i : EIdx) (ht : i.tag = ETag.forallE) (v : ENodeView)
    (h : t.get i = some v) : ∃ ty b, v = .forallE ty b := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
    ETag.forallE] at h
  cases hn : t.foralls.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_forall (st : EStore) (i : EIdx) (ht : i.tag = ETag.forallE) (v : ENodeView)
    (h : st.view i = some v) : ∃ ty b, v = .forallE ty b := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_forall _ _ ht v h
  · split at h
    · exact ETables.get_forall _ _ ht v h
    · simp at h

theorem ETables.getBind_of_get (t : ETables) (i : EIdx) (ht : i.tag = ETag.forallE) (ty b : EIdx)
    (h : t.get i = some (.forallE ty b)) : t.getBind i = some (ty, b) := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
    ETag.forallE] at h
  simp only [ETables.getBind, ht, ETag.lam, ETag.forallE]
  cases hn : t.foralls.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h ⊢; simp [ETag.forallE, ETag.lam] at *; exact h

theorem EStore.viewBind_of_view (st : EStore) (i : EIdx) (ht : i.tag = ETag.forallE) (ty b : EIdx)
    (h : st.view i = some (.forallE ty b)) : st.viewBind i = some (ty, b) := by
  unfold EStore.view at h
  unfold EStore.viewBind EStore.persGetBind
  split at h
  · rename_i hp; rw [if_pos hp]; exact ETables.getBind_of_get _ _ ht ty b h
  · rename_i hp; rw [if_neg hp]
    split at h
    · rename_i hs; rw [if_pos hs]; exact ETables.getBind_of_get _ _ ht ty b h
    · simp at h

theorem tag_forall_iff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.forallE) = decide (w >>> 28 = 6) := by
  have := decE_tag_eq w hw 6 (by decide)
  have e1 : (ETag.forallE : UInt32) = UInt32.ofNat 6 := rfl
  show ((decE w).tag == ETag.forallE) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

theorem viewBind_run (h : EIdx) (a : AState) :
    (viewBind h).run a = .ok (a.store.viewBind h, a) := rfl

theorem instW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (ao al e : Word) (args : List EIdx) (r : List Word),
    instW n m ao al e = some (r, m') → StageR dn vis fe m a → H e →
    decHL m ao.toNat al.toNat = some args → ao.toNat + al.toNat < 2 ^ 64 →
    ao.toNat + al.toNat ≤ iwTop m →
    ∃ x a', (ConRon.Arena.instPisWith args (decI e)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x := by
  induction n with
  | zero => intro dn fe vis m m' a ao al e args r h; simp [instW] at h
  | succ n ih =>
    intro dn fe vis m m' a ao al e args r h hS he hdec hb hit
    by_cases hal : al = 0
    · rw [instW_nil n m ao al e hal] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : args = [] := by
        have h0 : al.toNat = 0 := by rw [hal]; rfl
        rw [h0] at hdec; simpa [decHL, hslice?] using hdec.symm
      subst this
      exact ⟨some (decI e), a, rfl, hS, IWGrow.refl _, rfl, he, rfl⟩
    · have hl1 : al.toNat = (al.toNat - 1) + 1 := by have := toNat_ne_zero' hal; omega
      rw [hl1, decHL, hslice?_succ] at hdec
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdec
      obtain ⟨xa, hxa, rest, hrest, rfl⟩ := hdec
      by_cases hpi : e >>> 28 ≠ 6
      · rw [instW_nopi n m ao al e hal hpi] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
        have ht : ¬ ((decI e : EIdx).tag == ETag.forallE) = true := by
          rw [tag_forall_iff e he]; simpa using hpi
        simp only [ConRon.Arena.instPisWith, ht, if_false]; rfl
      · rw [instW_pi n m ao al e hal hpi] at h
        have he6 : e >>> 28 = 6 := by simpa using hpi
        cases hvl : eViewW m e with
        | nil => rw [hvl] at h; simp [instK1] at h
        | cons g vt =>
          have hne : eViewW m e ≠ [] := by rw [hvl]; simp
          rw [hvl] at h
          rw [instK1_ok n m ao al _ (by simp)] at h
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.1.arena.1 e hne
          rw [hvl] at hvr
          have ht : (decE e).tag = ETag.forallE := by
            have h1 : ((decI e : EIdx).tag == ETag.forallE) = true := by
              rw [tag_forall_iff e he, he6]; decide
            exact beq_iff_eq.mp h1
          obtain ⟨ty, bd, rfl⟩ := EStore.view_forall a.store (decE e) ht v hv
          simp only [ViewR, getD1_eq] at hvr
          obtain ⟨-, -, -, hy1, hy2⟩ := hvr
          have hy2' : (vt.tail.headD 0).toNat < 2 ^ 32 := by simpa using hy1
          have hy3 : decE (vt.tail.headD 0) = bd := by simpa using hy2
          have hbind : a.store.viewBind (decE e) = some (ty, bd) :=
            EStore.viewBind_of_view _ _ ht ty bd hv
          have hlt0 : ao.toNat < 2 ^ 64 := ao.toNat_lt
          obtain ⟨wa, hwa_eq, hwa_lt, hwa_dec⟩ := iwH_rdW hxa hlt0
          rw [UInt64.ofNat_toNat] at hwa_eq
          rw [hwa_eq] at h
          simp only [List.tail_cons] at h
          rcases hst : i1F m [CWF, vt.tail.headD 0, wa, 0] with _ | ⟨rb, m1⟩ <;> rw [hst] at h; · simp [instK2] at h
          rw [instK2_some] at h
          obtain ⟨x1, a1, hrun1, hS1, hg1, hlt1, hdec1⟩ :=
            i1F_ok dn vis fe (vt.tail.headD 0) wa 0 hy2' m m1 a rb hst hS
          rcases hw : instW n m1 (ao + 1) (al - 1) (rb.headD 0) with _ | ⟨r3, m3⟩ <;> rw [hw] at h; · simp [instK3] at h
          rw [instK3_some] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          have hao1 : (ao + 1).toNat = ao.toNat + 1 := toNat_add_one' (by omega)
          have hal1 : (al - 1).toNat = al.toNat - 1 := toNat_sub_one' hal
          have hdec' : decHL m1 (ao + 1).toNat (al - 1).toNat = some rest := by
            rw [hao1, hal1, decHL_grow hg1 (by omega)]; exact hrest
          obtain ⟨x3, a3, hrun3, hS3, hg3, hout3⟩ :=
            ih dn fe vis m1 m3 a1 (ao + 1) (al - 1) (rb.headD 0) rest r3 hw hS1 hlt1 hdec'
              (by rw [hao1, hal1]; omega) (by rw [hao1, hal1]; have := hg1.1; omega)
          refine ⟨x3, a3, ?_, hS3, hg1.trans hg3, ?_⟩
          · have htag : ((decI e : EIdx).tag == ETag.forallE) = true := by
              rw [tag_forall_iff e he, he6]; decide
            simp only [ConRon.Arena.instPisWith, htag, if_true, StateT.run_bind]
            rw [show (decI e : EIdx) = decE e from rfl, viewBind_run, except_ok_bind, hbind]
            simp only [except_ok_bind, StateT.run_bind]
            rw [show (decI (vt.tail.headD 0) : EIdx) = bd from hy3, hwa_dec, CWF_eq,
              show (0 : Word).toNat = 0 from rfl] at hrun1
            rw [hrun1]
            simp only [except_ok_bind]
            rw [← hdec1]
            exact hrun3
          · cases x3 with
            | none =>
              simp only [decOE] at hout3 ⊢
              exact hout3
            | some e3 =>
              simp only [decOE, decW0E] at hout3 ⊢
              obtain ⟨h1, h2, h3⟩ := hout3
              exact ⟨h1, by simpa using h2, by simpa using h3⟩

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "inst_pis_with" = some instPisWith) (hi1 : I1Prog p)
include hv hp hi1

/-- **`inst_pis_with` refines `instPisWith`** (no stub left). -/
@[refines ConRon.Arena.instPisWith]
theorem instPisWith_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ao al e : Word) (args : List EIdx) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hdec : decHL s₀.mem ao.toNat al.toNat = some args)
    (hb : ao.toNat + al.toNat < 2 ^ 64) (hit : ao.toNat + al.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_pis_with" [ao, al, e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.instPisWith args (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.instPisWith args (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.instPisWith args (decI e)) a₀); ⊤⦄ := by
  refine triple_post (instPisWith_spec p hv hp hi1 n s₀ ao al e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := instW_ok n dn fe vis _ _ a₀ ao al e args r hm hS he hdec hb hit
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-- `inst_pis_with` keeps the `abstract1` memo. -/
theorem instW_afr (n : Nat) : ∀ (m m' : Mem) (ao al e : Word) (r : List Word), instW n m ao al e = some (r, m') →
    AFr m m' := by
  induction n with
  | zero => intro m m' ao al e r h; simp [instW] at h
  | succ n ih =>
    intro m m' ao al e r h
    simp only [instW, instK1, instK2.eq_def, instK3.eq_def] at h
    afr_auto h [i1F_afr, ih _ _ _ _ _ _]

/-! ## `close_telescope` -/

mutual
def closeW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, dO, dl, i, body =>
    if dl = 0 then some ([body], m)
    else closeK1 dO i (closeW n m (dO + 1) (dl - 1) (i + 1) body)
def closeK1 (dO i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => closeK2 dO (abF m1 [CWF, r1.headD 0, i, 0])
def closeK2 (dO : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => closeK3 (mkForallW m2 (rdW (m2.arr64 IW) dO) (r2.headD 0))
def closeK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => if 4294967296 ≤ r then none else some ([r], m3)
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (dO dl i body r : Word) (r1 r2 : List Word)
theorem closeW_nil (h : dl = 0) : closeW (n + 1) m dO dl i body = some ([body], m) := by simp [closeW, h]
theorem closeW_cons (h : dl ≠ 0) : closeW (n + 1) m dO dl i body =
    closeK1 dO i (closeW n m (dO + 1) (dl - 1) (i + 1) body) := by simp [closeW, h]
theorem closeK1_some : closeK1 dO i (some (r1, m1)) =
    closeK2 dO (abF m1 [CWF, r1.headD 0, i, 0]) := by rw [closeK1]
theorem closeK2_some : closeK2 dO (some (r2, m2)) =
    closeK3 (mkForallW m2 (rdW (m2.arr64 IW) dO) (r2.headD 0)) := by rw [closeK2]
theorem closeK3_big (h : 4294967296 ≤ r) : closeK3 (some (r, m3)) = none := by simp [closeK3, h]
theorem closeK3_ok (h : ¬ 4294967296 ≤ r) : closeK3 (some (r, m3)) = some ([r], m3) := by simp [closeK3, h]
end arms
grind_pattern [ind_grind] closeW_nil => closeW (n + 1) m dO dl i body
grind_pattern [ind_grind] closeW_cons => closeW (n + 1) m dO dl i body
grind_pattern [ind_grind] closeK1_some => closeK1 dO i (some (r1, m1))
grind_pattern [ind_grind] closeK2_some => closeK2 dO (some (r2, m2))
grind_pattern [ind_grind] closeK3_big => closeK3 (some (r, m3))
grind_pattern [ind_grind] closeK3_ok => closeK3 (some (r, m3))

section spec
variable (p : Prog) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hp : p.lookup "close_telescope" = some closeTelescope) (hab : AbF p)
include hd hpf hpp hpi hmk hp hab

theorem closeTelescope_spec (n : Nat) : ∀ (s₀ : St) (dO dl i body : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_telescope" [dO, dl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ closeW n s₀.mem dO dl i body = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ dO dl i body
    rw [invoke_eq _ hp]; simp only [callFn, closeTelescope]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ dO dl i body
    simp only [invoke_eq _ hp, callFn, closeTelescope]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        abF_spec p hab n, mkForall_spec p hd hpf hpp hpi hmk n, ih] <;>
      finish (gen := 20)

end spec

theorem rdW_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hi : x.toNat < iwTop m) :
    rdW (m'.arr64 IW) x = rdW (m.arr64 IW) x := by
  simp only [rdW, hg.2.2.1 _ hi]

theorem closeW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (dO dl i body : Word) (ds : List EIdx) (r : List Word),
    closeW n m dO dl i body = some (r, m') → StageR dn vis fe m a → H body →
    decHL m dO.toNat dl.toNat = some ds → dO.toNat + dl.toNat < 2 ^ 64 →
    dO.toNat + dl.toNat ≤ iwTop m → i.toNat + dl.toNat < 2 ^ 64 → AbsOK m →
    ∃ x a', (ConRon.Arena.closeTelescope ds i.toNat (decI body)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0E m' r x ∧ AbsOK m' := by
  induction n with
  | zero => intro dn fe vis m m' a dO dl i body ds r h; simp [closeW] at h
  | succ n ih =>
    intro dn fe vis m m' a dO dl i body ds r h hS hbody hdec hb hit hib hA
    by_cases hdl : dl = 0
    · rw [closeW_nil n m dO dl i body hdl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : ds = [] := by
        have h0 : dl.toNat = 0 := by rw [hdl]; rfl
        rw [h0] at hdec; simpa [decHL, hslice?] using hdec.symm
      subst this
      exact ⟨decI body, a, rfl, hS, IWGrow.refl _, ⟨hbody, rfl⟩, hA⟩
    · have hl1 : dl.toNat = (dl.toNat - 1) + 1 := by have := toNat_ne_zero' hdl; omega
      rw [hl1, decHL, hslice?_succ] at hdec
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdec
      obtain ⟨d, hdd, bs, hbs, rfl⟩ := hdec
      rw [closeW_cons n m dO dl i body hdl] at h
      have hdo1 : (dO + 1).toNat = dO.toNat + 1 := toNat_add_one' (by omega)
      have hdl1 : (dl - 1).toNat = dl.toNat - 1 := toNat_sub_one' hdl
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_one' (by omega)
      rcases hr1 : closeW n m (dO + 1) (dl - 1) (i + 1) body with _ | ⟨r1, m1⟩ <;> rw [hr1] at h; · simp [closeK1] at h
      rw [closeK1_some] at h
      obtain ⟨x1, a1, hrun1, hS1, hg1, ⟨hlt1, hdec1⟩, hA1⟩ :=
        ih dn fe vis m m1 a (dO + 1) (dl - 1) (i + 1) body bs r1 hr1 hS hbody
          (by rw [hdo1, hdl1]; exact hbs) (by rw [hdo1, hdl1]; omega) (by rw [hdo1, hdl1]; omega)
          (by rw [hi1, hdl1]; omega) hA
      rw [hi1] at hrun1
      rcases hr2 : abF m1 [CWF, r1.headD 0, i, 0] with _ | ⟨r2, m2⟩ <;> rw [hr2] at h; · simp [closeK2] at h
      rw [closeK2_some] at h
      obtain ⟨x2, a2, hrun2, ⟨hS2, hg2, hlt2, hdec2⟩, hA2⟩ :=
        abF_ok dn vis fe (r1.headD 0) i 0 hlt1 m1 m2 a1 r2 hr2 ⟨hS1, hA1⟩
      rw [CWF_eq, hdec1, show (0 : Word).toNat = 0 from rfl] at hrun2
      have hg12 := hg1.trans hg2
      have hd0 : dO.toNat < iwTop m := by omega
      obtain ⟨wd, hwd_eq, hwd_lt, hwd_dec⟩ := iwH_rdW hdd (by omega)
      rw [UInt64.ofNat_toNat] at hwd_eq
      rw [rdW_grow hg12 hd0, hwd_eq] at h
      rcases hm : mkForallW m2 wd (r2.headD 0) with _ | ⟨rr, m3⟩ <;> rw [hm] at h; · simp [closeK3] at h
      by_cases hbig : 4294967296 ≤ rr
      · rw [closeK3_big _ _ hbig] at h; simp at h
      · rw [closeK3_ok _ _ hbig] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨a3, hrun3, hS3, hg3⟩ := mkForall_stage hS2 wd (r2.headD 0) hm
        refine ⟨decE rr, a3, ?_, hS3, hg12.trans hg3, ⟨?_, rfl⟩, mkForallW_afr hm hA2⟩
        · simp only [ConRon.Arena.closeTelescope, StateT.run_bind]
          simp only [hrun1, except_ok_bind, StateT.run_bind, hrun2, ← hwd_dec, ← hdec2]
          exact hrun3
        · have : rr.toNat < 2 ^ 32 := by
            have : ¬ (4294967296 : Nat) ≤ rr.toNat := hbig
            omega
          simpa using this

section census
variable (p : Prog) (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hp : p.lookup "close_telescope" = some closeTelescope) (hab : AbF p)
include hd hpf hpp hpi hmk hp hab

/-- **`close_telescope` refines `closeTelescope`** (through the `abstract1_fast` stub and master's
`mk_forall`). -/
@[refines ConRon.Arena.closeTelescope]
theorem closeTelescope_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis dO dl i body : Word) (ds : List EIdx) (hbody : H body)
    (hS : StageR dn vis fe s₀.mem a₀) (hdec : decHL s₀.mem dO.toNat dl.toNat = some ds)
    (hb : dO.toNat + dl.toNat < 2 ^ 64) (hit : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hib : i.toNat + dl.toNat < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_telescope" [dO, dl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decW0E s'.mem r (AM.res (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (closeTelescope_spec p hd hpf hpp hpi hmk hp hab n s₀ dO dl i body) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout, hA'⟩ :=
    closeW_ok n dn fe vis _ _ a₀ dO dl i body ds r hm hS hbody hdec hb hit hib hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout, hA'⟩

end census

end L.Ind
