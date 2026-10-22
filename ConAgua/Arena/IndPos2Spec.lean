import ConAgua.Arena.IndPos2
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.Env
import ConAgua.Arena.IndPosSpec
import ConAgua.Arena.IndMaster
import ConAgua.Arena.Pins
import ConAgua.Arena.IndCopy2
import ConAgua.Arena.MemoLibRel

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

/-- `UInt64.ofNat` of a sum, when the `Nat` is small. -/
theorem ofNat_add_small (q k : Nat) (hq : q + k < 2 ^ 64) :
    (UInt64.ofNat q + UInt64.ofNat k : Word) = UInt64.ofNat (q + k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add]
  have h1 : (UInt64.ofNat q).toNat = q := by simp; omega
  have h2 : (UInt64.ofNat k).toNat = k := by simp; omega
  have h3 : (UInt64.ofNat (q + k)).toNat = q + k := by simp; omega
  rw [h1, h2, h3]
  omega

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
      rw [hfound]
      simp only [if_pos hk3]
      obtain ⟨cv', caps', he, hcaps⟩ := decCI_kind3 hci (decCI_indInfo_kind hci)
      obtain rfl : caps = caps' := by
        have := he.symm; simp only [IConstantInfo.indInfo.injEq] at this; exact this.2.symm
      rw [decCaps] at hcaps
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
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
      cases hm : fe.find? (decI c) with
      | none => simp [hslice?]
      | some ci =>
        cases ci with
        | indInfo cv caps => exact absurd hm (hnind cv caps)
        | axiomInfo _ => simp [hslice?]
        | defnInfo _ _ _ => simp [hslice?]
        | thmInfo _ => simp [hslice?]
        | ctorInfo _ _ _ => simp [hslice?]
        | recInfo _ _ _ _ => simp [hslice?]
        | projInfo _ => simp [hslice?]

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
  rw [decCaps] at hcaps
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcaps
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
  rw [invoke_eq _ hp]
  simp only [callFn, envFindL]
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
  rw [invoke_eq _ hp]
  simp only [callFn, nestBlockOfL]
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
  else stripK ciq (rdW (m.arr64 EREC) (ciq + 5)) (rdW (m.arr64 EREC) (ciq + 6))
    (stubM "strip_pis" m [rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6),
      rdW (m.arr64 EREC) (ciq + 1 + 3)])

section arms
variable (m m1 : Mem) (ciq nPc nF : Word) (r : List Word)
theorem stripW_notctor (h : rdW (m.arr64 EREC) ciq ≠ 4) : stripW m ciq = some ([0, 0, 0, 0, 0], m) := by
  simp [stripW, h]
theorem stripW_ctor (h : rdW (m.arr64 EREC) ciq = 4) : stripW m ciq =
    stripK ciq (rdW (m.arr64 EREC) (ciq + 5)) (rdW (m.arr64 EREC) (ciq + 6))
    (stubM "strip_pis" m [rdW (m.arr64 EREC) (ciq + 5) + rdW (m.arr64 EREC) (ciq + 6),
      rdW (m.arr64 EREC) (ciq + 1 + 3)]) := by
  simp [stripW, h]
theorem stripK_fail (h : r.headD 0 = 0) : stripK ciq nPc nF (some (r, m1)) = some ([0, 0, 0, 0, 0], m1) := by
  simp only [stripK]; rw [if_pos h]
theorem stripK_ok (h : r.headD 0 ≠ 0) :
    stripK ciq nPc nF (some (r, m1)) = some ([1, ciq + 1, nPc, nF, r.tail.tail.tail.headD 0], m1) := by
  simp only [stripK]; rw [if_neg h]
end arms
grind_pattern [ind_grind] stripW_notctor => stripW m ciq
grind_pattern [ind_grind] stripW_ctor => stripW m ciq
grind_pattern [ind_grind] stripK_fail => stripK ciq nPc nF (some (r, m1))
grind_pattern [ind_grind] stripK_ok => stripK ciq nPc nF (some (r, m1))

theorem nestCtorEntryStrip_spec (p : Prog) (hp : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (n : Nat) (s₀ : St) (ciq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry_strip" [ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ stripW s₀.mem ciq = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestCtorEntryStrip]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "strip_pis" n] <;> finish (gen := 20)


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
    (∀ cv nPc nF, ci = .ctorInfo cv nPc nF → nPc + nF < 2 ^ 64 →
      ∃ x a', (stripPis (nPc + nF) cv.type).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
        IWGrow m m' ∧ StripOut m r ciq cv nPc nF x) ∧
    ((∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF) → r = [0, 0, 0, 0, 0] ∧ m' = m) := by
  obtain ⟨k, hk, hcases⟩ := decCI_kind_cases hci
  have hk0 := erec_nat (m := m) (w := ciq) (c := 0) (by simpa using hk) (by decide)
  have e0 : UInt64.ofNat 0 = 0 := rfl
  rw [e0, UInt64.add_zero] at hk0
  rcases hcases with ⟨rfl, cv, nPc, nF, rfl, hcv, hnP, hnF⟩ | ⟨hne, hnc⟩
  · have hker : rdW (m.arr64 EREC) ciq = 4 := by rw [hk0.1]; rfl
    rw [stripW_ctor m ciq hker] at h
    have hP := erec_nat (m := m) (w := ciq) (c := 5) hnP (by decide)
    have hF := erec_nat (m := m) (w := ciq) (c := 6) hnF (by decide)
    have hty := decCV_type hcv
    rw [Nat.add_assoc] at hty
    obtain ⟨wt, hwt, hwtlt, hwtd⟩ := erec_hd (m := m) (w := ciq) (c := 1 + 3) hty (by decide)
    have e13 : ciq + 1 + 3 = ciq + UInt64.ofNat (1 + 3) := by rw [UInt64.add_assoc]; rfl
    have hP' : rdW (m.arr64 EREC) (ciq + 5) = UInt64.ofNat nPc := hP.1
    have hF' : rdW (m.arr64 EREC) (ciq + 6) = UInt64.ofNat nF := hF.1
    rw [e13, hwt, hP', hF'] at h
    refine ⟨?_, fun hh => absurd rfl (hh cv nPc nF)⟩
    intro cv' nPc' nF' hc hsum
    obtain ⟨rfl, rfl, rfl⟩ : cv = cv' ∧ nPc = nPc' ∧ nF = nF' := by
      simp only [IConstantInfo.ctorInfo.injEq] at hc; exact ⟨hc.1, hc.2.1, hc.2.2⟩
    cases hs : stubM "strip_pis" m [UInt64.ofNat nPc + UInt64.ofNat nF, wt] with
    | none => rw [hs] at h; simp [stripK] at h
    | some rm =>
      obtain ⟨r1, m1⟩ := rm
      rw [hs] at h
      have hk' : (UInt64.ofNat nPc + UInt64.ofNat nF).toNat = nPc + nF := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hP.2, UInt64.toNat_ofNat_of_lt' hF.2]
        exact Nat.mod_eq_of_lt hsum
      obtain ⟨x, a1, hrun, hS1, hg, hdec⟩ :=
        stripPis_spec dn vis fe (UInt64.ofNat nPc + UInt64.ofNat nF) wt hwtlt m m1 a r1 hs hS
      rw [hk', hwtd] at hrun
      refine ⟨x, a1, hrun, ?_⟩
      by_cases hz : r1.headD 0 = 0
      · rw [stripK_fail _ _ _ _ _ hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases x with
        | none => exact ⟨hS1, hg, rfl⟩
        | some xv =>
          obtain ⟨l, e⟩ := xv
          simp only [decOLE] at hdec
          exact absurd hdec.1 (by rw [hz]; decide)
      · rw [stripK_ok _ _ _ _ _ hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
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
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
    else entryK2 C r (stubM "get_app_fn" m1 [CWF, r.tail.tail.tail.tail.headD 0])

def entryW (m : Mem) (C ciq : Word) : Option (List Word × Mem) := entryK1 C (stripW m ciq)

section arms
variable (C : Word) (r r2 v : List Word) (m1 m2 : Mem)
theorem entryK3_abort (h : v = []) : entryK3 C r m2 v = none := by simp [entryK3, h]
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
    entryK1 C (some (r, m1)) = entryK2 C r (stubM "get_app_fn" m1 [CWF, r.tail.tail.tail.tail.headD 0]) := by
  simp only [entryK1]; rw [if_neg h]
end arms
grind_pattern [ind_grind] entryK3_abort => entryK3 C r m2 v
grind_pattern [ind_grind] entryK3_miss => entryK3 C r m2 v
grind_pattern [ind_grind] entryK3_hit => entryK3 C r m2 v
grind_pattern [ind_grind] entryK2_notconst => entryK2 C r (some (r2, m2))
grind_pattern [ind_grind] entryK2_const => entryK2 C r (some (r2, m2))
grind_pattern [ind_grind] entryK1_fail => entryK1 C (some (r, m1))
grind_pattern [ind_grind] entryK1_ok => entryK1 C (some (r, m1))

theorem nestCtorEntry_spec (p : Prog) (hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "nest_ctor_entry" = some nestCtorEntry) (n : Nat) (s₀ : St) (C ciq : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry" [C, ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ entryW s₀.mem C ciq = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestCtorEntry]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestCtorEntryStrip_spec p hs n, stubM_spec p "get_app_fn" n, eView_spec p hv n] <;>
      finish (gen := 20) [entryW]


theorem viewConst_run (h : EIdx) (a : AState) :
    (viewConst h).run a = .ok (a.store.viewConst h, a) := rfl

def EntryOut (m' : Mem) (r : List Word) (ciq : Word) : Option (IConstantVal × Nat × Nat) → Prop
  | none => r = [0, 0, 0, 0]
  | some (cv, nPc, nF) => r = [1, ciq + 1, UInt64.ofNat nPc, UInt64.ofNat nF] ∧
      decCVp m' (ciq.toNat + 1) = some cv

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
    (hci : decCI (erecP m) dn ciq.toNat = some ci)
    (hsum : ∀ cv nPc nF, ci = .ctorInfo cv nPc nF → nPc + nF < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.nestCtorEntry (decI C) ci).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ EntryOut m' r ciq x := by
  unfold entryW at h
  cases h0 : stripW m ciq with
  | none => rw [h0] at h; simp [entryK1] at h
  | some rm0 =>
    obtain ⟨r0, m0⟩ := rm0
    rw [h0] at h
    obtain ⟨hctor, hnon⟩ := stripW_ok h0 hS hci
    by_cases hc : ∃ cv nPc nF, ci = .ctorInfo cv nPc nF
    · obtain ⟨cv, nPc, nF, rfl⟩ := hc
      obtain ⟨x, a1, hrun1, hS1, hg1, hout⟩ := hctor cv nPc nF rfl (hsum cv nPc nF rfl)
      cases x with
      | none =>
        simp only [StripOut] at hout
        subst hout
        rw [entryK1_fail _ _ _ (by rfl)] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨none, a1, ?_, hS1, hg1, rfl⟩
        simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind]
        rw [hrun1]; rfl
      | some xv =>
        obtain ⟨l, b⟩ := xv
        obtain ⟨w, rfl, hwlt, hwd, hcvm0⟩ := hout
        rw [entryK1_ok _ _ _ (by simp)] at h
        simp only [List.tail_cons, List.headD_cons] at h
        cases hg : stubM "get_app_fn" m0 [CWF, w] with
        | none => rw [hg] at h; simp [entryK2] at h
        | some rm2 =>
          obtain ⟨r2, m2⟩ := rm2
          rw [hg] at h
          obtain ⟨x2, a2, hrun2, hS2, hg2, hlt2, hdec2⟩ :=
            getAppFn_spec dn vis fe CWF w hwlt m0 m2 a1 r2 hg hS1
          rw [CWF_eq, hwd] at hrun2
          have htagiff := tag_const_iff (r2.headD 0) hlt2
          rw [hdec2] at htagiff
          by_cases hk : r2.headD 0 >>> 28 ≠ 3
          · rw [entryK2_notconst _ _ _ _ hk] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl⟩
            simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind]
            rw [hrun1]
            simp only [except_ok_bind, StateT.run_bind]
            rw [hrun2]
            simp only [except_ok_bind]
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
                simp only [ConRon.Arena.nestCtorEntry, StateT.run_bind]
                rw [hrun1]
                simp only [except_ok_bind, StateT.run_bind]
                rw [hrun2]
                simp only [except_ok_bind]
                simp only [ht, beq_self_eq_true, if_true, StateT.run_bind, viewConst_run, hview]
                simp only [except_ok_bind]
                rw [hbeq]
                by_cases hcn : vt.headD 0 = C
                · simp only [hcn, decide_true, if_true]; rfl
                · simp only [hcn, decide_false]; rfl
              by_cases hcn : vt.headD 0 = C
              · rw [entryK3_hit _ _ _ _ (by simp) (by simpa using hcn)] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨_, a2, htwin, hS2, hg1.trans hg2, ?_⟩
                simp only [hcn, if_true, EntryOut]
                refine ⟨rfl, ?_⟩
                exact (erecP_ext_grow (hg1.trans hg2)).decCV hcvm0
              · rw [entryK3_miss _ _ _ _ (by simp) (by simpa using hcn)] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨_, a2, htwin, hS2, hg1.trans hg2, ?_⟩
                simp only [hcn, if_false, EntryOut]
    · have hne : ∀ cv nPc nF, ci ≠ .ctorInfo cv nPc nF := fun cv n f hh => hc ⟨cv, n, f, hh⟩
      obtain ⟨rfl, rfl⟩ := hnon hne
      rw [entryK1_fail _ _ _ (by rfl)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
      cases ci with
      | ctorInfo cv n f => exact absurd ⟨cv, n, f, rfl⟩ hc
      | _ => rfl

section census
variable (p : Prog) (hs : p.lookup "nest_ctor_entry_strip" = some nestCtorEntryStrip)
    (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "nest_ctor_entry" = some nestCtorEntry)
include hs hv hp

/-- **`nest_ctor_entry` refines `nestCtorEntry`** (through the `strip_pis`/`get_app_fn` stubs; the
parameter and field counts sum without overflow). -/
@[refines ConRon.Arena.nestCtorEntry]
theorem nestCtorEntry_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis C ciq : Word) (ci : IConstantInfo) (hC : H C)
    (hS : StageR dn vis fe s₀.mem a₀) (hci : decCI (erecP s₀.mem) dn ciq.toNat = some ci)
    (hsum : ∀ cv nPc nF, ci = .ctorInfo cv nPc nF → nPc + nF < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctor_entry" [C, ciq]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestCtorEntry (decI C) ci) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestCtorEntry (decI C) ci) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      EntryOut s'.mem r ciq (AM.res (ConRon.Arena.nestCtorEntry (decI C) ci) a₀); ⊤⦄ := by
  refine triple_post (nestCtorEntry_spec p hs hv hp n s₀ C ciq) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := entryW_ok hC hm hS hci hsum
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-! ## `nest_res_head` -/

def resHeadK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => some ([if r.headD 0 >>> 28 = 1 then 1 else 0], m1)

def resHeadW (m : Mem) (e : Word) : Option (List Word × Mem) :=
  resHeadK (stubM "get_app_fn" m [CWF, e])

theorem resHeadK_some (r : List Word) (m1 : Mem) :
    resHeadK (some (r, m1)) = some ([if r.headD 0 >>> 28 = 1 then 1 else 0], m1) := rfl
grind_pattern [ind_grind] resHeadK_some => resHeadK (some (r, m1))

theorem nestResHead_spec (p : Prog) (hg : p.lookup "nest_res_head" = some nestResHeadL) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_res_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ resHeadW s₀.mem e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hg]
  simp only [callFn, nestResHeadL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "get_app_fn" n] <;> finish [resHeadW]

theorem resHeadW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem) (a : AState)
    (e : Word) (r : List Word) (he : H e) (h : resHeadW m e = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ a', (ConRon.Arena.nestResHead (decI e)).run a = .ok (r.headD 0 != 0, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  unfold resHeadW at h
  cases hs : stubM "get_app_fn" m [CWF, e] with
  | none => rw [hs] at h; simp [resHeadK] at h
  | some rm =>
    obtain ⟨r1, m1⟩ := rm
    rw [hs] at h
    simp only [resHeadK, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, a1, hrun, hS1, hg, hlt, hdec⟩ := getAppFn_spec dn vis fe CWF e he m m1 a r1 hs hS
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
theorem nestResHead_refines (p : Prog) (hg : p.lookup "nest_res_head" = some nestResHeadL) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis e : Word)
    (he : H e) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_res_head" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestResHead (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestResHead (decI e)) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      (r.headD 0 != 0) = AM.res (ConRon.Arena.nestResHead (decI e)) a₀; ⊤⦄ := by
  refine triple_post (nestResHead_spec p hg n s₀ e) ?_
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
    (stubM "instantiate1_fast" m [CWF, v.tail.tail.headD 0, rdW (m.arr64 IW) ao, 0])
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
    (stubM "instantiate1_fast" m [CWF, v.tail.tail.headD 0, rdW (m.arr64 IW) ao, 0]) := by simp [instK1, h]
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
    (hp : p.lookup "inst_pis_with" = some instPisWith) (n : Nat) :
    ∀ (s₀ : St) (ao al e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_pis_with" [ao, al, e]
    ⦃fun r s' => LocEq s' s₀ ∧ instW n s₀.mem ao al e = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ao al e
    rw [invoke_eq _ hp]; simp only [callFn, instPisWith]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ao al e
    rw [invoke_eq _ hp]
    simp only [callFn, instPisWith]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        eView_spec p hv n, stubM_spec p "instantiate1_fast" n, ih] <;> finish (gen := 20)


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
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
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
          cases hst : stubM "instantiate1_fast" m [CWF, vt.tail.headD 0, wa, 0] with
          | none => rw [hst] at h; simp [instK2] at h
          | some rm =>
            obtain ⟨rb, m1⟩ := rm
            rw [hst, instK2_some] at h
            obtain ⟨x1, a1, hrun1, hS1, hg1, hlt1, hdec1⟩ :=
              instantiate1Fast_spec dn vis fe CWF (vt.tail.headD 0) wa 0 hy2' hwa_lt m m1 a rb hst hS
            cases hw : instW n m1 (ao + 1) (al - 1) (rb.headD 0) with
            | none => rw [hw] at h; simp [instK3] at h
            | some rm3 =>
              obtain ⟨r3, m3⟩ := rm3
              rw [hw, instK3_some] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
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
    (hp : p.lookup "inst_pis_with" = some instPisWith)
include hv hp

/-- **`inst_pis_with` refines `instPisWith`** (through the `instantiate1_fast` stub). -/
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
  refine triple_post (instPisWith_spec p hv hp n s₀ ao al e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := instW_ok n dn fe vis _ _ a₀ ao al e args r hm hS he hdec hb hit
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-! ## `close_telescope` -/

mutual
def closeW : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, dO, dl, i, body =>
    if dl = 0 then some ([body], m)
    else closeK1 dO i (closeW n m (dO + 1) (dl - 1) (i + 1) body)
def closeK1 (dO i : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => closeK2 dO (stubM "abstract1_fast" m1 [CWF, r1.headD 0, i, 0])
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
    closeK2 dO (stubM "abstract1_fast" m1 [CWF, r1.headD 0, i, 0]) := by rw [closeK1]
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
  (hp : p.lookup "close_telescope" = some closeTelescope)
include hd hpf hpp hpi hmk hp

theorem closeTelescope_spec (n : Nat) : ∀ (s₀ : St) (dO dl i body : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_telescope" [dO, dl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ closeW n s₀.mem dO dl i body = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ dO dl i body
    rw [invoke_eq _ hp]; simp only [callFn, closeTelescope]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ dO dl i body
    rw [invoke_eq _ hp]
    simp only [callFn, closeTelescope]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "abstract1_fast" n, mkForall_spec p hd hpf hpp hpi hmk n, ih] <;>
      finish (gen := 20)

end spec


theorem rdW_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hi : x.toNat < iwTop m) :
    rdW (m'.arr64 IW) x = rdW (m.arr64 IW) x := by
  simp only [rdW, hg.2.2.1 _ hi]

theorem closeW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (dO dl i body : Word) (ds : List EIdx) (r : List Word),
    closeW n m dO dl i body = some (r, m') → StageR dn vis fe m a → H body →
    decHL m dO.toNat dl.toNat = some ds → dO.toNat + dl.toNat < 2 ^ 64 →
    dO.toNat + dl.toNat ≤ iwTop m → i.toNat + dl.toNat < 2 ^ 64 →
    ∃ x a', (ConRon.Arena.closeTelescope ds i.toNat (decI body)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decW0E m' r x := by
  induction n with
  | zero => intro dn fe vis m m' a dO dl i body ds r h; simp [closeW] at h
  | succ n ih =>
    intro dn fe vis m m' a dO dl i body ds r h hS hbody hdec hb hit hib
    by_cases hdl : dl = 0
    · rw [closeW_nil n m dO dl i body hdl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : ds = [] := by
        have h0 : dl.toNat = 0 := by rw [hdl]; rfl
        rw [h0] at hdec; simpa [decHL, hslice?] using hdec.symm
      subst this
      exact ⟨decI body, a, rfl, hS, IWGrow.refl _, hbody, rfl⟩
    · have hl1 : dl.toNat = (dl.toNat - 1) + 1 := by have := toNat_ne_zero' hdl; omega
      rw [hl1, decHL, hslice?_succ] at hdec
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdec
      obtain ⟨d, hdd, bs, hbs, rfl⟩ := hdec
      rw [closeW_cons n m dO dl i body hdl] at h
      have hdo1 : (dO + 1).toNat = dO.toNat + 1 := toNat_add_one' (by omega)
      have hdl1 : (dl - 1).toNat = dl.toNat - 1 := toNat_sub_one' hdl
      have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_one' (by omega)
      cases hr1 : closeW n m (dO + 1) (dl - 1) (i + 1) body with
      | none => rw [hr1] at h; simp [closeK1] at h
      | some rm1 =>
        obtain ⟨r1, m1⟩ := rm1
        rw [hr1, closeK1_some] at h
        obtain ⟨x1, a1, hrun1, hS1, hg1, hlt1, hdec1⟩ :=
          ih dn fe vis m m1 a (dO + 1) (dl - 1) (i + 1) body bs r1 hr1 hS hbody
            (by rw [hdo1, hdl1]; exact hbs) (by rw [hdo1, hdl1]; omega) (by rw [hdo1, hdl1]; omega)
            (by rw [hi1, hdl1]; omega)
        rw [hi1] at hrun1
        cases hr2 : stubM "abstract1_fast" m1 [CWF, r1.headD 0, i, 0] with
        | none => rw [hr2] at h; simp [closeK2] at h
        | some rm2 =>
          obtain ⟨r2, m2⟩ := rm2
          rw [hr2, closeK2_some] at h
          obtain ⟨x2, a2, hrun2, hS2, hg2, hlt2, hdec2⟩ :=
            abstract1Fast_spec dn vis fe CWF (r1.headD 0) i 0 hlt1 m1 m2 a1 r2 hr2 hS1
          rw [CWF_eq, hdec1, show (0 : Word).toNat = 0 from rfl] at hrun2
          have hg12 := hg1.trans hg2
          have hd0 : dO.toNat < iwTop m := by omega
          obtain ⟨wd, hwd_eq, hwd_lt, hwd_dec⟩ := iwH_rdW hdd (by omega)
          rw [UInt64.ofNat_toNat] at hwd_eq
          rw [rdW_grow hg12 hd0, hwd_eq] at h
          cases hm : mkForallW m2 wd (r2.headD 0) with
          | none => rw [hm] at h; simp [closeK3] at h
          | some rm3 =>
            obtain ⟨rr, m3⟩ := rm3
            rw [hm] at h
            by_cases hbig : 4294967296 ≤ rr
            · rw [closeK3_big _ _ hbig] at h; simp at h
            · rw [closeK3_ok _ _ hbig] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨a3, hrun3, hS3, hg3⟩ := mkForall_stage hS2 wd (r2.headD 0) hm
              refine ⟨decE rr, a3, ?_, hS3, hg12.trans hg3, ?_, rfl⟩
              · simp only [ConRon.Arena.closeTelescope, StateT.run_bind]
                rw [hrun1]
                simp only [except_ok_bind, StateT.run_bind]
                rw [hrun2]
                simp only [except_ok_bind]
                rw [← hwd_dec, ← hdec2]
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
  (hp : p.lookup "close_telescope" = some closeTelescope)
include hd hpf hpp hpi hmk hp

/-- **`close_telescope` refines `closeTelescope`** (through the `abstract1_fast` stub and master's
`mk_forall`). -/
@[refines ConRon.Arena.closeTelescope]
theorem closeTelescope_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis dO dl i body : Word) (ds : List EIdx) (hbody : H body)
    (hS : StageR dn vis fe s₀.mem a₀) (hdec : decHL s₀.mem dO.toNat dl.toNat = some ds)
    (hb : dO.toNat + dl.toNat < 2 ^ 64) (hit : dO.toNat + dl.toNat ≤ iwTop s₀.mem)
    (hib : i.toNat + dl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "close_telescope" [dO, dl, i, body]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decW0E s'.mem r (AM.res (ConRon.Arena.closeTelescope ds i.toNat (decI body)) a₀); ⊤⦄ := by
  refine triple_post (closeTelescope_spec p hd hpf hpp hpi hmk hp n s₀ dO dl i body) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := closeW_ok n dn fe vis _ _ a₀ dO dl i body ds r hm hS hbody hdec hb hit hib
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-! ## `pin_word` as a word model -/

def pinWordV (m : Mem) (k : Word) : Option Word :=
  if rdW (m.arr64 PINS) 0 = 0 then none else some (rdW (m.arr64 PINS) k)

theorem pinWord_specV (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ pinWordV s₀.mem k = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;> finish [pinWordV]


/-! ## `nest_canon_sub` -/

def canonK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => if 4294967296 ≤ r then none else some ([1, r], m2)
def canonK2 (nn mi : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (s, m1) => if 4294967296 ≤ s then none else canonK3 (fvinternW m1 (nn + mi) s)
def canonK1 (nn mi : Word) (m : Mem) : Option Word → Option (List Word × Mem)
  | none => none
  | some z => if 4294967296 ≤ z then none else canonK2 nn mi (sointernW m z)
def canonK0 (nn : Word) (m : Mem) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some fr => if fr.headD 0 = 0 then some ([0, 0], m)
      else canonK1 nn (fr.tail.headD 0) m (pinWordV m 53)
def canonW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, us, nn, c, v =>
    if v ≠ us then some ([0, 0], m) else canonK0 nn m (findW n m no nl c)

section arms
variable (n : Nat) (m m1 m2 : Mem) (no nl us nn c v mi r s z : Word) (fr : List Word)
theorem canonW_ne (h : v ≠ us) : canonW (n + 1) m no nl us nn c v = some ([0, 0], m) := by simp [canonW, h]
theorem canonW_eq (h : ¬ v ≠ us) : canonW (n + 1) m no nl us nn c v = canonK0 nn m (findW n m no nl c) := by
  simp only [canonW]; rw [if_neg h]
theorem canonK0_miss (h : fr.headD 0 = 0) : canonK0 nn m (some fr) = some ([0, 0], m) := by
  simp only [canonK0]; rw [if_pos h]
theorem canonK0_hit (h : ¬ fr.headD 0 = 0) :
    canonK0 nn m (some fr) = canonK1 nn (fr.tail.headD 0) m (pinWordV m 53) := by
  simp only [canonK0]; rw [if_neg h]
theorem canonK1_big (h : 4294967296 ≤ z) : canonK1 nn mi m (some z) = none := by simp [canonK1, h]
theorem canonK1_ok (h : ¬ 4294967296 ≤ z) : canonK1 nn mi m (some z) = canonK2 nn mi (sointernW m z) := by
  simp only [canonK1]; rw [if_neg h]
theorem canonK2_big (h : 4294967296 ≤ s) : canonK2 nn mi (some (s, m1)) = none := by simp [canonK2, h]
theorem canonK2_ok (h : ¬ 4294967296 ≤ s) :
    canonK2 nn mi (some (s, m1)) = canonK3 (fvinternW m1 (nn + mi) s) := by
  simp only [canonK2]; rw [if_neg h]
theorem canonK3_big (h : 4294967296 ≤ r) : canonK3 (some (r, m2)) = none := by simp [canonK3, h]
theorem canonK3_ok (h : ¬ 4294967296 ≤ r) : canonK3 (some (r, m2)) = some ([1, r], m2) := by
  simp only [canonK3]; rw [if_neg h]
end arms
grind_pattern [ind_grind] canonW_ne => canonW (n + 1) m no nl us nn c v
grind_pattern [ind_grind] canonW_eq => canonW (n + 1) m no nl us nn c v
grind_pattern [ind_grind] canonK0_miss => canonK0 nn m (some fr)
grind_pattern [ind_grind] canonK0_hit => canonK0 nn m (some fr)
grind_pattern [ind_grind] canonK1_big => canonK1 nn mi m (some z)
grind_pattern [ind_grind] canonK1_ok => canonK1 nn mi m (some z)
grind_pattern [ind_grind] canonK2_big => canonK2 nn mi (some (s, m1))
grind_pattern [ind_grind] canonK2_ok => canonK2 nn mi (some (s, m1))
grind_pattern [ind_grind] canonK3_big => canonK3 (some (r, m2))
grind_pattern [ind_grind] canonK3_ok => canonK3 (some (r, m2))

section spec
variable (p : Prog) (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hp : p.lookup "nest_canon_sub" = some nestCanonSub)
include hf hpw hsf hsp his hff hfp hif hp

theorem nestCanonSub_spec (n : Nat) (s₀ : St) (no nl us nn c v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_canon_sub" [no, nl, us, nn, c, v]
    ⦃fun r s' => LocEq s' s₀ ∧ canonW n s₀.mem no nl us nn c v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestCanonSub]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slFind_spec p hf n, pinWord_specV p hpw n, internSort_spec p hsf hsp his n,
        internFVar_spec p hff hfp hif n] <;> finish (gen := 20) [canonW]

end spec


theorem findIdx_decI (ws : List Word) (c : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : NIdx))).findIdx? (· == (decI c : NIdx)) = ws.findIdx? (· == c) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.findIdx?_cons]
    rw [decI_beq' w c (hws w (by simp)) hc]
    by_cases h : w = c
    · simp [h]
    · simp [h]
      have := ih (fun x hx => hws x (by simp [hx]))
      simp only [List.findIdx?_map] at this
      rw [this]

theorem notbig_of_lt {z : Word} (h : z.toNat < 2 ^ 32) : ¬ 4294967296 ≤ z := by
  intro hh
  have := UInt64.le_iff_toNat_le.mp hh
  have e : (4294967296 : Word).toNat = 4294967296 := by decide
  omega

theorem lt_of_notbig {z : Word} (h : ¬ 4294967296 ≤ z) : z.toNat < 2 ^ 32 := by
  have : ¬ (4294967296 : Word).toNat ≤ z.toNat := fun hh => h (UInt64.le_iff_toNat_le.mpr hh)
  have e : (4294967296 : Word).toNat = 4294967296 := by decide
  omega

theorem canonW_ok (n : Nat) : ∀ (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us nn c v : Word) (names : List NIdx) (r : List Word),
    canonW n m no nl us nn c v = some (r, m') → StageR dn vis fe m a → H c → H us → H v →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat < 2 ^ 64 →
    nn.toNat + names.length < 2 ^ 64 →
    ∃ x a', (ConRon.Arena.nestCanonSub names (decI us) nn.toNat (decI c) (decI v)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOE m' r x := by
  intro dn fe vis m m' a no nl us nn c v names r h hS hc hus hv hdec hb hnn
  cases n with
  | zero => simp [canonW] at h
  | succ n =>
  by_cases hvu : v ≠ us
  · rw [canonW_ne n m no nl us nn c v hvu] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    have : ¬ ((decI v : LsIdx) == decI us) = true := by
      rw [decI_beq' v us hv hus]; simpa using hvu
    simp only [ConRon.Arena.nestCanonSub, this, if_false]; rfl
  · rw [canonW_eq n m no nl us nn c v hvu] at h
    have hvu' : v = us := by simpa using hvu
    subst hvu'
    have hbeq : ((decI v : LsIdx) == decI v) = true := by simp
    obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m _ _ names hdec hb
    simp only [UInt64.ofNat_toNat] at hws
    have hlen : ws.length < 2 ^ 64 := by
      have := decHL_length m hdec; simp at this; omega
    cases hfw : findW n m no nl c with
    | none => rw [hfw] at h; simp [canonK0] at h
    | some fr =>
      rw [hfw] at h
      have hfr := findW_ok n _ _ _ _ _ _ hws hfw hlen
      have hfi := findIdx_decI ws c hwlt hc
      cases hwi : ws.findIdx? (· == c) with
      | none =>
        rw [hwi] at hfr
        subst hfr
        rw [canonK0_miss _ _ _ rfl] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
        simp only [ConRon.Arena.nestCanonSub, hbeq, ite_true, hfi, hwi]; rfl
      | some i =>
        rw [hwi] at hfr
        subst hfr
        rw [canonK0_hit _ _ _ (by simp)] at h
        simp only [List.tail_cons, List.headD_cons] at h
        cases hpw : pinWordV m 53 with
        | none => rw [hpw] at h; simp [canonK1] at h
        | some z =>
          rw [hpw] at h
          have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
            intro h0; simp [pinWordV, h0] at hpw
          have hz : z = pinW m 53 := by
            simp only [pinWordV, hpne, if_false, Option.some.injEq] at hpw
            rw [← hpw]; simp [pinW, rdW]
          have hpin0 : pinW m 0 ≠ 0 := by simpa [pinW, rdW] using hpne
          have hfull := hS.1.pins.full hpin0
          have hzlt : z.toNat < 2 ^ 32 := by rw [hz]; exact hfull.lv_lt.2.1
          rw [canonK1_ok _ _ _ _ (notbig_of_lt hzlt)] at h
          cases hso : sointernW m z with
          | none => rw [hso] at h; simp [canonK2] at h
          | some rm1 =>
            obtain ⟨s1, m1⟩ := rm1
            rw [hso] at h
            by_cases hsb : 4294967296 ≤ s1
            · rw [canonK2_big _ _ _ _ hsb] at h; simp at h
            rw [canonK2_ok _ _ _ _ hsb] at h
            obtain ⟨a1, hrun1, hS1, hg1⟩ := internSort_stage hS z hzlt hso
            have hs1lt : s1.toNat < 2 ^ 32 := lt_of_notbig hsb
            cases hfv : fvinternW m1 (nn + UInt64.ofNat i) s1 with
            | none => rw [hfv] at h; simp [canonK3] at h
            | some rm2 =>
              obtain ⟨rr, m2⟩ := rm2
              rw [hfv] at h
              by_cases hrb : 4294967296 ≤ rr
              · rw [canonK3_big _ _ hrb] at h; simp at h
              rw [canonK3_ok _ _ hrb] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 (nn + UInt64.ofNat i) s1 hs1lt hfv
              have hilt : i < ws.length := by
                have := List.findIdx?_eq_some_iff_findIdx_eq.mp hwi
                exact this.1
              have hnn' : nn.toNat + ws.length < 2 ^ 64 := by simpa using hnn
              have hsz : UInt64.size = 2 ^ 64 := rfl
              have hnn2 : (nn + UInt64.ofNat i).toNat = nn.toNat + i := by
                rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]
                exact Nat.mod_eq_of_lt (by omega)
              refine ⟨some (decE rr), a2, ?_, hS2, (hg1.trans hg2), ?_⟩
              · have hzl : (zeroLevel).run a = .ok (decI z, a) := by
                  rw [hz]; exact pinZeroLevel_run hfull
                simp only [ConRon.Arena.nestCanonSub, hbeq, ite_true, hfi, hwi]
                simp only [StateT.run_bind]
                rw [hzl]
                simp only [except_ok_bind, StateT.run_bind]
                simp only [ConRon.Arena.internSortE, ConRon.Arena.internFVarE]
                rw [hrun1]
                simp only [except_ok_bind, StateT.run_bind]
                rw [hnn2] at hrun2
                rw [hrun2]
                rfl
              · exact ⟨rfl, lt_of_notbig hrb, rfl⟩


section census
variable (p : Prog) (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hp : p.lookup "nest_canon_sub" = some nestCanonSub)
include hf hpw hsf hsp his hff hfp hif hp

/-- **`nest_canon_sub` refines `nestCanonSub`**. -/
@[refines ConRon.Arena.nestCanonSub]
theorem nestCanonSub_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us nn c v : Word) (names : List NIdx) (hc : H c) (hus : H us) (hv : H v)
    (hS : StageR dn vis fe s₀.mem a₀) (hdec : decHL s₀.mem no.toNat nl.toNat = some names)
    (hb : no.toNat + nl.toNat < 2 ^ 64) (hnn : nn.toNat + names.length < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_canon_sub" [no, nl, us, nn, c, v]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.nestCanonSub names (decI us) nn.toNat (decI c) (decI v)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestCanonSub names (decI us) nn.toNat (decI c) (decI v)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.nestCanonSub names (decI us) nn.toNat (decI c) (decI v)) a₀); ⊤⦄ := by
  refine triple_post (nestCanonSub_spec p hf hpw hsf hsp his hff hfp hif hp n s₀ no nl us nn c v) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := canonW_ok n dn fe vis _ _ a₀ no nl us nn c v names r hm hS hc hus hv hdec hb hnn
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

/-! ## `nest_frame_mates_go` -/

mutual
def matesW : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, c, off, l, oO, oL =>
    if l = 0 then some ([oO, oL], m)
    else matesK1 n m c off l oO oL (containsW n m oO oL (rdW (m.arr64 EREC) off))
def matesK1 (n : Nat) (m : Mem) (c off l oO oL : Word) : Option Word → Option (List Word × Mem)
  | none => none
  | some b =>
    if rdW (m.arr64 EREC) off = c ∨ b ≠ 0 then matesK3 (matesW n m c (off + 1) (l - 1) oO oL)
    else matesK2 n c off l (snocW n m oO oL (rdW (m.arr64 EREC) off))
def matesK2 (n : Nat) (c off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => matesK3 (matesW n m2 c (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0))
def matesK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([r.headD 0, r.tail.headD 0], m3)
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (c off l oO oL b : Word) (r r2 : List Word)
theorem matesW_nil (h : l = 0) : matesW (n + 1) m c off l oO oL = some ([oO, oL], m) := by simp [matesW, h]
theorem matesW_cons (h : l ≠ 0) : matesW (n + 1) m c off l oO oL =
    matesK1 n m c off l oO oL (containsW n m oO oL (rdW (m.arr64 EREC) off)) := by simp [matesW, h]
theorem matesK1_skip (h : rdW (m.arr64 EREC) off = c ∨ b ≠ 0) : matesK1 n m c off l oO oL (some b) =
    matesK3 (matesW n m c (off + 1) (l - 1) oO oL) := by simp only [matesK1]; rw [if_pos h]
theorem matesK1_add (h : ¬ (rdW (m.arr64 EREC) off = c ∨ b ≠ 0)) : matesK1 n m c off l oO oL (some b) =
    matesK2 n c off l (snocW n m oO oL (rdW (m.arr64 EREC) off)) := by simp only [matesK1]; rw [if_neg h]
theorem matesK2_some : matesK2 n c off l (some (r2, m2)) =
    matesK3 (matesW n m2 c (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0)) := by rw [matesK2]
theorem matesK3_some : matesK3 (some (r, m2)) = some ([r.headD 0, r.tail.headD 0], m2) := by rw [matesK3]
end arms
grind_pattern [ind_grind] matesW_nil => matesW (n + 1) m c off l oO oL
grind_pattern [ind_grind] matesW_cons => matesW (n + 1) m c off l oO oL
grind_pattern [ind_grind] matesK1_skip => matesK1 n m c off l oO oL (some b)
grind_pattern [ind_grind] matesK1_add => matesK1 n m c off l oO oL (some b)
grind_pattern [ind_grind] matesK2_some => matesK2 n c off l (some (r2, m2))
grind_pattern [ind_grind] matesK3_some => matesK3 (some (r, m2))

section spec
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hp : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL)
include hc ha hcp hsn hp

theorem nestFrameMatesGo_spec (n : Nat) : ∀ (s₀ : St) (c off l oO oL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_mates_go" [c, off, l, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ matesW n s₀.mem c off l oO oL = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ c off l oO oL
    rw [invoke_eq _ hp]; simp only [callFn, nestFrameMatesGoL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ c off l oO oL
    rw [invoke_eq _ hp]
    simp only [callFn, nestFrameMatesGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        slContains_spec p hc n, slSnoc_specW p ha hcp hsn n, ih] <;> finish (gen := 20)

end spec


theorem snocW_decK {k : IdxKind} {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} {xs : List (Idx k)}
    (h : snocW n m o l x = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hx : x.toNat < 2 ^ 32) (hxs : decHL m o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l + 1] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (xs ++ [decI x]) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ (l + 1).toNat = l.toNat + 1 ∧
    (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat = iwTop m' := by
  simp only [snocW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  cases hal : allocW m (l + 1) with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts hal hsz
  simp only [hal] at h
  cases hcp : copyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  subst hq hm1
  generalize hqq : rdW (m.arr64 CTL) 200 = q at *
  have hlm : l.toNat ≠ 2 ^ 64 - 1 := fun e => h0 (by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp [e])
  have hl1 : (l + 1).toNat = l.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := l.toNat_lt; omega
  rw [hl1] at hroom
  have hql : (q + l).toNat = q.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hIW := allocMem_IW m (l + 1)
  obtain ⟨hA, hS, hW, hG⟩ := copyW_get (n - 1) _ _ _ _ _ hcp (by simp only [iwTop, hqq] at hsrc; omega)
    (by rw [hIW]; omega) (by rw [hIW]; exact hsz)
  rw [hIW] at hS hG
  have hfr : MemFrame [IW] [200] m m2 :=
    (allocMem_frame m (l + 1)).trans (copy_frame hA (by rw [hS, hIW]) (by first | (rw [hW]) | (rw [hW]; simp [allocMem])))
  have hfr' := hfr.trans (set64IW_frame m2 (q + l) x)
  have hget : ∀ i, ((m2.set64 IW (q + l) x).arr64 IW)[i]? =
      if i = q.toNat + l.toNat then some x
      else if q.toNat ≤ i ∧ i < q.toNat + l.toNat then (m.arr64 IW)[o.toNat + (i - q.toNat)]?
      else (m.arr64 IW)[i]? := by
    intro i
    rw [set64IW_get, hql, hS, hG i]
    by_cases h1 : i = q.toNat + l.toNat
    · rw [if_pos ⟨h1, by omega⟩, if_pos h1]
    · rw [if_neg (by omega), if_neg h1]
  have hCTL : (m2.set64 IW (q + l) x).arr64 CTL = (allocMem m (l + 1)).arr64 CTL := by
    rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), hA CTL (by decide)]
  have htop : rdW ((m2.set64 IW (q + l) x).arr64 CTL) 200 = q + (l + 1) := by
    rw [hCTL, allocMem_top m _ hc, hqq]
  have hq' : q + (l + 1) = q + (l + 1) := rfl
  have hsum : (q + (l + 1)).toNat = q.toNat + (l.toNat + 1) := by
    rw [UInt64.toNat_add, hl1]; simp; omega
  refine ⟨rfl, ?_, ?_, hfr', hl1, ?_⟩
  · simp only [decHL]
    rw [hl1, hslice?_add]
    have h1 : (hslice? (iwA (m2.set64 IW (q + l) x)) q.toNat l.toNat : Option (List (Idx k))) =
        some xs := by
      rw [← hxs]; simp only [decHL]
      apply hslice?_congr
      intro j hj
      simp only [iwA, hget]
      rw [if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    have h2 : (hslice? (iwA (m2.set64 IW (q + l) x)) (q.toNat + l.toNat) 1 :
        Option (List (Idx k))) = some [decI x] := by
      rw [hslice?_succ]
      have : (hd? (iwA (m2.set64 IW (q + l) x)) (q.toNat + l.toNat) : Option (Idx k)) =
          some (decI x) := by simp [hd?, iwA, hget, hx]
      rw [this]; simp [hslice?]
    rw [h1, h2]; simp
  · refine iwGrow_of_frame hfr' (N := l + 1) ?_ ?_ hsz ?_
    · rw [htop, hqq]
    · simp only [iwTop, hqq]; omega
    · intro i hi
      simp only [iwTop, hqq] at hi
      rw [hget, if_neg (by omega), if_neg (by omega)]
  · simp only [iwTop, htop, hsum]; omega



theorem contains_decI (ws : List Word) (x : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : NIdx))).contains (decI x) = ws.contains x := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.contains_cons]
    rw [decI_beq' x w hx (hws w (by simp))]
    have := ih (fun y hy => hws y (by simp [hy]))
    rw [this]
    by_cases h : x = w <;> simp [h]

theorem matesW_ok (n : Nat) : ∀ (m m' : Mem) (c off l oO oL : Word) (block out : List NIdx) (r : List Word),
    matesW n m c off l oO oL = some (r, m') → (m.arr64 IW).size < 2 ^ 64 → 200 < (m.arr64 CTL).size →
    (m.arr64 EREC).size < 2 ^ 64 →
    H c → hslice? (erA m) off.toNat l.toNat = some block → decHL m oO.toNat oL.toNat = some out →
    oO.toNat + oL.toNat ≤ iwTop m → oO.toNat + oL.toNat < 2 ^ 64 →
    decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (ConRon.Arena.nestFrameMates.go (decI c) block out) ∧
    IWGrow m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
    (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  induction n with
  | zero => intro m m' c off l oO oL block out r h; simp [matesW] at h
  | succ n ih =>
    intro m m' c off l oO oL block out r h hsz hc200 hEs hc hblock hout hit hb
    by_cases hl : l = 0
    · rw [matesW_nil n m c off l oO oL hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : block = [] := by
        have h0 : l.toNat = 0 := by rw [hl]; rfl
        rw [h0] at hblock; simpa [hslice?] using hblock.symm
      subst this
      exact ⟨by simpa [ConRon.Arena.nestFrameMates.go] using hout, IWGrow.refl _, rfl, hit⟩
    · have hl1 : l.toNat = (l.toNat - 1) + 1 := by have := toNat_ne_zero' hl; omega
      rw [hl1, hslice?_succ] at hblock
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hblock
      obtain ⟨x, hx, rest, hrest, rfl⟩ := hblock
      obtain ⟨w0, hw0, hw0lt, hw0d⟩ := hd?_some hx
      have hrd : rdW (m.arr64 EREC) off = w0 := by
        have : (m.arr64 EREC)[off.toNat]? = some w0 := hw0
        simp only [rdW, this, Option.getD_some]
      obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m _ _ out hout hb
      simp only [UInt64.ofNat_toNat] at hws
      rw [matesW_cons n m c off l oO oL hl, hrd] at h
      cases hcn : containsW n m oO oL w0 with
      | none => rw [hcn] at h; simp [matesK1] at h
      | some b =>
        rw [hcn] at h
        have hbv := containsW_ok n _ _ _ _ _ _ hws hcn
        have hlt : off.toNat < (m.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp hw0).1
        have hoff1 : (off + 1).toNat = off.toNat + 1 := toNat_add_one' (by omega)
        have hl1' : (l - 1).toNat = l.toNat - 1 := toNat_sub_one' hl
        have hcond : ((decI w0 : NIdx) == decI c || (ws.map (fun w => (decI w : NIdx))).contains (decI w0)) =
            decide (w0 = c ∨ b ≠ 0) := by
          rw [decI_beq' w0 c hw0lt hc, contains_decI ws w0 hwlt hw0lt, hbv]
          by_cases h1 : w0 = c <;> by_cases h2 : ws.contains w0 = true <;> simp [h1, h2]
        have hblock' : hslice? (erA m) (off + 1).toNat (l - 1).toNat = some rest := by
          rw [hoff1, hl1']; exact hrest
        subst hw0d
        by_cases hskip : (w0 = c ∨ b ≠ 0)
        · have hskip' : rdW (m.arr64 EREC) off = c ∨ b ≠ 0 := by rw [hrd]; exact hskip
          rw [matesK1_skip n m c off l oO oL b hskip'] at h
          cases hrec : matesW n m c (off + 1) (l - 1) oO oL with
          | none => rw [hrec] at h; simp [matesK3] at h
          | some rm3 =>
            obtain ⟨r3, m3⟩ := rm3
            rw [hrec, matesK3_some] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hd, hg, hE', htop⟩ := ih m m3 c (off + 1) (l - 1) oO oL rest _ r3 hrec hsz hc200 hEs hc
              hblock' hout hit hb
            refine ⟨?_, hg, hE', by simpa using htop⟩
            rw [ConRon.Arena.nestFrameMates.go.eq_2, if_pos (by rw [hcond]; simpa using hskip)]
            simpa using hd
        · have hskip' : ¬ (rdW (m.arr64 EREC) off = c ∨ b ≠ 0) := by rw [hrd]; exact hskip
          rw [matesK1_add n m c off l oO oL b hskip', hrd] at h
          cases hsn : snocW n m oO oL w0 with
          | none => rw [hsn] at h; simp [matesK2] at h
          | some rm2 =>
            obtain ⟨r2, m2⟩ := rm2
            rw [hsn, matesK2_some] at h
            obtain ⟨hr2, hdec2, hg2, hfr2, hl2, htop2⟩ := snocW_decK hsn hsz hc200 hit hw0lt hout
            subst hr2
            simp only [List.headD_cons, List.tail_cons] at h
            cases hrec : matesW n m2 c (off + 1) (l - 1) (rdW (m.arr64 CTL) 200) (oL + 1) with
            | none => rw [hrec] at h; simp [matesK3] at h
            | some rm3 =>
              obtain ⟨r3, m3⟩ := rm3
              rw [hrec, matesK3_some] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hE2 : m2.arr64 EREC = m.arr64 EREC := hfr2.1 EREC (by decide) (by decide)
              have hsz2 : (m2.arr64 IW).size < 2 ^ 64 := by rw [hfr2.2.2.1 IW]; exact hsz
              have hc2 : 200 < (m2.arr64 CTL).size := by rw [hfr2.2.2.1 CTL]; exact hc200
              obtain ⟨hd, hg, hE', htop⟩ := ih m2 m3 c (off + 1) (l - 1) _ (oL + 1) rest _ r3 hrec hsz2 hc2
                (by rw [hE2]; exact hEs) hc (by simp only [erA]; rw [hE2]; exact hblock') (by simpa using hdec2)
                (Nat.le_of_eq htop2) (by have : iwTop m2 < 2 ^ 64 := (rdW (m2.arr64 CTL) 200).toNat_lt; omega)
              refine ⟨?_, hg2.trans hg, hE'.trans hE2, by simpa using htop⟩
              rw [ConRon.Arena.nestFrameMates.go.eq_2, if_neg (by rw [hcond]; simpa using hskip)]
              simpa using hd


section census
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hp : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL)
include hc ha hcp hsn hp

/-- **`nest_frame_mates_go` refines `nestFrameMates.go`**: the block is an `EREC` slice, the
accumulator an `IW` slice. -/
@[refines ConRon.Arena.nestFrameMates.go]
theorem nestFrameMatesGo_refines (n : Nat) (s₀ : St) (c off l oO oL : Word) (block out : List NIdx)
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hc200 : 200 < (s₀.mem.arr64 CTL).size)
    (hEs : (s₀.mem.arr64 EREC).size < 2 ^ 64) (hcH : H c)
    (hblock : hslice? (erA s₀.mem) off.toNat l.toNat = some block)
    (hout : decHL s₀.mem oO.toNat oL.toNat = some out)
    (hit : oO.toNat + oL.toNat ≤ iwTop s₀.mem) (hb : oO.toNat + oL.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_mates_go" [c, off, l, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (ConRon.Arena.nestFrameMates.go (decI c) block out) ∧ IWGrow s₀.mem s'.mem ∧
      s'.mem.arr64 EREC = s₀.mem.arr64 EREC ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  refine triple_post (nestFrameMatesGo_spec p hc ha hcp hsn hp n s₀ c off l oO oL) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨h1, h2, h3, h4⟩ := matesW_ok n _ _ c off l oO oL block out r hm hsz hc200 hEs hcH hblock hout hit hb
  exact ⟨hl, h1, h2, h3, h4⟩

end census


theorem decHL_zero_zero {k : IdxKind} (m : Mem) : (decHL m 0 0 : Option (List (Idx k))) = some [] := by
  simp [decHL, hslice?]

section census2
variable (p : Prog) (hc : p.lookup "sl_contains" = some slContains) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hcp : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hgo : p.lookup "nest_frame_mates_go" = some nestFrameMatesGoL)
  (hx : p.lookup "env_ix" = some envIxL) (hg : p.lookup "env_row_get" = some envRowGetL)
  (hf : p.lookup "env_find" = some envFindL) (hbo : p.lookup "nest_block_of" = some nestBlockOfL)
  (hp : p.lookup "nest_frame_mates" = some nestFrameMatesL)
include hc ha hcp hsn hgo hx hg hf hbo hp

/-- **`nest_frame_mates` refines `nestFrameMates`**. -/
@[refines ConRon.Arena.nestFrameMates]
theorem nestFrameMates_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis c : Word) (hcH : H c) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_frame_mates" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat =
        some (ConRon.Arena.nestFrameMates fe (decI c)) ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  obtain ⟨hOK1, hOK2, hOK3, hOK4, hOK5⟩ := hS.2
  have hE := hS.1.env
  rw [invoke_eq _ hp]
  simp only [callFn, nestFrameMatesL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      nestBlockOf_refines p hx hg hf hbo n (dn := dn) (fe := fe),
      nestFrameMatesGo_refines p hc ha hcp hsn hgo n (block := ConRon.Arena.nestBlockOf fe (decI c)) (out := [])] <;> finish (gen := 20) [ConRon.Arena.nestFrameMates, decHL_zero_zero]

end census2

/-! ## `mentions_any_go`, `mentions_any_node`: word models -/

mutual
def maGoW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, no, nl, f, h =>
    if f = 0 then none else maG1 n m no nl f h (eViewW m h)
def maG1 (n : Nat) (m : Mem) (no nl f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (0, m)
  else if v.headD 0 = 3 then maC m (containsW n m no nl (v.tail.headD 0))
  else maG3 n m no nl f h v (mfindG maSch m h 0)
def maG3 (n : Nat) (m : Mem) (no nl f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 MAM) (fr.tail.headD 0 * 4 + 3), m)
  else maG4 h (maNodeW n m no nl (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def maG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => maG5 r (msetG maSch m1 h 0 r)
def maG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def maC (m : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some r => some (r, m)
def maNodeW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, f1, g, x, y, z =>
    if g = 1 then maGoW n m no nl f1 y
    else if g = 4 ∨ g = 5 ∨ g = 6 then maB1 n no nl f1 y (maGoW n m no nl f1 x)
    else if g = 7 then maL1 n no nl f1 y z (maGoW n m no nl f1 x)
    else maP1 n no nl x (maGoW n m no nl f1 z)
def maB1 (n : Nat) (no nl f1 y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => maB2 b1 (maGoW n m1 no nl f1 y)
def maB2 (b1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m2)
def maL1 (n : Nat) (no nl f1 y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => maL2 n no nl f1 z b1 (maGoW n m1 no nl f1 y)
def maL2 (n : Nat) (no nl f1 z b1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => maL3 b1 b2 (maGoW n m2 no nl f1 z)
def maL3 (b1 b2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b3, m3) => some (if b1 ≠ 0 ∨ b2 ≠ 0 ∨ b3 ≠ 0 then 1 else 0, m3)
def maP1 (n : Nat) (no nl x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => maP2 b1 m1 (containsW n m1 no nl x)
def maP2 (b1 : Word) (m1 : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some b2 => some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m1)
end


section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (no nl f f1 h g x y z b1 b2 b3 r : Word) (v fr : List Word)
theorem maGoW_abort (hf : f = 0) : maGoW (n + 1) m no nl f h = none := by simp [maGoW, hf]
theorem maGoW_view (hf : f ≠ 0) : maGoW (n + 1) m no nl f h = maG1 n m no nl f h (eViewW m h) := by
  simp [maGoW, hf]
theorem maG1_abort (hv : v = []) : maG1 n m no nl f h v = none := by simp [maG1, hv]
theorem maG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    maG1 n m no nl f h v = some (0, m) := by simp only [maG1]; rw [if_neg hv, if_pos hg]
theorem maG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) : maG1 n m no nl f h v = maC m (containsW n m no nl (v.tail.headD 0)) := by
  simp only [maG1]; rw [if_neg hv, if_neg hg, if_pos h3]
theorem maG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) : maG1 n m no nl f h v = maG3 n m no nl f h v (mfindG maSch m h 0) := by
  simp only [maG1]; rw [if_neg hv, if_neg hg, if_neg h3]
theorem maG3_abort (hr : fr = []) : maG3 n m no nl f h v fr = none := by simp [maG3, hr]
theorem maG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    maG3 n m no nl f h v fr = some (rdW (m.arr64 MAM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [maG3]; rw [if_neg hr, if_pos hh]
theorem maG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    maG3 n m no nl f h v fr = maG4 h (maNodeW n m no nl (f - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [maG3]; rw [if_neg hr, if_neg hh]
theorem maG4_some : maG4 h (some (r, m1)) = maG5 r (msetG maSch m1 h 0 r) := by rw [maG4]
theorem maG5_some : maG5 r (some m2) = some (r, m2) := by rw [maG5]
theorem maC_some : maC m (some r) = some (r, m) := by rw [maC]
theorem maNodeW_fvar (hg : g = 1) : maNodeW (n + 1) m no nl f1 g x y z = maGoW n m no nl f1 y := by
  simp [maNodeW, hg]
theorem maNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : maNodeW (n + 1) m no nl f1 g x y z =
    maB1 n no nl f1 y (maGoW n m no nl f1 x) := by
  have : ¬ g = 1 := by
    intro e; rcases hg with h | h | h <;> (rw [e] at h; exact absurd h (by decide))
  simp only [maNodeW]; rw [if_neg this, if_pos hg]
theorem maNodeW_let (hg : g = 7) : maNodeW (n + 1) m no nl f1 g x y z =
    maL1 n no nl f1 y z (maGoW n m no nl f1 x) := by
  simp [maNodeW, hg]
theorem maNodeW_proj (hg1 : g ≠ 1) (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    maNodeW (n + 1) m no nl f1 g x y z = maP1 n no nl x (maGoW n m no nl f1 z) := by
  simp only [maNodeW]; rw [if_neg hg1, if_neg hg2, if_neg hg3]
theorem maB1_some : maB1 n no nl f1 y (some (b1, m1)) = maB2 b1 (maGoW n m1 no nl f1 y) := by rw [maB1]
theorem maB2_some : maB2 b1 (some (b2, m2)) = some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m2) := by rw [maB2]
theorem maL1_some : maL1 n no nl f1 y z (some (b1, m1)) = maL2 n no nl f1 z b1 (maGoW n m1 no nl f1 y) := by rw [maL1]
theorem maL2_some : maL2 n no nl f1 z b1 (some (b2, m2)) = maL3 b1 b2 (maGoW n m2 no nl f1 z) := by rw [maL2]
theorem maL3_some : maL3 b1 b2 (some (b3, m3)) =
    some (if b1 ≠ 0 ∨ b2 ≠ 0 ∨ b3 ≠ 0 then 1 else 0, m3) := by rw [maL3]
theorem maP1_some : maP1 n no nl x (some (b1, m1)) = maP2 b1 m1 (containsW n m1 no nl x) := by rw [maP1]
theorem maP2_some : maP2 b1 m1 (some b2) = some (if b1 ≠ 0 ∨ b2 ≠ 0 then 1 else 0, m1) := by rw [maP2]
end arms


attribute [ind_grind] maGoW_abort maGoW_view maG1_abort maG1_leaf maG1_const maG1_node maG3_abort maG3_hit
  maG3_miss maG4_some maG5_some maC_some maNodeW_fvar maNodeW_bin maNodeW_let maNodeW_proj maB1_some
  maB2_some maL1_some maL2_some maL3_some maP1_some maP2_some

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
  (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
  (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)

def MaGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_any_go" [no, nl, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ maGoW n s₀.mem no nl f h = some (r.headD 0, s'.mem); ⊤⦄

def MaNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl f1 g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_any_node" [no, nl, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ maNodeW n s₀.mem no nl f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄

include hv hc hf hput hgo in
theorem maGo_step (n : Nat) (ih : MaNodeSpec p n) : MaGoSpec p (n + 1) := by
  unfold MaNodeSpec at ih
  intro s₀ no nl f h
  rw [invoke_eq _ hgo]
  simp only [callFn, mentionsAnyGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, slContains_spec p hc n, memoFindG_spec maSch p _ hf n,
      memoPutG_spec maSch p _ hput n, ih] <;> finish (gen := 20)

include hc hgo hnode in
theorem maNode_step (n : Nat) (ih : MaGoSpec p n) : MaNodeSpec p (n + 1) := by
  unfold MaGoSpec at ih
  intro s₀ no nl f1 g x y z
  rw [invoke_eq _ hnode]
  simp only [callFn, mentionsAnyNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      slContains_spec p hc n, ih] <;> finish (gen := 20)

include hv hc hf hput hgo hnode in
theorem maGo_spec (n : Nat) : MaGoSpec p n ∧ MaNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ no nl f h; rw [invoke_eq _ hgo]; simp only [callFn, mentionsAnyGo]; vcgen [exec] <;> grind
    · intro s₀ no nl f1 g x y z; rw [invoke_eq _ hnode]; simp only [callFn, mentionsAnyNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨maGo_step p hv hc hf hput hgo n ih.2, maNode_step p hc hgo hnode n ih.1⟩

end spec


def maArm (names : List NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .fvar _ ty => ConRon.Arena.mentionsAnyGo names memo fuel ty
  | .app f a => do
    let (b1, m) ← ConRon.Arena.mentionsAnyGo names memo fuel f
    let (b2, m2) ← ConRon.Arena.mentionsAnyGo names m fuel a
    pure (b1 || b2, m2)
  | .lam ty body => do
    let (b1, m) ← ConRon.Arena.mentionsAnyGo names memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsAnyGo names m fuel body
    pure (b1 || b2, m2)
  | .forallE ty body => do
    let (b1, m) ← ConRon.Arena.mentionsAnyGo names memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsAnyGo names m fuel body
    pure (b1 || b2, m2)
  | .letE ty val body => do
    let (b1, m) ← ConRon.Arena.mentionsAnyGo names memo fuel ty
    let (b2, m2) ← ConRon.Arena.mentionsAnyGo names m fuel val
    let (b3, m3) ← ConRon.Arena.mentionsAnyGo names m2 fuel body
    pure (b1 || b2 || b3, m3)
  | .proj s _ sub => do
    let (b, m) ← ConRon.Arena.mentionsAnyGo names memo fuel sub
    pure (names.contains s || b, m)
  | _ => pure (false, memo)

theorem mentionsAnyGo_succ' (names : List NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) :
    ConRon.Arena.mentionsAnyGo names memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (false, memo)
      | .sort _ => pure (false, memo)
      | .lit _ => pure (false, memo)
      | .const n _ => pure (names.contains n, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← maArm names memo fuel v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.mentionsAnyGo.eq_2]
  congr 1
  funext v
  cases v <;> first | rfl | (simp only [maArm, bind_assoc, pure_bind]; rfl)


theorem getD2_eq (vl : List Word) : vl.getD 2 0 = vl.tail.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> rfl
theorem getD3_eq (vl : List Word) : vl.getD 3 0 = vl.tail.tail.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩ <;> rfl
theorem getD1_eq' (vl : List Word) : vl.getD 1 0 = vl.tail.headD 0 := by
  rcases vl with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rfl

theorem maFrame_arena {m m' : Mem} {a : AState} (hf : MemFrame [MAM] [203] m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, MAM])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR

theorem maFrame_iw {m m' : Mem} (hf : MemFrame [MAM] [203] m m') : m'.arr64 IW = m.arr64 IW :=
  hf.1 IW (by decide) (by decide)

theorem slR_congr {m m' : Mem} (hI : m'.arr64 IW = m.arr64 IW) {o l : Word} {ws : List Word}
    (h : SlR m o l ws) : SlR m' o l ws := by
  induction h with
  | nil => exact SlR.nil
  | @cons o l ws hl _ ih =>
    have := SlR.cons (m := m') (o := o) hl ih
    simpa [rdW, hI] using this


/-- The word-valued memo relation of the mentions walk. -/
abbrev maMR (m : Mem) (mp : Std.HashMap EIdx Bool) : Prop :=
  MemoRG maSch bmKey (fun w : Word => w != 0) m mp

def MaGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (no nl f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool),
    maGoW n m no nl f h = some (r, m') → ArenaR m a → H h → SlR m no nl ws →
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → maMR m mp →
    ∃ b mp', (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m'

theorem maNodeBin_ok (n : Nat) (ih : MaGoOK n) (m m' : Mem) (a : AState) (no nl f1 g x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hg : g = 4 ∨ g = 5 ∨ g = 6) (hx : H x) (hy : H y)
    (hn : maNodeW (n + 1) m no nl f1 g x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (do
        let (b1, m) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) m f1.toNat (decE y)
        pure (b1 || b2, m2) : AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  rw [maNodeW_bin n m no nl f1 g x y z hg] at hn
  cases h1 : maGoW n m no nl f1 x with
  | none => rw [h1] at hn; simp [maB1] at hn
  | some p1 =>
    obtain ⟨b1w, m1⟩ := p1
    rw [h1, maB1_some] at hn
    cases h2 : maGoW n m1 no nl f1 y with
    | none => rw [h2] at hn; simp [maB2] at hn
    | some p2 =>
      obtain ⟨b2w, m2⟩ := p2
      rw [h2, maB2_some] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl f1 x b1w ws mp h1 hA hx hws hwlt hM
      obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a no nl f1 y b2w ws mp1 h2 (maFrame_arena hf1 hA) hy
        (slR_congr (maFrame_iw hf1) hws) hwlt hM1
      refine ⟨c1 || c2, mp2, ?_, ?_, hM2, hf1.trans hf2⟩
      · simp only [StateT.run_bind]
        rw [hr1]
        simp only [except_ok_bind, StateT.run_bind]
        rw [hr2]
        simp only [except_ok_bind]
        rfl
      · rw [← hb1, ← hb2]
        by_cases e1 : b1w = 0 <;> by_cases e2 : b2w = 0 <;> simp [e1, e2]


theorem maNodeLet_ok (n : Nat) (ih : MaGoOK n) (m m' : Mem) (a : AState) (no nl f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hx : H x) (hy : H y) (hz : H z)
    (hn : maNodeW (n + 1) m no nl f1 7 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (do
        let (b1, m) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) m f1.toNat (decE y)
        let (b3, m3) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) m2 f1.toNat (decE z)
        pure (b1 || b2 || b3, m3) : AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  rw [maNodeW_let n m no nl f1 7 x y z rfl] at hn
  cases h1 : maGoW n m no nl f1 x with
  | none => rw [h1] at hn; simp [maL1] at hn
  | some p1 =>
    obtain ⟨b1w, m1⟩ := p1
    rw [h1, maL1_some] at hn
    cases h2 : maGoW n m1 no nl f1 y with
    | none => rw [h2] at hn; simp [maL2] at hn
    | some p2 =>
      obtain ⟨b2w, m2⟩ := p2
      rw [h2, maL2_some] at hn
      cases h3 : maGoW n m2 no nl f1 z with
      | none => rw [h3] at hn; simp [maL3] at hn
      | some p3 =>
        obtain ⟨b3w, m3⟩ := p3
        rw [h3, maL3_some] at hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl f1 x b1w ws mp h1 hA hx hws hwlt hM
        obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a no nl f1 y b2w ws mp1 h2 (maFrame_arena hf1 hA) hy
          (slR_congr (maFrame_iw hf1) hws) hwlt hM1
        obtain ⟨c3, mp3, hr3, hb3, hM3, hf3⟩ := ih m2 m3 a no nl f1 z b3w ws mp2 h3
          (maFrame_arena (hf1.trans hf2) hA) hz (slR_congr (maFrame_iw (hf1.trans hf2)) hws) hwlt hM2
        refine ⟨c1 || c2 || c3, mp3, ?_, ?_, hM3, (hf1.trans hf2).trans hf3⟩
        · simp only [StateT.run_bind]
          rw [hr1]
          simp only [except_ok_bind, StateT.run_bind]
          rw [hr2]
          simp only [except_ok_bind, StateT.run_bind]
          rw [hr3]
          simp only [except_ok_bind]
          rfl
        · rw [← hb1, ← hb2, ← hb3]
          by_cases e1 : b1w = 0 <;> by_cases e2 : b2w = 0 <;> by_cases e3 : b3w = 0 <;> simp [e1, e2, e3]

theorem maNodeProj_ok (n : Nat) (ih : MaGoOK n) (m m' : Mem) (a : AState) (no nl f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hx : H x) (hz : H z)
    (hn : maNodeW (n + 1) m no nl f1 9 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (do
        let (b, m) ← ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f1.toNat (decE z)
        pure ((ws.map (fun w => (decI w : NIdx))).contains (decI x) || b, m) :
          AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  rw [maNodeW_proj n m no nl f1 9 x y z (by decide) (by decide) (by decide)] at hn
  cases h1 : maGoW n m no nl f1 z with
  | none => rw [h1] at hn; simp [maP1] at hn
  | some p1 =>
    obtain ⟨b1w, m1⟩ := p1
    rw [h1, maP1_some] at hn
    cases h2 : containsW n m1 no nl x with
    | none => rw [h2] at hn; simp [maP2] at hn
    | some b2w =>
      rw [h2, maP2_some] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl f1 z b1w ws mp h1 hA hz hws hwlt hM
      have hws1 := slR_congr (maFrame_iw hf1) hws
      have hcont := containsW_ok n _ _ _ _ _ _ hws1 h2
      refine ⟨(ws.map (fun w => (decI w : NIdx))).contains (decI x) || c1, mp1, ?_, ?_, hM1, hf1⟩
      · simp only [StateT.run_bind]
        rw [hr1]
        simp only [except_ok_bind]
        rfl
      · rw [← hb1, contains_decI ws x hwlt hx, hcont]
        generalize ws.contains x = bc
        by_cases e1 : b1w = 0 <;> cases bc <;> simp [e1]

theorem maNodeFVar_ok (n : Nat) (ih : MaGoOK n) (m m' : Mem) (a : AState) (no nl f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hy : H y)
    (hn : maNodeW (n + 1) m no nl f1 1 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f1.toNat (decE y)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  rw [maNodeW_fvar n m no nl f1 1 x y z rfl] at hn
  exact ih m m' a no nl f1 y r ws mp hn hA hy hws hwlt hM


/-- The non-leaf, non-`const` views: the ones whose walk goes through `mentions_any_node`. -/
def NodeV : ENodeView → Prop
  | .fvar .. | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem maNode_arm (k : Nat) (ih : MaGoOK k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeV v) (m m' : Mem) (a : AState) (no nl f1 r : Word) (ws : List Word)
    (mp : Std.HashMap EIdx Bool)
    (hn : maNodeW (k + 1) m no nl f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hA : ArenaR m a) (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (maArm (ws.map (fun w => (decI w : NIdx))) mp f1.toNat v).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  cases v with
  | fvar i ty =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, -, hy, hdy⟩ := hvr
    rw [hg] at hn
    have := maNodeFVar_ok k ih m m' a no nl f1 _ _ _ r ws mp hy hn hA hws hwlt hM
    rw [← hdy] at *
    simp only [maArm]; exact this
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := maNodeBin_ok k ih m m' a no nl f1 _ _ _ _ r ws mp (Or.inl hg) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [maArm]; exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := maNodeBin_ok k ih m m' a no nl f1 _ _ _ _ r ws mp (Or.inr (Or.inl hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [maArm]; exact this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := maNodeBin_ok k ih m m' a no nl f1 _ _ _ _ r ws mp (Or.inr (Or.inr hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [maArm]; exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := maNodeLet_ok k ih m m' a no nl f1 _ _ _ r ws mp hx hy hz hn hA hws hwlt hM
    rw [hdx, hdy, hdz] at this
    simp only [maArm]; exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := maNodeProj_ok k ih m m' a no nl f1 _ _ _ r ws mp hx hz hn hA hws hwlt hM
    rw [hdz, hdx] at this
    simp only [maArm]; exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv


theorem maSch_wf : maSch.WF := ⟨by decide, by decide⟩

theorem maTwin_node (names : List NIdx) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx)
    (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeV v) :
    (ConRon.Arena.mentionsAnyGo names memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← maArm names memo fuel v
          pure (r, m.insert h r) : AM (Bool × Std.HashMap EIdx Bool)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | rw [mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]

theorem maGo_nodeCase (j : Nat) (ih : ∀ k, k + 1 < j + 1 → MaGoOK k) (m m' : Mem) (a : AState)
    (no nl f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : NodeV v)
    (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 1 ∨ vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : maG1 j m no nl f h vl = some (r, m')) (hA : ArenaR m a) (hh : H h)
    (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp) :
    ∃ b mp', (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp (F + 1) (decE h)).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ maMR m' mp' ∧ MemFrame [MAM] [203] m m' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e | e <;> rw [e] <;> decide
  have hn3 : ¬ vl.headD 0 = 3 := by
    rcases hgs with e | e | e | e | e | e <;> rw [e] <;> decide
  rw [maG1_node j m no nl f h vl hvl hnl hn3] at hb
  rw [maTwin_node _ _ _ _ a v hv hnv]
  by_cases hfr : mfindG maSch m h 0 = []
  · rw [maG3_abort j m no nl f h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG maSch m h 0).headD 0 ≠ 0
  · rw [maG3_hit j m no nl f h vl _ hfr hhit] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hmem := memoRG_hit maSch bmKey (fun w : Word => w != 0) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨_, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
    simp only [hmem]; rfl
  · rw [maG3_miss j m no nl f h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss maSch bmKey (fun w : Word => w != 0) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases j with
    | zero => simp [maNodeW, maG4] at hb
    | succ k =>
      cases hnode : maNodeW (k + 1) m no nl (f - 1) (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
          (vl.tail.tail.tail.headD 0) with
      | none => rw [hnode] at hb; simp [maG4] at hb
      | some pn =>
        obtain ⟨rn, m1⟩ := pn
        rw [hnode, maG4_some] at hb
        cases hset : msetG maSch m1 h 0 rn with
        | none => rw [hset] at hb; simp [maG5] at hb
        | some m2 =>
          rw [hset, maG5_some] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          have hf1 : f - 1 = f - 1 := rfl
          have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
          obtain ⟨bb, mp1, hr1, hbb, hM1, hfr1⟩ := maNode_arm k (ih k (by omega)) vl v hvr hnv m m1 a no nl (f - 1) rn
            ws mp hnode hA hws hwlt hM
          rw [hF1] at hr1
          have hset' := memoRG_set maSch maSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
          have hfs : MemFrame [MAM] [203] m1 m2 := msetG_frame maSch maSch_wf m1 m2 h 0 rn hset
          refine ⟨bb, mp1.insert (decE h) bb, ?_, hbb, ?_, hfr1.trans hfs⟩
          · rw [hmiss]
            simp only [StateT.run_bind]
            rw [hr1]
            simp only [except_ok_bind]
            rfl
          · rw [← hbb]; exact hset'

theorem maGo_step_ok (j : Nat) (ih : ∀ k, k + 1 < j + 1 → MaGoOK k) : MaGoOK (j + 1) := by
  intro m m' a no nl f h r ws mp hb hA hh hws hwlt hM
  by_cases hf0 : f = 0
  · rw [maGoW_abort j m no nl f h hf0] at hb; simp at hb
  rw [maGoW_view j m no nl f h hf0] at hb
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [maG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h hne
    rw [hvl] at hvr hb
    cases v with
    | bvar i =>
      rw [hF, mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      rw [maG1_leaf j m no nl f h _ (by simp) (Or.inl hg0)] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | sort u =>
      rw [hF, mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      rw [maG1_leaf j m no nl f h _ (by simp) (Or.inr (Or.inl hg0))] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | lit l =>
      rw [hF, mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      rw [maG1_leaf j m no nl f h _ (by simp) (Or.inr (Or.inr hg0))] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | const nn us =>
      rw [hF, mentionsAnyGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      simp only [ViewR, getD1_eq'] at hvr
      obtain ⟨hg3, hx, hdx, -⟩ := hvr
      have hg3' : (g :: vt).headD 0 = 3 := hg3
      rw [maG1_const j m no nl f h _ (by simp) (by rw [hg3']; decide) hg3'] at hb
      cases hc : containsW j m no nl ((g :: vt).tail.headD 0) with
      | none => rw [hc] at hb; simp [maC] at hb
      | some rc =>
        rw [hc, maC_some] at hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        have hcv := containsW_ok j _ _ _ _ _ _ hws hc
        refine ⟨(ws.map (fun w => (decI w : NIdx))).contains nn, mp, ?_, ?_, hM, MemFrame.refl _ _ _⟩
        · rfl
        · rw [hcv, ← hdx, contains_decI ws _ hwlt hx]
          generalize ws.contains _ = bc
          cases bc <;> simp
    | fvar i ty => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inl hvr.1) hb hA hh hws hwlt hM
    | app f' x' => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inl hvr.1)) hb hA hh hws hwlt hM
    | lam f' x' => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inl hvr.1))) hb hA hh hws hwlt hM
    | forallE f' x' => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hA hh hws hwlt hM
    | letE t v' b' => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvr.1))))) hb hA hh hws hwlt hM
    | proj s i e => rw [hF]; exact maGo_nodeCase j ih m m' a no nl f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hvr.1))))) hb hA hh hws hwlt hM


theorem maGoOK (n : Nat) : MaGoOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a no nl f h r ws mp hb; simp [maGoW] at hb
    | succ j => exact maGo_step_ok j (fun k hk => ih k (by omega))

/-- **The stage relation across a writer above array 136 and `CTL[129]`** (the per-call memos). -/
theorem StageR.frame_hi {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem}
    {a : AState} {A : List ArrId} {C : List Word} (hS : StageR dn vis fe m a) (hf : MemFrame A C m m')
    (hA : ∀ b ∈ A, 137 ≤ b) (hC : ∀ x ∈ C, 130 ≤ x.toNat) (hA2 : IW ∉ A) (hC2 : (200 : Word) ∉ C) :
    StageR dn vis fe m' a ∧ IWGrow m m' := by
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW hA2 (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (fun h => by have := hA _ h; simp [EREC] at this)
    (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 200 hC2
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 :=
    hf.2.1 129 (fun h => by have := hC _ h; simp at this)
  refine ⟨⟨CheckR.frame_hi hA hC hf hS.1, ?_⟩, ?_⟩
  · simp only [IWOK, iwTop, erTop, hI, hE, h200, h129, hf.2.2.1 CTL]; exact hS.2
  · refine ⟨?_, ?_, fun i _ => by rw [hI], fun i _ => by rw [hE]⟩
    · simp only [iwTop, h200]; exact Nat.le_refl _
    · simp only [erTop, h129]; exact Nat.le_refl _


section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
  (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
  (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)
include hv hc hf hput hgo hnode

/-- **`mentions_any_go` (with `mentions_any_node`) refines `mentionsAnyGo`**, from a memo related to
the twin's. -/
@[refines ConRon.Arena.mentionsAnyGo]
theorem mentionsAnyGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl f h : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool) (hh : H h)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hM : maMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "mentions_any_go" [no, nl, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)) a₀ ∧
      AM.st (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)) a₀ = a₀ ∧
      (r.headD 0 != 0) =
        (AM.res (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)) a₀).1 ∧
      maMR s'.mem
        (AM.res (ConRon.Arena.mentionsAnyGo (ws.map (fun w => (decI w : NIdx))) mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((maGo_spec p hv hc hf hput hgo hnode n).1 s₀ no nl f h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', hrun, hb, hM', hfr⟩ := maGoOK n _ _ a₀ no nl f h _ ws mp hm hS.1.arena.1 hh hws hwlt hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  refine ⟨hl, hok, hst, by rw [hres]; exact hb, by rw [hres]; exact hM', hS', hg⟩

end census


/-! ### `mentions_any_const` -/

def maClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if rdW (m1.arr64 CTL) maSch.cs + 2 = 0 then none else some (r, mclearG maSch m1)

def maConstW (n : Nat) (m : Mem) (no nl e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) maSch.cs + 2 = 0 then none else maClrK (maGoW n (mclearG maSch m) no nl CWF e)

theorem maConstW_eq (n : Nat) (m : Mem) (no nl e : Word) (h0 : rdW (m.arr64 CTL) maSch.cs + 2 ≠ 0) :
    maConstW n m no nl e = maClrK (maGoW n (mclearG maSch m) no nl CWF e) := by simp [maConstW, h0]
theorem maClrK_some (r : Word) (m1 : Mem) (h0 : rdW (m1.arr64 CTL) maSch.cs + 2 ≠ 0) :
    maClrK (some (r, m1)) = some (r, mclearG maSch m1) := by simp [maClrK, h0]
attribute [ind_grind] maConstW_eq maClrK_some

theorem mentionsAnyConst_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "sl_contains" = some slContains)
    (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
    (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
    (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)
    (hcl : p.lookup "ma_clear" = some (memoClearG maSch))
    (hp : p.lookup "mentions_any_const" = some mentionsAnyConst) (n : Nat) (s₀ : St) (no nl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_any_const" [no, nl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ maConstW n s₀.mem no nl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (maGo_spec p hv hc hf hput hgo hnode n).1
  unfold MaGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, mentionsAnyConst]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec maSch p _ hcl n, ih] <;>
    finish


theorem maConstW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl e r : Word) (ws : List Word) (mp0 : Std.HashMap EIdx Bool)
    (hb : maConstW n m no nl e = some (r, m')) (hS : StageR dn vis fe m a) (hh : H e)
    (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : maMR m mp0) :
    ∃ b, (ConRon.Arena.mentionsAnyConst (ws.map (fun w => (decI w : NIdx))) (decE e)).run a =
        .ok (b, a) ∧ (r != 0) = b ∧ maMR m' ∅ ∧ StageR dn vis fe m' a ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) maSch.cs + 2 = 0
  · simp [maConstW, h0] at hb
  rw [maConstW_eq n m no nl e h0] at hb
  have hf0 := mclearG_frame maSch m
  have hM0 := memoRG_clear maSch maSch_wf bmKey (fun w : Word => w != 0) m mp0 hM h0
  have hA0 : ArenaR (mclearG maSch m) a :=
    ArenaR.frame (A := []) (C := [maSch.cs, maSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by simp [maSch] at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.1.arena.1
  have hws0 : SlR (mclearG maSch m) no nl ws := slR_congr (hf0.1 IW (by simp) (by decide)) hws
  cases hg : maGoW n (mclearG maSch m) no nl CWF e with
  | none => rw [hg] at hb; simp [maClrK] at hb
  | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [hg] at hb
    by_cases h1 : rdW (m1.arr64 CTL) maSch.cs + 2 = 0
    · simp [maClrK, h1] at hb
    rw [maClrK_some r1 m1 h1] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨c, mp1, hrun, hbb, hM1, hfr1⟩ := maGoOK n _ _ a no nl CWF e r1 ws ∅ hg hA0 hh hws0 hwlt hM0
    rw [CWF_eq] at hrun
    have hM2 := memoRG_clear maSch maSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h1
    have hf2 := mclearG_frame maSch m1
    have hfall : MemFrame [MAM] [maSch.cs, maSch.cs + 1] m (mclearG maSch m1) :=
      ((hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp [maSch]))).trans
        (hf2.mono (by simp) (by simp))
    obtain ⟨hS', hg'⟩ := StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
      (by intro x hx; simp [maSch] at hx; rcases hx with rfl | rfl <;> decide) (by decide)
      (by simp [maSch])
    refine ⟨c, ?_, hbb, hM2, hS', hg'⟩
    simp only [ConRon.Arena.mentionsAnyConst, StateT.run_bind]
    rw [hrun]
    rfl


section census3
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "ma_find" = some (memoFindG maSch)) (hput : p.lookup "ma_put" = some (memoPutG maSch))
  (hgo : p.lookup "mentions_any_go" = some mentionsAnyGo)
  (hnode : p.lookup "mentions_any_node" = some mentionsAnyNode)
  (hcl : p.lookup "ma_clear" = some (memoClearG maSch))
  (hp : p.lookup "mentions_any_const" = some mentionsAnyConst)
include hv hc hf hput hgo hnode hcl hp

/-- **`mentions_any_const` refines `mentionsAnyConst`**: one memoised DAG walk between two clears;
the per-call memo is any well-formed one on entry (`mp0`) and empty after. -/
@[refines ConRon.Arena.mentionsAnyConst]
theorem mentionsAnyConst_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl e : Word) (ws : List Word) (mp0 : Std.HashMap EIdx Bool) (hh : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hM : maMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "mentions_any_const" [no, nl, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.mentionsAnyConst (ws.map (fun w => (decI w : NIdx))) (decE e)) a₀ ∧
      AM.st (ConRon.Arena.mentionsAnyConst (ws.map (fun w => (decI w : NIdx))) (decE e)) a₀ = a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.mentionsAnyConst (ws.map (fun w => (decI w : NIdx))) (decE e)) a₀ ∧
      maMR s'.mem ∅ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (mentionsAnyConst_spec p hv hc hf hput hgo hnode hcl hp n s₀ no nl e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, hrun, hb, hM', hS', hg⟩ := maConstW_ok n dn fe vis _ _ a₀ no nl e _ ws mp0 hm hS hh hws hwlt hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hb, hM', hS', hg⟩

end census3

/-! ## `nest_occ_go`, `nest_occ_node`: word models -/

mutual
def noGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lo, hi, f, h =>
    if f = 0 then none else noG1 n m no nl lo hi f h (eViewW m h)
def noG1 (n : Nat) (m : Mem) (no nl lo hi f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (0, m)
  else if v.headD 0 = 1 then
    some ((if lo ≤ v.tail.headD 0 ∧ v.tail.headD 0 < hi then 1 else 0), m)
  else if v.headD 0 = 3 then noC m (containsW n m no nl (v.tail.headD 0))
  else noG3 n m no nl lo hi f h v (mfindG noSch m h 0)
def noG3 (n : Nat) (m : Mem) (no nl lo hi f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 NOM) (fr.tail.headD 0 * 4 + 3), m)
  else noG4 h (noNodeW n m no nl lo hi (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def noG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => noG5 r (msetG noSch m1 h 0 r)
def noG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def noC (m : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some r => some (r, m)
def noNodeW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lo, hi, f1, g, x, y, z =>
    if g = 4 ∨ g = 5 ∨ g = 6 then noB1 n no nl lo hi f1 y (noGoW n m no nl lo hi f1 x)
    else if g = 7 then noL1 n no nl lo hi f1 y z (noGoW n m no nl lo hi f1 x)
    else noGoW n m no nl lo hi f1 z
def noB1 (n : Nat) (no nl lo hi f1 y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => if b1 ≠ 0 then some (1, m1) else noGoW n m1 no nl lo hi f1 y
def noL1 (n : Nat) (no nl lo hi f1 y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b1, m1) => if b1 ≠ 0 then some (1, m1) else noL2 n no nl lo hi f1 z (noGoW n m1 no nl lo hi f1 y)
def noL2 (n : Nat) (no nl lo hi f1 z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (b2, m2) => if b2 ≠ 0 then some (1, m2) else noGoW n m2 no nl lo hi f1 z
end

section arms
variable (n : Nat) (m m1 m2 : Mem) (no nl lo hi f f1 h g x y z b1 b2 r : Word) (v fr : List Word)
theorem noGoW_abort (hf : f = 0) : noGoW (n + 1) m no nl lo hi f h = none := by simp [noGoW, hf]
theorem noGoW_view (hf : f ≠ 0) :
    noGoW (n + 1) m no nl lo hi f h = noG1 n m no nl lo hi f h (eViewW m h) := by simp [noGoW, hf]
theorem noG1_abort (hv : v = []) : noG1 n m no nl lo hi f h v = none := by simp [noG1, hv]
theorem noG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    noG1 n m no nl lo hi f h v = some (0, m) := by simp only [noG1]; rw [if_neg hv, if_pos hg]
theorem noG1_fvar (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h1 : v.headD 0 = 1) : noG1 n m no nl lo hi f h v =
      some ((if lo ≤ v.tail.headD 0 ∧ v.tail.headD 0 < hi then 1 else 0), m) := by
  simp only [noG1]; rw [if_neg hv, if_neg hg, if_pos h1]
theorem noG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h1 : ¬ v.headD 0 = 1) (h3 : v.headD 0 = 3) :
    noG1 n m no nl lo hi f h v = noC m (containsW n m no nl (v.tail.headD 0)) := by
  simp only [noG1]; rw [if_neg hv, if_neg hg, if_neg h1, if_pos h3]
theorem noG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h1 : ¬ v.headD 0 = 1) (h3 : ¬ v.headD 0 = 3) :
    noG1 n m no nl lo hi f h v = noG3 n m no nl lo hi f h v (mfindG noSch m h 0) := by
  simp only [noG1]; rw [if_neg hv, if_neg hg, if_neg h1, if_neg h3]
theorem noG3_abort (hr : fr = []) : noG3 n m no nl lo hi f h v fr = none := by simp [noG3, hr]
theorem noG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    noG3 n m no nl lo hi f h v fr = some (rdW (m.arr64 NOM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [noG3]; rw [if_neg hr, if_pos hh]
theorem noG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    noG3 n m no nl lo hi f h v fr = noG4 h (noNodeW n m no nl lo hi (f - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [noG3]; rw [if_neg hr, if_neg hh]
theorem noG4_some : noG4 h (some (r, m1)) = noG5 r (msetG noSch m1 h 0 r) := by rw [noG4]
theorem noG5_some : noG5 r (some m2) = some (r, m2) := by rw [noG5]
theorem noC_some : noC m (some r) = some (r, m) := by rw [noC]
theorem noNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) : noNodeW (n + 1) m no nl lo hi f1 g x y z =
    noB1 n no nl lo hi f1 y (noGoW n m no nl lo hi f1 x) := by
  simp only [noNodeW]; rw [if_pos hg]
theorem noNodeW_let (hg : g = 7) : noNodeW (n + 1) m no nl lo hi f1 g x y z =
    noL1 n no nl lo hi f1 y z (noGoW n m no nl lo hi f1 x) := by
  have : ¬ (g = 4 ∨ g = 5 ∨ g = 6) := by
    intro e; rcases e with e | e | e <;> (rw [hg] at e; exact absurd e (by decide))
  simp only [noNodeW]; rw [if_neg this, if_pos hg]
theorem noNodeW_proj (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    noNodeW (n + 1) m no nl lo hi f1 g x y z = noGoW n m no nl lo hi f1 z := by
  simp only [noNodeW]; rw [if_neg hg2, if_neg hg3]
theorem noB1_some : noB1 n no nl lo hi f1 y (some (b1, m1)) =
    (if b1 ≠ 0 then some (1, m1) else noGoW n m1 no nl lo hi f1 y) := by rw [noB1]
theorem noL1_some : noL1 n no nl lo hi f1 y z (some (b1, m1)) =
    (if b1 ≠ 0 then some (1, m1) else noL2 n no nl lo hi f1 z (noGoW n m1 no nl lo hi f1 y)) := by rw [noL1]
theorem noL2_some : noL2 n no nl lo hi f1 z (some (b2, m2)) =
    (if b2 ≠ 0 then some (1, m2) else noGoW n m2 no nl lo hi f1 z) := by rw [noL2]
end arms

attribute [ind_grind] noGoW_abort noGoW_view noG1_abort noG1_leaf noG1_fvar noG1_const noG1_node
  noG3_abort noG3_hit noG3_miss noG4_some noG5_some noC_some noNodeW_bin noNodeW_let noNodeW_proj
  noB1_some noL1_some noL2_some

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "no_find" = some (memoFindG noSch)) (hput : p.lookup "no_put" = some (memoPutG noSch))
  (hgo : p.lookup "nest_occ_go" = some nestOccGo)
  (hnode : p.lookup "nest_occ_node" = some nestOccNode)

def NoGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl lo hi f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ_go" [no, nl, lo, hi, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ noGoW n s₀.mem no nl lo hi f h = some (r.headD 0, s'.mem); ⊤⦄

def NoNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl lo hi f1 g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ_node" [no, nl, lo, hi, f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ noNodeW n s₀.mem no nl lo hi f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄

include hv hc hf hput hgo in
theorem noGo_step (n : Nat) (ih : NoNodeSpec p n) : NoGoSpec p (n + 1) := by
  unfold NoNodeSpec at ih
  intro s₀ no nl lo hi f h
  rw [invoke_eq _ hgo]
  simp only [callFn, nestOccGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, slContains_spec p hc n, memoFindG_spec noSch p _ hf n,
      memoPutG_spec noSch p _ hput n, ih] <;> finish (gen := 20)

include hc hgo hnode in
theorem noNode_step (n : Nat) (ih : NoGoSpec p n) : NoNodeSpec p (n + 1) := by
  unfold NoGoSpec at ih
  intro s₀ no nl lo hi f1 g x y z
  rw [invoke_eq _ hnode]
  simp only [callFn, nestOccNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      slContains_spec p hc n, ih] <;> finish (gen := 20)

include hv hc hf hput hgo hnode in
theorem noGo_spec (n : Nat) : NoGoSpec p n ∧ NoNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ no nl lo hi f h; rw [invoke_eq _ hgo]; simp only [callFn, nestOccGo]; vcgen [exec] <;> grind
    · intro s₀ no nl lo hi f1 g x y z; rw [invoke_eq _ hnode]; simp only [callFn, nestOccNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨noGo_step p hv hc hf hput hgo n ih.2, noNode_step p hc hgo hnode n ih.1⟩

end spec


def noArm (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .app f a => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel f
    if b then pure (true, m) else ConRon.Arena.nestOccGo names lo hi m fuel a
  | .lam ty body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m) else ConRon.Arena.nestOccGo names lo hi m fuel body
  | .forallE ty body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m) else ConRon.Arena.nestOccGo names lo hi m fuel body
  | .letE ty val body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel val
      if b2 then pure (true, m2) else ConRon.Arena.nestOccGo names lo hi m2 fuel body
  | .proj _ _ sub => ConRon.Arena.nestOccGo names lo hi memo fuel sub
  | _ => pure (false, memo)

/-- The twin's arm for a non-leaf view, with the memo insertion each branch makes. -/
def noArmI (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) :
    ENodeView → AM (Bool × Std.HashMap EIdx Bool)
  | .app f a => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel f
    if b then pure (true, m.insert h true) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel a
      pure (b2, m2.insert h b2)
  | .lam ty body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m.insert h true) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel body
      pure (b2, m2.insert h b2)
  | .forallE ty body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m.insert h true) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel body
      pure (b2, m2.insert h b2)
  | .letE ty val body => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel ty
    if b then pure (true, m.insert h true) else do
      let (b2, m2) ← ConRon.Arena.nestOccGo names lo hi m fuel val
      if b2 then pure (true, m2.insert h true) else do
        let (b3, m3) ← ConRon.Arena.nestOccGo names lo hi m2 fuel body
        pure (b3, m3.insert h b3)
  | .proj _ _ sub => do
    let (b, m) ← ConRon.Arena.nestOccGo names lo hi memo fuel sub
    pure (b, m.insert h b)
  | _ => pure (false, memo.insert h false)

def NodeVo : ENodeView → Prop
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem nestOccGo_succ' (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat)
    (h : EIdx) :
    ConRon.Arena.nestOccGo names lo hi memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (false, memo)
      | .sort _ => pure (false, memo)
      | .lit _ => pure (false, memo)
      | .fvar i _ => pure (decide (lo ≤ i) && decide (i < hi), memo)
      | .const n _ => pure (names.contains n, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => noArmI names lo hi memo fuel h v) := by
  rw [ConRon.Arena.nestOccGo.eq_2]
  congr 1

theorem noTwin_node (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat)
    (h : EIdx) (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeVo v) :
    (ConRon.Arena.nestOccGo names lo hi memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => noArmI names lo hi memo fuel h v : AM (Bool × Std.HashMap EIdx Bool)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [ConRon.Arena.nestOccGo.eq_2, StateT.run_bind, view_run _ a _ hv, except_ok_bind]; rfl)

theorem noArmI_eq (names : List NIdx) (lo hi : Nat) (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx)
    (v : ENodeView) (hnv : NodeVo v) :
    noArmI names lo hi memo fuel h v = (do
      let (r, m) ← noArm names lo hi memo fuel v
      pure (r, m.insert h r) : AM (Bool × Std.HashMap EIdx Bool)) := by
  cases v with
  | letE ty val body =>
    simp only [noArmI, noArm, bind_assoc]
    congr 1; funext x
    split
    · simp
    · simp only [bind_assoc, pure_bind]
      congr 1; funext y
      split <;> simp
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv
  | proj _ _ _ => simp [noArmI, noArm]
  | app f a =>
    simp only [noArmI, noArm, bind_assoc]
    congr 1; funext x
    split <;> simp
  | lam f a =>
    simp only [noArmI, noArm, bind_assoc]
    congr 1; funext x
    split <;> simp
  | forallE f a =>
    simp only [noArmI, noArm, bind_assoc]
    congr 1; funext x
    split <;> simp

theorem noFrame_arena {m m' : Mem} {a : AState} (hf : MemFrame [NOM] [205] m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, NOM])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR

theorem noFrame_iw {m m' : Mem} (hf : MemFrame [NOM] [205] m m') : m'.arr64 IW = m.arr64 IW :=
  hf.1 IW (by decide) (by decide)

abbrev noMR (m : Mem) (mp : Std.HashMap EIdx Bool) : Prop :=
  MemoRG noSch bmKey (fun w : Word => w != 0) m mp

def NoGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (no nl lo hi f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool),
    noGoW n m no nl lo hi f h = some (r, m') → ArenaR m a → H h → SlR m no nl ws →
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → noMR m mp →
    ∃ b mp', (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat
        (decE h)).run a = .ok ((b, mp'), a) ∧ (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m'

theorem noNodeBin_ok (n : Nat) (ih : NoGoOK n) (m m' : Mem) (a : AState) (no nl lo hi f1 g x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hg : g = 4 ∨ g = 5 ∨ g = 6) (hx : H x) (hy : H y)
    (hn : noNodeW (n + 1) m no nl lo hi f1 g x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (do
        let (b, m) ← ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f1.toNat (decE x)
        if b then pure (true, m) else
          ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat m f1.toNat (decE y) :
          AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  rw [noNodeW_bin n m no nl lo hi f1 g x y z hg] at hn
  cases h1 : noGoW n m no nl lo hi f1 x with
  | none => rw [h1] at hn; simp [noB1] at hn
  | some p1 =>
    obtain ⟨b1w, m1⟩ := p1
    rw [h1, noB1_some] at hn
    obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl lo hi f1 x b1w ws mp h1 hA hx hws hwlt hM
    by_cases e1 : b1w ≠ 0
    · rw [if_pos e1] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      have hc1 : c1 = true := by rw [← hb1]; simpa using e1
      refine ⟨true, mp1, ?_, by simp, hM1, hf1⟩
      simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind, hc1, if_true]
      rfl
    · rw [if_neg e1] at hn
      have hc1 : c1 = false := by rw [← hb1]; simpa using e1
      obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m' a no nl lo hi f1 y r ws mp1 hn (noFrame_arena hf1 hA) hy
        (slR_congr (noFrame_iw hf1) hws) hwlt hM1
      refine ⟨c2, mp2, ?_, hb2, hM2, hf1.trans hf2⟩
      simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind, hc1]
      simpa using hr2


theorem noNodeLet_ok (n : Nat) (ih : NoGoOK n) (m m' : Mem) (a : AState) (no nl lo hi f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hx : H x) (hy : H y) (hz : H z)
    (hn : noNodeW (n + 1) m no nl lo hi f1 7 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (do
        let (b, m) ← ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f1.toNat (decE x)
        if b then pure (true, m) else do
          let (b2, m2) ← ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat m f1.toNat (decE y)
          if b2 then pure (true, m2) else
            ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat m2 f1.toNat (decE z) :
          AM (Bool × Std.HashMap EIdx Bool)).run a = .ok ((b, mp'), a) ∧
      (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  rw [noNodeW_let n m no nl lo hi f1 7 x y z rfl] at hn
  cases h1 : noGoW n m no nl lo hi f1 x with
  | none => rw [h1] at hn; simp [noL1] at hn
  | some p1 =>
    obtain ⟨b1w, m1⟩ := p1
    rw [h1, noL1_some] at hn
    obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a no nl lo hi f1 x b1w ws mp h1 hA hx hws hwlt hM
    by_cases e1 : b1w ≠ 0
    · rw [if_pos e1] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      have hc1 : c1 = true := by rw [← hb1]; simpa using e1
      refine ⟨true, mp1, ?_, by simp, hM1, hf1⟩
      simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind, hc1, if_true]
      rfl
    · rw [if_neg e1] at hn
      have hc1 : c1 = false := by rw [← hb1]; simpa using e1
      cases h2 : noGoW n m1 no nl lo hi f1 y with
      | none => rw [h2] at hn; simp [noL2] at hn
      | some p2 =>
        obtain ⟨b2w, m2⟩ := p2
        rw [h2, noL2_some] at hn
        have hA1 := noFrame_arena hf1 hA
        have hws1 := slR_congr (noFrame_iw hf1) hws
        obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a no nl lo hi f1 y b2w ws mp1 h2 hA1 hy hws1 hwlt hM1
        by_cases e2 : b2w ≠ 0
        · rw [if_pos e2] at hn
          simp only [Option.some.injEq, Prod.mk.injEq] at hn
          obtain ⟨rfl, rfl⟩ := hn
          have hc2 : c2 = true := by rw [← hb2]; simpa using e2
          refine ⟨true, mp2, ?_, by simp, hM2, hf1.trans hf2⟩
          simp only [StateT.run_bind]
          rw [hr1]
          simp only [except_ok_bind, hc1, StateT.run_bind, Bool.false_eq_true, ↓reduceIte]
          rw [hr2]
          simp only [except_ok_bind, hc2, ↓reduceIte]
          rfl
        · rw [if_neg e2] at hn
          have hc2 : c2 = false := by rw [← hb2]; simpa using e2
          obtain ⟨c3, mp3, hr3, hb3, hM3, hf3⟩ := ih m2 m' a no nl lo hi f1 z r ws mp2 hn
            (noFrame_arena (hf1.trans hf2) hA) hz (slR_congr (noFrame_iw (hf1.trans hf2)) hws) hwlt hM2
          refine ⟨c3, mp3, ?_, hb3, hM3, (hf1.trans hf2).trans hf3⟩
          simp only [StateT.run_bind]
          rw [hr1]
          simp only [except_ok_bind, hc1, StateT.run_bind, Bool.false_eq_true, ↓reduceIte]
          rw [hr2]
          simp only [except_ok_bind, hc2, Bool.false_eq_true, ↓reduceIte]
          simpa using hr3


theorem noNodeProj_ok (n : Nat) (ih : NoGoOK n) (m m' : Mem) (a : AState) (no nl lo hi f1 x y z r : Word)
    (ws : List Word) (mp : Std.HashMap EIdx Bool) (hz : H z)
    (hn : noNodeW (n + 1) m no nl lo hi f1 9 x y z = some (r, m')) (hA : ArenaR m a) (hws : SlR m no nl ws)
    (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f1.toNat
        (decE z)).run a = .ok ((b, mp'), a) ∧ (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  rw [noNodeW_proj n m no nl lo hi f1 9 x y z (by decide) (by decide)] at hn
  exact ih m m' a no nl lo hi f1 z r ws mp hn hA hz hws hwlt hM

theorem noNode_arm (k : Nat) (ih : NoGoOK k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVo v) (m m' : Mem) (a : AState) (no nl lo hi f1 r : Word) (ws : List Word)
    (mp : Std.HashMap EIdx Bool)
    (hn : noNodeW (k + 1) m no nl lo hi f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hA : ArenaR m a) (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (noArm (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f1.toNat v).run a =
        .ok ((b, mp'), a) ∧ (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  cases v with
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := noNodeBin_ok k ih m m' a no nl lo hi f1 _ _ _ _ r ws mp (Or.inl hg) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [noArm]; exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := noNodeBin_ok k ih m m' a no nl lo hi f1 _ _ _ _ r ws mp (Or.inr (Or.inl hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [noArm]; exact this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := noNodeBin_ok k ih m m' a no nl lo hi f1 _ _ _ _ r ws mp (Or.inr (Or.inr hg)) hx hy hn hA hws hwlt hM
    rw [hdx, hdy] at this
    simp only [noArm]; exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := noNodeLet_ok k ih m m' a no nl lo hi f1 _ _ _ r ws mp hx hy hz hn hA hws hwlt hM
    rw [hdx, hdy, hdz] at this
    simp only [noArm]; exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := noNodeProj_ok k ih m m' a no nl lo hi f1 _ _ _ r ws mp hz hn hA hws hwlt hM
    rw [hdz] at this
    simp only [noArm]; exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv

theorem noSch_wf : noSch.WF := ⟨by decide, by decide⟩

theorem noGo_nodeCase (j : Nat) (ih : ∀ k, k + 1 < j + 1 → NoGoOK k) (m m' : Mem) (a : AState)
    (no nl lo hi f h r : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVo v) (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : noG1 j m no nl lo hi f h vl = some (r, m')) (hA : ArenaR m a) (hh : H h)
    (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp) :
    ∃ b mp', (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp (F + 1)
        (decE h)).run a = .ok ((b, mp'), a) ∧ (r != 0) = b ∧ noMR m' mp' ∧ MemFrame [NOM] [205] m m' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have hn1 : ¬ vl.headD 0 = 1 := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have hn3 : ¬ vl.headD 0 = 3 := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  rw [noG1_node j m no nl lo hi f h vl hvl hnl hn1 hn3] at hb
  rw [noTwin_node _ _ _ _ _ _ a v hv hnv]
  by_cases hfr : mfindG noSch m h 0 = []
  · rw [noG3_abort j m no nl lo hi f h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG noSch m h 0).headD 0 ≠ 0
  · rw [noG3_hit j m no nl lo hi f h vl _ hfr hhit] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hmem := memoRG_hit noSch bmKey (fun w : Word => w != 0) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨_, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
    simp only [hmem]; rfl
  · rw [noG3_miss j m no nl lo hi f h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss noSch bmKey (fun w : Word => w != 0) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases j with
    | zero => simp [noNodeW, noG4] at hb
    | succ k =>
      cases hnode : noNodeW (k + 1) m no nl lo hi (f - 1) (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
          (vl.tail.tail.tail.headD 0) with
      | none => rw [hnode] at hb; simp [noG4] at hb
      | some pn =>
        obtain ⟨rn, m1⟩ := pn
        rw [hnode, noG4_some] at hb
        cases hset : msetG noSch m1 h 0 rn with
        | none => rw [hset] at hb; simp [noG5] at hb
        | some m2 =>
          rw [hset, noG5_some] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
          obtain ⟨bb, mp1, hr1, hbb, hM1, hfr1⟩ := noNode_arm k (ih k (by omega)) vl v hvr hnv m m1 a no nl lo hi
            (f - 1) rn ws mp hnode hA hws hwlt hM
          rw [hF1] at hr1
          have hset' := memoRG_set noSch noSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
          have hfs : MemFrame [NOM] [205] m1 m2 := msetG_frame noSch noSch_wf m1 m2 h 0 rn hset
          refine ⟨bb, mp1.insert (decE h) bb, ?_, hbb, ?_, hfr1.trans hfs⟩
          · rw [hmiss]
            simp only [noArmI_eq _ _ _ _ _ _ v hnv, StateT.run_bind]
            rw [hr1]
            simp only [except_ok_bind]
            rfl
          · rw [← hbb]; exact hset'


theorem noGo_step_ok (j : Nat) (ih : ∀ k, k + 1 < j + 1 → NoGoOK k) : NoGoOK (j + 1) := by
  intro m m' a no nl lo hi f h r ws mp hb hA hh hws hwlt hM
  by_cases hf0 : f = 0
  · rw [noGoW_abort j m no nl lo hi f h hf0] at hb; simp at hb
  rw [noGoW_view j m no nl lo hi f h hf0] at hb
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [noG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA h hne
    rw [hvl] at hvr hb
    cases v with
    | bvar i =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      rw [noG1_leaf j m no nl lo hi f h _ (by simp) (Or.inl hg0)] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | sort u =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      rw [noG1_leaf j m no nl lo hi f h _ (by simp) (Or.inr (Or.inl hg0))] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | lit l =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      rw [noG1_leaf j m no nl lo hi f h _ (by simp) (Or.inr (Or.inr hg0))] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨false, mp, rfl, rfl, hM, MemFrame.refl _ _ _⟩
    | const nn us =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      simp only [ViewR, getD1_eq'] at hvr
      obtain ⟨hg3, hx, hdx, -⟩ := hvr
      have hg3' : (g :: vt).headD 0 = 3 := hg3
      rw [noG1_const j m no nl lo hi f h _ (by simp) (by rw [hg3']; decide) (by rw [hg3']; decide) hg3'] at hb
      cases hc : containsW j m no nl ((g :: vt).tail.headD 0) with
      | none => rw [hc] at hb; simp [noC] at hb
      | some rc =>
        rw [hc, noC_some] at hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        have hcv := containsW_ok j _ _ _ _ _ _ hws hc
        refine ⟨(ws.map (fun w => (decI w : NIdx))).contains nn, mp, ?_, ?_, hM, MemFrame.refl _ _ _⟩
        · rfl
        · rw [hcv, ← hdx, contains_decI ws _ hwlt hx]
          generalize ws.contains _ = bc
          cases bc <;> simp
    | fvar i ty =>
      rw [hF, nestOccGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      simp only [ViewR, getD1_eq'] at hvr
      obtain ⟨hg1, hix, -⟩ := hvr
      have hg1' : (g :: vt).headD 0 = 1 := hg1
      rw [noG1_fvar j m no nl lo hi f h _ (by simp) (by rw [hg1']; decide) hg1'] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨decide (lo.toNat ≤ i) && decide (i < hi.toNat), mp, rfl, ?_, hM, MemFrame.refl _ _ _⟩
      generalize (g :: vt).tail.headD 0 = x at hix ⊢
      subst hix
      simp only [← UInt64.le_iff_toNat_le, ← UInt64.lt_iff_toNat_lt]
      by_cases c1 : lo ≤ x <;> by_cases c2 : x < hi <;> simp [c1, c2]
    | app f' x' => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inl hvr.1) hb hA hh hws hwlt hM
    | lam f' x' => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inl hvr.1)) hb hA hh hws hwlt hM
    | forallE f' x' => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inl hvr.1))) hb hA hh hws hwlt hM
    | letE t v' b' => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hA hh hws hwlt hM
    | proj s i e => rw [hF]; exact noGo_nodeCase j ih m m' a no nl lo hi f h r ws mp F hF hf0 _ _ hvr trivial hv (by simp) (Or.inr (Or.inr (Or.inr (Or.inr hvr.1)))) hb hA hh hws hwlt hM

theorem noGoOK (n : Nat) : NoGoOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a no nl lo hi f h r ws mp hb; simp [noGoW] at hb
    | succ j => exact noGo_step_ok j (fun k hk => ih k (by omega))




section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "no_find" = some (memoFindG noSch)) (hput : p.lookup "no_put" = some (memoPutG noSch))
  (hgo : p.lookup "nest_occ_go" = some nestOccGo)
  (hnode : p.lookup "nest_occ_node" = some nestOccNode)
include hv hc hf hput hgo hnode

/-- **`nest_occ_go` (with `nest_occ_node`) refines `nestOccGo`**, from a memo related to
the twin's. -/
@[refines ConRon.Arena.nestOccGo]
theorem nestOccGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lo hi f h : Word) (ws : List Word) (mp : Std.HashMap EIdx Bool) (hh : H h)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hM : noMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ_go" [no, nl, lo, hi, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat (decE h)) a₀ ∧
      AM.st (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat (decE h)) a₀ = a₀ ∧
      (r.headD 0 != 0) =
        (AM.res (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat (decE h)) a₀).1 ∧
      noMR s'.mem
        (AM.res (ConRon.Arena.nestOccGo (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((noGo_spec p hv hc hf hput hgo hnode n).1 s₀ no nl lo hi f h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, mp', hrun, hb, hM', hfr⟩ := noGoOK n _ _ a₀ no nl lo hi f h _ ws mp hm hS.1.arena.1 hh hws hwlt hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  refine ⟨hl, hok, hst, by rw [hres]; exact hb, by rw [hres]; exact hM', hS', hg⟩

end census


/-! ### `nest_occ` -/

def noClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if rdW (m1.arr64 CTL) noSch.cs + 2 = 0 then none else some (r, mclearG noSch m1)

def noConstW (n : Nat) (m : Mem) (no nl lo hi e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) noSch.cs + 2 = 0 then none else noClrK (noGoW n (mclearG noSch m) no nl lo hi CWF e)

theorem noConstW_eq (n : Nat) (m : Mem) (no nl lo hi e : Word) (h0 : rdW (m.arr64 CTL) noSch.cs + 2 ≠ 0) :
    noConstW n m no nl lo hi e = noClrK (noGoW n (mclearG noSch m) no nl lo hi CWF e) := by simp [noConstW, h0]
theorem noClrK_some (r : Word) (m1 : Mem) (h0 : rdW (m1.arr64 CTL) noSch.cs + 2 ≠ 0) :
    noClrK (some (r, m1)) = some (r, mclearG noSch m1) := by simp [noClrK, h0]
attribute [ind_grind] noConstW_eq noClrK_some

theorem nestOcc_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hc : p.lookup "sl_contains" = some slContains)
    (hf : p.lookup "no_find" = some (memoFindG noSch)) (hput : p.lookup "no_put" = some (memoPutG noSch))
    (hgo : p.lookup "nest_occ_go" = some nestOccGo)
    (hnode : p.lookup "nest_occ_node" = some nestOccNode)
    (hcl : p.lookup "no_clear" = some (memoClearG noSch))
    (hp : p.lookup "nest_occ" = some nestOcc) (n : Nat) (s₀ : St) (no nl lo hi e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_occ" [no, nl, lo, hi, e]
    ⦃fun r s' => LocEq s' s₀ ∧ noConstW n s₀.mem no nl lo hi e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (noGo_spec p hv hc hf hput hgo hnode n).1
  unfold NoGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, nestOcc]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec noSch p _ hcl n, ih] <;>
    finish


theorem noConstW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl lo hi e r : Word) (ws : List Word) (mp0 : Std.HashMap EIdx Bool)
    (hb : noConstW n m no nl lo hi e = some (r, m')) (hS : StageR dn vis fe m a) (hh : H e)
    (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hM : noMR m mp0) :
    ∃ b, (ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat (decE e)).run a =
        .ok (b, a) ∧ (r != 0) = b ∧ noMR m' ∅ ∧ StageR dn vis fe m' a ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) noSch.cs + 2 = 0
  · simp [noConstW, h0] at hb
  rw [noConstW_eq n m no nl lo hi e h0] at hb
  have hf0 := mclearG_frame noSch m
  have hM0 := memoRG_clear noSch noSch_wf bmKey (fun w : Word => w != 0) m mp0 hM h0
  have hA0 : ArenaR (mclearG noSch m) a :=
    ArenaR.frame (A := []) (C := [noSch.cs, noSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by simp [noSch] at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.1.arena.1
  have hws0 : SlR (mclearG noSch m) no nl ws := slR_congr (hf0.1 IW (by simp) (by decide)) hws
  cases hg : noGoW n (mclearG noSch m) no nl lo hi CWF e with
  | none => rw [hg] at hb; simp [noClrK] at hb
  | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [hg] at hb
    by_cases h1 : rdW (m1.arr64 CTL) noSch.cs + 2 = 0
    · simp [noClrK, h1] at hb
    rw [noClrK_some r1 m1 h1] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨c, mp1, hrun, hbb, hM1, hfr1⟩ := noGoOK n _ _ a no nl lo hi CWF e r1 ws ∅ hg hA0 hh hws0 hwlt hM0
    rw [CWF_eq] at hrun
    have hM2 := memoRG_clear noSch noSch_wf bmKey (fun w : Word => w != 0) m1 mp1 hM1 h1
    have hf2 := mclearG_frame noSch m1
    have hfall : MemFrame [NOM] [noSch.cs, noSch.cs + 1] m (mclearG noSch m1) :=
      ((hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp [noSch]))).trans
        (hf2.mono (by simp) (by simp))
    obtain ⟨hS', hg'⟩ := StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
      (by intro x hx; simp [noSch] at hx; rcases hx with rfl | rfl <;> decide) (by decide)
      (by simp [noSch])
    refine ⟨c, ?_, hbb, hM2, hS', hg'⟩
    simp only [ConRon.Arena.nestOcc, StateT.run_bind]
    rw [hrun]
    rfl


section census3
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hc : p.lookup "sl_contains" = some slContains)
  (hf : p.lookup "no_find" = some (memoFindG noSch)) (hput : p.lookup "no_put" = some (memoPutG noSch))
  (hgo : p.lookup "nest_occ_go" = some nestOccGo)
  (hnode : p.lookup "nest_occ_node" = some nestOccNode)
  (hcl : p.lookup "no_clear" = some (memoClearG noSch))
  (hp : p.lookup "nest_occ" = some nestOcc)
include hv hc hf hput hgo hnode hcl hp

/-- **`nest_occ` refines `nestOcc`**: one memoised DAG walk between two clears;
the per-call memo is any well-formed one on entry (`mp0`) and empty after. -/
@[refines ConRon.Arena.nestOcc]
theorem nestOcc_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lo hi e : Word) (ws : List Word) (mp0 : Std.HashMap EIdx Bool) (hh : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hM : noMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_occ" [no, nl, lo, hi, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat (decE e)) a₀ ∧
      AM.st (ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat (decE e)) a₀ = a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.nestOcc (ws.map (fun w => (decI w : NIdx))) lo.toNat hi.toNat (decE e)) a₀ ∧
      noMR s'.mem ∅ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (nestOcc_spec p hv hc hf hput hgo hnode hcl hp n s₀ no nl lo hi e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨b, hrun, hb, hM', hS', hg⟩ := noConstW_ok n dn fe vis _ _ a₀ no nl lo hi e _ ws mp0 hm hS hh hws hwlt hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hb, hM', hS', hg⟩

end census3

/-! ## `member_idx_at` -/

def memK (n : Nat) (m : Mem) (no nl lvls : Word) (v : List Word) : Option (List Word × Mem) :=
  if v = [] then none
  else if v.tail.tail.headD 0 ≠ lvls then some ([0, 0], m)
  else match findW n m no nl (v.tail.headD 0) with
    | none => none
    | some r => some ([r.headD 0, r.tail.headD 0], m)

def memW (n : Nat) (m : Mem) (no nl lvls e : Word) : Option (List Word × Mem) :=
  if e >>> 28 ≠ 3 then some ([0, 0], m) else memK n m no nl lvls (eViewW m e)

theorem memW_not (n : Nat) (m : Mem) (no nl lvls e : Word) (h : e >>> 28 ≠ 3) :
    memW n m no nl lvls e = some ([0, 0], m) := by simp [memW, h]
theorem memW_const (n : Nat) (m : Mem) (no nl lvls e : Word) (h : ¬ e >>> 28 ≠ 3) :
    memW n m no nl lvls e = memK n m no nl lvls (eViewW m e) := by simp only [memW]; rw [if_neg h]
theorem memK_abort (n : Nat) (m : Mem) (no nl lvls : Word) (v : List Word) (h : v = []) :
    memK n m no nl lvls v = none := by simp [memK, h]
theorem memK_miss (n : Nat) (m : Mem) (no nl lvls : Word) (v : List Word) (h : v ≠ [])
    (h2 : v.tail.tail.headD 0 ≠ lvls) : memK n m no nl lvls v = some ([0, 0], m) := by
  simp only [memK]; rw [if_neg h, if_pos h2]
theorem memK_find (n : Nat) (m : Mem) (no nl lvls : Word) (v : List Word) (h : v ≠ [])
    (h2 : ¬ v.tail.tail.headD 0 ≠ lvls) : memK n m no nl lvls v =
      (match findW n m no nl (v.tail.headD 0) with
        | none => none
        | some r => some ([r.headD 0, r.tail.headD 0], m)) := by
  simp only [memK]; rw [if_neg h, if_neg h2]
attribute [ind_grind] memW_not memW_const memK_abort memK_miss memK_find

theorem memberIdxAt_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hf : p.lookup "sl_find" = some slFind) (hp : p.lookup "member_idx_at" = some memberIdxAt)
    (n : Nat) (s₀ : St) (no nl lvls e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "member_idx_at" [no, nl, lvls, e]
    ⦃fun r s' => LocEq s' s₀ ∧ memW n s₀.mem no nl lvls e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memberIdxAt]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, eView_spec p hv n,
      slFind_spec p hf n] <;> finish (gen := 20)


/-- `(ok, idx)` against an `Option Nat`. -/
def MemIdxOut (r : List Word) : Option Nat → Prop
  | none => r = [0, 0]
  | some i => r = [1, UInt64.ofNat i]

theorem memW_ok (n : Nat) (m m' : Mem) (a : AState) (no nl lvls e : Word) (r : List Word)
    (ws : List Word) (hA : ArenaR m a) (he : H e)
    (hlv : H lvls) (hws : SlR m no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hlen : ws.length < 2 ^ 64) (h : memW n m no nl lvls e = some (r, m')) :
    m' = m ∧ ∃ o, (ConRon.Arena.memberIdxAt? (ws.map (fun w => (decI w : NIdx))) (decI lvls)
      (decI e)).run a = .ok (o, a) ∧ MemIdxOut r o := by
  have htag := tag_const_iff e he
  by_cases hd : e >>> 28 ≠ 3
  · rw [memW_not n m no nl lvls e hd] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, none, ?_, rfl⟩
    have : ¬ ((decI e : EIdx).tag == ETag.const) = true := by rw [htag]; simpa using hd
    simp only [ConRon.Arena.memberIdxAt?, this, if_false]; rfl
  · rw [memW_const n m no nl lvls e hd] at h
    have he3 : e >>> 28 = 3 := by simpa using hd
    cases hvl : eViewW m e with
    | nil => rw [hvl] at h; simp [memK] at h
    | cons g vt =>
      have hne : eViewW m e ≠ [] := by rw [hvl]; simp
      obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA e hne
      rw [hvl] at hvr h
      have ht : (decE e).tag = ETag.const := by
        have h1 : ((decI e : EIdx).tag == ETag.const) = true := by rw [htag, he3]; decide
        exact beq_iff_eq.mp h1
      obtain ⟨nn, us0, rfl⟩ := EStore.view_const a.store (decE e) ht v hv
      simp only [ViewR, getD1_eq', getD2_eq] at hvr
      obtain ⟨-, hx, hdx, hy, hdy⟩ := hvr
      have hview : a.store.viewConst (decE e) = some (nn, us0) :=
        EStore.viewConst_of_view _ _ ht nn us0 hv
      have hbeq : (us0 == decI lvls) = decide ((g :: vt).tail.tail.headD 0 = lvls) := by
        rw [← hdy]; exact decI_beq' _ _ hy hlv
      by_cases hl : (g :: vt).tail.tail.headD 0 ≠ lvls
      · rw [memK_miss n m no nl lvls _ (by simp) hl] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, none, ?_, rfl⟩
        have : ¬ (us0 == decI lvls) = true := by rw [hbeq]; simpa using hl
        have htg : ((decI e : EIdx).tag == ETag.const) = true := by rw [htag, he3]; decide
        simp only [ConRon.Arena.memberIdxAt?, htg, if_true, StateT.run_bind]
        rw [show (decI e : EIdx) = decE e from rfl, viewConst_run, except_ok_bind, hview]
        simp only [this, if_false]; rfl
      · rw [memK_find n m no nl lvls _ (by simp) hl] at h
        cases hfw : findW n m no nl ((g :: vt).tail.headD 0) with
        | none => rw [hfw] at h; simp at h
        | some fr =>
          rw [hfw] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hfr := findW_ok n _ _ _ _ _ _ hws hfw hlen
          have hl' : (g :: vt).tail.tail.headD 0 = lvls := by simpa using hl
          have htg : ((decI e : EIdx).tag == ETag.const) = true := by rw [htag, he3]; decide
          have hfi := findIdx_decI ws ((g :: vt).tail.headD 0) hwlt hx
          refine ⟨rfl, (ws.map (fun w => (decI w : NIdx))).findIdx? (· == nn), ?_, ?_⟩
          · simp only [ConRon.Arena.memberIdxAt?, htg, if_true, StateT.run_bind]
            rw [show (decI e : EIdx) = decE e from rfl, viewConst_run, except_ok_bind, hview]
            have : (us0 == decI lvls) = true := by rw [hbeq]; simpa using hl'
            simp only [this, if_true]; rfl
          · rw [← hdx, hfi, hfr]
            cases hwi : ws.findIdx? (· == (g :: vt).tail.headD 0) <;> simp [MemIdxOut]

section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hf : p.lookup "sl_find" = some slFind)
  (hp : p.lookup "member_idx_at" = some memberIdxAt)
include hv hf hp

/-- **`member_idx_at` refines `memberIdxAt?`**. -/
@[refines ConRon.Arena.memberIdxAt?]
theorem memberIdxAt_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lvls e : Word) (ws : List Word) (he : H e) (hlv : H lvls)
    (hS : StageR dn vis fe s₀.mem a₀) (hws : SlR s₀.mem no nl ws) (hwlt : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hlen : ws.length < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "member_idx_at" [no, nl, lvls, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.memberIdxAt? (ws.map (fun w => (decI w : NIdx))) (decI lvls) (decI e)) a₀ ∧
      AM.st (ConRon.Arena.memberIdxAt? (ws.map (fun w => (decI w : NIdx))) (decI lvls) (decI e)) a₀ = a₀ ∧
      MemIdxOut r
        (AM.res (ConRon.Arena.memberIdxAt? (ws.map (fun w => (decI w : NIdx))) (decI lvls) (decI e)) a₀) ∧
      s'.mem = s₀.mem; ⊤⦄ := by
  refine triple_post (memberIdxAt_spec p hv hf hp n s₀ no nl lvls e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨hmem, o, hrun, hout⟩ := memW_ok n _ _ a₀ no nl lvls e r ws hS.1.arena.1 he hlv hws hwlt hlen hm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hout, hmem⟩

end census

/-! ## `ph_app` -/

theorem ETables.get_app (t : ETables) (i : EIdx) (ht : i.tag = ETag.app) (v : ENodeView)
    (h : t.get i = some v) : ∃ f x, v = .app f x := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app] at h
  cases hn : t.apps.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_app (st : EStore) (i : EIdx) (ht : i.tag = ETag.app) (v : ENodeView)
    (h : st.view i = some v) : ∃ f x, v = .app f x := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_app _ _ ht v h
  · split at h
    · exact ETables.get_app _ _ ht v h
    · simp at h

theorem ETables.get_fvar (t : ETables) (i : EIdx) (ht : i.tag = ETag.fvar) (v : ENodeView)
    (h : t.get i = some v) : ∃ k ty, v = .fvar k ty := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar] at h
  cases hn : t.fvars.node? i.idxNat with
  | none => simp [hn] at h
  | some x => simp [hn] at h; exact ⟨_, _, h.symm⟩

theorem EStore.view_fvar (st : EStore) (i : EIdx) (ht : i.tag = ETag.fvar) (v : ENodeView)
    (h : st.view i = some v) : ∃ k ty, v = .fvar k ty := by
  unfold EStore.view at h
  split at h
  · exact ETables.get_fvar _ _ ht v h
  · split at h
    · exact ETables.get_fvar _ _ ht v h
    · simp at h

theorem ETables.getApp_of_get (t : ETables) (i : EIdx) (ht : i.tag = ETag.app) (f x : EIdx)
    (h : t.get i = some (.app f x)) : t.getApp i = some (f, x) := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app] at h
  simp only [ETables.getApp]
  cases hn : t.apps.node? i.idxNat with
  | none => simp [hn] at h
  | some y => simp [hn] at h ⊢; exact h

theorem EStore.viewApp_of_view (st : EStore) (i : EIdx) (ht : i.tag = ETag.app) (f x : EIdx)
    (h : st.view i = some (.app f x)) : st.viewApp i = some (f, x) := by
  unfold EStore.view at h
  unfold EStore.viewApp EStore.persGetApp
  split at h
  · rename_i hp; rw [if_pos hp]; exact ETables.getApp_of_get _ _ ht f x h
  · rename_i hp; rw [if_neg hp]
    split at h
    · rename_i hs; rw [if_pos hs]; exact ETables.getApp_of_get _ _ ht f x h
    · simp at h

theorem viewApp_run' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewApp h).run a = .ok (a.store.viewApp h, a) := rfl


theorem ETables.getFVarIdx_of_get' (t : ETables) (i : EIdx) (ht : i.tag = ETag.fvar) (k : Nat) (ty : EIdx)
    (h : t.get i = some (.fvar k ty)) : t.getFVarIdx i = some k := by
  simp only [ETables.get, ht, ETag.bvar, ETag.fvar] at h
  simp only [ETables.getFVarIdx]
  cases hn : t.fvars.node? i.idxNat with
  | none => simp [hn] at h
  | some y => simp [hn] at h ⊢; exact h.1

theorem EStore.viewFVarIdx_of_view' (st : EStore) (i : EIdx) (ht : i.tag = ETag.fvar) (k : Nat) (ty : EIdx)
    (h : st.view i = some (.fvar k ty)) : st.viewFVarIdx i = some k := by
  unfold EStore.view at h
  unfold EStore.viewFVarIdx EStore.persGetFVarIdx
  split at h
  · rename_i hp; rw [if_pos hp]; exact ETables.getFVarIdx_of_get' _ _ ht k ty h
  · rename_i hp; rw [if_neg hp]
    split at h
    · rename_i hs; rw [if_pos hs]; exact ETables.getFVarIdx_of_get' _ _ ht k ty h
    · simp at h

theorem viewFVarIdx_run'' (h : EIdx) (a : AState) :
    (ConRon.Arena.viewFVarIdx h).run a = .ok (a.store.viewFVarIdx h, a) := rfl


mutual
def phW : Nat → Mem → Word → Word → Word → Option (List Word)
  | 0, _, _, _, _ => none
  | k + 1, m, b, e, n =>
    if n = 0 then
      (if e >>> 28 ≠ 3 then some [0, 0, 0] else phK0 (eViewW m e))
    else if e >>> 28 ≠ 4 then some [0, 0, 0]
    else phK1 k m b n (eViewW m e)
def phK0 (v : List Word) : Option (List Word) :=
  if v = [] then none else some [1, v.tail.headD 0, v.tail.tail.headD 0]
def phK1 (k : Nat) (m : Mem) (b n : Word) (v : List Word) : Option (List Word) :=
  if v = [] then none
  else if v.tail.tail.headD 0 >>> 28 ≠ 1 then some [0, 0, 0]
  else phK2 k m b n (v.tail.headD 0) (eViewW m (v.tail.tail.headD 0))
def phK2 (k : Nat) (m : Mem) (b n x : Word) (w : List Word) : Option (List Word) :=
  if w = [] then none
  else if w.tail.headD 0 ≠ b + (n - 1) then some [0, 0, 0]
  else phK3 (phW k m b x (n - 1))
def phK3 : Option (List Word) → Option (List Word)
  | none => none
  | some r => some [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0]
end

section arms
variable (k : Nat) (m : Mem) (b e n x : Word) (v w r : List Word)
theorem phW_n0_miss (h0 : n = 0) (h : e >>> 28 ≠ 3) : phW (k + 1) m b e n = some [0, 0, 0] := by
  simp [phW, h0, h]
theorem phW_n0 (h0 : n = 0) (h : ¬ e >>> 28 ≠ 3) : phW (k + 1) m b e n = phK0 (eViewW m e) := by
  simp only [phW]; rw [if_pos h0, if_neg h]
theorem phW_miss (h0 : n ≠ 0) (h : e >>> 28 ≠ 4) : phW (k + 1) m b e n = some [0, 0, 0] := by
  simp only [phW]; rw [if_neg h0, if_pos h]
theorem phW_app (h0 : n ≠ 0) (h : ¬ e >>> 28 ≠ 4) : phW (k + 1) m b e n = phK1 k m b n (eViewW m e) := by
  simp only [phW]; rw [if_neg h0, if_neg h]
theorem phK0_abort (h : v = []) : phK0 v = none := by simp [phK0, h]
theorem phK0_ok (h : v ≠ []) : phK0 v = some [1, v.tail.headD 0, v.tail.tail.headD 0] := by
  simp only [phK0]; rw [if_neg h]
theorem phK1_abort (h : v = []) : phK1 k m b n v = none := by simp [phK1, h]
theorem phK1_miss (h : v ≠ []) (h2 : v.tail.tail.headD 0 >>> 28 ≠ 1) : phK1 k m b n v = some [0, 0, 0] := by
  simp only [phK1]; rw [if_neg h, if_pos h2]
theorem phK1_ok (h : v ≠ []) (h2 : ¬ v.tail.tail.headD 0 >>> 28 ≠ 1) :
    phK1 k m b n v = phK2 k m b n (v.tail.headD 0) (eViewW m (v.tail.tail.headD 0)) := by
  simp only [phK1]; rw [if_neg h, if_neg h2]
theorem phK2_abort (h : w = []) : phK2 k m b n x w = none := by simp [phK2, h]
theorem phK2_miss (h : w ≠ []) (h2 : w.tail.headD 0 ≠ b + (n - 1)) : phK2 k m b n x w = some [0, 0, 0] := by
  simp only [phK2]; rw [if_neg h, if_pos h2]
theorem phK2_ok (h : w ≠ []) (h2 : ¬ w.tail.headD 0 ≠ b + (n - 1)) :
    phK2 k m b n x w = phK3 (phW k m b x (n - 1)) := by
  simp only [phK2]; rw [if_neg h, if_neg h2]
theorem phK3_some : phK3 (some r) = some [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0] := by rw [phK3]
end arms
attribute [ind_grind] phW_n0_miss phW_n0 phW_miss phW_app phK0_abort phK0_ok phK1_abort phK1_miss phK1_ok
  phK2_abort phK2_miss phK2_ok phK3_some

theorem phApp_spec (p : Prog) (hv : p.lookup "e_view" = some eView)
    (hp : p.lookup "ph_app" = some phApp) (k : Nat) :
    ∀ (s₀ : St) (b e n : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "ph_app" [b, e, n]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ phW k s₀.mem b e n = some r; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ b e n
    rw [invoke_eq _ hp]; simp only [callFn, phApp]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ b e n
    rw [invoke_eq _ hp]
    simp only [callFn, phApp]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, eView_spec p hv k, ih] <;>
      finish (gen := 20) [St.setLocs_mem']


theorem tag_app_iff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.app) = decide (w >>> 28 = 4) := by
  have := decE_tag_eq w hw 4 (by decide)
  have e1 : (ETag.app : UInt32) = UInt32.ofNat 4 := rfl
  show ((decE w).tag == ETag.app) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

theorem tag_fvar_iff (w : Word) (hw : w.toNat < 2 ^ 32) :
    ((decI w : EIdx).tag == ETag.fvar) = decide (w >>> 28 = 1) := by
  have := decE_tag_eq w hw 1 (by decide)
  have e1 : (ETag.fvar : UInt32) = UInt32.ofNat 1 := rfl
  show ((decE w).tag == ETag.fvar) = _
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e1, this]
  exact Iff.rfl

def PhOut (r : List Word) : Option (NIdx × LsIdx) → Prop
  | none => r.headD 0 = 0
  | some (c, us) => ∃ w1 w2, r = [1, w1, w2] ∧ w1.toNat < 2 ^ 32 ∧ decI w1 = c ∧
      w2.toNat < 2 ^ 32 ∧ decI w2 = us

theorem phW_ok (k : Nat) : ∀ (m : Mem) (a : AState) (b e n : Word) (N : Nat) (r : List Word),
    n.toNat = N → phW k m b e n = some r → ArenaR m a → H e → b.toNat + N < 2 ^ 64 →
    ∃ o, (ConRon.Arena.phApp? b.toNat (decI e) N).run a = .ok (o, a) ∧ PhOut r o := by
  induction k with
  | zero => intro m a b e n N r _ h; simp [phW] at h
  | succ k ih =>
    intro m a b e n N r hN h hA he hb
    by_cases hn0 : n = 0
    · have hN0 : N = 0 := by rw [← hN, hn0]; rfl
      subst hN0
      by_cases hd : e >>> 28 ≠ 3
      · rw [phW_n0_miss k m b e n hn0 hd] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨none, ?_, rfl⟩
        have : ¬ ((decI e : EIdx).tag == ETag.const) = true := by rw [tag_const_iff e he]; simpa using hd
        simp only [ConRon.Arena.phApp?, this, if_false]; rfl
      · rw [phW_n0 k m b e n hn0 hd] at h
        have he3 : e >>> 28 = 3 := by simpa using hd
        cases hvl : eViewW m e with
        | nil => rw [hvl] at h; simp [phK0] at h
        | cons g vt =>
          have hne : eViewW m e ≠ [] := by rw [hvl]; simp
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA e hne
          rw [hvl] at hvr h
          rw [phK0_ok _ (by simp)] at h
          simp only [Option.some.injEq] at h
          subst h
          have ht : (decE e).tag = ETag.const := by
            have h1 : ((decI e : EIdx).tag == ETag.const) = true := by rw [tag_const_iff e he, he3]; decide
            exact beq_iff_eq.mp h1
          obtain ⟨nn, us0, rfl⟩ := EStore.view_const a.store (decE e) ht v hv
          simp only [ViewR, getD1_eq', getD2_eq] at hvr
          obtain ⟨-, hx, hdx, hy, hdy⟩ := hvr
          have hview : a.store.viewConst (decE e) = some (nn, us0) :=
            EStore.viewConst_of_view _ _ ht nn us0 hv
          have htg : ((decI e : EIdx).tag == ETag.const) = true := by rw [tag_const_iff e he, he3]; decide
          refine ⟨some (nn, us0), ?_, ?_⟩
          · simp only [ConRon.Arena.phApp?, htg, if_true, StateT.run_bind]
            rw [show (decI e : EIdx) = decE e from rfl, viewConst_run, except_ok_bind, hview]
            rfl
          · exact ⟨_, _, rfl, hx, hdx, hy, hdy⟩
    · obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by have := toNat_ne_zero' hn0; omega⟩
      by_cases hd : e >>> 28 ≠ 4
      · rw [phW_miss k m b e n hn0 hd] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨none, ?_, rfl⟩
        have : ¬ ((decI e : EIdx).tag == ETag.app) = true := by rw [tag_app_iff e he]; simpa using hd
        simp only [ConRon.Arena.phApp?, this, if_false]; rfl
      · rw [phW_app k m b e n hn0 hd] at h
        have he4 : e >>> 28 = 4 := by simpa using hd
        cases hvl : eViewW m e with
        | nil => rw [hvl] at h; simp [phK1] at h
        | cons g vt =>
          have hne : eViewW m e ≠ [] := by rw [hvl]; simp
          obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hA e hne
          rw [hvl] at hvr h
          have ht : (decE e).tag = ETag.app := by
            have h1 : ((decI e : EIdx).tag == ETag.app) = true := by rw [tag_app_iff e he, he4]; decide
            exact beq_iff_eq.mp h1
          obtain ⟨f', a', rfl⟩ := EStore.view_app a.store (decE e) ht v hv
          simp only [ViewR, getD1_eq', getD2_eq] at hvr
          obtain ⟨-, hx, hdx, hy, hdy⟩ := hvr
          have hview : a.store.viewApp (decE e) = some (f', a') :=
            EStore.viewApp_of_view _ _ ht f' a' hv
          have htg : ((decI e : EIdx).tag == ETag.app) = true := by rw [tag_app_iff e he, he4]; decide
          by_cases hy1 : (g :: vt).tail.tail.headD 0 >>> 28 ≠ 1
          · rw [phK1_miss k m b n _ (by simp) hy1] at h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨none, ?_, rfl⟩
            have : ¬ (a'.tag == ETag.fvar) = true := by
              rw [← hdy]
              show ¬ ((decI ((g :: vt).tail.tail.headD 0) : EIdx).tag == ETag.fvar) = true
              rw [tag_fvar_iff _ hy]; simpa using hy1
            simp only [ConRon.Arena.phApp?, htg, if_true, StateT.run_bind]
            rw [show (decI e : EIdx) = decE e from rfl, viewApp_run', except_ok_bind, hview]
            simp only [this, if_false]; rfl
          · rw [phK1_ok k m b n _ (by simp) hy1] at h
            have hy1' : (g :: vt).tail.tail.headD 0 >>> 28 = 1 := by simpa using hy1
            cases hvl2 : eViewW m ((g :: vt).tail.tail.headD 0) with
            | nil => rw [hvl2] at h; simp [phK2] at h
            | cons g2 vt2 =>
              have hne2 : eViewW m ((g :: vt).tail.tail.headD 0) ≠ [] := by rw [hvl2]; simp
              obtain ⟨v2, hv2, hvr2⟩ := eViewW_ok m a hA _ hne2
              rw [hvl2] at hvr2 h
              have hyd : decE ((g :: vt).tail.tail.headD 0) = a' := hdy
              rw [hyd] at hv2
              have ht2 : a'.tag = ETag.fvar := by
                have h1 : ((decI ((g :: vt).tail.tail.headD 0) : EIdx).tag == ETag.fvar) = true := by
                  rw [tag_fvar_iff _ hy, hy1']; decide
                rw [← hyd]; exact beq_iff_eq.mp h1
              obtain ⟨j, ty, rfl⟩ := EStore.view_fvar a.store a' ht2 v2 hv2
              simp only [ViewR, getD1_eq'] at hvr2
              obtain ⟨-, hj, -⟩ := hvr2
              have hfi : a.store.viewFVarIdx a' = some j := EStore.viewFVarIdx_of_view' _ _ ht2 j ty hv2
              have hnn : (n - 1).toNat = N' := by rw [toNat_sub_one' hn0, hN]; rfl
              have hbn : (b + (n - 1)).toNat = b.toNat + N' := by
                rw [UInt64.toNat_add, hnn]; exact Nat.mod_eq_of_lt (by omega)
              by_cases hm : (g2 :: vt2).tail.headD 0 ≠ b + (n - 1)
              · rw [phK2_miss k m b n _ _ (by simp) hm] at h
                simp only [Option.some.injEq] at h
                subst h
                refine ⟨none, ?_, rfl⟩
                have htfv : (a'.tag == ETag.fvar) = true := by
                  rw [← hyd]
                  show ((decI ((g :: vt).tail.tail.headD 0) : EIdx).tag == ETag.fvar) = true
                  rw [tag_fvar_iff _ hy, hy1']; decide
                have hjne : ¬ (j == b.toNat + N') = true := by
                  intro hc
                  have : j = b.toNat + N' := beq_iff_eq.mp hc
                  apply hm
                  apply UInt64.toNat_inj.mp
                  rw [hbn, ← this, ← hj]
                simp only [ConRon.Arena.phApp?, htg, if_true, StateT.run_bind]
                rw [show (decI e : EIdx) = decE e from rfl, viewApp_run', except_ok_bind, hview]
                simp only [htfv, if_true, StateT.run_bind]
                rw [viewFVarIdx_run'', except_ok_bind, hfi]
                simp only [hjne, if_false]; rfl
              · rw [phK2_ok k m b n _ _ (by simp) hm] at h
                cases hrec : phW k m b ((g :: vt).tail.headD 0) (n - 1) with
                | none => rw [hrec] at h; simp [phK3] at h
                | some r' =>
                  rw [hrec, phK3_some] at h
                  simp only [Option.some.injEq] at h
                  obtain ⟨o, hro, hpo⟩ := ih m a b _ (n - 1) N' r' hnn hrec hA hx (by omega)
                  subst h
                  have hm' : (g2 :: vt2).tail.headD 0 = b + (n - 1) := by simpa using hm
                  have hjeq : j = b.toNat + N' := by rw [← hbn, ← hm', ← hj]
                  have htfv : (a'.tag == ETag.fvar) = true := by
                    rw [← hyd]
                    show ((decI ((g :: vt).tail.tail.headD 0) : EIdx).tag == ETag.fvar) = true
                    rw [tag_fvar_iff _ hy, hy1']; decide
                  refine ⟨o, ?_, ?_⟩
                  · simp only [ConRon.Arena.phApp?, htg, if_true, StateT.run_bind]
                    rw [show (decI e : EIdx) = decE e from rfl, viewApp_run', except_ok_bind, hview]
                    simp only [htfv, if_true, StateT.run_bind]
                    rw [viewFVarIdx_run'', except_ok_bind, hfi]
                    have : (j == b.toNat + N') = true := by rw [hjeq]; simp
                    simp only [this, if_true]
                    rw [← hdx]
                    exact hro
                  · cases o with
                    | none => simpa [PhOut] using hpo
                    | some pr =>
                      obtain ⟨c, us⟩ := pr
                      obtain ⟨w1, w2, hr, h1, h2, h3, h4⟩ := hpo
                      subst hr
                      exact ⟨w1, w2, rfl, h1, h2, h3, h4⟩


section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hp : p.lookup "ph_app" = some phApp)
include hv hp

/-- **`ph_app` refines `phApp?`**: the constant applied to exactly the placeholders. -/
@[refines ConRon.Arena.phApp?]
theorem phApp_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis b e n : Word) (N : Nat) (hN : n.toNat = N) (he : H e)
    (hb : b.toNat + N < 2 ^ 64) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "ph_app" [b, e, n]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      AM.ok (ConRon.Arena.phApp? b.toNat (decI e) N) a₀ ∧
      AM.st (ConRon.Arena.phApp? b.toNat (decI e) N) a₀ = a₀ ∧
      PhOut r (AM.res (ConRon.Arena.phApp? b.toNat (decI e) N) a₀); ⊤⦄ := by
  refine triple_post (phApp_spec p hv hp k s₀ b e n) ?_
  rintro r s' ⟨hl, hmem, hm⟩
  obtain ⟨o, hrun, hout⟩ := phW_ok k _ a₀ b e n N r hN hm hS.1.arena.1 he hb
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hmem, hok, hst, by rw [hres]; exact hout⟩

end census

/-! ## `app_hole` -/

def ahC : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => some ([r.headD 0, r.tail.headD 0], m1)

def ahK (n : Nat) (m : Mem) (no nl us nn : Word) : Option (List Word) → Option (List Word × Mem)
  | none => none
  | some r => if r.headD 0 = 0 then some ([0, 0], m)
      else ahC (canonW n m no nl us nn (r.tail.headD 0) (r.tail.tail.headD 0))

def ahW (n : Nat) (m : Mem) (no nl us b nn e : Word) : Option (List Word × Mem) :=
  ahK n m no nl us nn (phW n m b e nn)

section arms
variable (n : Nat) (m : Mem) (no nl us nn : Word) (r : List Word)
theorem ahK_none (h : r.headD 0 = 0) : ahK n m no nl us nn (some r) = some ([0, 0], m) := by
  simp only [ahK]; rw [if_pos h]
theorem ahK_some (h : ¬ r.headD 0 = 0) :
    ahK n m no nl us nn (some r) = ahC (canonW n m no nl us nn (r.tail.headD 0) (r.tail.tail.headD 0)) := by
  simp only [ahK]; rw [if_neg h]
theorem ahC_some (r : List Word) (m1 : Mem) : ahC (some (r, m1)) = some ([r.headD 0, r.tail.headD 0], m1) := rfl
end arms
attribute [ind_grind] ahK_none ahK_some ahC_some

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hph : p.lookup "ph_app" = some phApp)
  (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hcs : p.lookup "nest_canon_sub" = some nestCanonSub)
  (hp : p.lookup "app_hole" = some appHole)
include hv hph hf hpw hsf hsp his hff hfp hif hcs hp

theorem appHole_spec (n : Nat) (s₀ : St) (no nl us b nn e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "app_hole" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧ ahW n s₀.mem no nl us b nn e = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, appHole]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      phApp_spec p hv hph n, nestCanonSub_spec p hf hpw hsf hsp his hff hfp hif hcs n] <;>
    finish (gen := 40) [St.setLocs_mem', ahW]

end spec


theorem ahW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us b nn e : Word) (N : Nat) (names : List NIdx) (r : List Word)
    (hh : ahW n m no nl us b nn e = some (r, m')) (hS : StageR dn vis fe m a) (hN : nn.toNat = N)
    (he : H e) (hus : H us) (hb : b.toNat + N < 2 ^ 64)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hnn : nn.toNat + names.length < 2 ^ 64) :
    ∃ x a', (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOE m' r x := by
  unfold ahW at hh
  cases hph : phW n m b e nn with
  | none => rw [hph] at hh; simp [ahK] at hh
  | some r0 =>
    rw [hph] at hh
    obtain ⟨o, hrun, hpo⟩ := phW_ok n m a b e nn N r0 hN hph hS.1.arena.1 he hb
    by_cases hz : r0.headD 0 = 0
    · rw [ahK_none n m no nl us nn r0 hz] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
      cases o with
      | none =>
        simp only [ConRon.Arena.appHole?, StateT.run_bind]
        rw [hrun]; rfl
      | some pr =>
        obtain ⟨c, us0⟩ := pr
        obtain ⟨w1, w2, hr0, -⟩ := hpo
        rw [hr0] at hz; simp at hz
    · rw [ahK_some n m no nl us nn r0 hz] at hh
      cases o with
      | none => exact absurd hpo hz
      | some pr =>
        obtain ⟨c, us0⟩ := pr
        obtain ⟨w1, w2, hr0, hw1, hd1, hw2, hd2⟩ := hpo
        subst hr0
        cases hcw : canonW n m no nl us nn w1 w2 with
        | none =>
          simp only [List.tail_cons, List.headD_cons] at hh
          rw [hcw] at hh; simp [ahC] at hh
        | some pc =>
          obtain ⟨rc, m1⟩ := pc
          simp only [List.tail_cons, List.headD_cons] at hh
          rw [hcw, ahC_some] at hh
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          obtain ⟨x, a', hrun', hS', hg, hout⟩ := canonW_ok n dn fe vis m m1 a no nl us nn w1 w2 names rc hcw hS
            hw1 hus hw2 hdec hno hnn
          refine ⟨x, a', ?_, hS', hg, ?_⟩
          · simp only [ConRon.Arena.appHole?, StateT.run_bind]
            rw [hrun]
            simp only [except_ok_bind]
            rw [hN, hd1, hd2] at hrun'
            exact hrun'
          · cases x with
            | none => simpa [decOE] using hout
            | some e3 =>
              simp only [decOE, decW0E] at hout ⊢
              obtain ⟨h1, h2, h3⟩ := hout
              exact ⟨h1, by simpa using h2, by simpa using h3⟩


section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView) (hph : p.lookup "ph_app" = some phApp)
  (hf : p.lookup "sl_find" = some slFind) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hcs : p.lookup "nest_canon_sub" = some nestCanonSub)
  (hp : p.lookup "app_hole" = some appHole)
include hv hph hf hpw hsf hsp his hff hfp hif hcs hp

/-- **`app_hole` refines `appHole?`**. -/
@[refines ConRon.Arena.appHole?]
theorem appHole_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn e : Word) (N : Nat) (names : List NIdx) (hN : nn.toNat = N)
    (he : H e) (hus : H us) (hb : b.toNat + N < 2 ^ 64) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hnn : nn.toNat + names.length < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "app_hole" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.appHole? names (decI us) b.toNat N (decI e)) a₀); ⊤⦄ := by
  refine triple_post (appHole_spec p hv hph hf hpw hsf hsp his hff hfp hif hcs hp n s₀ no nl us b nn e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := ahW_ok n dn fe vis _ _ a₀ no nl us b nn e N names r hm hS hN he hus hb
    hdec hno hnn
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

end L.Ind
