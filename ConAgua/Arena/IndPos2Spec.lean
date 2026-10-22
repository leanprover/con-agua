import ConAgua.Arena.IndPos2
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.Env
import ConAgua.Arena.IndPosSpec
import ConAgua.Arena.IndMaster
import ConAgua.Arena.IndPartsSpec3
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


theorem findIdx_decIP (ws : List Word) (c : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
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
      have hfi := findIdx_decIP ws c hwlt hc
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
          have hfi := findIdx_decIP ws ((g :: vt).tail.headD 0) hwlt hx
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

/-! ## Low frames: writers of the store tiers (arrays and `CTL` words below 64) -/

def LowFr (m m' : Mem) : Prop :=
  ∃ (A : List ArrId) (C : List Word), MemFrame A C m m' ∧ (∀ b ∈ A, b < 64) ∧ (∀ x ∈ C, x.toNat < 64)

theorem LowFr.refl (m : Mem) : LowFr m m := ⟨[], [], MemFrame.refl _ _ _, by simp, by simp⟩

theorem LowFr.trans {m₁ m₂ m₃ : Mem} (h₁ : LowFr m₁ m₂) (h₂ : LowFr m₂ m₃) : LowFr m₁ m₃ := by
  obtain ⟨A₁, C₁, f₁, a₁, c₁⟩ := h₁
  obtain ⟨A₂, C₂, f₂, a₂, c₂⟩ := h₂
  refine ⟨A₁ ++ A₂, C₁ ++ C₂, (f₁.mono (fun b hb => List.mem_append_left _ hb) (fun x hx => List.mem_append_left _ hx)).trans
    (f₂.mono (fun b hb => List.mem_append_right _ hb) (fun x hx => List.mem_append_right _ hx)), ?_, ?_⟩
  · intro b hb; rcases List.mem_append.mp hb with h | h; exact a₁ b h; exact a₂ b h
  · intro x hx; rcases List.mem_append.mp hx with h | h; exact c₁ x h; exact c₂ x h

theorem sointernW_low {m m' : Mem} {u r : Word} (h : sointernW m u = some (r, m')) : LowFr m m' := by
  have h₂ := h; rw [sointernW_eq] at h₂
  exact ⟨_, _, internM_frame _ sortSch_wf _ _ _ _ _ _ _ _ h₂, by simp [sortSch, SOREC, SOSLOT], by simp [sortSch]⟩

theorem fvinternW_low {m m' : Mem} {u ty r : Word} (h : fvinternW m u ty = some (r, m')) : LowFr m m' := by
  have h₂ := h; rw [fvinternW_eq] at h₂
  exact ⟨_, _, internM_frame _ fvarSch_wf _ _ _ _ _ _ _ _ h₂, by simp [fvarSch, FVREC, FVSLOT], by simp [fvarSch]⟩

theorem mkAppW_low {m m' : Mem} {f x r : Word} (hI : mkAppW m f x = some (r, m')) : LowFr m m' := by
  have hf : MemFrame [ADER, AREC, ASLOT] [4, 5] m m' := by
    unfold mkAppW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [ainternW_eq] at hx; exact internM_frame _ appSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact ⟨_, _, hf, by simp [ADER, AREC, ASLOT], by simp⟩

theorem mkLamW_low {m m' : Mem} {t b r : Word} (hI : mkLamW m t b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame [LADER, LAREC, LASLOT] [28, 29] m m' := by
    unfold mkLamW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [lainternW_eq] at hx; exact internM_frame _ lamSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact ⟨_, _, hf, by simp [LADER, LAREC, LASLOT], by simp⟩

theorem mkForallW_low {m m' : Mem} {t b r : Word} (hI : mkForallW m t b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame [FADER, FAREC, FASLOT] [30, 31] m m' := by
    unfold mkForallW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [fainternW_eq] at hx; exact internM_frame _ forallSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact ⟨_, _, hf, by simp [FADER, FAREC, FASLOT], by simp⟩

theorem mkLetW_low {m m' : Mem} {t v b r : Word} (hI : mkLetW m t v b = some (r, m')) : LowFr m m' := by
  have hf : MemFrame [LEDER, LEREC, LESLOT] [20, 21] m m' := by
    unfold mkLetW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [leinternW_eq] at hx; exact internM_frame _ letSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact ⟨_, _, hf, by simp [LEDER, LEREC, LESLOT], by simp⟩


theorem mkProjW_low {m m' : Mem} {n i e r : Word} (hI : mkProjW m n i e = some (r, m')) : LowFr m m' := by
  have hf : MemFrame [PJDER, PJREC, PJSLOT] [32, 33] m m' := by
    unfold mkProjW at hI; split at hI; · cases hI
    exact mkK_frame (by decide) (fun r₁ m₁ hx => by
      rw [pjinternW_eq] at hx; exact internM_frame _ projSch_wf _ _ _ _ _ _ _ _ hx) hI
  exact ⟨_, _, hf, by simp [PJDER, PJREC, PJSLOT], by simp⟩

theorem canonW_low (n : Nat) {m m' : Mem} {no nl us nn c v : Word} {r : List Word}
    (h : canonW n m no nl us nn c v = some (r, m')) : LowFr m m' := by
  cases n with
  | zero => simp [canonW] at h
  | succ n =>
  by_cases hvu : v ≠ us
  · rw [canonW_ne n m no nl us nn c v hvu] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact LowFr.refl _
  · rw [canonW_eq n m no nl us nn c v hvu] at h
    cases hfw : findW n m no nl c with
    | none => rw [hfw] at h; simp [canonK0] at h
    | some fr =>
      rw [hfw] at h
      by_cases hz : fr.headD 0 = 0
      · rw [canonK0_miss _ _ _ hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact LowFr.refl _
      · rw [canonK0_hit _ _ _ hz] at h
        cases hpw : pinWordV m 53 with
        | none => rw [hpw] at h; simp [canonK1] at h
        | some z =>
          rw [hpw] at h
          by_cases hzb : 4294967296 ≤ z
          · rw [canonK1_big _ _ _ _ hzb] at h; simp at h
          rw [canonK1_ok _ _ _ _ hzb] at h
          cases hso : sointernW m z with
          | none => rw [hso] at h; simp [canonK2] at h
          | some p1 =>
            obtain ⟨s1, m1⟩ := p1
            rw [hso] at h
            by_cases hsb : 4294967296 ≤ s1
            · rw [canonK2_big _ _ _ _ hsb] at h; simp at h
            rw [canonK2_ok _ _ _ _ hsb] at h
            cases hfv : fvinternW m1 (nn + (fr.tail.headD 0)) s1 with
            | none => rw [hfv] at h; simp [canonK3] at h
            | some p2 =>
              obtain ⟨rr, m2⟩ := p2
              rw [hfv] at h
              by_cases hrb : 4294967296 ≤ rr
              · rw [canonK3_big _ _ hrb] at h; simp at h
              rw [canonK3_ok _ _ hrb] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact (sointernW_low hso).trans (fvinternW_low hfv)


/-! ## `replace_apps_go` / `replace_apps_node` -/

structure MkLook (p : Prog) : Prop where
  hd : p.lookup "der_b" = some derB
  appF : p.lookup "app_find" = some appFind
  appP : p.lookup "app_push" = some appPush
  appI : p.lookup "intern_app" = some internApp
  appM : p.lookup "mk_app" = some mkApp
  lamF : p.lookup "lam_find" = some lamFind
  lamP : p.lookup "lam_push" = some lamPush
  lamI : p.lookup "intern_lam" = some internLamL
  lamM : p.lookup "mk_lam" = some mkLam
  forF : p.lookup "forall_find" = some forallFind
  forP : p.lookup "forall_push" = some forallPush
  forI : p.lookup "intern_forall" = some internForallL
  forM : p.lookup "mk_forall" = some mkForall
  ltF : p.lookup "letE_find" = some letFind
  ltP : p.lookup "letE_push" = some letPush
  ltI : p.lookup "intern_letE" = some internLet
  ltM : p.lookup "mk_let" = some mkLet
  prjF : p.lookup "proj_find" = some projFind
  prjP : p.lookup "proj_push" = some projPush
  prjI : p.lookup "intern_proj" = some internProj
  prjM : p.lookup "mk_proj" = some mkProj

structure AhLook (p : Prog) : Prop where
  hv : p.lookup "e_view" = some eView
  hph : p.lookup "ph_app" = some phApp
  hf : p.lookup "sl_find" = some slFind
  hpw : p.lookup "pin_word" = some pinWordL
  hsf : p.lookup "sort_find" = some sortFind
  hsp : p.lookup "sort_push" = some sortPush
  his : p.lookup "intern_sort" = some internSort
  hff : p.lookup "fvar_find" = some fvarFind
  hfp : p.lookup "fvar_push" = some fvarPush
  hif : p.lookup "intern_fvar" = some internFVar
  hcs : p.lookup "nest_canon_sub" = some nestCanonSub
  hp : p.lookup "app_hole" = some appHole

/-- `app_hole` at any exec fuel. -/
def ahWf : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, us, b, nn, e => ahW k m no nl us b nn e

theorem appHole_spec' (p : Prog) (hl : AhLook p) (k : Nat) (s₀ : St) (no nl us b nn e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "app_hole" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧ ahWf k s₀.mem no nl us b nn e = some (r, s'.mem); ⊤⦄ := by
  cases k with
  | zero =>
    rw [invoke_eq _ hl.hp]; simp only [callFn, appHole]; vcgen [exec] <;> grind
  | succ n => exact appHole_spec p hl.hv hl.hph hl.hf hl.hpw hl.hsf hl.hsp hl.his hl.hff hl.hfp hl.hif hl.hcs hl.hp n s₀ no nl us b nn e

def rpMkW (m : Mem) (g a2 x2 c2 y : Word) (x : Word) : Option (Word × Mem) :=
  if g = 4 then mkAppW m a2 x2
  else if g = 5 then mkLamW m a2 x2
  else if g = 6 then mkForallW m a2 x2
  else if g = 7 then mkLetW m a2 x2 c2
  else mkProjW m x y a2

mutual
def rpGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, us, b, nn, f, h =>
    if f = 0 then none else rpG1 n m no nl us b nn f h (eViewW m h)
def rpG1 (n : Nat) (m : Mem) (no nl us b nn f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8 then some (h, m)
  else if v.headD 0 = 3 then rpH h (ahWf n m no nl us b nn h)
  else rpG3 n m no nl us b nn f h v (mfindG raSch m h 0)
def rpH (h : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rr, m1) => some ((if rr.headD 0 ≠ 0 then rr.tail.headD 0 else h), m1)
def rpG3 (n : Nat) (m : Mem) (no nl us b nn f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 RAM) (fr.tail.headD 0 * 4 + 3), m)
  else rpG4 h (rpNodeW n m no nl us b nn (f - 1) h (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def rpG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => rpG5 r (msetG raSch m1 h 0 r)
def rpG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def rpNodeW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, us, b, nn, f1, h, g, x, y, z =>
    if g = 4 then rpA1 n m no nl us b nn f1 h x y (ahWf n m no nl us b nn h)
    else if g = 5 ∨ g = 6 then rpB1 n no nl us b nn f1 g x y (rpGoW n m no nl us b nn f1 x)
    else if g = 7 then rpL1 n no nl us b nn f1 x y z (rpGoW n m no nl us b nn f1 x)
    else rpP1 n m no nl us b nn f1 x y z (rpGoW n m no nl us b nn f1 z)
def rpA1 (n : Nat) (m : Mem) (no nl us b nn f1 h x y : Word) :
    Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rr, m1) =>
    if rr.headD 0 ≠ 0 then some (rr.tail.headD 0, m1)
    else rpB1 n no nl us b nn f1 4 x y (rpGoW n m1 no nl us b nn f1 x)
def rpB1 (n : Nat) (no nl us b nn f1 g x y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rpB2 g a2 x (rpGoW n m1 no nl us b nn f1 y)
def rpB2 (g a2 x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x2, m2) => rpMkW m2 g a2 x2 0 0 0
def rpL1 (n : Nat) (no nl us b nn f1 x y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rpL2 n no nl us b nn f1 z a2 (rpGoW n m1 no nl us b nn f1 y)
def rpL2 (n : Nat) (no nl us b nn f1 z a2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x2, m2) => rpL3 a2 x2 (rpGoW n m2 no nl us b nn f1 z)
def rpL3 (a2 x2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (c2, m3) => rpMkW m3 7 a2 x2 c2 0 0
def rpP1 (n : Nat) (m : Mem) (no nl us b nn f1 x y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (a2, m1) => rpMkW m1 9 a2 0 0 y x
end


section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (no nl us b nn f f1 h g x y z a2 x2 c2 r : Word) (v fr rr : List Word)
theorem rpGoW_abort (hf : f = 0) : rpGoW (n + 1) m no nl us b nn f h = none := by simp [rpGoW, hf]
theorem rpGoW_view (hf : f ≠ 0) :
    rpGoW (n + 1) m no nl us b nn f h = rpG1 n m no nl us b nn f h (eViewW m h) := by simp [rpGoW, hf]
theorem rpG1_abort (hv : v = []) : rpG1 n m no nl us b nn f h v = none := by simp [rpG1, hv]
theorem rpG1_leaf (hv : v ≠ []) (hg : v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8) :
    rpG1 n m no nl us b nn f h v = some (h, m) := by simp only [rpG1]; rw [if_neg hv, if_pos hg]
theorem rpG1_const (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : v.headD 0 = 3) : rpG1 n m no nl us b nn f h v = rpH h (ahWf n m no nl us b nn h) := by
  simp only [rpG1]; rw [if_neg hv, if_neg hg, if_pos h3]
theorem rpG1_node (hv : v ≠ []) (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8))
    (h3 : ¬ v.headD 0 = 3) :
    rpG1 n m no nl us b nn f h v = rpG3 n m no nl us b nn f h v (mfindG raSch m h 0) := by
  simp only [rpG1]; rw [if_neg hv, if_neg hg, if_neg h3]
theorem rpH_some : rpH h (some (rr, m1)) = some ((if rr.headD 0 ≠ 0 then rr.tail.headD 0 else h), m1) := by rw [rpH]
theorem rpG3_abort (hr : fr = []) : rpG3 n m no nl us b nn f h v fr = none := by simp [rpG3, hr]
theorem rpG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    rpG3 n m no nl us b nn f h v fr = some (rdW (m.arr64 RAM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [rpG3]; rw [if_neg hr, if_pos hh]
theorem rpG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    rpG3 n m no nl us b nn f h v fr = rpG4 h (rpNodeW n m no nl us b nn (f - 1) h (v.headD 0)
      (v.tail.headD 0) (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [rpG3]; rw [if_neg hr, if_neg hh]
theorem rpG4_some : rpG4 h (some (r, m1)) = rpG5 r (msetG raSch m1 h 0 r) := by rw [rpG4]
theorem rpG5_some : rpG5 r (some m2) = some (r, m2) := by rw [rpG5]
theorem rpNodeW_app : rpNodeW (n + 1) m no nl us b nn f1 h 4 x y z =
    rpA1 n m no nl us b nn f1 h x y (ahWf n m no nl us b nn h) := by simp [rpNodeW]
theorem rpNodeW_bin (hg : g = 5 ∨ g = 6) : rpNodeW (n + 1) m no nl us b nn f1 h g x y z =
    rpB1 n no nl us b nn f1 g x y (rpGoW n m no nl us b nn f1 x) := by
  have : ¬ g = 4 := by intro e; rcases hg with e' | e' <;> (rw [e] at e'; exact absurd e' (by decide))
  simp only [rpNodeW]; rw [if_neg this, if_pos hg]
theorem rpNodeW_let : rpNodeW (n + 1) m no nl us b nn f1 h 7 x y z =
    rpL1 n no nl us b nn f1 x y z (rpGoW n m no nl us b nn f1 x) := by simp [rpNodeW]
theorem rpNodeW_proj (hg4 : ¬ g = 4) (hg5 : ¬ (g = 5 ∨ g = 6)) (hg7 : ¬ g = 7) :
    rpNodeW (n + 1) m no nl us b nn f1 h g x y z =
    rpP1 n m no nl us b nn f1 x y z (rpGoW n m no nl us b nn f1 z) := by
  simp only [rpNodeW]; rw [if_neg hg4, if_neg hg5, if_neg hg7]
theorem rpA1_hit (hh : rr.headD 0 ≠ 0) : rpA1 n m no nl us b nn f1 h x y (some (rr, m1)) =
    some (rr.tail.headD 0, m1) := by simp only [rpA1]; rw [if_pos hh]
theorem rpA1_miss (hh : ¬ rr.headD 0 ≠ 0) : rpA1 n m no nl us b nn f1 h x y (some (rr, m1)) =
    rpB1 n no nl us b nn f1 4 x y (rpGoW n m1 no nl us b nn f1 x) := by simp only [rpA1]; rw [if_neg hh]
theorem rpB1_some : rpB1 n no nl us b nn f1 g x y (some (a2, m1)) =
    rpB2 g a2 x (rpGoW n m1 no nl us b nn f1 y) := by rw [rpB1]
theorem rpB2_some : rpB2 g a2 x (some (x2, m2)) = rpMkW m2 g a2 x2 0 0 0 := by rw [rpB2]
theorem rpL1_some : rpL1 n no nl us b nn f1 x y z (some (a2, m1)) =
    rpL2 n no nl us b nn f1 z a2 (rpGoW n m1 no nl us b nn f1 y) := by rw [rpL1]
theorem rpL2_some : rpL2 n no nl us b nn f1 z a2 (some (x2, m2)) =
    rpL3 a2 x2 (rpGoW n m2 no nl us b nn f1 z) := by rw [rpL2]
theorem rpL3_some : rpL3 a2 x2 (some (c2, m3)) = rpMkW m3 7 a2 x2 c2 0 0 := by rw [rpL3]
theorem rpP1_some : rpP1 n m no nl us b nn f1 x y z (some (a2, m1)) = rpMkW m1 9 a2 0 0 y x := by rw [rpP1]
theorem rpMkW_app : rpMkW m 4 a2 x2 c2 y x = mkAppW m a2 x2 := by simp [rpMkW]
theorem rpMkW_lam : rpMkW m 5 a2 x2 c2 y x = mkLamW m a2 x2 := by simp [rpMkW]
theorem rpMkW_forall : rpMkW m 6 a2 x2 c2 y x = mkForallW m a2 x2 := by simp [rpMkW]
theorem rpMkW_let : rpMkW m 7 a2 x2 c2 y x = mkLetW m a2 x2 c2 := by simp [rpMkW]
theorem rpMkW_proj : rpMkW m 9 a2 x2 c2 y x = mkProjW m x y a2 := by simp [rpMkW]
end arms
attribute [ind_grind] rpGoW_abort rpGoW_view rpG1_abort rpG1_leaf rpG1_const rpG1_node rpH_some rpG3_abort
  rpG3_hit rpG3_miss rpG4_some rpG5_some rpNodeW_app rpNodeW_bin rpNodeW_let rpNodeW_proj rpA1_hit
  rpA1_miss rpB1_some rpB2_some rpL1_some rpL2_some rpL3_some rpP1_some rpMkW_app rpMkW_lam rpMkW_forall
  rpMkW_let rpMkW_proj


section spec
variable (p : Prog) (hl : AhLook p) (hk : MkLook p)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)

def RpGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl us b nn f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_apps_go" [no, nl, us, b, nn, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ rpGoW n s₀.mem no nl us b nn f h = some (r.headD 0, s'.mem); ⊤⦄

def RpNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (no nl us b nn f1 h g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_apps_node" [no, nl, us, b, nn, f1, h, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ rpNodeW n s₀.mem no nl us b nn f1 h g x y z = some (r.headD 0, s'.mem); ⊤⦄

include hl hf hput hgo in
theorem rpGo_step (n : Nat) (ih : RpNodeSpec p n) : RpGoSpec p (n + 1) := by
  unfold RpNodeSpec at ih
  intro s₀ no nl us b nn f h
  rw [invoke_eq _ hgo]
  simp only [callFn, replaceAppsGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hl.hv n, appHole_spec' p hl n, memoFindG_spec raSch p _ hf n,
      memoPutG_spec raSch p _ hput n, ih] <;> finish (gen := 20) [St.setLocs_mem']

include hl hk hgo hnode in
theorem rpNode_step (n : Nat) (ih : RpGoSpec p n) : RpNodeSpec p (n + 1) := by
  unfold RpGoSpec at ih
  intro s₀ no nl us b nn f1 h g x y z
  rw [invoke_eq _ hnode]
  simp only [callFn, replaceAppsNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      appHole_spec' p hl n, ih,
      mkApp_spec p hk.hd hk.appF hk.appP hk.appI hk.appM n,
      mkLam_spec p hk.hd hk.lamF hk.lamP hk.lamI hk.lamM n,
      mkForall_spec p hk.hd hk.forF hk.forP hk.forI hk.forM n,
      mkLet_spec p hk.hd hk.ltF hk.ltP hk.ltI hk.ltM n,
      mkProj_spec p hk.hd hk.prjF hk.prjP hk.prjI hk.prjM n] <;> finish (gen := 20) [St.setLocs_mem']

include hl hk hf hput hgo hnode in
theorem rpGo_spec (n : Nat) : RpGoSpec p n ∧ RpNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ no nl us b nn f h; rw [invoke_eq _ hgo]; simp only [callFn, replaceAppsGo]; vcgen [exec] <;> grind
    · intro s₀ no nl us b nn f1 h g x y z; rw [invoke_eq _ hnode]; simp only [callFn, replaceAppsNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨rpGo_step p hl hf hput hgo n ih.2, rpNode_step p hl hk hgo hnode n ih.1⟩

end spec


def rpClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if rdW (m1.arr64 CTL) raSch.cs + 2 = 0 then none else some (r, mclearG raSch m1)

def rpConstW (n : Nat) (m : Mem) (no nl us b nn e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) raSch.cs + 2 = 0 then none
  else rpClrK (rpGoW n (mclearG raSch m) no nl us b nn CWF e)

theorem rpConstW_eq (n : Nat) (m : Mem) (no nl us b nn e : Word) (h0 : rdW (m.arr64 CTL) raSch.cs + 2 ≠ 0) :
    rpConstW n m no nl us b nn e = rpClrK (rpGoW n (mclearG raSch m) no nl us b nn CWF e) := by
  simp [rpConstW, h0]
theorem rpClrK_some (r : Word) (m1 : Mem) (h0 : rdW (m1.arr64 CTL) raSch.cs + 2 ≠ 0) :
    rpClrK (some (r, m1)) = some (r, mclearG raSch m1) := by simp [rpClrK, h0]
attribute [ind_grind] rpConstW_eq rpClrK_some

theorem replaceApps_spec (p : Prog) (hl : AhLook p) (hk : MkLook p)
    (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
    (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
    (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
    (hcl : p.lookup "ra_clear" = some (memoClearG raSch))
    (hp : p.lookup "replace_apps" = some replaceApps) (n : Nat) (s₀ : St) (no nl us b nn e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_apps" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧ rpConstW n s₀.mem no nl us b nn e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (rpGo_spec p hl hk hf hput hgo hnode n).1
  unfold RpGoSpec at ih
  rw [invoke_eq _ hp]
  simp only [callFn, replaceApps]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec raSch p _ hcl n, ih] <;>
    finish


/-! ### The relational side -/

def rpArm (names : List NIdx) (us : LsIdx) (b n : Nat) (memo : Std.HashMap EIdx EIdx) (fuel : Nat)
    (h : EIdx) : ENodeView → AM (EIdx × Std.HashMap EIdx EIdx)
  | .app a x => do
    match ← ConRon.Arena.appHole? names us b n h with
    | some r => pure (r, memo)
    | none => do
      let (a2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel a
      let (x2, m2) ← ConRon.Arena.replaceAppsGo names us b n m fuel x
      let r ← internAppE a2 x2
      pure (r, m2)
  | .lam t body => do
    let (t2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel t
    let (b2, m2) ← ConRon.Arena.replaceAppsGo names us b n m fuel body
    let r ← internLamE t2 b2
    pure (r, m2)
  | .forallE t body => do
    let (t2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel t
    let (b2, m2) ← ConRon.Arena.replaceAppsGo names us b n m fuel body
    let r ← internForallEE t2 b2
    pure (r, m2)
  | .letE t val body => do
    let (t2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel t
    let (v2, m2) ← ConRon.Arena.replaceAppsGo names us b n m fuel val
    let (b2, m3) ← ConRon.Arena.replaceAppsGo names us b n m2 fuel body
    let r ← internLetEE t2 v2 b2
    pure (r, m3)
  | .proj s i x => do
    let (x2, m) ← ConRon.Arena.replaceAppsGo names us b n memo fuel x
    let r ← internProjE s i x2
    pure (r, m)
  | _ => pure (h, memo)

def NodeVr : ENodeView → Prop
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem replaceAppsGo_succ' (names : List NIdx) (us : LsIdx) (b n : Nat) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) :
    ConRon.Arena.replaceAppsGo names us b n memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (h, memo)
      | .sort _ => pure (h, memo)
      | .lit _ => pure (h, memo)
      | .fvar _ _ => pure (h, memo)
      | .const _ _ =>
        match ← ConRon.Arena.appHole? names us b n h with
        | some r => pure (r, memo)
        | none => pure (h, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← rpArm names us b n memo fuel h v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.replaceAppsGo.eq_2]
  congr 1
  funext v
  cases v with
  | app a' x' =>
    simp only [rpArm, bind_assoc, pure_bind]
    cases hm : memo[h]? with
    | some r => rfl
    | none =>
      refine congrArg (ConRon.Arena.appHole? names us b n h >>= ·) (funext fun x => ?_)
      cases x <;> simp [bind_assoc]
  | lam t body => simp only [rpArm, bind_assoc, pure_bind]; rfl
  | forallE t body => simp only [rpArm, bind_assoc, pure_bind]; rfl
  | letE t v' body => simp only [rpArm, bind_assoc, pure_bind]; rfl
  | proj s i x => simp only [rpArm, bind_assoc, pure_bind]; rfl
  | bvar _ => rfl
  | sort _ => rfl
  | lit _ => rfl
  | fvar _ _ => rfl
  | const _ _ => rfl


theorem raSch_wf : raSch.WF := ⟨by decide, by decide⟩

abbrev rpMR (m : Mem) (mp : Std.HashMap EIdx EIdx) : Prop :=
  MemoRG raSch bmKey (fun w : Word => decE w) m mp

theorem rpMR_low {m m' : Mem} (hf : LowFr m m') {mp : Std.HashMap EIdx EIdx} (h : rpMR m mp) :
    rpMR m' mp := by
  obtain ⟨A, C, hf, hA, hC⟩ := hf
  exact memoRG_frame raSch raSch_wf bmKey (fun w : Word => decE w) A C
    (fun hmem => by have := hA _ hmem; simp [raSch, RAM] at this)
    (fun hmem => by have := hC _ hmem; simp [raSch] at this) m m' hf mp h

theorem ahW_low {n : Nat} {m m' : Mem} {no nl us b nn e : Word} {r : List Word}
    (h : ahW n m no nl us b nn e = some (r, m')) : LowFr m m' := by
  unfold ahW at h
  cases hph : phW n m b e nn with
  | none => rw [hph] at h; simp [ahK] at h
  | some r0 =>
    rw [hph] at h
    by_cases hz : r0.headD 0 = 0
    · rw [ahK_none n m no nl us nn r0 hz] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact LowFr.refl _
    · rw [ahK_some n m no nl us nn r0 hz] at h
      cases hc : canonW n m no nl us nn (r0.tail.headD 0) (r0.tail.tail.headD 0) with
      | none => rw [hc] at h; simp [ahC] at h
      | some pc =>
        obtain ⟨rc, m1⟩ := pc
        rw [hc, ahC_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact canonW_low n hc

def RpGoOK (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (no nl us b nn f h r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx),
    rpGoW n m no nl us b nn f h = some (r, m') → StageR dn vis fe m a → H h → H us →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat < 2 ^ 64 →
    no.toNat + nl.toNat ≤ iwTop m → nn.toNat = N → nn.toNat + names.length < 2 ^ 64 →
    b.toNat + N < 2 ^ 64 → rpMR m mp →
    ∃ a' mp', (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)).run a =
        .ok ((decE r, mp'), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp'

/-- Two children and an interning: the shared shape of `lam` and `forallE`. -/
theorem rpBin_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k) (g : Word)
    (mkW : Mem → Word → Word → Option (Word × Mem)) (iop : EIdx → EIdx → AM EIdx)
    (hmk : ∀ m a2 x2, rpMkW m g a2 x2 0 0 0 = mkW m a2 x2)
    (hst : ∀ (m m' : Mem) (a : AState) (u v r : Word), StageR dn vis fe m a → mkW m u v = some (r, m') →
      ∃ a', (iop (decE u) (decE v)).run a = .ok (decE r, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m')
    (hlow : ∀ (m m' : Mem) (u v r : Word), mkW m u v = some (r, m') → LowFr m m')
    (m m' : Mem) (a : AState) (no nl us b nn f1 x y r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpB1 k no nl us b nn f1 g x y (rpGoW k m no nl us b nn f1 x) = some (r, m'))
    (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (do
        let (t2, mm) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f1.toNat (decE x)
        let (b2, m2) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mm f1.toNat (decE y)
        let r ← iop t2 b2
        pure (r, m2) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  cases h1 : rpGoW k m no nl us b nn f1 x with
  | none => rw [h1] at hn; simp [rpB1] at hn
  | some p1 =>
    obtain ⟨a2, m1⟩ := p1
    rw [h1, rpB1_some] at hn
    cases h2 : rpGoW k m1 no nl us b nn f1 y with
    | none => rw [h2] at hn; simp [rpB2] at hn
    | some p2 =>
      obtain ⟨x2, m2⟩ := p2
      rw [h2, rpB2_some, hmk] at hn
      obtain ⟨a1, mp1, hr1, hS1, hg1, hM1⟩ := ih m m1 a no nl us b nn f1 x a2 N names mp h1 hS hx hus hdec hno hit hN hnn hb hM
      have hdec1 : decHL m1 no.toNat nl.toNat = some names := by rw [decHL_grow hg1 hit]; exact hdec
      obtain ⟨a2', mp2, hr2, hS2, hg2, hM2⟩ := ih m1 m2 a1 no nl us b nn f1 y x2 N names mp1 h2 hS1 hy hus hdec1 hno
        (by have := hg1.1; omega) hN hnn hb hM1
      obtain ⟨a3, hr3, hS3, hg3⟩ := hst m2 m' a2' a2 x2 r hS2 hn
      refine ⟨a3, mp2, ?_, hS3, (hg1.trans hg2).trans hg3, rpMR_low (hlow m2 m' a2 x2 r hn) hM2⟩
      simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind, StateT.run_bind]
      rw [hr2]
      simp only [except_ok_bind, StateT.run_bind]
      rw [hr3]
      rfl


theorem rpLet_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k)
    (m m' : Mem) (a : AState) (no nl us b nn f1 x y z r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpL1 k no nl us b nn f1 x y z (rpGoW k m no nl us b nn f1 x) = some (r, m'))
    (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hz : H z) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (do
        let (t2, mm) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f1.toNat (decE x)
        let (v2, m2) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mm f1.toNat (decE y)
        let (b2, m3) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N m2 f1.toNat (decE z)
        let r ← internLetEE t2 v2 b2
        pure (r, m3) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  cases h1 : rpGoW k m no nl us b nn f1 x with
  | none => rw [h1] at hn; simp [rpL1] at hn
  | some p1 =>
    obtain ⟨a2, m1⟩ := p1
    rw [h1, rpL1_some] at hn
    cases h2 : rpGoW k m1 no nl us b nn f1 y with
    | none => rw [h2] at hn; simp [rpL2] at hn
    | some p2 =>
      obtain ⟨x2, m2⟩ := p2
      rw [h2, rpL2_some] at hn
      cases h3 : rpGoW k m2 no nl us b nn f1 z with
      | none => rw [h3] at hn; simp [rpL3] at hn
      | some p3 =>
        obtain ⟨c2, m3⟩ := p3
        rw [h3, rpL3_some, rpMkW_let] at hn
        obtain ⟨a1, mp1, hr1, hS1, hg1, hM1⟩ := ih m m1 a no nl us b nn f1 x a2 N names mp h1 hS hx hus hdec hno hit hN hnn hb hM
        have hdec1 : decHL m1 no.toNat nl.toNat = some names := by rw [decHL_grow hg1 hit]; exact hdec
        obtain ⟨a2', mp2, hr2, hS2, hg2, hM2⟩ := ih m1 m2 a1 no nl us b nn f1 y x2 N names mp1 h2 hS1 hy hus hdec1 hno
          (by have := hg1.1; omega) hN hnn hb hM1
        have hg12 := hg1.trans hg2
        have hdec2 : decHL m2 no.toNat nl.toNat = some names := by rw [decHL_grow hg12 hit]; exact hdec
        obtain ⟨a3', mp3, hr3, hS3, hg3, hM3⟩ := ih m2 m3 a2' no nl us b nn f1 z c2 N names mp2 h3 hS2 hz hus hdec2 hno
          (by have := hg12.1; omega) hN hnn hb hM2
        obtain ⟨a4, hr4, hS4, hg4⟩ := mkLet_stage hS3 a2 x2 c2 hn
        refine ⟨a4, mp3, ?_, hS4, (hg12.trans hg3).trans hg4, rpMR_low (mkLetW_low hn) hM3⟩
        simp only [StateT.run_bind]
        rw [hr1]
        simp only [except_ok_bind, StateT.run_bind]
        rw [hr2]
        simp only [except_ok_bind, StateT.run_bind]
        rw [hr3]
        simp only [except_ok_bind, StateT.run_bind]
        have hr4' : (internLetEE (decE a2) (decE x2) (decE c2)).run a3' = .ok (decE r, a4) := hr4
        rw [hr4']
        rfl

theorem rpProj_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k)
    (m m' : Mem) (a : AState) (no nl us b nn f1 x y z r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpP1 k m no nl us b nn f1 x y z (rpGoW k m no nl us b nn f1 z) = some (r, m'))
    (hS : StageR dn vis fe m a) (hz : H z) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (do
        let (x2, mm) ← ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f1.toNat (decE z)
        let r ← internProjE (decI x) y.toNat x2
        pure (r, mm) : AM (EIdx × Std.HashMap EIdx EIdx)).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  cases h1 : rpGoW k m no nl us b nn f1 z with
  | none => rw [h1] at hn; simp [rpP1] at hn
  | some p1 =>
    obtain ⟨a2, m1⟩ := p1
    rw [h1, rpP1_some, rpMkW_proj] at hn
    obtain ⟨a1, mp1, hr1, hS1, hg1, hM1⟩ := ih m m1 a no nl us b nn f1 z a2 N names mp h1 hS hz hus hdec hno hit hN hnn hb hM
    obtain ⟨a3, hr3, hS3, hg3⟩ := mkProj_stage hS1 x y a2 hn
    refine ⟨a3, mp1, ?_, hS3, hg1.trans hg3, rpMR_low (mkProjW_low hn) hM1⟩
    simp only [StateT.run_bind]
    rw [hr1]
    simp only [except_ok_bind, StateT.run_bind]
    have hr3' : (internProjE (decI x) y.toNat (decE a2)).run a1 = .ok (decE r, a3) := hr3
    rw [hr3']
    rfl


theorem rpApp_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k)
    (m m' : Mem) (a : AState) (no nl us b nn f1 h x y r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpA1 k m no nl us b nn f1 h x y (ahWf k m no nl us b nn h) = some (r, m'))
    (hS : StageR dn vis fe m a) (hh : H h) (hx : H x) (hy : H y) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (rpArm names (decI us) b.toNat N mp f1.toNat (decE h) (.app (decE x) (decE y))).run a =
        .ok ((decE r, mp'), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  cases k with
  | zero => simp [ahWf, rpA1] at hn
  | succ j =>
    cases hah : ahW j m no nl us b nn h with
    | none => simp only [ahWf] at hn; rw [hah] at hn; simp [rpA1] at hn
    | some pr =>
      obtain ⟨rr, m1⟩ := pr
      simp only [ahWf] at hn
      rw [hah] at hn
      obtain ⟨xo, a1, hrun1, hS1, hg1, hout⟩ := ahW_ok j dn fe vis m m1 a no nl us b nn h N names rr hah hS hN hh hus hb
        hdec hno hnn
      rw [show (decI h : EIdx) = decE h from rfl] at hrun1
      by_cases hh0 : rr.headD 0 ≠ 0
      · rw [rpA1_hit _ _ _ _ _ _ _ _ _ _ _ _ _ hh0] at hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        cases xo with
        | none => exact absurd hout hh0
        | some e' =>
          simp only [decOE, decW0E] at hout
          obtain ⟨-, -, hd⟩ := hout
          refine ⟨a1, mp, ?_, hS1, hg1, rpMR_low (ahW_low hah) hM⟩
          simp only [rpArm, StateT.run_bind]
          rw [hrun1]
          simp only [except_ok_bind]
          rw [show decE (rr.tail.headD 0) = e' from hd]
          rfl
      · rw [rpA1_miss _ _ _ _ _ _ _ _ _ _ _ _ _ hh0] at hn
        have hz : rr.headD 0 = 0 := by simpa using hh0
        have hxo : xo = none := by
          cases xo with
          | none => rfl
          | some e' => simp only [decOE] at hout; rw [hout.1] at hz; simp at hz
        subst hxo
        have hdec1 : decHL m1 no.toNat nl.toNat = some names := by rw [decHL_grow hg1 hit]; exact hdec
        obtain ⟨a', mp', hr, hS', hg', hM'⟩ := rpBin_ok dn fe vis (j + 1) ih 4 (fun m a b => mkAppW m a b) internAppE
          (fun m a2 x2 => by simp [rpMkW])
          (fun m m' a u v r hS hI => mkApp_stage hS u v hI) (fun m m' u v r hI => mkAppW_low hI)
          m1 m' a1 no nl us b nn f1 x y r N names mp hn hS1 hx hy hus hdec1 hno
          (by have := hg1.1; omega) hN hnn hb (rpMR_low (ahW_low hah) hM)
        refine ⟨a', mp', ?_, hS', hg1.trans hg', hM'⟩
        simp only [rpArm, StateT.run_bind]
        rw [hrun1]
        simp only [except_ok_bind]
        exact hr


theorem rpNode_arm (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (k : Nat)
    (ih : RpGoOK dn fe vis k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v) (hnv : NodeVr v)
    (m m' : Mem) (a : AState) (no nl us b nn f1 h r : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx)
    (hn : rpNodeW (k + 1) m no nl us b nn f1 h (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hS : StageR dn vis fe m a) (hh : H h) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hb : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (rpArm names (decI us) b.toNat N mp f1.toNat (decE h) v).run a = .ok ((decE r, mp'), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  cases v with
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rpNodeW_app] at hn
    have := rpApp_ok dn fe vis k ih m m' a no nl us b nn f1 h _ _ r N names mp hn hS hh hx hy hus hdec hno hit hN hnn hb hM
    rw [hdx, hdy] at this
    exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rpNodeW_bin k m no nl us b nn f1 h 5 _ _ _ (Or.inl rfl)] at hn
    obtain ⟨a', mp', hr, hS', hg', hM'⟩ := rpBin_ok dn fe vis k ih 5 (fun m a b => mkLamW m a b) internLamE
      (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkLam_stage hS u v hI) (fun m m' u v r hI => mkLamW_low hI)
      m m' a no nl us b nn f1 _ _ r N names mp hn hS hx hy hus hdec hno hit hN hnn hb hM
    rw [hdx, hdy] at hr
    exact ⟨a', mp', hr, hS', hg', hM'⟩
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    rw [hg, rpNodeW_bin k m no nl us b nn f1 h 6 _ _ _ (Or.inr rfl)] at hn
    obtain ⟨a', mp', hr, hS', hg', hM'⟩ := rpBin_ok dn fe vis k ih 6 (fun m a b => mkForallW m a b) internForallEE
      (fun m a2 x2 => by simp [rpMkW])
      (fun m m' a u v r hS hI => mkForall_stage hS u v hI) (fun m m' u v r hI => mkForallW_low hI)
      m m' a no nl us b nn f1 _ _ r N names mp hn hS hx hy hus hdec hno hit hN hnn hb hM
    rw [hdx, hdy] at hr
    exact ⟨a', mp', hr, hS', hg', hM'⟩
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg, rpNodeW_let] at hn
    have := rpLet_ok dn fe vis k ih m m' a no nl us b nn f1 _ _ _ r N names mp hn hS hx hy hz hus hdec hno hit hN hnn hb hM
    rw [hdx, hdy, hdz] at this
    exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hi, hz, hdz⟩ := hvr
    rw [hg, rpNodeW_proj k m no nl us b nn f1 h 9 _ _ _ (by decide) (by decide) (by decide)] at hn
    have := rpProj_ok dn fe vis k ih m m' a no nl us b nn f1 _ _ _ r N names mp hn hS hz hus hdec hno hit hN hnn hb hM
    rw [hdz, hdx, hi] at this
    exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv


theorem rpTwin_node (names : List NIdx) (us : LsIdx) (b n : Nat) (memo : Std.HashMap EIdx EIdx)
    (fuel : Nat) (h : EIdx) (a : AState) (v : ENodeView) (hv : a.store.view h = some v) (hnv : NodeVr v) :
    (ConRon.Arena.replaceAppsGo names us b n memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← rpArm names us b n memo fuel h v
          pure (r, m.insert h r) : AM (EIdx × Std.HashMap EIdx EIdx)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [replaceAppsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind])

theorem rpGo_nodeCase (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (j : Nat)
    (ih : ∀ k, k + 1 < j + 1 → RpGoOK dn fe vis k) (m m' : Mem) (a : AState)
    (no nl us b nn f h r : Word) (N : Nat) (names : List NIdx) (mp : Std.HashMap EIdx EIdx) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVr v) (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : rpG1 j m no nl us b nn f h vl = some (r, m')) (hS : StageR dn vis fe m a) (hh : H h) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR m mp) :
    ∃ a' mp', (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp (F + 1) (decE h)).run a =
        .ok ((decE r, mp'), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 1 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  have hn3 : ¬ vl.headD 0 = 3 := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  rw [rpG1_node j m no nl us b nn f h vl hvl hnl hn3] at hb
  rw [rpTwin_node _ _ _ _ _ _ _ a v hv hnv]
  by_cases hfr : mfindG raSch m h 0 = []
  · rw [rpG3_abort j m no nl us b nn f h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG raSch m h 0).headD 0 ≠ 0
  · rw [rpG3_hit j m no nl us b nn f h vl _ hfr hhit] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hmem := memoRG_hit raSch bmKey (fun w : Word => decE w) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨a, mp, ?_, hS, IWGrow.refl _, hM⟩
    simp only [hmem]; rfl
  · rw [rpG3_miss j m no nl us b nn f h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss raSch bmKey (fun w : Word => decE w) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases j with
    | zero => simp [rpNodeW, rpG4] at hb
    | succ k =>
      cases hnode : rpNodeW (k + 1) m no nl us b nn (f - 1) h (vl.headD 0) (vl.tail.headD 0)
          (vl.tail.tail.headD 0) (vl.tail.tail.tail.headD 0) with
      | none => rw [hnode] at hb; simp [rpG4] at hb
      | some pn =>
        obtain ⟨rn, m1⟩ := pn
        rw [hnode, rpG4_some] at hb
        cases hset : msetG raSch m1 h 0 rn with
        | none => rw [hset] at hb; simp [rpG5] at hb
        | some m2 =>
          rw [hset, rpG5_some] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
          obtain ⟨a1, mp1, hr1, hS1, hg1, hM1⟩ := rpNode_arm dn fe vis k (ih k (by omega)) vl v hvr hnv m m1 a no nl us b
            nn (f - 1) h rn N names mp hnode hS hh hus hdec hno hit hN hnn hbN hM
          rw [hF1] at hr1
          have hset' := memoRG_set raSch raSch_wf bmKey (fun w : Word => decE w) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
          have hfs : MemFrame [RAM] [raSch.cs + 1] m1 m2 := msetG_frame raSch raSch_wf m1 m2 h 0 rn hset
          obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 hfs (by intro b hb; simp at hb; subst hb; decide)
            (by intro x hx; simp [raSch] at hx; subst hx; decide) (by decide) (by simp [raSch])
          refine ⟨a1, mp1.insert (decE h) (decE rn), ?_, hS2, hg1.trans hg2, hset'⟩
          rw [hmiss]
          simp only [StateT.run_bind]
          rw [hr1]
          simp only [except_ok_bind]
          rfl


theorem rpGo_step_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (j : Nat)
    (ih : ∀ k, k + 1 < j + 1 → RpGoOK dn fe vis k) : RpGoOK dn fe vis (j + 1) := by
  intro m m' a no nl us b nn f h r N names mp hb hS hh hus hdec hno hit hN hnn hbN hM
  by_cases hf0 : f = 0
  · rw [rpGoW_abort j m no nl us b nn f h hf0] at hb; simp at hb
  rw [rpGoW_view j m no nl us b nn f h hf0] at hb
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [rpG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m a hS.1.arena.1 h hne
    rw [hvl] at hvr hb
    have leaf : ∀ (hg : (g :: vt).headD 0 = 0 ∨ (g :: vt).headD 0 = 1 ∨ (g :: vt).headD 0 = 2 ∨ (g :: vt).headD 0 = 8),
        (match v with | .bvar _ | .sort _ | .lit _ | .fvar _ _ => True | _ => False) →
        ∃ a' mp', (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)).run a =
          .ok ((decE r, mp'), a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ rpMR m' mp' := by
      intro hg hv'
      rw [rpG1_leaf j m no nl us b nn f h _ (by simp) hg] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨a, mp, ?_, hS, IWGrow.refl _, hM⟩
      rw [hF, replaceAppsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      cases v <;> first | rfl | exact False.elim hv'
    cases v with
    | bvar i =>
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      exact leaf (Or.inl hg0) trivial
    | sort u =>
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      exact leaf (Or.inr (Or.inr (Or.inl hg0))) trivial
    | lit l =>
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      exact leaf (Or.inr (Or.inr (Or.inr hg0))) trivial
    | fvar i ty =>
      have hg0 : (g :: vt).headD 0 = 1 := hvr.1
      exact leaf (Or.inr (Or.inl hg0)) trivial
    | const nn' us' =>
      have hg3 : (g :: vt).headD 0 = 3 := hvr.1
      rw [rpG1_const j m no nl us b nn f h _ (by simp) (by rw [hg3]; decide) hg3] at hb
      cases j with
      | zero => simp [ahWf, rpH] at hb
      | succ i =>
        cases hah : ahW i m no nl us b nn h with
        | none => simp only [ahWf] at hb; rw [hah] at hb; simp [rpH] at hb
        | some pr =>
          obtain ⟨rr, m1⟩ := pr
          simp only [ahWf] at hb
          rw [hah, rpH_some] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨xo, a1, hrun1, hS1, hg1, hout⟩ := ahW_ok i dn fe vis m m1 a no nl us b nn h N names rr hah hS hN hh hus
            hbN hdec hno hnn
          rw [show (decI h : EIdx) = decE h from rfl] at hrun1
          refine ⟨a1, mp, ?_, hS1, hg1, rpMR_low (ahW_low hah) hM⟩
          rw [hF, replaceAppsGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
          simp only [StateT.run_bind]
          rw [hrun1]
          simp only [except_ok_bind]
          cases xo with
          | none =>
            simp only [decOE] at hout
            simp only [hout, ne_eq, not_true_eq_false, if_false]; rfl
          | some e' =>
            simp only [decOE, decW0E] at hout
            obtain ⟨h1, -, hd⟩ := hout
            have hne : ¬ rr.headD 0 = 0 := by rw [h1]; decide
            rw [if_pos (show rr.headD 0 ≠ 0 from hne)]
            show (pure (e', mp) : AM _).run a1 = _
            rw [show decE (rr.tail.headD 0) = e' from hd]; rfl
    | app f' x' =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inl hvr.1) hb hS hh hus hdec hno hit hN hnn hbN hM
    | lam f' x' =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inl hvr.1)) hb hS hh hus hdec hno hit hN hnn hbN hM
    | forallE f' x' =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inl hvr.1))) hb hS hh hus hdec hno hit hN hnn hbN hM
    | letE t v' b' =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hS hh hus hdec hno hit hN hnn hbN hM
    | proj s i e =>
      rw [hF]
      exact rpGo_nodeCase dn fe vis j ih m m' a no nl us b nn f h r N names mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inr hvr.1)))) hb hS hh hus hdec hno hit hN hnn hbN hM


theorem rpGoOK (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) :
    RpGoOK dn fe vis n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a no nl us b nn f h r N names mp hb; simp [rpGoW] at hb
    | succ j => exact rpGo_step_ok dn fe vis j (fun k hk => ih k (by omega))

theorem rpConstW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us b nn e r : Word) (N : Nat) (names : List NIdx)
    (mp0 : Std.HashMap EIdx EIdx)
    (hb : rpConstW n m no nl us b nn e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hN : nn.toNat = N) (hnn : nn.toNat + names.length < 2 ^ 64)
    (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR m mp0) :
    ∃ a', (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)).run a = .ok (decE r, a') ∧
      rpMR m' ∅ ∧ StageR dn vis fe m' a' ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) raSch.cs + 2 = 0
  · simp [rpConstW, h0] at hb
  rw [rpConstW_eq n m no nl us b nn e h0] at hb
  have hf0 := mclearG_frame raSch m
  have hM0 := memoRG_clear raSch raSch_wf bmKey (fun w : Word => decE w) m mp0 hM h0
  obtain ⟨hS0, hg0⟩ := StageR.frame_hi hS hf0 (by intro b hb; simp at hb) (by intro x hx; simp [raSch] at hx; rcases hx with rfl | rfl <;> decide)
    (by simp) (by simp [raSch])
  have hdec0 : decHL (mclearG raSch m) no.toNat nl.toNat = some names := by rw [decHL_grow hg0 hit]; exact hdec
  cases hg : rpGoW n (mclearG raSch m) no nl us b nn CWF e with
  | none => rw [hg] at hb; simp [rpClrK] at hb
  | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [hg] at hb
    by_cases h1 : rdW (m1.arr64 CTL) raSch.cs + 2 = 0
    · simp [rpClrK, h1] at hb
    rw [rpClrK_some r1 m1 h1] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨a1, mp1, hrun, hS1, hg1, hM1⟩ := rpGoOK dn fe vis n _ _ a no nl us b nn CWF e r1 N names ∅ hg hS0 he hus hdec0
      hno (by have := hg0.1; omega) hN hnn hbN hM0
    rw [CWF_eq] at hrun
    have hM2 := memoRG_clear raSch raSch_wf bmKey (fun w : Word => decE w) m1 mp1 hM1 h1
    have hf2 := mclearG_frame raSch m1
    obtain ⟨hS2, hg2⟩ := StageR.frame_hi hS1 hf2 (by intro b hb; simp at hb) (by intro x hx; simp [raSch] at hx; rcases hx with rfl | rfl <;> decide)
      (by simp) (by simp [raSch])
    refine ⟨a1, ?_, hM2, hS2, (hg0.trans hg1).trans hg2⟩
    simp only [ConRon.Arena.replaceApps, StateT.run_bind]
    rw [hrun]
    rfl


section census
variable (p : Prog) (hl : AhLook p) (hk : MkLook p)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
include hl hk hf hput hgo hnode

/-- **`replace_apps_go` (with `replace_apps_node`) refines `replaceAppsGo`**, from a memo related to
the twin's. -/
@[refines ConRon.Arena.replaceAppsGo]
theorem replaceAppsGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn f h : Word) (N : Nat) (names : List NIdx)
    (mp : Std.HashMap EIdx EIdx) (hh : H h) (hus : H us) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hN : nn.toNat = N)
    (hnn : nn.toNat + names.length < 2 ^ 64) (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "replace_apps_go" [no, nl, us, b, nn, f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀ ∧
      decE (r.headD 0) =
        (AM.res (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀).1 ∧
      rpMR s'.mem
        (AM.res (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem
        (AM.st (ConRon.Arena.replaceAppsGo names (decI us) b.toNat N mp f.toNat (decE h)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((rpGo_spec p hl hk hf hput hgo hnode n).1 s₀ no nl us b nn f h) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨a', mp', hrun, hS', hg, hM'⟩ := rpGoOK dn fe vis n _ _ a₀ no nl us b nn f h _ N names mp hm hS hh hus hdec
    hno hit hN hnn hbN hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], by rw [hres]; exact hM', by rw [hst]; exact hS', hg⟩

end census

section census2
variable (p : Prog) (hl : AhLook p) (hk : MkLook p)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
  (hcl : p.lookup "ra_clear" = some (memoClearG raSch))
  (hp : p.lookup "replace_apps" = some replaceApps)
include hl hk hf hput hgo hnode hcl hp

/-- **`replace_apps` refines `replaceApps`**: one memoised DAG walk between two clears. -/
@[refines ConRon.Arena.replaceApps]
theorem replaceApps_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us b nn e : Word) (N : Nat) (names : List NIdx)
    (mp0 : Std.HashMap EIdx EIdx) (he : H e) (hus : H us) (hS : StageR dn vis fe s₀.mem a₀)
    (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hN : nn.toNat = N)
    (hnn : nn.toNat + names.length < 2 ^ 64) (hbN : b.toNat + N < 2 ^ 64) (hM : rpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "replace_apps" [no, nl, us, b, nn, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀ ∧
      decE (r.headD 0) = AM.res (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀ ∧
      rpMR s'.mem ∅ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.replaceApps names (decI us) b.toNat N (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (replaceApps_spec p hl hk hf hput hgo hnode hcl hp n s₀ no nl us b nn e) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨a', hrun, hM', hS', hg⟩ := rpConstW_ok n dn fe vis _ _ a₀ no nl us b nn e _ N names mp0 hm hS he hus hdec hno
    hit hN hnn hbN hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hres], hM', by rw [hst]; exact hS', hg⟩

end census2

/-! ## `depth_go`, `depth_node`: word models -/

def dpFin (mx : Word) (m : Mem) : Option (Word × Mem) :=
  if 4294967295 ≤ mx then none else some (mx + 1, m)

mutual
def dpGoW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, f, h => if f = 0 then none else dpG1 n m f h (eViewW m h)
def dpG1 (n : Nat) (m : Mem) (f h : Word) (v : List Word) : Option (Word × Mem) :=
  if v = [] then none
  else if v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8 then some (1, m)
  else dpG3 n m f h v (mfindG dpSch m h 0)
def dpG3 (n : Nat) (m : Mem) (f h : Word) (v fr : List Word) : Option (Word × Mem) :=
  if fr = [] then none
  else if fr.headD 0 ≠ 0 then some (rdW (m.arr64 DPM) (fr.tail.headD 0 * 4 + 3), m)
  else dpG4 h (dpNodeW n m (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
    (v.tail.tail.tail.headD 0))
def dpG4 (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => dpG5 r (msetG dpSch m1 h 0 r)
def dpG5 (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m2 => some (r, m2)
def dpNodeW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, f1, g, x, y, z =>
    if g = 4 ∨ g = 5 ∨ g = 6 then dpB1 n f1 y (dpGoW n m f1 x)
    else if g = 7 then dpL1 n f1 y z (dpGoW n m f1 x)
    else dpP1 (dpGoW n m f1 z)
def dpB1 (n : Nat) (f1 y : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d1, m1) => dpB2 d1 (dpGoW n m1 f1 y)
def dpB2 (d1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d2, m2) => dpFin (maxW d1 d2) m2
def dpL1 (n : Nat) (f1 y z : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d1, m1) => dpL2 n f1 z d1 (dpGoW n m1 f1 y)
def dpL2 (n : Nat) (f1 z d1 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d2, m2) => dpL3 d1 d2 (dpGoW n m2 f1 z)
def dpL3 (d1 d2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d3, m3) => dpFin (maxW (maxW d1 d2) d3) m3
def dpP1 : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (d1, m1) => dpFin d1 m1
end

section arms
variable (n : Nat) (m m1 m2 m3 : Mem) (f f1 h g x y z d1 d2 d3 r : Word) (v fr : List Word)
theorem dpGoW_abort (hf : f = 0) : dpGoW (n + 1) m f h = none := by simp [dpGoW, hf]
theorem dpGoW_view (hf : f ≠ 0) : dpGoW (n + 1) m f h = dpG1 n m f h (eViewW m h) := by simp [dpGoW, hf]
theorem dpG1_abort (hv : v = []) : dpG1 n m f h v = none := by simp [dpG1, hv]
theorem dpG1_leaf (hv : v ≠ [])
    (hg : v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8) :
    dpG1 n m f h v = some (1, m) := by simp only [dpG1]; rw [if_neg hv, if_pos hg]
theorem dpG1_node (hv : v ≠ [])
    (hg : ¬ (v.headD 0 = 0 ∨ v.headD 0 = 1 ∨ v.headD 0 = 2 ∨ v.headD 0 = 3 ∨ v.headD 0 = 8)) :
    dpG1 n m f h v = dpG3 n m f h v (mfindG dpSch m h 0) := by
  simp only [dpG1]; rw [if_neg hv, if_neg hg]
theorem dpG3_abort (hr : fr = []) : dpG3 n m f h v fr = none := by simp [dpG3, hr]
theorem dpG3_hit (hr : fr ≠ []) (hh : fr.headD 0 ≠ 0) :
    dpG3 n m f h v fr = some (rdW (m.arr64 DPM) (fr.tail.headD 0 * 4 + 3), m) := by
  simp only [dpG3]; rw [if_neg hr, if_pos hh]
theorem dpG3_miss (hr : fr ≠ []) (hh : ¬ fr.headD 0 ≠ 0) :
    dpG3 n m f h v fr = dpG4 h (dpNodeW n m (f - 1) (v.headD 0) (v.tail.headD 0)
      (v.tail.tail.headD 0) (v.tail.tail.tail.headD 0)) := by
  simp only [dpG3]; rw [if_neg hr, if_neg hh]
theorem dpG4_some : dpG4 h (some (r, m1)) = dpG5 r (msetG dpSch m1 h 0 r) := by rw [dpG4]
theorem dpG5_some : dpG5 r (some m2) = some (r, m2) := by rw [dpG5]
theorem dpNodeW_bin (hg : g = 4 ∨ g = 5 ∨ g = 6) :
    dpNodeW (n + 1) m f1 g x y z = dpB1 n f1 y (dpGoW n m f1 x) := by
  simp only [dpNodeW]; rw [if_pos hg]
theorem dpNodeW_let (hg : g = 7) : dpNodeW (n + 1) m f1 g x y z = dpL1 n f1 y z (dpGoW n m f1 x) := by
  have : ¬ (g = 4 ∨ g = 5 ∨ g = 6) := by
    intro e; rcases e with e | e | e <;> (rw [hg] at e; exact absurd e (by decide))
  simp only [dpNodeW]; rw [if_neg this, if_pos hg]
theorem dpNodeW_proj (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) :
    dpNodeW (n + 1) m f1 g x y z = dpP1 (dpGoW n m f1 z) := by
  simp only [dpNodeW]; rw [if_neg hg2, if_neg hg3]
theorem dpB1_some : dpB1 n f1 y (some (d1, m1)) = dpB2 d1 (dpGoW n m1 f1 y) := by rw [dpB1]
theorem dpB2_some : dpB2 d1 (some (d2, m2)) = dpFin (maxW d1 d2) m2 := by rw [dpB2]
theorem dpL1_some : dpL1 n f1 y z (some (d1, m1)) = dpL2 n f1 z d1 (dpGoW n m1 f1 y) := by rw [dpL1]
theorem dpL2_some : dpL2 n f1 z d1 (some (d2, m2)) = dpL3 d1 d2 (dpGoW n m2 f1 z) := by rw [dpL2]
theorem dpL3_some : dpL3 d1 d2 (some (d3, m3)) = dpFin (maxW (maxW d1 d2) d3) m3 := by rw [dpL3]
theorem dpP1_some : dpP1 (some (d1, m1)) = dpFin d1 m1 := by rw [dpP1]
theorem dpFin_big (hb : 4294967295 ≤ d1) : dpFin d1 m = none := by simp [dpFin, hb]
theorem dpFin_ok (hb : ¬ 4294967295 ≤ d1) : dpFin d1 m = some (d1 + 1, m) := by simp [dpFin, hb]
end arms
attribute [ind_grind] dpGoW_abort dpGoW_view dpG1_abort dpG1_leaf dpG1_node dpG3_abort dpG3_hit dpG3_miss
  dpG4_some dpG5_some dpNodeW_bin dpNodeW_let dpNodeW_proj dpB1_some dpB2_some dpL1_some dpL2_some
  dpL3_some dpP1_some dpFin_big dpFin_ok

section spec
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "dp_find" = some (memoFindG dpSch)) (hput : p.lookup "dp_put" = some (memoPutG dpSch))
  (hgo : p.lookup "depth_go" = some depthGo) (hnode : p.lookup "depth_node" = some depthNode)

def DpGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (f h : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "depth_go" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ dpGoW n s₀.mem f h = some (r.headD 0, s'.mem); ⊤⦄

def DpNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (f1 g x y z : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "depth_node" [f1, g, x, y, z]
    ⦃fun r s' => LocEq s' s₀ ∧ dpNodeW n s₀.mem f1 g x y z = some (r.headD 0, s'.mem); ⊤⦄

include hv hf hput hgo in
theorem dpGo_step (n : Nat) (ih : DpNodeSpec p n) : DpGoSpec p (n + 1) := by
  unfold DpNodeSpec at ih
  intro s₀ f h
  rw [invoke_eq _ hgo]
  simp only [callFn, depthGo]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p hv n, memoFindG_spec dpSch p _ hf n, memoPutG_spec dpSch p _ hput n, ih] <;>
    finish (gen := 20)

include hgo hnode in
theorem dpNode_step (n : Nat) (ih : DpGoSpec p n) : DpNodeSpec p (n + 1) := by
  unfold DpGoSpec at ih
  intro s₀ f1 g x y z
  rw [invoke_eq _ hnode]
  simp only [callFn, depthNode]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
    finish (gen := 20) [maxW]

include hv hf hput hgo hnode in
theorem dpGo_spec (n : Nat) : DpGoSpec p n ∧ DpNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ f h; rw [invoke_eq _ hgo]; simp only [callFn, depthGo]; vcgen [exec] <;> grind
    · intro s₀ f1 g x y z; rw [invoke_eq _ hnode]; simp only [callFn, depthNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨dpGo_step p hv hf hput hgo n ih.2, dpNode_step p hgo hnode n ih.1⟩

end spec


/-! ### The relational side -/

def dpArm (memo : Std.HashMap EIdx Nat) (fuel : Nat) : ENodeView → AM (Nat × Std.HashMap EIdx Nat)
  | .app f a => do
    let (d1, m) ← ConRon.Arena.depthGo memo fuel f
    let (d2, m2) ← ConRon.Arena.depthGo m fuel a
    pure (max d1 d2 + 1, m2)
  | .lam ty body => do
    let (d1, m) ← ConRon.Arena.depthGo memo fuel ty
    let (d2, m2) ← ConRon.Arena.depthGo m fuel body
    pure (max d1 d2 + 1, m2)
  | .forallE ty body => do
    let (d1, m) ← ConRon.Arena.depthGo memo fuel ty
    let (d2, m2) ← ConRon.Arena.depthGo m fuel body
    pure (max d1 d2 + 1, m2)
  | .letE ty val body => do
    let (d1, m) ← ConRon.Arena.depthGo memo fuel ty
    let (d2, m2) ← ConRon.Arena.depthGo m fuel val
    let (d3, m3) ← ConRon.Arena.depthGo m2 fuel body
    pure (max (max d1 d2) d3 + 1, m3)
  | .proj _ _ x => do
    let (d, m) ← ConRon.Arena.depthGo memo fuel x
    pure (d + 1, m)
  | _ => pure (1, memo)

def NodeVd : ENodeView → Prop
  | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

theorem depthGo_succ' (memo : Std.HashMap EIdx Nat) (fuel : Nat) (h : EIdx) :
    ConRon.Arena.depthGo memo (fuel + 1) h = (do
      let v ← view h
      match v with
      | .bvar _ => pure (1, memo)
      | .fvar _ _ => pure (1, memo)
      | .sort _ => pure (1, memo)
      | .const _ _ => pure (1, memo)
      | .lit _ => pure (1, memo)
      | v =>
        match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← dpArm memo fuel v
          pure (r, m.insert h r)) := by
  rw [ConRon.Arena.depthGo.eq_2]
  congr 1
  funext v
  cases v <;> first | rfl | (simp only [dpArm, bind_assoc, pure_bind]; rfl)

theorem dpTwin_node (memo : Std.HashMap EIdx Nat) (fuel : Nat) (h : EIdx) (a : AState) (v : ENodeView)
    (hv : a.store.view h = some v) (hnv : NodeVd v) :
    (ConRon.Arena.depthGo memo (fuel + 1) h).run a =
      ((match memo[h]? with
        | some r => pure (r, memo)
        | none => do
          let (r, m) ← dpArm memo fuel v
          pure (r, m.insert h r) : AM (Nat × Std.HashMap EIdx Nat)).run a) := by
  cases v <;> first
    | exact False.elim hnv
    | (rw [depthGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind])

theorem dpSch_wf : dpSch.WF := ⟨by decide, by decide⟩

theorem dpFrame_arena {m m' : Mem} {a : AState} (hf : MemFrame [DPM] [207] m m') (hR : ArenaR m a) :
    ArenaR m' a :=
  ArenaR.frame (fun b hb => by simp at hb; subst hb; simp [arenaArrs, storeArrs, memoArrs, DPM])
    (fun x hx => by simp at hx; subst hx; exact not_mem_arenaCtl _ (by decide)) hf hR

abbrev dpMR (m : Mem) (mp : Std.HashMap EIdx Nat) : Prop :=
  MemoRG dpSch bmKey (fun w : Word => w.toNat) m mp

def DpGoOK (n : Nat) : Prop :=
  ∀ (m m' : Mem) (a : AState) (f h r : Word) (mp : Std.HashMap EIdx Nat),
    dpGoW n m f h = some (r, m') → ArenaR m a → H h → dpMR m mp →
    ∃ d mp', (ConRon.Arena.depthGo mp f.toNat (decE h)).run a = .ok ((d, mp'), a) ∧ r.toNat = d ∧
      dpMR m' mp' ∧ MemFrame [DPM] [207] m m'

theorem fin_toNat {d : Word} (hb : ¬ 4294967295 ≤ d) : (d + 1).toNat = d.toNat + 1 := by
  have : d.toNat < 4294967295 := by
    have e : (4294967295 : Word).toNat = 4294967295 := by decide
    have : ¬ (4294967295 : Word).toNat ≤ d.toNat := fun hh => hb (UInt64.le_iff_toNat_le.mpr hh)
    omega
  rw [UInt64.toNat_add]; simp; omega


theorem dpNodeBin_ok (n : Nat) (ih : DpGoOK n) (m m' : Mem) (a : AState) (f1 g x y z r : Word)
    (mp : Std.HashMap EIdx Nat) (hg : g = 4 ∨ g = 5 ∨ g = 6) (hx : H x) (hy : H y)
    (hn : dpNodeW (n + 1) m f1 g x y z = some (r, m')) (hA : ArenaR m a) (hM : dpMR m mp) :
    ∃ d mp', (do
        let (d1, mm) ← ConRon.Arena.depthGo mp f1.toNat (decE x)
        let (d2, m2) ← ConRon.Arena.depthGo mm f1.toNat (decE y)
        pure (max d1 d2 + 1, m2) : AM (Nat × Std.HashMap EIdx Nat)).run a = .ok ((d, mp'), a) ∧
      r.toNat = d ∧ dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
  rw [dpNodeW_bin n m f1 g x y z hg] at hn
  cases h1 : dpGoW n m f1 x with
  | none => rw [h1] at hn; simp [dpB1] at hn
  | some p1 =>
    obtain ⟨d1w, m1⟩ := p1
    rw [h1, dpB1_some] at hn
    cases h2 : dpGoW n m1 f1 y with
    | none => rw [h2] at hn; simp [dpB2] at hn
    | some p2 =>
      obtain ⟨d2w, m2⟩ := p2
      rw [h2, dpB2_some] at hn
      by_cases hb : 4294967295 ≤ maxW d1w d2w
      · rw [dpFin_big _ _ hb] at hn; simp at hn
      rw [dpFin_ok _ _ hb] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a f1 x d1w mp h1 hA hx hM
      obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a f1 y d2w mp1 h2 (dpFrame_arena hf1 hA) hy hM1
      refine ⟨max c1 c2 + 1, mp2, ?_, ?_, hM2, hf1.trans hf2⟩
      · simp only [StateT.run_bind]
        rw [hr1]
        simp only [except_ok_bind, StateT.run_bind]
        rw [hr2]
        simp only [except_ok_bind]
        rfl
      · rw [fin_toNat hb, maxW_toNat, hb1, hb2]

theorem dpNodeLet_ok (n : Nat) (ih : DpGoOK n) (m m' : Mem) (a : AState) (f1 x y z r : Word)
    (mp : Std.HashMap EIdx Nat) (hx : H x) (hy : H y) (hz : H z)
    (hn : dpNodeW (n + 1) m f1 7 x y z = some (r, m')) (hA : ArenaR m a) (hM : dpMR m mp) :
    ∃ d mp', (do
        let (d1, mm) ← ConRon.Arena.depthGo mp f1.toNat (decE x)
        let (d2, m2) ← ConRon.Arena.depthGo mm f1.toNat (decE y)
        let (d3, m3) ← ConRon.Arena.depthGo m2 f1.toNat (decE z)
        pure (max (max d1 d2) d3 + 1, m3) : AM (Nat × Std.HashMap EIdx Nat)).run a = .ok ((d, mp'), a) ∧
      r.toNat = d ∧ dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
  rw [dpNodeW_let n m f1 7 x y z rfl] at hn
  cases h1 : dpGoW n m f1 x with
  | none => rw [h1] at hn; simp [dpL1] at hn
  | some p1 =>
    obtain ⟨d1w, m1⟩ := p1
    rw [h1, dpL1_some] at hn
    cases h2 : dpGoW n m1 f1 y with
    | none => rw [h2] at hn; simp [dpL2] at hn
    | some p2 =>
      obtain ⟨d2w, m2⟩ := p2
      rw [h2, dpL2_some] at hn
      cases h3 : dpGoW n m2 f1 z with
      | none => rw [h3] at hn; simp [dpL3] at hn
      | some p3 =>
        obtain ⟨d3w, m3⟩ := p3
        rw [h3, dpL3_some] at hn
        by_cases hb : 4294967295 ≤ maxW (maxW d1w d2w) d3w
        · rw [dpFin_big _ _ hb] at hn; simp at hn
        rw [dpFin_ok _ _ hb] at hn
        simp only [Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a f1 x d1w mp h1 hA hx hM
        obtain ⟨c2, mp2, hr2, hb2, hM2, hf2⟩ := ih m1 m2 a f1 y d2w mp1 h2 (dpFrame_arena hf1 hA) hy hM1
        obtain ⟨c3, mp3, hr3, hb3, hM3, hf3⟩ := ih m2 m3 a f1 z d3w mp2 h3
          (dpFrame_arena (hf1.trans hf2) hA) hz hM2
        refine ⟨max (max c1 c2) c3 + 1, mp3, ?_, ?_, hM3, (hf1.trans hf2).trans hf3⟩
        · simp only [StateT.run_bind]
          rw [hr1]
          simp only [except_ok_bind, StateT.run_bind]
          rw [hr2]
          simp only [except_ok_bind, StateT.run_bind]
          rw [hr3]
          simp only [except_ok_bind]
          rfl
        · rw [fin_toNat hb, maxW_toNat, maxW_toNat, hb1, hb2, hb3]

theorem dpNodeProj_ok (n : Nat) (ih : DpGoOK n) (m m' : Mem) (a : AState) (f1 g x y z r : Word)
    (mp : Std.HashMap EIdx Nat) (hg2 : ¬ (g = 4 ∨ g = 5 ∨ g = 6)) (hg3 : g ≠ 7) (hz : H z)
    (hn : dpNodeW (n + 1) m f1 g x y z = some (r, m')) (hA : ArenaR m a) (hM : dpMR m mp) :
    ∃ d mp', (do
        let (d, mm) ← ConRon.Arena.depthGo mp f1.toNat (decE z)
        pure (d + 1, mm) : AM (Nat × Std.HashMap EIdx Nat)).run a = .ok ((d, mp'), a) ∧
      r.toNat = d ∧ dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
  rw [dpNodeW_proj n m f1 g x y z hg2 hg3] at hn
  cases h1 : dpGoW n m f1 z with
  | none => rw [h1] at hn; simp [dpP1] at hn
  | some p1 =>
    obtain ⟨d1w, m1⟩ := p1
    rw [h1, dpP1_some] at hn
    by_cases hb : 4294967295 ≤ d1w
    · rw [dpFin_big _ _ hb] at hn; simp at hn
    rw [dpFin_ok _ _ hb] at hn
    simp only [Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    obtain ⟨c1, mp1, hr1, hb1, hM1, hf1⟩ := ih m m1 a f1 z d1w mp h1 hA hz hM
    refine ⟨c1 + 1, mp1, ?_, ?_, hM1, hf1⟩
    · simp only [StateT.run_bind]
      rw [hr1]
      simp only [except_ok_bind]
      rfl
    · rw [fin_toNat hb, hb1]


theorem dpNode_arm (k : Nat) (ih : DpGoOK k) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVd v) (m m' : Mem) (a : AState) (f1 r : Word) (mp : Std.HashMap EIdx Nat)
    (hn : dpNodeW (k + 1) m f1 (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
      (vl.tail.tail.tail.headD 0) = some (r, m'))
    (hA : ArenaR m a) (hM : dpMR m mp) :
    ∃ d mp', (dpArm mp f1.toNat v).run a = .ok ((d, mp'), a) ∧ r.toNat = d ∧ dpMR m' mp' ∧
      MemFrame [DPM] [207] m m' := by
  cases v with
  | app f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := dpNodeBin_ok k ih m m' a f1 _ _ _ _ r mp (Or.inl hg) hx hy hn hA hM
    rw [hdx, hdy] at this
    simp only [dpArm]; exact this
  | lam f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := dpNodeBin_ok k ih m m' a f1 _ _ _ _ r mp (Or.inr (Or.inl hg)) hx hy hn hA hM
    rw [hdx, hdy] at this
    simp only [dpArm]; exact this
  | forallE f x' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy⟩ := hvr
    have := dpNodeBin_ok k ih m m' a f1 _ _ _ _ r mp (Or.inr (Or.inr hg)) hx hy hn hA hM
    rw [hdx, hdy] at this
    simp only [dpArm]; exact this
  | letE t v' b' =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, hy, hdy, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := dpNodeLet_ok k ih m m' a f1 _ _ _ r mp hx hy hz hn hA hM
    rw [hdx, hdy, hdz] at this
    simp only [dpArm]; exact this
  | proj s i e =>
    simp only [ViewR, getD1_eq', getD2_eq, getD3_eq] at hvr
    obtain ⟨hg, hx, hdx, -, hz, hdz⟩ := hvr
    rw [hg] at hn
    have := dpNodeProj_ok k ih m m' a f1 9 _ _ _ r mp (by decide) (by decide) hz hn hA hM
    rw [hdz] at this
    simp only [dpArm]; exact this
  | bvar _ => exact False.elim hnv
  | sort _ => exact False.elim hnv
  | const _ _ => exact False.elim hnv
  | lit _ => exact False.elim hnv
  | fvar _ _ => exact False.elim hnv

theorem dpGo_nodeCase (j : Nat) (ih : ∀ k, k + 1 < j + 1 → DpGoOK k) (m m' : Mem) (a : AState)
    (f h r : Word) (mp : Std.HashMap EIdx Nat) (F : Nat)
    (hF : f.toNat = F + 1) (hf0 : f ≠ 0) (vl : List Word) (v : ENodeView) (hvr : ViewR vl v)
    (hnv : NodeVd v) (hv : a.store.view (decE h) = some v) (hvl : vl ≠ [])
    (hgs : vl.headD 0 = 4 ∨ vl.headD 0 = 5 ∨ vl.headD 0 = 6 ∨ vl.headD 0 = 7 ∨ vl.headD 0 = 9)
    (hb : dpG1 j m f h vl = some (r, m')) (hA : ArenaR m a) (hh : H h) (hM : dpMR m mp) :
    ∃ d mp', (ConRon.Arena.depthGo mp (F + 1) (decE h)).run a = .ok ((d, mp'), a) ∧ r.toNat = d ∧
      dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
  have hnl : ¬ (vl.headD 0 = 0 ∨ vl.headD 0 = 1 ∨ vl.headD 0 = 2 ∨ vl.headD 0 = 3 ∨ vl.headD 0 = 8) := by
    rcases hgs with e | e | e | e | e <;> rw [e] <;> decide
  rw [dpG1_node j m f h vl hvl hnl] at hb
  rw [dpTwin_node _ _ _ a v hv hnv]
  by_cases hfr : mfindG dpSch m h 0 = []
  · rw [dpG3_abort j m f h vl _ hfr] at hb; simp at hb
  by_cases hhit : (mfindG dpSch m h 0).headD 0 ≠ 0
  · rw [dpG3_hit j m f h vl _ hfr hhit] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hmem := memoRG_hit dpSch bmKey (fun w : Word => w.toNat) m mp hM h 0 hfr hhit ⟨hh, rfl⟩
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmem
    refine ⟨_, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
    simp only [hmem]; rfl
  · rw [dpG3_miss j m f h vl _ hfr hhit] at hb
    have hmiss := memoRG_miss dpSch bmKey (fun w : Word => w.toNat) m mp hM h 0 ⟨hh, rfl⟩ hfr (by simpa using hhit)
    have : bmKey.dk h 0 = decE h := rfl
    rw [this] at hmiss
    cases j with
    | zero => simp [dpNodeW, dpG4] at hb
    | succ k =>
      cases hnode : dpNodeW (k + 1) m (f - 1) (vl.headD 0) (vl.tail.headD 0) (vl.tail.tail.headD 0)
          (vl.tail.tail.tail.headD 0) with
      | none => rw [hnode] at hb; simp [dpG4] at hb
      | some pn =>
        obtain ⟨rn, m1⟩ := pn
        rw [hnode, dpG4_some] at hb
        cases hset : msetG dpSch m1 h 0 rn with
        | none => rw [hset] at hb; simp [dpG5] at hb
        | some m2 =>
          rw [hset, dpG5_some] at hb
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          have hF1 : (f - 1).toNat = F := by rw [toNat_sub_one' hf0, hF]; rfl
          obtain ⟨d, mp1, hr1, hbb, hM1, hfr1⟩ := dpNode_arm k (ih k (by omega)) vl v hvr hnv m m1 a (f - 1) rn mp
            hnode hA hM
          rw [hF1] at hr1
          have hset' := memoRG_set dpSch dpSch_wf bmKey (fun w : Word => w.toNat) m1 mp1 hM1 h 0 rn ⟨hh, rfl⟩ m2 hset
          have hfs : MemFrame [DPM] [dpSch.cs + 1] m1 m2 := msetG_frame dpSch dpSch_wf m1 m2 h 0 rn hset
          refine ⟨d, mp1.insert (decE h) d, ?_, hbb, ?_, hfr1.trans hfs⟩
          · rw [hmiss]
            simp only [StateT.run_bind]
            rw [hr1]
            simp only [except_ok_bind]
            rfl
          · rw [← hbb]; exact hset'


theorem dpGo_step_ok (j : Nat) (ih : ∀ k, k + 1 < j + 1 → DpGoOK k) : DpGoOK (j + 1) := by
  intro m m' a f h r mp hb hA hh hM
  by_cases hf0 : f = 0
  · rw [dpGoW_abort j m f h hf0] at hb; simp at hb
  rw [dpGoW_view j m f h hf0] at hb
  obtain ⟨F, hF⟩ : ∃ F, f.toNat = F + 1 := ⟨f.toNat - 1, by have := toNat_ne_zero' hf0; omega⟩
  cases hvl : eViewW m h with
  | nil => rw [hvl] at hb; simp [dpG1] at hb
  | cons g vt =>
    have hne : eViewW m h ≠ [] := by rw [hvl]; simp
    obtain ⟨v, hv, hvr⟩ := eViewW_ok m (a) hA h hne
    rw [hvl] at hvr hb
    have leaf : ∀ (hg : (g :: vt).headD 0 = 0 ∨ (g :: vt).headD 0 = 1 ∨ (g :: vt).headD 0 = 2 ∨
        (g :: vt).headD 0 = 3 ∨ (g :: vt).headD 0 = 8),
        (match v with | .bvar _ | .sort _ | .lit _ | .fvar _ _ | .const _ _ => True | _ => False) →
        ∃ d mp', (ConRon.Arena.depthGo mp f.toNat (decE h)).run a = .ok ((d, mp'), a) ∧ r.toNat = d ∧
          dpMR m' mp' ∧ MemFrame [DPM] [207] m m' := by
      intro hg hv'
      rw [dpG1_leaf j m f h _ (by simp) hg] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨1, mp, ?_, rfl, hM, MemFrame.refl _ _ _⟩
      rw [hF, depthGo_succ', StateT.run_bind, view_run _ a _ hv, except_ok_bind]
      cases v <;> first | rfl | exact False.elim hv'
    cases v with
    | bvar i =>
      have hg0 : (g :: vt).headD 0 = 0 := by simpa [ViewR] using hvr.1
      exact leaf (Or.inl hg0) trivial
    | fvar i ty =>
      have hg0 : (g :: vt).headD 0 = 1 := hvr.1
      exact leaf (Or.inr (Or.inl hg0)) trivial
    | sort u =>
      have hg0 : (g :: vt).headD 0 = 2 := by simpa [ViewR] using hvr.1
      exact leaf (Or.inr (Or.inr (Or.inl hg0))) trivial
    | const nn us =>
      have hg0 : (g :: vt).headD 0 = 3 := hvr.1
      exact leaf (Or.inr (Or.inr (Or.inr (Or.inl hg0)))) trivial
    | lit l =>
      have hg0 : (g :: vt).headD 0 = 8 := by simpa [ViewR] using hvr
      exact leaf (Or.inr (Or.inr (Or.inr (Or.inr hg0)))) trivial
    | app f' x' =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inl hvr.1) hb hA hh hM
    | lam f' x' =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inl hvr.1)) hb hA hh hM
    | forallE f' x' =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inl hvr.1))) hb hA hh hM
    | letE t v' b' =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inl hvr.1)))) hb hA hh hM
    | proj s i e =>
      rw [hF]
      exact dpGo_nodeCase j ih m m' a f h r mp F hF hf0 _ _ hvr trivial hv (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inr hvr.1)))) hb hA hh hM

theorem dpGoOK (n : Nat) : DpGoOK n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => intro m m' a f h r mp hb; simp [dpGoW] at hb
    | succ j => exact dpGo_step_ok j (fun k hk => ih k (by omega))


def dpClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) => if rdW (m1.arr64 CTL) dpSch.cs + 2 = 0 then none else some (r, mclearG dpSch m1)

def dpConstW (n : Nat) (m : Mem) (e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) dpSch.cs + 2 = 0 then none else dpClrK (dpGoW n (mclearG dpSch m) CWF e)

theorem dpConstW_eq (n : Nat) (m : Mem) (e : Word) (h0 : rdW (m.arr64 CTL) dpSch.cs + 2 ≠ 0) :
    dpConstW n m e = dpClrK (dpGoW n (mclearG dpSch m) CWF e) := by simp [dpConstW, h0]
theorem dpClrK_some (r : Word) (m1 : Mem) (h0 : rdW (m1.arr64 CTL) dpSch.cs + 2 ≠ 0) :
    dpClrK (some (r, m1)) = some (r, mclearG dpSch m1) := by simp [dpClrK, h0]
attribute [ind_grind] dpConstW_eq dpClrK_some

def wfW (n : Nat) (m : Mem) (e : Word) : Option (Word × Mem) :=
  match dpConstW n m e with
  | none => none
  | some (d, m1) => if 4294967296 ≤ d then none else some (d + 1024, m1)

theorem wf_none (n : Nat) (m : Mem) (e : Word) (h : dpConstW n m e = none) : wfW n m e = none := by
  simp [wfW, h]
theorem wf_big (n : Nat) (m m1 : Mem) (e d : Word) (h : dpConstW n m e = some (d, m1))
    (hb : 4294967296 ≤ d) : wfW n m e = none := by simp [wfW, h, hb]
theorem wf_ok (n : Nat) (m m1 : Mem) (e d : Word) (h : dpConstW n m e = some (d, m1))
    (hb : ¬ 4294967296 ≤ d) : wfW n m e = some (d + 1024, m1) := by simp [wfW, h, hb]
attribute [ind_grind] wf_none wf_big wf_ok

section spec2
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "dp_find" = some (memoFindG dpSch)) (hput : p.lookup "dp_put" = some (memoPutG dpSch))
  (hgo : p.lookup "depth_go" = some depthGo) (hnode : p.lookup "depth_node" = some depthNode)
  (hcl : p.lookup "dp_clear" = some (memoClearG dpSch))
  (hd : p.lookup "depth" = some depth)

include hv hf hput hgo hnode hcl hd in
theorem depth_spec (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "depth" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ dpConstW n s₀.mem e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (dpGo_spec p hv hf hput hgo hnode n).1
  unfold DpGoSpec at ih
  rw [invoke_eq _ hd]
  simp only [callFn, depth]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec dpSch p _ hcl n, ih] <;>
    finish

include hv hf hput hgo hnode hcl hd in
theorem whnfWalkFuel_spec (hw : p.lookup "whnf_walk_fuel" = some whnfWalkFuel) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "whnf_walk_fuel" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ wfW n s₀.mem e = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hw]
  simp only [callFn, whnfWalkFuel]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, depth_spec p hv hf hput hgo hnode hcl hd n] <;>
    finish (gen := 20) [wfW]

end spec2


theorem dpConstW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (e r : Word) (mp0 : Std.HashMap EIdx Nat)
    (hb : dpConstW n m e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e) (hM : dpMR m mp0) :
    ∃ d, (ConRon.Arena.depth (decE e)).run a = .ok (d, a) ∧ r.toNat = d ∧ dpMR m' ∅ ∧
      StageR dn vis fe m' a ∧ IWGrow m m' := by
  by_cases h0 : rdW (m.arr64 CTL) dpSch.cs + 2 = 0
  · simp [dpConstW, h0] at hb
  rw [dpConstW_eq n m e h0] at hb
  have hf0 := mclearG_frame dpSch m
  have hM0 := memoRG_clear dpSch dpSch_wf bmKey (fun w : Word => w.toNat) m mp0 hM h0
  have hA0 : ArenaR (mclearG dpSch m) a :=
    ArenaR.frame (A := []) (C := [dpSch.cs, dpSch.cs + 1]) (fun b hb => by simp at hb)
      (fun x hx => by simp [dpSch] at hx; rcases hx with rfl | rfl <;> exact not_mem_arenaCtl _ (by decide)) hf0
      hS.1.arena.1
  cases hg : dpGoW n (mclearG dpSch m) CWF e with
  | none => rw [hg] at hb; simp [dpClrK] at hb
  | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [hg] at hb
    by_cases h1 : rdW (m1.arr64 CTL) dpSch.cs + 2 = 0
    · simp [dpClrK, h1] at hb
    rw [dpClrK_some r1 m1 h1] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨d, mp1, hrun, hbb, hM1, hfr1⟩ := dpGoOK n _ _ a CWF e r1 ∅ hg hA0 he hM0
    rw [CWF_eq] at hrun
    have hM2 := memoRG_clear dpSch dpSch_wf bmKey (fun w : Word => w.toNat) m1 mp1 hM1 h1
    have hf2 := mclearG_frame dpSch m1
    have hfall : MemFrame [DPM] [dpSch.cs, dpSch.cs + 1] m (mclearG dpSch m1) :=
      ((hf0.mono (by simp) (by simp)).trans (hfr1.mono (by simp) (by simp [dpSch]))).trans
        (hf2.mono (by simp) (by simp))
    obtain ⟨hS', hg'⟩ := StageR.frame_hi hS hfall (by intro b hb; simp at hb; subst hb; decide)
      (by intro x hx; simp [dpSch] at hx; rcases hx with rfl | rfl <;> decide) (by decide)
      (by simp [dpSch])
    refine ⟨d, ?_, hbb, hM2, hS', hg'⟩
    simp only [ConRon.Arena.depth, StateT.run_bind]
    rw [hrun]
    rfl

theorem wfW_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (e r : Word) (mp0 : Std.HashMap EIdx Nat)
    (hb : wfW n m e = some (r, m')) (hS : StageR dn vis fe m a) (he : H e) (hM : dpMR m mp0) :
    ∃ d, (ConRon.Arena.whnfWalkFuel (decE e)).run a = .ok (d, a) ∧ r.toNat = d ∧ dpMR m' ∅ ∧
      StageR dn vis fe m' a ∧ IWGrow m m' := by
  unfold wfW at hb
  cases hc : dpConstW n m e with
  | none => rw [hc] at hb; simp at hb
  | some p1 =>
    obtain ⟨d, m1⟩ := p1
    rw [hc] at hb
    by_cases hbig : 4294967296 ≤ d
    · simp [hbig] at hb
    simp only [hbig, if_false, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨dd, hrun, hdd, hM', hS', hg⟩ := dpConstW_ok n dn fe vis m m1 a e d mp0 hc hS he hM
    have hlt : d.toNat < 2 ^ 32 := by
      have e1 : (4294967296 : Word).toNat = 4294967296 := by decide
      have : ¬ (4294967296 : Word).toNat ≤ d.toNat := fun hh => hbig (UInt64.le_iff_toNat_le.mpr hh)
      omega
    refine ⟨dd + 1024, ?_, ?_, hM', hS', hg⟩
    · simp only [ConRon.Arena.whnfWalkFuel, StateT.run_bind]
      rw [hrun]
      simp only [except_ok_bind]
      show (pure (dd + fuelSlack) : AM Nat).run a = _
      rfl
    · rw [UInt64.toNat_add, hdd]
      have e2 : (1024 : Word).toNat = 1024 := by decide
      rw [e2]
      have h64 : dd < 2 ^ 32 := by rw [← hdd]; exact hlt
      exact Nat.mod_eq_of_lt (by simp; omega)


section census
variable (p : Prog) (hv : p.lookup "e_view" = some eView)
  (hf : p.lookup "dp_find" = some (memoFindG dpSch)) (hput : p.lookup "dp_put" = some (memoPutG dpSch))
  (hgo : p.lookup "depth_go" = some depthGo) (hnode : p.lookup "depth_node" = some depthNode)
  (hcl : p.lookup "dp_clear" = some (memoClearG dpSch))
  (hd : p.lookup "depth" = some depth) (hw : p.lookup "whnf_walk_fuel" = some whnfWalkFuel)

include hv hf hput hgo hnode in
/-- **`depth_go` (with `depth_node`) refines `depthGo`**, from a memo related to the twin's. -/
@[refines ConRon.Arena.depthGo]
theorem depthGo_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis f h : Word) (mp : Std.HashMap EIdx Nat) (hh : H h)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : dpMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "depth_go" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.depthGo mp f.toNat (decE h)) a₀ ∧
      AM.st (ConRon.Arena.depthGo mp f.toNat (decE h)) a₀ = a₀ ∧
      (r.headD 0).toNat = (AM.res (ConRon.Arena.depthGo mp f.toNat (decE h)) a₀).1 ∧
      dpMR s'.mem (AM.res (ConRon.Arena.depthGo mp f.toNat (decE h)) a₀).2 ∧
      StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post ((dpGo_spec p hv hf hput hgo hnode n).1 s₀ f h) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨d, mp', hrun, hb, hM', hfr⟩ := dpGoOK n _ _ a₀ f h _ mp hm hS.1.arena.1 hh hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  obtain ⟨hS', hg⟩ := StageR.frame_hi hS hfr (by intro b hb; simp at hb; subst hb; decide)
    (by intro x hx; simp at hx; subst hx; decide) (by decide) (by decide)
  refine ⟨hl, hok, hst, by rw [hres]; exact hb, by rw [hres]; exact hM', hS', hg⟩

include hv hf hput hgo hnode hcl hd in
/-- **`depth` refines `depth`**: one memoised DAG walk between two clears. -/
@[refines ConRon.Arena.depth]
theorem depth_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis e : Word) (mp0 : Std.HashMap EIdx Nat) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : dpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "depth" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.depth (decE e)) a₀ ∧
      AM.st (ConRon.Arena.depth (decE e)) a₀ = a₀ ∧
      (r.headD 0).toNat = AM.res (ConRon.Arena.depth (decE e)) a₀ ∧
      dpMR s'.mem ∅ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (depth_spec p hv hf hput hgo hnode hcl hd n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨d, hrun, hb, hM', hS', hg⟩ := dpConstW_ok n dn fe vis _ _ a₀ e _ mp0 hm hS he hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hb, hM', hS', hg⟩

include hv hf hput hgo hnode hcl hd hw in
/-- **`whnf_walk_fuel` refines `whnfWalkFuel`**: the depth plus the slack. -/
@[refines ConRon.Arena.whnfWalkFuel]
theorem whnfWalkFuel_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis e : Word) (mp0 : Std.HashMap EIdx Nat) (he : H e)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : dpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "whnf_walk_fuel" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.whnfWalkFuel (decE e)) a₀ ∧
      AM.st (ConRon.Arena.whnfWalkFuel (decE e)) a₀ = a₀ ∧
      (r.headD 0).toNat = AM.res (ConRon.Arena.whnfWalkFuel (decE e)) a₀ ∧
      dpMR s'.mem ∅ ∧ StageR dn vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (whnfWalkFuel_spec p hv hf hput hgo hnode hcl hd hw n s₀ e) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨d, hrun, hb, hM', hS', hg⟩ := wfW_ok n dn fe vis _ _ a₀ e _ mp0 hm hS he hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst, by rw [hres]; exact hb, hM', hS', hg⟩

end census

/-! ## `nest_phs` -/

mutual
def phsGoW : Nat → Mem → Word → Word → Word → Option Mem
  | 0, _, _, _, _ => none
  | k + 1, m, q, n, i => if n ≤ i then some m else phsK1 k m q n i (pinWordV m 53)
def phsK1 (k : Nat) (m : Mem) (q n i : Word) : Option Word → Option Mem
  | none => none
  | some z => if 4294967296 ≤ z then none else phsK2 k q n i (sointernW m z)
def phsK2 (k : Nat) (q n i : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (s, m1) => if 4294967296 ≤ s then none else phsK3 k q n i (fvinternW m1 i s)
def phsK3 (k : Nat) (q n i : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (v, m2) => if 4294967296 ≤ v then none else phsGoW k (m2.set64 IW (q + i) v) q n (i + 1)
end

section arms
variable (k : Nat) (m m1 m2 : Mem) (q n i z s v : Word)
theorem phsGoW_done (h : n ≤ i) : phsGoW (k + 1) m q n i = some m := by simp [phsGoW, h]
theorem phsGoW_step (h : ¬ n ≤ i) : phsGoW (k + 1) m q n i = phsK1 k m q n i (pinWordV m 53) := by
  simp [phsGoW, h]
theorem phsK1_big (h : 4294967296 ≤ z) : phsK1 k m q n i (some z) = none := by simp [phsK1, h]
theorem phsK1_ok (h : ¬ 4294967296 ≤ z) : phsK1 k m q n i (some z) = phsK2 k q n i (sointernW m z) := by
  simp only [phsK1]; rw [if_neg h]
theorem phsK2_big (h : 4294967296 ≤ s) : phsK2 k q n i (some (s, m1)) = none := by simp [phsK2, h]
theorem phsK2_ok (h : ¬ 4294967296 ≤ s) : phsK2 k q n i (some (s, m1)) = phsK3 k q n i (fvinternW m1 i s) := by
  simp only [phsK2]; rw [if_neg h]
theorem phsK3_big (h : 4294967296 ≤ v) : phsK3 k q n i (some (v, m2)) = none := by simp [phsK3, h]
theorem phsK3_ok (h : ¬ 4294967296 ≤ v) :
    phsK3 k q n i (some (v, m2)) = phsGoW k (m2.set64 IW (q + i) v) q n (i + 1) := by
  simp only [phsK3]; rw [if_neg h]
end arms
attribute [ind_grind] phsGoW_done phsGoW_step phsK1_big phsK1_ok phsK2_big phsK2_ok phsK3_big phsK3_ok

section spec
variable (p : Prog) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hp : p.lookup "nest_phs_go" = some nestPhsGo)
include hpw hsf hsp his hff hfp hif hp

theorem nestPhsGo_spec (k : Nat) : ∀ (s₀ : St) (q n i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_phs_go" [q, n, i]
    ⦃fun _ s' => LocEq s' s₀ ∧ phsGoW k s₀.mem q n i = some s'.mem; ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ q n i
    rw [invoke_eq _ hp]; simp only [callFn, nestPhsGo]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ q n i
    rw [invoke_eq _ hp]
    simp only [callFn, nestPhsGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        pinWord_specV p hpw k, internSort_spec p hsf hsp his k, internFVar_spec p hff hfp hif k, ih] <;>
      finish (gen := 20)

end spec


def phsB (q nn : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m2 => some ([q, nn], m2)
def phsA (k : Nat) (nn : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m1) => phsB q nn (phsGoW k m1 q nn 0)
def phsW (k : Nat) (m : Mem) (nn : Word) : Option (List Word × Mem) := phsA k nn (allocW m nn)
theorem phsB_some (q nn : Word) (m2 : Mem) : phsB q nn (some m2) = some ([q, nn], m2) := rfl
theorem phsA_some (k : Nat) (nn q : Word) (m1 : Mem) : phsA k nn (some (q, m1)) = phsB q nn (phsGoW k m1 q nn 0) := rfl
attribute [ind_grind] phsB_some phsA_some

section spec2
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hg : p.lookup "nest_phs_go" = some nestPhsGo) (hp : p.lookup "nest_phs" = some nestPhs)
include ha hpw hsf hsp his hff hfp hif hg hp

theorem nestPhs_spec (k : Nat) (s₀ : St) (nn : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_phs" [nn]
    ⦃fun r s' => LocEq s' s₀ ∧ phsW k s₀.mem nn = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestPhs]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      iwAlloc_specW p ha k, nestPhsGo_spec p hpw hsf hsp his hff hfp hif hg k] <;>
    finish (gen := 20) [phsW]

end spec2


theorem decHL_write {k : IdxKind} (m : Mem) (q i v : Word) (ws : List (Idx k))
    (hv : v.toNat < 2 ^ 32) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hb : q.toNat + i.toNat < (m.arr64 IW).size) (h : decHL m q.toNat i.toNat = some ws) :
    decHL (m.set64 IW (q + i) v) q.toNat (i.toNat + 1) = some (ws ++ [decI v]) := by
  have hqi : (q + i).toNat = q.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  simp only [decHL]
  rw [hslice?_add]
  have h1 : (hslice? (iwA (m.set64 IW (q + i) v)) q.toNat i.toNat : Option (List (Idx k))) = some ws := by
    rw [← h]; simp only [decHL]
    apply hslice?_congr
    intro j hj
    simp only [iwA, set64IW_get]
    rw [if_neg (by omega)]
  have h2 : (hslice? (iwA (m.set64 IW (q + i) v)) (q.toNat + i.toNat) 1 : Option (List (Idx k))) =
      some [decI v] := by
    rw [hslice?_succ]
    have : (hd? (iwA (m.set64 IW (q + i) v)) (q.toNat + i.toNat) : Option (Idx k)) = some (decI v) := by
      simp [hd?, iwA, set64IW_get, hqi, hb, hv]
    rw [this]; simp [hslice?]
  rw [h1, h2]; simp


theorem StageR.set_iw {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR dn vis fe m a) (p x : Word) : StageR dn vis fe (m.set64 IW p x) a := by
  have hf := set64IW_frame m p x
  have hC : (m.set64 IW p x).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hE : (m.set64 IW p x).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨CheckR.frame_iw hf hS.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.2
  have hI := hf.2.2.1 IW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [iwTop, hC, hI]; exact h1
  · simp only [erTop, hC, hE]; exact h2
  · rw [hI]; exact h3
  · rw [hE]; exact h4
  · rw [hC]; exact h5

/-- The pool outside `[q, q + n)`, its top and size, the constant records: unchanged. -/
def KeepIW (q n : Word) (m m' : Mem) : Prop :=
  (∀ idx, (idx < q.toNat ∨ q.toNat + n.toNat ≤ idx) → (m'.arr64 IW)[idx]? = (m.arr64 IW)[idx]?) ∧
  iwTop m' = iwTop m ∧ erTop m' = erTop m ∧ (m'.arr64 IW).size = (m.arr64 IW).size ∧
  m'.arr64 EREC = m.arr64 EREC

theorem KeepIW.refl (q n : Word) (m : Mem) : KeepIW q n m m := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem KeepIW.trans {q n : Word} {m₁ m₂ m₃ : Mem} (h₁ : KeepIW q n m₁ m₂) (h₂ : KeepIW q n m₂ m₃) :
    KeepIW q n m₁ m₃ :=
  ⟨fun idx hi => (h₂.1 idx hi).trans (h₁.1 idx hi), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem KeepIW.of_low {q n : Word} {m m' : Mem} (h : LowFr m m') : KeepIW q n m m' := by
  obtain ⟨A, C, hf, hA, hC⟩ := h
  have hI : m'.arr64 IW = m.arr64 IW := hf.1 IW (fun hh => by have := hA _ hh; simp [IW] at this) (by decide)
  have hE : m'.arr64 EREC = m.arr64 EREC := hf.1 EREC (fun hh => by have := hA _ hh; simp [EREC] at this) (by decide)
  have h200 : rdW (m'.arr64 CTL) 200 = rdW (m.arr64 CTL) 200 := hf.2.1 200 (fun hh => by have := hC _ hh; simp at this)
  have h129 : rdW (m'.arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (fun hh => by have := hC _ hh; simp at this)
  exact ⟨fun _ _ => by rw [hI], by simp only [iwTop, h200], by simp only [erTop, h129], by rw [hI], hE⟩

theorem KeepIW.set {q n i v : Word} (m : Mem) (hi : i.toNat < n.toNat) (hqi : (q + i).toNat = q.toNat + i.toNat) :
    KeepIW q n m (m.set64 IW (q + i) v) := by
  have hC : (m.set64 IW (q + i) v).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hE : (m.set64 IW (q + i) v).arr64 EREC = m.arr64 EREC := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  refine ⟨fun idx hidx => ?_, by simp only [iwTop, hC], by simp only [erTop, hC], (set64IW_frame m _ _).2.2.1 IW, hE⟩
  rw [set64IW_get, if_neg (by omega)]


theorem lowFr_iw {m m' : Mem} (h : LowFr m m') : m'.arr64 IW = m.arr64 IW := by
  obtain ⟨A, C, hf, hA, hC⟩ := h
  exact hf.1 IW (fun hh => by have := hA _ hh; simp [IW] at this) (by decide)

def phF (i : Nat) : AM EIdx := do
  let z ← zeroLevel
  let s ← internSortE z
  internFVarE i s

theorem nestPhs_eq (n : Nat) : ConRon.Arena.nestPhs n = (List.range' 0 n).mapM phF := by
  simp only [ConRon.Arena.nestPhs, List.range_eq_range']
  rfl

theorem range'_mapM_succ (i k : Nat) :
    (List.range' i (k + 1)).mapM phF = (do
      let x ← phF i
      let xs ← (List.range' (i + 1) k).mapM phF
      pure (x :: xs)) := by
  rw [List.range'_succ, List.mapM_cons]

theorem phsGoW_ok (k : Nat) : ∀ (m m' : Mem) (a : AState) (q n i : Word) (ws : List EIdx)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word),
    phsGoW k m q n i = some m' → StageR dn vis fe m a → i.toNat ≤ n.toNat →
    q.toNat + n.toNat ≤ (m.arr64 IW).size → (m.arr64 IW).size < 2 ^ 64 →
    decHL m q.toNat i.toNat = some ws →
    ∃ phs a', ((List.range' i.toNat (n.toNat - i.toNat)).mapM phF).run a = .ok (phs, a') ∧
      StageR dn vis fe m' a' ∧ KeepIW q n m m' ∧ decHL m' q.toNat n.toNat = some (ws ++ phs) := by
  induction k with
  | zero => intro m m' a q n i ws dn fe vis h; simp [phsGoW] at h
  | succ k ih =>
    intro m m' a q n i ws dn fe vis h hS hi hq hsz hdec
    by_cases hd : n ≤ i
    · rw [phsGoW_done k m q n i hd] at h
      simp only [Option.some.injEq] at h
      subst h
      have hin : n.toNat - i.toNat = 0 := by
        have := UInt64.le_iff_toNat_le.mp hd; omega
      have hien : i.toNat = n.toNat := by
        have := UInt64.le_iff_toNat_le.mp hd; omega
      refine ⟨[], a, ?_, hS, KeepIW.refl _ _ _, ?_⟩
      · rw [hin]; rfl
      · rw [← hien]; simpa using hdec
    · rw [phsGoW_step k m q n i hd] at h
      have hlt : i.toNat < n.toNat := by
        have : ¬ n.toNat ≤ i.toNat := fun hh => hd (UInt64.le_iff_toNat_le.mpr hh)
        omega
      cases hpw : pinWordV m 53 with
      | none => rw [hpw] at h; simp [phsK1] at h
      | some z =>
        rw [hpw] at h
        by_cases hzb : 4294967296 ≤ z
        · rw [phsK1_big _ _ _ _ _ _ hzb] at h; simp at h
        rw [phsK1_ok _ _ _ _ _ _ hzb] at h
        have hzlt := lt_of_notbig hzb
        have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
          intro h0; simp [pinWordV, h0] at hpw
        have hz : z = pinW m 53 := by
          simp only [pinWordV, hpne, if_false, Option.some.injEq] at hpw
          rw [← hpw]; simp [pinW, rdW]
        have hpin0 : pinW m 0 ≠ 0 := by simpa [pinW, rdW] using hpne
        have hfull := hS.1.pins.full hpin0
        cases hso : sointernW m z with
        | none => rw [hso] at h; simp [phsK2] at h
        | some p1 =>
          obtain ⟨s1, m1⟩ := p1
          rw [hso] at h
          by_cases hsb : 4294967296 ≤ s1
          · rw [phsK2_big _ _ _ _ _ _ hsb] at h; simp at h
          rw [phsK2_ok _ _ _ _ _ _ hsb] at h
          have hs1lt := lt_of_notbig hsb
          cases hfv : fvinternW m1 i s1 with
          | none => rw [hfv] at h; simp [phsK3] at h
          | some p2 =>
            obtain ⟨v, m2⟩ := p2
            rw [hfv] at h
            by_cases hvb : 4294967296 ≤ v
            · rw [phsK3_big _ _ _ _ _ _ hvb] at h; simp at h
            rw [phsK3_ok _ _ _ _ _ _ hvb] at h
            have hvlt := lt_of_notbig hvb
            obtain ⟨a1, hr1, hS1, hg1⟩ := internSort_stage hS z hzlt hso
            obtain ⟨a2, hr2, hS2, hg2⟩ := internFVar_stage hS1 i s1 hs1lt hfv
            have hlow : LowFr m m2 := (sointernW_low hso).trans (fvinternW_low hfv)
            have hI2 := lowFr_iw hlow
            have hqi : (q + i).toNat = q.toNat + i.toNat := by
              rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
            have hdec2 : decHL m2 q.toNat i.toNat = some ws := by
              rw [← hdec]; simp only [decHL, iwA, hI2]
            have hdec3 := decHL_write m2 q i v ws hvlt (by rw [hI2]; exact hsz) (by rw [hI2]; omega) hdec2
            have hS3 := hS2.set_iw (q + i) v
            have hi1 : (i + 1).toNat = i.toNat + 1 := toNat_add_one' (by omega)
            obtain ⟨phs, a3, hrun, hS4, hK, hdecF⟩ := ih (m2.set64 IW (q + i) v) m' a2 q n (i + 1) (ws ++ [decI v]) dn fe vis h
              hS3 (by rw [hi1]; omega) (by rw [(set64IW_frame m2 (q + i) v).2.2.1 IW, hI2]; exact hq)
              (by rw [(set64IW_frame m2 (q + i) v).2.2.1 IW, hI2]; exact hsz) (by rw [hi1]; exact hdec3)
            have hn1 : n.toNat - i.toNat = (n.toNat - (i.toNat + 1)) + 1 := by omega
            refine ⟨decE v :: phs, a3, ?_, hS4, ?_, ?_⟩
            · rw [hn1, range'_mapM_succ]
              simp only [StateT.run_bind]
              have hzl : zeroLevel.run a = .ok (decI z, a) := by
                rw [hz]; exact pinZeroLevel_run hfull
              have e1 : (phF i.toNat).run a = .ok (decE v, a2) := by
                simp only [phF, StateT.run_bind]
                rw [hzl]
                simp only [except_ok_bind, StateT.run_bind]
                simp only [ConRon.Arena.internSortE, ConRon.Arena.internFVarE]
                rw [hr1]
                simp only [except_ok_bind]
                exact hr2
              rw [e1]
              simp only [except_ok_bind, StateT.run_bind]
              rw [hi1] at hrun
              rw [hrun]
              rfl
            · exact ((KeepIW.of_low hlow).trans (KeepIW.set m2 (by omega) hqi)).trans hK
            · simp only [List.append_assoc, List.singleton_append] at hdecF; exact hdecF


theorem StageR.alloc {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m1 : Mem} {k q : Word} (hS : StageR dn vis fe m a) (h : allocW m k = some (q, m1)) :
    StageR dn vis fe m1 a ∧ IWGrow m m1 ∧ q = rdW (m.arr64 CTL) 200 ∧ q.toNat + k.toNat ≤ (m.arr64 IW).size ∧
      iwTop m1 = q.toNat + k.toNat := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.2
  obtain ⟨hq, hm1, hroom⟩ := allocW_facts h h3
  subst hm1
  have hf := allocMem_frame m k
  have hqi : q.toNat = iwTop m := by simp only [iwTop, hq]
  have htop : iwTop (allocMem m k) = q.toNat + k.toNat := by
    simp only [iwTop, allocMem_top m k h5, ← hq]
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have h129 : rdW ((allocMem m k).arr64 CTL) 129 = rdW (m.arr64 CTL) 129 := hf.2.1 129 (by simp)
  have hE : (allocMem m k).arr64 EREC = m.arr64 EREC := hf.1 EREC (by simp [EREC, IW]) (by decide)
  refine ⟨⟨CheckR.frame_iw hf hS.1, ?_, ?_, ?_, ?_, ?_⟩, allocMem_grow m k (by omega) h5, hq, hroom, htop⟩
  · rw [htop, hf.2.2.1 IW]; exact hroom
  · simp only [erTop, h129, hE]; exact h2
  · rw [hf.2.2.1 IW]; exact h3
  · rw [hE]; exact h4
  · rw [hf.2.2.1 CTL]; exact h5

theorem phsW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (nn : Word) (r : List Word)
    (h : phsW k m nn = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ phs a', (ConRon.Arena.nestPhs nn.toNat).run a = .ok (phs, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some phs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  unfold phsW at h
  cases hal : allocW m nn with
  | none => rw [hal] at h; simp [phsA] at h
  | some pq =>
    obtain ⟨q, m1⟩ := pq
    rw [hal, phsA_some] at h
    obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
    cases hl : phsGoW k m1 q nn 0 with
    | none => rw [hl] at h; simp [phsB] at h
    | some m2 =>
      rw [hl, phsB_some] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
      have hroom1 : q.toNat + nn.toNat ≤ (m1.arr64 IW).size := by
        have := hS1.2.1; simp only [iwTop] at htop1 this; omega
      obtain ⟨phs, a', hrun, hS2, hK, hdec⟩ := phsGoW_ok k m1 m2 a q nn 0 [] dn fe vis hl hS1
        (by simp) hroom1 hsz1 (by simp [decHL, hslice?])
      refine ⟨phs, a', ?_, hS2, ?_, by simpa using hdec, ?_⟩
      · rw [nestPhs_eq]
        simpa using hrun
      · obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hK
        refine ⟨?_, ?_, fun idx hidx => ?_, fun idx hidx => ?_⟩
        · rw [hK2]; exact hg1.1
        · rw [hK3]; exact hg1.2.1
        · have hq : idx < q.toNat := by
            have : q.toNat = iwTop m := by simp only [iwTop, hqd]
            omega
          rw [hK1 idx (Or.inl hq)]; exact hg1.2.2.1 idx hidx
        · rw [hK5]; exact hg1.2.2.2 idx hidx
      · show q.toNat + nn.toNat ≤ iwTop m2
        rw [hK.2.1, htop1]; exact Nat.le_refl _


section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hpw : p.lookup "pin_word" = some pinWordL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hg : p.lookup "nest_phs_go" = some nestPhsGo) (hp : p.lookup "nest_phs" = some nestPhs)
include ha hpw hsf hsp his hff hfp hif hg hp

/-- **`nest_phs` refines `nestPhs`**: the canonical parameter variables as a new `IW` slice. -/
@[refines ConRon.Arena.nestPhs]
theorem nestPhs_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis nn : Word) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_phs" [nn]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestPhs nn.toNat) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestPhs nn.toNat) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat = some (AM.res (ConRon.Arena.nestPhs nn.toNat) a₀); ⊤⦄ := by
  refine triple_post (nestPhs_spec p ha hpw hsf hsp his hff hfp hif hg hp k s₀ nn) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨phs, a', hrun, hS', hgr, hdec, -⟩ := phsW_ok k dn fe vis _ _ a₀ nn r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hgr, by rw [hres]; exact hdec⟩

end census

end L.Ind
