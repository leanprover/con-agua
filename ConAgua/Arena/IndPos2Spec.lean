import ConAgua.Arena.IndPos2
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.Env

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

end L.Ind
